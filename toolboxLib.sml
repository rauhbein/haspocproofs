structure toolboxLib :> toolboxLib  =
struct

open HolKernel boolLib bossLib;

(* 
  this library is a collection of generally useful
  ML-functions, for instance, for:
    - list operations
    - HOL term matching and finding
    - HOL type reasoning  
  Note that this library is not supposed to contain
  tactics, convertions, or rules, which can be found
  in tacticsLib instead. 
*)


(* matching and finding *)
fun is_match t1 t2 =
    let 
       val sm = (SOME (match_term t1 t2)) handle _ => NONE
    in
       case sm 
        of SOME _ => true
         | NONE => false
    end;

fun is_type_match pattern ty = 
    (let
      val _ = match_type pattern ty
    in true end) handle _ => false;


fun find_term_opt f t =  ((SOME (find_term f t)) handle HOL_ERR _ => NONE);
fun there_is_some t1 t2 = (find_term_opt (term_eq t1) t2 <> NONE);

(* are two substitutions consistent on a given pattern term? *)
fun consistent_on pattern subs1 subs2 =
    (subst subs1 (subst subs2 pattern))
     =  (subst subs2 (subst subs1 pattern));


(* is a variable starting with an underscore? *)
fun is_underscore trm =
    is_var trm andalso (dest_var trm |> fst |>  String.isPrefix "_");

(* is a redex variable starting with an underscore? *)
fun is_underscore_redex (s:{redex: Term.term, residue: Term.term}) =
    is_underscore (#redex s);




(* generates theorem 
   !P. (!x. P x) = P x1 /\ ... /\ P xn
   where x1 ... xn are the constructors of the given type *)
fun fall_constructors_thm_of ty =
    let
       val pred_ty = ``:^ty -> bool``
       val singles = map ((curry mk_comb) (mk_var("P",pred_ty))) (TypeBase.constructors_of ty) |> list_mk_conj
       val gl =  ``!P. (!x. P x) = ^singles``
       val th = prove(gl, GEN_TAC THEN EQ_TAC THEN FULL_SIMP_TAC (srw_ss()) [TypeBase.induction_of ty])
    in
      th
    end;


(* list operations *)
fun remove_redundancy_simp lst =
    (case lst
     of []    => []
     |  x::[] => [x]
     |  x::xs => (if (List.exists (fn y => x = y) xs) then (remove_redundancy_simp xs) else (x::(remove_redundancy_simp xs))));


fun remove_redundancy_by_eq eqf lst =
    (case lst
     of []    => []
     |  x::[] => [x]
     |  x::xs => (if (List.exists (eqf x) xs) then (remove_redundancy_by_eq eqf xs) else (x::(remove_redundancy_by_eq eqf xs))));

fun pump_list_simp xs ol ml = 
    snd (ListPair.unzip (List.mapPartial (fn x => List.find (fn (a,b) => a=x) (ListPair.zip (ml, xs))) ol));

fun is_contained xs ys =
    (case xs 
     of [] => true
     | x::s => ((List.exists (fn y => x = y) ys) andalso (is_contained s ys)));

fun compare_lists xs ys = (is_contained xs ys andalso is_contained ys xs);

fun map_until f g pred lst =
   case lst of 
        [] => []
      | (x::xs) => (let val fx = (f x) in
                    (if (pred fx) then (fx::(map g xs)) else (fx::(map_until f g pred xs))) end);


(* borrowed from New Jersey-SML library ListXProd:
   map a function across the cross product of two lists *)
fun mapX f (l1, l2) = let
  fun lp1 ([], resL) = rev resL
    | lp1 (x::r, resL) = let
 	fun lp2 ([], resL) = lp1 (r, resL)
 	  | lp2 (y::r, resL) = lp2 (r, f(x, y) :: resL)
 	in
 	  lp2 (l2, resL)
 	end
  in
    lp1 (l1, [])
  end;

(* borrowed from New Jersey-SML library ListXProd:
   fold a function across the cross product of two lists *)
fun foldX f (l1, l2) = let
  fun lp1 ([], accum) = accum
    | lp1 (x::r, accum) = let
	fun lp2 ([], accum) = lp1 (r, accum)
	  | lp2 (y::r, accum) = lp2 (r, f(x, y, accum))
	in
	  lp2 (l2, accum)
	end
  in
    fn init => lp1 (l1, init)
  end;



(* match_and_learn:
   ================
  
 Expects a list of pairs of lists in the following shape:
  
 [ ([pattern_11, ..., pattern_1n], [term_11, ..., term_1m]),
   ...,
   ([pattern_k1, ..., pattern_kr], [term_k1, ..., term_kq]) ]
  
 Each pair represents one learning round and is comprised of 
 a list of pattern terms and a list of input terms.
 For instance, a pattern term could be ``P (X, _)``
 and an input term ``P (x0, y0)``.
 The task of match_and_learn is to match the input term against
 the pattern and find a substitution instantiating X with x0.
 Within one round, all input terms are matched against all 
 patterns and match_and_learn raises an exception if an
 inconsistency occurs. With every new round, all variables
 identified in earlier rounds become fixed. New input terms not
 agreeing with fixed variables are simply ignored rather than
 raising an exception. However, (non-ignored) input terms of 
 the same round and disagreeing on a non-fixed variable will
 still cause an exception.
  
 Example use case: First, find THE ONE state mentioned as argument
 of an invariant. It is fine if there are multiple invariant predicates
 on the very same state, but match_and_learn fails if there are several
 different states referred to by the predicates of the invariant.
 Then in a second round, find THE ONE post-state connected to the
 pre-state identified in the first round, typically through a 
 transition predicate. It is fine if there are transition predicates
 on other pre-states (no matter what post-states they link to),
 but match_and_learn will fail if there are several different post-states 
 connected to the pre-state from the first round. *)

fun match_and_learn_one_match fixed cand pattern trm =
  if not (is_match pattern trm)
  then cand
  else
    let val s = match_term pattern trm |> fst |> List.filter (not o is_underscore_redex) in
      if not (consistent_on pattern s fixed)
      then cand
      else 
        let
          val erm = mk_HOL_ERR "toolBoxLib" "match_and_learn_one_match fixed"
          val _ = if not (consistent_on pattern s cand) then raise (erm "inconsistent input terms") else ()
        in 
          (cand@s)
        end
    end;

fun match_and_learn_one_round fixed (plst, ilst) =
     foldX (fn (p,i,c) => c@(match_and_learn_one_match fixed c p i) |> remove_redundancy_simp) (plst, ilst) fixed;

fun match_and_learn roundlist =
     List.foldl (fn (pr, s) => s@(match_and_learn_one_round s pr)  |> remove_redundancy_simp) [] roundlist;


end

