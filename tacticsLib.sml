structure tacticsLib :> tacticsLib =
struct

    open HolKernel boolLib bossLib;
    open toolboxLib;


(* 
   this library is a collection of generally useful
   tactics, convertions, rules, term manipulation ... 
*)
val ERR = mk_HOL_ERR "tacticsLib"



(* the following fix allows to use the new name PAT_X_ASSAM 
   for the old behaviour of PAT_ASSAM in all versions of HOL *)	
local
    val PAT_X_ASSUM = PAT_ASSUM
    open Tactical
  in
    val PAT_X_ASSUM = PAT_X_ASSUM
end

(* simplify a term *)
fun SIMP_TERM ss lst trm =
    rhs (concl (SIMP_CONV ss lst trm handle _ => REFL trm));


val UNDISCH_MATCH_TAC = fn MATCH => (PAT_X_ASSUM MATCH (fn th => (MP_TAC th)));
val UNDISCH_ALL_TAC = (REPEAT (UNDISCH_MATCH_TAC ``X``));
val SPEC_ASSUM_TAC = fn (MATCH, SLIST) => (REPEAT (PAT_X_ASSUM MATCH (fn th => ASSUME_TAC (SPECL SLIST th))));
val SPEC_AND_KEEP_ASSUM_TAC = fn (MATCH, SLIST) => (PAT_X_ASSUM MATCH (fn th => ASSUME_TAC th THEN ASSUME_TAC (SPECL SLIST th)));
val THROW_AWAY_TAC = fn MATCH => (REPEAT (PAT_X_ASSUM MATCH (fn th => IMP_RES_TAC th)));
val THROW_ONE_AWAY_TAC = fn MATCH => (PAT_X_ASSUM MATCH (fn th => IMP_RES_TAC th));
val THROW_AWAY_IMPLICATIONS_TAC = (REPEAT (WEAKEN_TAC is_imp));
val ASSERT_ASSUM_TAC = fn MATCH => (PAT_X_ASSUM MATCH (fn th => ASSUME_TAC th));
val PROTECTED_RW_TAC = fn MATCH => (PAT_X_ASSUM MATCH (fn th => (RW_TAC (srw_ss()) [] THEN ASSUME_TAC th)));
val PROTECTED_OR_RW_TAC = fn RWLIST => (PAT_X_ASSUM ``X \/ Y`` (fn th => (RW_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (RW_TAC (srw_ss()) RWLIST);
val PROTECTED_OR_SIMP_TAC = fn RWLIST => (PAT_X_ASSUM ``X \/ Y`` (fn th => (FULL_SIMP_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (FULL_SIMP_TAC (srw_ss()) RWLIST);
val CONJ_ASSUM_TAC = (REPEAT (PAT_X_ASSUM ``A /\ AA`` (fn th => ASSUME_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT2 th))));
fun FORCE_REWRITE_TAC thm = (let val (_, trm) = dest_thm (SPEC_ALL thm)
                                 val (ab, c) = dest_comb trm
                                 val (a, b) = dest_comb ab
                             in SUBGOAL_THEN c (fn sgl => ASSUME_TAC thm THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                             end) handle _ => ALL_TAC;
fun FORCE_REV_REWRITE_TAC thm = (let val (_, trm) = dest_thm (SPEC_ALL thm)
                                 val (ab, c) = dest_comb trm
                                 val (a, b) = dest_comb ab
                             in SUBGOAL_THEN b (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                             end) handle _ => ALL_TAC;


val ASSUME_SPECL_TAC = 
fn l => fn thm => ASSUME_TAC (SPECL l thm);

val ASSUME_SIMP_TAC = 
fn l => fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) l thm);

val IMP_RES_SIMP_TAC = 
fn l => fn thm => IMP_RES_TAC (SIMP_RULE (srw_ss()) l thm);


val ASSUME_SPEC_TAC = 
fn l => fn thm => ASSUME_TAC (SPEC l thm);


val ASSUME_SPECL_SIMP_TAC = 
fn l => fn sthms => fn thm => ASSUME_TAC (SPECL l (SIMP_RULE (srw_ss()) sthms thm));

val IMP_RES_SPEC_TAC = 
fn l => fn thm => IMP_RES_TAC (SPEC l thm);

val IMP_RES_SPECL_TAC = 
fn l => fn thm => IMP_RES_TAC (SPECL l thm);

val MP_SPEC_TAC = 
fn l => fn thm => MP_TAC (SPEC l thm);

val MP_SPECL_TAC = 
fn l => fn thm => MP_TAC (SPECL l thm);

val ASSUME_SPECL_INST_TAC =  
 fn sl => fn tl => fn thm =>
	     ASSUME_TAC (SPECL sl (INST_TYPE tl thm)) 


val ASSUME_SPECL_GEN_REWRITE_TAC =
 fn (l , thm, simps) => ASSUME_TAC (SPECL 
					l (GEN_ALL (REWRITE_RULE simps thm)));



fun REDUCE_SIMP splittac = 
    fn gl =>  let val (glist, justif) = (splittac gl) in
              let val minlist = (remove_redundancy_simp glist) in
              let val minjust = (if (glist=minlist)
                                 then justif 
                                 else (fn tlist => (justif (pump_list_simp tlist glist minlist)))) in
              (minlist, minjust)
              end   end   end; 

fun equal_goals g1 g2 =
    (if (g1 = g2)
      then true
    else
      (let val (l1,h1) = g1 in
       let val (l2,h2) = g2 in
         ((h1 = h2) andalso compare_lists l1 l2)
       end end));

fun remove_redundancy_gls lst =
    (case lst
     of []    => []
     |  x::[] => [x]
     |  x::xs => (if (List.exists (fn y => equal_goals x y) xs) then (remove_redundancy_gls xs) else (x::(remove_redundancy_gls xs))));


fun pump_list_gls xs ol ml = 
    snd (ListPair.unzip (List.mapPartial (fn x => List.find (fn (a,b) => equal_goals a x) (ListPair.zip (ml, xs))) ol));


fun REDUCE splittac = 
    fn gl =>  let val (glist, justif) = (splittac gl) in
              let val minlist = (remove_redundancy_gls glist) in
              let val minjust = (if (glist=minlist)
                                 then justif 
                                 else (fn tlist => (justif (pump_list_gls tlist glist minlist)))) in
              (minlist, minjust)
              end   end   end; 


(* demo:

g `((D A = D B)==>  (A=B))   /\ 
   ((D A = D B) ==> (A=B))   /\ 
   ((E X = E Y) ==> (X=Y))   /\ 
   ((R V = R U) ==> (V=U))   /\ 
   ((E X = E Y) ==> (X=Y))   /\ 
   ((D A = D B) ==> (A=B))`;
e(RW_TAC (srw_ss()) []);
e(REDUCE (RW_TAC (srw_ss()) []));

*)

fun emptyt th [] = th
  | emptyt th _ = raise ERR "emptyt" "Bind Error";



fun compose_validation (input:(goal list * validation) list) (theorems:(thm list)) =
    case input of
         [] => []
       | ((g,v)::xs) => (v (List.take(theorems,length g)))::(compose_validation xs (List.drop(theorems, length g))); 

fun DEPTH_TAC d =
  (fn gl => 
    if (d = 0)
           then ALL_TAC gl (*([gl], (fn [th] => th))*)
           else (let val (olst, oval) = (EVAL_TAC 
                  THEN FULL_SIMP_TAC (srw_ss()) [] 
                  THEN RW_TAC (srw_ss()) []   
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN UNDISCH_ALL_TAC) gl
                 val answers = map_until (DEPTH_TAC (d-1)) ALL_TAC (fn (gl,vl) => (gl <> [])) olst
                 in
                      (List.concat (map fst answers), (fn thl => oval (compose_validation answers thl)))
                 end));

fun DEPTH_LIST depthlist =
  (fn gl => 
      case depthlist of
           [] =>  ALL_TAC gl (*([gl], (fn [th] => th))*)
         | (T1::TLIST) => let val (olst, oval) = T1 gl
                 val answers = map_until (DEPTH_LIST TLIST) ALL_TAC (fn (gl,vl) => (gl <> [])) olst
                 in
                      (List.concat (map fst answers), (fn thl => oval (compose_validation answers thl)))
                 end);


fun DEPTH_FIRST depthlist =  (* scheme borrowed from THEN-tactical *)
   fn g =>
     case depthlist of
           [] => (ALL_TAC g)
         | (T1::TLIST) =>
                (let
                   val (gl, vf) = T1 g
                in
                   case itlist
                          (fn goal => fn (G, V, lengths, stop) =>
                            let 
                              val answer = (if stop then (ALL_TAC goal) else ((DEPTH_FIRST TLIST) goal))
                            in
                            case answer of
                               ([], vfun) => let
                                                val th = vfun []
                                             in
                                                (G, emptyt th :: V, 0 :: lengths, false)
                                             end
                             | (goals, vfun) =>
                                  (goals @ G, vfun :: V, length goals :: lengths, true)
                            end)
                          gl ([], [], [], false) of
                      ([], V, _, _) =>
                          ([], let val th = vf (map (fn f => f []) V) in emptyt th end)
                    | (G, V, lengths, _) => (G, (vf o mapshape lengths V))
                end);




fun FST_AND_SND_TAC (asm,gol) =
   let
      val to_split = flatten (map (fn a => find_terms (fn trm => (not (pairSyntax.is_pair trm)) andalso (fst (dest_type ( type_of trm)) = "prod") andalso ((not (is_const (strip_comb trm |> fst))) orelse ((dest_const (strip_comb trm |> fst) |> fst) <> "UNCURRY"))) a) asm)
      val thms = map (fn element => prove (``^element = (FST ^element, SND ^element)``,Cases_on `^element` THEN FULL_SIMP_TAC (srw_ss()) [])) to_split
      val lhsc = lhs o concl
      val HAMED_CONV = (fn trm =>
                            case  List.find (fn t => (lhsc t) = trm) thms
                              of SOME t => t
                               | NONE => raise UNCHANGED)
in
   (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV HAMED_CONV)) THEN CONV_TAC (DEPTH_CONV HAMED_CONV)) (asm,gol)
end; 




fun FST_AND_SND_CONV trm =
   let
      val to_split =  (fn a => find_terms (fn trm => (not (pairSyntax.is_pair trm)) andalso (fst (dest_type ( type_of trm)) = "prod") andalso ((not (is_const (strip_comb trm |> fst))) orelse ((dest_const (strip_comb trm |> fst) |> fst) <> "UNCURRY"))) a) trm
      val thms = map (fn element => prove (``^element = (FST ^element, SND ^element)``,Cases_on `^element` THEN FULL_SIMP_TAC (srw_ss()) [])) to_split
      val lhsc = lhs o concl
      val HAMED_CONV = (fn trm =>
                            case  List.find (fn t => (lhsc t) = trm) thms
                              of SOME t => t
                               | NONE => raise UNCHANGED)
in
   (DEPTH_CONV HAMED_CONV) trm
end; 


val fst_and_snd_flat_lem = prove(``(trm:('a # 'b)) = (FST trm, SND trm)``,
                           Cases_on `trm` THEN  FULL_SIMP_TAC (srw_ss()) []);


val pair_fst_and_snd_flat_lem = prove(``pair_CASE (trm:('a # 'b)) = pair_CASE (FST trm, SND trm)``,
                           Cases_on `trm` THEN  FULL_SIMP_TAC (srw_ss()) []);

(*

val keep_def = Define `keep x = x`;


val pair_fst_and_snd_flat_keep_lem = prove(``pair_CASE (trm:('a # 'b)) = pair_CASE (scratch$keep(FST trm), scratch$keep(SND trm))``,
                           Cases_on `trm` THEN  FULL_SIMP_TAC (srw_ss()) [keep_def]);
*)


fun FST_AND_SND_FLAT_CONV trm =
     if (not ((not (pairSyntax.is_pair trm)) andalso (fst (dest_type ( type_of trm)) = "prod") andalso ((not (is_const (strip_comb trm |> fst))) orelse ((dest_const (strip_comb trm |> fst) |> fst) <> "UNCURRY")))) then raise UNCHANGED
     else
       prove (``^trm = (FST ^trm, SND ^trm)``,Cases_on `^trm` THEN FULL_SIMP_TAC (srw_ss()) []);
     

fun FST_AND_SND_FLAT_CONV2 trm =
     if (not ((not (pairSyntax.is_pair trm)) andalso (fst (dest_type ( type_of trm)) = "prod") andalso ((not (is_const (strip_comb trm |> fst))) orelse ((dest_const (strip_comb trm |> fst) |> fst) <> "UNCURRY")))) then raise UNCHANGED
     else
       PURE_ONCE_REWRITE_CONV [fst_and_snd_flat_lem] trm;

fun FST_AND_SND_STRICT_CONV trm =
     if (not ((fst (dest_type ( type_of trm)) = "prod"))) then raise UNCHANGED
     else
       prove (``^trm = (FST ^trm, SND ^trm)``,Cases_on `^trm` THEN FULL_SIMP_TAC (srw_ss()) []);


fun FST_AND_SND_STRICT_CONV2 trm =
     if (not ((fst (dest_type ( type_of trm)) = "prod"))) then raise UNCHANGED
     else
       PURE_ONCE_REWRITE_CONV [fst_and_snd_flat_lem] trm;

fun FST_AND_SND_ON_VARS_CONV trm =
     if (not ((is_var trm) andalso (fst (dest_type ( type_of trm)) = "prod"))) then raise UNCHANGED
     else
       PURE_ONCE_REWRITE_CONV [fst_and_snd_flat_lem] trm;

fun FST_AND_SND_ON_CASE_VARS_CONV trm =
     if (not (fst (dest_const (fst (dest_comb trm))) = "pair_CASE")) orelse 
        (not (is_var (snd (dest_comb trm)))) then raise UNCHANGED
     else
       PURE_ONCE_REWRITE_CONV [pair_fst_and_snd_flat_lem] trm;

(*

fun FST_AND_SND_ON_CASE_VARS_CONV2 trm =
     if (not (fst (dest_const (fst (dest_comb trm))) = "pair_CASE")) orelse 
        (not (is_var (snd (dest_comb trm)))) then raise UNCHANGED
     else
       (PURE_ONCE_REWRITE_CONV [pair_fst_and_snd_flat_keep_lem] THENC SIMP_CONV (srw_ss()) []) trm;
*)

fun FST_AND_SND_RULE thm =
    CONV_RULE FST_AND_SND_CONV thm;




(* like CHANGED_TAC, but also reacting to alpha-equivalent goals
   - the tactic undisch first *)

fun ALPHA_CHANGED_TAC tac (asm,gol) =
    let
      val (newgls, p) = tac (asm,gol)
    in
      case newgls 
        of [] => ([], p)
         | [ng] => let
                     val (ung, unp) = (UNDISCH_ALL_TAC ng)
                     val (ug, up) = (UNDISCH_ALL_TAC (asm,gol))
                   in
                     case (ung,ug) 
                       of ([(ungl,ung')],[(ugl,ug')]) => if (aconv ung' ug') then NO_TAC (asm,gol)
                                            else (newgls,p)
                       | _ => (newgls, p)
                   end
         | _ => (newgls,p)
    end;



fun term_by claim proof = 
    (SUBGOAL_THEN claim ASSUME_TAC) THENL [proof, ALL_TAC];

fun LIMITED_METIS_TAC n =
    let 
       val metis_param  = ({interface = #interface metisTools.defaults, limit = ({time = (NONE:real option), infs = SOME (n:int)}:metisTools.limit), solver = #solver metisTools.defaults}:metisTools.parameters);
    in
       metisTools.GEN_METIS_TAC metis_param
    end;

fun TIME_LIMITED_METIS_TAC t lst (asm,gl) =
    (with_flag (metisTools.limit, {time = (SOME t:real option), infs = (NONE:int option)}) (METIS_TAC lst)) (asm,gl);

fun INFS_LIMITED_METIS_TAC i lst (asm,gl) =
    (with_flag (metisTools.limit, {time = (NONE:real option), infs = (SOME i:int option)}) (METIS_TAC lst)) (asm,gl);


(* in the following we copy something from schneiderUtils
   since importing the entire library conflicts with our definitions *)
fun elem_ 0 l = hd l | elem_ i l = elem_ (i-1) (tl l)
fun delete_ i l = if i=0 then tl l
		 else (hd l)::(delete_ (i-1) (tl l))
fun POP_NO_ASSUM_ i thfun (asl,w) = thfun (ASSUME (elem_ i asl)) ((delete_ i asl),w)
fun POP_NO_TAC_ i = POP_NO_ASSUM_ i (fn x=> ALL_TAC)


fun THROW_NO_TAC n (asml,gl) =
    POP_NO_TAC_ (length asml - n - 1) (asml,gl);

fun PRINT_TAC str (asm,gl) =
     let val _ = print str in ALL_TAC (asm,gl) end;


(* tactical to ignore matching goals *)
fun EXCEPT_FOR trm tac (asm, gl) =
    if is_match trm gl
    then ALL_TAC (asm, gl)
    else tac (asm, gl);

fun EXCEPT_FOR_THESE trmlst tac (asm, gl) =
    case List.find (fn trm => is_match trm gl) trmlst
     of NONE => tac (asm,gl)
     | SOME x => ALL_TAC (asm,gl);

fun ONLY_FOR trm tac (asm, gl) =
    if is_match trm gl
    then tac (asm, gl)
    else ALL_TAC (asm, gl);

fun ONLY_FOR_THESE trmlst tac (asm, gl) =
    case List.find (fn trm => is_match trm gl) trmlst
     of NONE => ALL_TAC (asm,gl)
     | SOME x => tac (asm,gl);




(******** existential reasoning **********)


(* instantiate existentially quantified variables in goal
   with their exact name *)
fun FEED_EXISTS_TAC (asm,gol) =
     let
          val (var, _) = dest_exists gol
          val nvar =(case fst (dest_var var) of
                          _ => var)
          in
             (EXISTS_TAC nvar) (asm,gol)
     end; 


(* move an existentially quantified variable to the front *)
fun REORDER_EXISTS_TAC front  =
        CONV_TAC (RESORT_EXISTS_CONV (fn elist => front::(List.filter (fn el => el <> front) elist)));

(* move existentially quantified variables of a certain type to the front *)
fun TYPE_REORDER_EXISTS_TAC etype  =
    let
        val transf = (fn elist =>
                         let
                             val agree_on_type = List.filter (fn el => (type_of el) = etype) elist;
                             val disagree_on_type = List.filter (fn el => (type_of el) <> etype) elist;
                         in
                             (agree_on_type@disagree_on_type)
                         end)
    in
       CONV_TAC (RESORT_EXISTS_CONV transf)
    end;

(* like TYPE_REORDER_EXISTS_TAC, but fails if no success *)
fun TYPE_REORDER_EXISTS_OR_FAIL_TAC etype  =
    let
        val transf = (fn elist =>
                         let
                             val agree_on_type = List.filter (fn el => (type_of el) = etype) elist;
                             val _ = (if (agree_on_type = []) then fail() else ());
                             val disagree_on_type = List.filter (fn el => (type_of el) <> etype) elist;
                         in
                             (agree_on_type@disagree_on_type)
                         end)
    in
       CONV_TAC (RESORT_EXISTS_CONV transf)
    end;


(* instantiates the first variable that matches the type of the parameter;
   side effect: all other variables of that type will be in front afterwards *)
fun FIRST_EXISTS_TAC trm =
    TYPE_REORDER_EXISTS_OR_FAIL_TAC (type_of trm) THEN EXISTS_TAC trm;


(* not exported set functions *)
fun has_intersection (l1:term list) l2 =
    foldl (fn (b,res) => res orelse b)  false (map (fn e2 => List.exists (fn e1 => e1 = e2) l1) l2);
fun find_independent_set connected_fn (I:term list) Q R =
    case Q 
      of [] => (I,R)
      | (x::xs) => 
            let
               val (Rq,Rr) = partition (connected_fn x) R
            in
               find_independent_set connected_fn (x::I) (xs@Rq) Rr
            end;

(* split existential goal into independent existential goals
   or reorder the existentially quantified variables,
   tactics come in different flavours *)
fun SPLIT_EXIST_CONV trm =
  let
    val _ = if (is_exists trm) then () else raise UNCHANGED
    val strm = (snd o strip_exists) trm
    val _ = if (is_conj strm) then () else raise UNCHANGED
    val (c1,cl) = case remove_redundancy_simp (strip_conj strm)
	            of [] => raise UNCHANGED
	           | (x1::xl) => (x1,xl)
    val (C1,C2) = find_independent_set (fn t1 => fn t2 => has_intersection (free_vars t1) (free_vars t2)) ([]:term list) [c1] cl
    val _ = if (C2 = [] orelse C1 = []) then raise UNCHANGED else ()
    val newtrm = mk_conj (list_mk_exists(free_vars (list_mk_conj C1), (list_mk_conj C1)),
                          list_mk_exists(free_vars (list_mk_conj C2), (list_mk_conj C2)))
  in
     prove(``^trm = ^newtrm``, METIS_TAC [])
  end;
val SPLIT_EXIST_TAC  =
  REPEAT ((CONV_TAC SPLIT_EXIST_CONV) THEN CONJ_TAC);
val SPLIT_EXIST_TAC2 =
  (CONV_TAC (DEPTH_CONV EXISTS_AND_REORDER_CONV) THEN (REPEAT CONJ_TAC));
val SPLIT_EXIST_TAC3 =
  (CONV_TAC (DEPTH_CONV EXISTS_AND_CONV) THEN (REPEAT CONJ_TAC) THEN CONV_TAC (DEPTH_CONV AND_EXISTS_CONV));
val SPLIT_EXIST_TAC4 =
  (CONV_TAC (DEPTH_CONV EXISTS_AND_REORDER_CONV) THEN (REPEAT CONJ_TAC) THEN CONV_TAC (REDEPTH_CONV RIGHT_AND_EXISTS_CONV) THEN CONV_TAC (REDEPTH_CONV LEFT_AND_EXISTS_CONV));
val SPLIT_EXIST_TAC5 =
  (CONV_TAC (DEPTH_CONV EXISTS_AND_REORDER_CONV) THEN (REPEAT CONJ_TAC) THEN CONV_TAC (REDEPTH_CONV (RIGHT_AND_EXISTS_CONV THENC LEFT_AND_EXISTS_CONV)));
val SPLIT_EXIST_TAC6 =
    (REPEAT (CHANGED_TAC (SPLIT_EXIST_TAC5 THEN SPLIT_EXIST_TAC4)));


(* also quite useful for existential reasoning:
   FULL_SIMP_TAC  ((srw_ss()) ++(quantHeuristicsLib.QUANT_INST_ss [quantHeuristicsLib.std_qp])) [] *)



(***************** HASPOC ****************************
   rather specific to the HASPOC proof,
   but independent from project specific definitions *)


(* check if a term is a predicate constant that states
   whether a component can perform a certain step
   from the given pre-state to the given post-state *)
fun is_step_predicate tm =
    let
      val ty = type_of tm
    in
              (is_const tm) 
      andalso (      (is_type_match ``:'a # 'a -> bool`` ty)
              orelse (is_type_match ``:'a # 'b # 'a -> bool`` ty)
              orelse (is_type_match ``:'a # 'b # 'c # 'a -> bool`` ty)
              orelse (is_type_match ``:'a # 'b # 'c # 'd # 'a -> bool`` ty))
    end;

(* a tactic that looks for step predicates (see above)
   and filters the given theorem/axiom-list 
   before mapping that list to another/provided theorem-tactic *)
fun FIND_STEP_PREDICATES_TAC lst the_thm_tactic (asm, gl) =
    let
      val predicates = map (find_terms is_step_predicate) asm |> flatten
      val axioms = map (fn predicate => filter (fn a => there_is_some predicate (concl a)) lst) predicates
                   |> flatten |> remove_redundancy_by_eq (fn x => fn y => (concl x = concl y))
    in
      (MAP_EVERY the_thm_tactic axioms) (asm,gl)
    end;

(* puts premises of a theorem forward that involve step predicates
   -- helps with IMP_RES_TAC *)
fun STEP_PREDICATE_FIRST_RULE thm =
    let 
       val und_thm = UNDISCH_ALL (SPEC_ALL thm)
       val (pre,conc) = dest_thm und_thm
       val pre = map strip_conj pre |> flatten
       val (pre1,pre2) = List.partition (fn t => find_term_opt is_step_predicate t <> NONE) pre
       val disc_thm = List.foldr (uncurry DISCH) (DISCH_ALL und_thm) (pre1@pre2)
    in
      GEN_ALL (SIMP_RULE bool_ss [] disc_thm)
    end;



end
