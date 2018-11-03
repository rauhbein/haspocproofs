structure annotationsLib  =
struct

open HolKernel boolLib bossLib;



val trivial_true = prove(``T``, SIMP_TAC bool_ss []);

fun hide_away (bname, cname, trm) =
    case free_vars trm
      of [] => let
                 val var_trm = mk_var (bname ^ "__" ^ cname, ``:bool``)
                 val the_def = Define `^var_trm = ^trm`
               in
                 the_def
               end
        | p => let
                 val params = pairLib.list_mk_pair p
                 val pty = type_of params
                 val var_trm = mk_var (bname ^ "__" ^ cname, ``:^pty -> bool``)
                 val the_def = Define `^var_trm ^params = ^trm`
               in
                 the_def
               end;
    

fun store_conjuncts (basename:string, l1 : thm list, l2: (string*term) list) =
    case (l1,l2)
       of ([], _) => []
       |  (_, []) => []
       |  (th::l1', (n,tr)::l2') => if ((n <> "") andalso (concl th = tr))
                                then 
                                 let 
                                    val clear_thm  = save_thm(basename ^ "_'_" ^ n, GEN_ALL (DISCH_ALL th))
                                    val hide_def = hide_away(basename, n, tr)
                                    val hidden_thm = save_thm(basename ^ "_''_" ^n, REWRITE_RULE[hide_def |> SPEC_ALL |> SYM |> GEN_ALL] clear_thm)
                                 in hide_def::(store_conjuncts (basename,l1',l2')) 
                                 end                                 
                                else store_conjuncts (basename, l1', l2');


fun new_annotated_axiom (name:string, cond:term, lst:(string *term) list) =
    let
       val conj = list_mk_conj (map snd lst)
       val imp = if (cond = ``T``) then conj else mk_imp(cond,conj)
       val ax = new_axiom(name, gen_all imp)
       val hide_defs = store_conjuncts (name, SPEC_ALL ax |> UNDISCH_ALL |> CONJUNCTS, lst)
       val hide_thm = save_thm (name ^ "_''", REWRITE_RULE (map (GEN_ALL o SYM o SPEC_ALL) hide_defs) ax)
    in 
     ax
    end;

fun store_annotated_thm (name, cond:term, lst:(string *term) list, proof) =
    let
       val conj = list_mk_conj (map snd lst)
       val imp = if (cond = ``T``) then conj else mk_imp(cond,conj)
       val th = store_thm(name, gen_all imp, proof)
       val hide_defs = store_conjuncts (name, SPEC_ALL th |> UNDISCH_ALL |> CONJUNCTS, lst)
       val hide_thm = save_thm (name ^ "_''", REWRITE_RULE (map (GEN_ALL o SYM o SPEC_ALL) hide_defs) th)
    in 
     th
    end;

fun get_thm_name th =
    (map axioms ((current_theory())::(ancestry "-")))@(map theorems ((current_theory())::(ancestry "-"))) |> flatten |> List.find (fn (n,t) => (concl t = concl th)) |> Option.map fst;


fun get_annotated_conjuncts th =
    case get_thm_name th
      of NONE => []
       | SOME n => (DB.find (n^"_'_") |> map (fn ((try, tn),(t,c)) => (String.extract(tn,3+String.size n,NONE),t)));
    

fun get_annotated_conj (th:thm, key:string) =
    case List.find (fn (n,t) => (n=key)) (rev (get_annotated_conjuncts th)) 
      of NONE => trivial_true
       | SOME (n,t) => t;


fun HIDE th = 
    case (get_thm_name th)
      of NONE => th
       | SOME n => case ((map theorems ((current_theory())::(ancestry "-"))) |> flatten |> List.find (fn (n',t) => (n'= n^"_''")) |> Option.map snd)
                   of NONE => th
                    | SOME th' => th';


fun DefOf n =
    valOf ((map definitions ((current_theory())::(ancestry "-"))) |> flatten |> List.find (fn (n',t) => (n'= n^"_def")) |> Option.map snd);



infix 0 //;
infix 0 ///;
infix 0 -:;

fun (th:thm) // (str:string) = get_annotated_conj(th,str);
fun (th:thm) /// (n:int) = List.nth(SPEC_ALL th |> UNDISCH_ALL |> CONJUNCTS, n) |> DISCH_ALL |> GEN_ALL;
fun a -: b = (a,b);

(* TODO: definitions (f(p,q) = ?x y z. A(p,q,x) /\ B(y,q)) *)



(*

open parametersTheory;

val new_goodP_axiom = new_annotated_axiom("new_goodP_axiom",
``EVEN dummy``,
["channel_source_bound" -:
 ``!s. (s < PAR.ns) ==> (FST(PAR.cpol s) < PAR.ng)``,
 "channel_target_bound" -:
 ``!s. (s < PAR.ns) ==> (SND(PAR.cpol s) < PAR.ng)``,
 "unique_channels" -:
 ``!s s'. (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s') ==> (PAR.cpol(s) <> PAR.cpol(s'))``,
 "channel_nonrefl" -:
 ``!s g. (s < PAR.ns) ==> PAR.cpol(s) <> (g,g)``,
 "unique_source_address" -:
 ``!s s'.  (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s') ==> (FST(PAR.cpol s) = FST(PAR.cpol s')) ==> (FST(PAR.igca s) <> FST(PAR.igca s'))``,
 "unique_target_address" -:
 ``!s s'.  (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s') ==> (SND(PAR.cpol s) = SND(PAR.cpol s')) ==> (SND(PAR.igca s) <> SND(PAR.igca s'))``,
 "peripheral_interrupts" -: 
 ``!g pe i. (i IN (PAR.pirq_gp g pe)) ==> (?n. (i = PIR n))``,
 "" -:
 ``!s g g'. (s < PAR.ns) ==> (PAR.cpol s = (g,g')) ==> ((FST (PAR.igca s)) IN (PAR.A_G g))``,
 "" -:
 ``!s g g'. (s < PAR.ns) ==> (PAR.cpol s = (g,g')) ==> ((SND (PAR.igca s)) IN (PAR.A_G g'))``,
 "" -:
 ``!g pe. (PAR.A_gp g pe) PSUBSET (PAR.A_G g)``,
 "dummy" -:
 ``PAR.ng < dummy +2``
]);


new_goodP_axiom;
new_goodP_axiom // "channel_target_bound";
new_goodP_axiom // "non_existing";
new_goodP_axiom // "";
new_goodP_axiom // "dummy";
new_goodP_axiom /// 3;
get_annotated_conjuncts new_goodP_axiom;
HIDE new_goodP_axiom;
DefOf "new_goodP_axiom__dummy";

*)


(* OLD implementation with references:

type annotated_thm = {name: string, full:thm, compact:thm, lst: (string*term) list};

val annotation_net = ref (LVTermNet.empty : (annotated_thm LVTermNet.lvtermnet));

fun add_to_annotation_net (x:annotated_thm) =
    annotation_net := LVTermNet.insert ((!annotation_net), ([], x |> #full |> concl), x);

fun reset_annotation_net () =
    annotation_net :=  (LVTermNet.empty : (annotated_thm LVTermNet.lvtermnet));

fun find_in_annotation_net tm =
    case (LVTermNet.find (!annotation_net, ([],tm)))
      of [] => NONE
      | (x::lst) => SOME (x);

fun new_annotated_axiom (name:string, cond:term, lst:(string *term) list) =
    let
       val conj = list_mk_conj (map snd lst)
       val imp = if (cond = ``T``) then conj else mk_imp(cond,conj)
       val ax = new_axiom(name, gen_all imp)
       val _ = add_to_annotation_net {name = name, full = ax, compact = ax, lst = lst}
    in 
     ax
    end;

fun source (th:thm) =
    case find_in_annotation_net (concl th)
       of NONE => NONE
        | SOME x => SOME (#lst x);



fun thm_from_annotated_list (l1 : thm list, l2: (string*term) list, key:string) =
    case (l1,l2)
       of ([], _) => NONE
       |  (_, []) => NONE
       |  (x1::l1', x2::l2') => if ((key = fst x2) andalso (concl x1 = snd x2))
                             then SOME x1 
                             else thm_from_annotated_list (l1',l2',key);


fun get_annotated_conj (th:thm, key:string) =
    case find_in_annotation_net (concl th)
       of NONE => trivial_true
        | SOME x => case thm_from_annotated_list(SPEC_ALL th |> UNDISCH_ALL |> CONJUNCTS, #lst x,key)
                        of NONE => trivial_true
                         | SOME t => GEN_ALL (DISCH_ALL t);


*)

end
