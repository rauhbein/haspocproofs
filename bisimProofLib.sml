structure bisimProofLib   =
struct

open HolKernel boolLib bossLib;

open toolboxLib;
open tacticsLib;

open haspoctypesTheory;
open axfuncsTheory;
open hypervisorTheory;
open idealTheory;
open idealInvProofTheory;
open refinedTheory;
open refinedInvTheory;
open bisimTheory;

open haspocLib;

open annotationsLib; infix //; infix ///; infix -:;

val ERR = mk_HOL_ERR "bisimProofLib";

(************ flags  ************)



datatype MemOpType = NoMem | HarmlessMem | GICMem;
datatype AnnotationType = withAnnotations | withoutAnnotations;


(*********** grouped definitions and theorems *********************)


val bisim_definitions =
  [bisim_corereq_guest_def, bisim_corereq_hyp_def, bisim_corereq_gicd_def,bisim_gicdmsg_ideal_def, bisim_mmureq_guest_def, bisim_gicdmsg_refined_def, bisim_gicdreq_ideal_def, bisim_gicdreq_refined_def, bisim_gicd_fail_def, bisim_perirq_def, bisim_igcirq_def, bisim_sgiirq_def, bisim_memory_def, bisim_periph_def, bisim_smmureq_def, bisim_giccreq_def, bisim_memreq_def, bisim_ext_def, bisim_psci_def, bisim_gicc_reg_def, bisim_gicd_reg_def, bisim_pi_def, bisim_ctx_def, bisim_send_igc_def];

val bisim_core_definitions = 
  [bisim_gicdmsg_ideal_core_def, bisim_corereq_guest_core_def, bisim_corereq_hyp_core_def, bisim_corereq_gicd_core_def, bisim_mmureq_guest_core_def, bisim_gicdmsg_refined_core_def, bisim_gicdreq_ideal_core_def, bisim_gicdreq_refined_core_def, bisim_perirq_core_def, bisim_igcirq_core_def, bisim_sgiirq_core_def, bisim_ctx_core_def, bisim_send_igc_core_def, bisim_gicdreq_fail_core_def, bisim_pi_guest_def];

val idg_parts =
  [id_inv_unique_rpl_def, id_inv_cifreq_def, id_inv_pifreq_def, id_inv_perreq_def, id_inv_cifadr_def, id_inv_pifadr_def, id_inv_ioreq_def, id_inv_pifrpl_def, id_inv_memrpl_def, id_inv_mem_reqsent_def, id_inv_gic_q_def, id_inv_gic_pi_def, inv_good_idcore_def, inv_good_mem_def, inv_good_per_def, idg_inv_def, id_inv_cifrpl_def];



(************ general proof machinery for bisim proofs  ************)



(* check if a term looks like a bisim predicate *)
fun is_bisim_predicate tm =
    let
      val ty = type_of tm
    in
              (is_const tm) 
      andalso (is_type_match ``:refined_model # ideal_model -> bool`` ty)
    end;

(* a tactic that looks for bisim predicates in assumption list
   and filters the given theorem/axiom-list 
   before mapping that list to another/provided theorem-tactic *)
fun FIND_BISIM_PREDICATES_IN_PREMISES_TAC lst the_thm_tactic (asm, gl) =
    let
      val predicates = map (find_terms is_bisim_predicate) asm |> flatten
      val axioms = map (fn predicate => filter (fn a => there_is_some predicate (concl a)) lst) predicates
                   |> flatten |> remove_redundancy_by_eq (fn x => fn y => (concl x = concl y))
    in
      (MAP_EVERY the_thm_tactic axioms) (asm,gl)
    end;

(* a tactic that looks for bisim predicates in goal
   and filters the given theorem/axiom-list 
   before mapping that list to another/provided theorem-tactic *)
fun FIND_BISIM_PREDICATES_IN_GOAL_TAC lst the_thm_tactic (asm, gl) =
    let
      val predicates = find_terms is_bisim_predicate gl
      val axioms = map (fn predicate => filter (fn a => there_is_some predicate (concl a)) lst) predicates
                   |> flatten |> remove_redundancy_by_eq (fn x => fn y => (concl x = concl y))
    in
      (MAP_EVERY the_thm_tactic axioms) (asm,gl)
    end;

(* like FIND_BISIM_PREDICATES_IN_GOAL_TAC,
   but instantiates theorems with state terms from goal *)
fun SPEC_BISIM_FROM_GOAL_TAC lst the_thm_tactic (asm, gl) =
    let
      val predicates = find_terms is_bisim_predicate gl
      val axioms = map (fn predicate => filter (fn a => there_is_some predicate (concl a)) lst) predicates
                   |> flatten |> remove_redundancy_by_eq (fn x => fn y => (concl x = concl y))
      val ref_state_trm = find_term_opt ((is_type_match ``:refined_model``) o type_of) gl
      val id_state_trm = find_term_opt ((is_type_match ``:ideal_model``) o type_of) gl
      val axioms = case ref_state_trm of
                           NONE => axioms
                         | SOME rs => map (fn t => SPECL [``RM:refined_model``, rs] t handle _ => t) axioms
      val axioms = case id_state_trm of
                           NONE => axioms
                         | SOME is => map (fn t => SPECL [``IM:ideal_model``, is] t handle _ => t) axioms
   in
        (MAP_EVERY the_thm_tactic axioms) (asm,gl)
    end;

(* instantiate universally quantified premises with states of the assumption list *)
fun RES_SPEC_WITH_STATES_FROM_PREMISES_TAC keep (asm,gl) =
    let
      val id_states = map (find_terms ((is_type_match ``:ideal_model``) o type_of)) asm |> flatten |> remove_redundancy_simp |> List.filter (fn x => (x <> ``ARB:ideal_model``))
      val ref_states = map (find_terms ((is_type_match ``:refined_model``) o type_of)) asm |> flatten |> remove_redundancy_simp |> List.filter (fn x => (x <> ``ARB:refined_model``))
      val tact = TRY (PAT_X_ASSUM ``!IM:ideal_model. X`` (fn t => (if keep then ASSUME_TAC t else ALL_TAC) THEN MAP_EVERY (fn s => ASSUME_TAC (SPEC s t)) id_states))
      THEN TRY (PAT_X_ASSUM ``!RM:refined_model. X`` (fn t =>  (if keep then ASSUME_TAC t else ALL_TAC) THEN MAP_EVERY (fn s => ASSUME_TAC (SPEC s t)) ref_states))
    in
        tact (asm,gl)   
    end;

(* instantiate universally quantified premises with states of the goal *)
fun RES_SPEC_WITH_STATES_FROM_GOAL_TAC keep (asm,gl) =
    let
      val id_states = map (find_terms ((is_type_match ``:ideal_model``) o type_of)) [gl] |> flatten |> remove_redundancy_simp |> List.filter (fn x => (x <> ``ARB:ideal_model``))
      val ref_states = map (find_terms ((is_type_match ``:refined_model``) o type_of)) [gl] |> flatten |> remove_redundancy_simp |> List.filter (fn x => (x <> ``ARB:refined_model``))
      val tact = TRY (PAT_X_ASSUM ``!IM:ideal_model. X`` (fn t => (if keep then ASSUME_TAC t else ALL_TAC) THEN MAP_EVERY (fn s => ASSUME_TAC (SPEC s t)) id_states))
      THEN TRY (PAT_X_ASSUM ``!RM:refined_model. X`` (fn t =>  (if keep then ASSUME_TAC t else ALL_TAC) THEN MAP_EVERY (fn s => ASSUME_TAC (SPEC s t)) ref_states))
    in
        tact (asm,gl)   
    end;

(* takes a functional goal and uses a corresponding theorem from a list to apply a given tactic *)
fun APPLY_TAC_WITH_THM_FROM_LIST_FOR_FUNC_GOAL lst thm_tac (ass,goal) =
    let val (function, _) = strip_comb goal
	val thm_op = List.find (fn thm => 
  (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) thm = function
				     ) lst
    in if isSome thm_op then
	   (thm_tac (valOf thm_op))(ass, goal)
       else ALL_TAC (ass, goal)
    end;



(* unfolds the definition of all ideal guest transitions mentioned in the
   (existential) goal *)
fun UNFOLD_IDEAL_TRANS_IN_GOAL_TAC (asm,gl) = 
 let
  (* preprocessing input *) 
  val idsteps_in_goal = find_terms (is_match ``ideal_guest_trans(G0,g,step,G1)``) gl
                        |> remove_redundancy_simp
  (* rewrite transition *)  
  val evthms = map (computeLib.RESTR_EVAL_CONV [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``, ``base_adr``, ``Frpl``, ``gicd_req_ok``]) idsteps_in_goal
 in
  (RW_TAC std_ss evthms) (asm, gl)
 end;


(* EVAL-unfolds the definition of the current refined transition in the premises,
   current = matching the refined state of the one and only SIM predicate,
   boolean parameter indicates whether to keep step predicate or not *)
fun UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC keep (asm,gl) = 
 let
  (* preprocessing input *)
  val erm = mk_HOL_ERR "bisimProofLib" "UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC"
  val sims = map (fn a =>  [match_term ``SIM(the_rPreState,the_iPreState)`` a] handle _ => []) asm 
             |> flatten |> remove_redundancy_simp
  val sim = case sims of
              [] => raise (erm "no simulation relation established in premises")
            | (s::[]) => #1 s
            | _ => raise (erm "too many simulation relations provided in premises")
 val refsteps = List.filter (is_match ``refined_trans(the_rPreState,x,the_rPostState)``) asm 
               |> remove_redundancy_simp 
               |> List.filter (fn rs => (subst sim ``the_rPreState:refined_model``) = (dest_comb rs |> #2 |> pairLib.dest_pair |> #1)) 
  (* rewrite tact *)  
  val evthms = map (computeLib.RESTR_EVAL_CONV [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``, ``base_adr``, ``Frpl``, ``gicd_req_ok``, ``mode``, ``MODE``, ``Mode``, ``gicAR``]) refsteps
  val tact = (fn r => UNDISCH_THEN r (fn t => (if keep then ASSUME_TAC t else ALL_TAC) 
                                       THEN ASSUME_TAC (REWRITE_RULE evthms t)))
 in
  (MAP_EVERY tact refsteps) (asm, gl)
 end;


(* carefully unfolds the definition of the current refined transition in the premises;
   current = matching the refined state of the one and only SIM predicate;
   boolean parameter indicates whether to keep step predicate or not;
   carefully means through rewriting of selected definitions rather than applying EVAL,
   especially useful for transitions that boil down to more than just uninterpreted step predicates;
   NOTE: the rewrite list still needs to be filled with more definitions
         to support more transitions *)
fun CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC keep (asm,gl)  =
 let
  (* rewrite list *)
  val rwlst = [refined_trans_def, ref_rule_hv_internal_def, hv_step_def, hv_ts_def, UNIQUE_REQ ref_rule_core_rcv_mrpl_def, UNIQUE_REQ ref_rule_per_rcv_dmarpl_def, per_step_def, refcore_step_def, mmu_step_def, ref_rule_per_rcv_pev_def, ref_rule_mem_internal_def, mem_step_def]
  (* preprocessing input *)
  val erm = mk_HOL_ERR "bisimProofLib" "CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC"
  val sims = map (fn a =>  [match_term ``SIM(the_rPreState,the_iPreState)`` a] handle _ => []) asm 
             |> flatten |> remove_redundancy_simp
  val sim = case sims of
              [] => raise (erm "no simulation relation established in premises")
            | (s::[]) => #1 s
            | _ => raise (erm "too many simulation relations provided in premises")
  val refsteps = List.filter (is_match ``refined_trans(the_rPreState,x,the_rPostState)``) asm 
               |> remove_redundancy_simp 
               |> List.filter (fn rs => (subst sim ``the_rPreState:refined_model``) = (dest_comb rs |> #2 |> pairLib.dest_pair |> #1))
  val rule_res = List.filter (is_match ``hv_rule (_, _, _) = _ ``) asm 
               |> remove_redundancy_simp 
  (* rewrite tact *)  
  val evthms = map (fn rs =>
                    List.foldl (uncurry DISCH) (SIMP_CONV (srw_ss()) rwlst rs) rule_res
                    |> SIMP_RULE (srw_ss()) []) refsteps
  val tact = (fn (r,et) => UNDISCH_THEN r (fn t => ASSUME_TAC t
                                                   THEN TRY (CHANGED_TAC (REV_FULL_SIMP_TAC bool_ss [et] THEN
                                                                              FULL_SIMP_TAC bool_ss [et])
                                                             THEN (if keep then ASSUME_TAC t else ALL_TAC))))
 in
   (MAP_EVERY tact (ListPair.zip(refsteps,evthms))) (asm, gl)
 end;


(* unfolds all refined transitions (and possibly more) 
   through rewriting selected definitions rather than applying EVAL,
   especially useful for transitions that boil down to more than just uninterpreted step predicates;
   NOTE: - May have side effects! Rewriting and furher simplification 
           in fact not limited to refined transitions. Consider 
           CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC instead.
         - The rewrite list still needs to be filled with more definitions
           to support more transitions. *)
val CAREFUL_UNFOLD_REFINED_TRANS_TAC =
     FULL_SIMP_TAC (srw_ss()) [refined_trans_def, ref_rule_hv_internal_def, hv_step_def] THEN
     REV_FULL_SIMP_TAC (srw_ss()) [hv_ts_def, hv_rule_res_sym_lem] THEN
     REPEAT BasicProvers.VAR_EQ_TAC;



(* allows to split off bisimulation proof from existential proof
   as soon as enough assertions are specified *)    
fun SPLIT_OFF_SIM_FROM_GOAL_TAC (asm,gl) =
 let
  val (el,gl2) = strip_exists gl
  val sim = find_term (is_match ``SIM(rs,is)``) gl2
  val subg = subst [sim |-> ``T``] gl2
             |> (curry list_mk_exists) el
 in
  (SUBGOAL_THEN subg (fn t =>
          ASSUME_TAC t
          THEN FULL_SIMP_TAC (srw_ss()) []
          THEN REPEAT (HINT_EXISTS_TAC THEN FULL_SIMP_TAC (srw_ss()) [])))
  (asm,gl)
 end;


(* given premise
     hv_rule _ = _
   in the assumption list,
   add the only positive guard to the assumption list *)
fun HV_RULE_GUARD_TAC (asm,gl) = 
  let
    val hvrule_trms = map (find_terms (is_match ``hv_rule _ = _``)) asm
                      |> flatten |> remove_redundancy_simp
    val hvrule_thms = map
                      (fn t => (SIMP_CONV ((srw_ss())++normalForms.cond_lift_SS) [hv_rule_def]) t
                               |> EQ_IMP_RULE |> fst
                               |> SIMP_RULE std_ss [IMP_CONJ_THM]
                               |> CONJUNCTS
                               |> List.filter (not o is_neg o snd o dest_imp o concl))
                      hvrule_trms
                      |> flatten
  in
    (MAP_EVERY IMP_RES_TAC hvrule_thms) (asm, gl)
  end;


(* returns a lemma on the consequences of
   a given clause when SIM is given as premise *)
fun SIM_CLAUSE_THM clause =
   SIM_def
   |> SPEC_ALL
   |> EQ_IMP_RULE |> fst
   |> SIMP_RULE std_ss [PULL_FORALL]
   |> SPEC clause
   |> SIMP_RULE (srw_ss()) ([bisim_rel_def]@bisim_definitions@bisim_core_definitions);

(* IMP_RES_TAC wrapper to go from SIM(_,_) to
   the content of the given clause *)
fun IMP_RES_SIM_CLAUSE_TAC clause =
    IMP_RES_TAC (SIM_CLAUSE_THM clause);

(* if SIM(_,_) is in the assumption list,
   this tactical passes the consequences of the given SIM-Clause
   to the theorem-tactic provided as second parameter *)
fun WITH_SIM_CLAUSE clause thmtac =
    PAT_X_ASSUM ``SIM(_, _)``
    (fn t => ASSUME_TAC t THEN thmtac (MP (SIM_CLAUSE_THM clause) t));

(* tries to infer properties matching "matchterm" from
   a SIM predicate in the proof state, its clause "clause",
   and the rest of the proof state *)
fun MATCHING_BY_SIM_CLAUSE clause matchterm tlst (asm,gl) =
 let
  val (res,vali) = IMP_RES_SIM_CLAUSE_TAC clause (asm,gl)
  val newasms = res |> map fst |> flatten |> remove_redundancy_simp
  val targets = map (find_terms (is_match matchterm)) newasms |> flatten |> remove_redundancy_simp
  val tacs = map (fn t => TRY (term_by t (IMP_RES_SIM_CLAUSE_TAC clause >> FULL_SIMP_TAC std_ss [] >> TIME_LIMITED_METIS_TAC 0.1 ([SIM_CLAUSE_THM clause]@tlst)))) targets
 in
  (EVERY tacs) (asm,gl)
 end;

(* returns the InvG corollary identified by the given name,
   but with InvI as precondition instead of InvG;
   this is sometimes more gentle to the proof state than the original corollary *) 
fun InvG_corollary_by_InvI name =
    SPECL [``g:num``, ``IM.G g``] (InvG_corollaries // name)
    |> DISCH ``g < PAR.ng`` 
    |> DISCH ``InvI IM`` 
    |> SIMP_RULE std_ss [fst(EQ_IMP_RULE (SPEC_ALL InvI_def))];

(* returns the InvG clause identified by the given name,
   but with InvI as precondition instead of InvG;
   this is sometimes more gentle to the proof state than the original corollary *) 
fun InvG_clause_by_InvI clause =
    SPECL [``IM.G g``, ``g:num``] InvG_def
    |> DISCH ``g < PAR.ng`` 
    |> DISCH ``InvI IM`` 
    |> SIMP_RULE std_ss [fst(EQ_IMP_RULE (SPEC_ALL InvI_def))]
    |> UNDISCH_ALL
    |> SPEC clause
    |> SIMP_RULE (srw_ss()) [idg_inv_def]
    |> SIMP_RULE std_ss idg_parts
    |> DISCH_ALL;



(************ canonical forms (preservation predicates)  ************)



(* test if goal has ref_preserves_from_to_r predicate *)
fun IS_CANONICAL_REF_PRESERVES_FROM_TO_R (asm,gl) =
    if there_is_some ``ref_preserves_from_to_r`` gl then ALL_TAC (asm,gl) else NO_TAC (asm,gl);


(* test if goal has ref_preserves_from predicate *)
fun IS_CANONICAL_REF_PRESERVES_FROM (asm,gl) =
    if there_is_some ``ref_preserves_from`` gl then ALL_TAC (asm,gl) else NO_TAC (asm,gl);


(* undischarge necessary predicates to enable rewriting
   into canonical preservation predicates *)
fun CANONICAL_UNDISCH_REF_PRESERVES_TAC (asm,gl) =
 let
  (* preprocessing input *) 
  val erm = mk_HOL_ERR "bisimProofLib" "CANONICAL_UNDISCH_REF_PRESERVES_TAC"
  val glcpattern = ``?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')``
  val (glprec,glcon) = if is_match glcpattern gl then (``T``, gl)
                       else if is_match ``prec ==> ^glcpattern`` (SIMP_TERM bool_ss [AND_IMP_INTRO] gl) then dest_imp (SIMP_TERM bool_ss [AND_IMP_INTRO] gl)
                       else raise (erm "goal not in right shape")
  val asml_ = asm@(strip_conj (SIMP_TERM bool_ss [GSYM CONJ_ASSOC] glprec))
  val asml = List.filter (not o is_forall) asml_
  val gll = strip_exists glcon |> snd |> strip_conj
  val substi = match_and_learn [([``SIM (the_rPostState,_)``, ``ideal_model_comp(the_iPreState,_,_)``], gll), 
                                ([``refined_trans(the_rPreState,the_refstep,the_rPostState)``], asml)]
               handle _ => raise (erm "cannot identify states")
  (* undisch tacs *)
  val undischlist = [``SIM(the_rPreState,the_iPreState)``,
                     ``InvI the_iPreState``,
                     ``InvR the_rPreState``,
                     ``refined_trans (the_rPreState, the_refstep, the_rPostState)``]
                    |> map (subst substi) 
                    |> List.rev
  val tac = MAP_EVERY (fn t => TRY (UNDISCH_TAC t)) undischlist
 in
  tac (asm,gl)
 end;

    
(* given a goal as ref_preserves_from_to_r predicate,
   quantify over all poststates to prepare for rewriting
   towards ref_preserves_from predicate *)
fun CANONICAL_FORALL_REF_PRESERVES_FROM_TAC (asm,gl) =
  let
    (* preprocessing input *) 
    val erm = mk_HOL_ERR "bisimProofLib" "CANONICAL_FORALL_REF_PRESERVES_FROM_TAC"
    val glcpattern = ``ref_preserves_from_to_r _ _ _ _``
    val (glprec,glcon) = if is_match glcpattern gl then (``T``, gl)
                         else if is_match ``prec ==> ^glcpattern`` (SIMP_TERM bool_ss [AND_IMP_INTRO] gl) then dest_imp (SIMP_TERM bool_ss [AND_IMP_INTRO] gl)
                         else raise (erm "goal not in right shape")
    val asml_ = asm@(strip_conj (SIMP_TERM bool_ss [GSYM CONJ_ASSOC] glprec))
    val asml = List.filter (not o is_forall) asml_
    val gll = strip_exists glcon |> snd |> strip_conj
    val substi = match_and_learn [([``ref_preserves_from_to_r _ _ _ the_rPostState``], gll)]
                 handle _ => raise (erm "cannot identify post state")
    val rm' = subst substi ``the_rPostState:refined_model``
  in
   SPEC_TAC (rm',rm') (asm,gl)
  end;


(* try to rewrite goal into ref_preserves_from_to_r predicate,
   being as careful as possible regarding the rest of the goal/assumptions *)
val CANONICAL_REF_PRESERVES_FROM_TO_R_TAC =
    FIRST [(* check if we are already in canonical form *)
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           (* maybe rewriting is already enabled, possibly after massaging *)
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold, GSYM AND_IMP_INTRO] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           SIMP_TAC bool_ss [pred_reorder_lem, GSYM CONJ_ASSOC] THEN
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold, GSYM AND_IMP_INTRO] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           SIMP_TAC bool_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
           SIMP_TAC bool_ss [pred_reorder_lem, GSYM CONJ_ASSOC] THEN
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold, GSYM AND_IMP_INTRO] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           (* otherwise undisch required predicates first *)
           CANONICAL_UNDISCH_REF_PRESERVES_TAC THEN
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           CANONICAL_UNDISCH_REF_PRESERVES_TAC THEN
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold, GSYM AND_IMP_INTRO] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           CANONICAL_UNDISCH_REF_PRESERVES_TAC THEN
           SIMP_TAC bool_ss [pred_reorder_lem, GSYM CONJ_ASSOC] THEN
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold, GSYM AND_IMP_INTRO] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R,
           CANONICAL_UNDISCH_REF_PRESERVES_TAC THEN
           SIMP_TAC bool_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
           SIMP_TAC bool_ss [pred_reorder_lem, GSYM CONJ_ASSOC] THEN
           SIMP_TAC bool_ss [GSYM ref_preserves_from_to_r_unfold, GSYM AND_IMP_INTRO] THEN
           IS_CANONICAL_REF_PRESERVES_FROM_TO_R];
   

(* try to rewrite goal into ref_preserves_from predicate,
   being as careful as possible regarding the rest of the goal/assumptions *)
val CANONICAL_REF_PRESERVES_FROM_TAC =
     FIRST [(* check if we are already in canonical form *)
            IS_CANONICAL_REF_PRESERVES_FROM,
            (* otherwise go to ref_preserves_from_to_r first *)
            CANONICAL_REF_PRESERVES_FROM_TO_R_TAC THEN
            FIRST [(* rewriting already possible *)
                   SIMP_TAC bool_ss [GSYM ref_preserves_from_def] THEN
                   IS_CANONICAL_REF_PRESERVES_FROM,
                   (* move quantifier, then rewrite *)
                   SIMP_TAC bool_ss [GSYM ref_preserves_from_def, RIGHT_FORALL_IMP_THM] THEN
                   IS_CANONICAL_REF_PRESERVES_FROM,
                   (* move one quantifier among several ones, then rewrite *)
                   CONV_TAC (ONCE_DEPTH_CONV (SWAP_FORALL_CONV THENC (CHANGED_CONV (ONCE_DEPTH_CONV FORALL_IMP_CONV)))) THEN
                   SIMP_TAC bool_ss [GSYM ref_preserves_from_def],
                   (* introduce quantifier first *)
                   CANONICAL_FORALL_REF_PRESERVES_FROM_TAC THEN
                      FIRST [(* rewriting already possible *)
                             SIMP_TAC bool_ss [GSYM ref_preserves_from_def] THEN
                             IS_CANONICAL_REF_PRESERVES_FROM,
                             (* move quantifier, then rewrite *)
                             SIMP_TAC bool_ss [GSYM ref_preserves_from_def, RIGHT_FORALL_IMP_THM] THEN
                             IS_CANONICAL_REF_PRESERVES_FROM,
                             (* move one quantifier among several ones, then rewrite *)
                             CONV_TAC (ONCE_DEPTH_CONV (SWAP_FORALL_CONV THENC (CHANGED_CONV (ONCE_DEPTH_CONV FORALL_IMP_CONV)))) THEN
                             SIMP_TAC bool_ss [GSYM ref_preserves_from_def]
                            ]
                  ]
           ];





(************ reducing preservation goals into suitable subgoals 
              --> automation       *****************************)




(* tactic to add some text as advice *)
fun DESCRIBE_TASK_TAC str show =
    let 
       val strterm = stringLib.fromMLstring str
    in
       if (show = withAnnotations)
       then TRY (Q.UNABBREV_TAC `YourTask`) THEN Q.ABBREV_TAC (`YourTask = ^strterm`)
       else ALL_TAC
    end;


(* tactic that introduces the necessary subgoals for stepping
    the ideal transition specified by a parameter
    without the refined transition *)
fun SOLO_IDEAL_STEP_TAC (steprule:term, mot:MemOpType, annotate:AnnotationType) (asm,gl) = 
 let
    (* sanity check input *) 
    val erm = ERR "SOLO_IDEAL_STEP_TAC"
    val (ruletype, ruleparam) = dest_comb steprule handle _ => raise (erm "invalid step rule")
    val _ = if (ruletype = ``EXTERNAL_SND`` orelse ruletype = ``EXTERNAL_RCV``)
              then raise (erm "only internal guest transitions supported so far")
            else if (ruletype <> ``INTERNAL``)
              then raise (erm "invalid step rule")
            else ()
    val _ = if (mot <> NoMem) andalso (mot <> HarmlessMem) then (raise erm "updates on memory not supported yet") else ()
 in
     (MATCH_MP_TAC id_internal_solo_with_cond_obligations_lem THEN
      BETA_TAC THEN
      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC bool_ss [] THEN
      EXISTS_TAC ruleparam)
     (asm,gl)
 end;



(* tactic that introduces the necessary subgoals for stepping
    the ideal transition specified by a parameter
    along with the refined transition in the assumption *)
fun PURE_STEP_IDEAL_ALONG_WITH_REFINED_TAC (steprule, mot, annotate:AnnotationType) (asm,gl) = 
    let
       (* preprocessing input *) 
       val erm = mk_HOL_ERR "bisimProofLib" "PURE_STEP_IDEAL_ALONG_WITH_REFINED_TAC"
       val sims = map (fn a =>  [match_term ``SIM(the_rPreState,the_iPreState)`` a] handle _ => []) asm |> flatten |> remove_redundancy_simp
       val sim = case sims of
                   [] => raise (erm "no simulation relation established in premises")
                 | (s::[]) => #1 s
                 | _ => raise (erm "too many simulation relations provided in premises")
       val refsteps = map (fn a =>  [match_term ``refined_trans(the_rPreState,x,the_rPostState)`` a] handle _ => []) asm 
                     |> flatten |> remove_redundancy_simp 
                     |> List.filter (fn rs => subst sim ``the_rPreState:refined_model`` = subst (#1 rs) ``the_rPreState:refined_model``)
       val refstep = case refsteps of
                   [] => raise (erm "no refined step on identified prestate found")
                 | (s::[]) => #1 s
                 | _ => raise (erm "more than one refined step on identified prestate possible")
       val (ruletype, ruleparam) = dest_comb steprule handle _ => raise (erm "invalid step rule")
       val _ = if (ruletype = ``EXTERNAL_SND`` orelse ruletype = ``EXTERNAL_RCV``)
                 then raise (erm "only internal guest transitions supported so far")
               else if (ruletype <> ``INTERNAL``)
                 then raise (erm "invalid step rule")
               else ()
       val _ = if (mot = NoMem) then () else (raise erm "updates on memory not supported yet")
       val free_step_vars = free_vars ruleparam
       val (old_vars, new_vars) = List.partition (fn v => List.foldl (fn (a,r) => free_in v a orelse r) false (gl::asm)) free_step_vars
       val occupied_vars = new_vars@(map free_vars (gl::asm) |> flatten)@[``G:guest``] |> remove_redundancy_simp
       val rename_lst =  sim
                        @refstep
                        @[``the_g:num`` |-> variant occupied_vars ``g:num``]
                        @[``the_new_G:guest`` |-> with_flag(priming,SOME "_") (uncurry variant) (occupied_vars, ``G:guest``)]
                        @[``the_iPostState:ideal_model`` |-> with_flag(priming,SOME "_") (uncurry variant) (occupied_vars, ``IM:ideal_model``)]
       (* formulation of subgoals 
           - subgoal 3 depends on subgoal 1
           - subgoal 4 depends on subgoals 2 and 3
           - subgoal 5 depends on subgoals 3 and 4
           - in the end, we provide assertions on subgoals 3, 4, and 5 to the original goal *)
       val subgoal1 = ``the_g < PAR.ng /\ ideal_guest_trans (the_iPreState.G the_g, the_g, ^steprule, the_new_G)``
                      |> subst rename_lst
                      |> (curry list_mk_exists) ((map (subst rename_lst) [``the_new_G:guest``, ``the_g:num``])@(rev new_vars))
       val subgoal2 = ``ideal_guest_trans (G, g, ^steprule, G') ==> (mem_abs(G.m) = mem_abs(G'.m))``
                      |> gen_all
       val subgoal3 = ``(the_g < PAR.ng) /\
                        ideal_guest_trans (the_iPreState.G the_g, the_g, ^steprule, the_new_G) /\ 
                        (the_iPostState = the_iPreState with G := (the_g =+ the_new_G) the_iPreState.G)``
                      |> subst rename_lst
                      |> (curry list_mk_exists) ((map (subst rename_lst) [``the_new_G:guest``, ``the_g:num``])@(rev new_vars)@[subst rename_lst``the_iPostState:ideal_model``])
       val subgoal4 = ``ideal_model_trans (the_iPreState, C_INTERNAL, the_iPostState)``
                      |> subst rename_lst                     
       val subgoal5 = ``SIM(the_rPostState, the_iPostState) /\ (InvI the_iPostState) /\ (InvR the_rPostState)``
                      |> subst rename_lst
       (* subgoal descriptions *)
       val des1 = DESCRIBE_TASK_TAC "Show that the ideal transition can be fired (is enabled)!" annotate
       val des2 = DESCRIBE_TASK_TAC "Show that the ideal transition does not affect the memory!" annotate
       val des3 = DESCRIBE_TASK_TAC "Establish the ideal poststate!" annotate
       val des4 = DESCRIBE_TASK_TAC "Establish the ideal transition!" annotate
       val des5 = DESCRIBE_TASK_TAC "Establish the bisimulation relation and invariants!" annotate
       val des0 = DESCRIBE_TASK_TAC "One more step should have been taken by now. Take further steps or finish here!" annotate
       (* impose subgoals *)
       val tact =        `^subgoal3` by des3
                  THENL [`^subgoal1` by des1, `^subgoal4` by des4]
                  THENL [ALL_TAC, ALL_TAC, `^subgoal2` by des2, `^subgoal5` by des5 THENL [ALL_TAC, des0]]
    in
        tact (asm,gl)
    end;


(* like PURE_STEP_IDEAL_ALONG_WITH_REFINED_TAC, but allows to couple parameters even beyond
   the initial passing of the step-rule parameters *)
fun PURE_STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (steprule, mot, annotate) (asm,gl) = 
    let
       (* preprocessing input *) 
       val erm = mk_HOL_ERR "bisimProofLib" "PURE_STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC"
       val sims = map (fn a =>  [match_term ``SIM(the_rPreState,the_iPreState)`` a] handle _ => []) asm |> flatten |> remove_redundancy_simp
       val sim = case sims of
                   [] => raise (erm "no simulation relation established in premises")
                 | (s::[]) => #1 s
                 | _ => raise (erm "too many simulation relations provided in premises")
       val refsteps = map (fn a =>  [match_term ``refined_trans(the_rPreState,x,the_rPostState)`` a] handle _ => []) asm 
                     |> flatten |> remove_redundancy_simp 
                     |> List.filter (fn rs => subst sim ``the_rPreState:refined_model`` = subst (#1 rs) ``the_rPreState:refined_model``)
       val refstep = case refsteps of
                   [] => raise (erm "no refined step on identified prestate found")
                 | (s::[]) => #1 s
                 | _ => raise (erm "more than one refined step on identified prestate possible")
       val (ruletype, ruleparam) = dest_comb steprule handle _ => raise (erm "invalid step rule")
       val _ = if (ruletype = ``EXTERNAL_SND`` orelse ruletype = ``EXTERNAL_RCV``)
                 then raise (erm "only internal guest transitions supported so far")
               else if (ruletype <> ``INTERNAL``)
                 then raise (erm "invalid step rule")
               else ()
       val _ = if (mot = NoMem) then () else (raise erm "updates on memory not supported yet")
       val free_step_vars = free_vars ruleparam
       val (old_vars, new_vars) = List.partition (fn v => List.foldl (fn (a,r) => free_in v a orelse r) false (gl::asm)) free_step_vars
       val occupied_vars = new_vars@(map free_vars (gl::asm) |> flatten)@[``G:guest``] |> remove_redundancy_simp
       val rename_lst =  sim
                        @refstep
                        @[``the_g:num`` |-> variant occupied_vars ``g:num``]
                        @[``the_new_G:guest`` |-> with_flag(priming,SOME "_") (uncurry variant) (occupied_vars, ``G:guest``)]
                        @[``the_iPostState:ideal_model`` |-> with_flag(priming,SOME "_") (uncurry variant) (occupied_vars, ``IM:ideal_model``)]
       (* formulation of subgoals 
           - subgoal 3 depends on subgoal 1
           - subgoal 4 depends on subgoals 1, 2 and 3
           - subgoal 5 depends on subgoals 1, 3 and 4
	- in the end, we provide assertions on subgoals 3, 4, and 5 to the original goal *)
       val s1_p1 = subst rename_lst ``the_g < PAR.ng``
       val s1_p2 = subst rename_lst ``ideal_guest_trans (the_iPreState.G the_g, the_g, ^steprule, the_new_G)``
       val s1_p3 = subst rename_lst ``SIM(the_rPostState, the_iPreState with G := (the_g =+ the_new_G) the_iPreState.G)``
       val subgoal1 = list_mk_conj [s1_p1, s1_p2, s1_p3]
                      |> (curry list_mk_exists) ((map (subst rename_lst) [``the_new_G:guest``, ``the_g:num``])@(rev new_vars))
       val subgoal2 = ``ideal_guest_trans (G, g, ^steprule, G') ==> (mem_abs(G.m) = mem_abs(G'.m))``
                      |> gen_all
       val subgoal3 = ``the_iPostState = the_iPreState with G := (the_g =+ the_new_G) the_iPreState.G``
                      |> subst rename_lst
                      |> (curry list_mk_exists) [subst rename_lst``the_iPostState:ideal_model``]
       val subgoal4 = ``ideal_model_trans (the_iPreState, C_INTERNAL, the_iPostState)``
                      |> subst rename_lst                     
       val subgoal5 = ``SIM(the_rPostState, the_iPostState) /\ (InvI the_iPostState) /\ (InvR the_rPostState)``
                      |> subst rename_lst
       (* subgoal descriptions *)
       val des1 = DESCRIBE_TASK_TAC "Show that the guest transition is enabled for a coupling that preserves the bisimulation!" annotate
       val des2 = DESCRIBE_TASK_TAC "Show that the ideal transition does not affect the memory!" annotate
       val des3 = DESCRIBE_TASK_TAC "Establish the ideal poststate!" annotate
       val des4 = DESCRIBE_TASK_TAC "Establish the ideal transition!" annotate
       val des5 = DESCRIBE_TASK_TAC "Establish the bisimulation relation and invariants!" annotate
       val des0 = DESCRIBE_TASK_TAC "One more step should have been taken by now. Take further steps or finish here!" annotate
       (* remove unneccessary results *)
       val rmv1p12 = MAP_EVERY (fn x => UNDISCH_THEN x (fn y => ALL_TAC)) [s1_p1, s1_p2]
       val rmv1p3 = MAP_EVERY (fn x => UNDISCH_THEN x (fn y => ALL_TAC)) [s1_p3]
       val rmv1 = MAP_EVERY (fn x => UNDISCH_THEN x (fn y => ALL_TAC)) (strip_conj (#2 (strip_exists subgoal1)))
       val rmv3 = MAP_EVERY (fn x => UNDISCH_THEN x (fn y => ALL_TAC)) (strip_conj (#2 (strip_exists subgoal3)))
       (* impose subgoals *)
       val tact =       BasicProvers.byA(`^subgoal1`, des1)
	          THENL [ALL_TAC, BasicProvers.byA(`^subgoal3`,des3)]
                  THENL [ALL_TAC, rmv1, BasicProvers.byA(`^subgoal4`,des4)]
                  THENL [ALL_TAC, ALL_TAC, rmv1p3 THEN BasicProvers.byA(`^subgoal2`,des2), BasicProvers.byA(`^subgoal5`, des5) THENL [rmv1p12, des0 THEN rmv1p3]]
    in
        tact (asm,gl)
    end;



(* removes old sim and inv predicates,
   tries to prove the remaining goal if trivial (i.e. if we are done),
   otherwise provides the taken step as witness to simplify goal *)
fun CLEAN_UP_AFTER_COMMON_STEP_TAC (asm,gl) = 
 let
   (* preprocessing input *) 
  val erm = mk_HOL_ERR "bisimProofLib" "CLEAN_UP_AFTER_COMMON_STEP_TAC"
  val refsteps = map (fn a =>  [match_term ``refined_trans(the_rPreState,x,the_rPostState)`` a] handle _ => []) asm 
                     |> flatten |> map #1 |> remove_redundancy_simp 
  val idsteps = map (fn a =>  [match_term ``ideal_model_trans(the_iPreState,the_CompRule,the_iPostState)`` a] handle _ => []) asm 
                     |> flatten |> map #1 |> remove_redundancy_simp 
  val idsteps_in_goal =  find_terms (is_match ``ideal_model_trans(the_iPreState,y,the_iPostState)``) gl
                         |> remove_redundancy_simp 
  val sims_in_goal =  find_terms (is_match ``SIM(rs,is)``) gl |> remove_redundancy_simp 
                      |> map (fn sr => dest_comb sr |> #2 |> pairLib.dest_pair |> #1)
                      |> map (fn rs => ``SIM(^rs, the_nextState)``)
  val known_idsteps = ListPair.map (fn (isg,isp) => 
                                    if ((dest_comb isg |> #2 |> pairLib.dest_pair |> #1)
                                        = subst isp ``the_iPreState:ideal_model``)
                                    then [isp] else []) (idsteps_in_goal, idsteps)
                       |> flatten |> remove_redundancy_simp                         
  val sims = List.filter (is_match ``SIM(some_rState,some_iState)``) asm |> remove_redundancy_simp
  val invis = List.filter (is_match ``InvI(some_iState)``) asm |> remove_redundancy_simp
  val invrs = List.filter (is_match ``InvR(some_rState)``) asm |> remove_redundancy_simp
  val refidlst = ListPair.map (fn (rs,is) => (subst (is@rs) ``SIM (the_rPreState, the_iPreState)``,
                                              subst (is@rs) ``SIM (the_rPostState, the_iPostState)``))(refsteps, idsteps)
  val sim_remove_lst = map (fn (oldsim, newsim) => 
                               if ((List.exists (equal newsim) sims) andalso (List.exists (equal oldsim) sims))
                               then [oldsim] else []) refidlst
                       |> flatten |> remove_redundancy_simp
  val InvI_remove_lst = map (fn is => 
                                if ((List.exists (equal (subst is ``InvI(the_iPostState)``)) invis)
                                   andalso (List.exists (equal (subst is ``InvI(the_iPreState)``)) invis))
                               then [(subst is ``InvI(the_iPreState)``)] else []) idsteps
                         |> flatten |> remove_redundancy_simp
  val InvR_remove_lst = map (fn rs => 
                                if ((List.exists (equal (subst rs ``InvR(the_rPostState)``)) invrs)
                                   andalso (List.exists (equal (subst rs ``InvR(the_rPreState)``)) invrs))
                               then [(subst rs ``InvR(the_rPreState)``)] else []) refsteps
                         |> flatten |> remove_redundancy_simp
  val occupied_vars = (map free_vars (gl::asm) |> flatten) |> remove_redundancy_simp
  val rename_lst =  [``the_n:num`` |-> variant occupied_vars ``n:num``]
                   @[``the_nextState:ideal_model`` |-> with_flag(priming,SOME "_") (uncurry variant) (occupied_vars, ``IM:ideal_model``)]
  val alt_gls = map (fn is => list_mk_conj ((``ideal_model_comp (the_iPostState,the_n,the_nextState)``)::sims_in_goal)
                              |> subst (is@rename_lst)
                              |> (curry list_mk_exists) (map (subst (is@rename_lst)) [``the_n:num``, ``the_nextState:ideal_model``])) known_idsteps
  (* remove old inv and sim predicates *)
  val tact =  MAP_EVERY (fn t => UNDISCH_THEN t (fn t2 => ALL_TAC)) 
              (sim_remove_lst@InvI_remove_lst@InvR_remove_lst)
  (* check if goal already solvable *)
  val tact = tact THEN TRY (LIMITED_METIS_TAC 1 [CONJUNCT1 ideal_model_comp_def])
  (* otherwise provide last ideal transition as witness
     and transform goal to standardform *)
  val tact = tact THEN TRY (MAP_FIRST (fn ng => SUFF_TAC ng THENL [LIMITED_METIS_TAC 1 [] THEN NO_TAC, ALL_TAC]) alt_gls)
 in
  tact (asm, gl)
 end;



(* adds preparation and aftermath to PURE_STEP_IDEAL_ALONG_WITH_REFINED_TAC *)
fun STEP_IDEAL_ALONG_WITH_REFINED_TAC (steprule, mot, annotate) (asm,gl) = 
    let
       val occupied_vars = (map free_vars (gl::asm) |> flatten) |> remove_redundancy_simp
       val the_m = variant occupied_vars ``m:num``
       val tact =      Q.REFINE_EXISTS_TAC `SUC ^the_m`
                  THEN RW_TAC (srw_ss()) [ideal_model_comp_rev_lem]
                  THEN PURE_STEP_IDEAL_ALONG_WITH_REFINED_TAC (steprule, mot, annotate)
                  THENL [(* subgoal: ideal guest transition is enabled
                            aftermath: TBD *)
                         ALL_TAC,
                         (* subgoal: describe ideal poststate after guest transition
                            aftermath: solved quite trivially *)
                         NTAC 2 FEED_EXISTS_TAC
                         THEN FULL_SIMP_TAC (srw_ss()) []
                         THEN TRY (LIMITED_METIS_TAC 1 []),
                         (* subgoal: ideal guest transition does not affect memory
                            aftermath: remove unnecessary assumptions
                                       and try to prove subgoal
                            TODO: employ theorems for mem-operations not affecting abstraction *)
                         REPEAT (PRED_ASSUM (not o markerSyntax.is_abbrev) (fn x => ALL_TAC))
                         THEN REPEAT GEN_TAC
                         THEN TRY (computeLib.RESTR_EVAL_TAC [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``] 
                                    THEN RW_TAC (srw_ss()) [mem_snd_req_axiom]
                                    THEN RW_TAC (srw_ss()) []
                                    THEN LIMITED_METIS_TAC 1 [mem_snd_req_axiom]),
                         (* subgoal: composed ideal transition exists
                            aftermath: solve *)
                         RW_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def]
                         THEN ASSUME_TAC syncInv_lem
                         THEN (RES_SPEC_WITH_STATES_FROM_PREMISES_TAC false)
                         THEN (RES_SPEC_WITH_STATES_FROM_GOAL_TAC false)
                         THEN FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM]
                         THEN METIS_TAC [InvI_def,shared_mem_upd_lem, sync_shared_mem_upd_of_guest_def],
                         (* subgoal: re-establish bisimulation and invariants
                            aftermath: take care of invariants *)
                         REPEAT CONJ_TAC
                         THENL [DESCRIBE_TASK_TAC "Establish the bisimulation relation!" annotate,
                                METIS_TAC [ideal_model_trans_InvI_lem],
                                METIS_TAC [refined_trans_InvR_lem]],
                         (* original goal
                            aftermath: try to solve, but at least remove old predicates
                                       and simplify existential goal *)
                         CLEAN_UP_AFTER_COMMON_STEP_TAC]
    in
       tact (asm,gl)
    end;


(* adds preparation and aftermath to PURE_STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC *)
fun STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (steprule, mot, annotate) (asm,gl) = 
    let
       val occupied_vars = (map free_vars (gl::asm) |> flatten) |> remove_redundancy_simp
       val the_m = variant occupied_vars ``m:num``
       val tact =      Q.REFINE_EXISTS_TAC `SUC ^the_m`
                  THEN RW_TAC (srw_ss()) [ideal_model_comp_rev_lem]
                  THEN PURE_STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (steprule, mot, annotate)
		  THENL [(* subgoal: ideal guest transition is enabled
                            aftermath: TBD *)
                         ALL_TAC,
                         (* subgoal: describe ideal poststate after guest transition
                            aftermath: solved quite trivially *)
                         FULL_SIMP_TAC (srw_ss()) []
                         THEN TRY (LIMITED_METIS_TAC 1 []),
                         (* subgoal: ideal guest transition does not affect memory
                            aftermath: remove unnecessary assumptions
                                       and try to prove subgoal
                            TODO: employ theorems for mem-operations not affecting abstraction *)
                         REPEAT (PRED_ASSUM (not o markerSyntax.is_abbrev) (fn x => ALL_TAC))
                         THEN REPEAT GEN_TAC
                         THEN TRY (computeLib.RESTR_EVAL_TAC [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``] 
                                    THEN RW_TAC (srw_ss()) []
                                    THEN RW_TAC (srw_ss()) []
                                    THEN LIMITED_METIS_TAC 1 [mem_snd_req_axiom]),
                         (* subgoal: composed ideal transition exists
                            aftermath: solve *)
                         RW_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def]
                         THEN ASSUME_TAC syncInv_lem
                         THEN (RES_SPEC_WITH_STATES_FROM_PREMISES_TAC false)
                         THEN (RES_SPEC_WITH_STATES_FROM_GOAL_TAC false)
                         THEN FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM]
                         THEN METIS_TAC [InvI_def,shared_mem_upd_lem, sync_shared_mem_upd_of_guest_def],
                         (* subgoal: re-establish bisimulation and invariants
                            aftermath: take care of invariants *)
                         REPEAT CONJ_TAC
                         THENL [RW_TAC bool_ss [],
                                METIS_TAC [ideal_model_trans_InvI_lem],
                                METIS_TAC [refined_trans_InvR_lem]],
                         (* original goal
                            aftermath: try to solve, but at least remove old predicates
                                       and simplify existential goal *)
                         CLEAN_UP_AFTER_COMMON_STEP_TAC]
    in
       tact (asm,gl)
    end;


(* turn condition on ideal and refined state into lambda abstraction *)
fun abs_ir_cond cond =
    if (is_abs cond)
     then cond
     else
       let
         val is = case (find_terms ((equal ``:ideal_model``) o type_of) cond |> remove_redundancy_simp)
                   of [] => ``IM:ideal_model``
                    | [x] => x
                    | _ => raise ERR "abs_ri_cond" "too many ideal states"
         val rs = case (find_terms ((equal ``:refined_model``) o type_of) cond |> remove_redundancy_simp)
                   of [] => ``RM:refined_model``
                    | [x] => x
                    | _ => raise ERR "abs_ri_cond" "too many refined states"
       in
         list_mk_abs ([is,rs], cond)
       end;


(* refined -> ideal:
   introduce a forward prestep in the ideal world only
   and establish some postcondition unless already established;
   split the preservation goal into:
      1. obligations for the introduced prestep
      2. preservation goal almost as before, but assuming
         that the prestep has happened with its postcondition *)
fun POSTCOND_FORWARDSTEP_IDEAL_TAC cond =
  let val lem = INST [``cond:ideal_model-> refined_model -> bool`` |-> abs_ir_cond cond]
                postcond_forwardstep_ideal_lem3 |> BETA_RULE
    in
      CANONICAL_REF_PRESERVES_FROM_TAC THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC lem THEN 
      STRIP_TAC THENL
         [REPEAT STRIP_TAC,
          REPEAT STRIP_TAC]
    end;


fun RW_FS_IMPRESS thm =
RW_TAC (srw_ss()) [thm]
THEN FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM]
THEN IMP_RES_TAC thm;

fun STRONG_FS_TAC lst = FULL_SIMP_TAC ((srw_ss())++ARITH_ss++normalForms.cond_lift_SS) (combinTheory.APPLY_UPDATE_THM::lst);


fun InvI_EXPAND g = InvG_imp_lem |> SPEC g |> SIMP_RULE (srw_ss()) [InvG_EXPAND];


end



