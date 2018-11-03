(* This library contains machinery to prove the ideal invariant *)

(********** Loading *************)

structure idealInvProofLib   =
struct

open HolKernel boolLib bossLib List;

open pred_setTheory;
open math_lemmasTheory;
open axtypesTheory;
open haspoctypesTheory;
open haspocSimps;
open parametersTheory;
open axfuncsTheory;
open hypervisorTheory;
open idealTheory;

open toolboxLib;
open tacticsLib;
open annotationsLib; 
open haspocLib;


(* operators *)
infix //; infix ///; infix -:; (* from annotationsLib*)
fun --- (a, b) = (a,b); (* build a tuple without using parentheses *)
fun ++> (x, (((a,b),c),d)) = (x,(a,b,c,d));
infix 1 ---;
infix ++>;


(************* strategy  ***********)

(* for each ideal invariant part ("context") that can occur as a subgoal
   we collect:
    1. a list of definitions that should be unfolded,
       typically of other invariants that this invariant part depends on
       (the definition of the context is implicitly provided)
    2. a list of InvG corollaries that help to prove the subgoal
    3. input for METIS_TAC, specific to that subgoal
    4. a tactic useful for that subgoal 
   The strategy is stored as a term net. *)

val STANDARD_STRATEGY = ([]:thm list) --- ([]:string list) --- ([]:thm list) --- ALL_TAC;

val MEMRPL_SPLIT_TAC = REPEAT STRIP_TAC >>
                       REPEAT IF_CASES_TAC >>
                       FULL_SIMP_TAC (srw_ss()) [];

val id_inv_strategy_lst =
    [``id_inv_cifreq_core`` ++> [inv_good_idcore_def] --- [] --- [NOT_IN_EMPTY] --- ALL_TAC,
     ``id_inv_gicreq_`` ++> [id_inv_perreq__def, GICC_GICD_OK_def] --- ["gicd_req_ok"] --- [per_gic_disj_lem] --- ALL_TAC,
     ``id_inv_memrpl_`` ++> [inv_good_mem_def, id_inv_gicreq__def, id_inv_perreq__def, 
                             combinTheory.APPLY_UPDATE_THM, GICC_GICD_OK_def] 
                              --- ["gicd_req_ok"]
                              --- [per_gic_disj_lem, per_disj_lem] --- MEMRPL_SPLIT_TAC,
     ``id_inv_gic_q_``    ++> [GICC_GICD_OK_def, id_inv_gicreq__def] --- ["gicd_req_ok"] --- [irqID_11, SGI_11, igc_pir_number_lem, IGC_NOTIN_PIRQ_lem, IGC_IN_xPIRQ_lem] --- ALL_TAC,
     ``idgic_gm_conf``    ++> [idgic_gm_conf_def, GICC_GICD_OK_def, id_inv_gicreq__def, PI_def] --- ["gicd_req_ok"] 
                              --- [irqID_11, in_PIRQ_lem, guest_irq_def, PIstate_distinct] --- (TRY CASE_TAC), 
     ``id_inv_unique_rpl_bif`` ++>  [id_inv_pifrpl__def] --- ["cifrpl2"] --- [] --- ALL_TAC,
     ``id_inv_unique_rpl_mem`` ++> [inv_good_mem_def] ---[] --- [unique_match_thm] --- ALL_TAC,
     ``id_inv_bifreq`` ++> [] --- ["cifrpl2", "pifrpl2"] --- [] --- ALL_TAC,
     ``id_inv_bifreq_mem`` ++> STANDARD_STRATEGY,
     ``id_inv_cifadr_`` ++> STANDARD_STRATEGY,
     ``id_inv_pifadr_`` ++> STANDARD_STRATEGY,
     ``id_inv_cifrpl_`` ++> [id_inv_unique_rpl_bif_def, id_inv_cifadr__def] --- [] --- [Rpl_PAdr_ReqOf_lem] --- ALL_TAC,
     ``id_inv_pifrpl_`` ++> [id_inv_unique_rpl_bif_def, id_inv_pifadr__def] --- [] --- [Rpl_PAdr_ReqOf_lem] --- ALL_TAC,
     ``id_inv_perreq_`` ++> [id_inv_gicreq__def] --- [] --- [per_disj_lem, per_gic_disj_lem] --- ALL_TAC,
     ``id_inv_ioreq_`` ++> STANDARD_STRATEGY,
     ``id_inv_pifreq_per`` ++> STANDARD_STRATEGY,
     ``id_inv_mem_reqsent_`` ++> [inv_good_mem_def] --- [] --- [] --- ALL_TAC
    ];

val id_inv_strategy = foldl (uncurry Net.insert) Net.empty id_inv_strategy_lst;


(* looking up strategy parts *)

fun lookup_ii_rwlst trm =
    case Net.lookup trm id_inv_strategy 
     of [] => []
      | lst => (dest_const trm |> #1 |> (C (curry (op ^))) "_def" |> fetch "ideal" handle _ => TRUTH)
               ::(lst |> map #1 |> flatten);

fun lookup_ii_corlst trm =
    Net.lookup trm id_inv_strategy |> map #2 |> flatten |> map ((curry get_annotated_conj) InvG_corollaries);

fun lookup_ii_metlst trm =
    Net.lookup trm id_inv_strategy |> map #3 |> flatten;

fun lookup_ii_tac trm =
    Net.lookup trm id_inv_strategy |> map #4 |> hd handle _ => ALL_TAC;


(* TACTICALS providing the relevant definition-rewrites (RW),
   the InvG-corollaries (COR), the METIS-input (MET),
   and the tactic (TAC) from the strategy specific to the context(s).
   The contexts are either taken from the goal (GL), are passed as
   parameter (CTX) by tactical WITH_CTX, or are pulled from a global
   reference variable after having pushed there before (PULL).
   The latter method seems to get confused sometimes when 
   several subgoals are processed at once. *)

fun II_GL_RW lst_tac (asm, gl) =
  let
    val consts = find_terms is_const gl
    val rlst = map lookup_ii_rwlst consts |> flatten
  in
   lst_tac rlst (asm,gl)
  end;

val ii_strategy_gl = ref ([]:term list);

fun II_PUSH (asm,gl) =
  let
    val consts = find_terms is_const gl
    val _ = ii_strategy_gl := consts
  in
   ALL_TAC (asm,gl)
  end;

fun II_PULL_RW lst_tac =
  let
    val consts = !ii_strategy_gl
    val rlst = map lookup_ii_rwlst consts |> flatten
  in
   lst_tac rlst
  end;


fun II_PULL_COR lst_tac =
  let
    val consts = !ii_strategy_gl
    val rlst = map lookup_ii_corlst consts |> flatten
  in
   lst_tac rlst
  end;


fun II_PULL_MET lst_tac =
  let
    val consts = !ii_strategy_gl
    val rlst = map lookup_ii_metlst consts |> flatten
  in
   lst_tac rlst
  end;

fun II_PULL_TAC (asm,gl) =
 let
    val consts = !ii_strategy_gl
    val tacs = map lookup_ii_tac consts
  in
   (EVERY tacs) (asm,gl)
  end;

fun WITH_CTX ctac (asm,gl) =
  let
    val consts = find_terms is_const gl
  in
   ctac consts (asm,gl)
  end;

fun II_CTX_MET consts lst_tac =
  let
    val rlst = map lookup_ii_metlst consts |> flatten
  in
   lst_tac rlst
  end;


fun II_CTX_COR consts lst_tac =
  let
    val rlst = map lookup_ii_corlst consts |> flatten
  in
   lst_tac rlst
  end;

fun II_CTX_TAC consts (asm,gl) =
 let
    val tacs = map lookup_ii_tac consts
  in
   (EVERY tacs) (asm,gl)
  end;

(************* grouped or unexported defs/theorems  ***********)


val id_inv_alternative_defs =
    [id_inv_unique_rpl_def', id_inv_cifreq_def', id_inv_pifreq_def', id_inv_gicreq_def', id_inv_perreq_def',
     id_inv_cifadr_def', id_inv_pifadr_def', id_inv_ioreq_def',  id_inv_cifrpl_def', id_inv_pifrpl_def',
     id_inv_memrpl_def', id_inv_mem_reqsent_def', id_inv_gic_q_def', id_inv_gic_pi_def];

val id_inv_part_defs =
    [id_inv_unique_rpl_bif_def, id_inv_unique_rpl_mem_def, id_inv_cifreq_core_def, id_inv_bifreq_def,
     id_inv_bifreq_mem_def, id_inv_pifreq_per_def, id_inv_gicreq__def, id_inv_perreq__def, id_inv_cifadr__def,
     id_inv_pifadr__def, id_inv_ioreq__def, id_inv_cifrpl__def, id_inv_pifrpl__def, id_inv_memrpl__def,
     id_inv_mem_reqsent__def, id_inv_gic_q__def];

val mem_axioms_lst = [mem_rcv_rpl_axiom, mem_rcv_req_axiom, mem_snd_req_axiom, mem_internal_axiom,
                     mem_step_snd_rpl_fully_merged_diff_lem];

val per_axioms_lst = [per_active_axiom, per_send_dma_axiom, per_rcv_dma_axiom, per_rcv_io_axiom, per_snd_iorpl_axiom, per_event_step_axiom, per_irq_step_axiom, per_internal_axiom];

val idgic_axioms_lst = (map ((curry get_annotated_conj) idgic_step_axiom)
                        ["rcv_req", "rcv_irq", "snd_irq", "rcv_igc", "good_rpl"])
                       @[idgic_step_snd_rpl_inv_merged_lem, idgic_step_dist_irq_inv_merged_lem2];

val idcore_axioms_lst = map ((curry get_annotated_conj) idcore_step_axiom)
    ["internal", "snd_pcil", "snd_igc", "rcv_phys", "snd_req", "rcv_rpl", "rcv_fault", "rcv_psci", "startup"]; 

val all_step_axioms = mem_axioms_lst@per_axioms_lst@idcore_axioms_lst@idgic_axioms_lst
                      |> map UNIQUE_REQ;

val fallc_imp = fall_constructors_thm_of ``:IDG_INVS`` |> SPEC ``\i. idg_inv(G,g,i)`` |>  BETA_RULE |> EQ_IMP_RULE |> #1;



(*************** tactics ***********)


(* unfolds the step predicates in the premises (with EVAL)
   and keeps the original *)
val UNFOLD_STEP_PREDICATE_TAC =
    ASSUM_LIST (fn l => FIND_STEP_PREDICATES_TAC l (fn t => REPEAT_TCL CHOOSE_THEN ASSUME_TAC 
               ((UNIQUE_REQ (computeLib.RESTR_EVAL_RULE [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``, ``base_adr``, ``Frpl``, ``gicd_req_ok``, ``mode``, ``MODE``, ``Mode``, ``gicAR``] t)))));


(* prints the current obligation: invariant clause and ideal transitions *)
fun PRINT_OBLIGATION_TAC (asm, gl) =
  let
    val consts = find_terms (is_const) gl
                 |> filter (fn t => case lookup_ii_rwlst t of [] => false | _ => true)
                 |> remove_redundancy_simp
    val cname = map (fst o dest_const) consts
    val ctext = foldl (fn (c,t) => t ^ " | " ^ c) "" cname
    val steps = map (find_terms (is_step_predicate)) asm |> flatten |> remove_redundancy_simp
    val sname =  map (fst o dest_const) steps
    val stext = foldl (fn (s,t) => t ^ " | " ^ s) "" sname
  in
   (PRINT_TAC ("----------------\n" ^ ctext ^ "\n | of\n" ^ stext ^ "\n----------------\n\n\n")) (asm,gl)
  end;


(* desperate last resort tactic for reasoning on the parameters
    -- should maybe only be used to check if something is provable at all
       from what we know, not as a tactic in a final proof script
    -- either solves current subgoal or fails, does not massage subgoal *)
val DESPERATE_PARAM_TAC =
            RW_TAC (srw_ss()) [good_proj_axiom]
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC (REWRITE_RULE [refined_goodP_def, perAR_def] refined_goodP_axiom)
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN CCONTR_TAC
       THEN RES_TAC
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN CCONTR_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN REV_FULL_SIMP_TAC (srw_ss()) []
       THEN METIS_TAC [(* knowledge on parameters *)
                       refined_goodP_def,
                       refined_goodP_axiom,
                       goodP_axiom,
                       good_proj_axiom,
                       coupling_axiom,
                       Trans_axiom,
                       (* definitions *)
                       perAR_def,
                       gicAR_def,
                       Agicd_def,
                       (* sets, options, etc. *)
                       pred_setTheory.DISJOINT_DEF,
                       pred_setTheory.PSUBSET_DEF,
                       pred_setTheory.SUBSET_DEF,
                       pred_setTheory.IN_INTER,
                       pred_setTheory.NOT_IN_EMPTY,
                       pred_setTheory.INTER_DEF,
                       pred_setTheory.EMPTY_DEF,
                       pred_setTheory.GSPEC_ETA,
                       pred_setTheory.UNION_DEF,
                       pred_setTheory.BIGUNION,
                       optionTheory.IS_SOME_EXISTS,
                       optionTheory.THE_DEF,
                       NOT_EQ_SYM_RW,
                       NO_MEMBER_NOT_EQ_RW,
                       lambda_eq_pred_lem,
                       (* address lemmas *)
                       GICaddresses_lem,
                       igc_adr_disj_lem,
                       other_igc_chan_lem,
                       igc_chan_def,
                       other_igc_chan_def,
                       no_igc_chan_def,
                       normal_guest_mem_trans_lem,
                       normal_guest_mem_disj_lem,
                       unshared_guest_mem_disj_lem];


(*************** finish ***********)

end



