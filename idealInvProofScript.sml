(* This theory proves the invariant of the ideal model.
   To that end, the following areas are dealt with:
    1. First we prove the invariant for the core component separately.
    2. In the main part, we show the invariant for an entire guest.
       This concerns several hundreds of combinations 
       of transitions and invariant clauses.
       We employ machinery from idealInvProofLib to address this complexity.
    3. Finally we prove lemmas on the composed model and put
       the puzzle pieces together. *)


(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib;

open pred_setTheory;
open math_lemmasTheory;
open axtypesTheory;
open haspoctypesTheory;
open haspocSimps;
open parametersTheory;
open axfuncsTheory;
open hypervisorTheory;
open idealTheory;

open tacticsLib;
open toolboxLib;
open haspocLib;
open annotationsLib; infix //; infix ///; infix -:;
open idealInvProofLib;

val _ = new_theory "idealInvProof";


(************* ideal core invariant ***************)




(* cases of idcore_step as suggested by Thomas Tuerk *)
val idcore_step_CASES = store_thm ("id_core_step_CASES", ``
  idcore_step  (C, a, C') <=> (
    (?c. (a = RCV (PHYS NONE c)) /\ idcore_step_rcv_phys (C, C')) \/
    (?r. (a = RCV (MRPL r)) /\ idcore_step_rcv_rpl (C, r, C')) \/
    (?e. (a = RCV (PSCI e)) /\ idcore_step_rcv_psci (C, e, C'))) \/
    (?g c. (a = RCV (STARTUP g c)) /\ idcore_step_startup (C, g, c, C')) \/
    (?r. (a = SEND (MREQ r)) /\ idcore_step_snd_req (C, r, C')) \/
    (?l. (a = SEND (PSCIL l)) /\ idcore_step_snd_pscil (C, l, C')) \/
    (?s. (a = SEND (SIGC s)) /\ idcore_step_snd_igc (C, s, C')) \/
    ((a = TAU) /\ idcore_step_internal (C, C')) ``,
  ONCE_REWRITE_TAC[idcore_step_def] THEN
  Cases_on `a` THEN (
    SIMP_TAC std_ss [Action_distinct, Action_case_def, Action_11] THEN
    Cases_on `M` THEN  SIMP_TAC std_ss [Message_case_def, Message_11, Message_distinct]
  )
  THEN Cases_on `o'` THEN SIMP_TAC std_ss []);


(* proof of ideal core invariant *)
(* by a first case split on the clauses and a subsequent split on the steps *)
val inv_good_idcore_lem = store_thm("inv_good_idcore_lem",
    ``!C a C'. inv_good_idcore C /\ idcore_step(C,a,C') ==> inv_good_idcore C'``,
    FULL_SIMP_TAC std_ss [inv_good_idcore_def] THEN
    REPEAT STRIP_TAC THENL
    [(* clause 1: cardinality *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom THEN
     FULL_SIMP_TAC (srw_ss()++ARITH_ss) [pred_setTheory.CARD_DIFF_EQN],
     (* clause 2: finite *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom THEN
     FULL_SIMP_TAC (srw_ss()++ARITH_ss) [pred_setTheory.CARD_DIFF_EQN],
     (* clause 3: mode *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom  THEN
     UNDISCH_ALL_TAC THEN
     REPEAT CASE_TAC THEN
     TRY (Cases_on `r`) THEN
     FULL_SIMP_TAC (srw_ss()) [Frpl_ALT_DEF, iMode_def, MODE_upd_lem, idCGreset_axiom, CGreset_axiom],
     (* clause 4: empty req_sent if inactive *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom,
     (* clause 5: flushed if inactive *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom,
     (* clause 6: inactive on launch *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom THEN
     UNDISCH_ALL_TAC THEN
     REPEAT CASE_TAC THEN
     RW_TAC arith_ss [] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN 
     METIS_TAC [idcore_step_axiom // "rcv_psci"],
     (* clause 7: curr_va updated on send, otherwise req_sent' empty,
	   not needed *)
     `idcore_req_sent C' <> EMPTY` by (
         CCONTR_TAC >>
         FULL_SIMP_TAC (srw_ss()) [pred_setTheory.NOT_IN_EMPTY]
     ) >>
     `FINITE (idcore_req_sent C')` by (
         FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
         IMP_RES_TAC idcore_step_axiom THEN
         FULL_SIMP_TAC (srw_ss()++ARITH_ss) [pred_setTheory.CARD_DIFF_EQN]
     ) >>
     `CARD (idcore_req_sent C') = 1` by (
         `CARD (idcore_req_sent C') <= 1` by (
             FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
             IMP_RES_TAC idcore_step_axiom THEN
             FULL_SIMP_TAC (srw_ss()++ARITH_ss) [pred_setTheory.CARD_DIFF_EQN]
         ) >>
         `CARD (idcore_req_sent C') <> 0` by (
     	     METIS_TAC [pred_setTheory.CARD_EQ_0]
     	 ) >>
     	 DECIDE_TAC
     ) >>
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom THEN
     UNDISCH_ALL_TAC THEN
     REPEAT CASE_TAC THEN
     RW_TAC arith_ss [] THEN
     IMP_RES_TAC pred_setTheory.CARD_DIFF_EQN >>
     FULL_SIMP_TAC (srw_ss()++ARITH_ss) [pred_setTheory.NOT_IN_EMPTY,
     					 IN_INTER_SING_lem] >>
     METIS_TAC [idcore_step_axiom // "snd_req"],
     (* clause 8: empty req_sent on flush *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom THEN
     METIS_TAC [next_int_not_flushed_lem, delete_only_element_lem],
     (* postpone clauses 9 -12 *)
     ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC]
    THEN
    ((* clauses 9 - 12: internal state waiting for GIC reply *)
     FULL_SIMP_TAC std_ss [idcore_step_CASES] THEN
     IMP_RES_TAC idcore_step_axiom THEN
     TRY (Cases_on `r`) THEN
     FULL_SIMP_TAC bool_ss [id_abs_int_def, next_int_snd_def] THEN
     UNDISCH_ALL_TAC THEN
     REPEAT CASE_TAC THEN
     Cases_on `cis_abs (idcore_int C')` THEN
     Cases_on `cis_abs (idcore_int C)` THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     METIS_TAC [Rreq_def, Wreq_def, idcore_gicd_rrpl_def, PAdr_rw_lem, MsgOf_rewrites,
               max_one_element_lem, obvious_req_rep_attributes_lem]));




(************* guest internal invariant ***************)



(* helping lemma to quickly deal with preproven or assumed invariants *)
val preproven_idg_invariants =
      prove(``InvG (G, g) ==> ideal_guest_trans(G,g,R,G') ==>
             (idg_inv (G',g,IDG_GOOD_IDCORE) /\ idg_inv(G',g,IDG_GOOD_PER) /\ idg_inv(G',g,IDG_GOOD_MEM))``,
               REWRITE_TAC [ideal_guest_trans_def] >>
               (Cases_on `R`)  >> 
               (Cases_on `I'`) >>
               RW_TAC pure_ss [InvG_def] >>
               PAT_X_ASSUM ``!inv:IDG_INVS. X``
                    (fn th => MAP_EVERY
                    (fn i => ASSUME_TAC (SPEC i th)) [``IDG_GOOD_IDCORE``,``IDG_GOOD_MEM``,``IDG_GOOD_PER``]) >>
               UNDISCH_ALL_TAC >>
               computeLib.RESTR_EVAL_TAC [``inv_good_idcore``, ``inv_good_mem``, ``inv_good_per_wrap``, ``idcore_step``, ``mem_step``, ``per_wrap_step``] >>
               REPEAT STRIP_TAC >>
               RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
               METIS_TAC [inv_good_idcore_lem, inv_good_mem_axiom, inv_good_per_wrap_lem]
);


(* Proof of ideal guest-internal invariants:
   about 31 transitions x 20 invariant clauses = 620 combinations,
   whereof roughly 300 non-trivial subgoals 
   --
   The proof employs machinery from idealInvProofLib.
   This library includes a "strategy", a data structure that maps
   invariant clauses to a set of definitions, theorems, corollaries and tactics,
   which then will be employed here in case the respective clause
   is identified in the subgoal.
   The intention is to be able to come up with a rather universal 
   brief proof description that is agnostic on whether case splits
   are done on invariant clauses or on transitions first. *)


val InvG_thm = store_thm("InvG_thm",
    ``!g G G' R. g < PAR.ng ==> InvG (G, g) ==> ideal_guest_trans(G,g,R,G') ==> InvG(G',g)``,
    (* deal with preproven/assumed invariants *)
    REPEAT STRIP_TAC >>
    IMP_RES_TAC preproven_idg_invariants >>
    (* for all others, case distinction for applied transition *)
    FULL_SIMP_TAC (srw_ss()) [ideal_guest_trans_def] >>
    TRY (Cases_on `R`)  >> 
    TRY (Cases_on `I'`) >>
    PAT_X_ASSUM ``InvG (G, g)``
      (fn t => ASSUME_TAC t >>
               FULL_SIMP_TAC (srw_ss()) [InvG_EXPAND, idg_inv_def] >>
               ASSUME_TAC t) >>
    UNFOLD_STEP_PREDICATE_TAC >>
    (* some invariants are trivial, since their components are not affected *)
    FULL_SIMP_TAC (srw_ss()) id_inv_alternative_defs >>
    (* unfold semantics and split off into 
       one transition vs. one invariant clause per subgoal *)
    FIND_STEP_PREDICATES_TAC all_step_axioms IMP_RES_TAC >>
    REPEAT STRIP_TAC >>
    IMP_RES_TAC good_match_lem >>
    FULL_SIMP_TAC (srw_ss()) [FORALL_AND_THM, combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID] >>
    (* for each subgoal, do the following steps;
      here, tactical WITH_CTX extracts constants from the goal and provides them
      via parameter c to some tailored tactics/tacticals:
        - II_CTX_TAC applies the tactics which the strategy datastructure
                     associates with the identified constants 
        - II_CTX_MET extracts theorems from the strategy datastructure
                     that are relevant for the identified constants
                     and provides them to a METIS solver tactic
        - II_CTX_COR is used to enhance the assertion list
                     based on the InvG corollaries *)
    WITH_CTX
    (fn c =>
      (* unfold involved clauses and split cases *)
      REPEAT IF_CASES_TAC >>
      II_GL_RW ((FULL_SIMP_TAC (srw_ss())) o (map UNIQUE_REQ)) >>
      REPEAT GEN_TAC >>
      REPEAT DISCH_TAC >>
      REWRITE_TAC [combinTheory.APPLY_UPDATE_THM] >>
      REPEAT IF_CASES_TAC >>
      (* include corollaries, simplify and apply clause specific tactics and Metis *)
      II_CTX_COR c ((MAP_EVERY IMP_RES_TAC) o (map UNIQUE_REQ)) >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, 
				optionTheory.SOME_11] >>
      REV_FULL_SIMP_TAC (srw_ss()) [] >>
      II_CTX_TAC c >>
      II_CTX_MET c (fn l => TRY (INFS_LIMITED_METIS_TAC 1 ([not_all_req_rep_lem, match_ReqOf_lem, inv_good_per_wrap_def, optionTheory.IS_SOME_EXISTS]@l)))
    )
    (* Peripheral cases, treat separately *)
    >| [Cases_on `r = ReqOf q` >> (
            FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
            INFS_LIMITED_METIS_TAC 1 [not_all_req_rep_lem, match_ReqOf_lem, inv_good_per_wrap_def, optionTheory.IS_SOME_EXISTS, optionTheory.SOME_11]
	)
	,
	INFS_LIMITED_METIS_TAC 1 [not_all_req_rep_lem, match_ReqOf_lem, inv_good_per_wrap_def, optionTheory.IS_SOME_EXISTS, optionTheory.SOME_11]
	,
	Cases_on `ReqOf r = ReqOf q'` >> (
            FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
            INFS_LIMITED_METIS_TAC 1 [not_all_req_rep_lem, match_ReqOf_lem, inv_good_per_wrap_def, optionTheory.IS_SOME_EXISTS, optionTheory.SOME_11]
	)
	,
	FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
       ]
);


(************* other parts of the composed invariant  ***************)


val syncInv_lem = store_thm("syncInv_lem",
     ``!IM IM'. syncInv IM /\ (!g. g < PAR.ng ==> (mem_abs (IM.G g).m = mem_abs (IM'.G g).m))
            ==> syncInv IM'``,
     RW_TAC (srw_ss()) [syncInv_def]
       THEN METIS_TAC []);


(* incoming channels are read-only,
   somewhat a guest internal-invariant, but since it does not hold globally
   in the composed model, we don't include it into InvG. *)
val igc_in_read_only_lem =
    store_thm("igc_in_read_only_lem",
    ``!G G' g a x. InvG (G,g)
        ==> (a IN receiverMem g)
        ==> ideal_guest_trans (G,g,INTERNAL x,G')
        ==> (mem_abs G'.m a = mem_abs G.m a)``,
   RW_TAC (srw_ss()) [InvG_def, fall_constructors_thm_of ``:IDG_INVS``]
     THEN UNDISCH_ALL_TAC
     THEN computeLib.RESTR_EVAL_TAC [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``, ``base_adr``,
                                     ``Frpl``, ``gicd_req_ok``, ``Wreq``]
     THEN RW_TAC (srw_ss()) []
     THEN Cases_on `x`
     THEN FULL_SIMP_TAC (srw_ss()) []
     THEN RW_TAC (srw_ss()) []
     THEN FIND_STEP_PREDICATES_TAC all_step_axioms IMP_RES_TAC
     THEN FULL_SIMP_TAC (srw_ss()) []
     THEN TRY (LIMITED_METIS_TAC 1 [])
     THEN FIND_STEP_PREDICATES_TAC [mem_read_axiom, mem_write_axiom, mem_fault_axiom, mem_walk_axiom] IMP_RES_TAC
     THEN FULL_SIMP_TAC (srw_ss()) []
     THEN MP_TAC (SPECL [``q':request``, ``r:reply``] resolve_match_cases_lem)
     THEN RW_TAC (srw_ss()) []
     THEN FULL_SIMP_TAC (srw_ss()) [Frpl_def]
     THEN METIS_TAC [memory_upd_axiom, PAdrWrite_lem]);


(* memory_upd preserves the InvG invariant *)
val memory_upd_preserves_InvG_lem =
    store_thm("memory_upd_preserves_InvG_lem",
    ``!G G' g a v. (g < PAR.ng) ==> InvG(G,g) ==> (G' = G with m := memory_upd(a,v) (G.m))
       ==> InvG(G',g)``,
         RW_TAC (srw_ss()) [InvG_def, fall_constructors_thm_of ``:IDG_INVS``]
    THEN UNDISCH_ALL_TAC
    THEN computeLib.RESTR_EVAL_TAC [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``]
    THEN TRY (LIMITED_METIS_TAC 1 [memory_upd_axiom]));




(************* composed invariant: induction start  ***************)


val InvIstart_lem = store_thm("InvIstart_lem",
    ``!M. id_start M ==> InvI M``,
    RW_TAC (srw_ss()) [id_start_def, InvI_def]
    THENL [(* guest internal invariant *)
                SPEC_ASSUM_TAC (``!g:num. X``, [``g:num``])
           THEN UNDISCH_ALL_TAC
           THEN RW_TAC (srw_ss()) [InvG_def, fall_constructors_thm_of ``:IDG_INVS``]
           THEN UNDISCH_ALL_TAC
           THEN computeLib.RESTR_EVAL_TAC [``MODE``]
           THEN RW_TAC (srw_ss()) [idCGreset_axiom, CGreset_axiom, per_reset_axiom]
           THEN METIS_TAC [],
           (* sync invariant *)
                RW_TAC (srw_ss()) [syncInv_def]
           THEN FST_AND_SND_TAC
           THEN FULL_SIMP_TAC (srw_ss()) []
           THEN METIS_TAC [goodP_axiom]]);



(************* composed invariant: restructuring  ***************)


(* invariant preserved (induction step) *)
val InvI_preserve_lem = store_thm("InvI_preserve_lem", ``
!M n M'. InvI M ==> ideal_model_comp(M, n, M') ==> InvI M'
``,
(* induction over number of steps *)
     NTAC 2 GEN_TAC
THEN Induct_on `n`
THENL [(* 1. base case *)
            FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def],
       (* 2. induction step *)
            RW_TAC (srw_ss()) [ideal_model_comp_def]
       THEN FULL_SIMP_TAC (srw_ss()) [InvI_def]
       THEN RW_TAC (srw_ss()) []
       THEN RES_TAC
       THENL [(* 2.1. guest internal invariant *)
                   FULL_SIMP_TAC (srw_ss()) [ideal_model_trans_def]
              THEN Cases_on `R'`
              THEN FULL_SIMP_TAC (srw_ss()) []
              THENL [(* 2.1.1. guest internal step *)
                          FULL_SIMP_TAC (srw_ss()) [comp_rule_internal_def]
                     THEN `InvG (G',g')` by METIS_TAC [InvG_thm]
                     THEN FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def,
                                                    do_sync_shared_mem_upd_of_guest_def,
                                                    combinTheory.APPLY_UPDATE_THM]
                     THEN RW_TAC (srw_ss()) []
                     THEN UNDISCH_ALL_TAC
                     THEN IF_CASES_TAC
                     THEN RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
                     THEN FULL_SIMP_TAC (srw_ss()) []
                     THEN Cases_on `g = g'`
                     THEN FULL_SIMP_TAC (srw_ss()) [goodP_axiom]
                     THEN RES_TAC
                           (* TODO: simplify the following part *)
                     THENL [(*2.1.1.1. active guest *)
                                 `(!s. ~(s < PAR.ns) \/ PAR.cpol s <> (g',g'))`
                                  by (     FST_AND_SND_TAC
                                      THEN REV_FULL_SIMP_TAC (srw_ss()) []
                                      THEN METIS_TAC [FST_AND_SND_RULE goodP_axiom])
                            THEN RES_TAC
                            THEN FULL_SIMP_TAC (srw_ss()) []
                            THEN `?memo. X g' = G' with m := memo` by (METIS_TAC [])
                            THEN `memo = (X g).m`
                                  by (     FULL_SIMP_TAC (srw_ss()) []
                                      THEN REV_FULL_SIMP_TAC (srw_ss()) [])
                            THEN REV_FULL_SIMP_TAC (srw_ss()) [SPEC_ALL guest_trivial_upd_m_lem |> SYM],
                            (* 2.1.1.2. foreign guests *)
                                 `   ((X g).m = (IM''.G g).m)
                                  \/ (?ad va. (X g).m = memory_upd (ad,va) (IM''.G g).m)`
                                  by (     RW_TAC (srw_ss()) []
                                      THEN FST_AND_SND_TAC
                                      THEN REV_FULL_SIMP_TAC (srw_ss()) []
                                      THEN METIS_TAC [goodP_axiom])
                            THEN `?memo. X g = (IM''.G g) with m := memo ` by (METIS_TAC [])
                            THENL [(* 2.1.1.2.1. not receiver *)
                                        `memo = (X g).m`
                                         by (     FULL_SIMP_TAC (srw_ss()) []
                                             THEN REV_FULL_SIMP_TAC (srw_ss()) [])
                                   THEN REV_FULL_SIMP_TAC (srw_ss()) [SPEC_ALL guest_trivial_upd_m_lem |> SYM],
                                   (* 2.1.1.2.2. updated receiver memory *)
                                        `memo = (memory_upd (ad,va) (IM''.G g).m)`
                                         by (     FULL_SIMP_TAC (srw_ss()) []
                                             THEN REV_FULL_SIMP_TAC (srw_ss()) [])
                                    THEN FULL_SIMP_TAC (srw_ss()) []
                                    THEN REV_FULL_SIMP_TAC (srw_ss()) []
                                    THEN METIS_TAC [memory_upd_preserves_InvG_lem]]],
                     (* 2.1.2. IGC signal *)
                          FULL_SIMP_TAC (srw_ss()) [comp_rule_igc_def,
                                                    combinTheory.APPLY_UPDATE_THM]
                     THEN METIS_TAC [InvG_thm],
                     (* 2.1.3. RCU signal *)
                          FULL_SIMP_TAC (srw_ss()) [comp_rule_rcu_def,
                                                    combinTheory.APPLY_UPDATE_THM]
                     THEN METIS_TAC [InvG_thm]],
              (* 2.2. sync invariant *)
                   FULL_SIMP_TAC (srw_ss()) [syncInv_def]
              THEN RW_TAC (srw_ss()) []
              THEN FULL_SIMP_TAC (srw_ss()) [ideal_model_trans_def]
              THEN Cases_on `R'`
              THEN FULL_SIMP_TAC (srw_ss()) []
              THENL [(* 2.2.1. guest internal step *)
                          FULL_SIMP_TAC (srw_ss()) [comp_rule_internal_def,
                                                    combinTheory.APPLY_UPDATE_THM,
                                                    sync_shared_mem_upd_of_guest_def,
                                                    do_sync_shared_mem_upd_of_guest_def]
                     THEN RW_TAC (srw_ss()) []
                     THEN UNDISCH_ALL_TAC
                     THEN TRY IF_CASES_TAC
                     THEN RW_TAC (srw_ss()) []
                     THEN RES_TAC
                     THEN Cases_on `g = g1`
                     THEN Cases_on `g = g2`
                     THEN FULL_SIMP_TAC (srw_ss()) []
                     THEN TRY (FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, syncInv_def]
                               THEN LIMITED_METIS_TAC 1 [goodP_axiom])
                     THENL [(* 2.2.1.1.  g1 --> g2 = g *)
                                 IMP_RES_TAC (SIMP_RULE (srw_ss()) [receiverMem_def] igc_in_read_only_lem)
                            THEN FST_AND_SND_TAC
                            THEN FULL_SIMP_TAC (srw_ss()) []
                            THEN METIS_TAC [goodP_axiom],
                            (* 2.2.1.2.  g1 <> g <> g2 *)
                                 `!s. (~(s < PAR.ns)) \/ (PAR.cpol s <> (g, g2)) \/ (SND (PAR.igca s) <> a2)`
                                  by (     FST_AND_SND_TAC
                                      THEN FULL_SIMP_TAC (srw_ss()) []
                                      THEN METIS_TAC [goodP_axiom])
                            THEN `!s. (~(s < PAR.ns)) \/ (PAR.cpol s <> (g, g1)) \/ (SND (PAR.igca s) <> a1)`
                                  by (     FST_AND_SND_TAC
                                           THEN FULL_SIMP_TAC (srw_ss()) []
                                           THEN METIS_TAC [goodP_axiom])
                            THEN FULL_SIMP_TAC (srw_ss()) []],
                     (* 2.2.2. IGC signal *)
                          FULL_SIMP_TAC (srw_ss()) [comp_rule_igc_def, combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID, ideal_guest_trans_def, id_rule_external_snd_igc_def, id_rule_external_rcv_igc_def]
                     THEN RW_TAC (srw_ss()) []
                     THEN METIS_TAC [],
                     (* 2.2.3. RCU signal *)
                          FULL_SIMP_TAC (srw_ss()) [comp_rule_rcu_def, combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID, ideal_guest_trans_def, id_rule_external_snd_rcu_def, id_rule_external_rcv_rcu_def]
                     THEN RW_TAC (srw_ss()) []
                     THEN METIS_TAC []]]]);



(* THEOREM: invariant preserved *)
val InvI_lem = store_thm("InvI_lem",
      ``!M n M'. good_ideal_comp(M, n, M') ==> InvI M'``,
      RW_TAC (srw_ss()) [good_ideal_comp_def]
        THEN IMP_RES_TAC InvIstart_lem
        THEN IMP_RES_TAC InvI_preserve_lem);


val ideal_model_trans_InvI_lem =
    store_thm("ideal_model_trans_InvI_lem",
    ``!IM R IM'. ideal_model_trans (IM, R, IM') ==>  InvI IM ==> InvI IM'``,
    RW_TAC (srw_ss()) []
     THEN IMP_RES_TAC InvI_preserve_lem
     THEN SPEC_ASSUM_TAC (``!n:num M:ideal_model. X``, [``SUC 0``])
     THEN FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def]
     THEN METIS_TAC []);




(*************** finish ***********)

val _ = export_theory();
