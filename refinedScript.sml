(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 
open tacticsLib; 

open axtypesTheory;
open haspoctypesTheory;
open parametersTheory;
open axfuncsTheory;
open hypervisorTheory;

val _ = new_theory "refined";

(******************** HELPER FUNCTIONS **********************)

(* outstanding reply for core c *)

val pend_rpl_def = Define `pend_rpl (MMUrpl, MEMrpl, c:num, q:reply) = 
(q, CoreSender c) IN MEMrpl \/ q IN MMUrpl
`;


(******************** REFINED MODEL **********************)

(************* Hypervisor steps *****************)

val hv_step_def = Define `hv_step (hv : hv_state, c :num, a : Action, hv' : hv_state) =
	case a of
          | RCV (MRPL r) => hv_ts(hv, c, SOME r) = SOME (hv', NONE, NONE)
          | SEND (PSCIL l) => hv_ts(hv, c, NONE) = SOME (hv', NONE, SOME l)
          | SEND (MREQ r) => hv_ts(hv, c, NONE) = SOME (hv', SOME r, NONE)
          | TAU => hv_ts(hv, c, NONE) = SOME (hv',NONE,NONE)
          | _   => F
`;

(**************** Synchronized Steps *****************)

(* NOTE: prioritization betweem physical and virtual interrupts 
   implementation-dependent, treat equally here *)
val ref_rule_core_rcv_irq_def = Define `ref_rule_core_rcv_irq (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) < 2 /\
?C' GIC'. 
       (      refcore_step(M.C c, RCV(PHYS NONE c), C') 
	   /\ gic_step(M.GIC,SEND(PHYS NONE c), GIC')
        \/    refcore_step(M.C c, RCV(VIRT c), C') 
           /\ gic_step(M.GIC,SEND(VIRT c),GIC')
       )
    /\ (M' = M with <| C := (c =+ C') M.C; GIC := GIC'|>)
`;

val ref_rule_core_rcv_mrpl_def = Define `ref_rule_core_rcv_mrpl (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) < 2 /\
?r C' MMU' q. 
             refcore_step(M.C c, RCV(MRPL r), C') 
	  /\ mmu_step(M.MMU c, SEND(MRPL r), MMU') 
	  /\ q IN refcore_req_sent (M.C c) /\ match(q,r)
	  /\ (M' = M with <| C := (c =+ C') M.C; MMU := (c =+ MMU') M.MMU|>)
`;

val ref_rule_core_rcv_event_def = Define `ref_rule_core_rcv_event (M : refined_model, c : num, M' : refined_model) = 
?e PS' C'. 
            psci_step(M.PSCI, SEND(PSCI e), c :num, PS') 
         /\ refcore_step(M.C c, RCV(PSCI e), C') 
         /\ ((e = StartCore c) \/ (e = StopCore c))
	 (* NOTE: simplification, never stop core during handler *)
         /\ ((e = StopCore c) ==> Mode (M.C c) < 2)
	 (* NOTE: simplification, never send start core during handler *)
         /\ ((e = StartCore c) ==> (~(refcore_abs (M.C c)).active /\
		                    Mode (M.C c) <> 2 \/ 
				    Mode (M.C c) < 2))
         /\ (M' = M with <| C := (c =+ C') M.C; PSCI := PS'|>)
`;

val ref_rule_core_snd_mreq_def = Define `ref_rule_core_snd_mreq (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) < 2 /\
?r C' MMU'. 
             refcore_step(M.C c, SEND(MREQ r), C') 
          /\ mmu_step(M.MMU c, RCV(MREQ r), MMU') 
          /\ (M' = M with <| C := (c =+ C') M.C; MMU := (c =+ MMU') M.MMU|>)
`;

val ref_rule_core_internal_def = Define `ref_rule_core_internal (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) < 2 /\
?C'. refcore_step(M.C c, TAU, C') /\ (M' = M with <| C := (c =+ C') M.C|>)
`;

val ref_rule_hv_rcv_mrpl_def = Define `ref_rule_hv_rcv_mrpl (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) >= 2 /\
?r hv' MMU'. 
              hv_step(HVabs(M,c), c, RCV(MRPL r), hv') 
           /\ mmu_step(M.MMU c, SEND(MRPL r), MMU') 
           /\ (M' = HVupd(M,hv',c) with <| MMU := (c =+ MMU') M.MMU |>)
`;

val ref_rule_hv_snd_elist_def = Define `ref_rule_hv_snd_elist (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) >= 2 /\
?l hv', PS'. 
              hv_step(HVabs(M,c), c, SEND(PSCIL l), hv') 
           /\ psci_step(M.PSCI, RCV(PSCIL l), c, PS') 
           /\ (M' = HVupd(M,hv',c) with <| PSCI := PS' |>)
`;

val ref_rule_hv_snd_mreq_def = Define `ref_rule_hv_snd_mreq (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) >= 2 /\
?r hv' MMU'. 
              hv_step(HVabs(M,c), c, SEND(MREQ r), hv') 
           /\ mmu_step(M.MMU c, RCV(MREQ r), MMU') 
           /\ (M' = HVupd(M,hv',c) with <| MMU := (c =+ MMU') M.MMU|>)
`;

val ref_rule_hv_internal_def = Define `ref_rule_hv_internal (M : refined_model, c : num, M' : refined_model) = 
Mode (M.C c) >= 2 /\
?hv'. hv_step(HVabs(M,c), c, TAU, hv') /\ (M' = HVupd(M,hv',c))
`;

val ref_rule_mmu_snd_mreq_def = Define `ref_rule_mmu_snd_mreq (M : refined_model, c : num, M' : refined_model) = 
?r MMU' m'. 
             mmu_step(M.MMU c, SEND(SREQ r (CoreSender c)), MMU') 
          /\ mem_step(M.m, RCV(SREQ r (CoreSender c)), NONE, m') 
          /\ (M' = M with <|MMU := (c =+ MMU') M.MMU; m := m'|>)
`;

val ref_rule_mmu_rcv_mrpl_def = Define `ref_rule_mmu_rcv_mrpl (M : refined_model, c : num, M' : refined_model) = 
?r MMU' m' q. 
             mmu_step(M.MMU c, RCV(SRPL r (CoreSender c)), MMU') 
          /\ mem_step(M.m, SEND(SRPL r (CoreSender c)), NONE, m') 
	  /\ q IN mmu_req_sent (M.MMU c) /\ match(q,r)
          /\ (M' = M with <|MMU := (c =+ MMU') M.MMU; m := m'|>)
`;

val ref_rule_mmu_internal_def = Define `ref_rule_mmu_internal (M : refined_model, c : num, M' : refined_model) = 
?MMU'. mmu_step(M.MMU c, TAU, MMU') /\ (M' = M with <|MMU := (c =+ MMU') M.MMU|>)
`;

val ref_rule_per_rcv_dmarpl_def = Define `ref_rule_per_rcv_dmarpl (M : refined_model, p : num, M' : refined_model) = 
?r SMMU' P' q. 
              mmu_step(M.SMMU p, SEND(MRPL r), SMMU') 
           /\ per_wrap_step(M.P p, RCV(MRPL r), P') 
           /\ q IN per_req_sent (M.P p).st /\ match(q,r)
           /\ (M' = M with <|SMMU := (p =+ SMMU') M.SMMU; P := (p =+ P') M.P|>)
`;

(* fix cores as sole IO request senders, can be extended here *)
val ref_rule_per_rcv_ioreq_def = Define `ref_rule_per_rcv_ioreq (M : refined_model, p : num, M' : refined_model) = 
?r m' P' c. 
             c < RPAR.nc /\ PAdr r IN RPAR.Amap (PER p) 
          /\ mem_step(M.m, SEND(SREQ r (CoreSender c)), NONE, m') 
          /\ per_wrap_step(M.P p, RCV(SREQ r (CoreSender c)), P') 
          /\ (M' = M with <|m := m'; P := (p =+ P') M.P|>)
`;

val ref_rule_per_rcv_pev_def = Define `ref_rule_per_rcv_pev (M : refined_model, p : num, M' : refined_model) = 
?P'. per_wrap_step(M.P p, RCV(PEV (rPEF(M.E_in, p))), P') /\ 
     (M' = M with <|P := (p =+ P') M.P|>)
`;

val ref_rule_per_snd_dmareq_def = Define `ref_rule_per_snd_dmareq (M : refined_model, p : num, M' : refined_model) = 
?r SMMU' P'. 
              mmu_step(M.SMMU p, RCV(MREQ r), SMMU') 
           /\ per_wrap_step(M.P p, SEND(MREQ r), P') 
           /\ (M' = M with <|SMMU := (p =+ SMMU') M.SMMU; P := (p =+ P') M.P|>)
`;

(* fix cores as sole IO request senders, can be extended here *)
val ref_rule_per_snd_iorpl_def = Define `ref_rule_per_snd_iorpl (M : refined_model, p : num, M' : refined_model) = 
?r m' P' c q. 
             c < RPAR.nc
          /\ mem_step(M.m, RCV(SRPL r (CoreSender c)), NONE, m') 
          /\ per_wrap_step(M.P p, SEND(SRPL r (CoreSender c)), P') 
          /\ (q, CoreSender c) IN mem_req_sent (M.m) /\ match(q,r)
          /\ (M' = M with <|m := m'; P := (p =+ P') M.P|>)
`;

val ref_rule_per_snd_pev_def = Define `ref_rule_per_snd_pev (M : refined_model, p : num, M' : refined_model) = 
?P' l. 
        per_wrap_step(M.P p, SEND(PEV l), P') 
     /\ (!e. MEM e l ==> (evper e = p))
     /\ (M' = M with <|P := (p =+ P') M.P; E_out := M.E_out ++ l|>)
`;

val ref_rule_per_snd_irq_def = Define `ref_rule_per_snd_irq (M : refined_model, p : num, M' : refined_model) = 
?P' q GIC'. 
	(PIR q) IN RPAR.pirq_p(p)
     /\ q >= 16
     /\ q < 1020
     /\ per_wrap_step(M.P p, SEND(PERQ (PIR q)), P') 
     /\ gic_step(M.GIC, RCV(PERQ (PIR q)), GIC')
     /\ (M' = M with <|P := (p =+ P') M.P; GIC := GIC'|>)
`;

val ref_rule_per_internal_def = Define `ref_rule_per_internal (M : refined_model, p : num, M' : refined_model) = 
?P'. per_wrap_step(M.P p, TAU, P') /\ (M' = M with <|P := (p =+ P') M.P|>)
`;

val ref_rule_smmu_snd_dmareq_def = Define `ref_rule_smmu_snd_dmareq (M : refined_model, p : num, M' : refined_model) = 
?r SMMU' m'. 
              mmu_step(M.SMMU p, SEND(SREQ r (PeripheralSender p)), SMMU') 
           /\ mem_step(M.m, RCV(SREQ r (PeripheralSender p)), NONE, m') 
           /\ (M' = M with <|SMMU := (p =+ SMMU') M.SMMU; m := m'|>)
`;

val ref_rule_smmu_rcv_dmarpl_def = Define `ref_rule_smmu_rcv_dmarpl (M : refined_model, p : num, M' : refined_model) = 
?r SMMU' m' q. 
              mmu_step(M.SMMU p, RCV(SRPL r (PeripheralSender p)), SMMU') 
           /\ mem_step(M.m, SEND(SRPL r (PeripheralSender p)), NONE, m') 
           /\ q IN mmu_req_sent (M.SMMU p) /\ match(q,r)
           /\ (M' = M with <|SMMU := (p =+ SMMU') M.SMMU; m := m'|>)
`;

val ref_rule_smmu_internal_def = Define `ref_rule_smmu_internal (M : refined_model, p : num, M' : refined_model) = 
?SMMU'. mmu_step(M.SMMU p, TAU, SMMU') /\ (M' = M with <|SMMU := (p =+ SMMU') M.SMMU|>)
`;

(* IO requests to the GIC only from Cores *)
val ref_rule_gic_rcv_ioreq_def = Define `ref_rule_gic_rcv_ioreq (M : refined_model, M' : refined_model) = 
?r m' GIC' c a. 
             gicAR a /\ PAdr r IN RPAR.Amap a /\ c < RPAR.nc
          /\ mem_step(M.m, SEND(SREQ r (CoreSender c)), NONE, m') 
          /\ gic_step(M.GIC, RCV(SREQ r (CoreSender c)), GIC') 
          /\ (M' = M with <|m := m'; GIC := GIC'|>)
`;

val ref_rule_gic_snd_iorpl_def = Define `ref_rule_gic_snd_iorpl (M : refined_model, M' : refined_model) = 
?r m' GIC' c q. 
	     c < RPAR.nc
          /\ gic_step(M.GIC, SEND(SRPL r (CoreSender c)), GIC') 
          /\ mem_step(M.m, RCV(SRPL r (CoreSender c)), NONE, m') 
          /\ (q, CoreSender c) IN mem_req_sent (M.m) /\ match(q,r)
          /\ (M' = M with <|m := m'; GIC := GIC'|>)
`;

val ref_rule_mem_internal_def = Define `ref_rule_mem_internal (M : refined_model, M' : refined_model) = 
?m'. mem_step(M.m, TAU, NONE, m') /\ (M' = M with <|m := m'|>)
`;

(**************** Refined Model Transition System ***************)

val _ = Datatype `Refined_Rule = CORE_RCV_IRQ num | CORE_RCV_MRPL num | CORE_RCV_EVENT num | CORE_SND_MREQ num | CORE_INTERNAL num | HV_RCV_MRPL num | HV_SND_ELIST num | HV_SND_MREQ num | HV_INTERNAL num | MMU_SND_MREQ num | MMU_RCV_MRPL num | MMU_INTERNAL num | PER_RCV_DMARPL num | PER_RCV_IOREQ num | PER_RCV_PEV num | PER_SND_DMAREQ num | PER_SND_IORPL num | PER_SND_PEV num | PER_SND_IRQ num | PER_INTERNAL num | SMMU_RCV_DMARPL num | SMMU_SND_DMAREQ num | SMMU_INTERNAL num | GIC_RCV_IOREQ | GIC_SND_IORPL | MEM_INTERNAL`;

val refined_trans_def = Define `refined_trans (M : refined_model, R : Refined_Rule, M' : refined_model) =
	case R of
          | CORE_RCV_IRQ c0 => c0 < RPAR.nc /\ ref_rule_core_rcv_irq(M,c0,M')
          | CORE_RCV_MRPL c1 => c1 < RPAR.nc /\ ref_rule_core_rcv_mrpl(M,c1,M')
          | CORE_RCV_EVENT c2 => c2 < RPAR.nc /\ ref_rule_core_rcv_event(M,c2,M')
          | CORE_SND_MREQ c3 => c3 < RPAR.nc /\ ref_rule_core_snd_mreq(M,c3,M')
          | CORE_INTERNAL c4 => c4 < RPAR.nc /\ ref_rule_core_internal(M,c4,M')
          | HV_RCV_MRPL c5 => c5 < RPAR.nc /\ ref_rule_hv_rcv_mrpl(M,c5,M')
          | HV_SND_ELIST c6 => c6 < RPAR.nc /\ ref_rule_hv_snd_elist(M,c6,M')
          | HV_SND_MREQ c7 => c7 < RPAR.nc /\ ref_rule_hv_snd_mreq(M,c7,M')
          | HV_INTERNAL c8 => c8 < RPAR.nc /\ ref_rule_hv_internal(M,c8,M')
          | MMU_RCV_MRPL c9 => c9 < RPAR.nc /\ ref_rule_mmu_rcv_mrpl(M,c9,M')
          | MMU_SND_MREQ c10 => c10 < RPAR.nc /\ ref_rule_mmu_snd_mreq(M,c10,M')
          | MMU_INTERNAL c11 => c11 < RPAR.nc /\ ref_rule_mmu_internal(M,c11,M')
          | PER_RCV_DMARPL p0 => p0 < RPAR.np /\ ref_rule_per_rcv_dmarpl(M,p0,M')
          | PER_RCV_IOREQ p1 => p1 < RPAR.np /\ ref_rule_per_rcv_ioreq(M,p1,M')
          | PER_RCV_PEV p2 => p2 < RPAR.np /\ ref_rule_per_rcv_pev(M,p2,M')
          | PER_SND_DMAREQ p3 => p3 < RPAR.np /\ per_active (M.P p3).st
			      /\ ref_rule_per_snd_dmareq(M,p3,M')
          | PER_SND_IORPL p4 => p4 < RPAR.np /\ per_active (M.P p4).st
			     /\ ref_rule_per_snd_iorpl(M,p4,M')
          | PER_SND_PEV p5 => p5 < RPAR.np /\ per_active (M.P p5).st
			   /\ ref_rule_per_snd_pev(M,p5,M')
          | PER_SND_IRQ p6 => p6 < RPAR.np /\ per_active (M.P p6).st
			   /\ ref_rule_per_snd_irq(M,p6,M')
          | PER_INTERNAL p7 => p7 < RPAR.np /\ ref_rule_per_internal(M,p7,M')
          | SMMU_RCV_DMARPL p8 => p8<RPAR.np /\ ref_rule_smmu_rcv_dmarpl(M,p8,M')
          | SMMU_SND_DMAREQ p9 => p9<RPAR.np /\ ref_rule_smmu_snd_dmareq(M,p9,M')
          | SMMU_INTERNAL p10 => p10<RPAR.nc /\ ref_rule_smmu_internal(M,p10,M')
          | GIC_RCV_IOREQ => ref_rule_gic_rcv_ioreq(M,M')
          | GIC_SND_IORPL => ref_rule_gic_snd_iorpl(M,M')
          | MEM_INTERNAL => ref_rule_mem_internal(M,M')
`;



(*************** finish ***********)

val _ = export_theory();

