(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 
open tacticsLib; 

open math_lemmasTheory;
open axtypesTheory;
open haspoctypesTheory;
open parametersTheory;
open axfuncsTheory;
open hypervisorTheory;
open refinedTheory;

val _ = new_theory "refinedInv";


(* helper functions *)

val cev_def = Define `cev (e:event, c:num) =
case e of
  | StartCore c => T
  | StopCore c => T
  | _ => F
`;

val flev_def = Define `flev (el:event list, c:num) =
FOLDR (\e e'. if cev (e',c) then e' else e) (SndIgc 0) el
`;


(* refined model invariants *) 

val ref_inv_img_def = Define `ref_inv_img (M : refined_model) =
boot_images_present (mem_abs M.m)
`;

val ref_inv_psci_def = Define `ref_inv_psci (M : refined_model) =
!c. c < RPAR.nc ==> 
    (M.PSCI.pow c = (refcore_abs(M.C c)).active)
 /\ (!e. MEM e (M.PSCI.events c) ==> psciev c e)
`;

val ref_inv_gicpol_def = Define `ref_inv_gicpol (M : refined_model) =
       (gic_abs M.GIC).gicd IN gic_gm_conf
    /\ (!q. Q M.GIC q <> INACTIVE ==>
       case q of 
	 | PIR n           => n >= 16 /\ n < 1020 /\ PIR n IN refPIRQ
	 | SGI (id,c,c')   => id <= 7w /\
			      ( (PCG c = PCG c') \/ 
				(id = 7w) /\ 
				?s. s < PAR.ns /\ (PAR.cpol s = (PCG c, PCG c')) )
       ) 
    /\ (!q c. c < RPAR.nc /\ VI M.GIC c q <> INACTIVE ==>
       case q of 
(* NOTE: IGC interrupt mapped to ideal PIR *) 
	 | PIR n           => n >= 16 /\ n < 1020 /\ q IN (xPIRQ (PCG c)) 
			      /\ (q IN PIRQ (PCG c) ==> VI M.GIC c q <> PENDACT)
	 | SGI (id,c',c'') => (c = c'') /\ id <=+ 7w /\ (c' < PAR.nc_g (PCG c))
(* no SGIs for other cores pending here *)
	 | _               => F 
       )
`;
    
val ref_inv_gicc_def = Define `ref_inv_gicc (M : refined_model) =
!c. c < RPAR.nc ==> inv_gicc((gic_abs M.GIC).gicc c)
`;

val ref_inv_hist_def = Define `ref_inv_hist (M : refined_model) =
!c. c < RPAR.nc ==> 
   (mode(refcore_abs (M.C c)) < 2 ==> 
	(refcore_abs (M.C c)).H.init_boot
     /\ (refcore_abs (M.C 0)).H.init_hv
     /\ (?c'. c' < RPAR.nc /\ (PCG c' = PCG c) /\ (PCC c' = 0) /\ (refcore_abs (M.C c')).H.init_guest)
     /\ (refcore_abs (M.C c)).H.init_core
     /\ (refcore_abs (M.C c)).H.launched)
/\ (c <> 0 /\ mode(refcore_abs (M.C c)) < 3 ==> 
	(refcore_abs (M.C c)).H.init_boot)
(* secondary cold boot *)
/\ (c <> 0 /\ (mode(refcore_abs (M.C c)) = 3) /\ ((refcore_abs(M.C c)).PC = AHV PC_SLEEP) ==>
	(refcore_abs (M.C c)).H.init_boot
     /\ ~(refcore_abs (M.C c)).H.init_core
     /\ ~(refcore_abs (M.C c)).H.launched)
(* secondary warm boot *)
/\ (c <> 0 /\ warm(refcore_abs (M.C c)) ==>
	(refcore_abs (M.C c)).H.init_boot
     /\	(refcore_abs (M.C 0)).H.init_hv
     /\ ~(refcore_abs (M.C c)).H.init_guest
     /\ ((PCC c) <> 0 ==> (?c'. c' < RPAR.nc /\ (PCG c' = PCG c) /\ (PCC c' = 0) /\ (refcore_abs (M.C c')).H.init_guest))
     /\ ~(refcore_abs (M.C c)).H.init_core
     /\ ~(refcore_abs (M.C c)).H.launched)
(* soft boot *)
/\ (soft(refcore_abs (M.C c)) ==>
	(refcore_abs (M.C 0)).H.init_hv
     /\ (?c'. c' < RPAR.nc /\ (PCG c' = PCG c) /\ (PCC c' = 0) /\ (refcore_abs (M.C c')).H.init_guest)
     /\ (refcore_abs (M.C c)).H.init_core
     /\ ~(refcore_abs (M.C c)).H.launched)
(* primary boot hv_init *) 
/\ ((mode(refcore_abs (M.C c)) = 2) /\ (refcore_abs(M.C c)).PC <> AHV PC_INIT_PRIM_ENTRY ==>
	(refcore_abs (M.C 0)).H.init_hv )
(* primary boot hv_guest *) 
/\ ((mode(refcore_abs (M.C c)) = 2) /\ (refcore_abs(M.C c)).PC NOTIN {AHV PC_INIT_PRIM_ENTRY; AHV PC_INIT_PRIM} ==>
        (?c'. c' < RPAR.nc /\ (PCG c' = PCG c) /\ (PCC c' = 0) /\ (refcore_abs (M.C c')).H.init_guest) )
(* primary boot hv_core *) 
/\ ((mode(refcore_abs (M.C c)) = 2) /\ (refcore_abs(M.C c)).PC NOTIN {AHV PC_INIT_PRIM_ENTRY; AHV PC_INIT_SEC_ENTRY; AHV PC_INIT_PRIM; AHV PC_INIT_GUEST} ==>
        (refcore_abs (M.C c)).H.init_core )
(* in hypervisor after launch *) 
/\ ((mode(refcore_abs (M.C c)) = 2) /\ (refcore_abs(M.C c)).PC NOTIN {AHV PC_INIT_PRIM_ENTRY; AHV PC_INIT_SEC_ENTRY; AHV PC_INIT_PRIM; AHV PC_INIT_GUEST; AHV PC_INIT_CORE} ==>
        (refcore_abs (M.C c)).H.launched )
(* launched means all is initialized *)
/\ ((refcore_abs (M.C c)).H.launched ==>
       	(refcore_abs (M.C c)).H.init_boot
     /\ (refcore_abs (M.C 0)).H.init_hv
     /\ (?c'. c' < RPAR.nc /\ (PCG c' = PCG c) /\ (PCC c' = 0) /\ (refcore_abs (M.C c')).H.init_guest)
     /\ (refcore_abs (M.C c)).H.init_core )
`;

val ref_inv_per_active_def = Define `ref_inv_per_active (M : refined_model) =
!p c. p < RPAR.np /\ c < RPAR.nc /\ (PCG c = PPG p) /\ (PCC c = 0) 
   /\ ~(refcore_abs (M.C c)).H.launched 
==> 
~per_active (M.P p).st
`;

val ref_inv_regel3_def = Define `ref_inv_regel3 (M : refined_model) =
!c. c < RPAR.nc /\ (refcore_abs (M.C c)).H.init_boot ==> 
   ((refcore_abs (M.C c)).SPR(INR SCR_EL3) = 0b10100000001w:bool[64])
/\ ((refcore_abs (M.C c)).SPR(INR VBAR_EL3) = AHV VBAR_PSCI)
`;

val ref_inv_pow_def = Define `ref_inv_pow (M : refined_model) =
!c. c < RPAR.nc /\ (refcore_abs (M.C 0)).H.init_hv ==> 
   (pow ((mem_abs (M.m)) (ADRDS POW)) c = 
    case flev (M.PSCI.events c, c) of
      | StartCore c => T
      | StopCore c => F
      | _ => M.PSCI.pow c )
`;

val ref_inv_msgbox_def = Define `ref_inv_msgbox (M : refined_model) =
!g g'. g < PAR.ng /\ g' < PAR.ng 
    /\ (refcore_abs (M.C 0)).H.init_hv 
    /\ ~(?s. s < PAR.ns /\ (PAR.cpol s = (g,g'))) ==> 
~(mbox ((mem_abs (M.m)) (ADRDS MBOX)) (g,g'))
`;

val ref_inv_igcsgi_def = Define `ref_inv_igcsgi (M : refined_model) =
!c c'. c < RPAR.nc /\ c' < RPAR.nc /\ PCG c <> PCG c' 
    /\ (refcore_abs (M.C 0)).H.init_hv ==>
((Q M.GIC (SGI (7w,c,c')) = PENDING) \/
 (Q M.GIC (SGI (7w,c,c')) = ACTIVE) ==>
	mbox ((mem_abs (M.m)) (ADRDS MBOX)) (PCG c,PCG c'))
/\ Q M.GIC (SGI (7w,c,c')) <> PENDACT
`;

val ref_inv_pt_def = Define `ref_inv_pt (M : refined_model) =
!g. g < PAR.ng /\ (?c. c < RPAR.nc /\ (PCG c = g) /\ (PCC c = 0) 
   /\ (refcore_abs (M.C c)).H.init_guest) ==>
(!a. a IN RPAR.A_PT g ==> ((mem_abs M.m) a = GI g a))
`;

val ref_inv_ppt_def = Define `ref_inv_ppt (M : refined_model) =
!g. g < PAR.ng /\ (?c. c < RPAR.nc /\ (PCG c = g) /\ (PCC c = 0) 
   /\ (refcore_abs (M.C c)).H.init_guest) ==>
(!a. a IN RPAR.A_PPT g ==> ((mem_abs M.m) a = GIP g a))
`;

val ref_inv_smmu_def = Define `ref_inv_smmu (M : refined_model) =
!g. g < PAR.ng /\ (?c. c < RPAR.nc /\ (PCG c = g) /\ (PCC c = 0) 
    /\ (refcore_abs (M.C c)).H.init_guest) ==>
(!p. p < RPAR.np /\ (PPG p = g) ==> 
        ((mmu_abs (M.SMMU p)).cfg = SMMU_GI g)
     /\ (mmu_abs (M.SMMU p)).active
     /\ (!q. q IN mmu_ptl_hist (M.SMMU p) ==>
             golden_rpl (RPAR.A_PPT (PPG p),GIP (PPG p)) q))
`;

val ref_inv_regel2_def = Define `ref_inv_regel2 (M : refined_model) =
!c. c < RPAR.nc /\ (refcore_abs (M.C c)).H.init_core ==> 
   (((refcore_abs (M.C c)).SPR(INR HCR_EL2) = 0x800F803Fw) \/
   ((refcore_abs (M.C c)).SPR(INR HCR_EL2) = 0x800F80BFw))
/\ ((refcore_abs (M.C c)).SPR(INR VBAR_EL2) = AHV VBAR)
`;

val ref_inv_mmu_def = Define `ref_inv_mmu (M : refined_model) =
!c. c < RPAR.nc /\ (refcore_abs (M.C c)).H.init_core ==> 
   ((mmu_abs (M.MMU c)).cfg = MMU_GI (PCG c))
/\ (!q. q IN mmu_ptl_hist (M.MMU c) ==> golden_rpl (RPAR.A_PT (PCG c), GI (PCG c)) q)
/\ (mode(refcore_abs (M.C c)) < 2 ==> 
	(mmu_abs (M.MMU c)).active
     /\ (!r. r IN mmu_req_sent (M.MMU c) ==> PAdr r <> FAULT_ADDRESS)) 
/\ (mode(refcore_abs (M.C c)) >= 2 ==> 
       ((refcore_abs (M.C c)).PC IN {AHV VBAR + 0x400w; AHV VBAR + 0x480w; AHV PC_INIT_CORE} <=> (mmu_abs (M.MMU c)).active)
    /\ ((mmu_abs (M.MMU c)).active ==> !r. (mmu_abs (M.MMU c)).state r = IDLE))
`;

val ref_inv_hventry_def = Define `ref_inv_hventry (M : refined_model) =
!c. c < RPAR.nc /\ (mode(refcore_abs (M.C c)) >= 2) /\ 
(refcore_abs (M.C c)).PC IN {AHV VBAR + 0x400w; AHV VBAR + 0x480w} ==> 
	(refcore_req_sent (M.C c) = EMPTY)
     /\ (mmu_req_rcvd (M.MMU c) = EMPTY)
     /\ (mmu_req_sent (M.MMU c) = EMPTY)
     /\ (mmu_rpl_rcvd (M.MMU c) = EMPTY)
     /\ (!r. (r, CoreSender c) NOTIN mem_req_rcvd (M.m))
     /\ (!r. (r, CoreSender c) NOTIN mem_req_sent (M.m))
     /\ (!r. (r, CoreSender c) NOTIN mem_rpl_rcvd (M.m))
     /\ (!r. (r, CoreSender c) NOTIN gic_req_rcvd (M.GIC))
     /\ (!r p. p < RPAR.np ==> (M.P p).IOreq_rcvd r <> SOME (CoreSender c))
`;

(* TODO?: need inv-msg? maybe just for hv steps, 
can probably be proven from good_core invariant *)

val ref_inv_mmureq_def = Define `ref_inv_mmureq (M : refined_model) =
!c. c < RPAR.nc ==>  
   (!r. r IN refcore_req_sent (M.C c) <=> r IN mmu_req_rcvd (M.MMU c)) 
/\ (!r. r IN mmu_req_sent (M.MMU c) <=> (r, CoreSender c) IN mem_req_rcvd (M.m)) 
`;

val ref_inv_smmureq_def = Define `ref_inv_smmureq (M : refined_model) =
!p. p < RPAR.np ==>  
   (!r. r IN per_req_sent (M.P p).st <=> r IN mmu_req_rcvd (M.SMMU p)) 
/\ (!r. r IN mmu_req_sent (M.SMMU p) <=> 
	(r, PeripheralSender p) IN mem_req_rcvd (M.m)) 
`;

val ref_inv_gicreq_def = Define `ref_inv_gicreq (M : refined_model) =
!r s. (r, s) IN gic_req_rcvd (M.GIC) <=> 
((r, s) IN mem_req_sent (M.m) /\ 
?ar. PAdr r IN RPAR.Amap ar /\ gicAR(ar))
`;

val ref_inv_perreq_def = Define `ref_inv_perreq (M : refined_model) =
!p. p < RPAR.np ==>
(!r s. ((M.P p).IOreq_rcvd r = SOME s) <=> 
((r, s) IN mem_req_sent (M.m) /\ (47><12)(Adr r) IN RPAR.Amap (PER p)))
`;

(* we do not allow peripheral to perform DMA requests to IO ports, 
this restriction could be lifted but one needs to adapt transition rules *)
val ref_inv_ioreq_def = Define `ref_inv_ioreq (M : refined_model) =
!r q s. ((r, s) IN mem_req_sent (M.m) \/ (q, s) IN mem_rpl_rcvd (M.m)) ==> 
   (!p. s <> PeripheralSender p)
`;

val ref_inv_mmurpl_def = Define `ref_inv_mmurpl (M : refined_model) =
(* received MMU replies are matching requests, 
no outstanding matching request in memory *)
   (!c q. c < RPAR.nc /\ q IN mmu_rpl_rcvd (M.MMU c) ==> 
        (?r l. ((mmu_abs(M.MMU c)).state r = FINAL (SOME l)) /\ match(l,q))
     /\ ~(?r. (r, CoreSender c) IN (mem_req_rcvd M.m) /\ match(r,q)) )
(* received SMMU replies are matching peripheral requests, 
no outstanding matching DMA request in memory*)
/\ (!p q. p < RPAR.np /\ q IN mmu_rpl_rcvd (M.SMMU p) ==> 
        (?r l. ((mmu_abs(M.SMMU p)).state r = FINAL (SOME l)) /\ match(l,q))
     /\ ~(?r. (r, PeripheralSender p) IN (mem_req_rcvd M.m) /\ match(r,q)))
`;

val ref_inv_memrpl_def = Define `ref_inv_memrpl (M : refined_model) =
!q s. (q,s) IN (mem_rpl_rcvd M.m) ==> 
   (?r. (r,s) IN (mem_req_rcvd M.m) /\ match(r,q))
/\ ~(?r. (r,s) IN (gic_req_rcvd M.GIC) /\ match(r,q))
/\ ~(?r p. p < RPAR.np /\ ((M.P p).IOreq_rcvd r = SOME s) /\ match(r,q))
`;

val no_pending_hyp_gicd_write_def = Define `
no_pending_hyp_gicd_write(M,g,r) =
!c req. 
   c < RPAR.nc 
/\ (PCG c = g) 
/\ (Mode (M.C c) = 2) 
/\ req IN refcore_req_sent(M.C c) 
==> 
~(Wreq(req) /\ PAdr req IN RPAR.Amap GICD /\ 
  (THE (decgicd ((11><0) (Adr req))) = r))
`; 

val ref_inv_hyp_gcpy_def = Define `ref_inv_hyp_gcpy (M : refined_model) =
!g r. g < PAR.ng /\ ~req_gicd(r,F) /\ (refcore_abs (M.C 0)).H.init_hv /\ 
      no_pending_hyp_gicd_write(M,g,r)
==>
( gcpys ((mem_abs(M.m)) (ADRDS (GCPY g))) (g, r) = 
  GICDfltr(g, r, (gic_abs(M.GIC)).gicd r) )
`;

val ref_inv_hyp_gwrite_def = Define `ref_inv_hyp_gwrite (M : refined_model) =
!g r v. g < PAR.ng /\ ~req_gicd(r,F) /\ (?B. ~fail_gicd(r,B)) /\
      ( ?c req. c < RPAR.nc /\ (PCG c = g) /\ req IN refcore_req_sent(M.C c) /\
		Wreq(req) /\ (THE (decgicd ((11><0) (Adr req))) = r) /\ 
		(Req_val req = v) /\ (Mode (M.C c) = 2) )
==>
( gcpys ((mem_abs(M.m)) (ADRDS (GCPY g))) (g, r) = 
  GICDfltr(g, r, GICDupd(r, (gic_abs(M.GIC)).gicd r, v)) )
`;

val ref_inv_hyp_greq_def = Define `ref_inv_hyp_greq (M : refined_model) =
!c r. c < RPAR.nc ==> 
      ( Mode (M.C c) >= 2 /\ r IN refcore_req_sent(M.C c) ==>
	PAdr r IN RPAR.Amap GICC UNION RPAR.Amap GICD UNION RPAR.Amap GICH 
        /\ ((PAdr r = Agicd) ==> request_gicd r)
        /\ (refcore_abs (M.C c)).H.init_core )
   /\ ( r IN mmu_req_sent(M.MMU c) /\ PAdr r IN RPAR.Amap GICD ==> 
	(Mode (M.C c) = 2) /\ (refcore_abs(M.C c)).PC IN
	  {AHV PC_GICD_ACCESS; AHV PC_SIGC_RCV_SGI})
   /\ ( r IN refcore_req_sent(M.C c) /\
	PAdr r IN RPAR.Amap GICC UNION RPAR.Amap GICH ==> 
	(Mode (M.C c) = 2) /\ (refcore_abs(M.C c)).PC IN 
	  {AHV PC_ASYNC_RCV_ACK; AHV PC_IRQ_RCV_EOI; AHV PC_IRQ_RCV_CHECK;
	   AHV PC_IRQ_RCV_INJECT; AHV PC_IRQ_RCV_DEACT; AHV PC_RIGC_RCV_EOI; 
	   AHV PC_RIGC_RCV_CHECK; AHV PC_RIGC_RCV_INJECT; AHV PC_RIGC_RCV_DEACT}
	) 
`;

val ref_inv_hyp_gmsg_def = Define `ref_inv_hyp_gmsg (M : refined_model) =
!c. c < RPAR.nc /\ (Mode (M.C c) >= 2) ==> 
case revAHV((refcore_abs(M.C c)).PC) of 
  | SOME PC_GICD_ACCESS => 
      ?r. PAdr r IN RPAR.Amap GICD /\ 
	  (refcore_req_sent(M.C c) = {GICDreqconv(PCG c, r)})
  | SOME PC_ASYNC_RCV_ACK => 
      (refcore_req_sent(M.C c) = {Read Agicc_aiar 4 dummy_info})
  | SOME PC_IRQ_RCV_EOI => 
      ?v. refcore_req_sent(M.C c) = {Write Agicc_aeoir 4 v dummy_info}
  | SOME PC_IRQ_RCV_CHECK => 
      (refcore_req_sent(M.C c) = {Read (Agich_lr (lirq ((mem_abs M.m) (ADRDS LIRQ)) c)) 4 dummy_info})      
  | SOME PC_IRQ_RCV_INJECT => 
      ?v.
      refcore_req_sent(M.C c) = {Write (Agich_lr (lirq ((mem_abs M.m) (ADRDS LIRQ)) c)) 4 v dummy_info}
  | SOME PC_IRQ_RCV_DEACT => 
      ?v. refcore_req_sent(M.C c) = {Write Agicc_dir 4 v dummy_info}
  | SOME PC_SIGC_RCV_SGI => 
      ?v:bool[32]. 
      (refcore_req_sent(M.C c) = {Write Agicd_sgir 4 (w2v v) dummy_info})
      /\ ((3><0)v = 7w:bool[4]) /\ (!t. t<8 /\ ((23><16)v = (1w:bool[8] << t)) 
		==> ?s. s < PAR.ns /\ (PAR.cpol s = (PCG c, PCG t))
		     /\ mbox ((mem_abs M.m) (ADRDS MBOX)) (PCG c, PCG t)) 
  | SOME PC_RIGC_RCV_EOI => 
      ?v. refcore_req_sent(M.C c) = {Write Agicc_aeoir 4 v dummy_info}
  | SOME PC_RIGC_RCV_CHECK => 
      refcore_req_sent(M.C c) = {Read (Aigc_lr(FST(THE(ligc((mem_abs M.m)(ADRDS LIGC)) c)))) 4 dummy_info}
  | SOME PC_RIGC_RCV_INJECT => 
      ?v.
      refcore_req_sent(M.C c) = {Write (Aigc_lr(FST(THE(ligc((mem_abs M.m)(ADRDS LIGC)) c)))) 4 v dummy_info}
  | SOME PC_RIGC_RCV_DEACT => 
      ?v. refcore_req_sent(M.C c) = {Write Agicc_dir 4 v dummy_info}
  | _ => refcore_req_sent(M.C c) = EMPTY
`;

val Arigc_def = Define `Arigc = {AHV PC_RIGC_SND_EOI; AHV PC_RIGC_RCV_EOI; AHV PC_RIGC_SND_CHECK; AHV PC_RIGC_RCV_CHECK; AHV PC_RIGC_SND_INJECT; AHV PC_RIGC_RCV_INJECT; AHV PC_RIGC_SND_DEACT; AHV PC_RIGC_RCV_DEACT; AHV PC_RIGC_RETURN}
`;

val ref_inv_hyp_ligc_def = Define `ref_inv_hyp_ligc (M : refined_model) =
!c. c < RPAR.nc /\ (Mode (M.C c) = 2) /\ (refcore_abs(M.C c)).PC IN Arigc
    ==>
    ( mbox ((mem_abs (M.m)) (ADRDS MBOX)) (PCG (SND(THE(ligc((mem_abs M.m)(ADRDS LIGC)) c))), PCG c) )
 /\ ( ~( ((refcore_abs(M.C c)).PC = AHV PC_RIGC_RCV_DEACT) 
         /\ (?q. pend_rpl(mmu_rpl_rcvd (M.MMU c), mem_rpl_rcvd M.m, c, q))
       \/ ((refcore_abs(M.C c)).PC = AHV PC_RIGC_RETURN)) 
        ==>
      (Q M.GIC (SGI (7w, SND(THE(ligc((mem_abs M.m)(ADRDS LIGC)) c)), c)) = ACTIVE) )
`;

val ref_inv_hyp_ackigc_def = Define `ref_inv_hyp_ackigc (M : refined_model) =
!c c'. c < RPAR.nc /\ c' < RPAR.nc /\ c <> c' /\ (PCG c <> PCG c') 
    /\ (Mode (M.C c) = 2) 
    /\ ( ((refcore_abs(M.C c)).PC = AHV PC_RIGC_SND_EOI) \/
	 ((refcore_abs(M.C c)).PC = AHV PC_ASYNC_RCV_ACK) /\
	 ?r q. pend_rpl(mmu_rpl_rcvd (M.MMU c), mem_rpl_rcvd M.m, c, q) /\ r IN refcore_req_sent(M.C c) /\ match(r,q) /\ ~Frpl(q) /\ ((Rpl_val q):bool[10] = 7w) /\ (w2n((12><10)((Rpl_val q):bool[32]):bool[3]) = c') ) ==>
    ( mbox ((mem_abs (M.m)) (ADRDS MBOX)) (PCG c', PCG c) )
 /\ ( Q M.GIC (SGI (7w, c', c)) = ACTIVE )
`;

val ref_inv_hyp_iso_mmu_lookup_def = Define `ref_inv_hyp_iso_mmu_lookup (M : refined_model) =
!c r l. c < RPAR.nc /\ ((mmu_abs(M.MMU c)).state r = TRANS (SOME l)) ==> 
	PTreq l /\ (PAdr l IN (RPAR.A_PT (PCG c)))
`;

val ref_inv_hyp_iso_mmu_pte_def = Define `ref_inv_hyp_iso_mmu_pte (M : refined_model) =
!c q. c < RPAR.nc /\ q IN mmu_ptl_hist(M.MMU c) ==>
   PTrpl(q)
/\ (Rpl_PAdr q IN (RPAR.A_PT (PCG c)))
/\ (Rpl_val q :bool[64] = mem_read (GI (PCG c)) (Rpl_Adr q) 8) 
`;

val ref_inv_hyp_iso_mmu_final_def = Define `ref_inv_hyp_iso_mmu_final (M : refined_model) =
!c r l. c < RPAR.nc /\ ((mmu_abs(M.MMU c)).state r = FINAL (SOME l)) /\
	(mmu_abs(M.MMU c)).active /\ l IN mmu_req_sent(M.MMU c) ==> 
   PAdr r IN PAR.A_G (PCG c) 
/\ (PAdr l = ATrans (PCG c) (PAdr r)) /\ xlated(r,l) 
/\ (ATrans (PCG c) (PAdr r) <> FAULT_ADDRESS)
/\ (PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PCG c)} ==> ~Wreq r)
`;

val ref_inv_hyp_iso_mmu_final_rpl_def = Define `
ref_inv_hyp_iso_mmu_final_rpl (M : refined_model) =
!c r l q. c < RPAR.nc /\ ((mmu_abs(M.MMU c)).state r = FINAL (SOME l)) 
       /\ (mmu_abs(M.MMU c)).active /\ q IN mmu_rpl_rcvd(M.MMU c) /\ match(l,q)
==> 
   PAdr r IN PAR.A_G (PCG c) 
/\ (PAdr l = ATrans (PCG c) (PAdr r)) /\ xlated(r,l) 
/\ (ATrans (PCG c) (PAdr r) <> FAULT_ADDRESS)
/\ (PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PCG c)} 
    ==> ~Wreq r)
`;


val ref_inv_hyp_iso_mmu_fault_def = Define `ref_inv_hyp_iso_mmu_fault (M : refined_model) =
!c r. c < RPAR.nc /\ ((mmu_abs(M.MMU c)).state r = FAULT) ==> 
(PAdr r NOTIN PAR.A_G (PCG c) \/ (PAdr r IN RPAR.Amap GICD)
\/ (PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PCG c)} /\ Wreq r))
`;

val ref_inv_hyp_iso_smmu_lookup_def = Define `ref_inv_hyp_iso_smmu_lookup (M : refined_model) =
!p r l. p < RPAR.np /\ ((mmu_abs(M.SMMU p)).state r = TRANS (SOME l)) ==> 
	PTreq l /\ (PAdr l IN (RPAR.A_PPT (PPG p)))
`;

val ref_inv_hyp_iso_smmu_pte_def = Define `ref_inv_hyp_iso_smmu_pte (M : refined_model) =
!p q. p < RPAR.np /\ q IN mmu_rpl_rcvd(M.SMMU p) /\ PTrpl(q) /\ 
      (Rpl_PAdr q IN (RPAR.A_PPT (PPG p))) ==> 
(Rpl_val q :bool[64] = mem_read (GIP (PPG p)) (Rpl_Adr q) 8)
`;

val ref_inv_hyp_iso_smmu_final_def = Define `
ref_inv_hyp_iso_smmu_final (M : refined_model) =
!p r l. p < RPAR.np /\ ((mmu_abs(M.SMMU p)).state r = FINAL (SOME l)) 
     /\ l IN mmu_req_sent(M.SMMU p) ==> 
   (PAdr r IN PAR.A_G (PPG p) )
/\ (PAdr l = ATrans (PPG p) (PAdr r)) /\ xlated(r,l)
/\ (ATrans (PPG p) (PAdr r) <> FAULT_ADDRESS)
/\ (PAdr r NOTIN RPAR.Amap GICC)
/\ (PAdr r NOTIN RPAR.Amap GICD)
/\ (!p'. p' < PAR.np_g (PPG p) ==> PAdr r NOTIN PAR.A_gp (PPG p) p')
/\ (PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PPG p)} ==> ~Wreq r)
`;

val ref_inv_hyp_iso_smmu_final_none_def = Define `
ref_inv_hyp_iso_smmu_final_none (M : refined_model) =
!p r. p < RPAR.np /\ ((mmu_abs(M.SMMU p)).state r = FINAL NONE) 
        ==> 
   (PAdr r IN PAR.A_G (PPG p) )
/\ (ATrans (PPG p) (PAdr r) <> FAULT_ADDRESS)
/\ (PAdr r NOTIN RPAR.Amap GICC)
/\ (PAdr r NOTIN RPAR.Amap GICD)
/\ (!p'. p' < PAR.np_g (PPG p) ==> PAdr r NOTIN PAR.A_gp (PPG p) p')
/\ (PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PPG p)} ==> ~Wreq r)
`;


val ref_inv_hyp_iso_smmu_final_rpl_def = Define `
ref_inv_hyp_iso_smmu_final_rpl (M : refined_model) =
!p r l q. p < RPAR.np /\ ((mmu_abs(M.SMMU p)).state r = FINAL (SOME l))
       /\ q IN mmu_rpl_rcvd(M.SMMU p) /\ match(l,q)
==>
   (PAdr r IN PAR.A_G (PPG p) )
/\ (PAdr l = ATrans (PPG p) (PAdr r)) /\ xlated(r,l)
/\ (ATrans (PPG p) (PAdr r) <> FAULT_ADDRESS)
/\ (PAdr r NOTIN RPAR.Amap GICC)
/\ (PAdr r NOTIN RPAR.Amap GICD)
/\ (!p'. p' < PAR.np_g (PPG p) ==> PAdr r NOTIN PAR.A_gp (PPG p) p')
/\ (PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PPG p)} ==> ~Wreq r)
`;



val ref_inv_hyp_iso_smmu_fault_def = Define `ref_inv_hyp_iso_smmu_fault (M : refined_model) =
!p r. p < RPAR.np /\ ((mmu_abs(M.SMMU p)).state r = FAULT) ==> 
(PAdr r NOTIN PAR.A_G (PPG p)) \/ 
(PAdr r IN RPAR.Amap GICC) \/
(PAdr r IN RPAR.Amap GICD) \/ 
(?p'. p' < PAR.np_g (PPG p) /\ PAdr r IN (PAR.A_gp (PPG p) p')) \/ 
(PAdr r IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PPG p)} /\ Wreq r)
`;

val ref_inv_hyp_iso_per_def = Define `ref_inv_hyp_iso_per (M : refined_model) =
!p r c. p < RPAR.np /\ c < RPAR.nc 
     /\ ((M.P p).IOreq_rcvd r = SOME (CoreSender c))
 ==>
	(PPG p = PCG c)
`;

(* LR at address Agich_lr IRQ contains 
- zero (not mapped to guest or never injected)
- vid=pid=IRQ and HW bit set (peripheral interrupts mapped to guest)
- pid=id_igc and HW bit not set and no maintenance irq required (igc interrupt, if mapped to guest)
- vid = PSQ pid and HW bit not set and no maintenance irq required (SGIs belonging to guest)
 *)
val ref_inv_hyp_lr_def = Define `ref_inv_hyp_lr (M : refined_model) =
!c q lr. c < RPAR.nc /\ (lr = (gic_abs M.GIC).gich c (gich_lr q))
==>
   (lr = 0w) 
\/ case q of 
     | PIR n => (    (?s c'. s < PAR.ns /\ (PAR.id_igc s = n) 
			  /\ (PAR.cpol s = (PCG c', PCG c)) 
			  /\ ~(lr ' 31) /\ ~(lr ' 19) )  
		  \/ PIR n IN PIRQ (PCG c) /\ (lr ' 31)
		     /\ (w2n((19><10)lr :bool[10]) = n) )
		/\ (lr ' 30) /\ ((29><28)lr :bool[2] <> 0b11w) 
		/\ (w2n((9><0)lr :bool[10]) = n)
     | SGI (id, c', c'') =>  (c = c'') /\ (PCG c' = PCG c) /\ id <=+ 7w 
			  /\ ~(lr ' 31) /\ (lr ' 30) /\ ~(lr ' 19)
			  /\ ((9><0)lr :bool[10] = w2w id) 
		          /\ ((12><10)lr :bool[3] = n2w (PCC c')) 
`;

val ref_inv_hyp_pc_def = Define `ref_inv_hyp_pc (M : refined_model) =
!c r. c < RPAR.nc /\ (Mode (M.C c) >= 2) /\ r IN refcore_req_sent (M.C c) ==> 
(refcore_abs(M.C c)).PC NOTIN {AHV PC_INIT_PRIM_ENTRY; 
			       AHV PC_INIT_SEC_ENTRY; 
			       AHV PC_INIT_PRIM; 
			       AHV PC_INIT_GUEST; 
			       AHV PC_INIT_CORE}
`;

(* no gicd writes while GLOCK is free, also no reads but no writes sufficient *)
val ref_inv_hyp_glock_def = Define `ref_inv_hyp_glock (M : refined_model) = 
!g. 
   g < PAR.ng 
/\ (refcore_abs(M.C 0)).H.init_hv 
/\ (Glock((mem_abs M.m)(ADRDS GLOCK)) = NONE)
==>
!r. no_pending_hyp_gicd_write(M,g,r)
`;

(* no rogue external inputs *)
val ref_inv_E_in_def = Define `ref_inv_E_in (M : refined_model) = 
!e. MEM e M.E_in ==> evper e < RPAR.np
`;

(******** wrapping up *********)

val _ = Datatype `REFINED_INVS = INV_IMG | INV_PSCI | INV_GICPOL | INV_GICC | INV_HIST | INV_PER_ACTIVE | INV_REGEL3 | INV_POW | INV_MSGBOX | INV_IGCSGI | INV_PT | INV_PPT | INV_SMMU | INV_REGEL2 | INV_MMU | INV_HVENTRY | INV_MMUREQ | INV_SMMUREQ | INV_GICREQ | INV_PERREQ | INV_IOREQ | INV_MMURPL | INV_MEMRPL | INV_HYP_GCPY | INV_HYP_GREQ | INV_HYP_GWRITE | INV_HYP_GMSG | INV_HYP_LIGC | INV_HYP_ACKIGC | INV_HYP_ISO_MMU_LOOKUP | INV_HYP_ISO_MMU_PTE | INV_HYP_ISO_MMU_FINAL | INV_HYP_ISO_MMU_FINAL_RPL | INV_HYP_ISO_MMU_FAULT | INV_HYP_ISO_SMMU_LOOKUP | INV_HYP_ISO_SMMU_PTE | INV_HYP_ISO_SMMU_FINAL | INV_HYP_ISO_SMMU_FINAL_NONE | INV_HYP_ISO_SMMU_FINAL_RPL | INV_HYP_ISO_SMMU_FAULT | INV_HYP_ISO_PER | INV_HYP_LR | INV_HYP_PC | INV_HYP_GLOCK | INV_E_IN | INV_GOOD_REFCORE | INV_GOOD_MMU | INV_GOOD_SMMU | INV_GOOD_MEM | INV_GOOD_PER`;

val ref_inv_def = Define `ref_inv (M : refined_model, inv:REFINED_INVS) =
case inv of
  | INV_IMG => ref_inv_img M
  | INV_PSCI => ref_inv_psci M
  | INV_GICPOL => ref_inv_gicpol M
  | INV_GICC => ref_inv_gicc M
  | INV_HIST => ref_inv_hist M
  | INV_REGEL3 => ref_inv_regel3 M
  | INV_POW => ref_inv_pow M
  | INV_MSGBOX => ref_inv_msgbox M
  | INV_IGCSGI => ref_inv_igcsgi M
  | INV_PT => ref_inv_pt M
  | INV_PPT => ref_inv_ppt M
  | INV_SMMU => ref_inv_smmu M
  | INV_PER_ACTIVE => ref_inv_per_active M
  | INV_REGEL2 => ref_inv_regel2 M
  | INV_MMU => ref_inv_mmu M
  | INV_HVENTRY => ref_inv_hventry M
  | INV_MMUREQ => ref_inv_mmureq M
  | INV_SMMUREQ => ref_inv_smmureq M
  | INV_GICREQ => ref_inv_gicreq M
  | INV_PERREQ => ref_inv_perreq M
  | INV_IOREQ => ref_inv_ioreq M
  | INV_MMURPL => ref_inv_mmurpl M
  | INV_MEMRPL => ref_inv_memrpl M
  | INV_HYP_GCPY => ref_inv_hyp_gcpy M
  | INV_HYP_GREQ => ref_inv_hyp_greq M
  | INV_HYP_GWRITE => ref_inv_hyp_gwrite M
  | INV_HYP_GMSG => ref_inv_hyp_gmsg M
  | INV_HYP_LIGC => ref_inv_hyp_ligc M
  | INV_HYP_ACKIGC => ref_inv_hyp_ackigc M
  | INV_HYP_ISO_MMU_LOOKUP => ref_inv_hyp_iso_mmu_lookup M
  | INV_HYP_ISO_MMU_PTE => ref_inv_hyp_iso_mmu_pte M
  | INV_HYP_ISO_MMU_FINAL => ref_inv_hyp_iso_mmu_final M
  | INV_HYP_ISO_MMU_FINAL_RPL => ref_inv_hyp_iso_mmu_final_rpl M
  | INV_HYP_ISO_MMU_FAULT => ref_inv_hyp_iso_mmu_fault M
  | INV_HYP_ISO_SMMU_LOOKUP => ref_inv_hyp_iso_smmu_lookup M
  | INV_HYP_ISO_SMMU_PTE => ref_inv_hyp_iso_smmu_pte M
  | INV_HYP_ISO_SMMU_FINAL => ref_inv_hyp_iso_smmu_final M
  | INV_HYP_ISO_SMMU_FINAL_NONE => ref_inv_hyp_iso_smmu_final_none M
  | INV_HYP_ISO_SMMU_FINAL_RPL => ref_inv_hyp_iso_smmu_final_rpl M
  | INV_HYP_ISO_SMMU_FAULT => ref_inv_hyp_iso_smmu_fault M
  | INV_HYP_ISO_PER => ref_inv_hyp_iso_per M
  | INV_HYP_LR => ref_inv_hyp_lr M
  | INV_HYP_PC => ref_inv_hyp_pc M
  | INV_HYP_GLOCK => ref_inv_hyp_glock M
  | INV_E_IN => ref_inv_E_in M
  | INV_GOOD_REFCORE => !c. c < RPAR.nc ==> inv_good_refcore (M.C c)
  | INV_GOOD_MMU => !c. c < RPAR.nc ==> inv_good_mmu (M.MMU c)
  | INV_GOOD_MEM => inv_good_mem M.m
  | INV_GOOD_SMMU => !p. p < RPAR.np ==> inv_good_mmu (M.SMMU p)
  | INV_GOOD_PER => !p. p < RPAR.np ==> inv_good_per_wrap (M.P p)
`;

val InvR_def = Define `InvR (M : refined_model) = !inv. ref_inv(M,inv)`;

(*************** some corollaries / lemmas ****************)

val InvR_EXPAND = save_thm("InvR_EXPAND", 
((SIMP_CONV (srw_ss()++DatatypeSimps.expand_type_quants_stateful_ss()) [InvR_def] )
THENC
(SIMP_CONV (srw_ss()) [ref_inv_def])) 
``InvR RM``
);

val refcore_req_sent_boot_lem = store_thm("refcore_req_sent_boot_lem", ``
!RM c. 
   InvR RM 
/\ c < RPAR.nc 
/\ (    (refcore_abs (RM.C c) = Creset c) 
     \/ warm (refcore_abs (RM.C c))
     \/ soft (refcore_abs (RM.C c)))
==>
(refcore_req_sent (RM.C c) = EMPTY)
``,
  REPEAT STRIP_TAC
  >| [(* Creset *)
      `Mode (RM.C c) >= 2` by (
          FULL_SIMP_TAC arith_ss [Mode_def, Creset_axiom]
      )
      ,
      (* warm *)
      IMP_RES_TAC warm_soft_axiom >>
      `Mode (RM.C c) >= 2` by (
          FULL_SIMP_TAC arith_ss [Mode_def, mode_def]
      )
      ,
      (* soft *)
      IMP_RES_TAC warm_soft_axiom >>
      `Mode (RM.C c) >= 2` by (
          FULL_SIMP_TAC arith_ss [Mode_def, mode_def]
      )
     ] >> (
      IMP_RES_TAC revAHV_boot_lem >>
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      IMP_RES_TAC ref_inv_hyp_gmsg_def >>
      REV_FULL_SIMP_TAC (srw_ss()) [] 
  )
);

val refcore_req_sent_not_hventry_lem = store_thm("refcore_req_sent_not_hventry_lem",``
!RM c. 
   InvR RM 
/\ c < RPAR.nc 
/\ (Mode (RM.C c) = 2) 
/\ refcore_req_sent (RM.C c) <> EMPTY
==> (refcore_abs (RM.C c)).PC NOTIN {AHV VBAR + 0x400w; AHV VBAR + 0x480w}
``,
  REPEAT GEN_TAC THEN 
	 MATCH_MP_TAC (prove (``
			     ((P0 /\ P1 /\ P2) ==> P3 ==> C) ==>
			     ((P0 /\ P1 /\ P2 /\ P3) ==> C)``,
			      METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  CONV_TAC CONTRAPOS_CONV THEN
  SIMP_TAC bool_ss [] THEN 
  `ref_inv(RM,INV_HVENTRY)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `Mode (RM.C c) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
  FULL_SIMP_TAC std_ss [Mode_def] THEN 
  `ref_inv_hventry RM` by (   FULL_SIMP_TAC (srw_ss()) [ref_inv_def] ) THEN 
  RW_TAC std_ss [] THEN
  IMP_RES_TAC (ref_inv_hventry_def |> SIMP_RULE arith_ss [mode_def])
);

val core_req_sent_lem = store_thm("core_req_sent_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ r IN refcore_req_sent (RM.C c)
==>
r IN mmu_req_rcvd (RM.MMU c)
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_MMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_mmureq_def
);

val mmu_req_rcvd_lem = store_thm("mmu_req_rcvd_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ r IN mmu_req_rcvd (RM.MMU c)
==>
r IN refcore_req_sent (RM.C c)
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_MMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_mmureq_def
);

val mmu_sent_rcvd_lem = store_thm("mmu_sent_rcvd_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ r IN mmu_req_sent (RM.MMU c)
==>
?r'. r' IN mmu_req_rcvd (RM.MMU c)
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_GOOD_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  RES_TAC THEN 
  IMP_RES_TAC inv_good_mmu_def THEN (
      METIS_TAC [MMUstate_distinct] )
);

val ref_mmu_sent_match_lem = store_thm("ref_mmu_sent_match_lem", ``
!RM c r q.
   InvR RM
/\ c < RPAR.nc
/\ r IN mmu_req_sent (RM.MMU c)
/\ match(r,q)
==>
    (?r'. match_final (RM.MMU c) (r',q)) 
\/ ((?r'. match_trans (RM.MMU c) (r',q)) /\ ~(?r'. match_final (RM.MMU c) (r',q)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  MATCH_MP_TAC mmu_sent_match_lem >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  METIS_TAC []  
);

val ref_smmu_sent_match_lem = store_thm("ref_smmu_sent_match_lem", ``
!RM p r q.
   InvR RM
/\ p < RPAR.np
/\ r IN mmu_req_sent (RM.SMMU p)
/\ match(r,q)
==>
    (?r'. match_final (RM.SMMU p) (r',q)) 
\/ ((?r'. match_trans (RM.SMMU p) (r',q)) 
     /\ ~(?r'. match_final (RM.SMMU p) (r',q)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  MATCH_MP_TAC mmu_sent_match_lem >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  METIS_TAC []  
);

val mem_req_rcvd_lem = store_thm("mem_req_rcvd_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (r, CoreSender c) IN mem_req_rcvd RM.m
==>
r IN mmu_req_sent (RM.MMU c)
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_MMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_mmureq_def
);

val mem_req_rcvd_lem2 = store_thm("mem_req_rcvd_lem2", ``
!RM p r.
   InvR RM
/\ p < RPAR.np
/\ (r, PeripheralSender p) IN mem_req_rcvd RM.m
==>
r IN mmu_req_sent (RM.SMMU p)
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_SMMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_smmureq_def
);

val mem_req_sent_lem = store_thm("mem_req_sent_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (r, CoreSender c) IN mem_req_sent RM.m
==>
(r, CoreSender c) IN mem_req_rcvd RM.m
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_GOOD_MEM)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC inv_good_mem_def 
);

val gic_req_rcvd_lem = store_thm("gic_req_rcvd_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (r, CoreSender c) IN gic_req_rcvd RM.GIC
==>
(r, CoreSender c) IN mem_req_sent RM.m
``,
  RW_TAC (srw_ss()) [] THEN 				 
  `ref_inv(RM,INV_GICREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_gicreq_def
);


val request_gicd_core_mmu_lem = store_thm("request_gicd_core_mmu_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (PAdr r IN RPAR.Amap GICD)    
/\ r IN mmu_req_sent (RM.MMU c) 
==>
   (Mode (RM.C c) = 2)
/\ ~(mmu_abs (RM.MMU c)).active
/\ r IN refcore_req_sent(RM.C c)
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  `ref_inv(RM,INV_HIST)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_MMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_HYP_GREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_HYP_PC)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_GOOD_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN  
  `inv_good_mmu (RM.MMU c)` by ( RES_TAC ) THEN 
  `Mode (RM.C c) = 2` by (
      FULL_SIMP_TAC (srw_ss()) [ref_inv_hyp_greq_def] THEN
      RES_TAC ) THEN 
  `?r'. r' IN mmu_req_rcvd (RM.MMU c)` by (
      IMP_RES_TAC mmu_sent_rcvd_lem THEN 
      HINT_EXISTS_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `refcore_req_sent(RM.C c) <> EMPTY` by (
      FULL_SIMP_TAC (srw_ss()) [ref_inv_mmureq_def] THEN 
      RES_TAC THEN 
      IMP_RES_TAC pred_setTheory.MEMBER_NOT_EMPTY ) THEN 
  IMP_RES_TAC refcore_req_sent_not_hventry_lem THEN
  `Mode (RM.C c) >= 2` by (FULL_SIMP_TAC arith_ss [] ) THEN 
  `?r''. r'' IN refcore_req_sent (RM.C c)` by (
      IMP_RES_TAC pred_setTheory.MEMBER_NOT_EMPTY THEN 
      HINT_EXISTS_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN
  IMP_RES_TAC ref_inv_hyp_pc_def THEN
  `(refcore_abs (RM.C c)).H.init_core` by (
      FULL_SIMP_TAC (srw_ss()) [Mode_def] THEN
      IMP_RES_TAC (ref_inv_hist_def |> SIMP_RULE (srw_ss()) [mode_def]) ) THEN
  `~(mmu_abs (RM.MMU c)).active` by (
      FULL_SIMP_TAC (srw_ss()) [Mode_def] THEN 
      IMP_RES_TAC (ref_inv_mmu_def |> SIMP_RULE (srw_ss()) [mode_def]) THEN 
      METIS_TAC [] ) THEN 
  `r IN mmu_req_rcvd (RM.MMU c)` by (
      `(mmu_abs (RM.MMU c)).state r <> IDLE` by (
          IMP_RES_TAC inv_good_mmu_def THEN
          REV_FULL_SIMP_TAC (srw_ss()) [] THEN 
	  FULL_SIMP_TAC (srw_ss()) [] ) THEN 
      IMP_RES_TAC inv_good_mmu_def ) THEN 
  IMP_RES_TAC ref_inv_mmureq_def THEN
  RW_TAC (srw_ss()) []				      
);


val request_gicd_lem = store_thm("request_gicd_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (PAdr r = Agicd)		       
/\ (    r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m 
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
request_gicd r 
``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1 /\ P2) ==> (P3a \/ P3b \/ P3c \/ P3d ) ==> C) ==>
    ((P0 /\ P1 /\ P2 /\ (P3a \/ P3b \/ P3c \/ P3d)) ==> C)``,
    METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  MATCH_MP_TAC (prove (``
    (P3a ==> C) /\
    (P3b ==> P3a) /\
    (P3c ==> P3b) /\
    (P3d ==> P3c) ==>
    ((P3a \/ P3b \/ P3c \/ P3d) ==> C)``,
    METIS_TAC[])) THEN REPEAT STRIP_TAC 
  THENL[(* case: mmu_req_sent *)
        `ref_inv(RM,INV_HYP_GREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	`PAdr r IN RPAR.Amap GICD` by ( 
	    FULL_SIMP_TAC (srw_ss()) [Agicd_lem] ) THEN
	IMP_RES_TAC request_gicd_core_mmu_lem THEN
	`Mode (RM.C c) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
	IMP_RES_TAC ref_inv_hyp_greq_def,
	(* case: mem_req_rcvd *)
	METIS_TAC[mem_req_rcvd_lem],
	(* case: mem_req_sent *)
	METIS_TAC[mem_req_sent_lem],
	(* case: mem_req_sent *)
	METIS_TAC[gic_req_rcvd_lem]
       ]
);

val mode_req_not_FA_lem = store_thm("mode_req_not_FA_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ Mode (RM.C c) < 2
/\ (    r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m 
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
PAdr r <> FAULT_ADDRESS
``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1 /\ P2) ==> (P3a \/ P3b \/ P3c \/ P3d ) ==> C) ==>
    ((P0 /\ P1 /\ P2 /\ (P3a \/ P3b \/ P3c \/ P3d)) ==> C)``,
    METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  MATCH_MP_TAC (prove (``
    (P3a ==> C) /\
    (P3b ==> P3a) /\
    (P3c ==> P3b) /\
    (P3d ==> P3c) ==>
    ((P3a \/ P3b \/ P3c \/ P3d) ==> C)``,
    METIS_TAC[])) THEN REPEAT STRIP_TAC 
  THENL[(* case: mmu_req_sent *)
	`(refcore_abs (RM.C c)).H.init_core` by (
	    `ref_inv(RM,INV_HIST)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	    FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	    IMP_RES_TAC ref_inv_hist_def THEN 
	    FULL_SIMP_TAC (srw_ss()) [Mode_def, mode_def] ) THEN 
        `ref_inv(RM,INV_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	IMP_RES_TAC ref_inv_mmu_def THEN 
	FULL_SIMP_TAC (srw_ss()) [Mode_def, mode_def] THEN
	RES_TAC,
	(* case: mem_req_rcvd *)
	METIS_TAC[mem_req_rcvd_lem],
	(* case: mem_req_sent *)
	METIS_TAC[mem_req_sent_lem],
	(* case: mem_req_sent *)
	METIS_TAC[gic_req_rcvd_lem]
       ]  
);

val mmu_inactive_lem = store_thm("mmu_inactive_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ r IN mmu_req_rcvd (RM.MMU c)
/\ Mode (RM.C c) >= 2
==>
~(mmu_abs (RM.MMU c)).active
``,
  RW_TAC (srw_ss()) [] THEN 
  `ref_inv(RM,INV_MMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_HYP_PC)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_HYP_GREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  `ref_inv(RM,INV_HVENTRY)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  `r IN refcore_req_sent (RM.C c)` by ( IMP_RES_TAC ref_inv_mmureq_def ) THEN 
  `(refcore_abs (RM.C c)).H.init_core` by (
      IMP_RES_TAC ref_inv_hyp_greq_def ) THEN 
  IMP_RES_TAC ref_inv_hyp_pc_def THEN 
  FULL_SIMP_TAC std_ss [Mode_def] THEN 
  `(refcore_abs (RM.C c)).PC NOTIN {AHV VBAR + 0x400w; AHV VBAR + 0x480w}` by ( 
      CCONTR_TAC THEN 
      IMP_RES_TAC ( ref_inv_hventry_def |> SIMP_RULE std_ss [mode_def] ) THEN 
      FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY] ) THEN 
  `(refcore_abs (RM.C c)).PC NOTIN {AHV VBAR + 0x400w; AHV VBAR + 0x480w; AHV PC_INIT_CORE}` by ( 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  IMP_RES_TAC ( ref_inv_mmu_def |> SIMP_RULE std_ss [mode_def] ) THEN 
  FULL_SIMP_TAC (srw_ss()) []
);

val mmu_active_mode_lem = store_thm("mmu_active_mode_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ r IN mmu_req_rcvd (RM.MMU c)
/\ (mmu_abs (RM.MMU c)).active
==>
Mode (RM.C c) < 2
``,
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  `Mode (RM.C c) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) >>
  IMP_RES_TAC mmu_inactive_lem
);

val init_core_lem = store_thm("init_core_lem", ``
!RM c r. 
   InvR RM
/\ c < RPAR.nc 
/\ (Mode (RM.C c) < 2) 
==> 
(refcore_abs (RM.C c)).H.init_core
``,
  RW_TAC (srw_ss()) [] THEN 
  `ref_inv(RM,INV_HIST)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_hist_def THEN 
  FULL_SIMP_TAC arith_ss [Mode_def, mode_def]
);

val init_hv_lem = store_thm("init_hv_lem", ``
!RM c r. 
   InvR RM
/\ c < RPAR.nc 
/\ (Mode (RM.C c) < 2) 
==> 
(refcore_abs (RM.C 0)).H.init_hv
``,
  RW_TAC (srw_ss()) [] THEN 
  `ref_inv(RM,INV_HIST)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_hist_def THEN 
  FULL_SIMP_TAC arith_ss [Mode_def, mode_def]
);

val mmu_active_lem = store_thm("mmu_active_lem", ``
!RM c.
   InvR RM
/\ c < RPAR.nc
/\ Mode (RM.C c) < 2
==>
(mmu_abs (RM.MMU c)).active
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC init_core_lem THEN 
  `ref_inv(RM,INV_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  IMP_RES_TAC ref_inv_mmu_def THEN 
  FULL_SIMP_TAC (srw_ss()) [Mode_def, mode_def]
);

val guest_req_mode_lem = store_thm("guest_req_mode_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ PAdr r IN RPAR.Amap (GUEST (PCG c))
/\ (    r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m 
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
Mode (RM.C c) < 2
``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1 /\ P2) ==> (P3a \/ P3b \/ P3c \/ P3d ) ==> C) ==>
    ((P0 /\ P1 /\ P2 /\ (P3a \/ P3b \/ P3c \/ P3d)) ==> C)``,
    METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  MATCH_MP_TAC (prove (``
    (P3a ==> C) /\
    (P3b ==> P3a) /\
    (P3c ==> P3b) /\
    (P3d ==> P3c) ==>
    ((P3a \/ P3b \/ P3c \/ P3d) ==> C)``,
    METIS_TAC[])) THEN REPEAT STRIP_TAC 
  THENL[(* case: mmu_req_sent *)
	CCONTR_TAC THEN 
	`Mode (RM.C c) >= 2` by DECIDE_TAC THEN 
	`~(mmu_abs (RM.MMU c)).active` by PROVE_TAC[mmu_inactive_lem, mmu_sent_rcvd_lem] THEN 
	`r IN mmu_req_rcvd (RM.MMU c)` by (
	    `ref_inv(RM,INV_GOOD_MMU)` by ( 
	        FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	    FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	    RES_TAC THEN 
	    IMP_RES_TAC inv_good_mmu_def THEN 
	    REV_FULL_SIMP_TAC (srw_ss()) [] THEN
	    `(mmu_abs (RM.MMU c)).state r <> IDLE` by (
	        FULL_SIMP_TAC (srw_ss()) [] ) THEN 
	    RES_TAC THEN
	    IMP_RES_TAC inv_good_mmu_def ) THEN 
        `ref_inv(RM,INV_MMUREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	`ref_inv(RM,INV_HYP_GREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	`r IN refcore_req_sent (RM.C c)` by ( 
	    IMP_RES_TAC ref_inv_mmureq_def ) THEN 
	`?A. singleAR A /\ A <> GICV /\ PAdr r IN RPAR.Amap A` by (
	    IMP_RES_TAC ref_inv_hyp_greq_def  THEN 
	    FULL_SIMP_TAC (srw_ss()) [singleAR_def] THEN (
	        HINT_EXISTS_TAC THEN
		FULL_SIMP_TAC (srw_ss()) []
	    )
	) THEN 
	`guestAR(GUEST (PCG c),PAR)` by ( 
	    `PCG c < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
	    FULL_SIMP_TAC (srw_ss()) [guestAR_def] ) THEN 
	`DISJOINT (RPAR.Amap A) (RPAR.Amap (GUEST (PCG c)))` by METIS_TAC[
           refined_goodP_axiom_Amap_disjoint, ARpred_REWRITES] THEN
	METIS_TAC [pred_setTheory.IN_DISJOINT],
	(* case: mem_req_rcvd *)
	METIS_TAC[mem_req_rcvd_lem],
	(* case: mem_req_sent *)
	METIS_TAC[mem_req_sent_lem],
	(* case: mem_req_sent *)
	METIS_TAC[gic_req_rcvd_lem]
       ]  
);


val guest_req_not_gicd_mode_lem = store_thm("guest_req_not_gicd_mode_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ PAdr r IN RPAR.Amap (GUEST (PCG c))
/\ (    r IN mmu_req_rcvd (RM.MMU c) 
     \/ r IN refcore_req_sent (RM.C c) ) 
==>
Mode (RM.C c) < 2
``,
  REPEAT GEN_TAC >>
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1 /\ P2) ==> (P3a \/ P3b) ==> C) ==>
    ((P0 /\ P1 /\ P2 /\ (P3a \/ P3b )) ==> C)``,
    METIS_TAC[])) >>
  STRIP_TAC >> 
  MATCH_MP_TAC (prove (``
    (P3b ==> C) /\
    (P3a ==> P3b) ==>
    ((P3a \/ P3b) ==> C)``,
    METIS_TAC[])) >> REPEAT STRIP_TAC 
  >| [(* case: refcore_req_sent *)
      CCONTR_TAC >>
      `Mode (RM.C c) >= 2` by DECIDE_TAC >>
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      `PAdr r IN RPAR.Amap GICC UNION RPAR.Amap GICD UNION RPAR.Amap GICH` by (
          IMP_RES_TAC ref_inv_hyp_greq_def
      ) >> 
      `PCG c < PAR.ng` by ( IMP_RES_TAC good_proj_in_range_impls ) >>
      FULL_SIMP_TAC (srw_ss()) [] >> (
          METIS_TAC [gic_not_guest_mem_lem]
      )
      ,
      (* case: mmu_req_rcvd *)
      METIS_TAC[mmu_req_rcvd_lem]
     ]  
);

val guest_req_not_FA_lem = store_thm("guest_req_not_FA_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ PAdr r IN RPAR.Amap (GUEST (PCG c))
/\ (    r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m 
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
PAdr r <> FAULT_ADDRESS
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN (
      `Mode (RM.C c) < 2` by ( IMP_RES_TAC guest_req_mode_lem ) THEN 
      IMP_RES_TAC mode_req_not_FA_lem
  )
);

val init_core_req_lem = store_thm("init_core_req_lem", ``
!RM c.
   InvR RM
/\ c < RPAR.nc
/\ (    (?r. r IN refcore_req_sent (RM.C c))
     \/ (?r. r IN mmu_req_rcvd (RM.MMU c))
     \/ (?r. r IN mmu_req_sent (RM.MMU c)) 
     \/ (?r. (r, CoreSender c) IN mem_req_rcvd RM.m)
     \/ (?r. (r, CoreSender c) IN mem_req_sent RM.m)
     \/ (?r. (r, CoreSender c) IN gic_req_rcvd RM.GIC) )
==>
(refcore_abs (RM.C c)).H.init_core
``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1) ==> (P3a \/ P3b \/ P3c \/ P3d \/ P3e \/ P3f) ==> C) ==>
    ((P0 /\ P1 /\ (P3a \/ P3b \/ P3c \/ P3d \/ P3e \/ P3f)) ==> C)``,
    METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  MATCH_MP_TAC (prove (``
    (P3a ==> C) /\
    (P3b ==> P3a) /\
    (P3c ==> P3b) /\
    (P3d ==> P3c) /\
    (P3e ==> P3d) /\
    (P3f ==> P3e) ==>
    ((P3a \/ P3b \/ P3c \/ P3d \/ P3e \/ P3f) ==> C)``,
    METIS_TAC[])) THEN REPEAT STRIP_TAC 
  THENL[(* case: refcore_sent_req *)
	Cases_on `(Mode (RM.C c) >= 2)`
        THENL[(* case: Mode >= 2 *)
	      `ref_inv(RM,INV_HYP_GREQ)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	      FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	      IMP_RES_TAC ref_inv_hyp_greq_def,
	      (* case: Mode < 2 *)
	      `Mode (RM.C c) < 2` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
	      `ref_inv(RM,INV_HIST)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
	      FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
	      IMP_RES_TAC ref_inv_hist_def THEN 
	      FULL_SIMP_TAC arith_ss [Mode_def, mode_def]
	     ],
	(* case: mmu_req_rcvd *)
	METIS_TAC [mmu_req_rcvd_lem],
	(* case: mmu_req_sent *)
	METIS_TAC [mmu_sent_rcvd_lem], 
 	(* case: mem_req_rcvd *)
        METIS_TAC [mem_req_rcvd_lem],
	(* case: mem_req_sent *)
        METIS_TAC [mem_req_sent_lem],
	(* case: gic_req_rcvd *)
        METIS_TAC [gic_req_rcvd_lem]
       ]
);

val init_core_req_forall_lem = store_thm("init_core_req_forall_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (    r IN refcore_req_sent (RM.C c)
     \/ r IN mmu_req_rcvd (RM.MMU c)
     \/ r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
(refcore_abs (RM.C c)).H.init_core
``,
  RW_TAC (srw_ss()) [] THEN (
      METIS_TAC [init_core_req_lem] )
);

val mmu_inactive_req_lem = store_thm("mmu_inactive_req_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ Mode (RM.C c) >= 2
/\ (    r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m 
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
~(mmu_abs (RM.MMU c)).active
``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1 /\ P2) ==> (P3a \/ P3b \/ P3c \/ P3d ) ==> C) ==>
    ((P0 /\ P1 /\ P2 /\ (P3a \/ P3b \/ P3c \/ P3d)) ==> C)``,
    METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  MATCH_MP_TAC (prove (``
    (P3a ==> C) /\
    (P3b ==> P3a) /\
    (P3c ==> P3b) /\
    (P3d ==> P3c) ==>
    ((P3a \/ P3b \/ P3c \/ P3d) ==> C)``,
    METIS_TAC[])) THEN REPEAT STRIP_TAC 
  THENL[(* case: mmu_req_sent *)
	IMP_RES_TAC mmu_sent_rcvd_lem THEN 
	METIS_TAC [mmu_inactive_lem],
 	(* case: mem_req_rcvd *)
        METIS_TAC [mem_req_rcvd_lem],
	(* case: mem_req_sent *)
        METIS_TAC [mem_req_sent_lem],
	(* case: gic_req_rcvd *)
        METIS_TAC [gic_req_rcvd_lem]
       ]
);

val mmu_inactive_forward_lem = store_thm("mmu_inactive_forward_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ ~(mmu_abs (RM.MMU c)).active
/\ r IN mmu_req_sent (RM.MMU c) 
==>
r IN mmu_req_rcvd (RM.MMU c) 
``,
  RW_TAC (srw_ss()) [] THEN 	 
  `ref_inv(RM,INV_GOOD_MMU)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_def] ) THEN
  FULL_SIMP_TAC (srw_ss()) [ref_inv_def] THEN
  RES_TAC THEN 
  IMP_RES_TAC inv_good_mmu_def THEN (
      METIS_TAC [MMUstate_distinct] )
);

val hyp_no_gicv_msg_lem = store_thm("hyp_no_gicv_msg_lem", ``
!RM c r. 
   InvR RM
/\ c < RPAR.nc 
/\ (Mode (RM.C c) >= 2) 
/\ r IN refcore_req_sent (RM.C c)
==> 
PAdr r NOTIN RPAR.Amap GICV
``,
  RW_TAC (srw_ss()) [InvR_EXPAND] THEN 
  IMP_RES_TAC ref_inv_hyp_gmsg_def THEN 
  Cases_on `revAHV (refcore_abs (RM.C c)).PC` 
  THEN1 (
      FULL_SIMP_TAC (srw_ss()) []
  ) THEN 
  `   (47><12) Agicc_aiar NOTIN RPAR.Amap GICV 
   /\ (47><12) Agicc_aeoir NOTIN RPAR.Amap GICV
   /\ (!q. (47><12) (Agich_lr q) NOTIN RPAR.Amap GICV)
   /\ (47><12) Agicc_dir NOTIN RPAR.Amap GICV` 
  by ( METIS_TAC [Agicch_axiom, gicAR_disj_EXPAND] ) THEN 
  `(47><12) Agicd_sgir NOTIN RPAR.Amap GICV` 
  by ( METIS_TAC [Agicd_axiom, gicAR_disj_EXPAND] ) THEN 
  Cases_on `x` THEN ( 
      FULL_SIMP_TAC (srw_ss()) [Aigc_lr_def] THEN 
      FULL_SIMP_TAC (srw_ss()) [pred_setTheory.IN_SING, GICDreqconv_PAdr_lem] THEN      TRY ( METIS_TAC [gicAR_disj_EXPAND] ) THEN 
      FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def] 
  )
);

val gicv_req_mode_lem = store_thm("gicv_req_mode_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ PAdr r IN RPAR.Amap GICV		       
/\ (    r IN refcore_req_sent (RM.C c)
     \/ r IN mmu_req_rcvd (RM.MMU c)
     \/	r IN mmu_req_sent (RM.MMU c) 
     \/ (r, CoreSender c) IN mem_req_rcvd RM.m 
     \/ (r, CoreSender c) IN mem_req_sent RM.m
     \/ (r, CoreSender c) IN gic_req_rcvd RM.GIC )
==>
(Mode (RM.C c) < 2)
``,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1 /\ P2) ==> (P3a \/ P3b \/ P3c \/ P3d \/ P3e \/ P3f) ==> C) ==>
    ((P0 /\ P1 /\ P2 /\ (P3a \/ P3b \/ P3c \/ P3d \/ P3e \/ P3f)) ==> C)``,
    METIS_TAC[])) THEN 
  STRIP_TAC THEN 
  MATCH_MP_TAC (prove (``
    (P3a /\ ~C ==> F) /\
    (P3b ==> P3a) /\
    ((P3c /\ ~C) ==> P3b) /\
    (P3d ==> P3c) /\
    (P3e ==> P3d) /\
    (P3f ==> P3e) ==>
    ((P3a \/ P3b \/ P3c \/ P3d \/ P3e \/ P3f) ==> C)``,
    METIS_TAC[])) THEN REPEAT STRIP_TAC 
  THENL [(* case: refcore_req_sent *)
	 `Mode (RM.C c) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
	 METIS_TAC [hyp_no_gicv_msg_lem],
	 (* case: mmu_req_rcvd *)
	 METIS_TAC [mmu_req_rcvd_lem],
	 (* case: mmu_req_sent *)
	 `Mode (RM.C c) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
	 `~(mmu_abs (RM.MMU c)).active` by ( 
	     IMP_RES_TAC mmu_inactive_req_lem
	 ) THEN 
	 METIS_TAC [mmu_inactive_forward_lem],
 	 (* case: mem_req_rcvd *)
         METIS_TAC [mem_req_rcvd_lem],
	 (* case: mem_req_sent *)
         METIS_TAC [mem_req_sent_lem],
	 (* case: gic_req_rcvd *)
         METIS_TAC [gic_req_rcvd_lem]
	]
);

val InvR_haspoc_exc_conf_lem = store_thm("InvR_haspoc_exc_conf_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ mode (refcore_abs (RM.C c)) < 2
==>
haspoc_exc_conf (RM.C c)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
  `(refcore_abs (RM.C c)).H.init_boot` by ( METIS_TAC [ref_inv_hist_def] ) >>
  `(refcore_abs (RM.C c)).H.init_core` by ( METIS_TAC [ref_inv_hist_def] ) >>
  RW_TAC std_ss [haspoc_exc_conf_def]
  >| [(* SCR_EL3 *)
      IMP_RES_TAC ref_inv_regel3_def
      ,
      (* HCR_EL2 *)
      METIS_TAC [ref_inv_regel2_def]
     ]
);

val InvR_VBAR_lem = store_thm("InvR_VBAR_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ mode (refcore_abs (RM.C c)) < 2
==>
((refcore_abs (RM.C c)).SPR (INR VBAR_EL2) = AHV VBAR)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
  `(refcore_abs (RM.C c)).H.init_core` by ( METIS_TAC [ref_inv_hist_def] ) >>
  METIS_TAC [ref_inv_regel2_def]
);

val InvR_VBAR_not_GICD_lem = store_thm("InvR_VBAR_not_GICD_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ Mode (RM.C c) < 2
==>
(refcore_abs (RM.C c)).SPR (INR VBAR_EL2) + 0x400w NOTIN {AHV PC_GICD_SAVE_CTX; 
							  AHV PC_GICD_ACCESS; 
							  AHV PC_GICD_FILTER}
``,
  NTAC 4 STRIP_TAC >>
  `mode (refcore_abs (RM.C c)) < 2` by ( 
      FULL_SIMP_TAC std_ss [Mode_def, mode_def]
  ) >>
  RW_TAC std_ss [InvR_VBAR_lem, pred_setTheory.IN_INSERT,
		 pred_setTheory.NOT_IN_EMPTY] >> (
      METIS_TAC [AHV_corollaries]
  )
);

val InvR_core_FLUSHED_req_sent_lem = 
store_thm("InvR_core_FLUSHED_req_sent_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ (ref_abs_int (RM.C c) = FLUSHED)
==>
(refcore_req_sent (RM.C c) = EMPTY)
``,
  RW_TAC std_ss [InvR_EXPAND] >>
  RES_TAC >>
  IMP_RES_TAC inv_good_refcore_def
);

val InvR_core_launched_lem = store_thm("InvR_core_launched_lem", ``
!RM c.
   InvR RM
/\ c < RPAR.nc
/\ Mode (RM.C c) < 2
==>
(refcore_abs (RM.C c)).H.launched
``,
  RW_TAC std_ss [InvR_EXPAND] >>
  `mode (refcore_abs (RM.C c)) < 2` by (
      FULL_SIMP_TAC std_ss [Mode_def, mode_def]
  ) >>
  IMP_RES_TAC ref_inv_hist_def
);

val InvR_core_curr_va_lem = store_thm("InvR_core_curr_va_lem", ``
!RM c r.
   InvR RM
/\ c < RPAR.nc
/\ r IN refcore_req_sent (RM.C c)
==>
   ~PTreq r
==>
((11 >< 0) (curr_va (refcore_int (RM.C c))) =
 (11 >< 0) (Adr r) :bool[12])
``,
  RW_TAC std_ss [InvR_EXPAND] >>
  RES_TAC >>
  METIS_TAC [inv_good_refcore_def]
);


(* MMU lemmas *)

val mmu_fault_state_lem = store_thm("mmu_fault_state_lem", ``
!RM c r.
   c < RPAR.nc
/\ InvR RM
/\ PAdr r IN PAR.A_G (PCG c)
/\ PAdr r NOTIN RPAR.Amap GICD
/\ (PAdr r IN receiverMem (PCG c) ==> ~Wreq r)
==>
(mmu_abs (RM.MMU c)).state r <> FAULT
``,
  REPEAT STRIP_TAC >>				    
  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_mmu_fault_def >>
  FULL_SIMP_TAC std_ss [receiverMem_def]
);

val mmu_fault_not_GICD_req_lem = store_thm("mmu_fault_not_GICD_req_lem", ``
!M c r. c < RPAR.nc 
     /\ InvR M
     /\ ((mmu_abs(M.MMU c)).state r = FAULT)
     /\ (PAdr r NOTIN RPAR.Amap GICD) ==> 
PAdr r NOTIN PAR.A_G (PCG c) \/ PAdr r IN receiverMem (PCG c) /\ Wreq r
``,
  RW_TAC std_ss [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_mmu_fault_def >> (
      RW_TAC std_ss [receiverMem_def]
  )
);

val smmu_fault_rpl_def = Define `smmu_fault_rpl p q = 
   p < RPAR.np /\ (
       Rpl_PAdr q NOTIN PAR.A_G (PPG p)
    \/ Rpl_PAdr q IN RPAR.Amap GICC
    \/ Rpl_PAdr q IN RPAR.Amap GICD
    \/ (?p_. p_ < PAR.np_g (PPG p) /\ Rpl_PAdr q IN PAR.A_gp (PPG p) p_) 
    \/ (?r. match(r,q) /\ PAdr r IN receiverMem (PPG p) /\ Wreq r)
   )
`;

val id_smmu_fault_rpl_def = Define `id_smmu_fault_rpl p g q = 
   p < PAR.np_g g /\ (
       Rpl_PAdr q NOTIN PAR.A_G g
    \/ Rpl_PAdr q IN RPAR.Amap GICC
    \/ Rpl_PAdr q IN RPAR.Amap GICD
    \/ (?p_. p_ < PAR.np_g g /\ Rpl_PAdr q IN PAR.A_gp g p_) 
    \/ (?r. match(r,q) /\ PAdr r IN receiverMem g /\ Wreq r)
   )
`;

val id_smmu_fault_req_def = Define `id_smmu_fault_req p g r =
   p < PAR.np_g g /\ (
       PAdr r NOTIN PAR.A_G g
    \/ PAdr r IN RPAR.Amap GICC
    \/ PAdr r IN RPAR.Amap GICD
    \/ (?p'. p' < PAR.np_g g /\ PAdr r IN PAR.A_gp g p')
    \/ (PAdr r IN receiverMem g /\ Wreq r)
   )
`;

val id_smmu_fault_match_lem = store_thm("id_smmu_fault_match_lem", ``
!p g r q. p < PAR.np_g g /\ match(r,q) ==>
    (id_smmu_fault_req p g r <=> id_smmu_fault_rpl p g q)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC match_PAdr_eq_lem >>
  RW_TAC std_ss [id_smmu_fault_req_def, id_smmu_fault_rpl_def] >>
  METIS_TAC [unique_match_thm]
);

val smmu_final_not_fault_lem = store_thm("smmu_final_not_fault_lem", ``
!RM p r l. 
    InvR RM
 /\ p < RPAR.np 
 /\ ((mmu_abs (RM.SMMU p)).state r = FINAL l)
      ==> 
~id_smmu_fault_req (PPP p) (PPG p) r
``,
  RW_TAC (srw_ss()) [InvR_EXPAND] >>
  Cases_on `l`
  >| [(* NONE *)
      IMP_RES_TAC ref_inv_hyp_iso_smmu_final_none_def
      ,
      (* SOME *)
      RES_TAC >>
      Cases_on `x IN mmu_req_sent (RM.SMMU p)` 
      >| [(* sent *)
	  IMP_RES_TAC ref_inv_hyp_iso_smmu_final_def
	  ,
	  (* sent but reply received *) 
	  `?q. q IN mmu_rpl_rcvd (RM.SMMU p) /\ match (x,q)` by (
              METIS_TAC [inv_good_mmu_def, pred_setTheory.IN_INSERT, 
			 pred_setTheory.NOT_IN_EMPTY]
	  ) >>
	  IMP_RES_TAC ref_inv_hyp_iso_smmu_final_rpl_def
	 ]
     ] >> (
      RW_TAC std_ss [id_smmu_fault_req_def] >>
      REWRITE_TAC [GSYM IMP_DISJ_THM] >>
      STRIP_TAC >>
      RW_TAC std_ss [receiverMem_def]
  )
);

val smmu_fault_state_lem = store_thm("smmu_fault_state_lem", ``
!RM p r.
   p < RPAR.np
/\ InvR RM
/\ PAdr r IN PAR.A_G (PPG p)
/\ PAdr r NOTIN RPAR.Amap GICC
/\ PAdr r NOTIN RPAR.Amap GICD
/\ (!p_. p_ < PAR.np_g (PPG p) ==> PAdr r NOTIN PAR.A_gp (PPG p) p_)
/\ (PAdr r IN receiverMem (PPG p) ==> ~Wreq r)
==>
(mmu_abs (RM.SMMU p)).state r <> FAULT
``,
  REPEAT STRIP_TAC >>				    
  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_smmu_fault_def >> (
      RES_TAC
  ) >>
  FULL_SIMP_TAC std_ss [receiverMem_def]
);



(* golden MMU configuration *)

val mmu_golden_conf_lem = store_thm("mmu_golden_conf_lem", ``
!RM c.
   c < RPAR.nc
/\ InvR RM
/\ (refcore_abs (RM.C c)).H.init_core
/\ Mode (RM.C c) < 2
==>
mmu_golden_conf (RM.MMU c, 
		 GI (PCG c), 
		 MMU_GI (PCG c), 
		 RPAR.A_PT (PCG c), 
		 golden_RO (PCG c), 
		 Trans (PCG c))
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, Mode_def] THEN 
  `PCG c < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  IMP_RES_TAC (ref_inv_mmu_def |> SIMP_RULE std_ss [mode_def]) THEN 
  IMP_RES_TAC golden_Trans_axiom THEN 
  FULL_SIMP_TAC (srw_ss()) [mmu_golden_conf_def]
);

(* golden SMMU configuration *)

val per_active_req_lem = store_thm("per_active_req_lem", ``
!RM p r.
   p < RPAR.np
/\ InvR RM
/\ (    r IN per_req_sent (RM.P p).st
     \/ r IN mmu_req_rcvd (RM.SMMU p) )
==>
per_active (RM.P p).st
``,
  REPEAT GEN_TAC >>
  MATCH_MP_TAC (prove (``
    ((P0 /\ P1) ==> (P3a \/ P3b) ==> C) ==>
    ((P0 /\ P1 /\ (P3a \/ P3b)) ==> C)``,
    METIS_TAC[])) >>
  STRIP_TAC >> 
  MATCH_MP_TAC (prove (``
    (P3a ==> C) /\
    (P3b ==> P3a) ==>
    ((P3a \/ P3b) ==> C)``,
    METIS_TAC[])) >> 
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  REPEAT STRIP_TAC 
  >| [(* case: req in per *)
      METIS_TAC [inv_good_per_wrap_def, inv_good_per_def, 
		 pred_setTheory.MEMBER_NOT_EMPTY]
      ,
      (* case: req in SMMU *)
      METIS_TAC [ref_inv_smmureq_def]
     ]
);

val per_active_init_guest_lem = store_thm("per_active_init_guest_lem", ``
!RM p. 
   p < RPAR.np
/\ InvR RM
/\ per_active (RM.P p).st
==>
?c. c < RPAR.nc /\ (PCG c = PPG p) /\ (PCC c = 0)
 /\ (refcore_abs (RM.C c)).H.init_guest
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `PPG p < PAR.ng` by (
      IMP_RES_TAC good_proj_axiom
  ) >>
  `?c. c < RPAR.nc /\ (PCG c = PPG p) /\ (PCC c = 0)` by (
      EXISTS_TAC ``PCGC_inv (PPG p, 0)`` >>
      `0 < PAR.nc_g (PPG p)` by (
          METIS_TAC [goodP_axiom]
      ) >>
      METIS_TAC [PCGC_PPGP_inv_def]
  ) >>
  `(refcore_abs (RM.C c)).H.launched` by (   
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      METIS_TAC [ref_inv_per_active_def]
  ) >>
  `(refcore_abs (RM.C c)).H.init_guest` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      METIS_TAC [ref_inv_hist_def, PCG_PCC_inj]
  ) >>
  METIS_TAC []
);

val smmu_per_active_lem = store_thm("smmu_per_active_lem", ``
!RM p. 
   p < RPAR.np
/\ InvR RM
/\ per_active (RM.P p).st
==>
   ((mmu_abs (RM.SMMU p)).cfg = SMMU_GI (PPG p)) 
/\ (mmu_abs (RM.SMMU p)).active
/\ (!q. q IN mmu_ptl_hist (RM.SMMU p) ==>
        golden_rpl (RPAR.A_PPT (PPG p),GIP (PPG p)) q)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `PPG p < PAR.ng` by (
      IMP_RES_TAC good_proj_axiom
  ) >>
  IMP_RES_TAC per_active_init_guest_lem >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  METIS_TAC [ref_inv_smmu_def]
);


val smmu_golden_conf_lem = store_thm("smmu_golden_conf_lem", ``
!RM p.
   p < RPAR.np
/\ InvR RM
/\ per_active (RM.P p).st
==>
mmu_golden_conf (RM.SMMU p, 
		 GIP (PPG p), 
		 SMMU_GI (PPG p), 
		 RPAR.A_PPT (PPG p), 
		 golden_RO (PPG p), 
		 Trgip (PPG p))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `PPG p < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) >>
  IMP_RES_TAC smmu_per_active_lem >>
  IMP_RES_TAC golden_Trgip_axiom >> 
  FULL_SIMP_TAC (srw_ss()) [mmu_golden_conf_def]
);

(* GIC lemmas *)


(**************** SIMULATION INVARIANT *******************)

val SimInvR_def = Define `SimInvR (M : refined_model) = 
   ((refcore_abs(M.C 0)).H.init_hv ==> (Glock((mem_abs M.m)(ADRDS GLOCK)) = NONE))
/\ (!c. c < RPAR.nc ==> 
       (    Mode (M.C c) < 2  
	 \/ (Mode (M.C c) = 2) 
	    /\ (refcore_abs(M.C c)).PC IN {AHV PC_GICD_SAVE_CTX; 
					   AHV PC_GICD_FILTER} ) 
         \/ (refcore_abs(M.C c) = Creset c) 
         \/ soft(refcore_abs(M.C c)) )
/\ (!c r. c < RPAR.nc ==> 
       ?l. (mmu_abs (M.MMU c)).state r IN {IDLE; FAULT; FINAL l} )
/\ (!c r. c < RPAR.nc /\ PAdr r IN RPAR.Amap GICD ==> 
       ((mmu_abs (M.MMU c)).state r = IDLE) )
/\ (!p r. p < RPAR.np ==> 
       ?l. (mmu_abs (M.SMMU p)).state r IN {IDLE; FAULT; FINAL l} )
`;

val SimInvR_no_TRANS_lem = store_thm("SimInvR_no_TRANS_lem", ``
!RM c r l.
   SimInvR RM
/\ c < RPAR.nc
==>
(mmu_abs (RM.MMU c)).state r <> TRANS l
``,
  RW_TAC (srw_ss()) [SimInvR_def] >>
  METIS_TAC [MMUstate_distinct]  
);

val SimInvR_smmu_no_TRANS_lem = store_thm("SimInvR_smmu_no_TRANS_lem", ``
!RM p r l.
   SimInvR RM
/\ p < RPAR.np
==>
(mmu_abs (RM.SMMU p)).state r <> TRANS l
``,
  RW_TAC (srw_ss()) [SimInvR_def] >>
  METIS_TAC [MMUstate_distinct]  
);

val smmu_fault_lem = store_thm("smmu_fault_lem", ``
!RM p r. 
    InvR RM
 /\ SimInvR RM
 /\ p < RPAR.np 
 /\ r IN mmu_req_rcvd (RM.SMMU p)
 /\ id_smmu_fault_req (PPP p) (PPG p) r
      ==> 
((mmu_abs (RM.SMMU p)).state r = FAULT)
``,
  REPEAT STRIP_TAC >>
  `?l. (mmu_abs (RM.SMMU p)).state r IN {IDLE; FAULT; FINAL l}` by (
      FULL_SIMP_TAC std_ss [SimInvR_def]
  ) >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT, MMUstate_distinct,
		        pred_setTheory.NOT_IN_EMPTY]
  >| [(* not IDLE *)
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      RES_TAC >>
      IMP_RES_TAC inv_good_mmu_def
      ,
      (* not FINAL *)
      IMP_RES_TAC smmu_final_not_fault_lem
     ]
);



(******************** INITIAL CONFIGURATION ***********************)

val ref_core_start_def = Define `ref_core_start (M : refined_model, c: num) =
   (refcore_abs(M.C c) = Creset c)
/\ (ref_abs_int(M.C c) = FLUSHED)
/\ (refcore_req_sent(M.C c) = EMPTY)
/\ ~(mmu_abs(M.MMU c)).active
/\ (mmu_req_rcvd(M.MMU c) = EMPTY)
/\ (mmu_req_sent(M.MMU c) = EMPTY)
/\ (mmu_rpl_rcvd(M.MMU c) = EMPTY)
/\ (mmu_ptl_hist(M.MMU c) = EMPTY)
/\ (!r. (mmu_abs (M.MMU c)).state r = IDLE)
/\ (!q. VI M.GIC c q = INACTIVE)
/\ (!r. (gic_abs M.GIC).gicc c r = GICCinit r)
/\ (!r. (gic_abs M.GIC).gich c r = GICHinit r)
/\ (!r. (gic_abs M.GIC).gicv c r = GICVinit r)
/\ M.PSCI.pow c
/\ (M.PSCI.events c = NIL)
`;

val ref_per_start_def = Define `ref_per_start (M : refined_model, p: num) =
   ((M.P p).st = per_reset)
/\ ~per_active (M.P p).st
/\ (!r. ~IS_SOME((M.P p).IOreq_rcvd r))
/\ ~(mmu_abs(M.SMMU p)).active
/\ (mmu_req_rcvd(M.SMMU p) = EMPTY)
/\ (mmu_req_sent(M.SMMU p) = EMPTY)
/\ (mmu_rpl_rcvd(M.SMMU p) = EMPTY)
/\ (mmu_ptl_hist(M.SMMU p) = EMPTY)
/\ (!r. (mmu_abs (M.SMMU p)).state r = IDLE)
`;

val ref_start_def = Define `ref_start (M : refined_model) =
   (!c. c < RPAR.nc ==> ref_core_start(M, c))
/\ (!p. p < RPAR.np ==> ref_per_start(M, p))
/\ (mem_req_rcvd(M.m) = EMPTY)
/\ (mem_req_sent(M.m) = EMPTY)
/\ (mem_rpl_rcvd(M.m) = EMPTY)
/\ ref_inv_img M
/\ (M.E_in = NIL) /\ (M.E_out = NIL)
/\ (!q. Q M.GIC q = INACTIVE)
/\ ((gic_abs (M.GIC)).gicd = (\r. GICDinit r))
/\ (gic_req_rcvd M.GIC = EMPTY)
`;

(* induction start *)

val InvR_definitions = [ref_inv_img_def, ref_inv_psci_def, ref_inv_gicpol_def, ref_inv_gicc_def, ref_inv_hist_def, ref_inv_regel3_def, ref_inv_pow_def, ref_inv_msgbox_def, ref_inv_igcsgi_def, ref_inv_pt_def, ref_inv_ppt_def, ref_inv_smmu_def, ref_inv_per_active_def, ref_inv_regel2_def, ref_inv_mmu_def, ref_inv_hventry_def, ref_inv_mmureq_def, ref_inv_smmureq_def, ref_inv_gicreq_def, ref_inv_perreq_def, ref_inv_ioreq_def, ref_inv_mmurpl_def, ref_inv_memrpl_def, ref_inv_hyp_gcpy_def, ref_inv_hyp_greq_def, ref_inv_hyp_gwrite_def, ref_inv_hyp_gmsg_def, ref_inv_hyp_ligc_def, ref_inv_hyp_ackigc_def, ref_inv_hyp_iso_mmu_lookup_def, ref_inv_hyp_iso_mmu_pte_def, ref_inv_hyp_iso_mmu_final_def, ref_inv_hyp_iso_mmu_final_rpl_def, ref_inv_hyp_iso_mmu_fault_def, ref_inv_hyp_iso_smmu_lookup_def, ref_inv_hyp_iso_smmu_pte_def, ref_inv_hyp_iso_smmu_final_def, ref_inv_hyp_iso_smmu_final_none_def, ref_inv_hyp_iso_smmu_final_rpl_def, ref_inv_hyp_iso_smmu_fault_def, ref_inv_hyp_iso_per_def, ref_inv_hyp_lr_def, ref_inv_hyp_pc_def, ref_inv_hyp_glock_def, ref_inv_E_in_def, inv_good_refcore_def, inv_good_mmu_def, inv_good_mem_def, inv_good_per_def, inv_good_per_wrap_def];

val Creset_mode_lem = store_thm("Creset_mode_lem", ``
~(mode (Creset c) < 2) /\ mode (Creset c) <> 2 /\ ~(mode (Creset c) < 3)
``,
  `mode (Creset c) = 3` by (
      FULL_SIMP_TAC (srw_ss()) [Creset_axiom, mode_def, Mode_def]
  ) >>
  FULL_SIMP_TAC arith_ss []
);

val Creset_Mode_lem = store_thm("Creset_Mode_lem", ``
(refcore_abs (M.C c) = Creset c) ==> 
~(Mode (M.C c) < 2) /\ Mode (M.C c) <> 2 /\ ~(Mode (M.C c) < 3)
``,
  STRIP_TAC >>
  `Mode (M.C c) = 3` by (
      FULL_SIMP_TAC (srw_ss()) [Creset_axiom, mode_def, Mode_def]
  ) >>
  FULL_SIMP_TAC arith_ss []
);

val AHV_not_reset_cor = store_thm("AHV_not_reset_cor", ``
AHV p <> (Creset c).SPR (INR RVBAR_EL3)
``,
  METIS_TAC [AHV_axiom]
);

val Creset_not_warm_soft_lem = store_thm("Creset_not_warm_soft_lem", ``
~warm(Creset c) /\ ~soft(Creset c)
``,
  METIS_TAC [Creset_axiom, warm_soft_axiom]
);

val Creset_revAHV_lem = store_thm("Creset_revAHV_lem", ``
revAHV (Creset c).PC = NONE
``,
  METIS_TAC [Creset_axiom, AHV_not_reset_cor, revAHV_axiom]
);

val positive_nc_cor = store_thm("positive_nc_core", ``
0 < RPAR.nc
``,
  RW_TAC std_ss [refined_goodP_axiom]
);

val InvRstart_lem = store_thm("InvRstart_lem", ``
!M. ref_start M ==> InvR M 
``,   
  RW_TAC (srw_ss()) [InvR_EXPAND] THEN (
      FULL_SIMP_TAC (srw_ss()) [ref_start_def, ref_core_start_def, 
				ref_per_start_def] THEN 
      RW_TAC (srw_ss()) (InvR_definitions@[per_reset_axiom, 
					   Creset_revAHV_lem,
					   no_pending_hyp_gicd_write_def]) THEN 
      RES_TAC THEN 
      TRY (METIS_TAC [Creset_mode_lem, Creset_Mode_lem, AHV_not_reset_cor, 
		      Creset_not_warm_soft_lem, Creset_axiom, 
		      Creset_revAHV_lem, positive_nc_cor, per_reset_axiom, 
		      gm_conf_init_ax, gicc_init_ax, gich_init_ax, 
		      MMUstate_distinct, pred_setTheory.NOT_IN_EMPTY,
		      listTheory.MEM, optionTheory.NOT_SOME_NONE] )
  )
);


val refstart_SimInvR_lem = store_thm("refstart_SimInvR_lem", ``
!M. ref_start M ==> SimInvR M
``,
  RW_TAC (srw_ss()) [ref_start_def, ref_core_start_def, Creset_axiom,
		     ref_per_start_def, SimInvR_def, positive_nc_cor]
);


(******************** COMPUTATIONS ***********************)

val refined_comp_def = Define `
   (refined_comp (RM, 0    , RM') = (RM = RM'))
/\ (refined_comp (RM, SUC n, RM') = 
    ?R RM''. refined_comp(RM,n,RM'') /\ refined_trans(RM'',R,RM'))
`;

val good_refined_comp_def = Define `good_refined_comp (RM, n , RM') = 
ref_start RM /\ refined_comp (RM, n, RM')
`;

(* THEOREM: invariant preserved *)

(* TODO: prove *)
val refined_trans_InvR_lem =
    store_thm("refined_trans_InvR_lem",
    ``!RM R RM'. refined_trans (RM, R, RM') ==>  InvR RM ==> InvR RM'``,
    cheat (*
    RW_TAC (srw_ss()) [] THEN 
    ASSUME_TAC (SPECL [``RM:refined_model``, ``SUC 0``, ``RM':refined_model``] InvR_lem) THEN 
    FULL_SIMP_TAC bool_ss [good_refined_comp_def, refined_comp_def] THEN 
    METIS_TAC [] *)
);


val InvR_lem = store_thm("InvR_lem", ``
!M n M'. good_refined_comp(M, n, M') ==> InvR M'
``,
  Induct_on `n` >> (
      RW_TAC (srw_ss()) [good_refined_comp_def]
  )
  THENL[(* case: n=0 *)
	FULL_SIMP_TAC (srw_ss()) [refined_comp_def] >>
	RW_TAC (srw_ss()) [InvRstart_lem]
        ,
	(* case: n->n+1 *)
	FULL_SIMP_TAC (srw_ss()) [good_refined_comp_def, refined_comp_def] >>
	RES_TAC >>
	IMP_RES_TAC refined_trans_InvR_lem
       ]
);

val refined_comp_InvR_lem = store_thm ("refined_comp_InvR_lem", ``
!M n M'. refined_comp(M, n, M') ==> InvR M ==> InvR M'
``,
  Induct_on `n` >> ( RW_TAC (srw_ss()) [refined_comp_def] ) >>
  (* case: n->n+1 *)
  METIS_TAC [refined_trans_InvR_lem]
);

(*************** finish ***********)

val _ = export_theory();
