(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 
open tacticsLib; 
open ConseqConv;

open math_lemmasTheory;
open axtypesTheory;
open haspoctypesTheory;
open parametersTheory;
open axfuncsTheory;
open hypervisorTheory;
open refinedTheory;
open refinedInvTheory;
open idealTheory;
open idealInvProofTheory;
open bisimTheory;

open tacticsLib;
open haspocLib;
open bisimProofLib;
open haspocSimps;

open annotationsLib; infix //; infix ///; infix -:;

val _ = new_theory "bisimProof";

(* more general lemmas that potentially could go somewhere else *)

val PIR_PQQ_lem = 
     store_thm ("PIR_PQQ_lem",
     ``   (PQQ g (PIR q) = PIR q)
       /\ (q <> 1023 ==> i <> PIR q ==> PQQ g i <> PIR q)
       /\ (q < 1020 ==> ((PQQ g i = PIR q) = (i = PIR q))) ``,
     Cases_on `i` THEN SIMP_TAC (srw_ss()) [PQQ_lem] THEN     
     PairCases_on `p` THEN RW_TAC (srw_ss()) [PQQ_lem] THEN
     DECIDE_TAC);

val PIRQ_disjoint_lem =
    store_thm ("PIRQ_disjoint_lem",
    `` (g < PAR.ng) ==> (g' < PAR.ng) ==> (g <> g')
        ==> (DISJOINT (PIRQ g) (PIRQ g'))``,
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [PIRQ_def, pirq_g_def,
      GSYM LEFT_FORALL_IMP_THM, refine_pirq_qp] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC refined_goodP_axiom_pirq_p_disjoint THEN
    ASM_SIMP_TAC (srw_ss()) []);

val PIRQ_IPIRQ_disjoint_lem = store_thm ("PIRQ_IPIRQ_disjoint_lem",`` 
(g < PAR.ng) ==> (DISJOINT (PIRQ g) (IPIRQ g))
``,
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) 
	     [PIRQ_def, pirq_g_def,IPIRQ_def, ipirq_g_def, 
	      GSYM LEFT_FORALL_IMP_THM, refine_pirq_qp] >>
    REPEAT STRIP_TAC >>
    RW_TAC (srw_ss()) [pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    REWRITE_TAC [GSYM IMP_DISJ_THM] >>
    STRIP_TAC >>
    IMP_RES_TAC good_proj_in_range_impls >>
    `?q. x = PIR q` by ( 
        METIS_TAC [refined_goodP_axiom]
    ) >>
    RW_TAC (srw_ss()) []
);


val PIRQ_disjoint_conseq_lem =
    store_thm ("PIRQ_disjoint_conseq_lem",
    ``   (per IN (PAR.pirq_gp g0 p0))
     ==> (PIRQ g0 INTER PIRQ g = EMPTY)
     ==> (p0 < PAR.np_g g0)
     ==> (per NOTIN (PIRQ g))``,
  RW_TAC (srw_ss()) [empty_intersect_lem, PIRQ_def, pirq_g_def] THEN
  METIS_TAC []);

val PIRQ_disjoint_lem2 =
    store_thm ("PIRQ_disjoint_lem2",
     ``(per IN (PAR.pirq_gp g0 p0)) ==> (g0 < PAR.ng) ==> (g < PAR.ng) ==> (g <> g0) ==> (p0 < PAR.np_g g0) 
          ==> (per NOTIN (PIRQ g))``,
    METIS_TAC [PIRQ_disjoint_lem, PIRQ_disjoint_conseq_lem, pred_setTheory.DISJOINT_DEF]);

val req_gicd_VOL_lem =
    store_thm("req_gicd_VOL_lem",
    ``req_gicd (r,F) = (?R. r = VOL R)``,
    Cases_on `r`
    THEN FULL_SIMP_TAC (srw_ss()) [req_gicd_def]);

val proj_bound_lem = store_thm("proj_bound_lem", ``
!c. c < RPAR.nc ==> PCG c < PAR.ng /\ PCC c < PAR.nc_g (PCG c)
``,
  METIS_TAC [good_proj_axiom]
);

val pproj_bound_lem = store_thm("pproj_bound_lem", ``
!p. p < RPAR.np ==> PPG p < PAR.ng /\ PPP p < PAR.np_g (PPG p)
``,
  METIS_TAC [good_proj_axiom]
);

val refined_vIRQ_def = Define `
    (refined_vIRQ g (PIR n) = PIR n IN xPIRQ g)
 /\ (refined_vIRQ g (SGI (id,s,r)) = id <=+ 7w /\ s < PAR.nc_g g 
			          /\ r < RPAR.nc /\ (PCG r = g))
`;

val PRQ_PIR_inv_lem = store_thm("PRQ_PIR_inv_lem", ``
!id g. g < PAR.ng /\ PIR id IN xPIRQ g ==> 
?q. (PIR id = PRQ g q) /\ refined_vIRQ g q
``,
  REPEAT STRIP_TAC >>
  EXISTS_TAC ``PIR id`` >>
  RW_TAC std_ss [PRQ_def, refined_vIRQ_def]
);

val PRQ_SGI_inv_lem = store_thm("PRQ_SGI_inv_lem", ``
!id s r g. g < PAR.ng /\ s < PAR.nc_g g /\ id <=+ 7w /\ r < PAR.nc_g g 
==>
?q. ((SGI (id,s,r)) = PRQ g q) /\ refined_vIRQ g q
``,
  REPEAT STRIP_TAC >>
  `?c. (r = PCC c) /\ c < RPAR.nc /\ (g = PCG c)` by ( 
      METIS_TAC [PCGC_PPGP_inv_def] 
  ) >>
  EXISTS_TAC ``SGI (id,s,c)`` >>
  RW_TAC std_ss [PRQ_def, refined_vIRQ_def]
);

val PRQ_inv_lem = store_thm("PRQ_inv_lem", ``
!q g. g < PAR.ng /\ xguest_irq g q ==> ?q'. (q = PRQ g q') /\ refined_vIRQ g q'
``,
  Cases >> ( REPEAT STRIP_TAC )
  >| [(* SGI *)
      `?id s r. p=(id,s,r)` by ( 
          METIS_TAC [pairTheory.pair_CASES] 
      ) >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC xguest_irq_def >>
      METIS_TAC [PRQ_SGI_inv_lem]
      ,
      (* PIR *)
      IMP_RES_TAC xguest_irq_def >>
      METIS_TAC [PRQ_PIR_inv_lem]
     ]
);

val HD_MAP_lem = store_thm("HD_MAP_lem", ``
!f l. l <> [] ==> (HD (MAP f l) = f (HD l))
``,
  STRIP_TAC >>
  Induct >> ( RW_TAC std_ss [listTheory.MAP] ) >>
  RW_TAC std_ss [listTheory.HD]
);

val MEM_HD_lem = store_thm("MEM_HD_lem", ``
!l. l <> [] ==> MEM (HD l) l
``,
  Induct >> ( RW_TAC std_ss [listTheory.MEM] ) >>
  RW_TAC std_ss [listTheory.HD]
);

val MAP_not_nil_lem = store_thm("MAP_not_nil_lem", ``
!f l. MAP f l <> [] ==> l <> []
``,
  STRIP_TAC >>
  Induct >> ( RW_TAC std_ss [listTheory.MAP] ) 
);


(***************** SOME LEMMAS ********************)


val xlated_mem_req_lem = store_thm("xlated_mem_req_lem", ``
!RM r c.
   InvR RM
/\ c < RPAR.nc
/\ PAdr r IN RPAR.Amap (GUEST (PCG c))
/\ (r, CoreSender c) IN mem_req_rcvd RM.m
==> 
?r'. (r = Trreq (PCG c) r')
  /\ IS_SOME (Trans (PCG c) (PAdr r'))
``,
  RW_TAC (srw_ss()) [] THEN
  `PCG c < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  `?px. IS_SOME (Trans (PCG c) px) /\ (PAdr r = THE (Trans (PCG c) px))` by (
      IMP_RES_TAC Trans_axiom THEN
      HINT_EXISTS_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN
  `?r'. (PAdr r = THE (Trans (PCG c) (PAdr r'))) 
     /\ xlated(r',r) /\ (PAdr r'=px)` by (
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `?r'. (PAdr r' = px) /\ xlated(r',r)` by (
          Cases_on `r` THEN
          FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def] 
	  THENL[(*case: Read *)
		EXISTS_TAC ``Read (((px:bool[36]) @@ ((11><0) (c':bool[48]) :bool[12])) :bool[48]) n m``,
		(*case: Write *)
		EXISTS_TAC ``Write (((px:bool[36]) @@ ((11><0) (c':bool[48]) :bool[12])) :bool[48]) n l m``,
		(*case: Walk *)
		EXISTS_TAC ``Walk (((px:bool[36]) @@ ((11><0) (c':bool[48]) :bool[12])) :bool[48]) m``
	       ] THEN 
	  FULL_SIMP_TAC (srw_ss()) [xlated_def, Adr_def] THEN
	  RW_TAC (srw_ss()) [PAdr_extract_lem, bx_extract_lem]
      ) THEN 
      HINT_EXISTS_TAC THEN
      FULL_SIMP_TAC (srw_ss()) []
  ) THEN 
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC Trreq_xlated_Trans_lem THEN 
  HINT_EXISTS_TAC THEN
  FULL_SIMP_TAC (srw_ss()) []
);

val xlated_mmu_req_lem = store_thm("xlated_mmu_req_lem", ``
!RM r r' c.
   InvR RM
/\ c < RPAR.nc
/\ r' IN mmu_req_rcvd (RM.MMU c)
/\ r IN mmu_req_sent (RM.MMU c)
/\ (mmu_abs (RM.MMU c)).active
/\ ((mmu_abs (RM.MMU c)).state r' = FINAL (SOME r))
==> 
   (r = Trreq (PCG c) r')
/\ IS_SOME (Trans (PCG c) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PCG c)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_def >>
  IMP_RES_TAC ATrans_lem >>
  RW_TAC (srw_ss()) [Trreq_xlated_ATrans_lem]
);

val xlated_smmu_req_lem = store_thm("xlated_smmu_req_lem", ``
!RM r r' p.
   InvR RM
/\ p < RPAR.np
/\ r' IN mmu_req_rcvd (RM.SMMU p)
/\ r IN mmu_req_sent (RM.SMMU p)
/\ ((mmu_abs (RM.SMMU p)).state r' = FINAL (SOME r))
==> 
   (r = Trreq (PPG p) r')
/\ IS_SOME (Trans (PPG p) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PPG p)
/\ PAdr r' NOTIN A_gicper
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_smmu_final_def >>
  IMP_RES_TAC ATrans_lem >>
  RW_TAC (srw_ss()) [Trreq_xlated_ATrans_lem] >>
  (* >| [(* case: ATrans in GUEST *) *)
  (*     RW_TAC (srw_ss()) [ATrans_def] >> *)
  (*     IMP_RES_TAC not_in_GICD_not_Agicd_lem >> *)
  (*     IMP_RES_TAC pproj_bound_lem >> *)
  (*     IMP_RES_TAC guest_adr_trans_lem *)
  (*     , *)
      (* case: ATrans not in A_gicper *)
      IMP_RES_TAC guest_mem_A_gicper_lem >>
      METIS_TAC [pproj_bound_lem]
     (* ] *)
);


val xlated_mmu_rpl_lem = store_thm("xlated_mmu_rpl_lem", ``
!RM r r' q c.
   InvR RM
/\ c < RPAR.nc
/\ r IN mmu_req_rcvd (RM.MMU c)
/\ q IN mmu_rpl_rcvd (RM.MMU c)
/\ match(r',q)
/\ (mmu_abs (RM.MMU c)).active
/\ ((mmu_abs (RM.MMU c)).state r = FINAL (SOME r'))
==> 
   (r' = Trreq (PCG c) r)
/\ IS_SOME (Trans (PCG c) (PAdr r))
/\ PAdr r IN PAR.A_G (PCG c)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_rpl_def >>
  IMP_RES_TAC ATrans_lem >>
  RW_TAC (srw_ss()) [Trreq_xlated_ATrans_lem]
);

val xlated_smmu_rpl_lem = store_thm("xlated_smmu_rpl_lem", ``
!RM r r' q p.
   InvR RM
/\ p < RPAR.np
/\ r IN mmu_req_rcvd (RM.SMMU p)
/\ q IN mmu_rpl_rcvd (RM.SMMU p)
/\ match(r',q)
/\ (mmu_abs (RM.SMMU p)).active
/\ ((mmu_abs (RM.SMMU p)).state r = FINAL (SOME r'))
==> 
   (r' = Trreq (PPG p) r)
/\ IS_SOME (Trans (PPG p) (PAdr r))
/\ PAdr r IN PAR.A_G (PPG p)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_hyp_iso_smmu_final_rpl_def >>
  IMP_RES_TAC ATrans_lem >>
  RW_TAC (srw_ss()) [Trreq_xlated_ATrans_lem]
);

val Trreq_per_lem = store_thm("Trreq_per_lem", ``
!r g p. 
   g < PAR.ng
/\ p < PAR.np_g g 
/\ PAdr r IN PAR.A_gp g p 
/\ IS_SOME (Trans g (PAdr r))
==>
   (Trreq g r = r)
``,
  REPEAT STRIP_TAC >>
  RW_TAC std_ss [Trreq_xlated_ATrans_lem]
  >| [(* ATrans *)
      IMP_RES_TAC trans_per_adr_lem >>
      RW_TAC std_ss [ATrans_def]
      ,
      (* xlated *)
      RW_TAC std_ss [xlated_id_lem]
     ]
);

val Trrpl_per_lem = store_thm("Trrpl_per_lem", ``
!r q g p. 
   g < PAR.ng
/\ p < PAR.np_g g 
/\ match(r,q)
/\ PAdr r IN PAR.A_gp g p 
/\ IS_SOME (Trans g (PAdr r))
==>
   (Trrpl g q = q)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC good_match_lem >>
  RW_TAC std_ss [Trrpl_xlated_ATrans_lem]
  >| [(* ATrans *)
      IMP_RES_TAC match_PAdr_eq_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC trans_per_adr_lem >>
      RW_TAC std_ss [ATrans_def]
      ,
      (* xlated *)
      RW_TAC std_ss [xlated_rpl_id_lem]
     ]
);



val mmu_sent_per_req_lem = store_thm("mmu_sent_per_req_lem", ``
!RM r c p. 
   InvR RM
/\ c < RPAR.nc
/\ p < RPAR.np
/\ r IN mmu_req_sent (RM.MMU c)
/\ PAdr r IN RPAR.Amap (PER p)
==>
?r'. 
   PAdr r' IN PAR.A_G (PCG c) 
/\ (r = Trreq (PCG c) r')
/\ (PCG c = PPG p)
/\ PAdr r' IN PAR.A_gp (PPG p) (PPP p)
/\ (mmu_abs (RM.MMU c)).active
``,
  REPEAT STRIP_TAC >>
  `inv_good_mmu (RM.MMU c)` by ( FULL_SIMP_TAC std_ss [InvR_EXPAND] ) >>
  IMP_RES_TAC inv_good_mmu_def
  >| [(* TRANS -> contradiction *)
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      IMP_RES_TAC ref_inv_hyp_iso_mmu_lookup_def >>
      IMP_RES_TAC proj_bound_lem >>
      `PAdr r IN RPAR.Amap HV` by ( 
          METIS_TAC [refined_goodP_axiom, pred_setTheory.SUBSET_DEF]
      ) >>
      `?g. g < PAR.ng /\ PAdr r IN RPAR.Amap (GUEST g)` by ( 
          METIS_TAC [refined_goodP_axiom, pred_setTheory.SUBSET_DEF]
      ) >>
      `singleAR HV` by ( REWRITE_TAC [singleAR_def, AddressRegion_distinct] ) >>
      `guestAR (GUEST g, PAR)` by ( RW_TAC std_ss [guestAR_def] ) >>
      `HV <> GICV` by ( REWRITE_TAC [AddressRegion_distinct] ) >>
      `DISJOINT (RPAR.Amap HV) (RPAR.Amap (GUEST g))` by (
          METIS_TAC [refined_goodP_axiom_Amap_disjoint]
      ) >>
      METIS_TAC [pred_setTheory.IN_DISJOINT]
      ,
      (* FINAL *)
      `r' IN mmu_req_rcvd (RM.MMU c)` by (
          METIS_TAC [MMUstate_distinct]
      ) >>
      Cases_on `(mmu_abs (RM.MMU c)).active`
      >| [(* active -> translation into guest memory *)
	  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_def >>
	  HINT_EXISTS_TAC >>
	  IMP_RES_TAC proj_bound_lem >>
	  ASM_REWRITE_TAC [] >>
	  MATCH_MP_TAC (
	      prove(``A /\ (A ==> B) ==> A /\ B``, PROVE_TAC [])
	  ) >>
	  REPEAT STRIP_TAC
	  >| [(* Trreq *)
	      RW_TAC std_ss [Trreq_xlated_ATrans_lem]
	      ,
	      (* same guest *)
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC ATrans_lem >>
	      `THE (Trans (PCG c) (PAdr r')) IN RPAR.Amap (PER p)` by (
	          METIS_TAC [Trreq_PAdr_Trans_lem]
	      ) >>
	      `PAdr r' IN PAR.A_gp (PPG p) (PPP p)` by (
	          IMP_RES_TAC per_trans_lem
	      ) >>
	      IMP_RES_TAC pproj_bound_lem >>
	      `PAdr r' IN PAR.A_G (PPG p)` by (
	          METIS_TAC [goodP_axiom, pred_setTheory.PSUBSET_DEF, 
			     pred_setTheory.SUBSET_DEF]
	      ) >>
	      METIS_TAC [goodP_axiom]
	      ,
	      (* A_gp *)
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC ATrans_lem >>
	      `THE (Trans (PCG c) (PAdr r')) IN RPAR.Amap (PER p)` by (
	          METIS_TAC [Trreq_PAdr_Trans_lem]
	      ) >>
	      METIS_TAC [per_trans_lem]
	     ]
	  ,
	  (* inactive -> contradiction *)
	  FULL_SIMP_TAC std_ss [] >>
	  RW_TAC std_ss [] >>
	  `Mode (RM.C c) >= 2` by (
	      CCONTR_TAC >>
	      `Mode (RM.C c) < 2` by ( FULL_SIMP_TAC arith_ss [] ) >>
	      IMP_RES_TAC mmu_active_lem	      
	  ) >>
	  IMP_RES_TAC mmu_req_rcvd_lem >>
	  `PAdr r IN RPAR.Amap GICC UNION 
		     RPAR.Amap GICD UNION 
		     RPAR.Amap GICH` by (
	      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	      IMP_RES_TAC ref_inv_hyp_greq_def
	  ) >>
	  `?AR. PAdr r IN RPAR.Amap AR /\ gicAR AR` by (
	      METIS_TAC [gicAR_def, pred_setTheory.IN_UNION]
	  ) >>
	  IMP_RES_TAC GICaddresses_lem >>
	  METIS_TAC [pred_setTheory.IN_INTER, pred_setTheory.NOT_IN_EMPTY]
	 ]
     ]
);

val gicv_Trreq_gicc_lem  = store_thm("gicv_Trreq_gicc_lem", ``
!g r r'. 
   g < PAR.ng
/\ PAdr r IN RPAR.Amap GICV 
/\ (r = Trreq g r')
/\ IS_SOME (Trans g (PAdr r'))
==> 
PAdr r' IN RPAR.Amap GICC
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC Trreq_PAdr_Trans_lem THEN 
  IMP_RES_TAC Trans_axiom THEN 
  FULL_SIMP_TAC (srw_ss()) []
);

val GICDreq_mem_lem = store_thm("GICDreq_mem_lem", ``
!RM IM c r.
   c < RPAR.nc 
/\ bisim_gicdreq_refined(RM,IM)
/\ bisim_gicdmsg_refined(RM,IM)
/\ InvR RM
/\ (r, CoreSender c) IN mem_req_rcvd RM.m
/\ PAdr r IN RPAR.Amap GICD
/\ ~(?q. (q, CoreSender c) IN mem_rpl_rcvd RM.m /\ match(r,q))
==>
     (Mode (RM.C c) = 2)  
/\ ( ((refcore_abs (RM.C c)).PC = AHV PC_GICD_ACCESS) /\ 
     (?r'. (r', CoreSender (PCC c)) IN idgic_req_rcvd (IM.G (PCG c)).GIC
        /\ (GICDreqconv(PCG c,r) = GICDreqconv(PCG c,r')) )
\/   ((refcore_abs (RM.C c)).PC = AHV PC_SIGC_RCV_SGI) /\
     ~(?r'. (r', CoreSender (PCC c)) IN idgic_req_rcvd (IM.G (PCG c)).GIC) )
``,
  RW_TAC (srw_ss()) [InvR_EXPAND] THEN (
      `r IN mmu_req_sent (RM.MMU c)` by ( IMP_RES_TAC ref_inv_mmureq_def ) THEN 
      IMP_RES_TAC ref_inv_hyp_greq_def 
  ) THEN
  `~(?q. pend_rpl (mmu_rpl_rcvd (RM.MMU c), mem_rpl_rcvd RM.m, c, q) /\ match (r,q))` by (    
      FULL_SIMP_TAC (srw_ss()) [pend_rpl_def] THEN
      RES_TAC THEN 
      IMP_RES_TAC inv_good_mmu_def THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      METIS_TAC [] 
  ) THEN 
  `InvR RM` by ( RW_TAC (srw_ss()) [InvR_EXPAND]) THEN 
  IMP_RES_TAC request_gicd_core_mmu_lem THEN
  IMP_RES_TAC bisim_gicdreq_refined_def THEN 
  IMP_RES_TAC bisim_gicdmsg_refined_def THEN 
  IMP_RES_TAC bisim_gicdreq_refined_core_def THEN  
  IMP_RES_TAC bisim_gicdmsg_refined_core_def THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  METIS_TAC []
);

val Mode_PCC_lem = store_thm("Mode_PCC_lem", ``
!RM c c'. 
   c < RPAR.nc
/\ c' < RPAR.nc 
/\ (PCG c = PCG c')
/\ Mode (RM.C c) < 2 /\ (Mode (RM.C c') = 2) 
==> 
PCC c <> PCC c'
``,
  RW_TAC arith_ss [] THEN 
  `Mode (RM.C c) <> Mode (RM.C c')` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
  `c <> c'` by ( 
      CCONTR_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] 
  ) THEN 
  METIS_TAC [PCG_PCC_inj]
);

val Mode_ineq_lem = store_thm("Mode_ineq_lem", ``
!RM c c'. 
   c < RPAR.nc
/\ c' < RPAR.nc 
/\ Mode (RM.C c) < 2 /\ (Mode (RM.C c') >= 2) 
==> 
c <> c'
``,
  RW_TAC arith_ss [] THEN 
  `Mode (RM.C c) <> Mode (RM.C c')` by ( FULL_SIMP_TAC arith_ss [] ) THEN 
  CCONTR_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) [] 
);

val Mode_arith_lem = store_thm("Mode_arith_lem", ``
!C. 
   Mode C < 2
==> 
Mode C <> 2 /\ Mode C <> 3 /\ ~(Mode C >= 2)
``,
  FULL_SIMP_TAC arith_ss [] 
);


val Mode_mode_lem = store_thm ("Mode_mode_lem", ``
!RM C. Mode C = mode (refcore_abs C)
``,
  RW_TAC std_ss [Mode_def, mode_def]
);

val mode_Mode_lem = store_thm ("mode_Mode_lem", ``
!RM C. mode (refcore_abs C) = Mode C
``,
  RW_TAC std_ss [Mode_def, mode_def]
);

val HVabs_mmu_send_lem = store_thm ("HVabs_mmu_send_lem", ``
!RM c c' m' MMU'.
   c <> c'
/\ (mem_abs RM.m = mem_abs m')
==> 
(HVabs (RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>,c') = HVabs (RM,c'))
``,
  RW_TAC std_ss [HVabs_def,combinTheory.APPLY_UPDATE_THM]
);

val HVabs_gic_send_lem = store_thm ("HVabs_gic_send_lem", ``
!RM c m' GIC'.
(mem_abs RM.m = mem_abs m')
==> 
(HVabs (RM with <|m := m'; GIC := GIC'|>,c) = HVabs (RM,c))
``,
  RW_TAC std_ss [HVabs_def,combinTheory.APPLY_UPDATE_THM]
);


val refined_comp_concat_lem = store_thm("refined_comp_concat_lem", ``
!RM n RM' n' RM''. refined_comp (RM,n,RM') /\ refined_comp (RM',n',RM'')
==>
?n''. refined_comp (RM,n'',RM'') /\ (n''=n+n')
``,
  Induct_on `n'`
  THEN1 ( RW_TAC (srw_ss()) [refined_comp_def] THEN 
          FULL_SIMP_TAC (srw_ss()) []
  ) THEN 
  RW_TAC (srw_ss()) [refined_comp_def] THEN 
  RES_TAC THEN 
  IMP_RES_TAC refined_comp_def THEN 
  `SUC n'' = n + SUC n'` by (
      RW_TAC arith_ss []
  ) THEN 
  FULL_SIMP_TAC (srw_ss()) []
);


val virq_guest_mode_lem = store_thm("virq_guest_mode_lem", ``
!RM IM c q.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ Mode (RM.C c) < 2
==>
((idgic_abs (IM.G (PCG c)).GIC).Q (PCC c) (PRQ (PCG c) q) = VI RM.GIC c q)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC good_proj_in_range_impls >>
  Cases_on `q`
  >| [(* case: SGI *)
      Cases_on `?id c'. (p = (id, c', c)) /\ id <=+ 7w
                     /\ (c' < PAR.nc_g (PCG c))`       
      >| [(* case: SGI belonging to c and guest *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  `bisim_sgiirq_core(RM.GIC,(IM.G (PCG c)).GIC,K F,c)` by (
	      IMP_RES_TAC bisim_sgiirq_def >>
	      METIS_TAC [nuvi_guest_mode_K_lem]
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [bisim_sgiirq_core_def, 
				    combinTheory.K_THM] >>
	  CASE_TAC
	  ,
	  (* case: rogue SGI *)
	  `VI RM.GIC c (SGI p) = INACTIVE` by (
	      CCONTR_TAC >>
	      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	      `?id s r. p = (id, s, r)` by ( 
	          METIS_TAC [pairTheory.pair_CASES] 
	      ) >>
	      RW_TAC std_ss [] >> (
	          IMP_RES_TAC ref_inv_gicpol_def >>
	          FULL_SIMP_TAC (srw_ss()) []
	      )
	  ) >>
	  `(idgic_abs (IM.G (PCG c)).GIC).Q (PCC c) (PRQ (PCG c) (SGI p)) = 
	   INACTIVE` 
	  by (
	      CCONTR_TAC >>
	      `?id s r. p = (id, s, r)` by ( 
	          METIS_TAC [pairTheory.pair_CASES] 
	      ) >>
	      IMP_RES_TAC ( InvI_EXPAND ``PCG c`` ) >>
	      FULL_SIMP_TAC std_ss [PRQ_def] >> (
	          Cases_on `(PCG r = PCG c) /\ r < RPAR.nc`
	          >| [FULL_SIMP_TAC (srw_ss()) [] >>
		      IMP_RES_TAC id_inv_gic_q_def >>
	              FULL_SIMP_TAC (srw_ss()) [] >>
		      TRY ( METIS_TAC [PCG_PCC_inj] ) >>
	              FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] 
		      ,
		      FULL_SIMP_TAC (srw_ss()) [] >> (
		          FULL_SIMP_TAC (srw_ss()) [] >>
			  IMP_RES_TAC id_inv_gic_q_def >>
	                  FULL_SIMP_TAC (srw_ss()) [] 
		      )
		     ]
	      )			  
	  ) >>
	  FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* case: PIR *)
      Cases_on `igc_irq_for_core (n,c)`
      >| [(* case: virtual IGC interrupt *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  `bisim_igcirq_core(RM.GIC,(IM.G (PCG c)).GIC,K F,c)` by (
	      IMP_RES_TAC bisim_igcirq_def >>
	      METIS_TAC [nuigc_guest_mode_K_lem]
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [bisim_igcirq_core_def, 
				    combinTheory.K_THM, PRQ_def] >>
	  CASE_TAC
	  ,
	  (* case: regular peripheral interrupt *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  `bisim_perirq_core(RM.GIC,(IM.G (PCG c)).GIC,K F,c)` by (
              IMP_RES_TAC bisim_perirq_def >>
              METIS_TAC [nuvi_guest_mode_K_lem]
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [bisim_perirq_core_def, 
				    combinTheory.K_THM, PRQ_def] >>
	  CASE_TAC
	 ]
     ]
);

val InvI_SGI_pending_lem = store_thm("InvI_SGI_pending_lem", ``
!IM g c id s r. 
    g < PAR.ng
 /\ c < PAR.nc_g g
 /\ InvI IM
 /\ ((idgic_abs (IM.G g).GIC).Q c (SGI (id,s,r)) = PENDING)
==>
    (r = c)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ( InvI_EXPAND ``g:num`` ) >>
  IMP_RES_TAC id_inv_gic_q_def >>
  PAT_X_ASSUM ``!q:irqID. 
      (idgic_abs (IM.G g).GIC).Q c q <> INACTIVE ==> z`` (
      fn thm => ASSUME_TAC ( SPEC ``SGI (id,s,r)`` thm )
  ) >>
  THROW_AWAY_TAC ``!q c. x`` >>
  REV_FULL_SIMP_TAC (srw_ss()) [IRQstate_distinct]
);

val InvR_SGI_pending_lem = store_thm("InvR_SGI_pending_lem", ``
!RM c id s r. 
    c < RPAR.nc
 /\ InvR RM
 /\ (VI RM.GIC c (SGI (id,s,r)) = PENDING)
==>
    (r = c)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
  IMP_RES_TAC ref_inv_gicpol_def >>
  PAT_X_ASSUM ``!q:irqID. VI RM.GIC c q <> INACTIVE ==> z`` (
      fn thm => ASSUME_TAC ( SPEC ``SGI (id,s,r)`` thm )
  ) >>
  THROW_AWAY_TAC ``!q c. x`` >>
  REV_FULL_SIMP_TAC (srw_ss()) [IRQstate_distinct]
);


(************** some hv lemmas ************)

val hv_gicd_entry_state_lem = store_thm("hv_gicd_entry_state_lem", ``
!RM c.
   c < RPAR.nc 
/\ Mode (RM.C c) < 2 
==>
~hv_gicd_entry_state (HVabs (RM,c))
``,
  RW_TAC arith_ss [HVabs_def, hv_gicd_entry_state_def, mode_def, Mode_def]
);

val hv_gicd_entry_state_eq_lem = store_thm("hv_gicd_entry_state_eq_lem", ``
!RM RM' c.
   c < RPAR.nc 
/\ (RM.C c = RM'.C c)
==>
(hv_gicd_entry_state (HVabs (RM,c)) <=> hv_gicd_entry_state (HVabs (RM',c)))
``,
  RW_TAC arith_ss [HVabs_def, hv_gicd_entry_state_def]
);


val hv_guard_mmu_fault_lem = store_thm("hv_guard_mmu_fault_lem", ``
!RM c.
   c < RPAR.nc 
/\ Mode (RM.C c) < 2 
==>
~hv_guard_mmu_fault (HVabs (RM,c),c)
``,
  RW_TAC arith_ss [HVabs_def, hv_guard_mmu_fault_def, mode_def, Mode_def]
);

val hv_guard_mmu_fault_eq_lem = store_thm("hv_guard_mmu_fault_eq_lem", ``
!RM RM' c.
   c < RPAR.nc 
/\ (RM.C c = RM'.C c)
==>
(hv_guard_mmu_fault (HVabs (RM,c),c) <=> hv_guard_mmu_fault (HVabs (RM',c),c))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hv_gicd_entry_state_eq_lem >>
  RW_TAC (srw_ss()) [HVabs_def, hv_guard_mmu_fault_def] 
);

val hv_mmu_fault_entry_eq_lem = store_thm("hv_mmu_fault_entry_eq_lem", ``
!RM RM' c.
   c < RPAR.nc 
/\ (RM.C c = RM'.C c)
==>
(hv_mmu_fault_entry_point (HVabs (RM,c)).C 
	<=> 
 hv_mmu_fault_entry_point (HVabs (RM',c)).C)
``,
  RW_TAC (srw_ss()) [HVabs_def, hv_mmu_fault_entry_point_def] 
);

val hv_guard_gicd_fail_lem = store_thm("hv_guard_gicd_fail_lem", ``
!RM RM' c.
   c < RPAR.nc 
/\ (RM.C c = RM'.C c)
==>
(hv_guard_gicd_fail (HVabs (RM,c)) <=> hv_guard_gicd_fail (HVabs (RM',c)))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hv_gicd_entry_state_eq_lem >>
  RW_TAC (srw_ss()) [HVabs_def, hv_guard_gicd_fail_def] 
);

val hv_guard_gicd_fail_mode_lem = store_thm("hv_guard_gicd_fail_mode_lem", ``
!RM c.
   c < RPAR.nc 
/\ Mode (RM.C c) < 2
==>
~hv_guard_gicd_fail (HVabs (RM,c))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hv_guard_gicd_fail_def >> (
      IMP_RES_TAC hv_gicd_entry_state_def >>
      FULL_SIMP_TAC (srw_ss()) [HVabs_def] >>
      FULL_SIMP_TAC arith_ss [Mode_mode_lem] 
  )
);

val bisim_mmu_req_rcvd_lem = store_thm("bisim_mmu_req_rcvd_lem", ``
!IM RM c r.
   c < RPAR.nc
/\ SIM (RM, IM)
/\ Mode (RM.C c) < 2
/\ (mmu_abs (RM.MMU c)).active
/\ r IN mmu_req_rcvd (RM.MMU c)
==>
r IN ((IM.G (PCG c)).cif (PCC c)).req_rcvd
``,
  RW_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_mmureq_guest_def >>
  IMP_RES_TAC hv_gicd_entry_state_lem >>
  IMP_RES_TAC hv_guard_mmu_fault_lem >>
  IMP_RES_TAC bisim_mmureq_guest_core_def
);

val bisim_cif_req_rcvd_lem = store_thm("bisim_cif_req_rcvd_lem", ``
!IM RM c r.
   c < RPAR.nc
/\ SIM (RM, IM)
/\ Mode (RM.C c) < 2
/\ (mmu_abs (RM.MMU c)).active
/\ r IN ((IM.G (PCG c)).cif (PCC c)).req_rcvd
==>
r IN mmu_req_rcvd (RM.MMU c)
``,
  RW_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_mmureq_guest_def >>
  IMP_RES_TAC hv_gicd_entry_state_lem >>
  IMP_RES_TAC hv_guard_mmu_fault_lem >>
  IMP_RES_TAC bisim_mmureq_guest_core_def
);

val bisim_pif_req_rcvd_lem = store_thm("bisim_pif_req_rcvd_lem", ``
!IM RM p r.
   p < RPAR.np
/\ SIM (RM, IM)
/\ r IN ((IM.G (PPG p)).pif (PPP p)).req_rcvd
==>
r IN mmu_req_rcvd (RM.SMMU p)
``,
  RW_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_smmureq_def >>
  FULL_SIMP_TAC std_ss []
);

(* golden lookup lemmas *)

val invisible_lookup_req_lem = store_thm("invisible_lookup_req_lem", ``
!RM IM c r r' MMU' m'. 
   c < RPAR.nc
/\ InvR RM
/\ SIM (RM,IM)
/\ Mode (RM.C c) < 2
/\ ((mmu_abs (RM.MMU c)).state r = TRANS NONE)
/\ ((mmu_abs MMU').state r = TRANS (SOME r'))
/\ mmu_step_snd_req (RM.MMU c,r',MMU')
/\ mem_step_rcv_req (RM.m, r', CoreSender c, m')
==>
SIM(RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>,IM)
``,
  RW_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC std_ss [SIM_EXPAND] THEN 
  REPEAT STRIP_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, mmu_step_def] THEN 
  IMP_RES_TAC mem_rcv_req_axiom THEN 
  IMP_RES_TAC mmu_send_axiom THEN 
  (* add some context *)
  `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
  IMP_RES_TAC init_core_lem THEN 
  IMP_RES_TAC mmu_active_lem THEN 
  IMP_RES_TAC mmu_golden_conf_lem THEN 
  IMP_RES_TAC mmu_golden_lookup_axiom THEN 
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  THEN (REPEAT IF_CASES_TAC THEN 
	STRONG_FS_TAC ([mode_Mode_lem]@bisim_core_definitions) THEN
	TRY ( METIS_TAC [PCG_PCC_inj, Mode_PCC_lem, Mode_ineq_lem, HVabs_mmu_send_lem, Trreq_eq_req_lem, PT_Trreq_lem] ) ) THEN (
  (* case: bisim_mmureq_guest *)
  STRONG_FS_TAC [hv_gicd_entry_state_lem, hv_guard_mmu_fault_lem] THEN 
  RW_TAC (srw_ss()) [] THENL
      [(* case 1: *)
       RES_TAC THEN ( 
           METIS_TAC [hv_gicd_entry_state_lem, hv_guard_mmu_fault_lem] 
       ),
       (* case 2: *)
       EQ_TAC THEN ( RW_TAC (srw_ss()) [] ) THEN 
       `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
       METIS_TAC [PT_Trreq_lem]
      ]
  ) 
);



val invisible_lookup_rpl_lem = store_thm("invisible_lookup_rpl_lem", ``
!RM IM c r r' q MMU' m'. 
   c < RPAR.nc
/\ InvR RM
/\ SIM (RM,IM)
/\ Mode (RM.C c) < 2
/\ ((mmu_abs (RM.MMU c)).state r = TRANS (SOME r'))
/\ match(r',q)
/\ mmu_step_rcv_rpl (RM.MMU c, q, MMU')
/\ mem_step_snd_rpl (RM.m, q, CoreSender c, m')
==>
SIM(RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>,IM)
``,
  RW_TAC (srw_ss()) [] THEN 
  (* add some context *)
  `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
  IMP_RES_TAC init_core_lem THEN 
  IMP_RES_TAC mmu_active_lem THEN 
  IMP_RES_TAC mmu_golden_conf_lem THEN
  `PTreq r' /\ PAdr r' IN RPAR.A_PT (PCG c)` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] THEN 
      IMP_RES_TAC ref_inv_hyp_iso_mmu_lookup_def THEN 
      RW_TAC (srw_ss()) []
  ) THEN 
  `Rpl_PAdr q IN RPAR.A_PT (PCG c)` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) THEN 
  `(q,CoreSender c) NOTIN mem_rpl_rcvd RM.m` by (
      CCONTR_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] THEN 
      IMP_RES_TAC mem_rpl_rcvd_lem THEN 
      METIS_TAC [PT_gic_per_disj_lem]
  ) THEN 
  IMP_RES_TAC mem_walk_lem THEN
  `inv_good_mmu (RM.MMU c)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] ) THEN 
  IMP_RES_TAC mmu_lookup_rpl_lem THEN 
  FULL_SIMP_TAC std_ss [SIM_EXPAND] THEN 
  REPEAT STRIP_TAC THEN 
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  THEN (REPEAT IF_CASES_TAC THEN 
	STRONG_FS_TAC ([mode_Mode_lem]@bisim_core_definitions) THEN
	TRY ( METIS_TAC [PCG_PCC_inj, Mode_PCC_lem, Mode_ineq_lem, HVabs_mmu_send_lem, Trreq_eq_req_lem, PT_Trreq_lem] ) ) THEN (
  (* case: bisim_mmureq_guest *)
  STRONG_FS_TAC [hv_gicd_entry_state_lem, hv_guard_mmu_fault_lem] THEN 
  RW_TAC (srw_ss()) [] THENL
      [(* case 1: *)
       RES_TAC THEN ( 
           METIS_TAC [hv_gicd_entry_state_lem, hv_guard_mmu_fault_lem] 
       ),
       (* case 2: *)
       EQ_TAC THEN ( RW_TAC (srw_ss()) [] ) THEN 
       `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
       METIS_TAC [PT_Trreq_lem]
      ]
  ) 
);


val golden_lookup_lem = store_thm("golden_lookup_lem", ``
!RM IM c r MMU'.
   c < RPAR.nc
/\ InvR RM
/\ SIM (RM,IM)
/\ Mode (RM.C c) < 2
/\ r IN mmu_req_rcvd (RM.MMU c)
/\ mmu_golden_lookup (RM.MMU c, r, GI (PCG c), MMU')
==> 
?m'.
   refined_comp (RM, 2, RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>)
/\ SIM (RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>, IM)
/\ InvR (RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>)
/\ r IN mmu_req_rcvd MMU'
/\ (mem_abs m' = mem_abs RM.m)
``,
  REPEAT GEN_TAC THEN 				  
  STRIP_TAC THEN 
  `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
  `(refcore_abs (RM.C c)).H.init_core` by ( IMP_RES_TAC init_core_req_lem ) THEN 
  IMP_RES_TAC mmu_golden_conf_lem THEN
  `(mmu_abs (RM.MMU c)).active` by ( 
      FULL_SIMP_TAC (srw_ss()) [mmu_golden_conf_def] 
  ) THEN 
  FULL_SIMP_TAC (srw_ss()) [mmu_golden_lookup_def] THEN 
  (* send step is computation *)
  `?m''. mem_step_rcv_req(RM.m,r',CoreSender c,m'')` by (
      FULL_SIMP_TAC (srw_ss()) [mem_rcv_req_enabled_axiom]
  ) THEN 
  `refined_trans(RM, MMU_SND_MREQ c, RM with <|m := m''; MMU := (c =+ MMU'') RM.MMU|>)` by (
      FULL_SIMP_TAC (srw_ss()) [refined_trans_def, ref_rule_mmu_snd_mreq_def, mmu_step_def, mem_step_def] THEN 
      METIS_TAC [] 
  ) THEN 
  `refined_comp (RM, SUC 0, RM with <|m := m''; MMU := (c =+ MMU'') RM.MMU|>)` by ( 
      METIS_TAC [refined_comp_def]
  ) THEN
  IMP_RES_TAC refined_trans_InvR_lem THEN
  (* reply can be sent by memory *)
  `?m'. mem_step_snd_rpl(m'',q,CoreSender c,m')` by (
      MATCH_MP_TAC mem_snd_rpl_enabled_axiom THEN 
      HINT_EXISTS_TAC THEN 
      RW_TAC (srw_ss()) [] 
      THEN1 ( 
          IMP_RES_TAC mem_rcv_req_axiom THEN 
	  FULL_SIMP_TAC (srw_ss()) []
      ) THEN 
      (* impossible cases *)
      TRY (
          IMP_RES_TAC mmu_golden_lookup_axiom THEN 
	  IMP_RES_TAC PT_gic_per_disj_lem THEN 
	  FULL_SIMP_TAC (srw_ss()) [] THEN 
	  TRY ( METIS_TAC [Rreq_not_PTreq_lem] ) THEN 
	  NO_TAC
      ) THEN 
      (* show that value is from golden image *)
      `(?c'. c' < RPAR.nc /\ (PCG c' = PCG c) /\ (PCC c' = 0) 
          /\ (refcore_abs (RM.C c')).H.init_guest)` by (
          FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, Mode_def] THEN 
	  IMP_RES_TAC (ref_inv_hist_def |> SIMP_RULE (srw_ss()) [mode_def] ) THEN
	  METIS_TAC []
      ) THEN
      IMP_RES_TAC mmu_golden_lookup_axiom THEN 
      RW_TAC (srw_ss()) [PTreq_Sz_lem] THEN
      IMP_RES_TAC match_Adr_eq_lem THEN 
      RW_TAC (srw_ss()) [mem_read_def] THEN 
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] THEN 
      IMP_RES_TAC ref_inv_pt_def THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      METIS_TAC [PAdr_def, Adr_def]
  ) THEN 
  (* second refined step is possible *)
  `refined_trans(RM with <| m := m''; MMU := (c =+ MMU'') RM.MMU|>, MMU_RCV_MRPL c, RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>)` by (
      IMP_RES_TAC mmu_send_axiom THEN 
      FULL_SIMP_TAC (srw_ss()++normalForms.cond_lift_SS) [refined_trans_def, ref_rule_mmu_rcv_mrpl_def, mmu_step_def, mem_step_def, pred_setTheory.UNION_DEF, combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ] THEN       
      METIS_TAC [] 
  ) THEN 
  (* solving first goal: computation exists *)
  IMP_RES_TAC refined_trans_InvR_lem THEN
  `refined_comp (RM, SUC (SUC 0), RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>)` by (
      IMP_RES_TAC refined_comp_def THEN 
      FULL_SIMP_TAC (srw_ss()) []
  ) THEN 
  FULL_SIMP_TAC arith_ss [] THEN 
  HINT_EXISTS_TAC THEN 
  RW_TAC (srw_ss()) [] THEN1 (
  (* show that simulation is preserved, need two lemmas *)
  (* step 1: *)
  Q.ABBREV_TAC `RM'' = RM with <|m := m''; MMU := (c =+ MMU'') RM.MMU|>` THEN 
  `SIM(RM'',IM)` by ( 
      Q.UNABBREV_TAC `RM''` THEN  
      IMP_RES_TAC (invisible_lookup_req_lem |> SPEC ``RM:refined_model``)
  ) THEN 
  (* step 2: *)
  `SIM (RM'' with <|m := m'; MMU := (c =+ MMU') RM''.MMU|>,IM)` by (
      `(Mode (RM''.C c) < 2) /\ (RM''.MMU c = MMU'') /\ (RM''.m = m'')` by (
          Q.UNABBREV_TAC `RM''` THEN 
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) THEN 
      RW_TAC (srw_ss()) [] THEN 
      IMP_RES_TAC (invisible_lookup_rpl_lem |> SPEC ``RM'':refined_model``) 
  ) THEN 
  Q.UNABBREV_TAC `RM''` THEN 
  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ]
  ) THEN1 ( 
  (* r IN mmu_req_rcvd MMU' *)
  `r IN mmu_req_rcvd MMU''` by (
      IMP_RES_TAC mmu_send_axiom THEN (
          FULL_SIMP_TAC (srw_ss()) []
      )
  ) THEN 
  IMP_RES_TAC mmu_memrpl_axiom THEN 
  FULL_SIMP_TAC (srw_ss()) []
  ) THEN 
  (* mem_abs unchanged *)
  Q.ABBREV_TAC `RM'' = RM with <|m := m''; MMU := (c =+ MMU'') RM.MMU|>` THEN 
  `PTreq r' /\ PAdr r' IN RPAR.A_PT (PCG c)` by (
      `ref_inv_hyp_iso_mmu_lookup RM''` by (
          FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
      ) THEN 
      Q.UNABBREV_TAC `RM''` THEN 					
      IMP_RES_TAC ref_inv_hyp_iso_mmu_lookup_def THEN 
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] THEN 
      METIS_TAC []
  ) THEN 
  `Rpl_PAdr q IN RPAR.A_PT (PCG c)` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) THEN 
  `(q,CoreSender c) NOTIN mem_rpl_rcvd m''` by (
      CCONTR_TAC THEN 
      Q.UNABBREV_TAC `RM''` THEN 					
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] THEN 
      IMP_RES_TAC mem_rpl_rcvd_lem THEN 
      METIS_TAC [PT_gic_per_disj_lem]
  ) THEN 
  `mem_abs m' = mem_abs m''` by (
      METIS_TAC [mem_walk_lem]
  ) THEN 
  `mem_abs m'' = mem_abs RM.m` by (
      METIS_TAC [mem_rcv_req_axiom]
  ) THEN 
  METIS_TAC []
);


val golden_comp_lem = store_thm("golden_comp_lem", ``
!RM IM c r n MMU'.
   c < RPAR.nc
/\ InvR RM
/\ SIM (RM,IM)
/\ Mode (RM.C c) < 2
/\ r IN mmu_req_rcvd (RM.MMU c)
/\ mmu_golden_comp (RM.MMU c, r, GI (PCG c), MMU', n)
==> 
?m'.
   refined_comp (RM, 2*n, RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>)
/\ SIM (RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>, IM)
/\ InvR (RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>)
/\ Mode ((RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>).C c) < 2
/\ r IN mmu_req_rcvd ((RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>).MMU c)
/\ (mem_abs m' = mem_abs RM.m)
``,
  Induct_on `n`
  THENL[(* Induction Start *)
	RW_TAC (srw_ss()) [mmu_golden_comp_def] THEN 
        FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_ID] THEN 
	EXISTS_TAC ``RM.m:memory`` THEN 
	`RM with <|m := RM.m; MMU := RM.MMU|> = RM` by (
	    RW_TAC (srw_ss()) [refined_model_component_equality]
	) THEN 
	RW_TAC (srw_ss()) [refined_comp_def] 
	, 
	(* Induction Step *)
	RW_TAC (srw_ss()) [mmu_golden_comp_def] THEN 
	PAT_X_ASSUM ``!rm im c r mmu'. x`` 
	    (fn thm => MP_TAC (SPECL [``RM:refined_model``,
				      ``IM:ideal_model``,
				      ``c:num``,
				      ``r:request``,
				      ``MMU'':mmu``] thm)) THEN 
	RW_TAC (srw_ss()) [] THEN 
	FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] THEN 
	Q.ABBREV_TAC `RM'' = RM with <|m := m'; MMU := (c =+ MMU'') RM.MMU|>` THEN
	`r IN mmu_req_rcvd (RM''.MMU c) /\ Mode (RM''.C c) < 2 /\ mmu_golden_lookup (RM''.MMU c,r,GI (PCG c),MMU')` by (
	    Q.UNABBREV_TAC `RM''` THEN 
	    FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	) THEN 
	`?m''. refined_comp (RM'',2, 
			     RM'' with <|m := m''; MMU := (c =+ MMU') RM''.MMU|>) 
	    /\ SIM (RM'' with <|m := m''; MMU := (c =+ MMU') RM''.MMU|>,IM)
	    /\ InvR (RM'' with <|m := m''; MMU := (c =+ MMU') RM''.MMU|>)
	    /\ r IN mmu_req_rcvd MMU'
            /\ (mem_abs m'' = mem_abs RM''.m)` by (
	    IMP_RES_TAC golden_lookup_lem THEN 
	    METIS_TAC []
	) THEN 
	IMP_RES_TAC refined_comp_concat_lem THEN 
	`2 * SUC n = 2 * n + 2` by (
	    RW_TAC arith_ss []
	) THEN 
	Q.UNABBREV_TAC `RM''` THEN     
	RW_TAC (srw_ss()) [] THEN 
	FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_EQ] THEN 
	HINT_EXISTS_TAC THEN 
	RW_TAC (srw_ss()) []
       ]
);

val mmu_Trreq_aligned_lem = store_thm("mmu_Trreq_aligned_lem", ``
!RM r g c.
   InvR RM
/\ g < PAR.ng
/\ c < RPAR.nc
/\ Trreq g r IN mmu_req_sent (RM.MMU c)
==>
req_aligned r
``,
  REPEAT STRIP_TAC >>
  `req_aligned (Trreq g r)` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      METIS_TAC [inv_good_mmu_def]
  ) >>
  IMP_RES_TAC Trreq_aligned_lem
);

val golden_mmu_Trreq_lem = store_thm("golden_mmu_Trreq_lem", ``
!RM c r r' MMU'.
   c < RPAR.nc
/\ InvR RM
/\ (mmu_abs (RM.MMU c)).active
/\ mmu_step_snd_req (RM.MMU c, r,MMU')
/\ ((mmu_abs (RM.MMU c)).state r' = FINAL NONE)
/\ ((mmu_abs MMU').state r' = FINAL (SOME r))
==>
(r = Trreq (PCG c) r') /\ IS_SOME (Trans (PCG c) (PAdr r'))
``,
  REPEAT GEN_TAC >> STRIP_TAC >>
  `r' IN mmu_req_rcvd (RM.MMU c)` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      RES_TAC >>
      METIS_TAC [inv_good_mmu_def, MMUstate_distinct]
  ) >>
  `(refcore_abs (RM.C c)).H.init_core` by (
      IMP_RES_TAC init_core_req_forall_lem
  ) >>
  `Mode (RM.C c) < 2` by (
      CCONTR_TAC >>
      `Mode (RM.C c) >= 2` by ( DECIDE_TAC ) >>
      METIS_TAC [mmu_inactive_lem]
  ) >>
  IMP_RES_TAC mmu_golden_conf_lem >>
  IMP_RES_TAC mmu_golden_final_axiom >>
  RW_TAC (srw_ss()) [Trreq_xlated_Trans_lem, PAdr_def, PAdr_extract_lem] >>
  IMP_RES_TAC mmu_send_axiom >> (
      REV_FULL_SIMP_TAC std_ss [] >>
      `r' = r''` by (
          CCONTR_TAC >>
          METIS_TAC []
      ) >>
      METIS_TAC [MMUstate_distinct]
  )
);

val final_mmu_rpl_no_fwd_lem = store_thm("final_mmu_rpl_no_fwd_lem", ``
!RM IM n r' q MMU' m' cif' im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.nc
/\ mmu_step_rcv_rpl (RM.MMU n,Trrpl (PCG n) q,MMU')
/\ mem_step_snd_rpl (RM.m,Trrpl (PCG n) q,CoreSender n,m')
/\ Trreq (PCG n) r' IN mmu_req_sent (RM.MMU n)
/\ match (Trreq (PCG n) r',Trrpl (PCG n) q)
/\ ((mmu_abs (RM.MMU n)).state r' = FINAL (SOME (Trreq (PCG n) r')))
(* /\ (refcore_abs (RM.C n)).active *)
/\ Mode (RM.C n) < 2
/\ IS_SOME (Trans (PCG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PCG n)
/\ PAdr r' NOTIN A_gicper
/\ r' IN ((IM.G (PCG n)).cif (PCC n)).req_sent
/\ mem_step_snd_rpl ((IM.G (PCG n)).m,q,CoreSender (PCC n), im')
/\ match (r',q)
/\ IS_SOME (Trans (PCG n) (Rpl_PAdr q))
/\ bif_step_rcv_rpl ((IM.G (PCG n)).cif (PCC n),q,cif')
==>
?n' IM'.
  ideal_model_comp (IM,n',IM') /\
  SIM (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,IM')
``,
  REPEAT STRIP_TAC >>
  (* start with computation part *)
  IMP_RES_TAC proj_bound_lem >>
  `?G'. id_rule_cif_rcv_rpl(IM.G (PCG n), PCC n, G') 
     /\ (G' = (IM.G (PCG n)) with 
              <|cif := (PCC n =+ cif') ((IM.G (PCG n)).cif); m := im'|>)` by (
      RW_TAC (srw_ss()) [id_rule_cif_rcv_rpl_def, 
			 mem_step_def, bif_step_def] >>
      METIS_TAC []
  ) >>
  `?IM'. ideal_guest_trans(IM.G (PCG n), PCG n, 
			   INTERNAL (IR_CIF_RCV_SRPL (PCC n)), G')
         /\ (IM' = IM with G := (PCG n =+ G') IM.G)` by (
      RW_TAC (srw_ss()) [ideal_guest_trans_def] 
  ) >>
  (* add some context *)
  RW_TAC (srw_ss()) [] >>
  `(q,CoreSender (PCC n)) NOTIN mem_rpl_rcvd ((IM.G (PCG n)).m)` by (
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `(Trrpl (PCG n) q,CoreSender n) NOTIN mem_rpl_rcvd (RM.m)` by (
      IMP_RES_TAC not_A_gicper_Trreq_lem >>
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `req_aligned r'` by ( IMP_RES_TAC mmu_Trreq_aligned_lem ) >>
  `inv_good_mem (IM.G (PCG n)).m` by (
     FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``PCG n``]
  ) >>
  `good_rpl q` by ( IMP_RES_TAC good_mem_rpl_axiom ) >>
  `inv_good_mmu (RM.MMU n)` by (
     FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
  ) >>
  `(mmu_abs (RM.MMU n)).active` by (
      IMP_RES_TAC mmu_active_lem
  ) >>
  `  (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd (RM.MMU n) UNION {Trrpl (PCG n) q})
  /\ (mmu_req_sent MMU' = mmu_req_sent (RM.MMU n) DIFF {Trreq (PCG n) r'})
  /\ (mmu_ptl_hist MMU' = mmu_ptl_hist (RM.MMU n))
  /\ ((mmu_abs MMU').state = (mmu_abs (RM.MMU n)).state)
  /\ (mmu_req_rcvd MMU' = mmu_req_rcvd (RM.MMU n))
  /\ (mmu_abs MMU').active
  /\ ((mmu_abs MMU').cfg = (mmu_abs (RM.MMU n)).cfg)` by (
      METIS_TAC [mmu_final_rpl_lem]
  ) >>
  `  (cif'.req_rcvd = ((IM.G (PCG n)).cif (PCC n)).req_rcvd)
  /\ (cif'.rpl_rcvd = ((IM.G (PCG n)).cif (PCC n)).rpl_rcvd UNION {q})
  /\ (cif'.req_sent = ((IM.G (PCG n)).cif (PCC n)).req_sent DIFF {r'})` by (
      METIS_TAC [bif_rcv_rpl_lem]
  ) >>
  IMP_RES_TAC guest_Trreq_lem >>
  IMP_RES_TAC HV_guest_disj_lem >> 
  `req_aligned (Trreq (PCG n) r')` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
	  METIS_TAC [inv_good_mmu_def]
  ) >>
  `!a. a IN RPAR.Amap HV ==> (mem_abs m' a = mem_abs RM.m a)` by (
      IMP_RES_TAC mem_unchanged_lem 
  ) >>
  IMP_RES_TAC hvds_unchanged_lem >>
  `!g r. g < PAR.ng ==> 
         (gcpys (mem_abs m' (ADRDS (GCPY g))) (g,r) =
          gcpys (mem_abs RM.m (ADRDS (GCPY g))) (g,r))` by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  `!c b. c < RPAR.nc ==> (
	     ctxs (mem_abs m' (ADRDS (CTX c))) (b,c) =
             ctxs (mem_abs RM.m (ADRDS (CTX c))) (b,c))`  by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  IMP_RES_TAC mem_snd_rpl_merged_lem >>
  (* case split depending on write to A_IGCout *)
  Cases_on `(PAdr r' NOTIN A_IGCin (PCG n) /\ (PAdr r' NOTIN A_IGCout (PCG n)) 
	    \/ ~Wreq r')`
  >| [(* show that syncInv still holds *)
      Q.ABBREV_TAC `IM' = IM with G := (PCG n =+ (IM.G (PCG n) with
          <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)) IM.G` >>
      `syncInv IM'` by ( 
	  METIS_TAC [cif_no_igc_write_sync_lem] 
      ) >> 
      Q.ABBREV_TAC `not_write_or_igc =
      	(PAdr r' NOTIN A_IGCin (PCG n) /\ (PAdr r' NOTIN A_IGCout (PCG n))
      	    \/ ~Wreq r')` >>
      (* show existence of ideal computation *) 
      `sync_shared_mem_upd_of_guest (IM', PCG n, IM')` by (
          RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
      ) >>
      `comp_rule_internal(IM,IM')`  by ( 
	  METIS_TAC [comp_rule_internal_def]
      ) >> 
      `ideal_model_trans (IM, C_INTERNAL, IM')` by (
          RW_TAC (srw_ss()) [ideal_model_trans_def]
      ) >>
      `ideal_model_comp (IM, SUC 0, IM')` by (
          METIS_TAC [ideal_model_comp_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [] >>
      (* show that memory is still in simulation *)
      `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
             (mem_abs((IM'.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
          REPEAT STRIP_TAC >>
	  Cases_on `g = PCG n` 
	  >| [`(IM'.G g).m = im'` by (
	          Q.UNABBREV_TAC `IM'` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      METIS_TAC [mem_access_bisim_lem]
	      ,
	      `(IM'.G g).m = (IM.G g).m` by (
	          Q.UNABBREV_TAC `IM'` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
              METIS_TAC [no_igc_write_mem_upd_others_lem]
	     ]
      ) >>
      `~hv_guard_mmu_fault 
           (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n),n)` by (
          MATCH_MP_TAC hv_guard_mmu_fault_lem >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `~hv_gicd_entry_state
           (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n))` by (
          MATCH_MP_TAC hv_gicd_entry_state_lem >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      (* show SIM *) 
      Q.UNABBREV_TAC `IM'` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      EXCEPT_FOR ``bisim_send_igc _`` (
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	  ) >>
      	  TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			   hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			   hv_mmu_fault_entry_eq_lem,
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			   nuvi_def, nuigc_def, nusgi_def] ) )
      )
      ) >>
      (* send_igc *)
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
      `nusgi((\c. RM.C c),
	     (\c. if n = c then 
		      mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
		  else 
		      mmu_rpl_rcvd (RM.MMU c)),
	     mem_rpl_rcvd RM.m) = 
       nusgi((\c. RM.C c),
	     (\c. mmu_rpl_rcvd (RM.MMU c)),
              mem_rpl_rcvd RM.m)` by (
          RW_TAC std_ss [FUN_EQ_THM] >>
          `?a b. x = (a,b)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
	  Cases_on `a = n` >> (
	      RW_TAC std_ss [nusgi_def, Mode_arith_lem]
	  )
      ) >>
      METIS_TAC []
      ,
      (* case: write to IGC memory *)
      FULL_SIMP_TAC (srw_ss()) []
      >| [(* case: write to A_IGCin -> not possible *)
	  FULL_SIMP_TAC (srw_ss()) [A_IGCin_def, InvR_EXPAND] >>
	  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  METIS_TAC []
	  ,
	  (* case: write to A_IGCout -> prove additional sync *)
	  Q.ABBREV_TAC `IM' = IM with G := (PCG n =+ (IM.G (PCG n) with
              <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)) IM.G` >>
	  `?s g2 a2. 
	      s < PAR.ns
	   /\ g2 < PAR.ng
	   /\ (PAR.cpol s = (PCG n,g2))
	   /\ (PAR.igca s = (PAdr r',a2))
	   /\ do_sync_shared_mem_upd_of_guest(IM',PCG n,
		IM' with <|G := (g2 =+ 
	(IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G (PCG n)).m (PAdr r')) 
					 (IM'.G g2).m|>) ) IM'.G|>)` by (
	      METIS_TAC [cif_igc_write_sync_lem] 
	  ) >>
	  Q.ABBREV_TAC `IM'' = IM' with <|G := (g2 =+ 
	(IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G (PCG n)).m (PAdr r')) 
					 (IM'.G g2).m|>) ) IM'.G|>` >>
	  (* show existence of computation *)
	  `PCG n <> g2` by (
	      CCONTR_TAC >>
	      FULL_SIMP_TAC std_ss [] >>
	      RW_TAC std_ss [] >> 
	      METIS_TAC [goodP_axiom]
	  ) >>
	  `sync_shared_mem_upd_of_guest (IM',PCG n,IM'')` by (
	      Cases_on `syncInv IM'`
	      >| [(* case: memory update with same value *) 
		  `mem_abs (IM'.G (PCG n)).m (PAdr r') = 
	           mem_abs (IM'.G g2).m a2` by (
		      METIS_TAC [syncInv_def]
		  ) >>
		  `IM'' = IM'` by (
		      Q.UNABBREV_TAC `IM''` >>
		      ASM_REWRITE_TAC [] >>
		      RW_TAC (srw_ss()) [memory_id_upd_axiom, 
					 combinTheory.APPLY_UPDATE_ID,
					 GSYM guest_trivial_upd_m_lem,		  
					 SYM ideal_model_just_guests_lem]
		  ) >>
		  RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
		  ,
		  (* case: unartificial update *)
		  RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
		 ]
	  ) >>
	  `comp_rule_internal(IM,IM'')`  by ( 
	      METIS_TAC [comp_rule_internal_def]
	  ) >> 
	  `ideal_model_trans (IM, C_INTERNAL, IM'')` by (
              RW_TAC (srw_ss()) [ideal_model_trans_def]
	  ) >>
	  `ideal_model_comp (IM, SUC 0, IM'')` by (
              METIS_TAC [ideal_model_comp_def]
	  ) >>
	  EXISTS_TAC ``SUC 0`` >>
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [] >>
	  (* add context about write *)
	  `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
		(mem_abs((IM''.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
              REPEAT STRIP_TAC >>
	      Cases_on `g = PCG n` 
	      >| [(* case: PCG n *) 
	          `(IM''.G g).m = (IM'.G g).m` by (
	              Q.UNABBREV_TAC `IM''` >>
		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		  ) >>
	          `(IM'.G g).m = im'` by (
	              Q.UNABBREV_TAC `IM'` >>
		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		  ) >>
		  ASM_REWRITE_TAC [] >>
		  METIS_TAC [mem_access_bisim_lem]
		  ,
		  Cases_on `g = g2`
		  >| [(* case: g2 *)
		      Cases_on `a = a2`
		      >| [(* updated page *)
		          Q.UNABBREV_TAC `IM''` >>
		          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM,
					     memory_upd_mem_abs_id_lem] >>
			  `Trans g a = Trans (PCG n) (PAdr r')` by (
			      METIS_TAC [Trans_axiom,
					 pairTheory.FST, pairTheory.SND]
			  ) >>
			  `(IM'.G (PCG n)).m = im'` by (
			      Q.UNABBREV_TAC `IM'` >>
			      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
			  ) >>
			  ASM_REWRITE_TAC [] >>
			  METIS_TAC [mem_access_bisim_lem]
			  ,
			  (* other pages *)
		          Q.UNABBREV_TAC `IM''` >>
		          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
			  `mem_abs (memory_upd (a2,
				mem_abs (IM'.G (PCG n)).m (PAdr r'))
					       (IM'.G g).m) a = 
		           mem_abs (IM'.G g).m a` by (
			      METIS_TAC [memory_upd_axiom] 
			  ) >>
			  `(IM'.G g).m = (IM.G g).m` by (
			      Q.UNABBREV_TAC `IM'` >>
			      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
			  ) >>
			  ASM_REWRITE_TAC [] >>
			  METIS_TAC [igc_write_mem_upd_others_lem]
			 ]
		      ,
		      (* all other unaffected guests *)
		      `(IM''.G g).m = (IM'.G g).m` by (
		          Q.UNABBREV_TAC `IM''` >>
			  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		      ) >>
		      `(IM'.G g).m = (IM.G g).m` by (
		          Q.UNABBREV_TAC `IM'` >>
			  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		      ) >>
		      ASM_REWRITE_TAC [] >>
		      METIS_TAC [igc_write_mem_upd_others_lem]
		     ]
		 ]
	  ) >>
	  `!g. g < PAR.ng ==>
	       (mem_req_rcvd (IM''.G g).m = mem_req_rcvd (IM'.G g).m)
	    /\ (mem_req_sent (IM''.G g).m = mem_req_sent (IM'.G g).m)
	    /\ (mem_rpl_rcvd (IM''.G g).m = mem_rpl_rcvd (IM'.G g).m)` by (
	      STRIP_TAC >> STRIP_TAC >> Cases_on `g = g2`
	      >| [Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
		      METIS_TAC [memory_upd_axiom]
		  )
		  ,
		  Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		 ]
	  ) >>
	  `!g. g < PAR.ng ==>
	       ((IM''.G g).cif = (IM'.G g).cif)` by (
	      STRIP_TAC >> STRIP_TAC >>
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  (* prove SIM *)
	  Q.UNABBREV_TAC `IM'` >>
	  Q.UNABBREV_TAC `IM''` >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  REPEAT STRIP_TAC >> (
	  EXCEPT_FOR ``bisim_send_igc _`` (
	  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	  (* try to solve straight-forward cases *)
	  >> (REPEAT IF_CASES_TAC >>
              STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] ) )
	  )
	  ) >>
	  (* send_igc *)
	  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	  `nusgi((\c. RM.C c),
		 (\c. if n = c then 
			  mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
		      else 
			  mmu_rpl_rcvd (RM.MMU c)),
		 mem_rpl_rcvd RM.m) = 
           nusgi((\c. RM.C c),
		 (\c. mmu_rpl_rcvd (RM.MMU c)),
		 mem_rpl_rcvd RM.m)` by (
              RW_TAC std_ss [FUN_EQ_THM] >>
	      `?a b. x = (a,b)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
	      Cases_on `a = n` >> (
	          RW_TAC std_ss [nusgi_def, Mode_arith_lem]
	      )
	  ) >>
	  METIS_TAC []
	 ]
     ]
);

val do_sync_igc_write_lem = store_thm("do_sync_igc_write_lem", ``
!IM IM' IM'' n r' q cif' im' s ra rg.
   InvI IM
/\ rg < PAR.ng
/\ n < RPAR.nc
/\ req_aligned r'
/\ match (r',q)
/\ s < PAR.ns
/\ (PAR.igca s = (PAdr r',ra))
/\ (PAR.cpol s = (PCG n,rg))
/\ rg <> PCG n
/\ (q,CoreSender (PCC n)) NOTIN mem_rpl_rcvd (IM.G (PCG n)).m
/\ mem_step_snd_rpl ((IM.G (PCG n)).m,q,CoreSender (PCC n), im')
/\ do_sync_shared_mem_upd_of_guest (IM'',PCG n,IM')
/\ Abbrev (IM'' = <|G := (PCG n =+ IM.G (PCG n) with
                      <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)
                          IM.G|>)
==>
   (IM'.G (PCG n) = IM.G (PCG n) with 
                        <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; 
			  m := im'|>)
/\ (IM'.G rg = IM.G rg with 
        m := memory_upd (ra, mem_abs im' (PAdr r')) (IM.G rg).m)
/\ (!g. g < PAR.ng /\ g <> PCG n /\ g <> rg ==> (IM'.G g = IM.G g))  
``,
  REPEAT STRIP_TAC
  >| [(* PGC n *)
      `~(?s. s < PAR.ns /\ (PAR.cpol s = (PCG n,PCG n)))` by (
           METIS_TAC [goodP_axiom]
      ) >>
      `(IM'.G (PCG n)).m = (IM''.G (PCG n)).m` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      `IM'.G (PCG n) = IM''.G (PCG n)` suffices_by (
          Q.UNABBREV_TAC `IM''` >>
          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `?x. IM'.G (PCG n) = IM''.G (PCG n) with m := x` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      RW_TAC std_ss [guest_component_equality]
      ,
      (* receiving guest *)
      `(IM'.G rg).m = memory_upd 
                          (ra, mem_abs (IM''.G (PCG n)).m (PAdr r')) 
		          (IM''.G rg).m` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      `IM.G rg = IM''.G rg` by (
          Q.UNABBREV_TAC `IM''` >>
          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>
      ASM_REWRITE_TAC [] >>
      `?x. IM'.G rg = IM''.G rg with m := x` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      RW_TAC std_ss [guest_component_equality] >>
      `(IM''.G (PCG n)).m = im'` by (
          Q.UNABBREV_TAC `IM''` >>
          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>   
      ASM_REWRITE_TAC []
      ,
      (* any other guest *)
      `IM.G g = IM''.G g` by (
          Q.UNABBREV_TAC `IM''` >>
	  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>   
      ASM_REWRITE_TAC [] >>
      `PCG n < PAR.ng` by ( METIS_TAC [good_proj_in_range_impls] ) >>
      Cases_on `?s. s < PAR.ns /\ (PAR.cpol s = (PCG n,g))`
      >| [(* exists channel -> identical update *)
	  FULL_SIMP_TAC std_ss [] >>
          `?sa ga. PAR.igca s' = (sa,ga)` by (
	      METIS_TAC [pairTheory.pair_CASES]
	  ) >>
	  `(IM'.G g).m = memory_upd 
                         (ga, mem_abs (IM''.G (PCG n)).m sa) 
		         (IM''.G g).m` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
	  ) >>
	  `s' <> s` by (
	       CCONTR_TAC >>
	       FULL_SIMP_TAC std_ss []
	  ) >>
	  `sa <> PAdr r'` by ( 
	       METIS_TAC [goodP_axiom, pairTheory.FST] 
	  ) >>
	  `mem_abs (IM''.G (PCG n)).m sa = mem_abs (IM''.G g).m ga` by (
	      `mem_abs (IM''.G (PCG n)).m sa = 
	       mem_abs (IM.G g).m ga` suffices_by (
	          RW_TAC std_ss []
	      ) >>
	      IMP_RES_TAC InvI_def >>
	      `mem_abs (IM''.G (PCG n)).m sa = 
	       mem_abs (IM.G (PCG n)).m sa` suffices_by (
	          STRIP_TAC >>
		  THROW_AWAY_TAC ``IM.G g = IM''.G g`` >>
		  ASM_REWRITE_TAC [] >>
		  IMP_RES_TAC syncInv_def >>
		  ASM_REWRITE_TAC []
	      ) >>
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      METIS_TAC [mem_aligned_unchanged_lem]
	  ) >>
	  FULL_SIMP_TAC std_ss [memory_id_upd_axiom] >>
          `?x. IM'.G g = IM''.G g with m := x` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
          ) >>
          RW_TAC std_ss [guest_component_equality]
	  ,
	  (* no output channel *)
	  `(IM'.G g).m = (IM''.G g).m` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
	  ) >>
          `?x. IM'.G g = IM''.G g with m := x` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
          ) >>
          RW_TAC std_ss [guest_component_equality]
	 ]
     ]
);

val id_final_mmu_rpl_no_fwd_lem = store_thm("id_final_mmu_rpl_no_fwd_lem", ``
!RM IM IM' n r' q MMU' m' cif' im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ SimInvR RM
/\ n < RPAR.nc
/\ mmu_step_rcv_rpl (RM.MMU n,Trrpl (PCG n) q,MMU')
/\ mem_step_snd_rpl (RM.m,Trrpl (PCG n) q,CoreSender n,m')
/\ Trreq (PCG n) r' IN mmu_req_sent (RM.MMU n)
/\ match (Trreq (PCG n) r',Trrpl (PCG n) q)
/\ ((mmu_abs (RM.MMU n)).state r' = FINAL (SOME (Trreq (PCG n) r')))
/\ Mode (RM.C n) < 2
/\ IS_SOME (Trans (PCG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PCG n)
/\ PAdr r' NOTIN A_gicper
/\ r' IN ((IM.G (PCG n)).cif (PCC n)).req_sent
/\ mem_step_snd_rpl ((IM.G (PCG n)).m,q,CoreSender (PCC n), im')
/\ match (r',q)
/\ IS_SOME (Trans (PCG n) (Rpl_PAdr q))
/\ bif_step_rcv_rpl ((IM.G (PCG n)).cif (PCC n),q,cif')
/\ sync_shared_mem_upd_of_guest
       (<|G := 
	    (PCG n =+ IM.G (PCG n) with
                 <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)
                IM.G|>,PCG n,IM')
==>
?n' RM'.
  refined_comp (RM,n',RM') /\
  SIM (RM',IM') /\
  SimInvR RM'
``,
  REPEAT STRIP_TAC >>
  (* start with computation part *)
  IMP_RES_TAC proj_bound_lem >>
  `ref_rule_mmu_rcv_mrpl(RM, n, 
			 RM with <|MMU := (n =+ MMU') RM.MMU; m := m'|>)` by (
      RW_TAC (srw_ss()) [ref_rule_mmu_rcv_mrpl_def, 
			 mem_step_def, mmu_step_def] >>
      METIS_TAC []
  ) >>
  `refined_trans(RM, MMU_RCV_MRPL n, RM with <|MMU := (n =+ MMU') RM.MMU; 
					       m := m'|>)` by (
      RW_TAC (srw_ss()) [refined_trans_def] 
  ) >>
  (* add some context *)
  `(q,CoreSender (PCC n)) NOTIN mem_rpl_rcvd ((IM.G (PCG n)).m)` by (
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `(Trrpl (PCG n) q,CoreSender n) NOTIN mem_rpl_rcvd (RM.m)` by (
      IMP_RES_TAC not_A_gicper_Trreq_lem >>
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `req_aligned r'` by ( IMP_RES_TAC mmu_Trreq_aligned_lem ) >>
  `inv_good_mem (IM.G (PCG n)).m` by (
     FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``PCG n``]
  ) >>
  `good_rpl q` by ( IMP_RES_TAC good_mem_rpl_axiom ) >>
  `inv_good_mmu (RM.MMU n)` by (
     FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
  ) >>
  `(mmu_abs (RM.MMU n)).active` by (
      IMP_RES_TAC mmu_active_lem
  ) >>
  `  (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd (RM.MMU n) UNION {Trrpl (PCG n) q})
  /\ (mmu_req_sent MMU' = mmu_req_sent (RM.MMU n) DIFF {Trreq (PCG n) r'})
  /\ (mmu_ptl_hist MMU' = mmu_ptl_hist (RM.MMU n))
  /\ ((mmu_abs MMU').state = (mmu_abs (RM.MMU n)).state)
  /\ (mmu_req_rcvd MMU' = mmu_req_rcvd (RM.MMU n))
  /\ (mmu_abs MMU').active
  /\ ((mmu_abs MMU').cfg = (mmu_abs (RM.MMU n)).cfg)` by (
      METIS_TAC [mmu_final_rpl_lem]
  ) >>
  `  (cif'.req_rcvd = ((IM.G (PCG n)).cif (PCC n)).req_rcvd)
  /\ (cif'.rpl_rcvd = ((IM.G (PCG n)).cif (PCC n)).rpl_rcvd UNION {q})
  /\ (cif'.req_sent = ((IM.G (PCG n)).cif (PCC n)).req_sent DIFF {r'})` by (
      METIS_TAC [bif_rcv_rpl_lem]
  ) >>
  IMP_RES_TAC guest_Trreq_lem >>
  IMP_RES_TAC HV_guest_disj_lem >> 
  `req_aligned (Trreq (PCG n) r')` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
	  METIS_TAC [inv_good_mmu_def]
  ) >>
  `!a. a IN RPAR.Amap HV ==> (mem_abs m' a = mem_abs RM.m a)` by (
      IMP_RES_TAC mem_unchanged_lem 
  ) >>
  IMP_RES_TAC hvds_unchanged_lem >>
  `!g r. g < PAR.ng ==> 
         (gcpys (mem_abs m' (ADRDS (GCPY g))) (g,r) =
          gcpys (mem_abs RM.m (ADRDS (GCPY g))) (g,r))` by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  `!c b. c < RPAR.nc ==> (
	     ctxs (mem_abs m' (ADRDS (CTX c))) (b,c) =
             ctxs (mem_abs RM.m (ADRDS (CTX c))) (b,c))`  by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  IMP_RES_TAC mem_snd_rpl_merged_lem >>
  (* case split depending on write to A_IGCout *)
  Cases_on `(PAdr r' NOTIN A_IGCin (PCG n) /\ (PAdr r' NOTIN A_IGCout (PCG n)) 
	    \/ ~Wreq r')`
  >| [(* show that syncInv still holds *)
      Q.ABBREV_TAC `IM'' = <|G := (PCG n =+ IM.G (PCG n) with
                    <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)
				  IM.G|>` >>
      `syncInv IM''` by ( 
	  MATCH_MP_TAC cif_no_igc_write_sync_lem >>
	  HINT_EXISTS_TAC >>
	  HINT_EXISTS_TAC >>
	  HINT_EXISTS_TAC >>
	  HINT_EXISTS_TAC >>
	  EXISTS_TAC ``PCC n`` >>
	  HINT_EXISTS_TAC >>
	  EXISTS_TAC ``CoreSender (PCC n)`` >>
	  EXISTS_TAC ``r':request`` >>
	  ASM_REWRITE_TAC [] >>
	  Q.UNABBREV_TAC `IM''` >>
	  RW_TAC (srw_ss()) []
      ) >> 
      Q.ABBREV_TAC `not_write_or_igc =
      	(PAdr r' NOTIN A_IGCin (PCG n) /\ (PAdr r' NOTIN A_IGCout (PCG n))
      	    \/ ~Wreq r')` >>
      (* show existence of refined computation *) 
      FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
      `refined_comp(RM,SUC 0, RM with <|m := m'; 
				        MMU := (n =+ MMU') RM.MMU|>)` by (
          METIS_TAC [refined_comp_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [] >>
      (* show that memory is still in simulation *)
      `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
             (mem_abs((IM''.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
          REPEAT STRIP_TAC >>
	  Cases_on `g = PCG n` 
	  >| [`(IM''.G g).m = im'` by (
	          Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      METIS_TAC [mem_access_bisim_lem]
	      ,
	      `(IM''.G g).m = (IM.G g).m` by (
	          Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
              METIS_TAC [no_igc_write_mem_upd_others_lem]
	     ]
      ) >>
      `~hv_guard_mmu_fault 
           (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n),n)` by (
          MATCH_MP_TAC hv_guard_mmu_fault_lem >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `~hv_gicd_entry_state
           (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n))` by (
          MATCH_MP_TAC hv_gicd_entry_state_lem >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      (* show SIM *) 
      STRIP_TAC >- (
      Q.UNABBREV_TAC `IM''` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      EXCEPT_FOR ``bisim_send_igc _`` (
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	  ) >>
      	  TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			   hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			   hv_mmu_fault_entry_eq_lem,
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			   nuvi_def, nuigc_def, nusgi_def] ) )
      )
      ) >>
      (* send_igc *)
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
      `nusgi((\c. RM.C c),
	     (\c. if n = c then 
		      mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
		  else 
		      mmu_rpl_rcvd (RM.MMU c)),
	     mem_rpl_rcvd RM.m) = 
       nusgi((\c. RM.C c),
	     (\c. mmu_rpl_rcvd (RM.MMU c)),
              mem_rpl_rcvd RM.m)` by (
          RW_TAC std_ss [FUN_EQ_THM] >>
          `?a b. x = (a,b)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
	  Cases_on `a = n` >> (
	      RW_TAC std_ss [nusgi_def, Mode_arith_lem]
	  )
      ) >>
      METIS_TAC []
      ) >>
      (* SimInvR *)
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ,
      (* case: write to IGC memory *)
      FULL_SIMP_TAC (srw_ss()) []
      >| [(* case: write to A_IGCin -> not possible *)
	  FULL_SIMP_TAC (srw_ss()) [A_IGCin_def, InvR_EXPAND] >>
	  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  METIS_TAC []
	  ,
	  (* case: write to A_IGCout -> prove additional sync *)
	  Q.ABBREV_TAC `IM'' = <|G := (PCG n =+ IM.G (PCG n) with
                        <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)
					  IM.G|>` >>
	  Cases_on `syncInv IM''`
	  >| [(* syncInv -> Write no effect *)
              FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
	      `refined_comp(RM,SUC 0, RM with <|m := m'; 
				         MMU := (n =+ MMU') RM.MMU|>)` by (
                  METIS_TAC [refined_comp_def]
	      ) >>
	      EXISTS_TAC ``SUC 0`` >>
	      HINT_EXISTS_TAC >>
	      ASM_REWRITE_TAC [] >>
	      (* show that memory is still in simulation *)
              `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
	       (mem_abs((IM''.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
                  REPEAT STRIP_TAC >>
              	  Cases_on `g = PCG n` 
           	  >| [(* same guest *)
           	      `(IM''.G g).m = im'` by (
           	          Q.UNABBREV_TAC `IM''` >>
           		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
           	      ) >>
           	      ASM_REWRITE_TAC [] >>
           	      METIS_TAC [mem_access_bisim_lem]
           	      ,
           	      (* other guest *)
           	      Cases_on `THE (Trans g a) = THE (Trans (PCG n) (PAdr r'))`
           	      >| [(* igc input channel, unchanged *)
           		  `?s. s < PAR.ns /\ (PAR.cpol s = (PCG n, g)) /\
           		       (PAR.igca s = (PAdr r', a))` by (
           		      METIS_TAC [Trans_eq_igc_out_lem]
           		  ) >>
           		  `mem_abs (IM''.G g).m a = 
           	           mem_abs (IM''.G (PCG n)).m (PAdr r')` by (
           		      METIS_TAC [syncInv_def]
           		  ) >>
           		  `(IM''.G (PCG n)).m = im'` by (
           	              Q.UNABBREV_TAC `IM''` >>
           		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
           		  ) >>
           		  `Trans g a = Trans (PCG n) (PAdr r')` by (
           		      METIS_TAC [Trans_axiom, 
					 pairTheory.FST, pairTheory.SND]   
           		  ) >>
           		  ASM_REWRITE_TAC [] >>
           		  METIS_TAC [mem_access_bisim_lem]
           		  ,
           		  (* other address, unchanged *)
           		  `(IM''.G g).m = (IM.G g).m` by (
           	              Q.UNABBREV_TAC `IM''` >>
           		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
           		  ) >>
           		  `a <> Agicd` by (
           		      METIS_TAC [Agicd_A_gicper_lem]
           		  ) >>
           		  `IS_SOME (Trans g a)` by (
           		      METIS_TAC [Trans_axiom]   
           		  ) >>
           		  `THE (Trans g a) <> PAdr (Trreq (PCG n) r')` by (
           		      RW_TAC std_ss [Trreq_PAdr_Trans_lem]
           		  ) >>
           		  `mem_abs m' (THE (Trans g a)) = 
           	           mem_abs RM.m (THE (Trans g a))` by (
           		      METIS_TAC [mem_aligned_unchanged_lem]
           		  ) >>
           		  ASM_REWRITE_TAC [] >>
           		  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
           		  IMP_RES_TAC bisim_memory_def
           		 ]
           	     ]
	      ) >>
              `~hv_guard_mmu_fault 
                   (HVabs (RM with <|m := m'; 
				     MMU := (n =+ MMU') RM.MMU|>,n),n)` by (
                  MATCH_MP_TAC hv_guard_mmu_fault_lem >>
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
              ) >>
              `~hv_gicd_entry_state
                   (HVabs (RM with <|m := m'; 
				     MMU := (n =+ MMU') RM.MMU|>,n))` by (
                  MATCH_MP_TAC hv_gicd_entry_state_lem >>
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
              ) >>
              IMP_RES_TAC hv_guard_mmu_fault_lem >>
              IMP_RES_TAC hv_gicd_entry_state_lem >>
              (* show SIM *) 
              STRIP_TAC >- (
              Q.UNABBREV_TAC `IM''` >>
              FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
              REPEAT STRIP_TAC >> (
              EXCEPT_FOR ``bisim_send_igc _`` (
              FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
              (* try to solve straight-forward cases *)
              >> (REPEAT IF_CASES_TAC >>
                  STRONG_FS_TAC ([]@bisim_core_definitions) >>
              	  `RM.C c = (RM with <|m := m'; 
				       MMU := (n =+ MMU') RM.MMU|>).C c` by (
                      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
              	  ) >>
              	  TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
              			   hv_guard_mmu_fault_eq_lem, 
				   hv_guard_gicd_fail_lem,
              			   hv_mmu_fault_entry_eq_lem,
              			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              			   proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
              			   nuvi_def, nuigc_def, nusgi_def] ) )
              )
              ) >>
              (* send_igc *)
              FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
              `nusgi((\c. RM.C c),
              	     (\c. if n = c then 
              		      mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
              		  else 
              		      mmu_rpl_rcvd (RM.MMU c)),
              	     mem_rpl_rcvd RM.m) = 
               nusgi((\c. RM.C c),
              	     (\c. mmu_rpl_rcvd (RM.MMU c)),
                      mem_rpl_rcvd RM.m)` by (
                  RW_TAC std_ss [FUN_EQ_THM] >>
                  `?a b. x = (a,b)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
              	  Cases_on `a = n` >> (
              	      RW_TAC std_ss [nusgi_def, Mode_arith_lem]
              	  )
              ) >>
              METIS_TAC []
              ) >>
              (* SimInvR *)
              FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
              RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	      ,
	      (* not syncInv *)
              FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
	      `?s rg ra. s < PAR.ns /\ rg < PAR.ng /\
                         (PAR.igca s = (PAdr r',ra)) /\
			 (PAR.cpol s = (PCG n, rg)) /\ rg <> PCG n` by (
	          FULL_SIMP_TAC std_ss [A_IGCout_def, GSPEC_f_lem] >>
		  HINT_EXISTS_TAC >>
		  METIS_TAC [quantHeuristicsTheory.FST_PAIR_EQ,
			     goodP_axiom]
	      ) >>
	      `(IM'.G (PCG n) = IM.G (PCG n) with
                <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>) /\
               (IM'.G rg = IM.G rg with
                m := memory_upd (ra,mem_abs im' (PAdr r')) (IM.G rg).m) /\
               !g. g < PAR.ng /\ g <> PCG n /\ g <> rg ==> 
		   (IM'.G g = IM.G g)` by (
	          MATCH_MP_TAC do_sync_igc_write_lem >>
		  HINT_EXISTS_TAC >>
		  METIS_TAC []
	      ) >>
	      (* show existence of refined computation *)
              `refined_comp(RM,SUC 0, RM with 
                   <|m := m'; MMU := (n =+ MMU') RM.MMU|>)` by (
                  METIS_TAC [refined_comp_def]
              ) >>
	      EXISTS_TAC ``SUC 0`` >>
	      HINT_EXISTS_TAC >>
	      ASM_REWRITE_TAC [] >>
	      (* add context about write *)
	      `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
	      	(mem_abs((IM'.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
                  REPEAT STRIP_TAC >>
	          Cases_on `g = PCG n` 
	          >| [(* case: PCG n *) 
	              `(IM'.G g).m = im'` by (
	                  Q.UNABBREV_TAC `IM''` >>
	      	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      	  ) >>
	      	  ASM_REWRITE_TAC [] >>
	      	  METIS_TAC [mem_access_bisim_lem]
	      	  ,
	      	  Cases_on `g = rg`
	      	  >| [(* case: g2 *)
	      	      Cases_on `a = ra`
	      	      >| [(* updated page *)
	      		  `Trans g a = Trans (PCG n) (PAdr r')` by (
	      		      METIS_TAC [Trans_axiom,
	      				 pairTheory.FST, pairTheory.SND]
	      		  ) >>
	      		  ASM_REWRITE_TAC [] >>
	      		  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM,
	      				 memory_upd_mem_abs_id_lem] >>
	      		  METIS_TAC [mem_access_bisim_lem]
	      		  ,
	      		  (* other pages *)
	      		  `mem_abs (IM.G rg with m := 
	      		       memory_upd (ra,mem_abs im' (PAdr r')) (IM.G rg).m
	      			   ).m a = mem_abs (IM.G rg).m a` by (
	      		      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      		      METIS_TAC [memory_upd_axiom]
	      		  ) >>
	      		  ASM_REWRITE_TAC [] >>
	      		  METIS_TAC [igc_write_mem_upd_others_lem]
	      		 ]
	      	      ,
	      	      (* all other unaffected guests *)
	      	      RES_TAC >>
	      	      ASM_REWRITE_TAC [] >>
	      	      METIS_TAC [igc_write_mem_upd_others_lem]
	      	     ]
	      	 ]
	      ) >>
	      `!g. g < PAR.ng ==>
	           (mem_req_rcvd (IM'.G g).m = mem_req_rcvd (IM''.G g).m)
	        /\ (mem_req_sent (IM'.G g).m = mem_req_sent (IM''.G g).m)
	        /\ (mem_rpl_rcvd (IM'.G g).m = mem_rpl_rcvd (IM''.G g).m)` by (
	          STRIP_TAC >> STRIP_TAC >> Cases_on `g = rg`
	          >| [Q.UNABBREV_TAC `IM''` >>
	      	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
	      	          METIS_TAC [memory_upd_axiom]
	      	      )
	      	      ,
	      	      Cases_on `g = PCG n` >> (
	      	          Q.UNABBREV_TAC `IM''` >>
	      	          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
	      	              METIS_TAC [memory_upd_axiom]
	      	          ) 
	      	      )
	      	     ]
	      ) >>
	      `!g. g < PAR.ng ==>
	           ((IM'.G g).cif = (IM''.G g).cif)` by (
	          STRIP_TAC >> STRIP_TAC >> Cases_on `g = PCG n` 
	          >| [Q.UNABBREV_TAC `IM''` >>
	              RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] 
	              ,
	      	      Cases_on `g = rg` >> (
	                  Q.UNABBREV_TAC `IM''` >>
	          	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      	      )
	             ]
	      ) >>
	      (* prove SIM *)
	      Q.UNABBREV_TAC `IM''` >>
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      REPEAT STRIP_TAC
	  >| [(* ctx *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* memory *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS
	      ,
	      (* periph *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >> (
	          Cases_on `PPG p = PCG n`
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
	              ,
	              Cases_on `PPG p = rg` >> (
	                  STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
	             ]
	      )
	      ,
	      (* corereq_guest *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* corereq_hyp *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* corereq_gicd *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* mmureq_guest *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  IF_CASES_TAC
		  >| [`PCC n <> PCC c` by (
		          METIS_TAC [PCG_PCC_inj]
		      ) >>
		      RW_TAC std_ss [] >>
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* gicdmsg_ideal *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  IF_CASES_TAC
		  >| [`PCC n <> PCC c` by (
		          METIS_TAC [PCG_PCC_inj]
		      ) >>
		      RW_TAC std_ss [] >>
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* gicdmsg_refined *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  IF_CASES_TAC
		  >| [`PCC n <> PCC c` by (
		          METIS_TAC [PCG_PCC_inj]
		      ) >>
		      RW_TAC std_ss [] >>
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* smmureq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >> (
	          Cases_on `PPG p = PCG n`
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
	              ,
	              Cases_on `PPG p = rg` >> (
	                 STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
	             ]
	      )
	      ,
	      (* giccreq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* gicdreq_ideal *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* gicdreq_refined *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* gicd_fail *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      )
	      ,
	      (* memreq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS
	      >| [IF_CASES_TAC
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		  ,
		  Cases_on `PPG p = PCG n`
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		      ,
		      Cases_on `PPG p = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* perirq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
	          ,
		  Cases_on `PCG c = PCG n` 
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* igcirq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
	          ,
		  Cases_on `PCG c = PCG n` 
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* sgiirq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
	          ,
		  Cases_on `PCG c = PCG n` 
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
		     ]
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			       nuvi_def, nuigc_def, nusgi_def] )
	      ) 
	      ,
	      (* send_igc *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      STRONG_FS_TAC ([]@bisim_core_definitions) >>
	      REPEAT STRIP_TAC >> (
	          Cases_on `g = PCG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `g = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
	      ) >> (
	          `nusgi((\c. RM.C c),
	          	 (\c. if n = c then 
	          		  mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
	          	      else 
	          		  mmu_rpl_rcvd (RM.MMU c)),
	          	 mem_rpl_rcvd RM.m) = 
                   nusgi((\c. RM.C c),
	          	 (\c. mmu_rpl_rcvd (RM.MMU c)),
	          	 mem_rpl_rcvd RM.m)` by (
                      RW_TAC std_ss [FUN_EQ_THM] >>
	              `?a b. x = (a,b)` by ( 
		          METIS_TAC [pairTheory.pair_CASES] 
		      ) >>
	              Cases_on `a = n` >> (
	                  RW_TAC std_ss [nusgi_def, Mode_arith_lem]
	              )
	          ) >>
	          METIS_TAC []
	      )
	      ,
	      (* bisim_ext *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >> (
	          Cases_on `g = PCG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `g = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
	      )
	      ,
	      (* psci *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS
	      >| [Cases_on `PCG c = PCG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		  ,
	          Cases_on `PCG c = PCG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		 ]
	      ,
	      (* gicc_reg *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PCG n`
	      >| [STRONG_FS_TAC []
		  ,
		  Cases_on `PCG c = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* gicd_reg *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `g = PCG n`
	      >| [STRONG_FS_TAC []
		  ,
		  Cases_on `g = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* pi *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `g = PCG n`
	      >| [STRONG_FS_TAC []
		  ,
		  Cases_on `g = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      ALL_TAC
	     ] >>
	      (* SimInvR *)
              FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
              RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	     ]
	 ]
     ]
);

val final_mmu_rpl_fwd_lem = store_thm("final_mmu_rpl_fwd_lem", ``
!RM IM n r' q MMU' m' cif' im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.nc
/\ mmu_step_rcv_rpl (RM.MMU n,Trrpl (PCG n) q,MMU')
/\ mem_step_snd_rpl (RM.m,Trrpl (PCG n) q,CoreSender n,m')
/\ Trreq (PCG n) r' IN mmu_req_sent (RM.MMU n)
/\ match (Trreq (PCG n) r',Trrpl (PCG n) q)
/\ ((mmu_abs (RM.MMU n)).state r' = FINAL (SOME (Trreq (PCG n) r')))
(* /\ (refcore_abs (RM.C n)).active *)
/\ Mode (RM.C n) < 2
/\ IS_SOME (Trans (PCG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PCG n)
/\ PAdr r' IN A_gicper
/\ r' IN ((IM.G (PCG n)).cif (PCC n)).req_sent
/\ mem_step_snd_rpl ((IM.G (PCG n)).m,q,CoreSender (PCC n), im')
/\ match (r',q)
/\ IS_SOME (Trans (PCG n) (Rpl_PAdr q))
/\ bif_step_rcv_rpl ((IM.G (PCG n)).cif (PCC n),q,cif')
==>
?n' IM'.
  ideal_model_comp (IM,n',IM') /\
  SIM (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,IM')
``,
  REPEAT STRIP_TAC >>
  (* start with computation part *)
  IMP_RES_TAC proj_bound_lem >>
  `?G'. id_rule_cif_rcv_rpl(IM.G (PCG n), PCC n, G') 
     /\ (G' = (IM.G (PCG n)) with 
              <|cif := (PCC n =+ cif') ((IM.G (PCG n)).cif); m := im'|>)` by (
      RW_TAC (srw_ss()) [id_rule_cif_rcv_rpl_def, 
			 mem_step_def, bif_step_def] >>
      METIS_TAC []
  ) >>
  `?IM'. ideal_guest_trans(IM.G (PCG n), PCG n, 
			   INTERNAL (IR_CIF_RCV_SRPL (PCC n)), G')
         /\ (IM' = IM with G := (PCG n =+ G') IM.G)` by (
      RW_TAC (srw_ss()) [ideal_guest_trans_def] 
  ) >>
  (* add some context *)
  RW_TAC (srw_ss()) [] >>
  `(q,CoreSender (PCC n)) IN mem_rpl_rcvd ((IM.G (PCG n)).m)` by (
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_fw_lem]
  ) >>
  `(Trrpl (PCG n) q,CoreSender n) IN mem_rpl_rcvd (RM.m)` by (
      IMP_RES_TAC A_gicper_Trreq_lem >>
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_fw_lem]
  ) >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `req_aligned r'` by ( IMP_RES_TAC mmu_Trreq_aligned_lem ) >>
  `inv_good_mem (IM.G (PCG n)).m` by (
     FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``PCG n``]
  ) >>
  `good_rpl q` by ( IMP_RES_TAC good_mem_rpl_axiom ) >>
  `inv_good_mmu (RM.MMU n)` by (
     FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
  ) >>
  `(mmu_abs (RM.MMU n)).active` by (
      IMP_RES_TAC mmu_active_lem
  ) >>
  `  (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd (RM.MMU n) UNION {Trrpl (PCG n) q})
  /\ (mmu_req_sent MMU' = mmu_req_sent (RM.MMU n) DIFF {Trreq (PCG n) r'})
  /\ (mmu_ptl_hist MMU' = mmu_ptl_hist (RM.MMU n))
  /\ ((mmu_abs MMU').state = (mmu_abs (RM.MMU n)).state)
  /\ (mmu_req_rcvd MMU' = mmu_req_rcvd (RM.MMU n))
  /\ (mmu_abs MMU').active
  /\ ((mmu_abs MMU').cfg = (mmu_abs (RM.MMU n)).cfg)` by (
      METIS_TAC [mmu_final_rpl_lem]
  ) >>
  `  (cif'.req_rcvd = ((IM.G (PCG n)).cif (PCC n)).req_rcvd)
  /\ (cif'.rpl_rcvd = ((IM.G (PCG n)).cif (PCC n)).rpl_rcvd UNION {q})
  /\ (cif'.req_sent = ((IM.G (PCG n)).cif (PCC n)).req_sent DIFF {r'})` by (
      METIS_TAC [bif_rcv_rpl_lem]
  ) >>
  `(mem_abs m' = mem_abs RM.m) /\ 
   (mem_req_rcvd m' = 
        mem_req_rcvd RM.m DIFF {(Trreq (PCG n) r',CoreSender n)}) /\ 
   (mem_req_sent m' = mem_req_sent RM.m) /\ 
   (mem_rpl_rcvd m' = 
        mem_rpl_rcvd RM.m DIFF {Trrpl (PCG n) q,CoreSender n})` by (
      METIS_TAC [mem_io_fw_axiom, unique_match_thm] 
  ) >>
  `(mem_abs im' = mem_abs (IM.G (PCG n)).m) /\ 
   (mem_req_rcvd im' = 
        mem_req_rcvd (IM.G (PCG n)).m DIFF {(r',CoreSender (PCC n))}) /\ 
   (mem_req_sent im' = mem_req_sent (IM.G (PCG n)).m) /\ 
   (mem_rpl_rcvd im' = 
        mem_rpl_rcvd (IM.G (PCG n)).m DIFF {(q,CoreSender (PCC n))})` by (
      METIS_TAC [mem_io_fw_axiom, unique_match_thm] 
  ) >>
  (* show that syncInv still holds *)
  Q.ABBREV_TAC `IM' = IM with G := (PCG n =+ (IM.G (PCG n) with
      <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)) IM.G` >>
  `syncInv IM'` by ( 
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM'` >>
      RW_TAC (srw_ss()) [] >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]          
  ) >> 
  (* show existence of ideal computation *) 
  `sync_shared_mem_upd_of_guest (IM', PCG n, IM')` by (
      RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
  ) >>
  `comp_rule_internal(IM,IM')`  by ( 
      METIS_TAC [comp_rule_internal_def]
  ) >> 
  `ideal_model_trans (IM, C_INTERNAL, IM')` by (
      RW_TAC (srw_ss()) [ideal_model_trans_def]
  ) >>
  `ideal_model_comp (IM, SUC 0, IM')` by (
      METIS_TAC [ideal_model_comp_def]
  ) >>
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC [] >>
  `~hv_guard_mmu_fault 
       (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n),n)` by (
      MATCH_MP_TAC hv_guard_mmu_fault_lem >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  `~hv_gicd_entry_state
       (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n))` by (
      MATCH_MP_TAC hv_gicd_entry_state_lem >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  IMP_RES_TAC hv_guard_mmu_fault_lem >>
  IMP_RES_TAC hv_gicd_entry_state_lem >>
  `!q' c. n <> c ==>
       (pend_rpl (mmu_rpl_rcvd (RM.MMU c),
		  mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
		  c,q') = 
	pend_rpl (mmu_rpl_rcvd (RM.MMU c),
		  mem_rpl_rcvd RM.m,
		  c,q'))` by (
      RW_TAC std_ss [pend_rpl_def, pred_setTheory.IN_DIFF] >>
      EQ_TAC
      >| [METIS_TAC []
	  ,
	  RW_TAC std_ss [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
	 ]
  ) >>
  `!q' c. c < RPAR.nc /\ (PCG n = PCG c) /\ n <> c ==>
       (id_pend_rpl(((IM.G (PCG c)).cif (PCC c)).rpl_rcvd,
		    mem_rpl_rcvd (IM.G (PCG c)).m DIFF {(q,CoreSender (PCC n))},
		    PCG c,PCC c,q') = 
	id_pend_rpl(((IM.G (PCG c)).cif (PCC c)).rpl_rcvd,
		    mem_rpl_rcvd (IM.G (PCG c)).m,
		    PCG c,PCC c,q'))` by (
      RW_TAC std_ss [id_pend_rpl_def, pred_setTheory.IN_DIFF] >>
      `PCC c <> PCC n` by ( METIS_TAC [PCG_PCC_inj] ) >>
      EQ_TAC
      >| [METIS_TAC []
	  ,
	  RW_TAC std_ss [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
	 ]
  ) >>
  `!id c. n <> c ==>
   (nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) (PIR id,c) = 
    nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m,
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) (PIR id,c))` by (
      RW_TAC std_ss [nuvi_def]
  ) >>
  `!id c. n <> c ==>
   (nuigc(RM.C c,mmu_rpl_rcvd (RM.MMU c),
	  mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
	  llr (mem_abs RM.m (ADRDS LLR)) c) (PIR id,c) = 
    nuigc(RM.C c,mmu_rpl_rcvd (RM.MMU c),
	  mem_rpl_rcvd RM.m,
	  llr (mem_abs RM.m (ADRDS LLR)) c) (PIR id,c))` by (
      RW_TAC std_ss [nuigc_def]
  ) >>
  `!id c c'. n <> c ==>
   (nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) 
	    (PSQ_inv (PCG c) (SGI (id,c',c)),c) = 
    nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m,
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) 
	    (PSQ_inv (PCG c) (SGI (id,c',c)),c))` by (
      RW_TAC std_ss [nuvi_def]
  ) >>
  (* show SIM *) 
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  EXCEPT_FOR ``bisim_send_igc _`` (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
		       hv_mmu_fault_entry_eq_lem,
		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
		       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
		       nuvi_def, nuigc_def, nusgi_def] ) )
  )
  ) >>
  (* send_igc *)
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
  `nusgi((\c. RM.C c),
	 (\c. if n = c then 
		  mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
	      else 
		  mmu_rpl_rcvd (RM.MMU c)),
	 mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)}) = 
   nusgi((\c. RM.C c),
	 (\c. mmu_rpl_rcvd (RM.MMU c)),
	 mem_rpl_rcvd RM.m)` by (
      RW_TAC std_ss [FUN_EQ_THM] >>
      `?a b. x = (a,b)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
      Cases_on `a = n` >> (
          RW_TAC std_ss [nusgi_def, Mode_arith_lem]
      )
  ) >>
  METIS_TAC []				     
);

val id_final_mmu_rpl_fwd_lem = store_thm("id_final_mmu_rpl_fwd_lem", ``
!RM IM IM' n r' q MMU' m' cif' im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ SimInvR RM
/\ n < RPAR.nc
/\ mmu_step_rcv_rpl (RM.MMU n,Trrpl (PCG n) q,MMU')
/\ mem_step_snd_rpl (RM.m,Trrpl (PCG n) q,CoreSender n,m')
/\ Trreq (PCG n) r' IN mmu_req_sent (RM.MMU n)
/\ match (Trreq (PCG n) r',Trrpl (PCG n) q)
/\ ((mmu_abs (RM.MMU n)).state r' = FINAL (SOME (Trreq (PCG n) r')))
/\ Mode (RM.C n) < 2
/\ IS_SOME (Trans (PCG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PCG n)
/\ PAdr r' IN A_gicper
/\ r' IN ((IM.G (PCG n)).cif (PCC n)).req_sent
/\ mem_step_snd_rpl ((IM.G (PCG n)).m,q,CoreSender (PCC n), im')
/\ match (r',q)
/\ IS_SOME (Trans (PCG n) (Rpl_PAdr q))
/\ bif_step_rcv_rpl ((IM.G (PCG n)).cif (PCC n),q,cif')
/\ sync_shared_mem_upd_of_guest
       (<|G := 
	    (PCG n =+ IM.G (PCG n) with
                 <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)
                IM.G|>,PCG n,IM')
==>
?n' RM'.
  refined_comp (RM,n',RM') /\
  SIM (RM',IM') /\
  SimInvR RM'
``,
  REPEAT STRIP_TAC >>
  (* start with computation part *)
  IMP_RES_TAC proj_bound_lem >>
  `ref_rule_mmu_rcv_mrpl(RM, n, 
			 RM with <|MMU := (n =+ MMU') RM.MMU; m := m'|>)` by (
      RW_TAC (srw_ss()) [ref_rule_mmu_rcv_mrpl_def, 
			 mem_step_def, mmu_step_def] >>
      METIS_TAC []
  ) >>
  `refined_trans(RM, MMU_RCV_MRPL n, RM with <|MMU := (n =+ MMU') RM.MMU; 
					       m := m'|>)` by (
      RW_TAC (srw_ss()) [refined_trans_def] 
  ) >>
  (* add some context *)
  `(q,CoreSender (PCC n)) IN mem_rpl_rcvd ((IM.G (PCG n)).m)` by (
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_fw_lem]
  ) >>
  `(Trrpl (PCG n) q,CoreSender n) IN mem_rpl_rcvd (RM.m)` by (
      IMP_RES_TAC A_gicper_Trreq_lem >>
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_fw_lem]
  ) >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `req_aligned r'` by ( IMP_RES_TAC mmu_Trreq_aligned_lem ) >>
  `inv_good_mem (IM.G (PCG n)).m` by (
     FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``PCG n``]
  ) >>
  `good_rpl q` by ( IMP_RES_TAC good_mem_rpl_axiom ) >>
  `inv_good_mmu (RM.MMU n)` by (
     FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
  ) >>
  `(mmu_abs (RM.MMU n)).active` by (
      IMP_RES_TAC mmu_active_lem
  ) >>
  `  (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd (RM.MMU n) UNION {Trrpl (PCG n) q})
  /\ (mmu_req_sent MMU' = mmu_req_sent (RM.MMU n) DIFF {Trreq (PCG n) r'})
  /\ (mmu_ptl_hist MMU' = mmu_ptl_hist (RM.MMU n))
  /\ ((mmu_abs MMU').state = (mmu_abs (RM.MMU n)).state)
  /\ (mmu_req_rcvd MMU' = mmu_req_rcvd (RM.MMU n))
  /\ (mmu_abs MMU').active
  /\ ((mmu_abs MMU').cfg = (mmu_abs (RM.MMU n)).cfg)` by (
      METIS_TAC [mmu_final_rpl_lem]
  ) >>
  `  (cif'.req_rcvd = ((IM.G (PCG n)).cif (PCC n)).req_rcvd)
  /\ (cif'.rpl_rcvd = ((IM.G (PCG n)).cif (PCC n)).rpl_rcvd UNION {q})
  /\ (cif'.req_sent = ((IM.G (PCG n)).cif (PCC n)).req_sent DIFF {r'})` by (
      METIS_TAC [bif_rcv_rpl_lem]
  ) >>
  `(mem_abs m' = mem_abs RM.m) /\ 
   (mem_req_rcvd m' = 
        mem_req_rcvd RM.m DIFF {(Trreq (PCG n) r',CoreSender n)}) /\ 
   (mem_req_sent m' = mem_req_sent RM.m) /\ 
   (mem_rpl_rcvd m' = 
        mem_rpl_rcvd RM.m DIFF {Trrpl (PCG n) q,CoreSender n})` by (
      METIS_TAC [mem_io_fw_axiom, unique_match_thm] 
  ) >>
  `(mem_abs im' = mem_abs (IM.G (PCG n)).m) /\ 
   (mem_req_rcvd im' = 
        mem_req_rcvd (IM.G (PCG n)).m DIFF {(r',CoreSender (PCC n))}) /\ 
   (mem_req_sent im' = mem_req_sent (IM.G (PCG n)).m) /\ 
   (mem_rpl_rcvd im' = 
        mem_rpl_rcvd (IM.G (PCG n)).m DIFF {(q,CoreSender (PCC n))})` by (
      METIS_TAC [mem_io_fw_axiom, unique_match_thm] 
  ) >>
  (* show that syncInv still holds *)
  Q.ABBREV_TAC `IM'' = <|G := (PCG n =+ IM.G (PCG n) with
                       <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif; m := im'|>)
				  IM.G|>` >>
  `syncInv IM''` by ( 
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [] >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]          
  ) >> 
  (* show existence of refined computation *) 
  FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
  `refined_comp(RM,SUC 0, RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>)` by (
      METIS_TAC [refined_comp_def]
  ) >>
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC [] >>
  `~hv_guard_mmu_fault 
       (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n),n)` by (
      MATCH_MP_TAC hv_guard_mmu_fault_lem >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  `~hv_gicd_entry_state
       (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n))` by (
      MATCH_MP_TAC hv_gicd_entry_state_lem >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  IMP_RES_TAC hv_guard_mmu_fault_lem >>
  IMP_RES_TAC hv_gicd_entry_state_lem >>
  `!q' c. n <> c ==>
       (pend_rpl (mmu_rpl_rcvd (RM.MMU c),
		  mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
		  c,q') = 
	pend_rpl (mmu_rpl_rcvd (RM.MMU c),
		  mem_rpl_rcvd RM.m,
		  c,q'))` by (
      RW_TAC std_ss [pend_rpl_def, pred_setTheory.IN_DIFF] >>
      EQ_TAC
      >| [METIS_TAC []
	  ,
	  RW_TAC std_ss [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
	 ]
  ) >>
  `!q' c. c < RPAR.nc /\ (PCG n = PCG c) /\ n <> c ==>
       (id_pend_rpl(((IM.G (PCG c)).cif (PCC c)).rpl_rcvd,
		    mem_rpl_rcvd (IM.G (PCG c)).m DIFF {(q,CoreSender (PCC n))},
		    PCG c,PCC c,q') = 
	id_pend_rpl(((IM.G (PCG c)).cif (PCC c)).rpl_rcvd,
		    mem_rpl_rcvd (IM.G (PCG c)).m,
		    PCG c,PCC c,q'))` by (
      RW_TAC std_ss [id_pend_rpl_def, pred_setTheory.IN_DIFF] >>
      `PCC c <> PCC n` by ( METIS_TAC [PCG_PCC_inj] ) >>
      EQ_TAC
      >| [METIS_TAC []
	  ,
	  RW_TAC std_ss [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
	 ]
  ) >>
  `!id c. n <> c ==>
   (nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) (PIR id,c) = 
    nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m,
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) (PIR id,c))` by (
      RW_TAC std_ss [nuvi_def]
  ) >>
  `!id c. n <> c ==>
   (nuigc(RM.C c,mmu_rpl_rcvd (RM.MMU c),
	  mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
	  llr (mem_abs RM.m (ADRDS LLR)) c) (PIR id,c) = 
    nuigc(RM.C c,mmu_rpl_rcvd (RM.MMU c),
	  mem_rpl_rcvd RM.m,
	  llr (mem_abs RM.m (ADRDS LLR)) c) (PIR id,c))` by (
      RW_TAC std_ss [nuigc_def]
  ) >>
  `!id c c'. n <> c ==>
   (nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)},
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) 
	    (PSQ_inv (PCG c) (SGI (id,c',c)),c) = 
    nuvi(RM.C c,
	 mmu_rpl_rcvd (RM.MMU c),
	 mem_rpl_rcvd RM.m,
	 lirq (mem_abs RM.m (ADRDS LIRQ)) c) 
	    (PSQ_inv (PCG c) (SGI (id,c',c)),c))` by (
      RW_TAC std_ss [nuvi_def]
  ) >>
  (* show SIM *) 
  STRIP_TAC >- (
    Q.UNABBREV_TAC `IM''` >>
    FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
    REPEAT STRIP_TAC >> (
    EXCEPT_FOR ``bisim_send_igc _`` (
    FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
    (* try to solve straight-forward cases *)
    >> (REPEAT IF_CASES_TAC >>
        STRONG_FS_TAC ([]@bisim_core_definitions) >>
        `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
            FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
        ) >>
        TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
    		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
    		       hv_mmu_fault_entry_eq_lem,
    		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
    		       proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
    		       nuvi_def, nuigc_def, nusgi_def] ) )
    )
    ) >>
    (* send_igc *)
    FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
    `nusgi((\c. RM.C c),
    	 (\c. if n = c then 
    		  mmu_rpl_rcvd (RM.MMU c) UNION {Trrpl (PCG c) q}
    	      else 
    		  mmu_rpl_rcvd (RM.MMU c)),
    	 mem_rpl_rcvd RM.m DIFF {(Trrpl (PCG n) q,CoreSender n)}) = 
     nusgi((\c. RM.C c),
    	 (\c. mmu_rpl_rcvd (RM.MMU c)),
    	 mem_rpl_rcvd RM.m)` by (
        RW_TAC std_ss [FUN_EQ_THM] >>
        `?a b. x = (a,b)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
        Cases_on `a = n` >> (
            RW_TAC std_ss [nusgi_def, Mode_arith_lem]
        )
    ) >>
    METIS_TAC []				    
  ) >> 
  (* SimInvR *)
  FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
);

(* similar lemmas for SMMU *)

val invisible_smmu_lookup_lem = store_thm("invisible_smmu_lookup_lem", ``
!RM IM p r r' SMMU' m'. 
   p < RPAR.np
/\ InvR RM
/\ SIM (RM,IM)
/\ per_active (RM.P p).st
/\ ((mmu_abs (RM.SMMU p)).state r = TRANS NONE)
/\ ((mmu_abs SMMU').state r = TRANS (SOME r'))
/\ mmu_step_snd_req (RM.SMMU p,r',SMMU')
/\ mem_step_rcv_req (RM.m, r', PeripheralSender p, m')
==>
SIM(RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>,IM)
``,
  RW_TAC (srw_ss()) [] >>
  (* add some context *)
  `PPG p < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
  `(mmu_abs (RM.SMMU p)).active` by (
      IMP_RES_TAC smmu_per_active_lem 
  ) >>
  IMP_RES_TAC smmu_golden_conf_lem >>
  IMP_RES_TAC mmu_golden_lookup_axiom >>
  IMP_RES_TAC mem_rcv_req_axiom >>
  `(!r''. r <> r'' ==>
          ((mmu_abs SMMU').state r'' = (mmu_abs (RM.SMMU p)).state r'') 
       /\ (mmu_abs (RM.SMMU p)).state r'' <> TRANS (SOME r')
       /\ (mmu_abs (RM.SMMU p)).state r'' <> FINAL (SOME r') ) /\    
   (mmu_req_sent SMMU' = mmu_req_sent (RM.SMMU p) UNION {r'}) /\
   (mmu_req_rcvd SMMU' = mmu_req_rcvd (RM.SMMU p)) /\
   (mmu_rpl_rcvd SMMU' = mmu_rpl_rcvd (RM.SMMU p)) /\
   (mmu_ptl_hist SMMU' = mmu_ptl_hist (RM.SMMU p)) /\
   ((mmu_abs SMMU').active) /\
   ((mmu_abs SMMU').cfg = (mmu_abs (RM.SMMU p)).cfg)` by (
      METIS_TAC [mmu_send_axiom]
  ) >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem, 
		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem, 
		       hv_mmu_fault_entry_eq_lem,
		       PPT_Trreq_lem, pproj_bound_lem] ) ) 
  )
);

val invisible_smmu_lookup_rpl_lem = store_thm("invisible_smmu_lookup_rpl_lem", ``
!RM IM p r r' q SMMU' m'. 
   p < RPAR.np
/\ InvR RM
/\ SIM (RM,IM)
/\ per_active (RM.P p).st
/\ ((mmu_abs (RM.SMMU p)).state r = TRANS (SOME r'))
/\ match(r',q)
/\ mmu_step_rcv_rpl (RM.SMMU p, q, SMMU')
/\ mem_step_snd_rpl (RM.m, q, PeripheralSender p, m')
==>
SIM(RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>,IM)
``,
  RW_TAC (srw_ss()) [] >>
  (* add some context *)
  `PPG p < PAR.ng` by IMP_RES_TAC good_proj_axiom >>
  IMP_RES_TAC smmu_golden_conf_lem >>
  `PTreq r' /\ PAdr r' IN RPAR.A_PPT (PPG p)` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      IMP_RES_TAC ref_inv_hyp_iso_smmu_lookup_def >>
      RW_TAC (srw_ss()) []
  ) >>
  `Rpl_PAdr q IN RPAR.A_PPT (PPG p)` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `(q,PeripheralSender p) NOTIN mem_rpl_rcvd RM.m` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      IMP_RES_TAC mem_rpl_rcvd_lem >>
      METIS_TAC [PPT_gic_per_disj_lem]
  ) >>
  IMP_RES_TAC mem_walk_lem THEN
  `inv_good_mmu (RM.SMMU p)` by ( FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] ) >>
  IMP_RES_TAC mmu_lookup_rpl_lem >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
  REPEAT STRIP_TAC >>
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem, 
		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem, 
		       hv_mmu_fault_entry_eq_lem,
		       PPT_Trreq_lem, pproj_bound_lem] ) ) 
);


val golden_smmu_lookup_lem = store_thm("golden_smmu_lookup_lem", ``
!RM IM p r SMMU'.
   p < RPAR.np
/\ InvR RM
/\ SIM (RM,IM)
/\ per_active (RM.P p).st
/\ r IN mmu_req_rcvd (RM.SMMU p)
/\ mmu_golden_lookup (RM.SMMU p, r, GIP (PPG p), SMMU')
==> 
?m'.
   refined_comp (RM, 2, RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>)
/\ SIM (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>, IM)
/\ InvR (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>)
/\ r IN mmu_req_rcvd SMMU'
/\ (mem_abs m' = mem_abs RM.m)
``,
  REPEAT GEN_TAC >> 				  
  STRIP_TAC >> 
  `PPG p < PAR.ng` by IMP_RES_TAC good_proj_axiom >> 
  IMP_RES_TAC smmu_golden_conf_lem >>
  `(mmu_abs (RM.SMMU p)).active` by ( 
      FULL_SIMP_TAC (srw_ss()) [mmu_golden_conf_def] 
  ) >>
  FULL_SIMP_TAC (srw_ss()) [mmu_golden_lookup_def] >> 
  (* send step is computation *)
  `?m''. mem_step_rcv_req(RM.m,r',PeripheralSender p,m'')` by (
      FULL_SIMP_TAC (srw_ss()) [mem_rcv_req_enabled_axiom]
  ) >>
  `refined_trans(RM, SMMU_SND_DMAREQ p, 
		 RM with <|m := m''; SMMU := (p =+ MMU'') RM.SMMU|>)` by (
      FULL_SIMP_TAC (srw_ss()) [refined_trans_def, ref_rule_smmu_snd_dmareq_def, 
				mmu_step_def, mem_step_def] >>
      METIS_TAC [] 
  ) >>
  `refined_comp (RM, SUC 0, RM with <|m := m''; SMMU := (p =+ MMU'') RM.SMMU|>)` 
  by ( 
      METIS_TAC [refined_comp_def]
  ) >>
  IMP_RES_TAC refined_trans_InvR_lem >>
  (* reply can be sent by memory *)
  `?m'. mem_step_snd_rpl(m'', q, PeripheralSender p,m')` by (
      MATCH_MP_TAC mem_snd_rpl_enabled_axiom >>
      HINT_EXISTS_TAC >> 
      RW_TAC (srw_ss()) [] 
      >- ( 
          IMP_RES_TAC mem_rcv_req_axiom >>
	  FULL_SIMP_TAC (srw_ss()) []
      ) >> 
      (* impossible cases *)
      TRY (
          IMP_RES_TAC mmu_golden_lookup_axiom >> 
	  IMP_RES_TAC PPT_gic_per_disj_lem >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  TRY ( METIS_TAC [Rreq_not_PTreq_lem] ) >>
	  NO_TAC
      ) >> 
      (* show that value is from golden image *)
      `(?c'. c' < RPAR.nc /\ (PCG c' = PPG p) /\ (PCC c' = 0) 
          /\ (refcore_abs (RM.C c')).H.init_guest)` by (
	  METIS_TAC [per_active_init_guest_lem]
      ) >>
      IMP_RES_TAC mmu_golden_lookup_axiom >>
      RW_TAC (srw_ss()) [PTreq_Sz_lem] >>
      IMP_RES_TAC match_Adr_eq_lem >>
      RW_TAC (srw_ss()) [mem_read_def] >>
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      IMP_RES_TAC ref_inv_ppt_def >>
      FULL_SIMP_TAC (srw_ss()) [] >> 
      METIS_TAC [PAdr_def, Adr_def]
  ) >>
  (* second refined step is possible *)
  `refined_trans(RM with <| m := m''; SMMU := (p =+ MMU'') RM.SMMU|>, SMMU_RCV_DMARPL p, RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>)` by (
      IMP_RES_TAC mmu_send_axiom >>
      FULL_SIMP_TAC (srw_ss()++normalForms.cond_lift_SS) [refined_trans_def, ref_rule_smmu_rcv_dmarpl_def, mmu_step_def, mem_step_def, pred_setTheory.UNION_DEF, combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ] >>
      METIS_TAC [] 
  ) >>
  (* solving first goal: computation exists *)
  IMP_RES_TAC refined_trans_InvR_lem >>
  `refined_comp (RM, SUC (SUC 0), RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>)` by (
      IMP_RES_TAC refined_comp_def >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  FULL_SIMP_TAC arith_ss [] >>
  HINT_EXISTS_TAC >>
  RW_TAC (srw_ss()) [] >- (
  (* show that simulation is preserved, need two lemmas *)
  (* step 1: *)
  Q.ABBREV_TAC `RM'' = RM with <|m := m''; SMMU := (p =+ MMU'') RM.SMMU|>` >> 
  `SIM(RM'',IM)` by ( 
      Q.UNABBREV_TAC `RM''` >>
      IMP_RES_TAC (invisible_smmu_lookup_lem |> SPEC ``RM:refined_model``)
  ) >>
  (* step 2: *)
  `SIM (RM'' with <|m := m'; SMMU := (p =+ SMMU') RM''.SMMU|>,IM)` by (
      `per_active (RM''.P p).st /\ (RM''.SMMU p = MMU'') /\ (RM''.m = m'')` by (
          Q.UNABBREV_TAC `RM''` >> 
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      RW_TAC (srw_ss()) [] >>
      IMP_RES_TAC (invisible_smmu_lookup_rpl_lem |> SPEC ``RM'':refined_model``) 
  ) >>
  Q.UNABBREV_TAC `RM''` >>
  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ]
  ) >- ( 
  (* r IN mmu_req_rcvd MMU' *)
  `r IN mmu_req_rcvd MMU''` by (
      IMP_RES_TAC mmu_send_axiom >> (
          FULL_SIMP_TAC (srw_ss()) []
      )
  ) >>
  IMP_RES_TAC mmu_memrpl_axiom >>
  FULL_SIMP_TAC (srw_ss()) []
  ) >>
  (* mem_abs unchanged *)
  Q.ABBREV_TAC `RM'' = RM with <|m := m''; SMMU := (p =+ MMU'') RM.SMMU|>` >> 
  `PTreq r' /\ PAdr r' IN RPAR.A_PPT (PPG p)` by (
      `ref_inv_hyp_iso_smmu_lookup RM''` by (
          FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
      ) >>
      Q.UNABBREV_TAC `RM''` >>			
      IMP_RES_TAC ref_inv_hyp_iso_smmu_lookup_def >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC []
  ) >>
  `Rpl_PAdr q IN RPAR.A_PPT (PPG p)` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `(q,PeripheralSender p) NOTIN mem_rpl_rcvd m''` by (
      CCONTR_TAC >>
      Q.UNABBREV_TAC `RM''` >>					
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      IMP_RES_TAC mem_rpl_rcvd_lem >>
      METIS_TAC [PPT_gic_per_disj_lem]
  ) >> 
  `mem_abs m' = mem_abs m''` by (
      METIS_TAC [mem_walk_lem]
  ) >>
  `mem_abs m'' = mem_abs RM.m` by (
      METIS_TAC [mem_rcv_req_axiom]
  ) >> 
  METIS_TAC []
);


val golden_smmu_comp_lem = store_thm("golden_smmu_comp_lem", ``
!RM IM p r n SMMU'.
   p < RPAR.np
/\ InvR RM
/\ SIM (RM,IM)
/\ per_active (RM.P p).st
/\ r IN mmu_req_rcvd (RM.SMMU p)
/\ mmu_golden_comp (RM.SMMU p, r, GIP (PPG p), SMMU', n)
==> 
?m'.
   refined_comp (RM, 2*n, RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>)
/\ SIM (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>, IM)
/\ InvR (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>)
/\ per_active ((RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>).P p).st 
/\ r IN mmu_req_rcvd ((RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>).SMMU p)
/\ (mem_abs m' = mem_abs RM.m)
``,
  Induct_on `n`
  >|  [(* Induction Start *)
       RW_TAC (srw_ss()) [mmu_golden_comp_def] >> 
       FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_ID] >>
       EXISTS_TAC ``RM.m:memory`` >>
       `RM with <|m := RM.m; SMMU := RM.SMMU|> = RM` by (
	   RW_TAC (srw_ss()) [refined_model_component_equality]
       ) >> 
       RW_TAC (srw_ss()) [refined_comp_def] 
       , 
       (* Induction Step *)
       RW_TAC (srw_ss()) [mmu_golden_comp_def] >>
       PAT_X_ASSUM ``!rm im p r smmu'. x`` 
           (fn thm => MP_TAC (SPECL [``RM:refined_model``,
				     ``IM:ideal_model``,
				     ``p:num``,
				     ``r:request``,
				     ``MMU'':mmu``] thm)) >>
       RW_TAC (srw_ss()) [] >>
       FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
       Q.ABBREV_TAC `RM'' = RM with <|m := m'; SMMU := (p =+ MMU'') RM.SMMU|>` >>
       `r IN mmu_req_rcvd (RM''.SMMU p) /\ per_active(RM''.P p).st /\ mmu_golden_lookup (RM''.SMMU p,r,GIP (PPG p),SMMU')` by (
           Q.UNABBREV_TAC `RM''` >>
	   FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
       ) >>
       `?m''. refined_comp (RM'',2, 
			 RM'' with <|m := m''; SMMU := (p =+ SMMU') RM''.SMMU|>) 
	   /\ SIM (RM'' with <|m := m''; SMMU := (p =+ SMMU') RM''.SMMU|>,IM)
	   /\ InvR (RM'' with <|m := m''; SMMU := (p =+ SMMU') RM''.SMMU|>)
	   /\ r IN mmu_req_rcvd SMMU'
           /\ (mem_abs m'' = mem_abs RM''.m)` by (
	   IMP_RES_TAC golden_smmu_lookup_lem >>
	   METIS_TAC []
       ) >>
       IMP_RES_TAC refined_comp_concat_lem >>
       `2 * SUC n = 2 * n + 2` by (
           RW_TAC arith_ss []
       ) >>
       Q.UNABBREV_TAC `RM''` >>
       RW_TAC (srw_ss()) [] >> 
       FULL_SIMP_TAC (srw_ss()) [combinTheory.UPDATE_EQ] >>
       HINT_EXISTS_TAC >>
       RW_TAC (srw_ss()) []
      ]
);

val smmu_Trreq_aligned_lem = store_thm("smmu_Trreq_aligned_lem", ``
!RM r g p.
   InvR RM
/\ g < PAR.ng
/\ p < RPAR.np
/\ Trreq g r IN mmu_req_sent (RM.SMMU p)
==>
req_aligned r
``,
  REPEAT STRIP_TAC >>
  `req_aligned (Trreq g r)` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      METIS_TAC [inv_good_mmu_def]
  ) >>
  IMP_RES_TAC Trreq_aligned_lem
);

val golden_smmu_Trreq_lem = store_thm("golden_mmu_Trreq_lem", ``
!RM p r r' SMMU'.
   p < RPAR.np
/\ InvR RM
/\ (mmu_abs (RM.SMMU p)).active
/\ mmu_step_snd_req (RM.SMMU p, r,SMMU')
/\ ((mmu_abs (RM.SMMU p)).state r' = FINAL NONE)
/\ ((mmu_abs SMMU').state r' = FINAL (SOME r))
==>
(r = Trreq (PPG p) r') /\ IS_SOME (Trans (PPG p) (PAdr r'))
``,
  REPEAT GEN_TAC >> STRIP_TAC >>
  `r' IN mmu_req_rcvd (RM.SMMU p)` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      RES_TAC >>
      METIS_TAC [inv_good_mmu_def, MMUstate_distinct]
  ) >>
  `per_active (RM.P p).st` by ( IMP_RES_TAC per_active_req_lem ) >>
  IMP_RES_TAC smmu_golden_conf_lem >>
  IMP_RES_TAC mmu_golden_final_axiom >>
  IMP_RES_TAC pproj_bound_lem >>
  IMP_RES_TAC Trgip_Trans_lem >>
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC (srw_ss()) [Trreq_xlated_Trans_lem, PAdr_def, PAdr_extract_lem] >>
  IMP_RES_TAC mmu_send_axiom >> (
      REV_FULL_SIMP_TAC std_ss [] >>
      `r' = r''` by (
          CCONTR_TAC >>
          METIS_TAC []
      ) >>
      METIS_TAC [MMUstate_distinct]
  )
);

val final_smmu_rpl_lem = store_thm("final_smmu_rpl_lem", ``
!RM IM n r' q SMMU' m' pif' im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.np
/\ mmu_step_rcv_rpl (RM.SMMU n,Trrpl (PPG n) q,SMMU')
/\ mem_step_snd_rpl (RM.m,Trrpl (PPG n) q,PeripheralSender n,m')
/\ Trreq (PPG n) r' IN mmu_req_sent (RM.SMMU n)
/\ match (Trreq (PPG n) r',Trrpl (PPG n) q)
/\ ((mmu_abs (RM.SMMU n)).state r' = FINAL (SOME (Trreq (PPG n) r')))
(* /\ r' IN mmu_req_rcvd (RM.SMMU n) *)
/\ per_active (RM.P n).st
(* /\ r' IN ((IM.G (PPG n)).pif (PPP n)).req_rcvd *)
/\ IS_SOME (Trans (PPG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PPG n)
/\ PAdr r' NOTIN A_gicper
/\ r' IN ((IM.G (PPG n)).pif (PPP n)).req_sent
(* /\ (Trreq (PPG n) r',PeripheralSender n) IN mem_req_rcvd RM.m *)
(* /\ (r',PeripheralSender (PPP n)) IN mem_req_rcvd (IM.G (PPG n)).m *)
/\ mem_step_snd_rpl ((IM.G (PPG n)).m,q,PeripheralSender (PPP n), im')
/\ match (r',q)
/\ IS_SOME (Trans (PPG n) (Rpl_PAdr q))
/\ bif_step_rcv_rpl ((IM.G (PPG n)).pif (PPP n),q,pif')
==>
?n' IM'.
  ideal_model_comp (IM,n',IM') /\
  SIM (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>,IM')
``,
  REPEAT STRIP_TAC >>
  (* start with computation part *)
  IMP_RES_TAC pproj_bound_lem >>
  `?G'. id_rule_pif_rcv_dmarpl(IM.G (PPG n), PPP n, G') 
     /\ (G' = (IM.G (PPG n)) with 
              <|m := im'; pif := (PPP n =+ pif') ((IM.G (PPG n)).pif)|>)` by (
      RW_TAC (srw_ss()) [id_rule_pif_rcv_dmarpl_def, 
			 mem_step_def, bif_step_def] >>
      METIS_TAC []
  ) >>
  `?IM'. ideal_guest_trans(IM.G (PPG n), PPG n, 
			   INTERNAL (IR_PIF_RCV_DMARPL (PPP n)), G')
         /\ (IM' = IM with G := (PPG n =+ G') IM.G)` by (
      RW_TAC (srw_ss()) [ideal_guest_trans_def] 
  ) >>
  (* add some context *)
  RW_TAC (srw_ss()) [] >>
  `(q,PeripheralSender (PPP n)) NOTIN mem_rpl_rcvd ((IM.G (PPG n)).m)` by (
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `(Trrpl (PPG n) q,PeripheralSender n) NOTIN mem_rpl_rcvd (RM.m)` by (
      IMP_RES_TAC not_A_gicper_Trreq_lem >>
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `req_aligned r'` by ( IMP_RES_TAC smmu_Trreq_aligned_lem ) >>
  `inv_good_mem (IM.G (PPG n)).m` by (
     FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``PPG n``]
  ) >>
  `good_rpl q` by ( IMP_RES_TAC good_mem_rpl_axiom ) >>
  `inv_good_mmu (RM.SMMU n)` by (
     FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
  ) >>
  `(mmu_abs (RM.SMMU n)).active` by (
      IMP_RES_TAC smmu_per_active_lem
  ) >>
  `  (mmu_rpl_rcvd SMMU' = mmu_rpl_rcvd (RM.SMMU n) UNION {Trrpl (PPG n) q})
  /\ (mmu_req_sent SMMU' = mmu_req_sent (RM.SMMU n) DIFF {Trreq (PPG n) r'})
  /\ (mmu_ptl_hist SMMU' = mmu_ptl_hist (RM.SMMU n))
  /\ ((mmu_abs SMMU').state = (mmu_abs (RM.SMMU n)).state)
  /\ (mmu_req_rcvd SMMU' = mmu_req_rcvd (RM.SMMU n))
  /\ (mmu_abs SMMU').active
  /\ ((mmu_abs SMMU').cfg = (mmu_abs (RM.SMMU n)).cfg)` by (
      METIS_TAC [mmu_final_rpl_lem]
  ) >>
  `  (pif'.req_rcvd = ((IM.G (PPG n)).pif (PPP n)).req_rcvd)
  /\ (pif'.rpl_rcvd = ((IM.G (PPG n)).pif (PPP n)).rpl_rcvd UNION {q})
  /\ (pif'.req_sent = ((IM.G (PPG n)).pif (PPP n)).req_sent DIFF {r'})` by (
      METIS_TAC [bif_rcv_rpl_lem]
  ) >>
  IMP_RES_TAC guest_Trreq_lem >>
  IMP_RES_TAC HV_guest_disj_lem >> 
  `req_aligned (Trreq (PPG n) r')` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
	  METIS_TAC [inv_good_mmu_def]
  ) >>
  `!a. a IN RPAR.Amap HV ==> (mem_abs m' a = mem_abs RM.m a)` by (
      IMP_RES_TAC mem_unchanged_lem 
  ) >>
  IMP_RES_TAC hvds_unchanged_lem >>
  `!g r. g < PAR.ng ==> 
         (gcpys (mem_abs m' (ADRDS (GCPY g))) (g,r) =
          gcpys (mem_abs RM.m (ADRDS (GCPY g))) (g,r))` by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  IMP_RES_TAC mem_snd_rpl_merged_lem >>
  (* case split depending on write to A_IGCout *)
  Cases_on `(PAdr r' NOTIN A_IGCin (PPG n) /\ (PAdr r' NOTIN A_IGCout (PPG n)) 
	    \/ ~Wreq r')`
  >| [(* show that syncInv still holds *)
      Q.ABBREV_TAC `IM' = IM with G := (PPG n =+ (IM.G (PPG n) with
          <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)) IM.G` >>
      `syncInv IM'` by ( 
	  METIS_TAC [pif_no_igc_write_sync_lem] 
      ) >> 
      Q.ABBREV_TAC `not_write_or_igc =
      	(PAdr r' NOTIN A_IGCin (PPG n) /\ (PAdr r' NOTIN A_IGCout (PPG n))
      	    \/ ~Wreq r')` >>
      (* show existence of ideal computation *) 
      `sync_shared_mem_upd_of_guest (IM', PPG n, IM')` by (
          RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
      ) >>
      `comp_rule_internal(IM,IM')`  by ( 
	  METIS_TAC [comp_rule_internal_def]
      ) >> 
      `comp_rule_internal(IM,IM')`  by ( 
	  METIS_TAC [comp_rule_internal_def]
      ) >> 
      `ideal_model_trans (IM, C_INTERNAL, IM')` by (
          RW_TAC (srw_ss()) [ideal_model_trans_def]
      ) >>
      `ideal_model_comp (IM, SUC 0, IM')` by (
          METIS_TAC [ideal_model_comp_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [] >>
      (* show that memory is still in simulation *)
      `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
             (mem_abs((IM'.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
          REPEAT STRIP_TAC >>
	  Cases_on `g = PPG n` 
	  >| [`(IM'.G g).m = im'` by (
	          Q.UNABBREV_TAC `IM'` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      METIS_TAC [mem_access_bisim_lem]
	      ,
	      `(IM'.G g).m = (IM.G g).m` by (
	          Q.UNABBREV_TAC `IM'` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
              METIS_TAC [no_igc_write_mem_upd_others_lem]
	     ]
      ) >>
      (* show SIM *) 
      Q.UNABBREV_TAC `IM'` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >>
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `RM.C c = (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	  ) >>
      	  TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      			   hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			   hv_mmu_fault_entry_eq_lem,
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   pproj_bound_lem] ) )
      ,
      (* case: write to IGC memory *)
      FULL_SIMP_TAC (srw_ss()) []
      >| [(* case: write to A_IGCin -> not possible *)
	  FULL_SIMP_TAC (srw_ss()) [A_IGCin_def, InvR_EXPAND] >>
	  IMP_RES_TAC ref_inv_hyp_iso_smmu_final_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  METIS_TAC []
	  ,
	  (* case: write to A_IGCout -> prove additional sync *)
	  Q.ABBREV_TAC `IM' = IM with G := (PPG n =+ (IM.G (PPG n) with
              <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)) IM.G` >>
	  `?s g2 a2. 
	      s < PAR.ns
	   /\ g2 < PAR.ng
	   /\ (PAR.cpol s = (PPG n,g2))
	   /\ (PAR.igca s = (PAdr r',a2))
	   /\ do_sync_shared_mem_upd_of_guest(IM',PPG n,
		IM' with <|G := (g2 =+ 
	(IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G (PPG n)).m (PAdr r')) 
					 (IM'.G g2).m|>) ) IM'.G|>)` by (
	      METIS_TAC [pif_igc_write_sync_lem] 
	  ) >>
	  Q.ABBREV_TAC `IM'' = IM' with <|G := (g2 =+ 
	(IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G (PPG n)).m (PAdr r')) 
					 (IM'.G g2).m|>) ) IM'.G|>` >>
	  (* show existence of computation *)
	  `PPG n <> g2` by (
	      CCONTR_TAC >>
	      FULL_SIMP_TAC std_ss [] >>
	      RW_TAC std_ss [] >> 
	      METIS_TAC [goodP_axiom]
	  ) >>
	  `sync_shared_mem_upd_of_guest (IM',PPG n,IM'')` by (
	      Cases_on `syncInv IM'`
	      >| [(* case: memory update with same value *) 
		  `mem_abs (IM'.G (PPG n)).m (PAdr r') = 
	           mem_abs (IM'.G g2).m a2` by (
		      METIS_TAC [syncInv_def]
		  ) >>
		  `IM'' = IM'` by (
		      Q.UNABBREV_TAC `IM''` >>
		      ASM_REWRITE_TAC [] >>
		      RW_TAC (srw_ss()) [memory_id_upd_axiom, 
					 combinTheory.APPLY_UPDATE_ID,
					 GSYM guest_trivial_upd_m_lem,		  
					 SYM ideal_model_just_guests_lem]
		  ) >>
		  RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
		  ,
		  (* case: unartificial update *)
		  RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
		 ]
	  ) >>
	  `comp_rule_internal(IM,IM'')`  by ( 
	      METIS_TAC [comp_rule_internal_def]
	  ) >> 
	  `ideal_model_trans (IM, C_INTERNAL, IM'')` by (
              RW_TAC (srw_ss()) [ideal_model_trans_def]
	  ) >>
	  `ideal_model_comp (IM, SUC 0, IM'')` by (
              METIS_TAC [ideal_model_comp_def]
	  ) >>
	  EXISTS_TAC ``SUC 0`` >>
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [] >>
	  (* add context about write *)
	  `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
		(mem_abs((IM''.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
              REPEAT STRIP_TAC >>
	      Cases_on `g = PPG n` 
	      >| [(* case: PPG n *) 
	          `(IM''.G g).m = (IM'.G g).m` by (
	              Q.UNABBREV_TAC `IM''` >>
		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		  ) >>
	          `(IM'.G g).m = im'` by (
	              Q.UNABBREV_TAC `IM'` >>
		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		  ) >>
		  ASM_REWRITE_TAC [] >>
		  METIS_TAC [mem_access_bisim_lem]
		  ,
		  Cases_on `g = g2`
		  >| [(* case: g2 *)
		      Cases_on `a = a2`
		      >| [(* updated page *)
		          Q.UNABBREV_TAC `IM''` >>
		          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM,
					     memory_upd_mem_abs_id_lem] >>
			  `Trans g a = Trans (PPG n) (PAdr r')` by (
			      METIS_TAC [Trans_axiom,
					 pairTheory.FST, pairTheory.SND]
			  ) >>
			  `(IM'.G (PPG n)).m = im'` by (
			      Q.UNABBREV_TAC `IM'` >>
			      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
			  ) >>
			  ASM_REWRITE_TAC [] >>
			  METIS_TAC [mem_access_bisim_lem]
			  ,
			  (* other pages *)
		          Q.UNABBREV_TAC `IM''` >>
		          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
			  `mem_abs (memory_upd (a2,
				mem_abs (IM'.G (PPG n)).m (PAdr r'))
					       (IM'.G g).m) a = 
		           mem_abs (IM'.G g).m a` by (
			      METIS_TAC [memory_upd_axiom] 
			  ) >>
			  `(IM'.G g).m = (IM.G g).m` by (
			      Q.UNABBREV_TAC `IM'` >>
			      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
			  ) >>
			  ASM_REWRITE_TAC [] >>
			  METIS_TAC [igc_write_mem_upd_others_lem]
			 ]
		      ,
		      (* all other unaffected guests *)
		      `(IM''.G g).m = (IM'.G g).m` by (
		          Q.UNABBREV_TAC `IM''` >>
			  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		      ) >>
		      `(IM'.G g).m = (IM.G g).m` by (
		          Q.UNABBREV_TAC `IM'` >>
			  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		      ) >>
		      ASM_REWRITE_TAC [] >>
		      METIS_TAC [igc_write_mem_upd_others_lem]
		     ]
		 ]
	  ) >>
	  `!g. g < PAR.ng ==>
	       (mem_req_rcvd (IM''.G g).m = mem_req_rcvd (IM'.G g).m)
	    /\ (mem_req_sent (IM''.G g).m = mem_req_sent (IM'.G g).m)
	    /\ (mem_rpl_rcvd (IM''.G g).m = mem_rpl_rcvd (IM'.G g).m)` by (
	      STRIP_TAC >> STRIP_TAC >> Cases_on `g = g2`
	      >| [Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
		      METIS_TAC [memory_upd_axiom]
		  )
		  ,
		  Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
		 ]
	  ) >>
	  `!g. g < PAR.ng ==>
	       ((IM''.G g).pif = (IM'.G g).pif)` by (
	      STRIP_TAC >> STRIP_TAC >>
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  (* prove SIM *)
	  Q.UNABBREV_TAC `IM'` >>
	  Q.UNABBREV_TAC `IM''` >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  REPEAT STRIP_TAC >>
	  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	  (* try to solve straight-forward cases *)
	  >> (REPEAT IF_CASES_TAC >>
	      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	      `RM.C c = (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>).C c` 
	      by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
      	      TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       pproj_bound_lem] ) )
	 ]
     ]
);


val do_sync_igc_smmu_write_lem = store_thm("do_sync_igc_smmu_write_lem", ``
!IM IM' IM'' n r' q pif' im' s ra rg.
   InvI IM
/\ rg < PAR.ng
/\ n < RPAR.np
/\ req_aligned r'
/\ match (r',q)
/\ s < PAR.ns
/\ (PAR.igca s = (PAdr r',ra))
/\ (PAR.cpol s = (PPG n,rg))
/\ rg <> PPG n
/\ (q,PeripheralSender (PPP n)) NOTIN mem_rpl_rcvd (IM.G (PPG n)).m
/\ mem_step_snd_rpl ((IM.G (PPG n)).m,q,PeripheralSender (PPP n), im')
/\ do_sync_shared_mem_upd_of_guest (IM'',PPG n,IM')
/\ Abbrev (IM'' = <|G := (PPG n =+ IM.G (PPG n) with
                      <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)
                          IM.G|>)
==>
   (IM'.G (PPG n) = IM.G (PPG n) with 
                        <|m := im';
			  pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)
/\ (IM'.G rg = IM.G rg with 
        m := memory_upd (ra, mem_abs im' (PAdr r')) (IM.G rg).m)
/\ (!g. g < PAR.ng /\ g <> PPG n /\ g <> rg ==> (IM'.G g = IM.G g))  
``,
  REPEAT STRIP_TAC
  >| [(* PGC n *)
      `~(?s. s < PAR.ns /\ (PAR.cpol s = (PPG n,PPG n)))` by (
           METIS_TAC [goodP_axiom]
      ) >>
      `(IM'.G (PPG n)).m = (IM''.G (PPG n)).m` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      `IM'.G (PPG n) = IM''.G (PPG n)` suffices_by (
          Q.UNABBREV_TAC `IM''` >>
          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `?x. IM'.G (PPG n) = IM''.G (PPG n) with m := x` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      RW_TAC std_ss [guest_component_equality]
      ,
      (* receiving guest *)
      `(IM'.G rg).m = memory_upd 
                          (ra, mem_abs (IM''.G (PPG n)).m (PAdr r')) 
		          (IM''.G rg).m` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      `IM.G rg = IM''.G rg` by (
          Q.UNABBREV_TAC `IM''` >>
          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>
      ASM_REWRITE_TAC [] >>
      `?x. IM'.G rg = IM''.G rg with m := x` by (
          METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
      ) >>
      RW_TAC std_ss [guest_component_equality] >>
      `(IM''.G (PPG n)).m = im'` by (
          Q.UNABBREV_TAC `IM''` >>
          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>   
      ASM_REWRITE_TAC []
      ,
      (* any other guest *)
      `IM.G g = IM''.G g` by (
          Q.UNABBREV_TAC `IM''` >>
	  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ) >>   
      ASM_REWRITE_TAC [] >>
      `PPG n < PAR.ng` by ( METIS_TAC [good_proj_in_range_impls] ) >>
      Cases_on `?s. s < PAR.ns /\ (PAR.cpol s = (PPG n,g))`
      >| [(* exists channel -> identical update *)
	  FULL_SIMP_TAC std_ss [] >>
          `?sa ga. PAR.igca s' = (sa,ga)` by (
	      METIS_TAC [pairTheory.pair_CASES]
	  ) >>
	  `(IM'.G g).m = memory_upd 
                         (ga, mem_abs (IM''.G (PPG n)).m sa) 
		         (IM''.G g).m` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
	  ) >>
	  `s' <> s` by (
	       CCONTR_TAC >>
	       FULL_SIMP_TAC std_ss []
	  ) >>
	  `sa <> PAdr r'` by ( 
	       METIS_TAC [goodP_axiom, pairTheory.FST] 
	  ) >>
	  `mem_abs (IM''.G (PPG n)).m sa = mem_abs (IM''.G g).m ga` by (
	      `mem_abs (IM''.G (PPG n)).m sa = 
	       mem_abs (IM.G g).m ga` suffices_by (
	          RW_TAC std_ss []
	      ) >>
	      IMP_RES_TAC InvI_def >>
	      `mem_abs (IM''.G (PPG n)).m sa = 
	       mem_abs (IM.G (PPG n)).m sa` suffices_by (
	          STRIP_TAC >>
		  THROW_AWAY_TAC ``IM.G g = IM''.G g`` >>
		  ASM_REWRITE_TAC [] >>
		  IMP_RES_TAC syncInv_def >>
		  ASM_REWRITE_TAC []
	      ) >>
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      METIS_TAC [mem_aligned_unchanged_lem]
	  ) >>
	  FULL_SIMP_TAC std_ss [memory_id_upd_axiom] >>
          `?x. IM'.G g = IM''.G g with m := x` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
          ) >>
          RW_TAC std_ss [guest_component_equality]
	  ,
	  (* no output channel *)
	  `(IM'.G g).m = (IM''.G g).m` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
	  ) >>
          `?x. IM'.G g = IM''.G g with m := x` by (
              METIS_TAC [do_sync_shared_mem_upd_of_guest_def]
          ) >>
          RW_TAC std_ss [guest_component_equality]
	 ]
     ]
);

val id_final_smmu_rpl_lem = store_thm("id_final_smmu_rpl_lem", ``
!RM IM IM' n r' q SMMU' m' pif' im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ SimInvR RM
/\ n < RPAR.np
/\ mmu_step_rcv_rpl (RM.SMMU n,Trrpl (PPG n) q,SMMU')
/\ mem_step_snd_rpl (RM.m,Trrpl (PPG n) q,PeripheralSender n,m')
/\ Trreq (PPG n) r' IN mmu_req_sent (RM.SMMU n)
/\ match (Trreq (PPG n) r',Trrpl (PPG n) q)
/\ (mmu_abs (RM.SMMU n)).active
/\ ((mmu_abs (RM.SMMU n)).state r' = FINAL (SOME (Trreq (PPG n) r')))
/\ IS_SOME (Trans (PPG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PPG n)
/\ PAdr r' NOTIN A_gicper
/\ r' IN ((IM.G (PPG n)).pif (PPP n)).req_sent
/\ mem_step_snd_rpl ((IM.G (PPG n)).m,q,PeripheralSender (PPP n), im')
/\ match (r',q)
/\ IS_SOME (Trans (PPG n) (Rpl_PAdr q))
/\ bif_step_rcv_rpl ((IM.G (PPG n)).pif (PPP n),q,pif')
/\ sync_shared_mem_upd_of_guest
       (<|G := 
	    (PPG n =+ IM.G (PPG n) with
                 <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)
                IM.G|>,PPG n,IM')
==>
?n' RM'.
  refined_comp (RM,n',RM') /\
  SIM (RM',IM') /\
  SimInvR RM'
``,
  REPEAT STRIP_TAC >>
  (* start with computation part *)
  IMP_RES_TAC pproj_bound_lem >>
  `ref_rule_smmu_rcv_dmarpl(RM, n, 
       RM with <|SMMU := (n =+ SMMU') RM.SMMU; m := m'|>)` by (
      RW_TAC (srw_ss()) [ref_rule_smmu_rcv_dmarpl_def, 
			 mem_step_def, mmu_step_def] >>
      METIS_TAC []
  ) >>
  `refined_trans(RM, SMMU_RCV_DMARPL n, RM with <|SMMU := (n =+ SMMU') RM.SMMU; 
					          m := m'|>)` by (
      RW_TAC (srw_ss()) [refined_trans_def] 
  ) >>
  (* add some context *)
  `(q,PeripheralSender (PPP n)) NOTIN mem_rpl_rcvd ((IM.G (PPG n)).m)` by (
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `(Trrpl (PPG n) q,PeripheralSender n) NOTIN mem_rpl_rcvd (RM.m)` by (
      IMP_RES_TAC not_A_gicper_Trreq_lem >>
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [mem_no_fw_lem]
  ) >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `req_aligned r'` by ( IMP_RES_TAC smmu_Trreq_aligned_lem ) >>
  `inv_good_mem (IM.G (PPG n)).m` by (
     FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``PPG n``]
  ) >>
  `good_rpl q` by ( IMP_RES_TAC good_mem_rpl_axiom ) >>
  `inv_good_mmu (RM.SMMU n)` by (
     FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND]
  ) >>
  `  (mmu_rpl_rcvd SMMU' = mmu_rpl_rcvd (RM.SMMU n) UNION {Trrpl (PPG n) q})
  /\ (mmu_req_sent SMMU' = mmu_req_sent (RM.SMMU n) DIFF {Trreq (PPG n) r'})
  /\ (mmu_ptl_hist SMMU' = mmu_ptl_hist (RM.SMMU n))
  /\ ((mmu_abs SMMU').state = (mmu_abs (RM.SMMU n)).state)
  /\ (mmu_req_rcvd SMMU' = mmu_req_rcvd (RM.SMMU n))
  /\ (mmu_abs SMMU').active
  /\ ((mmu_abs SMMU').cfg = (mmu_abs (RM.SMMU n)).cfg)` by (
      METIS_TAC [mmu_final_rpl_lem]
  ) >>
  `  (pif'.req_rcvd = ((IM.G (PPG n)).pif (PPP n)).req_rcvd)
  /\ (pif'.rpl_rcvd = ((IM.G (PPG n)).pif (PPP n)).rpl_rcvd UNION {q})
  /\ (pif'.req_sent = ((IM.G (PPG n)).pif (PPP n)).req_sent DIFF {r'})` by (
      METIS_TAC [bif_rcv_rpl_lem]
  ) >>
  IMP_RES_TAC guest_Trreq_lem >>
  IMP_RES_TAC HV_guest_disj_lem >> 
  `req_aligned (Trreq (PPG n) r')` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
	  METIS_TAC [inv_good_mmu_def]
  ) >>
  `!a. a IN RPAR.Amap HV ==> (mem_abs m' a = mem_abs RM.m a)` by (
      IMP_RES_TAC mem_unchanged_lem 
  ) >>
  IMP_RES_TAC hvds_unchanged_lem >>
  `!g r. g < PAR.ng ==> 
         (gcpys (mem_abs m' (ADRDS (GCPY g))) (g,r) =
          gcpys (mem_abs RM.m (ADRDS (GCPY g))) (g,r))` by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  `!c b. c < RPAR.nc ==> (
	     ctxs (mem_abs m' (ADRDS (CTX c))) (b,c) =
             ctxs (mem_abs RM.m (ADRDS (CTX c))) (b,c))`  by (
      METIS_TAC [hvds_unchanged_lem]
  ) >>
  IMP_RES_TAC mem_snd_rpl_merged_lem >>
  (* case split depending on write to A_IGCout *)
  Cases_on `(PAdr r' NOTIN A_IGCin (PPG n) /\ (PAdr r' NOTIN A_IGCout (PPG n)) 
	    \/ ~Wreq r')`
  >| [(* show that syncInv still holds *)
      Q.ABBREV_TAC `IM'' = <|G := (PPG n =+ IM.G (PPG n) with
                    <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)
				  IM.G|>` >>
      `syncInv IM''` by ( 
	  MATCH_MP_TAC pif_no_igc_write_sync_lem >>
	  HINT_EXISTS_TAC >>
	  HINT_EXISTS_TAC >>
	  HINT_EXISTS_TAC >>
	  HINT_EXISTS_TAC >>
	  EXISTS_TAC ``PPP n`` >>
	  HINT_EXISTS_TAC >>
	  EXISTS_TAC ``PeripheralSender (PPP n)`` >>
	  EXISTS_TAC ``r':request`` >>
	  ASM_REWRITE_TAC [] >>
	  Q.UNABBREV_TAC `IM''` >>
	  RW_TAC (srw_ss()) []
      ) >> 
      Q.ABBREV_TAC `not_write_or_igc =
      	(PAdr r' NOTIN A_IGCin (PPG n) /\ (PAdr r' NOTIN A_IGCout (PPG n))
      	    \/ ~Wreq r')` >>
      (* show existence of refined computation *) 
      FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
      `refined_comp(RM,SUC 0, RM with <|m := m'; 
				        SMMU := (n =+ SMMU') RM.SMMU|>)` by (
          METIS_TAC [refined_comp_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [] >>
      (* show that memory is still in simulation *)
      `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
             (mem_abs((IM''.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
          REPEAT STRIP_TAC >>
	  Cases_on `g = PPG n` 
	  >| [`(IM''.G g).m = im'` by (
	          Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      METIS_TAC [mem_access_bisim_lem]
	      ,
	      `(IM''.G g).m = (IM.G g).m` by (
	          Q.UNABBREV_TAC `IM''` >>
		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
              METIS_TAC [no_igc_write_mem_upd_others_lem]
	     ]
      ) >>
      (* show SIM *) 
      STRIP_TAC >- (
      Q.UNABBREV_TAC `IM''` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `RM.C c = (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	  ) >>
      	  TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       pproj_bound_lem] ) )
      )
      ) >>
      (* SimInvR *)
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
      ,
      (* case: write to IGC memory *)
      FULL_SIMP_TAC (srw_ss()) []
      >| [(* case: write to A_IGCin -> not possible *)
	  FULL_SIMP_TAC (srw_ss()) [A_IGCin_def, InvR_EXPAND] >>
	  IMP_RES_TAC ref_inv_hyp_iso_smmu_final_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  METIS_TAC []
	  ,
	  (* case: write to A_IGCout -> prove additional sync *)
	  Q.ABBREV_TAC `IM'' = <|G := (PPG n =+ IM.G (PPG n) with
                        <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>)
					  IM.G|>` >>
	  Cases_on `syncInv IM''`
	  >| [(* syncInv -> Write no effect *)
              FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
	      `refined_comp(RM,SUC 0, RM with <|m := m'; 
				         SMMU := (n =+ SMMU') RM.SMMU|>)` by (
                  METIS_TAC [refined_comp_def]
	      ) >>
	      EXISTS_TAC ``SUC 0`` >>
	      HINT_EXISTS_TAC >>
	      ASM_REWRITE_TAC [] >>
	      (* show that memory is still in simulation *)
              `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
	       (mem_abs((IM''.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
                  REPEAT STRIP_TAC >>
              	  Cases_on `g = PPG n` 
           	  >| [(* same guest *)
           	      `(IM''.G g).m = im'` by (
           	          Q.UNABBREV_TAC `IM''` >>
           		  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
           	      ) >>
           	      ASM_REWRITE_TAC [] >>
           	      METIS_TAC [mem_access_bisim_lem]
           	      ,
           	      (* other guest *)
           	      Cases_on `THE (Trans g a) = THE (Trans (PPG n) (PAdr r'))`
           	      >| [(* igc input channel, unchanged *)
           		  `?s. s < PAR.ns /\ (PAR.cpol s = (PPG n, g)) /\
           		       (PAR.igca s = (PAdr r', a))` by (
           		      METIS_TAC [Trans_eq_igc_out_lem]
           		  ) >>
           		  `mem_abs (IM''.G g).m a = 
           	           mem_abs (IM''.G (PPG n)).m (PAdr r')` by (
           		      METIS_TAC [syncInv_def]
           		  ) >>
           		  `(IM''.G (PPG n)).m = im'` by (
           	              Q.UNABBREV_TAC `IM''` >>
           		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
           		  ) >>
           		  `Trans g a = Trans (PPG n) (PAdr r')` by (
           		      METIS_TAC [Trans_axiom, 
					 pairTheory.FST, pairTheory.SND]   
           		  ) >>
           		  ASM_REWRITE_TAC [] >>
           		  METIS_TAC [mem_access_bisim_lem]
           		  ,
           		  (* other address, unchanged *)
           		  `(IM''.G g).m = (IM.G g).m` by (
           	              Q.UNABBREV_TAC `IM''` >>
           		      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
           		  ) >>
           		  `a <> Agicd` by (
           		      METIS_TAC [Agicd_A_gicper_lem]
           		  ) >>
           		  `IS_SOME (Trans g a)` by (
           		      METIS_TAC [Trans_axiom]   
           		  ) >>
           		  `THE (Trans g a) <> PAdr (Trreq (PPG n) r')` by (
           		      RW_TAC std_ss [Trreq_PAdr_Trans_lem]
           		  ) >>
           		  `mem_abs m' (THE (Trans g a)) = 
           	           mem_abs RM.m (THE (Trans g a))` by (
           		      METIS_TAC [mem_aligned_unchanged_lem]
           		  ) >>
           		  ASM_REWRITE_TAC [] >>
           		  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
           		  IMP_RES_TAC bisim_memory_def
           		 ]
           	     ]
	      ) >>
              (* show SIM *) 
              STRIP_TAC >- (
              Q.UNABBREV_TAC `IM''` >>
              FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
              REPEAT STRIP_TAC >> (
              FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
              (* try to solve straight-forward cases *)
              >> (REPEAT IF_CASES_TAC >>
                  STRONG_FS_TAC ([]@bisim_core_definitions) >>
              	  `RM.C c = (RM with <|m := m'; 
				       SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
              	  ) >>
              	  TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              			   hv_guard_mmu_fault_eq_lem, 
				   hv_guard_gicd_fail_lem,
              			   hv_mmu_fault_entry_eq_lem,
              			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              			   pproj_bound_lem] ) )
              )
              ) >>
              (* SimInvR *)
              FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
              RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	      ,
	      (* not syncInv *)
              FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
	      `?s rg ra. s < PAR.ns /\ rg < PAR.ng /\
                         (PAR.igca s = (PAdr r',ra)) /\
			 (PAR.cpol s = (PPG n, rg)) /\ rg <> PPG n` by (
	          FULL_SIMP_TAC std_ss [A_IGCout_def, GSPEC_f_lem] >>
		  HINT_EXISTS_TAC >>
		  METIS_TAC [quantHeuristicsTheory.FST_PAIR_EQ,
			     goodP_axiom]
	      ) >>
	      `(IM'.G (PPG n) = IM.G (PPG n) with
                <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>) /\
               (IM'.G rg = IM.G rg with
                m := memory_upd (ra,mem_abs im' (PAdr r')) (IM.G rg).m) /\
               !g. g < PAR.ng /\ g <> PPG n /\ g <> rg ==> 
		   (IM'.G g = IM.G g)` by (
	          MATCH_MP_TAC do_sync_igc_smmu_write_lem >>
		  HINT_EXISTS_TAC >>
		  METIS_TAC []
	      ) >>
	      (* show existence of refined computation *)
              `refined_comp(RM,SUC 0, RM with 
                   <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>)` by (
                  METIS_TAC [refined_comp_def]
              ) >>
	      EXISTS_TAC ``SUC 0`` >>
	      HINT_EXISTS_TAC >>
	      ASM_REWRITE_TAC [] >>
	      (* add context about write *)
	      `!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
	      	(mem_abs((IM'.G g).m) a = mem_abs m' (THE(Trans g a)))` by (
                  REPEAT STRIP_TAC >>
	          Cases_on `g = PPG n` 
	          >| [(* case: PPG n *) 
	              `(IM'.G g).m = im'` by (
	                  Q.UNABBREV_TAC `IM''` >>
	      	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      	  ) >>
	      	  ASM_REWRITE_TAC [] >>
	      	  METIS_TAC [mem_access_bisim_lem]
	      	  ,
	      	  Cases_on `g = rg`
	      	  >| [(* case: g2 *)
	      	      Cases_on `a = ra`
	      	      >| [(* updated page *)
	      		  `Trans g a = Trans (PPG n) (PAdr r')` by (
	      		      METIS_TAC [Trans_axiom,
	      				 pairTheory.FST, pairTheory.SND]
	      		  ) >>
	      		  ASM_REWRITE_TAC [] >>
	      		  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM,
	      				 memory_upd_mem_abs_id_lem] >>
	      		  METIS_TAC [mem_access_bisim_lem]
	      		  ,
	      		  (* other pages *)
	      		  `mem_abs (IM.G rg with m := 
	      		       memory_upd (ra,mem_abs im' (PAdr r')) (IM.G rg).m
	      			   ).m a = mem_abs (IM.G rg).m a` by (
	      		      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      		      METIS_TAC [memory_upd_axiom]
	      		  ) >>
	      		  ASM_REWRITE_TAC [] >>
	      		  METIS_TAC [igc_write_mem_upd_others_lem]
	      		 ]
	      	      ,
	      	      (* all other unaffected guests *)
	      	      RES_TAC >>
	      	      ASM_REWRITE_TAC [] >>
	      	      METIS_TAC [igc_write_mem_upd_others_lem]
	      	     ]
	      	 ]
	      ) >>
	      `!g. g < PAR.ng ==>
	           (mem_req_rcvd (IM'.G g).m = mem_req_rcvd (IM''.G g).m)
	        /\ (mem_req_sent (IM'.G g).m = mem_req_sent (IM''.G g).m)
	        /\ (mem_rpl_rcvd (IM'.G g).m = mem_rpl_rcvd (IM''.G g).m)` by (
	          STRIP_TAC >> STRIP_TAC >> Cases_on `g = rg`
	          >| [Q.UNABBREV_TAC `IM''` >>
	      	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
	      	          METIS_TAC [memory_upd_axiom]
	      	      )
	      	      ,
	      	      Cases_on `g = PPG n` >> (
	      	          Q.UNABBREV_TAC `IM''` >>
	      	          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
	      	              METIS_TAC [memory_upd_axiom]
	      	          ) 
	      	      )
	      	     ]
	      ) >>
	      `!g. g < PAR.ng ==>
	           ((IM'.G g).pif = (IM''.G g).pif)` by (
	          STRIP_TAC >> STRIP_TAC >> Cases_on `g = PPG n` 
	          >| [Q.UNABBREV_TAC `IM''` >>
	              RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] 
	              ,
	      	      Cases_on `g = rg` >> (
	                  Q.UNABBREV_TAC `IM''` >>
	          	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      	      )
	             ]
	      ) >>
	      (* prove SIM *)
	      Q.UNABBREV_TAC `IM''` >>
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      REPEAT STRIP_TAC
	  >| [(* ctx *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* memory *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS
	      ,
	      (* periph *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >> (
	          Cases_on `PPG p = PPG n`
	          >| [STRONG_FS_TAC ([]@bisim_core_definitions)
	              ,
	              Cases_on `PPG p = rg` >> (
	                  STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
	             ]
	      )
	      ,
	      (* corereq_guest *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* corereq_hyp *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* corereq_gicd *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* mmureq_guest *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* gicdmsg_ideal *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* gicdmsg_refined *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* smmureq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >> (
	          IF_CASES_TAC
	          >| [IF_CASES_TAC
		      >| [`n = p` by ( METIS_TAC [PPG_PPP_inj] ) >>
			  STRONG_FS_TAC ([]@bisim_core_definitions)
			  ,
			  `n <> p` by ( METIS_TAC [PPG_PPP_inj] ) >>
			  STRONG_FS_TAC ([]@bisim_core_definitions)
			  ]
	              ,
	              Cases_on `PPG p = rg` >> (
	                 STRONG_FS_TAC ([]@bisim_core_definitions)
	              )
	             ] >> (
	          `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      		  ) >>
		  TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              			   hv_guard_mmu_fault_eq_lem, 
				   hv_guard_gicd_fail_lem,
              			   hv_mmu_fault_entry_eq_lem,
              			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              			   pproj_bound_lem] ) 
		  )
	      )
	      ,
	      (* giccreq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* gicdreq_ideal *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* gicdreq_refined *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* gicd_fail *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      )
	      ,
	      (* memreq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* perirq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n` 
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
	          )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* igcirq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n` 
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
	          )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* sgiirq *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n` 
	      >| [STRONG_FS_TAC ([]@bisim_core_definitions)
		  ,
		  Cases_on `PCG c = rg` >> (
		      STRONG_FS_TAC ([]@bisim_core_definitions)
	          )
		 ] >> (
      	      `RM.C c = (RM with <|m := m'; 
				   SMMU := (n =+ SMMU') RM.SMMU|>).C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	      ) >>
              TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
              		       hv_guard_mmu_fault_eq_lem, 
			       hv_guard_gicd_fail_lem,
              		       hv_mmu_fault_entry_eq_lem,
              		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
              		       pproj_bound_lem] ) 
	      ) 
	      ,
	      (* send_igc *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      STRONG_FS_TAC ([]@bisim_core_definitions) >>
	      REPEAT STRIP_TAC >> (
	          Cases_on `g = PPG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `g = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
	      )
	      ,
	      (* bisim_ext *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >> (
	          Cases_on `g = PPG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `g = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
	      )
	      ,
	      (* psci *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS
	      >| [Cases_on `PCG c = PPG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		  ,
	          Cases_on `PCG c = PPG n`
	          >| [STRONG_FS_TAC []
		      ,
		      Cases_on `PCG c = rg` >> (
		          STRONG_FS_TAC ([]@bisim_core_definitions)
		      )
		     ]
		 ]
	      ,
	      (* gicc_reg *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `PCG c = PPG n`
	      >| [STRONG_FS_TAC []
		  ,
		  Cases_on `PCG c = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* gicd_reg *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `g = PPG n`
	      >| [STRONG_FS_TAC []
		  ,
		  Cases_on `g = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      (* pi *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		  bisim_definitions RW_FS_IMPRESS >>
	      Cases_on `g = PPG n`
	      >| [STRONG_FS_TAC []
		  ,
		  Cases_on `g = rg` >> (
		     STRONG_FS_TAC ([]@bisim_core_definitions)
		  )
		 ]
	      ,
	      ALL_TAC
	     ] >>
	      (* SimInvR *)
              FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
              RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	     ]
	 ]
     ]
);


(* golden fault information *)

(* not valid any more *)
(* val mmu_golden_fault_FAR_lem = store_thm("mmu_golden_fault_FAR_lem", `` *)
(* !RM q MMU' c. *)
(*    c < RPAR.nc *)
(* /\ InvR RM *)
(* /\ Mode (RM.C c) < 2 *)
(* /\ mmu_step_snd_rpl(RM.MMU c,q,MMU')  *)
(* /\ Frpl q *)
(* ==> *)
(* ((11 >< 0) (extract_FAR (fiOf q)) = (11 >< 0) (Rpl_Adr q) :bool[12]) *)
(* ``, *)
(*   REPEAT STRIP_TAC >> *)
(*   `(refcore_abs (RM.C c)).H.init_core` by (  *)
(*       FULL_SIMP_TAC std_ss [InvR_EXPAND, Mode_mode_lem] >> *)
(*       METIS_TAC [ref_inv_hist_def]  *)
(*   ) >> *)
(*   IMP_RES_TAC mmu_golden_conf_lem >> *)
(*   IMP_RES_TAC Frpl_ALT_DEF >> *)
(*   IMP_RES_TAC mmu_golden_fault_FAR_axiom >> *)
(*   `good_rpl q` by ( RW_TAC std_ss [good_rpl_def] ) >> *)
(*   ASM_REWRITE_TAC [fiOf_def] >> *)
(*   RW_TAC std_ss [Rpl_Adr_ReqOf_lem, ReqOf_def] *)
(* ); *)

(* refined memory reply lemma *)

val ref_mem_core_rpl_lem = store_thm("ref_mem_core_rpl_lem", ``
!RM IM c r q im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ c < RPAR.nc
/\ mem_step_snd_rpl((IM.G (PCG c)).m, q, CoreSender (PCC c), im')
/\ match (r,q)
/\ match (Trreq (PCG c) r,Trrpl (PCG c) q)
/\ IS_SOME (Trans (PCG c) (PAdr r))
/\ PAdr r IN PAR.A_G (PCG c)
(* /\ r' IN ((IM.G (PCG c)).cif (PCC c)).req_sent *)
/\ (Trreq (PCG c) r,CoreSender c) IN mem_req_rcvd RM.m
/\ (r,CoreSender (PCC c)) IN mem_req_rcvd (IM.G (PCG c)).m
==>
?m'. mem_step_snd_rpl (RM.m, Trrpl (PCG c) q, CoreSender c,m') 
``,
  REPEAT STRIP_TAC >>
  `good_rpl q` by ( METIS_TAC [good_match_lem] ) >>
  IMP_RES_TAC good_proj_in_range_impls >>
  Cases_on `PAdr r IN A_gicper`
  >| [(* forwarded IO reply *)
      IMP_RES_TAC good_proj_in_range_impls >>
      `PAdr (Trreq (PCG c) r) IN A_gicper` by (
          METIS_TAC [A_gicper_Trreq_lem]
      ) >>
      `(q,CoreSender (PCC c)) IN mem_rpl_rcvd (IM.G (PCG c)).m` by (
          CCONTR_TAC >>
	  IMP_RES_TAC good_rpl_cases_lem
	  >| [(* read *)
	      METIS_TAC [mem_read_axiom, unique_match_thm]
	      ,
	      (* write *)
	      METIS_TAC [mem_write_axiom, unique_match_thm]
	      ,
	      (* walk *)
	      METIS_TAC [mem_walk_axiom, unique_match_thm]
	      ,
	      (* fault *)
	      METIS_TAC [mem_fault_axiom, Frpl_def]
	     ]
      ) >>
      `Rpl_PAdr q <> Agicd` by ( 
          IMP_RES_TAC match_PAdr_eq_lem >>
          METIS_TAC [Trans_axiom]	  
      ) >>
      `(Trrpl (PCG c) q, CoreSender c) IN mem_rpl_rcvd RM.m` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_memreq_def
      ) >>
      METIS_TAC [mem_snd_rpl_enabled_axiom]
      ,
      (* generated reply *)
      `PAdr (Trreq (PCG c) r) NOTIN A_gicper` by (
          METIS_TAC [not_A_gicper_Trreq_lem]
      ) >>
      `(q,CoreSender (PCC c)) NOTIN mem_rpl_rcvd (IM.G (PCG c)).m` by (
          CCONTR_TAC >>
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC mem_io_fw_axiom >>
	  METIS_TAC [unique_match_thm]
      ) >>
      `Rpl_PAdr q <> Agicd` by ( 
          IMP_RES_TAC match_PAdr_eq_lem >>
          METIS_TAC [Trans_axiom]	  
      ) >>
      `(Trrpl (PCG c) q, CoreSender c) NOTIN mem_rpl_rcvd RM.m` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  METIS_TAC [bisim_memreq_def]
      ) >>
      BasicProvers.byA (
          `Rreq (Trreq (PCG c) r) \/ PTreq (Trreq (PCG c) r) ==>
                (Rpl_val (Trrpl (PCG c) q) = mem_read (mem_abs (RM.m)) 
						      (Adr (Trreq (PCG c) r)) 
						      (SzOf (Trreq (PCG c) r)))`,
          RW_TAC std_ss [])
	  >| [(* Read *)
	      Cases_on `r` >> (
	          FULL_SIMP_TAC std_ss [Rreq_def, Trreq_def]
	      ) >>
	      BasicProvers.byA (
	          `?v. q = ReadValue (Read c' n m) v`,
	          IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def, Trrpl_def] 
		  ) 
	      ) >- (
	          (* fault cases *)
	          BasicProvers.byA (
		      `Frpl (Fault r fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      ) >- (
	          BasicProvers.byA (
 		      `Frpl (Fault r fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      )	>>
	      `v = w2v (mem_read (mem_abs (IM.G (PCG c)).m) 
				 (Adr (Read c' n m)) n)` by (
	          IMP_RES_TAC mem_read_axiom >>
	          METIS_TAC [Trreq_def, unique_match_thm]
	      ) >>
	      `Rpl_val (Trrpl (PCG c) q):word64 = Rpl_val q` by (
	          IMP_RES_TAC good_match_lem >>
		  IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def] >>
		      REV_FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
		  ) >>
		  RW_TAC std_ss [Rpl_val_def]
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [Rpl_val_def, Adr_def, SzOf_def,
					bitstringTheory.v2w_w2v] >>
	      MATCH_MP_TAC EQ_SYM >>
	      MATCH_MP_TAC mem_read_lem >>
	      FULL_SIMP_TAC std_ss [PAdr_def, Adr_def]
	      ,
	      (* Walk *)
	      Cases_on `r` >> (
	          FULL_SIMP_TAC std_ss [PTreq_def, Trreq_def]
	      ) >>
	      BasicProvers.byA (
	          `?v. q = WalkResult (Walk c' m) v`,
	          IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def, Trrpl_def] 
		  ) 
	      ) >- (
	          (* fault cases *)
	          BasicProvers.byA (
		      `Frpl (Fault r fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      ) >- (
	          BasicProvers.byA (
		      `Frpl (Fault r fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      )	>>
	      `v = mem_read (mem_abs (IM.G (PCG c)).m) 
			    (Adr (Walk c' m)) 8` by (
	          IMP_RES_TAC mem_walk_axiom >>
	          METIS_TAC [Trreq_def, unique_match_thm]
	      ) >>
	      `Rpl_val (Trrpl (PCG c) q):word64 = Rpl_val q` by (
	          IMP_RES_TAC good_match_lem >>
		  IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def] >>
		      REV_FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
		  ) >>
		  RW_TAC std_ss [Rpl_val_def]
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [Rpl_val_def, Adr_def, SzOf_def,
					wordsTheory.w2w_id] >>
	      MATCH_MP_TAC EQ_SYM >>
	      MATCH_MP_TAC mem_read_lem >>
	      FULL_SIMP_TAC std_ss [PAdr_def, Adr_def]
	      ,
	      (* finish *)
              METIS_TAC [mem_snd_rpl_enabled_axiom]
	     ]
     ]
);

val ref_mem_per_rpl_lem = store_thm("ref_mem_per_rpl_lem", ``
!RM IM p r q im'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ p < RPAR.np
/\ mem_step_snd_rpl((IM.G (PPG p)).m, q, PeripheralSender (PPP p), im')
/\ match (r,q)
/\ match (Trreq (PPG p) r,Trrpl (PPG p) q)
/\ IS_SOME (Trans (PPG p) (PAdr r))
/\ PAdr r IN PAR.A_G (PPG p)
/\ PAdr r NOTIN A_gicper
/\ (Trreq (PPG p) r,PeripheralSender p) IN mem_req_rcvd RM.m
==>
?m'. mem_step_snd_rpl (RM.m, Trrpl (PPG p) q, PeripheralSender p,m') 
``,
  REPEAT STRIP_TAC >>
  `good_rpl q` by ( METIS_TAC [good_match_lem] ) >>
  IMP_RES_TAC good_proj_in_range_impls >>
  `PAdr (Trreq (PPG p) r) NOTIN A_gicper` by (
      METIS_TAC [not_A_gicper_Trreq_lem]
  ) >>
  `(q,PeripheralSender (PPP p)) NOTIN mem_rpl_rcvd (IM.G (PPG p)).m` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC mem_io_fw_axiom >>
      METIS_TAC [unique_match_thm]
  ) >>
  `Rpl_PAdr q <> Agicd` by ( 
      IMP_RES_TAC match_PAdr_eq_lem >>
      METIS_TAC [Trans_axiom]	  
  ) >>
  `(Trrpl (PPG p) q, PeripheralSender p) NOTIN mem_rpl_rcvd RM.m` by (
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      METIS_TAC [ref_inv_ioreq_def]
  ) >>
  BasicProvers.byA (
      `Rreq (Trreq (PPG p) r) \/ PTreq (Trreq (PPG p) r) ==>
            (Rpl_val (Trrpl (PPG p) q) = mem_read (mem_abs (RM.m)) 
						  (Adr (Trreq (PPG p) r)) 
						  (SzOf (Trreq (PPG p) r)))`,
      RW_TAC std_ss [])
      >| [(* Read *)
	  Cases_on `r` >> (
	      FULL_SIMP_TAC std_ss [Rreq_def, Trreq_def]
	  ) >>
	  `?v. q = ReadValue (Read c n m) v` by (
	      IMP_RES_TAC good_rpl_cases_lem >> (
	          FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def, Trrpl_def] 
	      ) >> (
	          (* fault cases *)
	          BasicProvers.byA (
	              `Frpl (Fault r fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      )
	  ) >>
	  `v = w2v (mem_read (mem_abs (IM.G (PPG p)).m) 
			     (Adr (Read c n m)) n)` by (
	      IMP_RES_TAC mem_read_axiom >>
	      METIS_TAC [Trreq_def, unique_match_thm]
	  ) >>
	  `Rpl_val (Trrpl (PPG p) q):word64 = Rpl_val q` by (
	      IMP_RES_TAC good_match_lem >>
	      IMP_RES_TAC good_rpl_cases_lem >> (
	          FULL_SIMP_TAC (srw_ss()) [match_def] >>
	          REV_FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
	      ) >>
	      RW_TAC std_ss [Rpl_val_def]
	  ) >>
	  REV_FULL_SIMP_TAC std_ss [Rpl_val_def, Adr_def, SzOf_def,
				    bitstringTheory.v2w_w2v] >>
	  MATCH_MP_TAC EQ_SYM >>
	  MATCH_MP_TAC mem_read_lem >>
	  FULL_SIMP_TAC std_ss [PAdr_def, Adr_def]
	  ,
	  (* Walk *)
	  Cases_on `r` >> (
	      FULL_SIMP_TAC std_ss [PTreq_def, Trreq_def]
	  ) >>
	  `?v. q = WalkResult (Walk c m) v` by (
	      IMP_RES_TAC good_rpl_cases_lem >> (
	      FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def, Trrpl_def] 
	      ) >> (
	          (* fault cases *)
	          `Frpl (Fault r fi)` by (
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      )
	  ) >>
	  `v = mem_read (mem_abs (IM.G (PPG p)).m) 
			(Adr (Walk c m)) 8` by (
	      IMP_RES_TAC mem_walk_axiom >>
	      METIS_TAC [Trreq_def, unique_match_thm]
	  ) >>
	  `Rpl_val (Trrpl (PPG p) q):word64 = Rpl_val q` by (
	      IMP_RES_TAC good_match_lem >>
	      IMP_RES_TAC good_rpl_cases_lem >> (
	          FULL_SIMP_TAC (srw_ss()) [match_def] >>
	          REV_FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
	      ) >>
	      RW_TAC std_ss [Rpl_val_def]
	  ) >>
	  REV_FULL_SIMP_TAC std_ss [Rpl_val_def, Adr_def, SzOf_def,
				    wordsTheory.w2w_id] >>
	  MATCH_MP_TAC EQ_SYM >>
	  MATCH_MP_TAC mem_read_lem >>
	  FULL_SIMP_TAC std_ss [PAdr_def, Adr_def]
	  ,
	  (* finish *)
	  METIS_TAC [mem_snd_rpl_enabled_axiom]
	 ]				   
);

(* ideal memory reply lemma *)

val id_mem_rpl_lem = store_thm("id_mem_rpl_lem", ``
!RM IM n r r' q m'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.np
/\ mem_step_snd_rpl (RM.m, q, PeripheralSender n,m')
/\ match (Trreq (PPG n) r',q)
/\ IS_SOME (Trans (PPG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PPG n)
/\ PAdr r' NOTIN A_gicper
/\ r' IN ((IM.G (PPG n)).pif (PPP n)).req_sent
/\ (Trreq (PPG n) r',PeripheralSender n) IN mem_req_rcvd RM.m
/\ (r',PeripheralSender (PPP n)) IN mem_req_rcvd (IM.G (PPG n)).m
==>
?im' iq. mem_step_snd_rpl((IM.G (PPG n)).m, iq, PeripheralSender (PPP n), im')
      /\ (q = Trrpl (PPG n) iq)
``,
  REPEAT STRIP_TAC >>
  `(q, PeripheralSender n) NOTIN mem_rpl_rcvd (RM.m)` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
      IMP_RES_TAC ref_inv_ioreq_def >>
      METIS_TAC []
  ) >>
  Cases_on `Rreq r' \/ PTreq r'`
  >| [(* Case: Read or Walk *)
      `?iq. match(r',iq) /\ 
	    (Rpl_val iq = mem_read (mem_abs (IM.G (PPG n)).m) 
					    (Adr r') (SzOf r'))
	    /\ xlated_rpl(iq,q)` by (
          Cases_on `r'`
	  >| [(* Read *)
	      FULL_SIMP_TAC (srw_ss()) [match_def, PTreq_def] >> 
	      EXISTS_TAC ``ReadValue (Read c n' m) 
	                             (w2v (mem_read (mem_abs (IM.G (PPG n)).m) 
						   (Adr (Read c n' m)) 
						   (SzOf (Read c n' m))))`` >>
	      RW_TAC (srw_ss()) [Rpl_val_def, bitstringTheory.v2w_w2v, 
				 xlated_rpl_def] >>
	      Cases_on `q`
	      >| [(* Read Reply *)
	          EXISTS_TAC ``r:request`` >>
		  `r = Trreq (PPG n) (Read c n' m)` by (
		      Cases_on `Trreq (PPG n) (Read c n' m)` >> (
		          FULL_SIMP_TAC (srw_ss()) [match_def]
		      )
		  ) >> 
		  IMP_RES_TAC pproj_bound_lem >>
		  IMP_RES_TAC Trreq_xlated_Trans_lem >> 
		  ASM_REWRITE_TAC [] >>
		  FULL_SIMP_TAC (srw_ss()) [Trreq_def] >>
		  IMP_RES_TAC mem_read_axiom >>
		  FULL_SIMP_TAC (srw_ss()) [] >>
		  Cases_on `r'` >> (
		      FULL_SIMP_TAC (srw_ss()) [match_def, SzOf_def, Adr_def]
		  ) >>
		  FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def] >>
		  METIS_TAC [mem_read_lem]
		  ,
		  (* Write reply not possible *)
		  FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def]
		  ,
		  (* Walk reply not possible *)
		  FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def]
		  ,
		  (* Faulty read not possible, by axiom *)		  
		  `Frpl (Fault r f)` by (
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
		 ]
	      ,
	      (* Write *)
	      FULL_SIMP_TAC (srw_ss()) [Rreq_def, PTreq_def]
	      ,
	      (* Walk *)
	      FULL_SIMP_TAC (srw_ss()) [Rreq_def] >>
	      RW_TAC (srw_ss()) [match_def] >>
	      EXISTS_TAC ``WalkResult (Walk c m) 
	                              (mem_read (mem_abs (IM.G (PPG n)).m) 
						(Adr (Walk c m)) 
						(SzOf (Walk c m)))`` >>
	      RW_TAC (srw_ss()) [Rpl_val_def, xlated_rpl_def] >>
	      EXISTS_TAC ``Trreq (PPG n) (Walk c m)`` >> 
	      IMP_RES_TAC pproj_bound_lem >>
	      `xlated (Walk c m, Trreq (PPG n) (Walk c m))` by (
                  METIS_TAC [Trreq_xlated_Trans_lem]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      Cases_on `q` >> ( FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def]	) 
	      >| [(* Walk reply *)
		  IMP_RES_TAC mem_walk_axiom >>
	          RW_TAC (srw_ss()) [] >>
		  FULL_SIMP_TAC (srw_ss()) [SzOf_def, Adr_def] >>
		  RES_TAC >>
		  Cases_on `r` >> (
		      FULL_SIMP_TAC (srw_ss()) [match_def, SzOf_def, Adr_def]
		  ) >>
		  FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def] >>
		  METIS_TAC [mem_read_lem]
		  ,
		  (* Faulty walk not possible, by axiom *)		  
		  `Frpl (Fault (Walk (ipat (PPG n) c) m) f)` by (
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
		 ]
	     ]
      ) >>
      `?im'. mem_step_snd_rpl((IM.G (PPG n)).m,iq,
			       PeripheralSender (PPP n),im')` by (
          IMP_RES_TAC mem_snd_rpl_enabled_axiom >>
	  REV_FULL_SIMP_TAC (srw_ss()) []
      ) >>
      IMP_RES_TAC pproj_bound_lem >>
      `q = Trrpl (PPG n) iq` by (
          METIS_TAC [match_Trrpl_lem]
      ) >>
      METIS_TAC []
      ,
      (* Case: Write *) 
      `?iq. match(r',iq) /\ xlated_rpl(iq,q)` by (
          Cases_on `r'` >> (
              Cases_on `q` >> (
                  FULL_SIMP_TAC (srw_ss()) [Rreq_def, PTreq_def, 
					    match_def, Trreq_def]
	      )	  
	  )
	  >| [(* Write reply *)
	      EXISTS_TAC ``WrittenValue (Write c n' l m)`` >>
	      REWRITE_TAC [xlated_rpl_def] >>
	      EXISTS_TAC ``Write (ipat (PPG n) c) n' l m`` >>
	      REWRITE_TAC [xlated_def] >>
	      EXISTS_TAC ``Adr r`` >>
	      RW_TAC (srw_ss()) [ipat_def, Adr_def] >>
	      FULL_SIMP_TAC (srw_ss()) [ATrans_def, PAdr_def, Adr_def] >>
	      FULL_SIMP_TAC (srw_ss()) [optionTheory.IS_SOME_EXISTS] >>
	      RW_TAC (srw_ss()) [bx_extract_lem] 
	      ,
	      (* Fault reply *)
	      `Frpl (Fault (Write (ipat (PPG n) c) n' l m) f)` by (
	          FULL_SIMP_TAC (srw_ss()) [Frpl_def]
	      ) >>
	      METIS_TAC [mem_fault_axiom]
	     ]
      ) >>
      IMP_RES_TAC pproj_bound_lem >>
      `q = Trrpl (PPG n) iq` by (
          METIS_TAC [match_Trrpl_lem]
      ) >>
      METIS_TAC [mem_snd_rpl_enabled_axiom]
     ]
);

val id_mem_core_rpl_lem = store_thm("id_mem_core_rpl_lem", ``
!RM IM n r' q m'.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.nc
/\ mem_step_snd_rpl (RM.m, q, CoreSender n,m')
/\ match (Trreq (PCG n) r',q)
/\ IS_SOME (Trans (PCG n) (PAdr r'))
/\ PAdr r' IN PAR.A_G (PCG n)
(* /\ PAdr r' NOTIN A_gicper *)
/\ r' IN ((IM.G (PCG n)).cif (PCC n)).req_sent
/\ (Trreq (PCG n) r',CoreSender n) IN mem_req_rcvd RM.m
/\ (r',CoreSender (PCC n)) IN mem_req_rcvd (IM.G (PCG n)).m
==>
?im' iq. mem_step_snd_rpl((IM.G (PCG n)).m, iq, CoreSender (PCC n), im')
      /\ (q = Trrpl (PCG n) iq)
``,
  REPEAT STRIP_TAC >>
  Cases_on `PAdr r' IN A_gicper`
  >| [(* forwarded IO reply *)
      IMP_RES_TAC good_match_lem >>
      IMP_RES_TAC good_proj_in_range_impls >>
      `PAdr (Trreq (PCG n) r') IN A_gicper` by (
          METIS_TAC [A_gicper_Trreq_lem]
      ) >>
      `(q,CoreSender n) IN mem_rpl_rcvd RM.m` by (
          CCONTR_TAC >>
	  IMP_RES_TAC good_rpl_cases_lem
	  >| [(* read *)
	      METIS_TAC [mem_read_axiom, unique_match_thm]
	      ,
	      (* write *)
	      METIS_TAC [mem_write_axiom, unique_match_thm]
	      ,
	      (* walk *)
	      METIS_TAC [mem_walk_axiom, unique_match_thm]
	      ,
	      (* fault *)
	      METIS_TAC [mem_fault_axiom, Frpl_def]
	     ]
      ) >>
      `?iq. match(r', iq) /\ (q = Trrpl (PCG n) iq)` by (
          METIS_TAC [Trrpl_exists_lem]
      ) >>
      `Rpl_PAdr iq <> Agicd` by ( 
          IMP_RES_TAC match_PAdr_eq_lem >>
          METIS_TAC [Trans_axiom]	  
      ) >>
      `(iq, CoreSender (PCC n)) IN 
           mem_rpl_rcvd (IM.G (PCG n)).m` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_memreq_def
      ) >>
      METIS_TAC [mem_snd_rpl_enabled_axiom]
      ,
      (* generated reply *)
      IMP_RES_TAC good_match_lem >>
      IMP_RES_TAC good_proj_in_range_impls >>
      `PAdr (Trreq (PCG n) r') NOTIN A_gicper` by (
          METIS_TAC [not_A_gicper_Trreq_lem]
      ) >>
      `(q,CoreSender n) NOTIN mem_rpl_rcvd RM.m` by (
          CCONTR_TAC >>
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC mem_io_fw_axiom >>
	  METIS_TAC [unique_match_thm]
      ) >>
      `?iq. match(r', iq) /\ (q = Trrpl (PCG n) iq)` by (
          METIS_TAC [Trrpl_exists_lem]
      ) >>
      `Rpl_PAdr iq <> Agicd` by ( 
          IMP_RES_TAC match_PAdr_eq_lem >>
          METIS_TAC [Trans_axiom]	  
      ) >>
      `(iq, CoreSender (PCC n)) NOTIN 
           mem_rpl_rcvd (IM.G (PCG n)).m` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  METIS_TAC [bisim_memreq_def]
      ) >>
      BasicProvers.byA (
          `Rreq r' \/ PTreq r' ==>
           (Rpl_val iq = mem_read (mem_abs ((IM.G (PCG n)).m)) 
				  (Adr r') 
				  (SzOf r'))`,
          RW_TAC std_ss [])
	  >| [(* Read *)
	      Cases_on `r'` >> (
	          FULL_SIMP_TAC std_ss [Rreq_def]
	      ) >>
	      BasicProvers.byA (
	          `?v. Trrpl (PCG n) iq = 
	               ReadValue (Read (ipat (PCG n) c) n' m) v`,
  	          IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def, Trrpl_def] 
		  ) 
	      ) >- (
	          (* fault cases *)
	          BasicProvers.byA (
		      `Frpl (Fault (Read (ipat (PCG n) c) n' m) fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      ) >- (
	          BasicProvers.byA (
		      `Frpl (Fault (Read (ipat (PCG n) c) n' m) fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      )	>>
	      `v = w2v (mem_read (mem_abs RM.m) 
				 (Adr (Read (ipat (PCG n) c) n' m)) n')` by (
	          IMP_RES_TAC mem_read_axiom >>
	          METIS_TAC [Trreq_def, unique_match_thm]
	      ) >>
	      `Rpl_val iq:word64 = Rpl_val (Trrpl (PCG n) iq)` by (
	          IMP_RES_TAC good_match_lem >>
		  IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def] >>
		      REV_FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
		  ) >>
		  RW_TAC std_ss [Rpl_val_def]
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [Rpl_val_def, Adr_def, SzOf_def,
					bitstringTheory.v2w_w2v] >>
	      MATCH_MP_TAC mem_read_lem >>
	      FULL_SIMP_TAC std_ss [PAdr_def, Adr_def]
	      ,
	      (* Walk *)
	      Cases_on `r'` >> (
	          FULL_SIMP_TAC std_ss [PTreq_def]
	      ) >>
	      BasicProvers.byA (
	          `?v. Trrpl (PCG n) iq = 
	               WalkResult (Walk (ipat (PCG n) c) m) v`,
	          IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def, Trreq_def, Trrpl_def] 
		  ) 
	      ) >- (
	          (* fault cases *)
	          BasicProvers.byA (
		      `Frpl (Fault (Walk (ipat (PCG n) c) m) fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      ) >- (
	          BasicProvers.byA (
		      `Frpl (Fault (Walk (ipat (PCG n) c) m) fi)`,
		      FULL_SIMP_TAC (srw_ss()) [Frpl_def]
		  ) >>
		  METIS_TAC [mem_fault_axiom]
	      )	>>
	      `v = mem_read (mem_abs RM.m) 
			    (Adr (Walk (ipat (PCG n) c) m)) 8` by (
	          IMP_RES_TAC mem_walk_axiom >>
	          METIS_TAC [Trreq_def, unique_match_thm]
	      ) >>
	      `Rpl_val iq:word64 = Rpl_val (Trrpl (PCG n) iq)` by (
	          IMP_RES_TAC good_match_lem >>
		  IMP_RES_TAC good_rpl_cases_lem >> (
	              FULL_SIMP_TAC (srw_ss()) [match_def] >>
		      REV_FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
		  ) >>
		  RW_TAC std_ss [Rpl_val_def]
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [Rpl_val_def, Adr_def, SzOf_def,
					wordsTheory.w2w_id] >>
	      MATCH_MP_TAC mem_read_lem >>
	      FULL_SIMP_TAC std_ss [PAdr_def, Adr_def]
	      ,
	      (* finish *)
	      METIS_TAC [mem_snd_rpl_enabled_axiom]
	     ]
     ]
);


(* ideal gic reply lemmas *)

val idgic_good_rpl_lem = store_thm("idgic_good_rpl_lem", ``
!IM G' q c g. 
   g < PAR.ng
/\ c < PAR.nc_g g
/\ InvI IM
/\ idgic_step_snd_rpl ((IM.G g).GIC, q, CoreSender c, g, G')
==>
?r. (r, CoreSender c) IN idgic_req_rcvd (IM.G g).GIC /\ match (r,q)
 /\ (PAdr r IN RPAR.Amap GICC \/  
        PAdr r IN RPAR.Amap GICD 
     /\ ~(gicd_acc_not_supported (MsgOf r)) 
     /\ gicd_req_ok r)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ( idgic_step_axiom // "good_rpl" ) >>
  IMP_RES_TAC ( InvI_EXPAND ``g:num`` ) >>
  HINT_EXISTS_TAC >>
  IMP_RES_TAC id_inv_gicreq_def >> (
      RW_TAC (srw_ss()) []
  ) >>
  (* case: GICD *)
  IMP_RES_TAC id_inv_mem_reqsent_def >> (
      RW_TAC (srw_ss()) [] >>
      `(ReqOf q) ∈ ((IM.G g).cif c).req_sent` by (
          IMP_RES_TAC id_inv_cifreq_def
      ) >>
      METIS_TAC [id_inv_cifadr_def]
  )      
);

val ideal_gicv_rpl_step_lem = store_thm("ideal_gicv_rpl_step_lem", ``
!RM IM k GIC' m' q r.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ match (q,r)
/\ (q,CoreSender (PCC k)) IN mem_req_sent (IM.G (PCG k)).m
/\ PAdr q IN RPAR.Amap GICC
==>
?gic' M'.
  gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic') /\
  mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC proj_bound_lem >>
  IMP_RES_TAC gicc_trans_lem >>
  `PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by ( 
      METIS_TAC [Trreq_PAdr_Trans_lem]
  ) >>
  IMP_RES_TAC match_IS_SOME_Trans_lem >>
  IMP_RES_TAC Trans_match_lem >>
  `Rpl_PAdr (Trrpl (PCG k) r) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `(q, CoreSender (PCC k)) IN idgic_req_rcvd (IM.G (PCG k)).GIC` by (
      METIS_TAC [idgic_good_rpl_lem, unique_match_thm]
  ) >>
  `PAdr q <> Agicd` by ( 
      METIS_TAC [singleAR_disj_EXPAND, not_in_GICD_not_Agicd_lem]
  ) >>
  `(Trreq (PCG k) q, CoreSender k) IN mem_req_sent RM.m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_memreq_def
  ) >>
  `(Trreq (PCG k) q, CoreSender k) IN gic_req_rcvd RM.GIC` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_giccreq_def 
  ) >>
  `Mode (RM.C k) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  (* show that GIC can send reply and that it is Trrpl (PCG k) r *) 
  IMP_RES_TAC gic_rpl_enable_axiom >>
  `xlated_rpl(r, q')` by ( 
      MATCH_MP_TAC ( gicc_rpl_reg_bisim_axiom |> SPEC_ALL |> UNDISCH 
		         |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL )  >>
      HINT_EXISTS_TAC >>
      EXISTS_TAC ``PSQ`` >>
      EXISTS_TAC ``PRQ`` >>
      HINT_EXISTS_TAC >>
      EXISTS_TAC ``GIC':idgic`` >>
      EXISTS_TAC ``(IM.G (PCG k)).GIC:idgic`` >>
      EXISTS_TAC ``PCC k`` >>
      EXISTS_TAC ``G':gic`` >>
      EXISTS_TAC ``RM.GIC:gic`` >>
      HINT_EXISTS_TAC >>
      EXISTS_TAC ``k:num`` >>
      RW_TAC (srw_ss()) []
      >| [(* good PRQ *)
	  METIS_TAC [good_PRQ_lem]
	  ,
          (* good PSQ *)
	  METIS_TAC [good_PSQ_lem]
	  ,
	  (* good coupling GICDfltr vs PQQ *)
	  `(\g. PRQ g o PSQ g) = PQQ` by (
	      RW_TAC std_ss [GSYM PQQ_def, ETA_THM]
	  ) >>
	  ASM_REWRITE_TAC [gicdfltr_pistate_axiom]
	  ,
          (* gicc and gicv equal *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  METIS_TAC [bisim_gicc_reg_def]
	  ,
	  (* Q and VI equal *)
	  METIS_TAC [virq_guest_mode_lem]
	  ,
	  (* volatile gicd registers filtered *)
	  METIS_TAC [bisim_gicd_reg_vol_lem]
	  ,
	  (* 13 LSBs of addresses equal *)
	  RW_TAC std_ss [compare_13_lsb] 
	  >| [(* case: Padr ' 0 equal *)
	      RW_TAC (srw_ss()) [Adr_Trreq_ipat_lem, ipat_def, 
				 PAdr_extract_lem] >>
	      FULL_SIMP_TAC (srw_ss()) [PAdr_def, Trreq_def, ATrans_def] >>
	      METIS_TAC [Trans_axiom]
	      , 
	      (* case: bx the same *)
	      RW_TAC (srw_ss()) [Adr_Trreq_ipat_lem, ipat_def, bx_extract_lem]
	     ]
	  ,
	  (* requests xlated *)
	  METIS_TAC [xlated_req_Trreq_lem]
	 ]
  ) >>
  `q' = Trrpl (PCG k) r` by (
      `good_rpl r /\ good_rpl q'` by ( METIS_TAC [good_match_lem] ) >>
      `Rpl_PAdr q' = ATrans (PCG k) (Rpl_PAdr r)` by (
          FULL_SIMP_TAC (srw_ss()) [ATrans_def] >>
	  IMP_RES_TAC match_PAdr_eq_lem >>
	  FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_Trans_lem] >>
	  IMP_RES_TAC Trrpl_PAdr_ATrans_lem >>
	  FULL_SIMP_TAC (srw_ss()) [ATrans_def] >>
	  METIS_TAC []
      ) >> 
      METIS_TAC [Trrpl_xlated_ATrans_lem]
  ) >>
  RW_TAC (srw_ss()) [] >>
  METIS_TAC [mem_rcv_rpl_enabled_axiom]
);


val refined_gicv_rpl_step_lem = store_thm("refined_gicv_rpl_step_lem", ``
!RM IM k GIC' m' q r.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ gic_step_snd_rpl(RM.GIC, Trrpl (PCG k) r,CoreSender k,GIC')
/\ mem_step_rcv_rpl (RM.m, Trrpl (PCG k) r,CoreSender k,m')
/\ (Trreq (PCG k) q, CoreSender k) IN mem_req_sent RM.m
/\ match (Trreq (PCG k) q, Trrpl (PCG k) r)
/\ match (q,r)
/\ Rpl_PAdr (Trrpl (PCG k) r) IN RPAR.Amap GICV
/\ PAdr q IN RPAR.Amap GICC
==>
?gic' M'.
  idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,gic') /\
  mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),M')
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC proj_bound_lem >>
  IMP_RES_TAC gicc_trans_lem >>
  `PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by ( 
      METIS_TAC [Trreq_PAdr_Trans_lem]
  ) >>
  `IS_SOME (Trans (PCG k) (Rpl_PAdr r))` by (
      IMP_RES_TAC match_IS_SOME_Trans_lem 
  ) >>
  `Rpl_PAdr r IN RPAR.Amap GICC` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `(Trreq (PCG k) q, CoreSender k) IN gic_req_rcvd RM.GIC` by (
      METIS_TAC [gic_good_rpl_axiom, unique_match_thm]
  ) >>
  `PAdr q <> Agicd` by ( 
      METIS_TAC [singleAR_disj_EXPAND, not_in_GICD_not_Agicd_lem]
  ) >>
  `(q, CoreSender (PCC k)) IN mem_req_sent (IM.G (PCG k)).m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_memreq_def
  ) >>
  `(q, CoreSender (PCC k)) IN idgic_req_rcvd (IM.G (PCG k)).GIC` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_giccreq_def 
  ) >>
  `Mode (RM.C k) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  (* show that GIC can send reply and that it is Trrpl (PCG k) r *) 
  `?G' q'.
      idgic_step_snd_rpl((IM.G (PCG k)).GIC,q',CoreSender (PCC k),PCG k,G') 
   /\ match (q,q')` by (
      METIS_TAC [idgic_step_axiom // "snd_rpl_enabled"]
  ) >>
  `xlated_rpl(q',Trrpl (PCG k) r)` by ( 
      MATCH_MP_TAC ( gicc_rpl_reg_bisim_axiom |> SPEC_ALL |> UNDISCH 
		         |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL ) >>
      HINT_EXISTS_TAC >>		
      EXISTS_TAC ``PSQ`` >>
      EXISTS_TAC ``PRQ`` >>
      HINT_EXISTS_TAC >>
      EXISTS_TAC ``G':idgic`` >>
      EXISTS_TAC ``(IM.G (PCG k)).GIC:idgic`` >>
      EXISTS_TAC ``PCC k`` >>
      EXISTS_TAC ``GIC':gic`` >>
      EXISTS_TAC ``RM.GIC:gic`` >>
      HINT_EXISTS_TAC >>
      EXISTS_TAC ``k:num`` >>
      RW_TAC (srw_ss()) []
      >| [(* good PRQ *)
	  METIS_TAC [good_PRQ_lem]
	  ,
          (* good PSQ *)
	  METIS_TAC [good_PSQ_lem]
	  ,
	  (* good coupling GICDfltr vs PQQ *)
	  `(\g. PRQ g o PSQ g) = PQQ` by (
	      RW_TAC std_ss [GSYM PQQ_def, ETA_THM]
	  ) >>
	  ASM_REWRITE_TAC [gicdfltr_pistate_axiom]
	  ,
          (* gicc and gicv equal *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  METIS_TAC [bisim_gicc_reg_def]
	  ,
	  (* Q and VI equal *)
	  METIS_TAC [virq_guest_mode_lem]
	  ,
	  (* volatile gicd registers filtered *)
	  METIS_TAC [bisim_gicd_reg_vol_lem]
	  ,
	  (* 13 LSBs of addresses equal *)
	  RW_TAC std_ss [compare_13_lsb] 
	  >| [(* case: Padr ' 0 equal *)
	      RW_TAC (srw_ss()) [Adr_Trreq_ipat_lem, ipat_def, 
				 PAdr_extract_lem] >>
	      FULL_SIMP_TAC (srw_ss()) [PAdr_def, Trreq_def, ATrans_def] >>
	      METIS_TAC [Trans_axiom]
	      , 
	      (* case: bx the same *)
	      RW_TAC (srw_ss()) [Adr_Trreq_ipat_lem, ipat_def, bx_extract_lem]
	     ]
	  ,
	  (* requests xlated *)
	  METIS_TAC [xlated_req_Trreq_lem]
	 ]
  ) >>
  `good_rpl r /\ good_rpl q'` by ( METIS_TAC [good_match_lem] ) >>
  `xlated_rpl (r, Trrpl (PCG k) r)` by ( METIS_TAC [xlated_rpl_Trrpl_lem] ) >>
  `xlated_rpl (Trrpl (PCG k) r, r)` by ( METIS_TAC [xlated_rpl_sym_lem] ) >>
  `xlated_rpl (q', r)` by ( METIS_TAC [xlated_rpl_trans_lem] ) >>
  `q' = r` by (
      `Rpl_PAdr q' = Rpl_PAdr r` by (
	  IMP_RES_TAC match_PAdr_eq_lem >>
	  FULL_SIMP_TAC (srw_ss()) []
      ) >> 
      METIS_TAC [rpl_eq_lem]
  ) >>
  RW_TAC (srw_ss()) [] >>
  METIS_TAC [mem_rcv_rpl_enabled_axiom]
);



(* GICC/GICV reply bisim lemmas *)

val gicv_rpl_bisim_lem = store_thm("gicv_rpl_lem", ``
!RM IM c r q:reply GIC' gic'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ c < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG c)).GIC, q,CoreSender (PCC c),PCG c,GIC')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG c) q,CoreSender c,gic')
/\ Rpl_PAdr q IN RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG c) q) IN RPAR.Amap GICV
/\ match (r,q)
/\ match (Trreq (PCG c) r,Trrpl (PCG c) q)
/\ IS_SOME (Trans (PCG c) (PAdr r))
(* /\ IS_SOME (Trans (PCG c) (Rpl_PAdr q)) *)
/\ (Trreq (PCG c) r,CoreSender c) IN mem_req_sent RM.m
==>
   xlated_rpl (q,Trrpl (PCG c) q) 
/\ (!R. (idgic_abs GIC').gicc (PCC c) R = (gic_abs gic').gicv c R) 
/\ (!q. (idgic_abs GIC').Q (PCC c) (PRQ (PCG c) q) = VI gic' c q) 
/\ (!R. (idgic_abs GIC').gicd (VOL R) =
        GICDfltr (PCG c,VOL R,(gic_abs gic').gicd (VOL R)))
/\ !g' R. g' < PAR.ng /\ g' <> (PCG c) ==>
       (GICDfltr (g',VOL R,(gic_abs gic').gicd (VOL R)) =
        GICDfltr (g',VOL R,(gic_abs RM.GIC).gicd (VOL R)))
``,
  REPEAT GEN_TAC >>				   
  STRIP_TAC >>
  IMP_RES_TAC proj_bound_lem >>
  `good_prq PRQ` by ( METIS_TAC [good_PRQ_lem] ) >>
  `good_psq PSQ` by ( METIS_TAC [good_PSQ_lem] ) >>
  `gicdfltr_pqq_coupling (GICDfltr,(λg. PRQ g ∘ PSQ g))` by (
      `(\g. PRQ g o PSQ g) = PQQ` by (
         RW_TAC std_ss [GSYM PQQ_def, ETA_THM]
      ) >>
      ASM_REWRITE_TAC [gicdfltr_pistate_axiom]
  ) >>
  `!R. (idgic_abs (IM.G (PCG c)).GIC).gicc (PCC c) R = 
       (gic_abs RM.GIC).gicv c R` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_gicc_reg_def]
  ) >>
  `PAdr r IN RPAR.Amap GICC /\ PAdr (Trreq (PCG c) r) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C c) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  `!q. (idgic_abs (IM.G (PCG c)).GIC).Q (PCC c) (PRQ (PCG c) q) = 
       VI RM.GIC c q` by (
      METIS_TAC [virq_guest_mode_lem]
  ) >>
  `!R. (idgic_abs (IM.G (PCG c)).GIC).gicd (VOL R) =
       GICDfltr (PCG c,VOL R,(gic_abs RM.GIC).gicd (VOL R))` by (
      METIS_TAC [bisim_gicd_reg_vol_lem]
  ) >>
  `((12 >< 0) (Adr r)):bool[13] = (12 >< 0) (Adr (Trreq (PCG c) r))` by ( 
      RW_TAC std_ss [compare_13_lsb]
      >| [(* case: Padr ' 0 equal *)
	  RW_TAC (srw_ss()) [Adr_Trreq_ipat_lem, ipat_def, 
			     PAdr_extract_lem] >>
          FULL_SIMP_TAC (srw_ss()) [PAdr_def, Trreq_def, ATrans_def] >>
	  METIS_TAC [Trans_axiom]
	  , 
	  (* case: bx the same *)
	  RW_TAC (srw_ss()) [Adr_Trreq_ipat_lem, ipat_def, bx_extract_lem]
	 ]
  ) >>
  `xlated (r, Trreq (PCG c) r)` by ( METIS_TAC [xlated_req_Trreq_lem] ) >>
  METIS_TAC [gicc_rpl_reg_bisim_axiom]
);


val gicv_rpl_bisim_perirq_lem = store_thm("gicv_rpl_bisim_perirq_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
bisim_perirq (RM',IM')
``,
  RW_TAC (srw_ss()) [] >>
  `!q. (idgic_abs GIC').Q (PCC k) (PRQ (PCG k) q) = VI gic' k q` by (
      METIS_TAC [gicv_rpl_bisim_lem]
  ) >>
  `PAdr q IN RPAR.Amap GICC /\ PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C k) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  RW_TAC (srw_ss()) [bisim_perirq_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `k = c`
  >| [(* case: k = c *)
      RW_TAC (srw_ss()) [nuvi_guest_mode_K_lem] >>
      RW_TAC (srw_ss()) [bisim_perirq_core_def, combinTheory.K_THM] >>
      `(idgic_abs GIC').Q (PCC c) (PRQ (PCG c) (PIR id)) =
       VI gic' c (PIR id)` by ( METIS_TAC [] ) >>
      FULL_SIMP_TAC (srw_ss()) [PRQ_def] >>
      CASE_TAC 
      ,
      (* case: k <> c *) 
      RW_TAC (srw_ss()) [PCG_PCC_inj]
      >| [(* case: same guest *)
	  `PCC k <> PCC c` by ( METIS_TAC [PCG_PCC_inj] ) >>
	  `(idgic_abs GIC').Q (PCC c) = 
           (idgic_abs (IM.G (PCG k)).GIC).Q (PCC c)` by (
	      METIS_TAC [idgic_step_axiom // "snd_rpl_gicc"]
	  )
	  ,
	  (* case: other guest *)
	  ALL_TAC
	 ] >> (
          `VI gic' c = VI RM.GIC c` by (
              METIS_TAC [gic_gicv_rpl_axiom, VI_def]
          ) >>
          IMP_RES_TAC mem_rcv_rpl_axiom >>
          RW_TAC (srw_ss()) [bisim_perirq_core_def] >>
          RW_TAC std_ss [nuvi_other_core_reply_lem] >> (
             FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
             IMP_RES_TAC bisim_perirq_def >>
             METIS_TAC [bisim_perirq_core_def]
          )
      )
     ]
);


val gicv_rpl_bisim_sgiirq_lem = store_thm("gicv_rpl_bisim_sgiirq_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
bisim_sgiirq(RM',IM')
``,
  RW_TAC (srw_ss()) [] >>
  `!q. (idgic_abs GIC').Q (PCC k) (PRQ (PCG k) q) = VI gic' k q` by (
      METIS_TAC [gicv_rpl_bisim_lem]
  ) >>
  `PAdr q IN RPAR.Amap GICC /\ PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C k) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  RW_TAC (srw_ss()) [bisim_sgiirq_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `k = c`
  >| [(* case: k = c *)
      RW_TAC (srw_ss()) [nuvi_guest_mode_K_lem] >>
      RW_TAC (srw_ss()) [bisim_sgiirq_core_def, combinTheory.K_THM] >>
      CASE_TAC 
      ,
      (* case: k <> c *) 
      RW_TAC (srw_ss()) [PCG_PCC_inj]
      >| [(* case: same guest *)
	  `PCC k <> PCC c` by ( METIS_TAC [PCG_PCC_inj] ) >>
	  `(idgic_abs GIC').Q (PCC c) = 
           (idgic_abs (IM.G (PCG k)).GIC).Q (PCC c)` by (
	      METIS_TAC [idgic_step_axiom // "snd_rpl_gicc"]
	  )
	  ,
	  (* case: other guest *)
	  ALL_TAC
	 ] >> (
          `VI gic' c = VI RM.GIC c` by (
              METIS_TAC [gic_gicv_rpl_axiom, VI_def]
          ) >>
          IMP_RES_TAC mem_rcv_rpl_axiom >>
          RW_TAC (srw_ss()) [bisim_sgiirq_core_def] >>
          RW_TAC std_ss [nuvi_other_core_reply_lem] >> (
             FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
             IMP_RES_TAC bisim_sgiirq_def >>
             METIS_TAC [bisim_sgiirq_core_def]
          )
      )
     ]
);

val gicv_rpl_bisim_igcirq_lem = store_thm("gicv_rpl_bisim_igcirq_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
bisim_igcirq(RM',IM')
``,
  RW_TAC (srw_ss()) [] >>
  `!q. (idgic_abs GIC').Q (PCC k) (PRQ (PCG k) q) = VI gic' k q` by (
      METIS_TAC [gicv_rpl_bisim_lem]
  ) >>
  `PAdr q IN RPAR.Amap GICC /\ PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C k) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  RW_TAC (srw_ss()) [bisim_igcirq_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `k = c`
  >| [(* case: k = c *)
      RW_TAC (srw_ss()) [nuigc_guest_mode_K_lem] >>
      RW_TAC (srw_ss()) [bisim_igcirq_core_def, combinTheory.K_THM] >>
      `(idgic_abs GIC').Q (PCC c) (PRQ (PCG c) (PIR id)) =
       VI gic' c (PIR id)` by ( METIS_TAC [] ) >>
      FULL_SIMP_TAC (srw_ss()) [PRQ_def] >>
      CASE_TAC 
      ,
      (* case: k <> c *) 
      RW_TAC (srw_ss()) [PCG_PCC_inj]
      >| [(* case: same guest *)
	  `PCC k <> PCC c` by ( METIS_TAC [PCG_PCC_inj] ) >>
	  `(idgic_abs GIC').Q (PCC c) = 
           (idgic_abs (IM.G (PCG k)).GIC).Q (PCC c)` by (
	      METIS_TAC [idgic_step_axiom // "snd_rpl_gicc"]
	  )
	  ,
	  (* case: other guest *)
	  ALL_TAC
	 ] >> (
          `VI gic' c = VI RM.GIC c` by (
              METIS_TAC [gic_gicv_rpl_axiom, VI_def]
          ) >>
          IMP_RES_TAC mem_rcv_rpl_axiom >>
          RW_TAC (srw_ss()) [bisim_igcirq_core_def] >>
          RW_TAC std_ss [nuigc_other_core_reply_lem] >> (
             FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
             IMP_RES_TAC bisim_igcirq_def >>
             METIS_TAC [bisim_igcirq_core_def]
          )
      )
     ]
);


val gicv_rpl_bisim_send_igc_lem = store_thm("gicv_rpl_bisim_send_igc_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
bisim_send_igc(RM',IM')
``,
  RW_TAC (srw_ss()) [] >>
  `!id s r. Q gic' (SGI (id, s, r)) = Q RM.GIC (SGI (id, s, r))` by (
      METIS_TAC [gicv_rpl_Q_sgi_lem]
  ) >>
  `PAdr q IN RPAR.Amap GICC /\ PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C k) < 2` by ( 
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  RW_TAC (srw_ss()) [bisim_send_igc_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `k = c'`
  >| [(* case: k = c *)
      RW_TAC (srw_ss()) [bisim_send_igc_core_def]
      >| [(* mbox *)
          IMP_RES_TAC mem_rcv_rpl_axiom >>
	  FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_send_igc_def >>
	  FULL_SIMP_TAC (srw_ss()) [bisim_send_igc_core_def]
	  ,
	  (* address book *)
	  IMP_RES_TAC mem_rcv_rpl_axiom >>
	  FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_send_igc_def >>
	  IMP_RES_TAC proj_bound_lem >>
	  FULL_SIMP_TAC (srw_ss()) [bisim_send_igc_core_def] >>
	  METIS_TAC [nusgi_other_core_reply_lem] 
	 ]
      ,
      (* case: k <> c *) 
      RW_TAC (srw_ss()) [bisim_send_igc_core_def]
      >| [(* mbox *)
	  RW_TAC (srw_ss()) [PCG_PCC_inj] >> (
              IMP_RES_TAC mem_rcv_rpl_axiom >>
	      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_send_igc_def >>
	      FULL_SIMP_TAC (srw_ss()) [bisim_send_igc_core_def]
	  )
	  ,
	  (* address book *)
	  RW_TAC (srw_ss()) [PCG_PCC_inj] >> (
	      IMP_RES_TAC mem_rcv_rpl_axiom >>
	      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_send_igc_def >>
	      IMP_RES_TAC proj_bound_lem >>
	      FULL_SIMP_TAC (srw_ss()) [bisim_send_igc_core_def] >>
	      METIS_TAC [nusgi_guest_mode_lem,
			 nusgi_other_core_reply_lem] 
	  )
	 ]
     ]
);


val gicv_rpl_bisim_pi_lem = store_thm("gicv_rpl_bisim_pi_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
bisim_pi(RM',IM')
``,
  RW_TAC (srw_ss()) [] >>
  `(!R. (idgic_abs GIC').gicd (VOL R) =
        GICDfltr (PCG k,VOL R,(gic_abs gic').gicd (VOL R))) /\
   !g' R. g' < PAR.ng /\ g' <> PCG k ==>
       (GICDfltr (g',VOL R,(gic_abs gic').gicd (VOL R)) =
        GICDfltr (g',VOL R,(gic_abs RM.GIC).gicd (VOL R)))` by (
      METIS_TAC [gicv_rpl_bisim_lem]
  ) >>
  `PAdr q IN RPAR.Amap GICC /\ PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C k) < 2` by (
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  IMP_RES_TAC proj_bound_lem >>
  (* IMP_RES_TAC bisim_gicd_reg_guest_mode_lem >> *)
  `gicdfltr_pqq_coupling(GICDfltr,PQQ)` by ( 
      METIS_TAC [gicdfltr_pistate_axiom]
  ) >>
  RW_TAC (srw_ss()) [bisim_pi_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `PCG k = g`
  >| [(* case: PCG k = g *)
      RW_TAC (srw_ss()) [bisim_pi_guest_def, PI_def] >> (
          `PQQ (PCG k) q' IN PIRQ (PCG k) UNION IPIRQ (PCG k)` by (
	      FULL_SIMP_TAC (srw_ss()) []
	  ) >>
	  `PQQ (PCG k) q' IN PIRQ (PCG k) ==> 
	   PQQ (PCG k) q' NOTIN IPIRQ (PCG k)` by (
	      METIS_TAC [PIRQ_IPIRQ_disjoint_lem, pred_setTheory.IN_DISJOINT]
	  ) >>
	  `PQQ (PCG k) q' IN IPIRQ (PCG k) ==> 
	   PQQ (PCG k) q' NOTIN PIRQ (PCG k)` by (
	      METIS_TAC [PIRQ_IPIRQ_disjoint_lem, pred_setTheory.IN_DISJOINT]
	  ) >>
	  RES_TAC >>
          IMP_RES_TAC gicdfltr_pqq_coupling_def >>
	  ASM_REWRITE_TAC [Q_def] >>
	  CASE_TAC
      )
      ,
      (* case: PCG k <> c *) 
      `!R. (idgic_abs (IM.G g).GIC).gicd (VOL R) =
           GICDfltr (g,VOL R,(gic_abs gic').gicd (VOL R))` by (
          METIS_TAC [bisim_gicd_reg_vol_lem]
      ) >>
      RW_TAC (srw_ss()) [bisim_pi_guest_def, PI_def] >> (
          `PQQ g q' IN PIRQ g UNION IPIRQ g` by (
	      FULL_SIMP_TAC (srw_ss()) []
	  ) >>
	  `PQQ g q' IN PIRQ g ==> 
	   PQQ g q' NOTIN IPIRQ g` by (
	      METIS_TAC [PIRQ_IPIRQ_disjoint_lem, pred_setTheory.IN_DISJOINT]
	  ) >>
	  `PQQ g q' IN IPIRQ g ==> 
	   PQQ g q' NOTIN PIRQ g` by (
	      METIS_TAC [PIRQ_IPIRQ_disjoint_lem, pred_setTheory.IN_DISJOINT]
	  ) >>
	  RES_TAC >>
          IMP_RES_TAC gicdfltr_pqq_coupling_def >>
	  ASM_REWRITE_TAC [Q_def] >>
	  CASE_TAC
      )
     ]
);

val gicv_rpl_reg_bisim_lem = store_thm("gicc_rpl_reg_bisim_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
!R c. c < RPAR.nc /\ (PCG c = PCG k) ==> 
      ((idgic_abs GIC').gicc (PCC c) R = (gic_abs gic').gicv c R)
``,
  RW_TAC (srw_ss()) [] >>
  Cases_on `k = c` 
  >| [(* k = c *)
      METIS_TAC [gicv_rpl_bisim_lem]
      ,
      (* k <> c *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_gicc_reg_def >>
      `PCC k <> PCC c` by ( METIS_TAC [PCG_PCC_inj] ) >>
      METIS_TAC [gic_gicv_rpl_axiom, idgic_step_axiom // "snd_rpl_gicc"]
     ]
);

val gicv_rpl_bisim_gicd_reg_lem = store_thm("gicc_rpl_bisim_gicd_reg_lem", ``
!RM IM RM' IM' k q r GIC' m' gic' M'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ k < RPAR.nc
/\ idgic_step_snd_rpl((IM.G (PCG k)).GIC,r,CoreSender (PCC k),PCG k,GIC')
/\ mem_step_rcv_rpl ((IM.G (PCG k)).m,r,CoreSender (PCC k),m')
/\ gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
/\ mem_step_rcv_rpl (RM.m,Trrpl (PCG k) r,CoreSender k,M')
/\ Rpl_PAdr r ∈ RPAR.Amap GICC
/\ Rpl_PAdr (Trrpl (PCG k) r) ∈ RPAR.Amap GICV
/\ match (q,r)
/\ match (Trreq (PCG k) q,Trrpl (PCG k) r)
/\ IS_SOME (Trans (PCG k) (PAdr q))
/\ IS_SOME (Trans (PCG k) (Rpl_PAdr r))
/\ (q,CoreSender (PCC k)) ∈ mem_req_sent (IM.G (PCG k)).m
/\ (Trreq (PCG k) q,CoreSender k) ∈ mem_req_sent RM.m
/\ (RM' = RM with <|m := M'; GIC := gic'|>)
/\ (IM' = <|G := (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>)
==>
bisim_gicd_reg(RM',IM')
``,
  RW_TAC (srw_ss()) [] >>
  `(!R. (idgic_abs GIC').gicd (VOL R) =
        GICDfltr (PCG k,VOL R,(gic_abs gic').gicd (VOL R))) /\
   !g' R. g' < PAR.ng /\ g' <> PCG k ==>
       (GICDfltr (g',VOL R,(gic_abs gic').gicd (VOL R)) =
        GICDfltr (g',VOL R,(gic_abs RM.GIC).gicd (VOL R)))` by (
      METIS_TAC [gicv_rpl_bisim_lem]
  ) >>
  `PAdr q IN RPAR.Amap GICC /\ PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  `Mode (RM.C k) < 2` by (
      METIS_TAC [gicv_req_mode_lem]
  ) >>
  IMP_RES_TAC proj_bound_lem >>
  IMP_RES_TAC bisim_gicd_reg_guest_mode_lem >>
  RW_TAC (srw_ss()) [bisim_gicd_reg_def, combinTheory.APPLY_UPDATE_THM,
		     req_gicd_F_lem] >>
  Cases_on `PCG k = g`
  >| [(* PCG k = g*)
      RW_TAC (srw_ss()) []
      >| [(* VOL *)
	  METIS_TAC []
	  ,
	  (* CONST / MUTE *)
	  IMP_RES_TAC mem_rcv_rpl_axiom >>
	  RW_TAC (srw_ss()) [] >>
	  `!R. (idgic_abs GIC').gicd (CONST R) = 
               (idgic_abs (IM.G (PCG k)).GIC).gicd (CONST R)` by (
	      METIS_TAC [idgic_step_axiom // "snd_rpl_gicc"]
	  ) >>
	  `!R. (idgic_abs GIC').gicd (MUTE R) = 
               (idgic_abs (IM.G (PCG k)).GIC).gicd (MUTE R)` by (
	      METIS_TAC [idgic_step_axiom // "snd_rpl_gicc"]
	  ) >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  IMP_RES_TAC ( bisim_gicd_reg_def 
			    |> SIMP_RULE std_ss [req_gicd_F_lem] ) >>
	  Cases_on `r'` >> (
	      METIS_TAC []
	  )
	 ]
      ,
      RW_TAC (srw_ss()) []
      >| [(* VOL *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  IMP_RES_TAC ( bisim_gicd_reg_def 
			    |> SIMP_RULE std_ss [req_gicd_F_lem] ) >>
	  METIS_TAC []
	  ,
	  (* CONST / MUTE *)
	  IMP_RES_TAC mem_rcv_rpl_axiom >>
	  RW_TAC (srw_ss()) [] >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  IMP_RES_TAC ( bisim_gicd_reg_def 
			    |> SIMP_RULE std_ss [req_gicd_F_lem] ) >>
	  Cases_on `r'` >> (
	      METIS_TAC []
	  )
	 ]
     ]
);


(* SimInvR lemmas *)

val SimInvR_no_req_mode_lem = store_thm("SimInvR_no_req_mode_lem", ``
!RM IM g cg c.
   g < PAR.ng
/\ cg < PAR.nc_g g
/\ c < RPAR.nc
/\ SIM (RM,IM)
/\ SimInvR RM
/\ InvI IM
/\ InvR RM
/\ (idcore_abs((IM.G g).C cg)).active
/\ (idcore_req_sent ((IM.G g).C cg) = EMPTY)
/\ (PCG c = g) /\ (PCC c = cg)
==>
Mode (RM.C c) < 2
``,
  RW_TAC (srw_ss()) [SimInvR_def] >>
  RES_TAC 
  >| [(* case: GICD_SAVE_CTX *)
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      `bisim_corereq_gicd_core(RM.C c,(IM.G (PCG c)).C (PCC c), HVabs (RM,c))` 
      by ( FULL_SIMP_TAC (srw_ss()) [bisim_corereq_gicd_def] ) >>
      IMP_RES_TAC bisim_corereq_gicd_core_def >>
      REV_FULL_SIMP_TAC (srw_ss()) [pred_setTheory.NOT_IN_EMPTY]
      ,
      (* case: GICD_FILTER *) 
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      `bisim_corereq_gicd_core(RM.C c,(IM.G (PCG c)).C (PCC c), HVabs (RM,c))` 
      by ( FULL_SIMP_TAC (srw_ss()) [bisim_corereq_gicd_def] ) >>
      IMP_RES_TAC bisim_corereq_gicd_core_def >>
      REV_FULL_SIMP_TAC (srw_ss()) [pred_setTheory.NOT_IN_EMPTY]
      ,
      (* case: reset *)
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      `(refcore_abs (RM.C c)).H.launched` by (
          FULL_SIMP_TAC (srw_ss()) [bisim_ctx_def] >>
	  RES_TAC >> (
	      IMP_RES_TAC bisim_ctx_core_def >>
	      METIS_TAC []
	  )
      ) >>
      METIS_TAC [Creset_axiom]
      ,
      (* case: soft boot *)
      `mode (refcore_abs(RM.C c)) = 3` by (
          RW_TAC (srw_ss()) [warm_soft_axiom]
      ) >>
      `(idcore_abs((IM.G (PCG c)).C (PCC c))).H.launch` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND, bisim_ctx_def] >>
	  RES_TAC >> ( IMP_RES_TAC bisim_ctx_core_def )
      ) >>
      `~(idcore_abs((IM.G (PCG c)).C (PCC c))).active` by (
          `inv_good_idcore ((IM.G (PCG c)).C (PCC c))` by (
              `idg_inv(IM.G (PCG c), PCG c, IDG_GOOD_IDCORE)` by (
	          IMP_RES_TAC InvI_def >>
	          FULL_SIMP_TAC (srw_ss()) [InvG_def]
	      ) >>
	      FULL_SIMP_TAC (srw_ss()) [idg_inv_def]
          ) >>
	  IMP_RES_TAC inv_good_idcore_def
      )
     ]
);

val SimInvR_req_mode_lem = store_thm("SimInvR_req_mode_lem", ``
!RM IM c r.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ SimInvR RM
/\ InvI IM
/\ InvR RM
/\ (idcore_abs((IM.G (PCG c)).C (PCC c))).active
/\ r IN idcore_req_sent ((IM.G (PCG c)).C (PCC c))
/\ PAdr r <> Agicd
==>
Mode (RM.C c) < 2
``,
  RW_TAC (srw_ss()) [SimInvR_def] >>
  IMP_RES_TAC proj_bound_lem >>
  RES_TAC 
  >| [(* case: GICD_SAVE_CTX *)
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      `bisim_corereq_gicd_core(RM.C c, 
			       (IM.G (PCG c)).C (PCC c), 
			       HVabs (RM,c))` by ( 
          METIS_TAC [bisim_corereq_gicd_def]
      ) >>
      IMP_RES_TAC bisim_corereq_gicd_core_def >>
      REV_FULL_SIMP_TAC (srw_ss()) [] >>
      `r' = r` by (
          FULL_SIMP_TAC (srw_ss()) [pred_setTheory.IN_SING]
      ) >>
      FULL_SIMP_TAC (srw_ss()) []
      ,
      (* case: GICD_FILTER *) 
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      `bisim_corereq_gicd_core(RM.C c, 
			       (IM.G (PCG c)).C (PCC c), 
			       HVabs (RM,c))` by ( 
          METIS_TAC [bisim_corereq_gicd_def]
      ) >>
      IMP_RES_TAC bisim_corereq_gicd_core_def >>
      REV_FULL_SIMP_TAC (srw_ss()) [] >>
      `r' = r` by (
          FULL_SIMP_TAC (srw_ss()) [pred_setTheory.IN_SING]
      ) >>
      FULL_SIMP_TAC (srw_ss()) []
      ,
      (* case: reset *)
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      `(refcore_abs (RM.C c)).H.launched` by (
          IMP_RES_TAC bisim_ctx_def >>
          `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active 
           ==>
	   (refcore_abs (RM.C c)).H.launched` by (
	      METIS_TAC [bisim_ctx_core_def]
	  ) >>
	  RW_TAC (srw_ss()) [PCGC_inv_rewrites]
      ) >>
      METIS_TAC [Creset_axiom]
      ,
      (* case: soft boot *)
      `mode (refcore_abs(RM.C c)) = 3` by (
          RW_TAC (srw_ss()) [warm_soft_axiom]
      ) >>
      `(idcore_abs(
	(IM.G (PCG c)).C (PCC c))).H.launch` by (
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_ctx_def >>
	  FULL_SIMP_TAC (srw_ss()) [bisim_ctx_core_def]
      ) >>
      `inv_good_idcore (
          (IM.G (PCG c)).C (PCC c))` by (
          `idg_inv(IM.G (PCG c), PCG c, IDG_GOOD_IDCORE)` by (
	      IMP_RES_TAC InvI_def >>
	      FULL_SIMP_TAC (srw_ss()) [InvG_def]
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [idg_inv_def]
      ) >>
      `idcore_req_sent(
	 (IM.G (PCG c)).C (PCC c)) = EMPTY` by (
	  IMP_RES_TAC inv_good_idcore_def >>
	  REV_FULL_SIMP_TAC (srw_ss()) []
      ) >>
      METIS_TAC [pred_setTheory.NOT_IN_EMPTY]
     ]
);

val mmu_guest_send_lem = store_thm("mmu_guest_send_lem", ``
!RM c r MMU'.
   c < RPAR.nc
/\ InvR RM
/\ SimInvR RM
/\ (mmu_abs (RM.MMU c)).active
/\ mmu_step_snd_req (RM.MMU c, Trreq (PCG c) r,MMU')
==>
   req_aligned (Trreq (PCG c) r)
/\ (mmu_req_sent MMU' = mmu_req_sent(RM.MMU c) UNION {Trreq (PCG c) r})
/\ Trreq (PCG c) r NOTIN mmu_req_sent(RM.MMU c) 
/\ ((mmu_abs MMU').state r = FINAL (SOME (Trreq (PCG c) r))) 
/\ xlated (r,Trreq (PCG c) r)
/\ ((mmu_abs(RM.MMU c)).state r = FINAL NONE)
/\ (!r'. r' <> r ==>
         ((mmu_abs MMU').state r' = (mmu_abs(RM.MMU c)).state r') 
      /\ (mmu_abs(RM.MMU c)).state r' <> TRANS (SOME (Trreq (PCG c) r)) 
      /\ (mmu_abs(RM.MMU c)).state r' <> FINAL (SOME (Trreq (PCG c) r)))
/\ (!q. q IN mmu_rpl_rcvd(RM.MMU c) ==> ~match ((Trreq (PCG c) r),q))
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd(RM.MMU c)) 
/\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd(RM.MMU c)) 
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist(RM.MMU c)) 
/\ (mmu_abs MMU').active
/\ ((mmu_abs MMU').cfg = (mmu_abs(RM.MMU c)).cfg)
``,
  REPEAT GEN_TAC >> STRIP_TAC >>
  IMP_RES_TAC proj_bound_lem >>
  `!r' l. (mmu_abs (RM.MMU c)).state r' <> TRANS l` by (
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      METIS_TAC [MMUstate_distinct]
  ) >>
  IMP_RES_TAC mmu_send_axiom 
  >| [(* case: FINAL *)
      `   (Trreq (PCG c) r = Trreq (PCG c) r') 
       /\ IS_SOME (Trans (PCG c) (PAdr r'))` by (
          MATCH_MP_TAC golden_mmu_Trreq_lem >>
	  METIS_TAC []
      ) >>
      `r = r'` by (
          METIS_TAC [Trreq_eq_req_lem]
      ) >>
      RW_TAC (srw_ss()) [xlated_req_Trreq_lem]
      ,
      (* case: TRANS => contradiction *)
      METIS_TAC []
     ]
);   

val smmu_guest_send_lem = store_thm("smmu_guest_send_lem", ``
!RM p r SMMU'.
   p < RPAR.np
/\ InvR RM
/\ SimInvR RM
/\ (mmu_abs (RM.SMMU p)).active
/\ mmu_step_snd_req (RM.SMMU p, Trreq (PPG p) r,SMMU')
==>
   req_aligned (Trreq (PPG p) r)
/\ (mmu_req_sent SMMU' = mmu_req_sent(RM.SMMU p) UNION {Trreq (PPG p) r})
/\ Trreq (PPG p) r NOTIN mmu_req_sent(RM.SMMU p) 
/\ ((mmu_abs SMMU').state r = FINAL (SOME (Trreq (PPG p) r))) 
/\ xlated (r,Trreq (PPG p) r)
/\ ((mmu_abs(RM.SMMU p)).state r = FINAL NONE)
/\ (!r'. r' <> r ==>
         ((mmu_abs SMMU').state r' = (mmu_abs(RM.SMMU p)).state r') 
      /\ (mmu_abs(RM.SMMU p)).state r' <> TRANS (SOME (Trreq (PPG p) r)) 
      /\ (mmu_abs(RM.SMMU p)).state r' <> FINAL (SOME (Trreq (PPG p) r)))
/\ (!q. q IN mmu_rpl_rcvd(RM.SMMU p) ==> ~match ((Trreq (PPG p) r),q))
/\ (mmu_req_rcvd SMMU' = mmu_req_rcvd(RM.SMMU p)) 
/\ (mmu_rpl_rcvd SMMU' = mmu_rpl_rcvd(RM.SMMU p)) 
/\ (mmu_ptl_hist SMMU' = mmu_ptl_hist(RM.SMMU p)) 
/\ (mmu_abs SMMU').active
/\ ((mmu_abs SMMU').cfg = (mmu_abs(RM.SMMU p)).cfg)
``,
  REPEAT GEN_TAC >> STRIP_TAC >>
  IMP_RES_TAC pproj_bound_lem >>
  `!r' l. (mmu_abs (RM.SMMU p)).state r' <> TRANS l` by (
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      METIS_TAC [MMUstate_distinct]
  ) >>
  IMP_RES_TAC mmu_send_axiom 
  >| [(* case: FINAL *)
      `   (Trreq (PPG p) r = Trreq (PPG p) r') 
       /\ IS_SOME (Trans (PPG p) (PAdr r'))` by (
          MATCH_MP_TAC golden_smmu_Trreq_lem >>
	  METIS_TAC []
      ) >>
      `r = r'` by (
          METIS_TAC [Trreq_eq_req_lem]
      ) >>
      RW_TAC (srw_ss()) [xlated_req_Trreq_lem]
      ,
      (* case: TRANS => contradiction *)
      METIS_TAC []
     ]
);   

val SimInvR_smmu_add_eq_mem_cc = store_thm("SimInvR_smmu_add_eq_mem_cc",``
SimInvR (RM with <|m := RM.m; SMMU := (p =+ SMMU') RM.SMMU; 
		   P := (p =+ P') RM.P|>) 
==>
SimInvR (RM with <|SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ P') RM.P|>)
``,
  `RM with <|m := RM.m; SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ P') RM.P|> 
    =
   RM with <|SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ P') RM.P|>` by (
      RW_TAC (srw_ss()) [refined_model_component_equality]
  ) >>
  RW_TAC (srw_ss()) []
);


(* InvI lemmas *)

val ideal_INTERNAL_InvI_lem = store_thm("ideal_per_snd_req_InvI_lem", ``
!a IM g G' IM' IM''.
   InvI IM
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL a, G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
InvI IM'
``,
  RW_TAC std_ss [] >>
  `ideal_model_comp(IM,SUC 0,IM')` by (
      RW_TAC (srw_ss()) [ideal_model_comp_def] >>
      EXISTS_TAC ``C_INTERNAL`` >>
      RW_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def] >>
      METIS_TAC []
   ) >>
  METIS_TAC [InvI_preserve_lem]
);


(* THEOREM: refined invariant preserved *)

val bisim_ctx_lem = store_thm("bisim_ctx_lem", ``
!RM RM' IM IM'. 
   bisim_ctx (RM,IM)
/\ (RM.C = RM'.C)
/\ (mem_abs RM.m = mem_abs RM'.m)
/\ (!g. g < PAR.ng ==> ((IM.G g).C = (IM'.G g).C))
==>
bisim_ctx(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_ctx_def, bisim_ctx_core_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN RES_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [sc_done_IGC_def]
  THEN METIS_TAC []
);

val bisim_mmureq_guest_lem = store_thm("bisim_mmureq_guest_lem", ``
!RM RM' IM IM'. 
   bisim_mmureq_guest (RM,IM)
/\ (RM.MMU = RM'.MMU)
/\ (!c. HVabs(RM,c) = HVabs(RM',c))
/\ (RM.C = RM'.C)
/\ (!g. g < PAR.ng ==> ((IM.G g).cif = (IM'.G g).cif))
==>
bisim_mmureq_guest(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_mmureq_guest_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN  METIS_TAC []
);

val bisim_gicdmsg_ideal_lem = store_thm("bisim_gicdmsg_ideal_lem", ``
!RM RM' IM IM'. 
   bisim_gicdmsg_ideal (RM,IM)
/\ (RM.MMU = RM'.MMU)
/\ (RM.C = RM'.C)
/\ (RM.m = RM'.m)
/\ (!g. g < PAR.ng ==> ((IM.G g).m = (IM'.G g).m))
/\ (!g. g < PAR.ng ==> ((IM.G g).GIC = (IM'.G g).GIC))
/\ (!g. g < PAR.ng ==> ((IM.G g).cif = (IM'.G g).cif))
==>
bisim_gicdmsg_ideal(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_gicdmsg_ideal_def, pend_rpl_def, id_pend_rpl_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN METIS_TAC []
);

val bisim_gicdmsg_refined_lem = store_thm("bisim_gicdmsg_refined_lem", ``
!RM RM' IM IM'. 
   bisim_gicdmsg_refined (RM,IM)
/\ (RM.MMU = RM'.MMU)
/\ (RM.C = RM'.C)
/\ (RM.m = RM'.m)
/\ (!g. g < PAR.ng ==> ((IM.G g).m = (IM'.G g).m))
/\ (!g. g < PAR.ng ==> ((IM.G g).GIC = (IM'.G g).GIC))
/\ (!g. g < PAR.ng ==> ((IM.G g).cif = (IM'.G g).cif))
==>
bisim_gicdmsg_refined(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_gicdmsg_refined_def, pend_rpl_def, id_pend_rpl_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN METIS_TAC []
);

(* TODO: prove minimal nuvi lemma for relevant parts of dependencies *)

val bisim_perirq_lem = store_thm("bisim_perirq_lem", ``
!RM RM' IM IM'. 
   bisim_perirq (RM,IM)
/\ (RM.C = RM'.C)
/\ (RM.GIC = RM'.GIC)
/\ (RM.m = RM'.m)
/\ (RM.MMU = RM'.MMU)
/\ (!g. g < PAR.ng ==> ((IM.G g).GIC = (IM'.G g).GIC))
==>
bisim_perirq(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_perirq_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN METIS_TAC []
);


(* TODO: prove minimal nusgi lemma *)

val bisim_sgiirq_lem = store_thm("bisim_sgiirq_lem", ``
!RM RM' IM IM'. 
   bisim_sgiirq (RM,IM)
/\ (RM.C = RM'.C)
/\ (RM.GIC = RM'.GIC)
/\ (RM.m = RM'.m)
/\ (RM.MMU = RM'.MMU)
/\ (!g. g < PAR.ng ==> ((IM.G g).GIC = (IM'.G g).GIC))
==>
bisim_sgiirq(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_sgiirq_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN METIS_TAC []
);

val bisim_send_igc_lem = store_thm("bisim_send_igc_lem", ``
!RM RM' IM IM'. 
   bisim_send_igc (RM,IM)
/\ (RM.C = RM'.C)
/\ (RM.GIC = RM'.GIC)
/\ (RM.MMU = RM'.MMU)
/\ (RM.m = RM'.m)
/\ (!g. (IM.G g).sIGC = (IM'.G g).sIGC)
/\ (!g. (IM.G g).GIC = (IM'.G g).GIC)
==>
bisim_send_igc(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_send_igc_def] >> 
  FULL_SIMP_TAC (srw_ss()) []
);

val bisim_send_igc_core_step_lem = store_thm("bisim_send_igc_core_step_lem", ``
!RM RM' IM IM'. 
   bisim_send_igc (RM,IM)
/\ (!c. (RM.C c = RM'.C c) \/ 
        ((Mode (RM.C c) <> 2
           \/ (refcore_abs (RM.C c)).PC <> AHV PC_SIGC_RCV_SGI /\
              (refcore_abs (RM.C c)).PC <> AHV PC_RIGC_RCV_DEACT /\
              (refcore_abs (RM.C c)).PC <> AHV PC_RIGC_RETURN)
             /\ 
	 (Mode (RM'.C c) <> 2
	   \/ (refcore_abs (RM'.C c)).PC <> AHV PC_SIGC_RCV_SGI /\
              (refcore_abs (RM'.C c)).PC <> AHV PC_RIGC_RCV_DEACT /\
              (refcore_abs (RM'.C c)).PC <> AHV PC_RIGC_RETURN)
	 /\ ((refcore_abs (RM.C c)).H = (refcore_abs (RM'.C c)).H))
   )
/\ (Q RM.GIC = Q RM'.GIC)
/\ (!c. (RM.MMU c = RM'.MMU c) \/ 
        (mmu_rpl_rcvd (RM.MMU c) = mmu_rpl_rcvd (RM'.MMU c)) \/
        (Mode (RM.C c) <> 2 /\ Mode (RM'.C c) <> 2 ))
/\ (RM.m = RM'.m)
/\ (!g. (IM.G g).sIGC = (IM'.G g).sIGC)
==>
bisim_send_igc(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_send_igc_def, bisim_send_igc_core_def] 
  >- ( METIS_TAC [] ) >>
  `!c.
   nusgi ((λc. RM.C c),(λc. mmu_rpl_rcvd (RM.MMU c)), mem_rpl_rcvd RM.m) (c,c')
    = 
   nusgi ((λc. RM'.C c),(λc. mmu_rpl_rcvd (RM'.MMU c)), mem_rpl_rcvd RM'.m) (c,c')
  ` by (
      FULL_SIMP_TAC (srw_ss()) [nusgi_def] >> METIS_TAC []
  ) >>
  EQ_TAC
  >| [RW_TAC (srw_ss()) [] >>
      `?c. c < RPAR.nc /\ (PCG c = g) /\ c <> c' /\
           (((Q RM.GIC (SGI (7w,c,c')) = PENDING) \/
           (Q RM.GIC (SGI (7w,c,c')) = ACTIVE)) \/
           nusgi
                      ((\c. RM.C c),(\c. mmu_rpl_rcvd (RM.MMU c)),
                       mem_rpl_rcvd RM.m) (c,c') \/
           (Mode (RM.C c') = 2) /\
           (((refcore_abs (RM.C c')).PC = AHV PC_RIGC_RCV_DEACT) \/
           ((refcore_abs (RM.C c')).PC = AHV PC_RIGC_RETURN))) 
      ` by (
          METIS_TAC []
      ) >> ( METIS_TAC [] )
      ,
      METIS_TAC []
     ]
);



(* TODO: prove minimal nuigc lemma *)

val bisim_igcirq_lem = store_thm("bisim_igcirq_lem", ``
!RM RM' IM IM'. 
   bisim_igcirq (RM,IM)
/\ (RM.C = RM'.C)
/\ (RM.GIC = RM'.GIC)
/\ (RM.m = RM'.m)
/\ (RM.MMU = RM'.MMU)
/\ (!g. g < PAR.ng ==> ((IM.G g).GIC = (IM'.G g).GIC))
==>
bisim_igcirq(RM',IM')
``,
  RW_TAC (srw_ss()) [bisim_igcirq_def]
  THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
  THEN METIS_TAC []
);

(*by Thomas Tuerk *)
val SIM_bisim_periph = store_thm ("SIM_bisim_periph",
  ``!RM IM. SIM (RM, IM) ==> !p. p < RPAR.np ==>
      ((RM.P p).st = ((IM.G (PPG p)).P (PPP p)).st)``,
  SIMP_TAC std_ss [SIM_EXPAND, bisim_periph_def]);


(* group used theorems according to where/how we use them in the case distinctions *)
val start_and_metis_lst = [bisim_memory_def, bisim_corereq_guest_def, bisim_smmureq_def, bisim_giccreq_def,  bisim_gicdreq_refined_def, bisim_gicd_fail_def, bisim_memreq_def, bisim_ext_def, bisim_psci_def, bisim_gicc_reg_def, bisim_pi_def];

val start_and_impres_lst = [bisim_gicd_reg_def, bisim_corereq_hyp_def, bisim_corereq_gicd_def, bisim_gicdreq_ideal_def];

val solved_by_impres_only_lst = [bisim_ctx_lem, bisim_mmureq_guest_lem, bisim_gicdmsg_ideal_lem, bisim_gicdmsg_refined_lem, bisim_perirq_lem, bisim_igcirq_lem, bisim_sgiirq_lem, bisim_send_igc_lem];


(* refined -> ideal simulation helper lemmas *)

(* HARD: needs to be coupled with SGI handler execution *)
val ideal_C_RCU_sim_step_lem = store_thm("ideal_C_RCU_sim_step_lem", ``
!IM RM IM'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ ideal_model_trans(IM,C_RCU,IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* HARD: needs to be coupled with IGC interrupt reception handler *)
val ideal_C_IGC_sim_step_lem = store_thm("ideal_C_IGC_sim_step_lem", ``
!IM RM IM'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ ideal_model_trans(IM,C_IGC,IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

val ideal_ready_irqs_lem = store_thm("ideal_ready_irqs_lem", ``
!IM c q. 
    c < RPAR.nc
 /\ InvI IM
 /\ q IN ready_irqs(
	     (idgic_abs (IM.G (PCG c)).GIC).Q (PCC c),
             ipmsk ((idgic_abs (IM.G (PCG c)).GIC).gicc (PCC c)))
==>
xguest_irq (PCG c) q
``,
  RW_TAC std_ss [ready_irqs_def, pred_setTheory.IN_GSPEC_IFF] >>
  `(idgic_abs (IM.G (PCG c)).GIC).Q (PCC c) q <> INACTIVE` by (
      RW_TAC std_ss [IRQstate_distinct]
  ) >>
  IMP_RES_TAC good_proj_in_range_impls >>
  IMP_RES_TAC ( InvI_EXPAND ``PCG c`` ) >>
  IMP_RES_TAC id_inv_gic_q_def >>
  Cases_on `q`
  >| [(* SGI *)
      `?id s r. p=(id,s,r)` by ( 
          METIS_TAC [pairTheory.pair_CASES] 
      ) >>
      RW_TAC std_ss [] >>
      FULL_SIMP_TAC (srw_ss()) [xguest_irq_def]
      ,
      (* PIR *)
      FULL_SIMP_TAC (srw_ss()) [xguest_irq_def]
     ]      
);

val ready_irq_prio_sim_lem = store_thm("ready_irq_prio_sim_lem", ``
!RM IM c.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ Mode (RM.C c) < 2
==>
({w2n (prio q) | q IN ready_irqs
     ((idgic_abs (IM.G (PCG c)).GIC).Q (PCC c),
      ipmsk ((gic_abs RM.GIC).gicv c))} = 
 {w2n (prio q) | q IN ready_irqs
     ((VI RM.GIC c,ipmsk ((gic_abs RM.GIC).gicv c)))})
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, GSPEC_f_lem] >>
  FULL_SIMP_TAC std_ss [ready_irqs_def, 
			pred_setTheory.IN_GSPEC_IFF] >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      Cases_on `q`
      >| [(* SGI *)
	  `?id s r. p=(id,s,r)` by ( 
	      METIS_TAC [pairTheory.pair_CASES] 
	  ) >>
	  RW_TAC std_ss [] >>
	  `PCG c < PAR.ng /\ PCC c < PAR.nc_g (PCG c)` by ( 
	      METIS_TAC [good_proj_in_range_impls] 
	  ) >>
	  IMP_RES_TAC InvI_SGI_pending_lem >>
	  EXISTS_TAC ``SGI (id,s,c)`` >>
	  `SGI (id,s,r) = PRQ (PCG c) (SGI (id,s,c))` by (
	      RW_TAC std_ss [PRQ_def]
	  ) >>
	  RW_TAC std_ss [wordsTheory.w2n_11, prio_SGI_axiom]
	  >| [(* VI *)
	      FULL_SIMP_TAC std_ss [] >>
	      METIS_TAC [virq_guest_mode_lem]
	      ,
	      (* ipmsk *)
	      METIS_TAC [ipmsk_SGI_axiom]
	     ]
	  ,
	  (* PIR *)
	  EXISTS_TAC ``PIR n`` >>
	  `PIR n = PRQ (PCG c) (PIR n)` by (
	      RW_TAC std_ss [PRQ_def]
	  ) >>
	  RW_TAC std_ss [] >>
	  FULL_SIMP_TAC std_ss [] >>
	  METIS_TAC [virq_guest_mode_lem]
	 ]
      ,
      (* <== *)
      STRIP_TAC >>
      EXISTS_TAC ``PRQ (PCG c) q`` >>
      `PCG c < PAR.ng /\ PCC c < PAR.nc_g (PCG c)` by ( 
	  METIS_TAC [good_proj_in_range_impls] 
      ) >>
      RW_TAC std_ss []
      >| [(* prio *)
	  Cases_on `q` 
	  >| [(* SGI *)
	      `?id s r. p=(id,s,r)` by ( 
		  METIS_TAC [pairTheory.pair_CASES] 
	      ) >>
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC InvR_SGI_pending_lem >>
	      RW_TAC std_ss [wordsTheory.w2n_11, PRQ_def,
			     prio_SGI_axiom]
	      ,
	      (* PIR *)
	      RW_TAC std_ss [wordsTheory.w2n_11, PRQ_def]
	     ]
	  ,
	  (* Q *)
	  METIS_TAC [virq_guest_mode_lem]
	  ,
	  (* ipmsk *)
	  Cases_on `q` 
	  >| [(* SGI *)
	      `?id s r. p=(id,s,r)` by ( 
		  METIS_TAC [pairTheory.pair_CASES] 
	      ) >>
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC InvR_SGI_pending_lem >>
	      RW_TAC std_ss [PRQ_def] >>
	      METIS_TAC [ipmsk_SGI_axiom]
	      ,
	      (* PIR *)
	      RW_TAC std_ss [PRQ_def]
	     ]
	 ]
     ]
);

val ideal_gic_snd_virq_sim_lem = store_thm("ideal_gic_snd_virq_sim_lem", ``
!RM IM c iGIC'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ Mode (RM.C c) < 2
/\ idgic_step_snd_irq ((IM.G (PCG c)).GIC,PCC c,iGIC')
==>
?rGIC'. gic_step_snd_irq (RM.GIC,c,T,rGIC')
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ( idgic_step_axiom // "snd_irq" ) >> 
  MATCH_MP_TAC ( gic_snd_virt_irq_enabled_axiom ) >>
  `xguest_irq (PCG c) q` by ( METIS_TAC [ideal_ready_irqs_lem] ) >>
  IMP_RES_TAC good_proj_in_range_impls >>
  `?rq. (q = PRQ (PCG c) rq) /\ refined_vIRQ (PCG c) rq` by ( 
      METIS_TAC [PRQ_inv_lem] 
  ) >>
  FULL_SIMP_TAC std_ss [vmsk_ipmsk_axiom] >>
  `(idgic_abs (IM.G (PCG c)).GIC).gicc (PCC c) = (gic_abs RM.GIC).gicv c` by (
      METIS_TAC [bisim_gicc_reg_def, SIM_EXPAND]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  EXISTS_TAC ``rq:irqID`` >>
  STRIP_TAC >- (
      (* ready_irqs *)
      RW_TAC std_ss [] >>
      FULL_SIMP_TAC std_ss [ready_irqs_def, pred_setTheory.IN_GSPEC_IFF] >>
      IMP_RES_TAC virq_guest_mode_lem >>
      FULL_SIMP_TAC std_ss [] >>
      Cases_on `rq`
      >| [(* SGI *)
	  `?id s r. p=(id,s,r)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
	  RW_TAC std_ss [] >>
	  `r < RPAR.nc /\ (PCG r = PCG c)` by ( 
	      METIS_TAC [refined_vIRQ_def] 
	  ) >>
	  METIS_TAC [PRQ_def, ipmsk_SGI_axiom]
	  ,
	  (* PIR *)
	  FULL_SIMP_TAC std_ss [PRQ_def]
	 ]
  ) >>
  STRIP_TAC >- (
      (* max_prio *)
      IMP_RES_TAC ready_irq_prio_sim_lem >>
      `max_prio(ready_irqs (VI RM.GIC c,ipmsk ((gic_abs RM.GIC).gicv c))) = 
       max_prio(ready_irqs
		    ((idgic_abs (IM.G (PCG c)).GIC).Q (PCC c),
		     ipmsk ((gic_abs RM.GIC).gicv c)))` by (
          RW_TAC std_ss [max_prio_def]
      ) >>
      RW_TAC std_ss [] >>
      `w2n (prio rq) = w2n (prio (PRQ (PCG c) rq))` suffices_by (
          ASM_REWRITE_TAC []
      ) >>
      Cases_on `rq`
      >| [(* SGI *)
	  `?id s r. p=(id,s,r)` by ( 
	      METIS_TAC [pairTheory.pair_CASES] 
	  ) >>
	  THROW_AWAY_TAC ``w2n (prio x) = z`` >>
	  FULL_SIMP_TAC std_ss [] >>
	  `r < RPAR.nc /\ (PCG r = PCG c)` by ( 
	      METIS_TAC [refined_vIRQ_def] 
	  ) >>
	  RW_TAC std_ss [wordsTheory.w2n_11] >>
	  ASM_REWRITE_TAC [PRQ_def] >>
	  RW_TAC std_ss [prio_SGI_axiom]
	  ,
	  (* PIR *)
	  RW_TAC std_ss [wordsTheory.w2n_11, PRQ_def]
	 ]
  ) >>
  STRIP_TAC >- (
      (* PIR id *)
      NTAC 2 STRIP_TAC >>
      FULL_SIMP_TAC std_ss [xguest_irq_def, PRQ_def]
  ) >> (
      (* SGI id *)
      NTAC 4 STRIP_TAC >>
      FULL_SIMP_TAC std_ss [refined_vIRQ_def, PRQ_def] >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC PCG_PCC_inj
  )
);

val ideal_core_rcv_virt_sim_lem = store_thm("ideal_core_rcv_virt_sim_lem", ``
!RM IM c IC'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ idcore_step_rcv_phys ((IM.G (PCG c)).C (PCC c),IC')
==>
?RC'. refcore_step_rcv_virt(RM.C c,RC')
``,
  REPEAT STRIP_TAC >>
  `haspoc_exc_conf (RM.C c)` by ( 
      METIS_TAC [InvR_haspoc_exc_conf_lem, Mode_mode_lem]
  ) >>
  IMP_RES_TAC ( idcore_step_axiom // "rcv_phys" ) >>
  `(?C'. refcore_step_rcv_phys (RM.C c,C')) /\
    ?C'. refcore_step_rcv_virt (RM.C c,C')` suffices_by (
      METIS_TAC []
  ) >>
  MATCH_MP_TAC ( refcore_irq_enabled_axiom ) >>
  IMP_RES_TAC bisim_refined_core_active_lem >>
  IMP_RES_TAC bisim_guest_core_lem >>
  FULL_SIMP_TAC arith_ss []
);

val bisim_ctx_core_virt_irq_lem = store_thm("bisim_ctx_core_virt_irq", ``
!RM IM c RC' IC'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ refcore_step_rcv_virt (RM.C c,RC')
/\ idcore_step_rcv_phys ((IM.G (PCG c)).C (PCC c),IC')
==>
bisim_ctx_core (idcore_abs IC', 
		refcore_abs RC', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC RC',c),
	        ectx RC',
                refcore_int RC',
                idcore_int IC') /\
(Mode RC' < 2) /\
(iMode IC' < 2) /\
(refcore_abs (RM.C c)).active /\ (refcore_abs RC').active /\
(idcore_abs ((IM.G (PCG c)).C (PCC c))).active /\ (idcore_abs IC').active /\
(refcore_req_sent (RM.C c) = EMPTY) /\ 
(refcore_req_sent RC' = EMPTY) /\ 
(ref_abs_int (RM.C c) = FLUSHED) /\
(ref_abs_int RC' = FLUSHED) /\ 
(idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = EMPTY) /\ 
(idcore_req_sent IC' = EMPTY) /\ 
(id_abs_int ((IM.G (PCG c)).C (PCC c)) = FLUSHED) /\
(id_abs_int IC' = FLUSHED) /\ 
(id_abs_int IC' = FLUSHED) /\ 
((refcore_abs RC').H = (refcore_abs (RM.C c)).H)
``,
  NTAC 6 STRIP_TAC >>
  IMP_RES_TAC soft_Mode_lem >>
  `mode (refcore_abs (RM.C c)) < 2` by ( 
      FULL_SIMP_TAC std_ss [Mode_mode_lem] 
  ) >>
  IMP_RES_TAC InvR_haspoc_exc_conf_lem >>
  IMP_RES_TAC refcore_virt_irq_axiom >>
  IMP_RES_TAC ( idcore_step_axiom // "rcv_phys" ) >>
  IMP_RES_TAC bisim_guest_core_lem >>
  FULL_SIMP_TAC std_ss [Mode_mode_lem] >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  REV_FULL_SIMP_TAC std_ss [bisim_ctx_core_def, Mode_mode_lem] >>
  `(mode (refcore_abs (RM.C c)) <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) <> 2)` by ( DECIDE_TAC ) >>
  `mode (refcore_abs RC') = 1` by ( 
      FULL_SIMP_TAC std_ss [mode_def, MODE_upd_lem]
  ) >>
  `(mode (refcore_abs RC') <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs RC') < 2)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs RC') <> 2)` by ( DECIDE_TAC ) >>
  IMP_RES_TAC soft_mode_lem >>
  RW_TAC std_ss []
  >| [(* guest SPRs unchanged *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INL r:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      PAT_X_ASSUM ``!r:SPRguest. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``r:SPRguest`` thm 
		    )
      ) >>
      PAT_X_ASSUM ``!r:SPRguest. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``r:SPRguest`` thm 
		    )
      ) >>
      Cases_on `(r = ELR_EL1) \/ (r = ISR_EL1) \/ (r = SPSR_EL1)` >> (
	  REV_FULL_SIMP_TAC std_ss [] >> (
	      FULL_SIMP_TAC std_ss [exception_regs_axiom]
	  )
      )
      ,
      (* refcore_int unchanged *)
      FULL_SIMP_TAC std_ss [ref_abs_int_def, id_abs_int_def] >>
      METIS_TAC [cis_abs_flushed_axiom]
      ,
      (* iMode' *)
      FULL_SIMP_TAC std_ss [iMode_def, MODE_upd_lem]
     ]      
);

(* MEDIUM: only core affected, **GUEST/SWITCH**
need to argue that interrupt step is possible on refined model *)
val ideal_CORE_RCV_IRQ_sim_step_lem = store_thm("ideal_CORE_RCV_IRQ_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_RCV_IRQ n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [ideal_guest_trans_def,
                            id_rule_core_rcv_irq_def, 
			    idcore_step_def, idgic_step_def] >>
  RW_TAC std_ss [] >>
  (* sync redundant *)
  `syncInv <|G := (g =+ IM.G g with
               <|C := (n =+ C') (IM.G g).C; GIC := gic'|>) IM.G |>` by (
      MATCH_MP_TAC syncInv_lem >>
      FULL_SIMP_TAC std_ss [InvI_def] >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  (* construct refined comp *)
  `?c. (n = PCC c) /\ (g = PCG c) /\ c < RPAR.nc` by ( 
      METIS_TAC [PCGC_PPGP_inv_def]
  ) >>
  RW_TAC std_ss [] >>
  `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active` by (
      METIS_TAC [idcore_step_axiom // "rcv_phys"]
  ) >>
  `Mode (RM.C c) < 2` by ( METIS_TAC [SimInvR_no_req_mode_lem] ) >>
  `?rGIC'. gic_step_snd_irq (RM.GIC,c,T,rGIC')` by (
      METIS_TAC [ideal_gic_snd_virq_sim_lem]
  ) >>
  `?RC'. refcore_step_rcv_virt(RM.C c,RC')` by (
      METIS_TAC [ideal_core_rcv_virt_sim_lem]
  ) >>
  EXISTS_TAC ``SUC 0`` >>
  REWRITE_TAC [refined_comp_def] >>
  EXISTS_TAC ``RM with <|C := (c =+ RC') RM.C; GIC := rGIC'|>`` >>
  STRIP_TAC >- (
      EXISTS_TAC ``CORE_RCV_IRQ c`` >>
      EXISTS_TAC ``RM:refined_model`` >>
      RW_TAC std_ss [refined_trans_def, ref_rule_core_rcv_irq_def, 
		     refcore_step_def, gic_step_def] >>
      METIS_TAC []
  ) >>
  (* prepare SIM proof *)
  IMP_RES_TAC bisim_ctx_core_virt_irq_lem >>
  `(gic_req_rcvd rGIC' = gic_req_rcvd RM.GIC) /\
   (gic_abs rGIC' = gic_abs RM.GIC) /\ 
   (Q rGIC' = Q RM.GIC) /\ (VI rGIC' = VI RM.GIC)` by (
      METIS_TAC [gic_snd_irq_axiom]
  ) >>
  `(idgic_abs gic' = idgic_abs ((IM.G (PCG c)).GIC)) /\ 
   (idgic_req_rcvd gic' = idgic_req_rcvd ((IM.G (PCG c)).GIC)) /\
   (PI gic' = PI ((IM.G (PCG c)).GIC))` by (
      METIS_TAC [idgic_step_axiom // "snd_irq"]
  ) >>
  `~hv_guard_mmu_fault 
       (HVabs(RM with <|C := (c =+ RC') RM.C; GIC := rGIC'|>,c),c)` by (
      MATCH_MP_TAC hv_guard_mmu_fault_lem >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  `~hv_gicd_entry_state
       (HVabs(RM with <|C := (c =+ RC') RM.C; GIC := rGIC'|>,c))` by (
      MATCH_MP_TAC hv_gicd_entry_state_lem >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  IMP_RES_TAC hv_guard_mmu_fault_lem >>
  IMP_RES_TAC hv_gicd_entry_state_lem >>
  STRIP_TAC
  >| [(* prove SIM *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      (* most cases *)
        EXCEPT_FOR ``bisim_send_igc _``
          (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
             FULL_SIMP_TAC (srw_ss()) 
	         (nuigc_def::(bisim_pi_guest_def::bisim_core_definitions)) >>
             TRY (Cases_on `n=c`) >>
             REPEAT IF_CASES_TAC >>    
             FULL_SIMP_TAC (srw_ss()++ARITH_ss) 
	         [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                  HVabs_def, nuvi_def] >>
             REV_FULL_SIMP_TAC arith_ss [] >>
             TRY (INFS_LIMITED_METIS_TAC 1 
	              [PCG_PCC_inj, good_proj_in_range_impls, Mode_arith_lem,
		       Mode_def, mode_def, Trrpl_eq_rpl_lem, AHV_corollaries]
		 )
          ) 
      ) >>
      (* send_igc *)
      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
      EXISTS_TAC ``RM:refined_model`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC arith_ss [AHV_corollaries]
      )
      ,
      (* SimInvR *)
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      REPEAT STRIP_TAC
      >| [(* Glock *)
	  Cases_on `c=0` >> (
	      FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      REV_FULL_SIMP_TAC std_ss []
	  )
	  ,
	  (* Mode *)
	  Cases_on `c=c'` >> (
	      FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	  )
	 ]
     ]
);

(* MEDIUM: only core affected, **GUEST/SWITCH**
need special cases for fault and GICD replies, 
need to argue that same reply is present in both models *)
val ideal_CORE_RCV_MRPL_sim_step_lem = store_thm("ideal_CORE_RCV_MRPL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_RCV_MRPL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_core_rcv_rpl_def] >>
  FULL_SIMP_TAC (srw_ss()) [idcore_step_def] >>
  `syncInv <|G := (g =+ IM.G g with
               <|C := (n =+ C') (IM.G g).C;
                 cif := (n =+ cif') (IM.G g).cif|>) IM.G |>` by (
      MATCH_MP_TAC syncInv_lem >>
      FULL_SIMP_TAC std_ss [InvI_def] >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  `?c. c = PCGC_inv (g, n)` by ( RW_TAC (srw_ss()) [] ) >>
  `c < RPAR.nc /\ (PCG c = g) /\ (PCC c = n)` by (
      IMP_RES_TAC PCGC_PPGP_inv_def >>
      FULL_SIMP_TAC (srw_ss()) [] 
  ) >> 
  IMP_RES_TAC SimInvR_no_TRANS_lem >>
  FULL_SIMP_TAC (srw_ss()) [bif_step_def]
  >| [(* forwarded reply *)
      `?q. q IN ((IM.G g).cif n).req_rcvd /\ match (q,r) 
        /\ r IN ((IM.G g).cif n).rpl_rcvd` by (
          METIS_TAC [bif_step_snd_rpl_def]
      ) >>
      `q' = q` by ( METIS_TAC [unique_match_thm] ) >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC bif_step_snd_reply_lem >>
      `(idcore_abs((IM.G g).C n)).active` by (
          METIS_TAC [idcore_step_axiom // "rcv_rpl"]
      ) >>
      Cases_on `PAdr q = Agicd`
      >| [(* gicd handler emulation step *)
	  cheat
	  ,
	  (* regular memory reply -> first build core step *)
	  `Mode (RM.C c) < 2` by ( METIS_TAC [SimInvR_req_mode_lem] ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  `idcore_req_sent ((IM.G g).C n) = refcore_req_sent (RM.C c)` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND, bisim_corereq_guest_def,
				    bisim_corereq_guest_core_def] >>
	      METIS_TAC []
	  ) >>
	  `q IN refcore_req_sent (RM.C c)` by ( FULL_SIMP_TAC std_ss [] ) >>
	  `(refcore_abs (RM.C c)).H.launched` by (
	      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	      METIS_TAC [ref_inv_hist_def, Mode_mode_lem]
	  ) >>
	  `(refcore_abs (RM.C c)).active` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND, bisim_ctx_def] >>
	      METIS_TAC [bisim_ctx_core_def]
	  ) >>
	  `?RC'. refcore_step_rcv_rpl (RM.C c,r,RC')` by (
	      MATCH_MP_TAC refcore_rcv_rpl_enabled_axiom >>
	      `Mode (RM.C c) <= 1` by ( DECIDE_TAC ) >>
	      METIS_TAC []
	  ) >>
	  (* mmu step *)
	  IMP_RES_TAC mmu_active_lem >>
	  `q IN mmu_req_rcvd (RM.MMU c)` by ( 
	      METIS_TAC [bisim_cif_req_rcvd_lem] 
	  ) >>
	  `Trrpl (PCG c) r IN mmu_rpl_rcvd (RM.MMU c) 
	   /\ IS_SOME(Trans (PCG c) (Rpl_PAdr r))` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND, bisim_mmureq_guest_def] >>
	      METIS_TAC [bisim_mmureq_guest_core_def]
	  ) >>
	  `?R TR. ((mmu_abs(RM.MMU c)).state R = FINAL (SOME TR)) 
	       /\ match(TR,Trrpl (PCG c) r)` by (
	      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	      METIS_TAC [ref_inv_mmurpl_def]
	  ) >> 
	  `R IN mmu_req_rcvd (RM.MMU c)` by (
	      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	      METIS_TAC [inv_good_mmu_def, MMUstate_distinct]
	  ) >>
	  `match(Trreq (PCG c) q,Trrpl (PCG c) r)` by (
	      `q = ReqOf r` by METIS_TAC [match_ReqOf_lem] >>
	      IMP_RES_TAC good_match_lem >>
	      `IS_SOME (Trans (PCG c) (PAdr q))` by (
	          METIS_TAC [Rpl_PAdr_ReqOf_lem]
	      ) >>
	      METIS_TAC [Trans_match_lem]
	  ) >>
	  `TR = Trreq (PCG c) q` by ( METIS_TAC [unique_match_thm] ) >>
	  FULL_SIMP_TAC std_ss [] >>
	  `(Trreq (PCG c) q = Trreq (PCG c) R) /\ 
	   IS_SOME (Trans (PCG c) (PAdr R))` by (
	      METIS_TAC [xlated_mmu_rpl_lem]
	  ) >>
	  `R = q` by ( METIS_TAC [Trreq_eq_req_lem] ) >>
	  RW_TAC std_ss [] >>
	  `?q MMU'. mmu_step_snd_rpl (RM.MMU c,q,MMU') /\ match (R,q) /\
		    Rpl_val_eq q (Trrpl (PCG c) r)` by ( 
	      MATCH_MP_TAC mmu_final_rpl_axiom >>
	      HINT_EXISTS_TAC >>
	      METIS_TAC []
	  ) >>
	  `q = r` by (
  	      IMP_RES_TAC good_match_lem >>
	      `Rpl_val_eq (Trrpl (PCG c) r) r` by ( 
	          METIS_TAC [Trrpl_Rpl_val_eq_lem]
	      ) >>
	      IMP_RES_TAC Rpl_val_eq_trans_lem >>
	      IMP_RES_TAC match_Rpl_eq_lem
	  ) >>
	  RW_TAC std_ss [] >>
	  (* refined model step *)
	  `refined_comp (RM,SUC 0,RM with 
               <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>)` by (
	      RW_TAC std_ss [refined_comp_def] >>
	      EXISTS_TAC ``CORE_RCV_MRPL c`` >>
	      RW_TAC std_ss [refined_trans_def,ref_rule_core_rcv_mrpl_def, 
			     refcore_step_def] >>
	      EXISTS_TAC ``q:reply`` >>
	      EXISTS_TAC ``RC':refcore`` >>
	      EXISTS_TAC ``MMU':mmu`` >>
	      EXISTS_TAC ``R:request`` >>
	      RW_TAC std_ss [mmu_step_def]
	  ) >>
	  Cases_on `Frpl q`
	  >| [(* Fault reply -> execute kernel handler *)
	      cheat
	      ,
	      (* no fault -> same step executed, apply step and bisim axioms *)
	      EXISTS_TAC ``SUC 0`` >>
	      HINT_EXISTS_TAC >>
	      FULL_SIMP_TAC std_ss [] >>
	      `(refcore_abs RC').active /\
	       (refcore_req_sent RC' = refcore_req_sent (RM.C c) DIFF {R}) /\
	       ((refcore_abs RC').H = (refcore_abs (RM.C c)).H) /\
	       (Mode RC' < 2)` by (
	          IMP_RES_TAC refcore_rcv_rpl_axiom >>
		  IMP_RES_TAC unique_match_thm >> 
		  FULL_SIMP_TAC std_ss [] 
	      ) >>
	      IMP_RES_TAC soft_Mode_lem >>
	      `R IN idcore_req_sent ((IM.G (PCG c)).C (PCC c)) /\ 
	       (idcore_req_sent C' = 
		idcore_req_sent ((IM.G (PCG c)).C (PCC c)) DIFF {R}) /\
	       (idcore_abs C').active /\
	       ((idcore_abs C').H = (idcore_abs ((IM.G (PCG c)).C (PCC c))).H) /\
	       iMode ((IM.G (PCG c)).C (PCC c)) < 2 /\ iMode C' < 2` by (
	          IMP_RES_TAC ( idcore_step_axiom // "rcv_rpl" ) >>
		  IMP_RES_TAC unique_match_thm >> 
		  FULL_SIMP_TAC std_ss [] 
	      ) >>
	      `((idcore_abs C').PC = (refcore_abs RC').PC) /\
	       ((idcore_abs C').PSTATE = (refcore_abs RC').PSTATE) /\
	       ((idcore_abs C').GPR = (refcore_abs RC').GPR) /\
	       (!r. (idcore_abs C').SPR r = (refcore_abs RC').SPR (INL r)) /\
	       (idcore_int C' = refcore_int RC')` by (
	          MATCH_MP_TAC core_rcv_rpl_bisim_axiom	>>
		  EXISTS_TAC ``RM.C c`` >>
		  HINT_EXISTS_TAC >>
		  EXISTS_TAC ``q:reply`` >>
		  FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC match_ReqOf_lem >>
		  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
		  IMP_RES_TAC bisim_ctx_def >>
		  FULL_SIMP_TAC std_ss [bisim_ctx_core_def, Mode_mode_lem] >>
		  REV_FULL_SIMP_TAC arith_ss []
	      ) >>
	      `(mmu_rpl_rcvd MMU' = 
		mmu_rpl_rcvd (RM.MMU c) DIFF {Trrpl (PCG c) q}) /\
               xlated_rpl (q,Trrpl (PCG c) q) /\ ~st2_fault q /\
	       (mmu_req_rcvd MMU' = mmu_req_rcvd (RM.MMU c) DIFF {R}) /\
	       ((mmu_abs MMU').state R = IDLE) /\
	       (!r'. r' <> R ==>
	           ((mmu_abs MMU').state r' = (mmu_abs (RM.MMU c)).state r')) /\
	       (mmu_req_sent MMU' = mmu_req_sent (RM.MMU c)) /\
	       (mmu_ptl_hist MMU' = mmu_ptl_hist (RM.MMU c)) /\
	       ((mmu_abs MMU').active <=> (mmu_abs (RM.MMU c)).active) /\
	       ((mmu_abs MMU').cfg = (mmu_abs (RM.MMU c)).cfg)` by (
	          IMP_RES_TAC match_ReqOf_lem >>
		  IMP_RES_TAC mmu_reply_lem >>
		  `ReqOf q' = Trreq (PCG c) R` by (
		      REV_FULL_SIMP_TAC std_ss [MMUstate_11]
		  ) >>
		  `q' = Trrpl (PCG c) q` by (
		      MATCH_MP_TAC match_Trrpl_lem >>
		      EXISTS_TAC ``R:request`` >>
		      FULL_SIMP_TAC std_ss []
		  ) >>
		  RW_TAC std_ss []
	      ) >>
	      (* prove SimInvR *)
	      `SimInvR (RM with 
                   <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>)` by (
	          RW_TAC std_ss [SimInvR_def,combinTheory.APPLY_UPDATE_THM] >> (
	              FULL_SIMP_TAC std_ss [SimInvR_def] )
		  >| [(* primary core *)
		      Cases_on `0 = c'` >> (
		      	  FULL_SIMP_TAC std_ss [SimInvR_def]
		      )
		      ,
		      (* primary core's MMU *)
		      Cases_on `0 = c'` >> (
		      	  FULL_SIMP_TAC std_ss [SimInvR_def]
		      ) >>
		      Cases_on `r = R` >> (
		          FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
		      )
		      ,
		      (* primary core's MMU GICD request *)
		      Cases_on `0 = c'` >> (
			  FULL_SIMP_TAC std_ss [SimInvR_def]
		      ) >>
		      Cases_on `r = R` >> (
		          FULL_SIMP_TAC std_ss []
		      )
		      ,
		      (* other core *)
		      Cases_on `c = c'` >> (
		      	  FULL_SIMP_TAC std_ss [SimInvR_def]
		      )
		      ,
		      (* other core's MMU *)
		      Cases_on `c = c'` >> (
		      	  FULL_SIMP_TAC std_ss [SimInvR_def]
		      ) >>
		      Cases_on `r = R` >> (
		          FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
		      )
		      ,
		      (* primary core's MMU GICD request *)
		      Cases_on `c = c'` >> (
			  FULL_SIMP_TAC std_ss [SimInvR_def]
		      ) >>
		      Cases_on `r = R` >> (
		          FULL_SIMP_TAC std_ss []
		      )
		     ]
	      ) >>
	      FULL_SIMP_TAC std_ss [] >>
	      (* prove SIM *)
	      IMP_RES_TAC good_match_lem >>
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
	      REPEAT STRIP_TAC >> (
	        EXCEPT_FOR ``bisim_send_igc _`` (
		  FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		      bisim_definitions RW_FS_IMPRESS >>
		  FULL_SIMP_TAC (srw_ss()) (nuigc_def::bisim_core_definitions) >>
		  TRY (Cases_on `n=c`) >>
		  REPEAT IF_CASES_TAC >>    
		  FULL_SIMP_TAC (srw_ss()++ARITH_ss) [
		      combinTheory.APPLY_UPDATE_THM, 
		      mode_def, iMode_def, Mode_def, HVabs_def, 
		      hv_guard_mmu_fault_def, hv_gicd_entry_state_def, 
		      nuvi_def, hv_guard_gicd_fail_def] >>
		  REV_FULL_SIMP_TAC arith_ss [] >>
		  TRY ( INFS_LIMITED_METIS_TAC 1 [
			PCG_PCC_inj, good_proj_in_range_impls, 
			Trrpl_eq_rpl_lem, 
			mmu_fault_not_GICD_req_lem, 
			AHV_corollaries, 
			Mode_def, Mode_arith_lem] ) 
		)
	      ) >>
    	      (* send_igc *)
    	      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
    	      EXISTS_TAC ``RM:refined_model`` >>
    	      EXISTS_TAC ``IM:ideal_model`` >>
    	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
    	      	FULL_SIMP_TAC arith_ss []
    	      )
	     ]
	 ]
      ,
      (* fault -> hypervisor mmu/gicd handler injection *)
      cheat
     ]
);

(* EASY: same step in both models **GUEST/SWITCH** *)
val ideal_CORE_RCV_EVENT_sim_step_lem = store_thm("ideal_CORE_RCV_EVENT_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_RCV_EVENT n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_core_rcv_event_def]
  >| [(* StartCore - involves boot code *)
      `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >>
       Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                              <|C := (n =+ C') (IM.G g).C; PSCI := PS'|>)
				       IM.G|>` >>
      `syncInv IM''` by ( 
          MATCH_MP_TAC syncInv_lem >>
          HINT_EXISTS_TAC >>
	  Q.UNABBREV_TAC `IM''` >>
          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
      `?c. c < RPAR.nc /\ (g = PCG c) /\ (n = PCC c)` by (
          METIS_TAC [PCGC_PPGP_inv_def, PCGC_inv_rewrites]
      ) >>
      RW_TAC std_ss [] >>
      Cases_on `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active`
      >| [(* active -> redundant *)
	  FULL_SIMP_TAC (srw_ss()) [idpsci_step_def, idcore_step_def] >>
	  `(refcore_abs (RM.C c)).active /\ 
	   (refcore_abs (RM.C c)).H.launched` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_ctx_def >>
	      METIS_TAC [bisim_ctx_core_def]
	  ) >>
	  `Mode (RM.C c) < 2` by (
	      IMP_RES_TAC SimInvR_def
	      >| [(* Mode = 2 *)
	          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	          IMP_RES_TAC bisim_corereq_gicd_def >>
	          IMP_RES_TAC bisim_corereq_gicd_core_def >>
	          FULL_SIMP_TAC (srw_ss()) [] >> (
	              RES_TAC >>
		      FULL_SIMP_TAC (srw_ss()) []
		  )
		  ,
		  (* Creset *)
		  METIS_TAC [Creset_axiom]
		  ,
		  (* soft *)
		  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	          IMP_RES_TAC ref_inv_hist_def
		 ]
	  ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  `(refcore_req_sent (RM.C c) = EMPTY)` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_corereq_guest_def >>
	      METIS_TAC [bisim_corereq_guest_core_def]
	  ) >>
	  EXISTS_TAC ``SUC 0`` >>
	  RW_TAC std_ss [refined_comp_def, PULL_EXISTS] >>
	  FIRST_EXISTS_TAC ``CORE_RCV_EVENT c`` >>
	  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_core_rcv_event_def, 
			     PULL_EXISTS, psci_step_def, refcore_step_def] >>
	  EXISTS_TAC ``StartCore c`` >>
	  `?RC'. refcore_step_rcv_psci (RM.C c, StartCore c,RC')` by (
	      `Mode (RM.C c) <= 1` by ( RW_TAC arith_ss [] ) >>
	      METIS_TAC [refcore_psci_enabled_axiom]
	  ) >>
	  `?ps'. psci_step_snd_event (RM.PSCI, StartCore c,c,ps')` by (
	      RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	      EXISTS_TAC ``RM.PSCI with
                  <|events := (c =+ TL (RM.PSCI.events c))
	  			  RM.PSCI.events;
	  	    pow := (c =+ T) RM.PSCI.pow|>`` >>
	      IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	      IMP_RES_TAC psci_step_snd_event_def >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      `HD (MAP PEE (RM.PSCI.events c)) = StartCore (PCC c)` by (
	          METIS_TAC []
	      ) >>
	      MATCH_MP_TAC (
	          prove(``(B ==> A) /\ B ==> A /\ B``, PROVE_TAC [])
	      ) >>
	      STRIP_TAC 
	      >| [(* HD *)
		  STRIP_TAC >>
		  FULL_SIMP_TAC std_ss [HD_MAP_lem] >>
		  FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
		  Cases_on `HD (RM.PSCI.events c)` >> (
		      FULL_SIMP_TAC (srw_ss()) []
		  ) >>
		  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
		  `MEM (StartCore n) (RM.PSCI.events c)` by (
		      METIS_TAC [MEM_HD_lem]
		  ) >>
		  IMP_RES_TAC ref_inv_psci_def >>
		  FULL_SIMP_TAC std_ss [psciev_def]
		  ,
		  (* not [] *)
		  REV_FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC MAP_not_nil_lem 
		 ]
	  ) >>
	  EXISTS_TAC ``ps':psci_state`` >>
	  EXISTS_TAC ``RC':refcore`` >>
	  ASM_REWRITE_TAC [] >>
	  (* add context *)
	  IMP_RES_TAC psci_step_snd_event_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  IMP_RES_TAC refcore_psci_start_axiom >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  `Mode RC' < 2` by ( FULL_SIMP_TAC std_ss [Mode_def] ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  `~hv_guard_mmu_fault (HVabs(RM with <|C := (c =+ RM.C c) RM.C; 
	  					PSCI := ps'|>,c),c)` by (
	      MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  `~hv_gicd_entry_state (HVabs(RM with <|C := (c =+ RM.C c) RM.C; 
	  					 PSCI := ps'|>,c))` by (
	      MATCH_MP_TAC hv_gicd_entry_state_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  IMP_RES_TAC hv_guard_mmu_fault_lem >>
	  IMP_RES_TAC hv_gicd_entry_state_lem >>
	  IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  (* SimInvR *)
	  `SimInvR (RM with <|C := (c =+ RM.C c) RM.C; PSCI := ps'|>)` by (
	      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  ASM_REWRITE_TAC [] >>
	  (* prove SIM *)
	  Q.UNABBREV_TAC `IM'` >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  REPEAT STRIP_TAC >> (
	    EXCEPT_FOR_THESE [``bisim_psci _ ``] (
	    FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	    (* try to solve straight-forward cases *)
	    REPEAT IF_CASES_TAC >>
            STRONG_FS_TAC ([]@bisim_core_definitions) >>
	    `!c'. c' <> c ==> (RM.C c' = (RM with <|C := (c =+ RM.C c) RM.C; 
	  				            PSCI := ps'|>).C c')` by (
               FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	    ) >>
      	    TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      	  		    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
	  		    hv_mmu_fault_entry_eq_lem,
      	  		    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
	  		    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
	  		    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
	  		    nuigc_guest_mode_lem] ) ) 
	  ) >>
	  (* bisim_psci *)
	  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	  >| [IF_CASES_TAC >> (
	          METIS_TAC [PCG_PCC_inj]
	      )
	      ,
	      IF_CASES_TAC
	      >| [IF_CASES_TAC
	       	  >| [IF_CASES_TAC
	       	      >| [METIS_TAC [listTheory.NULL_EQ, 
	       			     listTheory.MAP_TL]
	       		  ,
	       		  METIS_TAC [PCG_PCC_inj]
	       		 ]
	       	      ,
	       	      METIS_TAC [PCG_PCC_inj]
	       	     ]
	       	  ,
	       	  METIS_TAC [PCG_PCC_inj]
	         ]
	     ]
	  ,
	  (* inactive -> either running in boot loader or off *)
	  Cases_on `(refcore_abs (RM.C c)).active`
	  >| [(* in reset or soft reboot -> not possible *)
	      FULL_SIMP_TAC (srw_ss()) [idpsci_step_def, idcore_step_def] >>
	      `(Mode (RM.C c) = 3) /\ (refcore_req_sent (RM.C c) = EMPTY)` by (
	          IMP_RES_TAC SimInvR_def
	          >| [(* Mode < 2 *)
		      METIS_TAC [bisim_guest_mode_lem]
		      ,
		      (* Mode = 2 *)
		      `(refcore_abs (RM.C c)).PC NOTIN 
                           {AHV PC_INIT_PRIM_ENTRY; AHV PC_INIT_SEC_ENTRY;
			    AHV PC_INIT_PRIM; AHV PC_INIT_GUEST; 
			    AHV PC_INIT_CORE}` by (
		          FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT,
						pred_setTheory.NOT_IN_EMPTY] >> (
			      RW_TAC std_ss [] >> (
			          MATCH_MP_TAC AHV_inj >>
				  CCONTR_TAC >>
				  FULL_SIMP_TAC std_ss [] >>
				  IMP_RES_TAC HV_CODE2num_11 >>
				  FULL_SIMP_TAC std_ss [HV_CODE2num_thm]
			      )
			  )
		      ) >>
		      `(refcore_abs (RM.C c)).H.launched` by (
		          FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
			  IMP_RES_TAC ref_inv_hist_def >>
			  FULL_SIMP_TAC std_ss [Mode_mode_lem]
		      ) >>
		      IMP_RES_TAC soft_Mode_lem >>
	              FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	              IMP_RES_TAC bisim_ctx_def >>
	              METIS_TAC [bisim_ctx_core_def]
	       	      ,
	       	      (* Creset *)
		      RW_TAC std_ss [Mode_def] >> (
	       	          METIS_TAC [Creset_axiom, refcore_req_sent_boot_lem]
		      )
	       	      ,
		      (* soft *)
		      RW_TAC std_ss [Mode_def] >> (
	       	          METIS_TAC [mode_def, warm_soft_axiom, 
				     refcore_req_sent_boot_lem]
		      )
	       	     ]
	      ) >>
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_ctx_def >>
	      METIS_TAC [Mode_mode_lem, bisim_ctx_core_def]
	      ,
	      (* inactive -> start up *)
	      FULL_SIMP_TAC (srw_ss()) [idpsci_step_def, idcore_step_def] >>
	      IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	      REV_FULL_SIMP_TAC (srw_ss()) [] >>
	      IMP_RES_TAC proj_bound_lem >>
	      `Mode (RM.C c) < 2` by (
	          `Mode (RM.C c) <> 3` by (
	              FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	              IMP_RES_TAC bisim_ctx_def >>
	              METIS_TAC [Mode_mode_lem, bisim_ctx_core_def] 
	          ) >>
	          IMP_RES_TAC SimInvR_def
	          >| [(* Mode = 2 *)
	              FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	              IMP_RES_TAC bisim_corereq_gicd_def >>
	              IMP_RES_TAC bisim_corereq_gicd_core_def >>
	              FULL_SIMP_TAC (srw_ss()) [] >> (
	                  RES_TAC >>
	       	          FULL_SIMP_TAC (srw_ss()) []
	       	      )
	       	      ,
	       	      (* Creset *)
	       	      METIS_TAC [Mode_def, Creset_axiom]
	       	      ,
	       	      (* soft *)
	       	      METIS_TAC [warm_soft_axiom, Mode_mode_lem]
	       	 ]
	      ) >>
	      IMP_RES_TAC soft_Mode_lem >>
	      IMP_RES_TAC InvR_core_launched_lem >>
	      `(refcore_req_sent (RM.C c) = EMPTY)` by (
	          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	          IMP_RES_TAC bisim_corereq_guest_def >>
	          METIS_TAC [bisim_corereq_guest_core_def]
	      ) >>
	      EXISTS_TAC ``SUC 0`` >>
	      RW_TAC std_ss [refined_comp_def, PULL_EXISTS] >>
	      FIRST_EXISTS_TAC ``CORE_RCV_EVENT c`` >>
	      RW_TAC (srw_ss()) [refined_trans_def, ref_rule_core_rcv_event_def, 
	       			 PULL_EXISTS, psci_step_def, refcore_step_def] >>
	      EXISTS_TAC ``StartCore c`` >>
	      `?RC'. refcore_step_rcv_psci (RM.C c, StartCore c,RC')` by (
	          `Mode (RM.C c) <= 1` by ( RW_TAC arith_ss [] ) >>
	          METIS_TAC [refcore_psci_enabled_axiom]
	      ) >>
	      FULL_SIMP_TAC (srw_ss()) [idpsci_step_def, idcore_step_def] >> 
	      `?ps'. psci_step_snd_event (RM.PSCI, StartCore c,c,ps')` by (
	          RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	          EXISTS_TAC ``RM.PSCI with
                      <|events := (c =+ TL (RM.PSCI.events c))
	       			  RM.PSCI.events;
	       	        pow := (c =+ T) RM.PSCI.pow|>`` >>
	          IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	          IMP_RES_TAC psci_step_snd_event_def >>
	          FULL_SIMP_TAC (srw_ss()) [] >>
	          `HD (MAP PEE (RM.PSCI.events c)) = StartCore (PCC c)` by (
	              METIS_TAC []
	          ) >>
	          MATCH_MP_TAC (
	              prove(``(B ==> A) /\ B ==> A /\ B``, PROVE_TAC [])
	          ) >>
	          STRIP_TAC 
	          >| [(* HD *)
	       	      STRIP_TAC >>
	       	      FULL_SIMP_TAC std_ss [HD_MAP_lem] >>
	       	      FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
	       	      Cases_on `HD (RM.PSCI.events c)` >> (
	       	          FULL_SIMP_TAC (srw_ss()) []
	       	      ) >>
	       	      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	       	      `MEM (StartCore n) (RM.PSCI.events c)` by (
	       	          METIS_TAC [MEM_HD_lem]
	       	      ) >>
	       	      IMP_RES_TAC ref_inv_psci_def >>
	       	      FULL_SIMP_TAC std_ss [psciev_def]
	       	      ,
	       	      (* not [] *)
	       	      REV_FULL_SIMP_TAC std_ss [] >>
	       	      IMP_RES_TAC MAP_not_nil_lem 
	       	     ]
	      ) >>
	      EXISTS_TAC ``ps':psci_state`` >>
	      EXISTS_TAC ``RC':refcore`` >>
	      ASM_REWRITE_TAC [] >>
	      (* add context *)
	      IMP_RES_TAC psci_step_snd_event_def >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      IMP_RES_TAC refcore_psci_start_axiom >>
	      REV_FULL_SIMP_TAC std_ss [] >>
	      `(idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = EMPTY) /\ 
	       (idcore_req_sent C' = EMPTY) /\ 
	       ~((idcore_abs C').active) /\ 
	       ((idcore_abs C').H.launch) /\
               ((idcore_abs C').PC = 
		(idcore_abs ((IM.G (PCG c)).C (PCC c))).PC) /\
               ((idcore_abs C').PSTATE = 
	        (idcore_abs ((IM.G (PCG c)).C (PCC c))).PSTATE) /\
               ((idcore_abs C').GPR = 
		(idcore_abs ((IM.G (PCG c)).C (PCC c))).GPR) /\
               ((idcore_abs C').SPR = 
		(idcore_abs ((IM.G (PCG c)).C (PCC c))).SPR) /\
	       (id_abs_int ((IM.G (PCG c)).C (PCC c)) = FLUSHED) /\
	       (id_abs_int C' = FLUSHED)` by (
	          IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	          FULL_SIMP_TAC (srw_ss()) [] >>
	          REV_FULL_SIMP_TAC (srw_ss()) []
	      ) >>
	      `Mode RC' = 3` by ( 
	          FULL_SIMP_TAC std_ss [Mode_def] >>
	          METIS_TAC [mode_def, warm_soft_axiom]
	      ) >>
	      `~(Mode RC' < 2)` by ( FULL_SIMP_TAC arith_ss [] ) >>
	      `Mode RC' <> 2` by ( FULL_SIMP_TAC arith_ss [] ) >>
	      IMP_RES_TAC soft_Mode_lem >>
	      `~hv_guard_mmu_fault (HVabs(RM with <|C := (c =+ RC') RM.C; 
	       					PSCI := ps'|>,c),c)` by (
	          FULL_SIMP_TAC (srw_ss()) [HVabs_def, 
					    combinTheory.APPLY_UPDATE_THM,
					    hv_gicd_entry_state_def,
					    hv_guard_mmu_fault_def, 
					    Mode_mode_lem]
	      ) >>
	      `~hv_gicd_entry_state (HVabs(RM with <|C := (c =+ RC') RM.C; 
	       					 PSCI := ps'|>,c))` by (
	          FULL_SIMP_TAC (srw_ss()) [HVabs_def, 
					    combinTheory.APPLY_UPDATE_THM,
					    hv_gicd_entry_state_def,
					    Mode_mode_lem]
	      ) >>
	      IMP_RES_TAC hv_guard_mmu_fault_lem >>
	      IMP_RES_TAC hv_gicd_entry_state_lem >>
	      (* SimInvR *)
	      `SimInvR (RM with <|C := (c =+ RC') RM.C; PSCI := ps'|>)` by (
	          FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
	          RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      (* prove SIM *)
	      Q.UNABBREV_TAC `IM'` >>
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      REPEAT STRIP_TAC >> (
	        EXCEPT_FOR_THESE [``bisim_send_igc _``, ``bisim_psci _ ``] (
	        FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		    bisim_definitions RW_FS_IMPRESS >>
	        (* try to solve straight-forward cases *)
	        REPEAT IF_CASES_TAC >>
                STRONG_FS_TAC ([]@bisim_core_definitions) >>
	        `!c'. c' <> c ==> (RM.C c' = (RM with <|C := (c =+ RC') RM.C; 
	       				            PSCI := ps'|>).C c')` by (
                   FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	        ) >>
      	        TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      	       		    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
	       		    hv_mmu_fault_entry_eq_lem,
      	       		    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
	       		    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
	       		    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
	       		    nuigc_guest_mode_lem, nusgi_boot_mode_lem,
			    nuvi_boot_mode_lem, nuigc_boot_mode_lem] ) ) )
	      >| [(* bisim_send_igc *)
	          FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		      bisim_definitions RW_FS_IMPRESS >>
	          IF_CASES_TAC
	          >| [(* c = c' *)
	       	     STRONG_FS_TAC ([]@bisim_core_definitions) >>
	       	     REPEAT STRIP_TAC
	       	     >| [METIS_TAC []
	       	         ,
	       	         `!c_. c_ < RPAR.nc ==>
	       	          (nusgi((\c. RM.C c),
	       	      	     (\c. mmu_rpl_rcvd (RM.MMU c)),
	       	      	     mem_rpl_rcvd RM.m) (c_,c') =
	       	           nusgi((\c. if c' = c then RC' else RM.C c),
	       	      	     (\c. mmu_rpl_rcvd (RM.MMU c)),
	       	      	     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
	       	             RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
	       	      	 METIS_TAC [Mode_arith_lem]
	       	         ) >>
	       	         METIS_TAC [nusgi_def, Mode_arith_lem]
	       	        ]
	       	     ,
	       	     (* n <> c' *)
	       	     STRONG_FS_TAC ([]@bisim_core_definitions) >>
	       	     REPEAT STRIP_TAC
	       	     >| [METIS_TAC []
	       	         ,
	       	         `!c_. c_ < RPAR.nc ==>
	       	          (nusgi((\c. RM.C c),
	       	      	     (\c. mmu_rpl_rcvd (RM.MMU c)),
	       	      	     mem_rpl_rcvd RM.m) (c_,c') =
	       	           nusgi((\c''. if c = c'' then RC' else RM.C c''),
	       	      	     (\c. mmu_rpl_rcvd (RM.MMU c)),
	       	      	     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
	       	             RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
	       	      	 METIS_TAC [Mode_arith_lem]
	       	         ) >>
	       	         METIS_TAC [Mode_arith_lem]
	       	        ]
	       	     ]
	          ,
	          (* bisim_psci *)
	          FIND_BISIM_PREDICATES_IN_GOAL_TAC 
		      bisim_definitions RW_FS_IMPRESS
	              >| [IF_CASES_TAC >> (
	       	              METIS_TAC [PCG_PCC_inj]
	       		  )
	       		  ,
	       	          IF_CASES_TAC
	       	          >| [IF_CASES_TAC
	       	              >| [IF_CASES_TAC
	       	           	  >| [METIS_TAC [listTheory.NULL_EQ, 
	       	           			 listTheory.MAP_TL]
	       	           	      ,
	       	           	      METIS_TAC [PCG_PCC_inj]
	       	           	     ]
	       	           	  ,
	       	           	  METIS_TAC [PCG_PCC_inj]
	       	           	 ]
	       	              ,
	       	              METIS_TAC [PCG_PCC_inj]
	       	             ]
	       	         ]     
	         ]
	     ]
	 ]
      ,
      (* StopCore *)
      `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >>
       Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                              <|C := (n =+ C') (IM.G g).C; PSCI := PS'|>)
				       IM.G|>` >>
      `syncInv IM''` by ( 
          MATCH_MP_TAC syncInv_lem >>
          HINT_EXISTS_TAC >>
	  Q.UNABBREV_TAC `IM''` >>
          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
      `?c. c < RPAR.nc /\ (g = PCG c) /\ (n = PCC c)` by (
          METIS_TAC [PCGC_PPGP_inv_def, PCGC_inv_rewrites]
      ) >>
      RW_TAC std_ss [] >>
      Cases_on `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active`
      >| [(* active -> turn off *)
	  `(refcore_abs (RM.C c)).active /\ 
	   (refcore_abs (RM.C c)).H.launched` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_ctx_def >>
	      METIS_TAC [bisim_ctx_core_def]
	  ) >>
	  `Mode (RM.C c) < 2` by (
	      IMP_RES_TAC SimInvR_def
	      >| [(* Mode = 2 *)
	          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	          IMP_RES_TAC bisim_corereq_gicd_def >>
	          IMP_RES_TAC bisim_corereq_gicd_core_def >>
	          FULL_SIMP_TAC (srw_ss()) [] >> (
	              RES_TAC >>
		      FULL_SIMP_TAC (srw_ss()) []
		  )
		  ,
		  (* Creset *)
		  METIS_TAC [Creset_axiom]
		  ,
		  (* soft *)
		  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	          IMP_RES_TAC ref_inv_hist_def
		 ]
	  ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  `(refcore_req_sent (RM.C c) = EMPTY)` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_corereq_guest_def >>
	      METIS_TAC [bisim_corereq_guest_core_def]
	  ) >>
	  EXISTS_TAC ``SUC 0`` >>
	  RW_TAC std_ss [refined_comp_def, PULL_EXISTS] >>
	  FIRST_EXISTS_TAC ``CORE_RCV_EVENT c`` >>
	  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_core_rcv_event_def, 
			     PULL_EXISTS, psci_step_def, refcore_step_def] >>
	  EXISTS_TAC ``StopCore c`` >>
	  `?RC'. refcore_step_rcv_psci (RM.C c, StopCore c,RC')` by (
	      `Mode (RM.C c) <= 1` by ( RW_TAC arith_ss [] ) >>
	      METIS_TAC [refcore_psci_enabled_axiom]
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [idpsci_step_def, idcore_step_def] >> 
	  `?ps'. psci_step_snd_event (RM.PSCI, StopCore c,c,ps')` by (
	      RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	      EXISTS_TAC ``RM.PSCI with
                  <|events := (c =+ TL (RM.PSCI.events c))
	  			  RM.PSCI.events;
	  	    pow := (c =+ F) RM.PSCI.pow|>`` >>
	      IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	      IMP_RES_TAC psci_step_snd_event_def >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      `HD (MAP PEE (RM.PSCI.events c)) = StopCore (PCC c)` by (
	          METIS_TAC []
	      ) >>
	      MATCH_MP_TAC (
	          prove(``(B ==> A) /\ B ==> A /\ B``, PROVE_TAC [])
	      ) >>
	      STRIP_TAC 
	      >| [(* HD *)
		  STRIP_TAC >>
		  FULL_SIMP_TAC std_ss [HD_MAP_lem] >>
		  FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
		  Cases_on `HD (RM.PSCI.events c)` >> (
		      FULL_SIMP_TAC (srw_ss()) []
		  ) >>
		  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
		  `MEM (StopCore n) (RM.PSCI.events c)` by (
		      METIS_TAC [MEM_HD_lem]
		  ) >>
		  IMP_RES_TAC ref_inv_psci_def >>
		  FULL_SIMP_TAC std_ss [psciev_def]
		  ,
		  (* not [] *)
		  REV_FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC MAP_not_nil_lem 
		 ]
	  ) >>
	  EXISTS_TAC ``ps':psci_state`` >>
	  EXISTS_TAC ``RC':refcore`` >>
	  ASM_REWRITE_TAC [] >>
	  (* add context *)
	  IMP_RES_TAC psci_step_snd_event_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  IMP_RES_TAC refcore_psci_stop_axiom >>
	  `(idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = EMPTY) /\ 
	   (idcore_req_sent C' = EMPTY) /\ 
	   ~((idcore_abs C').active) /\ 
	   ~((idcore_abs C').H.launch) /\
           ((idcore_abs C').PC = (idcore_abs ((IM.G (PCG c)).C (PCC c))).PC) /\
           ((idcore_abs C').PSTATE = 
	    (idcore_abs ((IM.G (PCG c)).C (PCC c))).PSTATE) /\
           ((idcore_abs C').GPR = (idcore_abs ((IM.G (PCG c)).C (PCC c))).GPR) /\
           ((idcore_abs C').SPR = (idcore_abs ((IM.G (PCG c)).C (PCC c))).SPR) /\
	   (id_abs_int ((IM.G (PCG c)).C (PCC c)) = FLUSHED) /\
	   (id_abs_int C' = FLUSHED)` by (
	      IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      REV_FULL_SIMP_TAC (srw_ss()) []
	  ) >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  `Mode RC' < 2` by ( FULL_SIMP_TAC std_ss [Mode_def] ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  `~hv_guard_mmu_fault (HVabs(RM with <|C := (c =+ RC') RM.C; 
	  					PSCI := ps'|>,c),c)` by (
	      MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  `~hv_gicd_entry_state (HVabs(RM with <|C := (c =+ RC') RM.C; 
	  					 PSCI := ps'|>,c))` by (
	      MATCH_MP_TAC hv_gicd_entry_state_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  IMP_RES_TAC hv_guard_mmu_fault_lem >>
	  IMP_RES_TAC hv_gicd_entry_state_lem >>
	  (* SimInvR *)
	  `SimInvR (RM with <|C := (c =+ RC') RM.C; PSCI := ps'|>)` by (
	      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  ASM_REWRITE_TAC [] >>
	  (* prove SIM *)
	  Q.UNABBREV_TAC `IM'` >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  REPEAT STRIP_TAC >> (
	    EXCEPT_FOR_THESE [``bisim_send_igc _``, ``bisim_psci _ ``] (
	    FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	    (* try to solve straight-forward cases *)
	    REPEAT IF_CASES_TAC >>
            STRONG_FS_TAC ([]@bisim_core_definitions) >>
	    `!c'. c' <> c ==> (RM.C c' = (RM with <|C := (c =+ RC') RM.C; 
	  				            PSCI := ps'|>).C c')` by (
               FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	    ) >>
      	    TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      	  		    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
	  		    hv_mmu_fault_entry_eq_lem,
      	  		    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
	  		    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
	  		    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
	  		    nuigc_guest_mode_lem] ) ) )
	  >| [(* bisim_send_igc *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	      IF_CASES_TAC
	      >| [(* c = c' *)
	  	 STRONG_FS_TAC ([]@bisim_core_definitions) >>
	  	 REPEAT STRIP_TAC
	  	 >| [METIS_TAC []
	  	     ,
	  	     `!c_. c_ < RPAR.nc ==>
	  	      (nusgi((\c. RM.C c),
	  		     (\c. mmu_rpl_rcvd (RM.MMU c)),
	  		     mem_rpl_rcvd RM.m) (c_,c') =
	  	       nusgi((\c. if c' = c then RC' else RM.C c),
	  		     (\c. mmu_rpl_rcvd (RM.MMU c)),
	  		     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
	  	         RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
	  		 METIS_TAC [Mode_arith_lem]
	  	     ) >>
	  	     METIS_TAC [nusgi_def, Mode_arith_lem]
	  	    ]
	  	 ,
	  	 (* n <> c' *)
	  	 STRONG_FS_TAC ([]@bisim_core_definitions) >>
	  	 REPEAT STRIP_TAC
	  	 >| [METIS_TAC []
	  	     ,
	  	     `!c_. c_ < RPAR.nc ==>
	  	      (nusgi((\c. RM.C c),
	  		     (\c. mmu_rpl_rcvd (RM.MMU c)),
	  		     mem_rpl_rcvd RM.m) (c_,c') =
	  	       nusgi((\c''. if c = c'' then RC' else RM.C c''),
	  		     (\c. mmu_rpl_rcvd (RM.MMU c)),
	  		     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
	  	         RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
	  		 METIS_TAC [Mode_arith_lem]
	  	     ) >>
	  	     METIS_TAC [Mode_arith_lem]
	  	    ]
	  	]
	      ,
	      (* bisim_psci *)
	      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	      >| [IF_CASES_TAC >> (
	  	     METIS_TAC [PCG_PCC_inj]
	  	  )
	  	  ,
	  	  IF_CASES_TAC
	  	  >| [IF_CASES_TAC
	  	      >| [IF_CASES_TAC
	  	   	  >| [METIS_TAC [listTheory.NULL_EQ, 
	  	   			 listTheory.MAP_TL]
	  	   	      ,
	  	   	      METIS_TAC [PCG_PCC_inj]
	  	   	     ]
	  	   	  ,
	  	   	  METIS_TAC [PCG_PCC_inj]
	  	   	 ]
	  	      ,
	  	      METIS_TAC [PCG_PCC_inj]
	  	     ]
	  	 ]
	     ]
	  ,
	  (* already off -> no effect but on PSCI *)
	  FULL_SIMP_TAC (srw_ss()) [idpsci_step_def, idcore_step_def] >>
	  IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	  REV_FULL_SIMP_TAC (srw_ss()) [] >>
	  IMP_RES_TAC proj_bound_lem >>
	  `Mode (RM.C c) < 2` by (
	      `Mode (RM.C c) <> 3` by (
	          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	          IMP_RES_TAC bisim_ctx_def >>
	          METIS_TAC [Mode_mode_lem, bisim_ctx_core_def] 
	      ) >>
	      IMP_RES_TAC SimInvR_def
	      >| [(* Mode = 2 *)
	          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	          IMP_RES_TAC bisim_corereq_gicd_def >>
	          IMP_RES_TAC bisim_corereq_gicd_core_def >>
	          FULL_SIMP_TAC (srw_ss()) [] >> (
	              RES_TAC >>
		      FULL_SIMP_TAC (srw_ss()) []
		  )
		  ,
		  (* Creset *)
		  METIS_TAC [Mode_def, Creset_axiom]
		  ,
		  (* soft *)
		  METIS_TAC [warm_soft_axiom, Mode_mode_lem]
		 ]
	  ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  IMP_RES_TAC InvR_core_launched_lem >>
	  `~(refcore_abs (RM.C c)).active` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_ctx_def >>
	      METIS_TAC [bisim_ctx_core_def]
	  ) >>
	  `(refcore_req_sent (RM.C c) = EMPTY)` by (
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_corereq_guest_def >>
	      METIS_TAC [bisim_corereq_guest_core_def]
	  ) >>
	  EXISTS_TAC ``SUC 0`` >>
	  RW_TAC std_ss [refined_comp_def, PULL_EXISTS] >>
	  FIRST_EXISTS_TAC ``CORE_RCV_EVENT c`` >>
	  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_core_rcv_event_def, 
			     PULL_EXISTS, psci_step_def, refcore_step_def] >>
	  EXISTS_TAC ``StopCore c`` >>
	  `?RC'. refcore_step_rcv_psci (RM.C c, StopCore c,RC')` by (
	      `Mode (RM.C c) <= 1` by ( RW_TAC arith_ss [] ) >>
	      METIS_TAC [refcore_psci_enabled_axiom]
	  ) >>
	  `?ps'. psci_step_snd_event (RM.PSCI, StopCore c,c,ps')` by (
	      RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	      EXISTS_TAC ``RM.PSCI with
                  <|events := (c =+ TL (RM.PSCI.events c))
	  			  RM.PSCI.events;
	  	    pow := (c =+ F) RM.PSCI.pow|>`` >>
	      IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	      IMP_RES_TAC psci_step_snd_event_def >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      `HD (MAP PEE (RM.PSCI.events c)) = StopCore (PCC c)` by (
	          METIS_TAC []
	      ) >>
	      MATCH_MP_TAC (
	          prove(``(B ==> A) /\ B ==> A /\ B``, PROVE_TAC [])
	      ) >>
	      STRIP_TAC 
	      >| [(* HD *)
		  STRIP_TAC >>
		  FULL_SIMP_TAC std_ss [HD_MAP_lem] >>
		  FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
		  Cases_on `HD (RM.PSCI.events c)` >> (
		      FULL_SIMP_TAC (srw_ss()) []
		  ) >>
		  FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
		  `MEM (StopCore n) (RM.PSCI.events c)` by (
		      METIS_TAC [MEM_HD_lem]
		  ) >>
		  IMP_RES_TAC ref_inv_psci_def >>
		  FULL_SIMP_TAC std_ss [psciev_def]
		  ,
		  (* not [] *)
		  REV_FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC MAP_not_nil_lem 
		 ]
	  ) >>
	  EXISTS_TAC ``ps':psci_state`` >>
	  EXISTS_TAC ``RC':refcore`` >>
	  ASM_REWRITE_TAC [] >>
	  (* add context *)
	  IMP_RES_TAC psci_step_snd_event_def >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  IMP_RES_TAC refcore_psci_stop_axiom >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  `Mode RC' < 2` by ( FULL_SIMP_TAC std_ss [Mode_def] ) >>
	  IMP_RES_TAC soft_Mode_lem >>
	  `~hv_guard_mmu_fault (HVabs(RM with <|C := (c =+ RM.C c) RM.C; 
	  					PSCI := ps'|>,c),c)` by (
	      MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  `~hv_gicd_entry_state (HVabs(RM with <|C := (c =+ RM.C c) RM.C; 
	  					 PSCI := ps'|>,c))` by (
	      MATCH_MP_TAC hv_gicd_entry_state_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  IMP_RES_TAC hv_guard_mmu_fault_lem >>
	  IMP_RES_TAC hv_gicd_entry_state_lem >>
	  (* SimInvR *)
	  `SimInvR (RM with <|C := (c =+ RM.C c) RM.C; PSCI := ps'|>)` by (
	      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  ASM_REWRITE_TAC [] >>
	  (* prove SIM *)
	  Q.UNABBREV_TAC `IM'` >>
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  REPEAT STRIP_TAC >> (
	    EXCEPT_FOR_THESE [``bisim_psci _ ``] (
	    FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	    (* try to solve straight-forward cases *)
	    REPEAT IF_CASES_TAC >>
            STRONG_FS_TAC ([]@bisim_core_definitions) >>
	    `!c'. c' <> c ==> (RM.C c' = (RM with <|C := (c =+ RM.C c) RM.C; 
	  				            PSCI := ps'|>).C c')` by (
               FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	    ) >>
      	    TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      	  		    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
	  		    hv_mmu_fault_entry_eq_lem,
      	  		    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
	  		    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
	  		    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
	  		    nuigc_guest_mode_lem] ) ) 
	  ) >>
	  (* bisim_psci *)
	  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	  >| [IF_CASES_TAC >> (
	          METIS_TAC [PCG_PCC_inj]
	      )
	      ,
	      IF_CASES_TAC
	      >| [IF_CASES_TAC
	       	  >| [IF_CASES_TAC
	       	      >| [METIS_TAC [listTheory.NULL_EQ, 
	       			     listTheory.MAP_TL]
	       		  ,
	       		  METIS_TAC [PCG_PCC_inj]
	       		 ]
	       	      ,
	       	      METIS_TAC [PCG_PCC_inj]
	       	     ]
	       	  ,
	       	  METIS_TAC [PCG_PCC_inj]
	         ]
	     ]
	 ]
     ]
);

val ideal_core_snd_req_lem = store_thm("ideal_core_snd_req_lem", ``
!RM IM g cg c C' cif' IM' RC' MMU' r.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ g < PAR.ng
/\ cg < PAR.nc_g g
/\ idcore_step_snd_req ((IM.G g).C cg,r,C')
/\ bif_step ((IM.G g).cif cg,RCV (MREQ r),cif')
/\ sync_shared_mem_upd_of_guest (<|G := (g =+ IM.G g with
     <|C := (cg =+ C') (IM.G g).C; cif := (cg =+ cif') (IM.G g).cif|>) IM.G|>,g,IM')
/\ c < RPAR.nc
/\ (PCG c = g)
/\ (PCC c = cg)
/\ (idcore_abs ((IM.G g).C cg)).active
/\ Mode (RM.C c) < 2
/\ (mmu_abs (RM.MMU c)).active
/\ refcore_step_snd_req (RM.C c,r,RC')
/\ mmu_step_rcv_req (RM.MMU c,r,MMU')
/\ ((idcore_abs C').PC = (refcore_abs RC').PC)
/\ ((idcore_abs C').PSTATE = (refcore_abs RC').PSTATE)
/\ ((idcore_abs C').GPR = (refcore_abs RC').GPR)
/\ (!R. (idcore_abs C').SPR R = (refcore_abs RC').SPR (INL R))
 /\ (idcore_int C' = refcore_int RC') 
==>
   refined_comp(RM, 1, RM with <| C:=(c =+ RC') RM.C; MMU:=(c =+ MMU') RM.MMU|>)
/\ SIM (RM with <| C:=(c =+ RC') RM.C; MMU:=(c =+ MMU') RM.MMU|>,IM')
``,
  RW_TAC std_ss [] >- (
      (* case: refined_comp *)
      REWRITE_TAC [refined_comp_def, prove(``1 = SUC 0``, RW_TAC arith_ss [])] >>
      EXISTS_TAC ``CORE_SND_MREQ c`` >>
      EXISTS_TAC ``RM:refined_model`` >>
      RW_TAC (srw_ss()) [refined_trans_def, ref_rule_core_snd_mreq_def, 
			 refcore_step_def, mmu_step_def] >>
      METIS_TAC []
  ) >>
  IMP_RES_TAC soft_Mode_lem >>
  (* case: SIM *)
  `syncInv (<|G := (PCG c =+ IM.G (PCG c) with
                   <|C := (PCC c =+ C') (IM.G (PCG c)).C;
		     cif := (PCC c =+ cif') (IM.G (PCG c)).cif|>) IM.G|>)` by (
      `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
      `!g. g < PAR.ng ==>
       ((IM.G g).m = 
       ((<|G := (PCG c =+ IM.G (PCG c) with
             <|C := (PCC c =+ C') (IM.G (PCG c)).C;
	      cif := (PCC c =+ cif') (IM.G (PCG c)).cif|>) IM.G|>).G g).m)` 
      by ( STRONG_FS_TAC [] ) >>
      METIS_TAC [syncInv_lem]
  ) >>
  FULL_SIMP_TAC (srw_ss()) [bif_step_def, bif_step_rcv_req_def, 
			    sync_shared_mem_upd_of_guest_def] >>
  IMP_RES_TAC (idcore_step_axiom // "snd_req") >>
  IMP_RES_TAC mmu_corereq_axiom >>
  IMP_RES_TAC refcore_send_axiom >>
  `~(idcore_abs ((IM.G (PCG c)).C (PCC c))).H.launch` by (
      `inv_good_idcore ((IM.G (PCG c)).C (PCC c))` by (
          FULL_SIMP_TAC (srw_ss()) [InvI_EXPAND ``(PCG c)``]
      ) >>
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [inv_good_idcore_def]
  ) >>
  IMP_RES_TAC hv_gicd_entry_state_lem >>
  IMP_RES_TAC hv_guard_mmu_fault_lem >>
  `~hv_gicd_entry_state 
    (HVabs (RM with <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>,c)) /\
   ~hv_guard_mmu_fault
    (HVabs (RM with <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>,c),c)` 
  by (
      `(RM with <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>).C c = RC'`
      by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      METIS_TAC [hv_gicd_entry_state_lem, hv_guard_mmu_fault_lem]
  ) >> 
  `~soft (refcore_abs RC')` by ( METIS_TAC [soft_Mode_lem] ) >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >>
  EXCEPT_FOR ``bisim_send_igc (RM',IM')`` (  
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
  (* try to solve straight-forward cases *)
      TRY ( REPEAT IF_CASES_TAC >> 
      FULL_SIMP_TAC (srw_ss()++ARITH_ss) ([HVabs_def, nuvi_def, nuigc_def, nusgi_def, bisim_pi_guest_def, pred_setTheory.UNION_DEF, pred_setTheory.EXTENSION, combinTheory.APPLY_UPDATE_THM]@bisim_core_definitions) >>
      TRY ( METIS_TAC [IN_DEF, PCG_PCC_inj, proj_bound_lem, Mode_PCC_lem, Mode_mode_lem, Trreq_eq_req_lem, Mode_arith_lem, good_proj_in_range_impls] ) ) 
  ) >>
  (* case: bisim_send_igc *)
  MATCH_MP_TAC bisim_send_igc_core_step_lem >>
  EXISTS_TAC ``RM:refined_model`` >>
  EXISTS_TAC ``IM:ideal_model`` >>
  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
  METIS_TAC [Mode_arith_lem]
);

val ideal_core_snd_req_InvI_lem = store_thm("ideal_core_snd_req_InvI_lem", ``
!IM g n G' IM' IM''.
   InvI IM
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_SND_MREQ n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
InvI IM'
``,
  METIS_TAC [ideal_INTERNAL_InvI_lem]
);


val core_mmu_SimInvR_lem = store_thm("core_mmu_SimInvR_lem", ``
!RM c r C' MMU' m'.
   c < RPAR.nc
/\ PAdr r NOTIN RPAR.Amap GICD
/\ InvR RM
/\ SimInvR RM
/\ ( (Mode C' < 2 \/
      (Mode C' = 2) /\
       (refcore_abs C').PC IN {AHV PC_GICD_SAVE_CTX; AHV PC_GICD_FILTER}) 
    \/ (refcore_abs C' = Creset c) \/ soft (refcore_abs C')) 
/\ ((refcore_abs C').H = (refcore_abs (RM.C c)).H)
/\ (!r'. r' <> r ==> ((mmu_abs MMU').state r' = (mmu_abs (RM.MMU c)).state r'))
/\ (?l. (mmu_abs MMU').state r ∈ {IDLE; FAULT; FINAL l})
/\ (mem_abs m' (ADRDS GLOCK) = mem_abs RM.m (ADRDS GLOCK))
==>
SimInvR (RM with <|C := (c =+ C') RM.C; m := m'; MMU := (c =+ MMU') RM.MMU|>)
``,
  REPEAT GEN_TAC >>
  Q.ABBREV_TAC 
    `RM' = RM with <|C := (c =+ C') RM.C; m := m'; MMU := (c =+ MMU') RM.MMU|>` >>
  STRIP_TAC >> (      
      RW_TAC (srw_ss()) [SimInvR_def]
      >| [(* case: Glock *)
	  `RM'.m = m'` by (
     	      Q.UNABBREV_TAC `RM'` >>
     	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
          ) >>
          `(refcore_abs (RM.C 0)).H.init_hv` by (
	      `(refcore_abs (RM.C 0)).H = (refcore_abs (RM'.C 0)).H` by (
     	          Q.UNABBREV_TAC `RM'` >>
     	          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
		      METIS_TAC []
		  )
	      ) >>
	      METIS_TAC []
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
          ,
          (* case: Mode / PC *)
          `c' <> c ==> (RM'.C c' = RM.C c')` by (
     	      Q.UNABBREV_TAC `RM'` >>
     	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
          ) >>
	  `RM'.C c = C'` by (
     	      Q.UNABBREV_TAC `RM'` >>
     	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
          FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
          METIS_TAC []
          ,
          (* case: MMU state *) 
          Cases_on `c = c'`
          >| [(* case: c = c' *)
     	      Q.UNABBREV_TAC `RM'` >>
     	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]  >> (
     	      Cases_on `r = r'`
     	      >| [(* case: r = r' *)
     	          RW_TAC (srw_ss()) []
     	          ,
     	          (* case: r <> r' *)
     	          FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
     	         ]
	      )
     	      ,
     	      (* case: c <> c' *)
     	      Q.UNABBREV_TAC `RM'` >>
     	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]  >>
     	      FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
     	     ]
          ,
          (* case: no GICD requests *)
          Cases_on `r = r'`
          >| [(* case: r = r' - contradiction *)
     	      FULL_SIMP_TAC (srw_ss()) []
     	      ,
     	      (* case: r <> r' *)
     	      Cases_on `c = c'` >> (
     	          Q.UNABBREV_TAC `RM'` >>
     	          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
     	          FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
	      )
	     ]
          ,
          (* case: SMMU states *)
          Q.UNABBREV_TAC `RM'` >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
          FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
         ]
  )
);
			   
			   
val core_req_not_gicd_SimInvR_lem = store_thm("core_req_gicd_SimInvR_lem", ``
!RM c r RC' MMU'. 
   c < RPAR.nc
/\ Mode (RM.C c) < 2
/\ PAdr r NOTIN RPAR.Amap GICD
/\ InvR RM
/\ SimInvR RM
/\ refcore_step_snd_req (RM.C c,r,RC')
/\ mmu_step_rcv_req (RM.MMU c,r,MMU')
/\ (mmu_abs MMU').state r IN {FAULT; FINAL NONE}
==>
SimInvR (RM with <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>)
``,
  REPEAT GEN_TAC >> STRIP_TAC >>
  `Mode RC' < 2` by ( METIS_TAC [refcore_send_axiom] ) >>
  `!r'. r' <> r ==> ((mmu_abs MMU').state r' = (mmu_abs (RM.MMU c)).state r')`
  by ( METIS_TAC [mmu_corereq_axiom] ) >>
  `(refcore_abs RC').H = (refcore_abs (RM.C c)).H`
  by ( METIS_TAC [refcore_send_axiom] ) >>
  `RM with <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|> = 
   RM with <|C := (c =+ RC') RM.C; m := RM.m; MMU := (c =+ MMU') RM.MMU|>` by (
      FULL_SIMP_TAC (srw_ss()) [refined_model_component_equality]  
  ) >> 
  RW_TAC (srw_ss()) [] >>
  MATCH_MP_TAC core_mmu_SimInvR_lem >> 
  FULL_SIMP_TAC (srw_ss()) [] >> (
      METIS_TAC []
  )
);


(* HARD: core + MMU translation steps in both models **GUEST/SWITCH**
need to use core bisimulation property to show that same request can be sent 
need to step MMU until fault or final state, requires golden comp argument *)
val ideal_CORE_SND_MREQ_sim_step_lem = store_thm("ideal_CORE_SND_MREQ_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_SND_MREQ n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_core_snd_req_def] >>
  FULL_SIMP_TAC (srw_ss()) [idcore_step_def] >>
  `?c. c = PCGC_inv (g, n)` by ( RW_TAC (srw_ss()) [] ) >>
  `c < RPAR.nc /\ (PCG c = g) /\ (PCC c = n)` by (
      IMP_RES_TAC PCGC_PPGP_inv_def >>
      FULL_SIMP_TAC (srw_ss()) [] 
  ) >> 
  `(idcore_abs((IM.G g).C n)).active /\ (idcore_req_sent ((IM.G g).C n) = EMPTY)`
  by (
      METIS_TAC [idcore_step_axiom // "snd_req"]
  ) >>
  IMP_RES_TAC SimInvR_no_req_mode_lem >>
  `refcore_req_sent (RM.C c) = EMPTY` by (
      METIS_TAC [SIM_EXPAND, bisim_corereq_guest_def, bisim_corereq_guest_core_def] ) >> 
  IMP_RES_TAC mmu_active_lem >>
  (* EXIST of first refined step *)
  `?RC'. refcore_step_snd_req(RM.C c, r, RC')
   /\ ((idcore_abs C').PC = (refcore_abs RC').PC)
   /\ ((idcore_abs C').PSTATE = (refcore_abs RC').PSTATE)
   /\ ((idcore_abs C').GPR = (refcore_abs RC').GPR)
   /\ (!R. (idcore_abs C').SPR R = (refcore_abs RC').SPR (INL R))
   /\ (idcore_int C' = refcore_int RC')` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND, bisim_ctx_def, bisim_ctx_core_def] >>
      METIS_TAC [Mode_def, iMode_def, mode_def, core_send_ideal_bisim_axiom, 
		 Mode_arith_lem]
  ) >>
  `?MMU'. mmu_step_rcv_req (RM.MMU c, r, MMU')` by (
      `r NOTIN ((IM.G g).cif n).req_rcvd` by (
          FULL_SIMP_TAC (srw_ss()) [bif_step_def, bif_step_rcv_req_def] 
      ) >>
      `r NOTIN mmu_req_rcvd (RM.MMU c)` by (
          CCONTR_TAC >>
	  METIS_TAC [SIM_EXPAND, bisim_mmureq_guest_def, 
		     bisim_mmureq_guest_core_def]
      ) >>
      METIS_TAC [mmu_rcv_req_enabled_axiom]
  ) >> 
  `refined_comp(RM, 1, RM with <| C:=(c =+ RC') RM.C; MMU:=(c =+ MMU') RM.MMU|>)
   /\ SIM (RM with <| C:=(c =+ RC') RM.C; MMU:=(c =+ MMU') RM.MMU|>,IM')` by (
      METIS_TAC [ideal_core_snd_req_lem]
  ) >>
  (* perform MMU translation *)
  Q.ABBREV_TAC 
      `RM' = RM with <|C := (c =+ RC') RM.C; MMU := (c =+ MMU') RM.MMU|>` >>
  `InvR RM'` by ( METIS_TAC [refined_comp_InvR_lem] ) >>
  `InvI IM'` by ( 
      METIS_TAC [ideal_core_snd_req_InvI_lem |> 
		 SIMP_RULE (srw_ss()) [ideal_guest_trans_def,
				       id_rule_core_snd_req_def, 
				       idcore_step_def] ] 
  ) >>
  `Mode (RM'.C c) < 2` by (
      Q.UNABBREV_TAC `RM'` >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC [refcore_send_axiom]
  ) >>
  `(refcore_abs (RM'.C c)).H.init_core` by ( METIS_TAC [init_core_lem] ) >> 
  `mmu_golden_conf (RM'.MMU c, GI (PCG c), MMU_GI(PCG c), RPAR.A_PT (PCG c),
		    golden_RO (PCG c), Trans (PCG c))` by (
      METIS_TAC [mmu_golden_conf_lem]
  ) >>
  `r IN mmu_req_rcvd (RM'.MMU c) /\ 
   (mmu_abs (RM'.MMU c)).state r IN {TRANS NONE; FAULT}` by (
      Q.UNABBREV_TAC `RM'` >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]  >>
      `(mmu_req_rcvd MMU' = mmu_req_rcvd (RM.MMU c) UNION {r}) /\
       (mmu_abs MMU').state r IN {TRANS NONE; FAULT}` by (
          METIS_TAC [mmu_corereq_axiom]
      ) >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  FULL_SIMP_TAC (srw_ss()) [] 
  >| [(* case: need to continue with translation *)
      `?MMU'' m. m > 0 /\ mmu_golden_comp(RM'.MMU c, r, GI (PCG c), MMU'', m)
	      /\ (mmu_abs MMU'').state r IN {FAULT; FINAL NONE}` by (
          METIS_TAC [mmu_golden_trans_axiom]
      ) >>
      `?m'.
            refined_comp (RM',2 * m,RM' with 
                <|m := m'; MMU := (c =+ MMU'') RM'.MMU|>) 
         /\ SIM (RM' with <|m := m'; MMU := (c =+ MMU'') RM'.MMU|>,IM') 
         /\ InvR (RM' with <|m := m'; MMU := (c =+ MMU'') RM'.MMU|>) 
         /\ Mode ((RM' with <|m := m'; MMU := (c =+ MMU'') RM'.MMU|>).C c) < 2 
	 /\ r IN mmu_req_rcvd ((RM' with <|m := m'; MMU := (c =+ MMU'') RM'.MMU|>).MMU c)
	 /\ (mem_abs m' = mem_abs RM'.m)` by (
          METIS_TAC [golden_comp_lem]
      ) >>
      Q.ABBREV_TAC 
          `RM'' = RM' with <|m := m'; MMU := (c =+ MMU'') RM'.MMU|>` >>
      `refined_comp(RM, 1 + 2 * m, RM'')` by (
          METIS_TAC [refined_comp_concat_lem]
      ) >>
      (* cases on GICD request *)
      Cases_on `PAdr r IN RPAR.Amap GICD`
      >| [(* case: GICD request, TODO: need lemma stepping into hypervisor *)
	  cheat
	  ,
	  (* case: normal request, finish up, prove SimInvR *)
	  EXISTS_TAC ``1 + 2 * m`` >>
	  HINT_EXISTS_TAC >>
	  RW_TAC (srw_ss()) [] >>
	  Q.UNABBREV_TAC `RM'` >>
	  Q.UNABBREV_TAC `RM''` >>
	  Q.ABBREV_TAC `RS = {FAULT; FINAL NONE}` >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM,
				    combinTheory.UPDATE_EQ] >>
  	  MATCH_MP_TAC core_mmu_SimInvR_lem >> 
	  HINT_EXISTS_TAC >>
	  RW_TAC (srw_ss()) []
	  >| [(* case: refcore.H *)
	      METIS_TAC [refcore_send_axiom]
	      ,
	      (* case: mmu state r' *)
	      `(mmu_abs MMU').state r' = (mmu_abs (RM.MMU c)).state r'` by (
	          METIS_TAC [mmu_corereq_axiom]
	      ) >>
              `inv_good_mmu MMU'` by (
	          FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND,
					    combinTheory.APPLY_UPDATE_THM] >>
		  METIS_TAC []
	      ) >>
	      `(mmu_abs MMU'').state r' = (mmu_abs MMU').state r'` by (
	          METIS_TAC [golden_comp_mmu_state_lem]
	      ) >>
	      METIS_TAC []
	      ,
	      (* case: mmu state r *)
	      Q.UNABBREV_TAC `RS` >>
	      FULL_SIMP_TAC (srw_ss()) []
	     ]
	 ]
      ,
      (* case: FAULT *)
      Cases_on `PAdr r IN RPAR.Amap GICD`
      >| [(* case: GICD fault - TODO: need lemma stepping into hypervisor *)
	  cheat
	  ,
	  (* case: normal fault - finish by proving SimInvR *)
	  EXISTS_TAC ``1`` >>
	  HINT_EXISTS_TAC >>
	  RW_TAC (srw_ss()) [] >>
	  Q.UNABBREV_TAC `RM'` >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  METIS_TAC [core_req_not_gicd_SimInvR_lem |> SIMP_RULE (srw_ss()) []]
	 ]
     ]
);

val bisim_core_internal_lem = store_thm("bisim_core_internal_lem", ``
!RM IM c RC' IC'.
    c < RPAR.nc
 /\ InvI IM
 /\ InvR RM
 /\ SIM (RM,IM)
 /\ Mode (RM.C c) < 2
 /\ Mode RC' < 2
 /\ refcore_step_internal (RM.C c,RC')
 /\ idcore_step_internal ((IM.G (PCG c)).C (PCC c),IC')
==>
bisim_ctx_core (idcore_abs IC', 
		refcore_abs RC', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC RC',c),
	        ectx RC',
                refcore_int RC',
                idcore_int IC') /\
(refcore_abs RC').active /\ 
(refcore_req_sent RC' = refcore_req_sent (RM.C c)) /\
((refcore_abs RC').H = (refcore_abs (RM.C c)).H) /\
(idcore_req_sent IC' = idcore_req_sent ((IM.G (PCG c)).C (PCC c))) /\ 
(idcore_abs IC').active /\ 
((idcore_abs IC').H = (idcore_abs ((IM.G (PCG c)).C (PCC c))).H) /\ 
iMode ((IM.G (PCG c)).C (PCC c)) < 2 /\
iMode IC' < 2
``,
  NTAC 6 STRIP_TAC >>
  IMP_RES_TAC soft_Mode_lem >>
  IMP_RES_TAC refcore_internal_axiom >>
  IMP_RES_TAC (idcore_step_axiom // "internal") >>
  IMP_RES_TAC bisim_guest_mode_lem >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  IMP_RES_TAC bisim_corereq_guest_def >>
  IMP_RES_TAC bisim_corereq_guest_core_def >>
  `(idcore_int ((IM.G (PCG c)).C (PCC c)) = refcore_int (RM.C c)) /\
   ((idcore_abs ((IM.G (PCG c)).C (PCC c))).GPR = (refcore_abs (RM.C c)).GPR) /\
   ((idcore_abs ((IM.G (PCG c)).C (PCC c))).PSTATE =
       (refcore_abs (RM.C c)).PSTATE) /\
   ((idcore_abs ((IM.G (PCG c)).C (PCC c))).PC = (refcore_abs (RM.C c)).PC) /\
   (!r. (idcore_abs ((IM.G (PCG c)).C (PCC c))).SPR r =
        (refcore_abs (RM.C c)).SPR (INL r)) /\
   (refcore_abs (RM.C c)).H.launched` by (
      REV_FULL_SIMP_TAC arith_ss [bisim_ctx_core_def, Mode_mode_lem]
  ) >>
  `((idcore_abs IC').PC = (refcore_abs RC').PC) /\
   ((idcore_abs IC').PSTATE = (refcore_abs RC').PSTATE) /\
   ((idcore_abs IC').GPR = (refcore_abs RC').GPR) /\
   (!R. (idcore_abs IC').SPR R = (refcore_abs RC').SPR (INL R)) /\
   (idcore_int IC' = refcore_int RC')` by (
      METIS_TAC [core_internal_bisim_axiom]
  ) >>
  FULL_SIMP_TAC arith_ss [bisim_ctx_core_def, Mode_mode_lem]
);

(* EASY: same step in both models, only core affected **GUEST/SWITCH** *)
val ideal_CORE_INTERNAL_sim_step_lem = store_thm("ideal_CORE_INTERNAL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_INTERNAL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  REPEAT STRIP_TAC >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >>
  `syncInv IM''` by ( 
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      FULL_SIMP_TAC (srw_ss()) [ideal_guest_trans_def, 
				id_rule_core_internal_def]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  FULL_SIMP_TAC (srw_ss()) [ideal_guest_trans_def, 
			    id_rule_core_internal_def, idcore_step_def] >>
  RW_TAC std_ss [] >>
  (* existence of refined internal step *)
  `?c. c = PCGC_inv (g, n)` by ( RW_TAC (srw_ss()) [] ) >>
  `c < RPAR.nc /\ (PCG c = g) /\ (PCC c = n)` by (
      IMP_RES_TAC PCGC_PPGP_inv_def >>
      FULL_SIMP_TAC (srw_ss()) [] 
  ) >> 
  RW_TAC std_ss [] >>
  `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active /\ 
   (idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = EMPTY)` by (
      IMP_RES_TAC ( idcore_step_axiom // "internal" ) >>
      ASM_REWRITE_TAC []
  ) >>
  `Mode (RM.C c) < 2` by ( METIS_TAC [SimInvR_no_req_mode_lem] ) >>
  `refcore_req_sent (RM.C c) = EMPTY` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_corereq_guest_def >>
      IMP_RES_TAC bisim_corereq_guest_core_def >>
      FULL_SIMP_TAC std_ss []
  ) >>
  IMP_RES_TAC bisim_refined_core_active_lem >>
  `?RC'. refcore_step_internal (RM.C c,RC') /\ (Mode RC' < 2)` by (
      METIS_TAC [refcore_internal_enabled_axiom]
  ) >>
  EXISTS_TAC ``SUC 0`` >>
  EXISTS_TAC ``RM with C := (c =+ RC') RM.C`` >>
  RW_TAC std_ss [refined_comp_def]
  >| [(* refined computation *)
      EXISTS_TAC ``CORE_INTERNAL c`` >>
      RW_TAC (srw_ss()) [refined_trans_def, ref_rule_core_internal_def,
			 refcore_step_def] >>
      HINT_EXISTS_TAC >>
      RW_TAC (srw_ss()) []
      ,
      (* SIM *)
      `bisim_ctx_core
          (idcore_abs C',refcore_abs RC',
      	   ctxs (mem_abs RM.m (ADRDS (CTX c))) (sc_done_IGC RC',c),
      	   ectx RC',refcore_int RC',idcore_int C') /\
       (refcore_abs RC').active /\
       (refcore_req_sent RC' = refcore_req_sent (RM.C c)) /\
       ((refcore_abs RC').H = (refcore_abs (RM.C c)).H) /\
       (idcore_req_sent C' = idcore_req_sent ((IM.G (PCG c)).C (PCC c))) /\
       (idcore_abs C').active /\
       ((idcore_abs C').H = (idcore_abs ((IM.G (PCG c)).C (PCC c))).H) /\
       iMode ((IM.G (PCG c)).C (PCC c)) < 2 /\ iMode C' < 2` by (
          METIS_TAC [bisim_core_internal_lem]
      ) >>
      `~hv_guard_mmu_fault (HVabs(RM with C := (c =+ RC') RM.C,c),c)` by (
          MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `~hv_gicd_entry_state (HVabs(RM with C := (c =+ RC') RM.C,c))` by (
	  MATCH_MP_TAC hv_gicd_entry_state_lem >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      (* prove SIM *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
	(* most cases *)
      EXCEPT_FOR ``bisim_send_igc _``
       (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	FULL_SIMP_TAC (srw_ss()) 
	    (nuigc_def::(bisim_pi_guest_def::bisim_core_definitions)) >>
	TRY (Cases_on `n=c`) >>
	REPEAT IF_CASES_TAC >>	  
	FULL_SIMP_TAC (srw_ss()++ARITH_ss) 
	    [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
	     HVabs_def, nuvi_def] >>
	REV_FULL_SIMP_TAC arith_ss [] >>
	TRY (INFS_LIMITED_METIS_TAC 1 
	         [PCG_PCC_inj, good_proj_in_range_impls, Mode_arith_lem, 
		  Mode_def, Trrpl_eq_rpl_lem, AHV_corollaries]
	    )
       ) 
      ) >>
      (* send_igc *)
      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
      EXISTS_TAC ``RM:refined_model`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC arith_ss [AHV_corollaries]
      )
      ,
      (* SimInvR *)
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      REPEAT STRIP_TAC
      >| [(* Glock *)
	  `(refcore_abs RC').H = (refcore_abs (RM.C c)).H` by (
	      IMP_RES_TAC refcore_internal_axiom
	  ) >>
	  Cases_on `c=0` >> (
	      FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      REV_FULL_SIMP_TAC std_ss []
	  )
	  ,
	  (* Mode *)
	  Cases_on `c=c'` >> (
	      FULL_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	  )
	 ]
     ]
);

(* MEDIUM: success case of PSCI handler, two steps, memory not affected *)
val ideal_CORE_SND_ELIST_sim_step_lem = store_thm("ideal_CORE_SND_ELIST_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_SND_ELIST n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* EASY: fail case of PSCI handler, two steps, only core affected *)
val ideal_CORE_FAIL_PSCI_sim_step_lem = store_thm("ideal_CORE_FAIL_PSCI_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_FAIL_PSCI n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* EASY: fail case of SIGC handler, only core affected *)
val ideal_CORE_FAIL_SIGC_sim_step_lem = store_thm("ideal_CORE_FAIL_SIGC_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CORE_FAIL_SIGC n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* EASY: same step in both models, need SMMU coupling for reply **GUEST/SWITCH** *)
val ideal_PER_RCV_DMARPL_sim_step_lem = store_thm("ideal_PER_RCV_DMARPL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_RCV_DMARPL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_rcv_dmarpl_def,
		     per_wrap_step_def, per_step_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  Q.ABBREV_TAC `IM'' = <|G := (PPG p =+ IM.G (PPG p) with
                         <|P := (PPP p =+ P') (IM.G (PPG p)).P;
			   pif := (PPP p =+ pif') (IM.G (PPG p)).pif|>) 
				   IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  IMP_RES_TAC SimInvR_smmu_no_TRANS_lem >>
  (* forwarded reply *)
  `?q. q IN ((IM.G (PPG p)).pif (PPP p)).req_rcvd /\ match (q,r) 
    /\ r IN ((IM.G (PPG p)).pif (PPP p)).rpl_rcvd` by (
      METIS_TAC [bif_step_snd_rpl_def]
  ) >>
  `q' = q` by ( METIS_TAC [unique_match_thm] ) >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC bif_step_snd_reply_lem >>
  `q IN per_req_sent (RM.P p).st` by (
      IMP_RES_TAC SIM_bisim_periph >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  `per_active (RM.P p).st` by ( IMP_RES_TAC per_active_req_lem ) >>
  `(mmu_abs (RM.SMMU p)).active` by ( IMP_RES_TAC smmu_per_active_lem ) >>
  (* first build peripheral step *)
  `per_step_rcv_rpl ((RM.P p).st,r,P'.st)` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  (* mmu step *)
  `q IN mmu_req_rcvd (RM.SMMU p)` by ( 
      METIS_TAC [bisim_pif_req_rcvd_lem] 
  ) >>
  `Trrpl (PPG p) r IN mmu_rpl_rcvd (RM.SMMU p) /\ 
   IS_SOME(Trans (PPG p) (Rpl_PAdr r))` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_smmureq_def]
  ) >>
  `?R TR. ((mmu_abs(RM.SMMU p)).state R = FINAL (SOME TR)) 
       /\ match(TR,Trrpl (PPG p) r)` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [ref_inv_mmurpl_def]
  ) >> 
  `R IN mmu_req_rcvd (RM.SMMU p)` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [inv_good_mmu_def, MMUstate_distinct]
  ) >>
  `match(Trreq (PPG p) q,Trrpl (PPG p) r)` by (
      `q = ReqOf r` by METIS_TAC [match_ReqOf_lem] >>
      IMP_RES_TAC good_match_lem >>
      `IS_SOME (Trans (PPG p) (PAdr q))` by (
  	 METIS_TAC [Rpl_PAdr_ReqOf_lem]
      ) >>
      METIS_TAC [Trans_match_lem]
  ) >>
  `TR = Trreq (PPG p) q` by ( METIS_TAC [unique_match_thm] ) >>
  FULL_SIMP_TAC std_ss [] >>
  `(Trreq (PPG p) q = Trreq (PPG p) R) /\ 
   IS_SOME (Trans (PPG p) (PAdr R))` by (
      METIS_TAC [xlated_smmu_rpl_lem]
  ) >>
  `R = q` by ( METIS_TAC [Trreq_eq_req_lem] ) >>
  RW_TAC std_ss [] >>
  `?q SMMU'. mmu_step_snd_rpl (RM.SMMU p,q,SMMU') /\ match (R,q) /\
     Rpl_val_eq q (Trrpl (PPG p) r)` by ( 
      MATCH_MP_TAC mmu_final_rpl_axiom >>
      HINT_EXISTS_TAC >>
      METIS_TAC []
  ) >>
  `q = r` by (
      IMP_RES_TAC good_match_lem >>
      `Rpl_val_eq (Trrpl (PPG p) r) r` by ( 
          METIS_TAC [Trrpl_Rpl_val_eq_lem]
      ) >>
      IMP_RES_TAC Rpl_val_eq_trans_lem >>
      IMP_RES_TAC match_Rpl_eq_lem
  ) >>
  RW_TAC std_ss [] >>
  Q.ABBREV_TAC `Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>` >>
  (* refined model step *)
  `refined_comp (RM,SUC 0,RM with 
                 <|SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [refined_comp_def] >>
      EXISTS_TAC ``PER_RCV_DMARPL p`` >>
      RW_TAC std_ss [refined_trans_def,ref_rule_per_rcv_dmarpl_def, 
		     per_wrap_step_def, per_step_def] >>
      EXISTS_TAC ``q:reply`` >>
      EXISTS_TAC ``SMMU':mmu`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``R:request`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC std_ss [mmu_step_def]
  ) >>
  (* same step executed, apply step and bisim axioms *)
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  (* add some contect about result *)
  `(mmu_rpl_rcvd SMMU' = mmu_rpl_rcvd (RM.SMMU p) DIFF {Trrpl (PPG p) q}) /\
   xlated_rpl (q,Trrpl (PPG p) q) /\ ~st2_fault q /\
   (mmu_req_rcvd SMMU' = mmu_req_rcvd (RM.SMMU p) DIFF {R}) /\
   ((mmu_abs SMMU').state R = IDLE) /\
   (!r'. r' <> R ==>
         ((mmu_abs SMMU').state r' = (mmu_abs (RM.SMMU p)).state r')) /\
   (mmu_req_sent SMMU' = mmu_req_sent (RM.SMMU p)) /\
   (mmu_ptl_hist SMMU' = mmu_ptl_hist (RM.SMMU p)) /\
   (mmu_abs SMMU').active /\
   ((mmu_abs SMMU').cfg = (mmu_abs (RM.SMMU p)).cfg)` by (
      IMP_RES_TAC match_ReqOf_lem >>
      IMP_RES_TAC mmu_reply_lem >- (
          `ReqOf q' = Trreq (PPG p) R` by (
              REV_FULL_SIMP_TAC std_ss [MMUstate_11]
          ) >>
          `q' = Trrpl (PPG p) q` by (
              MATCH_MP_TAC match_Trrpl_lem >>
              EXISTS_TAC ``R:request`` >>
              FULL_SIMP_TAC std_ss []
          ) >>
          RW_TAC std_ss []
      ) >>
      REV_FULL_SIMP_TAC std_ss [MMUstate_distinct]
  ) >>
  (* prove SimInvR *)
  `SimInvR (RM with 
       <|SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [SimInvR_def,combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC std_ss [SimInvR_def] 
      ) >>
      Cases_on `p = p'` >> (
          RW_TAC std_ss []
      ) >>
      Cases_on `r = R` >>(
          RW_TAC std_ss []
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INSERT]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  (* prove SIM *)
  IMP_RES_TAC good_match_lem >>
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|SMMU := (p =+ SMMU') RM.SMMU; 
			   P := (p =+ <|st := P'.st; 
				        IOreq_rcvd := (RM.P p).IOreq_rcvd|>)
				    RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
		       pproj_bound_lem] ) )
  ) 
);

(* EASY: same step in both models, need memory coupling for request **GUEST/SWITCH** *)
val ideal_PER_RCV_IOREQ_sim_step_lem = store_thm("ideal_PER_RCV_IOREQ_sim_step_lem", ``
!IM RM IM' IM'' r n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_RCV_IOREQ r n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_rcv_ioreq_def] >>
  Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                         <|m := m'; P := (n =+ P') (IM.G g).P|>)
				  IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
      IMP_RES_TAC mem_snd_req_axiom >>
      ASM_REWRITE_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  `?k. (c = PCC k) /\ (PCG k = PPG p) /\ k < RPAR.nc` by (
      EXISTS_TAC ``PCGC_inv (g,c)``  >>
      METIS_TAC [PCGC_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  Q.ABBREV_TAC `GuestIndex = (PCG k = PPG p)` >>
  (* forwarded IO request *)
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, per_wrap_step_def, per_step_def] >>
  IMP_RES_TAC mem_snd_req_axiom >>
  (* mem step *)
  `PAdr r <> Agicd` by (
      FULL_SIMP_TAC std_ss [coupling_axiom] >>
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [SYM Agicd_in_GICD_lem] >>
      `gicAR GICD` by ( REWRITE_TAC [gicAR_def] ) >>
      IMP_RES_TAC GICaddresses_lem >>
      `PAdr r IN RPAR.Amap GICD INTER RPAR.Amap (PER p)` suffices_by (
          FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INTER]
  ) >>
  `(Trreq (PPG p) r, CoreSender k) IN mem_req_rcvd RM.m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `(Trreq (PPG p) r, CoreSender k) NOTIN mem_req_sent RM.m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `(!q. (q,CoreSender k) IN mem_rpl_rcvd RM.m ==> 
	~match (Trreq (PPG p) r,q))` by (
      REPEAT STRIP_TAC >>
      `match (Trreq (PCG k) r, q)` by ( METIS_TAC [] )  >>
      IMP_RES_TAC pproj_bound_lem >>
      `IS_SOME (Trans (PCG k) (PAdr r))` by (
          METIS_TAC [trans_per_lem]
      ) >>
      IMP_RES_TAC proj_bound_lem >>
      `?q'. match (r,q') /\ (q = Trrpl (PCG k) q')` by ( 
          METIS_TAC [Trrpl_exists_lem]
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      `Rpl_PAdr q' <> Agicd` by ( METIS_TAC [match_PAdr_eq_lem] ) >>
      `(q',CoreSender (PCC k)) IN mem_rpl_rcvd (IM.G (PPG p)).m` by (
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
          METIS_TAC [bisim_memreq_def]
      ) >>
      RES_TAC
  ) >>
  IMP_RES_TAC pproj_bound_lem >>
  `IS_SOME (Trans (PPG p) (PAdr r))` by (
      METIS_TAC [trans_per_lem]
  ) >>
  IMP_RES_TAC A_gicper_Trreq_lem >>
  `?RM'. mem_step_snd_req (RM.m,Trreq (PPG p) r,CoreSender k,RM')` by (
      METIS_TAC [mem_snd_req_enabled_axiom]
  ) >>
  (* peripheral step *)
  `per_step_rcv_req ((RM.P p).st,Trreq (PPG p) r, P'.st)` by (
      IMP_RES_TAC Trreq_per_lem >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  Q.ABBREV_TAC `Pw' = <|st := P'.st; 
                        IOreq_rcvd := 
			    (r =+ SOME (CoreSender k))
				(RM.P p).IOreq_rcvd|>` >>
  (* refined model step *)
  `refined_comp (RM,SUC 0,RM with
                 <|m := RM'; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [refined_comp_def] >>
      EXISTS_TAC ``PER_RCV_IOREQ p`` >>
      RW_TAC std_ss [refined_trans_def,ref_rule_per_rcv_ioreq_def,
  		     per_wrap_step_def, per_step_def] >>
      EXISTS_TAC ``Trreq (PPG p) r`` >>
      EXISTS_TAC ``RM':memory`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``k:num`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC std_ss [mem_step_def] >>
      IMP_RES_TAC Trreq_per_lem >>
      ASM_REWRITE_TAC [] >>
      FULL_SIMP_TAC std_ss [coupling_axiom]
  ) >>
  (* same step executed, apply step and bisim axioms *)
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  (* add some contect about result *)
  IMP_RES_TAC mem_snd_req_axiom >>
  (* prove SimInvR *)
  `SimInvR (RM with
       <|m := RM'; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [SimInvR_def,combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC std_ss [SimInvR_def]
      ) 
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  (* prove SIM *)
  IMP_RES_TAC good_match_lem >>
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|m := RM'; 
			   P := (p =+ <|st := P'.st; 
				        IOreq_rcvd := 
					(r =+ SOME (CoreSender k))
					    (RM.P p).IOreq_rcvd|>) 
				    RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem, PSI_def] ) )
  )
);

(* EASY: same step in both models, only peripheral affected **GUEST/SWITCH** *)
val ideal_PER_RCV_PEV_sim_step_lem = store_thm("ideal_PER_RCV_PEV_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_RCV_PEV n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
?n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_rcv_pev_def,
		     per_wrap_step_def, per_step_def] >>
  Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                                    <|P := (n =+ P') (IM.G g).P|>) IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  (* existence of per step *)
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_PERIPH `` >>
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_EXT `` >>
  EXISTS_TAC ``SUC 0`` >>
  RW_TAC std_ss [refined_comp_def] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] >>
  FIRST_EXISTS_TAC ``PER_RCV_PEV p`` >>
  RW_TAC std_ss [refined_trans_def, ref_rule_per_rcv_pev_def] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] >>
  Q.ABBREV_TAC `Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>` >>
  EXISTS_TAC ``Pw':periph_wrapper`` >>
  IMP_RES_TAC good_proj_in_range_impls >>
  `!e. MEM e RM.E_in ==> evper e < RPAR.np` by ( 
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [ref_inv_E_in_def] 
  ) >>
  `per_wrap_step (RM.P p,RCV (PEV (rPEF (RM.E_in,p))),Pw')` by (
      Q.UNABBREV_TAC `Pw'` >>
      FULL_SIMP_TAC (srw_ss()) [PEF_lem, per_wrap_step_def, per_step_def]
  ) >>
  ASM_REWRITE_TAC [] >>
  (* SimInvR *)
  `SimInvR (RM with P := (p =+ Pw') RM.P)` by (
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>
  ASM_REWRITE_TAC [] >>
  (* bisim *)
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS 
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|P := (p =+ <|st := P'.st; 
				     IOreq_rcvd := (RM.P p).IOreq_rcvd|>) 
					RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem] ) )
  )
);

val ideal_per_snd_req_lem = store_thm("ideal_per_snd_req_lem", ``
!RM IM g pg p P' pif' IM' SMMU' r.
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ g < PAR.ng
/\ pg < PAR.np_g g
/\ per_step_snd_req (((IM.G g).P pg).st,r,P'.st)
/\ (P'.IOreq_rcvd = ((IM.G g).P pg).IOreq_rcvd)
/\ bif_step ((IM.G g).pif pg,RCV (MREQ r),pif')
/\ sync_shared_mem_upd_of_guest (<|G := (g =+ IM.G g with
     <|P := (pg =+ P') (IM.G g).P; pif := (pg =+ pif') (IM.G g).pif|>) IM.G|>,g,IM')
/\ p < RPAR.np
/\ (PPG p = g)
/\ (PPP p = pg)
/\ per_active ((IM.G g).P pg).st
/\ per_active (RM.P p).st
/\ (mmu_abs (RM.SMMU p)).active
/\ per_step_snd_req ((RM.P p).st,r,P'.st)
/\ Abbrev (Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>)
/\ mmu_step_rcv_req (RM.SMMU p,r,SMMU')
==>
   refined_comp(RM, 1, RM with <| P:=(p =+ Pw') RM.P; 
			          SMMU:=(p =+ SMMU') RM.SMMU|>)
/\ SIM (RM with <| P:=(p =+ Pw') RM.P; SMMU:=(p =+ SMMU') RM.SMMU|>,IM')
``,
  RW_TAC std_ss [] >- (
      (* case: refined_comp *)
      REWRITE_TAC [refined_comp_def, prove(``1 = SUC 0``, RW_TAC arith_ss [])] >>
      EXISTS_TAC ``PER_SND_DMAREQ p`` >>
      EXISTS_TAC ``RM:refined_model`` >>
      RW_TAC (srw_ss()) [refined_trans_def, ref_rule_per_snd_dmareq_def, 
			 per_wrap_step_def, per_step_def, mmu_step_def] >>
      EXISTS_TAC ``r:request`` >>
      EXISTS_TAC ``SMMU':mmu`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC (srw_ss()) []
  ) >>
  (* case: SIM *)
  `syncInv (<|G := (PPG p =+ IM.G (PPG p) with
                   <|P := (PPP p =+ P') (IM.G (PPG p)).P;
		     pif := (PPP p =+ pif') (IM.G (PPG p)).pif|>) IM.G|>)` by (
      `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
      `!g. g < PAR.ng ==>
       ((IM.G g).m = 
       ((<|G := (PPG p =+ IM.G (PPG p) with
             <|P := (PPP p =+ P') (IM.G (PPG p)).P;
	       pif := (PPP p =+ pif') (IM.G (PPG p)).pif|>) IM.G|>).G g).m)` 
      by ( STRONG_FS_TAC [] ) >>
      METIS_TAC [syncInv_lem]
  ) >>
  FULL_SIMP_TAC (srw_ss()) [bif_step_def, bif_step_rcv_req_def, 
			    sync_shared_mem_upd_of_guest_def] >>
  IMP_RES_TAC (per_send_dma_axiom) >>
  IMP_RES_TAC mmu_corereq_axiom >>
  Q.UNABBREV_TAC `Pw'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
  REPEAT STRIP_TAC >>
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|SMMU := (p =+ SMMU') RM.SMMU; 
			   P := (p =+ <|st := P'.st; 
				        IOreq_rcvd := (RM.P p).IOreq_rcvd|>) 
				    RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem, 
		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem, 
		       hv_mmu_fault_entry_eq_lem,
		       PPT_Trreq_lem, pproj_bound_lem] ) )
);

val per_smmu_SimInvR_lem = store_thm("per_smmu_SimInvR_lem", ``
!RM p r P' SMMU' m'.
   p < RPAR.np
/\ InvR RM
/\ SimInvR RM
/\ (!r'. r' <> r ==> ((mmu_abs SMMU').state r' = (mmu_abs (RM.SMMU p)).state r'))
/\ (?l. (mmu_abs SMMU').state r ∈ {IDLE; FAULT; FINAL l})
/\ (mem_abs m' (ADRDS GLOCK) = mem_abs RM.m (ADRDS GLOCK))
==>
SimInvR (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ P') RM.P|>)
``,
  REPEAT STRIP_TAC >>		
  Q.ABBREV_TAC `RS = {IDLE; FAULT; FINAL l}` >>
  FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
  RW_TAC (srw_ss()) [] >>  
  Cases_on `p = p'`
  >| [(* case: p = p' *)
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      Cases_on `r = r'`
      >| [(* case: r = r' *)
	  Q.UNABBREV_TAC `RS` >>
	  FULL_SIMP_TAC (srw_ss()) [] 
	  ,
	  (* case: r <> r' *)
	  METIS_TAC []
	 ]
      ,
      (* case: p <> p' *)
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
     ]
);


(* HARD: same peripheral step in both models, **GUEST/SWITCH**
need to step SMMU until fault or final state, requires golden comp argument *)
val ideal_PER_SND_DMAREQ_sim_step_lem = store_thm("ideal_PER_SND_DMAREQ_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_SND_DMAREQ n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
?n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_snd_dmareq_def] >>
  FULL_SIMP_TAC (srw_ss()) [per_wrap_step_def, per_step_def] >>
  `?p. p = PPGP_inv (g, n)` by ( RW_TAC (srw_ss()) [] ) >>
  `p < RPAR.np /\ (PPG p = g) /\ (PPP p = n)` by (
      IMP_RES_TAC PCGC_PPGP_inv_def >>
      FULL_SIMP_TAC (srw_ss()) [] 
  ) >> 
  `per_active ((IM.G g).P n).st`  by (
      METIS_TAC [per_send_dma_axiom]
  ) >>
  `per_active (RM.P p).st` by ( METIS_TAC [SIM_EXPAND, bisim_periph_def] ) >> 
  `(mmu_abs (RM.SMMU p)).active` by ( IMP_RES_TAC smmu_per_active_lem  ) >>
  (* EXIST of first refined step *)
  `per_step_snd_req((RM.P p).st, r, P'.st)` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  `?SMMU'. mmu_step_rcv_req (RM.SMMU p, r, SMMU')` by (
      `r NOTIN ((IM.G g).pif n).req_rcvd` by (
          FULL_SIMP_TAC (srw_ss()) [bif_step_def, bif_step_rcv_req_def] 
      ) >>
      `r NOTIN mmu_req_rcvd (RM.SMMU p)` by (
	  METIS_TAC [SIM_EXPAND, bisim_smmureq_def]
      ) >>
      METIS_TAC [mmu_rcv_req_enabled_axiom]
  ) >> 
  Q.ABBREV_TAC `Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>` >>
  `refined_comp(RM, 1, RM with <| P:=(p =+ Pw') RM.P; 
			          SMMU:=(p =+ SMMU') RM.SMMU|>)
   /\ SIM (RM with <| P:=(p =+ Pw') RM.P; SMMU:=(p =+ SMMU') RM.SMMU|>,IM')` by (
      MATCH_MP_TAC ideal_per_snd_req_lem >>
      METIS_TAC []
  ) >>
  (* perform MMU translation *)
  Q.ABBREV_TAC 
      `RM' = RM with <|P := (p =+ Pw') RM.P; SMMU := (p =+ SMMU') RM.SMMU|>` >>
  `InvR RM'` by ( METIS_TAC [refined_comp_InvR_lem] ) >>
  `InvI IM'` by ( 
      METIS_TAC [ideal_INTERNAL_InvI_lem |> SPEC ``IR_PER_SND_DMAREQ n`` |>
		 SIMP_RULE (srw_ss()) [ideal_guest_trans_def,
				       id_rule_per_snd_dmareq_def, 
				       per_wrap_step_def,per_step_def] ] 
  ) >>
  `per_active (RM'.P p).st` by (
      Q.UNABBREV_TAC `RM'` >>
      Q.UNABBREV_TAC `Pw'` >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC [per_send_dma_axiom]
  ) >>
  `mmu_golden_conf (RM'.SMMU p, GIP (PPG p), SMMU_GI(PPG p), RPAR.A_PPT (PPG p),
		     golden_RO (PPG p), Trgip (PPG p))` by (
      IMP_RES_TAC smmu_golden_conf_lem
  ) >>
  `r IN mmu_req_rcvd (RM'.SMMU p) /\ 
   (mmu_abs (RM'.SMMU p)).state r IN {TRANS NONE; FAULT}` by (
      Q.UNABBREV_TAC `RM'` >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]  >>
      `(mmu_req_rcvd SMMU' = mmu_req_rcvd (RM.SMMU p) UNION {r}) /\
       (mmu_abs SMMU').state r IN {TRANS NONE; FAULT}` by (
          METIS_TAC [mmu_corereq_axiom]
      ) >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  FULL_SIMP_TAC (srw_ss()) [] 
  >| [(* case: need to continue with translation *)
      `?SMMU'' m. m > 0 /\ mmu_golden_comp(RM'.SMMU p, r, GIP (PPG p), SMMU'', m)
	      /\ (mmu_abs SMMU'').state r IN {FAULT; FINAL NONE}` by (
          METIS_TAC [mmu_golden_trans_axiom]
      ) >>
      `?m'.
            refined_comp (RM',2 * m,RM' with 
                <|m := m'; SMMU := (p =+ SMMU'') RM'.SMMU|>) 
         /\ SIM (RM' with <|m := m'; SMMU := (p =+ SMMU'') RM'.SMMU|>,IM') 
         /\ InvR (RM' with <|m := m'; SMMU := (p =+ SMMU'') RM'.SMMU|>) 
         /\ per_active(
                (RM' with <|m := m'; SMMU := (p =+ SMMU'') RM'.SMMU|>).P p).st
	 /\ r IN mmu_req_rcvd (
                (RM' with <|m := m'; SMMU := (p =+ SMMU'') RM'.SMMU|>).SMMU p)
	 /\ (mem_abs m' = mem_abs RM'.m)` by (
          METIS_TAC [golden_smmu_comp_lem]
      ) >>
      Q.ABBREV_TAC 
          `RM'' = RM' with <|m := m'; SMMU := (p =+ SMMU'') RM'.SMMU|>` >>
      `refined_comp(RM, 1 + 2 * m, RM'')` by (
          METIS_TAC [refined_comp_concat_lem]
      ) >>
      (* finish up, prove SimInvR *)
      EXISTS_TAC ``1 + 2 * m`` >>
      HINT_EXISTS_TAC >>
      RW_TAC (srw_ss()) [] >>
      `inv_good_mmu SMMU'` by (
          `SMMU' = RM'.SMMU p` by (
	      Q.UNABBREV_TAC `RM'` >>
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] 
      ) >>
      Q.UNABBREV_TAC `RM'` >>
      Q.UNABBREV_TAC `RM''` >>
      Q.ABBREV_TAC `RS = {FAULT; FINAL NONE}` >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM,
				combinTheory.UPDATE_EQ] >>
      (* mainly condition on SMMU states remains to be shown*)
      `!r'. r' <> r ==> 
	    ((mmu_abs SMMU'').state r' = (mmu_abs SMMU').state r')`
      by ( METIS_TAC [golden_comp_mmu_state_lem] ) >>
      `!r'. r' <> r ==> 
	    ((mmu_abs SMMU').state r' = (mmu_abs (RM.SMMU p)).state r')`
      by ( METIS_TAC [mmu_corereq_axiom] ) >>
      `!r'. r' <> r ==> 
	    ((mmu_abs SMMU'').state r' = (mmu_abs (RM.SMMU p)).state r')`
      by ( METIS_TAC [] ) >>
      MATCH_MP_TAC per_smmu_SimInvR_lem >>
      Q.UNABBREV_TAC `RS` >>
      HINT_EXISTS_TAC >>
      FULL_SIMP_TAC (srw_ss()) []
      ,
      (* case: FAULT - finish by proving SimInvR *)
      EXISTS_TAC ``1`` >>
      HINT_EXISTS_TAC >>
      RW_TAC (srw_ss()) [] >>
      Q.UNABBREV_TAC `RM'` >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      `!r'. r' <> r ==> 
	    ((mmu_abs SMMU').state r' = (mmu_abs (RM.SMMU p)).state r')`
      by ( METIS_TAC [mmu_corereq_axiom] ) >>
      MATCH_MP_TAC SimInvR_smmu_add_eq_mem_cc >>
      MATCH_MP_TAC per_smmu_SimInvR_lem >>
      HINT_EXISTS_TAC >>
      FULL_SIMP_TAC (srw_ss()) []
     ]
);

val id_pend_rpl_add_lem = store_thm("id_pend_rpl_add_lem", ``
!IM q_ c_ c r'. c < RPAR.nc /\ c_ < RPAR.nc /\ (PCG c = PCG c_) /\ c_ <> c 
==>
  (id_pend_rpl (((IM.G (PCG c_)).cif (PCC c_)).rpl_rcvd,
		mem_rpl_rcvd (IM.G (PCG c_)).m UNION 
		{(r',CoreSender (PCC c))},
			PCG c_,PCC c_,q_) = 
   id_pend_rpl (((IM.G (PCG c_)).cif (PCC c_)).rpl_rcvd,
		mem_rpl_rcvd (IM.G (PCG c_)).m,
		PCG c_,PCC c_,q_))
``,
  RW_TAC std_ss [id_pend_rpl_def, pred_setTheory.IN_UNION,
		 pred_setTheory.IN_SING] >>
  METIS_TAC [PCG_PCC_inj]
);

val pend_rpl_add_lem = store_thm("pend_rpl_add_lem", ``
!RM q_ r' c c_. c_ < RPAR.nc /\ (PCG c = PCG c_) /\ c_ <> c ==>
	  (pend_rpl(mmu_rpl_rcvd (RM.MMU c_),
		    mem_rpl_rcvd RM.m UNION 
		    {(Trrpl (PCG c) r',CoreSender c)},c_,q_) = 
	   pend_rpl(mmu_rpl_rcvd (RM.MMU c_),
		    mem_rpl_rcvd RM.m,c_,q_))
``,
  RW_TAC std_ss [pend_rpl_def, pred_setTheory.IN_UNION,
		 pred_setTheory.IN_SING]
);

val pend_rpl_add_other_guest_lem = store_thm("pend_rpl_add_other_guest_lem", ``
!RM q_ r' c c_. c_ < RPAR.nc /\ (PCG c <> PCG c_) /\ c_ <> c ==>
	  (pend_rpl(mmu_rpl_rcvd (RM.MMU c_),
		    mem_rpl_rcvd RM.m UNION 
		    {(Trrpl (PCG c) r',CoreSender c)},c_,q_) = 
	   pend_rpl(mmu_rpl_rcvd (RM.MMU c_),
		    mem_rpl_rcvd RM.m,c_,q_))
``,
  RW_TAC std_ss [pend_rpl_def, pred_setTheory.IN_UNION,
		 pred_setTheory.IN_SING]
);

(* EASY: same step in both models, affects memory replies **GUEST/SWITCH** *)
val ideal_PER_SND_IORPL_sim_step_lem = store_thm("ideal_PER_SND_IORPL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_SND_IORPL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_snd_iorpl_def] >>
  Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                         <|m := m'; P := (n =+ P') (IM.G g).P|>)
				  IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
      IMP_RES_TAC mem_rcv_rpl_axiom >>
      ASM_REWRITE_TAC []
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  `?k. (c = PCC k) /\ (PCG k = PPG p) /\ k < RPAR.nc` by (
      EXISTS_TAC ``PCGC_inv (g,c)``  >>
      METIS_TAC [PCGC_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  Q.ABBREV_TAC `GuestIndex = (PCG k = PPG p)` >>
  (* forwarded IO request *)
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, per_wrap_step_def, per_step_def] >>
  IMP_RES_TAC mem_rcv_rpl_axiom >>
  `r' = q` by ( METIS_TAC [unique_match_thm] ) >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC pproj_bound_lem >>
  `PAdr q IN PAR.A_gp (PPG p) (PPP p)` by (
      IMP_RES_TAC per_snd_iorpl_axiom >>
      IMP_RES_TAC ( InvI_EXPAND ``PPG p`` ) >>
      `?s. ((IM.G (PPG p)).P (PPP p)).IOreq_rcvd r'' = SOME s` by (
          METIS_TAC [inv_good_per_wrap_def, optionTheory.IS_SOME_EXISTS]
      ) >>
      IMP_RES_TAC id_inv_perreq_def >>
      METIS_TAC [unique_match_thm]
  ) >>
  (* mem step *)
  `PAdr q <> Agicd` by (
      REV_FULL_SIMP_TAC std_ss [coupling_axiom] >>
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [SYM Agicd_in_GICD_lem] >>
      `gicAR GICD` by ( REWRITE_TAC [gicAR_def] ) >>
      IMP_RES_TAC GICaddresses_lem >>
      `PAdr q IN RPAR.Amap GICD INTER RPAR.Amap (PER p)` suffices_by (
          FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INTER]
  ) >>
  `(Trreq (PPG p) q, CoreSender k) IN mem_req_sent RM.m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `IS_SOME (Trans (PPG p) (PAdr q))` by (
      METIS_TAC [trans_per_lem]
  ) >>
  IMP_RES_TAC match_IS_SOME_Trans_lem >>
  IMP_RES_TAC Trans_match_lem >>
  `?RM'. mem_step_rcv_rpl (RM.m,Trrpl (PPG p) r,CoreSender k,RM')` by (
      METIS_TAC [mem_rcv_rpl_enabled_axiom]
  ) >>
  (* peripheral step *)
  `per_step_snd_rpl ((RM.P p).st,Trrpl (PPG p) r, P'.st)` by (
      IMP_RES_TAC Trrpl_per_lem >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  `per_active (RM.P p).st` by ( METIS_TAC [per_snd_iorpl_axiom] ) >>
    (* refined model step *)
  Q.ABBREV_TAC `Pw' = <|st := P'.st; 
                        IOreq_rcvd := (ReqOf (Trrpl (PPG p) r) =+ NONE) 
					  (RM.P p).IOreq_rcvd|>` >>
  `refined_comp (RM,SUC 0,RM with
                 <|m := RM'; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [refined_comp_def] >>
      EXISTS_TAC ``PER_SND_IORPL p`` >>
      RW_TAC std_ss [refined_trans_def,ref_rule_per_snd_iorpl_def,
  		     per_wrap_step_def, per_step_def] >>
      EXISTS_TAC ``Trrpl (PPG p) r`` >>
      EXISTS_TAC ``RM':memory`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``k:num`` >>
      EXISTS_TAC ``Trreq (PPG p) q:request`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC std_ss [mem_step_def]
  ) >>
  (* same step executed, apply step and bisim axioms *)
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC mem_rcv_rpl_axiom >>
  `r'' = Trreq (PPG p) q` by ( METIS_TAC [unique_match_thm] ) >>
  `r''' = q` by ( METIS_TAC [unique_match_thm] ) >>
  Q.UNABBREV_TAC `GuestIndex` >>
  (* prove SimInvR *)
  `SimInvR (RM with
       <|m := RM'; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [SimInvR_def,combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC std_ss [SimInvR_def]
      ) 
  ) >>
  RW_TAC std_ss [] >>
  `(Trreq (PCG k) q,CoreSender k) IN mem_req_rcvd RM.m` by (
      METIS_TAC [mem_req_sent_lem]
  ) >>
  IMP_RES_TAC mem_req_rcvd_lem >>
  `(mmu_abs(RM.MMU k)).active` by (
      METIS_TAC [Trreq_per_lem, coupling_axiom, mmu_sent_per_req_lem]
  ) >>
  `Mode (RM.C k) < 2` by (
      MATCH_MP_TAC mmu_active_mode_lem >>
      METIS_TAC [mmu_sent_rcvd_lem]
  ) >>
  (* prove SIM *)
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|m := RM'; 
			       P := (p =+ <|st := P'.st; 
				            IOreq_rcvd := 
					    (ReqOf (Trrpl (PPG p) r) =+ NONE) 
						(RM.P p).IOreq_rcvd|>) 
					RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( Cases_on `c = k` ) >> 
      TRY ( INFS_LIMITED_METIS_TAC 1 [pend_rpl_add_lem, 
				      id_pend_rpl_add_lem, 
				      pend_rpl_add_other_guest_lem] ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, PSI_def, 
		       id_pend_rpl_add_lem, pend_rpl_add_lem,
		       pend_rpl_add_other_guest_lem, 
		       hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem, Trrpl_per_lem, 
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem, Mode_arith_lem, 
		       nuvi_guest_mode_lem, nuvi_other_core_reply_lem,
		       nuigc_guest_mode_lem, nuigc_other_core_reply_lem,
		       nusgi_guest_mode_lem, nusgi_other_core_reply_lem] ) )
  )
);

(* EASY: same step in both models, affects only peripheral and E_out **GUEST/SWITCH** *)
val ideal_PER_SND_PEV_sim_step_lem = store_thm("ideal_PER_SND_PEV_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_SND_PEV n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_snd_pev_def,
		     per_wrap_step_def, per_step_def] >>
  Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                                    <|P := (n =+ P') (IM.G g).P;
				      E_out := (IM.G g).E_out ++ l|>) IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  (* existence of per step *)
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_PERIPH `` >>
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_EXT `` >>
  EXISTS_TAC ``SUC 0`` >>
  RW_TAC std_ss [refined_comp_def] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] >>
  FIRST_EXISTS_TAC ``PER_SND_PEV p`` >>
  RW_TAC std_ss [refined_trans_def, ref_rule_per_snd_pev_def] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] >>
  Q.ABBREV_TAC `Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>` >>
  EXISTS_TAC ``Pw':periph_wrapper`` >>
  EXISTS_TAC ``l:pevent list`` >>
  `per_wrap_step (RM.P p,SEND (PEV l),Pw')` by (
      Q.UNABBREV_TAC `Pw'` >>
      FULL_SIMP_TAC (srw_ss()) [per_wrap_step_def, per_step_def, 
			    per_event_step_axiom] 
  ) >>
  `per_active (RM.P p).st` by ( METIS_TAC [per_event_step_axiom] ) >>
  `!e. MEM e l ==> (evper e = p)` by ( 
      METIS_TAC [PPG_PPP_inj, evper_ax] 
  ) >>
  (* SimInvR *)
  `SimInvR (RM with <|P := (p =+ Pw') RM.P; E_out := RM.E_out ++ l|>)` by (
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>
  ASM_REWRITE_TAC [] >>
  (* bisim *)
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS 
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|P := (p =+ <|st := P'.st; 
				            IOreq_rcvd := (RM.P p).IOreq_rcvd|>)
					RM.P; 
			       E_out := RM.E_out ++ l|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem, PEL_append_lem, PEL_other_lem] ) )
  )
);

(* MEDIUM: same step in both models, 
need GIC axioms to couple PI with GICD interrupt state **GUEST/SWITCH** *)
val ideal_PER_SND_IRQ_sim_step_lem = store_thm("ideal_PER_SND_IRQ_sim_step_lem", ``
!IM RM IM' IM'' n n0 g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_SND_IRQ n n0), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_snd_irq_def, 
		     per_wrap_step_def, per_step_def, idgic_step_def] >>
  Q.ABBREV_TAC `IM'' = <|G := (g =+ IM.G g with 
                         <|P := (n0 =+ P') (IM.G g).P; GIC := GIC'|>)
  				  IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
  `syncInv IM''` by ( 
       MATCH_MP_TAC syncInv_lem >>
       HINT_EXISTS_TAC >>
       Q.UNABBREV_TAC `IM''` >>
       RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >> 
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  `?p. p < RPAR.np /\ (g = PPG p) /\ (n0 = PPP p)` by (
      METIS_TAC [PCGC_PPGP_inv_def, PPGP_inv_rewrites]
  ) >>
  RW_TAC (srw_ss()) [] >>
  (* existence of steps *)
  `?rGIC'. gic_step_rcv_irq(RM.GIC,PIR n,rGIC')` by (
      METIS_TAC [gic_rcv_irq_enabled_axiom]
  ) >>
  `per_step_snd_irq((RM.P p).st,n,P'.st)` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  (* refined computation *)
  Q.ABBREV_TAC `Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>` >>
  `ref_rule_per_snd_irq (RM,p,RM with <|P := (p =+ Pw') RM.P; 
				        GIC := rGIC'|>)` by (
      RW_TAC std_ss [ref_rule_per_snd_irq_def] >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``n:num`` >>
      EXISTS_TAC ``rGIC':gic`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC std_ss [per_wrap_step_def, per_step_def, gic_step_def] >>
      METIS_TAC [coupling_axiom]
  ) >>
  `refined_trans(RM, PER_SND_IRQ p, RM with <|P := (p =+ Pw') RM.P; 
				              GIC := rGIC'|>)` by (
      RW_TAC (srw_ss()) [refined_trans_def] >>
      METIS_TAC [per_irq_step_axiom]
  ) >>
  `refined_comp(RM, SUC 0, RM with <|P := (p =+ Pw') RM.P; GIC := rGIC'|>)` by (
      METIS_TAC [refined_comp_def]
  ) >>
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  (* SimInvR *)
  `SimInvR (RM with <|P := (p =+ Pw') RM.P; GIC := rGIC'|>)` by (
      FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  (* prove SIM *)
  IMP_RES_TAC gic_rcv_irq_axiom >>
  IMP_RES_TAC (idgic_step_axiom // "rcv_irq") >>
  Q.UNABBREV_TAC `Pw'` >>  
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
      (* most cases *)
      TRY (REPEAT IF_CASES_TAC >>
           FULL_SIMP_TAC (srw_ss()) ([VI_def, HVabs_def, mode_def, Mode_def]@bisim_core_definitions) >>
           METIS_TAC [PPG_PPP_inj] >>
           NO_TAC) )
  (* special cases *)
  >| [(* bisim_gicd_reg *)
      Cases_on `r` >> (
          FULL_SIMP_TAC (srw_ss()) [req_gicd_VOL_lem] >>
          IMP_RES_TAC PIRQ_disjoint_lem2 >>
          IMP_RES_TAC (STEP_PREDICATE_FIRST_RULE gic_rcv_irq_bisim_axiom) >>
          IMP_RES_TAC gic_rcv_irq_gicdfltr_axiom >>
          FULL_SIMP_TAC (srw_ss()) [req_gicd_VOL_lem] >>
	  TRY ( IF_CASES_TAC ) >>
	  TRY ( METIS_TAC [GICDreg_distinct] )
      )
      ,
      (* bisim_pi_guest_def *)
      REPEAT IF_CASES_TAC >> 
      FULL_SIMP_TAC std_ss [bisim_pi_guest_def]
      >| [(* PPG n = g*)
          GEN_TAC >>
          Cases_on `PIR n = q` >> (
              IMP_RES_TAC PIR_PQQ_lem >>
              REV_FULL_SIMP_TAC std_ss [] >>
              TRY (LIMITED_METIS_TAC 1 []) >> 
              (* and PIR n = q *)
              IMP_RES_TAC good_proj_in_range_impls >>
              IMP_RES_TAC in_lPIRQ_lem >>
              Cases_on `Q RM.GIC (PIR n)` >> (
                  Cases_on `PI (IM.G g).GIC (PIR n)` >> (
                      FULL_SIMP_TAC std_ss [] >>
                      SPEC_ASSUM_TAC (``!q:irqID. X``, [``q:irqID``]) >>
                      REV_FULL_SIMP_TAC (srw_ss()) [] >>
		      FULL_SIMP_TAC std_ss [] >>
                      LIMITED_METIS_TAC 1 [good_proj_in_range_impls, 
					   PIstate_distinct]
		  )
	      )
	  ) 
	  ,
          (* PPG n <> g *)
          GEN_TAC >>
          Cases_on `PIR n = q` >> (
              IMP_RES_TAC PIR_PQQ_lem >>
              IMP_RES_TAC PIRQ_disjoint_lem2 >>
              RW_TAC (srw_ss()++HASPOC_SS) [] >>
              LIMITED_METIS_TAC 1 []
	  )
	 ]
     ]
);

(* **GUEST/SWITCH** *)
val ideal_PER_INTERNAL_sim_step_lem = store_thm("ideal_PER_INTERNAL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PER_INTERNAL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_internal_def]
  (* COUPLING *)
  THEN EXISTS_TAC ``SUC 0``
  THEN Q.ABBREV_TAC `Pw' = <|st := P'.st; 
                     IOreq_rcvd := (RM.P (PPGP_inv (g, n))).IOreq_rcvd|>`
  THEN Q.EXISTS_TAC `RM with P := (PPGP_inv (g, n) =+ Pw') RM.P`
  THEN REPEAT STRIP_TAC 
  THENL [(* EXIST of refined step*)
         SIMP_TAC std_ss [refined_comp_def] 
         THEN Q.EXISTS_TAC `PER_INTERNAL (PPGP_inv (g, n))` 
         THEN ASM_SIMP_TAC (srw_ss()) [refined_trans_def, ref_rule_per_internal_def, good_proj_in_range_impls] 
         THEN EXISTS_TAC ``Pw':periph_wrapper`` 
	 THEN Q.UNABBREV_TAC `Pw'`
         THEN FULL_SIMP_TAC (srw_ss()) [per_wrap_step_def]
         THEN MP_TAC (Q.SPECL [`RM`, `IM`] SIM_bisim_periph) 
         THEN ASM_SIMP_TAC std_ss [good_proj_in_range_impls, PPGP_inv_rewrites]
         ,
         (* leave bisim part for later *)
         ALL_TAC
         ,
         (* SimInvR *)
         FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
        ]
  (* IGC sync transparent *)
  THEN IMP_RES_TAC InvI_def
  THEN IMP_RES_TAC syncInv_lem
  THEN IMP_RES_TAC (STEP_PREDICATE_FIRST_RULE shared_mem_upd_lem)
  THEN RES_SPEC_WITH_STATES_FROM_PREMISES_TAC false
  THEN FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM]
  (* BISIM *)
  THEN FULL_SIMP_TAC (srw_ss()) [per_wrap_step_def] 
  THEN Q.UNABBREV_TAC `Pw'`
  THEN FULL_SIMP_TAC std_ss [SIM_EXPAND] 
  THEN RW_TAC (srw_ss()) (start_and_metis_lst@start_and_impres_lst)
  THEN FULL_SIMP_TAC (srw_ss()) [fall_constructors_thm_of ``:BISIM_CLAUSE``, bisim_rel_def]
  (* all cases except BISIM_PERIPH  *)
  THEN EXCEPT_FOR ``bisim_periph (RM',IM')``
       (      (* instantiate theorems by matching predicate in goal (and imp_res some others)  *)
              SPEC_BISIM_FROM_GOAL_TAC (solved_by_impres_only_lst) ASSUME_TAC 
         THEN MAP_EVERY IMP_RES_TAC start_and_impres_lst 
         THEN FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM, HVabs_def]  
             (* METIS for everything left *)
         THEN METIS_TAC (HVabs_def::start_and_metis_lst))
  (* BISIM_PERIPH case *)
  THEN FULL_SIMP_TAC std_ss [bisim_periph_def]
  THEN RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  THEN FULL_SIMP_TAC std_ss [PPGP_inv_rewrites]
  THEN RW_TAC std_ss []
  THEN FULL_SIMP_TAC std_ss [PPGP_inv_rewrites]
  THEN METIS_TAC [PPGP_inv_rewrites]
);

val ideal_gicc_rcv_req_lem  = store_thm("ideal_gicc_rcv_req_lem", ``
!RM IM r c m' GIC'.
   SIM(RM,IM)
/\ InvI IM
/\ InvR RM
/\ PAdr r IN RPAR.Amap GICC
/\ c < RPAR.nc
/\ mem_step ((IM.G (PCG c)).m,SEND (SREQ r (CoreSender (PCC c))),NONE,m')
/\ idgic_step((IM.G (PCG c)).GIC,RCV (SREQ r (CoreSender (PCC c))),0,GIC')
==>
?RM' rGIC'. 
   mem_step(RM.m, SEND(SREQ (Trreq (PCG c) r) (CoreSender c)), NONE, RM')
/\ gic_step(RM.GIC, RCV(SREQ (Trreq (PCG c) r) (CoreSender c)), rGIC') 
/\ IS_SOME (Trans (PCG c) (PAdr r))
``,
  RW_TAC (srw_ss()) [] >>
  `(r, CoreSender (PCC c)) IN mem_req_rcvd (IM.G (PCG c)).m` by (
      FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
      IMP_RES_TAC mem_snd_req_axiom 
  ) >>
  `PAdr r <> Agicd` by (
      IMP_RES_TAC gic_gicd_disj_lem >>
      ASSUME_TAC Agicd_lem >>
      PROVE_TAC [] 
  ) >>
  `(Trreq (PCG c) r, CoreSender c) IN mem_req_rcvd RM.m /\ 
   IS_SOME (Trans (PCG c) (PAdr r))` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  IMP_RES_TAC proj_bound_lem >>
  IMP_RES_TAC gicc_trans_lem >>
  `mem_step_snd_req ((IM.G (PCG c)).m,r,CoreSender (PCC c),m')` by (
      FULL_SIMP_TAC (srw_ss()) [mem_step_def]
  ) >>
  `(r,CoreSender (PCC c)) NOTIN mem_req_sent (IM.G (PCG c)).m` by (
      METIS_TAC [mem_snd_req_axiom]
  ) >>
  `(Trreq (PCG c) r, CoreSender c) NOTIN mem_req_sent RM.m` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `!q. (q,CoreSender c) IN mem_rpl_rcvd RM.m ==> 
       ~match (Trreq (PCG c) r,q)` by (
      REPEAT STRIP_TAC >>
      `?iq. match (r,iq) /\ (q = Trrpl (PCG c) iq)` by (
          METIS_TAC [Trrpl_exists_lem]
      ) >>
      RW_TAC std_ss [] >>
      `(iq, CoreSender (PCC c)) NOTIN mem_rpl_rcvd (IM.G (PCG c)).m` by (
          METIS_TAC [mem_snd_req_axiom]
      ) >>
      `Rpl_PAdr iq <> Agicd` by ( METIS_TAC [match_PAdr_eq_lem] ) >>
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `PAdr r IN A_gicper` by ( 
      RW_TAC std_ss [A_gicper_def, pred_setTheory.IN_GSPEC_IFF, gicAR_def] >>
      METIS_TAC []
  ) >>
  IMP_RES_TAC A_gicper_Trreq_lem >>
  `?RM'. mem_step(RM.m, SEND(SREQ (Trreq (PCG c) r) (CoreSender c)),
		  NONE, RM')` by (
      RW_TAC (srw_ss()) [mem_step_def] >>
      METIS_TAC [mem_snd_req_enabled_axiom] 
  ) >>
  `gicAR GICV` by ( RW_TAC (srw_ss()) [gicAR_def] ) >>
  `PAdr (Trreq (PCG c) r) IN RPAR.Amap GICV` by (
      METIS_TAC [Trreq_PAdr_Trans_lem]
  ) >>
  `?rGIC'. gic_step(RM.GIC, RCV (SREQ (Trreq (PCG c) r) (CoreSender c)), 
		    rGIC')` by (
      RW_TAC (srw_ss()) [gic_step_def] >>
      METIS_TAC [gic_rcv_io_enabled_axiom]
  ) >>
  METIS_TAC []
);

val refined_gicv_rcv_req_sim_lem  = store_thm("refined_gicv_rcv_req_sim_lem", ``
!RM IM r r' c m' GIC' im' iGIC'.
   SIM(RM,IM)
/\ InvI IM
/\ InvR RM
/\ PAdr r IN RPAR.Amap GICV
/\ c < RPAR.nc
/\ PAdr r' IN RPAR.Amap GICC
/\ (r = Trreq (PCG c) r')
/\ mem_step (RM.m, SEND (SREQ r (CoreSender c)), NONE, m')
/\ gic_step (RM.GIC, RCV (SREQ r (CoreSender c)), GIC')
/\ mem_step((IM.G (PCG c)).m, SEND(SREQ r' (CoreSender (PCC c))), NONE, im')
/\ idgic_step((IM.G (PCG c)).GIC, RCV(SREQ r' (CoreSender (PCC c))), 0, iGIC') 
/\ ideal_model_comp (IM,1,IM with <| G := ((PCG c) =+ IM.G (PCG c) with <|m := im'; GIC := iGIC'|>) IM.G |>)
==>
SIM  (RM with <|m := m'; GIC := GIC'|>,
      <|G := (PCG c =+ IM.G (PCG c) with <|m := im'; GIC := iGIC'|>) IM.G|>)
``,
  RW_TAC (srw_ss()) [] THEN 
  (* adding context information *)
  `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom THEN 
  IMP_RES_TAC gic_gicd_disj_lem THEN 
  IMP_RES_TAC not_in_GICD_not_Agicd_lem THEN 
  IMP_RES_TAC gicv_guest_mem_lem THEN 
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, gic_step_def, idgic_step_def] THEN 
  IMP_RES_TAC mem_snd_req_axiom THEN 
  `IS_SOME (Trans (PCG c) (PAdr r'))` by ( 
      IMP_RES_TAC xlated_mem_req_lem THEN 
      METIS_TAC [Trreq_eq_req_lem]
  ) THEN 
  IMP_RES_TAC gic_rcv_io_axiom THEN 
  IMP_RES_TAC (idgic_step_axiom // "rcv_req") THEN 
  `Mode (RM.C c) < 2` by ( IMP_RES_TAC gicv_req_mode_lem ) THEN 
  IMP_RES_TAC mmu_active_lem THEN 
  (* split into cases *)
  FULL_SIMP_TAC std_ss [SIM_EXPAND] THEN 
  REPEAT STRIP_TAC THEN 
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS THEN 
  (* try to solve straight-forward cases *)
  TRY (REPEAT IF_CASES_TAC THEN 
	FULL_SIMP_TAC (srw_ss()++ARITH_ss) ([HVabs_def, VI_def, Q_def, PI_def, bisim_pi_guest_def, pred_setTheory.UNION_DEF]@bisim_core_definitions) THEN
	TRY ( METIS_TAC [IN_DEF, PCG_PCC_inj, Mode_PCC_lem, Trreq_eq_req_lem, good_proj_in_range_impls] ))
);

(* MEDIUM: need to distinguish GICC **GUEST/SWITCH** and GICD requests
GICD requests either emulated or requested, no refined step in both cases *)
val ideal_GIC_RCV_IOREQ_sim_step_lem = store_thm("ideal_GIC_RCV_IOREQ_sim_step_lem", ``
!IM RM IM' IM'' r g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_GIC_RCV_IOREQ r), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_gic_rcv_ioreq_def]
  >| [(* case GICC *)
      `?k. (g = PCG k) /\ (c = PCC k) /\ k < RPAR.nc` by (
          EXISTS_TAC ``PCGC_inv (g,c)`` >>
          METIS_TAC [PCGC_inv_rewrites, good_proj_in_range_impls]
      ) >>
      FULL_SIMP_TAC bool_ss [] >>
      `?RM' rGIC'. 
	  mem_step(RM.m, SEND(SREQ (Trreq (PCG k) r) (CoreSender k)), NONE, RM')
       /\ gic_step(RM.GIC, RCV(SREQ (Trreq (PCG k) r) (CoreSender k)), rGIC') 
       /\ IS_SOME (Trans (PCG k) (PAdr r))` by (
          METIS_TAC [ideal_gicc_rcv_req_lem]
      ) >>
      IMP_RES_TAC gicc_trans_lem >>
      `PAdr (Trreq (PCG k) r) IN RPAR.Amap GICV` by (
          METIS_TAC [Trreq_PAdr_Trans_lem]
      ) >>
      `ref_rule_gic_rcv_ioreq(RM,RM with <|m := RM'; GIC := rGIC'|>)` by (
          RW_TAC std_ss [ref_rule_gic_rcv_ioreq_def] >>
	  `gicAR GICV` by ( RW_TAC std_ss [gicAR_def] ) >>
	  METIS_TAC []
      ) >>
      `refined_trans(RM,GIC_RCV_IOREQ,RM with <|m := RM'; GIC := rGIC'|>)` by (
          RW_TAC (srw_ss()) [refined_trans_def]
      ) >>
      `refined_comp(RM,SUC 0,RM with <|m := RM'; GIC := rGIC'|>)` by (
          METIS_TAC [refined_comp_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss []
      >| [(* SIM *)
	  `ideal_model_comp(IM,SUC 0,IM')` by (
	      RW_TAC std_ss [ideal_model_comp_def] >>
	      EXISTS_TAC ``C_INTERNAL`` >>
	      RW_TAC std_ss [ideal_model_trans_def, comp_rule_internal_def] >>
	      EXISTS_TAC ``PCG k`` >>
	      EXISTS_TAC ``IR_GIC_RCV_IOREQ r`` >>
	      EXISTS_TAC ``IM.G (PCG k) with <|m := m'; GIC := GIC'|>`` >>
	      RW_TAC (srw_ss()) [ideal_guest_trans_def, 
				 id_rule_gic_rcv_ioreq_def] >>
	      METIS_TAC []
	  ) >>
	  Q.ABBREV_TAC `IM'' = <|G := (PCG k =+ IM.G (PCG k) with 
                                 <|m := m'; GIC := GIC'|>) IM.G|>` >>
	  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
          `syncInv IM''` by ( 
	      MATCH_MP_TAC syncInv_lem >>
	      HINT_EXISTS_TAC >>
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	      FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
	      IMP_RES_TAC mem_snd_req_axiom >>
	      ASM_REWRITE_TAC []
	  ) >> 
	  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  Q.UNABBREV_TAC `IM''` >>
	  MATCH_MP_TAC refined_gicv_rcv_req_sim_lem >>
	  METIS_TAC [ideal_model_updates_eq_literal]
	  ,
	  (* SimInvR *)
	  FULL_SIMP_TAC (srw_ss()) [SimInvR_def] >>
	  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	  FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
          METIS_TAC [mem_snd_req_axiom]
	 ]
      ,
      (* case GICD *)
      cheat
     ]
);

(* HARD: need to distinguish GICC and GICD requests  **GUEST/SWITCH** 
GICC same step in both models but need to account for address translation
GICD requests either emulated, then couple with hypervisor Gcpy access
or requested, then execute complete refined GIC access, 7 steps *)
val ideal_GIC_SND_IORPL_sim_step_lem = store_thm("ideal_GIC_SND_IORPL_sim_step_lem", ``
!IM RM IM' IM'' g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_GIC_SND_IORPL), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_gic_snd_iorpl_def,
		     idgic_step_def, mem_step_def] >>
  `?k. (g = PCG k) /\ (c = PCC k) /\ k < RPAR.nc` by (
      EXISTS_TAC ``PCGC_inv (g,c)`` >>
      METIS_TAC [PCGC_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  `(PAdr q IN RPAR.Amap GICC \/ PAdr q IN RPAR.Amap GICD)` by (
      METIS_TAC [idgic_good_rpl_lem, unique_match_thm]
  )
  >| [(* case: no GICC -> translated to GICV access,
	       show existence of refined step *)
      `?gic' M'. gic_step_snd_rpl (RM.GIC,Trrpl (PCG k) r,CoreSender k,gic')
              /\ mem_step_rcv_rpl (RM.m, Trrpl (PCG k) r, 
				   CoreSender k, M')` by (
          METIS_TAC [ideal_gicv_rpl_step_lem]
      ) >> 
      `gic_step(RM.GIC, 
		SEND (SRPL (Trrpl (PCG k) r) (CoreSender k)), gic')` by (
          RW_TAC (srw_ss()) [gic_step_def]
      ) >>
      `mem_step(RM.m, RCV (SRPL (Trrpl (PCG k) r) (CoreSender k)), NONE, M')` by (
          RW_TAC (srw_ss()) [mem_step_def]
      ) >>
      `PAdr q <> Agicd` by ( 
          METIS_TAC [singleAR_disj_EXPAND, not_in_GICD_not_Agicd_lem]
      ) >>
      `(Trreq (PCG k) q, CoreSender k) IN mem_req_sent RM.m /\ 
       IS_SOME (Trans (PCG k) (PAdr q))` by (
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  METIS_TAC [bisim_memreq_def]
      ) >>
      IMP_RES_TAC match_IS_SOME_Trans_lem >>
      IMP_RES_TAC Trans_match_lem >>
      Q.ABBREV_TAC `RM' = RM with <|m := M'; GIC := gic'|>` >>
      `ref_rule_gic_snd_iorpl(RM, RM')` by (
          METIS_TAC [ref_rule_gic_snd_iorpl_def]
      ) >>
      `refined_trans(RM, GIC_SND_IORPL, RM')` by (
	  RW_TAC (srw_ss()) [refined_trans_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      EXISTS_TAC ``RM':refined_model`` >>
      `refined_comp(RM,SUC 0, RM')` by (
          METIS_TAC [refined_comp_def] 
      ) >>
      ASM_REWRITE_TAC [] >>
      (* prove SimInvR *)
      IMP_RES_TAC mem_rcv_rpl_axiom >>
      `(r' = Trreq (PCG k) q) /\ (r'' = q)` by ( 
          METIS_TAC [unique_match_thm] 
      ) >>
      RW_TAC std_ss [] THEN_LT
      LASTGOAL (
          Q.UNABBREV_TAC `RM'` >>
	  FULL_SIMP_TAC (srw_ss()) [SimInvR_def]
      ) >>
      (* add some context - GIC bisim *)
      `Rpl_PAdr r IN RPAR.Amap GICC` by ( METIS_TAC [match_PAdr_eq_lem] ) >>
      `(q,CoreSender (PCC k)) IN idgic_req_rcvd (IM.G (PCG k)).GIC /\ 
       (idgic_req_rcvd GIC' = idgic_req_rcvd (IM.G (PCG k)).GIC DIFF
                              {(q,CoreSender (PCC k))}) /\ 
       (* (!R. (idgic_abs GIC').gicd (CONST R) =  *)
       (* 	    (idgic_abs (IM.G (PCG k)).GIC).gicd (CONST R)) /\  *)
       (* (!R. (idgic_abs GIC').gicd (MUTE R) =  *)
       (* 	    (idgic_abs (IM.G (PCG k)).GIC).gicd (MUTE R)) /\  *)
       (!c'. c' <> (PCC k) ==>
         ((idgic_abs GIC').gicc c' = (idgic_abs (IM.G (PCG k)).GIC).gicc c'))` 
      by ( 
          METIS_TAC [idgic_step_axiom // "snd_rpl_gicc", unique_match_thm] 
      ) >>
      `PAdr (Trreq (PCG k) q) IN RPAR.Amap GICV` by (
          RW_TAC std_ss [Trreq_PAdr_Trans_lem] >>
	  IMP_RES_TAC gicc_trans_lem 
      ) >>
      `Rpl_PAdr (Trrpl (PCG k) r) IN RPAR.Amap GICV` by (
          METIS_TAC [match_PAdr_eq_lem]
      ) >>
      `(Trreq (PCG k) q,CoreSender k) IN gic_req_rcvd RM.GIC /\ 
       (gic_req_rcvd gic' = gic_req_rcvd RM.GIC DIFF
                            {(Trreq (PCG k) q,CoreSender k)}) /\ 
       ((gic_abs gic').gicc = (gic_abs RM.GIC).gicc) /\
       (* (!R. (gic_abs gic').gicd (CONST R) = (gic_abs RM.GIC).gicd (CONST R)) /\ *)
       (* (!R. (gic_abs gic').gicd (MUTE R) = (gic_abs RM.GIC).gicd (MUTE R)) /\ *)
       (!c'. c' <> k ==>
         ((gic_abs gic').gicv c' = (gic_abs RM.GIC).gicv c'))` 
      by ( 
          METIS_TAC [gic_gicv_rpl_axiom, unique_match_thm] 
      ) >>
      (* extract IM' *)
      Q.ABBREV_TAC `IM'' = <|G :=
              (PCG k =+ IM.G (PCG k) with <|m := m'; GIC := GIC'|>) IM.G|>` >>
      `syncInv IM''` by (
          MATCH_MP_TAC syncInv_lem >>
	  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >>
	  HINT_EXISTS_TAC >> 
	  ASM_REWRITE_TAC [] >>
	  REPEAT STRIP_TAC >>
	  Cases_on `g=PCG k` >> (
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  )	  
      ) >>
      FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
      RW_TAC (srw_ss()) [] >>
      (* proof hints *)
      `Mode (RM.C k) < 2` by ( 
          METIS_TAC [gicv_req_mode_lem]
      ) >>
      `bisim_perirq(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_perirq_lem]
      ) >>
      `bisim_sgiirq(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_sgiirq_lem]
      ) >>
      `bisim_igcirq(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_igcirq_lem]
      ) >>
      `bisim_send_igc(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_send_igc_lem]
      ) >>
      `bisim_pi(RM',IM')` by ( 
          METIS_TAC [gicv_rpl_bisim_pi_lem]
      ) >>
      `!R c. c < RPAR.nc /\ (PCG c = PCG k) ==> 
	     ((idgic_abs GIC').gicc (PCC c) R = (gic_abs gic').gicv c R)` by (
          METIS_TAC [gicv_rpl_reg_bisim_lem]
      ) >>
      `bisim_gicd_reg(RM',IM')` by ( 
          METIS_TAC [gicv_rpl_bisim_gicd_reg_lem]
      ) >>
      (* prove SIM *)
      Q.UNABBREV_TAC `RM'` >>
      Q.UNABBREV_TAC `IM'` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >>
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([pend_rpl_def, bisim_pi_guest_def,
			  id_pend_rpl_def]@bisim_core_definitions) >>
      	  `!c. (RM with <|m := M'; GIC := gic'|>).C c = RM.C c`
	  by ( FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] ) >> 
      	  TRY ( TIME_LIMITED_METIS_TAC 1.0 [PCG_PCC_inj, proj_bound_lem,
      			   hv_gicd_entry_state_lem, hv_gicd_entry_state_eq_lem, 
			   hv_guard_mmu_fault_lem, hv_guard_mmu_fault_eq_lem,
			   hv_mmu_fault_entry_eq_lem, 
			   hv_guard_gicd_fail_lem,
			   (* HVabs_gic_send_lem, *)
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   Mode_arith_lem, Mode_ineq_lem] ) )
      ,
      (* case: GICD access -> virtualized by hypervisor *)
      cheat
     ]
);

(* HARD: step complete IRQ reception handler *)
val ideal_GIC_DIST_sim_step_lem = store_thm("ideal_GIC_DIST_sim_step_lem", ``
!IM RM IM' IM'' i n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_GIC_DIST i n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* EASY: same step in both models, nothing changes  **GUEST/SWITCH** *)
val ideal_MEM_INTERNAL_sim_step_lem = store_thm("ideal_MEM_INTERNAL_sim_step_lem", ``
!IM RM IM' IM'' g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_MEM_INTERNAL), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_mem_internal_def,
			    mem_step_def, valid_sender__def, valid_sender_def]
  >| [(* CoreSender *)
      `?c'. c' < RPAR.nc /\ (g = PCG c') /\ (c = PCC c')` by (
          METIS_TAC [PCGC_PPGP_inv_def, PCGC_inv_rewrites]
      ) >>
      RW_TAC (srw_ss()) [] >>
      IMP_RES_TAC mem_internal_axiom >>
      `PAdr r <> Agicd` by (
          METIS_TAC [not_in_A_gicper_lem, not_in_GICD_not_Agicd_lem]
      ) >>
      `   (Trreq (PCG c') r, CoreSender c') IN mem_req_rcvd(RM.m) 
       /\ IS_SOME(Trans (PCG c') (PAdr r))` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  METIS_TAC [bisim_memreq_def]
      ) >>
      `PAdr(Trreq (PCG c') r) NOTIN A_gicper` by (
          IMP_RES_TAC A_gicper_Trans_adr_lem >>
	  METIS_TAC [Trreq_PAdr_Trans_lem]
      ) >>
      `?m''. mem_step_internal (RM.m,CoreSender c',m'')` by (
          METIS_TAC [mem_internal_enabled_axiom]
      ) >>
      `valid_sender_ NONE (CoreSender c')` by (
          METIS_TAC [valid_sender__def, valid_ref_sender_def]
      ) >>
      `mem_step(RM.m,TAU,NONE,m'')` by (
          FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
	  METIS_TAC []
      ) >>
      `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
      `syncInv (<|G := (PCG c' =+ IM.G (PCG c') with m := m') IM.G|>)` by (
          MATCH_MP_TAC syncInv_lem >>
	  HINT_EXISTS_TAC >>
	  STRONG_FS_TAC []
      ) >>
      `IM' = <|G := (PCG c' =+ IM.G (PCG c') with m := m') IM.G|>` by ( 
          METIS_TAC [shared_mem_upd_lem]
      ) >>
      RW_TAC (srw_ss()) []	  
      ,
      (* PeripheralSender *)
      `?p'. p' < RPAR.np /\ (g = PPG p') /\ (p = PPP p')` by (
          METIS_TAC [PCGC_PPGP_inv_def, PPGP_inv_rewrites]
      ) >>
      RW_TAC (srw_ss()) [] >>
      IMP_RES_TAC mem_internal_axiom >>
      `   (Trreq (PPG p') r, PeripheralSender p') IN mem_req_rcvd(RM.m) 
       /\ IS_SOME(Trans (PPG p') (PAdr r))` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  METIS_TAC [bisim_memreq_def]
      ) >>
      `PAdr(Trreq (PPG p') r) NOTIN A_gicper` by (
          IMP_RES_TAC A_gicper_Trans_adr_lem >>
	  METIS_TAC [Trreq_PAdr_Trans_lem]
      ) >>
      `?m''. mem_step_internal (RM.m,PeripheralSender p',m'')` by (
          METIS_TAC [mem_internal_enabled_axiom]
      ) >>
      `valid_sender_ NONE (PeripheralSender p')` by (
          METIS_TAC [valid_sender__def, valid_ref_sender_def]
      ) >>
      `mem_step(RM.m,TAU,NONE,m'')` by (
          FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
	  METIS_TAC []
      ) >>
      `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
      `syncInv (<|G := (PPG p' =+ IM.G (PPG p') with m := m') IM.G|>)` by (
          MATCH_MP_TAC syncInv_lem >>
	  HINT_EXISTS_TAC >>
	  STRONG_FS_TAC []
      ) >>
      `IM' = <|G := (PPG p' =+ IM.G (PPG p') with m := m') IM.G|>` by ( 
          METIS_TAC [shared_mem_upd_lem]
      ) >>
      RW_TAC (srw_ss()) []	  
     ] >> (
      (* prove refined_comp *)
      `ref_rule_mem_internal(RM,RM with m := m'')` by (
          METIS_TAC [ref_rule_mem_internal_def]
      ) >>
      `refined_trans(RM,MEM_INTERNAL,RM with m := m'')` by (
          FULL_SIMP_TAC (srw_ss()) [refined_trans_def]
      ) >>
      `refined_comp(RM,SUC 0,RM with m := m'')` by (
          FULL_SIMP_TAC arith_ss [refined_comp_def] >>
	  METIS_TAC []
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      EXISTS_TAC ``(RM with m := m'') : refined_model`` >>
      `   (mem_abs m'' = mem_abs RM.m)
       /\ (mem_req_rcvd m'' = mem_req_rcvd RM.m)
       /\ (mem_req_sent m'' = mem_req_sent RM.m)
       /\ (mem_rpl_rcvd m'' = mem_rpl_rcvd RM.m)` by (
          METIS_TAC [mem_internal_axiom]
      ) >>
      RW_TAC (srw_ss()) []
      >| [(* prove SIM *)
	  FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
	  REPEAT STRIP_TAC >>
	  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	  (* try to solve straight-forward cases *)
	  >> (REPEAT IF_CASES_TAC >>
	      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	      `!c. RM.C c = (RM with m := m'').C c` by (
                  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	      ) >>
	      TRY ( METIS_TAC [PPG_PPP_inj, PPG_PPP_inj, 
			       hv_gicd_entry_state_eq_lem, 
			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem, 
			       hv_mmu_fault_entry_eq_lem, 
			       proj_bound_lem, pproj_bound_lem] ) )
	  ,
	  (* prove SimInvR *)
	  STRONG_FS_TAC [SimInvR_def]
	 ]
  )  
);

val cif_mmu_step_lem = store_thm("cif_mmu_step_lem", ``
!RM IM c r cif' mem'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ SimInvR RM
/\ InvI IM
/\ InvR RM
/\ PAdr r IN PAR.A_G (PCG c)
/\ bif_step_snd_req ((IM.G (PCG c)).cif (PCC c),r,cif')
/\ mem_step_rcv_req ((IM.G (PCG c)).m,r,CoreSender (PCC c),mem')
/\ PAdr r NOTIN RPAR.Amap GICD
/\ (PAdr r IN receiverMem (PCG c) ==> ~Wreq r)
==>
?MMU' m'. mmu_step_snd_req (RM.MMU c, Trreq (PCG c) r, MMU')
       /\ mem_step_rcv_req (RM.m, Trreq (PCG c) r, CoreSender c, m')
``,
  REPEAT STRIP_TAC >>
  (* add some context *)
  IMP_RES_TAC proj_bound_lem >>
  IMP_RES_TAC not_in_GICD_not_Agicd_lem >>
  `IS_SOME (Trans (PCG c) (PAdr r))` by (
      METIS_TAC [guest_adr_trans_lem]
  ) >>
  `r IN ((IM.G (PCG c)).cif (PCC c)).req_rcvd /\ 
   r NOTIN ((IM.G (PCG c)).cif (PCC c)).req_sent /\ 
   !q. q IN ((IM.G (PCG c)).cif (PCC c)).rpl_rcvd ==> ~match(r,q)` by (
      FULL_SIMP_TAC std_ss [bif_step_snd_req_def]
  ) >>
  `r IN idcore_req_sent ((IM.G (PCG c)).C (PCC c))` by (
      IMP_RES_TAC (InvI_EXPAND ``PCG c``) >>
      FULL_SIMP_TAC (srw_ss()) [id_inv_cifreq_def]
  ) >>
  `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active` by (
      `idcore_req_sent ((IM.G (PCG c)).C (PCC c)) <> EMPTY` by (
          METIS_TAC [pred_setTheory.NOT_IN_EMPTY]
      ) >>
      `inv_good_idcore ((IM.G (PCG c)).C (PCC c))` by (
          IMP_RES_TAC (InvI_EXPAND ``PCG c``)
      ) >>
      METIS_TAC [inv_good_idcore_def]
  ) >>
  IMP_RES_TAC SimInvR_req_mode_lem >>
  IMP_RES_TAC mmu_active_lem >>
  (* request pending on MMU and no reply received yet *)
  `r IN mmu_req_rcvd (RM.MMU c) /\ 
   Trreq (PCG c) r NOTIN mmu_req_sent (RM.MMU c) /\ 
   !q. q IN mmu_rpl_rcvd (RM.MMU c) ==> ~match(Trreq (PCG c) r,q)` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      IMP_RES_TAC bisim_mmureq_guest_def >>
      REPEAT STRIP_TAC 
      >| [(* case: request received *)
	  IMP_RES_TAC bisim_mmureq_guest_core_def >> (
	      METIS_TAC []
	  )
	  ,
          (* case: request not sent *)
	  IMP_RES_TAC bisim_mmureq_guest_core_def >>
          METIS_TAC []
	  ,
	  (* case: reply not received *)
	  BasicProvers.byA(
	      `?q'. q = Trrpl (PCG c) q'`,
              METIS_TAC [match_Trreq_exist_Trrpl_lem]
	  ) >>
	  RW_TAC (srw_ss()) [] >>
	  IMP_RES_TAC match_Trreq_IS_SOME_rpl_lem >>
	  `match(r,q')` by ( IMP_RES_TAC Trans_match_lem ) >>
	  IMP_RES_TAC bisim_mmureq_guest_core_def >>
	  METIS_TAC []
	 ]
  ) >>
  (* request not IDLE or FAULT in MMU *)
  `(mmu_abs (RM.MMU c)).state r <> IDLE` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [inv_good_mmu_def]
  ) >>
  IMP_RES_TAC mmu_fault_state_lem >>
  (* request has state FINAL NONE *)
  `!l. (mmu_abs (RM.MMU c)).state r NOTIN 
   {TRANS (SOME l); FINAL (SOME l)}` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      RES_TAC >>
      `l IN mmu_req_sent (RM.MMU c) \/
       ?q. q IN mmu_rpl_rcvd (RM.MMU c) /\ match (l,q)` by (
      METIS_TAC [inv_good_mmu_def]
  )
  >| [(* case: l was sent *)
      FULL_SIMP_TAC (srw_ss()) []
      >| [(* case: TRANS (SOME l) -> contradiction by SimInvR *)
	  IMP_RES_TAC SimInvR_def >>
	      IMP_RES_TAC SimInvR_no_TRANS_lem 
	  ,
	  (* case: FINAL (SOME l) -> must be Trreq g r *)
	  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_def >>
	  `l = Trreq (PCG c) r` by (
	      IMP_RES_TAC Trreq_xlated_ATrans_lem 
	  ) >>
	  METIS_TAC []
	 ]
      ,
      (* case: q was received *)
      FULL_SIMP_TAC (srw_ss()) []
      >| [(* case: TRANS (SOME l) -> contradiction by SimInvR *)
	  IMP_RES_TAC SimInvR_def >>
	  IMP_RES_TAC SimInvR_no_TRANS_lem 
	  ,
	  (* case: FINAL (SOME l) -> must be Trrpl g q *)
	  IMP_RES_TAC ref_inv_hyp_iso_mmu_final_rpl_def >>
	  `l = Trreq (PCG c) r` by (
	      IMP_RES_TAC Trreq_xlated_ATrans_lem 
	  ) >>
	  METIS_TAC []
	 ]
     ]
  ) >>
  `(mmu_abs (RM.MMU c)).state r = FINAL NONE` by (
      Cases_on `(mmu_abs (RM.MMU c)).state r` >> (
          FULL_SIMP_TAC (srw_ss()) []
      ) 
      >| [(* case: TRANS (SOME l) -> contradiction by SimInvR *)
	  IMP_RES_TAC SimInvR_def >>
	  IMP_RES_TAC SimInvR_no_TRANS_lem 
	  ,
	  (* case: NONE <> SOME l *)
	  METIS_TAC [optionTheory.NOT_IS_SOME_EQ_NONE, 
		     optionTheory.IS_SOME_EXISTS]
	 ]
  ) >>
  IMP_RES_TAC mmu_final_req_axiom >>
  IMP_RES_TAC golden_mmu_Trreq_lem >>
  METIS_TAC [mem_rcv_req_enabled_axiom]
);



(* MEDIUM: need special case for GICD request -> no step 
need address translation and MMU coupling of requests  **GUEST/SWITCH** *)
val ideal_CIF_SND_SREQ_sim_step_lem = store_thm("ideal_CIF_SND_SREQ_sim_step_lem", ``
!IM RM IM' IM'' r n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CIF_SND_SREQ r n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
?n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_cif_snd_req_def,
		     bif_step_def, mem_step_def] >>
  `?c. (g = PCG c) /\ (n = PCC c) /\ c < RPAR.nc` by (
      EXISTS_TAC ``PCGC_inv (g,n)`` >>
      METIS_TAC [PCGC_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  Cases_on `PAdr r IN RPAR.Amap GICD`
  >| [(* case: GICD access -> empty refined step *)
      cheat
      ,
      (* case: no GICD -> show existence of refined steps *)
      `?MMU' m'. mmu_step_snd_req (RM.MMU c, Trreq (PCG c) r, MMU')
              /\ mem_step_rcv_req (RM.m, Trreq (PCG c) r, 
				   CoreSender c, m')` by (
          METIS_TAC [cif_mmu_step_lem]
      ) >> 
      `mmu_step(RM.MMU c, 
		SEND (SREQ (Trreq (PCG c) r) (CoreSender c)), MMU')` by (
          RW_TAC (srw_ss()) [mmu_step_def]
      ) >>
      `mem_step(RM.m, RCV (SREQ (Trreq (PCG c) r) (CoreSender c)), NONE, m')` by (
          RW_TAC (srw_ss()) [mem_step_def]
      ) >>
      Q.ABBREV_TAC `RM' = RM with <|MMU := (c =+ MMU') RM.MMU; 
				      m := m'|>` >>
      `ref_rule_mmu_snd_mreq(RM, c, RM')` by (
          METIS_TAC [ref_rule_mmu_snd_mreq_def]
      ) >>
      `refined_trans(RM, MMU_SND_MREQ c, RM')` by (
	  RW_TAC (srw_ss()) [refined_trans_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      EXISTS_TAC ``RM':refined_model`` >>
      `refined_comp(RM,SUC 0, RM')` by (
          METIS_TAC [refined_comp_def] 
      ) >>
      ASM_REWRITE_TAC [] >>
      (* add some context *)
      `IS_SOME (Trans (PCG c) (PAdr r))` by (
          `PAdr r <> Agicd` by ( IMP_RES_TAC not_in_GICD_not_Agicd_lem ) >>
          METIS_TAC [guest_adr_trans_lem]
      ) >>
      FULL_SIMP_TAC std_ss [bif_step_snd_req_def] >>
      `r IN idcore_req_sent ((IM.G (PCG c)).C (PCC c))` by (
          IMP_RES_TAC (InvI_EXPAND ``PCG c``) >>
	  FULL_SIMP_TAC (srw_ss()) [id_inv_cifreq_def]
      ) >>
      `(idcore_abs ((IM.G (PCG c)).C (PCC c))).active` by (
          `idcore_req_sent ((IM.G (PCG c)).C (PCC c)) <> EMPTY` by (
	      METIS_TAC [pred_setTheory.NOT_IN_EMPTY]
	  ) >>
	  `inv_good_idcore ((IM.G (PCG c)).C (PCC c))` by (
              IMP_RES_TAC (InvI_EXPAND ``PCG c``)
	  ) >>
	  METIS_TAC [inv_good_idcore_def]
      ) >>
      IMP_RES_TAC not_in_GICD_not_Agicd_lem >>
      IMP_RES_TAC SimInvR_req_mode_lem >>
      IMP_RES_TAC mmu_active_lem >>
      IMP_RES_TAC mmu_guest_send_lem >>          
      IMP_RES_TAC mem_rcv_req_axiom >>
      (* prove SimInvR *)
      `SimInvR RM'` by (
          `SimInvR (RM with
           <|C := (c =+ RM.C c) RM.C; m := m'; MMU := (c =+ MMU') RM.MMU|>)` by (
	      MATCH_MP_TAC core_mmu_SimInvR_lem >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      METIS_TAC []
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_ID] >>
	  `RM' = RM with <|C := RM.C; m := m'; MMU := (c =+ MMU') RM.MMU|>` by (
	      Q.UNABBREV_TAC `RM'` >>
	      FULL_SIMP_TAC (srw_ss()) [refined_model_component_equality]
	  ) >>
	  ASM_REWRITE_TAC []
      ) >>
      ASM_REWRITE_TAC [] >>
      (* extract IM' *)
      Q.ABBREV_TAC `IM'' = <|G := (PCG c =+ IM.G (PCG c) with
           <|cif := (PCC c =+ cif') (IM.G (PCG c)).cif; m := mem'|>) IM.G|>` >>
      `syncInv IM''` by (
          MATCH_MP_TAC syncInv_lem >>
	  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >>
	  HINT_EXISTS_TAC >> 
	  ASM_REWRITE_TAC [] >>
	  REPEAT STRIP_TAC >>
	  Cases_on `g=PCG c` >> (
	      Q.UNABBREV_TAC `IM''` >>
	      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  )	  
      ) >>
      FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
      RW_TAC (srw_ss()) [] >>
      (* prove SIM *)
      Q.UNABBREV_TAC `RM'` >>
      Q.UNABBREV_TAC `IM'` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >>
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `Mode ((RM with <|m := m'; MMU := (c =+ MMU') RM.MMU|>).C c) < 2`
	  by ( FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] ) >>
      	  TRY ( METIS_TAC [PCG_PCC_inj, proj_bound_lem,
      			   hv_gicd_entry_state_lem, hv_gicd_entry_state_eq_lem, 
			   hv_guard_mmu_fault_lem, hv_guard_mmu_fault_eq_lem,
			   hv_mmu_fault_entry_eq_lem,
			   hv_guard_gicd_fail_lem,
			   HVabs_mmu_send_lem, 
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   Mode_arith_lem, Mode_ineq_lem] ) )
     ]
);

(* MEDIUM: need special case for GICD request -> no step
need address translation, memory and MMU coupling  **GUEST/SWITCH**
need to distinguish IO and actual memory replies *)
val ideal_CIF_RCV_SRPL_sim_step_lem = store_thm("ideal_CIF_RCV_SRPL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CIF_RCV_SRPL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
?n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_cif_rcv_rpl_def, 
		     bif_step_def, mem_step_def] >>
  `?c. c < RPAR.nc /\ (g = PCG c) /\ (n = PCC c)` by (
      METIS_TAC [PCGC_PPGP_inv_def]
  ) >>
  Cases_on `Mode (RM.C c) < 2`
  >| [(* regular access, one-to-one simulation *)
      IMP_RES_TAC mmu_active_lem >>
      `Trreq (PCG c) q IN mmu_req_sent (RM.MMU c) /\ 
       IS_SOME(Trans (PCG c) (PAdr q))` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_mmureq_guest_def >>
	  METIS_TAC [bisim_mmureq_guest_core_def]
      ) >>
      `?r'. ((mmu_abs (RM.MMU c)).state r' = FINAL (SOME (Trreq (PCG c) q))) /\
            xlated (r',Trreq (PCG c) q)` by (
          FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
	  RES_TAC >>
	  METIS_TAC [inv_good_mmu_def, SimInvR_no_TRANS_lem, 
		     pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
      ) >>
      `PAdr r' IN PAR.A_G (PCG c) /\ 
       (PAdr (Trreq (PCG c) q) = ATrans (PCG c) (PAdr r')) /\
       ATrans (PCG c) (PAdr r') <> FAULT_ADDRESS /\
       (PAdr r' IN {SND (PAR.igca s) | s < PAR.ns /\ 
				       (SND (PAR.cpol s) = PCG c)} ==>
            ~Wreq r')` by (
          FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
          METIS_TAC [ref_inv_hyp_iso_mmu_final_def]
      ) >>
      IMP_RES_TAC proj_bound_lem >>
      RW_TAC std_ss [] >>
      `r' = q` by (
          MATCH_MP_TAC Trreq_eq_req_lem >>
	  HINT_EXISTS_TAC >>
	  IMP_RES_TAC ATrans_lem >>
	  RW_TAC std_ss [Trreq_xlated_ATrans_lem]
      ) >>
      RW_TAC std_ss [] >>
      `q IN ((IM.G (PCG c)).cif (PCC c)).req_rcvd` by (
          METIS_TAC [bif_step_rcv_rpl_def, unique_match_thm]
      ) >>
      IMP_RES_TAC bisim_cif_req_rcvd_lem >>
      IMP_RES_TAC ATrans_match_lem >>
      `?MMU'. mmu_step_rcv_rpl (RM.MMU c,Trrpl (PCG c) r,MMU')` by (
          METIS_TAC [mmu_rcv_rpl_enabled_axiom]
      ) >>
      `(q, CoreSender (PCC c)) IN mem_req_rcvd ((IM.G (PCG c)).m)` by (
          IMP_RES_TAC ( InvI_EXPAND ``PCG c`` ) >>
          IMP_RES_TAC id_inv_cifreq_def
      ) >>
      `PAdr q <> Agicd` by (
          METIS_TAC [trans_guest_adr_lem]
      ) >>
      `(Trreq (PCG c) q, CoreSender c) IN mem_req_rcvd RM.m` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_memreq_def
      )	>>
      `?m'. mem_step_snd_rpl (RM.m,Trrpl (PCG c) r,CoreSender c,m')` by (
          METIS_TAC [ref_mem_core_rpl_lem]
      ) >>
      `IS_SOME (Trans (PCG c) (Rpl_PAdr r))` by (
          METIS_TAC [match_PAdr_eq_lem]
      ) >>
      Cases_on `PAdr q IN A_gicper`
      >| [(* forwarded IO reply *)
	  METIS_TAC [id_final_mmu_rpl_fwd_lem]
	  ,
	  (* generated reply *)
	  METIS_TAC [id_final_mmu_rpl_no_fwd_lem]
	 ]
      ,
      (* GICD access -> emulated by hypervisor *)
      cheat
     ]
);


val pif_mmu_step_lem = store_thm("pif_mmu_step_lem", ``
!RM IM p r pif' mem'.
   p < RPAR.np
/\ SIM (RM,IM)
/\ SimInvR RM
/\ InvI IM
/\ InvR RM
/\ PAdr r IN PAR.A_G (PPG p)
/\ bif_step_snd_req ((IM.G (PPG p)).pif (PPP p),r,pif')
/\ mem_step_rcv_req ((IM.G (PPG p)).m,r,PeripheralSender (PPP p),mem')
/\ PAdr r NOTIN RPAR.Amap GICC
/\ PAdr r NOTIN RPAR.Amap GICD
/\ (!p_. p_ < PAR.np_g (PPG p) ==> PAdr r NOTIN PAR.A_gp (PPG p) p_)
/\ (PAdr r IN receiverMem (PPG p) ==> ~Wreq r)
==>
?SMMU' m'. mmu_step_snd_req (RM.SMMU p, Trreq (PPG p) r, SMMU')
        /\ mem_step_rcv_req (RM.m, Trreq (PPG p) r, PeripheralSender p, m')
``,
  REPEAT STRIP_TAC >>
  (* add some context *)
  IMP_RES_TAC pproj_bound_lem >>
  IMP_RES_TAC not_in_GICD_not_Agicd_lem >>
  `IS_SOME (Trans (PPG p) (PAdr r))` by (
      METIS_TAC [guest_adr_trans_lem]
  ) >>
  `r IN ((IM.G (PPG p)).pif (PPP p)).req_rcvd /\ 
   r NOTIN ((IM.G (PPG p)).pif (PPP p)).req_sent /\ 
   !q. q IN ((IM.G (PPG p)).pif (PPP p)).rpl_rcvd ==> ~match(r,q)` by (
      FULL_SIMP_TAC std_ss [bif_step_snd_req_def]
  ) >>
  `r IN per_req_sent ((IM.G (PPG p)).P (PPP p)).st` by (
      IMP_RES_TAC (InvI_EXPAND ``PPG p``) >>
      FULL_SIMP_TAC (srw_ss()) [id_inv_pifreq_def]
  ) >>
  `r IN per_req_sent (RM.P p).st` by (
      IMP_RES_TAC SIM_bisim_periph >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  `per_active (RM.P p).st` by ( IMP_RES_TAC per_active_req_lem ) >>
  `(mmu_abs (RM.SMMU p)).active` by ( IMP_RES_TAC smmu_per_active_lem ) >>
  (* request pending on SMMU and no reply received yet *)
  `r IN mmu_req_rcvd (RM.SMMU p) /\ 
   Trreq (PPG p) r NOTIN mmu_req_sent (RM.SMMU p) /\ 
   !q. q IN mmu_rpl_rcvd (RM.SMMU p) ==> ~match(Trreq (PPG p) r,q)` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC 
      >| [(* case: request received *)
	  METIS_TAC [bisim_smmureq_def]
	  ,
          (* case: request not sent *)
	  METIS_TAC [bisim_smmureq_def]
	  ,
	  (* case: reply not received *)
	  `?q'. q = Trrpl (PPG p) q'` by (
              METIS_TAC [match_Trreq_exist_Trrpl_lem]
	  ) >>
	  RW_TAC (srw_ss()) [] >>
	  IMP_RES_TAC match_Trreq_IS_SOME_rpl_lem >>
	  `match(r,q')` by ( IMP_RES_TAC Trans_match_lem ) >>
	  METIS_TAC [bisim_smmureq_def]
	 ]
  ) >>
  (* request not IDLE or FAULT in SMMU *)
  `(mmu_abs (RM.SMMU p)).state r <> IDLE` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [inv_good_mmu_def]
  ) >>
  IMP_RES_TAC smmu_fault_state_lem >>
  (* request has state FINAL NONE *)
  `!l. (mmu_abs (RM.SMMU p)).state r NOTIN 
   {TRANS (SOME l); FINAL (SOME l)}` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      RES_TAC >>
      `l IN mmu_req_sent (RM.SMMU p) \/
       ?q. q IN mmu_rpl_rcvd (RM.SMMU p) /\ match (l,q)` by (
          METIS_TAC [inv_good_mmu_def]
      )
      >| [(* case: l was sent *)
	  FULL_SIMP_TAC (srw_ss()) []
	  >| [(* case: TRANS (SOME l) -> contradiction by SimInvR *)
	      IMP_RES_TAC SimInvR_def >>
	      IMP_RES_TAC SimInvR_smmu_no_TRANS_lem 
	      ,
	      (* case: FINAL (SOME l) -> must be Trreq g r *)
	      IMP_RES_TAC ref_inv_hyp_iso_smmu_final_def >>
	      `l = Trreq (PPG p) r` by (
	          IMP_RES_TAC Trreq_xlated_ATrans_lem 
	      ) >>
	      METIS_TAC []
	     ]
	  ,
	  (* case: q was received *)
	  FULL_SIMP_TAC (srw_ss()) []
	  >| [(* case: TRANS (SOME l) -> contradiction by SimInvR *)
	      IMP_RES_TAC SimInvR_def >>
	      IMP_RES_TAC SimInvR_smmu_no_TRANS_lem 
	      ,
	      (* case: FINAL (SOME l) -> must be Trrpl g q *)
	      IMP_RES_TAC ref_inv_hyp_iso_smmu_final_rpl_def >>
	      `l = Trreq (PPG p) r` by (
	          IMP_RES_TAC Trreq_xlated_ATrans_lem 
	      ) >>
	      METIS_TAC []
	     ]
	 ]
  ) >>
  `(mmu_abs (RM.SMMU p)).state r = FINAL NONE` by (
      Cases_on `(mmu_abs (RM.SMMU p)).state r` >> (
          FULL_SIMP_TAC (srw_ss()) []
      ) 
      >| [(* case: TRANS (SOME l) -> contradiction by SimInvR *)
	  IMP_RES_TAC SimInvR_def >>
	  IMP_RES_TAC SimInvR_smmu_no_TRANS_lem 
	  ,
	  (* case: NONE <> SOME l *)
	  METIS_TAC [optionTheory.NOT_IS_SOME_EQ_NONE, 
		     optionTheory.IS_SOME_EXISTS]
	 ]
  ) >>
  IMP_RES_TAC mmu_final_req_axiom >>
  IMP_RES_TAC golden_smmu_Trreq_lem >>
  METIS_TAC [mem_rcv_req_enabled_axiom]
);


(* EASY: same step in both models,  **GUEST/SWITCH**
need address translation and SMMU coupling *)
val ideal_PIF_SND_DMAREQ_sim_step_lem = store_thm("ideal_PIF_SND_DMAREQ_sim_step_lem", ``
!IM RM IM' IM'' r n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PIF_SND_DMAREQ r n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
?n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_pif_snd_dmareq_def,
		     bif_step_def, mem_step_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC guest_mem_A_gicper_lem >>
  (* show existence of refined steps *)
  `?SMMU' m'. mmu_step_snd_req (RM.SMMU p, Trreq (PPG p) r, SMMU')
	  /\ mem_step_rcv_req (RM.m, Trreq (PPG p) r, 
				   PeripheralSender p, m')` by (
      METIS_TAC [pif_mmu_step_lem]
  ) >> 
  `mmu_step(RM.SMMU p, 
	    SEND (SREQ (Trreq (PPG p) r) (PeripheralSender p)), SMMU')` by (
      RW_TAC (srw_ss()) [mmu_step_def]
  ) >>
  `mem_step(RM.m, 
	    RCV (SREQ (Trreq (PPG p) r) (PeripheralSender p)), NONE, m')` by (
      RW_TAC (srw_ss()) [mem_step_def]
  ) >>
  Q.ABBREV_TAC `RM' = RM with <|SMMU := (p =+ SMMU') RM.SMMU; m := m'|>` >>
  `ref_rule_smmu_snd_dmareq(RM, p, RM')` by (
      METIS_TAC [ref_rule_smmu_snd_dmareq_def]
  ) >>
  `refined_trans(RM, SMMU_SND_DMAREQ p, RM')` by (
      RW_TAC (srw_ss()) [refined_trans_def]
  ) >>
  EXISTS_TAC ``SUC 0`` >>
  EXISTS_TAC ``RM':refined_model`` >>
  `refined_comp(RM,SUC 0, RM')` by (
      METIS_TAC [refined_comp_def] 
  ) >>
  ASM_REWRITE_TAC [] >>
  (* add some context *)
  `IS_SOME (Trans (PPG p) (PAdr r))` by (
      `PAdr r <> Agicd` by ( IMP_RES_TAC not_in_GICD_not_Agicd_lem ) >>
      METIS_TAC [guest_adr_trans_lem]
  ) >>
  FULL_SIMP_TAC std_ss [bif_step_snd_req_def] >>
  `r IN per_req_sent ((IM.G (PPG p)).P (PPP p)).st` by (
      IMP_RES_TAC (InvI_EXPAND ``PPG p``) >>
      FULL_SIMP_TAC (srw_ss()) [id_inv_pifreq_def]
  ) >>
  `r IN per_req_sent (RM.P p).st` by (
      IMP_RES_TAC SIM_bisim_periph >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  `per_active (RM.P p).st` by ( IMP_RES_TAC per_active_req_lem ) >>
  IMP_RES_TAC not_in_GICD_not_Agicd_lem >>
  `(mmu_abs (RM.SMMU p)).active` by ( IMP_RES_TAC smmu_per_active_lem ) >>
  IMP_RES_TAC smmu_guest_send_lem >>	     
  IMP_RES_TAC mem_rcv_req_axiom >>
  (* prove SimInvR *)
  `SimInvR RM'` by (
      `SimInvR (RM with
       <|m := m'; SMMU := (p =+ SMMU') RM.SMMU; P := (p =+ RM.P p) RM.P|>)` by (
	      MATCH_MP_TAC per_smmu_SimInvR_lem >>
	      FULL_SIMP_TAC (srw_ss()) [] >>
	      METIS_TAC []
      ) >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_ID] >>
      `RM' = RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU; 
		       P := RM.P|>` by (
          Q.UNABBREV_TAC `RM'` >>
	  FULL_SIMP_TAC (srw_ss()) [refined_model_component_equality]
      ) >>
      ASM_REWRITE_TAC []
  ) >>
  ASM_REWRITE_TAC [] >>
  (* extract IM' *)
  Q.ABBREV_TAC `IM'' = <|G := (PPG p =+ IM.G (PPG p) with
       <| m := MEM'; pif := (PPP p =+ pif') (IM.G (PPG p)).pif|>) IM.G|>` >>
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >>
      HINT_EXISTS_TAC >> 
      ASM_REWRITE_TAC [] >>
      REPEAT STRIP_TAC >>
      Cases_on `g=PPG p` >> (
          Q.UNABBREV_TAC `IM''` >>
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      )	  
  ) >>
  FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def] >>
  RW_TAC (srw_ss()) [] >>
  (* prove SIM *)
  Q.UNABBREV_TAC `RM'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >>
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `RM.C c = (RM with <|m := m'; SMMU := (p =+ SMMU') RM.SMMU|>).C c` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	  ) >>
      	  TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      			       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			       hv_mmu_fault_entry_eq_lem,
      			       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			       pproj_bound_lem] ) )
);

(* EASY: same step in both models,  **GUEST/SWITCH**
need address translation, memory and SMMU coupling *)
val ideal_PIF_RCV_DMARPL_sim_step_lem = store_thm("ideal_PIF_RCV_DMARPL_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PIF_RCV_DMARPL n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_pif_rcv_dmarpl_def, 
		     bif_step_def, mem_step_def] >>
  `?p. p < RPAR.np /\ (g = PPG p) /\ (n = PPP p)` by (
      METIS_TAC [PCGC_PPGP_inv_def]
  ) >>
  `Trreq (PPG p) q IN mmu_req_sent (RM.SMMU p) /\ 
   IS_SOME(Trans (PPG p) (PAdr q))` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  METIS_TAC [bisim_smmureq_def]
  ) >>
  `q IN ((IM.G g).pif n).req_rcvd` by (
      METIS_TAC [bif_step_rcv_rpl_def, unique_match_thm]
  ) >>
  `q IN mmu_req_rcvd (RM.SMMU p)` by (
      METIS_TAC [bisim_pif_req_rcvd_lem]
  ) >>
  `per_active (RM.P p).st` by ( IMP_RES_TAC per_active_req_lem ) >>
  `(mmu_abs (RM.SMMU p)).active` by ( IMP_RES_TAC smmu_per_active_lem ) >>
  `?r'. ((mmu_abs (RM.SMMU p)).state r' = FINAL (SOME (Trreq (PPG p) q))) /\
	xlated (r',Trreq (PPG p) q)` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND]  >>
      RES_TAC >>
      METIS_TAC [inv_good_mmu_def, SimInvR_smmu_no_TRANS_lem]
  ) >>
  `PAdr r' IN PAR.A_G (PPG p) /\ 
   (PAdr (Trreq (PPG p) q) = ATrans (PPG p) (PAdr r')) /\
   xlated (r',Trreq (PPG p) q) /\ ATrans (PPG p) (PAdr r') <> FAULT_ADDRESS /\
   PAdr r' NOTIN RPAR.Amap GICC /\ PAdr r' NOTIN RPAR.Amap GICD /\
   (!p'. p' < PAR.np_g (PPG p) ==> PAdr r' NOTIN PAR.A_gp (PPG p) p') /\
   (PAdr r' IN {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = PPG p)} ==>
        ~Wreq r')` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [ref_inv_hyp_iso_smmu_final_def]
  ) >>
  IMP_RES_TAC pproj_bound_lem >>
  RW_TAC std_ss [] >>
  `r' = q` by (
      MATCH_MP_TAC Trreq_eq_req_lem >>
	  HINT_EXISTS_TAC >>
	  IMP_RES_TAC ATrans_lem >>
	  RW_TAC std_ss [Trreq_xlated_ATrans_lem]
  ) >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC ATrans_match_lem >>
  `?SMMU'. mmu_step_rcv_rpl (RM.SMMU p,Trrpl (PPG p) r,SMMU')` by (
      METIS_TAC [mmu_rcv_rpl_enabled_axiom]
  ) >>
  `(q, PeripheralSender (PPP p)) IN mem_req_rcvd ((IM.G (PPG p)).m)` by (
      IMP_RES_TAC ( InvI_EXPAND ``PPG p`` ) >>
      IMP_RES_TAC id_inv_pifreq_def
  ) >>
  `PAdr q <> Agicd` by (
      METIS_TAC [trans_guest_adr_lem]
  ) >>
  `(Trreq (PPG p) q, PeripheralSender p) IN mem_req_rcvd RM.m` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_memreq_def
  ) >>
  IMP_RES_TAC guest_mem_A_gicper_lem >>
  `?m'. mem_step_snd_rpl (RM.m,Trrpl (PPG p) r,PeripheralSender p,m')` by (
      METIS_TAC [ref_mem_per_rpl_lem]
  ) >>
  `IS_SOME (Trans (PPG p) (Rpl_PAdr r))` by (
      METIS_TAC [match_PAdr_eq_lem]
  ) >>
  METIS_TAC [id_final_smmu_rpl_lem]
);


(* MEDIUM: special case for GICD faults -> fault injection, 
need coupling of CIF and MMU, need exception semantics  *)
val ideal_CIF_FAULT_sim_step_lem = store_thm("ideal_CIF_FAULT_sim_step_lem", ``
!IM RM IM' IM'' r n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_CIF_FAULT r n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* EASY: same step in both models  **GUEST/SWITCH**
need coupling of PIF and SMMU *)
val ideal_PIF_FAULT_sim_step_lem = store_thm("ideal_PIF_FAULT_sim_step_lem", ``
!IM RM IM' IM'' r n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_PIF_FAULT r n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  REPEAT STRIP_TAC >>	
  `n < PAR.np_g g /\ id_smmu_fault_rpl n g r /\
   id_rule_pif_snd_fault(IM.G g, r, n, g, G')` by (
      FULL_SIMP_TAC (srw_ss()) [ideal_guest_trans_def, id_smmu_fault_rpl_def] >>
      METIS_TAC []
  ) >>
  FULL_SIMP_TAC (srw_ss()) [id_rule_pif_snd_fault_def, 
			    per_wrap_step_def, per_step_def] >>
  `?p. (g = PPG p) /\ (n = PPP p) /\ p < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,n)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  Q.ABBREV_TAC `IM'' = <|G := (PPG p =+ IM.G (PPG p) with
                         <|P := (PPP p =+ P') (IM.G (PPG p)).P;
			   pif := (PPP p =+ pif') (IM.G (PPG p)).pif|>) 
				   IM.G|>` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv IM''` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `IM''` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
  ) >>
  FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
  (* generated fault reply *)
  `?q. q IN ((IM.G (PPG p)).pif (PPP p)).req_rcvd /\ match (q,r) /\
       (fiOf r = golden_fi (GIP (PPG p),
			    SMMU_GI (PPG p),
			    RPAR.A_PPT (PPG p),
			    golden_RO (PPG p)) q)
    /\ r NOTIN ((IM.G (PPG p)).pif (PPP p)).rpl_rcvd
    /\ Frpl r
    ` by (
      METIS_TAC [bif_step_snd_fault_def]
  ) >>
  `q' = q` by ( METIS_TAC [unique_match_thm] ) >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC bif_step_snd_fault_lem >>
  `q IN per_req_sent (RM.P p).st` by (
      IMP_RES_TAC SIM_bisim_periph >>
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  `per_active (RM.P p).st` by ( IMP_RES_TAC per_active_req_lem ) >>
  `(mmu_abs (RM.SMMU p)).active` by ( IMP_RES_TAC smmu_per_active_lem ) >>
  (* first build peripheral step *)
  `per_step_rcv_rpl ((RM.P p).st,r,P'.st)` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  (* mmu step *)
  `q IN mmu_req_rcvd (RM.SMMU p)` by (
      METIS_TAC [bisim_pif_req_rcvd_lem]
  ) >>
  IMP_RES_TAC id_smmu_fault_match_lem >>
  IMP_RES_TAC smmu_fault_lem >>
  IMP_RES_TAC mmu_fault_rpl_axiom >>
  `q'' = r` by (
      IMP_RES_TAC Frpl_match_lem >>
      IMP_RES_TAC smmu_golden_conf_lem >>
      IMP_RES_TAC mmu_golden_fault_FAR_axiom >>
      FULL_SIMP_TAC std_ss [fiOf_def]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  (* refined model step *)
  Q.ABBREV_TAC `Pw' = <|st := P'.st; IOreq_rcvd := (RM.P p).IOreq_rcvd|>` >>
  `refined_comp (RM,SUC 0,RM with
                 <|SMMU := (p =+ MMU') RM.SMMU; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [refined_comp_def] >>
      EXISTS_TAC ``PER_RCV_DMARPL p`` >>
      RW_TAC std_ss [refined_trans_def,ref_rule_per_rcv_dmarpl_def,
  		     per_wrap_step_def, per_step_def] >>
      EXISTS_TAC ``q'':reply`` >>
      EXISTS_TAC ``MMU':mmu`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``q:request`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC std_ss [mmu_step_def]
  ) >>
  (* same step executed, apply step and bisim axioms *)
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  (* add some contect about result *)
  `(mmu_rpl_rcvd MMU' = mmu_rpl_rcvd (RM.SMMU p)) /\
   (mmu_req_rcvd MMU' = mmu_req_rcvd (RM.SMMU p) DIFF {q}) /\
   ((mmu_abs MMU').state q = IDLE) /\
   (!r'. r' <> q ==>
         ((mmu_abs MMU').state r' = (mmu_abs (RM.SMMU p)).state r')) /\
   (mmu_req_sent MMU' = mmu_req_sent (RM.SMMU p)) /\
   (mmu_ptl_hist MMU' = mmu_ptl_hist (RM.SMMU p)) /\
   (mmu_abs MMU').active /\
   ((mmu_abs MMU').cfg = (mmu_abs (RM.SMMU p)).cfg)` by (
      IMP_RES_TAC match_ReqOf_lem >>
      IMP_RES_TAC mmu_reply_lem >- (
	  REV_FULL_SIMP_TAC std_ss [MMUstate_distinct]
      ) >>
      RW_TAC std_ss []
  ) >>
  (* prove SimInvR *)
  `SimInvR (RM with
       <|SMMU := (p =+ MMU') RM.SMMU; P := (p =+ Pw') RM.P|>)` by (
      RW_TAC std_ss [SimInvR_def,combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC std_ss [SimInvR_def]
      ) >>
      Cases_on `p = p'` >> (
          RW_TAC std_ss []
      ) >>
      Cases_on `r = q` >>(
          RW_TAC std_ss []
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INSERT]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  (* prove SIM *)
  IMP_RES_TAC good_match_lem >>
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `IM''` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `RM.C c = (RM with <|SMMU := (p =+ MMU') RM.SMMU;
  			   P := (p =+ <|st := P'.st; 
				        IOreq_rcvd := (RM.P p).IOreq_rcvd|>) 
				    RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
  		       pproj_bound_lem] ) )
  )
);

(* EASY: launch step in hypervisor initialization *)
val ideal_STARTUP_sim_step_lem = store_thm("ideal_STARTUP_sim_step_lem", ``
!IM RM IM' IM'' n g G'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ g < PAR.ng
/\ ideal_guest_trans(IM.G g, g, INTERNAL (IR_RULE_STARTUP n), G')
/\ (IM'' = IM with G := (g =+ G') IM.G)
/\ sync_shared_mem_upd_of_guest (IM'', g, IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  cheat
);

(* **GUEST/SWITCH** *)
val ideal_C_INTERNAL_sim_step_thm = store_thm("ideal_C_INTERNAL_sim_step_thm", ``
!IM RM IM'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ ideal_model_trans(IM,C_INTERNAL,IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  RW_TAC (srw_ss()) [ideal_model_trans_def]
  THEN IMP_RES_TAC comp_rule_internal_def
  THEN Cases_on `x`
  THENL [METIS_TAC [ideal_CORE_RCV_IRQ_sim_step_lem], 
	 METIS_TAC [ideal_CORE_RCV_MRPL_sim_step_lem], 
	 METIS_TAC [ideal_CORE_RCV_EVENT_sim_step_lem], 
	 METIS_TAC [ideal_CORE_SND_MREQ_sim_step_lem], 
	 METIS_TAC [ideal_CORE_INTERNAL_sim_step_lem], 
	 METIS_TAC [ideal_CORE_SND_ELIST_sim_step_lem],
	 METIS_TAC [ideal_CORE_FAIL_PSCI_sim_step_lem], 
	 METIS_TAC [ideal_CORE_FAIL_SIGC_sim_step_lem], 
	 METIS_TAC [ideal_PER_RCV_DMARPL_sim_step_lem], 
	 METIS_TAC [ideal_PER_RCV_IOREQ_sim_step_lem], 
	 METIS_TAC [ideal_PER_RCV_PEV_sim_step_lem], 
	 METIS_TAC [ideal_PER_SND_DMAREQ_sim_step_lem], 
	 METIS_TAC [ideal_PER_SND_IORPL_sim_step_lem], 
	 METIS_TAC [ideal_PER_SND_PEV_sim_step_lem], 
	 METIS_TAC [ideal_PER_SND_IRQ_sim_step_lem], 
	 METIS_TAC [ideal_PER_INTERNAL_sim_step_lem], 
	 METIS_TAC [ideal_GIC_RCV_IOREQ_sim_step_lem], 
	 METIS_TAC [ideal_GIC_SND_IORPL_sim_step_lem], 
	 METIS_TAC [ideal_GIC_DIST_sim_step_lem], 
	 METIS_TAC [ideal_MEM_INTERNAL_sim_step_lem], 
	 METIS_TAC [ideal_CIF_SND_SREQ_sim_step_lem], 
	 METIS_TAC [ideal_CIF_RCV_SRPL_sim_step_lem], 
	 METIS_TAC [ideal_PIF_SND_DMAREQ_sim_step_lem], 
	 METIS_TAC [ideal_PIF_RCV_DMARPL_sim_step_lem], 
	 METIS_TAC [ideal_CIF_FAULT_sim_step_lem], 
	 METIS_TAC [ideal_PIF_FAULT_sim_step_lem], 
	 METIS_TAC [ideal_STARTUP_sim_step_lem]]
);


val ideal_refined_sim_step_thm = store_thm("ideal_refined_sim_step_thm", ``
!IM RM R IM'.
   SIM (RM, IM) /\ SimInvR RM /\ InvI IM /\ InvR RM 
/\ ideal_model_trans(IM,R,IM')
==>
∃n RM'. refined_comp (RM,n,RM') /\ SIM (RM',IM') /\ SimInvR RM'
``,
  Cases_on `R`
  THENL [REWRITE_TAC [ideal_C_INTERNAL_sim_step_thm],
	 REWRITE_TAC [ideal_C_IGC_sim_step_lem],
	 REWRITE_TAC [ideal_C_RCU_sim_step_lem]]
);



(* THEOREM: top level bisimulation

direction IM-> RM
*)


val ideal_refined_bisim_thm = store_thm("ideal_refined_bisim_thm", ``
!IM n IM' RM. 
   SIM (RM, IM)
/\ ref_start RM
/\ good_ideal_comp (IM, n, IM')
==>
?n' RM'. good_refined_comp(RM, n', RM') /\ SIM (RM', IM') /\ SimInvR RM' 
``,
  Induct_on `n`
  THEN1 ( RW_TAC (srw_ss()) [good_ideal_comp_def, ideal_model_comp_def]
	  THEN EXISTS_TAC ``0``
	  THEN HINT_EXISTS_TAC
          THEN `0 < RPAR.nc` by RW_TAC (srw_ss()) [refined_goodP_axiom |> SIMP_RULE bool_ss [refined_goodP_def]]
	  THEN RW_TAC (srw_ss()) [good_refined_comp_def , refined_comp_def]
	  THEN FULL_SIMP_TAC (srw_ss()) [ref_core_start_def, refstart_SimInvR_lem]
  )
  THEN RW_TAC (srw_ss()) [good_refined_comp_def, refined_comp_def, good_ideal_comp_def, ideal_model_comp_def]
  THEN IMP_RES_TAC good_ideal_comp_def
  THEN IMP_RES_TAC InvI_lem
  THEN RES_TAC
  THEN IMP_RES_TAC InvR_lem
  THEN IMP_RES_TAC good_refined_comp_def
  THEN IMP_RES_TAC ideal_refined_sim_step_thm
  THEN IMP_RES_TAC refined_comp_concat_lem
  THEN METIS_TAC []
);



(* direction RM-> IM *)


val bisim_ctx_core_phys_irq_lem = store_thm("bisim_ctx_core_phys_irq", ``
!RM IM c C'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ refcore_step_rcv_phys (RM.C c,C')
==>
bisim_ctx_core (idcore_abs ((IM.G (PCG c)).C (PCC c)), 
		refcore_abs C', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC C',c),
	        ectx C',
                refcore_int C',
                idcore_int ((IM.G (PCG c)).C (PCC c))) /\
(Mode C' = 2) /\
(refcore_abs (RM.C c)).active /\ (refcore_abs C').active /\
(refcore_req_sent C' = EMPTY) /\ 
(ref_abs_int (RM.C c) = FLUSHED) /\
(ref_abs_int C' = FLUSHED) /\ 
((refcore_abs C').H = (refcore_abs (RM.C c)).H) /\ 
((refcore_abs C').PC = AHV VBAR + 0x480w) /\
((refcore_abs C').GPR = (refcore_abs (RM.C c)).GPR) /\
~hv_mmu_fault_entry_point (refcore_abs C')
``,
  NTAC 5 STRIP_TAC >>
  IMP_RES_TAC soft_Mode_lem >>
  `mode (refcore_abs (RM.C c)) < 2` by ( 
      FULL_SIMP_TAC std_ss [Mode_mode_lem] 
  ) >>
  IMP_RES_TAC InvR_haspoc_exc_conf_lem >>
  IMP_RES_TAC refcore_phys_irq_axiom >>
  FULL_SIMP_TAC std_ss [Mode_mode_lem] >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  REV_FULL_SIMP_TAC std_ss [bisim_ctx_core_def, Mode_mode_lem] >>
  `(mode (refcore_abs (RM.C c)) <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) <> 2)` by ( DECIDE_TAC ) >>
  `mode (refcore_abs C') = 2` by ( 
      FULL_SIMP_TAC std_ss [mode_def, MODE_upd_lem]
  ) >>
  IMP_RES_TAC soft_mode_lem >>
  `(mode (refcore_abs C') <> 3)` by ( DECIDE_TAC ) >>
  `~(mode (refcore_abs C') < 2)` by ( DECIDE_TAC ) >>
  FULL_SIMP_TAC std_ss [ectx_def] >>
  `(refcore_abs C').SPR (INR VBAR_EL2) = 
   (refcore_abs (RM.C c)).SPR (INR VBAR_EL2)` by (
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR VBAR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
  ) >>
  IMP_RES_TAC InvR_VBAR_lem >>
  `~sc C'` by (
      RW_TAC std_ss [sc_def] >>
      Q.UNABBREV_TAC `a` >>
      RW_TAC std_ss [] >>
      DISJ1_TAC >>
      RW_TAC std_ss [] >>
      blastLib.BBLAST_PROVE_TAC 
  ) >>
  RW_TAC std_ss []
  >| [(* new PC not in HV init *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT, 
			    pred_setTheory.NOT_IN_EMPTY, 
			    AHV_corollaries]
      ,
      (* guest SPRs unchanged *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INL r:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      Cases_on `r = ISR_EL1`
      >| [(* ISR_EL1 *)
	  DISJ2_TAC >>
	  FULL_SIMP_TAC std_ss []
	  ,
	  DISJ1_TAC >>
	  FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* PC saved *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC std_ss [] >>
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR ELR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
      ,
      (* PSTATE saved *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC std_ss [] >>
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR SPSR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* GPR unchanged *)
      RW_TAC std_ss [] 
      ,
      (* source/target register saved in ESR -> contradiction *)
      REV_FULL_SIMP_TAC std_ss [ref_abs_int_def, pred_setTheory.IN_INSERT,
				AbsCIstate_distinct, 
				pred_setTheory.NOT_IN_EMPTY]
      ,
      (* PC saved in context -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* PSTATE saved in context -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* GPR saved in context -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* source / target register after JISR -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* not mmu fault entry point *)
      RW_TAC std_ss [hv_mmu_fault_entry_point_def] >> 
      DISJ1_TAC >>
      blastLib.BBLAST_PROVE_TAC
     ]      
);

val refined_gic_snd_virq_sim_lem = store_thm("refined_gic_snd_virq_sim_lem", ``
!RM IM c rGIC'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ Mode (RM.C c) < 2
/\ gic_step_snd_irq (RM.GIC,c,T,rGIC')
==>
?iGIC'. idgic_step_snd_irq ((IM.G (PCG c)).GIC,PCC c,iGIC')
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC gic_snd_irq_axiom >> (
      REV_FULL_SIMP_TAC std_ss []
  ) >>
  MATCH_MP_TAC ( idgic_step_axiom // "snd_irq_enabled" ) >>
  FULL_SIMP_TAC std_ss [vmsk_ipmsk_axiom] >>
  `(idgic_abs (IM.G (PCG c)).GIC).gicc (PCC c) = (gic_abs RM.GIC).gicv c` by (
      METIS_TAC [bisim_gicc_reg_def, SIM_EXPAND]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  EXISTS_TAC ``PRQ (PCG c) q`` >>
  STRIP_TAC >- (
      (* ready_irqs *)
      FULL_SIMP_TAC std_ss [ready_irqs_def, pred_setTheory.IN_GSPEC_IFF] >>
      IMP_RES_TAC virq_guest_mode_lem >>
      ASM_REWRITE_TAC [] >>
      Cases_on `q`
      >| [(* SGI *)
	  `?id s r. p=(id,s,r)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
	  RW_TAC std_ss [PRQ_def] >>
	  METIS_TAC [ipmsk_SGI_axiom]
	  ,
	  (* PIR *)
	  RW_TAC std_ss [PRQ_def]
	 ]
  ) >>
  STRIP_TAC >- (
      (* max_prio *)
      IMP_RES_TAC ready_irq_prio_sim_lem >>
      `max_prio(ready_irqs
		    ((idgic_abs (IM.G (PCG c)).GIC).Q (PCC c),
		     ipmsk ((gic_abs RM.GIC).gicv c))) =        
       max_prio(ready_irqs (VI RM.GIC c,ipmsk ((gic_abs RM.GIC).gicv c)))` by (
          RW_TAC std_ss [max_prio_def]
      ) >>
      ASM_REWRITE_TAC [] >>
      `w2n (prio (PRQ (PCG c) q)) = w2n (prio q)` suffices_by (
          ASM_REWRITE_TAC []
      ) >>
      Cases_on `q`
      >| [(* SGI *)
	  `?id s r. p=(id,s,r)` by ( 
	      METIS_TAC [pairTheory.pair_CASES] 
	  ) >>
	  THROW_AWAY_TAC ``w2n (prio (SGI p)) = z`` >>
	  FULL_SIMP_TAC std_ss [] >>
	  `r = c` by (
	      FULL_SIMP_TAC std_ss [ready_irqs_def, 
				    pred_setTheory.IN_GSPEC_IFF] >>
	      IMP_RES_TAC InvR_SGI_pending_lem 
	  ) >>
	  RW_TAC std_ss [wordsTheory.w2n_11, PRQ_def,
			 prio_SGI_axiom]
	  ,
	  (* PIR *)
	  RW_TAC std_ss [wordsTheory.w2n_11, PRQ_def]
	 ]
  ) >>
  STRIP_TAC >- (
      (* PIR id *)
      NTAC 2 STRIP_TAC >>
      `PCG c < PAR.ng /\ PCC c < PAR.nc_g (PCG c)` by ( 
          METIS_TAC [good_proj_in_range_impls] 
      ) >>
      `q = PIR id` by (
          Cases_on `q`
          >| [(* SGI *)
	      `?id s r. p=(id,s,r)` by ( 
	          METIS_TAC [pairTheory.pair_CASES] 
	      ) >>
	      `r = c` by (
	          FULL_SIMP_TAC std_ss [ready_irqs_def, 
					pred_setTheory.IN_GSPEC_IFF] >>
		  IMP_RES_TAC InvR_SGI_pending_lem 
	      ) >>
	      FULL_SIMP_TAC std_ss [PRQ_def] >>
	      REV_FULL_SIMP_TAC std_ss [irqID_distinct]
	      ,
	      (* PIR *)
	      FULL_SIMP_TAC std_ss [PRQ_def]
	     ]
      ) >>
      RES_TAC >>
      ASM_REWRITE_TAC []
  ) >> ( 
      (* SGI id *)
      NTAC 4 STRIP_TAC >>
      `PCG c < PAR.ng /\ PCC c < PAR.nc_g (PCG c)` by ( 
          METIS_TAC [good_proj_in_range_impls] 
      ) >>
      `q = SGI (id,c',c)` by (
          Cases_on `q`
          >| [(* SGI *)
	      `?id s r. p=(id,s,r)` by ( 
	          METIS_TAC [pairTheory.pair_CASES] 
	      ) >>
	      `r = c` by (
	          FULL_SIMP_TAC std_ss [ready_irqs_def, 
					pred_setTheory.IN_GSPEC_IFF] >>
		  IMP_RES_TAC InvR_SGI_pending_lem 
	      ) >>
	      FULL_SIMP_TAC std_ss [PRQ_def] >>
	      REV_FULL_SIMP_TAC std_ss [irqID_11]
	      ,
	      (* PIR *)
	      FULL_SIMP_TAC std_ss [PRQ_def, irqID_distinct]
	     ]
      ) >>
      RES_TAC >>
      FULL_SIMP_TAC std_ss [PRQ_def] >>
      REV_FULL_SIMP_TAC std_ss [irqID_11]
  )
);

val refined_core_rcv_virt_sim_lem = store_thm("refined_core_rcv_virt_sim_lem", ``
!RM IM c RC'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ refcore_step_rcv_virt(RM.C c,RC')
==>
?IC'. idcore_step_rcv_phys ((IM.G (PCG c)).C (PCC c),IC')
``,
  REPEAT STRIP_TAC >>
  `haspoc_exc_conf (RM.C c)` by ( 
      METIS_TAC [InvR_haspoc_exc_conf_lem, Mode_mode_lem]
  ) >>
  IMP_RES_TAC refcore_virt_irq_axiom >>
  MATCH_MP_TAC ( idcore_step_axiom // "rcv_phys_enabled" ) >>
  IMP_RES_TAC bisim_guest_core_lem >>
  FULL_SIMP_TAC arith_ss []
);


(* MEDIUM: same core step, need to distinguish virtual and physical interrupt 
need GIC coupling so that interrupt request is possible in ideal model 
**GUEST/SWITCH**
*)
val refined_CORE_RCV_IRQ_sim_step_lem = store_thm("refined_CORE_RCV_IRQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,CORE_RCV_IRQ n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  REPEAT STRIP_TAC >>
  CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  FULL_SIMP_TAC (srw_ss()) [ref_rule_core_rcv_irq_def, 
			    refcore_step_def, gic_step_def]
  >| [(* PHYS -> enter hypervisor, GIC unchanged *)
      `(gic_req_rcvd GIC' = gic_req_rcvd RM.GIC) /\
       (gic_abs GIC' = gic_abs RM.GIC) /\ 
       (Q GIC' = Q RM.GIC) /\ (VI GIC' = VI RM.GIC)` by (
          METIS_TAC [gic_snd_irq_axiom]
      ) >>
      IMP_RES_TAC bisim_ctx_core_phys_irq_lem >>
      IMP_RES_TAC InvR_core_FLUSHED_req_sent_lem >>
      `~hv_guard_mmu_fault 
           (HVabs(RM with <|C := (n =+ C') RM.C; GIC := GIC'|>,n),n)` by (
          CCONTR_TAC >>
          FULL_SIMP_TAC (srw_ss()) [HVabs_def] >>
          IMP_RES_TAC hv_mmu_fault_entry_point_lem >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `~hv_gicd_entry_state
           (HVabs(RM with <|C := (n =+ C') RM.C; GIC := GIC'|>,n))` by (
          RW_TAC std_ss [HVabs_def, combinTheory.APPLY_UPDATE_THM, 
      			 hv_gicd_entry_state_def] >>
	  DISJ1_TAC >>
      	  blastLib.BBLAST_PROVE_TAC
      ) >>
      `~hv_guard_gicd_fail
           (HVabs(RM with <|C := (n =+ C') RM.C; GIC := GIC'|>,n))` by (
          RW_TAC std_ss [hv_guard_gicd_fail_def]
      ) >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      `~hv_guard_gicd_fail (HVabs (RM,n))` by (
          RW_TAC std_ss [hv_guard_gicd_fail_def]
      ) >>
      (* ideal core *)
      `idcore_req_sent ((IM.G (PCG n)).C (PCC n)) = EMPTY` by (
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_corereq_guest_def >>
	  IMP_RES_TAC bisim_corereq_guest_core_def >>
	  ASM_REWRITE_TAC []
      ) >>
      IMP_RES_TAC bisim_guest_mode_lem >>
      (* stuttering ideal step *)
      EXISTS_TAC ``0`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      FULL_SIMP_TAC std_ss [ideal_model_comp_def] >>
      (* prove SIM *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      (* most cases *)
        EXCEPT_FOR ``bisim_send_igc _``
          (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
             FULL_SIMP_TAC (srw_ss()) 
	         (nuigc_def::(bisim_pi_guest_def::bisim_core_definitions)) >>
             TRY (Cases_on `n=c`) >>
             REPEAT IF_CASES_TAC >>    
             FULL_SIMP_TAC (srw_ss()++ARITH_ss) 
	         [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                  HVabs_def, nuvi_def] >>
             REV_FULL_SIMP_TAC arith_ss [] >>
             TRY (INFS_LIMITED_METIS_TAC 1 
	              [PCG_PCC_inj, good_proj_in_range_impls, 
		       Trrpl_eq_rpl_lem, AHV_corollaries]
		 )
          ) 
      ) >>
      (* send_igc *)
      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
      EXISTS_TAC ``RM:refined_model`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC arith_ss [AHV_corollaries]
      )
      ,
      (* VIRT *)
      `?iGIC'. idgic_step_snd_irq ((IM.G (PCG n)).GIC,PCC n,iGIC')` by (
          METIS_TAC [refined_gic_snd_virq_sim_lem]
      ) >>
      `?IC'. idcore_step_rcv_phys ((IM.G (PCG n)).C (PCC n),IC')` by (
          METIS_TAC [refined_core_rcv_virt_sim_lem]
      ) >>
      IMP_RES_TAC bisim_ctx_core_virt_irq_lem >>
      `(gic_req_rcvd GIC' = gic_req_rcvd RM.GIC) /\
       (gic_abs GIC' = gic_abs RM.GIC) /\ 
       (Q GIC' = Q RM.GIC) /\ (VI GIC' = VI RM.GIC)` by (
          METIS_TAC [gic_snd_irq_axiom]
      ) >>
      `(idgic_abs iGIC' = idgic_abs ((IM.G (PCG n)).GIC)) /\ 
       (idgic_req_rcvd iGIC' = idgic_req_rcvd ((IM.G (PCG n)).GIC)) /\
       (PI iGIC' = PI ((IM.G (PCG n)).GIC))` by (
          METIS_TAC [idgic_step_axiom // "snd_irq"]
      ) >>
      `~hv_guard_mmu_fault 
           (HVabs(RM with <|C := (n =+ C') RM.C; GIC := GIC'|>,n),n)` by (
          MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `~hv_gicd_entry_state
           (HVabs(RM with <|C := (n =+ C') RM.C; GIC := GIC'|>,n))` by (
          MATCH_MP_TAC hv_gicd_entry_state_lem >>
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      (* construct ideal comp *)
      STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC 
          (``INTERNAL (IR_CORE_RCV_IRQ (PCC n))``, NoMem, withoutAnnotations) >>
      FIRST_EXISTS_TAC ``PCG n`` >>
      UNFOLD_IDEAL_TRANS_IN_GOAL_TAC >>  
      IMP_RES_TAC good_proj_in_range_impls >>   
      FULL_SIMP_TAC (srw_ss()) [] >>
      EXISTS_TAC ``IM.G (PCG n) with
          <|C := (PCC n =+ IC') (IM.G (PCG n)).C; GIC := iGIC'|>`` >>
      STRIP_TAC >- ( METIS_TAC [] ) >>
      (* prove SIM *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      (* most cases *)
        EXCEPT_FOR ``bisim_send_igc _``
          (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
             FULL_SIMP_TAC (srw_ss()) 
	         (nuigc_def::(bisim_pi_guest_def::bisim_core_definitions)) >>
             TRY (Cases_on `n=c`) >>
             REPEAT IF_CASES_TAC >>    
             FULL_SIMP_TAC (srw_ss()++ARITH_ss) 
	         [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                  HVabs_def, nuvi_def] >>
             REV_FULL_SIMP_TAC arith_ss [] >>
             TRY (INFS_LIMITED_METIS_TAC 1 
	              [PCG_PCC_inj, good_proj_in_range_impls, 
		       Trrpl_eq_rpl_lem, AHV_corollaries]
		 )
          ) 
      ) >>
      (* send_igc *)
      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
      EXISTS_TAC ``RM:refined_model`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC arith_ss [AHV_corollaries]
      )
     ]
);

val bisim_ctx_core_guest_fault_lem = 
store_thm("bisim_ctx_core_guest_fault_lem", ``
!RM IM g c q C' C''.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ Mode (RM.C c) < 2
/\ Frpl q
/\ ~st2_fault q 
/\ refcore_step_rcv_rpl (RM.C c,q,C')
/\ idcore_step_rcv_rpl ((IM.G (PCG c)).C (PCC c),q,C'')
==>
bisim_ctx_core (idcore_abs C'', 
		refcore_abs C', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC C',c),
	        ectx C',
                refcore_int C',
                idcore_int C'') /\
(Mode C' = 1) /\ (iMode C'' = 1) /\ 
(refcore_req_sent C' = EMPTY) /\ (idcore_req_sent C'' = EMPTY) /\
(ref_abs_int C' = FLUSHED) /\ (id_abs_int C'' = FLUSHED) /\
((refcore_abs C').PC = (idcore_abs C'').PC) /\
((refcore_abs C').H = (refcore_abs (RM.C c)).H)
``,
  NTAC 8 STRIP_TAC >>
  IMP_RES_TAC refcore_rcv_rpl_axiom >>
  IMP_RES_TAC Frpl_ALT_DEF >>
  IMP_RES_TAC (idcore_step_axiom // "rcv_fault") >>
  IMP_RES_TAC refcore_rcv_fault_axiom >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  REV_FULL_SIMP_TAC arith_ss [bisim_ctx_core_def, Mode_mode_lem] >>
  `(mode (refcore_abs (RM.C c)) <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) <> 2)` by ( DECIDE_TAC ) >>
  `mode (refcore_abs C') = 1` by ( 
      FULL_SIMP_TAC std_ss [mode_def, MODE_upd_lem]
  ) >>
  `iMode C'' = 1` by ( 
      FULL_SIMP_TAC std_ss [iMode_def, MODE_upd_lem]
  ) >>
  `(mode (refcore_abs C') <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs C') <> 2)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs C') < 2)` by ( DECIDE_TAC ) >>
  `~soft (refcore_abs C')` by ( FULL_SIMP_TAC arith_ss [soft_mode_lem] ) >>
  RW_TAC std_ss []
  >| [(* SPR *)
      Cases_on `(r'' = ELR_EL1) \/ (r'' = ESR_EL1) \/ 
                (r'' = FAR_EL1) \/ (r'' = SPSR_EL1)`
      >| [(* exception registers *)
	  FULL_SIMP_TAC std_ss []
	  >| [(* ELR_EL1 *)
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [] >>
	      PAT_X_ASSUM ``!r. x`` (
	          fn thm => ASSUME_TAC ( 
			        SPEC ``INL ELR_EL1:SPRguest + SPRhyp`` thm 
			    )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss []
	      ,
	      (* ESR_EL1 *)
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [exception_regs_axiom] >>
	      PAT_X_ASSUM ``!r. x`` (
	          fn thm => ASSUME_TAC ( 
			        SPEC ``INL ESR_EL1:SPRguest + SPRhyp`` thm 
			    )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [exception_regs_axiom]
	      ,
	      (* FAR_EL1 *)
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [exception_regs_axiom] >>
	      PAT_X_ASSUM ``!r. x`` (
	          fn thm => ASSUME_TAC ( 
			        SPEC ``INL FAR_EL1:SPRguest + SPRhyp`` thm 
			    )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [exception_regs_axiom]
	      ,
	      (* FAR_EL1 *)
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      PAT_X_ASSUM ``!r:SPRguest. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [exception_regs_axiom] >>
	      PAT_X_ASSUM ``!r. x`` (
	          fn thm => ASSUME_TAC ( 
			        SPEC ``INL SPSR_EL1:SPRguest + SPRhyp`` thm 
			    )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [exception_regs_axiom]
	     ]
	  ,
	  (* other regs *)
	  PAT_X_ASSUM ``!r:SPRguest. x`` (
	      fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	  ) >>
	  PAT_X_ASSUM ``!r:SPRguest. x`` (
	      fn thm => ASSUME_TAC ( SPEC ``r'':SPRguest`` thm )
	  ) >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  PAT_X_ASSUM ``!r. x`` (
	      fn thm => ASSUME_TAC ( 
			    SPEC ``INL r'':SPRguest + SPRhyp`` thm 
			)
	  ) >>
	  REV_FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* internal state *)
      FULL_SIMP_TAC std_ss [ref_abs_int_def, id_abs_int_def] >>
      IMP_RES_TAC cis_abs_flushed_axiom 
     ]
);

val bisim_ctx_core_st2_fault_lem = 
store_thm("bisim_ctx_core_st2_fault_lem", ``
!RM IM g c q C'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ Frpl q
/\ st2_fault q 
/\ refcore_step_rcv_rpl (RM.C c,q,C')
==>
bisim_ctx_core (idcore_abs ((IM.G (PCG c)).C (PCC c)), 
		refcore_abs C', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC C',c),
	        ectx C',
                refcore_int C',
                idcore_int ((IM.G (PCG c)).C (PCC c))) /\
(Mode C' = 2) /\
(refcore_req_sent C' = EMPTY) /\ 
(ref_abs_int C' = FLUSHED) /\ 
(refcore_abs (RM.C c)).active /\ (refcore_abs C').active /\
((refcore_abs C').PC = (refcore_abs (RM.C c)).SPR (INR VBAR_EL2) + 0x400w) /\
((refcore_abs C').H = (refcore_abs (RM.C c)).H) /\
hv_mmu_fault_entry_point (refcore_abs C') /\
((39 >< 4) ((refcore_abs C').SPR (INR HPFAR_EL2)) = Rpl_PAdr q) /\
(~PTreq (ReqOf q) ==>
 ((11 >< 0) ((refcore_abs C').SPR (INR FAR_EL2)) =
    (11 >< 0) (curr_va (refcore_int (RM.C c))) :bool[12]))
``,
  NTAC 7 STRIP_TAC >>
  IMP_RES_TAC soft_Mode_lem >>
  IMP_RES_TAC refcore_rcv_rpl_axiom >>
  IMP_RES_TAC Frpl_ALT_DEF >>
  FULL_SIMP_TAC std_ss [st2_fault_def, Mode_mode_lem] >>
  IMP_RES_TAC match_Fault_lem >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC InvR_haspoc_exc_conf_lem >>
  IMP_RES_TAC refcore_fault_axiom >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  REV_FULL_SIMP_TAC std_ss [bisim_ctx_core_def, Mode_mode_lem] >>
  `(mode (refcore_abs (RM.C c)) <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) <> 2)` by ( DECIDE_TAC ) >>
  `mode (refcore_abs C') = 2` by ( 
      FULL_SIMP_TAC std_ss [mode_def, MODE_upd_lem]
  ) >>
  IMP_RES_TAC soft_mode_lem >>
  `(mode (refcore_abs C') <> 3)` by ( DECIDE_TAC ) >>
  `~(mode (refcore_abs C') < 2)` by ( DECIDE_TAC ) >>
  FULL_SIMP_TAC std_ss [ectx_def] >>
  `(refcore_abs C').SPR (INR VBAR_EL2) = 
   (refcore_abs (RM.C c)).SPR (INR VBAR_EL2)` by (
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR VBAR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
  ) >>
  `~sc C'` by (
      RW_TAC std_ss [sc_def] >>
      Q.UNABBREV_TAC `a` >>
      RW_TAC std_ss [] >>
      DISJ2_TAC >>
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR ESR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      REWRITE_TAC [extract_ESR_not_sc_lem]
  ) >>
  IMP_RES_TAC InvR_VBAR_lem >>
  RW_TAC std_ss []
  >| [(* new PC not in HV init *)
      RW_TAC std_ss [] >>
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT, 
			    pred_setTheory.NOT_IN_EMPTY, 
			    AHV_corollaries]
      ,
      (* guest SPRs unchanged *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INL r'':SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* PC saved *)
      RW_TAC std_ss [] >>
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR ELR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
      ,
      (* PSTATE saved *)
      RW_TAC std_ss [] >>
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR SPSR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* GPR unchanged *)
      RW_TAC std_ss [] 
      ,
      (* source/target register saved in ESR *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR ESR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      REWRITE_TAC [wordsTheory.WORD_w2w_EXTRACT,
		   wordsTheory.WORD_EXTRACT_COMP_THM] >>
      EVAL_TAC >>
      RW_TAC std_ss [extract_ESR_GICD_gpr_lem]
      ,
      (* PC saved in context -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* PSTATE saved in context -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* GPR saved in context -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* source / target register after JISR -> contradiction *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
      ,
      (* mmu fault entry point *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR ESR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      RW_TAC std_ss [hv_mmu_fault_entry_point_def] >> 
      REWRITE_TAC [wordsTheory.WORD_w2w_EXTRACT,
		   wordsTheory.WORD_EXTRACT_COMP_THM] >>
      EVAL_TAC >>
      REWRITE_TAC [extract_ESR_excp_code_lem]
      ,
      (* fault address saved into HPFAR *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC ( 
	      SPEC ``INR HPFAR_EL2:SPRguest + SPRhyp`` thm 
		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      IMP_RES_TAC good_Frpl_lem >>
      RW_TAC std_ss [Rpl_PAdr_ReqOf_lem, ReqOf_def] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* page index in FAR_EL2 *)
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC (
      	      SPEC ``INR FAR_EL2:SPRguest + SPRhyp`` thm
      		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      REWRITE_TAC [ReqOf_def] >>
      REWRITE_TAC [wordsTheory.WORD_w2w_EXTRACT,
      		   wordsTheory.WORD_EXTRACT_COMP_THM] >>
      EVAL_TAC
     ]      
);


(* EASY: same step in both models, **GUEST/SWITCH**
need MMU coupling and core semantics / bisim property *)
val refined_CORE_RCV_MRPL_sim_step_lem = store_thm("refined_CORE_RCV_MRPL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,CORE_RCV_MRPL n,RM')
==>
?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* start with what we know about refined side *)
  REPEAT STRIP_TAC >>
  CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  `(mmu_abs (RM.MMU n)).active` by METIS_TAC [InvR_EXPAND, ref_inv_mmu_def, Mode_def, mode_def, init_core_lem] >>
  Cases_on `PAdr (ReqOf r) IN RPAR.Amap GICD` >|
  [(* 1. GICD ACCCESS (stuttering ideal step) *)
   EXISTS_TAC ``0`` >>
   EXISTS_TAC ``IM:ideal_model`` >>
   SIMP_TAC std_ss [ideal_model_comp_def] >>
   IMP_RES_TAC good_proj_in_range_impls >>   
   IMP_RES_TAC mmu_reply_lem >-
   ((* cannot be forwarding case *)
    METIS_TAC [GICD_ATrans_lem, InvR_EXPAND, ref_inv_hyp_iso_mmu_final_rpl_def]
   ) >>
   IMP_RES_TAC (Frpl_ALT_DEF |> EQ_IMP_RULE |> fst |> REWRITE_RULE [satTheory.AND_IMP]) >>
   REPEAT BasicProvers.VAR_EQ_TAC >>
   REV_FULL_SIMP_TAC std_ss [ReqOf_def] >>
   `haspoc_exc_conf (RM.C n)` by METIS_TAC [InvR_EXPAND, haspoc_exc_conf_def, Mode_def, mode_def,
                                         ref_inv_hist_def, ref_inv_regel3_def, ref_inv_regel2_def] >>
   IMP_RES_TAC (refcore_fault_axiom |> REWRITE_RULE [satTheory.AND_IMP]) >>
   IMP_RES_SIM_CLAUSE_TAC ``BISIM_CTX`` >>
   IMP_RES_SIM_CLAUSE_TAC ``BISIM_COREREQ_GUEST `` >>
   REV_FULL_SIMP_TAC (std_ss++ARITH_ss) [mode_def, Mode_def] >>
   `id_abs_int ((IM.G (PCG n)).C (PCC n)) <> FLUSHED` by METIS_TAC [InvG_clause_by_InvI ``IDG_GOOD_IDCORE``, pred_setTheory.NOT_IN_EMPTY] >>
   `(idcore_abs ((IM.G (PCG n)).C (PCC n))).active` by METIS_TAC  [InvG_clause_by_InvI ``IDG_GOOD_IDCORE``] >>
   `st2_fault (Fault r' f)` by ( METIS_TAC [compute_fault_axiom] ) >>
   `fi_st2 f` by ( FULL_SIMP_TAC std_ss [st2_fault_def] ) >>
   `MODE ((refcore_abs C').PSTATE) = 2` by ASM_SIMP_TAC arith_ss [MODE_upd_lem] >>
   (* bisim *)
   FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
   REPEAT STRIP_TAC >>
   (* most cases *)
   EXCEPT_FOR ``bisim_send_igc _``
     (TRY (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
          FULL_SIMP_TAC (srw_ss()) (nuigc_def::bisim_core_definitions) >>
          TRY (Cases_on `n=c`) >>
          REPEAT IF_CASES_TAC >>    
          FULL_SIMP_TAC (srw_ss()++ARITH_ss) [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                                              HVabs_def, hv_guard_mmu_fault_def, hv_gicd_entry_state_def, nuvi_def] >>
          REV_FULL_SIMP_TAC arith_ss [] >>
          INFS_LIMITED_METIS_TAC 1 [PCG_PCC_inj, good_proj_in_range_impls, Trrpl_eq_rpl_lem]
     )) >>   
   cheat (* TODO: 9 cases left *),
   (* 2. NON-GICD ACCCESS *)
   IMP_RES_TAC soft_Mode_lem >>
   IMP_RES_TAC mmu_reply_lem >|
   [(* 2.1. PROPAGATING REPLY *)
    STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_CORE_RCV_MRPL (PCC n))``, NoMem, withoutAnnotations) >>
    (* 2.1.A. coupling *)
    FIRST_EXISTS_TAC ``PCG n`` >>
    UNFOLD_IDEAL_TRANS_IN_GOAL_TAC >>  
    IMP_RES_TAC good_proj_in_range_impls >>   
    FULL_SIMP_TAC (srw_ss()) [] >>
    SPLIT_EXIST_TAC4 >>
    FIRST_EXISTS_TAC ``r:reply`` >>
    FIRST_EXISTS_TAC ``ReqOf r`` >>
    `ReqOf q' = Trreq (PCG n) (ReqOf r)` by METIS_TAC [Trreq_xlated_ATrans_lem, ref_inv_hyp_iso_mmu_final_rpl_def, InvR_EXPAND] >>
    `q' = Trrpl (PCG n) r` by METIS_TAC [match_Trrpl_lem] >>
    `IS_SOME (Trans (PCG n) (Rpl_PAdr r))` by METIS_TAC [ATrans_lem, ref_inv_hyp_iso_mmu_final_rpl_def, InvR_EXPAND, match_PAdr_eq_lem] >>
    IMP_RES_TAC Trreq_xlated_ATrans_lem >>
    IMP_RES_SIM_CLAUSE_TAC ``BISIM_COREREQ_GUEST `` >>
    MATCHING_BY_SIM_CLAUSE ``BISIM_MMUREQ_GUEST`` ``_ IN _.rpl_rcvd`` [] >>
    IMP_RES_TAC good_match_lem >>
    FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS, matching_request_set_lem] >>
    IMP_RES_TAC (InvG_clause_by_InvI ``IDG_CIFRPL`` |> UNIQUE_REQ) >>
    SPLIT_OFF_SIM_FROM_GOAL_TAC >|
    [(* 2.1.B. ideal step exists + InvG consequences *)
     METIS_TAC [InvG_clause_by_InvI ``IDG_GOOD_IDCORE``,
                idcore_step_axiom // "rcv_rpl_enabled",
                pred_setTheory.MEMBER_NOT_EMPTY,
                arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
                arithmeticTheory.TWO],
     (* 2.1.C. bisim *)
     IMP_RES_SIM_CLAUSE_TAC ``BISIM_CTX`` >>
     REV_FULL_SIMP_TAC (std_ss++ARITH_ss) [mode_def, Mode_def] >>
     `id_abs_int ((IM.G (PCG n)).C (PCC n)) <> FLUSHED` by METIS_TAC [InvG_clause_by_InvI ``IDG_GOOD_IDCORE``, pred_setTheory.NOT_IN_EMPTY] >>
     Cases_on `Frpl r` >|
     [(* 2.1.C.1. PROPAGATING FAULT *)
      IMP_RES_TAC ( bisim_ctx_core_guest_fault_lem |>
			SIMP_RULE std_ss [Mode_def, iMode_def] ) >>
      IMP_RES_TAC match_PAdr_eq_lem >> 
      `~soft (refcore_abs C')` by (
          FULL_SIMP_TAC arith_ss [Mode_def, soft_Mode_lem]
      ) >>
      (* REV_FULL_SIMP_TAC std_ss [id_abs_int_def, ref_abs_int_def] >> *)
      (* start case distinction *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >- (
          FULL_SIMP_TAC std_ss [bisim_ctx_def] >>
	  RW_TAC std_ss [] >>
	  Cases_on `n=c`
	  >| [(* stepped core *)
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	      ,
	      (* other cores *)
	      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	      `PCC n <> PCC c` by ( METIS_TAC [PCG_PCC_inj] ) >>
	      RW_TAC std_ss []
	     ]
      ) >> (
      (* most cases *)
      EXCEPT_FOR ``bisim_send_igc _``
        (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
             FULL_SIMP_TAC (srw_ss()) (nuigc_def::bisim_core_definitions) >>
             TRY (Cases_on `n=c`) >>
             REPEAT IF_CASES_TAC >>    
             FULL_SIMP_TAC (srw_ss()++ARITH_ss) [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                                                 HVabs_def, hv_guard_mmu_fault_def, hv_gicd_entry_state_def, nuvi_def] >>
             REV_FULL_SIMP_TAC arith_ss [] >>
             INFS_LIMITED_METIS_TAC 1 [PCG_PCC_inj, good_proj_in_range_impls, Trrpl_eq_rpl_lem]
        )
      ) >>
      (* send_igc *)
      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
      EXISTS_TAC ``RM:refined_model`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
          RW_TAC arith_ss [Mode_def]
      )
      ,
      (* 2.1.C.2. PROPAGATING NON-FAULT *)
      IMP_RES_TAC (refcore_rcv_rpl_axiom |> UNIQUE_REQ) >> 
      IMP_RES_TAC (idcore_step_axiom // "rcv_rpl" |> UNIQUE_REQ) >>
      `~soft (refcore_abs C')` by (
          FULL_SIMP_TAC arith_ss [Mode_def, soft_Mode_lem]
      ) >>
      IMP_RES_TAC match_PAdr_eq_lem >>   
      IMP_RES_TAC ((STEP_PREDICATE_FIRST_RULE o (REWRITE_RULE [Mode_def])) core_rcv_rpl_bisim_axiom) >>
      REV_FULL_SIMP_TAC std_ss [id_abs_int_def, ref_abs_int_def] >>
      (* start case distinction *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >>
      (* most cases *)
      EXCEPT_FOR ``bisim_send_igc _``
        (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
             FULL_SIMP_TAC (srw_ss()) (nuigc_def::bisim_core_definitions) >>
             TRY (Cases_on `n=c`) >>
             REPEAT IF_CASES_TAC >>    
             FULL_SIMP_TAC (srw_ss()++ARITH_ss) [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                                                 HVabs_def, hv_guard_mmu_fault_def, hv_gicd_entry_state_def, nuvi_def] >>
             REV_FULL_SIMP_TAC arith_ss [] >>
             INFS_LIMITED_METIS_TAC 1 [PCG_PCC_inj, good_proj_in_range_impls, Trrpl_eq_rpl_lem]
        ) >>
      (* send_igc *)
      MATCH_MP_TAC bisim_send_igc_core_step_lem >>
      EXISTS_TAC ``RM:refined_model`` >>
      EXISTS_TAC ``IM:ideal_model`` >>
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
          FULL_SIMP_TAC arith_ss [Mode_def]
      )
     ]
    ],
    (* 2.2. GENERATING FAULT *)
    EXISTS_TAC ``0`` >>
    EXISTS_TAC ``IM:ideal_model`` >>
    REWRITE_TAC [ideal_model_comp_def] >>
    IMP_RES_TAC compute_fault_axiom >>
    IMP_RES_TAC InvR_core_curr_va_lem >>
    IMP_RES_TAC bisim_ctx_core_st2_fault_lem >>
    IMP_RES_TAC soft_Mode_lem >>
    IMP_RES_TAC match_PAdr_eq_lem >>
    IMP_RES_TAC good_Frpl_lem >>
    `Adr (ReqOf r) = ((39><4)((refcore_abs C').SPR(INR HPFAR_EL2)):bool[36])
		  @@ ((11><0)(Adr (ReqOf r)):bool[12])` by (
		  (* @@ ((11><0)((refcore_abs C').SPR(INR FAR_EL2)):bool[12])` by ( *)
        RW_TAC std_ss [] >>
	`Adr (ReqOf r) = Rpl_Adr r` by ( METIS_TAC [Rpl_Adr_ReqOf_lem] ) >>
	RW_TAC std_ss [Rpl_Adr_concat_lem]
    ) >>
    `hv_mmu_fault_entry_point (
	 (HVabs (RM with <|C := (n =+ C') RM.C; MMU := (n =+ MMU') RM.MMU|>,
		 n)).C )` by (
        RW_TAC std_ss [HVabs_def, combinTheory.APPLY_UPDATE_THM]
    ) >>
    `(39 >< 4) ((HVabs (
        RM with <|C := (n =+ C') RM.C; MMU := (n =+ MMU') RM.MMU|>,
		  n)).C.SPR (INR HPFAR_EL2)) <> Agicd` by (
        RW_TAC std_ss [HVabs_def, combinTheory.APPLY_UPDATE_THM] >>
	IMP_RES_TAC good_Frpl_lem >>
	`Rpl_PAdr r NOTIN RPAR.Amap GICD` by (
	     METIS_TAC [Rpl_PAdr_ReqOf_lem]
	) >>
	IMP_RES_TAC not_in_GICD_not_Agicd_lem
    ) >>
    `~hv_gicd_entry_state (
	 HVabs (RM with <|C := (n =+ C') RM.C; MMU := (n =+ MMU') RM.MMU|>,
		n))` by (
        RW_TAC std_ss [HVabs_def, combinTheory.APPLY_UPDATE_THM, 
		       hv_gicd_entry_state_def]
    ) >>
    `hv_guard_mmu_fault (
	 (HVabs (RM with <|C := (n =+ C') RM.C; MMU := (n =+ MMU') RM.MMU|>,
		 n),n))` by (
        FULL_SIMP_TAC std_ss [hv_mmu_fault_entry_point_def] >>
        RW_TAC std_ss [HVabs_def, hv_guard_mmu_fault_def, 
		       combinTheory.APPLY_UPDATE_THM]
    ) >>
    `(refcore_abs((RM with 
                  <|C := (n =+ C') RM.C; MMU := (n =+ MMU') RM.MMU|>).C n)).PC 
          NOTIN {AHV PC_GICD_SAVE_CTX; 
		 AHV PC_GICD_ACCESS; 
		 AHV PC_GICD_FILTER}` by (
        RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM, InvR_VBAR_not_GICD_lem]
    ) >>
    IMP_RES_TAC ( InvR_VBAR_lem |> SIMP_RULE std_ss [GSYM Mode_mode_lem] ) >>
    IMP_RES_TAC core_req_sent_lem >>
    IMP_RES_TAC bisim_mmu_req_rcvd_lem >>
    (* unfold SIM *)
    FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
    REPEAT STRIP_TAC >- (
        FULL_SIMP_TAC std_ss [bisim_ctx_def] >>
	RW_TAC std_ss [] >>
	Cases_on `n=c`
	>| [(* stepped core *)
	    RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
	    ,
	    (* other cores *)
	    RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
	    `PCC n <> PCC c` by ( METIS_TAC [PCG_PCC_inj] ) >>
	    RW_TAC std_ss []
	   ]
    ) >> (
      (* most cases *)
      EXCEPT_FOR ``bisim_send_igc _`` (
        FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	FULL_SIMP_TAC (srw_ss()) (nuigc_def::bisim_core_definitions) >>
        TRY (Cases_on `n=c`) >>
        REPEAT IF_CASES_TAC >>    
        FULL_SIMP_TAC (srw_ss()++ARITH_ss) [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def, HVabs_def, hv_guard_mmu_fault_def, hv_gicd_entry_state_def, nuvi_def, hv_guard_gicd_fail_def] >>
        REV_FULL_SIMP_TAC arith_ss [] >>
        TRY ( INFS_LIMITED_METIS_TAC 1 [PCG_PCC_inj, good_proj_in_range_impls, Trrpl_eq_rpl_lem, mmu_fault_not_GICD_req_lem, AHV_corollaries] ) 
      )
    ) >>
    (* send_igc *)
    MATCH_MP_TAC bisim_send_igc_core_step_lem >>
    EXISTS_TAC ``RM:refined_model`` >>
    EXISTS_TAC ``IM:ideal_model`` >>
    RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
	RW_TAC arith_ss [Mode_def, AHV_corollaries]
    ) >>
    FULL_SIMP_TAC arith_ss [Mode_def]
   ]
  ]
);

val alt_ref_rule_core_rcv_event_def = Define `
alt_ref_rule_core_rcv_event(M,c,M') =
?e PS' C'.
    psci_step (M.PSCI,SEND (PSCI e),c,PS') /\
    refcore_step (M.C c,RCV (PSCI e),C') /\
    ((e = StartCore c) \/ (e = StopCore c)) /\
    ((e = StopCore c) ==> Mode (M.C c) < 2) /\
    ((e = StartCore c) ==>
     ~(refcore_abs (M.C c)).active /\ Mode (M.C c) <> 2 \/
      (refcore_abs (M.C c)).active /\ Mode (M.C c) < 2) /\
    (M' = M with <|C := (c =+ C') M.C; PSCI := PS'|>)
`;

val core_rcv_event_rw = store_thm("core_event_rw", ``
!M c M'. ref_rule_core_rcv_event(M,c,M') <=> alt_ref_rule_core_rcv_event(M,c,M')
``,
  RW_TAC std_ss [alt_ref_rule_core_rcv_event_def, 
		 ref_rule_core_rcv_event_def] >>
  EQ_TAC >> (
      STRIP_TAC >> (
          HINT_EXISTS_TAC >>
          HINT_EXISTS_TAC >>
          HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [event_distinct]
      ) >>
      RES_TAC >> (
          FULL_SIMP_TAC arith_ss []
      )
  )
);

(* EASY: same step in both models, only core and PSCI affected **GUEST/SWITCH** *)
val refined_CORE_RCV_EVENT_sim_step_lem = store_thm("refined_CORE_RCV_EVENT_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,CORE_RCV_EVENT n,RM')
==>
?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
 (* choosing step *)
 RW_TAC (srw_ss()) [] >>
 STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_CORE_RCV_EVENT (PCC n))``, NoMem, withoutAnnotations) >>
 (* coupling *)
 RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_core_rcv_event_def,
		    idcore_step_def, idpsci_step_def] >>
 FULL_SIMP_TAC (srw_ss()) [refined_trans_def, core_rcv_event_rw] >>
 FULL_SIMP_TAC (srw_ss()) [refined_trans_def, alt_ref_rule_core_rcv_event_def,
			   PULL_EXISTS, refcore_step_def, psci_step_def]
 >| [(* 1. start core *)
     FIRST_EXISTS_TAC ``PCG n`` >>
     REV_FULL_SIMP_TAC std_ss []
     >| [(* refcore inactive *)
	 IMP_RES_TAC proj_bound_lem >>
	 `~(idcore_abs ((IM.G (PCG n)).C (PCC n))).active` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def]
	 ) >>
	 (* TODO: Mode 3 -> boot loader *)
	 Cases_on `Mode (RM.C n) = 3` >- (cheat) >>
	 `Mode (RM.C n) < 2` by (
	     ASSUME_TAC (SPEC ``RM.C n`` Mode_bound_lem ) >>
	     DECIDE_TAC
	 ) >>
	 EXISTS_TAC ``StartCore (PCC n)`` >>
	 `?IC'. idcore_step_rcv_psci ((IM.G (PCG n)).C (PCC n),
				      StartCore (PCC n),IC')` by (
	     METIS_TAC [idcore_step_axiom // "rcv_psci_enabled"]
	 ) >>
	 `?ps'. psci_step_snd_event ((IM.G (PCG n)).PSCI,
				     StartCore (PCC n),PCC n,ps')` by (
	     RW_TAC (srw_ss()) [psci_step_snd_event_def] >> 
	     EXISTS_TAC ``(IM.G (PCG n)).PSCI with
                 <|events := (PCC n =+ TL ((IM.G (PCG n)).PSCI.events (PCC n)))
				 (IM.G (PCG n)).PSCI.events;
		   pow := (PCC n =+ T) (IM.G (PCG n)).PSCI.pow|>`` >>
	     IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	     IMP_RES_TAC psci_step_snd_event_def >>
	     RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	     RW_TAC (srw_ss()) [HD_MAP_lem, PEE_def]
	 ) >>
	 `~(idcore_abs ((IM.G (PCG n)).C (PCC n))).H.launch` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def, Mode_mode_lem, Mode_arith_lem]
	 ) >>
	 EXISTS_TAC ``ps':psci_state`` >>
	 EXISTS_TAC ``IC':idcore`` >>
	 ASM_REWRITE_TAC [] >>
	 (* add context *)
	 FULL_SIMP_TAC (srw_ss()) [] >>
	 IMP_RES_TAC psci_step_snd_event_def >>
	 FULL_SIMP_TAC (srw_ss()) [] >>
	 IMP_RES_TAC refcore_psci_start_axiom >>
	 `(idcore_req_sent ((IM.G (PCG n)).C (PCC n)) = EMPTY) /\ 
	  (idcore_req_sent IC' = EMPTY) /\ 
	  ~((idcore_abs IC').active) /\ 
	  ((idcore_abs IC').H.launch) /\
          ((idcore_abs IC').PC = (idcore_abs ((IM.G (PCG n)).C (PCC n))).PC) /\
          ((idcore_abs IC').PSTATE = 
	   (idcore_abs ((IM.G (PCG n)).C (PCC n))).PSTATE) /\
          ((idcore_abs IC').GPR = (idcore_abs ((IM.G (PCG n)).C (PCC n))).GPR) /\
          ((idcore_abs IC').SPR = (idcore_abs ((IM.G (PCG n)).C (PCC n))).SPR) /\
	  (id_abs_int ((IM.G (PCG n)).C (PCC n)) = FLUSHED) /\
	  (id_abs_int IC' = FLUSHED)` by (
	     IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	     FULL_SIMP_TAC (srw_ss()) [] >>
	     REV_FULL_SIMP_TAC (srw_ss()) []
	 ) >>
	 REV_FULL_SIMP_TAC std_ss [] >>
	 `(Mode C' = 3) /\ (refcore_abs C').active` by ( 
	     METIS_TAC [warm_soft_axiom, Mode_mode_lem]
	 ) >>
	 `~hv_guard_mmu_fault (HVabs(RM with <|C := (n =+ C') RM.C; 
						PSCI := PS'|>,n),n)` by (
	     FULL_SIMP_TAC (srw_ss()) [HVabs_def, hv_guard_mmu_fault_def,
				       combinTheory.APPLY_UPDATE_THM] >>
	     FULL_SIMP_TAC arith_ss [Mode_mode_lem]
	 ) >>
	 `~hv_gicd_entry_state (HVabs(RM with <|C := (n =+ C') RM.C; 
						 PSCI := PS'|>,n))` by (
	     FULL_SIMP_TAC (srw_ss()) [HVabs_def, hv_gicd_entry_state_def,
				       combinTheory.APPLY_UPDATE_THM] >>
	     FULL_SIMP_TAC arith_ss [Mode_mode_lem]
	 ) >>
	 `~hv_gicd_entry_state (HVabs(RM with <|C := (n =+ C') RM.C; 
						 PSCI := PS'|>,n))` by (
	     FULL_SIMP_TAC (srw_ss()) [HVabs_def, hv_gicd_entry_state_def,
				       combinTheory.APPLY_UPDATE_THM] >>
	     FULL_SIMP_TAC arith_ss [Mode_mode_lem]
	 ) >>
	 `~hv_guard_gicd_fail (HVabs(RM with <|C := (n =+ C') RM.C; 
					       PSCI := PS'|>,n))` by (
	     FULL_SIMP_TAC (srw_ss()) [HVabs_def, hv_guard_gicd_fail_def,
				       hv_gicd_entry_state_def,
				       combinTheory.APPLY_UPDATE_THM] >>
	     FULL_SIMP_TAC arith_ss [Mode_mode_lem]
	 ) >>
	 IMP_RES_TAC hv_guard_mmu_fault_lem >>
	 IMP_RES_TAC hv_gicd_entry_state_lem >>
	 IMP_RES_TAC hv_guard_gicd_fail_mode_lem >>
	 (* prove SIM *)
	 FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	 REPEAT STRIP_TAC >> (
	   EXCEPT_FOR_THESE [``bisim_send_igc _``, ``bisim_psci _ ``] (
	   FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	   (* try to solve straight-forward cases *)
	   REPEAT IF_CASES_TAC >>
           STRONG_FS_TAC ([]@bisim_core_definitions) >>
	   `!c. n <> c ==> (RM.C c = (RM with <|C := (n =+ C') RM.C; 
					        PSCI := PS'|>).C c)` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	   ) >>
      	   TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			    hv_mmu_fault_entry_eq_lem,
      			    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
			    nuigc_guest_mode_lem, nusgi_boot_mode_lem, 
			    nuvi_boot_mode_lem, nuigc_boot_mode_lem] ) ) )
	 >| [(* bisim_send_igc *)
	     FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	     IF_CASES_TAC
	     >| [(* n = c' *)
		 STRONG_FS_TAC ([]@bisim_core_definitions) >>
		 REPEAT STRIP_TAC
		 >| [METIS_TAC []
		     ,
		     `!c_. c_ < RPAR.nc ==>
		      (nusgi((λc. RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c') =
		       nusgi((λc. if c' = c then C' else RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
		         RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
			 METIS_TAC [Mode_arith_lem]
		     ) >>
		     METIS_TAC [nusgi_def, Mode_arith_lem]
		    ]
		 ,
		 (* n <> c' *)
		 STRONG_FS_TAC ([]@bisim_core_definitions) >>
		 REPEAT STRIP_TAC
		 >| [METIS_TAC []
		     ,
		     `!c_. c_ < RPAR.nc ==>
		      (nusgi((λc. RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c') =
		       nusgi((λc. if n = c then C' else RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
		         RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
			 METIS_TAC [Mode_arith_lem]
		     ) >>
		     METIS_TAC [Mode_arith_lem]
		    ]
		]
	     ,
	     (* bisim_psci *)
	     FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	     >| [IF_CASES_TAC >> (
		     METIS_TAC [PCG_PCC_inj]
		 )
		 ,
		 IF_CASES_TAC
		 >| [IF_CASES_TAC
		     >| [IF_CASES_TAC
			 >| [METIS_TAC [listTheory.NULL_EQ, 
					listTheory.MAP_TL]
			     ,
			     METIS_TAC [PCG_PCC_inj]
			    ]
			 ,
			 METIS_TAC [PCG_PCC_inj]
			]
		     ,
		     METIS_TAC [PCG_PCC_inj]
		    ]
		]
	    ]
	 ,
         (* redundant StartCore message *) 
	 FULL_SIMP_TAC std_ss [event_distinct] >>
         IMP_RES_TAC refcore_psci_start_axiom >>
	 EXISTS_TAC ``PEE e`` >>
	 FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
	 REV_FULL_SIMP_TAC std_ss [] >>
	 IMP_RES_TAC proj_bound_lem >>
	 IMP_RES_TAC soft_Mode_lem >>
	 `(refcore_abs (RM.C n)).H.launched` by (
             METIS_TAC [InvR_EXPAND, ref_inv_hist_def, Mode_mode_lem]
	 ) >>
	 `(idcore_abs ((IM.G (PCG n)).C (PCC n))).active` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def]
	 ) >>
	 `idcore_req_sent ((IM.G (PCG n)).C (PCC n)) = EMPTY` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_corereq_guest_def >>
	     METIS_TAC [bisim_corereq_guest_core_def]
	 ) >>
	 `?IC'. idcore_step_rcv_psci ((IM.G (PCG n)).C (PCC n),
				      StartCore (PCC n),IC')` by (
	     METIS_TAC [idcore_step_axiom // "rcv_psci_enabled"]
	 ) >>
	 `?ps'. psci_step_snd_event ((IM.G (PCG n)).PSCI,
				     StartCore (PCC n),PCC n,ps')` by (
	     RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	     EXISTS_TAC ``(IM.G (PCG n)).PSCI with
                 <|events := (PCC n =+ TL ((IM.G (PCG n)).PSCI.events (PCC n)))
				 (IM.G (PCG n)).PSCI.events;
		   pow := (PCC n =+ T) (IM.G (PCG n)).PSCI.pow|>`` >>
	     IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	     IMP_RES_TAC psci_step_snd_event_def >>
	     RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	     RW_TAC (srw_ss()) [HD_MAP_lem, PEE_def]
	 ) >>
	 `~(idcore_abs ((IM.G (PCG n)).C (PCC n))).H.launch` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def, Mode_mode_lem, Mode_arith_lem]
	 ) >>
	 EXISTS_TAC ``ps':psci_state`` >>
	 EXISTS_TAC ``IC':idcore`` >>
	 ASM_REWRITE_TAC [] >>
	 (* add context *)
	 IMP_RES_TAC psci_step_snd_event_def >>
	 FULL_SIMP_TAC (srw_ss()) [] >>
	 IMP_RES_TAC refcore_psci_start_axiom >>
	 IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	 REV_FULL_SIMP_TAC (srw_ss()) [] >>
	 `Mode C' < 2` by ( FULL_SIMP_TAC std_ss [Mode_def] ) >>
	 IMP_RES_TAC soft_Mode_lem >>
	 `~hv_guard_mmu_fault (HVabs(RM with <|C := (n =+ C') RM.C; 
						PSCI := PS'|>,n),n)` by (
	     MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ) >>
	 `~hv_gicd_entry_state (HVabs(RM with <|C := (n =+ C') RM.C; 
						 PSCI := PS'|>,n))` by (
	     MATCH_MP_TAC hv_gicd_entry_state_lem >>
	     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ) >>
	 `~hv_guard_gicd_fail (HVabs(RM with <|C := (n =+ C') RM.C; 
					       PSCI := PS'|>,n))` by (
	     FULL_SIMP_TAC (srw_ss()) [HVabs_def, hv_guard_gicd_fail_def,
				       hv_gicd_entry_state_def,
				       combinTheory.APPLY_UPDATE_THM] >>
	     FULL_SIMP_TAC arith_ss [Mode_mode_lem]
	 ) >>
	 IMP_RES_TAC hv_guard_mmu_fault_lem >>
	 IMP_RES_TAC hv_gicd_entry_state_lem >>
	 IMP_RES_TAC hv_guard_gicd_fail_mode_lem >>
	 (* prove SIM *)
	 FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	 REPEAT STRIP_TAC >> (
	   EXCEPT_FOR_THESE [``bisim_psci _ ``] (
	   FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	   (* try to solve straight-forward cases *)
	   REPEAT IF_CASES_TAC >>
           STRONG_FS_TAC ([]@bisim_core_definitions) >>
	   `!c. n <> c ==> (RM.C c = (RM with <|C := (n =+ RM.C n) RM.C; 
					        PSCI := PS'|>).C c)` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	   ) >>
      	   TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			    hv_mmu_fault_entry_eq_lem,
      			    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
			    nuigc_guest_mode_lem] ) ) 
	 ) >>
	 FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	 >| [IF_CASES_TAC >> (
	         METIS_TAC [PCG_PCC_inj]
	     )
	     ,
	     IF_CASES_TAC
	     >| [IF_CASES_TAC
		 >| [IF_CASES_TAC
		     >| [METIS_TAC [listTheory.NULL_EQ, 
				    listTheory.MAP_TL]
		         ,
			 METIS_TAC [PCG_PCC_inj]
			]
		     ,
		     METIS_TAC [PCG_PCC_inj]
		    ]
	         ,
		 METIS_TAC [PCG_PCC_inj]
		]
	    ]	
	]
     ,
     (* 2. stop core *)
     EXISTS_TAC ``PCG n`` >>
     EXISTS_TAC ``PEE e`` >>
     FULL_SIMP_TAC std_ss [] >>
     REV_FULL_SIMP_TAC std_ss [] >>
     Cases_on `(refcore_abs (RM.C n)).active`
     >| [(* active -> turn off *)
	 `(refcore_req_sent (RM.C n) = EMPTY)` by (
             METIS_TAC [refcore_psci_stop_axiom]
	 ) >>
	 IMP_RES_TAC proj_bound_lem >>
	 FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
	 IMP_RES_TAC bisim_guest_mode_lem >>
	 `idcore_req_sent ((IM.G (PCG n)).C (PCC n)) = EMPTY` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_corereq_guest_def >>
	     METIS_TAC [bisim_corereq_guest_core_def]
	 ) >>
	 `?IC'. idcore_step_rcv_psci ((IM.G (PCG n)).C (PCC n),
				      StopCore (PCC n),IC')` by (
	     METIS_TAC [idcore_step_axiom // "rcv_psci_enabled"]
	 ) >>
	 `?ps'. psci_step_snd_event ((IM.G (PCG n)).PSCI,
				     StopCore (PCC n),PCC n,ps')` by (
	     RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	     EXISTS_TAC ``(IM.G (PCG n)).PSCI with
                 <|events := (PCC n =+ TL ((IM.G (PCG n)).PSCI.events (PCC n)))
				 (IM.G (PCG n)).PSCI.events;
		   pow := (PCC n =+ F) (IM.G (PCG n)).PSCI.pow|>`` >>
	     IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	     IMP_RES_TAC psci_step_snd_event_def >>
	     RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	     RW_TAC (srw_ss()) [HD_MAP_lem, PEE_def]
	 ) >>
	 `~(idcore_abs ((IM.G (PCG n)).C (PCC n))).H.launch` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def, Mode_mode_lem, Mode_arith_lem]
	 ) >>
	 EXISTS_TAC ``ps':psci_state`` >>
	 EXISTS_TAC ``IC':idcore`` >>
	 ASM_REWRITE_TAC [] >>
	 (* add context *)
	 IMP_RES_TAC psci_step_snd_event_def >>
	 FULL_SIMP_TAC (srw_ss()) [] >>
	 IMP_RES_TAC refcore_psci_stop_axiom >>
	 `(idcore_req_sent ((IM.G (PCG n)).C (PCC n)) = EMPTY) /\ 
	  (idcore_req_sent IC' = EMPTY) /\ 
	  ~((idcore_abs IC').active) /\ 
	  ~((idcore_abs IC').H.launch) /\
          ((idcore_abs IC').PC = (idcore_abs ((IM.G (PCG n)).C (PCC n))).PC) /\
          ((idcore_abs IC').PSTATE = 
	   (idcore_abs ((IM.G (PCG n)).C (PCC n))).PSTATE) /\
          ((idcore_abs IC').GPR = (idcore_abs ((IM.G (PCG n)).C (PCC n))).GPR) /\
          ((idcore_abs IC').SPR = (idcore_abs ((IM.G (PCG n)).C (PCC n))).SPR) /\
	  (id_abs_int ((IM.G (PCG n)).C (PCC n)) = FLUSHED) /\
	  (id_abs_int IC' = FLUSHED)` by (
	     IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	     FULL_SIMP_TAC (srw_ss()) [] >>
	     REV_FULL_SIMP_TAC (srw_ss()) []
	 ) >>
	 REV_FULL_SIMP_TAC std_ss [] >>
	 `Mode C' < 2` by ( FULL_SIMP_TAC std_ss [Mode_def] ) >>
	 `~hv_guard_mmu_fault (HVabs(RM with <|C := (n =+ C') RM.C; 
						PSCI := PS'|>,n),n)` by (
	     MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ) >>
	 `~hv_gicd_entry_state (HVabs(RM with <|C := (n =+ C') RM.C; 
						 PSCI := PS'|>,n))` by (
	     MATCH_MP_TAC hv_gicd_entry_state_lem >>
	     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ) >>
	 IMP_RES_TAC hv_guard_mmu_fault_lem >>
	 IMP_RES_TAC hv_gicd_entry_state_lem >>
	 (* prove SIM *)
	 FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	 REPEAT STRIP_TAC >> (
	   EXCEPT_FOR_THESE [``bisim_send_igc _``, ``bisim_psci _ ``] (
	   FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	   (* try to solve straight-forward cases *)
	   REPEAT IF_CASES_TAC >>
           STRONG_FS_TAC ([]@bisim_core_definitions) >>
	   `!c. n <> c ==> (RM.C c = (RM with <|C := (n =+ C') RM.C; 
					        PSCI := PS'|>).C c)` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	   ) >>
      	   TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			    hv_mmu_fault_entry_eq_lem,
      			    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
			    nuigc_guest_mode_lem] ) ) )
	 >| [(* bisim_send_igc *)
	     FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	     IF_CASES_TAC
	     >| [(* n = c' *)
		 STRONG_FS_TAC ([]@bisim_core_definitions) >>
		 REPEAT STRIP_TAC
		 >| [METIS_TAC []
		     ,
		     `!c_. c_ < RPAR.nc ==>
		      (nusgi((λc. RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c') =
		       nusgi((λc. if c' = c then C' else RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
		         RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
			 METIS_TAC [Mode_arith_lem]
		     ) >>
		     METIS_TAC [nusgi_def, Mode_arith_lem]
		    ]
		 ,
		 (* n <> c' *)
		 STRONG_FS_TAC ([]@bisim_core_definitions) >>
		 REPEAT STRIP_TAC
		 >| [METIS_TAC []
		     ,
		     `!c_. c_ < RPAR.nc ==>
		      (nusgi((λc. RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c') =
		       nusgi((λc. if n = c then C' else RM.C c),
			     (λc. mmu_rpl_rcvd (RM.MMU c)),
			     mem_rpl_rcvd RM.m) (c_,c'))` by ( 
		         RW_TAC std_ss [nusgi_def, Mode_arith_lem] >>
			 METIS_TAC [Mode_arith_lem]
		     ) >>
		     METIS_TAC [Mode_arith_lem]
		    ]
		]
	     ,
	     (* bisim_psci *)
	     FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	     >| [IF_CASES_TAC >> (
		     METIS_TAC [PCG_PCC_inj]
		 )
		 ,
		 IF_CASES_TAC
		 >| [IF_CASES_TAC
		     >| [IF_CASES_TAC
			 >| [METIS_TAC [listTheory.NULL_EQ, 
					listTheory.MAP_TL]
			     ,
			     METIS_TAC [PCG_PCC_inj]
			    ]
			 ,
			 METIS_TAC [PCG_PCC_inj]
			]
		     ,
		     METIS_TAC [PCG_PCC_inj]
		    ]
		]
	    ]
	 ,
	 (* already off -> no effect but on PSCI *)
	 IMP_RES_TAC refcore_psci_stop_axiom >>
	 FULL_SIMP_TAC (srw_ss()) [PEE_def] >>
	 REV_FULL_SIMP_TAC std_ss [] >>
	 IMP_RES_TAC proj_bound_lem >>
	 `~(idcore_abs ((IM.G (PCG n)).C (PCC n))).active` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def]
	 ) >>
	 `?IC'. idcore_step_rcv_psci ((IM.G (PCG n)).C (PCC n),
				      StopCore (PCC n),IC')` by (
	     METIS_TAC [idcore_step_axiom // "rcv_psci_enabled"]
	 ) >>
	 `?ps'. psci_step_snd_event ((IM.G (PCG n)).PSCI,
				     StopCore (PCC n),PCC n,ps')` by (
	     RW_TAC (srw_ss()) [psci_step_snd_event_def] >>
	     EXISTS_TAC ``(IM.G (PCG n)).PSCI with
                 <|events := (PCC n =+ TL ((IM.G (PCG n)).PSCI.events (PCC n)))
				 (IM.G (PCG n)).PSCI.events;
		   pow := (PCC n =+ F) (IM.G (PCG n)).PSCI.pow|>`` >>
	     IMP_RES_SIM_CLAUSE_TAC ``BISIM_PSCI `` >>
	     IMP_RES_TAC psci_step_snd_event_def >>
	     RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	     RW_TAC (srw_ss()) [HD_MAP_lem, PEE_def]
	 ) >>
	 `~(idcore_abs ((IM.G (PCG n)).C (PCC n))).H.launch` by (
	     FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	     IMP_RES_TAC bisim_ctx_def >>
	     METIS_TAC [bisim_ctx_core_def, Mode_mode_lem, Mode_arith_lem]
	 ) >>
	 EXISTS_TAC ``ps':psci_state`` >>
	 EXISTS_TAC ``IC':idcore`` >>
	 ASM_REWRITE_TAC [] >>
	 (* add context *)
	 IMP_RES_TAC psci_step_snd_event_def >>
	 FULL_SIMP_TAC (srw_ss()) [] >>
	 IMP_RES_TAC refcore_psci_stop_axiom >>
	 IMP_RES_TAC (idcore_step_axiom // "rcv_psci") >>
	 REV_FULL_SIMP_TAC (srw_ss()) [] >>
	 `Mode C' < 2` by ( FULL_SIMP_TAC std_ss [Mode_def] ) >>
	 `~hv_guard_mmu_fault (HVabs(RM with <|C := (n =+ C') RM.C; 
						PSCI := PS'|>,n),n)` by (
	     MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ) >>
	 `~hv_gicd_entry_state (HVabs(RM with <|C := (n =+ C') RM.C; 
						 PSCI := PS'|>,n))` by (
	     MATCH_MP_TAC hv_gicd_entry_state_lem >>
	     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ) >>
	 IMP_RES_TAC hv_guard_mmu_fault_lem >>
	 IMP_RES_TAC hv_gicd_entry_state_lem >>
	 (* prove SIM *)
	 FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	 REPEAT STRIP_TAC >> (
	   EXCEPT_FOR_THESE [``bisim_psci _ ``] (
	   FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	   (* try to solve straight-forward cases *)
	   REPEAT IF_CASES_TAC >>
           STRONG_FS_TAC ([]@bisim_core_definitions) >>
	   `!c. n <> c ==> (RM.C c = (RM with <|C := (n =+ RM.C n) RM.C; 
					        PSCI := PS'|>).C c)` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	   ) >>
      	   TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			    hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			    hv_mmu_fault_entry_eq_lem,
      			    Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			    proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			    nusgi_guest_mode_lem, nuvi_guest_mode_lem,
			    nuigc_guest_mode_lem] ) ) 
	 ) >>
	 FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
	 >| [IF_CASES_TAC >> (
	         METIS_TAC [PCG_PCC_inj]
	     )
	     ,
	     IF_CASES_TAC
	     >| [IF_CASES_TAC
		 >| [IF_CASES_TAC
		     >| [METIS_TAC [listTheory.NULL_EQ, 
				    listTheory.MAP_TL]
		         ,
			 METIS_TAC [PCG_PCC_inj]
			]
		     ,
		     METIS_TAC [PCG_PCC_inj]
		    ]
	         ,
		 METIS_TAC [PCG_PCC_inj]
		]
	    ]
	]
    ]
);

(* EASY: same step in both models, **GUEST/SWITCH**
need CIF and MMU coupling, core bisim property *)
val refined_CORE_SND_MREQ_sim_step_lem = store_thm("refined_CORE_SND_MREQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,CORE_SND_MREQ n,RM')
==>
?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
 (* focus on existence of guest transition and bisim - leave trivia to tactic *)
 RW_TAC (srw_ss()) []
 THEN STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_CORE_SND_MREQ (PCC n))``, NoMem, withAnnotations)
 (* coupling: don't split goals before main witnesses provided.
    Normally we could then split with SPLIT_OFF_SIM_FROM_GOAL_TAC,
    but in this case we need to hold on until core_send_refined_bisim_axiom
    has provided extra assertions *)
 THEN UNFOLD_IDEAL_TRANS_IN_GOAL_TAC
 THEN UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true
 THEN RW_TAC std_ss []
 THEN IMP_RES_TAC soft_Mode_lem
 THEN SPLIT_EXIST_TAC6
 THEN TYPE_REORDER_EXISTS_TAC ``:request``
 THEN TYPE_REORDER_EXISTS_TAC ``:num``
 THEN EXISTS_TAC ``PCG n``
 THEN EXISTS_TAC ``r:request``
 THEN FULL_SIMP_TAC (srw_ss()) []
 (* existential proof *)
 THEN RW_TAC (srw_ss()) []
 THEN `bisim_rel (RM,BISIM_CTX,IM)` by (FULL_SIMP_TAC (srw_ss()) [SIM_def])
 THEN `(refcore_abs (RM.C n)).active /\ (refcore_req_sent (RM.C n) = EMPTY)` by (
          METIS_TAC [refcore_send_axiom]
      ) 
 THEN `(refcore_abs (RM.C n)).H.launched` by (
          METIS_TAC [InvR_EXPAND, ref_inv_hist_def, Mode_mode_lem]
      )
 THEN IMP_RES_TAC (``bisim_rel (RM,BISIM_CTX,IM)`` |> SIMP_CONV (srw_ss()) [bisim_rel_def, bisim_ctx_def, bisim_ctx_core_def])
 THEN `iMode ((IM.G (PCG n)).C (PCC n)) < 2` by (
          METIS_TAC [Mode_def, iMode_def, mode_def]
      )
 THEN `idcore_req_sent ((IM.G (PCG n)).C (PCC n)) = EMPTY` by (
          METIS_TAC [SIM_EXPAND, bisim_corereq_guest_def, 
		     bisim_corereq_guest_core_def]
      )
 THEN `mode (refcore_abs (RM.C n)) < 2` by ( METIS_TAC [Mode_mode_lem] )
 THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
 THEN IMP_RES_TAC good_proj_axiom 
 THEN FULL_SIMP_TAC (srw_ss()) []
 THEN IMP_RES_TAC refcore_send_axiom 
 THEN `~soft (refcore_abs C')` by ( METIS_TAC [soft_Mode_lem] )
 (* THEN `ref_inv (RM, INV_HIST)` by FULL_SIMP_TAC (srw_ss()) [InvR_def] *)
 (* THEN FULL_SIMP_TAC (srw_ss()) [ref_inv_def] *)
 (* THEN IMP_RES_TAC ref_inv_hist_def *)
 THEN `?IC'. idcore_step_snd_req ((IM.G (PCG n)).C (PCC n),r,IC')
    /\ ((idcore_abs IC').PC = (refcore_abs C').PC)
    /\ ((idcore_abs IC').PSTATE = (refcore_abs C').PSTATE)
    /\ ((idcore_abs IC').GPR = (refcore_abs C').GPR)
    /\ (!R. (idcore_abs IC').SPR R = (refcore_abs C').SPR (INL R))
    /\ (idcore_int IC' = refcore_int C')` by (
     METIS_TAC [core_send_refined_bisim_axiom]
 )
 THEN IMP_RES_TAC mmu_active_lem 
 THEN UNDISCH_ALL_TAC
 THEN RW_TAC (srw_ss()) [Mode_def, iMode_def, mode_def]
 THEN `r NOTIN ((IM.G (PCG n)).cif (PCC n)).req_rcvd` by ( (* TODO: make lemma *)
          `r NOTIN mmu_req_rcvd (RM.MMU n)` by (
              CCONTR_TAC >>
	      METIS_TAC [mmu_corereq_axiom]
	  ) >>
	  IMP_RES_TAC (mmu_active_lem |> SIMP_RULE std_ss [Mode_def]) >>
	  CCONTR_TAC >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  METIS_TAC [SIM_EXPAND, bisim_mmureq_guest_def, 
		     bisim_mmureq_guest_core_def, 
		     hv_gicd_entry_state_lem |> SIMP_RULE std_ss [Mode_def], 
		     hv_guard_mmu_fault_lem |> SIMP_RULE std_ss [Mode_def]]
      )
 THEN EXISTS_TAC ``IC':idcore``
 THEN FULL_SIMP_TAC (srw_ss()) []
 (* preparation bisim proof *)
 THEN IMP_RES_TAC mmu_corereq_axiom 
 THEN IMP_RES_TAC (idcore_step_axiom // "snd_req")
 THEN THROW_AWAY_TAC ``Y ==> X``
 THEN THROW_AWAY_TAC ``!x:idcore. X``
 THEN FULL_SIMP_TAC (srw_ss()) [SIM_def]
 THEN Cases_on `C`
 THEN RW_TAC (srw_ss()) [] 
 THEN FULL_SIMP_TAC (srw_ss()) [fall_constructors_thm_of ``:BISIM_CLAUSE``, bisim_rel_def]
 (* most cases *)
 THEN EXCEPT_FOR_THESE [``bisim_send_igc _``, ``bisim_gicd_reg _ ``]
      (APPLY_TAC_WITH_THM_FROM_LIST_FOR_FUNC_GOAL bisim_definitions RW_FS_IMPRESS
       THEN (Cases_on `n = c`
             THEN1 (STRONG_FS_TAC bisim_core_definitions
                    THEN RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
                    THEN RES_TAC
                    THEN STRONG_FS_TAC [pend_rpl_def, nuvi_def, nuigc_def, HVabs_def, mode_def, Mode_def, hv_guard_mmu_fault_def, hv_gicd_entry_state_def]
                    THEN REV_FULL_SIMP_TAC arith_ss [])
             THEN STRONG_FS_TAC [HVabs_def, good_proj_axiom]))
 (* special cases: bisim_send_igc and bisim_gicd_reg *)
 THEN APPLY_TAC_WITH_THM_FROM_LIST_FOR_FUNC_GOAL bisim_definitions RW_FS_IMPRESS
 THEN Cases_on `n=0`  
 THEN STRONG_FS_TAC [bisim_send_igc_core_def]
 THEN RW_TAC arith_ss []
 THEN TRY (CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV)) 
 THEN SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) [] 
 THEN STRONG_FS_TAC [nusgi_def, Mode_def]
 THEN METIS_TAC []
);

val bisim_ctx_core_hvc_lem = 
store_thm("bisim_ctx_core_hvc_lem", ``
!RM IM c v C'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ haspoc_exc_conf (RM.C c)
/\ (Mode (RM.C c) = 1)
/\ HVC_next(RM.C c,v)
/\ refcore_step_internal (RM.C c,C')
==>
bisim_ctx_core (idcore_abs ((IM.G (PCG c)).C (PCC c)), 
		refcore_abs C', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC C',c),
	        ectx C',
                refcore_int C',
                idcore_int ((IM.G (PCG c)).C (PCC c))) /\
(Mode C' = 2) /\
(refcore_req_sent (RM.C c) = EMPTY) /\ 
(refcore_req_sent C' = EMPTY) /\ 
(ref_abs_int C' = FLUSHED) /\ 
(refcore_abs (RM.C c)).active /\ (refcore_abs C').active /\
((refcore_abs C').PC = AHV VBAR + 0x400w) /\
((refcore_abs C').H = (refcore_abs (RM.C c)).H) /\
(((refcore_abs C').SPR (INR ESR_EL2)) = 0x5800w:bool[16] @@ v ) /\
(idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = EMPTY) /\ 
~hv_mmu_fault_entry_point (refcore_abs C')
``,
  NTAC 6 STRIP_TAC >>
  `~soft (refcore_abs (RM.C c))` by (
      FULL_SIMP_TAC arith_ss [soft_Mode_lem]
  ) >>
  IMP_RES_TAC refcore_HVC_next_axiom >>
  IMP_RES_TAC refcore_hvc_axiom >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_corereq_guest_def >>
  IMP_RES_TAC bisim_corereq_guest_core_def >>
  IMP_RES_TAC bisim_ctx_def >>
  REV_FULL_SIMP_TAC std_ss [bisim_ctx_core_def, Mode_mode_lem] >>
  `(mode (refcore_abs (RM.C c)) <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) <> 2)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) < 2)` by ( DECIDE_TAC ) >>
  `mode (refcore_abs C') = 2` by ( 
      FULL_SIMP_TAC std_ss [mode_def, MODE_upd_lem]
  ) >>
  IMP_RES_TAC soft_mode_lem >>
  `(mode (refcore_abs C') <> 3)` by ( DECIDE_TAC ) >>
  `~(mode (refcore_abs C') < 2)` by ( DECIDE_TAC ) >>
  FULL_SIMP_TAC std_ss [ectx_def] >>
  `(refcore_abs C').SPR (INR VBAR_EL2) =
   (refcore_abs (RM.C c)).SPR (INR VBAR_EL2)` by (
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC (
  	      SPEC ``INR VBAR_EL2:SPRguest + SPRhyp`` thm
  		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
  ) >>
  `sc C'` by (
      RW_TAC std_ss [sc_def] >> ( Q.UNABBREV_TAC `a` ) 
      >| [(* PC *)
	  IMP_RES_TAC InvR_VBAR_lem >>
	  RW_TAC std_ss []
	  ,
	  (* mode *)
	  ASM_REWRITE_TAC []
	  ,
	  (* ESR *)
	  SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
			  [``INR ESR_EL2:SPRguest + SPRhyp``]) >>
	  REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
	  blastLib.BBLAST_PROVE_TAC
	 ]
  ) >>
  IMP_RES_TAC InvR_VBAR_lem >>
  `AHV VBAR + 1024w IN {AHV VBAR + 1024w; AHV VBAR + 1152w}` by (
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
  ) >>
  RW_TAC std_ss []
  >| [(* VBAR *)
      METIS_TAC [AHV_corollaries, pred_setTheory.IN_INSERT, 
		 pred_setTheory.NOT_IN_EMPTY]
      ,
      (* guest SPRs *)
      DISJ1_TAC >>
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INL r:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
      ,
      (* PC *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC (srw_ss()) [] >>
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INR ELR_EL2:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* PSTATE *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC (srw_ss()) [] >>
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INR SPSR_EL2:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* GPR *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC (srw_ss()) []
      ,
      (* GICD_RS / WS -> contradiction *)
      IMP_RES_TAC good_proj_in_range_impls >>
      IMP_RES_TAC ( InvI_EXPAND ``PCG c`` ) >>
      IMP_RES_TAC inv_good_idcore_int_lem >>
      REV_FULL_SIMP_TAC std_ss [id_abs_int_def] >>
      FULL_SIMP_TAC std_ss []
      ,
      (* ESR_EL2 *)
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INR ESR_EL2:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
      ,
      (* not mmu fault *)
      RW_TAC std_ss [hv_mmu_fault_entry_point_def] >> (
          SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
			  [``INR ESR_EL2:SPRguest + SPRhyp``]) >>
	  REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
	  blastLib.BBLAST_PROVE_TAC
      )          
     ]
);      

val bisim_ctx_core_smc_lem = 
store_thm("bisim_ctx_core_smc_lem", ``
!RM IM c v C'.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ haspoc_exc_conf (RM.C c)
/\ (Mode (RM.C c) = 1)
/\ SMC_next(RM.C c,v)
/\ refcore_step_internal (RM.C c,C')
==>
bisim_ctx_core (idcore_abs ((IM.G (PCG c)).C (PCC c)), 
		refcore_abs C', 
		ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC C',c),
	        ectx C',
                refcore_int C',
                idcore_int ((IM.G (PCG c)).C (PCC c))) /\
(Mode C' = 2) /\
(refcore_req_sent (RM.C c) = EMPTY) /\ 
(refcore_req_sent C' = EMPTY) /\ 
(ref_abs_int C' = FLUSHED) /\ 
(refcore_abs (RM.C c)).active /\ (refcore_abs C').active /\
((refcore_abs C').PC = AHV VBAR + 0x400w) /\
((refcore_abs C').H = (refcore_abs (RM.C c)).H) /\
(((refcore_abs C').SPR (INR ESR_EL2)) = 0x5C00w:bool[16] @@ v ) /\
(idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = EMPTY) /\ 
~hv_mmu_fault_entry_point (refcore_abs C')
``,
  NTAC 6 STRIP_TAC >>
  `~soft (refcore_abs (RM.C c))` by (
      FULL_SIMP_TAC arith_ss [soft_Mode_lem]
  ) >>
  IMP_RES_TAC refcore_SMC_next_axiom >>
  IMP_RES_TAC refcore_smc_axiom >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_corereq_guest_def >>
  IMP_RES_TAC bisim_corereq_guest_core_def >>
  IMP_RES_TAC bisim_ctx_def >>
  REV_FULL_SIMP_TAC std_ss [bisim_ctx_core_def, Mode_mode_lem] >>
  `(mode (refcore_abs (RM.C c)) <> 3)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) <> 2)` by ( DECIDE_TAC ) >>
  `(mode (refcore_abs (RM.C c)) < 2)` by ( DECIDE_TAC ) >>
  `mode (refcore_abs C') = 2` by ( 
      FULL_SIMP_TAC std_ss [mode_def, MODE_upd_lem]
  ) >>
  IMP_RES_TAC soft_mode_lem >>
  `(mode (refcore_abs C') <> 3)` by ( DECIDE_TAC ) >>
  `~(mode (refcore_abs C') < 2)` by ( DECIDE_TAC ) >>
  FULL_SIMP_TAC std_ss [ectx_def] >>
  `(refcore_abs C').SPR (INR VBAR_EL2) =
   (refcore_abs (RM.C c)).SPR (INR VBAR_EL2)` by (
      PAT_X_ASSUM ``!r:SPRguest + SPRhyp. x`` (
          fn thm => ASSUME_TAC (
  	      SPEC ``INR VBAR_EL2:SPRguest + SPRhyp`` thm
  		    )
      ) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
  ) >>
  `sc C'` by (
      RW_TAC std_ss [sc_def] >> ( Q.UNABBREV_TAC `a` ) 
      >| [(* PC *)
	  IMP_RES_TAC InvR_VBAR_lem >>
	  RW_TAC std_ss []
	  ,
	  (* mode *)
	  ASM_REWRITE_TAC []
	  ,
	  (* ESR *)
	  SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
			  [``INR ESR_EL2:SPRguest + SPRhyp``]) >>
	  REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
	  blastLib.BBLAST_PROVE_TAC
	 ]
  ) >>
  IMP_RES_TAC InvR_VBAR_lem >>
  `AHV VBAR + 1024w IN {AHV VBAR + 1024w; AHV VBAR + 1152w}` by (
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INSERT]
  ) >>
  RW_TAC std_ss []
  >| [(* VBAR *)
      METIS_TAC [AHV_corollaries, pred_setTheory.IN_INSERT, 
		 pred_setTheory.NOT_IN_EMPTY]
      ,
      (* guest SPRs *)
      DISJ1_TAC >>
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INL r:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
      ,
      (* PC *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC (srw_ss()) [] >>
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INR ELR_EL2:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* PSTATE *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC (srw_ss()) [] >>
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INR SPSR_EL2:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
      blastLib.BBLAST_PROVE_TAC
      ,
      (* GPR *)
      Q.UNABBREV_TAC `a` >>
      RW_TAC (srw_ss()) []
      ,
      (* GICD_RS / WS -> contradiction *)
      IMP_RES_TAC good_proj_in_range_impls >>
      IMP_RES_TAC ( InvI_EXPAND ``PCG c`` ) >>
      IMP_RES_TAC inv_good_idcore_int_lem >>
      REV_FULL_SIMP_TAC std_ss [id_abs_int_def] >>
      FULL_SIMP_TAC std_ss []
      ,
      (* ESR_EL2 *)
      SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
		      [``INR ESR_EL2:SPRguest + SPRhyp``]) >>
      REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom]
      ,
      (* not mmu fault *)
      RW_TAC std_ss [hv_mmu_fault_entry_point_def] >> (
          SPEC_ASSUM_TAC (``!r:SPRguest + SPRhyp. x``,
			  [``INR ESR_EL2:SPRguest + SPRhyp``]) >>
	  REV_FULL_SIMP_TAC std_ss [exception_hyp_regs_axiom] >>
	  blastLib.BBLAST_PROVE_TAC
      )          
     ]
);      


(* MEDIUM: same step in both models or SMC/HVC entry **GUEST/SWITCH**  *)
val refined_CORE_INTERNAL_sim_step_lem = store_thm("refined_CORE_INTERNAL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,CORE_INTERNAL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  REPEAT STRIP_TAC >>
  Cases_on `Mode (RM'.C n) < 2`
  >| [(* couple with same ideal step *)
      STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC 
          (``INTERNAL (IR_CORE_INTERNAL (PCC n))``, 
	   NoMem, withoutAnnotations) >>
      UNFOLD_IDEAL_TRANS_IN_GOAL_TAC >>
      UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
      RW_TAC std_ss [] >>
      FIRST_EXISTS_TAC ``PCG n`` >>
      IMP_RES_TAC good_proj_in_range_impls >>
      FULL_SIMP_TAC (srw_ss()) [] >>
      SPLIT_EXIST_TAC6 >>
      FULL_SIMP_TAC (srw_ss()) [] >>
      SPLIT_OFF_SIM_FROM_GOAL_TAC 
      >| [(* enabled *)
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  MATCH_MP_TAC ( idcore_step_axiom // "internal_enabled" ) >>
	  IMP_RES_TAC refcore_internal_axiom >>
	  IMP_RES_TAC bisim_guest_mode_lem >>
	  FULL_SIMP_TAC arith_ss [SIM_EXPAND] >>
	  IMP_RES_TAC bisim_corereq_guest_def >>
	  FULL_SIMP_TAC std_ss [bisim_corereq_guest_core_def]
	  ,
	  (* bisim *)
	  FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  `bisim_ctx_core
               (idcore_abs C'',refcore_abs C',
		ctxs (mem_abs RM.m (ADRDS (CTX n))) (sc_done_IGC C',n),
		ectx C',refcore_int C',idcore_int C'') /\
	   (refcore_abs C').active /\
	   (refcore_req_sent C' = refcore_req_sent (RM.C n)) /\
           ((refcore_abs C').H = (refcore_abs (RM.C n)).H) /\
           (idcore_req_sent C'' = idcore_req_sent ((IM.G (PCG n)).C (PCC n))) /\
           (idcore_abs C'').active /\
           ((idcore_abs C'').H = (idcore_abs ((IM.G (PCG n)).C (PCC n))).H) /\
           iMode ((IM.G (PCG n)).C (PCC n)) < 2 /\ iMode C'' < 2` by (
	      METIS_TAC [bisim_core_internal_lem]
	  ) >>
	  `~hv_guard_mmu_fault (HVabs(RM with C := (n =+ C') RM.C,n),n)` by (
              MATCH_MP_TAC hv_guard_mmu_fault_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
          `~hv_gicd_entry_state (HVabs(RM with C := (n =+ C') RM.C,n))` by (
              MATCH_MP_TAC hv_gicd_entry_state_lem >>
	      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  IMP_RES_TAC hv_guard_mmu_fault_lem >>
	  IMP_RES_TAC hv_gicd_entry_state_lem >>
	  (* prove SIM *)
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
          REPEAT STRIP_TAC >> (
	  (* most cases *)
          EXCEPT_FOR ``bisim_send_igc _``
           (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	    FULL_SIMP_TAC (srw_ss()) 
	        (nuigc_def::(bisim_pi_guest_def::bisim_core_definitions)) >>
            TRY (Cases_on `n=c`) >>
            REPEAT IF_CASES_TAC >>    
            FULL_SIMP_TAC (srw_ss()++ARITH_ss) 
	        [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                 HVabs_def, nuvi_def] >>
            REV_FULL_SIMP_TAC arith_ss [] >>
            TRY (INFS_LIMITED_METIS_TAC 1 
	        [PCG_PCC_inj, good_proj_in_range_impls, 
		 Trrpl_eq_rpl_lem, AHV_corollaries]
		)
           ) 
	  ) >>
	  (* send_igc *)
	  MATCH_MP_TAC bisim_send_igc_core_step_lem >>
	  EXISTS_TAC ``RM:refined_model`` >>
	  EXISTS_TAC ``IM:ideal_model`` >>
	  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
              FULL_SIMP_TAC arith_ss [AHV_corollaries]
	  )
	 ]
      ,
      (* SMC or HVC entry *)
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, 
				refined_trans_def, 
				ref_rule_core_internal_def] >>
      `haspoc_exc_conf (RM.C n)` by (
          FULL_SIMP_TAC std_ss [Mode_mode_lem, InvR_haspoc_exc_conf_lem]
      ) >>
      REV_FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      `Mode C' > 1` by ( DECIDE_TAC ) >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      `(?v. HVC_next(RM.C n,v) \/ SMC_next(RM.C n,v)) /\ 
       (Mode (RM.C n) = 1)` by (
          METIS_TAC [refcore_mode_change_axiom, Action_distinct] 
      ) >> ( FULL_SIMP_TAC (srw_ss()) [refcore_step_def] )
      >| [(* HVC *)
	  IMP_RES_TAC bisim_ctx_core_hvc_lem 
	  ,
	  (* SMC *)
	  IMP_RES_TAC bisim_ctx_core_smc_lem 
	 ] >> 
      (* for both cases: *) ( 
          `~hv_guard_mmu_fault 
               (HVabs(RM with C := (n =+ C') RM.C,n),n)` by (
              CCONTR_TAC >>
              FULL_SIMP_TAC std_ss [] >>
              IMP_RES_TAC hv_mmu_fault_entry_point_lem >>
              FULL_SIMP_TAC (srw_ss()) [HVabs_def, 
					combinTheory.APPLY_UPDATE_THM]
          ) >>
          `~hv_gicd_entry_state
               (HVabs(RM with C := (n =+ C') RM.C,n))` by (
              FULL_SIMP_TAC (srw_ss()) [hv_gicd_entry_state_def, HVabs_def, 
          				combinTheory.APPLY_UPDATE_THM] >>
              DISJ2_TAC >>
              DISJ1_TAC >>
              blastLib.BBLAST_PROVE_TAC
          ) >>
          `~hv_guard_gicd_fail
               (HVabs(RM with C := (n =+ C') RM.C,n))` by (
              FULL_SIMP_TAC (srw_ss()) [hv_guard_gicd_fail_def]
          ) >>
     	  (* stuttering ideal step *)
	  EXISTS_TAC ``0`` >>
	  EXISTS_TAC ``IM:ideal_model`` >>
	  RW_TAC std_ss [ideal_model_comp_def] >>
	  (* prove SIM *)
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
          REPEAT STRIP_TAC >> (
	  (* most cases *)
          EXCEPT_FOR ``bisim_send_igc _``
           (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
	    FULL_SIMP_TAC (srw_ss()) 
	        (nuigc_def::(bisim_pi_guest_def::bisim_core_definitions)) >>
            TRY (Cases_on `n=c`) >>
            REPEAT IF_CASES_TAC >>    
            FULL_SIMP_TAC (srw_ss()++ARITH_ss) 
	        [combinTheory.APPLY_UPDATE_THM, mode_def, iMode_def, Mode_def,
                 HVabs_def, nuvi_def] >>
            REV_FULL_SIMP_TAC arith_ss [] >>
            TRY (INFS_LIMITED_METIS_TAC 1 
	        [PCG_PCC_inj, good_proj_in_range_impls, 
		 Trrpl_eq_rpl_lem, AHV_corollaries]
		)
           ) 
	  ) >>
	  (* send_igc *)
	  MATCH_MP_TAC bisim_send_igc_core_step_lem >>
	  EXISTS_TAC ``RM:refined_model`` >>
	  EXISTS_TAC ``IM:ideal_model`` >>
	  RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >> (
              FULL_SIMP_TAC arith_ss [AHV_corollaries]
	  )
      )
     ]
);

(* HARD: lots of cases for GIC replies, no corresponding ideal step *)
val refined_HV_RCV_MRPL_sim_step_lem = store_thm("refined_HV_RCV_MRPL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,HV_RCV_MRPL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  cheat
);

(* EASY: similar steps in both models *)
val refined_HV_SND_ELIST_sim_step_lem = store_thm("refined_HV_SND_ELIST_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,HV_SND_ELIST n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  cheat
);

(* HARD: lots of cases for GIC requests, no corresponding ideal step 
need MMU semantics *)
val refined_HV_SND_MREQ_sim_step_lem = store_thm("refined_HV_SND_MREQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,HV_SND_MREQ n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  cheat
);


(* GICD reply case for refined_HV_INTERNAL *)
val postcond = ``?q.  q IN ((IM.G (PCG n)).cif (PCC n)).rpl_rcvd
                 /\ (Rpl_PAdr q = Agicd)
                 /\ (GICDrpl (mem_abs RM.m (ADRDS GICDRPL)) n = GICDrplconv (PCG n,q))``;

val refined_HV_INTERNAL_GICD_REPLY_READ_lem = store_thm("refined_HV_INTERNAL_GICD_REPLY_READ_lem", ``
!IM RM RM' n.
 (hv_rule (HVabs (RM,n),n,NONE) = HV_GICD_REPLY_READ) ==>
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,HV_INTERNAL n,RM')
==>
?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* split into prestep and common step *)
  POSTCOND_FORWARDSTEP_IDEAL_TAC postcond THENL
  [(* 1. prestep: CIF_RCV_SRPL *)
     SOLO_IDEAL_STEP_TAC (``INTERNAL (IR_CIF_RCV_SRPL (PCC n))``, HarmlessMem, withAnnotations) THEN
     (* 1.1. COUPLING *)
     EXISTS_TAC ``PCG n`` THEN 
     UNFOLD_IDEAL_TRANS_IN_GOAL_TAC THEN
     CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC false THEN     
     HV_RULE_GUARD_TAC THEN
     FULL_SIMP_TAC std_ss [hv_guard_gicd_reply_read_def] THEN
     WITH_SIM_CLAUSE ``BISIM_GICDMSG_REFINED`` (fn t => ASSUME_TAC (SPEC ``n:num`` t)) THEN
     REV_FULL_SIMP_TAC (srw_ss()) [id_pend_rpl_def, HVabs_def, Mode_def, mode_def, AHV_axiom] THENL
     [ALL_TAC, METIS_TAC []] THEN
     IMP_RES_TAC good_proj_in_range_impls THEN
     IMP_RES_TAC (InvG_corollary_by_InvI "mem_rpl_cif_req" |> UNIQUE_REQ) THEN
     SPLIT_EXIST_TAC4 THEN
     NTAC 2 (FIRST_EXISTS_TAC ``q:reply``) THEN
     NTAC 2 (FIRST_EXISTS_TAC ``ReqOf q``) THEN
     FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM] THEN
     SPLIT_OFF_SIM_FROM_GOAL_TAC THENL
     [(* 1.2. EXIST + mem_abs *)
        METIS_TAC [mem_io_fw_axiom, mem_snd_rpl_enabled_axiom, InvG_clause_by_InvI ``IDG_MEMRPL``,
                   Agicd_A_gicper_lem, match_PAdr_eq_lem],
      (* 1.3. BISIM *)
        (* step consequences *)
        IMP_RES_TAC (UNIQUE_REQ mem_io_fw_axiom) THEN
        (* start case distinction *)
        FULL_SIMP_TAC std_ss [SIM_EXPAND] THEN
        REPEAT STRIP_TAC THEN  
        ((* for all cases *)
         FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS THEN
         FULL_SIMP_TAC std_ss bisim_core_definitions THEN
         Cases_on `n=c` THEN
         RW_TAC bool_ss [] THEN
         REV_FULL_SIMP_TAC (srw_ss()) [id_pend_rpl_def, AHV_axiom] THEN
         METIS_TAC [match_PAdr_eq_lem, unique_match_thm, PCG_PCC_inj,
                    arithmeticTheory.GREATER_OR_EQ, mmu_inactive_req_lem, Mode_def])
     ],
   (* >>>>> >>>>> >>>>> >>>>> *)
   (* 2. common step: CORE_RCV_MRPL *)
     SIMP_TAC std_ss [ref_preserves_from_unfold] THEN
     REPEAT STRIP_TAC THEN
     STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_CORE_RCV_MRPL (PCC n))``, NoMem, withAnnotations) THEN
     (* 2.1. COUPLING *)
     FIRST_EXISTS_TAC ``PCG n`` THEN 
     UNFOLD_IDEAL_TRANS_IN_GOAL_TAC THEN
     CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC false THEN 
     IMP_RES_TAC good_proj_in_range_impls THEN     
     HV_RULE_GUARD_TAC THEN
     FULL_SIMP_TAC (srw_ss()) [hv_guard_gicd_reply_read_def] THEN
     IMP_RES_TAC (InvG_clause_by_InvI ``IDG_CIFRPL`` |> UNIQUE_REQ) THEN
     SPLIT_EXIST_TAC4 THEN
     FIRST_EXISTS_TAC ``q:reply`` THEN
     FIRST_EXISTS_TAC ``ReqOf q`` THEN
     FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] THEN
     UNIQUE_REQ_TAC THEN
     SPLIT_OFF_SIM_FROM_GOAL_TAC THENL
      [(* 2.2. EXIST + InvG consequences *)
         METIS_TAC [InvG_clause_by_InvI ``IDG_GOOD_IDCORE``,
                    InvG_clause_by_InvI ``IDG_CIFREQ``,
                    idcore_step_axiom // "rcv_rpl_enabled",
                    pred_setTheory.MEMBER_NOT_EMPTY,
                    arithmeticTheory.LESS_EQ_IFF_LESS_SUC,
                    arithmeticTheory.TWO],
      (* 2.3. BISIM *)
        (* step consequences *)
        IMP_RES_TAC (idcore_step_axiom // "rcv_rpl" |> UNIQUE_REQ) THEN
        IMP_RES_TAC match_PAdr_eq_lem THEN
        REV_FULL_SIMP_TAC (srw_ss()) [HVabs_def] THEN 
        `?R. id_abs_int ((IM.G (PCG n)).C (PCC n)) = GICD_RS R` by 
           METIS_TAC [InvG_clause_by_InvI ``IDG_GOOD_IDCORE``, good_proj_in_range_impls,
                     GICDrplconv_preserves_Rreq_Wreq_lem, Rreq_def, ReqOf_def, Agicd_lem] THEN
        FULL_SIMP_TAC (srw_ss()) [Agicd_lem, HVupd_def, hv_rule_gicd_reply_read_def, LET_DEF, idcore_gicd_rrpl_def] THEN
        REPEAT BasicProvers.VAR_EQ_TAC THEN
        (* start case distinction *)
        FULL_SIMP_TAC std_ss [SIM_EXPAND] THEN
        REPEAT STRIP_TAC THEN  
        (* most cases *)
        EXCEPT_FOR_THESE [``bisim_gicdmsg_refined _``, ``bisim_gicdmsg_ideal _ ``, ``bisim_mmureq_guest _``]
         (TRY (FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS THEN
           FULL_SIMP_TAC (srw_ss()) (nuigc_def::bisim_core_definitions) THEN
           LIMITED_METIS_TAC 1 [match_PAdr_eq_lem, mmu_upd_axiom] THEN
           NO_TAC)) THEN
        (* TODO: 16 clauses left *)
        cheat]
  ]
);


(* possibly the proof of bisim_ctx proof can start with something like:

     FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS THEN
     FULL_SIMP_TAC (srw_ss()) (bisim_core_definitions) THEN
     Cases_on `n=c` THEN    
     FULL_SIMP_TAC (srw_ss()) [mode_refcore_upd_lem2] THEN
     FULL_SIMP_TAC (srw_ss()) [refcore_upd_axiom'] THEN
     REV_FULL_SIMP_TAC (srw_ss()) [] THEN 
     FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
     FULL_SIMP_TAC (srw_ss()) [AHV_axiom, mode_def] THEN
     FULL_SIMP_TAC ((srw_ss())++normalForms.cond_lift_SS) [combinTheory.APPLY_UPDATE_THM] THEN

     CCONTR_TAC THEN
     REV_FULL_SIMP_TAC (srw_ss()) [GSYM AHV_axiom] THEN
     FULL_SIMP_TAC (srw_ss()) [AHV_corollaries] THEN

     TRY (LIMITED_METIS_TAC 1 [PCG_PCC_inj, refcore_upd_axiom]) THEN
     TRY (LIMITED_METIS_TAC 1 [match_PAdr_eq_lem, unique_match_thm, PCG_PCC_inj,
                    arithmeticTheory.GREATER_OR_EQ, mmu_inactive_req_lem, Mode_def,
                     mmu_upd_axiom, refcore_upd_axiom])
*)



(* HARD: lots of cases, but mainly saving/restoring context and boot steps,
no corresponding ideal steps except for launch, fault injection, GICD reply *)
val refined_HV_INTERNAL_sim_step_lem = store_thm("refined_HV_INTERNAL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,HV_INTERNAL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  cheat
);


val mmu_final_bisim_lem = store_thm("mmu_final_bisim_lem", ``
!RM IM n r' MMU' m' cif' im' IM'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.nc
/\ bif_step_snd_req ((IM.G (PCG n)).cif (PCC n),r',cif')
/\ mem_step_rcv_req ((IM.G (PCG n)).m,r',CoreSender (PCC n),im')
/\ mmu_step_snd_req (RM.MMU n, Trreq (PCG n) r', MMU')
/\ mem_step_rcv_req (RM.m, Trreq (PCG n) r', CoreSender n,m')
/\ Mode (RM.C n) < 2
/\ (mmu_abs (RM.MMU n)).active
/\ ((mmu_abs (RM.MMU n)).state r' = FINAL NONE)
/\ ((mmu_abs MMU').state r' = FINAL (SOME (Trreq (PCG n) r')))
/\ IS_SOME (Trans (PCG n) (PAdr r'))
/\ sync_shared_mem_upd_of_guest (IM with G := (PCG n =+ ((IM.G (PCG n)) 
      with <|cif := ((PCC n) =+ cif') (IM.G (PCG n)).cif; m := im'|>)) IM.G,
			         PCG n,IM')  
==>
   ideal_model_comp (IM,SUC 0,IM') 
/\ SIM (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,IM')
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  Q.ABBREV_TAC `G' = (IM.G (PCG n)) 
      with <|cif := ((PCC n) =+ cif') (IM.G (PCG n)).cif; m := im'|> ` >>
  RW_TAC (srw_ss()) []
  >| [(* computation *)
      `id_rule_cif_snd_req (IM.G (PCG n), r', PCC n, G')` by (
          RW_TAC (srw_ss()) [id_rule_cif_snd_req_def, 
			     mem_step_def, bif_step_def] >>
	  METIS_TAC []
      ) >>
      IMP_RES_TAC proj_bound_lem >>
      IMP_RES_TAC init_core_lem >>
      IMP_RES_TAC mmu_golden_conf_lem >>
      IMP_RES_TAC mmu_golden_final_axiom >>
      IMP_RES_TAC Trans_gicd_lem >>
      `ideal_guest_trans (IM.G (PCG n), PCG n, 
			  INTERNAL (IR_CIF_SND_SREQ r' (PCC n)), G')` 
      by (
          RW_TAC (srw_ss()) [ideal_guest_trans_def] >> (
	      METIS_TAC [trans_guest_adr_lem, golden_RO_lem]
	  )
      ) >>
      `comp_rule_internal(IM,IM')` by (
          METIS_TAC [comp_rule_internal_def]
      ) >>
      `ideal_model_trans(IM,C_INTERNAL,IM')` by (
          FULL_SIMP_TAC (srw_ss()) [ideal_model_trans_def]
      ) >>
      `ideal_model_comp(IM,SUC 0,IM')` by (
          METIS_TAC [ideal_model_comp_def]
      ) >>
      FULL_SIMP_TAC arith_ss []
      ,
      (* prove SIM *)
      `(IM with G := (PCG n =+ G') IM.G) = IM'` by (
          `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
          `syncInv (IM with G := (PCG n =+ G') IM.G)` by ( 
              MATCH_MP_TAC syncInv_lem >>
	      HINT_EXISTS_TAC >>
	      RW_TAC (srw_ss()) [] >>
	      IMP_RES_TAC mem_rcv_req_axiom >>
	      Q.UNABBREV_TAC `G'` >>
	      STRONG_FS_TAC [] 
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
      ) >> 
      Q.UNABBREV_TAC `G'` >>
      RW_TAC (srw_ss()) [] >>
      THROW_AWAY_TAC ``sync_shared_mem_upd_of_guest x`` >>
      (* add some context *)
      IMP_RES_TAC mem_rcv_req_axiom >>
      IMP_RES_TAC mmu_send_axiom >> (
          `r'' = r'` by ( METIS_TAC [] ) >>
	  RW_TAC (srw_ss()) [] >>
	  FULL_SIMP_TAC std_ss [MMUstate_distinct] 
      ) >>
      IMP_RES_TAC bif_step_snd_req_def >>
      `~hv_guard_mmu_fault 
           (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n),n)` by (
          MATCH_MP_TAC hv_guard_mmu_fault_lem >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `~hv_gicd_entry_state
           (HVabs (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,n))` by (
          MATCH_MP_TAC hv_gicd_entry_state_lem >>
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      IMP_RES_TAC hv_guard_mmu_fault_lem >>
      IMP_RES_TAC hv_gicd_entry_state_lem >>
      (* show SIM *) 
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >> (
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([]@bisim_core_definitions) >>
      	  `RM.C c = (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>).C c` by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      	  ) >>
      	  TRY ( METIS_TAC [PCG_PCC_inj, hv_gicd_entry_state_eq_lem,
      			   hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
			   hv_mmu_fault_entry_eq_lem,
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   proj_bound_lem, Mode_mode_lem, Mode_arith_lem,
			   nuvi_def, nuigc_def, nusgi_def] ) )
      )
     ]
);


(* MEDIUM: need special case for GICD requests -> no ideal steps
need CIF / MMU coupling, address translation, ISO invariants **GUEST/SWITCH** *)
val refined_MMU_SND_MREQ_sim_step_lem = store_thm("refined_MMU_SND_MREQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,MMU_SND_MREQ n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_mmu_snd_mreq_def, 
		     mmu_step_def, mem_step_def] >>
  Cases_on `(mmu_abs(RM.MMU n)).active`
  >| [ (* MMU active *)
      IMP_RES_TAC mmu_send_axiom
      >| [(* case: final request - couple with ideal request *)
          `r' IN mmu_req_rcvd (RM.MMU n)` by (
              FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def]
          ) >>
          `r' IN ((IM.G (PCG n)).cif (PCC n)).req_rcvd` by (
              FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	      IMP_RES_TAC bisim_mmureq_guest_def >>
	      METIS_TAC [bisim_mmureq_guest_core_def]
          ) >>
	  IMP_RES_TAC mmu_active_mode_lem >>
	  IMP_RES_TAC init_core_lem >>
          IMP_RES_TAC mmu_golden_conf_lem >>
          IMP_RES_TAC mmu_golden_final_axiom >>
          IMP_RES_TAC proj_bound_lem >>
          `xlated(r',r)` by ( METIS_TAC [] ) >>
          `r = Trreq (PCG n) r'` by (
              RW_TAC (srw_ss()) [Trreq_xlated_Trans_lem, 
				 PAdr_def, PAdr_extract_lem]
          ) >>
          (* show pif step exists *)
          `?cif'. bif_step ((IM.G (PCG n)).cif (PCC n),
           			SEND (SREQ r' (CoreSender (PCC n))),cif')` by (
              RW_TAC (srw_ss()) [bif_step_def, bif_step_snd_req_def]
           	  >| [(* r' not sent yet *)
                      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
		      IMP_RES_TAC bisim_mmureq_guest_def >>
		      METIS_TAC [bisim_mmureq_guest_core_def]
           	      ,
           	      (* no reply received yet *)
           	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >> (
           	          `IS_SOME (Trans (PCG n) (Rpl_PAdr q)) /\
           	           Trrpl (PCG n) q IN mmu_rpl_rcvd (RM.MMU n)` by (
			      IMP_RES_TAC bisim_mmureq_guest_def >>
			   METIS_TAC [bisim_mmureq_guest_core_def]
           		  ) >>
           		  CCONTR_TAC >>
           		  FULL_SIMP_TAC std_ss [] >>
           		  IMP_RES_TAC Trans_match_lem >>
           		  METIS_TAC []
           	      )
           	     ]
          ) >>
          (* show mem step exists *)
          `?im'. mem_step ((IM.G (PCG n)).m, 
           		   RCV (SREQ r' (CoreSender (PCC n))), NONE, im')` by (
              RW_TAC (srw_ss()) [mem_step_def] >>
              METIS_TAC [mem_rcv_req_enabled_axiom]
          ) >>
          FULL_SIMP_TAC (srw_ss()) [mem_step_def, bif_step_def] >> (
              (* apply lemma *)
              EXISTS_TAC ``SUC 0`` >>
           	  Q.ABBREV_TAC `IM'' = <|G := (PCG n =+ IM.G (PCG n) with
                  <|cif := (PCC n =+ cif') (IM.G (PCG n)).cif;
		    m := im'|>) IM.G|>` >>
              EXISTS_TAC ``IM'':ideal_model`` >>		     
              MATCH_MP_TAC mmu_final_bisim_lem >>
           	  REPEAT HINT_EXISTS_TAC >>
           	  RW_TAC (srw_ss()) [] >>
           	  (* prove sync is redundant *)
           	  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
           	  `syncInv IM''` by ( 
           	      MATCH_MP_TAC syncInv_lem >>
           	      HINT_EXISTS_TAC >>
           	      RW_TAC (srw_ss()) [] >>
           	      IMP_RES_TAC mem_rcv_req_axiom >>
           	      Q.UNABBREV_TAC `IM''` >>
           	      STRONG_FS_TAC [] 
           	  ) >>
           	  RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
          )
	  ,
	  (* case: translation request - invisible *)
	  `r' IN mmu_req_rcvd (RM.MMU n)` by ( 
	      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def] 
	  ) >>
	  `Mode (RM.C n) < 2` by (
	      CCONTR_TAC >>
	      `Mode (RM.C n) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) >>
	      METIS_TAC [mmu_inactive_lem]
	  ) >>
	  `SIM (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,IM)` by (
	      IMP_RES_TAC invisible_lookup_req_lem
	  ) >>
	  EXISTS_TAC ``0`` >>
	  HINT_EXISTS_TAC >>
	  FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def]
	 ]
      ,
      (* MMU inactive - invisible HV request, TODO: GICD virtualization case *)
      cheat
  ]
);

(* MEDIUM: need special case for GICD requests -> no ideal steps
need CIF / MMU coupling, address translation, ISO invariants *)
val refined_MMU_RCV_MRPL_sim_step_lem = store_thm("refined_MMU_RCV_MRPL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,MMU_RCV_MRPL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_mmu_rcv_mrpl_def, 
		     mmu_step_def, mem_step_def] >>
  `(?r'. match_final (RM.MMU n) (r',r)) \/ 
   (?r'. match_trans (RM.MMU n) (r',r)) 
    /\ ~(?r'. match_final (RM.MMU n) (r',r))` by (
      METIS_TAC [ref_mmu_sent_match_lem]
  ) >| 
      [(* case: match final - distinguish hv steps *)
       FULL_SIMP_TAC (srw_ss()) [match_final_def] >>
       `r'' = q` by ( METIS_TAC [unique_match_thm] ) >>
       RW_TAC (srw_ss()) [] >>
       `inv_good_mmu (RM.MMU n)` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] 
       ) >>
       `r' IN mmu_req_rcvd (RM.MMU n)` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def] 
       ) >>
       Cases_on `PAdr q IN RPAR.Amap (GUEST (PCG n))`
       >| [(* guest step *)
	   `Mode (RM.C n) < 2` by ( IMP_RES_TAC guest_req_mode_lem ) >>
	   IMP_RES_TAC mmu_active_lem >>
	   `r' IN ((IM.G (PCG n)).cif (PCC n)).req_rcvd` by (
               FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	       IMP_RES_TAC bisim_mmureq_guest_def >>
	       FULL_SIMP_TAC std_ss [bisim_mmureq_guest_core_def]
	   ) >>
	   IMP_RES_TAC xlated_mmu_req_lem >> 
	   RW_TAC (srw_ss()) [] >>
           `r' IN ((IM.G (PCG n)).cif (PCC n)).req_sent` by (
               FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	       IMP_RES_TAC bisim_mmureq_guest_def >>
	       FULL_SIMP_TAC std_ss [bisim_mmureq_guest_core_def]
           ) >>
	   `(Trreq (PCG n) r', CoreSender n) IN mem_req_rcvd(RM.m)` by (
               FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
	       IMP_RES_TAC ref_inv_mmureq_def
	   ) >>
	   IMP_RES_TAC good_proj_in_range_impls >>
	   `PAdr r' <> Agicd` by ( METIS_TAC [Trans_axiom] ) >>
	   `(r', CoreSender (PCC n)) IN mem_req_rcvd((IM.G (PCG n)).m)` by (
               FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	       IMP_RES_TAC bisim_memreq_def
	   ) >>
	   `?im' q. mem_step_snd_rpl((IM.G (PCG n)).m, q, 
				     CoreSender (PCC n), im')
		 /\ (r = Trrpl (PCG n) q)` by ( 
               METIS_TAC [id_mem_core_rpl_lem]
	   ) >>
	   RW_TAC (srw_ss()) [] >>
	   `match(r',q)` by (
               IMP_RES_TAC IS_SOME_ATrans_lem >>
	       IMP_RES_TAC ATrans_match_lem
	   ) >>
	   `IS_SOME (Trans (PCG n) (Rpl_PAdr q))` by (
               IMP_RES_TAC match_PAdr_eq_lem >>
	       METIS_TAC []
	   ) >>
	   `?cif'. bif_step_rcv_rpl((IM.G (PCG n)).cif (PCC n), q, cif')` by (
               METIS_TAC [bif_step_rcv_rpl_def]
	   ) >>
	   (* lemma for computation / SIM *)
	   Cases_on `PAdr r' IN A_gicper`
	   >| [(* forwarded IO reply *)
	       METIS_TAC [final_mmu_rpl_fwd_lem]
	       ,
	       (* generated reply *)
	       METIS_TAC [final_mmu_rpl_no_fwd_lem]
	      ]
	   ,
	   (* hypervisor step *)
	   cheat
	  ]
       ,
       (* case: invisible translation *)
       FULL_SIMP_TAC (srw_ss()) [match_trans_def] >>
       `r'' = q` by ( METIS_TAC [unique_match_thm] ) >>
       RW_TAC (srw_ss()) [] >>
       `(mmu_abs(RM.MMU n)).active` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def] >>
	   METIS_TAC []
       ) >>
       `r' IN mmu_req_rcvd (RM.MMU n)` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def] 
       ) >>
       `Mode (RM.C n) < 2` by (
           CCONTR_TAC >>
	   `Mode (RM.C n) >= 2` by ( FULL_SIMP_TAC arith_ss [] ) >>
	   METIS_TAC [mmu_inactive_lem]
       ) >>
       `SIM (RM with <|m := m'; MMU := (n =+ MMU') RM.MMU|>,IM)` by (
           IMP_RES_TAC invisible_lookup_rpl_lem
       ) >>
       EXISTS_TAC ``0`` >>
       HINT_EXISTS_TAC >>
       FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def]
      ]
);

(* EASY: nothing happens **GUEST/SWITCH** *)
val refined_MMU_INTERNAL_sim_step_lem = store_thm("refined_MMU_INTERNAL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,MMU_INTERNAL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* no ideal step *)
  RW_TAC std_ss [] >>
  EXISTS_TAC ``0``>>
  SIMP_TAC std_ss [ideal_model_comp_def] >>
  (* refined semantics *)
  UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC mmu_internal_axiom >>
  (* bisim *)
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >>
  (* all cases *)
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
  TRY (
      FULL_SIMP_TAC (srw_ss()) ([HVabs_def, 
				 combinTheory.APPLY_UPDATE_THM]@bisim_core_definitions) >>
      TRY ( `(mmu_abs(RM.MMU c)).active` by ( METIS_TAC [] ) ) >>
      LIMITED_METIS_TAC 1 []
  )
);

(* EASY: same step in both models, need PIF / SMMU coupling **GUEST/SWITCH** *)
val refined_PER_RCV_DMARPL_sim_step_lem = store_thm("refined_PER_RCV_DMARPL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_RCV_DMARPL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* refined semantics *)
  RW_TAC std_ss [] >>
  CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  FULL_SIMP_TAC (srw_ss()) [per_wrap_step_def, per_step_def] >>
  IMP_RES_TAC per_rcv_dma_axiom >>
  IMP_RES_TAC good_proj_in_range_impls >>
  `(mmu_abs (RM.SMMU n)).active` by METIS_TAC [InvR_EXPAND, ref_inv_smmu_def, per_active_init_guest_lem] >>
  IMP_RES_TAC mmu_reply_lem >|
  [(* 1. NO FAULT *)
   STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_PER_RCV_DMARPL (PPP n))``, NoMem, withoutAnnotations) >>
   (* coupling *)
   UNFOLD_IDEAL_TRANS_IN_GOAL_TAC >>
   RW_TAC std_ss [] >>
   FIRST_EXISTS_TAC ``PPG n`` >>
   IMP_RES_TAC good_proj_in_range_impls >>
   FULL_SIMP_TAC (srw_ss()) [] >>
   SPLIT_EXIST_TAC4 >>
   FIRST_EXISTS_TAC ``r:reply`` >>
   FIRST_EXISTS_TAC ``ReqOf r`` >>
   Q.ABBREV_TAC `Pw' = <|st := P'.st; 
		 IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|>` >>
   FIRST_EXISTS_TAC ``Pw':periph_wrapper`` >>
   `ReqOf q' = Trreq (PPG n) (ReqOf r)` by METIS_TAC [Trreq_xlated_ATrans_lem, ref_inv_hyp_iso_smmu_final_rpl_def, InvR_EXPAND] >>
   `q' = Trrpl (PPG n) r` by METIS_TAC [match_Trrpl_lem] >>
   `IS_SOME (Trans (PPG n) (Rpl_PAdr r))` by METIS_TAC [ATrans_lem, ref_inv_hyp_iso_smmu_final_rpl_def, InvR_EXPAND, match_PAdr_eq_lem] >>
   IMP_RES_SIM_CLAUSE_TAC ``BISIM_PERIPH `` >>
   MATCHING_BY_SIM_CLAUSE ``BISIM_SMMUREQ`` ``_ IN _.rpl_rcvd`` [] >>
   IMP_RES_TAC good_match_lem >>
   FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS, matching_request_set_lem] >>
   IMP_RES_TAC good_proj_in_range_impls >>
   IMP_RES_TAC (InvG_clause_by_InvI ``IDG_PIFRPL`` |> UNIQUE_REQ) >>
   SPLIT_OFF_SIM_FROM_GOAL_TAC >|
   [(* enabled *)
    Q.UNABBREV_TAC `Pw'` >>
    RW_TAC (srw_ss()) [] >>
    METIS_TAC [],
    (* bisim *)
    Q.UNABBREV_TAC `Pw'` >>
    FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
    REPEAT STRIP_TAC >>
    (* all cases *)
    FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
    FULL_SIMP_TAC (srw_ss()) bisim_core_definitions >>
    FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, HVabs_def,
                              hv_guard_mmu_fault_def, hv_gicd_entry_state_def, hv_guard_gicd_fail_def] >>
    INFS_LIMITED_METIS_TAC 1 [PPG_PPP_inj, Trrpl_eq_rpl_lem, good_match_lem]
   ],
   (* 2. FAULT *)
   STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_PIF_FAULT r (PPP n))``, NoMem, withoutAnnotations) >>
   (* coupling *)
   FIRST_EXISTS_TAC ``PPG n`` >>
   UNFOLD_IDEAL_TRANS_IN_GOAL_TAC >>  
   IMP_RES_TAC good_proj_in_range_impls >>   
   FULL_SIMP_TAC (srw_ss()) [] >>
   `r NOTIN ((IM.G (PPG n)).pif (PPP n)).rpl_rcvd` by 
              METIS_TAC  [InvR_EXPAND, ref_inv_hyp_iso_smmu_fault_def,
                         receiverMem_def, UNIQUE_REQ (InvG_clause_by_InvI ``IDG_PIFRPL``), good_proj_axiom] >>
   FULL_SIMP_TAC (srw_ss()) [] >>
   IMP_RES_TAC good_match_lem >>
   FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS, matching_request_set_lem] >>
   Q.ABBREV_TAC `Pw' = <|st := P'.st; 
		 IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|>` >>
   FIRST_EXISTS_TAC ``Pw':periph_wrapper`` >>
   FIRST_EXISTS_TAC ``ReqOf r`` >>
   FIRST_EXISTS_TAC ``ReqOf r`` >>
   IMP_RES_SIM_CLAUSE_TAC ``BISIM_PERIPH `` >>
   FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS, Rpl_PAdr_ReqOf_lem] >>
   SPLIT_EXIST_TAC3 >|
   [(* address violating policy *)
    UNIQUE_REQ_TAC >>
    FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, ref_inv_hyp_iso_smmu_fault_def] >>
    METIS_TAC [],
    (* step exists *)
    Q.UNABBREV_TAC `Pw'` >>
    RW_TAC (srw_ss()) [],
    (* IOreq_rcvd perserved *)
    Q.UNABBREV_TAC `Pw'` >>
    RW_TAC (srw_ss()) [],
    (* request received by PIF *)
    Q.UNABBREV_TAC `Pw'` >>
    RW_TAC (srw_ss()) [] >>
    METIS_TAC [good_proj_axiom, InvG_clause_by_InvI ``IDG_PIFREQ``],
    (* golden_fi *)
    IMP_RES_TAC Frpl_match_lem >>
    IMP_RES_TAC smmu_golden_conf_lem >>
    IMP_RES_TAC mmu_golden_fault_FAR_axiom >>
    FULL_SIMP_TAC std_ss [fiOf_def, golden_RO_lem, receiverMem_def] >>
    METIS_TAC [fiOf_def],
    (* request not forwarded by PIF *)
    METIS_TAC [InvR_EXPAND,
               ref_inv_hyp_iso_smmu_fault_def,
               receiverMem_def,
               good_proj_axiom,
               InvG_clause_by_InvI ``IDG_PIFADR``,
               GSYM match_ReqOf_lem],
    (* bisim *)
    Q.UNABBREV_TAC `Pw'` >>
    FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
    REPEAT STRIP_TAC >>
    ((* all cases *)
     FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
     FULL_SIMP_TAC (srw_ss()) bisim_core_definitions >>
     FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, HVabs_def,
                               hv_guard_mmu_fault_def, hv_gicd_entry_state_def, hv_guard_gicd_fail_def] >>
     INFS_LIMITED_METIS_TAC 1 [PPG_PPP_inj])
   ]
  ]
);

(* EASY: same step in both models, **GUEST/SWITCH**
need memory coupling for request and 1-to-1 address translation *)
val refined_PER_RCV_IOREQ_sim_step_lem = store_thm("refined_PER_RCV_IOREQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_RCV_IOREQ n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_per_rcv_ioreq_def] >>
  Q.ABBREV_TAC `RM' = <|m := m'; P := (n =+ P') RM.P|>` >>
  (* forwarded IO request *)
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, per_wrap_step_def, per_step_def] >>
  IMP_RES_TAC mem_snd_req_axiom >>
  IMP_RES_TAC mem_req_rcvd_lem >>
  (* mem step *)
  IMP_RES_TAC pproj_bound_lem >>
  `PAdr r IN PAR.A_gp (PPG n) (PPP n)` by (
      FULL_SIMP_TAC std_ss [coupling_axiom]
  ) >>
  `?r'. PAdr r' IN PAR.A_G (PCG c) /\ (r = Trreq (PCG c) r') /\
        (PCG c = PPG n) /\ PAdr r' IN PAR.A_gp (PPG n) (PPP n)` by (
      METIS_TAC [mmu_sent_per_req_lem]
  ) >>
  Q.ABBREV_TAC `GuestIndex = (PCG c = PPG n)` >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC proj_bound_lem >>
  IMP_RES_TAC pproj_bound_lem >>
  `PAdr r' <> Agicd` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [SYM Agicd_in_GICD_lem] >>
      `PAdr r' IN RPAR.Amap (PER n)` by (
          METIS_TAC [coupling_axiom]
      ) >>
      `gicAR GICD` by ( REWRITE_TAC [gicAR_def] ) >>
      IMP_RES_TAC GICaddresses_lem >>
      `PAdr r' IN RPAR.Amap GICD INTER RPAR.Amap (PER n)` suffices_by (
          FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INTER]
  ) >>
  `IS_SOME (Trans (PCG c) (PAdr r'))` by ( IMP_RES_TAC guest_adr_trans_lem ) >>
  `(r', CoreSender (PCC c)) IN mem_req_rcvd (IM.G (PCG c)).m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `(r', CoreSender (PCC c)) NOTIN mem_req_sent (IM.G (PCG c)).m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `(!q. (q,CoreSender (PCC c)) IN mem_rpl_rcvd (IM.G (PCG c)).m ==> 
	~match (r',q))` by (
      REPEAT STRIP_TAC >>
      `Rpl_PAdr q <> Agicd` by ( METIS_TAC [match_PAdr_eq_lem] ) >>
      `(Trrpl (PCG c) q,CoreSender c) IN mem_rpl_rcvd RM.m` by (
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
          METIS_TAC [bisim_memreq_def]
      ) >>
      IMP_RES_TAC match_IS_SOME_Trans_lem >>
      `match (Trreq (PCG c) r',Trrpl (PCG c) q)` by (
          IMP_RES_TAC Trans_match_lem
      ) >>
      RES_TAC
  ) >>
  `PAdr r' IN A_gicper` by ( METIS_TAC [not_A_gicper_Trreq_lem] ) >>
  `?im'. mem_step_snd_req ((IM.G (PPG n)).m,r',CoreSender (PCC c),im')` by (
      METIS_TAC [mem_snd_req_enabled_axiom]
  ) >>
  (* peripheral step *)
  `IS_SOME (Trans (PPG n) (PAdr r'))` by ( METIS_TAC [] ) >>
  Q.UNABBREV_TAC `GuestIndex` >>
  Q.ABBREV_TAC `Pw' = <|st := P'.st; 
                IOreq_rcvd := (r' =+ SOME (CoreSender (PCC c)))
				  ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|>` >>
  FULL_SIMP_TAC std_ss [] >>
  `per_step_rcv_req (((IM.G (PPG n)).P (PPP n)).st,r', P'.st)` by (
      IMP_RES_TAC Trreq_per_lem >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  (* ideal model step *)
  `id_rule_per_rcv_ioreq(IM.G (PPG n), r', PPP n, PPG n, 
			 IM.G (PPG n) with <|m := im'; 
			   P := (PPP n =+ Pw') (IM.G (PPG n)).P|>)` by (
      RW_TAC std_ss [id_rule_per_rcv_ioreq_def] >>
      EXISTS_TAC ``im':memory`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``PCC c`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC (srw_ss()) [mem_step_def, per_wrap_step_def, per_step_def] >>
      METIS_TAC []
  ) >>
  `ideal_guest_trans(IM.G (PPG n), PPG n, 
		     INTERNAL (IR_PER_RCV_IOREQ r' (PPP n)), 
		     IM.G (PPG n) with <|m := im'; 
			   P := (PPP n =+ Pw') (IM.G (PPG n)).P|>)` by (
      RW_TAC (srw_ss()) [ideal_guest_trans_def]
  ) >>
  Q.ABBREV_TAC `G' = IM.G (PPG n) with <|m := im'; 
		        P := (PPP n =+ Pw') (IM.G (PPG n)).P|>` >>
  Q.ABBREV_TAC `IM' = IM with G := (PPG n =+ G') IM.G` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv <|G := (PPG n =+ G') IM.G|>` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `G'` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
      IMP_RES_TAC mem_snd_req_axiom >>
      ASM_REWRITE_TAC []
  ) >>
  `sync_shared_mem_upd_of_guest(<|G := (PPG n =+ G') IM.G|>,PPG n,IM')` by (
      FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
      Q.UNABBREV_TAC `IM'` >>
      RW_TAC (srw_ss()) []
  ) >>
  `ideal_model_comp (IM,SUC 0,IM')` by (
      RW_TAC std_ss [ideal_model_comp_def] >>
      EXISTS_TAC ``C_INTERNAL`` >>
      RW_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def] >>
      EXISTS_TAC ``PPG n`` >>
      EXISTS_TAC ``IR_PER_RCV_IOREQ r' (PPP n)`` >>
      EXISTS_TAC ``G':guest`` >>
      ASM_REWRITE_TAC []
  ) >>
  (* same step executed, apply step and bisim axioms *)
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  (* add some contect about result *)
  IMP_RES_TAC mem_snd_req_axiom >>
  (* prove SIM *)
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `G'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|m := m'; P := (n =+ P') RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem, Trreq_per_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem, PSI_def] ) )
  )
);

(* EASY: same step in both models, need E_in coupling **GUEST/SWITCH** *)
(* TODO: I guess the transition systems needs to be adapted,
         since no peripheral should receive the entire E_in-list, should it? *)
val refined_PER_RCV_PEV_sim_step_lem = store_thm("refined_PER_RCV_PEV_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_RCV_PEV n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* coupling*)
  RW_TAC std_ss [] >>
  STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC 
      (``INTERNAL (IR_PER_RCV_PEV (PPP n))``, NoMem, withoutAnnotations) >>
  CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  FULL_SIMP_TAC (srw_ss()) [per_wrap_step_def, per_step_def] >>
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_rcv_pev_def,
  		     per_wrap_step_def, per_step_def] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] >>
  FIRST_EXISTS_TAC ``PPG n`` >>
  FIRST_EXISTS_TAC ``<|st := P'.st; 
    IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|> :periph_wrapper`` >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_PERIPH `` >>
  IMP_RES_TAC good_proj_in_range_impls >>
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_EXT `` >>
  `!e. MEM e RM.E_in ==> evper e < RPAR.np` by ( 
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      METIS_TAC [ref_inv_E_in_def] 
  ) >>
  FULL_SIMP_TAC (srw_ss()) [PEF_lem] >>
  (* bisim *)
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS 
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|P := (n =+ P') RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem] ) )
  )
);

(* EASY: same step in both models, need to show  PIF / SMMU coupling **GUEST/SWITCH** *)
val refined_PER_SND_DMAREQ_sim_step_lem = store_thm("refined_PER_SND_DMAREQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_SND_DMAREQ n,RM')
==>
?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* focus on existence of guest transition and bisim - leave trivia to tactic *)
  RW_TAC (srw_ss()) [] >>
  STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC 
      (``INTERNAL (IR_PER_SND_DMAREQ (PPP n))``, NoMem, withAnnotations) >>
  (* coupling: don't split goals before main witnesses provided.
     Normally we could then split with SPLIT_OFF_SIM_FROM_GOAL_TAC,
     but in this case we need to hold on until core_send_refined_bisim_axiom
     has provided extra assertions *)
  UNFOLD_IDEAL_TRANS_IN_GOAL_TAC >>
  UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  RW_TAC std_ss [] >>
  SPLIT_EXIST_TAC6 >>
  TYPE_REORDER_EXISTS_TAC ``:request`` >>
  TYPE_REORDER_EXISTS_TAC ``:num`` >>
  EXISTS_TAC ``PPG n`` >>
  EXISTS_TAC ``r:request`` >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  (* existential proof *)
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC pproj_bound_lem >>
  `per_step_snd_req(((IM.G (PPG n)).P (PPP n)).st, r, P'.st)` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  `(mmu_abs(RM.SMMU n)).active` by ( IMP_RES_TAC smmu_per_active_lem ) >>
  IMP_RES_TAC mmu_corereq_axiom >>
  REV_FULL_SIMP_TAC std_ss [] >>
  `r NOTIN ((IM.G (PPG n)).pif (PPP n)).req_rcvd` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_smmureq_def]
  ) >>
  EXISTS_TAC ``<|st := P'.st; 
    IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|> :periph_wrapper`` >>
  FULL_SIMP_TAC std_ss [] >>
  (* bisim proof *)
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|SMMU := (n =+ SMMU') RM.SMMU; 
			       P := (n =+ P') RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem] ) )
  )
);

(* EASY: same step in both models, need to show memory coupling **GUEST/SWITCH** *)
val refined_PER_SND_IORPL_sim_step_lem = store_thm("refined_PER_SND_IORPL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_SND_IORPL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_per_snd_iorpl_def] >>
  Q.ABBREV_TAC `RM' = <|m := m'; P := (n =+ P') RM.P|>` >>
  (* forwarded IO request *)
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, per_wrap_step_def, per_step_def] >>
  IMP_RES_TAC mem_rcv_rpl_axiom >>
  `r' = q` by ( METIS_TAC [unique_match_thm] ) >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC mem_req_sent_lem >>
  IMP_RES_TAC mem_req_rcvd_lem >>
  (* mem step *)
  IMP_RES_TAC pproj_bound_lem >>
  IMP_RES_TAC per_snd_iorpl_axiom >>
  `r' = q` by ( METIS_TAC [unique_match_thm] ) >>
  RW_TAC std_ss [] >>
  `PAdr q IN RPAR.Amap (PER n)` by (
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >>
      `?s. (RM.P n).IOreq_rcvd q = SOME s` by (
          METIS_TAC [inv_good_per_wrap_def, optionTheory.IS_SOME_EXISTS]
      ) >>
      METIS_TAC [ref_inv_perreq_def, PAdr_def]
  ) >>
  `PAdr q IN PAR.A_gp (PPG n) (PPP n)` by (
      FULL_SIMP_TAC std_ss [coupling_axiom]
  ) >>
  `?q'. PAdr q' IN PAR.A_G (PCG c) /\ (q = Trreq (PCG c) q') /\
        (PCG c = PPG n) /\ PAdr q' IN PAR.A_gp (PPG n) (PPP n) /\ 
	(mmu_abs (RM.MMU c)).active` by (
      METIS_TAC [mmu_sent_per_req_lem]
  ) >>
  Q.ABBREV_TAC `GuestIndex = (PCG c = PPG n)` >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC proj_bound_lem >>
  `PAdr q' <> Agicd` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [SYM Agicd_in_GICD_lem] >>
      `PAdr q' IN RPAR.Amap (PER n)` by (
          METIS_TAC [coupling_axiom]
      ) >>
      `gicAR GICD` by ( REWRITE_TAC [gicAR_def] ) >>
      IMP_RES_TAC GICaddresses_lem >>
      `PAdr q' IN RPAR.Amap GICD INTER RPAR.Amap (PER n)` suffices_by (
          FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INTER]
  ) >>
  `IS_SOME (Trans (PCG c) (PAdr q'))` by ( IMP_RES_TAC guest_adr_trans_lem ) >>
  `(q', CoreSender (PCC c)) IN mem_req_sent (IM.G (PCG c)).m` by (
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_memreq_def]
  ) >>
  `?r'. match (q',r') /\ (r = Trrpl (PCG c) r')` by (
      METIS_TAC [Trrpl_exists_lem]
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  `?im'. mem_step_rcv_rpl ((IM.G (PPG n)).m,r',CoreSender (PCC c),im')` by (
      METIS_TAC [mem_rcv_rpl_enabled_axiom]
  ) >>
  (* peripheral step *)
  `IS_SOME (Trans (PPG n) (PAdr q'))` by ( METIS_TAC [] ) >>
  Q.UNABBREV_TAC `GuestIndex` >>
  FULL_SIMP_TAC std_ss [] >>
  `per_step_snd_rpl (((IM.G (PPG n)).P (PPP n)).st,r', P'.st)` by (
      IMP_RES_TAC Trrpl_per_lem >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      METIS_TAC [bisim_periph_def]
  ) >>
  (* ideal model step *)
  Q.ABBREV_TAC `Pw' = <|st := P'.st;
    IOreq_rcvd := (ReqOf r' =+ NONE) ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|>` >>
  `id_rule_per_snd_iorpl(IM.G (PPG n), PPP n, PPG n, 
			 IM.G (PPG n) with <|m := im'; 
			   P := (PPP n =+ Pw') (IM.G (PPG n)).P|>)` by (
      RW_TAC std_ss [id_rule_per_snd_iorpl_def] >>
      EXISTS_TAC ``r':reply`` >>
      EXISTS_TAC ``im':memory`` >>
      EXISTS_TAC ``Pw':periph_wrapper`` >>
      EXISTS_TAC ``PCC c`` >>
      EXISTS_TAC ``q':request`` >>
      Q.UNABBREV_TAC `Pw'` >>
      RW_TAC std_ss [mem_step_def, per_wrap_step_def, per_step_def] >> (
          METIS_TAC []
      )
  ) >>
  `ideal_guest_trans(IM.G (PPG n), PPG n, 
		     INTERNAL (IR_PER_SND_IORPL (PPP n)), 
		     IM.G (PPG n) with <|m := im'; 
			   P := (PPP n =+ Pw') (IM.G (PPG n)).P|>)` by (
      RW_TAC (srw_ss()) [ideal_guest_trans_def]
  ) >>
  Q.ABBREV_TAC `G' = IM.G (PPG n) with <|m := im'; 
		        P := (PPP n =+ Pw') (IM.G (PPG n)).P|>` >>
  Q.ABBREV_TAC `IM' = IM with G := (PPG n =+ G') IM.G` >>
  `syncInv IM` by ( FULL_SIMP_TAC std_ss [InvI_def] ) >> 
  `syncInv <|G := (PPG n =+ G') IM.G|>` by (
      MATCH_MP_TAC syncInv_lem >>
      HINT_EXISTS_TAC >>
      Q.UNABBREV_TAC `G'` >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      FULL_SIMP_TAC (srw_ss()) [mem_step_def] >>
      IMP_RES_TAC mem_rcv_rpl_axiom >>
      ASM_REWRITE_TAC []
  ) >>
  `sync_shared_mem_upd_of_guest(<|G := (PPG n =+ G') IM.G|>,PPG n,IM')` by (
      FULL_SIMP_TAC std_ss [sync_shared_mem_upd_of_guest_def] >>
      Q.UNABBREV_TAC `IM'` >>
      RW_TAC (srw_ss()) []
  ) >>
  `ideal_model_comp (IM,SUC 0,IM')` by (
      RW_TAC std_ss [ideal_model_comp_def] >>
      EXISTS_TAC ``C_INTERNAL`` >>
      RW_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def] >>
      EXISTS_TAC ``PPG n`` >>
      EXISTS_TAC ``IR_PER_SND_IORPL (PPP n)`` >>
      EXISTS_TAC ``G':guest`` >>
      ASM_REWRITE_TAC []
  ) >>
  (* same step executed, apply step and bisim axioms *)
  EXISTS_TAC ``SUC 0`` >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  (* add some contect about result *)
  IMP_RES_TAC mem_rcv_rpl_axiom >>
  `r'' = q'` by ( METIS_TAC [unique_match_thm] ) >>
  `r''' = Trreq (PPG n) q'` by ( METIS_TAC [unique_match_thm] ) >>
  RW_TAC std_ss [] >>
  `IS_SOME (Trans (PPG n) (Rpl_PAdr r'))` by (
      IMP_RES_TAC match_IS_SOME_Trans_lem
  ) >>
  `Mode (RM.C c) < 2` by (
      MATCH_MP_TAC mmu_active_mode_lem >>
      METIS_TAC [mmu_sent_rcvd_lem]
  ) >>
  (* prove SIM *)
  Q.UNABBREV_TAC `Pw'` >>
  Q.UNABBREV_TAC `G'` >>
  Q.UNABBREV_TAC `IM'` >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|m := m'; P := (n =+ P') RM.P|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( Cases_on `c' = c` ) >> 
      TRY ( INFS_LIMITED_METIS_TAC 1 [pend_rpl_add_lem, 
				      id_pend_rpl_add_lem, 
				      pend_rpl_add_other_guest_lem] ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, PSI_def,
		       id_pend_rpl_add_lem, pend_rpl_add_lem,
		       pend_rpl_add_other_guest_lem, 
		       hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem, Trrpl_per_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem, Mode_arith_lem, 
		       nuvi_guest_mode_lem, nuvi_other_core_reply_lem,
		       nuigc_guest_mode_lem, nuigc_other_core_reply_lem,
		       nusgi_guest_mode_lem, nusgi_other_core_reply_lem] ) )
  )
);


(* EASY: same step in both models, need to show E_out coupling **GUEST/SWITCH** *)
val refined_PER_SND_PEV_sim_step_lem = store_thm("refined_PER_SND_PEV_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_SND_PEV n,RM')
==>
?n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  (* coupling*)
  RW_TAC std_ss [] >>
  STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC 
      (``INTERNAL (IR_PER_SND_PEV (PPP n))``, NoMem, withoutAnnotations) >>
  CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_per_snd_pev_def,
  		    per_step_def] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS, ref_rule_per_snd_pev_def, 
			    per_wrap_step_def, per_step_def] >>
  FIRST_EXISTS_TAC ``l:pevent list`` >>
  FIRST_EXISTS_TAC ``PPG n`` >>
  FIRST_EXISTS_TAC ``<|st := P'.st; 
    IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|> :periph_wrapper`` >>
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_PERIPH `` >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  IMP_RES_TAC good_proj_in_range_impls >>
  IMP_RES_SIM_CLAUSE_TAC ``BISIM_EXT `` >>
  ASM_REWRITE_TAC [] >>
  (* bisim *)
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >> (
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS 
  (* try to solve straight-forward cases *)
  >> (REPEAT IF_CASES_TAC >>
      STRONG_FS_TAC ([]@bisim_core_definitions) >>
      `!c. RM.C c = (RM with <|P := (n =+ P') RM.P; 
			       E_out := RM.E_out ++ l|>).C c` by (
          FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      TRY ( METIS_TAC [PCG_PCC_inj, PPG_PPP_inj, hv_gicd_entry_state_eq_lem,
      		       hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem,
  		       hv_mmu_fault_entry_eq_lem,
      		       Trreq_eq_req_lem, Trrpl_eq_rpl_lem, proj_bound_lem,
  		       pproj_bound_lem, PEL_append_lem, PEL_other_lem] ) )
  )
);


(* MEDIUM: same step in both models, need GIC semantics to show coupling 
**GUEST/SWITCH**  *)
val refined_PER_SND_IRQ_sim_step_lem = store_thm("refined_PER_SND_IRQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_SND_IRQ n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
 (* start with reducing goal to COUPLING, EXIST, and BISIM of one common step *) 
 REPEAT STRIP_TAC
 THEN STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_PER_SND_IRQ irq (PPP n))``, NoMem, withAnnotations)
 THEN UNFOLD_IDEAL_TRANS_IN_GOAL_TAC
 THEN UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true 
 THEN RW_TAC (srw_ss()) []
 (**** COUPLING ****)
 THEN SPLIT_EXIST_TAC6
 THEN TYPE_REORDER_EXISTS_TAC ``:periph_wrapper``
 THEN TYPE_REORDER_EXISTS_TAC ``:num``
 THEN EXISTS_TAC ``PPG n``
 THEN EXISTS_TAC ``q:num``
 THEN EXISTS_TAC ``<|st := P'.st; 
    IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|> :periph_wrapper``
 THEN FULL_SIMP_TAC bool_ss []
 THEN SPLIT_OFF_SIM_FROM_GOAL_TAC
 THENL [(**** EXIST: ideal internal guest step enabled ****)        
         `bisim_rel (RM,BISIM_PERIPH,IM)` by (FULL_SIMP_TAC (srw_ss()) [SIM_def])
        THEN IMP_RES_TAC (bisim_rel_def |> SIMP_RULE bool_ss [bisim_periph_def])
        THEN IMP_RES_TAC good_proj_in_range_impls
        THEN FULL_SIMP_TAC (srw_ss()) []
        THEN LIMITED_METIS_TAC 1 [coupling_axiom, in_PIRQ_lem, idgic_step_axiom // "rcv_irq_enabled"],
        (**** BISIM ****)
        IMP_RES_TAC good_proj_in_range_impls
          (* step consequences *)
        THEN IMP_RES_TAC gic_rcv_irq_axiom
        THEN IMP_RES_TAC (idgic_step_axiom // "rcv_irq")
          (* start case distinction *)
        THEN FULL_SIMP_TAC std_ss [SIM_EXPAND]
        THEN REPEAT STRIP_TAC
        THEN FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
          (* most cases *)
        THEN TRY (REPEAT IF_CASES_TAC
                   THEN FULL_SIMP_TAC (srw_ss()) ([VI_def, HVabs_def, mode_def, Mode_def]@bisim_core_definitions)
                   THEN METIS_TAC [PPG_PPP_inj]
                   THEN NO_TAC)
          (* special cases *)
        THENL [(* bisim_gicd_reg *)
               Cases_on `r`
               THEN FULL_SIMP_TAC (srw_ss()) [req_gicd_VOL_lem]
               THEN IMP_RES_TAC PIRQ_disjoint_lem2
               THEN IMP_RES_TAC (STEP_PREDICATE_FIRST_RULE gic_rcv_irq_bisim_axiom)
               THEN IMP_RES_TAC gic_rcv_irq_gicdfltr_axiom
               THEN FULL_SIMP_TAC (srw_ss()) [req_gicd_VOL_lem]
	       THEN TRY ( IF_CASES_TAC )
	       THEN TRY ( METIS_TAC [GICDreg_distinct] ),
               (* bisim_pi_guest_def *)
               REPEAT IF_CASES_TAC
               THEN FULL_SIMP_TAC std_ss [bisim_pi_guest_def]
               THENL [(* PPG n = g*)
                       GEN_TAC
                        THEN Cases_on `PIR q = q'`
                        THEN IMP_RES_TAC PIR_PQQ_lem
                        THEN REV_FULL_SIMP_TAC std_ss []
                        THEN TRY (LIMITED_METIS_TAC 1 []) 
                        (* and PIR q = q' *)
                        THEN IMP_RES_TAC good_proj_in_range_impls
                        THEN IMP_RES_TAC in_lPIRQ_lem
                        THEN Cases_on `Q RM.GIC (PIR q)`
                        THEN Cases_on `PI (IM.G g).GIC (PIR q)`
                        THEN FULL_SIMP_TAC std_ss []
                        THEN SPEC_ASSUM_TAC (``!q:irqID. X``, [``q':irqID``])
                        THEN REV_FULL_SIMP_TAC (srw_ss()) []
                        THEN LIMITED_METIS_TAC 1 [],
                       (* PPG n <> g *)
                       GEN_TAC
                        THEN Cases_on `PIR q = q'`
                        THEN IMP_RES_TAC PIR_PQQ_lem
                        THEN IMP_RES_TAC PIRQ_disjoint_lem2
                        THEN RW_TAC (srw_ss()++HASPOC_SS) []
                        THEN LIMITED_METIS_TAC 1 []]]]);


(* EASY: same step in both models, nothing else affected 
**GUEST/SWITCH**
*)
val refined_PER_INTERNAL_sim_step_lem = store_thm("refined_PER_INTERNAL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,PER_INTERNAL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
(* start with reducing goal to COUPLING, EXIST, and BISIM of one common step *) 
 REPEAT STRIP_TAC
 THEN STEP'N'COUPLE_IDEAL_ALONG_WITH_REFINED_TAC (``INTERNAL (IR_PER_INTERNAL (PPP n))``, NoMem, withAnnotations)
 THEN UNFOLD_IDEAL_TRANS_IN_GOAL_TAC
 THEN UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true 
 THEN RW_TAC (srw_ss()) []
 (**** COUPLING ****)
 THEN SPLIT_EXIST_TAC6
 THEN TYPE_REORDER_EXISTS_TAC ``:periph_wrapper``
 THEN TYPE_REORDER_EXISTS_TAC ``:num``
 THEN EXISTS_TAC ``PPG n``
 THEN EXISTS_TAC ``<|st := P'.st; 
    IOreq_rcvd := ((IM.G (PPG n)).P (PPP n)).IOreq_rcvd|> :periph_wrapper``
 THEN FULL_SIMP_TAC bool_ss []
 THEN SPLIT_OFF_SIM_FROM_GOAL_TAC
 THENL [(**** EXIST: ideal internal guest step enabled ****)        
         `bisim_rel (RM,BISIM_PERIPH,IM)` by (FULL_SIMP_TAC (srw_ss()) [SIM_def])
        THEN IMP_RES_TAC (bisim_rel_def |> SIMP_RULE bool_ss [bisim_periph_def])
        THEN IMP_RES_TAC good_proj_in_range_impls
        THEN FULL_SIMP_TAC (srw_ss()) [],
        (**** BISIM ****)
        FULL_SIMP_TAC std_ss [SIM_EXPAND]
        THEN REPEAT STRIP_TAC
        THEN FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
        (* all cases *)
        THEN (REPEAT IF_CASES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) (HVabs_def::bisim_core_definitions)
                THEN METIS_TAC [PPG_PPP_inj]
                THEN NO_TAC)]);


(* EASY: same step in both models, need memory coupling **GUEST/SWITCH** *)
val refined_SMMU_RCV_DMARPL_sim_step_lem = store_thm("refined_SMMU_RCV_DMARPL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,SMMU_RCV_DMARPL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_smmu_rcv_dmarpl_def, 
		     mmu_step_def, mem_step_def] >>
  `(?r'. match_final (RM.SMMU n) (r',r)) \/ 
   (?r'. match_trans (RM.SMMU n) (r',r)) 
    /\ ~(?r'. match_final (RM.SMMU n) (r',r))` by (
      METIS_TAC [ref_smmu_sent_match_lem]
  ) >| 
      [(* case: match final - first show existence of steps *)
       FULL_SIMP_TAC (srw_ss()) [match_final_def] >>
       `r'' = q` by ( METIS_TAC [unique_match_thm] ) >>
       RW_TAC (srw_ss()) [] >>
       `inv_good_mmu (RM.SMMU n)` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] 
       ) >>
       `r' IN mmu_req_rcvd (RM.SMMU n)` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def] 
       ) >>
       `per_active (RM.P n).st` by ( IMP_RES_TAC per_active_req_lem ) >>
       `r' IN ((IM.G (PPG n)).pif (PPP n)).req_rcvd` by (
           FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND, bisim_smmureq_def]
       ) >>
       IMP_RES_TAC xlated_smmu_req_lem >> 
       RW_TAC (srw_ss()) [] >>
       `r' IN ((IM.G (PPG n)).pif (PPP n)).req_sent` by (
           FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	   IMP_RES_TAC bisim_smmureq_def
       ) >>
       `(Trreq (PPG n) r', PeripheralSender n) IN mem_req_rcvd(RM.m)` by (
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND] >>
	   IMP_RES_TAC ref_inv_smmureq_def
       ) >>
       `(r', PeripheralSender (PPP n)) IN mem_req_rcvd((IM.G (PPG n)).m)` by (
           FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
	   IMP_RES_TAC bisim_memreq_def
       ) >>
       `?im' q. mem_step_snd_rpl((IM.G (PPG n)).m, q, 
				 PeripheralSender (PPP n), im')
	     /\ (r = Trrpl (PPG n) q)` by ( 
           METIS_TAC [id_mem_rpl_lem]
       ) >>
       RW_TAC (srw_ss()) [] >>
       `match(r',q)` by (
           IMP_RES_TAC pproj_bound_lem >>
           IMP_RES_TAC IS_SOME_ATrans_lem >>
	   IMP_RES_TAC ATrans_match_lem
       ) >>
       `IS_SOME (Trans (PPG n) (Rpl_PAdr q))` by (
           IMP_RES_TAC match_PAdr_eq_lem >>
	   METIS_TAC []
       ) >>
       `?pif'. bif_step_rcv_rpl((IM.G (PPG n)).pif (PPP n), q, pif')` by (
           METIS_TAC [bif_step_rcv_rpl_def]
       ) >>
       (* lemma for computation / SIM *)
       METIS_TAC [final_smmu_rpl_lem]
       ,
       (* case: invisible translation *)
       FULL_SIMP_TAC (srw_ss()) [match_trans_def] >>
       `r'' = q` by ( METIS_TAC [unique_match_thm] ) >>
       RW_TAC (srw_ss()) [] >>
       `r' IN mmu_req_rcvd (RM.SMMU n)` by ( 
           FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def] 
       ) >>
       `per_active (RM.P n).st` by ( IMP_RES_TAC per_active_req_lem ) >>
       `SIM (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>,IM)` by (
           IMP_RES_TAC invisible_smmu_lookup_rpl_lem
       ) >>
       EXISTS_TAC ``0`` >>
       HINT_EXISTS_TAC >>
       FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def]
      ]
);

val smmu_final_bisim_lem = store_thm("smmu_final_bisim_lem", ``
!RM IM n r' SMMU' m' pif' im' IM'.  
   SIM (RM,IM)
/\ InvI IM
/\ InvR RM
/\ n < RPAR.np
/\ bif_step_snd_req ((IM.G (PPG n)).pif (PPP n),r',pif')
/\ mem_step_rcv_req ((IM.G (PPG n)).m,r',PeripheralSender (PPP n),im')
/\ mmu_step_snd_req (RM.SMMU n, Trreq (PPG n) r', SMMU')
/\ mem_step_rcv_req (RM.m, Trreq (PPG n) r', PeripheralSender n,m')
/\ per_active (RM.P n).st
/\ (mmu_abs (RM.SMMU n)).active
/\ ((mmu_abs (RM.SMMU n)).state r' = FINAL NONE)
/\ ((mmu_abs SMMU').state r' = FINAL (SOME (Trreq (PPG n) r')))
/\ IS_SOME (Trans (PPG n) (PAdr r'))
/\ sync_shared_mem_upd_of_guest (IM with G := (PPG n =+ ((IM.G (PPG n)) 
      with <|m := im'; pif := ((PPP n) =+ pif') (IM.G (PPG n)).pif|>)) IM.G,
			         PPG n,IM')  
==>
   ideal_model_comp (IM,1,IM') 
/\ SIM (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>,IM')
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  Q.ABBREV_TAC `G' = (IM.G (PPG n)) 
      with <|m := im'; pif := ((PPP n) =+ pif') (IM.G (PPG n)).pif|> ` >>
  RW_TAC (srw_ss()) []
  >| [(* computation *)
      `id_rule_pif_snd_dmareq (IM.G (PPG n), r', PPP n, G')` by (
          RW_TAC (srw_ss()) [id_rule_pif_snd_dmareq_def, 
			     mem_step_def, bif_step_def] >>
	  METIS_TAC []
      ) >>
      IMP_RES_TAC pproj_bound_lem >>
      IMP_RES_TAC smmu_golden_conf_lem >>
      IMP_RES_TAC mmu_golden_final_axiom >>
      `ideal_guest_trans (IM.G (PPG n), PPG n, 
			  INTERNAL (IR_PIF_SND_DMAREQ r' (PPP n)), G')` 
      by (
          RW_TAC (srw_ss()) [ideal_guest_trans_def] >> (
	      METIS_TAC [trans_guest_adr_lem, Trgip_gicc_lem, Trgip_gicd_lem,
			 golden_RO_lem, Trgip_per_lem]
	  )
      ) >>
      `comp_rule_internal(IM,IM')` by (
          METIS_TAC [comp_rule_internal_def]
      ) >>
      `ideal_model_trans(IM,C_INTERNAL,IM')` by (
          FULL_SIMP_TAC (srw_ss()) [ideal_model_trans_def]
      ) >>
      `ideal_model_comp(IM,SUC 0,IM')` by (
          METIS_TAC [ideal_model_comp_def]
      ) >>
      FULL_SIMP_TAC arith_ss []
      ,
      (* prove SIM *)
      `(IM with G := (PPG n =+ G') IM.G) = IM'` by (
          `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
          `syncInv (IM with G := (PPG n =+ G') IM.G)` by ( 
              MATCH_MP_TAC syncInv_lem >>
	      HINT_EXISTS_TAC >>
	      RW_TAC (srw_ss()) [] >>
	      IMP_RES_TAC mem_rcv_req_axiom >>
	      Q.UNABBREV_TAC `G'` >>
	      STRONG_FS_TAC [] 
	  ) >>
	  FULL_SIMP_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
      ) >> 
      Q.UNABBREV_TAC `G'` >>
      RW_TAC (srw_ss()) [] >>
      THROW_AWAY_TAC ``sync_shared_mem_upd_of_guest x`` >>
      (* add some context *)
      IMP_RES_TAC mem_rcv_req_axiom >>
      IMP_RES_TAC mmu_send_axiom >> (
          `r'' = r'` by ( METIS_TAC [] ) >>
	  RW_TAC (srw_ss()) [] >>
	  FULL_SIMP_TAC std_ss [MMUstate_distinct] 
      ) >>
      IMP_RES_TAC bif_step_snd_req_def >>
      (* use standard tactic *)
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >> 
      REPEAT STRIP_TAC >>
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
	  STRONG_FS_TAC ([]@bisim_core_definitions) >>
	  `!c. RM.C c = (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>).C c` 
	  by (
              FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ) >>
	  TRY ( METIS_TAC [PPG_PPP_inj, hv_gicd_entry_state_eq_lem, 
			   hv_guard_mmu_fault_eq_lem, hv_guard_gicd_fail_lem, 
			   hv_mmu_fault_entry_eq_lem,
			   Trreq_eq_req_lem, pproj_bound_lem] ) ) 
     ]
);


(* MEDIUM: same step in both models, need SMMU / PIF coupling, **GUEST/SWITCH**
need MMU semantics ISO invariants *)
val refined_SMMU_SND_DMAREQ_sim_step_lem = store_thm("refined_SMMU_SND_DMAREQ_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,SMMU_SND_DMAREQ n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_smmu_snd_dmareq_def, 
		     mmu_step_def, mem_step_def] >>
  `per_active (RM.P n).st` by (
      IMP_RES_TAC mmu_send_axiom >> (
          `r' IN mmu_req_rcvd (RM.SMMU n)` by (
	      FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def]
	  ) >>
	  METIS_TAC [per_active_req_lem]
      )
  ) >>
  `(mmu_abs(RM.SMMU n)).active` by ( METIS_TAC [smmu_per_active_lem] ) >>
  IMP_RES_TAC mmu_send_axiom
  >| [(* case: final request - couple with ideal request *)
      `r' IN mmu_req_rcvd (RM.SMMU n)` by (
          FULL_SIMP_TAC (srw_ss()) [InvR_EXPAND, inv_good_mmu_def]
      ) >>
      `r' IN ((IM.G (PPG n)).pif (PPP n)).req_rcvd` by (
          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND, bisim_smmureq_def]
      ) >>
      IMP_RES_TAC smmu_golden_conf_lem >>
      IMP_RES_TAC mmu_golden_final_axiom >>
      IMP_RES_TAC pproj_bound_lem >>
      IMP_RES_TAC Trgip_Trans_lem >>
      `IS_SOME(Trans (PPG n) (PAdr r'))` by (
          FULL_SIMP_TAC (srw_ss()) []
      ) >>
      `xlated(r',r)` by ( METIS_TAC [] ) >>
      `r = Trreq (PPG n) r'` by (
          RW_TAC (srw_ss()) [Trreq_xlated_Trans_lem, PAdr_def, PAdr_extract_lem]
      ) >>
      (* show pif step exists *)
      `?pif'. bif_step ((IM.G (PPG n)).pif (PPP n),
			SEND (SREQ r' (PeripheralSender (PPP n))),pif')` by (
          RW_TAC (srw_ss()) [bif_step_def, bif_step_snd_req_def]
	  >| [(* r' not sent yet *)
              FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND, bisim_smmureq_def]
	      ,
	      (* no reply received yet *)
	      FULL_SIMP_TAC std_ss [SIM_EXPAND] >> (
	          `IS_SOME (Trans (PPG n) (Rpl_PAdr q)) /\
	           Trrpl (PPG n) q IN mmu_rpl_rcvd (RM.SMMU n)` by (
		      METIS_TAC [bisim_smmureq_def]
		  ) >>
		  CCONTR_TAC >>
		  FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC Trans_match_lem >>
		  METIS_TAC []
	      )
	     ]
      ) >>
      (* show mem step exists *)
      `?im'. mem_step ((IM.G (PPG n)).m, 
		       RCV (SREQ r' (PeripheralSender (PPP n))), NONE, im')` by (
          RW_TAC (srw_ss()) [mem_step_def] >>
          METIS_TAC [mem_rcv_req_enabled_axiom]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [mem_step_def, bif_step_def] >> (
          (* apply lemma *)
          EXISTS_TAC ``1`` >>
	  Q.ABBREV_TAC `IM'' = <|G := (PPG n =+ IM.G (PPG n) with
              <|m := im'; pif := (PPP n =+ pif') (IM.G (PPG n)).pif|>) IM.G|>` >>
          EXISTS_TAC ``IM'':ideal_model`` >>		     
          MATCH_MP_TAC smmu_final_bisim_lem >>
	  REPEAT HINT_EXISTS_TAC >>
	  RW_TAC (srw_ss()) [] >>
	  (* prove sync is redundant *)
	  `syncInv IM` by ( FULL_SIMP_TAC (srw_ss()) [InvI_def] ) >>
	  `syncInv IM''` by ( 
	      MATCH_MP_TAC syncInv_lem >>
	      HINT_EXISTS_TAC >>
	      RW_TAC (srw_ss()) [] >>
	      IMP_RES_TAC mem_rcv_req_axiom >>
	      Q.UNABBREV_TAC `IM''` >>
	      STRONG_FS_TAC [] 
	  ) >>
	  RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
      )
      ,
      (* case: invisible translation request *)
      `SIM (RM with <|m := m'; SMMU := (n =+ SMMU') RM.SMMU|>,IM)` by (
          IMP_RES_TAC invisible_smmu_lookup_lem
      ) >>
      EXISTS_TAC ``0`` >>
      HINT_EXISTS_TAC >>
      FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def]
     ]
);

(* EASY: nothing happens **GUEST/SWITCH** *)
val refined_SMMU_INTERNAL_sim_step_lem = store_thm("refined_SMMU_INTERNAL_sim_step_lem", ``
!IM RM RM' n.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,SMMU_INTERNAL n,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
    (* no ideal step *)
  RW_TAC std_ss [] >>
  EXISTS_TAC ``0``>>
  SIMP_TAC std_ss [ideal_model_comp_def] >>
  (* refined semantics *)
  UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC mmu_internal_axiom >>
  (* bisim *)
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  REPEAT STRIP_TAC >>
  (* all cases *)
  FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
  FULL_SIMP_TAC (srw_ss()) ([hv_gicd_entry_state_def, hv_guard_mmu_fault_def,hv_guard_gicd_fail_def,
                             HVabs_def, combinTheory.APPLY_UPDATE_THM]@bisim_core_definitions) >>
  LIMITED_METIS_TAC 1 []
);

val gic_req_not_gicv_no_trans_lem = store_thm("gic_req_not_gicv_no_trans_lem", ``
!r r' a g. 
   g < PAR.ng 
/\ gicAR a 
/\ a <> GICV 
/\ PAdr r IN RPAR.Amap a
/\ (Trreq g r' = r)
==>
~IS_SOME (Trans g (PAdr r'))
``,
  RW_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem, ATrans_def] THEN 
  Cases_on `IS_SOME (Trans g (PAdr r'))` 
  THENL [(* case: prove contradiction *)
         FULL_SIMP_TAC (srw_ss()) [] THEN 
         IMP_RES_TAC gic_trans_lem THEN 
	 `DISJOINT (RPAR.Amap a) (RPAR.Amap GICV)` by (
             MATCH_MP_TAC refined_goodP_axiom_Amap_disjoint THEN
             ASM_SIMP_TAC (srw_ss()) []
         ) THEN
	 METIS_TAC [pred_setTheory.IN_DISJOINT],
	 (* trivial case *)
	 FULL_SIMP_TAC (srw_ss()) []
	]	 
);

val refined_invisible_gic_rcv_lem  = store_thm("refined_invisible_gic_rcv_lem", ``
!RM IM r c m' GIC' a.
   SIM(RM,IM)
/\ InvI IM
/\ InvR RM
/\ gicAR a
/\ a <> GICV
/\ PAdr r IN RPAR.Amap a
/\ c < RPAR.nc
/\ mem_step (RM.m, SEND (SREQ r (CoreSender c)), NONE, m')
/\ gic_step (RM.GIC, RCV (SREQ r (CoreSender c)), GIC')
==>
SIM (RM with <|m := m'; GIC := GIC'|>,IM) 
``,
  RW_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC std_ss [SIM_EXPAND] THEN 
  REPEAT STRIP_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) [mem_step_def, gic_step_def] THEN 
  IMP_RES_TAC mem_snd_req_axiom THEN 
  IMP_RES_TAC gic_rcv_io_axiom THEN 
  EXCEPT_FOR ``bisim_giccreq _`` (
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      THEN (REPEAT IF_CASES_TAC THEN 
	    FULL_SIMP_TAC (srw_ss()) ([HVabs_def, 
				       VI_def, 
				       Q_def, 
				       bisim_pi_guest_def]@bisim_core_definitions) THEN
	    TRY ( METIS_TAC [] ) 
	   )
  ) THEN 
  (* bisim_giccreq cases *)
  TRY (
      FULL_SIMP_TAC std_ss [bisim_giccreq_def] >>
      REPEAT STRIP_TAC >>
      RES_TAC >>
      RW_TAC (srw_ss()) [] >>
      EQ_TAC
      THENL [STRIP_TAC
	     THENL [RES_TAC,
		    `r <> Trreq (PCG c') r'` by (
		        CCONTR_TAC >>
		        FULL_SIMP_TAC std_ss [] >>
		        IMP_RES_TAC proj_bound_lem >>
		        `PAdr r NOTIN RPAR.Amap GICV` by (
		        	  METIS_TAC [gicAR_def, gicAR_disj_lem]
		        ) >>
		        METIS_TAC [gic_trans_lem, Trreq_PAdr_Trans_lem]
		    ) >>
		    FULL_SIMP_TAC std_ss []
		   ],
	     RW_TAC (srw_ss()) []
	    ] >>
      NO_TAC
  ) >>	 
  (* bisim_memreq cases *)
  TRY ( EQ_TAC
	THENL [STRIP_TAC
	       THENL [RES_TAC, 
		      (* `G = a` by ( IMP_RES_TAC gicAR_disj_lem ) THEN  *)
		      `PCG c' < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
		      IMP_RES_TAC gic_req_not_gicv_no_trans_lem],
		RW_TAC (srw_ss()) []]
      )	 
  (* bisim_gicdreq_refined cases *)	
  THEN ( RW_TAC (srw_ss()) []
	 THENL [RES_TAC,
		METIS_TAC [],
 	        `PAdr r IN RPAR.Amap GICD` by (
		    FULL_SIMP_TAC (srw_ss()) [Agicd_lem] ) THEN 
		IMP_RES_TAC GICDreq_mem_lem THEN 
		METIS_TAC [],
		`PAdr r IN RPAR.Amap GICD` by (
		    FULL_SIMP_TAC (srw_ss()) [Agicd_lem] ) THEN 
		IMP_RES_TAC GICDreq_mem_lem THEN 
		METIS_TAC []
	       ]
       )
);


val refined_io_trans_req_lem = store_thm("refined_io_trans_req_lem", ``
!A r g p.
   g < PAR.ng
/\ PAdr (Trreq g r) IN A_gicper
/\ IS_SOME (Trans g (PAdr r))
==>
PAdr r IN A_gicper
``,
  RW_TAC (srw_ss()) [A_gicper_def]  
  THENL[(* case: GIC *)
	IMP_RES_TAC Trreq_PAdr_Trans_lem THEN 
	`gicAR GICV` by ( FULL_SIMP_TAC (srw_ss()) [gicAR_def] ) THEN
        `PAdr r IN RPAR.Amap GICC /\ (THE (Trans g (PAdr r))) IN RPAR.Amap GICV` 
	by (
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    IMP_RES_TAC gic_trans_lem  THEN
	    `gicAR GICV` by ( FULL_SIMP_TAC (srw_ss()) [gicAR_def] ) THEN
	    FULL_SIMP_TAC (srw_ss()) [] ) THEN
        METIS_TAC [gicAR_def],
	(* case: PER *)
	IMP_RES_TAC Trreq_PAdr_Trans_lem THEN 
	`PAR.A_gp (PPG p) (PPP p) = RPAR.Amap (PER p)` by (
	    IMP_RES_TAC coupling_axiom ) THEN
        FULL_SIMP_TAC (srw_ss()) [] THEN
	IMP_RES_TAC per_trans_lem THEN
        METIS_TAC []
       ]	
);


val refined_mem_snd_req_bisim_lem = store_thm("refined_mem_snd_req_bisim_lem", ``
!RM IM r' c m'.
   SIM(RM,IM)
/\ InvI IM
/\ InvR RM
/\ PAdr (Trreq (PCG c) r') IN RPAR.Amap (GUEST (PCG c))
/\ IS_SOME (Trans (PCG c) (PAdr r'))
/\ PAdr r' <> Agicd
/\ c < RPAR.nc
/\ mem_step (RM.m, SEND (SREQ (Trreq (PCG c) r') (CoreSender c)), NONE, m')
==>
?im'. mem_step((IM.G (PCG c)).m, SEND(SREQ r' (CoreSender (PCC c))), NONE, im')
``,
  RW_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC (srw_ss()) [mem_step_def] THEN 
  `PCG c < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  IMP_RES_TAC mem_snd_req_axiom THEN 
  `bisim_rel(RM,BISIM_MEMREQ,IM)` by ( FULL_SIMP_TAC (srw_ss()) [SIM_def] ) THEN
  Q.ABBREV_TAC `X = PAdr (Trreq (PCG c) r') IN RPAR.Amap G UNION RPAR.Amap (PER p)` THEN 
  FULL_SIMP_TAC (srw_ss()) [bisim_rel_def] THEN 
  `(r', CoreSender (PCC c)) IN mem_req_rcvd (IM.G (PCG c)).m` by (
      IMP_RES_TAC bisim_memreq_def ) THEN 
  `(r', CoreSender (PCC c)) NOTIN mem_req_sent (IM.G (PCG c)).m` by (
      IMP_RES_TAC bisim_memreq_def THEN
      METIS_TAC [] ) THEN 
  `PAdr (Trreq (PCG c) r') <> FAULT_ADDRESS` by (
      IMP_RES_TAC guest_req_not_FA_lem ) THEN 
  `ATrans (PCG c) (PAdr r') <> FAULT_ADDRESS` by (
      FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem] ) THEN 
  `!q. match(Trreq (PCG c) r', Trrpl (PCG c) q) ==> (Trrpl (PCG c) q,CoreSender c) NOTIN mem_rpl_rcvd RM.m` by (
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `!q. match(r',q) ==> match(Trreq (PCG c) r', Trrpl (PCG c) q)` by (
      IMP_RES_TAC ATrans_match_lem ) THEN 
  `!q. Rpl_PAdr q <> Agicd ==> (Trrpl (PCG c) q, CoreSender c) NOTIN mem_rpl_rcvd RM.m ==> (q, CoreSender (PCC c)) NOTIN mem_rpl_rcvd (IM.G (PCG c)).m` by (
      IMP_RES_TAC bisim_memreq_def THEN
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `!q. match(r',q) ==> Rpl_PAdr q <> Agicd` by (
      RW_TAC (srw_ss()) [] THEN 
      IMP_RES_TAC match_PAdr_eq_lem THEN
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `!q. match(r',q) ==> (q, CoreSender (PCC c)) NOTIN mem_rpl_rcvd (IM.G (PCG c)).m` by (
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `!q. (q, CoreSender (PCC c)) IN mem_rpl_rcvd (IM.G (PCG c)).m ==> ~match(r',q) ` by (
      GEN_TAC THEN 
      CONV_TAC CONTRAPOS_CONV THEN
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `PAdr r' IN A_gicper` by ( 
      Q.UNABBREV_TAC `X` THEN 
      IMP_RES_TAC refined_io_trans_req_lem THEN
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  METIS_TAC [mem_snd_req_enabled_axiom]
);


val idgic_rcv_io_lem  = store_thm("idgic_rcv_io_lem", ``
!IM r c A.
   gicAR A
/\ PAdr r IN RPAR.Amap A
/\ c < RPAR.nc
==>
?iGIC'.
idgic_step((IM.G (PCG c)).GIC, RCV(SREQ r (CoreSender (PCC c))), 0, iGIC') 
``,
  RW_TAC (srw_ss()) [idgic_step_def] THEN 
  IMP_RES_TAC (idgic_step_axiom // "rcv_req_enabled") THEN 
  FULL_SIMP_TAC (srw_ss()) []
);


val refined_gicv_rcv_req_lem  = store_thm("refined_gicv_rcv_req_lem", ``
!RM IM r c m' GIC'.
   SIM(RM,IM)
/\ InvI IM
/\ InvR RM
/\ PAdr r IN RPAR.Amap GICV
/\ c < RPAR.nc
/\ mem_step (RM.m, SEND (SREQ r (CoreSender c)), NONE, m')
/\ gic_step (RM.GIC, RCV (SREQ r (CoreSender c)), GIC')
==>
?im' iGIC' r'.
   mem_step((IM.G (PCG c)).m, SEND(SREQ r' (CoreSender (PCC c))), NONE, im')
/\ idgic_step((IM.G (PCG c)).GIC, RCV(SREQ r' (CoreSender (PCC c))), 0, iGIC') 
/\ (r = Trreq (PCG c) r') /\ IS_SOME (Trans (PCG c) (PAdr r'))
/\ (PAdr r' IN RPAR.Amap GICC)
``,
  RW_TAC (srw_ss()) [] THEN 
  `PCG c < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  `PAdr r IN RPAR.Amap (GUEST (PCG c))` by ( IMP_RES_TAC gicv_guest_mem_lem ) THEN
  `(r, CoreSender c) IN mem_req_rcvd RM.m` by (
      FULL_SIMP_TAC (srw_ss()) [mem_step_def] THEN 
      IMP_RES_TAC mem_snd_req_axiom ) THEN 
  `?r'. (r = Trreq (PCG c) r') /\ IS_SOME (Trans (PCG c) (PAdr r'))` by (
      IMP_RES_TAC xlated_mem_req_lem THEN 
      HINT_EXISTS_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  IMP_RES_TAC gicv_Trreq_gicc_lem THEN 
  `PAdr r' <> Agicd` by (
      IMP_RES_TAC gic_gicd_disj_lem THEN
      ASSUME_TAC Agicd_lem THEN
      PROVE_TAC [] ) THEN 
  RW_TAC (srw_ss()) [] THEN 
  `?im'. mem_step((IM.G (PCG c)).m, SEND(SREQ r' (CoreSender (PCC c))), NONE, im')` by (
      IMP_RES_TAC refined_mem_snd_req_bisim_lem THEN 
      HINT_EXISTS_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `gicAR GICC` by ( FULL_SIMP_TAC (srw_ss()) [gicAR_def] ) THEN 
  `?iGIC'. idgic_step((IM.G (PCG c)).GIC, RCV(SREQ r' (CoreSender (PCC c))), 0, iGIC')` by (
      IMP_RES_TAC idgic_rcv_io_lem THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  METIS_TAC []
);



val refined_gic_rcv_req_comp_lem  = store_thm("refined_gic_rcv_req_comp_lem", ``
!IM r c m' GIC' im' iGIC' g a.
   InvI IM
/\ g < PAR.ng
/\ c < PAR.nc_g g
/\ (PAdr r IN RPAR.Amap GICC \/ PAdr r IN RPAR.Amap GICD)
/\ mem_step((IM.G g).m, SEND(SREQ r (CoreSender c)), NONE, im')
/\ idgic_step((IM.G g).GIC, RCV(SREQ r (CoreSender c)), 0, iGIC') 
==>
ideal_model_comp (IM,SUC 0,IM with <| G := (g =+ IM.G g with <|m := im'; GIC := iGIC'|>) IM.G |>)
``,
  RW_TAC (srw_ss()) [ideal_model_comp_def]
  THEN EXISTS_TAC ``C_INTERNAL``
  THEN RW_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def]
  THEN HINT_EXISTS_TAC
  THEN EXISTS_TAC ``IR_GIC_RCV_IOREQ r``
  THEN RW_TAC (srw_ss()) [ideal_guest_trans_def, id_rule_gic_rcv_ioreq_def, sync_shared_mem_upd_of_guest_def]
  THEN `syncInv IM` by FULL_SIMP_TAC (srw_ss()) [InvI_def]
  THEN `syncInv (IM with <| G := (g =+ IM.G g with <|m := im'; GIC := iGIC'|>) IM.G |>)` by (
        STRONG_FS_TAC [syncInv_def, mem_step_def]
        THEN IMP_RES_TAC mem_snd_req_axiom
        THEN METIS_TAC [] )
  THEN EXISTS_TAC ``IM.G g with <|m := im'; GIC := iGIC'|>``
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN EXISTS_TAC ``im':memory``
  THEN EXISTS_TAC ``iGIC':idgic``
  THEN EXISTS_TAC ``c:num``
  THEN FULL_SIMP_TAC (srw_ss()) []
);




val refined_gicv_adr_trans_lem = store_thm("refined_gicv_adr_trans_lem", ``
!g r'. g < PAR.ng /\ IS_SOME(Trans g (PAdr r')) ==>
( PAdr (Trreq g r') IN RPAR.Amap GICV
==>
   PAdr r' IN RPAR.Amap GICC)
``,
  RW_TAC std_ss []
  THEN IMP_RES_TAC Trreq_PAdr_Trans_lem
  THEN FULL_SIMP_TAC std_ss []
  THEN IMP_RES_TAC Trans_axiom
);


(* MEDIUM: need to distinguish GICC / GICD / GICH / GICV accesses, 
for most no corresponding ideal step, need address translation for GICV,
need GIC semantics **GUEST/SWITCH**
*)
val refined_GIC_RCV_IOREQ_sim_step_lem = store_thm("refined_GIC_RCV_IOREQ_sim_step_lem", ``
!IM RM RM'.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,GIC_RCV_IOREQ,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_gic_rcv_ioreq_def]
  THEN Cases_on `a = GICV` 
  THENL [(* case GICV *)
	 FULL_SIMP_TAC bool_ss []
	 THEN `?im' iGIC' r'. 
	       mem_step((IM.G (PCG c)).m, SEND(SREQ r' (CoreSender (PCC c))), NONE, im')
            /\ idgic_step((IM.G (PCG c)).GIC, RCV(SREQ r' (CoreSender (PCC c))), 0, iGIC') /\ (r = Trreq (PCG c) r') /\ IS_SOME (Trans (PCG c) (PAdr r'))` by (
	       IMP_RES_TAC refined_gicv_rcv_req_lem 
	       THEN EXISTS_TAC ``im':memory``
	       THEN EXISTS_TAC ``iGIC':idgic``
	       THEN EXISTS_TAC ``r':request``
	       THEN FULL_SIMP_TAC bool_ss [] )
	 THEN `PCG c < PAR.ng` by IMP_RES_TAC good_proj_axiom
	 THEN `PCC c < PAR.nc_g (PCG c)` by IMP_RES_TAC good_proj_axiom
	 THEN `PAdr r' IN RPAR.Amap GICC` by (
	       IMP_RES_TAC refined_gicv_adr_trans_lem 
               THEN FULL_SIMP_TAC std_ss [] )
	 THEN IMP_RES_TAC refined_gic_rcv_req_comp_lem		
	 THEN THROW_AWAY_TAC ``Y ==> X``
	 THEN THROW_AWAY_TAC ``!x:request. X``
         THEN EXISTS_TAC ``SUC 0``
	 THEN HINT_EXISTS_TAC 
	 THEN FULL_SIMP_TAC arith_ss [] 
	 THEN RW_TAC (srw_ss()) []
	 THEN METIS_TAC [refined_gicv_rcv_req_sim_lem],
	 (* case GICC, GICD, GICH *)
         EXISTS_TAC ``0``
         THEN EXISTS_TAC ``IM:ideal_model``
	 THEN RW_TAC bool_ss [ideal_model_comp_def]
         THEN IMP_RES_TAC refined_invisible_gic_rcv_lem
	]
);  



(* HARD: need to distinguish GICC **GUEST/SWITCH** / GICD / GICH / GICV accesses, 
lots of cases
need GIC semantics and establish GICD coupling
*)
val refined_GIC_SND_IORPL_sim_step_lem = store_thm("refined_GIC_SND_IORPL_sim_step_lem", ``
!IM RM RM'.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,GIC_SND_IORPL,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  RW_TAC (srw_ss()) [refined_trans_def, ref_rule_gic_snd_iorpl_def,
		     gic_step_def, mem_step_def] >>
  IMP_RES_TAC good_proj_in_range_impls >>
  Cases_on `Rpl_PAdr r IN RPAR.Amap GICV`
  >| [(* case: GICV access -> translated guest access to GICC,
	       show existence of translated reply first *)
      `PAdr q IN RPAR.Amap GICV` by ( METIS_TAC [match_PAdr_eq_lem] ) >>
      `(q, CoreSender c) IN mem_req_rcvd RM.m` by (
          METIS_TAC [mem_req_sent_lem]
      ) >>
      IMP_RES_TAC gicv_guest_mem_lem >>
      `?ir. (q = Trreq (PCG c) ir) /\ IS_SOME (Trans (PCG c) (PAdr ir))` by (
          METIS_TAC [xlated_mem_req_lem]
      ) >>
      `?iq. r = Trrpl (PCG c) iq` by ( 
          METIS_TAC [match_Trreq_exist_Trrpl_lem]
      ) >>
      IMP_RES_TAC gicv_Trreq_gicc_lem >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC match_Trreq_IS_SOME_rpl_lem >>
      IMP_RES_TAC Trans_match_lem >>
      (* show existence of ideal comp *)
      `?gic' M'. idgic_step_snd_rpl ((IM.G (PCG c)).GIC,
				     iq, CoreSender (PCC c), PCG c, gic')
              /\ mem_step_rcv_rpl ((IM.G (PCG c)).m, iq, 
				   CoreSender (PCC c), M')` by (
          METIS_TAC [refined_gicv_rpl_step_lem]
      ) >> 
      `idgic_step((IM.G (PCG c)).GIC, 
		SEND (SRPL iq (CoreSender (PCC c))), PCG c, gic')` by (
          RW_TAC (srw_ss()) [idgic_step_def]
      ) >>
      `mem_step((IM.G (PCG c)).m, RCV (SRPL iq (CoreSender (PCC c))), NONE, M')` by (
          RW_TAC (srw_ss()) [mem_step_def]
      ) >>
      `PAdr ir <> Agicd` by ( 
          METIS_TAC [singleAR_disj_EXPAND, not_in_GICD_not_Agicd_lem]
      ) >>
      `(ir, CoreSender (PCC c)) IN mem_req_sent (IM.G (PCG c)).m` by (
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
	  METIS_TAC [bisim_memreq_def]
      ) >>
      Q.ABBREV_TAC `G' = (IM.G (PCG c)) with <|m := M'; GIC := gic'|>` >>
      `id_rule_gic_snd_iorpl(IM.G (PCG c), PCG c, G')` by (
          METIS_TAC [id_rule_gic_snd_iorpl_def]
      ) >>
      `ideal_guest_trans(IM.G (PCG c), PCG c, 
			 INTERNAL IR_GIC_SND_IORPL, G')` by (
	  RW_TAC (srw_ss()) [ideal_guest_trans_def]
      ) >>
      Q.ABBREV_TAC `IM' = <|G := (PCG c =+ G') IM.G|>` >>
      `syncInv IM'` by (
	  MATCH_MP_TAC syncInv_lem >>
          IMP_RES_TAC mem_rcv_rpl_axiom >>
	  Q.UNABBREV_TAC `IM'` >>
	  Q.UNABBREV_TAC `G'` >>
	  FULL_SIMP_TAC std_ss [InvI_def] >>
	  HINT_EXISTS_TAC >>
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ) >>
      `sync_shared_mem_upd_of_guest(IM',PCG c,IM')` by (
          RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]
      ) >>
      `comp_rule_internal(IM,IM')` by (
          RW_TAC (srw_ss()) [comp_rule_internal_def] >>
          METIS_TAC []
      ) >>
      `ideal_model_trans(IM, C_INTERNAL, IM')` by (
          RW_TAC (srw_ss()) [ideal_model_trans_def]
      ) >>
      EXISTS_TAC ``SUC 0`` >>
      EXISTS_TAC ``IM':ideal_model`` >>
      `ideal_model_comp(IM,SUC 0, IM')` by (
          METIS_TAC [ideal_model_comp_def] 
      ) >>
      ASM_REWRITE_TAC [] >>
      (* add some context - GIC bisim *)
      `Rpl_PAdr iq IN RPAR.Amap GICC` by ( METIS_TAC [match_PAdr_eq_lem] ) >>
      `(ir,CoreSender (PCC c)) IN idgic_req_rcvd (IM.G (PCG c)).GIC /\ 
       (idgic_req_rcvd gic' = idgic_req_rcvd (IM.G (PCG c)).GIC DIFF
                              {(ir,CoreSender (PCC c))}) /\ 
       (!c'. c' <> (PCC c) ==>
         ((idgic_abs gic').gicc c' = (idgic_abs (IM.G (PCG c)).GIC).gicc c'))` 
      by ( 
          METIS_TAC [idgic_step_axiom // "snd_rpl_gicc", unique_match_thm] 
      ) >>
      `(Trreq (PCG c) ir,CoreSender c) IN gic_req_rcvd RM.GIC /\ 
       (gic_req_rcvd GIC' = gic_req_rcvd RM.GIC DIFF
                            {(Trreq (PCG c) ir,CoreSender c)}) /\ 
       ((gic_abs GIC').gicc = (gic_abs RM.GIC).gicc) /\
       (!c'. c' <> c ==>
         ((gic_abs GIC').gicv c' = (gic_abs RM.GIC).gicv c'))` 
      by ( 
          METIS_TAC [gic_gicv_rpl_axiom, unique_match_thm] 
      ) >>
      (* proof hints *)
      Q.UNABBREV_TAC `G'` >>
      Q.ABBREV_TAC `RM' = RM with <|m := m'; GIC := GIC'|>` >>
      `Mode (RM.C c) < 2` by ( 
          METIS_TAC [gicv_req_mode_lem]
      ) >>
      `bisim_perirq(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_perirq_lem]
      ) >>
      `bisim_sgiirq(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_sgiirq_lem]
      ) >>
      `bisim_igcirq(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_igcirq_lem]
      ) >>
      `bisim_send_igc(RM',IM')` by (
          METIS_TAC [gicv_rpl_bisim_send_igc_lem]
      ) >>
      `bisim_pi(RM',IM')` by ( 
          METIS_TAC [gicv_rpl_bisim_pi_lem]
      ) >>
      `!R c'. c' < RPAR.nc /\ (PCG c' = PCG c) ==> 
	     ((idgic_abs gic').gicc (PCC c') R = (gic_abs GIC').gicv c' R)` by (
          METIS_TAC [gicv_rpl_reg_bisim_lem]
      ) >>
      `bisim_gicd_reg(RM',IM')` by ( 
          METIS_TAC [gicv_rpl_bisim_gicd_reg_lem]
      ) >>
      IMP_RES_TAC mem_rcv_rpl_axiom >>
      `(r' = Trreq (PCG c) ir) /\ (r = ir)` by ( 
          METIS_TAC [unique_match_thm] 
      ) >>      
      RW_TAC (srw_ss()) [] >>
      (* prove SIM *)
      Q.UNABBREV_TAC `RM'` >>
      Q.UNABBREV_TAC `IM'` >>
      FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
      REPEAT STRIP_TAC >>
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS
      (* try to solve straight-forward cases *)
      >> (REPEAT IF_CASES_TAC >>
          STRONG_FS_TAC ([pend_rpl_def, bisim_pi_guest_def,
			  id_pend_rpl_def]@bisim_core_definitions) >>
      	  `!c. (RM with <|m := m'; GIC := GIC'|>).C c = RM.C c`
	  by ( FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] ) >> 
      	  TRY ( TIME_LIMITED_METIS_TAC 1.0 [PCG_PCC_inj, proj_bound_lem,
      			   hv_gicd_entry_state_lem, hv_gicd_entry_state_eq_lem, 
			   hv_guard_mmu_fault_lem, hv_guard_mmu_fault_eq_lem,
			   hv_mmu_fault_entry_eq_lem,
			   hv_guard_gicd_fail_lem,
			   (* HVabs_gic_send_lem,  *)
      			   Trreq_eq_req_lem, Trrpl_eq_rpl_lem,
			   Mode_arith_lem, Mode_ineq_lem] ) )
      ,
      (* case: GICD access -> virtualized by hypervisor *)
      cheat
     ]
);

(* EASY: nothing changes, just don't step the other model here **GUEST/SWITCH** *)
val refined_MEM_INTERNAL_sim_step_lem = store_thm("refined_MEM_INTERNAL_sim_step_lem", ``
!IM RM RM'.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,MEM_INTERNAL,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
   RW_TAC std_ss [] >>
   EXISTS_TAC ``0`` >>
   EXISTS_TAC ``IM:ideal_model`` >>
   RW_TAC std_ss [ideal_model_comp_def] >>
   CAREFUL_UNFOLD_CURRENT_REFINED_TRANS_IN_PREMISES_TAC true >>
   IMP_RES_TAC mem_internal_axiom >>
   FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
   REPEAT STRIP_TAC >>
     ((* all cases *)
      FIND_BISIM_PREDICATES_IN_GOAL_TAC bisim_definitions RW_FS_IMPRESS >>
      FULL_SIMP_TAC (srw_ss()) bisim_core_definitions >>
      FULL_SIMP_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM, HVabs_def] >>
      INFS_LIMITED_METIS_TAC 1 [])
);


val refined_ideal_sim_step_thm = store_thm("refined_ideal_sim_step_thm", ``
!IM RM R RM'.
   SIM (RM, IM) /\ InvI IM /\ InvR RM /\ refined_trans(RM,R,RM')
==>
∃n IM'. ideal_model_comp (IM,n,IM') /\ SIM (RM',IM')
``,
  Cases_on `R`
  THENL [REWRITE_TAC [refined_CORE_RCV_IRQ_sim_step_lem],
	 REWRITE_TAC [refined_CORE_RCV_MRPL_sim_step_lem],
	 REWRITE_TAC [refined_CORE_RCV_EVENT_sim_step_lem],
	 REWRITE_TAC [refined_CORE_SND_MREQ_sim_step_lem],
	 REWRITE_TAC [refined_CORE_INTERNAL_sim_step_lem],
	 REWRITE_TAC [refined_HV_RCV_MRPL_sim_step_lem],
	 REWRITE_TAC [refined_HV_SND_ELIST_sim_step_lem],
	 REWRITE_TAC [refined_HV_SND_MREQ_sim_step_lem],
	 REWRITE_TAC [refined_HV_INTERNAL_sim_step_lem],
	 REWRITE_TAC [refined_MMU_SND_MREQ_sim_step_lem],
	 REWRITE_TAC [refined_MMU_RCV_MRPL_sim_step_lem],
	 REWRITE_TAC [refined_MMU_INTERNAL_sim_step_lem],
	 REWRITE_TAC [refined_PER_RCV_DMARPL_sim_step_lem],
	 REWRITE_TAC [refined_PER_RCV_IOREQ_sim_step_lem],
	 REWRITE_TAC [refined_PER_RCV_PEV_sim_step_lem],
	 REWRITE_TAC [refined_PER_SND_DMAREQ_sim_step_lem],
	 REWRITE_TAC [refined_PER_SND_IORPL_sim_step_lem],
	 REWRITE_TAC [refined_PER_SND_PEV_sim_step_lem],
	 REWRITE_TAC [refined_PER_SND_IRQ_sim_step_lem],
	 REWRITE_TAC [refined_PER_INTERNAL_sim_step_lem],
	 REWRITE_TAC [refined_SMMU_RCV_DMARPL_sim_step_lem],
	 REWRITE_TAC [refined_SMMU_SND_DMAREQ_sim_step_lem],
	 REWRITE_TAC [refined_SMMU_INTERNAL_sim_step_lem],
	 REWRITE_TAC [refined_GIC_RCV_IOREQ_sim_step_lem],
	 REWRITE_TAC [refined_GIC_SND_IORPL_sim_step_lem],
	 REWRITE_TAC [refined_MEM_INTERNAL_sim_step_lem]]
);


val refined_ideal_bisim_thm = store_thm("refined_ideal_bisim_thm", ``
!RM n RM' IM. 
   SIM (RM, IM)
/\ id_start IM
/\ good_refined_comp (RM, n, RM')
==>
?n' IM'. good_ideal_comp(IM, n', IM') /\ SIM (RM', IM') 
``,   
  Induct_on `n`
  THEN1 ( RW_TAC (srw_ss()) [good_refined_comp_def, refined_comp_def]
	  THEN EXISTS_TAC ``0``
	  THEN HINT_EXISTS_TAC
	  THEN RW_TAC (srw_ss()) [good_ideal_comp_def, ideal_model_comp_def]
  )
  THEN RW_TAC (srw_ss()) [good_refined_comp_def, refined_comp_def, good_ideal_comp_def, ideal_model_comp_def]
  THEN IMP_RES_TAC good_refined_comp_def
  THEN IMP_RES_TAC InvR_lem
  THEN RES_TAC
  THEN IMP_RES_TAC InvI_lem
  THEN IMP_RES_TAC good_ideal_comp_def
  THEN IMP_RES_TAC refined_ideal_sim_step_thm
  THEN IMP_RES_TAC ideal_comp_concat_lem
  THEN METIS_TAC []
);



(*************** finish ***********)

val _ = export_theory();
