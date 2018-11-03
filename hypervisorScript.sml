(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 
open axfuncsTheory;

open math_lemmasTheory;
open axtypesTheory;
open haspoctypesTheory;
open parametersTheory;
open axfuncsTheory;
open tacticsLib; 

open annotationsLib; infix //; infix ///; infix -:;

val _ = new_theory "hypervisor";

(*** helper lemmas ***)

(* This is FUN_EQ_THM *)
val lambda_eq_pred_lem = store_thm("lambda_eq_pred_lem", ``
!P Q. ((\x. P x) = (\x. Q x)) ==> (!x. P x = Q x)
``,
  RW_TAC (srw_ss()) [ETA_AX]
);

(* This is EQ_SYM_EQ with negation *)
val NOT_EQ_SYM_RW = store_thm("NOT_EQ_SYM_RW", ``!P Q. (P <> Q) <=> (Q <> P)``,
RW_TAC (srw_ss()) [boolTheory.EQ_IMP_THM]
);

val NO_MEMBER_NOT_EQ_RW = store_thm("NO_MEMBER_NOT_EQ_RW", ``
!x y A. x IN A /\ y NOTIN A ==> x <> y
``,
  PROVE_TAC[]);

val EQ_NEG_RW = store_thm("EQ_NEG_RW", ``!P Q. (P = Q) <=> (~P = ~Q)``, PROVE_TAC[]);

(*** axiomatization ***)

(* Golden Image MMU configuration *)

(* Golden MMU configuration for each guest *)
new_constant("MMU_GI", ``:num -> MMUcfg``);
(* Golden SMMU configuration for each guest *)
new_constant("SMMU_GI", ``:num -> MMUcfg``);


(* Golden Image 2nd stage page tables for each guest *)
val _ = new_constant("GI", ``:num -> bool[36] -> PAGE``);
(* Golden Image SMMU page tables for each guest *)
val _ = new_constant("GIP", ``:num -> bool[36] -> PAGE``);


(* Projections *)

(* refined core to ideal core *)
val _ = new_constant("PCC", ``:num -> num``);
(* refined core to guest *)
val _ = new_constant("PCG", ``:num -> num``);
(* refined peripheral to ideal peripheral *)
val _ = new_constant("PPP", ``:num -> num``);
(* refined peripheral to guest *)
val _ = new_constant("PPG", ``:num -> num``);


val projections_inequal_lem = 
    store_thm("projections_inequal_lem",
    ``   (PCC c1 <> PCC c2 ==> (c1 <> c2))
      /\ (PCG c1 <> PCG c2 ==> (c1 <> c2))
      /\ (PPP p1 <> PPP p2 ==> (p1 <> p2))
      /\ (PPG p1 <> PPG p2 ==> (p1 <> p2))``,
    PROVE_TAC []);

val refined_ipirq_g_def = Define `refined_ipirq_g p g = 
{SGI (id,c,c') | (c, c', id) | 
   c < p.nc /\ (PCG c = g) 
/\ c' < p.nc /\ (PCG c' = g) 
/\ id <=+ 7w }`;

val refined_IPIRQ_g_def = Define `refIPIRQ_g = refined_ipirq_g RPAR`;



(*** projections and bijections as suggested by Thomas Tuerk ***)


val good_proj_axiom_tm = ``
   (!c. c < RPAR.nc ==> PCG c < PAR.ng /\ PCC c < (PAR.nc_g (PCG c)))
/\ (!p. p < RPAR.np ==> PPG p < PAR.ng /\ PPP p < (PAR.np_g (PPG p)))
/\ (!c c'. c < RPAR.nc /\ c' < RPAR.nc /\ c <> c' /\ (PCG c = PCG c') ==> 
						     PCC c <> PCC c')
/\ (!p p'. p < RPAR.np /\ p' < RPAR.np /\ p <> p' /\ (PPG p = PPG p') ==> 
						     PPP p <> PPP p')
/\ (!g cg. g < PAR.ng /\ cg < PAR.nc_g g ==> 
		(?c. c < RPAR.nc /\ (PCG c = g) /\ (PCC c = cg)))
/\ (!g pg. g < PAR.ng /\ pg < PAR.np_g g ==> 
		(?p. p < RPAR.np /\ (PPG p = g) /\ (PPP p = pg)))
``

val good_proj_axiom_alt_def = prove (``^good_proj_axiom_tm <=> (?PCGC_inv PPGP_inv.
      (!g cg. (g < PAR.ng /\ cg < PAR.nc_g g) <=> (PCGC_inv (g, cg) < RPAR.nc)) /\
      (!c. c < RPAR.nc ==> (PCGC_inv (PCG c, PCC c) = c)) /\
      (!g cg. (g < PAR.ng /\ cg < PAR.nc_g g) ==> (PCG (PCGC_inv (g, cg)) = g)) /\
      (!g cg. (g < PAR.ng /\ cg < PAR.nc_g g) ==> (PCC (PCGC_inv (g, cg)) = cg)) /\
      (!g pg. (g < PAR.ng /\ pg < PAR.np_g g) <=> (PPGP_inv (g, pg) < RPAR.np)) /\
      (!p. p < RPAR.np ==> (PPGP_inv (PPG p, PPP p) = p)) /\
      (!g pg. (g < PAR.ng /\ pg < PAR.np_g g) ==> (PPG (PPGP_inv (g, pg)) = g)) /\
      (!g pg. (g < PAR.ng /\ pg < PAR.np_g g) ==> (PPP (PPGP_inv (g, pg)) = pg)))``, 
  Tactical.REVERSE EQ_TAC THEN1 METIS_TAC[] THEN
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `\(g, cg). if ((g < PAR.ng) /\ (cg < PAR.nc_g g)) then 
     (@c. c < RPAR.nc /\ (PCG c = g) /\ (PCC c = cg)) else RPAR.nc` THEN  
  Q.EXISTS_TAC `\(g, pg). 
    if (g < PAR.ng /\ pg < PAR.np_g g) then (@p. p < RPAR.np /\ (PPG p = g) /\ (PPP p = pg)) else RPAR.np` THEN
  SIMP_TAC std_ss [] THEN
  METIS_TAC[prim_recTheory.LESS_REFL])


val good_proj_axiom = new_axiom("good_proj_axiom", good_proj_axiom_tm);

val PCGC_PPGP_inv_def = new_specification ("PCGC_PPGP_inv_def", ["PCGC_inv", "PPGP_inv"],
   CONV_RULE (K good_proj_axiom_alt_def) good_proj_axiom)

val good_proj_in_range_impls = store_thm ("good_proj_in_range_impls",
   ``(!g cg. (g < PAR.ng /\ cg < PAR.nc_g g) ==> (PCGC_inv (g, cg) < RPAR.nc)) /\
     (!g cg. (PCGC_inv (g, cg) < RPAR.nc) ==> g < PAR.ng) /\
     (!g cg. (PCGC_inv (g, cg) < RPAR.nc) ==> cg < PAR.nc_g g) /\
     (!c. c < RPAR.nc ==> PCG c < PAR.ng) /\ 
     (!c. c < RPAR.nc ==> PCC c < (PAR.nc_g (PCG c))) /\
     (!g pg. (g < PAR.ng /\ pg < PAR.np_g g) ==> (PPGP_inv (g, pg) < RPAR.np)) /\
     (!g pg. ((PPGP_inv (g, pg) < RPAR.np) ==> (g < PAR.ng))) /\
     (!g pg. ((PPGP_inv (g, pg) < RPAR.np) ==> (pg < PAR.np_g g))) /\
     (!p. p < RPAR.np ==> PPG p < PAR.ng) /\
     (!p. p < RPAR.np ==> PPP p < (PAR.np_g (PPG p)))``,
   METIS_TAC[PCGC_PPGP_inv_def]);

val PPGP_inv_inj = store_thm ("PPGP_inv_inj",
   ``!g pg g' pg'. (g < PAR.ng /\ pg < PAR.np_g g) /\
                   (g' < PAR.ng /\ pg' < PAR.np_g g') ==>
                   ((PPGP_inv (g, pg) = PPGP_inv (g', pg')) <=>
                    ((g = g') /\ (pg = pg')))``,
   METIS_TAC[PCGC_PPGP_inv_def]);

val PCGC_inv_inj = store_thm ("PCGC_inv_inj",
   ``!g cg g' cg'. (g < PAR.ng /\ cg < PAR.nc_g g) /\
                   (g' < PAR.ng /\ cg' < PAR.nc_g g') ==>
                   ((PCGC_inv (g, cg) = PCGC_inv (g', cg')) <=>
                    ((g = g') /\ (cg = cg')))``,
   METIS_TAC[PCGC_PPGP_inv_def]);

val PCG_PCC_inj = store_thm ("PCG_PCC_inj",
   ``!c c'. c < RPAR.nc /\ c' < RPAR.nc /\ (PCG c = PCG c') /\ (PCC c = PCC c') ==>
            (c = c')``,
   METIS_TAC[PCGC_PPGP_inv_def]);

val PPG_PPP_inj = store_thm ("PPG_PPP_inj",
   ``!p p'. p < RPAR.np /\ p' < RPAR.np /\ (PPG p = PPG p') /\ (PPP p = PPP p') ==>
            (p = p')``,
    METIS_TAC[PCGC_PPGP_inv_def]);

val PCGC_inv_rewrites = store_thm ("PCGC_inv_rewrites",
  ``(!c. c < RPAR.nc ==> (PCGC_inv (PCG c, PCC c) = c)) /\
    (!g cg. (g < PAR.ng /\ cg < PAR.nc_g g) ==> (PCG (PCGC_inv (g, cg)) = g)) /\
    (!g cg. (g < PAR.ng /\ cg < PAR.nc_g g) ==> (PCC (PCGC_inv (g, cg)) = cg)) /\
    (!g cg. (PCGC_inv (g, cg) < RPAR.nc) ==> (PCC (PCGC_inv (g, cg)) = cg)) ``,
   SIMP_TAC std_ss [PCGC_PPGP_inv_def]);


val PPGP_inv_rewrites = store_thm ("PPGP_inv_rewrites",
``(!p. p < RPAR.np ==> (PPGP_inv (PPG p, PPP p) = p)) /\
  (!g pg. (g < PAR.ng /\ pg < PAR.np_g g) ==> (PPG (PPGP_inv (g, pg)) = g)) /\
  (!g pg. (g < PAR.ng /\ pg < PAR.np_g g) ==> (PPP (PPGP_inv (g, pg)) = pg)) /\
  (!g pg. (PPGP_inv (g, pg) < RPAR.np) ==> (PPG (PPGP_inv (g, pg)) = g))``, 
  SIMP_TAC std_ss [PCGC_PPGP_inv_def]);


val _ = export_rewrites ["PPGP_inv_rewrites", "good_proj_in_range_impls",
      "PPGP_inv_inj", "PCGC_inv_rewrites", "PCGC_inv_inj"];

val RPAR_np_alt_def = store_thm ("RPAR_np_alt_def",
  ``RPAR.np = SUM PAR.ng PAR.np_g``,
  Q.ABBREV_TAC `ps = \n. {(g, pg) | g < n /\ (pg < PAR.np_g g)}` THEN
  sg `!n. ps n = BIGUNION (IMAGE (\g. IMAGE (\pg. (g, pg)) (count (PAR.np_g g))) (count n))` THEN1 (
    UNABBREV_ALL_TAC THEN
    ONCE_REWRITE_TAC[pred_setTheory.EXTENSION] THEN
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM]  THEN
    METIS_TAC[]
  ) THEN
  sg `!n. FINITE (ps n)` THEN1 (
    ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.FINITE_BIGUNION_EQ,
      pred_setTheory.IMAGE_FINITE, pred_setTheory.FINITE_COUNT,
      pred_setTheory.IN_IMAGE, GSYM LEFT_FORALL_IMP_THM]
  ) THEN
  Q.SUBGOAL_THEN `RPAR.np = CARD (count RPAR.np)` SUBST1_TAC THEN1 (
    REWRITE_TAC[pred_setTheory.CARD_COUNT]
  ) THEN
  Q.SUBGOAL_THEN `SUM PAR.ng PAR.np_g = CARD (ps PAR.ng)` SUBST1_TAC THEN1 (
    `!n. CARD (ps n) = SUM n PAR.np_g` suffices_by METIS_TAC[] THEN
    Induct THEN (
      ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [sum_numTheory.SUM_def]
    ) THEN
    ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.COUNT_SUC] THEN
    PAT_X_ASSUM ``!n:num. ps n = _`` (ASSUME_TAC o GSYM) THEN 
    ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [
      pred_setTheory.CARD_UNION_EQN, pred_setTheory.FINITE_COUNT,
      pred_setTheory.IMAGE_FINITE] THEN
    sg `IMAGE (\pg. (n,pg)) (count (PAR.np_g n)) INTER (ps n) = {}` THEN1 (
       ONCE_REWRITE_TAC[pred_setTheory.EXTENSION] THEN
       UNABBREV_ALL_TAC THEN
       SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++QI_ss) []
    ) THEN
    sg `CARD (IMAGE (\pg. (n,pg)) (count (PAR.np_g n))) =  PAR.np_g n` THEN1 (
      sg `!s. INJ (\pg:num. (n, pg)) s UNIV` THEN1 (
         SIMP_TAC std_ss [pred_setTheory.INJ_DEF, pred_setTheory.IN_UNIV]
      ) THEN
      ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] THEN
      METIS_TAC [pred_setTheory.INJ_CARD_IMAGE_EQ, pred_setTheory.FINITE_COUNT,
        pred_setTheory.CARD_COUNT]
    ) THEN
    ASM_SIMP_TAC (arith_ss++pred_setLib.PRED_SET_ss) []
  ) THEN
  Q.SUBGOAL_THEN `CARD (ps PAR.ng) = CARD (IMAGE PPGP_inv (ps PAR.ng))` SUBST1_TAC THEN1 ( 
    `INJ PPGP_inv (ps PAR.ng) UNIV` suffices_by METIS_TAC[pred_setTheory.INJ_CARD_IMAGE_EQ] THEN
    UNABBREV_ALL_TAC THEN
    SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INJ_DEF, 
       PPGP_inv_inj, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
       GSYM LEFT_FORALL_IMP_THM]
  ) THEN
  `IMAGE PPGP_inv (ps PAR.ng) = count RPAR.np` suffices_by PROVE_TAC[] THEN
  UNABBREV_ALL_TAC THEN
  SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.EXTENSION,
    GSYM RIGHT_EXISTS_AND_THM] THEN
  METIS_TAC [PCGC_PPGP_inv_def]);


val RPAR_nc_alt_def = store_thm ("RPAR_nc_alt_def",
  ``RPAR.nc = SUM PAR.ng PAR.nc_g``,
 Q.ABBREV_TAC `ps = \n. {(g, pc) | g < n /\ (pc < PAR.nc_g g)}` THEN
 sg `!n. ps n = BIGUNION (IMAGE (\g. IMAGE (\pc. (g, pc)) (count (PAR.nc_g g))) (count n))` THEN1 (
   UNABBREV_ALL_TAC THEN
   ONCE_REWRITE_TAC[pred_setTheory.EXTENSION] THEN
   SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [GSYM RIGHT_EXISTS_AND_THM,
     GSYM LEFT_EXISTS_AND_THM]  THEN
   METIS_TAC[]
 ) THEN
 sg `!n. FINITE (ps n)` THEN1 (
   ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.FINITE_BIGUNION_EQ,
     pred_setTheory.IMAGE_FINITE, pred_setTheory.FINITE_COUNT,
     pred_setTheory.IN_IMAGE, GSYM LEFT_FORALL_IMP_THM]
 ) THEN
 Q.SUBGOAL_THEN `RPAR.nc = CARD (count RPAR.nc)` SUBST1_TAC THEN1 (
   REWRITE_TAC[pred_setTheory.CARD_COUNT]
 ) THEN
 Q.SUBGOAL_THEN `SUM PAR.ng PAR.nc_g = CARD (ps PAR.ng)` SUBST1_TAC THEN1 (
   `!n. CARD (ps n) = SUM n PAR.nc_g` suffices_by METIS_TAC[] THEN
   Induct THEN (
     ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [sum_numTheory.SUM_def]
   ) THEN
   ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.COUNT_SUC] THEN
   PAT_X_ASSUM ``!n:num. ps n = _`` (ASSUME_TAC o GSYM) THEN 
   ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [
     pred_setTheory.CARD_UNION_EQN, pred_setTheory.FINITE_COUNT,
     pred_setTheory.IMAGE_FINITE] THEN
   sg `IMAGE (\pc. (n,pc)) (count (PAR.nc_g n)) INTER (ps n) = {}` THEN1 (
      ONCE_REWRITE_TAC[pred_setTheory.EXTENSION] THEN
      UNABBREV_ALL_TAC THEN
      SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss++QI_ss) []
   ) THEN
   sg `CARD (IMAGE (\pc. (n,pc)) (count (PAR.nc_g n))) =  PAR.nc_g n` THEN1 (
     sg `!s. INJ (\pc:num. (n, pc)) s UNIV` THEN1 (
        SIMP_TAC std_ss [pred_setTheory.INJ_DEF, pred_setTheory.IN_UNIV]
     ) THEN
     ASM_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] THEN
     METIS_TAC [pred_setTheory.INJ_CARD_IMAGE_EQ, pred_setTheory.FINITE_COUNT,
       pred_setTheory.CARD_COUNT]
   ) THEN
   ASM_SIMP_TAC (arith_ss++pred_setLib.PRED_SET_ss) []
 ) THEN
 Q.SUBGOAL_THEN `CARD (ps PAR.ng) = CARD (IMAGE PCGC_inv (ps PAR.ng))` SUBST1_TAC THEN1 ( 
   `INJ PCGC_inv (ps PAR.ng) UNIV` suffices_by METIS_TAC[pred_setTheory.INJ_CARD_IMAGE_EQ] THEN
   UNABBREV_ALL_TAC THEN
   SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.INJ_DEF, 
      PCGC_inv_inj, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM]
 ) THEN
 `IMAGE PCGC_inv (ps PAR.ng) = count RPAR.nc` suffices_by PROVE_TAC[] THEN
 UNABBREV_ALL_TAC THEN
 SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [pred_setTheory.EXTENSION,
   GSYM RIGHT_EXISTS_AND_THM] THEN
 METIS_TAC [PCGC_PPGP_inv_def]);







(* coupling refined and ideal model parameters *)

val coupling_axiom = new_axiom("coupling_axiom", ``
(* the number of cores for each guest is reflected by PCG *)
   (!g. g < PAR.ng ==> (PAR.nc_g g = CARD {c:num | c < RPAR.nc /\ (PCG c = g)}))
(* the number of peripherals for each guest is reflected by PPG *)
/\ (!g. g < PAR.ng ==> (PAR.np_g g = CARD {p:num | p < RPAR.np /\ (PPG p = g)}))
(* Peripherals in both models trigger the same interrupts *)
/\ (!p. p < RPAR.np ==> (PAR.pirq_gp (PPG p) (PPP p) = RPAR.pirq_p p))
(* the refined model address region of each guest has the same size 
as ideal guest memory minus 1 (for the GICD region) *)
/\ (!g. g < PAR.ng ==> (CARD (RPAR.Amap (GUEST g)) = (CARD (PAR.A_G g) - 1)))
(* the gicd region is part of the ideal guest memory but 
not mapped to the guest in the refined model *)
/\ (!g. RPAR.Amap GICD PSUBSET PAR.A_G g /\ 
	(RPAR.Amap GICD INTER RPAR.Amap (GUEST g) = EMPTY))
(* same for GICC region *)
/\ (!g. RPAR.Amap GICC PSUBSET PAR.A_G g /\ 
	(RPAR.Amap GICC INTER RPAR.Amap (GUEST g) = EMPTY))
(* virtual interface only mapped to guest in refined model *)
/\ (!g. (RPAR.Amap GICV INTER PAR.A_G g = EMPTY) /\ 
	RPAR.Amap GICV PSUBSET RPAR.Amap (GUEST g))
(* virtual irq control interface never mapped to guest *)
/\ (!g. (RPAR.Amap GICH INTER PAR.A_G g = EMPTY) /\ 
	(RPAR.Amap GICH INTER RPAR.Amap(GUEST g) = EMPTY))
(* peripheral address regions are mapped identically *)
/\ (!p. p < RPAR.np ==> (PAR.A_gp (PPG p) (PPP p) = RPAR.Amap (PER p)))
(* each guest's refined memory region includes all its peripherals *)
/\ (!p. p < RPAR.np ==> RPAR.Amap (PER p) SUBSET RPAR.Amap (GUEST (PPG p)))
(* IGC channel capacity is limited to 1 page *)
/\ (!s g g'. s < PAR.ns /\ g < PAR.ng /\ g' < PAR.ng /\ (PAR.cpol s = (g,g')) ==>
		(CARD (RPAR.A_IGC g g') = 1))
(* no memory allocated for disallowed IGC channels *)
/\ (!g g'. g < PAR.ng /\ g' < PAR.ng /\ ~(?s. PAR.cpol s = (g,g')) ==>
		(RPAR.A_IGC g g' = EMPTY))
``);




(* Thomas TuerK: first coupling axiom is not needed
   TODO: adapt actual axiom  *)
val first_coupling_axiom = prove (
``(!g. g < PAR.ng ==> (PAR.nc_g g = CARD {c:num | c < RPAR.nc /\ (PCG c = g)}))``,
 REPEAT STRIP_TAC THEN
 Q.SUBGOAL_THEN `{c | c < RPAR.nc /\ (PCG c = g)} =
   IMAGE (\cg. PCGC_inv (g, cg)) (count (PAR.nc_g g))` SUBST1_TAC THEN1 (
   ONCE_REWRITE_TAC[pred_setTheory.EXTENSION] THEN
   SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] THEN

   METIS_TAC[PCGC_PPGP_inv_def]
 ) THEN
 `INJ  (\cg. PCGC_inv (g,cg)) (count (PAR.nc_g g)) UNIV` suffices_by 
   METIS_TAC [pred_setTheory.INJ_CARD_IMAGE_EQ, pred_setTheory.FINITE_COUNT,
      pred_setTheory.CARD_COUNT] THEN
 ASM_SIMP_TAC std_ss [pred_setTheory.INJ_DEF, pred_setTheory.IN_COUNT,
   pred_setTheory.IN_UNIV, PCGC_inv_inj]);


(* Thomas Tuerk: second coupling axiom is not needed 
   TODO: adapt actual axiom *)
val second_coupling_axiom = prove (
``(!g. g < PAR.ng ==> (PAR.np_g g = CARD {p:num | p < RPAR.np /\ (PPG p = g)}))``,
 REPEAT STRIP_TAC THEN
 Q.SUBGOAL_THEN `{p | p < RPAR.np /\ (PPG p = g)} =
   IMAGE (\pg. PPGP_inv (g, pg)) (count (PAR.np_g g))` SUBST1_TAC THEN1 (
   ONCE_REWRITE_TAC[pred_setTheory.EXTENSION] THEN
   SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) [] THEN
   METIS_TAC[PCGC_PPGP_inv_def]
 ) THEN
 `INJ  (\pg. PPGP_inv (g,pg)) (count (PAR.np_g g)) UNIV` suffices_by 
   METIS_TAC [pred_setTheory.INJ_CARD_IMAGE_EQ, pred_setTheory.FINITE_COUNT,
      pred_setTheory.CARD_COUNT] THEN 
 ASM_SIMP_TAC std_ss [pred_setTheory.INJ_DEF, pred_setTheory.IN_COUNT,
   pred_setTheory.IN_UNIV, PPGP_inv_inj]);


val refine_pirq_qp = store_thm ("refine_pirq_qp",
  ``g < PAR.ng /\ pe < PAR.np_g g ==> 
    (PAR.pirq_gp g pe = RPAR.pirq_p (PPGP_inv (g, pe)))``,
METIS_TAC[PCGC_PPGP_inv_def, coupling_axiom]);


(* projecting core indices in SGI interrupts *)

(* first project SGI sender to refined virtual interrupts *)
val PSQ_def = Define `
   (PSQ g (SGI (id, s, c)) = if (PCG s = g) /\ (PCG c = g) 
				/\ s < RPAR.nc /\ c < RPAR.nc
			     then SGI (id, PCC s, c) 
			     else PIR 1023)
/\ (PSQ g q = q)
`;

(* need to translate back sender core for nuvi search 
   as virtual interrupts already contain translated sender *)
val PSQ_inv_def = Define `
   (PSQ_inv g (SGI (id, s, c)) = SGI (id, PCGC_inv(g,s), c))
/\ (PSQ_inv g q = q)
`;

(* couple with ideal SGIs by translating also receiver *) 
val PRQ_def = Define `
   (PRQ g (SGI (id, s, c)) = if (PCG c = g) /\ c < RPAR.nc 
			     then SGI (id, s, PCC c) 
                             else PIR 1023)
/\ (PRQ g q = q)
`;

(* combination *)
val PQQ_def = Define `PQQ g = (PRQ g) o (PSQ g)`;

val PQQ_lem = store_thm("PQQ_lem", ``
   (PQQ g (SGI (id, c, c')) = if (PCG c = g) /\ (PCG c'=g) /\ 
				 c < RPAR.nc /\ c' < RPAR.nc
			      then SGI (id, PCC c, PCC c') 
			      else PIR 1023)
/\ (PQQ g (PIR q) = PIR q)
``,
  RW_TAC (srw_ss()) [PQQ_def, PSQ_def, PRQ_def]
);


val good_PRQ_lem = store_thm("good_PRQ_lem", ``
good_prq PRQ
``,
  RW_TAC (srw_ss()) [good_prq_def, PRQ_def] >> (
      Cases_on `(PCG c = g) /\ c < RPAR.nc` >> ( 
          FULL_SIMP_TAC (srw_ss()) [] >>
	  TRY ( METIS_TAC [good_proj_in_range_impls] ) >>
	  FULL_SIMP_TAC (srw_ss()) []  
      )
  )
);


val good_PSQ_lem = store_thm("good_PSQ_lem", ``
good_psq PSQ
``,
  RW_TAC (srw_ss()) [good_psq_def, PSQ_def] >> (
      Cases_on `(PCG s = g) /\ (PCG c = g) /\ s < RPAR.nc /\ c < RPAR.nc` >> ( 
          FULL_SIMP_TAC (srw_ss()) [] >>
	  TRY ( METIS_TAC [good_proj_in_range_impls] ) >>
	  FULL_SIMP_TAC (srw_ss()) []  
      )
  )    
);


(* projecting pevent list to specific guest *)
val PEL_def = Define `PEL (el: pevent list, g:num) = 
FILTER (\e. PPG(evper e) = g) el
`;

(* filtering out events for specific peripheral, refined / ideal version *)
val rPEF_def = Define `rPEF (el: pevent list, p:num) = 
FILTER (\e. evper e = p) el
`;

val iPEF_def = Define `iPEF (el: pevent list, p:num) = 
FILTER (\e. PPP (evper e) = p) el
`;

val PEF_lem = store_thm("PEF_lem", ``
!p. p < RPAR.np ==> 
    !l. (!e. MEM e l ==> evper e < RPAR.np) 
        ==> 
    (iPEF (PEL (l,PPG p), PPP p) = rPEF (l, p))
``,
  STRIP_TAC >>
  STRIP_TAC >>
  Induct
  >| [(* [] *)
      RW_TAC std_ss [iPEF_def, rPEF_def, PEL_def] >>
      RW_TAC std_ss [listTheory.FILTER]
      ,
      (* h::l *)
      RW_TAC std_ss [listTheory.MEM] >>
      `evper h < RPAR.np` by ( METIS_TAC [] ) >>
      `!e. MEM e l ==> evper e < RPAR.np` by ( METIS_TAC [] ) >>
      RES_TAC >>
      FULL_SIMP_TAC std_ss [iPEF_def, rPEF_def, PEL_def] >>
      RW_TAC std_ss [listTheory.FILTER, listTheory.MEM] >>
      `PPP (evper h) <> PPP p` by ( METIS_TAC [PPG_PPP_inj] ) >>
      RW_TAC std_ss []
     ]
);

val PEL_append_lem = store_thm("PEL_append_lem", ``
!n p. p < RPAR.np /\ (!e. MEM e n ==> (evper e = p))
    ==> 
!l. PEL (l ++ n, PPG p) = PEL (l,PPG p) ++ n
``,
  NTAC 3 STRIP_TAC >>
  Induct 
  >| [(* [] *)
      RW_TAC std_ss [PEL_def, rich_listTheory.APPEND_NIL, listTheory.FILTER] >>
      Induct_on `n`
      >| [(* [] *)
	  RW_TAC std_ss [listTheory.MEM, listTheory.FILTER]
	  ,
	  (* h::n *)
	  RW_TAC std_ss [listTheory.MEM, listTheory.FILTER]
	 ]
      ,
      (* h::l *)
      FULL_SIMP_TAC std_ss [PEL_def, listTheory.FILTER, listTheory.APPEND] >>
      GEN_TAC >>
      IF_CASES_TAC 
      >| [(* same guest *)
	  RW_TAC std_ss [listTheory.APPEND]
	  ,
	  RW_TAC std_ss []
	 ]
     ]
);

val PEL_other_lem = store_thm("PEL_other_lem", ``
!n p g. p < RPAR.np /\ (PPG p <> g) /\ (!e. MEM e n ==> (evper e = p))
    ==> 
!l. PEL (l ++ n, g) = PEL (l,g)
``,
  NTAC 4 STRIP_TAC >>
  Induct 
  >| [(* [] *)
      RW_TAC std_ss [rich_listTheory.APPEND_NIL] >>
      Induct_on `n`
      >| [(* [] *)
	  RW_TAC std_ss []
	  ,
	  (* h::n *)
	  RW_TAC std_ss [listTheory.MEM] >>
	  `PPG (evper h) <> g` by ( METIS_TAC [] ) >>
          FULL_SIMP_TAC std_ss [PEL_def, listTheory.FILTER]
	 ]
      ,
      (* h::l *)
      FULL_SIMP_TAC std_ss [PEL_def, listTheory.FILTER, listTheory.APPEND]
     ]
);


(* projecting psci events *)
val PEE_def = Define `PEE (e: event) = 
case e of
  | StopCore c => StopCore (PCC c)
  | StartCore c => StartCore (PCC c)
  | _ => e
`;

val PEG_def = Define `PEG (e: event) = 
case e of
  | StopCore c => PCG c
  | StartCore c => PCG c
  | _ => ARB
`;

val PPL_def = Define `PPL (el: event list, g:num) = 
MAP PEE (FILTER (\e. PEG e = g) el)
`;

(* dmsk contains all unowned interrupts *)
val gic_golden_mask_axiom = new_axiom("gic_golden_mask_axiom", ``
!G c q. (gic_abs G).gicd IN gic_gm_conf
     /\ inv_gicc ((gic_abs G).gicc c)
     /\ (PQQ (PCG c) q) NOTIN PIRQ (PCG c) UNION IPIRQ (PCG c)
==>
     q IN dmsk((gic_abs G).gicd, (gic_abs G).gicc c, c)
``);

(* we map peripherals and GICD into guest address space by identity mapping, 
GICD address is thus the same in both models *)
val Agicd_def = Define `Agicd = base_adr (RPAR.Amap GICD)`;

val Agicd_lem = store_thm("Agicd_lem",``
Agicd IN RPAR.Amap GICD
``,
  FULL_SIMP_TAC (srw_ss()) [Agicd_def] THEN 
  MATCH_MP_TAC base_adr_in_set_lem THEN
  `(CARD (RPAR.Amap GICD) = 1) /\ FINITE (RPAR.Amap GICD)` by (
      FULL_SIMP_TAC (srw_ss()) [refined_goodP_axiom |> SIMP_RULE bool_ss [refined_goodP_def]] ) THEN 
  IMP_RES_TAC math_lemmasTheory.singleton_not_empty_lem
);
	
val not_in_GICD_not_Agicd_lem = store_thm("not_in_GICD_not_Agicd_lem", ``
!a. a NOTIN RPAR.Amap GICD ==> a <> Agicd
``,
  GEN_TAC THEN 
  STRIP_TAC THEN
  ASSUME_TAC Agicd_lem THEN 
  METIS_TAC []
);

val Agicd_eq_GICD_lem = store_thm("Agicd_eq_GICD_lem",
    ``RPAR.Amap GICD = {Agicd}``,
    METIS_TAC [Agicd_lem, pred_setTheory.SING_DEF, pred_setTheory.SING_IFF_CARD1,
               pred_setTheory.IN_SING, refined_goodP_axiom]);

val Agicd_in_GICD_lem = store_thm("Agicd_in_GICD_lem",
    ``x IN RPAR.Amap GICD = (x = Agicd)``,
    METIS_TAC [pred_setTheory.IN_SING, Agicd_eq_GICD_lem]);

val Agicd_A_gicper_lem = store_thm("Agicd_A_gicper_lem",
    ``Agicd IN A_gicper``,
     SIMP_TAC (srw_ss()) [A_gicper_def, gicAR_def] THEN
     METIS_TAC [Agicd_lem]);


(* Address translation function for guests*)

val _ = new_constant("Trans", ``: num -> bool[36] -> bool[36] option``);

val Trans_axiom = new_axiom("Trans_axiom", ``
(* Translation only defined on each guest's ideal memory space, except GICD *)
   (!g a. g < PAR.ng ==> 
		((a IN PAR.A_G g /\ a<>Agicd) <=> IS_SOME(Trans g a)) )
(* Translation is injective for each guest *)
/\ (!g a a'. g < PAR.ng /\ a <> a' /\ Trans g a <> NONE /\ Trans g a' <> NONE ==>
		(Trans g a) <> (Trans g a'))
(* Translation maps into each guest's refined memory space, except GICD *)
/\ (!g a. g < PAR.ng ==> (a IN PAR.A_G g /\ a <> Agicd <=> 
		IS_SOME (Trans g a) /\ THE (Trans g a) IN RPAR.Amap (GUEST g)) )
(* each physical guest address is mapped *)
/\ (!g a. g < PAR.ng /\ a IN RPAR.Amap (GUEST g) ==> 
	        ?b. IS_SOME (Trans g b) /\ ( a = THE (Trans g b)) )
(* GICD is not mapped *)
/\ (!g. g < PAR.ng ==> (Trans g Agicd = NONE))
(* GICC region is mapped to GICV region, maintaining the order of pages *)
/\ (!g a. g < PAR.ng ==> ( a IN RPAR.Amap GICC <=>
		   IS_SOME (Trans g a) /\ THE (Trans g a) IN RPAR.Amap GICV ) )
/\ (!g a. g < PAR.ng /\ a IN RPAR.Amap GICC ==> 
	           (THE (Trans g a) ' 0 = a ' 0) )
(* All peripherals are identity-mapped *)
/\ (!g a p. g < PAR.ng /\ p < PAR.np_g g /\ a IN PAR.A_gp g p ==>
		(Trans g a = SOME a))
(* The IGC channels are mapped uniquely into refined memory *)
/\ (!g g' a. g < PAR.ng /\ g' < PAR.ng ==>
	((?s. s < PAR.ns /\ (PAR.cpol s = (g,g')) /\ (a = FST (PAR.igca s))) <=>
		IS_SOME (Trans g a) /\ THE (Trans g a) IN RPAR.A_IGC g g'))
/\ (!g g' a. g < PAR.ng /\ g' < PAR.ng ==>
	((?s. s < PAR.ns /\ (PAR.cpol s = (g',g)) /\ (a = SND (PAR.igca s))) <=>
		(IS_SOME (Trans g a) /\ THE (Trans g a) IN RPAR.A_IGC g' g)))
(* The IGC channels are shared between guests in refined memory *)
(* TODO?: we could possibly prove this as a lemma *)
/\ (!g g' a b. g < PAR.ng /\ g' < PAR.ng ==>
       ((?s. s < PAR.ns  /\ (PAR.cpol s = (g,g')) /\
             (a = FST (PAR.igca s)) /\ (b = SND (PAR.igca s))) ==>
		   (Trans g a = Trans g' b)))
``);


val A_IGCin_Trans_lem = store_thm("A_IGCin_Trans_lem", ``
!g g' a. 
   g < PAR.ng 
/\ g' < PAR.ng 
/\ g <> g'
/\ IS_SOME (Trans g a) 
/\ THE (Trans g a) IN RPAR.A_IGC g' g
==>
a IN A_IGCin g
``,
  RW_TAC (srw_ss()) [A_IGCin_def] >>
  METIS_TAC [Trans_axiom, pairTheory.SND]
);

val A_IGCout_Trans_lem = store_thm("A_IGCout_Trans_lem", ``
!g g' a. 
   g < PAR.ng 
/\ g' < PAR.ng 
/\ g <> g'
/\ IS_SOME (Trans g a) 
/\ THE (Trans g a) IN RPAR.A_IGC g g'
==>
a IN A_IGCout g
``,
  RW_TAC (srw_ss()) [A_IGCout_def] >>
  METIS_TAC [Trans_axiom, pairTheory.FST]
);


(* need wrapper to hide nasty consequences of underspecified THE *)
val FAULT_ADDRESS_def = Define `FAULT_ADDRESS = Agicd`;

val FAULT_ADDRESS_lem = store_thm("FAULT_ADDRESS_lem", ``
!A a. A <> GICD /\ a IN RPAR.Amap A
   /\ (singleAR A \/ perAR(A,RPAR) \/ guestAR(A,PAR))
==>
a <> FAULT_ADDRESS 
``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  `DISJOINT (RPAR.Amap GICD) (RPAR.Amap A)` by (
    MATCH_MP_TAC refined_goodP_axiom_Amap_disjoint THEN
    FULL_SIMP_TAC (srw_ss()) []
  ) THEN
  `a IN RPAR.Amap GICD` by ( FULL_SIMP_TAC (srw_ss()) [Agicd_lem, FAULT_ADDRESS_def] ) THEN 
  PROVE_TAC[pred_setTheory.IN_DISJOINT]
);

val ATrans_def = Define `
ATrans g a = if IS_SOME (Trans g a) then THE (Trans g a) else FAULT_ADDRESS
`;

val ATrans_lem = store_thm("ATrans_lem", ``
!g a. ATrans g a <> FAULT_ADDRESS 
==>
IS_SOME (Trans g a)
``,
  RW_TAC (srw_ss()) [ATrans_def]
);

val IS_SOME_ATrans_lem = store_thm("IS_SOME_ATrans_lem", ``
!g a. g < PAR.ng
/\ IS_SOME (Trans g a)
==>
ATrans g a <> FAULT_ADDRESS
``,
  RW_TAC (srw_ss()) [ATrans_def] THEN 
  `THE (Trans g a) IN RPAR.Amap (GUEST g)` by ( IMP_RES_TAC Trans_axiom ) THEN 
  IMP_RES_TAC FAULT_ADDRESS_lem THEN 
  METIS_TAC [AddressRegion_distinct, guestAR_def]
);

val ATrans_inj = store_thm("ATrans_inj", ``
!g a a'. 
   g < PAR.ng
/\ ATrans g a <> FAULT_ADDRESS
/\ (ATrans g a = ATrans g a')
==>
(a = a')
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC ATrans_lem THEN 
  `IS_SOME (Trans g a')` by (
      `ATrans g a' <> FAULT_ADDRESS` by ( FULL_SIMP_TAC std_ss [] ) THEN 
      IMP_RES_TAC ATrans_lem 
  ) THEN 
  IMP_RES_TAC quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE THEN 
  FULL_SIMP_TAC (srw_ss()) [ATrans_def] THEN 
  `Trans g a = Trans g a'` by (
      IMP_RES_TAC optionTheory.IS_SOME_EXISTS THEN 
      FULL_SIMP_TAC (srw_ss()) [optionTheory.THE_DEF]
  ) THEN 
  CCONTR_TAC THEN 
  IMP_RES_TAC Trans_axiom
);


val guest_adr_trans_lem = store_thm("guest_adr_trans_lem", ``
!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a <> Agicd  ==>
IS_SOME (Trans g a) /\ THE (Trans g a) IN RPAR.Amap (GUEST g) 
``,
RW_TAC (srw_ss()) []
THEN IMP_RES_TAC Trans_axiom
);

val trans_guest_adr_lem = store_thm("trans_guest_adr_lem", ``
!g a. g < PAR.ng /\ IS_SOME (Trans g a) ==>
a IN PAR.A_G g /\ a <> Agicd
``,
RW_TAC (srw_ss()) [] THEN ( IMP_RES_TAC Trans_axiom )
);


val GICD_ATrans_lem = store_thm(
   "GICD_ATrans_lem",
   ``a IN RPAR.Amap GICD /\ g < PAR.ng ==> (ATrans g a = FAULT_ADDRESS)``,
   SIMP_TAC std_ss [ATrans_def] >>
   METIS_TAC [Agicd_in_GICD_lem, Trans_axiom]);


val gic_trans_lem = store_thm("gic_trans_lem", ``
!A g a. 
   g < PAR.ng 
/\ gicAR A 
/\ (THE (Trans g a)) IN RPAR.Amap A 
/\ IS_SOME (Trans g a)
==> 
a IN RPAR.Amap GICC /\ (THE (Trans g a)) IN RPAR.Amap GICV
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  `a IN PAR.A_G g /\ a <> Agicd` by (
      IMP_RES_TAC Trans_axiom THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN
  `THE (Trans g a) IN RPAR.Amap (GUEST g)` by (
      IMP_RES_TAC Trans_axiom ) THEN
  `A = GICV` by (
      FULL_SIMP_TAC (srw_ss()) [gicAR_def] THEN
      IMP_RES_TAC gic_not_guest_mem_lem THEN
      PROVE_TAC [] ) THEN 
  RW_TAC (srw_ss()) [] THEN
  IMP_RES_TAC Trans_axiom
);

val gicc_trans_lem = store_thm("gicc_trans_lem", ``
!g a. 
   g < PAR.ng 
/\ a IN RPAR.Amap GICC
==> 
(THE (Trans g a)) IN RPAR.Amap GICV /\ IS_SOME (Trans g a)
``,
  METIS_TAC [Trans_axiom]
);


val Trans_gicc_lem = store_thm("Trans_gicc_lem", ``
!g a. g < PAR.ng /\ IS_SOME (Trans g a) ==>
THE (Trans g a) NOTIN RPAR.Amap GICC
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC trans_guest_adr_lem >>
  IMP_RES_TAC guest_adr_trans_lem >>
  METIS_TAC [gic_not_guest_mem_lem]
);

val Trans_gicd_lem = store_thm("Trans_gicd_lem", ``
!g a. g < PAR.ng /\ IS_SOME (Trans g a) ==>
a NOTIN RPAR.Amap GICD
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC trans_guest_adr_lem >>
  METIS_TAC [Agicd_in_GICD_lem]
);


val per_surj_map_lem = store_thm("per_surj_map_lem", ``
!a p.
   p < RPAR.np
/\ a IN RPAR.Amap (PER p)
==>
?b. b IN PAR.A_gp (PPG p) (PPP p) 
 /\ (THE (Trans (PPG p) b) = a)
 /\ IS_SOME (Trans (PPG p) b)
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  `PPG p < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  `PPP p < PAR.np_g (PPG p)` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  `!b. b IN PAR.A_gp (PPG p) (PPP p) ==> (Trans (PPG p) b = SOME b)` by (
      IMP_RES_TAC Trans_axiom ) THEN 
  `PAR.A_gp (PPG p) (PPP p) = RPAR.Amap (PER p)` by (
      IMP_RES_TAC coupling_axiom ) THEN
  `Trans (PPG p) a = SOME a` by ( PROVE_TAC [] ) THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  HINT_EXISTS_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [optionTheory.THE_DEF, optionTheory.IS_SOME_DEF]
);  

val per_trans_lem = store_thm("per_trans_lem", ``
!g p a. 
   g < PAR.ng 
/\ p < RPAR.np
/\ (THE (Trans g a)) IN RPAR.Amap (PER p)
/\ IS_SOME (Trans g a)
==> 
(a IN PAR.A_gp (PPG p) (PPP p)) /\ (a = THE (Trans g a)) /\ (PPG p = g)
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  `PAR.A_gp (PPG p) (PPP p) = RPAR.Amap (PER p)` by (
      IMP_RES_TAC coupling_axiom ) THEN
  `a IN PAR.A_G g /\ a <> Agicd` by (
      IMP_RES_TAC Trans_axiom THEN 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN
  `PPG p = g` by (
      CCONTR_TAC THEN
      `PPG p < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
      `PPP p < PAR.np_g (PPG p)` by ( IMP_RES_TAC good_proj_axiom ) THEN 
      `THE (Trans g a) IN RPAR.Amap (GUEST (PPG p))` by (
          IMP_RES_TAC coupling_axiom THEN
          FULL_SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF] ) THEN
      `THE (Trans g a) IN RPAR.Amap (GUEST g)` by (
          IMP_RES_TAC Trans_axiom ) THEN
      `THE (Trans g a) NOTIN RPAR.Amap GICV `by (
	  `DISJOINT (RPAR.Amap GICV) (RPAR.Amap (PER p))` by (
	      MATCH_MP_TAC refined_goodP_axiom_Amap_disjoint THEN
              ASM_SIMP_TAC (srw_ss()) []) THEN  
	  PROVE_TAC [pred_setTheory.IN_DISJOINT] ) THEN 
      `THE (Trans g a) NOTIN RPAR.A_IGC g (PPG p)` by (
	  `DISJOINT (RPAR.Amap (PER p)) (RPAR.A_IGC g (PPG p))` by (
	      METIS_TAC [refined_goodP_axiom, ARpred_REWRITES] ) THEN
	  PROVE_TAC [pred_setTheory.IN_DISJOINT] ) THEN 
      `THE (Trans g a) NOTIN RPAR.A_IGC (PPG p) g` by (
	  `DISJOINT (RPAR.Amap (PER p)) (RPAR.A_IGC (PPG p) g)` by (
	      METIS_TAC [refined_goodP_axiom, ARpred_REWRITES] ) THEN
	  PROVE_TAC [pred_setTheory.IN_DISJOINT] ) THEN 
      `RPAR.Amap (GUEST (PPG p)) INTER RPAR.Amap (GUEST g) = RPAR.A_IGC (PPG p) g UNION RPAR.A_IGC g (PPG p) UNION RPAR.Amap GICV` by (
          IMP_RES_TAC refined_goodP_axiom ) THEN 
      FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN 
      PROVE_TAC [] 
  ) THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN
  IMP_RES_TAC per_surj_map_lem  THEN 
  `a = b` by ( 
      CCONTR_TAC THEN
      IMP_RES_TAC Trans_axiom THEN 
      METIS_TAC [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS, optionTheory.THE_DEF] ) THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN
  `PPG p < PAR.ng` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  `PPP p < PAR.np_g (PPG p)` by ( IMP_RES_TAC good_proj_axiom ) THEN 
  `Trans g b = SOME b` by (
      IMP_RES_TAC Trans_axiom THEN 
      METIS_TAC [] ) THEN
  FULL_SIMP_TAC (srw_ss()) [optionTheory.THE_DEF]
);

val PT_Trans_lem = store_thm("PT_Trans_lem", ``
!g a a'.
   g < PAR.ng
/\ a IN RPAR.A_PT g
/\ IS_SOME (Trans g a')
==>
THE (Trans g a') <> a
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC trans_guest_adr_lem THEN 
  IMP_RES_TAC guest_adr_trans_lem THEN 
  IMP_RES_TAC PT_guest_disj_lem THEN 
  CCONTR_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) []
);

val PPT_Trans_lem = store_thm("PPT_Trans_lem", ``
!g a a'.
   g < PAR.ng
/\ a IN RPAR.A_PPT g
/\ IS_SOME (Trans g a')
==>
THE (Trans g a') <> a
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC trans_guest_adr_lem THEN 
  IMP_RES_TAC guest_adr_trans_lem THEN 
  IMP_RES_TAC PPT_guest_disj_lem THEN 
  CCONTR_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) []
);

val A_gicper_Trans_lem = store_thm("A_gicper_Trans_lem", ``
!r g. 
   g < PAR.ng
/\ ATrans g (PAdr r) <> FAULT_ADDRESS
/\ PAdr r NOTIN RPAR.Amap GICC
/\ PAdr r NOTIN RPAR.Amap GICD
/\ (!p. p < PAR.np_g g ==> PAdr r NOTIN PAR.A_gp g p)
==>
ATrans g (PAdr r) NOTIN A_gicper
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC ATrans_lem >>
  RW_TAC (srw_ss()) [ATrans_def, A_gicper_def, GSYM IMP_DISJ_THM]
  >| [(* case: not gic *)
      IMP_RES_TAC ( gic_trans_lem |> SPEC_ALL |> CONTRAPOS 
				  |> GEN_ALL |> SIMP_RULE bool_ss [] ) >>
      METIS_TAC [] 
      ,
      (* case: not per *) 
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [] >>
      IMP_RES_TAC per_trans_lem >>
      METIS_TAC [good_proj_in_range_impls]
     ]      
);

val guest_mem_A_gicper_lem = store_thm("guest_mem_A_gicper_lem", ``
!g a. 
   g < PAR.ng
/\ a IN PAR.A_G g
/\ a NOTIN RPAR.Amap GICC
/\ a NOTIN RPAR.Amap GICD
/\ (!p. p < PAR.np_g g ==> a NOTIN PAR.A_gp g p)
==>
a NOTIN A_gicper
``,
  RW_TAC (srw_ss()) [A_gicper_def]
  >| [REWRITE_TAC [GSYM IMP_DISJ_THM] >>
      STRIP_TAC >>
      FULL_SIMP_TAC (srw_ss()) [gicAR_def] >> (
          METIS_TAC [goodP_axiom, pred_setTheory.IN_DISJOINT]
      )
      ,
      REWRITE_TAC [GSYM IMP_DISJ_THM] >>
      STRIP_TAC >>
      `!g' p'. g' < PAR.ng /\ p' < PAR.np_g g' ==> a NOTIN PAR.A_gp g' p'` by (
          REPEAT GEN_TAC >> STRIP_TAC >>
	  Cases_on `g=g'`
	  >| [FULL_SIMP_TAC (srw_ss()) []
	      ,
	      METIS_TAC [goodP_axiom]
	     ]
      ) >>
      `RPAR.Amap (PER p) = PAR.A_gp (PPG p) (PPP p)` by (
          METIS_TAC [coupling_axiom]
      ) >>
      ASM_REWRITE_TAC [] >>
      METIS_TAC [good_proj_in_range_impls]
     ]
);

val not_in_A_gicper_lem = store_thm("not_in_A_gicper_lem", ``
!a. a NOTIN A_gicper
==>
   a NOTIN RPAR.Amap GICC
/\ a NOTIN RPAR.Amap GICD
/\ a NOTIN RPAR.Amap GICH
/\ a NOTIN RPAR.Amap GICV
/\ (!p g. g < PAR.ng /\ p < PAR.np_g g ==> a NOTIN PAR.A_gp g p)
``,
  GEN_TAC >> STRIP_TAC >>
  FULL_SIMP_TAC (srw_ss()) [A_gicper_def, gicAR_def] >>
  RW_TAC (srw_ss()) []
  >| [METIS_TAC []
      ,
      METIS_TAC []
      ,
      METIS_TAC []
      ,
      METIS_TAC []
      ,
      `PPGP_inv(g,p) < RPAR.np` by (
          METIS_TAC [good_proj_in_range_impls]
      ) >> 
      `PAR.A_gp g p = RPAR.Amap (PER (PPGP_inv (g,p)))` by (
          METIS_TAC [coupling_axiom, PPGP_inv_rewrites, 
		     good_proj_in_range_impls]
      ) >> 
      METIS_TAC []
     ]
);

val A_gicper_Trans_adr_lem = store_thm("A_gicper_Trans_adr_lem", ``
!a g. 
   g < PAR.ng
/\ IS_SOME (Trans g a)
/\ a NOTIN A_gicper
==>
THE (Trans g a) NOTIN A_gicper
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC not_in_A_gicper_lem >>
  RW_TAC (srw_ss()) [A_gicper_def, GSYM IMP_DISJ_THM]
  >| [(* case: not gic *)
      IMP_RES_TAC ( gic_trans_lem |> SPEC_ALL |> CONTRAPOS 
				  |> GEN_ALL |> SIMP_RULE bool_ss [] ) >>
      METIS_TAC [] 
      ,
      (* case: not per *) 
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [] >>
      IMP_RES_TAC per_trans_lem >>
      METIS_TAC [good_proj_in_range_impls]
     ]      
);

val Trans_adr_A_gicper_lem = store_thm("Trans_adr_A_gicper_lem", ``
!a g. 
   g < PAR.ng
/\ IS_SOME (Trans g a)
/\ THE (Trans g a) NOTIN A_gicper
==>
a NOTIN A_gicper
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC not_in_A_gicper_lem >>
  FULL_SIMP_TAC (srw_ss()) [A_gicper_def] >>
  RW_TAC (srw_ss()) [GSYM IMP_DISJ_THM]
  >| [(* case: not gic *)
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [] >>
      IMP_RES_TAC trans_guest_adr_lem >>
      `a NOTIN RPAR.Amap GICD` by ( METIS_TAC [Agicd_in_GICD_lem] ) >>
      `a NOTIN RPAR.Amap GICH /\ a NOTIN RPAR.Amap GICV` by (
          METIS_TAC [goodP_axiom, pred_setTheory.IN_DISJOINT]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [gicAR_def] >> (
          METIS_TAC [gicc_trans_lem]
      )
      ,
      (* case: not per *) 
      Cases_on `PPG p = g`
      >| [(* same guest *)
	  `RPAR.Amap (PER p) = PAR.A_gp (PPG p) (PPP p)` by (
	      METIS_TAC [coupling_axiom]
	  ) >>
	  ASM_REWRITE_TAC [] >>
	  CCONTR_TAC >>
	  FULL_SIMP_TAC (srw_ss()) [] >>
	  `PPP p < PAR.np_g (PPG p)` by ( 
	      METIS_TAC [good_proj_in_range_impls] 
	  ) >>
	  `THE (Trans g a) = a` by (
              METIS_TAC [Trans_axiom, optionTheory.THE_DEF]
          ) >>
	  `THE (Trans g a) ∉ RPAR.Amap (PER p)` by ( METIS_TAC [] ) >>
	  METIS_TAC []
	  ,
	  (* other guest's peripheral *)
	  `RPAR.Amap (PER p) = PAR.A_gp (PPG p) (PPP p)` by (
	      METIS_TAC [coupling_axiom]
	  ) >>
	  ASM_REWRITE_TAC [] >>
	  `PPG p < PAR.ng` by ( 
	      METIS_TAC [good_proj_in_range_impls] 
	  ) >>
	  `PPP p < PAR.np_g (PPG p)` by ( 
	      METIS_TAC [good_proj_in_range_impls] 
	  ) >>
	  IMP_RES_TAC trans_guest_adr_lem >>
	  METIS_TAC [goodP_axiom]
	 ]      
     ]
);

val trans_per_lem = store_thm("trans_per_lem", ``
!a g p. g < PAR.ng /\ p < PAR.np_g g /\ a IN PAR.A_gp g p ==>
IS_SOME (Trans g a)
``,
  REPEAT STRIP_TAC >>
  `a IN PAR.A_G g` by ( 
      METIS_TAC [goodP_axiom, 
		 pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF]
  ) >>
  `?p'. (g = PPG p') /\ (p = PPP p') /\ p' < RPAR.np` by (
      EXISTS_TAC ``PPGP_inv (g,p)`` >>
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  ) >>
  RW_TAC std_ss [] >>
  `a <> Agicd` by (
      MATCH_MP_TAC not_in_GICD_not_Agicd_lem >>
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [coupling_axiom] >>
      `gicAR GICD` by ( REWRITE_TAC [gicAR_def] ) >>
      IMP_RES_TAC GICaddresses_lem >>
      `a IN RPAR.Amap GICD INTER RPAR.Amap (PER p')` suffices_by (
          FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
      ) >>
      RW_TAC std_ss [pred_setTheory.IN_INTER]
  ) >>
  IMP_RES_TAC guest_adr_trans_lem
);

val trans_per_adr_lem = store_thm("trans_per_adr_lem", ``
!a g p. 
   g < PAR.ng
/\ p < PAR.np_g g 
/\ a IN PAR.A_gp g p 
==>
   (Trans g a = SOME a)
``,
  REPEAT STRIP_TAC >>
  METIS_TAC [Trans_axiom]
); 

(* SIMPLIFIED *)
val igc_adr_disj_lem = store_thm("igc_adr_disj_lem", ``
!a g g' b h h'. g < PAR.ng /\ g' < PAR.ng /\ h < PAR.ng /\ h' < PAR.ng 
     /\ g <> g' /\ h <> h' /\ (g,g') <> (h,h') 
     /\ a IN RPAR.A_IGC g g' /\ b IN RPAR.A_IGC h h' ==>
				  (a <> b)
``,
 REPEAT STRIP_TAC THEN
 `DISJOINT (RPAR.A_IGC g g') (RPAR.A_IGC h h')` by METIS_TAC[refined_goodP_axiom] THEN
 METIS_TAC [pred_setTheory.IN_DISJOINT]
);


(* SIMPLIFIED *)
val shared_guest_mem_lem = store_thm("shared_guest_mem_lem", ``
!g g' a b. g < PAR.ng /\ g' < PAR.ng /\ g <> g'
  /\ a IN RPAR.Amap (GUEST g) /\ b IN RPAR.Amap (GUEST g') /\ (a = b) ==>
	(a IN RPAR.A_IGC g g' \/ a IN RPAR.A_IGC g' g \/ a IN RPAR.Amap GICV)
``,
  SIMP_TAC std_ss [] THEN
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `b IN (RPAR.Amap (GUEST g) INTER RPAR.Amap (GUEST g')) <=>
                  b IN (RPAR.A_IGC g g' UNION RPAR.A_IGC g' g UNION RPAR.Amap GICV)` MP_TAC THEN1 (
    METIS_TAC[refined_goodP_axiom]
  ) THEN
  ASM_SIMP_TAC std_ss [pred_setTheory.IN_INTER, pred_setTheory.IN_UNION] THEN
  PROVE_TAC[]);


(* a is ideal address for IGC channel between g <-> g' *)
val igc_chan_def = Define `igc_chan (a:bool[36], g:num, g':num) = 
?s. (s < PAR.ns) /\ 
       ( (PAR.cpol s = (g,g')) /\ (a = FST (PAR.igca s)) 
      \/ (PAR.cpol s = (g',g)) /\ (a = SND (PAR.igca s)) )
`; 

(* a is ideal address for IGC channel between g <-> g' *)
val other_igc_chan_def = Define `other_igc_chan (a:bool[36], g:num, g':num) = 
?s gx. gx < PAR.ng /\ g <> gx /\ g' <> gx /\ (s < PAR.ns) /\ 
       ( (PAR.cpol s = (g,gx)) /\ (a = FST (PAR.igca s)) 
      \/ (PAR.cpol s = (gx,g)) /\ (a = SND (PAR.igca s)) )
`; 

(* a is not an IGC channel address in guest g *)
val no_igc_chan_def = Define `no_igc_chan (a:bool[36], g:num) = 
!g'. g' < PAR.ng /\ g <> g' ==> ~?s. (s < PAR.ns) /\ 
	 ( (PAR.cpol s = (g,g')) /\ (a = FST (PAR.igca s))
	\/ (PAR.cpol s = (g',g)) /\ (a = SND (PAR.igca s)) ) 
`;


val other_igc_chan_lem = store_thm("other_igc_chan_lem", ``
!a g g'. g < PAR.ng /\ g' < PAR.ng /\ g <> g' /\ other_igc_chan(a,g,g') ==>
?gx. gx < PAR.ng /\ g <> gx /\ g' <> gx /\ igc_chan (a,g,gx)
``,
  RW_TAC (srw_ss()) [other_igc_chan_def]
  THEN HINT_EXISTS_TAC
  THEN RW_TAC (srw_ss()) [igc_chan_def]
  THEN HINT_EXISTS_TAC
  THEN RW_TAC (srw_ss()) []
);


val igc_chan_other_guest_lem = store_thm("igc_chan_other_guest_lem", ``
!g g' g'' a a' s.
   g < PAR.ng
/\ g' < PAR.ng
/\ g'' < PAR.ng
/\ g <> g''
/\ g' <> g''
/\ a IN PAR.A_G g
/\ s < PAR.ns
/\ (PAR.cpol s = (g,g'))
/\ (PAR.igca s = (a,a'))
/\ a NOTIN A_gicper
==>
(THE (Trans g a)) NOTIN RPAR.Amap (GUEST g'')
``,
  RW_TAC (srw_ss()) [] >>
  `a <> Agicd` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [Agicd_A_gicper_lem]
  ) >>
  `IS_SOME (Trans g a) /\ THE(Trans g a) IN RPAR.Amap (GUEST g)` by (
      METIS_TAC [guest_adr_trans_lem]
  ) >>
  `THE (Trans g a) NOTIN A_gicper` by (
      IMP_RES_TAC A_gicper_Trans_adr_lem
  ) >>
  `THE (Trans g a) NOTIN RPAR.Amap GICV` by (
      IMP_RES_TAC not_in_A_gicper_lem
  ) >>
  `THE (Trans g a) IN RPAR.A_IGC g g'` by (
      METIS_TAC [Trans_axiom, pairTheory.FST]
  ) >>
  `g <> g'` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [] >>
      METIS_TAC [goodP_axiom]
  ) >>
  `THE (Trans g a) NOTIN RPAR.A_IGC g'' g` by (
      `(g, g') <> (g'', g)` by (
          FULL_SIMP_TAC (srw_ss()) []
      ) >>
      METIS_TAC [refined_goodP_axiom, pred_setTheory.IN_DISJOINT]
  ) >>
  `THE (Trans g a) NOTIN RPAR.A_IGC g g''` by (
      `(g, g') <> (g, g'')` by (
          FULL_SIMP_TAC (srw_ss()) []
      ) >>
      METIS_TAC [refined_goodP_axiom, pred_setTheory.IN_DISJOINT]
  ) >>
  `THE (Trans g a) NOTIN 
   RPAR.A_IGC g g'' UNION RPAR.A_IGC g'' g UNION RPAR.Amap GICV` by (
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  CCONTR_TAC >>
  `THE (Trans g a) IN RPAR.Amap (GUEST g) INTER RPAR.Amap (GUEST g'')` by (
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  `RPAR.Amap (GUEST g) INTER RPAR.Amap (GUEST g'') = 
   RPAR.A_IGC g g'' UNION RPAR.A_IGC g'' g UNION RPAR.Amap GICV` by (
      METIS_TAC [refined_goodP_axiom]
  ) >>
  METIS_TAC []
);

(* SIMPLIFIED *)
val no_igc_chan_lem = store_thm("no_igc_chan_lem", ``
!g g' a. g < PAR.ng /\ g' < PAR.ng /\ g <> g' ==> 
(no_igc_chan(a,g) <=> ~igc_chan(a,g,g') /\ ~other_igc_chan(a,g,g'))
``,
RW_TAC (srw_ss()) [no_igc_chan_def, igc_chan_def, other_igc_chan_def]
THEN METIS_TAC []
);

(* SIMPLIFIED *)
val normal_guest_mem_trans_lem = store_thm("normal_guest_mem_trans_lem", ``
!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a <> Agicd /\ a NOTIN RPAR.Amap GICC 
  /\ no_igc_chan(a,g) ==>
                IS_SOME (Trans g a)
             /\ THE (Trans g a) IN RPAR.Amap (GUEST g)
	     /\ THE (Trans g a) NOTIN RPAR.Amap GICC
	     /\ THE (Trans g a) NOTIN RPAR.Amap GICV
	     /\ !g'. g'<PAR.ng /\ g <> g' ==> 
			       THE (Trans g a) NOTIN RPAR.A_IGC g g' 
			    /\ THE (Trans g a) NOTIN RPAR.A_IGC g' g
``,
 MP_TAC Trans_axiom
 THEN MP_TAC coupling_axiom
 THEN RW_TAC (srw_ss()) [pred_setTheory.INTER_DEF, pred_setTheory.GSPEC_ETA, no_igc_chan_def]
 THEN METIS_TAC []
);

(* SIMPLIFIED *)
val igc_chan_trans_lem = store_thm("igc_chan_trans_lem", ``
!a g g'. g < PAR.ng /\ g' < PAR.ng /\ g <> g' /\ a IN PAR.A_G g /\ a <> Agicd
      /\ igc_chan(a,g,g') ==>
                IS_SOME (Trans g a)
             /\ THE (Trans g a) IN RPAR.Amap (GUEST g)
             /\ THE (Trans g a) IN RPAR.Amap (GUEST g')
	     /\ (THE (Trans g a) IN RPAR.A_IGC g g' 
	        \/ THE (Trans g a) IN RPAR.A_IGC g' g)
``,
  REPEAT GEN_TAC
  THEN IMP_RES_TAC guest_adr_trans_lem
  THEN RW_TAC (srw_ss()) [igc_chan_def]
  THEN ASSUME_TAC Trans_axiom
  THEN RES_TAC
  THEN METIS_TAC [refined_goodP_axiom, refined_goodP_def,pred_setTheory.SUBSET_DEF]
);



(* SIMPLIFIED *)
val normal_guest_mem_disj_lem = store_thm("normal_guest_mem_disj_lem", ``
!g g' a b. g < PAR.ng /\ g' < PAR.ng /\ g <> g'
  /\ a IN PAR.A_G g /\ a <> Agicd /\ a NOTIN RPAR.Amap GICC 
  /\ b IN PAR.A_G g' /\ b <> Agicd /\ b NOTIN RPAR.Amap GICC 
  /\ no_igc_chan(a,g) /\ no_igc_chan(b,g')
==>
  (Trans g a) <> (Trans g' b)
``,
  RW_TAC (srw_ss()) []
  THEN IMP_RES_TAC normal_guest_mem_trans_lem
  THEN IMP_RES_TAC shared_guest_mem_lem
  THEN FULL_SIMP_TAC (srw_ss()) [optionTheory.IS_SOME_EXISTS]
  THEN REV_FULL_SIMP_TAC (srw_ss()) []
);



(* SIMPLIFIED *)
val unshared_guest_mem_disj_lem = store_thm("unshared_guest_mem_disj_lem", ``
!g g' a b. g < PAR.ng /\ g' < PAR.ng /\ g <> g'
  /\ a IN PAR.A_G g /\ a <> Agicd /\ a NOTIN RPAR.Amap GICC 
  /\ b IN PAR.A_G g' /\ b <> Agicd /\ b NOTIN RPAR.Amap GICC 
  /\ ~igc_chan(a,g,g') /\ ~igc_chan(b,g',g) ==>
		(Trans g a) <> (Trans g' b)
``,
  RW_TAC (srw_ss()) []
  THEN ASSUME_TAC no_igc_chan_lem
  THEN Cases_on `other_igc_chan(a,g,g')`
  THEN Cases_on `other_igc_chan(b,g',g)`
  THEN1  ((* case other-other *)
         ASSUME_TAC  other_igc_chan_lem
         THEN ASSUME_TAC igc_adr_disj_lem
         THEN ASSUME_TAC igc_chan_trans_lem
         THEN FULL_SIMP_TAC (srw_ss()) []
         THEN METIS_TAC [])
    (* all other cases *)
  THEN ASSUME_TAC normal_guest_mem_trans_lem
  THEN ASSUME_TAC guest_adr_trans_lem
  THEN ASSUME_TAC shared_guest_mem_lem 
  THEN METIS_TAC []
);


val unshared_guest_mem_Trans_lem = store_thm("unshared_guest_mem_Trans_lem", ``
!g g' a.
   g < PAR.ng
/\ g' < PAR.ng
/\ g <> g'
/\ a IN PAR.A_G g
/\ a NOTIN A_IGCin g
/\ a NOTIN A_IGCout g
/\ a NOTIN A_gicper
==>
(THE (Trans g a)) NOTIN RPAR.Amap (GUEST g')
``,
  RW_TAC (srw_ss()) [] >>
  `a <> Agicd` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [Agicd_A_gicper_lem]
  ) >>
  `IS_SOME (Trans g a) /\ THE(Trans g a) IN RPAR.Amap (GUEST g)` by (
      METIS_TAC [guest_adr_trans_lem]
  ) >>
  `THE (Trans g a) NOTIN A_gicper` by (
      IMP_RES_TAC A_gicper_Trans_adr_lem
  ) >>
  `THE (Trans g a) NOTIN RPAR.Amap GICV` by (
      IMP_RES_TAC not_in_A_gicper_lem
  ) >>
  `THE (Trans g a) NOTIN RPAR.A_IGC g' g` by (
      METIS_TAC [A_IGCin_Trans_lem]
  ) >>
  `THE (Trans g a) NOTIN RPAR.A_IGC g g'` by (
      METIS_TAC [A_IGCout_Trans_lem]
  ) >>
  `THE (Trans g a) NOTIN 
   RPAR.A_IGC g g' UNION RPAR.A_IGC g' g UNION RPAR.Amap GICV` by (
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  CCONTR_TAC >>
  `THE (Trans g a) IN RPAR.Amap (GUEST g) INTER RPAR.Amap (GUEST g')` by (
      FULL_SIMP_TAC (srw_ss()) []
  ) >>
  `RPAR.Amap (GUEST g) INTER RPAR.Amap (GUEST g') = 
   RPAR.A_IGC g g' UNION RPAR.A_IGC g' g UNION RPAR.Amap GICV` by (
      METIS_TAC [refined_goodP_axiom]
  ) >>
  METIS_TAC []
);

(* TODO: move somewhere else *)

val GSPEC_f_lem = store_thm("GSPEC_f_lem", ``
!x f P. x IN {f x | P x} <=> ?y. (x = f y) /\ P y
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_APP] >>
      IMP_RES_TAC pred_setTheory.GSPECIFICATION_applied >>
      FULL_SIMP_TAC std_ss [] >>
      METIS_TAC []
      ,
      (* <== *)
      STRIP_TAC >>
      IMP_RES_TAC pred_setTheory.IN_GSPEC
     ]
);


val Trans_eq_igc_out_lem = store_thm("Trans_eq_igc_out_lem", ``
!s r a b. 
    s < PAR.ng
 /\ r < PAR.ng
 /\ s <> r
 /\ a IN PAR.A_G s 
 /\ a NOTIN A_gicper
 /\ b IN PAR.A_G r
 /\ b NOTIN A_gicper
 /\ (THE (Trans s a) = THE (Trans r b))
 /\ a IN A_IGCout s
==>
?ch. ch < PAR.ns /\ (PAR.cpol ch = (s,r)) /\ (PAR.igca ch = (a,b))
``,
  REPEAT STRIP_TAC >>
  `a <> Agicd` by ( METIS_TAC [Agicd_A_gicper_lem] ) >>
  `b <> Agicd` by ( METIS_TAC [Agicd_A_gicper_lem] ) >>
  `a NOTIN RPAR.Amap GICC` by ( IMP_RES_TAC not_in_A_gicper_lem ) >>
  `b NOTIN RPAR.Amap GICC` by ( IMP_RES_TAC not_in_A_gicper_lem ) >>
  `IS_SOME (Trans s a) /\ THE (Trans s a) IN RPAR.Amap (GUEST s)` by (
      METIS_TAC [Trans_axiom]
  ) >>
  `IS_SOME (Trans r b) /\ THE (Trans r b) IN RPAR.Amap (GUEST r)` by (
      METIS_TAC [Trans_axiom]
  ) >>
  `Trans s a = Trans r b` by (
      METIS_TAC [optionTheory.THE_DEF, 
		 optionTheory.IS_SOME_EXISTS,
		 optionTheory.SOME_11]
  ) >>
  `igc_chan(a,s,r) \/ igc_chan(b,r,s)` by (
      METIS_TAC [unshared_guest_mem_disj_lem] )
  >| [(* a *)
      FULL_SIMP_TAC std_ss [igc_chan_def]
      >| [(* s to r *)
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [] >>
	  MATCH_MP_TAC EQ_SYM >>
	  REWRITE_TAC [quantHeuristicsTheory.FST_PAIR_EQ] >>
	  `THE (Trans r b) IN 
	       RPAR.Amap (GUEST s) INTER RPAR.Amap (GUEST r)` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
	  ) >>
	  `THE (Trans r b) IN 
	       RPAR.A_IGC s r UNION RPAR.A_IGC r s UNION RPAR.Amap GICV` by (
	      METIS_TAC [refined_goodP_axiom]
	  ) >>
	  `THE (Trans r b) NOTIN RPAR.Amap GICV` by (
	      METIS_TAC [A_gicper_Trans_adr_lem, not_in_A_gicper_lem]
	  ) >>
	  THROW_AWAY_TAC ``a = FST x`` >>
	  `THE (Trans r b) IN RPAR.A_IGC s r \/ 
           THE (Trans r b) IN RPAR.A_IGC r s` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] ) 
	  >| [(* A_IGC s r *)
	      `?s''.  s'' < PAR.ns /\ (PAR.cpol s'' = (s,r)) /\ 
		      (b = SND (PAR.igca s''))` by ( 
	          METIS_TAC [Trans_axiom] 
	      ) >>
	      `s' = s''` suffices_by ( RW_TAC std_ss [] ) >>
	      CCONTR_TAC >>
	      METIS_TAC [cpol_inj, pairTheory.pair_CASES]
	      ,
	      (* A_IGC r s -> contradiction *)
	      `a IN A_IGCin s` by (
	          METIS_TAC [A_IGCin_Trans_lem]
	      )	>>
	      IMP_RES_TAC IGC_in_out_disj >>
	      METIS_TAC [pred_setTheory.IN_DISJOINT]
	     ]
	  ,
	  (* r to s -> contradiction *)
	  `a IN A_IGCin s` by (
	      FULL_SIMP_TAC std_ss [A_IGCin_def, GSPEC_f_lem] >>
	      HINT_EXISTS_TAC >>
	      RW_TAC std_ss [pairTheory.SND]
	  ) >>
	  IMP_RES_TAC IGC_in_out_disj >>
	  METIS_TAC [pred_setTheory.IN_DISJOINT]
	 ]
      ,
      (* b *)
      FULL_SIMP_TAC std_ss [igc_chan_def]
      >| [(* r to s -> contradiction *)
	  `THE (Trans r b) IN 
	       RPAR.Amap (GUEST s) INTER RPAR.Amap (GUEST r)` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
	  ) >>
	  `THE (Trans r b) IN 
	       RPAR.A_IGC s r UNION RPAR.A_IGC r s UNION RPAR.Amap GICV` by (
	      METIS_TAC [refined_goodP_axiom]
	  ) >>
	  `THE (Trans r b) NOTIN RPAR.Amap GICV` by (
	      METIS_TAC [A_gicper_Trans_adr_lem, not_in_A_gicper_lem]
	  ) >>
	  `THE (Trans r b) IN RPAR.A_IGC s r \/ 
           THE (Trans r b) IN RPAR.A_IGC r s` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] ) 
	  >| [(* A_IGC s r -> contradiction *)
	      `?s''.  s'' < PAR.ns /\ (PAR.cpol s'' = (s,r)) /\ 
		      (b = SND (PAR.igca s''))` by ( 
	          METIS_TAC [Trans_axiom] 
	      ) >>
	      `FST (PAR.igca s') <> SND (PAR.igca s'')` suffices_by (
	          FULL_SIMP_TAC std_ss []
	      ) >>
	      `s' <> s''` by (
	          CCONTR_TAC >>
		  REV_FULL_SIMP_TAC std_ss [] >>
		  `r = s` by ( METIS_TAC [pairTheory.PAIR_EQ] ) >>
		  METIS_TAC [goodP_axiom]
	      ) >>
	      `FST (PAR.cpol s') = SND (PAR.cpol s'')` by (
	          FULL_SIMP_TAC std_ss [pairTheory.FST, pairTheory.SND]
	      ) >>
	      METIS_TAC [goodP_axiom]
	      ,
	      (* A_IGC r s -> contradiction *)
	      `a IN A_IGCin s` by (
	          METIS_TAC [A_IGCin_Trans_lem]
	      )	>>
	      IMP_RES_TAC IGC_in_out_disj >>
	      METIS_TAC [pred_setTheory.IN_DISJOINT]
	     ]
	  ,
	  (* s to r *)
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [] >>
	  MATCH_MP_TAC EQ_SYM >>
	  REWRITE_TAC [quantHeuristicsTheory.SND_PAIR_EQ] >>
	  `THE (Trans s a) IN 
	       RPAR.Amap (GUEST s) INTER RPAR.Amap (GUEST r)` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
	  ) >>
	  `THE (Trans s a) IN 
	       RPAR.A_IGC s r UNION RPAR.A_IGC r s UNION RPAR.Amap GICV` by (
	      METIS_TAC [refined_goodP_axiom]
	  ) >>
	  `THE (Trans s a) NOTIN RPAR.Amap GICV` by (
	      METIS_TAC [A_gicper_Trans_adr_lem, not_in_A_gicper_lem]
	  ) >>
	  THROW_AWAY_TAC ``b = SND x`` >>
	  `THE (Trans s a) IN RPAR.A_IGC s r \/ 
           THE (Trans s a) IN RPAR.A_IGC r s` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] ) 
	  >| [(* A_IGC s r *)
	      `?s''.  s'' < PAR.ns /\ (PAR.cpol s'' = (s,r)) /\ 
		      (a = FST (PAR.igca s''))` by ( 
	          METIS_TAC [Trans_axiom] 
	      ) >>
	      `s' = s''` suffices_by ( RW_TAC std_ss [] ) >>
	      CCONTR_TAC >>
	      METIS_TAC [cpol_inj, pairTheory.pair_CASES]
	      ,
	      (* A_IGC r s -> contradiction *)
	      `a IN A_IGCin s` by (
	          METIS_TAC [A_IGCin_Trans_lem]
	      )	>>
	      IMP_RES_TAC IGC_in_out_disj >>
	      METIS_TAC [pred_setTheory.IN_DISJOINT]
	     ]
	 ]
     ]
);

(* Address translation function for peripherals of a given guest
exclude accesses to gic or other peripherals
*)

val _ = new_constant("Trgip", ``: num -> bool[36] -> bool[36] option``);

val Trgip_axiom = new_axiom("Trgip_axiom", ``
(* Translation only defined on each guest's ideal memory space *)
   (!g a. g < PAR.ng /\ a NOTIN PAR.A_G g ==> (Trgip g a = NONE))
(* GIC regions are not mapped *)
/\ (!g a A. g < PAR.ng /\ gicAR A /\ a IN RPAR.Amap A ==> (Trgip g a = NONE))
(* Peripherals are not mapped *)
/\ (!g a p. g < PAR.ng /\ p < PAR.np_g g /\ a IN PAR.A_gp g p ==>
		(Trgip g a = NONE))
(* Translation is injective for each guest *)
/\ (!g a a'. g < PAR.ng /\ a <> a' /\ Trgip g a <> NONE /\ Trgip g a' <> NONE ==>
		(Trgip g a) <> (Trgip g a'))
(* Translation maps into each guest's refined memory space, 
excluding GIC and peripherals *)
/\ (!g a. g < PAR.ng /\ a IN PAR.A_G g /\ ~(?A. gicAR A /\ a IN RPAR.Amap A) /\ 
	  ~(?p. p < PAR.np_g g /\ a IN PAR.A_gp g p) ==>
		IS_SOME (Trgip g a) /\ THE (Trgip g a) IN RPAR.Amap (GUEST g)
	     /\ (!p. p < RPAR.np ==> THE (Trgip g a) NOTIN RPAR.Amap (PER p))
	     /\ (!A. gicAR A ==> THE (Trgip g a) NOTIN RPAR.Amap A))
(* Translation for valid addresses equal to Trans *)
/\ (!g a. g < PAR.ng /\ a IN PAR.A_G g /\ ~(?A. gicAR A /\ a IN RPAR.Amap A) /\ 
	  ~(?p. p < PAR.np_g g /\ a IN PAR.A_gp g p) ==> (Trgip g a = Trans g a))
``);

val golden_RO_def = Define `golden_RO g = 
{SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = g)}
`;

val golden_RO_lem = store_thm("golden_RO_lem", ``
golden_RO g = receiverMem g
``,
  RW_TAC std_ss [golden_RO_def, receiverMem_def]
);

val golden_Trans_axiom = new_axiom("golden_Trans_axiom", ``
!g. g < PAR.ng ==> 
golden(GI g, MMU_GI g, RPAR.A_PT g, golden_RO g, Trans g) 
``);

val golden_Trgip_axiom = new_axiom("golden_Trgip_axiom", ``
!g. g < PAR.ng ==> 
golden(GIP g, SMMU_GI g, RPAR.A_PPT g, golden_RO g, Trgip g) 
``);

val Trgip_IS_SOME_lem = store_thm("Trgip_IS_SOME_lem", ``
!g a. 
   g < PAR.ng 
/\ IS_SOME(Trgip g a)
==>
   a IN PAR.A_G g 
/\ ~(?A. gicAR A /\ a IN RPAR.Amap A) 
/\ ~(?p. p < PAR.np_g g /\ a IN PAR.A_gp g p)
``,
  RW_TAC (srw_ss()) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >> (
      CCONTR_TAC >>
      METIS_TAC [Trgip_axiom]
  )
);

val Trgip_Trans_lem = store_thm("Trgip_Trans_lem", ``
!g a. 
   g < PAR.ng 
/\ IS_SOME(Trgip g a)
==>
((Trgip g a) = (Trans g a))
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC Trgip_IS_SOME_lem >>
  METIS_TAC [Trgip_axiom]
);

val Trgip_gicc_lem = store_thm("Trgip_gicc_lem", ``
!g a. 
   g < PAR.ng 
/\ IS_SOME(Trgip g a)
==>
a NOTIN RPAR.Amap GICC
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC Trgip_IS_SOME_lem >>
  METIS_TAC [gicAR_def]
);

val Trgip_gicd_lem = store_thm("Trgip_gicd_lem", ``
!g a. 
   g < PAR.ng 
/\ IS_SOME(Trgip g a)
==>
a NOTIN RPAR.Amap GICD
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC Trgip_IS_SOME_lem >>
  METIS_TAC [gicAR_def]
);

val Trgip_per_lem = store_thm("Trgip_per_lem", ``
!g a. 
   g < PAR.ng 
/\ IS_SOME(Trgip g a)
==>
(!p. p < PAR.np_g g ==> a NOTIN PAR.A_gp g p)
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC Trgip_IS_SOME_lem >>
  METIS_TAC []
);

(* images *)

val _ = new_constant("check_sig", ``: PAGE # haspoc_image -> bool``);
val _ = new_constant("secure_hash_256", ``: PAGE -> bool[256]``);

val _ = new_constant("IMG", ``:(HASPOC_IMAGES -> haspoc_image)``);
val _ = new_constant("packed_image", ``:(haspoc_image -> (bool[36] -> PAGE))``);
val _ = new_constant("ADR_hve0", ``:bool[64]``);


val goodIMG_axiom = new_axiom("goodIMG_axiom", ``
	(!img. good_image(IMG img))
     /\ (!img. range_i(IMG(img)) SUBSET RPAR.Amap(FLASH))
     /\ (!img img'. img <> img' ==> (range_i(IMG img) INTER range_i(IMG img') = EMPTY))
     /\	(!img a. ((IMG img).entry = SOME a) ==> (47><12)a IN range_d(IMG img))
     /\	(range_d(IMG IMG_RK) SUBSET RPAR.Amap BOOT)
     /\	((IMG IMG_RK).entry = NONE)
     /\	(range_d(IMG IMG_HV) SUBSET RPAR.Amap HV)
     /\	((IMG IMG_HV).entry = SOME ADR_hve0)
     /\	((IMG IMG_HV).EL = SOME 2)
     /\	(range_d(IMG IMG_HVconf) SUBSET RPAR.Amap HV)
     /\	((IMG IMG_RK).entry = NONE)
     /\	(!g. g<PAR.ng ==> range_d(IMG (IMG_G g)) SUBSET RPAR.Amap (GUEST g))
     /\	(!g. g<PAR.ng ==> ((IMG (IMG_G g)).entry = NONE))
     /\	(!g. g<PAR.ng ==> range_d(IMG (IMG_Gconf g)) SUBSET RPAR.Amap (GUEST g))
     /\	(!g. g<PAR.ng ==> ((IMG (IMG_Gconf g)).entry = NONE))
     /\	(range_d(IMG IMG_Mconf) SUBSET RPAR.Amap MC)
     /\	((IMG IMG_Mconf).EL = SOME 3)
     /\	(range_d(IMG IMG_BOOT) SUBSET RPAR.Amap BOOT)
     /\	((IMG IMG_BOOT).EL = SOME 3)
``);


(******************** IMAGES **********************)

val good_image_def = Define `good_image (img:haspoc_image) =
	((img.entry = NONE) <=> (img.EL = NONE))
	    `;

val range_i_def = Define `range_i (img:haspoc_image) =
	    \a:bool[36]. w2n img.adr <= w2n a /\ w2n a < w2n img.adr + img.isz
`;

val range_d_def = Define `range_d (img:haspoc_image) =
	    \a:bool[36]. w2n img.dadr <= w2n a /\ w2n a < w2n img.dadr + img.dsz
`;

val boot_image_def = Define `boot_image (i : HASPOC_IMAGES) = 
case i of
  | IMG_G g => g < PAR.ng
  | IMG_Gconf g => g < PAR.ng
  | _ => T
`;

val boot_images_present_def = Define `boot_images_present (m : bool[36] -> PAGE) = 
!i a. boot_image(i) /\ a >= 0w /\ a < n2w (IMG i).isz ==>
      (m ((IMG i).adr + a) = packed_image(IMG i) a)
`;

val boot_images_installed_def = Define `boot_images_installed (m : bool[36] -> PAGE) = 
!i a. boot_image(i) /\ a >= 0w /\ a < n2w (IMG i).dsz ==>
      (m ((IMG i).dadr + a) = (IMG i).data a)
`;

new_constant("install_boot_images", ``:(bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val install_boot_images_axiom = new_axiom("install_boot_images_axiom", ``
!m m'. (m' = install_boot_images m)  ==>
        boot_images_installed m
     /\ (!a img. boot_image(img) /\ a NOTIN range_d(IMG img) ==> (m' a = m a)) 
``);

val root_key_hash_def = Define `root_key_hash (m : bool[36] -> PAGE) = 
((((w2n((6><0)RPAR.a_rkh:bool[7])+1)*256-1) >< (w2n((6><0)RPAR.a_rkh:bool[7]) * 256))(m ((42><7)RPAR.a_rkh))):bool[256]
`; 

(* define boot success based on root key hash and signed images in memory *)
val boot_success_def = Define `boot_success (m : bool[36] -> PAGE) = 
   (secure_hash_256((IMG IMG_RK).data 0w) = root_key_hash(m))
/\ (!i. boot_image(i) /\ i <> IMG_RK ==> check_sig((IMG IMG_RK).data 0w, IMG i))
/\ boot_images_present m
`;

(******************** HYPERVISOR DATA STRUCTURES  **********************)

val _ = Datatype `HVDS = MBOX | POW | GLOCK | LIRQ | LLR | LIGC | GCPY num | GICDRPL | CTX num`;

val _ = new_constant("ADRDS", ``:(HVDS -> bool[36])``);

val good_hvds_def = Define `
   (good_hvds (GCPY g) = g < PAR.ng)
/\ (good_hvds (CTX c) = c < RPAR.nc)
/\ (good_hvds _ = T)
`;

(* too simplify, we assume that all are allocated on different pages *)
val ADRDS_axiom = new_axiom("ADRDS_axiom", ``
(* all data structures allocated in HV memory *)
	(!ds. good_hvds ds ==> ADRDS ds IN RPAR.Amap HV )
(* not overlapping with guest page tables *)
     /\ (!ds g. good_hvds ds ==> g < PAR.ng ==> ADRDS ds NOTIN RPAR.A_PT g)
(* not overlapping with peripheral page tables *)
     /\ (!ds per. good_hvds ds ==> per < RPAR.np ==> 
		  ADRDS ds NOTIN RPAR.A_PPT per)
(* all are allocated in different pages *)
     /\ (!ds ds'. good_hvds ds ==> good_hvds ds' ==> ds <> ds' ==> 
		  ADRDS ds <> ADRDS ds')
``);

val _ = Hol_datatype `guest_context =
  <| PC: bool[64];
     PSTATE: bool[32];
     GPR: GPRguest -> bool[64]
  |>`;

(* guest context abstraction *) 
val _ = new_constant("ctxs", ``:PAGE -> bool # num -> guest_context``);

val _ = new_constant("ctxs_upd", ``:bool # num # guest_context -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val ctxs_upd_axiom = new_axiom("ctxs_upd_axiom", ``
	!m b c x m'. (m' = ctxs_upd (b,c,x) m) ==>
		   (ctxs(m' (ADRDS (CTX c))) (b,c) = x)
		/\ (!c' b'. c' <> c ==> 
	(ctxs(m' (ADRDS (CTX c))) (b',c') = ctxs(m (ADRDS (CTX c))) (b',c)))
		/\ (!a. (a <> ADRDS (CTX c)) ==> (m' a = m a))
``);

(* recentrly receivied IRQs for each core *)
(* need implementation invariant that:
-- peripheral interrupts are allowed
-- SGIs are actually addressed to c and allowed
-- no IGC interrupts
*)
val _ = new_constant("lirq", ``:PAGE -> (num -> irqID)``);

val _ = new_constant("lirq_upd", ``:(num # irqID) -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val lirq_upd_axiom = new_axiom("lirq_upd_axiom", ``
	!m c q m'. (m' = lirq_upd (c,q) m) ==>
		   (lirq(m' (ADRDS LIRQ)) c = q)
		/\ (!c'. c' <> c ==> 
			(lirq(m' (ADRDS LIRQ)) c = lirq(m (ADRDS LIRQ)) c))
		/\ (!a. (a <> ADRDS LIRQ) ==> (m' a = m a))
``);

val _ = new_constant("llr", ``:PAGE -> (num -> bool[32])``);

val _ = new_constant("llr_upd", ``:(num # bool[32]) -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val llr_upd_axiom = new_axiom("llr_upd_axiom", ``
	!m c x m'. (m' = llr_upd (c,x) m) ==>
		   (llr(m' (ADRDS LLR)) c = x)
		/\ (!c'. c' <> c ==> 
			(llr(m' (ADRDS LLR)) c = llr(m (ADRDS LLR)) c))
		/\ (!a. (a <> ADRDS LLR) ==> (m' a = m a))
``);

(* recently received IGC interrupts for each core, channel and core number *)
(* need implementation invariant that:
-- channel numbers and core indices are in range
-- sender core matches channel ID  
-- channel ID  is allowed for receiver
*)
val _ = new_constant("ligc", ``:PAGE -> (num -> (num # num) option)``);

val _ = new_constant("ligc_upd", ``:(num # (num # num) option) -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val ligc_upd_axiom = new_axiom("ligc_upd_axiom", ``
	!m c x m'. (m' = ligc_upd (c,x) m) ==>
		   (ligc(m' (ADRDS LIGC)) c = x)
		/\ (!c'. c' <> c ==> 
			(ligc(m' (ADRDS LIGC)) c = ligc(m (ADRDS LIGC)) c))
		/\ (!a. (a <> ADRDS LIGC) ==> (m' a = m a))
``);

(* abstracting from specific message box implementation here *)
val _ = new_constant("mbox", ``:PAGE -> (num # num -> bool)``);

val _ = new_constant("mbox_upd", ``:(num # num -> bool) -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val mbox_upd_axiom = new_axiom("mbox_upd_axiom", ``
	!m x m'. (m' = mbox_upd x m) ==>
		   (mbox(m' (ADRDS MBOX)) = x)
		/\ (!a. (a <> ADRDS MBOX) ==> (m' a = m a))
``);

(* power state structure to keep track of active cores *)
val _ = new_constant("pow", ``:PAGE -> (num -> bool)``);

val _ = new_constant("pow_upd", ``:(num -> bool) -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val pow_upd_axiom = new_axiom("pow_upd_axiom", ``
	!m x m'. (m' = pow_upd x m) ==>
		   (pow(m' (ADRDS POW)) = x)
		/\ (!a. (a <> ADRDS POW) ==> (m' a = m a))
``);

(* GICD local copies for each guest *)
val _ = new_constant("gcpys", ``:PAGE -> (num # GICDreg -> bool[32])``);

val _ = new_constant("gcpys_upd", ``:num # GICDreg # bool[32] -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);
val _ = new_constant("gcpys_init",``:(bool[36] -> PAGE) -> (bool[36] -> PAGE)``);


val gcpys_upd_axiom = new_axiom("gcpys_upd_axiom", ``
	!m g r x m'. (m' = gcpys_upd (g,r,x) m) ==>
		   (gcpys(m' (ADRDS (GCPY g))) (g,r) = x)
		/\ (!g' r'. (g' <> g \/ r' <> r) ==> 
	(gcpys(m' (ADRDS (GCPY g))) (g',r') = gcpys(m (ADRDS (GCPY g))) (g,r)))
		/\ (!a. (a <> ADRDS (GCPY g)) ==> (m' a = m a))
``);

val gcpys_init_axiom = new_axiom("gcpys_init_axiom", ``
	!m g m'. (m' = gcpys_init m) ==>
		   (gcpys(m' (ADRDS (GCPY g))) (g,r) = GICDinit r)
		/\ (!a. (a <> ADRDS (GCPY g)) ==> (m' a = m a))
``);


(* global GICD lock *)
val _ = new_constant("Glock", ``:PAGE -> num option``);

val _ = new_constant("Glock_upd", ``:num option -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val Glock_upd_axiom = new_axiom("Glock_upd_axiom", ``
	!m x m'. (m' = Glock_upd x m) ==>
		   (Glock(m' (ADRDS GLOCK)) = x)
		/\ (!a. (a <> ADRDS GLOCK) ==> (m' a = m a))
``);

(* virtualized GICD reply *)
val _ = new_constant("GICDrpl", ``:PAGE -> num -> reply``);

val _ = new_constant("GICDrpl_upd", ``:(num # reply) -> (bool[36] -> PAGE) -> (bool[36] -> PAGE)``);

val GICDrpl_upd_axiom = new_axiom("GICDrpl_upd_axiom", ``
	!m c q m'. (m' = GICDrpl_upd (c,q) m) ==>
		   (GICDrpl(m' (ADRDS GICDRPL)) c = q)
		/\ (!c'. c' <> c ==> 
	(GICDrpl(m' (ADRDS GICDRPL)) c = GICDrpl(m (ADRDS GICDRPL)) c))
		/\ (!a. (a <> ADRDS GICDRPL) ==> (m' a = m a))
``);


val ADRDS_unchanged_lem = store_thm("ADRDS_unchanged_lem", ``
!m:(bool[36] -> PAGE) m' ds.
   (!a. a IN RPAR.Amap HV ==> (m' a = m a))
/\ good_hvds ds
==>
(m' (ADRDS ds) = m (ADRDS ds))
``,
  REPEAT STRIP_TAC >>
  `ADRDS ds IN RPAR.Amap HV` by ( METIS_TAC [ADRDS_axiom] ) >>
  METIS_TAC []
);

val hvds_unchanged_lem = store_thm("hvds_unchanged_lem", ``
!m:(bool[36] -> PAGE) m'.
   (!a. a IN RPAR.Amap HV ==> (m' a = m a))
==>
   (!b c. c < RPAR.nc ==>
	  (ctxs(m' (ADRDS (CTX c))) (b,c) = ctxs(m (ADRDS (CTX c))) (b,c)))
/\ (!c. lirq(m' (ADRDS LIRQ)) c = lirq(m (ADRDS LIRQ)) c)
/\ (!c. llr(m' (ADRDS LLR)) c = llr(m (ADRDS LLR)) c)
/\ (!c. ligc(m' (ADRDS LIGC)) c = ligc(m (ADRDS LIGC)) c)
/\ (mbox(m' (ADRDS MBOX)) = mbox(m (ADRDS MBOX)))
/\ (pow(m' (ADRDS POW)) = pow(m (ADRDS POW)))
/\ (!g r. g < PAR.ng ==>
          (gcpys(m' (ADRDS (GCPY g))) (g,r) = gcpys(m (ADRDS (GCPY g))) (g,r)))
/\ (Glock(m' (ADRDS GLOCK)) = Glock(m (ADRDS GLOCK)))
/\ (!c. GICDrpl(m' (ADRDS GICDRPL)) c = GICDrpl(m (ADRDS GICDRPL)) c)
``,
  RW_TAC (srw_ss()) []
  >| [`good_hvds (CTX c)` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds LIRQ` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds LLR` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds LIGC` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds MBOX` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds POW` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds (GCPY g)` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds GLOCK` by ( RW_TAC (srw_ss()) [good_hvds_def] )
      ,
      `good_hvds GICDRPL` by ( RW_TAC (srw_ss()) [good_hvds_def] )
     ]
  >> ( METIS_TAC [ADRDS_unchanged_lem] )
);


(*************** HV abstraction ***************)

(* TODO: take only hypervisor memory to simplify proofs *)
val HVabs_def = Define `HVabs (M : refined_model, c : num) =
	<| C := refcore_abs(M.C c); req_sent:= refcore_req_sent(M.C c); m := mem_abs(M.m); MMU := mmu_abs (M.MMU c); SMMU := \p. mmu_abs (M.SMMU p)|> : hv_state
                `;

val HVupd_def = Define `HVupd (M : refined_model, hv : hv_state, c : num) =
   M with <| C := (c =+ refcore_upd(M.C c,hv.C,hv.req_sent)) M.C; 
	     m := memory_set_upd (RPAR.Amap HV,hv.m) M.m; 
             MMU := (c =+ mmu_upd(M.MMU c, hv.MMU)) M.MMU; 
	     SMMU := \p. mmu_upd(M.SMMU p, hv.SMMU p)|> 
`;

(* HV update only updates state of core c, HV memory and SMMUs, rest unchanged *)

val HVupd_unchanged_lem = store_thm("HVupd_unchanged_lem", ``
!M hv c M'. (M' = HVupd(M,hv,c)) ==> 
		  (M'.GIC = M.GIC) 
	       /\ (M'.P = M.P)
	       /\ (M'.E_in = M.E_in)
	       /\ (M'.E_out = M.E_out)
	       /\ (mem_req_rcvd M'.m = mem_req_rcvd M.m)
	       /\ (mem_req_sent M'.m = mem_req_sent M.m)
	       /\ (mem_rpl_rcvd M'.m = mem_rpl_rcvd M.m)
               /\ (!c'. (c <> c') ==> (M'.C c' = M.C c') /\ (M'.MMU c' = M.MMU c')) 
               /\ (!a. a NOTIN RPAR.Amap HV ==> (mem_abs(M'.m) a = mem_abs(M.m) a)) 
``,   ASSUME_TAC memory_set_upd_axiom
      THEN RW_TAC (srw_ss()) [HVupd_def]
      THEN EVAL_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
);


(*************** Hypervisor Transition System ****************)

(* disjoint HV program positions *)

val _ = Datatype `HV_CODE = PC_LOOP | PC_SLEEP | PC_INIT_PRIM_ENTRY | PC_INIT_PRIM | PC_INIT_GUEST | PC_INIT_CORE | PC_INIT_SEC_ENTRY | PC_GICD_SAVE_CTX | PC_GICD_ACCESS | PC_GICD_FILTER | PC_ASYNC_SND_ACK | PC_ASYNC_RCV_ACK | PC_IRQ_SND_EOI | PC_IRQ_RCV_EOI | PC_IRQ_SND_CHECK | PC_IRQ_RCV_CHECK | PC_IRQ_SND_INJECT | PC_IRQ_RCV_INJECT | PC_IRQ_RETURN | PC_IRQ_SND_DEACT | PC_IRQ_RCV_DEACT | PC_SIGC_SND_SGI | PC_SIGC_RCV_SGI | PC_SIGC_RETURN | PC_RIGC_SND_EOI | PC_RIGC_RCV_EOI | PC_RIGC_SND_CHECK | PC_RIGC_RCV_CHECK | PC_RIGC_SND_INJECT | PC_RIGC_RCV_INJECT | PC_RIGC_SND_DEACT | PC_RIGC_RCV_DEACT | PC_RIGC_RETURN | VBAR | VBAR_PSCI`;

(* virtual HV addresses for these locations, we assume the hypervisor uses an identity mapping for simplicity, modulo ASIDs and VMIDs *) 
val _ = new_constant("AHV", ``:HV_CODE -> bool[64]``);

val AHV_axiom = new_axiom("AHV_axiom", ``
(* all HV positions in HV memory *)
     (!p. (47><12)(AHV p) IN RPAR.Amap HV)
(* all word alligned *)
  /\ (!p. (1 >< 0)(AHV p) = 0w:bool[2])
(* all disjoint but within the same address space  *)
  /\ (!p p'. p <> p' ==> AHV p <> AHV p' )
  /\ (!p p'. p <> p' ==> ((63><48)(AHV p):bool[16] = (63><48)(AHV p'):bool[16]))
(* non lying within the 2K HV exception vector table *)
  /\ (!p. p <> VBAR ==> (47><11)(AHV p):bool[37] <> (47><11)(AHV VBAR):bool[37])
(* non lying within the 2K PSCI exception vector table *)
  /\ (!p. p <> VBAR_PSCI ==> (47><11)(AHV p):bool[37] <> (47><11)(AHV VBAR_PSCI):bool[37])
(* VBAR addresses are 2K aligned *)
  /\ ((10 >< 0)(AHV VBAR) = 0w:bool[11])
  /\ ((10 >< 0)(AHV VBAR_PSCI) = 0w:bool[11])
(* HV entrypoint as defined before *)
  /\ (AHV PC_INIT_PRIM_ENTRY = ADR_hve0)
(* HV addresses do not coincide with reset address *)
  /\ !c p. AHV p <> (Creset c).SPR(INR RVBAR_EL3)
``);

val AHV_corollaries = store_thm(
   "AHV_corollaries", 
   `` (!p. AHV p <> AHV VBAR + 0x400w)
    /\(!p. AHV p <> AHV VBAR + 0x480w)`` ,
     METIS_TAC [still_different_after_add_lem, AHV_axiom, different_after_add_lem]);

val AHV_inj = store_thm("AHV_inj", ``
!p p'. p <> p' ==> AHV p <> AHV p'
``,
    METIS_TAC [AHV_axiom]
);


(* reverse lookup *)
val _ = new_constant("revAHV", ``:bool[64] -> HV_CODE option``);

val coreID_def = Define `coreID (C : refcore_config) = core_id(C.SPR(INL MPIDR_EL1))`;

val Creset_axiom = new_axiom("Creset_axiom", ``
!c.  (Creset c).active 
  /\ ((Creset c).PC = (Creset c).SPR(INR RVBAR_EL3))
  /\ (core_id((Creset c).SPR(INL(MPIDR_EL1))) = c) 
  /\ (MODE((Creset c).PSTATE) = 3)
  /\ ~(Creset c).H.init_boot
  /\ ~(Creset c).H.init_hv
  /\ ~(Creset c).H.init_guest
  /\ ~(Creset c).H.init_core
  /\ ~(Creset c).H.launched
``);

val CGreset_axiom = new_axiom("CGreset_axiom", ``
!g c. (CGreset(g,c)).active
(* emulate core id, probably more necessary but we omit it here *) 
   /\ (core_id((CGreset(g,c)).SPR(INL MPIDR_EL1)) = c) 
   /\ (MODE((CGreset(g,c)).PSTATE) = 1)
   /\ ((CGreset(g,c)).PC = THE (IMG (IMG_G g)).entry)
``);

val revAHV_axiom = new_axiom("revAHV_axiom", ``
   (!p. revAHV (AHV p) = SOME p)
/\ (!pc. ~(?p'. AHV p' = pc) ==> (revAHV pc = NONE))
``);

val warm_soft_axiom = new_axiom("warm_soft_axiom", ``
!C. ~(warm C /\ soft C)
 /\ (warm C \/ soft C ==> 
			 (47><12) C.PC IN RPAR.Amap BOOT 
		      /\ C.PC <> C.SPR(INR RVBAR_EL3)
		      /\ C.PC <> AHV PC_LOOP
		      /\ C.PC <> AHV PC_SLEEP
                      /\ (!p. C.PC <> AHV p)
		      /\ (mode C = 3)
		      /\ C.active)
``);


val revAHV_boot_lem = store_thm("revAHV_boot_lem", ``
!C c. ((C = Creset c) \/ warm C \/ soft C) ==> (revAHV C.PC = NONE)
``,
  REPEAT STRIP_TAC >- (
      (* Creset *)
      RW_TAC std_ss [Creset_axiom] >>
      METIS_TAC [revAHV_axiom, AHV_axiom]
  ) >> (
      (* warm / soft *)
      METIS_TAC [warm_soft_axiom, revAHV_axiom, AHV_axiom]
  )   
);


(* creating finite lists of events *)

(* (reverse) list of natural numbers < n for which f holds *)
val enum_list_def = Define `
   (enum_list f 0 = NIL)
/\ (enum_list f (SUC n) = if f n then n :: enum_list f n else enum_list f n)
`;

val power_up_list_def = Define `power_up_list(f : num -> bool) =  
MAP (\c. StartCore c) (enum_list f RPAR.nc)
`;

(* add history information to core update *)

val refcore_upd_axiom = new_axiom("refcore_upd_axiom", ``
!C core R C'. (C' = refcore_upd (C,core,R)) ==>
              (refcore_abs C' = core with <|H := 
	<|init_boot := ((refcore_abs C).H.init_boot \/ 
			((mode core = 3) /\ 
			 (core.PC <> core.SPR(INR RVBAR_EL3)) /\ 
			 (core.PC <> AHV PC_LOOP)));
	  init_hv := ((refcore_abs C).H.init_hv \/ 
		        ((mode core = 3) /\ (core.PC = AHV PC_INIT_PRIM)));
	  init_guest := ((refcore_abs C).H.init_guest \/ 
		        ((mode core = 3) /\ (core.PC = AHV PC_INIT_GUEST)));
	  init_core := ((refcore_abs C).H.init_core \/
		        ((mode core = 3) /\ (core.PC = AHV PC_INIT_CORE)));
	  launched := ((refcore_abs C).H.launched \/ mode core < 2)|> |>)
	   /\ (refcore_req_sent C' = R)
	   /\ (ref_abs_int C' = FLUSHED)
``);

val refcore_upd_axiom' = save_thm("refcore_upd_axiom'", (* for the simplifier a version without C' *)
       SPEC_ALL refcore_upd_axiom
    |> SIMP_RULE bool_ss [] 
    |> EXISTS_IMP ``C':refcore``
    |> SIMP_RULE bool_ss []);

val mode_refcore_upd_lem = store_thm("mode_refcore_upd_lem",
    ``mode (refcore_abs (refcore_upd (_, absC , _))) = mode absC``,
    SIMP_TAC (srw_ss()) [refcore_upd_axiom', mode_def]);

val mode_refcore_upd_lem2 = store_thm("mode_refcore_upd_lem2",
    ``mode (refcore_abs (refcore_upd (C, refcore_abs C with <| PC := pc ; PSTATE := pstate; GPR := gpr |>, _)))
      = MODE pstate``,
    SIMP_TAC (srw_ss()) [refcore_upd_axiom', mode_def]);
 

(* state and rule definitions *)

(* Boot & Initialization *)

val hv_state_reset_def = Define `hv_state_reset (hv:hv_state) = 
   (hv.C = Creset (coreID (hv.C))) 
/\ (hv.req_sent = EMPTY) 
/\ (hv.C.PC = hv.C.SPR(INR RVBAR_EL3))
/\ (mode (hv.C) = 3)
`;

val hv_guard_init_abort_def = Define `
hv_guard_init_abort (hv:hv_state, c : num) =
hv_state_reset hv /\ (c = 0) /\ ~boot_success(hv.m)
`;

val hv_rule_init_abort_def = Define `
hv_rule_init_abort (hv:hv_state) =
hv with <|C := (hv.C with <|PC := AHV PC_LOOP|>)|> 
`;

val hv_guard_loop_def = Define `
hv_guard_loop (hv:hv_state, c:num) =
   ((hv.C.PC = AHV PC_LOOP) \/ (hv.C.PC = AHV PC_SLEEP)) /\ 
   (mode(hv.C) = 3) /\ (hv.req_sent = EMPTY)
`;

val hv_rule_loop_def = Define `
hv_rule_loop (hv:hv_state) = hv
`;

val hv_guard_init_prim_cold_def = Define `
hv_guard_init_prim_cold (hv:hv_state, c:num) =
hv_state_reset hv /\ (c = 0) /\ boot_success(hv.m)
`;

val hv_rule_init_prim_cold_def = Define `
hv_rule_init_prim_cold (hv:hv_state) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_PRIM_ENTRY;
			    SPR := (((INR SCR_EL3) =+ 0b10100000001w:bool[64]) o
				   ((INR VBAR_EL3) =+ AHV VBAR_PSCI)) hv.C.SPR;
			    PSTATE := MODE_upd(hv.C.PSTATE, 2)|>);
          m := install_boot_images (hv.m)|>
`;			    

val hv_guard_init_prim_init_def = Define `
hv_guard_init_prim_init (hv:hv_state, c:num) =
   (hv.C.PC = AHV PC_INIT_PRIM_ENTRY) 
/\ (mode(hv.C) = 2) 
/\ (c = 0) 
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_init_prim_init_def = Define `
hv_rule_init_prim_init (hv:hv_state) =
(hv with <|C := (hv.C with <|PC := AHV PC_INIT_PRIM|>);
           m := (Glock_upd NONE o
		 mbox_upd (\g,g'.F) o
		 gcpys_init o
                 pow_upd (\c.(PCC c = 0) /\ c>0)) hv.m|>,
power_up_list (\c.(PCC c = 0) /\ c>0))
`;			    

val hv_guard_init_guest_def = Define `
hv_guard_init_guest (hv:hv_state) =
   (hv.C.PC = AHV PC_INIT_PRIM) 
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_init_guest_def = Define `
hv_rule_init_guest (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_GUEST|>);
          m := \a. if a IN RPAR.A_PT (PCG c) then GI (PCG c) a
                   else if a IN RPAR.A_PPT (PCG c) then GIP (PCG c) a
		   else hv.m a;
	  SMMU := \p. if (PPG p = PCG c) then 
		<|active := T; state := \r. IDLE; cfg := SMMU_GI (PCG c)|>
		      else hv.SMMU p|>
`;			    

val hv_guard_init_core_def = Define `
hv_guard_init_core (hv:hv_state) =
   (hv.C.PC = AHV PC_INIT_GUEST) /\ (mode(hv.C) = 2) /\ (hv.req_sent = EMPTY)
`;

val hv_rule_init_core_def = Define `
hv_rule_init_core (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_CORE;
			    SPR := ((INR HCR_EL2 =+ 0x800F803Fw) o
				    (INR VBAR_EL2 =+ AHV VBAR)) hv.C.SPR|>);
          m := (ligc_upd (c, NONE) o
	        lirq_upd (c, PIR 1023)) hv.m;
	  MMU := <|active := T; state := \r. IDLE; cfg := MMU_GI (PCG c)|> |>
`;			    

val hv_guard_init_launch_def = Define `
hv_guard_init_launch (hv:hv_state) =
   (hv.C.PC = AHV PC_INIT_CORE) /\ (mode(hv.C) = 2) /\ (hv.req_sent = EMPTY)
`;

val hv_rule_init_launch_def = Define `
hv_rule_init_launch (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|active := T;
			    PC := (CGreset(PCG c,PCC c)).PC;
			    GPR := (CGreset(PCG c,PCC c)).GPR;
			    SPR := \r. case r of
	                     | INL R => (CGreset(PCG c,PCC c)).SPR r
	                     | INR R => hv.C.SPR r;
			    PSTATE := (CGreset(PCG c,PCC c)).PSTATE |>)|>
`;			    

val hv_guard_init_sec_cold_def = Define `
hv_guard_init_sec_cold (hv:hv_state, c : num) =
hv_state_reset hv /\ (c <> 0)
`;

val hv_rule_init_sec_cold_def = Define `
hv_rule_init_sec_cold (hv:hv_state, c:num) =
(hv with <|C := (hv.C with 
                 <|PC := AHV PC_SLEEP;
		   SPR := (((INR SCR_EL3) =+ 0b10100000001w:bool[64]) o
 		 	   ((INR VBAR_EL3) =+ AHV VBAR_PSCI)) hv.C.SPR|>)|>,
[StopCore c])
`;			    

val hv_guard_init_warm_def = Define `
hv_guard_init_warm (hv:hv_state, c : num) = 
   warm(hv.C) 
/\ (c <> 0) 
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_init_warm_def = Define `
hv_rule_init_warm (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_SEC_ENTRY;
			    PSTATE := MODE_upd(hv.C.PSTATE, 2)|>)|>
`;			    

val hv_guard_init_sec_prim_def = Define `
hv_guard_init_sec_prim (hv:hv_state, c : num) =
   (hv.C.PC = AHV PC_INIT_SEC_ENTRY) 
/\ (mode(hv.C) = 2) 
/\ (PCC c = 0)
/\ (hv.req_sent = EMPTY)

`;

val hv_rule_init_sec_prim_def = Define `
hv_rule_init_sec_prim (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_PRIM|>)|>
`;			    

val hv_guard_init_sec_sec_def = Define `
hv_guard_init_sec_sec (hv:hv_state, c : num) =
   (hv.C.PC = AHV PC_INIT_SEC_ENTRY) 
/\ (mode(hv.C) = 2) 
/\ (PCC c <> 0)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_init_sec_sec_def = Define `
hv_rule_init_sec_sec (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_GUEST|>)|>
`;			    

val hv_guard_init_soft_def = Define `
hv_guard_init_soft (hv:hv_state) = soft(hv.C) /\ (hv.req_sent = EMPTY)

`;

val hv_rule_init_soft_def = Define `
hv_rule_init_soft (hv:hv_state, c:num) =
hv with <|C := (hv.C with <|PC := AHV PC_INIT_CORE;
			    PSTATE := MODE_upd(hv.C.PSTATE, 2)|>)|>
`;			    

(* Power Control SMC Handlers *)

val hv_smc_entry_state_def = Define `
hv_smc_entry_state (hv:hv_state) = 
   (hv.C.PC = AHV VBAR + 0x400w) 
/\ (mode(hv.C) = 2) 
/\ ((31><26)(hv.C.SPR(INR ESR_EL2)) = 0b010111w:bool[6])
/\ (hv.req_sent = EMPTY)
`;

val hv_guard_smc_issue_def = Define `
hv_guard_smc_issue (hv:hv_state, c:num) = 
hv_smc_entry_state hv /\
!e. MEM e (decsmc ((15><0)(hv.C.SPR(INR ESR_EL2)))) ==>
    case e of 
      | StartCore c' => c' < PAR.nc_g (PCG c)
      | StopCore c' => c' < PAR.nc_g (PCG c)
      | _ => F
`;

val hv_rule_smc_issue_def = Define `
hv_rule_smc_issue (hv:hv_state) =
let 
    cmd = (decsmc ((15><0)(hv.C.SPR(INR ESR_EL2))))
in
    (hv with <|C := (hv.C with <|PC := hv.C.SPR(INR ELR_EL2);
			         PSTATE := (31><0)(hv.C.SPR(INR SPSR_EL2))|>);
               m := pow_upd (\c. if MEM (StartCore c) cmd then T
			         else if MEM (StopCore c) cmd then F
				 else pow (hv.m (ADRDS POW)) c) hv.m|>,
     cmd)
`;			    

val hv_guard_smc_deny_def = Define `
hv_guard_smc_deny (hv:hv_state, c:num) = 
hv_smc_entry_state hv /\
?e c'. MEM e (decsmc ((15><0)(hv.C.SPR(INR ESR_EL2))))
    /\ ((e = StartCore c') \/ (e = StopCore c')) 
    /\ c' >= PAR.nc_g (PCG c)
`;

val hv_rule_smc_deny_def = Define `
hv_rule_smc_deny (hv:hv_state) =
hv with <|C := (hv.C with <|PC := hv.C.SPR(INR ELR_EL2);
			    PSTATE := (31><0)(hv.C.SPR(INR SPSR_EL2))|>)|>
`;			    

(* GIC Distributor Virtualization *)

(* dummy message info for hypervisor requests *)
val _ = new_constant("dummy_info", ``:msginfo``);


(* GICDfltr and GICDwconv axioms 
- if gicd only contains filtered values for guest g, then only its g's pending
- filter on gicd preserves all interrupts of g, but mask active SGIs
- dmask and idmask are the same for hypervisor GICC conf
- update with converted value yields same result as ideal update on filtered value
- converted requests preserve golden configuration
*)

val gicdfltr_pistate_axiom = new_axiom("gicdfltr_pistate_axiom", ``
gicdfltr_pqq_coupling(GICDfltr,PQQ)
``);

val gicdfltr_mask_axiom = new_axiom("gicdfltr_mask_axiom", ``
!g gicd gicd' gicc q. 
   gicd IN gic_gm_conf /\ inv_gicc gicc 
/\ (!r. gicd' r = GICDfltr(g,r, gicd r)) 
==>
(!c. (PCG c = g) ==> (idmsk(gicd', PCC c) = dmsk(gicd, gicc, c)))
``);

(* filtered ideal update equivalent to ideal update of filtered value
also update does not affect other guests view of distributor *)
val gicdfltr_wconv_upd_axiom = new_axiom("gicdfltr_wconv_upd_axiom", ``
!g r u v. 
(GICDfltr(g,r, GICDupd(r,u,GICDwconv(g,r,v))) = 
 idGICDupd g (r,GICDfltr(g,r,u),v) )
/\
(!g'. g' <> g ==> 
      (GICDfltr(g',r, GICDupd(r,u,GICDwconv(g,r,v))) = GICDfltr(g',r,u)) )
``);




(* extend on requests and replies *)

val GICDreqconv_def = Define `GICDreqconv(g:num, r:request) =
case r of
  | Write a d v i => if (47><12)a IN RPAR.Amap GICD /\ 
			IS_SOME (decgicd ((11><0)a)) 
		     then Write a d (w2v(GICDwconv(g,THE(decgicd((11><0)a)),v2w(v)))) i
		     else r
  | _ => r
`;

val GICDrplconv_def = Define `GICDrplconv(g:num, q:reply) =
case q of
  | ReadValue (Read a d i) v => if (47><12)a IN RPAR.Amap GICD /\ 
			    IS_SOME (decgicd ((11><0)a)) 
			 then ReadValue (Read a d i) (w2v(GICDfltr(g,THE(decgicd((11><0)a)),v2w(v))))
	                 else q
  | WrittenValue (Write a d v i) => if (47><12)a IN RPAR.Amap GICD /\ 
			       IS_SOME (decgicd ((11><0)a)) 
			    then WrittenValue (Write a d (w2v(GICDwconv(g,THE(decgicd((11><0)a)),v2w(v)))) i)
			    else q
  | _ => q
`;

val GICDrplconv_preserves_Rreq_Wreq_lem = store_thm(
   "GICDrplconv_preserves_Rreq_Wreq_lem",
   ``  (Rreq (ReqOf q) = Rreq (ReqOf (GICDrplconv(g:num, q:reply))))
    /\ (Wreq (ReqOf q) = Wreq (ReqOf (GICDrplconv(g:num, q:reply))))``,
   Cases_on `q` THEN 
   Cases_on `r` THEN
   SIMP_TAC (srw_ss()++normalForms.cond_lift_SS)  [GICDrplconv_def, Rreq_def, Wreq_def, ReqOf_def]);

val GICDreqconv_PAdr_lem = store_thm("GICDreqconv_PAdr_lem", ``
!g r. PAdr (GICDreqconv(g,r)) = PAdr r
``,
  RW_TAC (srw_ss()) [] THEN 
  Cases_on `r` THEN (
      RW_TAC (srw_ss()) [GICDreqconv_def, PAdr_def, Adr_def] )
);

val gic_golden_conf_upd_axiom = new_axiom("golden_conf_upd_axiom", ``
!r r' g G q id G'. 
   ((r = GICDreqconv(g,r')) \/ PAdr r NOTIN RPAR.Amap GICD)
/\ (gic_abs G).gicd IN gic_gm_conf
/\ gic_step_snd_rpl(G,q,id,G')
/\ (r,id) IN gic_req_rcvd G
/\ match(r,q)
==>
   (gic_abs G').gicd IN gic_gm_conf
/\ (!irq. (PQQ g irq) NOTIN PIRQ g UNION IPIRQ g ==>
	  ((irqstate (gic_abs G').gicd) irq = (irqstate (gic_abs G).gicd) irq) )
``);

(* when the GIC distributor has to be accessed directly *)
val req_gicd_def = Define `
req_gicd (r:GICDreg, w:bool) = 
case r of
  | CONST R => F
  | MUTE R => w
  | VOL R => T
`;

val req_gicd_F_lem = store_thm("req_gicd_F_lem", ``
!r. req_gicd(r,F) <=> ?R. r = VOL R
``,
  Cases >> ( RW_TAC (srw_ss()) [req_gicd_def] )
);


val reqgicd_def = Define `
reqgicd (off:bool[12], w:bool) = req_gicd(THE(decgicd off), w)
`;

val request_gicd_def = Define `request_gicd r = 
case r of
  | Read a d i => reqgicd ((11><0)a,F)
  | Write a d v i => reqgicd ((11><0)a,T)
  | _ => F
`;


(* when the write access needs to update the local copy *)
val upd_gicd_def = Define `
upd_gicd (r:GICDreg) = 
case r of
  | CONST R => F
  | MUTE R => T
  | VOL R => F
`;
val updgicd_def = Define `
updgicd (off:bool[12]) = upd_gicd(THE(decgicd off))
`;



(* GICDfltr does not change for passive guests when GIC receives interrupt *)
val gic_rcv_irq_gicdfltr_axiom = new_axiom("gic_rcv_irq_gicdfltr_axiom", ``
!G n G' g r. gic_step_rcv_irq(G,PIR n,G') ==> 
             (PIR n) NOTIN PIRQ g ==> 
             req_gicd(r,F) ==>
             (GICDfltr (g, r, (gic_abs G').gicd r) = GICDfltr (g, r, (gic_abs G).gicd r))``);


(* bisimulation axiom for GICDfltr when GICs receive interrupts *)
val gic_rcv_irq_bisim_axiom = new_axiom("gic_rcv_irq_bisim_axiom",
   `` !iGIC iGIC' n rGIC rGIC' r g.
      idgic_step_rcv_irq(iGIC, PIR n, g, iGIC') /\ gic_step_rcv_irq(rGIC, PIR n, rGIC')
      /\ req_gicd(r,F) /\ ((idgic_abs iGIC).gicd r = GICDfltr(g,r, (gic_abs rGIC).gicd r))
      ==>
      ((idgic_abs iGIC').gicd r = GICDfltr (g, r, (gic_abs rGIC').gicd r))``);




val hv_gicd_entry_state_def = Define `
hv_gicd_entry_state (hv:hv_state) = 
   (hv.C.PC = AHV VBAR + 0x400w) 
/\ (mode(hv.C) = 2) 
/\ ((31><26)(hv.C.SPR(INR ESR_EL2)) = 0b100100w:bool[6])
/\ ((39><4)(hv.C.SPR(INR HPFAR_EL2)) = Agicd)
/\ (hv.req_sent = EMPTY)
`;

val hv_guard_gicd_fail_def = Define `
hv_guard_gicd_fail (hv:hv_state) = 
hv_gicd_entry_state hv /\
(  failgicd((11><0)(hv.C.SPR(INR FAR_EL2)),
	    ~word_bit 23(hv.C.SPR(INR ESR_EL2)),
	    word_bit 6 (hv.C.SPR(INR ESR_EL2)))
\/ iss_gicd_not_supported((31><0)(hv.C.SPR(INR ESR_EL2))) )
`;

val hv_rule_gicd_fail_def = Define `
hv_rule_gicd_fail (hv:hv_state) =
let 
    spsr = hv.C.SPR(INR SPSR_EL2) 
in
    hv with <|C := (hv.C with <|PC := hv.C.SPR(INL VBAR_EL1) + ghoff spsr;
			        PSTATE := MODE_upd(hv.C.PSTATE, 1);
			        SPR := (
		((INL SPSR_EL1) =+ spsr) o
		((INL ELR_EL1) =+ hv.C.SPR(INR ELR_EL2)) o
		((INL ESR_EL1) =+ if word_bit 2 spsr
				  then 0x96000000w:bool[64]
		                  else 0x92000000w:bool[64]) o
		((INL FAR_EL1) =+ hv.C.SPR(INR FAR_EL2))) hv.C.SPR|>)|>
`;			    

val hv_guard_gicd_save_ctx_def = Define `
hv_guard_gicd_save_ctx (hv:hv_state) = 
   hv_gicd_entry_state hv
/\ ~failgicd((11><0)(hv.C.SPR(INR FAR_EL2)),
	     ~word_bit 23(hv.C.SPR(INR ESR_EL2)),
	     word_bit 6 (hv.C.SPR(INR ESR_EL2)))
`;

val hv_rule_gicd_save_ctx_def = Define `
hv_rule_gicd_save_ctx (hv:hv_state,c:num) =
    hv with <|C := (hv.C with <|PC := AHV PC_GICD_SAVE_CTX|>);
	      MMU := (hv.MMU with <|active := F|>);
              m := (ctxs_upd(F,c,
		     <|PC := hv.C.SPR(INR ELR_EL2);
		       PSTATE := (31><0) (hv.C.SPR(INR SPSR_EL2));
		       GPR := hv.C.GPR|>))  hv.m|>
`;

val hv_guard_gicd_emu_read_def = Define `
hv_guard_gicd_emu_read (hv:hv_state) = 
   (hv.C.PC = AHV PC_GICD_SAVE_CTX)
/\ (mode(hv.C) = 2) 
/\ ~reqgicd((11><0)(hv.C.SPR(INR FAR_EL2)),F)
/\ ~word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (Glock(hv.m (ADRDS GLOCK)) = NONE)
`;

val hv_rule_gicd_emu_read_def = Define `
hv_rule_gicd_emu_read (hv:hv_state,c:num) =
let 
    g = PCG c
in let
    off = (11><0)(hv.C.SPR(INR FAR_EL2))
in let
    reg = THE(decgicd off)
in let
    sz = if word_bit 23 (hv.C.SPR(INR ESR_EL2)) then 4 else 1
in 
    hv with <|C := (hv.C with <|PC := AHV PC_GICD_FILTER|>);
              m := ((GICDrpl_upd 
		    (c, ReadValue (Read (Agicd @@ off) sz dummy_info)
				  (w2v (gcpys (hv.m (ADRDS (GCPY g))) (g,reg))) )) ) hv.m|>
`;			    

val hv_guard_gicd_emu_write_def = Define `
hv_guard_gicd_emu_write (hv:hv_state) = 
   (hv.C.PC = AHV PC_GICD_SAVE_CTX)
/\ (mode(hv.C) = 2) 
/\ ~reqgicd((11><0)(hv.C.SPR(INR FAR_EL2)),T)
/\ word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (Glock(hv.m (ADRDS GLOCK)) = NONE)
`;

val hv_rule_gicd_emu_write_def = Define `
hv_rule_gicd_emu_write (hv:hv_state,c:num) =
let 
    g = PCG c
in let
    sz = if word_bit 23 (hv.C.SPR(INR ESR_EL2)) then 4 else 1
in let 
    off = (11><0)(hv.C.SPR(INR FAR_EL2)):bool[12]
in let
    reg = THE(decgicd off)
in let
    u = (31><0)(hv.C.GPR(gprX (w2n ((20><16)(hv.C.SPR(INR ESR_EL2)):bool[5]))))
in let
    v' = GICDupd(reg, gcpys (hv.m (ADRDS (GCPY g))) (g, reg), u)
in 
    hv with <|C := (hv.C with <|PC := AHV PC_GICD_FILTER|>);
              m := ((GICDrpl_upd 
		    (c, WrittenValue (Write 
			    (Agicd @@ off) 
			    sz 
			    (w2v u) 
			    dummy_info))) o
		    (if updgicd off then gcpys_upd (g,reg,GICDfltr(g,reg,v'))
		     else \m.m) ) hv.m|>
`;			    

val hv_guard_gicd_req_read_def = Define `
hv_guard_gicd_req_read (hv:hv_state) = 
   (hv.C.PC = AHV PC_GICD_SAVE_CTX)
/\ (mode(hv.C) = 2) 
/\ reqgicd((11><0)(hv.C.SPR(INR FAR_EL2)),F)
/\ ~word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (Glock(hv.m (ADRDS GLOCK)) = NONE)
`;

val hv_rule_gicd_req_read_def = Define `
hv_rule_gicd_req_read (hv:hv_state,c:num) =
let 
    off = (11><0)(hv.C.SPR(INR FAR_EL2)):bool[12]
in let
    sz = if word_bit 23 (hv.C.SPR(INR ESR_EL2)) then 4 else 1
in let
    r = Read (Agicd @@ off) sz dummy_info
in 
   (hv with <|C := (hv.C with <|PC := AHV PC_GICD_ACCESS|>);
	      req_sent := {r};
              m := ((Glock_upd (SOME c)) ) hv.m|>,
    r)
`;			    

val hv_guard_gicd_req_write_def = Define `
hv_guard_gicd_req_write (hv:hv_state) = 
   (hv.C.PC = AHV PC_GICD_SAVE_CTX)
/\ (mode(hv.C) = 2) 
/\ reqgicd((11><0)(hv.C.SPR(INR FAR_EL2)),T)
/\ word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (Glock(hv.m (ADRDS GLOCK)) = NONE)
`;

val hv_rule_gicd_req_write_def = Define `
hv_rule_gicd_req_write (hv:hv_state,c:num) =
let 
    g = PCG c
in let
    sz = if word_bit 23 (hv.C.SPR(INR ESR_EL2)) then 4 else 1
in let 
    off = (11><0)(hv.C.SPR(INR FAR_EL2)):bool[12]
in let
    reg = THE(decgicd off)
in let
    u = (31><0)(hv.C.GPR(gprX (w2n ((20><16)(hv.C.SPR(INR ESR_EL2)):bool[5]))))
in let
    v' = GICDupd(reg, gcpys (hv.m (ADRDS (GCPY g))) (g, reg), u)
in let
    r = GICDreqconv(g, Write (Agicd @@ off) sz (w2v u) dummy_info)
in 
   (hv with <|C := (hv.C with <|PC := AHV PC_GICD_ACCESS|>);
	      req_sent := {r};
              m := ((Glock_upd (SOME c)) o
		    (if updgicd off then gcpys_upd (g,reg,GICDfltr(g,reg,v'))
		     else \m.m) ) hv.m|>,
    r)					     
`;			    

val hv_guard_gicd_unlock_read_def = Define `
hv_guard_gicd_unlock_read (hv:hv_state,c:num,q:reply) = 
   (hv.C.PC = AHV PC_GICD_ACCESS)
/\ (mode(hv.C) = 2)
/\ ~word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (?a d v i. (q = ReadValue (Read a d i) v) /\ ((47><12) a = Agicd))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_gicd_unlock_read_def = Define `
hv_rule_gicd_unlock_read (hv:hv_state,c:num,q:reply) =
let 
    g = PCG c
in let
    reg = THE(decgicd ((11><0)(Rpl_Adr q)))
in let 
    q' = GICDrplconv(g,q)
in 
    hv with <|C := (hv.C with <|PC := AHV PC_GICD_FILTER|>);
	      req_sent := EMPTY;
              m := ((GICDrpl_upd(c,q')) o
		    (Glock_upd NONE) o
		    (gcpys_upd (g,reg,Rpl_val q')) ) hv.m|>
`;			    

val hv_guard_gicd_unlock_write_def = Define `
hv_guard_gicd_unlock_write (hv:hv_state,c:num,q:reply) = 
   (hv.C.PC = AHV PC_GICD_ACCESS)
/\ (mode(hv.C) = 2)
/\ word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (?a d v i. (q = WrittenValue (Write a d v i)) /\ ((47><12) a = Agicd))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_gicd_unlock_write_def = Define `
hv_rule_gicd_unlock_write (hv:hv_state,c:num,q:reply) =
    hv with <|C := (hv.C with <|PC := AHV PC_GICD_FILTER|>);
	      req_sent := EMPTY;
              m := ((GICDrpl_upd(c,q)) o
		    (Glock_upd NONE) ) hv.m|>
`;			    

val hv_guard_gicd_reply_read_def = Define `
hv_guard_gicd_reply_read (hv:hv_state,c:num) = 
   (hv.C.PC = AHV PC_GICD_FILTER)
/\ (mode(hv.C) = 2)
/\ ~word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (?a d v i. (GICDrpl (hv.m (ADRDS GICDRPL)) c = ReadValue (Read a d i) v))
`;

val hv_rule_gicd_reply_read_def = Define `
hv_rule_gicd_reply_read (hv:hv_state,c:num) =
let 
    v = Rpl_val(GICDrpl (hv.m (ADRDS GICDRPL)) c)
in let
    reg = gprX (w2n ((20><16) (hv.C.SPR(INR ESR_EL2)):bool[5]))
in let
    ctx = ctxs (hv.m (ADRDS (CTX c))) (F,c)
in 
    hv with <|C := (hv.C with <|PC := ctx.PC + 4w; 
			        PSTATE := ctx.PSTATE;
			        GPR := \r. if r = reg then v else ctx.GPR r|>);
	      MMU := (hv.MMU with <|active := T|>)|>
`;			    

val hv_guard_gicd_reply_write_def = Define `
hv_guard_gicd_reply_write (hv:hv_state,c:num) = 
   (hv.C.PC = AHV PC_GICD_FILTER)
/\ (mode(hv.C) = 2)
/\ word_bit 6 (hv.C.SPR(INR ESR_EL2))
/\ (?a d v i. (GICDrpl (hv.m (ADRDS GICDRPL)) c = WrittenValue (Write a d v i)))
`;

val hv_rule_gicd_reply_write_def = Define `
hv_rule_gicd_reply_write (hv:hv_state,c:num) =
let 
    ctx = ctxs (hv.m (ADRDS (CTX c))) (F,c)
in 
    hv with <|C := (hv.C with <|PC := ctx.PC + 4w; 
			        PSTATE := ctx.PSTATE;
			        GPR := ctx.GPR|>);
	      MMU := (hv.MMU with <|active := T|>)|>
`;			    

(* Interrupt virtualization handlers *)

val hv_guard_async_irq_def = Define `hv_guard_async_irq (hv:hv_state) = 
   (hv.req_sent = EMPTY) 
/\ (hv.C.PC = AHV VBAR + 0x480w)
/\ (mode(hv.C) = 2) 
/\ (word_bit 7 (hv.C.SPR(INL ISR_EL1)))
`;

val hv_rule_async_irq_def = Define `
hv_rule_async_irq (hv:hv_state,c:num) =
    hv with <|C := (hv.C with <|PC := AHV PC_ASYNC_SND_ACK|>);
	      MMU := (hv.MMU with <|active := F|>);
              m := ctxs_upd (F,c,
		   <|PC := hv.C.SPR(INR ELR_EL2);
		     PSTATE := (31><0) (hv.C.SPR(INR SPSR_EL2));
		     GPR := hv.C.GPR|>) hv.m|>
`;			    

val hv_guard_async_snd_ack_def = Define `
hv_guard_async_snd_ack (hv:hv_state) = 
   (hv.C.PC = AHV PC_ASYNC_SND_ACK)
/\ (mode(hv.C) = 2) 
/\ (hv.req_sent = EMPTY) 
`;

val hv_rule_async_snd_ack_def = Define ` hv_rule_async_snd_ack
(hv:hv_state) = let r = Read Agicc_aiar 4 dummy_info in (hv with <|C
:= (hv.C with <|PC := AHV PC_ASYNC_RCV_ACK|>); req_sent := {r}|>, r)
`;

val hv_state_async_ack_def = Define `
hv_state_async_ack (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_ASYNC_SND_ACK)
/\ (mode(hv.C) = 2) 
/\ (?v. q = ReadValue (Read Agicc_aiar 4 dummy_info) v)
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_guard_irq_rcv_ack_def = Define `
hv_guard_irq_rcv_ack (hv:hv_state, c:num, q:reply) = 
   hv_state_async_ack(hv,q)
/\ let v = Rpl_val q :bool[32] in
   let irq = w2n ((9><0) v :bool[10]) in
   let t = w2n ((12><10) v :bool[3]) in
   irq >= 8 /\ irq <= 1023 /\ (irq <= 15 ==> (PCG c = PCG t))
`;

val hv_rule_irq_rcv_ack_def = Define `
hv_rule_irq_rcv_ack (hv:hv_state,c:num,q:reply) =
let 
    v = Rpl_val q :bool[32]
in let
    id = (9><0) v :bool[10]
in let
    s = w2n ((12><10) v :bool[3])
in let
    irq = if id <=+ 15w then SGI ((3><0) id, s, c) else PIR (w2n id)
in 
    hv with <|C := (hv.C with <|PC := AHV PC_IRQ_SND_EOI|>);
	      req_sent := EMPTY;
              m := lirq_upd (c,irq) hv.m|>
`;			    

val hv_guard_irq_snd_eoi_def = Define `
hv_guard_irq_snd_eoi (hv:hv_state) = 
   (hv.C.PC = AHV PC_IRQ_SND_EOI)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_irq_snd_eoi_def = Define `
hv_rule_irq_snd_eoi (hv:hv_state,c:num) =
let 
    irq = (lirq (hv.m (ADRDS LIRQ)) c)
in let
    v = case irq of 
	  | SGI (id,s,c') => (n2w s :bool[22]) @@ (w2w id :bool[10])
	  | PIR q => n2w q :bool[32]
in let
    r = Write Agicc_aeoir 4 (w2v v) dummy_info
in 
   (hv with <|C := (hv.C with <|PC := AHV PC_IRQ_RCV_EOI|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_irq_rcv_eoi_def = Define `
hv_guard_irq_rcv_eoi (hv:hv_state, q:reply) = 
   (hv.C.PC = AHV PC_IRQ_RCV_EOI)
/\ (mode(hv.C) = 2)
/\ (?v. q = WrittenValue (Write Agicc_aeoir 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_irq_rcv_eoi_def = Define `
hv_rule_irq_rcv_eoi (hv:hv_state) =
   hv with <|C := (hv.C with <|PC := AHV PC_IRQ_SND_CHECK|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_irq_snd_check_def = Define `
hv_guard_irq_snd_check (hv:hv_state) = 
   (hv.C.PC = AHV PC_IRQ_SND_CHECK)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_irq_snd_check_def = Define `
hv_rule_irq_snd_check (hv:hv_state,c:num) =
let
    irq = lirq (hv.m (ADRDS LIRQ)) c
in let
    r = Read (Agich_lr irq) 4 dummy_info
in
   (hv with <|C := (hv.C with <|PC := AHV PC_IRQ_RCV_CHECK|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_irq_rcv_check_def = Define `
hv_guard_irq_rcv_check (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_IRQ_RCV_CHECK)
/\ (mode(hv.C) = 2) 
/\ (?v irq. q = ReadValue (Read (Agich_lr irq) 4 dummy_info) v)
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val inj_def = Define `inj (g:num, irq:irqID, l:bool[32]) = 
   irq IN (PIRQ g UNION refIPIRQ_g g)
/\ !q. ((irq = PIR q) ==> q >=16 /\ q < 1020 /\ ~word_bit 29 l)
/\ ~word_bit 28 l
`;

val hv_rule_irq_rcv_check_def = Define `
hv_rule_irq_rcv_check (hv:hv_state,c:num,q:reply) =
let 
    g = PCG c
in let
    l = Rpl_val q :bool[32]
in let
    irq = lirq (hv.m (ADRDS LIRQ)) c
in
    hv with <|C := (hv.C with <|PC := if inj(g,irq,l) 
				      then AHV PC_IRQ_SND_INJECT
				      else AHV PC_IRQ_SND_DEACT|>);
	      req_sent := EMPTY;
              m := llr_upd(c,l) hv.m|>
`;			    


val hv_guard_irq_snd_inject_def = Define `
hv_guard_irq_snd_inject (hv:hv_state) = 
   (hv.C.PC = AHV PC_IRQ_SND_INJECT)
/\ (mode(hv.C) = 2) 
/\ (hv.req_sent = EMPTY)
`;

val injlr_def = Define `injlr (a:bool[48], l:bool[32], irq : irqID) = 
case (word_bit 29 l, irq) of
  | (F, PIR q) =>        Write a 4 (w2v(((((0b1101w:bool[4] @@ 
					(prio irq)):bool[9] @@
					0w:bool[3]):bool[12] @@
					(n2w q :bool[10])):bool[22] @@ 
					(n2w q :bool[10])):bool[32])) 
			           dummy_info
  | (F, SGI (id,s,c)) => Write a 4 (w2v(((((0b0101w:bool[4] @@
					(prio irq)):bool[9] @@
				        0w:bool[10]):bool[19] @@ 
					(n2w (PCC s) :bool[3])):bool[22] @@
					(w2w id :bool[10])):bool[32])) 
			           dummy_info
  | (T,_) =>             Write a 4 (w2v(((((31><30) l :bool[2]) @@
				        0b11w:bool[2]):bool[4] @@
				        ((27><0) l:bool[28])):bool[32])) 
			           dummy_info
`;

val hv_rule_irq_snd_inject_def = Define `
hv_rule_irq_snd_inject (hv:hv_state,c:num) =
let
    irq = lirq (hv.m (ADRDS LIRQ)) c
in let
    lr = llr (hv.m (ADRDS LLR)) c
in let
    r = injlr(Agich_lr irq, lr, irq)
in
   (hv with <|C := (hv.C with <|PC := AHV PC_IRQ_RCV_INJECT|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_irq_rcv_inject_def = Define `
hv_guard_irq_rcv_inject (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_IRQ_RCV_INJECT)
/\ (mode(hv.C) = 2) 
/\ (?v irq. q = WrittenValue (Write (Agich_lr irq) 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_irq_rcv_inject_def = Define `
hv_rule_irq_rcv_inject (hv:hv_state,c:num) =
let 
    irq = lirq (hv.m (ADRDS LIRQ)) c
in
    hv with <|C := (hv.C with <|PC := if irq IN refIPIRQ_g (PCG c)
				      then AHV PC_IRQ_SND_DEACT
				      else AHV PC_IRQ_RETURN|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_irq_snd_deact_def = Define `
hv_guard_irq_snd_deact (hv:hv_state) = 
   (hv.C.PC = AHV PC_IRQ_SND_DEACT)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val deact_def = Define `deact (irq : irqID) = 
case (irq) of
  | PIR q =>        Write Agicc_dir 4 (w2v((0w:bool[22] @@ 
					(n2w q :bool[10])):bool[32])) 
			           dummy_info
  | SGI (id,s,c) => Write Agicc_dir 4 (w2v(((0w:bool[19] @@
				       (n2w (PCC s) :bool[3])):bool[22] @@
				       (w2w id :bool[10])):bool[32])) 
			           dummy_info
  | _ =>            Write Agicc_dir 4 (w2v (1023w:bool[32])) dummy_info
`;

val hv_rule_irq_snd_deact_def = Define `
hv_rule_irq_snd_deact (hv:hv_state,c:num) =
let
    irq = lirq (hv.m (ADRDS LIRQ)) c
in let
    r = deact irq
in
   (hv with <|C := (hv.C with <|PC := AHV PC_IRQ_RCV_DEACT|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_irq_rcv_deact_def = Define `
hv_guard_irq_rcv_deact (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_IRQ_RCV_DEACT)
/\ (mode(hv.C) = 2) 
/\ (?v. q = WrittenValue (Write Agicc_dir 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_irq_rcv_deact_def = Define `
hv_rule_irq_rcv_deact (hv:hv_state) =
    hv with <|C := (hv.C with <|PC := AHV PC_IRQ_RETURN|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_irq_return_def = Define `
hv_guard_irq_return (hv:hv_state) = 
   (hv.C.PC = AHV PC_IRQ_RETURN)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

(* TODO: set ISR_EL1 to 0x80 *)
val hv_rule_irq_return_def = Define `
hv_rule_irq_return (hv:hv_state,c:num) =
let 
    ctx = ctxs (hv.m (ADRDS (CTX c))) (F,c)
in let
    hcr = bit_field_insert 7 7 (1w:bool[1]) (hv.C.SPR(INR HCR_EL2))
in 
    hv with <|C := (hv.C with <|PC := ctx.PC; 
			        PSTATE := ctx.PSTATE;
			        GPR := ctx.GPR;
		                SPR := ((INR HCR_EL2) =+ hcr) hv.C.SPR|>);
	      MMU := (hv.MMU with <|active := T|>)|>
`;			    

(* Send IGC notification handler *)

val hv_guard_sigc_entry_def = Define `
hv_guard_sigc_entry (hv:hv_state) = 
   (hv.C.PC = AHV VBAR + 0x400w) 
/\ (mode(hv.C) = 2) 
/\ ((31><26)(hv.C.SPR(INR ESR_EL2)) = 0b010110w:bool[6])
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_sigc_entry_def = Define `
hv_rule_sigc_entry (hv:hv_state,c:num) =
    hv with <|C := (hv.C with <|PC := AHV PC_SIGC_SND_SGI|>);
	      MMU := (hv.MMU with <|active := F|>);
              m := ctxs_upd (T,c,
		   <|PC := hv.C.SPR(INR ELR_EL2);
		     PSTATE := (31><0) (hv.C.SPR(INR SPSR_EL2));
		     GPR := hv.C.GPR|>) hv.m|>
`;

(* when to grant an SGI interrupt *)
val grant_def = Define `
grant (hv:hv_state, v:bool[16], g:num, g':num) = 
   decsigc v <> NONE
/\ (PAR.cpol(THE (decsigc v)) = (g,g'))
/\ (?c. (PCG c = g') /\ pow (hv.m (ADRDS POW)) c)
/\ ~(mbox (hv.m (ADRDS MBOX)) (g,g'))
`;

(* TODO?: prove that grant implies g<>g' due to cpol axioms *)

val hv_guard_sigc_drop_def = Define `
hv_guard_sigc_drop (hv:hv_state, c:num) = 
   (hv.C.PC = AHV PC_SIGC_SND_SGI) 
/\ (mode(hv.C) = 2) 
/\ (hv.req_sent = EMPTY)
/\ (!g'. g' < PAR.ng ==> ~grant(hv, (15><0)(hv.C.SPR(INR ESR_EL2)), PCG c, g'))
`;

val hv_rule_sigc_drop_def = Define `
hv_rule_sigc_drop (hv:hv_state,c:num) =
let 
    ctx = ctxs (hv.m (ADRDS (CTX c))) (F,c)
in 
    hv with <|C := (hv.C with <|PC := ctx.PC + 4w; 
			        PSTATE := ctx.PSTATE;
			        GPR := ctx.GPR;
		                SPR := hv.C.SPR|>);
	      MMU := (hv.MMU with <|active := T|>)|>
`;			    

val chan_tgt_def = Define `chan_tgt (s:num) = SND (PAR.cpol s)
`;

val _ = new_constant("target", ``:hv_state # num -> num``);
val target_axiom = new_axiom("target_axiom", ``
!hv g t. (t = target(hv,g)) ==>
(!c. c < PAR.nc_g g 
  /\ (PCG c = g) 
  /\ pow (hv.m (ADRDS POW)) c ==> PCC t <= PCC c)
``);

val hv_guard_sigc_snd_sgi_def = Define `
hv_guard_sigc_snd_sgi (hv:hv_state, c:num) = 
   (hv.C.PC = AHV PC_SIGC_SND_SGI) 
/\ (mode(hv.C) = 2) 
/\ (hv.req_sent = EMPTY)
/\ let g' = chan_tgt (THE (decsigc ((15><0)(hv.C.SPR(INR ESR_EL2))))) in
(g' < PAR.ng /\ grant(hv, (15><0)(hv.C.SPR(INR ESR_EL2)), PCG c, g'))
`;

val hv_rule_sigc_snd_sgi_def = Define `
hv_rule_sigc_snd_sgi (hv:hv_state, c:num) =
let 
    g = PCG c
in let
    g' = chan_tgt (THE (decsigc ((15><0)(hv.C.SPR(INR ESR_EL2)))))
in let
    t = target(hv,g)
in let
    r = Write Agicd_sgir 4 (w2v(((0w:bool[8] @@ 
				  (1w:bool[8] << t)):bool[16] @@ 
				  0x000Fw:bool[16]):bool[32])) dummy_info
in
    (hv with <|C := (hv.C with <|PC := AHV PC_SIGC_RCV_SGI|>);
	       req_sent := {r};
               m := mbox_upd (\x. if x = (g,g') then T 
				  else mbox (hv.m (ADRDS MBOX)) x) hv.m|>,
     r)
`;			    

val hv_guard_sigc_rcv_sgi_def = Define `
hv_guard_sigc_rcv_sgi (hv:hv_state, q:reply) = 
   (hv.C.PC = AHV PC_SIGC_RCV_SGI)
/\ (mode(hv.C) = 2)
/\ (?v. q = WrittenValue (Write Agicd_sgir 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_sigc_rcv_sgi_def = Define `
hv_rule_sigc_rcv_sgi (hv:hv_state) =
   hv with <|C := (hv.C with <|PC := AHV PC_SIGC_RETURN|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_sigc_return_def = Define `
hv_guard_sigc_return (hv:hv_state, c:num) = 
   (hv.C.PC = AHV PC_SIGC_RETURN) 
/\ (mode(hv.C) = 2) 
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_sigc_return_def = Define `
hv_rule_sigc_return (hv:hv_state,c:num) =
let 
    ctx = ctxs (hv.m (ADRDS (CTX c))) (T,c)
in 
    hv with <|C := (hv.C with <|PC := ctx.PC + 4w; 
			        PSTATE := ctx.PSTATE;
			        GPR := ctx.GPR;
		                SPR := hv.C.SPR|>);
	      MMU := (hv.MMU with <|active := T|>)|>
`;			    

(* Receive IGC notification interrupt handler *)

val Aigc_lr_def = Define `Aigc_lr s = Agich_lr (PIR (PAR.id_igc s))`;

val hv_guard_rigc_rcv_ack_def = Define `
hv_guard_rigc_rcv_ack (hv:hv_state, c:num, q:reply) = 
   hv_state_async_ack(hv,q)
/\ let v = Rpl_val q :bool[32] in
   let irq = w2n ((9><0) v :bool[10]) in
   let t = w2n ((12><10) v :bool[3]) in
   (irq = 15) /\ PCG c <> PCG t /\ (?s. PAR.cpol(s) = (PCG t, PCG c))
`;

val hv_rule_rigc_rcv_ack_def = Define `
hv_rule_rigc_rcv_ack (hv:hv_state,c:num,q:reply) =
let 
    v = Rpl_val q :bool[32]
in let
    c' = w2n ((12><10) v :bool[3])
in let 
    (* how do you know inv_pol is returning SOME .. *)
    s = THE (inv_pol (PCG c', PCG c))
in 
    hv with <|C := (hv.C with <|PC := AHV PC_RIGC_SND_EOI|>);
	      req_sent := EMPTY;
              m := ligc_upd (c,SOME (s, c')) hv.m|>
`;			    

val hv_guard_rigc_snd_eoi_def = Define `
hv_guard_rigc_snd_eoi (hv:hv_state) = 
   (hv.C.PC = AHV PC_RIGC_SND_EOI)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_rigc_snd_eoi_def = Define `
hv_rule_rigc_snd_eoi (hv:hv_state,c:num) =
let 
    c' = SND (THE (ligc (hv.m (ADRDS LIGC)) c))
in let
    r = Write Agicc_aeoir 4 (w2v (((0w:bool[19] @@ 
				  (n2w c' :bool[3])):bool[22] @@
				   7w:bool[10]):bool[32])) dummy_info
in 
   (hv with <|C := (hv.C with <|PC := AHV PC_RIGC_RCV_EOI|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_rigc_rcv_eoi_def = Define `
hv_guard_rigc_rcv_eoi (hv:hv_state, q:reply) = 
   (hv.C.PC = AHV PC_RIGC_RCV_EOI)
/\ (mode(hv.C) = 2)
/\ (?v. q = WrittenValue (Write Agicc_aeoir 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_rigc_rcv_eoi_def = Define `
hv_rule_rigc_rcv_eoi (hv:hv_state) =
   hv with <|C := (hv.C with <|PC := AHV PC_RIGC_SND_CHECK|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_rigc_snd_check_def = Define `
hv_guard_rigc_snd_check (hv:hv_state) = 
   (hv.C.PC = AHV PC_RIGC_SND_CHECK)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_rigc_snd_check_def = Define `
hv_rule_rigc_snd_check (hv:hv_state,c:num) =
let
    s = FST (THE (ligc (hv.m (ADRDS LIGC)) c))
in let
    r = Read (Aigc_lr s) 4 dummy_info
in
   (hv with <|C := (hv.C with <|PC := AHV PC_RIGC_RCV_CHECK|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_rigc_rcv_check_def = Define `
hv_guard_rigc_rcv_check (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_RIGC_RCV_CHECK)
/\ (mode(hv.C) = 2) 
/\ (?v irq. q = ReadValue (Read (Aigc_lr irq) 4 dummy_info) v)
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_rigc_rcv_check_def = Define `
hv_rule_rigc_rcv_check (hv:hv_state,c:num,q:reply) =
let 
    l = Rpl_val q :bool[32]
in
    hv with <|C := (hv.C with <|PC := if ~word_bit 28 l 
				      then AHV PC_RIGC_SND_INJECT
				      else AHV PC_RIGC_SND_DEACT|>);
	      req_sent := EMPTY;
              m := llr_upd(c,l) hv.m|>
`;			    

val hv_guard_rigc_snd_inject_def = Define `
hv_guard_rigc_snd_inject (hv:hv_state) = 
   (hv.C.PC = AHV PC_RIGC_SND_INJECT)
/\ (mode(hv.C) = 2) 
/\ (hv.req_sent = EMPTY)
`;

val injlrIGC_def = Define `injlrIGC (s:num, l:bool[32]) = 
case word_bit 29 l of
  | F => Write (Aigc_lr s) 4 (w2v((((0b0101w:bool[4] @@ 
				     prioIGC):bool[9] @@
				     0w:bool[13]):bool[22] @@
				    (n2w (PAR.id_igc s)) :bool[10]):bool[32])) 
			      dummy_info
  | T => Write (Aigc_lr s) 4 (w2v(((((31><30) l :bool[2]) @@
				      0b11w:bool[2]):bool[4] @@
				     ((27><0) l:bool[28])):bool[32])) 
	                      dummy_info
`;

val hv_rule_rigc_snd_inject_def = Define `
hv_rule_rigc_snd_inject (hv:hv_state,c:num) =
let
    s = FST (THE (ligc (hv.m (ADRDS LIGC)) c))
in let
    lr = llr (hv.m (ADRDS LLR)) c
in let
    r = injlrIGC(s, lr)
in
   (hv with <|C := (hv.C with <|PC := AHV PC_RIGC_RCV_INJECT|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_rigc_rcv_inject_def = Define `
hv_guard_rigc_rcv_inject (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_RIGC_RCV_INJECT)
/\ (mode(hv.C) = 2) 
/\ (?v s. q = WrittenValue (Write (Aigc_lr s) 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_rigc_rcv_inject_def = Define `
hv_rule_rigc_rcv_inject (hv:hv_state,c:num) =
    hv with <|C := (hv.C with <|PC := AHV PC_IRQ_SND_DEACT|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_rigc_snd_deact_def = Define `
hv_guard_rigc_snd_deact (hv:hv_state) = 
   (hv.C.PC = AHV PC_RIGC_SND_DEACT)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_rigc_snd_deact_def = Define `
hv_rule_rigc_snd_deact (hv:hv_state,c:num) =
let
    c' = SND (THE (ligc (hv.m (ADRDS LIGC)) c))
in let
    r = Write Agicc_dir 4 (w2v(((0w:bool[19] @@
				(n2w c' :bool[3])):bool[22] @@
				(7w :bool[10])):bool[32])) 
	                   dummy_info
in
   (hv with <|C := (hv.C with <|PC := AHV PC_RIGC_RCV_DEACT|>);
	      req_sent := {r}|>,
    r)
`;			    

val hv_guard_rigc_rcv_deact_def = Define `
hv_guard_rigc_rcv_deact (hv:hv_state,q:reply) = 
   (hv.C.PC = AHV PC_RIGC_RCV_DEACT)
/\ (mode(hv.C) = 2) 
/\ (?v. q = WrittenValue (Write Agicc_dir 4 v dummy_info))
/\ (?r. r IN hv.req_sent /\ match(r,q))
`;

val hv_rule_rigc_rcv_deact_def = Define `
hv_rule_rigc_rcv_deact (hv:hv_state) =
    hv with <|C := (hv.C with <|PC := AHV PC_RIGC_RETURN|>);
	      req_sent := EMPTY|>
`;			    

val hv_guard_rigc_return_def = Define `
hv_guard_rigc_return (hv:hv_state) = 
   (hv.C.PC = AHV PC_RIGC_RETURN)
/\ (mode(hv.C) = 2)
/\ (hv.req_sent = EMPTY)
`;

val hv_rule_rigc_return_def = Define `
hv_rule_rigc_return (hv:hv_state,c:num) =
let 
    c' = SND (THE (ligc (hv.m (ADRDS LIGC)) c))
in let
    ctx = ctxs (hv.m (ADRDS (CTX c))) (F,c)
in let
    hcr = bit_field_insert 7 7 (1w:bool[1]) (hv.C.SPR(INR HCR_EL2))
in 
    hv with <|C := (hv.C with <|PC := ctx.PC; 
			        PSTATE := ctx.PSTATE;
			        GPR := ctx.GPR;
		                SPR := ((INR HCR_EL2) =+ hcr) hv.C.SPR|>);
	      MMU := (hv.MMU with <|active := T|>);
	      m := (ligc_upd (c,NONE) o
		    mbox_upd (\x. if x = (PCG c', PCG c) then F 
				  else mbox (hv.m (ADRDS MBOX)) x)) hv.m|>
`;			    

(* MMU fault handler *)

val Afault_def = Define `Afault (g:num) =
\a. a NOTIN (PAR.A_G g) \/ (a = Agicd)
`;			    

val hv_mmu_fault_entry_point_def = Define`
hv_mmu_fault_entry_point (C:refcore_config) = 
   (C.PC = AHV VBAR + 0x400w) 
/\ (mode C = 2) 
/\ (case (31><26)(C.SPR(INR ESR_EL2)):bool[6] of 
      | 0b100100w:bool[6] => T
      | 0b100000w:bool[6] => T
      | _ => F)
`;

val hv_guard_mmu_fault = Define `
hv_guard_mmu_fault (hv:hv_state,c:num) = 
   (hv.C.PC = AHV VBAR + 0x400w) 
/\ (mode(hv.C) = 2) 
/\ (case (31><26)(hv.C.SPR(INR ESR_EL2)):bool[6] of 
      | 0b100100w:bool[6] => T
      | 0b100000w:bool[6] => T
      | _ => F)
(* /\ ((word_bit 24)(hv.C.SPR(INR ESR_EL2)) = T) *)
(* /\ ((5><3)(hv.C.SPR(INR ESR_EL2)) = 0b000w:bool[3]) *)
(* /\ ((39><4)(hv.C.SPR(INR HPFAR_EL2)) IN Afault (PCG c)) *)
/\ (hv.req_sent = EMPTY)
/\ ~(hv_gicd_entry_state hv)
`;

val hv_mmu_fault_entry_point_lem = store_thm("hv_mmu_fault_entry_point_lem", ``
!hv c. hv_guard_mmu_fault (hv,c) ==> hv_mmu_fault_entry_point (hv.C)
``,
  RW_TAC std_ss [hv_mmu_fault_entry_point_def, hv_guard_mmu_fault]
);

val hv_rule_mmu_fault_def = Define `
hv_rule_mmu_fault (hv:hv_state) =
let 
    spsr = hv.C.SPR(INR SPSR_EL2) 
in
    hv with <|C := (hv.C with <|PC := hv.C.SPR(INL VBAR_EL1) + ghoff spsr;
			        PSTATE := MODE_upd(hv.C.PSTATE, 1);
			        SPR := (
		((INL SPSR_EL1) =+ spsr) o
		((INL ELR_EL1) =+ hv.C.SPR(INR ELR_EL2)) o
		((INL ESR_EL1) =+ (((31><27)(hv.C.SPR(INR ESR_EL2)):bool[5] @@
				    (v2w [spsr ' 2] :bool[1])):bool[6] @@
				    ((1w << 25) :bool[26])):bool[64]) o
		((INL FAR_EL1) =+ hv.C.SPR(INR FAR_EL2))) hv.C.SPR|>)|>
`;			    


(* Hypervisor transition relation *)

val _ = Datatype `HV_RULE = HV_INIT_ABORT | HV_LOOP | HV_INIT_PRIM_COLD | HV_INIT_PRIM_INIT | HV_INIT_GUEST | HV_INIT_CORE | HV_INIT_LAUNCH | HV_INIT_SEC_COLD | HV_INIT_WARM | HV_INIT_SEC_PRIM | HV_INIT_SEC_SEC | HV_INIT_SOFT | HV_SMC_ISSUE | HV_SMC_DENY | HV_GICD_FAIL | HV_GICD_EMU_READ | HV_GICD_EMU_WRITE | HV_GICD_REQ_READ | HV_GICD_REQ_WRITE | HV_GICD_UNLOCK_READ reply | HV_GICD_UNLOCK_WRITE reply | HV_GICD_REPLY_READ | HV_GICD_REPLY_WRITE | HV_ASYNC_IRQ | HV_ASYNC_SND_ACK | HV_IRQ_RCV_ACK reply | HV_IRQ_SND_EOI | HV_IRQ_RCV_EOI | HV_IRQ_SND_CHECK | HV_IRQ_RCV_CHECK reply | HV_IRQ_SND_INJECT | HV_IRQ_RCV_INJECT | HV_IRQ_SND_DEACT | HV_IRQ_RCV_DEACT | HV_IRQ_RETURN | HV_SIGC_ENTRY | HV_SIGC_DROP | HV_SIGC_SND_SGI | HV_SIGC_RCV_SGI | HV_SIGC_RETURN | HV_RIGC_RCV_ACK reply | HV_RIGC_SND_EOI | HV_RIGC_RCV_EOI | HV_RIGC_SND_CHECK | HV_RIGC_RCV_CHECK reply | HV_RIGC_SND_INJECT | HV_RIGC_RCV_INJECT reply | HV_RIGC_SND_DEACT | HV_RIGC_RCV_DEACT | HV_RIGC_RETURN | HV_MMU_FAULT | HV_BLOCK`;

val hv_rule_def = Define `hv_rule (hv:hv_state, c: num, rpl : reply option) = 
case rpl of
| SOME q =>
if hv_guard_gicd_unlock_read(hv,c,q) then HV_GICD_UNLOCK_READ q else
if hv_guard_gicd_unlock_write(hv,c,q) then HV_GICD_UNLOCK_WRITE q else
if hv_guard_irq_rcv_ack(hv,c,q) then HV_IRQ_RCV_ACK q else
if hv_guard_irq_rcv_eoi(hv,q) then HV_IRQ_RCV_EOI else
if hv_guard_irq_rcv_check(hv,q) then HV_IRQ_RCV_CHECK q else
if hv_guard_irq_rcv_inject(hv,q) then HV_IRQ_RCV_INJECT else
if hv_guard_irq_rcv_deact(hv,q) then HV_IRQ_RCV_DEACT else
if hv_guard_sigc_rcv_sgi(hv,q) then HV_SIGC_RCV_SGI  else
if hv_guard_rigc_rcv_ack(hv,c,q) then HV_RIGC_RCV_ACK q else
if hv_guard_rigc_rcv_eoi(hv,q) then HV_RIGC_RCV_EOI else
if hv_guard_rigc_rcv_check(hv,q) then HV_RIGC_RCV_CHECK q else
if hv_guard_rigc_rcv_inject(hv,q) then HV_RIGC_RCV_INJECT q else
if hv_guard_rigc_rcv_deact(hv,q) then HV_RIGC_RCV_DEACT 
else HV_BLOCK
| NONE =>
if hv_guard_init_abort(hv,c) then HV_INIT_ABORT else
if hv_guard_loop(hv,c) then HV_LOOP else
if hv_guard_init_prim_cold(hv,c) then HV_INIT_PRIM_COLD else
if hv_guard_init_prim_init(hv,c) then HV_INIT_PRIM_INIT else
if hv_guard_init_guest hv then HV_INIT_GUEST else
if hv_guard_init_core hv then HV_INIT_CORE else
if hv_guard_init_launch hv then HV_INIT_LAUNCH else
if hv_guard_init_sec_cold(hv,c) then HV_INIT_SEC_COLD else
if hv_guard_init_warm(hv,c) then HV_INIT_WARM else
if hv_guard_init_sec_prim(hv,c) then HV_INIT_SEC_PRIM else
if hv_guard_init_sec_sec(hv,c) then HV_INIT_SEC_SEC else
if hv_guard_init_soft(hv) then HV_INIT_SOFT else
if hv_guard_smc_issue(hv,c) then HV_SMC_ISSUE else
if hv_guard_smc_deny(hv,c) then HV_SMC_DENY else
if hv_guard_gicd_fail hv then HV_GICD_FAIL else
if hv_guard_gicd_emu_read hv then HV_GICD_EMU_READ else
if hv_guard_gicd_emu_write hv then HV_GICD_EMU_WRITE else
if hv_guard_gicd_req_read hv then HV_GICD_REQ_READ else
if hv_guard_gicd_req_write hv then HV_GICD_REQ_WRITE else
if hv_guard_gicd_reply_read(hv,c) then HV_GICD_REPLY_READ else
if hv_guard_gicd_reply_write(hv,c) then HV_GICD_REPLY_WRITE else
if hv_guard_async_irq hv then HV_ASYNC_IRQ else
if hv_guard_async_snd_ack hv then HV_ASYNC_SND_ACK else
if hv_guard_irq_snd_eoi hv then HV_IRQ_SND_EOI else
if hv_guard_irq_snd_check hv then HV_IRQ_SND_CHECK else
if hv_guard_irq_snd_inject hv then HV_IRQ_SND_INJECT else
if hv_guard_irq_snd_deact hv then HV_IRQ_SND_DEACT else
if hv_guard_irq_return hv then HV_IRQ_RETURN else
if hv_guard_sigc_entry hv then HV_SIGC_ENTRY else
if hv_guard_sigc_drop(hv,c) then HV_SIGC_DROP else 
if hv_guard_sigc_snd_sgi(hv,c) then HV_SIGC_SND_SGI else
if hv_guard_sigc_return(hv,c) then HV_SIGC_RETURN else
if hv_guard_rigc_snd_eoi hv then HV_RIGC_SND_EOI else
if hv_guard_rigc_snd_check hv then HV_RIGC_SND_CHECK else
if hv_guard_rigc_snd_inject hv then HV_RIGC_SND_INJECT else
if hv_guard_rigc_snd_deact hv then HV_RIGC_SND_DEACT else
if hv_guard_rigc_return hv then HV_RIGC_RETURN else
if hv_guard_mmu_fault(hv,c) then HV_MMU_FAULT 
else HV_BLOCK
`;

val hv_ts_def = Define `hv_ts (hv:hv_state, c: num, rpl : reply option) = 
case hv_rule(hv,c,rpl) of
  | HV_INIT_ABORT => SOME (hv_rule_init_abort hv, NONE, NONE)
  | HV_LOOP => SOME (hv_rule_loop hv, NONE, NONE)
  | HV_INIT_PRIM_COLD => SOME (hv_rule_init_prim_cold hv, NONE, NONE)
  | HV_INIT_PRIM_INIT => let (hv', l) = hv_rule_init_prim_init hv in 
			     SOME(hv', NONE, SOME l)
  | HV_INIT_GUEST => SOME (hv_rule_init_guest(hv,c), NONE, NONE)
  | HV_INIT_CORE => SOME (hv_rule_init_core(hv,c), NONE, NONE)
  | HV_INIT_LAUNCH => SOME (hv_rule_init_launch(hv,c), NONE, NONE)
  | HV_INIT_SEC_COLD => let (hv', l) = hv_rule_init_sec_cold(hv,c) in 
			     SOME(hv', NONE, SOME l)
  | HV_INIT_WARM => SOME (hv_rule_init_warm(hv,c), NONE, NONE)
  | HV_INIT_SEC_PRIM => SOME (hv_rule_init_guest(hv,c), NONE, NONE)
  | HV_INIT_SEC_SEC => SOME (hv_rule_init_sec_sec(hv,c), NONE, NONE)
  | HV_INIT_SOFT => SOME (hv_rule_init_soft(hv,c), NONE, NONE)
  | HV_SMC_ISSUE => let (hv', l) = hv_rule_smc_issue hv in 
			     SOME(hv', NONE, SOME l)
  | HV_SMC_DENY => SOME (hv_rule_smc_deny hv, NONE, NONE)
  | HV_GICD_FAIL => SOME (hv_rule_gicd_fail hv, NONE, NONE)
  | HV_GICD_EMU_READ => SOME (hv_rule_gicd_emu_read(hv,c), NONE, NONE)
  | HV_GICD_EMU_WRITE => SOME (hv_rule_gicd_emu_write(hv,c), NONE, NONE)
  | HV_GICD_REQ_READ =>  let (hv', r) = hv_rule_gicd_req_read(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_GICD_REQ_WRITE => let (hv', r) = hv_rule_gicd_req_write(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_GICD_REPLY_READ => SOME (hv_rule_gicd_reply_read(hv,c), NONE, NONE)
  | HV_GICD_REPLY_WRITE => SOME (hv_rule_gicd_reply_write(hv,c), NONE, NONE)
  | HV_ASYNC_IRQ => SOME (hv_rule_async_irq(hv,c), NONE, NONE)
  | HV_ASYNC_SND_ACK => let (hv', r) = hv_rule_async_snd_ack hv in 
			     SOME(hv', SOME r, NONE)
  | HV_IRQ_SND_EOI => let (hv', r) = hv_rule_irq_snd_eoi(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_IRQ_SND_CHECK => let (hv', r) = hv_rule_irq_snd_check(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_IRQ_SND_INJECT => let (hv', r) = hv_rule_irq_snd_inject(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_IRQ_SND_DEACT => let (hv', r) = hv_rule_irq_snd_deact(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_IRQ_RETURN =>  SOME (hv_rule_irq_return(hv,c), NONE, NONE)
  | HV_SIGC_ENTRY =>  SOME (hv_rule_sigc_entry(hv,c), NONE, NONE)
  | HV_SIGC_DROP => SOME (hv_rule_sigc_drop(hv,c), NONE, NONE)
  | HV_SIGC_SND_SGI => let (hv', r) = hv_rule_sigc_snd_sgi(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_SIGC_RETURN => SOME (hv_rule_sigc_return(hv,c), NONE, NONE)
  | HV_RIGC_SND_EOI => let (hv', r) = hv_rule_rigc_snd_eoi(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_RIGC_SND_CHECK => let (hv', r) = hv_rule_rigc_snd_check(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_RIGC_SND_INJECT => let (hv', r) = hv_rule_rigc_snd_inject(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_RIGC_SND_DEACT => let (hv', r) = hv_rule_rigc_snd_deact(hv,c) in 
			     SOME(hv', SOME r, NONE)
  | HV_RIGC_RETURN => SOME (hv_rule_rigc_return(hv,c), NONE, NONE)
  | HV_MMU_FAULT => SOME (hv_rule_mmu_fault hv, NONE, NONE)
  | HV_GICD_UNLOCK_READ q => SOME (hv_rule_gicd_unlock_read(hv,c,q), NONE, NONE)
  | HV_GICD_UNLOCK_WRITE q => SOME (hv_rule_gicd_unlock_write(hv,c,q), NONE,NONE)
  | HV_IRQ_RCV_ACK q => SOME (hv_rule_irq_rcv_ack(hv,c,q), NONE, NONE)
  | HV_IRQ_RCV_EOI => SOME (hv_rule_irq_rcv_eoi hv, NONE, NONE)
  | HV_IRQ_RCV_CHECK q => SOME (hv_rule_irq_rcv_check(hv,c,q), NONE, NONE)
  | HV_IRQ_RCV_INJECT => SOME (hv_rule_irq_rcv_inject(hv,c), NONE, NONE)
  | HV_IRQ_RCV_DEACT => SOME (hv_rule_irq_rcv_deact hv, NONE, NONE)
  | HV_SIGC_RCV_SGI  => SOME (hv_rule_sigc_rcv_sgi hv, NONE, NONE)
  | HV_RIGC_RCV_ACK q => SOME (hv_rule_rigc_rcv_ack(hv,c,q), NONE, NONE)
  | HV_RIGC_RCV_EOI => SOME (hv_rule_rigc_rcv_eoi hv, NONE, NONE)
  | HV_RIGC_RCV_CHECK q => SOME (hv_rule_rigc_rcv_check(hv,c,q), NONE, NONE)
  | HV_RIGC_RCV_INJECT q => SOME (hv_rule_rigc_rcv_inject(hv,c), NONE, NONE)
  | HV_RIGC_RCV_DEACT => SOME (hv_rule_rigc_rcv_deact hv, NONE, NONE)
  | HV_BLOCK => SOME (hv, NONE, NONE)
`;


val hv_rule_res_sym_lem = store_thm("hv_rule_res_sym_lem",
     ``(hv_rule_ (hv:hv_state,n:num) = (hv':hv_state))
     = (hv' = hv_rule_ (hv,n))``,
    METIS_TAC []);


(*************** finish ***********)

val _ = export_theory();
