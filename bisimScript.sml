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

val _ = new_theory "bisim";

(**************** HELPER FUNCTIONS ******************)

(* extending translation to request and replies *)

val ipat_def = Define `ipat (g:num) (a:bool[48]) = 
((ATrans g ((47><12) a)) @@ ((11><0) a :bool[12])):bool[48] 
`;

val Trreq_def = Define `
   (Trreq (g:num) (Read a d i) = Read (ipat g a) d i)
/\ (Trreq (g:num) (Write a d v i) = Write (ipat g a) d v i)
/\ (Trreq (g:num) (Walk a i) = Walk (ipat g a) i)
`;

val Trrpl_def = Define `
   (Trrpl (g:num) (ReadValue (Read a d i) v) = ReadValue (Read (ipat g a) d i) v)
/\ (Trrpl (g:num) (WrittenValue (Write a d v i)) = WrittenValue (Write (ipat g a) d v i))
/\ (Trrpl (g:num) (WalkResult (Walk a i) v) = WalkResult (Walk (ipat g a) i) v)
/\ (Trrpl (g:num) (Fault (Read a d i) fi) = Fault (Read (ipat g a) d i) fi)
/\ (Trrpl (g:num) (Fault(Write a d v i) fi) = Fault (Write (ipat g a) d v i) fi)
/\ (Trrpl (g:num) (Fault (Walk a i) fi) = Fault (Walk (ipat g a) i) fi)
/\ (Trrpl (g:num) _ = WrittenValue (Walk 0w dummy_info))
`;

val Trreq_PAdr_Trans_lem = store_thm("Trreq_PAdr_Trans_lem", ``
!g r. IS_SOME(Trans g (PAdr r)) ==>
(PAdr (Trreq g r) = THE (Trans g (PAdr r)))
``,
  RW_TAC (srw_ss()) [] THEN 
  Cases_on `r` THEN 
  FULL_SIMP_TAC (srw_ss()) [Trreq_def, ipat_def, ATrans_def, PAdr_def, Adr_def, optionTheory.THE_DEF, optionTheory.IS_SOME_EXISTS] THEN 
  RW_TAC (srw_ss()) [PAdr_extract_lem]
);

val Trreq_PAdr_ATrans_lem = store_thm("Trreq_PAdr_ATrans_lem", ``
!g r. (PAdr (Trreq g r) = ATrans g (PAdr r))
``,
  RW_TAC (srw_ss()) [] THEN 
  Cases_on `r` THEN (
      FULL_SIMP_TAC (srw_ss()) [Trreq_def, ipat_def, PAdr_def, Adr_def] THEN 
      RW_TAC (srw_ss()) [PAdr_extract_lem]
  )
);

val Trreq_PAdr_inj_lem = store_thm("Trreq_PAdr_inj_lem", ``
!r r' g.
   g < PAR.ng
/\ IS_SOME (Trans g (PAdr r))
==>
((PAdr r = PAdr r') <=> (PAdr (Trreq g r) = PAdr (Trreq g r')))
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [STRIP_TAC >>
      ASM_REWRITE_TAC [Trreq_PAdr_ATrans_lem]
      ,
      STRIP_TAC >>
      FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem] >>
      IMP_RES_TAC IS_SOME_ATrans_lem >>
      IMP_RES_TAC ATrans_inj
     ]
);

val Trreq_xlated_Trans_lem = store_thm("Trreq_xlated_Trans_lem", ``
!r r' g. g < PAR.ng /\ IS_SOME(Trans g (PAdr r')) 
==>
((r = Trreq g r') <=> ((PAdr r = THE(Trans g (PAdr r'))) /\ xlated(r',r)))
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN 
  EQ_TAC 
  THENL [(* case: ==> *)
	 STRIP_TAC THEN
	 IMP_RES_TAC Trreq_PAdr_Trans_lem THEN 
	 RW_TAC (srw_ss()) [] THEN 
         Cases_on `r'` THEN
	 FULL_SIMP_TAC (srw_ss()) [xlated_def, Trreq_def, ATrans_def, PAdr_def, Adr_def, optionTheory.THE_DEF, optionTheory.IS_SOME_EXISTS, ipat_def] THEN 
	 RW_TAC (srw_ss()) [bx_extract_lem],
	 (* case: <== *)
	 STRIP_TAC THEN
	 Cases_on `r'` THEN
	 FULL_SIMP_TAC (srw_ss()) [xlated_def] THEN 
	 RW_TAC (srw_ss()) [Trreq_def, ATrans_def, ipat_def] THEN
	 FULL_SIMP_TAC (srw_ss()) [PAdr_rw_lem, optionTheory.THE_DEF, optionTheory.IS_SOME_EXISTS] THEN 
	 PROVE_TAC [PAdr_bx_concat_lem, optionTheory.THE_DEF]
	]
);

val Trreq_xlated_ATrans_lem = store_thm("Trreq_xlated_ATrans_lem", ``
!r r' g. g < PAR.ng
==>
((r = Trreq g r') <=> ((PAdr r = ATrans g (PAdr r')) /\ xlated(r',r)))
``,
  RW_TAC (srw_ss()) [] THEN 
  Cases_on `ATrans g (PAdr r') = FAULT_ADDRESS`
  THENL [Cases_on `r` THEN (
             Cases_on `r'` THEN (
	         EQ_TAC THEN (
		     STRIP_TAC THEN 
		     FULL_SIMP_TAC (srw_ss()) [Trreq_def, ipat_def, xlated_def, PAdr_def, Adr_def] THEN
		     REV_FULL_SIMP_TAC (srw_ss()) [] THEN
		     RW_TAC (srw_ss()) [] THEN 
		     METIS_TAC [bx_extract_lem, PAdr_extract_lem, PAdr_bx_concat_lem]
		 )
	     )
	 ),
	 IMP_RES_TAC ATrans_lem THEN 
         FULL_SIMP_TAC (srw_ss()) [ATrans_def] THEN 
	 IMP_RES_TAC Trreq_xlated_Trans_lem THEN 
	 FULL_SIMP_TAC (srw_ss()) []
	]
);

val good_rpl_cases_lem = store_thm("good_rpl_cases_lem", ``
!q. good_rpl q
<=>
   (?a d i v. q = ReadValue (Read a d i) v)
\/ (?a d i v. q = WrittenValue (Write a d v i))
\/ (?a i v. q = WalkResult (Walk a i) v)
\/ (?r fi. q = Fault r fi)
``,
  Cases THEN (
    RW_TAC (srw_ss()) [good_rpl_def] THEN
    Cases_on `r` THEN ( 
      RW_TAC (srw_ss()) [good_rpl_def]
    )
  )
);


val Trrpl_xlated_ATrans_lem = store_thm("Trrpl_xlated_ATrans_lem", ``
!q q' g. g < PAR.ng /\ good_rpl q /\ good_rpl q'
==>
((q = Trrpl g q') <=> ((Rpl_PAdr q = ATrans g (Rpl_PAdr q')) /\ xlated_rpl(q',q)))
``,
  RW_TAC (srw_ss()) [good_rpl_cases_lem] THEN (
      TRY (Cases_on `r`) THEN 
      TRY (Cases_on `r'`) THEN 
      FULL_SIMP_TAC (srw_ss()) [Trrpl_def, ipat_def, xlated_rpl_def, Rpl_PAdr_def, Rpl_Adr_def, xlated_def] THEN
      EQ_TAC THEN (
          STRIP_TAC THEN 
       	  REV_FULL_SIMP_TAC (srw_ss()) [] THEN
	  RW_TAC (srw_ss()) [] THEN (
	      METIS_TAC [bx_extract_lem, PAdr_extract_lem, PAdr_bx_concat_lem]
	  )
      )
  )
);


val good_Trrpl_lem = store_thm("good_Trrpl_lem", ``
!g q. g < PAR.ng ==>
(good_rpl q <=> good_rpl (Trrpl g q))
``,
  GEN_TAC THEN 
  Cases THEN_LT
  LASTGOAL ( Cases_on `r`) THEN ( 
      STRIP_TAC THEN
      EQ_TAC 
      THENL [RW_TAC (srw_ss()) [good_rpl_cases_lem] THEN (
                 RW_TAC (srw_ss()) [Trrpl_def]),
	     RW_TAC (srw_ss()) [good_rpl_cases_lem] THEN ( 
	         TRY (Cases_on `r'`) THEN ( 
 	             TRY (Cases_on `r`) THEN (
	                 FULL_SIMP_TAC (srw_ss()) [Trrpl_def] 
		     )
	         )
	     )
	    ]
  )
);

val Adr_Trreq_ipat_lem = store_thm("Adr_Trreq_ipat_lem", ``
!g r. g < PAR.ng ==>
(Adr (Trreq g r) = ipat g (Adr r))
``,
  Cases_on `r` THEN (
      RW_TAC (srw_ss()) [PAdr_def, Adr_def, Trreq_def]
  )
);

val ipat_inj_lem = store_thm("ipat_inj_lem", ``
!g a b. 
   g < PAR.ng 
/\ IS_SOME(Trans g ((47><12)a)) 
/\ IS_SOME(Trans g ((47><12)b))
==>
(((ipat g a):bool[48] = ipat g b) ==> (a = b))
``,
  RW_TAC (srw_ss()) [ipat_def, ATrans_def] THEN 
  FULL_SIMP_TAC (srw_ss()) [optionTheory.IS_SOME_EXISTS] THEN
  REV_FULL_SIMP_TAC (srw_ss()) [optionTheory.THE_DEF] THEN 
  IMP_RES_TAC concat_eq_lem THEN 
  RW_TAC (srw_ss()) [] THEN 
  `Trans g ((47 >< 12) a) <> NONE` by ( FULL_SIMP_TAC (srw_ss()) [] ) THEN
  `Trans g ((47 >< 12) b) <> NONE` by ( FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  `Trans g ((47 >< 12) b) = Trans g ((47 >< 12) a)` by (
  REV_FULL_SIMP_TAC (srw_ss()) [optionTheory.THE_DEF] ) THEN 
  `((47 >< 12) a):bool[36] = (47 >< 12) b` by (
      CCONTR_TAC THEN 
      IMP_RES_TAC Trans_axiom THEN
      FULL_SIMP_TAC (srw_ss()) []
  ) THEN 
  PROVE_TAC [PAdr_bx_concat_lem]
);

val ipat_inj_ATrans_lem = store_thm("ipat_inj_ATrans_lem", ``
!g a b. 
   g < PAR.ng 
/\ ATrans g ((47><12)a) <> FAULT_ADDRESS 
/\ ATrans g ((47><12)b) <> FAULT_ADDRESS
 ==>
(((ipat g a):bool[48] = ipat g b) ==> (a = b))
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC ATrans_lem THEN 
  IMP_RES_TAC ipat_inj_lem 
);


val Trrpl_PAdr_ATrans_lem = store_thm("Trrpl_PAdr_ATrans_lem", ``
!g q. g < PAR.ng  /\ good_rpl q ==>
(Rpl_PAdr (Trrpl g q) = ATrans g (Rpl_PAdr q))
``,
  RW_TAC (srw_ss()) [] THEN 
  FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem] THEN_LT
  LASTGOAL ( Cases_on `r` ) THEN (
      RW_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [Trrpl_def, Rpl_PAdr_def, Rpl_Adr_def, ipat_def] THEN 
      RW_TAC (srw_ss()) [PAdr_extract_lem]
  )
);



val Rpl_Adr_Trrpl_ipat_lem = store_thm("Rpl_Adr_Trrpl_ipat_lem", ``
!g q. g < PAR.ng /\ good_rpl q ==>
(Rpl_Adr (Trrpl g q) = ipat g (Rpl_Adr q))
``,
  RW_TAC (srw_ss()) [good_rpl_cases_lem] THEN_LT
  LASTGOAL ( Cases_on `r` ) THEN (
      RW_TAC (srw_ss()) [Rpl_PAdr_def, Rpl_Adr_def, Trrpl_def]
  )
);


(* can only show this for untranslated requests,
for invalid translations of q underspecified THE could still cause a match *) 
val match_IS_SOME_Trans_lem = store_thm("match_IS_SOME_Trans_lem", ``
!g r q. 
   g < PAR.ng 
/\ IS_SOME(Trans g (PAdr r))
/\ match(r,q)
==> 
IS_SOME(Trans g (Rpl_PAdr q))
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN 
  IMP_RES_TAC match_PAdr_eq_lem THEN 
  FULL_SIMP_TAC (srw_ss()) [] 
);

val match_not_FAULT_ATrans_lem = store_thm("match_not_FAULT_ATrans_lem", ``
!g r q. 
   g < PAR.ng 
/\ match(r,q)
==> 
(ATrans g (PAdr r) <> FAULT_ADDRESS <=> ATrans g (Rpl_PAdr q) <> FAULT_ADDRESS)
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN 
  IMP_RES_TAC match_PAdr_eq_lem THEN 
  FULL_SIMP_TAC (srw_ss()) [] 
);


val Trans_match_lem = store_thm("Trans_match_lem", ``
!g r q. g < PAR.ng /\ IS_SOME(Trans g (PAdr r)) /\ IS_SOME(Trans g (Rpl_PAdr q))
==>
(match(Trreq g r, Trrpl g q) <=> match(r,q))
``,
  (* cases: read / write / walk *)
  Cases_on `r` THEN ( 
      RW_TAC (srw_ss()) [Trreq_def] THEN
      EQ_TAC 
      THENL [
      (* case: ==> *)
          STRIP_TAC THEN
          IMP_RES_TAC good_match_lem THEN 
	  `good_rpl q` by ( IMP_RES_TAC good_Trrpl_lem ) THEN
          `good_rpl (Trrpl g q)` by ( IMP_RES_TAC good_Trrpl_lem ) THEN 
	  FULL_SIMP_TAC (srw_ss()) [match_def] 
	  THENL [
	  (* case: Result *)
	      FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem] THEN (
	          FULL_SIMP_TAC (srw_ss()) [DatatypeSimps.cases_to_top_RULE Trrpl_def] (* reduce to two non-bogus cases *)
	      )
	      THENL [
	      (* case: matching q *)
		  RW_TAC (srw_ss()) [] THEN 
	          FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def, Rpl_PAdr_def, Rpl_Adr_def] THEN 
		  IMP_RES_TAC ipat_inj_lem,
		  (* case: fault *)
		  RW_TAC (srw_ss()) [] THEN 
		  Cases_on `r` THEN (
		      FULL_SIMP_TAC (srw_ss()) [ATrans_def, DatatypeSimps.cases_to_top_RULE Trrpl_def]  )
	      ],
	  (* case: Fault *)
	      FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem] THEN (
	          FULL_SIMP_TAC (srw_ss()) [ATrans_def, DatatypeSimps.cases_to_top_RULE Trrpl_def] (* reduce to non-bogus cases *)
	      ) THEN 
	      RW_TAC (srw_ss()) [] THEN 
	      Cases_on `r'` THEN (
	          FULL_SIMP_TAC (srw_ss()) [ATrans_def, DatatypeSimps.cases_to_top_RULE Trrpl_def]  
	      ) THEN 
	      FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def, Rpl_PAdr_def, Rpl_Adr_def] THEN 
	      IMP_RES_TAC ipat_inj_lem
	  ],
      (* case: <== *)
          STRIP_TAC THEN
          IMP_RES_TAC good_match_lem THEN 
	  `good_rpl q` by ( IMP_RES_TAC good_Trrpl_lem ) THEN
          `good_rpl (Trrpl g q)` by ( IMP_RES_TAC good_Trrpl_lem ) THEN 
	  FULL_SIMP_TAC (srw_ss()) [match_def] THEN (
	      FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem] THEN (
                  FULL_SIMP_TAC (srw_ss()) [ATrans_def, DatatypeSimps.cases_to_top_RULE Trrpl_def] (* reduce to two non-bogus cases *)
	      )
	  )
      ]
  )
);


val ATrans_match_lem = store_thm("ATrans_match_lem", ``
!g r q. 
   g < PAR.ng 
/\ ATrans g (PAdr r) <> FAULT_ADDRESS
==>
(match(Trreq g r, Trrpl g q) <=> match(r,q))
``,
  RW_TAC (srw_ss()) [] THEN 
  EQ_TAC 
  THENL [(* case: ==> *)
      STRIP_TAC THEN 
      IMP_RES_TAC match_PAdr_eq_lem THEN 
      `PAdr (Trreq g r) = ATrans g (PAdr r)` by (
          FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem] ) THEN 
      IMP_RES_TAC good_match_lem THEN 
      `good_rpl q` by (IMP_RES_TAC good_Trrpl_lem) THEN 
      IMP_RES_TAC Trrpl_PAdr_ATrans_lem THEN 
      `ATrans g (Rpl_PAdr q) <> FAULT_ADDRESS` by (
          FULL_SIMP_TAC (srw_ss()) [] ) THEN 
      IMP_RES_TAC ATrans_lem THEN 
      IMP_RES_TAC Trans_match_lem,
      (* case: <== *)
      STRIP_TAC THEN 
      IMP_RES_TAC match_PAdr_eq_lem THEN 
      `ATrans g (Rpl_PAdr q) <> FAULT_ADDRESS` by (
          FULL_SIMP_TAC (srw_ss()) [] ) THEN 
      IMP_RES_TAC ATrans_lem THEN 
      IMP_RES_TAC Trans_match_lem
	]
);

val match_Trrpl_lem = store_thm("match_Trrpl_lem", ``
!g r q q'. 
   g < PAR.ng 
/\ match(r,q)
/\ match(Trreq g r, q') 
/\ xlated_rpl(q,q') 
==>
(q' = Trrpl g q)
``,
  RW_TAC (srw_ss()) [] THEN 
  `Rpl_PAdr q' = PAdr (Trreq g r)` by (
      FULL_SIMP_TAC (srw_ss()) [match_PAdr_eq_lem] ) THEN 
  `PAdr r = Rpl_PAdr q` by (
      FULL_SIMP_TAC (srw_ss()) [match_PAdr_eq_lem] ) THEN 
  `PAdr (Trreq g r) = ATrans g (PAdr r)` by (
      FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem] ) THEN 
  `Rpl_PAdr q' = ATrans g (Rpl_PAdr q)` by ( 
      FULL_SIMP_TAC (srw_ss()) [] ) THEN 
  IMP_RES_TAC good_match_lem THEN 
  IMP_RES_TAC Trrpl_xlated_ATrans_lem						 
);

(* equality of translations and requests *)

val req_eq_lem = store_thm("req_eq_lem", ``
!r r'.
(r = r') <=> ((PAdr r = PAdr r') /\ xlated(r,r'))
``,
  RW_TAC (srw_ss()) [] THEN 
  EQ_TAC 
  THENL [Cases_on `r` THEN (
             RW_TAC (srw_ss()) [xlated_def] ),
	 Cases_on `r` THEN (
	     Cases_on `r'` THEN (
                 RW_TAC (srw_ss()) [xlated_def, PAdr_def, Adr_def] THEN
		 METIS_TAC [PAdr_bx_concat_lem]
	     )
	 )
	]
);

val xlated_Trreq_lem = store_thm("xlated_Trreq_lem", ``
!g r r'.
   g < PAR.ng
==>
(xlated(r,r') <=> xlated(Trreq g r, Trreq g r'))
``,
  RW_TAC (srw_ss()) [] THEN 
  EQ_TAC THEN (
      Cases_on `r` THEN (
  	  Cases_on `r'` THEN (
	      RW_TAC (srw_ss()) [xlated_def, Trreq_def, ipat_def, bx_extract_lem]
	  )
      )
  )
);

val xlated_req_Trreq_lem = store_thm("xlated_req_Trreq_lem", ``
!g r. xlated(r,Trreq g r)
``,
  RW_TAC (srw_ss()) [] >>
  Cases_on `r` >> (
      RW_TAC (srw_ss()) [xlated_def, Trreq_def, ipat_def, bx_extract_lem]
  )
);

val xlated_rpl_Trrpl_lem = store_thm("xlated_rpl_Trrpl_lem", ``
!g q. good_rpl q ==> xlated_rpl(q,Trrpl g q)
``,
  RW_TAC (srw_ss()) [good_rpl_cases_lem] >> (
      TRY ( Cases_on `r` ) >> (
          RW_TAC (srw_ss()) [xlated_rpl_def, xlated_def, Trrpl_def, 
			     ATrans_def, ipat_def, bx_extract_lem]
      )
  )
);


val Trreq_eq_req_lem = store_thm("Trreq_eq_req_lem", ``
!g r r'.
   g < PAR.ng
/\ IS_SOME (Trans g (PAdr r))
/\ (Trreq g r = Trreq g r')
==> 
(r = r')
``,
(* sketch: 
Tr = Tr' 
PAdr Tr = PAdr Tr' /\ xlated(Tr,Tr')
AT PAdr r = AT PAdr /\ xlated(r,r')
IS_SOME ==> AT PAdr r <> AF
PAdr r = PAdr r' /\ xlated(r,r')
r = r'
*) 
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC req_eq_lem THEN 
  `ATrans g (PAdr r) = ATrans g (PAdr r')` by (
      METIS_TAC [Trreq_PAdr_ATrans_lem]
  ) THEN 
  `xlated(r,r')` by ( IMP_RES_TAC xlated_Trreq_lem ) THEN 
  IMP_RES_TAC IS_SOME_ATrans_lem THEN 
  IMP_RES_TAC ATrans_inj THEN   
  IMP_RES_TAC req_eq_lem
);


val PT_Trreq_lem = store_thm("PT_Trreq_lem", ``
!g r r'.
   g < PAR.ng
/\ PAdr r IN RPAR.A_PT g
/\ IS_SOME (Trans g (PAdr r'))
==>
Trreq g r' <> r
``,
  RW_TAC (srw_ss()) [] THEN 
  CCONTR_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) [EQ_SYM_EQ] THEN 
  IMP_RES_TAC Trreq_xlated_Trans_lem THEN 
  IMP_RES_TAC PT_Trans_lem THEN 
  METIS_TAC []
);

val PPT_Trreq_lem = store_thm("PPT_Trreq_lem", ``
!g r r'.
   g < PAR.ng
/\ PAdr r IN RPAR.A_PPT g
/\ IS_SOME (Trans g (PAdr r'))
==>
Trreq g r' <> r
``,
  RW_TAC (srw_ss()) [] THEN 
  CCONTR_TAC THEN 
  FULL_SIMP_TAC (srw_ss()) [EQ_SYM_EQ] THEN 
  IMP_RES_TAC Trreq_xlated_Trans_lem THEN 
  IMP_RES_TAC PPT_Trans_lem THEN 
  METIS_TAC []
);


val xlated_aligned_lem = store_thm("xlated_aligned_lem", ``
!r r'. xlated(r,r') ==> (req_aligned r = req_aligned r')
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC xlated_bx_lem >>
  IMP_RES_TAC xlated_SzOf_lem >>
  RW_TAC (srw_ss()) [req_aligned_lem] >>
  METIS_TAC [aligned_bx_lem]
);

val Trreq_aligned_lem = store_thm("Trreq_aligned_lem", ``
!g r. g < PAR.ng ==>
(req_aligned (Trreq g r) <=> req_aligned r)
``,
  REPEAT STRIP_TAC >>
  `?r'. r' = Trreq g r` by ( RW_TAC std_ss [] ) >>
  IMP_RES_TAC Trreq_xlated_ATrans_lem >>
  IMP_RES_TAC xlated_aligned_lem >>
  RW_TAC (srw_ss()) []
);

(* equality of translations and replies *)


val ReqOf_match_lem = store_thm("ReqOf_match_lem", ``
!q. good_rpl q ==> match(ReqOf q,q)
``,
  Cases >> (
      FULL_SIMP_TAC (srw_ss()) [good_rpl_def] >>
      RW_TAC (srw_ss()) [match_def,ReqOf_def] >>
      Cases_on `r` >> (
          FULL_SIMP_TAC (srw_ss()) [good_rpl_def] >>
          RW_TAC (srw_ss()) [match_def]
      )
  )
);

val match_exist_lem = store_thm("match_exist_lem", ``
!q. good_rpl q ==> ?r. match(r,q)
``,
  REPEAT STRIP_TAC >>
  METIS_TAC [ReqOf_match_lem]
);

val good_rpl_Adr_lem = store_thm("good_rpl_Adr_lem", ``
!q. good_rpl q ==> (Rpl_Adr q = Adr (ReqOf q))
``,
  Cases >> (
      Cases_on `r` >> (
          RW_TAC (srw_ss()) [good_rpl_def, Rpl_Adr_def, Adr_def, ReqOf_def]
      )
  )  
);


val rpl_eq_lem = store_thm("rpl_eq_lem", ``
!q q'. good_rpl q /\ good_rpl q' ==>
((q = q') <=> ((Rpl_PAdr q = Rpl_PAdr q') /\ xlated_rpl(q,q')))
``,
  RW_TAC (srw_ss()) [] >>
  EQ_TAC 
  >| [Cases_on `q` >> ( RW_TAC (srw_ss()) [xlated_rpl_def, xlated_id_lem] )
      ,
      Cases_on `q` >> (
          Cases_on `q'` >> (
              RW_TAC (srw_ss()) [xlated_rpl_def, Rpl_PAdr_ReqOf_lem, ReqOf_def] >>
	      METIS_TAC [req_eq_lem]
	  )
      )
     ]
);

val xlated_Trrpl_lem = store_thm("xlated_Trrpl_lem", ``
!g q q'.
   g < PAR.ng /\ good_rpl q /\ good_rpl q'
==>
(xlated_rpl(q,q') <=> xlated_rpl(Trrpl g q, Trrpl g q'))
``,
  RW_TAC (srw_ss()) [] >>
  EQ_TAC >> (
      Cases_on `q` >> (
  	  Cases_on `q'` >> (
	      RW_TAC (srw_ss()) [] >>
	      Cases_on `r` >> (
	          Cases_on `r'` >> (
		      FULL_SIMP_TAC (srw_ss()) [xlated_def, xlated_rpl_def, 
						Trrpl_def, ipat_def, 
						bx_extract_lem, good_rpl_def]
		  )	  
	      )
	  )
      )
  )      
);

val Trrpl_eq_rpl_lem = store_thm("Trrpl_eq_rpl_lem", ``
!g q q'.
   g < PAR.ng
/\ good_rpl q
/\ IS_SOME (Trans g (Rpl_PAdr q))
/\ (Trrpl g q = Trrpl g q')
==>
(q = q')
``,
  RW_TAC (srw_ss()) [] >>
  `good_rpl (Trrpl g q) ` by ( IMP_RES_TAC good_Trrpl_lem) >>
  `good_rpl (Trrpl g q') ` by ( METIS_TAC [] ) >>
  `good_rpl q' ` by ( IMP_RES_TAC good_Trrpl_lem ) >>
  `(Rpl_PAdr (Trrpl g q) = Rpl_PAdr (Trrpl g q')) /\
   xlated_rpl (Trrpl g q, Trrpl g q')` by (
      METIS_TAC [rpl_eq_lem]
  ) >>
  `ATrans g (Rpl_PAdr q) = ATrans g (Rpl_PAdr q')` by (
      METIS_TAC [Trrpl_PAdr_ATrans_lem]
  ) >>
  `xlated_rpl(q,q')` by ( IMP_RES_TAC xlated_Trrpl_lem ) >>
  IMP_RES_TAC IS_SOME_ATrans_lem >>
  IMP_RES_TAC ATrans_inj >> 
  IMP_RES_TAC rpl_eq_lem
);


val match_Trreq_exist_Trrpl_lem = store_thm("match_Trreq_exist_Trrpl_lem", ``
!g r q.
   g < PAR.ng
/\ IS_SOME (Trans g (PAdr r))
/\ match(Trreq g r, q)
==>
?q'. q = Trrpl g q'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC good_match_lem >>
  Cases_on `r` >> (
      Cases_on `q` >> (
          FULL_SIMP_TAC (srw_ss()) [Trreq_def, match_def, good_rpl_def]
      )
  )
  >| [EXISTS_TAC ``ReadValue (Read c n m) l``
      ,
      EXISTS_TAC ``Fault (Read c n m) f``
      ,
      EXISTS_TAC ``WrittenValue (Write c n l m)``
      ,
      EXISTS_TAC ``Fault (Write c n l m) f``
      ,
      EXISTS_TAC ``WalkResult (Walk c m) c'``
      ,
      EXISTS_TAC ``Fault (Walk c m) f``
     ] >>
  RW_TAC std_ss [Trrpl_def]
);

val match_Trreq_IS_SOME_rpl_lem = store_thm("match_Trreq_IS_SOME_rpl_lem", ``
!g r q.
   g < PAR.ng
/\ IS_SOME (Trans g (PAdr r))
/\ match(Trreq g r, Trrpl g q)
==>
IS_SOME (Trans g (Rpl_PAdr q))
``,
  REPEAT STRIP_TAC >>					    
  IMP_RES_TAC match_PAdr_eq_lem >>
  IMP_RES_TAC good_match_lem >>
  FULL_SIMP_TAC std_ss [Trreq_PAdr_ATrans_lem] >>
  IMP_RES_TAC IS_SOME_ATrans_lem >>
  MATCH_MP_TAC ATrans_lem >>
  `good_rpl q` by ( IMP_RES_TAC good_Trrpl_lem ) >>
  METIS_TAC [Trrpl_PAdr_ATrans_lem]
);	  

val Trrpl_Rpl_val_eq_lem = store_thm("Trrpl_Rpl_val_eq_lem", ``
!q g. good_rpl q ==> Rpl_val_eq (Trrpl g q) q
``,
  REPEAT STRIP_TAC >> 
  IMP_RES_TAC good_rpl_cases_lem >> (
      RW_TAC std_ss [Trrpl_def, Rpl_val_eq_def]
  ) >>
  Cases_on `r` >> (
      RW_TAC std_ss [Trrpl_def, Rpl_val_eq_def]
  )
);

val Trrpl_exists_lem = store_thm("Trrpl_exists_lem", ``
!r q g. 
    g < PAR.ng
 /\ IS_SOME (Trans g (PAdr r))
 /\ match (Trreq g r,q)
==>
?q'. match(r, q') /\ (q = Trrpl g q')
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC good_match_lem >>
  Cases_on `r`
  >| [(* read *)
      Cases_on `Frpl q`
      >| [(* fault *)
	  EXISTS_TAC ``Fault (Read c n m) (fiOf q)``
          ,
	  (* read reply *)
	  EXISTS_TAC ``ReadValue (Read c n m) (Rpl_val_bs q)``
	 ] >> (
          (* both cases *)
          RW_TAC std_ss [match_def] >>
	  MATCH_MP_TAC match_Trrpl_lem >>
	  EXISTS_TAC ``Read c n m`` >>
	  RW_TAC std_ss [xlated_rpl_def, match_def] >>
	  EXISTS_TAC ``Read (ipat g c) n m`` >>
	  RW_TAC std_ss [xlated_def]
	  >| [(* q *)
	      FULL_SIMP_TAC std_ss [Trreq_def] >>
	      IMP_RES_TAC good_rpl_cases_lem >> (
	          FULL_SIMP_TAC std_ss [match_def, reply_distinct, Frpl_def] 
	      ) >>
	      RW_TAC std_ss [fiOf_def, Rpl_val_bs_def]
	      ,
	      (* ipat *)
	      RW_TAC std_ss [ipat_def] >>
	      blastLib.BBLAST_PROVE_TAC
	     ]
      )	      
      ,
      (* write *)
      Cases_on `Frpl q`
      >| [(* fault *)
	  EXISTS_TAC ``Fault (Write c n l m) (fiOf q)``
          ,
	  (* read reply *)
	  EXISTS_TAC ``WrittenValue (Write c n l m)``
	 ] >> (
          (* both cases *)
          RW_TAC std_ss [match_def] >>
	  MATCH_MP_TAC match_Trrpl_lem >>
	  EXISTS_TAC ``Write c n l m`` >>
	  RW_TAC std_ss [xlated_rpl_def, match_def] >>
	  EXISTS_TAC ``Write (ipat g c) n l m`` >>
	  RW_TAC std_ss [xlated_def]
	  >| [(* q *)
	      FULL_SIMP_TAC std_ss [Trreq_def] >>
	      IMP_RES_TAC good_rpl_cases_lem >> (
	          FULL_SIMP_TAC std_ss [match_def, reply_distinct, Frpl_def] 
	      ) >>
	      RW_TAC std_ss [fiOf_def]
	      ,
	      (* ipat *)
	      RW_TAC std_ss [ipat_def] >>
	      blastLib.BBLAST_PROVE_TAC
	     ]
      )	      
      ,
      (* walk *)
      Cases_on `Frpl q`
      >| [(* fault *)
	  EXISTS_TAC ``Fault (Walk c m) (fiOf q)``
          ,
	  (* read reply *)
	  EXISTS_TAC ``WalkResult (Walk c m) (Rpl_val q)``
	 ] >> (
          (* both cases *)
          RW_TAC std_ss [match_def] >>
	  MATCH_MP_TAC match_Trrpl_lem >>
	  EXISTS_TAC ``Walk c m`` >>
	  RW_TAC std_ss [xlated_rpl_def, match_def] >>
	  EXISTS_TAC ``Walk (ipat g c) m`` >>
	  RW_TAC std_ss [xlated_def]
	  >| [(* q *)
	      FULL_SIMP_TAC std_ss [Trreq_def] >>
	      IMP_RES_TAC good_rpl_cases_lem >> (
	          FULL_SIMP_TAC std_ss [match_def, reply_distinct, Frpl_def] 
	      ) >>
	      RW_TAC std_ss [fiOf_def, Rpl_val_def, wordsTheory.w2w_id]
	      ,
	      (* ipat *)
	      RW_TAC std_ss [ipat_def] >>
	      blastLib.BBLAST_PROVE_TAC
	     ]
      )
     ]	      
);

(* exception context *) 
val sc_def = Define `sc (C:refcore) = 
let a = refcore_abs C in
   (a.PC = AHV VBAR + 0x400w) 
/\ (mode(a) = 2) 
/\ ((31><27)(a.SPR(INR ESR_EL2)) = 0b01011w:bool[5])
/\ (refcore_req_sent C = EMPTY)
`;

val sc_done_IGC_def = Define `sc_done_IGC (RC: refcore) = 
sc RC /\ 
~((Mode RC = 2) /\ ((refcore_abs RC).PC = AHV PC_SIGC_RCV_SGI))
`;


val ectx_def = Define `ectx (C:refcore) = 
let a = refcore_abs C in
    <|PC := if sc(C) then a.SPR(INR ELR_EL2) - 4w else a.SPR(INR ELR_EL2);
      PSTATE := (31><0) (a.SPR(INR SPSR_EL2));
      GPR := a.GPR|> : guest_context 
`;

(* new virtual interrupt to be injected *)
val injq_def = Define `injq (g:num, irq:irqID) = 
   irq IN (PIRQ g UNION refIPIRQ_g g)
/\ !q. ((irq = PIR q) ==> q >=16 /\ q < 1020)
`;

val irqid_def = Define `irqid (irq:irqID) = 
case irq of
  | PIR q => n2w q :bool[10]
  | SGI (id, c, c') => w2w id :bool[10]
`;


val nuvi_def = Define `nuvi (RC, MMUrpl, MEMrpl, Lirq) (irq,c) = 
   (Mode RC = 2)
(* in virtual interrupt injection handler *)
/\ (refcore_abs RC).PC IN {AHV PC_ASYNC_RCV_ACK; AHV PC_IRQ_SND_EOI;
			   AHV PC_IRQ_RCV_EOI; AHV PC_IRQ_SND_CHECK;
			   AHV PC_IRQ_RCV_CHECK; AHV PC_IRQ_SND_INJECT;
			   AHV PC_IRQ_RCV_INJECT}
(* reply from gic present for read of acknowledgment register, matches irq *)
/\ ( (?q v. (q = ReadValue (Read Agicc_aiar 4 dummy_info) v)
	  /\ pend_rpl(MMUrpl,MEMrpl,c,q)
	  /\ ((9><0)(Rpl_val q :bool[32]) = irqid irq)
	  /\ ((refcore_abs RC).PC = AHV PC_ASYNC_RCV_ACK)) 
   \/ (irq = Lirq) 
      /\ ((refcore_abs RC).PC <> AHV PC_ASYNC_RCV_ACK) )
(* irq can be injected in principle for the corresponding guest *)
/\ injq(PCG c, irq)
(* not yet injected *)
/\ ~(?q v. (q = WrittenValue (Write (Agich_lr irq) 4 v dummy_info))
        /\ pend_rpl(MMUrpl,MEMrpl,c,q)
        /\ ((refcore_abs RC).PC = AHV PC_IRQ_RCV_INJECT)) 
`;

(* freshly injected igc interrupt *)
val nuigc_def = Define `
nuigc (RC, MMUrpl, MEMrpl, Llr) (irq:irqID, c:num) =
?s c'. s < PAR.ns /\ c' < RPAR.nc /\ PCG c <> PCG c' 
/\ (PAR.cpol s = (PCG c', PCG c))
/\ (w2n(irqid irq) = PAR.id_igc s) /\ (irq = SGI (7w, c', c))
(* in igc injection handler *)
/\ (Mode RC = 2)
/\ (refcore_abs RC).PC IN {AHV PC_RIGC_RCV_INJECT;
			   AHV PC_RIGC_SND_DEACT;
			   AHV PC_RIGC_RCV_DEACT;
			   AHV PC_RIGC_RETURN}
(* if there was an injection, it has been completed *)
/\ (((refcore_abs RC).PC = AHV PC_RIGC_RCV_INJECT) ==>
      ?q v. (q = WrittenValue (Write (Aigc_lr s) 4 v dummy_info)) 
         /\ pend_rpl(MMUrpl,MEMrpl,c,q))
(* igc irq was injected (as it was not pending before) *)
/\  ~(word_bit 28 Llr)
`;


(* igc interrupt request to GIC on the way*)
val nusgi_def = Define `
nusgi (RCs,MMUrpls,MEMrpl) (c:num, c':num) =
   (Mode (RCs c) = 2)
/\ ((refcore_abs (RCs c)).PC = AHV PC_SIGC_RCV_SGI)
(* SGI from c to c' requested *)
/\ (?r. r IN refcore_req_sent (RCs c)
     /\ (r = Write Agicd_sgir 4 (w2v(((0w:bool[8] @@ 
				(1w:bool[8] << c')):bool[16] @@ 
				 0x000Fw:bool[16]):bool[32])) dummy_info)
     (* not processed by GIC yet *)
     /\ ~(?q. pend_rpl(MMUrpls c,MEMrpl,c,q) /\ match(r,q)) )
`;


(**************** BISIMULATION CLAUSES ******************)

val bisim_ctx_core_def = Define `bisim_ctx_core (CI, CR, ctx, ectx, rint, iint) = 
(* TODO: the next line does not hold during soft reboot init core phase *)
   (CI.active <=> CR.H.launched /\ CR.active /\ ~soft CR)
/\ (CI.H.launch <=> ((mode CR = 3) \/ 
		     (mode CR = 2) /\ CR.PC IN {AHV PC_INIT_PRIM_ENTRY;
						AHV PC_INIT_PRIM; 
						AHV PC_INIT_GUEST; 
						AHV PC_INIT_CORE;
						AHV PC_INIT_SEC_ENTRY}) )
(* TODO: add hv internal steps where ISR is out of sync *)
/\ (!r. (CI.SPR(r) = CR.SPR(INL r)) \/ 
        (r = ISR_EL1) /\ (mode CR = 2) /\ 
        (CR.PC = AHV VBAR + 0x480w) /\ (CR.SPR(INL r) = 0x80w))
/\ (CI.active ==> if mode CR < 2 then 
		      (CI.PC = CR.PC)
		   /\ (CI.PSTATE = CR.PSTATE)
		   /\ (CI.GPR = CR.GPR)
		   /\ (iint = rint)
		  else if (mode CR = 2) 
		       /\ CR.PC IN {AHV VBAR + 0x400w; AHV VBAR + 0x480w} then
		      (CI.PC = ectx.PC)
		   /\ (CI.PSTATE = ectx.PSTATE)
		   /\ (CI.GPR = ectx.GPR)
		   /\ (!R. cis_abs iint IN {GICD_RS R; GICD_WS R} ==>       
			(gprX(w2n((20><16)(CR.SPR(INR ESR_EL2)) :bool[5])) = R) )
		  else 
		      (CI.PC = ctx.PC)
		   /\ (CI.PSTATE = ctx.PSTATE)
		   /\ (CI.GPR = ctx.GPR)
		   /\ (!R. cis_abs iint IN {GICD_RS R; GICD_WS R} ==>       
			(gprX(w2n((20><16)(CR.SPR(INR ESR_EL2)) :bool[5])) = R) )
)
`;

val bisim_ctx_def = Define `bisim_ctx (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> 
bisim_ctx_core ((idcore_abs((IM.G (PCG c)).C (PCC c))),
		(refcore_abs(RM.C c)),
		(ctxs (mem_abs(RM.m) (ADRDS (CTX c))) (sc_done_IGC(RM.C c),c)),
	        (ectx(RM.C c)),
                refcore_int(RM.C c),
                idcore_int((IM.G (PCG c)).C (PCC c)))
`;

val bisim_memory_def = Define `bisim_memory (RM:refined_model, IM:ideal_model) = 
!g a. g < PAR.ng /\ a IN PAR.A_G g /\ a NOTIN A_gicper ==> 
      (mem_abs((IM.G g).m) a = mem_abs(RM.m) (THE(Trans g a)))
`;

val PSI_def = Define`
   (PSI (SOME (CoreSender id)) = SOME (CoreSender (PCC id)))
/\ (PSI (SOME (PeripheralSender id)) = SOME (PeripheralSender (PPP id)))
/\ (PSI NONE = NONE)
`;

(* implies that activity and received requests are equal *)
val bisim_periph_def = Define `bisim_periph (RM:refined_model, IM:ideal_model) = 
!p. p < RPAR.np ==> 
    (((IM.G (PPG p)).P (PPP p)).st = (RM.P p).st)
 /\ (!r. ((IM.G (PPG p)).P (PPP p)).IOreq_rcvd r = PSI ((RM.P p).IOreq_rcvd r))
`;

val bisim_corereq_guest_core_def = Define `bisim_corereq_guest_core (RC, IC) = 
Mode RC < 2 ==>  (idcore_req_sent IC  = refcore_req_sent RC)
`;

val bisim_corereq_guest_def = Define `bisim_corereq_guest (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> bisim_corereq_guest_core(RM.C c, (IM.G (PCG c)).C (PCC c))
`;

val bisim_corereq_hyp_core_def = Define `bisim_corereq_hyp_core (RC, IC, hv) = 
   Mode RC >= 2 
/\ ~hv_gicd_entry_state hv
/\ ~hv_mmu_fault_entry_point (hv.C)
/\ (refcore_abs RC).PC NOTIN {AHV PC_GICD_SAVE_CTX; AHV PC_GICD_ACCESS; AHV PC_GICD_FILTER} 
==> 
(idcore_req_sent IC = EMPTY)
`;

val bisim_corereq_hyp_def = Define `bisim_corereq_hyp (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> bisim_corereq_hyp_core(RM.C c, (IM.G (PCG c)).C (PCC c), HVabs(RM,c))
`;

val bisim_corereq_gicd_core_def = Define `bisim_corereq_gicd_core (RC, IC, hv) = 
   (Mode RC = 2)
/\ (hv_gicd_entry_state hv \/
    (refcore_abs RC).PC IN {AHV PC_GICD_SAVE_CTX; AHV PC_GICD_ACCESS; AHV PC_GICD_FILTER}) 
==> 
    (?r. (idcore_req_sent IC = {r}) /\ (PAdr r = Agicd))
`;

val bisim_corereq_gicd_def = Define `bisim_corereq_gicd (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> bisim_corereq_gicd_core(RM.C c, (IM.G (PCG c)).C (PCC c), HVabs(RM,c))
`;

val bisim_mmureq_guest_core_def = Define `bisim_mmureq_guest_core (RC, MMU, cif, hv, c) = 
   (!r. r IN cif.req_rcvd ==> 
	(r IN mmu_req_rcvd MMU
     \/ hv_gicd_entry_state hv /\ (PAdr r = Agicd) 
     \/ hv_guard_mmu_fault(hv,c) 
        /\ (PAdr r NOTIN PAR.A_G (PCG c) \/ 
	    PAdr r IN receiverMem (PCG c)/\ Wreq r)
        /\ (Adr r = ((39><4)((refcore_abs RC).SPR(INR HPFAR_EL2)):bool[36])
		@@ ((11><0)((refcore_abs RC).SPR(INR FAR_EL2)):bool[12]))))
/\ (!r. r IN mmu_req_rcvd MMU ==> r IN cif.req_rcvd)
/\ (hv_gicd_entry_state hv ==> 
       (?r. r IN cif.req_rcvd /\ (PAdr r = Agicd)) )
/\ (hv_guard_mmu_fault(hv,c) ==>
       (?r. r IN cif.req_rcvd
        /\ (PAdr r NOTIN PAR.A_G (PCG c) \/ 
	    PAdr r IN receiverMem (PCG c)/\ Wreq r)
        /\ (Adr r = ((39><4)((refcore_abs RC).SPR(INR HPFAR_EL2)):bool[36])
		 @@ ((11><0)((refcore_abs RC).SPR(INR FAR_EL2)):bool[12]))))
/\ (!r. ( r IN cif.req_sent <=> 
	  (Trreq (PCG c) r IN mmu_req_sent MMU 
	   /\ IS_SOME(Trans (PCG c) (PAdr r)) ) ) )
/\ (!q. ( q IN cif.rpl_rcvd <=> 
	  (Trrpl (PCG c) q IN mmu_rpl_rcvd MMU 
	   /\ IS_SOME(Trans (PCG c) (Rpl_PAdr q)) ) ) )
`;

val bisim_mmureq_guest_def = Define `bisim_mmureq_guest (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc /\ (mmu_abs (RM.MMU c)).active ==> 
bisim_mmureq_guest_core (RM.C c,
			 RM.MMU c, 
			 (IM.G (PCG c)).cif (PCC c), 
			 HVabs(RM,c), 
			 c)
`;

(* coupling of messages uses GICDreqconv on both sides 
in order to cover both read and write replies
multiple conversion of same message is fix *)
val bisim_gicdmsg_ideal_core_def = Define `
bisim_gicdmsg_ideal_core (RC, MMU, Grpl, rMrpl, cif, iGICreq, iMrpl, c) = 
!r. ~(mmu_abs MMU).active /\ r IN cif.req_rcvd 
==> 
   (PAdr r = Agicd) /\ (Mode RC = 2) 
(* GICD request still in bus interface or memory *)
/\ ((r, CoreSender (PCC c)) NOTIN iGICreq /\ 
    ~(?q. id_pend_rpl(cif.rpl_rcvd, iMrpl, PCG c, PCC c, q) /\ match(r,q))
    ==>
        ((refcore_abs RC).PC = AHV PC_GICD_SAVE_CTX )
        /\ (refcore_req_sent RC = EMPTY) )  
(* GICD arrived in GIC *)
/\ ((r, CoreSender (PCC c)) IN iGICreq
    ==>
        ((refcore_abs RC).PC = AHV PC_GICD_SAVE_CTX )
        /\ (refcore_req_sent RC = EMPTY) 
     \/ ((refcore_abs RC).PC = AHV PC_GICD_ACCESS )
        /\ (?r'. r' IN refcore_req_sent RC 
	      /\ (GICDreqconv(PCG c, r') = GICDreqconv(PCG c, r))) )  
(* GIC reply is in memory or bus interface*)
/\ (!q. id_pend_rpl(cif.rpl_rcvd, iMrpl, PCG c, PCC c, q) /\ match(r,q) 
     ==>
        (* GIC / GIC copy access finished *)
        ((refcore_abs RC).PC = AHV PC_GICD_FILTER )
        /\ (Grpl = GICDrplconv(PCG c, q))  
        /\ (refcore_req_sent RC = EMPTY)  
     \/ (* GIC reply outstanding *)
        ((refcore_abs RC).PC = AHV PC_GICD_ACCESS )
        /\ q NOTIN cif.rpl_rcvd
        /\ (?q'. pend_rpl(mmu_rpl_rcvd MMU, rMrpl, c, q)
	      /\ (GICDrplconv(PCG c, q') = GICDrplconv(PCG c, q))) )  
`;


(* coupling of GICD messages from the ideal view *)
val bisim_gicdmsg_ideal_def = Define `
bisim_gicdmsg_ideal (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> 
bisim_gicdmsg_ideal_core (RM.C c, 
			 RM.MMU c, 
			 GICDrpl (mem_abs(RM.m) (ADRDS GICDRPL)) c, 
			 mem_rpl_rcvd RM.m, 
			 (IM.G (PCG c)).cif (PCC c), 
			 idgic_req_rcvd (IM.G (PCG c)).GIC, 
			 mem_rpl_rcvd (IM.G (PCG c)).m, 
			 c)
`;

val bisim_gicdmsg_refined_core_def = Define `
bisim_gicdmsg_refined_core (RC, MMUrpl, Grpl, rMrpl, cif, iGICreq, iMrpl, c) = 
   (((refcore_abs RC).PC = AHV PC_GICD_SAVE_CTX) ==>
       ?r. r IN cif.req_rcvd /\ (PAdr r = Agicd)
        /\ ~(?q. id_pend_rpl(cif.rpl_rcvd, iMrpl, PCG c, PCC c, q) 
	      /\ match(r,q)) )
(* GIC access pending but no reply yet: ideal request is in the GIC *)
/\ (!r. ((refcore_abs RC).PC = AHV PC_GICD_ACCESS) 
    /\ r IN refcore_req_sent RC
    /\ ~(?q. pend_rpl(MMUrpl, rMrpl, c, q) /\ match(r,q) ) ==>
       ?r'. (PAdr r' = Agicd) /\ r' IN cif.req_rcvd
         /\ (r', CoreSender (PCC c)) IN iGICreq
	 /\ (GICDreqconv(PCG c, r) = GICDreqconv(PCG c, r')) ) 
(* GIC produced reply, not consumed yet: ideal reply in memory, matches *)
/\ (!r q. ((refcore_abs RC).PC = AHV PC_GICD_ACCESS)
    /\ r IN refcore_req_sent RC
    /\ pend_rpl(MMUrpl, rMrpl, c, q) /\ match(r,q) ==>
       (PAdr r = Agicd) /\ 
       ?q'. (q', CoreSender(PCC c)) IN iMrpl
         /\ q' NOTIN cif.rpl_rcvd  
         /\ (GICDrplconv(PCG c, q) = GICDrplconv(PCG c, q')) ) 
(* GIC reply consumed: ideal reply in memory or bus IF, matches stored reply *)
/\ (((refcore_abs RC).PC = AHV PC_GICD_FILTER) ==>
       ?q. id_pend_rpl(cif.rpl_rcvd, iMrpl, PCG c, PCC c, q)
        /\ (Rpl_PAdr q = Agicd) 
        /\ (Grpl = GICDrplconv(PCG c, q)) )
(* ideal GIC empty while requesting SGI *)
/\ (((refcore_abs RC).PC = AHV PC_SIGC_RCV_SGI) ==>
	(cif.req_rcvd = EMPTY) 
     /\ ~(?r'. (r', CoreSender (PCC c)) IN iGICreq) ) 
`;

(* corresponding refined view *)
val bisim_gicdmsg_refined_def = Define `
bisim_gicdmsg_refined (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc /\ (Mode (RM.C c) = 2) 
==>
bisim_gicdmsg_refined_core (RM.C c,
			    mmu_rpl_rcvd (RM.MMU c), 
			    GICDrpl (mem_abs(RM.m) (ADRDS GICDRPL)) c, 
			    mem_rpl_rcvd RM.m, 
			    (IM.G (PCG c)).cif (PCC c), 
			    idgic_req_rcvd (IM.G (PCG c)).GIC, 
			    mem_rpl_rcvd (IM.G (PCG c)).m, 
			    c)
`;

val bisim_smmureq_def = Define `bisim_smmureq (RM:refined_model, IM:ideal_model) = 
!p. p < RPAR.np ==> 
   (((IM.G (PPG p)).pif (PPP p)).req_rcvd = mmu_req_rcvd(RM.SMMU p))
/\ (!r. r IN ((IM.G (PPG p)).pif (PPP p)).req_sent <=> 
	(Trreq (PPG p) r IN mmu_req_sent(RM.SMMU p)
	 /\ IS_SOME(Trans (PPG p) (PAdr r)) ) )
/\ (!q. q IN ((IM.G (PPG p)).pif (PPP p)).rpl_rcvd <=> 
	(Trrpl (PPG p) q IN mmu_rpl_rcvd(RM.SMMU p) 
	 /\ IS_SOME(Trans (PPG p) (Rpl_PAdr q)) ) )
`;

val bisim_giccreq_def = Define `bisim_giccreq (RM:refined_model, IM:ideal_model) = 
!r c. c < RPAR.nc /\ PAdr r IN RPAR.Amap GICC ==> 
    (((Trreq (PCG c) r, CoreSender c) IN gic_req_rcvd(RM.GIC) 
      /\ IS_SOME(Trans (PCG c) (PAdr r)))     <=> 
     (r, CoreSender (PCC c)) IN idgic_req_rcvd((IM.G (PCG c)).GIC) )
`;

val bisim_gicdreq_ideal_core_def = Define `
bisim_gicdreq_ideal_core (RC, iGICreq, c) = 
!r. 
(PAdr r = Agicd) /\ (r, CoreSender (PCC c)) IN iGICreq ==> 
   (Mode RC = 2) 
/\ (refcore_abs RC).PC IN {AHV PC_GICD_SAVE_CTX; AHV PC_GICD_ACCESS}
`;

val bisim_gicdreq_ideal_def = Define `
bisim_gicdreq_ideal (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> 
bisim_gicdreq_ideal_core (RM.C c, idgic_req_rcvd (IM.G (PCG c)).GIC, c)
`;

val bisim_gicdreq_refined_core_def = Define `
bisim_gicdreq_refined_core (RC, rGICreq, iGICreq, c) = 
!r. (PAdr r = Agicd) 
 /\ (r, CoreSender c) IN rGICreq
==> 
   (Mode RC = 2) /\ 
(  ((refcore_abs RC).PC = AHV PC_GICD_ACCESS) /\ 
   (?r'. (r', CoreSender (PCC c)) IN iGICreq 
      /\ (GICDreqconv(PCG c,r) = GICDreqconv(PCG c,r')) )
\/ ((refcore_abs RC).PC = AHV PC_SIGC_RCV_SGI)
   )
`;

val bisim_gicdreq_refined_def = Define `
bisim_gicdreq_refined (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==>
bisim_gicdreq_refined_core (RM.C c, gic_req_rcvd RM.GIC, 
			    idgic_req_rcvd (IM.G (PCG c)).GIC, c) 
`;

val bisim_gicdreq_fail_core_def = Define `
bisim_gicdreq_fail_core (hv, CIFreq, c) = 
hv_guard_gicd_fail hv ==>
?r. r IN CIFreq
 /\ (PAdr r = Agicd)
 /\ (~gicd_req_ok r \/ gicd_acc_not_supported(MsgOf r))
`;

val bisim_gicd_fail_def = Define `
bisim_gicd_fail (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc /\ (Mode (RM.C c) = 2) ==>
bisim_gicdreq_fail_core (HVabs(RM,c), ((IM.G (PCG c)).cif (PCC c)).req_rcvd, c) 
`;

val bisim_memreq_def = Define `bisim_memreq (RM:refined_model, IM:ideal_model) = 
(!c. c < RPAR.nc ==>
     (!r. PAdr r <> Agicd ==>
          (((Trreq (PCG c) r, CoreSender c) IN mem_req_rcvd(RM.m) 
	    /\ IS_SOME(Trans (PCG c) (PAdr r))) <=> 
    	   (r ,CoreSender (PCC c)) IN mem_req_rcvd((IM.G (PCG c)).m))
       /\ (((Trreq (PCG c) r, CoreSender c) IN mem_req_sent(RM.m) 
	    /\ IS_SOME(Trans (PCG c) (PAdr r))) <=> 
    	   (r, CoreSender (PCC c)) IN mem_req_sent((IM.G (PCG c)).m)) )
  /\ (!q. Rpl_PAdr q <> Agicd ==> 
          ((Trrpl (PCG c) q, CoreSender c) IN mem_rpl_rcvd(RM.m) <=> 
	   (q, CoreSender (PCC c)) IN mem_rpl_rcvd((IM.G (PCG c)).m)) ) )
/\
(!p. p < RPAR.np ==>
     (!r. (((Trreq (PPG p) r, PeripheralSender p) IN mem_req_rcvd(RM.m) 
	    /\ IS_SOME(Trans (PPG p) (PAdr r))) <=> 
           (r, PeripheralSender (PPP p)) IN mem_req_rcvd((IM.G (PPG p)).m)) ) ) 
`;

val igc_irq_for_core_def = Define `igc_irq_for_core (id,c) = 
?s g'. s < PAR.ns /\ g' < PAR.ng /\ (g' <> PCG c) 
    /\ (PAR.cpol s = (g', PCG c)) /\ (PAR.id_igc s = id)
`;


val bisim_perirq_core_def = Define `
bisim_perirq_core (rGIC, iGIC, Nuvi, c) = 
!q id. (q = PIR id) /\ ~igc_irq_for_core (id,c) 
==> 
((idgic_abs iGIC).Q (PCC c) q = 
case VI rGIC c q of 
  | INACTIVE => if Nuvi (q,c) then PENDING else INACTIVE
  | PENDING  => PENDING
  | ACTIVE   => if Nuvi (q,c) then PENDACT else ACTIVE
  | PENDACT  => PENDACT
)
`;

(* in the ideal model virtualized physical interupts are injected earlier *)
val bisim_perirq_def = Define `
bisim_perirq (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==>
bisim_perirq_core (RM.GIC, 
		   (IM.G (PCG c)).GIC, 
		   nuvi (RM.C c, 
			 mmu_rpl_rcvd (RM.MMU c), 
			 mem_rpl_rcvd RM.m, 
			 lirq (mem_abs(RM.m) (ADRDS LIRQ)) c), 
		   c)
`;

val bisim_igcirq_core_def = Define `
bisim_igcirq_core (rGIC, iGIC, Nuigc, c) = 
!q id. (q = PIR id) /\ igc_irq_for_core (id,c) 
==> 
((idgic_abs iGIC).Q (PCC c) q = 
case VI rGIC c q of 
  | INACTIVE => INACTIVE
  | PENDING  => if Nuigc (q,c) then INACTIVE else PENDING
  | ACTIVE   => ACTIVE
  | PENDACT  => if Nuigc (q,c) then ACTIVE else PENDACT
)
`;

(* IGC interrupts become visible later *)
val bisim_igcirq_def = Define `bisim_igcirq (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc
==> 
bisim_igcirq_core (RM.GIC, 
		   (IM.G (PCG c)).GIC, 
		   nuigc (RM.C c, 
			  mmu_rpl_rcvd (RM.MMU c), 
			  mem_rpl_rcvd RM.m, 
			  llr (mem_abs(RM.m) (ADRDS LLR)) c), 
		   c)
`;

(* virtual SGI interrupts in refined model have already translated sender,
   need to adapt receiver using PRQ and translate back sender for nuvi search *)
val bisim_sgiirq_core_def = Define `
bisim_sgiirq_core (rGIC,iGIC,Nuvi,c) = 
!q id c'. (q = SGI (id, c', c)) /\ id <=+ 7w /\ (c' < PAR.nc_g (PCG c))
==> 
((idgic_abs iGIC).Q (PCC c) (PRQ (PCG c) q) = 
case VI rGIC c q of 
  | INACTIVE => if Nuvi (PSQ_inv (PCG c) q,c) then PENDING else INACTIVE
  | PENDING  => PENDING
  | ACTIVE   => if Nuvi (PSQ_inv (PCG c) q,c) then PENDACT else ACTIVE
  | PENDACT  => PENDACT
)
`;


(* SGIs are also injected earlier but we need to project core indices *)
val bisim_sgiirq_def = Define `
bisim_sgiirq (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==> 
bisim_sgiirq_core (RM.GIC, 
		   (IM.G (PCG c)).GIC, 
		   nuvi (RM.C c, 
			 mmu_rpl_rcvd (RM.MMU c), 
			 mem_rpl_rcvd RM.m, 
			 lirq (mem_abs(RM.m) (ADRDS LIRQ)) c), 
		   c)
`;

(* RC = receiver core c' *)
val bisim_send_igc_core_def = Define `
bisim_send_igc_core (RC, rGIC, Mbox, Sigc, Nusgi, c') = 
!g g' s. g < PAR.ng /\ g' < PAR.ng /\ g <> g' /\ s < PAR.ns 
      /\ (PCG c' = g') /\ (PAR.cpol s = (g,g'))
==>
   ( ((Sigc g).flags s) <=> Mbox (g,g') )
/\ ( (((Sigc g).addressbook s) = SOME (PCC c')) <=> 
    ?c. c < RPAR.nc /\ (PCG c = g) /\ (c <> c') /\
      (  Q (rGIC) (SGI (7w, c, c')) IN {PENDING; ACTIVE}
      \/ Nusgi (c,c') 
      \/ (Mode RC = 2) /\ (refcore_abs RC).PC IN 
			  {AHV PC_RIGC_RCV_DEACT; AHV PC_RIGC_RETURN} ) 
)
`;


val bisim_send_igc_def = Define `
bisim_send_igc (RM:refined_model, IM:ideal_model) = 
!c'. c' < RPAR.nc /\ (refcore_abs(RM.C 0)).H.init_hv
==>
bisim_send_igc_core (RM.C c',
		     RM.GIC, 
		     mbox (mem_abs RM.m (ADRDS MBOX)),
		     (\g. (IM.G g).sIGC), 
		     nusgi ((\c. RM.C c),
			    (\c. mmu_rpl_rcvd (RM.MMU c)),
			    mem_rpl_rcvd RM.m), 
		     c')
`;

val bisim_ext_def = Define `bisim_ext (RM:refined_model, IM:ideal_model) = 
!g. g < PAR.ng ==>
((IM.G g).E_in = PEL (RM.E_in, g)) /\ ((IM.G g).E_out = PEL (RM.E_out, g))
`;

val bisim_psci_def = Define `bisim_psci (RM:refined_model, IM:ideal_model) = 
!c. c < RPAR.nc ==>
   ((IM.G (PCG c)).PSCI.pow (PCC c) = RM.PSCI.pow c)
/\ ((IM.G (PCG c)).PSCI.events (PCC c) = MAP PEE (RM.PSCI.events c))
`;

val bisim_gicc_reg_def = Define `bisim_gicc_reg (RM:refined_model, IM:ideal_model) = 
!c r. c < RPAR.nc ==>
   ((idgic_abs (IM.G (PCG c)).GIC).gicc (PCC c) r = (gic_abs(RM.GIC)).gicv c r)
`;

(* TODO: do I care about non-accessible registers? should remain unchanged *)
val bisim_gicd_reg_def = Define `bisim_gicd_reg (RM:refined_model, IM:ideal_model) = 
!g r. g < PAR.ng /\ (* (?B. ~fail_gicd(r,B)) /\  *)(refcore_abs(RM.C 0)).H.init_hv ==>
if req_gicd(r,F) then
  (idgic_abs (IM.G g).GIC).gicd r = GICDfltr(g,r,(gic_abs(RM.GIC)).gicd r)
else
  (idgic_abs (IM.G g).GIC).gicd r = gcpys ((mem_abs RM.m) (ADRDS (GCPY g))) (g,r)
`;

val igc_irq_def = Define `igc_irq q = 
?s c c'. s < PAR.ns /\ (PAR.cpol s = (PCG c, PCG c')) /\ (q = SGI (7w, c, c')) 
`;

(* TODO: redundant with gicd reg invariant? *)
val bisim_pi_guest_def = Define `bisim_pi_guest (rGIC:gic, iGIC:idgic, g:num) = 
!q. 
   ((PQQ g q) IN PIRQ g ==>
       ( (PI iGIC (PQQ g q) = NOT_ASSERTED) 
     	 <=> 
         (Q rGIC q = INACTIVE) ) 
    /\ ( (PI iGIC (PQQ g q) = ASSERTED) 
     	 <=> 
         (Q rGIC q = PENDING)  ) 
    /\ ( (PI iGIC (PQQ g q) = FORWARDED) 
     	 <=> 
         (Q rGIC q = ACTIVE)   ) 
    /\ ( (PI iGIC (PQQ g q) = ASS_FWD) 
     	 <=> 
         (Q rGIC q = PENDACT) )  )
/\ ((PQQ g q) IN IPIRQ g ==>
       ( (PI iGIC (PQQ g q) = NOT_ASSERTED) 
     	 <=> 
         (Q rGIC q IN {INACTIVE; ACTIVE}) ) 
    /\ ( (PI iGIC (PQQ g q) = ASSERTED) 
     	 <=> 
         (Q rGIC q IN {PENDING; PENDACT}) )  ) 
`;

(* TODO?: invariant that irqs active and injected at most in one core *)
val bisim_pi_def = Define `bisim_pi (RM:refined_model, IM:ideal_model) = 
!g. g < PAR.ng ==> bisim_pi_guest (RM.GIC, (IM.G g).GIC, g)
`;


(* wrapping up *)

val _ = Datatype `BISIM_CLAUSE = BISIM_CTX | BISIM_MEMORY | BISIM_PERIPH | BISIM_COREREQ_GUEST | BISIM_COREREQ_HYP | BISIM_COREREQ_GICD | BISIM_MMUREQ_GUEST | BISIM_GICDMSG_IDEAL | BISIM_GICDMSG_REFINED | BISIM_SMMUREQ | BISIM_GICCREQ | BISIM_GICDREQ_IDEAL | BISIM_GICDREQ_REFINED | BISIM_GICD_FAIL | BISIM_MEMREQ | BISIM_PERIRQ | BISIM_IGCIRQ | BISIM_SGIIRQ | BISIM_SEND_IGC | BISIM_EXT | BISIM_PSCI | BISIM_GICC_REG | BISIM_GICD_REG | BISIM_PI`;

val bisim_rel_def = Define `bisim_rel (RM : refined_model, c:BISIM_CLAUSE, IM : ideal_model) =
case c of
  | BISIM_CTX => bisim_ctx (RM,IM)
  | BISIM_MEMORY => bisim_memory (RM,IM)
  | BISIM_PERIPH => bisim_periph (RM,IM)
  | BISIM_COREREQ_GUEST => bisim_corereq_guest (RM,IM)
  | BISIM_COREREQ_HYP => bisim_corereq_hyp (RM,IM)
  | BISIM_COREREQ_GICD => bisim_corereq_gicd (RM,IM)
  | BISIM_MMUREQ_GUEST => bisim_mmureq_guest (RM,IM)
  | BISIM_GICDMSG_IDEAL => bisim_gicdmsg_ideal (RM,IM)
  | BISIM_GICDMSG_REFINED => bisim_gicdmsg_refined (RM,IM)
  | BISIM_GICD_FAIL => bisim_gicd_fail (RM,IM)
  | BISIM_SMMUREQ => bisim_smmureq (RM,IM)
  | BISIM_GICCREQ => bisim_giccreq (RM,IM)
  | BISIM_GICDREQ_IDEAL => bisim_gicdreq_ideal (RM,IM)
  | BISIM_GICDREQ_REFINED => bisim_gicdreq_refined (RM,IM)
  | BISIM_MEMREQ => bisim_memreq (RM,IM)
  | BISIM_PERIRQ => bisim_perirq (RM,IM)
  | BISIM_IGCIRQ => bisim_igcirq (RM,IM)
  | BISIM_SGIIRQ => bisim_sgiirq (RM,IM)
  | BISIM_SEND_IGC => bisim_send_igc (RM,IM)
  | BISIM_EXT => bisim_ext (RM,IM)
  | BISIM_PSCI => bisim_psci (RM,IM)
  | BISIM_GICC_REG => bisim_gicc_reg (RM,IM)
  | BISIM_GICD_REG => bisim_gicd_reg (RM,IM)
  | BISIM_PI => bisim_pi (RM,IM)
`;

val SIM_def = Define `SIM (RM : refined_model, IM : ideal_model) =
!C. bisim_rel (RM, C, IM) 
`;

(* by Thomas Tuerk *)
val SIM_EXPAND = save_thm ("SIM_EXPAND",
SIMP_CONV (srw_ss()++DatatypeSimps.expand_type_quants_stateful_ss()) 
  [SIM_def, bisim_rel_def] ``SIM (RM, IM)``)


(***************************)


(******** PRESERVATION PREDICATES ***********)

(* the following predicates describe canonical forms of preservation properties;
   they are mostly introduced for technical reasons to support automatic reasoning,
   but some of them can also make human-readable proofs more concise *)



(* expresses that a given refined step can be matched with ideal steps, so that:
    - we start in the given prestates,
    - reach the given ideal poststate,
    - the transition preserves SIM
   (if the given refined poststate is reachable) *)
val ref_preserves_from_to_def = Define `ref_preserves_from_to RM IM refstep RM' IM' =
       SIM (RM,IM) /\ InvI IM /\ InvR RM /\ refined_trans (RM, refstep, RM')
       ==>
       ?n. ideal_model_comp (IM,n,IM') ∧ SIM (RM',IM')`;

(* expresses that a given refined step can be matched with ideal steps, so that:
    - we start in the given prestates,
    - the transition preserves SIM 
   (if the given refined poststate is reachable)*)
val ref_preserves_from_to_r_def = Define `ref_preserves_from_to_r RM IM refstep RM' =
    ?IM'. ref_preserves_from_to RM IM refstep RM' IM'`;

val ref_preserves_from_to_r_unfold = save_thm("ref_preserves_from_to_r_unfold",
    (SIMP_CONV std_ss [ref_preserves_from_to_r_def, ref_preserves_from_to_def, RIGHT_EXISTS_IMP_THM]
     THENC ONCE_DEPTH_CONV SWAP_EXISTS_CONV)
    ``ref_preserves_from_to_r RM IM refstep RM'``);


(* expresses that a given refined step can be matched with ideal steps, so that:
    - we start in the given prestates,
    - the transition preserves SIM *)
val ref_preserves_from_def = Define `ref_preserves_from RM IM refstep =
    !RM'. ref_preserves_from_to_r RM IM refstep RM'`;

val ref_preserves_from_unfold = save_thm("ref_preserves_from_unfold",
    (SIMP_CONV std_ss [ref_preserves_from_def, ref_preserves_from_to_r_unfold])
    ``ref_preserves_from RM IM refstep``);

(* expresses that a given refined step can be matched with ideal steps,
   so that the transition preserves SIM *)
val ref_preserves_def = Define `ref_preserves refstep =
      !IM RM. ref_preserves_from RM IM refstep`;

val ref_preserves_unfold = save_thm("ref_preserves_unfold",
    (SIMP_CONV std_ss [ref_preserves_def, ref_preserves_from_unfold])
    ``ref_preserves refstep``);


(* expresses that a given ideal step progresses into the given ideal poststate
   and preserves SIM in respect to the given refined step without
   any progress in the refined world *)
val id_preserves_solo_from_to_def = Define `id_preserves_solo_from_to RM IM idstep IM' =
    SIM (RM, IM) /\ InvI IM /\ InvR RM
    ==> ideal_model_trans(IM,idstep,IM') /\ SIM(RM,IM') /\ InvI IM'`;

(* expresses that there is an ideal step that establishes the given postcondition
   and preserves SIM in respect to the given refined step without
   any progress in the refined world *)
val id_solo_preservable_with_cond_from_def = Define `id_solo_preservable_with_cond_from RM IM cond =
    ~cond IM RM /\ SIM (RM, IM) /\ InvI IM /\ InvR RM  ==> 
    ?idstep IM'. ideal_model_trans(IM,idstep,IM') /\ SIM(RM,IM') /\ InvI IM' /\ (cond IM' RM)`;

(* bring related predicates into a canonical order to assist rewriting *)
val pred_reorder_lem =
    store_thm ("pred_reorder_lem",
  `` (InvI i /\ SIM (r,i) = SIM (r,i) /\ InvI i)
  /\ (InvR r /\ SIM (r,i) = SIM (r,i) /\ InvR r)
  /\ (InvR r /\ InvI i = InvI i /\ InvR r)
  /\ (InvI i /\ SIM (r,i) /\ X = SIM (r,i) /\ InvI i /\ X)
  /\ (InvR r /\ SIM (r,i) /\ X = SIM (r,i) /\ InvR r /\ X)
  /\ (InvR r /\ InvI i /\ X = InvI i /\ InvR r /\ X)
  /\ (refined_trans(r,s,r') /\ X = X /\ refined_trans (r,s,r'))
  /\ (InvR r /\ X /\ refined_trans(r,s,r') = X /\ InvR r /\ refined_trans (r,s,r'))
  /\ (InvR r /\ X /\ Y /\ refined_trans(r,s,r') = X /\ Y /\ InvR r /\ refined_trans (r,s,r'))
  /\ (InvI i /\ X /\ InvR r /\ refined_trans(r,s,r') = X /\ InvI i /\ InvR r /\ refined_trans (r,s,r'))
  /\ (InvI i /\ X /\ Y /\ InvR r /\ refined_trans(r,s,r') = X /\ Y /\ InvI i /\ InvR r /\ refined_trans (r,s,r'))
  /\ (SIM (r,i) /\ X /\ InvI i /\ InvR r /\ refined_trans(r,s,r') = X /\ SIM(r,i) /\ InvI i /\ InvR r /\ refined_trans (r,s,r'))
  /\ (SIM (r,i) /\ X /\ Y /\ InvI i /\ InvR r /\ refined_trans(r,s,r') = X /\ Y /\ SIM(r,i) /\ InvI i /\ InvR r /\ refined_trans (r,s,r')) ``,
     SIMP_TAC std_ss [CONJ_ASSOC]
THEN SIMP_TAC std_ss [CONJ_COMM]
THEN METIS_TAC []);





(******** PRESERVATION DECOMPOSITION LEMMAS ***********)

(* the following lemmas help to decompose preservation goals in canonical form
   into subgoals, allowing to handle the matching between ideal and refined world
   step by step *)




(* refined -> ideal:
   introduce a forward prestep in the ideal world only
   and establish some postcondition unless already established;
   split the preservation goal into:
      1. obligations for the introduced prestep
      2. preservation goal almost as before, but assuming
         that the prestep has happened with its postcondition
   -- comes in different flavors *)
val postcond_forwardstep_ideal_lem1 =
   store_thm("postcond_forwardstep_ideal_lem1",
   ``((?RM'. ~cond IM RM /\ SIM (RM,IM) /\ InvI IM /\ InvR RM /\ refined_trans (RM, refstep, RM'))
        ==> ?IM1 R. ideal_model_trans (IM,R,IM1) /\ SIM(RM, IM1) /\ InvI IM1 /\ (cond IM1 RM)) 
   /\
     (!IM. cond IM RM ==> ref_preserves_from RM IM refstep)
  ==>
     ref_preserves_from RM IM refstep``,
  REPEAT STRIP_TAC
   THEN Cases_on `~cond IM RM`
   THEN FULL_SIMP_TAC bool_ss [GSYM LEFT_FORALL_IMP_THM, ref_preserves_from_unfold]
   THEN METIS_TAC [ideal_model_comp_rev_lem]);

val postcond_forwardstep_ideal_lem2 =
   store_thm("postcond_forwardstep_ideal_lem2",
   ``((?RM'. ~cond IM RM /\ refined_trans (RM, refstep, RM'))
        ==> ?IM1 idstep. id_preserves_solo_from_to RM IM idstep IM1 /\ (cond IM1 RM)) 
   /\
     (!IM. cond IM RM ==> ref_preserves_from RM IM refstep)
  ==>
     ref_preserves_from RM IM refstep``,
  REPEAT STRIP_TAC
   THEN Cases_on `~cond IM RM`
   THEN FULL_SIMP_TAC bool_ss [GSYM LEFT_FORALL_IMP_THM, ref_preserves_from_unfold, id_preserves_solo_from_to_def]
   THEN METIS_TAC [ideal_model_comp_rev_lem]);

val postcond_forwardstep_ideal_lem3 =
   store_thm("postcond_forwardstep_ideal_lem3",
   ``(!RM'. (refined_trans (RM, refstep, RM') ==> id_solo_preservable_with_cond_from RM IM cond)) 
   /\
     (!IM. cond IM RM ==> ref_preserves_from RM IM refstep)
  ==>
     ref_preserves_from RM IM refstep``,
  REPEAT STRIP_TAC
   THEN Cases_on `~cond IM RM`
   THEN FULL_SIMP_TAC bool_ss [GSYM LEFT_FORALL_IMP_THM, ref_preserves_from_unfold,
                               id_solo_preservable_with_cond_from_def]
   THEN METIS_TAC [ideal_model_comp_rev_lem]);



(* refined -> ideal:
   decompose preservation goal for solo-steps
   of the ideal world into the essential proof obligations,
   if step is internal and does not change mem_abs *)
val id_internal_solo_with_cond_obligations_lem =
    store_thm("id_internal_solo_with_cond_obligations_lem",
    ``( ~cond IM RM /\ SIM (RM, IM) /\ InvI IM /\ InvR RM
        ==>
        (?intstep g G'.
          g < PAR.ng /\
          ideal_guest_trans(IM.G g, g, INTERNAL intstep, G') /\
          (mem_abs (IM.G g).m = mem_abs G'.m) /\
          SIM (RM, IM with G := (g =+ G') IM.G) /\
          cond (IM with G := (g =+ G') IM.G) RM))
      ==> id_solo_preservable_with_cond_from RM IM cond``,
    REPEAT STRIP_TAC THEN
    SIMP_TAC bool_ss [id_solo_preservable_with_cond_from_def] THEN
    REPEAT STRIP_TAC THEN 
    FULL_SIMP_TAC bool_ss [] THEN
    EXISTS_TAC ``C_INTERNAL`` THEN
    EXISTS_TAC ``IM with G := (g =+ G') IM.G`` THEN
    ASM_SIMP_TAC std_ss [] THEN
    ASSUME_TAC (SPECL [``IM:ideal_model``, ``IM with G := (g =+ G') IM.G``] syncInv_lem) THEN
    FULL_SIMP_TAC (srw_ss()) [ideal_model_trans_def, comp_rule_internal_def,
                              InvI_def, combinTheory.APPLY_UPDATE_THM] THEN
    METIS_TAC [InvG_thm, sync_shared_mem_upd_of_guest_def]);


val mem_read_lem = store_thm("mem_read_lem", ``
!RM IM g a d.
   SIM (RM, IM)
/\ g < PAR.ng
/\ (47><12) a IN PAR.A_G g 
/\ (47><12) a NOTIN A_gicper
==>
(mem_read (mem_abs RM.m) (ipat g a) d = mem_read (mem_abs (IM.G g).m) a d)
``,
  REPEAT STRIP_TAC >>
  `mem_abs(RM.m) (THE(Trans g ((47><12)a))) = 
   mem_abs((IM.G g).m) ((47><12)a)` by (
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memory_def]
  ) >>
  `(47><12) a <> Agicd` by (
      METIS_TAC [Agicd_A_gicper_lem, NO_MEMBER_NOT_EQ_RW]
  ) >>
  `IS_SOME (Trans g ((47><12) a))` by (
      METIS_TAC [guest_adr_trans_lem]
  ) >>
  FULL_SIMP_TAC (srw_ss()) [optionTheory.IS_SOME_EXISTS] >>
  RW_TAC (srw_ss()) [mem_read_def, ipat_def, ATrans_def, bytext_def,
		     optionTheory.THE_DEF] >> 
  RW_TAC (srw_ss()) [PAdr_extract_lem, bx_extract_lem] >>
  FULL_SIMP_TAC (srw_ss()) [optionTheory.THE_DEF]
);

val guest_Trreq_lem = store_thm("guest_Trreq_lem", ``
!g r. 
   g < PAR.ng
/\ PAdr r IN PAR.A_G g
/\ PAdr r NOTIN A_gicper
/\ IS_SOME (Trans g (PAdr r))
==>
PAdr (Trreq g r) IN RPAR.Amap (GUEST g) 
``,
  RW_TAC (srw_ss()) [Trreq_PAdr_Trans_lem] >>
  `PAdr r <> Agicd` by (
      CCONTR_TAC >>
      FULL_SIMP_TAC (srw_ss()) [Agicd_A_gicper_lem]
  ) >>
  IMP_RES_TAC guest_adr_trans_lem
);

val not_A_gicper_Trreq_lem = store_thm("not_A_gicper_Trreq_lem", ``
!g r. 
   g < PAR.ng
/\ PAdr r NOTIN A_gicper
/\ IS_SOME (Trans g (PAdr r))
==>
PAdr (Trreq g r) NOTIN A_gicper 
``,
  RW_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem] >>
  MATCH_MP_TAC A_gicper_Trans_lem >>
  FULL_SIMP_TAC (srw_ss()) [A_gicper_def, gicAR_def] >>
  `!p. p < RPAR.np ==> (RPAR.Amap (PER p) = PAR.A_gp (PPG p) (PPP p))` by (
      METIS_TAC [coupling_axiom]
  ) >>
  RW_TAC (srw_ss()) [IS_SOME_ATrans_lem] >> (
      METIS_TAC [PPGP_inv_rewrites, good_proj_in_range_impls]
  )
);

val A_gicper_Trreq_lem = store_thm("A_gicper_Trreq_lem", ``
!g r. 
   g < PAR.ng
/\ PAdr r IN A_gicper
/\ IS_SOME (Trans g (PAdr r))
==>
PAdr (Trreq g r) IN A_gicper 
``,
  RW_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem, ATrans_def, IS_SOME_ATrans_lem] >>
  IMP_RES_TAC ( Trans_adr_A_gicper_lem |> SPEC_ALL 
				       |> CONTRAPOS 
				       |> SIMP_RULE std_ss [] ) >>
  PAT_X_ASSUM ``!g. x`` (
      fn thm => ASSUME_TAC ( SPEC ``g:num`` thm )
  ) >>
  REV_FULL_SIMP_TAC std_ss [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
);

val mem_access_bisim_lem = store_thm("mem_access_bisim_lem", ``
!RM IM g r q a m' im' rid iid.
   g < PAR.ng
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ mem_step_snd_rpl (RM.m, Trrpl g q, rid, m')
/\ mem_step_snd_rpl ((IM.G g).m, q, iid, im')
/\ (q, iid) NOTIN mem_rpl_rcvd (IM.G g).m
/\ (Trrpl g q, rid) NOTIN mem_rpl_rcvd RM.m
/\ match (r,q)
/\ match (Trreq g r, Trrpl g q)
/\ IS_SOME (Trans g (PAdr r))
/\ req_aligned r
/\ PAdr r IN PAR.A_G g
/\ PAdr r NOTIN A_gicper
/\ a IN PAR.A_G g
/\ a NOTIN A_gicper
==>
(mem_abs im' a = mem_abs m' (THE (Trans g a)))
``,
  REPEAT STRIP_TAC >>
  `req_aligned (Trreq g r)` by ( IMP_RES_TAC Trreq_aligned_lem ) >>
  Cases_on `a <> PAdr r`
  >| [(* case: other pages *)
      `THE (Trans g a) <> PAdr (Trreq g r)` by (
          FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_ATrans_lem] >>
          IMP_RES_TAC IS_SOME_ATrans_lem >> 
	  `ATrans g (PAdr r) <> ATrans g a` by (
              METIS_TAC [ATrans_inj]
	  ) >>
	  `a <> Agicd` by (
	      CCONTR_TAC >>
	      FULL_SIMP_TAC (srw_ss()) [Agicd_A_gicper_lem]
	  ) >>
	  `IS_SOME (Trans g a)` by ( 
	      METIS_TAC [guest_adr_trans_lem]
	  ) >>
	  METIS_TAC [ATrans_def]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      IMP_RES_TAC bisim_memory_def >>
      METIS_TAC [mem_aligned_unchanged_lem]
      ,
      (* case: accessed page *)
      FULL_SIMP_TAC (srw_ss()) [] >>
      RW_TAC (srw_ss()) [] >>
      Cases_on `Wreq r`
      >| [(* case: write *) 
	  Cases_on `r` >> (
	      Cases_on `q` >> (
	          FULL_SIMP_TAC (srw_ss()) [Wreq_def, match_def]
	      )
	  ) 
	  >| [(* case: write reply *)
	      `mem_abs im' = mem_abs (
	       memory_upd (
	           (47 >< 12) c, 
		   page_write (mem_abs (IM.G g).m ((47 >< 12) c),
			       (11 >< 0) c,n,l) )
			  (IM.G g).m)` by (
	          METIS_TAC [mem_write_axiom]
	      ) >>
	      FULL_SIMP_TAC (srw_ss()) [Trrpl_def] >>
	      `mem_abs m' = mem_abs (
	       memory_upd (
	           (47 >< 12) (ipat g c), 
		   page_write (mem_abs RM.m ((47 >< 12) (ipat g c)),
			       (11 >< 0) (ipat g c),n,l) )
			  RM.m)` by (
	          METIS_TAC [mem_write_axiom]
	      ) >>
	      FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def] >>
	      `mem_abs (IM.G g).m ((47 >< 12) c) = 
	       mem_abs RM.m ((47 >< 12) (ipat g c))` by (
	          FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND, ipat_def, ATrans_def] >>
		  REWRITE_TAC [PAdr_extract_lem] >>
		  METIS_TAC [bisim_memory_def]
	      ) >>
	      ASM_REWRITE_TAC [] >>
	      RW_TAC (srw_ss()) [ipat_def, ATrans_def, PAdr_extract_lem, 
				 bx_extract_lem] >>
	      REWRITE_TAC [memory_upd_mem_abs_id_lem]
	      ,
	      (* case: write fault *)
	      `Frpl (Fault (Write c n l m) f)` by (
	          RW_TAC (srw_ss()) [Frpl_def]
	      ) >>
	      METIS_TAC [mem_fault_axiom]
	     ]
	  ,
	  (* case: unchanged *)
	  Cases_on `r` >> (
	      Cases_on `q` >> (
	          FULL_SIMP_TAC (srw_ss()) [Wreq_def, match_def]
	      )
	  )
	  >| [(* case: read reply *)
	      FULL_SIMP_TAC (srw_ss()) [Trrpl_def] >>
	      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
              IMP_RES_TAC bisim_memory_def >>
	      METIS_TAC [mem_read_axiom]
	      ,
	      (* case: read fault *)
	      `Frpl (Fault (Read c n m) f)` by (
	          RW_TAC (srw_ss()) [Frpl_def]
	      ) >>
	      METIS_TAC [mem_fault_axiom]
	      ,
	      (* case: walk reply *)
	      FULL_SIMP_TAC (srw_ss()) [Trrpl_def] >>
	      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
              IMP_RES_TAC bisim_memory_def >>
	      METIS_TAC [mem_walk_axiom]
	      ,
	      (* case: walk fault *)
	      `Frpl (Fault (Walk c m) f)` by (
	          RW_TAC (srw_ss()) [Frpl_def]
	      ) >>
	      METIS_TAC [mem_fault_axiom]
	     ]
	 ]	      
     ]	    
);


val no_igc_write_mem_upd_others_lem = 
store_thm("no_igc_write_mem_upd_others_lem", ``
!RM IM g r q m' im' rid iid.
   g < PAR.ng
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ mem_step_snd_rpl (RM.m, Trrpl g q, rid, m')
/\ mem_step_snd_rpl ((IM.G g).m, q, iid, im')
/\ (q, iid) NOTIN mem_rpl_rcvd (IM.G g).m
/\ (Trrpl g q, rid) NOTIN mem_rpl_rcvd RM.m
/\ match (r,q)
/\ match (Trreq g r, Trrpl g q)
/\ IS_SOME (Trans g (PAdr r))
(* /\ IS_SOME (Trans (PPG n) (Rpl_PAdr q)) *)
/\ req_aligned (Trreq g r)  
/\ PAdr r IN PAR.A_G g
/\ PAdr r NOTIN A_gicper
/\ (PAdr r NOTIN A_IGCin g /\ PAdr r NOTIN A_IGCout g \/ ~Wreq r)
==>
!g' a. g' < PAR.ng /\ g <> g' /\ a IN PAR.A_G g' /\ a NOTIN A_gicper ==> 
       (mem_abs (IM.G g').m a = mem_abs m' (THE (Trans g' a)))
``,
  RW_TAC (srw_ss()) [] >> (
      `a <> Agicd` by (
          CCONTR_TAC >>
          FULL_SIMP_TAC (srw_ss()) [Agicd_A_gicper_lem]
      ) >>
      `IS_SOME (Trans g' a) /\ THE(Trans g' a) IN RPAR.Amap (GUEST g')` by (
          METIS_TAC [guest_adr_trans_lem]
      )
  )
  >| [(* case: address not in A_IGCout *)
      `PAdr (Trreq g r) NOTIN RPAR.Amap (GUEST g')` by (
          RW_TAC (srw_ss()) [Trreq_PAdr_Trans_lem] >>
	  METIS_TAC [unshared_guest_mem_Trans_lem]
      ) >>
      `mem_abs m' (THE (Trans g' a)) = mem_abs RM.m (THE (Trans g' a))` by (
          METIS_TAC [mem_unchanged_lem]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memory_def]
      ,
      (* case: no write *)
      `~Wreq (Trreq g r)` by (
          Cases_on `r` >> (
	      FULL_SIMP_TAC (srw_ss()) [Trreq_def, Wreq_def]
	  )
      ) >>
      `mem_abs m' (THE (Trans g' a)) = mem_abs RM.m (THE (Trans g' a))` by (
          METIS_TAC [mem_unchanged_lem]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memory_def]
     ]
);


val igc_write_mem_upd_others_lem = store_thm("igc_write_mem_upd_others_lem", ``
!RM IM g g2 r q m' im' rid iid s a2.
   g < PAR.ng
/\ SIM (RM,IM)
/\ InvR RM
/\ InvI IM
/\ mem_step_snd_rpl (RM.m, Trrpl g q, rid, m')
/\ mem_step_snd_rpl ((IM.G g).m, q, iid, im')
/\ (q, iid) NOTIN mem_rpl_rcvd (IM.G g).m
/\ (Trrpl g q, rid) NOTIN mem_rpl_rcvd RM.m
/\ match (r,q)
/\ match (Trreq g r, Trrpl g q)
/\ IS_SOME (Trans g (PAdr r))
/\ req_aligned (Trreq g r)  
/\ PAdr r IN PAR.A_G g
/\ PAdr r NOTIN A_gicper
/\ Wreq r
/\ s < PAR.ns
/\ g2 < PAR.ng
/\ (PAR.cpol s = (g,g2))
/\ (PAR.igca s = (PAdr r,a2))
==>
!g' a. g' < PAR.ng /\ g <> g' /\ a IN PAR.A_G g' /\ a NOTIN A_gicper 
       /\ (g' <> g2 \/ a <> a2) 
       ==> 
       (mem_abs (IM.G g').m a = mem_abs m' (THE (Trans g' a)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  REPEAT GEN_TAC >>
  MATCH_MP_TAC ( prove(``(A /\ B /\ C /\ D ==> E ==> X) 
                             ==>
                         (A /\ B /\ C /\ D /\ E ==> X)``, METIS_TAC []) ) >>
  STRIP_TAC >>
  MATCH_MP_TAC ( prove(``((A \/ B /\ ~A) ==> X) 
                             ==>
                         ((A \/ B) ==> X)``, METIS_TAC []) ) >>  
  RW_TAC (srw_ss()) [] >> (
      `a <> Agicd` by (
          CCONTR_TAC >>
          FULL_SIMP_TAC (srw_ss()) [Agicd_A_gicper_lem]
      ) >>
      `IS_SOME (Trans g' a) /\ THE(Trans g' a) IN RPAR.Amap (GUEST g')` by (
          METIS_TAC [guest_adr_trans_lem]
      )
  )
  >| [(* case: address in other guest *)
      `PAdr (Trreq g r) NOTIN RPAR.Amap (GUEST g')` by (
          RW_TAC (srw_ss()) [Trreq_PAdr_Trans_lem] >>
	  METIS_TAC [igc_chan_other_guest_lem]
      ) >>
      `mem_abs m' (THE (Trans g' a)) = mem_abs RM.m (THE (Trans g' a))` by (
          METIS_TAC [mem_unchanged_lem]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memory_def]
      ,
      (* case: write to other address in g2 *)
      `Trans g (PAdr r) = Trans g' a2` by (
          METIS_TAC [Trans_axiom,pairTheory.FST, pairTheory.SND]
      ) >>
      `IS_SOME (Trans g' a2)` by (
          METIS_TAC []
      ) >>
      `Trans g' a <> Trans g' a2` by (
          METIS_TAC [Trans_axiom]
      ) >>
      `PAdr (Trreq g r) NOTIN {THE (Trans g' a)}` by (
          FULL_SIMP_TAC (srw_ss()) [Trreq_PAdr_Trans_lem, 
				    optionTheory.IS_SOME_EXISTS] >>
	  METIS_TAC []
      ) >>
      `THE (Trans g' a) IN {THE (Trans g' a)}` by (
          FULL_SIMP_TAC (srw_ss()) []
      ) >>
      `mem_abs m' (THE (Trans g' a)) = mem_abs RM.m (THE (Trans g' a))` by (
          METIS_TAC [mem_unchanged_lem]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [SIM_EXPAND] >>
      METIS_TAC [bisim_memory_def]
     ]
);


val nuvi_guest_mode_lem = store_thm("nuvi_guest_mode_lem", ``
!RC MMUrpl MEMrpl Lirq irq c. 
   Mode RC < 2 
==>
~(nuvi (RC,MMUrpl,MEMrpl,Lirq) (irq, c))
``,
  FULL_SIMP_TAC arith_ss [nuvi_def]
);

val nuvi_boot_mode_lem = store_thm("nuvi_boot_mode_lem", ``
!RC MMUrpl MEMrpl Lirq irq c. 
   (Mode RC = 3) 
==>
~(nuvi (RC,MMUrpl,MEMrpl,Lirq) (irq, c))
``,
  FULL_SIMP_TAC arith_ss [nuvi_def]
);

val nuvi_guest_mode_K_lem = store_thm("nuvi_guest_mode_K_lem", ``
!RC MMUrpl MEMrpl Lirq. 
   Mode RC < 2 
==>
(nuvi (RC,MMUrpl,MEMrpl,Lirq) = K F)
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [FUN_EQ_THM, combinTheory.K_THM] >>
  STRIP_TAC >>
  `?irq c. x = (irq,c)` by ( RW_TAC (srw_ss()) [pairTheory.pair_CASES] ) >>
  RW_TAC (srw_ss()) [nuvi_guest_mode_lem]
);

val nuvi_other_core_reply_lem = store_thm("nuvi_other_core_reply_lem", ``
!RC MMUrpl MEMrpl Lirq irq c q c'. 
   c < RPAR.nc 
/\ c' < RPAR.nc
/\ c <> c'
==>
(nuvi (RC,MMUrpl,MEMrpl UNION {(q, CoreSender c')},Lirq) (irq,c) =
 nuvi (RC,MMUrpl,MEMrpl,Lirq) (irq,c))
``,
  RW_TAC (srw_ss()) [nuvi_def, pend_rpl_def]
);

val nuigc_guest_mode_lem = store_thm("nuigc_guest_mode_lem", ``
!RC MMUrpl MEMrpl Llr irq c. 
   Mode RC < 2 
==>
~(nuigc (RC,MMUrpl,MEMrpl,Llr) (irq, c))
``,
  FULL_SIMP_TAC arith_ss [nuigc_def]
);

val nuigc_boot_mode_lem = store_thm("nuigc_boot_mode_lem", ``
!RC MMUrpl MEMrpl Llr irq c. 
   (Mode RC = 3) 
==>
~(nuigc (RC,MMUrpl,MEMrpl,Llr) (irq, c))
``,
  FULL_SIMP_TAC arith_ss [nuigc_def]
);

val nuigc_guest_mode_K_lem = store_thm("nuigc_guest_mode_K_lem", ``
!RC MMUrpl MEMrpl Llr. 
   Mode RC < 2 
==>
(nuigc (RC,MMUrpl,MEMrpl,Llr) = K F)
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [FUN_EQ_THM, combinTheory.K_THM] >>
  STRIP_TAC >>
  `?irq c. x = (irq,c)` by ( RW_TAC (srw_ss()) [pairTheory.pair_CASES] ) >>
  RW_TAC (srw_ss()) [nuigc_guest_mode_lem]
);

val nuigc_other_core_reply_lem = store_thm("nuigc_other_core_reply_lem", ``
!RC MMUrpl MEMrpl Llr irq c q c'. 
   c < RPAR.nc 
/\ c' < RPAR.nc
/\ c <> c'
==>
(nuigc (RC,MMUrpl,MEMrpl UNION {(q, CoreSender c')},Llr) (irq, c) = 
 nuigc (RC,MMUrpl,MEMrpl,Llr) (irq, c))
``,
  RW_TAC (srw_ss()) [nuigc_def, pend_rpl_def]
);

val nusgi_guest_mode_lem = store_thm("nusgi_guest_mode_lem", ``
!RCs MMUrpl MEMrpl c c'. 
   Mode (RCs c) < 2 
==>
~(nusgi (RCs,MMUrpl,MEMrpl) (c, c'))
``,
  FULL_SIMP_TAC arith_ss [nusgi_def]
);

val nusgi_boot_mode_lem = store_thm("nusgi_boot_mode_lem", ``
!RCs MMUrpl MEMrpl c c'. 
   (Mode (RCs c) = 3) 
==>
~(nusgi (RCs,MMUrpl,MEMrpl) (c, c'))
``,
  FULL_SIMP_TAC arith_ss [nusgi_def]
);

val nusgi_other_core_reply_lem = store_thm("nusgi_other_core_reply_lem", ``
!RC MMUrpl MEMrpl s r q c. 
   s < RPAR.nc 
/\ c < RPAR.nc
/\ s <> c
==>
(nusgi (RC,MMUrpl,MEMrpl UNION {(q, CoreSender c)}) (s, r) = 
 nusgi (RC,MMUrpl,MEMrpl) (s, r))
``,
  RW_TAC (srw_ss()) [nusgi_def, pend_rpl_def]
);


val bisim_gicd_reg_vol_lem = store_thm("bisim_gicd_reg_vol_lem", ``
!RM IM g c.
   g < PAR.ng
/\ c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
==>
(!R. (idgic_abs (IM.G g).GIC).gicd (VOL R) =
     GICDfltr (g,(VOL R),(gic_abs RM.GIC).gicd (VOL R)))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC init_hv_lem >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_gicd_reg_def >>
  FULL_SIMP_TAC (srw_ss()) [req_gicd_F_lem] >>
  METIS_TAC []
);

val soft_Mode_lem = store_thm("soft_Mode_lem", ``
!RC. Mode RC < 2 \/ (Mode RC = 2) ==> ~soft (refcore_abs RC)
``,
  REPEAT STRIP_TAC >> (
      IMP_RES_TAC warm_soft_axiom >>
      FULL_SIMP_TAC arith_ss [Mode_def, mode_def]
  )  
);

val soft_mode_lem = store_thm("soft_mode_lem", ``
!RC. mode RC < 2 \/ (mode RC = 2) ==> ~soft RC
``,
  REPEAT STRIP_TAC >> (
      IMP_RES_TAC warm_soft_axiom >>
      FULL_SIMP_TAC arith_ss []
  )  
);

val bisim_gicd_reg_guest_mode_lem = 
store_thm("bisim_gicd_reg_guest_mode_lem", ``
!RM IM g c.
   g < PAR.ng
/\ c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ SimInvR RM
/\ Mode (RM.C c) < 2
==>
(!r. (idgic_abs (IM.G g).GIC).gicd r =
     GICDfltr (g,r,(gic_abs RM.GIC).gicd r))
``,
  REPEAT STRIP_TAC >>
  Cases_on `?R. r = VOL R`
  >| [(* case: VOL R *)
      RW_TAC std_ss [] >>
      METIS_TAC [bisim_gicd_reg_vol_lem]
      ,
      (* case: CONST or MUTE *)
      IMP_RES_TAC init_hv_lem >>
      `(idgic_abs (IM.G g).GIC).gicd r =
       gcpys (mem_abs RM.m (ADRDS (GCPY g))) (g,r)` by (
          Q.ABBREV_TAC `nex = ?R. r = VOL R` >>
          FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
          Q.UNABBREV_TAC `nex` >>
          IMP_RES_TAC ( bisim_gicd_reg_def 
			    |> SIMP_RULE std_ss [req_gicd_F_lem] ) >>
	  METIS_TAC []
      ) >>
      `Glock((mem_abs RM.m)(ADRDS GLOCK)) = NONE` by (
          METIS_TAC [SimInvR_def]
      ) >>
      FULL_SIMP_TAC std_ss [InvR_EXPAND] >> 
      `no_pending_hyp_gicd_write(RM,g,r)` by (
          METIS_TAC [ref_inv_hyp_glock_def]
      ) >>
      IMP_RES_TAC ( ref_inv_hyp_gcpy_def
			|> SIMP_RULE std_ss [req_gicd_F_lem] )
     ]
);


val bisim_guest_mode_lem = store_thm("bisim_guest_mode_lem", ``
!RM IM c.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ (refcore_abs (RM.C c)).active
==>
    iMode ((IM.G (PCG c)).C (PCC c)) < 2
 /\ (idcore_abs ((IM.G (PCG c)).C (PCC c))).active
``,
  NTAC 4 STRIP_TAC >>
  IMP_RES_TAC InvR_core_launched_lem >>
  IMP_RES_TAC soft_Mode_lem >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  IMP_RES_TAC bisim_ctx_core_def >>
  REV_FULL_SIMP_TAC std_ss [Mode_def, iMode_def, mode_def]
);

val bisim_refined_core_active_lem = store_thm("bisim_refined_core_active_lem", ``
!RM IM c.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ (idcore_abs ((IM.G (PCG c)).C (PCC c))).active
==>
(refcore_abs (RM.C c)).active
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC InvR_core_launched_lem >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  IMP_RES_TAC bisim_ctx_core_def
);


val bisim_guest_core_lem = store_thm("bisim_guest_core_lem", ``
!RM IM c.
   c < RPAR.nc
/\ SIM (RM,IM)
/\ InvR RM
/\ Mode (RM.C c) < 2
/\ (refcore_abs (RM.C c)).active
==>
    iMode ((IM.G (PCG c)).C (PCC c)) < 2
 /\ (idcore_abs ((IM.G (PCG c)).C (PCC c))).active
 /\ ((idcore_abs ((IM.G (PCG c)).C (PCC c))).GPR = (refcore_abs (RM.C c)).GPR)
 /\ ((idcore_abs ((IM.G (PCG c)).C (PCC c))).PC = (refcore_abs (RM.C c)).PC)
 /\ ((idcore_abs ((IM.G (PCG c)).C (PCC c))).PSTATE = 
     (refcore_abs (RM.C c)).PSTATE)
 /\ (!r. (idcore_abs ((IM.G (PCG c)).C (PCC c))).SPR r = 
         (refcore_abs (RM.C c)).SPR (INL r))
 /\ (id_abs_int ((IM.G (PCG c)).C (PCC c)) = ref_abs_int (RM.C c))
 /\ (idcore_req_sent ((IM.G (PCG c)).C (PCC c)) = 
     refcore_req_sent (RM.C c))
``,
  NTAC 4 STRIP_TAC >>
  IMP_RES_TAC InvR_core_launched_lem >>
  IMP_RES_TAC soft_Mode_lem >>
  FULL_SIMP_TAC std_ss [SIM_EXPAND] >>
  IMP_RES_TAC bisim_ctx_def >>
  IMP_RES_TAC bisim_ctx_core_def >>
  REV_FULL_SIMP_TAC arith_ss [Mode_def, iMode_def, mode_def, 
			      id_abs_int_def, ref_abs_int_def] >>
  IMP_RES_TAC bisim_corereq_guest_def >>
  IMP_RES_TAC bisim_corereq_guest_core_def >>
  FULL_SIMP_TAC std_ss [Mode_def]
);


(*************** finish ***********)

val _ = export_theory();
