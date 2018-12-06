(* This theory contains general lemmas
   on arithmetics, lists, words, sets and 
   other standard HOL objects, (possibly)
   applied in but not limited to the project. 

   Preferably, this theory should not depend
   on other project theories, but can depend
   on libraries such as tacticsLib, toolboxLib
   etc. *)


(************* Loading ***************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 
open pred_setTheory;
open tacticsLib;

val _ = new_theory "math_lemmas";



(************** trivia *************)


(* oneTheory.one is more general *)
(* 
val unit_arb_lem = 
    store_thm ("unit_arb_lem",
               ``ARB = ()``,
               Cases_on `ARB:unit` THEN RW_TAC (srw_ss()) []);
*)

(* this is lemma TRUTH *)
(*
val trivially_true =
    store_thm ("trivially_true",
               ``T``,
               RW_TAC (srw_ss()) []);
*)

(************* logic *******************)

(* this is lemma boolTheory.COND_ID *)
(*
val cond_merge_lem = 
    store_thm("cond_merge_lem",
    ``!cond x. (if cond then x else x) = x``,
     METIS_TAC []);
*)

val imp_merge_lem1 = 
    store_thm("imp_merge_lem1",
    ``(A ==> B) ==> (~A ==> B) ==> B``,
     METIS_TAC []);

val imp_merge_lem2 = 
    store_thm("imp_merge_lem2",
    ``((A ==> B) /\ (~A ==> B)) = B``,
     METIS_TAC []);

val imp_merge_lem3 =
    store_thm("imp_merge_lem3",
    ``  (( A ==> B) ==> ((~A ==> B) = B))
     /\ ((~A ==> B) ==> (( A ==> B) = B))``,
    METIS_TAC []);

(************ quantifiers **********)

(* this is FORALL_AND_THM *)
(*
val forall_and_lem = 
    store_thm("forall_and_lem",
       ``!P Q. (!x y. P x /\ Q y) = ((!x. P x) /\ (!y. Q y))``,
       RW_TAC (srw_ss()) [] THEN EQ_TAC THEN RW_TAC (srw_ss()) []);
*)


(************* Lists  ****************)

(* GENLIST I = COUNT_LIST *)
val genlist_triple_lem =
      store_thm("genlist_triple_lem",
       ``!s x. (s < x) ==>
          (GENLIST I x =
           GENLIST I s ++ [s] ++ GENLIST (\t. s + (t + 1)) (x − (s + 1)))``,
       RW_TAC (srw_ss()) []
         THEN `GENLIST I ((x - (1+s)) + (1+s)) = ((GENLIST I s) ++ (GENLIST (\t. I (t + s)) 1)) ++ (GENLIST (\t. I (t + (1+s))) (x - (1 + s)))` by RW_TAC (bool_ss) [listTheory.GENLIST_APPEND]
         THEN UNDISCH_ALL_TAC
         THEN RW_TAC (arith_ss) []
         THEN FULL_SIMP_TAC (srw_ss()) []);

val genlist_boundaries_lem1 =
      store_thm("genlist_boundaries_lem1",
       ``EVERY (\s. s < lim) (FILTER filter (GENLIST I lim))``,
       FULL_SIMP_TAC arith_ss [rich_listTheory.EVERY_GENLIST, listTheory.EVERY_FILTER]);

val genlist_boundaries_lem2 =
      store_thm("genlist_boundaries_lem2",
       ``EVERY (\s. s < lim) (FILTER filter (GENLIST (\t. s + (t + 1)) (lim - (s + 1))))``,
       FULL_SIMP_TAC arith_ss [rich_listTheory.EVERY_GENLIST, listTheory.EVERY_FILTER]);


val every_filter_lem =
    store_thm("every_filter_lem",
       ``EVERY P (FILTER P (lst: num list))``,
       RW_TAC (srw_ss()) [listTheory.EVERY_FILTER]);



(**************** sets ******************)

(* Looks a bit weird, sounds like SUBSET_EMPTY +  NOT_IN_EMPTY 
val subset_of_empty_lem =
      store_thm("subset_of_empty_lem",
        ``!s r. (s SUBSET EMPTY) ==> (s = EMPTY) /\ (r NOTIN s)``,
        FULL_SIMP_TAC (srw_ss()) []);
*)


val OPTION_TO_SET_def = Define `
  (OPTION_TO_SET NONE = {}) /\
  (OPTION_TO_SET (SOME x) = {x})`

val IN_OPTION_TO_SET = store_thm ("IN_OPTION_TO_SET",
  ``x IN (OPTION_TO_SET opt) <=> (opt = SOME x)``,
Cases_on `opt` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, NOT_IN_EMPTY, IN_INSERT] THEN
  PROVE_TAC[]
))

val OPTION_TO_SET_INJ = store_thm ("OPTION_TO_SET_INJ",
  ``(OPTION_TO_SET opt1 = OPTION_TO_SET opt2) <=> (opt1 = opt2)``,

Cases_on `opt1` THEN Cases_on `opt2` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, NOT_IN_EMPTY, IN_INSERT, EXTENSION] THEN
  PROVE_TAC[]
));

val FINITE_OPTION_TO_SET = store_thm ("FINITE_OPTION_TO_SET",
  ``FINITE (OPTION_TO_SET opt)``,
Cases_on `opt` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, FINITE_EMPTY, FINITE_INSERT]
));

val CARD_OPTION_TO_SET_EQ_EMPTY = store_thm ("CARD_OPTION_TO_SET_EQ_EMPTY",
  ``((OPTION_TO_SET opt) = EMPTY) <=> (opt = NONE)``,
Cases_on `opt` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, NOT_INSERT_EMPTY]
));

val CARD_OPTION_TO_SET_0 = store_thm ("CARD_OPTION_TO_SET_0",
  ``(CARD (OPTION_TO_SET opt) = 0) <=> (opt = NONE)``,
Cases_on `opt` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, CARD_EMPTY, CARD_INSERT, FINITE_EMPTY,
    NOT_IN_EMPTY]
));

val CARD_OPTION_TO_SET_1 = store_thm ("CARD_OPTION_TO_SET_1",
  ``(CARD (OPTION_TO_SET opt) = 1) <=> (IS_SOME opt)``,
Cases_on `opt` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, CARD_EMPTY, CARD_INSERT, FINITE_EMPTY,
    NOT_IN_EMPTY]
));

val CARD_OPTION_TO_SET_LE_1 = store_thm ("CARD_OPTION_TO_SET_LE_1",
  ``CARD (OPTION_TO_SET opt) <= 1``,
Cases_on `opt` THEN (
  SIMP_TAC std_ss [OPTION_TO_SET_def, CARD_EMPTY, CARD_INSERT, FINITE_EMPTY,
    NOT_IN_EMPTY]
));

val CARD_LEQ_1_IMPLIES_OPTION_TO_SET = store_thm ("CARD_LEQ_1_IMPLIES_OPTION_TO_SET",
  ``(CARD X <= 1) ==> FINITE X ==> ?opt. X = OPTION_TO_SET opt``,

REPEAT STRIP_TAC THEN
`(CARD X = 0) \/ (CARD X = 1)` by DECIDE_TAC THENL [
   `X = EMPTY` by PROVE_TAC[CARD_EQ_0] THEN
   Q.EXISTS_TAC `NONE` THEN
   ASM_REWRITE_TAC [OPTION_TO_SET_def],

   `?x. X = {x}` by METIS_TAC[SING_DEF, SING_IFF_CARD1] THEN
   Q.EXISTS_TAC `SOME x` THEN
   ASM_REWRITE_TAC [OPTION_TO_SET_def]
]);


val CARD_LEQ_1_OPTION_TO_SET = store_thm ("CARD_LEQ_1_OPTION_TO_SET",
  ``((CARD X <= 1) /\ FINITE X) <=> ?opt. X = OPTION_TO_SET opt``,

EQ_TAC THEN1 PROVE_TAC[CARD_LEQ_1_IMPLIES_OPTION_TO_SET] THEN
SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, CARD_OPTION_TO_SET_LE_1,
  FINITE_OPTION_TO_SET]);


val _ = export_rewrites ["OPTION_TO_SET_def", "IN_OPTION_TO_SET", "OPTION_TO_SET_INJ",
  "FINITE_OPTION_TO_SET", "CARD_OPTION_TO_SET_0", "CARD_OPTION_TO_SET_1",
  "CARD_OPTION_TO_SET_LE_1", "CARD_OPTION_TO_SET_EQ_EMPTY"];


(* Unit and singleton sets are defined a bit weird. I wonder whether this is really needed *)
val max_one_element_lem = 
      store_thm("max_one_element_lem",
      ``   (CARD X <= 1 ==> FINITE X ==> r <> q ==> r IN X ==> q IN X ==> F)
        /\ (r IN X ==> q IN X ==> CARD X <= 1 ==> FINITE X ==> (r = q))``,

      
   Tactical.REVERSE (Cases_on `FINITE X /\ CARD X <= 1`) THEN1 (
      FULL_SIMP_TAC std_ss []  
   ) THEN
   `?opt. X = OPTION_TO_SET opt` by PROVE_TAC[CARD_LEQ_1_OPTION_TO_SET] THEN
   ASM_SIMP_TAC (srw_ss()) []);


val empty_or_singel_lem =
      store_thm("empty_or_singel_lem",
      ``!X. CARD X <= 1 ==> FINITE X ==> (X = EMPTY) \/ (X <> EMPTY /\ (CARD X = 1))``,

        REPEAT STRIP_TAC THEN
        `?opt. X = OPTION_TO_SET opt` by PROVE_TAC[CARD_LEQ_1_OPTION_TO_SET] THEN
        ASM_SIMP_TAC (srw_ss()) [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]);


val min_set_in_set_lem = 
    store_thm("min_set_in_set_lem",
    ``!X. (?z. z IN X) ==> MIN_SET X IN X``,
     METIS_TAC [pred_setTheory.MIN_SET_DEF, whileTheory.LEAST_INTRO, boolTheory.IN_DEF]);

val singleton_not_empty_lem =
    store_thm("singleton_not_empty_lem",
    ``!X. (CARD X = 1) ==> (X <> EMPTY)``,
    `1 <> 0` by DECIDE_TAC THEN
    METIS_TAC [CARD_EMPTY]);


val empty_intersect_lem = 
    store_thm("empty_intersect_lem",
    ``(A INTER B = EMPTY) = (!x. ~ (x IN A /\ x IN B))``,
       SIMP_TAC std_ss [pred_setTheory.EXTENSION, pred_setTheory.IN_INTER, pred_setTheory.NOT_IN_EMPTY]);

(* This proof mixes up set and function worlds and is therefore too complicated 
          RW_TAC ((srw_ss())) [pred_setTheory.INTER_DEF, pred_setTheory.GSPEC_ETA, ETA_AX]
     THEN METIS_TAC [pred_setTheory.MEMBER_NOT_EMPTY, boolTheory.IN_DEF]);
*)

(* Again trouble with definition of CARD s *)
val delete_only_element_lem =
  store_thm ("delete_only_element_lem",
 ``(CARD s <= 1 ==> FINITE s ==> x IN s ==> P1 x ==> (s DIFF {x | P1 x} = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> P2 (x, y) ==> (s DIFF {x | P2 (x,y)} = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> P3 (y, x) ==> (s DIFF {x | P3 (y,x)} = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> P4 (x, f x) ==> (s DIFF {x | P4 (x,f x)} = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> P4'(x, f' x y) ==> (s DIFF {x | P4' (x,f' x y)} = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> P4''(x, f'' x y z) ==> (s DIFF {x | P4'' (x,f'' x y z)} = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> (s DELETE x = EMPTY)) /\
   (CARD s <= 1 ==> FINITE s ==> x IN s ==> (s DIFF {x} = EMPTY))``,

  Cases_on `CARD s <= 1` THEN ASM_REWRITE_TAC[] THEN
  Cases_on `FINITE s` THEN ASM_REWRITE_TAC[] THEN
  Cases_on `x IN s` THEN ASM_REWRITE_TAC[] THEN
  `s = OPTION_TO_SET (SOME x)` by PROVE_TAC[CARD_LEQ_1_IMPLIES_OPTION_TO_SET, IN_OPTION_TO_SET] THEN
  FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  PROVE_TAC[]);

val NOT_IN_DIFF_SING = store_thm("NOT_IN_DIFF_SING", ``
!A x. x NOTIN A DIFF {x}
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, pred_setTheory.IN_SING]
);

val DISJOINT_MEMBER_NOT_EQUAL = store_thm("DISJOINT_MEMBER_NOT_EQUAL", ``
!a b A B. DISJOINT A B /\ a IN A /\ b IN B ==> a <> b
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.DISJOINT_DEF, pred_setTheory.INTER_DEF,
		        pred_setTheory.EMPTY_DEF, pred_setTheory.GSPEC_ETA] >>
  METIS_TAC []
); 

val not_empty_CARD_lem = store_thm("not_empty_CARD_lem", ``
!s. FINITE s ==> s <> EMPTY ==> CARD s > 0
``,
  REPEAT STRIP_TAC >>
  `CARD s <> 0` suffices_by ( DECIDE_TAC ) >>
  METIS_TAC [pred_setTheory.CARD_EQ_0]
);

val IN_INTER_SING_lem = store_thm("IN_INTER_SING_lem", ``
!s x. x IN s ==> (s INTER {x} = {x})
``,
  REPEAT STRIP_TAC >>
  RW_TAC std_ss [pred_setTheory.EXTENSION] >>
  RW_TAC std_ss [pred_setTheory.IN_INTER, 
		 pred_setTheory.IN_SING] >>
  METIS_TAC []
);

(************** words ********************)



val all16cases = Theory.save_thm("all16cases",
  blastLib.BBLAST_PROVE
    ``(n = 0w) \/ (n = 1w) \/ (n = 2w) \/ (n = 3w) \/
      (n = 4w) \/ (n = 5w) \/ (n = 6w) \/ (n = 7w) \/ (n = 8w) \/
      (n = 9w) \/ (n = 10w) \/ (n = 11w) \/ (n = 12w) \/ (n = 13w) \/
      (n = (14w:word4)) \/ (n = 15w)``);


val none_of_16_cases = store_thm("none_of_16_cases",
    ``~ ((n <> 0w) /\ (n <> 1w) /\ (n <> 2w) /\ (n <> 3w) /\
      (n <> 4w) /\ (n <> 5w) /\ (n <> 6w) /\ (n <> 7w) /\ (n <> 8w) /\
      (n <> 9w) /\ (n <> 10w) /\ (n <> 11w) /\ (n <> 12w) /\ (n <> 13w) /\
      (n <> (14w:word4)) /\ (n <> 15w))``, METIS_TAC[all16cases]);


val PAdr_extract_lem = store_thm("PAdr_extract_lem", ``
!pa:bool[36] bx:bool[12].
(47><12) ((pa @@ bx):bool[48]) = pa
``,
  REPEAT GEN_TAC THEN				 
  STRIP_ASSUME_TAC (wordsTheory.EXTRACT_CONCAT |> ISPECL [``pa:bool[36]``, ``bx:bool[12]``] |> INST_TYPE [gamma |-> ``:48``, alpha |-> ``:48``] |> SIMP_RULE (srw_ss()++WORD_ss) [])
);


val bx_extract_lem = store_thm("bx_extract_lem", ``
!pa:bool[36] bx:bool[12].
(11><0) ((pa @@ bx):bool[48]) = bx
``,
  REPEAT GEN_TAC THEN				 
  STRIP_ASSUME_TAC (wordsTheory.EXTRACT_CONCAT |> ISPECL [``pa:bool[36]``, ``bx:bool[12]``] |> INST_TYPE [gamma |-> ``:48``, alpha |-> ``:48``] |> SIMP_RULE (srw_ss()++WORD_ss) [])
);

val full_extract_lem = store_thm("full_extract_lem", ``
!a:bool[48]. (47><0)a = a
``,
  REPEAT GEN_TAC THEN	
  MATCH_MP_TAC wordsTheory.WORD_EXTRACT_ID THEN
  Cases_on `a` THEN
  FULL_SIMP_TAC (arith_ss++WORD_ss) [wordsTheory.w2n_n2w]
);

val PAdr_bx_concat_lem = store_thm("PAdr_bx_concat_lem", ``
!a:bool[48].
a = ((47><12) a :bool[36]) @@ ((11><0) a :bool[12])
``,
  REPEAT GEN_TAC THEN				 
  ASSUME_TAC (wordsTheory.CONCAT_EXTRACT |> ISPECL [``47``, ``11``, ``0``, ``a:bool[48]``] |> INST_TYPE [beta |-> ``:36``, gamma |-> ``:12``, delta |-> ``:48``] |> SIMP_RULE (std_ss++ARITH_ss++WORD_ss) []) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  RW_TAC (srw_ss()) [full_extract_lem]
);

val concat_eq_lem = store_thm("concat_eq_lem", ``
!a:bool[36] b:bool[12] x:bool[36] y:bool[12].
((a @@ b):bool[48] = (x @@ y):bool[48]) <=> ((a=x) /\ (b=y))
``,
  REPEAT GEN_TAC THEN
  EQ_TAC 
  THEN1 (
      RW_TAC (srw_ss()++WORD_ss) [] 
      THENL[(* case: a = x *)
            `(47 >< 12) ((a @@ b):bool[48]) = a` by (
	        RW_TAC (srw_ss()) [PAdr_extract_lem] ) THEN 
            `(47 >< 12) ((x @@ y):bool[48]) = x` by (
	        RW_TAC (srw_ss()) [PAdr_extract_lem] ) THEN 
	    REV_FULL_SIMP_TAC (srw_ss()) [],
	    (* case: b = y *)
	    `(11 >< 0) ((a @@ b):bool[48]) = b` by (
	        RW_TAC (srw_ss()) [bx_extract_lem] ) THEN 
            `(11 >< 0) ((x @@ y):bool[48]) = y` by (
	        RW_TAC (srw_ss()) [bx_extract_lem] ) THEN 
	    REV_FULL_SIMP_TAC (srw_ss()) []
	   ]
  ) THEN 
  RW_TAC (srw_ss()) []
);

val concat_eq_lem_3711 = save_thm("concat_eq_lem_3711", 
blastLib.BBLAST_PROVE ``
!a:bool[36] b:bool[12] x:bool[36] y:bool[12].
((a @@ b):bool[48] = (x @@ y):bool[48]) <=> ((a=x) /\ (b=y))
``);

val still_different_after_add_lem = save_thm (
   "still_different_after_add_lem", blastLib.BBLAST_PROVE ``
   ((((47><11) (a:bool[64])):bool[37]) <> (((47><11) (b:bool[64])):bool[37]))
   ==> (((10 >< 0) b = 0w:bool[11]))
   ==>   ((a:bool[64]) <> ((b:bool[64]) + 0x400w))
      /\ ((a:bool[64]) <> ((b:bool[64]) + 0x480w))``);

val different_after_add_lem = save_thm (
   "different_after_add_lem", blastLib.BBLAST_PROVE ``
      ((a:word64) <> a + 0x400w)
   /\ (a <> a + 0x480w)``);

val compare_13_lsb = save_thm ("compare_13_lsb", 
blastLib.BBLAST_PROVE ``
    (((12><0)(a:word48)):bool[13] = ((12><0)(b:word48)):bool[13])
       <=>
    (((47><12)(a:word48)):bool[36] ' 0 = ((47><12)(b:word48)):bool[36] ' 0)
 /\ (((11><0)(a:word48)):bool[12] = ((11><0)(b:word48)):bool[12])
``);



(*************** finish ****************)

val _ = export_theory();




