signature tacticsLib =
sig
    val SIMP_TERM : simpLib.simpset -> Abbrev.thm list -> Abbrev.term -> Abbrev.term
    val UNDISCH_MATCH_TAC : Abbrev.term -> Abbrev.tactic
    val UNDISCH_ALL_TAC  : Abbrev.tactic
    val SPEC_ASSUM_TAC  : Abbrev.term * Abbrev.term list -> Abbrev.tactic
    val SPEC_AND_KEEP_ASSUM_TAC : Abbrev.term * Abbrev.term list -> Abbrev.tactic
    val THROW_AWAY_TAC  : Abbrev.term -> Abbrev.tactic
    val THROW_ONE_AWAY_TAC  : Abbrev.term -> Abbrev.tactic
    val THROW_AWAY_IMPLICATIONS_TAC  : Abbrev.tactic
    val ASSERT_ASSUM_TAC  : Abbrev.term -> Abbrev.tactic
    val PROTECTED_RW_TAC  : Abbrev.term -> Abbrev.tactic
    val PROTECTED_OR_RW_TAC  : Abbrev.thm list -> Abbrev.tactic
    val PROTECTED_OR_SIMP_TAC  : Abbrev.thm list -> Abbrev.tactic
    val CONJ_ASSUM_TAC  : Abbrev.tactic
    val FORCE_REWRITE_TAC  : Abbrev.thm -> Abbrev.tactic
    val FORCE_REV_REWRITE_TAC  : Abbrev.thm -> Abbrev.tactic
    val ASSUME_SPECL_TAC  : Abbrev.term list -> Abbrev.thm -> Abbrev.tactic
    val ASSUME_SIMP_TAC  : Abbrev.thm list -> Abbrev.thm -> Abbrev.tactic
    val IMP_RES_SIMP_TAC  : Abbrev.thm list -> Abbrev.thm -> Abbrev.tactic
    val ASSUME_SPEC_TAC  : Thm.term -> Thm.thm -> Abbrev.tactic
    val ASSUME_SPECL_SIMP_TAC 
	: Abbrev.term list -> Abbrev.thm list -> Abbrev.thm -> Abbrev.tactic
    val IMP_RES_SPEC_TAC  : Thm.term -> Thm.thm -> Abbrev.tactic
    val IMP_RES_SPECL_TAC  : Abbrev.term list -> Abbrev.thm -> Abbrev.tactic
    val MP_SPEC_TAC  : Thm.term -> Thm.thm -> Abbrev.tactic
    val MP_SPECL_TAC  : Abbrev.term list -> Abbrev.thm -> Abbrev.tactic
    val ASSUME_SPECL_GEN_REWRITE_TAC 
	: Abbrev.term list * Abbrev.thm * Abbrev.thm list -> Abbrev.tactic
    val ASSUME_SPECL_INST_TAC 
	:
	Abbrev.term list ->
	(Thm.hol_type, Thm.hol_type) Lib.subst -> Thm.thm -> Abbrev.tactic   
    val REDUCE_SIMP :  ('a -> ''b list * ('c list -> 'd)) -> 'a -> ''b list * ('c list -> 'd)
    val equal_goals : ''a list * ''b -> ''a list * ''b -> bool
    val remove_redundancy_gls : (''a list * ''b) list -> (''a list * ''b) list
    val pump_list_gls : 'a list -> (''b list * ''c) list -> (''b list * ''c) list -> 'a list
    val REDUCE :  ('a -> (''b list * ''c) list * ('d list -> 'e)) -> 'a -> (''b list * ''c) list * ('d list -> 'e)
    val emptyt : 'a -> 'b list -> 'a
    val compose_validation : (Abbrev.goal list * (Thm.thm list -> Thm.thm)) list -> Thm.thm list -> Thm.thm list
    val DEPTH_TAC : int -> Abbrev.goal -> Abbrev.goal list * Abbrev.validation
    val DEPTH_LIST : (Abbrev.goal -> Abbrev.goal list * (Thm.thm list -> Thm.thm)) list -> Abbrev.goal -> Abbrev.goal list * Abbrev.validation
    val DEPTH_FIRST : (Abbrev.goal -> Abbrev.goal list * (Thm.thm list -> Thm.thm)) list -> Abbrev.goal -> Abbrev.goal list * Abbrev.validation
    val FST_AND_SND_TAC : Abbrev.tactic
    val FST_AND_SND_CONV: Abbrev.conv
    val fst_and_snd_flat_lem : Thm.thm
    val pair_fst_and_snd_flat_lem : Thm.thm
    val FST_AND_SND_FLAT_CONV : Abbrev.conv
    val FST_AND_SND_FLAT_CONV2 : Abbrev.conv
    val FST_AND_SND_STRICT_CONV : Abbrev.conv
    val FST_AND_SND_STRICT_CONV2 : Abbrev.conv
    val FST_AND_SND_ON_VARS_CONV : Abbrev.conv
    val FST_AND_SND_ON_CASE_VARS_CONV : Abbrev.conv
    val FST_AND_SND_RULE : Thm.thm -> Thm.thm
    val ALPHA_CHANGED_TAC : Abbrev.tactic -> Abbrev.tactic
    val term_by : Thm.term -> Abbrev.tactic -> Abbrev.tactic
    val LIMITED_METIS_TAC : int -> Thm.thm list -> metisTools.tactic
    val TIME_LIMITED_METIS_TAC : real -> Thm.thm list -> metisTools.tactic
    val INFS_LIMITED_METIS_TAC : int -> Thm.thm list -> metisTools.tactic
    val THROW_NO_TAC : int -> Abbrev.tactic
    val PRINT_TAC : string -> Abbrev.tactic
    val EXCEPT_FOR : Thm.term -> Abbrev.tactic -> Abbrev.tactic
    val EXCEPT_FOR_THESE : Thm.term list -> Abbrev.tactic -> Abbrev.tactic
    val ONLY_FOR : Thm.term -> Abbrev.tactic -> Abbrev.tactic
    val ONLY_FOR_THESE : Thm.term list -> Abbrev.tactic -> Abbrev.tactic
    val is_step_predicate : Thm.term -> bool
    val FIND_STEP_PREDICATES_TAC : Thm.thm list -> (Thm.thm -> Abbrev.tactic) -> Abbrev.tactic
    val STEP_PREDICATE_FIRST_RULE : Thm.thm -> Thm.thm
    val FEED_EXISTS_TAC : Abbrev.tactic
    val REORDER_EXISTS_TAC : Thm.term -> Abbrev.tactic
    val TYPE_REORDER_EXISTS_TAC :  Abbrev.hol_type -> Abbrev.tactic
    val TYPE_REORDER_EXISTS_OR_FAIL_TAC :  Abbrev.hol_type -> Abbrev.tactic
    val FIRST_EXISTS_TAC :  Thm.term -> Abbrev.tactic
    val SPLIT_EXIST_CONV : Abbrev.conv
    val SPLIT_EXIST_TAC : Abbrev.tactic
    val SPLIT_EXIST_TAC2 : Abbrev.tactic
    val SPLIT_EXIST_TAC3 : Abbrev.tactic
    val SPLIT_EXIST_TAC4 : Abbrev.tactic
    val SPLIT_EXIST_TAC5 : Abbrev.tactic
    val SPLIT_EXIST_TAC6 : Abbrev.tactic
    val PAT_X_ASSUM : Abbrev.term -> (Thm.thm -> Abbrev.tactic) -> Abbrev.tactic
end
