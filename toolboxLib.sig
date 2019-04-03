signature toolboxLib =
sig
  (* match and find *)
  val is_match : Abbrev.term -> Abbrev.term -> bool
  val is_type_match : Abbrev.hol_type -> Abbrev.hol_type -> bool
  val find_term_opt : (Abbrev.term -> bool) -> Abbrev.term -> Abbrev.term option
  val there_is_some : Abbrev.term -> Abbrev.term -> bool
  val is_underscore : Abbrev.term -> bool
  val is_underscore_redex : {redex: Term.term, residue: Term.term} -> bool
  val consistent_on :  Term.term -> (Term.term, Term.term) Term.subst -> (Term.term, Term.term) Term.subst -> bool
  val match_and_learn : (Term.term list * Term.term list) list -> (Term.term, Term.term) Term.subst  
  (* list operations *)
  val mapX : ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
  val foldX : ('a * 'b * 'c -> 'c) -> 'a list * 'b list -> 'c -> 'c 
  val remove_redundancy_simp : ''a list -> ''a list
  val remove_redundancy_by_eq : ('a -> 'a -> bool) -> 'a list -> 'a list
  val pump_list_simp : 'a list -> ''b list -> ''b list -> 'a list
  val is_contained : ''a list -> ''a list -> bool
  val compare_lists : ''a list -> ''a list -> bool
  val map_until : ('a -> 'b) -> ('a -> 'b) -> ('b -> bool) -> 'a list -> 'b list
  (* generating theorems for types *)  
  val fall_constructors_thm_of : Abbrev.hol_type -> Abbrev.thm   
end
