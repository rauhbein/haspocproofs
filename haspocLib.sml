structure haspocLib =
struct

open HolKernel boolLib bossLib;

open toolboxLib;
open tacticsLib;
open annotationsLib; infix //; infix ///; infix -:;

open haspoctypesTheory;



(* substitutes theorem parts of the form
   "there is a matching request satisfying ..." with
   "the request of that reply satisfies ..." *)
val UNIQUE_REQ = (SIMP_RULE bool_ss [unique_req_lem]) o (SIMP_RULE pure_ss [unique_req_lem]);
val UNIQUE_REQ_TAC = SIMP_TAC bool_ss [unique_req_lem];


end



