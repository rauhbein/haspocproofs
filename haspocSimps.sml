structure haspocSimps :> haspocSimps =
struct

open HolKernel boolLib simpLib
open haspoctypesTheory
open parametersTheory
open hypervisorTheory

val HASPOC_SS = rewrites [obvious_req_rep_attributes_lem, obvious_matches_lem, obvious_mismatches_lem, MsgOf_rewrites,
                          obviously_not_in_IPIRQ_lem, projections_inequal_lem];


end