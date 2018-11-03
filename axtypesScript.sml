(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open tacticsLib; 

val _ = new_theory "axtypes";

(***************** Type Names ******************)

(* uninstantiated components of the ideal and refined model,
   these are placeholders for actual component models and there types *)


(******************** BOTH MODELS ************************)

(* internal state to abstract unmodeled components *)
val _ = new_type("core_internal_state", 0);

(* memory and peripheral states,
   one type fits all for peripherals, e.g., via sum type *)
val _ = new_type("memory", 0);
val _ = new_type("peripheral",0);

(* peripheral I/O event type, e.g., incoming network package *)
val _ = new_type("pevent",0);

(*  aux info for message, memory type, cacheability, serial number, etc *)
val _ = new_type("msginfo",0);

(*  aux info for memory/MMU fault replies *)
val _ = new_type("fault_info",0);

(* Type of register names general purpose registers *)
val _ = new_type("GPRguest",0);
(* special purpose registers in ARMv8 *)
val _ = new_type("SPRguest",0);


(******************** IDEAL MODEL ************************)

(* idgic: ideal gic state, 
   idcore: ideal core state, reduced to guest accessible functionality,
           special semantics for some hypercalls *)
val _ = new_type("idgic", 0);
val _ = new_type("idcore", 0);


(******************** REFINED MODEL **********************)

(* types for refined core state, second stage MMU, and GIC,
   memory and peripheral states same in ideal / refined model *)
val _ = new_type("refcore", 0);
val _ = new_type("mmu", 0);
val _ = new_type("gic", 0);

(* general and special purpose registers for use of the hypervisor, 
   these are not accessible by the guest, i.e., in EL2/EL3 only *)
val _ = new_type("GPRhyp",0);
val _ = new_type("SPRhyp",0);

(* special purpose registers for MMU *)
val _ = new_type("MMUcfg",0);

(* GIC cpu memory mapped interface registers,
   Same used at ideal and refined level *)
(* NOTE: GICCreg does not cover volatile read only and write-only registers
   e.g., GICC_IAR, GICC_HPPIR, etc : 
   when reading those their value is computed
   on the fly from the distributor state *) 
val _ = new_type("GICCreg",0); 

(* distributor registers, volatile case, 
   the value of these registers depends on the interrupt state, 
   hence they cannot be fixed by writing to them,
   similarly write registers only with side effects fall in this category *)
val _ = new_type("GICDregvol",0);

(* mutable GICD registers, these behave like normal SPRs *)
val _ = new_type("GICDregmute",0);

(* constant, i.e., read-only and non-volatile, 
   their value can be cached / emulated by the hypervisor 
   to avoid accessing the GIC *)
val _ = new_type("GICDregconst",0);

(* virtual interrupt controller interface registers*)
val _ = new_type("GICHreg",0);

(*************** finish ***********)

val _ = export_theory();
