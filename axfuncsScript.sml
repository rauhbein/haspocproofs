(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 


open math_lemmasTheory;
open axtypesTheory;
open haspoctypesTheory;
open parametersTheory;
open tacticsLib; 
open annotationsLib; infix //; infix ///; infix -:;

open haspocLib;

val _ = new_theory "axfuncs";

(* Here we define the abstract specifications for the components of the ideal
   and refined model. 

   For simplicity, all assumptions are introduced as axioms. These axioms should
   be replaced by theorems on a given instantiation. In order to increase the
   trust in the proofs the axiomatic definitions can be replaced by
   specification functions, similar to the parameters of the model.
*)

(******************** HELPER FUNCTIONS******************)


(* allocation of IRQ IDs to the List registers in the 
   GIC virtualization interface, as mapped by hypervisor for all guests 

   The GIC offers 64 list registers to inject virtual interrupts into the guest,
   therefore up to 64 interrupts can be configured per core. In the hypervisor
   design we fix the allocation of these registers for the IRQs that belong to a
   certain guest. Note that IRQs are never shared between guests and each core
   has their own copy of list registers, therefore the same list register can be
   allocated for different IRQs on cores of different guests. However no IRQ is
   ever allocated to different list registers or to list registers for cores of
   guests that do not own the interrupt.

   The simplified allocation avoids dynamic resource management of the list
   registers at the cost of limiting the number of virtual interrupts per guest
   to 64.
*)
new_constant("gich_lr", ``:irqID -> GICHreg``);


(* different irqs from same guest map to different LRs,
   except SGIs for different cores 

   Conversely disj_lr_irq q q' g does not hold, if:
   - q = q'
   - q and q' are interrupts that do not belong to the same guest
   - q and q' are SGIs that target different cores 

   In these cases q and q' can be mapped to the same list register on cores of 
   different guests (or even different cores of the same guest in the SGI case)
*)
val disj_lr_irq_def = Define `disj_lr_irq(q,q',g) = 
case (q,q') of
  | (PIR m, PIR n) => q IN xPIRQ g /\ q' IN xPIRQ g /\ m<>n
  | (SGI x, PIR n) => q IN IPIRQ g /\ q' IN xPIRQ g
  | (PIR n, SGI x) => q IN xPIRQ g /\ q' IN IPIRQ g
  | (SGI (id,c,c'), SGI (id',d,d')) => q IN IPIRQ g /\ q' IN IPIRQ g   
				    /\ (c' = d') /\ (id <> id' \/ c <> d)
`;


(* Axiom: interrupts that must be mapped to different LRs
          are actually mapped to different LRs *)
val gich_lr_ax = new_axiom("gich_lr_ax", ``
!q q' g. disj_lr_irq(q,q',g) ==> gich_lr q <> gich_lr q'
``);

(* uninterpreted initial state for the GIC *)
new_constant("GICCinit", ``:GICCreg -> bool[32]``);
new_constant("GICDinit", ``:GICDreg -> bool[32]``);
new_constant("GICHinit", ``:GICHreg -> bool[32]``);
new_constant("GICVinit", ``:GICCreg -> bool[32]``);

(* uninterpreted set of "golden" GIC distributor configurations that implement
   IRQ isolation between different guests using the distributor mask bits
   gm = "golden mask"
*) 
new_constant("gic_gm_conf",
   ``:(GICDreg -> bool[32]) set``);


(* Axiom: initial configuration of GIC distributor is secure, e.g., 
          by disabling all IRQ forwarding 

   This assumption is reasonable, because no interrupt handlers are installed
   after boot (besides for reset), hence interrupt signaling should be disabled
   until enabled explicitly by the system software. Even if the GIC distributor
   is not disabled initially, interrupts are only triggered if the core's IRQ
   mask register is cleared, i.e., when the hypervisor launches the guest.
   
   In the latter case the initialization would have to model the GIC
   initialization, which we omit here for simplicity, assuming that the GIC
   starts in a secure configuration.
*)
val gm_conf_init_ax = new_axiom("gm_conf_init_ax", ``
(\r. GICDinit r) IN gic_gm_conf
``);

(* uninterpreted constraints on GICC configuration

   in practice (i.e., our hypervisor) these are:
   - enable only non-secure interrupts
   - use AIAR register
   - EOIModeNS = 1
   - priority mask allows all interrupts to be signalled

   since we do not model these details of the interrupt controller, they have to
   added for a suitable instantiation of the model
 *)
new_constant("inv_gicc", ``:(GICCreg -> bool[32]) -> bool``);

(* Axiom: again we assume here that the constraints holds initially *)
val gicc_init_ax = new_axiom("gicc_init_ax", ``
inv_gicc GICCinit 
``);

(* Axiom: all lrs empty initially, therefore no virtual interupts are pending *)
val gich_init_ax = new_axiom("gich_init_ax", ``
!q. GICHinit (gich_lr q) = 0w
``);


(* non-supported memory operations on GICD

   As mentioned in the discussion of the internal core states, not all memory
   operations on the GICD are supported to be virtualized by the hypervisor.
   
   The below definition defines all cases of the exception syndrome register for
   which emulation of a GICD memory access fails, as the negation of all
   supported cases.    
*) 
val iss_gicd_not_supported_def = Define `iss_gicd_not_supported(iss:bool[32]) = 
~( (iss ' 28) (* data abort, assuming iss is data / instruction memory abort *)
   /\ (iss ' 24) (* ISS syndrome field is valid *)
   /\ ((22><21)iss = 0b00w:bool[2]) (* allow byte or word accesses, 
				       no sign extension of data *) 
   /\ (iss ' 15) (* 64bit register access *)
   /\ ~(iss ' 14) (* no acquire release semantics *)
   /\ ((8><7)iss = 0w:bool[2]) (* no cache management instruction,
				  not a stage 2 fault for state 1 page table *)
   /\ ((5><2)iss = 0b0001w:bool[4]) ) (* Translation fault *)
`;


(* Golden Image MMU abstraction

   set of page tables that implement the desired memory isolation, we leave the
   details of the page table layout undefined here and assume that the
   hypervisor sets up page tables with the desired properties. This assumption
   has to be discharged for a given MMU model and the hypervisor implementation.

   The page tables and desired translation are specified by 5 parameters:

   golden (GI, cfg, PT, RO, tr) 

   GI - "golden image" of the page tables, 
        represented as a page addressable memory
   cfg - the configuration of the MMU registers, determining, e.g., where the
         top-level page table is located
   PT - the set of pages used for translation, 
        all other pages in GI can be ignored
   RO - the set of input addresses that need to be read-only, 
        this will only be used for our uni-directional IGC channels in memory
   tr - the desired translation function implemented by the page tables:
        tr a = SOME b - page a is mapped to page b
	tr a = NONE - page a is unmapped
        We deliberately do not encode access permissions here, as in our design
        (except for IGC memory) accesses to guest memory are unrestricted.
   
   Thus the set can be interpreted as a predicate saying: "a page table
   structure set up according to parameters GI, cfg, PT, and RO implements a
   translation according to function tr.

   We will later further restrict the behaviour of the MMU if it is configured
   according to a "golden" page table image.
 *)
new_constant("golden", ``:((bool[36] -> PAGE) # 
			   MMUcfg # 
			   (bool[36] set) # 
			   (bool[36] set) # 
			   (bool[36] -> (bool[36] option))) set``);

(* Axiom: a golden page table configuration guarantees at least:
   - all read only regions are mapped
   - no addresses are mapped into the page table region
*)
val golden_axiom = new_axiom("golden_axiom", ``
!GI cfg PT RO tr a. 
golden (GI, cfg, PT, RO, tr) ==>
   (a IN RO ==> IS_SOME (tr a))
/\ (IS_SOME (tr a) ==> (THE (tr a)) NOTIN PT)
``);


(* Golden fault information 

   golden_fi (GI, cfg, PT, RO) r

   returns the fault information produced by a page table configured according
   to a "golden image" with parameters GI, cfg, PT, RO for request r.

   The output is irrelevant if no fault is produced for r.
*)
new_constant("golden_fi", ``:((bool[36] -> PAGE) # 
			      MMUcfg # 
			      (bool[36] set) # 
			      (bool[36] set)) -> request -> fault_info``);


(* guest handler offsets for synchronous faults 

   this offset into the interrupt vector table is used when handling a synconous
   fault. It depends on the PSTATE value and routes to different handlers
   depending on the mode in which the fault occurred and the configuration of
   which stack pointer was used by the interrupted code.

   the handlers are residing in the hypervisor and are used to catch guest
   access violations, hypercalls, and to emulate the GIC distributor
*)
val ghoff_def = Define `
ghoff (d:bool[64]) = 
if word_bit 2 d then 
    if word_bit 0 d then 0x200w:bool[64]
    else 0x000w:bool[64]
else 0x400w:bool[64]
`;

(* guest handler offsets for asynchronous faults

   again the interrupt handler that is chosen for the fault depends on the value
   of the PSTATE register.

   asynchronous faults are usually peripheral or inter-processor interrupts and
   must be injected by the hypervisor into the guest.
 *)
val async_ghoff_def = Define `
async_ghoff (d:bool[64]) = 
if word_bit 2 d then 
    if word_bit 0 d then 0x280w:bool[64]
    else 0x080w:bool[64]
else 0x480w:bool[64]
`;

(* dmsk (GICD,GICC,c) 

   returns set of masked interrupts combining distributor enabling, target, and
   gicc priority mask, for a given GICD state and the GICC state of core c
 
   This function abstracts from the different mechanisms in the GIC that allow
   to enable or disable forwarding of interrupts to a certain core. If an
   interrupt is in the set it is considered disabled.
*)
new_constant("dmsk", ``:(GICDreg -> bool[32]) # 
			(GICCreg -> bool[32]) # 
			num -> 
		        (irqID set)``);

(* idmsk GICD c

   ideal distributor mask, according enabling and targeting information in the
   distriutor registers for core c

   we use a different function for determining the masked interrupts in the
   ideal GIC distributor because interrupt distributing is modeled in a
   different way in the GIC. In particular, interrupts are not directly
   forwarded to the cores by the distributor but there is an intermediate core
   interrupt state (Q) which represents the interrupts virtualized by the
   hypervisor.
*)
new_constant("idmsk", ``:(GICDreg -> bool[32]) # num -> (irqID set)``);

(* vmsk: GICV priority mask, configured by the guest via the virtual interrupt
         interface

   for simplicity we do not model the interrupt priority mask directly but just
   record whether an interrupt is enabled or disabled by the priority mask, as
   the hypervisor sets up fixed priorities for the interrupts.
*)
new_constant("vmsk", ``:(GICCreg -> bool[32]) -> (irqID set)``);

(* ideal priority mask, configured by guest 

   this is identical to the vmsk definition
*)
val ipmsk_def = Define `ipmsk gicc = vmsk gicc`;

(* former axiom: identity of vmsk and ipmsk *) 
val vmsk_ipmsk_axiom = store_thm("vmsk_ipmsk_axiom", ``
!gicc. vmsk gicc = ipmsk gicc
``,
  RW_TAC std_ss [ipmsk_def]
);

(* Axiom: the vmsk does not distinguish SGIs with the same ID but different
sources or targets *)
val vmsk_SGI_axiom = new_axiom("vmsk_SGI_axiom", ``
!gicc id a b c d. 
SGI (id,a,b) IN vmsk gicc <=> SGI (id,c,d) IN vmsk gicc
``);

(* similarly for ipmsk *)
val ipmsk_SGI_axiom = store_thm("ipmsk_SGI_axiom", ``
!gicc id a b c d. 
SGI (id,a,b) IN ipmsk gicc <=> SGI (id,c,d) IN ipmsk gicc
``,
  RW_TAC std_ss [GSYM vmsk_ipmsk_axiom, vmsk_SGI_axiom]
);

(* the fixed interrupt priorities set up by the hypervisor *)
val _ = new_constant("prio", ``:irqID -> bool[5]``);
(* the fixed IGC interrupt priority set up by the hypervisor *)
val _ = new_constant("prioIGC", ``:bool[5]``);

(* Axiom: SGI interrupts with the same ID have the same priority *)
val prio_SGI_axiom = new_axiom("prio_SGI_axiom", ``
!id a b c d. prio (SGI (id, a, b)) = prio (SGI (id, c, d))
``);

(* ready_irqs IS msk

   the set of interrupts that are ready to be signaled to a core according to
   interrupt state IS and interrupt mask msk
*)
val ready_irqs_def = Define `
ready_irqs (IS : irqID -> IRQstate , msk : irqID set) = 
{q | (IS q = PENDING) /\ q NOTIN msk}
`;

(* max_prio S
   
   the interrupt with maximum priority in a set of interrupts S.

   as usual, IRQ priority values are decreasing with increasing priority *)
val max_prio_def = Define `max_prio (S : irqID set) = 
MIN_SET { w2n(prio q) | q IN S}
`;

(* lr2virq (v,c)

   decodes the interrupt stored in the list register with value v in the GICH
   interface of core c, as configured by the hypervisor

   this reflects the format of list registers in the ARM GICv2 spec
*)
val lr2virq_def = Define `lr2virq (v : bool[32], c:num) = 
if (9><0) v:bool[10] <=+ 15w 
then SGI ((3><0) v, w2n((12><10)v :bool[3]), c) 
else PIR (w2n ((9><0) v:bool[10]))
`;

(* virqlrs (gich, vq, c) 

   the set of interrupts mapping to virtual interrupt vq in the LRs of virtual
   interrupt control interface gich for core c.

   As the hypervisor has dedicated list registers for each virtual interrupt of
   a guest, this set contains at most one interrupt and if it does, the virtual
   interrupt is identical to q, unless it is an SGI interrupt where the senders
   may differ.
*)
val virqlrs_def = Define `virqlrs (gich: GICHreg -> bool[32], vq, c:num) = 
{q | (gich (gich_lr q)) ' 30 /\ (vq = lr2virq(gich (gich_lr q), c))}	 
`;

(* decoding GICD register from byte offset into GICD page *)
val _ = new_constant("decgicd", ``:bool[12] -> GICDreg option``);
(* address of the GICD_SGIR register, used to request SGI interrupts *)
val _ = new_constant("Agicd_sgir", ``:bool[48]``);

(* GICD register update function:
    
   GICDupd (R,x,y) = z

   writing y to register R that has previously value x results in value z.

   Most GIC registers do not have a normal memory semantics, in that they assume
   the values they are written with. Instead they are often written with masks
   that flip certain bits but leave others unchanged, thus interrupts can be
   configured without having to read out the value x first.

   Function GICDupd encodes the update behaviour for each register R of the GICD
*)
new_constant("GICDupd", ``:GICDreg # bool[32] # bool[32] -> bool[32]``);

(* ideal GICD register update function for guest g 
   
   idGICDupd g is similar to GICDupd, only that it takes into account which
   configurations of the GICD are allowed for guest g. Thus it encodes the
   update behaviour of register R in the GICD as emulated by the hypervisor for
   that particular guest. Then attempts to configure interrupts not belonging to
   g should have no effect. 
*)
new_constant("idGICDupd", 
	     ``:num -> GICDreg # bool[32] # bool[32] -> bool[32]``);

(* some generalization of ideal GICD updates, needed later,
   the idea here is that we can specify the a register changes its value but
   only according to what would be allowed by an explicit update via idGICDupd
*)

(* ideal GICD register reg updated from gicdreg to gicdreg', or unchanged *)
val someIdGICDupd_def = Define `
    someIdGICDupd g reg gicdreg gicdreg' =
        (gicdreg' = gicdreg)
     \/ (?v. gicdreg' = idGICDupd g (reg, gicdreg, v))`;

(* ideal GICD register reg updated from gicdreg to gicdreg' in n steps *)
val someIdGICDupd_n_def = Define `
       (someIdGICDupd_n g reg gicdreg gicdreg' 0 =  (gicdreg' = gicdreg))
    /\ (someIdGICDupd_n g reg gicdreg gicdreg' (SUC n) = 
        ?gicdreg_.   someIdGICDupd_n g reg gicdreg gicdreg_ n
                  /\ someIdGICDupd g reg gicdreg_ gicdreg')`;

(* Lemma: extend to n+1 steps by simply skipping update *)
val someIdGICDupd_more_lem = store_thm(
   "someIdGICDupd_more_lem",
    ``someIdGICDupd_n g reg gicdreg gicdreg' n ==> 
      someIdGICDupd_n g reg gicdreg gicdreg' (SUC n)``,
    STRIP_TAC >>
    PURE_ONCE_REWRITE_TAC [someIdGICDupd_n_def] >>
    Q.EXISTS_TAC `gicdreg'` >>
    ASM_SIMP_TAC std_ss [someIdGICDupd_def]);

(* generalization to arbitrary n *)
val someIdGICDupds_def = Define `
    someIdGICDupds g reg gicdreg gicdreg' = 
?n. someIdGICDupd_n g reg gicdreg gicdreg' n`;

(* Lemma: any update can be achieved by some number of updates *)
val someIdGICDupd_someIdGICDupds_lem = store_thm(
   "someIdGICDupd_someIdGICDupds_lem",
    ``someIdGICDupd g reg gicdreg gicdreg' ==> 
      someIdGICDupds g reg gicdreg gicdreg'``,
    REWRITE_TAC [someIdGICDupds_def] >>
    STRIP_TAC >>
    EXISTS_TAC ``SUC 0`` >>
    ASM_SIMP_TAC bool_ss [someIdGICDupd_n_def]);
    
(* Lemma: transitivity of ideal GICD updates *)
val someIdGICDupds_trans_lem = store_thm(
   "someIdGICDupds_trans_lem",
   ``someIdGICDupds g reg gicdreg gicdreg' /\ 
     someIdGICDupds g reg gicdreg' gicdreg''
       ==> someIdGICDupds g reg gicdreg gicdreg''``,
    REWRITE_TAC [someIdGICDupds_def] >>
    REPEAT STRIP_TAC >>
    EXISTS_TAC ``(n:num) + n'`` >>
    UNDISCH_ALL_TAC >>
    Q.SPEC_TAC (`gicdreg''`, `gicdreg''`) >>
    Induct_on `n'` >|
    [(* base case *)
     ASM_SIMP_TAC arith_ss [someIdGICDupd_n_def],
     (* induction step *)
     ASM_SIMP_TAC arith_ss [someIdGICDupd_n_def] >>
     `n + SUC n' = SUC (n + n')` by DECIDE_TAC >>
     ASM_SIMP_TAC bool_ss [] >>
     PURE_ONCE_REWRITE_TAC [someIdGICDupd_n_def] >>
     METIS_TAC []]);


(* abstract core internal state *)

(* mapping the interal state of the core to the abstract core internal state, 
   that determines whether GICD accesses can be emulated after memory faults 
*)
val _ = new_constant("cis_abs", ``:core_internal_state -> AbsCIstate``);
(* target or source register for memory operations, as stored in the core
   internal state after a faulting memory access, that can be emulated
*)
val _ = new_constant("ts_reg", ``:core_internal_state -> GPRguest``);

(* Axiom: there is a unique internal state (as represented by
core_internal_state type) corresponding to the abstract FLUSHED state, that
represents the internal state of the core before an exception is taken and
implies that no memory accesses are outstanding for the core.

Intuitively the FLUSHED state refers to the state were the core pipeline was
flushed due to an exception and all memory accesses have completed. This state
is restored when returning from an exception.
*)
val cis_abs_flushed_axiom = new_axiom("cis_abs_flushed_axiom", ``
!a b. (cis_abs a = FLUSHED) /\ (cis_abs b = FLUSHED) ==> (a = b)
``);

(* identify non-supported gicd accesses, 
   we assume that the message info contains the necessary informations *)
val _ = new_constant("gicd_acc_not_supported", ``:msginfo -> bool``);
(* the contents of the fault address register after receiving the given fault *)
val _ = new_constant("extract_FAR", ``:fault_info -> bool[64]``);
(* the contents of the exception syndrome register for the given request and
fault information as well as the internal core state *) 
val _ = new_constant("extract_ESR", 
        ``:core_internal_state # request # fault_info -> bool[32]``);
(* converting GPR indixes/numbers to register names *)
val _ = new_constant("gprX", ``:(num -> GPRguest)``);

(* semantics of ESR, depending on faulting request and fault info *)
val extract_ESR_axiom = new_annotated_axiom("extract_ESR_axiom",
``T``,
["general" -: 
 (* general properties guaranteed by ARMv8 spec *)
 ``!cis r fi esr. 
   (extract_ESR (cis,r,fi) = esr) 
   ==> 
   (* data or instruction fault *)
       ((31><29)esr = 0b100w:bool[3])
    /\ ((27><26)esr = 0b00w:bool[2])
    /\ (esr ' 24 ==>  
	(* caused by second stage translation fault or address size fault *)
	   ((5><3)esr = 0b000w:bool[3])
	(* size of access is 2^esr[23:22] bytes *)
	/\ (((23><22) esr:bool[2] = 0b00w) <=> (SzOf r = 1))
	/\ (((23><22) esr:bool[2] = 0b01w) <=> (SzOf r = 2))
	/\ (((23><22) esr:bool[2] = 0b10w) <=> (SzOf r = 4))
	/\ (((23><22) esr:bool[2] = 0b11w) <=> (SzOf r = 8))
	(* fault on stage 1 walk *)
	/\ (esr ' 7 <=> PTreq r)
        (* fault on Write *)
	/\ (esr ' 6 <=> Wreq r) )
``,
 "gicd_supported" -: 
 (* information from internal core state for supported GICD accesses *)
 ``!cis r fi esr.
   (extract_ESR (cis,r,fi) = esr) /\ 
   (?R. cis_abs cis IN {GICD_RS R; GICD_WS R}) 
   ==>
   (* target/source register encoded in esr[20:16] *)
      (gprX(w2n((20><16)esr :bool[5])) = R)
   (* emulation of access is supported *)
    /\ ~iss_gicd_not_supported(esr)
``,
 "gicd_not_supported" -:
 (* internal core state identifies unsupported GICD accesses *)
 ``!cis r fi esr.
   (extract_ESR (cis,r,fi) = esr) /\ (cis_abs cis IN {GICD_RNS; GICD_WNS}) 
   ==>
   (* emulation not supported *)
      iss_gicd_not_supported(esr)
``]);

(* Lemma: memory faults never cause a syscall exception *)
val extract_ESR_not_sc_lem = store_thm("extract_ESR_not_sc_lem", ``
!cis r fi. (31 >< 27) ( w2w (extract_ESR (cis,r,fi)) :bool[64]) <> 11w:bool[5]
``,
  RW_TAC std_ss [] >>
  `?esr. extract_ESR (cis,r,fi) = esr` by ( RW_TAC std_ss [] ) >>
  IMP_RES_TAC ( extract_ESR_axiom // "general" ) >>
  ASM_REWRITE_TAC [] >>
  UNDISCH_TAC ``(27 >< 26) (esr:bool[32]) = 0w:bool[2]`` >>
  BBLAST_PROVE_TAC
);

(* Lemma: coupling between internal state and ESR for supported GICD accesses *)
val extract_ESR_GICD_gpr_lem = store_thm("extract_ESR_GICD_gpr_lem", ``
!cis r fi esr R. cis_abs cis IN {GICD_RS R; GICD_WS R} ==>
    (gprX (w2n ((20><16) (extract_ESR (cis,r,fi)) :bool[5])) = R) 
``,
  RW_TAC std_ss [] >>
  `?esr. extract_ESR (cis,r,fi) = esr` by ( RW_TAC std_ss [] ) >>
  IMP_RES_TAC ( extract_ESR_axiom // "gicd_supported" ) >>
  ASM_REWRITE_TAC []
);

(* Lemma: possible ESR codes for memory faults: data or instr abort *)
val extract_ESR_excp_code_lem = store_thm("extract_ESR_excp_code_lem", ``
!cis r fi. 
    (((31><26) (extract_ESR (cis,r,fi)) :bool[6]) = 36w) \/
    (((31><26) (extract_ESR (cis,r,fi)) :bool[6]) = 32w) 
``,
  RW_TAC std_ss [] >>
  `?esr. extract_ESR (cis,r,fi) = esr` by ( RW_TAC std_ss [] ) >>
  IMP_RES_TAC ( extract_ESR_axiom // "general" ) >>
  ASM_REWRITE_TAC [] >>
  UNDISCH_TAC ``(27 >< 26) (esr:bool[32]) = 0w:bool[2]`` >>
  UNDISCH_TAC ``(31 >< 29) (esr:bool[32]) = 4w:bool[3]`` >>
  BBLAST_PROVE_TAC
);


(* definition of ESR for memory exceptions into EL1, i.e., handled by guest,
   depending on core_internal state (not used), PSTATE, request, fault info 

   The definition reuses extract_ESR to obtain to the highest 5 bits of the ESR
   code (which is independent of the internal state) identifying either a data
   or instruction abort. The next bit, based on PSTATE tells whether the
   exception occurred within the same or a lower exception level. The remainder
   of the ESR register (the ISS code) is invalid in EL1.
*)
val extract_ESR_EL1_def = Define `
extract_ESR_EL1 (cis : core_internal_state, 
		 r : request, 
		 fi : fault_info, 
		 ps:bool[32]) =
( ((31><27)(extract_ESR (cis, r, fi)):bool[5] 
@@ (v2w [ps ' 2] :bool[1])):bool[6] 
@@ ((1w << 25) :bool[26]) ):bool[32]
`;

(* new value for the abstract internal state when sending a memory request 
   
   The next state depends on the type of the request and whether emulation is
   supported by the hypervisor. In case of support the target or source register
   for the request is extracted from the internal state.

   Page table walks on the GIC distributor are never supported.
*)
val next_int_snd_def = Define`
   (next_int_snd cis (Read a d i) = 
       if ((47><12)a IN RPAR.Amap GICD) then 
	   if gicd_acc_not_supported i then GICD_RNS else GICD_RS (ts_reg cis)
       else OTHER)
/\ (next_int_snd cis (Write a d v i) = 
       if ((47><12)a IN RPAR.Amap GICD) then 
	   if gicd_acc_not_supported i then GICD_WNS else GICD_WS (ts_reg cis)
       else OTHER)
(* TODO: map walks on GICD to GICD_RNS? 
         not needed, actually GICD_RNS and GICD_WNS could be merged with OTHER,
         the ISS field indicates to HV that emulation is not supported
 *)
/\ (next_int_snd cis (Walk a i) = OTHER)
`;

(* Lemma: memory request not accessing the GICD set internal state to OTHER *)
val next_int_not_gicd_lem = store_thm("next_int_not_gicd_lem", ``
!cis r. PAdr r NOTIN RPAR.Amap GICD ==> (next_int_snd cis r = OTHER)
``,
  GEN_TAC THEN
  Cases THEN 
  RW_TAC (srw_ss()) [next_int_snd_def, PAdr_def, Adr_def]
);

(* Lemma: after a memory request is sent the internal state is never FLUSHED *)
val next_int_not_flushed_lem = store_thm("next_int_not_flushed_lem", ``
!cis r. next_int_snd cis r <> FLUSHED
``,
  GEN_TAC THEN
  Cases THEN 
  RW_TAC (srw_ss()) [next_int_snd_def, PAdr_def, Adr_def]
);


(* in addition to certain memory requests not being allowed on the GICD per se,
   some supported request types may still fail if they are target certain
   registers that are not virtualized, the registers are read-only, or the wrong
   access size is used. In general GICD registers are either byte- or
   word32-sized.

   fail_gicd (R,B,w)

   states that an access to register R fails if it is a byte access (B=true) or
   a word access (B=false) and a write (w=true) or a read (w=false)
*)
val _ = new_constant("fail_gicd", ``:GICDreg # bool # bool -> bool``);

(* fail_gicd (off,B,w) applies fail_gicd for a given offset into the GICD area

   accesses to off fail additionally if the offset does not represent a GICD
   register, or if a word access is not aligned
 *)
val failgicd_def = Define `
failgicd (off:bool[12], B:bool, w) = 
   (decgicd off = NONE)
\/ fail_gicd(THE(decgicd off), B, w)
\/ (~B /\ ((1><0)off <> 0w:bool[2]))
`;

(* get IRQ number as 10bit string from irqID *)
val irq_id_def = Define `irq_id (q:irqID) = 
case q of
  | PIR n         => n2w n  :bool[10]
  | SGI (id,c,c') => w2w id :bool[10]
`;

(* identify supported GICD access requests wrt. fail_gicd and access size *)
val gicd_req_ok_def = Define `gicd_req_ok r = 
let off = (11><0) (Adr r) in
let (d,w) = case r of
	      | Read a d i    => (d,F)
	      | Write a d v i => (d,T)
	      | _             => (8,F) in
~failgicd(off, d=1, w) /\ d IN {1;4}
`;

(* second stage faults *)

(* identify stage 2 translation faults *)
val _ = new_constant("fi_st2", ``:fault_info -> bool``);

(* st2_fault q - fault reply q is for a stage 2 translation fault *)
val st2_fault_def = Define `
    (st2_fault (Fault r i) = fi_st2 i) 
 /\ (st2_fault _ = F)
`;

(* decoding SMCs and HVCs *)

(* decsmc x - decoding the requested power control commands
   
   the power controller driver is running in EL3, i.e., the secure world. Guests
   can send commands to the controller via explicit secure monitor calls (SMC)
   similar to hypercalls and syscalls.

   Since we do not want to introduce the API for the PSCI controller, we
   introduce function decsmc that decodes the requested power commands from the
   argument of the SMC, i.e., a 16bit string x. It produces a list of Start or
   Stop commands along with the targeted core.
*)   
val _ = new_constant("decsmc", ``:bool[16] -> event list``);

(* Axiom: the decoding function only produces commands that target cores of the
   system and it does not start and stop the same core in the same list of
   commands. The latter assumption is not essential to the proof and rather a
   sanity check.
*)
val decsmc_axiom = new_axiom("decsmc_axiom", ``
!x l. (l = decsmc x) ==>
      !e. MEM e l ==> case e of 
			 | StartCore c => c < RPAR.nc /\ ~(MEM (StopCore c) l)
			 | StopCore c => c < RPAR.nc /\ ~(MEM (StartCore c) l)
			 | _ => F
``);

(* decsigc x - decode IGC notification request from hypercall argument x,
   this is part of the hypervisor ABI that we do not want to detail here *)
val _ = new_constant("decsigc", ``:bool[16] -> num option``);

(* Axiom: the IGC request decoding function only yields existing channels.
   NOTE: in case it returns NONE the hypercall fails.
 *)
val decsigc_axiom = new_axiom("decsigc_axiom", ``
!x s. (decsigc x = SOME s) ==> s < PAR.ns
``);

(* reset state of each core *)

(* Creset c - the initial abstract state of refined core c after reset,
   different cores may have different reset states due to ID registers *)
val _ = new_constant("Creset", ``:num -> refcore_config``);
(* CGreset(g,c) - the initial refined abstract state of core c of guest g after
   reset and initialization by the hypervisor, in particular this state should
   reflect the entrypoint of the guest software *)
val _ = new_constant("CGreset", ``:num # num -> refcore_config``); 
(* extract core id out of hardware ID register MPIDR_EL1 *) 
val _ = new_constant("core_id", ``:bool[64] -> num``);

(* identifies core state at warm boot, i.e., when waken up by primary core *)
val _ = new_constant("warm", ``:refcore_config -> bool``);
(* identifies core state after soft reboot *)
val _ = new_constant("soft", ``:refcore_config -> bool``);

    
(******************** IDEAL MODEL **********************)

(************ abstractions ************)

(* explicit EL1 SPR names needed for ideal model semantics 

   these registers and their semantics need to be covered by any instantiation
   of the model.
*)
(* exception syndrome register *)
new_constant("ESR_EL1", ``:SPRguest``);
(* saved program status (PSTATE) register *)
new_constant("SPSR_EL1", ``:SPRguest``);
(* exception link register *)
new_constant("ELR_EL1", ``:SPRguest``);
(* fault address register *)
new_constant("FAR_EL1", ``:SPRguest``);
(* interrupt vector base address register for EL1 *)
new_constant("VBAR_EL1", ``:SPRguest``);
(* multiprocessor ID register for EL1 *)
new_constant("MPIDR_EL1", ``:SPRguest``);
(* interrupt status register, signals pending FIQ, IRQ, SError interrupts *)
new_constant("ISR_EL1", ``:SPRguest``);

(* all these register names are unique, 
   we require it for exception-related ones *)
val exception_regs_axiom = new_axiom("exception_regs_axiom", ``
    ELR_EL1 <> ESR_EL1 /\ ELR_EL1 <> FAR_EL1 /\ ELR_EL1 <> SPSR_EL1
 /\ ESR_EL1 <> FAR_EL1 /\ ESR_EL1 <> SPSR_EL1 /\ FAR_EL1 <> SPSR_EL1
 /\ ISR_EL1 <> ELR_EL1 /\ ISR_EL1 <> SPSR_EL1
``);

(******* ideal core abstraction functions *******)

(* the following uninterpreted functions must be defined for a given
   instatiation of the ideal core model *)
(* ideal core abstraction function *)
new_constant("idcore_abs", ``:(idcore -> idcore_config)``);
(* internal state of ideal core *)
new_constant("idcore_int", ``:(idcore -> core_internal_state)``);
(* set of pending memory requests from the ideal core *)
new_constant("idcore_req_sent", ``:(idcore -> request set)``);
(* update function, to update the register state and pending requests of a 
   given ideal core *)
new_constant("idcore_upd", ``:idcore # idcore_config # request set -> idcore``);
(* idCGreset(g,c) - abstract reset state for ideal core c of guest g *)
new_constant("idCGreset", ``:num # num -> idcore_config``);

(* exception leve of ideal core, should always be EL0 or EL1 *)
val iMode_def = Define `iMode (c:idcore) = MODE((idcore_abs(c)).PSTATE)`;
(* abstract internal state of ideal core *)
val id_abs_int_def = Define `id_abs_int C = cis_abs ( idcore_int C)`;

(* next instructions will perform HVC or SMC in ideal core,
   the call will use the given 16bit argument *)
val _ = new_constant("id_HVC_next", ``:idcore # bool[16] -> bool``);
val _ = new_constant("id_SMC_next", ``:idcore # bool[16] -> bool``);

(* Axiom *)
val idcore_HVC_next_axiom = new_axiom("idcore_HVC_next_axiom", ``
!C v. id_HVC_next(C,v) ==> (idcore_req_sent C = EMPTY) /\ (idcore_abs C).active
``);

val idcore_SMC_next_axiom = new_axiom("idcore_SMC_next_axiom", ``
!C v. id_SMC_next(C,v) ==> (idcore_req_sent C = EMPTY) /\ (idcore_abs C).active
``);

val idCGreset_axiom = new_axiom("idCGreset_axiom", ``
!g c. ((idCGreset(g,c)).active = F)
   /\ ((idCGreset(g,c)).H.launch = F)
   /\ ((idCGreset(g,c)).PC = (CGreset(g,c)).PC)
   /\ ((idCGreset(g,c)).PSTATE = (CGreset(g,c)).PSTATE)
   /\ ((idCGreset(g,c)).GPR = (CGreset(g,c)).GPR)
   /\ (!r. (idCGreset(g,c)).SPR(r) = (CGreset(g,c)).SPR(INL r))
``);


(******* ideal gic core abstraction functions *******)

(* received and unanswered I/O requests of an ideal GIC, including sender ID *)
new_constant("idgic_req_rcvd", ``:(idgic -> (request # senderID) set)``);
(* the ideal GIC abstraction function *) 
new_constant("idgic_abs", ``:(idgic -> idgic_config)``);

(* physical interrupt state abstaction of the abstract ideal GIC distributor
   
   pistate gicd q

   records the current state of interrupt q in the ideal GIC:

   NOT_ASSERTED - the interrupt was not signaled to the ideal GIC
   ASSERTED - the interrupt was signaled to the ideal GIC but not forwarded
   FORWARDED - the interrupt was forwarded to a core interface within the guest
   ASS_FWD - the interrupt was forwarded but signaled to the GIC again

   Note that these states are synonymous with the PENDING/ACTIVE interrupt
   states within the refined GIC distributor, however as interrupt signaling in
   the ideal model has another level of indirection due to the hypervisor
   involvement, we decided to rename the states in the ideal GIC.
*)   
new_constant("pistate", ``:(GICDreg -> bool[32]) -> (irqID -> PIstate)``);

(* Axiom: the GICD interrupt state only depends on its volatile registers,
   these registers can be read by a core to assess the interrupt state *)
val pistate_axiom = new_axiom("pistate_axiom", ``
!gicd gicd'.
(!R. gicd (VOL R) = gicd' (VOL R)) <=> (pistate gicd = pistate gicd')
``);

(* physical interrupt state of the ideal GIC *)
val PI_def = Define `PI (G:idgic) = pistate ((idgic_abs G).gicd)`;

(* invariant for ideal GICD state under "golden mask" for guest g

   - all interrupts not belonging to g are NOT_ASSERTED
   - SGI interrupts can never be in state ASS_FWD,
     this is specific to the GICv2 model which never makes inter-processor
     interrupts active and pending at the same time
*)
val idgic_gm_conf_def = Define `
    idgic_gm_conf g gicd = 
    (!q. ~guest_irq g q ==> (pistate gicd q = NOT_ASSERTED)) /\
    (!id c' c''. pistate gicd (SGI (id,c',c'')) <> ASS_FWD)`;


(* equivalent (original, more ugly) definition *)
val idgic_gm_conf_def' = store_thm(
   "idgic_gm_conf_def'", ``
   idgic_gm_conf g gicd =
   (!q. pistate gicd q <> NOT_ASSERTED ==>
       case q of
         (* NOTE: no IGC interrupts here *)
         | PIR n           => n >= 16 /\ n < 1020 /\ q IN PIRQ g UNION IPIRQ g
         (* NOTE: SGI interrupts are deactivated in the dist step,
                  thus never active and pending / ASS_FWD *)
         | SGI (id,c',c'') => id <=+ 7w /\ c' < PAR.nc_g g /\ c'' < PAR.nc_g g
                              /\ (pistate gicd q <> ASS_FWD))``,
   SIMP_TAC (srw_ss()) [idgic_gm_conf_def, guest_irq_def'''] >>
   EQ_TAC >>
   REPEAT STRIP_TAC >>
   UNDISCH_ALL_TAC >>
   REPEAT CASE_TAC >|
   [REPEAT STRIP_TAC >>
     SPEC_ASSUM_TAC (``!q:irqID. X``, [``SGI (q,q',r')``]) >>
     FULL_SIMP_TAC (srw_ss()) [] >>
     METIS_TAC [],
    REPEAT STRIP_TAC >>
     SPEC_ASSUM_TAC (``!q:irqID. X``, [``PIR n``]) >>
     FULL_SIMP_TAC (srw_ss()) [] >>
     METIS_TAC [],
    REPEAT STRIP_TAC >>
     SPEC_ASSUM_TAC (``!q:irqID. X``, [``SGI (q,q',r')``]) >>
     FULL_SIMP_TAC (srw_ss()) [] >>
     METIS_TAC [],
    REPEAT STRIP_TAC >>
     SPEC_ASSUM_TAC (``!q:irqID. X``, [``PIR n``]) >>
     FULL_SIMP_TAC (srw_ss()) [] >>
     METIS_TAC [],
    REPEAT STRIP_TAC >>
     SPEC_ASSUM_TAC (``!q:irqID. X``, [``SGI (id, c', c'')``]) >>
     FULL_SIMP_TAC (srw_ss()) [] >>
     METIS_TAC [PIstate_distinct]]);

(* Lemma: in golden mask configuration, only interrupts belonging to guest are
          asserted in ideal GIC distributor *)
val asserted_guest_irq_lem = store_thm(
   "asserted_guest_irq_lem", 
   `` (pistate gicd irq = ASSERTED) /\ (idgic_gm_conf g gicd)
     ==> guest_irq g irq``,
    METIS_TAC [idgic_gm_conf_def, PIstate_distinct]);


(* Axiom: updates of the ideal GICD using idGICDupd function, preserve the
          golden mask configuration by construction 

   TODO: this should rather be an axiom on idGICDupd directly, then generalize
*)
val someIdGICDupds_axiom = new_axiom(
   "someIdGICDupds_axiom", ``!g gicd gicd'.
   (idgic_gm_conf g gicd) /\ (!reg. someIdGICDupds g reg (gicd reg) (gicd' reg))
   ==>
   (idgic_gm_conf g gicd')``);

(* Lemma: one idGICDupd on a register preserves golden mask configuration *)
val idGICDupd_lem = store_thm(
   "idGICDupd_lem", ``
   (idgic_gm_conf g gicd)
   ==>
   (idgic_gm_conf g ((reg =+ idGICDupd g (reg, gicd reg, v)) gicd))``,
   `(!r. someIdGICDupds g r (gicd r) 
	 (((reg =+ idGICDupd g (reg, gicd reg, v)) gicd) r)) ` suffices_by 
       METIS_TAC [someIdGICDupds_axiom] >>
   GEN_TAC >>
   Cases_on `r = reg` >>
   ((* for both cases *)
    ASM_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_THM] >>
    MATCH_MP_TAC someIdGICDupd_someIdGICDupds_lem >>
    SIMP_TAC std_ss [someIdGICDupd_def] >>
    METIS_TAC []
   ));

(* Lemma: similar for generalized update on the same register *)
val someIdGICDupd_preserves_idgic_gm_conf_lem = store_thm(
   "someIdGICDupd_preserves_idgic_gm_conf_lem",
   ``(idgic_gm_conf g gicd) /\ (someIdGICDupd g reg (gicd reg) gicdreg')
      ==>
     (idgic_gm_conf g ((reg =+ gicdreg') gicd))``,
    RW_TAC std_ss [someIdGICDupd_def] >>
    ASM_SIMP_TAC std_ss [combinTheory.APPLY_UPDATE_ID, idGICDupd_lem]);


(* Lemma: similar for series of updates on the same register *)
val someIdGICDupds_preserves_idgic_gm_conf_lem = store_thm(
   "someIdGICDupds_preserves_idgic_gm_conf_lem",
   ``(idgic_gm_conf g gicd) /\ (someIdGICDupds g reg (gicd reg) gicdreg')
      ==>
     (idgic_gm_conf g ((reg =+ gicdreg') gicd))``,
    RW_TAC std_ss [someIdGICDupds_def] >>
    UNDISCH_ALL_TAC >>
    Q.SPEC_TAC (`gicdreg'`, `gicdreg'`) >>
    Induct_on `n` >|
    [(* base case *)
     ASM_SIMP_TAC std_ss [someIdGICDupd_n_def, combinTheory.APPLY_UPDATE_ID],
     (* induction step *)
     RW_TAC std_ss [someIdGICDupd_n_def] >>
     METIS_TAC [someIdGICDupd_preserves_idgic_gm_conf_lem, 
		combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_EQ]]);


(************ abstract transitions ************)

(**** different ideal core steps ****)
(* transition relations, stepping from ideal core state C to C'

   idcore_step_rcv_phys(C,C') - receive physical interrupt
   idcore_step_rcv_rpl(C,q,C') - receive memory reply q
   idcore_step_snd_req(C,r,C') - receive memory request r
   idcore_step_internal(C,C') - internal step, e.g., arithmetic operation
   idcore_step_snd_pscil(C,l,C') - send list of commands to power controller
   idcore_step_snd_igc(C,s,C') - request IGC notification interrupt on channel s
   idcore_step_rcv_psci(C,x,C') - receive PSCI command x
   idcore_step_rcv_startup(C,g,c,C') - start up core c of guest g at reset 
*)
val _ = new_constant("idcore_step_rcv_phys", 
		     ``:idcore # idcore -> bool``);
val _ = new_constant("idcore_step_rcv_rpl", 
		     ``:idcore # reply # idcore -> bool``);
val _ = new_constant("idcore_step_snd_req", 
		     ``:idcore # request # idcore -> bool``);
val _ = new_constant("idcore_step_internal", 
		     ``:idcore # idcore -> bool``);
val _ = new_constant("idcore_step_snd_pscil", 
		     ``:idcore # event list # idcore -> bool``);
val _ = new_constant("idcore_step_snd_igc", 
		     ``:idcore # num # idcore -> bool``);
val _ = new_constant("idcore_step_rcv_psci", 
		     ``:idcore # event # idcore -> bool``);
val _ = new_constant("idcore_step_startup", 
		     ``:idcore # num # num # idcore -> bool``);

(* abstract ideal semantics of receiving read reply from GIC 

   - increase PC
   - update target register R with read value
*)
val idcore_gicd_rrpl = Define `idcore_gicd_rrpl (C:idcore_config) r R = 
C with <| PC := C.PC + 4w; GPR := (R =+ Rpl_val r) C.GPR |>
`;

(* abstract ideal semantics of receiving write reply from GIC 

   - increase PC
*)
val idcore_gicd_wrpl = Define `idcore_gicd_wrpl (C:idcore_config) r R = 
C with <| PC := C.PC + 4w |>
`;

(* abstract specification of ideal core transitions,
   these are expressed on the ideal core state abstractions,
   any instantiation of the ideal core needs to adhere to these conditions.
*) 
val idcore_step_axiom = new_annotated_axiom ("idcore_step_axiom",
``T``,
["internal" -:
 (* internal step

    pre-conditions:
    - core is active
    - no requests to memory are pending   

    post-conditions:
    - the core is still active
    - no memory requests were issued
    - the history variable (launch) is unchanged
    - the internal state may change between OTHER and FLUSHED
    - the exception level may change but not higher than EL1

    Since internal steps can flush the internal state, they often precede
    asynchronous exceptions, as these can only be taken if the internal state is
    FLUSHED.
 *)
 ``!C C'.   idcore_step_internal(C,C') ==> 
                (idcore_req_sent C = idcore_req_sent C') 
             /\ (idcore_abs C).active
             /\ (idcore_abs C').active
             /\ ((idcore_abs C').H = (idcore_abs C).H)
             /\ (idcore_req_sent C = EMPTY)
             (* /\ (id_abs_int C' = FLUSHED) *)
             /\ (id_abs_int C IN {OTHER; FLUSHED} ==> 
			    id_abs_int C' IN {OTHER; FLUSHED})
             /\ (id_abs_int C NOTIN {OTHER; FLUSHED} ==> 
			    (id_abs_int C' = id_abs_int C))
             /\ iMode C' < 2``,
 "internal_enabled" -: 
 (* internal steps can always be executed if the preconditions hold, 
    additionally the exception level must not be above EL1.
    An instantiation may need to allow stuttering steps to conform.
 *)
 ``!C. (idcore_abs C).active /\ iMode C <= 1 /\ (idcore_req_sent C = EMPTY) ==>
       ?C'. idcore_step_internal(C,C')``,
 "snd_pcil" -:
 (* send list l of PSCI commands to power controller (via hypervisor)

    pre-conditions:
    - the next instruction is a secure monitor call
    - its argument encodes list l
    - no memory request is pending
    - the core is active and in EL1

    post-conditions:
    - the core is still active and in EL1
    - no memory requests were issued
    - the history variable (launch) is unchanged
    - the internal state is FLUSHED (due to the call to the hypervisor)
 *)
 ``!C C' l. idcore_step_snd_pscil(C,l,C') ==> 
	     ?v.
                id_SMC_next(C,v)
             /\ (l = decsmc v)
	     /\ (idcore_req_sent C = EMPTY)
             /\ (idcore_req_sent C' = EMPTY)
             /\ (idcore_abs C).active
             /\ (idcore_abs C').active
             /\ ((idcore_abs C').H = (idcore_abs C).H)
             /\ (id_abs_int C' = FLUSHED)
             /\ ((iMode C = 1) /\ (iMode C' = 1))``,
 "snd_pscil_enabled" -:
 (* PSCI commands can always be sent if the preconditions hold. *)
 ``!C l. (iMode C = 1) /\ (idcore_req_sent C = EMPTY) /\ (idcore_abs C).active
      /\ (?v. id_SMC_next(C,v) /\ (l = decsmc v))
	 ==> 
	 ?C'. idcore_step_snd_pscil(C,l,C')``,
 "snd_igc" -:
 (* request IGC notification interrupt for channel s

    pre-conditions:
    - the next instruction is a hypercall
    - its argument encodes channel s, s=PAR.ns encodes a non-existing channel
    - no memory request is pending
    - the core is active and in EL1

    post-conditions:
    - the core is still active and in EL1
    - no memory requests were issued
    - the history variable (launch) is unchanged
    - the internal state is FLUSHED (due to the call to the hypervisor)

    TODO: increase PC
 *)
 ``!C C' s. idcore_step_snd_igc(C,s,C') ==> 
	     ?v.
                id_HVC_next(C,v)
             /\ (s = if IS_SOME(decsigc v) then THE (decsigc v) else PAR.ns)
	     /\ (idcore_req_sent C = EMPTY)
	     /\ (idcore_req_sent C' = EMPTY)
             /\ (idcore_abs C).active
             /\ (idcore_abs C').active
             /\ ((idcore_abs C').H = (idcore_abs C).H)
             /\ (id_abs_int C' = FLUSHED)
             /\ (iMode C = 1) /\ (iMode C' = 1)``,
 "snd_igc_enabled" -:
 (* IGC notifications can always be requested if the preconditions hold. *)
 ``!C s. (iMode C = 1) /\ (idcore_req_sent C = EMPTY) /\ (idcore_abs C).active
      /\ (?v. id_HVC_next(C,v)
      /\ (s = if IS_SOME(decsigc v) then THE (decsigc v) else PAR.ns))
	 ==> 
	 ?C'. idcore_step_snd_igc(C,s,C')``,
 (* receive physical interrupt, take asynchronous exception

    pre-conditions:
    - the core is active
    - no memory request is pending
    - the internal state is FLUSHED
    - IRQs are not masked in the PSTATE register

    post-conditions:
    - the core is still active
    - no memory requests were issued
    - the history variable (launch) is unchanged
    - the internal state is still FLUSHED
    - the PC is set to the entry point of the corresponding interrupt handler,
      according to the interrupt vector table and the required offset
    - the exception level is updated to EL1
    - the GPRs are unchanged
    - SPR ELR_EL1 contains the old PC
    - SPR ISR_EL1 indicates an IRQ
    - SPR SPSR_EL1 contains the old value of PSTATE
    - other SPRs of EL1 are unchanged

    TODO: this should also mask the interrupts, and possibly update other fields
	  of PSTATE too, not required for bisimulation proof though
 *)
 "rcv_phys" -:
 ``!C C'. idcore_step_rcv_phys(C,C') ==> 
                (idcore_req_sent C = EMPTY) 
             /\ (idcore_req_sent C' = EMPTY)
             /\ (id_abs_int C = FLUSHED)
             /\ (id_abs_int C' = FLUSHED)
	     /\ ~word_bit 7 (idcore_abs C).PSTATE
             /\ ((idcore_abs C').active /\ (idcore_abs C).active)
             /\ ((idcore_abs C').H = (idcore_abs C).H)
             /\ ((idcore_abs C').PC = (idcore_abs C).SPR(VBAR_EL1) + 
				      async_ghoff(w2w (idcore_abs C).PSTATE)) 
             /\ ((idcore_abs C').PSTATE = MODE_upd((idcore_abs C).PSTATE, 1))
             /\ ((idcore_abs C').GPR = (idcore_abs C).GPR)
             /\ (!r.
		 if r=ELR_EL1 then (idcore_abs C').SPR r = (idcore_abs C).PC
		 else if r=ISR_EL1 then (idcore_abs C').SPR r = 0x80w
		 else if r=SPSR_EL1 then (idcore_abs C').SPR r = w2w ((idcore_abs C).PSTATE)
		 else (idcore_abs C').SPR r  = (idcore_abs C).SPR r )``,
 "rcv_phys_enabled" -:
 (* physical interrupts can always be received if the preconditions hold.
    additionally the exception level must be at most EL1.
    Note that this requires any instantiation to be ready to take an
    asynchronous exception when the internal state is FLUSHED *)
 ``!C. iMode C <= 1 /\ (idcore_req_sent C = EMPTY)
    /\ ~word_bit 7 (idcore_abs C).PSTATE
    /\ (id_abs_int C = FLUSHED)
    /\ (idcore_abs C).active
       ==> 
       ?C'. idcore_step_rcv_phys(C,C')``,
 "snd_req" -:
 (* send memory request r

    pre-conditions:
    - the core is active
    - no memory request is pending
    - the exception level is at most EL1

    post-conditions:
    - the core is still active
    - the memory request r is recorded in idcore_reqsent
    - the history variable (launch) is unchanged
    - the internal state is updated by next_int_snd
    - the exception level is unchanged

    Note that the requirement to have no pending memory requests essentially
    forces any core instantiation to issue memory requests sequentially, i.e.,
    it does not allow to have several memory requests pending at the same time.

    We initially put the restriction here to reduce the complexity of the model,
    however we do not use it in the defintion of the invariants and bisimulation
    relation and it does not seem to simplify the proof significantly, hence it
    can be dropped if needed. However, this has implications on the definition
    of exception handling.

    The restriction makes it harder to model side-effects of out-of-order
    execution in the cores, however it does not rule it out completely, as the
    core in our system not only contains the execution units but also the first
    stage MMU including corresponding TLB(s) and may contain virtually-indexed
    L1 caches that can satisfy out-of-order memory accesses.

    In any case, the sequence of memory accesses issued by the core is in no way
    bound to a program order. The number of simultaneous memory accesses is in
    fact bound by the memory subsystem and thus depending on the specific
    hardware platform, hence it should be restricted using a model parameter
    (which in this development is implicitly assumed to be one).
 
    NOTE: we do not define when sending a request needs to be enabled, as this
    depends on the instruction executing on the core.
 *)
 ``!C C' r. idcore_step_snd_req(C,r,C') ==>
	        (idcore_req_sent C = EMPTY)
             /\ (idcore_req_sent C' = {r})
             /\ (idcore_abs C).active
             /\ (idcore_abs C').active
             /\ ((idcore_abs C').H = (idcore_abs C).H)
	     /\ iMode C < 2
             /\ (iMode C' = iMode C)
	     /\ (id_abs_int C' = next_int_snd (idcore_int C) r)
``,
 "rcv_rpl" -:
 (* receive memory reply r

    pre-conditions:
    - the core is active
    - a matching memory request q is pending
    - the exception level is at most EL1

    post-conditions:
    - the core is still active
    - the memory request q is removed from idcore_reqsent
    - the history variable (launch) is unchanged
    - the internal state is updated by next_int_snd
    - the exception level is unchanged except a fault is received
    - the internal state is updated depending on whether q accessed the GICD:
      - q read/write GICD: the core is updated according to the semantics,
                           the internal state is FLUSHED (due to the involvement
                           of the hypervisor emulating the access)
      - otherwise the internal state maybe FLUSHED or OTHER
 *)
 ``!C C' r. idcore_step_rcv_rpl(C,r,C') ==>
          ?q. 
	     q IN idcore_req_sent C /\ match(q,r) 
          /\ (idcore_req_sent C' = idcore_req_sent C DIFF {q})
          /\ (idcore_abs C).active
          /\ (idcore_abs C').active
          /\ ((idcore_abs C').H = (idcore_abs C).H)
	  /\ iMode C < 2
          /\ (~Frpl r ==> (iMode C' = iMode C))
	  /\ (case id_abs_int C of
		| GICD_RS R => 
		       (idcore_abs C' = idcore_gicd_rrpl (idcore_abs C) r R)
		    /\ (id_abs_int C' = FLUSHED)
		| GICD_WS R => 
		       (idcore_abs C' = idcore_gicd_wrpl (idcore_abs C) r R)
		    /\ (id_abs_int C' = FLUSHED)
		| _ => ((id_abs_int C') IN {OTHER; FLUSHED}))
``,
 "rcv_rpl_enabled" -:
 (* memory replies can always be received if the preconditions hold *)
 ``!C q. iMode C <= 1 /\ (?r. r IN idcore_req_sent C /\ match(r,q))  
      /\ (idcore_abs C).active
	 ==> 
	 ?C'. idcore_step_rcv_rpl(C,q,C')``,
 "rcv_fault" -:
 (* receive memory reply q which is a fault for request r, 
    the core takes an exception into EL1

    the same pre- and post-conditions as above apply

    additional post-conditions:
    - no message is pending
    - the PC is set to the entry point of the corresponding exception handler,
      according to the interrupt vector table and the required offset
    - the exception level is updated to EL1
    - the GPRs are unchanged
    - SPR ELR_EL1 contains the old PC
    - SPR ESR_EL1 contains extracted fault information
    - SPR FAR_EL1 contains the faulting address information
    - SPR SPSR_EL1 contains the old value of PSTATE
    - other SPRs of EL1 are unchanged
    - the internal state is FLUSHED

    Note that here the simplification of having at most one memory access
    pending in the core pays off because we do not have to model the cases where
    one memory access causes a fault and the others are still pending. In order
    to ensure precise exceptions, the program order of memory accesses would be
    required as well as a mechanism to cancel memory requests (or ignore their
    replies) if they are program-order-after the faulting request.
 *)
 ``!C C' q r fi. idcore_step_rcv_rpl(C,q,C') /\ (q = Fault r fi) ==>
	     (idcore_abs C).active /\ (idcore_abs C').active 
	  /\ ((idcore_abs C').PC = (idcore_abs C).SPR(VBAR_EL1) + 
				   ghoff(w2w (idcore_abs C).PSTATE)) 
	  /\ ((idcore_abs C').PSTATE = MODE_upd((idcore_abs C).PSTATE, 1))
	  /\ ((idcore_abs C').GPR = (idcore_abs C).GPR)
	  /\ (!R. if R=ELR_EL1 then (idcore_abs C').SPR R = (idcore_abs C).PC
		  else if R=ESR_EL1 then 
		      (idcore_abs C').SPR R = 
		      w2w (extract_ESR_EL1 (idcore_int C, r, fi, 
					    (idcore_abs C).PSTATE))
		  else if R=FAR_EL1 then 
		      (idcore_abs C').SPR R = w2w (extract_FAR fi)
		  else if R=SPSR_EL1 then 
		      (idcore_abs C').SPR R = w2w ((idcore_abs C).PSTATE)
		  else (idcore_abs C').SPR R  = (idcore_abs C).SPR R )
	  /\ (idcore_req_sent C' = EMPTY)
	  /\ (id_abs_int C' = FLUSHED)
	  /\ ((idcore_abs C').H = (idcore_abs C).H)``,
 "rcv_psci" -:
 (* receive a PSCI event e from the power controller

    pre-conditions:
    - no memory request is pending
    - the internal state is FLUSHED (always the case for inactive cores)
    - e must be StartCore c or StopCore c for some core index c 
      (we ignore if the core ID matches)

    post-conditions:
    - no memory requests were issued
    - the history variable (launch) and the power state depend on e:
      StartCore: ignore if already active, no changes
		 if inactive set launch to true, no other changes
      StopCore: ignore if already inactive, no changes
                if active make inactive and set launch to false
    - the internal state is still FLUSHED

    Observe that the preconditions ensure that a core is never powered down in
    the middle of a memory request, i.e., it shuts down gracefully.
 *)
 ``!C C' e. idcore_step_rcv_psci(C,e,C') ==>
             (idcore_req_sent C = EMPTY)
	  /\ (idcore_req_sent C' = EMPTY)
	  /\ (case e of 
	       | StopCore _ => (if ~(idcore_abs C).active
	                        then (C' = C)
				else ((idcore_abs C') = (idcore_abs C) 
                                with <|active := F ; H := <| launch := F |> |>))
	       | StartCore _ => (if (idcore_abs C).active
	                        then (C' = C)
	                        else (idcore_abs C' = idcore_abs(C) 
                                with H := <| launch := T |>))
	       | _ => F)
	  /\ (id_abs_int C = FLUSHED)
          /\ (id_abs_int C' = FLUSHED)``,
 "rcv_psci_enabled" -:
 (* we require that a core can always be powered up while it is inactive,
    in this case no memory requests are supposed to be pending *)
 ``!C e. ((idcore_req_sent C = EMPTY) \/ ~(idcore_abs C).active)
	   ==> 
	   ?C'. idcore_step_rcv_psci(C,e,C')``,
 "startup" -: 
 (* start execution after reset / power up on core c of guest g

    pre-conditions:
    - the launch bit is set

    post-conditions:
    - set all registers to their initial values according to idCGreset
    - the core is active
    - launch is set to false
    - no memory requests were issued
    - the internal state is FLUSHED

    When a core is powered up in the refined model the EL3 boot code and EL2
    hypervisor initializationis executed before the guest code can start
    executing. This boot phase is invisible in the ideal model. Instead there is
    one atomic startup transition that performs all the initialization steps
    that are implemented by the boot loader and the hypervisor.
 *)
 ``!C C' g c. idcore_step_startup(C,g,c,C') ==>
             ((idcore_abs C).H.launch)
          /\ (idcore_abs(C') = idCGreset(g,c)
              with <| active := T;  H := <| launch := F|> |>)
	  /\ (idcore_req_sent C' = EMPTY)
	  /\ (id_abs_int C' = FLUSHED)
``
]);

(* invariant on the ideal core in terms of abstraction,
   mainly sanity checks and implicit assumptions of the model:

   - at most one pending memory request
   - the exception level is at most EL1
   - inactive cores have no pending memory request and a FLUSHED internal state
   - if the launch bit is set, the core is inactive / powered down
   - if the abstract interal state is FLUSHED, no memory request are pending
   - the internal state is GICD_RS R iff an memory mapped I/O read access to the
     GICD is pending, that can be emulated by the hypervisor and the resulting
     value will be written into R
   - the internal state is GICD_RNS if an unsupported GICD read is pending
   - the internal state is GICD_WS R iff an memory mapped I/O write access to
     the GICD is pending, that can be emulated by the hypervisor and the
     value to be written is taken from source register R
   - the internal state is GICD_WNS if an unsupported GICD write is pending

   TODO: GICD_RNS and GICD_WNS can probably be omitted / merged with OTHER
*)
val inv_good_idcore_def = Define `inv_good_idcore (C:idcore) = 
    (CARD(idcore_req_sent C) <= 1)
 /\ FINITE (idcore_req_sent C)
 /\ iMode C < 2
 /\ ((~(idcore_abs C).active) ==> (idcore_req_sent C = EMPTY))
 /\ ((~(idcore_abs C).active) ==> (id_abs_int C = FLUSHED))
 /\ ((idcore_abs C).H.launch ==> ~(idcore_abs C).active)
 /\ ((id_abs_int C = FLUSHED) ==> (idcore_req_sent C = EMPTY))
 /\ ((?R. id_abs_int C = GICD_RS R) <=> 
	 (?r. Rreq r /\ PAdr r IN RPAR.Amap GICD 
             /\ ~gicd_acc_not_supported (MsgOf r) /\ r IN idcore_req_sent C) )
 /\ ((id_abs_int C = GICD_RNS) <=> 
	 (?r. Rreq r /\ PAdr r IN RPAR.Amap GICD 
             /\ gicd_acc_not_supported (MsgOf r) /\ r IN idcore_req_sent C) )
 /\ ((?R. (id_abs_int C = GICD_WS R)) <=> 
	 (?r. Wreq r /\ PAdr r IN RPAR.Amap GICD 
             /\ ~gicd_acc_not_supported (MsgOf r) /\ r IN idcore_req_sent C) )
 /\ ((id_abs_int C = GICD_WNS) <=> 
	 (?r. Wreq r /\ PAdr r IN RPAR.Amap GICD 
             /\ gicd_acc_not_supported (MsgOf r) /\ r IN idcore_req_sent C) )
`;

(* Lemma: if the ideal core invariant holds and no memory request is pending,
          then the abstract internal state is neither GICD_RS nor GICD_WS *)
val inv_good_idcore_int_lem = store_thm("inv_good_idcore_int_lem", ``
!C. inv_good_idcore C /\ (idcore_req_sent C = EMPTY) ==>
    !R. id_abs_int C NOTIN {GICD_RS R; GICD_WS R}
``,
  RW_TAC std_ss [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >> (
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC inv_good_idcore_def >>
      REV_FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
  )
);

(**** GIC steps ****)

(* transitions of the ideal GIC, stepping from state G to G'

   idgic_step_rcv_req(G,r,s,G') - receive memory-mapped I/O request r from s
   idgic_step_rcv_irq(G,q,g,G') - receive peripheral interrupt q within guest g
   idgic_step_dist_irq(G,r,c,g,G') - 
	forward interrupt q to the ideal GIC interface of core c in guest g
   idgic_step_snd_irq(G,c,G') - trigger (virtualized) IRQ in core c
   idgic_step_snd_rpl(G,q,s,g,G') - send MMIO reply q from s within guest g
   idgic_step_rcv_igc(G,s,c,G') - 
	receive IGC notification interrupt for core c on inter-guest 
	communication channel s

   Note that some of the ideal GIC transitions take the guest ID as a parameter.
   The idea behind this is that the ideal GIC by construction implements the
   interrupt isolation policy of the hypervisor, i.e., it never signals
   interrupts that do not belong to its guest and it does not expose any
   information about interrupts belonging to other guests through its memory
   mapped I/O interface. This reflects the interrupt virtualization implemented
   by the hypervisor.

   In the same way, other virtualized functionality, like the distribution of
   interrupts to the (virtual) core interfaces and the reception of IGC
   notification interrupts from other guests, is represented by special
   transitions of the ideal GIC.
*)
val _ = new_constant("idgic_step_rcv_req", 
		     ``:idgic # request # senderID # idgic -> bool``);
val _ = new_constant("idgic_step_rcv_irq", 
		     ``:idgic # irqID # num # idgic -> bool``);
val _ = new_constant("idgic_step_dist_irq", 
		     ``:idgic # irqID # num # num # idgic -> bool``);
val _ = new_constant("idgic_step_snd_irq", 
		     ``:idgic # num # idgic  -> bool``);
val _ = new_constant("idgic_step_snd_rpl", 
		     ``:idgic # reply # senderID # num # idgic -> bool``);
val _ = new_constant("idgic_step_rcv_igc", 
		     ``:idgic # num # num # idgic -> bool``);



(* abstract specification of ideal generic interrupt controller,
   the desired behavoiur is expressed via the ideal GIC state abstractions,
   any instantiation of the ideal GIC needs to adhere to these conditions.
*) 
val idgic_step_axiom = new_annotated_axiom ("idgic_step_axiom",
``T``,
["rcv_req" -:
 (* receive memory-mapped I/O request r from sender s

    pre-conditions:
    - none assumed

    post-conditions:
    - the request (r,s) is recorded in idgic_req_rcvd
    - the rest of the abstract GIC state is unchanged
 *)
 ``!G G' r s. idgic_step_rcv_req (G,r,s,G') ==>
              (idgic_req_rcvd G' = (idgic_req_rcvd G UNION {(r,s)}))
           /\ ((idgic_abs G') = (idgic_abs G))``, 
 "rcv_req_enabled" -:
 (* we demand that the ideal GIC is always ready to receive MMIO requests that
    are directed at the GIC region in memory *)
 ``!G r id. (?A. gicAR A /\ PAdr r IN RPAR.Amap A) ==> 
   ?G'. idgic_step_rcv_req(G,r,id,G')``,
 "rcv_irq" -:
 (* receive peripheral irq q within guest g

    pre-conditions:
    - none assumed

    post-conditions:
    - the pending memory-mapped I/O requests are unchanged
    - if q is a peripheral interrupt of g the physical interrupt state changes:
        if q was NOT_ASSERTED -> q becomes ASSERTED
        if q was ASSERTED -> q stays ASSERTED, additional interrupt is ignored
        if q was FORWARDED -> state of q becomes ASS_FWD
        if q was ASS_FWD -> no change, additional interrupt is ignored
    - the physical interrupt state of all other interrupts is unchanged
    - the constant and mutable GICD registers are unchanged, i.e., only the
      volatile part of GICD may change (according to the change in PI)
    - the interrupt core interfaces are unchanged
    - the core interface state (GICC) is unchanged
 *)
  ``!G G' q g. idgic_step_rcv_irq (G,q,g,G') ==>
             (idgic_req_rcvd G' = idgic_req_rcvd G)
          /\ (q IN lPIRQ g ==>
              (PI G' q = case PI G q of
                          | NOT_ASSERTED => ASSERTED
			  | ASSERTED     => ASSERTED
	        	  | FORWARDED    => ASS_FWD
			  | ASS_FWD  => ASS_FWD))
          /\ (!q'. q <> q' ==> (PI G' q' = PI G q'))
          /\ (!r. (idgic_abs G').gicd (CONST r) = (idgic_abs G).gicd (CONST r))
          /\ (!r. (idgic_abs G').gicd (MUTE r) = (idgic_abs G).gicd (MUTE r))
          /\ ((idgic_abs G).Q = (idgic_abs G').Q)
          /\ ((idgic_abs G).gicc = (idgic_abs G').gicc)``, 
 "rcv_irq_enabled" -:
 (* a peripheral interrupt belonging to g may be received at all times *)
 ``!G q g. ?G'. (q IN PIRQ g) ==> idgic_step_rcv_irq(G,q,g,G')``,
 (* forward interrupt q to the interrupt interface of core c within guest g

    pre-conditions:
    - q must have interrupt state ASSERTED
    - if q is a peripheral interrupt, i.e., not an SGI:
        q must be INACTIVE at the core interface (Q)
        q must have a valid peripheral interrupt id
    - if q is an SGI (inter-processor interrupt) from core c':
	q may be INACTIVE or ACTIVE at the core interface
        q must be a non-secure interrupt (id <= 7) and targeting c
        c' must be a core belonging to g
    - q is not masked at the distributor, i.e., forwarding it to c is enabled

    post-conditions:
    - add that the pending memory-mapped I/O requests are unchanged
    - the physical interrupt state changes:
        if q is a peripheral, it becomes FORWARDED 
        if q is a SGI, it becomes NOT_ASSERTED (SGI semantics in GICv2)
        for all other interrupts the state is unchanged
    - the interrupt core interface of core c changes:
        if q was INACTIVE -> q becomes PENDING
        if q was PENDING -> q stays PENDING, additional interrupt is ignored
        if q was ACTIVE -> state of q becomes PENDING AND ACTIVE
        if q was PENDACT -> no change, additional interrupt is ignored
    - the core interfaces of all other cores are unchanged
    - the constant and mutable GICD registers are unchanged, i.e., only the
      volatile part of GICD may change (according to the change in PI)
    - the core interface state (GICC) is unchanged 

    Note that the GICC state in this model contains only configuration data and
    is not influenced by changes in the interrupt state, represented by Q. While
    there are GICC registers that display the interrupt state, the ideal GIC
    consults Q for reads to these registers and formats the information in the
    memory reply accordingly.

    The same approach is not viable for the GIC distributor state as the GICv2
    spec allows an operating system to save and restore the volatile distributor
    state, hence PI (pistate) is a function of the GICD registers.

    TODO: the current definition does not consider interrupt priorities when
    forwarding. Intuitively, q whould have the highest priority among all other
    ASSERTED interrupts that are unmasked for c.
 *)
 "dist_irq" -:
  ``!G G' q c. idgic_step_dist_irq (G,q,c,g,G') ==> 
               (idgic_req_rcvd G' = idgic_req_rcvd G)
            /\ (PI G q = ASSERTED)
            /\ (!id. (q = PIR id) ==> ((idgic_abs G).Q c q = INACTIVE))
            /\ (!id. (q = PIR id) ==> (id >= 16 /\ id < 1020))
	    /\ (!id c' c''. (q = SGI (id,c',c'')) ==> 
		    (((idgic_abs G).Q c q) IN {ACTIVE; INACTIVE}))
	    /\ (!id c' c''. (q = SGI (id,c',c'')) ==> 
		    id <=+ 7w /\ (c'' = c) /\ c' < PAR.nc_g g)
	    /\ q NOTIN idmsk((idgic_abs G).gicd, c)
            /\ (!q'. PI G' q' = if q' = q then 
				    case q of
				      | PIR n => FORWARDED
				      | SGI x => NOT_ASSERTED
				else PI G q')
	    /\ (!q' c'. (idgic_abs G').Q c' q' = 
		        if (q' = q) /\ (c' = c) then
			    case (idgic_abs G).Q c q of
                              | INACTIVE => PENDING 
			      | PENDING  => PENDING
			      | ACTIVE   => PENDACT
			      | PENDACT  => PENDACT 
			else (idgic_abs G).Q c' q' )
            /\ ((idgic_abs G).gicc = (idgic_abs G').gicc)
            /\ (!r. (idgic_abs G').gicd (CONST r) = 
		(idgic_abs G).gicd (CONST r))
            /\ (!r. (idgic_abs G').gicd (MUTE r) = 
		(idgic_abs G).gicd (MUTE r))``,
 "dist_irq_enabled" -:
 (* forwarding interrupts should always be possible if the pre-conditions hold,
    TODO: add all pre-conditions *) 
 ``!G q c. (PI G q = ASSERTED)
        /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
        /\ (!id c' c''. (q = SGI (id,c',c'')) ==> id <=+ 7w /\ (c'' = c))
        /\ q NOTIN idmsk((idgic_abs G).gicd, c)
   ==>
   ?G'. idgic_step_dist_irq (G,q,c,G')``,
 "snd_irq" -:
 (* send interrupt q to core c, triggering an exception

    pre-conditions:
    - q is PENDING at the interrupt interface for c and not masked
    - q is has the highest priority of such interrupts
    - if q is a peripheral interrupt, it has a valid ID
    - if q is an SGI it targets c and as an ID <= 7

    post-conditions:
    - the pending MMIO requests are unchangd
    - the abstract GIC and physical interrupt states are unchanged
 *)
  ``!G c G'. idgic_step_snd_irq (G,c,G') ==>
             (?q R. 
	        (R = ready_irqs((idgic_abs G).Q c, ipmsk((idgic_abs G).gicc c)))
             /\ q IN R /\ (w2n (prio q) = max_prio R)
             /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
            /\ (!id c' c''. (q = SGI (id, c', c'')) ==> id <=+ 7w /\ (c'' = c)))
            /\ (idgic_req_rcvd G' = idgic_req_rcvd G)
            /\ ((idgic_abs G') = (idgic_abs G))
	    /\ (PI G' = PI G)``,
 "snd_irq_enabled" -:
 (* sending interrupts should always be possible if the pre-conditions hold *) 
  ``!G c. (?q R. 
           (R = ready_irqs((idgic_abs G).Q c, ipmsk((idgic_abs G).gicc c)))
	/\ q IN R /\ (w2n (prio q) = max_prio R)
        /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
        /\ (!id c' c''. (q = SGI (id, c', c'')) ==> id <=+ 7w /\ (c'' = c)) )
    ==> 
    ?G'. idgic_step_snd_irq (G,c,G')``,
 "snd_rpl_gicc" -:
 (* send reply q to core c of guest g, for an MMIO request to the GICC

    pre-conditions:
    - a matching request r is pending at the GIC

    post-conditions:
    - the pending MMIO requests is removed from idgic_req_rcvd
    - the constant and mutable registers of the GICD state are unchanged
    - the interrupt core interface of c may change for peripheral interrupts or
      SGIs targeting c, due to acknowledgement or deactivation of interrupts,
      we overapproximate the state change as follows:
        INACTIVE interrupts stay INACTIVE
        PENDING interrupts may become ACTIVE
        ACTIVE interrupts may become INACTIVE
        PENDING AND ACTIVE interrupts may become PENDING
        invalid / unsupported interrupt ranges stay INACTIVE
    - the GICC states and interrupt interfaces of other cores are unchanged
    - for all cores INACTIVE interrupts stay INACTIVE
    - peripheral interrupts of guest g cannot become PENDACT for core c,
      TODO: this seems redundant
    - the physical interrupt state of peripheral interrupts q at the
      distributor may be affected by deactivation at the GICC interface,
      depending on the new state Q' q and the old state PI q:
	Q' q INACTIVE and PI q FORWARDED -> PI' q becomes NOT_ASSERTED
        Q' q INACTIVE and PI q ASS_FWD -> PI' q becomes ASSERTED
	otherwise -> PI' q unchanged
    - SGIs are not affected by deactivation at the GICC (GICv2 semantics)

    The main take-away from these restrictions is that a guest cannot activate
    any interrupts by accessing the GICC interface, in particular not those
    assigned to other guests. It can merely deactivate interrupts, hence
    interrupt isolation is preserved.

    Note that we only specify core accesses to the GIC, peripherals are barred
    from accessing the GIC via the hypervisor's SMMU configuration.
 *)
  ``!G G' q c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G') 
              /\ Rpl_PAdr q IN RPAR.Amap GICC
    ==> 
    ?r.     	
       (r, CoreSender c) IN idgic_req_rcvd G /\ match(r,q)
    /\ (idgic_req_rcvd G' = idgic_req_rcvd G DIFF {(r, CoreSender c)})
    /\ (!R. (idgic_abs G').gicd (CONST R) = (idgic_abs G).gicd (CONST R))
    /\ (!R. (idgic_abs G').gicd (MUTE R) = (idgic_abs G).gicd (MUTE R))
    /\ (!irq. (?id:bool[10] c'. 
		       (irq = SGI ((3><0) id, c', c)) /\ id <=+ 7w
                    \/ (irq = PIR (w2n id)) /\ id >=+ 16w /\ id <+ 1020w) ==>
            	case (idgic_abs G).Q c irq of 
    (* GICC accesses cannot make inactive interrupt pending or active *)
              | INACTIVE => (idgic_abs G').Q c irq = INACTIVE
              | PENDING  => (idgic_abs G').Q c irq IN {PENDING; ACTIVE}
              | ACTIVE   => (idgic_abs G').Q c irq IN {ACTIVE; INACTIVE}
              | PENDACT  => (idgic_abs G').Q c irq IN {PENDACT; PENDING} ) 
    /\ (!n. (n>7 /\ n<16 \/ n>=1020) ==> 
	    ((idgic_abs G').Q c (PIR n) = INACTIVE))
    /\ (!c'. c <> c' ==> ((idgic_abs G').Q c' = (idgic_abs G).Q c')
                      /\ ((idgic_abs G').gicc c' = (idgic_abs G).gicc c'))
    (* all INACTIVE interrupts stay INACTIVE, 
       this includes SGIs at Q c that do not target c (not covered above) *)
    /\ (!c_ irq. ((idgic_abs G).Q c_ irq = INACTIVE) ==> 
	    ((idgic_abs G').Q c_ irq = INACTIVE))
    /\ (!n. (PIR n IN PIRQ g) /\ ((idgic_abs G).Q c (PIR n) <> PENDACT) ==> 
				 ((idgic_abs G').Q c (PIR n) <> PENDACT))
    (* interrupt deactivation may affect peripheral interrupt states *)
    /\ (!pir. PI G' pir = 
	if (?n. (n>=16) /\ (n<1020) /\ (pir = PIR n) 
	     /\ (idgic_abs G').Q c pir <> (idgic_abs G).Q c pir )
	    then
	        case ((idgic_abs G').Q c pir, PI G pir) of 
	 	      | (INACTIVE, FORWARDED)  => NOT_ASSERTED
	 	      | (INACTIVE, ASS_FWD)    => ASSERTED
	 	      | _                      => PI G pir 
	else PI G pir )``,
 "gicd_read" -:
 (* send reply q to core c of guest g, for an MMIO read request to the GICD

    pre-conditions:
    - it accesses a valid GICD register with a byte or word access
    - a matching read request r is pending at the GIC

    post-conditions:
    - the pending MMIO requests is removed from idgic_req_rcvd
    - the abstract GIC state is unchanged, thus read accesses to the distributor
      (as opposed to the GICC) do not have side effects

    Again we only specify core accesses to the GIC. Peripherals have no access.
 *)
 ``!G q r G' v c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G') 
		 /\ Rpl_PAdr q IN RPAR.Amap GICD
                 /\ (q = ReadValue r v)
   ==> 
   let off = (11><0) (Rpl_Adr q) in
   let reg = (idgic_abs G).gicd (THE (decgicd off)) in
      IS_SOME (decgicd off)
   /\ (?a i. (r = Read a 1 i) /\ (v = w2v ((7><0)reg :bool[8]))
          \/ (r = Read a 4 i) /\ (v = w2v reg) )
   /\ (r, CoreSender c) IN idgic_req_rcvd G /\ match(r,q)
   /\ (idgic_req_rcvd G' = idgic_req_rcvd G DIFF {(r,CoreSender c)})
   /\ (idgic_abs G' = idgic_abs G)``,
 "gicd_write" -:
 (* send reply q to core c of guest g, for an MMIO write request to the GICD

    pre-conditions:
    - it accesses a valid GICD register R
    - TODO: need to restrict access size?
    - a matching write request r is pending at the GIC
    

    post-conditions:
    - the pending MMIO requests is removed from idgic_req_rcvd
    - in general, if GICD registers change they only may do so if the change is
      allowed by the ideal update function
    - constant registers stay constant,
      TODO: this should be a property of the update function
    - if R is mutable, it is updated using the update fuction for guest g 
    - all other mutable registers are unchanged
    - if R is volatile, it is updated using the update fuction for guest g 
    - if R is mutable, volatile registers may only change if GICD_SGIR is
      accessed, requesting an inter-processor interrupt
    - the GICC state and all interrupt core interfaces are unchanged

    The essential point in these restrictions is that GICD registers are updated
    using idGICDupd depending on guest index g, thus it is by construction
    guaranteed that no configuration that may break interrupt isolation can be
    established. In particular, the "golden mask" configuration of the GICD is
    preserved, hence no interrupts of other guests are active or pending.

    Note that we explicitly allow volatile registers to change even if they are
    not explicitly accessed, however by construction, these changes are
    restricted to what can be changed by applying the idGICDupd function.

    Again we only specify core accesses to the GIC. Peripherals have no access.
 *)
 ``!G q r G' v c g. idgic_step_snd_rpl(G, q, CoreSender c, g, G') 
		 /\ Rpl_PAdr q IN RPAR.Amap GICD
		 /\ (q = WrittenValue r)
		 /\ (Req_val r = v)
   ==> 
   let off = (11><0) (Rpl_Adr q) in 
   let reg = THE (decgicd off) in
   let u = (idgic_abs G).gicd reg in
      IS_SOME (decgicd off) 
   /\ (r, CoreSender c) IN idgic_req_rcvd G /\ match(r,q)
   /\ (idgic_req_rcvd G' = idgic_req_rcvd G DIFF {(r,CoreSender c)})
   /\ (!GR. someIdGICDupds g GR ((idgic_abs G).gicd GR) ((idgic_abs G').gicd GR))
   /\ (!R. (idgic_abs G').gicd (CONST R) = (idgic_abs G).gicd (CONST R))
   /\ (!R. (idgic_abs G').gicd (MUTE R) = if MUTE R = reg then
    					      idGICDupd g (reg, u, v)
    					  else (idgic_abs G).gicd (MUTE R))
   /\ (!R. (VOL R = reg) ==> 
	   ((idgic_abs G').gicd (VOL R) = idGICDupd g (reg, u, v)) )
   /\ ((?R. (MUTE R) = reg) /\ Adr r <> Agicd_sgir ==> 
    	!R. (idgic_abs G').gicd (VOL R) = (idgic_abs G).gicd (VOL R))
   /\ ((idgic_abs G').gicc = (idgic_abs G).gicc)
   /\ ((idgic_abs G').Q = (idgic_abs G).Q)``,
 "gicd_fault" -:
 (* an access to the GICD does not result in a fault if gicd_req_ok holds for
    the corresponding request *)
 ``!G q r G' c g. idgic_step_snd_rpl(G, q, CoreSender c, g, G') 
               /\ Rpl_PAdr q IN RPAR.Amap GICD
	       /\ (r, CoreSender c) IN idgic_req_rcvd G
	       /\ match(r,q)
	       /\ gicd_req_ok r
   ==> 
   ~Frpl q``,
 "snd_rpl_enabled" -:
 (* the GIC may always answer any pending MMIO request *)
 ``!G r id g. (r,id) IN idgic_req_rcvd G  ==>
   ?G' q. idgic_step_snd_rpl(G,q,id,g,G') /\ match(r,q)``,
 "good_rpl" -:
 (* the GIC only sends good replies matching a pending request *) 
 ``!G G' q id g. idgic_step_snd_rpl(G,q,id,g,G') ==>
     (ReqOf q, id) IN idgic_req_rcvd G /\ match(ReqOf q,q)``,
 "snd_fault" -:
 (* the ideal GIC sends a fault reply to a matching MMIO request r if:
    - r did not target the GICC or GICD memory-mapped interfaces, or
    - r was not byte or word sized
 *) 
 ``!G G' r q id g. 
      idgic_step_snd_rpl(G,q,id,g,G') 
   /\ match(r,q)
   /\ (r,id) IN idgic_req_rcvd G
   /\ (PAdr r NOTIN RPAR.Amap GICC \/ PAdr r NOTIN RPAR.Amap GICD \/ 
       SzOf r IN {2;8})
   ==> Frpl q``,
 "rcv_igc" -:
 (* receive IGC notification interrupt for core c on channel s

    pre-conditions:
    - none assumed

    post-conditions:
    - the pending MMIO requests are unchanged
    - the interrupt interface of core c changes for the corresponding peripheral
      interrupt q:
        if q was INACTIVE it becomes PENDING
        if q was ACTIVE it becomes PENDING AND ACTIVE
        otherwise it is unchanged, as the interrupt is already pending
    - for all other interrupts and cores the interrupt interfaces are unchanged
    - the GICC and GICD states are unchanged

    Note that the IGC interrupt bypasses the distributor and is directly
    injected into the interrupt core interface. This reflects the virtualized
    nature of the interrupt, i.e., it is implemented in software by the
    hypervisor using a physical inter-processer interrupt but this fact is
    hidden on the ideal level.

    TODO: define enabled condition (always)
 *)
 ``!G G' s c. idgic_step_rcv_igc (G,s,c,G') ==>
              (idgic_req_rcvd G' = idgic_req_rcvd G)
	   /\ (!q' c'. (idgic_abs G').Q c' q' = 
	    	        if (q' = PIR (PAR.id_igc s)) /\ (c' = c) then
	    		    case (idgic_abs G).Q c q' of
                              | INACTIVE => PENDING 
	    		      | PENDING  => PENDING
	    		      | ACTIVE   => PENDACT
	    		      | PENDACT  => PENDACT 
	    		else (idgic_abs G).Q c' q' )
           /\ ((idgic_abs G).gicc = (idgic_abs G').gicc)
           /\ ((idgic_abs G).gicd = (idgic_abs G').gicd)``
]);



(* Lemma: merging cases and pre-conditions, 
   showing that on GIC reply steps remove the corresponding request *)
val idgic_step_snd_rpl_merged_lem =
     store_thm("idgic_step_snd_rpl_merged_lem",
      ``!G G' q r c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G')
          /\ (r, CoreSender c) IN idgic_req_rcvd G /\ match (r,q)
          /\ (PAdr r IN RPAR.Amap GICC \/  
	      PAdr r IN RPAR.Amap GICD /\ gicd_req_ok r)
         ==>  (idgic_req_rcvd G' = 
	       idgic_req_rcvd G DIFF {(r,CoreSender c)})``,
      RW_TAC (srw_ss()) []
       THEN Cases_on `r`
       THEN Cases_on `q`
       THEN IMP_RES_TAC match_def 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN MAP_EVERY IMP_RES_TAC [idgic_step_axiom // "snd_rpl_gicc", 
				   idgic_step_axiom // "gicd_fault",
                                   idgic_step_axiom // "gicd_read", 
				   idgic_step_axiom // "gicd_write"]
       THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF, Rpl_PAdr_def, PAdr_def, 
				      unique_match_thm,
                                      Rpl_Adr_def, Adr_def, Frpl_def, 
				      gicd_req_ok_def]
       THEN METIS_TAC [unique_match_thm]);

(* Lemma: alternate formulation using DELETE *)
val idgic_step_snd_rpl_merged_lem' =
     store_thm("idgic_step_snd_rpl_merged_lem'",
      ``!G G' q c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G')
          /\ (ReqOf q, CoreSender c) IN idgic_req_rcvd G /\ match (ReqOf q,q)
          /\ (PAdr (ReqOf q) IN RPAR.Amap GICC \/ 
	      PAdr (ReqOf q) IN RPAR.Amap GICD /\ gicd_req_ok (ReqOf q))
         ==>  (idgic_req_rcvd G' = 
	       idgic_req_rcvd G DELETE (ReqOf q,CoreSender c))``,
      METIS_TAC [idgic_step_snd_rpl_merged_lem, matching_request_set_lem, 
		 pred_setTheory.DELETE_DEF]);

(* Lemma: extracting IRQ ids *)
val id_lem_ = blastLib.BBLAST_PROVE 
``((3><0) (((0w:bool[6])@@id):bool[10]) = (id:word4)) /\ 
  ((id <=+ 7w) ==> ((((0w:bool[6])@@id):bool[10]) <=+ 7w))``;

(* Lemma: merged changes to Q due to MMIO requests*)
val idgic_step_snd_rpl_Q_merged_lem =
    store_thm("idgic_step_snd_rpl_Q_merged_lem",
  ``!G G' q c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G')
       /\ (ReqOf q, CoreSender c) IN idgic_req_rcvd G /\ match (ReqOf q,q)
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC \/ 
	   PAdr (ReqOf q) IN RPAR.Amap GICD /\ gicd_req_ok (ReqOf q))
  ==>
     (PAdr (ReqOf q) IN RPAR.Amap GICD  ==> 
	   ((idgic_abs G').Q = (idgic_abs G).Q))
  /\ (PAdr (ReqOf q) IN RPAR.Amap GICC  ==> 
	   (!c'. c <> c' ==> ((idgic_abs G').Q c' = (idgic_abs G).Q c')))
  /\ (PAdr (ReqOf q) IN RPAR.Amap GICC  ==>
         (!irq. (    (?id:bool[4] c'. (irq = SGI (id, c', c)) /\ id <=+ 7w)
                  \/ (?id:bool[10] c'. 
		      (irq = PIR (w2n id)) /\ id >=+ 16w /\ id <+ 1020w) ) ==>
         (((idgic_abs G).Q c irq = INACTIVE) ==> 
		((idgic_abs G').Q c irq = INACTIVE)) /\
         (((idgic_abs G).Q c irq = PENDING) ==> 
		((idgic_abs G').Q c irq IN {PENDING; ACTIVE})) /\
         (((idgic_abs G).Q c irq = ACTIVE) ==> 
		((idgic_abs G').Q c irq IN {ACTIVE; INACTIVE})) /\
         (((idgic_abs G).Q c irq = PENDACT) ==> 
		((idgic_abs G').Q c irq IN {PENDACT; PENDING}))) 
         /\ (!n. (n>7 /\ n<16 \/ n>=1020) ==> 
		 ((idgic_abs G').Q c (PIR n) = INACTIVE)))``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC pure_ss [] >>
  IMP_RES_TAC good_match_lem >>
  IMP_RES_TAC Rpl_PAdr_ReqOf_lem >>
  FULL_SIMP_TAC pure_ss [good_rpl_cases_lem] >>
  MAP_EVERY IMP_RES_TAC [idgic_step_axiom // "snd_rpl_gicc", 
			 idgic_step_axiom // "gicd_fault",
                         idgic_step_axiom // "gicd_read", 
			 idgic_step_axiom // "gicd_write"] >>
  FULL_SIMP_TAC pure_ss [] >>
  REV_FULL_SIMP_TAC std_ss [ReqOf_def, gicAR_disj_EXPAND] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  REV_FULL_SIMP_TAC pure_ss [] >>
  REV_FULL_SIMP_TAC (srw_ss()) [LET_DEF, Frpl_def, gicd_req_ok_def] >>
  ((* applying id_lem_ where needed *)
    ASSUME_TAC id_lem_ >>
    REV_FULL_SIMP_TAC (srw_ss()) [] >>
    RES_TAC >>
    REV_FULL_SIMP_TAC (srw_ss()) [] >>
    SPEC_ASSUM_TAC (``!c'':num. X``, [``c':num``]) >>
    REV_FULL_SIMP_TAC (srw_ss()) []
  ));

(* Lemma: INACTIVE interrupts are never activated at Q via MMIO requests *)
val idgic_step_snd_rpl_Q_inactive_merged_lem =
    store_thm("idgic_step_snd_rpl_Q_inactive_merged_lem",
  ``!G G' q c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G')
       /\ (ReqOf q, CoreSender c) IN idgic_req_rcvd G /\ match (ReqOf q,q)
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC \/ 
	   PAdr (ReqOf q) IN RPAR.Amap GICD /\ gicd_req_ok (ReqOf q))
     ==>
     (!c_ irq. ((idgic_abs G).Q c_ irq = INACTIVE) ==> 
	  ((idgic_abs G').Q c_ irq = INACTIVE))``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC pure_ss [] >>
  IMP_RES_TAC good_match_lem >>
  IMP_RES_TAC Rpl_PAdr_ReqOf_lem >>
  FULL_SIMP_TAC pure_ss [good_rpl_cases_lem] >>
  MAP_EVERY IMP_RES_TAC [idgic_step_axiom // "snd_rpl_gicc", 
			 idgic_step_axiom // "gicd_fault",
                         idgic_step_axiom // "gicd_read", 
			 idgic_step_axiom // "gicd_write"] >>
  FULL_SIMP_TAC pure_ss [] >>
  REV_FULL_SIMP_TAC std_ss [ReqOf_def, gicAR_disj_EXPAND] >>
  REV_FULL_SIMP_TAC (srw_ss()) [LET_DEF, Frpl_def, gicd_req_ok_def] );

(* Lemma: peripheral interrupts never become PENDACT at Q via MMIO requests *)
val idgic_step_snd_rpl_Q_pendact_merged_lem =
    store_thm("idgic_step_snd_rpl_Q_pendact_merged_lem",
  ``!G G' q c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G')
       /\ (ReqOf q, CoreSender c) IN idgic_req_rcvd G /\ match (ReqOf q,q)
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC \/ 
	   PAdr (ReqOf q) IN RPAR.Amap GICD /\ gicd_req_ok (ReqOf q))
     ==>
     (!c_ n. (PIR n IN PIRQ g) /\ ((idgic_abs G).Q c_ (PIR n) <> PENDACT) ==> 
				  ((idgic_abs G').Q c_ (PIR n) <> PENDACT))``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC pure_ss [] >>
  IMP_RES_TAC good_match_lem >>
  IMP_RES_TAC Rpl_PAdr_ReqOf_lem >>
  FULL_SIMP_TAC pure_ss [good_rpl_cases_lem] >>
  MAP_EVERY IMP_RES_TAC [idgic_step_axiom // "snd_rpl_gicc", 
			 idgic_step_axiom // "gicd_fault",
                         idgic_step_axiom // "gicd_read", 
			 idgic_step_axiom // "gicd_write"] >>
  FULL_SIMP_TAC pure_ss [] >>
  REV_FULL_SIMP_TAC std_ss [ReqOf_def, gicAR_disj_EXPAND] >>
  REV_FULL_SIMP_TAC (srw_ss()) [LET_DEF, Frpl_def, gicd_req_ok_def] >>
  METIS_TAC [] );

(* Lemma: golden mask config of GICD is preserved by MMIO accesses *)
val idgic_step_snd_rpl_PI_merged_lem = store_thm(
   "idgic_step_snd_rpl_PI_merged_lem",
   ``!G G' q c g. idgic_step_snd_rpl (G,q,CoreSender c,g,G')
       /\ (ReqOf q, CoreSender c) IN idgic_req_rcvd G /\ match (ReqOf q,q)
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC \/ 
	   PAdr (ReqOf q) IN RPAR.Amap GICD /\ gicd_req_ok (ReqOf q))
    ==> idgic_gm_conf g (idgic_abs G).gicd
    ==> idgic_gm_conf g (idgic_abs G').gicd``,
  REPEAT GEN_TAC >>
  REPEAT DISCH_TAC >>
  FULL_SIMP_TAC pure_ss [] >>
  IMP_RES_TAC good_match_lem >>
  IMP_RES_TAC Rpl_PAdr_ReqOf_lem >|
  [(*GICC*)
   IMP_RES_TAC (idgic_step_axiom // "snd_rpl_gicc") >>
   REV_FULL_SIMP_TAC (srw_ss()) [PI_def, idgic_gm_conf_def] >>
   REPEAT STRIP_TAC >>
   REPEAT CASE_TAC,
   (*GICD*)
   FULL_SIMP_TAC pure_ss [good_rpl_cases_lem] >>
   MAP_EVERY IMP_RES_TAC [idgic_step_axiom // "gicd_fault", 
                          idgic_step_axiom // "gicd_read",
                          idgic_step_axiom // "gicd_write"] >>
   FULL_SIMP_TAC pure_ss [] >>
   REV_FULL_SIMP_TAC (srw_ss()) [ReqOf_def,  LET_DEF, Frpl_def, 
				 gicd_req_ok_def] >>
   METIS_TAC [someIdGICDupds_axiom]]);

(* generalization: OK accesses to GICC and GICD *)
val GICC_GICD_OK_def = Define `GICC_GICD_OK req =
       PAdr req IN RPAR.Amap GICC \/
      (PAdr req IN RPAR.Amap GICD /\ gicd_req_ok req)`;

(* Lemma: merged effects of MMIO accesses to the ideal GIC *)
val idgic_step_snd_rpl_fully_merged_lem_ = store_thm(
   "idgic_step_snd_rpl_fully_merged_lem_",
   ``!G G' q c g. 
        idgic_step_snd_rpl (G,q,CoreSender c,g,G')
    ==> match (ReqOf q,q)
    ==> (ReqOf q, CoreSender c) IN idgic_req_rcvd G
    ==> GICC_GICD_OK (ReqOf q)
    ==>   (idgic_gm_conf g (idgic_abs G).gicd ==> 
			 idgic_gm_conf g (idgic_abs G').gicd)
       /\ (idgic_req_rcvd G' = idgic_req_rcvd G DELETE (ReqOf q,CoreSender c))
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICD  ==> 
		((idgic_abs G').Q = (idgic_abs G).Q))
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC  ==> 
		(!c'. c <> c' ==> ((idgic_abs G').Q c' = (idgic_abs G).Q c')))
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC  ==>
            (!irq. (    (?id:bool[4] c'. (irq = SGI (id, c', c)) /\ id <=+ 7w)
                     \/ (?id:bool[10] c'. 
			 (irq = PIR (w2n id)) /\ id >=+ 16w /\ id <+ 1020w)) ==>
            (((idgic_abs G).Q c irq = INACTIVE) ==> 
			((idgic_abs G').Q c irq = INACTIVE)) /\
            (((idgic_abs G).Q c irq = PENDING) ==> 
			((idgic_abs G').Q c irq IN {PENDING; ACTIVE})) /\
            (((idgic_abs G).Q c irq = ACTIVE) ==> 
			((idgic_abs G').Q c irq IN {ACTIVE; INACTIVE})) /\
            (((idgic_abs G).Q c irq = PENDACT) ==> 
			((idgic_abs G').Q c irq IN {PENDACT; PENDING}))) 
            /\ (!n. (n>7 /\ n<16 \/ n>=1020) ==> 
		    ((idgic_abs G').Q c (PIR n) = INACTIVE)))``,
   METIS_TAC [idgic_step_snd_rpl_merged_lem', idgic_step_snd_rpl_Q_merged_lem, 
	      idgic_step_snd_rpl_PI_merged_lem, GICC_GICD_OK_def]);
  
(* Lemma: merged effects of MMIO accesses to the ideal GIC, 
          removed assumptions *)
val idgic_step_snd_rpl_fully_merged_lem = store_thm(
   "idgic_step_snd_rpl_fully_merged_lem",
   ``!G G' q c g. 
        idgic_step_snd_rpl (G,q,CoreSender c,g,G')
    ==> GICC_GICD_OK (ReqOf q)
    ==>   (idgic_gm_conf g (idgic_abs G).gicd ==> 
			 idgic_gm_conf g (idgic_abs G').gicd)
       /\ (idgic_req_rcvd G' = idgic_req_rcvd G DELETE (ReqOf q,CoreSender c))
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICD  ==> 
		((idgic_abs G').Q = (idgic_abs G).Q))
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC  ==> 
		(!c'. c <> c' ==> ((idgic_abs G').Q c' = (idgic_abs G).Q c')))
       /\ (PAdr (ReqOf q) IN RPAR.Amap GICC  ==>
            (!irq. (    (?id:bool[4] c'. (irq = SGI (id, c', c)) /\ id <=+ 7w)
                     \/ (?id:bool[10] c'. 
			 (irq = PIR (w2n id)) /\ id >=+ 16w /\ id <+ 1020w)) ==>
            (((idgic_abs G).Q c irq = INACTIVE) ==> 
			((idgic_abs G').Q c irq = INACTIVE)) /\
            (((idgic_abs G).Q c irq = PENDING) ==> 
			((idgic_abs G').Q c irq IN {PENDING; ACTIVE})) /\
            (((idgic_abs G).Q c irq = ACTIVE) ==> 
			((idgic_abs G').Q c irq IN {ACTIVE; INACTIVE})) /\
            (((idgic_abs G).Q c irq = PENDACT) ==> 
			((idgic_abs G').Q c irq IN {PENDACT; PENDING}))) 
            /\ (!n. (n>7 /\ n<16 \/ n>=1020) ==> 
		    ((idgic_abs G').Q c (PIR n) = INACTIVE)))``,
   METIS_TAC [idgic_step_snd_rpl_fully_merged_lem_, 
	      idgic_step_axiom // "good_rpl"]);
  
(* Lemma: merged guarantees for interrupt state *)
val idgic_step_snd_rpl_inv_merged_lem = store_thm(
   "idgic_step_snd_rpl_inv_merged_lem",
   ``!G G' q c g. 
        idgic_step_snd_rpl (G,q,CoreSender c,g,G')
    ==> GICC_GICD_OK (ReqOf q)
    ==>   (idgic_gm_conf g (idgic_abs G).gicd ==> 
			 idgic_gm_conf g (idgic_abs G').gicd)
       /\ (idgic_req_rcvd G' = idgic_req_rcvd G DELETE (ReqOf q,CoreSender c))
       /\ (!c_ irq. ((idgic_abs G).Q c_ irq = INACTIVE) ==> 
	       ((idgic_abs G').Q c_ irq = INACTIVE))
       /\ (!c_ n. (PIR n IN PIRQ g) /\ 
		  ((idgic_abs G).Q c_ (PIR n) <> PENDACT) ==> 
		  ((idgic_abs G').Q c_ (PIR n) <> PENDACT))``,
   METIS_TAC [idgic_step_snd_rpl_merged_lem', GICC_GICD_OK_def,
              idgic_step_snd_rpl_Q_inactive_merged_lem, 
	      idgic_step_snd_rpl_Q_pendact_merged_lem,
              idgic_step_snd_rpl_PI_merged_lem, 
	      idgic_step_axiom // "good_rpl"]);
  
(* Lemma: merged properties of distribution step *)
val idgic_step_dist_irq_inv_merged_lem = store_thm(
   "idgic_step_dist_irq_inv_merged_lem",
   ``idgic_step_dist_irq (G,q,c,g,G') ==>
     (idgic_req_rcvd G' = idgic_req_rcvd G) /\
     (idgic_gm_conf g (idgic_abs G).gicd ==> 
		    idgic_gm_conf g (idgic_abs G').gicd) /\
     (!c_ irq. (c_ <> c \/ irq <> q) ==> 
	  ((idgic_abs G').Q c_ irq = (idgic_abs G).Q c_ irq)) /\
     (!id. (q = PIR id) ==> idgic_gm_conf g (idgic_abs G).gicd ==> 
	   (PIR id) IN (xPIRQ g)) /\
     (!id c_. (q = PIR id) ==> 
	  (idgic_abs G).Q c_ q <> PENDACT ==> 
		(idgic_abs G').Q c_ q <> PENDACT) /\
     (!id. (q = PIR id) ==> id >= 16 /\ id < 1020) /\
     (!id c' c''. (q = SGI (id,c',c'')) ==>  
	  id <=+ 7w /\ (c'' = c) /\ c' < PAR.nc_g g)``,
    DISCH_TAC >>
    IMP_RES_TAC (idgic_step_axiom // "dist_irq") >>
    REPEAT STRIP_TAC >|
    [(* req_rcvd: trivial *)
     ASM_SIMP_TAC std_ss [],
     (* PI invariant *)
     FULL_SIMP_TAC (srw_ss()) [idgic_gm_conf_def, PI_def] >>
     (REPEAT CASE_TAC) >>
     METIS_TAC [irqID_11, in_PIRQ_lem, guest_irq_def, PIstate_distinct],
     (* Q for other cores *)
     REV_FULL_SIMP_TAC (srw_ss()) [],
     (* Q for other interrupts *)
     REV_FULL_SIMP_TAC (srw_ss()) [],
     (* xPIRQ *)
     FULL_SIMP_TAC (srw_ss()) [PI_def] >>
     METIS_TAC [guest_irq_PIRQ_xPIRQ_lem, asserted_guest_irq_lem],
     (* PENDACT *)
     Cases_on `c_ = c` >>
     REV_FULL_SIMP_TAC std_ss [] >>
     FULL_SIMP_TAC (srw_ss()) [],
     (* all other subgoals trivial *)
     REV_FULL_SIMP_TAC (srw_ss()) [],
     REV_FULL_SIMP_TAC (srw_ss()) [],
     REV_FULL_SIMP_TAC (srw_ss()) [],
     REV_FULL_SIMP_TAC (srw_ss()) [],
     REV_FULL_SIMP_TAC (srw_ss()) []
    ]);


(* Lemma: merged guarantees of distributor step, focus on interrupt state *)
val idgic_step_dist_irq_inv_merged_lem2 = store_thm(
   "idgic_step_dist_irq_inv_merged_lem2",
   ``idgic_step_dist_irq (G,q,c,g,G') ==>
     (idgic_req_rcvd G' = idgic_req_rcvd G) /\
     (idgic_gm_conf g (idgic_abs G).gicd ==> 
		    idgic_gm_conf g (idgic_abs G').gicd) /\
     (!c_ irq. (c_ <> c \/ irq <> q) ==> 
	  ((idgic_abs G').Q c_ irq = (idgic_abs G).Q c_ irq)) /\
     ((?id. (q = PIR id) /\
      (idgic_gm_conf g (idgic_abs G).gicd ==> (PIR id) IN (xPIRQ g)) /\
      (!c_. (idgic_abs G).Q c_ q <> PENDACT ==> 
		(idgic_abs G').Q c_ q <> PENDACT) /\
      (id >= 16) /\ 
      (id < 1020))
      \/
      (?id c'. (q = SGI (id,c',c)) /\ id <=+ 7w /\ c' < PAR.nc_g g))``,
    DISCH_TAC >>
    IMP_RES_TAC idgic_step_dist_irq_inv_merged_lem >>
    NTAC 2 (RW_TAC (srw_ss()) []) >>
    Cases_on `q` >|
    [(* SGI *)
      rename1 `SGI triple` >>
      Cases_on `triple` >>
      rename1 `SGI (id, tuple)` >>
      Cases_on `tuple` >>
      METIS_TAC [],
     (* PI *)
      METIS_TAC []]);



(******************** REFINED MODEL **********************)

(*** refined core abstractions ***)

(* EL2 and EL3 special purpose registers, 
   for use of hypervisor / boot loader only *)

(* reset vector base address register *)
new_constant("RVBAR_EL3", ``:SPRhyp``);
(* secure mode control register *)
new_constant("SCR_EL3", ``:SPRhyp``);
(* EL3 interrupt vector base register *)
new_constant("VBAR_EL3", ``:SPRhyp``);
(* EL2 interrupt vector base register *)
new_constant("VBAR_EL2", ``:SPRhyp``);
(* hypervisor control register *)
new_constant("HCR_EL2", ``:SPRhyp``);
(* EL2 exception status register *) 
new_constant("ESR_EL2", ``:SPRhyp``);
(* EL2 exception link register *) 
new_constant("ELR_EL2", ``:SPRhyp``);
(* EL2 saved processor status register *) 
new_constant("SPSR_EL2", ``:SPRhyp``);
(* EL2 hypervisor intermediate physical fault address register,
   for stage 2 guest exceptions *) 
new_constant("HPFAR_EL2", ``:SPRhyp``);
(* EL2 virtual fault address register *) 
new_constant("FAR_EL2", ``:SPRhyp``);

(* all registers are unique *)
val exception_hyp_regs_axiom = new_axiom("exception_hyp_regs_axiom", ``
    ELR_EL2 <> ESR_EL2 /\ ELR_EL2 <> HPFAR_EL2 /\ ELR_EL2 <> SPSR_EL2
 /\ ESR_EL2 <> HPFAR_EL2 /\ ESR_EL2 <> SPSR_EL2 /\ HPFAR_EL2 <> SPSR_EL2
 /\ ELR_EL2 <> FAR_EL2 /\ ESR_EL2 <> FAR_EL2 /\ HPFAR_EL2 <> FAR_EL2
 /\ FAR_EL2 <> SPSR_EL2
 /\ VBAR_EL2 <> ELR_EL2 /\ VBAR_EL2 <> ESR_EL2 /\ VBAR_EL2 <> HPFAR_EL2 
 /\ VBAR_EL2 <> SPSR_EL2 /\ VBAR_EL2 <> FAR_EL2
``);

(* refined core abstraction function *)
new_constant("refcore_abs", ``:(refcore -> refcore_config)``);

(* exception level of refined core *)
val Mode_def = Define `Mode (c:refcore) = MODE((refcore_abs(c)).PSTATE)`;

(* Lemma: exception level of refined core at most EL3 *)
val Mode_bound_lem = store_thm("Mode_bound_lem", ``
!C. Mode C <= 3
``,
  RW_TAC std_ss [Mode_def, MODE_bound_lem]
);


(* internal pipeline state abstraction, we require it to be flushed:
  - before and after recieve interrupt step 
  - after SMC/HVC step 
  - after receive fault step
  - after internal step (if requests EMPTY)
  
  Since the abstract FLUSHED state signifies a unique internal state, we can use
  it to couple the internal state of refined and ideal cores after a hypervisor
  intervention, essentially forcing both cores to have the same internal state.
*)
new_constant("refcore_int", ``:(refcore -> core_internal_state)``);
val ref_abs_int_def = Define `ref_abs_int C = cis_abs ( refcore_int C)`;

(* outstanding memory requests of the refined core,
   that have not been answered yet *)
new_constant("refcore_req_sent", ``:(refcore -> request set)``);

(* refcore_upd(C,AC,RS) = C'
 
   function updating a refined core C to C' such that its abstract state becomes
   AC and its outstand ing request set becomes RS

   semantics defined in hypervisorScript to account for update of history
   variables. The updated core has a FLUSHED internal state.
*)
new_constant("refcore_upd", ``:refcore # refcore_config # request set -> refcore``);

(*** MMU abstraction functions ***)

new_constant("mmu_abs", ``:(mmu -> mmu_config)``);
(* pending requests (sent / received) and memory replies *)
new_constant("mmu_req_rcvd", ``:(mmu -> request set)``);
new_constant("mmu_req_sent", ``:(mmu -> request set)``);
new_constant("mmu_rpl_rcvd", ``:(mmu -> reply set)``);
(* history of all previous page table lookups *)
new_constant("mmu_ptl_hist", ``:(mmu -> reply set)``);


(* page table origin / base address for stage 2 page table,
   extracted from MMU configuration *)
new_constant("PTO", ``:(MMUcfg -> bool[64])``);

(* mmu_upd (MMU,cfg) = MMU'
  
   updates configuration of MMU with cfg
*) 
new_constant("mmu_upd", ``:mmu # mmu_config -> mmu``);

(* Axiom: update semantics, only cfg updated *)
val mmu_upd_axiom = new_axiom("mmu_upd_axiom", ``
!MMU U MMU'. (MMU' = mmu_upd (MMU,U)) ==>
              (mmu_abs MMU' = U)
	   /\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU)
	   /\ (mmu_req_sent MMU' = mmu_req_sent MMU)
	   /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
	   /\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
``);

(*** memory abstraction ***)

(* received/pending requests, incl DMA requests from peripherals *)
new_constant("mem_req_rcvd", ``:(memory -> (request # senderID) set)``);
(* pending memory mapped IO requests that were forwarded to peripherals *)
new_constant("mem_req_sent", ``:(memory -> (request # senderID) set)``);
(* received memory mapped IO replies from peripherals, 
   to be forwarded to cores *)
new_constant("mem_rpl_rcvd", ``:(memory -> (reply # senderID) set)``);

(* memory abstraction function,

   We model memory as a flat map of addresses to pages, ignoring any underlying
   storage archtictecture and hierarchy. This model is sound if the underlying
   memory is coherent and multicopy-atomic, i.e., all observers have the same
   view of memory contents and see updates at the same "time". The latter is (as
   of late) guaranteed for ARM processors. Memory coherency can be broken by
   guest software, e.g., through the use of mismatched cacheability attributes,
   misconfigured shareability attributes for shared memory, or rowhammer
   attacks. We do not consider these attacks on this level of abstraction.

   See Nemati et al, "Formal Verification of Integrity-Preserving
   Countermeasures against Cache Storage Side-Channels", POST 2018 for a
   methodology to combat these attack vectors for a given instantiation.
*)
new_constant("mem_abs", ``:(memory -> (bool[36] -> PAGE))``);

(*** GIC abstraction ***)

(* pending memory mapped IO requests to the GIC *)
new_constant("gic_req_rcvd", ``:(gic -> (request # senderID) set)``);
(* GIC abstraction function *)
new_constant("gic_abs", ``:(gic -> gic_config)``);

(* abstract IRQ state in the distributor
   
   The distributor largely determines the state of interrupt signals in the
   system. This state may be read by a core through the distributor register
   interface. In order to abstract from the registers we introduce the irqstate
   abstraction function that maps each interrupt ID to its current interrupt
   state.
*)
new_constant("irqstate", ``:(GICDreg -> bool[32]) -> (irqID -> IRQstate)``);

(* Axiom: the interrupt state only depends on volatile GICD registers *)
val irqstate_axiom = new_axiom("irqstate_axiom", ``
!gicd gicd'.
(!R. gicd (VOL R) = gicd' (VOL R)) <=> (irqstate gicd = irqstate gicd')
``);

(* virqstate(gich,c)

   the virtual interupt state for core c, as extracted from the list registers
   in the virtual interrupt control interface, modeled as a mapping from
   interrupt ID to interrupt state.

   The list register bits 29 and 28 encode the ACTIVE and PENDING state
   respectively. Note that there is at most one matching LR for each virq, as
   noted earlier (see virqlrs_def).
*)
val virqstate_def = Define `virqstate (gich: GICHreg -> bool[32], c) = 
\q. if (?IRQ. virqlrs(gich,q,c) = {IRQ}) then
	let lr = gich (gich_lr (CHOICE (virqlrs(gich,q,c)))) in
	case (lr ' 29, lr ' 28) of
	  | (F,F) => INACTIVE
	  | (F,T) => PENDING
	  | (T,F) => ACTIVE
	  | (T,T) => PENDACT
    else INACTIVE	
`;

(* shorthands for interrupt and virtual interupt state,
   Note that VI will be mapped to Q in the ideal model. 
   Similarly Q should match PI for interrupts belonging to its guest 
*) 
val Q_def = Define `Q (G:gic) = irqstate ((gic_abs G).gicd)`;
val VI_def = Define `VI (G:gic) c = virqstate ((gic_abs G).gich c, c)`;

(* GICD register filter, and write conversion functions 

   These functions are introduced to abstract from the filtering of guest
   requests to the GIC distributor that has to be implemented by the hypervisor
   to virtualize the GICD.

   GICDfltr(g,r,v) = v'

   is used for describing the effect of read filtering, i.e., v' is the result
   of applying filtering for guest g on the value v of GICD register r.
   Intutitively, the filter should set all bits in v to default values for
   interrupts that do no belong to g, effectively marking them as INACTIVE.

   GICDwconv(g,r,v) = v'
   
   is used for converting writes to the GICD in such a way that they do not
   modify the configuration of interrupts that do not belong to guest g. As many
   registers in the GICD are written using bit enabling or disabling masks, the
   filter would just set those bits in the value v of the write request to zero
   which should not be altered. Therefore the original value of the register is
   not needed to determine the new value v' for the write to register r.
*)
new_constant("GICDfltr", ``:num # GICDreg # bool[32] -> bool[32]``);
new_constant("GICDwconv", ``:num # GICDreg # bool[32] -> bool[32]``);

(* Axiom: no read filtering is applied for invalid GICD registers *)
val fail_gicd_fltr_axiom = new_axiom("fail_gicd_fltr_axiom", ``
!g r v w. (!B. fail_gicd(r,B,w)) ==> (GICDfltr(g,r,v) = v)
``);

(* Axiom: the filtered result needs no more filtering, i.e., subsequent
   application of the read filter leaves the read value unchanged
*)
val gicdfltr_fixpoint_axiom = new_axiom("gicdfltr_fixpoint_axiom", ``
!g r v v'. (GICDfltr(g,r,v) = v') ==>
(GICDfltr(g,r,v') = v')
``);

(* Axiom: the write conversion is perfect/instantaneous, i.e., converting an
   already converted write value again, has no effect
*)
val gicdwconv_fixpoint_axiom = new_axiom("gicdwconv_fixpoint_axiom", ``
!g r v v'. (GICDwconv(g,r,v) = v') ==>
(GICDwconv(g,r,v') = v')
``);

(* mapping the effects of read filtering to the ideal interrupt state 

   for a given read filter function and mapping of refined to ideal interrupts,
   the predicate states that if all volatile registers are filtered in a GICD
   state then the corresponding ideal interrupt state for a given guest match
   the refined interrupts, and all other interrupts are NOT_ASSERTED.

   The mapping of interprocessor interrupts (SGIs) takes into acount the special
   treatment by the hypervisor which deactivates ACTIVE SGIs in the ideal
   distributor when they are forwarded to the virtual interrupt interface.
*)
val gicdfltr_pqq_coupling_def = Define `
gicdfltr_pqq_coupling(gicdfltr, pqq) = 
!g gicd gicd' q. (!r. gicd' (VOL r) = gicdfltr(g,VOL r,gicd (VOL r))) ==>
((pistate gicd') (pqq g q) = 
    if (pqq g q) IN PIRQ g UNION IPIRQ g then 
	case (irqstate gicd) q of
          | INACTIVE => NOT_ASSERTED
	  | PENDING  => ASSERTED
	  | ACTIVE   => if pqq g q IN IPIRQ g then NOT_ASSERTED 
			else FORWARDED 
	  | PENDACT  => if pqq g q IN IPIRQ g then ASSERTED 
			else ASS_FWD
    else NOT_ASSERTED )
`;

(* good SGI receiver projections 

   prq g q maps an interrupt q to the corresponding virtual interrupt ID within
   guest g. The only change occurs for SGIs in which cases receiver core ID is
   adapted to the numbering within the guest. We say such a projection is good
   if this mapping reflects the number of cores in the guest.
*)
val good_prq_def = Define `good_prq prq =
   (!g id s c s' c'. c < RPAR.nc /\ g < PAR.ng /\ 
		     (prq g (SGI (id, s, c)) = SGI (id, s', c')) 
		         ==> 
                     c' < PAR.nc_g g /\ (s' = s))
/\ (!g q. prq g (PIR q) = PIR q)
`;

(* good SGI sender projections 

   psq g q is similar to prq g q only that it adapts the sender ID instead of
   the receiver ID.
*)
val good_psq_def = Define `good_psq psq =
   (!g id s c s' c'. s < RPAR.nc /\ g < PAR.ng /\ 
		     (psq g (SGI (id, s, c)) = SGI (id, s', c')) 
		         ==> 
                     s' < PAR.nc_g g /\ (c' = c))
/\ (!g q. psq g (PIR q) = PIR q)
`;


(* GIC registers *)

(* interrupt acknowledgement register *)
val _ = new_constant("Agicc_aiar", ``:bool[48]``);
(* end of interrupt interrupt register *)
val _ = new_constant("Agicc_aeoir", ``:bool[48]``);
(* deactivate interrupt register *)
val _ = new_constant("Agicc_dir", ``:bool[48]``);

(* mapping of each interrupt to dedicated list register address *)
val _ = new_constant("Agich_lr", ``:irqID -> bool[48]``);

(* Axioms on GIC registers:
   - the first three are GIC registers
   - list registers are allocated in the virtual interrupt control interface
   - interrupts of guest g that need to be allocated in different list registers,
     are in fact assigned different list register addresses
*)
val Agicch_axiom = new_axiom("Agicch_axiom", ``
   (47><12) Agicc_aiar IN RPAR.Amap GICC
/\ (47><12) Agicc_aeoir IN RPAR.Amap GICC
/\ (47><12) Agicc_dir IN RPAR.Amap GICC
/\ (!q. (47><12) (Agich_lr q) IN RPAR.Amap GICH)
/\ (!g q q'. disj_lr_irq(q,q',g) ==> Agich_lr q <> Agich_lr q')
``);

(* Axiom: SGI request register is allocated in GICD area *)
val Agicd_axiom = new_axiom("Agicd_axiom", ``
((47><12)Agicd_sgir) IN (RPAR.Amap GICD)
``);


(*** peripheral model ***)

(* pending memory mapped IO requests from cores *)
new_constant("per_req_rcvd", ``:(peripheral -> request set)``);
(* pending DMA requests *)
new_constant("per_req_sent", ``:(peripheral -> request set)``);
(* peripheral reset state
   TODO: this should be defined per peripheral
 *)
new_constant("per_reset", ``:peripheral``);
(* flag recording whether peripheral is active/running *)
new_constant("per_active", ``:(peripheral -> bool)``);

(* Axiom: after reset no IO or DMA requests are pending *)
val per_reset_axiom = new_axiom("per_reset_axiom",
    ``   (per_req_sent per_reset = EMPTY)
      /\ (per_req_rcvd per_reset = EMPTY)``);


(* axiomatized memory update. page granularity

   memory_upd (a,v) m = m' 

   updates memory m to m' where the page with address a is set to content v
*)
val _ = new_constant("memory_upd", ``:bool[36] # PAGE -> memory -> memory``);

(* Axiom: abstract memory update semantics
   - the request and reply sets are unchanged
   - page a is updated with value v
   - all other memory contents are unchanged
*)
val memory_upd_axiom = new_axiom("memory_upd_axiom", ``
	!m a v m'. (m' = memory_upd (a,v) m) ==>
		   (mem_req_rcvd m' = mem_req_rcvd m)
		/\ (mem_req_sent m' = mem_req_sent m)
		/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
		/\ ((mem_abs m') a = v)
		/\ (!a'. (a' <> a) ==> ((mem_abs m') a' = (mem_abs m) a'))
``);

(* Axiom: updating a page with itself does not affect the memory *)
val memory_id_upd_axiom = new_axiom("memory_id_upd_axiom", ``
!m a. memory_upd (a, mem_abs m a) m = m
``);

(* Lemma: the abstraction reflects the update of a page *)
val memory_upd_mem_abs_id_lem = store_thm("memory_upd_mem_abs_id_lem", ``
!m pg a. mem_abs (memory_upd (a, pg) m) a = pg
``,
  METIS_TAC [memory_upd_axiom]
);


(* update with whole set of addresses and a reference memory abstraction *)
val _ = new_constant("memory_set_upd", 
``:bool[36] set # (bool[36] -> PAGE) -> memory -> memory``);

(* Axiom: the memory update has the expected semantics:
   - the request and reply sets are unchanged
   - page a in a is updated with value V(a)
   - all other memory contents (outside A) are unchanged
 *)
val memory_set_upd_axiom = new_axiom("memory_set_upd_axiom", ``
	!m A V m'. (m' = memory_set_upd (A,V) m) ==>
		   (mem_req_rcvd m' = mem_req_rcvd m)
		/\ (mem_req_sent m' = mem_req_sent m)
		/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
		/\ (!a. a IN A ==> ((mem_abs m') a = V a))
		/\ (!a. a NOTIN A ==> ((mem_abs m') a = (mem_abs m) a))
``);


(**************** Core steps *****************)

(**** uninterpreted model of refined core steps ****)
(* transition relations, stepping from refined core state C to C'

   refcore_step_rcv_phys(C,C') - receive physical interrupt
   refcore_step_rcv_virt(C,C') - receive virtual interrupt
   refcore_step_rcv_rpl(C,q,C') - receive memory reply q
   refcore_step_rcv_psci(C,x,C') - receive PSCI command x
   refcore_step_snd_req(C,r,C') - receive memory request r
   refcore_step_internal(C,C') - internal step, e.g., arithmetic operation
*)
val _ = new_constant("refcore_step_rcv_phys", 
		     ``:refcore # refcore -> bool``);
val _ = new_constant("refcore_step_rcv_virt", 
		     ``:refcore # refcore -> bool``);
val _ = new_constant("refcore_step_rcv_rpl", 
		     ``:refcore # reply # refcore -> bool``);
val _ = new_constant("refcore_step_rcv_psci", 
		     ``:refcore # event # refcore -> bool``);
val _ = new_constant("refcore_step_snd_req", 
		     ``:refcore # request # refcore -> bool``);
val _ = new_constant("refcore_step_internal", 
		     ``:refcore # refcore -> bool``);

(* refcore_step(C,a,C') - refined core transition relation

   the following actions a are defined:
   
   RCV (PHYS NONE c) - receive physical interrupt at core c,
       the first argument of the action is only used in the ideal GIC distributor
   RCV (VIRT c) - receive virtual interrupt at core c
   RCV (MRPL r) - receive memory reply r from the MMU
   RCV (PSCI e) - receive power controll command e, i.e., StartCore / StopCore
   SEND (MREQ r) - send memory request r to the MMU
   TAU - perform internal step

   the relation does not hold for any other actions
*)
val refcore_step_def = Define `refcore_step (C : refcore, a : Action, C' : refcore) =
	case a of
	  | RCV (PHYS NONE c)  => refcore_step_rcv_phys(C,C')
	  | RCV (VIRT c)  => refcore_step_rcv_virt(C,C')
          | RCV (MRPL r) => refcore_step_rcv_rpl(C,r,C')
          | RCV (PSCI e) => refcore_step_rcv_psci(C,e,C')
          | SEND (MREQ r) => refcore_step_snd_req(C,r,C')
          | TAU => refcore_step_internal(C,C')
          | _   => F
`;

val refcore_gicd_rrpl_def = Define `refcore_gicd_rrpl (C:refcore_config) r R = 
C with <| PC := C.PC + 4w; GPR := (R =+ Rpl_val r) C.GPR |>
`;

val refcore_gicd_wrpl_def = Define `refcore_gicd_wrpl (C:refcore_config) r R = 
C with <| PC := C.PC + 4w |>
`;

(* assume sequential core here for simplification, needed? *)
val inv_good_refcore_def = Define `inv_good_refcore (C:refcore) = 
    CARD(refcore_req_sent C) <= 1 /\ FINITE (refcore_req_sent C)
 /\ ((~(refcore_abs C).active) ==> (refcore_req_sent C = EMPTY))
 /\ ((ref_abs_int C = FLUSHED) ==> (refcore_req_sent C = EMPTY))
 /\ ((?R. ref_abs_int C = GICD_RS R) <=> 
	 (?r. Rreq r /\ PAdr r IN RPAR.Amap GICD /\ r IN refcore_req_sent C
             /\ ~gicd_acc_not_supported (MsgOf r)) )
 /\ ((ref_abs_int C = GICD_RNS) <=> 
	 (?r. Rreq r /\ PAdr r IN RPAR.Amap GICD /\ r IN refcore_req_sent C
             /\ gicd_acc_not_supported (MsgOf r)) )
 /\ ((?R. (ref_abs_int C = GICD_WS R)) <=> 
	 (?r. Wreq r /\ PAdr r IN RPAR.Amap GICD /\ r IN refcore_req_sent C
             /\ ~gicd_acc_not_supported (MsgOf r)) )
 /\ ((ref_abs_int C = GICD_WNS) <=> 
	 (?r. Wreq r /\ PAdr r IN RPAR.Amap GICD /\ r IN refcore_req_sent C
             /\ gicd_acc_not_supported (MsgOf r)) )
`;

val inv_good_refcore_axiom = new_axiom("inv_good_refcore_axiom", ``
!C a C'. inv_good_refcore C /\ refcore_step(C,a,C') ==> inv_good_refcore C'
``);

(* two-state invariants on core behaviour *)
(* NOTE: we only ever use these function in EL1/0, thus simplified *)

(* history semantics *)
val refcore_send_axiom = new_axiom("refcore_send_axiom", ``
!C r C'. refcore_step_snd_req(C,r,C') ==>
   (refcore_abs C).active /\ (refcore_abs C').active
(* only one request at a time, needs to be adapted for more advanced core *)
/\ (refcore_req_sent C = EMPTY)
/\ (refcore_req_sent C' = refcore_req_sent C UNION {r})
/\ ((refcore_abs C).H = (refcore_abs C').H)
/\ (Mode C' = Mode C)
/\ (ref_abs_int C' = next_int_snd (refcore_int C) r)
``);

val refcore_rcv_rpl_axiom = new_axiom("refcore_rcv_rpl_axiom", ``
!C q C'. refcore_step_rcv_rpl(C,q,C')
==>
?r.
   r IN refcore_req_sent C /\ match(r,q)    
/\ (refcore_abs C).active /\ (refcore_abs C').active
/\ (refcore_req_sent C' = refcore_req_sent C DIFF {r})
/\ ((refcore_abs C').H = (refcore_abs C).H)
/\ (~Frpl q /\ Mode C < 2 ==> Mode C' < 2)
/\ (case ref_abs_int C of
      | GICD_RS R => 
            (refcore_abs C' = refcore_gicd_rrpl (refcore_abs C) q R)
         /\ (ref_abs_int C' = FLUSHED)
      | GICD_WS R => 
            (refcore_abs C' = refcore_gicd_wrpl (refcore_abs C) q R)
	 /\ (ref_abs_int C' = FLUSHED)
      | _ =>  (ref_abs_int C' IN {OTHER; FLUSHED}))
``);



val refcore_rcv_fault_axiom = new_axiom("refcore_rcv_fault_axiom", ``
!C q C' r fi. refcore_step_rcv_rpl(C,q,C') /\ (q = Fault r fi) 
           /\ Mode C < 2 /\ ~st2_fault q 
==>
    ((refcore_abs C').PC = (refcore_abs C).SPR(INL VBAR_EL1) + 
			   ghoff(w2w (refcore_abs C).PSTATE)) 
 /\ ((refcore_abs C').PSTATE = MODE_upd((refcore_abs C).PSTATE, 1))
 /\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
 /\ (!R. if R=INL ELR_EL1 then 
	     (refcore_abs C').SPR R = (refcore_abs C).PC
	 else if R=INL ESR_EL1 then 
	     (refcore_abs C').SPR R = w2w (
	         extract_ESR_EL1 (refcore_int C, 
				  r, 
				  fi, 
				  (refcore_abs C).PSTATE) )
	 else if R=INL FAR_EL1 then 
	     (refcore_abs C').SPR R = w2w (extract_FAR fi)
	 else if R=INL SPSR_EL1 then 
	     (refcore_abs C').SPR R = w2w ((refcore_abs C).PSTATE)
	 else (refcore_abs C').SPR R  = (refcore_abs C).SPR R )
 /\ (refcore_req_sent C' = EMPTY)
 /\ (ref_abs_int C' = FLUSHED)
 /\ ((refcore_abs C').H = (refcore_abs C).H)
``);

val refcore_internal_axiom = new_axiom("refcore_internal_axiom", ``
!C C'. refcore_step_internal(C,C') ==>
   (refcore_abs C).active /\ (refcore_abs C').active
/\ (refcore_req_sent C' = refcore_req_sent C)
/\ (refcore_req_sent C = EMPTY) 
(* /\ (ref_abs_int C' = FLUSHED) *)
/\ (ref_abs_int C IN {OTHER; FLUSHED} ==> ref_abs_int C' IN {OTHER; FLUSHED})
/\ (ref_abs_int C NOTIN {OTHER; FLUSHED} ==> (ref_abs_int C' = ref_abs_int C))
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);

(* TODO: the mode restriction should be part of the axiom above *)
val refcore_internal_enabled_axiom = 
new_axiom("refcore_internal_enabled_axiom", ``
!C. (refcore_abs C).active /\ Mode C < 2 /\ (refcore_req_sent C = EMPTY) 
    ==> 
?C'. refcore_step_internal(C,C') /\ (Mode C' = Mode C)
``);


(* psci semantics *)

val refcore_psci_start_axiom = new_axiom("refcore_psci_start_axiom", ``
!C c C'. refcore_step_rcv_psci(C,StartCore c, C') ==>
   (if (refcore_abs C).active then (C' = C)
    else if Mode C < 2 then soft (refcore_abs C') else warm (refcore_abs C'))
/\ ((refcore_abs C').SPR = (refcore_abs C).SPR)
/\ (refcore_req_sent C = EMPTY)
/\ (refcore_req_sent C' = EMPTY)
/\ (ref_abs_int C' = FLUSHED)
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);

val refcore_psci_stop_axiom = new_axiom("refcore_psci_stop_axiom", ``
!C c C'. refcore_step_rcv_psci(C,StopCore c, C') ==>
    if ~(refcore_abs C).active then (C' = C)
    else ((refcore_abs C').active = F) 
      /\ ((refcore_abs C').PC = (refcore_abs C).PC)
      /\ ((refcore_abs C').PSTATE = (refcore_abs C).PSTATE)
      /\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
      /\ ((refcore_abs C').SPR = (refcore_abs C).SPR)
      /\ (refcore_req_sent C = EMPTY)
      /\ (refcore_req_sent C' = EMPTY)
      /\ ((refcore_abs C').H = (refcore_abs C).H)
      /\ (ref_abs_int C' = FLUSHED)
``);


(* interrupt and exception semantics *)

val haspoc_exc_conf_def = Define `haspoc_exc_conf (C : refcore) =
   ((refcore_abs C).SPR(INR SCR_EL3) = 0b10100000001w:bool[64])
/\ (    ((refcore_abs C).SPR(INR HCR_EL2) = 0x800F803Fw) 
     \/ ((refcore_abs C).SPR(INR HCR_EL2) = 0x800F80BFw) )
`;

val refcore_fault_axiom = new_axiom("refcore_fault_axiom", ``
!C R fi C'. refcore_step_rcv_rpl(C, Fault R fi, C')
        /\ haspoc_exc_conf C /\ fi_st2 fi
        /\ (R IN refcore_req_sent C)
==>
   (refcore_abs C).active /\ (refcore_abs C').active 
/\ ((refcore_abs C').PC = (refcore_abs C).SPR(INR VBAR_EL2) + 0x400w) 
/\ ((refcore_abs C').PSTATE = MODE_upd((refcore_abs C).PSTATE, 2))
/\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
/\ (!r. 
if r=INR ELR_EL2 then (refcore_abs C').SPR r = (refcore_abs C).PC
else if r=INR ESR_EL2 then (refcore_abs C').SPR r = w2w (extract_ESR (refcore_int C, R, fi))
else if r=INR FAR_EL2 then (refcore_abs C').SPR r = w2w (extract_FAR fi)
else if r=INR HPFAR_EL2 then (refcore_abs C').SPR r = 
			         w2w ( (PAdr R @@ (0b0000w:bool[4])) :bool[40])
else if r=INR SPSR_EL2 then (refcore_abs C').SPR r = w2w ((refcore_abs C).PSTATE)
else (refcore_abs C').SPR r  = (refcore_abs C).SPR r 
)
/\ (refcore_req_sent C' = EMPTY)
/\ (ref_abs_int C' = FLUSHED)
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);



val refcore_phys_irq_axiom = new_axiom("refcore_phys_irq_axiom", ``
!C C'. refcore_step_rcv_phys(C, C')
        /\ haspoc_exc_conf C
==>
   (refcore_abs C).active /\ (refcore_abs C').active
/\ ((refcore_abs C').PC = (refcore_abs C).SPR(INR VBAR_EL2) + 0x480w) 
/\ ((refcore_abs C').PSTATE = MODE_upd((refcore_abs C).PSTATE, 2))
/\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
/\ (!r.
if r=INR ELR_EL2 then (refcore_abs C').SPR r = (refcore_abs C).PC
else if r=INL ISR_EL1 then (refcore_abs C').SPR r = 0x80w
else if r=INR SPSR_EL2 then (refcore_abs C').SPR r = w2w ((refcore_abs C).PSTATE)
else (refcore_abs C').SPR r  = (refcore_abs C).SPR r 
)
/\ (refcore_req_sent C = EMPTY)
/\ (refcore_req_sent C' = EMPTY)
/\ (ref_abs_int C = FLUSHED)
/\ ~word_bit 7 (refcore_abs C).PSTATE
/\ (ref_abs_int C' = FLUSHED)
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);

val refcore_virt_irq_axiom = new_axiom("refcore_virt_irq_axiom", ``
!C q C'. refcore_step_rcv_virt(C, C')
        /\ haspoc_exc_conf C
==>
   (refcore_abs C).active /\ (refcore_abs C').active
/\ ((refcore_abs C').PC = (refcore_abs C).SPR(INL VBAR_EL1) + 
                          async_ghoff(w2w (refcore_abs C).PSTATE)) 
/\ ((refcore_abs C').PSTATE = MODE_upd((refcore_abs C).PSTATE, 1))
/\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
/\ (!r.
if r=INL ELR_EL1 then (refcore_abs C').SPR r = (refcore_abs C).PC
else if r=INL ISR_EL1 then (refcore_abs C').SPR r = 0x80w
else if r=INL SPSR_EL1 then (refcore_abs C').SPR r = w2w ((refcore_abs C).PSTATE)
else (refcore_abs C').SPR r  = (refcore_abs C).SPR r 
)
/\ (refcore_req_sent C = EMPTY)
/\ (refcore_req_sent C' = EMPTY)
/\ (ref_abs_int C = FLUSHED)
/\ ~word_bit 7 (refcore_abs C).PSTATE
/\ (ref_abs_int C' = FLUSHED)
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);

(* next instructions will perform HVC or SMC *)
val _ = new_constant("HVC_next", ``:refcore # bool[16] -> bool``);
val _ = new_constant("SMC_next", ``:refcore # bool[16] -> bool``);

val refcore_HVC_next_axiom = new_axiom("refcore_HVC_next_axiom", ``
!C v. HVC_next(C,v) ==> (refcore_req_sent C = EMPTY) /\ (refcore_abs C).active
``);

val refcore_SMC_next_axiom = new_axiom("refcore_SMC_next_axiom", ``
!C v. SMC_next(C,v) ==> (refcore_req_sent C = EMPTY) /\ (refcore_abs C).active
``);

val refcore_hvc_axiom = new_axiom("refcore_hvc_axiom", ``
!C v C'. refcore_step_internal(C, C')
        /\ haspoc_exc_conf C
	/\ HVC_next(C,v) /\ (Mode C = 1)
==>
   (refcore_abs C).active /\ (refcore_abs C').active
/\ ((refcore_abs C').PC = (refcore_abs C).SPR(INR VBAR_EL2) + 0x400w) 
/\ ((refcore_abs C').PSTATE = MODE_upd((refcore_abs C).PSTATE, 2))
/\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
/\ (!r. 
if r=INR ELR_EL2 then (refcore_abs C').SPR r = (refcore_abs C).PC + 4w
else if r=INR ESR_EL2 then (refcore_abs C').SPR r = 0x5800w:bool[16] @@ v 
else if r=INR SPSR_EL2 then (refcore_abs C').SPR r = w2w ((refcore_abs C).PSTATE)
else (refcore_abs C').SPR r  = (refcore_abs C).SPR r 
)
/\ (refcore_req_sent C' = EMPTY)
/\ (ref_abs_int C' = FLUSHED)
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);

val refcore_smc_axiom = new_axiom("refcore_smc_axiom", ``
!C v C'. refcore_step_internal(C, C')
        /\ haspoc_exc_conf C
	/\ SMC_next(C, v) /\ (Mode C = 1)
==>
   (refcore_abs C).active /\ (refcore_abs C').active
/\ ((refcore_abs C').PC = (refcore_abs C).SPR(INR VBAR_EL2) + 0x400w) 
/\ ((refcore_abs C').PSTATE = MODE_upd((refcore_abs C).PSTATE, 2))
/\ ((refcore_abs C').GPR = (refcore_abs C).GPR)
/\ (!r. 
if r=INR ELR_EL2 then (refcore_abs C').SPR r = (refcore_abs C).PC + 4w
else if r=INR ESR_EL2 then (refcore_abs C').SPR r = 0x5C00w:bool[16] @@ v 
else if r=INR SPSR_EL2 then (refcore_abs C').SPR r = w2w ((refcore_abs C).PSTATE)
else (refcore_abs C').SPR r  = (refcore_abs C).SPR r 
)
/\ (refcore_req_sent C' = EMPTY)
/\ (ref_abs_int C' = FLUSHED)
/\ ((refcore_abs C').H = (refcore_abs C).H)
``);

(* mode change restrictions to >EL1 *)

(* only 
-- hvc and smc internal steps
-- physical interrupts
-- psci start when inactive 
-- received fault replies
may change mode to EL>1
*)

val refcore_mode_change_axiom = new_axiom("refcore_mode_change_axiom", ``
!C a C'. refcore_step(C, a, C') /\ haspoc_exc_conf C /\ Mode C < 2 ==> 
( Mode C' > 1
       <=> 
  (  (a = TAU) /\ (?v. HVC_next(C,v) \/ SMC_next(C,v)) /\ (Mode C = 1) 
  \/ (?c. a = RCV (PHYS NONE c))
  \/ (?c. (a = RCV (PSCI (StartCore c))) /\ ~(refcore_abs C).active)
  \/ (?r q. (a = RCV (MRPL q)) /\ Frpl q /\ match(r,q) 
         /\ r IN (refcore_req_sent C) ) ) 
)
``);

(* liveness / enabled axioms *)

(* only receive irq in mode EL<2, if no requests pending and ~PSTATE.I (bit 7) *)
val refcore_irq_enabled_axiom = new_axiom("refcore_irq_enabled_axiom", ``
!C. haspoc_exc_conf C 
 /\ Mode C <= 1 
 /\ (refcore_req_sent C = EMPTY)
 /\ ~word_bit 7 (refcore_abs C).PSTATE
 /\ (ref_abs_int C = FLUSHED)
 /\ (refcore_abs C).active
==> 
(?C'. refcore_step_rcv_phys(C,C')) /\ (?C'. refcore_step_rcv_virt(C,C'))
``);

(* only receive replies if matching request *)
val refcore_rcv_rpl_enabled_axiom = new_axiom("refcore_rcv_rpl_enabled_axiom", ``
!C q. Mode C <= 1 /\ (?r. r IN refcore_req_sent C /\ match(r,q))  
   /\ (refcore_abs C).active
==> 
?C'. refcore_step_rcv_rpl(C,q,C')
``);

(* onl
y receive power events in while there are no requests outstanding *)
val refcore_psci_enabled_axiom = new_axiom("refcore_psci_enabled_axiom", ``
!C e. ((refcore_req_sent C = EMPTY) \/ ~(refcore_abs C).active)
==> 
?C'. refcore_step_rcv_psci(C,e,C')
``);

(* sending and internal steps may be enabled or not, 
we just need to schedule them if the ideal mode performs them as well *) 

(* TODO: core step bisimulation axioms (with the ideal model),
sending and internal steps to be existentially quantified, need both directions
*)

val core_send_refined_bisim_axiom = new_axiom("core_send_refined_bisim_axiom", ``
!IC RC RC' r.
   ((idcore_abs IC).PC = (refcore_abs RC).PC)
/\ ((idcore_abs IC).PSTATE = (refcore_abs RC).PSTATE)
/\ ((idcore_abs IC).GPR = (refcore_abs RC).GPR)
/\ (!R. (idcore_abs IC).SPR R = (refcore_abs RC).SPR (INL R))
/\ (idcore_int IC = refcore_int RC) 
/\ (idcore_req_sent IC = EMPTY) 
/\ (refcore_req_sent RC = EMPTY) 
/\ Mode RC < 2
/\ iMode IC < 2
/\ refcore_step_snd_req(RC,r,RC')
==>
?IC'. idcore_step_snd_req(IC,r,IC')
   /\ ((idcore_abs IC').PC = (refcore_abs RC').PC)
   /\ ((idcore_abs IC').PSTATE = (refcore_abs RC').PSTATE)
   /\ ((idcore_abs IC').GPR = (refcore_abs RC').GPR)
   /\ (!R. (idcore_abs IC').SPR R = (refcore_abs RC').SPR (INL R))
   /\ (idcore_int IC' = refcore_int RC') 
``);
       
val core_send_ideal_bisim_axiom = new_axiom("core_send_ideal_bisim_axiom", ``
!RC IC IC' r.
   ((idcore_abs IC).PC = (refcore_abs RC).PC)
/\ ((idcore_abs IC).PSTATE = (refcore_abs RC).PSTATE)
/\ ((idcore_abs IC).GPR = (refcore_abs RC).GPR)
/\ (!R. (idcore_abs IC).SPR R = (refcore_abs RC).SPR (INL R))
/\ (idcore_int IC = refcore_int RC) 
/\ (idcore_req_sent IC = EMPTY) 
/\ (refcore_req_sent RC = EMPTY) 
/\ Mode RC < 2
/\ iMode IC < 2
/\ idcore_step_snd_req(IC,r,IC')
==>
?RC'. refcore_step_snd_req(RC,r,RC')
   /\ ((idcore_abs IC').PC = (refcore_abs RC').PC)
   /\ ((idcore_abs IC').PSTATE = (refcore_abs RC').PSTATE)
   /\ ((idcore_abs IC').GPR = (refcore_abs RC').GPR)
   /\ (!R. (idcore_abs IC').SPR R = (refcore_abs RC').SPR (INL R))
   /\ (idcore_int IC' = refcore_int RC') 
``);


val core_rcv_rpl_bisim_axiom = new_axiom("core_rcv_rpl_bisim_axiom", ``
!RC RC' IC IC' r.
   ((idcore_abs IC).active = (refcore_abs RC).active)
/\ ((idcore_abs IC).PC = (refcore_abs RC).PC)
/\ ((idcore_abs IC).PSTATE = (refcore_abs RC).PSTATE)
/\ ((idcore_abs IC).GPR = (refcore_abs RC).GPR)
/\ (!R. (idcore_abs IC).SPR R = (refcore_abs RC).SPR (INL R))
/\ (idcore_int IC = refcore_int RC) 
/\ (idcore_req_sent IC = refcore_req_sent RC) 
/\ ((ReqOf r) IN idcore_req_sent IC) 
/\ ((ReqOf r) IN refcore_req_sent RC) 
/\ Mode RC < 2
/\ iMode IC < 2
/\ iMode IC' < 2 
/\ Mode RC' < 2
/\ idcore_step_rcv_rpl(IC,r,IC')
/\ refcore_step_rcv_rpl(RC,r,RC')
/\ ~Frpl r
==>
      ((idcore_abs IC').PC = (refcore_abs RC').PC)
   /\ ((idcore_abs IC').PSTATE = (refcore_abs RC').PSTATE)
   /\ ((idcore_abs IC').GPR = (refcore_abs RC').GPR)
   /\ (!R. (idcore_abs IC').SPR R = (refcore_abs RC').SPR (INL R))
   /\ (idcore_int IC' = refcore_int RC') 
``);

val core_internal_bisim_axiom = new_axiom("core_internal_bisim_axiom", ``
!RC RC' IC IC'.
   ((idcore_abs IC).active = (refcore_abs RC).active)
/\ ((idcore_abs IC).PC = (refcore_abs RC).PC)
/\ ((idcore_abs IC).PSTATE = (refcore_abs RC).PSTATE)
/\ ((idcore_abs IC).GPR = (refcore_abs RC).GPR)
/\ (!R. (idcore_abs IC).SPR R = (refcore_abs RC).SPR (INL R))
/\ (idcore_int IC = refcore_int RC) 
/\ (idcore_req_sent IC = refcore_req_sent RC) 
/\ Mode RC < 2
/\ iMode IC < 2
/\ iMode IC' < 2 
/\ Mode RC' < 2
/\ idcore_step_internal(IC,IC')
/\ refcore_step_internal(RC,RC')
==>
      ((idcore_abs IC').PC = (refcore_abs RC').PC)
   /\ ((idcore_abs IC').PSTATE = (refcore_abs RC').PSTATE)
   /\ ((idcore_abs IC').GPR = (refcore_abs RC').GPR)
   /\ (!R. (idcore_abs IC').SPR R = (refcore_abs RC').SPR (INL R))
   /\ (idcore_int IC' = refcore_int RC') 
``);



(***************** PSCI steps ******************)

(* definition of the simplified power controller semantics, 

   as all power control is handled by the hypervisor, a simple model for use in
   both the ideal and refined model is sufficient *)

(* psciev c e - e is a PSCI command for core c *)
val psciev_def = Define `
   (psciev c' (StartCore c) = (c = c'))
/\ (psciev c' (StopCore c) = (c = c'))
/\ (psciev c' _ = F)
`;

(* psci_step_rcv_elist(PS,l,PS')

   transition of the power controller from state PS to PS' when receiving a list
   of PSCI commands l

   preconditions:
   none required

   postconditions:
   -  the commands for core c are appended to its list of outstanding commands
*)
val psci_step_rcv_elist_def = Define `
psci_step_rcv_elist (PS : psci_state, l: event list, PS' : psci_state) =
(PS' = PS with <| events := \c. PS.events c ++ FILTER (psciev c) l|>)
`;


(* psci_step_snd_event(PS,e,c,PS')

   transition of the power controller from state PS to PS' when sending a
   command e to core c

   preconditions:
   - e is a command at head of the queue of outstanding commands for core c
   - e is a PSCI command event (not an SGI signal)

   postconditions:
   -  the command e is popped from the queue for core c
   -  the local power state record is updated according to e
*)
val psci_step_snd_event_def = Define `
psci_step_snd_event (PS : psci_state, e: event, c:num, PS' : psci_state) =
(HD (PS.events c) = e) /\ (PS.events c <> []) /\ 
(!c'. e <> SndIgc c') /\ 
(PS'.events = (c =+ TL (PS.events c)) PS.events) /\
(PS'.pow = case e of
	       | StopCore c => (c =+ F) PS.pow
	       | StartCore c => (c =+ T) PS.pow
	       | _ => PS.pow)
`;

(* transitions of the power controller for core c

   RCV (PSCIL l) - receive list of power commands
   SEND (PSCI e) - send next outstanding command to given core c
*)
val psci_step_def = Define `psci_step (PS : psci_state, a : Action, c:num, PS' : psci_state) = 
	case a of
	  | RCV (PSCIL l)  => psci_step_rcv_elist(PS,l,PS')
          | SEND (PSCI e) => psci_step_snd_event(PS,e,c:num,PS')
          | _   => F
`;

(**************** MMU steps *****************)

val _ = new_constant("mmu_step_rcv_rpl", ``:mmu # reply # mmu -> bool``);
val _ = new_constant("mmu_step_rcv_req", ``:mmu # request # mmu -> bool``);
val _ = new_constant("mmu_step_snd_req", ``:mmu # request # mmu -> bool``);
val _ = new_constant("mmu_step_snd_rpl", ``:mmu # reply # mmu -> bool``);
val _ = new_constant("mmu_step_internal", ``:mmu # mmu -> bool``);

val mmu_step_def = Define `mmu_step (MMU : mmu, a : Action, MMU' : mmu) =
	case a of
          | RCV (SRPL r id) => mmu_step_rcv_rpl(MMU,r,MMU')
          | RCV (MREQ r) => mmu_step_rcv_req(MMU,r,MMU')
          | SEND (SREQ r id) => mmu_step_snd_req(MMU,r,MMU')
          | SEND (MRPL r) => mmu_step_snd_rpl(MMU,r,MMU')
          | TAU => mmu_step_internal(MMU,MMU')
          | _   => F
`;

(* MMU invariants:
- rcvd requests iff request state not IDLE
- requests sent exactly translation or final requests
- translation requests only PTWs
- inactive ==> no translating requests
- all sent requests aligned
*)

val padr_aligned_def = Define `padr_aligned (a:bool[48], d:num) =
case d of
  | 1 => T
  | 2 => word_bit 0 a = F
  | 4 => ((1><0) a:bool[2]) = 0w
  | 8 => ((2><0) a:bool[3]) = 0w
  | _ => F
`;		

val aligned_bx_lem = store_thm("aligned_bx_lem", ``
!a a' d. (((11 >< 0) a):bool[12] = (11 >< 0) a')
==>
(padr_aligned (a, d) <=> padr_aligned (a', d))
``,
  REPEAT STRIP_TAC >> 
  RW_TAC (srw_ss()) [padr_aligned_def] 
  >| [(* false case *)
      FULL_SIMP_TAC arith_ss []
      ,
      (* case: 2 *)
      FULL_SIMP_TAC arith_ss [GSYM wordsTheory.WORD_EQ] >>
      `0 < dimindex (:12)` by ( EVAL_TAC ) >>
      `word_bit 0 (((11 >< 0) a):bool[12]) = 
       word_bit 0 (((11 >< 0) a'):bool[12])` by ( RES_TAC ) >>
      FULL_SIMP_TAC arith_ss [wordsTheory.word_extract_def, 
			      wordsTheory.word_bits_def,
			      wordsTheory.word_bit_def] >>
      FULL_SIMP_TAC (srw_ss()) [wordsTheory.w2w] >>
      FULL_SIMP_TAC (srw_ss()) [fcpTheory.FCP_BETA]
      ,
      (* case: 4 *)
      `(1 >< 0) (((11 >< 0) a):bool[12]) :bool[2] = 
       (1 >< 0) (((11 >< 0) a'):bool[12])` by (
          FULL_SIMP_TAC (srw_ss()) []
      ) >>
      FULL_SIMP_TAC (srw_ss()) [wordsTheory.WORD_EXTRACT_COMP_THM]
      ,
      (* case: 1 and 8 *)
      Cases_on `d=1` >> ( RW_TAC (srw_ss()) [] ) >>
      Cases_on `d=8` >> ( RW_TAC (srw_ss()) [] ) >>
      `(2 >< 0) (((11 >< 0) a):bool[12]) :bool[3] = 
       (2 >< 0) (((11 >< 0) a'):bool[12])` by (
          FULL_SIMP_TAC (srw_ss()) []
      ) >>
      FULL_SIMP_TAC (srw_ss()) [wordsTheory.WORD_EXTRACT_COMP_THM]
     ]
);


val req_aligned_def = Define `req_aligned (r:request) =
case r of
  | Read a d i => padr_aligned (a, d)
  | Write a d v i => padr_aligned (a, d)
  | Walk a i => padr_aligned (a, 8)
`;			   

val req_aligned_lem = store_thm("req_aligned_lem", ``
!r. req_aligned r = padr_aligned (Adr r, SzOf r)
``,
  Cases >> (
      RW_TAC (srw_ss()) [req_aligned_def, Adr_def, SzOf_def]
  )
);			   


val match_trans_def = Define `match_trans (MMU:mmu) (r:request, q:reply) =
?r'. ((mmu_abs MMU).state r = TRANS (SOME r')) /\ match(r',q)
`;		

val match_final_def = Define `match_final (MMU:mmu) (r:request, q:reply) =
?r'. ((mmu_abs MMU).state r = FINAL (SOME r')) /\ match(r',q)
`;		

   
val inv_good_mmu_def = Define `inv_good_mmu (MMU:mmu) = 
   (!r. r IN mmu_req_rcvd(MMU) <=> (mmu_abs MMU).state r <> IDLE)
/\ (!l. l IN mmu_req_sent(MMU) ==> 
	(?r. ((mmu_abs MMU).state r = TRANS (SOME l)) /\ (mmu_abs MMU).active 
	  \/ ((mmu_abs MMU).state r = FINAL (SOME l)) /\ 
	         (if (mmu_abs MMU).active then xlated(r,l) else (r=l)) ) )
/\ (!q. q IN mmu_rpl_rcvd MMU ==> ?r. match_trans MMU (r,q) 
				   \/ match_final MMU (r,q))
/\ (!l r. (mmu_abs MMU).state r IN {TRANS (SOME l); FINAL (SOME l)} ==>
          (l IN mmu_req_sent MMU \/ ?q. q IN mmu_rpl_rcvd MMU /\ match(l,q)) )
/\ (!r l. ((mmu_abs MMU).state r = TRANS (SOME l)) ==> PTreq l)
/\ ((?r l. (((mmu_abs MMU).state r = TRANS l) \/ 
            ((mmu_abs MMU).state r = FAULT))) ==> (mmu_abs MMU).active)
/\ (!r r' l l'. (mmu_abs MMU).state r IN {TRANS (SOME l); FINAL (SOME l)}
             /\ (mmu_abs MMU).state r' IN {TRANS (SOME l'); FINAL (SOME l')}
	    ==> r <> r' ==> l <> l' )
/\ (!r. r IN mmu_req_sent(MMU) ==> req_aligned(r))
/\ (!r. r IN mmu_req_sent(MMU) ==> ~(?q. q IN mmu_rpl_rcvd MMU /\ match(r,q)))
/\ (!q. q IN mmu_ptl_hist(MMU) ==> ?r v. q = WalkResult r v)
`;

val inv_good_mmu_axiom = new_axiom("inv_good_mmu_axiom", ``
!MMU a MMU'. inv_good_mmu MMU /\ mmu_step(MMU,a,MMU') ==> inv_good_mmu MMU'
``);

(* two-state invariants:
- PT lookups always aligned
- final lookups always aligned (?, core should break them down) 
- only reply to actual requests, send received memory reply
- history semantics
- if configured as golden image, then only send requests to GI
- if only ever received lookups from GI, then only send final requests to A_G
- GI configured mmu returns faults for requests outside of A_G
*)

val mmu_send_axiom = new_axiom("mmu_send_axiom", ``
!MMU r MMU'. mmu_step_snd_req(MMU,r,MMU') ==>
   req_aligned r
/\ (mmu_req_sent MMU' = mmu_req_sent MMU UNION {r})
/\ r NOTIN mmu_req_sent MMU
/\ (?r'. (   ((mmu_abs MMU').state r' = FINAL (SOME r)) 
	      /\ (if (mmu_abs MMU).active then xlated(r',r) else (r'=r))
	      /\ ((mmu_abs MMU).state r' = FINAL NONE) 
	  \/ ((mmu_abs MMU').state r' = TRANS (SOME r)) 
	      /\ ((mmu_abs MMU).state r' = TRANS NONE) )
    /\ !r''. r' <> r'' ==> ((mmu_abs MMU').state r'' = (mmu_abs MMU).state r'') 
                        /\ (mmu_abs MMU).state r'' <> TRANS (SOME r)
                        /\ (mmu_abs MMU).state r'' <> FINAL (SOME r) )
/\ (!r'. ((mmu_abs MMU').state r' = TRANS (SOME r)) ==> PTreq r)
/\ (!q. q IN mmu_rpl_rcvd MMU ==> ~match(r,q))
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU)
/\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)
``);			 

val _ = new_constant("compute_fault", ``:mmu # request -> reply``);
val compute_fault_axiom = new_axiom("compute_fault_axiom", ``
!MMU r q. (q = compute_fault(MMU,r)) /\ ((mmu_abs MMU).state r = FAULT) ==>
   Frpl q /\ match(r,q) /\ st2_fault q
``);

val mmu_reply_axiom = new_axiom("mmu_reply_axiom", ``
!MMU q MMU'. mmu_step_snd_rpl(MMU,q,MMU') ==>
?r. 
   match(r,q)
/\ (   (?q' l. ((mmu_abs MMU).state r = FINAL (SOME l))
            /\ q' IN mmu_rpl_rcvd MMU /\ match(l,q')
            /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU DIFF {q'})
            /\ (xlated_rpl(q,q'))
	    /\ ~st2_fault q) 
    \/ ((mmu_abs MMU).state r = FAULT) 
       /\ (q = compute_fault(MMU,r))
       /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU))
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU DIFF {r})
/\ ((mmu_abs MMU').state r = IDLE)
/\ (!r'. r <> r' ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r') )
/\ (mmu_req_sent MMU' = mmu_req_sent MMU)
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)
``);			 


val mmu_reply_lem = store_thm("mmu_reply_lem", ``
!MMU q MMU'. mmu_step_snd_rpl(MMU,q,MMU') ==> 
   match(ReqOf q, q)
/\ (   (?q'. ((mmu_abs MMU).state (ReqOf q) = FINAL (SOME (ReqOf q')))
            /\ q' IN mmu_rpl_rcvd MMU /\ match(ReqOf q', q')
            /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU DIFF {q'})
            /\ (xlated_rpl(q,q'))
            /\ (Frpl q ==> Frpl q') 
	    /\ ~st2_fault q)
    \/ ((mmu_abs MMU).state (ReqOf q) = FAULT) 
       /\ (q = compute_fault(MMU,(ReqOf q)))
       /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
       /\ Frpl q)
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU DIFF {ReqOf q})
/\ ((mmu_abs MMU').state (ReqOf q) = IDLE)
/\ (!r'. r' <> (ReqOf q) ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r') )
/\ (mmu_req_sent MMU' = mmu_req_sent MMU)
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)``,
METIS_TAC [match_ReqOf_lem, unique_match_thm, ReqOf_def, mmu_reply_axiom, compute_fault_axiom, xlated_rpl_Frpl_lem]);			 



val mmu_reply_fault_lem = store_thm("mmu_reply_fault_lem", ``
!MMU q MMU'. mmu_step_snd_rpl(MMU,q,MMU') ==> Frpl q ==> 
   match(ReqOf q, q)
/\ (   (?q'. ((mmu_abs MMU).state (ReqOf q) = FINAL (SOME (ReqOf q')))
            /\ q' IN mmu_rpl_rcvd MMU /\ match(ReqOf q', q')
            /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU DIFF {q'})
            /\ (xlated_rpl(q,q'))
            /\ Frpl q') 
    \/ ((mmu_abs MMU).state (ReqOf q) = FAULT) 
       /\ (q = compute_fault(MMU,(ReqOf q)))
       /\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU))
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU DIFF {ReqOf q})
/\ ((mmu_abs MMU').state (ReqOf q) = IDLE)
/\ (!r'. r' <> (ReqOf q) ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r') )
/\ (mmu_req_sent MMU' = mmu_req_sent MMU)
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)``,
METIS_TAC [match_ReqOf_lem, unique_match_thm, ReqOf_def, mmu_reply_axiom, compute_fault_axiom, xlated_rpl_Frpl_lem]);			 




val mmu_memrpl_axiom = new_axiom("mmu_memrpl_axiom", ``
!MMU q MMU'. mmu_step_rcv_rpl(MMU,q,MMU') ==>
   (if ?r. match_final MMU (r,q) then
        (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU UNION {q})
     /\ (mmu_req_sent MMU' = mmu_req_sent MMU DIFF {r' | ?r. ((mmu_abs MMU).state r = FINAL (SOME r')) /\ match(r',q)})
     /\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
     /\ ((mmu_abs MMU').state = (mmu_abs MMU).state)
    else 
        (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
     /\ (mmu_req_sent MMU' = mmu_req_sent MMU DIFF {r' | ?r. ((mmu_abs MMU).state r = TRANS (SOME r')) /\ match(r',q)})
     /\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU UNION {q})
     /\ (!r. match_trans MMU (r,q) ==>
	    (mmu_abs MMU').state r IN {TRANS NONE; FINAL NONE; FAULT} )
     /\ (!r. ~match_trans MMU (r,q) ==> 
	    ((mmu_abs MMU').state r = (mmu_abs MMU).state r) )
   )
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)
``);			 

val mmu_corereq_axiom = new_axiom("mmu_corereq_axiom", ``
!MMU r MMU'. mmu_step_rcv_req(MMU,r,MMU') ==>
   (if (mmu_abs MMU).active then
        (mmu_abs MMU').state r IN {TRANS NONE; FAULT}
    else
        (mmu_abs MMU').state r IN {FINAL NONE; FAULT}
   )
/\ (!r'. r <> r' ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r'))
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU UNION {r})
/\ (r NOTIN mmu_req_rcvd MMU)
/\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
/\ (mmu_req_sent MMU' = mmu_req_sent MMU)
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)
``);			 

val mmu_internal_axiom = new_axiom("mmu_internal_axiom", ``
!MMU MMU'. mmu_step_internal(MMU,MMU') ==>
   (mmu_abs MMU' = mmu_abs MMU)
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU)
/\ (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
/\ (mmu_req_sent MMU' = mmu_req_sent MMU)
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
``);			 

val golden_rpl_def = Define `golden_rpl (PT,GI) q = 
   Rpl_PAdr q IN PT
/\ (Rpl_val q :bool[64] = mem_read GI (Rpl_Adr q) (Rpl_SzOf q))
`;

val mmu_golden_conf_def = Define `mmu_golden_conf (MMU : mmu, GI, cfg, PT, RO, tr) =
   golden (GI, cfg, PT, RO, tr) 
/\ ((mmu_abs MMU).active)
/\ ((mmu_abs MMU).cfg = cfg)
/\ (!q. q IN mmu_ptl_hist MMU ==> golden_rpl (PT,GI) q)
`;
    
(* only send requests to golden page table *)
val mmu_golden_lookup_axiom = new_axiom("mmu_golden_lookup_axiom", ``
!MMU r MMU' GI cfg PT RO tr r'.
   mmu_golden_conf (MMU, GI, cfg, PT, RO, tr) 
/\ mmu_step_snd_req(MMU,r,MMU') 
/\ ((mmu_abs MMU').state r' = TRANS (SOME r)) ==>
	 PTreq r /\ PAdr r IN PT

``);			 

(* only send final accesses to mapped region *)
val mmu_golden_final_axiom = new_axiom("mmu_golden_final_axiom", ``
!MMU r MMU' GI cfg PT RO tr r'.
   mmu_golden_conf (MMU, GI, cfg, PT, RO, tr) 
/\ mmu_step_snd_req(MMU,r,MMU') 
/\ ((mmu_abs MMU').state r' = FINAL (SOME r)) ==>
	 IS_SOME(tr (PAdr r')) 
      /\ (Adr r = (THE (tr (PAdr r'))) @@ (11><0)(Adr r'):bool[12])
      /\ (PAdr r' IN RO ==> ~Wreq r')
``);			 

(* faulting addresses are outside of guest memory or writes to RO region *)
val mmu_golden_fault_axiom = new_axiom("mmu_golden_fault_axiom", ``
!MMU a MMU' GI cfg PT RO tr r.
   mmu_golden_conf (MMU, GI, cfg, PT, RO, tr) 
/\ mmu_step(MMU,a,MMU') 
/\ (mmu_abs MMU).state r <> FAULT
/\ ((mmu_abs MMU').state r = FAULT) 
==>
((tr (PAdr r) = NONE) \/ PAdr r IN RO /\ Wreq r)
``);			 

(* no translation faults, fault info contains requested address *)
val mmu_golden_fault_FAR_axiom = new_axiom("mmu_golden_fault_FAR_axiom", ``
!MMU q MMU' GI cfg PT RO tr r fi.
   mmu_golden_conf (MMU, GI, cfg, PT, RO, tr) 
/\ mmu_step_snd_rpl(MMU,q,MMU') 
/\ (q = Fault r fi)
==>
((11 >< 0) (extract_FAR fi) = (11 >< 0) (Adr r) :bool[12]) /\
(fi = golden_fi (GI, cfg, PT, RO) r)
``);


(* 
- if disabled, accesses to the GIC never faults
- if disabled, final state reached directly
TODO: need other conditions on request than alignment?
*)
val mmu_gicreq_axiom = new_axiom("mmu_gicreq_axiom", ``
!MMU r MMU'. mmu_step_rcv_req(MMU,r,MMU') 
          /\ ~(mmu_abs MMU).active
          /\ (?A. gicAR A /\ PAdr r IN RPAR.Amap A) 
	  /\ req_aligned r
==>
   ((mmu_abs MMU').state r = FINAL NONE)
``);			 

(*
- liveness properties:
-- always able to receive new request
-- always able to receive matching memory reply
-- golden translation will eventually yield final state or fault
-- from final state final request can be sent
-- from fault state faulting reply can be sent
-- final result can always be forwarded
*)

val mmu_rcv_req_enabled_axiom = new_axiom("mmu_rcv_req_enabled_axiom", ``
!MMU r. r NOTIN mmu_req_rcvd MMU ==> ?MMU'. mmu_step_rcv_req(MMU,r,MMU')
``);

val mmu_rcv_rpl_enabled_axiom = new_axiom("mmu_rcv_rpl_enabled_axiom", ``
!MMU r q. r IN mmu_req_sent MMU /\ match(r,q) ==> 
?MMU'. mmu_step_rcv_rpl(MMU,q,MMU')
``);

val mmu_golden_lookup_def = Define `mmu_golden_lookup (MMU, r, GI, MMU') =
?r' MMU'' q.   
   ((mmu_abs MMU).state r = TRANS NONE)
/\ mmu_step_snd_req(MMU,r',MMU'')
/\ ((mmu_abs MMU'').state r = TRANS (SOME r'))
/\ match(r',q)
/\ (Rpl_val q :bool[64] = mem_read GI (Rpl_Adr q) 8)
/\ mmu_step_rcv_rpl(MMU'',q,MMU')
`;

val mmu_golden_comp_def = Define `
   (mmu_golden_comp (MMU, r, GI, MMU', 0) = (MMU = MMU'))
/\ (mmu_golden_comp (MMU, r, GI, MMU', SUC n) = 
    ?MMU''. mmu_golden_comp (MMU,r,GI,MMU'',n) 
	 /\ mmu_golden_lookup (MMU'',r,GI,MMU') )
`;

val mmu_golden_trans_axiom = new_axiom("mmu_golden_trans_axiom", ``
!MMU GI cfg PT RO tr r.
   mmu_golden_conf (MMU, GI, cfg, PT, RO, tr) 
/\ ((mmu_abs MMU).state r = TRANS NONE) 
==>
?MMU' n. n > 0
      /\ mmu_golden_comp (MMU,r,GI,MMU',n)
      /\ (mmu_abs MMU').state r IN {FAULT; FINAL NONE}
``);			 

val mmu_final_req_axiom = new_axiom("mmu_final_req_axiom", ``
!MMU r. ((mmu_abs MMU).state r = FINAL NONE) ==>
?r' MMU'. mmu_step_snd_req(MMU,r',MMU') 
       /\ ((mmu_abs MMU').state r = FINAL (SOME r')) 
``);			 

val mmu_fault_rpl_axiom = new_axiom("mmu_fault_rpl_axiom", ``
!MMU r. ((mmu_abs MMU).state r = FAULT) ==>
?q MMU'. mmu_step_snd_rpl(MMU,q,MMU')
      /\ match(r,q)
      /\ Frpl q
``);			 

val mmu_final_rpl_axiom = new_axiom("mmu_final_rpl_axiom", ``
!MMU r l q'. ((mmu_abs MMU).state r = FINAL (SOME l))
          /\ q' IN mmu_rpl_rcvd MMU
	  /\ match(l,q')
==>
?q MMU'. mmu_step_snd_rpl(MMU,q,MMU')
      /\ match(r,q)
      /\ Rpl_val_eq q q' 
``);			 

(* restrict fault info for GICD faults *)
val mmu_gicd_fault_rpl_axiom = new_axiom("mmu_gicd_fault_rpl_axiom", ``
!MMU r q MMU' fi. mmu_step_snd_rpl(MMU,q,MMU') 
	       /\ (q = Fault r fi)
	       /\ (PAdr r IN RPAR.Amap GICD)
==>
   (failgicd((11><0) (extract_FAR fi), SzOf r = 1, Wreq r) <=> ~gicd_req_ok r)
``);

val mmu_unique_lookup_match_lem = store_thm("mmu_unique_lookup_match_lem", ``
!MMU q r l.
   inv_good_mmu MMU   
/\ ((mmu_abs MMU).state r = TRANS (SOME l))
/\ match(l,q)
==>
   ~(?r'. match_final MMU (r',q))
/\ ({r' | ?r. ((mmu_abs MMU).state r = TRANS (SOME r')) /\ match (r',q)} = {l})
``,
  RW_TAC (srw_ss()) [match_final_def]
  THENL[(* case: ~match_final *)
	CCONTR_TAC THEN 
	FULL_SIMP_TAC (srw_ss()) [] THEN 
	IMP_RES_TAC unique_match_thm THEN 
	`r <> r'` by ( 
	    CCONTR_TAC THEN 
	    FULL_SIMP_TAC (srw_ss()) [] 
	) THEN 
	IMP_RES_TAC inv_good_mmu_def THEN 
	FULL_SIMP_TAC (srw_ss()) [] THEN 
	RES_TAC
        ,
	(* case: unique match *)
	`!r' r''. ((mmu_abs MMU).state r' = TRANS (SOME r'')) /\ match (r'',q)
	      ==> ((r'=r) /\ (r'' = l))` by (
	    REPEAT GEN_TAC THEN 
	    STRIP_TAC THEN 
	    IMP_RES_TAC unique_match_thm THEN 
	    RW_TAC (srw_ss()) [] THEN 
	    CCONTR_TAC THEN 
	    IMP_RES_TAC inv_good_mmu_def THEN 
	    FULL_SIMP_TAC (srw_ss()) [] THEN 
	    RES_TAC
        ) THEN 
	FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN 
	METIS_TAC []	
       ]
);			 

val mmu_unique_final_match_lem = store_thm("mmu_unique_final_match_lem", ``
!MMU q r l.
   inv_good_mmu MMU   
/\ ((mmu_abs MMU).state r = FINAL (SOME l))
/\ match(l,q)
==>
   ~(?r'. match_trans MMU (r',q))
/\ ({r' | ?r. ((mmu_abs MMU).state r = FINAL (SOME r')) /\ match (r',q)} = {l})
``,
  RW_TAC (srw_ss()) [match_trans_def]
  THENL[(* case: ~match_final *)
	CCONTR_TAC THEN 
	FULL_SIMP_TAC (srw_ss()) [] THEN 
	IMP_RES_TAC unique_match_thm THEN 
	`r <> r'` by ( 
	    CCONTR_TAC THEN 
	    FULL_SIMP_TAC (srw_ss()) [] 
	) THEN 
	IMP_RES_TAC inv_good_mmu_def THEN 
	FULL_SIMP_TAC (srw_ss()) [] THEN 
	RES_TAC
        ,
	(* case: unique match *)
	`!r' r''. ((mmu_abs MMU).state r' = FINAL (SOME r'')) /\ match (r'',q)
	      ==> ((r'=r) /\ (r'' = l))` by (
	    REPEAT GEN_TAC THEN 
	    STRIP_TAC THEN 
	    IMP_RES_TAC unique_match_thm THEN 
	    RW_TAC (srw_ss()) [] THEN 
	    CCONTR_TAC THEN 
	    IMP_RES_TAC inv_good_mmu_def THEN 
	    FULL_SIMP_TAC (srw_ss()) [] THEN 
	    RES_TAC
        ) THEN 
	FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN 
	METIS_TAC []	
       ]
);			 

val mmu_sent_match_lem = store_thm("mmu_sent_match_lem", ``
!MMU r q.
   inv_good_mmu MMU   
/\ r IN mmu_req_sent MMU
/\ match(r,q)
==>
    (?r'. match_final MMU (r',q)) 
\/ ((?r'. match_trans MMU (r',q)) /\ ~(?r'. match_final MMU (r',q)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  HO_MATCH_MP_TAC ( prove(``(f z \/ g z) /\ (g z ==> ~f z)
					   ==> 
			    (f z \/ g z /\ ~f z)``, 
			  METIS_TAC []) ) >>
  STRIP_TAC
  >| [(* case: trans or final *)
      RW_TAC (srw_ss()) [match_final_def, match_trans_def] >>
      IMP_RES_TAC inv_good_mmu_def >> (
          METIS_TAC []
      )
      ,
      (* case: trans then not final *)
      RW_TAC (srw_ss()) [match_trans_def] >>
      IMP_RES_TAC mmu_unique_lookup_match_lem >>
      METIS_TAC []
     ]
);



val mmu_lookup_rpl_lem = store_thm("mmu_lookup_rpl_lem", ``
!MMU q r l MMU'.
   inv_good_mmu MMU   
/\ ((mmu_abs MMU).state r = TRANS (SOME l))
/\ match(l,q)
/\ mmu_step_rcv_rpl(MMU,q,MMU')
==>
   (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU)
/\ (mmu_req_sent MMU' = mmu_req_sent MMU DIFF {l})
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU UNION {q})
/\ (mmu_abs MMU').state r IN {TRANS NONE; FINAL NONE; FAULT}
/\ (!r'. r' <> r ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r'))
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)
``,
  REPEAT GEN_TAC THEN 
  STRIP_TAC THEN 
  IMP_RES_TAC mmu_unique_lookup_match_lem THEN 
  IMP_RES_TAC mmu_memrpl_axiom THEN 
  REV_FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION] THEN 
  RW_TAC (srw_ss()) []
  THEN1 ( FULL_SIMP_TAC (srw_ss()) [match_trans_def] ) THEN 
  `~match_trans MMU (r',q)` by (
      RW_TAC (srw_ss()) [match_trans_def] THEN 
      CCONTR_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      RES_TAC THEN 
      IMP_RES_TAC inv_good_mmu_def THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      RES_TAC
  ) THEN 
  RES_TAC  
);			 

val mmu_final_rpl_lem = store_thm("mmu_final_rpl_lem", ``
!MMU q r l MMU'.
   inv_good_mmu MMU   
/\ ((mmu_abs MMU).state r = FINAL (SOME l))
/\ match(l,q)
/\ l IN mmu_req_sent MMU
/\ mmu_step_rcv_rpl(MMU,q,MMU')
==>
   (mmu_rpl_rcvd MMU' = mmu_rpl_rcvd MMU UNION {q})
/\ (mmu_req_sent MMU' = mmu_req_sent MMU DIFF {l})
/\ (mmu_ptl_hist MMU' = mmu_ptl_hist MMU)
/\ ((mmu_abs MMU').state = (mmu_abs MMU).state)
/\ (mmu_req_rcvd MMU' = mmu_req_rcvd MMU)
/\ ((mmu_abs MMU').active = (mmu_abs MMU).active)
/\ ((mmu_abs MMU').cfg = (mmu_abs MMU).cfg)
``,
  REPEAT GEN_TAC THEN 
  STRIP_TAC THEN 
  IMP_RES_TAC mmu_unique_final_match_lem THEN 
  `?r'. match_final MMU (r',q)` by (
      METIS_TAC [mmu_sent_match_lem]
  ) THEN 
  IMP_RES_TAC mmu_memrpl_axiom THEN 
  REV_FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC []
);			 


val golden_lookup_mmu_state_lem = store_thm("golden_lookup_mmu_state_lem", ``
!MMU r GI MMU'. 
   inv_good_mmu MMU
/\ mmu_golden_lookup(MMU,r,GI,MMU') 
==>
   (!r'. r' <> r ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r'))
/\ inv_good_mmu MMU'
``,
  RW_TAC (srw_ss()) [mmu_golden_lookup_def] >> (
      `mmu_step(MMU,SEND (SREQ r' id), MMU'')` by (
          RW_TAC (srw_ss()) [mmu_step_def]
      ) >>
      `inv_good_mmu MMU''` by (
          METIS_TAC [inv_good_mmu_axiom]
      ) >>
      `mmu_step(MMU'',RCV (SRPL q id), MMU')` by (
          RW_TAC (srw_ss()) [mmu_step_def]
      ) >>
      `inv_good_mmu MMU'` by (
          METIS_TAC [inv_good_mmu_axiom]
      ) 
  ) >>
  `(mmu_abs MMU').state r'' = (mmu_abs MMU'').state r''` by (
      METIS_TAC [mmu_lookup_rpl_lem]
  ) >>
  `(mmu_abs MMU'').state r'' = (mmu_abs MMU).state r''` by (
      METIS_TAC [mmu_send_axiom]
  ) >>
  METIS_TAC []
);


val golden_comp_mmu_state_lem = store_thm("golden_comp_mmu_state_lem", ``
!MMU r GI n MMU'. 
   inv_good_mmu MMU
/\ mmu_golden_comp(MMU,r,GI,MMU',n) 
==>
   (!r'. r' <> r ==> ((mmu_abs MMU').state r' = (mmu_abs MMU).state r'))
/\ inv_good_mmu MMU'
``,
  Induct_on `n`
  >| [(* n=0 *)
      RW_TAC (srw_ss()) [mmu_golden_comp_def] >>
      FULL_SIMP_TAC std_ss []
      ,
      (* n->n+1 *)
      RW_TAC std_ss [mmu_golden_comp_def] >> ( RES_TAC )
      >| [`((mmu_abs MMU').state r' = (mmu_abs MMU'').state r')` by (
	      METIS_TAC [golden_lookup_mmu_state_lem]
	  ) >>
	  METIS_TAC []
	  ,
	  `inv_good_mmu MMU'` by (
	      METIS_TAC [golden_lookup_mmu_state_lem]
	  )
	 ]
     ]
);


    
(**************** Peripheral steps *****************)

(**** uninterpreted model of the peripherals ****)
(* peripheral transition relations for different actions

   per_step_rcv_rpl(P,q,P') - receive DMA reply q from SMMU
   per_step_rcv_req(P,r,P') - receive memory-mapped I/O (MMIO) request r
   per_step_rcv_pev(P,l,P') - receive list l of related external input events
   per_step_snd_req(P,r,P') - send DMA request to SMMU
   per_step_snd_rpl(P,q,P') - send MMIO reply to memory, to be forwarded to core
   per_step_snd_pev(P,l,P') - send list l of external output events
   per_step_snd_irq(P,q,P') - signal interrupt q to GIC
   per_step_internal(P,P') - internal step
*)
val _ = new_constant("per_step_rcv_rpl", 
		     ``:peripheral # reply # peripheral -> bool``);
val _ = new_constant("per_step_rcv_req", 
		     ``:peripheral # request # peripheral -> bool``);
val _ = new_constant("per_step_rcv_pev", 
		     ``:peripheral # pevent list # peripheral -> bool``);
val _ = new_constant("per_step_snd_req", 
		     ``:peripheral # request # peripheral -> bool``);
val _ = new_constant("per_step_snd_rpl", 
		     ``:peripheral # reply # peripheral -> bool``);
val _ = new_constant("per_step_snd_pev", 
		     ``:peripheral # pevent list # peripheral -> bool``);
val _ = new_constant("per_step_snd_irq", 
		     ``:peripheral # num # peripheral -> bool``);
val _ = new_constant("per_step_internal", 
		     ``:peripheral # peripheral -> bool``);

(* per_step(P,a,P') - transition relation for peripherals

   RCV (MRPL r) - receive DMA reply r from SMMU
   RCV (SREQ r id) - receive MMIO request from sender id
   RCV (PEV l) - receive list l of external inputs
   SEND (MREQ r) - send DMA request r to SMMU
   SEND (SRPL q id) - send MMIO reply q to memory, forwarded to sender core id
   SEND (PEV l) - send list l of external outputs
   SEND (PERQ (PIR q)) - send physical device interrupt PIR q to GIC
   TAU - internal action

   the relation does not hold for any other actions.
*)
val per_step_def = Define `
per_step (P : peripheral, a : Action, P' : peripheral) =
	case a of
          | RCV (MRPL r) => per_step_rcv_rpl(P,r,P')
          | RCV (SREQ r id) => per_step_rcv_req(P,r,P')
          | RCV (PEV l) => per_step_rcv_pev(P,l,P')
          | SEND (MREQ r) => per_step_snd_req(P,r,P')
          | SEND (SRPL r id) => per_step_snd_rpl(P,r,P')
          | SEND (PEV l) => per_step_snd_pev(P,l,P')
          | SEND (PERQ (PIR q)) => per_step_snd_irq(P,q,P')
          | TAU => per_step_internal(P,P')
          | _   => F
`;

(* per_wrap_step(Pw,a,Pw) - peripheral wrapper semantics

   we define the message history variables for memory-mapped I/O to the
   peripherals explicitly, so that we can omit sender IDs from the peripheral
   transitions, then peripheral states are identical at the ideal and refined
   model, as exactly the same messages are received.

   the wrapper affects only memory-mapped I/O requests and replies:

   RCV (SREQ r id) - let peripheral receive message r and record its sender id
   SEND (SRPL q id) - peripheral replied with q, remove the corresponding 
		request from the records and attach the original sender id
  
   TODO: in the send case the id should match IOreq_rcvd(ReqOf q)

   In the other cases the history variable is unaffected and the wrapper simply
   proxies the request and reply messages of the underlying peripheral step.
*)
val per_wrap_step_def = Define `
per_wrap_step (Pw : periph_wrapper, a : Action, Pw' : periph_wrapper) =
case a of
  | RCV (SREQ r id) => per_step(Pw.st, a, Pw'.st) /\
		       (Pw'.IOreq_rcvd = (r =+ SOME id) Pw.IOreq_rcvd)
  | SEND (SRPL r id) => per_step(Pw.st, a, Pw'.st) /\
		        (Pw'.IOreq_rcvd = (ReqOf r =+ NONE) Pw.IOreq_rcvd)
  | _	=> per_step(Pw.st, a, Pw'.st) /\ 
	   (Pw'.IOreq_rcvd = Pw.IOreq_rcvd)
`;


(* Lemma: summary of the MMIO receive semantics *)
val per_wrap_rcv_io_lem = store_thm("per_wrap_rcv_io_lem", ``
!Pw r id Pw'. 
    per_wrap_step(Pw,RCV (SREQ r id),Pw')
==> 
    per_step(Pw.st, RCV (SREQ r id), Pw'.st)
 /\ (Pw'.IOreq_rcvd r = SOME id)
 /\ !r'. r' <> r ==> (Pw'.IOreq_rcvd r' = Pw.IOreq_rcvd r')
``,
  RW_TAC (srw_ss()) [per_wrap_step_def, combinTheory.APPLY_UPDATE_THM]
);

(* Lemma: summary of the MMIO send reply semantics 
   TODO: this should also contrain "id" once the definition is fixed
*)
val per_wrap_io_rpl_lem = store_thm("per_wrap_io_rpl_lem", ``
!Pw q id Pw'. 
    per_wrap_step(Pw,SEND (SRPL q id),Pw')
==> 
    per_step(Pw.st, SEND (SRPL q id), Pw'.st)
 /\ (Pw'.IOreq_rcvd (ReqOf q) = NONE)
 /\ !r. r <> ReqOf q ==> (Pw'.IOreq_rcvd r = Pw.IOreq_rcvd r)
``,
  RW_TAC (srw_ss()) [per_wrap_step_def, combinTheory.APPLY_UPDATE_THM]
);

(* Lemma: the peripheral wrapper always steps the peripheral with the same
action *)
val per_wrap_per_step_lem = store_thm("per_wrap_per_step_lem", ``
!Pw a Pw'. per_wrap_step(Pw,a,Pw') ==> per_step(Pw.st,a,Pw'.st)
``,
  Cases_on `a`
  >| [(* SEND *)
      Cases_on `M` >> (
          RW_TAC (srw_ss()) [per_wrap_step_def]
      )
      ,
      (* RCV *)
      Cases_on `M` >> (
          RW_TAC (srw_ss()) [per_wrap_step_def]
      )
      ,
      (* TAU *)
      RW_TAC (srw_ss()) [per_wrap_step_def]
     ]
);

(* per_IO_step a - a is an MMIO step *)
val per_IO_step_def = Define `
   (per_IO_step (RCV (SREQ r id)) = T)
/\ (per_IO_step (SEND (SRPL r id)) = T)
/\ (per_IO_step _ = F)
`;

(* Lemma: alternate definition for per_IO_step *)
val per_IO_step_lem = store_thm("per_IO_step_lem", ``
!a. per_IO_step a <=> ((?q id. a = SEND (SRPL q id)) \/ 
		       (?r id. a = RCV (SREQ r id)))
``,
  Cases_on `a` >> (
      RW_TAC std_ss [per_IO_step_def]
  ) >> (
      Cases_on `M` >> (
          RW_TAC std_ss [per_IO_step_def]
      )
  )
);

(* Lemma: only MMIO steps change the wrapper history variables *)
val per_wrap_not_IO_step_req_rcvd_lem = 
store_thm("per_wrap_not_IO_step_req_rcvd_lem", ``
!Pw a Pw'. ~per_IO_step a /\ per_wrap_step(Pw,a,Pw') ==>
    (Pw'.IOreq_rcvd = Pw.IOreq_rcvd)
``,
  Cases_on `a`
  >| [(* SEND *)
      Cases_on `M` >> (
          RW_TAC (srw_ss()) [per_IO_step_def, per_wrap_step_def]
      )
      ,
      (* RCV *)
      Cases_on `M` >> (
          RW_TAC (srw_ss()) [per_IO_step_def, per_wrap_step_def]
      )
      ,
      (* TAU *)
      RW_TAC (srw_ss()) [per_wrap_step_def]
     ]
);

(* invariant of peripheral components:
 
   Similar to the cores we also make the peripherals sequential, for simplicity,
   thus there is at most one DMA request pending by a peripheral.

   TODO: we never use this restriction, it can probably be dropped easily

   Moreover, inactive peripherals do not perform DMA operations, i.e., there are
   no pending DMA requests.
 *)
val inv_good_per_def = Define `inv_good_per (P:peripheral) = 
   CARD(per_req_sent P) <= 1
/\ (~per_active P ==> (per_req_sent P = EMPTY))
`;

(* Axiom: peripheral steps preserve the invariants

   In particular this means for the current invariant, that the peripheral does
   not send a second DMA request while one is already pending. Additionally,
   peripherals do not send DMA requests while inactive and they resolve all
   pending DMA requests before shutting down.
*)
val inv_good_per_axiom = new_axiom("inv_good_per_axiom", ``
!P a P'. inv_good_per P /\ per_step(P,a,P') ==> inv_good_per P'
``);

(* Axiom: only IO request can enable peripheral to start sending, or shut down,
   otherwise the activity state is preserved
   
   In principle it can also shut down when receiving a DMA reply.

   We are simplifying away internal and external deactivation here
 *)
val per_active_axiom = new_axiom("per_active_axiom", ``
!P l P'. (per_step(P,TAU,P') \/ per_step(P, RCV (PEV l), P')) ==> 
(per_active P = per_active P')
``);

(* wrapper invariant:

   the peripheral invariant holds

   The wrapper MMIO history variables are consistent with the corresponding
   message history variable in the abstract peripheral state.

   Note that the sender ID is not coupled, as it is not recorded in the
   peripheral, assuming that peripherals are agnostic to the assigned core id
*)
val inv_good_per_wrap_def = Define `inv_good_per_wrap (Pw:periph_wrapper) = 
    inv_good_per Pw.st
 /\ (!r. r IN per_req_rcvd Pw.st <=> IS_SOME (Pw.IOreq_rcvd r))
`;

(**** abstract behavioral specification ****)

(* per_step_snd_req(P,r,P') - sending DMA request r

   preconditons:
   - r has not already been sent, i.e., it is not currently pending
   - the peripheral is active   

   postconditions:
   - r is added to the currently pending DMA requests
   - the peripheral is still active
   - other abstract state (the record of received MMIO requests) is unchanged
*)
val per_send_dma_axiom = new_axiom("per_send_dma_axiom", ``
!P r P'. per_step_snd_req(P,r,P') ==> 
   (per_req_sent P' = per_req_sent P UNION {r})
/\ (r NOTIN per_req_sent P)
/\ (per_req_rcvd P' = per_req_rcvd P)
/\ per_active P
/\ per_active P'
``);


(* per_step_rcv_rpl(P,q,P') - receive DMA reply q

   preconditons:
   - the corresponding request r for q is pending
   - the peripheral is active   

   postconditions:
   - r is removed from the currently pending DMA requests
   - other abstract state (the record of received MMIO requests) is unchanged
*)
val per_rcv_dma_axiom = new_axiom("per_rcv_dma_axiom", ``
!P q P'. per_step_rcv_rpl(P,q,P')
==>
   (ReqOf q) IN per_req_sent P /\ match(ReqOf q, q)
/\ (per_req_sent P' = per_req_sent P DIFF {ReqOf q})
/\ (per_req_rcvd P' = per_req_rcvd P)
/\ per_active P
``);

(* per_step_rcv_req(P,r,P') - receive MMIO request r

   preconditons:
   - the request r is not already pending

   postconditions:
   - r is added to the currently pending MMIO requests
   - other abstract state (the record of sent DMA requests) is unchanged
*)
val per_rcv_io_axiom = new_axiom("per_rcv_io_axiom", ``
!P r id P'. per_step_rcv_req(P,r,P') ==> 
   r NOTIN per_req_rcvd P
/\ (per_req_sent P' = per_req_sent P)
/\ (per_req_rcvd P' = per_req_rcvd P UNION {r})
``);

(* per_step_snd_rpl(P,q,P') - send MMIO reply q

   preconditons:
   - the corresponding MMIO request r is pending
   - the peripheral is active 
   TODO: we may want to drop this, as it seems unnecessarily strict,
   a peripheral may first be configured before DMA capabilities are activated

   postconditions:
   - r is removed the currently pending MMIO requests
   - other abstract state (the record of sent DMA requests) is unchanged
*)
val per_snd_iorpl_axiom = new_axiom("per_snd_iorpl_axiom", ``
!P q id P'. per_step_snd_rpl(P,q,P')
==> 
?r. 
   r IN per_req_rcvd P /\ match(r,q)
/\ (per_req_sent P' = per_req_sent P)
/\ (per_req_rcvd P' = per_req_rcvd P DIFF {r})
/\ per_active P
``);

(* per_step_{snd/rcv}_pev(P,l,P') - 
   send/receive list l of external outputs/inputs

   preconditons:
   - in the send case, the peripheral is active 

   postconditions:
   - the abstract message record state is unchanged
*)
val per_event_step_axiom = new_axiom("per_event_step_axiom", ``
!P l P'. (per_step_rcv_pev(P,l,P') \/ per_step_snd_pev(P,l,P')) ==> 
   (per_req_sent P' = per_req_sent P)
/\ (per_req_rcvd P' = per_req_rcvd P)
/\ (per_step_snd_pev(P,l,P') ==> per_active P)
``);

(* per_step_snd_irq(P,q,P') - send decive interrupt q

   preconditons:
   - the peripheral is active 

   postconditions:
   - the abstract message record state is unchanged
*)
val per_irq_step_axiom = new_axiom("per_irq_step_axiom", ``
!P q P'. per_step_snd_irq(P,q,P') ==> 
   (per_req_sent P' = per_req_sent P)
/\ (per_req_rcvd P' = per_req_rcvd P)
/\ per_active P
``);

(* per_step_internal(P,P') - internal peripheral step

   preconditons:
   none assumed

   postconditions:
   - the abstract message record state is unchanged

   in addition the active state does not change, as given by per_active_axiom
*)
val per_internal_axiom = new_axiom("per_internal_axiom", ``
!P P'. per_step_internal(P,P') ==> 
   (per_req_sent P' = per_req_sent P)
/\ (per_req_rcvd P' = per_req_rcvd P)
``);

(* could prove this as lemma:

inactive peripherals do not send messages or interrupts

val per_inactive_axiom = new_axiom("per_active_axiom", ``
!P a P'. ~per_active P /\ a <> TAU /\ (!l. a <> RCV (PEV l)) 
      /\ (!r id. a <> RCV (SREQ r id))
==> 
~per_step(P, a, P')
``);
*)

(* we do not need liveness axioms and coupling between ideal and refined steps,
because configurations are equal in the ideal and refined model and transitions
are scheduled in lock-step *)

(* Lemma: if the invariants hold then MMIO requests are only received if they
are not only pending according to the wrapper records
*)
val per_wrap_io_unique_lem = store_thm("per_wrap_io_unique_lem", ``
!Pw r id Pw'. 
    per_wrap_step(Pw,RCV (SREQ r id),Pw')
 /\ inv_good_per_wrap Pw
==> 
    ~IS_SOME (Pw.IOreq_rcvd r)
``,
  RW_TAC (srw_ss()) [per_wrap_step_def, per_step_def] >>
  IMP_RES_TAC per_rcv_io_axiom >>
  IMP_RES_TAC inv_good_per_wrap_def >>
  METIS_TAC [optionTheory.NOT_IS_SOME_EQ_NONE]
);


(* Lemma: the received MMIO requests are only affected by MMIO steps *)
val per_not_IO_step_req_rcvd_lem = 
store_thm("per_not_IO_step_req_rcvd_lem", ``
!P a P'. ~per_IO_step a /\ per_step(P,a,P') ==>
    (per_req_rcvd P' = per_req_rcvd P)
``,
  Cases_on `a`
  >| [(* SEND *)
      Cases_on `M` >> (
          RW_TAC (srw_ss()) [per_IO_step_def, per_step_def] )
      >| [(* send dma request *)
	  IMP_RES_TAC per_send_dma_axiom
	  ,
	  (* send irq *)
	  Cases_on `i` >> (
	      FULL_SIMP_TAC (srw_ss()) []
	  ) >>
	  IMP_RES_TAC per_irq_step_axiom
	  ,
	  (* send pev *)
	  IMP_RES_TAC per_event_step_axiom
	 ]
      ,
      (* RCV *)
      Cases_on `M` >> (
          RW_TAC (srw_ss()) [per_IO_step_def, per_step_def]
      )
      >| [(* rcv dma reply *)
	  IMP_RES_TAC per_rcv_dma_axiom
	  ,
	  (* rcv pev *)
	  IMP_RES_TAC per_event_step_axiom
	 ]
      ,
      (* TAU *)
      RW_TAC (srw_ss()) [per_step_def] >>
      IMP_RES_TAC per_internal_axiom
     ]
);

(* Lemma: peripheral steps preserve the wrapper (and peripheral) invariants *)
val inv_good_per_wrap_lem = store_thm("inv_good_per_wrap_lem", ``
!P a P'. inv_good_per_wrap P /\ per_wrap_step(P,a,P') ==> inv_good_per_wrap P'
``,
  RW_TAC std_ss [inv_good_per_wrap_def]
  >| [(* inv_good_per *)
      IMP_RES_TAC per_wrap_per_step_lem >>
      IMP_RES_TAC inv_good_per_axiom
      ,
      (* IOreq_rcvd *)
      Cases_on `per_IO_step a`
      >| [(* IO step *)
	  IMP_RES_TAC per_IO_step_lem
	  >| [(* SEND reply *)
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC per_wrap_io_rpl_lem >>
	      FULL_SIMP_TAC (srw_ss()) [per_step_def] >>
	      IMP_RES_TAC per_snd_iorpl_axiom >>
	      IMP_RES_TAC match_ReqOf_lem >>
	      RW_TAC std_ss [] >>
	      Cases_on `r = ReqOf q`
	      >| [(* answered request *)
		  RW_TAC std_ss [NOT_IN_DIFF_SING]
		  ,
		  (* other request *)
		  RES_TAC >>
		  RW_TAC std_ss [pred_setTheory.IN_DIFF, 
				 pred_setTheory.IN_SING]
		 ]
	      ,
	      (* receive reply *)
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC per_wrap_rcv_io_lem >>
	      FULL_SIMP_TAC (srw_ss()) [per_step_def] >>
	      IMP_RES_TAC per_rcv_io_axiom >>
	      Cases_on `r = r'`
	      >| [(* received request *)
		  RW_TAC std_ss [pred_setTheory.IN_UNION, 
				 pred_setTheory.IN_SING]
		  ,
		  (* other request *)
		  RES_TAC >>
		  RW_TAC std_ss [pred_setTheory.IN_UNION, 
				 pred_setTheory.IN_SING]
		 ]
	     ]
	  ,
	  (* not IO step *)
	  IMP_RES_TAC per_wrap_not_IO_step_req_rcvd_lem >>
          IMP_RES_TAC per_wrap_per_step_lem >>
	  IMP_RES_TAC per_not_IO_step_req_rcvd_lem >>
	  RW_TAC std_ss [] 
	 ]
     ]	  
);




(**************** GIC steps *****************)

val _ = new_constant("gic_step_rcv_req", ``:gic # request # senderID # gic -> bool``);
val _ = new_constant("gic_step_rcv_irq", ``:gic # irqID # gic -> bool``);
val _ = new_constant("gic_step_snd_irq", ``:gic # num # bool # gic  -> bool``);
val _ = new_constant("gic_step_snd_rpl", ``:gic # reply # senderID # gic -> bool``);

(* no internal steps, do not know how to map to ideal model *)
val gic_step_def = Define `gic_step (G : gic, a : Action, G' : gic) =
	case a of
          | RCV (SREQ r id) => gic_step_rcv_req(G,r,id,G')
          | RCV (PERQ q) => gic_step_rcv_irq(G,q,G')
          | SEND (PHYS NONE c) => gic_step_snd_irq(G,c,F,G')
          | SEND (VIRT c) => gic_step_snd_irq(G,c,T,G')
          | SEND (SRPL r id) => gic_step_snd_rpl(G,r,id,G')
          | _   => F
`;

(* GIC semantics *)

(* receive req:
- updates req_rcvd
- registers and interrupt state do not change

- always possible if in GIC range
*)

val gic_rcv_io_axiom = new_axiom("gic_rcv_io_axiom", ``
!G r id G'. gic_step_rcv_req(G,r,id,G') ==> 
   (gic_req_rcvd G' = gic_req_rcvd G UNION {(r,id)})
/\ (gic_abs G' = gic_abs G)
``);

val gic_rcv_io_enabled_axiom = new_axiom("gic_rcv_io_enabled_axiom", ``
!G r id. (?A. gicAR A /\ PAdr r IN RPAR.Amap A) ==> 
?G'. gic_step_rcv_req(G,r,id,G')
``);

(* receive irq:
- does not change req_rcvd
- adds interrupt to Q
-- INACTIVE -> PENDING 
-- PENDING -> PENDING
-- ACTIVE -> PENDACT
-- PENDACT -> PENDACT
- VI unchanged
- GICV and GICH registers unchanged
- constant and mutable register unchanged
- volatile GICD register changes unspecified, needs to be coupled with ideal gic
- GICC unchanged, volatile registers not covered

- always possible
*)

val gic_rcv_irq_axiom = new_axiom("gic_rcv_irq_axiom", ``
!G q G'. gic_step_rcv_irq(G,q,G') ==> 
   (gic_req_rcvd G' = gic_req_rcvd G)
/\ (Q G' q = case Q G q of
                         | INACTIVE => PENDING 
			 | PENDING  => PENDING
			 | ACTIVE   => PENDACT
			 | PENDACT  => PENDACT)
/\ (!q'. q <> q' ==> (Q G' q' = Q G q'))
/\ ((gic_abs G').gich = (gic_abs G).gich)
/\ ((gic_abs G').gicv = (gic_abs G).gicv)
/\ (!r. (gic_abs G').gicd (CONST r) = (gic_abs G).gicd (CONST r))
/\ (!r. (gic_abs G').gicd (MUTE r) = (gic_abs G).gicd (MUTE r))
/\ ((gic_abs G).gicc = (gic_abs G').gicc)
``);

val gic_rcv_irq_enabled_axiom = new_axiom("gic_rcv_irq_enabled_axiom", ``
!G q. ?G'. gic_step_rcv_irq(G,q,G')
``);

(* send phys/virt irq :
- does not change req_rcvd
- does not change Q, VI
- does not change registers

[if in golden gicd conf and inv_gicc holds]
- possible if irq is PENDING and highest priority on that core and not PIR 0-7 
- also not masked according to dmsk / vmsk
- for virtual interrupts, no pending phys irq for that core (after masking)
 *)

val gic_snd_irq_axiom = new_axiom("gic_snd_irq_axiom", ``
!G c X G'. gic_step_snd_irq(G,c,X,G') ==> 
   (gic_req_rcvd G' = gic_req_rcvd G)
/\ (gic_abs G' = gic_abs G)
/\ (Q G' = Q G)
/\ (VI G' = VI G)
/\ (~X /\
   (?q R. (R = ready_irqs(Q G, dmsk((gic_abs G).gicd, (gic_abs G).gicc c, c)))
       /\ q IN R /\ (w2n (prio q) = max_prio R)
       /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
       /\ (!id c' c''. (q = SGI (id, c', c'')) ==> id <=+ 7w /\ (c'' = c)) )
    \/ X /\
   (?q R. (R = ready_irqs(VI G c, vmsk((gic_abs G).gicv c)))
       /\ q IN R /\ (w2n (prio q) = max_prio R)
       /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
       /\ (!id c' c''. (q = SGI (id, c', c'')) ==> id <=+ 7w /\ (c'' = c)) ))
``);

val gic_snd_phys_irq_enabled_axiom = new_axiom("gic_snd_phys_irq_enabled_axiom",``
!G c. inv_gicc ((gic_abs G).gicc c)
   /\ (?q R. (R = ready_irqs(Q G, 
			     dmsk((gic_abs G).gicd, (gic_abs G).gicc c, c)))
	  /\ q IN R /\ (w2n (prio q) = max_prio R)
          /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
          /\ (!id c' c''. (q = SGI (id, c', c'')) ==> id <=+ 7w /\ (c'' = c)) )
==>
?G'. gic_step_snd_irq(G,c,F,G') 
``);
 
(* no prioritization of virtual vs physical interrupts here *)
val gic_snd_virt_irq_enabled_axiom = new_axiom("gic_snd_virt_irq_enabled_axiom",``
!G c. (?q R. (R = ready_irqs(VI G c, vmsk((gic_abs G).gicv c)))
	  /\ q IN R /\ (w2n (prio q) = max_prio R)
          /\ (!id. (q = PIR id) ==> id >= 16 /\ id < 1020)
          /\ (!id c' c''. (q = SGI (id, c', c'')) ==> id <=+ 7w /\ (c'' = c)) )
==>
?G'. gic_step_snd_irq(G,c,T,G') 
``);


(* send reply
- only reply to actual requests, return correct register values for reads
- update according to gic register upd function for received requests
- history semantics
- return faults for fail_gicd and walks

- always possible for present request

NOTE: we only give the semantics for GICC that we use in the hypervisor.
*)

(* activates highest priority pending interrupt, if present,
may change highest priority pending interrupt and running priority (not volatile)
*)
val gic_read_aiar_axiom = new_axiom("gic_read_aiar_axiom", ``
!G q r id G' v c i. 
   (gic_abs G).gicd IN gic_gm_conf
/\ inv_gicc ((gic_abs G).gicc c)
/\ gic_step_snd_rpl(G,q,id,G') 
/\ ((q,id) = ((ReadValue r v), CoreSender c))
/\ (r = Read Agicc_aiar 4 i)
==> 
?irqid:bool[10] s:bool[3] irq R.
   (v = w2v((s @@ irqid) :bool[32]))
/\ (irqid <=+ 7w \/ irqid >=+ 16w /\ irqid <+ 1020w \/ (irqid = 1023w))
/\ (R = ready_irqs(Q G, dmsk((gic_abs G).gicd, (gic_abs G).gicc c, c)))
/\ (irqid <> 1023w ==> irq IN R /\ (w2n (prio irq) = max_prio R))
/\ ((irqid = 1023w) <=> (R = EMPTY))
/\ (irq = if irqid <=+ 15w then SGI ((3><0) irqid, w2n s, c) else PIR (w2n irqid))
/\ (r,id) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r,id)})
/\ ((gic_abs G').gich = (gic_abs G).gich)
/\ ((gic_abs G').gicv = (gic_abs G).gicv)
/\ (!c'. c' <> c ==> ((gic_abs G').gicc c' = (gic_abs G).gicc c'))
/\ inv_gicc ((gic_abs G').gicc c)
/\ (!r. (gic_abs G').gicd (CONST r) = (gic_abs G).gicd (CONST r))
/\ (!r. (gic_abs G').gicd (MUTE r) = (gic_abs G).gicd (MUTE r))
/\ ((irqid = 1023w) ==> !r. (gic_abs G').gicd (VOL r) = (gic_abs G).gicd (VOL r))
/\ (gic_abs G').gicd IN gic_gm_conf
(* assuming edge-triggered interrupt here:
interrupt becomes active, not pending-active *)
/\ (!q'. Q G' q' = if irqid <> 1023w /\ (q' = irq) then ACTIVE else Q G q')
``);

(* TODO: need bisimulation of gicd registers for read of AIAR / ideal dist step *)

(* simplification: we assume the fixed mapping of IRQs to VIs of the hypervisor,
each guest has enough LRs to dedicated one to each of its interrupts,
others are inactive, mapped to disjoint registers (that do not really exist) *)
val gic_read_lr_axiom = new_axiom("gic_read_lr_axiom", ``
!G q r id G' v c IRQ i. 
   gic_step_snd_rpl(G,q,id,G') 
/\ ((q,id) = ((ReadValue r v), CoreSender c))
/\ (r = Read (Agich_lr IRQ) 4 i)
==> 
   (v = w2v ((gic_abs G).gich c (gich_lr IRQ)))
/\ (r,id) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r,id)})
/\ (gic_abs G' = gic_abs G)
``);

val gich_pir_deact = Define `gich_pir_deact (G,G',c) (n,m) = 
?R lr.
   (lr = ((gic_abs G).gich c R))
/\ (n = w2n ((9><0)lr :bool[10]))
/\ (m = w2n ((19><10)lr :bool[10]))
/\ (n>=16) /\ (n<1020) 
/\ VI G' c (PIR n) <> VI G c (PIR n) 
/\ (lr ' 31)
`;

(* reads and writes of GICV registers can have side effects, e.g., GICV_AIAR *)
val gic_gicv_rpl_axiom = new_axiom("gic_gicv_rpl_axiom", ``
!G q c G'. 
   gic_step_snd_rpl(G, q, CoreSender c, G') 
/\ Rpl_PAdr q IN RPAR.Amap GICV
==> 
?r.
   (r, CoreSender c) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r, CoreSender c)})
/\ ((gic_abs G').gicc = (gic_abs G).gicc)
/\ (!r. (gic_abs G').gicd (CONST r) = (gic_abs G).gicd (CONST r))
/\ (!r. (gic_abs G').gicd (MUTE r) = (gic_abs G).gicd (MUTE r))
/\ (!irq id c'. (irq = if id <=+ 15w then SGI ((3><0) id, c', c) 
	               else PIR (w2n id))
	     /\ (id <=+ 7w \/ id >=+ 16w /\ id <+ 1020w) ==>
	case VI G c irq of 
(* GICV accesses cannot make inactive interrupt pending or active *)
          | INACTIVE => VI G' c irq = INACTIVE
          | PENDING  => VI G' c irq IN {PENDING; ACTIVE}
          | ACTIVE   => VI G' c irq IN {ACTIVE; INACTIVE}
          | PENDACT  => VI G' c irq IN {PENDACT; PENDING} )
/\ (!n. (n>7 /\ n<16 \/ n>=1020) ==> (VI G' c (PIR n) = INACTIVE))
(* only virtual interface of c affected *)
/\ (!c'. c <> c' ==> ((gic_abs G').gich c' = (gic_abs G).gich c') )
/\ (!c'. c <> c' ==> ((gic_abs G').gicv c' = (gic_abs G).gicv c') )
(* update state in corresponding LRs, only interrupt state changed *)
/\ (!R. (gic_abs G').gich c R = 
    let lr = ((gic_abs G).gich c R) in
	if (?pir. (R = (gich_lr pir)) /\ (lr ' 30)
	       /\ (!n. (n>7 /\ n<16 \/ n>=1020) ==> pir <> PIR n)) then
           case VI G' c (lr2virq(lr,c)) of
	     | INACTIVE => bit_field_insert 29 28 (0b00w:bool[2]) lr
	     | PENDING  => bit_field_insert 29 28 (0b01w:bool[2]) lr
	     | ACTIVE   => bit_field_insert 29 28 (0b10w:bool[2]) lr
	     | PENDACT  => bit_field_insert 29 28 (0b11w:bool[2]) lr 
	else lr )
(* interrupt deactivation may affect peripheral interrupt states *)
/\ (!pir. Q G' pir = 
	if ?(n,m). gich_pir_deact (G,G',c) (n,m) /\ (pir = PIR m)
        then
	    let x = @x. gich_pir_deact (G,G',c) x /\ 
		(pir = PIR (SND x)) in
            case (VI G' c (PIR (FST x)), Q G pir) of 
	      | (INACTIVE, ACTIVE)  => INACTIVE
	      | (INACTIVE, PENDACT) => PENDING
	      | _                   => Q G pir 
	else Q G pir )
``);

(* read of GICD do only change message state, no side effects *)
val gic_read_gicd_axiom = new_axiom("gic_read_gicd_axiom", ``
!G q r G' v c. 
   gic_step_snd_rpl(G, q, CoreSender c, G') 
/\ Rpl_PAdr q IN RPAR.Amap GICD
/\ (q = ReadValue r v)
==> 
let off = (11><0) (Rpl_Adr q) in
let reg = (gic_abs G).gicd (THE (decgicd off)) in
   IS_SOME (decgicd off)
/\ (?a i. (r = Read a 1 i) /\ (v = w2v ((7><0)reg :bool[8]))
       \/ (r = Read a 4 i) /\ (v = w2v reg) )
/\ (r, CoreSender c) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r, CoreSender c)})
/\ (gic_abs G' = gic_abs G)
``);

(* the requests below are the only ones the hypervisor ever sends to the GIC
therefore we do not need to specify what happens in case of a fault *)
val gic_rpl_gicd_fault_axiom = new_axiom("gic_rpl_gicd_fault_axiom", ``
!G q r G' c. 
   gic_step_snd_rpl(G, q, CoreSender c, G') 
/\ Rpl_PAdr q IN RPAR.Amap GICD
/\ (r, CoreSender c) IN gic_req_rcvd G
/\ match(r,q)
/\ gicd_req_ok r
==> 
   ~Frpl q
``);

(* writes to the GICD registers may affect other VOL registers,
e.g., GICD_SGIR, make pending / active etc, also affects interrupt state Q 
and volatile GICC registers, possibly on all cores, however not part of GICCreg *)
val gic_write_gicd_axiom = new_axiom("gic_write_gicd_axiom", ``
!G q r G' v c. 
   gic_step_snd_rpl(G, q, CoreSender c, G') 
/\ Rpl_PAdr q IN RPAR.Amap GICD
/\ (q = WrittenValue r)
/\ (Req_val r = v)
==> 
let off = (11><0) (Rpl_Adr q) in 
let reg = THE (decgicd off) in
let u = (gic_abs G).gicd reg in
   IS_SOME (decgicd off) 
/\ (r, CoreSender c) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r, CoreSender c)})
/\ (!R. (gic_abs G').gicd (CONST R) = (gic_abs G).gicd (CONST R))
/\ (!R. (gic_abs G').gicd (MUTE R) = if MUTE R = reg then
					 GICDupd(reg, u, v)
				     else (gic_abs G).gicd (MUTE R))
/\ (!R. (VOL R = reg) ==> ((gic_abs G').gicd (VOL R) = GICDupd(reg, u, v)) )
/\ ((?R. (MUTE R) = reg) /\ Adr r <> Agicd_sgir ==> 
	!R. (gic_abs G').gicd (VOL R) = (gic_abs G).gicd (VOL R))
/\ ((gic_abs G').gich = (gic_abs G).gich)
/\ ((gic_abs G').gicv = (gic_abs G).gicv)
/\ ((gic_abs G').gicc = (gic_abs G).gicc)
``);


(* write to SGIR enables up to 8 interrupts *)
val gic_write_sgir_axiom = new_axiom("gic_write_sgir_axiom", ``
!G q r G' v i c. 
   gic_step_snd_rpl(G, q, CoreSender c, G') 
/\ Rpl_PAdr q IN RPAR.Amap GICD
/\ (q = WrittenValue r)
/\ (r = Write Agicd_sgir 4 v i)
==> 
let u = v2w v :bool[32] in
let id = (3><0)u :bool[4] in 
let t = \i. case (25><24)u :bool[2] of
	      | 0b00w => ((23><16) u :bool[8]) ' i 
	      | 0b01w => i <> c
	      | 0b10w => i = c
	      | _ => F
in
   !irq. Q G' irq = if (?c'. c'< 8 /\ t c' /\ (irq = SGI (id, c', c))) then
			case Q G irq of
                          | INACTIVE => PENDING
			  | PENDING  => PENDING
			  | ACTIVE   => PENDACT
			  | PENDACT  => PENDACT
		    else Q G irq			    
``);

(* write updates LR, volatile GICV registers may change, not part of GICCreg *)
val gic_write_lr_axiom = new_axiom("gic_write_lr_axiom", ``
!G q r G' v i c IRQ. 
   gic_step_snd_rpl(G,q,CoreSender c,G') 
/\ (q = WrittenValue r)
/\ (r = Write (Agich_lr IRQ) 4 v i)
==> 
   (r,CoreSender c) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r,CoreSender c)})
/\ ((gic_abs G').gicc = (gic_abs G).gicc)
/\ ((gic_abs G').gicd = (gic_abs G).gicd)
/\ (!c' R. ((gic_abs G').gich c' R = 
	    if (c' = c) /\ (R = gich_lr IRQ) then v2w v
	    else (gic_abs G).gich c' R) )
/\ ((gic_abs G').gicv = (gic_abs G).gicv)
``);

(* write to EOIR with invariant GICC settings just lowers running priority
interrupt stays active *)
val gic_write_aeoir_axiom = new_axiom("gic_write_aeoir_axiom", ``
!G q r G' v i c. 
   inv_gicc ((gic_abs G).gicc c)
/\ gic_step_snd_rpl(G,q,CoreSender c,G') 
/\ (q = WrittenValue r)
/\ (r = Write Agicc_aeoir 4 v i)
==> 
   (r, CoreSender c) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r,CoreSender c)})
/\ (!c'. c' <> c ==> ((gic_abs G').gicc c' = (gic_abs G).gicc c'))
/\ (inv_gicc ((gic_abs G').gicc c))
/\ ((gic_abs G').gicd = (gic_abs G).gicd)
/\ ((gic_abs G').gich = (gic_abs G).gich) 
/\ ((gic_abs G').gicv = (gic_abs G).gicv)
``);

(* write to DIR with invariant GICC settings deactivates interrupt *)
val gic_write_dir_axiom = new_axiom("gic_write_dir_axiom", ``
!G q r G' v i c. 
   (gic_abs G).gicd IN gic_gm_conf
/\ inv_gicc ((gic_abs G).gicc c)
/\ gic_step_snd_rpl(G,q,CoreSender c,G') 
/\ (q = WrittenValue r)
/\ (r = Write Agicc_dir 4 v i)
==> 
let irq = lr2virq(v2w v,c) in
   (r, CoreSender c) IN gic_req_rcvd G /\ match(r,q)
/\ (gic_req_rcvd G' = gic_req_rcvd G DIFF {(r,CoreSender c)})
/\ (!c'. c' <> c ==> ((gic_abs G').gicc c' = (gic_abs G).gicc c'))
/\ (inv_gicc ((gic_abs G').gicc c))
/\ ((gic_abs G').gich = (gic_abs G).gich) 
/\ ((gic_abs G').gicv = (gic_abs G).gicv)
/\ (!r. (gic_abs G').gicd (CONST r) = (gic_abs G).gicd (CONST r))
/\ (!r. (gic_abs G').gicd (MUTE r) = (gic_abs G).gicd (MUTE r))
/\ (!q'. Q G' q' = if q'=irq then 
		       case Q G irq of
			 | INACTIVE => INACTIVE
			 | PENDING => PENDING (* considered software error *)
			 | ACTIVE => INACTIVE
			 | PENDACT => PENDING
		   else Q G q')
/\ (gic_abs G').gicd IN gic_gm_conf
``);


val gic_rpl_enable_axiom = new_axiom("gic_rpl_enable_axiom", ``
!G r id. 
(r,id) IN gic_req_rcvd G 
==>
?G' q. gic_step_snd_rpl(G,q,id,G') /\ match(r,q) 
``);

val gic_good_rpl_axiom = new_axiom("gic_good_rpl_axiom", ``
!G G' q id. gic_step_snd_rpl(G,q,id,G')
==>
?r. (r,id) IN gic_req_rcvd G /\ match(r,q) 
``);

(* only support accesses:
- to GIC memory 
- that are aligned 
- not walks 
- byte or word size
*)
val gic_fault_axiom = new_axiom("gic_fault_axiom", ``
!G G' r q id A. 
   gic_step_snd_rpl(G,q,id,G') 
/\ match(r,q)
/\ (r,id) IN gic_req_rcvd G
/\ gicAR A
/\ (PAdr r NOTIN RPAR.Amap A \/ SzOf r IN {2;8})
==>
Frpl q
``);

(* require no faults for hypervisor accesses *)
val gicd_fault_axiom = new_axiom("gicd_fault_axiom", ``
!G r id.
   gic_step_snd_rpl(G,q,id,G') /\ match(r,q) /\ (r,id) IN gic_req_rcvd G 
/\ ( (    (?i. r = Read Agicc_aiar 4 i)
       \/ (?i irq. r = Read (Agich_lr irq) 4 i)
       \/ (?i v. r = Write Agicc_aeoir 4 v i)
       \/ (?i v. r = Write Agicc_dir 4 v i)
       \/ (?i v. r = Write Agicd_sgir 4 v i)
       \/ (?i irq v. r = Write (Agich_lr irq) 4 v i)) )
==> ~Frpl q  
``);

(* bisimulation properties for coupled ideal GICC and refined GICV *)

val gicc_rpl_reg_bisim_axiom = new_axiom("gicc_rpl_reg_bisim_axiom", ``
!g ic c igic gic ir r iq q igic' gic' prq psq.
   g < PAR.ng
/\ ic < PAR.nc_g g
/\ c < RPAR.nc
/\ good_prq prq
/\ good_psq psq
/\ gicdfltr_pqq_coupling(GICDfltr, \g. (prq g) o (psq g))
/\ (!R. (idgic_abs igic).gicc ic R = (gic_abs gic).gicv c R) 
/\ (!q. (idgic_abs igic).Q ic (prq g q) = VI gic c q)
/\ (!R. (idgic_abs igic).gicd (VOL R) = 
        GICDfltr(g,VOL R,(gic_abs gic).gicd (VOL R)))
/\ PAdr ir IN RPAR.Amap GICC
/\ PAdr r IN RPAR.Amap GICV
/\ (((12><0)(Adr ir)):bool[13] = (12><0)(Adr r))
/\ xlated(ir,r)
/\ match(ir,iq)
/\ match(r,q)
/\ idgic_step_snd_rpl(igic, iq, CoreSender ic, g, igic')
/\ gic_step_snd_rpl(gic, q, CoreSender c, gic')
==>
   xlated_rpl(iq,q)
/\ (!R. (idgic_abs igic').gicc ic R = (gic_abs gic').gicv c R) 
/\ (!q. (idgic_abs igic').Q ic (prq g q) = VI gic' c q)
/\ (!R. (idgic_abs igic').gicd (VOL R) = 
        GICDfltr(g,VOL R,(gic_abs gic').gicd (VOL R)))
/\ (!g' R. g' < PAR.ng /\ g' <> g ==>
	   (GICDfltr(g',VOL R,(gic_abs gic').gicd (VOL R)) = 
            GICDfltr(g',VOL R,(gic_abs gic).gicd (VOL R))))
``);

(**************** Lemmas *****************)

val gicv_rpl_Q_sgi_lem = store_thm("gicv_rpl_Q_sgi_lem", ``
!gic q c gic' id s r.
   gic_step_snd_rpl(gic, q, CoreSender c, gic')
/\ Rpl_PAdr q IN RPAR.Amap GICV
==>
(Q gic' (SGI (id, s, r)) = Q gic (SGI (id, s, r)))
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC gic_gicv_rpl_axiom >>
  PAT_X_ASSUM ``!pir. Q gic' pir = X`` 
              (fn thm => ASSUME_TAC ( SPEC ``(SGI (id, s, r))`` thm )) >>
  ASM_REWRITE_TAC [] >>
  IF_CASES_TAC 
  >| [(* SGI not PIR -> show contradiction *)
      FULL_SIMP_TAC (srw_ss()) [GSYM pairTheory.PEXISTS_THM]
      ,
      (* Q unchanged *)
      REWRITE_TAC []
     ]
);


val gicv_rpl_Q_pir_lem = store_thm("gicv_rpl_Q_pir_lem", ``
!gic q c gic' id.
   gic_step_snd_rpl(gic, q, CoreSender c, gic')
/\ Rpl_PAdr q IN RPAR.Amap GICV
/\ Q gic' (PIR id) <> Q gic (PIR id)
==>
(Q gic' (PIR id) IN {INACTIVE; PENDING})
``,
  RW_TAC (srw_ss()) [] >>
  IMP_RES_TAC gic_gicv_rpl_axiom >>
  PAT_X_ASSUM ``!pir. Q gic' pir = X`` 
              (fn thm => ASSUME_TAC ( SPEC ``PIR id`` thm )) >>
  ASM_REWRITE_TAC [] >>
  IF_CASES_TAC 
  >| [(* PIR -> check all case combinations *)
      FULL_SIMP_TAC (srw_ss()) [LET_DEF] >>
      CASE_TAC  >> (
          CASE_TAC >> (
	      FULL_SIMP_TAC (srw_ss()) []
	  )
      )
      ,
      (* Q unchanged -> contradiction *)
      FULL_SIMP_TAC (srw_ss()) []
     ]
);


(**************** Memory steps *****************)

(**** uninterpreted memory model ****)

(* memory transition relations

   mem_step_rcv_rpl(m,q,id,m') - receive MMIO reply q for sender id
   mem_step_rcv_req(m,r,id,m') - receive memory request r from sender id
   mem_step_snd_req(m,r,id,m') - forward MMIO request r to peripheral / GIC 
		                 from sender id
   mem_step_snd_rpl(m,q,id,m') - send/forward reply q to sender id
   mem_step_internal(m,id,m') - perform internal step on behalf of sender id

   Internal steps are tied to specific sender of request thats handled in order
   to couple with corresponding ideal memory, could do the same for GIC if it
   had internal actions
*) 
val _ = new_constant("mem_step_rcv_rpl", 
		     ``:memory # reply # senderID # memory -> bool``);
val _ = new_constant("mem_step_rcv_req", 
		     ``:memory # request # senderID # memory -> bool``);
val _ = new_constant("mem_step_snd_req", 
		     ``:memory # request # senderID # memory -> bool``);
val _ = new_constant("mem_step_snd_rpl", 
		     ``:memory # reply # senderID # memory -> bool``);
val _ = new_constant("mem_step_internal", 
		     ``:memory # senderID # memory -> bool``);

(* mem_step(m,a, go, m') - 
   perform action a on memory m resulting in m', go is only used by internal
   steps in the ideal model in order to determine if the sender id is valid
   within the current guest, for refined memory it should always be NONE

   RCV (SRPL q id) - receive MMIO reply q for sender id
   RCV (SREQ r id) - receive memory request from sender id
   SEND (SREQ r id) - forward MMIO request r from sender id
   SEND (SRPL q id) - send memory/forward MMIO reply to sender id
   TAU - pick a valid sender wrt guest go, and perform a corresponding internal 
         step on behalf of one of its pending requests
*)
val mem_step_def = Define `
mem_step (m : memory, a : Action, go: num option, m' : memory) =
	case a of
          | RCV (SRPL r id) => mem_step_rcv_rpl(m,r,id,m')
          | RCV (SREQ r id) => mem_step_rcv_req(m,r,id,m')
          | SEND (SREQ r id) => mem_step_snd_req(m,r,id,m')
          | SEND (SRPL r id) => mem_step_snd_rpl(m,r,id,m')
          | TAU => ?id. valid_sender_ go id /\ mem_step_internal(m,id,m')
          | _   => F
`;

(* memory invariant:
   - sent MMIO requests are for GIC or peripheral
   - received MMIO replies:
     - are from GIC or peripheral,
     - match a received MMIO request
     - not have a corresponding sent request pending at the same time
   - all requests and replies received by the memory match uniquely
 *)
val inv_good_mem_def = Define `inv_good_mem (m:memory) = 
   (!r id. (r,id) IN (mem_req_sent m) ==> 
           (r,id) IN (mem_req_rcvd m) /\ PAdr r IN A_gicper)
/\ (!q id. (q,id) IN (mem_rpl_rcvd m) ==> 
        good_rpl q
     /\ (?r. (r,id) IN (mem_req_rcvd m) /\ match(r,q) /\ PAdr r IN A_gicper)
     /\ (!r. (r,id) IN (mem_req_sent m) ==> ~match(r,q)) )
/\ (!q q' r r' id. (q,id) IN (mem_rpl_rcvd m)
                /\ (q',id) IN (mem_rpl_rcvd m)
		/\ (r,id) IN (mem_req_rcvd m) /\ match(r,q)
		/\ (r',id) IN (mem_req_rcvd m) /\ match(r',q')
		==> ( (q=q') <=> (r=r') ) )
`;

(* semantics axioms *)

(* NOTE: the following semantics assume that memory is coherent, i.e., memory
abstraction only changes for writes, also internal steps have no visible effect
*)

(* mem_step_rcv_rpl(m,q,id,m') - receive MMIO reply q for sender id

   preconditions:
   - q matches a received MMIO request r from sender id
   - r targets the GIC or a peripheral
   - q is a well-formed reply

   postconditions:
   - (q,id) is added to the record of received MMIO replies
   - (r,id) is removed from the record of pending MMIO requests
   - the rest of the abstract state is unchanged
*)
val mem_rcv_rpl_axiom = new_axiom("mem_rcv_rpl_axiom", ``
!m q id m'. mem_step_rcv_rpl(m,q,id,m')
==>    
?r. 
   (r,id) IN mem_req_sent m /\ match(r,q)
/\ PAdr r IN A_gicper
/\ good_rpl q
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m)
/\ (mem_req_sent m' = mem_req_sent m DIFF {(r,id)})
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m UNION {(q,id)})
``);

(* mem_step_rcv_req(m,r,id,m') - receive memory request r from sender id

   preconditions:
   none assumed

   postconditions:
   - (r,id) is added to the record of received requests
   - the rest of the abstract state is unchanged
*)
val mem_rcv_req_axiom = new_axiom("mem_rcv_req_axiom", ``
!m r id m'. mem_step_rcv_req(m,r,id,m')
==>    
   (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m UNION {(r,id)})
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
``);

(* mem_step_snd_req(m,r,id,m') - forward MMIO request r for sender id

   preconditions:
   - r targets the GIC or a peripheral
   - (r,id) was received and is not currently pending / already sent
   - no reply for r was received yet (e.g., due to being sent earlier)

   postconditions:
   - (r,id) is added to the record of sent MMIO requests
   - the rest of the abstract state is unchanged
*)
val mem_snd_req_axiom = new_axiom("mem_snd_req_axiom", ``
!m r id m'. mem_step_snd_req(m,r,id,m')
==>
   PAdr r IN A_gicper
/\ (r,id) IN mem_req_rcvd m
/\ (r,id) NOTIN mem_req_sent m
/\ (!q. match(r,q) ==> (q,id) NOTIN mem_rpl_rcvd m)
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m)
/\ (mem_req_sent m' = mem_req_sent m UNION {(r,id)})
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
``);

(* mem_step_snd_rpl(m,q,id,m') - forward MMIO reply q to sender id

   preconditions:
   - q is a received MMIO reply
   - there exists a matching pending request r
   - r targets the GIC or a peripheral
   - q is well-formed 

   postconditions:
   - (r,id) is removed from the record of pending memory requests
   - (q,id) is removed from the record of received MMIO replies
   - the rest of the abstract state is unchanged
*)
val mem_io_fw_axiom = new_axiom("mem_io_fw_axiom", ``
!m q id m'. mem_step_snd_rpl(m,q,id,m') /\ (q,id) IN mem_rpl_rcvd m
==>
?r.
   (r,id) IN mem_req_rcvd m /\ match(r,q) /\ PAdr r IN A_gicper
/\ good_rpl q
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m DIFF {(r,id)})
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m DIFF {(q,id)})
``);

(* mem_step_snd_rpl(m,q,id,m') - send read reply q to sender id

   preconditions:
   - q is not a received MMIO reply
   - q is a read of d bytes of address a returning value v
   - there exists a matching pending request r
   - r does not target the GIC or a peripheral

   postconditions:
   - (r,id) is removed from the record of pending memory requests
   - v is the memory contents of d contiguous bytes starting at address a
   - the rest of the abstract state is unchanged
*)
val mem_read_axiom = new_axiom("mem_read_axiom", ``
!m q id m' a d v i. mem_step_snd_rpl(m,q,id,m') 
         /\ (q,id) NOTIN mem_rpl_rcvd m
	 /\ (q = ReadValue (Read a d i) v)
==>
?r.
   (r,id) IN mem_req_rcvd m /\ match(r,q) /\ PAdr r NOTIN A_gicper
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m DIFF {(r,id)})
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
/\ (v = w2v (mem_read (mem_abs m) (Adr r) d))
``);

(* mem_step_snd_rpl(m,q,id,m') - send page table lookup reply q to MMU of id

   preconditions:
   - q is not a received MMIO reply
   - q is a page table lookup of at address a returning value v
   - there exists a matching pending request r
   - r does not target the GIC or a peripheral

   postconditions:
   - (r,id) is removed from the record of pending memory requests
   - v is the memory contents of 8 contiguous bytes starting at address a
   - the rest of the abstract state is unchanged
*)
val mem_walk_axiom = new_axiom("mem_walk_axiom", ``
!m q id m' a v i. mem_step_snd_rpl(m,q,id,m') 
         /\ (q,id) NOTIN mem_rpl_rcvd m
	 /\ (q =  WalkResult (Walk a i) v)
==>
?r.
   (r,id) IN mem_req_rcvd m /\ match(r,q) /\ PAdr r NOTIN A_gicper
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m DIFF {(r,id)})
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
/\ (v = mem_read (mem_abs m) (Adr r) 8)  
``);

(* page_write(pg,a,d,v) = pg' - update d contiguous bytes at address a in page
pg with value v, resulting in page pg'

only defined for d=1,2,4,8, otherwise no effect

TODO: bit_field_insert only defined if a is aligned, prove lemma? 
*)
val page_write_def = Define `page_write (pg:PAGE, a : bool[12], d, v:bitstring) =
case d of 
  | 1 => bit_field_insert (w2n a + 7) (w2n a) (v2w v:bool[8]) pg
  | 2 => bit_field_insert (w2n a + 15) (w2n a) (v2w v:bool[16]) pg
  | 4 => bit_field_insert (w2n a + 31) (w2n a) (v2w v:bool[32]) pg
  | 8 => bit_field_insert (w2n a + 63) (w2n a) (v2w v:bool[64]) pg
  | _ => pg
`;

(* mem_step_snd_rpl(m,q,id,m') - send write reply q to sender id

   preconditions:
   - q is not a received MMIO reply
   - q is a write of d bytes at address with value v
   - there exists a matching pending request r
   - r does not target the GIC or a peripheral

   postconditions:
   - (r,id) is removed from the record of pending memory requests
   - the memory is updated with the corresponding modified page, 
     where only the targeted bytes changed to v
     TODO: this could be simplified by stating the effect directly 
           in terms of the memory abstraction
   - the rest of the abstract state is unchanged
*)
val mem_write_axiom = new_axiom("mem_write_axiom", ``
!m q id m' a d v i pg. mem_step_snd_rpl(m,q,id,m') 
         /\ (q,id) NOTIN mem_rpl_rcvd m
	 /\ (q = WrittenValue (Write a d v i))
	 /\ (pg = page_write((mem_abs m) ((47><12) a), (11><0) a, d, v))
==>
?r m''.
   (r,id) IN mem_req_rcvd m /\ match(r,q) /\ PAdr r NOTIN A_gicper
/\ (m'' = memory_upd ((47><12)a, pg) m)
/\ (mem_req_rcvd m' = mem_req_rcvd m'' DIFF {(r,id)})
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m'')
/\ (mem_abs m' = mem_abs m'')
``);

(* mem_step_snd_rpl(m,q,id,m') - send fault reply q to sender id

   preconditions:
   - q is a fault that was received as an MMIO reply

   postconditions:
   no additional restrictions than what is already defined above
  
   We never raise memory faults, unless forwarded from a peripheral or the GIC.
   This is a simplification: we do not consider parity/CRC faults, tampering;
   access to memory holes are prevented by the hypervisor/MMU
 *)
val mem_fault_axiom = new_axiom("mem_fault_axiom", ``
!m q id m'. mem_step_snd_rpl(m,q,id,m') /\ Frpl q
==>
(q,id) IN mem_rpl_rcvd m
``);


(* mem_step_snd_rpl(m,id,m') - internal step on behalf of sender id

   preconditions:
   - there exists a pending request r of sender id
   - r does not target the GIC or a peripheral

   postconditions:
   - the abstract state is unchanged

   Internal steps have no visible effect, if memory coherency can be broken,
   this can be exposed here, however the effects would have to be coupled with
   the ideal model through a bisimuation obligation.
*)
val mem_internal_axiom = new_axiom("mem_internal_axiom", ``
!m id m'. mem_step_internal(m,id,m')
==>    
   (?r. (r,id) IN mem_req_rcvd m /\ PAdr r NOTIN A_gicper)
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m)
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
``);

(* 
TODO?: lemma that memory abstraction changes only for writes
*) 

(* liveness / enabled axioms *)

(* enabling specification:
   
   an MMIO reply q must be receivable if:
   - there is a matching request pending as sent

   TODO: add necessary precondition about Agicper
*)
val mem_rcv_rpl_enabled_axiom = new_axiom("mem_rcv_rpl_enabled_axiom", ``
!m q r id. (r,id) IN mem_req_sent m /\ match(r,q)
==> 
?m'. mem_step_rcv_rpl(m,q,id,m')
``);

(* enabling specification: 

   the memory may receive any request at any time.

   Note that we do not consider duplicate requests from the same sender here as
   the cores send only one request at a time anyway. Also we assume that an
   instantiation will add serial numbers to memory requests so that each request
   is uniquely identified in the system.
*)
val mem_rcv_req_enabled_axiom = new_axiom("mem_rcv_req_enabled_axiom", ``
!m r id. ?m'. mem_step_rcv_req(m,r,id,m')
``);

(* enabling specification:

   sending an MMIO request r for sender id is possible if:
   - r was received by the memory from sender id
   - r was not yet sent
   - no matching reply was received yet
   - r targets the GIC or a peripheral
*)
val mem_snd_req_enabled_axiom = new_axiom("mem_snd_req_enabled_axiom", ``
!m r id. (r,id) IN mem_req_rcvd m       
      /\ (r,id) NOTIN mem_req_sent m
      /\ (!q. (q,id) IN mem_rpl_rcvd m ==> ~match(r,q))
      /\ PAdr r IN A_gicper
==>
?m'. mem_step_snd_req(m,r,id,m')
``);

(* enabling specification:

   sending an reply q to sender id is always possible if:
   - a matching request r was received by the memory from sender id
   - if r targets the GIC or a peripheral, then q was received earlier 
   - if r is not an MMIO request but a read / PT walk:
     - the returned value matches the contents in the abstract state
*)
val mem_snd_rpl_enabled_axiom = new_axiom("mem_snd_rpl_enabled_axiom", ``
!m q id. (?r. (r,id) IN mem_req_rcvd m /\ match(r,q)
	   /\ if PAdr r IN A_gicper
	      then (q,id) IN mem_rpl_rcvd m 
	      else (Rreq r \/ PTreq r) ==> 
		   (Rpl_val q = mem_read (mem_abs m) (Adr r) (SzOf r)) ) 
==>
?m'. mem_step_snd_rpl(m,q,id,m')
``);

(* enabling specification:

   internal steps are always possible for sender id if:
   - a matching request r was received by the memory from sender id
   - if r does not target the GIC or a peripheral
*)
(* internal steps possible for all senders that have requests present *)
val mem_internal_enabled_axiom = new_axiom("mem_internal_enabled_axiom", ``
!m id. (?r. (r,id) IN mem_req_rcvd m /\ PAdr r NOTIN A_gicper)
==>
?m'. mem_step_internal(m,id,m')
``);

(* Axiom: the memory only sends well-formed replies

   TODO: it should be possible to prove this explicitly from the specs 
*)
val good_mem_rpl_axiom = new_axiom("good_mem_rpl_axiom", ``
!m q id m'. inv_good_mem m /\ mem_step_snd_rpl (m,q,id,m')
==>
good_rpl q
``);

(* memory lemmas *)
val mem_acc_not_sent_lem = store_thm("mem_acc_not_sent_lem", ``
!m q id m'. 
   inv_good_mem m
/\ mem_step_snd_rpl(m,q,id,m') 
/\ (q,id) NOTIN mem_rpl_rcvd m
==>
(!r. (r,id) IN mem_req_sent m ==> ~match(r,q))
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC good_mem_rpl_axiom THEN
  `PAdr r IN A_gicper` by (
      FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN  
      METIS_TAC []
  ) THEN 
  FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem] 
  THENL[(* case: read reply *)
	`?r'. PAdr r' NOTIN A_gicper /\ match (r',q)` by (
	    IMP_RES_TAC mem_read_axiom THEN 
	    METIS_TAC []
	) THEN 
	CCONTR_TAC THEN 
	RW_TAC (srw_ss()) [] THEN 
        IMP_RES_TAC match_PAdr_eq_lem THEN 			     
	METIS_TAC [],
	(* case: write reply *)
	`?r'. PAdr r' NOTIN A_gicper /\ match (r',q)` by (
	    IMP_RES_TAC mem_write_axiom THEN 
	    METIS_TAC []
	) THEN 
	CCONTR_TAC THEN
	RW_TAC (srw_ss()) [] THEN
        IMP_RES_TAC match_PAdr_eq_lem THEN 			     
	METIS_TAC [],
	(* case: walk reply *)
	`?r'. PAdr r' NOTIN A_gicper /\ match (r',q)` by (
	    IMP_RES_TAC mem_walk_axiom THEN 
	    METIS_TAC []
	) THEN 
	CCONTR_TAC THEN
	RW_TAC (srw_ss()) [] THEN
        IMP_RES_TAC match_PAdr_eq_lem THEN 			     
	METIS_TAC [],
	(* case: fault reply - forwarded from IO - contradiction *)
	`Frpl q` by ( FULL_SIMP_TAC (srw_ss()) [Frpl_def] ) THEN 
	IMP_RES_TAC mem_fault_axiom
       ]
);

(* former axiom, now proved *)
val inv_good_mem_axiom = store_thm("inv_good_mem_axiom", ``
!m a m' go. inv_good_mem m /\ mem_step(m,a,go,m') ==> inv_good_mem m'
``,
  REPEAT STRIP_TAC THEN 				   
  Cases_on `a` THEN ( RW_TAC (srw_ss()) [mem_step_def] )
  THENL [(* case: send *)
	 Cases_on `M` THEN ( 
	     FULL_SIMP_TAC (srw_ss()) [mem_step_def] 
	 )
	 THENL[(* case: send req *)
	       FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN  
	       IMP_RES_TAC mem_snd_req_axiom THEN 
	       FULL_SIMP_TAC (srw_ss()) [] THEN 
	       METIS_TAC [pred_setTheory.IN_UNION, pred_setTheory.IN_SING],
	       (* case: send rpl *)
	       IMP_RES_TAC good_mem_rpl_axiom THEN 
	       Cases_on `(r,s) IN mem_rpl_rcvd m`
	       THEN1 (
	           (* case: forward IO reply *)
	           FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN 
	       	   IMP_RES_TAC mem_io_fw_axiom THEN 
	           FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
					 pred_setTheory.IN_SING] THEN 
		   RW_TAC (srw_ss()) [] THEN ( TRY ( METIS_TAC [] ) )
	       ) THEN 
	       (* case: memory access or fwd fault *)
	       FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem] 
	       THENL[(* case: read reply *)
	             FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN 
	             IMP_RES_TAC mem_read_axiom THEN 
	             FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
		     			   pred_setTheory.IN_SING] THEN 
		     RW_TAC (srw_ss()) [] THEN ( 
		         TRY ( METIS_TAC [pred_setTheory.IN_DIFF, 
		     			pred_setTheory.IN_SING, 
		     			mem_acc_not_sent_lem, 
		     			match_diff_lem, 
		     			unique_match_thm] ) ) THEN
		     RES_TAC THEN 
		     FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
		     			   pred_setTheory.IN_SING] THEN 
		     METIS_TAC [mem_acc_not_sent_lem, match_diff_lem]
		     ,
		     (* case: write reply *)
		     FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN 
	             IMP_RES_TAC mem_write_axiom THEN 
	             FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
		     			   pred_setTheory.IN_SING] THEN 
		     RW_TAC (srw_ss()) [] THEN ( 
		         TRY ( METIS_TAC [pred_setTheory.IN_DIFF, 
		     			  pred_setTheory.IN_SING, 
		     			  mem_acc_not_sent_lem, 
		     			  match_diff_lem, 
		     			  unique_match_thm] ) THEN 
		       RES_TAC ) THEN_LT
		     LASTGOAL ( METIS_TAC [unique_match_thm, 
					   mem_acc_not_sent_lem, 
		     			   match_diff_lem, memory_upd_axiom] )
		     THEN (
		         FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
		     			       pred_setTheory.IN_SING] THEN 
		         METIS_TAC [unique_match_thm, mem_acc_not_sent_lem, 
		     		    match_diff_lem, memory_upd_axiom]
		     )		         
		     ,
		     (* case: walk reply *)
	             FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN 
	             IMP_RES_TAC mem_walk_axiom THEN 
	             FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
		     			   pred_setTheory.IN_SING] THEN 
		     RW_TAC (srw_ss()) [] THEN ( 
		         TRY ( METIS_TAC [pred_setTheory.IN_DIFF, 
		     			  pred_setTheory.IN_SING, 
		     			  mem_acc_not_sent_lem, 
		     			  match_diff_lem, 
		     			  unique_match_thm] ) ) THEN
		     RES_TAC THEN 
		     FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, 
		     			   pred_setTheory.IN_SING] THEN 
		     METIS_TAC [mem_acc_not_sent_lem, match_diff_lem]
		     ,
		     (* case: fault reply - forwarded from IO - contradiction *)
		     `Frpl r` by ( FULL_SIMP_TAC (srw_ss()) [Frpl_def] ) THEN 
		     IMP_RES_TAC mem_fault_axiom
		    ]
	      ]
         ,
	 (* case: receive req / reply *)
	 Cases_on `M` THEN ( 
	     FULL_SIMP_TAC (srw_ss()) [mem_step_def] 
	 )
	 THENL[(* case: receive req *)
	       FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN  
	       IMP_RES_TAC mem_rcv_req_axiom THEN 
	       RW_TAC (srw_ss()) [] THEN 	       
	       TRY ( METIS_TAC [pred_setTheory.IN_UNION, 
				pred_setTheory.IN_SING,	  
				match_diff_lem, 
		     		unique_match_thm] ) 
	       ,
	       (* case: receive reply *)
	       FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN  
	       IMP_RES_TAC mem_rcv_rpl_axiom THEN 
	       RW_TAC (srw_ss()) [] THEN 	       
	       TRY ( METIS_TAC [pred_setTheory.IN_DIFF,
			        pred_setTheory.IN_UNION, 
				pred_setTheory.IN_SING,	  
				match_diff_lem, 
		     		unique_match_thm] )
	      ] 
         ,
	 (* case: internal *)
	 FULL_SIMP_TAC (srw_ss()) [mem_step_def] THEN 
	 IMP_RES_TAC mem_internal_axiom THEN 
	 FULL_SIMP_TAC (srw_ss()) [inv_good_mem_def] THEN 
	 METIS_TAC [] 
	]
);

val mem_rpl_rcvd_lem = store_thm("mem_rpl_rcvd_lem", ``
!q id m. inv_good_mem m /\ (q,id) IN mem_rpl_rcvd m ==> Rpl_PAdr q IN A_gicper
``,
  RW_TAC (srw_ss()) [inv_good_mem_def] THEN 
  RES_TAC THEN 
  IMP_RES_TAC match_PAdr_eq_lem THEN 
  METIS_TAC []
);

val mem_walk_lem = store_thm("mem_walk_lem", ``
!m q id m' r. mem_step_snd_rpl(m,q,id,m') 
         /\ (q,id) NOTIN mem_rpl_rcvd m
	 /\ PTreq r
         /\ match(r,q)
==>
   (r,id) IN mem_req_rcvd m /\ match(r,q) /\ PAdr r NOTIN A_gicper
/\ (mem_abs m' = mem_abs m)
/\ (mem_req_rcvd m' = mem_req_rcvd m DIFF {(r,id)})
/\ (mem_req_sent m' = mem_req_sent m)
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
/\ (Rpl_val q = mem_read (mem_abs m) (Adr r) 8)  
``,
  REPEAT GEN_TAC THEN 
  STRIP_TAC THEN 
  `~Frpl q` by (
      CCONTR_TAC THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      METIS_TAC [mem_fault_axiom]
  ) THEN 
  `?i v. q = WalkResult (Walk (Adr r) i) v` by (
      METIS_TAC [PTreq_match_lem]
  ) THEN 
  IMP_RES_TAC mem_walk_axiom THEN 
  `r = r'` by (
      IMP_RES_TAC unique_match_thm
  ) THEN 
  FULL_SIMP_TAC (srw_ss()) [Rpl_val_def, wordsTheory.w2w_id]
);

val mem_aligned_unchanged_lem = store_thm("mem_aligned_unchanged_lem", ``
!m q id m' r. mem_step_snd_rpl(m,q,id,m') 
         /\ (q,id) NOTIN mem_rpl_rcvd m
	 /\ req_aligned r
         /\ match(r,q)
==>
(!a. a <> PAdr r ==> (mem_abs m' a = mem_abs m a))
``,
  REPEAT STRIP_TAC >>
  Cases_on `r` >> (
      Cases_on `q` >> (
          FULL_SIMP_TAC (srw_ss()) [match_def]
      )
  )>|[(* case: read *)
      METIS_TAC [mem_read_axiom]
      ,
      (* case: read fault *)
      `Frpl (Fault (Read c n m'') f)` by ( RW_TAC (srw_ss()) [Frpl_def] ) >>
      METIS_TAC [mem_fault_axiom]
      ,
      (* case: write *)
      `mem_abs m' a = mem_abs (memory_upd ((47><12) c, 
					   page_write(mem_abs m ((47><12) c), 
						      (11><0) c, n, l))
					  m) a` by (
          METIS_TAC [mem_write_axiom]
      ) >>
      FULL_SIMP_TAC (srw_ss()) [PAdr_def, Adr_def] >>
      METIS_TAC [memory_upd_axiom]
      ,
      (* case: write fault *)
      `Frpl (Fault (Write c n l m'') f)` by ( RW_TAC (srw_ss()) [Frpl_def] ) >>
      METIS_TAC [mem_fault_axiom]
      ,
      (* case: walk *)
      METIS_TAC [mem_walk_axiom]
      , 
      (* case: walk fault *)
      `Frpl (Fault (Walk c m'') f)` by ( RW_TAC (srw_ss()) [Frpl_def] ) >>
      METIS_TAC [mem_fault_axiom]
     ]
);

val mem_unchanged_lem = store_thm("mem_unchanged_lem", ``
!m q id m' r A. mem_step_snd_rpl(m,q,id,m') 
         /\ (q,id) NOTIN mem_rpl_rcvd m
	 /\ req_aligned r
         /\ match(r,q)
	 /\ (PAdr r NOTIN A \/ ~Wreq r)
==>
(!a. a IN A ==> (mem_abs m' a = mem_abs m a))
``,
  REPEAT STRIP_TAC 
  >| [(* case: different address *)
      `a <> PAdr r` by (
          CCONTR_TAC >>
	  FULL_SIMP_TAC (srw_ss()) []
      ) >>
      METIS_TAC [mem_aligned_unchanged_lem]
      ,
      (* case: not write *)
      Cases_on `r` >> (
          Cases_on `q` >> (
              FULL_SIMP_TAC (srw_ss()) [match_def]
	  )
      )
      >|[(* case: read *)
         METIS_TAC [mem_read_axiom]
         ,
	 (* case: read fault *)
	 `Frpl (Fault (Read c n m'') f)` by ( RW_TAC (srw_ss()) [Frpl_def] ) >>
	 METIS_TAC [mem_fault_axiom]
         ,
	 (* case: write *)
         FULL_SIMP_TAC (srw_ss()) [Wreq_def]
         ,
	 (* case: write fault *)
         FULL_SIMP_TAC (srw_ss()) [Wreq_def]
         ,
	 (* case: walk *)
	 METIS_TAC [mem_walk_axiom]
         , 
	 (* case: walk fault *)
	 `Frpl (Fault (Walk c m'') f)` by ( RW_TAC (srw_ss()) [Frpl_def] ) >>
	 METIS_TAC [mem_fault_axiom]
	]
     ]
);

val mem_no_fw_lem = store_thm("mem_no_fw_lem", ``
!m q id m'. mem_step_snd_rpl(m,q,id,m') /\ Rpl_PAdr q NOTIN A_gicper
==>
(q,id) NOTIN mem_rpl_rcvd m
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC mem_io_fw_axiom >>
  IMP_RES_TAC match_PAdr_eq_lem >>
  FULL_SIMP_TAC (srw_ss()) []
);

val mem_fw_lem = store_thm("mem_fw_lem", ``
!m r q id m'. mem_step_snd_rpl(m,q,id,m') /\ match(r,q) /\ PAdr r IN A_gicper
==>
(q,id) IN mem_rpl_rcvd m
``,
  REPEAT STRIP_TAC >>
  CCONTR_TAC >>
  IMP_RES_TAC good_match_lem >>
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
      `Frpl q` by ( RW_TAC std_ss [Frpl_def] ) >>
      IMP_RES_TAC mem_fault_axiom
     ]
);


(* merge all step axioms on mem_step_snd_rpl for non-forwarding replies *)
val mem_step_snd_rpl_merged_lem =
     store_thm("mem_step_snd_rpl_merged_lem",
       ``!m q id m'. mem_step_snd_rpl (m,q,id,m') /\ (q,id) NOTIN mem_rpl_rcvd m /\ (?r0. match(r0,q))
           ==>
            ?r.
              (r,id) IN mem_req_rcvd m /\ match (r,q) /\
              (mem_req_rcvd m' = mem_req_rcvd m DIFF {(r,id)}) /\
              (mem_req_sent m' = mem_req_sent m) /\
              (mem_rpl_rcvd m' = mem_rpl_rcvd m)``,
            RW_TAC (srw_ss()) []
       THEN Cases_on `q`
       THEN Cases_on `r0`
       THEN FULL_SIMP_TAC (srw_ss()) [match_def]
       THEN MAP_EVERY IMP_RES_TAC [mem_write_axiom, mem_read_axiom, mem_walk_axiom, mem_fault_axiom]
       THEN FULL_SIMP_TAC (srw_ss()) [Frpl_def, match_def]
       THEN METIS_TAC [memory_upd_axiom, mem_acc_not_sent_lem]);


(* slightly different *)
val mem_snd_rpl_merged_lem = store_thm("mem_snd_rpl_merged_lem",``
!m r q id m'. 
   mem_step_snd_rpl (m,q,id,m') 
/\ (q,id) NOTIN mem_rpl_rcvd m 
/\ match(r,q)
==>
   (r,id) IN mem_req_rcvd m 
/\ (mem_req_rcvd m' = mem_req_rcvd m DIFF {(r,id)}) 
/\ (mem_req_sent m' = mem_req_sent m) 
/\ (mem_rpl_rcvd m' = mem_rpl_rcvd m)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC mem_step_snd_rpl_merged_lem >>
  `r = r'` by ( METIS_TAC [unique_match_thm] ) >>
  METIS_TAC []
);

(* same as mem_step_snd_rpl_merged_lem, but based on good_rpl and ReqOf *)
val mem_step_snd_rpl_merged_lem' =
     store_thm("mem_step_snd_rpl_merged_lem'",
       ``!m q id m'. mem_step_snd_rpl (m,q,id,m') /\ (q,id) NOTIN mem_rpl_rcvd m /\ good_rpl q
           ==>
              (ReqOf q,id) IN mem_req_rcvd m /\ match (ReqOf q,q) /\
              (mem_req_rcvd m' = mem_req_rcvd m DIFF {(ReqOf q,id)}) /\
              (mem_req_sent m' = mem_req_sent m) /\
              (mem_rpl_rcvd m' = mem_rpl_rcvd m)``,
       REPEAT GEN_TAC >>
       REPEAT DISCH_TAC >>
       FULL_SIMP_TAC pure_ss [good_match_ReqOf_lem] >>
       IMP_RES_TAC good_rpl_cases_lem >>
       FULL_SIMP_TAC pure_ss [] >>
       MAP_EVERY IMP_RES_TAC (map UNIQUE_REQ [mem_write_axiom, mem_read_axiom, mem_walk_axiom, mem_fault_axiom]) >>
       FULL_SIMP_TAC bool_ss [Frpl_def] >>
       METIS_TAC [memory_upd_axiom]);


(* merge all step axioms on mem_step_snd_rpl,
  including both forwarding and non-forwarding replies *)
val mem_step_snd_rpl_fully_merged_lem =
     store_thm("mem_step_snd_rpl_fully_merged_lem",
       ``!m q id m'. mem_step_snd_rpl (m,q,id,m') /\ good_rpl q
           ==>
              (ReqOf q,id) IN mem_req_rcvd m /\ match (ReqOf q,q) /\
              (mem_req_rcvd m' = mem_req_rcvd m DIFF {(ReqOf q,id)}) /\
              (mem_req_sent m' = mem_req_sent m) /\
              (mem_rpl_rcvd m' = if (q,id) IN mem_rpl_rcvd m then mem_rpl_rcvd m DIFF {(q,id)} else  mem_rpl_rcvd m) /\
              ((q,id) IN mem_rpl_rcvd m ==> PAdr (ReqOf q) IN A_gicper /\ (mem_abs m' = mem_abs m))``,
       REPEAT GEN_TAC >>
       REPEAT DISCH_TAC >>
       Cases_on `(q,id) IN mem_rpl_rcvd m` >|
       [(* forwarding *)
        METIS_TAC [UNIQUE_REQ mem_io_fw_axiom],
        (* non-forwarding *)
        METIS_TAC [mem_step_snd_rpl_merged_lem']
       ]);

val mem_step_snd_rpl_fully_merged_diff_lem =
     store_thm("mem_step_snd_rpl_fully_merged_diff_lem",
       ``!m q id m'. mem_step_snd_rpl (m,q,id,m') /\ good_rpl q
           ==>
              (ReqOf q,id) IN mem_req_rcvd m /\ match (ReqOf q,q) /\
              (mem_req_rcvd m' = mem_req_rcvd m DIFF {(ReqOf q,id)}) /\
              (mem_req_sent m' = mem_req_sent m) /\
              (mem_rpl_rcvd m' = mem_rpl_rcvd m DIFF {(q,id)}) /\
              ((q,id) IN mem_rpl_rcvd m ==> PAdr (ReqOf q) IN A_gicper /\ (mem_abs m' = mem_abs m))``,
       REPEAT STRIP_TAC >> 
       IMP_RES_TAC mem_step_snd_rpl_fully_merged_lem >> 
       METIS_TAC [GSYM pred_setTheory.DELETE_DEF, pred_setTheory.IN_DELETE, pred_setTheory.EXTENSION]);


val mem_step_snd_rpl_fully_merged_del_lem =
     store_thm("mem_step_snd_rpl_fully_merged_del_lem",
       ``!m q id m'. mem_step_snd_rpl (m,q,id,m') /\ good_rpl q
           ==>
              (ReqOf q,id) IN mem_req_rcvd m /\ match (ReqOf q,q) /\
              (mem_req_rcvd m' = mem_req_rcvd m DELETE (ReqOf q,id)) /\
              (mem_req_sent m' = mem_req_sent m) /\
              (mem_rpl_rcvd m' = mem_rpl_rcvd m DELETE (q,id)) /\
              ((q,id) IN mem_rpl_rcvd m ==> PAdr (ReqOf q) IN A_gicper /\ (mem_abs m' = mem_abs m))``,
       REPEAT STRIP_TAC >> 
       IMP_RES_TAC mem_step_snd_rpl_fully_merged_lem >> 
       METIS_TAC [GSYM pred_setTheory.DELETE_DEF, pred_setTheory.IN_DELETE, pred_setTheory.EXTENSION]);

(*************** finish ***********)

val _ = export_theory();
