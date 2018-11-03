(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib;
open blastLib;
open tacticsLib;

open axtypesTheory;
open haspoctypesTheory;

open math_lemmasTheory;
open annotationsLib; infix //; infix ///; infix -:;
open pred_setTheory;

val _ = new_theory "parameters";


(******************  address functions   **************)

(* some helper functions for address arithmetic and sets of addresses *)

(* logarithmic size of a set, i.e.:
   how many bits are needed to address its elements *)
val log_sz_def = Define `log_sz s = 
if CARD s <= 1 then 0 else LOG 2 (CARD s - 1) + 1
`;

(* Lemma: log_sz is a sound over-approximation *)
val log_sz_gt = store_thm ("log_sz_gt",
``CARD s <= 2 ** log_sz s``,

Cases_on `CARD s <= 1` THEN (
  ASM_SIMP_TAC arith_ss [log_sz_def]
) THEN
`(CARD s = SUC (CARD s - 1)) /\ (0 < (CARD s - 1))` by DECIDE_TAC  THEN
Q.ABBREV_TAC `cs = CARD s - 1` THEN
FULL_SIMP_TAC arith_ss [GSYM arithmeticTheory.ADD1, 
  GSYM arithmeticTheory.LESS_EQ, logrootTheory.LOG]);

(* Lemma: log_sz is the best fit *)
val log_sz_minimal = store_thm ("log_sz_minimal",
``!n. n < log_sz s ==> 2 ** n < CARD s``,

Cases_on `CARD s <= 1` THEN (
  ASM_SIMP_TAC arith_ss [log_sz_def]
) THEN
`(CARD s = SUC (CARD s - 1)) /\ (0 < (CARD s - 1))` by DECIDE_TAC  THEN
Q.ABBREV_TAC `cs = CARD s - 1` THEN
REPEAT STRIP_TAC THEN
`(2 ** n <= 2 ** LOG 2 cs) /\ (2 ** LOG 2 cs <= cs)` by 
  FULL_SIMP_TAC arith_ss [GSYM arithmeticTheory.ADD1, 
    GSYM arithmeticTheory.LESS_EQ_IFF_LESS_SUC, logrootTheory.LOG,
    logrootTheory.LOG_LE_MONO] THEN
ASM_SIMP_TAC arith_ss []);


(* the base address in a set of addresses, i.e.:
   the minimal address in that set,
   set to 0w if empty *)
val base_adr_def = Define `
   (base_adr s = if s = EMPTY then 0w:bool[36] else
                 n2w (MIN_SET (IMAGE w2n s)) :bool[36])
`;

(* Lemma: the base address of a set is from that set *)
val base_adr_in_set_lem =
    store_thm("base_adr_in_set_lem",
    ``!X. (X <> EMPTY) ==> base_adr X IN X``,

   FULL_SIMP_TAC std_ss [base_adr_def] THEN
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, GSYM LEFT_FORALL_IMP_THM,
     base_adr_def] THEN
   REPEAT STRIP_TAC THEN
   `MIN_SET (IMAGE w2n X) IN (IMAGE w2n X)`
       by METIS_TAC [pred_setTheory.IMAGE_IN, min_set_in_set_lem] THEN
   `(n2w:num -> bool[36]) (MIN_SET (IMAGE (w2n:bool[36] -> num) X)) IN 
    (IMAGE (n2w:num->bool[36]) (IMAGE w2n  X)) ` by 
       METIS_TAC [pred_setTheory.IMAGE_IN] THEN
   FULL_SIMP_TAC (srw_ss()) []);


(* a set of addresses is a contiguous memory region *)
val is_contiguous_def = Define `is_contiguous (s:bool[36] set) = 
!a. a IN s <=> (a >= base_adr s /\ a < base_adr s + n2w (CARD s))
`;

(* a set of addresses is aligned if its base address is aligned
   wrt. to the sets logarithmic size
   NOTE: the addresses may not be contiguous  *)
val is_aligned_def = Define `is_aligned (s:bool[36] set) = 
((log_sz s -1 >< 0)(base_adr s):bool[36] = 0w)
`;





(******************  PARAMETERS datatypes   **************)

(*******************************************************************************
params 

type of the ideal parameter data structure, components:
 - ng : number of guests
 - ns : number of IGC channels 
 - cpol(s)=(g,h) : communication channel policy, s is channel from guest g to h
 - igca(s)=(a,b) : channel s maps address a in g to address b in h
 - nc_g(g) : number of cores of guest g
 - pirq_gp(g)(p)=I : set of interrupts I belongs to peripheral p of guest g
 - id_igc(s) : interrupt number identified with notification for channels s
 - A_G(g) : the (intermediate physical) memory pages belonging to guest g
 - A_gp(g)(p) : the memory-mapped pages belonging to peripheral p of guest g 
*******************************************************************************)
val _ = Hol_datatype `params =
  <| ng: num;
     ns: num;
     cpol: num -> (num # num);
     igca: num -> (bool[36] # bool[36]);
     nc_g: num -> num;
     np_g: num -> num;
     pirq_gp: num -> num -> (irqID -> bool);
     id_igc: num -> num;
     A_G: num -> (bool[36] -> bool);
     A_gp: num -> num -> (bool[36] -> bool)
 |>`;


(* physical address region identifiers to be used in refined model
   ROM - code for the first stage boot loader and root key hash
   FLASH - where all other images (2nd stage boot loader, hypervisor) are stored
   MC - memory controller, which controls DRAM, initialized during boot
   SMMU - region where the SMMUs for restricting DMA are mapped
   BOOT - the memory used by the boot loader (code and data)
   HV - the hypervisor's memory (code and data)
   GUEST g - the physical RAM region for guest g
   PER p - the memory-mapped area for peripheral p
   GICC - the GIC interrupt core interface (also used ideal model) 
   GICD - the GIC interrupt distributor interface (also used ideal model) 
   GICH - the GIC interrupt virtualization interface (only used by hypervisor) 
   GICV - the GIC virtual interrupt interface (only exposed in refined model) 
*)
val _ = Datatype `AddressRegion = ROM | FLASH | MC | SMMU | BOOT | HV 
                                | GUEST num | PER num 
				| GICC | GICD | GICH | GICV`;

val AddressRegion_distinct = DB.fetch "-" "AddressRegion_distinct"
val AddressRegion_11 = DB.fetch "-" "AddressRegion_11"

(*******************************************************************************
refined_params 

type of the refined parameter data structure, components:
 - nc : number of cores (unbounded here, although max 8 for our platform)
 - np : number of peripherals 
 - pirq_p p : set of interrupts assignd for peripheral p
 - a_rkh : address of root key hash used during secure boot loader
 - Amap R : physical memory map, i.e., where is region R allocated
 - A_PT g : second level page table area for guest g
 - A_PPT g : SMMU page table area for peripherals of guest g
 - A_IGC g h : shared page location(s) for IGC channel from g to h 
	       (in practice singleton or empty set)
*******************************************************************************)
val _ = Hol_datatype `refined_params =
  <| nc: num; 
     np: num;
     pirq_p: num -> (irqID -> bool);
     a_rkh : bool[43];
     Amap : AddressRegion -> bool[36] set;
     A_PT : num -> bool[36] set;
     A_PPT : num -> bool[36] set;
     A_IGC : num -> num -> bool[36] set
 |>`;



(******************   AddressRegions                   **************)

(* guestAR A PAR - A is a guest address region according to PAR *)
val guestAR_def = Define `guestAR (a:AddressRegion, p:params) =
	(?g. (a=GUEST g) /\ g < p.ng)
                `;

(* perAR A RPAR - A is a peripheral address region according to RPAR *)
val perAR_def = Define `perAR (a:AddressRegion, p:refined_params) =
	(?per. (a=PER per) /\ per < p.np)
                `;
(* singleAR A RPAR - A is a special/single/system address region, 
   i.e., not guest or peripheral memory *)
val singleAR_def = Define `singleAR (a:AddressRegion) =
	(!x. (a<>GUEST x) /\ (a<>PER x))
                `;

(* gicAR A RPAR - A is an address region blonging to the GIC *)
val gicAR_def = Define `gicAR (a:AddressRegion) =
	((a = GICC) \/ (a = GICD) \/ (a = GICH) \/ (a = GICV))
                `;

(* singleAR rewrite, added by Thomas Tuerk *)
val singleAR_cases = store_thm ("singleAR_cases", ``!a. singleAR a <=>
  ((a = ROM) \/ (a = FLASH) \/ (a = MC) \/ (a = SMMU) \/
   (a = BOOT) \/ (a = HV) \/ gicAR a)``,
  Cases_on `a` THEN
  SIMP_TAC (srw_ss()) [singleAR_def, gicAR_def]
);


(* AddressRegion corollaries, added by Thomas Tuerk *)
val ARpred_implications = store_thm ("ARpred_implications",
  ``(!a. gicAR a ==> singleAR a) /\ 
    (!a p. gicAR a ==> ~(perAR (a, p))) /\ 
    (!a p. gicAR a ==> ~(guestAR (a, p))) /\
    (!a p p'. guestAR (a, p) ==> ~(perAR (a, p'))) /\
    (!a p. guestAR (a, p) ==> ~(singleAR a)) /\
    (!a p. guestAR (a, p) ==> ~(gicAR a)) /\
    (!a p p'. perAR (a, p) ==> ~(guestAR (a, p'))) /\
    (!a p. perAR (a, p) ==> ~(singleAR a)) /\
    (!a p. perAR (a, p) ==> ~(gicAR a)) /\
    (!a p. singleAR a ==> ~(perAR (a, p))) /\ 
    (!a p. singleAR a ==> ~(guestAR (a, p)))``,
  SIMP_TAC (srw_ss()) [guestAR_def, perAR_def, singleAR_def, gicAR_def,
  DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM]
);


(* AddressRegion rewrites, added by Thomas Tuerk *)
val ARpred_REWRITES = save_thm ("ARpred_REWRITES",
SIMP_RULE (std_ss++DatatypeSimps.expand_type_quants_ss [``:AddressRegion``] ++
     DatatypeSimps.type_rewrites_ss [``:AddressRegion``]) [] 
  (LIST_CONJ [singleAR_def, guestAR_def, perAR_def, gicAR_def]))

val _ = export_rewrites ["ARpred_REWRITES", "ARpred_implications"];



(******************   details parameters ideal model   **************)


(* abbreviations:
   igcin PAR g - incoming IGC channels of guest g 
   igcout PAR g - outgoing IGC channels of guest g
   pirq_g PAR g - peripheral interrupts in guest g
   ipirq_g PAR g - interprocessor interrupts in guest g
*)
val igcin_def = Define `igcin p g = 
(\s:num. s < p.ns /\ (?g':num. (g' < p.ng /\ (p.cpol(s) = (g',g)))))`;
val igcout_def = Define `igcout p g = 
(\s:num. s < p.ns /\ (?g':num. (g' < p.ng /\ (p.cpol(s) = (g,g')))))`;
val pirq_g_def = Define `pirq_g p g = 
BIGUNION (\s. (?pe. pe < (p.np_g g) /\ (s = p.pirq_gp g pe)))`; 
val ipirq_g_def = Define `ipirq_g p g = 
(\sgi. ?c c' id. (c < (p.nc_g g)) /\ (c' < (p.nc_g g)) 
              /\ (id <=+ 7w) /\ (sgi = SGI (id,c,c')))`;

(* address space corresponding to as_g parameter *)
val lin_add_space_def = Define `lin_add_space as_g = 
             \a:bool[36]. !i. (i < 36) ==> (i >= as_g) ==> (a ' i = F)`; 


(* assumptions on the parameters *)

val goodP_def = Define `goodP (PAR:params) (RPAR:refined_params) = 
 (* minimum_guests *)
 (0 < PAR.ng) /\
 (* minimum_cores *)
 (!g. g < PAR.ng ==> 0 < PAR.nc_g g) /\
 (* channel_source_bound *)
 (!s. (s < PAR.ns) ==> (FST(PAR.cpol s) < PAR.ng)) /\
 (* channel_target_bound *)
 (!s. (s < PAR.ns) ==> (SND(PAR.cpol s) < PAR.ng)) /\
 (* unique_channels *)
 (!s s'. (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s') 
         ==> (PAR.cpol(s) <> PAR.cpol(s'))) /\
 (* channel_nonreflexive *)
 (!s g. (s < PAR.ns) ==> PAR.cpol(s) <> (g,g)) /\
 (* unique_source_address,
    no outgoing channels share ICG memory region *)
 (!s s'.  (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s')
           ==> (FST(PAR.cpol s) = FST(PAR.cpol s')) 
           ==> (FST(PAR.igca s) <> FST(PAR.igca s'))) /\
 (* unique_target_address,
    no incoming channels share ICG memory region *)
 (!s s'.  (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s')
           ==> (SND(PAR.cpol s) = SND(PAR.cpol s')) 
           ==> (SND(PAR.igca s) <> SND(PAR.igca s'))) /\
 (* src_target_nand,
    no incoming channel shares IGC memory region with an outgoing channel *)
 (!s s'.  (s < PAR.ns) ==> (s' < PAR.ns) ==> (s <> s')
           ==> (FST(PAR.cpol s) = SND(PAR.cpol s')) 
           ==> (FST(PAR.igca s) <> SND(PAR.igca s'))) /\
 (* peripheral_interrupts, 
    TODO: add range for n? currently hardcoded in transition systems *) 
 (!g p i. (g < PAR.ng) ==> (p < PAR.np_g g)
          ==> (i IN (PAR.pirq_gp g p)) ==> (?n. i = PIR n)) /\
 (* igc_identifiers_disjoint,
    all incoming IGC channels og a guest have different notification IRQs *)
 (!g s s'. (g < PAR.ng) /\ (s < PAR.ns) /\ (s' < PAR.ns) /\ (s <> s')
        /\ (s IN (igcin PAR g)) /\ (s' IN (igcin PAR g)) 
	==> (PAR.id_igc s <> PAR.id_igc s')) /\
 (* igc_not_peripheral_interrupt,
    IGC notification IRQs are not mapped to existing peripheral IRQs *) 
 (!g s q. (g < PAR.ng)  /\ (s < PAR.ns)  /\ s IN (igcin PAR g)
       /\ (PIR q) IN (pirq_g PAR g) ==> (PAR.id_igc s <> q)) /\
 (* igc_pir_number,
    IGC notification interrupt identifiers are in the physical IRQ range *)
 (!s. (s < PAR.ns) ==> PAR.id_igc s >= 16 /\ PAR.id_igc s < 1020) /\
 (* good_source_address,
    outgoing IGC channels are allocated within guest memory *)
 (!s g g'. (g < PAR.ng) ==> (g' < PAR.ng) ==> (s < PAR.ns)
            ==> (PAR.cpol s = (g,g')) 
            ==> ((FST (PAR.igca s)) IN (PAR.A_G g))) /\
 (* good_target_address,
    incoming IGC channels are allocated within guest memory *)
 (!s g g'. (g < PAR.ng) ==> (g' < PAR.ng) ==> (s < PAR.ns)
           ==> (PAR.cpol s = (g,g')) 
           ==> ((SND (PAR.igca s)) IN (PAR.A_G g'))) /\
 (* peripheral_addresses, 
    guest memory includes associated memory mapped peripherals *)
 (!g p. (g < PAR.ng) ==> (p < PAR.np_g g) 
        ==> (PAR.A_gp g p) PSUBSET (PAR.A_G g)) /\
 (* peripherals_disjoint, 
    different peripherals are mapped to different addresses, even in different
    guests, the latter is added for simplicity of the proof, it allows mapping
    peripheral accesses to guests by their address *)
    (!g1 g2 p1 p2 a. (g1 < PAR.ng) ==> (g2 < PAR.ng) 
	             ==> (p1 < PAR.np_g g1) ==> (p2 < PAR.np_g g2) 
		     ==> a IN (PAR.A_gp g1 p1) ==> a IN (PAR.A_gp g2 p2)
		     ==> (g1 = g2) /\ (p1 = p2)) /\
 (* peripheral_guest_mem_disjoint,
    memory mapped peripherals are not located in other guests' RAM address
    space, again this is added for easier association of peripheral accesses
    with the corresponding guests *)
 (!g1 g2 p a. (g1 < PAR.ng) ==> (g2 < PAR.ng) ==> (p < PAR.np_g g1)
              ==> a IN (PAR.A_gp g1 p) ==> a IN (PAR.A_G g2) 
              ==> (g1 = g2)) /\
 (* per_gic_disjoint,
    GIC and peripherals are located in different parts of memory, *)
 (!g p G. (g < PAR.ng) ==> (p < PAR.np_g g) ==> gicAR G
           ==> (DISJOINT (PAR.A_gp g p) (RPAR.Amap G))) /\
 (* per_igc_disjoint,
    IGC channels are not allocated in peripheral memory *)
 (!s gs gt p. (gs < PAR.ng) ==> (gt < PAR.ng) ==> (s < PAR.ns)
     ==> (PAR.cpol s = (gs,gt)) 
     ==>  (p < PAR.np_g gs ==> FST (PAR.igca s) NOTIN PAR.A_gp gs p)
       /\ (p < PAR.np_g gt ==> SND (PAR.igca s) NOTIN PAR.A_gp gt p)) /\
 (* gic_addresses,
    the GICC and GICD regions are mapped into the RAM of each guest,
    no guest RAM overlaps with the GICH and GICV regions, 
    we assume here that the GIC addresses are exposed to the guests as they
    appear in hardware, again this simplifies the proof *)
 (!g. (g < PAR.ng) ==> ((RPAR.Amap GICC) PSUBSET (PAR.A_G g))
                    /\ ((RPAR.Amap GICD) PSUBSET (PAR.A_G g))
                    /\ (DISJOINT (RPAR.Amap GICH) (PAR.A_G g))
                    /\ (DISJOINT (RPAR.Amap GICV) (PAR.A_G g)))
`;



val refined_goodP_def = Define `refined_goodP (ip:params) (p:refined_params) =
(* we have at least one core *)	
		    (0 < p.nc)
(* we add that we have at least one peripheral, 
   it's not strictly necessary for correctness, 
   but it allows to define projections onto the peripheral indices *)
		 /\ (0 < p.np)
(* peripheral interrupts are not shared between peripherals *)	
                 /\ (!m n. m<p.np /\ n<p.np /\ m <> n ==>
			(p.pirq_p m INTER p.pirq_p n = EMPTY))
(* all peripheral interrupts are actual peripheral interrupts (i.e. no SGIs) *)	
	         /\ (!m irq. m<p.np /\ irq IN p.pirq_p m ==> ?q. irq = PIR q)
(* all single (system) address regions are disjoint *)
                 /\ (!a b. singleAR(a) /\ singleAR(b) /\ a <> b ==>
			(p.Amap(a) INTER p.Amap(b) = EMPTY))
(* peripheral address regions are aligned and contiguous *)
	         /\ (!a. perAR(a,p) ==> 
			 is_aligned(p.Amap a) /\ is_contiguous(p.Amap a))
(* peripheral address regions are disjoint *)
                 /\ (!a b. perAR(a,p) /\ perAR(b,p) /\ a <> b ==>
			(p.Amap(a) INTER p.Amap(b) = EMPTY))
(* peripheral regions are disjoint from single (system) regions *)
		 /\ (!a b. singleAR(a) /\ perAR(b,p) ==>
			(p.Amap(a) INTER p.Amap(b) = EMPTY))
(* single (system) address regions are disjoint from the guest regions, 
   except for the GIC virtual interface *)
		 /\ (!a b. singleAR(a) /\ a <> GICV /\ guestAR(b,ip) ==>
			(p.Amap(a) INTER p.Amap(b) = EMPTY))
(* all guest regions contain the GICV regions, 
   as it virtualizes the interrupt core interface for the guest's cores *)
		 /\ (!g. g<ip.ng ==> p.Amap(GICV) SUBSET p.Amap(GUEST g))
(* each peripheral region is part of a guest memory *) 
		 /\ (!per. per<p.np ==> 
	                ?g. g<ip.ng /\ p.Amap(PER per) SUBSET p.Amap(GUEST g))
(* IGC channel regions are contained in both corresponding guests *)
	         /\ (!g g'. g<ip.ng /\ g'<ip.ng /\ g <> g' ==>
			(p.A_IGC g g' SUBSET p.Amap(GUEST g) /\
                         p.A_IGC g g' SUBSET p.Amap(GUEST g')))
(* different IGC channels are disjoint *)
		 /\ (!g1 g2 g3 g4. g1 < ip.ng /\ g2 < ip.ng /\ g3 < ip.ng
			     /\ g1 <> g2 /\ g3 <> g4 /\ (g1,g2) <> (g3,g4) ==>
			(p.A_IGC g1 g2 INTER p.A_IGC g3 g4 = EMPTY))
(* different guests share only the IGC channels and the GICV region *)
	         /\ (!g g'. g<ip.ng /\ g'<ip.ng /\ g <> g' ==>
			(p.Amap(GUEST g) INTER p.Amap(GUEST g') = 
			 p.A_IGC g g' UNION p.A_IGC g' g UNION p.Amap(GICV)))
(* peripheral regions are disjoint from IGC channel regions *)
		 /\ (!a g g'. perAR(a,p) /\ g<ip.ng /\ g'<ip.ng /\ g <> g' ==>
			(p.Amap(a) INTER p.A_IGC g g' = EMPTY))
(* each guest uses a different page table *)
	         /\ (!g g'. g<ip.ng /\ g'<ip.ng /\ g <> g' ==>
			(p.A_PT(g) INTER p.A_PT(g') = EMPTY))
(* all guest page tables are stored in HV memory *)
		 /\ (!g. g<ip.ng ==> p.A_PT(g) SUBSET p.Amap(HV))
(* all peripherals use disjoint SMMU page tables *)
		 /\ (!g g'. g<ip.ng /\ g'<ip.ng /\ g <> g' ==>
			(p.A_PPT(g) INTER p.A_PPT(g') = EMPTY))
(* all SMMU page tables are stored in HV memory*)
		 /\ (!g. g<ip.ng ==> p.A_PPT(g) SUBSET p.Amap(HV))
(* the root key hash is stored in ROM *)
		 /\ (((42><7)p.a_rkh) IN p.Amap(ROM))
(* the GIC distributor region is just one page big *)
		 /\ (CARD (p.Amap GICD) = 1) /\ FINITE (p.Amap GICD)
(* the GICC and GICV regions have the same size (2 pages) *)
		 /\ (CARD (p.Amap GICC) = 2) /\ (CARD (p.Amap GICV) = 2)
		 /\ FINITE (p.Amap GICC) /\ FINITE (p.Amap GICV)
                `;


(*  evper maps external inputs and outputs to a defined peripheral *)
val good_evper_def = Define `good_evper (ep:pevent -> num) p =
!e. ep e < p.np
`;


(* existence proof for uninstatiated specification of parameters *)
val PAR_RPAR_exists = prove (``
?PAR RPAR evper. goodP PAR RPAR /\ refined_goodP PAR RPAR 
	      /\ good_evper evper RPAR``,

  Q.EXISTS_TAC `
  <| ng := 1;
     ns := 0;
     cpol := ARB;
     igca := ARB;
     nc_g := K 1;
     np_g := K 1;
     pirq_gp := K (K EMPTY);
     id_igc := ARB;
     A_G := K {1w; 2w; 3w};
     A_gp := K (K EMPTY)
  |>` THEN

  `!x. (x < 1) <=> (x = 0)` by DECIDE_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [PSUBSET_SING, refined_goodP_def, goodP_def] THEN
  Q.EXISTS_TAC `
  <| nc := 1; 
     np := 1;
     pirq_p := K EMPTY;
     a_rkh := 0w;
     Amap := (\ar. case ar of GICD => {1w} | GICC => {2w;3w} | GICV => {4w;5w}
			    | ROM => {0w} | GUEST g => {4w;5w} | _ => {});
     A_PT := K EMPTY;
     A_PPT := K EMPTY;
     A_IGC := ARB
 |>` THEN
 ASM_SIMP_TAC (srw_ss()) [singleAR_def, guestAR_def, perAR_def, PSUBSET_DEF,
   EXTENSION] THEN

 Q.EXISTS_TAC `K 0` THEN
 ASM_SIMP_TAC (srw_ss()) [good_evper_def] THEN
 REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `1w` THEN SIMP_TAC (srw_ss()) [],
   Q.EXISTS_TAC `2w` THEN SIMP_TAC (srw_ss()) [],

   `1w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   Cases_on `a` THEN Cases_on `b` THEN 
       ASM_SIMP_TAC (srw_ss()) [] THEN 
       METIS_TAC[]
   ,
   FULL_SIMP_TAC std_ss [is_aligned_def, log_sz_def,
			 base_adr_def,
			 pred_setTheory.CARD_EMPTY,
			 pred_setTheory.IMAGE_EMPTY] THEN
   BBLAST_PROVE_TAC
   ,
   FULL_SIMP_TAC std_ss [is_contiguous_def,  base_adr_def,
			 pred_setTheory.CARD_EMPTY,
			 pred_setTheory.NOT_IN_EMPTY] THEN
   BBLAST_PROVE_TAC
   ,
   `1w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 0w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 1w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 2w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 3w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `5w:36 word <> 4w` by SIMP_TAC (srw_ss()) [] THEN
   `1w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   `2w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   `3w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   `4w:36 word <> 5w` by SIMP_TAC (srw_ss()) [] THEN
   Cases_on `a` THEN ASM_SIMP_TAC (srw_ss()) [] THEN METIS_TAC[]
  ]
);


(* unintantiated specification of ideal / refined parameters
   from here on:
   PAR - ideal model parameters
   RPAR - refined model parameters 
   evper - mapping of external signals to peripherals
*)
val goodP_axioms_raw = new_specification ("goodP_axioms_raw",
  ["PAR", "RPAR", "evper"], PAR_RPAR_exists);

(* former axiom, now lemma *)
val evper_ax = store_thm("evper_ax", ``
!e. evper e < RPAR.np
``,
  METIS_TAC [goodP_axioms_raw, good_evper_def]
);


(* instantiating abbreviations for parameters *)
val IGCin_def = Define `IGCin = igcin PAR`;
val IGCout_def = Define `IGCout = igcout PAR`;

(* A_IGCin g - 
   intermediate physical addresses for incoming IGC channels of guest g *)
val A_IGCin_def = Define`A_IGCin g = 
{SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = g)}
`;

(* A_IGCout g - 
   intermediate physical addresses for outgoing IGC channels of guest g *)
val A_IGCout_def = Define`A_IGCout g = 
{FST (PAR.igca s) | s < PAR.ns /\ (FST (PAR.cpol s) = g)}
`;


(* instantiating abbreviations for parameters *)
val PIRQ_def = Define `PIRQ = pirq_g PAR`;
val IPIRQ_def = Define `IPIRQ = ipirq_g PAR`;

(* xPIRQ g - physical interrupts of guest g including IGC interrupts *)
val xPIRQ_def = Define `xPIRQ g = PIRQ g UNION {PIR (PAR.id_igc s) | s IN IGCin g}`;

(* lPIRQ g - physical interrupts of guest g excluding IGC interrupts *)
val lPIRQ_def = Define `lPIRQ g = PIRQ g INTER {PIR n | n >= 16 /\ n < 1020}`;
val lPIRQ_def' = store_thm(
   "lPIRQ_def'",
    ``  (lPIRQ g (PIR n) = (n >= 16 /\ n < 1020 /\ (PIR n) IN PIRQ g))
     /\ (lPIRQ g (SGI _) = F)``,
    SIMP_TAC (srw_ss()) [lPIRQ_def, PIRQ_def, pirq_g_def] >>
    METIS_TAC []);
val lPIRQ_lem = store_thm(
   "lPIRQ_lem", ``
    (((PIR n) IN lPIRQ g) = (n >= 16 /\ n < 1020 /\ (PIR n) IN PIRQ g)) /\
    (SGI (id,c',c'') NOTIN lPIRQ g)``,
    SIMP_TAC (srw_ss()) [lPIRQ_def', IN_DEF]);

val obviously_not_in_IPIRQ_lem =
    store_thm("obviously_not_in_IPIRQ_lem",
      ``PIR q NOTIN IPIRQ g``,
      RW_TAC (srw_ss()) [IPIRQ_def, ipirq_g_def]);

(* guest_irq g q - q is (non-IGC) IRQ of guest g *)
val guest_irq_def = Define `
    (guest_irq g (PIR n) = (n >= 16 /\ n < 1020 /\ (PIR n) IN PIRQ g)) /\
    (guest_irq g (SGI (id,c',c'')) = (SGI(id,c',c'')) IN IPIRQ g)`;

(* some alternative definitions and rewrites *)
val guest_irq_def' = store_thm(
   "guest_irq_def'", ``
    (guest_irq g (PIR n) = (n >= 16 /\ n < 1020 /\ (PIR n) IN PIRQ g)) /\
    (guest_irq g (SGI (id,c',c'')) = 
         (id <=+ 7w /\ c' < PAR.nc_g g /\ c'' < PAR.nc_g g))``,
    SIMP_TAC (srw_ss()) [guest_irq_def, IPIRQ_def, ipirq_g_def] >> 
    METIS_TAC []);
    
val guest_irq_def'' = store_thm(
   "guest_irq_def''", ``
    (guest_irq g (PIR n) = 
         (n >= 16 /\ n < 1020 /\ (PIR n) IN PIRQ g UNION IPIRQ g)) /\
    (guest_irq g (SGI (id,c',c'')) = 
         (id <=+ 7w /\ c' < PAR.nc_g g /\ c'' < PAR.nc_g g))``,
    SIMP_TAC (srw_ss()) [guest_irq_def', obviously_not_in_IPIRQ_lem]);
    
val guest_irq_def''' = store_thm(
   "guest_irq_def'''", ``
    guest_irq g q = 
      case q of
         | PIR n           => n >= 16 /\ n < 1020 /\ q IN PIRQ g UNION IPIRQ g
         | SGI (id,c',c'') => id <=+ 7w /\ c' < PAR.nc_g g /\ c'' < PAR.nc_g g
``,
    REPEAT CASE_TAC >> SIMP_TAC (srw_ss()) [guest_irq_def'']);

val guest_irq_def_ = store_thm(
   "guest_irq_def_",``
    (guest_irq g (PIR n) = (PIR n) IN lPIRQ g) /\
    (guest_irq g (SGI (id,c',c'')) = (SGI(id,c',c'')) IN IPIRQ g)``,
    SIMP_TAC (srw_ss()) [guest_irq_def, lPIRQ_lem]);

val guest_irq_PIRQ_xPIRQ_lem = store_thm(
   "guest_irq_PIRQ_xPIRQ_lem",
    ``guest_irq g (PIR n) ==> 
          PIR n IN PIRQ g /\ PIR n IN xPIRQ g /\ PIR n IN lPIRQ g``,
    SIMP_TAC (srw_ss()) [xPIRQ_def, guest_irq_def_, lPIRQ_lem]);

(* xguest_irq g q - q is IRQ of guest g (including IGC interrupts) *) 
val xguest_irq_def = Define `
    (xguest_irq g (PIR n) = (n >= 16 /\ n < 1020 /\ (PIR n) IN xPIRQ g)) /\
    (xguest_irq g (SGI (id,c',c'')) = (id <=+ 7w /\ 
				       c' < PAR.nc_g g /\ 
				       c'' < PAR.nc_g g))
`;

(* rewritten assumptions on ideal parameters *)
val goodP_axiom = save_thm("goodP_axiom",
  REWRITE_RULE [goodP_def, GSYM PIRQ_def, GSYM IPIRQ_def, GSYM IGCout_def, 
		GSYM IGCin_def, GSYM DISJOINT_DEF] 
    (CONJUNCT1 goodP_axioms_raw));

(* rewritten assumptions on refined parameters *)
val refined_goodP_axiom = save_thm("refined_goodP_axiom",
  REWRITE_RULE [refined_goodP_def, GSYM PIRQ_def, GSYM IPIRQ_def, 
		GSYM IGCout_def, GSYM IGCin_def, GSYM DISJOINT_DEF] 
    (CONJUNCT1 (CONJUNCT2 goodP_axioms_raw)));

(* valid_sender g s = s is a valid message sender ID within guest g *)
val valid_sender_def =  Define `valid_sender g s =
     (?c. (s = CoreSender c) /\ c < PAR.nc_g g)
  \/ (?p. (s = PeripheralSender p) /\ p < PAR.np_g g)`;

(* valid_ref_sender s = s is a valid message sender ID in the refined model *)
val valid_ref_sender_def =  Define `
     (valid_ref_sender (CoreSender c) = c < RPAR.nc)
  /\ (valid_ref_sender (PeripheralSender p) = p < RPAR.np)`;

(* generalization for both refined / ideal model *)
val valid_sender__def = Define `
     (valid_sender_ NONE s = valid_ref_sender s)
  /\ (valid_sender_ (SOME g) s = valid_sender g s)`;

(* receiverMem g - redundant to A_IGCin *) 
val receiverMem_def = Define `receiverMem g = 
    {SND (PAR.igca s) | s < PAR.ns /\ (SND (PAR.cpol s) = g)}`;

(* inv_pol (g,g') - inverse lookup of IGC channel via pair of guests *)
val inv_pol_axiom = new_specification ("inv_pol_axiom", ["inv_pol"],
  prove (``?inv_pol:num # num -> num option.
    !g g' s. (inv_pol (g,g') = SOME s) ==> (PAR.cpol s = (g,g'))``,
Q.EXISTS_TAC `K NONE` THEN SIMP_TAC std_ss []));

(* communication policy is injective receiving guests *)
val cpol_inj = store_thm("cpol_inj", ``
!s s' g g2 g2' a1 a2 a1' a2'.
   s < PAR.ns
/\ s' < PAR.ns
/\ s <> s'
/\ (PAR.cpol s = (g,g2))
/\ (PAR.cpol s' = (g,g2'))
/\ (PAR.igca s = (a1,a2))
/\ (PAR.igca s' = (a1',a2'))
==>
(g2 <> g2') /\ (a1 <> a1') /\ g2 < PAR.ng /\ g2' < PAR.ng
``,
  METIS_TAC [goodP_axiom, pairTheory.FST, pairTheory.SND]
);

(* some easy observations that might be helpful later *)
val channel_lem1 = store_thm("channel_lem1", ``
    !g g'. (g <> g') ==> (((IGCin g) INTER (IGCin g')) = EMPTY)``,
      SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_INTER, 
		       IGCin_def, igcin_def, IN_ABS] THEN
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss []);

val channel_lem2 = store_thm("channel_lem2", ``
    !g g'. (g <> g') ==> (((IGCout g) INTER (IGCout g')) = EMPTY)``,
      SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_INTER, 
		       IGCout_def, igcout_def, IN_ABS] THEN
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss []);


val channel_lem3 = store_thm("channel_lem3", ``
    !g g'. (g <> g') ==> (((IGCin g) INTER (IGCout g)) = EMPTY)``,
      SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_INTER, IGCin_def, IGCout_def,
        igcin_def, igcout_def, IN_ABS] THEN
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [] THEN
      REPEAT (BasicProvers.VAR_EQ_TAC) THEN
      METIS_TAC [goodP_axiom]);

val in_PIRQ_lem = store_thm(
   "in_PIRQ_lem",
   ``intr IN PAR.pirq_gp g p ==> p < PAR.np_g g ==> intr IN PIRQ g``,
   SIMP_TAC (srw_ss()) [PIRQ_def, pirq_g_def] >>
   METIS_TAC []);

val in_lPIRQ_lem = store_thm(
   "in_lPIRQ_lem",
   ``PIR n IN PAR.pirq_gp g p ==> p < PAR.np_g g ==> n >= 16 
			      ==> n < 1020 ==> PIR n IN lPIRQ g``,
   SIMP_TAC (srw_ss()) [lPIRQ_lem, pirq_g_def] >>
   METIS_TAC [in_PIRQ_lem]);

val in_IGCin_lem = store_thm(
   "in_IGCin_lem",
   ``(SND (PAR.cpol s) = g) ==> s < PAR.ns ==> s IN (IGCin g)``,
    RW_TAC std_ss [IGCin_def, igcin_def, IN_ABS] >>
    EXISTS_TAC  ``FST (PAR.cpol s)`` >>
    SIMP_TAC std_ss [] >>
    METIS_TAC [goodP_axiom]);

val IGC_NOTIN_PIRQ_lem = store_thm(
   "IGC_NOTIN_PIRQ_lem",
   ``((SND (PAR.cpol s) = g) ==> s < PAR.ns ==> g < PAR.ng 
			     ==> PIR (PAR.id_igc s) NOTIN PIRQ g) /\
     ((s IN (IGCin g)) ==> s < PAR.ns ==> g < PAR.ng 
		       ==> PIR (PAR.id_igc s) NOTIN PIRQ g)``,
   METIS_TAC [goodP_axiom, in_IGCin_lem]);

val IGC_IN_xPIRQ_lem = store_thm(
   "IGC_IN_xPIRQ_lem",
   ``((SND (PAR.cpol s) = g) ==> s < PAR.ns 
			     ==> PIR (PAR.id_igc s) IN xPIRQ g) /\
     ((s IN (IGCin g)) ==> PIR (PAR.id_igc s) IN xPIRQ g)``,
   SIMP_TAC (srw_ss()) [xPIRQ_def] >>
   METIS_TAC [in_IGCin_lem]);

val IGC_in_out_disj = store_thm("IGC_in_out_disj", ``
!g. g < PAR.ng ==> DISJOINT (A_IGCin g) (A_IGCout g)
``,
  REPEAT STRIP_TAC >>
  RW_TAC (srw_ss()) [A_IGCin_def, A_IGCout_def, pred_setTheory.IN_DISJOINT] >>
  MATCH_MP_TAC ( prove(``(~a ==> b) ==> (a \/ b)``, PROVE_TAC []) ) >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC ( prove(``(~b /\ ~c ==> a) ==> (a \/ b \/ c)``, 
		       PROVE_TAC []) ) >>
  FULL_SIMP_TAC (srw_ss()) [] >>
  STRIP_TAC >>
  Cases_on `s' = s` >- (
      `PAR.cpol s = (g,g)` by ( 
          METIS_TAC [pairTheory.PAIR]
      ) >>
      METIS_TAC [goodP_axiom]
  ) >>
  METIS_TAC [goodP_axiom]
);

val igc_pir_number_lem = store_thm(
   "igc_pir_number_lem",
   ``(!s. (s < PAR.ns) ==> PAR.id_igc s >= 16 /\ PAR.id_igc s < 1020)``,
   METIS_TAC [goodP_axiom]);


(* Lemma: RAM of one guest does not overlap with peripheral memory in
          any other guest *)
val id_guest_per_mem_lem = store_thm("id_guest_per_mem_lem", ``
!g g' p' a.
   g < PAR.ng
/\ g' < PAR.ng
/\ g <> g'
/\ p' < PAR.np_g g'
/\ a IN PAR.A_G g
==>
a NOTIN PAR.A_gp g' p'
``,
  REPEAT STRIP_TAC >>
  `a IN PAR.A_G g'` by ( METIS_TAC [goodP_axiom, 
				    pred_setTheory.PSUBSET_DEF, 
				    pred_setTheory.SUBSET_DEF] ) >>
  METIS_TAC [goodP_axiom]
);

(******************   details parameters refined model   **************)


(* Corollary: GICD region is contained in all ideal guest memory space *)
val Agicd_AG_lem = store_thm("Agicd_AG_lem", ``
!g. g < PAR.ng ==> (RPAR.Amap GICD) PSUBSET (PAR.A_G g)
``, METIS_TAC [goodP_axiom]);

(* Corollary: disjointness of address regions in Amap *)
val refined_goodP_axiom_Amap_disjoint = store_thm (
"refined_goodP_axiom_Amap_disjoint",
``!a b.
     ((singleAR a /\ singleAR b /\ a <> b) \/
     (perAR (a,RPAR) /\ perAR (b,RPAR) /\ a <> b) \/
     (singleAR a /\ perAR (b,RPAR)) \/
     (singleAR a /\ a <> GICV /\ guestAR (b,PAR))) ==>
     (DISJOINT (RPAR.Amap a) (RPAR.Amap b))``,

METIS_TAC [refined_goodP_axiom]);


(* Corollary: different interrupts for different peripherals *)
val refined_goodP_axiom_pirq_p_disjoint = store_thm (
"refined_goodP_axiom_pirq_p_disjoint",
``!m n. m < RPAR.np /\ n < RPAR.np /\ m <> n ==>
        (DISJOINT (RPAR.pirq_p m) (RPAR.pirq_p n))``,
METIS_TAC[refined_goodP_axiom]);


(* Corollary: GIC and peripheral addresses disjoint *)
val GICaddresses_lem = store_thm("GICaddresses_lem", ``
!a n. n<RPAR.np /\ gicAR(a) ==> (RPAR.Amap(a) INTER RPAR.Amap(PER n) = EMPTY)
``,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[GSYM DISJOINT_DEF] THEN
      MATCH_MP_TAC refined_goodP_axiom_Amap_disjoint THEN
      ASM_SIMP_TAC (srw_ss()) []);


(* Lemma: all GIC regions but GICV are not in refined guest address space *)
val gic_not_guest_mem_lem  = store_thm("gic_not_guest_mem_lem", ``
!g a. 
   g < PAR.ng 
/\ (a IN RPAR.Amap GICC \/ a IN RPAR.Amap GICD \/ a IN RPAR.Amap GICH)
==> 
a NOTIN RPAR.Amap (GUEST g)
``,

  REPEAT GEN_TAC THEN DISCH_TAC THEN
  Q.SUBGOAL_THEN `!a. singleAR a /\ a <> GICV /\ guestAR (GUEST g,PAR) ==>
     (DISJOINT (RPAR.Amap a) (RPAR.Amap (GUEST g)))` MP_TAC THEN1 (
    PROVE_TAC[refined_goodP_axiom_Amap_disjoint]) THEN

  PROVE_TAC [ARpred_REWRITES, AddressRegion_distinct, IN_DISJOINT]
);



(* Lemma: all GICV addresses are in refined guest address space *)
val gicv_guest_mem_lem  = store_thm("gicv_guest_mem_lem", ``
!g a. g < PAR.ng /\ a IN RPAR.Amap GICV ==> a IN RPAR.Amap (GUEST g)
``,
  REPEAT STRIP_TAC THEN
  `RPAR.Amap(GICV) SUBSET RPAR.Amap(GUEST g)` by (
      METIS_TAC[refined_goodP_axiom]) THEN 
  FULL_SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF]  
);

(* Lemma: all single (system) address spaces disjoint *)
val singleAR_disj_lem = store_thm("singleAR_disj_lem", ``
!A B a. 
   singleAR A 
/\ singleAR B 
/\ (A <> B)
/\ a IN RPAR.Amap A
==>
~ (a IN RPAR.Amap B)
``,
  REPEAT STRIP_TAC THEN
  `DISJOINT (RPAR.Amap A) (RPAR.Amap B)` by 
      PROVE_TAC [refined_goodP_axiom_Amap_disjoint] THEN 
  METIS_TAC [IN_DISJOINT]
);

(* expanded rewrite *)
val singleAR_disj_EXPAND = save_thm("singleAR_disj_EXPAND",
SIMP_RULE ((std_ss++(DatatypeSimps.expand_type_quants_ss[``:AddressRegion``]))
	          ++(DatatypeSimps.type_rewrites_ss[``:AddressRegion``])) 
	  [singleAR_def] singleAR_disj_lem
);


(* Lemma: different GIC regions are disjoint *)
val gicAR_disj_lem = store_thm("gicAR_disj_lem", ``
!A B a. 
   gicAR A 
/\ gicAR B 
/\ (A <> B)
/\ a IN RPAR.Amap A
==>
~ (a IN RPAR.Amap B)
``,
  METIS_TAC[ARpred_implications, singleAR_disj_lem]);


(* expanded rewrite *)
val gicAR_disj_EXPAND = save_thm("gicAR_disj_EXPAND",
SIMP_RULE ((std_ss++(DatatypeSimps.expand_type_quants_ss[``:AddressRegion``]))
                  ++(DatatypeSimps.type_rewrites_ss[``:AddressRegion``])) 
	  [gicAR_def, DISJ_COMM] gicAR_disj_lem
);


(* Lemma: disjointness of other GIC address regions from GICD *)
val gic_gicd_disj_lem  = store_thm("gic_gicd_disj_lem", ``
!a. (a IN RPAR.Amap GICC \/ a IN RPAR.Amap GICH \/ a IN RPAR.Amap GICV)
==> 
a NOTIN RPAR.Amap GICD
``,
  METIS_TAC[gicAR_disj_EXPAND]);

(* A_gicper - all peripheral and GIC physical page addresses *)
val A_gicper_def = Define `
A_gicper = {a |    (?G. gicAR G /\ a IN RPAR.Amap G) 
		\/ (?p. p < RPAR.np /\ a IN RPAR.Amap (PER p)) }
`;

(* Lemma: second stage MMU page tables are not allocated in A_gicper *)
val PT_gic_per_disj_lem = store_thm("PT_gic_per_disj_lem", ``
!g a. 
   g < PAR.ng
/\ a IN RPAR.A_PT g
==>
a NOTIN A_gicper
``,
  REPEAT STRIP_TAC THEN
  `a IN RPAR.Amap HV` by METIS_TAC[refined_goodP_axiom, SUBSET_DEF] THEN
  FULL_SIMP_TAC std_ss [A_gicper_def, IN_GSPEC_IFF] THENL [
    (* case: GIC *)
    `G = HV` by METIS_TAC[singleAR_disj_lem, ARpred_implications, 
			  ARpred_REWRITES] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    (* case: peripherals *)
    `DISJOINT (RPAR.Amap HV) (RPAR.Amap (PER p))` by 
         METIS_TAC[refined_goodP_axiom_Amap_disjoint, ARpred_REWRITES] THEN
     METIS_TAC [IN_DISJOINT]
  ]
);	   

(* Lemma: SMMU page tables are not allocated in A_gicper *)
val PPT_gic_per_disj_lem = store_thm("PPT_gic_per_disj_lem", ``
!g a. 
   g < PAR.ng
/\ a IN RPAR.A_PPT g
==>
a NOTIN A_gicper
``,
  REPEAT STRIP_TAC THEN
  `a IN RPAR.Amap HV` by METIS_TAC[refined_goodP_axiom, SUBSET_DEF] THEN
  FULL_SIMP_TAC std_ss [A_gicper_def, IN_GSPEC_IFF] THENL [
    (* case: GIC *)
    `G = HV` by METIS_TAC[singleAR_disj_lem, ARpred_implications, 
			  ARpred_REWRITES] THEN
    FULL_SIMP_TAC (srw_ss()) [],

    (* case: peripherals *)
    `DISJOINT (RPAR.Amap HV) (RPAR.Amap (PER p))` by 
         METIS_TAC[refined_goodP_axiom_Amap_disjoint, ARpred_REWRITES] THEN
     METIS_TAC [IN_DISJOINT]
  ]
);	   


(* Lemma: second stage MMU page tables are not allocated in guest memory *)
val PT_guest_disj_lem = store_thm("PT_guest_disj_lem", ``
!g g' a G. 
   g < PAR.ng
/\ g' < PAR.ng
/\ a IN RPAR.A_PT g
==>
a NOTIN RPAR.Amap (GUEST g')
``,
  REPEAT STRIP_TAC THEN
  `a IN RPAR.Amap HV` by METIS_TAC[refined_goodP_axiom, SUBSET_DEF] THEN
  `DISJOINT (RPAR.Amap HV) (RPAR.Amap (GUEST g'))` by 
      METIS_TAC[refined_goodP_axiom_Amap_disjoint, ARpred_REWRITES] THEN
  METIS_TAC [IN_DISJOINT]
);

(* Lemma: SMMU page tables are not allocated in A_gicper *)
val PPT_guest_disj_lem = store_thm("PPT_guest_disj_lem", ``
!g g' a G. 
   g < PAR.ng
/\ g' < PAR.ng
/\ a IN RPAR.A_PPT g
==>
a NOTIN RPAR.Amap (GUEST g')
``,
  REPEAT STRIP_TAC THEN
  `a IN RPAR.Amap HV` by METIS_TAC[refined_goodP_axiom, SUBSET_DEF] THEN
  `DISJOINT (RPAR.Amap HV) (RPAR.Amap (GUEST g'))` 
      by METIS_TAC[refined_goodP_axiom_Amap_disjoint, ARpred_REWRITES] THEN
  METIS_TAC [IN_DISJOINT]
);

(* Lemma: guest memory does not overlap with hypervisor memory *)
val HV_guest_disj_lem = store_thm("HV_guest_disj_lem", ``
!g a. 
   g < PAR.ng
/\ a IN RPAR.Amap (GUEST g)
==>
a NOTIN RPAR.Amap HV
``,
  REPEAT STRIP_TAC THEN
  `guestAR ((GUEST g), PAR)` by ( METIS_TAC [guestAR_def] ) >>
  `singleAR HV` by ( METIS_TAC [singleAR_cases] ) >> 
  METIS_TAC[refined_goodP_axiom, AddressRegion_distinct, IN_DISJOINT] 
);


(* peripheral and GIC addresses disjoint;
   previously proven via projections, coupling, and GICaddresses_lem,
   now a rather direct consequence of goodP_axiom,
   but kept for compatibility *)
val per_gic_disj_lem =
    store_thm("per_gic_disj_lem",
       ``   (!g p a. g < PAR.ng ==> p < PAR.np_g g ==> a IN PAR.A_gp g p 
				==> a IN RPAR.Amap GICC ==> F)
         /\ (!g p a. g < PAR.ng ==> p < PAR.np_g g ==> a IN PAR.A_gp g p 
				==> a IN RPAR.Amap GICD ==> F)
         /\ (!g p a H. g < PAR.ng ==> p < PAR.np_g g ==> a IN PAR.A_gp g p 
				  ==> a IN RPAR.Amap H ==> gicAR H ==> F)``,
         METIS_TAC [goodP_axiom,
                    gicAR_def,
                    pred_setTheory.DISJOINT_DEF,
                    pred_setTheory.IN_INTER,
                    pred_setTheory.NOT_IN_EMPTY]);
 
(* peripherals of the same guest are disjoint;
   previously proven via projections, coupling, and
   refined_goodP_axiom_Amap_disjoint, now a direct consequence of goodP_axiom
   (stating this more general for all peripherals), 
   but kept for compatibility *)
val per_disj_lem =
    store_thm("per_disj_lem",
       ``!g p1 p2 a. g < PAR.ng ==> (p1 <> p2) ==> p1 < PAR.np_g g 
				==> p2 < PAR.np_g g ==> a IN PAR.A_gp g p1
				==> a IN PAR.A_gp g p2 ==> F``,
         METIS_TAC [goodP_axiom]);

(************** refined model interrupts ***************)

(* pirq p - all peripheral interrupts according to refined parameter p *)
val pirq_def = Define `pirq p = 
    BIGUNION (\s. (?pe. pe < (p.np) /\ (s = p.pirq_p pe)))`; 
(* ipirq p c - 
   all inter-processor interrupts to core c according to refined parameter p *)
val ipirq_c_def = Define `ipirq_c p c'= 
    (\sgi. ?c id. (c < p.nc  /\ (id <=+ 7w) /\ (sgi = SGI (id,c,c'))))`;

(* instantiation for refined model parameters *)
val refined_PIRQ_def = Define `refPIRQ = pirq RPAR`;
val refined_IPIRQ_c_def = Define `refIPIRQ_c = ipirq_c RPAR`;
val refined_IPIRQ_def = Define `refIPIRQ = 
    BIGUNION (\s. ?c'. (c' < RPAR.nc) /\ (s = refIPIRQ_c c'))`;

(*************** finish ***********)

val _ = export_theory();






