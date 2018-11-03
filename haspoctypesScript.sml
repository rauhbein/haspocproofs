(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 
open tacticsLib; 

open axtypesTheory;

val _ = new_theory "haspoctypes";

(*************** Platform-specific type definitions ******************)

(* some helper functions for page-addressable memory *)

val _ = Parse.type_abbrev("PAGE", ``:bool[32768]``);

(* extract (read) d bytes from offset a within word x *)
val bytext_def = Define `bytext (a:'a word, d:num, x:'b word) = 
word_extract (w2n a + 8*d -1) (w2n a) x
`;

(* read d<=8 bytes from address a in page-addressable memory m *)
val mem_read_def = Define `
mem_read (m:bool[36]->PAGE) (a:bool[48]) (d:num) = 
(bytext((11><0)a:bool[12], d, m ((47><12)a))):bool[64]
`;

(* interrupts and GIC *) 

(* SGI software generated - id 4 bit, sender, receiver, 
   PIR peripheral generated - arg is number of interrupt *)
val _ = Hol_datatype `irqID = SGI of (word4 # num # num) | PIR of num`;

(* equality definition for SGIs *)
val SGI_11 = store_thm("SGI_11", ``
(SGI(a,b,c) = SGI(a',b',c')) = ((a=a') /\ (b=b') /\ (c=c'))
``,
    METIS_TAC [TypeBase.one_one_of ``:irqID``, pairTheory.PAIR_EQ]
);

(* interrupt state in GIC:
   INACTIVE - neither pending nor active in GIC 
   PENDING  - interrupt waiting to be signaled to / handled by a core 
   ACTIVE   - interrupt was acknowledged by receiver core, handling ongoing 
   PENDACT  - previous interrupt is being handled but it was triggered again *)
val _ = Datatype `IRQstate = INACTIVE | PENDING | ACTIVE | PENDACT`;
(* physical interrupt state on ideal level, basically synonyms for IRQstate *)
val _ = Datatype `PIstate = NOT_ASSERTED | ASSERTED | FORWARDED | ASS_FWD`;
(* three different types of GIC distributor registers *)
val _ = Datatype `GICDreg = CONST GICDregconst 
                          | MUTE GICDregmute 
			  | VOL GICDregvol`;


(* message types 

   here we define the messages used for communication
   between components in the decomposed model
*)

(* Types of messages sent core and PSCI / IGC interface:
   StopCore c  - request to power down core c
   StartCore c - request to start up core c
   SndIgc s    - send IGC notification interrupt for channel s *)
val _ = Datatype `event = StopCore num | StartCore num | SndIgc num`;

(* memory-based messages between memory, MMU, core, GIC, peripherals:

   used in both ideal and refined model,
   memory or peripheral access is requested by sending a request,
   execution of the request generates a reply:
   * reads and page table walks return the read value 
   * write replies are just a confirmation
   * faults indicate access violations / other failures,
   context determines whether address is intermediate or physical:
   * Core sends walk request to stage 1 MMU (internal to the core)
   * 1st stage MMU sends intermediate walk request to second stage 
   * second stage send physical walk request to mem 
   * in ideal model translation is invisible: 
     all addresses are intermediate physical,

   num: number of bytes, msginfo: info carried along, 

   Read a d i: read d bytes from address a 
   Write a d v i: write d bytes from v to address a 
   Walk a i: fetch page table entry (8 bytes) from address a ,

   we use bitstrings to denote variable length words,
   alternatively we could always extend to 64 bytes 

   walks include both 1st stage page table walks issued by the core
   and second stage page table walks issued by the MMU,
   if necessary the stage can be encoded in msginfo
*)

(* memory request type *)
val _ = Datatype `request = Read (bool[48]) num msginfo 
                          | Write (bool[48]) num bitstring msginfo
			  | Walk (bool[48]) msginfo`;

(* Reply to given request, which is included for easy matching 
   reads and walks include also the read value 
   faults contain fault information from memory / MMU *)
val _ = Datatype `reply = ReadValue request bitstring 
                        | WrittenValue request
			| WalkResult request (bool[64]) 
			| Fault request fault_info`;

(* sender ID for tagging message request / replies in memory subsystem,
   we distinguish cores and peripherals, the GIC does not send requests *)
val _ = Datatype `senderID = CoreSender num | PeripheralSender num`;

(* replies are valid / good if the request type matches *)
val good_rpl_def = Define `
   (good_rpl ( ReadValue ( Read a d i ) v ) = T)
/\ (good_rpl ( WrittenValue ( Write a d v i ) ) = T )
/\ (good_rpl ( WalkResult ( Walk a i ) w ) = T)
/\ (good_rpl ( Fault r fi ) = T)
/\ (good_rpl ( _ ) = F)
`;

(* helper predicates to avoid excessive pattern matching:
   Xreq r <=> r is an X request *)

val Rreq_def = Define `
   (Rreq (Read a d i) = T)
/\ (Rreq _ = F)
`;

val Wreq_def = Define `
   (Wreq (Write a d v i) = T)
/\ (Wreq _ = F)
`;

val PTreq_def = Define `
   (PTreq (Walk a i) = T) 
/\ (PTreq _ = F)
`;

(* similarly for replies, only matches good replies *)

val PTrpl_def = Define `
   (PTrpl (WalkResult (Walk a i) v) = T) 
/\ (PTrpl (WalkResult _ _) = F)
`;

val Frpl_def = Define `
   (Frpl (Fault r i) = T) 
/\ (Frpl _ = F)
`;


(* get address targeted by a request *)
val Adr_def = Define `
   (Adr (Read a d i) = a)
/\ (Adr (Write a d v i) = a) 
/\ (Adr (Walk a i) = a) 
`;

(* get message info of a request *)
val MsgOf_def = Define `
   (MsgOf (Read a d i) = i)
/\ (MsgOf (Write a d v i) = i)
/\ (MsgOf (Walk a i) = i)
`; 

(* get memory footprint / size of a request *)
val SzOf_def = Define `
   (SzOf (Read a d i) = d)
/\ (SzOf (Write a d v i) = d) 
/\ (SzOf (Walk a i) = 8)
`; 

(* get memory footprint / size of a reply *)
val Rpl_SzOf_def = Define `
   (Rpl_SzOf (ReadValue r v) = SzOf r)
/\ (Rpl_SzOf (WrittenValue r) = SzOf r) 
/\ (Rpl_SzOf (WalkResult r v) = SzOf r)
`; 

(* extracting the page address of a request *)
(* pops up everywhere! *)
val PAdr_def = Define `PAdr (r : request) = (47><12) (Adr r) :bool[36]`;

(* rewrites for instances of requests *)
val PAdr_rw_lem = store_thm("PAdr_rw_lem", ``
!a d v i.
   (PAdr (Read a d i) = (47 >< 12) a)
/\ (PAdr (Write a d v i) = (47 >< 12) a)
/\ (PAdr (Walk a i) = (47 >< 12) a)
``,
  RW_TAC (srw_ss()) [PAdr_def, Adr_def]			    
);

(* get targeted address from reply message *)
val Rpl_Adr_def = Define `
   (Rpl_Adr (ReadValue (Read a d i) v) = a)
/\ (Rpl_Adr (WrittenValue (Write a d v i)) = a) 
/\ (Rpl_Adr (WalkResult (Walk a i) v) = a)
/\ (Rpl_Adr (Fault (Read a d i) fi) = a) 
/\ (Rpl_Adr (Fault (Write a d v i) fi) = a) 
/\ (Rpl_Adr (Fault (Walk a i) fi) = a) 
`;

(* get page address from reply, also heavily used *)
val Rpl_PAdr_def = Define `Rpl_PAdr (q:reply) = (47><12) (Rpl_Adr q):bool[36]
`;

(* Lemma: decomposition of request address into page address + offset *)
val Adr_concat_lem = store_thm("Adr_concat_lem", ``
!r. Adr r = PAdr r @@ ((11 >< 0) (Adr r) :bool[12])
``,
  RW_TAC std_ss [PAdr_def] >>
  blastLib.BBLAST_PROVE_TAC
);

(* Lemma: decomposition of reply address into page address + offset *)
val Rpl_Adr_concat_lem = store_thm("Rpl_Adr_concat_lem", ``
!r. Rpl_Adr r = Rpl_PAdr r @@ ((11 >< 0) (Rpl_Adr r) :bool[12])
``,
  RW_TAC std_ss [Rpl_PAdr_def] >>
  blastLib.BBLAST_PROVE_TAC
);

(* match request with reply q,
   either a result or a matching fault was returned *)
val match_def = Define `
   (match (Read a d i, q) = (?v. q = ReadValue (Read a d i) v) 
                         \/ (?fi. q = Fault (Read a d i) fi))
/\ (match (Write a d v i, q) = (q = WrittenValue (Write a d v i))
			 \/ (?fi. q = Fault (Write a d v i) fi))
/\ (match (Walk a i, q) = (?v. q = WalkResult (Walk a i) v) 
			 \/ (?fi. q = Fault (Walk a i) fi))
`;


(* Lemma: for all requests there exists a matching reply *)
val match_reply_exist_lem = store_thm("match_reply_exist_lem", ``
!r. ?q. match(r,q)
``,
  GEN_TAC >>
  EXISTS_TAC ``Fault r fi`` >>
  Cases_on `r` >> (
      RW_TAC std_ss [match_def]
  )
);

(* get value to be written from a write request,
   undefined for reads / page table walks *)
val Req_val_def = Define `Req_val (Write a d v i) = v2w v
`;


(* get read/written value from a reply,
   undefined for faults *)
val Rpl_val_def = Define `
   (Rpl_val (ReadValue (Read a d i) v) = v2w v)
/\ (Rpl_val (WrittenValue (Write a d v i)) = v2w v)
/\ (Rpl_val (WalkResult (Walk a i) v) = w2w v)
`;

(* get returned raw bitstring for reads / writes *)
val Rpl_val_bs_def = Define `
   (Rpl_val_bs (ReadValue (Read a d i) v) = v)
/\ (Rpl_val_bs (WrittenValue (Write a d v i)) = v)
`;

(* equality for reply values, includes fault info *)
val Rpl_val_eq_def = Define `
   (Rpl_val_eq (ReadValue r v) (ReadValue r' v') = (v=v'))
/\ (Rpl_val_eq (WrittenValue (Write a d v i)) (WrittenValue (Write a' d' v' i'))
    = (v=v'))
/\ (Rpl_val_eq (WalkResult w v) (WalkResult w' v') = (v=v'))
/\ (Rpl_val_eq (Fault r i) (Fault r' i') = (i=i'))
/\ (Rpl_val_eq _ _ = F)
`;

(* xlated r r' states that r may be an address-translated version of r' 
   (or vice versa)

   as a necessary condition for requests being address-translated:
   - the request type must match
   - offset 12 bit into page must be the same 
   - they have the same auxiliary message information
   - for reads and writes: they have the same access size
   - for writes: the same value is written

   Note: this setting restricts the MMU to only modify the page index of a
   request. If the msginfo encodes memory parameters like memory type or
   cacheability attributes, and the hypervisor configures the MMU such that they
   are modified, this definition has to be refined to reflect which parts of
   msginfo are unchanged.
*)
val xlated_def = Define `
   (xlated (Read a d i, r') = ?a'. (r' = Read a' d i) 
		           /\ ((11><0) a :bool[12] = (11><0) a'))
/\ (xlated (Write a d v i, r') = ?a'. (r' = Write a' d v i) 
		              /\ ((11><0) a :bool[12] = (11><0) a'))
/\ (xlated (Walk a i, r') = ?a'. (r' = Walk a' i) 
		         /\ ((11><0) a :bool[12] = (11><0) a'))
`;

(* Lemmas: we show that xlated is an equivalence relation on requests *)

val xlated_id_lem = store_thm("xlated_id_lem", ``
!r. xlated (r,r)
``,
  Cases >> ( 
      RW_TAC (srw_ss()) [xlated_def]
  )
);

val xlated_sym_lem = store_thm("xlated_sym_lem", ``
!r r'. xlated (r,r') = xlated (r',r)
``,
  Cases >> ( 
      Cases >> (
          RW_TAC (srw_ss()) [xlated_def] >>
	  METIS_TAC []
      )
  )
);

val xlated_trans_lem = store_thm("xlated_trans_lem", ``
!r r' r''. xlated (r,r') /\ xlated (r',r'') ==> xlated(r, r'')
``,
  Cases >> ( 
      Cases >> (
          Cases >> (
	      RW_TAC (srw_ss()) [xlated_def]
	  )
      )
  )
);


(* Lemma: translated requests have the same byte indices / offset within page *)
val xlated_bx_lem = store_thm("xlated_bx_lem", ``
!r r'. xlated (r,r') ==> (((11><0) (Adr r)):bool[12] = (11><0) (Adr r'))
``,
  Cases >> ( 
      Cases >> (
          RW_TAC (srw_ss()) [xlated_def, Adr_def]
      )
  )
);

(* Lemma: translated requests have the same access size *)
val xlated_SzOf_lem = store_thm("xlated_SzOf_lem", ``
!r r'. xlated (r,r') ==> (SzOf r = SzOf r')
``,
  Cases >> ( 
      Cases >> (
          RW_TAC (srw_ss()) [xlated_def, SzOf_def]
      )
  )
);

(* xlated_rpl is similar to xlated but it relates address-translated replies,
   this definition is agnostic to whether the reply is good or not *)
val xlated_rpl_def = Define `
   (xlated_rpl (ReadValue r v, q') = ?r'. (q'=ReadValue r' v) /\ xlated(r,r'))
/\ (xlated_rpl (WrittenValue r, q') = ?r'. (q'=WrittenValue r') /\ xlated(r,r'))
/\ (xlated_rpl (WalkResult r v, q') = ?r'. (q'=WalkResult r' v) /\ xlated(r,r'))
/\ (xlated_rpl (Fault r fi, q') = ?r'. (q'=Fault r' fi) /\ xlated(r,r'))
`;

(* Lemmas: xlated_rpl is an equivalence relation *)

val xlated_rpl_id_lem = store_thm("xlated_rpl_id_lem", ``
!q. xlated_rpl(q,q)
``,
  Cases >> ( RW_TAC (srw_ss()) [xlated_rpl_def, xlated_id_lem] )
);

val xlated_rpl_sym_lem = store_thm("xlated_rpl_sym_lem", ``
!q q'. xlated_rpl(q,q') = xlated_rpl(q',q)
``,
  Cases >> (
      Cases >> (
          RW_TAC (srw_ss()) [xlated_rpl_def, xlated_sym_lem] >>
	  METIS_TAC []
      )
  )
);

val xlated_rpl_trans_lem = store_thm("xlated_rpl_trans_lem", ``
!q q' q''. xlated_rpl(q,q') /\ xlated_rpl(q',q'') ==> xlated_rpl(q,q'')
``,
  Cases >> (
      Cases >> (
          Cases >> (
              RW_TAC (srw_ss()) [xlated_rpl_def] >>
	      METIS_TAC [xlated_trans_lem]
	  )
      )
  )
);

(* Lemma: translated faults stay faults *)
val xlated_rpl_Frpl_lem = store_thm(
   "xlated_rpl_Frpl_lem",
   ``!q q'. xlated_rpl(q,q') /\ Frpl q ==> Frpl q'``,
   Cases >>
   Cases >>
   SIMP_TAC (srw_ss()) [xlated_rpl_def, Frpl_def]);


(* get the request from a reply *)
val ReqOf_def = Define `
    (ReqOf (ReadValue r v) = r)
 /\ (ReqOf (WrittenValue r) = r)
 /\ (ReqOf (WalkResult r w) = r)
 /\ (ReqOf (Fault r i) = r)`;


(* get the fault information from a fault reply,
   undefined for other replies *)
val fiOf_def = Define `
   (fiOf (Fault r i) = i)
`; 

(*************** core internal state abstraction *****************)

(* AbsCIState - abstract core internal state

   We use abstraction functions to only expose the relevant parts of a given
   core components. The abstraction exposes crucial resources such as general
   and special purpose registers. Other parts of the core, such as the state of
   the pipeline or the first stage MMU are considered internal to the core and
   not exposed by the abstraction. However some of the hidden state may effect
   externally visible behaviour, to this end we introduce another abstraction
   function that extracts the necessary information from the internal core
   state, that is not explicitly represented among the visible registers

   The internal state of the processor is then projected to a number of symbolic
   abstract states that carry the required information:

   FLUSHED - this signifies the state after an exception or interrupt is taken,
   in particular we assume that in this state the pipeline is flushed and no
   more memory accesses from the context before the interrupt are pending.

   Note: there are architectures where this is not necessarily the case. Here we
   assume it for a clear separation between the hypervisor and guest
   contexts. As hypervisor and guest memory accesses do not interfere it should
   be possible to prove a reordering theorem to justify our semantics where
   intuitively interrupts block until all guest memory accesses have
   completed. In any case, this issue concerns the instantiation of the model
   rather than its top level design.

   GICD_RS / GICD_RNS / GICD_WS / GICD_WNS - This concerns the state while a
   guest accesses memory mapped GICD registers. Reads and writes to these
   registers will be trapped by the hypervisor. Some read/write accesses are
   handled correctly, i.e., the source or target registers of the memory
   instructions are recorded in some interrupt state register. However some
   memory instructions, e.g., those with several source or target registers, are
   not supported by the functionality. They need complex decoding of the
   instruction in guest memory to enable emulation. To simplify things the
   hypervisor rejects such instructions accessing the GIC.

   The following abstract states encode these situations while a guest access to
   the GICD is pending in the core and before the hypervisor is entered due to a
   second stage memory access fault on the GIC distributor:

   GICD_RS r - a supported read instruction tries to access the GICD and the
   read value should be stored in register r

   GICD_RNS - an unsupported read instruction tries to access the GICD

   GICD_WS r - a supported write instruction tries to access the GICD and the
   value to be written is stored in register r

   GICD_WNS - an unsupported write instruction tries to access the GICD

   Identifying these four cases explicitly would require to expose a large part
   of the exception handling and instruction decoding in ARMv8. Since this would
   needlessly bloat the top level model we delegate the exact definition of
   these states to the instantiation via our abstraction paradigm.

   All other internal states of the core are mapped to OTHER, i.e., this is our
   catch-all state for cases where the internal state is irrelevant to
   externally visible execution.
*) 
val _ = Datatype `AbsCIstate = FLUSHED | GICD_RS GPRguest | GICD_RNS
			     | GICD_WS GPRguest | GICD_WNS | OTHER`;


(*************** actions and messages ****************)

(* Message - the overall datatype for all Messages passed between components
   (core, memory, mmu, smmu, peripheral, GIC, power controller)

   we use the same format for ideal and refined model messages, however some
   messages are only used in the ideal model.

   MREQ r - memory request message from core/peripheral, requesting r from
   second stage MMU/SMMU (or message box in ideal model)

   MRPL q - memory reply from MMU/SMMU (or ideal msgbox) core/peripheral

   SREQ r s - a request r from sender s to memory / a peripheral / the GIC,
   depending on address, the memory forwards memory-mapped I/O requests to the
   corresponding peripheral or the GIC. We restrict DMA accesses by peripherals
   to the memory, to keep the model simple. These requests are generated by the
   MMU/SMMU (or ideal msgbox).

   SRPL q s - a reply to a memory request from sender s, either sent to the
   MMU/SMMU of s by the memory or sent by the peripheral to the memory in order
   to later forward the reply to the MMU of core sender s.

   PHYS (SOME q / NONE) c: Physical interrupt from GIC to core c. In the refined
   model only NONE is used, as there is only a single interrupt line for IRQs
   that cannot hold the interrupt ID. In the ideal model SOME q is used in a
   PHYS message to distribute a pending interrupt in the distributer to the
   virtualized core interface of c. This reflects the way the hypervisor handles
   interrupt delivery. On the refined model PHYS interrupts are always trapped
   by the hypervisor and injected as virtual interrupts into the guest.

   VIRT c - a virtual interrupt to core c from the GIC, only used in the refined
   model as on the ideal model all interrupts are considered physical. Virtual
   interrupts are always trapped into the guest.

   PERQ q: physical interrupt q from a peripheral to the GIC

   PSCIL l: list of power commands l sent by core to power controller 

   PEV l: list of peripheral events received or sent by peripheral

   ONLY IN IDEAL MODEL:

   SIGC s: request for IGC notification interrupt on channel s

   RCU cn s (SOME co / NONE): message for determining the receiver core for an
   IGC interrupt on channel s. The receiving guest's power controller determines
   to send the notification interrupt to core co if that one is active and to
   none if all cores of the targeted guests are powered down. This reflects the
   implementation of the notification interrupt by the hypervisor where the
   choice of the receiver core depends on the guests power state.

   STARTUP g c: power up core c of guest g at reset. This is the equivalent of
   completing the refined model boot sequence in the ideal model. There the boot
   sequence is invisible and cores are kicked off initially by this message.
*)
val _ = Datatype `Message = MREQ request | MRPL reply 
			  | SREQ request senderID | SRPL reply senderID 
			  | PHYS (irqID option) num | VIRT num 
			  | PERQ irqID | PSCI event | PSCIL (event list) 
			  | PEV (pevent list) | SIGC num | IGCE num num
			  | RCU num num (num option) | STARTUP num num`;


(* as in the paper, there are send/receive/internal actions,
   we do not model external messages explicitly here for simplicity *)
val _ = Datatype `Action = SEND Message | RCV Message | TAU`;

(******************** PERIPHERAL WRAPPER **********************)

(* wrapper object around peripheral state, 
   
   used for bookkeeping of received and unanswered I/O messages. 

   This could be internal to the peripheral state but it would complicate the
   bisimulation definition as ideal and refined peripherals would need to
   distinguish ideal and refined sender IDs (which are not identical).
   
   Alternatively this could be part of the memory abstraction, as the memory
   forwards memory-mapped I/O requests and replies between the cores and
   peripherals. We place it closer to the peripherals in order to restrict their
   behaviours, e.g., to respond only to requests they have received.
    
   IOreq_rcvd r = NONE - request r was not received
   IOreq_rcvd r = SOME s - request r was received from sender s 
*)   
val _ = Hol_datatype `periph_wrapper = 
<| st : peripheral; IOreq_rcvd: request -> senderID option |>`;

(******************** IDEAL MODEL **********************)

(*** component types and state records ***)

(* sigc: component storing he state of pending igc interrupt

   flags s <=> outgoing message (IGC interrupt) is pending for channel s

   addressbook s = SOME c - 
   interrupt on channel s targeted at core c in receiving guest

   addressbook s = NONE - 
   target core for interrupt on channel s not determined yet
*)
val _ = Hol_datatype `sigc = 
<| flags : num -> bool; addressbook: num -> num option |>`;


(* psci_state - power controller state (both for refined model and each guest
   
   puw c <=> core c is powered up 
   events c = l - queue l of power commands is pending for core c

   The intuition here is that power commands are processed asyncronously by the
   power controller, queueing requests from the cores, processing them one by
   one, and popping them from the corresponding queue.
*)
val _ = Hol_datatype `psci_state =
  <| pow: num -> bool;
     events: num -> event list
 |>`;


(* bus_interface - MMU placeholder in ideal model 

   To simplify the coupling with the refined model, the second stage MMUs/SMMUs
   are represented as message buffers in the ideal model. No translation from
   intermediate physical to physical addresses takes place, messages are just
   buffered here until the translation in the underlying refined model is
   finished and requests are either forwarded to the memory or (in case of
   faults and replies) returned to the requesting core/peripheral. These buffers
   are at the interface to the memory bus, hence the name.

   req_rcvd - set of received/pending memory requests from a core/peripheral
   req_sent - set of forwarded memory requests that were not answered yet
   req_rcvd - set of received memory replies, to be forwarded to sender
*)
val _ = Hol_datatype `bus_interface =
  <| req_rcvd: request set;
     req_sent: request set;
     rpl_rcvd: reply set
 |>`;

(* guest - guest state record 

   C c - ideal model core state of the guest's core with index c
   cif c - stand-in for second stage MMU of core c as explained above
   m - intermediate-physical page-addressable guest memory
   P p - peripheral state of the guests peripheral p
   pif p - stand-in for SMMU of peripheral p as explained above
   GIC - the ideal GIC that each guest sees as exposed by the hypervisor 
   PSCI - power controller state
   E_in - list of received external events for the guest's peripherals
   E_out - list of sent external events by the guest's peripherals
   sIGC - records the pending IGC interrupts to other guests
 *)
val _ = Hol_datatype `guest =
  <| C: num -> idcore; 
     cif: num -> bus_interface; 
     m: memory; 
     P: num -> periph_wrapper; 
     pif: num -> bus_interface; 
     GIC: idgic;  
     PSCI: psci_state; 
     E_in: pevent list; 
     E_out: pevent list;
     sIGC: sigc   
 |>`;

(*** state abstractions for uninstantiated components ***)

(* idgic_config - ideal GIC abstraction

   This is an abstraction of the ideal GIC that only exposes what we need for
   the top level bisimulation proof. 

   gicc c R - the GIC core interface control register R for core c 

   The ideal GIC core interface allows each core to control among other things
   which interrupts will be signalled to it. Also this interface is used to
   acknowledge interrupt reception to the GIC and obtain the ID of the
   corresponding interrupt.

   gicd R - the GIC distributor register R

   The GIC distributor controls which interrupts are enabled, to which cores
   they can be mapped, including interprocessor interrupts. The ideal
   distributor functionality is restricted according to the interrupt isolation
   policy of the hypervisor.

   Q c q = x - interrupt q at core c has interrupt state x, e.g., PENDING

   This component represents the (virtual) interrupts for each core as scheduled
   by the hypervisor. In the ideal world peripheral interrupts or IPIs first
   become pending in the distributor and are then distributed to the core
   interrupt interface, represented by Q. This reflects the interrupt handling
   implemented by the hypervisor in the refined model: first the distributor
   interrupts a core directly, invoking the hypervisor who in a second step
   configures the virtual interrupt interface to send a corresponding virtual
   interrupt once the guest is running again.

   The status of Q cannot be read directly by the cores, instead they need to
   use the memory-mapped interface gicc. Hence some of the information contained
   in gicc and Q is redundant and needs to be kept in sync via invariants.
*)
val _ = Hol_datatype `idgic_config =
  <|
      gicc: num -> (GICCreg -> bool[32]);
      gicd: GICDreg -> bool[32];
      Q: num -> irqID -> IRQstate
  |>`;


(* idcore_hist - some history information for the ideal core

   launch <=> the core was not launched yet after system start

   this flag controls the LAUNCH transition that starts the ideal core execution
   after boot and initialization on the underlying refined model is completed.
*)
val _ = Hol_datatype `idcore_hist =
  <| 
     launch: bool
  |>`;


(* idcore_config - abstraction of the ideal core state 

   active - the core is powered on
   PC - program counter
   PSTATE - the processor state, including arithmetic flags and config infos
   GPR R - the general purpose register with name R
   SPR R - the EL0/EL1-accessible special purpose register with name R
   H - history information
*)
val _ = Hol_datatype `idcore_config =
  <| 
     active: bool;
     PC: bool[64];
     PSTATE: bool[32];
     GPR: GPRguest -> bool[64];
     SPR: SPRguest -> bool[64];
     H: idcore_hist
  |>`;


(******************** IMAGES **********************)

(* here we define the structure of images processed by the secure boot
loader. These are copied by the loader from non-volatile memory (FLASH) and
executed if they are signed by a key that matches the hash of the public root
key that is stored in the hardware platform. *)

(* the type of the signatures that come with the images
   
   We omit all details specific to the signature scheme here for simplicity and
   just treat the signatures as a blob of 32 bytes representing the signed hash
   of the image.

   for an instantiation of the signature scheme, 
   the detailed structure of the signature should be plugged in here
*)
val _ = Datatype `Signature = SIG (bool[256])`;

(* the information pertaining to a HASPOC image

   This data structure does not reflect the layout of the image in memory but
   rather contains all the necessary information for building the image, storing
   it into flash memory and securely loading it during the boot process.
  
   adr - the page address where the image is stored
   isz - the size of the image in number of pages
   dadr - the page address in physical memory where the contained data 
          should be copied
   dsz - the number of data pages to be copied
   data i - the contained data for page i, for dadr <= i < dadr + dsz
   sig - the associated cryptographic signature of the image 
   entry = SOME a - the image is executable and execution should start at 
		    virtual address a
   entry = NONE - the image contains only data and is not executable
   EL = SOME x - the image should be executed at execution level ELx, 
		 where 0 <= x <= 3
   EL = NONE - the image is not executable
*)
val _ = Hol_datatype `haspoc_image =
  <| adr: bool[36];
     isz: num;
     dadr: bool[36];
     dsz: num;
     data: bool[36] -> PAGE;
     sig: Signature;
     entry: bool[64] option;
     EL: num option
 |>`;

(* images used on the HASPOC platform 
   
   IMG_RK - root of trust public key corresponding to the root key hash burned
            into the hardware
   IMG_HV - image of the hypervisor (excluding secure boot)
   IMG_HVconf - image containing hypervisor configuration data, i.e., 
                the parameters for the set up of the guests
   IMG_G g - image for the code and data of guest g
   IMG_Gconf g - configuration data for guest g, used by the guest
   IMG_Mconf - firmware for the DRAM memory controller
   IMG_BOOT - the second stage of the secure bootloader
*)

val _ = Datatype `HASPOC_IMAGES = IMG_RK | IMG_HV | IMG_HVconf | IMG_G num | IMG_Gconf num | IMG_Mconf | IMG_BOOT`;


(******************** REFINED MODEL **********************)

(* state of the refined model

   C c - state of refined core c, for c < RPAR.nc
   PSCI - state of the power controller
   m - state of the memory subsystem
   MMU c - state of the second stage MMU for core c
   SMMU p - state of the SMMU for peripheral p < RPAR.np
   GIC - state of the generic interrupt controller
   P p - state of peripheral p
   E_in - list of external inputs to the peripherals
   E_out - list of external ouputs from the peripherals
*)
val _ = Hol_datatype `refined_model =
  <| C: num -> refcore;
     PSCI: psci_state;
     m: memory;
     MMU: num -> mmu;
     SMMU: num -> mmu;
     GIC: gic;
     P: num -> periph_wrapper;
     E_in: pevent list;
     E_out: pevent list
 |>`;

(* history variables for a single refined core

   We use these flags to keep track of the initialization process at system
   start and define the invariants that are being established by it. When the
   system boots the primary core executes the boot loader and the global
   hypervisor configuration phase. Each core is associated with exactly one
   guest, and the (virtual) primary core within that guest takes care of
   initializing the hypervisor accordingly. Finally, before guest code can run
   on a core the local configuration phase has to be completed.

   init_boot - boot loader finished
   init_hv - global hypervisor initialization finished
   init_guest - hypervisor initialization for corresponding guest finished
   init_core - local hypervisor initialization on this core finished
   launched - initialization finished, guest code was executed on this core
*)
val _ = Hol_datatype `refcore_hist =
  <| init_boot: bool;
     init_hv: bool;
     init_guest: bool;
     init_core: bool;
     launched: bool
  |>`;


(* abstraction of the refined core state, 

   this is similar to the ideal core state, just that EL2 and EL3 SPRs are
   exposed and we have different history variables

   active - the core is powered up
   PC - program counter
   PSTATE - flags and config information, e.g., the current execution level
   GPR - general purpose registers, accessible at EL0 and EL1
   SPR - special purpuse registers, accessible at EL0-EL3
   H - history variables
 *)
val _ = Hol_datatype `refcore_config =
  <| active: bool;
     PC: bool[64];
     PSTATE: bool[32];
     GPR: GPRguest -> bool[64];
     SPR: SPRguest + SPRhyp -> bool[64];
     H: refcore_hist
  |>`;


(* the execution level as defined in PSTATE[3:2] *)
val MODE_def = Define `MODE (ps:bool[32]) = 
                     w2n((word_extract 3 2 ps):bool[2]) `;
		     (* exception level *)
(* the execution level of a given abstract refined core *)
val mode_def = Define `mode (C:refcore_config) = MODE(C.PSTATE)`;
(* MODE_upd ps x = ps' - set new mode in ps' from natural number x *)
val MODE_upd_def = Define `MODE_upd (ps:bool[32], x : num) = 
	             bit_field_insert 3 2 ((n2w x):bool[2]) ps
`;

(* Lemma: execution level is always between 0 and 3 *)
val MODE_bound_lem = store_thm("MODE_bound_lem", ``
!ps. MODE ps <= 3
``,
  RW_TAC std_ss [MODE_def, wordsTheory.w2n_def] >>
  Cases_on `(3 >< 2) ps: bool[2]` >>
  FULL_SIMP_TAC std_ss [wordsTheory.dimword_2] >>
  EVAL_TAC >> 
  DECIDE_TAC
);

(* Lemma: execution level of abstract cores is always between 0 and 3 *)
val mode_bound_lem = store_thm("mode_bound_lem", ``
!C. mode C <= 3
``,
  RW_TAC std_ss [mode_def, MODE_bound_lem]
);

(* current abstract MMU state for a given memory request 

   used for both second stage MMUs and SMMUs

   - IDLE - request has not been received
   - TRANS (SOME r) - request has been received and address translation has
     issued a page table walk request r to the memory
   - TRANS NONE - request has been received and address translation is ongoing,
     however no corresponding page table lookup is currently pending
   - FINAL (SOME r) - address translation of the request has succeeded and the
     translated request r has been sent to memory
   - FINAL NONE - address translation of the request has succeeded but the
     translated request has not been sent to memory yet
   - FAULT - request has resulted in a fault
*)
val _ = Datatype `MMUstate = IDLE | TRANS (request option) 
			   | FINAL (request option) | FAULT`;


(* abstract state of MMUs
   
   active - address translation is enabled (always while guest is running
   state r - translation state of request r
   cfg - configuration state of the MMU, e.g., the page table base address and
   page size, this is set by the hypervisor only and stays constant during guest
   execution, this information is usually set through registers in the core, so
   it is duplicated here and updated for every translation request according to
   the core registers, the exact format is determined by instantiation of the
   MMU model and left uninterpreted here.
*)
val _ = Hol_datatype `mmu_config =
  <| active: bool;
     state: request -> MMUstate;
     cfg: MMUcfg
  |>`;



(* abstract state of the generic interrupt controller
   
   gicc c - interrupt core interface registers for core c, only accessed by the
   hypervisor
   gicd - global distributor interface registers, only accessed directly by the
   hypervisor, virtualized for each guest
   gich c - virtual interface controller registers for core c, only accessed by
   the hypervisor
   gicv c: Virtual interrupt controller core interface for core c, this is
   configured by the hypervisor through gicv and accessed in guest mode
*)
val _ = Hol_datatype `gic_config =
  <|
      gicc: num -> (GICCreg -> bool[32]);
      gicd: GICDreg -> bool[32];
      gich: num ->  (GICHreg -> bool[32]);
      gicv: num ->  (GICCreg -> bool[32])
  |>`;


(*************** HV abstraction ***************)

(* Abstract hypervisor state, affected by HV transitions 

   The hypervisor transitions are global system transitions that may affect not
   only the core on which the hypervisor transition is executed but also the
   corresponding second stage MMU, the SMMUs and the memory. Since we do not
   which to model the hypervisor on a memory transaction granularity (except for
   interactions with the GIC) a hypervisor transaction may affect all these
   resources in addition to the core registers in a single atomic step. However
   after initialization the (S)MMUs are not touched again and the MMU
   configuration is only affected by disabling the second stage address
   translation during hypervisor execution. Similarly, after initialization is
   finished, memory updates only target the hypervisor memory.

   C - abstract core configuration for the core running the hypervisor
   req_sent - pending memory requests (only for requests to the GIC)
   MMU - The second stage MMU state of the core concerned, off while EL>1
   SMMU p - the SMMU state for peripheral p, all SMMUs can be controlled by all
   HV threads, however their configuration is fixed during initialization
*)
val _ = Hol_datatype `hv_state =
  <| C: refcore_config;
     req_sent: request set;
     m: bool[36] -> PAGE;
     MMU: mmu_config;
     SMMU: num -> mmu_config
 |>`;



(*************** lemmas ***************)

(* some corollaries of above definitions *)

(* Lemma: removing all matching replies from a request set X *)
val match_out_lem = 
    store_thm("match_out_lem",
       ``!q r X. match(q,r) ==> q NOTIN (X DIFF {x | match(x,r)})``,
       FULL_SIMP_TAC (srw_ss()) []);

(* Lemma: matching replies are different from mismatching replies 
          for a given request *)
val match_diff_lem = 
    store_thm("match_diff_lem",
       ``!q r x. match(q,x) ==> ~ match(r,x) ==> q <> r``, 
       FULL_SIMP_TAC (srw_ss()) []);


(* alternative definition for Frpl,
   as suggested bt Thomas Tuerk *)
val Frpl_ALT_DEF = store_thm ("Frpl_ALT_DEF",
  ``Frpl r <=> (?r' f. r = Fault r' f)``,
   Cases_on `r` THEN
   SIMP_TAC (std_ss++DatatypeSimps.type_rewrites_stateful_ss()) [Frpl_def]);

(* Lemma: if a fault reply matches request r, the fault was wrt. r *)
val Frpl_match_lem = store_thm("Frpl_match_lem",
   ``(Frpl q /\ match(r,q)) <=> (?f. q = Fault r f)``,
    EQ_TAC THEN (
        TRY (Cases_on `r`) THEN (
            TRY (Cases_on `q`)  THEN (
                RW_TAC (srw_ss()) [Frpl_def, match_def] )
	)
    )
);

(* Lemma: as above but inlined def of Frpl *)
val match_Fault_lem = store_thm("match_Fault_lem", ``
!r r' i. match (r, Fault r' i) ==> (r = r')
``,
  Cases >> (
      RW_TAC std_ss [match_def]
  )
);

(* Lemma: non-faulty matches for page table walk requests r 
          are WalkResults for r *)
val PTreq_match_lem = store_thm("PTreq_match_lem",
   ``(PTreq r /\ match(r,q) /\ ~Frpl q) ==> 
     (?i v. q = WalkResult (Walk (Adr r) i) v)``,
   Cases_on `r` THEN (
       Cases_on `q` THEN (
           RW_TAC (srw_ss()) [PTreq_def, match_def, Adr_def, Frpl_def] 
       )
   )
			       );

(* Lemma: there exists only one matching request for any given reply *)
val unique_match_thm = store_thm("unique_match_thm",
     ``!q r r'.  match(r,q) /\ match(r',q) ==> (r = r')``,
      REPEAT GEN_TAC THEN STRIP_TAC THEN 
      Cases_on `r` THEN (
          Cases_on `r'` THEN (
	      Cases_on `q` THEN (
	          FULL_SIMP_TAC (srw_ss()) [match_def]
	      )
	  )
      )
);

(* Lemma: 
   - a reply cannot match all requests
   - a request cannot match all replies
   - the set of all replies contains at least two different replies
   - the set of all requests contains at least two different requests
*)
val not_all_req_rep_lem =
     store_thm("not_all_req_rep_lem",
     ``   (!r. ~(!q. match(q,r)))
       /\ (!q. ~(!r. match(q,r)))
       /\ (!X. (!x:reply.   x IN X) ==> 
	       (?x1 x2. x1 <> x2 /\ x1 IN X /\ x2 IN X))
       /\ (!X. (!x:request. x IN X) ==> 
	       (?x1 x2. x1 <> x2 /\ x1 IN X /\ x2 IN X))``,
     RW_TAC (srw_ss()) []
     THENL [     Cases_on `r`
            THEN RW_TAC (srw_ss()) []
            THEN Cases_on `r'`
            THEN FIRST [EXISTS_TAC ``Walk a i`` THEN 
			FULL_SIMP_TAC (srw_ss()) [match_def] THEN 
			NO_TAC
		        ,
                        EXISTS_TAC ``Read c n m`` THEN 
			FULL_SIMP_TAC (srw_ss()) [match_def] THEN 
			NO_TAC],
                 Cases_on `q`
            THEN RW_TAC (srw_ss()) [match_def]
            THEN EXISTS_TAC ``WalkResult (Read c n m) v``
            THEN FULL_SIMP_TAC (srw_ss()) [],
                 EXISTS_TAC ``WalkResult (Read c n m) v``
            THEN EXISTS_TAC ``WrittenValue (Read c n m)``
            THEN FULL_SIMP_TAC (srw_ss()) [],
                 EXISTS_TAC ``Read c n m``
            THEN EXISTS_TAC ``Walk a i``
            THEN FULL_SIMP_TAC (srw_ss()) []]);


(* Lemma:
   - a read reply can only match a read request, it is not a write request 
   - a write reply can only match a write request
   - a walk reply can only match a walk request, it is not a write request 
   - no request ever matches a misshaped read reply for a walk request
*)
val req_types_match_lem =
    store_thm("req_types_match_lem",
              ``  (!r r' l. match(r,ReadValue r' l) ==> 
		      (r' = r)  /\ (?a d i. r' = Read a d i ) /\ ~Wreq r')
               /\ (!r r'. match(r,WrittenValue r') ==> 
		      (r' = r) /\ (?w x y z. r' = Write w x y z ) /\ Wreq r')
               /\ (!r r' x. match(r,WalkResult r' x) ==> 
		      (r' = r) /\ (?a i. r' = Walk a i) /\ ~Wreq r')
               /\ (!r x y z.  ~match(r,ReadValue (Walk x y) z))``,
             RW_TAC (srw_ss()) []
               THEN Cases_on `r`
               THEN TRY (Cases_on `r'`)
               THEN FULL_SIMP_TAC (srw_ss()) [match_def, Wreq_def]);



(* Lemma: the possible cases for matching requests and replies, in verbatim *)
val resolve_match_cases_lem = 
     store_thm("resolve_match_cases_lem",
              ``!req rpl. match(req,rpl) ==>
                   (?a d i v. (req = Read a d i) /\ 
			(rpl = ReadValue (Read a d i) v) /\ 
			~Wreq (Read a d i))
                \/ (?a d i v. (req = Write a d v i) /\ 
			(rpl = WrittenValue (Write a d v i)) /\ 
			Wreq (Write a d v i))
                \/ (?a i v. (req = Walk a i) /\ 
			(rpl = WalkResult (Walk a i) v) /\ 
			~Wreq(Walk a i))
                \/ (?fi. (rpl = Fault req fi))``,
              RW_TAC (srw_ss()) []
               THEN TRY (Cases_on `req`)
               THEN TRY (Cases_on `rpl`)
               THEN FULL_SIMP_TAC (srw_ss()) [match_def, Wreq_def]);


(* Lemma: PAdr (Write w x y z) = (47 >< 12) w *)
val PAdrWrite_lem = save_thm("PAdrWrite_lem",
GEN_ALL ((SIMP_CONV (srw_ss()) [PAdr_def, Adr_def])
	     ``PAdr (Write w x y z)``));


(* Lemma: if i<=3, MODE_upd updates the mode successfully *)
val MODE_upd_lem = 
    store_thm("MODE_upd_lem",
    ``!x i. (i <= 3) ==> (MODE(MODE_upd(x,i)) = i)``,
    ASSUME_TAC (blastLib.BBLAST_PROVE 
       ``((3 >< 2) (bit_field_insert 3 2 (y:word2) ((x:word32)))) = (y:word2)``
       |> GEN_ALL)
    THEN RW_TAC (srw_ss()) [MODE_upd_def, MODE_def]
    THEN FULL_SIMP_TAC arith_ss []);

(* Lemma: request r matches reply q if r is the request answered by q *)
val match_ReqOf_lem =
    store_thm("match_ReqOf_lem",
    ``match(rq,rp) ==> (ReqOf rp = rq)``,
    METIS_TAC [resolve_match_cases_lem, ReqOf_def]);

(* substitutes
   "there is a matching request satisfying ..." with
   "the request of that reply satisfies ..." *)
val unique_req_lem = store_thm(
   "unique_req_lem", ``
       (  (?r.  match (r,q) /\ P0 r)
        = (match (ReqOf q,q) /\  P0 (ReqOf q))) 
    /\ (  (?r. P1 r /\ match (r,q) /\ P2 r)
        = (P1 (ReqOf q) /\ match (ReqOf q,q) /\  P2 (ReqOf q))) 
    /\ (  (?r. P1 r /\ match (r,q))
        = (P1 (ReqOf q) /\ match (ReqOf q,q)))
    /\ ((?r. P1 r /\ P2 r /\  match (r,q))
        = (P1 (ReqOf q) /\ P2 (ReqOf q) /\ match (ReqOf q,q)))
    /\ (  (?r. A /\ A' /\ P1 r /\ match (r,q) /\ P2 r)
        = (A /\ A' /\ P1 (ReqOf q) /\ match (ReqOf q,q) /\  P2 (ReqOf q)))
    /\ (  (?r p. A /\ P1 r /\ match (r, q))
        = (?p. A /\ P1 (ReqOf q) /\ match (ReqOf q, q)))
    /\ (  (?r p. Pp p /\ Prp r p /\ match (r, q))
        = (?p. Pp p /\ Prp (ReqOf q) p /\ match (ReqOf q, q)))``, 
   METIS_TAC [match_ReqOf_lem, unique_match_thm, ReqOf_def]);


(* trivial datatype lemmas *)

val guest_trivial_upd_m_lem =
    store_thm("guest_trivial_upd_m_lem",
    ``!G:guest. G = G with m:= G.m``,
    Cases_on `G` THEN SRW_TAC [] (TypeBase.updates_of ``:guest``));


(* contributions for simplification sets,
   only add here what you can accept to always being rewritten *)

val obvious_req_rep_attributes_lem =
    store_thm("obvious_req_rep_attributes_lem",
    ``( Wreq (Write a d v i))  /\ (~Wreq (Read a d i))     /\ 
      (~Wreq (Walk a i))       /\ (~Frpl (WrittenValue r)) /\ 
      (~Frpl (ReadValue r v))  /\ (~Frpl (WalkResult r x)) /\ 
      ( Frpl (Fault r f))
``,
    FULL_SIMP_TAC (srw_ss()) [Wreq_def, Frpl_def] THEN
    REPEAT CASE_TAC THEN
    FULL_SIMP_TAC (srw_ss()) []);

val obvious_matches_lem =
    store_thm("obvious_matches_lem",
       ``   match(Write a d v i, WrittenValue (Write a d v i))
         /\ match(Read a d i, ReadValue (Read a d i) z)
         /\ match(Walk a i, WalkResult (Walk a i) x)
         /\ match(r, Fault r f) ``,
    Cases_on `r` THEN (	      
        FULL_SIMP_TAC (srw_ss()) [match_def] )
);

val obvious_mismatches_lem =
    store_thm("obvious_mismatches_lem",
       ``   (~match(r, WrittenValue (Read a d i)))
         /\ (~match(r, WrittenValue (Walk a i)))
         /\ (~match(r, ReadValue (Walk a i) z))
         /\ (~match(r, ReadValue (Write a d v i) z))
         /\ (~match(r, WalkResult (Write a d v i) x))
         /\ (~match(r, WalkResult (Read a d i) x))
         /\ (~match(Write a d v i, WalkResult r x))
         /\ (~match(Write a d v i, ReadValue r z))
         /\ (~match(Read a d i, WrittenValue r))
         /\ (~match(Read a d i, WalkResult r x))
         /\ (~match(Walk a i, WrittenValue r))
         /\ (~match(Walk a i, ReadValue r z))``,
    Cases_on `r` THEN (	      
        FULL_SIMP_TAC (srw_ss()) [match_def] )
);

(* extract message info from request *)
val MsgOf_rewrites =
    save_thm("MsgOf_rewrites",
              LIST_CONJ (map (SIMP_CONV (srw_ss()) [MsgOf_def]) 
              [``MsgOf (Read a d m)``, 
	       ``MsgOf (Write a d v m)``, 
	       ``MsgOf (Walk a m)``]));

(* Lemma: requests cannot be both read and walk requests *)
val Rreq_not_PTreq_lem = store_thm("Rreq_not_PTreq_lem", ``
!r. ~Rreq r \/ ~PTreq r
``,
  Cases THEN 
  RW_TAC (srw_ss()) [Rreq_def, PTreq_def]
);

(* Lemma: walk requests always read 8 bytes *)
val PTreq_Sz_lem = store_thm("PTreq_Sz_lem", ``
!r. PTreq r ==> (SzOf r = 8)
``,
  Cases THEN 
  RW_TAC (srw_ss()) [PTreq_def, SzOf_def]
);

(* Lemma: cases for good (not misshaped) replies *)
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

(* Lemma: faults are always good replies *)
val good_Frpl_lem = store_thm("good_Frpl_lem", ``
!q. Frpl q ==> good_rpl q
``,
  RW_TAC std_ss [Frpl_ALT_DEF] >>
  RW_TAC std_ss [good_rpl_def]
);

(* Lemma: matching replies are always good *)
val good_match_lem = store_thm("good_match_lem", ``
!r q. match(r,q) ==> good_rpl q
``,
  Cases THEN 
  RW_TAC (srw_ss()) [DatatypeSimps.cases_to_top_RULE match_def, 
		     good_rpl_cases_lem]
);

(* Lemma: good replies always match the request they answer *)
val good_match_ReqOf_lem = store_thm("good_match_ReqOf_lem", ``
!q. good_rpl q ==> match(ReqOf q,q)
``,
  Cases >> 
  RW_TAC pure_ss [good_rpl_cases_lem, ReqOf_def] >>
  REWRITE_TAC [obvious_matches_lem]
);

(* Lemma: matching requests and replies target the same address *)
val match_Adr_eq_lem = store_thm("match_Adr_eq_lem", ``
!r q. match(r,q) ==> (Adr r = Rpl_Adr q)
``,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  IMP_RES_TAC good_match_lem THEN 
  Cases_on `r` THEN (
      FULL_SIMP_TAC (srw_ss()) [good_rpl_cases_lem, match_def] THEN (
          FULL_SIMP_TAC (srw_ss()) [] THEN 
	  RW_TAC (srw_ss()) [Adr_def, Rpl_Adr_def]
      )
  )
);	    

(* Lemma: matching requests and replies target the same page *)
val match_PAdr_eq_lem = store_thm("match_PAdr_eq_lem", ``
!r q. match(r,q) ==> (PAdr r = Rpl_PAdr q)
``,
  RW_TAC (srw_ss()) [] THEN 
  IMP_RES_TAC match_Adr_eq_lem THEN 
  RW_TAC (srw_ss()) [PAdr_def, Rpl_PAdr_def] 
);

(* Lemma: this is the converse of:
          "when two different replies match the same request, 
           they can only differ in the returned value" *)
val match_Rpl_eq_lem = store_thm("match_Rpl_eq_lem", ``
!r q q'. match(r,q) /\ match(r,q') /\ Rpl_val_eq q q' ==> (q = q')
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC good_match_lem >>
  IMP_RES_TAC good_rpl_cases_lem >> (
      FULL_SIMP_TAC std_ss [Rpl_val_eq_def] >>
      Cases_on `r` >> (
          FULL_SIMP_TAC std_ss [match_def, TypeBase.distinct_of ``:reply``,
				TypeBase.one_one_of ``:reply``]
      )
  )
);

(* Lemma: the Rpl_val_eq relation implies with the equlity of reply values,
          for good replies that are not both faults,

          NOTE: if the replies have different types Rpl_val_eq is false
                and the lemma holds vacuously *)
val Rpl_val_lem = store_thm("Rpl_val_lem", ``
!q q'. good_rpl q /\ good_rpl q' /\ 
       (~Frpl q \/ ~Frpl q') /\ Rpl_val_eq q q' ==> 
    (Rpl_val q = Rpl_val q')
``,
  REPEAT STRIP_TAC >> (
      IMP_RES_TAC good_rpl_cases_lem >> (
          FULL_SIMP_TAC std_ss [Rpl_val_eq_def, Rpl_val_def, Frpl_def]
      )
  )
);

(* Lemma: Rpl_val_eq is reflexive for good replies *)
val Rpl_val_eq_refl_lem = store_thm("Rpl_val_eq_refl_lem", ``
!q. good_rpl q ==> Rpl_val_eq q q
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC good_rpl_cases_lem >> (
      RW_TAC std_ss [Rpl_val_eq_def]
  )
);

(* Lemma: Rpl_val_eq is symmetric *)
val Rpl_val_eq_sym_lem = store_thm("Rpl_val_eq_sym_lem", ``
!q q'. Rpl_val_eq q q' ==> Rpl_val_eq q' q
``,
  Cases >> (
      Cases >> (
          RW_TAC std_ss [Rpl_val_eq_def]
      )
  ) >>
  Cases_on `r` >> (
      Cases_on `r'` >> (
          FULL_SIMP_TAC std_ss [Rpl_val_eq_def]
      )
  )      
);

(* Lemma: Rpl_val_eq is transitive *)
val Rpl_val_eq_trans_lem = store_thm("Rpl_val_eq_trans_lem", ``
!q q' q''. Rpl_val_eq q q' /\ Rpl_val_eq q' q'' ==> Rpl_val_eq q q''
``,
  Cases >> (
      Cases >> (
          Cases >> (
              RW_TAC std_ss [Rpl_val_eq_def]
	  )
      )
  ) >>
  Cases_on `r` >> (
      Cases_on `r'` >> (
          Cases_on `r''` >> (
              FULL_SIMP_TAC std_ss [Rpl_val_eq_def]
	  )
      )
  )      
);

(* gic lemmas *)

(* expand equality gicd registers *)
val gicd_eq_lem = store_thm("gicd_eq_lem", ``
!gicd gicd'.
(gicd = gicd')
    <=>
   (!R. gicd (CONST R) = gicd' (CONST R))
/\ (!R. gicd (MUTE R) = gicd' (MUTE R))
/\ (!R. gicd (VOL R) = gicd' (VOL R))
``,
  REPEAT GEN_TAC >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC (srw_ss()) []
      ,
      (* <== *)
      REPEAT STRIP_TAC >>
      `!r. gicd r = gicd' r` by ( 
          Cases >> ( METIS_TAC [] )
      ) >>
      METIS_TAC []
     ]
);

(* Lemma: the reply address of good replies equals their request's address *)
val Rpl_Adr_ReqOf_lem = store_thm(
   "Rpl_Adr_ReqOf_lem",
   ``good_rpl q ==> (Rpl_Adr q = Adr (ReqOf q))``,
    METIS_TAC [good_match_ReqOf_lem, match_Adr_eq_lem]);


(* Lemma: same as above but for page addresses *)
val Rpl_PAdr_ReqOf_lem = store_thm(
   "Rpl_PAdr_ReqOf_lem",
   ``good_rpl q ==> (Rpl_PAdr q = PAdr (ReqOf q))``,
    METIS_TAC [good_match_ReqOf_lem, match_PAdr_eq_lem]);


(* Lemma: for replies q for sender s, the set of matching requests (and senders)
is the singleton set containing just the request that q answers (plus sender s):
   - if there is a matching request for q (always the case for good replies)
   - if q is a good reply
*)
val matching_request_set_lem = store_thm(
   "matching_request_set_lem",
   ``  (match(r0,q) ==> ({(r,s) | match(r,q)} = {(ReqOf q, s)}))
    /\ (good_rpl q ==> ({(r,s) | match(r,q)} = {(ReqOf q, s)}))
    /\ (match(r0,q) ==> ({r | match(r,q)} = {ReqOf q}))
    /\ (good_rpl q ==> ({r | match(r,q)} = {ReqOf q}))``,
   FULL_SIMP_TAC (srw_ss()) [pred_setTheory.EXTENSION, unique_req_lem] >>
   METIS_TAC [match_ReqOf_lem, good_match_ReqOf_lem]);


(* rewrites for refined model updates wrt. core component *) 
val core_after_RM_update_lem = store_thm(
   "core_after_RM_update_lem", ``
     (((RM:refined_model) with <|m := _ ; SMMU := _ |>).C = RM.C)
  /\ (((RM:refined_model) with <|m := _ ; GIC := _ |>).C = RM.C)
  /\ (((RM:refined_model) with <|C := (c =+ C') RM.C; MMU := _ |>).C c = C')
  /\ ((c <> c') ==> (((RM:refined_model) with 
                     <|C := (c' =+ C') RM.C; MMU := _ |>).C c = RM.C c)) ``,
 RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]);

(*************** finish ***********)

val _ = export_theory();
