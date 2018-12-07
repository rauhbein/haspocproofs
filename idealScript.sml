(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib;

open axtypesTheory;
open haspoctypesTheory;
open parametersTheory;
open axfuncsTheory;
open hypervisorTheory;

open tacticsLib;
open toolboxLib;
open math_lemmasTheory;
open annotationsLib; infix //; infix ///; infix -:;

val _ = new_theory "ideal";


(******************  GUEST MODEL   **************)

(* The steps defined at the beginning of this file specify the pre- 
   and post conditions to be met for an ideal guest action to be 
   possible with respect to the involved interface/component.
   
   Often an action would involve two components, for instance a core 
   receiving an interrupt would go along with an interrupt controller 
   sending the interrupt.
   Later down, steps are therefore combined to rules.
   Together they form the transition system of an ideal guest. 

   The states and transition systems of the several guests are finally
   composed to an overall ideal model.

   We define invariants for the ideal guest transition systems and
   composed model.
   Furthermore, several lemmas are proven in this theory.               *)


(**************** Core steps *****************)


(*******************************************************************************
idcore_step ( ideal input core, 
	      action,
	      ideal output core )

wrapper for ideal core step, the following steps are possible:
 - receive physical interrupt
 - receive memory reply message
 - receive power management event, i.e., power up or down
 - send memory request
 - send list of commands to power controller
 - send request for IGC notification interrupt to IGC message box
 - core reset event for startup, only possible initially
 - internal core step, e.g., arithmetic operation 
*******************************************************************************)
val idcore_step_def = Define `
idcore_step (C : idcore, a : Action, C' : idcore) =
        case a of
          | RCV (PHYS NONE c)  => idcore_step_rcv_phys(C,C')
          | RCV (MRPL r) => idcore_step_rcv_rpl(C,r,C')
          | RCV (PSCI e) => idcore_step_rcv_psci(C,e,C')
          | SEND (MREQ r) => idcore_step_snd_req(C,r,C')
          | SEND (PSCIL l) => idcore_step_snd_pscil(C,l,C')
          | SEND (SIGC s) => idcore_step_snd_igc(C,s,C')
          | RCV (STARTUP g c) => idcore_step_startup(C,g,c,C')
          | TAU => idcore_step_internal(C,C')
          | _   => F`;



(***************** PSCI steps ******************)

(** most parts should be identical to the refined model,
    so we avoid to overwrite these definitions here **)

(* update receiving core for IGC *)
(* choose first core that is powered on *)
val idpsci_step_snd_rcu_def = Define `
idpsci_step_snd_rcu (PS : psci_state, cn:num, s:num, 
		     co:num option, PS' : psci_state) =
(PS' = PS) /\ (co = let available = (\c. (c < cn) /\ (PS.pow c)) 
		    in (if (available = EMPTY)
			then NONE else SOME (MIN_SET available)))
`;


(*******************************************************************************
idcpsci_step (input psci state, 
	      action,
              core numer,
	      output psci state)

ideal PSCI (power management) step, the following steps are possible:
 - receive list of events
 - send list of events
 - update receiving core for IGC
*******************************************************************************)

val idpsci_step_def = Define `
idpsci_step (PS : psci_state, a : Action, c: num, PS' : psci_state) =
        case a of
          | RCV (PSCIL l)  => psci_step_rcv_elist(PS,l,PS')
          | SEND (PSCI e) => psci_step_snd_event(PS,e,c,PS')
          | SEND (RCU cn s co) => idpsci_step_snd_rcu(PS,cn,s,co,PS')
          | _   => F
`;


(**************** bus interface (message box) steps *****************)
(* A bus interface is essentially a message box between a core or peripheral
   and the memory. While in the ideal model it simply is a forwarding proxy,
   it will be matched with an (S)MMU in the refined model *)


(* receive request *)
val bif_step_rcv_req_def = Define `bif_step_rcv_req (B:bus_interface, r:request, B':bus_interface) =
       r NOTIN B.req_rcvd
    /\ (B' = B with req_rcvd := (B.req_rcvd UNION {r}))`;

(* send request *)
(* forward received request if not done already and if reply not received yet *)
val bif_step_snd_req_def = Define `bif_step_snd_req (B:bus_interface, r:request, B':bus_interface) =
       (r IN B.req_rcvd)
    /\ (r NOTIN B.req_sent)
    /\ (!q. q IN B.rpl_rcvd  ==> ~ match(r,q))
    /\ (B' = B with req_sent := (B.req_sent UNION {r}))`;

(* receive reply *)
val bif_step_rcv_rpl_def = Define `bif_step_rcv_rpl (B:bus_interface, r:reply, B':bus_interface) =
       (?q. q IN B.req_rcvd /\ q IN B.req_sent /\ match(q,r))
    /\ (B' = B with <|rpl_rcvd := (B.rpl_rcvd UNION {r});
                      req_sent := (B.req_sent DIFF {q | match(q,r)}) |>)`;

(* send reply *)
val bif_step_snd_rpl_def = Define `bif_step_snd_rpl (B:bus_interface, r:reply, B':bus_interface) =
       (?q. q IN B.req_rcvd /\ match(q,r))
    /\ (r IN B.rpl_rcvd)
    /\ (B' = B with <|rpl_rcvd := (B.rpl_rcvd DIFF {r});
                   req_rcvd := (B.req_rcvd DIFF {q | match(q,r)}) |>)`;

(* send fault *)
val bif_step_snd_fault_def = Define `bif_step_snd_fault (B:bus_interface, r:reply,TI, B':bus_interface) =
       (Frpl r)
    /\ (?q. q IN B.req_rcvd /\ match(q,r) /\ (fiOf r = golden_fi TI q))
    /\ (r NOTIN B.rpl_rcvd)
    /\ (!q. q IN B.req_sent ==> ~ (match(q,r))) (* bif-generated faults only for non-forwarded requests *)
    /\ (B' = B with req_rcvd := (B.req_rcvd DIFF {q | match(q,r)}))`;



(*******************************************************************************
bif_step (input bus interface, 
	  action,
          output bus interface)

bus interface step, the following steps are possible:
 - receive reply
 - receive request
 - send request
 - forward reply/fault
*******************************************************************************)

val bif_step_def = Define `bif_step (B : bus_interface, a : Action, B' : bus_interface) =
        case a of
          | RCV (SRPL r id) => bif_step_rcv_rpl(B,r,B')
          | RCV (MREQ r) => bif_step_rcv_req(B,r,B')
          | SEND (SREQ r id) => bif_step_snd_req(B,r,B')
          | SEND (MRPL r) => (bif_step_snd_rpl(B,r,B') \/ 
			      ?TI. bif_step_snd_fault(B,r,TI,B'))
          | _   => F`;

(* lemma on effects of forwarding replies *)
val bif_step_snd_reply_lem = store_thm("bif_step_snd_reply_lem", ``
!B q B' r. bif_step_snd_rpl (B, q, B')
       /\ match(r,q)
            ==>
          q IN B.rpl_rcvd
       /\ (B'.rpl_rcvd = B.rpl_rcvd DIFF {q})
       /\ (B'.req_rcvd = B.req_rcvd DIFF {r})
       /\ (B'.req_sent = B.req_sent)
``,
  RW_TAC std_ss [bif_step_snd_rpl_def] >>
  `r = q'` by ( METIS_TAC [unique_match_thm] ) >>
  `{q' | match (q',q)} = {r}` suffices_by (
      RW_TAC std_ss []
  ) >>
  RW_TAC std_ss [pred_setTheory.EXTENSION, pred_setTheory.IN_GSPEC_IFF,
		 pred_setTheory.IN_SING] >>
  METIS_TAC [unique_match_thm]
);

(* lemma on effects of sending fault *)
val bif_step_snd_fault_lem = store_thm("bif_step_snd_fault_lem", ``
!B q B' TI r. bif_step_snd_fault (B, q, TI, B')
       /\ match(r,q)
            ==>
          q NOTIN B.rpl_rcvd
       /\ (B'.rpl_rcvd = B.rpl_rcvd)
       /\ (B'.req_rcvd = B.req_rcvd DIFF {r})
       /\ (B'.req_sent = B.req_sent)
``,
  RW_TAC std_ss [bif_step_snd_fault_def] >>
  `r = q'` by ( METIS_TAC [unique_match_thm] ) >>
  `{q' | match (q',q)} = {r}` suffices_by (
      RW_TAC std_ss []
  ) >>
  RW_TAC std_ss [pred_setTheory.EXTENSION, pred_setTheory.IN_GSPEC_IFF,
		 pred_setTheory.IN_SING] >>
  METIS_TAC [unique_match_thm]
);


(**************** GIC steps *****************)

(*******************************************************************************
idgic_step (input ideal GIC interface, 
	    action,
            guest number,
            output ideal GIC interface)

gic interface step, the following steps are possible:
 - receive request
 - receive interrupt
 - distribute pending physical interrupt to specified CPU interface
 - send interrupt
 - send reply
 - receive IGC
*******************************************************************************)

val idgic_step_def = Define `idgic_step (G : idgic, a : Action, g:num, G' : idgic) =
        case a of
          | RCV (SREQ r id) => idgic_step_rcv_req(G,r,id,G')
          | RCV (PERQ q) => idgic_step_rcv_irq(G,q,g,G')
          | RCV (PHYS (SOME q) c) => idgic_step_dist_irq(G,q,c,g,G')
          | SEND (PHYS NONE c) => idgic_step_snd_irq(G,c,G')
          | SEND (SRPL r id) => idgic_step_snd_rpl(G,r,id,g,G')
          | RCV (IGCE s c) => idgic_step_rcv_igc(G,s,c,G')
          | _   => F
`;




(**************** sIGC steps *****************)

(* send pending IGC signal in channel s to core c in receiving guest *)
val sigc_step_snd_igc_def = Define `sigc_step_snd_igc (S : sigc, s: num, c:  num, S' : sigc) =
      (S.flags s)
   /\ (S.addressbook s = SOME c)
   /\ (S' = S with <| flags := (s =+ F) S.flags |>) `;

(* add IGC signal for core co to channel s *)
(* receiving RCU is now done together with receiving an sIGC signal from the core *)
val sigc_step_rcv_rcu_def = Define `sigc_step_rcv_rcu (S: sigc, s:num, co: num option, S': sigc) =
     (S' = S with <| addressbook := (s =+ co) S.addressbook; flags := (s =+ T) S.flags |>)  `;


(*******************************************************************************
sigc_step (input sIGC interface, 
	    action,
            output sIGC interface)

sIGC interface step, the following steps are possible:
 - send out IGC signal from channel
 - add IGC signal to channel
*******************************************************************************)

val sigc_step_def = Define `sigc_step (S:sigc, a : Action, S':sigc) =
        case a of
          | SEND (IGCE s c) => sigc_step_snd_igc(S,s,c,S')
          | RCV (RCU cn s co) => sigc_step_rcv_rcu(S,s,co,S')
          | _   => F
`;


(**************** Memory steps *****************)
(** should be identical to the refined model,
  so we will avoid to overwrite its definitions here **)


(**************** Synchronized Steps within Guest *****************)

val id_rule_core_startup_def = Define `id_rule_core_startup (G:guest, g: num, c: num, G': guest) =
?C'.
      idcore_step(G.C c, RCV(STARTUP g c), C')
   /\ (G' = G with C := (c =+ C') G.C)`;


val id_rule_core_rcv_irq_def = Define `id_rule_core_rcv_irq (G: guest, c : num, G' : guest) =
          ?gic' C'.
                 (idcore_req_sent (G.C c) = EMPTY)
              /\ idcore_step(G.C c, RCV( PHYS NONE c), C')
              /\ idgic_step(G.GIC,SEND( PHYS NONE c), 0, gic')
              /\ (G' = G with <| GIC := gic'; C := (c =+ C') G.C |>)`;


val id_rule_core_snd_req_def = Define `id_rule_core_snd_req (G : guest, c : num, G' : guest) =
?r C' cif'.
             idcore_step(G.C c, SEND(MREQ r), C')
          /\ bif_step(G.cif c, RCV(MREQ r), cif')
          /\ (G' = G with <| C := (c =+ C') G.C; cif := (c =+ cif') G.cif |>)
`;


val id_rule_cif_snd_req_def = Define `id_rule_cif_snd_req (G : guest, r:request, c : num, G' : guest) =
?cif' mem'.
             bif_step(G.cif c, SEND(SREQ r (CoreSender c)), cif')
          /\ mem_step(G.m , RCV(SREQ r (CoreSender c)), NONE, mem')
          /\ (G' = G with <| cif := (c =+ cif') G.cif; m := mem' |>)
`;

val id_rule_cif_snd_fault_def = Define `id_rule_cif_snd_fault (G:guest, r:reply, c : num, G': guest) =
?C' cif' q.
             Frpl r
          /\ idcore_step(G.C c, RCV(MRPL r), C')
          /\ bif_step(G.cif c, SEND(MRPL r), cif')
          /\ q IN idcore_req_sent (G.C c) /\ match (q,r)
          /\ (G' = G with <| C := (c =+ C') G.C; cif := (c =+ cif') G.cif |>)
`;


val id_rule_core_rcv_rpl_def = Define `id_rule_core_rcv_rpl (G : guest, c : num, G' : guest) =
?r C' cif' q.
             idcore_step(G.C c, RCV(MRPL r), C')
          /\ bif_step(G.cif c, SEND(MRPL r), cif')
          /\ q IN idcore_req_sent (G.C c) /\ match (q,r)
          /\ r IN (G.cif c).rpl_rcvd (* guarantees that cif-generated faults are not enabled by this rule,
                                        but only by the appropriate rule that comes with address restrctions *)
          /\ (G' = G with <| C := (c =+ C') G.C; cif := (c =+ cif') G.cif |>)
`;

val id_rule_cif_rcv_rpl_def = Define `id_rule_cif_rcv_rpl (G : guest, c : num, G' : guest) =
?r cif' mem' q.
             bif_step(G.cif c, RCV(SRPL r (CoreSender c)), cif')
          /\ mem_step(G.m , SEND(SRPL r (CoreSender c)), NONE, mem')
          /\ q IN (G.cif c).req_sent /\ match (q,r)
          /\ (G' = G with <| cif := (c =+ cif') G.cif; m := mem' |>)
`;


val id_rule_core_rcv_event_def = Define `id_rule_core_rcv_event (G : guest, c : num, G' : guest) =
?e PS' C'.
            (idcore_req_sent (G.C c) = EMPTY)
         /\ ~(idcore_abs(G.C c)).H.launch
         /\ idpsci_step(G.PSCI, SEND(PSCI e), c, PS')
         /\ idcore_step(G.C c, RCV(PSCI e), C')
         /\ ((e = StartCore c) \/ (e = StopCore c))
         /\ (G' = G with <| C := (c =+ C') G.C; PSCI := PS'|>)
`;

val id_rule_core_internal_def = Define `id_rule_core_internal (G : guest, c : num, G' : guest) =
?C'. idcore_step(G.C c, TAU, C') /\ (G' = G with <| C := (c =+ C') G.C|>)
`;

val id_rule_core_snd_elist_def = Define `id_rule_core_snd_elist (G : guest, g : num, c : num, G' : guest) =
?l C' PS'.
              idcore_step(G.C c, SEND(PSCIL l), C')
           /\ idpsci_step(G.PSCI, RCV(PSCIL l), c, PS')
           /\ (!e. MEM e l ==>
               case e of
                 | StartCore c' => c' < PAR.nc_g g
                 | StopCore c' => c' < PAR.nc_g g
                 | _ => F )
           /\ (G' = G with <| C := (c =+ C') G.C; PSCI := PS'|>)
`;

val id_rule_core_fail_psci_def = Define `id_rule_core_fail_psci (G : guest, g : num, c : num, G' : guest) =
?l C'.
              idcore_step(G.C c, SEND(PSCIL l), C')
           /\ (?e c'. MEM e l /\ ((e = StartCore c') \/ (e = StopCore c')) /\ c' >= PAR.nc_g g)
           /\ (G' = G with <| C := (c =+ C') G.C|>)
`;

(* TODO: increase PC *)
val id_rule_core_fail_sigc_def = Define `id_rule_core_fail_sigc (G : guest, g : num, c : num, G' : guest) =
?C' s.
              idcore_step(G.C c, SEND (SIGC s), C')
           /\ ((s = PAR.ns) \/ G.sIGC.flags s \/ FST (PAR.cpol s) <> g)
           /\ (G' = G with <| C := (c =+ C') G.C|>)
`;

val id_rule_per_snd_dmareq_def = Define `id_rule_per_snd_dmareq (G : guest, p : num, G' : guest) =
?r pif' P'.
              bif_step(G.pif p, RCV(MREQ r), pif')
           /\ per_wrap_step(G.P p, SEND(MREQ r), P')
           /\ (G' = G with <| pif := (p =+ pif') G.pif; P := (p =+ P') G.P|>)
`;

val id_rule_pif_snd_dmareq_def = Define `id_rule_pif_snd_dmareq (G : guest, r: request, p : num, G' : guest) =
?MEM' pif'.
              mem_step(G.m, RCV(SREQ r (PeripheralSender p)), NONE, MEM')
           /\ bif_step(G.pif p, SEND(SREQ r (PeripheralSender p)), pif')
           /\ (G' = G with <| m := MEM'; pif := (p =+ pif') G.pif|>)
`;

val id_rule_pif_snd_fault_def = Define `id_rule_pif_snd_fault (G:guest, r:reply, p : num, g:num, G': guest) =
?P' pif' q.
             Frpl r
          /\ per_wrap_step(G.P p, RCV(MRPL r), P')
          /\ bif_step_snd_fault(G.pif p, r, 
			        (GIP g,SMMU_GI g,RPAR.A_PPT g, golden_RO g),
				pif')
          /\ q IN per_req_sent (G.P p).st /\ match (q,r)
          /\ (G' = G with <| P := (p =+ P') G.P; pif := (p =+ pif') G.pif |>)
`;


val id_rule_per_rcv_dmarpl_def = Define `id_rule_per_rcv_dmarpl (G : guest, p : num, G' : guest) =
?r pif' P' q.
              bif_step_snd_rpl(G.pif p, r, pif')
           /\ per_wrap_step(G.P p, RCV(MRPL r), P')
           /\ q IN per_req_sent (G.P p).st /\ match (q,r)
           /\ r IN (G.pif p).rpl_rcvd (* guarantees that pif-generated faults are not enabled by this rule,
                                         but only by the appropriate rule that comes with address restrctions *)
           /\ (G' = G with <| pif := (p =+ pif') G.pif; P := (p =+ P') G.P|>)
`;


val id_rule_pif_rcv_dmarpl_def = Define `id_rule_pif_rcv_dmarpl (G: guest, p : num, G' : guest) =
?r MEM' pif' q.
              mem_step(G.m, SEND(SRPL r (PeripheralSender p)), NONE, MEM')
           /\ bif_step(G.pif p, RCV(SRPL r (PeripheralSender p)), pif')
           /\ q IN (G.pif p).req_sent /\ match (q,r)
           /\ (G' = G with <| m := MEM'; pif := (p =+ pif') G.pif|>)
`;


(* fix cores as sole IO request senders, can be extended here *)
val id_rule_per_rcv_ioreq_def = Define `id_rule_per_rcv_ioreq (G : guest, r:request, p : num, g:num, G' : guest) =
?m' P' c.
             mem_step(G.m, SEND(SREQ r (CoreSender c)), NONE, m')
          /\ per_wrap_step(G.P p, RCV(SREQ r (CoreSender c)), P')
          /\ c < PAR.nc_g g
          /\ (G' = G with <|m := m'; P := (p =+ P') G.P|>)
`;

(* TODO: we do not have a transition for updating E_in *)
val id_rule_per_rcv_pev_def = Define `id_rule_per_rcv_pev (G : guest, p : num, G' : guest) =
?P'. per_wrap_step(G.P p, RCV(PEV (iPEF (G.E_in,p))), P') /\ 
     (G' = G with <|P := (p =+ P') G.P|>)
`;


(* fix cores as sole IO request senders, can be extended here *)
val id_rule_per_snd_iorpl_def = Define `id_rule_per_snd_iorpl (G : guest, p : num, g:num, G' : guest) =
?r m' P' c q.
             mem_step(G.m, RCV(SRPL r (CoreSender c)), NONE, m')
          /\ per_wrap_step(G.P p, SEND(SRPL r (CoreSender c)), P')
          /\ c < PAR.nc_g g
          /\ (q, CoreSender c) IN mem_req_sent (G.m) /\ match(q,r)
          /\ (G' = G with <|m := m'; P := (p =+ P') G.P|>)
`;


val id_rule_per_snd_pev_def = Define `id_rule_per_snd_pev  (G : guest, g: num, p : num, G' : guest) =
?P' l.
        per_wrap_step(G.P p, SEND(PEV l), P')
     /\ (!e. MEM e l ==> (PPP (evper e) = p) /\ (PPG (evper e) = g))
     /\ (G' = G with <|P := (p =+ P') G.P; E_out := G.E_out ++ l|>)
`;

val id_rule_per_snd_irq_def = Define `id_rule_per_snd_irq  (G : guest, q: num, p : num, g:num, G' : guest) =
?P' GIC'.
        per_wrap_step(G.P p, SEND(PERQ (PIR q)), P')
     /\ idgic_step(G.GIC, RCV(PERQ (PIR q)), g, GIC')
     /\ (G' = G with <|P := (p =+ P') G.P; GIC := GIC'|>)
`;

val id_rule_per_internal_def = Define `id_rule_per_internal (G : guest, p : num, G' : guest) =
?P'. per_wrap_step(G.P p, TAU, P') /\ (G' = G with <|P := (p =+ P') G.P|>)
`;


(* IO requests to the GIC only from Cores *)
val id_rule_gic_rcv_ioreq_def = Define `id_rule_gic_rcv_ioreq (G: guest, r:request, g:num, G': guest) =
?m' GIC' c.
             mem_step(G.m, SEND(SREQ r (CoreSender c)), NONE, m')
          /\ idgic_step(G.GIC, RCV(SREQ r (CoreSender c)), 0, GIC')
          /\ c < PAR.nc_g g
          /\ (G' = G with <|m := m'; GIC := GIC'|>)
`;

val id_rule_gic_snd_iorpl_def = Define `id_rule_gic_snd_iorpl (G : guest, g : num, G' : guest) =
?r m' GIC' c q.
             c < PAR.nc_g g
          /\ idgic_step(G.GIC, SEND(SRPL r (CoreSender c)), g, GIC')
          /\ mem_step(G.m, RCV(SRPL r (CoreSender c)), NONE, m')
          /\ (q, CoreSender c) IN mem_req_sent (G.m) /\ match(q,r)
          /\ (G' = G with <|m := m'; GIC := GIC'|>)
`;

(* irq injection rule *)
val id_rule_gic_dist_def = Define `id_rule_gic_dist (G : guest, q:irqID, c:num, g:num, G' : guest) =
?GIC'.
             idgic_step(G.GIC, RCV(PHYS (SOME q) c), g, GIC')
          /\ (G' = G with <|GIC := GIC'|>)
`;

val id_rule_mem_internal_def = Define `id_rule_mem_internal  (G : guest, g:num, G' : guest) =
?m'. mem_step(G.m, TAU, SOME g, m') /\ (G' = G with <|m := m'|>)
`;


val id_rule_external_snd_igc_def = Define `id_rule_external_snd_igc (G, s, c, G') =
?sigc'.
     sigc_step(G.sIGC, SEND(IGCE s c), sigc')
  /\ (G' = G with <| sIGC := sigc' |>)`;

val id_rule_external_rcv_igc_def = Define `id_rule_external_rcv_igc (G, s, c, G') =
?gic'.
     idgic_step(G.GIC, RCV(IGCE s c), 0,  gic')
  /\ (G' = G with <| GIC := gic' |>)`;

val id_rule_external_snd_rcu_def = Define `id_rule_external_snd_rcu (G:guest, cn, s, co, G':guest) =
?psci'.
     idpsci_step(G.PSCI, SEND (RCU cn s co), cn, psci')
  /\ (G' = G with <| PSCI := psci' |>)`;

(* receiving RCU is now done together with receiving an sIGC signal from the core *)
val id_rule_external_rcv_rcu_def = Define `id_rule_external_rcv_rcu (G, s, c, co, G') =
?sigc' C'.
     sigc_step(G.sIGC, RCV (RCU 0 s co), sigc')
  /\ idcore_step(G.C c, SEND (SIGC s), C')
  /\ (G' = G with <| sIGC := sigc'; C := (c =+ C') G.C  |>)`;

val id_rule_external_input_def = Define `id_rule_external_input (G:guest, g, l, G') =
(G' = G with <| E_in := G.E_in ++ PEL(l,g) |>)`;


(**************** Ideal Model Transition System ***************)

val _ = Datatype `Ideal_Internal_Rule = IR_CORE_RCV_IRQ num | IR_CORE_RCV_MRPL num | IR_CORE_RCV_EVENT num | IR_CORE_SND_MREQ num | IR_CORE_INTERNAL num | IR_CORE_SND_ELIST num | IR_CORE_FAIL_PSCI num | IR_CORE_FAIL_SIGC num | IR_PER_RCV_DMARPL num | IR_PER_RCV_IOREQ request num | IR_PER_RCV_PEV num | IR_PER_SND_DMAREQ num | IR_PER_SND_IORPL num | IR_PER_SND_PEV num | IR_PER_SND_IRQ num num | IR_PER_INTERNAL num | IR_GIC_RCV_IOREQ request | IR_GIC_SND_IORPL | IR_GIC_DIST irqID num | IR_MEM_INTERNAL | IR_CIF_SND_SREQ request num | IR_CIF_RCV_SRPL num | IR_PIF_SND_DMAREQ request num | IR_PIF_RCV_DMARPL num | IR_CIF_FAULT reply num | IR_PIF_FAULT reply num | IR_RULE_STARTUP num `;

val _ = Datatype `Ideal_External_Message = IGC_ num num | RCU_ num (num option) | INPUT (pevent list)`;

val _ = Datatype `Ideal_Rule = INTERNAL Ideal_Internal_Rule | EXTERNAL_SND Ideal_External_Message | EXTERNAL_RCV Ideal_External_Message`;

val ideal_guest_trans_def = Define `ideal_guest_trans (G: guest, g:num, R : Ideal_Rule, G': guest) =
        case R of
          | INTERNAL (IR_RULE_STARTUP c_) => c_ < (PAR.nc_g g) /\ id_rule_core_startup (G, g, c_, G')
          | INTERNAL (IR_CORE_RCV_IRQ c0) => c0 < (PAR.nc_g g) /\ id_rule_core_rcv_irq(G,c0,G')
          | INTERNAL (IR_CORE_RCV_MRPL c1) => c1 < (PAR.nc_g g) /\ id_rule_core_rcv_rpl(G,c1,G')
          | INTERNAL (IR_CIF_RCV_SRPL c1') => c1' < (PAR.nc_g g) /\ id_rule_cif_rcv_rpl(G,c1',G')
          | INTERNAL (IR_CORE_RCV_EVENT c2) => c2 < (PAR.nc_g g) /\ id_rule_core_rcv_event(G,c2,G')
          | INTERNAL (IR_CORE_SND_MREQ c3) => c3 < (PAR.nc_g g) /\ id_rule_core_snd_req(G,c3,G')
          | INTERNAL (IR_CIF_SND_SREQ r c3') => c3' < (PAR.nc_g g)
             /\ PAdr r IN (PAR.A_G g)
             /\ (PAdr r IN RPAR.Amap GICD ==>
                      ~(gicd_acc_not_supported (MsgOf r)) /\ gicd_req_ok r)
             /\ (PAdr r IN receiverMem g ==> ~Wreq r)
             /\ id_rule_cif_snd_req(G,r,c3',G')
          | INTERNAL (IR_CIF_FAULT r c3'') => c3'' < (PAR.nc_g g)
             /\ (    Rpl_PAdr r NOTIN (PAR.A_G g)
                 \/ (?req. match (req,r) /\ PAdr req IN receiverMem g /\ Wreq req)
                 \/ (Rpl_PAdr r IN RPAR.Amap GICD /\ (?req.
                       req IN (G.cif c3'').req_rcvd /\ match (req,r)
                   /\ ((gicd_acc_not_supported (MsgOf req)) \/ ~gicd_req_ok req) )))
             /\ id_rule_cif_snd_fault(G,r,c3'',G')
          | INTERNAL (IR_CORE_INTERNAL c4) => c4 < (PAR.nc_g g) /\ id_rule_core_internal(G,c4,G')
          | INTERNAL (IR_CORE_SND_ELIST c5) => c5 < (PAR.nc_g g) /\ id_rule_core_snd_elist(G,g,c5,G')
          | INTERNAL (IR_CORE_FAIL_PSCI c) => c < (PAR.nc_g g) /\ id_rule_core_fail_psci(G,g,c,G')
          | INTERNAL (IR_CORE_FAIL_SIGC c) => c < (PAR.nc_g g) /\ id_rule_core_fail_sigc(G,g,c,G')
          | INTERNAL (IR_PER_RCV_DMARPL p0) => p0 < (PAR.np_g g) /\ id_rule_per_rcv_dmarpl(G,p0,G')
          | INTERNAL (IR_PIF_RCV_DMARPL p0') => p0' < (PAR.np_g g) /\ id_rule_pif_rcv_dmarpl(G,p0',G')
          | INTERNAL (IR_PER_RCV_IOREQ r p1) => p1 < (PAR.np_g g) /\ (PAdr r) IN (PAR.A_gp g p1) /\ id_rule_per_rcv_ioreq(G,r,p1,g,G')
          | INTERNAL (IR_PER_RCV_PEV p2) => p2 < (PAR.np_g g) /\ id_rule_per_rcv_pev(G,p2,G')
          | INTERNAL (IR_PER_SND_DMAREQ p3) => p3 < (PAR.np_g g) /\ id_rule_per_snd_dmareq(G,p3,G')
          | INTERNAL (IR_PIF_SND_DMAREQ r p3') =>  p3' < (PAR.np_g g)
                                                /\ PAdr r IN (PAR.A_G g)
                                                /\ PAdr r NOTIN RPAR.Amap GICC
                                                /\ PAdr r NOTIN RPAR.Amap GICD
                                                /\ (PAdr r IN receiverMem g ==> ~Wreq r)
                                                /\ (!p_. p_ < PAR.np_g g ==> PAdr r NOTIN (PAR.A_gp g p_))
                                                /\ id_rule_pif_snd_dmareq(G,r,p3',G')
          | INTERNAL (IR_PIF_FAULT r p3'') =>  p3'' < (PAR.np_g g)
                                            /\ (   Rpl_PAdr r NOTIN (PAR.A_G g)
                                                \/ Rpl_PAdr r IN RPAR.Amap GICC
                                                \/ Rpl_PAdr r IN RPAR.Amap GICD
                                                \/ (?req. match (req,r) /\ PAdr req IN receiverMem g /\ Wreq req)
                                                \/ (?p_. p_ < PAR.np_g g /\ Rpl_PAdr r IN (PAR.A_gp g p_)))
                                            /\ id_rule_pif_snd_fault(G,r,p3'',g,G')
          | INTERNAL (IR_PER_SND_IORPL p4) => p4 < (PAR.np_g g) /\ id_rule_per_snd_iorpl(G,p4,g,G')
          | INTERNAL (IR_PER_SND_PEV p5) => p5 < (PAR.np_g g) /\ id_rule_per_snd_pev(G,g,p5,G')
          | INTERNAL (IR_PER_SND_IRQ q p6) => p6 < (PAR.np_g g) /\ (PIR q) IN ((PAR.pirq_gp) g p6) /\
                                               q >= 16 /\ q < 1020  /\ id_rule_per_snd_irq(G,q,p6,g,G')
          | INTERNAL (IR_PER_INTERNAL p7) => p7 < (PAR.np_g g) /\ id_rule_per_internal(G,p7,G')
          | INTERNAL (IR_GIC_RCV_IOREQ r) => (PAdr r IN RPAR.Amap GICC \/ PAdr r IN RPAR.Amap GICD) /\ id_rule_gic_rcv_ioreq(G,r,g,G')
          | INTERNAL (IR_GIC_SND_IORPL) => id_rule_gic_snd_iorpl(G,g,G')
(* TODO: only possible if no IGC interrupt pending for receiving core 
   because of priority issues,
   need to pass sIGC information of other guest from top level *)
          | INTERNAL (IR_GIC_DIST q' c') =>    c' < (PAR.nc_g g)
                                            /\ (idcore_req_sent(G.C c') = EMPTY)
                                            /\ (id_abs_int(G.C c') = FLUSHED)
                                            /\ id_rule_gic_dist(G,q',c',g,G')
          | INTERNAL (IR_MEM_INTERNAL) => id_rule_mem_internal(G,g,G')
          | EXTERNAL_SND (IGC_ s2 c8) =>       s2 < PAR.ns
                                            /\ (FST (PAR.cpol s2) = g)
                                            /\ c8 < (PAR.nc_g g)
                                            /\ id_rule_external_snd_igc (G,s2,c8,G')
          | EXTERNAL_RCV (IGC_ s3 c9) =>        s3 < PAR.ns
                                             /\ (SND (PAR.cpol s3) = g)
                                             /\ c9 < (PAR.nc_g g)
                                             /\ (idcore_req_sent(G.C c9) = EMPTY)
                                             /\ (id_abs_int(G.C c9) = FLUSHED)
                                             /\ id_rule_external_rcv_igc (G,s3,c9,G')
          | EXTERNAL_SND (RCU_ s4 co1) =>       s4 < PAR.ns
                                             /\ (SND (PAR.cpol s4) = g)
                                             /\ (case co1 of | NONE => T | SOME c_ => (c_ < (PAR.nc_g g)))
                                             /\ id_rule_external_snd_rcu (G,PAR.nc_g g,s4,co1,G')
          | EXTERNAL_RCV (RCU_ s5 co2) =>    (?c6.
                                                s5 < PAR.ns
                                             /\ (FST (PAR.cpol s5) = g)
                                             /\ c6 < (PAR.nc_g g)
                                             /\ id_rule_external_rcv_rcu (G, s5, c6, co2, G'))
	  | EXTERNAL_RCV (INPUT l) => id_rule_external_input (G, g, l, G')

          | _ => F`;




(* each reply set has not more than one reply per request *)
val id_inv_unique_rpl_def = Define `id_inv_unique_rpl (G:guest, g:num) =
    (!r q1 q2 c. c < PAR.nc_g g ==> q1 IN (G.cif c).rpl_rcvd ==> q2 IN  (G.cif c).rpl_rcvd
      ==> match(r,q1) ==> match(r,q2) ==> (q1 = q2))
 /\ (!r q1 q2 p. p < PAR.np_g g ==> q1 IN (G.pif p).rpl_rcvd ==> q2 IN  (G.pif p).rpl_rcvd
      ==> match(r,q1) ==> match(r,q2) ==> (q1 = q2))
 /\ (!r q1 q2 s. (q1,s) IN (mem_rpl_rcvd G.m) ==> (q2,s) IN (mem_rpl_rcvd G.m)
      ==> match(r,q1) ==> match(r,q2) ==> (q1 = q2))`;

val id_inv_unique_rpl_bif_def = Define `id_inv_unique_rpl_bif bif =
    !r q1 q2. q1 IN bif.rpl_rcvd ==> q2 IN bif.rpl_rcvd ==> match(r,q1) ==> match(r,q2) ==> (q1 = q2)`;

val id_inv_unique_rpl_mem_def = Define `id_inv_unique_rpl_mem m =
    !r q1 q2 s. (q1,s) IN (mem_rpl_rcvd m) ==> (q2,s) IN (mem_rpl_rcvd m)
              ==> match(r,q1) ==> match(r,q2) ==> (q1 = q2)`;

val id_inv_unique_rpl_def' = store_thm(
   "id_inv_unique_rpl_def'", ``id_inv_unique_rpl (G,g) =
    (!c. c < PAR.nc_g g ==> id_inv_unique_rpl_bif (G.cif c)) /\
    (!p. p < PAR.np_g g ==> id_inv_unique_rpl_bif (G.pif p)) /\
    (id_inv_unique_rpl_mem (G.m))``,
    EQ_TAC >>
    RW_TAC bool_ss [id_inv_unique_rpl_def, id_inv_unique_rpl_bif_def, id_inv_unique_rpl_mem_def] >>
    RES_TAC);


(* all requests received in cif are currently pending in corresponding core,
   all cif requests sent have been received,
   all requests received in mem are currently pending in corresponding cif *)
val id_inv_cifreq_def = Define `id_inv_cifreq (G:guest, g:num) =
!c. c < PAR.nc_g g ==>
   (!r. r IN idcore_req_sent (G.C c) <=> r IN (G.cif c).req_rcvd)
/\ (!r. r IN (G.cif c).req_sent ==> r IN (G.cif c).req_rcvd)
/\ (!r. r IN (G.cif c).req_sent <=> (r, CoreSender c) IN mem_req_rcvd (G.m))`;

val id_inv_cifreq_core_def = Define `id_inv_cifreq_core (C:idcore) (cif:bus_interface) =
  !r. r IN idcore_req_sent C <=> r IN cif.req_rcvd`;

val id_inv_bifreq_def = Define `id_inv_bifreq (bif:bus_interface) =
  !r. r IN bif.req_sent ==> r IN bif.req_rcvd`;

val id_inv_bifreq_mem_def = Define `id_inv_bifreq_mem m s (bif:bus_interface) =
  !r. r IN bif.req_sent <=> (r, s) IN mem_req_rcvd m`;

val id_inv_cifreq_def' = store_thm(
   "id_inv_cifreq_def'", ``id_inv_cifreq (G, g) =
   !c. c < PAR.nc_g g ==>
     id_inv_cifreq_core (G.C c) (G.cif c) /\
     id_inv_bifreq (G.cif c) /\
     id_inv_bifreq_mem (G.m) (CoreSender c) (G.cif c)``,
    REWRITE_TAC [id_inv_cifreq_def, id_inv_cifreq_core_def, id_inv_bifreq_def, id_inv_bifreq_mem_def]);


(* all DMA requests received in pif are currently pending in corresponding peripheral,
   all pif requests sent have been received,
   all DMA requests received in mem are currently pending in corresponding pif *)
val id_inv_pifreq_def = Define `id_inv_pifreq (G:guest, g:num) =
!p. p < PAR.np_g g ==>
   (!r. r IN per_req_sent (G.P p).st <=> r IN (G.pif p).req_rcvd)
/\ (!r. r IN (G.pif p).req_sent ==> r IN (G.pif p).req_rcvd)
/\ (!r. r IN (G.pif p).req_sent <=>  (r, PeripheralSender p) IN mem_req_rcvd (G.m))`;

val id_inv_pifreq_per_def = Define `id_inv_pifreq_per P (pif:bus_interface) =
  !r. r IN per_req_sent P.st <=> r IN pif.req_rcvd`;

val id_inv_pifreq_def' = store_thm(
   "id_inv_pifreq_def'", ``id_inv_pifreq (G, g) =
   !p. p < PAR.np_g g ==>
     id_inv_pifreq_per (G.P p) (G.pif p) /\
     id_inv_bifreq (G.pif p) /\
     id_inv_bifreq_mem (G.m) (PeripheralSender p) (G.pif p)``,
    REWRITE_TAC [id_inv_pifreq_def, id_inv_pifreq_per_def, id_inv_bifreq_def, id_inv_bifreq_mem_def]);

     
(* all pending GIC IO requests are sent by memory and addressed either to GICD or GICC *)
val id_inv_gicreq_def = Define `id_inv_gicreq (G : guest, g:num) =
!r s. ((r, s) IN idgic_req_rcvd (G.GIC) <=>
       ((r, s) IN mem_req_sent (G.m) /\ (PAdr r IN RPAR.Amap GICC \/ PAdr r IN RPAR.Amap GICD)))`;

val id_inv_gicreq__def = Define `id_inv_gicreq_ GIC m =
!r s. ((r, s) IN idgic_req_rcvd GIC <=>
       ((r, s) IN mem_req_sent m /\ (PAdr r IN RPAR.Amap GICC \/ PAdr r IN RPAR.Amap GICD)))`;

val id_inv_gicreq_def' = store_thm(
   "id_inv_gicreq_def'", ``id_inv_gicreq (G, g) = id_inv_gicreq_ (G.GIC) (G.m)``,
   REWRITE_TAC [id_inv_gicreq_def, id_inv_gicreq__def]);


(* all pending peripheral IO requests are sent by memory and addressed to the corresponding peripheral memory *)
val id_inv_perreq_def = Define `id_inv_perreq (G : guest, g:num) =
!p. p < PAR.np_g g ==>
(!r s. ((G.P p).IOreq_rcvd r = SOME s) <=>
((r, s) IN mem_req_sent (G.m) /\ PAdr r IN PAR.A_gp g p))`;

val id_inv_perreq__def = Define `id_inv_perreq_ P m g p =
(!r s. (P.IOreq_rcvd r = SOME s) <=>
((r, s) IN mem_req_sent m /\ PAdr r IN PAR.A_gp g p))`;

val id_inv_perreq_def' = store_thm(
   "id_inv_perreq_def'", ``id_inv_perreq (G : guest, g:num) =
   (!p. p < PAR.np_g g ==> id_inv_perreq_ (G.P p) (G.m) g p)``,
   REWRITE_TAC [id_inv_perreq_def, id_inv_perreq__def]);


(* all pending memory accesses are within the guest's memory area *)
val id_inv_cifadr_def = Define `id_inv_cifadr (G:guest, g:num) =
!c r. c < PAR.nc_g g ==>  r IN (G.cif c).req_sent ==>
       (PAdr r IN (PAR.A_G g))
    /\ (PAdr r IN RPAR.Amap GICD ==>
         ~(gicd_acc_not_supported (MsgOf r)) /\ gicd_req_ok r)
    /\ (PAdr r IN receiverMem g ==> ~Wreq r)`;

val id_inv_cifadr__def = Define `id_inv_cifadr_ (cif:bus_interface) g =
!r.  r IN cif.req_sent ==>
       (PAdr r IN (PAR.A_G g))
    /\ (PAdr r IN RPAR.Amap GICD ==>
         ~(gicd_acc_not_supported (MsgOf r)) /\ gicd_req_ok r)
    /\ (PAdr r IN receiverMem g ==> ~Wreq r)`;

val id_inv_cifadr_def' = store_thm(
   "id_inv_cifadr_def'", ``id_inv_cifadr (G, g) =
   !c. c < PAR.nc_g g ==> id_inv_cifadr_ (G.cif c) g``,
   EQ_TAC >>
   RW_TAC bool_ss [id_inv_cifadr_def, id_inv_cifadr__def] >>
   RES_TAC);


(* all pending DMA accesses are within the guest's memory area *)
val id_inv_pifadr_def = Define `id_inv_pifadr (G:guest, g:num) =
!p. p < PAR.np_g g ==>
  (!r. r IN (G.pif p).req_sent
  ==>   PAdr r IN (PAR.A_G g)
     /\ PAdr r NOTIN RPAR.Amap GICC
     /\ PAdr r NOTIN RPAR.Amap GICD
     /\ (PAdr r IN receiverMem g ==> ~Wreq r)
     /\ (!p'. p' < PAR.np_g g ==> PAdr r NOTIN (PAR.A_gp g p')))`;

val id_inv_pifadr__def = Define `id_inv_pifadr_ (pif:bus_interface) g p =
  (!r. r IN pif.req_sent
  ==>   PAdr r IN (PAR.A_G g)
     /\ PAdr r NOTIN RPAR.Amap GICC
     /\ PAdr r NOTIN RPAR.Amap GICD
     /\ (PAdr r IN receiverMem g ==> ~Wreq r)
     /\ (!p'. p' < PAR.np_g g ==> PAdr r NOTIN (PAR.A_gp g p')))`;

val id_inv_pifadr_def' = store_thm(
   "id_inv_pifadr_def'", ``id_inv_pifadr (G, g) =
   !p. p < PAR.np_g g ==> id_inv_pifadr_ (G.pif p) g p``,
   REWRITE_TAC [id_inv_pifadr_def, id_inv_pifadr__def]);


(* we do not allow peripherals to perform I/O requests,
   this restriction could be lifted but one needs to adapt transition rules *)
val id_inv_ioreq_def = Define `id_inv_ioreq (G:guest, g:num) =
!r q s. ((r, s) IN mem_req_sent (G.m) \/ (q, s) IN mem_rpl_rcvd (G.m)) ==>
   (!p. s <> PeripheralSender p)`;

val id_inv_ioreq__def = Define `id_inv_ioreq_ m =
!r q s. ((r, s) IN mem_req_sent m \/ (q, s) IN mem_rpl_rcvd m) ==>
   (!p. s <> PeripheralSender p)`;

val id_inv_ioreq_def' = store_thm(
   "id_inv_ioreq_def'", ``id_inv_ioreq (G, g) = id_inv_ioreq_ (G.m)``,
    REWRITE_TAC [id_inv_ioreq_def, id_inv_ioreq__def]);


(* all received replies in cif match a present request within the guest's memory area,
   all received replies in cif have no corresponding outstanding request in memory *)
val id_inv_cifrpl_def = Define `id_inv_cifrpl (G:guest, g:num) =
!c. c < PAR.nc_g g ==>
   (!q. q IN (G.cif c).rpl_rcvd ==>
        (?r. r IN (G.cif c).req_rcvd
          /\ match(r,q) 
          /\ (PAdr r IN (PAR.A_G g))
          /\ (PAdr r IN RPAR.Amap GICD ==>
              ~(gicd_acc_not_supported (MsgOf r)) /\ gicd_req_ok r)
          /\ (PAdr r IN receiverMem g ==> ~Wreq r))
     /\ ~(?r. (r, CoreSender c) IN (mem_req_rcvd G.m) /\ match(r,q)) )`;

val id_inv_cifrpl__def = Define `id_inv_cifrpl_ (cif:bus_interface) m g s =
   (!q. q IN cif.rpl_rcvd ==>
        (?r. r IN cif.req_rcvd
          /\ match(r,q) 
          /\ (PAdr r IN (PAR.A_G g))
          /\ (PAdr r IN RPAR.Amap GICD ==>
              ~(gicd_acc_not_supported (MsgOf r)) /\ gicd_req_ok r)
          /\ (PAdr r IN receiverMem g ==> ~Wreq r))
     /\ ~(?r. (r, s) IN (mem_req_rcvd m) /\ match(r,q)) )`;

val id_inv_cifrpl_def' = store_thm(
   "id_inv_cifrpl_def'", ``id_inv_cifrpl (G:guest, g:num) =
    (!c. c < PAR.nc_g g ==> id_inv_cifrpl_ (G.cif c) G.m g (CoreSender c))``,
    REWRITE_TAC [id_inv_cifrpl_def, id_inv_cifrpl__def]);


(* all received replies in pif match a present peripheral request,
all received replies in cif have no corresponding outstanding DMA request in memory *)
val id_inv_pifrpl_def = Define `id_inv_pifrpl (G:guest, g:num) =
!p. p < PAR.np_g g ==>
  (!q. q IN (G.pif p).rpl_rcvd ==>
       (?r. r IN (G.pif p).req_rcvd
         /\ match(r,q)
         /\ PAdr r IN (PAR.A_G g)
         /\ PAdr r NOTIN RPAR.Amap GICC
         /\ PAdr r NOTIN RPAR.Amap GICD
         /\ (PAdr r IN receiverMem g ==> ~Wreq r)
         /\ (!p'. p' < PAR.np_g g ==> PAdr r NOTIN (PAR.A_gp g p')))
   /\ ~(?r. (r, PeripheralSender p) IN (mem_req_rcvd G.m) /\ match(r,q)))`;

val id_inv_pifrpl__def = Define `id_inv_pifrpl_ (pif:bus_interface) m g s =
  (!q. q IN pif.rpl_rcvd ==>
       (?r. r IN pif.req_rcvd 
         /\ match(r,q)
         /\ PAdr r IN (PAR.A_G g)
         /\ PAdr r NOTIN RPAR.Amap GICC
         /\ PAdr r NOTIN RPAR.Amap GICD
         /\ (PAdr r IN receiverMem g ==> ~Wreq r)
         /\ (!p'. p' < PAR.np_g g ==> PAdr r NOTIN (PAR.A_gp g p')))
   /\ ~(?r. (r, s) IN (mem_req_rcvd m) /\ match(r,q)))`;

val id_inv_pifrpl_def' = store_thm(
   "id_inv_pifrpl_def'", ``id_inv_pifrpl (G:guest, g:num) =
    (!p. p < PAR.np_g g ==> id_inv_pifrpl_ (G.pif p) G.m g (PeripheralSender p))``,
    REWRITE_TAC [id_inv_pifrpl_def, id_inv_pifrpl__def]);


(* all received replies in memory match a present request,
   all received IO replies in memory have no corresponding outstanding requests in the GIC or peripherals *)
val id_inv_memrpl_def = Define `id_inv_memrpl (G: guest, g:num) =
!q s. (q,s) IN (mem_rpl_rcvd G.m) ==>
   (?r. (r,s) IN (mem_req_rcvd G.m) /\ match(r,q))
/\ ~(?r. (r,s) IN (idgic_req_rcvd G.GIC) /\ match(r,q))
/\ ~(?r p. p < PAR.np_g g /\ ((G.P p).IOreq_rcvd r = SOME s) /\ match(r,q))`;

val id_inv_memrpl__def = Define `id_inv_memrpl_ m gic P g =
!q s. (q,s) IN (mem_rpl_rcvd m) ==>
   (?r. (r,s) IN (mem_req_rcvd m) /\ match(r,q))
/\ ~(?r. (r,s) IN (idgic_req_rcvd gic) /\ match(r,q))
/\ ~(?r p. p < PAR.np_g g /\ ((P p).IOreq_rcvd r = SOME s) /\ match(r,q))`;

val id_inv_memrpl_def' = store_thm(
   "id_inv_memrpl_def'", ``id_inv_memrpl (G, g) = id_inv_memrpl_ G.m G.GIC G.P g``,
    REWRITE_TAC [id_inv_memrpl_def, id_inv_memrpl__def]); 


(* requests forwarded by memory (in mem_req_sent) have been received before
   and their addresses point to peripherals or GIC *)
val id_inv_mem_reqsent_def = Define `id_inv_mem_reqsent (G:guest, g:num) =
!r s. (r,s) IN (mem_req_sent G.m)
   ==>  ((r,s) IN (mem_req_rcvd G.m))
     /\ (PAdr r IN RPAR.Amap GICC \/ PAdr r IN RPAR.Amap GICD \/
         (?p. PAdr r IN PAR.A_gp g p /\ p < PAR.np_g g))`;

val id_inv_mem_reqsent__def = Define `id_inv_mem_reqsent_ m g =
!r s. (r,s) IN (mem_req_sent m)
   ==>  ((r,s) IN (mem_req_rcvd m))
     /\ (PAdr r IN RPAR.Amap GICC \/ PAdr r IN RPAR.Amap GICD \/
         (?p. PAdr r IN PAR.A_gp g p /\ p < PAR.np_g g))`;

val id_inv_mem_reqsent_def' = store_thm(
   "id_inv_mem_reqsent_def'", ``id_inv_mem_reqsent (G, g) = id_inv_mem_reqsent_ G.m g``,
    REWRITE_TAC [id_inv_mem_reqsent_def, id_inv_mem_reqsent__def]);


(* GIC.PI does not contain interrupts from other guests,
   foreign interrupts inactive
- all interupts (Q, PI, ...) part of (PIRQ g UNION IPIRQ g)
- all SGIs in Q c target core c and come from valid core
- all SGIs in P are between cores of the same guest
- for all channels s, PIR (id_igc s) NOT_ASSERTED in PI
- for all foreign channels s, PIR (id_igc s) (inactive ?) in Q
*)

val id_inv_gic_pi_def = Define `id_inv_gic_pi (G:guest, g:num) =
   idgic_gm_conf g (idgic_abs G.GIC).gicd`;

val id_inv_gic_q_def = Define `id_inv_gic_q (G:guest, g:num) =
    !q c. c < PAR.nc_g g /\ (idgic_abs G.GIC).Q c q <> INACTIVE ==>
       case q of
(* NOTE: IGC interrupt mapped to ideal PIR,
virtualized peripheral interrupts are never active and pending, only for SGIs *)
         | PIR n           => n >= 16 /\ n < 1020 /\ q IN (xPIRQ g)
                              /\ (q IN PIRQ g ==> (idgic_abs G.GIC).Q c q <> PENDACT)
         | SGI (id,c',c'') => (c = c'') /\ id <=+ 7w /\ c' < PAR.nc_g g`;

val id_inv_gic_q__def = Define `id_inv_gic_q_ GICQ g =
     (!id c' c'' c. (c < PAR.nc_g g /\ (GICQ c (SGI (id,c',c'')) <> INACTIVE) ==>
       (c = c'') /\ id <=+ 7w /\ c' < PAR.nc_g g))
  /\ (!n c. c < PAR.nc_g g /\ GICQ c (PIR n) <> INACTIVE ==>
        n >= 16 /\ n < 1020 /\ (PIR n) IN (xPIRQ g))
  /\ (!n c. c < PAR.nc_g g /\ (PIR n) IN PIRQ g ==> GICQ c (PIR n) <> PENDACT)`;


val id_inv_gic_q_def' = store_thm(
   "id_inv_gic_q_def'", ``id_inv_gic_q (G, g) = id_inv_gic_q_ (idgic_abs G.GIC).Q g``,
   EQ_TAC >>
   RW_TAC pure_ss [id_inv_gic_q_def, id_inv_gic_q__def] >>
   REPEAT CASE_TAC >>
   (* most cases *)
   RES_TAC >>
   FULL_SIMP_TAC (srw_ss()) [] >>
   (* Q PIR <> PENDACT *)
   ( CCONTR_TAC >>
    BasicProvers.byA (`(idgic_abs G.GIC).Q c (PIR n) <> INACTIVE`, ASM_SIMP_TAC (srw_ss()) []) >>
    RES_TAC >>
    FULL_SIMP_TAC (srw_ss()) [] >>
    REV_FULL_SIMP_TAC bool_ss []));


val _ = Datatype `IDG_INVS =  IDG_UNIQUE_RPL | IDG_CIFREQ | IDG_PIFREQ | IDG_GICREQ | IDG_PERREQ | IDG_CIFADR | IDG_PIFADR | IDG_IOREQ | IDG_CIFRPL | IDG_PIFRPL | IDG_MEMRPL | IDG_MEMSENT | IDG_GIC_PI | IDG_GIC_Q | IDG_GOOD_IDCORE | IDG_GOOD_MEM | IDG_GOOD_PER`;

val idg_inv_def = Define `idg_inv (G:guest, g:num, inv:IDG_INVS) =
  case inv of
    | IDG_UNIQUE_RPL => id_inv_unique_rpl (G,g)
    | IDG_CIFREQ => id_inv_cifreq (G,g)
    | IDG_PIFREQ => id_inv_pifreq (G,g)
    | IDG_GICREQ => id_inv_gicreq (G,g)
    | IDG_PERREQ => id_inv_perreq (G,g)
    | IDG_CIFADR => id_inv_cifadr (G,g)
    | IDG_PIFADR => id_inv_pifadr (G,g)
    | IDG_IOREQ  => id_inv_ioreq (G,g)
    | IDG_CIFRPL => id_inv_cifrpl (G,g)
    | IDG_PIFRPL => id_inv_pifrpl (G,g)
    | IDG_MEMRPL => id_inv_memrpl (G,g)
    | IDG_MEMSENT => id_inv_mem_reqsent (G,g)
    | IDG_GIC_PI =>  id_inv_gic_pi (G,g)
    | IDG_GIC_Q =>  id_inv_gic_q (G,g)
    | IDG_GOOD_IDCORE => !c. c < PAR.nc_g g ==> inv_good_idcore (G.C c)
    | IDG_GOOD_MEM => inv_good_mem G.m
    | IDG_GOOD_PER => !p. p < PAR.np_g g ==> inv_good_per_wrap (G.P p)`;


val InvG_def = Define `InvG (G : guest, g: num) = !inv. idg_inv(G,g,inv)`;


val InvG_corollaries = store_annotated_thm("InvG_corollaries",
``InvG(G, g) /\ (g < PAR.ng)``,
["memreq" -:
 (* all requests received in mem are currently pending in corresponding core *)
 ``!c. c < PAR.nc_g g ==> (!r. (r, CoreSender c) IN mem_req_rcvd (G.m) ==> r IN idcore_req_sent (G.C c))``,
 "giccorereq" -:
 (* all requests received in gic are currently pending in corresponding core *)
 ``!c. c < PAR.nc_g g ==> (!r. (r, CoreSender c) IN idgic_req_rcvd (G.GIC) ==> r IN idcore_req_sent (G.C c))``,
 "percorereq" -:
 (* all requests received in peripherals are currently pending in corresponding core *)
 ``!c p. c < PAR.nc_g g ==> p < PAR.np_g g ==> (!r. ((G.P p).IOreq_rcvd r = SOME (CoreSender c)) ==> r IN idcore_req_sent (G.C c))``,
 "dmamemreq" -:
 (* all DMA requests received in mem are currently pending in corresponding peripheral *)
 ``!p. p < PAR.np_g g ==> (!r. (r, PeripheralSender p) IN mem_req_rcvd (G.m) ==> r IN per_req_sent ((G:guest).P p).st)``,
 "onlycore2gic" -:
 (* requests received by GIC origin from a core *)
 ``!r s. ((r, s) IN idgic_req_rcvd (G.GIC) ==> (!p. s <> PeripheralSender p) /\ (?c. s = CoreSender c))``,
 "cifrpl2" -:
 (* no received reply in cif matches a request still marked as sent *)
 ``!c q. c < PAR.nc_g g ==> q IN (G.cif c).rpl_rcvd ==> ~ (?r. r IN (G.cif c).req_sent /\  match(r,q))``,
 "pifrpl2" -:
 (* no received reply in pif matches a request still marked as sent *)
 ``!p q. p < PAR.np_g g ==> q IN (G.pif p).rpl_rcvd ==> ~ (?r. r IN (G.pif p).req_sent /\  match(r,q))``,
 "memrcvd_from_bifs" -:
 (* requests received by memory are pending in cif or pif *)
 ``!r s. (r,s) IN mem_req_rcvd (G.m) /\ valid_sender g s
         <=> (?c. (r IN (G.cif c).req_sent) /\ (s = CoreSender c) /\ (c < PAR.nc_g g))
          \/ (?p. (r IN (G.pif p).req_sent) /\ (s = PeripheralSender p) /\ (p < PAR.np_g g))``,
 "mem_receivers" -:
 (* requests forwarded by memory were received by GIC or peripheral *)
 ``!r s. (r,s) IN mem_req_sent (G.m)  ==> (r,s) IN (idgic_req_rcvd G.GIC) \/ (?p. ((G.P p).IOreq_rcvd r = SOME s) /\ p < PAR.np_g g)``,
 "mem_nand" -:
 (* received reply and pending request exclude each other *)
 ``!r q s. match(r,q) ==> ~((q,s) IN (mem_rpl_rcvd G.m) /\ (r,s) IN (mem_req_sent ((G:guest).m)))``,
 "mem_rpl_cif_req" -:
 (* replies received by memory match a request received and forwarded in cif *)
 ``!q c. (q, CoreSender c) IN (mem_rpl_rcvd G.m) ==> c < PAR.nc_g g ==>
   (?r. r IN (G.cif c).req_sent /\ r IN (G.cif c).req_rcvd /\ match(r,q))``,
 (* GICD-requests in idgic_req_rcvd are gicd_req_ok *)
 "gicd_req_ok" -:
 ``!r c. (r, CoreSender c) IN idgic_req_rcvd (G.GIC) ==> c < PAR.nc_g g ==> PAdr r IN RPAR.Amap GICD ==> ~(gicd_acc_not_supported (MsgOf r)) /\ gicd_req_ok r ``
],
       RW_TAC (srw_ss()) [InvG_def, fall_constructors_thm_of ``:IDG_INVS``]
  THEN UNDISCH_ALL_TAC
  THEN computeLib.RESTR_EVAL_TAC [``match``, ``PAdr``, ``Rpl_PAdr``, ``iMode``]
  THEN RW_TAC (srw_ss()) [valid_sender_def]
  THEN TRY EQ_TAC
  THEN RW_TAC (srw_ss()) []
  THEN TRY (Cases_on `s`)
  THEN TRY (LIMITED_METIS_TAC 1 []));


(******************   COMPOSED IDEAL  MODEL   **************)

val _ = Hol_datatype `ideal_model =
  <| G: num -> guest
   |>`;

val ideal_model_just_guests_lem = store_thm("ideal_model_just_guests_lem",
                                            ``X = <|G := X.G|>``,
             `X.G = (<|G := X.G|>).G` by SRW_TAC [simpLib.type_ssfrag ``:ideal_model``] []
        THEN METIS_TAC ((TypeBase.accessors_of ``:ideal_model``)@[TypeBase.nchotomy_of ``:ideal_model``]));

val ideal_model_split_lem =
    store_thm("ideal_model_split_lem",
    ``<|G := X|> = ideal_model X``,
    ` <|G := X|>.G = (ideal_model X).G` by (RW_TAC (srw_ss()) [])
      THEN METIS_TAC ((#rewrs (TypeBase.simpls_of ``:ideal_model``))@(TypeBase.updates_of ``:ideal_model``)));


val ideal_model_equal_guests_lem =
    store_thm("ideal_model_equal_guests_lem",
    ``(M1 = M2) = (!g. (M1.G) g = (M2.G) g)``,
    Cases_on `M1`
      THEN Cases_on `M2`
      THEN FULL_SIMP_TAC (srw_ss()) [boolTheory.FUN_EQ_THM]);



val sync_channel_mem_def = Define `sync_channel_mem (IM, s) =
    let (g_src, g_trgt) = PAR.cpol s               in
    let (add_src, add_trgt) = PAR.igca s           in
    let trgt_mem = (IM.G g_trgt).m                 in
    let content = mem_abs ((IM.G g_src).m) add_src in
       IM with
         <| G := (g_trgt =+
                   (IM.G g_trgt with
                    <| m := memory_upd (add_trgt, content) trgt_mem |> )) IM.G |>`;


val sync_all_channels_def = Define `sync_all_channels IM =
    FOLDR (\s M. sync_channel_mem(M,s)) IM (GENLIST I PAR.ns)`;


val sync_guest_channels_def = Define `sync_guest_channels (IM,g) =
    FOLDR (\s M. sync_channel_mem(M,s)) IM (FILTER (\s. FST (PAR.cpol s) = g) (GENLIST I PAR.ns))`;



val untargeted_sync_guests_lem =
      store_thm("untargeted_sync_guests_lem",
          ``EVERY (\s. SND(PAR.cpol s) <> g_trgt) slist ==>
            ((FOLDR (\s M. sync_channel_mem (M,s)) M0 slist).G g_trgt = M0.G g_trgt)``,
              Induct_on `slist:num list`
                THEN RW_TAC (srw_ss()) []
                THEN UNDISCH_ALL_TAC
                THEN SPEC_TAC (``(FOLDR (\s M. sync_channel_mem (M,s)) M0 slist)``, ``M:ideal_model``)
                THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                THEN PairedLambda.GEN_BETA_TAC
                THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
                THEN METIS_TAC [memory_upd_axiom]);


fun GENLIST_BOUNDARIES_TAC1 (asm,gol) =
    case find_term_opt (is_match ``(FILTER filter (GENLIST I lim))``) gol
     of SOME t => ASSUME_TAC (INST (#1 (match_term ``(FILTER filter (GENLIST I lim))`` t))
                      genlist_boundaries_lem1) (asm,gol)
     | NONE => ALL_TAC (asm,gol);

fun GENLIST_BOUNDARIES_TAC2 (asm,gol) =
    case find_term_opt (is_match ``(FILTER filter (GENLIST (\t. s + (t + 1)) (lim - (s + 1))))``) gol
     of SOME t => ASSUME_TAC (INST (#1 (match_term ``(FILTER filter (GENLIST (\t. s + (t + 1)) (lim - (s + 1))))`` t))
                      genlist_boundaries_lem2) (asm,gol)
     | NONE => ALL_TAC (asm,gol);

val GENLIST_BOUNDARIES_TAC = GENLIST_BOUNDARIES_TAC1 THEN GENLIST_BOUNDARIES_TAC2;

fun EVERY_FILTER_TAC (asm,gol) =
    case find_term_opt (is_match ``(FILTER P lst)``) gol
     of SOME t => ASSUME_TAC (INST (#1 (match_term ``(FILTER P lst)`` t))
                      every_filter_lem) (asm,gol)
     | NONE => ALL_TAC (asm,gol);


val no_common_targets_lem =
      store_thm("no_common_targets_lem",
       ``(s < PAR.ns) ==> (PAR.cpol s = (g_src,g_trgt)) ==>
         (EVERY (\s. SND(PAR.cpol s) <> g_trgt) (FILTER (\s. FST (PAR.cpol s) = g_src) (GENLIST I s))
       /\ EVERY (\s. SND(PAR.cpol s) <> g_trgt) (FILTER (\s. FST (PAR.cpol s) = g_src) (GENLIST (\t. s + (t + 1)) (PAR.ns − (s + 1)))))``,
       REPEAT STRIP_TAC
         THEN GENLIST_BOUNDARIES_TAC
         THEN FULL_SIMP_TAC arith_ss [rich_listTheory.EVERY_GENLIST, listTheory.EVERY_FILTER]
         THEN GEN_TAC
         THEN REPEAT STRIP_TAC
         THEN (TRY (`i<>s` by (FULL_SIMP_TAC arith_ss [] THEN NO_TAC)))
         THEN (TRY (`s + (t + 1) <> s` by (FULL_SIMP_TAC arith_ss [] THEN NO_TAC)))
         THEN (TRY (`i < PAR.ns` by (FULL_SIMP_TAC arith_ss [] THEN NO_TAC)))
         THEN (TRY (`s + (t+1) < PAR.ns` by (FULL_SIMP_TAC arith_ss [] THEN NO_TAC)))
         THEN IMP_RES_TAC goodP_axiom
         THEN RW_TAC (srw_ss()) []
         THEN FULL_SIMP_TAC (srw_ss()) []);


val no_matching_channel_in_list_lem =
store_thm("no_matching_channel_in_list_lem",
       ``(!s. ~(s < lim) \/ (SND(PAR.cpol s) <> g_trgt))
          ==>
          EVERY (\s. SND(PAR.cpol s) <> g_trgt) (FILTER filter (GENLIST I lim))``,
         FULL_SIMP_TAC arith_ss [rich_listTheory.EVERY_GENLIST, listTheory.EVERY_FILTER]
           THEN METIS_TAC []);

val no_matching_channel_in_list_lem2 =
store_thm("no_matching_channel_in_list_lem2",
       ``(!s. ~(s < lim) \/ (PAR.cpol s <> (g_src,g_trgt)))
          ==>
          EVERY (\s. SND(PAR.cpol s) <> g_trgt) (FILTER  (\s. FST (PAR.cpol s) = g_src) (GENLIST I lim))``,
         FULL_SIMP_TAC arith_ss [rich_listTheory.EVERY_GENLIST, listTheory.EVERY_FILTER]
           THEN REPEAT STRIP_TAC
           THEN RW_TAC (srw_ss()) []
           THEN FULL_SIMP_TAC (srw_ss()) []
           THEN METIS_TAC []);


val sender_untouched_lem =
      store_thm("sender_untouched_lem",
``EVERY (\s. s < PAR.ns) (FILTER (\s. FST (PAR.cpol s) = g) slist)
==>
((FOLDR (\s M. sync_channel_mem (M,s)) IM (FILTER (\s. FST (PAR.cpol s) = g) slist)).G g = IM.G g)``,
         Induct_on `slist`
           THEN RW_TAC (srw_ss()) []
           THEN UNDISCH_ALL_TAC
           THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
           THEN UNDISCH_ALL_TAC
           THEN PairedLambda.GEN_BETA_TAC
           THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
           THEN IMP_RES_TAC goodP_axiom
           THEN FST_AND_SND_TAC
           THEN FULL_SIMP_TAC (srw_ss()) []);


val sync_shared_mem_def = Define `sync_shared_mem (IM:ideal_model, IM':ideal_model) =
   (* all shared memory has been copied *)
   (!s g1 g2 a1 a2.
       (s < PAR.ns)  ==> (PAR.cpol s = (g1, g2)) ==> (PAR.igca s = (a1,a2))
     ==>  (mem_abs ((IM'.G g2).m) a2 = mem_abs ((IM.G g1).m) a1))
   /\
   (* but no other memory has changed *)
   (!a g. (~(?s. (SND(PAR.igca s) = a) /\ (SND(PAR.cpol s) = g)))
     ==> (mem_abs ((IM'.G g).m) a = mem_abs ((IM.G g).m) a))
   /\
   (* nor has anything else *)
   (!g. ?x. IM'.G g = (IM.G g with m := x))
   /\
   (?X. IM' = IM with <| G := X |>)`;


val sync_shared_mem_of_guest_def = Define `sync_shared_mem_of_guest (IM:ideal_model, g1:num, IM':ideal_model) =
   (* all shared memory has been copied *)
   (!s g2 a1 a2.
       (s < PAR.ns)  ==> (PAR.cpol s = (g1, g2)) ==> (PAR.igca s = (a1,a2))
     ==>  (mem_abs ((IM'.G g2).m) a2 = mem_abs ((IM.G g1).m) a1))
   /\
   (* but no other memory has changed *)
   (!a g. (~(?s. (s < PAR.ns) /\ (SND(PAR.igca s) = a) /\ (SND(PAR.cpol s) = g) /\ (FST(PAR.cpol s) = g1)))
     ==> (mem_abs ((IM'.G g).m) a = mem_abs ((IM.G g).m) a))
   /\
   (* nor has anything else *)
   (!g. ?x. IM'.G g = (IM.G g with m := x))
   /\
   (?X. IM' = IM with <| G := X |>)`;


val do_sync_shared_mem_upd_of_guest_def = Define `do_sync_shared_mem_upd_of_guest (IM:ideal_model, g1:num, IM':ideal_model) =
   (* all shared memory has been copied *)
   (!s g2 a1 a2.
       (s < PAR.ns)  ==> (PAR.cpol s = (g1, g2)) ==> (PAR.igca s = (a1,a2))
     ==>  (mem_abs ((IM'.G g2).m) a2 = mem_abs ((IM.G g1).m) a1)
          /\ (((IM'.G g2).m) = memory_upd (a2, mem_abs ((IM.G g1).m) a1) ((IM.G g2).m)))
   /\
   (* but memory of non-receiving guests is unchanged *)
   (!g2. (~(?s. (s < PAR.ns) /\ (PAR.cpol s = (g1,g2))))
     ==> ((IM'.G g2).m = (IM.G g2).m))
   /\
   (* non-IGC-memory has not changed *)
   (!g2 a. (~(?s. (s < PAR.ns) /\ (PAR.cpol s = (g1,g2)) /\ (SND(PAR.igca s) = a)))
     ==> (mem_abs ((IM'.G g2).m) a = mem_abs ((IM.G g2).m) a))
   /\
   (* nor has any non-memory-component *)
   (!g. ?x. IM'.G g = (IM.G g with m := x))
   /\
   (?X. IM' = IM with <| G := X |>)`;



(* a theorem that shows that the axiomatic and the
   behavioral definitions from above are equal *)
val do_sync_shared_mem_upd_of_guest_alternative_def_lem =
    store_thm("do_sync_shared_mem_upd_of_guest_alternative_def_lem",
  ``do_sync_shared_mem_upd_of_guest (IM, g, IM') = (IM' = sync_guest_channels (IM,g))``,
  EQ_TAC
    THENL [(* 1. effects => explicit updates *)
           RW_TAC (srw_ss()) [sync_guest_channels_def, do_sync_shared_mem_upd_of_guest_def]
             THEN RW_TAC (srw_ss()) [ideal_model_equal_guests_lem]
             THEN SPEC_ASSUM_TAC (``!g. A ==> B``, [``g':num``])
             THEN SPEC_ASSUM_TAC (``!g a. A ==> B``, [``g':num``])
             THEN SPEC_ASSUM_TAC (``!g. ?x. A``, [``g':num``])
             THEN UNDISCH_ALL_TAC
             THEN RW_TAC (srw_ss()) []
             THEN Cases_on `(!s. ~(s < PAR.ns) \/ PAR.cpol s <> (g,g'))`
             THEN FULL_SIMP_TAC (srw_ss()) []
             THEN UNDISCH_ALL_TAC
             THEN RW_TAC (srw_ss()) []
             THENL [(* 1.1. no matching channel *)
                    FULL_SIMP_TAC (srw_ss()) [no_matching_channel_in_list_lem2, untargeted_sync_guests_lem]
                      THEN Cases_on `IM.G g'`
                      THEN RW_TAC (srw_ss()) (TypeBase.updates_of ``:guest``),
                    (* 1.2. matching channel *)
                    SPEC_ASSUM_TAC (``!s g2 a1 a2. X``,
                                   [``s:num``, ``g':num``, ``FST(PAR.igca s)``, ``SND(PAR.igca s)``])
                      THEN IMP_RES_TAC genlist_triple_lem
                      THEN FULL_SIMP_TAC (srw_ss()) [listTheory.FILTER_APPEND_DISTRIB, rich_listTheory.FOLDR_APPEND]
                      THEN IMP_RES_TAC no_common_targets_lem
                      THEN FULL_SIMP_TAC (srw_ss()) [untargeted_sync_guests_lem]
                      THEN IMP_RES_TAC untargeted_sync_guests_lem
                      THEN GENLIST_BOUNDARIES_TAC
                      THEN ASSUME_TAC (GEN_ALL sender_untouched_lem)
                      THEN UNDISCH_ALL_TAC
                      THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                      THEN PairedLambda.GEN_BETA_TAC
                      THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
                      THEN METIS_TAC [memory_upd_axiom]],
           (* 2. explicit updates => effects *)
           RW_TAC (srw_ss()) [sync_guest_channels_def, do_sync_shared_mem_upd_of_guest_def]
             THENL[(* 2.1. mem effects on updated mem
                      Note that there is max 1 update for every neighbour guest of g.*)
                   IMP_RES_TAC genlist_triple_lem
                     THEN FULL_SIMP_TAC (srw_ss()) [listTheory.FILTER_APPEND_DISTRIB, rich_listTheory.FOLDR_APPEND]
                     THEN IMP_RES_TAC no_common_targets_lem
                     THEN FULL_SIMP_TAC (srw_ss()) [untargeted_sync_guests_lem]
                     THEN IMP_RES_TAC untargeted_sync_guests_lem
                     THEN GENLIST_BOUNDARIES_TAC
                     THEN ASSUME_TAC (GEN_ALL sender_untouched_lem)
                     THEN UNDISCH_ALL_TAC
                     THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                     THEN PairedLambda.GEN_BETA_TAC
                     THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
                      THEN METIS_TAC [memory_upd_axiom],
                    (* 2.2. upd on updated mem
                       Note that there is max 1 update for every neighbour guest of g.*)
                   IMP_RES_TAC genlist_triple_lem
                     THEN FULL_SIMP_TAC (srw_ss()) [listTheory.FILTER_APPEND_DISTRIB, rich_listTheory.FOLDR_APPEND]
                     THEN IMP_RES_TAC no_common_targets_lem
                     THEN FULL_SIMP_TAC (srw_ss()) [untargeted_sync_guests_lem]
                     THEN IMP_RES_TAC untargeted_sync_guests_lem
                     THEN GENLIST_BOUNDARIES_TAC
                     THEN ASSUME_TAC (GEN_ALL sender_untouched_lem)
                     THEN UNDISCH_ALL_TAC
                     THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                     THEN PairedLambda.GEN_BETA_TAC
                     THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID],
                    (* 2.3. memory of non-receiving guests *)
                    GENLIST_BOUNDARIES_TAC
                      THEN EVERY_FILTER_TAC
                      THEN UNDISCH_ALL_TAC
                      THEN SPEC_TAC (``FILTER (\s. FST (PAR.cpol s) = g) (GENLIST I PAR.ns)``, ``slist:num list``)
                      THEN Induct_on `slist:num list`
                      THEN RW_TAC (srw_ss()) []
                      (* induction step: one update *)
                      THEN UNDISCH_ALL_TAC
                      THEN SPEC_TAC (``(FOLDR (\s M. sync_channel_mem (M,s)) IM slist)``, ``M:ideal_model``)
                      THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                      THEN PairedLambda.GEN_BETA_TAC
                      THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
                      THEN SPEC_ASSUM_TAC (``!s. X``, [``h:num``])
                      THEN UNDISCH_ALL_TAC
                      THEN RW_TAC (srw_ss()) []
                      THEN METIS_TAC [memory_upd_axiom],
                    (* 2.4. not-updated mem *)
                    GENLIST_BOUNDARIES_TAC
                      THEN EVERY_FILTER_TAC
                      THEN UNDISCH_ALL_TAC
                      THEN SPEC_TAC (``FILTER (\s. FST (PAR.cpol s) = g) (GENLIST I PAR.ns)``, ``slist:num list``)
                      THEN Induct_on `slist:num list`
                      THEN RW_TAC (srw_ss()) []
                      (* induction step: one update *)
                      THEN UNDISCH_ALL_TAC
                      THEN SPEC_TAC (``(FOLDR (\s M. sync_channel_mem (M,s)) IM slist)``, ``M:ideal_model``)
                      THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                      THEN PairedLambda.GEN_BETA_TAC
                      THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
                      THEN FULL_SIMP_TAC (srw_ss()) []
                      THEN SPEC_ASSUM_TAC (``!s. X``, [``h:num``])
                      THEN UNDISCH_ALL_TAC
                      THEN RW_TAC (srw_ss()) []
                      THEN METIS_TAC [memory_upd_axiom],
                    (* 2.5. only mem affected *)
                    EXISTS_TAC ``((FOLDR (\s M. sync_channel_mem (M,s)) IM (FILTER (\s. FST (PAR.cpol s) = g) (GENLIST I PAR.ns))).G g').m``
                      THEN SPEC_TAC (``FILTER (\s. FST (PAR.cpol s) = g) (GENLIST I PAR.ns)``, ``slist:num list``)
                      THEN Induct_on `slist:num list`
                      THEN RW_TAC (srw_ss()) []
                      THENL [(* 2.5.1. base case: empty channel list *)
                             Cases_on `IM.G g'`
                               THEN RW_TAC (srw_ss()) (TypeBase.updates_of ``:guest``),
                             (* 2.5.2. induction step: one update *)
                             UNDISCH_ALL_TAC
                               THEN SPEC_TAC (``(FOLDR (\s M. sync_channel_mem (M,s)) IM slist)``, ``M:ideal_model``)
                               THEN RW_TAC (srw_ss()) [sync_channel_mem_def, LET_DEF]
                               THEN PairedLambda.GEN_BETA_TAC
                               THEN RW_TAC ((srw_ss())++combinSimps.COMBIN_ss) [combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
                               THEN `!A B x u. (A:guest = B with m := x) ==> ((A with m := u) = (B with m:=u))` by SRW_TAC [] []
                               THEN METIS_TAC []],
                    (* 2.6. only guests affected *)
                    METIS_TAC [ideal_model_just_guests_lem]]]);


val syncInv_def = Define `syncInv (M : ideal_model) =
    !s g1 g2 a1 a2. s < PAR.ns ==> g1 < PAR.ng ==> g2 < PAR.ng ==> (PAR.cpol s = (g1, g2)) ==> (PAR.igca s = (a1,a2))
         ==>  (mem_abs ((M.G g2).m) a2 = mem_abs ((M.G g1).m) a1)`;

val sync_shared_mem_upd_of_guest_def = Define `sync_shared_mem_upd_of_guest (IM,g,IM') =
    if syncInv IM
    then (IM' = IM)
    else do_sync_shared_mem_upd_of_guest (IM,g,IM')`;


val comp_rule_internal_def = Define `comp_rule_internal (IM:ideal_model, IM'':ideal_model) =
?g x G' IM'.
      g < PAR.ng
   /\ ideal_guest_trans (IM.G g, g, INTERNAL x, G')
   /\ (IM' = IM with <| G := (g =+ G') IM.G |>)
   /\ sync_shared_mem_upd_of_guest(IM',g,IM'')`;



val comp_rule_igc_def = Define `comp_rule_igc (IM:ideal_model, IM':ideal_model) =
?g1 g2 s c G1' G2'.
     g1 < PAR.ng
  /\ g2 < PAR.ng
  /\  s < PAR.ns
  /\ (PAR.cpol s = (g1,g2))
  /\ (c < PAR.nc_g g2)
  /\ ideal_guest_trans (IM.G g1, g1, EXTERNAL_SND (IGC_ s c), G1')
  /\ ideal_guest_trans (IM.G g2, g2, EXTERNAL_RCV (IGC_ s c), G2')
  /\ (IM' = IM with <| G := (g1 =+ G1') ((g2 =+ G2') IM.G) |>) `;


val comp_rule_rcu_def = Define `comp_rule_rcu (IM:ideal_model, IM':ideal_model) =
?g1 g2 s co G1' G2'.
     g1 < PAR.ng
  /\ g2 < PAR.ng
  /\  s < PAR.ns
  /\ (PAR.cpol s = (g2,g1))
  /\ (case co of | NONE => T | SOME c => c < PAR.nc_g g1)
  /\ ideal_guest_trans (IM.G g1, g1, EXTERNAL_SND (RCU_ s co), G1')
  /\ ideal_guest_trans (IM.G g2, g2, EXTERNAL_RCV (RCU_ s co), G2')
  /\ (IM' = IM with <| G := (g1 =+ G1') ((g2 =+ G2') IM.G) |>) `;

val comp_rule_input_def = Define `comp_rule_input (IM:ideal_model, IM':ideal_model) =
?l. !g. g < PAR.ng ==> 
    ?G'. ideal_guest_trans (IM.G g, g, EXTERNAL_RCV (INPUT l), G')
      /\ (IM'.G g = G') `;


val _ = Datatype `Composed_Rule = C_INTERNAL | C_IGC | C_RCU | C_EXTI`;

(* TODO: pass sIGC information to constrain GIC_DIST action *)
val ideal_model_trans_def = Define `ideal_model_trans (IM:ideal_model, R:Composed_Rule, IM':ideal_model) =
    case R of
        C_INTERNAL => comp_rule_internal(IM, IM')
      | C_IGC      => comp_rule_igc     (IM, IM')
      | C_RCU      => comp_rule_rcu     (IM, IM')
      | C_EXTI     => comp_rule_input   (IM, IM')`;



(* outstanding reply for core c *)

val id_pend_rpl_def = Define `id_pend_rpl (CIFrpl, MEMrpl, g:num, c:num, q:reply) =
(q, CoreSender c) IN MEMrpl \/ q IN CIFrpl
`;



(******************** INITIAL CONFIGURATION ***********************)

val id_core_start_def = Define `id_core_start (G:guest, g:num, c:num) =
   (idcore_abs(G.C c) = idCGreset(g,c) with
     <| H := <| launch := (c = 0)|> |>)
/\ (idcore_req_sent(G.C c) = EMPTY)
/\ ((G.cif c).req_rcvd = EMPTY)
/\ ((G.cif c).req_sent = EMPTY)
/\ ((G.cif c).rpl_rcvd = EMPTY)
/\ (!q. (idgic_abs G.GIC).Q c q = INACTIVE)
/\ (!r. (idgic_abs G.GIC).gicc c r = GICCinit r)
/\ ~ (G.PSCI.pow c)
/\ (G.PSCI.events c = NIL)
/\ (cis_abs (idcore_int (G.C c)) = FLUSHED)
`;

val id_per_start_def = Define `id_per_start (G:guest, p:num) =
   ((G.P p).st = per_reset)
/\ ~per_active (G.P p).st
/\ (!r. ~IS_SOME ((G.P p).IOreq_rcvd r))
/\ ((G.pif p).req_rcvd = EMPTY)
/\ ((G.pif p).req_sent = EMPTY)
/\ ((G.pif p).rpl_rcvd = EMPTY)
`;

(* TODO: add G.init = 1 *)
val id_start_def = Define `id_start (M : ideal_model) =
!g. g < PAR.ng ==>
   (!c. c < PAR.nc_g g ==> id_core_start(M.G g, g, c))
/\ (!p. p < PAR.np_g g ==> id_per_start(M.G g, p))
/\ (mem_req_rcvd((M.G g).m) = EMPTY)
/\ (mem_req_sent((M.G g).m) = EMPTY)
/\ (mem_rpl_rcvd((M.G g).m) = EMPTY)
/\ ((M.G g).E_in = NIL) /\ ((M.G g).E_out = NIL)
/\ (idgic_req_rcvd ((M.G g).GIC) = EMPTY)
/\ (!q. PI (M.G g).GIC q = NOT_ASSERTED)
/\ ((idgic_abs ((M.G g).GIC)).gicd = (\r. GICDinit r))
/\ ((M.G g).sIGC.flags = EMPTY)
/\ (!s. s < PAR.ns ==> ((M.G g).sIGC.addressbook s = NONE))
/\ (!s g'. s < PAR.ns /\ (PAR.cpol s = (g,g')) ==>
    ((mem_abs (M.G g).m) (FST(PAR.igca s)) =
     (mem_abs (M.G g').m) (SND(PAR.igca s))) )
`;


(******************** COMPUTATIONS ***********************)

val ideal_model_comp_def = Define `
   (ideal_model_comp (IM, 0    , IM') = (IM = IM'))
/\ (ideal_model_comp (IM, SUC n, IM') =
    ?R IM''. ideal_model_comp(IM,n,IM'') /\ ideal_model_trans(IM'',R,IM'))
`;


val ideal_comp_concat_lem = store_thm("ideal_comp_concat_lem", ``
!IM n IM' n' IM''. ideal_model_comp (IM,n,IM') /\ ideal_model_comp (IM',n',IM'')
==>
?n''. ideal_model_comp (IM,n'',IM'')
``,
  Induct_on `n'`
  THEN1 ( RW_TAC (srw_ss()) [ideal_model_comp_def]
          THEN HINT_EXISTS_TAC
          THEN FULL_SIMP_TAC (srw_ss()) []
  )
  THEN RW_TAC (srw_ss()) [ideal_model_comp_def]
  THEN RES_TAC
  THEN IMP_RES_TAC ideal_model_comp_def
  THEN EXISTS_TAC ``SUC n'''``
  THEN FULL_SIMP_TAC (srw_ss()) []
);


val ideal_comp_concat_lem2 = store_thm("ideal_comp_concat_lem2",
     ``!IM n n' IM''.
       (?IM'. ideal_model_comp (IM,n,IM') /\ ideal_model_comp (IM',n',IM''))
         =
       ideal_model_comp (IM,n+n',IM'')``,
     Induct_on `n'`
      THEN RW_TAC (srw_ss()) [ideal_model_comp_def]
      THEN `n + SUC n' = SUC (n + n')` by RW_TAC (arith_ss) []
      THEN FULL_SIMP_TAC (srw_ss()) [ideal_model_comp_def]
      THEN METIS_TAC []);


val ideal_model_comp_rev_lem = store_thm("ideal_model_comp_rev_lem",
     ``!n i IM IM'.
        ideal_model_comp (IM,SUC n,IM') =
        (?R IM_. ideal_model_trans (IM, R, IM_) /\ ideal_model_comp (IM_,n,IM'))``,
     RW_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``IM:ideal_model``, ``1``, ``n:num``, ``IM':ideal_model``] ideal_comp_concat_lem2)
      THEN `SUC n = 1 + n` by FULL_SIMP_TAC (arith_ss) []
      THEN `1 = SUC 0` by FULL_SIMP_TAC (arith_ss) []
      THEN METIS_TAC [ideal_model_comp_def]);



val good_ideal_comp_def = Define `good_ideal_comp (IM, n, IM') =
     id_start IM /\ ideal_model_comp (IM, n, IM')`;



val syncInv_no_igc_lem = store_thm("syncInv_no_igc_lem", ``
!IM IM'. syncInv IM 
      /\ (!g a. g < PAR.ng ==> a IN A_IGCin g ==> 
			   (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
      /\ (!g a. g < PAR.ng ==> a IN A_IGCout g ==> 
			   (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
==>
syncInv IM'
``,
  RW_TAC (srw_ss()) [syncInv_def, A_IGCout_def, A_IGCin_def] >>
  `(a1 = FST (PAR.igca s)) /\ (a2 = SND (PAR.igca s)) /\ 
   (g1 = FST (PAR.cpol s)) /\ (g2 = SND (PAR.cpol s))` by (
      RW_TAC (srw_ss()) [] 
  ) >>
  `(mem_abs (IM.G g1).m a1 = mem_abs (IM'.G g1).m a1)` by (
      METIS_TAC []
  ) >>
  `(mem_abs (IM.G g2).m a2 = mem_abs (IM'.G g2).m a2)` by (
      METIS_TAC []
  ) >>
  `(mem_abs (IM.G g2).m a2 = mem_abs (IM.G g1).m a1)` by (
      METIS_TAC []
  ) >>
  METIS_TAC []
);

val shared_mem_upd_lem = store_thm("shared_mem_upd_lem",
       ``!IM g IM'. g < PAR.ng
                 /\ syncInv IM
                 /\ sync_shared_mem_upd_of_guest (IM, g:num, IM')
                ==> (IM = IM')``,
       RW_TAC (srw_ss()) [sync_shared_mem_upd_of_guest_def]);

val cif_igc_mem_unchanged_lem = store_thm("cif_igc_mem_unchanged_lem", ``
!IM IM' im' cif' g1 c1 q id r.
   g1 < PAR.ng
/\ c1 < PAR.nc_g g1
/\ mem_step_snd_rpl((IM.G g1).m,q,id,im')
/\ (IM' = IM with G := (g1 =+ ((IM.G g1) with 
       <|cif := (c1 =+ cif') (IM.G g1).cif; m := im'|>)) IM.G) 
/\ (q,id) NOTIN mem_rpl_rcvd ((IM.G g1).m)
/\ req_aligned r
/\ match(r,q)
/\ PAdr r IN A_IGCout g1
==>
   (!g a. g < PAR.ng ==> a IN A_IGCin g ==> 
		     (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
/\ (!g a. g <> g1 ==> a IN A_IGCout g ==> 
		     (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
/\ (!a. a <> PAdr r ==> (mem_abs (IM.G g1).m a = mem_abs (IM'.G g1).m a))
``,
  REPEAT STRIP_TAC 
  >| [(* case: input channels unchanged *)
      Cases_on `g = g1`
      >| [RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  `a <> PAdr r` by (
	      METIS_TAC [IGC_in_out_disj, DISJOINT_MEMBER_NOT_EQUAL]
	  ) >>
	  METIS_TAC [mem_aligned_unchanged_lem]
	  ,
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ]
      ,
      (* case: other guests outputs unaffected *)
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ,
      (* case: other addresses in g1 unchanged *)
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC [mem_aligned_unchanged_lem]
     ]
);

val pif_igc_mem_unchanged_lem = store_thm("pif_igc_mem_unchanged_lem", ``
!IM IM' im' pif' g1 p1 q id r.
   g1 < PAR.ng
/\ p1 < PAR.np_g g1
/\ mem_step_snd_rpl((IM.G g1).m,q,id,im')
/\ (IM' = IM with G := (g1 =+ ((IM.G g1) with 
       <|m := im'; pif := (p1 =+ pif') (IM.G g1).pif|>)) IM.G) 
/\ (q,id) NOTIN mem_rpl_rcvd ((IM.G g1).m)
/\ req_aligned r
/\ match(r,q)
/\ PAdr r IN A_IGCout g1
==>
   (!g a. g < PAR.ng ==> a IN A_IGCin g ==> 
		     (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
/\ (!g a. g <> g1 ==> a IN A_IGCout g ==> 
		     (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
/\ (!a. a <> PAdr r ==> (mem_abs (IM.G g1).m a = mem_abs (IM'.G g1).m a))
``,
  REPEAT STRIP_TAC 
  >| [(* case: input channels unchanged *)
      Cases_on `g = g1`
      >| [RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  `a <> PAdr r` by (
	      METIS_TAC [IGC_in_out_disj, DISJOINT_MEMBER_NOT_EQUAL]
	  ) >>
	  METIS_TAC [mem_aligned_unchanged_lem]
	  ,
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	 ]
      ,
      (* case: other guests outputs unaffected *)
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ,
      (* case: other addresses in g1 unchanged *)
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
      METIS_TAC [mem_aligned_unchanged_lem]
     ]
);


val single_igc_mem_upd_lem = store_thm("single_igc_mem_upd_lem", ``
!IM IM' g1 a1 s g2 a2.
   g1 < PAR.ng
/\ g2 < PAR.ng
/\ s < PAR.ns
/\ (PAR.cpol s = (g1,g2))
/\ (PAR.igca s = (a1,a2))
/\ syncInv IM
/\ (!g a. g < PAR.ng ==> a IN A_IGCin g ==> 
		     (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
/\ (!g a. g <> g1 ==> a IN A_IGCout g ==> 
		     (mem_abs (IM.G g).m a = mem_abs (IM'.G g).m a))
/\ (!a. a <> a1 ==> (mem_abs (IM.G g1).m a = mem_abs (IM'.G g1).m a))
==>
do_sync_shared_mem_upd_of_guest(IM',g1,
    IM' with <|G := (g2 =+ 
        (IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G g1).m a1) 
					 (IM'.G g2).m|>) ) IM'.G|>)
``,
  RW_TAC (srw_ss()) [do_sync_shared_mem_upd_of_guest_def]
  >| [(* case: mem_abs *)
      Cases_on `s' = s` 
      >| [(* s' = s *)
          `(a1' = a1) /\ (a2' = a2) /\ (g2' = g2)` by (
	      FULL_SIMP_TAC (srw_ss()) []
	  ) >>
          RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  METIS_TAC [memory_upd_axiom]
	  ,
	  (* s' <> s *)
	  `(g2 <> g2') /\ (a1 <> a1') /\ g2' < PAR.ng` by ( 
	      METIS_TAC [cpol_inj] 
	  ) >>
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  `a2' IN A_IGCin g2'` by (
	      FULL_SIMP_TAC (srw_ss()) [A_IGCin_def] >>
	      METIS_TAC [pairTheory.SND]
	  ) >>
	  METIS_TAC [syncInv_def]
	 ]
      ,
      (* case: memory update right *)
      Cases_on `s' = s` 
      >| [(* s' = s *)
          `(a1' = a1) /\ (a2' = a2) /\ (g2' = g2)` by (
	      FULL_SIMP_TAC (srw_ss()) []
	  ) >>
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
	  ,
	  (* s' <> s *)
	  `(g2 <> g2') /\ (a1 <> a1') /\ g2' < PAR.ng` by ( 
	      METIS_TAC [cpol_inj] 
	  ) >>
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  `mem_abs (IM'.G g1).m a1' = mem_abs (IM'.G g2').m a2'` by (
	      `a2' IN A_IGCin g2'` by (
	          FULL_SIMP_TAC (srw_ss()) [A_IGCin_def] >>
	          METIS_TAC [pairTheory.SND]
	      ) >>
	      METIS_TAC [syncInv_def]
	  ) >>
	  ASM_REWRITE_TAC [memory_id_upd_axiom] 
	 ]	  
      ,
      (* case: not a target of g1 *)
      `g2' <> g2` by ( METIS_TAC [] ) >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM]
      ,
      (* case: not a target or not IGC *)
      `(g2 <> g2') \/ (g2 = g2') /\ a2 <> a` by ( 
          METIS_TAC [pairTheory.SND] 
      ) >> ( RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] ) >>
      METIS_TAC [memory_upd_axiom]
      ,
      (* case: memory update assertion *)
      Cases_on `g = g2`
      >| [RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  METIS_TAC []
	  ,
	  RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >>
	  EXISTS_TAC ``(IM'.G g).m`` >>
	  RW_TAC (srw_ss()) [guest_component_equality]
	 ]
     ]
);

val cif_igc_write_sync_lem = store_thm("cif_igc_write_sync_lem", ``
!IM IM' im' cif' g1 c1 q id r.
   g1 < PAR.ng
/\ c1 < PAR.nc_g g1
/\ mem_step_snd_rpl((IM.G g1).m,q,id,im')
/\ (IM' = IM with G := (g1 =+ ((IM.G g1) with 
       <|cif := (c1 =+ cif') (IM.G g1).cif; m := im'|>)) IM.G) 
/\ (q,id) NOTIN mem_rpl_rcvd ((IM.G g1).m)
/\ req_aligned r
/\ match(r,q)
/\ PAdr r IN A_IGCout g1
/\ syncInv IM
==>
?s g2 a2. 
   s < PAR.ns
/\ g2 < PAR.ng
/\ (PAR.cpol s = (g1,g2))
/\ (PAR.igca s = (PAdr r,a2))
/\ do_sync_shared_mem_upd_of_guest(IM',g1,
    IM' with <|G := (g2 =+ 
        (IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G g1).m (PAdr r)) 
					 (IM'.G g2).m|>) ) IM'.G|>)
``,
  REPEAT STRIP_TAC >>
  `?s g2 a2. s < PAR.ns /\ g2 < PAR.ng /\ 
	     (PAR.cpol s = (g1,g2)) /\ (PAR.igca s = (PAdr r,a2))` by (
      FULL_SIMP_TAC (srw_ss()) [A_IGCout_def] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [] >>
      `?g2. PAR.cpol s = (g1,g2)` by (
          METIS_TAC [pairTheory.FST, pairTheory.PAIR]
      ) >>
      EXISTS_TAC ``g2:num`` >>
      ASM_REWRITE_TAC [] >>
      EXISTS_TAC ``SND (PAR.igca s)`` >>
      `SND (PAR.cpol s) < PAR.ng` by ( METIS_TAC [goodP_axiom] ) >>
      METIS_TAC [pairTheory.PAIR, pairTheory.SND]
  ) >>
  REPEAT HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC [] >>
  MATCH_MP_TAC single_igc_mem_upd_lem >>
  EXISTS_TAC ``IM:ideal_model`` >>
  EXISTS_TAC ``s:num`` >>
  METIS_TAC [cif_igc_mem_unchanged_lem]
);

val pif_igc_write_sync_lem = store_thm("pif_igc_write_sync_lem", ``
!IM IM' im' pif' g1 p1 q id r.
   g1 < PAR.ng
/\ p1 < PAR.np_g g1
/\ mem_step_snd_rpl((IM.G g1).m,q,id,im')
/\ (IM' = IM with G := (g1 =+ ((IM.G g1) with 
       <|m := im'; pif := (p1 =+ pif') (IM.G g1).pif|>)) IM.G) 
/\ (q,id) NOTIN mem_rpl_rcvd ((IM.G g1).m)
/\ req_aligned r
/\ match(r,q)
/\ PAdr r IN A_IGCout g1
/\ syncInv IM
==>
?s g2 a2. 
   s < PAR.ns
/\ g2 < PAR.ng
/\ (PAR.cpol s = (g1,g2))
/\ (PAR.igca s = (PAdr r,a2))
/\ do_sync_shared_mem_upd_of_guest(IM',g1,
    IM' with <|G := (g2 =+ 
        (IM'.G g2 with <|m := memory_upd (a2,mem_abs (IM'.G g1).m (PAdr r)) 
					 (IM'.G g2).m|>) ) IM'.G|>)
``,
  REPEAT STRIP_TAC >>
  `?s g2 a2. s < PAR.ns /\ g2 < PAR.ng /\ 
	     (PAR.cpol s = (g1,g2)) /\ (PAR.igca s = (PAdr r,a2))` by (
      FULL_SIMP_TAC (srw_ss()) [A_IGCout_def] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [] >>
      `?g2. PAR.cpol s = (g1,g2)` by (
          METIS_TAC [pairTheory.FST, pairTheory.PAIR]
      ) >>
      EXISTS_TAC ``g2:num`` >>
      ASM_REWRITE_TAC [] >>
      EXISTS_TAC ``SND (PAR.igca s)`` >>
      `SND (PAR.cpol s) < PAR.ng` by ( METIS_TAC [goodP_axiom] ) >>
      METIS_TAC [pairTheory.PAIR, pairTheory.SND]
  ) >>
  REPEAT HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC [] >>
  MATCH_MP_TAC single_igc_mem_upd_lem >>
  EXISTS_TAC ``IM:ideal_model`` >>
  EXISTS_TAC ``s:num`` >>
  METIS_TAC [pif_igc_mem_unchanged_lem]
);

val cif_no_igc_write_sync_lem = store_thm("cif_no_igc_write_sync_lem", ``
!IM IM' im' cif' g1 c1 q id r.
   g1 < PAR.ng
/\ c1 < PAR.nc_g g1
/\ mem_step_snd_rpl((IM.G g1).m,q,id,im')
/\ (IM' = IM with G := (g1 =+ ((IM.G g1) with 
       <|cif := (c1 =+ cif') (IM.G g1).cif; m := im'|>)) IM.G) 
/\ (q,id) NOTIN mem_rpl_rcvd ((IM.G g1).m)
/\ req_aligned r
/\ match(r,q)
/\ (PAdr r NOTIN A_IGCin g1 /\ (PAdr r NOTIN A_IGCout g1) \/ ~Wreq r)
/\ syncInv IM
==>
syncInv IM'
``,
  REPEAT STRIP_TAC >> ( 
      MATCH_MP_TAC syncInv_no_igc_lem >>
      EXISTS_TAC ``IM:ideal_model`` >>
      ASM_REWRITE_TAC [] >>
      `!g a. (a IN A_IGCin g1 \/ a IN A_IGCout g1) ==>
             (mem_abs (IM.G g1).m a = mem_abs im' a)` by (
          METIS_TAC[mem_unchanged_lem]
      ) >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
          METIS_TAC []
      )
  )
);


val pif_no_igc_write_sync_lem = store_thm("pif_no_igc_write_sync_lem", ``
!IM IM' im' pif' g1 p1 q id r.
   g1 < PAR.ng
/\ p1 < PAR.np_g g1
/\ mem_step_snd_rpl((IM.G g1).m,q,id,im')
/\ (IM' = IM with G := (g1 =+ ((IM.G g1) with 
       <|m := im'; pif := (p1 =+ pif') (IM.G g1).pif|>)) IM.G) 
/\ (q,id) NOTIN mem_rpl_rcvd ((IM.G g1).m)
/\ req_aligned r
/\ match(r,q)
/\ (PAdr r NOTIN A_IGCin g1 /\ (PAdr r NOTIN A_IGCout g1) \/ ~Wreq r)
/\ syncInv IM
==>
syncInv IM'
``,
  REPEAT STRIP_TAC >> ( 
      MATCH_MP_TAC syncInv_no_igc_lem >>
      EXISTS_TAC ``IM:ideal_model`` >>
      ASM_REWRITE_TAC [] >>
      `!g a. (a IN A_IGCin g1 \/ a IN A_IGCout g1) ==>
             (mem_abs (IM.G g1).m a = mem_abs im' a)` by (
          METIS_TAC[mem_unchanged_lem]
      ) >>
      RW_TAC (srw_ss()) [combinTheory.APPLY_UPDATE_THM] >> (
          METIS_TAC []
      )
  )
);

val bif_rcv_rpl_lem = store_thm("bif_rcv_rpl_lem", ``
!B r q B'.
   r IN B.req_sent 
/\ match(r,q)
/\ bif_step_rcv_rpl(B,q,B')
==>
   (B'.req_rcvd = B.req_rcvd)
/\ (B'.rpl_rcvd = B.rpl_rcvd UNION {q}) 
/\ (B'.req_sent = B.req_sent DIFF {r})
``,
  RW_TAC (srw_ss()) [bif_step_rcv_rpl_def] >>
  IMP_RES_TAC unique_match_thm >>
  RW_TAC (srw_ss()) [] >>
  `{q' | match(q',q)} = {q'}` by (
      RW_TAC (srw_ss()) [pred_setTheory.EXTENSION] >>
      METIS_TAC [unique_match_thm]
  ) >>
  RW_TAC (srw_ss()) []
);


(* ideal model invariant *)
val InvI_def = Define `InvI (M : ideal_model) =
    (* guest-internal invariant *)
    (!g. g < PAR.ng ==> InvG (M.G g, g))
    (* sync invarinat *)
 /\ syncInv(M)`;

val InvG_imp_lem = store_thm("InvG_imp_lem", ``
!g IM. g < PAR.ng ==> InvI IM ==> InvG (IM.G g, g)
``,
  RW_TAC (srw_ss()) [InvI_def]
);

val InvG_EXPAND = save_thm("InvG_EXPAND", 
(SIMP_CONV (srw_ss()++DatatypeSimps.expand_type_quants_ss([``:IDG_INVS``])) 
           [InvG_def]
THENC
(SIMP_CONV (srw_ss()) [idg_inv_def]))
``InvG (G,g)``
);


(*************** finish ***********)

val _ = export_theory();
