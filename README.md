# haspocproofs

HOL4 Model and Proofs for "On the Verification of System Level Information Flow
Properties for Virtualized Execution Platforms"

Submission to JCEN by Christoph Baumann, Oliver Schwarz, and Mads Dam

We verify information flow security for the design of the HASPOC hypervisor:

https://haspoc.sics.se/

## DISCLAIMER

The models and proofs presented here are a snapshot of our formal development. Note that so far only the steps of guests have been proven to preserve a bisimulation between the implementation model and an ideal specification, i.e., the transition system of the hypervisor has been modeled but not verified. 

Note that the documentation is slightly outdated and currently under revision. We will provide a complete and up-to-date version as soon as possible.

Moreover we acknowledge that our formalisation and the proofs may be seen as
rather inelegant and brute-force at times. We blame this in part on lack of
experience with the tool at the beginning of the project. Looking back, we would
certainly do things differently when it comes to the technical details. Please
keep in mind that this exercise was conducted as a feasability study for the
approach described in the paper. As such we see it as a confirmation of its
viability, even though the formalization surely needs improvement.

## BUILD NOTES

The theory can be built with the latest Kananaskis 12 release of HOL4 by
executing "Holmake" in the project directory. No makefile should be necessary,
all the necessary libraries are either contained in the project directory or
come with the HOL4 distribution.

See https://hol-theorem-prover.org/#get for instructions how to clone and
compile HOL4 from github.

## FURTHER COMMENTS

The proof itself completes in about 30 minutes on an unvirtualized machine with
8 cores and 32GiB of RAM. Most lemmas are proven in a few seconds while some
bigger lemmas may take significantly longer. Clearly, we haven't optimized the
proofs for speed.

In a few parts of the proof we were assisted by Thomas Tuerk, who provided some
improved definitions and lemmas. These parts are marked accordingly.

The abstract component models are provided in an axiomatized fashion. We
initially used "new_axiom" for all these specification functions. Later we
started to replace them gradually with "new_specification" constructions,
however this work is not finished. It seems to be easier to redefine them from
scratch as specification functions, using some dummy instantiations for the
existence proofs, than to replace the current axioms one by one.

As noted above, we only showed the bisimulation between the ideal and
refined model for steps that involve the guest. Lemmas about hypervisor steps
are mainly proven by "cheat", i.e., assumed to be true. The same holds for the
proof of the refined model invariant which was only conducted on paper.

Since this proof was only meant as a case study we simplified the hypervisor
design and the hardware behaviour in a few places. These simplifications are
mentioned in comments next to the corresponding definitions.

## FILE DESCRIPTION

* math_lemmasScript.sml   -- some mathematical lemmas about sets and bit vectors

* axtypesScript.sml       -- uninterpreted types used in the system models

* haspoctypesScript.sml   -- main type definitions and helper functions

* parametersScript.sml    -- parameters of the ideal and refined models

* axfuncsScript.sml       -- uninterpreted specification of the component models
  			     behavioral, enabling, and bisimulation specs
		         
* hypervisorScript.sml    -- hypervisor specification, address translation, 
                             and index mappings
		         
* refinedScript.sml       -- definition of refined model
		         
* idealScript.sml	  -- definition of ideal model and invariant
		         
* refinedInvScript.sml    -- definition of refined model invariant

* idealInvProofScript.sml -- proof of ideal invariant

* bisimScript.sml         -- definition of bisimulation relation

* bisimProofScript.sml    -- bisimulation proof for guest steps

* annotationsLib.sml      -- support for annotated definitions

* haspocLib.sml           -- custom helper tactics

* haspocSimps.sml         -- custom simplification set

* tacticsLib.sml          -- generic helper tactics

* toolboxLib.sml	  -- SML helper functions

* proof_sketch            -- sketch of bisimulation proof strategy, 
	 		     showing which steps are coupled for each proof goal

* doc/doc.pdf		  -- technical documentation of the formal work

* README.md		  -- this file

