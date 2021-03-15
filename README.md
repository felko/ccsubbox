# Capture Calculus proofs

This project contains the Coq proofs for Capture Calculus

We developed the proofs with Coq version 8.10.0.

A makefile is attached, but to recreate it in case of problems, run the following command:

    coq_makefile -f _CoqProject -o Makefile

Then, to actually build the proofs:

    make
    
## Overview

The proofs are based on an implementation of System F-Sub in locally nameless style.

- All definitions can be found in the file `CCsub_Definitions.v`.
- The files `CCsub_Infrastructure.v` and `CCsub_Lemmas.v` contain technical lemmas related to substitution and the locally nameless representation.
- File `CCsub_CvFacts.v` contains lemmas about `cv`.
- File `CCsub_Hints.v` contains hints and tactics we found useful for in the next file.
- The file `CCsub_Soundness.v` contains lemmas leading to and including preservation and progress.
- Finally, the file `CCsub_Examples.v` contains lemmas leading to and including preservation and progress.
