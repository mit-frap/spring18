(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

Require Import Frap Pset7Sig.

Theorem validator_ok:
  forall v s t, validator s t = true -> (v, s) =| (v, t).
Proof.
Admitted.
