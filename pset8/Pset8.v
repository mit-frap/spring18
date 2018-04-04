Require Import Frap Pset8Sig.

Set Implicit Arguments.

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
Admitted.

Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
Admitted.

Theorem safety :
  forall e t,
    hasty $0 e t -> invariantFor (trsys_of e)
                                 (fun e' => value e'
                                            \/ exists e'', step e' e'').
Proof.
Admitted.
