Require Import Frap Pset13Sig.

Set Implicit Arguments.

(* Stuck? Hints are available on the class website. *)

Lemma ht_prog1 : forall init, hoare_triple
                                (fun h => h $! 0 = init)
                                (fun _ _ => False)
                                prog1
                                (fun _ _ => True)
                                (fun _ h => h $! 0 > init).
Proof.
Admitted.

Theorem hoare_triple_sound :
  forall (t : Set) P (c : cmd t) Q,
    hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
    forall h,
      P h ->
      invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
Proof.
Admitted.
