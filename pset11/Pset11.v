Require Import Frap Pset11Sig.


(* Opaque mtree. *)
(* ^-- Don't forget to mark predicates opaque after you've finished proving 
 * all the key algebraic properties about them, in order for them to work
 * well with the [cancel] tactic. *)

Theorem lookup_ok : forall x p,
  {{mtreep p}}
    lookup x p
  {{_ ~> mtreep p}}.
Proof.
Admitted.

Theorem insert_ok : forall x p,
  {{mtreep p}}
    insert x p
  {{_ ~> mtreep p}}.
Proof.
Admitted.
