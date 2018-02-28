Require Import Frap Pset4Sig.
Require Import OrdersFacts.

(* Before beginning this problem set, please see Pset4Sig.v,
 * which contains the instructions.
 *)

(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset4Sig).
Include (OrderedTypeTest Pset4Sig).
(* Print OrderedTypeFacts. *)
(* Print OrderedTypeTest. *)

(* Our solution only needs (at most) the following facts from the above libraries.
 * But it is certainly okay if you use facts beyond these! 
 *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.

Theorem insert_member: forall t n, BST t -> member n (insert n t) = true.
Proof.
Admitted.

Theorem insert_ok: forall t n, BST t -> BST (insert n t).
Proof.
Admitted.

Theorem delete_ok: forall t n, BST t -> BST (delete n t).
Proof.
Admitted.

(* OPTIONAL PART! *)
(*Theorem delete_member: forall t n, BST t -> member n (delete n t) = false.
Proof.
Admitted.*)
