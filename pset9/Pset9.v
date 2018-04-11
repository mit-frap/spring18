(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 9 *)

Require Import Frap Pset9Sig.

Set Implicit Arguments.

Theorem logical_rel_fundamental:
  forall abst1 abst2 (value_rel_abs: exp -> exp -> Prop),
    (forall v1 v2, value_rel_abs v1 v2 -> value v1 /\ value v2) ->
    abst1 <> AbsT ->
    abst2 <> AbsT ->
    forall e G t,
      hasty None G e t ->
      logical_rel abst1 abst2 value_rel_abs G e e t.
Proof.
Admitted.

Theorem counter_impls_equiv:
  forall x e,
    hasty None ($0 $+ (x, counter_type)) e Nat ->
    exists n : nat,
      eval (subst counter_impl1 x e) n /\ eval (subst counter_impl2 x e) n.
Proof.
Admitted.
