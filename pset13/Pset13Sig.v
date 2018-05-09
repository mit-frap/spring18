(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 13 *)

Require Import Frap.

(* Authors: Peng Wang (wangpeng@csail.mit.edu), Adam Chlipala (adamc@csail.mit.edu) *)

Set Implicit Arguments.

(** * Rely/Guarantee Reasoning *)

(* In this problem set we will reason about concurrent programs using a program
 * logic called rely-guarantee program logic.  In this logic, in addition to
 * precondition and postcondition, each Hoare triple also contains a "rely,"
 * which specifies how the environment (i.e. other threads) can interfere and
 * change the state at any point; and a "guarantee," which specifies how
 * *any piece of* this program can change the state (so the Hoare triple should
 * really be called "Hoare quintuple").  The name "rely-guarantee" comes from
 * the interpretation "I rely on the environment to interfere in a way
 * compatible with the rely condition, and I guarantee that I will make no
 * atomic state change not allowed by the guarantee condition."  It is important
 * that the guarantee condition is imposed on all atomic state changes, because
 * any piece of a program can be run in a burst of execution by the scheduler,
 * and its effect is interference from other threads' points of view.  By
 * decomposing a multi-thread program into threads with rely/guarantee acting as
 * their interface, we achieve modular, thread-local reasoning. *)

(** ** Similar language definition as before, except that we group [Read] and
     * [Write] into a syntax category called [Atomic] operations. *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Inductive atomic : Set -> Type :=
| Read (addr : nat) : atomic nat
| Write (addr : nat) (value : nat) : atomic unit.

Inductive cmd : Set -> Type :=
| Return {t : Set} (r : t) : cmd t
| Bind {t t' : Set} (c1 : cmd t) (c2 : t -> cmd t') : cmd t'
| Fail {result} : cmd result
| Par (c1 c2 : cmd unit) : cmd unit
| Atomic {t : Set} (a : atomic t) : cmd t
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Notation heap := (fmap nat nat).
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

(* The next two definitions, of step relations, should be unsurprising by now,
 * essentially copying rules we've seen already in other contexts. *)

(* atomic step *)
Inductive astep : forall {t : Set}, heap * atomic t -> heap * t -> Prop :=
| StepRead : forall h a,
    astep (h, Read a) (h, h $! a)
| StepWrite : forall h a v,
    astep (h, Write a v) (h $+ (a, v), tt).

Hint Constructors astep.

Inductive step : forall {t : Set}, heap * cmd t -> heap * cmd t -> Prop :=
| StepBindRecur : forall {t t' : Set} (c1 c1' : cmd t) (c2 : t -> cmd t') h h',
    step (h, c1) (h', c1')
    -> step (h, Bind c1 c2) (h', Bind c1' c2)
| StepBindProceed : forall {t t' : Set} (v : t) (c2 : t -> cmd t') h,
    step (h, Bind (Return v) c2) (h, c2 v)
| StepPar1 : forall h c1 c2 h' c1',
    step (h, c1) (h', c1')
    -> step (h, Par c1 c2) (h', Par c1' c2)
| StepPar2 : forall h c1 c2 h' c2',
    step (h, c2) (h', c2')
    -> step (h, Par c1 c2) (h', Par c1 c2')
| StepAtomic : forall {t : Set} h a h' (v : t),
    astep (h, a) (h', v)
    -> step (h, Atomic a) (h', Return v) 
| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h,
  step (h, Loop init body) (h, x <- body init; match x with
                                               | Done y => Return y
                                               | Again y => Loop y body
                                               end).

Hint Constructors step.

Definition trsys_of h {t : Set} (c : cmd t) := {|
  Initial := {(h, c)};
  Step := step (t := t)
|}.

(* predicates on heaps *)
Definition hprop := heap -> Prop.
(* binary relations on heaps *)
Definition hrel := heap -> heap -> Prop.

(* "Stability" is an important notion in rely-guarantee logic.  A heap predicate
 * is stable under some interference (expressed as a binary relation on heaps,
 * telling us which heap changes the interference can cause) if whenever the
 * predicate holds before the interference, it will still hold after the
 * interference. *)
Definition stableP (P : hprop) (R : hrel) := forall h h', P h -> R h h' -> P h'.

(* [stableP] defined the basic interference notion, while [stableQ] adapts it to
 * work for postconditions, which are additionally parameterized over return
 * values. *)
Definition stableQ {t : Set} (Q : t -> hprop) (R : hrel) := forall v, stableP (Q v) R.

(* Here's a convenient predicate to assert both kinds of stability at once. *)
Definition stable {t : Set} (P : hprop) (Q : t -> hprop) R :=
  stableP P R /\ stableQ Q R.

Inductive hoare_triple : forall {t : Set}, hprop -> hrel -> cmd t -> hrel -> (t -> hprop) -> Prop :=
| HtBind : forall {t t' : Set} (c1 : cmd t) (c2 : t -> cmd t') P1 R G Q1 Q2 ,
    (* The bind rule is almost the same as before.  The same rely and guarantee
     * are propagated into subparts.  (Subparts can relax these parameters using
     * the Consequence rule.) *)
    hoare_triple P1 R c1 G Q1
    -> (forall r, hoare_triple (Q1 r) R (c2 r) G Q2)
    -> hoare_triple P1 R (Bind c1 c2) G Q2

| HtPar : forall P1 c1 Q1 P2 c2 Q2 R G1 G2 (P : hprop),
    (* The essence of rely-guarantee reasoning is shown here: one thread's
     * guarantee becomes another thread's rely. *)
    hoare_triple P1 (fun h h' => R h h' \/ G2 h h') c1 G1 Q1
    -> hoare_triple P2 (fun h h' => R h h' \/ G1 h h') c2 G2 Q2

    (* By design we require preconditions to remain stable. *)
    -> stableP P R

    (* We also allow weakening of the precondition into a different
     * more-permissive version for each new thread. *)
    -> (forall h, P h -> P1 h)
    -> (forall h, P h -> P2 h)

    -> hoare_triple P R (Par c1 c2) (fun h h' => G1 h h' \/ G2 h h') (fun r h => Q1 r h /\ Q2 r h)
    (* Note that the combined guarantee is effectively the union of guarantees
     * of the individual threads, while the combined postcondition is the
     * intersection of postconditions. *)

| HtFail : forall {result} R,
    (* Nothing changes for failure: it must be impossible to reach. *)
    hoare_triple (fun _ => False) R (Fail (result := result)) (fun _ _ => False) (fun _ _ => False)

| HtReturn : forall {t : Set} (P : hprop) (R G : hrel) (v : t),
    (* We add one extra premise for [Return], about stability. *)
    stableP P R
    -> hoare_triple P R (Return v) G (fun r h => P h /\ r = v)

| HtAtomic : forall {t : Set} (P : hprop) (R G : hrel) (Q : t -> hprop) a,
    (* Here is the rule that forces us to pick a nonempty guarantee set: it
     * should contain the effect of every atomic operation we run. *)
    (forall (v : t) h h', P h -> astep (h, a) (h', v) -> G h h')

    (* Furthermore, taking an atomic step should get us to the postcondition. *)
    -> (forall (v : t) h h', P h -> astep (h, a) (h', v) -> Q v h')

    (* Here we require both precondition and postcondition to be stable.
     * That is, the environment should not be able to invalidate the truth of
     * either one, when it only takes steps permitted by [R]. *)
    -> stable P Q R

    -> hoare_triple P R (Atomic a) G Q

| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc))
             (I : loop_outcome acc -> hprop) R G,
    (* This rule is about the same as before, with an extra stability
     * requirement. *)
    (forall acc, hoare_triple (I (Again acc)) R (body acc) G I)
    -> (forall acc, stableP (I (Done acc)) R)
    -> hoare_triple (I (Again init)) R (Loop init body) G (fun r h => I (Done r) h)

| HtConsequence : forall {t : Set} P R c G Q (P' : hprop) (R' G' : hrel) (Q' : t -> hprop),
    (* You can relax any part, in the right direction. *)
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', R' h h' -> R h h')
    -> (forall h h', G h h' -> G' h h')
    (* But make sure the new precondition is stable! *)
    -> stableP P' R'
    -> hoare_triple P' R' c G' Q'.

Hint Constructors hoare_triple.

(* You may find this lemma useful in the soundness proof we ask you to
 * complete. *)
Lemma always_stableP : forall (t : Set) P R c G (Q : t -> _),
    hoare_triple P R c G Q
    -> stableP P R.
Proof.
  induct 1; unfold stableP in *; first_order.
Qed.

Hint Resolve always_stableP.


(* The next span of code, up to the word "Example", sets up some automation
 * support. Feel free to skip ahead to the example to see the ingredients 
 * in action in the verification of an example program.
 *)

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
    stableP P R
    -> (forall h, P h -> Q v h)
    -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma HtFail' : forall {t : Set} (P : hprop) (R G : hrel) (Q : t -> hprop),
    (forall h, P h -> False)
    -> hoare_triple P R Fail G Q.
Proof.
  simplify.
  eapply HtConsequence with (R' := R) (G' := G) (Q' := Q); eauto.
  simplify; propositional.
  simplify; propositional.
  unfold stableP; simplify.
  first_order.
Qed.

Lemma HtConsequenceBasic : forall {t : Set} P R c G Q (P' : hprop) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> (forall v h, Q v h -> Q' v h)
    -> stableP P' R
    -> hoare_triple P' R c G Q'.
Proof.
  eauto.
Qed.

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> stableP P' R
    -> hoare_triple P' R c G Q.
Proof.
  eauto.
Qed.

Lemma HtWeaken : forall {t : Set} P R c G Q (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> hoare_triple P R c G Q'.
Proof.
  eauto.
Qed.

Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', G h h' -> G' h h')
    -> hoare_triple P R c G' Q'.
Proof.
  eauto.
Qed.

Require Import Eqdep.

(* The first several tactics are similar to those that we have
 * already seen for earlier iterations of our Hoare logics.
 *)
Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         | [ H : astep _ _ |- _ ] => invert H
                         | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H; subst
                         | [ |- stableP _ _ ] => unfold stableP in *
                         | [ |- stable _ _ _ ] => unfold stable, stableP, stableQ in *
                         end); try solve [ intuition linear_arithmetic | equality ].

Ltac step0 := apply HtReturn' || eapply HtFail' || eapply HtBind.
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac loop_inv0 Inv := (eapply HtStrengthen; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequenceBasic; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; simp.
Ltac strengthen P_ := apply HtStrengthen with (P := P_); simp.

(* Here are some new tactics:
 * The [fork] tactic builds a Hoare triple for a parallel program
 * with particular preconditions, rely/guarantees, and postconditions.
 *)
Ltac fork P1_ G1_ Q1_ P2_ G2_ Q2_ := eapply HtWeakenFancy; [ eapply HtPar with (P1 := P1_) (G1 := G1_) (Q1 := Q1_) (P2 := P2_) (G2 := G2_) (Q2 := Q2_) | .. ].
(* The [atomic] tactic builds a Hoare triple for an atomic step
 * with a particular postcondition.
 *)
Ltac atomic Q_ := eapply HtAtomic with (Q := Q_); simp.

(* When inverting facts involving [cmd]s, you may find that you have
 * equalities of the form [existT P p x = existT P p y]. The following
 * tactic derives the equality [x = y] from facts of this sort and
 * performs substitution. You may find this useful for your soundness 
 * proof of the rely-guarantee logic.
 * (This tactic performs a subset of what [simp] does.)
 * So what makes these strange-looking goals pop into existence, anyway?
 * They arise from inversion on hypotheses involving fancy types.
 * In general, inversion derives new equalities.  Sometimes a particular
 * derived equality relates terms whose *types* are computed via some
 * fancy recipe.  The constructor [existT] is used to package a term together
 * with its (first-class) type.  Interestingly, the natural inversion
 * principle, for equalities on those sorts of packages, is not provable in
 * Coq!  It's actually formally independent of Coq's logic.  However, a
 * standard-library lemma [inj_pair2] proves the inversion principle from a
 * more basic axiom.  For more detail (orthogonal to this course), see the
 * [Eqdep] module of the Coq standard library.
 *)
Ltac existT_subst :=
   repeat match goal with
   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H
   end; subst.

Hint Extern 1 (_ >= _) => linear_arithmetic.


(** * Example *)

(* Here is a demonstrative use of rely-guarantee logic to verify a concurrent
 * program.  We prove that two threads cooperate to keep the value in one memory
 * address even.  They follow a manually implemented locking protocol.  That is,
 * while our proofs in Concurrent Separation Logic assume a locking instruction
 * built into the language, here we code and justify mutual-exclusion
 * functionality explicitly. *)

Fixpoint isEven (n : nat) : bool :=
  match n with
  | O => true
  | S (S n') => isEven n'
  | _ => false
  end.

Definition prog2_th turn_addr data_addr me other :=
  (* First, we loop forever adding to a counter. *)
  for _ := tt loop
    (* The next loop waits until it's our turn to run. *)
    _ <- (for _ := tt loop
      (* We read from a flag [turn_addr] that holds the ID of the thread allowed
       * to run next. *)
      turn <- Atomic (Read turn_addr);
      if turn ==n me then
        (* Is it my turn?  Good; exit the loop. *)
        Return (Done tt)
      else
        (* Not my turn?  Go around again. *)
        Return (Again tt)
      done);
    (* OK, we are allowed to run.  Let's read the counter from [data_addr]. *)
    tmp <- Atomic (Read data_addr);
    if isEven tmp then
      (* Just to make this interesting, let's first write an odd value, based on
       * incrementing by 1!  The other thread had better not be looking now. *)
      _ <- Atomic (Write data_addr (1 + tmp));
      (* Now let's read back what we wrote. *)
      tmp2 <- Atomic (Read data_addr);
      (* Then increment again to reach an even value. *)
      _ <- Atomic (Write data_addr (1 + tmp2));
      (* Finally, flip the whose-turn flag to the other thread's ID. *)
      _ <- Atomic (Write turn_addr other);
      Return (Again tt)
    else
      (* Impossible case: we read an odd counter. *)
      Fail
  done.

Example prog2 turn_addr data_addr :=
  prog2_th turn_addr data_addr 0 1 || prog2_th turn_addr data_addr 1 0.

(* Let's prove this program against a natural spec. *)
Lemma ht_prog2 : forall turn_addr data_addr,
    turn_addr <> data_addr
    -> hoare_triple
         (fun h => isEven (h $! data_addr) = true /\ (h $! turn_addr = 0 \/ h $! turn_addr = 1))
         (* Precondition: data starts out even, and it's someone's turn. *)

         (fun _ _ => False)
         (* Rely: no other threads are allowed to do anything at all, because
          * this program is meant to run by itself, with just these two
          * threads. *)
         
         (prog2 turn_addr data_addr)

         (fun _ _ => True)
         (* Guarantee: we are generous to ourselves and allow any steps. ;-)
          * (We will still use stricter guarantees internally within the
          * proof.) *)

         (fun _ _ => False)
         (* Postcondition: the program is nonterminating by design! *).
Proof.
  unfold prog2, prog2_th.
  simp.

  (* We use the [fork] tactic to make progress when we get to a parallel
   * composition. *)
  fork (fun h => (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true)
                 \/ h $! turn_addr = 1)
       (* This is the precondition of the first thread.  Note how we make no
        * claim about the counter value if it is the *other* thread's turn.
        * Otherwise, the precondition would not be *stable*. *)

       (fun h h' => (h $! turn_addr = 0
                     /\ h' $! turn_addr = 0)
                    \/ (h $! turn_addr = 0
                        /\ h' $! turn_addr = 1
                        /\ isEven (h' $! data_addr) = true)
                    \/ (h $! turn_addr = 1
                        /\ h' $! turn_addr = 1
                        /\ h' $! data_addr = h $! data_addr))
       (* This is the first thread's guarantee: any step it takes should satisfy
        * this relation.  The details are easier to read in math than to explain
        * in prose! *)

       (fun (_ : unit) (_ : heap) => False)
       (* And here's the first thread's postcondition. *)

       (* We then repeat the mirror images to give the same specifications for
        * the second thread. *)
       (fun h => (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true)
                 \/ h $! turn_addr = 0)
       (fun h h' => (h $! turn_addr = 1
                     /\ h' $! turn_addr = 1)
                    \/ (h $! turn_addr = 1
                        /\ h' $! turn_addr = 0
                        /\ isEven (h' $! data_addr) = true)
                    \/ (h $! turn_addr = 0
                        /\ h' $! turn_addr = 0
                        /\ h' $! data_addr = h $! data_addr))
       (fun (_ : unit) (_ : heap) => False).

  (* Now we're verifying thread #1. *)

  (* The outer loop invariant is a repeat of the precondition, also asserting
   * that the loop can never terminate (e.g., [Done] mapped to [False]). *)
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => False
                                             | Again _ => (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 1
                                             end).
  step.
  (* Inner loop invariant: if the loop isn't done yet ([Again]), then we repeat
   * the precondition; otherwise, we have learned that it's our turn, so we use
   * the precondition with the case for "it's not my turn" pruned out. *)
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => h $! turn_addr = 0 /\ isEven (h $! data_addr) = true
                                             | Again _ => (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 1
                                             end).
  step.
  (* Every time we reach an atomic command (read or write), we call [atomic],
   * providing the postcondition explicitly.  Some care is needed in choosing
   * this predicate, since it must be *stable*.  That is, other threads must not
   * be allowed to falsify it. *)
  atomic (fun r h =>
            ((h $! turn_addr = 0 /\ isEven (h $! data_addr) = true)
             \/ h $! turn_addr = 1)
            /\ (r = 0 -> h $! turn_addr = 0)).
  (* Further details in this particular proof aren't essential for completing
   * this pset, but feel free to step through and see what's happening. *)
  cases (r ==n 0).
  step.
  step.
  step.
  atomic (fun r h =>
            h $! turn_addr = 0 /\ isEven (h $! data_addr) = true /\ r = h $! data_addr).
  simp.
  cases (isEven r0).
  step.
  atomic (fun (_ : unit) h =>
            exists r, h $! turn_addr = 0 /\ isEven r = true /\ h $! data_addr = 1 + r).
  eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun r' h =>
            exists r, h $! turn_addr = 0 /\ isEven r = true /\ h $! data_addr = 1 + r /\ r' = 1 + r).
  eauto.
  rewrite H4; eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun (_ : unit) h =>
            h $! turn_addr = 0 /\ isEven (h $! data_addr) = true).
  rewrite H4; eauto.
  step.
  atomic (fun (_ : unit) h =>
            (h $! turn_addr = 0 /\ isEven (h $! data_addr) = true)
            \/ h $! turn_addr = 1).
  step.
  step.

  (* Here's the proof for the second thread, where we switch [0]s with [1]s. *)
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => False
                                             | Again _ => (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 0
                                             end).
  step.
  loop_inv (fun (o : loop_outcome unit) h => match o with
                                             | Done _ => h $! turn_addr = 1 /\ isEven (h $! data_addr) = true
                                             | Again _ => (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true) \/ h $! turn_addr = 0
                                             end).
  step.
  atomic (fun r h =>
            ((h $! turn_addr = 1 /\ isEven (h $! data_addr) = true)
             \/ h $! turn_addr = 0)
            /\ (r = 1 -> h $! turn_addr = 1)).
  cases (r ==n 1).
  step.
  step.
  step.
  atomic (fun r h =>
            h $! turn_addr = 1 /\ isEven (h $! data_addr) = true /\ r = h $! data_addr).
  simp.
  cases (isEven r0).
  step.
  atomic (fun (_ : unit) h =>
            exists r, h $! turn_addr = 1 /\ isEven r = true /\ h $! data_addr = 1 + r).
  eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun r' h =>
            exists r, h $! turn_addr = 1 /\ isEven r = true /\ h $! data_addr = 1 + r /\ r' = 1 + r).
  eauto.
  rewrite H4; eauto.
  rewrite H4; eauto.
  simp.
  step.
  atomic (fun (_ : unit) h =>
            h $! turn_addr = 1 /\ isEven (h $! data_addr) = true).
  rewrite H4; eauto.
  step.
  atomic (fun (_ : unit) h =>
            (h $! turn_addr = 1 /\ isEven (h $! data_addr) = true)
            \/ h $! turn_addr = 0).
  step.
  step.
  
  simp.
  simp.
  simp.
  simp.
  simp.
Qed.


(* You will be asked to verify that this simpler program
   manages to increase the counter value. *)
Example prog1 :=
  (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
  || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1))).

(* Now let's turn to soundness, which is still defined in terms of the "not
 * about to fail" property.  Here we use an inductive version instead of the
 * recursive-function version. *)
Inductive notAboutToFail : forall {t : Set}, cmd t -> Prop :=
| NatfBind : forall t t' (c1 : cmd t) (c2 : t -> cmd t'),
    notAboutToFail c1 ->
    notAboutToFail (Bind c1 c2)
| NatfPar : forall c1 c2,
    notAboutToFail c1 ->
    notAboutToFail c2 ->
    notAboutToFail (Par c1 c2)
| NatfReturn : forall (t : Set) (v : t),
    notAboutToFail (Return v)
| NatfAtomic : forall t (a : atomic t),
    notAboutToFail (Atomic a)
| NatfLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)),
    notAboutToFail (Loop init body).

Hint Constructors notAboutToFail.

Module Type S.

  (* Verify that the program [prog1] manages to push the counter
   * value above its initial value. *)  
  Axiom ht_prog1 : forall init, hoare_triple
                                (fun h => h $! 0 = init)
                                (fun _ _ => False)
                                prog1
                                (fun _ _ => True)
                                (fun _ h => h $! 0 > init).

  (* Prove soundness of rely-guarantee program logic. *)
  Axiom hoare_triple_sound :
    forall (t : Set) P (c : cmd t) Q,
      hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
      forall h,
        P h ->
        invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).

End S.


(* Here are a few more lemmas that you may find helpful. *)

Lemma stableP_star :
  forall R h h',
    R^* h h' ->
    forall P,
      stableP P R ->
      P h ->
      P h'.
Proof.
  induct 1; simplify; eauto.
  eapply IHtrc; eauto.
Qed.

Lemma stableP_weakenR : forall P R,
    stableP P R
    -> forall R' : hrel, (forall h1 h2, R' h1 h2 -> R h1 h2)
                         -> stableP P R'.
Proof.
  simp; eauto.
Qed.

Lemma stableP_self : forall h R,
    stableP (fun h' => R^* h h') R.
Proof.
  simp.
  eauto using trc_trans.
Qed.

Hint Resolve stableP_self.

Lemma trc_imply :
  forall t R (s s' : t),
    R^* s s' ->
    forall (R' : _ -> _ -> Prop),
      (forall s s', R s s' -> R' s s') ->
      R'^* s s'.
Proof.
  induct 1; simplify; eauto.
Qed.

Lemma stable_stableQ : forall (t : Set) P (Q : t -> _) R r, stable P Q R -> stableP (Q r) R.
Proof.
  unfold stable; propositional; eauto.
Qed.
Hint Resolve stable_stableQ.

Lemma stable_stableP : forall (t : Set) P (Q : t -> _) R, stable P Q R -> stableP P R.
Proof.
  unfold stable; propositional; eauto.
Qed.
Hint Resolve stable_stableP.
