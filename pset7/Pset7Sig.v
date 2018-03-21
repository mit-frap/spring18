(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 7 *)

Require Import Frap Datatypes.
Export Datatypes.

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu), 
 * Adam Chlipala (adamc@csail.mit.edu),
 * Ben Sherman (sherman@csail.mit.edu)
 *)

Set Implicit Arguments.

(** * Translation Validation of Constant Assignment Code Motion *)

(* In this problem set, we verify an optimization called constant assignment
 * code motion by using verified translation validation.  Instead of proving the
 * correctness of some target optimizations directly, sometimes it is easier to
 * statically check the connection between source and target programs and to say
 * that they are equivalent when they pass the checker. Then we can use an
 * unproven function to make the transformation, so long as it always happens to
 * transform programs into compatible counterparts.  More formally, we
 * can state our high-level goal like below:
 * [forall s t, Validator s t = true -> forall v, (v, s) =| (v, t)]
 *
 * CompCert also actively uses the translation-validation mechanism to verify
 * a number of optimizations. One well-known instance is called lazy code motion
 * (LCM). For details, refer to this article:
 *   http://gallium.inria.fr/~xleroy/publi/validation-LCM.pdf
 *
 * Here we also _formally validate_ the correctness of simple code motion. The
 * target language is exactly same as you've seen in the textbook. We will also
 * use the same semantics and trace-equivalence definitions. *)


(** * The target language syntax, semantics, and trace equivalence definitions *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Inductive cmd :=
| Skip
| Nop (* Here we have a new command called [Nop], in order to mark some 
       * important spots in programs. Semantics for [Nop] slightly differ from
       * that of [Skip]. We will explain why we need this additional command
       * for our target optimizations. *)
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Output (e : arith).

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%arith body) (at level 75).

Definition valuation := fmap var nat.
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Inductive context :=
| Hole
| CSeq (C : context) (c : cmd).

Inductive plug : context -> cmd -> cmd -> Prop :=
| PlugHole : forall c, plug Hole c c
| PlugSeq : forall c C c' c2,
    plug C c c' -> plug (CSeq C c2) c (Sequence c' c2).

Inductive step0 : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| Step0Nop : forall v, step0 (v, Nop) None (v, Skip)
| Step0Assign : forall v x e,
    step0 (v, Assign x e) None (v $+ (x, interp e v), Skip)
| Step0Seq : forall v c2,
    step0 (v, Sequence Skip c2) None (v, c2)
| Step0IfTrue : forall v e then_ else_,
    interp e v <> 0 ->
    step0 (v, If e then_ else_) None (v, then_)
| Step0IfFalse : forall v e then_ else_,
    interp e v = 0 ->
    step0 (v, If e then_ else_) None (v, else_)
| Step0WhileTrue : forall v e body,
    interp e v <> 0 ->
    step0 (v, While e body) None (v, Sequence body (While e body))
| Step0WhileFalse : forall v e body,
    interp e v = 0 ->
    step0 (v, While e body) None (v, Skip)
| Step0Output : forall v e,
    step0 (v, Output e) (Some (interp e v)) (v, Skip).

Inductive cstep : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| CStep : forall C v c l v' c' c1 c2,
    plug C c c1 ->
    step0 (v, c) l (v', c') ->
    plug C c' c2 ->
    cstep (v, c1) l (v', c2).

Inductive generate : valuation * cmd -> list (option nat) -> Prop :=
| GenDone : forall vc,
    generate vc []
| GenSkip : forall v,
    generate (v, Skip) [None]
| GenSilent : forall vc vc' ns,
    cstep vc None vc' ->
    generate vc' ns ->
    generate vc ns
| GenOutput : forall vc n vc' ns,
    cstep vc (Some n) vc' ->
    generate vc' ns ->
    generate vc (Some n :: ns).

Hint Constructors plug step0 cstep generate.

Definition traceInclusion (vc1 vc2 : valuation * cmd) :=
  forall ns, generate vc1 ns -> generate vc2 ns.
Infix "<|" := traceInclusion (at level 70).

Definition traceEquivalence (vc1 vc2 : valuation * cmd) :=
  vc1 <| vc2 /\ vc2 <| vc1.
Infix "=|" := traceEquivalence (at level 70).


(** * Some utilities for defining both the code-motion translator and validator *)

(* [maydiff] contains a set of variables where the values for them _may differ_
 * between two valuations. You will see soon why we need this notion. *)
Definition maydiff := fmap var nat.

(* [arithNotReading] checks whether [e] reads some variables in [md]. *)
Fixpoint arithNotReading (e: arith) (md: maydiff) :=
  match e with
  | Const _ => true
  | Var x => if md $? x then false else true
  | Plus e1 e2
  | Minus e1 e2
  | Times e1 e2 => arithNotReading e1 md && arithNotReading e2 md
  end.

(* An extended one for [cmd] *)
Fixpoint cmdNotReading (c: cmd) (md: maydiff) :=
  match c with
  | Skip
  | Nop => true
  | Assign _ e
  | Output e => arithNotReading e md
  | Sequence c1 c2 => cmdNotReading c1 md && cmdNotReading c2 md
  | If e tc fc => arithNotReading e md && cmdNotReading tc md && cmdNotReading fc md
  | While e c => arithNotReading e md && cmdNotReading c md
  end.

(* [Scheme Equality] tries to generate a proof of the decidability of the usual
 * equality. *)
Scheme Equality for arith.
Scheme Equality for cmd.
(* Now we can use [arith_eq_dec] and [cmd_eq_dec]. *)


(** * A simple loop/branch invariant code motion translator *)

(* [constAssignCodeMotion] lifts some constant-assignment commands. Given a 
 * source program, it returns _a pair of programs_, say (hint, target).  These
 * programs will differ only in the motion of some constant assignments.  To
 * keep the structures of the commands in alignment, we add extra [Nop] markers.
 * For instance, consider this program.
 *  ["x" <- "y"; "z" <- 0]
 * We decide to reorder the two assignments.  To prepare for that reordering, we
 * add an extra "reserved spot" for the "z" assignment, before the "x"
 * assignment.
 *  [     Nop; "x" <- "y"; "z" <- 0]
 * This program is the "hint."  Then the actual motion works as follows, leaving
 * behind a [Nop] for any assignment that was moved.
 *  ["z" <- 0; "x" <- "y"; Nop]
 * This program is the "target."
 *
 * We use [Nop] instead of [Skip] to keep a 1-1 execution correspondence between
 * "hint" and "target".  If [Skip] was used, the correspondence breaks down
 * since [Skip] in a program either stops or moves to the next sequence, while
 * [Nop] and [Assign] make explicit steps to [Skip].
 *
 * Along with the optimization, our validator takes "hint" and "target" as 
 * inputs. In other words, it takes two programs with exactly the same structure
 * except some [Nop]-[Assign] matches. The equivalence between the source 
 * program and "hint" is trivial; certainly we can prove it, but we skip doing
 * so in this problem set. *)
Fixpoint constAssignCodeMotion (c: cmd) :=
  match c with
  | Sequence c1 (Assign x (Const n)) =>
    if cmdNotReading c1 ($0 $+ (x, n)) then
      (Sequence Nop (Sequence c1 (Assign x (Const n))),
       Sequence (Assign x (Const n)) (Sequence c1 Nop))
    else (c, c)
  | Sequence c1 c2 =>
    let (from1, to1) := constAssignCodeMotion c1 in
    let (from2, to2) := constAssignCodeMotion c2 in
    (Sequence from1 from2, Sequence to1 to2)
  | _ => (c, c)
  end.
(* This function is just an example of an optimization compatible with our
 * validator.  We actually won't ask you to prove anything about the optimizer,
 * just the validator.  The latter will end up supporting some optimizations
 * that change code inside loops! *)


(** * A validator to check code motions are performed correctly *)

(* Now here is our validator. As mentioned above, inputs ([s] and [t]) of 
 * the validator should have the same syntax structure except for 
 * [Nop]-[Assign] and [Assign]-[Nop] cases.
 *
 * [validator'] returns either [Some nmd] if the command pair is valid
 * and [nmd] is the post-maydiff set, and [None] if the command pair
 * is invalid.
 *)
Fixpoint validator' (s t: cmd) (md: maydiff) : option maydiff :=
  match s, t with
  | Nop, Nop => Some md
  | Skip, Skip => Some md
  | Assign sx se, Assign tx te =>
    if md $? tx then None
                     (* ^-- Give up if the assigned variable is already
                      *     different between the two sides. *)
         else if cmd_eq_dec s t
              then if arithNotReading se md
                   then Some md
                   else None
                   (* ^-- Since the commands are the same, we succeed if the
                    *     expression being assigned only uses variables that the
                    *     two sides agree on. *)
              else None
  | Nop, Assign x (Const n) =>
    if md $? x then None else Some (md $+ (x, n))
    (* ^-- A new variable to disagree on!  The right side has the assignment,
     * but the left doesn't. *)
  | Assign x (Const n), Nop =>
    (* Instead of returning [md $- x], we maintain the maydiff set. Now the
     * validator rejects some valid programs, but returning [md $- x] makes the
     * correctness proof difficult, so we do this to adjust the difficulty! *)
    match md $? x with
    | Some n' => if n ==n n' then Some md else None
    | None => None
    end
  | Sequence s1 s2, Sequence t1 t2 =>
    match validator' s1 t1 md with
    | None => None
    | Some md1 => validator' s2 t2 md1
    end
  | If se sc1 sc2, If te tc1 tc2 =>
    (* Dealing with branches/loops is also difficult; we give up all related
     * optimizations such as loop-invariant code motion or branch code
     * motion. *)
    match validator' sc1 tc1 md, validator' sc2 tc2 md with
     | Some _, Some _ => if cmd_eq_dec s t
                         then if cmdNotReading s md
                              then Some md
                              else None
                         else None
     | _,_ => None
     end
  | While se sc, While te tc =>
    match validator' sc tc md with
    | Some _ =>  if cmd_eq_dec s t then if
                     arithNotReading se md
                   then Some md else None
                 else None
    | _ => None
    end
  | Output se, Output te =>
    if arith_eq_dec se te
    then if arithNotReading se md
         then Some md
         else None
    else None
  | _, _ => None
  end.

Definition validator (s t: cmd) :=
  match validator' s t $0 with
  | Some _ => true
  | _ => false
  end.

(* Here is a simple example source program to check our validator successfully 
 * passes the generated hint and target programs. *)
Example example_source :=
  "y" <- 1 ;;
  when "y" then
    Output 2
  else
    Output 3
  done ;;
  "x" <- 4 ;;
  Output 5.

(* Here's a tricky way to run the optimization using tactics. *)
Theorem run_example : constAssignCodeMotion example_source <> (Skip, Skip).
Proof.
  simplify.
  (* At this point, the result is displayed within the goal. *)
  equality.
Qed.

Example validator_seems_good :
  let (hint, target) := constAssignCodeMotion example_source in
  validator hint target = true.
Proof.
  unfold validator; simplify; equality.
Qed.

(** Now you are asked to prove the correctness of the validator. *)
Module Type S.
  Axiom validator_ok :
    forall v s t, validator s t = true -> (v, s) =| (v, t).
End S.


(* Our solution winds up using these two lemmas from Frap. *)
Check join_idempotent.
Check includes_refl.

(* Below we provide some lemmas and a normal simulation relation for our 
 * new language (where [Nop] is added). You are encouraged to actively use them
 * to make your life easier. :-) *)

Theorem skip_or_step :
  forall v c, c = Skip \/ exists v' l c', cstep (v, c) l (v', c').
Proof.
  induct c; simplify; first_order; subst;
    try match goal with
        | [ H : cstep _ _ _ |- _ ] => invert H
        end;
    try match goal with
        | [ |- context[cstep (?v, If ?e _ _)] ] => cases (interp e v ==n 0)
        | [ |- context[cstep (?v, While ?e _)] ] => cases (interp e v ==n 0)
        end; eauto 10.
Qed.

Theorem plug_function :
  forall C c1 c2,
    plug C c1 c2 ->
    forall c2', plug C c1 c2' -> c2 = c2'.
Proof.
  induct 1; invert 1; eauto.
  apply IHplug in H5.
  equality.
Qed.

Lemma peel_cseq :
  forall C1 C2 c (c1 c2 : cmd),
    C1 = C2 /\ c1 = c2 -> CSeq C1 c = CSeq C2 c /\ c1 = c2.
Proof.
  equality.
Qed.

Hint Resolve peel_cseq.

Lemma plug_deterministic :
  forall v C c1 c2,
    plug C c1 c2 ->
    forall l vc1,
      step0 (v, c1) l vc1 ->
      forall C' c1',
        plug C' c1' c2 ->
        forall l' vc1',
          step0 (v, c1') l' vc1' -> C' = C /\ c1' = c1.
Proof.
  induct 1; invert 1; invert 1; invert 1; auto;
    try match goal with
        | [ H : plug _ _ _ |- _ ] => invert1 H
        end; eauto.
Qed.

Lemma deterministic0 :
  forall vc l vc',
    step0 vc l vc' ->
    forall l' vc'', step0 vc l' vc'' -> l = l' /\ vc'' = vc'.
Proof.
  invert 1; invert 1; simplify; propositional.
Qed.

Theorem deterministic :
  forall vc l vc',
    cstep vc l vc' ->
    forall l' vc'', cstep vc l' vc'' -> l = l' /\ vc' = vc''.
Proof.
  invert 1; invert 1; simplify.
  eapply plug_deterministic in H0; eauto.
  invert H0.
  eapply deterministic0 in H1; [|exact H6].
  propositional; subst; auto.
  invert H0.
  eapply plug_function in H2; [|exact H9].
  equality.
Qed.

Section simulation.
  Variable R : valuation * cmd -> valuation * cmd -> Prop.

  Hypothesis one_step :
    forall vc1 vc2,
      R vc1 vc2 -> forall vc1' l,
        cstep vc1 l vc1' ->
        exists vc2', cstep vc2 l vc2' /\ R vc1' vc2'.

  Hypothesis agree_on_termination : forall v1 v2 c2, R (v1, Skip) (v2, c2) -> c2 = Skip.

  Lemma simulation_fwd' :
    forall vc1 ns,
      generate vc1 ns ->
      forall vc2, R vc1 vc2 -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc2.
    apply agree_on_termination in H; subst.
    auto.

    eapply one_step in H; eauto.
    first_order.
    eauto.

    eapply one_step in H1; eauto.
    first_order.
    eauto.
  Qed.

  Theorem simulation_fwd : forall vc1 vc2, R vc1 vc2 -> vc1 <| vc2.
  Proof.
    unfold traceInclusion; eauto using simulation_fwd'.
  Qed.

  Lemma simulation_bwd' :
    forall vc2 ns, generate vc2 ns -> forall vc1, R vc1 vc2 -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    auto.
    eapply one_step in H; eauto.
    first_order.
    invert H.
    invert H4.
    invert H5.
    
    cases vc1; cases vc.
    assert (c = Skip \/ exists v' l c', cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
    invert H.
    invert H3.
    invert H4.
    specialize (one_step H1 H2).
    first_order.
    eapply deterministic in H; eauto.
    propositional; subst.
    eauto.

    cases vc1; cases vc.
    assert (c = Skip \/ exists v' l c', cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
    invert H.
    invert H3.
    invert H4.
    specialize (one_step H1 H2).
    first_order.
    eapply deterministic in H; eauto.
    propositional; subst.
    eauto.
  Qed.

  Theorem simulation_bwd : forall vc1 vc2, R vc1 vc2 -> vc2 <| vc1.
  Proof.
    unfold traceInclusion; eauto using simulation_bwd'.
  Qed.

  Theorem simulation : forall vc1 vc2, R vc1 vc2 -> vc1 =| vc2.
  Proof.
    simplify; split; auto using simulation_fwd, simulation_bwd.
  Qed.

End simulation.
