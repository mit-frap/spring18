(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 8 *)

Require Import Frap.

(* Authors: 
 * Peng Wang (wangpeng@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu) 
 *)

Set Implicit Arguments.

(** * Subtyping *)

(* We can't resist fitting in another crucial aspect of type systems:
 * *subtyping*, which formalizes when any value of one type should also be
 * permitted as a value of some other type.  Languages like Java include
 * *nominal* subtyping, based on declared type hierarchies.  Instead, here we
 * will prove soundness of *structural* subtyping, whose rules we'll get to
 * shortly.  The simply typed lambda calculus will be our starting point. *)

(* Expression syntax *)
Inductive exp  :=
(* Our old friends from simply typed lambda calculus *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)

(* New features, surrounding *tuple* types, which build composite types out of
 * constituents *)
| TupleNil
(* Empty tuple (no fields *)
| TupleCons (e1 e2 : exp)
(* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
 * nested tuple with all the remaining fields *)
| Proj (e : exp) (n : nat)
(* Grab the [n]th field of tuple [e]. *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VTupleNil : value TupleNil
| VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
.

(* The next few definitions are quite routine and should be safe to skim through
 * quickly; but start paying more attention when we get to defining the
 * subtyping relation! *)

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | TupleNil => TupleNil
  | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
  | Proj e2' n => Proj (subst e1 x e2') n
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| TupleCons1 (C : context) (e2 : exp)
| TupleCons2 (v1 : exp) (C : context)
| Proj1 (C : context) (n : nat)
.

(* Plugging an expression into a context *)
Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
| PlugTupleCons1 : forall C e e' e2,
    plug C e e'
    -> plug (TupleCons1 C e2) e (TupleCons e' e2)
| PlugTupleCons2 : forall v1 C e e',
    value v1
    -> plug C e e'
    -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
| PlugProj : forall C e e' n,
    plug C e e'
    -> plug (Proj1 C n) e (Proj e' n)
.

(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)

(* To project field 0 out of a tuple, just grab the first component. *)
| Proj0 : forall v1 v2,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) 0) v1

(* To project field [1+n], drop the first component and continue with [n]. *)
| ProjS : forall v1 v2 n,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
.

Inductive step : exp -> exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

Definition trsys_of (e : exp) :=
  {| Initial := {e}; Step := step |}.

(* Syntax of types *)
Inductive type :=
| Fun (dom ran : type)
| TupleTypeNil
| TupleTypeCons (t1 t2 : type)
.

Inductive subtype : type -> type -> Prop :=

(* Two function types are related if their components are related pairwise.
 * Counterintuitively, we *reverse* the comparison order for function domains!
 * It may be worth working through some examples to see why the relation would
 * otherwise be unsound. *)
| StFun : forall t1' t2' t1 t2,
    subtype t1 t1' ->
    subtype t2' t2 ->
    subtype (Fun t1' t2') (Fun t1 t2)

(* An empty tuple type is its own subtype. *)
| StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

(* However, a nonempty tuple type is also a subtype of the empty tuple type.
 * This rule gives rise to *width* subtyping, where we can drop some fields of
 * a tuple type to produce a subtype. *)
| StTupeNilCons : forall t1 t2,
    subtype (TupleTypeCons t1 t2) TupleTypeNil

(* We also have *depth* subtyping: we can replace tuple components with
 * subtypes. *)
| StTupleCons : forall t1' t2' t1 t2,
    subtype t1' t1 ->
    subtype t2' t2 ->
    subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
.

(* Here's a more compact notation for subtyping. *)
Infix "$<:" := subtype (at level 70).

Hint Constructors subtype.

(* Projecting out the nth field of a tuple type *)
Inductive proj_t : type -> nat -> type -> Prop :=
| ProjT0 : forall t1 t2,
    proj_t (TupleTypeCons t1 t2) 0 t1
| ProjTS : forall t1 t2 n t,
    proj_t t2 n t ->
    proj_t (TupleTypeCons t1 t2) (1 + n) t
.

(* Expression typing relation *)
Inductive hasty : fmap var type -> exp -> type -> Prop :=
| HtVar : forall G x t,
    G $? x = Some t ->
    hasty G (Var x) t
| HtAbs : forall G x e1 t1 t2,
    hasty (G $+ (x, t1)) e1 t2 ->
    hasty G (Abs x e1) (Fun t1 t2)
| HtApp : forall G e1 e2 t1 t2,
    hasty G e1 (Fun t1 t2) ->
    hasty G e2 t1 ->
    hasty G (App e1 e2) t2
| HtTupleNil : forall G,
    hasty G TupleNil TupleTypeNil
| HtTupleCons: forall G e1 e2 t1 t2,
    hasty G e1 t1 ->
    hasty G e2 t2 ->
    hasty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
| HtProj : forall G e n t t',
    hasty G e t' ->
    proj_t t' n t ->
    hasty G (Proj e n) t

(* This is the crucial rule: when an expression has a type, it also has any
 * supertype of that type.  We call this rule *subsumption*. *)
| HtSub : forall G e t t',
    hasty G e t' ->
    t' $<: t ->
    hasty G e t
.

Hint Constructors value plug step0 step proj_t hasty.

(* BEGIN handy tactic that we suggest for these proofs *)
Ltac t0 := match goal with
           | [ H : ex _ |- _ ] => invert H
           | [ H : _ /\ _ |- _ ] => invert H
           | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
           | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify

           | [ H : step _ _ |- _ ] => invert H
           | [ H : step0 _ _ |- _ ] => invert1 H
           | [ H : hasty _ _ _ |- _ ] => invert1 H
           | [ H : proj_t _ _ _ |- _ ] => invert1 H
           | [ H : plug _ _ _ |- _ ] => invert1 H
           | [ H : subtype _ _ |- _ ] => invert1 H
           | [ H : Some _ = Some _ |- _ ] => invert H
           end; subst.

Ltac t := simplify; subst; propositional; repeat (t0; simplify); try equality.
(* END handy tactic *)


Module Type S.
  (* Prove these two basic algebraic properties of subtyping. *)
  Axiom subtype_refl : forall t, t $<: t.
  Axiom subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.

  (* The real prize: prove soundness of this type system.
   * We suggest starting from a copy of the type-safety proof from the book's
   * LambdaCalculusAndTypeSoundness.v.  Essentially all of the lemmas from that
   * proof will be useful here, too, though some of their proofs need to
   * change. *)
  Axiom safety :
    forall e t,
      hasty $0 e t -> invariantFor (trsys_of e)
                                   (fun e' => value e'
                                              \/ exists e'', step e' e'').
End S.
