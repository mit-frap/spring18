(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 9 *)

Require Import Frap.

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu)
 * Ben Sherman (sherman@csail.mit.edu)
 * Adam Chlipala (adamc@csail.mit.edu) 
 *)

Set Implicit Arguments.

(** Data Abstraction via Contextual Equivalence *)

(* Here's a typical student reaction to the content on type systems from a
 * course like this one:
 *   "Yeah, it's good to prove that programs don't crash, but it's so much more
 *   exciting to prove that programs actually return correct answers, and we've
 *   seen plenty of techniques for that already (and will see more in the rest
 *   of the course).  Can we get this type-system stuff over with so we can move
 *   on to the _important_ stuff?"
 *
 * However, it turns out that type systems are very handy for formalizing a very
 * thorough kind of correctness condition for code libraries!  In particular,
 * let's return to _abstract data types_, which we first studied in Pset 4,
 * where we define a formal _interface_ for a data structure and prove that some
 * _implementation_ satisfies the interface.  Recall that Pset 4 asked you to
 * prove a selection of algebraic laws for some implementation.  But how do we
 * know that we picked the right set of laws?  What if we could show that the 
 * laws were somehow _complete_ for the interface, prescribing _all possible
 * behaviors_ of the abstract data type?
 *
 * The concept of _contextual equivalence_ formalizes that idea in a general
 * way.  Say we have a simple _reference implementation_ of an abstract data
 * type, and we also have a more fancy, optimized implementation.  Consider all
 * possible _client code_ that imports a library for this data structure.  It
 * doesn't known which of the two it will be linked with; it must work for both.
 * The two libraries are _contextually equivalent_ if no client code can tell
 * them apart, so, say, the client code computes the same answer regardless.
 *
 * It is crucial to formalize the library interface with a type, so that we can
 * constraint which client programs are valid.  That's exactly what we do in
 * this pset, in addition to introducing a method for proving contextual
 * equivalence. *)


(** * Language syntax, semantics, and typing *)

(* Here's our base language, which only uses features familiar from the last
 * pset and class examples. *)

Inductive exp  :=
(* First, the basic STLC ingredients *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)
(* Constants and basic arithmetic *)
| Const (n : nat)
| Add (e1 e2 : exp)
(* And pairs; they're less general than tuples in the previous problem set. *)
| Pair (e1 e2 : exp)
| Fst (e : exp)
| Snd (e : exp).

Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VConst : forall n, value (Const n)
| VPair : forall e1 e2, value e1 -> value e2 -> value (Pair e1 e2).

Hint Constructors value.
Hint Extern 1 (value _) => constructor.

(* Syntax of types *)
Inductive type :=
| Nat
| Fun (dom ran : type)
| Prod (t1 t2 : type)
(* We have a new type, called [AbsT], representing the abstract type.  When
 * implementing a certain data structure, we don't want to expose how it is
 * implemented by giving actual types of the implementation.  Instead, we just
 * claim that the implementation satisfies an abstract type.  Clients use it
 * without knowing the actual implementation, while the implementer should check
 * the type without any abstraction. *)
| AbsT.

(* Fancy notations *)
Coercion Var : var >-> exp.
Notation "\ x , e" := (Abs x e) (at level 51).
Infix "@" := App (at level 49, left associativity).
Coercion Const : nat >-> exp.
Infix "^+^" := Add (at level 50).
Notation "@( e1 , e2 )" := (Pair e1 e2) (at level 51).

Infix "-->" := Fun (at level 60, right associativity).
Notation "t1 ^*^ t2" := (Prod t1 t2) (at level 61).

(** A target ADT: simple counters *)
(* We want to prove that two simple counter implementations are
 * _contextually equivalent_, using a logical relation.  Below we can see two
 * implementations: [counter_impl1] is just using a single number to count.
 * Note that the counter exposes two distinct methods for incrementing its
 * value.  They should do the same work from the perspective of the external
 * world.  [counter_impl2] makes each increment method increment a different
 * private number, storing the two numbers within a pair. *)

Definition counter_type : type :=
  (AbsT ^*^ (* The internal counter value is abstracted; clients cannot use this
             * value.  In Java terms, think of this type part as a private
             * field. *)
  (AbsT --> Nat ^*^  (* Method to get the actual counter value *)
  (AbsT --> AbsT ^*^ (* Method to increase the counter value *)
   AbsT --> AbsT))). (* Second method to increase the counter value *)

(* Here's the simple reference implementation. *)
Definition counter_val1 := Const 0.
Definition counter_get1 := \"x", "x".
Definition counter_inc11 := \"x", "x" ^+^ 1.
Definition counter_inc21 := \"x", "x" ^+^ 1.
Definition counter_impl1 :=
  @(counter_val1, @(counter_get1, @(counter_inc11, counter_inc21))).

(* And here's the more convoluted two-counter version. *)
Definition counter_val2 := @(0, 0).
Definition counter_get2 := \"xy", (Fst "xy") ^+^ (Snd "xy").
Definition counter_inc12 := \"xy", @( (Fst "xy") ^+^ 1, Snd "xy" ).
Definition counter_inc22 := \"xy", @( Fst "xy", (Snd "xy") ^+^ 1 ).
Definition counter_impl2 :=
  @(counter_val2, @(counter_get2, @(counter_inc12, counter_inc22))).

(* Intuitively, client code can't distinguish these two versions, if it doesn't
 * know how the abstract type is implemented.  In this pset, we will work up to
 * proving that property for this example, in the process developing formal
 * machinery also applicable to many related examples.  (And all of this
 * generalizes to fancier languages with more expressive typing, though the
 * details are out of scope for the assignment.) *)

(* Some routine definitions again! They should should now be very familiar, so
 * it's safe for you to skim through quickly. But it is recommended to pay
 * attention to the typing rules, since now there is a new concept with
 * _abstract types_. *)

Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e => Abs y (if y ==v x then e else subst e1 x e)
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | Const n => Const n
  | Add e1' e2' => Add (subst e1 x e1') (subst e1 x e2')
  | Pair e1' e2' => Pair (subst e1 x e1') (subst e1 x e2')
  | Fst e => Fst (subst e1 x e)
  | Snd e => Snd (subst e1 x e)
  end.

(* We use a big-step semantics for this problem set. *)
Inductive eval : exp -> exp -> Prop :=
| BigAbs : forall x e,
    eval (Abs x e) (Abs x e)
| BigApp : forall e1 x e1' e2 v2 v,
    eval e1 (Abs x e1') ->
    eval e2 v2 ->
    eval (subst v2 x e1') v ->
    eval (App e1 e2) v
| BigConst : forall n,
    eval (Const n) (Const n)
| BigAdd : forall e1 e2 n1 n2,
    eval e1 (Const n1) ->
    eval e2 (Const n2) ->
    eval (Add e1 e2) (Const (n1 + n2))
| BigPair : forall e1 e2 v1 v2,
    eval e1 v1 ->
    eval e2 v2 ->
    eval (Pair e1 e2) (Pair v1 v2)
| BigFst : forall e v1 v2,
    eval e (Pair v1 v2) ->
    eval (Fst e) v1
| BigSnd : forall e v1 v2,
    eval e (Pair v1 v2) ->
    eval (Snd e) v2.

Hint Constructors eval.

(* Here is an expression-typing relation with a single abstract type.  Clients
 * use [hasty] with the first argument as [None], where the actual type is not
 * exposed.  On the contrary, the implementation side uses [hasty] with the
 * first argument as [Some abst], where [abst] is the actual type used to
 * implement the data structure. *)
Inductive hasty : option type -> fmap var type -> exp -> type -> Prop :=
| HtVar : forall abs G x t,
    G $? x = Some t ->
    hasty abs G (Var x) t

(* Now there are two typing rules for [Abs]. The first one is as usual, but
 * requires argument type not equal to [AbsT]. It is for ensuring that [G]
 * always stores the actual type information, not the abstract one. *)
| HtAbs : forall abs G x e1 t1 t2,
    hasty abs (G $+ (x, t1)) e1 t2 ->
    t1 <> AbsT ->
    hasty abs G (Abs x e1) (Fun t1 t2)
(* The second typing rule for [Abs] is for the case when the argument has an
 * abstract type [AbsT]. In this case, we store the actual type by referring to
 * [Some abst]. *)
| HtAbsAbs : forall abst G x e1 t2,
    hasty (Some abst) (G $+ (x, abst)) e1 t2 ->
    hasty (Some abst) G (Abs x e1) (Fun AbsT t2)

(* Then the next few rules are standard, with [abs] threaded through. *)
| HtApp : forall abs G e1 e2 t1 t2,
    hasty abs G e1 (Fun t1 t2) ->
    hasty abs G e2 t1 ->
    hasty abs G (App e1 e2) t2
| HtConst : forall abs G n,
    hasty abs G (Const n) Nat
| HtAdd : forall abs G e1 e2,
    hasty abs G e1 Nat ->
    hasty abs G e2 Nat ->
    hasty abs G (Add e1 e2) Nat
| HtPair : forall abs G e1 e2 t1 t2,
    hasty abs G e1 t1 ->
    hasty abs G e2 t2 ->
    hasty abs G (Pair e1 e2) (Prod t1 t2)
| HtFst : forall abs G e t1 t2,
    hasty abs G e (Prod t1 t2) ->
    hasty abs G (Fst e) t1
| HtSnd : forall abs G e t1 t2,
    hasty abs G e (Prod t1 t2) ->
    hasty abs G (Snd e) t2

(* Finally, one more rule for the abstract type.  [AbsT] can be instantiated to
 * the actual type only if the actual type is provided, meaning this typing
 * rule is for the implementer. *)
| HtAbsT1 : forall abst G e,
    hasty (Some abst) G e abst ->
    hasty (Some abst) G e AbsT.

Hint Constructors hasty.


(** * Logical relation *)

(* How can we prove that two expressions are contextually equivalent?  That is,
 * how can we show that no well-typed client program could tell them apart?
 * Reasoning explicitly about every possible client program would be a lot of
 * work!  Instead, here's a fun idea from the literature, _logical relations_,
 * that gives a straightforward condition where we avoid reasoning about client
 * programs explicitly.  The key distinguishing property of logical relations is
 * that they are defined by recursion on type structure, helping explain why use
 * of a type system is so critical to the approach. *)

Section LogicalRel.
  Variables (abst1 abst2 : type)
            (value_rel_abs: exp -> exp -> Prop).
  (* The relation is parameterized over two different implementation types for
   * the abstract type, along with a primitive relation for saying when two
   * "private field" values for the two sides should be considered to represent
   * the same abstract value. *)

  (* This relation says when two expressions are equivalent at some type.  It is
   * parameterized on the relation to use to compare two *values* at a type. *)
  Definition exp_rel' (v_rel: type -> exp -> exp -> Prop)
             (t: type) (e1 e2: exp): Prop :=
    (* First, the two expressions really have the claimed type, in the
     * corresponding implementations of the abstract type. *)
    hasty (Some abst1) $0 e1 t /\ hasty (Some abst2) $0 e2 t /\

    (* Then, both evaluate to values that are themselves related. *)
    exists v1 v2, eval e1 v1 /\ eval e2 v2 /\
                  v_rel t v1 v2.

  (* Now we go methodically through the types, explaining what equivalence means
   * for each one. *)
  Fixpoint value_rel (t: type) (e1 e2: exp) : Prop :=
    match t with
    | Nat =>
      (* An easy case: numbers are equivalent when equal. *)
      match e1, e2 with
      | Const n1, Const n2 => n1 = n2
      | _, _ => False
      end

    | Prod t1 t2 =>
      (* Another pretty easy case: equivalent pairs have equivalent
       * components. *)
      match e1, e2 with
      | Pair v11 v12, Pair v21 v22 =>
        value_rel t1 v11 v21 /\ value_rel t2 v12 v22
      | _, _ => False
      end

    | AbsT =>
      (* The abstract type picks up whatever [value_rel_abs] relation we
       * chose, additionally requiring that the two expressions are
       * well-typed. *)
      hasty (Some abst1) $0 e1 AbsT /\
      hasty (Some abst2) $0 e2 AbsT /\
      value_rel_abs e1 e2

    | Fun t' t'' =>
      (* Now the signature case of logical relations: "the two functions map
       * equivalent inputs to equivalent outputs." *)
      match e1, e2 with
      | Abs x1 e1', Abs x2 e2' =>
        hasty (Some abst1) $0 e1 t /\ hasty (Some abst2) $0 e2 t /\
        forall v1 v2, (* <-- These are the two equivalent inputs! *)
          hasty (Some abst1) $0 v1 t' -> hasty (Some abst2) $0 v2 t' ->
          value_rel t' v1 v2 (* ...and this hypothesis says so. *) ->
          exp_rel' value_rel t'' (subst v1 x1 e1') (subst v2 x2 e2')
                   (* These substitution results are the equivalent outputs. *)
      | _, _ => False
      end
    end.

  Definition exp_rel := exp_rel' value_rel.

  (* We also need to argue for equivalence of terms with free variables.
   * This relation formalizes it in terms of typing contexts [G].
   * Basically it says: "two expressions with free variables are equivalent iff
   * we get equivalent expressions by substituting equivalent values for all the
   * free variables." *)
  Definition g_rel (G: fmap var type) (g1 g2: fmap var exp) : Prop :=
    forall x,
      (* Any variable in [G] is mapped to equivalent values. *)
      (forall t,
          G $? x = Some t ->
          exists v1 v2, g1 $? x = Some v1 /\ g2 $? x = Some v2 /\ value_rel t v1 v2) /\

      (* Any variable _not_ in [G] is mapped to nothing. *)
      (G $? x = None -> g1 $? x = None /\ g2 $? x = None).

  (* Here we define substitution for several variables at once. *)
  Fixpoint substs (g : fmap var exp) (e : exp) : exp :=
    match e with
    | Var y =>
      match g $? y with
      | Some v => v
      | _ => Var y
      end
    | Abs y e' => Abs y (substs (g $- y) e')
    | App e' e'' => App (substs g e') (substs g e'')
    | Const n => Const n
    | Add e' e'' => Add (substs g e') (substs g e'')
    | Pair e' e'' => Pair (substs g e') (substs g e'')
    | Fst e' => Fst (substs g e')
    | Snd e' => Snd (substs g e')
    end.

  (* Finally, the most general logical relation, for expressions that are
   * allowed to contain free variables *)
  Definition logical_rel (G: fmap var type) (e1 e2: exp) (t: type) :=
    hasty (Some abst1) G e1 t /\ hasty (Some abst2) G e2 t /\
    forall g1 g2,
      g_rel G g1 g2 ->
      exp_rel t (substs g1 e1) (substs g2 e2).
End LogicalRel.


(** * Returning to the example of counters *)

(* Let's demonstrate this machinery by proving that our two counter
 * implementations inhabit the appropriate logical relation.  We'll use this
 * relation to capture when the "private fields" on the two sides are
 * equivalent. *)
Inductive value_rel_counters : exp -> exp -> Prop :=
| Vrc : forall c inc dec,
    c = inc + dec ->
    value_rel_counters c (@(inc, dec)).

Hint Constructors value_rel_counters.

Hint Extern 1 (_ $? _ = Some _) => simplify; reflexivity.

(* And here's how we prove the relation. *)
Theorem counter_impls_related:
  value_rel Nat (Nat ^*^ Nat) value_rel_counters
            counter_type counter_impl1 counter_impl2.
Proof.
  (* We unfold some symbols and reveal a type-specialized notion of
   * equivalence! *)
  simplify.
  (* Here we see a giant conjunction. Most of the conjuncts are
   * typing requirements, which are easy to discharge either with [eauto]
   * or by applying constructors. *)
  propositional; eauto 15;
    try solve[apply HtAbsAbs; eauto 10]; try solve[repeat constructor].
  (* The three remaining conjuncts are conditions on the three methods of
   * the counter.
   *)
  - (* First is the "get" method.  We have that the two sides have equivalent
     * private-field values, and we must show that the two "get" methods will
     * therefore return equivalent results. *)
    invert H4. constructor. constructor. eauto 10.
    split.  eauto 10.
    do 2 eexists. split.
    repeat constructor. split.
    repeat econstructor.
    constructor.
  - (* Next is the "inc1" method. *)
    invert H4. constructor. constructor. eauto 10.
    split.  eauto 10.
    do 2 eexists. split.
    repeat constructor. split.
    repeat econstructor.
    constructor. eauto 10.
    split. eauto 10. constructor. linear_arithmetic.
  - (* Finally, the "inc2" method. *)
    invert H4. constructor. constructor. eauto 10.
    split.  eauto 10.
    do 2 eexists. split.
    repeat constructor. split.
    repeat econstructor.
    constructor. eauto 10.
    split. eauto 10. constructor. linear_arithmetic.
Qed.

(* Believe it or not, that condition implies contextual equivalence of the two
 * implementations... but we'll need to spend the rest of the pset proving it.
 * ;-)  We should at least prove a more general theorem that applies to many
 * other abstract data types, too. *)


Module Type S.
  (* We ask you to prove the "fundamental property" of the logical relation. It
   * seems very weak (every value is related to itself?  sounds obvious,
   * right?), but it's actually strong enough to prove the contextual equality.
   * According to the definition of [logical_rel], [G] can be regarded as a
   * "placeholder" to substitute two values in the logical relation, where the
   * values may differ! *)
  Axiom logical_rel_fundamental:
    forall abst1 abst2 (value_rel_abs: exp -> exp -> Prop),
      (forall v1 v2, value_rel_abs v1 v2 -> value v1 /\ value v2) ->
      abst1 <> AbsT ->
      abst2 <> AbsT ->
      forall e G t,
        hasty None G e t ->
        logical_rel abst1 abst2 value_rel_abs G e e t.

  (* The following corollary should be quite easy to prove, using
   * [logical_rel_fundamental]. *)
  Axiom counter_impls_equiv:
    forall x e,
      hasty None ($0 $+ (x, counter_type)) e Nat ->
      exists n : nat,
        eval (subst counter_impl1 x e) n /\ eval (subst counter_impl2 x e) n.
End S.


(** We provide some lemmas which may help you prove the theorems. *)

Lemma value_eval : forall v, value v -> eval v v.
Proof.
  induct 1; eauto.
Qed.

Hint Resolve value_eval.

Lemma eval_value : forall e v, eval e v -> value v.
Proof.
  induct 1; eauto.
  - invert IHeval; eauto.
  - invert IHeval; eauto.
Qed.

Hint Resolve eval_value.

Hint Extern 1 (_ <> _) => equality.

(* [adds] is a binary operation for [fmap]s, doing a merge between two maps
 * where the second map takes priority for a common key. It should be useful
 * for merging two type environments.
 *)
Section Adds.

  Definition adds {A B} (m1 m2: fmap A B) :=
    merge (fun v1 v2 => match v2 with
                        | Some _ => v2
                        | _ => v1
                        end) m1 m2.

  Lemma adds_empty1:
    forall {B} (m: fmap var B), adds $0 m = m.
  Proof.
    intros; unfold adds.
    rewrite merge_empty1; auto.
    intros; cases x; auto.
  Qed.

  Lemma adds_empty2:
    forall {B} (m: fmap var B), adds m $0 = m.
  Proof.
    intros; unfold adds.
    rewrite merge_empty2; auto.
  Qed.

  Lemma adds_add:
    forall {B} (m1 m2: fmap var B) x v,
      adds m1 m2 $+ (x, v) = adds m1 (m2 $+ (x, v)).
  Proof.
    intros; apply fmap_ext; intros.
    cases (x ==v k); subst; simplify.
    - unfold adds; rewrite lookup_merge; simplify; auto.
    - unfold adds; rewrite lookup_merge; simplify; auto.
  Qed.

  Lemma adds_add2:
    forall {B} (m: fmap var B) x v,
      adds ($0 $+ (x, v)) (m $- x) = m $+ (x, v).
  Proof.
    intros; apply fmap_ext; intros.
    cases (x ==v k); subst; simplify.
    - unfold adds; rewrite lookup_merge; simplify; auto.
    - unfold adds; rewrite lookup_merge; simplify.
      cases (m $? k); equality.
  Qed.

  Lemma adds_remove:
    forall {B} (m1 m2: fmap var B) x v,
      adds (m1 $+ (x, v)) (m2 $- x) = adds m1 (m2 $+ (x, v)).
  Proof.
    intros; apply fmap_ext; intros.
    unfold adds; rewrite 2! lookup_merge.
    cases (x ==v k); subst; simplify; auto.
  Qed.

End Adds.

(* Some facts about [hasty] *)
Section HasTyFacts.

  Lemma hasty_Nat_value:
    forall abst G e,
      hasty abst G e Nat ->
      value e ->
      exists n, e = Const n.
  Proof.
    induct 1; simplify; eauto;
      try match goal with
          | [H: value _ |- _] => invert H
          end.
  Qed.

  (* Note that a different type [t1'] is used when the type information is 
   * stored.  It's due to the type instantiation that [hasty] does. *)
  Lemma hasty_Fun_value:
    forall abst G e t1 t2,
      hasty abst G e (Fun t1 t2) ->
      value e ->
      exists x1 t1' e2,
        e = Abs x1 e2 /\ hasty abst (G $+ (x1, t1')) e2 t2.
  Proof.
    induct 1; simplify; eauto;
      try match goal with
          | [H: value _ |- _] => invert H
          end.
  Qed.

  Lemma hasty_Prod_value:
    forall abst G e t1 t2,
      hasty abst G e (Prod t1 t2) ->
      value e ->
      exists e1 e2,
        e = @(e1, e2) /\ hasty abst G e1 t1 /\ hasty abst G e2 t2.
  Proof.
    induct 1; simplify; eauto;
      try match goal with
          | [H: value _ |- _] => invert H
          end.
  Qed.

  Lemma hasty_weakening:
    forall abst G e t,
      hasty abst G e t ->
      forall G',
        (forall x t, G $? x = Some t -> G' $? x = Some t) ->
        hasty abst G' e t.
  Proof.
    induct 1; simplify; eauto.
    - constructor; auto.
      apply IHhasty; intros.
      cases (x ==v x0); simplify; propositional; auto.
    - apply HtAbsAbs.
      apply IHhasty; intros.
      cases (x ==v x0); simplify; propositional; auto.
  Qed.

  Corollary hasty_weakening_empty:
    forall abst e t,
      hasty abst $0 e t ->
      forall G,
        hasty abst G e t.
  Proof.
    intros; apply hasty_weakening with (G:= $0); auto.
  Qed.
            
  Lemma hasty_weakening_abst:
    forall G e t, hasty None G e t ->
                  forall abst,
                    hasty (Some abst) G e t.
  Proof.
    induct 1; simplify; eauto.
  Qed.

  (* Closedness of expressions. 
   * [e] is closed iff it does not have any free variables.
   * We define a more general version that uses argument [vs] to express which
   * free variables are allowed. *)
  Fixpoint closed (e: exp) (vs: set var) :=
    match e with
    | Var x => x \in vs
    | Abs x e' => closed e' (vs \cup {x})
    | App e' e'' => closed e' vs /\ closed e'' vs
    | Const _ => True
    | Add e' e'' => closed e' vs /\ closed e'' vs
    | Pair e' e'' => closed e' vs /\ closed e'' vs
    | Fst e' => closed e' vs
    | Snd e' => closed e' vs
    end.

  (* When [e] is type-checked, then it's closed. *)
  Lemma hasty_closed:
    forall abst G e t,
      hasty abst G e t ->
      closed e (dom G).
  Proof.
    induct 1; simplify; eauto.
    eapply lookup_Some_dom; eauto.
  Qed.

  (* When [e] is closed, then it's not affected by substitutions. *)
  Lemma closed_subst:
    forall e (G: fmap var type),
      closed e (dom G) ->
      forall v x,
        G $? x = None ->
        subst v x e = e.
  Proof.
    induct e; simplify; try (propositional; f_equal; eauto; fail).
    - cases (x ==v x0); subst; propositional.
      apply lookup_None_dom in H0; propositional.
    - cases (x ==v x0); subst; propositional.
      f_equal.
      apply IHe with (G:= G $+ (x, Nat)); simplify; auto.
  Qed.

  (* Here's a special case of the above, for truly closed expressions. *)
  Lemma value_hasty_closed:
    forall e abst t,
      hasty abst $0 e t ->
      forall x v,
        subst v x e = e.
  Proof.
    intros.
    apply closed_subst with (G := $0).
    - eapply hasty_closed. eauto.
    - simplify; equality.
  Qed.

End HasTyFacts.

Hint Immediate hasty_weakening hasty_weakening_abst.

(* Some facts about [substs] *)
Section Substs.

  Lemma substs_empty:
    forall e, substs $0 e = e.
  Proof.
    induct e; simplify; eauto; try (f_equal; auto).
    replace (empty string exp $- x) with (empty string exp); auto.
    clear IHe; apply fmap_ext; simplify.
    cases (x ==v k); subst; simplify; equality.
  Qed.

  Lemma substs_single:
    forall x v e,
      substs ($0 $+ (x, v)) e = subst v x e.
  Proof.
    induct e; simplify; eauto; try (f_equal; auto).
    - cases (x ==v x0); subst; simplify.
      + cases (x0 ==v x0); equality.
      + cases (x0 ==v x); equality.
    - cases (x ==v x0); subst; simplify.
      + cases (x0 ==v x0); try equality.
        rewrite <-substs_empty.
        f_equal.
        apply fmap_ext; simplify.
        cases (x0 ==v k); subst; simplify; equality.
      + cases (x0 ==v x); subst; simplify; try equality.
        replace ($0 $+ (x, v) $- x0) with ($0 $+ (x, v)); auto.
        apply fmap_ext; simplify.
        cases (x ==v k); subst; simplify; try equality.
        cases (x0 ==v k); subst; simplify; try equality.
  Qed.

End Substs.

(* Some facts about logical relations *)
Section LogicalRelFacts.
  Variables (abst1 abst2 : type)
            (value_rel_abs: exp -> exp -> Prop).
  Hypotheses (Hvr: forall v1 v2, value_rel_abs v1 v2 -> value v1 /\ value v2).
  
  Lemma value_rel_value:
    forall t v1 v2,
      value_rel abst1 abst2 value_rel_abs t v1 v2 ->
      value v1 /\ value v2.
  Proof.
    induct t.
    - simplify.
      cases v1; try invert H.
      cases v2; try invert H.
      auto.
    - simplify.
      cases v1; try invert H.
      cases v2; try invert H.
      auto.
    - simplify.
      cases v1; try invert H.
      cases v2; try invert H.
      specialize (IHt1 _ _ H0).
      specialize (IHt2 _ _ H1).
      first_order; constructor; auto.
    - first_order.
  Qed.

  Lemma value_rel_hasty:
    forall t v1 v2,
      value_rel abst1 abst2 value_rel_abs t v1 v2 ->
      hasty (Some abst1) $0 v1 t /\ hasty (Some abst2) $0 v2 t.
  Proof.
    induct t; simplify; auto.
    - cases v1; try invert H.
      cases v2; try invert H.
      auto.
    - cases v1; try invert H.
      cases v2; try invert H.
      propositional; subst.
    - cases v1; try invert H.
      cases v2; try invert H.
      specialize (IHt1 _ _ H0).
      specialize (IHt2 _ _ H1).
      first_order; constructor; auto.
    - first_order.
  Qed.

  Lemma value_rel_implies_exp_rel:
    forall t v1 v2,
      value_rel abst1 abst2 value_rel_abs t v1 v2 ->
      exp_rel abst1 abst2 value_rel_abs t v1 v2.
  Proof.
    unfold exp_rel, exp_rel'; intros; repeat split.
    - apply value_rel_hasty in H; propositional.
    - apply value_rel_hasty in H; propositional.
    - exists v1, v2; repeat split; auto.
      + apply value_rel_value in H.
        apply value_eval; propositional.
      + apply value_rel_value in H.
        apply value_eval; propositional.
  Qed.

End LogicalRelFacts.
