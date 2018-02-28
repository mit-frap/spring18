(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 4 *)

Require Import Frap Datatypes Orders.
Export Datatypes Orders.

(* Note: This problem set is significantly more open-ended than
 * previous problem sets in this class: proving theorems may require
 * first conceiving and proving many auxiliary lemmas. We highly
 * recommend getting started early on the problem set and taking
 * advantage of office hours. Additionally, we will provide hints
 * on the class website. You may wish to first attempt the problem
 * set without consulting the hints, but they are available if
 * you wish.
 *)

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu),
 * Benjamin Sherman (sherman@csail.mit.edu), 
 *)

(** * Correctness of Binary Search Trees (BSTs) *)

(* Here we prove some correctness theorems about binary search trees (BSTs),
 * a famous data structure for finite sets, allowing fast (log-time) lookup,
 * insertion, and deletion of items.  (Actually, we won't quite achieve
 * the worst-case log-time bound here, as we will ignore the need for balancing.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined, by proving 1) both functions preserve the BST 
 * invariant, and 2) relations between the two functions and a membership
 * checker.
 *)

(* We define a polymorphic datatype [t] by including OrderedType, defined in the
 * Coq standard library. [t] should be ordered, in order to define some BST
 * operations. See the ingredients of [OrderedType] by [Print OrderedType].
 *)
Include OrderedType.
(* Print OrderedType. *)

(* Trees (not BSTs yet!) are an inductive structure, where [Leaf] doesn't have any
 * items, whereas [Node] has an item and two subtrees.
 *)
Inductive tree :=
| Leaf
| Node (d : t) (l r : tree).

(* Then a singleton is just a node without subtrees. *)
Definition Singleton (v: t) := Node v Leaf Leaf.

(* In order to define the BST spec, we define some predicates:
 * [tree_forall] is a higher-order predicate that says that all
 * items in a tree satisfy a particular predicate. This is used
 * to define [tree_lt] and [tree_gt], which say that all items
 * are less than or greater than a given value, respectively.
 * Note that we reference a less-than comparison
 * [lt] associated with the type [t]. Also note that these are
 * recursive functions returning logical predicates, built with
 * the usual connectives.
 *
 * Note that, like the definitions of [sum] and [all] that we
 * gave in problem set 3, [simplify] will not directly
 * simplify some terms involving [tree_lt] and [tree_gt] since
 * they are defined in terms of [tree_forall], so you may want
 * to use the [unfold] tactic to unfold these definitions
 * if you want [simplify] to reduce them using the definition
 * of [tree_forall].
 *)

Fixpoint tree_forall (P : t -> Prop) (tr: tree) :=
  match tr with
  | Leaf => True
  | Node v ltr rtr => P v /\ tree_forall P ltr /\ tree_forall P rtr
  end.

Definition tree_lt (n: t) := tree_forall (fun v => lt v n).

Definition tree_gt (n: t) := tree_forall (fun v => lt n v).

(* Using [tree_lt] and [tree_gt], a predicate for BSTs is now defined naturally. *)
Fixpoint BST (tr: tree) :=
  match tr with
  | Leaf => True
  | Node v lt rt =>
    BST lt /\ tree_lt v lt /\
    BST rt /\ tree_gt v rt
  end.

(* Here is a typical insertion routine for BSTs.
 * From a given value, we recursively compare the value with items in
 * the tree from the root, until the value reaches a certain [Leaf].
 * You may wonder whether the tree after an insertion also satisfies [BST]....
 * Yes! That is one of things you should prove.
 * Notice our use of a function [compare] over [t], which returns one of
 * three cases, based on the relative ordering of its argument.
 *)
Fixpoint insert (a: t) (tr: tree) : tree :=
  match tr with
  | Leaf => Singleton a
  | Node v lt rt =>
    match compare a v with
    | Lt => Node v (insert a lt) rt
    | Eq => tr
    | Gt => Node v lt (insert a rt)
    end
  end.

(* Let's define some useful functions for deletion.
 * [rightmost], as the name says, finds the rightmost item for a given tree,
 * if it exists.
 *)
Fixpoint rightmost (tr: tree) : option t :=
  match tr with
  | Leaf => None
  | Node v _ rt =>
    match rt with
    | Leaf => Some v
    | _ => rightmost rt
    end
  end.

(* [delete_rightmost] returns a new tree where the rightmost item is removed,
 * if it exists.
 *)
Fixpoint delete_rightmost (tr: tree) : tree :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt =>
    match rt with
    | Leaf => lt
    | _ => Node v lt (delete_rightmost rt)
    end
  end.

(* Using [rightmost] and [delete_rightmost], deletion is defined here.
 * It is your job to understand how an item is deleted from a tree, and to
 * think about how the function preserves [BST].
 *)
Fixpoint delete (a: t) (tr: tree) : tree :=
  match tr with
  | Leaf => Leaf
  | Node v lt rt =>
    match compare a v with
    | Lt => Node v (delete a lt) rt
    | Eq =>
      match rightmost lt with
      | Some rv => Node rv (delete_rightmost lt) rt
      | None => rt
      end
    | Gt => Node v lt (delete a rt)
    end
  end.

(* Lastly, we define a simple membership checker, to find whether a given value
 * belongs to the tree or not.
 *)
Fixpoint member (a: t) (tr: tree) : bool :=
  match tr with
  | Leaf => false
  | Node v lt rt =>
    match compare a v with
    | Lt => member a lt
    | Eq => true
    | Gt => member a rt
    end
  end.

(* Finally, here are the facts you should prove. *)
Module Type S.

  (* 1) After inserting a value, it should be found in the tree. *)
  Axiom insert_member: forall tr n, BST tr -> member n (insert n tr) = true.

  (* 2) Insertion preserves [BST]. *)
  Axiom insert_ok: forall tr n, BST tr -> BST (insert n tr).

  (* 3) Deletion also preserves [BST]. *)
  Axiom delete_ok: forall tr n, BST tr -> BST (delete n tr).
End S.


(* Looking for another puzzle?  Here's an *optional* question. *)
Module Type OPTIONAL.
  (* 4) After deleting a value, it should not be found in the tree. *)
  Axiom delete_member: forall tr n, BST tr -> member n (delete n tr) = false.
End OPTIONAL.


(* As a timesaver for this pset, here is a *complete* list of tactics we used
 * in our solution.
 * - [apply thm]: apply theorem/lemma or hypothesis [thm], when its conclusion
 *   matches the current goal.  Then we switch to proving the premises of [thm].
 * - [apply thm with (x := e)]: like above, but for cases where not all
 *   quantified variables of [thm] have their values determined just from the
 *   shape of the current goal.  Instead, we give manual instantiations for
 *   those variables.  Multiple [(x := e)] items can be specified, for different
 *   variables.
 * - [apply thm with (x := e) in H]: like above, but in the forward direction:
 *   match a hypothesis of [thm] against hypothesis [H], to replace [H] with the
 *   conclusion of [thm].  (We only used this one for the _optional_ part.)
 * - [assumption]: solve an easy case: the goal matches a hypothesis.
 * - [cases e]: proceed by case analysis on the top-level structure of term [e].
 *   Useful to invoke on applications of functions like [compare]!
 * - [equality]: solve a goal that follows just by properties of equality, including
 *   some generic facts about inductive types (e.g., all constructors are injective).
 * - [induct x]: induction on quantified variable [x] from the theorem statement.
 * - [propositional]: simplify by rules of propositional logic (e.g., for "and"
 *   connective [/\]).
 * - [rewrite thm]: use quantified equality [thm] to replace all instances of its
 *   lefthand side with its righthand side.
 * - [simplify]: algebraic simplification everywhere, by applying definitions
 *   of functions.
 * - [cbn [ident]]: reduce only the applications of the definition whose 
 *   name is [ident] in the goal.
 * - [cbn [ident] in *]: reduce only the applications of the definition whose 
 *   name is [ident] in the goal and the context.
 * - [invert H]: we used it to derive an equality [x = y] from [Some x = Some y]
 *   (though the tactic is more general).
 * - [subst]: Given equalities like [x = e], where [x] is a variable, eliminates
 *   the variable [x] by substituting [e] for it everywhere.
 * - [unfold ident]: unfold a definition named [ident] to its body in the
 *   conclusion.
 * - [unfold ident in *]: unfold a definition named [ident] to its body
 *   in the conclusion and the context.
 *)
