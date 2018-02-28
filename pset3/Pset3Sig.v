(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 3 *)

Require Import Frap.

(* In this problem set, we'll get some experience with higher-order functions,
 * which are functions that themselves take functions as arguments!
 *)

(*
 * First, we'll reproduce some definitions we need from Lecture 2,
 * [tree] and [flatten]:
 *)

Inductive tree {A} :=
| Leaf
| Node (l : tree) (d : A) (r : tree).
Arguments tree : clear implicits.

Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l d r => flatten l ++ d :: flatten r
  end.

Module Type S.

  (* Define the identity function [id], which just returns its
   * argument without modification.
   *)
  Parameter id : forall {A : Type}, A -> A.

  (* [compose] is another higher-order function: [compose g f]
   * applies [f] to its input and then applies [g]. Argument order
   * follows the general convention of functional composition in
   * mathematics denoted by the small circle.
   *)
  Parameter compose : forall {A B C : Type}, (B -> C) -> (A -> B) -> A -> C.

  (* If we map the [id] function over any list, we get the
   * same list back.
   *)
  Axiom map_id : forall {A : Type} (xs : list A),
    map id xs = xs.

  (* If we map the composition of two functions over the list,
   * it's the same as mapping the first function over the whole list
   * and then mapping the second function over that resulting list.
   *)
  Axiom map_compose : forall {A B C : Type} (g : B -> C) (f : A -> B)
                             (xs : list A),
    map (compose g f) xs = map g (map f xs).

  (* Next we can show some classic properties that demonstrate a
   * certain sense in which [map] only modifies the elements of
   * a list but preserves its structure: [map_length] shows it 
   * preserves length, and [map_append] and [map_rev] show that
   * it commutes with [++] and [rev], respectively.
   * For each of [length], [++], and [rev], it doesn't matter
   * whether we apply [map] before the operation or after.
   *)
  Axiom map_length : forall {A B : Type} (f : A -> B) (xs : list A),
    length (map f xs) = length xs.

  Axiom map_append : forall {A B : Type} (f : A -> B) (xs ys : list A),
    map f (xs ++ ys) = map f xs ++ map f ys.

  Axiom map_rev : forall {A B : Type} (f : A -> B) (xs : list A),
    map f (rev xs) = rev (map f xs).

  (* [fold] is a higher-order function that is even more general
   * than [map]. In essence, [fold f z] takes as input a list
   * and produces a term where the [cons] constructor is
   * replaced by [f] and the [nil] constructor is replaced
   * by [z].
   *
   * [fold] is a "right" fold, which associates the binary operation
   * the opposite way as the [fold_left] function that we defined
   * in lecture.
   *)
  Parameter fold : forall {A B : Type}, (A -> B -> B) -> B -> list A -> B.

  (* For instance, we should have
       fold plus 10 [1; 2; 3]
     = 1 + (2 + (3 + 10))
     = 16
   *)
  Axiom fold_example : fold plus 10 [1; 2; 3] = 16.

  (* Prove that [map] can actually be defined as a particular
   * sort of [fold].
   *)
  Axiom map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
    map f xs = fold (fun x ys => cons (f x) ys) nil xs.

  (* Since [fold f z] replaces [cons] with [f] and [nil] with
   * [z], [fold cons nil] should be the identity function.
   *)
  Axiom fold_id : forall {A : Type} (xs : list A),
    fold cons nil xs = xs.

  (* If we apply [fold] to the concatenation of two lists,
   * it is the same as folding the "right" list, and using
   * that as the starting point for folding the "left" list.
   *)
  Axiom fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                        (xs ys : list A),
    fold f z (xs ++ ys) =
    fold f (fold f z ys) xs.

  (* Using [fold], define a function that computes the
   * sum of a list of natural numbers.
   *)
  Parameter sum : list nat -> nat.

  (* Note that [simplify] fails to reduce [ sum [1; 2; 3] ].
   * This is due to a quirk of [simplify]'s behavior: because
   * unfolding [sum] does not present an immediate opportunity
   * for reduction (since [fold] will still need to be unfolded
   * to its fixpoint definition, no simplification is performed).
   * A simple remedy is to use the tactic [unfold sum] prior to
   * calling [simplify]. This should come in handy for future proofs
   * involving definitions that use [fold], too.
   *)
  Axiom sum_example : sum [1; 2; 3] = 6.
  
  (* Using [fold], define a function that computes the
   * conjunction of a list of Booleans (where the 0-ary
   * conjunction is defined as [true]).
   *)
  Parameter all : list bool -> bool.

  Axiom all_example : all [true; false; true] = false.

  (* The following two theorems, [sum_append] and [all_append],
   * say that the sum of the concatenation of two lists
   * is the same as summing each of the lists first and then
   * adding the result.
   *)
  Axiom sum_append : forall (xs ys : list nat),
      sum (xs ++ ys) = sum xs + sum ys.

  Axiom all_append : forall (xs ys : list bool),
      all (xs ++ ys) = andb (all xs) (all ys).

  (* Just like we defined [map] for lists, we can similarly define
   * a higher-order function [tree_map] which applies a function on
   * elements to all of the elements in the tree, leaving the tree
   * structure intact.
   *)
  Parameter tree_map : forall {A B : Type}, (A -> B) -> tree A -> tree B.

  Axiom tree_map_example :
    tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
    = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).

  (* [tree_map_flatten] shows that [map]
   * and [tree_map] are related by the [flatten] function.
   *)
  Axiom tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
      flatten (tree_map f t) = map f (flatten t).

  (* Using [fold], define a function that composes a list of functions,
   * applying the *last* function in the list *first*.
   *)
  Parameter compose_list : forall {A : Type}, list (A -> A) -> A -> A.

  Axiom compose_list_example :
    compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.

  (* Show that [sum xs] is the same as converting each number
   * in the list [xs] to a function that adds that number,
   * composing all of those functions together, and finally
   * applying that large composed function to [0].
   * Note that function [plus], when applied to just one number as an
   * argument, returns a function over another number, which
   * adds the original argument to it!
   *)
  Axiom compose_list_map_add_sum : forall (xs : list nat),
    compose_list (map plus xs) 0 = sum xs.
  
End S.

(* The template file Pset3.v also suggests some additional challenge problems,
 * which won't be graded but which provide extra practice with higher-order
 * functions. In these problems, you will implement the "continuation monad"
 * and prove a property about it.
 *)
