(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 2 *)

Require Import Frap.

(* Authors:
 * Ben Sherman (sherman@csail.mit.edu),
 * Adam Chlipala (adamc@csail.mit.edu)
 *)

(** * Polymorphic container types *)

(* In this problem set, we'll get some practice using some of the
 * polymorphic container types that we saw in Lecture 2, in particular,
 * [option], [list], and [tree]. We'll then use [tree] and [option]
 * together to create binary tries (i.e., finite maps keyed by lists of
 * Booleans).
 *
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

(* And here's one additional definition that we'll use in this problem set.
 * [either] combines two [option] values into one.
 * If either argument to [either] is a [Some], then so is
 * the result of the [either], preferring the contents of
 * the first argument if both are [Some].
 *
 * We will observe an "analogy" between the [either]
 * function on options and the [++] function on lists.
 *)
Definition either {A} (xo yo : option A) : option A :=
  match xo with
  | None => yo
  | Some x => Some x
  end.

(* A binary trie is a finite map keyed by lists of Booleans.
 * We will implement a binary trie with entries of type [A]
 * by [tree (option A)]. The value at the root of the tree
 * corresponds to the entry for the key [nil : list bool],
 * the left subtree contains entries for those keys that
 * begin with [true], and the right subtree contains entries
 * for those keys that begin with [false].
 *)
   
Definition binary_trie A := tree (option A).

(* Here, again, is the module type setting out exactly which theorems you need
 * to prove for full credit on this assignment. *)
Module Type S.

  (* If we [either] an [option] value with [None]
   * on the right, it leaves that value unchanged,
   * (just as if we put the [None] on the left).
   * This is analogous to how appending [nil]
   * on either side of a list leaves it unchanged.
   *)
  Axiom either_None_right : forall {A} (xo : option A),
    either xo None = xo.

  (* [either] is associative, just like [++].
   *)
  Axiom either_assoc : forall {A} (xo yo zo : option A),
    either (either xo yo) zo = either xo (either yo zo).

  (* [head] should compute the head of a list, that is,
   * it should return [Some] with the first element of
   * the list if the list is nonempty, and [None]
   * if the list is empty.
   *)
  Parameter head : forall {A}, list A -> option A.

  Axiom head_example : head [1; 2; 3] = Some 1.

  (* The following theorem makes a formal connection
   * between [either] and [++].
   *)
  Axiom either_app_head : forall {A} (xs ys : list A),
      head (xs ++ ys) = either (head xs) (head ys).

  (* [leftmost_Node] should compute the leftmost node of
   * a tree. 
   *
   * Please implement [leftmost_Node] directly using
   * recursion (i.e., pattern matching) on the [tree] argument,
   * without using the [flatten] operation.
   *)
  Parameter leftmost_Node : forall {A}, tree A -> option A.

  Axiom leftmost_Node_example :
    leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf)
    = Some 2.

  (* Prove that the leftmost node of the tree is the same
   * as the head of the list produced by flattening the tree
   * with an in-order traversal.
   *)
  Axiom leftmost_Node_head : forall {A} (t : tree A),
      leftmost_Node t = head (flatten t).

  (* Now let's work with the binary tries we defined earlier!
   *
   * Define [lookup] such that [lookup k t] looks up the
   * map entry corresponding to the key [k : list bool] in the
   * binary trie [t : binary_trie A], interpreting [t] such that
   * the value at the root of [t] corresponds to the 
   * entry for the key [nil], the left subtree contains entries 
   * for those keys that begin with [true], and the right subtree
   * contains entries for those keys that begin with [false].
   *)
  Parameter lookup : forall {A}, list bool -> binary_trie A -> option A.

  Axiom lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.

  Axiom lookup_example2 : lookup [false; true]
    (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                          = Some 1.

  (* [Leaf] represents an empty binary trie, so a lookup for
   * any key should return [None].
   *)
  Axiom lookup_empty : forall {A} (k : list bool),
      lookup k (Leaf : binary_trie A) = None.

  (* Define an operation to "insert" a key and optional value
   * into a binary trie. The [insert] definition should satisfy two
   * properties: one is [lookup_insert] below, which says that if we
   * look up a key [k] in a trie where [(k, v)] has just been inserted,
   * the result should be [v]. The other is that lookups on keys different
   * from the one just inserted should be the same as on the original map.
   *
   * If an entry for that key already exists, [insert] should replace
   * that entry with the new one being inserted. Note that [insert] can
   * be used to remove an entry from the trie, too, by inserting [None] 
   * as the value.
   *
   * Hint: it may be helpful to define an auxiliary function that inserts
   * a key and optional value into the empty trie.
   *)
  Parameter insert : forall {A}, list bool -> option A -> binary_trie A -> binary_trie A.

  Axiom insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
  Axiom insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.

  Axiom lookup_insert : forall {A} (k : list bool) (v : option A) (t : binary_trie A),
      lookup k (insert k v t) = v.
End S.

(* The template file Pset2.v also suggests an additional challenge problem,
 * which won't be graded, but which provides extra practice with container data
 * structures.  The key operation is *left-biased merge for trees*. *)
