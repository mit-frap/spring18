(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 3 *)

Require Import Frap Pset3Sig.

(* Define the identity function [id], which just returns its
 * argument without modification.
 *)
Definition id {A : Type} (x : A) : A.
Admitted.

(* [compose] is another higher-order function: [compose g f]
 * applies [f] to its input and then applies [g]. Argument order
 * follows the general convention of functional composition in
 * mathematics denoted by the small circle.
 *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B)
           (x : A) : C.
Admitted.

(* If we map the [id] function over any list, we get the
 * same list back.
 *)
Theorem map_id : forall {A : Type} (xs : list A),
    map id xs = xs.
Proof.
Admitted.

(* If we map the composition of two functions over the list,
 * it's the same as mapping the first function over the whole list
 * and then mapping the second function over that resulting list.
 *)
Theorem map_compose : forall {A B C : Type} (g : B -> C) (f : A -> B)
                        (xs : list A),
    map (compose g f) xs = map g (map f xs).
Proof.
Admitted.

(* Next we can show some classic properties that demonstrate a
 * certain sense in which [map] only modifies the elements of
 * a list, but preserves its structure: [map_length] shows it 
 * preserves length, and [map_append] and [map_rev] show that
 * it commutes with [++] and [rev], respectively.
 * For each of [length], [++], and [rev], it doesn't matter
 * whether we apply [map] before the operation or after.
 *)
Theorem map_length : forall {A B : Type} (f : A -> B) (xs : list A),
    length (map f xs) = length xs.
Proof.
Admitted.

Theorem map_append : forall {A B : Type} (f : A -> B) (xs ys : list A),
    map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
Admitted.

Theorem map_rev : forall {A B : Type} (f : A -> B) (xs : list A),
    map f (rev xs) = rev (map f xs).
Proof.
Admitted.

(* [fold] is a higher-order function that is even more general
 * than [map]. In essence, [fold f z] takes as input a list
 * and produces a term where the [cons] constructor is
 * replaced by [f] and the [nil] constructor is replaced
 * by [z].
 *
 * [fold] is a "right" fold, which associates the binary operation
 * the opposite way as the [left_fold] function that we defined
 * in lecture.
 *)
Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
         (xs : list A) : B.
Admitted.

(* For instance, we should have
     fold plus 10 [1; 2; 3]
   = 1 + (2 + (3 + 10))
   = 16
 *)
Example fold_example : fold plus 10 [1; 2; 3] = 16.
Proof.
Admitted.

(* Prove that [map] can actually be defined as a particular
 * sort of [fold].
 *)
Definition map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
    map f xs = fold (fun x ys => cons (f x) ys) nil xs.
Proof.
Admitted.

(* Since [fold f z] replaces [cons] with [f] and [nil] with
 * [z], [fold cons nil] should be the identity function.
 *)
Theorem fold_id : forall {A : Type} (xs : list A),
    fold cons nil xs = xs.
Proof.
Admitted.

(* If we apply [fold] to the concatenation of two lists,
 * it is the same as folding the "right" list and using
 * that as the starting point for folding the "left" list.
 *)
Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                        (xs ys : list A),
    fold f z (xs ++ ys) =
    fold f (fold f z ys) xs.
Proof.
Admitted.

(* Using [fold], define a function that computes the
 * sum of a list of natural numbers.
 *)
Definition sum : list nat -> nat.
Admitted.

(* Note that [simplify] fails to reduce [ sum [1; 2; 3] ].
 * This is due to a quirk of [simplify]'s behavior: because
 * unfolding [sum] does not present an immediate opportunity
 * for reduction (since [fold] will still need to be unfolded
 * to its fixpoint definition, no simplification is performed).
 * A simple remedy is to use the tactic [unfold sum] prior to
 * calling [simplify]. This should come in handy for future proofs
 * involving definitions that use [fold], too.
 *)
Example sum_example : sum [1; 2; 3] = 6.
Proof.
Admitted.

(* Using [fold], define a function that computes the
 * conjunction of a list of Booleans (where the 0-ary
 * conjunction is defined as [true]).
 *)
Definition all : list bool -> bool.
Admitted.

Example all_example : all [true; false; true] = false.
Proof.
Admitted.

(* The following two theorems, [sum_append] and [all_append],
 * say that the sum of the concatenation of two lists
 * is the same as summing each of the lists first and then
 * adding the result.
 *)
Theorem sum_append : forall (xs ys : list nat),
    sum (xs ++ ys) = sum xs + sum ys.
Proof.
Admitted.

Theorem all_append : forall (xs ys : list bool),
    all (xs ++ ys) = andb (all xs) (all ys).
Proof.
Admitted.

(* Just like we defined [map] for lists, we can similarly define
 * a higher-order function [tree_map] which applies a function on
 * elements to all of the elements in the tree, leaving the tree
 * structure in tact.
 *)
Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
  : tree B.
Admitted.

Example tree_map_example :
  tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
  = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
Proof.
Admitted.

(* [tree_map_flatten] shows that [map]
 * and [tree_map] are related by the [flatten] function.
 *)
Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
  flatten (tree_map f t) = map f (flatten t).
Proof.
Admitted.

(* Using [fold], define a function that composes a list of functions,
 * applying the *last* function in the list *first*.
 *)
Definition compose_list {A : Type} : list (A -> A) -> A -> A.
Admitted.

Example compose_list_example :
  compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
Proof.
Admitted.

(* Show that [sum xs] is the same as converting each number
 * in the list [xs] to a function that adds that number,
 * composing all of those functions together and finally
 * applying that large composed function to [0].
 *)
Theorem compose_list_map_add_sum : forall (xs : list nat),
    compose_list (map plus xs) 0 = sum xs.
Proof.
Admitted.

(* You've reached the end of the problem set. Congrats!
 *
 * If you're up for a completely optional additional challenge,
 * try the following exercises in implementing the "continuation monad"
 * and proving an exercise about it.
 *
 * If you don't want to complete this additional challenge, you
 * can just leave everything below unmodified.
 *)

(* The continuation monad [cont] describes those computations that
 * are written in continuation-passing style (CPS). A value of type
 * [cont A] is a function that, when given a continuation [k : A -> R]
 * for any type [R], returns a value of type [R].
 *)
Definition cont A := forall R, (A -> R) -> R.

(* Define [extract_cont], which demonstrates that it is possible to
 * extract a normal functional value from a CPS computation.
 *)
Definition extract_cont {A} (x : cont A) : A.
Admitted.

(* A *monad* is a common idiom in functional programming for composition
 * of computations that return certain higher-typed values.
 * A monad [m] has type [Type -> Type] and has two operations:
 * [ret : forall A, A -> m A], which injects a pure value into the monad, and
 * [bind : forall A B, m A -> (A -> m B) -> m B], which composes two monadic
 * computations together.
 * Define these operations for [cont] (hint: there is only one way to
 * implement operations with these types for [cont]).
 *)
Definition ret {A} (x : A) : cont A.
Admitted.

Definition bind {A B} (x : cont A) (f : A -> cont B) : cont B.
Admitted.

(* Monads are expected to satisfy certain laws relating the behavior
 * of these two operations. For the continuation monad, prove that
 * the following property holds:
 *)
Theorem ret_bind : forall {A B} (x : A) (f : A -> cont B)
    R (k : B -> R),
    bind (ret x) f R k = f x R k.
Proof.
Admitted.
