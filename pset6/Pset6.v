(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 6 *)

Require Import Frap.

(* Authors: 
 * Ben Sherman (sherman@csail.mit.edu),
 * Joonwon Choi (joonwonc@csail.mit.edu), 
 * Adam Chlipala (adamc@csail.mit.edu)
 *)

(* In this problem set, we will work with the following simple imperative language with
 * a nondeterministic choice operator. Your task is to define both big-step as well as
 * a particular kind of small-step operational semantics for this language
 * (one that is in fact deterministic), and to prove a theorem connecting the two:
 * if the small-step semantics aborts, then the big-step semantics may abort.
 *
 * This is the first problem set so far in this class that is truly open-ended.
 * We want to give you the flexibility to define the operational semantics as
 * you wish, and if you'd like you may even differ from the template shown here
 * if you find it more convenient.
 * Additionally, this is the first problem set where it is *NOT* sufficient to
 * just get the file compiling without any use of [admit] or [Admitted].
 * This will not necessarily guarantee that you have given reasonable semantics
 * for the programming language, and accordingly, will not necessarily
 * guarantee that you will earn full credit. For instance, if you define
 * your small-step semantics as the empty relation (which is incorrect), 
 * the theorem you must prove to connect your big-step and small-step 
 * semantics will be trivial.
 *)

(** * Syntax *)

(* Basic arithmetic expressions, as we've seen several times in class. *)
Inductive arith : Set :=
| Const : nat -> arith
| Var : var -> arith
| Plus : arith -> arith -> arith
| Eq : arith -> arith -> arith
(* should return 1 if the two expressions are equal, and 0 otherwise. *)
| Lt : arith -> arith -> arith
(* should return 1 if the two expressions are equal, and 0 otherwise. *)
.

(* The simple imperative language with a [Choose] syntax for 
 * nondeterminism. The intended meaning of the program 
 * [Choose c c'] is that either [c] should run or [c'] should run.
 *)
Inductive cmd :=
| Assign : var -> arith -> cmd
| Skip : cmd
| Seq : cmd -> cmd -> cmd
| Choose : cmd -> cmd -> cmd (* Here's the main novelty: nondeterministic choice *)
| If : arith -> cmd (* then *) -> cmd (* else *) -> cmd
| While : arith -> cmd -> cmd
| Abort : cmd (* This command should immediately terminate the program *)
.


(** Notations *)

Delimit Scope cmd_scope with cmd.

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "==" := Eq (at level 75) : arith_scope.
Infix "<" := Lt : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75) : cmd_scope.
Infix "<|>" := Choose (at level 78) : cmd_scope.
Infix ";;" := Seq (at level 80) : cmd_scope.

Notation "'if_' c 'then' t 'else' f" := (If c%arith t f) (at level 75) : cmd_scope.
Notation "'while' c 'do' p" := (While c%arith p) (at level 75) : cmd_scope.


(** * Examples *)

(* All nondeterministic realizations of [test_prog1] terminate
 * (either normally or by aborting). [test_prog1 5] may abort,
 * but [test_prog1 6] always terminates normally.
 *)
Definition test_prog1 (k : nat) : cmd := (
  "target" <- 8 ;;
  ("x" <- 3 <|> "x" <- 4) ;;
  ("y" <- 1 <|> "y" <- k) ;;
  if_ "x" + "y" == "target"
     then Abort
     else Skip
  )%cmd.

(* No matter the value of [num_iters], [test_prog2 num_iters]
 * always may potentially fail to terminate, and always
 * may potentially abort.
 *)
Definition test_prog2 (num_iters : nat) : cmd := (
   "acc" <- 0 ;;
   "n" <- 0;;
   while ("n" < 1) do (
     (Skip <|> "n" <- 1) ;;
     "acc" <- "acc" + 1
   ) ;;
   if_ "acc" == S num_iters
     then Abort
     else Skip
  )%cmd.


(* We've seen the expression language in class a few times,
 * so here we'll just give you the interpreter for that
 * expression language.
 *)
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
  | Eq e1 e2 => if interp e1 v ==n interp e2 v then 1 else 0
  | Lt e1 e2 => if lt_dec (interp e1 v) (interp e2 v) then 1 else 0
  end.

(** ** Part 1: Big-step operational semantics *)

(* You should define some result type (say, [result]) for values that commands
   in the language run to, and define a big-step operational semantics
   [eval : valuation -> cmd -> result -> Prop]
   that says when a program *may* run to some result in *some* nondeterministic
   realization of the program. Then you should also define a predicate
   [big_aborted : result -> Prop]
   that describes which results indicate that the program aborted.

 * Looking at the examples, we should have
   [exists res, eval $0 (test_prog1 5) res /\ big_aborted res]
   but
   [forall res, eval $0 (test_prog1 6) res -> big_aborted res -> False] 
 * . You are not required to prove these facts, but it could be a good
     sanity check!
 *)

Definition result : Set.
Admitted.

Definition eval : valuation -> cmd -> result -> Prop.
Admitted.

Definition big_aborted : result -> Prop.
Admitted.

(* As an optional sanity check, you may attempt to
 * prove that your big-step semantics behaves appropriately
 * for an example program:
 
Example test_prog1_reachable :
  exists res, eval $0 (test_prog1 5) res /\ big_aborted res.
Proof.
Admitted.

Example test_prog1_unreachable :
  forall res, eval $0 (test_prog1 6) res -> big_aborted res -> False.
Proof.
Admitted.
*)


  (** ** Part 2: Small-step deterministic operational semantics *)

(* Next, you should define a small-step operational semantics for this
   language that in some sense tries to run *all* possible nondeterministic
   realizations and aborts if any possible realization aborts.
   Define a type [state] that represents the underlying state that the
   small-step semantics should take steps on, and then define a small-step
   semantics
   [step : state -> state -> Prop]
   .

   Here's the twist: we ask that you define an operational semantics that 
   is *deterministic*, in the sense of the following formal statement:
   [forall s1 s2 s2', step s1 s2 -> step s1 s2' -> s2 = s2'].

   The operational model that we have in mind in this: when we encounter
   a nondeterministic choice, we execute the left branch. If the left
   branch terminates without aborting, we backtrack and try the
   other nondeterministic choice.

   Note that if any possible realization does not terminate,
   we allow the deterministic small-step semantics to diverge as well.
   (It is actually possible to define a semantics that always "finds" aborts,
   even if some branches of nondeterminism diverge!  However, the proof of that
   variant would likely be significantly more complicated, and we haven't tried
   it ourselves.)

   Define a function
   [init : valuation -> cmd -> state]
   that builds starting states for the small-step semantics,
   a predicate
   [small_aborted : state -> Prop]
   that describes which states are considered aborted, and
   a predicate
   [small_terminated : state -> Prop]
   that describes states that have run to completion without any
   nondeterministic branch aborting.

 * Looking at the examples, we should have
   [exists st, step^* (init $0 (test_prog1 5)) st /\ small_aborted st]
   but
   [forall st, step^* (init $0 (test_prog1 6)) st -> small_aborted st -> False]
   . You are not required to prove these facts, but it could be
   a good sanity check!
 *)

Definition state : Set.
Admitted.

Definition step : state -> state -> Prop.
Admitted.

Definition init : valuation -> cmd -> state.
Admitted.

Definition small_aborted : state -> Prop.
Admitted.

Definition small_terminated : state -> Prop.
Admitted.


(* As an optional sanity check, you may attempt to
 * prove that your small-step semantics behaves appropriately
 * for an example program:

Example test_prog1_reachable_small :
  exists st, step^* (init $0 (test_prog1 5)) st /\ small_aborted st.
Proof.
Admitted.

Example test_prog1_unreachable_small :
  forall st, step^* (init $0 (test_prog1 6)) st -> small_aborted st -> False.
Proof.
Admitted.
*)

(** ** Part 3: Connection between big- and small-step semantics *)

(* Prove the following theorem demonstrating the connection between the big-step
 * and small-step semantics:
 *
 * If the small-step semantics aborts, then the big-step semantics may
 * potentially abort.
 *)

Theorem small_abort_big_may_abort : forall v c s,
         step^* (init v c) s
      -> small_aborted s
      -> exists res, eval v c res /\ big_aborted res.
Proof.
Admitted.



(* As an additional challenge, you  you may want to prove the following
 * theorem. Note that this is *NOT* required for this assignment and
 * will not affect your grade.
 *
 * If the small-step semantics terminates without aborting, then the
 * big-step semantics may *not* abort.

Theorem small_terminates_big_may_not_abort :
       forall v c s,
         step^* (init v c) s
      -> small_terminated s
      -> forall res, 
             eval v c res 
          -> big_aborted res
          -> False.
Proof.
Admitted.
*)