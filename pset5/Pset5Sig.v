(** * 6.822 Formal Reasoning About Programs, Spring 2018 - Pset 5 *)

Require Import Frap Datatypes.
Export Datatypes.

(* Authors: 
 * Joonwon Choi (joonwonc@csail.mit.edu), 
 * Adam Chlipala (adamc@csail.mit.edu),
 * Ben Sherman (sherman@csail.mit.edu)
 *)

Set Implicit Arguments.

(** * Correctness of a Producer-Consumer implementation *)

(* In this problem set, we'll prove the correctness of a 
 * Producer-Consumer implementation.
 * For general specification, refer to this article first:
 *   https://en.wikipedia.org/wiki/Producer%E2%80%93consumer_problem
 *
 * Like with the last problem set, we will provide hints
 * on the class website. You may wish to first attempt the problem
 * set without consulting the hints, but they are available if
 * you wish.
 *
 * We will implement Producer-Consumer with locks.
 * In addition to the concurrency control, we have to think about interleavings
 * between Producer and Consumer, since they communicate via a buffer.
 *
 * Therefore, in order to solve the problem, you should either 1) carefully 
 * abstract the system enough to check with the FRAP model checker, or 2)
 * directly prove the given invariant (possibly with parameterized PRD_COUNT).
 *)

(* Here's another example of a reusable program for building multithreaded
 * systems out of systems for single threads.  We will build in general handling
 * of a standard locking protocol, in contrast to the freeform notion of shared
 * state in the [parallel] combinator we saw in class. *)

(* First, a general record type for adding a lock bit to a type of shared
 * state: *)
Record sharedWithLock shared := { Lock : bool; SharedOrig : shared }.

(* We force single-thread systems to use instantiations of this type for
 * their private state, to signal when they want to lock or unlock. *)
Inductive stateWithLock private :=
| Aprivate : private -> stateWithLock private
(* This is a state for a thread whose next step is *not* lock-related. *)

| Alock : stateWithLock private
| Aunlock : stateWithLock private
(* These states respectively indicate that the next thing the thread wants to do
 * is claim or relinquish the lock.  For simplicity, we make the arbitrary
 * choice that threads waiting to lock or unlock store no additional local
 * state, but the approach would generalize to including that state. *).

Arguments Alock {_}.
Arguments Aunlock {_}.
(* These lines ask Coq to infer the [private] type associated with a use of one
 * of the second two constructors. *)

(* Initial states of the two-thread system combine initial states of the
 * constituent systems, with the lock initialized to [false]. *)
Inductive locking_init shared private1 private2
          (init1 : threaded_state shared (stateWithLock private1) -> Prop)
          (init2 : threaded_state shared (stateWithLock private2) -> Prop)
  : threaded_state (sharedWithLock shared)
                   (stateWithLock private1 * stateWithLock private2) -> Prop :=
| Ainit : forall sh pr1 pr2,
    init1 {| Shared := sh; Private := pr1 |} ->
    init2 {| Shared := sh; Private := pr2 |} ->
    locking_init init1 init2 {| Shared := {| Lock := false; SharedOrig := sh |};
                            Private := (pr1, pr2) |}.

(* Here's the combined transition relation.  The rules come in symmetric pairs,
 * based on which of the two threads steps. *)
Inductive locking_step shared private1 private2
          (step1 : threaded_state shared (stateWithLock private1) ->
                   threaded_state shared (stateWithLock private1) -> Prop)
          (step2 : threaded_state shared (stateWithLock private2) ->
                   threaded_state shared (stateWithLock private2) -> Prop)
  : threaded_state (sharedWithLock shared) (stateWithLock private1 * stateWithLock private2) ->
    threaded_state (sharedWithLock shared) (stateWithLock private1 * stateWithLock private2) ->
    Prop :=

(* First, a thread that is not asking to lock or unlock may simply take a step
 * as normal. *)
| AstepN1 : forall sh pr1 pr2 sh' l pr1',
    step1 {| Shared := sh; Private := Aprivate pr1 |} {| Shared := sh'; Private := pr1' |} ->
    locking_step step1 step2
             {| Shared := {| Lock := l; SharedOrig := sh |}; Private := (Aprivate pr1, pr2) |}
             {| Shared := {| Lock := l; SharedOrig := sh' |}; Private := (pr1', pr2) |}
| AstepN2 : forall sh pr1 pr2 sh' l pr2',
    step2 {| Shared := sh; Private := Aprivate pr2 |} {| Shared := sh'; Private := pr2' |} ->
    locking_step step1 step2
             {| Shared := {| Lock := l; SharedOrig := sh |}; Private := (pr1, Aprivate pr2) |}
             {| Shared := {| Lock := l; SharedOrig := sh' |}; Private := (pr1, pr2') |}

(* A thread asking to lock may only step when the lock is not held, and then the
 * step toggles the lock. *)
| AstepLock1 : forall sh pr2 pr1',
    step1 {| Shared := sh; Private := Alock |} {| Shared := sh; Private := pr1' |} ->
    locking_step step1 step2
             {| Shared := {| Lock := false; SharedOrig := sh |}; Private := (Alock, pr2) |}
             {| Shared := {| Lock := true; SharedOrig := sh |}; Private := (pr1', pr2) |}
| AstepLock2 : forall sh pr1 pr2',
    step2 {| Shared := sh; Private := Alock |} {| Shared := sh; Private := pr2' |} ->
    locking_step step1 step2
             {| Shared := {| Lock := false; SharedOrig := sh |}; Private := (pr1, Alock) |}
             {| Shared := {| Lock := true; SharedOrig := sh |}; Private := (pr1, pr2') |}

(* A thread asking to unlock may only step when the lock is held, and then the
 * step toggles the lock. *)
| AstepUnlock1 : forall sh pr2 pr1',
    step1 {| Shared := sh; Private := Aunlock |} {| Shared := sh; Private := pr1' |} ->
    locking_step step1 step2
             {| Shared := {| Lock := true; SharedOrig := sh |}; Private := (Aunlock, pr2) |}
             {| Shared := {| Lock := false; SharedOrig := sh |}; Private := (pr1', pr2) |}
| AstepUnlock2 : forall sh pr1 pr2',
    step2 {| Shared := sh; Private := Aunlock |} {| Shared := sh; Private := pr2' |} ->
    locking_step step1 step2
             {| Shared := {| Lock := true; SharedOrig := sh |}; Private := (pr1, Aunlock) |}
             {| Shared := {| Lock := false; SharedOrig := sh |}; Private := (pr1, pr2') |}.

(* Here's the final definition of a two-thread system with locking. *)
Definition locking shared private1 private2
           (sys1 : trsys (threaded_state shared (stateWithLock private1)))
           (sys2 : trsys (threaded_state shared (stateWithLock private2))) :=
  {| Initial := locking_init sys1.(Initial) sys2.(Initial);
     Step := locking_step sys1.(Step) sys2.(Step)
  |}.

(* PRD_COUNT is the number of produced items by Producer.
 * This is large enough that direct use of "model_check" for the system
 * takes really long. Thus, yes, during grading for this problem set, we will 
 * just stop the checker if it takes a long time.
 *
 * Note that for PRD_COUNT = 15, we have hundreds of possible states.
 *)
Definition PRD_COUNT := 15.

(* Below is pseudocode of our Producer-Consumer implementation.  Producer always
 * produces "1" and pushes it to the buffer [buf].  Consumer pops the value from
 * the buffer and adds it to [acc].
 *)
(* <<
   queue buf = empty;
   int cnt = PRD_COUNT;
   int acc = 0;

   void produce() {
     int local;
     while (cnt > 0) {
       lock();
       cnt = cnt - 1;
       buf.push(1);
       unlock();
     }
   }

   void consume() {
     int local, val;
     while (true) {
       lock();
       val = buf.pop();
       acc = acc + val;
       unlock();
     }
   }
   >>
 *)

Inductive pd_thread :=
| CheckCount
| DecCount
| Push.

Inductive cs_thread :=
| Pop
| Acc (n : nat).

Record pdcs_global_state :=
  { buf : list nat;
    cnt : nat;
    acc : nat }.

Definition pd_state :=
  threaded_state pdcs_global_state (stateWithLock pd_thread).

Definition cs_state :=
  threaded_state pdcs_global_state (stateWithLock cs_thread).

Inductive pd_init : pd_state -> Prop :=
| PdInit :
    pd_init {| Shared := {| buf := nil; cnt := PRD_COUNT; acc := 0 |};
               Private := Aprivate CheckCount |}.

Inductive cs_init : cs_state -> Prop :=
| CsInit :
    cs_init {| Shared := {| buf := nil; cnt := PRD_COUNT; acc := 0 |};
                 Private := Alock |}.

Inductive pd_step : pd_state -> pd_state -> Prop :=
| PdCheckCount :
    forall b c a,
      pd_step   {| Shared := {| buf := b; cnt := S c; acc := a |};
                   Private := Aprivate CheckCount |}
                {| Shared := {| buf := b; cnt := S c; acc := a |};
                   Private := Alock |}
| PdLock :
    forall sh, pd_step        {| Shared := sh; Private := Alock |}
                         {| Shared := sh; Private := Aprivate DecCount |}
| PdDecCount :
    forall b c a,
      pd_step   {| Shared := {| buf := b; cnt := S c; acc := a |};
                   Private := Aprivate DecCount |}
                {| Shared := {| buf := b; cnt := c; acc := a |};
                   Private := Aprivate Push |}
| PdPush :
    forall b c a,
      pd_step   {| Shared := {| buf := b; cnt := c; acc := a |};
                   Private := Aprivate Push |}
                {| Shared := {| buf := 1 :: b; cnt := c; acc := a |};
                   Private := Aunlock |}
| PdUnlock :
    forall sh, pd_step        {| Shared := sh; Private := Aunlock |}
                         {| Shared := sh; Private := Aprivate CheckCount |}.

Inductive cs_step : cs_state -> cs_state -> Prop :=
| CsLock :
    forall sh, cs_step        {| Shared := sh; Private := Alock |}
                         {| Shared := sh; Private := Aprivate Pop |}
| CsPop :
    forall bh bt c a,
      cs_step   {| Shared := {| buf := bh :: bt; cnt := c; acc := a |};
                   Private := Aprivate Pop |}
                {| Shared := {| buf := bt; cnt := c; acc := a |};
                   Private := Aprivate (Acc bh) |}
| CsAcc :
    forall b c a v,
      cs_step   {| Shared := {| buf := b; cnt := c; acc := a |};
                   Private := Aprivate (Acc v) |}
                {| Shared := {| buf := b; cnt := c; acc := a + v |};
                   Private := Aunlock |}
| CsUnlock :
    forall sh, cs_step        {| Shared := sh; Private := Aunlock |}
                         {| Shared := sh; Private := Alock |}.

Definition pdcs2_sys := locking
                          {| Initial := pd_init;
                             Step := pd_step |}
                          {| Initial := cs_init;
                             Step := cs_step |}.

(* The correctness of the system is given as below: when Producer completely
 * produces all values and Consumer consumes all of them, then the accumulated
 * value equals PRD_COUNT.
 *)
Definition pdcs2_correct
           (s : threaded_state (sharedWithLock pdcs_global_state)
                               (stateWithLock pd_thread * stateWithLock cs_thread)) :=
  s.(Shared).(SharedOrig).(cnt) = 0 ->
  s.(Shared).(SharedOrig).(buf) = nil ->
  s.(Shared).(Lock) = false ->
  s.(Shared).(SharedOrig).(acc) = PRD_COUNT.

Module Type S.
  Axiom pdcs2_ok : invariantFor pdcs2_sys pdcs2_correct.
End S.
