From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.

Set Implicit Arguments.

(* NOTE: Elimination of a unused relaxed load is unsound under the
 * liveness-aware semantics.  Consider the following example:

    while (!y_plain) {
        r = x_rlx;
        fence(acquire);
    }

    ||

    y =rlx 1;
    x =rel 1;

 * Under the liveness-aware semantics, the loop *should* break, as
 * once `x_rlx` will read `x =rel 1` and the acquire fence guarantees
 * that `y_plain` will read 1.  However, the elimination of
 * `x_rlx` will allow the loop to run forever.
 *)

Lemma elim_read
      lc0 mem0
      loc ord
      (ORD: Ordering.le ord Ordering.plain)
      (WF: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0):
  exists ts val released,
    Local.read_step lc0 mem0 loc ts val released ord lc0.
Proof.
  destruct lc0.
  assert (exists from val released, Memory.get loc ((View.pln (TView.cur tview)) loc) mem0 = Some (from, Message.concrete val released)).
  { inv WF. ss. inv TVIEW_CLOSED. inv CUR.
    exploit PLN; eauto.
  }
  des. inv MEM. exploit CLOSED; eauto. i. des.
  esplits. econs; eauto; try refl.
  - econs; viewtac.
  - f_equal. apply TView.antisym.
    + apply TViewFacts.read_tview_incr.
    + unfold TView.read_tview. econs; repeat (condtac; aggrtac; try apply WF).
      etrans; apply WF.
Qed.
