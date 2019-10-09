Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
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

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import Promotion.
Require Import SimCommon.

Set Implicit Arguments.


Module PromotionProgress.
  Import SimCommon.

  Set Nested Proofs Allowed.

  Lemma progress_read_aux
        l view released b ts
        (RELEASED: View.le released view):
    sim_view l view (View.join (View.join view (View.singleton_ur_if b l ts)) released).
  Proof.
    destruct b; ss.
    - unfold View.singleton_ur, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      econs; ss; ii.
      + unfold TimeMap.join. condtac; ss.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
      + unfold TimeMap.join. condtac; ss.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
    - unfold View.singleton_rw, TimeMap.bot, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      econs; ss; ii.
      + unfold TimeMap.join.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
      + unfold TimeMap.join. condtac; ss.
        apply TimeFacts.antisym.
        * etrans; eauto using Time.join_l.
        * inv RELEASED.
          repeat eapply Time.join_spec; eauto using Time.bot_spec; try refl.
  Qed.

  Lemma progress_read
        l lc1 mem1 from val released ord
        (WF1: Local.wf lc1 mem1)
        (MEM1: Memory.closed mem1)
        (LATEST: Memory.get l (Memory.max_ts l mem1) mem1 = Some (from, Message.full val released))
        (SAFE: View.le released.(View.unwrap) lc1.(Local.tview).(TView.cur)):
    exists lc2,
      <<STEP: Local.read_step lc1 mem1 l (Memory.max_ts l mem1) val released ord lc2>> /\
      <<LC: sim_local l lc1 lc2>>.
  Proof.
    esplits.
    - econs; eauto.
      econs; i; eapply Memory.max_ts_spec2; apply WF1.
    - econs; try refl. econs; ss.
      + eapply progress_read_aux.
        condtac; ss. apply View.bot_spec.
      + eapply progress_read_aux.
        condtac; ss; eauto using View.bot_spec.
        etrans; eauto. apply WF1.
  Qed.

  Lemma progress_write
        l lc1 sc1 mem1 val releasedm released ord
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (MEM1: Memory.closed mem1)
        (WF_REL: View.opt_wf releasedm)
        (CLOSED_REL: Memory.closed_opt_view releasedm mem1)
        (PROMISES1: forall to, Memory.get l to lc1.(Local.promises) = None)
        (SAFE1: View.le releasedm.(View.unwrap) lc1.(Local.tview).(TView.cur)):
    exists lc2 mem2,
      <<STEP: Local.write_step lc1 sc1 mem1 l (Memory.max_ts l mem1) (Time.incr (Memory.max_ts l mem1))
                               val releasedm released ord lc2 sc1 mem2 Memory.op_kind_add>> /\
      <<LC: sim_local l lc1 lc2>> /\
      <<PROMISES2: forall to, Memory.get l to lc2.(Local.promises) = None>> /\
      <<SAFE2: View.le released.(View.unwrap) lc1.(Local.tview).(TView.cur)>>.
  Proof.
  Admitted.
End PromotionProgress.
