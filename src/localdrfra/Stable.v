Require Import Omega.
Require Import Bool.
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

Require Import RARace.

Set Implicit Arguments.


(* TODO: move *)

Lemma time_le_join_l
      l r
      (LE: Time.le r l):
  Time.join l r = l.
Proof.
  unfold Time.join. condtac; auto.
  apply TimeFacts.antisym; auto.
Qed.

Lemma time_le_join_r
      l r
      (LE: Time.le l r):
  Time.join l r = r.
Proof.
  rewrite Time.join_comm.
  apply time_le_join_l; auto.
Qed.


Module Stable.
  Section Stable.
    Variable L: Loc.t -> bool.

    (* normal *)

    Definition normal_view (view: View.t): Prop :=
      forall loc (LOC: L loc), view.(View.rlx) loc = view.(View.pln) loc.

    Inductive normal_tview (tview:TView.t): Prop :=
    | normal_tview_intro
        (REL: forall loc, normal_view (tview.(TView.rel) loc))
        (CUR: normal_view tview.(TView.cur))
        (ACQ: normal_view tview.(TView.acq))
    .

    Definition normal_memory (mem: Memory.t): Prop :=
      forall loc from to val released
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        normal_view released.

    Lemma join_normal_view
          view1 view2
          (NORMAL1: normal_view view1)
          (NORMAL2: normal_view view2):
      normal_view (View.join view1 view2).
    Proof.
      ii. unfold normal_view in *.
      destruct view1, view2. ss.
      unfold TimeMap.join.
      rewrite NORMAL1, NORMAL2; ss.
    Qed.

    Lemma singleton_ur_normal_view loc ts:
      normal_view (View.singleton_ur loc ts).
    Proof. ss. Qed.

    Lemma singleton_rw_normal_view
          loc ts
          (LOC: ~ L loc):
      normal_view (View.singleton_rw loc ts).
    Proof.
      ii. ss.
      unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; ss. subst. ss.
    Qed.

    Lemma singleton_ur_if_normal_view
          b loc ts
          (LOC: ~ L loc):
      normal_view (View.singleton_ur_if b loc ts).
    Proof.
      unfold View.singleton_ur_if. condtac.
      - apply singleton_ur_normal_view.
      - apply singleton_rw_normal_view. ss.
    Qed.


    (* stable *)

    Definition stable_view (mem: Memory.t) (view: View.t): Prop :=
      forall loc from val released
        (LOC: L loc)
        (GET: Memory.get loc (view.(View.rlx) loc) mem =
              Some (from, Message.concrete val (Some released))),
        View.le released view.

    Definition stable_timemap (mem: Memory.t) (tm: TimeMap.t): Prop :=
      stable_view mem (View.mk tm tm).

    Inductive stable_tview (mem: Memory.t) (tview: TView.t): Prop :=
    | stable_tview_intro
        (REL: forall loc (LOC: ~ L loc), stable_view mem (tview.(TView.rel) loc))
        (CUR: stable_view mem tview.(TView.cur))
        (ACQ: stable_view mem tview.(TView.acq))
    .

    Definition stable_memory (rels: ReleaseWrites.t) (mem: Memory.t): Prop :=
      forall loc from to val released
        (LOC: ~ L loc \/ List.In (loc, to) rels)
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        stable_view mem released.


    Lemma future_stable_view
          mem1 mem2 view
          (CLOSED: Memory.closed_view view mem1)
          (STABLE: stable_view mem1 view)
          (MEM_FUTURE: Memory.future mem1 mem2):
      stable_view mem2 view.
    Proof.
      ii. inv CLOSED. specialize (RLX loc). des.
      exploit Memory.future_get1; try exact RLX; eauto. i. des.
      rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
      exploit STABLE; eauto.
    Qed.

    Lemma future_stable_tview
          mem1 mem2 tview
          (CLOSED: TView.closed tview mem1)
          (STABLE: stable_tview mem1 tview)
          (MEM_FUTURE: Memory.future mem1 mem2):
      stable_tview mem2 tview.
    Proof.
      destruct tview. inv CLOSED. inv STABLE. ss.
      econs; ss; eauto using future_stable_view.
    Qed.

    Lemma join_stable_view
          mem view1 view2
          (STABLE1: stable_view mem view1)
          (STABLE2: stable_view mem view2):
      stable_view mem (View.join view1 view2).
    Proof.
      ii. unfold stable_view in *.
      unfold View.join, TimeMap.join in GET. ss.
      exploit Time.join_cases. i. des.
      - erewrite x0 in GET.
        exploit STABLE1; eauto. i.
        etrans; eauto. apply View.join_l.
      - erewrite x0 in GET.
        exploit STABLE2; eauto. i.
        etrans; eauto. apply View.join_r.
    Qed.

    Lemma bot_stable_view
          mem
          (MEM: Memory.closed mem):
      stable_view mem View.bot.
    Proof.
      ii. inv MEM. rewrite INHABITED in *. inv GET.
    Qed.

    Lemma singleton_ur_stable_view
          mem loc ts
          (MEM: Memory.closed mem)
          (LOC: ~ L loc):
      stable_view mem (View.singleton_ur loc ts).
    Proof.
      ii. revert GET. ss.
      unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; subst; ss. i.
      inv MEM. rewrite INHABITED in *. inv GET.
    Qed.

    Lemma singleton_rw_stable_view
          mem loc ts
          (MEM: Memory.closed mem)
          (LOC: ~ L loc):
      stable_view mem (View.singleton_rw loc ts).
    Proof.
      ii. revert GET. ss.
      unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; subst; ss. i.
      inv MEM. rewrite INHABITED in *. inv GET.
    Qed.

    Lemma singleton_ur_if_stable_view
          mem b loc ts
          (MEM: Memory.closed mem)
          (LOC: ~ L loc):
      stable_view mem (View.singleton_ur_if b loc ts).
    Proof.
      unfold View.singleton_ur_if. condtac.
      - apply singleton_ur_stable_view; ss.
      - apply singleton_rw_stable_view; ss.
    Qed.

    Lemma stable_view_stable_timemap
          mem view
          (VIEW: View.wf view)
          (STABLE: stable_view mem view):
      stable_timemap mem view.(View.rlx).
    Proof.
      ii. etrans; [eapply STABLE|]; eauto.
      econs; ss; try refl. apply VIEW.
    Qed.

    Lemma join_stable_timemap
          mem tm1 tm2
          (STABLE1: stable_timemap mem tm1)
          (STABLE2: stable_timemap mem tm2):
      stable_timemap mem (TimeMap.join tm1 tm2).
    Proof.
      unfold stable_timemap in *.
      hexploit join_stable_view; [exact STABLE1|exact STABLE2|]. ss.
    Qed.

    Lemma stable_tview_read_tview
          mem tview
          loc from val released ord
          (WF: TView.wf tview)
          (NORMAL: normal_tview tview)
          (STABLE: stable_tview mem tview)
          (LOC: L loc)
          (GET: Memory.get loc (tview.(TView.cur).(View.rlx) loc) mem =
                Some (from, Message.concrete val released)):
      TView.read_tview tview loc (tview.(TView.cur).(View.rlx) loc) released ord = tview.
    Proof.
      inv STABLE. inv NORMAL.
      destruct tview. unfold TView.read_tview. ss. f_equal.
      - rewrite (@View.le_join_l cur); cycle 1.
        { unfold View.singleton_ur_if. condtac; ss.
          - unfold View.singleton_ur. econs; ss.
            + ii. unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
              condtac; try apply Time.bot_spec. subst.
              rewrite CUR0; ss. refl.
            + ii. unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
              condtac; try apply Time.bot_spec. subst. refl.
          - unfold View.singleton_rw. econs; ss; try apply TimeMap.bot_spec.
            ii. unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
            condtac; try apply Time.bot_spec. subst. refl.
        }
        condtac; try apply View.join_bot_r.
        apply View.le_join_l.
        destruct released; eauto. apply View.bot_spec.
      - rewrite (@View.le_join_l acq); cycle 1.
        { etrans; [|eapply WF]. ss.
          unfold View.singleton_ur_if. condtac; ss.
          - unfold View.singleton_ur. econs; ss.
            + ii. unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
              condtac; try apply Time.bot_spec. subst.
              rewrite CUR0; ss. refl.
            + ii. unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
              condtac; try apply Time.bot_spec. subst. refl.
          - unfold View.singleton_rw. econs; ss; try apply TimeMap.bot_spec.
            ii. unfold TimeMap.singleton, LocFun.add, LocFun.find, LocFun.init.
            condtac; try apply Time.bot_spec. subst. refl.
        }
        condtac; try apply View.join_bot_r.
        apply View.le_join_l.
        etrans; [|eapply WF]. ss.
        destruct released; eauto. apply View.bot_spec.
    Qed.

    Lemma stable_memory_tail
          loc to rels mem
          (STABLE: stable_memory ((loc, to) :: rels) mem):
      stable_memory rels mem.
    Proof.
      ii. des.
      - eapply STABLE; eauto.
      - eapply STABLE; eauto. right. s. right. ss.
    Qed.


    (* step *)

    Lemma promise
          rels tview1 promises1 mem1 loc from to msg promises2 mem2 kind
          (TVIEW1: TView.closed tview1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview tview1)
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 tview1)
          (STABLE_MEM1: stable_memory rels mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              normal_view released /\ stable_view mem2 released)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 tview1>> /\
      <<STABLE_MEM2: stable_memory rels mem2>>.
    Proof.
      inv PROMISE; ss.
      { (* add *)
        splits.
        - ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + eapply NORMAL_MEM1; eauto.
        - inv STABLE_TVIEW1. econs; ss; ii; revert GET.
          + erewrite Memory.add_o; eauto. condtac; ss; i.
            * des. subst. inv GET.
              exploit Memory.add_get0; try exact MEM. i. des.
              inv TVIEW1. specialize (REL0 loc0). inv REL0.
              specialize (RLX loc). des. congr.
            * eapply REL; eauto.
          + erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET.
            exploit Memory.add_get0; try exact MEM. i. des.
            inv TVIEW1. inv CUR0.
            specialize (RLX loc). des. congr.
          + erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET.
            exploit Memory.add_get0; try exact MEM. i. des.
            inv TVIEW1. inv ACQ0.
            specialize (RLX loc). des. congr.
        - ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          + guardH LOC. des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH LOC. guardH o. inv MEM1. exploit CLOSED; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.add_get1; try exact RLX; eauto. i.
            rewrite x0 in *. inv GET0.
            eapply STABLE_MEM1; eauto.
      }

      { (* split *)
        des. subst.
        splits; ss.
        - ii. revert GET.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH o. des. subst. inv GET.
            exploit Memory.split_get0; try exact MEM. i. des.
            eapply NORMAL_MEM1; eauto.
          + eapply NORMAL_MEM1; eauto.
        - inv STABLE_TVIEW1. econs; ss; ii; revert GET.
          + erewrite Memory.split_o; eauto. repeat condtac; ss; i.
            * des. subst. inv GET.
              exploit Memory.split_get0; try exact MEM. i. des.
              inv TVIEW1. specialize (REL0 loc0). inv REL0.
              specialize (RLX loc). des. congr.
            * guardH o. des. subst. inv GET.
              exploit Memory.split_get0; try exact MEM. i. des.
              eapply REL; eauto.
            * eapply REL; eauto.
          + erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
            * des. subst. inv GET.
              exploit Memory.split_get0; try exact MEM. i. des.
              inv TVIEW1. inv CUR0.
              specialize (RLX loc). des. congr.
            * guardH o. des. subst. inv GET.
              exploit Memory.split_get0; try exact MEM. i. des. eauto.
          + erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
            * des. subst. inv GET.
              exploit Memory.split_get0; try exact MEM. i. des.
              inv TVIEW1. inv ACQ0.
              specialize (RLX loc). des. congr.
            * guardH o. des. subst. inv GET.
              exploit Memory.split_get0; try exact MEM. i. des. eauto.
        - ii. revert GET.
          erewrite Memory.split_o; eauto. repeat condtac; ss; i.
          + guardH LOC. des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH LOC. guardH o. des. subst. inv GET.
            exploit Memory.split_get0; try exact MEM. i. des.
            inv MEM1. exploit CLOSED; try exact GET1. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.split_get1; try exact RLX; eauto. i. des.
            rewrite GET4 in *. inv GET0.
            eapply STABLE_MEM1; eauto.
          + guardH LOC. guardH o. guardH o0.
            inv MEM1. exploit CLOSED; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.split_get1; try exact RLX; eauto. i. des.
            rewrite GET2 in *. inv GET0.
            eapply STABLE_MEM1; eauto.
      }

      { (* lower *)
        splits; ss.
        - ii. revert GET.
          erewrite Memory.lower_o; eauto. condtac; ss; i.
          + des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + eapply NORMAL_MEM1; eauto.
        - inv STABLE_TVIEW1. econs; ss; ii; revert GET.
          + erewrite Memory.lower_o; eauto. condtac; ss; i.
            * des. subst. inv GET.
              exploit Memory.lower_get0; try exact MEM. i. des.
              inv MSG_LE. inv RELEASED. etrans; eauto.
              eapply REL; eauto.
            * eapply REL; eauto.
          + erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET.
            exploit Memory.lower_get0; try exact MEM. i. des.
            inv MSG_LE. inv RELEASED. etrans; eauto.
          + erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET.
            exploit Memory.lower_get0; try exact MEM. i. des.
            inv MSG_LE. inv RELEASED. etrans; eauto.
        - ii. revert GET.
          erewrite Memory.lower_o; eauto. condtac; ss; i.
          + guardH LOC. des. subst. inv GET.
            exploit MSG; eauto. i. des. eauto.
          + guardH LOC. guardH o. inv MEM1. exploit CLOSED; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.lower_get1; try exact RLX; eauto. i. des.
            rewrite GET2 in *. inv GET0. inv MSG_LE. inv RELEASED.
            etrans; eauto.
            eapply STABLE_MEM1; eauto.
      }

      { (* cancel *)
        splits; ss.
        - ii. revert GET.
          erewrite Memory.remove_o; eauto. condtac; ss; i.
          eapply NORMAL_MEM1; eauto.
        - inv STABLE_TVIEW1. econs; ss; ii; revert GET.
          + erewrite Memory.remove_o; eauto. condtac; ss; i.
            eapply REL; eauto.
          + erewrite Memory.remove_o; eauto. condtac; ss; i; eauto.
          + erewrite Memory.remove_o; eauto. condtac; ss; i; eauto.
        - ii. revert GET.
          erewrite Memory.remove_o; eauto. condtac; ss; i.
          guardH LOC. guardH o. inv MEM1. exploit CLOSED; eauto. i. des.
          inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
          specialize (RLX loc1). des.
          exploit Memory.remove_get1; try exact RLX; eauto. i. des.
          { subst. exploit Memory.remove_get0; try exact MEM. i. des. congr. }
          rewrite GET2 in *. inv GET0.
          eapply STABLE_MEM1; eauto.
      }
    Qed.

    Lemma promise_step
          rels lc1 mem1 loc from to msg lc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              normal_view released /\ stable_view mem2 released)
          (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 lc2.(Local.tview)>> /\
      <<STABLE_MEM2: stable_memory rels mem2>> /\
      <<RELS_WF2: ReleaseWrites.wf rels lc2 mem2>>.
    Proof.
      inv STEP. exploit promise; try apply WF1; eauto. i. des.
      splits; auto. ii. ss.
      exploit RELS_WF1; eauto. i. des. split.
      - inv PROMISE.
        + erewrite Memory.add_o; eauto. condtac; ss.
          des. subst. exploit Memory.add_get0; try exact MEM. i. des. congr.
        + erewrite Memory.split_o; eauto. repeat condtac; ss.
          * des. subst. exploit Memory.split_get0; try exact MEM. i. des. congr.
          * guardH o. des. subst.
            exploit Memory.split_get0; try exact PROMISES. i. des. congr.
        + erewrite Memory.lower_o; eauto. condtac; ss.
          des. subst. exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
        + erewrite Memory.remove_o; eauto. condtac; ss.
      - destruct (Memory.op_kind_is_cancel kind) eqn:KIND.
        + destruct kind; ss. inv PROMISE.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. exploit Memory.remove_get0; try exact MEM. i. des. congr.
        + exploit Memory.promise_get1; eauto. i. des. inv MSG_LE. eauto.
    Qed.

    Lemma read_step_loc_cur
          rels lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (LOC: L loc)
          (TO: to = lc1.(Local.tview).(TView.cur).(View.rlx) loc)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<LC2: lc2 = lc1>>.
    Proof.
      unnw. inv STEP. destruct lc1. f_equal; ss.
      unfold TView.read_tview. condtac; ss; [|condtac; [|destruct ord]; ss].
      - condtac; [|destruct ord]; ss.
        destruct tview; ss. f_equal; ss.
        + repeat rewrite View.le_join_l; ss.
          * eapply View.singleton_ur_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
          * destruct released; try apply View.bot_spec. ss.
            inv STABLE_TVIEW1. eauto.
          * eapply View.singleton_ur_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
        + repeat rewrite View.le_join_l; ss.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_ur_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            destruct released; try apply View.bot_spec. ss.
            inv STABLE_TVIEW1. eauto.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_ur_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
      - destruct tview; ss. f_equal; ss.
        + repeat rewrite View.le_join_l; ss.
          * eapply View.singleton_ur_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
          * destruct released; try apply View.bot_spec.
          * eapply View.singleton_ur_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
        + repeat rewrite View.le_join_l; ss.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_ur_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            destruct released; try apply View.bot_spec. ss.
            inv STABLE_TVIEW1. eauto.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_ur_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
      - destruct tview; ss. f_equal; ss.
        + repeat rewrite View.le_join_l; ss.
          * eapply View.singleton_rw_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
          * destruct released; try apply View.bot_spec.
          * eapply View.singleton_rw_spec; try apply WF1.
            inv NORMAL_TVIEW1. rewrite CUR; ss. refl.
        + repeat rewrite View.le_join_l; ss.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_rw_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            destruct released; try apply View.bot_spec.
          * inv WF1. ss. inv TVIEW_WF. ss. etrans; eauto.
            eapply View.singleton_rw_spec; ss.
            inv NORMAL_TVIEW1. rewrite CUR0; ss. refl.
    Qed.

    Lemma read_step_loc_ra
          rels lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (LOC: L loc)
          (REL: List.In (loc, to) rels)
          (ORD: Ordering.le Ordering.acqrel ord)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<STABLE_TVIEW2: stable_tview mem1 lc2.(Local.tview)>> /\
      <<RELS_WF2: ReleaseWrites.wf rels lc2 mem1>>.
    Proof.
      inv STEP. ss. splits; ss.
      - inv NORMAL_TVIEW1. econs; ss.
        + repeat eapply join_normal_view; ss.
          { destruct ord; ss. }
          { condtac; ss. destruct released; ss; eauto. }
        + repeat eapply join_normal_view; ss.
          { destruct ord; ss. }
          { condtac; ss. destruct released; ss; eauto. }
      - inv STABLE_TVIEW1. econs; ss.
        + unfold View.singleton_ur_if.
          repeat (condtac; [|destruct ord; ss]). ii.
          destruct (Loc.eq_dec loc loc0); subst; ss.
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; ss. i.
            rewrite time_le_join_l in GET0; cycle 1.
            { etrans; [|eapply Time.join_r].
              inv MEM1. exploit CLOSED; try exact GET. i. des.
              inv MSG_TS. ss. }
            rewrite time_le_join_r in GET0; cycle 1.
            { inv READABLE. auto. }
            rewrite GET0 in *. inv GET. ss.
            etrans; [|apply View.join_r]. refl.
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; try congr; ss. i.
            rewrite (@time_le_join_l _ Time.bot) in GET0; try apply Time.bot_spec.
            exploit Time.join_cases. i. des.
            { rewrite x0 in GET0.
              exploit CUR; eauto. i. etrans; eauto.
              etrans; [|apply View.join_l].
              etrans; [|apply View.join_l].
              refl. }
            { rewrite x0 in GET0. destruct released; ss; cycle 1.
              { unfold TimeMap.bot in *.
                inv MEM1. rewrite INHABITED in GET0. ss. }
              exploit STABLE_MEM1; try exact GET; eauto. i.
              etrans; eauto.
              etrans; [|apply View.join_r].
              refl. }
        + unfold View.singleton_ur_if.
          repeat (condtac; [|destruct ord; ss]). ii.
          destruct (Loc.eq_dec loc loc0); subst; ss.
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; ss. i.
            rewrite Time.join_assoc in GET0.
            rewrite (@time_le_join_l to) in GET0; cycle 1.
            { inv MEM1. exploit CLOSED; try exact GET. i. des.
              inv MSG_TS. ss. }
            exploit Time.join_cases. i. des.
            { rewrite x0 in GET0.
              exploit ACQ; eauto. i. etrans; eauto.
              etrans; [|apply View.join_l].
              etrans; [|apply View.join_l].
              refl. }
            { rewrite x0 in GET0. rewrite GET0 in *. inv GET. ss.
              etrans; [|apply View.join_r]. 
              refl. }
          * unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
            revert GET0. condtac; try congr; ss. i.
            rewrite (@time_le_join_l _ Time.bot) in GET0; try apply Time.bot_spec.
            exploit Time.join_cases. i. des.
            { rewrite x0 in GET0.
              exploit ACQ; eauto. i. etrans; eauto.
              etrans; [|apply View.join_l].
              etrans; [|apply View.join_l].
              refl. }
            { rewrite x0 in GET0. destruct released; ss; cycle 1.
              { unfold TimeMap.bot in *.
                inv MEM1. rewrite INHABITED in GET0. ss. }
              exploit STABLE_MEM1; try exact GET; eauto. i.
              etrans; eauto.
              etrans; [|apply View.join_r].
              refl. }
    Qed.

    Lemma read_step_other
          rels lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (LOC: ~ L loc)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<STABLE_TVIEW2: stable_tview mem1 lc2.(Local.tview)>> /\
      <<RELS_WF2: ReleaseWrites.wf rels lc2 mem1>>.
    Proof.
      inv STEP. ss. splits; ss.
      - inv NORMAL_TVIEW1. econs; ss.
        + repeat apply join_normal_view; ss.
          * apply singleton_ur_if_normal_view. ss.
          * condtac; ss. destruct released; ss. eauto.
        + repeat apply join_normal_view; ss.
          * apply singleton_ur_if_normal_view. ss.
          * condtac; ss. destruct released; ss. eauto.
      - inv STABLE_TVIEW1. econs; ss.
        + repeat apply join_stable_view; ss.
          * apply singleton_ur_if_stable_view; ss.
          * condtac; ss.
            { destruct released; ss.
              - eapply STABLE_MEM1; eauto.
              - apply bot_stable_view; ss. }
            { apply bot_stable_view; ss. }
        + repeat apply join_stable_view; ss.
          * apply singleton_ur_if_stable_view; ss.
          * condtac; ss.
            { destruct released; ss.
              - eapply STABLE_MEM1; eauto.
              - apply bot_stable_view; ss. }
            { apply bot_stable_view; ss. }
    Qed.

    Lemma write_step_loc
          rels lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (WF_RELEASEDM: View.opt_wf releasedm)
          (CLOSED_RELEASEDM: Memory.closed_opt_view releasedm mem1)
          (NORMAL_RELEASEDM: normal_view releasedm.(View.unwrap))
          (RELEASEDM: View.le releasedm.(View.unwrap) lc1.(Local.tview).(TView.cur))
          (LOC: L loc)
          (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 lc2.(Local.tview)>> /\
      <<STABLE_MEM2: stable_memory (if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels) mem2>> /\
      <<RELS_WF2: ReleaseWrites.wf (if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels) lc2 mem2>>.
    Proof.
      exploit Local.write_step_future; eauto. i. des.
      inv STEP. inv WRITE. ss.
      assert (NORMAL_TVIEW2: normal_tview (TView.write_tview (Local.tview lc1) sc1 loc to ord)).
      { inv NORMAL_TVIEW1.
        econs; ss; i; try by (apply join_normal_view; ss).
        unfold LocFun.add. condtac; eauto. subst.
        condtac; apply join_normal_view; ss. }
      assert (STABLE_TVIEW2: stable_tview mem2 (TView.write_tview (Local.tview lc1) sc1 loc to ord)).
      { inv STABLE_TVIEW1. econs; ss; i.
        - condtac; ss.
          { unfold LocFun.add, LocFun.find.
            condtac; ss; subst; ii; ss.
            inv WF1. inv TVIEW_WF. inv TVIEW_CLOSED.
            destruct (REL1 loc0). specialize (RLX loc1). des.
            exploit Memory.promise_get1; try exact RLX; eauto.
            { inv PROMISE; ss. }
            i. des.
            rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
            etrans; eauto. eapply REL; eauto.
          }
          { unfold LocFun.add, LocFun.find.
            condtac; ss; subst; ii; ss.
            inv WF1. inv TVIEW_WF. inv TVIEW_CLOSED.
            destruct (REL1 loc0). specialize (RLX loc1). des.
            exploit Memory.promise_get1; try exact RLX; eauto.
            { inv PROMISE; ss. }
            i. des.
            rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
            etrans; eauto. eapply REL; eauto.
          }
        - ii. revert GET. ss.
          unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          condtac; ss; subst; i.
          + rewrite time_le_join_r in GET; cycle 1.
            { inv WRITABLE. econs. ss. }
            exploit Memory.promise_get0; try exact PROMISE.
            { inv PROMISE; ss. }
            i. des.
            rewrite GET in *. inv GET_MEM.
            revert H2. unfold TView.write_released. condtac; ss.
            unfold LocFun.add. repeat condtac; ss.
            * i. inv H2.
              repeat eapply View.join_spec; eauto using View.join_l, View.join_r.
            * i. inv H2.
              repeat eapply View.join_spec; eauto using View.join_l, View.join_r.
              etrans; try eapply WF1. apply View.join_l.
          + rewrite time_le_join_l in GET; try by apply Time.bot_spec.
            etrans; [|apply View.join_l].
            revert GET. inv PROMISE.
            { erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
              des. subst. inv GET. ss. }
            { erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
              - des. subst. inv GET. ss.
              - guardH o. des. subst. inv GET. ss. }
            { erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
              des. subst. inv GET. ss. }
            { exploit Memory.remove_get0; try exact PROMISES. i. des.
              exploit Memory.remove_get0; try exact REMOVE. i. des.
              congr. }
        - ii.  revert GET. ss.
          unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          condtac; ss; subst; i.
          + exploit Time.join_cases. i. des.
            * erewrite x0 in GET.
              inv WF1. inv TVIEW_CLOSED. inv ACQ0.
              destruct (RLX loc). des.
              exploit Memory.promise_get1; try exact H; eauto.
              { inv PROMISE; ss. }
              i. des.
              rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
              etrans; eauto.
              etrans; [|apply View.join_l].
              eauto.
            * erewrite x0 in GET.
              exploit Memory.promise_get0; try exact PROMISE.
              { inv PROMISE; ss. }
              i. des.
              rewrite GET in *. inv GET_MEM.
              revert H2. unfold TView.write_released. condtac; ss.
              unfold LocFun.add. repeat condtac; ss.
              { i. inv H2.
                repeat eapply View.join_spec; try apply View.join_r.
                - etrans; eauto.
                  etrans; try eapply WF1. apply View.join_l.
                - etrans; try eapply WF1. apply View.join_l. }
              { i. inv H2.
                repeat eapply View.join_spec; try apply View.join_r.
                - etrans; eauto.
                  etrans; try eapply WF1. apply View.join_l.
                - etrans; try eapply WF1. etrans; try eapply WF1. apply View.join_l. }
          + rewrite time_le_join_l in GET; try by apply Time.bot_spec.
            etrans; [|apply View.join_l].
            revert GET. inv PROMISE.
            { erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
              des. subst. inv GET. ss. }
            { erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
              - des. subst. inv GET. ss.
              - guardH o. des. subst. inv GET. ss. }
            { erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
              des. subst. inv GET. ss. }
            { exploit Memory.remove_get0; try exact PROMISES. i. des.
              exploit Memory.remove_get0; try exact REMOVE. i. des.
              congr. }
      }

      assert (NORMAL_RELEASED: forall released,
                 TView.write_released (Local.tview lc1) sc1 loc to releasedm ord = Some released ->
                 normal_view released).
      { unfold TView.write_released. repeat (condtac; ss).
        unfold LocFun.add. condtac; ss.
        - i. inv H. repeat apply join_normal_view; ss. apply NORMAL_TVIEW1.
        - i. inv H. unfold LocFun.add. condtac; ss.
          repeat apply join_normal_view; ss. apply NORMAL_TVIEW1. }

      condtac; ss.
      { assert (RELEASED: TView.write_released lc1.(Local.tview) sc1 loc to releasedm ord =
                          Some (View.join (View.singleton_ur loc to) lc1.(Local.tview).(TView.cur))).
        { unfold TView.write_released. repeat (condtac; ss); cycle 1.
          { destruct ord; ss. }
          f_equal.
          unfold LocFun.add. condtac; ss.
          rewrite (View.join_comm (View.singleton_ur loc to)).
          apply View.antisym; cycle 1.
          { etrans; [|eapply View.join_r]. refl. }
          apply View.join_spec; try refl.
          etrans; [|eapply View.join_l]. ss.
        }
        assert (STABLE_RELEASED:
                  stable_view mem2 (View.join (View.singleton_ur loc to) lc1.(Local.tview).(TView.cur))).
        { rewrite RELEASED in *. ii. revert GET. ss.
          unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find. condtac; ss.
          - subst. replace (Time.join to (View.rlx (TView.cur (Local.tview lc1)) loc)) with to; cycle 1.
            { rewrite time_le_join_l; ss.
              inv WRITABLE. econs. ss. }
            exploit Memory.promise_get0; try exact PROMISE; try by (inv PROMISE; ss). i. des.
            rewrite GET_MEM in *. inv GET. refl.
          - rewrite time_le_join_r; try by apply Time.bot_spec. i.
            inv WF1. inv TVIEW_CLOSED. inv CUR. specialize (RLX loc0). des.
            exploit Memory.promise_get1; try exact RLX; eauto; try by (inv PROMISE; ss). i. des.
            rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED0.
            etrans; eauto. etrans; [|apply View.join_r].
            eapply STABLE_TVIEW1; eauto.
        }
        exploit promise; try exact PROMISE; try apply WF1; eauto.
        { i. inv MSG. rewrite RELEASED in *. inv H1. split; ss.
          apply join_normal_view.
          eauto using singleton_ur_normal_view.
          apply NORMAL_TVIEW1. }
        i. des. splits; auto.
        - ii. ss. des.
          + eapply STABLE_MEM2; eauto.
          + inv LOC0. exploit Memory.promise_get0; try exact PROMISE; try by (inv PROMISE; ss). i. des.
            rewrite GET in *. inv GET_MEM.
            rewrite RELEASED in *. inv H2.
            eapply STABLE_RELEASED; eauto.
          + eapply STABLE_MEM2; eauto.
        - ii. ss. des.
          + inv IN. exploit Memory.promise_get2; eauto; try by (inv PROMISE; ss). i. des.
            exploit Memory.remove_get0; eauto. i. des. eauto.
          + exploit RELS_WF1; eauto. i. des.
            exploit Memory.promise_get1; try exact x0; eauto; try by (inv PROMISE; ss). i. des.
            inv MSG_LE. esplits; eauto.
            erewrite Memory.remove_o; eauto. condtac; ss.
            guardH o. inv PROMISE; ss.
            * erewrite Memory.add_o; eauto. condtac; ss.
            * erewrite Memory.split_o; eauto. repeat condtac; ss.
              guardH o0. des. subst.
              exploit Memory.split_get0; try exact PROMISES. i. des. congr.
            * erewrite Memory.lower_o; eauto. condtac; ss.
      }

      splits; auto.
      - ii. revert GET. inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss.
          * i. des. subst. inv GET.
            eapply NORMAL_RELEASED; eauto.
          * i. eapply NORMAL_MEM1; eauto.
        + erewrite Memory.split_o; eauto. repeat condtac; ss.
          * i. des. subst. inv GET.
            eapply NORMAL_RELEASED; eauto.
          * guardH o. des. subst. i. inv GET.
            exploit Memory.split_get0; try exact MEM. i. des.
            eapply NORMAL_MEM1; eauto.
          * i. eapply NORMAL_MEM1; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss.
          * i. des. subst. inv GET.
            eapply NORMAL_RELEASED; eauto.
          * i. eapply NORMAL_MEM1; eauto.
      - ii. guardH LOC0. revert GET. inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss.
          * i. des. subst. inv GET. unguard. des; ss. subst.
            exploit RELS_WF1; eauto. i. des.
            exploit Memory.add_get0; try exact MEM. i. des. congr.
          * guardH o. i. inv MEM1. exploit CLOSED; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.add_get1; try exact RLX; eauto. i.
            rewrite x0 in *. inv GET0. eapply STABLE_MEM1; eauto.
        + erewrite Memory.split_o; eauto. repeat condtac; ss.
          * i. des. subst. inv GET. unguard. des; ss.
            exploit RELS_WF1; eauto. i. des.
            exploit Memory.split_get0; try exact MEM. i. des. congr.
          * guardH o. i. des. subst. inv GET.
            exploit Memory.split_get0; try exact MEM. i. des.
            inv MEM1. exploit CLOSED; try exact GET1. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.split_get1; try exact RLX; eauto. i. des.
            rewrite GET4 in *. inv GET0.
            eapply STABLE_MEM1; eauto.
          * guardH o. guardH o0. i.
            inv MEM1. exploit CLOSED; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.split_get1; try exact RLX; eauto. i. des.
            rewrite GET2 in *. inv GET0. eapply STABLE_MEM1; eauto.
        + erewrite Memory.lower_o; eauto. condtac; ss.
          * i. des. subst. inv GET. unguard. des; ss.
            exploit RELS_WF1; eauto. i. des.
            exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
          * guardH o. i. inv MEM1. exploit CLOSED; eauto. i. des.
            inv MSG_CLOSED. inv CLOSED0. inv CLOSED1.
            specialize (RLX loc1). des.
            exploit Memory.lower_get1; try exact RLX; eauto. i. des. inv MSG_LE.
            rewrite GET2 in *. inv GET0. inv RELEASED.
            etrans; eauto. eapply STABLE_MEM1; eauto.
      - ii. ss. exploit RELS_WF1; eauto. i. des.
        exploit Memory.promise_get1; try exact x0; eauto; try by (inv PROMISE; ss). i. des.
        inv MSG_LE. esplits; eauto.
        erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
        inv PROMISE; ss.
        + erewrite Memory.add_o; eauto. condtac; ss.
        + erewrite Memory.split_o; eauto. repeat condtac; ss.
          guardH o0. des. subst.
          exploit Memory.split_get0; try exact PROMISES. i. des. congr.
        + erewrite Memory.lower_o; eauto. condtac; ss.
    Qed.

    Lemma write_step_loc_None
          rels lc1 sc1 mem1 loc from to val released ord lc2 sc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (LOC: L loc)
          (STEP: Local.write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 lc2.(Local.tview)>> /\
      <<STABLE_MEM2: stable_memory (if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels) mem2>> /\
      <<RELS_WF2: ReleaseWrites.wf (if Ordering.le Ordering.acqrel ord then (loc, to) :: rels else rels) lc2 mem2>>.
    Proof.
      eapply write_step_loc; eauto; ss.
      - apply View.bot_spec.
    Qed.

    Lemma write_step_other
          rels lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (LOC: ~ L loc)
          (WF_RELEASEDM: View.opt_wf releasedm)
          (CLOSED_RELEASEDM: Memory.closed_opt_view releasedm mem1)
          (NORMAL_RELEASEDM: normal_view releasedm.(View.unwrap))
          (STABLE_RELEASEDM: stable_view mem1 releasedm.(View.unwrap))
          (RELEASEDM: View.le releasedm.(View.unwrap) lc1.(Local.tview).(TView.cur))
          (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 lc2.(Local.tview)>> /\
      <<STABLE_MEM2: stable_memory rels mem2>> /\
      <<RELS_WF2: ReleaseWrites.wf rels lc2 mem2>>.
    Proof.
      exploit Local.write_step_future; eauto. i. des.
      inv STEP. inv WRITE. ss.
      assert (NORMAL_TVIEW2: normal_tview (TView.write_tview (Local.tview lc1) sc1 loc to ord)).
      { inv NORMAL_TVIEW1.
        econs; ss; i; try by (apply join_normal_view; ss).
        unfold LocFun.add. condtac; eauto. subst.
        condtac; apply join_normal_view; ss. }
      assert (STABLE_TVIEW2: stable_tview mem2 (TView.write_tview (Local.tview lc1) sc1 loc to ord)).
      { inv STABLE_TVIEW1. econs; ss; i.
        { condtac; ss.
          - unfold LocFun.add, LocFun.find.
            condtac; ss; subst; ii; ss.
            + revert GET.
              unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
              condtac; ss; i.
              * subst. congr.
              * rewrite time_le_join_l in GET; try by apply Time.bot_spec.
                etrans; [|eapply View.join_l].
                revert GET. inv PROMISE.
                { erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
                  des. subst. inv GET. ss. }
                { erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
                  - des. subst. inv GET. ss.
                  - guardH o. des. subst. inv GET. ss. }
                { erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
                  des. subst. inv GET. ss. }
                { exploit Memory.remove_get0; try exact PROMISES. i. des.
                  exploit Memory.remove_get0; try exact REMOVE. i. des.
                  congr. }
            + inv WF1. inv TVIEW_WF. inv TVIEW_CLOSED.
              destruct (REL1 loc0). specialize (RLX loc1). des.
              exploit Memory.promise_get1; try exact RLX; eauto.
              { inv PROMISE; ss. }
              i. des.
              rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
              etrans; eauto. eapply REL; eauto.
          - unfold LocFun.add, LocFun.find.
            condtac; ss; subst; ii; ss.
            + revert GET.
              unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
              condtac; ss; i.
              * subst. congr.
              * rewrite time_le_join_l in GET; try by apply Time.bot_spec.
                etrans; [|eapply View.join_l].
                revert GET. inv PROMISE.
                { erewrite Memory.add_o; eauto. condtac; ss; i.
                  - des. subst. inv GET. ss.
                  - eapply REL; eauto. }
                { erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
                  - des. subst. inv GET. ss.
                  - guardH o. des. subst. inv GET. ss.
                  - eapply REL; eauto. }
                { erewrite Memory.lower_o; eauto. condtac; ss; i.
                  - des. subst. inv GET. ss.
                  - eapply REL; eauto. }
                { exploit Memory.remove_get0; try exact PROMISES. i. des.
                  exploit Memory.remove_get0; try exact REMOVE. i. des.
                  congr. }
            + inv WF1. inv TVIEW_WF. inv TVIEW_CLOSED.
              destruct (REL1 loc0). specialize (RLX loc1). des.
              exploit Memory.promise_get1; try exact RLX; eauto.
              { inv PROMISE; ss. }
              i. des.
              rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
              etrans; eauto. eapply REL; eauto.
        }
        { ii. revert GET. ss.
          unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          condtac; ss; subst; i; try congr.
          rewrite time_le_join_l in GET; try by apply Time.bot_spec.
          etrans; [|apply View.join_l].
          revert GET. inv PROMISE.
          { erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET. ss. }
          { erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
            - des. subst. inv GET. ss.
            - guardH o. des. subst. inv GET. ss. }
          { erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET. ss. }
          { exploit Memory.remove_get0; try exact PROMISES. i. des.
            exploit Memory.remove_get0; try exact REMOVE. i. des.
            congr. }
        }
        { ii.  revert GET. ss.
          unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          condtac; ss; subst; i; try congr.
          rewrite time_le_join_l in GET; try by apply Time.bot_spec.
          etrans; [|apply View.join_l].
          revert GET. inv PROMISE.
          { erewrite Memory.add_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET. ss. }
          { erewrite Memory.split_o; eauto. repeat condtac; ss; i; eauto.
            - des. subst. inv GET. ss.
            - guardH o. des. subst. inv GET. ss. }
          { erewrite Memory.lower_o; eauto. condtac; ss; i; eauto.
            des. subst. inv GET. ss. }
          { exploit Memory.remove_get0; try exact PROMISES. i. des.
            exploit Memory.remove_get0; try exact REMOVE. i. des.
            congr. }
        }
      }

      exploit promise; try exact PROMISE; try apply WF1; eauto.
      { unfold TView.write_released. repeat (condtac; ss).
        - unfold LocFun.add. condtac; ss.
          i. inv MSG. split.
          + repeat apply join_normal_view; ss. apply NORMAL_TVIEW1.
          + ii. revert GET.
            destruct (Loc.eq_dec loc loc0); subst; try congr.
            ss. unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
            condtac; ss; try congr.
            rewrite (@time_le_join_l _ Time.bot); try by apply Time.bot_spec. i.
            rewrite <- View.join_assoc.
            etrans; [|apply View.join_l].
            eapply future_stable_view; try eapply GET; try eapply join_stable_view; eauto.
            * eapply Memory.join_closed_view; ss.
              { inv CLOSED_RELEASEDM; ss.
                apply Memory.closed_view_bot. apply MEM1. }
              { apply WF1. }
            * apply STABLE_TVIEW1.
        - unfold LocFun.add. condtac; ss.
          i. inv MSG. split.
          + repeat apply join_normal_view; ss. apply NORMAL_TVIEW1.
          + ii. revert GET.
            destruct (Loc.eq_dec loc loc0); subst; try congr.
            ss. unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
            condtac; ss; try congr.
            rewrite (@time_le_join_l _ Time.bot); try by apply Time.bot_spec. i.
            rewrite <- View.join_assoc.
            etrans; [|apply View.join_l].
            eapply future_stable_view; try eapply GET; try eapply join_stable_view; eauto.
            * eapply Memory.join_closed_view; ss.
              { inv CLOSED_RELEASEDM; ss.
                apply Memory.closed_view_bot. apply MEM1. }
              { apply WF1. }
            * apply STABLE_TVIEW1. ss.
      }

      i. des. splits; auto.
      ii. exploit RELS_WF1; eauto. i. des.
      exploit Memory.promise_get1; try exact x0; eauto; try by (inv PROMISE; ss). i. des. inv MSG_LE.
      esplits; eauto. s.
      erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
      inv PROMISE; ss.
      - erewrite Memory.add_o; eauto. condtac; ss.
      - erewrite Memory.split_o; eauto. repeat condtac; ss.
        guardH o0. des. subst.
        exploit Memory.split_get0; try exact PROMISES. i. des. congr.
      - erewrite Memory.lower_o; eauto. condtac; ss.
    Qed.

    Lemma write_step_other_None
          rels lc1 sc1 mem1 loc from to val released ord lc2 sc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (LOC: ~ L loc)
          (STEP: Local.write_step lc1 sc1 mem1 loc from to val None released ord lc2 sc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<NORMAL_MEM2: normal_memory mem2>> /\
      <<STABLE_TVIEW2: stable_tview mem2 lc2.(Local.tview)>> /\
      <<STABLE_MEM2: stable_memory rels mem2>> /\
      <<RELS_WF2: ReleaseWrites.wf rels lc2 mem2>>.
    Proof.
      eapply write_step_other; eauto; ss.
      - apply bot_stable_view. apply MEM1.
      - apply View.bot_spec.
    Qed.

    Lemma fence_step
          rels lc1 sc1 mem1 ordr ordw lc2 sc2
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (NORMAL_TVIEW1: normal_tview lc1.(Local.tview))
          (NORMAL_MEM1: normal_memory mem1)
          (STABLE_TVIEW1: stable_tview mem1 lc1.(Local.tview))
          (STABLE_SC1: stable_timemap mem1 sc1)
          (STABLE_MEM1: stable_memory rels mem1)
          (RELS_WF1: ReleaseWrites.wf rels lc1 mem1)
          (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
      <<NORMAL_TVIEW2: normal_tview lc2.(Local.tview)>> /\
      <<STABLE_TVIEW2: stable_tview mem1 lc2.(Local.tview)>> /\
      <<STABLE_SC2: stable_timemap mem1 sc2>> /\
      <<RELS_WF2: ReleaseWrites.wf rels lc2 mem1>>.
    Proof.
      inv STEP. ss. splits; ss.
      - inv NORMAL_TVIEW1.
        econs; ss; i; repeat (condtac; ss).
        + apply join_normal_view; ss.
        + apply join_normal_view; ss.
      - inv STABLE_TVIEW1.
        econs; ss; i; repeat (condtac; ss); eauto.
        + unfold TView.write_fence_sc. repeat (condtac; ss).
          * hexploit join_stable_view; [apply STABLE_SC1| apply ACQ|]. i.
            unfold View.join in H. ss. ii.
            etrans; [eapply H; eauto|].
            econs; try refl. ss.
            apply TimeMap.join_spec.
            { apply TimeMap.join_l. }
            { etrans; [|apply TimeMap.join_r]. apply WF1. }
          * hexploit join_stable_view; [apply STABLE_SC1| apply CUR|]. i.
            unfold View.join in H. ss. ii.
            etrans; [eapply H; eauto|].
            econs; try refl. ss.
            apply TimeMap.join_spec.
            { apply TimeMap.join_l. }
            { etrans; [|apply TimeMap.join_r]. apply WF1. }
        + unfold TView.write_fence_sc. repeat (condtac; ss).
          * hexploit join_stable_view; [apply STABLE_SC1| apply ACQ|]. i.
            unfold View.join in H. ss. ii.
            etrans; [eapply H; eauto|].
            econs; try refl. ss.
            apply TimeMap.join_spec.
            { apply TimeMap.join_l. }
            { etrans; [|apply TimeMap.join_r]. apply WF1. }
          * hexploit join_stable_view; [apply STABLE_SC1| apply CUR|]. i.
            unfold View.join in H. ss. ii.
            etrans; [eapply H; eauto|].
            econs; try refl. ss.
            apply TimeMap.join_spec.
            { apply TimeMap.join_l. }
            { etrans; [|apply TimeMap.join_r]. apply WF1. }
        + unfold TView.write_fence_sc. repeat (condtac; ss).
          * apply join_stable_view; ss.
            hexploit join_stable_view; [apply STABLE_SC1| apply ACQ|]. i.
            unfold View.join in H. ss. ii.
            etrans; [eapply H; eauto|].
            econs; try refl. ss.
            apply TimeMap.join_spec.
            { apply TimeMap.join_l. }
            { etrans; [|apply TimeMap.join_r]. apply WF1. }
          * apply join_stable_view; ss.
            hexploit join_stable_view; [apply STABLE_SC1| apply CUR|]. i.
            unfold View.join in H. ss. ii.
            etrans; [eapply H; eauto|].
            econs; try refl. ss.
            apply TimeMap.join_spec.
            { apply TimeMap.join_l. }
            { etrans; [|apply TimeMap.join_r]. apply WF1. }
        + rewrite View.le_join_l; try by apply View.bot_spec. ss.
      - unfold TView.write_fence_sc. repeat (condtac; ss).
        + eapply join_stable_timemap; ss.
          apply stable_view_stable_timemap.
          * apply WF1.
          * apply STABLE_TVIEW1.
        + eapply join_stable_timemap; ss.
          apply stable_view_stable_timemap.
          * apply WF1.
          * apply STABLE_TVIEW1.
    Qed.
  End Stable.
End Stable.
