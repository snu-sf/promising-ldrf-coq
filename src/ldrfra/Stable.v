Require Import Lia.
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

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import OrdStep.
Require Import Writes.

Set Implicit Arguments.


Module Normal.
  Section Normal.
    Variable L: Loc.t -> bool.

    Definition normal_view (view: View.t): Prop :=
      forall loc (LOC: L loc), (View.rlx view) loc = (View.pln view) loc.

    Variant normal_tview (tview:TView.t): Prop :=
    | normal_tview_intro
        (REL: forall loc, normal_view ((TView.rel tview) loc))
        (CUR: normal_view (TView.cur tview))
        (ACQ: normal_view (TView.acq tview))
    .

    Definition normal_memory (mem: Memory.t): Prop :=
      forall loc from to val released
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        normal_view released.

    Inductive normal_thread {lang: language} (e: Thread.t lang): Prop :=
    | normal_thread_intro
        (NORMAL_TVIEW: normal_tview (Local.tview (Thread.local e)))
        (NORMAL_MEMORY: normal_memory (Thread.memory e))
    .
    Hint Constructors normal_thread: core.

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

    Lemma get_normal_view
          mem loc from to val released
          (MEM: normal_memory mem)
          (GET: Memory.get loc to mem = Some (from, Message.concrete val released)):
      normal_view (View.unwrap released).
    Proof.
      destruct released; ss. eapply MEM; eauto.
    Qed.

    Lemma promise
          promises1 mem1 loc from to msg promises2 mem2 kind
          (NORMAL_MEM1: normal_memory mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              normal_view released)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      <<NORMAL_MEM2: normal_memory mem2>>.
    Proof.
      ii. revert GET. inv PROMISE; ss.
      - erewrite Memory.add_o; eauto. condtac; ss; i.
        + inv GET. eapply MSG; eauto.
        + eapply NORMAL_MEM1; eauto.
      - erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        + inv GET. eapply MSG; eauto.
        + guardH o. des. inv GET.
          exploit Memory.split_get0; try exact MEM. i. des.
          eapply NORMAL_MEM1; eauto.
        + eapply NORMAL_MEM1; eauto.
      - erewrite Memory.lower_o; eauto. condtac; ss; i.
        + inv GET. eapply MSG; eauto.
        + eapply NORMAL_MEM1; eauto.
      - erewrite Memory.remove_o; eauto. condtac; ss; i.
        eapply NORMAL_MEM1; eauto.
    Qed.

    Lemma write
          promises1 mem1 loc from to msg promises2 mem2 kind
          (NORMAL_MEM1: normal_memory mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              normal_view released)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      <<NORMAL_MEM2: normal_memory mem2>>.
    Proof.
      inv WRITE. eauto using promise.
    Qed.

    Lemma write_na
          ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          (NORMAL_MEM1: normal_memory mem1)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
      <<NORMAL_MEM2: normal_memory mem2>>.
    Proof.
      induction WRITE.
      - eapply write; eauto; ss.
      - apply IHWRITE. eapply write; eauto.
        unguard. des; subst; ss.
    Qed.

    Lemma promise_step
          lc1 mem1 loc from to msg lc2 mem2 kind
          (NORMAL_TVIEW1: normal_tview (Local.tview lc1))
          (NORMAL_MEM1: normal_memory mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              normal_view released)
          (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind):
      <<NORMAL_TVIEW2: normal_tview (Local.tview lc2)>> /\
      <<NORMAL_MEM2: normal_memory mem2>>.
    Proof.
      inv STEP. splits; ss. eapply promise; eauto.
    Qed.

    Lemma read_step
          lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (NORMAL_TVIEW1: normal_tview (Local.tview lc1))
          (NORMAL_MEM1: normal_memory mem1)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
          (TO: L loc -> Ordering.le ord Ordering.plain ->
               to = (TView.cur (Local.tview lc1)).(View.rlx) loc):
      <<NORMAL_TVIEW2: normal_tview (Local.tview lc2)>>.
    Proof.
      destruct lc1. inv NORMAL_TVIEW1. inv STEP. ss.
      hexploit get_normal_view; eauto. i.
      destruct (classic (L loc /\ Ordering.le ord Ordering.plain)).
      { des. exploit TO; eauto. i. subst.
        econs; ss.
        - apply join_normal_view.
          + rewrite View.le_join_l; ss.
            apply View.singleton_ur_if_spec; try apply WF1.
            condtac; try refl. rewrite CUR; ss. refl.
          + condtac; ss.
        - apply join_normal_view.
          + rewrite View.le_join_l; ss.
            apply View.singleton_ur_if_spec; try apply WF1.
            condtac; try apply WF1. rewrite CUR; ss. apply WF1.
          + condtac; ss.
      }
      { econs; ss.
        - repeat apply join_normal_view; try condtac; ss.
          unfold View.singleton_ur_if.
          condtac; eauto using singleton_ur_normal_view.
          destruct (L loc) eqn:LOC.
          + exfalso. apply H0. destruct ord; ss.
          + apply singleton_rw_normal_view; eauto. rewrite LOC. ss.
        - condtac; repeat eapply join_normal_view; eauto; ss.
          destruct (L loc) eqn:LOC.
          + exfalso. apply H0. destruct ord; ss.
          + apply singleton_rw_normal_view; eauto. rewrite LOC. ss.
      }
    Qed.

    Lemma write_step
          lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          (NORMAL_TVIEW1: normal_tview (Local.tview lc1))
          (NORMAL_MEM1: normal_memory mem1)
          (RELEASEDM: normal_view (View.unwrap releasedm))
          (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
      (<<NORMAL_TVIEW2: normal_tview (Local.tview lc2)>>) /\
      (<<NORMAL_MEM2: normal_memory mem2>>).
    Proof.
      destruct lc1. inv NORMAL_TVIEW1. inv STEP. ss.
      hexploit write; eauto.
      { i. revert MSG. unfold TView.write_released.
        condtac; ss. i. inv MSG.
        condtac; repeat apply join_normal_view; eauto.
        - unfold LocFun.add. condtac; ss.
          apply join_normal_view; ss.
        - unfold LocFun.add. condtac; ss.
          apply join_normal_view; ss.
      }
      i. des. splits; ss.
      econs; repeat apply join_normal_view; ss;
        try apply singleton_ur_normal_view. i.
      unfold LocFun.add.
      repeat condtac; ss; eauto;
        repeat apply join_normal_view; ss.
    Qed.

    Lemma write_na_step
          lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind
          (NORMAL_TVIEW1: normal_tview (Local.tview lc1))
          (NORMAL_MEM1: normal_memory mem1)
          (STEP: Local.write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind):
      (<<NORMAL_TVIEW2: normal_tview (Local.tview lc2)>>) /\
      (<<NORMAL_MEM2: normal_memory mem2>>).
    Proof.
      destruct lc1. inv NORMAL_TVIEW1. inv STEP. ss.
      hexploit write_na; eauto. i. des. splits; ss.
      econs; repeat apply join_normal_view; ss;
        try apply singleton_ur_normal_view. i.
      unfold LocFun.add.
      repeat condtac; ss; eauto;
        repeat apply join_normal_view; ss.
    Qed.

    Lemma fence_step
          lc1 sc1 ordr ordw lc2 sc2
          (NORMAL_TVIEW1: normal_tview (Local.tview lc1))
          (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
      (<<NORMAL_TVIEW2: normal_tview (Local.tview lc2)>>).
    Proof.
      inv NORMAL_TVIEW1. inv STEP. ss.
      econs; ss; i; repeat condtac; ss;
        repeat apply join_normal_view; ss.
    Qed.

    Lemma ord_program_step
          ordcr ordcw e lc1 sc1 mem1 lc2 sc2 mem2
          (WF1: Local.wf lc1 mem1)
          (NORMAL_TVIEW1: normal_tview (Local.tview lc1))
          (NORMAL_MEM1: normal_memory mem1)
          (STEP: OrdLocal.program_step L ordcr ordcw e lc1 sc1 mem1 lc2 sc2 mem2)
          (READ: forall loc to val released ord
                   (EVENT: ThreadEvent.is_reading e = Some (loc, to, val, released, ord))
                   (LOC: L loc)
                   (ORD: Ordering.le ord Ordering.plain),
              to = (TView.cur (Local.tview lc1)).(View.rlx) loc):
      (<<NORMAL_TVIEW2: normal_tview (Local.tview lc2)>>) /\
      (<<NORMAL_MEM2: normal_memory mem2>>).
    Proof.
      inv STEP; ss.
      - inv LOCAL. hexploit read_step; eauto.
        i. exploit READ; eauto.
        revert H0. condtac; ss. destruct ord, ordcr; ss.
      - inv LOCAL. hexploit write_step; eauto. ss.
      - inv LOCAL1. inv LOCAL2.
        hexploit read_step; eauto.
        { i. exploit READ; eauto.
          revert H0. condtac; ss. destruct ordr, ordcr; ss.
        }
        i. des.
        hexploit write_step; eauto.
        inv STEP. ss. eapply get_normal_view; eauto.
      - hexploit fence_step; eauto.
      - hexploit fence_step; eauto.
      - inv LOCAL.
        + hexploit write_na_step; eauto.
        + hexploit write_step; eauto. ss.
    Qed.

    Lemma future_normal_thread
          lang e sc' mem'
          (NORMAL: @normal_thread lang e)
          (NORMAL_MEM: normal_memory mem'):
      normal_thread (Thread.mk _ (Thread.state e) (Thread.local e) sc' mem').
    Proof.
      inv NORMAL. econs; ss.
    Qed.
  End Normal.
End Normal.


Module Stable.
  Section Stable.
    Variable L: Loc.t -> bool.

    Definition stable_view (mem: Memory.t) (view: View.t): Prop :=
      forall loc from val released
        (LOC: L loc)
        (GET: Memory.get loc ((View.rlx view) loc) mem =
              Some (from, Message.concrete val (Some released))),
        View.le released view.

    Definition stable_timemap (mem: Memory.t) (tm: TimeMap.t): Prop :=
      stable_view mem (View.mk tm tm).

    Inductive stable_tview (mem: Memory.t) (tview: TView.t): Prop :=
    | stable_tview_intro
        (REL: forall loc (LOC: ~ L loc), stable_view mem ((TView.rel tview) loc))
        (CUR: stable_view mem (TView.cur tview))
        (ACQ: stable_view mem (TView.acq tview))
    .

    Definition stable_memory (rels: Writes.t) (mem: Memory.t): Prop :=
      forall loc from to val released
        (LOC: ~ L loc \/
              exists ord, List.In (loc, to, ord) rels /\ Ordering.le Ordering.acqrel ord)
        (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
        stable_view mem released.

    Inductive stable_thread {lang: language} (rels: Writes.t) (e: Thread.t lang): Prop :=
    | stable_thread_intro
        (STABLE_TVIEW: Stable.stable_tview (Thread.memory e) (Local.tview (Thread.local e)))
        (STABLE_SC: Stable.stable_timemap (Thread.memory e) (Thread.sc e))
        (STABLE_MEMORY: Stable.stable_memory rels (Thread.memory e))
    .
    Hint Constructors stable_thread: core.


    Lemma future_stable_view
          mem1 mem2 view
          (CLOSED: Memory.closed_view view mem1)
          (STABLE: stable_view mem1 view)
          (MEM_FUTURE: Memory.future mem1 mem2):
      stable_view mem2 view.
    Proof.
      ii. inv CLOSED. specialize (RLX loc). des.
      exploit Memory.future_get1; try exact RLX; eauto; ss. i. des.
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

    Lemma future_stable_thread
          lang rels e sc' mem'
          (WF: Local.wf (Thread.local e) (Thread.memory e))
          (STABLE: stable_thread rels e)
          (SC: TimeMap.le (Thread.sc e) sc')
          (MEM: Memory.future (Thread.memory e) mem')
          (STABLE_SC: Stable.stable_timemap mem' sc')
          (STABLE_MEM: Stable.stable_memory rels mem'):
      stable_thread rels (Thread.mk lang (Thread.state e) (Thread.local e) sc' mem').
    Proof.
      destruct e, local. inv STABLE. inv WF. ss.
      econs; i; ss; eauto using Stable.future_stable_tview.
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
      stable_timemap mem (View.rlx view).
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
          (NORMAL: Normal.normal_tview L tview)
          (STABLE: stable_tview mem tview)
          (LOC: L loc)
          (GET: Memory.get loc ((View.rlx (TView.cur tview)) loc) mem =
                Some (from, Message.concrete val released)):
      TView.read_tview tview loc ((View.rlx (TView.cur tview)) loc) released ord = tview.
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
          a rels mem
          (STABLE: stable_memory (a :: rels) mem):
      stable_memory rels mem.
    Proof.
      ii. des.
      - eapply STABLE; eauto.
      - eapply STABLE; eauto. ss.
        right. esplits; eauto.
    Qed.

    Lemma promise_stable_view
          view promises1 mem1 loc from to msg promises2 mem2 kind
          (CLOSED1: Memory.closed_view view mem1)
          (STABLE1: stable_view mem1 view)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      stable_view mem2 view.
    Proof.
      ii. revert GET. inv PROMISE; ss.
      { erewrite Memory.add_o; eauto. condtac; ss; eauto.
        i. des. inv GET.
        exploit Memory.add_get0; try exact MEM. i. des.
        inv CLOSED1. specialize (RLX loc). des. congr.
      }
      { erewrite Memory.split_o; eauto. repeat condtac; ss; eauto.
        - i. des. inv GET.
          exploit Memory.split_get0; try exact MEM. i. des.
          inv CLOSED1. specialize (RLX loc). des. congr.
        - guardH o. i. des. inv GET.
          exploit Memory.split_get0; try exact MEM. i. des. eauto.
      }
      { erewrite Memory.lower_o; eauto. condtac; ss; eauto.
        i. des. inv GET.
        exploit Memory.lower_get0; try exact MEM. i. des.
        inv MSG_LE. inv RELEASED. etrans; eauto.
      }
      { erewrite Memory.remove_o; eauto. condtac; ss; eauto. }
    Qed.

    Lemma write_stable_view
          view promises1 mem1 loc from to msg promises2 mem2 kind
          (CLOSED1: Memory.closed_view view mem1)
          (STABLE1: stable_view mem1 view)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      stable_view mem2 view.
    Proof.
      inv WRITE. eauto using promise_stable_view.
    Qed.

    Lemma write_na_stable_view
          view ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          (CLOSED1: Memory.closed_view view mem1)
          (STABLE1: stable_view mem1 view)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
      stable_view mem2 view.
    Proof.
      induction WRITE; eauto using write_stable_view.
      hexploit write_stable_view; try exact WRITE_EX; eauto. i.
      hexploit Memory.write_closed_view; try exact WRITE_EX; eauto.
    Qed.

    Lemma promise_stable_tview
          tview promises1 mem1 loc from to msg promises2 mem2 kind
          (CLOSED1: TView.closed tview mem1)
          (STABLE1: stable_tview mem1 tview)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      stable_tview mem2 tview.
    Proof.
      inv CLOSED1. inv STABLE1.
      econs; eauto using promise_stable_view.
    Qed.

    Lemma write_stable_tview
          tview promises1 mem1 loc from to msg promises2 mem2 kind
          (CLOSED1: TView.closed tview mem1)
          (STABLE1: stable_tview mem1 tview)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      stable_tview mem2 tview.
    Proof.
      inv CLOSED1. inv STABLE1.
      econs; eauto using write_stable_view.
    Qed.

    Lemma write_na_stable_tview
          tview ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind
          (CLOSED1: TView.closed tview mem1)
          (STABLE1: stable_tview mem1 tview)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to msg promises2 mem2 msgs kinds kind):
      stable_tview mem2 tview.
    Proof.
      inv CLOSED1. inv STABLE1.
      econs; eauto using write_na_stable_view.
    Qed.

    Lemma promise_stable_memory
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (MEM1: Memory.closed mem1)
          (STABLE_MEM1: stable_memory rels mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              stable_view mem2 released)
          (PROMISE: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind):
      stable_memory rels mem2.
    Proof.
      unfold stable_memory in *. i. revert GET. guardH LOC.
      dup PROMISE. inv PROMISE0; ss.
      { (* add *)
        erewrite Memory.add_o; eauto. condtac; ss; i.
        - des. inv GET. eauto.
        - guardH o.
          inv MEM1. exploit CLOSED; eauto. i. des. inv MSG_CLOSED. inv CLOSED0.
          hexploit STABLE_MEM1; eauto. i.
          eapply promise_stable_view; eauto.
      }
      { (* split *)
        erewrite Memory.split_o; eauto. repeat condtac; ss; i.
        - des. inv GET. eauto.
        - guardH o. des. inv GET.
          exploit Memory.split_get0; try exact MEM. i. des.
          inv MEM1. exploit CLOSED; try exact GET0. i. des. inv MSG_CLOSED. inv CLOSED0.
          hexploit STABLE_MEM1; try exact GET0; eauto. i.
          eapply promise_stable_view; eauto.
        - guardH o. guardH o0.
          inv MEM1. exploit CLOSED; eauto. i. des. inv MSG_CLOSED. inv CLOSED0.
          hexploit STABLE_MEM1; eauto. i.
          eapply promise_stable_view; eauto.
      }
      { (* lower *)
        erewrite Memory.lower_o; eauto. condtac; ss; i.
        - des. inv GET. eauto.
        - guardH o.
          inv MEM1. exploit CLOSED; eauto. i. des. inv MSG_CLOSED. inv CLOSED0.
          hexploit STABLE_MEM1; eauto. i.
          eapply promise_stable_view; eauto.
      }
      { (* cancel *)
        erewrite Memory.remove_o; eauto. condtac; ss; i.
        guardH o.
        inv MEM1. exploit CLOSED; eauto. i. des. inv MSG_CLOSED. inv CLOSED0.
        hexploit STABLE_MEM1; eauto. i.
        eapply promise_stable_view; eauto.
      }
    Qed.

    Lemma write_stable_memory
          ord
          rels promises1 mem1 loc from to msg promises2 mem2 kind
          (MEM1: Memory.closed mem1)
          (STABLE_MEM1: stable_memory rels mem1)
          (WRITES1: Writes.wf L rels mem1)
          (RESERVE_ONLY1: OrdLocal.reserve_only L promises1)
          (MSG: forall val released
                  (LOC: ~ L loc \/ Ordering.le Ordering.acqrel ord)
                  (MSG: msg = Message.concrete val (Some released)),
              stable_view mem2 released)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      stable_memory (if L loc then (loc, to, ord) :: rels else rels) mem2.
    Proof.
      destruct (L loc) eqn:LOC; cycle 1.
      { inv WRITE. eauto using promise_stable_memory. }
      exploit OrdLocal.reserve_only_write_add; eauto. i. subst.
      inv WRITE. dup PROMISE. inv PROMISE0.
      unfold stable_memory in *. i. revert GET.
      erewrite Memory.add_o; eauto. condtac; ss; i.
      - des; clarify; eauto.
        inv WRITES1. exploit SOUND; eauto. i. des.
        exploit Memory.add_get0; try exact MEM. i. des. congr.
      - guardH o.
        hexploit STABLE_MEM1; eauto; i.
        { des; eauto. clarify. unguard. des; ss. }
        clear LOC0.
        inv MEM1. exploit CLOSED; eauto. i. des. inv MSG_CLOSED. inv CLOSED0.
        eapply promise_stable_view; eauto.
    Qed.

    Lemma write_na_stable_memory
          rels ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
          (MEM1: Memory.closed mem1)
          (STABLE_MEM1: stable_memory rels mem1)
          (WRITE: Memory.write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind):
      stable_memory rels mem2.
    Proof.
      induction WRITE.
      - inv WRITE. eapply promise_stable_memory; eauto; ss.
      - exploit Memory.write_closed; try exact WRITE_EX; ss.
        { unguard. des; subst; ss. econs. ss. }
        { unguard. des; subst; ss. econs. apply Time.bot_spec. }
        i. inv WRITE_EX.
        hexploit promise_stable_memory; try exact PROMISE; eauto.
        i. subst. unguard. des; ss.
    Qed.

    Lemma stable_memory_strong_relaxed
          rels mem loc to ord
          (ORD: Ordering.le ord Ordering.strong_relaxed):
      stable_memory rels mem <-> stable_memory ((loc, to, ord) :: rels) mem.
    Proof.
      split; ii.
      - eapply H; eauto. des; eauto.
        inv LOC; eauto. inv H0. destruct ord0; ss.
      - eapply H; eauto. des; eauto.
        right. esplits; eauto. right. ss.
    Qed.

    Lemma stable_memory_le
          rels mem loc to ord1 ord2
          (STABLE_MEM1: stable_memory ((loc, to, ord1) :: rels) mem)
          (ORD: Ordering.le ord2 ord1):
      stable_memory ((loc, to, ord2) :: rels) mem.
    Proof.
      ii. eapply STABLE_MEM1; eauto. des; eauto. inv LOC.
      - inv H. right. esplits; [left; eauto|]. etrans; eauto.
      - right. esplits; [right; eauto|]. ss.
    Qed.


    (* step *)

    Lemma promise_step
          rels lc1 mem1 loc from to msg lc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (STABLE_MEM1: stable_memory rels mem1)
          (MSG: forall val released
                  (MSG: msg = Message.concrete val (Some released)),
              stable_view mem2 released)
          (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind):
      <<STABLE_TVIEW2: stable_tview mem2 (Local.tview lc2)>> /\
      <<STABLE_MEM2: stable_memory rels mem2>>.
    Proof.
      inv STEP.
      hexploit promise_stable_tview; eauto; try apply WF1. i.
      hexploit promise_stable_memory; eauto.
    Qed.

    Lemma read_step_loc_cur
          lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1))
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (LOC: L loc)
          (TO: to = (TView.cur (Local.tview lc1)).(View.rlx) loc)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<LC2: lc2 = lc1>>.
    Proof.
      inv STEP. destruct lc1. f_equal; ss.
      erewrite stable_tview_read_tview; eauto. apply WF1.
    Qed.

    Lemma read_step_loc_ra
          rels ordw lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (STABLE_MEM1: stable_memory rels mem1)
          (LOC: L loc)
          (IN: List.In (loc, to, ordw) rels)
          (ORDW: Ordering.le Ordering.acqrel ordw)
          (ORD: Ordering.le Ordering.acqrel ord)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<STABLE_TVIEW2: stable_tview mem1 (Local.tview lc2)>>.
    Proof.
      inv STEP. ss.
      inv STABLE_TVIEW1. econs; ss.
      - unfold View.singleton_ur_if.
        repeat (condtac; [|destruct ord; ss]). ii.
        destruct (Loc.eq_dec loc loc0); subst; ss.
        + unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
          revert GET0. condtac; ss. i.
          rewrite TimeFacts.le_join_l in GET0; cycle 1.
          { etrans; [|eapply Time.join_r].
            inv MEM1. exploit CLOSED; try exact GET. i. des.
            inv MSG_TS. ss.
          }
          rewrite TimeFacts.le_join_r in GET0; cycle 1.
          { inv READABLE. auto. }
          rewrite GET0 in *. inv GET. ss.
          etrans; [|apply View.join_r]. refl.
        + unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
          revert GET0. condtac; try congr; ss. i.
          rewrite (@TimeFacts.le_join_l _ Time.bot) in GET0; try apply Time.bot_spec.
          exploit Time.join_cases. i. des.
          { rewrite x0 in GET0.
            exploit CUR; eauto. i. etrans; eauto.
            etrans; [|apply View.join_l].
            etrans; [|apply View.join_l].
            refl.
          }
          { rewrite x0 in GET0. destruct released; ss; cycle 1.
            { unfold TimeMap.bot in *.
              inv MEM1. rewrite INHABITED in GET0. ss. }
            exploit STABLE_MEM1; try exact GET; eauto. i.
            etrans; eauto.
            etrans; [|apply View.join_r].
            refl.
          }
      - unfold View.singleton_ur_if.
        repeat (condtac; [|destruct ord; ss]). ii.
        destruct (Loc.eq_dec loc loc0); subst; ss.
        + unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
          revert GET0. condtac; ss. i.
          rewrite Time.join_assoc in GET0.
          rewrite (@TimeFacts.le_join_l to) in GET0; cycle 1.
          { inv MEM1. exploit CLOSED; try exact GET. i. des.
            inv MSG_TS. ss. }
          exploit Time.join_cases. i. des.
          { rewrite x0 in GET0.
            exploit ACQ; eauto. i. etrans; eauto.
            etrans; [|apply View.join_l].
            etrans; [|apply View.join_l].
            refl.
          }
          { rewrite x0 in GET0. rewrite GET0 in *. inv GET. ss.
            etrans; [|apply View.join_r].
            refl.
          }
        + unfold TimeMap.join, View.singleton_ur_if,
            TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find in GET0.
          revert GET0. condtac; try congr; ss. i.
          rewrite (@TimeFacts.le_join_l _ Time.bot) in GET0; try apply Time.bot_spec.
          exploit Time.join_cases. i. des.
          { rewrite x0 in GET0.
            exploit ACQ; eauto. i. etrans; eauto.
            etrans; [|apply View.join_l].
            etrans; [|apply View.join_l].
            refl.
          }
          { rewrite x0 in GET0. destruct released; ss; cycle 1.
            { unfold TimeMap.bot in *.
              inv MEM1. rewrite INHABITED in GET0. ss. }
            exploit STABLE_MEM1; try exact GET; eauto. i.
            etrans; eauto.
            etrans; [|apply View.join_r]. refl.
          }
    Qed.

    Lemma read_step_other
          rels lc1 mem1 loc to val released ord lc2
          (WF1: Local.wf lc1 mem1)
          (MEM1: Memory.closed mem1)
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (STABLE_MEM1: stable_memory rels mem1)
          (LOC: ~ L loc)
          (STEP: Local.read_step lc1 mem1 loc to val released ord lc2):
      <<STABLE_TVIEW2: stable_tview mem1 (Local.tview lc2)>>.
    Proof.
      inv STEP. ss. splits; ss.
      inv STABLE_TVIEW1. econs; ss.
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

    Lemma write_tview_stable
          mem tview sc loc to ord
          (WF: TView.wf tview)
          (MEM: Memory.closed mem)
          (STABLE: stable_tview mem tview)
          (WRITABLE: TView.writable (TView.cur tview) sc loc to ord)
          (TO: forall from val released
                 (LOC: L loc)
                 (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released))),
              View.le released (TView.cur (TView.write_tview tview sc loc to ord))):
      stable_tview mem (TView.write_tview tview sc loc to ord).
    Proof.
      inv WRITABLE. inv STABLE. econs; ss; i.
      { condtac; ss.
        - unfold LocFun.add, LocFun.find.
          condtac; ss; eauto. subst.
          apply join_stable_view; eauto.
          apply singleton_ur_stable_view; eauto.
        - unfold LocFun.add, LocFun.find.
          condtac; ss; eauto. subst.
          apply join_stable_view; eauto.
          apply singleton_ur_stable_view; eauto.
      }
      { ii. ss. revert GET.
        unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; ss.
        - subst. rewrite TimeFacts.le_join_r; [|econs; ss]. eauto.
        - rewrite TimeFacts.le_join_l; try apply Time.bot_spec. i.
          exploit CUR; eauto. i.
          etrans; eauto. apply View.join_l.
      }
      { ii. ss. revert GET.
        unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; ss.
        - subst. exploit Time.join_cases. intro JOIN. des; rewrite JOIN; i.
          + exploit ACQ; eauto. i.
            etrans; eauto. apply View.join_l.
          + exploit TO; eauto. i.
            etrans; eauto.
            eapply View.join_spec; try apply View.join_r.
            etrans; [|apply View.join_l]. apply WF.
        - rewrite TimeFacts.le_join_l; try apply Time.bot_spec. i.
          exploit ACQ; eauto. i.
          etrans; eauto. apply View.join_l.
      }
    Qed.

    Lemma write_step
          rels lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (RELS_WF1: Writes.wf L rels mem1)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1))
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (STABLE_MEM1: stable_memory rels mem1)
          (WF_RELEASEDM: View.opt_wf releasedm)
          (CLOSED_RELEASEDM: Memory.closed_opt_view releasedm mem1)
          (STABLE_RELEASEDM: ~ L loc -> stable_view mem1 (View.unwrap releasedm))
          (RELEASEDM: L loc -> View.le (View.unwrap releasedm) (TView.cur (Local.tview lc1)))
          (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
      <<STABLE_TVIEW2: stable_tview mem2 (Local.tview lc2)>> /\
      <<STABLE_MEM2: stable_memory (if L loc then (loc, to, ord) :: rels else rels) mem2>>.
    Proof.
      exploit Local.write_step_future; try exact STEP; eauto. i. des.
      inv STEP. ss.
      hexploit write_stable_tview; eauto; try apply WF1. i.
      assert (REL: forall released
                     (LOC: L loc)
                     (REL: Some released = TView.write_released (Local.tview lc1) sc1 loc to releasedm ord),
                 View.le released (TView.cur (TView.write_tview (Local.tview lc1) sc1 loc to ord))).
      { unfold TView.write_released. condtac; ss. i. inv REL.
        unfold LocFun.add. repeat condtac; ss.
        - apply View.join_spec; try refl.
          etrans; eauto. apply View.join_l.
        - apply View.join_spec.
          + etrans; eauto. apply View.join_l.
          + apply View.join_spec; try by apply View.join_r.
            etrans; [|apply View.join_l]. apply WF1.
      }
      hexploit write_tview_stable; try exact H; eauto; try apply WF1.
      { i. exploit Memory.write_get2; eauto. i. des.
        rewrite GET in *. inv GET_MEM. eauto.
      }
      i. splits; auto.
      eapply write_stable_memory; try exact WRITE; eauto. i.
      revert MSG. unfold TView.write_released. condtac; ss. i. inv MSG.
      unfold LocFun.add. condtac; ss.
      destruct (classic (L loc)).
      - des; ss. condtac; try by destruct ord; ss.
        rewrite View.le_join_r; cycle 1.
        { etrans; [|apply View.join_l]. apply RELEASEDM. ss. }
        ii. ss. revert GET.
        unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; ss.
        + subst. rewrite TimeFacts.le_join_r; cycle 1.
          { inv WRITABLE. econs. ss. }
          exploit Memory.write_get2; eauto. i. des.
          rewrite GET in *. inv GET_MEM. eauto.
        + rewrite TimeFacts.le_join_l; try apply Time.bot_spec. i.
          etrans; [|apply View.join_l].
          inv H. eapply CUR; eauto.
      - guardH LOC. inv STABLE_TVIEW1.
        condtac; ss; repeat apply join_stable_view;
          (try by apply singleton_ur_stable_view);
          try eapply write_stable_view; eauto; try apply WF1.
        + apply Memory.unwrap_closed_opt_view; ss. apply MEM1.
        + apply Memory.unwrap_closed_opt_view; ss. apply MEM1.
    Qed.

    Lemma write_na_get_to
          ts promises1 mem1 loc from to val promsies2 mem2 msgs kinds kind
          (WRITE: Memory.write_na ts promises1 mem1 loc from to val promsies2 mem2 msgs kinds kind):
      Memory.get loc to mem2 = Some (from, Message.concrete val None).
    Proof.
      induction WRITE; eauto.
      exploit Memory.write_get2; eauto. i. des. ss.
    Qed.

    Lemma write_na_step
          rels lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind
          (WF1: Local.wf lc1 mem1)
          (SC1: Memory.closed_timemap sc1 mem1)
          (MEM1: Memory.closed mem1)
          (RELS_WF1: Writes.wf L rels mem1)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1))
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (STABLE_MEM1: stable_memory rels mem1)
          (STEP: Local.write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind):
      <<STABLE_TVIEW2: stable_tview mem2 (Local.tview lc2)>> /\
      <<STABLE_MEM2: stable_memory (if L loc then (loc, to, ord) :: rels else rels) mem2>>.
    Proof.
      exploit Local.write_na_step_future; try exact STEP; eauto. i. des.
      inv STEP. ss.
      hexploit write_na_stable_tview; eauto; try apply WF1. i.
      exploit Memory.write_na_times; eauto. i. des.
      hexploit write_tview_stable; try exact H; eauto; try apply WF1.
      { econs. eauto. }
      { i. apply write_na_get_to in WRITE. congr. }
      i. splits; eauto.
      eapply write_na_stable_memory; try exact WRITE; eauto.
      condtac; ss. rewrite <- stable_memory_strong_relaxed; eauto.
    Qed.

    Lemma fence_step
          rels lc1 sc1 mem1 ordr ordw lc2 sc2
          (WF1: Local.wf lc1 mem1)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1))
          (STABLE_TVIEW1: stable_tview mem1 (Local.tview lc1))
          (STABLE_SC1: stable_timemap mem1 sc1)
          (RELS_WF1: Writes.wf L rels mem1)
          (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
      <<STABLE_TVIEW2: stable_tview mem1 (Local.tview lc2)>> /\
      <<STABLE_SC2: stable_timemap mem1 sc2>>.
    Proof.
      inv STEP. ss. splits; ss.
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


    (* cap *)

    Lemma max_concrete_timemap_stable
          mem tm
          (CLOSED: Memory.closed mem)
          (MAX: Memory.max_concrete_timemap mem tm):
      stable_timemap mem tm.
    Proof.
      ii. dup CLOSED. inv CLOSED.
      exploit CLOSED1; eauto. i. des. inv MSG_CLOSED. inv CLOSED. inv CLOSED2.
      hexploit Memory.max_concrete_timemap_spec; try exact PLN; eauto. i.
      hexploit Memory.max_concrete_timemap_spec; try exact RLX; eauto. i.
      econs; ss.
    Qed.

    Lemma cap_normal_memory
          mem1 mem2
          (CLOSED: Memory.closed mem1)
          (CAP: Memory.cap mem1 mem2)
          (NORMAL: Normal.normal_memory L mem1):
      Normal.normal_memory L mem2.
    Proof.
      ii. exploit Memory.cap_inv; eauto. i. des; ss.
      eapply NORMAL; eauto.
    Qed.

    Lemma cap_stable_view
          mem1 mem2 view
          (CLOSED: Memory.closed mem1)
          (CAP: Memory.cap mem1 mem2)
          (STABLE: stable_view mem1 view):
      stable_view mem2 view.
    Proof.
      ii. exploit Memory.cap_inv; eauto. i. des; ss.
      eapply STABLE; eauto.
    Qed.

    Lemma cap_stable_timemap
          mem1 mem2 tm
          (CLOSED: Memory.closed mem1)
          (CAP: Memory.cap mem1 mem2)
          (STABLE: stable_timemap mem1 tm):
      stable_timemap mem2 tm.
    Proof.
      eapply cap_stable_view; eauto.
    Qed.

    Lemma cap_stable_tview
          mem1 mem2 tview
          (CLOSED: Memory.closed mem1)
          (CAP: Memory.cap mem1 mem2)
          (STABLE: stable_tview mem1 tview):
      stable_tview mem2 tview.
    Proof.
      inv STABLE. econs; eauto using cap_stable_view.
    Qed.

    Lemma cap_stable_memory
          rels mem1 mem2
          (CLOSED: Memory.closed mem1)
          (CAP: Memory.cap mem1 mem2)
          (STABLE: stable_memory rels mem1):
      stable_memory rels mem2.
    Proof.
      ii. guardH LOC.
      exploit Memory.cap_inv; try exact GET; eauto. i. des; ss.
      exploit Memory.cap_inv; try exact GET0; eauto. i. des; ss.
      eapply STABLE; eauto.
    Qed.
  End Stable.
End Stable.
