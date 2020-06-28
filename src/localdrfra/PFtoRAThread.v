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
Require Import Configuration.

Require Import PromiseConsistent.
Require Import Trace.
Require Import MemoryProps.
Require Import JoinedView.

Require Import LocalPF.
Require Import OrdStep.
Require Import RARace.
Require Import Stable.
Require Import PFtoRASimThread.

Set Implicit Arguments.


Module TraceWF.
  Definition wf (tr: Trace.t) (promises: Memory.t) (mem: Memory.t): Prop :=
    forall th e loc from to val released ord
      (IN: List.In (th, e) tr)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)),
      unchangable mem promises loc to from (Message.concrete val released).

  Lemma step_unchangable
        lang pf e e1 e2
        loc from to val released ord
        (STEP: @Thread.step lang pf e e1 e2)
        (EVENT: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
    unchangable e2.(Thread.memory) e2.(Thread.local).(Local.promises) loc to from (Message.concrete val released).
  Proof.
    destruct e; ss.
    - inv EVENT. inv STEP; inv STEP0. inv LOCAL. inv LOCAL0. inv WRITE. ss.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
      econs; eauto.
    - inv EVENT. inv STEP; inv STEP0. inv LOCAL. inv LOCAL1. inv LOCAL2. inv WRITE. ss.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.promise_get0; eauto; try by (inv PROMISE; ss). i. des.
      econs; eauto.
  Qed.

  Lemma steps_wf
        lang tr e1 e2
        (STEPS: @Trace.steps lang tr e1 e2):
    wf tr e2.(Thread.local).(Local.promises) e2.(Thread.memory).
  Proof.
    induction STEPS; ss. subst.
    ii. inv IN; eauto. inv H.
    eapply unchangable_trace_steps_increase; eauto using step_unchangable.
  Qed.

  Lemma steps_wf_other
        lang tr e1 e2 tr'
        (TRACE1: wf tr' e1.(Thread.local).(Local.promises) e1.(Thread.memory))
        (STEPS: @Trace.steps lang tr e1 e2):
    wf tr' e2.(Thread.local).(Local.promises) e2.(Thread.memory).
  Proof.
    revert tr' TRACE1. induction STEPS; i; ss.
    subst. apply IHSTEPS.
    ii. eapply unchangable_increase; eauto.
  Qed.

  Lemma steps_disjoint
        lang tr e1 e2 lc
        (STEPS: @Trace.steps lang tr e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory))
        (DISJOINT: Local.disjoint e1.(Thread.local) lc)
        (WF: Local.wf lc e1.(Thread.memory)):
    wf tr lc.(Local.promises) e2.(Thread.memory).
  Proof.
    induction STEPS; i; ss. subst. ii. inv IN.
    - inv H. exploit step_unchangable; eauto. i.
      exploit unchangable_trace_steps_increase; eauto. i. inv x1.
      econs; eauto.
      clear IHSTEPS STEPS.
      destruct (Memory.get loc to lc.(Local.promises)) as [[]|] eqn:GETP; ss.
      exfalso. inv WF. exploit PROMISES; eauto. i.
      destruct e0; ss; inv EVENT.
      + inv STEP; inv STEP0. inv LOCAL. inv LOCAL0. inv WRITE. inv PROMISE; ss.
        * exploit Memory.add_get0; try exact MEM. i. des. congr.
        * exploit Memory.split_get0; try exact MEM. i. des. congr.
        * exploit Memory.lower_get0; try exact PROMISES0. i. des.
          inv DISJOINT. inv DISJOINT0. exploit DISJOINT; eauto. i. des.
          exploit Memory.get_ts; try exact GET0. i. des; try congr.
          exploit Memory.get_ts; try exact GETP. i. des; try congr.
          apply (x1 to); econs; try refl; ss.
      + inv STEP; inv STEP0. inv LOCAL. inv LOCAL1. inv LOCAL2. inv WRITE. inv PROMISE; ss.
        * exploit Memory.add_get0; try exact MEM. i. des. congr.
        * exploit Memory.split_get0; try exact MEM. i. des. congr.
        * exploit Memory.lower_get0; try exact PROMISES0. i. des.
          inv DISJOINT. inv DISJOINT0. exploit DISJOINT; eauto. i. des.
          exploit Memory.get_ts; try exact GET1. i. des; try congr.
          exploit Memory.get_ts; try exact GETP. i. des; try congr.
          apply (x1 to); econs; try refl; ss.
    - exploit Thread.step_future; eauto. i. des.
      exploit Thread.step_disjoint; eauto. i. des.
      eapply IHSTEPS; eauto.
  Qed.

  Lemma steps_disjoint_other
        lang tr e1 e2 tr' lc
        (TRACE1: wf tr' e1.(Thread.local).(Local.promises) e1.(Thread.memory))
        (TRACE2: wf tr' lc.(Local.promises) e1.(Thread.memory))
        (STEPS: @Trace.steps lang tr e1 e2):
    wf tr' lc.(Local.promises) e2.(Thread.memory).
  Proof.
    hexploit steps_wf_other; eauto. ii.
    exploit H; eauto. i. inv x.
    exploit TRACE2; eauto. i. inv x. econs; ss.
  Qed.

  Lemma wf_app
        tr1 tr2 promises mem
        (TRACE1: wf tr1 promises mem)
        (TRACE2: wf tr2 promises mem):
    wf (tr1 ++ tr2) promises mem.
  Proof.
    ii. apply List.in_app_or in IN. des; eauto.
  Qed.

  Lemma app_wf
        tr1 tr2 promises mem
        (TRACE: wf (tr1 ++ tr2) promises mem):
    wf tr1 promises mem /\ wf tr2 promises mem.
  Proof.
    split; ii.
    - eapply TRACE; eauto. apply List.in_or_app. left. eauto.
    - eapply TRACE; eauto. apply List.in_or_app. right. eauto.
  Qed.
End TraceWF.


Module PFtoRAThread.
  Section PFtoRAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Definition closed_views (views: Loc.t -> Time.t -> list View.t) (mem: Memory.t): Prop :=
      forall loc ts view (LOC: ~ L loc) (IN: List.In view (views loc ts)),
        Memory.closed_view view mem.

    Definition normal_views (views: Loc.t -> Time.t -> list View.t): Prop :=
      forall loc ts view (LOC: ~ L loc) (IN: List.In view (views loc ts)),
        Stable.normal_view L view.

    Definition stable_views (mem: Memory.t) (views: Loc.t -> Time.t -> list View.t): Prop :=
      forall loc ts view (LOC: ~ L loc) (IN: List.In view (views loc ts)),
        Stable.stable_view L mem view.

    Lemma joined_opt_view_normal_view
          views loc ts released
          (NORMAL: normal_views views)
          (LOC: ~ L loc)
          (JOINED: joined_opt_view (views loc ts) (Some released)):
      Stable.normal_view L released.
    Proof.
      specialize (NORMAL loc ts).
      inv JOINED. induction JOINED0; ss.
      apply Stable.join_normal_view; eauto.
    Qed.

    Lemma joined_opt_view_stable_view
          mem views loc ts released
          (MEM: Memory.closed mem)
          (STABLE: stable_views mem views)
          (LOC: ~ L loc)
          (JOINED: joined_opt_view (views loc ts) (Some released)):
      Stable.stable_view L mem released.
    Proof.
      specialize (STABLE loc ts).
      inv JOINED. induction JOINED0.
      { ii. inv MEM. rewrite INHABITED in *. inv GET. }
      apply Stable.join_stable_view; eauto.
    Qed.

    Lemma future_closed_views
          views mem1 mem2
          (CLOSED1: closed_views views mem1)
          (FUTURE: Memory.future mem1 mem2):
      closed_views views mem2.
    Proof.
      ii. eapply Memory.future_closed_view; eauto.
    Qed.

    Lemma future_stable_views
          views mem1 mem2
          (STABLE1: stable_views mem1 views)
          (CLOSED1: closed_views views mem1)
          (FUTURE: Memory.future mem1 mem2):
      stable_views mem2 views.
    Proof.
      ii. exploit CLOSED1; eauto. i.
      inv x. specialize (RLX loc0). des.
      exploit Memory.future_get1; try exact RLX; eauto. i. des.
      rewrite GET0 in *. inv GET. inv MSG_LE. inv RELEASED.
      etrans; eauto. eapply STABLE1; eauto.
    Qed.

    Lemma step_closed_views
          views1 views2 rel mem
          (MEM: Memory.closed mem)
          (CLOSED1: closed_views views1 mem)
          (CLOSED_REL: forall loc, Memory.closed_view (rel loc) mem)
          (VIEW: forall loc ts (LOC: ~ L loc) (NEQ: views2 loc ts <> views1 loc ts),
              exists from val released,
                Memory.get loc ts mem = Some (from, Message.concrete val released) /\
                views2 loc ts = (View.join (rel loc) (View.singleton_ur loc ts))
                                  :: (all_join_views (View.singleton_ur loc ts) (views1 loc from))):
      closed_views views2 mem.
    Proof.
      ii. destruct (classic (views2 loc ts = views1 loc ts)).
      { rewrite H in *. eauto. }
      hexploit VIEW; eauto. i. des.
      rewrite H1 in *. ss. des.
      { subst. apply Memory.join_closed_view; eauto.
        econs; ss.
        - ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          condtac; ss; subst; eauto. esplits. eapply MEM.
        - ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
          condtac; ss; subst; eauto. esplits. eapply MEM.
      }
      specialize (CLOSED1 loc from).
      remember (views1 loc from) as views.
      clear rel Heqviews CLOSED_REL VIEW H H1.
      induction views; ss. des; eauto.
      subst. apply Memory.join_closed_view; eauto.
      econs; ss.
      - ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; ss; subst; eauto. esplits. eapply MEM.
      - ii. unfold TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; ss; subst; eauto. esplits. eapply MEM.
    Qed.

    Lemma step_normal_views
          views1 views2 rel
          (NORMAL1: normal_views views1)
          (NORMAL_REL: forall loc (LOC: ~ L loc), Stable.normal_view L (rel loc))
          (VIEW: forall loc ts (LOC: ~ L loc) (NEQ: views2 loc ts <> views1 loc ts),
              exists from, views2 loc ts = (View.join (rel loc) (View.singleton_ur loc ts))
                                        :: (all_join_views (View.singleton_ur loc ts) (views1 loc from))):
      normal_views views2.
    Proof.
      ii. destruct (classic (views2 loc ts = views1 loc ts)).
      { rewrite H in *. eapply NORMAL1; eauto. }
      hexploit VIEW; eauto. i. des.
      rewrite H0 in *. ss. des.
      { subst. eapply Stable.join_normal_view; eauto.
        apply Stable.singleton_ur_normal_view. }
      specialize (NORMAL1 loc from).
      remember (views1 loc from) as views.
      clear rel Heqviews NORMAL_REL VIEW H H0.
      induction views; ss. des; eauto.
      subst. eapply Stable.join_normal_view; eauto.
      apply Stable.singleton_ur_normal_view.
    Qed.

    Lemma step_stable_views
          views1 views2 rel mem
          (STABLE1: stable_views mem views1)
          (STABLE_REL: forall loc (LOC: ~ L loc), Stable.stable_view L mem (rel loc))
          (VIEW: forall loc ts (LOC: ~ L loc) (NEQ: views2 loc ts <> views1 loc ts),
              exists from, views2 loc ts = (View.join (rel loc) (View.singleton_ur loc ts))
                                        :: (all_join_views (View.singleton_ur loc ts) (views1 loc from))):
      stable_views mem views2.
    Proof.
      ii. destruct (classic (views2 loc ts = views1 loc ts)).
      { rewrite H in *. eapply STABLE1; eauto. }
      hexploit VIEW; eauto. i. des.
      rewrite H0 in *. ss. des.
      { subst. etrans; [|eapply View.join_l].
        revert GET. unfold View.join, View.singleton_ur. ss.
        unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
        condtac; ss; try congr.
        rewrite time_le_join_l; try apply Time.bot_spec. i.
        eapply STABLE_REL; eauto.
      }
      specialize (STABLE1 loc from0).
      remember (views1 loc from0) as views.
      clear rel from0 Heqviews STABLE_REL VIEW H H0.
      induction views; ss. des; eauto.
      subst. etrans; [|eapply View.join_l].
      revert GET. unfold View.join, View.singleton_ur. ss.
      unfold TimeMap.join, TimeMap.singleton, LocFun.add, LocFun.init, LocFun.find.
      condtac; ss; try congr.
      rewrite time_le_join_l; try apply Time.bot_spec. i.
      eapply STABLE1; eauto.
    Qed.


    (* well-formedness *)

    Inductive wf_pf (tr: Trace.t) (e: Thread.t lang): Prop :=
    | wf_pf_intro
        (WF: Local.wf e.(Thread.local) e.(Thread.memory))
        (SC: Memory.closed_timemap e.(Thread.sc) e.(Thread.memory))
        (MEM: Memory.closed e.(Thread.memory))
        (TRACE: TraceWF.wf tr e.(Thread.local).(Local.promises) e.(Thread.memory))
    .
    Hint Constructors wf_pf.

    Inductive wf_j (views: Loc.t -> Time.t -> list View.t) (e: Thread.t lang): Prop :=
    | wf_j_intro
        (WF: Local.wf e.(Thread.local) e.(Thread.memory))
        (SC: Memory.closed_timemap e.(Thread.sc) e.(Thread.memory))
        (MEM: Memory.closed e.(Thread.memory))
        (JOINED_REL: joined_released views e.(Thread.local).(Local.promises) e.(Thread.local).(Local.tview).(TView.rel))
        (JOINED_MEM: joined_memory views e.(Thread.memory))
        (JOINED_VIEWS: wf_views views)
    .
    Hint Constructors wf_j.

    Inductive wf_ra (rels: ReleaseWrites.t) (e: Thread.t lang): Prop :=
    | wf_ra_intro
        (WF: Local.wf e.(Thread.local) e.(Thread.memory))
        (SC: Memory.closed_timemap e.(Thread.sc) e.(Thread.memory))
        (MEM: Memory.closed e.(Thread.memory))
        (RELS: ReleaseWrites.wf rels e.(Thread.local).(Local.promises) e.(Thread.memory))
    .
    Hint Constructors wf_ra.

    Lemma step_pf_future
          tr1 pf e e1 e2
          (WF1: wf_pf tr1 e1)
          (STEP: Thread.step pf e e1 e2):
      <<WF2_PF: wf_pf (tr1 ++ [(e1.(Thread.local), e)]) e2>>.
    Proof.
      inv WF1. exploit Thread.step_future; eauto. i. des.
      econs; eauto.
      apply TraceWF.wf_app.
      - eapply TraceWF.steps_wf_other; eauto.
      - eapply TraceWF.steps_wf; eauto.
    Qed.

    Lemma step_j_future
          pf e e1 e2 views1 views2
          (WF1: wf_j views1 e1)
          (STEP: JThread.step pf e e1 e2 views1 views2):
      <<WF2_J: wf_j views2 e2>>.
    Proof.
      inv WF1. exploit JThread.step_future; eauto. i. des. eauto.
    Qed.

    Lemma step_ra_future
          rels1 rels2 e e1 e2
          (WF1: wf_ra rels1 e1)
          (STEP: RAThread.step lang L rels1 rels2 e e1 e2):
      <<WF2_RA: wf_ra rels2 e2>>.
    Proof.
      inv WF1. hexploit RAThread.step_rels_wf; eauto. i. inv STEP.
      - exploit OrdThread.step_future; eauto. i. des. eauto.
      - exploit OrdThread.step_future; eauto. i. des. eauto.
    Qed.

    Lemma steps_pf_future
          tr1 tr e1 e2
          (WF1: wf_pf tr1 e1)
          (STEPS: Trace.steps tr e1 e2):
      <<WF2_PF: wf_pf (tr1 ++ tr) e2>>.
    Proof.
      inv WF1. exploit Trace.steps_future; eauto. i. des.
      econs; eauto.
      apply TraceWF.wf_app.
      - eapply TraceWF.steps_wf_other; eauto.
      - eapply TraceWF.steps_wf; eauto.
    Qed.

    Lemma steps_j_future
          e1 e2 views1 views2
          (WF1: wf_j views1 e1)
          (STEPS: JThread.rtc_tau e1 e2 views1 views2):
      <<WF2_J: wf_j views2 e2>>.
    Proof.
      inv WF1. exploit JThread.tau_steps_future; eauto. i. des. eauto.
    Qed.

    Lemma steps_ra_future
          rels1 rels2 e1 e2
          (WF1: wf_ra rels1 e1)
          (STEPS: RAThread.steps lang L rels1 rels2 e1 e2):
      <<WF2_RA: wf_ra rels2 e2>>.
    Proof.
      induction STEPS; eauto.
      exploit step_ra_future; eauto.
    Qed.


    (* sim_thread *)

    Inductive sim_thread (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t)
              (e_pf e_j e_ra: Thread.t lang): Prop :=
    | sim_thread_intro
        (SIM_JOINED: JSim.sim_thread views e_j e_pf)
        (SIM_RA: PFtoRASimThread.sim_thread L rels e_ra e_j)

        (NORMAL_J: PFtoRASimThread.normal_thread L e_j)
        (NORMAL_RA: PFtoRASimThread.normal_thread L e_ra)
        (STABLE_RA: PFtoRASimThread.stable_thread L rels e_ra)
        (CLOSED_VIEWS: closed_views views e_ra.(Thread.memory))
        (NORMAL_VIEWS: normal_views views)
        (STABLE_VIEWS: stable_views e_ra.(Thread.memory) views)
    .

    Definition sim_trace (tr: Trace.t) (rels: ReleaseWrites.t): Prop :=
      forall th e loc from to val released ord
        (IN: List.In (th, e) tr)
        (EVENT: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord))
        (ORD: Ordering.le ord Ordering.strong_relaxed),
        ~ List.In (loc, to) rels.

    Lemma sim_thread_step_aux
          views1 rels1 e1_pf e1_j e1_ra
          pf e_pf e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_ra)
          (JOINED_REL: joined_released views1 e1_j.(Thread.local).(Local.promises) e1_j.(Thread.local).(Local.tview).(TView.rel))
          (JOINED_MEM: joined_memory views1 e1_j.(Thread.memory))
          (JOINED_VIEWS: wf_views views1)
          (WF1_PF: Local.wf e1_pf.(Thread.local) e1_pf.(Thread.memory))
          (SC1_PF: Memory.closed_timemap e1_pf.(Thread.sc) e1_pf.(Thread.memory))
          (MEM1_PF: Memory.closed e1_pf.(Thread.memory))
          (WF1_J: Local.wf e1_j.(Thread.local) e1_j.(Thread.memory))
          (SC1_J: Memory.closed_timemap e1_j.(Thread.sc) e1_j.(Thread.memory))
          (MEM1_J: Memory.closed e1_j.(Thread.memory))
          (WF1_RA: Local.wf e1_ra.(Thread.local) e1_ra.(Thread.memory))
          (SC1_RA: Memory.closed_timemap e1_ra.(Thread.sc) e1_ra.(Thread.memory))
          (MEM1_RA: Memory.closed e1_ra.(Thread.memory))
          (STEP_PF: Thread.step pf e_pf e1_pf e2_pf)
          (CONS: Local.promise_consistent e2_pf.(Thread.local))
          (PROMISE: forall loc from to msg kind
                      (EVENT: e_pf = ThreadEvent.promise loc from to msg kind)
                      (LOC: L loc),
              msg = Message.reserve):
      exists views2 e_j pf_j e2_j e_ra e2_ra,
        (<<STEP_J: JThread.step pf_j e_j e1_j e2_j views1 views2>>) /\
        (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\
        (<<STEP_RA: OrdThread.step L Ordering.acqrel pf_j e_ra e1_ra e2_ra>>) /\
        __guard__
          ((<<SIM2: sim_thread views2 (ReleaseWrites.append L e_ra rels1) e2_pf e2_j e2_ra>>) /\
           (<<EVENT_RA: PFtoRASimThread.sim_event e_ra e_j>>) \/
           (<<CONS: Local.promise_consistent e1_ra.(Thread.local)>>) /\
           (<<RACE: exists loc to val released ord,
               ThreadEvent.is_reading e_ra = Some (loc, to, val, released, ord) /\
               RAThread.ra_race L rels1 e1_ra.(Thread.local).(Local.tview) loc to ord>>)).
    Proof.
      hexploit JSim.sim_thread_step; try exact STEP; try eapply SIM1; eauto. i. des.
      destruct (classic (exists loc from to msg kind,
                            e_src = ThreadEvent.promise loc from to msg kind /\ ~ L loc)); cycle 1.
      { (* normal step *)
        inv STEP.
        hexploit PFtoRASimThread.thread_step; try exact STEP1; try eapply SIM1; eauto.
        { i. subst. destruct (L loc) eqn:LOC.
          - split; ss. inv EVENT.
            exploit PROMISE; eauto. i. subst. inv MSG. ss.
          - exfalso. apply H. esplits; eauto. congr.
        }
        i. unguard. des.
        - esplits; eauto. left. split; ss.
          exploit Thread.step_future; try exact STEP_PF; eauto. i. des.
          exploit Thread.step_future; try eapply STEP0; eauto. i. des.
          exploit OrdThread.step_future; try exact STEP_SRC; eauto. i. des.
          econs; eauto.
          + hexploit future_closed_views; try eapply SIM1; eauto. i.
            eapply step_closed_views; try eapply SIM1; eauto.
            * inv WF1. inv TVIEW_CLOSED. apply REL.
            * i. exploit VIEWSLE; eauto. i. des.
              inv SIM2. inv MEMORY0.
              exploit COMPLETE; try exact GET. i. des. inv MSG.
              inv LOCAL. inv TVIEW. specialize (REL loc). des_ifs.
              rewrite REL. esplits; eauto.
          + eapply step_normal_views; try eapply SIM1; eauto.
            * inv NORMAL2_SRC. inv NORMAL_TVIEW. i. eapply (REL loc).
            * i. exploit VIEWSLE; eauto. i. des.
              inv SIM2. inv MEMORY0.
              exploit COMPLETE; try exact GET. i. des. inv MSG.
              inv LOCAL. inv TVIEW. specialize (REL loc). des_ifs.
              rewrite REL. esplits; eauto.
          + hexploit future_stable_views; try eapply SIM1; eauto. i.
            eapply step_stable_views; try eapply SIM1; eauto.
            * inv STABLE2_SRC. inv STABLE_TVIEW. i. eapply (REL loc); eauto.
            * i. exploit VIEWSLE; eauto. i. des.
              inv SIM2. inv MEMORY0.
              exploit COMPLETE; try exact GET. i. des. inv MSG.
              inv LOCAL. inv TVIEW. specialize (REL loc). des_ifs.
              rewrite REL. esplits; eauto.
        - esplits; eauto. right. esplits; eauto.
          hexploit step_promise_consistent; try exact STEP_PF; try apply SIM1; eauto. i.
          inv SIM1. inv SIM_JOINED. inv SIM_RA.
          apply inj_pair2 in H4. subst.
          apply inj_pair2 in H5. subst. ss.
          hexploit JSim.sim_local_promise_consistent; try exact LOCAL; eauto. i. des.
          eapply PFtoRASimThread.sim_local_promise_consistent; eauto.
      }

      (* promise on ~ L *)
      des. subst. dup STEP. inv STEP0.
      inv STEP1; [|inv STEP0; inv LOCAL]. inv STEP0. ss.
      hexploit PFtoRASimThread.promise_step; try exact LOCAL; try eapply SIM1; eauto; try congr. s. i. des.
      destruct e1_ra. esplits; eauto.
      { econs. econs; eauto. }
      left.
      assert (MSG: forall (val: Const.t) (released: View.t) (MSG: msg = Message.concrete val (Some released)),
                 Stable.normal_view L released /\ Stable.stable_view L mem2_src released).
      { i. subst. split.
        - hexploit (@step_normal_views views1 views0); try eapply SIM1; eauto.
          { inv SIM1. ss. inv NORMAL_RA. inv NORMAL_TVIEW. i. eapply (REL loc0). }
          { s. i. exploit VIEWSLE; eauto. i. des.
            inv MEM2.
            exploit COMPLETE; try exact GET. i. des. inv MSG.
            inv LC2. inv TVIEW. specialize (REL loc0). des_ifs.
            inv STEP_SRC. ss. rewrite REL. esplits; eauto. }
          i. exploit PROMISE0; eauto. i. des.
          eapply joined_opt_view_normal_view; eauto.
        - exploit Local.promise_step_future; try exact STEP_SRC; eauto. s. i. des.
          hexploit future_closed_views; try eapply SIM1; try exact FUTURE. i.
          hexploit future_stable_views; try eapply SIM1; try exact FUTURE. i.
          hexploit (@step_stable_views views1 views0); try exact H1; eauto.
          { inv SIM1. ss. inv STABLE_RA. ss. inv STABLE_TVIEW.
            i. hexploit (REL loc0); ss. i.
            hexploit Stable.future_stable_view; try exact H2; try exact FUTURE; try eapply WF1_RA. i.
            eapply H3. }
          { i. exploit VIEWSLE; eauto. i. des.
            inv MEM2.
            exploit COMPLETE; try exact GET. i. des. inv MSG.
            inv LC2. inv TVIEW. specialize (REL loc0). des_ifs.
            inv STEP_SRC. ss. rewrite REL. esplits; eauto. }
          i. exploit PROMISE0; eauto. i. des.
          eapply joined_opt_view_stable_view; eauto.
      }
      hexploit PFtoRASimThread.sim_memory_stable_tview; try eapply SIM1. s. i.
      hexploit PFtoRASimThread.sim_memory_stable_memory; try eapply SIM1. s. i.
      exploit PFtoRASimThread.sim_release_writes_wf; try eapply SIM1. s. i. des.
      hexploit Stable.promise_step; try exact LOCAL; try eapply SIM1; eauto.
      { i. subst. exploit MSG; eauto. i. des. split; ss.
        eapply PFtoRASimThread.sim_memory_stable_view; eauto. }
      i. des.
      hexploit Stable.promise_step; try exact STEP_SRC; try eapply SIM1; eauto. i. des.
      split; try by econs.
      exploit Thread.step_future; try exact STEP_PF; eauto. i. des.
      exploit Local.promise_step_future; try exact LOCAL; eauto. s. i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; eauto. s. i. des.
      econs; ss; eauto.
      - inv SIM1. inv SIM_RA. econs; ss; eauto.
      - unfold ReleaseWrites.append. ss. econs; ss; eauto.
        inv SIM1. ss.
        eapply Stable.future_stable_view; try exact FUTURE0; try eapply SIM; ss.
        apply STABLE_RA.
      - hexploit future_closed_views; try eapply SIM1; eauto. i.
        eapply step_closed_views; try eapply SIM1; eauto.
        + inv WF1. inv TVIEW_CLOSED. apply REL.
        + i. exploit VIEWSLE; eauto. i. des.
          inv MEM2.
          exploit COMPLETE; try exact GET. i. des. inv MSG0.
          inv LC2. inv TVIEW. specialize (REL loc0). des_ifs.
          rewrite REL. esplits; eauto.
      - eapply step_normal_views; try eapply SIM1; eauto.
        + inv NORMAL_TVIEW0. i. eapply (REL loc0).
        + i. exploit VIEWSLE; eauto. i. des.
          inv MEM2.
          exploit COMPLETE; try exact GET. i. des. inv MSG0.
          inv LC2. inv TVIEW. specialize (REL loc0). des_ifs.
          rewrite REL. esplits; eauto.
      - hexploit future_stable_views; try eapply SIM1; eauto. i.
        eapply step_stable_views; try eapply SIM1; eauto.
        + inv STABLE_TVIEW0. i. eapply (REL loc0); eauto.
        + i. exploit VIEWSLE; eauto. i. des.
          inv MEM2.
          exploit COMPLETE; try exact GET. i. des. inv MSG0.
          inv LC2. inv TVIEW. specialize (REL loc0). des_ifs.
          rewrite REL. esplits; eauto.
    Qed.

    Lemma sim_thread_step
          tr1 views1 rels1 e1_pf e1_j e1_ra
          pf e_pf e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_ra)
          (SIM_TR1: sim_trace tr1 rels1)
          (WF1_PF: wf_pf tr1 e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: Thread.step pf e_pf e1_pf e2_pf)
          (PF: pf_event L e_pf)
          (CONS: Local.promise_consistent e2_pf.(Thread.local)):
      (exists views2 rels2 pf_j e_j e2_j e_ra e2_ra,
          (<<STEP_J: JThread.step pf_j e_j e1_j e2_j views1 views2>>) /\
          (<<STEP_RA: RAThread.step lang L rels1 rels2 e_ra e1_ra e2_ra>>) /\
          (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\
          (<<EVENT_RA: PFtoRASimThread.sim_event e_ra e_j>>) /\
          (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_ra>>) /\
          (<<SIM_TR2: sim_trace (tr1 ++ [(e1_pf.(Thread.local), e_pf)]) rels2>>)) \/
      (exists rels2 e2_ra,
          (<<RACE: RAThread.step lang L rels1 rels2 ThreadEvent.failure e1_ra e2_ra>>)).
    Proof.
      exploit sim_thread_step_aux; eauto; try apply WF1_PF; try apply WF1_J; try apply WF1_RA.
      i. unguard. des.
      - left. esplits; eauto.
        + econs 1. eauto.
        + ii. apply List.in_app_or in IN.
          apply ReleaseWrites.in_append_or in H. des.
          * inv WF1_PF. exploit TRACE; eauto. i. inv x.
            inv EVENT_J; inv EVENT_RA; ss.
            { inv H. inv STEP; inv STEP0. inv LOCAL. inv LOCAL0. inv WRITE. ss.
              inv PROMISE; ss.
              - exploit Memory.add_get0; try exact MEM0. i. des. congr.
              - exploit Memory.split_get0; try exact MEM0. i. des. congr.
              - exploit Memory.lower_get0; try exact PROMISES. i. des. congr. }
            { inv H. inv STEP; inv STEP0. inv LOCAL. inv LOCAL1. inv LOCAL2. inv WRITE. ss.
              inv PROMISE; ss.
              - exploit Memory.add_get0; try exact MEM0. i. des. congr.
              - exploit Memory.split_get0; try exact MEM0. i. des. congr.
              - exploit Memory.lower_get0; try exact PROMISES. i. des. congr. }
          * inv IN; ss. inv H2. inv EVENT_J; inv EVENT_RA; ss.
            { inv H. inv EVENT. destruct ord; ss. }
            { inv H. inv EVENT. destruct ord; ss. }
          * eapply SIM_TR1; eauto.
          * inv IN; ss. inv H0.
            inv WF1_RA. exploit RELS; eauto. i. des.
            inv EVENT_J; inv EVENT_RA; ss.
            { inv EVENT.
              inv STEP_RA; inv STEP0. inv LOCAL. inv LOCAL0. inv STEP0. inv WRITE. ss.
              inv PROMISE; ss.
              - exploit Memory.add_get0; try exact MEM0. i. des. congr.
              - exploit Memory.split_get0; try exact MEM0. i. des. congr.
              - exploit Memory.lower_get0; try exact PROMISES. i. des. congr. }
            { inv EVENT.
              inv STEP_RA; inv STEP0. inv LOCAL. inv LOCAL1. inv STEP0. inv LOCAL2. inv STEP0. inv WRITE. ss.
              inv PROMISE; ss.
              - exploit Memory.add_get0; try exact MEM0. i. des. congr.
              - exploit Memory.split_get0; try exact MEM0. i. des. congr.
              - exploit Memory.lower_get0; try exact PROMISES. i. des. congr. }
      - right. esplits. econs 2; eauto.
    Qed.

    Lemma sim_thread_steps
          tr1 views1 rels1 e1_pf e1_j e1_ra
          tr e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_ra)
          (SIM_TR1: sim_trace tr1 rels1)
          (WF1_PF: wf_pf tr1 e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEPS: Trace.steps tr e1_pf e2_pf)
          (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr)
          (PF: List.Forall (compose (pf_event L) snd) tr)
          (CONS: Local.promise_consistent e2_pf.(Thread.local)):
      (exists views2 rels2 e2_j e2_ra,
          (<<STEPS_J: JThread.rtc_tau e1_j e2_j views1 views2>>) /\
          (<<STEPS_RA: RAThread.tau_steps lang L rels1 rels2 e1_ra e2_ra>>) /\
          (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_ra>>) /\
          (<<SIM_TR2: sim_trace (tr1 ++ tr) rels2>>)) \/
      (exists rels2 rels3 e2_ra e3_ra,
          (<<STEPS_RA: RAThread.tau_steps lang L rels1 rels2 e1_ra e2_ra>>) /\
          (<<RACE: RAThread.step lang L rels2 rels3 ThreadEvent.failure e2_ra e3_ra>>)).
    Proof.
      revert tr1 views1 rels1 e1_j e1_ra SIM1 SIM_TR1 WF1_PF WF1_J WF1_RA SILENT PF CONS.
      induction STEPS; i; ss.
      { left. esplits; eauto.
        - econs 1; eauto.
        - rewrite List.app_nil_r. ss. }
      subst. exploit sim_thread_step; try exact SIM1; eauto.
      { ii. inv PF. exploit H1; ss; eauto. }
      { exploit Thread.step_future; try exact STEP; try apply WF1_PF. i. des.
        eapply rtc_tau_step_promise_consistent; try eapply Trace.silent_steps_tau_steps; eauto.
        inv SILENT. ss. }
      i. unguard. des.
      - exploit step_pf_future; eauto. i. des.
        exploit step_j_future; eauto. i. des.
        exploit step_ra_future; eauto. i. des.
        exploit IHSTEPS; eauto.
        { inv SILENT. ss. }
        { inv PF. ss. }
        i. rewrite <- List.app_assoc in x. des.
        + left. esplits; try exact SIM0; eauto.
          * econs 2; [eauto|..]; eauto.
            inv SILENT. ss. inv EVENT_J; ss.
          * econs 2; [eauto|..]; eauto.
            inv SILENT. ss. inv EVENT_J; inv EVENT_RA; ss.
        + right. esplits; eauto.
          econs 2; [eauto|..]; eauto.
          inv SILENT. ss. inv EVENT_J; inv EVENT_RA; ss.
      - right. esplits; eauto. econs 1.
    Qed.

    Lemma cap_wf_pf
          tr e sc mem
          (WF: wf_pf tr e)
          (CAP: Memory.cap e.(Thread.memory) mem)
          (SC: Memory.max_concrete_timemap mem sc):
      wf_pf tr (Thread.mk lang e.(Thread.state) e.(Thread.local) sc mem).
    Proof.
      inv WF.
      exploit Local.cap_wf; eauto. i.
      exploit Memory.cap_closed; eauto. i.
      hexploit Memory.max_concrete_timemap_closed; eauto. i.
      econs; ss.
      ii. exploit TRACE; eauto. i. inv x. econs; ss.
      inv CAP. eauto.
    Qed.

    Lemma cap_wf_j
          views e sc mem
          (WF: wf_j views e)
          (CAP: Memory.cap e.(Thread.memory) mem)
          (SC: Memory.max_concrete_timemap mem sc):
      wf_j views (Thread.mk lang e.(Thread.state) e.(Thread.local) sc mem).
    Proof.
      inv WF.
      exploit Local.cap_wf; eauto. i.
      exploit Memory.cap_closed; eauto. i.
      hexploit Memory.max_concrete_timemap_closed; eauto. i.
      exploit JSim.joined_memory_cap; eauto.
    Qed.

    Lemma cap_wf_ra
          rels e sc mem
          (WF: wf_ra rels e)
          (CAP: Memory.cap e.(Thread.memory) mem)
          (SC: Memory.max_concrete_timemap mem sc):
      wf_ra rels (Thread.mk lang e.(Thread.state) e.(Thread.local) sc mem).
    Proof.
      inv WF.
      exploit Local.cap_wf; eauto. i.
      exploit Memory.cap_closed; eauto. i.
      hexploit Memory.max_concrete_timemap_closed; eauto. i.
      econs; ss.
      ii. exploit RELS; eauto. i. des.
      inv CAP. exploit SOUND; eauto.
    Qed.

    Lemma sim_thread_cap
          tr views rels e_pf e_j e_ra
          sc_pf mem_pf sc_j mem_j sc_ra mem_ra
          (SIM: sim_thread views rels e_pf e_j e_ra)
          (WF_PF: wf_pf tr e_pf)
          (WF_J: wf_j views e_j)
          (WF_RA: wf_ra rels e_ra)
          (CAP_PF: Memory.cap e_pf.(Thread.memory) mem_pf)
          (SC_PF: Memory.max_concrete_timemap mem_pf sc_pf)
          (CAP_J: Memory.cap e_j.(Thread.memory) mem_j)
          (SC_J: Memory.max_concrete_timemap mem_j sc_j)
          (CAP_RA: Memory.cap e_ra.(Thread.memory) mem_ra)
          (SC_RA: Memory.max_concrete_timemap mem_ra sc_ra):
      (<<SIM_CAP: sim_thread views rels
                             (Thread.mk lang e_pf.(Thread.state) e_pf.(Thread.local) sc_pf mem_pf)
                             (Thread.mk lang e_j.(Thread.state) e_j.(Thread.local) sc_j mem_j)
                             (Thread.mk lang e_ra.(Thread.state) e_ra.(Thread.local) sc_ra mem_ra)>>) /\
      (<<WF_PF_CAP: wf_pf tr (Thread.mk lang e_pf.(Thread.state) e_pf.(Thread.local) sc_pf mem_pf)>>) /\
      (<<WF_J_CAP: wf_j views (Thread.mk lang e_j.(Thread.state) e_j.(Thread.local) sc_j mem_j)>>) /\
      (<<WF_RA_CAP: wf_ra rels (Thread.mk lang e_ra.(Thread.state) e_ra.(Thread.local) sc_ra mem_ra)>>).
    Proof.
      exploit cap_wf_pf; eauto. i.
      exploit cap_wf_j; eauto. i.
      exploit cap_wf_ra; eauto. i.
      splits; ss.
      inv SIM. econs; ss.
      - inv WF_PF. inv WF_J. inv x0. inv x1. inv SIM_JOINED.
        apply inj_pair2 in H2. apply inj_pair2 in H3. subst. ss.
        econs; eauto.
        + eapply SimMemory.sim_memory_cap; eauto.
        + eapply SimMemory.sim_memory_cap in MEM; eauto.
          eapply SimMemory.sim_memory_max_concrete_timemap in MEM; eauto.
          subst. refl.
      - inv SIM_RA. econs; ss.
        + exploit PFtoRASimThread.sim_memory_cap; eauto; try apply WF_J; try apply WF_RA. i.
          eapply PFtoRASimThread.sim_memory_max_concrete_timemap; eauto.
        + eapply PFtoRASimThread.sim_memory_cap; eauto; try apply WF_J; try apply WF_RA.
      - inv NORMAL_J. econs; ss.
        eapply Stable.cap_normal_memory; eauto. apply WF_J.
      - inv NORMAL_RA. econs; ss.
        eapply Stable.cap_normal_memory; eauto. apply WF_RA.
      - inv WF_RA. inv STABLE_RA. econs; ss.
        + eapply Stable.cap_stable_tview; eauto.
        + eapply Stable.max_concrete_timemap_stable; eauto; try apply x2.
        + eapply Stable.cap_stable_memory; eauto.
      - ii. eapply Memory.cap_closed_view; eauto.
      - ii. exploit Memory.cap_inv; try exact CAP_RA; eauto; try apply WF_RA. i. des; ss.
        exploit STABLE_VIEWS; eauto.
    Qed.

    Lemma sim_thread_consistent
          tr1 views1 rels1 e1_pf e1_j e1_ra
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_ra)
          (SIM_TR1: sim_trace tr1 rels1)
          (WF1_PF: wf_pf tr1 e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_RA: wf_ra rels1 e1_ra)
          (CONSISTENT: pf_consistent L e1_pf):
      RAThread.consistent lang L rels1 e1_ra.
    Proof.
      exploit Memory.cap_exists; try apply WF1_PF. i. des.
      exploit Memory.cap_exists; try apply WF1_J. i. des.
      exploit Memory.cap_exists; try apply WF1_RA. i. des.
      exploit Memory.cap_closed; try eapply WF1_PF; eauto. i.
      exploit Memory.cap_closed; try eapply WF1_J; eauto. i.
      exploit Memory.cap_closed; try eapply WF1_RA; eauto. i.
      exploit Memory.max_concrete_timemap_exists; try eapply x0. i. des.
      exploit Memory.max_concrete_timemap_exists; try eapply x1. i. des.
      exploit Memory.max_concrete_timemap_exists; try eapply x2. i. des.
      exploit sim_thread_cap; eauto. i. des. ii.
      exploit Memory.cap_inj; [exact CAP2|exact CAP1|..]; try apply WF1_RA. i. subst.
      exploit Memory.max_concrete_timemap_inj; [exact SC_MAX|exact x5|]. i. subst.
      inv CONSISTENT. des. exploit CONSISTENT; eauto. i. des.
      - exploit sim_thread_steps; try exact STEPS; eauto.
        { inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0. ss. }
        i. des.
        + exploit steps_pf_future; try exact STEPS; eauto. i. des.
          exploit steps_j_future; try exact STEPS_J; eauto. i. des.
          exploit steps_ra_future; try eapply RAThread.tau_steps_steps;
            try exact STEPS_RA; eauto. i. des.
          exploit sim_thread_step; try exact FAILURE; eauto; ss.
          { inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0. ss. }
          i. des.
          * left. inv EVENT_J; inv EVENT_RA.
            unfold RAThread.steps_failure. esplits; eauto.
          * left. unfold RAThread.steps_failure. esplits; eauto.
        + left. unfold RAThread.steps_failure. esplits; eauto.
      - exploit sim_thread_steps; try exact STEPS; eauto.
        { ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. ss. }
        i. des.
        + right. esplits; eauto.
          inv SIM2. inv SIM_JOINED.
          apply inj_pair2 in H2. apply inj_pair2 in H3. subst. ss.
          exploit JSim.sim_local_memory_bot; eauto. i.
          inv SIM_RA. ss. subst. inv LOCAL0. congr.
        + left. unfold RAThread.steps_failure. esplits; eauto.
    Qed.
  End PFtoRAThread.
End PFtoRAThread.
