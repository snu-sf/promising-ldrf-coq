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
Require Import Configuration.

Require Import PromiseConsistent.
Require Import Trace.
Require Import MemoryProps.
Require Import Mapping.
Require Import JoinedView.

Require Import PFStep.
Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.
Require Import PFtoAPFSim.
Require Import APFtoRASim.

Set Implicit Arguments.


Module PFtoRAThread.
  Section PFtoRAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Definition closed_views (views: Loc.t -> Time.t -> list View.t) (mem: Memory.t): Prop :=
      forall loc ts view (LOC: ~ L loc) (IN: List.In view (views loc ts)),
        Memory.closed_view view mem.

    Definition normal_views (views: Loc.t -> Time.t -> list View.t): Prop :=
      forall loc ts view (LOC: ~ L loc) (IN: List.In view (views loc ts)),
        Normal.normal_view L view.

    Definition stable_views (mem: Memory.t) (views: Loc.t -> Time.t -> list View.t): Prop :=
      forall loc ts view (LOC: ~ L loc) (IN: List.In view (views loc ts)),
        Stable.stable_view L mem view.

    Lemma joined_opt_view_normal_view
          views loc ts released
          (NORMAL: normal_views views)
          (LOC: ~ L loc)
          (JOINED: joined_opt_view (views loc ts) (Some released)):
      Normal.normal_view L released.
    Proof.
      specialize (NORMAL loc ts).
      inv JOINED. induction JOINED0; ss.
      apply Normal.join_normal_view; eauto.
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
      exploit Memory.future_get1; try exact RLX; eauto; ss. i. des.
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
          (NORMAL_REL: forall loc (LOC: ~ L loc), Normal.normal_view L (rel loc))
          (VIEW: forall loc ts (LOC: ~ L loc) (NEQ: views2 loc ts <> views1 loc ts),
              exists from, views2 loc ts = (View.join (rel loc) (View.singleton_ur loc ts))
                                        :: (all_join_views (View.singleton_ur loc ts) (views1 loc from))):
      normal_views views2.
    Proof.
      ii. destruct (classic (views2 loc ts = views1 loc ts)).
      { rewrite H in *. eapply NORMAL1; eauto. }
      hexploit VIEW; eauto. i. des.
      rewrite H0 in *. ss. des.
      { subst. eapply Normal.join_normal_view; eauto.
        apply Normal.singleton_ur_normal_view.
      }
      specialize (NORMAL1 loc from).
      remember (views1 loc from) as views.
      clear rel Heqviews NORMAL_REL VIEW H H0.
      induction views; ss. des; eauto.
      subst. eapply Normal.join_normal_view; eauto.
      apply Normal.singleton_ur_normal_view.
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
        rewrite TimeFacts.le_join_l; try apply Time.bot_spec. i.
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
      rewrite TimeFacts.le_join_l; try apply Time.bot_spec. i.
      eapply STABLE1; eauto.
    Qed.


    (* well-formedness *)

    Variant wf_pf (e: Thread.t lang): Prop :=
    | wf_pf_intro
        (WF: Local.wf (Thread.local e) (Thread.memory e))
        (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
        (MEM: Memory.closed (Thread.memory e))
    .
    Hint Constructors wf_pf: core.

    Variant wf_j (views: Loc.t -> Time.t -> list View.t) (e: Thread.t lang): Prop :=
    | wf_j_intro
        (WF: Local.wf (Thread.local e) (Thread.memory e))
        (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
        (MEM: Memory.closed (Thread.memory e))
        (JOINED_REL: joined_released views (Local.promises (Thread.local e)) (Local.tview (Thread.local e)).(TView.rel))
        (JOINED_MEM: joined_memory views (Thread.memory e))
        (JOINED_VIEWS: wf_views views)
    .
    Hint Constructors wf_j: core.

    Variant wf_ra (rels: Writes.t) (e: Thread.t lang): Prop :=
    | wf_ra_intro
        (WF: Local.wf (Thread.local e) (Thread.memory e))
        (SC: Memory.closed_timemap (Thread.sc e) (Thread.memory e))
        (MEM: Memory.closed (Thread.memory e))
        (RELS: Writes.wf L rels (Thread.memory e))
        (RESERVE_ONLY: OrdLocal.reserve_only L (Local.promises (Thread.local e)))
    .
    Hint Constructors wf_ra: core.

    Lemma step_pf_future
          pf e e1 e2
          (WF1: wf_pf e1)
          (STEP: Thread.step pf e e1 e2):
      <<WF2_PF: wf_pf e2>>.
    Proof.
      inv WF1. exploit Thread.step_future; eauto. i. des.
      econs; eauto.
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
          ordr ordw rels1 rels2 e e1 e2
          (WF1: wf_ra rels1 e1)
          (ORDC: Ordering.le Ordering.plain ordw)
          (STEP: WThread.step L ordr ordw rels1 rels2 e e1 e2):
      <<WF2_APF: wf_ra rels2 e2>>.
    Proof.
      inv WF1.
      hexploit WThread.step_future; eauto. i. des.
      hexploit WThread.step_reserve_only; eauto. i. des.
      inv STEP.
      hexploit Writes.step_wf; eauto; ss.
    Qed.

    Lemma opt_step_pf_future
          e e1 e2
          (WF1: wf_pf e1)
          (STEP: Thread.opt_step e e1 e2):
      <<WF2_PF: wf_pf e2>>.
    Proof.
      inv STEP; eauto using step_pf_future.
    Qed.

    Lemma opt_step_j_future
          e e1 e2 views1 views2
          (WF1: wf_j views1 e1)
          (STEP: JThread.opt_step e e1 e2 views1 views2):
      <<WF2_J: wf_j views2 e2>>.
    Proof.
      inv STEP; eauto using step_j_future.
    Qed.

    Lemma opt_step_ra_future
          ordr ordw rels1 rels2 e e1 e2
          (WF1: wf_ra rels1 e1)
          (ORD: Ordering.le Ordering.plain ordw)
          (STEP: WThread.opt_step L ordr ordw rels1 rels2 e e1 e2):
      <<WF2_APF: wf_ra rels2 e2>>.
    Proof.
      inv STEP; eauto using step_ra_future.
    Qed.

    Lemma reserve_step_pf_future
          e1 e2
          (WF1: wf_pf e1)
          (STEP: Thread.reserve_step e1 e2):
      wf_pf e2.
    Proof.
      inv STEP. inv WF1.
      exploit Thread.step_future; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma reserve_step_j_future
          e1 e2 views
          (WF1: wf_j views e1)
          (STEP: JThread.reserve_step views e1 e2):
      wf_j views e2.
    Proof.
      inv STEP. inv WF1.
      exploit JThread.step_future; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma reserve_step_ra_future
          rels e1 e2
          (WF1: wf_ra rels e1)
          (STEP: Thread.reserve_step e1 e2):
      wf_ra rels e2.
    Proof.
      inv WF1.
      hexploit OrdThread.reserve_step_reserve_only; eauto. i. des.
      hexploit Writes.reserve_step_wf; eauto. i.
      inv STEP. exploit Thread.step_future; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma cancel_step_pf_future
          e1 e2
          (WF1: wf_pf e1)
          (STEP: Thread.cancel_step e1 e2):
      wf_pf e2.
    Proof.
      inv STEP. inv WF1.
      exploit Thread.step_future; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma cancel_step_j_future
          e1 e2 views
          (WF1: wf_j views e1)
          (STEP: JThread.cancel_step views e1 e2):
      wf_j views e2.
    Proof.
      inv STEP. inv WF1.
      exploit JThread.step_future; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma cancel_step_ra_future
          rels e1 e2
          (WF1: wf_ra rels e1)
          (STEP: Thread.cancel_step e1 e2):
      wf_ra rels e2.
    Proof.
      inv WF1.
      hexploit OrdThread.cancel_step_reserve_only; eauto. i. des.
      hexploit Writes.cancel_step_wf; eauto. i.
      inv STEP. exploit Thread.step_future; eauto. i. des.
      econs; eauto.
    Qed.

    Lemma steps_pf_future
          tr e1 e2
          (WF1: wf_pf e1)
          (STEPS: Trace.steps tr e1 e2):
      <<WF2_PF: wf_pf e2>>.
    Proof.
      inv WF1. exploit Trace.steps_future; eauto. i. des.
      econs; eauto.
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
          ordr ordw rels1 rels2 e1 e2
          (WF1: wf_ra rels1 e1)
          (ORDC: Ordering.le Ordering.plain ordw)
          (STEPS: WThread.steps L ordr ordw rels1 rels2 e1 e2):
      <<WF2_RA: wf_ra rels2 e2>>.
    Proof.
      induction STEPS; eauto.
      exploit step_ra_future; eauto.
    Qed.

    Lemma reserve_steps_pf_future
          e1 e2
          (WF1: wf_pf e1)
          (STEP: rtc (@Thread.reserve_step _) e1 e2):
      wf_pf e2.
    Proof.
      induction STEP; ss.
      eauto using reserve_step_pf_future.
    Qed.

    Lemma reserve_steps_j_future
          e1 e2 views
          (WF1: wf_j views e1)
          (STEP: rtc (@JThread.reserve_step views _) e1 e2):
      wf_j views e2.
    Proof.
      induction STEP; ss.
      eauto using reserve_step_j_future.
    Qed.

    Lemma reserve_steps_ra_future
          rels e1 e2
          (WF1: wf_ra rels e1)
          (STEP: rtc (@Thread.reserve_step _) e1 e2):
      wf_ra rels e2.
    Proof.
      induction STEP; ss.
      eauto using reserve_step_ra_future.
    Qed.

    Lemma cancel_steps_pf_future
          e1 e2
          (WF1: wf_pf e1)
          (STEP: rtc (@Thread.cancel_step _) e1 e2):
      wf_pf e2.
    Proof.
      induction STEP; ss.
      eauto using cancel_step_pf_future.
    Qed.

    Lemma cancel_steps_j_future
          e1 e2 views
          (WF1: wf_j views e1)
          (STEP: rtc (@JThread.cancel_step views _) e1 e2):
      wf_j views e2.
    Proof.
      induction STEP; ss.
      eauto using cancel_step_j_future.
    Qed.

    Lemma cancel_steps_ra_future
          rels e1 e2
          (WF1: wf_ra rels e1)
          (STEP: rtc (@Thread.cancel_step _) e1 e2):
      wf_ra rels e2.
    Proof.
      induction STEP; ss.
      eauto using cancel_step_ra_future.
    Qed.


    (* sim_thread *)

    Inductive sim_thread (views: Loc.t -> Time.t -> list View.t) (rels: Writes.t)
                         (e_pf e_j e_apf e_ra: Thread.t lang): Prop :=
    | sim_thread_intro
        (SIM_JOINED: JSim.sim_thread views e_j e_pf)
        (SIM_APF: PFtoAPFSim.sim_thread L rels e_apf e_j)
        (SIM_RA: APFtoRASim.sim_thread L rels e_ra e_apf)

        (NORMAL_APF: Normal.normal_thread L e_apf)
        (NORMAL_RA: Normal.normal_thread L e_ra)
        (STABLE_RA: Stable.stable_thread L rels e_ra)
        (CLOSED_VIEWS: closed_views views (Thread.memory e_ra))
        (NORMAL_VIEWS: normal_views views)
        (STABLE_VIEWS: stable_views (Thread.memory e_ra) views)
    .

    Lemma sim_thread_step_aux
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          pf e_pf e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (JOINED_REL: joined_released views1 (Local.promises (Thread.local e1_j)) (Local.tview (Thread.local e1_j)).(TView.rel))
          (JOINED_MEM: joined_memory views1 (Thread.memory e1_j))
          (JOINED_VIEWS: wf_views views1)
          (WRITES1_APF: Writes.wf L rels1 (Thread.memory e1_apf))
          (RESERVE_ONLY1_APF: OrdLocal.reserve_only L (Local.promises (Thread.local e1_apf)))
          (WRITES1_RA: Writes.wf L rels1 (Thread.memory e1_ra))
          (RESERVE_ONLY1_RA: OrdLocal.reserve_only L (Local.promises (Thread.local e1_ra)))
          (WF1_PF: Local.wf (Thread.local e1_pf) (Thread.memory e1_pf))
          (SC1_PF: Memory.closed_timemap (Thread.sc e1_pf) (Thread.memory e1_pf))
          (MEM1_PF: Memory.closed (Thread.memory e1_pf))
          (WF1_J: Local.wf (Thread.local e1_j) (Thread.memory e1_j))
          (SC1_J: Memory.closed_timemap (Thread.sc e1_j) (Thread.memory e1_j))
          (MEM1_J: Memory.closed (Thread.memory e1_j))
          (WF1_APF: Local.wf (Thread.local e1_apf) (Thread.memory e1_apf))
          (SC1_APF: Memory.closed_timemap (Thread.sc e1_apf) (Thread.memory e1_apf))
          (MEM1_APF: Memory.closed (Thread.memory e1_apf))
          (WF1_RA: Local.wf (Thread.local e1_ra) (Thread.memory e1_ra))
          (SC1_RA: Memory.closed_timemap (Thread.sc e1_ra) (Thread.memory e1_ra))
          (MEM1_RA: Memory.closed (Thread.memory e1_ra))
          (STEP_PF: Thread.step pf e_pf e1_pf e2_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf))
          (PROMISE: PF.pf_event L e_pf):
      (exists views2 e_j pf_j e2_j e_apf e2_apf e_ra e2_ra,
          (<<STEP_J: JThread.step pf_j e_j e1_j e2_j views1 views2>>) /\
          (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\
          (<<STEP_APF: OrdThread.step L Ordering.na Ordering.plain pf_j e_apf e1_apf e2_apf>>) /\
          (<<EVENT_APF: PFtoAPFSim.sim_event e_apf e_j>>) /\
          (<<STEP_RA: OrdThread.step L Ordering.acqrel Ordering.acqrel pf_j e_ra e1_ra e2_ra>>) /\
          (<<EVENT_RA: APFtoRASim.sim_event e_ra e_apf>>) /\
          (<<SIM2: sim_thread views2 (Writes.append L e_ra rels1) e2_pf e2_j e2_apf e2_ra>>)) \/
      (<<CONS: Local.promise_consistent (Thread.local e1_ra)>>) /\
      (<<RACE: RARaceW.ra_race L rels1 (Local.tview (Thread.local e1_ra)) (ThreadEvent.get_program_event e_pf)>>).
    Proof.
      hexploit JSim.sim_thread_step; try exact STEP; try eapply SIM1; eauto. i. des.
      destruct (classic (exists loc from to msg kind,
                            e_src = ThreadEvent.promise loc from to msg kind /\ ~ L loc)); cycle 1.
      { (* normal step *)
        inv STEP.
        hexploit PFtoAPFSim.thread_step; try eapply SIM1; eauto.
        { i. subst. inv EVENT.
          apply NNPP. ii. apply H. esplits; eauto. ii.
          apply H0. split; ss.
          exploit PROMISE; eauto. i. subst. inv MSG. ss.
        }
        i. des; cycle 1.
        { (* race *)
          right. splits.
          - eapply APFtoRASim.sim_thread_promise_consistent; try apply SIM1.
            eapply PFtoAPFSim.sim_thread_promise_consistent; try apply SIM1.
            inv SIM1. inv SIM_JOINED.
            apply inj_pair2 in H3, H4. subst. ss.
            eapply JSim.sim_local_promise_consistent; eauto.
            hexploit step_promise_consistent; try exact STEP_PF; eauto.
          - erewrite <- JSim.sim_event_program_event; eauto.
            erewrite APFtoRASim.sim_thread_ra_race; try apply SIM1; eauto.
        }
        hexploit APFtoRASim.thread_step; try exact STEP_SRC; try eapply SIM1; eauto.
        { i. subst. inv EVENT0. inv EVENT.
          apply NNPP. ii. apply H. esplits; eauto. ii.
          apply H0. split; ss.
          exploit PROMISE; eauto. i. subst. inv MSG. ss.
        }
        { inv EVENT0; ss. }
        { inv EVENT0; ss. }
        { inv EVENT0; ss. }
        i. des; cycle 1.
        { (* race *)
          right. splits.
          - eapply APFtoRASim.sim_thread_promise_consistent; try apply SIM1.
            eapply PFtoAPFSim.sim_thread_promise_consistent; try apply SIM1.
            inv SIM1. inv SIM_JOINED.
            apply inj_pair2 in H3, H4. subst. ss.
            eapply JSim.sim_local_promise_consistent; eauto.
            hexploit step_promise_consistent; try exact STEP_PF; eauto.
          - erewrite <- JSim.sim_event_program_event; try eapply EVENT.
            erewrite <- PFtoAPFSim.sim_event_eq_program_event; try exact EVENT0; eauto.
        }

        left. unguard. des. esplits; eauto.
        exploit Thread.step_future; try exact STEP_PF; eauto. i. des.
        exploit Thread.step_future; try eapply STEP0; eauto. i. des.
        exploit OrdThread.step_future; try exact STEP_SRC; eauto. i. des.
        exploit OrdThread.step_future; try exact STEP_SRC0; eauto. i. des.
        assert (VIEWS: forall loc ts (LOC: ~ L loc) (NEQ: views0 loc ts <> views1 loc ts),
                   exists from val released,
                     Memory.get loc ts (Thread.memory e2_src0) = Some (from, Message.concrete val released) /\
                     views0 loc ts =
                     (View.join (TView.rel (Local.tview (Thread.local e2_src0)) loc)
                                (View.singleton_ur loc ts))
                       :: (all_join_views (View.singleton_ur loc ts) (views1 loc from))).
        { i. exploit VIEWSLE; eauto. i. des.
          inv SIM2. inv MEMORY0.
          unfold Memory.get in GET. rewrite <- EQ in GET; ss.
          inv SIM0. inv MEMORY0.
          exploit COMPLETE0; try exact GET. i. des. inv MSG. des_ifs.
          esplits; eauto.
          inv LOCAL0. inv TVIEW. specialize (REL loc). des_ifs.
          rewrite REL. rewrite LOCAL. ss.
        }
        econs; eauto.
        - inv EVENT1; ss.
        - hexploit future_closed_views; try eapply SIM1; eauto. i.
          eapply step_closed_views; try eapply SIM1; eauto.
          inv WF3. inv TVIEW_CLOSED. apply REL.
        - eapply step_normal_views; try eapply SIM1; eauto.
          + inv NORMAL2_SRC0. inv NORMAL_TVIEW. i. eapply (REL loc).
          + i. exploit VIEWS; eauto. i. des. eauto.
        - hexploit future_stable_views; try eapply SIM1; eauto. i.
          eapply step_stable_views; try eapply SIM1; eauto.
          + inv STABLE2_SRC. inv STABLE_TVIEW. i. eapply (REL loc); eauto.
          + i. exploit VIEWS; eauto. i. des. eauto.
      }

      (* promise on ~ L *)
      des. subst. dup STEP. inv STEP0.
      inv STEP1; [|inv STEP0; inv LOCAL]. inv STEP0. ss.
      hexploit PFtoAPFSim.promise_step; try exact LOCAL; try eapply SIM1; eauto.
      { i. destruct msg; ss. exploit PROMISE0; eauto. i. des.
        inv x; eauto. econs. econs.
        hexploit Memory.promise_inhabited; try exact PROMISE1; try apply MEM1_APF. i.
        eapply joined_view_closed; try exact JOINED; eauto.
        assert (VIEWS1: closed_views views1 mem2_src).
        { ii. eapply Memory.promise_closed_view; eauto.
          eapply APFtoRASim.sim_memory_closed_view_src; try eapply SIM1; eauto.
        }
        destruct (classic (views0 loc to = views1 loc to)).
        { rewrite H1. rewrite List.Forall_forall. i. eauto. }
        exploit VIEWSLE; eauto. i. des. rewrite VIEW.
        exploit Memory.promise_get0; try exact PROMISE1.
        { inv PROMISE1; ss. }
        i. des.
        exploit Memory.singleton_ur_closed_view; try exact GET_MEM; eauto. i.
        inv LOCAL. ss. inv SIM1. inv SIM_APF. ss. subst.
        econs.
        - eapply Memory.join_closed_view; eauto.
          eapply Memory.promise_closed_view; try exact PROMISE1.
          apply WF1_APF.
        - rewrite List.Forall_forall. i.
          apply List.in_map_iff in H2. des. subst.
          eapply Memory.join_closed_view; eauto.
      }
      i. des. subst.
      hexploit APFtoRASim.promise_step; try exact STEP_SRC; try eapply SIM1; eauto; try congr. i. des.
      destruct e1_apf, e1_ra. ss.
      left. esplits; eauto.
      { econs 1; [econs|]; eauto. ii. clarify. }
      { econs. }
      { econs 1; [econs|]; eauto. ii. clarify. }
      { econs. }
      { assert (VIEWS: forall loc ts (LOC: ~ L loc) (NEQ: views0 loc ts <> views1 loc ts),
                   exists from val released,
                     Memory.get loc ts mem2_src0 = Some (from, Message.concrete val released) /\
                     views0 loc ts =
                     (View.join (TView.rel (Local.tview lc2_src) loc)
                                (View.singleton_ur loc ts))
                       :: (all_join_views (View.singleton_ur loc ts) (views1 loc from))).
        { i. exploit VIEWSLE; eauto. i. des.
          inv MEM2.
          unfold Memory.get in GET. rewrite <- EQ in GET; ss.
          inv MEM0.
          exploit COMPLETE0; try exact GET. i. des. inv MSG. des_ifs.
          esplits; eauto.
          inv LC2. inv TVIEW. specialize (REL loc0). des_ifs.
          rewrite REL. ss.
        }
        assert (MSG: forall (val: Const.t) (released: View.t) (MSG: msg = Message.concrete val (Some released)),
                   Normal.normal_view L released /\ Stable.stable_view L mem2_src0 released).
        { i. subst. split.
          - hexploit (@step_normal_views views1 views0); try eapply SIM1; eauto.
            { inv SIM1. ss. inv NORMAL_RA. inv NORMAL_TVIEW. i. eapply (REL loc0). }
            { s. i. exploit VIEWS; eauto. i. des.
              inv STEP_SRC0. ss. eauto.
            }
            i. exploit PROMISE0; eauto. i. des.
            eapply joined_opt_view_normal_view; eauto.
          - exploit Local.promise_step_future; try exact STEP_SRC0; eauto. s. i. des.
            hexploit future_closed_views; try eapply SIM1; try exact FUTURE. i.
            hexploit future_stable_views; try eapply SIM1; try exact FUTURE. i.
            hexploit (@step_stable_views views1 views0); try exact H1; eauto.
            { inv SIM1. ss. inv STABLE_RA. ss. inv STABLE_TVIEW.
              i. hexploit (REL loc0); ss. i.
              hexploit Stable.future_stable_view; try exact H2; try exact FUTURE; try eapply WF1_RA. i.
              eapply H3.
            }
            { i. exploit VIEWS; eauto. i. des.
              inv STEP_SRC0. ss. eauto.
            }
            i. exploit PROMISE0; eauto. i. des.
            eapply joined_opt_view_stable_view; eauto.
        }

        hexploit APFtoRASim.sim_memory_stable_tview; try eapply SIM1. s. i.
        hexploit APFtoRASim.sim_memory_stable_memory; try eapply SIM1. s. i.
        hexploit Normal.promise_step; try exact STEP_SRC; try eapply SIM1.
        { i. subst. exploit MSG; eauto. i. des. ss. }
        i. des.
        hexploit Normal.promise_step; try exact STEP_SRC0; try eapply SIM1.
        { i. subst. exploit MSG; eauto. i. des. ss. }
        i. des.
        hexploit Stable.promise_step; try exact STEP_SRC0; try eapply SIM1; eauto.
        { i. subst. exploit MSG; eauto. i. des. ss. }
        i. des.
        exploit Local.promise_step_future; try exact STEP_SRC0; eauto. s. i. des.
        unfold Writes.append. ss.
        inv SIM1. inv SIM_APF. inv SIM_RA. ss. subst.
        econs; eauto; ss.
        - econs; eauto. ss.
          eapply Stable.future_stable_view; try exact FUTURE; ss.
          apply STABLE_RA.
        - hexploit future_closed_views; try eapply SIM1; eauto. i.
          eapply step_closed_views; try eapply SIM1; eauto.
          inv WF2. inv TVIEW_CLOSED. apply REL.
        - eapply step_normal_views; try eapply SIM1; eauto.
          + inv NORMAL_TVIEW0. i. eapply (REL loc0).
          + i. exploit VIEWS; eauto. i. des. eauto.
        - hexploit future_stable_views; try eapply SIM1; eauto. i.
          eapply step_stable_views; try eapply SIM1; eauto.
          + inv STABLE_TVIEW2. i. eapply (REL loc0); eauto.
          + i. exploit VIEWS; eauto. i. des. eauto.
      }
    Qed.

    Lemma sim_event_ra_writes_append
          e_apf e_ra
          (SIM: APFtoRASim.sim_event e_ra e_apf):
      forall rels, Writes.append L e_apf rels = Writes.append L e_ra rels.
    Proof.
      inv SIM; ss.
    Qed.

    Lemma sim_thread_step
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          pf e_pf e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: Thread.step pf e_pf e1_pf e2_pf)
          (PF: PF.pf_event L e_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      (exists views2 rels2 pf_j e_j e2_j e_apf e2_apf e_ra e2_ra,
          (<<STEP_J: JThread.step pf_j e_j e1_j e2_j views1 views2>>) /\
          (<<STEP_APF: WThread.step L Ordering.na Ordering.plain rels1 rels2 e_apf e1_apf e2_apf>>) /\
          (<<STEP_RA: WThread.step L Ordering.acqrel Ordering.acqrel rels1 rels2 e_ra e1_ra e2_ra>>) /\
          (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\
          (<<EVENT_APF: PFtoAPFSim.sim_event e_apf e_j>>) /\
          (<<EVENT_RA: APFtoRASim.sim_event e_ra e_apf>>) /\
          (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_apf e2_ra>>)) \/
      (exists e st2,
          (<<CONS: Local.promise_consistent (Thread.local e1_ra)>>) /\
          (<<STEP: lang.(Language.step) e e1_ra.(Thread.state) st2>>) /\
          (<<RACE: RARaceW.ra_race L rels1 (Local.tview (Thread.local e1_ra)) e>>)).
    Proof.
      exploit sim_thread_step_aux; eauto; try apply WF1_PF; try apply WF1_J; try apply WF1_APF; try apply WF1_RA.
      i. des.
      { left. esplits; eauto.
        - erewrite <- sim_event_ra_writes_append; eauto.
          econs. eauto.
        - econs. eauto.
      }
      right.
      inv SIM1. inv SIM_JOINED.
      apply inj_pair2 in H2, H3. subst.
      destruct e1_apf, e1_ra.
      inv SIM_APF. inv SIM_RA. ss. subst.
      inv STEP.
      { inv STEP0. unfold RARaceW.ra_race in *. des; ss. }
      inv STEP0. esplits; eauto.
    Qed.

    Lemma sim_thread_opt_step
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          e_pf e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: Thread.opt_step e_pf e1_pf e2_pf)
          (PF: PF.pf_event L e_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      (exists views2 rels2 e_j e2_j e_apf e2_apf e_ra e2_ra,
          (<<STEP_J: JThread.opt_step e_j e1_j e2_j views1 views2>>) /\
          (<<STEP_APF: WThread.opt_step L Ordering.na Ordering.plain rels1 rels2 e_apf e1_apf e2_apf>>) /\
          (<<STEP_RA: WThread.opt_step L Ordering.acqrel Ordering.acqrel rels1 rels2 e_ra e1_ra e2_ra>>) /\
          (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\
          (<<EVENT_APF: PFtoAPFSim.sim_event e_apf e_j>>) /\
          (<<EVENT_RA: APFtoRASim.sim_event e_ra e_apf>>) /\
          (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_apf e2_ra>>)) \/
      (exists e st2,
          (<<CONS: Local.promise_consistent (Thread.local e1_ra)>>) /\
          (<<STEP: lang.(Language.step) e e1_ra.(Thread.state) st2>>) /\
          (<<RACE: RARaceW.ra_race L rels1 (Local.tview (Thread.local e1_ra)) e>>)).
    Proof.
      inv STEP.
      - left. esplits; eauto; try econs 1; econs.
      - exploit sim_thread_step; eauto. i. des.
        + left. esplits; (try by econs 2; eauto); ss.
        + right. eauto.
    Qed.

    Lemma sim_thread_steps
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          tr e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEPS: Trace.steps tr e1_pf e2_pf)
          (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr)
          (PF: List.Forall (compose (PF.pf_event L) snd) tr)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      (exists views2 rels2 e2_j e2_apf e2_ra,
          (<<STEPS_J: JThread.rtc_tau e1_j e2_j views1 views2>>) /\
          (<<STEPS_APF: WThread.tau_steps L Ordering.na Ordering.plain rels1 rels2 e1_apf e2_apf>>) /\
          (<<STEPS_RA: WThread.tau_steps L Ordering.acqrel Ordering.acqrel rels1 rels2 e1_ra e2_ra>>) /\
          (<<SIM2: sim_thread views2 rels2 e2_pf e2_j e2_apf e2_ra>>)) \/
      (exists rels2 e2_ra e st3,
          (<<STEPS_RA: WThread.tau_steps L Ordering.acqrel Ordering.acqrel rels1 rels2 e1_ra e2_ra>>) /\
          (<<CONS_RA: Local.promise_consistent (Thread.local e2_ra)>>) /\
          (<<STEP_RA: lang.(Language.step) e e2_ra.(Thread.state) st3>>) /\
          (<<RACE: RARaceW.ra_race L rels2 (Local.tview (Thread.local e2_ra)) e>>)).
    Proof.
      revert views1 rels1 e1_j e1_apf e1_ra SIM1 WF1_PF WF1_J WF1_APF WF1_RA SILENT PF CONS.
      induction STEPS; i; ss.
      { left. esplits; eauto; econs 1; eauto. }
      subst. exploit sim_thread_step; try exact SIM1; eauto.
      { ii. inv PF. exploit H1; ss; eauto. }
      { exploit Thread.step_future; try exact STEP; try apply WF1_PF. i. des.
        eapply rtc_tau_step_promise_consistent; try eapply Trace.silent_steps_tau_steps; eauto.
        inv SILENT. ss.
      }
      i. des.
      - exploit step_pf_future; eauto. i. des.
        exploit step_j_future; eauto. i. des.
        exploit step_ra_future; try exact WF1_APF; eauto; ss. i. des.
        exploit step_ra_future; try exact WF1_RA; eauto; ss. i. des.
        exploit IHSTEPS; eauto.
        { inv SILENT. ss. }
        { inv PF. ss. }
        i. des.
        + left. esplits; try exact SIM0; eauto.
          * econs 2; [eauto|..]; eauto.
            inv SILENT. ss. inv EVENT_J; ss.
          * econs 2; [eauto|..]; eauto.
            inv SILENT. ss. inv EVENT_J; inv EVENT_APF; ss.
          * econs 2; [eauto|..]; eauto.
            inv SILENT. ss. inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss.
        + right. esplits; eauto.
          econs 2; [eauto|..]; eauto.
          inv SILENT. ss. inv EVENT_J; inv EVENT_APF; inv EVENT_RA; ss.
      - right. esplits; eauto. econs 1.
    Qed.

    Lemma sim_thread_reserve_step
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: Thread.reserve_step e1_pf e2_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      exists e2_j e2_apf e2_ra,
        (<<STEP_J: JThread.reserve_step views1 e1_j e2_j>>) /\
        (<<STEP_APF: Thread.reserve_step e1_apf e2_apf>>) /\
        (<<STEP_RA: Thread.reserve_step e1_ra e2_ra>>) /\
        (<<SIM2: sim_thread views1 rels1 e2_pf e2_j e2_apf e2_ra>>).
    Proof.
      exploit JSim.sim_thread_reserve_step;
        try eapply SIM1; try eapply WF1_PF; try eapply WF1_J; eauto.
      i. des. inv STEP0. inv STEP1.
      exploit PFtoAPFSim.reserve_step;
        try eapply SIM1; try eapply WF1_J; try eapply WF1_APF.
      { econs; eauto. }
      i. des.
      exploit APFtoRASim.reserve_step;
        try eapply SIM1; try eapply WF1_APF; try eapply WF1_RA; eauto.
      i. des.
      esplits; eauto.
      exploit Thread.rtc_reserve_step_future; [econs 2|..];
        try eapply STEP_SRC; try eapply WF1_APF; eauto. i. des.
      exploit Thread.rtc_reserve_step_future; [econs 2|..];
        try eapply STEP_SRC0; try eapply WF1_RA; eauto. i. des.
      hexploit future_closed_views; try eapply SIM1; eauto. i.
      hexploit future_stable_views; try eapply SIM1; eauto. i.
      econs; eauto. apply SIM1.
    Qed.

    Lemma sim_thread_reserve_steps
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: rtc (@Thread.reserve_step _) e1_pf e2_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      exists e2_j e2_apf e2_ra,
        (<<STEP_J: rtc (@JThread.reserve_step views1 _) e1_j e2_j>>) /\
        (<<STEP_APF: rtc (@Thread.reserve_step _) e1_apf e2_apf>>) /\
        (<<STEP_RA: rtc (@Thread.reserve_step _) e1_ra e2_ra>>) /\
        (<<SIM2: sim_thread views1 rels1 e2_pf e2_j e2_apf e2_ra>>).
    Proof.
      revert e1_j e1_apf e1_ra SIM1 WF1_PF WF1_J WF1_APF WF1_RA.
      induction STEP; i; [esplits; eauto|].
      exploit sim_thread_reserve_step; eauto.
      { eapply rtc_reserve_step_promise_consistent; eauto. }
      i. des.
      exploit reserve_step_pf_future; eauto. i.
      exploit reserve_step_j_future; eauto. i.
      exploit reserve_step_ra_future; try exact STEP_APF; eauto. i.
      exploit reserve_step_ra_future; try exact STEP_RA; eauto. i.
      exploit IHSTEP; eauto. i. des.
      esplits.
      - econs 2; eauto.
      - econs 2; eauto.
      - econs 2; eauto.
      - ss.
    Qed.

    Lemma sim_thread_cancel_step
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: Thread.cancel_step e1_pf e2_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      exists e2_j e2_apf e2_ra,
        (<<STEP_J: JThread.cancel_step views1 e1_j e2_j>>) /\
        (<<STEP_APF: Thread.cancel_step e1_apf e2_apf>>) /\
        (<<STEP_RA: Thread.cancel_step e1_ra e2_ra>>) /\
        (<<SIM2: sim_thread views1 rels1 e2_pf e2_j e2_apf e2_ra>>).
    Proof.
      exploit JSim.sim_thread_cancel_step;
        try eapply SIM1; try eapply WF1_PF; try eapply WF1_J; eauto.
      i. des. inv STEP0. inv STEP1.
      exploit PFtoAPFSim.cancel_step;
        try eapply SIM1; try eapply WF1_J; try eapply WF1_APF.
      { econs; eauto. }
      i. des.
      exploit APFtoRASim.cancel_step;
        try eapply SIM1; try eapply WF1_APF; try eapply WF1_RA; eauto.
      i. des.
      esplits; eauto.
      exploit Thread.rtc_cancel_step_future; [econs 2|..];
        try eapply STEP_SRC; try eapply WF1_APF; eauto. i. des.
      exploit Thread.rtc_cancel_step_future; [econs 2|..];
        try eapply STEP_SRC0; try eapply WF1_RA; eauto. i. des.
      hexploit future_closed_views; try eapply SIM1; eauto. i.
      hexploit future_stable_views; try eapply SIM1; eauto. i.
      econs; eauto. apply SIM1.
    Qed.

    Lemma sim_thread_cancel_steps
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (STEP: rtc (@Thread.cancel_step _) e1_pf e2_pf)
          (CONS: Local.promise_consistent (Thread.local e2_pf)):
      exists e2_j e2_apf e2_ra,
        (<<STEP_J: rtc (@JThread.cancel_step views1 _) e1_j e2_j>>) /\
        (<<STEP_APF: rtc (@Thread.cancel_step _) e1_apf e2_apf>>) /\
        (<<STEP_RA: rtc (@Thread.cancel_step _) e1_ra e2_ra>>) /\
        (<<SIM2: sim_thread views1 rels1 e2_pf e2_j e2_apf e2_ra>>).
    Proof.
      revert e1_j e1_apf e1_ra SIM1 WF1_PF WF1_J WF1_APF WF1_RA.
      induction STEP; i; [esplits; eauto|].
      exploit sim_thread_cancel_step; eauto.
      { eapply rtc_cancel_step_promise_consistent; eauto. }
      i. des.
      exploit cancel_step_pf_future; eauto. i.
      exploit cancel_step_j_future; eauto. i.
      exploit cancel_step_ra_future; try exact STEP_APF; eauto. i.
      exploit cancel_step_ra_future; try exact STEP_RA; eauto. i.
      exploit IHSTEP; eauto. i. des.
      esplits.
      - econs 2; eauto.
      - econs 2; eauto.
      - econs 2; eauto.
      - ss.
    Qed.


    (* consistency *)

    Lemma cap_wf_pf
          e mem
          (WF: wf_pf e)
          (CAP: Memory.cap (Thread.memory e) mem):
      wf_pf (Thread.mk lang (Thread.state e) (Thread.local e) (Thread.sc e) mem).
    Proof.
      inv WF.
      exploit Local.cap_wf; eauto. i.
      exploit Memory.cap_closed; eauto. i.
      hexploit Memory.cap_closed_timemap; eauto.
    Qed.

    Lemma cap_wf_j
          views e mem
          (WF: wf_j views e)
          (CAP: Memory.cap (Thread.memory e) mem):
      wf_j views (Thread.mk lang (Thread.state e) (Thread.local e) (Thread.sc e) mem).
    Proof.
      inv WF.
      exploit Local.cap_wf; eauto. i.
      exploit Memory.cap_closed; eauto. i.
      hexploit Memory.cap_closed_timemap; eauto.
      exploit JSim.joined_memory_cap; eauto.
    Qed.

    Lemma cap_wf_ra
          rels e mem
          (WF: wf_ra rels e)
          (CAP: Memory.cap (Thread.memory e) mem):
      wf_ra rels (Thread.mk lang (Thread.state e) (Thread.local e) (Thread.sc e) mem).
    Proof.
      inv WF.
      exploit Local.cap_wf; eauto. i.
      exploit Memory.cap_closed; eauto. i.
      hexploit Memory.cap_closed_timemap; eauto. i.
      econs; ss.
      eapply Writes.cap_wf; try exact CAP; eauto.
    Qed.

    Lemma sim_thread_cap
          views rels e_pf e_j e_apf e_ra
          mem_pf mem_j mem_apf mem_ra
          (SIM: sim_thread views rels e_pf e_j e_apf e_ra)
          (WF_PF: wf_pf e_pf)
          (WF_J: wf_j views e_j)
          (WF_APF: wf_ra rels e_apf)
          (WF_RA: wf_ra rels e_ra)
          (CAP_PF: Memory.cap (Thread.memory e_pf) mem_pf)
          (CAP_J: Memory.cap (Thread.memory e_j) mem_j)
          (CAP_APF: Memory.cap (Thread.memory e_apf) mem_apf)
          (CAP_RA: Memory.cap (Thread.memory e_ra) mem_ra):
      (<<SIM_CAP: sim_thread views rels
                             (Thread.mk lang (Thread.state e_pf) (Thread.local e_pf) (Thread.sc e_pf) mem_pf)
                             (Thread.mk lang (Thread.state e_j) (Thread.local e_j) (Thread.sc e_j) mem_j)
                             (Thread.mk lang (Thread.state e_apf) (Thread.local e_apf) (Thread.sc e_apf) mem_apf)
                             (Thread.mk lang (Thread.state e_ra) (Thread.local e_ra) (Thread.sc e_ra) mem_ra)>>) /\
      (<<WF_PF_CAP: wf_pf (Thread.mk lang (Thread.state e_pf) (Thread.local e_pf) (Thread.sc e_pf) mem_pf)>>) /\
      (<<WF_J_CAP: wf_j views (Thread.mk lang (Thread.state e_j) (Thread.local e_j) (Thread.sc e_j) mem_j)>>) /\
      (<<WF_APF_CAP: wf_ra rels (Thread.mk lang (Thread.state e_apf) (Thread.local e_apf) (Thread.sc e_apf) mem_apf)>>) /\
      (<<WF_RA_CAP: wf_ra rels (Thread.mk lang (Thread.state e_ra) (Thread.local e_ra) (Thread.sc e_ra) mem_ra)>>).
    Proof.
      exploit cap_wf_pf; eauto. i.
      exploit cap_wf_j; eauto. i.
      exploit cap_wf_ra; try exact WF_APF; eauto. i.
      exploit cap_wf_ra; try exact WF_RA; eauto. i.
      splits; ss.
      inv SIM. econs; ss.
      - inv WF_PF. inv WF_J. inv x0. inv x1. inv SIM_JOINED.
        apply inj_pair2 in H2. apply inj_pair2 in H3. subst. ss.
        econs; eauto.
        eapply SimMemory.sim_memory_cap; eauto.
      - inv SIM_APF. econs; ss.
        eapply PFtoAPFSim.sim_memory_cap; eauto; try apply WF_J; try apply WF_APF.
      - inv SIM_RA. econs; ss.
        eapply APFtoRASim.sim_memory_cap; eauto; try apply WF_APF; try apply WF_RA.
      - inv NORMAL_APF. econs; ss.
        eapply Stable.cap_normal_memory; eauto. apply WF_APF.
      - inv NORMAL_RA. econs; ss.
        eapply Stable.cap_normal_memory; eauto. apply WF_RA.
      - inv WF_RA. inv STABLE_RA. econs; ss.
        + eapply Stable.cap_stable_tview; eauto.
        + eapply Stable.cap_stable_timemap; eauto.
        + eapply Stable.cap_stable_memory; eauto.
      - ii. eapply Memory.cap_closed_view; eauto.
      - ii. exploit Memory.cap_inv; try exact CAP_RA; eauto; try apply WF_RA. i. des; ss.
        exploit STABLE_VIEWS; eauto.
    Qed.

    Lemma local_map_promise_consistent
          lc1 lc2
          (LOCAL: local_map ident_map lc1 lc2)
          (CONS: Local.promise_consistent lc1):
      Local.promise_consistent lc2.
    Proof.
      destruct lc1, lc2. ss. inv LOCAL. ss.
      eapply promise_consistent_mon.
      { eapply promise_consistent_map; eauto.
        - apply ident_map_le.
        - apply ident_map_eq. }
      { eauto. }
      { refl. }
    Qed.

    Lemma local_map_ra_race
          lc1 lc2 rels e
          (LOCAL: local_map ident_map lc1 lc2)
          (RARACE: RARaceW.ra_race L rels (Local.tview lc1) e):
      RARaceW.ra_race L rels (Local.tview lc2) e.
    Proof.
      destruct lc1, lc2. ss. inv LOCAL. ss.
      unfold RARaceW.ra_race, RARaceW.wr_race, RARaceW.ww_race in *. des.
      - left. esplits; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
        inv TVIEW. inv map_cur. rewrite map_rlx. apply TVIEWLE.
      - left. esplits; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
        inv TVIEW. inv map_cur. rewrite map_rlx. apply TVIEWLE.
      - right. esplits; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
        inv TVIEW. inv map_cur. rewrite map_rlx. apply TVIEWLE.
      - right. esplits; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
        inv TVIEW. inv map_cur. rewrite map_rlx. apply TVIEWLE.
    Qed.

    Lemma sim_thread_consistent
          views1 rels1 e1_pf e1_j e1_apf e1_ra
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_apf e1_ra)
          (WF1_PF: wf_pf e1_pf)
          (WF1_J: wf_j views1 e1_j)
          (WF1_APF: wf_ra rels1 e1_apf)
          (WF1_RA: wf_ra rels1 e1_ra)
          (CONSISTENT: PF.pf_consistent L e1_pf):
      (<<CONSISTENT_J: JThread.consistent e1_j views1>>) /\
      (<<CONSISTENT_APF: OrdThread.consistent L Ordering.na Ordering.plain e1_apf>>) /\
      (<<CONSISTENT_RA: OrdThread.consistent L Ordering.acqrel Ordering.acqrel e1_ra>>) \/
      (exists rels2 e2_ra e st3,
          (<<STEPS_RA: WThread.tau_steps L Ordering.acqrel Ordering.acqrel rels1 rels2 e1_ra e2_ra>>) /\
          (<<CONS: Local.promise_consistent (Thread.local e2_ra)>>) /\
          (<<STEP_RA: lang.(Language.step) e e2_ra.(Thread.state) st3>>) /\
          (<<RACE: RARaceW.ra_race L rels2 (Local.tview (Thread.local e2_ra)) e>>)).
    Proof.
      hexploit JSim.sim_thread_consistent;
        try eapply SIM1; try eapply WF1_PF; try eapply WF1_J.
      { inv CONSISTENT. des.
        eapply Trace.consistent_thread_consistent; eauto.
      }
      intro CONSISTENT_J.
      exploit Memory.cap_exists; try apply WF1_PF. i. des.
      exploit Memory.cap_exists; try apply WF1_J. i. des.
      exploit Memory.cap_exists; try apply WF1_APF. i. des.
      exploit Memory.cap_exists; try apply WF1_RA. i. des.
      exploit Memory.cap_closed; try eapply WF1_PF; eauto. i.
      exploit Memory.cap_closed; try eapply WF1_J; eauto. i.
      exploit Memory.cap_closed; try eapply WF1_APF; eauto. i.
      exploit Memory.cap_closed; try eapply WF1_RA; eauto. i.
      exploit sim_thread_cap; eauto. i. des.
      inv CONSISTENT. des. exploit CONSISTENT; eauto. i. des.
      { (* failure *)
        exploit sim_thread_steps; try exact STEPS; eauto.
        { inv FAILURE; inv STEP; ss. inv LOCAL; ss; inv LOCAL0; ss. }
        i. des.
        - exploit steps_pf_future; try exact STEPS; eauto. i. des.
          exploit steps_j_future; try exact STEPS_J; eauto. i. des.
          exploit steps_ra_future; try eapply WThread.tau_steps_steps;
            try exact STEPS_APF; eauto. i. des.
          exploit steps_ra_future; try eapply WThread.tau_steps_steps;
            try exact STEPS_RA; eauto. i. des.
          exploit sim_thread_step; try exact FAILURE; eauto.
          { inv FAILURE; inv STEP; ss. inv LOCAL; ss; inv LOCAL0; ss. }
          { inv FAILURE; inv STEP; ss. inv LOCAL; ss; inv LOCAL0; ss. }
          i. des.
          + left. splits; ss.
            * ii. left.
              exploit Memory.cap_inj; [exact CAP1|exact CAP3|..]; try apply WF1_APF. i. subst.
              exploit WThread.tau_steps_ord_tau_steps; try exact STEPS_APF. i.
              inv STEP_APF. destruct pf; cycle 1.
              { inv STEP. inv STEP0. inv EVENT_APF; inv EVENT_J; ss. }
              unfold OrdThread.steps_failure. esplits; eauto.
              inv EVENT_APF; inv EVENT_J; ss.
            * ii. left.
              exploit Memory.cap_inj; [exact CAP2|exact CAP3|..]; try apply WF1_RA. i. subst.
              exploit WThread.tau_steps_ord_tau_steps; try exact STEPS_RA. i.
              inv STEP_RA. destruct pf; cycle 1.
              { inv STEP. inv STEP0. inv EVENT_RA; inv EVENT_APF; inv EVENT_J; ss. }
              unfold OrdThread.steps_failure. esplits; eauto.
              inv EVENT_RA; inv EVENT_APF; inv EVENT_J; ss.
          + right.
            exploit WThread.cap_tau_steps_current_tau_steps;
              try exact STEPS_RA; eauto; try apply WF1_RA. i. des.
            inv THREAD. ss.
            hexploit local_map_promise_consistent; try eapply LOCAL; eauto. i.
            esplits; eauto. s.
            eapply local_map_ra_race; eauto.
        - right.
          exploit WThread.cap_tau_steps_current_tau_steps;
            try exact STEPS_RA; eauto; try apply WF1_RA. i. des.
          inv THREAD. ss.
          hexploit local_map_promise_consistent; try eapply LOCAL; eauto. i.
          esplits; eauto. s.
          eapply local_map_ra_race; eauto.
      }
      { exploit sim_thread_steps; try exact STEPS; eauto.
        { ii. rewrite PROMISES in *. rewrite Memory.bot_get in *. ss. }
        i. des.
        - left. splits; ss.
          + ii. right.
            exploit Memory.cap_inj; [exact CAP1|exact CAP3|..]; try apply WF1_APF. i. subst.
            exploit WThread.tau_steps_ord_tau_steps; try exact STEPS_APF. i.
            esplits; eauto.
            inv SIM2. inv SIM_APF. rewrite LOCAL.
            inv SIM_JOINED.
            apply inj_pair2 in H2. apply inj_pair2 in H3. subst. ss.
            exploit JSim.sim_local_memory_bot; eauto.
          + ii. right.
            exploit Memory.cap_inj; [exact CAP2|exact CAP3|..]; try apply WF1_RA. i. subst.
            exploit WThread.tau_steps_ord_tau_steps; try exact STEPS_RA. i.
            esplits; eauto.
            inv SIM2. inv SIM_RA. inv LOCAL. rewrite PROMISES0.
            inv SIM_APF. rewrite LOCAL.
            inv SIM_JOINED.
            apply inj_pair2 in H2. apply inj_pair2 in H3. subst. ss.
            exploit JSim.sim_local_memory_bot; eauto.
        - right.
          exploit WThread.cap_tau_steps_current_tau_steps;
            try exact STEPS_RA; eauto; try apply WF1_RA. i. des.
          inv THREAD. ss.
          hexploit local_map_promise_consistent; try eapply LOCAL; eauto. i.
          esplits; eauto. s.
          eapply local_map_ra_race; eauto.
      }
    Qed.
  End PFtoRAThread.
End PFtoRAThread.
