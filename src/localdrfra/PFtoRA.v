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
Require Import JoinedView.

Require Import LocalDRF_PF.
Require Import OrdStep.
Require Import RARace.
Require Import Stable.
Require Import PFtoRASimThread.

Set Implicit Arguments.


Module PFtoRA.
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


    Inductive sim_thread (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t)
              (e_pf e_j e_ra: Thread.t lang): Prop :=
    | sim_thread_intro
        (SIM_JOINED: JSim.sim_thread views e_j e_pf)
        (JOINED_REL: joined_released views e_j.(Thread.local).(Local.promises) e_j.(Thread.local).(Local.tview).(TView.rel))
        (JOINED_MEM: joined_memory views e_j.(Thread.memory))
        (JOINED_VIEWS: wf_views views)

        (SIM_RA: PFtoRASimThread.sim_thread L rels e_ra e_j)
        (NORMAL_J: PFtoRASimThread.normal_thread L e_j)
        (NORMAL_RA: PFtoRASimThread.normal_thread L e_ra)
        (STABLE_RA: PFtoRASimThread.stable_thread L rels e_ra)
        (CLOSED_VIEWS: closed_views views e_ra.(Thread.memory))
        (NORMAL_VIEWS: normal_views views)
        (STABLE_VIEWS: stable_views e_ra.(Thread.memory) views)

        (WF_PF: Local.wf e_pf.(Thread.local) e_pf.(Thread.memory))
        (SC_PF: Memory.closed_timemap e_pf.(Thread.sc) e_pf.(Thread.memory))
        (MEM_PF: Memory.closed e_pf.(Thread.memory))
        (WF_J: Local.wf e_j.(Thread.local) e_j.(Thread.memory))
        (SC_J: Memory.closed_timemap e_j.(Thread.sc) e_j.(Thread.memory))
        (MEM_J: Memory.closed e_j.(Thread.memory))
        (WF_RA: Local.wf e_ra.(Thread.local) e_ra.(Thread.memory))
        (SC_RA: Memory.closed_timemap e_ra.(Thread.sc) e_ra.(Thread.memory))
        (MEM_RA: Memory.closed e_ra.(Thread.memory))
    .

    Lemma thread_step
          views1 rels1 e1_pf e1_j e1_ra
          pf e_pf e2_pf
          (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_ra)
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
        __guard__ (
          (<<SIM2: sim_thread views2 (ReleaseWrites.append L e_ra rels1) e2_pf e2_j e2_ra>>) /\
          (<<EVENT: PFtoRASimThread.sim_event e_ra e_j>>) \/
          (<<CONS: Local.promise_consistent e1_ra.(Thread.local)>>) /\
          (<<RACE: exists loc to val released ord,
              ThreadEvent.is_reading e_ra = Some (loc, to, val, released, ord) /\
              RARace.ra_race L rels1 e1_ra.(Thread.local).(Local.tview) loc to ord>>)).
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
          exploit Thread.step_future; try exact STEP_PF; try apply SIM1. i. des.
          exploit Thread.step_future; try eapply STEP0; try apply SIM1. i. des.
          exploit OrdThread.step_future; try exact STEP_SRC; try apply SIM1. i. des.
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
        - exploit Local.promise_step_future; try exact STEP_SRC; try apply SIM1. s. i. des.
          hexploit future_closed_views; try eapply SIM1; try exact FUTURE. i.
          hexploit future_stable_views; try eapply SIM1; try exact FUTURE. i.
          hexploit (@step_stable_views views1 views0); try exact H1; eauto.
          { inv SIM1. ss. inv STABLE_RA. ss. inv STABLE_TVIEW.
            i. hexploit (REL loc0); ss. i.
            hexploit Stable.future_stable_view; try exact H2; try exact FUTURE; try apply WF_RA. i.
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
      exploit Thread.step_future; try exact STEP_PF; try eapply SIM1. i. des.
      exploit Local.promise_step_future; try exact LOCAL; try eapply SIM1. s. i. des.
      exploit Local.promise_step_future; try exact STEP_SRC; try eapply SIM1. s. i. des.
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

    (* Lemma thread_steps *)
    (*       views1 rels1 e1_pf e1_j e1_ra *)
    (*       tr e_pf e2_pf *)
    (*       (SIM1: sim_thread views1 rels1 e1_pf e1_j e1_ra) *)
    (*       (STEPS: Trace.steps tr e1_pf e2_pf) *)
    (*       (SILENT: List.Forall (fun the => ThreadEvent.get_machine_event (snd the) = MachineEvent.silent) tr) *)
    (*       (VALID: List.Forall (compose (valid_event L) snd) tr) *)
    (*       (CONS: Local.promise_consistent e2_pf.(Thread.local)): *)
    (*   exists views2 e_j pf_j e2_j e_ra e2_ra, *)
    (*     (<<STEP_J: JThread.step pf_j e_j e1_j e2_j views1 views2>>) /\ *)
    (*     (<<EVENT_J: JSim.sim_event e_j e_pf>>) /\ *)
    (*     (<<STEP_RA: OrdThread.step L Ordering.acqrel pf_j e_ra e1_ra e2_ra>>) /\ *)
    (*     __guard__ ( *)
    (*       (<<SIM2: sim_thread views2 (ReleaseWrites.append L e_ra rels1) e2_pf e2_j e2_ra>>) /\ *)
    (*       (<<EVENT: PFtoRASimThread.sim_event e_ra e_j>>) \/ *)
    (*       (<<CONS: Local.promise_consistent e1_ra.(Thread.local)>>) /\ *)
    (*       (<<RACE: exists loc to val released ord, *)
    (*           ThreadEvent.is_reading e_ra = Some (loc, to, val, released, ord) /\ *)
    (*           RARace.ra_race L rels1 e1_ra.(Thread.local).(Local.tview) loc to ord>>)). *)
  End PFtoRAThread.


  Section PFtoRA.
    Variable L: Loc.t -> bool.

    Definition option_rel3 {A B C} (P: A -> B -> C -> Prop)
               (a: option A) (b: option B) (c: option C): Prop :=
      match a, b, c with
      | Some x, Some y, Some z => P x y z
      | None, None, None => True
      | _, _, _ => False
      end.

    Inductive sim_thread_sl (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t)
              (sc_pf sc_j sc_ra: TimeMap.t) (mem_pf mem_j mem_ra: Memory.t):
      forall (sl_pf sl_j sl_ra: {lang: language & Language.state lang} * Local.t), Prop :=
    | sim_thread_sl_intro
        lang st_pf lc_pf st_j lc_j st_ra lc_ra
        (SIM: sim_thread L views rels
                         (Thread.mk lang st_pf lc_pf sc_pf mem_pf)
                         (Thread.mk lang st_j lc_j sc_j mem_j)
                         (Thread.mk lang st_ra lc_ra sc_ra mem_ra)):
        sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra
                      (existT _ lang st_pf, lc_pf) (existT _ lang st_j, lc_j) (existT _ lang st_ra, lc_ra)
    .

    (* Lemma future_sim_thread_sl *)
    (*       lang st_pf st_j st_ra lc_pf lc_j lc_ra *)
    (*       views1 rels1 sc1_pf sc1_j sc1_ra mem1_pf mem1_j mem1_ra *)
    (*       views2 rels2 sc2_pf sc2_j sc2_ra mem2_pf mem2_j mem2_ra *)
    (*       (SIM1: sim_thread_sl views1 rels1 sc1_pf sc1_j sc1_ra mem1_pf mem1_j mem1_ra *)
    (*                            (existT _ lang st_pf, lc_pf) (existT _ lang st_j, lc_j) (existT _ lang st_ra, lc_ra)) *)
    (*       (SC_PF_FUTURE: TimeMap.le sc1_pf sc2_pf) *)
    (*       (SC_J_FUTURE: TimeMap.le sc1_j sc2_j) *)
    (*       (SC_RA_FUTURE: TimeMap.le sc1_ra sc2_ra) *)
    (*       (MEM_PF_FUTURE: Memory.future mem1_pf mem2_pf) *)
    (*       (MEM_J_FUTURE: Memory.future mem1_j mem2_j) *)
    (*       (MEM_RA_FUTURE: Memory.future mem1_ra mem2_ra) *)
    (*       (WF2_PF: Local.wf lc_pf mem2_pf) *)
    (*       (WF2_J: Local.wf lc_j mem2_j) *)
    (*       (WF2_RA: Local.wf lc_ra mem2_ra) *)
    (*       (SC2_PF: Memory.closed_timemap sc2_pf mem2_pf) *)
    (*       (SC2_J: Memory.closed_timemap sc2_j mem2_j) *)
    (*       (SC2_RA: Memory.closed_timemap sc2_ra mem2_ra) *)
    (*       (MEM2_PF: Memory.closed mem2_pf) *)
    (*       (MEM2_J: Memory.closed mem2_j) *)
    (*       (MEM2_RA: Memory.closed mem2_ra) *)
    (*       (SC2_PF_STABLE: Stable.stable_timemap L mem2_pf sc2_pf) *)
    (*       (SC2_PF_STABLE: Stable.stable_timemap L mem2_pf sc2_pf) *)
    (*       (SC2_PF_STABLE: Stable.stable_timemap L mem2_pf sc2_pf) *)

    Inductive sim_conf (rels: ReleaseWrites.t): forall (c_pf c_ra: Configuration.t), Prop :=
    | sim_conf_intro
        views
        ths_pf sc_pf mem_pf
        ths_j sc_j mem_j
        ths_ra sc_ra mem_ra
        (THS: forall tid,
            option_rel3
              (sim_thread_sl views rels sc_pf sc_j sc_ra mem_pf mem_j mem_ra)
              (IdentMap.find tid ths_pf)
              (IdentMap.find tid ths_j)
              (IdentMap.find tid ths_ra)):
        sim_conf rels
                 (Configuration.mk ths_pf sc_pf mem_pf)
                 (Configuration.mk ths_ra sc_ra mem_ra)
    .

    (* Lemma sim_conf_steps *)
    (*       views1 rels2 c1_pf c1_j c1_ra *)
    (*       c2_pf trs *)
    (*       (SIM: sim_conf views rels c1_pf c1_j c1_ra) *)
    (*       (WF1_PF: Configuration.wf c1_pf) *)
    (*       (WF1_J: Configuration.wf c1_j) *)
    (*       (WF1_RA: Configuration.wf c1_ra) *)
    (*       (STEPS_PF: LOCALDRF.configuration_steps_trace c1_pf c2_pf): *)
    (*   exists  *)
  End PFtoRA.
End PFtoRA.
