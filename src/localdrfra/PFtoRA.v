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

Require Import PromiseConsistent.
Require Import JoinedView.

Require Import OrdStep.
Require Import RARace.
Require Import Stable.
Require Import PFtoRASimThread.

Set Implicit Arguments.


Module PFtoRA.
  Section PFtoRAThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.


    Definition stable_views (mem: Memory.t) (views: Loc.t -> Time.t -> list View.t): Prop :=
      forall loc to view (IN: List.In view (views loc to)),
        Stable.stable_view L mem view.

    Definition sim_statelocal (views: Loc.t -> Time.t -> list View.t) (rels: ReleaseWrites.t)
               (sl_pf sl_j sl_ra: {lang: language & Language.state lang} * Local.t): Prop :=
      JSim.sim_statelocal views sl_j sl_pf /\
      PFtoRASimThread.sim_statelocal L rels sl_ra sl_j.

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
          admit.
        - esplits; eauto. right. esplits; eauto.
          hexploit step_promise_consistent; try exact STEP_PF; try apply SIM1; eauto. i.
          inv SIM1. inv SIM_JOINED. inv SIM_RA.
          apply inj_pair2 in H4. subst.
          apply inj_pair2 in H5. subst. ss.
          hexploit JSim.sim_local_promise_consistent; try exact LOCAL; eauto. i. des.
          eapply PFtoRASimThread.sim_local_promise_consistent; eauto.
      }

      (* promise on ~ L *)
      admit.
    Admitted.
  End PFtoRAThread.

  Section PFtoRA.
    Variable L: Loc.t -> bool.
  End PFtoRA.
End PFtoRA.
