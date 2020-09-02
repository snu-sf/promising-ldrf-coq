Require Import Omega.
Require Import Bool.
Require Import RelationClasses.
Require Import Program.

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
Require Import Behavior.

Require Import Single.
Require Import JoinedView.

Require Import LocalPFView.

Require Import OrdStep.
Require Import Stable.
Require Import RAStep.
Require Import PFtoRASimThread.
Require Import PFtoRA.

Set Implicit Arguments.


Section LocalDRFRA.
  Variable L: Loc.t -> bool.

  Definition ra_racefree (c: Configuration.t): Prop :=
    forall c1 c2 c3
      tid_w e_w loc from to val released ordw
      tid_r lang st3 lc3 e4 e5
      pf e_r released' ordr
      (STEPS1: rtc (@OrdConfiguration.all_step L Ordering.acqrel) c c1)
      (WRITE_STEP: OrdConfiguration.step L Ordering.acqrel e_w tid_w c1 c2)
      (WRITE_EVENT: ThreadEvent.is_writing e_w = Some (loc, from, to, val, released, ordw))
      (STEPS2: rtc (@OrdConfiguration.all_step L Ordering.acqrel) c2 c3)
      (FIND: IdentMap.find tid_r c3.(Configuration.threads) = Some (existT _ lang st3, lc3))
      (THREAD_STEPS: rtc (@OrdThread.all_step _ L Ordering.acqrel)
                         (Thread.mk _ st3 lc3 c3.(Configuration.sc) c3.(Configuration.memory))
                         e4)
      (CONS: Local.promise_consistent e4.(Thread.local))
      (READ_STEP: OrdThread.step L Ordering.acqrel pf e_r e4 e5)
      (READ_EVENT: ThreadEvent.is_reading e_r = Some (loc, to, val, released', ordr))
      (LOC: L loc)
      (HIGHER: Time.lt (e4.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) to)
      (ORDERING: Ordering.le ordw Ordering.strong_relaxed \/
                 Ordering.le ordr Ordering.strong_relaxed),
      False.

  Definition ra_racefree_syn (s: Threads.syntax): Prop :=
    ra_racefree (Configuration.init s).


  Lemma read_message_exists
        lang
        rels1 rels2 rels3 e1 e2 e3
        e loc to val released ord
        (PROMISES: RAThread.reserve_only L e1.(Thread.local).(Local.promises))
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (MEM1: Memory.closed e1.(Thread.memory))
        (STEPS: @RAThread.steps lang L rels1 rels2 e1 e2)
        (STEP: RAThread.step L rels2 rels3 e e2 e3)
        (EVENT: ThreadEvent.is_reading e = Some (loc, to, val, released, ord))
        (LOC: L loc)
        (HIGHER: Time.lt (e2.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) to):
    exists from,
      (<<GET: Memory.get loc to e1.(Thread.memory) = Some (from, Message.concrete val released)>>) /\
      (<<RELS: List.In (loc, to) rels1 <-> List.In (loc, to) rels2>>).
  Proof.
    assert (GET: exists from,
               Memory.get loc to e2.(Thread.memory) = Some (from, Message.concrete val released)).
    { destruct e; inv EVENT; inv STEP; inv STEP0; inv STEP; inv LOCAL.
      - inv LOCAL0. inv STEP. eauto.
      - inv LOCAL1. inv STEP. eauto. }
    des. clear rels3 e3 e STEP EVENT. exists from.
    dependent induction STEPS; try by (esplits; eauto).
    hexploit RAThread.step_reserve_only; try exact STEP; eauto. i. des.
    exploit RAThread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    clear IHSTEPS.
    inv STEP. inv STEP0; inv STEP; [|inv LOCAL]; ss; try by (esplits; eauto).
    - splits; ss.
      revert GET0. inv LOCAL. inv PROMISE.
      + erewrite Memory.add_o; eauto. condtac; ss.
        i. des. inv GET0. exploit PF; eauto. ss.
      + erewrite Memory.split_o; eauto. repeat condtac; ss.
        * i. des. inv GET0. inv H2. exploit PF; eauto. ss.
        * guardH o. i. des. inv GET0. inv H2.
          exploit Memory.split_get0; try exact PROMISES0. i. des.
          exploit H; try exact GET3; eauto. ss.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        i. des. inv GET0. exploit PF; eauto. ss.
      + erewrite Memory.remove_o; eauto. condtac; ss.
    - destruct (classic ((loc, to) = (loc0, to0))).
      { exfalso. symmetry in H0. inv H0.
        assert (Time.le to (lc2.(Local.tview).(TView.cur).(View.rlx) loc)).
        { inv LOCAL0. inv STEP. ss.
          unfold TimeMap.join, TimeMap.singleton.
          unfold LocFun.add, LocFun.init, LocFun.find. condtac; ss.
          apply Time.join_r. }
        exploit RAThread.steps_future; try exact STEPS; eauto. s. i. des.
        inv TVIEW_FUTURE0. inv CUR. rewrite (RLX loc) in H0.
        timetac.
      }
      revert GET0. inv LOCAL0. inv STEP. inv WRITE. inv PROMISE; ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
        { des. subst. ss. }
        guardH o. i. split; ss.
        unfold ReleaseWrites.append in *. ss. split; i.
        * apply RELS. repeat condtac; ss. right. ss.
        * exploit RELS0; eauto. repeat condtac; ss. i. des; ss.
          inv x. ss.
      + erewrite Memory.split_o; eauto. condtac; ss.
        { des. subst. ss. }
        guardH o. condtac; ss.
        { i. des. inv GET0. inv H3.
          exploit Memory.split_get0; try exact PROMISES0. i. des.
          exploit PROMISES; try exact GET1; ss. }
        guardH o0. i. split; ss.
        unfold ReleaseWrites.append in *. ss. split; i.
        * apply RELS. repeat condtac; ss. right. ss.
        * exploit RELS0; eauto. repeat condtac; ss. i. des; ss.
          inv x. ss.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        { des. subst. ss. }
        guardH o. i. split; ss.
        unfold ReleaseWrites.append in *. ss. split; i.
        * apply RELS. repeat condtac; ss. right. ss.
        * exploit RELS0; eauto. repeat condtac; ss. i. des; ss.
          inv x. ss.
    - destruct (classic ((loc, to) = (loc0, tsw))).
      { exfalso. symmetry in H0. inv H0.
        assert (Time.le to (lc2.(Local.tview).(TView.cur).(View.rlx) loc)).
        { inv LOCAL2. inv STEP. ss.
          unfold TimeMap.join, TimeMap.singleton.
          unfold LocFun.add, LocFun.init, LocFun.find. condtac; ss.
          apply Time.join_r. }
        exploit RAThread.steps_future; try exact STEPS; eauto. s. i. des.
        inv TVIEW_FUTURE0. inv CUR. rewrite (RLX loc) in H0.
        timetac.
      }
      revert GET0. inv LOCAL1. inv STEP. inv LOCAL2. inv STEP. inv WRITE. inv PROMISE; ss.
      + erewrite Memory.add_o; eauto. condtac; ss.
        { des. subst. ss. }
        guardH o. i. split; ss.
        unfold ReleaseWrites.append in *. ss. split; i.
        * apply RELS. repeat condtac; ss. right. ss.
        * exploit RELS0; eauto. repeat condtac; ss. i. des; ss.
          inv x. ss.
      + erewrite Memory.split_o; eauto. condtac; ss.
        { des. subst. ss. }
        guardH o. condtac; ss.
        { i. des. inv GET1. inv H3.
          exploit Memory.split_get0; try exact PROMISES0. i. des.
          exploit PROMISES; try exact GET2; ss. }
        guardH o0. i. split; ss.
        unfold ReleaseWrites.append in *. ss. split; i.
        * apply RELS. repeat condtac; ss. right. ss.
        * exploit RELS0; eauto. repeat condtac; ss. i. des; ss.
          inv x. ss.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        { des. subst. ss. }
        guardH o. i. split; ss.
        unfold ReleaseWrites.append in *. ss. split; i.
        * apply RELS. repeat condtac; ss. right. ss.
        * exploit RELS0; eauto. repeat condtac; ss. i. des; ss.
          inv x. ss.
  Qed.

  (* Lemma write_exists *)
  (*       rels1 rels2 e1 e2 *)
  (*       loc from to val released *)
  (*       (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory)) *)
  (*       (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory)) *)
  (*       (MEM1: Memory.closed e1.(Thread.memory)) *)
  (*       (STEPS: RAThread.steps rels1 rels2 e1 e2) *)
  (*       (LOC: L loc) *)
  (*       (GET1: Memory.get loc to e2.(Thread.memory) = Some (from,  *)
  (*       (GET2: Memory.get loc to e2.(Thread.memory) = Some (from, Message.concrete val released)): *)

  Lemma racefree_implies
        s
        (RACEFREE: ra_racefree_syn s):
    RARace.racefree_syn L s.
  Proof.
    ii. unfold RARace.ra_race in *. des.
  Admitted.

  Theorem local_drf_ra
          s
          (RACEFREE: ra_racefree_syn s):
    behaviors SConfiguration.machine_step (Configuration.init s) <1=
    behaviors (@OrdConfiguration.machine_step L Ordering.acqrel) (Configuration.init s).
  Proof.
    hexploit racefree_implies; eauto. i.
    specialize (PFtoRA.init_sim_conf L s). intro SIM.
    specialize (PFtoRA.init_wf_pf L s). intro WF_PF.
    specialize (PFtoRA.init_wf_j s). intro WF_J.
    specialize (PFtoRA.init_wf_ra s). intro WF_RA.
    ii. exploit (@local_DRFPF_view L); eauto.
    { eapply PFtoRA.sim_conf_racefree; eauto. }
    eapply PFtoRA.sim_conf_behavior; eauto.
  Qed.
End LocalDRFRA.
