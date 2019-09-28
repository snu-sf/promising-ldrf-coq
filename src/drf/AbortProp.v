Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.

Require Import DRF_PF.

Require Import PFConsistent.

Set Implicit Arguments.



Inductive added_memory_imm (tm: TimeMap.t): Memory.t -> Memory.t -> Prop :=
| added_memory_imm_intro
    m0 loc to from val m1
    (TLE: Time.le (tm loc) to)
    (ADD: Memory.add m0 loc to from (Message.full val None) m1)
  :
    added_memory_imm tm m0 m1
.

Definition added_memory (tm: TimeMap.t) := rtc (added_memory_imm tm).

Lemma added_memory_future tm m0 m1
      (ADDED: added_memory tm m0 m1)
  :
    Memory.future m0 m1.
Proof.
  ginduction ADDED; auto. etrans; [| apply IHADDED].
  inv H. econs; eauto. econs; eauto.
  econs. ss. eapply Time.bot_spec.
Qed.

Definition is_cancel (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise _ _ _ _ Memory.op_kind_cancel => True
  | _ => False
  end.

Inductive only_reserves (proms: Memory.t): Prop :=
| only_reserves_intro
    (RESERVES: forall loc to from msg (GET: Memory.get loc to proms = Some (from, msg)),
        msg = Message.reserve)
    (FINITE: Memory.finite proms)
.

Lemma reserves_cancelable lang st vw proms sc mem0
      (RESERVES: only_reserves proms)
      (MLE: Memory.le proms mem0)
  :
    exists mem1,
      rtc (tau (@pred_step is_cancel lang))
          (Thread.mk lang st (Local.mk vw proms) sc mem0)
          (Thread.mk lang st (Local.mk vw Memory.bot) sc mem1).
Proof.
  inv RESERVES. unfold Memory.finite in *. des.
  ginduction dom; ss; i.
  - exists mem0. replace proms with Memory.bot; auto.
    eapply Memory.ext. i. rewrite Memory.bot_get.
    destruct (Memory.get loc ts proms) as [[from msg]|] eqn:GET; auto.
    exfalso. eauto.
  - destruct a as [loc' to'].
    destruct (Memory.get loc' to' proms) as [[from' msg']|] eqn:GET.
    + exploit RESERVES0; eauto. i. clarify.
      exploit Memory.remove_exists.
      { eapply GET. }
      intros [prom1 REMOVE0].
      exploit Memory.remove_exists.
      { eapply MLE. eapply GET. }
      intros [mem1 REMOVE1]. hexploit IHdom.
      * instantiate (1:=mem1). instantiate (1:=prom1).
        ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
        eapply MLE in LHS. erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
      * i. erewrite Memory.remove_o in GET0; eauto. des_ifs.
        eapply RESERVES0; eauto.
      * i. erewrite Memory.remove_o in GET0; eauto. des_ifs.
        exploit FINITE; eauto. i. ss.
        des; ss; clarify.
      * i. des. exists mem2. econs 2.
        { econs.
          - instantiate (2:=ThreadEvent.promise loc' from' to' Message.reserve Memory.op_kind_cancel).
            econs; ss. econs. econs 1. econs; ss.
            econs; ss. econs; eauto.
          - ss. }
        eapply H.
    + eapply IHdom; eauto.
      i. exploit FINITE; eauto. i. des; clarify.
Qed.

Inductive concreter_memory (mem_src mem_tgt: Memory.t): Prop :=
| concreter_memory_intro
    (COVER: forall loc to (COV: covered loc to mem_src),
        covered loc to mem_tgt)
    (MSG: forall loc to from vw val
                 (GETTGT: Memory.get loc to mem_tgt = Some (from, Message.full val vw)),
        Memory.get loc to mem_src = Some (from, Message.full val vw))
.

(* Lemma concreter_memory_write mem_src0 mem_tgt0 prom0 *)
(*       loc from to val vw_src vw_tgt prom1 mem_tgt1 kind *)
(*       (CONCRETE: concreter_memory mem_src0 mem_tgt0) *)
(*       (MLESRC: Memory.le prom0 mem_src0) *)
(*       (MLETGT: Memory.le prom0 mem_tgt0) *)
(*       (VWLE: View.opt_le vw_src vw_tgt) *)
(*       (VWWF: View.opt_wf vw_src) *)
(*       (WRITE: Memory.write prom0 mem_tgt0 loc from to val vw_tgt prom1 mem_tgt1 kind) *)
(*   : *)
(*     exists mem_src1, *)
(*       (<<PROMISE: Memory.write prom0 mem_src0 loc from to val vw_src prom1 mem_src1 kind>>) /\ *)
(*       (<<CONCRETE: concreter_memory mem_src1 mem_tgt1>>). *)
(* Proof. *)
(*   inv WRITE. inv PROMISE. *)
(*   - exploit add_succeed_wf; try apply PROMISES. i. des. *)
(*     exploit add_succeed_wf; try apply MEM. i. des. *)

Lemma concreter_memory_step
      lang prom th_src th_tgt th_tgt' st st' vw vw' prom' sc sc'
      mem_src mem_tgt mem_tgt' tf e
      (VWF: TView.wf vw)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk vw prom) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk vw prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk vw' prom') sc' mem_tgt')
      (CONCRETE: concreter_memory mem_src mem_tgt)
      (MLESRC: Memory.le prom mem_src)
      (MLETGT: Memory.le prom mem_tgt)
      (STEP: Thread.step tf e th_tgt th_tgt')
  :
    exists v_src' mem_src' sc_src',
      (<<STEP: Thread.step
                 tf e th_src
                 (Thread.mk lang st' (Local.mk v_src' prom') sc_src' mem_src')>>) /\
      (<<CONCRETE: concreter_memory mem_src' mem_tgt'>>)
.
Proof.
Admitted.

Lemma progressable_in_added_rtc
      lang st lc sc0 sc1 m0 m1 tm
      (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc0 m0))
      (FUTURE: Memory.future m0 m1)
  :
    exists m2 e2,
      (<<ADDED: rtc (added_memory tm) m1 m2>>) /\
      (<<STEPS: rtc (Thread.tau_step (lang:=lang))
                    (Thread.mk _ st lc sc1 m1) e2>>) /\
      (<<PROMISES: Local.promises (Thread.local e2) = Memory.bot>>).
Proof.
Admitted.

Lemma promise_free_no_promise P lang (th0 th1: Thread.t lang) e
      (NOPROMISE: th0.(Thread.local).(Local.promises) = Memory.bot)
      (STEP: pred_step (P /1\ promise_free) e th0 th1)
  :
    (<<STEP: pred_step (P /1\ no_promise) e th0 th1>>) /\
    (<<NOPROMISE: th1.(Thread.local).(Local.promises) = Memory.bot>>).
Proof.
  inv STEP. inv STEP0. inv STEP.
  - inv STEP0. inv LOCAL. inv PROMISE; ss; des; clarify.
    + rewrite NOPROMISE in *.
      eapply Memory.lower_get0 in PROMISES. des.
      erewrite Memory.bot_get in *. clarify.
    + rewrite NOPROMISE in *.
      eapply Memory.remove_get0 in PROMISES. des.
      erewrite Memory.bot_get in *. clarify.
  - inv STEP0. inv LOCAL.
    + ss. esplits; eauto. econs; eauto. econs; eauto.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. ss.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. rewrite NOPROMISE in *.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE. ss.
        symmetry. eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL1. inv LOCAL2. rewrite NOPROMISE in *.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE. ss.
        symmetry. eapply MemoryMerge.MemoryMerge.add_remove; eauto.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. ss.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
      * inv LOCAL0. ss.
    + ss. esplits; eauto.
      * econs; eauto. econs; eauto.
Qed.

Definition pf_consistent_strong lang (e:Thread.t lang): Prop :=
  forall mem1 sc1
         (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1),
  exists e2,
    (<<STEPS: rtc (tau (@pred_step (promise_free /1\ no_sc) lang)) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\
    ((<<FAILURE: Local.failure_step e2.(Thread.local)>>) \/
     (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>)).

(* Definition pf_consistent_strong lang (e:Thread.t lang): Prop := *)
(*   forall mem1 sc1 *)
(*          (WF: Local.wf e.(Thread.local) e.(Thread.memory)) *)
(*          (MEM: Memory.closed e.(Thread.memory)) *)
(*          (CAP: Memory.cap e.(Thread.local).(Local.promises) e.(Thread.memory) mem1), *)
(*   exists e2 e3, *)
(*     (<<STEPS: rtc (tau (@pred_step (no_sc /1\ promise_free) lang)) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\ *)
(*     (<<FAILURE: pred_step (no_sc /1\ promise_free) (ThreadEvent.failure) e2 e3>>) \/ *)
(*     exists e2, *)
(*       (<<STEPS: rtc (tau (@pred_step (no_sc /1\ promise_free) lang)) (Thread.mk _ e.(Thread.state) e.(Thread.local) sc1 mem1) e2>>) /\ *)
(*       (<<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>). *)

Lemma write_promises_decrease prom0 mem0 loc from to val realeased prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to val realeased prom1 mem1 kind)
  :
    concrete_promised prom1 <2= concrete_promised prom0.
Proof.
  inv WRITE. inv PROMISE.
  - exploit MemoryMerge.MemoryMerge.add_remove.
    + eapply PROMISES.
    + eapply REMOVE.
    + i. clarify.
  - ii. inv PR.
    erewrite Memory.remove_o in GET; eauto. des_ifs.
    erewrite Memory.split_o in GET; eauto. des_ifs.
    + ss; des; clarify.
    + ss. des; clarify. eapply Memory.split_get0 in PROMISES.
      des. econs; eauto.
    + eapply Memory.split_get0 in PROMISES.
      guardH o. guardH o0. guardH o1. des. econs; eauto.
  - ii. inv PR.
    erewrite Memory.remove_o in GET; eauto. des_ifs.
    erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss; des; clarify.
    + econs; eauto.
  - clarify.
Qed.

Lemma pf_step_promises_decrease P lang e (th0 th1: Thread.t lang)
      (STEP: (@pred_step (promise_free /1\ P) lang) e th0 th1)
  :
    concrete_promised (th1.(Thread.local).(Local.promises)) <2=
    concrete_promised (th0.(Thread.local).(Local.promises)).
Proof.
  i. inv STEP. inv STEP0. des. inv STEP.
  - inv STEP0. ss. inv LOCAL. ss. inv PROMISE; clarify.
    + inv PR. erewrite Memory.lower_o in GET; eauto. des_ifs.
      * ss; des. clarify. eapply Memory.lower_get0 in PROMISES.
        des. econs; eauto.
      * econs; eauto.
    + inv PR. erewrite Memory.remove_o in GET; eauto. des_ifs.
      econs; eauto.
  - inv STEP0. ss. inv LOCAL; eauto.
    + inv LOCAL0. ss.
    + inv LOCAL0. ss. eapply write_promises_decrease; eauto.
    + inv LOCAL1. inv LOCAL2. ss. eapply write_promises_decrease; eauto.
    + inv LOCAL0. ss.
    + inv LOCAL0. ss.
Qed.

Lemma pf_step_rtc_promises_decrease P lang (th0 th1: Thread.t lang)
      (STEP: rtc (tau (@pred_step (promise_free /1\ P) lang)) th0 th1)
  :
    concrete_promised (th1.(Thread.local).(Local.promises)) <2=
    concrete_promised (th0.(Thread.local).(Local.promises)).
Proof.
  ginduction STEP; ss.
  i. eapply IHSTEP in PR; eauto. inv H.
  eapply pf_step_promises_decrease; eauto.
Qed.

Lemma le_inhabited mem0 mem1
      (INHABITED: Memory.inhabited mem0)
      (MLE: Memory.le mem0 mem1)
  :
    Memory.inhabited mem1.
Proof.
  ii. eapply MLE; eauto.
Qed.

Inductive configuration_step: forall (e:MachineEvent.t) (tid:Ident.t) (c1 c2:Configuration.t), Prop :=
| configuration_step_intro
    pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) e2)
    (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
    (CONSISTENT: forall (EVENT: e <> ThreadEvent.failure),
        Thread.consistent (Thread.mk _ st3 lc3 sc3 memory3))
  :
    configuration_step (ThreadEvent.get_machine_event e) tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(Configuration.threads)) sc3 memory3)
.

Lemma configuration_step_equivalent e tid c1 c2
  :
    Configuration.step e tid c1 c2 <-> configuration_step e tid c1 c2.
Proof.
  split.
  - i. inv H.
    + replace MachineEvent.failure with (ThreadEvent.get_machine_event ThreadEvent.failure); auto.
      econs; eauto. i. clarify.
    + econs; eauto.
  - i. inv H. destruct (classic (e0 = ThreadEvent.failure)).
    + clarify. econs 1; eauto.
    + econs 2; eauto.
Qed.

Lemma no_sc_any_sc_rtc
      P lang th_src th_tgt th_tgt' st st' lc lc' sc sc_src sc'
      mem mem'
      (STEP: rtc (tau (@pred_step (P /1\ no_sc) lang)) th_tgt th_tgt')
      (TH_SRC: th_src = Thread.mk lang st lc sc_src mem)
      (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem)
      (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem')
  :
    exists sc_src',
      (<<STEP: rtc (tau (@pred_step (P /1\ no_sc) lang))
                   th_src
                   (Thread.mk lang st' lc' sc_src' mem')>>).
Proof.
  ginduction STEP.
  - i. clarify. esplits; eauto.
  - i. clarify. destruct y. destruct local, lc, lc'. ss.
    inv H. exploit no_sc_any_sc; eauto. i. des.
    exploit IHSTEP; eauto. i. des.
    exists sc_src'0. esplits. econs; eauto.
Qed.

Lemma max_full_timemap_get mem tm loc to from val released
      (MAX: Memory.max_full_timemap mem tm)
      (GET: Memory.get loc to mem = Some (from, Message.full val released) )
  :
    Time.le to (tm loc).
Proof.
  specialize (MAX loc). inv MAX. eapply MAX0; eauto.
Qed.

Lemma pf_consistent_pf_consistent_strong lang (th: Thread.t lang)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory))
      (INHABITED: Memory.inhabited th.(Thread.memory))
      (CONSISTENT: pf_consistent th)
  :
    pf_consistent_strong th.
Proof.
  ii. exploit Memory.max_full_timemap_exists.
  { eapply le_inhabited; eauto. eapply Memory.cap_le; eauto. refl. }
  i. des. exploit CONSISTENT; eauto. i.
  destruct x as [e2 [STEPS GOOD]]. guardH GOOD. des.

  - eapply pf_step_promise_free_step_rtc in STEPS.
    eapply hold_or_not with (Q := no_sc) in STEPS. des.
    + destruct th. destruct e2. ss.
      exploit no_sc_any_sc_rtc; eauto. i. des.
      esplits; eauto. unguard. des.
      * left. ss. inv FAILURE; inv STEP0. inv LOCAL. eauto.
      * right. esplits; eauto.

    + exploit Thread.rtc_tau_step_future.
      { eapply thread_steps_pred_steps. eapply STEPS0. }
      { ss. eapply Local.cap_wf; eauto. }
      { ss. eapply Memory.max_full_timemap_closed; eauto. }
      { ss. eapply Memory.cap_closed; eauto. }
      i. des. ss. inv STEP.
      exploit Thread.step_future; eauto.
      i. des.

      hexploit (@rtc_tau_step_promise_consistent _ e3 e2); eauto.
      { eapply thread_steps_pred_steps; eauto. }
      { unguard. des.
        - inv FAILURE; inv STEP. inv LOCAL. inv LOCAL0. ss.
        - ii. rewrite PROMISES in *.
          erewrite Memory.bot_get in PROMISE. clarify. } intros PROMS.

      assert (RESERVES: only_reserves e2'.(Thread.local).(Local.promises)).
      { replace (Local.promises (Thread.local e2')) with
            (Local.promises (Thread.local e3)); cycle 1.
        { unfold no_sc in BREAKQ. des_ifs.
          - inv STEP0; inv STEP; ss. inv LOCAL. inv LOCAL0. ss.
          - inv STEP0; inv STEP; ss. inv LOCAL. inv LOCAL0. ss. }

        assert (MAXVIEW: TimeMap.le
                           tm
                           (View.rlx (TView.cur (Local.tview (Thread.local e3))))).
        { unfold no_sc in BREAKQ. des_ifs.
          - apply NNPP in BREAKQ. etrans; eauto.
            inv STEP0; inv STEP; ss. inv LOCAL. inv LOCAL0. ss. des_ifs.
          - etrans; eauto.
            inv STEP0; inv STEP; ss. inv LOCAL. inv LOCAL0. ss. }

        econs.
        - ii. destruct msg; auto. exfalso.
          eapply pf_step_rtc_promises_decrease in STEPS0; cycle 1.
          + eapply pf_step_promises_decrease; eauto.
            * econs; eauto. econs; eauto.
            * econs; eauto.
          + ss. inv STEPS0.
            eapply PROMS in GET.
            hexploit max_full_timemap_get.
            * eauto.
            * inv WF. eapply Memory.cap_le; eauto.
            * i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
        - inv WF0. eauto. }

      destruct e2'. destruct local. ss.
      eapply no_sc_any_sc_rtc in STEPS0; ss. des.
      exploit reserves_cancelable; eauto.
      { inv WF2. eauto. }
      i. des. esplits.
      * etrans.
        { eapply STEP. }
        { eapply pred_step_rtc_mon; eauto.
          unfold is_cancel. i. des_ifs. }
      * ss. eauto.
Qed.
