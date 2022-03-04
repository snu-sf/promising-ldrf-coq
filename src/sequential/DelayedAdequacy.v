Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Behavior.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import PromiseConsistent.
Require Import MemoryProps.

Require Import Program.

Require Import Pred.
Require Import Delayed.
Require Import LowerMemory.
Require Import DelayedStep.
Require Import DelayedSimulation.
Require Import NALoc.

Set Implicit Arguments.



Program Instance closed_future_timemap_PreOrder loc_na tm: PreOrder (closed_future_timemap loc_na tm).
Next Obligation.
Proof.
  ii. auto.
Qed.
Next Obligation.
Proof.
  ii. exploit H; eauto. exploit H0; eauto. i. etrans; eauto.
Qed.

Global Program Instance closed_future_view_PreOrder loc_na vw: PreOrder (closed_future_view loc_na vw).
Next Obligation.
Proof.
  ii. econs.
  { refl. }
  { refl. }
Qed.
Next Obligation.
Proof.
  ii. econs.
  { etrans; [eapply H|eapply H0]. }
  { etrans; [eapply H|eapply H0]. }
Qed.

Global Program Instance closed_future_tview_PreOrder loc_na tvw: PreOrder (closed_future_tview loc_na tvw).
Next Obligation.
Proof.
  ii. econs.
  { i. refl. }
  { refl. }
  { refl. }
Qed.
Next Obligation.
Proof.
  ii. econs.
  { i. etrans; [eapply H|eapply H0]. }
  { etrans; [eapply H|eapply H0]. }
  { etrans; [eapply H|eapply H0]. }
Qed.

Section WORLD.

Variable world: Type.

Variable world_messages_le: Messages.t -> Messages.t -> world -> world -> Prop.
Context `{world_messages_le_PreOrder: forall msgs_src msgs_tgt, PreOrder (world_messages_le msgs_src msgs_tgt)}.

Hypothesis world_messages_le_mon:
  forall msgs_src0 msgs_tgt0 msgs_src1 msgs_tgt1 w0 w1
         (LE: world_messages_le msgs_src1 msgs_tgt1 w0 w1)
         (MSGSRC: msgs_src0 <4= msgs_src1)
         (MSGTGT: msgs_tgt0 <4= msgs_tgt1),
    world_messages_le msgs_src0 msgs_tgt0 w0 w1.

Variable sim_memory: forall (w: world) (mem_src mem_tgt:Memory.t), Prop.
Variable sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop.

Variable loc_na: Loc.t -> Prop.


Section LANG.
  Variable lang_src lang_tgt: language.

  Definition sim_thread_wf
             b w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt :=
    (<<SIM: @DelayedSimulation.sim_thread world world_messages_le sim_memory sim_timemap loc_na lang_src lang_tgt b w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt>>) /\
    (<<LOCALSRC: Local.wf lc_src mem_src>>) /\
    (<<LOCALTGT: Local.wf lc_tgt mem_tgt>>) /\
    (<<SCSRC: Memory.closed_timemap sc_src mem_src>>) /\
    (<<SCTGT: Memory.closed_timemap sc_tgt mem_tgt>>) /\
    (<<MEMSRC: Memory.closed mem_src>>) /\
    (<<MEMTGT: Memory.closed mem_tgt>>) /\
    (<<TIMEMAP: b = false -> sim_timemap w sc_src sc_tgt>>) /\
    (<<MEMORY: b = false -> sim_memory w mem_src mem_tgt>>)
  .

  Lemma sim_thread_flag_mon
        b w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt
        (SIM: sim_thread_wf b w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
    :
      sim_thread_wf true w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt.
  Proof.
    red in SIM. des. red. esplits; eauto; ss.
    punfold SIM0. pfold. ii. exploit SIM0; eauto. i. des.
    { left. esplits; eauto; ss. }
    { right. eauto. }
  Qed.

  Lemma steps_steps_failure lang th0 th1
        (STEPS: rtc (@Thread.tau_step lang) th0 th1)
        (FAILURE: Thread.steps_failure th1)
    :
      Thread.steps_failure th0.
  Proof.
    unfold Thread.steps_failure in *. des. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_failure_failure
        (w: world) st_src lc_src sc_src mem_src
        st_tgt lc_tgt sc_tgt mem_tgt
        (SIM: _sim_thread_failure
                lang_src lang_tgt w st_src lc_src sc_src mem_src
                st_tgt lc_tgt sc_tgt mem_tgt)
    :
      Thread.steps_failure (Thread.mk _ st_src lc_src sc_src mem_src).
  Proof.
    red in SIM. des. eapply steps_steps_failure; eauto.
  Qed.

  Lemma sim_thread_wf_promise_step
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 pf_tgt e_tgt
        (STEP_TGT: Thread.step pf_tgt e_tgt
                               (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                               (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
        (PROMISE: is_promise e_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 st_src1 lc_src1 sc_src1 mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                      (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    red in SIM. des. punfold SIM0.
    exploit Thread.step_future; eauto. i. des. ss.
    hexploit step_promise_consistent; eauto. i. ss.
    exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit PROMISE0; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    right. inv SIM; ss. esplits.
    { eauto. }
    { red. esplits; eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_promise_steps
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
        (STEP_TGT: rtc (tau (@pred_step is_promise _))
                       (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                       (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 st_src1 lc_src1 sc_src1 mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                      (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    remember (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0).
    remember (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1).
    revert w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
           st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 Heqt Heqt0 SIM CONS_TGT.
    induction STEP_TGT; i; clarify.
    { right. esplits; eauto. refl. }
    { inv H. inv TSTEP. inv STEP. destruct y.
      hexploit sim_thread_wf_promise_step; eauto.
      { red in SIM. des.
        hexploit Thread.step_future; eauto. i. des; ss.
        hexploit rtc_all_step_promise_consistent.
        { eapply rtc_implies; [|eapply STEP_TGT]. i.
          inv H. inv TSTEP. econs; eauto.
        }
        all: eauto.
      }
      i. des.
      { left. eauto. }
      hexploit IHSTEP_TGT; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. eapply unchangable_increase in STEP0; eauto. }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_lower_step
        b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 e_tgt
        (STEP_TGT: lower_step e_tgt
                              (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                              (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 st_src1 lc_src1 sc_src1 mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                      (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: sim_thread_wf true w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    red in SIM. des. punfold SIM0. dup STEP_TGT. inv STEP_TGT; ss.
    hexploit Thread.step_program; eauto. intros _STEP.
    exploit Thread.step_future; eauto. i. des. ss.
    hexploit step_promise_consistent; eauto. i. ss.
    exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit LOWER; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    right. inv SIM; ss. esplits.
    { eauto. }
    { red. esplits; eauto; ss. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_lower_steps
        b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
        (STEP_TGT: rtc (tau (@lower_step _))
                       (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                       (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 st_src1 lc_src1 sc_src1 mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                      (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: sim_thread_wf true w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    remember (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0).
    remember (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1).
    revert b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
           st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 Heqt Heqt0 SIM CONS_TGT.
    induction STEP_TGT; i; clarify.
    { right. esplits; eauto.
      { eapply sim_thread_flag_mon; eauto. }
      { refl. }
    }
    { inv H. destruct y.
      hexploit sim_thread_wf_lower_step; eauto.
      { red in SIM. des. dup TSTEP. inv TSTEP. ss.
        hexploit Thread.program_step_future; eauto. i. des; ss.
        hexploit rtc_all_step_promise_consistent.
        { eapply rtc_implies; [|eapply STEP_TGT]. i.
          inv H. inv TSTEP. econs; eauto. econs; eauto. econs 2; eauto.
        }
        all: eauto.
      }
      i. des.
      { left. eauto. }
      hexploit IHSTEP_TGT; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. hexploit unchangable_increase.
            { inv TSTEP. econs 2; eauto. }
            { eauto. }
            { eauto. }
          }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_release_step
        b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 pf_tgt e_tgt
        (STEP_TGT: Thread.step pf_tgt e_tgt
                               (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                               (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (RELEASE: release_event e_tgt)
        (SIM: sim_thread_wf b w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 e_src
             st_src1 lc_src1 sc_src1 mem_src1
             st_src2 lc_src2 sc_src2 mem_src2
             st_src3 lc_src3 sc_src3 mem_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                       (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)
                     (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)
                       (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src3 lc_src3 sc_src3 mem_src3 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    red in SIM. des. punfold SIM0.
    exploit Thread.step_future; eauto. i. des. ss.
    hexploit step_promise_consistent; eauto. i. ss.
    exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit RELEASE0; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit Thread.rtc_tau_step_future; [eapply STEPS|..]; eauto. i. des; ss.
    hexploit Thread.opt_step_future; [eapply STEP_SRC|..]; eauto. i. des; ss.
    hexploit Thread.rtc_tau_step_future; [eapply STEPS_AFTER|..]; eauto. i. des; ss.
    right. inv SIM; ss. esplits.
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { red. esplits; eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_dstep
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 e_tgt
        (STEP_TGT: dstep e_tgt
                         (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                         (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 e_src
             st_src1 lc_src1 sc_src1 mem_src1
             st_src2 lc_src2 sc_src2 mem_src2
             st_src3 lc_src3 sc_src3 mem_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                       (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)
                     (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)
                       (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src3 lc_src3 sc_src3 mem_src3 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    inv STEP_TGT. dup SIM. red in SIM. des.
    hexploit rtc_implies; [|eapply PROMISES|].
    { instantiate (1:=@Thread.all_step _).
      i. inv H. inv TSTEP. econs; eauto.
    } intros PROMISES'.
    hexploit rtc_implies; [|eapply LOWERS|].
    { instantiate (1:=@Thread.all_step _).
      i. inv H. inv TSTEP. econs; eauto. econs; eauto. econs 2; eauto.
    } intros LOWERS'.
    hexploit Thread.rtc_all_step_future; [eapply PROMISES'|..]; eauto. i. des; ss.
    hexploit Thread.rtc_all_step_future; [eapply LOWERS'|..]; eauto. i. des; ss.
    hexploit Thread.step_future; [eapply STEP_RELEASE|..]; eauto. i. des; ss.
    hexploit step_promise_consistent; [eapply STEP_RELEASE|..]; eauto. intros CONS_TGT2.
    hexploit rtc_all_step_promise_consistent; [eapply LOWERS'|..]; eauto. intros CONS_TGT1.
    hexploit rtc_all_step_promise_consistent; [eapply PROMISES'|..]; eauto. intros CONS_TGT0.
    destruct e2, e3. ss.
    hexploit sim_thread_wf_promise_steps; eauto. i. des; ss.
    { eauto. }
    hexploit sim_thread_wf_lower_steps; eauto. i. des; ss.
    { left. eapply steps_steps_failure; eauto. }
    hexploit sim_thread_wf_release_step; eauto. i. des; ss.
    { left. eapply steps_steps_failure; eauto. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; [eauto|]. etrans; [eauto|]. eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { etrans.
      { eauto. }
      eapply world_messages_le_mon.
      2:{ i. eapply (unchangable_rtc_tau_step_increase STEPS); eauto. }
      2:{ i. eapply (unchangable_rtc_all_step_increase PROMISES'); eauto. }
      ss. etrans.
      { eauto. }
      eapply world_messages_le_mon.
      2:{ i. eapply (unchangable_rtc_tau_step_increase STEPS0); eauto. }
      2:{ i. eapply (unchangable_rtc_all_step_increase LOWERS'); eauto. }
      eauto.
    }
  Qed.

  Lemma sim_thread_wf_rtc_tau_dstep
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
        (STEP_TGT: rtc (tau (@dstep lang_tgt))
                       (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                       (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1
             st_src1 lc_src1 sc_src1 mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                      (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    remember (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0).
    remember (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1).
    revert w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
           st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 Heqt Heqt0 SIM CONS_TGT.
    induction STEP_TGT; i; clarify.
    { right. esplits; eauto. refl. }
    { inv H. destruct y.
      hexploit sim_thread_wf_dstep; eauto.
      { red in SIM. des.
        eapply dstep_rtc_all_step in TSTEP.
        eapply rtc_dstep_rtc_tau_step in STEP_TGT.
        hexploit Thread.rtc_all_step_future; [eapply TSTEP|..]; eauto. i. des; ss.
        hexploit rtc_tau_step_promise_consistent; [eapply STEP_TGT|..]; eauto.
      }
      i. des.
      { left. eauto. }
      assert (STEPS_SRC: rtc (@Thread.tau_step lang_src)
                             (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                             (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)).
      { etrans; [eauto|]. etrans; [|eapply STEPS2]. inv STEPS1.
        { refl. }
        { econs 2; [|refl]. econs.
          { econs; eauto. }
          { rewrite EVENT in EVENT0. inv EVENT0; ss. }
        }
      }
      hexploit IHSTEP_TGT; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS_SRC; eauto. }
          { i. hexploit unchangable_rtc_all_step_increase.
            { eapply dstep_rtc_all_step; eauto. }
            { eauto. }
            { eauto. }
          }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_dsteps
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 e_tgt
        (STEP_TGT: dsteps e_tgt
                          (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                          (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: Local.promise_consistent lc_tgt1)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 e_src
             st_src1 lc_src1 sc_src1 mem_src1
             st_src2 lc_src2 sc_src2 mem_src2
             st_src3 lc_src3 sc_src3 mem_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                       (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)
                     (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)
                       (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
        (<<EVENT: machine_event_le e_tgt (ThreadEvent.get_machine_event e_src)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src3 lc_src3 sc_src3 mem_src3 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
        (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>).
  Proof.
    inv STEP_TGT.
    { dup SIM. red in SIM. des.
      pose proof (rtc_dstep_rtc_tau_step DSTEPS) as DSTEPS'.
      hexploit Thread.rtc_tau_step_future; [eapply DSTEPS'|..]; eauto. i. des; ss.
      hexploit rtc_all_step_promise_consistent.
      { eapply rtc_implies; [|eapply PROMISES]. i.
        inv H. inv TSTEP. econs; eauto.
      }
      all: eauto. intros CONS_TGT1.
      hexploit rtc_tau_step_promise_consistent.
      { eapply rtc_dstep_rtc_tau_step. eapply DSTEPS. }
      all: eauto. intros CONS_TGT0. destruct e2. ss.
      hexploit sim_thread_wf_rtc_tau_dstep; eauto. i. des; ss.
      { left. eauto. }
      hexploit sim_thread_wf_promise_steps; eauto. i. des; ss.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { eauto. }
      { econs 1. }
      { eauto. }
      { econs. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. hexploit unchangable_rtc_tau_step_increase; [eapply DSTEPS'|..]; eauto. }
        }
      }
    }
    { dup SIM. red in SIM. des.
      pose proof (rtc_dstep_rtc_tau_step DSTEPS) as DSTEPS'.
      pose proof (dstep_rtc_all_step DSTEP) as DSTEP'.
      hexploit Thread.rtc_tau_step_future; [eapply DSTEPS'|..]; eauto. i. des; ss.
      hexploit rtc_all_step_promise_consistent; [eapply DSTEP'|..]; eauto. intros CONS_TGT1.
      hexploit rtc_tau_step_promise_consistent; [eapply DSTEPS'|..]; eauto. intros CONS_TGT0.
      destruct e2. ss.
      hexploit sim_thread_wf_rtc_tau_dstep; eauto. i. des; ss.
      { left. eauto. }
      hexploit sim_thread_wf_dstep; eauto. i. des; ss.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { etrans; eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { etrans.
        { eauto. }
        { eapply world_messages_le_mon; eauto.
          { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
          { i. hexploit unchangable_rtc_tau_step_increase; [eapply DSTEPS'|..]; eauto. }
        }
      }
    }
  Qed.

  Lemma sim_thread_wf_cap
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt
        cap_src cap_tgt
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt)
        (CONS_TGT: Local.promise_consistent lc_tgt)
        (CAPSRC: Memory.cap mem_src0 cap_src)
        (CAPTGT: Memory.cap mem_tgt cap_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 st_src1 lc_src1 sc_src1 mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st_src0 lc_src0 sc_src0 cap_src)
                      (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<SIM: sim_thread_wf false w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt lc_tgt sc_tgt cap_tgt>>).
  Proof.
    red in SIM. des. punfold SIM0. exploit SIM0; eauto. i. des; ss.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit CAP; eauto. i. des. inv SIM; ss. right. esplits.
    { refl. }
    { red. esplits; eauto.
      { eapply Local.cap_wf; eauto. }
      { eapply Local.cap_wf; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed_timemap; eauto. }
      { eapply Memory.cap_closed; eauto. }
      { eapply Memory.cap_closed; eauto. }
    }
  Qed.

  Lemma sim_thread_wf_terminal
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt
        (SIM: sim_thread_wf true w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt)
        (LANG_TGT: Language.is_terminal _ st_tgt)
        (LOCAL_TGT: Local.is_terminal lc_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
    exists w1
           st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
      (<<LANG_SRC: Language.is_terminal _ st_src1>>) /\
      (<<LOCAL_SRC: Local.is_terminal lc_src1>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>) /\
      (<<MEM: sim_memory w1 mem_src1 mem_tgt>>) /\
      (<<SC: sim_timemap w1 sc_src1 sc_tgt>>)

  .
  Proof.
    red in SIM. des. punfold SIM0. exploit SIM0; eauto.
    { eapply Local.terminal_promise_consistent; eauto. }
    i. des.
    2:{ left. eapply sim_thread_failure_failure; eauto. }
    exploit TERMINAL; eauto.
    { eapply LOCAL_TGT. }
    i. des; ss.
    { left. eapply steps_steps_failure; eauto. }
    right. esplits; eauto.
  Qed.

  Definition sim_thread_wf_past w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt :=
    exists w' sc_src' mem_src' sc_tgt' mem_tgt',
      (<<SIM: sim_thread_wf false w' st_src lc_src sc_src' mem_src' st_tgt lc_tgt sc_tgt' mem_tgt'>>) /\
      (<<SC_FUTURE_SRC: TimeMap.le sc_src' sc_src>>) /\
      (<<SC_FUTURE_TGT: TimeMap.le sc_tgt' sc_tgt>>) /\
      (<<MEM_FUTURE_SRC: Memory.future_weak mem_src' mem_src>>) /\
      (<<MEM_FUTURE_TGT: Memory.future_weak mem_tgt' mem_tgt>>) /\
      (<<CLOSEDFUTURE: closed_future_tview loc_na lc_tgt.(Local.tview) mem_tgt' mem_tgt>>) /\
      (<<WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) (Messages.of_memory lc_tgt.(Local.promises)) w' w>>) /\
      (<<CONSISTENTSRC: Thread.consistent (Thread.mk _ st_src lc_src sc_src' mem_src')>>) /\
      (<<CONSISTENTTGT: Local.promise_consistent lc_tgt>>) /\
      (<<NFAILURE: ~ Thread.steps_failure (Thread.mk _ st_src lc_src sc_src' mem_src')>>) /\
      (<<LOCALSRC: Local.wf lc_src mem_src>>) /\
      (<<LOCALTGT: Local.wf lc_tgt mem_tgt>>) /\
      (<<SCSRC: Memory.closed_timemap sc_src mem_src>>) /\
      (<<SCTGT: Memory.closed_timemap sc_tgt mem_tgt>>) /\
      (<<MEMSRC: Memory.closed mem_src>>) /\
      (<<MEMTGT: Memory.closed mem_tgt>>) /\
      (<<TIMEMAP: sim_timemap w sc_src sc_tgt>>) /\
      (<<MEMORY: sim_memory w mem_src mem_tgt>>)
  .

  Lemma sim_thread_wf_past_future
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt
        (SIM: sim_thread_wf_past w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
    exists w1
           st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
      (<<SIM: sim_thread_wf false w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt lc_tgt sc_tgt mem_tgt>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>).
  Proof.
    red in SIM. des. red in SIM0. des.
    punfold SIM. exploit SIM; eauto. i. des.
    2:{ exfalso. eapply NFAILURE. eapply sim_thread_failure_failure; eauto. }
    exploit FUTURE; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    inv SIM0; ss. right. esplits; eauto.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    red. esplits; eauto.
  Qed.

  Lemma sim_thread_wf_consistent_aux
        w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt
        (CONSISTENT: delayed_consistent (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt))
        (SIM: sim_thread_wf false w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src sc_src mem_src)>>) \/
      (<<CONSISTENT: Thread.consistent (Thread.mk _ st_src lc_src sc_src mem_src)>>).
  Proof.
    destruct (classic (Thread.steps_failure (Thread.mk _ st_src lc_src sc_src mem_src))) as [FAILURE|NFAILURE].
    { auto. }
    right. ii. ss.
    hexploit Memory.cap_exists.
    { red in SIM. des. eapply MEMTGT. }
    intros [cap_tgt CAPTGT]. des.
    hexploit sim_thread_wf_cap; eauto.
    { red in SIM. des. eapply delayed_consistent_promise_consistent in CONSISTENT; eauto. }
    exploit CONSISTENT; eauto. i. des; ss.
    { left. destruct e2. subst.
      hexploit sim_thread_wf_dsteps; eauto.
      { inv DSTEPS. inv DSTEP. inv STEP_RELEASE; inv STEP; ss.
        inv LOCAL; ss; inv LOCAL0; ss.
      }
      i. des.
      { eapply steps_steps_failure; eauto. }
      { inv EVENT. inv STEPS1; ss.
        repeat red. esplits.
        { etrans; eauto. }
        { replace pf with true in STEP; [eauto|]. inv STEP; inv STEP0; ss. }
        { auto. }
      }
    }
    { destruct e2, e3. subst. ss.
      pose proof (dsteps_rtc_all_step DSTEPS) as STEPS_TGT0.
      hexploit rtc_implies; [|eapply STEPS0|..].
      { instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. econs; eauto. econs 2; eauto. }
      intros STEPS_TGT1.
      dup SIM0. red in SIM0. des.
      hexploit Thread.rtc_all_step_future; [eapply STEPS_TGT0|..]; eauto; ss. i. des.
      hexploit rtc_tau_step_promise_consistent; [eapply STEPS_TGT1|..]; eauto.
      { eapply Local.bot_promise_consistent in PROMISES; eauto. }
      intros CONSISTENT1.
      hexploit sim_thread_wf_dsteps; eauto. i. des.
      { left. eapply steps_steps_failure; eauto. }
      { hexploit sim_thread_wf_lower_steps; eauto.
        { eapply Local.bot_promise_consistent in PROMISES; eauto. }
        i. des.
        { left. eapply steps_steps_failure; [|eauto].
          etrans; eauto. etrans; eauto. etrans; [|eauto]. inv STEPS2.
          { refl. }
          { econs 2; [|refl]. econs.
            { econs; eauto. }
            { inv EVENT; ss. }
          }
        }
        inv EVENT. red in SIM1. des.
        assert (STEPS_SRC: rtc (@Thread.tau_step _) (Thread.mk _ st_src lc_src sc_src mem1) (Thread.mk _ st_src4 lc_src4 sc_src4 mem_src4)).
        { etrans; eauto. etrans; eauto. etrans; [|eauto]. etrans; [|eauto]. inv STEPS2.
          { refl. }
          { econs 2; [|refl]. econs; eauto. econs; eauto. }
        }
        red in SIM3. des.
        punfold SIM1. exploit SIM1; eauto.
        { eapply Local.bot_promise_consistent in PROMISES; eauto. }
        i. des; ss.
        2:{ left. eapply steps_steps_failure; eauto. eapply sim_thread_failure_failure; eauto. }
        exploit CERTIFICATION; eauto. i. des.
        { left. eapply steps_steps_failure; eauto. eapply steps_steps_failure; eauto. }
        right. esplits.
        { etrans; eauto. }
        { eauto. }
      }
    }
  Qed.

  Lemma sim_thread_wf_consistent
        w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt
        (CONSISTENT: delayed_consistent (Thread.mk _ st_tgt lc_tgt sc_tgt mem_tgt))
        (SIM: sim_thread_wf false w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src lc_src sc_src mem_src)>>) \/
    ((<<CONSISTENT: Thread.consistent (Thread.mk _ st_src lc_src sc_src mem_src)>>) /\
     (<<SIM: sim_thread_wf_past w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt>>))
  .
  Proof.
    hexploit sim_thread_wf_consistent_aux; eauto. i. des; eauto.
    destruct (classic (Thread.steps_failure (Thread.mk _ st_src lc_src sc_src mem_src))) as [FAILURE|NFAILURE].
    { auto. }
    right. splits; auto. dup SIM. red in SIM. des.
    red. esplits; eauto; try by refl.
    eapply delayed_consistent_promise_consistent in CONSISTENT; eauto.
  Qed.

  Lemma sim_thread_wf_past_dsteps
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 e_tgt
        (STEP_TGT: dsteps e_tgt
                          (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                          (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf_past w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: e_tgt <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
    :
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      exists w1 e_src
             st_src1 lc_src1 sc_src1 mem_src1
             st_src2 lc_src2 sc_src2 mem_src2
             st_src3 lc_src3 sc_src3 mem_src3,
        (<<STEPS0: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                       (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
        (<<STEPS1: Thread.opt_step
                     e_src
                     (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)
                     (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
        (<<STEPS2: rtc (@Thread.tau_step _)
                       (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)
                       (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
        (<<EVENT: machine_event_le e_tgt (ThreadEvent.get_machine_event e_src)>>) /\
        (<<CONT: forall (EVENT: ThreadEvent.get_machine_event e_src <> MachineEvent.failure),
            (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) \/
            ((<<CONSISTENT: Thread.consistent (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
             (<<SIM: sim_thread_wf_past w1 st_src3 lc_src3 sc_src3 mem_src3 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
             (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>))>>).
  Proof.
    assert (CONSISTENT: Local.promise_consistent lc_tgt1).
    { destruct (classic (e_tgt = MachineEvent.failure)).
      { subst. inv STEP_TGT. inv DSTEP; ss.
        inv STEP_RELEASE; inv STEP; ss.
        inv LOCAL; ss; inv LOCAL0; ss.
      }
      { red in SIM. des.
        eapply dsteps_rtc_all_step in STEP_TGT.
        hexploit Thread.rtc_all_step_future; eauto.
        i. des; ss.
        hexploit delayed_consistent_promise_consistent; eauto.
      }
    }
    hexploit sim_thread_wf_past_future; eauto. i. des.
    { left. eauto. }
    hexploit sim_thread_wf_dsteps; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { i. hexploit CONS_TGT; eauto.
      { inv EVENT; ss. rewrite H1 in *. ss. }
      i. hexploit sim_thread_wf_consistent; eauto. i. des.
      { eauto. }
      { right. esplits; eauto.
        etrans.
        { eauto. }
        eapply world_messages_le_mon; eauto.
        i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto.
      }
    }
  Qed.

  Lemma sim_thread_wf_past_dsteps_full
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1 e_tgt
        (STEP_TGT: dsteps e_tgt
                          (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                          (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (SIM: sim_thread_wf_past w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (CONS_TGT: e_tgt <> MachineEvent.failure ->
                   delayed_consistent (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
      ((exists w1 st_src1 lc_src1 sc_src1 mem_src1,
           (<<STEPS0: rtc (@Thread.tau_step _)
                          (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                          (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
           (<<SILENT: e_tgt = MachineEvent.silent>>) /\
           (<<CONSISTENT: Thread.consistent (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
           (<<SIM: sim_thread_wf_past w1 st_src1 lc_src1 sc_src1 mem_src1 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
           (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>)) \/
       (exists pf_src e_src
               st_src1 lc_src1 sc_src1 mem_src1
               st_src2 lc_src2 sc_src2 mem_src2,
           (<<STEPS0: rtc (@Thread.tau_step _)
                          (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                          (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
           (<<STEPS1: Thread.step
                        pf_src e_src
                        (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)
                        (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
           (<<CONSISTENT0: Thread.consistent (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) /\
           (<<EVENT: machine_event_le e_tgt (ThreadEvent.get_machine_event e_src)>>) /\
           (<<CONT: __guard__
                      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)>>) \/
                       (exists w1 st_src3 lc_src3 sc_src3 mem_src3,
                           (<<STEPS2: rtc (@Thread.tau_step _)
                                          (Thread.mk _ st_src2 lc_src2 sc_src2 mem_src2)
                                          (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
                           (<<CONSISTENT1: Thread.consistent (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)>>) /\
                           (<<SIM: sim_thread_wf_past w1 st_src3 lc_src3 sc_src3 mem_src3 st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1>>) /\
                           (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>)))>>))).
  Proof.
    hexploit sim_thread_wf_past_dsteps; eauto. i. des.
    { left. eauto. }
    destruct (ThreadEvent.get_machine_event e_src) eqn:EQ.
    { assert (STEPS_SRC: rtc (@Thread.tau_step _ )
                             (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                             (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)).
      { etrans; eauto. etrans; [|eauto]. inv STEPS1.
        { refl. }
        { econs 2; [|refl]. econs; eauto. econs; eauto. }
      }
      hexploit CONT; eauto; ss. i. des.
      { left. eapply steps_steps_failure; eauto. }
      right. esplits.
      { left. esplits; eauto. inv EVENT; auto. }
    }
    { inv STEPS1; ss. right. right. esplits.
      { eauto. }
      { eauto. }
      { red. right. esplits.
        { refl. }
        { ss. inv STEP; inv STEP0; ss. inv LOCAL; ss.
          inv LOCAL0. ss. eauto.
        }
      }
      { rewrite EQ. eauto. }
      hexploit CONT; eauto; ss. i. des.
      { left. eapply steps_steps_failure; [|eauto]; eauto. }
      right. esplits; eauto.
    }
    { inv STEPS1; ss. left. repeat red. esplits.
      { eauto. }
      { replace pf with true in STEP; [eauto|].
        inv STEP; ss. inv STEP0; ss.
      }
      { eauto. }
    }
  Qed.

  Lemma sim_thread_wf_past_terminal
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0
        st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1
        (SIM: sim_thread_wf_past w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
        (STEPS_TGT: rtc (tau (@lower_step _))
                        (Thread.mk _ st_tgt0 lc_tgt0 sc_tgt0 mem_tgt0)
                        (Thread.mk _ st_tgt1 lc_tgt1 sc_tgt1 mem_tgt1))
        (LANG_TGT: Language.is_terminal _ st_tgt1)
        (LOCAL_TGT: Local.is_terminal lc_tgt1)
    :
    (<<FAILURE: Thread.steps_failure (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)>>) \/
    exists w1
           st_src1 lc_src1 sc_src1 mem_src1,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st_src0 lc_src0 sc_src0 mem_src0)
                    (Thread.mk _ st_src1 lc_src1 sc_src1 mem_src1)>>) /\
      (<<LANG_SRC: Language.is_terminal _ st_src1>>) /\
      (<<LOCAL_SRC: Local.is_terminal lc_src1>>) /\
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt0 lc_tgt0.(Local.promises)) w0 w1>>) /\
      (<<MEM: sim_memory w1 mem_src1 mem_tgt1>>) /\
      (<<SC: sim_timemap w1 sc_src1 sc_tgt1>>)
  .
  Proof.
    hexploit sim_thread_wf_past_future; eauto. i. des.
    { left. eauto. }
    hexploit sim_thread_wf_lower_steps; eauto.
    { inv LOCAL_TGT. eapply Local.bot_promise_consistent; eauto. }
    i. des.
    { left. eapply steps_steps_failure; eauto. }
    hexploit sim_thread_wf_terminal; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; [|eauto]. etrans; eauto. }
    { eauto. }
    { eauto. }
    { etrans.
      { eauto. }
      eapply world_messages_le_mon.
      { etrans.
        { eauto. }
        eapply world_messages_le_mon.
        { eauto. }
        { i. eapply unchangable_rtc_tau_step_increase in STEPS0; eauto. }
        { i. eapply rtc_implies in STEPS_TGT.
          2:{ instantiate (1:=@Thread.tau_step _). i. inv H. inv TSTEP. econs; eauto. econs; eauto. econs 2; eauto. }
          eapply unchangable_rtc_tau_step_increase in STEPS_TGT; eauto. }
      }
      { i. eapply unchangable_rtc_tau_step_increase in STEPS; eauto. }
      { auto. }
    }
    { eauto. }
    { eauto. }
  Qed.

  Lemma sim_thread_wf_past_update
        w0 st_src lc_src sc_src0 mem_src0 st_tgt lc_tgt sc_tgt0 mem_tgt0
        w1 sc_src1 mem_src1 sc_tgt1 mem_tgt1
        (SIM: sim_thread_wf_past w0 st_src lc_src sc_src0 mem_src0 st_tgt lc_tgt sc_tgt0 mem_tgt0)
        (SC_FUTURE_SRC: TimeMap.le sc_src0 sc_src1)
        (SC_FUTURE_TGT: TimeMap.le sc_tgt0 sc_tgt1)
        (MEM_FUTURE_SRC: Memory.future_weak mem_src0 mem_src1)
        (MEM_FUTURE_TGT: Memory.future_weak mem_tgt0 mem_tgt1)
        (WORLD_FUTURE: world_messages_le (Messages.of_memory lc_src.(Local.promises)) (Messages.of_memory lc_tgt.(Local.promises)) w0 w1)
        (LOCALSRC: Local.wf lc_src mem_src1)
        (LOCALTGT: Local.wf lc_tgt mem_tgt1)
        (SCSRC: Memory.closed_timemap sc_src1 mem_src1)
        (SCTGT: Memory.closed_timemap sc_tgt1 mem_tgt1)
        (MEMSRC: Memory.closed mem_src1)
        (MEMTGT: Memory.closed mem_tgt1)
        (TIMEMAP: sim_timemap w1 sc_src1 sc_tgt1)
        (MEMORY: sim_memory w1 mem_src1 mem_tgt1)
        (CLOSEDFUTURE: closed_future_tview loc_na lc_tgt.(Local.tview) mem_tgt0 mem_tgt1)
    :
    sim_thread_wf_past w1 st_src lc_src sc_src1 mem_src1 st_tgt lc_tgt sc_tgt1 mem_tgt1.
  Proof.
    red in SIM. des. red. esplits; eauto.
    { etrans; eauto. }
    { etrans; eauto. }
    { etrans; eauto. }
    { etrans; eauto. }
  Qed.
End LANG.

Section Simulation.
  Definition SIM :=
    forall (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim
             (sim: SIM)
             (ths_src0:Threads.t) (sc_src0:TimeMap.t) (mem_src0:Memory.t)
             (ths_tgt0:Threads.t) (sc_tgt0:TimeMap.t) (mem_tgt0:Memory.t)
    : Prop :=
    forall (WF_SRC: Configuration.wf (Configuration.mk ths_src0 sc_src0 mem_src0))
           (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0)),
      (<<TERMINAL:
         forall (TERMINAL_TGT: d_na_terminal_steps loc_na (IdentSet.elements (Threads.tids ths_tgt0)) (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0)),
           (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 sc_src0 mem_src0)>>) \/
            exists ths_src1 sc_src1 mem_src1,
              (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 sc_src0 mem_src0) (Configuration.mk ths_src1 sc_src1 mem_src1)>>) /\
              (<<TERMINAL_SRC: Threads.is_terminal ths_src1>>)>>) /\
        (<<STEP:
          forall e_tgt tid_tgt ths_tgt1 sc_tgt1 mem_tgt1
                 (STEP_TGT: d_na_step loc_na e_tgt tid_tgt (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0) (Configuration.mk ths_tgt1 sc_tgt1 mem_tgt1)),
            (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 sc_src0 mem_src0)>>) \/
              exists e_src tid_src ths_src1 sc_src1 mem_src1 ths_src2 sc_src2 mem_src2,
                (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 sc_src0 mem_src0) (Configuration.mk ths_src1 sc_src1 mem_src1)>>) /\
                (<<STEP_SRC: Configuration.opt_step e_src tid_src (Configuration.mk ths_src1 sc_src1 mem_src1) (Configuration.mk ths_src2 sc_src2 mem_src2)>>) /\
                (<<EVENT: machine_event_le e_tgt e_src>>) /\
                ((<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src2 sc_src2 mem_src2)>>) \/
                   exists ths_src3 sc_src3 mem_src3,
                     (<<STEPS_AFTER: rtc Configuration.tau_step (Configuration.mk ths_src2 sc_src2 mem_src2) (Configuration.mk ths_src3 sc_src3 mem_src3)>>) /\
                     (<<SIM: forall (EVENT: e_src <> MachineEvent.failure), sim ths_src3 sc_src3 mem_src3 ths_tgt1 sc_tgt1 mem_tgt1>>))>>).

  Lemma _sim_mon: monotone6 _sim.
  Proof.
    ii. exploit IN; try apply SC1; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des; eauto.
    { right. esplits; eauto. }
    { right. esplits; eauto. right. esplits; eauto. }
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco6 _sim bot6.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_adequacy
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt
      (WF_SRC: Configuration.wf (Configuration.mk ths_src sc_src mem_src))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (SIM: sim ths_src sc_src mem_src ths_tgt sc_tgt mem_tgt):
  delayed_na_behaviors loc_na (Configuration.mk ths_tgt sc_tgt mem_tgt) <2=
  behaviors Configuration.step (Configuration.mk ths_src sc_src mem_src).
Proof.
  s. i.
  revert WF_SRC WF_TGT SIM.
  revert ths_src sc_src mem_src.
  remember (Configuration.mk ths_tgt sc_tgt mem_tgt).
  revert ths_tgt sc_tgt mem_tgt Heqt.
  induction PR; i; subst.
  - punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit TERMINAL; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + eapply rtc_tau_step_behavior; eauto.
      econs 1. eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + red in FAILURE. des.
      eapply rtc_tau_step_behavior; eauto. inv STEP_SRC.
      { eapply rtc_tau_step_behavior; eauto. eapply behaviors_failure; eauto. }
      { inv EVENT0. econs 2; [eauto| | auto].
        { eapply rtc_tau_step_behavior; eauto. eapply behaviors_failure; eauto. }
        { etrans; eauto. }
      }
    + hexploit SIM1; eauto.
      { inv EVENT0; ss. }
      clear SIM1. intros SIM1.
      inv SIM1; [|done]. inv STEP.
      eapply rtc_tau_step_behavior; eauto.
      exploit DConfiguration.step_future; try exact STEP1; eauto. i. des.
      exploit Configuration.rtc_step_future;[eapply STEPS_SRC|..]; eauto. i. des.
      exploit Configuration.opt_step_future;[eapply STEP_SRC|..]; eauto. i. des.
      exploit Configuration.rtc_step_future;[eapply STEPS_AFTER|..]; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv EVENT0. inv STEP_SRC.
      econs 2; [eauto| |auto].
      2:{ etrans; eauto. }
      eapply rtc_tau_step_behavior; eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + red in FAILURE. des.
      eapply rtc_tau_step_behavior; eauto. inv STEP_SRC.
      { eapply rtc_tau_step_behavior; eauto. eapply behaviors_failure; eauto. }
      { eapply rtc_tau_step_behavior; eauto. inv EVENT. econs 3; eauto. }
    + eapply rtc_tau_step_behavior; eauto. inv STEP.
      exploit DConfiguration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; try exact STEPS_SRC; eauto. i. des.
      inv EVENT. inv STEP_SRC. econs 3; eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      inv EVENT. inv STEP_SRC.
      { eapply rtc_tau_step_behavior; eauto. econs 3; eauto. }
      { eapply rtc_tau_step_behavior; eauto.
        econs 4; eauto. eapply rtc_tau_step_behavior; eauto. econs 3; eauto. }
    + hexploit SIM1; eauto.
      { inv EVENT; ss. }
      clear SIM1. intros SIM1.
      inv SIM1; [|done].
      eapply rtc_tau_step_behavior; eauto. inv STEP.
      exploit DConfiguration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; try exact STEPS_SRC; eauto. i. des.
      inv STEP_SRC.
      * eapply rtc_tau_step_behavior; eauto.
        eapply IHPR; [..|eauto|]; eauto.
        exploit Configuration.rtc_step_future; try exact STEPS_AFTER; eauto. i. des. auto.
      * inv EVENT. econs 4; eauto. eapply rtc_tau_step_behavior; eauto.
        exploit Configuration.step_future; try apply STEP1; eauto. s. i. des.
        eapply IHPR; eauto.
        exploit Configuration.rtc_step_future; try exact STEPS_AFTER; eauto. i. des. auto.
  - econs 5.
Qed.

Lemma tids_find
      tids ths_src ths_tgt
      tid
      (TIDS_SRC: tids = Threads.tids ths_src)
      (TIDS_TGT: tids = Threads.tids ths_tgt):
  (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
  (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
Proof.
  split; i; des.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
  - destruct (IdentSet.mem tid tids) eqn:MEM.
    + rewrite TIDS_SRC in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_src); ss.
      destruct p. destruct s. esplits; eauto.
    + rewrite TIDS_TGT in MEM.
      rewrite Threads.tids_o in MEM.
      destruct (IdentMap.find tid ths_tgt); ss.
Qed.

Lemma thread_rtc_step_rtc_step
      ths1_src sc1_src mem1_src
      sc2_src mem2_src
      tid lang_src st1_src lc1_src st2_src lc2_src
      (WF_SRC: Configuration.wf (Configuration.mk ths1_src sc1_src mem1_src))
      (FIND: IdentMap.find tid ths1_src = Some (existT _ lang_src st1_src, lc1_src))
      (STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk lang_src st2_src lc2_src sc2_src mem2_src))
      (LOCAL: Thread.consistent (Thread.mk lang_src st2_src lc2_src sc2_src mem2_src)):
  (<<STEPS: rtc Configuration.tau_step
                (Configuration.mk ths1_src sc1_src mem1_src)
                (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) sc2_src mem2_src)>>).
Proof.
  inv WF_SRC. inv WF. ss. exploit THREADS; eauto. i.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  generalize (rtc_tail STEPS). i. des.
  - inv H0. inv TSTEP.
    assert (STEP0: Configuration.step
                     MachineEvent.silent tid
                     (Configuration.mk ths1_src sc1_src mem1_src)
                     (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) sc2_src mem2_src)).
    { rewrite <- EVENT. econs; ss; eauto. }
    econs; eauto. econs; eauto.
  - inv H.
    replace (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) with ths1_src; auto.
    apply IdentMap.eq_leibniz. ii.
    rewrite -> IdentMap.gsident; auto.
Qed.

Lemma thread_failure_configuration_failure
      ths1_src sc1_src mem1_src
      tid lang_src st1_src lc1_src
      (WF_SRC: Configuration.wf (Configuration.mk ths1_src sc1_src mem1_src))
      (FIND: IdentMap.find tid ths1_src = Some (existT _ lang_src st1_src, lc1_src))
      (STEPS: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src))
  :
  Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src).
Proof.
  red in STEPS. des. destruct e2, e3.
  red. esplits.
  { refl. }
  rewrite <- EVENT_FAILURE. econs; eauto; ss.
Qed.

Lemma sim_threads_terminal_step
      (tids: Ident.t -> Prop)
      ths_src0 sc_src0 mem_src0
      ths_tgt0 sc_tgt0 mem_tgt0 w0
      ths_tgt1 sc_tgt1 mem_tgt1
      tid
      (TIDS: Threads.tids ths_src0 = Threads.tids ths_tgt0)
      (SIM: forall tid0 lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                   (IN: tids tid0),
          IdentMap.find tid0 ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid0 ths_tgt0 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          @sim_thread_wf_past lang_src lang_tgt w0 st_src lc_src sc_src0 mem_src0 st_tgt lc_tgt sc_tgt0 mem_tgt0)
      (TERMINAL: forall tid0 lang_src st_src lc_src
                        (NIN: ~ tids tid0),
          IdentMap.find tid0 ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>))
      (WF_SRC: Configuration.wf (Configuration.mk ths_src0 sc_src0 mem_src0))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0))
      (STEP_TGT: d_na_terminal_step loc_na tid (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0) (Configuration.mk ths_tgt1 sc_tgt1 mem_tgt1))
      (NTID: tids tid)
  :
    (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 sc_src0 mem_src0)>>) \/
    exists ths_src1 sc_src1 mem_src1 w1,
      (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 sc_src0 mem_src0) (Configuration.mk ths_src1 sc_src1 mem_src1)>>) /\
      (<<SIM: forall tid0 lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                     (IN: tids tid0)
                     (NEQ: tid0 <> tid),
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid0 ths_tgt1 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          @sim_thread_wf_past lang_src lang_tgt w1 st_src lc_src sc_src1 mem_src1 st_tgt lc_tgt sc_tgt1 mem_tgt1>>) /\
      (<<TERMINAL: forall tid0 lang_src st_src lc_src
                          (TID: tid0 = tid \/ ~ tids tid0),
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>)>>) /\
      (<<TIDS: Threads.tids ths_src1 = Threads.tids ths_tgt1>>)
.
Proof.
  i. inv STEP_TGT. dup STEP. inv STEP. ss.
  destruct (IdentMap.find tid ths_src0) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
  { remember (Threads.tids ths_src0) as tids0 eqn:TIDS_SRC.
    exploit tids_find; [exact TIDS_SRC|exact TIDS|..]. i. des.
    exploit x1; eauto. i. des. rewrite FIND_SRC in x. inv x. }
  dup WF_SRC. dup WF_TGT.
  inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
  exploit SIM; eauto. i.
  hexploit sim_thread_wf_past_terminal; eauto. i. des.
  { left. eapply thread_failure_configuration_failure; eauto. }
  { hexploit thread_rtc_step_rtc_step; [eapply WF_SRC0|..]; eauto.
    { ii. right. esplits; eauto. inv LOCAL_SRC. ss. }
    i. right. esplits; eauto.
    { instantiate (1:=w1).
      i. hexploit DConfiguration.terminal_step_future; eauto. i. des.
      hexploit Configuration.rtc_step_future; eauto. i. des. ss.
      inv WF0. inv WF2. ss. inv WF. inv WF0.
      exploit THREADS1; eauto. i. exploit THREADS2; eauto. i.
      erewrite IdentMap.gso in H0; auto. erewrite IdentMap.gso in H1; auto.
      hexploit SIM; eauto. i.
      eapply sim_thread_wf_past_update; eauto.
      { eapply Memory.future_future_weak; eauto. }
      { eapply Memory.future_future_weak; eauto. }
      { eapply world_messages_le_mon; eauto.
        { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
        { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. }
      }
    }
    { i. ss. des.
      { subst. erewrite IdentMap.gss in H0. dependent destruction H0; eauto. }
      { erewrite IdentMap.gso in H0; eauto.
        ii. subst. eapply TID0; eauto.
      }
    }
    { rewrite ! Threads.tids_add. f_equal; auto. }
  }
Qed.

Lemma sim_threads_terminal_steps
      ths_src0 sc_src0 mem_src0
      ths_tgt0 sc_tgt0 mem_tgt0 w0
      tids
      (STEPS_TGT: d_na_terminal_steps loc_na tids (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0))
      (WF_SRC: Configuration.wf (Configuration.mk ths_src0 sc_src0 mem_src0))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0))
      (SIM: forall tid0 lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                   (IN: List.In tid0 tids),
          IdentMap.find tid0 ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid0 ths_tgt0 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          @sim_thread_wf_past lang_src lang_tgt w0 st_src lc_src sc_src0 mem_src0 st_tgt lc_tgt sc_tgt0 mem_tgt0)
      (TERMINAL: forall tid lang_src st_src lc_src
                        (NIN: ~ List.In tid tids),
          IdentMap.find tid ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>))
      (TIDS: Threads.tids ths_src0 = Threads.tids ths_tgt0)
  :
    (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 sc_src0 mem_src0)>>) \/
    exists ths_src1 sc_src1 mem_src1,
      (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 sc_src0 mem_src0) (Configuration.mk ths_src1 sc_src1 mem_src1)>>) /\
      (<<TERMINAL: forall tid0 lang_src st_src lc_src,
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>)>>)
.
Proof.
  remember (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0) as c_tgt0.
  revert ths_src0 sc_src0 mem_src0 ths_tgt0 sc_tgt0 mem_tgt0 w0 WF_SRC WF_TGT SIM TERMINAL TIDS Heqc_tgt0.
  induction STEPS_TGT; i; subst.
  { right. esplits; eauto. }
  { destruct c2. ss.
    hexploit (@sim_threads_terminal_step (fun tid0 => List.In tid0 (tid::tids))).
    { eapply TIDS. }
    { i. eapply SIM0; eauto. }
    { i. eapply TERMINAL; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
    { ss. eauto. }
    i. des.
    { left. eauto. }
    inv STEP. hexploit DConfiguration.terminal_step_future; eauto. i. des; ss.
    hexploit Configuration.rtc_step_future; eauto. i. des; ss.
    hexploit IHSTEPS_TGT.
    { eapply WF0. }
    { eapply WF2. }
    { i. eapply SIM1; eauto. ii. subst. eauto. }
    { i. eapply TERMINAL0; [|eauto]. destruct (Ident.eq_dec tid0 tid); auto.
      right. ii. des; clarify.
    }
    { auto. }
    { auto. }
    i. des.
    { red in FAILURE. des. left. repeat red. esplits.
      { etrans; eauto. }
      { eauto. }
    }
    { right. esplits.
      { etrans; eauto. }
      i. eauto.
    }
  }
  { inv STEP. inv STEP0. ss.
    destruct (IdentMap.find tid ths_src0) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src0) as tids0 eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS|..]. i. des.
      exploit x1; eauto. i. des. rewrite FIND_SRC in x. inv x. }
    hexploit SIM0; eauto. i.
    hexploit sim_thread_wf_past_dsteps_full; eauto. i. des; ss.
    { left. eapply thread_failure_configuration_failure; eauto. }
    { left. inv EVENT. eapply thread_failure_configuration_failure; eauto.
      replace pf_src with true in *.
      2:{ inv STEPS1; inv STEP; ss. }
      repeat red. esplits; eauto.
    }
  }
Qed.

Lemma sim_threads_terminal
      ths_src0 sc_src0 mem_src0
      ths_tgt0 sc_tgt0 mem_tgt0 w0
      (STEPS_TGT: d_na_terminal_steps loc_na (IdentSet.elements (Threads.tids ths_tgt0)) (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0))
      (WF_SRC: Configuration.wf (Configuration.mk ths_src0 sc_src0 mem_src0))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0))
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src0 = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt0 = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          @sim_thread_wf_past lang_src lang_tgt w0 st_src lc_src sc_src0 mem_src0 st_tgt lc_tgt sc_tgt0 mem_tgt0)
      (TIDS: Threads.tids ths_src0 = Threads.tids ths_tgt0)
  :
    (<<FAILURE: Configuration.steps_failure (Configuration.mk ths_src0 sc_src0 mem_src0)>>) \/
    exists ths_src1 sc_src1 mem_src1,
      (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths_src0 sc_src0 mem_src0) (Configuration.mk ths_src1 sc_src1 mem_src1)>>) /\
      (<<TERMINAL: forall tid0 lang_src st_src lc_src,
          IdentMap.find tid0 ths_src1 = Some (existT _ lang_src st_src, lc_src) ->
          (<<STATE: (Language.is_terminal lang_src) st_src>>) /\ (<<THREAD: Local.is_terminal lc_src>>)>>)
.
Proof.
  eapply sim_threads_terminal_steps; eauto.
  i. exfalso. eapply NIN.
  cut (SetoidList.InA eq tid (IdentSet.elements (Threads.tids ths_src0))).
  { rewrite <- TIDS. clear. i. induction H; ss; eauto. }
  eapply IdentSet.elements_spec1. eapply LocSet.Facts.mem_2.
  rewrite Threads.tids_o. rewrite H. auto.
Qed.

Lemma sim_threads_sim
      ths_src sc0_src mem0_src
      ths_tgt sc0_tgt mem0_tgt w
      (TIDS: Threads.tids ths_src = Threads.tids ths_tgt)
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          @sim_thread_wf_past lang_src lang_tgt w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt)
  :
    sim ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt.
Proof.
  remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
  rename TIDS into TIDS_TGT.
  revert w ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt tids TIDS_SRC TIDS_TGT SIM.
  pcofix CIH. i. pfold. ii. splits.
  - (* TERMINAL CASE *)
    subst. i. eapply sim_threads_terminal; eauto.

  - (* STEP CASE *)
    i. inv STEP_TGT. dup STEP. inv STEP. ss.
    destruct (IdentMap.find tid_tgt ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite FIND_SRC in x. inv x. }
    dup WF_SRC. dup WF_TGT.
    inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
    exploit SIM0; eauto. i.
    hexploit sim_thread_wf_past_dsteps_full; eauto. i. des.
    { left. eapply thread_failure_configuration_failure; eauto. }
    { hexploit thread_rtc_step_rtc_step; [eapply WF_SRC0|..]; eauto.
      i. right. esplits.
      { eauto. }
      { econs 1. }
      { subst. econs. }
      { right. esplits.
        { refl. }
        { right. eapply CIH; ss.
          { rewrite ! Threads.tids_add. f_equal; eauto. }
          { i. rewrite IdentMap.gsspec in H0. rewrite IdentMap.gsspec in H1. des_ifs.
            { inv H0. eapply inj_pair2 in H2. eapply inj_pair2 in H4. subst. eauto. }
            { eapply DConfiguration.step_future in STEP0; eauto. des. ss.
              eapply Configuration.rtc_step_future in H; eauto. des. ss.
              hexploit SIM0; eauto. i. inv WF0. inv WF2. ss.
              eapply sim_thread_wf_past_update; eauto.
              { eapply Memory.future_future_weak; eauto. }
              { eapply Memory.future_future_weak; eauto. }
              { eapply world_messages_le_mon; eauto.
                { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
                { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. }
              }
              { inv WF. eapply THREADS1. erewrite IdentMap.gso; eauto. }
              { inv WF0. eapply THREADS1. erewrite IdentMap.gso; eauto. }
              { red in SIM1. des. eauto. }
              { red in SIM1. des. eauto. }
            }
          }
        }
      }
    }
    { right.
      assert (STEP_SRC: Configuration.step
                          (ThreadEvent.get_machine_event e_src) tid_tgt
                          (Configuration.mk ths_src sc0_src mem0_src)
                          (Configuration.mk
                             (IdentMap.add tid_tgt (existT _ lang_src st_src2, lc_src2) ths_src)
                             sc_src2 mem_src2)).
      { econs; eauto. }
      hexploit Configuration.step_future; eauto. i. des.
      hexploit DConfiguration.step_future; eauto. i. des. ss.
      esplits.
      { refl. }
      { econs 2. eauto. }
      { eauto. }
      red in CONT. des.
      { left. eapply thread_failure_configuration_failure; eauto.
        erewrite IdentMap.gss. eauto.
      }
      { hexploit thread_rtc_step_rtc_step; [eapply WF2|..]; eauto.
        { erewrite IdentMap.gss. eauto. }
        i. des.
        hexploit Configuration.rtc_step_future; eauto. i. des.
        right. esplits.
        { eauto. }
        right. eapply CIH; ss.
        { rewrite IdentMap.add_add_eq.
          rewrite ! Threads.tids_add. f_equal; eauto. }
        { i. rewrite ! IdentMap.gsspec in H0. rewrite IdentMap.gsspec in H1. des_ifs.
          { inv H0. eapply inj_pair2 in H2. eapply inj_pair2 in H4. subst. eauto. }
          { hexploit SIM0; eauto. i. inv WF0. inv WF1. ss.
            eapply sim_thread_wf_past_update; eauto.
            { eapply Memory.future_future_weak; eauto. etrans; eauto. }
            { eapply Memory.future_future_weak; eauto. }
            { eapply world_messages_le_mon; eauto.
              { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
              { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. }
            }
            { inv WF0. eapply THREADS1. erewrite ! IdentMap.gso; eauto. }
            { inv WF. eapply THREADS1. erewrite IdentMap.gso; eauto. }
            { red in SIM1. des. eauto. }
            { red in SIM1. des. eauto. }
            { eapply CLOSEDFUTURE; eauto; ss. ii. subst.
              inv EVENT. intuition.
            }
          }
        }
      }
    }
    Unshelve. all: ss; eauto.
Qed.

Lemma local_init_wf
  :
    Local.wf Local.init Memory.init.
Proof.
  econs; eauto; ss.
  { eapply TView.bot_wf. }
  { eapply TView.bot_closed. }
  { eapply Memory.bot_le. }
  { eapply Memory.bot_finite. }
Qed.

Lemma sim_init (s_src s_tgt: Threads.syntax) (w_init: world)
      (SIM: forall tid,
          option_rel (fun '(existT _ lang_src st_src) '(existT _ lang_tgt st_tgt) =>
                        @sim_thread world world_messages_le sim_memory sim_timemap loc_na
                                    lang_src lang_tgt false w_init
                                    (lang_src.(Language.init) st_src) Local.init TimeMap.bot Memory.init
                                    (lang_tgt.(Language.init) st_tgt) Local.init TimeMap.bot Memory.init) (IdentMap.find tid s_src) (IdentMap.find tid s_tgt))
      (MEM: sim_memory w_init Memory.init Memory.init)
      (SC: sim_timemap w_init TimeMap.bot TimeMap.bot)
  :
    delayed_na_behaviors loc_na (Configuration.init s_tgt) <2=
    behaviors Configuration.step (Configuration.init s_src).
Proof.
  destruct (classic (exists tid lang syn,
                        (<<FIND: IdentMap.find tid s_src = Some (existT _ lang syn)>>) /\
                        (<<FAILURE: Thread.steps_failure (Thread.mk lang (lang.(Language.init) syn) Local.init TimeMap.bot Memory.init)>>))) as [?|NFAILURE].
  { des. red in FAILURE. des. destruct e2, e3. i. econs 3.
    rewrite <- EVENT_FAILURE. econs; eauto; ss.
    unfold Threads.init. rewrite IdentMap.Facts.map_o.
    setoid_rewrite FIND. ss.
  }
  eapply sim_adequacy.
  { eapply Configuration.init_wf. }
  { eapply Configuration.init_wf. }
  { eapply sim_threads_sim.
    { eapply IdentSet.ext. i. specialize (SIM i). ss.
      rewrite Threads.tids_o. rewrite Threads.tids_o. unfold Threads.init.
      rewrite ! IdentMap.Facts.map_o in *. unfold option_map in *. des_ifs.
      { setoid_rewrite Heq in SIM. setoid_rewrite Heq0 in SIM. ss. }
      { setoid_rewrite Heq in SIM. setoid_rewrite Heq0 in SIM. ss. }
    }
    { i. specialize (SIM tid). unfold Threads.init in *.
      rewrite IdentMap.Facts.map_o in *. unfold option_map in *. des_ifs.
      dependent destruction H. dependent destruction H1.
      setoid_rewrite Heq in SIM. setoid_rewrite Heq0 in SIM. ss.
      des_ifs. ss. red. esplits.
      { red. esplits; eauto.
        { eapply local_init_wf. }
        { eapply local_init_wf. }
        { eapply Memory.closed_timemap_bot. eapply Memory.init_closed. }
        { eapply Memory.closed_timemap_bot. eapply Memory.init_closed. }
        { eapply Memory.init_closed. }
        { eapply Memory.init_closed. }
      }
      { refl. }
      { refl. }
      { refl. }
      { refl. }
      { refl. }
      { refl. }
      { ii. right. esplits; [refl|..]. ss. }
      { eapply Local.bot_promise_consistent; eauto. }
      { ii. eapply NFAILURE; eauto. }
      { eapply local_init_wf. }
      { eapply local_init_wf. }
      { eapply Memory.closed_timemap_bot. eapply Memory.init_closed. }
      { eapply Memory.closed_timemap_bot. eapply Memory.init_closed. }
      { eapply Memory.init_closed. }
      { eapply Memory.init_closed. }
      { auto. }
      { auto. }
    }
  }
Qed.

End WORLD.
#[export] Hint Resolve _sim_thread_mon: paco.
