Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
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

Require Import gSimAux.
Require Import gSimulation.
Require Import Pred.
Require Import Delayed.
Require Import LowerMemory.
Require Import DelayedStep.
Require Import DelayedSimulation.

Set Implicit Arguments.



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

  Lemma dstep_rtc_all_step lang e th0 th1
        (STEP: dstep e th0 th1)
    :
      rtc (@Thread.all_step lang) th0 th1.
  Proof.
    inv STEP. etrans.
    { eapply rtc_implies; [|eapply PROMISES].
      i. inv H. inv TSTEP. econs; eauto.
    }
    etrans.
    { eapply rtc_implies; [|eapply LOWERS].
      i. inv H. inv TSTEP. econs; eauto. econs; eauto.
    }
    econs 2; [|refl]. econs; eauto. econs; eauto.
  Qed.

  Lemma rtc_tau_dstep_rtc_all_step lang th0 th1
        (STEPS: rtc (tau (@dstep lang)) th0 th1)
    :
      rtc (@Thread.all_step lang) th0 th1.
  Proof.
    induction STEPS.
    { refl. }
    etrans; [|eauto]. inv H.
    eapply dstep_rtc_all_step; eauto.
  Qed.

  Lemma dsteps_rtc_all_step lang e th0 th1
        (STEPS: dsteps e th0 th1)
    :
      rtc (@Thread.all_step lang) th0 th1.
  Proof.
    inv STEPS.
    { etrans.
      { eapply rtc_tau_dstep_rtc_all_step; eauto. }
      { eapply rtc_implies; [|eapply PROMISES].
        i. inv H. inv TSTEP. econs; eauto.
      }
    }
    { etrans.
      { eapply rtc_tau_dstep_rtc_all_step; eauto. }
      { eapply dstep_rtc_all_step; eauto. }
    }
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
          inv H. inv TSTEP. econs; eauto. econs; eauto.
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
      i. inv H. inv TSTEP. econs; eauto. econs; eauto.
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
        eapply rtc_tau_dstep_rtc_all_step in STEP_TGT.
        hexploit Thread.rtc_all_step_future; [eapply TSTEP|..]; eauto. i. des; ss.
        hexploit rtc_all_step_promise_consistent; [eapply STEP_TGT|..]; eauto.
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
      pose proof (rtc_tau_dstep_rtc_all_step DSTEPS) as DSTEPS'.
      hexploit Thread.rtc_all_step_future; [eapply DSTEPS'|..]; eauto. i. des; ss.
      hexploit rtc_all_step_promise_consistent.
      { eapply rtc_implies; [|eapply PROMISES]. i.
        inv H. inv TSTEP. econs; eauto.
      }
      all: eauto. intros CONS_TGT1.
      hexploit rtc_all_step_promise_consistent.
      { eapply rtc_tau_dstep_rtc_all_step. eapply DSTEPS. }
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
          { i. hexploit unchangable_rtc_all_step_increase; [eapply DSTEPS'|..]; eauto. }
        }
      }
    }
    { dup SIM. red in SIM. des.
      pose proof (rtc_tau_dstep_rtc_all_step DSTEPS) as DSTEPS'.
      pose proof (dstep_rtc_all_step DSTEP) as DSTEP'.
      hexploit Thread.rtc_all_step_future; [eapply DSTEPS'|..]; eauto. i. des; ss.
      hexploit rtc_all_step_promise_consistent; [eapply DSTEP'|..]; eauto. intros CONS_TGT1.
      hexploit rtc_all_step_promise_consistent; [eapply DSTEPS'|..]; eauto. intros CONS_TGT0.
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
          { i. hexploit unchangable_rtc_all_step_increase; [eapply DSTEPS'|..]; eauto. }
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

  Lemma delayed_consistent_promise_consistent lang (th: Thread.t lang)
        (CONSISTENT: delayed_consistent th)
        (MEM: Memory.closed th.(Thread.memory))
        (LOCAL: Local.wf th.(Thread.local) th.(Thread.memory))
        (SC: Memory.closed_timemap th.(Thread.sc) th.(Thread.memory))
    :
      Local.promise_consistent th.(Thread.local).
  Proof.
    hexploit Memory.cap_exists; eauto. i. des.
    hexploit Local.cap_wf; eauto. i.
    hexploit Memory.cap_closed_timemap; eauto. i.
    hexploit Memory.cap_closed; eauto. i.
    exploit CONSISTENT; eauto. i. des.
    { pose proof (dsteps_rtc_all_step DSTEPS) as STEPS.
      eapply rtc_all_step_promise_consistent in STEPS; eauto; ss.
      inv DSTEPS; ss. inv DSTEP. inv STEP_RELEASE; inv STEP; ss.
      inv LOCAL0; ss; inv LOCAL1; ss.
    }
    { pose proof (dsteps_rtc_all_step DSTEPS) as STEPS.
      eapply rtc_all_step_promise_consistent in STEPS; eauto; ss.
      eapply Local.bot_promise_consistent in PROMISES; eauto.
    }
  Qed.

  Lemma sim_thread_wf_terminal
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt
        (SIM: sim_thread_wf false w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt)
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
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)
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
      (* (<<CLOSEDFUTURE: closed_future_tview loc_na lc_tgt.(Local.tview) mem_tgt' mem_tgt>>) /\ *)
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
    exploit FUTURE; eauto.
    { admit. }
    i. des.
    { left. eapply steps_steps_failure; eauto. }
    inv SIM0; ss. right. esplits; eauto.
    hexploit Thread.rtc_tau_step_future; eauto. i. des; ss.
    red. esplits; eauto.
  Admitted.

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
    { destruct e2. subst.
      hexploit sim_thread_wf_dsteps; eauto.
      { eapply Local.bot_promise_consistent in PROMISES; eauto. }
      i. des.
      { left. eapply steps_steps_failure; eauto. }
      { inv EVENT. red in SIM1. des.
        assert (STEPS_SRC: rtc (@Thread.tau_step _) (Thread.mk _ st_src lc_src sc_src mem1) (Thread.mk _ st_src3 lc_src3 sc_src3 mem_src3)).
        { etrans; eauto. etrans; eauto. etrans; [|eauto]. inv STEPS1.
          { refl. }
          { econs 2; [|refl]. econs; eauto. econs; eauto. }
        }
        punfold SIM2. exploit SIM2; eauto.
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

  Lemma sim_thread_wf_past_terminal
        w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt
        (SIM: sim_thread_wf_past w0 st_src0 lc_src0 sc_src0 mem_src0 st_tgt lc_tgt sc_tgt mem_tgt)
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
      (<<WORLD: world_messages_le (unchangable mem_src0 lc_src0.(Local.promises)) (unchangable mem_tgt lc_tgt.(Local.promises)) w0 w1>>)
  .
  Proof.
    hexploit sim_thread_wf_past_future; eauto. i. des.
    { left. eauto. }
    hexploit sim_thread_wf_terminal; eauto. i. des.
    { left. eapply steps_steps_failure; eauto. }
    right. esplits.
    { etrans; eauto. }
    { eauto. }
    { eauto. }
    { eauto. }
  Qed.

End LANG.

Section Simulation.
  Definition SIM :=
    forall (w: world) (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim
             (sim: SIM)
             (w0: world)
             (ths_src0:Threads.t) (sc_src0:TimeMap.t) (mem_src0:Memory.t)
             (ths_tgt0:Threads.t) (sc_tgt0:TimeMap.t) (mem_tgt0:Memory.t)
    : Prop :=
    forall (SC0: sim_timemap w0 sc_src0 sc_tgt0)
           (MEMORY0: sim_memory w0 mem_src0 mem_tgt0)
           (WF_SRC: Configuration.wf (Configuration.mk ths_src0 sc_src0 mem_src0))
           (WF_TGT: Configuration.wf (Configuration.mk ths_tgt0 sc_tgt0 mem_tgt0)),
      (<<TERMINAL:
        forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
          (<<FAILURE: Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src)>>) \/
            exists ths2_src sc2_src mem2_src w2,
              (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>>) /\
              (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
              (<<MEMORY: sim_memory w2 views1 mem2_src mem1_tgt>>) /\
              (<<TERMINAL_SRC: Threads.is_terminal ths2_src>>)>>) /\
        (<<STEP:
          forall e_tgt tid_tgt ths3_tgt sc3_tgt mem3_tgt views3
                 (STEP_TGT: JConfiguration.step e_tgt tid_tgt (Configuration.mk ths1_tgt sc1_tgt mem1_tgt) (Configuration.mk ths3_tgt sc3_tgt mem3_tgt) views1 views3),
            (<<FAILURE: Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src)>>) \/
              exists e_src tid_src ths2_src sc2_src mem2_src ths3_src sc3_src mem3_src ths4_src sc4_src mem4_src w3,
                (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>>) /\
                  (<<STEP_SRC: Configuration.opt_step e_src tid_src (Configuration.mk ths2_src sc2_src mem2_src) (Configuration.mk ths3_src sc3_src mem3_src)>>) /\
                  (<<STEPS_AFTER: rtc Configuration.tau_step (Configuration.mk ths3_src sc3_src mem3_src) (Configuration.mk ths4_src sc4_src mem4_src)>>) /\
                  (<<EVENT: machine_event_le e_tgt e_src>>) /\
                  (<<SC3: sim_timemap w3 sc4_src sc3_tgt>>) /\
                  (<<MEMORY3: sim_memory w3 views3 mem4_src mem3_tgt>>) /\
                  (<<SIM: sim w3 ths4_src sc4_src mem4_src ths3_tgt sc3_tgt mem3_tgt views3>>)>>).

  Lemma _sim_mon: monotone8 _sim.
  Proof.
    ii. exploit IN; try apply SC1; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco8 _sim bot8.
End Simulation.
Hint Resolve _sim_mon: paco.


Lemma sim_adequacy
      ths_src sc_src mem_src
      ths_mid sc_mid mem_mid
      ths_tgt sc_tgt mem_tgt w views
      (WF_SRC: Configuration.wf (Configuration.mk ths_src sc_src mem_src))
      (WF_MID: JConfiguration.wf views (Configuration.mk ths_mid sc_mid mem_mid))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (SC: sim_timemap w sc_src sc_mid)
      (MEMORY: sim_memory w views mem_src mem_mid)
      (SIM: sim w ths_src sc_src mem_src ths_mid sc_mid mem_mid views)
      (JSIM: JSim.sim_configuration
               views
               (Configuration.mk ths_mid sc_mid mem_mid)
               (Configuration.mk ths_tgt sc_tgt mem_tgt)):
  behaviors Configuration.step (Configuration.mk ths_tgt sc_tgt mem_tgt) <2=
  behaviors Configuration.step (Configuration.mk ths_src sc_src mem_src).
Proof.
  s. i.
  revert w WF_SRC WF_MID WF_TGT SC MEMORY SIM JSIM.
  revert ths_src sc_src mem_src.
  revert ths_mid sc_mid mem_mid.
  remember (Configuration.mk ths_tgt sc_tgt mem_tgt).
  revert views ths_tgt sc_tgt mem_tgt Heqt.
  induction PR; i; subst.
  - punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit JSim.sim_configuration_terminal; eauto. i.
    exploit TERMINAL0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + eapply rtc_tau_step_behavior; eauto.
      econs 1. eauto.
  - destruct c2.
    hexploit JSim.step_sim_configuration; eauto. i. des. destruct c_src1.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP1; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + inv SIM2; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try exact STEP; eauto. i. des.
      exploit Configuration.rtc_step_future;[eapply STEPS_SRC|..]; eauto. i. des.
      exploit Configuration.opt_step_future;[eapply STEP_SRC|..]; eauto. i. des.
      exploit Configuration.rtc_step_future;[eapply STEPS_AFTER|..]; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv EVENT0. inv STEP_SRC.
      econs 2; [eauto| |auto].
      2:{ etrans; eauto. }
      eapply rtc_tau_step_behavior; eauto.
      exploit JConfiguration.step_future; eauto. i. des.
      eapply IHPR; eauto.
  - destruct c2.
    hexploit JSim.step_sim_configuration; eauto. i. des. destruct c_src1.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP1; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM2; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try exact STEP; eauto. i. des.
      exploit JConfiguration.step_future; eauto. i. des.
      exploit Configuration.rtc_step_future; try exact STEPS_SRC; eauto. i. des.
      inv EVENT. inv STEP_SRC. econs 3; eauto.
  - destruct c2.
    hexploit JSim.step_sim_configuration; eauto. i. des. destruct c_src1.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    hexploit STEP1; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM2; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try exact STEP; eauto. i. des.
      exploit JConfiguration.step_future; eauto. i. des.
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

Lemma sim_thread_sim
      ths_src sc0_src mem0_src
      ths_tgt sc0_tgt mem0_tgt w views
      (TIDS: Threads.tids ths_src = Threads.tids ths_tgt)
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          @sim_thread_past lang_src lang_tgt w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt (views, finalized (Configuration.mk ths_tgt sc0_tgt mem0_tgt)))
  :
    sim w ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt views.
Proof.
  remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
  rename TIDS into TIDS_TGT.
  revert w views ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt tids TIDS_SRC TIDS_TGT SIM.
  pcofix CIH. i. pfold. ii. splits.
  - (* TERMINAL CASE *)
    assert (NOTIN: forall tid lang_src st_src lc_src
                     (FIND: IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src))
                     (TID: ~ List.In tid (IdentSet.elements tids)),
               Language.is_terminal _ st_src /\ Local.is_terminal lc_src).
    { i. destruct (IdentSet.mem tid tids) eqn:MEM.
      - exfalso. apply TID. rewrite IdentSet.mem_spec in MEM.
        rewrite <- IdentSet.elements_spec1 in MEM.
        clear - MEM. induction MEM; [econs 1|econs 2]; auto.
      - rewrite TIDS_SRC in MEM. rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src) eqn:IFIND; [inv MEM|]. ss. }
    assert (IN: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
                  (TID: List.In tid (IdentSet.elements tids)),
               IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
               IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
               @sim_thread_past lang_src lang_tgt w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt (views, finalized (Configuration.mk ths_tgt sc1_tgt mem1_tgt))).
    { i. hexploit SIM0; eauto. i. des. esplits.
      eapply sim_thread_future; eauto; try refl. }
    assert (WORLD0: forall tid st_src lc_src st_tgt lc_tgt
                           (TID: List.In tid (IdentSet.elements tids))
                           (FINDSRC: IdentMap.find tid ths_src = Some (st_src, lc_src))
                           (FINDTGT: IdentMap.find tid ths_tgt = Some (st_tgt, lc_tgt)),
               world_messages_le (Messages.of_memory lc_src.(Local.promises)) (Messages.of_memory lc_tgt.(Local.promises)) w w1).
    { i. eapply WORLD; eauto. }
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto. }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto. }
    revert NOTIN IN TIDS_MEM NODUP.
    move tids at top. clear SIM0 WORLD. clear FINSRC. revert_until CIH.
    induction (IdentSet.elements tids); i.
    { right. esplits; eauto; try refl. ii. exploit NOTIN; eauto. }
    destruct (IdentMap.find a ths_src) as [[[lang_src st_src] lc_src]|] eqn:ASRC;
      destruct (IdentMap.find a ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:ATGT; cycle 1.
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x0; eauto. i. des. rewrite ATGT in x. inv x. }
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite ASRC in x. inv x. }
    { exploit IHl; [exact TIDS_SRC|exact TIDS_TGT|exact SC1|exact MEMORY1|..]; eauto; i.
      - refl.
      - eapply NOTIN; eauto. ii. inv H; ss. congr.
      - exploit IN; eauto.
        { econs 2; eauto. }
        { i. des. esplits; eauto. eapply sim_thread_future; eauto; try refl.
          eapply WORLD0; eauto. econs 2; eauto.  }
      - eapply TIDS_MEM; eauto. econs 2; eauto.
      - inv NODUP. ss.
    }
    generalize WF_SRC. intro X. inv X. ss. inv WF. exploit THREADS; eauto. i.
    generalize WF_TGT. intro X. inv X. inv WF.
    ss. inv WF0. exploit THREADS0; eauto. i.
    exploit (IN a); eauto. i. des.
    hexploit sim_thread_future; eauto.
    { eapply Memory.future_future_weak; eauto. }
    { eapply Memory.future_future_weak; eauto. }
    i. hexploit sim_thread_terminal; eauto.
    { i. eapply finalized_unchangable in PR; eauto. }
    { exploit TERMINAL_TGT; eauto. i. des. eauto. }
    { exploit TERMINAL_TGT; eauto. i. des. inv THREAD. eauto. }
    i. des.
    + (* failure *)
      left. unfold Thread.steps_failure in FAILURE. des.
      exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
      exploit Thread.step_future; try exact STEP_FAILURE; eauto. s. i. des.
      unfold Configuration.steps_failure.
      destruct e3. ss.
      esplits; [refl|]. rewrite <- EVENT_FAILURE. econs; eauto. destruct e; ss.
    + (* non-failure *)
      exploit thread_rtc_step_rtc_step; [eauto|eauto|exact STEPS|..].
      { ii. right. esplits; [refl|..]. ss. } i. des; auto.
      exploit Configuration.rtc_step_future; try eapply x3; eauto. s. i. des.
      exploit IHl; [| |exact SC2|exact MEMORY|..]; try exact WF2; try exact WF_TGT;
        try exact SC_FUTURE_TGT; try exact MEM_FUTURE_TGT;
          try (etrans; [exact SC_FUTURE_SRC|exact SC_FUTURE]);
          try (etrans; [exact MEM_FUTURE_SRC|exact MEM_FUTURE]); eauto; i.
      { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
      { refl. }
      { rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
        - subst. Configuration.simplify.
        - eapply NOTIN; eauto. ii. des; ss. subst. ss. }
      { rewrite IdentMap.gsspec in H0. revert H0. condtac; ss; i.
        - subst. inv NODUP. congr.
        - exploit IN; eauto. i. des.
          esplits. eapply sim_thread_future; eauto; try refl.
          etrans.
          { eapply WORLD0; eauto. }
          { eapply world_messages_le_mon; [eauto|..].
            { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
            { destruct lc_tgt0, lc_tgt. eapply other_promise_unchangable; eauto. eapply WF_TGT. }
          }
      }
      { inv NODUP. ss. }
      des.
      * left.
        unfold Configuration.steps_failure in *. des. esplits; [|eauto].
        etrans; eauto.
      * right. esplits; cycle 1; eauto.
        { etrans; eauto. }

  - (* STEP CASE *)
    i. dup STEP_TGT. inv STEP_TGT. destruct e2. ss.
    destruct (classic (Configuration.steps_failure (Configuration.mk ths_src sc1_src mem1_src))); auto.
    destruct (IdentMap.find tid_tgt ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite FIND_SRC in x. inv x. }
    dup WF_SRC. dup WF_TGT.
    inv WF_SRC. inv WF_TGT. inv WF. inv WF0. inv WF. ss.
    exploit SIM0; eauto. i. des.
    exploit sim_thread_future; eauto using Memory.future_future_weak. i.
    hexploit sim_thread_plus_step; try exact STEPS;
      try apply x1; eauto using Memory.future_future_weak; ss.
    { destruct (classic (ThreadEvent.get_machine_event e = MachineEvent.failure)).
      - inv STEP. inv STEP0; inv STEP; ss. inv LOCAL; ss; inv LOCAL0; ss.
      - exploit JThread.tau_steps_future; eauto. s. i. des.
        exploit JThread.step_future; eauto. s. i. des.
        hexploit JThread.consistent_thread_consistent; eauto.
        i. hexploit consistent_promise_consistent; eauto.
    }
    { i. eapply finalized_unchangable in PR; eauto. }
    s. i. des.
    + left.
      unfold Thread.steps_failure in FAILURE. des.
      unfold Configuration.steps_failure.
      destruct e3. ss.
      esplits; eauto. rewrite <- EVENT_FAILURE. econs; eauto. destruct e; ss.
    + assert (OPTSTEP: Configuration.opt_step
                         (ThreadEvent.get_machine_event e_src) tid_tgt
                         (Configuration.mk ths_src sc1_src mem1_src)
                         (Configuration.mk (IdentMap.add tid_tgt (existT _ lang_src st3_src, lc3_src) ths_src) sc3_src mem3_src)).
      { inv STEP0.
        { generalize (rtc_tail STEPS0). intro X. des.
          - inv X0. inv TSTEP. ss.
            inv EVENT. rewrite <- EVENT0.
            + econs 2. econs; eauto. i.
              unguard. des; clarify; auto.
              eapply sim_thread_consistent; eauto.
          - ss. inv X. rewrite IdentMap.gsident; auto.
        }
        { econs. econs; eauto. i.
          unguard. des; clarify; auto.
          eapply sim_thread_consistent; eauto.
        }
      }
      exploit Configuration.opt_step_future; eauto.
      i. ss. des.
      eapply thread_rtc_step_rtc_step in STEPS_AFTER; eauto; cycle 1.
      { apply IdentMap.gss. }
      { eapply sim_thread_consistent; eauto. }
      exploit Configuration.rtc_step_future; eauto. i. des.
      exploit JConfiguration.step_future; eauto. i. ss. des.
      right. esplits; eauto. right. eapply CIH; ss.
      { rewrite IdentMap.add_add_eq.
        rewrite Threads.tids_add. rewrite Threads.tids_add.
        f_equal. auto.
      }
      { i. apply sim_thread_sim_thread_past in SIM1; auto.
        2:{ eapply sim_thread_consistent; eauto. }
        Configuration.simplify.
        { esplits; eauto. eapply sim_thread_future; eauto; try refl.
          i. ss. inv WF_TGT0.
          eapply JConfiguration.step_configuration_step in STEP_TGT0. des.
          { eapply step_finalized; eauto. }
          { eapply step_committed_finalized; eauto.
            ss. apply IdentMap.gss. }
        }
        { exploit SIM0; eauto. i. des. esplits; eauto.
          eapply sim_thread_future; eauto.
          { eapply Memory.future_future_weak. etrans; eauto. etrans; eauto. }
          { eapply Memory.future_future_weak. etrans; eauto. }
          { etrans.
            { eapply WORLD; eauto. }
            { eapply world_messages_le_mon; [eauto|..].
              { destruct lc_src0, lc_src. eapply other_promise_unchangable; eauto. }
              { destruct lc_tgt, lc1. eapply other_promise_unchangable; eauto. eapply WF_TGT0. }
            }
          }
          { etrans; eauto. }
          { eapply JConfiguration.step_configuration_step in STEP_TGT0. inv WF_TGT0.
            i. eapply step_finalized; eauto. }
        }
      }
Qed.

End WORLD.
Hint Resolve _sim_thread_mon: paco.
