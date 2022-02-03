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

Require Import JoinedView.
Require Import gSimAux.
Require Import gSimulation.
Require Import Delayed.
Require Import LowerMemory.

Set Implicit Arguments.



Section WORLD.

Variable world: Type.

Variable world_messages_le: Messages.t -> world -> world -> Prop.
Context `{world_messages_le_PreOrder: forall msgs, PreOrder (world_messages_le msgs)}.

Hypothesis world_messages_le_mon:
  forall msgs0 msgs1 w0 w1
         (LE: world_messages_le msgs1 w0 w1)
         (MSGS: msgs0 <4= msgs1),
    world_messages_le msgs0 w0 w1.

Variable sim_memory: forall (w: world) (mem_src mem_tgt:Memory.t), Prop.
Variable sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop.


Section SimulationThread.
  Definition SIM_THREAD :=
    forall (lang_src lang_tgt:language)
           (b: bool) (w: world)
           (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
           (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim_thread_step
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             (w0: world)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt :=
    forall pf_tgt e_tgt st3_tgt lc3_tgt sc3_tgt mem3_tgt
           (STEP_TGT: Thread.step pf_tgt e_tgt
                                   (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                                   (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
           (CONS_TGT: Local.promise_consistent lc3_tgt),
      (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
      exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src st4_src lc4_src sc4_src mem4_src w3 b1,
        (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
        (<<STEPS: rtc (@Thread.tau_step _)
                      (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                      (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
        (<<STEP_SRC: Thread.opt_step e_src
                                     (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                                     (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
        (<<STEPS_AFTER: rtc (@Thread.tau_step _)
                      (Thread.mk _ st3_src lc3_src sc3_src mem3_src)
                      (Thread.mk _ st4_src lc4_src sc4_src mem4_src)>>) /\
        (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
        (<<RELEASE: release_event e_tgt -> b1 = false>>) /\
        (<<SC3: b1 = false -> sim_timemap w3 sc4_src sc3_tgt>>) /\
        (<<MEMORY3: b1 = false -> sim_memory w3 mem4_src mem3_tgt>>) /\
        (<<SIM: sim_thread b1 w3 st4_src lc4_src sc4_src mem4_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
        (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w0 w3>>)
  .

  Definition sim_memory_future
             (b0: bool)
             (prom_src prom_tgt: Memory.t)
             (mem0_src mem1_src mem0_tgt mem1_tgt: Memory.t)
             (sc0_src sc1_src sc0_tgt sc1_tgt: TimeMap.t)
             (w0 w1: world): Prop :=
    if b0
    then
      (<<MEMSRC: mem1_src = mem0_src>>) /\
      (<<MEMTGT: mem1_tgt = mem0_tgt>>) /\
      (<<SCSRC: sc1_src = sc0_src>>) /\
      (<<SCTGT: sc1_tgt = sc0_tgt>>) /\
      (<<WORLD: w1 = w0>>)
    else
      (<<MEMSRC: Memory.future_weak mem0_src mem1_src>>) /\
      (<<MEMTGT: Memory.future_weak mem0_tgt mem1_tgt>>) /\
      (<<SCSRC: TimeMap.le sc0_src sc1_src>>) /\
      (<<SCTGT: TimeMap.le sc0_tgt sc1_tgt>>) /\
      (<<WORLD: world_messages_le (Messages.of_memory prom_src) w0 w1>>)
  .

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (lang_src lang_tgt:language)
             (b0: bool) (w0: world)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    (<<FUTURE: forall w1 sc1_src mem1_src
                      sc1_tgt mem1_tgt views1 fin1
                      (SC: b0 = false -> sim_timemap w1 sc1_src sc1_tgt)
                      (MEMORY: b0 = false -> sim_memory w1 mem1_src mem1_tgt)
                      (WF_SRC: Local.wf lc1_src mem1_src)
                      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
                      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
                      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
                      (MEM_SRC: Memory.closed mem1_src)
                      (MEM_TGT: Memory.closed mem1_tgt)
                      (CONS_TGT: Local.promise_consistent lc1_tgt)
                      (FUTURE: sim_memory_future
                                 b0
                                 (lc1_src.(Local.promises)) (lc1_tgt.(Local.promises))
                                 mem0_src mem1_src mem0_tgt mem1_tgt
                                 sc0_src sc1_src sc0_tgt sc1_tgt
                                 w0 w1),
        (<<TERMINAL:
           forall
             (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
             (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
             exists st2_src lc2_src sc2_src mem2_src w2,
               (<<STEPS: rtc (@Thread.tau_step _)
                             (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
               (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
               (<<MEMORY: sim_memory w2 mem2_src mem1_tgt>>) /\
               (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
               (<<LOCAL: lc1_tgt.(Local.promises) = Memory.bot -> lc2_src.(Local.promises) = Memory.bot>>) /\
               (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w2>>)>>) /\
        (<<PROMISES:
           forall (BOOL: b0 = true)
                  (PROMISES_TGT: (Local.promises lc1_tgt) = Memory.bot),
             (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc0_src mem0_src)>>) \/
             exists st2_src lc2_src sc2_src mem2_src,
               (<<STEPS: rtc (@Thread.tau_step _)
                             (Thread.mk _ st1_src lc1_src sc0_src mem0_src)
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
               (<<PROMISES_SRC: (Local.promises lc2_src) = Memory.bot>>)>>) /\
        (<<STEP: _sim_thread_step _ _ (@sim_thread lang_src lang_tgt)
                                  w1
                                  st1_src lc1_src sc1_src mem1_src
                                  st1_tgt lc1_tgt sc1_tgt mem1_tgt>>)>>) /\
    (<<CAP: forall (BOOL: b0 = false)
                   (MEMORY: sim_memory w0 mem0_src mem0_tgt)
                   (WF_SRC: Local.wf lc1_src mem0_src)
                   (WF_TGT: Local.wf lc1_tgt mem0_tgt)
                   (SC_SRC: Memory.closed_timemap sc0_src mem0_src)
                   (SC_TGT: Memory.closed_timemap sc0_tgt mem0_tgt)
                   (MEM_SRC: Memory.closed mem0_src)
                   (MEM_TGT: Memory.closed mem0_tgt)
                   (CONS_TGT: Local.promise_consistent lc1_tgt),
        (<<CAP: forall cap_src cap_tgt
                       (CAPSRC: Memory.cap mem0_src cap_src)
                       (CAPTGT: Memory.cap mem0_tgt cap_tgt),
            exists w3,
              (<<SC3: sim_timemap w3 sc0_src sc0_tgt>>) /\
              (<<MEMORY3: sim_memory w3 cap_src cap_tgt>>) /\
              (<<SIM: sim_thread _ _ true w3 st1_src lc1_src sc0_src cap_src st1_tgt lc1_tgt sc0_tgt cap_tgt>>)>>)>>)
  .

  Lemma _sim_thread_mon: monotone14 _sim_thread.
  Proof.
    ii. destruct x13. red in IN. des. red. splits; auto.
    ii. exploit FUTURE; eauto. i. des. splits; auto.
    { ii. exploit STEP; eauto. i. des; eauto.
      right. esplits; eauto. }
    { ii. exploit CAP; eauto. i. des. esplits; eauto. }
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco14 _sim_thread bot14.

  Lemma sim_thread_mon
        (lang_src lang_tgt:language)
        (sim_terminal1 sim_terminal2: SIM_TERMINAL lang_src lang_tgt)
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <11= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. destruct x24. punfold PR. pfold.
    red in PR. red. des. splits; auto.
    { ii. exploit FUTURE; eauto. i. des. splits; auto.
      { i. exploit TERMINAL; eauto. i. des; eauto.
        right. esplits; eauto. }
      { ii. exploit STEP; eauto. i. des; eauto.
        inv SIM0; [|done].
        right. esplits; eauto. }
    }
    { i. exploit CAP; eauto. i. des. esplits; eauto.
      inv SIM0; [|done]. right. auto. }
  Qed.
End SimulationThread.
Hint Resolve _sim_thread_mon: paco.

Definition sim_thread_past lang_src lang_tgt sim_terminal (b: bool) w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt '(views, fin) :=
  if b
  then sim_thread sim_terminal true w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt (views, fin)
  else exists w' sc_src' mem_src' sc_tgt' mem_tgt' views' fin',
      (<<SIM: @sim_thread lang_src lang_tgt sim_terminal false w' st_src lc_src sc_src' mem_src' st_tgt lc_tgt sc_tgt' mem_tgt' (views', fin')>>) /\
      (<<SC_FUTURE_SRC: TimeMap.le sc_src' sc_src>>) /\
      (<<SC_FUTURE_TGT: TimeMap.le sc_tgt' sc_tgt>>) /\
      (<<MEM_FUTURE_SRC: Memory.future_weak mem_src' mem_src>>) /\
      (<<MEM_FUTURE_TGT: Memory.future_weak mem_tgt' mem_tgt>>) /\
      (<<WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w' w>>) /\
      (<<VIEW: views_le views' views>>) /\
      (<<FIN: fin' <4= fin>>)
.
Arguments sim_thread_past: simpl never.

Lemma sim_thread_sim_thread_past:
  sim_thread <14= sim_thread_past.
Proof.
  ii. destruct x13. red. destruct x3; auto. esplits; eauto; try refl.
Qed.

Lemma committed_same prom mem fin
  :
    fin \4/ committed mem prom mem prom = fin.
Proof.
  extensionality loc. extensionality to. extensionality from. extensionality msg.
  eapply Coq.Logic.PropExtensionality.propositional_extensionality.
  split; auto. i. des; auto.
  exfalso. inv H. ss.
Qed.

Lemma sim_thread_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      b w1
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      views1 views3 fin1 fin3
      (STEP: @JThread.step lang_tgt pf_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt)
                          views1 views3)
      (SC: sim_timemap w1 sc1_src sc1_tgt)
      (MEMORY: sim_memory b w1 views1 mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (REL: joined_released views1 lc1_tgt.(Local.promises) lc1_tgt.(Local.tview).(TView.rel))
      (JOINED: joined_memory views1 mem1_tgt)
      (FINMEMORY: fin1 <4= unchangable mem1_tgt lc1_tgt.(Local.promises))
      (VIEWS: wf_views views1)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt (views1, fin1))
      (FIN: fin3 = fin1 \4/ committed mem1_tgt lc1_tgt.(Local.promises) mem3_tgt lc3_tgt.(Local.promises)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src st4_src lc4_src sc4_src mem4_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<STEPS_AFTER: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st3_src lc3_src sc3_src mem3_src)
                  (Thread.mk _ st4_src lc4_src sc4_src mem4_src)>>) /\
    (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
    (<<SC: sim_timemap w3 sc4_src sc3_tgt>>) /\
    (<<MEMORY: sim_memory b w3 views3 mem4_src mem3_tgt>>) /\
    (<<WF_SRC: Local.wf lc4_src mem4_src>>) /\
    (<<WF_TGT: Local.wf lc3_tgt mem3_tgt>>) /\
    (<<SC_SRC: Memory.closed_timemap sc4_src mem4_src>>) /\
    (<<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>>) /\
    (<<MEM_SRC: Memory.closed mem4_src>>) /\
    (<<MEM_TGT: Memory.closed mem3_tgt>>) /\
    (<<SIM: sim_thread sim_terminal b w3 st4_src lc4_src sc4_src mem4_src st3_tgt lc3_tgt sc3_tgt mem3_tgt (views3, fin3)>>) /\
    (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w3>>) /\
    (<<REL: joined_released views3 lc3_tgt.(Local.promises) lc3_tgt.(Local.tview).(TView.rel)>>) /\
    (<<JOINED: joined_memory views3 mem3_tgt>>) /\
    (<<VIEWS: wf_views views3>>) /\
    (<<FINMEMORY: fin3 <4= unchangable mem3_tgt lc3_tgt.(Local.promises)>>)
.
Proof.
  hexploit step_promise_consistent.
  { eapply JThread.step_thread_step; eauto. }
  all: eauto.
  s. i. red in SIM. destruct b; ss.
  { punfold SIM. red in SIM. des.
    exploit JThread.step_future; eauto. s. i. des.
    exploit FUTURE; eauto; ss.
    { splits; auto. }
    i. des. exploit STEP0; eauto; ss.
    i. des; eauto.
    inv SIM; [|done]. right.
    exploit Thread.rtc_tau_step_future; try apply STEPS; eauto. s. i. des.
    exploit Thread.opt_step_future; eauto. s. i. des.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    esplits; eauto. i. des.
    { eapply FINMEMORY in PR.
      eapply JThread.step_thread_step in STEP.
      eapply step_unchangable in STEP; eauto. }
    { inv PR. auto. }
  }
  { des. punfold SIM0. red in SIM0. des.
    exploit JThread.step_future; eauto. s. i. des.
    exploit FUTURE; eauto; ss.
    { splits; auto. }
    i. des. exploit STEP0; eauto; ss.
    i. des; eauto.
    inv SIM; [|done]. right.
    exploit Thread.rtc_tau_step_future; try apply STEPS; eauto. s. i. des.
    exploit Thread.opt_step_future; eauto. s. i. des.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    esplits; eauto. i. des.
    { eapply FINMEMORY in PR.
      eapply JThread.step_thread_step in STEP.
      eapply step_unchangable in STEP; eauto. }
    { inv PR. auto. }
  }
Qed.

Lemma sim_thread_opt_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      b w1
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      views1 views3 fin1 fin3
      (STEP: @JThread.opt_step lang_tgt e_tgt
                               (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                               (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt)
                               views1 views3)
      (SC: sim_timemap w1 sc1_src sc1_tgt)
      (MEMORY: sim_memory b w1 views1 mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (REL: joined_released views1 lc1_tgt.(Local.promises) lc1_tgt.(Local.tview).(TView.rel))
      (JOINED: joined_memory views1 mem1_tgt)
      (FINMEMORY: fin1 <4= unchangable mem1_tgt lc1_tgt.(Local.promises))
      (VIEWS: wf_views views1)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt (views1, fin1))
      (FIN: fin3 = fin1 \4/ committed mem1_tgt lc1_tgt.(Local.promises) mem3_tgt lc3_tgt.(Local.promises)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src st4_src lc4_src sc4_src mem4_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                             (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<STEPS_AFTER: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st3_src lc3_src sc3_src mem3_src)
                  (Thread.mk _ st4_src lc4_src sc4_src mem4_src)>>) /\
    (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
    (<<SC: sim_timemap w3 sc4_src sc3_tgt>>) /\
    (<<MEMORY: sim_memory b w3 views3 mem4_src mem3_tgt>>) /\
    (<<WF_SRC: Local.wf lc4_src mem4_src>>) /\
    (<<WF_TGT: Local.wf lc3_tgt mem3_tgt>>) /\
    (<<SC_SRC: Memory.closed_timemap sc4_src mem4_src>>) /\
    (<<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>>) /\
    (<<MEM_SRC: Memory.closed mem4_src>>) /\
    (<<MEM_TGT: Memory.closed mem3_tgt>>) /\
    (<<SIM: sim_thread_past sim_terminal b w3 st4_src lc4_src sc4_src mem4_src st3_tgt lc3_tgt sc3_tgt mem3_tgt (views3, fin3)>>) /\
    (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w3>>) /\
    (<<REL: joined_released views3 lc3_tgt.(Local.promises) lc3_tgt.(Local.tview).(TView.rel)>>) /\
    (<<JOINED: joined_memory views3 mem3_tgt>>) /\
    (<<VIEWS: wf_views views3>>) /\
    (<<FINMEMORY: fin3 <4= unchangable mem3_tgt lc3_tgt.(Local.promises)>>)
.
Proof.
  inv STEP.
  - right. esplits; eauto; ss.
    { econs 1. }
    { econs. }
    { rewrite committed_same. auto. }
    { refl. }
    { i. des; auto. inv PR; ss. }
  - hexploit sim_thread_step; eauto; ss. i. des; eauto.
    right. esplits; eauto. eapply sim_thread_sim_thread_past; eauto.
Qed.

Lemma sim_thread_rtc_step
      lang_src lang_tgt
      sim_terminal
      b w1
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt
      views1 views2 fin1 fin2
      (STEPS: @JThread.rtc_tau lang_tgt e1_tgt e2_tgt views1 views2)
      (SC: sim_timemap w1 sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory b w1 views1 mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e2_tgt))
      (REL: joined_released views1 (Thread.local e1_tgt).(Local.promises) (Thread.local e1_tgt).(Local.tview).(TView.rel))
      (JOINED: joined_memory views1 (Thread.memory e1_tgt))
      (FINMEMORY: fin1 <4= unchangable e1_tgt.(Thread.memory) e1_tgt.(Thread.local).(Local.promises))
      (VIEWS: wf_views views1)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt) (views1, fin1))
      (FIN: fin2 = fin1 \4/ committed (Thread.memory e1_tgt) (Thread.local e1_tgt).(Local.promises) (Thread.memory e2_tgt) (Thread.local e2_tgt).(Local.promises)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists st2_src lc2_src sc2_src mem2_src w2,
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<SC: sim_timemap w2 sc2_src (Thread.sc e2_tgt)>>) /\
    (<<MEMORY: sim_memory b w2 views2 mem2_src (Thread.memory e2_tgt)>>) /\
    (<<WF_SRC: Local.wf lc2_src mem2_src>>) /\
    (<<WF_TGT: Local.wf (Thread.local e2_tgt) (Thread.memory e2_tgt)>>) /\
    (<<SC_SRC: Memory.closed_timemap sc2_src mem2_src>>) /\
    (<<SC_TGT: Memory.closed_timemap (Thread.sc e2_tgt) (Thread.memory e2_tgt)>>) /\
    (<<MEM_SRC: Memory.closed mem2_src>>) /\
    (<<MEM_TGT: Memory.closed (Thread.memory e2_tgt)>>) /\
    (<<SIM: sim_thread_past sim_terminal b w2 st2_src lc2_src sc2_src mem2_src (Thread.state e2_tgt) (Thread.local e2_tgt) (Thread.sc e2_tgt) (Thread.memory e2_tgt) (views2, fin2)>>) /\
    (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w2>>) /\
    (<<REL: joined_released views2 (Thread.local e2_tgt).(Local.promises) (Thread.local e2_tgt).(Local.tview).(TView.rel)>>) /\
    (<<JOINED: joined_memory views2 (Thread.memory e2_tgt)>>) /\
    (<<VIEWS: wf_views views2>>) /\
    (<<FINMEMORY: fin2 <4= unchangable e2_tgt.(Thread.memory) e2_tgt.(Thread.local).(Local.promises)>>)
.
Proof.
  revert w1 SC MEMORY WF_SRC WF_TGT SC_SRC SC_TGT MEM_SRC MEM_TGT SIM FINMEMORY FIN.
  revert st1_src lc1_src sc1_src mem1_src fin1 fin2.
  induction STEPS; i.
  { right. esplits; eauto.
    { subst. rewrite committed_same. auto. }
    { refl. }
    { subst. i. des; auto. inv PR; ss. }
  }
  destruct e1, e2.
  exploit JThread.step_future; eauto. s. i. des.
  hexploit rtc_tau_step_promise_consistent.
  { eapply JThread.tau_steps_thread_tau_steps. eauto. }
  all: ss. i.
  hexploit sim_thread_step; eauto; ss. i. des; eauto.
  hexploit IHSTEPS; try exact FINMEMORY0; eauto; ss.
  { eapply sim_thread_sim_thread_past; eauto. }
  i. des.
  - left. inv FAILURE0. des.
    unfold Thread.steps_failure. esplits; [|eauto|eauto].
    etrans; eauto. etrans; eauto.
    etrans; [|eauto]. etrans; [|eauto]. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + rewrite EVENT in *. inv EVENT0. auto.
  - right. esplits; try apply MEMORY1; eauto.
    { etrans; [eauto|]. etrans; [|eauto]. inv STEP0; eauto.
      econs 2; eauto. econs.
      + econs. eauto.
      + rewrite EVENT in *. inv EVENT0. auto.
    }
    { subst. erewrite f_equal; [eauto|]. f_equal.
      extensionality loc. extensionality to. extensionality from. extensionality msg.
      eapply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; auto.
      { i. des; auto. inv H0.
        destruct (classic (unchangable memory0 local0.(Local.promises) loc to from msg)).
        { left. right. econs; eauto. }
        { right. econs; eauto. }
      }
      { i. des; auto.
        { right. inv H0. econs; eauto.
          eapply rtc_step_unchangable.
          { eapply JThread.tau_steps_thread_tau_steps; eauto. }
          { ss. }
        }
        { right. inv H0. econs; eauto.
          ii. eapply NUNCHANGABLE.
          inv STEP. ss. eapply step_unchangable in STEP1; eauto. }
      }
    }
    { etrans; [eauto|].
      eapply world_messages_le_mon; eauto.
      i. eapply rtc_step_unchangable in STEPS0; eauto.
      eapply opt_step_unchangable in STEP0; eauto.
      eapply rtc_step_unchangable in STEPS_AFTER; eauto.
    }
    { i. subst. des; auto. inv PR; auto. }
Qed.

Lemma sim_thread_plus_step_aux
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      b w1
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt e3_tgt
      views1 views2 views3
      fin1 fin3
      (STEPS: @JThread.rtc_tau lang_tgt e1_tgt e2_tgt views1 views2)
      (STEP: @JThread.step lang_tgt pf_tgt e_tgt e2_tgt e3_tgt views2 views3)
      (SC: sim_timemap w1 sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory b w1 views1 mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e3_tgt))
      (REL: joined_released views1 (Thread.local e1_tgt).(Local.promises) (Thread.local e1_tgt).(Local.tview).(TView.rel))
      (JOINED: joined_memory views1 (Thread.memory e1_tgt))
      (FINMEMORY: fin1 <4= unchangable e1_tgt.(Thread.memory) e1_tgt.(Thread.local).(Local.promises))
      (VIEWS: wf_views views1)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt) (views1, fin1))
      (FIN: fin3 = fin1 \4/ committed (Thread.memory e1_tgt) (Thread.local e1_tgt).(Local.promises) (Thread.memory e3_tgt) (Thread.local e3_tgt).(Local.promises)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src st4_src lc4_src sc4_src mem4_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<STEPS_AFTER: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st3_src lc3_src sc3_src mem3_src)
                 (Thread.mk _ st4_src lc4_src sc4_src mem4_src)>>) /\
    (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
    (<<SC: sim_timemap w3 sc4_src (Thread.sc e3_tgt)>>) /\
    (<<MEMORY: sim_memory b w3 views3 mem4_src (Thread.memory e3_tgt)>>) /\
    (<<WF_SRC: Local.wf lc4_src mem4_src>>) /\
    (<<WF_TGT: Local.wf (Thread.local e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<SC_SRC: Memory.closed_timemap sc4_src mem4_src>>) /\
    (<<SC_TGT: Memory.closed_timemap (Thread.sc e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<MEM_SRC: Memory.closed mem4_src>>) /\
    (<<MEM_TGT: Memory.closed (Thread.memory e3_tgt)>>) /\
    (<<SIM: sim_thread sim_terminal b w3 st4_src lc4_src sc4_src mem4_src (Thread.state e3_tgt) (Thread.local e3_tgt) (Thread.sc e3_tgt) (Thread.memory e3_tgt) (views3, fin3)>>) /\
    (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w3>>) /\
    (<<REL: joined_released views3 (Thread.local e3_tgt).(Local.promises) (Thread.local e3_tgt).(Local.tview).(TView.rel)>>) /\
    (<<JOINED: joined_memory views3 (Thread.memory e3_tgt)>>) /\
    (<<VIEWS: wf_views views3>>) /\
    (<<FINMEMORY: fin3 <4= unchangable e3_tgt.(Thread.memory) e3_tgt.(Thread.local).(Local.promises)>>)
.
Proof.
  destruct e1_tgt, e2_tgt, e3_tgt. ss.
  exploit JThread.tau_steps_future; eauto. s. i. des.
  hexploit step_promise_consistent.
  { eapply JThread.step_thread_step. eauto. }
  all: ss. i.
  hexploit sim_thread_rtc_step; eauto; ss. i. des; eauto.
  exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
  hexploit sim_thread_step; try exact STEP; try exact SIM0; eauto; ss. i. des.
  - left. inv FAILURE. des.
    unfold Thread.steps_failure. esplits; [|eauto|eauto].
    etrans; eauto.
  - right. dup STEPS0. rewrite STEPS1 in STEPS0.
    esplits; [|apply STEPS0|apply STEP0|apply STEPS_AFTER|..]; eauto.
    { erewrite f_equal; [eauto|]. f_equal. subst.
      extensionality loc. extensionality to. extensionality from. extensionality msg.
      eapply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; auto.
      { i. des; auto. inv H0.
        destruct (classic (unchangable memory0 local0.(Local.promises) loc to from msg)).
        { left. right. econs; eauto. }
        { right. econs; eauto. }
      }
      { i. des; auto.
        { right. inv H0. econs; eauto.
          eapply JThread.step_thread_step in STEP.
          eapply step_unchangable in STEP; eauto.
        }
        { right. inv H0. econs; eauto.
          ii. eapply NUNCHANGABLE.
          eapply JThread.tau_steps_thread_tau_steps in STEPS.
          eapply rtc_step_unchangable in STEPS; eauto. }
      }
    }
    { etrans; [eauto|].
      eapply world_messages_le_mon; eauto.
      i. eapply rtc_step_unchangable in STEPS2; eauto. }
    { i. subst. des; auto. inv PR. auto. }
Qed.

Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src sc2_src mem1_src mem2_src w1 views1
      st_tgt lc_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt w2 views2 fin1 fin2
      (SIM: @sim_thread_past lang_src lang_tgt sim_terminal false w1 st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt (views1, fin1))
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt)
      (WORLD: world_messages_le (Messages.of_memory lc_src.(Local.promises)) w1 w2)
      (VIEWS: views_le views1 views2)
      (FIN: fin1 <4= fin2):
  sim_thread_past sim_terminal false w2 st_src lc_src sc2_src mem2_src st_tgt lc_tgt sc2_tgt mem2_tgt (views2, fin2).
Proof.
  red in SIM. red. des. ss. esplits; eauto.
  { etrans; eauto. }
  { etrans; eauto. }
  { etrans; eauto. }
  { etrans; eauto. }
Qed.

Lemma cap_property
      mem1 mem2 lc sc
      (CAP: Memory.cap mem1 mem2)
      (WF: Local.wf lc mem1)
      (SC: Memory.closed_timemap sc mem1)
      (CLOSED: Memory.closed mem1):
  (<<FUTURE: Memory.future_weak mem1 mem2>>) /\
  (<<WF: Local.wf lc mem2>>) /\
  (<<SC: Memory.closed_timemap sc mem2>>) /\
  (<<CLOSED: Memory.closed mem2>>).
Proof.
  splits.
  - eapply Memory.cap_future_weak; eauto.
  - eapply Local.cap_wf; eauto.
  - eapply Memory.cap_closed_timemap; eauto.
  - eapply Memory.cap_closed; eauto.
Qed.

Lemma joined_memory_cap views mem cap
      (JOINED: joined_memory views mem)
      (CAP: Memory.cap mem cap)
      (CLOSED: Memory.closed mem)
  :
    joined_memory views cap.
Proof.
  inv JOINED. econs.
  - i. eapply Memory.cap_inv in GET; eauto. des; eauto; clarify.
  - i. exploit ONLY; eauto. i. des.
    eapply Memory.cap_le in GET; eauto. refl.
  - i. eapply List.Forall_impl; try apply CLOSED0; eauto.
    i. ss. eapply Memory.cap_closed_view; eauto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      w
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      views fin
      (SIM: sim_thread sim_terminal false w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt (views, fin))
      (SC: sim_timemap w sc_src sc_tgt)
      (MEMORY: sim_memory false w views mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (REL: joined_released views lc_tgt.(Local.promises) lc_tgt.(Local.tview).(TView.rel))
      (JOINED: joined_memory views mem_tgt)
      (FINMEMORY: fin <4= unchangable mem_tgt lc_tgt.(Local.promises))
      (VIEWS: wf_views views)
      (CONSISTENT: JThread.consistent (Thread.mk lang_tgt st_tgt lc_tgt sc_tgt mem_tgt) views):
  Thread.consistent (Thread.mk lang_src st_src lc_src sc_src mem_src).
Proof.
  hexploit consistent_promise_consistent.
  { eapply JThread.consistent_thread_consistent. eauto. }
  all: ss. i.
  generalize SIM. intro X.
  red in X. punfold X. red in X. des. clear FUTURE.
  exploit Memory.cap_exists; try exact MEM_TGT; eauto. i. des.
  exploit Memory.cap_exists; try exact MEM_SRC; eauto. i. des.
  exploit CAP; eauto. i. des. inv SIM0; [|done].
  assert (SIM0: sim_thread_past sim_terminal true w3 st_src lc_src sc_src mem0 st_tgt lc_tgt sc_tgt mem2 (views, fin)) by auto.
  exploit cap_property; try exact CAP0; eauto. i. des.
  exploit cap_property; try exact CAP1; eauto. i. des.
  exploit joined_memory_cap; eauto. intros JOINED0.
  assert (FINMEMORY0: fin <4= unchangable mem2 (Local.promises lc_tgt)).
  { i. apply FINMEMORY in PR. inv PR. econs; eauto.
    eapply Memory.cap_le; eauto. refl. }
  exploit CONSISTENT; eauto. s. i. des.
  - left. des. s.
    assert (mem1 = mem0).
    { eapply Memory.cap_inj; eauto. } subst.
    assert (JSTEP: JThread.step true e e2 e3 views2 views2).
    { eapply JThread.tau_steps_future in STEPS; eauto. des. ss.
      inv STEP_FAILURE.
      { inv STEP; ss. }
      inv STEP. inv LOCAL; ss.
      { econs; ss. econs 2; ss. econs; eauto. }
      { econs; ss. econs 2; ss. econs; ss. econs; eauto. }
      { econs; ss. econs 2; ss. econs; ss. econs; eauto. }
    }
    hexploit sim_thread_plus_step_aux; try exact STEPS; try exact FAILURE; eauto; try refl.
    { hexploit non_silent_step_promise_consistent; eauto.
      { rewrite EVENT_FAILURE. ss. }
      i. des; auto.
    }
    i. ss. des; ss.
  - ii. ss.
    assert (mem1 = mem0).
    { eapply Memory.cap_inj; eauto. } subst.
    hexploit Local.bot_promise_consistent; eauto. i.
    exploit sim_thread_rtc_step; try apply STEPS; try exact x1; eauto; try refl.
    i. des; eauto.
    destruct e2. ss. punfold SIM1. red in SIM1. des.
    hexploit FUTURE1; try apply FINMEMORY1; eauto; ss.
    { splits; ss. } dup REL. i. des.
    exploit PROMISES0; eauto. i. des.
    + left. unfold Thread.steps_failure in *. des.
      esplits; [|eauto|eauto]. etrans; eauto.
    + right. eexists (Thread.mk _ _ _ _ _). splits; [|eauto].
      etrans; eauto.
Qed.

Lemma sim_thread_plus_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      b w1
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt e3_tgt
      views1 views2 views3
      fin1 fin3
      (STEPS: @JThread.rtc_tau lang_tgt e1_tgt e2_tgt views1 views2)
      (STEP: @JThread.step lang_tgt pf_tgt e_tgt e2_tgt e3_tgt views2 views3)
      (SC: sim_timemap w1 sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory b w1 views1 mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e3_tgt))
      (REL: joined_released views1 (Thread.local e1_tgt).(Local.promises) (Thread.local e1_tgt).(Local.tview).(TView.rel))
      (JOINED: joined_memory views1 (Thread.memory e1_tgt))
      (FINMEMORY: fin1 <4= unchangable e1_tgt.(Thread.memory) e1_tgt.(Thread.local).(Local.promises))
      (VIEWS: wf_views views1)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt) (views1, fin1))
      (FIN: fin3 = fin1 \4/ committed (Thread.memory e1_tgt) (Thread.local e1_tgt).(Local.promises) (Thread.memory e3_tgt) (Thread.local e3_tgt).(Local.promises)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src st4_src lc4_src sc4_src mem4_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                             (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<CONSISTENT: __guard__((Thread.mk _ st3_src lc3_src sc3_src mem3_src
                              =
                              Thread.mk _ st4_src lc4_src sc4_src mem4_src) \/ Thread.consistent (Thread.mk _ st3_src lc3_src sc3_src mem3_src))>>) /\
    (<<STEPS_AFTER: rtc (@Thread.tau_step lang_src)
                        (Thread.mk _ st3_src lc3_src sc3_src mem3_src)
                        (Thread.mk _ st4_src lc4_src sc4_src mem4_src)>>) /\
    (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
    (<<SC: sim_timemap w3 sc4_src (Thread.sc e3_tgt)>>) /\
    (<<MEMORY: sim_memory b w3 views3 mem4_src (Thread.memory e3_tgt)>>) /\
    (<<WF_SRC: Local.wf lc4_src mem4_src>>) /\
    (<<WF_TGT: Local.wf (Thread.local e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<SC_SRC: Memory.closed_timemap sc4_src mem4_src>>) /\
    (<<SC_TGT: Memory.closed_timemap (Thread.sc e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<MEM_SRC: Memory.closed mem4_src>>) /\
    (<<MEM_TGT: Memory.closed (Thread.memory e3_tgt)>>) /\
    (<<SIM: sim_thread sim_terminal b w3 st4_src lc4_src sc4_src mem4_src (Thread.state e3_tgt) (Thread.local e3_tgt) (Thread.sc e3_tgt) (Thread.memory e3_tgt) (views3, fin3)>>) /\
    (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) w1 w3>>) /\
    (<<REL: joined_released views3 (Thread.local e3_tgt).(Local.promises) (Thread.local e3_tgt).(Local.tview).(TView.rel)>>) /\
    (<<JOINED: joined_memory views3 (Thread.memory e3_tgt)>>) /\
    (<<VIEWS: wf_views views3>>) /\
    (<<FINMEMORY: fin3 <4= unchangable e3_tgt.(Thread.memory) e3_tgt.(Thread.local).(Local.promises)>>)
.
Proof.
  hexploit sim_thread_plus_step_aux; eauto. i. des.
  { left. auto. }
  destruct (ThreadEvent.get_machine_event e_src) eqn:EVT.
  { right. esplits.
    { eauto. }
    { etrans.
      { eapply Thread.tau_opt_tau.
        { eauto. }
        { eauto. }
        { eauto. }
      }
      { eauto. }
    }
    { econs 1. }
    { left. eauto. }
    all: eauto.
  }
  { right. esplits.
    { eauto. }
    { eauto. }
    { eauto. }
    { right. esplits; eauto. ii.  ss. right. esplits; [refl|..].
      ss. inv STEP0; ss. inv STEP1; inv STEP0; ss.
      inv LOCAL; ss. inv LOCAL0; ss. auto.
    }
    all: eauto. rewrite EVT. auto.
  }
  { left. inv STEP0; ss. repeat red.
    dup STEP1. inv STEP1; [inv STEP2|]; ss. esplits; eauto.
  }
Qed.


Section Simulation.
  Definition SIM :=
    forall (w: world) (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t) (views0: Loc.t -> Time.t -> list View.t), Prop.

  Definition _sim
             (sim: SIM)
             (w0: world)
             (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t)
             (views0: Loc.t -> Time.t -> list View.t): Prop :=
    forall w1 sc1_src mem1_src
           sc1_tgt mem1_tgt views1
           (SC1: sim_timemap w1 sc1_src sc1_tgt)
           (MEMORY1: sim_memory false w1 views1 mem1_src mem1_tgt)
           (WF_SRC: Configuration.wf (Configuration.mk ths1_src sc1_src mem1_src))
           (WF_TGT: JConfiguration.wf views1 (Configuration.mk ths1_tgt sc1_tgt mem1_tgt))
           (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
           (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
           (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
           (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt)
           (VIEWS_FUTURE: views_le views0 views1)
           (WORLD: forall tid st lc
                          (TID: IdentMap.find tid ths1_src = Some (st, lc)),
               world_messages_le (Messages.of_memory lc.(Local.promises)) w0 w1)
           (FINTGT: finalized (Configuration.mk ths1_tgt sc0_tgt mem0_tgt) <4= finalized (Configuration.mk ths1_tgt sc1_tgt mem1_tgt))
           (FINSRC: finalized (Configuration.mk ths1_src sc0_src mem0_src) <4= finalized (Configuration.mk ths1_src sc1_src mem1_src)),
      (<<TERMINAL:
         forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
           (<<FAILURE: Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src)>>) \/
           exists ths2_src sc2_src mem2_src w2,
             (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>>) /\
             (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
             (<<MEMORY: sim_memory false w2 views1 mem2_src mem1_tgt>>) /\
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
             (<<MEMORY3: sim_memory false w3 views3 mem4_src mem3_tgt>>) /\
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
      (MEMORY: sim_memory false w views mem_src mem_mid)
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
          exists sim_terminal,
            @sim_thread_past lang_src lang_tgt sim_terminal false w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt (views, finalized (Configuration.mk ths_tgt sc0_tgt mem0_tgt)))
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
               exists sim_terminal,
                 @sim_thread_past lang_src lang_tgt sim_terminal false w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt (views, finalized (Configuration.mk ths_tgt sc1_tgt mem1_tgt))).
    { i. hexploit SIM0; eauto. i. des. esplits.
      eapply sim_thread_future; eauto; try refl. }
    assert (WORLD0: forall tid st lc
                           (TID: List.In tid (IdentSet.elements tids))
                           (FIND: IdentMap.find tid ths_src = Some (st, lc)),
               world_messages_le (Messages.of_memory lc.(Local.promises)) w w1).
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
    exploit TERMINAL_TGT; eauto. i. des.
    hexploit Local.terminal_promise_consistent; eauto. i.
    red in x2. des. punfold SIM0. red in SIM0. des.
    exploit FUTURE; eauto; ss.
    { etrans; eauto. }
    { ss. splits; eauto using Memory.future_future_weak.
      { etrans; eauto. eapply Memory.future_future_weak; eauto. }
      { etrans; eauto. eapply Memory.future_future_weak; eauto. }
      { etrans; eauto. }
      { etrans; eauto. }
      { i. eapply FIN in PR. eapply finalized_unchangable in PR; eauto. }
    }
    i. des.
    exploit TERMINAL; eauto. i. des.
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
      { ii. right. esplits; [refl|..]. ss.
        inv THREAD. eapply sim_local_memory_bot; eauto. } i. des; auto.
      exploit Configuration.rtc_step_future; try eapply x3; eauto. s. i. des.
      exploit IHl; [| |exact SC2|exact MEMORY|..]; try exact WF2; try exact WF_TGT;
        try exact SC_FUTURE_TGT; try exact MEM_FUTURE_TGT;
          try (etrans; [exact SC_FUTURE_SRC|exact SC_FUTURE]);
          try (etrans; [exact MEM_FUTURE_SRC|exact MEM_FUTURE]); eauto; i.
      { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
      { refl. }
      { rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
        - subst. Configuration.simplify. split; auto.
          inv THREAD. econs. eapply sim_local_memory_bot; eauto.
        - eapply NOTIN; eauto. ii. des; ss. subst. ss. }
      { rewrite IdentMap.gsspec in H0. revert H0. condtac; ss; i.
        - subst. inv NODUP. congr.
        - exploit IN; eauto. i. des.
          esplits. eapply sim_thread_future; eauto; try refl.
          etrans.
          { eapply WORLD0; eauto. }
          { eapply world_messages_le_mon; [eauto|].
            destruct lc_src0, lc_src.
            eapply other_promise_unchangable; eauto. }
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
      { i. apply sim_thread_sim_thread_past in SIM1. Configuration.simplify.
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
            { eapply world_messages_le_mon; [eauto|].
              destruct lc_src, lc_src0.
              eapply other_promise_unchangable; eauto. }
          }
          { etrans; eauto. }
          { eapply JConfiguration.step_configuration_step in STEP_TGT0. inv WF_TGT0.
            i. eapply step_finalized; eauto. }
        }
      }
Qed.

End WORLD.
Hint Resolve _sim_thread_mon: paco.
