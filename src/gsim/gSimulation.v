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

Require Import Program.


Set Implicit Arguments.


(* TODO: remove Memory.closed condition in Memory.cap_inv Memory.cap_future_weak *)
Lemma memory_cap_future
      mem0 mem1
      (CAP: Memory.cap mem0 mem1)
  :
    Memory.future_weak mem0 mem1.
Admitted.


(* TODO: use FutureCertify to prove it *)
Module UndefCertify.
  Definition certified (c: Configuration.t): Prop. Admitted.

  Lemma step_certified c0 c1 e tid
        (STEP: Configuration.step e tid c0 c1)        
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
    :
      certified c1.
  Admitted.

  Lemma rtc_step_certified c0 c1
        (STEPS: rtc Configuration.tau_step c0 c1)        
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
    :
      certified c1.
  Proof.
    revert CERTIFIED WF. induction STEPS; auto.
    i. inv H. eapply IHSTEPS; auto.
    { eapply step_certified; eauto. }
    { eapply Configuration.step_future; eauto. }
  Qed.
  
  Lemma certified_init s
    :
      certified (Configuration.init s).
  Admitted.

  Definition unchanged (prom: Memory.t) (mem0 mem1: Memory.t): Prop :=
    forall loc to from
           (UNDEF: Memory.get loc to prom = Some (from, Message.undef)),
    forall ts1 ts0 msg
           (GET: Memory.get loc ts1 mem1 = Some (ts0, msg))
           (CONCRETE: msg <> Message.reserve),
      Memory.get loc ts1 mem0 = Some (ts0, msg).

  Program Instance unchanged_PreOrder prom: PreOrder (unchanged prom).
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Lemma cap_unchanged mem0 mem1 prom
        (CAP: Memory.cap mem0 mem1)
        (* (CLOSED: Memory.closed mem0) *)
    :
      unchanged prom mem0 mem1.
  Proof.
    ii. eapply Memory.cap_inv in GET; eauto. des; ss.
  Admitted.
  
  Lemma step_unchanged c0 c1 tid e
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
        (STEP: Configuration.step e tid c0 c1)
    :
      ((<<UNCHANGED: forall tid' st lc
                            (TID: tid' <> tid)
                            (TID: IdentMap.find tid' c0.(Configuration.threads) = Some (st, lc)),
           UndefCertify.unchanged lc.(Local.promises) c0.(Configuration.memory) c1.(Configuration.memory)>>) \/
       (<<FAILURE: Configuration.steps_failure c0>>)).
  Admitted.

  Lemma opt_step_unchanged c0 c1 tid e
        (CERTIFIED: certified c0)
        (WF: Configuration.wf c0)
        (STEP: Configuration.opt_step e tid c0 c1)
    :
      ((<<UNCHANGED: forall tid' st lc
                            (TID: tid' <> tid)
                            (TID: IdentMap.find tid' c0.(Configuration.threads) = Some (st, lc)),
           UndefCertify.unchanged lc.(Local.promises) c0.(Configuration.memory) c1.(Configuration.memory)>>) \/
       (<<FAILURE: Configuration.steps_failure c0>>)).
  Proof.
    inv STEP.
    { left. red. i. refl. }
    { eapply step_unchanged; eauto. }
  Qed.
End UndefCertify.



Section WORLD.

Variable world: Type.
Variable world_le: world -> world -> Prop.

Context `{world_le_PreOrder: @PreOrder _ world_le}.

Variable sim_memory: forall (b: bool) (w: world) (mem_src mem_tgt:Memory.t), Prop.
Variable sim_timemap: forall (w: world) (sc_src sc_tgt: TimeMap.t), Prop.
Variable sim_local: forall (w: world) (lc_src lc_tgt:Local.t), Prop.

Hypothesis sim_local_world_mon: forall (w0 w1: world) (WORLD: world_le w0 w1),
    sim_local w0 <2= sim_local w1.

Hypothesis sim_local_memory_bot:
  forall w lc_src lc_tgt
         (SIM: sim_local w lc_src lc_tgt)
         (BOT: (Local.promises lc_tgt) = Memory.bot),
    (Local.promises lc_src) = Memory.bot.

Hypothesis sim_memory_cap: forall
    w1
    mem1_src mem2_src
    mem1_tgt mem2_tgt
    sc1_src sc1_tgt
    (MEM1: sim_memory false w1 mem1_src mem1_tgt)
    (CAP_SRC: Memory.cap mem1_src mem2_src)
    (CAP_TGT: Memory.cap mem1_tgt mem2_tgt)
    (MEM1_SRC: Memory.closed mem1_src)
    (MEM1_TGT: Memory.closed mem1_tgt)
    (CLOSED_SRC: Memory.closed_timemap sc1_src mem1_src)
    (CLOSED_TGT: Memory.closed_timemap sc1_tgt mem1_tgt),
    exists w2,
      (<<MEM2: sim_memory true w2 mem2_src mem2_tgt>>) /\
      (<<TIMEMAP: sim_timemap w2 sc1_src sc1_tgt>>) /\
      (<<WORLD: world_le w1 w2>>)
.


Section SimulationThread.
  Definition SIM_TERMINAL (lang_src lang_tgt:language) :=
    forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition SIM_THREAD :=
    forall (lang_src lang_tgt:language) (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
           (b: bool) (w: world)
           (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
           (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim_thread_step
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             b0 (w0: world)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt
    :=
      forall pf_tgt e_tgt st3_tgt lc3_tgt sc3_tgt mem3_tgt
             (STEP_TGT: Thread.step pf_tgt e_tgt
                                    (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                                    (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt)),
        (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
        exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src w3,
          (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
          (<<STEPS: rtc (@Thread.tau_step _)
                        (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                        (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
          (<<STEP_SRC: Thread.opt_step e_src
                                       (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                                       (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
          (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
          (<<SC3: sim_timemap w3 sc3_src sc3_tgt>>) /\
          (<<MEMORY3: sim_memory b0 w3 mem3_src mem3_tgt>>) /\
          (<<SIM: sim_thread b0 w3 st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
          (<<WORLD: world_le w0 w3>>)
  .

  Definition sim_memory_future
             (b0 b1: bool)
             (prom_src prom_tgt: Memory.t)
             (mem0_src mem1_src mem0_tgt mem1_tgt: Memory.t)
             (sc0_src sc1_src sc0_tgt sc1_tgt: TimeMap.t)
             (w0 w1: world): Prop :=
    match b0, b1 with
    | false, false =>
      (<<MEMSRC: Memory.future_weak mem0_src mem1_src>>) /\
      (<<MEMTGT: Memory.future_weak mem0_tgt mem1_tgt>>) /\
      (<<SCSRC: TimeMap.le sc0_src sc1_src>>) /\
      (<<SCTGT: TimeMap.le sc0_tgt sc1_tgt>>) /\
      (<<WORLD: world_le w0 w1>>)
    | false, true =>
      (<<MEMSRC: Memory.cap mem0_src mem1_src>>) /\
      (<<MEMTGT: Memory.cap mem0_tgt mem1_tgt>>) /\
      (<<SCSRC: sc1_src = sc0_src>>) /\
      (<<SCTGT: sc1_tgt = sc0_tgt>>) /\
      (<<WORLD: world_le w0 w1>>)
    | true, false => False
    | true, true =>
      (<<MEMSRC: mem1_src = mem0_src>>) /\
      (<<MEMTGT: mem1_tgt = mem0_tgt>>) /\
      (<<SCSRC: sc1_src = sc0_src>>) /\
      (<<SCTGT: sc1_tgt = sc0_tgt>>) /\
      (<<WORLD: w1 = w0>>)
    end.

  Lemma sim_future_memory_sc_future
        (b0 b1: bool)
        (prom_src prom_tgt: Memory.t)
        (mem0_src mem1_src mem0_tgt mem1_tgt: Memory.t)
        (sc0_src sc1_src sc0_tgt sc1_tgt: TimeMap.t)
        (w0 w1: world)
        (FUTURE: sim_memory_future
                   b0 b1
                   prom_src prom_tgt
                   mem0_src mem1_src mem0_tgt mem1_tgt
                   sc0_src sc1_src sc0_tgt sc1_tgt
                   w0 w1)
    :
      (<<SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src>>) /\
      (<<SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt>>) /\
      (<<MEM_FUTURE_SRC: Memory.future_weak mem0_src mem1_src>>) /\
      (<<MEM_FUTURE_TGT: Memory.future_weak mem0_tgt mem1_tgt>>) /\
      (<<WORLD: world_le w0 w1>>).
  Proof.
    destruct b0, b1; ss; des; subst.
    - splits; try refl.
    - splits; try refl.
      { eapply memory_cap_future; eauto. }
      { eapply memory_cap_future; eauto. }
      { auto. }
    - splits; auto.
  Qed.

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (lang_src lang_tgt:language)
             (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
             (b0: bool) (w0: world)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall b1 w1 sc1_src mem1_src
           sc1_tgt mem1_tgt
           (SC: sim_timemap w1 sc1_src sc1_tgt)
           (MEMORY: sim_memory b1 w1 mem1_src mem1_tgt)
           (* (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src) *)
           (* (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt) *)
           (* (MEM_FUTURE_SRC: Memory.future_weak mem0_src mem1_src) *)
           (* (MEM_FUTURE_TGT: Memory.future_weak mem0_tgt mem1_tgt) *)
           (WF_SRC: Local.wf lc1_src mem1_src)
           (WF_TGT: Local.wf lc1_tgt mem1_tgt)
           (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
           (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
           (MEM_SRC: Memory.closed mem1_src)
           (MEM_TGT: Memory.closed mem1_tgt)
           (CONS_TGT: Local.promise_consistent lc1_tgt)
           (* (WORLD: world_le w0 w1) *)
           (FUTURE: sim_memory_future
                      b0 b1
                      lc1_src.(Local.promises) lc1_tgt.(Local.promises)
                      mem0_src mem1_src mem0_tgt mem1_tgt
                      sc0_src sc1_src sc0_tgt sc1_tgt
                      w0 w1)
           (UNCHANGED: UndefCertify.unchanged lc1_src.(Local.promises) mem0_src mem1_src),
      (<<TERMINAL:
         forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
           (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
           exists st2_src lc2_src sc2_src mem2_src w2,
             (<<STEPS: rtc (@Thread.tau_step _)
                           (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                           (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
             (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
             (<<MEMORY: sim_memory b1 w2 mem2_src mem1_tgt>>) /\
             (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
             (<<LOCAL: sim_local w2 lc2_src lc1_tgt>>) /\
             (<<TERMINAL: sim_terminal st2_src st1_tgt>>) /\
             (<<WORLD: world_le w1 w2>>)>>) /\
      (<<PROMISES:
         forall (PROMISES_TGT: (Local.promises lc1_tgt) = Memory.bot),
           (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
           exists st2_src lc2_src sc2_src mem2_src,
             (<<STEPS: rtc (@Thread.tau_step _)
                           (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                           (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
             (<<PROMISES_SRC: (Local.promises lc2_src) = Memory.bot>>)>>) /\
      (<<STEP: _sim_thread_step _ _ (@sim_thread lang_src lang_tgt sim_terminal)
                                b1 w1
                                st1_src lc1_src sc1_src mem1_src
                                st1_tgt lc1_tgt sc1_tgt mem1_tgt>>)
  .

  Lemma _sim_thread_mon: monotone13 _sim_thread.
  Proof.
    ii. exploit IN; try apply SC; eauto. i. des.
    splits; eauto. ii.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco13 _sim_thread bot13.

  Lemma sim_thread_mon
        (lang_src lang_tgt:language)
        (sim_terminal1 sim_terminal2: SIM_TERMINAL lang_src lang_tgt)
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <10= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; try apply SC; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des; eauto.
      right. esplits; eauto.
    - ii. exploit STEP; eauto. i. des; eauto.
      inv SIM0; [|done].
      right. esplits; eauto.
  Qed.
End SimulationThread.
Hint Resolve _sim_thread_mon: paco.

Definition sim_thread_past lang_src lang_tgt sim_terminal (b: bool) w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt :=
  if b
  then sim_thread sim_terminal true w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt
  else exists w' sc_src' mem_src' sc_tgt' mem_tgt',
      (<<SIM: @sim_thread lang_src lang_tgt sim_terminal false w' st_src lc_src sc_src' mem_src' st_tgt lc_tgt sc_tgt' mem_tgt'>>) /\
      (<<SC_FUTURE_SRC: TimeMap.le sc_src' sc_src>>) /\
      (<<SC_FUTURE_TGT: TimeMap.le sc_tgt' sc_tgt>>) /\
      (<<MEM_FUTURE_SRC: Memory.future_weak mem_src' mem_src>>) /\
      (<<MEM_FUTURE_TGT: Memory.future_weak mem_tgt' mem_tgt>>) /\
      (<<WORLD: world_le w' w>>) /\
      (<<UNCHANGED: UndefCertify.unchanged lc_src.(Local.promises) mem_src' mem_src>>)
.
Arguments sim_thread_past: simpl never.

Lemma sim_thread_sim_thread_past:
  sim_thread <13= sim_thread_past.
Proof.
  ii. red. destruct x3; auto. esplits; eauto; try refl.
Qed.

Lemma sim_thread_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      b w1
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: sim_timemap w1 sc1_src sc1_tgt)
      (MEMORY: sim_memory b w1 mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
    (<<SC: sim_timemap w3 sc3_src sc3_tgt>>) /\
    (<<MEMORY: sim_memory b w3 mem3_src mem3_tgt>>) /\
    (<<WF_SRC: Local.wf lc3_src mem3_src>>) /\
    (<<WF_TGT: Local.wf lc3_tgt mem3_tgt>>) /\
    (<<SC_SRC: Memory.closed_timemap sc3_src mem3_src>>) /\
    (<<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>>) /\
    (<<MEM_SRC: Memory.closed mem3_src>>) /\
    (<<MEM_TGT: Memory.closed mem3_tgt>>) /\
    (<<SIM: sim_thread sim_terminal b w3 st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
    (<<WORLD: world_le w1 w3>>).
Proof.
  hexploit step_promise_consistent; eauto. s. i. red in SIM. destruct b; ss.
  { punfold SIM. exploit SIM; eauto; ss.
    i. des.
    exploit Thread.step_future; eauto. s. i. des.
    exploit STEP0; eauto. i. des; eauto.
    inv SIM0 ; [|done]. right.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.opt_step_future; eauto. s. i. des.
    esplits; eauto.
  }
  { des.
    punfold SIM0. exploit SIM0; eauto; ss.
    i. des.
    exploit Thread.step_future; eauto. s. i. des.
    exploit STEP0; eauto. i. des; eauto.
    inv SIM ; [|done]. right.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.opt_step_future; eauto. s. i. des.
    esplits; eauto.
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
      (STEP: @Thread.opt_step lang_tgt e_tgt
                              (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                              (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: sim_timemap w1 sc1_src sc1_tgt)
      (MEMORY: sim_memory b w1 mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (CONS_TGT: Local.promise_consistent lc3_tgt)
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                             (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                             (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
    (<<SC: sim_timemap w3 sc3_src sc3_tgt>>) /\
    (<<MEMORY: sim_memory b w3 mem3_src mem3_tgt>>) /\
    (<<WF_SRC: Local.wf lc3_src mem3_src>>) /\
    (<<WF_TGT: Local.wf lc3_tgt mem3_tgt>>) /\
    (<<SC_SRC: Memory.closed_timemap sc3_src mem3_src>>) /\
    (<<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>>) /\
    (<<MEM_SRC: Memory.closed mem3_src>>) /\
    (<<MEM_TGT: Memory.closed mem3_tgt>>) /\
    (<<SIM: sim_thread_past sim_terminal b w3 st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
    (<<WORLD: world_le w1 w3>>)
.
Proof.
  inv STEP.
  - right. esplits; eauto; ss.
    { econs 1. }
    { refl. }
  - exploit sim_thread_step; eauto. i. des; eauto.
    right. esplits; eauto. eapply sim_thread_sim_thread_past; eauto.
Qed.

Lemma sim_thread_rtc_step
      lang_src lang_tgt
      sim_terminal
      b w1
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (SC: sim_timemap w1 sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory b w1 mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e2_tgt))
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists st2_src lc2_src sc2_src mem2_src w2,
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                  (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<SC: sim_timemap w2 sc2_src (Thread.sc e2_tgt)>>) /\
    (<<MEMORY: sim_memory b w2 mem2_src (Thread.memory e2_tgt)>>) /\
    (<<WF_SRC: Local.wf lc2_src mem2_src>>) /\
    (<<WF_TGT: Local.wf (Thread.local e2_tgt) (Thread.memory e2_tgt)>>) /\
    (<<SC_SRC: Memory.closed_timemap sc2_src mem2_src>>) /\
    (<<SC_TGT: Memory.closed_timemap (Thread.sc e2_tgt) (Thread.memory e2_tgt)>>) /\
    (<<MEM_SRC: Memory.closed mem2_src>>) /\
    (<<MEM_TGT: Memory.closed (Thread.memory e2_tgt)>>) /\
    (<<SIM: sim_thread_past sim_terminal b w2 st2_src lc2_src sc2_src mem2_src (Thread.state e2_tgt) (Thread.local e2_tgt) (Thread.sc e2_tgt) (Thread.memory e2_tgt)>>) /\
    (<<WORLD: world_le w1 w2>>)
.
Proof.
  revert w1 SC MEMORY WF_SRC WF_TGT SC_SRC SC_TGT MEM_SRC MEM_TGT SIM.
  revert st1_src lc1_src sc1_src mem1_src.
  induction STEPS; i.
  { right. esplits; eauto. refl. }
  inv H. inv TSTEP. destruct x, y. ss.
  exploit Thread.step_future; eauto. s. i. des.
  hexploit rtc_tau_step_promise_consistent; eauto. s. i.
  exploit sim_thread_step; eauto. i. des; eauto.
  exploit IHSTEPS; eauto.
  { eapply sim_thread_sim_thread_past. eauto. }
  i. des.
  - left. inv FAILURE0. des.
    unfold Thread.steps_failure. esplits; [|eauto|eauto].
    etrans; eauto. etrans; eauto. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + destruct e, e_src; ss.
  - right. destruct z. ss.
    esplits; try apply MEMORY1; eauto.
    2:{ etrans; eauto. }
    etrans; [eauto|]. etrans; [|eauto]. inv STEP0; eauto.
    econs 2; eauto. econs.
    + econs. eauto.
    + destruct e, e_src; ss.
Qed.

Lemma sim_thread_plus_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      b w1
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt e3_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt e2_tgt e3_tgt)
      (SC: sim_timemap w1 sc1_src (Thread.sc e1_tgt))
      (MEMORY: sim_memory b w1 mem1_src (Thread.memory e1_tgt))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed (Thread.memory e1_tgt))
      (CONS_TGT: Local.promise_consistent (Thread.local e3_tgt))
      (SIM: sim_thread_past sim_terminal b w1 st1_src lc1_src sc1_src mem1_src (Thread.state e1_tgt) (Thread.local e1_tgt) (Thread.sc e1_tgt) (Thread.memory e1_tgt)):
  (<<FAILURE: Thread.steps_failure (Thread.mk lang_src st1_src lc1_src sc1_src mem1_src)>>) \/
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src w3,
    (<<FAILURE: ThreadEvent.get_machine_event e_tgt <> MachineEvent.failure>>) /\
    (<<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
    (<<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
    (<<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>>) /\
    (<<SC: sim_timemap w3 sc3_src (Thread.sc e3_tgt)>>) /\
    (<<MEMORY: sim_memory b w3 mem3_src (Thread.memory e3_tgt)>>) /\
    (<<WF_SRC: Local.wf lc3_src mem3_src>>) /\
    (<<WF_TGT: Local.wf (Thread.local e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<SC_SRC: Memory.closed_timemap sc3_src mem3_src>>) /\
    (<<SC_TGT: Memory.closed_timemap (Thread.sc e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<MEM_SRC: Memory.closed mem3_src>>) /\
    (<<MEM_TGT: Memory.closed (Thread.memory e3_tgt)>>) /\
    (<<SIM: sim_thread sim_terminal b w3 st3_src lc3_src sc3_src mem3_src (Thread.state e3_tgt) (Thread.local e3_tgt) (Thread.sc e3_tgt) (Thread.memory e3_tgt)>>) /\
    (<<WORLD: world_le w1 w3>>)
.
Proof.
  destruct e1_tgt, e2_tgt, e3_tgt. ss.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  hexploit step_promise_consistent; eauto. s. i.
  exploit sim_thread_rtc_step; eauto. s. i. des; eauto.
  exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
  exploit sim_thread_step; try exact STEP; try exact SIM0; eauto. s. i. des.
  - left. inv FAILURE. des.
    unfold Thread.steps_failure. esplits; [|eauto|eauto].
    etrans; eauto.
  - right. rewrite STEPS1 in STEPS0.
    esplits; try exact STEPS0; try exact STEP0; eauto.
    etrans; eauto.
Qed.

Lemma sim_thread_future_false_true
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src mem1_src mem2_src w1
      st_tgt lc_tgt sc1_tgt mem1_tgt mem2_tgt w2
      (SIM: @sim_thread lang_src lang_tgt sim_terminal false w1 st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt)
      (MEM_FUTURE_SRC: Memory.cap mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.cap mem1_tgt mem2_tgt)
      (WORLD: world_le w1 w2):
  sim_thread sim_terminal true w2 st_src lc_src sc1_src mem2_src st_tgt lc_tgt sc1_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. destruct b1; ss; des; subst.
  exploit SIM; (try by etrans; eauto); eauto; ss.
  eapply UndefCertify.cap_unchanged; auto.
Qed.

Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src sc2_src mem1_src mem2_src w1
      st_tgt lc_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt w2
      (SIM: @sim_thread_past lang_src lang_tgt sim_terminal false w1 st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future_weak mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future_weak mem1_tgt mem2_tgt)
      (WORLD: world_le w1 w2)
      (UNCHANGED: UndefCertify.unchanged lc_src.(Local.promises) mem1_src mem2_src):
  sim_thread_past sim_terminal false w2 st_src lc_src sc2_src mem2_src st_tgt lc_tgt sc2_tgt mem2_tgt.
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

(* TODO: remove *)

Lemma sc_property
      sc1 sc2 mem
      (MAX: Memory.max_concrete_timemap mem sc2)
      (SC1: Memory.closed_timemap sc1 mem)
      (MEM: Memory.closed mem):
  (<<SC2: Memory.closed_timemap sc2 mem>>) /\
  (<<LE: TimeMap.le sc1 sc2>>).
Proof.
  splits.
  - eapply Memory.max_concrete_timemap_closed; eauto.
  - eapply Memory.max_concrete_timemap_spec; eauto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      w
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      (SIM: sim_thread sim_terminal false w st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
      (SC: sim_timemap w sc_src sc_tgt)
      (MEMORY: sim_memory false w mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (CONSISTENT: Thread.consistent (Thread.mk lang_tgt st_tgt lc_tgt sc_tgt mem_tgt)):
  Thread.consistent (Thread.mk lang_src st_src lc_src sc_src mem_src).
Proof.
  hexploit consistent_promise_consistent; eauto. s. i.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; ss; splits; try refl. i. des.
  ii. ss.
  exploit Memory.cap_exists; try exact MEM_TGT. i. des.
  exploit cap_property; try exact CAP; eauto. i. des.
  exploit cap_property; try exact CAP0; eauto. i. des.
  exploit sim_memory_cap; try exact MEMORY; eauto. i. des.
  exploit CONSISTENT; eauto. s. i. des.
  - left. inv FAILURE. des.
    exploit sim_thread_future_false_true; try exact SIM; eauto. i.
    exploit sim_thread_plus_step; try exact STEPS; try exact FAILURE; try exact x2; eauto; try refl.
    { inv STEP_FAILURE; inv STEP0; ss. inv LOCAL; ss; inv LOCAL0; ss. }
    i. des; ss.
  - hexploit Local.bot_promise_consistent; eauto. i.
    exploit sim_thread_future_false_true; try exact SIM; eauto. i.
    exploit sim_thread_rtc_step; try apply STEPS; try exact x1; eauto; try refl.
    i. des; eauto.
    destruct e2. ss.
    punfold SIM0. exploit SIM0; eauto; ss. i. des.
    exploit PROMISES1; eauto. i. des.
    + left. unfold Thread.steps_failure in *. des.
      esplits; [|eauto|eauto]. etrans; eauto.
    + right. eexists (Thread.mk _ _ _ _ _). splits; [|eauto].
      etrans; eauto.
Qed.




Section Simulation.
  Definition SIM :=
    forall (w: world) (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim
             (sim: SIM)
             (w0: world)
             (ths1_src:Threads.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (ths1_tgt:Threads.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall w1 sc1_src mem1_src
           sc1_tgt mem1_tgt
           (SC1: sim_timemap w1 sc1_src sc1_tgt)
           (MEMORY1: sim_memory false w1 mem1_src mem1_tgt)
           (WF_SRC: Configuration.wf (Configuration.mk ths1_src sc1_src mem1_src))
           (WF_TGT: Configuration.wf (Configuration.mk ths1_tgt sc1_tgt mem1_tgt))
           (CERTIFIED: UndefCertify.certified (Configuration.mk ths1_src sc1_src mem1_src))
           (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
           (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
           (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
           (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt)
           (WORLD: world_le w0 w1)
           (UNCHANGED: forall tid st lc
                              (TID: IdentMap.find tid ths1_src = Some (st, lc)),
               UndefCertify.unchanged lc.(Local.promises) mem0_src mem1_src),
      (<<TERMINAL:
         forall (TERMINAL_TGT: Threads.is_terminal ths1_tgt),
           (<<FAILURE: Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src)>>) \/
           exists ths2_src sc2_src mem2_src w2,
             (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>>) /\
             (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
             (<<MEMORY: sim_memory false w2 mem2_src mem1_tgt>>) /\
             (<<TERMINAL_SRC: Threads.is_terminal ths2_src>>) /\
             (<<WORLD: world_le w1 w2>>)>>) /\
      (<<STEP:
         forall e tid_tgt ths3_tgt sc3_tgt mem3_tgt
                (STEP_TGT: Configuration.step e tid_tgt (Configuration.mk ths1_tgt sc1_tgt mem1_tgt) (Configuration.mk ths3_tgt sc3_tgt mem3_tgt)),
           (<<FAILURE: Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src)>>) \/
           exists tid_src ths2_src sc2_src mem2_src ths3_src sc3_src mem3_src w3,
             (<<STEPS_SRC: rtc Configuration.tau_step (Configuration.mk ths1_src sc1_src mem1_src) (Configuration.mk ths2_src sc2_src mem2_src)>>) /\
             (<<STEP_SRC: Configuration.opt_step e tid_src (Configuration.mk ths2_src sc2_src mem2_src) (Configuration.mk ths3_src sc3_src mem3_src)>>) /\
             (<<SC3: sim_timemap w3 sc3_src sc3_tgt>>) /\
             (<<MEMORY3: sim_memory false w3 mem3_src mem3_tgt>>) /\
             (<<SIM: sim w3 ths3_src sc3_src mem3_src ths3_tgt sc3_tgt mem3_tgt>>) /\
             (<<WORLD: world_le w1 w3>>)>>).

  Lemma _sim_mon: monotone7 _sim.
  Proof.
    ii. exploit IN; try apply SC1; eauto. i. des.
    splits; eauto. i.
    exploit STEP; eauto. i. des; eauto.
    right. esplits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: SIM := paco7 _sim bot7.
End Simulation.
Hint Resolve _sim_mon: paco.


Definition admitt: forall P, P. Admitted.

Lemma sim_adequacy
      ths_src sc_src mem_src
      ths_tgt sc_tgt mem_tgt w
      (WF_SRC: Configuration.wf (Configuration.mk ths_src sc_src mem_src))
      (WF_TGT: Configuration.wf (Configuration.mk ths_tgt sc_tgt mem_tgt))
      (CERTIFIED: UndefCertify.certified (Configuration.mk ths_src sc_src mem_src))      
      (SC: sim_timemap w sc_src sc_tgt)
      (MEMORY: sim_memory false w mem_src mem_tgt)
      (SIM: sim w ths_src sc_src mem_src ths_tgt sc_tgt mem_tgt):
  behaviors Configuration.step (Configuration.mk ths_tgt sc_tgt mem_tgt) <1=
  behaviors Configuration.step (Configuration.mk ths_src sc_src mem_src).
Proof.
  s. i.
  revert w WF_SRC WF_TGT CERTIFIED SC MEMORY SIM.
  revert ths_src sc_src mem_src.
  remember (Configuration.mk ths_tgt sc_tgt mem_tgt).
  revert ths_tgt sc_tgt mem_tgt Heqt.
  induction PR; i; subst.
  - punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit TERMINAL0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + eapply rtc_tau_step_behavior; eauto.
      econs 1. eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3. eauto.
    + inv SIM1; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try apply STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv STEP_SRC. econs 2; [eauto|].
      exploit Configuration.step_future; try apply STEP1; auto. i. des.
      eapply IHPR; eauto.
      eapply UndefCertify.step_certified; eauto.
      eapply UndefCertify.rtc_step_certified; eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM1; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try apply STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv STEP_SRC. econs 3; eauto.
  - destruct c2.
    punfold SIM0. exploit SIM0; eauto; try refl. i. des.
    exploit STEP0; eauto. i. des.
    + inv FAILURE. des.
      eapply rtc_tau_step_behavior; eauto.
      econs 3; eauto.
    + inv SIM1; [|done].
      eapply rtc_tau_step_behavior; eauto.
      exploit Configuration.step_future; try apply STEP; eauto. i. des.
      exploit Configuration.rtc_step_future; eauto. i. des.
      inv STEP_SRC.
      * eapply IHPR; eauto.
        eapply UndefCertify.rtc_step_certified; eauto.
      * econs 4; eauto.
        exploit Configuration.step_future; try apply STEP1; eauto. s. i. des.
        eapply IHPR; eauto.
        eapply UndefCertify.step_certified; eauto.
        eapply UndefCertify.rtc_step_certified; eauto.
Qed.


Lemma sim_future
      ths_src sc1_src sc2_src mem1_src mem2_src
      ths_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt
      w1 w2
      (SIM: sim w1 ths_src sc1_src mem1_src ths_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt)
      (WORLD: world_le w1 w2)
      (UNCHANGED: forall tid st lc
                         (TID: IdentMap.find tid ths_src = Some (st, lc)),
          UndefCertify.unchanged lc.(Local.promises) mem1_src mem2_src):
  sim w2 ths_src sc2_src mem2_src ths_tgt sc2_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
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
      (LOCAL: Local.promises lc2_src = Memory.bot)
      (CERTIFIED: UndefCertify.certified (Configuration.mk ths1_src sc1_src mem1_src)):
  (<<STEPS: rtc Configuration.tau_step
                (Configuration.mk ths1_src sc1_src mem1_src)
                (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) sc2_src mem2_src)>>) /\
  ((<<UNCHANGED: forall tid' st lc
                        (TID: tid' <> tid)
                        (TID: IdentMap.find tid' ths1_src = Some (st, lc)),
       UndefCertify.unchanged lc.(Local.promises) mem1_src mem2_src>>) \/
   (<<FAILURE: Configuration.steps_failure (Configuration.mk ths1_src sc1_src mem1_src)>>))
.
Proof.
  inv WF_SRC. inv WF. ss. exploit THREADS; eauto. i.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  generalize (rtc_tail STEPS). i. des.
  - inv H0. inv TSTEP.
    assert (STEP0: Configuration.step
                     MachineEvent.silent tid
                     (Configuration.mk ths1_src sc1_src mem1_src)
                     (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) sc2_src mem2_src)).
    { rewrite <- EVENT. econs; ss; eauto.
      ii. ss. esplits; eauto. }
    split.
    { econs; eauto. econs; eauto. }
    { ii. eapply (@UndefCertify.step_unchanged
                    (Configuration.mk ths1_src sc1_src mem1_src)
                    (Configuration.mk (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) sc2_src mem2_src)); eauto.
      econs; eauto; ss. }
  - inv H.
    replace (IdentMap.add tid (existT _ lang_src st2_src, lc2_src) ths1_src) with ths1_src; auto.
    { split; auto. left. red. i. refl. }
    apply IdentMap.eq_leibniz. ii.
    rewrite -> IdentMap.gsident; auto.
Qed.

Lemma sim_thread_sim
      ths_src sc0_src mem0_src
      ths_tgt sc0_tgt mem0_tgt w
      (TIDS: Threads.tids ths_src = Threads.tids ths_tgt)
      (SIM: forall tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt,
          IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src) ->
          IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt) ->
          exists sim_terminal,
            @sim_thread_past lang_src lang_tgt sim_terminal false w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt)
  :
    sim w ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt.
Proof.
  remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
  rename TIDS into TIDS_TGT.
  revert w ths_src sc0_src mem0_src ths_tgt sc0_tgt mem0_tgt tids TIDS_SRC TIDS_TGT SIM.
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
                 @sim_thread_past lang_src lang_tgt sim_terminal false w st_src lc_src sc0_src mem0_src st_tgt lc_tgt sc0_tgt mem0_tgt).
    { eauto. }
    assert (UNCHANGED0: forall tid st lc
                               (TID: List.In tid (IdentSet.elements tids))
                               (FIND: IdentMap.find tid ths_src = Some (st, lc)),
               UndefCertify.unchanged (Local.promises lc) mem0_src mem1_src).
    { i. eapply UNCHANGED; eauto. }
    assert (TIDS_MEM: forall tid, List.In tid (IdentSet.elements tids) -> IdentSet.mem tid tids = true).
    { i. rewrite IdentSet.mem_spec.
      rewrite <- IdentSet.elements_spec1.
      eapply SetoidList.In_InA; auto. }
    assert (NODUP: List.NoDup (IdentSet.elements tids)).
    { specialize (IdentSet.elements_spec2w tids). i.
      clear - H. induction H; econs; eauto. }
    revert NOTIN IN TIDS_MEM NODUP.
    move tids at top. clear SIM0 UNCHANGED. revert_until CIH.
    induction (IdentSet.elements tids); i.
    { right. esplits; eauto; try refl. ii. exploit NOTIN; eauto. }
    destruct (IdentMap.find a ths_src) as [[[lang_src st_src] lc_src]|] eqn:ASRC;
      destruct (IdentMap.find a ths_tgt) as [[[lang_tgt st_tgt] lc_tgt]|] eqn:ATGT; cycle 1.
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x0; eauto. i. des. rewrite ATGT in x. inv x. }
    { exploit tids_find; [apply TIDS_SRC|apply TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite ASRC in x. inv x. }
    { exploit IHl; [exact TIDS_SRC|exact TIDS_TGT|exact SC1|exact MEMORY1|..]; eauto; i.
      - eapply UNCHANGED0; eauto. ss. auto.
      - eapply NOTIN; eauto. ii. inv H; ss. congr.
      - eapply IN; eauto. econs 2; eauto.
      - eapply TIDS_MEM; eauto. econs 2; eauto.
      - inv NODUP. ss.
    }
    generalize WF_SRC. intro X. inv X. ss. inv WF. exploit THREADS; eauto. i.
    generalize WF_TGT. intro X. inv X. ss. inv WF. exploit THREADS0; eauto. i.
    exploit (IN a); eauto. i. des.
    exploit TERMINAL_TGT; eauto. i. des.
    hexploit Local.terminal_promise_consistent; eauto. i.
    red in x2. des. punfold SIM0.
    exploit SIM0; try exact x; try exact x0; try exact SC; try exact SC0; eauto.
    { ss. splits; eauto using Memory.future_future_weak.
      { etrans; eauto. eapply Memory.future_future_weak; eauto. }
      { etrans; eauto. eapply Memory.future_future_weak; eauto. }
      { etrans; eauto. }
    }
    { etrans; eauto. }    
    i. des.
    exploit TERMINAL; eauto. i. des.
    + (* failure *)
      left. unfold Thread.steps_failure in FAILURE. des.
      exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
      exploit Thread.step_future; try exact STEP_FAILURE; eauto. s. i. des.
      unfold Configuration.steps_failure.
      destruct e3. ss.
      esplits; [refl|]. rewrite <- EVENT_FAILURE. econs; eauto. destruct e; ss.
    + (* non-failure *)
      exploit thread_rtc_step_rtc_step; try exact STEPS; eauto; i.
      { inv THREAD. eapply sim_local_memory_bot; eauto. } des; auto.
      exploit Configuration.rtc_step_future; try eapply x3; eauto. s. i. des.
      exploit IHl; [| |exact SC2|exact MEMORY|..]; try exact WF2; try exact WF_TGT;
        try exact SC_FUTURE_TGT; try exact MEM_FUTURE_TGT;
          try (etrans; [exact SC_FUTURE_SRC|exact SC_FUTURE]);
          try (etrans; [exact MEM_FUTURE_SRC|exact MEM_FUTURE]); eauto; i.
      { rewrite Threads.tids_add. rewrite IdentSet.add_mem; eauto. }
      { eapply UndefCertify.rtc_step_certified; eauto. }
      { assert (NEQ: tid <> a).
        { inv NODUP. ii. clarify. }
        rewrite IdentMap.gso in FIND; auto.
        transitivity mem1_src. 
        { eapply UNCHANGED0; eauto. }
        { eapply UNCHANGED1; eauto. }
      }
      { rewrite IdentMap.gsspec in FIND. revert FIND. condtac; ss; i.
        - subst. Configuration.simplify. split; auto.
          inv THREAD. econs. eapply sim_local_memory_bot; eauto.
        - eapply NOTIN; eauto. ii. des; ss. subst. ss. }
      { rewrite IdentMap.gsspec in H0. revert H0. condtac; ss; i.
        - subst. inv NODUP. congr.
        - exploit IN; eauto. i. des.
          esplits. eapply sim_thread_future; eauto; try refl. }
      { inv NODUP. ss. }
      des.
      * left.
        unfold Configuration.steps_failure in *. des. esplits; [|eauto].
        etrans; eauto.
      * right. esplits; cycle 1; eauto.
        { etrans; eauto. }
        { etrans; eauto. }

  - (* STEP CASE *)
    i. dup STEP_TGT. inv STEP_TGT. destruct e2. ss.
    destruct (classic (Configuration.steps_failure (Configuration.mk ths_src sc1_src mem1_src))); auto.
    destruct (IdentMap.find tid_tgt ths_src) as [[[lang_src st_src] lc_src]|] eqn:FIND_SRC; cycle 1.
    { remember (Threads.tids ths_src) as tids eqn:TIDS_SRC.
      exploit tids_find; [exact TIDS_SRC|exact TIDS_TGT|..]. i. des.
      exploit x1; eauto. i. des. rewrite FIND_SRC in x. inv x. }
    inv WF_SRC. inv WF_TGT. inv WF. inv WF0. ss.
    exploit SIM0; eauto. i. des.
    exploit sim_thread_future; eauto using Memory.future_future_weak. i.
    exploit sim_thread_plus_step; try exact STEPS; try exact x1;
      eauto using Memory.future_future_weak.
    { s. destruct (classic (ThreadEvent.get_machine_event e0 = MachineEvent.failure)).
      - inv STEP; inv STEP0; ss. inv LOCAL; ss; inv LOCAL0; ss.
      - exploit Thread.rtc_tau_step_future; eauto. s. i. des.
        exploit Thread.step_future; eauto. s. i. des.
        hexploit consistent_promise_consistent; eauto.
    }
    s. i. des.
    + left.
      unfold Thread.steps_failure in FAILURE. des.
      unfold Configuration.steps_failure.
      destruct e3. ss.
      esplits; eauto. rewrite <- EVENT_FAILURE. econs; eauto. destruct e; ss.

    + assert (OPTSTEP: Configuration.opt_step
                         (ThreadEvent.get_machine_event e0) tid_tgt  
                         (Configuration.mk ths_src sc1_src mem1_src)
                         (Configuration.mk (IdentMap.add tid_tgt (existT _ lang_src st3_src, lc3_src) ths_src) sc3_src mem3_src)).
      { inv STEP0.
        { generalize (rtc_tail STEPS0). intro X. des.
          - inv X0. inv TSTEP. ss.
            rewrite <- EVENT0. rewrite <- EVENT1. esplits; eauto.
            + econs 2. econs; eauto. i.
              eapply sim_thread_consistent; eauto.
          - ss. inv X. rewrite IdentMap.gsident; auto.
            rewrite <- EVENT0. ss.
        }
        { rewrite <- EVENT0. econs. econs; eauto.
          i. eapply sim_thread_consistent; eauto.
        }
      }
      exploit Configuration.opt_step_future; eauto.
      { econs; eauto; ss. }
      i. ss. des.
      exploit Configuration.step_future; eauto.
      { econs; eauto; ss. }
      i. ss. des.
      exploit UndefCertify.opt_step_unchanged; eauto.
      { econs; eauto; ss. }
      i. des; auto.
      right. esplits; eauto. right. eapply CIH; ss.
      { rewrite Threads.tids_add. rewrite Threads.tids_add.
        f_equal. auto. }
      { i. apply sim_thread_sim_thread_past in SIM1. Configuration.simplify.
        { esplits; eauto. }
        { exploit SIM0; eauto. i. des. esplits; eauto.
          eapply sim_thread_future; eauto.
          { eapply Memory.future_future_weak. etrans; eauto. }
          { eapply Memory.future_future_weak. etrans; eauto. }
          { etrans; eauto. }
          { etrans; eauto. }
        }
      }
Qed.

End WORLD.
Hint Resolve _sim_thread_mon: paco.
