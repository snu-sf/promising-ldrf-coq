Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.

Set Implicit Arguments.


Section SimulationThread.
  Variable (lang_src lang_tgt:Language.t).

  Definition SIM_TERMINAL :=
    forall (st_src:lang_src.(Language.state)) (st_tgt:lang_tgt.(Language.state)), Prop.

  Definition SIM_THREAD :=
    forall (sim_terminal: SIM_TERMINAL)
      (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
      (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.

  Definition _sim_thread_step
             (sim_thread: forall (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                            (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt
    :=
    forall pf_tgt e_tgt st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP_TGT: Thread.step pf_tgt e_tgt
                             (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                             (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt)),
    exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
      <<STEPS: rtc (@Thread.tau_step _)
                   (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                   (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
      <<STEP_SRC: Thread.opt_step e_src
                                  (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                                  (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
      <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
      <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
      <<MEMORY3: sim_memory mem3_src mem3_tgt>> /\
      <<SIM: sim_thread st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (sim_terminal: SIM_TERMINAL)
             (st1_src:lang_src.(Language.state)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:lang_tgt.(Language.state)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall sc1_src mem1_src
      sc1_tgt mem1_tgt
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
      (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
      (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
      (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (HALF_WF1_SRC: Memory.half_wf mem1_src)
      (HALF_WF1_TGT: Memory.half_wf mem1_tgt),
      <<TERMINAL:
        forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st1_tgt),
        exists st2_src lc2_src sc2_src mem2_src,
          <<STEPS: rtc (@Thread.tau_step _)
                       (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                       (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
          <<SC: TimeMap.le sc2_src sc1_tgt>> /\
          <<MEMORY: sim_memory mem2_src mem1_tgt>> /\
          <<TERMINAL_SRC: lang_src.(Language.is_terminal) st2_src>> /\
          <<LOCAL: sim_local SimPromises.bot lc2_src lc1_tgt>> /\
          <<TERMINAL: sim_terminal st2_src st1_tgt>>>> /\
      <<CONCRETE:
        forall mem2_src
          (CONCRETE_SRC: Memory.concrete_exact mem1_src mem2_src)
          (WF_SRC: Local.wf lc1_src mem2_src)
          (MEM_SRC: Memory.closed mem2_src)
          (NOHALF_SRC: Memory.no_half lc1_src.(Local.promises) mem2_src),
        exists mem2_tgt,
          <<MEMORY: sim_memory mem2_src mem2_tgt>> /\
          <<CONCRETE_TGT: Memory.concrete_exact mem1_tgt mem2_tgt>> /\
          <<WF_TGT: Local.wf lc1_tgt mem2_tgt>> /\
          <<MEM_TGT: Memory.closed mem2_tgt>> /\
          <<HALF_WF_TGT: Memory.half_wf mem2_tgt>> /\
          <<NOHALF_TGT: Memory.no_half lc1_tgt.(Local.promises) mem2_tgt>>>> /\
      <<PROMISES:
        forall (PROMISES_TGT: lc1_tgt.(Local.promises) = Memory.bot)
          (NOHALF_TGT: Memory.no_half lc1_tgt.(Local.promises) mem1_tgt),
        exists st2_src lc2_src sc2_src mem2_src,
          <<STEPS: rtc (@Thread.tau_step _)
                       (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                       (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
          <<PROMISES_SRC: lc2_src.(Local.promises) = Memory.bot>>>> /\
      <<STEP: _sim_thread_step (sim_thread sim_terminal)
                               st1_src lc1_src sc1_src mem1_src
                               st1_tgt lc1_tgt sc1_tgt mem1_tgt>>.

  Lemma _sim_thread_mon: monotone9 _sim_thread.
  Proof.
    ii. exploit IN; try apply SC; eauto. i. des.
    splits; eauto. ii.
    exploit STEP; eauto. i. des.
    esplits; eauto.
  Qed.
  Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco9 _sim_thread bot9.

  Lemma sim_thread_mon
        sim_terminal1 sim_terminal2
        (SIM: sim_terminal1 <2= sim_terminal2):
    sim_thread sim_terminal1 <8= sim_thread sim_terminal2.
  Proof.
    pcofix CIH. i. punfold PR. pfold. ii.
    exploit PR; try apply SC; eauto. i. des.
    splits; auto.
    - i. exploit TERMINAL; eauto. i. des.
      esplits; eauto.
    - ii. exploit STEP; eauto. i. des. inv SIM0; [|done].
      esplits; eauto.
  Qed.
End SimulationThread.
Hint Resolve _sim_thread_mon: paco.


Lemma sim_thread_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt
                          (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                          (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (HALF_WF_SRC: Memory.half_wf mem1_src)
      (HALF_WF_TGT: Memory.half_wf mem1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<HALF_WF_SRC: Memory.half_wf mem3_src>> /\
    <<HALF_WF_TGT: Memory.half_wf mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  punfold SIM. exploit SIM; eauto; try refl. i. des.
  exploit Thread.step_future; eauto. s. i. des.
  exploit STEP0; eauto. i. des. inv SIM0; [|done].
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit Thread.opt_step_future; eauto. s. i. des.
  esplits; eauto.
Qed.

Lemma sim_thread_opt_step
      lang_src lang_tgt
      sim_terminal
      e_tgt
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      st3_tgt lc3_tgt sc3_tgt mem3_tgt
      (STEP: @Thread.opt_step lang_tgt e_tgt
                              (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                              (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
      (SC: TimeMap.le sc1_src sc1_tgt)
      (MEMORY: sim_memory mem1_src mem1_tgt)
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed mem1_tgt)
      (HALF_WF_SRC: Memory.half_wf mem1_src)
      (HALF_WF_TGT: Memory.half_wf mem1_tgt)
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEMORY: sim_memory mem3_src mem3_tgt>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf lc3_tgt mem3_tgt>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap sc3_tgt mem3_tgt>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed mem3_tgt>> /\
    <<HALF_WF_SRC: Memory.half_wf mem3_src>> /\
    <<HALF_WF_TGT: Memory.half_wf mem3_tgt>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>.
Proof.
  inv STEP.
  - esplits; eauto. econs 1.
  - eapply sim_thread_step; eauto.
Qed.

Lemma sim_thread_rtc_step
      lang_src lang_tgt
      sim_terminal
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (SC: TimeMap.le sc1_src e1_tgt.(Thread.sc))
      (MEMORY: sim_memory mem1_src e1_tgt.(Thread.memory))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed e1_tgt.(Thread.memory))
      (HALF_WF_SRC: Memory.half_wf mem1_src)
      (HALF_WF_TGT: Memory.half_wf e1_tgt.(Thread.memory))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src e1_tgt.(Thread.state) e1_tgt.(Thread.local) e1_tgt.(Thread.sc) e1_tgt.(Thread.memory)):
  exists st2_src lc2_src sc2_src mem2_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<SC: TimeMap.le sc2_src e2_tgt.(Thread.sc)>> /\
    <<MEMORY: sim_memory mem2_src e2_tgt.(Thread.memory)>> /\
    <<WF_SRC: Local.wf lc2_src mem2_src>> /\
    <<WF_TGT: Local.wf e2_tgt.(Thread.local) e2_tgt.(Thread.memory)>> /\
    <<SC_SRC: Memory.closed_timemap sc2_src mem2_src>> /\
    <<SC_TGT: Memory.closed_timemap e2_tgt.(Thread.sc) e2_tgt.(Thread.memory)>> /\
    <<MEM_SRC: Memory.closed mem2_src>> /\
    <<MEM_TGT: Memory.closed e2_tgt.(Thread.memory)>> /\
    <<HALF_WF_SRC: Memory.half_wf mem2_src>> /\
    <<HALF_WF_TGT: Memory.half_wf e2_tgt.(Thread.memory)>> /\
    <<SIM: sim_thread sim_terminal st2_src lc2_src sc2_src mem2_src e2_tgt.(Thread.state) e2_tgt.(Thread.local) e2_tgt.(Thread.sc) e2_tgt.(Thread.memory)>>.
Proof.
  revert SC MEMORY WF_SRC WF_TGT SC_SRC SC_TGT MEM_SRC MEM_TGT HALF_WF_SRC HALF_WF_TGT SIM.
  revert st1_src lc1_src sc1_src mem1_src.
  induction STEPS; i.
  { esplits; eauto. }
  inv H. inv TSTEP. destruct x, y. ss.
  exploit sim_thread_step; eauto. i. des.
  exploit IHSTEPS; eauto. i. des.
  destruct z. ss.
  esplits; try apply MEMORY1; eauto.
  etrans; [eauto|]. etrans; [|eauto]. inv STEP0; eauto.
  econs 2; eauto. econs.
  - econs. eauto.
  - etrans; eauto.
Qed.

Lemma sim_thread_plus_step
      lang_src lang_tgt
      sim_terminal
      pf_tgt e_tgt
      st1_src lc1_src sc1_src mem1_src
      e1_tgt e2_tgt e3_tgt
      (STEPS: rtc (@Thread.tau_step lang_tgt) e1_tgt e2_tgt)
      (STEP: @Thread.step lang_tgt pf_tgt e_tgt e2_tgt e3_tgt)
      (SC: TimeMap.le sc1_src e1_tgt.(Thread.sc))
      (MEMORY: sim_memory mem1_src e1_tgt.(Thread.memory))
      (WF_SRC: Local.wf lc1_src mem1_src)
      (WF_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
      (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
      (MEM_SRC: Memory.closed mem1_src)
      (MEM_TGT: Memory.closed e1_tgt.(Thread.memory))
      (HALF_WF_SRC: Memory.half_wf mem1_src)
      (HALF_WF_TGT: Memory.half_wf e1_tgt.(Thread.memory))
      (SIM: sim_thread sim_terminal st1_src lc1_src sc1_src mem1_src e1_tgt.(Thread.state) e1_tgt.(Thread.local) e1_tgt.(Thread.sc) e1_tgt.(Thread.memory)):
  exists e_src st2_src lc2_src sc2_src mem2_src st3_src lc3_src sc3_src mem3_src,
    <<STEPS: rtc (@Thread.tau_step lang_src)
                 (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                 (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>> /\
    <<STEP: Thread.opt_step e_src
                            (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                            (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>> /\
    <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
    <<SC: TimeMap.le sc3_src e3_tgt.(Thread.sc)>> /\
    <<MEMORY: sim_memory mem3_src e3_tgt.(Thread.memory)>> /\
    <<WF_SRC: Local.wf lc3_src mem3_src>> /\
    <<WF_TGT: Local.wf e3_tgt.(Thread.local) e3_tgt.(Thread.memory)>> /\
    <<SC_SRC: Memory.closed_timemap sc3_src mem3_src>> /\
    <<SC_TGT: Memory.closed_timemap e3_tgt.(Thread.sc) e3_tgt.(Thread.memory)>> /\
    <<MEM_SRC: Memory.closed mem3_src>> /\
    <<MEM_TGT: Memory.closed e3_tgt.(Thread.memory)>> /\
    <<HALF_WF_SRC: Memory.half_wf mem3_src>> /\
    <<HALF_WF_TGT: Memory.half_wf e3_tgt.(Thread.memory)>> /\
    <<SIM: sim_thread sim_terminal st3_src lc3_src sc3_src mem3_src e3_tgt.(Thread.state) e3_tgt.(Thread.local) e3_tgt.(Thread.sc) e3_tgt.(Thread.memory)>>.
Proof.
  destruct e1_tgt, e2_tgt, e3_tgt. ss.
  exploit sim_thread_rtc_step; eauto. s. i. des.
  exploit Thread.rtc_tau_step_future; try exact STEPS; eauto. s. i. des.
  exploit Thread.rtc_tau_step_future; try exact STEPS0; eauto. s. i. des.
  exploit sim_thread_step; try exact STEP; try exact SIM0; eauto. s. i. des.
  rewrite STEPS1 in STEPS0.
  esplits; try exact STEPS0; try exact STEP0; eauto.
Qed.

Lemma sim_thread_future
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc1_src sc2_src mem1_src mem2_src
      st_tgt lc_tgt sc1_tgt sc2_tgt mem1_tgt mem2_tgt
      (SIM: @sim_thread lang_src lang_tgt sim_terminal st_src lc_src sc1_src mem1_src st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt):
  sim_thread sim_terminal st_src lc_src sc2_src mem2_src st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  pfold. ii.
  punfold SIM. exploit SIM; (try by etrans; eauto); eauto.
Qed.

Lemma sim_thread_consistent
      lang_src lang_tgt
      sim_terminal
      st_src lc_src sc_src mem_src
      st_tgt lc_tgt sc_tgt mem_tgt
      (SIM: sim_thread sim_terminal st_src lc_src sc_src mem_src st_tgt lc_tgt sc_tgt mem_tgt)
      (SC: TimeMap.le sc_src sc_tgt)
      (MEMORY: sim_memory mem_src mem_tgt)
      (WF_SRC: Local.wf lc_src mem_src)
      (WF_TGT: Local.wf lc_tgt mem_tgt)
      (SC_SRC: Memory.closed_timemap sc_src mem_src)
      (SC_TGT: Memory.closed_timemap sc_tgt mem_tgt)
      (MEM_SRC: Memory.closed mem_src)
      (MEM_TGT: Memory.closed mem_tgt)
      (HALF_WF_SRC: Memory.half_wf mem_src)
      (HALF_WF_TGT: Memory.half_wf mem_tgt)
      (CONSISTENT: Thread.consistent (Thread.mk lang_tgt st_tgt lc_tgt sc_tgt mem_tgt)):
  Thread.consistent (Thread.mk lang_src st_src lc_src sc_src mem_src).
Proof.
  generalize SIM. intro X.
  punfold X. exploit X; eauto; try refl. i. des.
  ii. ss. exploit CONCRETE; eauto. i. des.
  exploit CONSISTENT; eauto; try refl. i. des.
  exploit sim_thread_rtc_step; try apply MEMORY0;
    eauto using Memory.concrete_exact_closed_timemap; s.
  { eapply Memory.concrete_exact_half_wf; eauto. }
  { eapply sim_thread_future; eauto; try refl.
    - eapply Memory.no_half_concrete_exact_future; eauto;
        try apply WF_SRC; try apply WF.
    - eapply Memory.no_half_concrete_exact_future; eauto;
        try apply WF_TGT; try apply WF_TGT0. }
  i. des. destruct e2. ss.
  hexploit Thread.rtc_tau_step_no_half; try exact STEPS; eauto. s. i. des.
  punfold SIM0. exploit SIM0; eauto; try refl. i. des.
  exploit PROMISES1; eauto. i. des.
  eexists (Thread.mk _ _ _ _ _). splits; [|eauto].
  etrans; eauto.
Qed.
