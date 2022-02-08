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


Section SimulationThread.
  Definition SIM_THREAD :=
    forall (lang_src lang_tgt:language)
           (b: bool) (w: world)
           (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
           (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.


  Definition _sim_thread_promise_step
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
           (CONS_TGT: Local.promise_consistent lc3_tgt)
           (PROMISE: is_promise e_tgt),
    exists st2_src lc2_src sc2_src mem2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) \/
       exists w3,
         (<<SC3: sim_timemap w3 sc2_src sc3_tgt>>) /\
         (<<MEMORY3: sim_memory w3 mem2_src mem3_tgt>>) /\
         (<<SIM: sim_thread false w3 st2_src lc2_src sc2_src mem2_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) (unchangable mem1_tgt lc1_tgt.(Local.promises)) w0 w3>>))
  .

  Definition _sim_thread_cap
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             (w0: world)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt :=
    forall cap_src cap_tgt
           (CAPSRC: Memory.cap mem1_src cap_src)
           (CAPTGT: Memory.cap mem1_tgt cap_tgt),
    exists w3,
      (<<SC3: sim_timemap w3 sc1_src sc1_tgt>>) /\
      (<<MEMORY3: sim_memory w3 cap_src cap_tgt>>) /\
      (<<SIM: sim_thread false w3 st1_src lc1_src sc1_src cap_src st1_tgt lc1_tgt sc1_tgt cap_tgt>>).

  Definition _sim_thread_future
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             (w0: world)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt :=
    forall sc2_src mem2_src sc2_tgt mem2_tgt w1
           (MEMSRC: Memory.future_weak mem1_src mem2_src)
           (MEMTGT: Memory.future_weak mem1_tgt mem2_tgt)
           (SCSRC: TimeMap.le sc1_src sc2_src)
           (SCTGT: TimeMap.le sc1_tgt sc2_tgt)
           (WORLD: world_messages_le (Messages.of_memory lc1_src.(Local.promises)) (Messages.of_memory lc1_tgt.(Local.promises)) w0 w1)
           (SC: sim_timemap w1 sc2_src sc2_tgt)
           (MEMORY: sim_memory w1 mem2_src mem2_tgt)
           (WF_SRC: Local.wf lc1_src mem2_src)
           (WF_TGT: Local.wf lc1_tgt mem2_tgt)
           (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
           (SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt)
           (MEM_SRC: Memory.closed mem2_src)
           (MEM_TGT: Memory.closed mem2_tgt)
           (CONSISTENT: Thread.consistent (Thread.mk _ st1_src lc1_src sc1_src mem1_src)),
    exists st2_src lc2_src sc3_src mem3_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src sc2_src mem2_src)
                    (Thread.mk _ st2_src lc2_src sc3_src mem3_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc3_src mem3_src)>>) \/
       exists w3,
         (<<SC3: sim_timemap w3 sc3_src sc2_tgt>>) /\
         (<<MEMORY3: sim_memory w3 mem3_src mem2_tgt>>) /\
         (<<SIM: sim_thread false w3 st2_src lc2_src sc3_src mem3_src st1_tgt lc1_tgt sc2_tgt mem2_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable mem2_src lc1_src.(Local.promises)) (unchangable mem2_tgt lc1_tgt.(Local.promises)) w1 w3>>))
  .

  Definition _sim_thread_release_step
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
           (CONS_TGT: Local.promise_consistent lc3_tgt)
           (RELEASE: release_event e_tgt),
    exists st2_src lc2_src sc2_src mem2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) \/
       exists e_src st3_src lc3_src sc3_src mem3_src st4_src lc4_src sc4_src mem4_src w3,
         (<<STEP_SRC: Thread.opt_step e_src
                                      (Thread.mk _ st2_src lc2_src sc2_src mem2_src)
                                      (Thread.mk _ st3_src lc3_src sc3_src mem3_src)>>) /\
         (<<STEPS_AFTER: rtc (@Thread.tau_step _)
                             (Thread.mk _ st3_src lc3_src sc3_src mem3_src)
                             (Thread.mk _ st4_src lc4_src sc4_src mem4_src)>>) /\
         (<<EVENT: machine_event_le (ThreadEvent.get_machine_event e_tgt) (ThreadEvent.get_machine_event e_src)>>) /\
         (<<SC3: sim_timemap w3 sc4_src sc3_tgt>>) /\
         (<<MEMORY3: sim_memory w3 mem4_src mem3_tgt>>) /\
         (<<SIM: sim_thread false w3 st4_src lc4_src sc4_src mem4_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) (unchangable mem1_tgt lc1_tgt.(Local.promises)) w0 w3>>))
  .

  Definition _sim_thread_terminal
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             (w0: world)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt :=
    forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt)
           (BOT: lc1_tgt.(Local.promises) = Memory.bot),
    exists st2_src lc2_src sc2_src mem2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) \/
       exists w3,
         (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
         (<<BOT: lc2_src.(Local.promises) = Memory.bot>>) /\
         (<<SC3: sim_timemap w3 sc2_src sc1_tgt>>) /\
         (<<MEMORY3: sim_memory w3 mem2_src mem1_tgt>>) /\
         (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) (unchangable mem1_tgt lc1_tgt.(Local.promises)) w0 w3>>)).

  Definition _sim_thread_certification
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             (w0: world)
             st1_src lc1_src sc1_src mem1_src
             lc1_tgt :=
    forall (BOT: lc1_tgt.(Local.promises) = Memory.bot),
    exists st2_src lc2_src sc2_src mem2_src,
      (<<STEPS: rtc (@Thread.tau_step lang_src)
                    (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) \/
         (<<BOT: lc2_src.(Local.promises) = Memory.bot>>)).

  Definition _sim_thread_lower_step
             (lang_src lang_tgt:language)
             (sim_thread: forall (b1: bool) (w1: world) (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                                 (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop)
             (w0: world)
             st1_src lc1_src sc1_src mem1_src
             st1_tgt lc1_tgt sc1_tgt mem1_tgt :=
    forall e_tgt st3_tgt lc3_tgt sc3_tgt mem3_tgt
           (STEP_TGT: lower_step e_tgt
                                 (Thread.mk _ st1_tgt lc1_tgt sc1_tgt mem1_tgt)
                                 (Thread.mk _ st3_tgt lc3_tgt sc3_tgt mem3_tgt))
           (CONS_TGT: Local.promise_consistent lc3_tgt),
    exists st2_src lc2_src sc2_src mem2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
      ((<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) \/
       exists w3,
         ((<<SIM: sim_thread true w3 st2_src lc2_src sc2_src mem2_src st3_tgt lc3_tgt sc3_tgt mem3_tgt>>) /\
          (<<WORLD: world_messages_le (unchangable mem1_src lc1_src.(Local.promises)) (unchangable mem1_tgt lc1_tgt.(Local.promises)) w0 w3>>)))
  .

  Definition _sim_thread_failure
             (lang_src lang_tgt:language)
             (w0: world)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t) :=
    exists st2_src lc2_src sc2_src mem2_src,
      (<<STEPS: rtc (@Thread.tau_step _)
                    (Thread.mk _ st1_src lc1_src sc0_src mem0_src)
                    (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
        (<<FAILURE: Thread.steps_failure (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>).

  Definition _sim_thread
             (sim_thread: SIM_THREAD)
             (lang_src lang_tgt:language)
             (b0: bool) (w0: world)
             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall
      (WF_SRC: Local.wf lc1_src mem0_src)
      (WF_TGT: Local.wf lc1_tgt mem0_tgt)
      (SC_SRC: Memory.closed_timemap sc0_src mem0_src)
      (SC_TGT: Memory.closed_timemap sc0_tgt mem0_tgt)
      (MEM_SRC: Memory.closed mem0_src)
      (MEM_TGT: Memory.closed mem0_tgt)
      (CONS_TGT: Local.promise_consistent lc1_tgt),
      ((<<RELEASE: _sim_thread_release_step _ _ (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>) /\
         (<<CERTIFICATION: _sim_thread_certification _ lang_tgt (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src lc1_tgt>>) /\
         (<<LOWER: _sim_thread_lower_step _ _ (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>) /\
         (<<TERMINAL: _sim_thread_terminal _ _ (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>) /\
         (<<PROMISE: b0 = false -> _sim_thread_promise_step _ _ (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>) /\
         (<<CAP: b0 = false -> _sim_thread_cap _ _ (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>) /\
         (<<FUTURE: b0 = false -> _sim_thread_future _ _ (@sim_thread _ _) w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>)) \/
        (<<FAILURE: _sim_thread_failure _ _ w0 st1_src lc1_src sc0_src mem0_src st1_tgt lc1_tgt sc0_tgt mem0_tgt>>)
  .

  Lemma _sim_thread_mon: monotone12 _sim_thread.
  Proof.
    ii. red in IN. exploit IN; eauto. i. des; auto.
    left. splits; eauto.
    { ii. exploit RELEASE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
    { ii. exploit LOWER; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. }
    }
    { ii. exploit PROMISE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
    { ii. exploit CAP; eauto. i. des. esplits; eauto. }
    { ii. exploit FUTURE; eauto. i. des.
      { esplits; eauto. }
      { esplits; eauto. right. esplits; eauto. }
    }
  Qed.
  #[local] Hint Resolve _sim_thread_mon: paco.

  Definition sim_thread: SIM_THREAD := paco12 _sim_thread bot12.
End SimulationThread.
#[local] Hint Resolve _sim_thread_mon: paco.


(* Let sim_memory_lift: forall (w: world) (mem_src mem_tgt:Memory.t), Prop := *)
(*       fun w mem_src mem_tgt => *)
(*         exists mem_mid, *)
(*           (<<LOWER: lower_memory mem_mid mem_tgt>>) /\ *)
(*             (<<SIM: sim_memory w mem_src mem_mid>>) *)
(* . *)

(* Let sim_timemap_lift: forall (w: world_lift) (sc_src sc_tgt:Memory.t), Prop := *)
(*       fun '(w, mem_src', mem_mid') sc_src sc_tgt => *)
(*         exists mem_mid, *)
(*           (<<LOWER: lower_memory mem_mid mem_tgt>>) /\ *)
(*             (<<MEMSRC: mem_src = mem_src'>>) /\ *)
(*             (<<MEMMID: mem_mid = mem_mid'>>) /\ *)
(*             (<<SIM: sim_memory w mem_src mem_mid>>). *)


(* Let world_lift: Type := world * Memory.t * Memory.t. *)
(* Let world_lift_messages_le: Messages.t -> Messages.t -> world_lift -> world_lift -> Prop := *)
(*   fun msgs_src msgs_tgt '(w0, mem_src0, mem_mid0) '(w1, mem_src1, mem_mid1) => *)
(*     (<<MEMSRC: Memory.future_weak mem_src0 mem_src1>>) /\ *)
(*       (<<MEMTGT: Memory.future_weak mem_mid0 mem_mid1>>) /\ *)
(*       (<<WORLD: world_messages_le msgs_src msgs_tgt w0 w1>>). *)

(* Let world_lift_messages_le_PreOrder: forall msgs_src msgs_tgt, PreOrder (world_lift_messages_le msgs_src msgs_tgt). *)
(* Proof. *)
(*   unfold world_lift_messages_le. *)
(*   i. econs. *)
(*   { ii. des_ifs. splits; auto; refl. } *)
(*   { ii. des_ifs. des. splits; auto; etrans; eauto. } *)
(* Qed. *)

(* Local Existing Instances world_lift_messages_le_PreOrder. *)

(* Let world_lift_messages_le_mon: *)
(*   forall msgs_src0 msgs_tgt0 msgs_src1 msgs_tgt1 w0 w1 *)
(*          (LE: world_lift_messages_le msgs_src1 msgs_tgt1 w0 w1) *)
(*          (MSGSRC: msgs_src0 <4= msgs_src1) *)
(*          (MSGTGT: msgs_tgt0 <4= msgs_tgt1), *)
(*     world_lift_messages_le msgs_src0 msgs_tgt0 w0 w1. *)
(* Proof. *)
(*   unfold world_lift_messages_le. i. des_ifs. des. splits; auto. *)
(*   eapply world_messages_le_mon; eauto. *)
(* Qed. *)

(* Let sim_memory_lift: forall (w: world_lift) (mem_src mem_tgt:Memory.t), Prop := *)
(*       fun '(w, mem_src', mem_mid') mem_src mem_tgt => *)
(*         exists mem_mid, *)
(*           (<<LOWER: lower_memory mem_mid mem_tgt>>) /\ *)
(*             (<<MEMSRC: mem_src = mem_src'>>) /\ *)
(*             (<<MEMMID: mem_mid = mem_mid'>>) /\ *)
(*             (<<SIM: sim_memory w mem_src mem_mid>>). *)

(* Let sim_timemap_lift: forall (w: world_lift) (sc_src sc_tgt:Memory.t), Prop := *)
(*       fun '(w, mem_src', mem_mid') sc_src sc_tgt => *)
(*         exists mem_mid, *)
(*           (<<LOWER: lower_memory mem_mid mem_tgt>>) /\ *)
(*             (<<MEMSRC: mem_src = mem_src'>>) /\ *)
(*             (<<MEMMID: mem_mid = mem_mid'>>) /\ *)
(*             (<<SIM: sim_memory w mem_src mem_mid>>). *)

End WORLD.
#[export] Hint Resolve _sim_thread_mon: paco.
