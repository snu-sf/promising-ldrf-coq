Require Import RelationClasses.
Require Import Program.

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

Require Import PromiseConsistent.
Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import JoinedView.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.
Require Import LowerMemory.
Require Import FulfillStep.
Require Import ReorderStepPromise.
Require Import Trace.

Require Import gSimAux.

Set Implicit Arguments.


Definition is_promise (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.promise _ _ _ _ _ => True
  | _ => False
  end.

Definition release_event (e: ThreadEvent.t): Prop :=
  match e with
  | ThreadEvent.update _ _ _ _ _ _ _ _ ordw => Ordering.le Ordering.strong_relaxed ordw
  | ThreadEvent.write _ _ _ _ _ ord => Ordering.le Ordering.strong_relaxed ord
  | ThreadEvent.fence _ ordw => Ordering.le Ordering.strong_relaxed ordw
  | ThreadEvent.syscall _ => True
  | ThreadEvent.failure => True
  | ThreadEvent.racy_write _ _ _ => True
  | ThreadEvent.racy_update _ _ _ _ _ => True
  | _ => False
  end.

Variant lower_step {lang} e (th0 th1: Thread.t lang): Prop :=
| lower_step_intro
    (STEP: Thread.program_step e th0 th1)
    (NRELEASE: ~ release_event e)
    (MEM: lower_memory th1.(Thread.memory) th0.(Thread.memory))
.

Lemma lower_step_step lang:
  (@lower_step lang) <3= (@Thread.step lang true).
Proof.
  i. inv PR. econs 2. ss.
Qed.

Lemma tau_lower_step_tau_step lang:
  tau (@lower_step lang) <2= (@Thread.tau_step lang).
Proof.
  apply tau_mon.
  i. inv PR. econs. econs 2. ss.
Qed.

Lemma write_lower_memory_lower
      prom0 mem0 loc from to msg prom1 mem1 kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (LOWER: lower_memory mem1 mem0):
  Memory.op_kind_is_lower kind.
Proof.
  inv WRITE. inv PROMISE; eauto.
  { eapply Memory.add_get0 in MEM. des.
    hexploit lower_memory_get_inv; eauto. i. des; clarify. }
  { eapply Memory.split_get0 in MEM. des.
    hexploit lower_memory_get_inv; try apply GET1; eauto. i. des; clarify. }
  { eapply Memory.remove_get0 in MEM. des.
    hexploit lower_memory_get; eauto. i. des; clarify. }
Qed.

Lemma write_na_future
      ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind
      (WRITE: Memory.write_na ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind):
  Memory.future mem0 mem1.
Proof.
  induction WRITE.
  - inv WRITE. exploit Memory.promise_op; eauto. i.
    econs 2; eauto. econs; eauto.
    econs. apply Time.bot_spec.
  - etrans; try exact IHWRITE.
    inv WRITE_EX. exploit Memory.promise_op; eauto. i.
    econs 2; eauto. econs; eauto.
    + unguard. des; subst; ss. econs. ss.
    + unguard. des; subst; ss. econs. apply Time.bot_spec.
Qed.

Lemma write_na_lower_memory_lower
      ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind
      (WRITE: Memory.write_na ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind)
      (LOWER: lower_memory mem1 mem0)
  :
    (<<KINDS: List.Forall (fun kind => Memory.op_kind_is_lower kind) kinds>>) /\
    (<<KIND: Memory.op_kind_is_lower kind>>).
Proof.
  induction WRITE; eauto using write_lower_memory_lower.
  exploit write_na_future; try exact WRITE. i.
  inv WRITE_EX. inv PROMISE.
  - exploit Memory.add_get0; try exact MEM. i. des.
    exploit Memory.future_get1; try exact GET0; eauto.
    { unguard. des; subst; ss. }
    i. des.
    inv LOWER. exploit LOWER0.
    erewrite GET. erewrite GET1. i. inv x.
  - exploit Memory.split_get0; try exact MEM. i. des.
    exploit Memory.future_get1; try exact GET1; eauto. i. des.
    inv LOWER. exploit LOWER0.
    erewrite GET. erewrite GET3. i. inv x.
  - cut (lower_memory mem2 mem').
    { i. exploit IHWRITE; eauto. i. des. auto. }
    econs. i.
    erewrite (@Memory.lower_o mem'); eauto. condtac; ss.
    + des. subst.
      exploit Memory.lower_get0; try exact MEM. i. des.
      exploit Memory.future_get1; try exact GET0; eauto. i. des.
      inv LOWER. exploit LOWER0. erewrite GET. i. inv x.
      rewrite <- H0 in *. inv GET1. econs. eauto.
    + inv LOWER. eauto.
  - unguard. des; subst; ss.
Qed.

Lemma write_step_lower_memory_lower
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (LOWER: lower_memory mem2 mem1):
  Memory.op_kind_is_lower kind.
Proof.
  inv STEP. eapply write_lower_memory_lower; eauto.
Qed.

Lemma write_na_step_lower_memory_lower
      lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind
      (STEP: Local.write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind)
      (LOWER: lower_memory mem2 mem1):
  (<<KINDS: List.Forall (fun kind => Memory.op_kind_is_lower kind) kinds>>) /\
  (<<KIND: Memory.op_kind_is_lower kind>>).
Proof.
  inv STEP. eapply write_na_lower_memory_lower; eauto.
Qed.

Lemma write_lower_lower_memory
      promises1 mem1 loc from to msg promises2 mem2 kind
      (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind)
      (KIND: Memory.op_kind_is_lower kind):
  lower_memory mem2 mem1.
Proof.
  inv WRITE. inv PROMISE; ss. econs. i.
  erewrite (@Memory.lower_o mem2); eauto.
  condtac; ss; try refl. des. subst.
  exploit Memory.lower_get0; try exact MEM. i. des.
  rewrite GET. econs. ss.
Qed.

Lemma write_na_lower_lower_memory
      ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
      (WRITE: Memory.write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind)
      (KINDS: List.Forall (fun kind => Memory.op_kind_is_lower kind) kinds)
      (KIND: Memory.op_kind_is_lower kind):
  lower_memory mem2 mem1.
Proof.
  induction WRITE; eauto using write_lower_lower_memory.
  inv KINDS. etrans; try eapply IHWRITE; eauto.
  eapply write_lower_lower_memory; eauto.
Qed.

Lemma write_step_lower_lower_memory
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (KIND: Memory.op_kind_is_lower kind):
  lower_memory mem2 mem1.
Proof.
  inv STEP. eapply write_lower_lower_memory; eauto.
Qed.

Lemma write_na_step_lower_lower_memory
      lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind
      (STEP: Local.write_na_step lc1 sc1 mem1 loc from to val ord lc2 sc2 mem2 msgs kinds kind)
      (KINDS: List.Forall (fun kind => Memory.op_kind_is_lower kind) kinds)
      (KIND: Memory.op_kind_is_lower kind):
  lower_memory mem2 mem1.
Proof.
  inv STEP. eapply write_na_lower_lower_memory; eauto.
Qed.


Lemma lower_memory_promise_step
      lang pf e
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      lc1' mem1'
      (LC1: lower_local lc1' lc1)
      (MEM1: lower_memory mem1' mem1)
      (STEP: Thread.step pf e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (PROMISE: is_promise e)
      (WF1: Local.wf lc1' mem1'):
  exists lc2' mem2',
    (<<STEP: Thread.step pf e (Thread.mk lang st1 lc1' sc1 mem1') (Thread.mk lang st2 lc2' sc2 mem2')>>) /\
    (<<LC2: lower_local lc2' lc2>>) /\
    (<<MEM2: lower_memory mem2' mem2>>).
Proof.
  inv STEP; inv STEP0; [|inv LOCAL; ss].
  exploit lower_memory_promise_step; try apply WF1; eauto. i. des.
  esplits; eauto.
  econs 1. econs; eauto.
Qed.

Lemma lower_memory_promise_steps
      lang tr
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      lc1' mem1'
      (LC1: lower_local lc1' lc1)
      (MEM1: lower_memory mem1' mem1)
      (STEP: Trace.steps tr (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (PROMISE: List.Forall (fun x => is_promise (snd x)) tr)
      (WF1: Local.wf lc1' mem1')
      (SC1: Memory.closed_timemap sc1 mem1')
      (CLOSED1: Memory.closed mem1'):
  exists tr' lc2' mem2',
    (<<STEP: Trace.steps tr' (Thread.mk lang st1 lc1' sc1 mem1') (Thread.mk lang st2 lc2' sc2 mem2')>>) /\
    (<<EVENTS: List.Forall2 (fun x y => snd x = snd y) tr tr'>>) /\
    (<<LC2: lower_local lc2' lc2>>) /\
    (<<MEM2: lower_memory mem2' mem2>>).
Proof.
  revert lc1' mem1' LC1 MEM1 WF1 SC1 CLOSED1.
  dependent induction STEP; i.
  { esplits; eauto. }
  inv PROMISE. destruct th1. ss.
  exploit lower_memory_promise_step; try exact STEP; eauto. i. des.
  exploit Thread.step_future; try exact STEP1; eauto. s. i. des.
  exploit IHSTEP; eauto. i. des.
  esplits.
  - econs 2; eauto.
  - econs 2; eauto.
  - ss.
  - ss.
Qed.

Lemma lower_memory_lower_step
      lang e
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      lc1' mem1'
      (LC1: lower_local lc1' lc1)
      (MEM1: lower_memory mem1' mem1)
      (STEP: lower_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (WF1: Local.wf lc1 mem1)
      (WF1': Local.wf lc1' mem1')
      (CLOSED: Memory.closed mem1)
      (CLOSED1': Memory.closed mem1'):
  exists e' lc2' mem2',
    (<<STEP: lower_step e' (Thread.mk lang st1 lc1' sc1 mem1') (Thread.mk lang st2 lc2' sc2 mem2')>>) /\
    (<<EVENT: JSim.sim_event e' e>>) /\
    (<<LC2: lower_local lc2' lc2>>) /\
    (<<MEM2: lower_memory mem2' mem2>>).
Proof.
  inv STEP. inv STEP0. inv LOCAL; ss.
  { esplits.
    - econs; [econs; try econs 1|..]; eauto; ss. refl.
    - ss.
    - ss.
    - ss.
  }

  { exploit lower_memory_read_step; try exact MEM1; eauto. i. des.
    esplits.
    - econs; [econs; try econs 2|..]; eauto; ss. refl.
    - econs. ss.
    - ss.
    - ss.
  }

  { exploit lower_memory_write_step; try exact MEM1; eauto; try refl. i. des.
    replace sc_src1 with sc2 in *; cycle 1.
    { inv LOCAL0. inv STEP. ss. }
    esplits.
    - econs; [econs; try econs 3|..]; eauto; ss.
      exploit write_step_lower_memory_lower; try exact LOCAL0; eauto. i.
      inv KIND; ss.
      eapply write_step_lower_lower_memory; eauto.
    - econs. ss.
    - ss.
    - ss.
  }

  { exploit lower_memory_read_step; try exact MEM1; eauto; try refl. i. des.
    exploit Local.read_step_future; try exact LOCAL1; eauto. i. des.
    exploit Local.read_step_future; try exact STEP; eauto. i. des.
    exploit lower_memory_write_step; try exact MEM1; eauto; try refl. i. des.
    replace sc_src1 with sc2 in *; cycle 1.
    { inv LOCAL2. inv STEP0. ss. }
    esplits.
    - econs; [econs; try econs 4|..]; eauto; ss.
      exploit write_step_lower_memory_lower; try exact LOCAL2; eauto. i.
      inv KIND; ss.
      eapply write_step_lower_lower_memory; eauto.
    - econs; ss.
    - ss.
    - ss.
  }

  { exploit lower_memory_fence_step; try exact LC1; eauto; try refl. i. des.
    replace sc_src1 with sc2 in *; cycle 1.
    { inv LOCAL0. inv STEP. 
      unfold TView.write_fence_sc. condtac; ss. destruct ordw; ss.
    }
    esplits.
    - econs; [econs; try econs 5|..]; eauto; ss. refl.
    - ss.
    - ss.
    - ss.
  }

  { exploit lower_memory_write_na_step; try exact MEM1; eauto; try refl. i. des.
    replace sc_src1 with sc2 in *; cycle 1.
    { inv LOCAL0. inv STEP. ss. }
    esplits.
    - econs; [econs; try econs 8|..]; eauto; ss.
      exploit write_na_step_lower_memory_lower; try exact LOCAL0; eauto. i. des.
      eapply write_na_step_lower_lower_memory; eauto.
      { clear - KINDS KINDS0.
        induction KINDS; ss.
        inv KINDS0. inv H; ss. econs; ss. eauto.
      }
      { inv KIND; ss. }
    - econs; ss.
    - ss.
    - ss.
  }

  { exploit lower_memory_is_racy; try exact MEM1; try eapply LOCAL0; eauto. i.
    esplits.
    - econs; [econs; try econs 9|..]; eauto; ss. refl.
    - ss.
    - ss.
    - ss.
  }
Qed.

Lemma lower_memory_lower_steps
      lang
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      lc1' mem1'
      (LC1: lower_local lc1' lc1)
      (MEM1: lower_memory mem1' mem1)
      (STEP: rtc (tau lower_step) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (WF1: Local.wf lc1 mem1)
      (WF1': Local.wf lc1' mem1')
      (SC1: Memory.closed_timemap sc1 mem1)
      (SC1': Memory.closed_timemap sc1 mem1')
      (CLOSED: Memory.closed mem1)
      (CLOSED1': Memory.closed mem1'):
  exists lc2' mem2',
    (<<STEP: rtc (tau lower_step) (Thread.mk lang st1 lc1' sc1 mem1') (Thread.mk lang st2 lc2' sc2 mem2')>>) /\
    (<<LC2: lower_local lc2' lc2>>) /\
    (<<MEM2: lower_memory mem2' mem2>>).
Proof.
  revert lc1' mem1' LC1 MEM1 WF1' SC1' CLOSED1'.
  dependent induction STEP; i.
  { esplits; eauto. }
  inv H. destruct y.
  exploit lower_memory_lower_step; try exact TSTEP; eauto. i. des.
  exploit Thread.step_future; try eapply lower_step_step; try exact TSTEP; eauto. s. i. des.
  exploit Thread.step_future; try eapply lower_step_step; try exact STEP0; eauto. s. i. des.
  exploit IHSTEP; eauto. i. des.
  esplits.
  - econs 2; eauto. econs; eauto. inv EVENT0; ss.
  - ss.
  - ss.
Qed.

Lemma same_memory_promise_step
      lang pf pf' e
      (th1 th2 th1' th2': Thread.t lang)
      (STEP: Thread.step pf e th1 th2)
      (STEP': Thread.step pf' e th1' th2')
      (PROMISE: is_promise e)
      (MEM: th1.(Thread.memory) = th1'.(Thread.memory)):
  th2.(Thread.memory) = th2'.(Thread.memory).
Proof.
  inv STEP; inv STEP0; try by inv LOCAL; ss.
  inv STEP'; inv STEP; try by inv LOCAL0; ss.
  inv LOCAL. inv LOCAL0. ss. subst.
  exploit Memory.promise_op; try exact PROMISE0. i.
  exploit Memory.promise_op; try exact PROMISE1. i.
  eapply Memory.op_inj; eauto.
Qed.

Lemma same_memory_promise_steps
      lang tr tr'
      (th1 th2 th1' th2': Thread.t lang)
      (STEP: Trace.steps tr th1 th2)
      (STEP': Trace.steps tr' th1' th2')
      (PROMISE: List.Forall (fun x => is_promise (snd x)) tr)
      (TRACE: List.Forall2 (fun x y => snd x = snd y) tr tr')
      (MEM: th1.(Thread.memory) = th1'.(Thread.memory)):
  th2.(Thread.memory) = th2'.(Thread.memory).
Proof.
  revert tr' th1' th2' STEP' TRACE MEM.
  induction STEP; i.
  { inv TRACE. inv STEP'; ss. }
  subst. inv PROMISE. inv TRACE. inv STEP'. inv TR. ss. subst.
  exploit same_memory_promise_step; try exact MEM; eauto.
Qed.

Lemma promise_steps_trace_promise_steps
      lang (th1 th2: Thread.t lang)
      (STEPS: rtc (tau (@pred_step is_promise _)) th1 th2):
  exists tr,
    (<<STEPS: Trace.steps tr th1 th2>>) /\
    (<<PROMISE: List.Forall (fun x => is_promise (snd x)) tr>>).
Proof.
  induction STEPS; eauto.
  des. inv H. inv TSTEP. inv STEP.
  esplits; eauto.
Qed.

Lemma trace_promise_steps_promise_steps
      lang tr (th1 th2: Thread.t lang)
      (STEPS: Trace.steps tr th1 th2)
      (PROMISE: List.Forall (fun x => is_promise (snd x)) tr):
  rtc (tau (@pred_step is_promise _)) th1 th2.
Proof.
  induction STEPS; eauto.
  inv PROMISE; ss. inv H1.
  exploit IHSTEPS; eauto. i.
  etrans; try exact x.
  econs 2; try refl. econs.
  - econs; eauto. econs; eauto.
  - destruct e; ss.
Qed.

Lemma Forall2_refl
      A (f: A -> A -> Prop) (a: list A)
      (REFL: forall x, f x x):
  List.Forall2 f a a.
Proof.
  induction a; eauto.
Qed.

Lemma Forall2_trans
      A (f: A -> A -> Prop) (a b c: list A)
      (TRANS: forall x y z, f x y -> f y z -> f x z)
      (FORALL1: List.Forall2 f a b)
      (FORALL2: List.Forall2 f b c):
  List.Forall2 f a c.
Proof.
  revert c FORALL2.
  induction FORALL1; eauto. i.
  inv FORALL2. econs; eauto.
Qed.

Lemma trace_eq_promise
      (tr1 tr2: Trace.t)
      (EQ: List.Forall2 (fun x y => snd x = snd y) tr1 tr2)
      (PROMISE1: List.Forall (fun x => is_promise (snd x)) tr1):
  List.Forall (fun x => is_promise (snd x)) tr2.
Proof.
  induction EQ; eauto.
  inv PROMISE1. econs; eauto. congr.
Qed.

Lemma promise_step_sc
      lang pf e (th1 th2: Thread.t lang)
      (STEP: Thread.step pf e th1 th2)
      (PROMISE: is_promise e):
  th1.(Thread.sc) = th2.(Thread.sc).
Proof.
  inv STEP; inv STEP0; inv LOCAL; ss.
Qed.

Lemma promise_steps_sc
      lang tr (th1 th2: Thread.t lang)
      (STEPS: Trace.steps tr th1 th2)
      (PROMISE: List.Forall (fun x => is_promise (snd x)) tr):
  th1.(Thread.sc) = th2.(Thread.sc).
Proof.
  induction STEPS; eauto. subst.
  inv PROMISE. ss.
  exploit promise_step_sc; try exact STEP; eauto. i.
  rewrite x0. eauto.
Qed.

Lemma lower_step_sc
      lang e (th1 th2: Thread.t lang)
      (STEP: lower_step e th1 th2):
  th1.(Thread.sc) = th2.(Thread.sc).
Proof.
  inv STEP. inv STEP0. inv LOCAL; ss.
  - inv LOCAL0. ss.
  - inv LOCAL2. ss.
  - inv LOCAL0.
    unfold TView.write_fence_sc. condtac; ss.
    destruct ordw; ss.
  - inv LOCAL0. ss.
Qed.

Lemma lower_steps_sc
      lang (th1 th2: Thread.t lang)
      (STEPS: rtc (tau lower_step) th1 th2):
  th1.(Thread.sc) = th2.(Thread.sc).
Proof.
  induction STEPS; eauto.
  inv H. exploit lower_step_sc; try exact TSTEP; eauto. i. congr.
Qed.


Lemma step_split_pure
      lang pf e (th1 th2: Thread.t lang)
      (STEP: Thread.step pf e th1 th2)
      (NPROMISE: no_promise e)
      (NRELEASE: ~ release_event e)
      (MEM: th2.(Thread.memory) = th1.(Thread.memory))
  :
    (<<LOWER: tau lower_step th1 th2>>) /\
    (<<SC: th2.(Thread.sc) = th1.(Thread.sc)>>).
Proof.
  assert (SC: th2.(Thread.sc) = th1.(Thread.sc)).
  { inv STEP; inv STEP0; auto. inv LOCAL; ss.
    { inv LOCAL0; ss. }
    { inv LOCAL1; inv LOCAL2; ss. }
    { inv LOCAL0; ss.
      unfold TView.write_fence_sc.
      destruct (Ordering.le Ordering.seqcst ordw) eqn:ORD; ss.
      exfalso. eapply NRELEASE. destruct ordw; ss.
    }
    { inv LOCAL0; ss. }
  }
  esplits; eauto. econs.
  { inv STEP; [inv STEP0; ss|]. econs; eauto. rewrite MEM. refl. }
  { destruct e; ss. }
Qed.

Lemma memory_op_diff_only
      mem0 loc from to msg mem1 kind
      (WRITE: Memory.op mem0 loc from to msg mem1 kind)
      loc' to' from' msg'
      (SOME: Memory.get loc' to' mem1 = Some (from', msg'))
  :
    (exists from'' msg'',
        (<<GET: Memory.get loc' to' mem0 = Some (from'', msg'')>>) /\
        (<<MSG: Message.le msg' msg''>>)) \/
    ((<<LOC: loc' = loc>>) /\
     (<<TO: to' = to>>) /\
     (<<FROM: from' = from>>) /\
     (<<MSG: msg' = msg>>) /\
     (<<NONE: Memory.get loc' to' mem0 = None>>)).
Proof.
  inv WRITE.
  { erewrite Memory.add_o in SOME; eauto. des_ifs.
    { right. ss. des; clarify. splits; auto.
      eapply Memory.add_get0; eauto. }
    { left. esplits; eauto. refl. }
  }
  { erewrite Memory.split_o in SOME; eauto. des_ifs.
    { right. ss. des; clarify. splits; auto.
      eapply Memory.split_get0 in SPLIT. des; auto. }
    { left. ss. des; clarify. eapply Memory.split_get0 in SPLIT.
      des; clarify. esplits; eauto. refl. }
    { left. esplits; eauto. refl. }
  }
  { erewrite Memory.lower_o in SOME; eauto. des_ifs.
    { ss. des; clarify. left. eapply lower_succeed_wf in LOWER; eauto.
      des; eauto. }
    { left. esplits; eauto. refl. }
  }
  { erewrite Memory.remove_o in SOME; eauto. des_ifs.
    left. esplits; eauto. refl. }
Qed.

Lemma promise_step_tau_promise_step
      lang pf e (th0 th1: Thread.t lang)
      (STEP: Thread.promise_step pf e th0 th1)
  :
    tau (@pred_step is_promise _) th0 th1.
Proof.
  econs; eauto.
  { econs; eauto.
    { econs; eauto. econs 1; eauto. }
    { inv STEP; ss. }
  }
  { inv STEP; ss. }
Qed.

Lemma lower_step_tau_lower_step
      lang e (th0 th1: Thread.t lang)
      (STEP: lower_step e th0 th1)
  :
    tau lower_step th0 th1.
Proof.
  inv STEP. econs; eauto.
  { econs; eauto. }
  { destruct e; ss. }
Qed.

Lemma memory_lower_exists
      prom0 mem0 loc from to msg
      (CLOSED: Memory.closed mem0)
      (MLE: Memory.le prom0 mem0)
      (MSG: msg <> Message.reserve)
      (GET: Memory.get loc to prom0 = Some (from, msg))
      (BOT: Memory.bot_none prom0)
  :
    Memory.promise prom0 mem0 loc from to msg prom0 mem0 (Memory.op_kind_lower msg).
Proof.
  inv CLOSED. exploit CLOSED0.
  { eapply MLE. eauto. }
  i. des.
  hexploit Memory.lower_exists; try eassumption.
  { hexploit memory_get_ts_strong; eauto. i. des; clarify.
    rewrite BOT in GET. ss. }
  { refl. }
  i. des. hexploit Memory.lower_exists_le; eauto. i. des.
  hexploit lower_same_same; try apply H. i. subst.
  hexploit lower_same_same; try apply H0. i. subst.
  econs; eauto.
Qed.

Lemma split_memory_write
      promises1 mem1 loc from to msg promises2 mem2 kind
      (MESSAGE: msg <> Message.reserve)
      (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
  exists promises1',
    (<<PROMISE: Memory.promise promises1 mem1 loc from to msg promises1' mem2 kind>>) /\
    (<<WRITE_LOWER: Memory.write promises1' mem2 loc from to msg promises2 mem2 (Memory.op_kind_lower msg)>>).
Proof.
  exploit MemoryFacts.write_time_lt; eauto. i.
  assert (MSG: Message.wf msg).
  { inv WRITE. inv PROMISE; inv MEM; ss.
    - inv ADD. ss.
    - inv SPLIT. ss.
    - inv LOWER. ss.
  }
  assert (MSG_TO: Memory.message_to msg loc to).
  { inv WRITE. inv PROMISE; ss. }
  inv WRITE. esplits; eauto.
  exploit Memory.promise_get0; eauto.
  { inv PROMISE; ss. }
  i. des.
  exploit Memory.lower_exists_same; try exact GET_PROMISES; eauto. i.
  exploit Memory.lower_exists_same; try exact GET_MEM; eauto.
Qed.

Lemma split_write
      lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (REL_WF: View.opt_wf releasedm)
      (REL_CLOSED: Memory.closed_opt_view releasedm mem0)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (ORD: Ordering.le ord Ordering.relaxed)
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord lc2 sc2 mem2 kind):
  exists released' lc1,
    (<<RELEASED: released' = TView.write_released (Local.tview lc0) sc0 loc to releasedm ord>>) /\
    (<<PROMISE: Local.promise_step lc0 mem0 loc from to
                                   (Message.concrete val released') lc1 mem2 kind>>) /\
    (<<WRITE: Local.write_step lc1 sc0 mem2 loc from to val releasedm released ord lc2 sc2 mem2
                               (Memory.op_kind_lower (Message.concrete val released'))>>).
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit fulfill_write; try exact STEP2; eauto.
  subst. inv STEP1. ss.
Qed.

Lemma reorder_write_lower_rtc_promise
      lang
      promises1 mem1
      loc from to msg kind
      th2 th3
      (LE: Memory.le promises1 mem1)
      (KIND: Memory.op_kind_is_lower kind)
      (WRITE: Memory.write promises1 mem1 loc from to msg
                           th2.(Thread.local).(Local.promises) th2.(Thread.memory) kind)
      (STEPS: rtc (tau (@pred_step is_promise lang)) th2 th3):
  exists th2',
    (<<STEPS: rtc (tau (@pred_step is_promise lang))
                  (Thread.mk _ th2.(Thread.state)
                             (Local.mk th2.(Thread.local).(Local.tview) promises1)
                             th2.(Thread.sc) mem1)
                  th2'>>) /\
    (<<WRITE: Memory.write th2'.(Thread.local).(Local.promises) th2'.(Thread.memory)
                           loc from to msg
                           th3.(Thread.local).(Local.promises) th3.(Thread.memory) kind>>) /\
    (<<STATE: th2'.(Thread.state) = th3.(Thread.state)>>) /\
    (<<TVIEW: th2'.(Thread.local).(Local.tview) = th3.(Thread.local).(Local.tview)>>) /\
    (<<SC: th2'.(Thread.sc) = th3.(Thread.sc)>>).
Proof.
  revert promises1 mem1 LE WRITE.
  induction STEPS; i.
  { esplits; try refl. ss. }
  inv H. inv TSTEP. inv STEP. inv STEP0; inv STEP; inv LOCAL; ss.
  exploit reorder_memory_write_lower_promise; try exact WRITE; eauto. i. des.
  hexploit Memory.promise_le; try exact PROMISE0; eauto. i. des.
  exploit IHSTEPS; eauto. i. des.
  esplits; try exact WRITE1; eauto.
  econs 2; eauto. econs.
  - econs; [do 4 econs; eauto|]; ss.
    inv WRITE0. inv PROMISE1; ss.
    eapply lower_closed_message_inv; eauto.
  - ss.
Qed.

Lemma memory_write_lower_refl_inv
      promsies1 mem1 loc from to msg promises2 mem2
      (WRITE: Memory.write promsies1 mem1 loc from to msg promises2 mem2 (Memory.op_kind_lower msg)):
  mem1 = mem2.
Proof.
  inv WRITE. inv PROMISE; ss.
  apply Memory.ext. i.
  exploit Memory.lower_get0; try exact MEM. i. des.
  erewrite (@Memory.lower_o mem2); eauto. condtac; ss.
  des. subst. ss.
Qed.

Lemma promise_remove_messages
      promises0 mem0 loc from to msg promises1 mem1 kind
      promises2
      (PROMISE: Memory.promise promises0 mem0 loc from to msg promises1 mem1 kind)
      (REMOVE: Memory.remove promises1 loc from to msg promises2):
  Messages.of_memory promises1 <4=
  (Messages.of_memory promises2 \4/ committed mem0 promises0 mem1 promises2).
Proof.
  s. i. inv PR. revert GET. inv PROMISE; ss.
  { erewrite Memory.add_o; eauto. condtac; ss.
    - i. des. symmetry in GET. inv GET. right.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.add_get0; try exact MEM. i. des.
      econs; [econs; eauto|]. ii. inv H. congr.
    - i. left. econs.
      erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.add_o; eauto. condtac; ss.
  }
  { erewrite Memory.split_o; eauto. repeat (condtac; ss).
    - i. des. symmetry in GET. inv GET. right.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.split_get0; try exact MEM. i. des.
      econs; [econs; eauto|]. ii. inv H. congr.
    - guardH o. i. des. symmetry in GET. inv GET. left. econs.
      exploit Memory.split_get0; try exact PROMISES. i. des.
      erewrite Memory.remove_o; eauto. condtac; ss.
    - i. left. econs.
      erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.split_o; eauto. repeat (condtac; ss).
  }
  { erewrite Memory.lower_o; eauto. condtac; ss.
    - i. des. symmetry in GET. inv GET. right.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.lower_get0; try exact MEM. i. des.
      exploit Memory.lower_get0; try exact PROMISES. i. des.
      econs; [econs; eauto|]. ii. inv H. congr.
    - i. left. econs.
      erewrite Memory.remove_o; eauto. condtac; ss.
      erewrite Memory.lower_o; eauto. condtac; ss.
  }
  { exploit Memory.remove_get0; try exact REMOVE. i. des.
    exploit Memory.remove_get0; try exact PROMISES. i. des.
    congr.
  }
Qed.

Lemma split_step
      lang pf e (th0 th2: Thread.t lang)
      (STEP: Thread.step pf e th0 th2)
      (NRELEASE: ~ release_event e)
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (CLOSED: Memory.closed (Thread.memory th0)):
  exists th1,
    (<<PROMISES: rtc (tau (@pred_step is_promise _)) th0 th1>>) /\
    (<<LOWER: rtc (tau lower_step) th1 th2>>) /\
    (<<STATE: th0.(Thread.state) = th1.(Thread.state)>>) /\
    (<<MEM: th1.(Thread.memory) = th2.(Thread.memory)>>) /\
    (<<SC: th1.(Thread.sc) = th2.(Thread.sc)>>) /\
    (<<FIN: Messages.of_memory th1.(Thread.local).(Local.promises) <4=
            (Messages.of_memory th2.(Thread.local).(Local.promises) \4/
             committed th0.(Thread.memory) th0.(Thread.local).(Local.promises)
                       th2.(Thread.memory) th2.(Thread.local).(Local.promises))>>).
Proof.
  dup STEP. inv STEP.
  { (* promise *)
    exists th2. inv STEP1. ss. splits; eauto.
    econs; eauto. econs.
    - econs; [econs|]; eauto. ss.
    - ss.
  }

  inv STEP1. inv LOCAL0; ss.
  { (* silent *)
    exploit step_split_pure; eauto; ss. i. des. esplits; eauto.
  }
  { (* read *)
    exploit step_split_pure; eauto; ss. i. des. esplits; eauto.
    s. i. inv LOCAL1. eauto.
  }

  { (* write *)
    exploit split_write; try exact LOCAL1; eauto.
    { destruct ord; ss. }
    i. des.
    esplits.
    - econs 2; eauto. eapply promise_step_tau_promise_step. econs; eauto.
    - econs 2; eauto. eapply lower_step_tau_lower_step.
      econs; [econs; eauto|..]; eauto. refl.
    - ss.
    - ss.
    - inv WRITE. ss.
    - clear STEP0 WRITE.
      inv PROMISE. inv LOCAL1. inv WRITE. destruct lc1. ss.
      exploit Memory.promise_inj; [exact PROMISE|exact PROMISE0|]. i. des. subst.
      eapply promise_remove_messages; eauto.
  }

  { (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit split_write; try exact LOCAL2; eauto.
    { destruct ordw; ss. }
    i. des.
    exploit reorder_read_promise_diff; try exact LOCAL1; eauto.
    { inv WRITE. exploit MemoryFacts.write_time_lt; eauto. i.
      ii. inv H. timetac.
    }
    i. des.
    esplits.
    - econs 2; eauto. eapply promise_step_tau_promise_step. econs; eauto.
    - econs 2; eauto. eapply lower_step_tau_lower_step.
      econs; [econs; eauto|..]; eauto. refl.
    - ss.
    - ss.
    - inv WRITE. ss.
    - clear STEP0 WRITE PROMISE STEP2.
      inv STEP1. inv LOCAL1. inv LOCAL2. inv WRITE. destruct lc1. ss.
      exploit Memory.promise_inj; [exact PROMISE|exact PROMISE0|]. i. des. subst.
      eapply promise_remove_messages; eauto.
  }

  { (* fence *)
    exploit step_split_pure; eauto; ss. i. des. esplits; eauto.
    s. i. inv LOCAL1. eauto.
  }

  { (* na write *)
    clear STEP0. inv LOCAL1. ss.
    cut (exists th1 kinds' kind',
            rtc (tau (@pred_step is_promise _)) (Thread.mk _ st1 lc1 sc1 mem1) th1 /\
            Memory.write_na
              (View.rlx (TView.cur (Local.tview lc1)) loc)
              th1.(Thread.local).(Local.promises) th1.(Thread.memory)
              loc from to val promises2 mem2 msgs kinds' kind' /\
            th1.(Thread.state) = st1 /\
            th1.(Thread.local).(Local.tview) = lc1.(Local.tview) /\
            th1.(Thread.memory) = mem2 /\
            th1.(Thread.sc) = sc1 /\
            Messages.of_memory th1.(Thread.local).(Local.promises) <4=
            (Messages.of_memory promises2 \4/
            committed mem1 lc1.(Local.promises) mem2 promises2)).
    { i. des.
      destruct th1. ss. subst. rewrite <- H2 in *.
      esplits; eauto. econs 2; eauto. econs.
      - econs.
        + econs; cycle 1.
          * econs 8. econs; eauto.
          * ss.
        + ss.
        + refl.
      - ss.
    }

    destruct lc1. ss.
    remember (View.rlx (TView.cur tview) loc) as ts eqn:TS.
    assert (LE: Time.le (View.rlx (TView.cur tview) loc) ts) by (subst; refl).
    clear TS.
    induction WRITE.
    { inv WRITE. esplits.
      - econs 2; eauto. eapply promise_step_tau_promise_step. econs; eauto.
      - s. hexploit Memory.promise_get0; try exact PROMISE.
        { inv PROMISE; ss. }
        i. des.
        hexploit Memory.get_ts; try exact GET_MEM. i. des.
        { subst. inv WRITABLE. }
        hexploit Memory.lower_exists_same; try exact GET_PROMISES; eauto. i.
        hexploit Memory.lower_exists_same; try exact GET_MEM; eauto. i.
        econs 1.
        + ss.
        + econs; eauto. econs 3; eauto; ss.
          econs. apply Time.bot_spec.
      - refl.
      - refl.
      - refl.
      - refl.
      - s. eapply promise_remove_messages; eauto.
    }

    exploit Memory.write_future; try exact WRITE_EX; try apply LOCAL; eauto.
    { unguard. des; subst; ss. econs; ss. }
    i. des.
    exploit IHWRITE; eauto.
    { eapply Memory.future_closed_timemap; eauto. }
    { econs; try apply LOCAL; eauto.
      eapply TView.future_closed; eauto. apply LOCAL. }
    { econs. eapply TimeFacts.le_lt_lt; eauto. }
    i. des.
    exploit split_memory_write; try exact WRITE_EX.
    { unguard. des; subst; ss. }
    i. des.
    exploit reorder_write_lower_rtc_promise; try exact x; try apply WRITE_LOWER; eauto.
    { eapply Memory.promise_le; try eapply LOCAL; eauto. }
    s. i. des.
    esplits.
    - econs 2; try exact STEPS. econs; [econs|].
      + econs. econs. econs; eauto. econs; eauto.
        unguard. des; subst; ss. econs. ss.
      + ss.
      + ss.
    - econs 2; eauto.
    - congr.
    - congr.
    - exploit memory_write_lower_refl_inv; try exact WRITE0. i. congr.
    - congr.
    - clear IHWRITE.
  }

  { exploit step_split_pure; eauto; ss. i. des. esplits; eauto. }
Qed.

Lemma reorder_lower_step_promise_step
      lang pf e1 e2 (th0 th1 th2: @Thread.t lang)
      (WF: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (CLOSED: Memory.closed th0.(Thread.memory))
      (STEP1: lower_step e1 th0 th1)
      (STEP2: Thread.step pf e2 th1 th2)
      (ISPROMISE: is_promise e2)
      (CONS: Local.promise_consistent th2.(Thread.local)):
  exists th1',
    (<<STEP1: Thread.step pf e2 th0 th1'>>) /\
    (<<STEP2: lower_step e1 th1' th2>>) /\
    (<<STATE: th0.(Thread.state) = th1'.(Thread.state)>>).
Proof.
  inv STEP2; [|inv STEP; inv LOCAL; ss]. inv STEP. ss.
  inv STEP1. inv STEP. inv LOCAL0; ss.
  { esplits.
    - econs; ss. econs; eauto.
    - econs; ss. refl.
    - ss.
  }

  { exploit reorder_read_promise_diff; eauto.
    { ii. inv H.
      inv LOCAL1. inv LOCAL. ss.
      exploit Memory.promise_get0; eauto.
      { inv PROMISE; ss.
        exploit Memory.remove_get0; try exact MEM0. i. des. congr. }
      i. des.
      exploit Memory.promise_get1; eauto.
      { inv PROMISE; ss.
        exploit Memory.remove_get0; try exact MEM0. i. des. congr. }
      i. des. inv MSG_LE.
      rewrite GET_MEM in *. inv GET0.
      exploit CONS; try exact GET_PROMISES; ss.
      unfold TimeMap.join, View.singleton_ur_if. condtac.
      - unfold View.singleton_ur, TimeMap.singleton. ss.
        unfold LocFun.add, LocFun.init, LocFun.find. condtac; ss. i.
        exploit TimeFacts.join_lt_des; eauto. i. des.
        exploit TimeFacts.join_lt_des; try exact AC. i. des. timetac.
      - unfold View.singleton_rw, TimeMap.singleton. ss.
        unfold LocFun.add, LocFun.init, LocFun.find. condtac; ss. i.
        exploit TimeFacts.join_lt_des; eauto. i. des.
        exploit TimeFacts.join_lt_des; try exact AC. i. des. timetac.
    }
    i. des. esplits.
    - econs. econs; eauto.
    - econs; ss; try refl. econs; eauto.
    - ss.
  }

  { exploit write_step_lower_memory_lower; eauto. i.
    exploit reorder_write_lower_promise; eauto.
    { destruct ord; ss. }
    i. des.
    exploit write_step_lower_lower_memory; try exact STEP2; eauto. i.
    esplits.
    - econs. econs; eauto.
    - econs; ss. econs; eauto.
    - ss.
  }

  { exploit Local.read_step_future; eauto. i. des.
    exploit write_step_lower_memory_lower; eauto. i.
    exploit reorder_write_lower_promise; try exact LOCAL2; eauto.
    { destruct ordw; ss. }
    i. des.
    exploit write_step_lower_lower_memory; try exact STEP2; eauto. i.
    hexploit write_step_promise_consistent; try exact STEP2; eauto. i.
    exploit reorder_read_promise_diff; try exact LOCAL1; eauto.
    { ii. inv H0. clear LOCAL LOCAL2 STEP2.
      inv LOCAL1. inv STEP1. ss.
      exploit Memory.promise_get0; eauto.
      { inv PROMISE; ss.
        exploit Memory.remove_get0; try exact MEM0. i. des. congr. }
      i. des.
      exploit Memory.promise_get1; eauto.
      { inv PROMISE; ss.
        exploit Memory.remove_get0; try exact MEM0. i. des. congr. }
      i. des. inv MSG_LE.
      rewrite GET_MEM in *. inv GET0.
      exploit H; try exact GET_PROMISES; ss.
      unfold TimeMap.join, View.singleton_ur_if. condtac.
      - unfold View.singleton_ur, TimeMap.singleton. ss.
        unfold LocFun.add, LocFun.init, LocFun.find. condtac; ss. i.
        exploit TimeFacts.join_lt_des; eauto. i. des.
        exploit TimeFacts.join_lt_des; try exact AC. i. des. timetac.
      - unfold View.singleton_rw, TimeMap.singleton. ss.
        unfold LocFun.add, LocFun.init, LocFun.find. condtac; ss. i.
        exploit TimeFacts.join_lt_des; eauto. i. des.
        exploit TimeFacts.join_lt_des; try exact AC. i. des. timetac.
    }
    i. des. esplits.
    - econs. econs; eauto.
    - econs; ss. econs; eauto.
    - ss.
  }

  { exploit reorder_fence_promise; eauto.
    { destruct ordw; ss. }
    i. des. esplits.
    - econs. econs; eauto.
    - econs; ss; try refl. econs; eauto.
    - ss.
  }

  { exploit write_na_step_lower_memory_lower; eauto. i. des.
    exploit reorder_write_na_lower_promise; eauto.
    { inv LOCAL1. destruct ord; ss. }
    i. des.
    exploit write_na_step_lower_lower_memory; try exact STEP2; eauto. i.
    esplits.
    - econs. econs; eauto.
    - econs; ss. econs; eauto.
    - ss.
  }

  { exploit reorder_racy_read_promise; eauto. i. des. esplits.
    - econs. econs; eauto.
    - econs; ss; try refl. econs; eauto.
    - ss.
  }
Qed.

Lemma reorder_lower_steps_promise_steps
      lang tr (th0 th1 th2: @Thread.t lang)
      (WF: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
      (CLOSED: Memory.closed th0.(Thread.memory))
      (STEPS1: rtc (tau lower_step) th0 th1)
      (STEPS2: Trace.steps tr th1 th2)
      (PROMISE: List.Forall (fun x => is_promise (snd x)) tr)
      (CONS: Local.promise_consistent th2.(Thread.local)):
  exists tr' th1',
    (<<STEPS1: Trace.steps tr' th0 th1'>>) /\
    (<<TRACE: List.Forall2 (fun x y => snd x = snd y) tr tr'>>) /\
    (<<STEPS2: rtc (tau lower_step) th1' th2>>) /\
    (<<STATE: th0.(Thread.state) = th1'.(Thread.state)>>).
Proof.
  revert tr th2 STEPS2 PROMISE CONS.
  induction STEPS1; i.
  { esplits; eauto using Forall2_refl.
    clear - PROMISE STEPS2.
    induction STEPS2; eauto.
    subst. inv PROMISE. ss.
    rewrite <- IHSTEPS2; eauto.
    inv STEP; [|inv STEP0; inv LOCAL; ss].
    inv STEP0. ss.
  }
  inv H.
  exploit Thread.step_future; try eapply lower_step_step; eauto. i. des.
  exploit IHSTEPS1; eauto. i. des.
  cut (exists tr'' th1'',
          Trace.steps tr'' x th1'' /\
          List.Forall2 (fun x y => snd x = snd y) tr' tr'' /\
          lower_step e th1'' th1' /\
          x.(Thread.state) = th1''.(Thread.state)).
  { i. des. esplits; eauto.
    eapply Forall2_trans; eauto. congr.
  }
  exploit Trace.steps_future; try exact STEPS0; eauto. i. des.
  hexploit rtc_tau_step_promise_consistent;
    try eapply rtc_implies; try eapply tau_lower_step_tau_step; try exact STEPS3; eauto. i.
  assert (PROMISE': List.Forall (fun x => is_promise (snd x)) tr')
    by eauto using trace_eq_promise.
  clear z STEPS1 IHSTEPS1 STEPS2 STEPS3.
  clear - WF SC CLOSED TSTEP STEPS0 H PROMISE'.
  rename tr' into tr, th1' into z, STEPS0 into STEPS, PROMISE' into PROMISE.
  revert x e WF SC CLOSED TSTEP.
  induction STEPS; i.
  { esplits; eauto. }
  subst. inv PROMISE. ss.
  exploit Thread.step_future; try eapply lower_step_step; eauto. i. des.
  exploit Thread.step_future; try eapply STEP; eauto. i. des.
  hexploit Trace.steps_promise_consistent; try exact STEPS; eauto. i.
  exploit reorder_lower_step_promise_step; try exact TSTEP; eauto. i. des.
  exploit Thread.step_future; try eapply STEP1; eauto. i. des.
  exploit IHSTEPS; try exact STEP2; eauto. i. des.
  esplits; try exact x2; eauto. congr.
Qed.


Definition delayed {lang} (st0 st1: lang.(Language.state)) lc0 lc1 sc mem fin: Prop :=
    (<<MEM: Memory.closed mem>>) /\
    (<<SC: Memory.closed_timemap sc mem>>) /\
    (<<LOCAL0: Local.wf lc0 mem>>) /\
    (<<LOCAL1: Local.wf lc1 mem>>) /\
    (<<FIN: Messages.of_memory lc0.(Local.promises) <4= (Messages.of_memory lc1.(Local.promises) \4/ fin)>>) /\
    exists lc1' mem',
      (<<STEPS: rtc (tau lower_step) (Thread.mk _ st0 lc0 sc mem) (Thread.mk _ st1 lc1' sc mem')>>) /\
      (<<MEM: lower_memory mem' mem>>) /\
      (<<LOCAL: lower_local lc1' lc1>>).

Lemma delayed_refl
      lang (st: lang.(Language.state)) lc mem sc fin
      (MEM: Memory.closed mem)
      (SC: Memory.closed_timemap sc mem)
      (LOCAL: Local.wf lc mem)
  :
    delayed st st lc lc sc mem fin.
Proof.
  red. esplits; eauto.
  { refl. }
  { refl. }
Qed.

Lemma delayed_step
      lang (st0 st1 st2: Language.state lang) lc0 lc1 lc2
      mem1 sc1 mem2 sc2 fin
      pf e
      (STEP: Thread.step pf e (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2))
      (CONS: Local.promise_consistent lc2)
      (NRELEASE: ~ release_event e)
      (DELAYED: delayed st0 st1 lc0 lc1 sc1 mem1 fin)
  :
    exists lc0',
      (<<PROMISES: rtc (tau (@pred_step is_promise _)) (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st0 lc0' sc2 mem2)>>) /\
      (<<DELAYED: delayed st0 st2 lc0' lc2 sc2 mem2 (fin \4/ committed mem1 lc1.(Local.promises) mem2 lc2.(Local.promises))>>).
Proof.
  unfold delayed in DELAYED. des.
  exploit Thread.step_future; try exact STEP; eauto. s. i. des.
  exploit Thread.rtc_tau_step_future;
    try eapply rtc_implies; try eapply tau_lower_step_tau_step; eauto. s. i. des.
  exploit split_step; try exact STEP; eauto. s. i. des.
  exploit promise_steps_trace_promise_steps; eauto. i. des.
  clear STEP PROMISES. rename STEPS0 into PROMISES.
  destruct th1. ss. subst.
  exploit lower_memory_promise_steps; try exact MEM0; try exact PROMISES; eauto. i. des.
  rename STEP into PROMISES_L.
  exploit Trace.steps_future; try exact PROMISES; eauto. s. i. des.
  exploit Trace.steps_future; try exact PROMISES_L; eauto. s. i. des.
  exploit lower_memory_lower_steps; try exact MEM2; try exact LOWER; eauto. i. des.
  rename STEP into LOWER_L. clear LOWER.
  hexploit lower_local_consistent; try exact LC0; eauto. i.
  hexploit rtc_tau_step_promise_consistent;
    try eapply rtc_implies; try eapply tau_lower_step_tau_step; try exact LOWER_L; eauto. s. i.
  exploit reorder_lower_steps_promise_steps; try exact STEPS; try exact PROMISES_L; eauto.
  { eapply trace_eq_promise; eauto. }
  s. i. des. subst.
  move STEPS1 at bottom.
  exploit same_memory_promise_steps; [exact PROMISES|exact STEPS1|..]; eauto.
  { eapply Forall2_trans; eauto. congr. }
  s. i. subst. destruct th1'. ss.
  exploit lower_steps_sc; try exact STEPS2. s. i. subst.
  exploit promise_steps_sc; try exact STEPS1; eauto.
  { repeat (eapply trace_eq_promise; eauto). }
  s. i. subst.
  exploit trace_promise_steps_promise_steps; try exact STEPS1; eauto.
  { repeat (eapply trace_eq_promise; eauto). }
  i. esplits; try exact x0. clear x0.
  unfold delayed.
  exploit Trace.steps_future; try exact STEPS1; eauto. s. i. des.
  splits; auto; cycle 1.
  - esplits.
    + etrans; eauto.
    + ss.
    + ss.
  - 
Admitted.

Lemma delayed_future
      mem1 sc1
      lang (st0 st1: lang.(Language.state)) lc0 lc1 mem0 sc0 fin0 fin1
      (DELAYED: delayed st0 st1 lc0 lc1 mem0 sc0 fin0)
      (MEM: Memory.closed mem1)
      (SC: Memory.closed_timemap sc1 mem1)
      (LOCAL: Local.wf lc1 mem1)
      (FIN: fin1 <4= unchangable mem1 lc1.(Local.promises))
      (MEM_FUTURE: Memory.future mem0 mem1)
      (SC_FUTURE: TimeMap.le sc0 sc1)
      (FIN_FUTURE: fin0 <4= fin1)
  :
    delayed st0 st1 lc0 lc1 mem1 sc1 fin1.
Admitted.
