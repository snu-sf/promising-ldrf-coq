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

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import JoinedView.
Require Import Pred.
Require Import Trace.
Require Import MemoryProps.
Require Import LowerMemory.

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
    (STEP: Thread.step true e th0 th1)
    (NPROMISE: no_promise e)
    (NRELEASE: ~ release_event e)
    (MEM: lower_memory th1.(Thread.memory) th0.(Thread.memory))
.

Lemma write_lower_memory_lower prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (LOWER: lower_memory mem1 mem0)
  :
    exists msg, kind = Memory.op_kind_lower msg.
Proof.
  inv PROMISE. inv PROMISE0; eauto.
  { eapply Memory.add_get0 in MEM. des.
    hexploit lower_memory_get_inv; eauto. i. des; clarify. }
  { eapply Memory.split_get0 in MEM. des.
    hexploit lower_memory_get_inv; try apply GET1; eauto. i. des; clarify. }
  { eapply Memory.remove_get0 in MEM. des.
    hexploit lower_memory_get; eauto. i. des; clarify. }
Qed.

Lemma step_split_pure lang (th0 th2: Thread.t lang) e
      (STEP: Thread.step true e th0 th2)
      (NPROMISE: no_promise e)
      (NRELEASE: ~ release_event e)
      (MEM: th2.(Thread.memory) = th0.(Thread.memory))
  :
    exists th1,
      (<<PROMISES: rtc (tau (@pred_step is_promise _)) th0 th1>>) /\
      (<<LOWER: rtc (tau lower_step) th1 th2>>) /\
      (<<MEM: th1.(Thread.memory) = th2.(Thread.memory)>>) /\
      (<<SC: th1.(Thread.sc) = th2.(Thread.sc)>>).
Proof.
  assert (SC: th2.(Thread.sc) = th0.(Thread.sc)).
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
  subst. esplits.
  { econs. }
  { econs; [|econs]. econs; eauto.
    { econs; eauto. rewrite MEM. refl. }
    { destruct e; ss. }
  }
  { auto. }
  { auto. }
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

Lemma promise_step_tau_promise_step lang (th0 th1: Thread.t lang)
      pf e
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

Lemma lower_step_tau_lower_step lang (th0 th1: Thread.t lang)
      e
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

Lemma step_split lang (th0 th2: Thread.t lang) pf e
      (STEP: Thread.step pf e th0 th2)
      (NRELEASE: ~ release_event e)
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (CLOSED: Memory.closed (Thread.memory th0))
      (CONS: Local.promise_consistent th2.(Thread.local))
  :
    exists th1,
      (<<PROMISES: rtc (tau (@pred_step is_promise _)) th0 th1>>) /\
      (<<LOWER: rtc (tau lower_step) th1 th2>>) /\
      (<<MEM: th1.(Thread.memory) = th2.(Thread.memory)>>) /\
      (<<SC: th1.(Thread.sc) = th2.(Thread.sc)>>).
Proof.
  hexploit Thread.step_future; eauto. i. des.
  dup STEP. inv STEP.
  { exists th2. inv STEP1. ss. splits; eauto.
    econs; eauto. econs.
    { econs; eauto.
      { econs; eauto. }
      { ss. }
    }
    { ss. }
  }
  { inv STEP1. inv LOCAL0; ss.
    { eapply step_split_pure; eauto; ss. }
    { eapply step_split_pure; eauto; ss. }
    { inv LOCAL1. ss. dup WRITE. inv WRITE. esplits.
      { econs; [|econs]. eapply promise_step_tau_promise_step.
        econs.
        { econs; eauto. econs; ss. eapply TViewFacts.op_closed_released.
          { eapply SC. }
          { eauto. }
          { eapply LOCAL. }
          { eauto. }
          { eapply Memory.write_op; eauto. }
        }
        { ss. }
      }
      { econs; [|econs]. eapply lower_step_tau_lower_step.
        { econs.
          { econs 2. econs; eauto; cycle 1.
            { econs 3. econs; eauto; ss. econs; eauto.
              eapply memory_lower_exists; eauto.
              { eapply promise_memory_le; eauto. eapply LOCAL. }
              { ss. }
              { eapply Memory.remove_get0 in REMOVE. des. auto. }
              { eapply Memory.promise_bot_none; eauto. eapply LOCAL. }
            }
            { ss. }
          }
          { ss. }
          { ss. }
          { ss. refl. }
        }
      }
      { ss. }
      { ss. }
    }
    { admit. }
    { eapply step_split_pure; eauto; ss. }
    { admit. }
    { eapply step_split_pure; eauto; ss. }
  }
Admitted.

Definition delayed {lang} (st0 st1: lang.(Language.state))
           lc0 lc1 mem sc fin: Prop
  :=
    (<<MEM: Memory.closed mem>>) /\
    (<<SC: Memory.closed_timemap sc mem>>) /\
    (<<LOCAL0: Local.wf lc0 mem>>) /\
    (<<LOCAL1: Local.wf lc1 mem>>) /\
    (<<FIN: Messages.of_memory lc0.(Local.promises) <4= (Messages.of_memory lc1.(Local.promises) \4/ fin)>>) /\
    exists lc1' mem',
      (<<STEPS: rtc (tau lower_step) (Thread.mk _ st0 lc0 sc mem) (Thread.mk _ st1 lc1' sc mem')>>) /\
      (<<MEM: lower_memory mem' mem>>) /\
      (<<LOCAL: lower_local lc1' lc1>>).

Lemma delayed_refl lang (st: lang.(Language.state)) lc mem sc fin
      (MEM: Memory.closed mem)
      (SC: Memory.closed_timemap sc mem)
      (LOCAL: Local.wf lc mem)
  :
    delayed st st lc lc mem sc fin.
Proof.
  red. esplits; eauto.
  { refl. }
  { refl. }
Qed.

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

Lemma delayed_step
      lang (st0 st1 st2: Language.state lang) lc0 lc1 lc2
      mem1 sc1 mem2 sc2 fin
      pf e
      (STEP: Thread.step pf e (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2))
      (NRELEASE: ~ release_event e)
      (DELAYED: delayed st0 st1 lc0 lc1 mem1 sc1 fin)
  :
    exists lc0',
      (<<PROMISES: rtc (tau (@pred_step is_promise _)) (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st0 lc0' sc2 mem2)>>) /\
      (<<DELAYED: delayed st0 st2 lc0' lc2 mem2 sc2 (fin \4/ committed mem1 lc1.(Local.promises) mem2 lc2.(Local.promises))>>).
Proof.
Admitted.
