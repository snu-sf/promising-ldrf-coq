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

Inductive joined_promise_steps lang:
  forall (th0 th1: Thread.t lang) (views0 views1: Loc.t -> Time.t -> list View.t), Prop :=
| joined_promise_steps_base
    th0 views0
  :
    joined_promise_steps th0 th0 views0 views0
| joined_promise_steps_step
    th0 th1 th2 views0 views1 views2
    pf loc from to msg kind
    (STEP: JThread.step pf (ThreadEvent.promise loc from to msg kind) th0 th1 views0 views1)
    (STEPS: joined_promise_steps th1 th2 views1 views2)
  :
    joined_promise_steps th0 th2 views0 views2
.

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

Variant lower_step views {lang} e (th0 th1: Thread.t lang): Prop :=
| lower_step_intro
    (STEP: JThread.step true e th0 th1 views views)
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

Lemma step_split_pure lang (th0 th2: Thread.t lang) e views0 views2
      (STEP: JThread.step true e th0 th2 views0 views2)
      (NPROMISE: no_promise e)
      (NRELEASE: ~ release_event e)
      (MEM: th2.(Thread.memory) = th0.(Thread.memory))
  :
    exists th1,
      (<<PROMISES: joined_promise_steps th0 th1 views0 views2>>) /\
      (<<LOWER: rtc (tau (lower_step views2)) th1 th2>>) /\
      (<<MEM: th1.(Thread.memory) = th2.(Thread.memory)>>) /\
      (<<SC: th1.(Thread.sc) = th2.(Thread.sc)>>).
Proof.
  inv STEP. assert (views2 = views0).
  { extensionality loc. extensionality ts.
    destruct (classic (views2 loc ts = views0 loc ts)); auto.
    hexploit VIEWSLE; eauto. i. des.
    rewrite MEM in *. clarify.
  }
  assert (SC: th2.(Thread.sc) = th0.(Thread.sc)).
  { inv STEP0; inv STEP; auto. inv LOCAL; ss.
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

Definition views_mem_le
           (mem0 mem1: Memory.t)
           (views0 views1: Loc.t -> Time.t -> list View.t)
           (tvw: TView.t): Prop :=
  forall loc ts (NEQ: views1 loc ts <> views0 loc ts),
    (<<NIL: views0 loc ts = []>>) /\
    exists from val released,
      (<<GET: Memory.get loc ts mem1 = Some (from, Message.concrete val (Some released))>>) /\
      (<<NONE: Memory.get loc ts mem0 = None>>) /\
      (<<VIEW: views1 loc ts = (View.join (tvw.(TView.rel) loc) (View.singleton_ur loc ts))
                                 ::(all_join_views (View.singleton_ur loc ts) (views0 loc from))>>).

Lemma write_tview_join_singleton tvw sc loc0 ts0 ord loc1 ts1
      (ORD: ~ Ordering.le Ordering.acqrel ord)
      (TS: loc0 = loc1 -> Time.le ts0 ts1)
  :
    View.join (TView.rel (TView.write_tview tvw sc loc0 ts0 ord) loc1)
              (View.singleton_ur loc1 ts1) =
    View.join (TView.rel tvw loc1) (View.singleton_ur loc1 ts1).
Proof.
  ss. des_ifs. setoid_rewrite LocFun.add_spec; eauto.
  destruct (LocSet.Facts.eq_dec loc1 loc0).
  { subst. rewrite View.join_assoc. f_equal.
    rewrite singleton_ur_join. f_equal.
    apply TimeFacts.le_join_r. auto. }
  { refl. }
Qed.

Local Opaque TView.write_tview.

Lemma step_split lang (th0 th2: Thread.t lang) pf e views0 views2
      (STEP: JThread.step pf e th0 th2 views0 views2)
      (NRELEASE: ~ release_event e)
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
      (CLOSED: Memory.closed (Thread.memory th0))
      (CONS: Local.promise_consistent th2.(Thread.local))
      (MEMORY: joined_memory views0 th0.(Thread.memory))
      (VIEWS: wf_views views0)
      (RELEASED: joined_released views0 th0.(Thread.local).(Local.promises) th0.(Thread.local).(Local.tview).(TView.rel))
  :
    exists th1,
      (<<PROMISES: joined_promise_steps th0 th1 views0 views2>>) /\
      (<<LOWER: rtc (tau (lower_step views2)) th1 th2>>) /\
      (<<MEM: th1.(Thread.memory) = th2.(Thread.memory)>>) /\
      (<<SC: th1.(Thread.sc) = th2.(Thread.sc)>>).
Proof.
  dup STEP. inv STEP.
  assert (VIEWSLE0: views_le views0 views2).
  { ii. apply NNPP. ii. hexploit VIEWSLE; eauto. i. des; ss. }
  inv STEP1.
  { inv STEP. esplits.
    { econs; [|econs]. econs; eauto.
      { econs. econs; eauto. }
    }
    { econs. }
    { ss. }
    { ss. }
  }
  { inv STEP. inv LOCAL0; ss.
    { eapply step_split_pure; eauto; ss. }
    { eapply step_split_pure; eauto; ss. }
    { inv LOCAL1. ss. dup WRITE. inv WRITE. esplits.
      { econs; [|econs]. econs.
        { econs. econs; ss. econs.
          { eauto. }
          { econs; ss. eapply TViewFacts.op_closed_released; eauto.
            { eapply LOCAL. }
            { eapply Memory.write_op; eauto. }
          }
          { ss. }
        }
        { i. clarify. unfold TView.write_released in *.
          destruct (Ordering.le Ordering.relaxed ord) eqn:ORD0; econs.
          inv MEMORY0. hexploit (COMPLETE loc0 to0).
          { eapply Memory.write_get2 in WRITE0. des; eauto. }
          rewrite View.join_bot_l. ss.
          replace (Ordering.le Ordering.acqrel ord) with false in *.
          2:{ destruct ord; ss. }
          i. des. auto.
        }
        { i. ss.
          hexploit VIEWSLE; eauto. i. des.
          assert (ts = to).
          { eapply Memory.promise_op in PROMISE0.
            eapply memory_op_diff_only in PROMISE0; eauto. des; clarify. }
          subst. esplits; eauto.
          rewrite write_tview_join_singleton in VIEW; eauto.
          { destruct ord; ss. }
          { i. refl. }
        }
        { auto. }
        { auto. }
        { ss. ii. eapply Memory.promise_op_promise in PROMISE0. dup GET.
          eapply memory_op_diff_only in GET0; eauto. des; clarify.
          { inv MSG. inv RELEASED1.
            exploit RELEASED; eauto. i.
            replace (views0 loc0 ts) with (views2 loc0 ts) in x; auto.
            apply NNPP. ii. exploit VIEWSLE0; eauto. ii.
            rewrite H0 in x. ss. }
          { admit. }
        }
      }
      { admit. }
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
           lc0 lc1 mem sc views fin: Prop
  :=
    (<<MEM: Memory.closed mem>>) /\
    (<<SC: Memory.closed_timemap sc mem>>) /\
    (<<LOCAL0: Local.wf lc0 mem>>) /\
    (<<JOINED: joined_memory views mem>>) /\
    (<<RELEASED0: joined_released views lc0.(Local.promises) lc0.(Local.tview).(TView.rel)>>) /\
    (<<LOCAL1: Local.wf lc1 mem>>) /\
    (<<RELEASED1: joined_released views lc1.(Local.promises) lc1.(Local.tview).(TView.rel)>>) /\
    (<<FIN: Messages.of_memory lc0.(Local.promises) <4= (Messages.of_memory lc1.(Local.promises) \4/ fin)>>) /\
    exists lc1' mem',
      (<<STEPS: rtc (tau (lower_step views)) (Thread.mk _ st0 lc0 sc mem) (Thread.mk _ st1 lc1' sc mem')>>) /\
      (<<MEM: lower_memory mem' mem>>) /\
      (<<LOCAL: lower_local lc1' lc1>>).

Lemma delayed_refl lang (st: lang.(Language.state)) lc mem sc views fin
      (MEM: Memory.closed mem)
      (VIEWS: wf_views views)
      (SC: Memory.closed_timemap sc mem)
      (LOCAL: Local.wf lc mem)
      (JOINED: joined_memory views mem)
      (RELEASED: joined_released views lc.(Local.promises) lc.(Local.tview).(TView.rel))
  :
    delayed st st lc lc mem sc views fin.
Proof.
  red. esplits; eauto.
  { refl. }
  { refl. }
Qed.

Lemma delayed_future
      mem1 sc1 views1
      lang (st0 st1: lang.(Language.state)) lc0 lc1 mem0 sc0 views0 fin0 fin1
      (DELAYED: delayed st0 st1 lc0 lc1 mem0 sc0 views0 fin0)

      (MEM: Memory.closed mem1)
      (VIEWS: wf_views views1)
      (SC: Memory.closed_timemap sc1 mem1)
      (LOCAL: Local.wf lc1 mem1)
      (FIN: fin1 <4= unchangable mem1 lc1.(Local.promises))
      (JOINED: joined_memory views1 mem1)

      (MEM_FUTURE: Memory.future mem0 mem1)
      (SC_FUTURE: TimeMap.le sc0 sc1)
      (VIEWS_FUTURE: views_le views0 views1)
      (FIN_FUTURE: fin0 <4= fin1)
  :
    delayed st0 st1 lc0 lc1 mem1 sc1 views1 fin1.
Admitted.

Lemma delayed_step
      lang (st0 st1 st2: Language.state lang) lc0 lc1 lc2
      mem1 sc1 views1 mem2 sc2 views2 fin
      pf e
      (STEP: JThread.step pf e (Thread.mk _ st1 lc1 sc1 mem1) (Thread.mk _ st2 lc2 sc2 mem2) views1 views2)
      (NRELEASE: ~ release_event e)
      (DELAYED: delayed st0 st1 lc0 lc1 mem1 sc1 views1 fin)
  :
    exists lc0',
      (<<PROMISES: joined_promise_steps (Thread.mk _ st0 lc0 sc1 mem1) (Thread.mk _ st0 lc0' sc2 mem2) views1 views2>>) /\
      (<<DELAYED: delayed st0 st2 lc0' lc2 mem2 sc2 views2 (fin \4/ committed mem1 lc1.(Local.promises) mem2 lc2.(Local.promises))>>).
Proof.
Admitted.
