Require Import Lia.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Pred.
Require Import Trace.

Require Import MemoryMerge.
Require Import ReorderCancel.
Require Import MemoryProps.
Require Import OrderedTimes.
Require Import Cover.
Require Import Mapping.

Set Implicit Arguments.



Lemma promise_not_cancel_covered_increase prom0 prom1 mem0 mem1
      loc from to msg kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (NOTCANCEL: kind <> Memory.op_kind_cancel)
      loc0 ts0
      (COVERED: covered loc0 ts0 mem0)
  :
    covered loc0 ts0 mem1.
Proof.
  inv PROMISE.
  { erewrite (@add_covered mem1 mem0); eauto. }
  { erewrite (@split_covered mem1 mem0); eauto. }
  { erewrite (@lower_covered mem1 mem0); eauto. }
  { ss. }
Qed.

Lemma write_covered_increase prom0 prom1 mem0 mem1
      loc from to msg kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      loc0 ts0
      (COVERED: covered loc0 ts0 mem0)
  :
    covered loc0 ts0 mem1.
Proof.
  exploit Memory.write_not_cancel; eauto. i.
  inv WRITE. eapply promise_not_cancel_covered_increase; eauto.
  ii. subst. ss.
Qed.

Lemma write_na_covered_increase prom0 prom1 mem0 mem1
      ts loc from to msg msgs kinds kind
      (WRITE: Memory.write_na ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind)
      loc0 ts0
      (COVERED: covered loc0 ts0 mem0)
  :
    covered loc0 ts0 mem1.
Proof.
  induction WRITE; eauto using write_covered_increase.
Qed.

Lemma step_not_cancel_covered_increase lang (th0 th1: Thread.t lang) pf e
      (STEP: Thread.step pf e th0 th1)
      (NOTCANCEL: ~ ThreadEvent.is_cancel e)
      loc0 ts0
      (COVERED: covered loc0 ts0 (Thread.memory th0))
  :
    covered loc0 ts0 (Thread.memory th1).
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    eapply promise_not_cancel_covered_increase; eauto. ii. subst.
    inv PROMISE. ss.
  }
  { inv STEP0. inv LOCAL; auto.
    { inv LOCAL0. eapply write_covered_increase; eauto. }
    { inv LOCAL2. eapply write_covered_increase; eauto. }
    { inv LOCAL0. eapply write_na_covered_increase; eauto. }
  }
Qed.

Lemma traced_steps_not_cancel_covered_increase lang (th0 th1: Thread.t lang) tr
      (STEPS: Trace.steps tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: (fun e => ~ ThreadEvent.is_cancel e) (snd em)>>) tr)
      loc0 ts0
      (COVERED: covered loc0 ts0 (Thread.memory th0))
  :
    covered loc0 ts0 (Thread.memory th1).
Proof.
  ginduction STEPS; auto. i. clarify. inv EVENTS.
  eapply step_not_cancel_covered_increase in STEP; eauto.
Qed.



Section UNATTACHABLE.

  Inductive unattachable (mem: Memory.t) (loc: Loc.t) (ts: Time.t): Prop :=
  | unattachable_intro
      from to msg
      (MSG: Memory.get loc to mem = Some (from, msg))
      (FROM: Time.le from ts)
      (TO: Time.lt ts to)
  .

  Lemma lower_unattachable mem1 mem0 loc from to msg1 msg2
        (LOWER: Memory.lower mem0 loc from to msg1 msg2 mem1)
    :
      unattachable mem1 = unattachable mem0.
  Proof.
    extensionality loc0. extensionality ts0.
    exploit Memory.lower_get0; eauto. i. des.
    apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
    { inv H. erewrite Memory.lower_o in MSG; eauto. des_ifs.
      { ss. des; clarify. econs; eauto. }
      { econs; eauto. }
    }
    { inv H. eapply Memory.lower_get1 in MSG; eauto. des. econs; eauto. }
  Qed.

  Lemma split_unattachable mem1 mem0 loc ts1 ts2 ts3 msg2 msg3
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg2 msg3 mem1)
    :
      unattachable mem1 = unattachable mem0.
  Proof.
    extensionality loc0. extensionality ts0.
    exploit split_succeed_wf; eauto. i. des.
    exploit Memory.split_get0; eauto. i. des.
    apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
    { inv H. erewrite Memory.split_o in MSG; eauto. des_ifs.
      { ss. des; clarify. econs; eauto. }
      { ss. des; clarify. econs; eauto. etrans; eauto. left. auto. }
      { econs; eauto. }
    }
    { inv H. generalize (Memory.split_o loc0 to SPLIT). intros MSG0. des_ifs.
      { ss. des; clarify. }
      { ss. des; clarify.
        destruct (Time.le_lt_dec ts2 ts0).
        { econs; try apply MSG0; eauto. }
        { econs; try apply GET1; eauto. }
      }
      { erewrite MSG in *. clarify. econs; eauto. }
    }
  Qed.

  Lemma add_unattachable mem1 mem0 loc from to msg
        (ADD: Memory.add mem0 loc from to msg mem1)
    :
      unattachable mem1 =
      (fun loc0 ts0 =>
         unattachable mem0 loc0 ts0 \/ (loc0 = loc /\ Time.le from ts0 /\ Time.lt ts0 to)).
  Proof.
    extensionality loc0. extensionality ts0.
    exploit add_succeed_wf; eauto. i.  des.
    exploit Memory.add_get0; eauto. i. des.
    apply Coq.Logic.PropExtensionality.propositional_extensionality. split; i.
    { inv H. erewrite Memory.add_o in MSG; eauto. des_ifs.
      { ss. des; clarify. right. splits; auto. }
      { left. econs; eauto. }
    }
    { des; subst.
      { inv H. econs; eauto. eapply Memory.add_get1; eauto. }
      { econs; eauto. }
    }
  Qed.

End UNATTACHABLE.



Section LIFT.

  Lemma memory_remove_le_preserve mem0 mem0' mem1 mem1' loc from to msg
        (REMOVE0: Memory.remove mem0 loc from to msg mem0')
        (REMOVE1: Memory.remove mem1 loc from to msg mem1')
        (MLE: Memory.le mem0 mem1)
  :
    Memory.le mem0' mem1'.
  Proof.
    ii. erewrite Memory.remove_o; eauto.
    erewrite (@Memory.remove_o mem0' mem0) in LHS; eauto. des_ifs.
    eapply MLE; eauto.
  Qed.

  Lemma memory_add_le_preserve mem0 mem0' mem1 mem1' loc from to msg
        (ADD0: Memory.add mem0 loc from to msg mem0')
        (ADD1: Memory.add mem1 loc from to msg mem1')
        (MLE: Memory.le mem0 mem1)
    :
      Memory.le mem0' mem1'.
  Proof.
    ii. erewrite Memory.add_o; eauto.
    erewrite (@Memory.add_o mem0' mem0) in LHS; eauto. des_ifs.
    eapply MLE; eauto.
  Qed.

  Lemma memory_split_le_preserve mem0 mem0' mem1 mem1' loc ts1 ts2 ts3 msg2 msg3
        (SPLIT0: Memory.split mem0 loc ts1 ts2 ts3 msg2 msg3 mem0')
        (SPLIT1: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem1')
        (MLE: Memory.le mem0 mem1)
    :
      Memory.le mem0' mem1'.
  Proof.
    ii. erewrite Memory.split_o; eauto.
    erewrite (@Memory.split_o mem0' mem0) in LHS; eauto. des_ifs.
    eapply MLE; eauto.
  Qed.

  Lemma memory_lower_le_preserve mem0 mem0' mem1 mem1' loc from to msg1 msg2
        (LOWER0: Memory.lower mem0 loc from to msg1 msg2 mem0')
        (LOWER1: Memory.lower mem1 loc from to msg1 msg2 mem1')
        (MLE: Memory.le mem0 mem1)
    :
      Memory.le mem0' mem1'.
  Proof.
    ii. erewrite Memory.lower_o; eauto.
    erewrite (@Memory.lower_o mem0' mem0) in LHS; eauto. des_ifs.
    eapply MLE; eauto.
  Qed.

  Lemma step_lifting_promise prom0 prom1 mem0 mem1 cap0
        loc from to msg kind
        (spaces lefts: Loc.t -> Time.t -> Prop)
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
        (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
        (WRITENOTTO: ~ lefts loc to)
        (SOUND: Memory.le mem0 cap0)
        (SPACES:
           forall loc ts (COV: covered loc ts cap0),
             <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
        (LEFTS:
           forall loc ts (UNATTACHABLE: unattachable cap0 loc ts),
             <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
        (MEM0: Memory.closed mem0)
        (PROM0: Memory.le prom0 mem0)
        (PROM1: Memory.le prom0 cap0)
        (NOTCANCEL: kind <> Memory.op_kind_cancel)
    :
      exists cap1,
        (<<STEP: Memory.promise prom0 cap0 loc from to msg prom1 cap1 kind>>) /\
        (<<SOUND: Memory.le mem1 cap1>>) /\
        (<<SPACES:
           forall loc ts (COV: covered loc ts cap1),
             <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
        (<<LEFTS:
           forall loc ts (UNATTACHABLE: unattachable cap1 loc ts),
             <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
  Proof.
    inv PROMISE.
    { exploit add_succeed_wf; try apply MEM; eauto. i. des.
      exploit (@Memory.add_exists cap0 loc from to msg); eauto.
      { ii. exploit SPACES.
        { econs; eauto. }
        i. des.
        { inv COV. eapply DISJOINT; eauto. }
        { eapply WRITENOTIN; eauto. }
      }
      i. des. esplits.
      { econs; eauto. i. subst. exploit LEFTS.
        { econs; eauto.
          { refl. }
          { apply memory_get_ts_strong in GET. des; auto.
            subst. eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec. }
        }
        i. des; ss.
        { inv COV. destruct FROM.
          { eapply DISJOINT; eauto.
            { instantiate (1:=to). econs; ss. refl. }
            { econs; ss. left. eauto. }
          }
          { inv H. eapply ATTACH; eauto. }
        }
      }
      { eapply memory_add_le_preserve; eauto. }
      { i. erewrite add_covered in COV; eauto.
        erewrite (@add_covered mem1 mem0); eauto. des; eauto.
        eapply SPACES in COV. des; auto. }
      { i. erewrite add_unattachable in UNATTACHABLE; eauto.
        erewrite (@add_unattachable mem1 mem0); eauto. des; auto.
        eapply LEFTS in UNATTACHABLE. des; auto. }
    }
    { des. subst.
      exploit (@Memory.split_exists_le prom0 cap0); eauto. i. des. esplits.
      { econs; eauto. }
      { ii. erewrite Memory.split_o in LHS; eauto.
        erewrite (@Memory.split_o mem2 cap0); eauto. des_ifs.
        eapply SOUND; eauto. }
      { i. erewrite (@split_covered mem2 cap0) in COV; eauto.
        erewrite (@split_covered mem1 mem0); eauto. }
      { i. erewrite (@split_unattachable mem2 cap0) in UNATTACHABLE; eauto.
        erewrite (@split_unattachable mem1 mem0); eauto. }
    }
    { des. subst.
      exploit (@Memory.lower_exists_le prom0 cap0); eauto. i. des. esplits.
      { econs; eauto. }
      { ii. erewrite Memory.lower_o in LHS; eauto.
        erewrite (@Memory.lower_o mem2 cap0); eauto. des_ifs.
        eapply SOUND; eauto. }
      { i. erewrite (@lower_covered mem2 cap0) in COV; eauto.
        erewrite (@lower_covered mem1 mem0); eauto. }
      { i. erewrite (@lower_unattachable mem2 cap0) in UNATTACHABLE; eauto.
        erewrite (@lower_unattachable mem1 mem0); eauto. }
    }
    { ss. }
  Qed.

  Lemma step_lifting_write prom0 prom1 mem0 mem1 cap0
        loc from to msg kind
        (spaces lefts: Loc.t -> Time.t -> Prop)
        (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
        (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
        (WRITENOTTO: ~ lefts loc to)
        (SOUND: Memory.le mem0 cap0)
        (SPACES:
           forall loc ts (COV: covered loc ts cap0),
             <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
        (LEFTS:
           forall loc ts (UNATTACHABLE: unattachable cap0 loc ts),
             <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
        (MEM0: Memory.closed mem0)
        (PROM0: Memory.le prom0 mem0)
        (PROM1: Memory.le prom0 cap0)
    :
      exists cap1,
        (<<STEP: Memory.write prom0 cap0 loc from to msg prom1 cap1 kind>>) /\
        (<<SOUND: Memory.le mem1 cap1>>) /\
        (<<SPACES:
           forall loc ts (COV: covered loc ts cap1),
             <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
        (<<LEFTS:
           forall loc ts (UNATTACHABLE: unattachable cap1 loc ts),
             <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
  Proof.
    inv WRITE. exploit step_lifting_promise; eauto.
    { exploit Memory.write_not_cancel; eauto. ii. subst. ss. }
    i. des.
    esplits; eauto.
  Qed.

  Lemma step_lifting_write_na prom0 prom1 mem0 mem1 cap0
        ts loc from to msg msgs kinds kind
        (spaces lefts: Loc.t -> Time.t -> Prop)
        (WRITE: Memory.write_na ts prom0 mem0 loc from to msg prom1 mem1 msgs kinds kind)
        (WRITENOTIN: forall ts (ITV: Interval.mem (from, to) ts), ~ spaces loc ts)
        (WRITENOTIN_MSGS:
           List.Forall (fun m => forall ts (ITV: Interval.mem (fst m) ts), ~ spaces loc ts) msgs)
        (WRITENOTTO: ~ lefts loc to)
        (WRITENOTTO_MSGS: List.Forall (fun m => ~ lefts loc (snd (fst m))) msgs)
        (SOUND: Memory.le mem0 cap0)
        (SPACES:
           forall loc ts (COV: covered loc ts cap0),
             <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
        (LEFTS:
           forall loc ts (UNATTACHABLE: unattachable cap0 loc ts),
             <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
        (MEM0: Memory.closed mem0)
        (PROM0: Memory.le prom0 mem0)
        (PROM1: Memory.le prom0 cap0)
    :
      exists cap1,
        (<<STEP: Memory.write_na ts prom0 cap0 loc from to msg prom1 cap1 msgs kinds kind>>) /\
        (<<SOUND: Memory.le mem1 cap1>>) /\
        (<<SPACES:
           forall loc ts (COV: covered loc ts cap1),
             <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
        (<<LEFTS:
           forall loc ts (UNATTACHABLE: unattachable cap1 loc ts),
             <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
  Proof.
    move WRITE at top. revert_until WRITE.
    induction WRITE; i.
    { exploit step_lifting_write; eauto. i. des. esplits; eauto. }
    inv WRITENOTIN_MSGS. ss. inv WRITENOTTO_MSGS. ss.
    exploit step_lifting_write; eauto. i. des.
    exploit IHWRITE; eauto.
    { eapply Memory.write_closed; eauto.
      - unguard. des; subst; econs; eauto.
      - unguard. des; subst; econs; eauto. apply Time.bot_spec.
    }
    { eapply Memory.write_le; try exact WRITE_EX; eauto. }
    { eapply Memory.write_le; try exact STEP; eauto. }
    i. des. esplits; eauto.
  Qed.

  Lemma step_lifting_is_racy
        lc0 mem0 loc to ord cap0
        (RACE: Local.is_racy lc0 mem0 loc to ord)
        (SOUND: Memory.le mem0 cap0):
    (<<STEP: Local.is_racy lc0 cap0 loc to ord>>).
  Proof.
    inv RACE. exploit SOUND; eauto.
  Qed.

  Lemma step_lifting lang st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 cap0 pf e
        (spaces lefts: Loc.t -> Time.t -> Prop)
        (STEP: Thread.step pf e (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
        (WRITENOTIN: write_not_in spaces e)
        (WRITENOTTO: write_not_to lefts e)
        (NOTCANCEL: ~ ThreadEvent.is_cancel e)
        (SOUND: Memory.le mem0 cap0)
        (SPACES:
           forall loc ts (COV: covered loc ts cap0),
             <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
        (LEFTS:
           forall loc ts (UNATACHABLE: unattachable cap0 loc ts),
             <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
        (MEM0: Memory.closed mem0)
        (LOCAL0: Local.wf lc0 mem0)
        (SC0: Memory.closed_timemap sc0 mem0)
    :
      exists cap1,
        (<<STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 cap0) (Thread.mk _ st1 lc1 sc1 cap1)>>) /\
        (<<SOUND: Memory.le mem1 cap1>>) /\
        (<<SPACES:
           forall loc ts (COV: covered loc ts cap1),
             <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
        (<<UNATTACHABLE:
           forall loc ts (COV: unattachable cap1 loc ts),
             <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).

  Proof.
    inv STEP.
    { inv STEP0. inv LOCAL. ss.
      destruct (Memory.op_kind_is_cancel kind) eqn:KIND; ss.
      { destruct kind; ss. inv PROMISE; ss. }
      exploit step_lifting_promise; eauto.
      { eapply LOCAL0. }
      { transitivity mem0; eauto. eapply LOCAL0. }
      { destruct kind; ss. }
      i. des. esplits; eauto. econs. econs.
      { econs; eauto. eapply memory_concrete_le_closed_msg; eauto. }
      { ss. destruct kind; ss. }
    }
    { inv STEP0. inv LOCAL.
      { esplits; eauto. econs 2; eauto. econs; eauto. }
      { inv LOCAL1. eapply SOUND in GET. esplits; eauto. econs 2; eauto. econs; eauto. }
      { inv LOCAL1.
        exploit step_lifting_write; eauto.
        { eapply LOCAL0. }
        { transitivity mem0; eauto. eapply LOCAL0. }
        i. des. esplits; eauto. econs 2; eauto. econs; eauto.
      }
      { inv LOCAL1. eapply SOUND in GET. inv LOCAL2.
        exploit step_lifting_write; eauto.
        { eapply LOCAL0. }
        { transitivity mem0; eauto. eapply LOCAL0. }
        i. des. esplits; eauto. econs 2; eauto. econs; eauto.
      }
      { esplits; eauto. econs 2; eauto. econs; eauto. }
      { esplits; eauto. econs 2; eauto. econs; eauto. }
      { esplits; eauto. econs 2; eauto. econs; eauto. }
      { inv LOCAL1. ss. des.
        exploit step_lifting_write_na; eauto.
        { eapply LOCAL0. }
        { transitivity mem0; eauto. eapply LOCAL0. }
        i. des. esplits; eauto. econs 2; eauto. econs; eauto.
      }
      { inv LOCAL1. exploit step_lifting_is_racy; eauto. i. des.
        esplits; eauto. econs 2; eauto. econs; eauto.
      }
      { inv LOCAL1. exploit step_lifting_is_racy; eauto. i. des.
        esplits; eauto. econs 2; eauto. econs; eauto.
      }
      { inv LOCAL1; try by (esplits; eauto; econs 2; eauto; econs; eauto).
        exploit step_lifting_is_racy; eauto. i. des.
        esplits; eauto. econs 2; eauto. econs; eauto.
      }
    }
  Qed.

  Lemma traced_step_lifting lang st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 cap0 tr
        (spaces lefts: Loc.t -> Time.t -> Prop)
        (STEPS: Trace.steps tr (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk _ st1 lc1 sc1 mem1))
        (EVENTS: List.Forall (fun em => <<SAT: (write_not_in spaces /1\ write_not_to lefts /1\ (fun e => ~ ThreadEvent.is_cancel e)) (snd em)>>) tr)
        (SOUND: Memory.le mem0 cap0)
        (SPACES:
           forall loc ts (COV: covered loc ts cap0),
             <<COV: covered loc ts mem0>> \/ <<SPACE: spaces loc ts>>)
        (LEFTS:
           forall loc ts (UNATACHABLE: unattachable cap0 loc ts),
             <<COV: unattachable mem0 loc ts>> \/ <<LEFT: lefts loc ts>>)
        (MEM0: Memory.closed mem0)
        (LOCAL0: Local.wf lc0 mem0)
        (SC0: Memory.closed_timemap sc0 mem0)
    :
      exists cap1,
        (<<STEPS: Trace.steps tr (Thread.mk _ st0 lc0 sc0 cap0) (Thread.mk _ st1 lc1 sc1 cap1)>>) /\
        (<<SOUND: Memory.le mem1 cap1>>) /\
        (<<SPACES:
           forall loc ts (COV: covered loc ts cap1),
             <<COV: covered loc ts mem1>> \/ spaces loc ts>>) /\
        (<<LEFTS:
           forall loc ts (UNATACHABLE: unattachable cap1 loc ts),
             <<COV: unattachable mem1 loc ts>> \/ lefts loc ts>>).
  Proof.
    remember (Thread.mk lang st0 lc0 sc0 mem0).
    remember (Thread.mk lang st1 lc1 sc1 mem1). ginduction STEPS.
    { i. clarify. esplits; eauto. }
    { i. clarify. inv EVENTS. ss. des.
      exploit Thread.step_future; eauto. i. des.
      destruct th1. ss. exploit step_lifting; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. exists cap2. splits; auto. econs; eauto.
    }
  Qed.

End LIFT.


Fixpoint intervals_sum (l: list (Loc.t * Interval.t)):
  Loc.t -> Time.t -> Prop :=
  match l with
  | [] => bot2
  | (loc, (from, to))::tl =>
    fun loc0 ts0 =>
      (loc0 = loc /\ Interval.mem (from, to) ts0) \/
      intervals_sum tl loc0 ts0
  end.

Fixpoint intervals_sum_left (l: list (Loc.t * Interval.t)):
  Loc.t -> Time.t -> Prop :=
  match l with
  | [] => bot2
  | (loc, (from, to))::tl =>
    fun loc0 ts0 =>
      (loc0 = loc /\ Time.le from ts0 /\ Time.lt ts0 to) \/
      intervals_sum_left tl loc0 ts0
  end.

Lemma intervals_sum_interval l
      loc ts
  :
    intervals_sum l loc ts <->
    exists from to,
      (<<IN: List.In (loc, (from, to)) l>>) /\ (<<ITV: Interval.mem (from, to) ts>>).
Proof.
  ginduction l; ss.
  { i; split; i; ss. des. ss. }
  { i; split; i; ss.
    { destruct a. destruct t0. des; clarify.
      { esplits; eauto. }
      { eapply IHl in H. des. esplits; eauto. }
    }
    { destruct a. destruct t0. des; clarify; eauto. right.
      eapply IHl. eauto. }
  }
Qed.

Lemma intervals_sum_left_interval l
      loc ts
  :
    intervals_sum_left l loc ts <->
    exists from to,
      (<<IN: List.In (loc, (from, to)) l>>) /\ (<<FROM: Time.le from ts>>) /\ (<<TO: Time.lt ts to>>).
Proof.
  ginduction l; ss.
  { i; split; i; ss. des. ss. }
  { i; split; i; ss.
    { destruct a. destruct t0. des; clarify.
      { esplits; eauto. }
      { eapply IHl in H. des. esplits; eauto. }
    }
    { destruct a. destruct t0. des; clarify; eauto. right.
      eapply IHl. eauto. }
  }
Qed.

Lemma intervals_sum_app l1 l2 loc ts:
  intervals_sum (l1 ++ l2) loc ts <->
  intervals_sum l1 loc ts \/ intervals_sum l2 loc ts.
Proof.
  repeat rewrite intervals_sum_interval. split; i; des.
  - apply List.in_app_or in IN. des; eauto.
  - esplits; eauto. apply List.in_or_app. eauto.
  - esplits; eauto. apply List.in_or_app. eauto.
Qed.


Inductive reservations_added:
  forall (l: list (Loc.t * Interval.t)) (mem0 mem1: Memory.t), Prop :=
| reservations_added_base
    mem0
  :
    reservations_added [] mem0 mem0
| reservations_added_cons
    mem0 mem1 mem2 loc from to tl
    (ADD: Memory.add mem0 loc from to Message.reserve mem1)
    (TL: reservations_added tl mem1 mem2)
    (WF: Time.lt from to)
  :
    reservations_added ((loc, (from, to))::tl) mem0 mem2
.

Lemma reservations_added_trans l0 l1 mem0 mem1 mem2
      (ADDED0: reservations_added l0 mem0 mem1)
      (ADDED1: reservations_added l1 mem1 mem2)
  :
    reservations_added (l0 ++ l1) mem0 mem2.
Proof.
  ginduction l0; eauto.
  { i. inv ADDED0. ss. }
  { i. inv ADDED0. exploit IHl0; eauto. i. econs; eauto. }
Qed.


Lemma reservations_added_cancel
      loc from to mem0 mem1 mem2 tl
      (CANCEL: Memory.remove mem1 loc from to Message.reserve mem0)
      (TL: reservations_added tl mem1 mem2)
      (WF: Time.lt from to)
  :
    reservations_added ((loc, (from, to))::tl) mem0 mem2.
Proof.
  econs; eauto.
  exploit (@Memory.add_exists mem0 loc from to Message.reserve); eauto.
  { i. erewrite Memory.remove_o in GET2; eauto. des_ifs.
    exploit Memory.get_disjoint.
    { eapply GET2. }
    { eapply Memory.remove_get0; eauto. }
    i. ss. des; clarify. symmetry. auto.
  }
  i. des. replace mem1 with mem3; auto. eapply Memory.ext.
  i. erewrite (@Memory.add_o mem3 mem0); eauto.
  erewrite (@Memory.remove_o mem0 mem1); eauto. des_ifs.
  ss. des; clarify. symmetry. eapply Memory.remove_get0; eauto.
Qed.

Inductive disjoint_intervals
  :
    forall (l: list (Loc.t * Interval.t)), Prop :=
| disjoint_base
  :
    disjoint_intervals []
| disjoint_intervals_cons
    loc from to tl
    (TL: disjoint_intervals tl)
    (NITV: forall ts (ITV: Interval.mem (from, to) ts),
        ~ intervals_sum tl loc ts)
    (TS: Time.lt from to)
  :
    disjoint_intervals ((loc, (from, to)) :: tl)
.
#[export] Hint Constructors disjoint_intervals: core.

Lemma disjoint_intervals_app
      l1 l2
      (DISJOINT1: disjoint_intervals l1)
      (DISJOINT2: disjoint_intervals l2)
      (DISJOINT12: forall loc ts
                     (ITV1: intervals_sum l1 loc ts)
                     (ITV2: intervals_sum l2 loc ts),
          False):
  disjoint_intervals (l1 ++ l2).
Proof.
  revert l2 DISJOINT2 DISJOINT12.
  induction DISJOINT1; i; ss.
  exploit IHDISJOINT1; eauto. i.
  econs; eauto. ii.
  rewrite intervals_sum_app in H. des; eauto.
  eapply NITV; eauto.
Qed.



Lemma promise_needed_spaces prom0 prom1 mem0 mem1
      loc from to msg kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (WF: kind <> Memory.op_kind_cancel)
  :
    ((<<ALREADY: forall ts (ITV: Interval.mem (from, to) ts), covered loc ts mem0>>) /\
     (<<COVERED: forall loc ts, covered loc ts mem1 <-> covered loc ts mem0>>))
    \/
    ((<<NEW: forall ts (ITV: Interval.mem (from, to) ts), ~ covered loc ts mem0>>) /\
     (<<COVERED: forall loc0 ts0,
         covered loc0 ts0 mem1 <-> covered loc0 ts0 mem0 \/ (loc0 = loc /\ Interval.mem (from, to) ts0)>>) /\
     (<<WF: Time.lt from to>>))
.
Proof.
  inv PROMISE.
  { right. exploit add_succeed_wf; try apply MEM. i. des. splits; auto.
    { ii. inv H. eapply DISJOINT; eauto. }
    { i. erewrite (@add_covered mem1); eauto. }
  }
  { left. exploit split_succeed_wf; try apply MEM. i. des. splits; auto.
    { ii. econs; eauto. eapply Interval.le_mem; eauto. econs; ss.
      { refl. }
      { left. auto. }
    }
    { i. eapply split_covered; eauto. }
  }
  { left. exploit lower_succeed_wf; try apply MEM. i. des. splits; auto.
    { ii. econs; eauto. }
    { i. eapply lower_covered; eauto. }
  }
  { ss. }
Qed.

Lemma write_needed_spaces prom0 prom1 mem0 mem1
      loc from to msg kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
  :
    ((<<ALREADY: forall ts (ITV: Interval.mem (from, to) ts), covered loc ts mem0>>) /\
     (<<COVERED: forall loc ts, covered loc ts mem1 <-> covered loc ts mem0>>))
    \/
    ((<<NEW: forall ts (ITV: Interval.mem (from, to) ts), ~ covered loc ts mem0>>) /\
     (<<COVERED: forall loc0 ts0,
         covered loc0 ts0 mem1 <-> covered loc0 ts0 mem0 \/ (loc0 = loc /\ Interval.mem (from, to) ts0)>>) /\
     (<<WF: Time.lt from to>>))
.
Proof.
  exploit Memory.write_not_cancel; eauto. i.
  inv WRITE. eapply promise_needed_spaces; eauto.
  destruct kind; ss.
Qed.

Require Import MemoryFacts.

Lemma write_na_needed_spaces
      ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind
      ord
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind):
  exists l,
    (<<L: forall loc' from' to' (IN: List.In (loc', (from', to')) l),
        loc = loc' /\
        (from' = from /\ to' = to \/
         exists msg, List.In (from', to', msg) msgs)>>) /\
    (<<WRITENOTIN: write_not_in
                     (fun loc ts => ~ (covered loc ts mem0 \/ intervals_sum l loc ts))
                     (ThreadEvent.write_na loc msgs from to val ord)>>) /\
    (<<DISJOINT: disjoint_intervals l>>) /\
    (<<NITV: forall loc ts (ITV: intervals_sum l loc ts), ~ covered loc ts mem0>>) /\
    (<<COVERED: forall loc ts, covered loc ts mem1 <-> covered loc ts mem0 \/ intervals_sum l loc ts>>).
Proof.
  induction WRITE.
  { exploit write_needed_spaces; eauto. i. des.
    - exists []. splits; i; ss; eauto.
      + split; ss. ii. apply H. rewrite <- COVERED. left.
        exploit Memory.write_not_cancel; eauto. i.
        inv WRITE. exploit Memory.promise_get0; eauto. i. des.
        econs; eauto.
      + rewrite COVERED. split; i; des; ss; eauto.
    - exists [(loc, (from, to))]. splits; i; ss; eauto.
      + des; ss. inv IN. auto.
      + split; ss. ii. eauto.
      + des; ss. subst. eauto.
      + rewrite COVERED. split; i; des; eauto. ss.
  }
  exploit write_needed_spaces; eauto. ss. i. des.
  - exists l. splits; i; ss; eauto.
    + exploit L; eauto. i. des; eauto.
    + ii. exploit WRITENOTIN; eauto. rewrite COVERED0. ss.
    + econs; eauto.
      eapply List.Forall_impl; try eapply WRITENOTIN0. s. i.
      rewrite <- COVERED0. eauto.
    + rewrite <- COVERED0. eauto.
    + rewrite <- COVERED0. eauto.
  - exists ((loc, (from', to')) :: l). splits; ss; i.
    + des; try by (inv IN; eauto).
      exploit L; eauto. i. des; eauto.
    + hexploit WRITENOTIN; eauto. ii. apply H.
      rewrite COVERED0. ii. apply H0. des; eauto.
    + econs; ss; i.
      * ii. apply H. eauto.
      * eapply List.Forall_impl; try eapply WRITENOTIN0. s. i.
        hexploit H; eauto.
        rewrite COVERED0. ii.
        apply H0. ii. apply H1. des; eauto.
    + econs; eauto. ii.
      exploit NITV; eauto. rewrite COVERED0. eauto.
    + des; subst; eauto.
      hexploit NITV; eauto. ii. apply H.
      rewrite COVERED0. eauto.
    + rewrite COVERED. rewrite COVERED0. split; i; des; eauto.
Qed.

Lemma step_needed_spaces lang (th0 th1: Thread.t lang) pf e
      (times: Loc.t -> Time.t -> Prop)
      (STEP: Thread.step pf e th0 th1)
      (NOTCANCEL: ~ ThreadEvent.is_cancel e)
      (WFTIME: wf_time_evt times e)
  :
    exists l,
      (<<WRITENOTIN:
         write_not_in (fun loc ts => ~ (covered loc ts (Thread.memory th0) \/ intervals_sum l loc ts)) e>>) /\
      (<<DISJOINT: disjoint_intervals l>>) /\
      (<<NITV: forall loc ts (ITV: intervals_sum l loc ts), ~ covered loc ts (Thread.memory th0)>>) /\
      (<<COVERED: forall loc ts,
          covered loc ts (Thread.memory th1) <-> covered loc ts (Thread.memory th0) \/ intervals_sum l loc ts>>) /\
      (<<TIMES: List.Forall (fun locitv =>
                               times (fst locitv) (fst (snd locitv)) /\
                               times (fst locitv) (snd (snd locitv))) l>>)
.
Proof.
  inv STEP; inv STEP0; inv LOCAL; ss.
  { exploit promise_needed_spaces; eauto.
    { ii. subst. inv PROMISE; ss. }
    i. des.
    { exists []. splits; auto.
      - condtac; ss. ii. exploit ALREADY; eauto.
      - i. rewrite COVERED. split; eauto. i. des; eauto. inv H.
    }
    { exists [(loc, (from, to))]. splits; auto.
      - condtac; ss. ii. hexploit NEW; eauto.
      - i. inv ITV; ss. des. subst. eauto.
      - i. rewrite COVERED. split; i; des; eauto.
        + right. econs; eauto.
        + inv H; ss. des. eauto.
    }
  }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { inv LOCAL0. exploit write_needed_spaces; eauto. i. des.
    { exists []. splits; auto.
      i. rewrite COVERED. split; eauto. i. des; eauto. inv H.
    }
    { exists [(loc, (from, to))]. splits; auto.
      - ii. apply H. right. econs. eauto.
      - i. inv ITV; ss. des. subst. eauto.
      - i. rewrite COVERED. split; i; des; eauto.
        + right. econs; eauto.
        + inv H; ss. des. eauto.
    }
  }
  { inv LOCAL1. inv LOCAL2. ss.
    exploit write_needed_spaces; eauto. i. des.
    { exists []. splits; auto.
      i. rewrite COVERED. split; eauto. i. des; eauto. inv H.
    }
    { exists [(loc, (tsr, tsw))]. splits; auto.
      - ii. apply H. right. econs. eauto.
      - i. inv ITV; ss. des. subst. eauto.
      - i. rewrite COVERED. split; i; des; eauto.
        + right. econs; eauto.
        + inv H; ss. des. eauto.
    }
  }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { inv LOCAL0. exploit write_na_needed_spaces; eauto.
    instantiate (1 := ord). s. i. des.
    exists l. splits; eauto.
    rewrite List.Forall_forall. i.
    destruct x as [loc' [from' to']].
    exploit L; eauto. i. des; subst; ss.
    rewrite List.Forall_forall in MSGS.
    exploit MSGS; eauto.
  }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
  { exists []. splits; eauto. i. split; i; des; eauto. inv H. }
Qed.

Lemma traced_steps_needed_spaces lang (th0 th1: Thread.t lang) tr
      (times: Loc.t -> Time.t -> Prop)
      (STEP: Trace.steps tr th0 th1)
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ ThreadEvent.is_cancel e) /1\ wf_time_evt times) (snd em)>>) tr)
  :
    exists l,
      (<<WRITENOTIN:
         List.Forall (fun em => <<SAT: write_not_in (fun loc ts => ~ (covered loc ts (Thread.memory th0) \/ intervals_sum l loc ts)) (snd em)>>) tr>>) /\
      (<<DISJOINT: disjoint_intervals l>>) /\
      (<<NITV: forall loc ts (ITV: intervals_sum l loc ts), ~ covered loc ts (Thread.memory th0)>>) /\
      (<<COVERED: forall loc ts,
          covered loc ts (Thread.memory th1) <-> covered loc ts (Thread.memory th0) \/ intervals_sum l loc ts>>) /\
      (<<TIMES: List.Forall (fun locitv =>
                               times (fst locitv) (fst (snd locitv)) /\
                               times (fst locitv) (snd (snd locitv))) l>>)
.
Proof.
  ginduction STEP; i.
  { exists []. splits; auto. i. ss. split; auto. i. des; ss. }
  subst. inv EVENTS. des. exploit IHSTEP; eauto. i. des. clear IHSTEP.
  exploit step_needed_spaces; eauto. i. des.
  exists (l0 ++ l). splits.
  { econs; ss.
    - eapply write_not_in_mon; eauto. s. ii.
      apply PR. des; eauto. right.
      rewrite intervals_sum_interval in *. des.
      esplits; eauto. apply List.in_or_app. eauto.
    - eapply List.Forall_impl; try apply WRITENOTIN; eauto. s. i. des.
      eapply write_not_in_mon; eauto. s. ii.
      apply PR. rewrite COVERED0 in H3. des; eauto.
      + right. rewrite intervals_sum_interval in *. des.
        esplits; eauto. apply List.in_or_app. eauto.
      + right. rewrite intervals_sum_interval in *. des.
        esplits; eauto. apply List.in_or_app. eauto.
  }
  { apply disjoint_intervals_app; eauto. i.
    hexploit NITV; eauto. i.
    rewrite COVERED0 in H. apply H. eauto.
  }
  { i. rewrite intervals_sum_app in ITV. des; eauto.
    hexploit NITV; eauto. rewrite COVERED0. ii.
    apply H. eauto.
  }
  { i. rewrite COVERED, COVERED0, intervals_sum_app.
    split; i; des; eauto.
  }
  { rewrite List.Forall_app. split; ss. }
Qed.

Lemma reserve_empty_intervals times lang (th: Thread.t lang) l
      (DISJOINT: disjoint_intervals l)
      (NITV: forall loc ts (ITV: intervals_sum l loc ts),
          ~ covered loc ts (Thread.memory th))
      (MLE: Memory.le (Local.promises (Thread.local th)) (Thread.memory th))
      (TIMES: List.Forall (fun locitv =>
                             times (fst locitv) (fst (snd locitv)) /\
                             times (fst locitv) (snd (snd locitv))) l)
  :
    exists tr prom' mem',
      (<<STEPS: Trace.steps tr th (Thread.mk _ (Thread.state th) (Local.mk (Local.tview (Thread.local th)) prom') (Thread.sc th) mem')>>) /\
      (<<RESERVETRACE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve /1\ wf_time_evt times) (snd em)>>) tr>>) /\
      (<<ADDEDPROM: reservations_added l (Local.promises (Thread.local th)) prom'>>) /\
      (<<ADDEDMEM: reservations_added l (Thread.memory th) mem'>>)
.
Proof.
  ginduction l; i.
  { destruct th. destruct local. ss. exists []. esplits; eauto.
    { econs. }
    { econs. }
  }
  { inv DISJOINT. inv TIMES. ss.
    exploit (@Memory.add_exists (Thread.memory th) loc from to Message.reserve); eauto.
    { ii. eapply NITV.
      { left. eauto. }
      { econs; eauto. }
    }
    intros [mem MEM].
    exploit (@Memory.add_exists_le (Local.promises (Thread.local th)) (Thread.memory th)); eauto.
    intros [prom PROM].
    assert (STEP: Thread.step false (ThreadEvent.promise loc from to Message.reserve Memory.op_kind_add) th (Thread.mk _ (Thread.state th) (Local.mk (Local.tview (Thread.local th)) prom) (Thread.sc th) mem)).
    { destruct th. ss. econs. econs; ss. econs; ss. econs; ss. }
    exploit (@IHl times lang (Thread.mk _ (Thread.state th) (Local.mk (Local.tview (Thread.local th)) prom) (Thread.sc th) mem)); eauto; ss.
    { i. erewrite add_covered; eauto. ii. des; subst.
      { eapply NITV; eauto. }
      { eapply NITV0; eauto. }
    }
    { hexploit step_promises_le; eauto.
      { econs; eauto. }
      i. ss.
    }
    i. des. esplits.
    { econs; eauto. }
    { econs; ss. }
    { econs; eauto. }
    { econs; eauto. }
  }
Qed.

Lemma reservations_added_get_same mem1 mem0 l
      (ADDED: reservations_added l mem0 mem1)
      loc ts
      (NIN: forall from, ~ List.In (loc, (from, ts)) l)
  :
    Memory.get loc ts mem1 = Memory.get loc ts mem0.
Proof.
  ginduction ADDED; auto. i.
  erewrite IHADDED; eauto.
  { erewrite (@Memory.add_o mem1 mem0); eauto. des_ifs. ss. des; clarify.
    exfalso. eapply NIN; eauto. }
  { ii. ss. eapply NIN; eauto. }
Qed.

Lemma reservations_added_get_none mem1 mem0 l
      (ADDED: reservations_added l mem0 mem1)
      loc from ts
      (IN: List.In (loc, (from, ts)) l)
  :
    Memory.get loc ts mem0 = None.
Proof.
  ginduction ADDED; ss. i. des; clarify.
  { eapply Memory.add_get0; eauto. }
  { eapply IHADDED in IN. erewrite Memory.add_o in IN; eauto. des_ifs. }
Qed.

Lemma reservations_added_le_le l mem0 mem1 cap1 cap0
      (ADDED0: reservations_added l mem0 mem1)
      (MLE: Memory.le mem1 cap1)
      (ADDED1: reservations_added l cap0 cap1)
  :
    Memory.le mem0 cap0.
Proof.
  ii. destruct (classic (forall from, ~ List.In (loc, (from, to)) l)).
  { erewrite <- (@reservations_added_get_same cap1 cap0); eauto.
    erewrite <- (@reservations_added_get_same mem1 mem0) in LHS; eauto. }
  { eapply not_all_not_ex in H. des.
    erewrite reservations_added_get_none in LHS; eauto. ss. }
Qed.

Lemma cancel_reservations_added times l prom lang lc
      (ADDEDPROM: reservations_added l prom (Local.promises lc))
      (TIMES: List.Forall (fun locitv =>
                             times (fst locitv) (fst (snd locitv)) /\
                             times (fst locitv) (snd (snd locitv))) l)
  :
    exists tr,
      (<<CANCELTRACE: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) tr>>) /\
    forall
      (st: Language.state lang) sc mem
      (MLE: Memory.le (Local.promises lc) mem),
    exists mem',
      (<<STEPS: Trace.steps tr (Thread.mk _ st lc sc mem) (Thread.mk _ st (Local.mk (Local.tview lc) prom) sc mem')>>) /\
      (<<ADDEDMEM: reservations_added l mem' mem>>)
.
Proof.
  ginduction l; i.
  { exists []. splits; ss. i. destruct lc. ss. inv ADDEDPROM. esplits; eauto. econs. }
  { inv TIMES. inv ADDEDPROM.
    exploit IHl; eauto. i. des.
    eexists (tr++[(Local.mk (Local.tview lc) mem1, ThreadEvent.promise loc from to Message.reserve Memory.op_kind_cancel)]).
    splits.
    { eapply Forall_app; eauto. econs; ss. }
    i. exploit (x0 st sc mem); eauto. i. des.
    exploit (@Memory.remove_exists mem1 loc from to Message.reserve); eauto.
    { eapply Memory.add_get0; eauto. } i. des.
    exploit (@Memory.remove_exists_le mem1 mem'); eauto.
    { eapply trace_steps_promises_le in STEPS; eauto. } i. des.
    assert (mem2 = prom).
    { symmetry. eapply MemoryMerge.add_remove; eauto. } subst.
    esplits.
    { eapply Trace.steps_trans.
      { eapply STEPS. }
      { econs; eauto. econs 1; eauto. econs; eauto. }
    }
    { eapply reservations_added_cancel; eauto. }
  }
Qed.

Lemma step_finte_write_to (e: ThreadEvent.t)
      (times: Loc.t -> Time.t -> Prop)
      (EVENT: wf_time_evt times e)
  :
    exists (l: list (Loc.t * Time.t)),
      (<<EVENT: write_not_to (fun loc ts => ~ List.In (loc, ts) l) e>>) /\
      (<<TIMES: List.Forall (fun locts => times (fst locts) (snd locts)) l>>).
Proof.
  destruct e; try by (exists []; esplits; eauto); ss.
  { exists [(loc, to)]. esplits; ss.
    { des_ifs. ii. eapply H. auto. }
    { econs; ss. des. auto. }
  }
  { exists [(loc, to)]. esplits; ss.
    { ii. eapply H. auto. }
    { econs; ss. des. auto. }
  }
  { exists ((loc, to) :: (List.map (fun m => (loc, snd (fst m))) msgs)). s. splits.
    - ii. apply H. left. auto.
    - rewrite List.Forall_forall. ii. apply H0.
      right. exploit List.in_map; eauto.
      instantiate (1 := (fun m => (loc, snd (fst m)))). ss.
    - ss. des. econs; eauto.
      induction MSGS; ss. des. econs; eauto.
  }
  { exists [(loc, tsw)]. esplits; ss.
    { ii. eapply H. auto. }
    { econs; ss. des. auto. }
  }
Qed.

Lemma write_not_to_mon P0 P1
      (LE: P0 <2= P1)
  :
    write_not_to P1 <1= write_not_to P0.
Proof.
  ii. unfold write_not_to in *. des_ifs; auto.
  des. split; auto.
  induction PR0; eauto.
Qed.

Lemma traced_steps_finte_write_to (tr: Trace.t)
      (times: Loc.t -> Time.t -> Prop)
      (EVENTS: List.Forall (fun em => <<SAT: (wf_time_evt times) (snd em)>>) tr)
  :
    exists (l: list (Loc.t * Time.t)),
      (<<EVENTS: List.Forall (fun em => write_not_to (fun loc ts => ~ List.In (loc, ts) l) (snd em)) tr>>) /\
      (<<TIMES: List.Forall (fun locts => times (fst locts) (snd locts)) l>>).
Proof.
  ginduction tr.
  { i. inv EVENTS. exists []. esplits; eauto. }
  { i. inv EVENTS. exploit IHtr; eauto. i. des.
    exploit (@step_finte_write_to (snd a)); eauto. i. des.
    exists (l0 ++ l). esplits; eauto.
    { econs; eauto.
      { eapply write_not_to_mon; eauto. ii. eapply PR. eapply List.in_or_app; eauto. }
      { eapply List.Forall_impl; eauto. i. ss.
        eapply write_not_to_mon; eauto. ii. eapply PR. eapply List.in_or_app; eauto. }
    }
    { eapply Forall_app; eauto. }
  }
Qed.

Lemma reserve_write_to (times: Loc.t -> Time.t -> Prop)
      (DIVERGE: forall loc ts,
          exists ts',
            (<<TIMES: times loc ts'>>) /\
            (<<TS: Time.lt ts ts'>>))
      mem
      (MWF: memory_times_wf times mem)
      loc ts
      (TIMES: times loc ts)
  :
    (<<ALREADY: unattachable mem loc ts>>) \/
    (<<NEW: exists from mem',
        (<<TS: Time.lt ts from>>) /\
        (<<ADD: Memory.add mem loc ts from Message.reserve mem'>>) /\
        (<<TIMES: times loc from>>) /\
        (<<MWF: memory_times_wf times mem'>>)>>).
Proof.
  destruct (classic (unattachable mem loc ts)); auto. right.
  hexploit (@cell_elements_least
              (mem loc)
              (fun to => exists from msg,
                   (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
                   (<<TS: Time.lt ts from>>))).
  i. des.
  { hexploit (@Memory.add_exists mem loc ts from0 Message.reserve); ss.
    { ii. destruct (Time.le_lt_dec from2 ts).
      { eapply H. econs; eauto.
        inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      { dup GET2. eapply LEAST in GET2.
        { exploit memory_get_to_mon.
          { eapply GET1. }
          { eapply GET0. }
          { inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
          i. timetac.
        }
        esplits; eauto.
      }
    }
    i. des. esplits; eauto.
    { eapply MWF in GET0. des; auto. }
    { eapply MWF in GET0. des.
      ii. erewrite Memory.add_o in GET0; eauto. des_ifs.
      { ss. des; clarify. }
      { eapply MWF; eauto. }
    }
  }
  { hexploit (DIVERGE loc ts). i. des.
    hexploit (@Memory.add_exists mem loc ts ts' Message.reserve); ss.
    { ii. eapply EMPTY; eauto. esplits; eauto.
      destruct (Time.le_lt_dec from2 ts); auto. exfalso.
      eapply H. econs; eauto.
      inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
    i. des. esplits; eauto.
    ii. erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. }
    { eapply MWF; eauto. }
  }
Qed.

Lemma reserve_write_tos times lang (th: Thread.t lang) tos
      (DIVERGE: forall loc ts,
          exists ts',
            (<<TIMES: times loc ts'>>) /\
            (<<TS: Time.lt ts ts'>>))
      (MWF: memory_times_wf times (Thread.memory th))
      (MLE: Memory.le (Local.promises (Thread.local th)) (Thread.memory th))
      (TIMES: List.Forall (fun locts => times (fst locts) (snd locts)) tos)
  :
    exists l tr prom' mem',
      (<<STEPS: Trace.steps tr th (Thread.mk _ (Thread.state th) (Local.mk (Local.tview (Thread.local th)) prom') (Thread.sc th) mem')>>) /\
      (<<RESERVETRACE: List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve /1\ wf_time_evt times) (snd em)>>) tr>>) /\
      (<<ADDEDPROM: reservations_added l (Local.promises (Thread.local th)) prom'>>) /\
      (<<ADDEDMEM: reservations_added l (Thread.memory th) mem'>>) /\
      (<<WRITETO: forall loc ts (IN: List.In (loc, ts) tos),
          unattachable mem' loc ts>>) /\
      (<<TIMES: List.Forall (fun locitv =>
                               times (fst locitv) (fst (snd locitv)) /\
                               times (fst locitv) (snd (snd locitv))) l>>)
.
Proof.
  ginduction tos; i; ss.
  { exists [], []. destruct th. destruct local. ss. esplits; eauto; ss.
    { econs. }
    { econs. }
  }
  { inv TIMES. exploit IHtos; eauto. i. des.
    exploit reserve_write_to.
    { eauto. }
    { eapply memory_times_wf_traced in STEPS; eauto.
      eapply List.Forall_impl; eauto. i. ss. des; auto. }
    { eauto. }
    i. ss. des.
    { exists l, tr. esplits; eauto. i. des; auto. clarify. }
    { exploit (@Memory.add_exists_le prom' mem'); eauto.
      { eapply trace_steps_promises_le in STEPS; eauto. }
      i. des.
      assert (PROM: Memory.promise prom' mem' (fst a) (snd a) from Message.reserve promises2 mem'0 Memory.op_kind_add).
      { econs; eauto. }
      destruct th. esplits.
      { eapply Trace.steps_trans.
        { eauto. }
        { econs 2.
          { econs 1. econs; eauto. }
          { econs 1. }
          { ss. }
        }
      }
      { eapply Forall_app; eauto. econs; ss. }
      { ss. eapply reservations_added_trans.
        { eauto. }
        { econs; eauto. econs. }
      }
      { ss. eapply reservations_added_trans.
        { eauto. }
        { econs; eauto. econs. }
      }
      { i. erewrite add_unattachable; eauto. des; clarify.
        { right. splits; ss. refl. }
        { eauto. }
      }
      { eapply Forall_app; eauto. }
    }
  }
Qed.



Lemma reservations_added_non_covered l mem0 mem1
      (ADDED: reservations_added l mem0 mem1)
      loc ts
      (COVERED: covered loc ts mem0)
  :
    ~ intervals_sum l loc ts.
Proof.
  ginduction l; eauto. i. inv ADDED. ss. ii.
  des; clarify.
  { inv COVERED. eapply add_succeed_wf in ADD. des.
    eapply DISJOINT; eauto. }
  { eapply IHl; eauto. erewrite add_covered; eauto. }
Qed.

Lemma add_unattachable_disjoint mem1 mem0 loc from to msg
      (ADD: Memory.add mem0 loc from to msg mem1)
      loc0 ts0
      (UNATTACHABLE: unattachable mem0 loc0 ts0)
  :
    ~ (loc0 = loc /\ Time.le from ts0 /\ Time.lt ts0 to).
Proof.
  ii. des; subst. inv UNATTACHABLE.
  exploit add_succeed_wf; eauto. i. des.
  hexploit DISJOINT; eauto. i. eapply disjoint_equivalent2 in H. des; ss.
  { eapply TS1. eapply TimeFacts.le_lt_lt; eauto. }
  { eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
    { eapply TS0. } eapply TimeFacts.le_lt_lt.
    { instantiate (1:=ts0). unfold Time.join. des_ifs. }
    { unfold Time.meet. des_ifs. }
  }
Qed.

Lemma reservations_added_non_unattachable l mem0 mem1
      (ADDED: reservations_added l mem0 mem1)
      loc ts
      (UNATTACHABLE: unattachable mem0 loc ts)
  :
    ~ intervals_sum_left l loc ts.
Proof.
  ginduction l; eauto. i. inv ADDED. ss. ii.
  des; clarify.
  { exploit add_unattachable_disjoint; eauto. }
  { eapply IHl; eauto. erewrite add_unattachable; eauto. }
Qed.

Lemma reservations_added_unattachable l mem0 mem1
      (ADDED: reservations_added l mem0 mem1)
      loc ts
      (UNATTACHABLE: unattachable mem1 loc ts)
  :
    unattachable mem0 loc ts \/ intervals_sum_left l loc ts.
Proof.
  ginduction l; eauto. i.
  { inv ADDED. auto. }
  { i. inv ADDED. eapply IHl in TL; eauto. ss.
    erewrite add_unattachable in TL; eauto. des; auto. }
Qed.

Definition eventable (mem prom: Memory.t) (spaces: Loc.t -> Time.t -> Prop)
           (loc: Loc.t) (ts: Time.t): Prop :=
  concrete_promised mem loc ts \/
  covered loc ts prom \/
  spaces loc ts.

Definition eventable_below (mem prom: Memory.t) (spaces: Loc.t -> Time.t -> Prop)
           (loc: Loc.t) (ts: Time.t): Prop :=
  exists to, <<TIME: eventable mem prom spaces loc to>> /\ <<TS: Time.le ts to>>.

Lemma eventable_le_below mem0 prom0 mem1 prom1 spaces
      (INCR: eventable mem1 prom1 spaces <2= eventable mem0 prom0 spaces)
  :
    eventable_below mem1 prom1 spaces <2= eventable_below mem0 prom0 spaces.
Proof.
  ii. unfold eventable_below in *. des. esplits; eauto.
Qed.


Lemma event_in_concrete_or_writes_promise (spaces: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (NOTIN: if Memory.op_kind_is_cancel kind
              then True
              else (forall ts (ITV: Interval.mem (from, to) ts),
                       spaces loc ts \/ covered loc ts mem0))
      (CLOSED: Memory.closed mem0)
  :
    (<<INCR: eventable mem1 prom1 spaces <2= eventable mem0 prom0 spaces>>) /\
    (<<FROM: eventable_below mem0 prom0 spaces loc from>>) /\
    (<<TO: eventable_below mem0 prom0 spaces loc to>>).
Proof.
  unfold eventable. inv PROMISE.
  { exploit add_succeed_wf; try apply MEM; eauto. i. des.
    splits.
    { ii. des; auto.
      { inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
        { ss. des; clarify. right. exploit NOTIN; eauto.
          { econs; eauto. refl. }
          i. des; auto. inv x. exfalso. eapply DISJOINT; eauto.
          econs; ss. refl.
        }
        { left. econs; eauto. }
      }
      { erewrite add_covered in PR; eauto. des; auto. subst.
        right. right. exploit NOTIN; eauto. i. des; auto.
        inv x. exfalso. eapply DISJOINT; eauto. }
    }
    { exists to. esplits; eauto.
      { right. right. exploit NOTIN; eauto.
        { econs; eauto. refl. }
        i. des; auto. inv x. exfalso. eapply DISJOINT; eauto.
        econs; ss. refl.
      }
      { left. auto. }
    }
    { exists to. esplits; eauto.
      { right. right. exploit NOTIN; eauto.
        { econs; eauto. refl. }
        i. des; auto. inv x. exfalso. eapply DISJOINT; eauto.
        econs; ss. refl.
      }
      { refl. }
    }
  }
  { exploit split_succeed_wf; try apply PROMISES; eauto. i. des.
    splits.
    { ii. des; auto.
      { inv PR. erewrite Memory.split_o in GET; eauto. des_ifs.
        { ss. des; clarify. right. left. econs; eauto.
          econs; eauto. ss. left. auto. }
        { ss. des; clarify. right. left. econs; eauto.
          econs; eauto. ss. refl. }
        { left. econs; eauto. }
      }
      { erewrite split_covered in PR; eauto. }
    }
    { exists ts3. esplits; eauto.
      { right. left. econs; eauto. econs; eauto. refl. }
      { left. etrans; eauto. }
    }
    { exists ts3. esplits; eauto.
      { right. left. econs; eauto. econs; eauto. refl. }
      { left. auto. }
    }
  }
  { exploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
    splits.
    { ii. des; auto.
      { inv PR. erewrite Memory.lower_o in GET0; eauto. des_ifs.
        { ss. des; clarify. right. left. econs; eauto.
          econs; eauto. ss. refl. }
        { left. econs; eauto. }
      }
      { erewrite lower_covered in PR; eauto. }
    }
    { exists to. esplits; eauto.
      { right. left. econs; eauto. econs; eauto. refl. }
      { left. eauto. }
    }
    { exists to. esplits; eauto.
      { right. left. econs; eauto. econs; eauto. refl. }
      { refl. }
    }
  }
  { exploit Memory.remove_get0; try apply PROMISES; eauto. i. des.
    assert (TS: Time.lt from to).
    { exploit Memory.remove_get0; try apply MEM; eauto. i. des.
      inv CLOSED. apply memory_get_ts_strong in GET. des; auto.
      subst. erewrite INHABITED in GET1. ss. }
    splits.
    { ii. des; auto.
      { inv PR. erewrite Memory.remove_o in GET1; eauto. des_ifs.
        left. econs; eauto. }
      { erewrite remove_covered in PR; eauto. des; auto. }
    }
    { exists to. esplits; eauto.
      { right. left. econs; eauto. econs; eauto. refl. }
      { left. eauto. }
    }
    { exists to. esplits; eauto.
      { right. left. econs; eauto. econs; eauto. refl. }
      { refl. }
    }
  }
Qed.

Lemma event_in_concrete_or_writes_write (spaces: Loc.t -> Time.t -> Prop)
      prom0 mem0 loc from to prom1 mem1 msg kind
      (WRITE: Memory.write prom0 mem0 loc from to msg prom1 mem1 kind)
      (NOTIN: if Memory.op_kind_is_cancel kind
              then True
              else (forall ts (ITV: Interval.mem (from, to) ts),
                       spaces loc ts \/ covered loc ts mem0))
      (CLOSED: Memory.closed mem0)
  :
    (<<INCR: eventable mem1 prom1 spaces <2= eventable mem0 prom0 spaces>>) /\
    (<<FROM: eventable_below mem0 prom0 spaces loc from>>) /\
    (<<TO: eventable_below mem0 prom0 spaces loc to>>).
Proof.
  inv WRITE.
  exploit event_in_concrete_or_writes_promise; eauto. i. des. esplits; eauto.
  i. eapply INCR. unfold eventable in *. des; auto.
  erewrite remove_covered in PR; eauto. des; auto.
Qed.

Lemma event_in_concrete_or_writes_write_na (spaces: Loc.t -> Time.t -> Prop)
      ts prom0 mem0 loc from to prom1 mem1 val msgs kinds kind
      (WRITE: Memory.write_na ts prom0 mem0 loc from to val prom1 mem1 msgs kinds kind)
      (NOTIN: forall ts (ITV: Interval.mem (from, to) ts),
          spaces loc ts \/ covered loc ts mem0)
      (NOTIN_MSGS: List.Forall
                     (fun m => forall ts (ITV: Interval.mem (fst m) ts),
                          spaces loc ts \/ covered loc ts mem0)
                     msgs)
      (CLOSED: Memory.closed mem0)
  :
    (<<INCR: eventable mem1 prom1 spaces <2= eventable mem0 prom0 spaces>>) /\
    (<<FROM: eventable_below mem0 prom0 spaces loc from>>) /\
    (<<TO: eventable_below mem0 prom0 spaces loc to>>) /\
    (<<MSGS: List.Forall
               (fun m => eventable_below mem0 prom0 spaces loc (fst (fst m)) /\
                      eventable_below mem0 prom0 spaces loc (snd (fst m)))
               msgs>>).
Proof.
  induction WRITE.
  { exploit event_in_concrete_or_writes_write; eauto.
    { condtac; eauto. }
    i. des. splits; auto.
  }
  inv NOTIN_MSGS. ss.
  exploit event_in_concrete_or_writes_write; eauto.
  { condtac; eauto. }
  i. des.
  exploit IHWRITE; eauto.
  { i. exploit NOTIN; eauto. i. des; eauto.
    right. eapply write_covered_increase; eauto.
  }
  { eapply List.Forall_impl; try eapply H2. s. i.
    exploit H; eauto. i. des; eauto.
    right. eapply write_covered_increase; eauto.
  }
  { eapply Memory.write_closed; eauto.
    { unguard. des; subst; ss. econs. ss. }
    { unguard. des; subst; ss. econs. apply Time.bot_spec. }
  }
  i. des. splits; auto.
  - eapply eventable_le_below; eauto.
  - eapply eventable_le_below; eauto.
  - econs; ss.
    eapply List.Forall_impl; try eapply MSGS. s. i. des.
    split; eapply eventable_le_below; eauto.
Qed.

Lemma step_eventable_time lang (th0 th1: Thread.t lang) pf e
      (spaces: Loc.t -> Time.t -> Prop)
      (STEP: Thread.step pf e th0 th1)
      (WRITENOTIN: write_not_in (fun loc ts => ~ (spaces loc ts \/ covered loc ts (Thread.memory th0))) e)
      (CLOSED: Memory.closed (Thread.memory th0))
  :
    (<<INCR: eventable (Thread.memory th1) (Local.promises (Thread.local th1)) spaces <2=
             eventable (Thread.memory th0) (Local.promises (Thread.local th0)) spaces>>) /\
    (<<TIMES: tevent_map_weak
                (fun loc ts fts =>
                   ts = fts /\ eventable_below (Thread.memory th0) (Local.promises (Thread.local th0)) spaces loc ts)
                e e>>).
Proof.
  inv STEP.
  { inv STEP0; ss. inv LOCAL.
    eapply event_in_concrete_or_writes_promise in PROMISE; ss.
    { des. splits; eauto. econs; eauto. }
    { des_ifs. ii. apply NNPP. eapply WRITENOTIN; eauto. }
  }
  { inv STEP0; ss. inv LOCAL; ss; eauto.
    { splits; auto. econs. }
    { inv LOCAL0. ss. splits; auto. econs; eauto. split; auto.
      exists ts. splits; ss.
      { left. econs; eauto. ss. }
      { refl. }
    }
    { inv LOCAL0. eapply event_in_concrete_or_writes_write in WRITE; eauto.
      { des. splits; eauto. econs; eauto. }
      { des_ifs. ii. eapply NNPP. eauto. }
    }
    { inv LOCAL1. inv LOCAL2. eapply event_in_concrete_or_writes_write in WRITE; eauto.
      { des. splits; eauto. econs; eauto. }
      { des_ifs. ii. eapply NNPP. eauto. }
    }
    { inv LOCAL0. ss. splits; auto. econs; eauto. }
    { inv LOCAL0. ss. splits; auto. econs; eauto. }
    { inv LOCAL0. ss. splits; auto. econs; eauto. }
    { inv LOCAL0. ss.
      eapply event_in_concrete_or_writes_write_na in WRITE; eauto.
      { instantiate (1 := spaces) in WRITE.
        des. splits; eauto. econs; eauto.
        clear - MSGS. induction MSGS; eauto.
        des. econs; eauto. splits; eauto.
        destruct x as [[]]. destruct t1; econs.
      }
      { des. i. eapply NNPP. eauto. }
      { des. eapply List.Forall_impl; try eapply WRITENOTIN0. s. i.
        eapply NNPP. eauto.
      }
    }
    { splits; auto. econs; eauto. split; ss.
      inv LOCAL0. inv RACE.
      exists to. splits; ss.
      { left. econs; eauto. }
      { refl. }
    }
    { splits; auto. econs; eauto. splits; ss.
      inv LOCAL0. inv RACE.
      exists to. splits; ss.
      { left. econs; eauto. }
      { refl. }
    }
    { splits; auto. econs; eauto. splits; ss.
      inv LOCAL0.
      { exists Time.bot. splits; try refl.
        left. econs; try apply CLOSED. ss.
      }
      { exists Time.bot. splits; try refl.
        left. econs; try apply CLOSED. ss.
      }
      { inv RACE.
        exists to. splits; try refl.
        left. econs; eauto.
      }
    }
  }
Qed.

Lemma tevent_map_weak_mon (f0 f1: Loc.t -> Time.t -> Time.t -> Prop)
      (LE: f0 <3= f1)
  :
    tevent_map_weak f0 <2= tevent_map_weak f1.
Proof.
  i. inv PR; econs; eauto.
  induction MSGS; eauto. des.
  econs; eauto.
Qed.

Lemma traced_steps_eventable_time_normal lang (th0 th1: Thread.t lang) tr
      (spaces: Loc.t -> Time.t -> Prop)
      (STEPS: Trace.steps tr th0 th1)
      (WRITENOTIN: List.Forall (fun em => (write_not_in (fun loc ts => ~ (spaces loc ts \/ covered loc ts (Thread.memory th0))) /1\ (fun e => ~ ThreadEvent.is_cancel e)) (snd em)) tr)
      (MEM: Memory.closed (Thread.memory th0))
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    (<<INCR: eventable (Thread.memory th1) (Local.promises (Thread.local th1)) spaces <2= eventable (Thread.memory th0) (Local.promises (Thread.local th0)) spaces>>) /\
    (<<TIMES: List.Forall2
                (fun em fem =>
                   tevent_map_weak (fun loc ts fts => ts = fts /\ eventable_below (Thread.memory th0) (Local.promises (Thread.local th0)) spaces loc ts)
                                   (snd fem) (snd em)) tr tr>>).
Proof.
  ginduction STEPS.
  { i. splits; ss. }
  { i. subst. inv WRITENOTIN.
    exploit Thread.step_future; eauto. i. des.
    exploit IHSTEPS; eauto.
    { eapply List.Forall_impl; eauto.
      i. ss. des. splits; auto. eapply write_not_in_mon; eauto. i. ss.
      ii. eapply PR. des; eauto. right.
      eapply step_not_cancel_covered_increase; eauto. }
    i. des.
    hexploit step_eventable_time; eauto.
    i. des. esplits; eauto. econs; ss; eauto.
    eapply list_Forall2_impl; eauto.
    i. ss. eapply tevent_map_weak_mon; eauto.
    i. ss. des. subst. splits; auto.
    eapply eventable_le_below; eauto.
  }
Qed.

Lemma traced_steps_eventable_time_cancel lang (th0 th1: Thread.t lang) tr
      (spaces: Loc.t -> Time.t -> Prop)
      (STEPS: Trace.steps tr th0 th1)
      (WRITENOTIN: List.Forall (fun em => ThreadEvent.is_cancel (snd em)) tr)
      (MEM: Memory.closed (Thread.memory th0))
      (LOCAL: Local.wf (Thread.local th0) (Thread.memory th0))
      (SC: Memory.closed_timemap (Thread.sc th0) (Thread.memory th0))
  :
    (<<INCR: eventable (Thread.memory th1) (Local.promises (Thread.local th1)) spaces <2= eventable (Thread.memory th0) (Local.promises (Thread.local th0)) spaces>>) /\
    (<<TIMES: List.Forall2
                (fun em fem =>
                   tevent_map_weak (fun loc ts fts => ts = fts /\ eventable_below (Thread.memory th0) (Local.promises (Thread.local th0)) spaces loc ts)
                                   (snd fem) (snd em)) tr tr>>).
Proof.
  ginduction STEPS.
  { i. splits; ss. }
  { i. subst. inv WRITENOTIN.
    exploit Thread.step_future; eauto. i. des.
    hexploit step_eventable_time; eauto.
    { instantiate (1:=spaces). destruct e; ss. des_ifs. }
    exploit IHSTEPS; eauto. i. des.
    splits; eauto. econs; eauto.
    eapply list_Forall2_impl; eauto.
    i. ss. eapply tevent_map_weak_mon; eauto.
    i. ss. des. subst. splits; auto.
    eapply eventable_le_below; eauto.
  }
Qed.

Lemma reservations_added_covered mem0 mem1 l
      (ADDED: reservations_added l mem0 mem1)
      loc ts
  :
    covered loc ts mem1 <-> (covered loc ts mem0 \/ intervals_sum l loc ts).
Proof.
  ginduction l; ss.
  { i. inv ADDED. split; i; des; ss; auto. }
  { i. inv ADDED. rewrite IHl; eauto.
    rewrite (@add_covered mem3 mem0); eauto. split; i; des; auto. }
Qed.

Lemma reservations_added_covered_rev mem0 mem1 l
      (ADDED: reservations_added l mem0 mem1)
      loc ts
  :
    covered loc ts mem0 <-> (covered loc ts mem1 /\ ~ intervals_sum l loc ts).
Proof.
  split; i.
  { split.
    { eapply reservations_added_covered; eauto. }
    { eapply reservations_added_non_covered; eauto. }
  }
  { des. eapply reservations_added_covered in H; eauto. des; ss. }
Qed.

Lemma can_reserve_all_needed times
      (DIVERGE: forall loc ts,
          exists ts',
            (<<TIMES: times loc ts'>>) /\
            (<<TS: Time.lt ts ts'>>))
      lang
      st0 st1 lc0 lc1 sc0 sc1 mem0 mem1 tr
      (MWF: memory_times_wf times mem0)
      (STEPS: Trace.steps tr (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk lang st1 lc1 sc1 mem1))
      (EVENTS: List.Forall (fun em => <<SAT: ((fun e => ~ ThreadEvent.is_cancel e) /1\ wf_time_evt times) (snd em)>>) tr)
      (MEM: Memory.closed mem0)
      (LOCAL: Local.wf lc0 mem0)
      (SC: Memory.closed_timemap sc0 mem0)
  :
    exists lc0' mem0' tr_reserve tr_cancel reserves,
      (<<RESERVESTEPS:
         Trace.steps tr_reserve (Thread.mk lang st0 lc0 sc0 mem0) (Thread.mk lang st0 lc0' sc0 mem0')>>) /\
      (<<RESERVETRACE:
         List.Forall (fun em => <<SAT: (ThreadEvent.is_reserve /1\ wf_time_evt times) (snd em)>>) tr_reserve>>) /\
      (<<CANCELTRACE: List.Forall (fun em => <<SAT: (ThreadEvent.is_cancel /1\ wf_time_evt times) (snd em)>>) tr_cancel>>) /\
      (<<RESERVEMEM: reservations_added reserves mem0 mem0'>>) /\
      (<<CAP:
         forall cap0'
                (MLE: Memory.le mem0' cap0'),
         exists cap0 cap1 ,
           (<<CANCELSTEPS:
              Trace.steps tr_cancel (Thread.mk lang st0 lc0' sc0 cap0') (Thread.mk lang st0 lc0 sc0 cap0)>>) /\
           (<<STEPS:
              Trace.steps tr (Thread.mk lang st0 lc0 sc0 cap0) (Thread.mk lang st1 lc1 sc1 cap1)>>) /\
           (<<RESERVEMEM: reservations_added reserves cap0 cap0'>>)>>) /\
      (<<TIMES: forall max
                       (MAX: concrete_promise_max_timemap mem0' (Local.promises lc0') max),
          List.Forall2
            (fun em fem =>
               tevent_map_weak (fun loc ts fts => ts = fts /\ Time.le ts (max loc))
                               (snd fem) (snd em)) (tr_cancel ++ tr) (tr_cancel ++ tr)>>)
.
Proof.
  exploit (@traced_steps_finte_write_to tr); eauto.
  { eapply List.Forall_impl; eauto. i. ss. des. eauto. }
  intros [tos ?]. des.
  exploit traced_steps_needed_spaces; eauto.
  i. des.
  exploit reserve_empty_intervals; eauto.
  { eapply LOCAL. }
  i. des. ss.
  assert (MLE: Memory.le prom' mem').
  { eapply trace_steps_promises_le in STEPS0; eauto. eapply LOCAL. }
  exploit reserve_write_tos.
  { eauto. }
  { eapply memory_times_wf_traced in STEPS0; eauto.
    eapply List.Forall_impl; eauto. i. ss. des. eauto.
  }
  { ss. }
  { eauto. }
  i. des. ss.
  assert (ADDEDPROMALL: reservations_added (l ++ l0) (Local.promises lc0) prom'0).
  { eapply reservations_added_trans; eauto. }
  assert (ADDEDMEMALL: reservations_added (l ++ l0) mem0 mem'0).
  { eapply reservations_added_trans; eauto. }
  hexploit cancel_reservations_added.
  { instantiate (1:=Local.mk (Local.tview lc0) prom'0). eapply ADDEDPROMALL. }
  { eapply Forall_app; eauto. }
  i. des.
  assert (CAP: forall cap0'
                      (MLE: Memory.le mem'0 cap0'),
             exists cap0 cap1,
               Trace.steps
                 tr2
                 (Thread.mk _ st0 {| Local.tview := Local.tview lc0; Local.promises := prom'0 |} sc0 cap0')
                 (Thread.mk _ st0 lc0 sc0 cap0) /\
               Trace.steps
                 tr
                 (Thread.mk _ st0 lc0 sc0 cap0)
                 (Thread.mk _ st1 lc1 sc1 cap1) /\
               (<<ADDED: reservations_added (l ++ l0) cap0 cap0'>>))
  .
  { i. ss. exploit (H0 st0 sc0 cap0').
    { etrans; eauto. eapply trace_steps_promises_le in STEPS1; eauto. }
    i. des.
    assert (MLE1: Memory.le mem0 mem'1).
    { eapply reservations_added_le_le.
      { eapply ADDEDMEMALL. }
      { eapply MLE0. }
      { eauto. }
    }
    hexploit traced_step_lifting.
    { eapply STEPS. }
    { eapply list_Forall_sum.
      { eapply list_Forall_sum.
        { eapply EVENTS. }
        { eapply EVENTS0. }
        { instantiate (1:=fun em => <<SAT: ((fun e => ~ ThreadEvent.is_cancel e) /1\ write_not_to (fun loc ts => ~ List.In (loc, ts) tos)) (snd em)>>).
          i. ss. des. splits; auto. }
      }
      { eapply WRITENOTIN. }
      i. ss. des. splits; eauto.
    }
    { eapply MLE1. }
    { i. destruct (classic (covered loc ts mem0)); auto. right.
      ii. des; ss. eapply reservations_added_non_covered in ADDEDMEM1; eauto.
      eapply ADDEDMEM1. erewrite intervals_sum_interval.
      erewrite intervals_sum_interval in H1. des. esplits; eauto.
      eapply List.in_or_app; eauto. }
    { i. destruct (classic (unattachable mem0 loc ts)); auto. right.
      ii. des; ss. eapply reservations_added_non_unattachable in ADDEDMEM1; eauto.
      eapply ADDEDMEM1. erewrite intervals_sum_left_interval.
      eapply WRITETO in H1. eapply reservations_added_unattachable in H1; eauto.
      des; ss. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. des. exists mem'1, cap1.
    splits; eauto. destruct lc0. ss.
  }
  esplits.
  { eapply Trace.steps_trans.
    { eapply STEPS0. }
    { eapply STEPS1. }
  }
  { eapply Forall_app; eauto. }
  { eapply CANCELTRACE. }
  { eauto. }
  { i. exploit CAP; eauto. }
  { i. exploit (CAP mem'0).
    { refl. }
    i. des. ss.
    exploit Trace.steps_future; try apply STEPS0; eauto. i. des. ss.
    exploit Trace.steps_future; try apply STEPS1; eauto. i. des. ss.
    exploit Trace.steps_future; try apply x0; eauto. i. des. ss.
    exploit traced_steps_eventable_time_cancel; try apply x0; eauto; ss.
    { eapply List.Forall_impl; eauto. i. ss. des. splits; auto. }
    instantiate (1:=intervals_sum l). i. ss. des.
    assert (EVENTTIMES: forall loc ts
                               (EVENTABLE: eventable_below mem'0 prom'0 (intervals_sum l) loc ts),
               Time.le ts (max loc)).
    { i. unfold eventable_below in EVENTABLE. des. etrans; eauto.
      unfold eventable in TIME. des.
      { inv TIME. eapply MAX in GET; auto. }
      { inv TIME. eapply MAX in GET; auto. inv ITV. ss. etrans; eauto. }
      { eapply reservations_added_covered in ADDEDPROM; eauto. des.
        exploit ADDEDPROM1.
        { right. eauto. }
        i. eapply reservations_added_covered in ADDEDPROM0; eauto. des.
        exploit ADDEDPROM2.
        { left. eauto. }
        i. inv x2. eapply MAX in GET. inv ITV. ss. etrans; eauto.
      }
    }
    eapply List.Forall2_app.
    { eapply list_Forall2_impl; eauto. i. ss.
      eapply tevent_map_weak_mon; eauto. i. ss. des. subst. splits; auto. }
    { exploit traced_steps_eventable_time_normal; try apply x1; eauto; ss.
      { instantiate (1:=intervals_sum l).
        eapply list_Forall_sum.
        { eapply EVENTS. }
        { eapply WRITENOTIN. }
        i. ss. des. splits; auto.
        eapply write_not_in_mon; eauto. i. ss. ii. eapply PR.
        apply or_comm in H. apply or_strengthen in H. des; auto. right.
        erewrite reservations_added_covered_rev; try apply ADDED; eauto.
        erewrite reservations_added_covered_rev in SAT; try apply ADDEDMEMALL; eauto.
      }
      { i. des. eapply list_Forall2_impl; eauto. i. ss.
        eapply tevent_map_weak_mon; eauto. i. ss. des. subst. splits; auto.
        eapply eventable_le_below in PR0; eauto. }
    }
  }
Qed.
