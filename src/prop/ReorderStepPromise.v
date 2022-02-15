From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
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
Require Import Progress.

Require Import MemoryReorder.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import PromiseConsistent.

Require Import ReorderTView.

Set Implicit Arguments.


Lemma reorder_read_promise_diff
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 msg2 kind2
      lc0 mem0
      lc1
      lc2 mem2
      (DIFF: (loc1, ts1) <> (loc2, to2))
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 msg2 lc2 mem2 kind2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem2 kind2>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryFacts.promise_get1_diff; eauto. i. des.
  esplits; eauto.
Qed.

Lemma lower_closed_timemap_inv
      tm
      mem1 loc from to msg1 msg2 mem2
      (CLOSED: Memory.closed_timemap tm mem2)
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  Memory.closed_timemap tm mem1.
Proof.
  ii. specialize (CLOSED loc0). des.
  revert CLOSED. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
  des. subst. i. inv CLOSED.
  exploit Memory.lower_get0; eauto. i. des. inv MSG_LE. eauto.
Qed.

Lemma lower_closed_view_inv
      view
      mem1 loc from to msg1 msg2 mem2
      (CLOSED: Memory.closed_view view mem2)
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  Memory.closed_view view mem1.
Proof.
  inv CLOSED. econs; eauto using lower_closed_timemap_inv.
Qed.

Lemma lower_closed_message_inv
      msg
      mem1 loc from to msg1 msg2 mem2
      (CLOSED: Memory.closed_message msg mem2)
      (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2):
  Memory.closed_message msg mem1.
Proof.
  inv CLOSED; eauto.
  econs. inv CLOSED0; eauto.
  econs. eauto using lower_closed_view_inv.
Qed.

Lemma write_na_lower_closed_message_inv
      msg
      ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind
      (CLOSED: Memory.closed_message msg mem2)
      (KINDS: List.Forall Memory.op_kind_is_lower kinds)
      (KIND: Memory.op_kind_is_lower kind)
      (WRITE: Memory.write_na ts promises1 mem1 loc from to val promises2 mem2 msgs kinds kind):
  Memory.closed_message msg mem1.
Proof.
  induction WRITE.
  - inv WRITE. inv PROMISE; ss.
    eauto using lower_closed_message_inv.
  - inv KINDS. exploit IHWRITE; eauto. i.
    inv WRITE_EX. inv PROMISE; ss.
    eauto using lower_closed_message_inv.
Qed.

Lemma reorder_memory_write_lower_promise
      promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 kind1
      loc2 from2 to2 msg2 promises2 mem2 kind2
      (LE: Memory.le promises0 mem0)
      (KIND1: Memory.op_kind_is_lower kind1)
      (WRITE: Memory.write promises0 mem0 loc1 from1 to1 msg1 promises1 mem1 kind1)
      (PROMISE: Memory.promise promises1 mem1 loc2 from2 to2 msg2 promises2 mem2 kind2):
  exists promises1' mem1',
    (<<PROMISE: Memory.promise promises0 mem0 loc2 from2 to2 msg2 promises1' mem1' kind2>>) /\
    (<<WRITE: Memory.write promises1' mem1' loc1 from1 to1 msg1 promises2 mem2 kind1>>).
Proof.
  inv WRITE.
  destruct (classic ((loc1, to1) = (loc2, to2))).
  { inv H.
    exploit Memory.promise_get0; try exact PROMISE0.
    { destruct kind1; ss. }
    i. des.
    exploit Memory.remove_get0; eauto. i. des. clear GET.
    inv PROMISE.
    - exploit Memory.add_get0; try exact MEM. i. des. congr.
    - exploit Memory.split_get0; try exact MEM. i. des. congr.
    - exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
    - exploit Memory.remove_get0; try exact PROMISES. i. des. congr.
  }

  hexploit Memory.promise_le; try apply LE; eauto. i. des.
  exploit MemoryReorder.remove_promise; try exact REMOVE; eauto. i. des.
  inv PROMISE0; ss. inv x0; ss.
  { exploit MemoryReorder.lower_add; try exact PROMISES; eauto. i. des.
    exploit MemoryReorder.lower_add; try exact MEM; eauto. i. des.
    esplits; eauto. econs; eauto.
    i. exploit Memory.lower_get1; try exact GET; eauto. i. des. eauto.
  }
  { exploit MemoryReorder.lower_split; try exact PROMISES; eauto. i. des.
    exploit MemoryReorder.lower_split; try exact MEM; eauto. i. des.
    unguard; des; try congr.
    { inv FROM1. inv FROM0. inv PROMISE; ss.
      exploit Memory.remove_get0; eauto. i. des.
      exploit Memory.split_get0; try exact PROMISES1; eauto. i. des.
      congr.
    }
    inv FROM3. inv FROM2.
    esplits; eauto.
  }
  { exploit MemoryReorder.lower_lower; try exact PROMISES; eauto. i.
    exploit MemoryReorder.lower_lower; try exact MEM; eauto. i.
    des; subst; try congr.
    esplits; eauto.
  }
  { exploit MemoryReorder.lower_remove; try exact PROMISES; eauto. i. des.
    exploit MemoryReorder.lower_remove; try exact MEM; eauto. i. des.
    esplits; eauto.
  }
Qed.  

Lemma reorder_write_lower_promise
      loc1 from1 to1 val1 releasedm1 released1 ord1 kind1
      loc2 from2 to2 msg2 kind2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (KIND1: Memory.op_kind_is_lower kind1)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2):
  exists lc1' mem1',
    (<<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2>>) /\
    (<<STEP2: Local.write_step lc1' sc0 mem1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 sc1 mem2 kind1>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit reorder_memory_write_lower_promise; try apply WF0; eauto. i. des.
  esplits.
  - econs; eauto.
    inv WRITE0. inv PROMISE1; ss.
    eapply lower_closed_message_inv; eauto.
  - econs; eauto. destruct ord1; ss.
Qed.

Lemma reorder_memory_write_na_lower_promise
      ts promises0 mem0 loc1 from1 to1 val1 promises1 mem1 msgs1 kinds1 kind1
      loc2 from2 to2 msg2 promises2 mem2 kind2
      (LE: Memory.le promises0 mem0)
      (KINDS1: List.Forall Memory.op_kind_is_lower kinds1)
      (KIND1: Memory.op_kind_is_lower kind1)
      (WRITE: Memory.write_na ts promises0 mem0 loc1 from1 to1 val1 promises1 mem1 msgs1 kinds1 kind1)
      (PROMISE: Memory.promise promises1 mem1 loc2 from2 to2 msg2 promises2 mem2 kind2):
  exists promises1' mem1',
    (<<PROMISE: Memory.promise promises0 mem0 loc2 from2 to2 msg2 promises1' mem1' kind2>>) /\
    (<<WRITE: Memory.write_na ts promises1' mem1' loc1 from1 to1 val1 promises2 mem2 msgs1 kinds1 kind1>>).
Proof.
  induction WRITE.
  { exploit reorder_memory_write_lower_promise; eauto. i. des.
    esplits; eauto.
  }
  inv KINDS1.
  hexploit Memory.write_le; eauto. i. des.
  exploit IHWRITE; eauto. i. des.
  exploit reorder_memory_write_lower_promise; try exact WRITE_EX; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_write_na_lower_promise
      loc1 from1 to1 val1 ord1 msgs1 kinds1 kind1
      loc2 from2 to2 msg2 kind2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (KINDS1: List.Forall Memory.op_kind_is_lower kinds1)
      (KIND1: Memory.op_kind_is_lower kind1)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (STEP1: Local.write_na_step lc0 sc0 mem0 loc1 from1 to1 val1 ord1
                                  lc1 sc1 mem1 msgs1 kinds1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2):
  exists lc1' mem1',
    (<<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2>>) /\
    (<<STEP2: Local.write_na_step lc1' sc0 mem1' loc1 from1 to1 val1 ord1
                                  lc2 sc1 mem2 msgs1 kinds1 kind1>>).
Proof.
  inv STEP1. inv STEP2. ss.
  exploit reorder_memory_write_na_lower_promise; try apply WF0; eauto. i. des.
  esplits.
  - econs; eauto.
    eapply write_na_lower_closed_message_inv; eauto.
  - econs; eauto.
Qed.

Lemma reorder_update_lower_promise_diff
      lc0 sc0 mem0
      loc1 ts1 val1 released1 ord1 lc1
      from2 to2 val2 released2 ord2 lc2 sc2 mem2 kind2
      loc3 from3 to3 msg3 lc3 mem3 kind3
      (DIFF: (loc1, ts1) <> (loc3, to3))
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND2: Memory.op_kind_is_lower kind2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2 mem2 kind2)
      (STEP3: Local.promise_step lc2 mem2 loc3 from3 to3 msg3 lc3 mem3 kind3):
  exists lc1' mem1' lc2',
    (<<STEP1: Local.promise_step lc0 mem0 loc3 from3 to3 msg3 lc1' mem1' kind3>>) /\
    (<<STEP2: Local.read_step lc1' mem1' loc1 ts1 val1 released1 ord1 lc2'>>) /\
    (<<STEP3: Local.write_step lc2' sc0 mem1' loc1 from2 to2 val2 released1 released2 ord2 lc3 sc2 mem3 kind2>>).
Proof.
  exploit Local.read_step_future; eauto. i. des.
  exploit reorder_write_lower_promise; try exact STEP2; eauto. i. des.
  exploit reorder_read_promise_diff; try exact STEP1; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_fence_promise
      ordr1 ordw1
      loc2 from2 to2 msg2
      lc0 sc0 mem0
      lc1 sc1
      lc2 mem2
      kind
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (STEP1: Local.fence_step lc0 sc0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 msg2 lc2 mem2 kind):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem2 kind>> /\
    <<STEP2: Local.fence_step lc1' sc0 ordr1 ordw1 lc2 sc1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto.
    + s. i. destruct ordw1; inv ORDW1; inv H.
    + s. i. destruct ordw1; inv ORDW1; inv H.
Qed.

Lemma reorder_is_racy_promise
      loc1 to1 ord1
      loc2 from2 to2 msg2 kind2
      lc0 mem0
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.is_racy lc0 mem0 loc1 to1 ord1)
      (STEP2: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc2 mem2 kind2):
  <<STEP: Local.is_racy lc2 mem2 loc1 to1 ord1>>.
Proof.
  inv STEP1. inv STEP2.
  exploit Memory.promise_future; try exact PROMISE; try apply WF0; eauto. i. des.
  exploit Memory.future_get1; eauto. i. des.
  econs; eauto; ss.
  - destruct (Memory.get loc1 to1 promises2) as [[]|] eqn:X; ss.
    revert X. inv PROMISE; ss.
    + erewrite Memory.add_o; eauto. condtac; ss; try congr.
      i. des. inv X.
      exploit Memory.add_get0; try exact MEM. i. des. congr.
    + erewrite Memory.split_o; eauto. repeat (condtac; ss); try congr.
      * i. des. inv X.
        exploit Memory.split_get0; try exact MEM. i. des. congr.
      * guardH o. i. des. inv X.
        exploit Memory.split_get0; try exact PROMISES. i. des. congr.
    + erewrite Memory.lower_o; eauto. condtac; ss; try congr.
      i. des. inv X.
      exploit Memory.lower_get0; try exact PROMISES. i. des. congr.
    + erewrite Memory.remove_o; eauto. condtac; ss; try congr.
  - inv MSG_LE; ss.
  - i. exploit MSG2; eauto. i. subst. inv MSG_LE. ss.
Qed.

Lemma reorder_racy_read_promise
      loc1 to1 val1 ord1
      loc2 from2 to2 msg2 kind2
      lc0 mem0
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.racy_read_step lc0 mem0 loc1 to1 val1 ord1)
      (STEP2: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc2 mem2 kind2):
  <<STEP: Local.racy_read_step lc2 mem2 loc1 to1 val1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_promise; eauto.
Qed.

Lemma reorder_racy_write_promise
      loc1 to1 ord1
      loc2 from2 to2 msg2 kind2
      lc0 mem0
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.racy_write_step lc0 mem0 loc1 to1 ord1)
      (STEP2: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (CONS: Local.promise_consistent lc2):
  <<STEP: Local.racy_write_step lc2 mem2 loc1 to1 ord1>>.
Proof.
  inv STEP1.
  exploit reorder_is_racy_promise; eauto.
Qed.

Lemma reorder_racy_update_promise
      loc1 to1 ord1
      loc2 from2 to2 msg2 kind2
      lc0 mem0
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.racy_write_step lc0 mem0 loc1 to1 ord1)
      (STEP2: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (CONS: Local.promise_consistent lc2):
  <<STEP: Local.racy_write_step lc2 mem2 loc1 to1 ord1>>.
Proof.
  inv STEP1; eauto.
  exploit reorder_is_racy_promise; eauto.
Qed.
