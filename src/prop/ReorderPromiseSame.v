Require Import Omega.
Require Import RelationClasses.
Require Import Bool.

Require Import sflib.
From Paco Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Require Import PromiseConsistent.

Set Implicit Arguments.


Lemma reorder_promise_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 msg1 kind1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: (loc1, to1) <> (loc2, to2)):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.promise_get_inv_diff; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_promise_promise_lower_None
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 (Message.mk val2 None) lc2 mem2 kind2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (KIND2: Memory.op_kind_is_lower kind2 = true):
  (loc1 = loc2 /\ from1 = from2 /\ to1 = to2 /\ Message.le (Message.mk val2 None) msg1 /\ kind2 = Memory.op_kind_lower msg1 /\
   exists kind1', <<STEP: Local.promise_step lc0 mem0 loc1 from1 to1 (Message.mk val2 None) lc2 mem2 kind1'>>) \/
  (exists lc1' mem1' from2' kind1',
      <<STEP1: Local.promise_step lc0 mem0 loc2 from2' to2 (Message.mk val2 None) lc1' mem1' kind2>> /\
      <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 msg1 lc2 mem2 kind1'>>).
Proof.
  inv STEP1. inv STEP2. ss. inv PROMISE0; inv KIND2. inv PROMISE.
  - exploit MemoryReorder.add_lower; try exact PROMISES0; try exact PROMISES; eauto. i. des.
    + subst.
      exploit MemoryReorder.add_lower; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
      left. esplits; ss.
      * inv MEM. inv LOWER. ss.
      * econs; eauto.
    + exploit MemoryReorder.add_lower; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
      right. esplits; eauto. econs; eauto.
      eapply Memory.lower_closed_message_view; eauto.
  - destruct (classic ((loc1, ts3) = (loc2, to2))).
    { inv H.
      exploit MemoryReorder.split_lower_same; try exact PROMISES0; try exact PROMISES; eauto. i. des.
      exploit MemoryReorder.split_lower_same; try exact MEM1; try exact MEM; eauto. i. des.
      subst. right. esplits; eauto. econs; eauto.
      eapply Memory.lower_closed_message_view; eauto.
    }
    { exploit MemoryReorder.split_lower_diff; try exact PROMISES0; try exact PROMISES; eauto. i. des.
      - subst. exploit MemoryReorder.split_lower_diff; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
        left. esplits; eauto. inv MEM. inv LOWER. ss.
      - exploit MemoryReorder.split_lower_diff; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
        right. esplits; eauto. econs; eauto.
        eapply Memory.lower_closed_message_view; eauto.
    }
  - exploit MemoryReorder.lower_lower; try exact PROMISES0; try exact PROMISES; eauto. i. des.
    + subst.
      exploit MemoryReorder.lower_lower; try exact MEM1; try exact MEM; eauto. i. des; [|congr].
      left. esplits; eauto. inv MEM. inv LOWER. ss.
    + exploit MemoryReorder.lower_lower; try exact MEM1; try exact MEM; eauto. i. des; [congr|].
      right. esplits; eauto. econs; eauto.
      eapply Memory.lower_closed_message_view; cycle 1; eauto.
Qed.

Lemma reorder_promise_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 msg2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 msg2 lc2 mem2 kind2)
      (MSG_CLOSED: forall promises1' mem1' kind1' (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 msg2 promises1' mem1' kind1'),
          Memory.closed_message_view msg2 mem1')
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: forall to1' msg1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2 /\ forall msg2', kind2 <> Memory.op_kind_split to1' msg2'):
  exists lc1' mem1' kind2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 msg2 lc1' mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                (exists from1' kind1',
                    (loc1, to1) <> (loc2, to2) /\
                    (forall to1' msg1'
                       (LOC: loc1 = loc2)
                       (KIND: kind1' = Memory.op_kind_split to1' msg1'),
                        to1' <> to2 /\ forall msg2', kind2 <> Memory.op_kind_split to1' msg2') /\
                    Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'))>> /\
    <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE.
  { inv PROMISE0.
    - exploit MemoryReorder.add_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.add_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs; eauto.
      + right. esplits; eauto. econs; eauto.
        eapply Memory.add_closed_message_view; cycle 1; eauto.
      + auto.
    - exploit MemoryReorder.add_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto.
        * right. esplits; eauto.
          { ii. inv H. inv ADD3. inv ADD. eapply Time.lt_strorder. eauto. }
          { econs; eauto. eapply Memory.split_closed_message_view; eauto. }
        * auto.
      + exploit MemoryReorder.add_split; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
            revert GET. erewrite Memory.add_o; eauto. condtac; ss. des; congr.
          }
          { econs; eauto. eapply Memory.split_closed_message_view; eauto. }
        * auto.
    - exploit MemoryReorder.add_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto.
        * left. auto.
        * auto.
      + exploit MemoryReorder.add_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto. econs; eauto.
          eapply Memory.lower_closed_message_view; eauto.
        * auto.
  }
  { inv PROMISE0.
    - exploit MemoryReorder.split_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.split_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs; eauto.
      + right. esplits; eauto. econs; eauto.
        eapply Memory.add_closed_message_view; eauto.
      + auto.
    - exploit MemoryReorder.split_split; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. eapply LOCTS; eauto. }
      i. des.
      + subst. exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. inv SPLIT2. inv SPLIT. eapply Time.lt_strorder. eauto. }
        i. des; [|congr].
        esplits.
        * econs; eauto.
        * right. esplits; eauto.
          { ii. inv H. inv SPLIT2. inv SPLIT. eapply Time.lt_strorder. eauto. }
          { econs; eauto. eapply Memory.split_closed_message_view; cycle 1; eauto. }
        * congr.
      + exploit MemoryReorder.split_split; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. eapply LOCTS; eauto. }
        i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.split_get0; try exact MEM1; eauto. i. des.
            revert GET. erewrite Memory.split_o; eauto. repeat condtac; ss.
            guardH o0. des; congr.
          }
          { econs; eauto. eapply Memory.split_closed_message_view; cycle 1; eauto. }
        * auto.
    - exploit MemoryReorder.split_lower_diff; try exact PROMISES; try exact PROMISES0; eauto.
      { ii. inv H. exploit LOCTS; eauto. i. des. congr. }
      i. des.
      + subst. exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS; eauto. i. des. congr. }
        i. des; [|congr].
        esplits.
        * econs; eauto.
        * left. auto.
        * congr.
      + subst. exploit MemoryReorder.split_lower_diff; try exact MEM; try exact MEM0; eauto.
        { ii. inv H. exploit LOCTS; eauto. i. des. congr. }
        i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto. econs; eauto.
          eapply Memory.lower_closed_message_view; eauto.
        * congr.
  }
  { inv PROMISE0.
    - exploit MemoryReorder.lower_add; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_add; try exact MEM; try exact MEM0; eauto. i. des.
      esplits.
      + econs; eauto.
      + right. esplits; eauto. econs; eauto.
        eapply Memory.add_closed_message_view; eauto.
      + auto.
    - exploit MemoryReorder.lower_split; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      exploit MemoryReorder.lower_split; try exact MEM; try exact MEM0; eauto. i. des.
      unguardH FROM1. des.
      + inv FROM1. unguardH FROM0. des; [|congr]. inv FROM0.
        esplits.
        * econs; eauto.
        * right. esplits; eauto.
          { ii. inv H. inv SPLIT1. inv SPLIT.
            exfalso. eapply Time.lt_strorder. eauto.
          }
          { econs; eauto. eapply Memory.split_closed_message_view; eauto. }
        * congr.
      + inv FROM2. unguardH FROM0. des; [congr|]. inv FROM2.
        esplits.
        * econs; eauto.
        * right. esplits; eauto.
          { ii. inv H. exploit Memory.lower_get0; try exact MEM; eauto.
            exploit Memory.split_get0; try exact SPLIT0; eauto. i. des. congr.
          }
          { econs; eauto. eapply Memory.split_closed_message_view; eauto. }
        * auto.
    - exploit MemoryReorder.lower_lower; try exact PROMISES; try exact PROMISES0; eauto. i. des.
      + subst.
        exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [|congr].
        esplits.
        * econs; eauto.
        * left. auto.
        * congr.
      + exploit MemoryReorder.lower_lower; try exact MEM; try exact MEM0; eauto. i. des; [congr|].
        esplits.
        * econs; eauto.
        * right. esplits; eauto. econs; eauto.
          eapply Memory.lower_closed_message_view; cycle 1; eauto.
        * auto.
  }
Qed.

Lemma reorder_promise_fulfill
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS1: (loc1, to1) <> (loc2, to2))
      (LOCTS2: forall to1' msg1'
                 (LOC: loc1 = loc2)
                 (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 msg1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  inv PROMISE.
  - exploit MemoryReorder.add_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
  - exploit MemoryReorder.split_remove; try exact PROMISES; try exact REMOVE; eauto.
    { ii. inv H. eapply LOCTS2; eauto. }
    i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
  - exploit MemoryReorder.lower_remove; try exact REMOVE; eauto. i. des.
    esplits.
    + econs; eauto.
    + econs; ss. econs; ss.
Qed.

Lemma promise_step_nonsynch_loc_inv
      lc1 mem1 loc from to msg lc2 mem2 kind l
      (WF1: Local.wf lc1 mem1)
      (STEP: Local.promise_step lc1 mem1 loc from to msg lc2 mem2 kind)
      (NONPF: Memory.op_kind_is_lower_full kind = false \/ ~ Message.is_released_none msg)
      (NONSYNCH: Memory.nonsynch_loc l lc2.(Local.promises)):
  Memory.nonsynch_loc l lc1.(Local.promises).
Proof.
  guardH NONPF.
  ii.
  inv STEP. inv PROMISE; ss.
  - exploit Memory.add_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.split_get1; try exact GET; eauto. i. des.
    exploit NONSYNCH; eauto.
  - exploit Memory.lower_o; try exact PROMISES; eauto.
    instantiate (1 := t). instantiate (1 := l). condtac; ss.
    + i. des. subst. exploit NONSYNCH; eauto.
      destruct msg; destruct msg0; ss.
      * i. subst. unguard. des; ss.
        exploit Memory.lower_get0; try exact MEM. i. des.
        inv WF1. exploit PROMISES0; eauto. i.
        rewrite GET0 in x. inv x. ss.
      * exploit Memory.lower_get0; try exact PROMISES. i. des.
        rewrite GET in GET0. inv GET0.
        inv MEM. inv LOWER. inv MSG_LE0.
    + rewrite GET. i. exploit NONSYNCH; eauto.
Qed.

Lemma reorder_promise_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (NONPF: Memory.op_kind_is_lower_full kind1 = false \/ ~ Message.is_released_none msg1)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: forall to1' msg1'
                (LOC: loc1 = loc2)
                (KIND: kind1 = Memory.op_kind_split to1' msg1'),
          to1' <> to2 /\ forall msg2', kind2 <> Memory.op_kind_split to1' msg2'):
  exists kind2' lc1' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                ((loc1, to1) <> (loc2, to2) /\
                 exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>> /\
    <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>.
Proof.
  guardH NONPF.
  exploit Local.promise_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto; try by viewtac. i. des.
  exploit reorder_promise_promise; try exact STEP1; eauto.
  { i. subst.
    exploit Memory.promise_op; eauto. i. econs.
    eapply TViewFacts.op_closed_released; try exact x0; eauto.
    inv STEP1. apply LOCAL0.
  }
  i. des.
  unguardH STEP5. des.
  - inv STEP5.
    exploit promise_fulfill_write_exact; try exact STEP4; eauto.
    { i. hexploit ORD; eauto. i.
      eapply promise_step_nonsynch_loc_inv; try exact STEP1; eauto.
    }
    { inv STEP1. ss. }
    i. esplits; eauto. left; eauto.
  - exploit Local.promise_step_future; try exact STEP4; eauto. i. des.
    exploit reorder_promise_fulfill; try exact STEP6; eauto.
    { i. eapply STEP6; eauto. }
    i. des.
    exploit fulfill_step_future; try exact STEP7; try exact WF0; eauto; try by viewtac. i. des.
    exploit promise_fulfill_write_exact; try exact STEP4; eauto; try by viewtac.
    { i. hexploit ORD; eauto. i.
      eapply promise_step_nonsynch_loc_inv; try exact STEP1; eauto.
    }
    { subst. inv STEP1. ss. }
    i. esplits; eauto. right. esplits; eauto.
Qed.

Lemma reorder_promise_write'
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 msg1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 msg1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (NONPF: Memory.op_kind_is_lower_full kind1 = false \/ ~ Message.is_released_none msg1)
      (REL_WF: View.opt_wf releasedm2)
      (REL_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0):
  (loc1 = loc2 /\ Time.lt to1 to2) \/
  (exists kind2' lc1' mem1',
     <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
     <<STEP2: __guard__
                ((lc2, mem2, loc1, from1, to1) = (lc1', mem1', loc2, from2, to2) \/
                 ((loc1, to1) <> (loc2, to2) /\
                  exists from1' kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1' to1 msg1 lc2 mem2 kind1'>>))>> /\
     <<KIND2: kind2 = Memory.op_kind_add -> kind2' = Memory.op_kind_add>>).
Proof.
  guardH NONPF.
  destruct (classic (loc1 = loc2 /\ Time.lt to1 to2)); auto.
  right. eapply reorder_promise_write; eauto. i. subst. splits.
  - ii. subst. apply H. splits; auto.
    inv STEP1. inv PROMISE. inv MEM. inv SPLIT. auto.
  - ii. subst. apply H. splits; auto.
    inv STEP2. inv WRITE. inv PROMISE. exploit Memory.split_get0; eauto. i. des.
    inv STEP1. inv PROMISE. revert GET0. erewrite Memory.split_o; eauto. repeat condtac; ss.
    + i. des. inv GET0. inv MEM1. inv SPLIT.
      exfalso. eapply Time.lt_strorder. eauto.
    + guardH o. i. des. inv GET0. inv MEM. inv SPLIT. auto.
    + guardH o. des; congr.
Qed.

Hint Constructors Thread.program_step.
Hint Constructors Thread.step.

Lemma reorder_nonpf_program
      lang
      e1 e2 th0 th1 th2
      (STEP1: @Thread.step lang false e1 th0 th1)
      (STEP2: Thread.program_step e2 th1 th2)
      (CONS2: promise_consistent th2.(Thread.local))
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory)):
  exists th1',
     <<STEP1: Thread.program_step e2 th0 th1'>> /\
     <<STEP2: __guard__ (th2 = th1' \/ exists pf2' e2', Thread.promise_step pf2' e2' th1' th2)>>.
Proof.
  exploit Thread.step_future; eauto. i. des.
  inv STEP1. inv STEP. ss. inv STEP2. inv LOCAL1; ss.
  - (* silent *)
    esplits; eauto.
    right. esplits. econs; eauto.
  - (* read *)
    exploit reorder_promise_read; try exact LOCAL0; eauto; try by viewtac.
    { ii. inv H.
      inv LOCAL0. exploit Memory.promise_get2; eauto. i. des.
      exploit promise_consistent_promise_read; eauto. i.
      eapply Time.lt_strorder. eauto.
    }
    i. des. esplits.
    + econs; eauto.
    + right. esplits. econs; eauto.
  - (* write *)
    exploit reorder_promise_write'; try exact LOCAL0; eauto; try by viewtac.
    { apply promise_pf_false_inv. ss. }
    i. des.
    { subst. inv LOCAL0. exploit Memory.promise_get2; eauto. i. des.
      exploit promise_consistent_promise_write; eauto. i.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    }
    esplits.
    + econs; eauto.
    + unguardH STEP2. des.
      * inv STEP2. left. auto.
      * right. esplits. econs; eauto.
  - (* update *)
    exploit reorder_promise_read; try exact LOCAL1; eauto; try by viewtac.
    { ii. inv H.
      inv LOCAL0. exploit Memory.promise_get2; eauto. i. des.
      exploit promise_consistent_promise_read; eauto.
      { eapply write_step_promise_consistent; eauto. }
      i. eapply Time.lt_strorder. eauto.
    }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit reorder_promise_write'; try exact LOCAL2; eauto; try by viewtac.
    { apply promise_pf_false_inv. ss. }
    i. des.
    { subst. inv STEP2. exploit Memory.promise_get2; eauto. i. des.
      exploit promise_consistent_promise_write; eauto. i.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    }
    esplits.
    + econs; eauto.
    + unguardH STEP3. des.
      * inv STEP3. left. auto.
      * right. esplits. econs; eauto.
  - inv LOCAL0. inv LOCAL2.
    esplits; eauto.
    + econs; eauto. econs 5; eauto. econs; eauto. ss.
      intros ORDW l. eapply promise_step_nonsynch_loc_inv; eauto.
      * apply promise_pf_false_inv. ss.
      * apply RELEASE. ss.
    + right. esplits. econs; eauto.
  - inv LOCAL0. inv LOCAL2.
    esplits; eauto.
    + econs; eauto. econs 6; eauto. econs; eauto.
      intros ORDW l. eapply promise_step_nonsynch_loc_inv; eauto.
      * apply promise_pf_false_inv. ss.
      * apply RELEASE. ss.
    + right. esplits. econs; eauto.
Qed.

Lemma reorder_nonpf_pf
      lang
      e1 e2 th0 th1 th2
      (STEP1: @Thread.step lang false e1 th0 th1)
      (STEP2: Thread.step true e2 th1 th2)
      (CONS2: promise_consistent th2.(Thread.local))
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory)):
  (exists pf2' e2',
      <<STEP: Thread.step pf2' e2' th0 th2>> /\
      <<EVENT: __guard__ (e2' = e2 \/ (ThreadEvent.is_promising e2' /\ ThreadEvent.is_promising e2))>>) \/
  (exists e2' pf1' e1' th1',
      <<STEP1: Thread.step true e2' th0 th1'>> /\
      <<STEP2: Thread.promise_step pf1' e1' th1' th2>> /\
      <<EVENT: __guard__ (e2' = e2 \/ (ThreadEvent.is_promising e2' /\ ThreadEvent.is_promising e2))>>).
Proof.
  inv STEP2; ss.
  - inv STEP. ss. symmetry in PF. apply promise_pf_inv in PF. des. subst.
    destruct msg; ss. destruct released0; ss.
    inv STEP1. inv STEP. ss.
    exploit reorder_promise_promise_lower_None; eauto. i. des; subst.
    + left. esplits.
      * econs 1. econs; eauto.
      * right. ss.
    + right. esplits.
      * econs 1. econs; eauto.
      * econs; eauto.
      * right. ss.
  - exploit reorder_nonpf_program; eauto. i. des.
    unguardH STEP2. des.
    + subst. left. esplits; eauto. left. ss.
    + right. esplits; eauto. left. ss.
Qed.
