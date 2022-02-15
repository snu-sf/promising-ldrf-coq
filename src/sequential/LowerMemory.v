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
Require Import MemoryProps.

Set Implicit Arguments.


Variant lower_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
| lower_event_promise
    loc from to msg kind
  :
  lower_event
    (ThreadEvent.promise loc from to msg kind)
    (ThreadEvent.promise loc from to msg kind)
| lower_event_silent
  :
  lower_event
    ThreadEvent.silent
    ThreadEvent.silent
| lower_event_read
    loc ts val released_src released_tgt ord
    (RELEASED: View.opt_le released_src released_tgt)
  :
  lower_event
    (ThreadEvent.read loc ts val released_src ord)
    (ThreadEvent.read loc ts val released_tgt ord)
| lower_event_write
    loc from to val released_src released_tgt ord
    (RELEASED: View.opt_le released_src released_tgt)
  :
  lower_event
    (ThreadEvent.write loc from to val released_src ord)
    (ThreadEvent.write loc from to val released_tgt ord)
| lower_event_write_na
    loc msgs from to val ord
  :
  lower_event
    (ThreadEvent.write_na loc msgs from to val ord)
    (ThreadEvent.write_na loc msgs from to val ord)
| lower_event_update
    loc tsr tsw valr valw releasedr_src releasedr_tgt releasedw_src releasedw_tgt ordr ordw
    (RELEASEDR: View.opt_le releasedr_src releasedr_tgt)
    (RELEASEDW: View.opt_le releasedw_src releasedw_tgt)
  :
  lower_event
    (ThreadEvent.update loc tsr tsw valr valw releasedr_src releasedw_src ordr ordw)
    (ThreadEvent.update loc tsr tsw valr valw releasedr_tgt releasedw_tgt ordr ordw)
| lower_event_fence
    ordr ordw
  :
  lower_event
    (ThreadEvent.fence ordr ordw)
    (ThreadEvent.fence ordr ordw)
| lower_event_syscall
    e
  :
  lower_event
    (ThreadEvent.syscall e)
    (ThreadEvent.syscall e)
| lower_event_failure
  :
  lower_event
    ThreadEvent.failure
    ThreadEvent.failure
| lower_event_racy_read
    loc to val ord
  :
  lower_event
    (ThreadEvent.racy_read loc to val ord)
    (ThreadEvent.racy_read loc to val ord)
| lower_event_racy_write
    loc to val ord
  :
  lower_event
    (ThreadEvent.racy_write loc to val ord)
    (ThreadEvent.racy_write loc to val ord)
| lower_event_racy_update
    loc to valr valw ordr ordw
  :
  lower_event
    (ThreadEvent.racy_update loc to valr valw ordr ordw)
    (ThreadEvent.racy_update loc to valr valw ordr ordw)
.
Hint Constructors lower_event.


Global Program Instance lower_event_PreOrder: PreOrder lower_event.
Next Obligation. ii. destruct x; try (econs; eauto); refl. Qed.
Next Obligation. ii. inv H; inv H0; econs; eauto; etrans; eauto. Qed.

Lemma lower_event_program_event
      e_src e_tgt
      (EVENT: lower_event e_src e_tgt):
  ThreadEvent.get_program_event e_src = ThreadEvent.get_program_event e_tgt.
Proof.
  inv EVENT; ss.
Qed.

Lemma lower_event_machine_event
      e_src e_tgt
      (EVENT: lower_event e_src e_tgt):
  ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt.
Proof.
  inv EVENT; ss.
Qed.

Variant lower_memory_content: forall (cnt_src cnt_tgt: option (Loc.t * Message.t)), Prop :=
| lower_memory_content_none
  :
    lower_memory_content None None
| lower_memory_content_some
    from msg_src msg_tgt
    (MESSAGE: Message.le msg_src msg_tgt)
  :
    lower_memory_content (Some (from, msg_src)) (Some (from, msg_tgt))
.

Program Instance lower_memory_content_PreOrder: PreOrder lower_memory_content.
Next Obligation.
Proof.
  ii. destruct x as [[]|]; econs. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H; inv H0; econs. etrans; eauto.
Qed.


Variant lower_memory (mem_src mem_tgt: Memory.t): Prop :=
| lower_memory_intro
    (LOWER: forall loc to, lower_memory_content (Memory.get loc to mem_src) (Memory.get loc to mem_tgt))
.

Program Instance lower_memory_PreOrder: PreOrder lower_memory.
Next Obligation.
Proof.
  ii. econs. i. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H. inv H0. econs. i. etrans; eauto.
Qed.


Variant lower_local: forall (lc_src lc_tgt: Local.t), Prop :=
| lower_local_intro
    tvw_src tvw_tgt prom
    (TVIEW: TView.le tvw_src tvw_tgt)
  :
    lower_local (Local.mk tvw_src prom) (Local.mk tvw_tgt prom)
.

Program Instance lower_local_PreOrder: PreOrder lower_local.
Next Obligation.
Proof.
  ii. destruct x. econs; eauto. refl.
Qed.
Next Obligation.
Proof.
  ii. inv H; inv H0. econs; eauto. etrans; eauto.
Qed.

Lemma lower_local_consistent lc_src lc_tgt
      (LOCAL: lower_local lc_src lc_tgt)
      (CONSISTENT: Local.promise_consistent lc_tgt)
  :
    Local.promise_consistent lc_src.
Proof.
  inv LOCAL. ii. ss. exploit CONSISTENT; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto.
  ss. eapply TVIEW.
Qed.

Lemma lower_memory_get mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      loc from to msg_tgt
      (GETTGT: Memory.get loc to mem_tgt = Some (from, msg_tgt))
  :
    exists msg_src,
      (<<GETSRC: Memory.get loc to mem_src = Some (from, msg_src)>>) /\
      (<<MESSAGE: Message.le msg_src msg_tgt>>).
Proof.
  inv MEM. specialize (LOWER loc to). rewrite GETTGT in *.
  inv LOWER. eauto.
Qed.

Lemma lower_memory_get_inv mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      loc from to msg_src
      (GETSRC: Memory.get loc to mem_src = Some (from, msg_src))
  :
    exists msg_tgt,
      (<<GETTGT: Memory.get loc to mem_tgt = Some (from, msg_tgt)>>) /\
      (<<MESSAGE: Message.le msg_src msg_tgt>>).
Proof.
  inv MEM. specialize (LOWER loc to). rewrite GETSRC in *.
  inv LOWER. eauto.
Qed.


Lemma lower_memory_closed_timemap mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      tm
      (CLOSED: Memory.closed_timemap tm mem_tgt)
  :
    Memory.closed_timemap tm mem_src.
Proof.
  ii. specialize (CLOSED loc). des.
  hexploit lower_memory_get; eauto. i. des. inv MESSAGE. esplits; eauto.
Qed.

Lemma lower_memory_closed_view mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      vw
      (CLOSED: Memory.closed_view vw mem_tgt)
  :
    Memory.closed_view vw mem_src.
Proof.
  inv CLOSED. econs.
  { eapply lower_memory_closed_timemap; eauto. }
  { eapply lower_memory_closed_timemap; eauto. }
Qed.

Lemma lower_memory_closed_opt_view mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      vw
      (CLOSED: Memory.closed_opt_view vw mem_tgt)
  :
    Memory.closed_opt_view vw mem_src.
Proof.
  inv CLOSED; econs.
  eapply lower_memory_closed_view; eauto.
Qed.

Lemma lower_memory_closed_message mem_src mem_tgt
      (MEM: lower_memory mem_src mem_tgt)
      msg
      (CLOSED: Memory.closed_message msg mem_tgt)
  :
    Memory.closed_message msg mem_src.
Proof.
  inv CLOSED; econs.
  eapply lower_memory_closed_opt_view; eauto.
Qed.

Lemma lower_memory_add mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to msg_src msg_tgt mem_tgt1
      (ADD: Memory.add mem_tgt0 loc from to msg_tgt mem_tgt1)
      (MSG: Message.le msg_src msg_tgt)
      (WF: Message.wf msg_tgt -> Message.wf msg_src)
  :
    exists mem_src1,
      (<<ADD: Memory.add mem_src0 loc from to msg_src mem_src1>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>).
Proof.
  hexploit add_succeed_wf; eauto. i. des.
  hexploit (@Memory.add_exists mem_src0 loc from to msg_src); eauto.
  { i. hexploit lower_memory_get_inv; eauto. i. des. eauto. }
  i. des. esplits; eauto. econs. i.
  erewrite (@Memory.add_o mem2); eauto. erewrite (@Memory.add_o mem_tgt1); eauto. des_ifs.
  { des; clarify. econs; eauto. }
  { eapply MEM. }
Qed.

Lemma lower_memory_split mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc ts0 ts1 ts2 msg_src msg_tgt msg_src3 msg_tgt3 mem_tgt1 mem_src1
      (SPLITTGT: Memory.split mem_tgt0 loc ts0 ts1 ts2 msg_tgt msg_tgt3 mem_tgt1)
      (SPLITSRC: Memory.split mem_src0 loc ts0 ts1 ts2 msg_src msg_src3 mem_src1)
      (MSG: Message.le msg_src msg_tgt)
  :
    lower_memory mem_src1 mem_tgt1.
Proof.
  econs. i.
  erewrite (@Memory.split_o mem_src1); eauto. erewrite (@Memory.split_o mem_tgt1); eauto. des_ifs.
  { des; clarify. econs; eauto. }
  { clear o. econs.
    eapply Memory.split_get0 in SPLITTGT.
    eapply Memory.split_get0 in SPLITSRC. des.
    inv MEM. specialize (LOWER loc ts2).
    rewrite GET4 in LOWER. rewrite GET0 in LOWER. inv LOWER. auto.
  }
  { eapply MEM. }
Qed.

Lemma lower_memory_lower mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to msg_src1 msg_tgt1 msg_src2 msg_tgt2 mem_tgt1 mem_src1
      (SPLITTGT: Memory.lower mem_tgt0 loc from to msg_tgt1 msg_tgt2 mem_tgt1)
      (SPLITSRC: Memory.lower mem_src0 loc from to msg_src1 msg_src2 mem_src1)
      (MSG: Message.le msg_src2 msg_tgt2)
  :
    lower_memory mem_src1 mem_tgt1.
Proof.
  econs. i.
  erewrite (@Memory.lower_o mem_src1); eauto. erewrite (@Memory.lower_o mem_tgt1); eauto. des_ifs.
  { econs.
    eapply Memory.lower_get0 in SPLITTGT.
    eapply Memory.lower_get0 in SPLITSRC. des.
    inv MEM. specialize (LOWER loc to).
    rewrite GET1 in LOWER. rewrite GET in LOWER. inv LOWER. auto.
  }
  { eapply MEM. }
Qed.

Lemma lower_memory_remove mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to msg_src msg_tgt mem_tgt1 mem_src1
      (REMOVETGT: Memory.remove mem_tgt0 loc from to msg_tgt mem_tgt1)
      (REMOVESRC: Memory.remove mem_src0 loc from to msg_src mem_src1)
  :
    lower_memory mem_src1 mem_tgt1.
Proof.
  econs. i.
  erewrite (@Memory.remove_o mem_src1); eauto. erewrite (@Memory.remove_o mem_tgt1); eauto. des_ifs.
  { econs. }
  { eapply MEM. }
Qed.

Lemma lower_memory_promise mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to prom0 msg prom1 mem_tgt1 kind
      (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
      (MLE: Memory.le prom0 mem_src0)
  :
    exists mem_src1,
      (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>).
Proof.
  inv PROMISE.
  { hexploit lower_memory_add; try eassumption.
    { refl. }
    { auto. }
    i. des.
    hexploit (@Memory.add_exists_le prom0 mem_src0); eauto. i. des.
    esplits; eauto. econs; eauto.
    ii. hexploit lower_memory_get_inv; [eapply MEM|..]; eauto.
    i. des. eapply ATTACH; eauto.
  }
  { hexploit (@Memory.split_exists_le prom0 mem_src0); eauto. i. des.
    esplits; eauto. eapply lower_memory_split; eauto. refl. }
  { hexploit (@Memory.lower_exists_le prom0 mem_src0); eauto. i. des.
    esplits; eauto. eapply lower_memory_lower; eauto. refl. }
  { hexploit (@Memory.remove_exists_le prom0 mem_src0); eauto. i. des.
    esplits; eauto. eapply lower_memory_remove; eauto. }
Qed.

Lemma lower_memory_write mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      loc from to prom0 msg_src msg_tgt prom1 mem_tgt1 kind_tgt
      (WRITETGT: Memory.write prom0 mem_tgt0 loc from to msg_tgt prom1 mem_tgt1 kind_tgt)
      (MLE: Memory.le prom0 mem_src0)
      (MSG: Message.le msg_src msg_tgt)
      (WF: Message.wf msg_src)
      (MSGTO: Memory.message_to msg_tgt loc to -> Memory.message_to msg_src loc to)
  :
    exists mem_src1 kind_src,
      (<<WRITESRC: Memory.write prom0 mem_src0 loc from to msg_src prom1 mem_src1 kind_src>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<KIND: kind_src = kind_tgt>>).
Proof.
  inv WRITETGT. inv PROMISE.
  { hexploit lower_memory_add; eauto. i. des.
    hexploit (@Memory.add_exists_le prom0 mem_src0); eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; eauto.
      ii. hexploit lower_memory_get_inv; [eapply MEM|..]; eauto.
      i. des. eapply ATTACH; eauto. ii. subst. inv MSG; ss. }
    { hexploit (@MemoryMerge.add_remove loc from to msg_tgt prom0); eauto.
      i. subst. hexploit Memory.remove_exists.
      { eapply Memory.add_get0. eauto. }
      i. des.
      hexploit (@MemoryMerge.add_remove loc from to msg_src prom1); eauto.
      i. subst. auto.
    }
  }
  { hexploit split_succeed_wf; try apply PROMISES; eauto. i. des.
    hexploit (@Memory.split_exists prom0 loc from to ts3 msg_src msg3); eauto.
    i. des. hexploit (@Memory.split_exists_le prom0 mem_src0); eauto. i. des.
    esplits.
    { econs.
      { econs 2; eauto. inv MSG; ss. }
      { dup H. eapply Memory.split_get0 in H. des.
        hexploit (@Memory.remove_exists mem2).
        { eapply GET1. }
        i. des. replace prom1 with mem1; eauto.
        eapply Memory.ext. i.
        erewrite (@Memory.remove_o mem1); eauto.
        erewrite (@Memory.split_o mem2); eauto.
        erewrite (@Memory.remove_o prom1); eauto.
        erewrite (@Memory.split_o promises2); [|eauto].
        des_ifs.
      }
    }
    { eapply lower_memory_split; eauto. }
    { ss. }
  }
  { hexploit lower_succeed_wf; try apply PROMISES; eauto. i. des.
    hexploit (@Memory.lower_exists prom0 loc from to msg0 msg_src); eauto.
    { etrans; eauto. }
    i. des. hexploit (@Memory.lower_exists_le prom0 mem_src0); eauto. i. des.
    esplits.
    { econs.
      { econs 3; eauto. inv MSG; ss. }
      { dup H. eapply Memory.lower_get0 in H. des.
        hexploit (@Memory.remove_exists mem2).
        { eapply GET1. }
        i. des. replace prom1 with mem1; eauto.
        eapply Memory.ext. i.
        erewrite (@Memory.remove_o mem1); eauto.
        erewrite (@Memory.lower_o mem2); eauto.
        erewrite (@Memory.remove_o prom1); eauto.
        erewrite (@Memory.lower_o promises2); [|eauto].
        des_ifs.
      }
    }
    { eapply lower_memory_lower; eauto. }
    { ss. }
  }
  { inv MSG. hexploit (@Memory.remove_exists_le prom0 mem_src0); eauto. i. des.
    esplits.
    { econs.
      { econs 4; eauto. }
      { eauto. }
    }
    { eapply lower_memory_remove; eauto. }
    { ss. }
  }
Qed.

Lemma lower_memory_write_na
      mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      ts_src ts_tgt loc from to prom0 val prom1 mem_tgt1 msgs kinds_tgt kind_tgt
      (WRITETGT: Memory.write_na ts_tgt prom0 mem_tgt0 loc from to val prom1 mem_tgt1 msgs kinds_tgt kind_tgt)
      (MLE: Memory.le prom0 mem_src0)
      (TS: Time.le ts_src ts_tgt)
  :
    exists mem_src1 kinds_src kind_src,
      (<<WRITESRC: Memory.write_na ts_src prom0 mem_src0 loc from to val prom1 mem_src1 msgs kinds_src kind_src>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<KINDS: kinds_src = kinds_tgt>>) /\
      (<<KIND: kind_src = kind_tgt>>).
Proof.
  revert mem_src0 ts_src TS MEM MLE. induction WRITETGT.
  { i. hexploit lower_memory_write;
         try match goal with
             | [|- Message.le _ _] => refl
             end; eauto.
    i. des. esplits; eauto. econs; eauto. eapply TimeFacts.le_lt_lt; eauto.
  }
  { i. hexploit lower_memory_write; try eassumption.
    { refl. }
    { destruct MSG_EX; des; clarify. econs; eauto. }
    { destruct MSG_EX; des; clarify. }
    i. des. hexploit IHWRITETGT.
    { refl. }
    { eauto. }
    { eapply write_memory_le; eauto. }
    i. des. esplits.
    { econs 2; eauto. eapply TimeFacts.le_lt_lt; eauto. }
    { eauto. }
    { f_equal; eauto. }
    { eauto. }
  }
Qed.

Lemma lower_memory_promise_step mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 lc_tgt1 mem_tgt1 loc from to msg kind
      (STEP: Local.promise_step lc_tgt0 mem_tgt0 loc from to msg lc_tgt1 mem_tgt1 kind)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (WF: Memory.le lc_src0.(Local.promises) mem_src0)
  :
    exists mem_src1 lc_src1,
      (<<STEP: Local.promise_step lc_src0 mem_src0 loc from to msg lc_src1 mem_src1 kind>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>).
Proof.
  inv LOCAL. inv STEP. hexploit lower_memory_promise; eauto.
  i. des. ss. esplits; eauto.
  { econs; eauto. eapply lower_memory_closed_message; eauto. }
  { econs; eauto. }
Qed.

Lemma lower_memory_read_step mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 loc to val released_tgt ord lc_tgt1
      (STEP: Local.read_step lc_tgt0 mem_tgt0 loc to val released_tgt ord lc_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (CLOSED: Memory.closed mem_src0)
  :
    exists lc_src1 released_src,
      (<<STEP: Local.read_step lc_src0 mem_src0 loc to val released_src ord lc_src1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<RELEASED: View.opt_le released_src released_tgt>>) /\
      (<<RELWF: View.opt_wf released_src>>)
.
Proof.
  inv LOCAL. inv STEP. hexploit lower_memory_get; eauto.
  i. des. inv MESSAGE.
  hexploit TViewFacts.readable_mon; eauto.
  { eapply TVIEW. }
  { refl. }
  i. esplits; eauto.
  { econs; eauto. etrans; eauto. }
  { econs; eauto. ss. eapply read_tview_mon; eauto. refl. }
  { eapply CLOSED in GETSRC. des. inv MSG_WF. auto. }
Qed.

Lemma lower_memory_fence_step
      lc_src0 lc_tgt0 ordr ordw lc_tgt1 sc_tgt0 sc_tgt1 sc_src0
      (STEP: Local.fence_step lc_tgt0 sc_tgt0 ordr ordw lc_tgt1 sc_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: TimeMap.le sc_src0 sc_tgt0)
  :
    exists lc_src1 sc_src1,
      (<<STEP: Local.fence_step lc_src0 sc_src0 ordr ordw lc_src1 sc_src1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<SC: TimeMap.le sc_src1 sc_tgt1>>)
.
Proof.
  inv LOCAL. inv STEP. esplits.
  { econs; ss. }
  { econs; ss. eapply write_fence_tview_mon_same_ord; eauto.
    eapply read_fence_tview_mon_same_ord; eauto. }
  { eapply write_fence_fc_mon_same_ord; eauto.
    eapply read_fence_tview_mon_same_ord; eauto. }
Qed.

Lemma lower_memory_write_step mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 sc_tgt0 loc from to val releasedr_tgt releasedw_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt
      releasedr_src sc_src0
      (STEP: Local.write_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val releasedr_tgt releasedw_tgt ord lc_tgt1 sc_tgt1 mem_tgt1 kind_tgt)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: TimeMap.le sc_src0 sc_tgt0)
      (WFSRC: Local.wf lc_src0 mem_src0)
      (WFTGT: Local.wf lc_tgt0 mem_tgt0)
      (RELSRC: View.opt_wf releasedr_src)
      (RELTGT: View.opt_wf releasedr_tgt)
      (RELEASEDR: View.opt_le releasedr_src releasedr_tgt)
  :
    exists lc_src1 mem_src1 releasedw_src kind_src sc_src1,
      (<<STEP: Local.write_step lc_src0 sc_src0 mem_src0 loc from to val releasedr_src releasedw_src ord lc_src1 sc_src1 mem_src1 kind_src>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<RELEASEDW: View.opt_le releasedw_src releasedw_tgt>>) /\
      (<<SC: TimeMap.le sc_src1 sc_tgt1>>) /\
      (<<KIND: kind_src = kind_tgt>>)
.
Proof.
  inv LOCAL. inv STEP.
  hexploit TViewFacts.writable_mon; eauto.
  { eapply TVIEW. }
  { refl. }
  i. ss. hexploit lower_memory_write; try eassumption.
  { eapply WFSRC. }
  { econs; [refl|]. eapply TViewFacts.write_released_mon; try eassumption.
    { eapply WFTGT. }
    { refl. }
  }
  { econs; ss. eapply TViewFacts.write_future0; eauto. eapply WFSRC. }
  { i. inv H0. econs. etrans; eauto.
    hexploit TViewFacts.write_released_mon; eauto.
    { eapply WFTGT. }
    { refl. }
    i. eapply View.unwrap_opt_le in H0. eapply H0.
  }
  i. des. esplits; eauto.
  { ss. econs; eauto. eapply TViewFacts.write_tview_mon; eauto.
    { eapply WFTGT. }
    { refl. }
  }
  { eapply TViewFacts.write_released_mon; eauto.
    { eapply WFTGT. }
    { refl. }
  }
Qed.

Lemma lower_memory_write_na_step
      mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 sc_tgt0 loc from to val ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds_tgt kind_tgt
      sc_src0
      (STEP: Local.write_na_step lc_tgt0 sc_tgt0 mem_tgt0 loc from to val ord lc_tgt1 sc_tgt1 mem_tgt1 msgs kinds_tgt kind_tgt)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: TimeMap.le sc_src0 sc_tgt0)
      (WFSRC: Local.wf lc_src0 mem_src0)
      (WFTGT: Local.wf lc_tgt0 mem_tgt0)
  :
    exists lc_src1 mem_src1 kinds_src kind_src sc_src1,
      (<<STEP: Local.write_na_step lc_src0 sc_src0 mem_src0 loc from to val ord lc_src1 sc_src1 mem_src1 msgs kinds_src kind_src>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<SC: TimeMap.le sc_src1 sc_tgt1>>) /\
      (<<KINDS: kinds_src = kinds_tgt>>) /\
      (<<KIND: kind_src = kind_tgt>>)
.
Proof.
  inv LOCAL. inv STEP. hexploit lower_memory_write_na; try eassumption.
  { eapply WFSRC. }
  { ss. eapply TVIEW. }
  i. des. ss. esplits; eauto.
  econs; ss. eapply TViewFacts.write_tview_mon; eauto. eapply WFTGT.
Qed.

Lemma lower_memory_is_racy mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0
      loc to ord
      (RACE: Local.is_racy lc_tgt0 mem_tgt0 loc to ord)
      (LOCAL: lower_local lc_src0 lc_tgt0)
  :
    Local.is_racy lc_src0 mem_src0 loc to ord.
Proof.
  inv LOCAL. inv RACE.
  hexploit lower_memory_get; eauto. i. des.
  hexploit TViewFacts.racy_view_mon; eauto.
  { eapply TVIEW. }
  i. econs; eauto.
  { inv MESSAGE; ss. }
  { i. hexploit MSG2; auto. i. subst. inv MESSAGE; ss. }
Qed.

Lemma lower_memory_program_step mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 sc_tgt0 lc_tgt1 sc_tgt1 mem_tgt1
      sc_src0 e_tgt
      (STEP: Local.program_step e_tgt lc_tgt0 sc_tgt0 mem_tgt0 lc_tgt1 sc_tgt1 mem_tgt1)
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: TimeMap.le sc_src0 sc_tgt0)
      (WFSRC: Local.wf lc_src0 mem_src0)
      (WFTGT: Local.wf lc_tgt0 mem_tgt0)
      (CLOSEDSRC: Memory.closed mem_src0)
      (CLOSEDTGT: Memory.closed mem_tgt0)
  :
    exists e_src lc_src1 mem_src1 sc_src1,
      (<<STEP: Local.program_step e_src lc_src0 sc_src0 mem_src0 lc_src1 sc_src1 mem_src1>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<SC: TimeMap.le sc_src1 sc_tgt1>>) /\
      (<<EVENT: lower_event e_src e_tgt>>)
.
Proof.
  inv STEP.
  { esplits; eauto. }
  { hexploit lower_memory_read_step; eauto. i. des.
     eexists (ThreadEvent.read _ _ _ _ _). esplits; eauto. }
  { hexploit lower_memory_write_step; eauto. i. des.
    eexists (ThreadEvent.write _ _ _ _ _ _). esplits; eauto. }
  { hexploit lower_memory_read_step; eauto. i. des.
    hexploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
    hexploit Local.read_step_future; try apply STEP; eauto. i. des.
    hexploit lower_memory_write_step; eauto. i. des.
    eexists (ThreadEvent.update _ _ _ _ _ _ _ _ _). esplits; eauto. }
  { hexploit lower_memory_fence_step; eauto. i. des.
    eexists (ThreadEvent.fence _ _). esplits; eauto. }
  { hexploit lower_memory_fence_step; eauto. i. des.
    eexists (ThreadEvent.syscall _). esplits; eauto. }
  { inv LOCAL0.
    eexists (ThreadEvent.failure). esplits; eauto.
    econs. econs. eapply lower_local_consistent; eauto. }
  { hexploit lower_memory_write_na_step; eauto. i. des.
    eexists (ThreadEvent.write_na _ _ _ _ _ _). esplits; eauto. }
  { inv LOCAL0. hexploit lower_memory_is_racy; eauto. i.
    eexists (ThreadEvent.racy_read _ _ _ _). esplits; eauto. }
  { inv LOCAL0. hexploit lower_memory_is_racy; eauto. i.
    eexists (ThreadEvent.racy_write _ _ _ _). esplits; eauto.
    econs; eauto. econs; eauto.
    eapply lower_local_consistent; eauto. }
  { eexists (ThreadEvent.racy_update _ _ _ _ _ _). esplits; eauto.
    { econs. inv LOCAL0.
      { econs 1; auto. eapply lower_local_consistent; eauto. }
      { econs 2; auto. eapply lower_local_consistent; eauto. }
      { hexploit lower_memory_is_racy; eauto. i.
        econs 3; eauto. eapply lower_local_consistent; eauto. }
    }
  }
Qed.

Lemma lower_memory_thread_step lang st0 st1 mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 sc_tgt0 lc_tgt1 sc_tgt1 mem_tgt1
      sc_src0 e_tgt pf
      (STEP: Thread.step pf e_tgt (Thread.mk lang st0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk _ st1 lc_tgt1 sc_tgt1 mem_tgt1))
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: TimeMap.le sc_src0 sc_tgt0)
      (WFSRC: Local.wf lc_src0 mem_src0)
      (WFTGT: Local.wf lc_tgt0 mem_tgt0)
      (CLOSEDSRC: Memory.closed mem_src0)
      (CLOSEDTGT: Memory.closed mem_tgt0)
  :
    exists e_src lc_src1 mem_src1 sc_src1,
      (<<STEP: Thread.step pf e_src (Thread.mk _ st0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st1 lc_src1 sc_src1 mem_src1)>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<SC: TimeMap.le sc_src1 sc_tgt1>>) /\
      (<<EVENT: lower_event e_src e_tgt>>)
.
Proof.
  inv STEP.
  { inv STEP0. hexploit lower_memory_promise_step; eauto.
    { inv LOCAL. eapply WFSRC. }
    i. des. esplits; eauto.
    { econs 1. econs; eauto. }
  }
  { inv STEP0. hexploit lower_memory_program_step; eauto.
    i. des. esplits; eauto.
    econs 2. econs; eauto. erewrite lower_event_program_event; eauto.
  }
Qed.

Lemma lower_memory_thread_opt_step lang st0 st1 mem_src0 mem_tgt0
      (MEM: lower_memory mem_src0 mem_tgt0)
      lc_src0 lc_tgt0 sc_tgt0 lc_tgt1 sc_tgt1 mem_tgt1
      sc_src0 e_tgt
      (STEP: Thread.opt_step e_tgt (Thread.mk lang st0 lc_tgt0 sc_tgt0 mem_tgt0) (Thread.mk _ st1 lc_tgt1 sc_tgt1 mem_tgt1))
      (LOCAL: lower_local lc_src0 lc_tgt0)
      (SC: TimeMap.le sc_src0 sc_tgt0)
      (WFSRC: Local.wf lc_src0 mem_src0)
      (WFTGT: Local.wf lc_tgt0 mem_tgt0)
      (CLOSEDSRC: Memory.closed mem_src0)
      (CLOSEDTGT: Memory.closed mem_tgt0)
  :
    exists e_src lc_src1 mem_src1 sc_src1,
      (<<STEP: Thread.opt_step e_src (Thread.mk _ st0 lc_src0 sc_src0 mem_src0) (Thread.mk _ st1 lc_src1 sc_src1 mem_src1)>>) /\
      (<<MEM: lower_memory mem_src1 mem_tgt1>>) /\
      (<<LOCAL: lower_local lc_src1 lc_tgt1>>) /\
      (<<SC: TimeMap.le sc_src1 sc_tgt1>>) /\
      (<<EVENT: lower_event e_src e_tgt>>)
.
Proof.
  inv STEP.
  { esplits; eauto. econs. }
  { hexploit lower_memory_thread_step; eauto. i. des. esplits; eauto. econs; eauto. }
Qed.
