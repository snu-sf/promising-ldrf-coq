From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import MemoryProps.

Set Implicit Arguments.

Inductive split_reserve
          (promises1 mem1:Memory.t)
          (loc:Loc.t) (from to:Time.t) (msg:Message.t)
          (promises2 mem2:Memory.t): forall (kind:Memory.op_kind), Prop :=
| split_reserve_intro
    ts3
    (PROMISES: Memory.split promises1 loc from to ts3 msg Message.reserve promises2)
    (MEM: Memory.split mem1 loc from to ts3 msg Message.reserve mem2)
    (TS: Memory.message_to msg loc to)
    (RESERVE: exists val' released', msg = Message.concrete val' released'):
    split_reserve promises1 mem1 loc from to msg promises2 mem2 (Memory.op_kind_split ts3 Message.reserve)
.
Hint Constructors split_reserve.

Lemma split_reserve_write prom0 mem0 loc from to msg prom1 mem1 ts3 prom2
      (SEMI: split_reserve prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_split ts3 Message.reserve))
      (REMOVE: Memory.remove prom1 loc from to msg prom2)
      (MLE: Memory.le prom0 mem0)
  :
    exists prom_mid0 mem_mid0 mem_mid1,
      (<<REMOVE: Memory.promise prom0 mem0 loc from ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel>>) /\
      (<<ADDMESSAGE: Memory.write prom_mid0 mem_mid0 loc from to msg prom_mid0 mem_mid1 Memory.op_kind_add>>) /\
      (<<ADDRESERVE: Memory.promise prom_mid0 mem_mid1 loc to ts3 Message.reserve prom2 mem1 Memory.op_kind_add>>).
Proof.
  inv SEMI. des. clarify.
  hexploit split_succeed_wf; try apply PROMISES. i. des.
  exploit Memory.split_get0; [eapply PROMISES|]. intros. des.
  exploit (@Memory.remove_exists prom0 loc from ts3 Message.reserve); eauto.
  intros [prom_mid0 PROMREMOVE].
  exploit (@Memory.remove_exists_le prom0 mem0 loc from ts3 Message.reserve); eauto.
  intros [mem_mid0 MEMREMOVE].
  assert (PROMISE0: Memory.promise prom0 mem0 loc from ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel).
  { econs; eauto. }
  hexploit promise_memory_le; try apply PROMISE0; eauto. intros MLEMID0.
  exploit (@Memory.add_exists mem_mid0 loc from to (Message.concrete val' released')); eauto.
  { ii. erewrite Memory.remove_o in GET4; eauto. des_ifs. guardH o.
    exploit Memory.get_disjoint.
    { eapply GET4. }
    { eapply Memory.split_get0 in MEM. des. apply GET6. }
    i. des.
    { unguard. ss. des; clarify. }
    { eapply x1; eauto. inv LHS. econs; eauto.
      ss. etrans; eauto. left. auto. }
  }
  intros [mem_mid1 MEMADDMESSAGE].
  exploit (@Memory.add_exists_le prom_mid0 mem_mid0 loc from to (Message.concrete val' released')); eauto.
  intros [prom_mid1 PROMADDMESSAGE].
  exploit (@Memory.remove_exists prom_mid1 loc from to (Message.concrete val' released')).
  { eapply Memory.add_get0; eauto. }
  intros [prom_mid2 PROMFULFILL].
  assert (prom_mid2 = prom_mid0).
  { eapply MemoryFacts.add_remove_eq; eauto. } subst.
  assert (WRTIE0: Memory.write prom_mid0 mem_mid0 loc from to (Message.concrete val' released') prom_mid0 mem_mid1 Memory.op_kind_add).
  { econs; eauto. econs; eauto. i.
    erewrite Memory.remove_o in GET4; eauto. des_ifs. guardH o.
    exploit Memory.get_disjoint.
    { eapply GET4. }
    { eapply Memory.split_get0 in MEM. des. apply GET6. }
    i. des.
    { unguard. ss. des; clarify. }
    { eapply memory_get_ts_strong in GET4. des.
      { subst. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; try apply TS12. eapply Time.bot_spec. }
      eapply x0.
      { instantiate (1:=Time.meet to' ts3). unfold Time.meet. des_ifs.
        { econs; ss. refl. }
        { econs; ss. left. auto. }
      }
      { unfold Time.meet. des_ifs.
        { econs; ss. transitivity to; eauto. }
        { econs; ss.
          { transitivity to; eauto. }
          { refl. }
        }
      }
    }
  }
  hexploit write_memory_le; try apply WRITE0; eauto. intros MLEMID1.
  exploit (@Memory.add_exists mem_mid1 loc to ts3 Message.reserve); eauto.
  { ii. erewrite Memory.add_o in GET4; eauto. des_ifs.
    { ss. des; clarify. inv LHS. inv RHS. ss. timetac. }
    guardH o. erewrite Memory.remove_o in GET4; eauto. des_ifs. guardH o0.
    exploit Memory.get_disjoint.
    { eapply GET4. }
    { eapply Memory.split_get0 in MEM. des. apply GET6. }
    i. des.
    { unguard. ss. des; clarify. }
    { eapply x1; eauto. inv LHS. econs; eauto. }
  }
  intros [mem_mid2 MEMADDRESERVE].
  exploit (@Memory.add_exists_le prom_mid0 mem_mid1 loc to ts3 Message.reserve); eauto.
  intros [prom_mid2 PROMADDRESERVE].
  assert (PROMEQ: prom_mid2 = prom2).
  { eapply Memory.ext. intros.
    erewrite (@Memory.add_o prom_mid2 prom_mid0); eauto.
    erewrite (@Memory.remove_o prom_mid0 prom0); eauto.
    erewrite (@Memory.remove_o prom2 prom1); eauto.
    erewrite (@Memory.split_o prom1 prom0); eauto. des_ifs.
    { ss. des; clarify. }
    { ss. des; clarify. }
  }
  assert (MEMEQ: mem_mid2 = mem1).
  { eapply Memory.ext. intros.
    erewrite (@Memory.add_o mem_mid2 mem_mid1); eauto.
    erewrite (@Memory.add_o mem_mid1 mem_mid0); eauto.
    erewrite (@Memory.remove_o mem_mid0 mem0); eauto.
    erewrite (@Memory.split_o mem1 mem0); eauto. des_ifs.
    ss. des; clarify.
  }
  subst. esplits; eauto.
Qed.

Lemma split_reserve_promise prom0 mem0 loc from to msg prom1 mem1 ts3
      (SEMI: split_reserve prom0 mem0 loc from to msg prom1 mem1 (Memory.op_kind_split ts3 Message.reserve))
      (MLE: Memory.le prom0 mem0)
  :
    exists prom_mid0 mem_mid0 prom_mid1 mem_mid1,
      (<<REMOVE: Memory.promise prom0 mem0 loc from ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel>>) /\
      (<<ADDMESSAGE: Memory.promise prom_mid0 mem_mid0 loc from to msg prom_mid1 mem_mid1 Memory.op_kind_add>>) /\
      (<<ADDRESERVE: Memory.promise prom_mid1 mem_mid1 loc to ts3 Message.reserve prom1 mem1 Memory.op_kind_add>>) /\
      (<<CLOSEDMSG: Memory.closed_message msg mem1 -> Memory.closed_message msg mem_mid1>>).
Proof.
  inv SEMI. des. clarify.
  hexploit split_succeed_wf; try apply PROMISES. i. des.
  exploit Memory.split_get0; [eapply PROMISES|]. intros. des.
  exploit (@Memory.remove_exists prom0 loc from ts3 Message.reserve); eauto.
  intros [prom_mid0 PROMREMOVE].
  exploit (@Memory.remove_exists_le prom0 mem0 loc from ts3 Message.reserve); eauto.
  intros [mem_mid0 MEMREMOVE].
  assert (PROMISE0: Memory.promise prom0 mem0 loc from ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel).
  { econs; eauto. }
  hexploit promise_memory_le; try apply PROMISE0; eauto. intros MLEMID0.
  exploit (@Memory.add_exists mem_mid0 loc from to (Message.concrete val' released')); eauto.
  { ii. erewrite Memory.remove_o in GET4; eauto. des_ifs. guardH o.
    exploit Memory.get_disjoint.
    { eapply GET4. }
    { eapply Memory.split_get0 in MEM. des. apply GET6. }
    i. des.
    { unguard. ss. des; clarify. }
    { eapply x1; eauto. inv LHS. econs; eauto.
      ss. etrans; eauto. left. auto. }
  }
  intros [mem_mid1 MEMADDMESSAGE].
  exploit (@Memory.add_exists_le prom_mid0 mem_mid0 loc from to (Message.concrete val' released')); eauto.
  intros [prom_mid1 PROMADDMESSAGE].
  assert (PROMISE1: Memory.promise prom_mid0 mem_mid0 loc from to (Message.concrete val' released') prom_mid1 mem_mid1 Memory.op_kind_add).
  { econs; eauto. i.
    erewrite Memory.remove_o in GET4; eauto. des_ifs. guardH o.
    exploit Memory.get_disjoint.
    { eapply GET4. }
    { eapply Memory.split_get0 in MEM. des. apply GET6. }
    i. des.
    { unguard. ss. des; clarify. }
    { eapply memory_get_ts_strong in GET4. des.
      { subst. exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; try apply TS12. eapply Time.bot_spec. }
      eapply x0.
      { instantiate (1:=Time.meet to' ts3). unfold Time.meet. des_ifs.
        { econs; ss. refl. }
        { econs; ss. left. auto. }
      }
      { unfold Time.meet. des_ifs.
        { econs; ss. transitivity to; eauto. }
        { econs; ss.
          { transitivity to; eauto. }
          { refl. }
        }
      }
    }
  }
  hexploit promise_memory_le; try apply PROMISE1; eauto. intros MLEMID1.
  exploit (@Memory.add_exists mem_mid1 loc to ts3 Message.reserve); eauto.
  { ii. erewrite Memory.add_o in GET4; eauto. des_ifs.
    { ss. des; clarify. inv LHS. inv RHS. ss. timetac. }
    guardH o. erewrite Memory.remove_o in GET4; eauto. des_ifs. guardH o0.
    exploit Memory.get_disjoint.
    { eapply GET4. }
    { eapply Memory.split_get0 in MEM. des. apply GET6. }
    i. des.
    { unguard. ss. des; clarify. }
    { eapply x1; eauto. inv LHS. econs; eauto. }
  }
  intros [mem_mid2 MEMADDRESERVE].
  exploit (@Memory.add_exists_le prom_mid1 mem_mid1 loc to ts3 Message.reserve); eauto.
  intros [prom_mid2 PROMADDRESERVE].
  assert (PROMEQ: prom_mid2 = prom1).
  { eapply Memory.ext. intros.
    erewrite (@Memory.add_o prom_mid2 prom_mid1); eauto.
    erewrite (@Memory.add_o prom_mid1 prom_mid0); eauto.
    erewrite (@Memory.remove_o prom_mid0 prom0); eauto.
    erewrite (@Memory.split_o prom1 prom0); eauto. des_ifs.
    ss. des; clarify.
  }
  assert (MEMEQ: mem_mid2 = mem1).
  { eapply Memory.ext. intros.
    erewrite (@Memory.add_o mem_mid2 mem_mid1); eauto.
    erewrite (@Memory.add_o mem_mid1 mem_mid0); eauto.
    erewrite (@Memory.remove_o mem_mid0 mem0); eauto.
    erewrite (@Memory.split_o mem1 mem0); eauto. des_ifs.
    ss. des; clarify.
  }
  subst. esplits; eauto.
  { i. eapply memory_concrete_le_closed_msg; try apply H. ii.
    erewrite (@Memory.split_o mem1 mem0) in GET4; eauto.
    erewrite (@Memory.add_o mem_mid1 mem_mid0); eauto.
    erewrite (@Memory.remove_o mem_mid0 mem0); eauto. des_ifs.
  }
Qed.
