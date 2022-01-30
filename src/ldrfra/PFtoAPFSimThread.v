Require Import Omega.
Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import MemoryMerge.
Require Import MemoryReorder.

Require Import PFStep.
Require Import OrdStep.
Require Import Writes.
Require Import WStep.
Require Import Stable.

Set Implicit Arguments.


Module PFtoAPFSimThread.
  Section PFtoAPFSimThread.
    Variable lang: language.
    Variable L: Loc.t -> bool.

    Variant sim_memory (rels: Writes.t) (mem_src mem_tgt: Memory.t): Prop :=
    | sim_memory_intro
        (SOUND: Memory.le mem_src mem_tgt)
        (COMPLETE1: forall loc (LOC: ~ L loc)
                      from to msg (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
            (<<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>))
        (COMPLETE2: forall loc ts from to msg
                      (LOC: L loc) (LE: Time.le ts to)
                      (GET_TGT: Memory.get loc to mem_tgt = Some (from, msg)),
            (<<GET_SRC: Memory.get loc to mem_src = Some (from, msg)>>) \/
            exists from' to' val ord,
              (<<IN: List.In (loc, to', ord) rels>>) /\
              (<<LT: Time.lt ts to'>>) /\
              (<<ORD: Ordering.le ord Ordering.na>>) /\
              (<<GET_SRC: Memory.get loc to' mem_src = Some (from', Message.concrete val None)>>))
        (RESERVE: forall loc from to
                    (GET_TGT: Memory.get loc to mem_tgt = Some (from, Message.reserve)),
            (<<GET_SRC: Memory.get loc to mem_src = Some (from, Message.reserve)>>))
    .
    Hint Constructors sim_memory.

    Inductive sim_statelocal (rels: Writes.t):
      forall (sl_src sl_tgt: {lang : language & Language.state lang} * Local.t), Prop :=
    | sim_statelocal_intro
        lang st lc_src lc_tgt
        (LOCAL: lc_src = lc_tgt):
        sim_statelocal rels (existT _ lang st, lc_src) (existT _ lang st, lc_tgt)
    .
    Hint Constructors sim_statelocal.

    Inductive sim_thread (rels: Writes.t) (e_src e_tgt: Thread.t lang): Prop :=
    | sim_thread_intro
        (STATE: (Thread.state e_src) = (Thread.state e_tgt))
        (LOCAL: (Thread.local e_src) = (Thread.local e_tgt))
        (* (RESERVE_ONLY: OrdLocal.reserve_only L (Local.promises (Thread.local e_src))) *)
        (* (WRITES_WF: Writes.wf rels (Local.promises (Thread.local e_src)) (Thread.memory e_src)) *)
        (SC: (Thread.sc e_src) = (Thread.sc e_tgt))
        (MEMORY: sim_memory rels (Thread.memory e_src) (Thread.memory e_tgt))
    .
    Hint Constructors sim_thread.

    Lemma sim_memory_cons
          a rels mem_src mem_tgt
          (MEM: sim_memory rels mem_src mem_tgt):
      sim_memory (a :: rels) mem_src mem_tgt.
    Proof.
      inv MEM. econs; eauto. i.
      exploit COMPLETE2; eauto. i. des; eauto.
      right. esplits; eauto. econs 2. ss.
    Qed.

    Lemma sim_memory_append
          e rels mem_src mem_tgt
          (MEM: sim_memory rels mem_src mem_tgt):
      sim_memory (Writes.append L e rels) mem_src mem_tgt.
    Proof.
      unfold Writes.append.
      destruct e; ss; condtac; ss; apply sim_memory_cons; ss.
    Qed.

    Lemma sim_memory_app
          rels' rels mem_src mem_tgt
          (MEM: sim_memory rels mem_src mem_tgt):
      sim_memory (rels' ++ rels) mem_src mem_tgt.
    Proof.
      inv MEM. econs; eauto. i.
      exploit COMPLETE2; eauto. i. des; eauto.
      right. esplits; eauto.
      apply List.in_or_app. eauto.
    Qed.

    Lemma promise
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (PROMISE_TGT: Memory.promise promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind):
      exists mem2_src,
        <<PROMISE_SRC: Memory.promise promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv MEM1. inv PROMISE_TGT; ss.
      { (* add *)
        exploit (@Memory.add_exists mem1_src loc from to msg).
        { i. exploit SOUND; eauto. i.
          exploit Memory.add_get0; try exact MEM. i. des.
          exploit Memory.add_get1; try exact x; eauto. i.
          exploit Memory.get_disjoint; [exact GET0|exact x1|]. i. des; subst; ss. congr.
        }
        { inv MEM. inv ADD. ss. }
        { inv MEM. inv ADD. ss. }
        i. des. esplits; eauto. econs; ii.
        - erewrite Memory.add_o; eauto.
          revert LHS. erewrite Memory.add_o; try exact x0.
          condtac; ss; eauto.
        - erewrite Memory.add_o; eauto.
          revert GET_TGT. erewrite Memory.add_o; try exact MEM.
          condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.add_o; try exact MEM.
          condtac; ss.
          + i. des. clarify.
            exploit Memory.add_get0; try exact x0. i. des. eauto.
          + guardH o. i. exploit COMPLETE2; eauto. i. des.
            * exploit Memory.add_get1; try exact GET_SRC; eauto.
            * exploit Memory.add_get1; try exact GET_SRC; eauto. i.
              right. esplits; try exact x1; eauto.
        - erewrite Memory.add_o; eauto.
          revert GET_TGT. erewrite Memory.add_o; try exact MEM.
          condtac; ss; eauto.
      }

      { (* split *)
        exploit Memory.split_exists_le; try exact LE1_SRC; eauto. i. des.
        esplits; eauto. econs; ii.
        - erewrite Memory.split_o; eauto.
          revert LHS. erewrite Memory.split_o; try exact x0.
          repeat condtac; ss; eauto.
        - erewrite Memory.split_o; eauto.
          revert GET_TGT. erewrite Memory.split_o; try exact MEM.
          repeat condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.split_o; try exact MEM.
          repeat condtac; ss.
          + i. des. clarify.
            exploit Memory.split_get0; try exact x0. i. des. eauto.
          + guardH o. i. des. clarify.
            exploit Memory.split_get0; try exact x0. i. des. eauto.
          + guardH o. guardH o0.
            i. exploit COMPLETE2; eauto. i. des.
            * left. erewrite Memory.split_o; eauto. repeat condtac; ss; congr.
            * exploit Memory.split_get1; try exact GET_SRC; eauto. i. des.
              right. esplits; eauto.
        - erewrite Memory.split_o; eauto.
          revert GET_TGT. erewrite Memory.split_o; try exact MEM.
          repeat condtac; ss; eauto.
      }

      { (* lower *)
        exploit Memory.lower_exists_le; try exact LE1_SRC; eauto. i. des.
        esplits; eauto. econs; ii.
        - erewrite Memory.lower_o; eauto.
          revert LHS. erewrite Memory.lower_o; try exact x0.
          condtac; ss; eauto.
        - erewrite Memory.lower_o; eauto.
          revert GET_TGT. erewrite Memory.lower_o; try exact MEM.
          condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.lower_o; try exact MEM.
          condtac; ss.
          + i. des. clarify.
            exploit Memory.lower_get0; try exact x0. i. des. eauto.
          + guardH o. i. exploit COMPLETE2; eauto. i. des.
            * left. erewrite Memory.lower_o; eauto. condtac; ss; eauto.
            * exploit Memory.lower_get1; try exact GET_SRC; eauto. i. des.
              inv MSG_LE. inv RELEASED.
              right. esplits; eauto.
        - erewrite Memory.lower_o; eauto.
          revert GET_TGT. erewrite Memory.lower_o; try exact MEM.
          condtac; ss; eauto.
      }

      { (* remove *)
        exploit Memory.remove_exists_le; try exact LE1_SRC; eauto. i. des.
        esplits; eauto. econs; ii.
        - erewrite Memory.remove_o; eauto.
          revert LHS. erewrite Memory.remove_o; try exact x0.
          condtac; ss; eauto.
        - erewrite Memory.remove_o; eauto.
          revert GET_TGT. erewrite Memory.remove_o; try exact MEM.
          condtac; ss; eauto.
        - revert GET_TGT. erewrite Memory.remove_o; try exact MEM.
          condtac; ss.
          guardH o. i. exploit COMPLETE2; eauto. i. des.
          + left. erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          + exploit Memory.remove_get1; try exact GET_SRC; eauto. i. des.
            { subst. exploit Memory.remove_get0; try exact x0. i. des. congr. }
            right. esplits; eauto.
        - erewrite Memory.remove_o; eauto.
          revert GET_TGT. erewrite Memory.remove_o; try exact MEM.
          condtac; ss; eauto.
      }
    Qed.

    Lemma write
          rels mem1_src
          promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (WRITE_TGT: Memory.write promises1 mem1_tgt loc from to msg promises2 mem2_tgt kind):
      exists mem2_src,
        <<WRITE_SRC: Memory.write promises1 mem1_src loc from to msg promises2 mem2_src kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      inv WRITE_TGT. exploit promise; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_other
          rels mem1_src
          ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (LOC: ~ L loc)
          (WRITE_TGT: Memory.write_na ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind):
      exists mem2_src,
        <<WRITE_SRC: Memory.write_na ts promises1 mem1_src loc from to val promises2 mem2_src msgs kinds kind>> /\
        <<MEM2: sim_memory rels mem2_src mem2_tgt>>.
    Proof.
      revert mem1_src MEM1 WRITES1 LE1_SRC.
      induction WRITE_TGT; i.
      { exploit write; eauto. i. des. eauto. }
      exploit write; eauto. i. des.
      hexploit Memory.write_le; try exact WRITE_SRC; eauto. i.
      hexploit Writes.write_wf_other; try exact WRITE_SRC; eauto. i.
      exploit IHWRITE_TGT; try exact MEM2; eauto. i. des.
      esplits; eauto.
    Qed.

    Lemma write_add_memory_add
          promises1 mem1 loc from to msg promises2 mem2
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 Memory.op_kind_add):
      (<<PROMISES: promises2 = promises1>>) /\
      (<<ADD: Memory.add mem1 loc from to msg mem2>>).
    Proof.
      inv WRITE. inv PROMISE. splits; ss.
      exploit MemoryMerge.add_remove; try exact PROMISES; eauto.
    Qed.

    Lemma reorder_add_write_add
          promises0 mem0 loc from1 to1 msg1 mem1
          from2 to2 msg2 promises2 mem2
          (ADD: Memory.add mem0 loc from1 to1 msg1 mem1)
          (WRITE: Memory.write promises0 mem1 loc from2 to2 msg2 promises2 mem2 Memory.op_kind_add):
      exists mem1',
        (<<WRITE: Memory.write promises0 mem0 loc from2 to2 msg2 promises2 mem1' Memory.op_kind_add>>) /\
        (<<ADD: Memory.add mem1' loc from1 to1 msg1 mem2>>).
    Proof.
      inv WRITE. inv PROMISE.
      exploit MemoryReorder.add_add; [exact ADD|exact MEM|]. i. des.
      exploit MemoryMerge.add_remove; [exact PROMISES|exact REMOVE|]. i. subst.
      esplits; try exact ADD2.
      econs; [econs; eauto|]; eauto. i.
      exploit Memory.add_get1; try exact ADD; eauto.
    Qed.

    Lemma reserve_only_write_add
          promises1 mem1 loc from to msg promises2 mem2 kind
          (RESERVE_ONLY: OrdLocal.reserve_only L promises1)
          (LOC: L loc)
          (WRITE: Memory.write promises1 mem1 loc from to msg promises2 mem2 kind):
      kind = Memory.op_kind_add.
    Proof.
      inv WRITE. inv PROMISE; ss; exfalso.
      - exploit Memory.split_get0; try exact PROMISES. i. des. eauto.
      - exploit Memory.lower_get0; try exact PROMISES. i. des.
        exploit RESERVE_ONLY; eauto. i. subst. inv MSG_LE. ss.
      - exploit Memory.remove_get0; try exact PROMISES. i. des.
        exploit Memory.remove_get0; try exact REMOVE. i. des. congr.
    Qed.

    Lemma reorder_write_write_na
          promises0 mem0 loc from1 to1 msg1 promises1 mem1 kind1
          ts from2 to2 val2 promises2 mem2 msgs2 kinds2 kind2
          (RESERVE_ONLY: OrdLocal.reserve_only L promises0)
          (LOC: L loc)
          (WRITE: Memory.write promises0 mem0 loc from1 to1 msg1 promises1 mem1 kind1)
          (WRITE_NA: Memory.write_na ts promises1 mem1 loc from2 to2 val2 promises2 mem2 msgs2 kinds2 kind2):
      exists mem1',
        (<<WRITE_NA: Memory.write_na ts promises0 mem0 loc from2 to2 val2 promises2 mem1' msgs2 kinds2 kind2>>) /\
        (<<ADD: Memory.add mem1' loc from1 to1 msg1 mem2>>).
    Proof.
      exploit reserve_only_write_add; eauto. i. subst.
      exploit write_add_memory_add; eauto. i. des. subst.
      clear WRITE. revert ts mem0 mem1 promises2 mem2 kinds2 ADD WRITE_NA.
      induction msgs2 as [|[to' msg'] msgs]; i.
      { inv WRITE_NA.
        exploit reserve_only_write_add; eauto. i. subst.
        exploit reorder_add_write_add; eauto. i. des.
        esplits; eauto.
      }
      inv WRITE_NA.
      hexploit OrdLocal.write_reserve_only; try exact WRITE_EX; eauto. i.
      exploit reserve_only_write_add; try exact WRITE_EX; eauto. i. subst.
      exploit reorder_add_write_add; try exact ADD; eauto. i. des.
      exploit write_add_memory_add; try exact WRITE_EX. i. des. subst. clear ADD1.
      exploit IHmsgs; try exact ADD0; try exact WRITE_NA0. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_loc
          rels mem1_src
          ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind
          ord
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (RESERVE_ONLY: OrdLocal.reserve_only L promises1)
          (LE1_SRC: Memory.le promises1 mem1_src)
          (LOC: L loc)
          (ORD: Ordering.le ord Ordering.na)
          (WRITE_TGT: Memory.write_na ts promises1 mem1_tgt loc from to val promises2 mem2_tgt msgs kinds kind):
      exists mem2_src,
        (<<WRITE_SRC: Memory.write promises1 mem1_src loc from to (Message.concrete val None) promises2 mem2_src kind>>) /\
        (<<MEM2: sim_memory ((loc, to, ord) :: rels) mem2_src mem2_tgt>>).
    Proof.
      revert ts mem1_tgt promises2 mem2_tgt kinds MEM1 WRITE_TGT.
      induction msgs as [|[to' msg'] msgs]; i.
      { inv WRITE_TGT.
        exploit write; eauto. i. des.
        esplits; eauto using sim_memory_cons.
      }
      inv WRITE_TGT.
      exploit reserve_only_write_add; try exact WRITE_EX; eauto. i. subst.
      exploit reorder_write_write_na; eauto. i. des.
      exploit IHmsgs; try exact WRITE_NA0; eauto. i. des.
      esplits; eauto.
      exploit Memory.write_na_times; try exact WRITE_NA. i. des.
      clear - ORD LOC MSG_EX ADD MEM2 WRITE_SRC x1.
      inv MEM2. econs.
      - etrans; eauto. ii.
        erewrite Memory.add_o; eauto. condtac; ss; eauto. des. subst.
        exploit Memory.add_get0; eauto. i. des. congr.
      - i. revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; ss; eauto. i. des. clarify.
      - i. revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; ss; eauto. i. des. clarify.
        exploit Memory.write_get2; try exact WRITE_SRC. i. des.
        right. esplits; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
      - i. revert GET_TGT. erewrite Memory.add_o; eauto.
        condtac; ss; eauto. i. des. clarify.
        unguard. des; ss.
    Qed.

    Lemma promise_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to msg lc2_tgt mem2_tgt kind)
          (MSG1: forall promises2_src mem2_src
                   (PROMISE: Memory.promise (Local.promises lc1_src) mem1_src loc from to msg promises2_src mem2_src kind),
              Memory.closed_message msg mem2_src):
      exists lc2_src mem2_src,
        (<<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to msg lc2_src mem2_src kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit promise; try exact MEM; eauto; try apply WF1_SRC; try apply WF1_TGT. i. des.
      esplits; eauto.
    Qed.

    Lemma ordc_na
          ordc ord loc
          (ORDC: Ordering.le ordc Ordering.na):
      (if L loc then Ordering.join ord ordc else ord) = ord.
    Proof.
      condtac; ss.
      destruct ordc, ord; ss.
    Qed.

    Lemma read_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc to val released ord lc2_tgt
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_MEM1: Normal.normal_memory L mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc to val released ord lc2_tgt):
      (exists lc2_src,
          (<<STEP_SRC: OrdLocal.read_step L Ordering.na lc1_src mem1_src loc to val released ord lc2_src>>) /\
          (<<LC2: lc2_src = lc2_tgt>>) /\
          (<<NORMAL_TVIEW2: Normal.normal_tview L (Local.tview lc2_src)>>)) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv MEM1. inv STEP_TGT.
      destruct (Memory.get loc to mem1_src) as [[from_src msg_src]|] eqn:GET_SRC; cycle 1.
      { (* race *)
        destruct (L loc) eqn:LOC; cycle 1.
        { exploit COMPLETE1; eauto; try congr. }
        inv READABLE. inv NORMAL_TVIEW1.
        exploit COMPLETE2; eauto. i. des; try congr.
        right. unfold RARaceW.wr_race.
        esplits; try exact ORD0; eauto.
        rewrite CUR; ss.
      }
      exploit SOUND; eauto. i. rewrite x in *. inv GET.
      destruct (classic (L loc /\ Ordering.le ord Ordering.plain /\
                         Time.lt (View.rlx (TView.cur (Local.tview lc1_tgt)) loc) to)).
      { (* race *)
        right. des. unfold RARaceW.wr_race.
        inv WRITES1. exploit COMPLETE; try exact GET_SRC; eauto. i. des.
        esplits; eauto.
      }
      left. esplits.
      - econs; eauto. rewrite ordc_na; ss. eauto.
      - ss.
      - exploit Normal.read_step; try exact WF1_SRC; eauto. i.
        inv READABLE. inv NORMAL_TVIEW1. rewrite CUR in *; ss.
        inv PLN; ss.
        exfalso. apply H. splits; ss.
    Qed.

    Lemma write_step
          rels lc1_src sc1_src mem1_src
          lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm released ord lc2_tgt sc2_tgt mem2_tgt kind
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val
                                      releasedm released ord lc2_tgt sc2_tgt mem2_tgt kind):
      exists lc2_src sc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_step L Ordering.plain
                                         lc1_src sc1_src mem1_src loc from to val
                                         releasedm released ord lc2_src sc2_src mem2_src kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<SC2: sc2_src = sc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit write; try exact MEM1; eauto; try apply WF1_SRC. i. des.
      esplits; eauto.
      econs; eauto. econs; eauto; try (condtac; ss).
      - unfold TView.write_released.
        repeat condtac; destruct ord; ss.
      - inv WRITABLE. econs. ss.
      - destruct ord; ss.
      - f_equal. unfold TView.write_released.
        repeat condtac; destruct ord; ss.
    Qed.

    Lemma write_na_step_other
          rels lc1_src sc1_src mem1_src
          lc1_tgt sc1_tgt mem1_tgt loc from to val ord lc2_tgt sc2_tgt mem2_tgt msgs kinds kind
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (LOC: ~ L loc)
          (STEP_TGT: Local.write_na_step lc1_tgt sc1_tgt mem1_tgt loc from to val ord
                                         lc2_tgt sc2_tgt mem2_tgt msgs kinds kind):
      exists lc2_src sc2_src mem2_src,
        (<<STEP_SRC: Local.write_na_step lc1_src sc1_src mem1_src loc from to val ord
                                         lc2_src sc2_src mem2_src msgs kinds kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<SC2: sc2_src = sc2_tgt>>) /\
        (<<MEM2: sim_memory rels mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit write_na_other; eauto; try apply WF1_SRC. i. des.
      esplits; eauto.
    Qed.

    Lemma write_na_step_loc
          rels lc1_src sc1_src mem1_src
          lc1_tgt sc1_tgt mem1_tgt loc from to val ord lc2_tgt sc2_tgt mem2_tgt msgs kinds kind
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (LOC: L loc)
          (STEP_TGT: Local.write_na_step lc1_tgt sc1_tgt mem1_tgt loc from to val ord
                                         lc2_tgt sc2_tgt mem2_tgt msgs kinds kind):
      exists lc2_src sc2_src mem2_src,
        (<<STEP_SRC: OrdLocal.write_na_step L Ordering.plain
                                            lc1_src sc1_src mem1_src loc from to val ord
                                            lc2_src sc2_src mem2_src [] [] kind>>) /\
        (<<LC2: lc2_src = lc2_tgt>>) /\
        (<<SC2: sc2_src = sc2_tgt>>) /\
        (<<MEM2: sim_memory ((loc, to, ord) :: rels) mem2_src mem2_tgt>>).
    Proof.
      inv STEP_TGT.
      exploit write_na_loc; try exact MEM1; eauto; try apply WF1_SRC. i. des.
      esplits; eauto. econs 2; eauto.
      destruct (L loc); ss. econs; eauto.
      - exploit Memory.write_na_times; eauto. i. des.
        econs; eauto.
      - unfold TView.write_released. condtac; eauto.
        destruct ord; ss.
      - destruct ord; ss.
      - f_equal.
        unfold TView.write_tview. f_equal.
        repeat condtac; ss; destruct ord; ss.
    Qed.

    Lemma is_racy
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc ord
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.is_racy lc1_tgt mem1_tgt loc ord):
      (<<STEP_SRC: Local.is_racy lc1_src mem1_src loc ord>>) \/
      (exists to ordw,
          (<<LOC: L loc>>) /\
          (<<HIGHER: Time.lt (View.rlx (TView.cur (Local.tview lc1_src)) loc) to>>) /\
          (<<IN: List.In (loc, to, ordw) rels>>) /\
          (<<ORD: Ordering.le ordw Ordering.na>>)).
    Proof.
      inv MEM1. inv STEP_TGT.
      destruct (Memory.get loc to mem1_src) as [[from_src msg_src]|] eqn:GET_SRC.
      { exploit SOUND; eauto. i.
        rewrite x in *. inv GET. eauto.
      }
      destruct (L loc) eqn:LOC; cycle 1.
      { exploit COMPLETE1; eauto. rewrite LOC. ss. }
      exploit COMPLETE2; eauto.
      { econs. eauto. }
      i. des; eauto.
      right. esplits; eauto.
      inv NORMAL_TVIEW1. rewrite CUR; ss.
    Qed.

    Lemma racy_read_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc val ord
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.racy_read_step lc1_tgt mem1_tgt loc val ord):
      (<<STEP_SRC: OrdLocal.racy_read_step L Ordering.na lc1_src mem1_src loc val ord>>) \/
      (<<RACE: RARaceW.wr_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      - left. econs; eauto. rewrite ordc_na; ss.
      - right. unfold RARaceW.wr_race.
        esplits; eauto.
    Qed.

    Lemma racy_write_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc ord
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.racy_write_step lc1_tgt mem1_tgt loc ord):
      (<<STEP_SRC: OrdLocal.racy_write_step L Ordering.plain lc1_src mem1_src loc ord>>) \/
      (<<RACE: RARaceW.ww_race L rels (Local.tview lc1_src) loc ord>>).
    Proof.
      inv STEP_TGT.
      exploit is_racy; eauto. i. des.
      - destruct (L loc) eqn:LOC; cycle 1.
        { left. econs; eauto. rewrite LOC. eauto. }
        inv STEP_SRC. destruct msg; ss.
        + inv WRITES1. exploit COMPLETE; eauto. i. des.
          right. unfold RARaceW.ww_race.
          inv NORMAL_TVIEW1. rewrite CUR; ss.
          esplits; eauto. right.
          destruct ord; ss; exploit MSG2; ss.
        + left. econs; eauto.
      - right. unfold RARaceW.ww_race.
        esplits; eauto.
    Qed.

    Lemma racy_update_step
          rels lc1_src mem1_src
          lc1_tgt mem1_tgt loc ordr ordw
          (LC1: lc1_src = lc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (STEP_TGT: Local.racy_update_step lc1_tgt mem1_tgt loc ordr ordw):
      (<<STEP_SRC: Local.racy_update_step lc1_src mem1_src loc ordr ordw>>) \/
      (<<RACE: RARaceW.ww_race L rels (Local.tview lc1_src) loc ordw>>).
    Proof.
      inv STEP_TGT; eauto.
      exploit is_racy; eauto. i. des; eauto.
      right. unfold RARaceW.ww_race.
      esplits; eauto.
    Qed.

    Variant sim_event: forall (e_src e_tgt: ThreadEvent.t), Prop :=
    | sim_event_promise
        loc from to msg kind:
        sim_event (ThreadEvent.promise loc from to msg kind)
                  (ThreadEvent.promise loc from to msg kind)
    | sim_event_silent:
        sim_event ThreadEvent.silent ThreadEvent.silent
    | sim_event_read
        loc to val released ord:
        sim_event (ThreadEvent.read loc to val released ord)
                  (ThreadEvent.read loc to val released ord)
    | sim_event_write
        loc from to val released ord:
        sim_event (ThreadEvent.write loc from to val released ord)
                  (ThreadEvent.write loc from to val released ord)
    | sim_event_write_na
        loc msgs_src msgs_tgt from to val ord:
        sim_event (ThreadEvent.write_na loc msgs_src from to val ord)
                  (ThreadEvent.write_na loc msgs_tgt from to val ord)
    | sim_event_update
        loc from to valr valw releasedm released ordr ordw:
        sim_event (ThreadEvent.update loc from to valr valw releasedm released ordr ordw)
                  (ThreadEvent.update loc from to valr valw releasedm released ordr ordw)
    | sim_event_fence
        ordr ordw:
        sim_event (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
    | sim_event_syscall
        e:
        sim_event (ThreadEvent.syscall e) (ThreadEvent.syscall e)
    | sim_event_failure:
      sim_event ThreadEvent.failure ThreadEvent.failure
    | sim_event_racy_read
        loc val ord:
      sim_event (ThreadEvent.racy_read loc val ord)
                (ThreadEvent.racy_read loc val ord)
    | sim_event_racy_write
        loc val ord:
      sim_event (ThreadEvent.racy_write loc val ord)
                (ThreadEvent.racy_write loc val ord)
    | sim_event_racy_update
        loc valr valw ordr ordw:
      sim_event (ThreadEvent.racy_update loc valr valw ordr ordw)
                (ThreadEvent.racy_update loc valr valw ordr ordw)
    .
    Hint Constructors sim_event.

    Lemma program_step
          rels lc1_src sc1_src mem1_src
          e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt
          (LC1: lc1_src = lc1_tgt)
          (SC1: sc1_src = sc1_tgt)
          (MEM1: sim_memory rels mem1_src mem1_tgt)
          (WRITES1: Writes.wf L rels mem1_src)
          (RESERVE_ONLY1: OrdLocal.reserve_only L (Local.promises lc1_src))
          (NORMAL_TVIEW1: Normal.normal_tview L (Local.tview lc1_src))
          (NORMAL_MEM1: Normal.normal_memory L mem1_src)
          (WF1_SRC: Local.wf lc1_src mem1_src)
          (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
          (MEM1_SRC: Memory.closed mem1_src)
          (STEP_TGT: Local.program_step e_tgt lc1_tgt sc1_tgt mem1_tgt lc2_tgt sc2_tgt mem2_tgt):
      (exists e_src lc2_src sc2_src mem2_src,
          (<<STEP_SRC: OrdLocal.program_step L Ordering.na Ordering.plain 
                                             e_src lc1_src sc1_src mem1_src lc2_src sc2_src mem2_src>>) /\
          (<<EVENT: sim_event e_src e_tgt>>) /\
          (<<LC2: lc2_src = lc2_tgt>>) /\
          (<<SC2: sc2_src = sc2_tgt>>) /\
          (<<MEM2: sim_memory (Writes.append L e_src rels) mem2_src mem2_tgt>>) /\
          (<<NORMAL_TVIEW2: Normal.normal_tview L (Local.tview lc2_src)>>) /\
          (<<NORMAL_MEM2: Normal.normal_memory L mem2_src>>)) \/
      (<<RACE: RARaceW.ra_race L rels (Local.tview lc1_src) (ThreadEvent.get_program_event e_tgt)>>).
    Proof.
      inv STEP_TGT.
      - left. esplits; eauto. econs.
      - exploit read_step; eauto. i. des.
        + left. esplits; eauto. econs. ss.
        + right. left. ss. esplits; eauto.
      - exploit write_step; eauto. i. des.
        dup STEP_SRC. inv STEP_SRC0.
        exploit Normal.write_step; try exact STEP; eauto; ss. i. des.
        left. esplits; [econs 3|..]; eauto.
        eapply sim_memory_append; eauto.
      - exploit read_step; eauto. i. des; cycle 1.
        { right. left. esplits; ss; eauto. }
        dup STEP_SRC. inv STEP_SRC0.
        exploit Local.read_step_future; try exact STEP; eauto. i. des.
        exploit write_step; eauto. i. des.
        dup STEP_SRC0. inv STEP_SRC1.
        exploit Normal.write_step; try exact STEP0; eauto.
        { inv STEP. destruct releasedr; ss. eauto. }
        i. des.
        left. esplits; [econs 4|..]; eauto.
        eapply sim_memory_append; eauto.
      - left. esplits; [econs 5|..]; eauto.
        exploit Normal.fence_step; eauto.
      - left. esplits; [econs 6|..]; eauto.
        exploit Normal.fence_step; eauto.
      - left. esplits; [econs 7|..]; eauto.
      - destruct (L loc) eqn:LOC.
        + exploit write_na_step_loc; try exact LOCAL; eauto. i. des.
          exploit (@Normal.ord_program_step L Ordering.na Ordering.plain);
            try econs 8; eauto; ss. i. des.
          left. esplits; [econs 8|..]; eauto.
          unfold Writes.append. ss. condtac; ss.
        + exploit write_na_step_other; try exact LOCAL; eauto; try congr. i. des.
          exploit Normal.write_na_step; try exact STEP_SRC; eauto. i. des.
          left. esplits; [econs 8|..]; eauto.
          * econs; eauto. condtac; ss. eauto.
          * unfold Writes.append. ss. condtac; ss.
      - exploit racy_read_step; try exact LOCAL; eauto. i. des.
        + left. esplits; [econs 9|..]; eauto.
        + right. left. esplits; ss; eauto.
      - exploit racy_write_step; try exact LOCAL; eauto. i. des.
        + left. esplits; [econs 10|..]; eauto.
        + right. right. esplits; ss; eauto.
      - exploit racy_update_step; try exact LOCAL; eauto. i. des.
        + left. esplits; [econs 11|..]; eauto.
        + right. right. esplits; ss; eauto.
    Qed.
  End PFtoAPFSimThread.
End PFtoAPFSimThread.
