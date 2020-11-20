Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Single.

Require Import MemoryProps.

Lemma lower_max_ts mem1 mem0 loc from to msg0 msg1
      (INHABITED: Memory.inhabited mem0)
      (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
      loc0
  :
    Memory.max_ts loc0 mem1 = Memory.max_ts loc0 mem0.
Proof.
  hexploit Memory.lower_inhabited; eauto. intros INHABITED0.
  specialize (INHABITED loc0). specialize (INHABITED0 loc0).
  eapply Memory.max_ts_spec in INHABITED.
  eapply Memory.max_ts_spec in INHABITED0. des.
  eapply Memory.lower_get1 in GET0; eauto. des.
  erewrite Memory.lower_o in GET; eauto.
  eapply TimeFacts.antisym.
  - des_ifs.
    + ss. des; clarify. eapply Memory.lower_get0 in LOWER. des.
      eapply Memory.max_ts_spec; eauto.
    + eapply Memory.max_ts_spec; eauto.
  - eapply Memory.max_ts_spec; eauto.
Qed.

Lemma split_max_ts mem1 mem0 loc ts0 ts1 ts2 msg0 msg1
      (INHABITED: Memory.inhabited mem0)
      (SPLIT: Memory.split mem0 loc ts0 ts1 ts2 msg0 msg1 mem1)
      loc0
  :
    Memory.max_ts loc0 mem1 = Memory.max_ts loc0 mem0.
Proof.
  hexploit Memory.split_inhabited; eauto. intros INHABITED0.
  specialize (INHABITED loc0). specialize (INHABITED0 loc0).
  eapply Memory.max_ts_spec in INHABITED.
  eapply Memory.max_ts_spec in INHABITED0. des.
  eapply Memory.split_get1 in GET0; eauto. des.
  erewrite Memory.split_o in GET; eauto.
  eapply TimeFacts.antisym.
  - des_ifs.
    + ss. des; clarify.
      exploit split_succeed_wf; eauto. i. des.
      eapply Memory.split_get0 in SPLIT. des.
      eapply Memory.max_ts_spec in GET4. des.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt.
      { eapply TS23. }
      { eauto. }
    + ss. des; clarify. eapply Memory.split_get0 in SPLIT. des.
      eapply Memory.max_ts_spec; eauto.
    + eapply Memory.max_ts_spec; eauto.
  - eapply Memory.max_ts_spec; eauto.
Qed.

Lemma add_max_ts mem1 mem0 loc from to msg
      (INHABITED: Memory.inhabited mem0)
      (ADD: Memory.add mem0 loc from to msg mem1)
      loc0
  :
    Memory.max_ts loc0 mem1 =
    if (Loc.eq_dec loc0 loc)
    then Time.join to (Memory.max_ts loc0 mem0)
    else Memory.max_ts loc0 mem0.
Proof.
  hexploit Memory.add_inhabited; eauto. intros INHABITED0.
  specialize (INHABITED loc0). specialize (INHABITED0 loc0).
  eapply Memory.max_ts_spec in INHABITED.
  eapply Memory.max_ts_spec in INHABITED0. des.
  eapply Memory.add_get1 in GET0; eauto.
  des_ifs.
  { eapply TimeFacts.antisym.
    - erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. eapply Time.join_l.
      + etrans; [|eapply Time.join_r].
        eapply Memory.max_ts_spec; eauto.
    - eapply Time.join_spec.
      + eapply Memory.add_get0 in ADD. des.
        eapply Memory.max_ts_spec; eauto.
      + eapply Memory.max_ts_spec; eauto.
  }
  { erewrite Memory.add_o in GET; eauto. des_ifs.
    { ss. des; clarify. }
    eapply TimeFacts.antisym.
    - eapply Memory.max_ts_spec; eauto.
    - eapply Memory.max_ts_spec; eauto.
  }
Qed.


Lemma max_ts_maximal_covered mem (INHABITED: Memory.inhabited mem) loc:
  (Memory.max_ts loc mem = Time.bot /\ forall ts, ~ covered loc ts mem) \/
  (covered loc (Memory.max_ts loc mem) mem /\ forall ts (COVER: covered loc ts mem), Time.le ts (Memory.max_ts loc mem)).
Proof.
  destruct (Time.eq_dec (Memory.max_ts loc mem) Time.bot).
  { left. splits; auto. ii. inv H. inv ITV.
    eapply Memory.max_ts_spec in GET. des. ss.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    { eapply FROM. } etrans.
    { eapply TO. } etrans.
    { eapply MAX. }
    { rewrite e. eapply Time.bot_spec. }
  }
  { right. specialize (INHABITED loc).
    eapply Memory.max_ts_spec in INHABITED. des. splits.
    { econs; eauto. econs; ss; [|refl].
      eapply memory_get_ts_strong in GET. des; clarify. }
    { i. inv COVER. inv ITV. ss.
      eapply Memory.max_ts_spec in GET0. des. etrans; eauto. }
  }
Qed.


Module Shorter2.
  Inductive shorter_memory (mem_src mem_tgt: Memory.t): Prop :=
  | shorter_memory_contents
      (COVER: forall loc ts, covered loc ts mem_src <-> covered loc ts mem_tgt)
      (CONCRETE: forall loc to val released,
          (exists from_src, Memory.get loc to mem_src = Some (from_src, Message.concrete val released)) <->
          (exists from_tgt, Memory.get loc to mem_tgt = Some (from_tgt, Message.concrete val released)))
  .

  Lemma shorter_memory_closed_timemap mem_src mem_tgt tm
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_timemap tm mem_src <-> Memory.closed_timemap tm mem_tgt.
  Proof.
    unfold Memory.closed_timemap in *. split; i.
    { specialize (H loc). des.
      inv SHORTER. specialize (CONCRETE loc (tm loc) val released).
      des. exploit CONCRETE; eauto. i. des. eauto.
    }
    { specialize (H loc). des.
      inv SHORTER. specialize (CONCRETE loc (tm loc) val released).
      des. exploit CONCRETE0; eauto. i. des. eauto.
    }
  Qed.

  Lemma shorter_memory_inhabited mem_src mem_tgt
        (SHORTER: shorter_memory mem_src mem_tgt):
    Memory.inhabited mem_src <-> Memory.inhabited mem_tgt.
  Proof.
    inv SHORTER. split; ii.
    { specialize (H loc). specialize (CONCRETE loc Time.bot 0 None). des.
      exploit CONCRETE; eauto. i. des.
      erewrite x. f_equal. f_equal. eapply TimeFacts.antisym.
      { eapply memory_get_ts_le in x; eauto. }
      { eapply Time.bot_spec. }
    }
    { specialize (H loc). specialize (CONCRETE loc Time.bot 0 None). des.
      exploit CONCRETE0; eauto. i. des.
      erewrite x. f_equal. f_equal. eapply TimeFacts.antisym.
      { eapply memory_get_ts_le in x; eauto. }
      { eapply Time.bot_spec. }
    }
  Qed.

  Lemma shorter_memory_closed_view mem_src mem_tgt vw
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_view vw mem_src <-> Memory.closed_view vw mem_tgt.
  Proof.
    split; i.
    { inv H. econs.
      - erewrite <- shorter_memory_closed_timemap; eauto.
      - erewrite <- shorter_memory_closed_timemap; eauto.
    }
    { inv H. econs.
      - erewrite shorter_memory_closed_timemap; eauto.
      - erewrite shorter_memory_closed_timemap; eauto.
    }
  Qed.

  Lemma shorter_memory_closed_opt_view mem_src mem_tgt vw
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_opt_view vw mem_src <-> Memory.closed_opt_view vw mem_tgt.
  Proof.
    split; i.
    { inv H; econs.
      erewrite <- shorter_memory_closed_view; eauto.
    }
    { inv H; econs.
      erewrite shorter_memory_closed_view; eauto.
    }
  Qed.

  Lemma shorter_memory_closed_message mem_src mem_tgt msg
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_message msg mem_src <-> Memory.closed_message msg mem_tgt.
  Proof.
    split; i.
    { inv H; econs.
      erewrite <- shorter_memory_closed_opt_view; eauto.
    }
    { inv H; econs.
      erewrite shorter_memory_closed_opt_view; eauto.
    }
  Qed.

  Lemma shorter_memory_closed mem_src mem_tgt
        (SHORTER: shorter_memory mem_src mem_tgt):
    Memory.closed mem_src <-> Memory.closed mem_tgt.
  Proof.
    split; i.
    - inv H. econs.
      + i. destruct msg as [val released|].
        * dup SHORTER. inv SHORTER.
          specialize (CONCRETE loc to val released). des.
          exploit CONCRETE0; eauto. i. des.
          exploit CLOSED; eauto. i. des. esplits; eauto.
          erewrite <- shorter_memory_closed_message; eauto.
        * splits; eauto. econs.
      + erewrite <- shorter_memory_inhabited; eauto.
    - inv H. econs.
      + i. destruct msg as [val released|].
        * dup SHORTER. inv SHORTER.
          specialize (CONCRETE loc to val released). des.
          exploit CONCRETE; eauto. i. des.
          exploit CLOSED; eauto. i. des. esplits; eauto.
          erewrite shorter_memory_closed_message; eauto.
        * splits; eauto. econs.
      + erewrite shorter_memory_inhabited; eauto.
  Qed.

  Lemma shorter_memory_max_concrete_ts mem_src mem_tgt loc ts
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.max_concrete_ts mem_src loc ts <->
      Memory.max_concrete_ts mem_tgt loc ts.
  Proof.
    split; i.
    - inv H. econs.
      + des. inv SHORTER.
        specialize (CONCRETE loc ts val released). des.
        exploit CONCRETE; eauto. i. des. eauto.
      + i. inv SHORTER.
        specialize (CONCRETE loc to val' released'). des.
        exploit CONCRETE0; eauto. i. des. eauto.
    - inv H. econs.
      + des. inv SHORTER.
        specialize (CONCRETE loc ts val released). des.
        exploit CONCRETE0; eauto. i. des. eauto.
      + i. inv SHORTER.
        specialize (CONCRETE loc to val' released'). des.
        exploit CONCRETE; eauto. i. des. eauto.
  Qed.

  Lemma shorter_memory_max_concrete_timemap mem_src mem_tgt tm
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.max_concrete_timemap mem_src tm <->
      Memory.max_concrete_timemap mem_tgt tm.
  Proof.
    split; ii.
    - erewrite <- shorter_memory_max_concrete_ts; eauto.
    - erewrite shorter_memory_max_concrete_ts; eauto.
  Qed.

  Lemma shorter_memory_add mem_src0 mem_tgt0 mem_tgt1 loc from to msg
        (ADD: Memory.add mem_tgt0 loc from to msg mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      exists mem_src1,
        (<<ADD: Memory.add mem_src0 loc from to msg mem_src1>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    exploit add_succeed_wf; eauto. i. des.
    exploit (@Memory.add_exists mem_src0 loc from to msg); eauto.
    { ii. inv SHORTER. hexploit (proj1 (COVER loc x)); eauto.
      { econs; eauto. }
      i. inv H. eapply DISJOINT; eauto.
    }
    { i. des. esplits; eauto. econs.
      { i. erewrite (@add_covered mem_tgt1 mem_tgt0); eauto.
        erewrite (@add_covered mem2 mem_src0); eauto.
        inv SHORTER. erewrite (COVER loc0 ts). auto.
      }
      { i. erewrite (@Memory.add_o mem2 mem_src0); eauto.
        erewrite (@Memory.add_o mem_tgt1 mem_tgt0); eauto. des_ifs.
        eapply SHORTER; eauto.
      }
    }
  Qed.

  Lemma shorter_memory_lower mem_src0 mem_tgt0 mem_src1 mem_tgt1 loc from to msg0 msg1
        (LOWERSRC: Memory.lower mem_src0 loc from to msg0 msg1 mem_src1)
        (LOWERTGT: Memory.lower mem_tgt0 loc from to msg0 msg1 mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      shorter_memory mem_src1 mem_tgt1.
  Proof.
    econs.
    - i. erewrite (@lower_covered mem_tgt1 mem_tgt0); eauto.
      erewrite (@lower_covered mem_src1 mem_src0); eauto.
      eapply SHORTER; eauto.
    - i. erewrite (@Memory.lower_o mem_src1 mem_src0); eauto.
      erewrite (@Memory.lower_o mem_tgt1 mem_tgt0); eauto. des_ifs.
      eapply SHORTER.
  Qed.

  Lemma shorter_memory_split mem_src0 mem_tgt0 mem_src1 mem_tgt1 loc ts0 ts1 ts2 msg0 msg1
        (SPLITSRC: Memory.split mem_src0 loc ts0 ts1 ts2 msg0 msg1 mem_src1)
        (SPLITTGT: Memory.split mem_tgt0 loc ts0 ts1 ts2 msg0 msg1 mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      shorter_memory mem_src1 mem_tgt1.
  Proof.
    econs.
    - i. erewrite (@split_covered mem_tgt1 mem_tgt0); eauto.
      erewrite (@split_covered mem_src1 mem_src0); eauto.
      eapply SHORTER; eauto.
    - i. erewrite (@Memory.split_o mem_src1 mem_src0); eauto.
      erewrite (@Memory.split_o mem_tgt1 mem_tgt0); eauto. des_ifs.
      eapply SHORTER; eauto.
  Qed.

  Lemma shorter_memory_remove mem_src0 mem_tgt0 mem_src1 mem_tgt1 loc from to msg
        (SPLITSRC: Memory.remove mem_src0 loc from to msg mem_src1)
        (SPLITTGT: Memory.remove mem_tgt0 loc from to msg mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      shorter_memory mem_src1 mem_tgt1.
  Proof.
    econs.
    - i. erewrite (@remove_covered mem_tgt1 mem_tgt0); eauto.
      erewrite (@remove_covered mem_src1 mem_src0); eauto.
      inv SHORTER. erewrite (COVER loc0 ts); eauto.
    - i. erewrite (@Memory.remove_o mem_src1 mem_src0); eauto.
      erewrite (@Memory.remove_o mem_tgt1 mem_tgt0); eauto. des_ifs.
      eapply SHORTER; eauto.
  Qed.

  Lemma shorter_memory_get mem_src mem_tgt loc from_tgt to val released
        (SHORTER: shorter_memory mem_src mem_tgt)
        (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.concrete val released))
    :
      exists from_src,
        (<<GET: Memory.get loc to mem_src = Some (from_src, Message.concrete val released)>>).
  Proof.
    inv SHORTER. specialize (CONCRETE loc to val released).
    rewrite GET in *. eapply CONCRETE; eauto.
  Qed.

  Lemma shorter_memory_promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind mem_src0
        (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le prom0 mem_src0)
    :
      exists mem_src1,
        (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv PROMISE.
    - exploit shorter_memory_add; eauto. i. des.
      exists mem_src1. esplits.
      + econs 1; eauto. i. clarify.
        exploit add_succeed_wf; try apply MEM. i. des.
        exploit (@closed_point mem_tgt0 loc to to').
        { eapply memory_get_ts_strong in GET. des; clarify. inv TO1. }
        { i. eapply SHORTER. econs; eauto. }
        i. des. inv TS0.
        { eapply DISJOINT.
          - eapply GET0.
          - econs; [|refl]; ss.
          - econs; ss. left. auto.
        }
        { inv H. eapply ATTACH; eauto. }
      + eauto.
    - exploit Memory.split_exists_le; eauto. i. des.
      exists mem2. esplits.
      + econs 2; eauto.
      + eapply shorter_memory_split; eauto.
    - exploit Memory.lower_exists_le; eauto. i. des.
      exists mem2. esplits.
      + econs 3; eauto.
      + eapply shorter_memory_lower; eauto.
    - exploit Memory.remove_exists_le; eauto. i. des.
      exists mem2. esplits.
      + econs 4; eauto.
      + eapply shorter_memory_remove; eauto.
  Qed.

  Lemma shorter_memory_write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind mem_src0
        (WRITE: Memory.write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le prom0 mem_src0)
    :
      exists mem_src1,
        (<<WRITE: Memory.write prom0 mem_src0 loc from to val released prom1 mem_src1 kind>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv WRITE. exploit shorter_memory_promise; eauto.
    i. des. esplits; eauto.
  Qed.

  Lemma shorter_memory_local_read_step lc0 mem_tgt loc to val released ordr lc1 mem_src
        (READ: Local.read_step lc0 mem_tgt loc to val released ordr lc1)
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Local.read_step lc0 mem_src loc to val released ordr lc1.
  Proof.
    inv READ. eapply shorter_memory_get in GET; eauto. des. eauto.
  Qed.

  Lemma shorter_memory_local_write_step lc0 sc0 mem_tgt0 loc from to val releasedr releasedw ord lc1 sc1 mem_tgt1 kind mem_src0
        (WRITE: Local.write_step lc0 sc0 mem_tgt0 loc from to val releasedr releasedw ord lc1 sc1 mem_tgt1 kind)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le lc0.(Local.promises) mem_src0)
    :
      exists mem_src1,
        (<<WRITE: Local.write_step lc0 sc0 mem_src0 loc from to val releasedr releasedw ord lc1 sc1 mem_src1 kind>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv WRITE. exploit shorter_memory_write; eauto. i. des. esplits; eauto.
  Qed.

  Lemma shorter_memory_thread_step lang st0 st1 lc0 lc1 sc0 sc1 mem_tgt0 mem_tgt1 mem_src0 pf e
        (STEP: Thread.step pf e (Thread.mk lang st0 lc0 sc0 mem_tgt0) (Thread.mk _ st1 lc1 sc1 mem_tgt1))
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le lc0.(Local.promises) mem_src0)
    :
      exists mem_src1,
        (<<STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 mem_src0) (Thread.mk _ st1 lc1 sc1 mem_src1)>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv STEP.
    - inv STEP0. inv LOCAL. exploit shorter_memory_promise; eauto. i. des.
      esplits; eauto. econs 1; eauto. econs; eauto. econs; eauto.
      erewrite shorter_memory_closed_message; eauto.
    - inv STEP0. inv LOCAL.
      + esplits; eauto.
      + exploit shorter_memory_local_read_step; eauto. i.
        esplits; eauto.
      + exploit shorter_memory_local_write_step; eauto. i. des.
        esplits; eauto.
      + exploit shorter_memory_local_read_step; eauto. i.
        exploit shorter_memory_local_write_step; eauto.
        { inv LOCAL1. ss. } i. des.
        esplits; eauto.
      + esplits; eauto.
      + esplits; eauto.
      + esplits; eauto.
  Qed.

  Lemma shorter_memory_thread_steps lang st0 st1 lc0 lc1 sc0 sc1 mem_tgt0 mem_tgt1 mem_src0
        (STEPS: rtc (@Thread.tau_step _) (Thread.mk lang st0 lc0 sc0 mem_tgt0) (Thread.mk _ st1 lc1 sc1 mem_tgt1))
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le lc0.(Local.promises) mem_src0)
    :
      exists mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st0 lc0 sc0 mem_src0) (Thread.mk _ st1 lc1 sc1 mem_src1)>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    remember (Thread.mk lang st0 lc0 sc0 mem_tgt0).
    remember (Thread.mk lang st1 lc1 sc1 mem_tgt1). ginduction STEPS.
    { i. clarify. esplits; eauto. }
    { i. clarify. inv H. inv TSTEP. destruct y.
      exploit shorter_memory_thread_step; eauto. i. des.
      exploit IHSTEPS; eauto.
      { eapply step_memory_le in STEP0; eauto. } i. des.
      esplits; eauto. econs; eauto. econs; eauto. econs; eauto.
    }
  Qed.

End Shorter2.

Module Shorter.
  Definition shorter_memory (mem_src mem_tgt: Memory.t): Prop :=
    forall loc to,
      match (Memory.get loc to mem_src), (Memory.get loc to mem_tgt) with
      | None, None => True
      | Some (from_src, msg_src), Some (from_tgt, msg_tgt) =>
        msg_src = msg_tgt /\ Time.le from_tgt from_src
      | _, _ => False
      end
  .

  Lemma shorter_memory_closed_timemap mem_src mem_tgt tm
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_timemap tm mem_src <-> Memory.closed_timemap tm mem_tgt.
  Proof.
    unfold Memory.closed_timemap in *. split; i.
    { specialize (H loc). des.
      specialize (SHORTER loc (tm loc)). rewrite H in *. des_ifs.
      des; clarify. eauto.
    }
    { specialize (H loc). des.
      specialize (SHORTER loc (tm loc)). rewrite H in *. des_ifs.
      des; clarify. eauto.
    }
  Qed.

  Lemma shorter_memory_inhabited mem_src mem_tgt
        (SHORTER: shorter_memory mem_src mem_tgt):
    Memory.inhabited mem_src <-> Memory.inhabited mem_tgt.
  Proof.
    split; ii.
    { specialize (H loc). specialize (SHORTER loc Time.bot).
      rewrite H in *. des_ifs. des; clarify.
      inv SHORTER0; inv H0. eauto.
    }
    { specialize (H loc). specialize (SHORTER loc Time.bot).
      rewrite H in *. des_ifs. des; clarify.
      eapply memory_get_ts_le in Heq. inv Heq; inv H0. eauto.
    }
  Qed.

  Lemma shorter_memory_closed_view mem_src mem_tgt vw
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_view vw mem_src <-> Memory.closed_view vw mem_tgt.
  Proof.
    split; i.
    { inv H. econs.
      - erewrite <- shorter_memory_closed_timemap; eauto.
      - erewrite <- shorter_memory_closed_timemap; eauto.
    }
    { inv H. econs.
      - erewrite shorter_memory_closed_timemap; eauto.
      - erewrite shorter_memory_closed_timemap; eauto.
    }
  Qed.

  Lemma shorter_memory_closed_opt_view mem_src mem_tgt vw
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_opt_view vw mem_src <-> Memory.closed_opt_view vw mem_tgt.
  Proof.
    split; i.
    { inv H; econs.
      erewrite <- shorter_memory_closed_view; eauto.
    }
    { inv H; econs.
      erewrite shorter_memory_closed_view; eauto.
    }
  Qed.

  Lemma shorter_memory_closed_message mem_src mem_tgt msg
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.closed_message msg mem_src <-> Memory.closed_message msg mem_tgt.
  Proof.
    split; i.
    { inv H; econs.
      erewrite <- shorter_memory_closed_opt_view; eauto.
    }
    { inv H; econs.
      erewrite shorter_memory_closed_opt_view; eauto.
    }
  Qed.

  Lemma shorter_memory_closed mem_src mem_tgt
        (SHORTER: shorter_memory mem_src mem_tgt):
    Memory.closed mem_src <-> Memory.closed mem_tgt.
  Proof.
    split; i.
    - inv H. econs.
      + i. destruct msg as [val released|].
        * dup SHORTER.
          specialize (SHORTER loc to). rewrite MSG in *. des_ifs.
          des; clarify. eapply CLOSED in Heq. des. esplits; eauto.
          erewrite <- shorter_memory_closed_message; eauto.
        * splits; eauto. econs.
      + erewrite <- shorter_memory_inhabited; eauto.
    - inv H. econs.
      + i. destruct msg as [val released|].
        * dup SHORTER.
          specialize (SHORTER loc to). rewrite MSG in *. des_ifs.
          des; clarify. eapply CLOSED in Heq. des. esplits; eauto.
          erewrite shorter_memory_closed_message; eauto.
        * splits; eauto. econs.
      + erewrite shorter_memory_inhabited; eauto.
  Qed.

  Lemma shorter_memory_max_concrete_ts mem_src mem_tgt loc ts
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.max_concrete_ts mem_src loc ts <->
      Memory.max_concrete_ts mem_tgt loc ts.
  Proof.
    split; i.
    - inv H. econs.
      + des. specialize (SHORTER loc ts).
        unfold Memory.get in SHORTER.
        rewrite GET in SHORTER. des_ifs. des; clarify. eauto.
      + i. des. specialize (SHORTER loc to).
        unfold Memory.get in SHORTER.
        rewrite GET0 in SHORTER. des_ifs. des; clarify. eapply MAX; eauto.
    - inv H. econs.
      + des. specialize (SHORTER loc ts).
        unfold Memory.get in SHORTER.
        rewrite GET in SHORTER. des_ifs. des; clarify. eauto.
      + i. des. specialize (SHORTER loc to).
        unfold Memory.get in SHORTER.
        rewrite GET0 in SHORTER. des_ifs. des; clarify. eapply MAX; eauto.
  Qed.

  Lemma shorter_memory_max_concrete_timemap mem_src mem_tgt tm
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Memory.max_concrete_timemap mem_src tm <->
      Memory.max_concrete_timemap mem_tgt tm.
  Proof.
    split; ii.
    - erewrite <- shorter_memory_max_concrete_ts; eauto.
    - erewrite shorter_memory_max_concrete_ts; eauto.
  Qed.

  Lemma shorter_memory_max_ts mem_src mem_tgt
        (SHORTER: shorter_memory mem_src mem_tgt)
        (INHABITED: Memory.inhabited mem_tgt)
        loc
    :
      Memory.max_ts loc mem_src = Memory.max_ts loc mem_tgt.
  Proof.
    dup INHABITED. eapply shorter_memory_inhabited in INHABITED0; eauto.
    specialize (INHABITED loc). specialize (INHABITED0 loc).
    eapply Memory.max_ts_spec in INHABITED. des.
    eapply Memory.max_ts_spec in INHABITED0. des.
    set (SHORTER loc (Memory.max_ts loc mem_src)).
    rewrite GET0 in *.
    set (SHORTER loc (Memory.max_ts loc mem_tgt)).
    rewrite GET in *. des_ifs. des; clarify.
    eapply TimeFacts.antisym.
    { eapply Memory.max_ts_spec; eauto. }
    { eapply Memory.max_ts_spec; eauto. }
  Qed.

  Lemma shorter_memory_add mem_src0 mem_tgt0 mem_tgt1 loc from to msg
        (ADD: Memory.add mem_tgt0 loc from to msg mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      exists mem_src1,
        (<<ADD: Memory.add mem_src0 loc from to msg mem_src1>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    exploit add_succeed_wf; eauto. i. des.
    exploit (@Memory.add_exists mem_src0 loc from to msg); eauto.
    { ii. specialize (SHORTER loc to2).
      rewrite GET2 in *. des_ifs. des; clarify.
      eapply DISJOINT; eauto. inv RHS.
      econs; eauto. ss. eapply TimeFacts.le_lt_lt; eauto.
    }
    { i. des. esplits; eauto. ii.
      erewrite (@Memory.add_o mem2 mem_src0); eauto.
      erewrite (@Memory.add_o mem_tgt1 mem_tgt0); eauto. des_ifs.
      { ss. des; clarify. split; auto. refl. }
      { specialize (SHORTER loc0 to0).
        rewrite Heq in *. rewrite Heq0 in *. ss. }
      { specialize (SHORTER loc0 to0).
        rewrite Heq in *. rewrite Heq0 in *. ss. }
      { specialize (SHORTER loc0 to0).
        rewrite Heq in *. rewrite Heq0 in *. ss. }
    }
  Qed.

  Lemma shorter_memory_lower mem_src0 mem_tgt0 mem_src1 mem_tgt1 loc from to msg0 msg1
        (LOWERSRC: Memory.lower mem_src0 loc from to msg0 msg1 mem_src1)
        (LOWERTGT: Memory.lower mem_tgt0 loc from to msg0 msg1 mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      shorter_memory mem_src1 mem_tgt1.
  Proof.
    ii. erewrite (@Memory.lower_o mem_src1 mem_src0); eauto.
    erewrite (@Memory.lower_o mem_tgt1 mem_tgt0); eauto. des_ifs.
    { ss. des; clarify. split; auto. refl. }
    { specialize (SHORTER loc0 to0).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
    { specialize (SHORTER loc0 to0).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
    { specialize (SHORTER loc0 to0).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
  Qed.

  Lemma shorter_memory_split mem_src0 mem_tgt0 mem_src1 mem_tgt1 loc ts0 ts1 ts2 msg0 msg1
        (SPLITSRC: Memory.split mem_src0 loc ts0 ts1 ts2 msg0 msg1 mem_src1)
        (SPLITTGT: Memory.split mem_tgt0 loc ts0 ts1 ts2 msg0 msg1 mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      shorter_memory mem_src1 mem_tgt1.
  Proof.
    ii. erewrite (@Memory.split_o mem_src1 mem_src0); eauto.
    erewrite (@Memory.split_o mem_tgt1 mem_tgt0); eauto. des_ifs.
    { ss. des; clarify. split; auto. refl. }
    { ss. des; clarify. split; auto. refl. }
    { specialize (SHORTER loc0 to).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
    { specialize (SHORTER loc0 to).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
    { specialize (SHORTER loc0 to).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
  Qed.

  Lemma shorter_memory_remove mem_src0 mem_tgt0 mem_src1 mem_tgt1 loc from to msg
        (REMOVESRC: Memory.remove mem_src0 loc from to msg mem_src1)
        (REMOVETGT: Memory.remove mem_tgt0 loc from to msg mem_tgt1)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
    :
      shorter_memory mem_src1 mem_tgt1.
  Proof.
    ii. erewrite (@Memory.remove_o mem_src1 mem_src0); eauto.
    erewrite (@Memory.remove_o mem_tgt1 mem_tgt0); eauto. des_ifs.
    { specialize (SHORTER loc0 to0).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
    { specialize (SHORTER loc0 to0).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
    { specialize (SHORTER loc0 to0).
      rewrite Heq in *. rewrite Heq0 in *. ss. }
  Qed.

  Lemma shorter_memory_get mem_src mem_tgt loc from_tgt to val released
        (SHORTER: shorter_memory mem_src mem_tgt)
        (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.concrete val released))
    :
      exists from_src,
        (<<GET: Memory.get loc to mem_src = Some (from_src, Message.concrete val released)>>).
  Proof.
    specialize (SHORTER loc to). rewrite GET in *.
    des_ifs. des; clarify. eauto.
  Qed.

  Lemma shorter_memory_promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind mem_src0
        (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le prom0 mem_src0)
    :
      exists mem_src1,
        (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv PROMISE.
    - exploit shorter_memory_add; eauto. i. des.
      exists mem_src1. esplits.
      + econs 1; eauto. i.
        specialize (SHORTER loc to'). rewrite GET in *. des_ifs. des; clarify.
        inv SHORTER1.
        * exploit Memory.get_disjoint.
          { eapply Memory.add_get1; [eapply MEM|eapply Heq]. }
          { eapply Memory.add_get0; eauto. }
          i. des; clarify.
          { eapply Memory.add_get0 in MEM. des. clarify. }
          { eapply x0.
            { instantiate (1:=to). econs; ss.
              eapply memory_get_ts_le in GET. auto. }
            { econs; ss; [|refl].
              eapply add_succeed_wf in MEM. des. auto. }
          }
        * inv H. exploit ATTACH; eauto.
      + eauto.
    - exploit Memory.split_exists_le; eauto. i. des.
      exists mem2. esplits.
      + econs 2; eauto.
      + eapply shorter_memory_split; eauto.
    - exploit Memory.lower_exists_le; eauto. i. des.
      exists mem2. esplits.
      + econs 3; eauto.
      + eapply shorter_memory_lower; eauto.
    - exploit Memory.remove_exists_le; eauto. i. des.
      exists mem2. esplits.
      + econs 4; eauto.
      + eapply shorter_memory_remove; eauto.
  Qed.

  Lemma shorter_memory_write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind mem_src0
        (WRITE: Memory.write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le prom0 mem_src0)
    :
      exists mem_src1,
        (<<WRITE: Memory.write prom0 mem_src0 loc from to val released prom1 mem_src1 kind>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv WRITE. exploit shorter_memory_promise; eauto.
    i. des. esplits; eauto.
  Qed.

  Lemma shorter_memory_local_read_step lc0 mem_tgt loc to val released ordr lc1 mem_src
        (READ: Local.read_step lc0 mem_tgt loc to val released ordr lc1)
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      Local.read_step lc0 mem_src loc to val released ordr lc1.
  Proof.
    inv READ. eapply shorter_memory_get in GET; eauto. des. eauto.
  Qed.

  Lemma shorter_memory_local_write_step lc0 sc0 mem_tgt0 loc from to val releasedr releasedw ord lc1 sc1 mem_tgt1 kind mem_src0
        (WRITE: Local.write_step lc0 sc0 mem_tgt0 loc from to val releasedr releasedw ord lc1 sc1 mem_tgt1 kind)
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le lc0.(Local.promises) mem_src0)
    :
      exists mem_src1,
        (<<WRITE: Local.write_step lc0 sc0 mem_src0 loc from to val releasedr releasedw ord lc1 sc1 mem_src1 kind>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv WRITE. exploit shorter_memory_write; eauto. i. des. esplits; eauto.
  Qed.

  Lemma shorter_memory_thread_step lang st0 st1 lc0 lc1 sc0 sc1 mem_tgt0 mem_tgt1 mem_src0 pf e
        (STEP: Thread.step pf e (Thread.mk lang st0 lc0 sc0 mem_tgt0) (Thread.mk _ st1 lc1 sc1 mem_tgt1))
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le lc0.(Local.promises) mem_src0)
    :
      exists mem_src1,
        (<<STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 mem_src0) (Thread.mk _ st1 lc1 sc1 mem_src1)>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    inv STEP.
    - inv STEP0. inv LOCAL. exploit shorter_memory_promise; eauto. i. des.
      esplits; eauto. econs 1; eauto. econs; eauto. econs; eauto.
      erewrite shorter_memory_closed_message; eauto.
    - inv STEP0. inv LOCAL.
      + esplits; eauto.
      + exploit shorter_memory_local_read_step; eauto. i.
        esplits; eauto.
      + exploit shorter_memory_local_write_step; eauto. i. des.
        esplits; eauto.
      + exploit shorter_memory_local_read_step; eauto. i.
        exploit shorter_memory_local_write_step; eauto.
        { inv LOCAL1. ss. } i. des.
        esplits; eauto.
      + esplits; eauto.
      + esplits; eauto.
      + esplits; eauto.
  Qed.

  Lemma shorter_memory_thread_steps lang st0 st1 lc0 lc1 sc0 sc1 mem_tgt0 mem_tgt1 mem_src0
        (STEPS: rtc (@Thread.tau_step _) (Thread.mk lang st0 lc0 sc0 mem_tgt0) (Thread.mk _ st1 lc1 sc1 mem_tgt1))
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (MLE: Memory.le lc0.(Local.promises) mem_src0)
    :
      exists mem_src1,
        (<<STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st0 lc0 sc0 mem_src0) (Thread.mk _ st1 lc1 sc1 mem_src1)>>) /\
        (<<SHORTER: shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    remember (Thread.mk lang st0 lc0 sc0 mem_tgt0).
    remember (Thread.mk lang st1 lc1 sc1 mem_tgt1). ginduction STEPS.
    { i. clarify. esplits; eauto. }
    { i. clarify. inv H. inv TSTEP. destruct y.
      exploit shorter_memory_thread_step; eauto. i. des.
      exploit IHSTEPS; eauto.
      { eapply step_memory_le in STEP0; eauto. } i. des.
      esplits; eauto. econs; eauto. econs; eauto. econs; eauto.
    }
  Qed.

  Lemma shorter_memory_cap mem_src0 mem_tgt0 mem_src1
        (SHORTER: shorter_memory mem_src0 mem_tgt0)
        (CAP: Memory.cap mem_src0 mem_src1)
        (CLOSED: Memory.closed mem_tgt0)
    :
      exists mem_tgt1,
        (<<CAP: Memory.cap mem_tgt0 mem_tgt1>>) /\
        (<<SHORTER: Shorter2.shorter_memory mem_src1 mem_tgt1>>).
  Proof.
    exploit Memory.cap_exists; eauto. i. des.
    esplits; eauto. econs.
    { i. erewrite <- (@memory_cap_covered mem_tgt0 mem2); eauto.
      erewrite <- (@memory_cap_covered mem_src0); eauto.
      2: { eapply shorter_memory_closed; eauto. }
      erewrite shorter_memory_max_ts; eauto. eapply CLOSED.
    }
    { i. split; i.
      - des. eapply (@Memory.cap_inv mem_src0 mem_src1) in H; eauto.
        { des; clarify. specialize (SHORTER loc to).
          rewrite H in *. des_ifs. des; clarify.
          eapply CAP0 in Heq. eauto.
        }
        { eapply shorter_memory_closed; eauto. }
      - des. eapply (@Memory.cap_inv mem_tgt0 mem2) in H; eauto.
        { des; clarify. specialize (SHORTER loc to).
          rewrite H in *. des_ifs. des; clarify.
          eapply CAP in Heq. eauto.
        }
    }
  Qed.

  Lemma shorter_memory_consistent lang st lc sc mem_tgt mem_src
        (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc mem_tgt))
        (SHORTER: shorter_memory mem_src mem_tgt)
        (MLE: Memory.le lc.(Local.promises) mem_src)
        (CLOSED: Memory.closed mem_tgt)
    :
      Thread.consistent (Thread.mk lang st lc sc mem_src).
  Proof.
    ii. exploit shorter_memory_cap; eauto. i. des.
    exploit CONSISTENT; eauto.
    { erewrite <- Shorter2.shorter_memory_max_concrete_timemap; eauto. }
    i. des.
    { left. unfold Thread.steps_failure in *. des. destruct e2.
      eapply Shorter2.shorter_memory_thread_steps in STEPS; eauto.
      2: { etrans; eauto. eapply CAP. }
      des. inv FAILURE0; inv STEP. inv LOCAL.
      esplits; eauto.
    }
    { right. destruct e2.
      eapply Shorter2.shorter_memory_thread_steps in STEPS; eauto.
      2: { etrans; eauto. eapply CAP. }
      des. esplits; eauto.
    }
  Qed.

  Inductive shorter_configuration: Configuration.t -> Configuration.t -> Prop :=
  | shorter_configuration_intro
      ths sc mem_src mem_tgt
      (MEM: shorter_memory mem_src mem_tgt)
    :
      shorter_configuration (Configuration.mk ths sc mem_src) (Configuration.mk ths sc mem_tgt).

  Lemma shorter_configuration_step c_src0 c_tgt0 c_tgt1 e tid
        (STEP: Configuration.step e tid c_tgt0 c_tgt1)
        (SHORTER: shorter_configuration c_src0 c_tgt0)
        (WFSRC: Configuration.wf c_src0)
        (WFTGT: Configuration.wf c_tgt0)
    :
      exists c_src1,
        (<<STEP: Configuration.step e tid c_src0 c_src1>>) /\
        (<<SHORTER: shorter_configuration c_src1 c_tgt1>>).
  Proof.
    inv SHORTER. inv STEP; ss.
    - exploit Thread.rtc_tau_step_future; eauto; try by (eapply WFTGT; eauto).
      i. des. destruct e2. ss.
      exploit Thread.step_future; eauto. i. des. ss.
      exploit shorter_memory_thread_steps; eauto.
      { eapply WFSRC; eauto. } i. des.
      exploit Thread.rtc_tau_step_future; eauto; try by (eapply WFSRC; eauto).
      i. des. ss.
      exploit shorter_memory_thread_step; eauto.
      { eapply WF1. } i. des.
      exploit Thread.step_future; eauto. i. des. ss.
      esplits.
      + econs 1; eauto.
      + econs; eauto.
    - exploit Thread.rtc_tau_step_future; eauto; try by (eapply WFTGT; eauto).
      i. des. destruct e2. ss.
      exploit Thread.step_future; eauto. i. des. ss.
      exploit shorter_memory_thread_steps; eauto.
      { eapply WFSRC; eauto. } i. des.
      exploit Thread.rtc_tau_step_future; eauto; try by (eapply WFSRC; eauto).
      i. des. ss.
      exploit shorter_memory_thread_step; eauto.
      { eapply WF1. } i. des.
      exploit Thread.step_future; eauto. i. des. ss.
      esplits.
      + econs 2; eauto. eapply shorter_memory_consistent; eauto. eapply WF3.
      + econs; eauto.
  Qed.

  Lemma shorter_configuration_behavior c_src c_tgt
        (SHORTER: shorter_configuration c_src c_tgt)
        (WFSRC: Configuration.wf c_src)
        (WFTGT: Configuration.wf c_tgt)
    :
      behaviors SConfiguration.machine_step c_tgt <1=
      behaviors SConfiguration.machine_step c_src.
  Proof.
    ii. eapply SConfiguration.multi_step_equiv; eauto.
    eapply SConfiguration.multi_step_equiv in PR; eauto.
    ginduction PR.
    - i. econs 1; eauto. inv SHORTER. auto.
    - i. exploit shorter_configuration_step; eauto. i. des.
      exploit Configuration.step_future; try apply STEP; auto. i. des.
      exploit Configuration.step_future; try apply STEP0; auto. i. des.
      econs 2; eauto.
    - i. exploit shorter_configuration_step; eauto. i. des.
      econs 3; eauto.
    - i. exploit shorter_configuration_step; eauto. i. des.
      exploit Configuration.step_future; try apply STEP; auto. i. des.
      exploit Configuration.step_future; try apply STEP0; auto. i. des.
      econs 4; eauto.
  Qed.

End Shorter.
