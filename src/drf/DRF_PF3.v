Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.
Require Import ReorderPromises2.
Require Import AbortProp.

Require Import DRF_PF.

Require Import PFConsistent.

Set Implicit Arguments.



Definition wf_time_evt (P: Loc.t -> Time.t -> Prop) (e: ThreadEvent.t) : Prop :=
  match e with
  | ThreadEvent.promise loc from to msg kind =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.write loc from to val released ordw =>
    (<<FROM: P loc from>>) /\ (<<TO: P loc to>>)
  | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
    (<<TO: P loc to>>)
  | _ => True
  end.

Lemma wf_time_evt_mon P0 P1
      (LE: P0 <2= P1)
  :
    wf_time_evt P0 <1= wf_time_evt P1.
Proof.
  ii. unfold wf_time_evt in *. des_ifs; des; splits; eauto.
Qed.

Lemma step_times_list_exists P lang th0 th1 e
      (STEPS: (@pred_step P lang) e th0 th1)
  :
    exists times,
      (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang) e th0 th1.
Proof.
  inv STEPS. destruct e.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun l => if Loc.eq_dec l loc then
                       [from; to] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun l => if Loc.eq_dec l loc then
                       [tsw] else []).
    econs; eauto.
    ss. splits; auto; des_ifs; ss; eauto.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
  - exists (fun _ => []). econs; eauto. ss.
Qed.

Lemma times_list_exists P lang th0 th1
      (STEPS: rtc (tau (@pred_step P lang)) th0 th1)
  :
    exists times,
      rtc (tau (@pred_step (P /1\ wf_time_evt (fun loc to => List.In to (times loc))) lang)) th0 th1.
Proof.
  ginduction STEPS.
  - exists (fun _ => []). refl.
  - dup H. inv H0.
    eapply step_times_list_exists in TSTEP. des.
    exists (fun loc => times loc ++ times0 loc). econs 2.
    + econs; eauto. eapply pred_step_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
    + eapply pred_step_rtc_mon; eauto.
      i. ss. des. split; auto.
      eapply wf_time_evt_mon; eauto.
      i. ss. eapply List.in_or_app; eauto.
Qed.

Inductive add_cap (caps: Loc.t -> option (Time.t * Time.t * Message.t)): Memory.t -> Memory.t -> Prop :=
| add_cap_refl mem0
  :
    add_cap caps mem0 mem0
| add_cap_add
    loc from to msg mem0 mem1
    (CAP: caps loc = Some (from, to, msg))
    (ADD: Memory.add mem0 loc from to msg mem1)
  :
    add_cap caps mem0 mem1
.
Hint Constructors add_cap.

Lemma memory_op_le mem_src0 mem_tgt0 loc from to msg mem_src1 mem_tgt1 kind
      (MLE: Memory.le mem_src0 mem_tgt0)
      (OPSRC: Memory.op mem_src0 loc from to msg mem_src1 kind)
      (OPTGT: Memory.op mem_tgt0 loc from to msg mem_tgt1 kind)
  :
    Memory.le mem_src1 mem_tgt1.
Proof.
  inv OPSRC; inv OPTGT.
  - ii. erewrite Memory.add_o in LHS; eauto.
    erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.split_o in LHS; eauto.
    erewrite Memory.split_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.lower_o in LHS; eauto.
    erewrite Memory.lower_o; cycle 1; eauto. des_ifs; eauto.
  - ii. erewrite Memory.remove_o in LHS; eauto.
    erewrite Memory.remove_o; cycle 1; eauto. des_ifs; eauto.
Qed.

Inductive diff_after_promises (caps: Loc.t -> option (Time.t * Time.t * Message.t))
          (prom mem0 mem1: Memory.t): Prop :=
| diff_after_promises_intro
    (MLE: Memory.le mem0 mem1)

    (DIFF: forall loc to from msg
                  (GET: Memory.get loc to mem1 = Some (from, msg))
                  (NONE: Memory.get loc to mem0 = None),
        caps loc = Some (from, to, msg))

    (CAPS: forall loc to from msg
                  (CAP: caps loc = Some (from, to, msg)),
        (<<TGTGET: Memory.get loc to mem1 = Some (from, msg)>>) /\
        (<<PROMGET: Memory.get loc to prom = None>>) /\
        (<<SRCGET: forall (NONE: Memory.get loc to mem0 = None),
            exists from' to' val released,
              (<<PROM: Memory.get loc to' prom = Some (from', Message.full val released)>>)>>) /\
        (<<PROM: forall from' to' val released
                        (PROM: Memory.get loc to' prom = Some (from', Message.full val released)),
            (<<TLT: Time.lt to' to>>) /\ (<<GET: Memory.get loc to mem0 = None>>)>>))
.

Lemma diff_after_promise_unchangable caps prom0 mem_src0 mem_tgt0
      (MLE: Memory.le prom0 mem_src0)
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      loc from to msg
      (CAP: caps loc = Some (from, to, msg))
  :
    unchangable mem_tgt0 prom0 loc to from msg.
Proof.
  inv DIFF. eapply CAPS in CAP. des. econs; eauto.
Qed.

Lemma diff_after_promise_promise caps prom0 mem_src0 mem_tgt0
      loc from to msg kind prom1 mem_tgt1
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      (MLE: Memory.le prom0 mem_src0)
      (PROMISE: Memory.promise prom0 mem_tgt0 loc from to msg prom1 mem_tgt1 kind)
      (PF: (Memory.op_kind_is_lower_full kind && Message.is_released_none msg
            || Memory.op_kind_is_cancel kind)%bool)
  :
    exists mem_src1,
      (<<PROMISE: Memory.promise prom0 mem_src0 loc from to msg prom1 mem_src1 kind>>) /\
      (<<DIFF: diff_after_promises caps prom1 mem_src1 mem_tgt1>>).
Proof.
  generalize (unchangable_promise PROMISE). intros UNCH.
  dup DIFF. inv DIFF. inv PROMISE; ss.
  - unfold Message.is_released_none in *. des_ifs. des. clarify.
    dup MEM. eapply lower_succeed_wf in MEM0. des.
    exploit Memory.lower_exists.
    { eapply MLE. eapply lower_succeed_wf in PROMISES. des. eapply GET0. }
    { eauto. }
    { eauto. }
    { eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.lower_o in GET0; eauto.
        erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF1; eauto.
      * i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        eapply CAPS in CAP. des. splits; eauto.
        { i. erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
          eapply SRCGET in NONE. des. eapply Memory.lower_get1 in PROM0; eauto.
          des. inv MSG_LE0. esplits; eauto. }
        { i. erewrite Memory.lower_o in PROM0; eauto. des_ifs.
          - ss. des; clarify. exploit PROM.
            + eapply Memory.lower_get0 in PROMISES. des. eauto.
            + i. des. split; auto. eapply Memory.lower_get0 in PROMISES.
              erewrite Memory.lower_o; eauto. des_ifs. ss; des; clarify.
          - guardH o. dup PROM0. eapply PROM in PROM0. des. split; auto.
            erewrite Memory.lower_o; eauto. des_ifs. ss. des; clarify.
            exfalso. eapply Memory.lower_get0 in PROMISES. des. clarify. }
  - exploit Memory.remove_exists.
    { eapply Memory.remove_get0 in PROMISES. des.
      eapply MLE. eauto. }
    i. des. exists mem2. split.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.remove_o in GET; eauto.
        erewrite Memory.remove_o in NONE; eauto. des_ifs. eauto.
      * i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        eapply CAPS in CAP. des. splits; eauto.
        { i. erewrite Memory.remove_o in NONE; eauto. des_ifs.
          - ss. eapply Memory.remove_get0 in PROMISES. des; clarify.
          - guardH o. eapply SRCGET in NONE. des.
            exists from', to', val, released. erewrite Memory.remove_o; eauto.
            eapply Memory.remove_get0 in PROMISES. des_ifs. ss; des; clarify. }
        { i. erewrite Memory.remove_o in PROM0; eauto. des_ifs.
          guardH o. eapply PROM in PROM0. des. split; auto.
          erewrite Memory.remove_o; eauto. des_ifs. }
Qed.

Lemma diff_after_promise_write caps prom0 mem_src0 mem_tgt0
      loc from to val released kind prom1 mem_tgt1
      (DIFF: diff_after_promises caps prom0 mem_src0 mem_tgt0)
      (CAPSWF: forall loc from to msg (CAP: caps loc = Some (from, to, msg)),
          Time.lt from to)
      (MLE: Memory.le prom0 mem_src0)
      (WRITE: Memory.write prom0 mem_tgt0 loc from to val released prom1 mem_tgt1 kind)
  :
    exists mem_src1' mem_src1,
      (<<WRITE: Memory.write prom0 mem_src0 loc from to val released prom1 mem_src1' kind>>) /\
      (<<ADD: add_cap caps mem_src1' mem_src1>>) /\
      (<<DIFF: diff_after_promises caps prom1 mem_src1 mem_tgt1>>).
Proof.
  dup DIFF. inv DIFF. inv WRITE; ss.
  generalize (unchangable_promise PROMISE). intros UNCH.
  inv PROMISE; ss.
  - exploit Memory.add_exists_le.
    { eapply MLE0. }
    { eapply MEM. }
    intros [mem_src' ADD]. exists mem_src', mem_src'. splits; auto.
    + econs; eauto. econs; eauto. i. clarify.
    + assert (PROM: prom1 = prom0).
      { eapply MemoryFacts.MemoryFacts.add_remove_eq; eauto. } clarify.
      econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o.
        exploit DIFF1; eauto.
      * i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        eapply CAPS in CAP. des. splits; eauto.
        { i. erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o.
          eapply SRCGET in NONE. eauto. }
        { i. eapply PROM in PROM0. des. split; auto.
          erewrite Memory.add_o; eauto. des_ifs. ss. des; clarify.
          eapply Memory.add_get0 in MEM. des. clarify. }

  - exploit Memory.split_exists_le.
    { eapply MLE. }
    { eapply PROMISES. }
    intros [mem_src' SPLIT]. exists mem_src', mem_src'. splits; auto.
    + econs; eauto.
    + econs.
      * eapply memory_op_le; eauto.
      * i. erewrite Memory.split_o in GET; eauto.
        erewrite Memory.split_o in NONE; eauto. des_ifs. guardH o. guardH o0.
        exploit DIFF1; eauto.
      * i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        eapply CAPS in CAP. des. splits; eauto.
        { erewrite Memory.remove_o; eauto. des_ifs. }
        { i. erewrite Memory.split_o in NONE; eauto. des_ifs.
          guardH o. guardH o0. eapply SRCGET in NONE. des.
          dup PROM0. eapply Memory.split_get1 in PROM0; eauto. des.
          eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify.
          - eapply Memory.split_get0 in PROMISES. des. clarify.
          - esplits; eauto. }
        { dup PROMISES. eapply Memory.split_get0 in PROMISES; eauto. des.
          i. erewrite Memory.remove_o in PROM0; eauto. des_ifs. guardH o.
          erewrite Memory.split_o in PROM0; eauto. des_ifs; ss; clarify.
          - unguard. des; clarify.
          - guardH o0. des; clarify.
            eapply PROM in GET1. des. split; auto.
            erewrite Memory.split_o; eauto. des_ifs.
            + ss. des; clarify.
            + guardH o1. ss. des; clarify.
          - guardH o0. guardH o1. dup PROM0. eapply PROM in PROM0.
            des. split; auto.
            erewrite Memory.split_o; eauto. des_ifs.
            + ss. unguard. des; clarify.
            + ss. unguard. des; clarify. }

  - exploit Memory.lower_exists_le.
    { eapply MLE. }
    { eapply PROMISES. }
    intros [mem_src' LOWER].

    destruct (classic ((forall to' from' msg
                               (GET: Memory.get loc to' prom1 = Some (from', msg)),
                           msg = Message.reserve) /\
                       exists p, (<<CAP: caps loc = Some p>>))).
    { des. destruct p as [[from1 to1] msg1].
      dup CAP. eapply CAPS in CAP. des.
      exploit UNCH.
      { eapply diff_after_promise_unchangable; eauto. } i. inv x.
      hexploit (@Memory.add_exists mem_src' loc from1 to1 msg1); eauto.
      { i. dup GET2. eapply memory_op_le in GET2; eauto.
        exploit Memory.get_disjoint.
        - eapply GET.
        - eapply GET2.
        - i. des; clarify. exfalso.
          eapply Memory.lower_get0 in PROMISES. des.
          eapply PROM in GET1. des.
          erewrite Memory.lower_o in GET0; eauto. des_ifs; ss; des; clarify. }
      { eapply Cell.get_opt_wf; eauto. }
      intros [mem_src'' ADD]. exists mem_src', mem_src''.
      splits; eauto. econs.
      - hexploit memory_op_le; eauto. intros MLE1.
        ii. erewrite Memory.add_o in LHS; eauto. des_ifs; eauto.
        ss. des; clarify.
      - i. erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o.
        erewrite Memory.lower_o in GET0; eauto.
        erewrite Memory.lower_o in NONE; eauto. des_ifs. eapply DIFF1; eauto.
      - i. exploit UNCH.
        { eapply diff_after_promise_unchangable; eauto. } i. inv x.
        dup CAP. eapply CAPS in CAP. des. splits; eauto.
        + erewrite Memory.remove_o; eauto. des_ifs.
        + i. erewrite Memory.add_o in NONE; eauto. des_ifs. guardH o.
          erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o0.
          eapply SRCGET0 in NONE. des.
          eapply Memory.lower_get1 in PROM1; eauto. des. inv MSG_LE.
          eapply Memory.remove_get1 in GET2; eauto. des; clarify; eauto.
          ss. unguard. des; clarify.
        + i. dup PROM1. erewrite Memory.remove_o in PROM2; eauto. des_ifs.
          guardH o. erewrite Memory.lower_o in PROM2; eauto. des_ifs.
          * ss. unguard. des; clarify.
          * guardH o0. ss. eapply PROM0 in PROM2. des. split; auto.
            erewrite Memory.add_o; eauto. des_ifs.
            { ss. des; clarify. eapply H in PROM1. clarify. }
            { erewrite Memory.lower_o; eauto. des_ifs.
              unguard. ss. des;clarify. }
    }
    { exists mem_src', mem_src'. splits; auto.
      + econs; eauto.
      + econs.
        * eapply memory_op_le; eauto.
        * i. erewrite Memory.lower_o in GET; eauto.
          erewrite Memory.lower_o in NONE; eauto. des_ifs. guardH o.
          exploit DIFF1; eauto.
        * i. exploit UNCH.
          { eapply diff_after_promise_unchangable; eauto. } i. inv x.
          dup CAP. eapply CAPS in CAP. des. splits; eauto.
          { erewrite Memory.remove_o; eauto. des_ifs. }
          { i. erewrite Memory.lower_o in NONE; eauto. des_ifs.
            guardH o. eapply SRCGET in NONE. des.
            dup PROM0. eapply Memory.lower_get1 in PROM0; eauto. des.
            eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify.
            - apply not_and_or in H. des.
              + eapply not_all_ex_not in H. destruct H as [from1 H].
                eapply not_all_ex_not in H. destruct H as [to1 H].
                eapply not_all_ex_not in H. destruct H as [msg1 H].
                eapply imply_to_and in H. destruct H as [GET0 CONCRETE].
                destruct msg1; clarify. esplits; eauto.
              + exfalso. eapply H. esplits; eauto.
            - inv MSG_LE. esplits; eauto. }
          { dup PROMISES. eapply Memory.lower_get0 in PROMISES; eauto. des.
            i. erewrite Memory.remove_o in PROM0; eauto. des_ifs. guardH o.
            erewrite Memory.lower_o in PROM0; eauto. des_ifs; ss; clarify.
            - unguard. des; clarify.
            - guardH o0. eapply PROM in PROM0. des. split; auto.
              erewrite Memory.lower_o; eauto. des_ifs.
              ss. des; clarify. }
    }
Qed.

Lemma diff_after_promises_step caps P lang
      th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
      mem_src mem_tgt mem_tgt' e
      (CAPSWF: forall loc from to msg (CAP: caps loc = Some (from, to, msg)),
          Time.lt from to)
      (MLE: Memory.le prom mem_src)
      (STEP: (@pred_step P lang) e th_tgt th_tgt')
      (PROMISEFREE: P <1= promise_free)
      (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src)
      (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
      (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
      (DIFF: diff_after_promises caps prom mem_src mem_tgt)
      (CONSISTENT: Local.promise_consistent (Local.mk v' prom'))
  :
    exists mem_src' mem_src'',
      (<<STEP: (@pred_step P lang)
                 e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
      (<<ADD: add_cap caps mem_src' mem_src''>>) /\
      (<<DIFF: diff_after_promises caps prom' mem_src'' mem_tgt'>>)
.
Proof.
  inv STEP. dup SAT. eapply PROMISEFREE in SAT. inv STEP0. inv STEP.
  - inv STEP0. inv LOCAL. ss. clarify.
    exploit diff_after_promise_promise; eauto.
    i. des. exists mem_src1, mem_src1. splits; eauto.
    econs; eauto. econs; eauto. econs 1; eauto.
    econs; eauto. econs; eauto.
    unfold Message.is_released_none, Memory.op_kind_is_cancel, andb, orb in *.
    des_ifs.
    + econs. econs.
    + inv PROMISE. econs.
  - inv STEP0. inv LOCAL; ss.
    + exists mem_src, mem_src. splits; eauto.
      econs; eauto. econs; eauto.
    + dup LOCAL0. inv LOCAL0. ss. clarify.
      assert (GETSRC: Memory.get loc ts mem_src = Some (from, Message.full val released)).
      { inv DIFF. destruct (Memory.get loc ts mem_src) eqn: GET0.
        - destruct p. eapply MLE0 in GET0. clarify.
        - exploit DIFF0; eauto. intros CAP.
          eapply CAPS in CAP. des. eapply SRCGET in GET0. des.
          dup PROM0. eapply PROM in PROM0. des.
          exploit promise_consistent_promise_read; eauto.
          i. exfalso. eapply Time.lt_strorder. etrans; eauto. }
      exists mem_src, mem_src. splits; eauto.
      econs; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify.
      exploit diff_after_promise_write; eauto. i. des.
      exists mem_src1', mem_src1. splits; eauto.
      econs; eauto. econs; eauto.
    + eapply write_step_promise_consistent in CONSISTENT; eauto.
      dup LOCAL1. inv LOCAL1. inv LOCAL2. ss. clarify.
      assert (GETSRC: Memory.get loc tsr mem_src = Some (from, Message.full valr releasedr)).
      { inv DIFF. destruct (Memory.get loc tsr mem_src) eqn: GET0.
        - destruct p. eapply MLE0 in GET0. clarify.
        - exploit DIFF0; eauto. intros CAP.
          eapply CAPS in CAP. des. eapply SRCGET in GET0. des.
          dup PROM0. eapply PROM in PROM0. des.
          exploit promise_consistent_promise_read; eauto.
          i. exfalso. eapply Time.lt_strorder. etrans; eauto. }
      exploit diff_after_promise_write; eauto. i. des.
      exists mem_src1', mem_src1. splits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto.
    + inv LOCAL0. ss. clarify.
      exists mem_src, mem_src. splits; eauto.
      econs; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify.
      exists mem_src, mem_src. splits; eauto.
      econs; eauto. econs; eauto.
    + inv LOCAL0. ss. clarify.
      exists mem_src, mem_src. splits; eauto.
      econs; eauto. econs; eauto.
Qed.

Definition collapsing_latest_reserves (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: to = Memory.max_ts loc mem>>) /\
  (<<RESERVE: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
  (<<OTHER: L loc>>)
.

Definition collapsing_latest_reserves_times (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  exists from,
    (<<RESERVE: collapsing_latest_reserves L mem loc to from>>).

Definition collapsing_caps (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<FULL: Memory.max_full_ts mem0 loc from>>) /\
  (<<LATEST: exists from0 val released,
      (<<CAP: caps mem0 mem1 loc to from0 (Message.full val released)>>)>>) /\
  (<<OTHER: L loc>>)
.

Definition collapsing_caps_times (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<CAP: collapsing_caps L mem0 mem1 loc to from>>).

Definition times_in_memory (mem: Memory.t) (L: Loc.t -> list Time.t): Prop :=
  forall loc t,
    (<<SAT: List.In t (L loc)>>) <->
    (<<INMEMORY:
       (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
       (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>).

Lemma times_in_memory_exists mem
  :
    exists l, times_in_memory mem l.
Proof.
  hexploit (choice
              (fun loc tl =>
                 forall t,
                   (<<SAT: List.In t tl>>) <->
                   (<<INMEMORY:
                      (exists from msg, (<<GET: Memory.get loc t mem = Some (from, msg)>>)) \/
                      (exists to msg, (<<GET: Memory.get loc to mem = Some (t, msg)>>))>>))); auto.
  intros loc.
  hexploit (wf_cell_msgs_exists (mem loc)). i. des.
  exists ((List.map (fun ftm =>
                       match ftm with
                       | (from, _, _) => from
                       end) l)
            ++
            (List.map (fun ftm =>
                         match ftm with
                         | (_, to, _) => to
                         end) l)).
  i. split; i.
  - red in H. eapply List.in_app_or in H. des.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. right. eauto.
    + eapply List.in_map_iff in H. des.
      destruct x as [[from to] msg]. clarify.
      eapply COMPLETE in H0. left. eauto.
  - eapply List.in_or_app.  des.
    + right. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
    + left. eapply COMPLETE in GET.
      eapply List.in_map_iff. esplits; eauto. ss.
Qed.

Inductive caps_collapsing (L: Loc.t -> Prop)
          (mem: Memory.t): Loc.t -> Time.t -> Time.t -> Prop :=
| caps_collapsing_not_in
    loc t
    (NSAT: ~ L loc)
  :
    caps_collapsing L mem loc t t
| caps_collapsing_in_memory
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (TLE: Time.le t max)
  :
    caps_collapsing L mem loc t t
| caps_collapsing_latest_reserve
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (MAX: t = Memory.max_ts loc mem)
  :
    caps_collapsing L mem loc max t
| caps_collapsing_cap
    loc t max
    (SAT: L loc)
    (FULL: Memory.max_full_ts mem loc max)
    (CAP: t = Time.incr (Memory.max_ts loc mem))
  :
    caps_collapsing L mem loc max t
| caps_collapsing_outer_memory
    loc t
    (SAT: L loc)
    (TLE: Time.lt (Time.incr (Memory.max_ts loc mem)) t)
  :
    caps_collapsing L mem loc t t
.

Lemma forget_memory_get P mem0 mem1 loc to msg
      (FORGET: forget_memory P mem0 mem1)
      (GET: Memory.get loc to mem0 = Some msg)
  :
    (<<NOT: ~ P loc to>>) /\ (<<GET: Memory.get loc to mem1 = Some msg>>).
Proof.
  inv FORGET. destruct (classic (P loc to)).
  - exfalso. rewrite FORGET0 in GET; auto. clarify.
  - esplits; eauto.
    rewrite <- COMPLETE; auto.
Qed.

Lemma caps_get_reserve mem0 prom mem1 loc to from
      (RESERVE: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (CAPS: caps mem0 mem1 loc to from Message.reserve)
  :
    exists from0 to1 msg0 msg1,
      (<<GET0: Memory.get loc from mem0 = Some (from0, msg0)>>) /\
      (<<GET1: Memory.get loc to1 mem0 = Some (to, msg1)>>) /\
      (<<SPACE: forall t (ITV: Interval.mem (from, to) t), ~ covered loc t mem0>>)
.
Proof.
  unfold caps in CAPS. des. inv CAP.
  exploit COMPLETE; eauto. i. des.
  set (@cell_elements_least
         (mem0 loc)
         (fun t => Time.lt from t)). des.
  - hexploit (MIDDLE loc f from from0 to0).
    { econs; eauto. i.
      destruct (Memory.get loc ts mem0) eqn:GET2; auto. destruct p.
      exfalso. exploit LEAST.
      - eapply GET2.
      - eauto.
      - i. exploit Memory.get_ts; try apply GET.
        i. des; clarify.
        + eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          * eapply SAT.
          * eapply Time.bot_spec.
        + eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          * etrans.
            { eapply x1. }
            { eapply TS2. }
          * eauto. }
    { exploit memory_get_from_mon.
      - eapply x.
      - eapply GET.
      - eauto.
      - i. destruct x2; auto. destruct H. exfalso.
        exploit memory_get_from_inj.
        { eapply SOUND. eapply GET. }
        { eapply GET1. }
        i. des; clarify.
        + setoid_rewrite GET0 in GET. clarify.
        + eapply Time.lt_strorder; eauto. }
    i. exploit memory_get_from_inj.
    { eapply H. }
    { eapply GET1. }
    i. des; clarify.
    + esplits; eauto. ii. inv H0.
      exploit Memory.get_disjoint.
      * eapply SOUND. eapply GET2.
      * eapply H.
      * i. des; clarify. eapply x2; eauto.
    + specialize (INHABITED loc).
      eapply SOUND in INHABITED. clarify.
  - exploit Memory.max_ts_spec.
    { eapply x. }
    i. des. destruct MAX.
    + exfalso. eapply EMPTY; eauto.
    + unfold Time.eq in *. subst. exploit x0; auto. intros LATEST.
      exploit Memory.latest_val_exists; eauto. i. des.
      exploit Memory.max_full_view_exists; eauto. i. des.
      exploit BACK; eauto. i.
      exploit memory_get_from_inj.
      * eapply x1.
      * eapply GET1.
      * i. des; clarify.
        { exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          - eapply Time.incr_spec.
          - rewrite BOT0. eapply Time.bot_spec. }
        { erewrite INHABITED in GET0. clarify. }
Qed.

Definition memory_concrete_le (lhs rhs: Memory.t): Prop :=
  forall loc to from val released
         (GET: Memory.get loc to lhs = Some (from, Message.full val released)),
    Memory.get loc to rhs = Some (from, Message.full val released).

Lemma memory_concrete_le_le
  :
    Memory.le <2= memory_concrete_le.
Proof.
  ii. eauto.
Qed.
Hint Resolve memory_concrete_le_le.

Lemma memory_concrete_le_closed_timemap tm mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (TM: Memory.closed_timemap tm mem0)
  :
    Memory.closed_timemap tm mem1.
Proof.
  ii. hexploit (TM loc). i. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_closed_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_view vw mem0)
  :
    Memory.closed_view vw mem1.
Proof.
  inv VW. econs.
  - eapply memory_concrete_le_closed_timemap; eauto.
  - eapply memory_concrete_le_closed_timemap; eauto.
Qed.

Lemma memory_concrete_le_closed_opt_view vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: Memory.closed_opt_view vw mem0)
  :
    Memory.closed_opt_view vw mem1.
Proof.
  inv VW; econs.
  eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_closed_msg msg mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (MSG: Memory.closed_message msg mem0)
  :
    Memory.closed_message msg mem1.
Proof.
  inv MSG; econs.
  eapply memory_concrete_le_closed_opt_view; eauto.
Qed.

Lemma memory_concrete_le_closed_tview vw mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (VW: TView.closed vw mem0)
  :
    TView.closed vw mem1.
Proof.
  inv VW. econs.
  - i. eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
  - eapply memory_concrete_le_closed_view; eauto.
Qed.

Lemma memory_concrete_le_reserve_wf prom mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (RESERVE: Memory.reserve_wf prom mem0)
  :
    Memory.reserve_wf prom mem1.
Proof.
  ii. eapply RESERVE in GET. des.
  esplits; eauto.
Qed.

Lemma memory_concrete_le_local_wf lc mem0 mem1
      (MLE: memory_concrete_le mem0 mem1)
      (PROM: Memory.le (Local.promises lc) mem1)
      (LOCAL: Local.wf lc mem0)
  :
    Local.wf lc mem1.
Proof.
  inv LOCAL. econs; eauto.
  - eapply memory_concrete_le_closed_tview; eauto.
  - eapply memory_concrete_le_reserve_wf; eauto.
Qed.

Lemma partial_cap_closed prom mem0 mem1 mem2
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (MLE0: Memory.le mem0 mem1)
      (MLE1: Memory.le mem1 mem2)
  :
    Memory.closed mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  inv CLOSED. econs; eauto.
  i. destruct (Memory.get loc to mem0) as [[from0 msg0]|] eqn:GET.
  - dup GET. eapply MLE0 in GET. clarify.
    eapply CLOSED0 in GET0. des. esplits; eauto.
    eapply memory_concrete_le_closed_msg; eauto.
  - destruct msg.
    + eapply MLE1 in MSG.
      exploit caps_max_view; eauto.
      * econs; eauto.
      * i. des; clarify. esplits; eauto.
        { econs; eauto. econs; eauto. econs. refl. }
        { econs; eauto. ss. transitivity (Memory.max_ts loc mem0).
          - specialize (MAX loc). inv MAX. des.
            eapply Memory.max_ts_spec in GET0. des. eauto.
          - left. eapply Time.incr_spec. }
        { eapply memory_concrete_le_closed_msg; eauto.
          econs. econs. econs.
          - eapply Memory.max_full_timemap_closed; eauto.
          - eapply Memory.max_full_timemap_closed; eauto. }
    + esplits; eauto. econs.
Qed.

Lemma collapsing_caps_forget_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem1 mem2)
  :
    memory_concrete_le mem0 mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto. refl.
  - ii. des.
    + unfold collapsing_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
    + unfold collapsing_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des. clarify.
Qed.

Definition collapsable_cap (L: Loc.t -> Prop) (prom mem: Memory.t): Prop :=
  forall
    loc (SAT: L loc)
    from msg
    (GET: Memory.get loc (Memory.max_ts loc mem) prom = Some (from, msg)),
    msg <> Message.reserve.

Lemma collapsing_caps_forget_prom_le
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (CAP: Memory.cap prom mem0 mem2)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem1 mem2)
  :
    Memory.le prom mem1.
Proof.
  inv FORGET. ii.
  erewrite COMPLETE.
  - eapply Memory.cap_le in CAP; eauto.
  - ii. des.
    + unfold collapsing_latest_reserves_times in *. des.
      inv RESERVE. des. clarify.
      dup LHS. eapply MLE in LHS0. clarify.
      eapply COLLAPSABLE in OTHER. eapply OTHER in LHS. clarify.
    + unfold collapsing_caps_times in *. des.
      inv CAP0. des. unfold caps in CAP0. des.
      eapply MLE in LHS; eauto. clarify.
Qed.

Lemma identity_mapped_view tm maxmap (f: Loc.t -> Time.t -> Time.t -> Prop)
      (TM: TimeMap.le tm maxmap)
      (IDENT: forall loc ts (TS: Time.le ts (maxmap loc)), f loc ts ts)
  :
    timemap_map f tm tm.
Proof.
  ii. eapply IDENT; eauto.
Qed.

Lemma caps_collapsing_ident L mem loc maxts ts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le ts maxts)
  :
    (caps_collapsing L mem) loc ts ts.
Proof.
  i. destruct (classic (L loc)).
  - econs 2; eauto.
  - econs 1; eauto.
Qed.

Definition memory_reserve_wf mem := Memory.reserve_wf mem mem.

Lemma memory_reserve_wf_promise
      prom0 mem0 loc from to msg prom1 mem1 kind
      (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
      (RESERVE: memory_reserve_wf mem0)
  :
    memory_reserve_wf mem1.
Proof.
  inv PROMISE.
  - ii. erewrite Memory.add_o in GET; eauto. des_ifs.
    + ss; des; clarify. exploit RESERVE0; eauto.
      i. des. eapply Memory.add_get1 in x; eauto.
    + eapply RESERVE in GET; eauto. clear o. des.
      eapply Memory.add_get1 in GET; eauto.
  - ii. des. clarify. erewrite Memory.split_o in GET; eauto. des_ifs.
    + ss; des; clarify. eapply Memory.split_get0 in MEM. des.
      esplits; eauto.
    + eapply RESERVE in GET; eauto. clear o o0. des.
      eapply Memory.split_get1 in GET; eauto. des. esplits; eauto.
  - ii. erewrite Memory.lower_o in GET; eauto. des_ifs.
    + ss; des; clarify. inv MEM. inv LOWER. inv MSG_LE.
    + eapply RESERVE in GET; eauto. clear o. des.
      eapply Memory.lower_get1 in GET; eauto. des.
      inv MSG_LE. esplits; eauto.
  - ii. erewrite Memory.remove_o in GET; eauto. des_ifs. guardH o.
    dup MEM. eapply Memory.remove_get0 in MEM0. des.
    eapply RESERVE in GET; eauto. des. dup GET.
    eapply Memory.remove_get1 in GET2; eauto. ss. des; clarify.
    esplits; eauto.
Qed.

Lemma memory_reserve_wf_tstep lang (th0 th1: Thread.t lang) tf e
      (RESERVE: memory_reserve_wf th0.(Thread.memory))
      (STEP: Thread.step tf e th0 th1)
  :
    memory_reserve_wf th1.(Thread.memory).
Proof.
  inv STEP; inv STEP0; ss.
  - inv LOCAL. eapply memory_reserve_wf_promise; eauto.
  - inv LOCAL; eauto.
    + inv LOCAL0. inv WRITE.
      eapply memory_reserve_wf_promise; eauto.
    + inv LOCAL1. inv LOCAL2. inv WRITE.
      eapply memory_reserve_wf_promise; eauto.
Qed.

Lemma memory_reserve_wf_tsteps lang (th0 th1: Thread.t lang)
      (RESERVE: memory_reserve_wf th0.(Thread.memory))
      (STEP: rtc (tau (@Thread.step_allpf lang)) th0 th1)
  :
    memory_reserve_wf th1.(Thread.memory).
Proof.
  ginduction STEP; eauto.
  i. eapply IHSTEP; eauto. inv H. inv TSTEP.
  eapply memory_reserve_wf_tstep; eauto.
Qed.

Lemma memory_reserve_wf_init
  :
    memory_reserve_wf Memory.init.
Proof.
  ii. unfold Memory.get, Memory.init in *. ss.
  rewrite Cell.init_get in GET. des_ifs.
Qed.

Lemma memory_reserve_wf_configuration_step c0 c1 e tid
      (RESERVE: memory_reserve_wf c0.(Configuration.memory))
      (STEP: Configuration.step e tid c0 c1)
  :
    memory_reserve_wf c1.(Configuration.memory).
Proof.
  eapply configuration_step_equivalent in STEP. inv STEP. ss.
  eapply memory_reserve_wf_tstep in STEP0; eauto.
  eapply memory_reserve_wf_tsteps in STEPS; eauto.
Qed.

Lemma not_latest_reserve_le_max_full_ts loc mem ts to from msg
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
      (GET: Memory.get loc to mem = Some (from, msg))
  :
    (<<TLE: Time.le to ts>>) \/
    ((<<TO: to = Memory.max_ts loc mem>>) /\
     (<<FROM: from = ts>>) /\
     (<<MSG: msg = Message.reserve>>)).
Proof.
  inv MAX. des.
  destruct msg.
  - left. eapply MAX0; eauto.
  - exploit RESERVEWF; eauto. i. des.
    destruct (TimeFacts.le_lt_dec to ts); auto.
    dup x. eapply MAX0 in x; eauto. destruct x.
    + exfalso. exploit memory_get_from_mon.
      { eapply GET0. }
      { eapply GET. }
      { auto. }
      i. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
      * eapply x1.
      * eapply H.
    + unfold Time.eq in *. subst. right. esplits; eauto.
      setoid_rewrite GET0 in x0. clarify.
      dup GET. eapply Memory.max_ts_spec in GET1. des.
      destruct MAX; auto. exfalso.
      destruct msg.
      * eapply MAX0 in GET2. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { etrans.
          - eapply l.
          - eapply H. }
        { eauto. }
      * dup GET2. eapply RESERVEWF in GET2. des.
        eapply MAX0 in GET2.
        exploit memory_get_from_mon.
        { eapply GET. }
        { eapply GET1. }
        { eapply H. }
        i. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt.
        { eapply l. }
        { etrans.
          - eapply x0.
          - eapply Memory.get_ts in GET1. des; clarify. }
Qed.

Lemma max_full_ts_le_max_ts mem loc ts
      (MAX: Memory.max_full_ts mem loc ts)
  :
    Time.le ts (Memory.max_ts loc mem).
Proof.
  inv MAX. des.
  eapply Memory.max_ts_spec in GET. des; auto.
Qed.

Lemma max_full_ts_max_ts loc mem ts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX : Memory.max_full_ts mem loc ts)
  :
    (<<FULL: ts = Memory.max_ts loc mem>>) \/
    ((<<TLT: Time.lt ts (Memory.max_ts loc mem)>>) /\
     (<<GET: Memory.get loc (Memory.max_ts loc mem) mem = Some (ts, Message.reserve)>>)).
Proof.
  dup MAX. inv MAX. des.
  eapply Memory.max_ts_spec in GET. des.
  dup GET0. eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
  des; clarify.
  - left. eapply TimeFacts.antisym; eauto.
  - right. split; eauto. dup GET1.
    eapply memory_get_ts_strong in GET1. des; clarify.
    erewrite GET2 in *.
    erewrite INHABITED in GET0. clarify.
Qed.

Lemma caps_collapsing_ident2 L mem maxts loc ts fts
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.le fts maxts)
      (MAP: (caps_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  - exploit Memory.max_full_ts_inj.
    { eapply FULL. }
    { eapply MAX. }
    i. clarify. eapply TimeFacts.antisym; auto.
    eapply max_full_ts_le_max_ts in FULL; auto.
  - exfalso. eapply max_full_ts_le_max_ts in FULL. exfalso.
    eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
    + eapply DenseOrder.DenseOrder.incr_spec.
    + etrans.
      * eapply TS.
      * eapply max_full_ts_le_max_ts; eauto.
Qed.

Lemma caps_collapsing_ident3 L mem maxts loc ts fts
      (RESERVEWF : memory_reserve_wf mem)
      (INHABITED : Memory.inhabited mem)
      (MAX: Memory.max_full_ts mem loc maxts)
      (TS: Time.lt ts maxts)
      (MAP: (caps_collapsing L mem) loc ts fts)
  :
    ts = fts.
Proof.
  inv MAP; eauto.
  - exploit Memory.max_full_ts_inj.
    { eapply FULL. }
    { eapply MAX. }
    i. clarify. exfalso. eapply Time.lt_strorder; eauto.
  - exploit Memory.max_full_ts_inj.
    { eapply FULL. }
    { eapply MAX. }
    i. clarify. exfalso. eapply Time.lt_strorder; eauto.
Qed.

Lemma caps_collapsing_timemap L mem tm
      (INHABITED: Memory.inhabited mem)
      (TM: Memory.closed_timemap tm mem)
  :
    timemap_map (caps_collapsing L mem) tm tm.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [maxmap MAX].
  eapply identity_mapped_view.
  - eapply Memory.max_full_timemap_spec; eauto.
  - i. eapply caps_collapsing_ident; eauto.
Qed.

Lemma caps_collapsing_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_view vw mem)
  :
    view_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - eapply caps_collapsing_timemap; eauto.
  - eapply caps_collapsing_timemap; eauto.
Qed.

Lemma caps_collapsing_opt_view L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: Memory.closed_opt_view vw mem)
  :
    opt_view_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW; econs.
  eapply caps_collapsing_view; eauto.
Qed.

Lemma caps_collapsing_message L mem msg
      (INHABITED: Memory.inhabited mem)
      (MSG: Memory.closed_message msg mem)
  :
    msg_map (caps_collapsing L mem) msg msg.
Proof.
  inv MSG; econs.
  eapply caps_collapsing_opt_view; eauto.
Qed.

Lemma caps_collapsing_tview L mem vw
      (INHABITED: Memory.inhabited mem)
      (VW: TView.closed vw mem)
  :
    tview_map (caps_collapsing L mem) vw vw.
Proof.
  inv VW. econs.
  - i. eapply caps_collapsing_view; eauto.
  - eapply caps_collapsing_view; eauto.
  - eapply caps_collapsing_view; eauto.
Qed.

Lemma caps_collapsing_promises (L: Loc.t -> Prop) mem prom
      (MLE: Memory.le prom mem)
      (CLOSED: Memory.closed mem)
      (RESERVEWF: memory_reserve_wf mem)
      (INHABITED: Memory.inhabited mem)
      (LATESTRESERVE: forall
          loc (SAT: L loc)
          from msg
          (GET: Memory.get loc (Memory.max_ts loc mem) prom = Some (from, msg)),
          msg <> Message.reserve)
  :
    promises_map (caps_collapsing L mem) prom prom.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply MLE in GET0. eapply CLOSED1 in GET0. des.
    exists to, from, msg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET0.
      eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
      eapply or_strengthen in GET0. des; clarify.
      * esplits; eauto.
        { ii. unfold collapsed in *. des.
          eapply caps_collapsing_ident3 in MAP0; eauto; cycle 1.
          { eapply TimeFacts.lt_le_lt; eauto. } clarify.
          assert (TO: to = ft).
          { destruct TLE.
            - eapply caps_collapsing_ident3 in MAP1; eauto.
            - unfold Time.eq in *. clarify. inv MAP1; clarify.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * eapply TLE0.
                * eapply max_full_ts_le_max_ts; eauto.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * etrans.
                  { eapply Time.incr_spec. }
                  { eapply TLE0. }
                * eapply max_full_ts_le_max_ts; eauto. }
          clarify. eapply Time.lt_strorder; eauto. }
        { econs 2; eauto. }
        { eapply caps_collapsing_message; eauto. }
      * exfalso. exploit LATESTRESERVE; eauto.
    + splits; auto.
      * ii. unfold collapsed in *. des.
        inv MAP0; clarify. inv MAP1; clarify.
        eapply Time.lt_strorder. eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
  - i. exists fto, ffrom, fmsg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET.
      eapply not_latest_reserve_le_max_full_ts in GET; eauto.
      des; clarify.
      * splits; auto.
        { eapply caps_collapsing_ident; eauto. }
        { eapply caps_collapsing_ident; eauto.
          etrans; eauto.
          eapply memory_get_ts_strong in GET0. des; clarify.
          { refl. }
          { left. auto. } }
      * exfalso. exploit LATESTRESERVE; eauto.
    + splits; auto.
      * econs 1; eauto.
      * econs 1; eauto.
Qed.

Lemma memory_cap_message_closed prom mem0 mem1
      (CLOSED: Memory.closed mem0)
      (CAP: Memory.cap prom mem0 mem1)
      loc to from msg
      (GET: Memory.get loc to mem1 = Some (from, msg))
  :
    Memory.closed_message msg mem0.
Proof.
  eapply Memory.cap_inv in GET; eauto. des.
  - eapply CLOSED in GET. des; auto.
  - clarify.
  - clarify. econs. econs.
    eapply Memory.max_full_view_closed; eauto.
Qed.

Lemma memory_get_ts_le loc to mem from msg
      (GET: Memory.get loc to mem = Some (from, msg))
  :
    Time.le from to.
Proof.
  eapply Memory.get_ts in GET. des; clarify.
  - refl.
  - left. auto.
Qed.

Lemma caps_collapsing_memory
      mem0 mem1 mem2 mem3 prom (L0 L1: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (RESERVEWF0: memory_reserve_wf mem0)
      (INHABITED: Memory.inhabited mem0)
      (COLLAPSABLE0: collapsable_cap L0 prom mem0)
      (COLLAPSABLE1: collapsable_cap L1 prom mem0)
      (DISJOINTLOC: forall l (SAT0: L0 l) (SAT1: L1 l) , False)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L0 mem0 \2/ collapsing_caps_times L0 mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) mem3 mem2)
  :
    memory_map (caps_collapsing L1 mem0) mem3 mem2.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup FORGET0. inv FORGET0. dup FORGET1. inv FORGET1.
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply forget_memory_get in GET0; eauto. des.
    exists to, from, msg, msg.
    destruct (classic (L1 loc)).
    + esplits; eauto.
      * econs 2; eauto.
        eapply forget_memory_get in GET1; eauto. des.
        apply not_or_and in NOT. apply not_or_and in NOT0. des.
        dup GET0. eapply Memory.cap_inv in GET0; eauto. des; clarify.
        { dup GET0. eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
          des; clarify. exfalso. eapply NOT. econs; eauto. econs; eauto. }
        { inv GET2. dup GET5. eapply memory_get_ts_le in GET2.
          eapply not_latest_reserve_le_max_full_ts in GET5; eauto. des.
          - etrans; eauto.
          - clarify. refl. }
        { exfalso. eapply NOT2. econs; eauto. econs; eauto.
          esplits; eauto. econs; eauto. }
      * eapply caps_collapsing_message; eauto.
        eapply forget_memory_get in GET1; eauto. des.
        eapply memory_cap_message_closed in GET0; eauto.
      * refl.
    + esplits; eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
        eapply forget_memory_get in GET1; eauto. des.
        eapply memory_cap_message_closed in GET0; eauto.
      * refl.
  - i. destruct (classic (L1 loc)).
    + destruct (classic ((collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) loc fto)).
      * des.
        { inv H0. inv H1. des. clarify.
          dup GET. eapply forget_memory_get in GET0; eauto. des.
          dup RESERVE. eapply Memory.cap_le in RESERVE; eauto; [|refl]. clarify.


          memory_map

            Memory.get


          dup GET1. eapply forget_memory_get in GET1; eauto. des.


        admit.
      * apply not_or_and in H0. des.
        exists fto, ffrom, fmsg.
        assert (TS: Time.le  fto (tm loc)).
        { dup GET. eapply forget_memory_get in GET0; eauto. des.
          dup GET1. eapply Memory.cap_inv in GET1; eauto. des; clarify.
          - dup GET1. eapply not_latest_reserve_le_max_full_ts in GET1; eauto.
            des; clarify. exfalso. eapply H0. econs; eauto. econs; eauto.
          - inv GET2. dup GET5. eapply not_latest_reserve_le_max_full_ts in GET5; eauto.
            des; clarify.
            + eapply memory_get_ts_le in GET2. etrans; eauto.
            + refl.
          - exfalso. eapply H1. econs; eauto. econs; eauto.
            esplits; eauto. econs; eauto. }
        splits.
        { econs 2; eauto. }
        { erewrite COMPLETE0; eauto. ii. des; clarify. }
        { econs 2; eauto. etrans; eauto. eapply memory_get_ts_le; eauto. }
    + exists fto, ffrom, fmsg. esplits.
      * econs 1; eauto.
      * erewrite COMPLETE0; eauto. ii. des.
        { inv H0. inv H1. des. clarify. }
        { inv H0. inv H1. des. clarify. }
      * econs 1; eauto.





        Lemma caps_collapsing_memory
      mem0 mem1 mem2 mem3 prom (L0 L1: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (COLLAPSABLE0: collapsable_cap L0 prom mem0)
      (COLLAPSABLE1: collapsable_cap L1 prom mem0)
      (DISJOINTLOC: forall l (SAT0: L0 l) (SAT1: L1 l) , False)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L0 mem0 \2/ collapsing_caps_times L0 mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (collapsing_latest_reserves_times L1 mem0 \2/ collapsing_caps_times L1 mem0 mem1) mem3 mem2)
  :
    memory_map (caps_collapsing L1 mem0) mem3 mem2.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup FORGET0. inv FORGET0. dup FORGET1. inv FORGET1.
  dup CLOSED. inv CLOSED0. econs.
  - i.


    destruct (classic (L1 loc)).
    + dup GET. eapply forget_memory_get in GET0; eauto. des.
      e



      admit.
    + dup GET. eapply forget_memory_get in GET0; eauto. des.
      exists to, from, msg, msg. esplits; eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.
        eapply forget_memory_get in GET1; eauto. des.
        eapply memory_cap_message_closed in GET0; eauto.
      * refl.
  -  i.

        eapply memory_concrete_le_closed_msg.
        { eapply collapsing_caps_forget_le; eauto.

        eapply forget_memory_get in GET1; eauto.

      esplits; eauto.
      * econs 1; eauto.
      *


      des.
      dup GET1. erewrite <- COMPLETE0 in GET1; eauto. esplits; eauto.

      admit.
    +

      dup inv FO

Admitted.


Lemma caps_collapsing_memory
      mem0 mem1 mem2 mem3 prom (L0 L1: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (COLLAPSABLE0: collapsable_cap L0 prom mem0)
      (COLLAPSABLE1: collapsable_cap L1 prom mem0)
      (DISJOINTLOC: forall l (SAT0: L0 l) (SAT1: L1 l) , False)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (collapsing_latest_reserves_times L0 mem0 \2/ collapsing_caps_times L0 mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (collapsing_latest_reserves_times (L0 \1/ L1) mem0 \2/ collapsing_caps_times (L0 \1/ L1) mem0 mem1) mem3 mem1)
  :
    memory_map (caps_collapsing L1 mem0) mem3 mem2.
Proof.
  (* exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX]. *)
  (* dup CLOSED. inv CLOSED0. econs. *)
  (* - i. destruct (classic (L loc)). *)
  (*   + dup GET. eapply forget_memory_get in GET0; eauto. des. *)
Admitted.

Lemma other_collapsing_memory
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (COLLAPSABLE: collapsable_cap L prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (collapsing_latest_reserves_times L mem0 \2/ collapsing_caps_times L mem0 mem1) mem2 mem1)
  :
    memory_map (caps_collapsing L mem0) mem2 mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. destruct (classic (L loc)).
    + dup GET. eapply forget_memory_get in GET0; eauto. des.
Admitted.


Lemma other_collapsing_memory
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (SELF: forall loc (SAT: L loc),
          match Memory.get loc (Memory.max_ts loc mem) prom with
          | Some (_, Message.full _ _) => True
          | _ => False
          end)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET0: forget_memory (other_latest_reserves_times L mem0 \2/ other_caps_times L mem0 mem1) mem2 mem1)
      (FORGET1: forget_memory (other_latest_reserves_times L mem0 \2/ other_caps_times L mem0 mem1 \2/ ) mem3 mem2)
  :
    memory_map (caps_collapsing L mem0) mem2 mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. destruct (classic (L loc)).
    + dup GET. eapply forget_memory_get in GET0; eauto. des.
Admitted.


Definition self_latest_reseves_loc (mem prom: Memory.t) (loc: Loc.t): Prop :=
  Memory.latest_reserve loc mem prom.

(* Inductive self_collapsing (L: Loc.t -> Prop) *)
(*           (mem: Memory.t): Loc.t -> Time.t -> Time.t -> Prop := *)
(* | self_collapsing_not_in *)
(*     loc t *)
(*     (NSAT: ~ L loc) *)
(*   : *)
(*     self_collapsing L mem loc t t *)
(* | self_collapsing_in_memory *)
(*     loc t *)
(*     (SAT: L loc) *)
(*     (TLE: Time.le t (Memory.max_ts loc mem)) *)
(*   : *)
(*     self_collapsing L mem loc t t *)
(* | self_collapsing_cap *)
(*     loc t max *)
(*     (SAT: L loc) *)
(*     (FULL: max = Memory.max_ts loc mem) *)
(*     (CAP: t = Time.incr (Memory.max_ts loc mem)) *)
(*   : *)
(*     self_collapsing L mem loc max t *)
(* | self_collapsing_outer_memory *)
(*     loc t *)
(*     (SAT: L loc) *)
(*     (TLE: Time.lt (Time.incr (Memory.max_ts loc mem)) t) *)
(*   : *)
(*     self_collapsing L mem loc t t *)
(* . *)

Lemma self_collapsing_promises (L: Loc.t -> Prop) mem prom
      (MLE: Memory.le prom mem)
      (CLOSED: Memory.closed mem)
      (RESERVEWF: memory_reserve_wf mem)
      (INHABITED: Memory.inhabited mem)
      (SELF: forall loc (SAT: L loc),
          match Memory.get loc (Memory.max_ts loc mem) prom with
          | Some (_, Message.full _ _) => True
          | _ => False
          end)
  :
    promises_map (self_collapsing L mem) prom prom.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. dup GET. eapply MLE in GET0. eapply CLOSED1 in GET0. des.
    exists to, from, msg.
    destruct (classic (L loc)).
    + dup GET. eapply MLE in GET0.
      eapply not_latest_reserve_le_max_full_ts in GET0; eauto.
      eapply or_strengthen in GET0. des; clarify.
      * esplits; eauto.
        { ii. unfold collapsed in *. des.
          eapply caps_collapsing_ident3 in MAP0; eauto; cycle 1.
          { eapply TimeFacts.lt_le_lt; eauto. } clarify.
          assert (TO: to = ft).
          { destruct TLE.
            - eapply caps_collapsing_ident3 in MAP1; eauto.
            - unfold Time.eq in *. clarify. inv MAP1; clarify.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * eapply TLE0.
                * eapply max_full_ts_le_max_ts; eauto.
              + exfalso. eapply Time.lt_strorder.
                eapply TimeFacts.lt_le_lt.
                * etrans.
                  { eapply Time.incr_spec. }
                  { eapply TLE0. }
                * eapply max_full_ts_le_max_ts; eauto. }
          clarify. eapply Time.lt_strorder; eauto. }
        { econs 2; eauto. }
        { eapply caps_collapsing_message; eauto. }
      * exfalso. exploit OTHERS; eauto.
        unfold Memory.latest_reserve. rewrite GET. auto.
    + splits; auto.
      * ii. unfold collapsed in *. des.
        inv MAP0; clarify. inv MAP1; clarify.
        eapply Time.lt_strorder. eauto.
      * econs 1; eauto.
      * eapply caps_collapsing_message; eauto.


Lemma caps_collapsing_memory
      mem0 mem1 mem2 prom (L: Loc.t -> Prop)
      (MLE: Memory.le prom mem0)
      (CLOSED: Memory.closed mem0)
      (RESERVEWF: Memory.reserve_wf prom mem0)
      (INHABITED: Memory.inhabited mem0)
      (OTHERS: forall loc (SAT: L loc), Memory.latest_reserve loc prom mem0)
      (CAP: Memory.cap prom mem0 mem1)
      (FORGET: forget_memory (other_latest_reserves_times L mem0 \2/ other_caps_times L mem0 mem1) mem2 mem1)
  :
    memory_map (caps_collapsing L mem0) mem2 mem1.
Proof.
  exploit Memory.max_full_timemap_exists; eauto. intros [tm MAX].
  dup CLOSED. inv CLOSED0. econs.
  - i. destruct (classic (L loc)).
    + dup GET. eapply forget_memory_get in GET0; eauto. des.
Admitted.


Definition other_latest_reserves (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<LATEST: to = Memory.max_ts loc mem>>) /\
  (<<RESERVE: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
  (<<OTHER: L loc>>)
.

Definition other_latest_reserves_times (L: Loc.t -> Prop)
           (mem: Memory.t) (loc: Loc.t) (to: Time.t): Prop :=
  exists from,
    (<<RESERVE: other_latest_reserves L mem loc to from>>).

Definition other_caps (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) (from: Time.t) :=
  (<<FULL: Memory.max_full_ts mem0 loc from>>) /\
  (<<LATEST: exists from0 val released,
      (<<CAP: caps mem0 mem1 loc to from0 (Message.full val released)>>)>>) /\
  (<<OTHER: L loc>>)
.

Definition other_caps_times (L: Loc.t -> Prop)
           (mem0 mem1: Memory.t) (loc: Loc.t) (to: Time.t) :=
  exists from,
    (<<CAP: other_caps L mem0 mem1 loc to from>>).


Inductive shifted_map mlast mcert
          (updates: Loc.t -> Prop)
          (sky gap: TimeMap.t)
          (f: Loc.t -> Time.t -> Time.t): Prop :=
| shifted_map_intro
    (PRSV: map_preserving (times_in_memory mcert) f)
    (SAME: forall l t (TLE: Time.le t (Memory.max_ts l mlast)),
        f l t = t)
    (INGAP: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t),
        Time.lt (f l t) (gap l))
    (AFTERSKY: forall l t (TLT: Time.lt (Memory.max_ts l mcert) t),
        Time.lt (sky l) (f l t))
.

Lemma shifted_map_exists mlast mcert updates
      (MLE: Memory.le mlast mcert)
      (sky gap: TimeMap.t)
      (SKY: forall l, Time.lt (Memory.max_ts l mlast) (sky l))
      (GAP: forall l, Time.lt (Memory.max_ts l mlast) (gap l))
  :
    exists f, (<<SHIFTED: shifted_map mlast mcert updates sky gap f>>).
Proof.
  (* may be very hard... *)
Admitted.

Lemma shifted_map_preserving_last_mem  mlast mcert updates sky gap f
      (CLOSED: Memory.closed mlast)
      (SHIFTED: shifted_map mlast mcert updates sky gap f)
  :
    memory_map f mlast mlast.
Proof.
  inv SHIFTED. inv PRSV. econs; i.
  - exploit Memory.max_ts_spec; eauto. i. des.
    repeat erewrite SAME; eauto.
    + rewrite GET. unfold msg_map. des_ifs. repeat f_equal.
      inv CLOSED. exploit CLOSED0; try apply GET; eauto. i. des.
      inv MSG_CLOSED. inv CLOSED; ss. f_equal.
      destruct view. inv CLOSED1. unfold view_map, timemap_map. ss. f_equal.
      * extensionality l. erewrite SAME; auto.
        specialize (PLN l). des.
        exploit Memory.max_ts_spec; eauto. i. des. auto.
      * extensionality l. erewrite SAME; auto.
        specialize (RLX l). des.
        exploit Memory.max_ts_spec; eauto. i. des. auto.
    + exploit Memory.get_ts; try apply GET; eauto. i. des.
      * clarify.
      * left. eapply TimeFacts.lt_le_lt; eauto.
  - destruct msg_src as [from msg]. exploit Memory.max_ts_spec; eauto. i. des.
    esplits.
    + erewrite SAME; eauto.
    + eauto.
Qed.
