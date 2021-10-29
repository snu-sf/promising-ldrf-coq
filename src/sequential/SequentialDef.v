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

Require Import Event.

Set Implicit Arguments.



Definition get_machine_event (e: ProgramEvent.t): MachineEvent.t :=
  match e with
  | ProgramEvent.syscall e => MachineEvent.syscall e
  | ProgramEvent.failure => MachineEvent.failure
  | _ => MachineEvent.silent
  end.

Definition is_atomic_event (e: ProgramEvent.t): bool :=
  match e with
  | ProgramEvent.silent | ProgramEvent.failure => false
  | ProgramEvent.syscall _ | ProgramEvent.fence _ _ => true
  | ProgramEvent.read _ _ ord => Ordering.le Ordering.plain ord
  | ProgramEvent.write _ _ ord => Ordering.le Ordering.plain ord
  | ProgramEvent.update _ _ _ ordr ordw =>
    Ordering.le Ordering.plain ordr && Ordering.le Ordering.plain ordw
  end.

Definition is_accessing (e: ProgramEvent.t): option Loc.t :=
  match e with
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.syscall _ | ProgramEvent.fence _ _ => None
  | ProgramEvent.read l _ _ | ProgramEvent.write l _ _ | ProgramEvent.update l _ _ _ _ => Some l
  end.

Definition is_release (e: ProgramEvent.t): bool :=
  match e with
  | ProgramEvent.syscall _ => true
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.read _ _ _ => false
  | ProgramEvent.fence _ ord | ProgramEvent.write _ _ ord | ProgramEvent.update _ _ _ _ ord => Ordering.le Ordering.strong_relaxed ord
  end.

Definition is_acquire (e: ProgramEvent.t): bool :=
  match e with
  | ProgramEvent.syscall _ => true
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.write _ _ _ => false
  | ProgramEvent.read _ _ ord | ProgramEvent.update _ _ _ ord _ => Ordering.le Ordering.acqrel ord
  | ProgramEvent.fence ordr ordw => Ordering.le Ordering.seqcst ordw || Ordering.le Ordering.acqrel ordr
  end.


Module Perm.
  Variant t: Type :=
  | low
  | high
  .

  Definition meet (p0 p1: t): t :=
    match p0, p1 with
    | high, high => high
    | _, _ => low
    end.

  Definition join (p0 p1: t): t :=
    match p0, p1 with
    | low, low => low
    | _, _ => high
    end.

  Definition le (p0 p1: t): bool :=
    match p0, p1 with
    | low, _ => true
    | _, high => true
    | _, _ => false
    end.

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct x, y, z; ss.
  Qed.

  Lemma meet_le_l p0 p1:
    le (meet p0 p1) p0.
  Proof.
    destruct p0, p1; ss.
  Qed.

  Lemma meet_le_r p0 p1:
    le (meet p0 p1) p1.
  Proof.
    destruct p0, p1; ss.
  Qed.

  Lemma meet_spec p0 p1 p
        (LE0: le p p0)
        (LE1: le p p1)
    :
      le p (meet p0 p1).
  Proof.
    destruct p, p0, p1; ss.
  Qed.

  Lemma meet_mon_l p0 p1 p
        (LE: le p0 p1)
    :
      le (meet p0 p) (meet p1 p).
  Proof.
    destruct p, p0, p1; ss.
  Qed.

  Lemma meet_mon_r p0 p1 p
        (LE: le p0 p1)
    :
      le (meet p p0) (meet p p1).
  Proof.
    destruct p, p0, p1; ss.
  Qed.

  Lemma join_ge_l p0 p1:
    le p0 (join p0 p1).
  Proof.
    destruct p0, p1; ss.
  Qed.

  Lemma join_ge_r p0 p1:
    le p1 (join p0 p1).
  Proof.
    destruct p0, p1; ss.
  Qed.

  Lemma join_spec p0 p1 p
        (LE0: le p0 p)
        (LE1: le p1 p)
    :
      le (join p0 p1) p.
  Proof.
    destruct p, p0, p1; ss.
  Qed.

  Lemma join_mon_l p0 p1 p
        (LE: le p0 p1)
    :
      le (join p0 p) (join p1 p).
  Proof.
    destruct p, p0, p1; ss.
  Qed.

  Lemma join_mon_r p0 p1 p
        (LE: le p0 p1)
    :
      le (join p p0) (join p p1).
  Proof.
    destruct p, p0, p1; ss.
  Qed.
End Perm.


Module Perms.
  Definition t := Loc.t -> Perm.t.

  Definition meet (p0 p1: t): t :=
    fun loc => Perm.meet (p0 loc) (p1 loc).

  Definition join (p0 p1: t): t :=
    fun loc => Perm.join (p0 loc) (p1 loc).

  Definition update (loc: Loc.t) (p: Perm.t) (ps: t): t :=
    fun loc' => if Loc.eq_dec loc loc' then p else ps loc'.

  Definition acquired (p: t) (p_acq: t): Loc.t -> bool :=
    fun loc => Perm.le (p_acq loc) (p loc).

  Definition le (p0 p1: t): Prop :=
    forall loc, Perm.le (p0 loc) (p1 loc).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Lemma meet_le_l p0 p1:
    le (meet p0 p1) p0.
  Proof.
    ii. eapply Perm.meet_le_l; eauto.
  Qed.

  Lemma meet_le_r p0 p1:
    le (meet p0 p1) p1.
  Proof.
    ii. eapply Perm.meet_le_r; eauto.
  Qed.

  Lemma meet_spec p0 p1 p
        (LE0: le p p0)
        (LE1: le p p1)
    :
      le p (meet p0 p1).
  Proof.
    ii. eapply Perm.meet_spec; eauto.
  Qed.

  Lemma meet_mon_l p0 p1 p
        (LE: le p0 p1)
    :
      le (meet p0 p) (meet p1 p).
  Proof.
    ii. eapply Perm.meet_mon_l; eauto.
  Qed.

  Lemma meet_mon_r p0 p1 p
        (LE: le p0 p1)
    :
      le (meet p p0) (meet p p1).
  Proof.
    ii. eapply Perm.meet_mon_r; eauto.
  Qed.

  Lemma join_ge_l p0 p1:
    le p0 (join p0 p1).
  Proof.
    ii. eapply Perm.join_ge_l; eauto.
  Qed.

  Lemma join_ge_r p0 p1:
    le p1 (join p0 p1).
  Proof.
    ii. eapply Perm.join_ge_r; eauto.
  Qed.

  Lemma join_spec p0 p1 p
        (LE0: le p0 p)
        (LE1: le p1 p)
    :
      le (join p0 p1) p.
  Proof.
    ii. eapply Perm.join_spec; eauto.
  Qed.

  Lemma join_mon_l p0 p1 p
        (LE: le p0 p1)
    :
      le (join p0 p) (join p1 p).
  Proof.
    ii. eapply Perm.join_mon_l; eauto.
  Qed.

  Lemma join_mon_r p0 p1 p
        (LE: le p0 p1)
    :
      le (join p p0) (join p p1).
  Proof.
    ii. eapply Perm.join_mon_r; eauto.
  Qed.
End Perms.


Module Flag.
  Variant t :=
  | written
  | unwritten
  .

  Definition meet (f0 f1: t): t :=
    match f0, f1 with
    | written, written => written
    | _, _ => unwritten
    end.

  Definition le (f0 f1: t): bool :=
    match f0, f1 with
    | unwritten, _ => true
    | _, unwritten => false
    | _, written => true
    end.

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct x, y, z; ss.
  Qed.

  Lemma meet_le_l f0 f1:
    le (meet f0 f1) f0.
  Proof.
    destruct f0, f1; ss.
  Qed.

  Lemma meet_le_r f0 f1:
    le (meet f0 f1) f1.
  Proof.
    destruct f0, f1; ss.
  Qed.

  Lemma meet_spec f0 f1 f
        (LE0: le f f0)
        (LE1: le f f1)
    :
      le f (meet f0 f1).
  Proof.
    destruct f, f0, f1; ss.
  Qed.

  Lemma meet_mon_l f0 f1 f
        (LE: le f0 f1)
    :
      le (meet f0 f) (meet f1 f).
  Proof.
    destruct f, f0, f1; ss.
  Qed.

  Lemma meet_mon_r f0 f1 f
        (LE: le f0 f1)
    :
      le (meet f f0) (meet f f1).
  Proof.
    destruct f, f0, f1; ss.
  Qed.
End Flag.


Module Flags.
  Definition t := Loc.t -> Flag.t.

  Definition write (loc: Loc.t) (f: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then Flag.written else (f loc').

  Definition update (loc: Loc.t) (f: Flag.t) (fs: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then f else (fs loc').

  Definition meet (f0 f1: t): t :=
    fun loc => Flag.meet (f0 loc) (f1 loc).

  Definition le (f0 f1: t): Prop :=
    forall loc, Flag.le (f0 loc) (f1 loc).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Lemma meet_le_l f0 f1:
    le (meet f0 f1) f0.
  Proof.
    ii. eapply Flag.meet_le_l; eauto.
  Qed.

  Lemma meet_le_r f0 f1:
    le (meet f0 f1) f1.
  Proof.
    ii. eapply Flag.meet_le_r; eauto.
  Qed.

  Lemma meet_spec f0 f1 f
        (LE0: le f f0)
        (LE1: le f f1)
    :
      le f (meet f0 f1).
  Proof.
    ii. eapply Flag.meet_spec; eauto.
  Qed.

  Lemma meet_mon_l f0 f1 f
        (LE: le f0 f1)
    :
      le (meet f0 f) (meet f1 f).
  Proof.
    ii. eapply Flag.meet_mon_l; eauto.
  Qed.

  Lemma meet_mon_r f0 f1 f
        (LE: le f0 f1)
    :
      le (meet f f0) (meet f f1).
  Proof.
    ii. eapply Flag.meet_mon_r; eauto.
  Qed.
End Flags.


Module ValueMap.
  Definition t := Loc.t -> Const.t.

  Definition write (loc: Loc.t) (v: Const.t) (vs: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then v else (vs loc').

  Definition read (loc: Loc.t) (vs: t) := vs loc.

  Definition acquire (cond: Loc.t -> bool) (vs_acq: t) (vs: t): t :=
    fun loc => if (cond loc) then (vs loc) else (vs_acq loc).

  Definition release (vs_rel: t) (vs: t): Flags.t :=
    fun loc => if (Const.le (vs_rel loc) (vs loc))
               then Flag.written else Flag.unwritten.

  Definition le (vs0 vs1: t): Prop :=
    forall loc, Const.le (vs0 loc) (vs1 loc).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.
End ValueMap.


Module SeqMemory.
  Record t :=
    mk {
        value_map: ValueMap.t;
        flags: Flags.t;
      }.

  Definition read (loc: Loc.t) (m: t): Const.t :=
    ValueMap.read loc m.(value_map).

  Definition write (loc: Loc.t) (v: Const.t) (m: t): t :=
    mk (ValueMap.write loc v m.(value_map)) (Flags.write loc m.(flags)).

  Definition can_acquire (f: Flags.t) (m: t): Prop :=
    Flags.le f m.(flags).

  Definition acquire (cond: Loc.t -> bool) (vs_acq: ValueMap.t) (m: t): t :=
    mk (ValueMap.acquire cond vs_acq m.(value_map)) m.(flags).

  Definition release (f_rel: Flags.t) (vs_rel: ValueMap.t) (m: t): t :=
    mk m.(value_map) (Flags.meet (Flags.meet f_rel (ValueMap.release vs_rel m.(value_map))) m.(flags)).

  Variant update:
    forall
      (loc: Loc.t)
      (v_old: Const.t) (v_new: Const.t)
      (f_old: Flag.t) (f_new: Flag.t) (m0 m1: t), Prop :=
  | update_intro
      loc v_old v_new f_old f_new m0
      (VAL: Const.le v_old (m0.(value_map) loc))
      (FLAG: Flag.le f_old (m0.(flags) loc))
    :
      update
        loc v_old v_new f_old f_new
        m0
        (mk (ValueMap.write loc v_new m0.(value_map)) (Flags.update loc f_new m0.(flags)))
  .

  Definition le (m0 m1: t): Prop :=
    ValueMap.le m0.(value_map) m1.(value_map) /\ Flags.le m0.(flags) m1.(flags).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. split; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. inv H0. split; etrans; eauto.
  Qed.
End SeqMemory.


Module SeqEvent.
  Record input :=
    mk_input {
        in_accessed: option (Loc.t * Const.t * Flag.t);
        in_acquired: option unit;
        in_released: option (ValueMap.t * Flags.t);
      }.

  Record output :=
    mk_output {
        out_accessed: option (Perm.t * Const.t * Flag.t);
        out_acquired: option (Perms.t * ValueMap.t * Flags.t);
        out_released: option (Perms.t);
      }.

  Definition wf_input (e: ProgramEvent.t) (i: input): Prop :=
    (<<UPDATE: forall loc,
        ((exists v_old f_old, i.(in_accessed) = Some (loc, v_old, f_old)) <-> is_accessing e = Some loc)>>) /\
    (<<ACQUIRE: is_some i.(in_acquired) <-> is_acquire e>>) /\
    (<<RELEASE: is_some i.(in_released) <-> is_release e>>)
  .

  Definition wf_output (e: ProgramEvent.t) (o: output): Prop :=
    (<<UPDATE: is_some o.(out_accessed) <-> is_some (is_accessing e)>>) /\
    (<<ACQUIRE: is_some o.(out_acquired) <-> is_acquire e>>) /\
    (<<RELEASE: is_some o.(out_released) <-> is_release e>>)
  .

  Lemma wf_input_le e0 e1 i
        (EVENT: ProgramEvent.le e0 e1)
    :
      wf_input e0 i <-> wf_input e1 i.
  Proof.
    unfold wf_input. destruct e0, e1; ss; des; clarify.
  Qed.

  Lemma wf_output_le e0 e1 o
        (EVENT: ProgramEvent.le e0 e1)
    :
      wf_output e0 o <-> wf_output e1 o.
  Proof.
    unfold wf_output. destruct e0, e1; ss; des; clarify.
  Qed.

  Variant step_update:
    forall (i: option (Loc.t * Const.t * Flag.t))(o: option (Perm.t * Const.t * Flag.t))
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_update_none
      p m
    :
      step_update
        None None
        p m p m
  | step_update_some
      loc v_old f_old p_new v_new f_new
      p0 m0 p1 m1
      (PERM: p1 = Perms.update loc p_new p0)
      (MEM: SeqMemory.update loc v_old v_new f_old f_new m0 m1)
    :
      step_update
        (Some (loc, v_old, f_old)) (Some (p_new, v_new, f_new))
        p0 m0 p1 m1
  .

  Variant step_acquire:
    forall (i: option unit) (o: option (Perms.t * ValueMap.t * Flags.t))
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_acquire_none
      p m
    :
      step_acquire
        None None
        p m p m
  | step_acquire_some
      p_acq v_acq f_acq
      p0 m0 p1 m1
      (ACQ: SeqMemory.can_acquire f_acq m0)
      (PERM: p1 = Perms.join p0 p_acq)
      (MEM: m1 = SeqMemory.acquire (Perms.acquired p0 p_acq) v_acq m0)
    :
      step_acquire
        (Some tt) (Some (p_acq, v_acq, f_acq))
        p0 m0 p1 m1
  .

  Variant step_release:
    forall (i: option (ValueMap.t * Flags.t)) (o: option Perms.t)
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_release_none
      p m
    :
      step_release
        None None
        p m p m
  | step_release_some
      p_rel v_rel f_rel
      p0 m0 p1 m1
      (PERM: p1 = Perms.meet p0 p_rel)
      (MEM: m1 = SeqMemory.release f_rel v_rel m0)
    :
      step_release
        (Some (v_rel, f_rel)) (Some p_rel)
        p0 m0 p1 m1
  .

  Variant step:
    forall (i: input) (o: output)
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_intro
      i o p0 m0 p1 m1 p2 m2 p3 m3
      (UPD: step_update i.(in_accessed) o.(out_accessed) p0 m0 p1 m1)
      (ACQ: step_acquire i.(in_acquired) o.(out_acquired) p1 m1 p2 m2)
      (REL: step_release i.(in_released) o.(out_released) p2 m2 p3 m3)
    :
      step i o p0 m0 p3 m3
  .
End SeqEvent.


Module SeqState.
Section LANG.
  Variable lang: language.

  Record t :=
    mk {
        state: lang.(Language.state);
        memory: SeqMemory.t;
      }.

  Variant na_local_step (p: Perms.t):
    forall (e: MachineEvent.t)
           (pe: ProgramEvent.t)
           (m0: SeqMemory.t)
           (m1: SeqMemory.t), Prop :=
  | na_local_step_silent
      m
    :
      na_local_step
        p
        (MachineEvent.silent) (ProgramEvent.silent)
        m m
  | na_local_step_read
      m
      loc val ord
      (ORD: Ordering.le ord Ordering.na)
      (VAL: Perm.le Perm.high (p loc) -> Const.le val (SeqMemory.read loc m))
    :
      na_local_step
        p
        (MachineEvent.silent) (ProgramEvent.read loc val ord)
        m m
  | na_local_step_write
      m0 m1 e
      loc val ord
      (ORD: Ordering.le ord Ordering.na)
      (MEM: SeqMemory.write loc val m0 = m1)
      (PERM: e = if Perm.le Perm.high (p loc) then MachineEvent.silent else MachineEvent.failure)
    :
      na_local_step
        p
        e (ProgramEvent.write loc val ord)
        m0 m1
  | na_local_step_failure
      m
    :
      na_local_step
        p
        (MachineEvent.failure) (ProgramEvent.failure)
        m m
  | na_local_step_update
      m
      loc valr valw ordr ordw
      (ORD: __guard__(Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na))
    :
      na_local_step
        p
        (MachineEvent.failure) (ProgramEvent.update loc valr valw ordr ordw)
        m m
  .

  Variant na_step (p: Perms.t): MachineEvent.t -> t -> t -> Prop :=
  | na_step_intro
      st0 st1 m0 m1 e pe
      (LANG: lang.(Language.step) pe st0 st1)
      (LOCAL: na_local_step p e pe m0 m1)
    :
      na_step p e (mk st0 m0) (mk st1 m1)
  .

  Variant na_opt_step (p: Perms.t): MachineEvent.t -> t -> t -> Prop :=
  | na_opt_step_some
      e st0 st1
      (STEP: na_step p e st0 st1)
    :
      na_opt_step p e st0 st1
  | na_opt_step_none
      st0
    :
      na_opt_step p MachineEvent.silent st0 st0
  .
End LANG.
End SeqState.


Module Oracle.
  Record t :=
    mk {
        _t: Type;
        _step: ProgramEvent.t -> SeqEvent.input -> SeqEvent.output -> _t -> _t -> Prop;
        _o: _t;
      }.

  Variant step: forall (pe: ProgramEvent.t) (i: SeqEvent.input) (o: SeqEvent.output) (o0 o1: t), Prop :=
  | step_intro
      pe i o
      _t (_step: ProgramEvent.t -> SeqEvent.input -> SeqEvent.output -> _t -> _t -> Prop)
      (x0 x1: _t)
      (STEP: _step pe i o x0 x1)
    :
      step pe i o (@mk _t _step x0) (@mk _t _step x1)
  .

  Definition progress pe o0: Prop :=
    forall i (WF: SeqEvent.wf_input pe i),
    exists o o1, (<<STEP: step pe i o o0 o1>>) /\ (<<WF: SeqEvent.wf_output pe o>>).

  Variant _wf (wf: t -> Prop): t -> Prop :=
  | wf_intro
      (o0: t)
      (WF: forall pe i o o1 (STEP: step pe i o o0 o1),
          (<<INPUT: SeqEvent.wf_input pe i>>) /\
          (<<OUTPUT: SeqEvent.wf_output pe o>>) /\
          (<<ORACLE: wf o1>>))
      (LOAD: forall loc ord,
          exists val, progress (ProgramEvent.read loc val ord) o0)
      (STORE: forall loc ord val,
          progress (ProgramEvent.write loc val ord) o0)
      (FENCE: forall ordr ordw,
          progress (ProgramEvent.fence ordr ordw) o0)
    :
      _wf wf o0
  .

  Lemma wf_mon: monotone1 _wf.
  Proof.
    ii. inv IN. econs; eauto. i.
    exploit WF; eauto. i. des. splits; auto.
  Qed.
  #[export] Hint Resolve wf_mon: paco.

  Definition wf := paco1 _wf bot1.
End Oracle.


Module SeqThread.
Section LANG.
  Variable lang: language.

  Record t :=
    mk {
        state: SeqState.t lang;
        perm: Perms.t;
        oracle: Oracle.t;
      }.

  Variant na_step:
    forall (e: MachineEvent.t) (th0: t) (th1: t), Prop :=
  | na_step_intro
      p o e st0 st1
      (STEP: SeqState.na_step p e st0 st1)
    :
      na_step e (mk st0 p o) (mk st1 p o)
  .

  Lemma na_state_steps_na_steps p o st0 st1
        (STEPS: rtc (SeqState.na_step p MachineEvent.silent) st0 st1)
    :
      rtc (na_step MachineEvent.silent) (mk st0 p o) (mk st1 p o).
  Proof.
    induction STEPS.
    - refl.
    - econs; eauto. econs; eauto.
  Qed.

  Variant at_step:
    forall (e: ProgramEvent.t) (i: SeqEvent.input) (o: SeqEvent.output)
           (th0: t) (th1: t), Prop :=
  | at_step_intro
      e0 e1 i o
      st0 st1 p0 p1 o0 o1 m0 m1
      (LANG: lang.(Language.step) e1 st0 st1)
      (EVENT: ProgramEvent.le e0 e1)
      (ORACLE: Oracle.step e0 i o o0 o1)
      (MEM: SeqEvent.step i o p0 m0 p1 m1)
    :
      at_step e0 i o (mk (SeqState.mk _ st0 m0) p0 o0) (mk (SeqState.mk _ st1 m1) p1 o1)
  .

  Variant step (e: MachineEvent.t) (th0: t) (th1: t): Prop :=
  | step_na_step
      (STEP: na_step e th0 th1)
  | step_at_step
      pe i o
      (EVENT: e = get_machine_event pe)
      (STEP: at_step pe i o th0 th1)
  .

  Definition failure (th0: t): Prop :=
    exists th1, (<<FAILURE: step MachineEvent.failure th0 th1>>).
End LANG.
End SeqThread.


Section SIMULATION.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition sim_seq_terminal_case
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st_tgt0.(SeqState.state)),
    exists st_src1,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<TERMINAL_SRC: lang_src.(Language.is_terminal) st_src1.(SeqState.state)>>) /\
      (<<TERMINAL: sim_terminal st_src1.(SeqState.state) st_tgt0.(SeqState.state)>>) /\
      (<<MEM: SeqMemory.le st_tgt0.(SeqState.memory) st_src1.(SeqState.memory)>>).

  Definition sim_seq_na_step_case
             (sim_seq:
                forall
                  (p0: Perms.t)
                  (st_src0: SeqState.t lang_src)
                  (st_tgt0: SeqState.t lang_tgt), Prop)
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall st_tgt1 e (STEP_TGT: SeqState.na_step p0 e st_tgt0 st_tgt1),
    exists st_src1 st_src2,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<STEP: SeqState.na_opt_step p0 e st_src1 st_src2>>) /\
      (<<SIM: sim_seq p0 st_src2 st_tgt1>>).

  Definition sim_seq_at_step_case
             (sim_seq:
                forall
                  (p0: Perms.t)
                  (st_src0: SeqState.t lang_src)
                  (st_tgt0: SeqState.t lang_tgt), Prop)
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall st_tgt1 e_tgt
           (STEP_TGT: lang_tgt.(Language.step) e_tgt st_tgt0.(SeqState.state) st_tgt1)
           (ATOMIC: is_atomic_event e_tgt),
    exists st_src1 st_src2 e_src,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<STEP: lang_src.(Language.step) e_src st_src1.(SeqState.state) st_src2>>) /\
      (<<EVENT: ProgramEvent.le e_src e_tgt>>) /\
      (<<SIM: forall i o p1 mem_tgt
                     (INPUT: SeqEvent.wf_input e_tgt i)
                     (OUTPUT: SeqEvent.wf_output e_tgt o)
                     (STEP_TGT: SeqEvent.step i o p0 st_tgt0.(SeqState.memory) p1 mem_tgt),
          exists mem_src,
            (<<STEP_SRC: SeqEvent.step i o p0 st_src1.(SeqState.memory) p1 mem_src>>) /\
            (<<SIM: sim_seq p1
                            (SeqState.mk _ st_src2 mem_src)
                            (SeqState.mk _ st_tgt1 mem_tgt)>>)>>).

  Definition sim_seq_partial_case
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall o (WF: Oracle.wf o),
    exists th,
      (<<STEPS: rtc (SeqThread.step MachineEvent.silent) (SeqThread.mk st_src0 p0 o) th>>) /\
      ((<<FLAG: Flags.le st_tgt0.(SeqState.memory).(SeqMemory.flags) th.(SeqThread.state).(SeqState.memory).(SeqMemory.flags)>>) \/ (<<FAILURE: SeqThread.failure th>>)).

  Definition sim_seq_failure_case
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src): Prop :=
    forall o (WF: Oracle.wf o),
    exists th,
      (<<STEPS: rtc (SeqThread.step MachineEvent.silent) (SeqThread.mk st_src0 p0 o) th>>) /\
      (<<FAILURE: SeqThread.failure th>>).


  Variant _sim_seq
          (sim_seq:
             forall
               (p0: Perms.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (p0: Perms.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | sim_seq_normal
      (TERMINAL: sim_seq_terminal_case p0 st_src0 st_tgt0)
      (NASTEP: sim_seq_na_step_case sim_seq p0 st_src0 st_tgt0)
      (ATSTEP: sim_seq_at_step_case sim_seq p0 st_src0 st_tgt0)
      (PARTIAL: sim_seq_partial_case p0 st_src0 st_tgt0)
  | sim_seq_failure
      (FAILURE: sim_seq_failure_case p0 st_src0)
  .

  Definition sim_seq := paco3 _sim_seq bot3.
  Arguments sim_seq: clear implicits.

  Lemma sim_seq_mon: monotone3 _sim_seq.
  Proof.
    ii. inv IN.
    { econs 1; eauto.
      { ii. exploit NASTEP; eauto. i. des. esplits; eauto. }
      { ii. exploit ATSTEP; eauto. i. des. esplits; eauto.
        i. hexploit SIM; eauto. i. des. esplits; eauto. }
    }
    { econs 2; eauto. }
  Qed.


  Lemma sim_seq_partial_imm p st_src st_tgt
        (FLAGS: Flags.le st_tgt.(SeqState.memory).(SeqMemory.flags) st_src.(SeqState.memory).(SeqMemory.flags))
    :
      sim_seq_partial_case p st_src st_tgt.
  Proof.
    ii. esplits; [refl|]. left. auto.
  Qed.

  Lemma sim_seq_failure_imm p0 st_src0 st_tgt0 st_src1
        (FAILURE: SeqState.na_step p0 MachineEvent.failure st_src0 st_src1)
    :
      sim_seq p0 st_src0 st_tgt0.
  Proof.
    pfold. right. red. i. esplits; [refl|].
    econs. left. econs. eauto.
  Qed.

  Definition sim_seq_all (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state)): Prop :=
    forall p m,
      sim_seq
        p
        (SeqState.mk _ st_src m)
        (SeqState.mk _ st_tgt m).
End SIMULATION.
Arguments sim_seq [_] [_] _ _ _.
#[export] Hint Resolve sim_seq_mon: paco.





Require Import ITreeLang.
Require Import iCompatibility.

Section ADEQUACY.
  Variable R: Type.

  Definition sim_seq_itree (st_src: itree MemE.t R) (st_tgt: itree MemE.t R): Prop :=
    @sim_seq_all (lang R) (lang R) eq st_src st_tgt.

  Theorem adequacy_seq:
    sim_seq_itree <2= sim_itree eq.
  Proof.
  Admitted.
End ADEQUACY.
