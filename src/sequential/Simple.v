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


Program Instance option_rel_PreOrder A R `{@PreOrder A R}: PreOrder (option_rel R).
Next Obligation.
Proof.
  ii. destruct x; ss. refl.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.

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

Definition is_accessing (e: ProgramEvent.t): option (Loc.t * Const.t) :=
  match e with
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.syscall _ | ProgramEvent.fence _ _ => None
  | ProgramEvent.read l v _ | ProgramEvent.write l v _ | ProgramEvent.update l _ v _ _ => Some (l, v)
  end.

Definition is_updating (e: ProgramEvent.t): bool :=
  match e with
  | ProgramEvent.update _ _ _ _ _ => true
  | _ => false
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

Definition is_syscall (e: ProgramEvent.t): bool :=
  match e with
  | ProgramEvent.syscall _ => true
  | _ => false
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
  Definition t := bool.

  Definition meet (f0 f1: t): t := andb f0 f1.

  Definition join (f0 f1: t): t := orb f0 f1.

  Definition minus (f0 f1: t): t :=
    match f1 with
    | true => false
    | false => f0
    end.

  Definition le (f0 f1: t): bool := implb f0 f1.

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

  Lemma join_ge_l f0 f1:
    le f0 (join f0 f1).
  Proof.
    destruct f0, f1; ss.
  Qed.

  Lemma join_ge_r f0 f1:
    le f1 (join f0 f1).
  Proof.
    destruct f0, f1; ss.
  Qed.

  Lemma join_spec f0 f1 f
        (LE0: le f0 f)
        (LE1: le f1 f)
    :
      le (join f0 f1) f.
  Proof.
    destruct f, f0, f1; ss.
  Qed.

  Lemma join_mon_l f0 f1 f
        (LE: le f0 f1)
    :
      le (join f0 f) (join f1 f).
  Proof.
    destruct f, f0, f1; ss.
  Qed.

  Lemma join_mon_r f0 f1 f
        (LE: le f0 f1)
    :
      le (join f f0) (join f f1).
  Proof.
    destruct f, f0, f1; ss.
  Qed.

  Lemma minus_mon_l f0 f1 f
        (LE: le f1 f0)
    :
      le (minus f1 f) (minus f0 f).
  Proof.
    destruct f, f0, f1; ss.
  Qed.

  Lemma minus_mon_r f0 f1 f
        (LE: le f1 f0)
    :
      le (minus f f0) (minus f f1).
  Proof.
    destruct f, f0, f1; ss.
  Qed.
End Flag.


Module Flags.
  Definition t := Loc.t -> Flag.t.

  Definition top: t := fun _ => true.

  Definition bot: t := fun _ => false.

  Definition is_empty (f: t): Prop := forall loc, f loc = false.

  Definition update (loc: Loc.t) (f: Flag.t) (fs: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then f else (fs loc').

  Definition add (loc: Loc.t) (f: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then true else (f loc').

  Definition sub (loc: Loc.t) (f: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then false else (f loc').

  Definition sub_opt (loc: option Loc.t) (f: t): t :=
    match loc with
    | Some loc => sub loc f
    | None => f
    end.

  Definition meet (f0 f1: t): t :=
    fun loc => Flag.meet (f0 loc) (f1 loc).

  Definition join (f0 f1: t): t :=
    fun loc => Flag.join (f0 loc) (f1 loc).

  Definition minus (f0 f1: t): t :=
    fun loc => Flag.minus (f0 loc) (f1 loc).

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

  Lemma top_spec f:
    le f top.
  Proof.
    ii. destruct f; ss.
  Qed.

  Lemma bot_spec f:
    le bot f.
  Proof.
    ii. destruct f; ss.
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

  Lemma join_ge_l f0 f1:
    le f0 (join f0 f1).
  Proof.
    ii. eapply Flag.join_ge_l; eauto.
  Qed.

  Lemma join_ge_r f0 f1:
    le f1 (join f0 f1).
  Proof.
    ii. eapply Flag.join_ge_r; eauto.
  Qed.

  Lemma join_spec f0 f1 f
        (LE0: le f0 f)
        (LE1: le f1 f)
    :
      le (join f0 f1) f.
  Proof.
    ii. eapply Flag.join_spec; eauto.
  Qed.

  Lemma join_mon_l f0 f1 f
        (LE: le f0 f1)
    :
      le (join f0 f) (join f1 f).
  Proof.
    ii. eapply Flag.join_mon_l; eauto.
  Qed.

  Lemma join_mon_r f0 f1 f
        (LE: le f0 f1)
    :
      le (join f f0) (join f f1).
  Proof.
    ii. eapply Flag.join_mon_r; eauto.
  Qed.

  Lemma join_top_l f: join f top = top.
  Proof.
    extensionality x.
    unfold join, top; ss.
    unfold Flag.join. destruct (f x); ss.
  Qed.

  Lemma join_top_r f: join f top = top.
  Proof.
    extensionality x.
    unfold join, top; ss.
    unfold join. destruct (f x); ss.
  Qed.

  Lemma minus_mon_l f0 f1 f
        (LE: le f1 f0)
    :
      le (minus f1 f) (minus f0 f).
  Proof.
    ii. eapply Flag.minus_mon_l; eauto.
  Qed.

  Lemma minus_mon_r f0 f1 f
        (LE: le f1 f0)
    :
      le (minus f f0) (minus f f1).
  Proof.
    ii. eapply Flag.minus_mon_r; eauto.
  Qed.
End Flags.


Module ValueMap.
  Definition t := Loc.t -> Const.t.

  Definition write (loc: Loc.t) (v: Const.t) (vs: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then v else (vs loc').

  Definition read (loc: Loc.t) (vs: t) := vs loc.

  Definition acquire (cond: Loc.t -> bool) (vs_acq: t) (vs: t): t :=
    fun loc => if (cond loc) then (vs loc) else (vs_acq loc).

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
    mk (ValueMap.write loc v m.(value_map))
       (Flags.update loc true m.(flags))
  .

  Variant acquire (cond: Loc.t -> bool) (v_acq: ValueMap.t):
    forall (m_before: t) (f: Flags.t) (m_after: t), Prop :=
  | acquire_intro
      m
    :
      acquire
        cond
        v_acq
        m
        (m.(flags))
        (mk (ValueMap.acquire cond v_acq m.(value_map)) m.(flags))
  .

  Variant release:
    forall (m: t) (f_rel: Flags.t) (v_rel: ValueMap.t) (m_after: t), Prop :=
  | release_intro
      m
    :
      release
        m
        (m.(flags))
        (m.(value_map))
        (mk m.(value_map) Flags.bot)
  .

  Variant update:
    forall
      (loc: Loc.t) (v_new: Const.t)
      (m_before: t)
      (v: Const.t) (f: Flag.t)
      (m_after: t), Prop :=
  | update_intro
      m loc v_new
    :
      update
        loc
        v_new
        m
        (m.(value_map) loc)
        (m.(flags) loc)
        (mk (ValueMap.write loc v_new m.(value_map))
            (Flags.update loc false m.(flags)))
  .
End SeqMemory.


Module Oracle.
  Record input :=
    mk_input {
        in_access: option (Loc.t * Const.t * Flag.t);
        in_acquire: option (unit);
        in_release: option (unit);
      }.

  Record output :=
    mk_output {
        out_access: option (Perm.t);
        out_acquire: option (Perms.t * ValueMap.t);
        out_release: option (Perms.t);
      }.

  Definition wf_input (e: ProgramEvent.t) (i: input): Prop :=
    (<<UPDATE: forall loc,
        ((exists v_old f_old, i.(in_access) = Some (loc, v_old, f_old)) <-> exists v_new, is_accessing e = Some (loc, v_new))>>) /\
    (<<ACQUIRE: is_some i.(in_acquire) <-> is_acquire e>>) /\
    (<<RELEASE: is_some i.(in_release) <-> is_release e>>)
  .

  Definition wf_output (e: ProgramEvent.t) (o: output): Prop :=
    (<<UPDATE: is_some o.(out_access) <-> is_accessing e>>) /\
    (<<ACQUIRE: is_some o.(out_acquire) <-> is_acquire e>>) /\
    (<<RELEASE: is_some o.(out_release) <-> is_release e>>)
  .

  Definition in_access_le (i0 i1: (Loc.t * Const.t * Flag.t)): Prop :=
    match i0, i1 with
    | (l0, v0, f0), (l1, v1, f1) =>
      (<<LOC: l0 = l1>>) /\ (<<VAL: Const.le v0 v1>>) /\
      (<<FLAG: Flag.le f0 f1>>)
    end.

  Definition in_acquire_le (i0 i1: unit): Prop := i0 = i1.

  Definition in_release_le (i0 i1: unit): Prop := i0 = i1.

  Definition input_le (i0 i1: input): Prop :=
    (<<ACCESS: option_rel in_access_le i0.(in_access) i1.(in_access)>>) /\
    (<<ACQUIRE: option_rel in_acquire_le i0.(in_acquire) i1.(in_acquire)>>) /\
    (<<RELEASE: option_rel in_release_le i0.(in_release) i1.(in_release)>>)
  .

  Program Instance in_access_le_PreOrder: PreOrder in_access_le.
  Next Obligation.
  Proof.
    ii. unfold in_access_le. des_ifs. splits; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold in_access_le in *. des_ifs. des. splits; etrans; eauto.
  Qed.

  Program Instance in_acquire_le_PreOrder: PreOrder in_acquire_le.

  Program Instance in_release_le_PreOrder: PreOrder in_release_le.

  Program Instance input_le_PreOrder: PreOrder input_le.
  Next Obligation.
  Proof.
    ii. unfold input_le. splits; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold input_le in *. des. splits; etrans; eauto.
  Qed.


  Record t :=
    mk {
        _t: Type;
        _step: ProgramEvent.t -> input -> output -> _t -> _t -> Prop;
        _o: _t;
      }.

  Variant step: forall (pe: ProgramEvent.t) (i: input) (o: output) (o0 o1: t), Prop :=
  | step_intro
      pe i o
      _t (_step: ProgramEvent.t -> input -> output -> _t -> _t -> Prop)
      (x0 x1: _t)
      (STEP: _step pe i o x0 x1)
    :
      step pe i o (@mk _t _step x0) (@mk _t _step x1)
  .

  Definition progress pe o0: Prop :=
    forall i (WF: wf_input pe i),
    exists o o1, (<<STEP: step pe i o o0 o1>>) /\ (<<WF: wf_output pe o>>).

  Variant _wf (wf: t -> Prop): t -> Prop :=
  | wf_intro
      (o0: t)
      (WF: forall pe i o o1 (STEP: step pe i o o0 o1),
          (<<INPUT: wf_input pe i>>) /\
          (<<OUTPUT: wf_output pe o>>) /\
          (<<ORACLE: wf o1>>))
      (LOAD: forall loc ord, exists val,
            progress (ProgramEvent.read loc val ord) o0 /\
            forall valw ordw, progress (ProgramEvent.update loc val valw ord ordw) o0)
      (STORE: forall loc ord val,
          progress (ProgramEvent.write loc val ord) o0)
      (FENCE: forall ordr ordw,
          progress (ProgramEvent.fence ordr ordw) o0)
      (SYSCALL: forall e, progress (ProgramEvent.syscall e) o0)
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


Module SeqEvent.
  Record input :=
    mk_input {
        in_access: option (Loc.t * Const.t * Flag.t * Const.t);
        in_acquire: option (Flags.t);
        in_release: option (ValueMap.t * Flags.t);
      }.

  Definition in_access_written (i: option (Loc.t * Const.t * Flag.t * Const.t)): Flags.t :=
    match i with
    | Some (loc, _, true, _) => Flags.add loc Flags.bot
    | _ => Flags.bot
    end.

  Definition in_release_written (i: option (ValueMap.t * Flags.t)): Flags.t :=
    match i with
    | Some (_, f) => f
    | _ => Flags.bot
    end.

  Definition written (i: input): Flags.t :=
    Flags.join (in_access_written i.(in_access)) (in_release_written i.(in_release)).

  Definition get_oracle_input (i: input): Oracle.input :=
    Oracle.mk_input
      (option_map (fun '(loc, v_old, f, v_new) => (loc, v_old, f)) i.(in_access))
      (option_map (fun _ => tt) i.(in_acquire))
      (option_map (fun _ => tt) i.(in_release))
  .

  Variant in_access_match: forall (d0 d1: Flags.t) (i_src i_tgt: option (Loc.t * Const.t * Flag.t * Const.t)), Prop :=
  | in_access_match_none
      d0 d1
      (FLAG: Flags.le d0 d1)
    :
      in_access_match d0 d1 None None
  | in_access_match_some
      d0 d1
      l v_src v_tgt f_src f_tgt v_new_src v_new_tgt
      (VAL: Const.le v_tgt v_src)
      (FLAG: Flag.le (Flag.join f_tgt (d0 l)) f_src)
      (DEFERRED: forall loc (LOC: loc <> l), Flag.le (d0 loc) (d1 loc))
    :
      in_access_match d0 d1 (Some (l, v_src, f_src, v_new_src)) (Some (l, v_tgt, f_tgt, v_new_tgt))
  .

  Variant in_acquire_match: forall (d0 d1: Flags.t) (i_src i_tgt: option (Flags.t)), Prop :=
  | in_acquire_match_none
      d0 d1
      (FLAG: Flags.le d0 d1)
    :
      in_acquire_match d0 d1 None None
  | in_acquire_match_some
      d0 d1
      f_src f_tgt
      (FLAG: Flags.le (Flags.join f_tgt d0) f_src)
    :
      in_acquire_match d0 d1 (Some f_src) (Some f_tgt)
  .

  Variant in_release_match: forall (d0 d1: Flags.t) (i_src i_tgt: option (ValueMap.t * Flags.t)), Prop :=
  | in_release_match_none
      d0 d1
      (FLAG: Flags.le d0 d1)
    :
      in_release_match d0 d1 None None
  | in_release_match_some
      d0 d1
      v_src v_tgt f_src f_tgt
      (VAL: forall loc (UNDEFERRED: d1 loc = false), Const.le (v_tgt loc) (v_src loc))
      (DEFERRED: Flags.le (Flags.join f_tgt d0) (Flags.join f_src d1))
    :
      in_release_match d0 d1 (Some (v_src, f_src)) (Some (v_tgt, f_tgt))
  .

  Variant input_match (d0 d3: Flags.t) (i_src i_tgt: input): Prop :=
  | input_match_intro
      d1 d2
      (ACCESS: in_access_match d0 d1 i_src.(in_access) i_tgt.(in_access))
      (ACQUIRE: in_acquire_match d1 d2 i_src.(in_acquire) i_tgt.(in_acquire))
      (RELEASE: in_release_match d2 d3 i_src.(in_release) i_tgt.(in_release))
    :
      input_match d0 d3 i_src i_tgt
  .

  Lemma in_access_match_mon d_before0 d_before1 d_after0 d_after1
        i_src i_tgt
        (MATCH: in_access_match d_before1 d_after0 i_src i_tgt)
        (BEFORE: Flags.le d_before0 d_before1)
        (AFTER: Flags.le d_after0 d_after1)
    :
      in_access_match d_before0 d_after1 i_src i_tgt.
  Proof.
    inv MATCH; econs; eauto.
    { etrans; eauto. etrans; eauto. }
    { etrans; eauto. eapply Flag.join_mon_r. eauto. }
    { i. transitivity (d_before1 loc); auto. transitivity (d_after0 loc); auto. }
  Qed.

  Lemma in_acquire_match_mon d_before0 d_before1 d_after0 d_after1
        i_src i_tgt
        (MATCH: in_acquire_match d_before1 d_after0 i_src i_tgt)
        (BEFORE: Flags.le d_before0 d_before1)
        (AFTER: Flags.le d_after0 d_after1)
    :
      in_acquire_match d_before0 d_after1 i_src i_tgt.
  Proof.
    inv MATCH; econs; eauto.
    { etrans; eauto. etrans; eauto. }
    { etrans; eauto. eapply Flags.join_mon_r. eauto. }
  Qed.

  Lemma in_release_match_mon d_before0 d_before1 d_after0 d_after1
        i_src i_tgt
        (MATCH: in_release_match d_before1 d_after0 i_src i_tgt)
        (BEFORE: Flags.le d_before0 d_before1)
        (AFTER: Flags.le d_after0 d_after1)
    :
      in_release_match d_before0 d_after1 i_src i_tgt.
  Proof.
    inv MATCH; econs; eauto.
    { etrans; eauto. etrans; eauto. }
    { i. eapply VAL; eauto. specialize (AFTER loc).
      destruct (d_after0 loc), (d_after1 loc); ss. }
    { transitivity (Flags.join f_tgt d_before1).
      { eapply Flags.join_mon_r; eauto. }
      etrans; eauto.
      { eapply Flags.join_mon_r; eauto. }
    }
  Qed.

  Lemma input_match_mon d_before0 d_before1 d_after0 d_after1 i_src i_tgt
        (MATCH: input_match d_before1 d_after0 i_src i_tgt)
        (DBEFORE: Flags.le d_before0 d_before1)
        (DAFTER: Flags.le d_after0 d_after1)
    :
      input_match d_before0 d_after1 i_src i_tgt.
  Proof.
    inv MATCH. econs.
    { eapply in_access_match_mon; eauto. refl. }
    { eapply in_acquire_match_mon; eauto; refl. }
    { eapply in_release_match_mon; eauto. refl. }
  Qed.

  Lemma in_access_match_bot d i
    :
      in_access_match Flags.bot d i i.
  Proof.
    destruct i as [[[[] ?] ?]|]; econs; eauto; ss.
    { refl. }
    { eapply Flag.join_spec; eauto. refl. }
  Qed.

  Lemma in_acquire_match_bot d i
    :
      in_acquire_match Flags.bot d i i.
  Proof.
    destruct i as [|]; econs; eauto; ss.
    { eapply Flags.join_spec; eauto; ss. refl. }
  Qed.

  Lemma in_release_match_bot d i
    :
      in_release_match Flags.bot d i i.
  Proof.
    destruct i as [[]|]; econs; eauto; ss.
    { i. refl. }
    { eapply Flags.join_mon_r. ss. }
  Qed.

  Lemma input_match_bot d i
    :
      input_match Flags.bot d i i.
  Proof.
    econs.
    { eapply in_access_match_bot. }
    { eapply in_acquire_match_bot. }
    { eapply in_release_match_bot. }
  Qed.

  Definition wf_input (e: ProgramEvent.t) (i: input): Prop :=
    (<<UPDATE: forall loc v_new,
        ((exists v_old f_old, i.(in_access) = Some (loc, v_old, f_old, v_new)) <-> (is_accessing e = Some (loc, v_new)))>>) /\
    (<<ACQUIRE: is_some i.(in_acquire) <-> is_acquire e>>) /\
    (<<RELEASE: is_some i.(in_release) <-> is_release e>>)
  .

  (* Lemma wf_input_event_le e0 e1 i *)
  (*       (EVENT: ProgramEvent.le e0 e1) *)
  (*   : *)
  (*     wf_input e0 i <-> wf_input e1 i. *)
  (* Proof. *)
  (*   unfold wf_input. destruct e0, e1; ss; des; clarify. *)
  (*   { split; i; des; splits; i; split; eauto. *)
  (*     { i. eapply UPDATE in H. des. inv H. eauto. } *)
  (*     { i. eapply UPDATE. des. inv H. eauto. } *)
  (*     { i. eapply UPDATE in H. des. inv H. eauto. } *)
  (*     { i. eapply UPDATE. des. inv H. eauto. } *)
  (*   } *)
  (*   { split; i; des; splits; i; split; eauto. *)
  (*     { i. eapply UPDATE in H. des. inv H. eauto. } *)
  (*     { i. eapply UPDATE. des. inv H. eauto. } *)
  (*     { i. eapply UPDATE in H. des. inv H. eauto. } *)
  (*     { i. eapply UPDATE. des. inv H. eauto. } *)
  (*   } *)
  (* Qed. *)

  Variant step_update:
    forall (i: option (Loc.t * Const.t * Flag.t * Const.t)) (o: option (Perm.t))
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_update_none
      p m
    :
      step_update
        None None
        p m p m
  | step_update_some
      loc v f p_new v_new
      p0 m0 p1 m1
      (PERM: p1 = Perms.update loc p_new p0)
      (MEM: SeqMemory.update loc v_new m0 v f m1)
    :
      step_update
        (Some (loc, v, f, v_new)) (Some (p_new))
        p0 m0 p1 m1
  .

  Variant step_acquire:
    forall (i: option (Flags.t)) (o: option (Perms.t * ValueMap.t))
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_acquire_none
      p m
    :
      step_acquire
        None None
        p m p m
  | step_acquire_some
      p_acq v_acq f
      p0 m0 p1 m1
      (PERM: p1 = Perms.join p0 p_acq)
      (MEM: SeqMemory.acquire (Perms.acquired p0 p_acq) v_acq m0 f m1)
    :
      step_acquire
        (Some f) (Some (p_acq, v_acq))
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
      (MEM: SeqMemory.release m0 f_rel v_rel m1)
    :
      step_release
        (Some (v_rel, f_rel)) (Some p_rel)
        p0 m0 p1 m1
  .

  Variant step:
    forall (i: input) (o: Oracle.output)
           (p0: Perms.t) (m0: SeqMemory.t) (p1: Perms.t) (m1: SeqMemory.t), Prop :=
  | step_intro
      i o p0 m0 p1 m1 p2 m2 p3 m3
      (UPD: step_update i.(in_access) o.(Oracle.out_access) p0 m0 p1 m1)
      (ACQ: step_acquire i.(in_acquire) o.(Oracle.out_acquire) p1 m1 p2 m2)
      (REL: step_release i.(in_release) o.(Oracle.out_release) p2 m2 p3 m3)
    :
      step i o p0 m0 p3 m3
  .

  Lemma step_update_match i_src i_tgt d0 d1 o p0 m0 p1 m1
        (STEP: step_update i_src o p0 m0 p1 m1)
        (MATCH: in_access_match d0 d1 i_src i_tgt)
    :
      in_access_match (Flags.join d0 m0.(SeqMemory.flags)) (Flags.join d1 m1.(SeqMemory.flags)) i_src i_tgt.
  Proof.
    inv STEP.
    { inv MATCH. econs; eauto. eapply Flags.join_mon_l. auto. }
    inv MEM. ss. inv MATCH. econs; eauto.
    { unfold Flags.join. destruct f_tgt, (d0 loc), (SeqMemory.flags m0 loc); ss. }
    { i. unfold Flags.join, Flags.update. des_ifs.
      eapply Flag.join_mon_l. auto. }
  Qed.

  Lemma step_acquire_match i_src i_tgt d0 d1 o p0 m0 p1 m1
        (STEP: step_acquire i_src o p0 m0 p1 m1)
        (MATCH: in_acquire_match d0 d1 i_src i_tgt)
    :
      in_acquire_match (Flags.join d0 m0.(SeqMemory.flags)) (Flags.join d1 m1.(SeqMemory.flags)) i_src i_tgt.
  Proof.
    inv STEP.
    { inv MATCH. econs; eauto. eapply Flags.join_mon_l. auto. }
    inv MEM. ss. inv MATCH. econs; eauto.
    eapply Flags.join_spec.
    { etrans; eauto. eapply Flags.join_ge_l. }
    { eapply Flags.join_spec; eauto.
      { etrans; eauto. eapply Flags.join_ge_r. }
      { refl. }
    }
  Qed.

  Lemma step_release_match i_src i_tgt d0 d1 o p0 m0 p1 m1
        (STEP: step_release i_src o p0 m0 p1 m1)
        (MATCH: in_release_match d0 d1 i_src i_tgt)
    :
      in_release_match (Flags.join d0 m0.(SeqMemory.flags)) (Flags.join d1 m1.(SeqMemory.flags)) i_src i_tgt.
  Proof.
    inv STEP.
    { inv MATCH. econs; eauto. eapply Flags.join_mon_l. auto. }
    inv MEM. ss. inv MATCH. econs; eauto.
    { i. eapply VAL; eauto.
      unfold Flags.join in UNDEFERRED. destruct (d1 loc); ss. }
    { eapply Flags.join_spec.
      { etrans; [eapply Flags.join_ge_l|]. etrans; [eauto|].
        eapply Flags.join_spec.
        { eapply Flags.join_ge_l. }
        { etrans; [|eapply Flags.join_ge_r]. eapply Flags.join_ge_l. }
      }
      { eapply Flags.join_spec.
        { etrans; [eapply Flags.join_ge_r|]. etrans; [eauto|].
          eapply Flags.join_spec.
          { eapply Flags.join_ge_l. }
          { etrans; [|eapply Flags.join_ge_r]. eapply Flags.join_ge_l. }
        }
        { eapply Flags.join_ge_l. }
      }
    }
  Qed.

  Lemma step_input_match i_src i_tgt d0 d1 o p0 m0 p1 m1
        (STEP: step i_src o p0 m0 p1 m1)
        (MATCH: input_match d0 d1 i_src i_tgt)
    :
      input_match (Flags.join d0 m0.(SeqMemory.flags)) (Flags.join d1 m1.(SeqMemory.flags)) i_src i_tgt.
  Proof.
    inv STEP. inv MATCH. econs.
    { eapply step_update_match; eauto. }
    { eapply step_acquire_match; eauto. }
    { eapply step_release_match; eauto. }
  Qed.

  Lemma step_update_inj
        p m
        i1 o1 p1 m1
        i2 o2 p2 m2
        (STEP1: step_update i1 o1 p m p1 m1)
        (STEP2: step_update i2 o2 p m p2 m2)
        (INPUT: forall loc1 v_old1 f1 v_new1
                  loc2 v_old2 f2 v_new2
                  (IN1: i1 = Some (loc1, v_old1, f1, v_new1))
                  (IN2: i2 = Some (loc2, v_old2, f2, v_new2)),
            loc1 = loc2 /\ v_new1 = v_new2)
        (OUTPUT: o1 = o2):
    i1 = i2 /\ p1 = p2 /\ m1 = m2.
  Proof.
    subst. inv STEP1; inv STEP2; ss.
    exploit INPUT; eauto. i. des. subst.
    inv MEM. inv MEM0. ss.
  Qed.

  Lemma step_acquire_inj
        p m
        i1 o1 p1 m1
        i2 o2 p2 m2
        (STEP1: step_acquire i1 o1 p m p1 m1)
        (STEP2: step_acquire i2 o2 p m p2 m2)
        (OUTPUT: o1 = o2):
    i1 = i2 /\ p1 = p2 /\ m1 = m2.
  Proof.
    subst. inv STEP1; inv STEP2; ss.
    inv MEM. inv MEM0. ss.
  Qed.

  Lemma step_release_inj
        p m
        i1 o1 p1 m1
        i2 o2 p2 m2
        (STEP1: step_release i1 o1 p m p1 m1)
        (STEP2: step_release i2 o2 p m p2 m2)
        (OUTPUT: o1 = o2):
    i1 = i2 /\ p1 = p2 /\ m1 = m2.
  Proof.
    subst. inv STEP1; inv STEP2; ss.
    inv MEM. inv MEM0. ss.
  Qed.

  Lemma step_inj
        p m
        i1 o1 p1 m1
        i2 o2 p2 m2
        (STEP1: step i1 o1 p m p1 m1)
        (STEP2: step i2 o2 p m p2 m2)
        (INPUT: forall loc1 v_old1 f1 v_new1
                  loc2 v_old2 f2 v_new2
                  (IN1: i1.(in_access) = Some (loc1, v_old1, f1, v_new1))
                  (IN2: i2.(in_access) = Some (loc2, v_old2, f2, v_new2)),
            loc1 = loc2 /\ v_new1 = v_new2)
        (OUTPUT: o1 = o2):
    i1 = i2 /\ p1 = p2 /\ m1 = m2.
  Proof.
    destruct i1, i2. inv STEP1. inv STEP2. ss.
    exploit step_update_inj; [exact UPD|exact UPD0|..]; eauto. i. des. subst.
    exploit step_acquire_inj; [exact ACQ|exact ACQ0|..]; eauto. i. des. subst.
    exploit step_release_inj; [exact REL|exact REL0|..]; eauto. i. des. subst. ss.
  Qed.

  Lemma step_update_inj_perms
        p
        i1 o1 m1 p1 m1'
        i2 o2 m2 p2 m2'
        (STEP1: step_update i1 o1 p m1 p1 m1')
        (STEP2: step_update i2 o2 p m2 p2 m2')
        (INPUT: forall loc1 v_old1 f1 v_new1
                  loc2 v_old2 f2 v_new2
                  (IN1: i1 = Some (loc1, v_old1, f1, v_new1))
                  (IN2: i2 = Some (loc2, v_old2, f2, v_new2)),
            loc1 = loc2)
        (OUTPUT: o1 = o2):
    p1 = p2.
  Proof.
    subst. inv STEP1; inv STEP2; ss.
    exploit INPUT; eauto. i. des. subst.
    inv MEM. inv MEM0. ss.
  Qed.

  Lemma step_acquire_inj_perms
        p
        i1 o1 m1 p1 m1'
        i2 o2 m2 p2 m2'
        (STEP1: step_acquire i1 o1 p m1 p1 m1')
        (STEP2: step_acquire i2 o2 p m2 p2 m2')
        (OUTPUT: o1 = o2):
    p1 = p2.
  Proof.
    subst. inv STEP1; inv STEP2; ss.
  Qed.

  Lemma step_release_inj_perms
        p
        i1 o1 m1 p1 m1'
        i2 o2 m2 p2 m2'
        (STEP1: step_release i1 o1 p m1 p1 m1')
        (STEP2: step_release i2 o2 p m2 p2 m2')
        (OUTPUT: o1 = o2):
    p1 = p2.
  Proof.
    subst. inv STEP1; inv STEP2; ss.
  Qed.

  Lemma step_inj_perms
        p
        i1 o1 m1 p1 m1'
        i2 o2 m2 p2 m2'
        (STEP1: step i1 o1 p m1 p1 m1')
        (STEP2: step i2 o2 p m2 p2 m2')
        (INPUT: forall loc1 v_old1 f1 v_new1
                  loc2 v_old2 f2 v_new2
                  (IN1: i1.(in_access) = Some (loc1, v_old1, f1, v_new1))
                  (IN2: i2.(in_access) = Some (loc2, v_old2, f2, v_new2)),
            loc1 = loc2)
        (OUTPUT: o1 = o2):
    p1 = p2.
  Proof.
    destruct i1, i2. inv STEP1. inv STEP2. ss.
    exploit step_update_inj_perms; [exact UPD|exact UPD0|..]; eauto. i. subst.
    exploit step_acquire_inj_perms; [exact ACQ|exact ACQ0|..]; eauto. i. subst.
    exploit step_release_inj_perms; [exact REL|exact REL0|..]; eauto.
  Qed.
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



Module SeqThread.
Section LANG.
  Variable lang: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang -> SeqState.t lang -> Prop.

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
      (STEP: state_step p e st0 st1)
    :
      na_step e (mk st0 p o) (mk st1 p o)
  .

  Lemma na_state_steps_na_steps p o st0 st1
        (STEPS: rtc (state_step p MachineEvent.silent) st0 st1)
    :
      rtc (na_step MachineEvent.silent) (mk st0 p o) (mk st1 p o).
  Proof.
    induction STEPS.
    - refl.
    - econs; eauto. econs; eauto.
  Qed.

  Variant at_step:
    forall (e: ProgramEvent.t) (i: SeqEvent.input) (o: Oracle.output)
           (th0: t) (th1: t), Prop :=
  | at_step_intro
      e0 e1 i0 i1 o
      st0 st1 p0 p1 o0 o1 m0 m1
      (LANG: lang.(Language.step) e1 st0 st1)
      (ATOMIC: is_atomic_event e1)
      (EVENT: ProgramEvent.le e0 e1)
      (INPUT: Oracle.input_le i0 (SeqEvent.get_oracle_input i1))
      (ORACLE: Oracle.step e0 i0 o o0 o1)
      (MEM: SeqEvent.step i1 o p0 m0 p1 m1)
      (INPUT: SeqEvent.wf_input e1 i1)
    :
      at_step e1 i1 o (mk (SeqState.mk _ st0 m0) p0 o0) (mk (SeqState.mk _ st1 m1) p1 o1)
  .

  Definition failure (th0: t): Prop :=
    exists th1, (<<FAILURE: na_step MachineEvent.failure th0 th1>>).

  Inductive steps: forall
      (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output))
      (th0 th1: t), Prop :=
  | steps_base
      th
    :
      steps [] th th
  | steps_na_step
      tr th0 th1 th2
      (STEP: na_step MachineEvent.silent th0 th1)
      (STEPS: steps tr th1 th2)
    :
      steps tr th0 th2
  | steps_at_step
      e i o tr th0 th1 th2
      (STEP: at_step e i o th0 th1)
      (STEPS: steps tr th1 th2)
    :
      steps ((e, i, o)::tr) th0 th2
  .

  Inductive writing_trace: forall
      (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output))
      (w: Flags.t), Prop :=
  | writing_trace_base
    :
      writing_trace [] Flags.bot
  | writing_trace_cons
      tr e i o w
      (TRACE: writing_trace tr w)
      (UPDATE: ~ is_updating e)
      (ACQUIRE: ~ is_acquire e)
    :
      writing_trace ((e, i, o)::tr) (Flags.join (SeqEvent.written i) w)
  .

  (* Lemma writing_trace_mon d0 d1 tr w *)
  (*       (DEFERRED: Flags.le d0 d1) *)
  (*       (WRITING: writing_trace d1 tr w) *)
  (*   : *)
  (*     writing_trace d0 tr w. *)
  (* Proof. *)
  (*   revert d0 DEFERRED. induction WRITING. *)
  (*   { econs 1. } *)
  (*   { econs 2. *)
  (*     { eapply IHWRITING. eapply Flags.minus_mon_l; eauto. } *)
  (*     { eauto. } *)
  (*     { i. eapply ACCESS in SOME. des; auto. *)
  (*       specialize (DEFERRED loc). destruct (d loc), (d0 loc); ss. auto. } *)
  (*   } *)
  (* Qed. *)
End LANG.
End SeqThread.


Section SIMULATION.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition sim_seq_terminal_case
             (p0: Perms.t) (d0: Flags.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st_tgt0.(SeqState.state)),
    exists st_src1,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<TERMINAL_SRC: lang_src.(Language.is_terminal) st_src1.(SeqState.state)>>) /\
      (<<TERMINAL: sim_terminal st_src1.(SeqState.state) st_tgt0.(SeqState.state)>>) /\
      (<<VALUE: ValueMap.le st_tgt0.(SeqState.memory).(SeqMemory.value_map) st_src1.(SeqState.memory).(SeqMemory.value_map)>>) /\
      (<<FLAG: Flags.le (Flags.join d0 st_tgt0.(SeqState.memory).(SeqMemory.flags)) st_src1.(SeqState.memory).(SeqMemory.flags)>>)
  .

  Definition sim_seq_na_step_case
             (sim_seq:
                forall
                  (p0: Perms.t) (d0: Flags.t)
                  (st_src0: SeqState.t lang_src)
                  (st_tgt0: SeqState.t lang_tgt), Prop)
             (p0: Perms.t) (d0: Flags.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall st_tgt1 e (STEP_TGT: SeqState.na_step p0 e st_tgt0 st_tgt1),
    exists st_src1 st_src2,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<STEP: SeqState.na_opt_step p0 e st_src1 st_src2>>) /\
      (<<SIM: sim_seq p0 d0 st_src2 st_tgt1>>)
  .

  Definition sim_seq_at_step_case
             (sim_seq:
                forall
                  (p0: Perms.t) (d0: Flags.t)
                  (st_src0: SeqState.t lang_src)
                  (st_tgt0: SeqState.t lang_tgt), Prop)
             (p0: Perms.t) (d0: Flags.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall st_tgt1 e_tgt
           (STEP_TGT: lang_tgt.(Language.step) e_tgt st_tgt0.(SeqState.state) st_tgt1)
           (ATOMIC: is_atomic_event e_tgt),
    exists st_src1 st_src2 e_src,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<STEP: lang_src.(Language.step) e_src st_src1.(SeqState.state) st_src2>>) /\
      (<<EVENT: ProgramEvent.le e_tgt e_src>>) /\
      (<<SIM: forall i_tgt o p1 mem_tgt
                     (INPUT: SeqEvent.wf_input e_tgt i_tgt)
                     (OUTPUT: Oracle.wf_output e_tgt o)
                     (STEP_TGT: SeqEvent.step i_tgt o p0 st_tgt0.(SeqState.memory) p1 mem_tgt),
          exists i_src mem_src d1,
            (<<STEP_SRC: SeqEvent.step i_src o p0 st_src1.(SeqState.memory) p1 mem_src>>) /\
            (<<MATCH: SeqEvent.input_match d0 d1 i_src i_tgt>>) /\
            (<<INPUT: SeqEvent.wf_input e_src i_src>>) /\
            (<<SIM: sim_seq p1
                            d1
                            (SeqState.mk _ st_src2 mem_src)
                            (SeqState.mk _ st_tgt1 mem_tgt)>>)>>)
  .

  Definition sim_seq_partial_case
             (p0: Perms.t) (d0: Flags.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall o (WF: Oracle.wf o),
    exists th tr w,
      (<<STEPS: SeqThread.steps (@SeqState.na_step _) tr (SeqThread.mk st_src0 p0 o) th>>) /\
      (<<TRACE: SeqThread.writing_trace tr w>>) /\
      ((<<FLAGS: Flags.le (Flags.join d0 st_tgt0.(SeqState.memory).(SeqMemory.flags)) (Flags.join w th.(SeqThread.state).(SeqState.memory).(SeqMemory.flags))>>) \/ (<<FAILURE: SeqThread.failure (@SeqState.na_step _) th>>))
  .

  Definition sim_seq_failure_case
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src): Prop :=
    forall o (WF: Oracle.wf o),
    exists th tr w,
      (<<STEPS: SeqThread.steps (@SeqState.na_step _) tr (SeqThread.mk st_src0 p0 o) th>>) /\
      (<<TRACE: SeqThread.writing_trace tr w>>) /\
      (<<FAILURE: SeqThread.failure (@SeqState.na_step _) th>>)
  .


  Variant _sim_seq
          (sim_seq:
             forall
               (p0: Perms.t) (d0: Flags.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (p0: Perms.t) (d0: Flags.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | sim_seq_normal
      (TERMINAL: sim_seq_terminal_case p0 d0 st_src0 st_tgt0)
      (NASTEP: sim_seq_na_step_case sim_seq p0 d0 st_src0 st_tgt0)
      (ATSTEP: sim_seq_at_step_case sim_seq p0 d0 st_src0 st_tgt0)
      (PARTIAL: sim_seq_partial_case p0 d0 st_src0 st_tgt0)
  | sim_seq_failure
      (FAILURE: sim_seq_failure_case p0 st_src0)
  .

  Definition sim_seq := paco4 _sim_seq bot4.
  Arguments sim_seq: clear implicits.

  Lemma sim_seq_mon: monotone4 _sim_seq.
  Proof.
    ii. inv IN.
    { econs 1; eauto.
      { ii. exploit NASTEP; eauto. i. des. esplits; eauto. }
      { ii. exploit ATSTEP; eauto. i. des. esplits; eauto.
        i. hexploit SIM; eauto. i. des. esplits; eauto. }
    }
    { econs 2; eauto. }
  Qed.


  Lemma sim_seq_partial_imm p d st_src st_tgt
        (FLAGS: Flags.le (Flags.join d st_tgt.(SeqState.memory).(SeqMemory.flags)) st_src.(SeqState.memory).(SeqMemory.flags))
    :
      sim_seq_partial_case p d st_src st_tgt.
  Proof.
    ii. esplits; [econs 1|econs|]; eauto.
  Qed.

  Lemma sim_seq_failure_imm p0 d st_src0 st_tgt0 st_src1
        (FAILURE: SeqState.na_step p0 MachineEvent.failure st_src0 st_src1)
    :
      sim_seq p0 d st_src0 st_tgt0.
  Proof.
    pfold. right. red. i. esplits; [econs 1|econs|].
    red. esplits. econs. eauto.
  Qed.

  Definition sim_seq_all (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state)): Prop :=
    forall p m,
      sim_seq
        p Flags.bot
        (SeqState.mk _ st_src m)
        (SeqState.mk _ st_tgt m).
End SIMULATION.
Arguments sim_seq [_] [_] _ _ _.
#[export] Hint Resolve sim_seq_mon: paco.





Require Import ITreeLang.
Require Import iCompatibility.

Section ADEQUACY.
  Variable R_src R_tgt: Type.
  Variable sim_val: R_src -> R_tgt -> Prop.

  Definition sim_seq_itree (st_src: itree MemE.t R_src) (st_tgt: itree MemE.t R_tgt): Prop :=
    @sim_seq_all (lang R_src) (lang R_tgt) (sim_terminal sim_val) st_src st_tgt.

  Theorem adequacy_seq:
    sim_seq_itree <2= sim_itree sim_val.
  Proof.
  Admitted.
End ADEQUACY.
