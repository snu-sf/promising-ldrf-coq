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

Module Perm.
  Variant t: Type :=
  | none
  | full
  .

  Definition le (p0 p1: t): bool :=
    match p0, p1 with
    | none, _ => true
    | _, full => true
    | _, _ => false
    end.
End Perm.

Variant flag :=
| unwritten
| written
| promised
.

Definition flag_le (f_src f_tgt: flag): bool :=
  match f_src, f_tgt with
  | written, _ => true
  | unwritten, unwritten => true
  | unwritten, promised => true
  | promised, promised => true
  | _, _ => false
  end.

Program Instance flag_le_PreOrder: PreOrder flag_le.
Next Obligation.
Proof.
  ii. destruct x; ss.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss.
Qed.

Definition Perms := Loc.t -> Perm.t.

Module SeqCell.
   Definition t := (Const.t * flag)%type.

   Definition le (c0 c1: t): Prop :=
     match c0, c1 with
     | (v0, f0), (v1, f1) => v0 = v1 /\ flag_le f0 f1
     end.

   Program Instance le_PreOrder: PreOrder le.
   Next Obligation.
   Proof.
     ii. destruct x; ss. split; auto. refl.
   Qed.
   Next Obligation.
   Proof.
     ii. destruct x, y, z; ss.
     des. subst. splits; auto. etrans; eauto.
   Qed.
End SeqCell.


Module SeqMemory.
  Definition t := Loc.t -> SeqCell.t.

  Definition update (loc: Loc.t) (val: Const.t) (m: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then (val, written) else (m loc').

  Definition le (m_src m_tgt: t): Prop :=
    forall loc, SeqCell.le (m_src loc) (m_tgt loc).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.
End SeqMemory.


Module SeqState.
Section LANG.
  Variable lang: language.

  Record t :=
    mk {
        state: lang.(Language.state);
        memory: SeqMemory.t;
      }.

  (* without oracle *)
  Variant na_local_step (p: Perms):
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
      (VAL: Perm.le Perm.full (p loc) -> fst (m loc) = val)
    :
      na_local_step
        p
        (MachineEvent.silent) (ProgramEvent.read loc val ord)
        m m
  | na_local_step_write
      m0 m1 e
      loc val ord
      (ORD: Ordering.le ord Ordering.na)
      (MEM: SeqMemory.update loc val m0 = m1)
      (PERM: e = if Perm.le Perm.full (p loc) then MachineEvent.silent else MachineEvent.failure)
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

  Variant na_step (p: Perms): MachineEvent.t -> t -> t -> Prop :=
  | na_step_intro
      st0 st1 m0 m1 e pe
      (LANG: lang.(Language.step) pe st0 st1)
      (LOCAL: na_local_step p e pe m0 m1)
    :
      na_step p e (mk st0 m0) (mk st1 m1)
  .

  Variant na_opt_step (p: Perms): MachineEvent.t -> t -> t -> Prop :=
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


Variant diff :=
| diff_rlx (* no change *)
| diff_acq
| diff_rel
| diff_reset
.

Definition diffs := Loc.t -> diff.

Definition update_mem
           (d: diffs) (v_diff: Loc.t -> Const.t) (m0: SeqMemory.t): SeqMemory.t :=
  fun loc =>
    match (d loc) with
    | diff_rlx | diff_rel => m0 loc
    | diff_acq | diff_reset => (v_diff loc, unwritten)
    end.

Definition update_perm (d: diffs) (p0: Perms): Perms :=
  fun loc =>
    match (d loc) with
    | diff_rlx | diff_reset => p0 loc
    | diff_acq => Perm.full
    | diff_rel => Perm.none
    end.

Definition match_mem (d: diffs) (mem_src mem_tgt: SeqMemory.t) :=
  forall loc,
    match (d loc) with
    | diff_rel | diff_reset => SeqCell.le (mem_src loc) (mem_tgt loc)
    | _ => True
    end.


Definition wf_diff_perms (d: diffs) (p: Perms): Prop :=
  forall loc,
    match (d loc), (p loc) with
    | diff_rlx, _ => True
    | diff_rel, Perm.full => True
    | diff_reset, Perm.full => True
    | diff_acq, Perm.none => True
    | _, _ => False
    end.

Definition wf_diff_event (d: diffs) (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.read loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_rel | diff_reset => False
      | diff_acq => Ordering.le Ordering.acqrel ord
      | diff_rlx => True
      end
  | ProgramEvent.write loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_acq | diff_reset => False
      | diff_rel => Ordering.le Ordering.acqrel ord
      | diff_rlx => True
      end
  | ProgramEvent.update loc _ _ ordr ordw =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_reset => False
      | diff_rel => Ordering.le Ordering.acqrel ordw
      | diff_acq => Ordering.le Ordering.acqrel ordr
      | diff_rlx => True
      end
  | ProgramEvent.fence ordr ordw =>
    forall loc',
      match (d loc') with
      | diff_reset => False
      | diff_rel => Ordering.le Ordering.acqrel ordw
      | diff_acq => Ordering.le Ordering.acqrel ordr
      | diff_rlx => True
      end
  | _ => True
  end.

Definition is_atomic_event (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.silent | ProgramEvent.failure => False
  | ProgramEvent.syscall _ | ProgramEvent.fence _ _ => True
  | ProgramEvent.read _ _ ord => Ordering.le Ordering.plain ord
  | ProgramEvent.write _ _ ord => Ordering.le Ordering.plain ord
  | ProgramEvent.update _ _ _ ordr ordw =>
    Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw
  end.


Section SIMULATION.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition _sim_seq
             (sim_seq:
                forall
                  (p0: Perms)
                  (st_src0: SeqState.t lang_src)
                  (st_tgt0: SeqState.t lang_tgt), Prop)
    :
      forall
        (p0: Perms)
        (st_src0: SeqState.t lang_src)
        (st_tgt0: SeqState.t lang_tgt), Prop :=
    fun p0 st_src0 st_tgt0 =>
      (<<TERMINAL:
         forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st_tgt0.(SeqState.state)),
         exists st_src1,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<TERMINAL_SRC: lang_src.(Language.is_terminal) st_src1.(SeqState.state)>>) /\
           (<<TERMINAL: sim_terminal st_src1.(SeqState.state) st_tgt0.(SeqState.state)>>)>>) /\
      (<<NASTEP:
         forall st_tgt1 e (STEP_TGT: SeqState.na_step p0 e st_tgt0 st_tgt1),
         exists st_src1 st_src2,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<STEP: SeqState.na_opt_step p0 e st_src1 st_src2>>) /\
           (<<SIM: sim_seq p0 st_src2 st_tgt1>>)>>) /\
      (<<ATSTEP:
         forall st_tgt1 e
                (STEP_TGT: lang_tgt.(Language.step) e st_tgt0.(SeqState.state) st_tgt1)
                (ATOMIC: is_atomic_event e),
         exists st_src1 st_src2,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<STEP: lang_src.(Language.step) e st_src1.(SeqState.state) st_src2>>) /\
           (<<SIM: forall d v_diff
                          (DIFF: wf_diff_event d e)
                          (PERM: wf_diff_perms d p0),
               (<<MEM: match_mem d st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
               (<<SIM: sim_seq (update_perm d p0)
                           (SeqState.mk _ st_src2 (update_mem d v_diff st_src1.(SeqState.memory)))
                           (SeqState.mk _ st_tgt1 (update_mem d v_diff st_tgt0.(SeqState.memory)))>>)>>)>>).

  Lemma sim_seq_mon: monotone3 _sim_seq.
  Proof.
    unfold _sim_seq. ii. des. esplits; eauto.
    { i. exploit NASTEP; eauto. i. des. esplits; eauto. }
    { i. exploit ATSTEP; eauto. i. des. esplits; eauto.
      i. exploit SIM; eauto. i. des. esplits; eauto. }
  Qed.

  Definition sim_seq := paco3 _sim_seq bot3.
End SIMULATION.
Arguments sim_seq [_] [_] _ _ _.
#[export] Hint Resolve sim_seq_mon: paco.





Module Oracle.
  Definition t: Type. Admitted.

  Definition step:
    forall (e: ProgramEvent.t)
           (d: diffs)
           (o0: t)
           (o1: t), Prop.
  Admitted.

  Lemma step_wf e d o0 o1
        (STEP: step e d o0 o1)
    :
      wf_diff_event d e.
  Admitted.
End Oracle.


Module SeqThread.
Section LANG.
  Variable lang: language.

  Record t :=
    mk {
        state: SeqState.t lang;
        perm: Perms;
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
End LANG.
End SeqThread.

Require Import ITreeLang.
Require Import iCompatibility.

Section ADEQUACY.
  Variable R: Type.

  Definition sim_seq_itree (st_src: itree MemE.t R) (st_tgt: itree MemE.t R): Prop :=
    forall p m,
      sim_seq eq p (SeqState.mk (lang R) st_src m) (SeqState.mk (lang R) st_tgt m).

  Theorem adequacy_seq:
    sim_seq_itree <2= sim_itree eq.
  Proof.
  Admitted.
End ADEQUACY.
