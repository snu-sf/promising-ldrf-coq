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
  Variant t :=
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
Definition flag := bool.

Module SeqMemory.
  Definition t := Loc.t -> Const.t * flag.

  Definition update (loc: Loc.t) (val: Const.t) (m: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then (val, true) else (m loc').
End SeqMemory.



Variant diff :=
| diff_rlx
| diff_rel (val: Const.t) (f: flag)
| diff_acq (val: Const.t)
| diff_relacq (valw: Const.t) (f: flag) (valr: Const.t)
.

Definition diffs := Loc.t -> diff.

Definition is_acq (d: diff): bool :=
  match d with
  | diff_acq _  => true
  | _ => false
  end.

Definition is_rel (d: diff): bool :=
  match d with
  | diff_rel _ _  => true
  | _ => false
  end.

Definition is_rlx (d: diff): bool :=
  match d with
  | diff_rlx => true
  | _ => false
  end.

Variant wf_diff (d: diffs): forall (e: ProgramEvent.t), Prop :=
| wf_diff_syscall
    e
  :
    wf_diff d (ProgramEvent.syscall e)
| wf_diff_fence
    ordr ordw
    (ACQ: forall loc (ORD: is_acq (d loc)), Ordering.le Ordering.acqrel ordr)
    (REL: forall loc (ORD: is_rel (d loc)), Ordering.le Ordering.acqrel ordw)
  :
    wf_diff d (ProgramEvent.fence ordr ordw)
| wf_diff_read
    loc val ord
    (REL: forall loc' (NEQ: loc' <> loc) (ORD: is_rel (d loc)), False)
    (ACQ: forall loc' (NEQ: loc' <> loc) (ORD: is_acq (d loc)),
        Ordering.le Ordering.acqrel ord)
    (NA: Ordering.le Ordering.plain ord)
  :
    wf_diff d (ProgramEvent.read loc val ord)
| wf_diff_write
    loc val ord
    (ACQ: forall loc' (NEQ: loc' <> loc) (ORD: is_acq (d loc)), False)
    (REL: forall loc' (NEQ: loc' <> loc) (ORD: is_rel (d loc)),
        Ordering.le Ordering.acqrel ord)
    (NA: Ordering.le Ordering.plain ord)
  :
    wf_diff d (ProgramEvent.write loc val ord)
| wf_diff_update
    loc valr valw ordr ordw
    (ACQ: forall loc' (NEQ: loc' <> loc) (ORD: is_acq (d loc)),
        Ordering.le Ordering.acqrel ordr)
    (REL: forall loc' (NEQ: loc' <> loc) (ORD: is_rel (d loc)),
        Ordering.le Ordering.acqrel ordw)
    (ORDR: Ordering.le Ordering.plain ordr)
    (ORDW: Ordering.le Ordering.plain ordw)
  :
    wf_diff d (ProgramEvent.update loc valr valw ordr ordw)
.

Definition Perms := Loc.t -> Perm.t.


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
      wf_diff d e.
  Admitted.
End Oracle.



Definition


Module SeqLocal.
  Variant step:
    forall (e: ProgramEvent.t)
           (m0: SeqMemory.t) (p0: Perms) (o0: Oracle)
           (m1: SeqMemory.t) (p1: Perms) (o1: Oracle), Prop :=
  .
End SeqLocal.



De



Module State.
Section LANG.
  Variable lang: language.

  Record t :=
    mk {
        state: lang.(Language.state);
        memory: SeqMemory.t;
        perm: Perms;
        oracle: Oracle;
      }.

  (* without oracle *)
  Variant na_local_step (p: Perms) (o: Oracle):
    forall (e: MachineEvent.t)
           (pe: ProgramEvent.t)
           (m0: SeqMemory.t)
           (m1: SeqMemory.t), Prop :=
  | na_local_step_silent
      m
    :
      na_local_step
        p o
        (MachineEvent.silent) (ProgramEvent.silent)
        m m
  | na_local_step_read
      m
      loc val ord
      (ORD: Ordering.le ord Ordering.na)
      (VAL: Perm.le Perm.full (p loc) -> fst (m loc) = val)
    :
      na_local_step
        p o
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
        p o
        e (ProgramEvent.write loc val ord)
        m0 m1
  | na_local_step_failure
      m
    :
      na_local_step
        p o
        (MachineEvent.failure) (ProgramEvent.failure)
        m m
  | na_local_step_update
      m
      loc valr valw ordr ordw
      (ORD: __guard__(Ordering.le ordr Ordering.na \/ Ordering.le ordw Ordering.na))
    :
      na_local_step
        p o
        (MachineEvent.failure) (ProgramEvent.update loc valr valw ordr ordw)
        m m
  .

  Variant na_step: MachineEvent.t -> t -> t -> Prop :=
  | na_step_intro
      p o
      st0 st1 m0 m1 e pe
      (LANG: lang.(Language.step) pe st0 st1)
      (LOCAL: na_local_step p o e pe m0 m1)
    :
      na_step e (mk st0 m0 p o) (mk st1 m1 p o)
  .

  Variant at_step: MachineEvent.t -> t -> t -> Prop :=
  | at_step_read
      st0 st1
      m0 p0 o0
      loc val ord
      m1 p1 o1
      (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st0 st1)
    :
      at_step MachineEvent.silent (mk st0 m0 p0 o0) (mk st1 m1 p1 o1)
  | at_step_write
      st0 st1
      m0 p0 o0
      loc val ord
      m1 p1 o1
      (STEP: lang.(Language.step) (ProgramEvent.write loc val ord) st0 st1)
    :
      at_step MachineEvent.silent (mk st0 m0 p0 o0) (mk st1 m1 p1 o1)
  | at_step_update
      st0 st1
      m0 p0 o0
      loc valr valw ordr ordw
      m1 p1 o1
      (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st0 st1)
    :
      at_step MachineEvent.silent (mk st0 m0 p0 o0) (mk st1 m1 p1 o1)
  | at_step_fence
      st0 st1
      m0 p0 o0
      ordr ordw
      m1 p1 o1
      (STEP: lang.(Language.step) (ProgramEvent.fence ordr ordw) st0 st1)
    :
      at_step MachineEvent.silent (mk st0 m0 p0 o0) (mk st1 m1 p1 o1)
  | at_step_syscall
      st0 st1
      m0 p0 o0
      e
      m1 p1 o1
      (STEP: lang.(Language.step) (ProgramEvent.syscall e) st0 st1)
    :
      at_step (MachineEvent.syscall e) (mk st0 m0 p0 o0) (mk st1 m1 p1 o1)
  .

  Local.program_step

ProgramEvent.t

  | na_step_read
      st0 st1
      m p o
      loc val ord
      (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st0 st1)
      (ORD: Ordering.le ord Ordering.na)
      (VAL: Perm.le Perm.full (p loc) -> fst (m loc) = val)
    :
      na_step MachineEvent.silent (mk st0 m p o) (mk st1 m p o)
  | na_step_write
      st0 st1
      m0 p o
      loc val ord
      m1 e
      (STEP: lang.(Language.step) (ProgramEvent.write loc val ord) st0 st1)
      (ORD: Ordering.le ord Ordering.na)
      (MEM: SeqMemory.update loc val m0 = m1)
      (PERM: e = if Perm.le Perm.full (p loc) then MachineEvent.silent else MachineEvent.failure)
    :
      na_step e (mk st0 m0 p o) (mk st1 m1 p o)
  .


  | na_step_write_race
      st0 st1
      m0 p o m1
      loc val ord
      (STEP: lang.(Language.step) (ProgramEvent.write loc val ord) st0 st1)
      (ORD: Ordering.le ord Ordering.na)
      (MEM: SeqMemory.update loc val m0 = m1)
    :
      na_step MachineEvent.silent (mk st0 m0 p o) (mk st1 m1 p o)
  .

  | na_step_racy_read
      st0 st1
      loc val ord
      (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st0 st1)
      (ORD: Ordering.le ord Ordering.na)
      m p o
    :
      na_step (mk st0 m p o) (mk st1 m p o)
  .


Ordering.t


  | na_step_silent
      st0 st1
      (STEP: lang.(Language.step) ProgramEvent.silent st0 st1)
      m p o
    :
      na_step (mk st0 m p o) (mk st1 m p o)
  .

ProgramEvent.t



Definition update_mem :=

Module Memory.
  Definition t := Loc.t -> Cell.t.


Memory.t

Variant mem_permission

ProgramEvent.t
