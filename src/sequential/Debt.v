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

Definition is_atomic_event (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.silent | ProgramEvent.failure => False
  | ProgramEvent.syscall _ | ProgramEvent.fence _ _ => True
  | ProgramEvent.read _ _ ord => Ordering.le Ordering.plain ord
  | ProgramEvent.write _ _ ord => Ordering.le Ordering.plain ord
  | ProgramEvent.update _ _ _ ordr ordw =>
    Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw
  end.

Definition is_accessing (e: ProgramEvent.t): option Loc.t :=
  match e with
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.syscall _ | ProgramEvent.fence _ _ => None
  | ProgramEvent.read loc _ _ | ProgramEvent.write loc _ _ | ProgramEvent.update loc _ _ _ _ => Some loc
  end.

Definition is_release_event (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.read _ _ _ => False
  | ProgramEvent.fence _ ord | ProgramEvent.write _ _ ord | ProgramEvent.update _ _ _ _ ord => Ordering.le Ordering.strong_relaxed ord
  end.

Definition is_acquire_event (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.silent | ProgramEvent.failure | ProgramEvent.write _ _ _ => False
  | ProgramEvent.read _ _ ord | ProgramEvent.update _ _ _ ord _ => Ordering.le Ordering.acqrel ord
  | ProgramEvent.fence ordr ordw => ordw = Ordering.seqcst  \/ Ordering.le Ordering.acqrel ordr
  end.


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

Module Perms.
  Definition t := Loc.t -> Perm.t.
End Perms.

Module Flag.
  Variant t :=
  | written
  | unwritten
  | debt
  .

  Definition le (f_tgt f_src: t): bool :=
    match f_tgt, f_src with
    | debt, _ => true
    | _, debt => false
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
End Flag.

Module Flags.
  Definition t := Loc.t -> Flag.t.

  Definition le (f_tgt f_src: t): Prop :=
    forall loc, Flag.le (f_tgt loc) (f_src loc).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.
End Flags.

Module SeqCell.
   Definition t := (Const.t * Flag.t)%type.

   Definition flag (c: t): Flag.t := snd c.

   Definition debt (c: t): t :=
     let (v, f) := c in (v, Flag.debt).

   Definition write (v: Const.t): t :=
     (v, Flag.written).

   Definition update (v1: Const.t) (c: t): t :=
     let (v0, f) := c in (v1, f).

   (* checked at final *)
   Definition le (c0 c1: t): Prop :=
     match c0, c1 with
     | (v0, f0), (v1, f1) => v0 = v1 /\ Flag.le f0 f1
     end.

   (* checked every moment *)
   Definition le_partial (c0 c1: t): Prop :=
     Flag.le (flag c0) (flag c1).

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

   Program Instance le_partial_PreOrder: PreOrder le_partial.
   Next Obligation.
   Proof.
     ii. unfold le_partial in *. refl.
   Qed.
   Next Obligation.
   Proof.
     ii. unfold le_partial in *. etrans; eauto.
   Qed.

   Lemma le_le_partial c0 c1 (LE: le c0 c1)
     :
       le_partial c0 c1.
   Proof.
     destruct c0, c1. ss. des; auto.
   Qed.

   Definition init (v: Const.t): t := (v, Flag.unwritten).

   Variant release: forall (c_before c_released c_after: t), Prop :=
   | release_normal
       c0 c1
       (LE: le c0 c1)
     :
       release c1 c0 c0
   | release_debt
       c0 c1
     :
       release c0 c1 (debt c0)
   .
End SeqCell.


Module SeqMemory.
  Definition t := Loc.t -> SeqCell.t.

  Definition flags (m: t): Flags.t := fun loc => snd (m loc).

  Definition update (loc: Loc.t) (c: SeqCell.t) (m: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then c else (m loc').

  Definition write (loc: Loc.t) (val: Const.t) (m: t): t :=
    update loc (SeqCell.write val) m.

  Definition le (m_tgt m_src: t): Prop :=
    forall loc, SeqCell.le (m_tgt loc) (m_src loc).

  Definition le_partial (m_tgt m_src: t): Prop :=
    Flags.le (flags m_tgt) (flags m_src).

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Program Instance le_partial_PreOrder: PreOrder le_partial.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.


  Lemma le_le_partial m_tgt m_src (LE: le m_tgt m_src)
    :
      le_partial m_tgt m_src.
  Proof.
    ii. eapply SeqCell.le_le_partial. auto.
  Qed.

  Definition init (vals: Loc.t -> Const.t): t :=
    fun loc => SeqCell.init (vals loc).

  Variant release: forall (m_before: t) (m_released: option t) (m_after: t), Prop :=
  | release_some
      m_before m_released m_after
      (RELEASE: forall loc, SeqCell.release (m_before loc) (m_released loc) (m_after loc))
    :
      release m_before (Some m_released) m_after
  | release_none
      m
    :
      release m None m
  .
End SeqMemory.


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
      (MEM: SeqMemory.write loc val m0 = m1)
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


Variant diff :=
| diff_none
| diff_rel
| diff_acq (v: Const.t)
.

Definition diffs := Loc.t -> diff.

Definition update_mem
           (d: diffs) (m0: SeqMemory.t): SeqMemory.t :=
  fun loc =>
    match (d loc) with
    | diff_none | diff_rel => m0 loc
    | diff_acq v1 => SeqCell.update v1 (m0 loc)
    end.

Definition update_perm (d: diffs) (p0: Perms.t): Perms.t :=
  fun loc =>
    match (d loc) with
    | diff_none => p0 loc
    | diff_acq _ => Perm.full
    | diff_rel => Perm.none
    end.


Definition wf_diff_perms (l: option Loc.t) (d: diffs) (p: Perms.t): Prop :=
  forall loc,
    match (d loc), (p loc) with
    | diff_none, _ => True
    | diff_rel, Perm.full => True
    | diff_acq _, Perm.none => True
    | diff_acq _, Perm.full => l = Some loc
    | _, _ => False
    end.

Definition wf_diff_event (d: diffs) (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.read loc val ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_rel => False
      | diff_acq _ => Ordering.le Ordering.acqrel ord
      | diff_none => True
      end
  | ProgramEvent.write loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_acq _ => False
      | diff_rel => Ordering.le Ordering.strong_relaxed ord
      | diff_none => True
      end
  | ProgramEvent.update loc _ _ ordr ordw =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_rel => Ordering.le Ordering.strong_relaxed ordw
      | diff_acq _ => Ordering.le Ordering.acqrel ordr
      | diff_none => True
      end
  | ProgramEvent.fence ordr ordw =>
    forall loc',
      match (d loc') with
      | diff_rel => Ordering.le Ordering.strong_relaxed ordw
      | diff_acq _ => Ordering.le Ordering.acqrel ordr
      | diff_none => True
      end
  | _ => True
  end.

Definition wf_released (m_released: option SeqMemory.t) (e: ProgramEvent.t): Prop :=
  match m_released with
  | Some _ => is_release_event e
  | None => ~ is_release_event e
  end.

Definition match_cell (l: option Loc.t) (c: option SeqCell.t) (m: SeqMemory.t): Prop :=
  match l, c with
  | Some l, Some c => SeqCell.le c (m l)
  | None, None => True
  | _, _ => False
  end.

Definition update_cell (l: option Loc.t) (c: option SeqCell.t) (m: SeqMemory.t): SeqMemory.t :=
  match l, c with
  | Some l, Some c => SeqMemory.update l c m
  | _, _ => m
  end.

Definition wf_cell (c: option SeqCell.t) (e: ProgramEvent.t): Prop :=
  match (is_accessing e) with
  | Some loc => is_some c
  | _ => ~ is_some c
  end.


Module Oracle.
  Definition t: Type. Admitted.

  Definition step:
    forall (p0: Perms.t)
           (e: ProgramEvent.t)
           (c0: option SeqCell.t)
           (d: diffs)
           (m_released: option SeqMemory.t)
           (o0: t)
           (o1: t), Prop.
  Admitted.

  Definition progress e o0 p0 c0 d: Prop :=
    forall m_released (WF: wf_released m_released e),
      exists o1, step p0 e c0 d m_released o0 o1.

  Variant _wf (wf: t -> Prop): t -> Prop :=
  | wf_intro
      (o0: t)
      (WF: forall p0 e c0 d (m_released: option SeqMemory.t) (o1: t)
                  (STEP: step p0 e c0 d m_released o0 o1),
          (<<EVENT: wf_diff_event d e>>) /\
          (<<PERM: wf_diff_perms (is_accessing e) d p0>>) /\
          (<<CELL: wf_cell c0 e>>) /\
          (<<RELEASED: wf_released m_released e>>) /\
          (<<ORACLE: wf o1>>))
      (LOAD: forall p0 c0 loc ord
                    (ORD: Ordering.le ord Ordering.strong_relaxed),
          exists v d, progress (ProgramEvent.read loc v ord) o0 p0 (Some c0) d)
      (STORE: forall p0 c0 loc ord val,
          exists d, progress (ProgramEvent.write loc val ord) o0 p0 c0 d)
      (FENCE: forall p0 ordr ordw
                     (ORDR: Ordering.le ordr Ordering.strong_relaxed)
                     (ORDW: Ordering.le ordw Ordering.acqrel),
          exists d, progress (ProgramEvent.fence ordr ordw) o0 p0 None d)
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
    forall (e: ProgramEvent.t) (d: diffs) (m_released: option SeqMemory.t)
           (th0: t) (th1: t), Prop :=
  | at_step_intro
      p0 p1 o0 o1 e c d m_released st0 st1 m0 m_upd m1
      (STEP: lang.(Language.step) e st0 st1)
      (ORACLE: Oracle.step p0 e c d m_released o0 o1)
      (CELL: match_cell (is_accessing e) c m0)
      (PERM: p1 = update_perm d p0)
      (MEM: m_upd = update_mem d (update_cell (is_accessing e) c m0))
      (RELEASE: SeqMemory.release m_upd m_released m1)
    :
      at_step e d m_released (mk (SeqState.mk _ st0 m0) p0 o0) (mk (SeqState.mk _ st1 m1) p1 o1)
  .

  Variant step (e: MachineEvent.t) (th0: t) (th1: t): Prop :=
  | step_na_step
      (STEP: na_step e th0 th1)
  | step_at_step
      pe d m_released
      (EVENT: e = get_machine_event pe)
      (STEP: at_step pe d m_released th0 th1)
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
    forall st_tgt1 e
           (STEP_TGT: lang_tgt.(Language.step) e st_tgt0.(SeqState.state) st_tgt1)
           (ATOMIC: is_atomic_event e),
    exists st_src1 st_src2,
      (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
      (<<MEM: is_acquire_event e -> SeqMemory.le_partial st_tgt0.(SeqState.memory) st_src1.(SeqState.memory)>>) /\
      (<<STEP: lang_src.(Language.step) e st_src1.(SeqState.state) st_src2>>) /\
      (<<SIM: forall d c mem_released mem_tgt
                     (EVENT: wf_diff_event d e)
                     (PERM: wf_diff_perms (is_accessing e) d p0)
                     (RELEASED: wf_released mem_released e)
                     (CELL: wf_cell c e)
                     (MATCH: match_cell (is_accessing e) c st_tgt0.(SeqState.memory))
                     (MEM: SeqMemory.release (update_mem d (update_cell (is_accessing e) c st_tgt0.(SeqState.memory))) mem_released mem_tgt),
          exists mem_src,
            (<<MATCH: match_cell (is_accessing e) c st_src1.(SeqState.memory)>>) /\
            (<<MEM: SeqMemory.release (update_mem d (update_cell (is_accessing e) c st_src1.(SeqState.memory))) mem_released mem_src>>) /\
            (<<SIM: sim_seq (update_perm d p0)
                            (SeqState.mk _ st_src2 mem_src)
                            (SeqState.mk _ st_tgt1 mem_tgt)>>)>>).

  Definition sim_seq_partial_case
             (p0: Perms.t)
             (st_src0: SeqState.t lang_src)
             (st_tgt0: SeqState.t lang_tgt): Prop :=
    forall o (WF: Oracle.wf o),
    exists th,
      (<<STEPS: rtc (SeqThread.step MachineEvent.silent) (SeqThread.mk st_src0 p0 o) th>>) /\
      ((<<MEM: SeqMemory.le_partial st_tgt0.(SeqState.memory) th.(SeqThread.state).(SeqState.memory)>>) \/ (<<FAILURE: SeqThread.failure th>>)).

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
        (MEM: SeqMemory.le_partial st_tgt.(SeqState.memory) st_src.(SeqState.memory))
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
    forall p vals,
      sim_seq
        p
        (SeqState.mk _ st_src (SeqMemory.init vals))
        (SeqState.mk _ st_tgt (SeqMemory.init vals)).
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
