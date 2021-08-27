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
  | unwritten
  | written
  .

  Definition le (f_src f_tgt: t): bool :=
    match f_src, f_tgt with
    | written, _ => true
    | unwritten, unwritten => true
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
End Flag.


Module SeqCell.
   Definition t := (Const.t * Flag.t)%type.


   Definition unflag: t -> t :=
     fun '(v, f) => (v, Flag.unwritten).

   (* checked at final *)
   Definition le (c0 c1: t): Prop :=
     match c0, c1 with
     | (v0, f0), (v1, f1) => v0 = v1 /\ Flag.le f0 f1
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


   (* checked at acquire *)
   Definition le_flag (c0 c1: t): Prop :=
     match c0, c1 with
     | (v0, f0), (v1, f1) => Flag.le f0 f1
     end.

   Program Instance le_flag_PreOrder: PreOrder le_flag.
   Next Obligation.
   Proof.
     ii. destruct x; ss. refl.
   Qed.
   Next Obligation.
   Proof.
     ii. destruct x, y, z; ss.
     des. subst. splits; auto. etrans; eauto.
   Qed.


   (* checked every moment *)
   Definition le_partial (c0 c1: t): Prop :=
     match c0, c1 with
     | (v0, f0), (v1, f1) =>
       f0 = Flag.written \/ (v0 = v1 /\ Flag.le f0 f1)
     end.

   Program Instance le_partial_PreOrder: PreOrder le_partial.
   Next Obligation.
   Proof.
     ii. destruct x; ss. right. split; auto. refl.
   Qed.
   Next Obligation.
   Proof.
     ii. destruct x, y, z; ss.
     des; subst; auto.
     { left. destruct t1; ss. }
     { right. split; auto. etrans; eauto. }
   Qed.


   Lemma le_le_partial c0 c1 (LE: le c0 c1)
     :
       le_partial c0 c1.
   Proof.
     destruct c0, c1. ss. des; auto.
   Qed.

   Lemma le_le_flag c0 c1 (LE: le c0 c1)
     :
       le_flag c0 c1.
   Proof.
     destruct c0, c1. ss. des; auto.
   Qed.

   Definition init (v: Const.t): t := (v, Flag.unwritten).
End SeqCell.


Module SeqMemory.
  Definition t := Loc.t -> SeqCell.t.

  Definition update (loc: Loc.t) (val: Const.t) (m: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then (val, Flag.written) else (m loc').


  Definition le_loc (loc: Loc.t) (m_src m_tgt: t): Prop :=
    SeqCell.le (m_src loc) (m_tgt loc).

  Definition le (m_src m_tgt: t): Prop :=
    forall loc, SeqCell.le (m_src loc) (m_tgt loc).

  Definition le_flag (m_src m_tgt: t): Prop :=
    forall loc, SeqCell.le_flag (m_src loc) (m_tgt loc).

  Definition le_partial (m_src m_tgt: t): Prop :=
    forall loc, SeqCell.le_partial (m_src loc) (m_tgt loc).


  Program Instance le_loc_PreOrder (loc: Loc.t): PreOrder (le_loc loc).
  Next Obligation.
  Proof.
    ii. unfold le_loc in *. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. unfold le_loc in *. etrans; eauto.
  Qed.

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. etrans; eauto.
  Qed.

  Program Instance le_flag_PreOrder: PreOrder le_flag.
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


  Lemma le_le_loc loc m_src m_tgt (LE: le m_src m_tgt)
    :
      le_loc loc m_src m_tgt.
  Proof.
    apply LE.
  Qed.

  Lemma le_le_partial m_src m_tgt (LE: le m_src m_tgt)
    :
      le_partial m_src m_tgt.
  Proof.
    ii. eapply SeqCell.le_le_partial. auto.
  Qed.

  Lemma le_le_flag m_src m_tgt (LE: le m_src m_tgt)
    :
      le_flag m_src m_tgt.
  Proof.
    ii. eapply SeqCell.le_le_flag. auto.
  Qed.

  Definition init (vals: Loc.t -> Const.t): t :=
    fun loc => SeqCell.init (vals loc).
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
| diff_acq (v: Const.t)
| diff_rel
| diff_unflag
| diff_update (v: Const.t)
.

Definition non_release_diff (d: diff): Prop :=
  match d with
  | diff_rel | diff_unflag => False
  | _ => True
  end.

Definition diffs := Loc.t -> diff.

Definition update_mem
           (d: diffs) (m0: SeqMemory.t): SeqMemory.t :=
  fun loc =>
    let (v0, f0) := (m0 loc) in
    match (d loc) with
    | diff_none => (v0, f0)
    | diff_rel | diff_unflag => (v0, Flag.unwritten)
    | diff_acq v1 | diff_update v1 => (v1, f0)
    end.

Definition update_perm (d: diffs) (p0: Perms.t): Perms.t :=
  fun loc =>
    match (d loc) with
    | diff_none | diff_update _ | diff_unflag => p0 loc
    | diff_acq _ => Perm.full
    | diff_rel => Perm.none
    end.


Definition wf_diff_perms (d: diffs) (p: Perms.t): Prop :=
  forall loc,
    match (d loc), (p loc) with
    | diff_none, _ => True
    | diff_rel, Perm.full => True
    | diff_update _, Perm.full => True
    | diff_acq _, Perm.none => True
    | diff_unflag, Perm.full => True
    | _, _ => False
    end.

Definition wf_diff_event (d: diffs) (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.read loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_rel | diff_update _ | diff_unflag => False
      | diff_acq _ => Ordering.le Ordering.acqrel ord
      | diff_none => True
      end
  | ProgramEvent.write loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_acq _ | diff_update _ => False
      | diff_rel | diff_unflag => Ordering.le Ordering.acqrel ord
      | diff_none => True
      end
  | ProgramEvent.update loc _ _ ordr ordw =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_update _ => False
      | diff_rel | diff_unflag => Ordering.le Ordering.acqrel ordw
      | diff_acq _ => Ordering.le Ordering.acqrel ordr
      | diff_none => True
      end
  | ProgramEvent.fence ordr ordw =>
    forall loc',
      match (d loc') with
      | diff_update _ => False
      | diff_rel | diff_unflag => Ordering.le Ordering.acqrel ordw
      | diff_acq _ => Ordering.le Ordering.acqrel ordr
      | diff_none => True
      end
  | _ => True
  end.


Definition target_loc (e: ProgramEvent.t) (loc: Loc.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.read loc' _ _ => loc = loc'
  | ProgramEvent.write loc' _ _ => loc = loc'
  | ProgramEvent.update loc' _ _ _ _ => loc = loc'
  | _ => False
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

Definition is_acquire_event (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.fence ordr _ => Ordering.le Ordering.acqrel ordr
  | ProgramEvent.read _ _ ord => Ordering.le Ordering.acqrel ord
  | ProgramEvent.update _ _ _ _ _ => True
  | _ => False
  end.



Module Oracle.
  Definition t: Type. Admitted.

  Definition step:
    forall (p0: Perms.t)
           (mem0: SeqMemory.t)
           (e: ProgramEvent.t)
           (d: diffs)
           (o0: t)
           (o1: t), Prop.
  Admitted.

  Variant _wf (wf: t -> Prop): t -> Prop :=
  | wf_intro
      o0
      (DIFF: forall p0 mem0 e d o1
                    (STEP: step p0 mem0 e d o0 o1),
          (<<EVENT: wf_diff_event d e>>) /\
          (<<PERM: wf_diff_perms d p0>>) /\
          (<<WF: wf o1>>))
      (LOAD: forall p0 mem0 loc ord
                    (ORD: Ordering.le ord Ordering.strong_relaxed),
          exists v d o1, (<<STEP: step p0 mem0 (ProgramEvent.read loc v ord) d o0 o1>>) /\
                         (<<NOREL: forall loc, non_release_diff (d loc)>>))
      (STORE: forall p0 mem0 loc ord val,
          exists d o1, (<<STEP: step p0 mem0 (ProgramEvent.write loc val ord) d o0 o1>>) /\
                       (<<NOREL: forall loc, non_release_diff (d loc)>>))
      (FENCE: forall p0 mem0 ordr ordw
                     (ORD: Ordering.le ordr Ordering.strong_relaxed),
          exists d o1, (<<STEP: step p0 mem0 (ProgramEvent.fence ordr ordw) d o0 o1>>) /\
                       (<<NOREL: forall loc, non_release_diff (d loc)>>))
    :
      _wf wf o0
  .

  Lemma wf_mon: monotone1 _wf.
  Proof.
    ii. inv IN. econs; eauto. i.
    exploit DIFF; eauto. i. des. splits; auto.
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
    forall (e: MachineEvent.t) (th0: t) (th1: t), Prop :=
  | at_step_intro
      p0 p1 o0 o1 e d st0 st1 m0 m1 me
      (STEP: lang.(Language.step) e st0 st1)
      (ORACLE: Oracle.step p0 m0 e d o0 o1)
      (PERM: p1 = update_perm d p0)
      (MEM: m1 = update_mem d m0)
      (EVENT: me = get_machine_event e)
    :
      at_step me (mk (SeqState.mk _ st0 m0) p0 o0) (mk (SeqState.mk _ st1 m1) p1 o1)
  .

  Variant step (e: MachineEvent.t) (th0: t) (th1: t): Prop :=
  | step_na_step
      (STEP: na_step e th0 th1)
  | step_at_step
      (STEP: at_step e th0 th1)
  .

  Definition failure (th0: t): Prop :=
    exists th1, (<<FAILURE: step MachineEvent.failure th0 th1>>).
End LANG.
End SeqThread.


Section SIMULATION.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Variant _sim_seq
          (sim_seq:
             forall
               (p0: Perms.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
    :
      forall
        (p0: Perms.t)
        (st_src0: SeqState.t lang_src)
        (st_tgt0: SeqState.t lang_tgt), Prop :=
  | sim_seq_intro
      (p0: Perms.t)
      (st_src0: SeqState.t lang_src)
      (st_tgt0: SeqState.t lang_tgt)
      (TERMINAL:
         forall (TERMINAL_TGT: lang_tgt.(Language.is_terminal) st_tgt0.(SeqState.state)),
         exists st_src1,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<TERMINAL_SRC: lang_src.(Language.is_terminal) st_src1.(SeqState.state)>>) /\
           (<<TERMINAL: sim_terminal st_src1.(SeqState.state) st_tgt0.(SeqState.state)>>) /\
           (<<MEM: SeqMemory.le st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>))
      (NASTEP:
         forall st_tgt1 e (STEP_TGT: SeqState.na_step p0 e st_tgt0 st_tgt1),
         exists st_src1 st_src2,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<STEP: SeqState.na_opt_step p0 e st_src1 st_src2>>) /\
           (<<SIM: sim_seq p0 st_src2 st_tgt1>>))
      (ATSTEP:
         forall st_tgt1 e
                (STEP_TGT: lang_tgt.(Language.step) e st_tgt0.(SeqState.state) st_tgt1)
                (ATOMIC: is_atomic_event e),
         exists st_src1 st_src2,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<FLAG: is_acquire_event e -> SeqMemory.le_flag st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
           (<<MEM: forall loc (LOC: target_loc e loc),
               SeqMemory.le_loc loc st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
           (<<STEP: lang_src.(Language.step) e st_src1.(SeqState.state) st_src2>>) /\
           (<<SIM: forall d
                          (EVENT: wf_diff_event d e)
                          (PERM: wf_diff_perms d p0),
               (<<SIM: sim_seq (update_perm d p0)
                               (SeqState.mk _ st_src2 (update_mem d st_src1.(SeqState.memory)))
                               (SeqState.mk _ st_tgt1 (update_mem d st_tgt0.(SeqState.memory)))>>)>>))
      (PARTIAL: forall o (WF: Oracle.wf o),
          exists th,
            (<<STEPS: rtc (SeqThread.step MachineEvent.silent) (SeqThread.mk st_src0 p0 o) th>>) /\
            ((<<MEM: SeqMemory.le_partial th.(SeqThread.state).(SeqState.memory) st_tgt0.(SeqState.memory)>>) \/ (<<FAILURE: SeqThread.failure th>>)))
    :
      _sim_seq sim_seq p0 st_src0 st_tgt0
  | sim_seq_failure
      (p0: Perms.t)
      (st_src0: SeqState.t lang_src)
      (st_tgt0: SeqState.t lang_tgt)
      (FAILURE: forall o (WF: Oracle.wf o),
          exists th,
            (<<STEPS: rtc (SeqThread.step MachineEvent.silent) (SeqThread.mk st_src0 p0 o) th>>) /\
            (<<FAILURE: SeqThread.failure th>>))
    :
      _sim_seq sim_seq p0 st_src0 st_tgt0
  .

  Lemma sim_seq_mon: monotone3 _sim_seq.
  Proof.
    ii. inv IN.
    { econs 1; eauto.
      { i. hexploit NASTEP; eauto. i. des. esplits; eauto. }
      { i. exploit ATSTEP; eauto. i. des. esplits; eauto.
        i. hexploit SIM; eauto. }
    }
    { econs 2; eauto. }
  Qed.

  Definition sim_seq := paco3 _sim_seq bot3.
End SIMULATION.
Arguments sim_seq [_] [_] _ _ _.
#[export] Hint Resolve sim_seq_mon: paco.





Require Import ITreeLang.
Require Import iCompatibility.

Section ADEQUACY.
  Variable R: Type.

  Definition sim_seq_itree (st_src: itree MemE.t R) (st_tgt: itree MemE.t R): Prop :=
    forall p vals,
      sim_seq
        eq
        p
        (SeqState.mk (lang R) st_src (SeqMemory.init vals))
        (SeqState.mk (lang R) st_tgt (SeqMemory.init vals)).

  Theorem adequacy_seq:
    sim_seq_itree <2= sim_itree eq.
  Proof.
  Admitted.
End ADEQUACY.
