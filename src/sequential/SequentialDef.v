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

Definition Perms := Loc.t -> Perm.t.

Module SeqCell.
   Definition t := (Const.t * Flag.t)%type.

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

   Definition flag_le (c0 c1: t): Prop :=
     match c0, c1 with
     | (v0, f0), (v1, f1) => Flag.le f0 f1
     end.

   Program Instance flag_le_PreOrder: PreOrder flag_le.
   Next Obligation.
   Proof.
     ii. destruct x; ss. refl.
   Qed.
   Next Obligation.
   Proof.
     ii. destruct x, y, z; ss.
     des. subst. splits; auto. etrans; eauto.
   Qed.

   Lemma le_flag_le c0 c1 (LE: le c0 c1):
     flag_le c0 c1.
   Proof.
     destruct c0, c1. ss. des; auto.
   Qed.

   Definition is_written (c: t): Prop :=
     match c with
     | (_, Flag.written) => True
     | _ => False
     end.

   Definition init (v: Const.t): t := (v, Flag.unwritten).
End SeqCell.


Module SeqMemory.
  Definition t := Loc.t -> SeqCell.t.

  Definition update (loc: Loc.t) (val: Const.t) (m: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then (val, Flag.written) else (m loc').

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
| diff_acq (v: Const.t)
| diff_rel
| diff_reset (v: Const.t)
.

Definition diffs := Loc.t -> diff.

Definition kept := Loc.t -> bool.
Definition kept_bot: kept := fun _ => false.

Definition update_flag (k: bool) (f_new: Flag.t) (c: SeqCell.t): SeqCell.t :=
  match c with
  | (v, f_old) => if k then (v, f_new) else (v, f_old)
  end.

Definition update_mem
           (k: kept) (f_new: Flag.t)
           (d: diffs) (m0: SeqMemory.t): SeqMemory.t :=
  fun loc =>
    match (d loc) with
    | diff_rlx | diff_rel => update_flag (k loc) f_new (m0 loc)
    | diff_acq v | diff_reset v => (v, Flag.unwritten)
    end.

Definition update_perm (k: kept) (d: diffs) (p0: Perms): Perms :=
  fun loc =>
    match (d loc) with
    | diff_rlx | diff_reset _ => p0 loc
    | diff_acq _ => Perm.full
    | diff_rel => if (k loc) then p0 loc else Perm.none
    end.

Definition match_mem (k: kept) (d: diffs) (mem_src mem_tgt: SeqMemory.t) :=
  forall loc,
    match (d loc) with
    | diff_acq _ | diff_rlx => True
    | diff_reset _ => SeqCell.le (mem_src loc) (mem_tgt loc)
    | diff_rel => k loc \/ SeqCell.le (mem_src loc) (mem_tgt loc)
    end.

Definition match_flag (mem_src mem_tgt: SeqMemory.t) :=
  forall loc,
    SeqCell.flag_le (mem_src loc) (mem_tgt loc).

Definition wf_diff_perms (d: diffs) (p: Perms): Prop :=
  forall loc,
    match (d loc), (p loc) with
    | diff_rlx, _ => True
    | diff_rel, Perm.full => True
    | diff_reset _, Perm.full => True
    | diff_acq _, Perm.none => True
    | _, _ => False
    end.

Definition wf_diff_event (d: diffs) (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.syscall _ => True
  | ProgramEvent.read loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_rel | diff_reset _ => False
      | diff_acq _ => Ordering.le Ordering.acqrel ord
      | diff_rlx => True
      end
  | ProgramEvent.write loc _ ord =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_acq _ | diff_reset _ => False
      | diff_rel => Ordering.le Ordering.acqrel ord
      | diff_rlx => True
      end
  | ProgramEvent.update loc _ _ ordr ordw =>
    forall loc' (NEQ: loc' <> loc),
      match (d loc') with
      | diff_reset _ => False
      | diff_rel => Ordering.le Ordering.acqrel ordw
      | diff_acq _ => Ordering.le Ordering.acqrel ordr
      | diff_rlx => True
      end
  | ProgramEvent.fence ordr ordw =>
    forall loc',
      match (d loc') with
      | diff_reset _ => False
      | diff_rel => Ordering.le Ordering.acqrel ordw
      | diff_acq _ => Ordering.le Ordering.acqrel ordr
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

Definition is_acq_event (e: ProgramEvent.t): Prop :=
  match e with
  | ProgramEvent.fence ordr _ => Ordering.le Ordering.acqrel ordr
  | ProgramEvent.read _ _ ord => Ordering.le Ordering.acqrel ord
  | ProgramEvent.update _ _ _ _ _ => True
  | _ => False
  end.



Module Oracle.
  Definition t: Type. Admitted.

  Definition step:
    forall (p0: Perms)
           (e: ProgramEvent.t)
           (d: diffs)
           (o0: t)
           (o1: t), Prop.
  Admitted.

  Variant _wf (wf: t -> Prop): t -> Prop :=
  | wf_intro
      o0
      (DIFF: forall p0 e d o1
                    (STEP: step p0 e d o0 o1),
          (<<EVENT: wf_diff_event d e>>) /\
          (<<PERM: wf_diff_perms d p0>>) /\
          (<<WF: wf o1>>))
      (LOAD: forall p0 loc ord
                    (ORD: Ordering.le ord Ordering.strong_relaxed),
          exists val d o1, (<<STEP: step p0 (ProgramEvent.read loc val ord) d o0 o1>>))
      (STORE: forall p0 loc ord val,
          exists d o1, (<<STEP: step p0 (ProgramEvent.write loc val ord) d o0 o1>>))
      (FENCE: forall p0 ordr ordw
                     (ORD: Ordering.le ordr Ordering.strong_relaxed),
          exists d o1, (<<STEP: step p0 (ProgramEvent.fence ordr ordw) d o0 o1>>))
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

  Variant at_step:
    forall (e: MachineEvent.t) (th0: t) (th1: t), Prop :=
  | at_step_intro
      p0 p1 o0 o1 e d st0 st1 m0 m1 me
      (STEP: lang.(Language.step) e st0 st1)
      (ORACLE: Oracle.step p0 e d o0 o1)
      (PERM: p1 = update_perm kept_bot d p0)
      (MEM: m1 = update_mem kept_bot Flag.unwritten d m0)
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
    exists th1 th2,
      (<<STEPS: rtc (step MachineEvent.silent) th0 th1>>) /\
      (<<FAILURE: step MachineEvent.failure th1 th2>>).

  Definition certified (mem: SeqMemory.t) (th0: t): Prop :=
    exists th1,
      (<<STEPS: rtc (step MachineEvent.silent) th0 th1>>) /\
      (<<MEM: forall loc
                     (PERM: th0.(perm) loc = Perm.full)
                     (WRITTEN: SeqCell.is_written (mem loc)),
          SeqCell.is_written (th1.(state).(SeqState.memory) loc)>>).
End LANG.
End SeqThread.


Section SIMULATION.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.


  Variant _sim_seq_gen
          (sim_seq_gen:
             forall
               (p0: Perms)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
    :
      forall
        (p0: Perms)
        (st_src0: SeqState.t lang_src)
        (st_tgt0: SeqState.t lang_tgt), Prop :=
  | sim_seq_gen_intro
      (p0: Perms)
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
           (<<SIM: sim_seq_gen p0 st_src2 st_tgt1>>))
      (ATSTEP:
         forall st_tgt1 e
                (STEP_TGT: lang_tgt.(Language.step) e st_tgt0.(SeqState.state) st_tgt1)
                (ATOMIC: is_atomic_event e),
         exists k st_src1 st_src2,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<STEP: lang_src.(Language.step) e st_src1.(SeqState.state) st_src2>>) /\
           (<<SIM: forall d
                          (EVENT: wf_diff_event d e)
                          (PERM: wf_diff_perms d p0),
               (<<MEM: match_mem k d st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
               (<<SIM: sim_seq_gen (update_perm k d p0)
                                   (SeqState.mk _ st_src2 (update_mem k Flag.unwritten d st_src1.(SeqState.memory)))
                                   (SeqState.mk _ st_tgt1 (update_mem k Flag.written d st_tgt0.(SeqState.memory)))>>)>>))
      (CERTIFIED: forall o (WF: Oracle.wf o),
          SeqThread.certified st_tgt0.(SeqState.memory) (SeqThread.mk st_src0 p0 o))
    :
      _sim_seq_gen sim_seq_gen p0 st_src0 st_tgt0
  | sim_seq_gen_failure
      (p0: Perms)
      (st_src0: SeqState.t lang_src)
      (st_tgt0: SeqState.t lang_tgt)
      (FAILURE: forall o (WF: Oracle.wf o),
          SeqThread.failure (SeqThread.mk st_src0 p0 o))
    :
      _sim_seq_gen sim_seq_gen p0 st_src0 st_tgt0
  .

  Lemma sim_seq_gen_mon: monotone3 _sim_seq_gen.
  Proof.
    ii. inv IN.
    { econs 1; eauto.
      { i. hexploit NASTEP; eauto. i. des. esplits; eauto. }
      { i. exploit ATSTEP; eauto. i. des. esplits; eauto.
        i. hexploit SIM; eauto. i. des. esplits; eauto. }
    }
    { econs 2; eauto. }
  Qed.

  Definition sim_seq_gen := paco3 _sim_seq_gen bot3.



  Inductive _sim_seq
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
  | sim_seq_intro
      (synch: bool)
      (p0: Perms)
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
           (<<SIM: forall (SYNC: synch = true), sim_seq p0 st_src2 st_tgt1>>) /\
           (<<SIM: forall (SYNC: synch = false), _sim_seq sim_seq p0 st_src2 st_tgt1>>) /\
           (<<FLAG: forall (SYNC: synch = true), match_flag st_src2.(SeqState.memory) st_tgt1.(SeqState.memory)>>))
      (ATSTEP:
         forall st_tgt1 e
                (STEP_TGT: lang_tgt.(Language.step) e st_tgt0.(SeqState.state) st_tgt1)
                (ATOMIC: is_atomic_event e),
         exists k st_src1 st_src2,
           (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
           (<<STEP: lang_src.(Language.step) e st_src1.(SeqState.state) st_src2>>) /\
           (<<FLAG: forall (SYNC: synch = true \/ is_acq_event e),
               match_flag st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
           (<<SIM: forall d
                          (EVENT: wf_diff_event d e)
                          (PERM: wf_diff_perms d p0),
               (<<MEM: match_mem k d st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
               (<<SIM: forall (SYNC: synch = true),
                   sim_seq (update_perm k d p0)
                           (SeqState.mk _ st_src2 (update_mem k Flag.unwritten d st_src1.(SeqState.memory)))
                           (SeqState.mk _ st_tgt1 (update_mem k Flag.written d st_tgt0.(SeqState.memory)))>>) /\
               (<<SIM: forall (SYNC: synch = false),
                   _sim_seq sim_seq (update_perm k d p0)
                            (SeqState.mk _ st_src2 (update_mem k Flag.unwritten d st_src1.(SeqState.memory)))
                            (SeqState.mk _ st_tgt1 (update_mem k Flag.written d st_tgt0.(SeqState.memory)))>>)>>))
    :
      _sim_seq sim_seq p0 st_src0 st_tgt0
  | sim_seq_failure
      (p0: Perms)
      (st_src0: SeqState.t lang_src)
      (st_tgt0: SeqState.t lang_tgt)
      (FAILURE: forall o (WF: Oracle.wf o),
          SeqThread.failure (SeqThread.mk st_src0 p0 o))
    :
      _sim_seq sim_seq p0 st_src0 st_tgt0
  .

  Lemma sim_seq_ind
        (sim_seq: forall
            (p0: Perms)
            (st_src0: SeqState.t lang_src)
            (st_tgt0: SeqState.t lang_tgt), Prop)
        (P: forall
            (p0: Perms)
            (st_src0: SeqState.t lang_src)
            (st_tgt0: SeqState.t lang_tgt), Prop)
        (STEP: forall
            (synch: bool)
            (p0: Perms)
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
                 (<<SIM: forall (SYNC: synch = true), sim_seq p0 st_src2 st_tgt1>>) /\
                 (<<SIM: forall (SYNC: synch = false), _sim_seq sim_seq p0 st_src2 st_tgt1 /\ P p0 st_src2 st_tgt1>>) /\
                 (<<FLAG: forall (SYNC: synch = true), match_flag st_src2.(SeqState.memory) st_tgt1.(SeqState.memory)>>))
            (ATSTEP:
               forall st_tgt1 e
                      (STEP_TGT: lang_tgt.(Language.step) e st_tgt0.(SeqState.state) st_tgt1)
                      (ATOMIC: is_atomic_event e),
               exists k st_src1 st_src2,
                 (<<STEPS: rtc (SeqState.na_step p0 MachineEvent.silent) st_src0 st_src1>>) /\
                 (<<STEP: lang_src.(Language.step) e st_src1.(SeqState.state) st_src2>>) /\
                 (<<FLAG: forall (SYNC: synch = true \/ is_acq_event e),
                     match_flag st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
                 (<<SIM: forall d
                                (EVENT: wf_diff_event d e)
                                (PERM: wf_diff_perms d p0),
                     (<<MEM: match_mem k d st_src1.(SeqState.memory) st_tgt0.(SeqState.memory)>>) /\
                     (<<SIM: forall (SYNC: synch = true),
                         sim_seq (update_perm k d p0)
                                 (SeqState.mk _ st_src2 (update_mem k Flag.unwritten d st_src1.(SeqState.memory)))
                                 (SeqState.mk _ st_tgt1 (update_mem k Flag.written d st_tgt0.(SeqState.memory)))>>) /\
                     (<<SIM: forall (SYNC: synch = false),
                         _sim_seq sim_seq (update_perm k d p0)
                                  (SeqState.mk _ st_src2 (update_mem k Flag.unwritten d st_src1.(SeqState.memory)))
                                  (SeqState.mk _ st_tgt1 (update_mem k Flag.written d st_tgt0.(SeqState.memory))) /\
                         P (update_perm k d p0)
                           (SeqState.mk _ st_src2 (update_mem k Flag.unwritten d st_src1.(SeqState.memory)))
                           (SeqState.mk _ st_tgt1 (update_mem k Flag.written d st_tgt0.(SeqState.memory)))>>)>>)),
            P p0 st_src0 st_tgt0)
      (FAILURE: forall
          (p0: Perms)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt)
          (FAILURE: forall o (WF: Oracle.wf o),
              SeqThread.failure (SeqThread.mk st_src0 p0 o)),
          P p0 st_src0 st_tgt0)
    :
      forall p0 st_src0 st_tgt0 (SIM: _sim_seq sim_seq p0 st_src0 st_tgt0), P p0 st_src0 st_tgt0.
  Proof.
    fix IH 4. i. inv SIM.
    { eapply STEP.
      { eauto. }
      { i. hexploit NASTEP; eauto. i. des. esplits; eauto. }
      { i. hexploit ATSTEP; eauto. i. des. esplits; eauto.
        i. hexploit SIM; eauto. i. des. esplits; eauto. }
    }
    { eapply FAILURE; eauto. }
  Qed.

  Lemma sim_seq_mon: monotone3 _sim_seq.
  Proof.
    ii. eapply sim_seq_ind; eauto.
    { i. econs 1; eauto.
      { i. hexploit NASTEP; eauto. i. des. esplits; eauto. i. eapply SIM0; auto. }
      { i. exploit ATSTEP; eauto. i. des. esplits; eauto.
        i. hexploit SIM; eauto. i. des. esplits; eauto. i. eapply SIM1; eauto. }
    }
    { i. econs 2; eauto. }
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
