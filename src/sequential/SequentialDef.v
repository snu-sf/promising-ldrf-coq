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

Variant flag :=
| unwritten
| written
| promised
.

Definition flag_le (f_src f_tgt: flag): bool :=
  match f_src, f_tgt with
  | promised, _ => false
  | written, _ => true
  | unwritten, unwritten => true
  | _, _ => false
  end.

Definition Perms := Loc.t -> Perm.t.

Module SeqMemory.
  Definition t := Loc.t -> Const.t * flag.

  Definition update (loc: Loc.t) (val: Const.t) (m: t): t :=
    fun loc' => if Loc.eq_dec loc' loc then (val, written) else (m loc').

  Definition le (m_src m_tgt: t): Prop :=
    forall loc,
      match (m_src loc), (m_tgt loc) with
      | (v_src, f_src), (v_tgt, f_tgt) =>
        v_src = v_tgt /\ flag_le f_src f_tgt
      end.
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
End LANG.
End SeqState.


Variant sort :=
| rlx (* no change *)
| srlx (
| acq
| rel
| relacq
| event
| upd
.

  perms
  mem_src
  mem_tgt
  written_src
  written_tgt
  proms_src


Variant at_step:
  forall
    (s: sort)
    (p0: Perms)
    (m_src0: SeqMemory.t)
    (m_tgt0: SeqMemory.t)
    (proms0: Proms)
    (p1: Perms)
    (m_src1: SeqMemory.t)
    (m_tgt1: SeqMemory.t)
    (proms1: Proms), Prop :=
| at_step_rlx
    p m_src m_tgt proms
  :
    at_step
      rlx
      p m_src m_tgt proms
      p m_src m_tgt proms
| at_step

(* srlx *)
| (* rel *)
| (* acq *)


| at_step_srlx
    p m_src m_tgt proms
  :
    at_step
      rlx
      p m_src m_tgt proms
      p m_src m_tgt proms
.





Variant at_step:
  forall
    (p0: Perms)
    (m_src0: SeqMemory.t)
    (m_tgt0: SeqMemory.t)
    (proms0: Proms)
    (p1: Perms)
    (m_src1: SeqMemory.t)
    (m_tgt1: SeqMemory.t)
    (proms1: Proms), Prop :=
| at_step_rlx



    rlx fence
    rlx


    rlx/plain load
    rlx/plain store
    srlx store
    acq load
    rel store
    upd





Module Released.
  Definition t := Loc.t -> option (Const.t * flag).

  Definition le (rels0 rels: t): Prop :=
    forall loc,
      match (rels0 loc), (rels1 loc) with
      | Some (



Definition released_vals: Type := Loc.t -> option (Comn

Definition mem_diff:


Variant diff :=
| diff_rlx
| diff_rel (* (val: Const.t) (f: flag) *)
| diff_acq (val: Const.t)
| diff_relacq (* (valw: Const.t) (f: flag) *) (valr: Const.t)
.

Definition diffs := Loc.t -> diff.

Definition is_acq (d: diff): bool :=
  match d with
  | diff_acq _  => true
  | _ => false
  end.

Definition is_rel (d: diff): bool :=
  match d with
  | diff_rel => true
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

Variant update_perms (d: diffs) (p0 p1: perms)


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
End LANG.
End SeqState.

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

  Variant at_local_step (p: Perms):
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
End LANG.
End State.

Section SIMULATION.
  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition SIM_SEQ :=
    forall
      (p: Perms)
      (st_src: lang_src.(Language.state))
      (mem_src: SeqMemory.t)
      (st_tgt: lang_tgt.(Language.state))
      (mem_tgt: SeqMemory.t), Prop.

  Inductive _sim_seq
            (sim_seq: SIM_SEQ)
            (p: Perms)
            (st_src0: lang_src.(Language.state))
            (mem_src0: SeqMemory.t)
            (st_tgt0: lang_tgt.(Language.state))
            (mem_tgt0: SeqMemory.t): Prop :=
  | sim_seq_step
      (NASTEP: forall st_tgt1 e
                      (STEP_TGT: State.na_step





      (TERMINAL: forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
          (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
          exists st2_src lc2_src sc2_src mem2_src w2,
            (<<STEPS: rtc (@Thread.tau_step _)
                          (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                          (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
            (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
            (<<MEMORY: sim_memory w2 mem2_src mem1_tgt>>) /\
            (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
            (<<LOCAL: sim_local w2 lc2_src lc1_tgt>>) /\
            (<<TERMINAL: sim_terminal st2_src st1_tgt>>) /\
            (<<WORLD: world_le w1 w2>>)>>) /\


    (M<



             (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
             (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t): Prop :=
    forall w1 sc1_src mem1_src
           sc1_tgt mem1_tgt
           (SC: sim_timemap w1 sc1_src sc1_tgt)
           (MEMORY: sim_memory w1 mem1_src mem1_tgt)
           (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
           (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
           (MEM_FUTURE_SRC: Memory.future_weak mem0_src mem1_src)
           (MEM_FUTURE_TGT: Memory.future_weak mem0_tgt mem1_tgt)
           (WF_SRC: Local.wf lc1_src mem1_src)
           (WF_TGT: Local.wf lc1_tgt mem1_tgt)
           (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
           (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
           (MEM_SRC: Memory.closed mem1_src)
           (MEM_TGT: Memory.closed mem1_tgt)
           (CONS_TGT: Local.promise_consistent lc1_tgt)
           (WORLD: world_le w0 w1),
      (<<TERMINAL:
         forall (TERMINAL_TGT: (Language.is_terminal lang_tgt) st1_tgt),
           (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
           exists st2_src lc2_src sc2_src mem2_src w2,
             (<<STEPS: rtc (@Thread.tau_step _)
                           (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                           (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
             (<<SC: sim_timemap w2 sc2_src sc1_tgt>>) /\
             (<<MEMORY: sim_memory w2 mem2_src mem1_tgt>>) /\
             (<<TERMINAL_SRC: (Language.is_terminal lang_src) st2_src>>) /\
             (<<LOCAL: sim_local w2 lc2_src lc1_tgt>>) /\
             (<<TERMINAL: sim_terminal st2_src st1_tgt>>) /\
             (<<WORLD: world_le w1 w2>>)>>) /\
      (<<PROMISES:
         forall (PROMISES_TGT: (Local.promises lc1_tgt) = Memory.bot),
           (<<FAILURE: Thread.steps_failure (Thread.mk _ st1_src lc1_src sc1_src mem1_src)>>) \/
           exists st2_src lc2_src sc2_src mem2_src,
             (<<STEPS: rtc (@Thread.tau_step _)
                           (Thread.mk _ st1_src lc1_src sc1_src mem1_src)
                           (Thread.mk _ st2_src lc2_src sc2_src mem2_src)>>) /\
             (<<PROMISES_SRC: (Local.promises lc2_src) = Memory.bot>>)>>) /\
      (<<STEP: _sim_thread_step _ _ (@sim_thread lang_src lang_tgt sim_terminal)
                                w1
                                st1_src lc1_src sc1_src mem1_src
                                st1_tgt lc1_tgt sc1_tgt mem1_tgt>>).


  Inductive _sim
            (sim:
               forall
                 (st_src: lang.(Language.state))
                 (mem_src: SeqMemory.t)
                 (p_src: Perms)
                 (st_tgt: lang.(Language.state))
                 (mem_tgt: SeqMemory.t)
                 (p_tgt: Perms), Prop):
    forall
      (st_src: lang.(Language.state))
      (mem_src: SeqMemory.t)
      (p_src: Perms)
      (st_tgt: lang.(Language.state))
      (mem_tgt: SeqMemory.t)
      (p_tgt: Perms), Prop :=
  | sim_final
      st_src mem_src p_src st_tgt mem_tgt p_tgt
      (TGT: lang.(Language.is_terminal) st_tgt)
      (SRC: lang.(Language.is_terminal) st_src)

sim_thread


  Definition SIM_TERMINAL (lang_src lang_tgt:language) :=
    forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Definition SIM_THREAD :=
    forall (lang_src lang_tgt:language) (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
           (w: world)
           (st1_src:(Language.state lang_src)) (lc1_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
           (st1_tgt:(Language.state lang_tgt)) (lc1_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop.




Language.t


          state: lang.(Language.state);
        memory: SeqMemory.t;
        perm: Perms;




Module Memory.
  Definition t := Loc.t -> Cell.t.


Memory.t

Variant mem_permission

ProgramEvent.t
