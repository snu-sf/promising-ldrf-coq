From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
From ExtLib Require Export
     Data.String
     Data.Map.FMapAList
     Functor FunctorLaws
     Structures.Maps
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import List.
Require Import String.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.
Require Export ITreeLib.
Require Export Program.

Require Import Sequential.
Require Import SequentialITree.
Require Import FlagAux.
Require Import ITreeLang.





Section LANG.

  Definition is_na_inst (i: Inst.t) :=
    match i with
    | Inst.skip
    | Inst.assign _ _
    | Inst.abort
    | Inst.choose _ =>
      True
    | Inst.load _ _ ord
    | Inst.store _ _ ord =>
      Ordering.le ord Ordering.na
    | Inst.update _ _ _ ordr ordw =>
      (Ordering.le ordr Ordering.na) \/ (Ordering.le ordw Ordering.na)
    | _ => False
    end.

  Definition update_mem_na (v: Const.t) (i: Inst.t) (m: SeqMemory.t) :=
    match i with
    | Inst.store lhs _ _ =>
      SeqMemory.write lhs v m
    | _ =>
      m
    end.

  Variant match_inst_pe: Inst.t -> ProgramEvent.t -> Prop :=
  | match_inst_pe_load
      lhs rhs ord val
    :
      match_inst_pe (Inst.load lhs rhs ord) (ProgramEvent.read rhs val ord)
  | match_inst_pe_store
      lhs rhs ord val
    :
      match_inst_pe (Inst.store lhs rhs ord) (ProgramEvent.write lhs val ord)
  | match_inst_pe_update_failure
      lhs loc rmw ordr ordw val
    :
      match_inst_pe (Inst.update lhs loc rmw ordr ordw) (ProgramEvent.read loc val ordr)
  | match_inst_pe_update_success
      lhs loc rmw ordr ordw valr valw
    :
      match_inst_pe (Inst.update lhs loc rmw ordr ordw) (ProgramEvent.update loc valr valw ordr ordw)
  | match_inst_pe_fence
      ordr ordw
    :
      match_inst_pe (Inst.fence ordr ordw) (ProgramEvent.fence ordr ordw)
  | match_inst_pe_syscall
      lhs rhses sev
    :
      match_inst_pe (Inst.syscall lhs rhses) (ProgramEvent.syscall sev).

End LANG.



Section SIMAUX.

  Variable R_src R_tgt: Type.
  Variable sim_val: R_src -> R_tgt -> Prop.

  Definition term : Language.state (lang _) -> Language.state (lang _) -> Prop :=
    sim_terminal sim_val.


  Lemma na_steps_steps
        (L: language) (src0 src1: SeqState.t L) p o
        (NAS: rtc (SeqState.na_step p MachineEvent.silent) src0 src1)
    :
      SeqThread.steps (SeqState.na_step (lang:=_)) []
                      {| SeqThread.state := src0; SeqThread.perm := p; SeqThread.oracle := o |}
                      {| SeqThread.state := src1; SeqThread.perm := p; SeqThread.oracle := o |}.
  Proof.
    induction NAS.
    { econs 1. }
    econs 2.
    { econs 1. eauto. }
    eauto.
  Qed.

  Lemma sim_seq_term
        r g p d (src tgt: SeqState.t (lang _))
        (TERMINAL_TGT : Language.is_terminal (lang _) (SeqState.state tgt))
        (TERM: sim_seq_terminal_case term p d src tgt)
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d src tgt.
  Proof.
    gstep. econs 1; i.
    1: eauto.
    - ii. exfalso.
      unfold sim_seq_terminal_case in TERM. hexploit TERM; eauto; i. clear TERM; rename H into TERM. des. ss.
      inv STEP_TGT. ss. unfold ILang.is_terminal in TERMINAL_SRC. des.
      rewrite TERMINAL_SRC in TERMINAL. inv TERMINAL. inv LANG; ss.
    - ii. exfalso.
      unfold sim_seq_terminal_case in TERM. hexploit TERM; eauto; i. clear TERM; rename H into TERM. des. ss.
      unfold ILang.is_terminal in TERMINAL_TGT. des.
      rewrite TERMINAL_TGT in STEP_TGT. inv STEP_TGT.
    - ii.
      unfold sim_seq_terminal_case in TERM. hexploit TERM; eauto; i. clear TERM; rename H into TERM. des. ss.
      exists (SeqThread.mk st_src1 p o). ss. exists []; exists Flags.bot. splits; try red.
      3: left; ss.
      2: econs 1.
      eapply na_steps_steps; eauto.
  Qed.

  Definition ubM (e: MachineEvent.t) := (e = MachineEvent.failure).

  Lemma sim_seq_na
        r g p d (src tgt: SeqState.t (lang _))
        (PARTIAL: sim_seq_partial_case p d src tgt)
        (NATGT: exists st_tgt1 e, (SeqState.na_step p e tgt st_tgt1) /\ (<<NOUB: not (ubM e)>>))
        (NA: sim_seq_na_step_case (gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term) p d src tgt)
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d src tgt.
  Proof.
    gstep. econs 1; i.
    2:{ auto. }
    - ii. exfalso.
      des. unfold sim_seq_na_step_case in NA. hexploit NA; eauto; i. clear NA; rename H into NA. des. ss.
      unfold ILang.is_terminal in TERMINAL_TGT. des.
      inv NATGT. ss. clarify. inv LANG.
    - ii. exfalso.
      des. unfold sim_seq_na_step_case in NA. hexploit NA; eauto; i. clear NA; rename H into NA. des. ss.
      inv NATGT. ss.
      depgen NOUB. depgen STEP_TGT. depgen ATOMIC. depgen LANG. depgen LOCAL.
      clear; i.
      inv LANG; ss; clarify.
      + inv STEP_TGT; ss; clarify.
      + inv STEP_TGT; ss; clarify.
      + inv STEP_TGT; ss; clarify.
        inv LOCAL; ss; clarify.
        destruct ord; ss.
      + inv STEP_TGT; ss; clarify.
        inv LOCAL; ss; clarify.
        destruct ord; ss.
      + inv STEP_TGT; ss; clarify.
        * inv LOCAL; ss; clarify.
          destruct ORD.
          { destruct ordr; ss. }
          { destruct ordw; ss. }
        * inv LOCAL; ss; clarify.
          unfold ubM in NOUB. ss.
      + inv STEP_TGT; ss; clarify.
        * inv LOCAL; ss; clarify.
          destruct ordr; ss.
        * inv LOCAL; ss; clarify.
          destruct ordr; ss.
      + inv STEP_TGT; ss; clarify.
        inv LOCAL; ss; clarify.
      + inv STEP_TGT; ss; clarify.
        inv LOCAL; ss; clarify.
      + inv STEP_TGT; ss; clarify.
    - auto.
  Qed.

  Lemma sim_seq_atomic
        r g p d (src tgt: SeqState.t (lang _))
        (PARTIAL: sim_seq_partial_case p d src tgt)
        (NOUB: forall tgt1 e, SeqState.na_step p e tgt tgt1 -> not (ubM e))
        (ATGT: exists st_tgt1 e,
            (<<STEP: Language.step _ e (SeqState.state tgt) st_tgt1>>) /\
            (<<ATOMIC: is_atomic_event e>>))
        (AT: sim_seq_at_step_case (gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term) p d src tgt)
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d src tgt.
  Proof.
    gstep. econs 1; i.
    3:{ eauto. }
    - ii. exfalso.
      des. unfold sim_seq_at_step_case in AT. hexploit AT; eauto; i. clear AT; rename H into AT. des. ss.
      unfold ILang.is_terminal in TERMINAL_TGT. des.
      rewrite TERMINAL_TGT in STEP. inv STEP.
    - ii. exfalso.
      des. unfold sim_seq_at_step_case in AT. hexploit AT; eauto; i. clear AT; rename H into AT. des. ss.
      depgen NOUB. depgen STEP. depgen ATOMIC. depgen STEP_TGT. clear. i.
      hexploit NOUB; eauto. i. clear NOUB; rename H into NOUB.
      inv STEP_TGT. ss. inv LANG; ss; clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
        destruct ord; ss; clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
        destruct ord; ss; clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
        * apply andb_prop in ATOMIC. des. destruct ORD.
          { destruct ordr; ss. }
          { destruct ordw; ss. }
        * unfold ubM in NOUB. clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
        * apply andb_prop in ATOMIC; des. destruct ordr; ss.
        * destruct ordr; ss.
      + inv LOCAL; ss; clarify.
      + inv LOCAL; ss; clarify.
      + inv LOCAL; ss; clarify. inv STEP; ss; clarify.
    - auto.
  Qed.



  Lemma sim_seq_tau
        r g p d
        src tgt
        src_m tgt_m
        (src_t tgt_t: itree _ _)
        (SRC: src = @SeqState.mk (lang _) (tau;; src_t) src_m)
        (TGT: tgt = @SeqState.mk (lang _) (tau;; tgt_t) tgt_m)
        (PARTIAL: sim_seq_partial_case p d src tgt)
        (SIM: gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term p d
                      (@SeqState.mk (lang _) src_t src_m)
                      (@SeqState.mk (lang _) tgt_t tgt_m))
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d src tgt.
  Proof.
    clarify.
    eapply sim_seq_na; eauto.
    { exists (SeqState.mk (lang _) tgt_t tgt_m). exists MachineEvent.silent. split; ss; eauto.
      econs; ss; eauto.
      - econs 1; eauto.
      - econs 1; eauto.
    }
    ii. inv STEP_TGT. inv LANG. inv LOCAL.
    exists (SeqState.mk (lang _) (tau;; src_t) src_m), (SeqState.mk (lang _) src_t src_m).
    splits; ss; eauto.
    econs 1; eauto. econs 1; ss; eauto.
    - econs 1; eauto.
    - econs 1; eauto.
  Qed.

  Lemma sim_seq_tau_tgt
        r g p d
        src tgt
        src_m tgt_m
        (src_t tgt_t: itree _ _)
        (SRC: src = @SeqState.mk (lang _) (src_t) src_m)
        (TGT: tgt = @SeqState.mk (lang _) (tau;; tgt_t) tgt_m)
        (PARTIAL: sim_seq_partial_case p d src tgt)
        (SIM: gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term p d
                      (@SeqState.mk (lang _) src_t src_m)
                      (@SeqState.mk (lang _) tgt_t tgt_m))
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d src tgt.
  Proof.
    clarify.
    eapply sim_seq_na; eauto.
    { eexists. exists MachineEvent.silent. split; ss; eauto.
      econs; ss; eauto.
      - econs 1; eauto.
      - econs 1; eauto.
    }
    ii. inv STEP_TGT. inv LANG. inv LOCAL.
    do 2 eexists. splits; ss; eauto.
    econs 2; eauto.
  Qed.

  Lemma seq_thread_failure
        src src_m p o
    :
      SeqThread.failure (SeqState.na_step (lang:=lang R_src))
                        (@SeqThread.mk (lang R_src)
                                       (@SeqState.mk (lang R_src) (v <- trigger MemE.abort;; src v) src_m)
                                       p o).
  Proof.
    econs. red. econs 1. econs. rewrite bind_trigger. econs. econs.
  Qed.

  Lemma sim_seq_ub:
    forall r g p d src tgt src_m tgt_m,
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d
             (@SeqState.mk (lang _) (v <- trigger MemE.abort;; src v) src_m)
             (@SeqState.mk (lang _) (tgt) tgt_m).
  Proof.
    i. gstep. econs 2. ii. do 3 eexists. splits.
    - econs 1.
    - econs 1.
    - eapply seq_thread_failure.
  Qed.

  Lemma partial_same_mem
        (src: SeqState.t (lang R_src)) (tgt: SeqState.t (lang R_tgt)) p
        (SAME: (SeqState.memory src) = (SeqState.memory tgt))
    :
      sim_seq_partial_case p Flags.bot src tgt.
  Proof.
    apply sim_seq_partial_imm. rewrite SAME. refl.
  Qed.

  Lemma sim_seq_partial_case_mon
        p d0 d1 (src: SeqState.t (lang R_src)) (tgt: SeqState.t (lang R_tgt))
        (LE: Flags.le d0 d1)
        (PSIM: sim_seq_partial_case p d1 src tgt)
    :
      sim_seq_partial_case p d0 src tgt.
  Proof.
    unfold sim_seq_partial_case in *. ii. hexploit PSIM; clear PSIM; eauto. i; des.
    - esplits; eauto.
      left. etrans. 2: eauto. apply Flags.join_spec.
      + etrans. eauto. eapply Flags.join_ge_l.
      + eapply Flags.join_ge_r.
    - esplits; eauto.
  Qed.

End SIMAUX.
