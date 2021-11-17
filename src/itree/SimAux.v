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
Require Import iCompatibility.

Require Import Simple.
Require Import FlagAux.
Require Import ITreeLang.



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
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p d src tgt.
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
        (NA: sim_seq_na_step_case (gupaco4 (_sim_seq term) (cpn4 (_sim_seq term)) g) p d src tgt)
    :
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p d src tgt.
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
        (AT: sim_seq_at_step_case (gupaco4 (_sim_seq term) (cpn4 (_sim_seq term)) g) p d src tgt)
    :
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p d src tgt.
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
        (SIM: gupaco4 (_sim_seq term) (cpn4 (_sim_seq term)) g p d
                      (@SeqState.mk (lang _) src_t src_m)
                      (@SeqState.mk (lang _) tgt_t tgt_m))
    :
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p d src tgt.
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
        (SIM: gupaco4 (_sim_seq term) (cpn4 (_sim_seq term)) g p d
                      (@SeqState.mk (lang _) src_t src_m)
                      (@SeqState.mk (lang _) tgt_t tgt_m))
    :
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p d src tgt.
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
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p d
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





Section UPTO.

  Variable lang_src: language.
  Variable lang_tgt: language.

  Variable sim_terminal: forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

  Lemma event_step_flags
        i o p0 p1 m0 m1
        (STEP: SeqEvent.step i o p0 m0 p1 m1)
    :
      Flags.le (SeqMemory.flags m0)
               (Flags.join (SeqMemory.flags m1) (SeqEvent.written i)).
  Proof.
    inv STEP.
    inv ACQ.
    { clear H. inv UPD.
      { clear H. inv REL.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          rewrite flags_join_bot_l. rewrite flags_join_bot_r. refl.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          rewrite flags_join_bot_l.
          inv MEM. ss. rewrite flags_join_bot_l. refl.
      }
      { clear H. inv REL.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. inv MEM0. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
      }
    }
    { clear H. inv MEM. ss. inv UPD; ss.
      { clear H. inv REL; ss.
        - clear H. apply Flags.join_ge_l.
        - clear H. inv MEM; ss. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          do 2 rewrite flags_join_bot_l. refl.
      }
      { clear H. inv REL; ss.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. apply Flag.join_ge_l.
        - clear H. unfold SeqEvent.written. rewrite <- H1. rewrite <- H2.
          inv MEM. ss. inv MEM0. ss. des_ifs.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
          + ii. unfold Flags.update, Flags.add, Flags.join. des_ifs. do 2 rewrite flag_join_bot_l. refl.
      }
    }
  Qed.

  Lemma at_step_flags
        e i o (th0 th1: SeqThread.t (lang_src))
        (STEP: SeqThread.at_step e i o th0 th1)
    :
      Flags.le (SeqMemory.flags (SeqState.memory (SeqThread.state th0)))
               (Flags.join (SeqMemory.flags (SeqState.memory (SeqThread.state th1))) (SeqEvent.written i)).
  Proof.
    inv STEP. ss. eapply event_step_flags; eauto.
  Qed.


  Lemma one_na_step_flags
        (st1 st2: SeqState.t (lang_src)) p
        (STEP: SeqState.na_step p MachineEvent.silent st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    inv STEP. inv LOCAL; try refl. des_ifs.
    destruct m0; ss. ii. unfold Flags.update. condtac.
    - destruct (flags loc0); ss.
    - refl.
  Qed.

  Lemma na_step_flags
        (th0 th1: SeqThread.t (lang_src))
        (STEP: SeqThread.na_step (@SeqState.na_step lang_src) MachineEvent.silent th0 th1)
    :
      Flags.le (SeqMemory.flags (SeqState.memory (SeqThread.state th0)))
               (SeqMemory.flags (SeqState.memory (SeqThread.state th1))).
  Proof.
    inv STEP. eapply one_na_step_flags; eauto.
  Qed.

  Lemma na_steps_flags
        (st1 st2: SeqState.t (lang_src)) p
        (STEPS: rtc (SeqState.na_step p MachineEvent.silent) st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    induction STEPS.
    { refl. }
    hexploit one_na_step_flags; eauto.
    i. etrans; eauto.
  Qed.

  Lemma one_na_step_flags_events
        (st1 st2: SeqState.t (lang_src)) p e
        (STEP: SeqState.na_step p e st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    destruct e.
    { eapply one_na_step_flags; eauto. }
    - inv STEP. inv LOCAL. des_ifs.
    - inv STEP. inv LOCAL; ss; try refl.
      des_ifs. ii. unfold Flags.update. clear Heq. des_ifs. destruct (SeqMemory.flags m0 loc); ss. refl.
  Qed.

  Lemma opt_na_step_flags_events
        (st1 st2: SeqState.t (lang_src)) p e
        (STEP: SeqState.na_opt_step p e st1 st2)
    :
      Flags.le st1.(SeqState.memory).(SeqMemory.flags) st2.(SeqState.memory).(SeqMemory.flags).
  Proof.
    inv STEP. eapply one_na_step_flags_events; eauto. refl.
  Qed.


  Lemma partial_step_flags tr w th0 th1
        (STEPS: SeqThread.steps (@SeqState.na_step lang_src) tr th0 th1)
        (WF: Oracle.wf th0.(SeqThread.oracle))
        (TRACE: SeqThread.writing_trace tr w)
    :
      (Flags.le (th0.(SeqThread.state).(SeqState.memory).(SeqMemory.flags))
                (Flags.join th1.(SeqThread.state).(SeqState.memory).(SeqMemory.flags) w)).
  Proof.
    depgen w. induction STEPS; i; ss.
    { inv TRACE. rewrite flags_join_bot_r. refl. }
    { hexploit IHSTEPS; clear IHSTEPS; eauto.
      { inv STEP. ss. }
      { i. hexploit na_step_flags; eauto. i. etrans. 2:eauto. auto. }
    }
    inv TRACE.
    hexploit IHSTEPS; clear IHSTEPS; eauto.
    { inv STEP. ss. unfold Oracle.wf in WF. punfold WF. 2: eapply Oracle.wf_mon.
      inv WF. hexploit WF0; clear WF0; eauto. i; des. pclearbot. auto. }
    i. rename H into IH.
    hexploit at_step_flags; eauto. i. etrans. eauto. clear H.
    match goal with | [|-_ _ (_ ?a (_ ?b ?c))] =>
                      replace (Flags.join a (Flags.join b c)) with (Flags.join (Flags.join a c) b) end.
    2:{ rewrite flags_join_comm. rewrite flags_join_assoc. symmetry.
        rewrite flags_join_assoc. f_equal. rewrite flags_join_comm. auto. }
    apply Flags.join_mon_l. auto.
  Qed.


  Variant deferred_le_sf_ctx
          (sim_seq:
             forall
               (p0: Perms.t) (d0: Flags.t)
               (st_src0: SeqState.t lang_src)
               (st_tgt0: SeqState.t lang_tgt), Prop)
          (p0: Perms.t) (d0: Flags.t)
          (st_src0: SeqState.t lang_src)
          (st_tgt0: SeqState.t lang_tgt): Prop :=
  | deferred_le_sf_ctx_intro
      d1
      (LESF: Flags.le d0 (Flags.join d1 (st_src0.(SeqState.memory).(SeqMemory.flags))))
      (SIM: sim_seq p0 d1 st_src0 st_tgt0).

  Lemma deferred_le_sf_ctx_mon: monotone4 deferred_le_sf_ctx.
  Proof. ii. inv IN. econs 1; eauto. Qed.

  Hint Resolve deferred_le_sf_ctx_mon: paco.

  Lemma deferred_le_sf_ctx_wrespectful: wrespectful4 (@_sim_seq lang_src lang_tgt sim_terminal) deferred_le_sf_ctx.
  Proof.
    econs; eauto with paco.
    ii. inv PR. dup SIM. apply GF in SIM. inv SIM.
    2:{ econs 2. unfold sim_seq_failure_case in *. i. hexploit FAILURE; clear FAILURE; eauto. }
    econs 1.
    4:{ unfold sim_seq_partial_case in PARTIAL.
        ii. hexploit PARTIAL; clear PARTIAL; eauto. i; des.
        - esplits; eauto.
          hexploit partial_step_flags; eauto. i. ss.
          left. etrans. eapply Flags.join_mon_l. eapply LESF.
          etrans. rewrite <- flags_join_assoc.
          match goal with | [|- _ (_ _ (Flags.join ?a ?b)) _] => replace (Flags.join a b) with (Flags.join b a) end.
          2:{ apply flags_join_comm. }
          rewrite flags_join_assoc. eapply Flags.join_mon_l. eapply FLAGS.
          rewrite flags_join_comm.
          apply Flags.join_spec; auto. rewrite flags_join_comm. auto. refl.
        - esplits; eauto.
    }
    { clear NASTEP ATSTEP PARTIAL. unfold sim_seq_terminal_case in *. i.
      hexploit TERMINAL; clear TERMINAL; eauto. i; des.
      eexists. splits; eauto.
      etrans. eapply Flags.join_mon_l. eapply LESF. rewrite <- flags_join_assoc.
      match goal with | [|- _ (_ _ (Flags.join ?a ?b)) _] => replace (Flags.join a b) with (Flags.join b a) end.
      2:{ apply flags_join_comm. }
      rewrite flags_join_assoc. etrans. eapply Flags.join_mon_l. eapply FLAG.
      hexploit na_steps_flags; eauto. i. rewrite flags_join_comm.
      hexploit Flags.join_spec. eapply H. refl. i; auto.
    }
    { clear TERMINAL ATSTEP PARTIAL. unfold sim_seq_na_step_case in *. i.
      hexploit NASTEP; clear NASTEP; eauto. i; des.
      do 2 eexists. splits; eauto. eapply rclo4_clo_base. econs; eauto.
      hexploit opt_na_step_flags_events; eauto. i.
      hexploit na_steps_flags; eauto. i. etrans. eapply LESF. apply Flags.join_mon_r.
      etrans. eapply H0. auto.
    }
    { clear TERMINAL NASTEP PARTIAL. unfold sim_seq_at_step_case in *. i.
      hexploit ATSTEP; clear ATSTEP; eauto. i; des.
      do 3 eexists. splits; eauto. i. hexploit SIM; clear SIM; eauto. i; des.
      do 2 eexists. eexists. esplits; eauto.
      2:{ eapply rclo4_clo_base. econs. refl. eauto. }
      ss. eapply SeqEvent.input_match_mon.
      3: refl.
      { eapply SeqEvent.step_input_match. eapply STEP_SRC. eapply MATCH. }
      etrans. eapply LESF. apply Flags.join_mon_r. eapply na_steps_flags; eauto.
    }
  Qed.

  Lemma deferred_le_sf_ctx_spec: deferred_le_sf_ctx <5=
                                 gupaco4 (@_sim_seq lang_src lang_tgt sim_terminal)
                                         (cpn4 (@_sim_seq lang_src lang_tgt sim_terminal)).
  Proof. i. eapply wrespect4_uclo; eauto with paco. eapply deferred_le_sf_ctx_wrespectful. Qed.


  Lemma sim_seq_upto_deferred
        g p d0 d1 src tgt
        (LE: Flags.le d0 d1)
        (SIM: gupaco4 (@_sim_seq lang_src lang_tgt sim_terminal)
                      (cpn4 (@_sim_seq lang_src lang_tgt sim_terminal)) g p d1 src tgt)
    :
      gupaco4 (@_sim_seq lang_src lang_tgt sim_terminal)
              (cpn4 (@_sim_seq lang_src lang_tgt sim_terminal)) g p d0 src tgt.
  Proof.
    guclo deferred_le_sf_ctx_spec. econs; eauto. etrans; eauto. apply Flags.join_ge_l.
  Qed.

End UPTO.
Hint Resolve cpn4_wcompat: paco.
