Require Import Bool.
Require Import RelationClasses.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import List.

Require Import SeqLib.
Require Import Simple.
Require Import OracleFacts.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module SeqTrace.
  Variant result: Type :=
  | term (v: ValueMap.t) (f: Flags.t)
  | partial (f: Flags.t)
  | ub
  .

  Definition t: Type := list (ProgramEvent.t * SeqEvent.input * Oracle.output) * result.

  Inductive le: Flags.t -> t -> t -> Prop :=
  | le_term
      d v_src v_tgt f_src f_tgt
      (VAL: ValueMap.le v_tgt v_src)
      (FLAG: Flags.le (Flags.join d f_tgt) f_src)
    :
      le d ([], term v_tgt f_tgt) ([], term v_src f_src)
  | le_partial
      d tr_src f_src f_tgt w
      (TRACE: SeqThread.writing_trace d tr_src w)
      (FLAG: Flags.le (Flags.join d f_tgt) (Flags.join w f_src))
    :
      le d ([], partial f_tgt) (tr_src, partial f_src)
  | le_ub
      d tr_src tr_tgt w
      (TRACE: SeqThread.writing_trace d tr_src w)
    :
      le d tr_tgt (tr_src, ub)
  | le_cons
      d0 d1 e_src e_tgt i_src i_tgt o tr_src tr_tgt r_src r_tgt
      (LE: le d1 (tr_tgt, r_tgt) (tr_src, r_src))
      (MATCH: SeqEvent.input_match d0 d1 i_src i_tgt)
      (EVENT: ProgramEvent.le e_tgt e_src)
    :
      le d0 ((e_tgt, i_tgt, o)::tr_tgt, r_tgt) ((e_src, i_src, o)::tr_src, r_src)
  .

  Lemma le_deferred_mon d0 d1 tr0 tr1
        (DEFERRED: Flags.le d0 d1)
        (LE: le d1 tr0 tr1)
    :
      le d0 tr0 tr1.
  Proof.
    induction LE.
    { econs 1; eauto. etrans; eauto.
      eapply Flags.join_mon_l. eauto. }
    { econs 2.
      { eapply SeqThread.writing_trace_mon; eauto. }
      { etrans; eauto. eapply Flags.join_mon_l; eauto. }
    }
    { econs 3; eauto. eapply SeqThread.writing_trace_mon; eauto. }
    { econs 4.
      { eauto. }
      { eapply SeqEvent.input_match_mon; eauto. refl. }
      { eauto. }
    }
  Qed.

  Program Instance le_PreOrder: PreOrder (le Flags.bot).
  Next Obligation.
  Proof.
    ii. destruct x. induction l.
    { destruct r.
      { econs 1; refl. }
      { econs 2; eauto.
        { econs 1. }
        { refl. }
      }
      { econs 3; eauto. econs 1. }
    }
    { destruct a as [[e i] o]. econs 4; eauto.
      { eapply SeqEvent.input_match_bot; eauto. }
      { refl. }
    }
  Qed.
  Next Obligation.
  Proof.
    ii. destruct z. ginduction l.
    { i. inv H0.
      { inv H. econs 1.
        { etrans; eauto. }
        { etrans; eauto. }
      }
      { inv TRACE. inv H. inv TRACE. econs 2.
        { econs. }
        { etrans; eauto. }
      }
      { econs 3. econs. }
    }
    { i.
  Admitted.

  Definition incl (b0: t -> Prop) (b1: t -> Prop): Prop :=
    forall tr0, b0 tr0 -> exists tr1, b1 tr1 /\ le Flags.bot tr0 tr1.

  Program Instance incl_PreOrder: PreOrder incl.
  Next Obligation.
  Proof.
    ii. exists tr0. split; auto. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. apply H in H1. des. apply H0 in H1. des.
    esplits; eauto. etrans; eauto.
  Qed.
End SeqTrace.


Module SeqBehavior.
Section LANG.
  Variable lang: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang -> SeqState.t lang -> Prop.

  Inductive behavior: forall (th0: SeqThread.t lang) (tr: SeqTrace.t), Prop :=
  | behavior_term
      st v f p o
      (TERMINAL: lang.(Language.is_terminal) st)
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f)) p o) ([], SeqTrace.term v f)
  | behavior_partial
      st v f p o
    :
      behavior (SeqThread.mk (SeqState.mk _ st (SeqMemory.mk v f)) p o) ([], SeqTrace.partial f)
  | behavior_ub
      st m p o
      (FAILURE: SeqThread.failure state_step (SeqThread.mk (SeqState.mk _ st m) p o))
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) ([], SeqTrace.ub)
  | behavior_na_step
      th0 th1 tr
      (STEP: SeqThread.na_step state_step MachineEvent.silent th0 th1)
      (BEHAVIOR: behavior th1 tr)
    :
      behavior th0 tr
  | behavior_at_step
      e i o th0 th1 es st
      (STEP: SeqThread.at_step e i o th0 th1)
      (BEHAVIOR: behavior th1 (es, st))
    :
      behavior th0 ((e, i, o)::es, st)
  .
End LANG.

Definition refine
           (lang_tgt lang_src: language)
           (st_tgt: lang_tgt.(Language.state)) (st_src: lang_src.(Language.state))
  : Prop :=
  forall p m o (WF: Oracle.wf o),
    SeqTrace.incl
      (behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
      (behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)).
End SeqBehavior.


Section DETERMINISM.
  Variable lang: language.

  Definition similar (e0 e1: ProgramEvent.t): Prop :=
    match e0, e1 with
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ ord0 = ord1
    | ProgramEvent.write loc0 val0 ord0, ProgramEvent.write loc1 val1 ord1 =>
      loc0 = loc1 /\ ord0 = ord1 /\ val0 = val1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ ordr0 = ordr1 /\ ordw0 = ordw1 /\ (valr0 = valr1 -> valw0 = valw1)
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ ord0 = ordr1 /\ val0 <> valr1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ ordr0 = ord1 /\ valr0 <> val1
    | ProgramEvent.fence ordr0 ordw0, ProgramEvent.fence ordr1 ordw1 =>
      ordr0 = ordr1 /\ ordw0 = ordw1
    | _, _ => e0 = e1
    end.

  Lemma similar_le_eq
        e1 e2 e
        (SIMILAR: similar e1 e2)
        (LE1: ProgramEvent.le e e1)
        (LE2: ProgramEvent.le e e2):
    e1 = e2.
  Proof.
    destruct e1, e2, e; ss.
    - inv LE1. inv LE2. ss.
    - des. subst. ss.
    - des. subst. exploit SIMILAR2; eauto. i. subst. ss.
    - inv LE1. inv LE2. ss.
  Qed.

  Variant _deterministic (deterministic: lang.(Language.state) -> Prop) (st0: lang.(Language.state)): Prop :=
  | deterministic_intro
      (PRESERVE:
         forall e st1 (STEP: lang.(Language.step) e st0 st1),
           deterministic st1)
      (STEP_TERMINAL:
         forall e st1 (STEP: lang.(Language.step) e st0 st1)
                (TERMINAL: lang.(Language.is_terminal) st0), False)
      (STEP_STEP:
         forall e1 st1 (STEP1: lang.(Language.step) e1 st0 st1)
                e2 st2 (STEP2: lang.(Language.step) e2 st0 st2),
           similar e1 e2 /\ (e1 = e2 -> st1 = st2))
      (NO_NA_UPDATE:
         forall loc valr valw ordr ordw st1
           (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st0 st1),
           Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
  .

  Lemma deterministic_mon: monotone1 _deterministic.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.
  Hint Resolve deterministic_mon: paco.

  Definition deterministic := paco1 _deterministic bot1.
End DETERMINISM.
#[export] Hint Resolve deterministic_mon: paco.

Lemma deterministic_steps
      lang e1 e2 st st1 st2
      (DETERM: deterministic lang st)
      (STEP1: lang.(Language.step) e1 st st1)
      (STEP2: lang.(Language.step) e2 st st2):
  similar e1 e2 /\ (e1 = e2 -> st1 = st2).
Proof.
  punfold DETERM. inv DETERM. eauto.
Qed.

Lemma step_deterministic
      lang e st0 st1
      (DETERM: deterministic lang st0)
      (STEP: lang.(Language.step) e st0 st1):
  deterministic lang st1.
Proof.
  punfold DETERM. inv DETERM.
  exploit PRESERVE; eauto. i. inv x; done.
Qed.


Section ADEQUACY.
  Variable lang_src lang_tgt: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang_src -> SeqState.t lang_src -> Prop.

  Definition lang_read_value (lang: language): Prop :=
    (<<READ: forall loc val ord st1 st2 val'
               (STEP: lang.(Language.step) (ProgramEvent.read loc val ord) st1 st2),
        (<<READ': exists st2',
            lang.(Language.step) (ProgramEvent.read loc val' ord) st1 st2'>>) \/
        (<<UPDATE': exists valw ordw st2',
            lang.(Language.step) (ProgramEvent.update loc val' valw ord ordw) st1 st2'>>)>>) /\
    (<<UPDATE: forall loc valr valw ordr ordw st1 st2 valr'
               (STEP: lang.(Language.step) (ProgramEvent.update loc valr valw ordr ordw) st1 st2),
        (<<READ': exists st2',
            lang.(Language.step) (ProgramEvent.read loc valr' ordr) st1 st2'>>) \/
        (<<UPDATE': exists valw' st2',
            lang.(Language.step) (ProgramEvent.update loc valr' valw' ordr ordw) st1 st2'>>)>>).

  Hypothesis lang_read_value_src: lang_read_value lang_src.

  Hypothesis state_step_subset: state_step <4= (@SeqState.na_step _).

  Hypothesis state_step_determ:
    forall p st e0 e1 st0 st1
           (STEP0: state_step p e0 st st0)
           (STEP1: state_step p e1 st st1),
      e0 = e1 /\ st0 = st1.

  Lemma refine_mon
        (st_tgt: lang_tgt.(Language.state)) (st_src: lang_src.(Language.state))
        (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
        (TOP: forall p m o (WF: Oracle.wf o),
            SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
            <1=
            SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)):
    forall p m o (WF: Oracle.wf o),
      SeqTrace.incl
        (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
        (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)).
  Proof.
    ii. specialize (TOP p m o WF).
    exploit REFINE; eauto. i. des. eauto.
  Qed.


  (** lemmas on event and event step *)

  Lemma le_is_accessing
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_accessing e1 <-> is_accessing e2.
  Proof.
    destruct e1, e2; ss; inv LE; des; subst; ss.
  Qed.

  Lemma le_is_acquire
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_acquire e1 <-> is_acquire e2.
  Proof.
    destruct e1, e2; ss; inv LE; des; subst; ss.
  Qed.

  Lemma le_is_release
        e1 e2
        (LE: ProgramEvent.le e1 e2):
    is_release e1 <-> is_release e2.
  Proof.
    destruct e1, e2; ss; inv LE; des; subst; ss.
  Qed.

  Lemma le_wf_output
        e1 e2 o
        (LE: ProgramEvent.le e1 e2):
    Oracle.wf_output e1 o <-> Oracle.wf_output e2 o.
  Proof.
    unfold Oracle.wf_output. unnw.
    erewrite le_is_accessing, le_is_acquire, le_is_release; eauto.
  Qed.

  Lemma event_step_update_exists
        e (o: option Perm.t) p1 m1
        (WF_OUTPUT: o <-> is_accessing e):
    exists i,
      (<<WF: forall loc v_new,
          ((exists v_old f_old, i = Some (loc, v_old, f_old, v_new)) <->
           (is_accessing e = Some (loc, v_new)))>>) /\
      exists p2 m2, (<<STEP: SeqEvent.step_update i o p1 m1 p2 m2>>).
  Proof.
    exists (match is_accessing e with
       | Some (loc, v_new) =>
         Some (loc, m1.(SeqMemory.value_map) loc, m1.(SeqMemory.flags) loc, v_new)
       | None => None
       end).
    split.
    { split; i; des_ifs; des; ss; eauto. inv H. ss. }
    { des_ifs; destruct o; try by intuition.
      - esplits. econs; eauto. econs.
      - esplits. econs.
    }
  Qed.

  Lemma event_step_acquire_exists
        e (o: option (Perms.t * ValueMap.t)) p1 m1
        (WF_OUTPUT: o <-> is_acquire e):
    exists (i: option Flags.t),
      (<<WF: i <-> is_acquire e>>) /\
      exists p2 m2, (<<STEP: SeqEvent.step_acquire i o p1 m1 p2 m2>>).
  Proof.
    exists (if is_acquire e then Some m1.(SeqMemory.flags) else None).
    split.
    { split; i; des_ifs; des; ss; eauto. }
    { des_ifs; destruct o as [[]|]; try by intuition.
      - esplits. econs; eauto. econs.
      - esplits. econs.
    }
  Qed.

  Lemma event_step_release_exists
        e (o: option Perms.t) p1 m1
        (WF_OUTPUT: o <-> is_release e):
    exists (i: option (ValueMap.t * Flags.t)),
      (<<WF: i <-> is_release e>>) /\
      exists p2 m2, (<<STEP: SeqEvent.step_release i o p1 m1 p2 m2>>).
  Proof.
    exists (if is_release e then Some (m1.(SeqMemory.value_map), m1.(SeqMemory.flags)) else None).
    split.
    { split; i; des_ifs; des; ss; eauto. }
    { des_ifs; destruct o; try by intuition.
      - esplits. econs; eauto. econs.
      - esplits. econs.
    }
  Qed.

  Lemma event_step_exists
        e o p1 m1
        (WF_OUTPUT: Oracle.wf_output e o):
    exists i,
      (<<WF: SeqEvent.wf_input e i>>) /\
      exists p2 m2,
        (<<STEP: SeqEvent.step i o p1 m1 p2 m2>>).
  Proof.
    unfold Oracle.wf_output in *. destruct o. ss. splitsH.
    exploit (event_step_update_exists e out_access p1 m1); ss. i. des.
    exploit (event_step_acquire_exists e out_acquire p2 m2); ss. i. des.
    exploit (event_step_release_exists e out_release p0 m0); ss. i. des.
    exists (SeqEvent.mk_input i i0 i1). split.
    - unfold SeqEvent.wf_input. splits; ss.
    - esplits. econs; eauto.
  Qed.


  (** definitions and lemmas on match_trace *)

  Variant min_match (I: Type) (imatch: forall (d1 d2: Flags.t) (i_src i_tgt: I), Prop)
          (d1 d2: Flags.t) (i_src i_tgt: I): Prop :=
  | min_match_intro
      (MATCH: imatch d1 d2 i_src i_tgt)
      (MIN: forall d (MATCH: imatch d1 d i_src i_tgt), Flags.le d2 d)
  .

  Lemma min_access_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.in_access_match d1 d2 i_src i_tgt):
    exists d_min, min_match SeqEvent.in_access_match d1 d_min i_src i_tgt.
  Proof.
    i. inv MATCH.
    { exists d1. econs; [econs 1; refl|]. i. inv MATCH. ss. }
    exists (fun loc => if Loc.eq_dec loc l then false else (d1 loc)).
    econs.
    - econs; eauto. i. condtac; ss. refl.
    - i. inv MATCH. ii. condtac; ss. eauto.
  Qed.

  Lemma min_acquire_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.in_acquire_match d1 d2 i_src i_tgt):
    exists d_min, min_match SeqEvent.in_acquire_match d1 d_min i_src i_tgt.
  Proof.
    inv MATCH.
    { exists d1. econs; [econs 1; refl|]. i. inv MATCH. ss. }
    exists Flags.bot. econs; ss. econs; eauto.
  Qed.
  
  Lemma min_release_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.in_release_match d1 d2 i_src i_tgt):
    exists d_min, min_match SeqEvent.in_release_match d1 d_min i_src i_tgt.
  Proof.
    inv MATCH.
    { exists d1. econs; [econs 1; refl|]. i. inv MATCH. ss. }
    exists (fun loc => if Const.le (v_tgt loc) (v_src loc)
               then andb (orb (f_tgt loc) (d1 loc)) (negb (f_src loc))
               else true).
    econs; ii.
    - econs; ii; des_ifs.
      unfold Flags.join. condtac; ss.
      + destruct (f_tgt loc), (d1 loc), (f_src loc); ss.
      + destruct (f_tgt loc), (d1 loc), (f_src loc); ss.
    - inv MATCH. condtac; ss.
      + specialize (DEFERRED0 loc). unfold Flags.join in *.
        destruct (f_tgt loc), (d1 loc), (f_src loc), (d loc); ss.
      + specialize (VAL0 loc). destruct (d loc); ss.
        exploit VAL0; eauto. i. congr.
  Qed.

  Lemma min_match_le_min
        I imatch d1 d2 i_src i_tgt
        (MIN: @min_match I imatch d1 d2 i_src i_tgt)
        (MON: forall d1 d2 d1' d2' i_src i_tgt
                (MATCH: imatch d1 d2 i_src i_tgt)
                (LE1: Flags.le d1' d1)
                (LE2: Flags.le d2 d2'),
            imatch d1' d2' i_src i_tgt)
        d1' d2'
        (MATCH: imatch d1' d2' i_src i_tgt)
        (LE: Flags.le d1 d1'):
    Flags.le d2 d2'.
  Proof.
    exploit MON; try exact MATCH; try exact LE; try refl. i.
    inv MIN. eapply MIN0; eauto.
  Qed.

  Lemma min_input_match_exists
        d1 d2 i_src i_tgt
        (MATCH: SeqEvent.input_match d1 d2 i_src i_tgt):
    exists d_min, (<<MIN: min_match SeqEvent.input_match d1 d_min i_src i_tgt>>).
  Proof.
    inv MATCH.
    exploit min_access_match_exists; eauto. intro MIN_ACCESS. des.
    hexploit min_match_le_min; try exact MIN_ACCESS; try exact ACCESS;
      eauto using SeqEvent.in_access_match_mon; try refl. i.
    exploit SeqEvent.in_acquire_match_mon; try exact ACQUIRE; try exact H; try refl. i.
    exploit min_acquire_match_exists; try exact x0. intro MIN_ACQUIRE. des.
    hexploit min_match_le_min; try exact MIN_ACQUIRE; try exact ACQUIRE;
      eauto using SeqEvent.in_acquire_match_mon. i.
    exploit SeqEvent.in_release_match_mon; try exact RELEASE; try exact H0; try refl. i.
    exploit min_release_match_exists; try exact x1. intro MIN_RELEASE. des.
    clear d0 d2 d3 ACCESS ACQUIRE RELEASE H x0 H0 x1.
    exists d_min1. econs.
    { econs; [apply MIN_ACCESS|apply MIN_ACQUIRE|apply MIN_RELEASE]. }
    i. inv MATCH.
    hexploit min_match_le_min; try exact MIN_ACCESS; try exact ACCESS;
      eauto using SeqEvent.in_access_match_mon; try refl. i.
    hexploit min_match_le_min; try exact MIN_ACQUIRE; try exact ACQUIRE;
      eauto using SeqEvent.in_acquire_match_mon. i.
    hexploit min_match_le_min; try exact MIN_RELEASE; try exact RELEASE;
      eauto using SeqEvent.in_release_match_mon.
  Qed.

  Inductive match_trace (imatch: forall (d1 d2: Flags.t) (i_src i_tgt: SeqEvent.input), Prop):
    forall (d_init: Flags.t) (d: Flags.t) (tr_src tr_tgt: list (ProgramEvent.t * SeqEvent.input * Oracle.output)), Prop :=
  | match_trace_nil
      d:
      match_trace imatch d d [] []
  | match_trace_snoc
      d_init d1 tr_src tr_tgt d2
      e_src i_src o_src
      e_tgt i_tgt o_tgt
      (MATCH: match_trace imatch d_init d1 tr_src tr_tgt)
      (EVENT: ProgramEvent.le e_tgt e_src)
      (INPUT: imatch d1 d2 i_src i_tgt)
      (OUTPUT: o_src = o_tgt):
      match_trace imatch d_init d2 (tr_src ++ [(e_src, i_src, o_src)]) (tr_tgt ++ [(e_tgt, i_tgt, o_tgt)])
  .

  Lemma match_trace_cons
        imatch d1 d2 tr_src tr_tgt
        d0 e_src i_src o_src e_tgt i_tgt o_tgt
        (TRACE: match_trace imatch d1 d2 tr_src tr_tgt)
        (EVENT: ProgramEvent.le e_tgt e_src)
        (INPUT: imatch d0 d1 i_src i_tgt)
        (OUTPUT: o_src = o_tgt):
    match_trace imatch d0 d2 ((e_src, i_src, o_src) :: tr_src) ((e_tgt, i_tgt, o_tgt) :: tr_tgt).
  Proof.
    induction TRACE.
    { replace [(e_src, i_src, o_src)] with ([] ++ [(e_src, i_src, o_src)]) by ss.
      replace [(e_tgt, i_tgt, o_tgt)] with ([] ++ [(e_tgt, i_tgt, o_tgt)]) by ss.
      econs 2; eauto. econs.
    }
    exploit IHTRACE; eauto. i.
    replace ((e_src, i_src, o_src) :: tr_src ++ [(e_src0, i_src0, o_src0)]) with
      (((e_src, i_src, o_src) :: tr_src) ++ [(e_src0, i_src0, o_src0)]) by ss.
    replace ((e_tgt, i_tgt, o_tgt) :: tr_tgt ++ [(e_tgt0, i_tgt0, o_tgt0)]) with
      (((e_tgt, i_tgt, o_tgt) :: tr_tgt) ++ [(e_tgt0, i_tgt0, o_tgt0)]) by ss.
    econs 2; eauto.
  Qed.

  Lemma trace_le_match
        d_init tr_src v_src f_src tr_tgt v_tgt f_tgt
        (LE: SeqTrace.le d_init
                         (tr_tgt, SeqTrace.term v_tgt f_tgt)
                         (tr_src, SeqTrace.term v_src f_src)):
    exists d,
      (<<MATCH: match_trace SeqEvent.input_match d_init d tr_src tr_tgt>>) /\
      (<<FLAGS: Flags.le (Flags.join d f_tgt) (f_src)>>).
  Proof.
    remember (tr_src, SeqTrace.term v_src f_src) as r_src.
    remember (tr_tgt, SeqTrace.term v_tgt f_tgt) as r_tgt.
    revert tr_src v_src f_src tr_tgt v_tgt f_tgt Heqr_src Heqr_tgt.
    induction LE; i; subst; ss.
    { inv Heqr_src. inv Heqr_tgt. esplits; eauto. econs 1. }
    inv Heqr_src. inv Heqr_tgt.
    exploit IHLE; eauto. i. des. clear IHLE.
    esplits; eauto.
    eapply match_trace_cons; eauto.
  Qed.

  Lemma last_eq_inv
        A l1 l2 (a1 a2: A)
        (EQ: l1 ++ [a1] = l2 ++ [a2]):
    l1 = l2 /\ a1 = a2.
  Proof.
    split.
    - erewrite <- (removelast_last l1 a1).
      erewrite <- (removelast_last l2 a2).
      congr.
    - erewrite <- (last_last l1 a1 a1).
      erewrite <- (last_last l2 a2 a1).
      congr.
  Qed.

  Lemma min_match_trace_min
        d_init d_min d tr_src tr_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) d_init d_min tr_src tr_tgt)
        (TRACE: match_trace SeqEvent.input_match d_init d tr_src tr_tgt):
    Flags.le d_min d.
  Proof.
    revert d TRACE. induction MIN_TRACE; i.
    { inv TRACE; try refl. destruct tr_src; ss. }
    inv TRACE.
    { destruct tr_src; ss. }
    apply last_eq_inv in H2, H3. des. inv H1. inv H0.
    hexploit IHMIN_TRACE; eauto. i.
    eapply min_match_le_min; eauto using SeqEvent.input_match_mon.
  Qed.

  Lemma match_trace_le_terminal
        d tr_src v_src f_src tr_tgt v_tgt f_tgt
        (MIN_TRACE: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt)
        (LE: SeqTrace.le Flags.bot
                         (tr_tgt, SeqTrace.term v_tgt f_tgt)
                         (tr_src, SeqTrace.term v_src f_src)):
    Flags.le (Flags.join d f_tgt) f_src.
  Proof.
    exploit trace_le_match; eauto. i. des.
    hexploit min_match_trace_min; eauto. i.
    etrans; eauto.
    apply Flags.join_mon_l; auto.
  Qed.


  (** definitions and lemmas on state_steps *)

  Inductive state_steps (lang: language)
                        (step: forall (p: Perms.t) (e: MachineEvent.t) (st1 st2: SeqState.t lang), Prop):
    forall (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output))
      (st1 st2: SeqState.t lang) (p1 p2: Perms.t), Prop :=
  | state_steps_refl
      st p:
      state_steps step [] st st p p
  | state_steps_at_step
      e i o st1 st2 st3 p1 p3
      tr st4 p4
      (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
      (LSTEP: lang.(Language.step) e st2.(SeqState.state) st3.(SeqState.state))
      (ATOMIC: is_atomic_event e)
      (INPUT: SeqEvent.wf_input e i)
      (ESTEP: SeqEvent.step i o p1 st2.(SeqState.memory) p3 st3.(SeqState.memory))
      (STEPS: state_steps step tr st3 st4 p3 p4):
      state_steps step ((e, i, o)::tr) st1 st4 p1 p4
  .

  Lemma na_steps_behavior
        lang (step: Perms.t -> MachineEvent.t -> SeqState.t lang -> SeqState.t lang -> Prop)
        (st1 st2: SeqState.t lang) p orc tr
        (STEPS: rtc (step p MachineEvent.silent) st1 st2)
        (BEH: SeqBehavior.behavior step (SeqThread.mk st2 p orc) tr):
    SeqBehavior.behavior step (SeqThread.mk st1 p orc) tr.
  Proof.
    induction STEPS; ss.
    econs 4; try eapply IHSTEPS; eauto.
    econs. ss.
  Qed.

  Lemma steps_behavior_terminal
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (TERMINAL: lang.(Language.is_terminal) st2.(SeqState.state))
        (ORACLE: oracle_follows_trace orc0 tr orc):
    SeqBehavior.behavior step
                         (SeqThread.mk st0 p0 orc)
                         (tr, SeqTrace.term st2.(SeqState.memory).(SeqMemory.value_map) st2.(SeqState.memory).(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - eapply na_steps_behavior; eauto.
      destruct st2, memory. ss. econs 1; eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st0, st3. econs; eauto; try refl.
  Qed.

  Lemma steps_behavior_partial
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (ORACLE: oracle_follows_trace orc0 tr orc):
    SeqBehavior.behavior step
                         (SeqThread.mk st0 p0 orc)
                         (tr, SeqTrace.partial st2.(SeqState.memory).(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - eapply na_steps_behavior; eauto.
      destruct st2, memory. ss. econs 2; eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st0, st3. econs; eauto; try refl.
  Qed.

  Lemma steps_behavior_ub
        lang step orc0 tr (st0 st1 st2 st3: SeqState.t lang) p0 p1 orc
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (FAILURE: step p1 MachineEvent.failure st2 st3)
        (ORACLE: oracle_follows_trace orc0 tr orc):
    SeqBehavior.behavior step (SeqThread.mk st0 p0 orc) (tr, SeqTrace.ub).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - eapply na_steps_behavior; eauto.
      destruct st2. econs 3; eauto. econs. econs. eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st0, st4. econs; eauto; try refl.
  Qed.

  Lemma event_step_oracle_input
        e ie o p1 m1 p2 m2
        (WF: SeqEvent.wf_input e ie)
        (STEP: SeqEvent.step ie o p1 m1 p2 m2):
    SeqEvent.get_oracle_input ie = oracle_input_of_event e m1.
  Proof.
    destruct ie. inv STEP; ss.
    unfold SeqEvent.wf_input, SeqEvent.get_oracle_input, oracle_input_of_event in *.
    ss. splitsH.
    repeat f_equal.
    - inv UPD; ss; des_ifs; ss.
      + specialize (H t t0). des. exploit H5; eauto. i. des. ss.
      + specialize (H t t0). des. exploit H5; eauto. i. des. inv x.
        inv MEM. ss.
      + specialize (H loc v_new). des. exploit H; eauto. i. ss.
    - inv ACQ; ss; condtac; ss; intuition.
    - inv REL; ss; condtac; ss; intuition.
  Qed.

  Lemma steps_behavior_at_step
        lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc
        e i o st3 p3 m3
        (STEPS: state_steps step tr st0 st1 p0 p1)
        (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2)
        (ATSTEP: lang.(Language.step) e st2.(SeqState.state) st3)
        (ESTEP: SeqEvent.step i o p1 st2.(SeqState.memory) p3 m3)
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (OUTPUT: Oracle.wf_output e o)
        (ORACLE: oracle_follows_trace (add_oracle e (SeqEvent.get_oracle_input i) o orc0) tr orc):
      exists f, SeqBehavior.behavior step (SeqThread.mk st0 p0 orc)
                                (tr ++ [(e, i, o)], SeqTrace.partial f).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    { destruct st2. ss. destruct m3. ss.
      assert (exists orc', Oracle.step e (SeqEvent.get_oracle_input i) o orc orc').
      { inv ORACLE. punfold LE2. inv LE2.
        exploit LE.
        { econs. econs 1. }
        i. des. esplits; eauto.
      }
      des.
      esplits.
      eapply na_steps_behavior; eauto. econs 5.
      - econs; try refl; eauto.
      - econs 2.
    }
    clear INPUT OUTPUT.
    inv ORACLE. exploit COMPLETE; try refl.
    { eapply wf_input_oracle_wf_input; eauto. }
    i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des.
    exploit IHSTEPS; eauto. i. des. esplits; eauto. ss.
    eapply na_steps_behavior; eauto.
    econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
    destruct st0, st4. econs; eauto; try refl.
  Qed.

  Lemma event_step_exists_full e p1 m1:
    exists i o p2 m2,
      (<<WF_INPUT: SeqEvent.wf_input e i>>) /\
      (<<WF_OUTPUT: Oracle.wf_output e o>>) /\
      (<<ESTEP: SeqEvent.step i o p1 m1 p2 m2>>).
  Proof.
    specialize (oracle_input_of_event_wf e m1). i.
    exploit oracle_simple_output_wf; eauto. i.
    exploit event_step_exists; eauto. i. des. esplits; eauto.
  Qed.

  (* Lemma steps_behavior_at_step *)
  (*       lang step orc0 tr (st0 st1 st2: SeqState.t lang) p0 p1 orc *)
  (*       e i o st3 *)
  (*       (STEPS: state_steps step tr st0 st1 p0 p1) *)
  (*       (NASTEPS: rtc (step p1 MachineEvent.silent) st1 st2) *)
  (*       (ATSTEP: lang.(Language.step) e st2.(SeqState.state) st3) *)
  (*       (ATOMIC: is_atomic_event e) *)
  (*       (INPUT: i = oracle_input_of_event e st2.(SeqState.memory)) *)
  (*       (OUTPUT: o = oracle_simple_output i) *)
  (*       (ORACLE: oracle_follows_trace (add_oracle e i o orc0) tr orc): *)
  (*   exists ie f, *)
  (*     (<<INPUT: i = SeqEvent.get_oracle_input ie>>) /\ *)
  (*     (<<BEH: SeqBehavior.behavior step (SeqThread.mk st0 p0 orc) *)
  (*                                  (tr ++ [(e, ie, o)], SeqTrace.partial f)>>). *)
  (* Proof. *)
  (*   revert orc ORACLE. induction STEPS; i. *)
  (*   { destruct st2. ss. *)
  (*     assert (exists orc', Oracle.step e i o orc orc'). *)
  (*     { inv ORACLE. punfold LE2. inv LE2. *)
  (*       exploit LE. *)
  (*       { econs. econs 1. } *)
  (*       i. des. esplits; eauto. *)
  (*     } *)
  (*     i. des. *)
  (*     exploit oracle_input_of_event_wf. rewrite <- INPUT. i. *)
  (*     exploit oracle_simple_output_wf; eauto. i. *)
  (*     exploit event_step_exists; eauto. *)
  (*     instantiate (1:=memory). *)
  (*     instantiate (1:=p). *)
  (*     i. des. destruct m2. *)
  (*     exploit event_step_oracle_input; try exact WF; eauto. rewrite <- INPUT. i. subst. *)
  (*     esplits. *)
  (*     - eauto. *)
  (*     - eapply na_steps_behavior; eauto. econs 5. *)
  (*       + econs; try refl; eauto. *)
  (*         rewrite x2. eauto. *)
  (*       + econs 2. *)
  (*   } *)
  (*   clear INPUT OUTPUT. *)
  (*   inv ORACLE. exploit COMPLETE; try refl. *)
  (*   { eapply wf_input_oracle_wf_input; eauto. } *)
  (*   i. des. exploit SOUND; eauto. i. des. exploit x0; try refl. i. des. *)
  (*   exploit IHSTEPS; eauto. i. des. esplits; eauto. ss. *)
  (*   eapply na_steps_behavior; eauto. *)
  (*   econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto. *)
  (*   destruct st0, st4. econs; eauto; try refl. *)
  (* Qed. *)
  
  Lemma wf_input_wf_output
        e i o p1 m1 p2 m2
        (STEP: SeqEvent.step i o p1 m1 p2 m2)
        (WF: SeqEvent.wf_input e i):
    Oracle.wf_output e o.
  Proof.
    destruct i, o. inv STEP. ss.
    unfold SeqEvent.wf_input, Oracle.wf_output in *. ss. splitsH.
    apply wf_in_access_some in H.
    splitsH. splits.
    - inv UPD; ss.
    - inv ACQ; ss.
    - inv REL; ss.
  Qed.

  Lemma state_steps_wf_trace
        lang step tr (st1 st2: SeqState.t lang) p1 p2
        (STEPS: state_steps step tr st1 st2 p1 p2):
    wf_trace tr.
  Proof.
    induction STEPS; ss.
    econs; eauto. split; ss.
    eapply wf_input_wf_output; eauto.
  Qed.

  Variant simple_match_event: forall e_src e_tgt, Prop :=
  | simple_match_event_intro
      e_src i_src (o: Oracle.output)
      e_tgt i_tgt
      (EVENT: ProgramEvent.le e_tgt e_src)
      (INPUT: oracle_similar_input (SeqEvent.get_oracle_input i_src) (SeqEvent.get_oracle_input i_tgt)):
      simple_match_event (e_src, i_src, o) (e_tgt, i_tgt, o)
  .

  Program Instance simple_match_event_PreOrder: PreOrder simple_match_event.
  Next Obligation.
    ii. destruct x as [[]]. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.

  Lemma match_trace_simple_match
        d_init d tr_src tr_tgt
        (TRACE: match_trace (min_match SeqEvent.input_match) d_init d tr_src tr_tgt):
    Forall2 simple_match_event tr_src tr_tgt.
  Proof.
    induction TRACE; eauto. subst.
    apply Forall2_app; ss. econs; ss. econs; eauto.
    eapply input_match_similar. eapply INPUT.
  Qed.

  Lemma simple_match_follows1
        orc0 tr1 tr2 orc
        (MATCH: Forall2 simple_match_event tr1 tr2)
        (FOLLOWS: oracle_follows_trace orc0 tr1 orc):
    oracle_follows_trace orc0 tr2 orc.
  Proof.
    revert orc FOLLOWS. induction MATCH; i; eauto. inv H.
    inv FOLLOWS. econs; i.
    - exploit SOUND; try exact STEP. i. des. split.
      + destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
      + i. exploit x0; try by (etrans; eauto). i. des. splits; auto.
    - eapply COMPLETE; eauto; try by etrans; eauto.
      destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
  Qed.

  Lemma simple_match_follows2
        orc0 tr1 tr2 orc
        (MATCH: Forall2 simple_match_event tr1 tr2)
        (FOLLOWS: oracle_follows_trace orc0 tr2 orc):
    oracle_follows_trace orc0 tr1 orc.
  Proof.
    revert orc FOLLOWS. induction MATCH; i; eauto. inv H.
    inv FOLLOWS. econs; i.
    - exploit SOUND; try exact STEP. i. des. split.
      + destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
      + i. exploit x0.
        { etrans; eauto. symmetry. ss. }
        i. des. splits; auto.
    - eapply COMPLETE; eauto.
      + destruct e_src, e_tgt; ss; inv EVENT; des; subst; ss.
      + etrans; eauto. symmetry. ss.
  Qed.

  Lemma na_local_step_na_event
        p me pe m1 m2
        (STEP: SeqState.na_local_step p me pe m1 m2):
    ~ is_atomic_event pe.
  Proof.
    ii. inv STEP; ss.
    - destruct ord; ss.
    - destruct ord; ss.
    - unguard. des; destruct ordr, ordw; ss.
  Qed.

  Lemma similar_is_atomic
        e1 e2
        (E1: forall loc valr valw ordr ordw
               (E: e1 = ProgramEvent.update loc valr valw ordr ordw),
            Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
        (E2: forall loc valr valw ordr ordw
               (E: e2 = ProgramEvent.update loc valr valw ordr ordw),
            Ordering.le Ordering.plain ordr /\ Ordering.le Ordering.plain ordw)
        (SIMILAR: similar e1 e2):
    is_atomic_event e1 <-> is_atomic_event e2.
  Proof.
    destruct e1, e2; ss; des; subst; ss.
    - exploit E2; eauto. i. des.
      destruct ordr, ordw; ss.
    - exploit E1; eauto. i. des.
      destruct ord, ordw; ss.
  Qed.

  Lemma state_step_behavior
        p st1 st2 orc tr r
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: state_step p MachineEvent.silent st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, r))
        (TRACE: tr <> []):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, r).
  Proof.
    inv BEH; ss.
    - inv STEP0.
      exploit state_step_determ; [exact STEP|exact STEP1|]. i. des. subst. ss.
    - inv STEP0. exploit state_step_subset; eauto. i. inv x.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LANG|exact LANG0|]. i. des.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x2 in *.
      exploit na_local_step_na_event; eauto. ss.
  Qed.

  Lemma rtc_state_step_behavior
        p st1 st2 orc tr r
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: rtc (state_step p MachineEvent.silent) st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, r))
        (TRACE: tr <> []):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, r).
  Proof.
    revert DETERM BEH. induction STEP; i; ss.
    exploit state_step_behavior; eauto. i.
    apply IHSTEP; eauto.
    exploit state_step_subset; eauto. i. inv x0. s.
    punfold DETERM. inv DETERM. exploit PRESERVE; eauto. i.
    inv x; ss.
  Qed.

  Lemma state_step_behavior_ub
        p st1 st2 orc tr
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: state_step p MachineEvent.silent st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, SeqTrace.ub)):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, SeqTrace.ub).
  Proof.
    inv BEH; ss.
    - inv FAILURE. inv H.
      exploit state_step_determ; [exact STEP|exact STEP0|]. i. des. ss.
    - inv STEP0.
      exploit state_step_determ; [exact STEP|exact STEP1|]. i. des. subst. ss.
    - inv STEP0. exploit state_step_subset; eauto. i. inv x.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LANG|exact LANG0|]. i. des.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x2 in *.
      exploit na_local_step_na_event; eauto. ss.
  Qed.

  Lemma rtc_state_step_behavior_ub
        p st1 st2 orc tr
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: rtc (state_step p MachineEvent.silent) st1 st2)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p orc) (tr, SeqTrace.ub)):
    SeqBehavior.behavior state_step (SeqThread.mk st2 p orc) (tr, SeqTrace.ub).
  Proof.
    revert DETERM BEH. induction STEP; i; ss.
    exploit state_step_behavior_ub; eauto. i.
    apply IHSTEP; eauto.
    exploit state_step_subset; eauto. i. inv x0. s.
    punfold DETERM. inv DETERM. exploit PRESERVE; eauto. i.
    inv x; ss.
  Qed.

  Lemma rtc_na_step_deterministic
        lang p st1 st2
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEPS: rtc (@SeqState.na_step lang p MachineEvent.silent) st1 st2):
    deterministic _ st2.(SeqState.state).
  Proof.
    induction STEPS; ss.
    apply IHSTEPS. inv H. ss.
    eapply step_deterministic; eauto.
  Qed.

  Lemma rtc_state_step_deterministic
        p st1 st2
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: rtc (state_step p MachineEvent.silent) st1 st2):
    deterministic _ st2.(SeqState.state).
  Proof.
    induction STEP; ss.
    exploit state_step_subset; eauto. i. inv x0.
    apply IHSTEP. eapply step_deterministic; eauto.
  Qed.

  Lemma state_steps_deterministic
        tr st1 st2 p1 p2
        (DETERM: deterministic _ st1.(SeqState.state))
        (STEP: state_steps state_step tr st1 st2 p1 p2):
    deterministic _ st2.(SeqState.state).
  Proof.
    induction STEP; ss.
    apply IHSTEP. exploit rtc_state_step_deterministic; eauto. i.
    eapply step_deterministic; eauto.
  Qed.

  Lemma wf_input_in_access
        e i1 i2
        loc1 v_old1 f1 v_new1
        loc2 v_old2 f2 v_new2
        (WF1: SeqEvent.wf_input e i1)
        (WF2: SeqEvent.wf_input e i2)
        (IN1: i1.(SeqEvent.in_access) = Some (loc1, v_old1, f1, v_new1))
        (IN2: i2.(SeqEvent.in_access) = Some (loc2, v_old2, f2, v_new2)):
    loc1 = loc2 /\ v_new1 = v_new2.
  Proof.
    unfold SeqEvent.wf_input in *. des.
    destruct i1, i2. ss. subst.
    specialize (UPDATE0 loc1 v_new1). des. exploit UPDATE0; eauto. i.
    specialize (UPDATE loc2 v_new2). des. exploit UPDATE; eauto. i.
    rewrite x in *. inv x0. ss.
  Qed.
  
  Lemma wf_input_similar
        e i1 i2
        (WF1: SeqEvent.wf_input e i1)
        (WF2: SeqEvent.wf_input e i2):
    oracle_similar_input (SeqEvent.get_oracle_input i1) (SeqEvent.get_oracle_input i2).
  Proof.
    unfold SeqEvent.wf_input in *. des. destruct i1, i2; ss.
    unfold oracle_similar_input; ss.
    etrans; eauto. repeat rewrite andb_true_iff. splits.
    - destruct (is_accessing e) as [[loc v]|].
      + specialize (UPDATE0 loc v). specialize (UPDATE loc v). des.
        exploit UPDATE2; eauto. i. des. subst.
        exploit UPDATE1; eauto. i. des. subst.
        ss. apply Loc.eqb_refl.
      + destruct in_access as [[[[]]]|].
        { specialize (UPDATE0 t t2). des. exploit UPDATE0; eauto. ss. }
        destruct in_access0 as [[[[]]]|].
        { specialize (UPDATE t t2). des. exploit UPDATE; eauto. ss. }
        ss.
    - destruct in_acquire, in_acquire0; eauto.
    - destruct in_release, in_release0; eauto.
  Qed.

  Lemma behavior_steps_ub
        lang step (th1: SeqThread.t lang) tr
        (BEH: SeqBehavior.behavior step th1 (tr, SeqTrace.ub)):
    exists th2 st3,
      (<<STEPS: SeqThread.steps step tr th1 th2>>) /\
      (<<FAILURE: step th2.(SeqThread.perm) MachineEvent.failure th2.(SeqThread.state) st3>>).
  Proof.
    remember (tr, SeqTrace.ub) as r.
    revert tr Heqr.
    dependent induction BEH; i; inv Heqr; ss.
    - unfold SeqThread.failure in *. des. inv FAILURE0.
      esplits; [econs 1|]; eauto.
    - exploit IHBEH; eauto. i. des.
      esplits; [econs 2; eauto|]; eauto.
    - exploit IHBEH; eauto. i. des.
      esplits; [econs 3; eauto|]; eauto.
  Qed.

  Lemma behavior_steps_at_step
        lang step (th1: SeqThread.t lang) e i o tr r
        (BEH: SeqBehavior.behavior step th1 ((e, i, o) :: tr, r)):
    exists st2 st3,
      (<<STEPS: rtc (step th1.(SeqThread.perm) MachineEvent.silent) th1.(SeqThread.state) st2>>) /\
      (<<STEP: lang.(Language.step) e st2.(SeqState.state) st3>>).
  Proof.
    remember ((e, i, o) :: tr, r) as res.
    revert e i o tr r Heqres.
    dependent induction BEH; i; inv Heqres; ss.
    - exploit IHBEH; eauto. i. des.
      inv STEP. ss.
      esplits; [econs 2; eauto|]; eauto.
    - inv STEP. ss. esplits; eauto.
  Qed.

  Lemma at_step_behavior
        e i o p1 st1 p2 st2
        orc_init orc1 x l y ly r
        (DETERM: deterministic _ st1.(SeqState.state))
        (LSTEP: lang_src.(Language.step) e st1.(SeqState.state) st2.(SeqState.state))
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (ESTEP: SeqEvent.step i o p1 st1.(SeqState.memory) p2 st2.(SeqState.memory))
        (ORACLE: oracle_follows_trace orc_init (y :: ly) orc1)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc1) (x :: l, r))
        (EVENT1: simple_match_event (e, i, o) y)
        (* (EVENT2: simple_match_event x y) *):
    exists orc2,
      (<<EVENT: x = (e, i, o)>>) /\
      (<<ORACLE2: oracle_follows_trace orc_init ly orc2>>) /\
      (<<BEH2: SeqBehavior.behavior state_step (SeqThread.mk st2 p2 orc2) (l, r)>>).
  Proof.
    inv BEH.
    { inv STEP. exploit state_step_subset; eauto. i. inv x0.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
      exploit similar_is_atomic; eauto; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
      rewrite x3 in *. inv LOCAL; ss; try destruct ord; ss.
    }
    inv STEP. ss.
    punfold DETERM. inv DETERM.
    exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
    destruct y as [[ey iy] oy].
    replace o with oy in * by (inv EVENT1; ss).       
    replace e0 with e in *; cycle 1.
    { clear - ORACLE EVENT1 ORACLE0 x EVENT.
      inv EVENT1. clear INPUT.
      inv ORACLE. exploit SOUND; eauto. i. des.
      clear - x EVENT EVENT0 EVENT1.
      unfold eq_reading_value in *.
      destruct e1, e0, e, ey; ss; inv EVENT; inv EVENT0; des; subst; ss.
      exploit x2; eauto. i. subst. ss.
    }
    assert (ISIMILAR: oracle_similar_input (SeqEvent.get_oracle_input iy) i1).
    { clear - ORACLE EVENT1 ORACLE0 EVENT INPUT INPUT0 INPUT1. inv EVENT1.
      apply input_le_similar in INPUT0.
      exploit wf_input_similar; [exact INPUT|exact INPUT1|]. i.
      symmetry. etrans; eauto.
      symmetry. etrans; eauto.
      symmetry. ss.
    }
    replace o0 with oy in *; cycle 1.
    { clear - ORACLE EVENT1 ORACLE0 EVENT INPUT INPUT0 INPUT1 ISIMILAR. inv EVENT1.
      inv ORACLE. exploit SOUND; eauto. i. des.
      exploit x0; eauto. i. des. ss.
    }
    destruct st2. ss. exploit x0; eauto. i. subst.
    exploit SeqEvent.step_inj; [exact ESTEP|exact MEM|..]; eauto.
    { i. exploit wf_input_in_access; [exact INPUT|exact INPUT1|..]; eauto. }
    i. des. subst.
    esplits; eauto.
    inv ORACLE. exploit SOUND; try exact ORACLE0. i. des.
    apply x2. ss.
  Qed.

  Lemma steps_behavior_prefix_terminal
        tr_src tr_tgt
        st1 st2 p1 p2
        orc_init orc tr_src' v_src f_src
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STRACE: Forall2 simple_match_event tr_src' tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace orc_init tr_tgt orc)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc)
                                   (tr_src', SeqTrace.term v_src f_src)):
    (<<TRACES: tr_src = tr_src'>>) /\
    exists st3,
      (<<NASTEPS: rtc (state_step p2 MachineEvent.silent) st2 st3>>) /\
      (<<TERMINAL: lang_src.(Language.is_terminal) st3.(SeqState.state)>>) /\
      (<<VALUE_MAP: st3.(SeqState.memory).(SeqMemory.value_map) = v_src>>) /\
      (<<FLAGS: st3.(SeqState.memory).(SeqMemory.flags) = f_src>>).
  Proof.
    revert tr_src' tr_tgt orc v_src f_src TRACE STRACE ORACLE BEH.
    induction STEPS; i.
    { clear ORACLE DETERM. inv TRACE. inv STRACE. split; ss.
      remember (SeqThread.mk st p orc) as th1.
      remember ([], SeqTrace.term v_src f_src) as tr.
      revert st v_src f_src Heqth1 Heqtr.
      induction BEH; i; inv Heqth1; try inv Heqtr.
      - esplits; eauto; ss.
      - inv STEP. exploit IHBEH; eauto. i. des. esplits.
        + econs 2; eauto.
        + ss.
        + ss.
        + ss.
    }
    exploit rtc_state_step_behavior; eauto.
    { ii. subst. inv STRACE. inv TRACE. }
    i. inv TRACE. inv STRACE.
    exploit at_step_behavior; try exact LSTEP; try exact x0; eauto.
    { eapply rtc_state_step_deterministic; eauto. }
    i. des. subst.
    exploit IHSTEPS; try exact H5; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto.
      eapply rtc_state_step_deterministic; eauto.
    }
    i. des. subst. esplits; eauto.
  Qed.
  
  Lemma steps_behavior_prefix_ub
        tr_src tr_tgt
        st1 st2 p1 p2
        orc_init orc tr_src'
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace orc_init tr_tgt orc)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc) (tr_src', SeqTrace.ub)):
    exists orc2 th tr st3,
      (<<ORACLE2: oracle_follows_trace orc_init [] orc2>>) /\
      (<<TRACES: tr_src' = tr_src ++ tr>>) /\
      (<<STEPS: SeqThread.steps state_step tr (SeqThread.mk st2 p2 orc2) th>>) /\
      (<<FAILURE: state_step th.(SeqThread.perm) MachineEvent.failure th.(SeqThread.state) st3>>).
  Proof.
    revert tr_src' tr_tgt orc TRACE ORACLE BEH.
    induction STEPS; i.
    { exploit behavior_steps_ub; eauto. i. des.
      inv TRACE. ss. esplits; eauto.
    }    
    exploit rtc_state_step_behavior_ub; eauto. i. inv TRACE.
    exploit rtc_state_step_deterministic; eauto. i.
    destruct tr_src' as [|[[e' i'] o'] tr_src'].
    { inv x0; ss.
      - inv FAILURE. inv H.
        exploit state_step_subset; eauto. i. inv x.
        punfold x1. inv x1.
        exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
        exploit similar_is_atomic; try exact x; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
        rewrite x2 in *.
        exploit na_local_step_na_event; eauto. ss.
      - inv STEP. exploit state_step_subset; eauto. i. inv x.
        punfold x1. inv x1.
        exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
        exploit similar_is_atomic; try exact x; try by (i; subst; eapply NO_NA_UPDATE; eauto). i.
        rewrite x2 in *.
        exploit na_local_step_na_event; eauto. ss.
    }
    exploit at_step_behavior; try exact LSTEP; try exact x0; eauto. i. des. inv EVENT.
    exploit IHSTEPS; try exact H3; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto. }
    i. des. subst. esplits; eauto. ss.
  Qed.

  Lemma steps_behavior_prefix_partial
        tr_src tr_tgt
        st1 st2 p1 p2
        orc_init orc tr_src' e i o tr_src_ex f_src
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STRACE: Forall2 simple_match_event tr_src' tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace orc_init tr_tgt orc)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc)
                                   (tr_src' ++ [(e, i, o)] ++ tr_src_ex, SeqTrace.partial f_src)):
    exists orc',
      (<<LE1: oracle_le orc' orc_init>>) /\
        (<<LE2: oracle_le orc_init orc'>>) /\
        (<<TRACES: tr_src = tr_src'>>) /\
        (<<BEH_EX: SeqBehavior.behavior state_step (SeqThread.mk st2 p2 orc')
                                        ((e, i, o) :: tr_src_ex, SeqTrace.partial f_src)>>).
  Proof.
    revert tr_src' tr_tgt orc TRACE STRACE ORACLE BEH.
    induction STEPS; i.
    { inv TRACE. inv STRACE. inv ORACLE. esplits; eauto. }
    exploit rtc_state_step_behavior; eauto.
    { destruct tr_src'; ss. }
    i. inv TRACE. inv STRACE.
    exploit at_step_behavior; try exact LSTEP; try exact x0; eauto.
    { eapply rtc_state_step_deterministic; eauto. }
    i. des. subst.
    exploit IHSTEPS; try exact H5; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto.
      eapply rtc_state_step_deterministic; eauto.
    }
    i. des. subst. esplits; eauto.
  Qed.

  Lemma trace_le_cases
        d tr_tgt tr_src
        (LE: SeqTrace.le d tr_tgt tr_src):
    (<<TERM: exists tr_src' v_src f_src tr_tgt' v_tgt f_tgt,
        tr_src = (tr_src', SeqTrace.term v_src f_src) /\
        tr_tgt = (tr_tgt', SeqTrace.term v_tgt f_tgt) /\
        List.Forall2 simple_match_event tr_src' tr_tgt' /\
        ValueMap.le v_tgt v_src(*  /\ *)
        (* Flags.le (Flags.join d f_tgt) f_src*)>>) \/
    (<<PARTIAL: exists tr_src' tr_src_ex f_src tr_tgt' f_tgt,
        (* SeqThread.writing_trace d tr_src_ex w /\ *)
        tr_src = (tr_src' ++ tr_src_ex, SeqTrace.partial f_src) /\
        tr_tgt = (tr_tgt', SeqTrace.partial f_tgt) /\
        List.Forall2 simple_match_event tr_src' tr_tgt'(*  /\ *)
        (* Flags.le (Flags.join d f_tgt) (Flags.join w f_src) *)>>) \/
    (<<UB: exists tr_src', tr_src = (tr_src', SeqTrace.ub)>>).
  Proof.
    induction LE.
    { left. esplits; eauto. }
    { right. left. esplits; eauto. refl. }
    { right. right. esplits; eauto. }
    des.
    - inv TERM. inv TERM0.
      left. esplits; eauto.
      econs 2; eauto. econs; eauto.
      eapply input_match_similar; eauto.
    - inv PARTIAL. inv PARTIAL0.
      right. left. esplits.
      + replace ((e_src, i_src, o) :: tr_src' ++ tr_src_ex) with
            (((e_src, i_src, o) :: tr_src') ++ tr_src_ex) by ss. refl.
      + ss.
      + econs 2; eauto. econs; eauto.
        eapply input_match_similar; eauto.
    - inv UB. right. right.
      esplits; eauto.
  Qed.

  Lemma steps_implies
        lang step1 step2 tr (th1 th2: SeqThread.t lang)
        (IMPLIES: step1 <4= step2)
        (STEPS: SeqThread.steps step1 tr th1 th2):
    SeqThread.steps step2 tr th1 th2.
  Proof.
    induction STEPS; try by econs 1.
    { econs 2; eauto. inv STEP. econs. eauto. }
    { econs 3; eauto. }
  Qed.

  Lemma simple_match_last_inv
        tr_src tr_tgt e_tgt
        (MATCH: Forall2 simple_match_event tr_src (tr_tgt ++ [e_tgt])):
    exists tr_src' e_src,
      tr_src = tr_src' ++ [e_src] /\
        Forall2 simple_match_event tr_src' tr_tgt /\
        simple_match_event e_src e_tgt.
  Proof.
    revert tr_src MATCH. induction tr_tgt; ss; i.
    { inv MATCH. inv H3. esplits; eauto. ss. }
    inv MATCH. exploit IHtr_tgt; eauto. i. des. subst.
    esplits; eauto. ss.
  Qed.

  Lemma refinement_implies_simulation_aux
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        (REFINE: forall p m o (WF: Oracle.wf o),
            SeqTrace.incl
              (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
              (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)))
        (DETERM: deterministic _ st_src)
        p m p1 d
        tr_src st1_src
        tr_tgt st0_tgt st1_tgt
        (STEPS_SRC: state_steps state_step tr_src (SeqState.mk _ st_src m) st1_src p p1)
        (STEPS_TGT: state_steps (@SeqState.na_step lang_tgt) tr_tgt (SeqState.mk _ st_tgt m) st0_tgt p p1)
        (NASTEPS_TGT: rtc (SeqState.na_step p1 MachineEvent.silent) st0_tgt st1_tgt)
        (TRACES: match_trace (min_match SeqEvent.input_match) Flags.bot d tr_src tr_tgt):
      sim_seq (fun _ _ => True) p1 d st1_src st1_tgt.
  Proof.
    specialize (REFINE p m).
    revert p1 d tr_src st1_src tr_tgt st0_tgt st1_tgt STEPS_SRC STEPS_TGT NASTEPS_TGT TRACES.
    pcofix CIH. i. pfold.
    destruct (classic (sim_seq_failure_case p1 d st1_src)).
    { econs 2; eauto. }
    assert (NONUB: exists orc,
               (<<WF: Oracle.wf orc>>) /\
               (forall th tr w
                  (STEPS: SeqThread.steps (@SeqState.na_step _) tr (SeqThread.mk st1_src p1 orc) th)
                  (TRACE: SeqThread.writing_trace d tr w)
                  (FAILURE: SeqThread.failure (@SeqState.na_step _) th),
                 False)).
    { clear - H. unfold sim_seq_failure_case in H.
      apply not_all_ex_not in H. des. rename n into orc. exists orc.
      destruct (classic (Oracle.wf orc)); cycle 1.
      { exfalso. apply H. i. ss. }
      split; ss. i. apply H. i. esplits; eauto.
    }
    des.

    econs.
    { (* terminal *)
      ii. exploit steps_behavior_terminal; try exact STEPS_TGT; eauto.
      { eapply (oracle_of_trace_follows tr_tgt orc). }
      intro BEH_TGT.
      exploit REFINE; try exact BEH_TGT.
      { apply oracle_of_trace_wf. eapply state_steps_wf_trace; eauto. ss. }
      i. des.
      exploit trace_le_cases; eauto. i. des; try congr.
      { (* src terminal *)
        inv TERM0.
        exploit steps_behavior_prefix_terminal; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst.
        esplits; try exact TERMINAL; eauto.
        - eapply rtc_implies; try eapply state_step_subset. ss.
        - eapply match_trace_le_terminal; eauto.
      }
      { (* src UB *)
        subst.
        exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst.
        exfalso.
        inv ORACLE2. destruct th. ss.
        exploit oracle_le_steps; try exact LE1; try exact STEPS. i. des.
        exploit steps_implies; try exact x2; try apply state_step_subset. i.
        eapply NONUB0; eauto; cycle 1.
        { unfold SeqThread.failure. esplits. econs. eauto. }
        { admit. }
      }
    }

    { (* na step *)
      ii. destruct e.
      { (* silent *)
        esplits; eauto; try by econs 2.
        right. eapply CIH; eauto. etrans; eauto.
      }
      { (* syscall *)
        inv STEP_TGT. inv LOCAL; ss. destruct (p1 loc); ss.
      }
      { (* failure *)
        exploit steps_behavior_ub; eauto.
        { eapply (oracle_of_trace_follows tr_tgt orc). }
        intro BEH_TGT.
        exploit REFINE; try exact BEH_TGT.
        { apply oracle_of_trace_wf; ss. eapply state_steps_wf_trace; eauto. }
        i. des.
        exploit trace_le_cases; eauto. i. des; try congr. subst.
        exploit steps_behavior_prefix_ub; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. subst.
        exfalso.
        inv ORACLE2. destruct th. ss.
        exploit oracle_le_steps; try exact LE1; try exact STEPS. i. des.
        exploit steps_implies; try exact x2; try apply state_step_subset. i.
        eapply NONUB0; eauto; cycle 1.
        { unfold SeqThread.failure. esplits. econs. eauto. }
        { admit. }
      }
    }

    { (* at step *)
      ii.
      cut (exists (st_src1 : SeqState.t lang_src) (st_src2 : Language.state lang_src)
             (e_src : ProgramEvent.t),
              rtc (SeqState.na_step p1 MachineEvent.silent) st1_src st_src1 /\
              Language.step lang_src e_src (SeqState.state st_src1) st_src2 /\
              ProgramEvent.le e_tgt e_src).
      { i. des. esplits; eauto. i.
        exploit steps_behavior_at_step; eauto.
        { instantiate (2:=orc). eapply oracle_of_trace_follows. }
        intro BEH_TGT. des.
        exploit REFINE; try exact BEH_TGT.
        { eapply oracle_of_trace_wf.
          - eapply state_steps_wf_trace; eauto.
          - eapply add_oracle_wf; eauto.
            eapply wf_input_oracle_wf_input. ss.
        }
        i. des.
        exploit trace_le_cases; eauto. i. des; try congr; subst.
        { (* src partial *)
          inv PARTIAL0.
          exploit simple_match_last_inv; try exact PARTIAL1. i. des. subst. clear PARTIAL1.
          (* exploit state_steps_deterministic; eauto; ss. i. *)
          (* exploit rtc_na_step_deterministic; eauto. i. *)
          (* exploit deterministic_steps;[|exact  *)
          destruct e_src0 as [[e_src0 i_src] o_src]. inv x3.
          rewrite <- app_assoc in x.
          exploit steps_behavior_prefix_partial; try exact STEPS_SRC; try exact x; eauto.
          { eapply match_trace_simple_match; eauto. }
          { apply oracle_of_trace_follows. }
          i. des. symmetry in TRACES0. subst.
          (** TODO *)
          exploit behavior_steps_at_step; eauto. s. i. des.
          esplits; try exact STEP; ss.
          eapply rtc_implies; try eapply STEPS. eauto.
        }
      }

      specialize (event_step_exists_full e_tgt p1 st1_tgt.(SeqState.memory)). i. des.
      exploit steps_behavior_at_step; eauto.
      { instantiate (2:=orc). eapply oracle_of_trace_follows. }
      intro BEH_TGT. des.
      exploit REFINE; try exact BEH_TGT.
      { eapply oracle_of_trace_wf.
        - eapply state_steps_wf_trace; eauto.
        - eapply add_oracle_wf; eauto.
          eapply wf_input_oracle_wf_input. ss.
      }
      i. des.
      exploit trace_le_cases; eauto. i. des; try congr; subst.
      { (* src partial *)
        inv PARTIAL0.
        exploit simple_match_last_inv; try exact PARTIAL1. i. des. subst. clear PARTIAL1.
        destruct e_src as [[e_src i_src] o_src]. inv x3.
        rewrite <- app_assoc in x.
        exploit steps_behavior_prefix_partial; try exact STEPS_SRC; try exact x; eauto.
        { eapply match_trace_simple_match; eauto. }
        { apply oracle_of_trace_follows. }
        i. des. symmetry in TRACES0. subst.
        exploit behavior_steps_at_step; eauto. s. i. des.
        esplits; try exact STEP; ss.
        eapply rtc_implies; try eapply STEPS. eauto.
      }
      { (* src ub *)
        admit.
      }
    }

    { (* partial *)
      admit.
    }
  Admitted.

  Theorem refinement_implies_simulation
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
          (DETERM: deterministic _ st_src)
          (TOP: forall p m o (WF: Oracle.wf o),
              SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_src m) p o)
              <1=
              SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o))
    :
      sim_seq_all _ _ (fun _ _ => True) st_src st_tgt.
  Proof.
    ii. eapply refinement_implies_simulation_aux; eauto; try by econs 1.
    ii. exploit REFINE; eauto. i. des. eauto.
  Qed.
End ADEQUACY.
