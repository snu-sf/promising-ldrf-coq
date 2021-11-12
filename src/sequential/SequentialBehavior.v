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

Set Implicit Arguments.
Set Nested Proofs Allowed.

Ltac existT_elim1 :=
  match goal with
  | H: existT _ ?T1 ?v1 = existT _ ?T2 ?v2 |- _ =>
    match T1 with
    | T2 => apply EqdepTheory.inj_pair2 in H
    | _ => assert (T1 = T2) by (apply EqdepFacts.eq_sigT_fst in H; ss);
          subst T2
    end
  end.

Ltac existT_elim := repeat existT_elim1.


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
      st m p o tr
      (FAILURE: SeqThread.failure state_step (SeqThread.mk (SeqState.mk _ st m) p o))
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) (tr, SeqTrace.ub)
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

Lemma step_deterministic
      lang e st0 st1
      (DETERM: deterministic lang st0)
      (STEP: lang.(Language.step) e st0 st1):
  deterministic lang st1.
Proof.
  punfold DETERM. inv DETERM.
  exploit PRESERVE; eauto. i. inv x; done.
Qed.


(* TODO: move to simple.v *)

Lemma wf_input_oracle_wf_input
      e i
      (WF: SeqEvent.wf_input e i):
  Oracle.wf_input e (SeqEvent.get_oracle_input i).
Proof.
  destruct i. inv WF. ss. des. econs; ss. splits; split; i.
  - apply ACQUIRE. destruct in_acquire; ss.
  - destruct in_acquire; auto.
  - apply RELEASE. destruct in_release; ss.
  - destruct in_release; auto.
Qed.


(* facts on oracle *)

Definition oracle_simple_output (i: Oracle.input): Oracle.output :=
  let 'Oracle.mk_input acc acq rel := i in
  Oracle.mk_output
    (if is_some acc then Some (Perm.low, Const.undef) else None)
    (if is_some acq then Some (fun _ => Perm.low, fun _ => Const.undef) else None)
    (if is_some rel then Some (fun _ => Perm.low) else None).

Lemma oracle_simple_output_wf
      pe i
      (WF: Oracle.wf_input pe i):
  Oracle.wf_output pe (oracle_simple_output i).
Proof.
  unfold Oracle.wf_input, Oracle.wf_output in *. des.
  destruct i. ss.
  splits; try by (destruct in_acquire, in_release; ss).
  destruct in_access; ss.
  - destruct p as [[loc v] f].
    specialize (UPDATE loc). des.
    exploit UPDATE; eauto. i. rewrite x. ss.
  - destruct (is_accessing pe); ss.
    specialize (UPDATE t). des.
    exploit UPDATE0; eauto. i. des. ss.
Qed.

Definition dummy_oracle_step
           (pe: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc0 orc1: unit): Prop :=
  Oracle.wf_input pe i /\ o = oracle_simple_output i.

Definition dummy_oracle: Oracle.t := Oracle.mk dummy_oracle_step tt.

Lemma dummy_oracle_wf: Oracle.wf dummy_oracle.
Proof.
  pcofix CIH. pfold. econs; ii.
  - inv STEP. existT_elim. subst. inv STEP0. splits; ss.
    + apply oracle_simple_output_wf; ss.
    + right. destruct x2. ss.
  - exists Const.undef. ii.
    esplits; try eapply oracle_simple_output_wf; eauto.
    econs. econs; eauto.
  - esplits; try eapply oracle_simple_output_wf; eauto.
    econs. econs; eauto.
  - esplits; try eapply oracle_simple_output_wf; eauto.
    econs. econs; eauto.
    Unshelve.
    all: ss.
Qed.

Definition oracle_similar_input_access (i1 i2: option (Loc.t * Const.t * Flag.t)): bool :=
  match i1, i2 with
  | Some (loc1, _, _), Some (loc2, _, _) => Loc.eqb loc1 loc2
  | None, None => true
  | _, _ => false
  end.

Definition oracle_similar_input (i1 i2: Oracle.input): bool :=
  andb (oracle_similar_input_access i1.(Oracle.in_access) i2.(Oracle.in_access))
       (andb (eqb (is_some i1.(Oracle.in_acquire)) (is_some i2.(Oracle.in_acquire)))
             (eqb (is_some i1.(Oracle.in_release)) (is_some i2.(Oracle.in_release)))).

Global Program Instance oracle_similar_input_Equivalence: Equivalence oracle_similar_input.
Next Obligation.
  ii. destruct x. destruct in_access.
  - destruct p as [[]]. unfold oracle_similar_input, oracle_similar_input_access. ss.
    rewrite Loc.eqb_refl. destruct in_acquire, in_release; ss.
  - destruct in_acquire, in_release; ss.
Qed.
Next Obligation.
  ii. destruct x, y. unfold oracle_similar_input in *. ss.
  inv H. etrans; eauto.
  repeat rewrite andb_true_iff in *. des. splits.
  - destruct in_access0, in_access; ss.
    + destruct p as [[]], p0 as [[]].
      rewrite Loc.eqb_eq in *. congr.
    + destruct p as [[]]. ss.
  - destruct in_acquire, in_acquire0; ss.
  - destruct in_release, in_release0; ss.
Qed.
Next Obligation.
  ii. destruct x, y, z. unfold oracle_similar_input in *. ss.
  inv H. inv H0. etrans; eauto.
  repeat rewrite andb_true_iff in *. des. splits.
  - destruct in_access, in_access0, in_access1; ss.
    + destruct p as [[]], p1 as [[]], p0 as [[]].
      rewrite Loc.eqb_eq in *. congr.
    + destruct p0 as [[]]. ss.
  - destruct in_acquire, in_acquire0; ss.
  - destruct in_release, in_release0; ss.
Qed.

Lemma input_match_similar
      d0 d1 i_src i_tgt
      (MATCH: SeqEvent.input_match d0 d1 i_src i_tgt):
  oracle_similar_input (SeqEvent.get_oracle_input i_src) (SeqEvent.get_oracle_input i_tgt).
Proof.
  inv MATCH. unfold oracle_similar_input in *.
  destruct i_src, i_tgt. ss.
  inv ACCESS; inv ACQUIRE; inv RELEASE; ss; rewrite Loc.eqb_refl; ss.
Qed.

Lemma input_le_similar
      i0 i1
      (LE: Oracle.input_le i0 i1):
  oracle_similar_input i0 i1.
Proof.
  destruct i0, i1.
  unfold Oracle.input_le, oracle_similar_input in *. ss. des.
  etrans; eauto.
  repeat rewrite andb_true_iff. splits.
  - destruct in_access, in_access0; ss.
    destruct p as [[]], p0 as [[]]; ss. des. subst. apply Loc.eqb_refl.
  - destruct in_acquire, in_acquire0; ss.
  - destruct in_release, in_release0; ss.
Qed.

Lemma oracle_similar_input_loc
      i1 i2
      loc1 v1 f1
      loc2 v2 f2
      (SIMILAR: oracle_similar_input i1 i2)
      (IN1: i1.(Oracle.in_access) = Some (loc1, v1, f1))
      (IN2: i2.(Oracle.in_access) = Some (loc2, v2, f2)):
  loc1 = loc2.
Proof.
  destruct i1, i2; ss. subst.
  unfold oracle_similar_input, oracle_similar_input_access in *. ss.
  inv SIMILAR. apply andb_prop in H0. des.
  rewrite Loc.eqb_eq in H0. ss.
Qed.

Definition oracle_output_of_event
           (i: Oracle.input) (o: Oracle.output) (i_src: Oracle.input): Oracle.output :=
  if oracle_similar_input i i_src
  then o
  else oracle_simple_output i_src.

Variant oracle_step_of_event (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t):
  forall (pe: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc0 orc1: option orc.(Oracle._t)), Prop :=
| oracle_step_of_event_None
    e' i' o'
    (* (EVENT: same_reading_value e e') *)
    (INPUT: Oracle.wf_input e' i')
    (OUT: o' = oracle_output_of_event i o i'):
    oracle_step_of_event i o orc e' i' o' None (Some orc.(Oracle._o))
| oracle_step_of_event_Some
    e' i' o' orc0 orc1
    (STEP: orc.(Oracle._step) e' i' o' orc0 orc1):
    oracle_step_of_event i o orc e' i' o' (Some orc0) (Some orc1)
.

Definition oracle_of_event
           (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t): Oracle.t :=
  Oracle.mk (oracle_step_of_event i o orc) None.

Fixpoint oracle_of_trace_aux
         (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output)) (orc: Oracle.t): Oracle.t :=
  match tr with
  | [] => orc
  | (e, i, o) :: tr =>
    oracle_of_event e (SeqEvent.get_oracle_input i) o (oracle_of_trace_aux tr orc)
  end.

Definition oracle_of_trace tr := oracle_of_trace_aux tr dummy_oracle.

Inductive oracle_follows_trace:
  forall (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output)) (orc: Oracle.t), Prop :=
| oracle_follows_trace_nil
    orc:
    oracle_follows_trace [] orc
| oracle_follows_trace_cons
    e i o tr orc1
    (SOUND: forall e' i' o' orc2
              (INPUT: oracle_similar_input (SeqEvent.get_oracle_input i) i')
              (STEP: Oracle.step e' i' o' orc1 orc2),
        (* (<<EVENT: same_reading_value e e'>>) /\ *)
        (<<OUTPUT: o' = o>>) /\
        (<<FOLLOWS: oracle_follows_trace tr orc2>>))
    (COMPLETE: forall e' i'
                 (* (EVENT: same_reading_value e e') *)
                 (INPUT: oracle_similar_input (SeqEvent.get_oracle_input i) i')
                 (WF_INPUT: Oracle.wf_input e' i'),
        exists orc2,
          (<<STEP: Oracle.step e' i' o orc1 orc2>>)):
    oracle_follows_trace ((e, i, o) :: tr) orc1
.

Lemma some_oracle_follows
      tr i o _t _step (orc1 orc2: _t) orc
      (FOLLOWS: oracle_follows_trace
                  tr (Oracle.mk (oracle_step_of_event i o (Oracle.mk _step orc1)) (Some orc))):
  oracle_follows_trace
    tr (Oracle.mk (oracle_step_of_event i o (Oracle.mk _step orc2)) (Some orc)).
Proof.
  revert orc1 orc2 orc FOLLOWS.
  induction tr; i; try by econs 1. ss.
  inv FOLLOWS. econs; i.
  - clear COMPLETE.
    inv STEP. existT_elim. subst. inv STEP0. ss.
    exploit SOUND; try exact INPUT.
    { econs. econs; eauto. }
    s. i. des. eauto.
  - clear IHtr SOUND.
    exploit COMPLETE; eauto. i. des.
    inv STEP. existT_elim. subst. inv STEP0. ss.
    esplits. econs. econs. s. eauto.
Qed.

Lemma option_oracle_follows
      tr orc i o
      (FOLLOWS: oracle_follows_trace tr orc):
  oracle_follows_trace
    tr (Oracle.mk (oracle_step_of_event i o orc) (Some orc.(Oracle._o))).
Proof.
  revert orc i o FOLLOWS.
  induction tr; i; try by econs 1.
  inv FOLLOWS. econs; i.
  - inv STEP. existT_elim. subst. inv STEP0.
    destruct orc.
    exploit SOUND; try exact INPUT.
    { econs; eauto. }
    s. i. des. subst. splits; ss.
    exploit IHtr; try exact FOLLOWS. s. i.
    eapply some_oracle_follows; eauto.
  - exploit COMPLETE; eauto. i. des. inv STEP. s.
    esplits. econs. econs. eauto.
Qed.

Lemma oracle_of_trace_follows tr:
  oracle_follows_trace tr (oracle_of_trace tr).
Proof.
  induction tr; try by econs 1.
  destruct a as [[e i] o]. econs; i.
  - inv STEP. existT_elim. subst. inv STEP0.
    unfold oracle_output_of_event. condtac; ss. splits; ss.
    eapply option_oracle_follows. auto.
  - esplits. unfold oracle_of_trace. ss. econs. econs; eauto.
    unfold oracle_output_of_event. condtac; ss.
Qed.

Definition wf_trace tr: Prop :=
  Forall (fun x => match x with
                | (e, i, o) => SeqEvent.wf_input e i /\ Oracle.wf_output e o
                end) tr.

Lemma oracle_similar_input_fields
      i1 i2
      (SIMILAR: oracle_similar_input i1 i2):
  (i1.(Oracle.in_access) <-> i2.(Oracle.in_access)) /\
  (i1.(Oracle.in_acquire) <-> i2.(Oracle.in_acquire)) /\
  (i1.(Oracle.in_release) <-> i2.(Oracle.in_release)).
Proof.
  destruct i1, i2. ss.
  unfold oracle_similar_input in *. inv SIMILAR.
  repeat rewrite andb_true_iff in *. des.
  apply eqb_prop in H1, H2. rewrite H1, H2. splits; ss.
  destruct in_access, in_access0; ss.
  destruct p as [[]]. ss.
Qed.

Lemma wf_in_access_some
      (i: option (Loc.t * Const.t * Flag.t)) e
      (WF: forall loc, (exists v_old f_old, i = Some (loc, v_old, f_old)) <->
                  is_accessing e = Some loc):
  i <-> is_accessing e.
Proof.
  destruct i; ss.
  - destruct p as [[]]. destruct (WF t).
    exploit H; eauto. i. rewrite x. ss.
  - destruct e; ss.
    + destruct (WF loc). exploit H0; eauto. i. des. ss.
    + destruct (WF loc). exploit H0; eauto. i. des. ss.
    + destruct (WF loc). exploit H0; eauto. i. des. ss.
Qed.

Lemma oracle_output_of_event_wf
      e i o e' i'
      (WF_INPUT: Oracle.wf_input e i)
      (WF_OUTPUT: Oracle.wf_output e o)
      (WF: Oracle.wf_input e' i'):
  Oracle.wf_output e' (oracle_output_of_event i o i').
Proof.
  unfold oracle_output_of_event. condtac; cycle 1.
  { apply oracle_simple_output_wf. ss. }
  unfold Oracle.wf_input, Oracle.wf_output in *.
  exploit oracle_similar_input_fields; eauto. i.
  repeat match goal with
         | [H: ?a /\ ?b |- _] => inv H
         end.
  unnw. splits; cycle 1.
  { rewrite H7. rewrite <- H10. rewrite H1. ss. }
  { rewrite H8. rewrite <- H11. rewrite H2. ss. }
  apply wf_in_access_some in H0, H6.
  rewrite H3. rewrite <- H6. rewrite H. ss.
Qed.

#[export] Hint Resolve Oracle.wf_mon: paco.

Lemma option_oracle_wf
      orc i o
      (WF: Oracle.wf orc):
  Oracle.wf (Oracle.mk (oracle_step_of_event i o orc) (Some orc.(Oracle._o))).
Proof.
  destruct orc. ss.
  generalize _o at 1. revert _o WF.
  pcofix CIH. i. punfold WF. inv WF.
  pfold. econs; i.
  { inv STEP. existT_elim. subst. inv STEP0. ss.
    exploit WF0; [econs; eauto|]. i. des. splits; ss.
    inv ORACLE; try done. right. eauto.
  }
  { clear - LOAD.
    specialize (LOAD loc ord). des. exists val.
    ii. exploit LOAD; eauto. i. des.
    inv STEP. existT_elim. subst.
    esplits; eauto. econs. econs. eauto.
  }
  { clear - STORE.
    ii. exploit STORE; eauto. i. des.
    inv STEP. existT_elim. subst.
    esplits; eauto. econs. econs. eauto.
  }
  { clear - FENCE.
    ii. exploit FENCE; eauto. i. des.
    inv STEP. existT_elim. subst.
    esplits; eauto. econs. econs. eauto.
  }
Qed.

Lemma oracle_of_trace_wf
      tr
      (WF: wf_trace tr):
  Oracle.wf (oracle_of_trace tr).
Proof.
  revert WF. induction tr; i.
  { unfold oracle_of_trace. ss.
    eapply paco1_mon; try eapply dummy_oracle_wf. ss.
  }
  destruct a as [[e i] o]. inv WF. des.
  exploit IHtr; eauto. i. clear IHtr.
  pfold. econs; i.
  { unfold oracle_of_trace in *. ss.
    inv STEP. existT_elim. subst. inv STEP0. splits; ss.
    { eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input; eauto.
    }
    left. apply option_oracle_wf. auto.
  }
  { exists Const.undef. ii. esplits.
    - unfold oracle_of_trace. ss. econs. econs; eauto.
    - eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
  }
  { ii. esplits.
    - unfold oracle_of_trace. ss. econs. econs; eauto.
    - eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
  }
  { ii. esplits.
    - unfold oracle_of_trace. ss. econs. econs; eauto.
    - eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
  }
Qed.


Section ADEQUACY.
  Variable lang_src lang_tgt: language.
  Variable state_step:
    Perms.t -> MachineEvent.t -> SeqState.t lang_src -> SeqState.t lang_src -> Prop.

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

  Inductive match_trace: forall (d: Flags.t) (tr_src tr_tgt: list (ProgramEvent.t * SeqEvent.input * Oracle.output)), Prop :=
  | match_trace_nil d:
      match_trace d [] []
  | match_trace_cons
      d1 tr_src tr_tgt d2
      e_src i_src o_src
      e_tgt i_tgt o_tgt
      (MATCH: match_trace d1 tr_src tr_tgt)
      (EVENT: ProgramEvent.le e_tgt e_src)
      (INPUT: SeqEvent.input_match d1 d2 i_src i_tgt)
      (OUTPUT: o_src = o_tgt):
      match_trace d2 (tr_src ++ [(e_src, i_src, o_src)]) (tr_tgt ++ [(e_tgt, i_tgt, o_tgt)])
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
        lang step tr (st1 st2: SeqState.t lang) p1 p2 orc
        (STEPS: state_steps step tr st1 st2 p1 p2)
        (TERMINAL: lang.(Language.is_terminal) st2.(SeqState.state))
        (ORACLE: oracle_follows_trace tr orc):
    SeqBehavior.behavior step
                         (SeqThread.mk st1 p1 orc)
                         (tr, SeqTrace.term st2.(SeqState.memory).(SeqMemory.value_map) st2.(SeqState.memory).(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - destruct st, memory. ss. econs 1; eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st2, st3. econs; eauto; try refl.
  Qed.

  Lemma steps_behavior_partial
        lang step tr (st1 st2: SeqState.t lang) p1 p2 orc
        (STEPS: state_steps step tr st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace tr orc):
    SeqBehavior.behavior step
                         (SeqThread.mk st1 p1 orc)
                         (tr, SeqTrace.partial st2.(SeqState.memory).(SeqMemory.flags)).
  Proof.
    revert orc ORACLE. induction STEPS; i.
    - destruct st, memory. ss. econs 2; eauto.
    - eapply na_steps_behavior; eauto.
      inv ORACLE. exploit COMPLETE; try refl.
      { eapply wf_input_oracle_wf_input; eauto. }
      i. des. exploit SOUND; eauto; try refl. i. des.
      econs 5; try eapply IHSTEPS; try eapply FOLLOWS; eauto.
      destruct st2, st3. econs; eauto; try refl.
  Qed.
  
  Lemma wf_input_wf_output
        e i o p1 m1 p2 m2
        (STEP: SeqEvent.step i o p1 m1 p2 m2)
        (WF: SeqEvent.wf_input e i):
    Oracle.wf_output e o.
  Proof.
    destruct i, o.
    unfold SeqEvent.wf_input, Oracle.wf_output in *. ss.
    repeat match goal with
           | [H: ?a /\ ?b |- _] => inv H
           end.
    inv STEP. ss. unnw. apply wf_in_access_some in H.
    splits.
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
        d tr_src tr_tgt
        (TRACE: match_trace d tr_src tr_tgt):
    Forall2 simple_match_event tr_src tr_tgt.
  Proof.
    induction TRACE; eauto. subst.
    apply Forall2_app; ss. econs; ss.
    econs; eauto. eapply input_match_similar; eauto. 
  Qed.

  Lemma simple_match_follows1
        tr1 tr2 orc
        (MATCH: Forall2 simple_match_event tr1 tr2)
        (FOLLOWS: oracle_follows_trace tr1 orc):
    oracle_follows_trace tr2 orc.
  Proof.
    revert orc FOLLOWS. induction MATCH; i; eauto. inv H.
    inv FOLLOWS. econs; i.
    - exploit SOUND; try exact STEP.
      { etrans; eauto. }
      i. des. splits; auto.
    - eapply COMPLETE; eauto. etrans; eauto.
  Qed.

  Lemma simple_match_follows2
        tr1 tr2 orc
        (MATCH: Forall2 simple_match_event tr1 tr2)
        (FOLLOWS: oracle_follows_trace tr2 orc):
    oracle_follows_trace tr1 orc.
  Proof.
    revert orc FOLLOWS. induction MATCH; i; eauto. inv H.
    inv FOLLOWS. econs; i.
    - exploit SOUND; eauto.
      { etrans; eauto. symmetry. ss. }
      i. des. splits; auto.
    - eapply COMPLETE; eauto. etrans; eauto. symmetry. ss.
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
    inv x; try done.
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

  Lemma at_step_behavior
        e i o p1 st1 p2 st2
        orc1 x y l r
        (DETERM: deterministic _ st1.(SeqState.state))
        (LSTEP: lang_src.(Language.step) e st1.(SeqState.state) st2.(SeqState.state))
        (ATOMIC: is_atomic_event e)
        (INPUT: SeqEvent.wf_input e i)
        (ESTEP: SeqEvent.step i o p1 st1.(SeqState.memory) p2 st2.(SeqState.memory))
        (ORACLE: oracle_follows_trace (y :: l) orc1)
        (BEH: SeqBehavior.behavior state_step (SeqThread.mk st1 p1 orc1) (x :: l, r))
        (EVENT1: simple_match_event (e, i, o) y)
        (EVENT2: simple_match_event x y):
    exists orc2,
      (<<EVENT: x = (e, i, o)>>) /\
      (<<ORACLE2: oracle_follows_trace l orc2>>) /\
      (<<BEH2: SeqBehavior.behavior state_step (SeqThread.mk st2 p2 orc2) (l, r)>>).
  Proof.
    inv BEH.
    { unfold SeqThread.failure in *. des. inv FAILURE0.
      exploit state_step_subset; eauto. i. inv x0.
      punfold DETERM. inv DETERM.
      exploit STEP_STEP; [exact LSTEP|exact LANG|]. i. des.
      destruct e; inv LOCAL; ss.
      - des. subst. exploit NO_NA_UPDATE; eauto. i. des.
        unguard. destruct ordr, ordw; des; ss.
      - des. subst. destruct ord0; ss.
      - des. subst. exploit NO_NA_UPDATE; eauto. i. des.
        unguard. destruct ordr0, ordw0; des; ss.
    }
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
    replace o0 with oy in * by (inv EVENT2; ss).
    exploit similar_le_eq; try exact x.
    { inv EVENT1. eauto. }
    { inv EVENT2. eauto. }
    i. subst. exploit x0; eauto.
    i. destruct st2. ss. subst.
    exploit SeqEvent.step_inj; [exact ESTEP|exact MEM|..]; eauto.
    { inv EVENT1. inv EVENT2. i.
      destruct i, i0. ss. subst.
      eapply oracle_similar_input_loc.
      - etrans; try exact INPUT1. symmetry. eapply INPUT2.
      - ss.
      - ss.
    }
    i. des. subst.
    esplits; eauto.
    inv ORACLE. exploit SOUND; try exact ORACLE0.
    { inv EVENT2. exploit input_le_similar; eauto. i.
      symmetry. etrans; eauto.
    }
    i. des. ss.
  Qed.

  Lemma steps_behavior_prefix_terminal
        tr_src tr_tgt
        st1 st2 p1 p2
        orc tr_src' v_src f_src
        (DETERM: deterministic _ st1.(SeqState.state))
        (TRACE: Forall2 simple_match_event tr_src tr_tgt)
        (STRACE: Forall2 simple_match_event tr_src' tr_tgt)
        (STEPS: state_steps state_step tr_src st1 st2 p1 p2)
        (ORACLE: oracle_follows_trace tr_tgt orc)
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
    { eapply simple_match_follows2; eauto.
      econs; eauto. refl.
    }
    i. des. subst.
    exploit IHSTEPS; try exact H5; try eapply BEH2; eauto.
    { eapply step_deterministic; try eapply LSTEP; eauto.
      eapply rtc_state_step_deterministic; eauto.
    }
    { eapply simple_match_follows1; eauto. }
    i. des. subst. esplits; eauto.
  Qed.

  (* Definition steps_failure lang step (p: Perms.t) (st: SeqState.t lang): Prop := *)
  (*   exists st1 st2, *)
  (*     (<<STEPS: rtc (step p MachineEvent.silent) st st1>>) /\ *)
  (*     (<<FAILURE: step p MachineEvent.failure st1 st2>>). *)

  (* Lemma behavior_steps_terminal *)
  (*       lang step (th1: SeqThread.t lang) tr v f *)
  (*       (BEH: SeqBehavior.behavior step th1 (tr, SeqTrace.term v f)): *)
  (*   exists tr' st2 p2, *)
  (*     (<<STEPS: state_steps step tr' th1.(SeqThread.state) st2 th1.(SeqThread.perm) p2>>) /\ *)
  (*     ((<<TRACE: tr' = tr>>) /\ *)
  (*      (<<TERMINAL: lang.(Language.is_terminal) st2.(SeqState.state)>>) /\ *)
  (*      (<<VALUE_MAP: st2.(SeqState.memory).(SeqMemory.value_map) = v>>) /\ *)
  (*      (<<FLAGS: st2.(SeqState.memory).(SeqMemory.flags) = f>>) \/ *)
  (*      (<<FAILURE: steps_failure step p2 st2>>)). *)
  (* Proof. *)
  (*   clear - BEH. *)
  (*   remember (tr, SeqTrace.term v f) as r. *)
  (*   revert tr v f Heqr. *)
  (*   dependent induction BEH; i; inv Heqr; ss. *)
  (*   - esplits; [|left]; splits. *)
  (*     + econs 1. *)
  (*     + ss. *)
  (*     + ss. *)
  (*     + ss. *)
  (*     + ss. *)
  (*   - unfold SeqThread.failure in *. des. inv FAILURE0. *)
  (*     esplits; [econs 1|]. *)
  (*     right. unfold steps_failure. esplits; eauto. *)
  (*   - exploit IHBEH; eauto. i. inv STEP. ss. des. *)
  (*     + esplits; [|left]; splits. *)
  (*       * econs 2; eauto. *)
  (*       * ss. *)
  (*       * ss. *)
  (*       * ss. *)
  (*       * ss. *)
  (*     + unfold steps_failure in *. des. esplits. *)
  (*       * econs 2; eauto. *)
  (*       * right. eauto. *)
  (*   - exploit IHBEH; eauto. i. inv STEP. ss. des; subst. *)
  (*     + esplits; [|left]; splits. *)
  (*       * econs 3; eauto; ss; eauto. *)
  (*       * ss. *)
  (*       * ss. *)
  (*       * ss. *)
  (*       * ss. *)
  (*     + unfold steps_failure in *. des. esplits. *)
  (*       * econs 3; eauto; ss; eauto. *)
  (*       * right. eauto. *)
  (* Qed. *)

  (* Lemma behavior_steps_partial *)
  (*       lang step (th1: SeqThread.t lang) tr f *)
  (*       (BEH: SeqBehavior.behavior step th1 (tr, SeqTrace.partial f)): *)
  (*   exists tr' st2 p2, *)
  (*     (<<STEPS: state_steps step tr' th1.(SeqThread.state) st2 th1.(SeqThread.perm) p2>>) /\ *)
  (*     ((<<TRACE: tr' = tr>>) /\ *)
  (*      (<<FLAGS: st2.(SeqState.memory).(SeqMemory.flags) = f>>) \/ *)
  (*      (<<FAILURE: steps_failure step p2 st2>>)). *)
  (* Proof. *)
  (*   clear - BEH. *)
  (*   remember (tr, SeqTrace.partial f) as r. *)
  (*   revert tr f Heqr. *)
  (*   dependent induction BEH; i; inv Heqr; ss. *)
  (*   - esplits; [|left]; splits. *)
  (*     + econs 1. *)
  (*     + ss. *)
  (*     + ss. *)
  (*   - unfold SeqThread.failure in *. des. inv FAILURE0. *)
  (*     esplits; [econs 1|]. *)
  (*     right. unfold steps_failure. esplits; eauto. *)
  (*   - exploit IHBEH; eauto. i. inv STEP. ss. des. *)
  (*     + esplits; [|left]; splits. *)
  (*       * econs 2; eauto. *)
  (*       * ss. *)
  (*       * ss. *)
  (*     + unfold steps_failure in *. des. esplits. *)
  (*       * econs 2; eauto. *)
  (*       * right. eauto. *)
  (*   - exploit IHBEH; eauto. i. inv STEP. ss. des; subst. *)
  (*     + esplits; [|left]; splits. *)
  (*       * econs 3; eauto; ss; eauto. *)
  (*       * ss. *)
  (*       * ss. *)
  (*     + unfold steps_failure in *. des. esplits. *)
  (*       * econs 3; eauto; ss; eauto. *)
  (*       * right. eauto. *)
  (* Qed. *)

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

  Lemma refinement_implies_simulation_aux
        (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
        (REFINE: forall p m o (WF: Oracle.wf o),
            SeqTrace.incl
              (SeqBehavior.behavior (@SeqState.na_step _) (SeqThread.mk (SeqState.mk _ st_tgt m) p o))
              (SeqBehavior.behavior state_step (SeqThread.mk (SeqState.mk _ st_src m) p o)))
        (DETERM: deterministic _ st_src)
        p m p1 d
        tr_src st1_src
        tr_tgt st1_tgt
        (STEPS_SRC: state_steps state_step tr_src (SeqState.mk _ st_src m) st1_src p p1)
        (STEPS_TGT: state_steps (@SeqState.na_step lang_tgt) tr_tgt (SeqState.mk _ st_tgt m) st1_tgt p p1)
        (TRACES: match_trace d tr_src tr_tgt):
      sim_seq (fun _ _ => True) p1 d st1_src st1_tgt.
  Proof.
    specialize (REFINE p m).
    revert p1 d tr_src st1_src tr_tgt st1_tgt STEPS_SRC STEPS_TGT TRACES.
    pcofix CIH. i. pfold.
    destruct (classic (sim_seq_failure_case p1 d st1_src)).
    { econs 2; eauto. }

    econs.
    { (* terminal *)
      ii. exploit steps_behavior_terminal; try exact STEPS_TGT; eauto.
      { eapply oracle_of_trace_follows. }
      intro BEH_TGT.
      exploit REFINE; try exact BEH_TGT.
      { apply oracle_of_trace_wf. eapply state_steps_wf_trace; eauto. }
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
        - Lemma match_trace_le_flags
                d tr_src v_src f_src tr_tgt v_tgt f_tgt
                (TRACE: match_trace d tr_src tr_tgt)
                (LE: SeqTrace.le Flags.bot
                                 (tr_tgt, SeqTrace.term v_tgt f_tgt)
                                 (tr_src, SeqTrace.term v_src f_src)):
            Flags.le (Flags.join d f_tgt) f_src.
          Proof.
            revert d TRACE. induction LE.
            { admit. }
            { admit. }
            { admit. }
            {
          Admitted.
          eapply match_trace_le_flags; eauto.
      }
      { (* src UB *)
        admit.
      }
    }

    { (* na step *)
      ii. destruct e.
      { esplits; eauto; try by econs 2.
        right. eapply CIH; eauto.
        econs 2; eauto.
      }
      { inv STEP_TGT. inv LOCAL; ss. destruct (p1 loc); ss. }
      admit.
    }

    { (* at step *)
      admit.
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
