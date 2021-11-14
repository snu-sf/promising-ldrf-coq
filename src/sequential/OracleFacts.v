Require Import Bool.
Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.

Require Import Simple.
Require Import SeqLib.

Set Implicit Arguments.
Set Nested Proofs Allowed.


#[export] Hint Resolve Oracle.wf_mon: paco.

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

Ltac splitsH := 
  repeat match goal with
         | [H: ?a /\ ?b |- _] => inv H
         end; unnw.


(* TODO: move to simple.v *)

Lemma wf_input_oracle_wf_input
      e i
      (WF: SeqEvent.wf_input e i):
  Oracle.wf_input e (SeqEvent.get_oracle_input i).
Proof.
  unfold SeqEvent.wf_input, Oracle.wf_input in *. splitsH.
  destruct i. ss. splits.
  - split; i; des.
    + destruct in_access; ss. destruct p as [[[]]]. inv H0.
      specialize (H loc t2). des. eauto.
    + specialize (H loc v_new). des.
      exploit H5; eauto. i. des. rewrite x. ss. eauto.
  - rewrite <- H1. destruct in_acquire; ss.
  - rewrite <- H2. destruct in_release; ss.
Qed.


(* facts on oracle *)

Variant _oracle_le (oracle_le: Oracle.t -> Oracle.t -> Prop): Oracle.t -> Oracle.t -> Prop :=
| oracle_le_intro
    lhs rhs
    (LE: forall e i o lhs1 (STEP: Oracle.step e i o lhs lhs1),
      exists rhs1, (<<STEP: Oracle.step e i o rhs rhs1>>) /\
              (<<LE1: oracle_le lhs1 rhs1>>)):
  _oracle_le oracle_le lhs rhs.

Lemma oracle_le_mon: monotone2 _oracle_le.
Proof.
  ii. inv IN. econs. i. exploit LE0; eauto. i. des. eauto.
Qed.
#[export] Hint Resolve oracle_le_mon: paco.

Definition oracle_le := paco2 _oracle_le bot2.
Arguments oracle_le: clear implicits.

Lemma oracle_le_refl orc: oracle_le orc orc.
Proof.
  revert orc. pcofix CIH. i.
  pfold. econs. i. esplits; eauto.
Qed.

Lemma oracle_le_trans
      orc1 orc2 orc3
      (LE1: oracle_le orc1 orc2)
      (LE2: oracle_le orc2 orc3):
  oracle_le orc1 orc3.
Proof.
  revert orc1 orc2 orc3 LE1 LE2. pcofix CIH. i.
  pfold. econs. i.
  punfold LE1. inv LE1. punfold LE2. inv LE2.
  exploit LE; eauto. i. des.
  exploit LE0; eauto. i. des.
  esplits; eauto.
  inv LE1; try done. inv LE2; try done.
  right. eapply CIH; eauto.
Qed.

Program Instance oracle_le_PreOrder: PreOrder oracle_le.
Next Obligation.
  ii. revert x. pcofix CIH. i.
  pfold. econs. i. esplits; eauto.
Qed.
Next Obligation.
  ii. revert x y z H H0. pcofix CIH. i.
  pfold. econs. i.
  punfold H0. inv H0. punfold H1. inv H1.
  exploit LE; eauto. i. des.
  exploit LE0; eauto. i. des.
  esplits; eauto.
  inv LE1; try done. inv LE2; try done.
  right. eapply CIH; eauto.
Qed.

Lemma wf_in_access_some
      (i: option (Loc.t * Const.t * Flag.t * Const.t)) e
      (WF: forall loc v_new,
          ((exists v_old f_old, i = Some (loc, v_old, f_old, v_new)) <->
             (is_accessing e = Some (loc, v_new)))):
  i <-> is_accessing e.
Proof.
  destruct i; ss.
  - destruct p as [[[]]]. destruct (WF t t2).
    exploit H; eauto. i. rewrite x. ss.
  - destruct e; ss.
    + destruct (WF loc val). exploit H0; eauto. i. des. ss.
    + destruct (WF loc val). exploit H0; eauto. i. des. ss.
    + destruct (WF loc valw). exploit H0; eauto. i. des. ss.
Qed.

Lemma oracle_wf_in_access_some
      (i: option (Loc.t * Const.t * Flag.t)) e
      (WF: forall loc, (exists v_old f_old, i = Some (loc, v_old, f_old)) <->
                    (exists v_new, is_accessing e = Some (loc, v_new))):
  i <-> is_accessing e.
Proof.
  destruct i; ss.
  - destruct p as [[]]. destruct (WF t).
    exploit H; eauto. i. des. rewrite x. ss.
  - destruct e; ss.
    + destruct (WF loc). exploit H0; eauto. i. des. ss.
    + destruct (WF loc). exploit H0; eauto. i. des. ss.
    + destruct (WF loc). exploit H0; eauto. i. des. ss.
Qed.

Definition oracle_simple_output (i: Oracle.input): Oracle.output :=
  let 'Oracle.mk_input acc acq rel := i in
  Oracle.mk_output
    (if is_some acc then Some Perm.low else None)
    (if is_some acq then Some (fun _ => Perm.low, fun _ => Const.undef) else None)
    (if is_some rel then Some (fun _ => Perm.low) else None).

Lemma oracle_simple_output_wf
      pe i
      (WF: Oracle.wf_input pe i):
  Oracle.wf_output pe (oracle_simple_output i).
Proof.
  unfold Oracle.wf_input, Oracle.wf_output in *. splitsH.
  apply oracle_wf_in_access_some in H.
  rewrite <- H, <- H1, <- H2.
  destruct i. ss. splits.
  - destruct in_access; ss.
  - destruct in_acquire; ss.
  - destruct in_release; ss.
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

Definition reading_value_of (e: ProgramEvent.t): option Const.t :=
  match e with
  | ProgramEvent.read _ v _
  | ProgramEvent.update _ v _ _ _ => Some v
  | _ => None
  end.

Definition eq_reading_value (e1 e2: ProgramEvent.t): Prop :=
  match reading_value_of e1, reading_value_of e2 with
  | Some v1, Some v2 => v1 = v2
  | _, _ => True
  end.

Program Instance eq_reading_value_Reflexive: Reflexive eq_reading_value.
Next Obligation.
  ii. destruct x; ss.
Qed.

Program Instance eq_reading_value_Symmetric: Symmetric eq_reading_value.
Next Obligation.
  ii. destruct x, y; ss; inv H; ss.
Qed.

Variant oracle_step_of_event (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t):
  forall (pe: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc0 orc1: option orc.(Oracle._t)), Prop :=
| oracle_step_of_event_None
    e' i' o'
    (EVENT: eq_reading_value e e')
    (INPUT: Oracle.wf_input e' i')
    (OUT: o' = oracle_output_of_event i o i'):
    oracle_step_of_event e i o orc e' i' o' None (Some orc.(Oracle._o))
| oracle_step_of_event_Some
    e' i' o' orc0 orc1
    (STEP: orc.(Oracle._step) e' i' o' orc0 orc1):
    oracle_step_of_event e i o orc e' i' o' (Some orc0) (Some orc1)
.

Definition oracle_of_event
           (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t): Oracle.t :=
  Oracle.mk (oracle_step_of_event e i o orc) None.

Fixpoint oracle_of_trace_aux
         (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output)) (orc: Oracle.t): Oracle.t :=
  match tr with
  | [] => orc
  | (e, i, o) :: tr =>
    oracle_of_event e (SeqEvent.get_oracle_input i) o (oracle_of_trace_aux tr orc)
  end.

Definition oracle_of_trace tr orc_init := oracle_of_trace_aux tr orc_init.

Inductive oracle_follows_trace (orc0: Oracle.t):
  forall (tr: list (ProgramEvent.t * SeqEvent.input * Oracle.output)) (orc: Oracle.t), Prop :=
| oracle_follows_trace_nil
    orc
    (LE: oracle_le orc orc0):
    oracle_follows_trace orc0 [] orc
| oracle_follows_trace_cons
    e i o tr orc1
    (SOUND: forall e' i' o' orc2
              (STEP: Oracle.step e' i' o' orc1 orc2),
        (<<EVENT: eq_reading_value e e'>>) /\
        (oracle_similar_input (SeqEvent.get_oracle_input i) i' ->
         (<<OUTPUT: o' = o>>) /\
         (<<FOLLOWS: oracle_follows_trace orc0 tr orc2>>)))
    (COMPLETE: forall e' i'
                 (EVENT: eq_reading_value e e')
                 (INPUT: oracle_similar_input (SeqEvent.get_oracle_input i) i')
                 (WF_INPUT: Oracle.wf_input e' i'),
        exists orc2,
          (<<STEP: Oracle.step e' i' o orc1 orc2>>)):
    oracle_follows_trace orc0 ((e, i, o) :: tr) orc1
.

Lemma option_oracle_follows
      orc0 tr orc e i o
      (FOLLOWS: oracle_follows_trace orc0 tr orc):
  oracle_follows_trace
    orc0 tr (Oracle.mk (oracle_step_of_event e i o orc) (Some orc.(Oracle._o))).
Proof.
  destruct orc. ss.
  generalize _o at 1.
  revert _o i o FOLLOWS.
  induction tr; i.
  { inv FOLLOWS. econs 1.
    revert orc0 _o _o0 LE. pcofix CIH. i. pfold. econs. i.
    inv STEP. existT_elim. subst. inv STEP0. ss.
    punfold LE. inv LE. exploit LE0.
    { econs. eauto. }
    i. des. inv LE1; try done.
    exploit CIH; eauto. i.
    esplits; eauto.
  }
  inv FOLLOWS. econs; i.
  - inv STEP. existT_elim. subst. inv STEP0.
    exploit SOUND.
    { econs; eauto. }
    i. des. split; ss. i.
    exploit x0; eauto. i. des. subst. splits; ss.
    eapply IHtr; eauto.
  - exploit COMPLETE; eauto. i. des. inv STEP. existT_elim. subst.
    esplits. econs. econs. eauto.
Qed.

Lemma oracle_of_trace_follows tr orc_init:
  oracle_follows_trace orc_init tr (oracle_of_trace tr orc_init).
Proof.
  induction tr.
  { econs. ss. apply oracle_le_refl. }
  destruct a as [[e i] o]. econs; i.
  - inv STEP. existT_elim. subst. inv STEP0.
    unfold oracle_output_of_event. condtac; ss. splits; ss. i.
    split; ss. eapply option_oracle_follows. auto.
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
  exploit oracle_similar_input_fields; eauto. i. splitsH.
  splits; cycle 1.
  { rewrite H7. rewrite <- H10. rewrite H1. ss. }
  { rewrite H8. rewrite <- H11. rewrite H2. ss. }
  apply oracle_wf_in_access_some in H0, H6.
  rewrite H3. rewrite <- H6. rewrite H. ss.
Qed.

Lemma option_oracle_wf
      orc e i o
      (WF: Oracle.wf orc):
  Oracle.wf (Oracle.mk (oracle_step_of_event e i o orc) (Some orc.(Oracle._o))).
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
      tr orc_init
      (TRACE: wf_trace tr)
      (INIT: Oracle.wf orc_init):
  Oracle.wf (oracle_of_trace tr orc_init).
Proof.
  revert TRACE. induction tr; i; ss.
  destruct a as [[e i] o]. inv TRACE. des.
  exploit IHtr; eauto. i. clear IHtr.
  pfold. econs; i.
  { unfold oracle_of_trace in *. ss.
    inv STEP. existT_elim. subst. inv STEP0. splits; ss.
    { eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input; eauto.
    }
    left. apply option_oracle_wf. auto.
  }
  { destruct (reading_value_of e) as [v|] eqn:READING.
    - exists v. ii. esplits.
      + econs. econs; eauto. destruct e; ss; inv READING; ss.
      + eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
    - exists Const.undef. ii. esplits.
      + econs. econs; eauto. destruct e; ss.
      + eapply oracle_output_of_event_wf; eauto.
        apply wf_input_oracle_wf_input. ss.
  }
  { ii. esplits.
    - econs. econs; eauto. destruct e; ss.
    - eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
  }
  { ii. esplits.
    - econs. econs; eauto. destruct e; ss.
    - eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
  }
Qed.
