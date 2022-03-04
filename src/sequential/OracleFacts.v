Require Import Bool.
Require Import RelationClasses.
Require Import List.
Require Import Program.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.

Require Import Sequential.
Require Import SeqLib.

Set Implicit Arguments.


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


(** oracle_le *)

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

Lemma oracle_le_steps
      lang step tr (st1: SeqState.t lang) p1 orc1 orc1' st2 p2 orc2
      (ORACLE: oracle_le orc1 orc1')
      (STEPS: SeqThread.steps step tr
                              (SeqThread.mk st1 p1 orc1)
                              (SeqThread.mk st2 p2 orc2)):
  exists orc2',
    SeqThread.steps step tr
                    (SeqThread.mk st1 p1 orc1')
                    (SeqThread.mk st2 p2 orc2').
Proof.
  remember (SeqThread.mk st1 p1 orc1) as th1.
  remember (SeqThread.mk st2 p2 orc2) as th2.
  revert st1 p1 orc1 orc1' st2 p2 orc2 ORACLE Heqth1 Heqth2.
  dependent induction STEPS; i; subst.
  { inv Heqth2. esplits. econs 1. }
  { inv STEP. exploit IHSTEPS; eauto. i. des.
    esplits. econs 2; eauto. econs. ss.
  }
  { inv STEP. punfold ORACLE. inv ORACLE.
    exploit LE; eauto. i. des. inv LE1; try done.
    exploit IHSTEPS; try eapply H; eauto. i. des.
    esplits. econs 3; try exact x. econs; eauto.
  }
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


(** dummy_oracle *)

Definition dummy_oracle_step
           (_t: Type) (pe: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc0 orc1: _t): Prop :=
  Oracle.wf_input pe i /\ o = oracle_simple_output i.

Definition dummy_oracle: Oracle.t := Oracle.mk (@dummy_oracle_step unit) tt.

Lemma dummy_oracle_wf: Oracle.wf dummy_oracle.
Proof.
  pcofix CIH. pfold. econs; ii.
  - inv STEP. existT_elim. subst. inv STEP0. splits; ss.
    + apply oracle_simple_output_wf; ss.
    + right. destruct x2. ss.
  - exists Const.undef. split; ii.
    + esplits; try eapply oracle_simple_output_wf; eauto.
      econs. econs; eauto.
    + esplits; try eapply oracle_simple_output_wf; eauto.
      econs. econs; eauto.
  - esplits; try eapply oracle_simple_output_wf; eauto.
    econs. econs; eauto.
  - esplits; try eapply oracle_simple_output_wf; eauto.
    econs. econs; eauto.
  - esplits; try eapply oracle_simple_output_wf; eauto.
    econs. econs; eauto.
    Unshelve.
    all: ss.
Qed.


(** oracle_of_trace *)

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
    (LE1: oracle_le orc orc0)
    (LE2: oracle_le orc0 orc):
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
  { inv FOLLOWS. econs.
    - clear LE2. revert orc0 _o _o0 LE1.
      pcofix CIH. i. pfold. econs. i.
      inv STEP. existT_elim. subst. inv STEP0. ss.
      punfold LE1. inv LE1. exploit LE.
      { econs. eauto. }
      i. des. inv LE1; try done.
      exploit CIH; eauto. i.
      esplits; eauto.
    - clear LE1. revert orc0 _o _o0 LE2.
      pcofix CIH. i. pfold. econs. i.
      punfold LE2. inv LE2. exploit LE; eauto. i. des.
      inv LE1; try done.
      inv STEP0. existT_elim. subst.
      exploit CIH; eauto. i.
      esplits.
      { econs. econs. eauto. }
      right. eauto.
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
  { econs; ss; apply oracle_le_refl. }
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
    specialize (LOAD loc ord). des. exists val. split; ii.
    - exploit LOAD; eauto. i. des.
      inv STEP. existT_elim. subst.
      esplits; eauto. econs. econs. eauto.
    - exploit LOAD0; eauto. i. des.
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
  { clear - SYSCALL.
    ii. exploit SYSCALL; eauto. i. des.
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
    - exists v. split; ii.
      + esplits.
        * econs. econs; eauto. destruct e; ss; inv READING; ss.
        * eapply oracle_output_of_event_wf; eauto.
          apply wf_input_oracle_wf_input. ss.
      + esplits.
        * econs. econs; eauto. destruct e; ss; inv READING; ss.
        * eapply oracle_output_of_event_wf; eauto.
          apply wf_input_oracle_wf_input. ss.
    - exists Const.undef. split; ii.
      + esplits.
        * econs. econs; eauto. destruct e; ss.
        * eapply oracle_output_of_event_wf; eauto.
          apply wf_input_oracle_wf_input. ss.
      + esplits.
        * econs. econs; eauto. destruct e; ss.
        * eapply oracle_output_of_event_wf; eauto.
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
  { ii. esplits.
    - econs. econs; eauto. destruct e; ss.
    - eapply oracle_output_of_event_wf; eauto.
      apply wf_input_oracle_wf_input. ss.
  }
Qed.


(** add_oracle *)

Inductive add_oracle_t (_t: Type): Type :=
| add_oracle_init (orc: _t)
| add_oracle_orc (orc: _t)
.

Variant add_oracle_step (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output)
        (_t: Type) (step: ProgramEvent.t -> Oracle.input -> Oracle.output -> _t -> _t -> Prop):
  forall (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output)
    (orc0 orc1: add_oracle_t _t), Prop :=
| add_oracle_step_init_event
    orc0:
    add_oracle_step e i o step e i o (add_oracle_init orc0) (add_oracle_orc orc0)
| add_oracle_step_init_orc
    e' i' o' orc0 orc1
    (STEP: step e' i' o' orc0 orc1):
    add_oracle_step e i o step e' i' o' (add_oracle_init orc0) (add_oracle_orc orc1)
| add_oracle_step_orc
    e' i' o' orc0 orc1
    (STEP: step e' i' o' orc0 orc1):
    add_oracle_step e i o step e' i' o' (add_oracle_orc orc0) (add_oracle_orc orc1)
.

Definition add_oracle
           (e: ProgramEvent.t) (i: Oracle.input) (o: Oracle.output) (orc: Oracle.t): Oracle.t :=
  Oracle.mk (add_oracle_step e i o orc.(Oracle._step)) (add_oracle_init orc.(Oracle._o)).

Lemma add_oracle_orc_le e i o _t step orc:
  oracle_le (Oracle.mk (@add_oracle_step e i o _t step) (add_oracle_orc orc)) (Oracle.mk step orc).
Proof.
  revert orc. pcofix CIH. i. pfold. econs. i.
  inv STEP. existT_elim. subst. inv STEP0. esplits.
  - econs. eauto.
  - right. ss.
Qed.

Lemma add_oracle_spec
      e i o orc_init
      e' i' o' orc0 orc1
      (ORACLE: orc0 = add_oracle e i o orc_init)
      (STEP: Oracle.step e' i' o' orc0 orc1):
  (e' = e /\ i' = i /\ o' = o /\ oracle_le orc1 orc_init) \/
  (exists orc_init1,
      (<<STEP: Oracle.step e' i' o' orc_init orc_init1>>) /\
      (<<LE: oracle_le orc1 orc_init1>>)).
Proof.
  subst. inv STEP. existT_elim. subst. inv STEP0.
  - left. splits; ss.
    destruct orc_init. ss. eapply add_oracle_orc_le; eauto.
  - right. destruct orc_init. ss. esplits.
    + econs. eauto.
    + eapply add_oracle_orc_le; eauto.
Qed.

Lemma add_oracle_init_progress
      e i o _t step orc
      e'
      (PROGRESS: Oracle.progress e' (Oracle.mk step orc)):
  Oracle.progress e' (Oracle.mk (@add_oracle_step e i o _t step) (add_oracle_init orc)).
Proof.
  unfold Oracle.progress in *. i.
  exploit PROGRESS; eauto. i. des.
  inv STEP. existT_elim. subst.
  esplits; eauto. econs. econs. eauto.
Qed.

Lemma add_oracle_orc_progress
      e i o _t step orc
      e'
      (PROGRESS: Oracle.progress e' (Oracle.mk step orc)):
  Oracle.progress e' (Oracle.mk (@add_oracle_step e i o _t step) (add_oracle_orc orc)).
Proof.
  unfold Oracle.progress in *. i.
  exploit PROGRESS; eauto. i. des.
  inv STEP. existT_elim. subst.
  esplits; eauto. econs. econs. eauto.
Qed.

Lemma add_oracle_orc_wf
      e i o _t step orc
      (WF: Oracle.wf (Oracle.mk step orc)):
  Oracle.wf (Oracle.mk (@add_oracle_step e i o _t step) (add_oracle_orc orc)).
Proof.
  revert orc WF. pcofix CIH. i.
  punfold WF. inv WF.
  pfold. econs; i; eauto using add_oracle_orc_progress.
  - inv STEP. existT_elim. subst. inv STEP0.
    exploit WF0; [econs; eauto|]. i. des.
    inv ORACLE; try done. splits; auto.
  - specialize (LOAD loc ord). des. exists val.
    split; i; apply add_oracle_orc_progress; ss.
Qed.

Lemma add_oracle_wf
      e i o orc_init
      (WF_INPUT: Oracle.wf_input e i)
      (WF_OUTPUT: Oracle.wf_output e o)
      (WF: Oracle.wf orc_init):
  Oracle.wf (add_oracle e i o orc_init).
Proof.
  destruct orc_init.
  dup WF. punfold WF. inv WF.
  pfold. econs; i; eauto using add_oracle_init_progress.
  { inv STEP. existT_elim. subst. inv STEP0.
    - splits; auto. left. apply add_oracle_orc_wf. ss.
    - exploit WF1; [econs; eauto|]. i. des.
      inv ORACLE; try done. splits; ss.
      left. eapply add_oracle_orc_wf. ss.
  }
  { specialize (LOAD loc ord). des. exists val.
    split; i; eapply add_oracle_init_progress; ss.
  }
Qed.

Lemma nil_steps_any_oracle
      lang step st1 p1 orc1 st2 p2 orc2 orc
      (STEPS: SeqThread.steps step [] (@SeqThread.mk lang st1 p1 orc1) (SeqThread.mk st2 p2 orc2)):
  orc1 = orc2 /\
  SeqThread.steps step [] (SeqThread.mk st1 p1 orc) (SeqThread.mk st2 p2 orc).
Proof.
  dependent induction STEPS; ss.
  - split; ss. econs.
  - destruct th1.
    exploit IHSTEPS; eauto. i. des.
    inv STEP. splits; ss.
    econs 2; eauto. econs. ss.
Qed.

Lemma steps_cons_inv
      lang step e i o tr st1 p1 orc1 th4
      (STEPS: SeqThread.steps step ((e, i, o) :: tr)
                              (@SeqThread.mk lang st1 p1 orc1) th4):
  exists st2 th3,
    (<<NASTEPS: SeqThread.steps step [] (SeqThread.mk st1 p1 orc1) (SeqThread.mk st2 p1 orc1)>>) /\
    (<<ATSTEP: SeqThread.at_step e i o (SeqThread.mk st2 p1 orc1) th3>>) /\
    (<<STEPS: SeqThread.steps step tr th3 th4>>).
Proof.
  dependent induction STEPS; ss.
  - destruct th1. inv STEP.
    exploit IHSTEPS; eauto. i. des.
    esplits; eauto. econs 2; eauto. econs. ss.
  - esplits; eauto. econs 1.
Qed.

Lemma steps_app
      lang step tr1 tr2 (th1 th2 th3: SeqThread.t lang)
      (STEPS1: SeqThread.steps step tr1 th1 th2)
      (STEPS2: SeqThread.steps step tr2 th2 th3):
  SeqThread.steps step (tr1 ++ tr2) th1 th3.
Proof.
  induction STEPS1; ss.
  - econs 2; eauto.
  - econs 3; eauto.
Qed.

Lemma add_oracle_steps_inv
      lang step e i o orc tr st1 p1 orc1 st2 p2 orc2
      (ORACLE: oracle_le orc1 (add_oracle e i o orc))
      (STEPS: SeqThread.steps step tr
                              (@SeqThread.mk lang st1 p1 orc1)
                              (SeqThread.mk st2 p2 orc2)):
  (exists orc2',
      SeqThread.steps step tr
                      (SeqThread.mk st1 p1 orc)
                      (SeqThread.mk st2 p2 orc2')) \/
  (exists e' i' o' tr',
      (<<TRACE: tr = (e', i', o') :: tr'>>) /\
      (<<EVENT: ProgramEvent.le e e'>>) /\
      (<<INPUT: Oracle.input_le i (SeqEvent.get_oracle_input i')>>) /\
      (<<OUTPUT: o' = o>>)).
Proof.
  destruct tr.
  { left. exploit nil_steps_any_oracle; eauto. i. des. esplits; eauto. }
  destruct p as [[e' i'] o'].
  exploit steps_cons_inv; eauto. i. des. clear STEPS.
  inv ATSTEP.
  punfold ORACLE. inv ORACLE. exploit LE; eauto. i. des. inv LE1; ss.
  exploit add_oracle_spec; eauto. i. des; subst.
  { right. esplits; eauto. }
  left.
  exploit oracle_le_steps; try exact STEPS0.
  { eapply oracle_le_trans; eauto. }
  i. des. exists orc2'.
  replace ((e', i', o') :: tr) with ([] ++ (e', i', o') :: tr).
  eapply steps_app.
  { eapply nil_steps_any_oracle; eauto. }
  econs 3; eauto; ss.
  econs; eauto. ss.
Qed.

Definition oracle_input_of_event (e: ProgramEvent.t) (m: SeqMemory.t): Oracle.input :=
  Oracle.mk_input
    (match is_accessing e with
     | Some (loc, _) => Some (loc, m.(SeqMemory.value_map) loc, m.(SeqMemory.flags) loc)
     | None => None
     end)
    (if is_acquire e then Some () else None)
    (if is_release e then Some () else None)
.

Lemma oracle_input_of_event_wf e m:
  Oracle.wf_input e (oracle_input_of_event e m).
Proof.
  unfold Oracle.wf_input. splits; ss; try by des_ifs.
  ss. des_ifs; split; i; des; inv H; eauto.
Qed.
