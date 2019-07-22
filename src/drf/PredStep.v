Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.

Require Import Coq.Logic.Classical.

Set Implicit Arguments.

Section PredStep.

  Definition te_pred := ThreadEvent.t -> Prop.

  Inductive pred_step (P : te_pred) lang (e:ThreadEvent.t)
             (e1 e2:Thread.t lang) : Prop :=
  | pred_step_intro (STEP : Thread.step_allpf e e1 e2) (SAT : P e)
  .

  Lemma pred_step_program_step P lang e :
        @pred_step P lang e <2= @Thread.step_allpf lang e. 
  Proof.
    intros t1 t2 []. eauto.
  Qed.

  Lemma program_step_true_step lang e :
        @Thread.step_allpf lang e <2= @pred_step (fun _ => True) lang e.
  Proof.
    econs; eauto.
  Qed.

  Lemma pred_step_mon P Q lang e (LE : P <1= Q) :
    @pred_step P lang e <2= @pred_step Q lang e.
  Proof.
    intros t1 t2 []. econs; eauto.
  Qed.

  Lemma hold_or_not (P Q : te_pred) lang e1 e2
        (STEP : rtc (tau (@pred_step P lang)) e1 e2) :
    (<<HOLD : rtc (tau (@pred_step (P /1\ Q) lang)) e1 e2>>) \/
    (<<NOT : exists e e2' e3, (<<STEPS : rtc (tau (@pred_step (P /1\ Q) lang)) e1 e2'>>) /\
                              (<<STEP : Thread.step_allpf e e2' e3>>) /\
                              (<<BREAKP : P e>>) /\ (<<BREAKQ : ~ Q e>>)>>).
  Proof.
    induction STEP as [th | th1 th2 th3 HD TL IH].
    - auto.
    - inv HD. inv TSTEP. destruct (classic (Q e)) as [QT | QF]. des.
      + left. repeat (econs; eauto).
      + right. do 4 (eauto; econs).
        * apply Operators_Properties.clos_rt_rt1n.
          eapply Relation_Operators.rt_trans. repeat (econs; eauto).
          eapply Operators_Properties.clos_rt1n_rt. eauto.
        * eauto. 
      + right. repeat (econs; eauto).
  Qed.

  Definition no_promise (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise _ _ _ _ _ => False
    | _ => True
    end.

  Definition no_read_msgs (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.read loc to _ _ _ => ~ (MSGS loc to)
    | ThreadEvent.update loc from _ _ _ _ _ _ _ => ~ (MSGS loc from)
    | _ => True
    end.

  Definition write_not_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | _ => True
    end.

  Definition write_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), (MSGS loc t)
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), (MSGS loc t)
    | _ => True
    end.

End PredStep.