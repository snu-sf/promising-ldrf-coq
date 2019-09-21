Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
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

  Lemma pred_step_program_step P:
        @pred_step P <4= @Thread.step_allpf.
  Proof.
    i. inv PR. eauto.
  Qed.

  Lemma program_step_true_step:
        @Thread.step_allpf <4= @pred_step (fun _ => True).
  Proof.
    econs; eauto.
  Qed.

  Lemma pred_step_mon P Q (LE : P <1= Q) :
    @pred_step P <4= @pred_step Q.
  Proof.
    i. inv PR. econs; eauto.
  Qed.

  Lemma pred_step_rtc_mon P Q lang (LE : P <1= Q) :
    rtc (tau (@pred_step P lang)) <2= rtc (tau (@pred_step Q lang)).
  Proof.
    i. induction PR; eauto.
    eapply Relation_Operators.rt1n_trans; eauto.
    inv H. econs; eauto. eapply pred_step_mon; eauto.
  Qed.

  Lemma thread_steps_pred_steps P lang:
    rtc (tau (@pred_step P lang)) <2= rtc (@Thread.tau_step lang).
  Proof.
    i. induction PR; eauto.
    eapply Relation_Operators.rt1n_trans; eauto.
    inv H. inv TSTEP. econs; eauto.
  Qed.

  Lemma pred_steps_thread_steps lang:
    rtc (@Thread.tau_step lang) <2= rtc (tau (@pred_step (fun _ => True) lang)).
  Proof.
    i. induction PR; eauto.
    eapply Relation_Operators.rt1n_trans; eauto.
    inv H. econs; eauto. eapply program_step_true_step; eauto.
  Qed.

  Lemma hold_or_not (P Q : te_pred) lang e1 e2
        (STEP : rtc (tau (@pred_step P lang)) e1 e2) :
    (<<HOLD : rtc (tau (@pred_step (P /1\ Q) lang)) e1 e2>>) \/
    (<<NOT : exists e e2' e3, (<<STEPS0 : rtc (tau (@pred_step (P /1\ Q) lang)) e1 e2'>>) /\
                              (<<STEP : Thread.step_allpf e e2' e3>>) /\
                              (<<BREAKP : P e>>) /\ (<<BREAKQ : ~ Q e>>) /\
                              (<<STEPS1 : rtc (tau (@pred_step P lang)) e3 e2>>)>>).
  Proof.
    induction STEP as [th | th1 th2 th3 HD TL IH]; auto.
    inv HD. inv TSTEP. destruct (classic (Q e)) as [QT | QF]. des.
    - left. repeat (econs; eauto).
    - right. do 4 (eauto; econs).
      * apply Operators_Properties.clos_rt_rt1n.
        eapply Relation_Operators.rt_trans. repeat (econs; eauto).
        eapply Operators_Properties.clos_rt1n_rt. eauto.
      * eauto.
    - right. repeat (econs; eauto).
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

  Definition no_update_on (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      ~ MSGS loc from
    | _ => True
    end.

  Definition no_sc (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.fence _ ordw => ~ Ordering.le Ordering.seqcst ordw
    | ThreadEvent.syscall _ => False
    | _ => True
    end
  .

  Definition write_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.write loc from to _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), (MSGS loc t)
    | ThreadEvent.update loc from to _ _ _ _ _ _ =>
      forall t (IN: Interval.mem (from, to) t), (MSGS loc t)
    | _ => True
    end.

  Lemma write_not_in_mon L0 L1
        e
        (NOTIN: write_not_in L1 e)
        (LE: L0 <2= L1)
    :
      write_not_in L0 e.
  Proof.
    i. unfold write_not_in in *. des_ifs.
    - ii. eapply NOTIN; eauto.
    - ii. eapply NOTIN; eauto.
  Qed.

  Lemma no_read_msgs_mon L0 L1
        e
        (NOTIN: no_read_msgs L1 e)
        (LE: L0 <2= L1)
    :
      no_read_msgs L0 e.
  Proof.
    i. unfold no_read_msgs in *. des_ifs.
    - ii. eapply NOTIN; eauto.
    - ii. eapply NOTIN; eauto.
  Qed.

  Lemma no_update_on_mon L0 L1
        e
        (NOTIN: no_update_on L1 e)
        (LE: L0 <2= L1)
    :
      no_update_on L0 e.
  Proof.
    i. unfold no_update_on in *. des_ifs.
    ii. eapply NOTIN; eauto.
  Qed.

  Lemma no_promise_program_step lang :
    (@pred_step no_promise lang) <3= (@Thread.program_step lang).
  Proof.
    i. inv PR. inv STEP. inv STEP0; clarify.
    inv STEP. ss.
  Qed.

  Lemma no_promise_program_step_rtc lang :
    rtc (tau (@pred_step no_promise lang)) <2= rtc (tau (@Thread.program_step _)).
  Proof.
    i. induction PR.
    - refl.
    - econs; eauto. inv H. econs; eauto.
      eapply no_promise_program_step; eauto.
  Qed.

  Definition promise_free (e: ThreadEvent.t): Prop :=
    match e with
    | ThreadEvent.promise loc from to msg kind =>
      (Memory.op_kind_is_lower_full kind && Message.is_released_none msg
       || Memory.op_kind_is_cancel kind)%bool
    | _ => True
    end.

  Lemma promise_free_step_pf_step lang:
    @pred_step promise_free lang <3= @Thread.step lang true.
  Proof.
    i. inv PR. inv STEP. inv STEP0; ss.
    - unfold promise_free in *.
      econs 1. replace pf with true in *; ss.
      inv STEP; ss.
    - econs 2; eauto.
  Qed.

  Lemma promise_free_step_pf_step_rtc lang :
    rtc (tau (@pred_step promise_free lang)) <2= rtc (tau (@Thread.step _ true)).
  Proof.
    i. induction PR.
    - refl.
    - econs; eauto. inv H. econs; eauto.
      eapply promise_free_step_pf_step; eauto.
  Qed.

End PredStep.