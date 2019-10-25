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
    | ThreadEvent.promise loc from to _ _ =>
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

  Lemma pf_step_promise_free_step lang:
    @Thread.step lang true <3= @pred_step promise_free lang.
  Proof.
    i. inv PR.
    - econs; eauto.
      + econs; eauto. econs 1; eauto.
      + inv STEP. ss.
    - econs; eauto.
      + econs; eauto. econs 2; eauto.
      + inv STEP. inv LOCAL; ss.
  Qed.

  Lemma pf_step_promise_free_step_rtc lang :
    rtc (tau (@Thread.step _ true)) <2= rtc (tau (@pred_step promise_free lang)).
  Proof.
    i. induction PR.
    - refl.
    - econs; eauto. inv H. econs; eauto.
      eapply pf_step_promise_free_step; eauto.
  Qed.

  Definition no_acq_read_msgs (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.read loc to _ _ ord =>
      forall (SAT: MSGS loc to), ~ Ordering.le Ordering.acqrel ord
    | ThreadEvent.update loc from _ _ _ _ _ ordr _ =>
      forall (SAT: MSGS loc from), ~ Ordering.le Ordering.acqrel ordr
    | _ => True
    end
  .

  Definition is_cancel (e: ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise _ _ _ _ Memory.op_kind_cancel => True
    | _ => False
    end.

  Definition te_rel := ThreadEvent.t -> ThreadEvent.t -> Prop.

  Lemma pred_step_shift (P_src P_tgt: te_pred) (R: te_rel)
        (SHIFT: forall e_src e_tgt (SAT: P_tgt e_tgt) (REL: R e_src e_tgt), P_src e_src)
        e_src e_tgt lang (th0 th1: Thread.t lang)
        (SAT: P_tgt e_tgt)
        (REL: R e_src e_tgt)
        (STEP: Thread.step_allpf e_src th0 th1)
    :
      pred_step P_src e_src th0 th1.
  Proof.
    econs; eauto.
  Qed.

  Definition same_machine_event e_src e_tgt :=
    ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt.

End PredStep.