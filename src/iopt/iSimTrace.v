From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimThread.
Require Import iCompatibility.

Require Import ITreeLang.

Set Implicit Arguments.


Definition lang_steps_failure [lang] (st1: Language.state lang): Prop :=
  exists st2 st3,
    <<STEPS: rtc ((Language.step lang) ProgramEvent.silent) st1 st2>> /\
    <<FAILURE: (Language.step lang) ProgramEvent.failure st2 st3>>.

Lemma rtc_lang_tau_step_rtc_thread_tau_step lang
      st1 st2 lc sc mem
      (STEP: rtc ((Language.step lang) ProgramEvent.silent) st1 st2):
  rtc (@Thread.tau_step lang) (Thread.mk lang st1 lc sc mem) (Thread.mk lang st2 lc sc mem).
Proof.
  induction STEP.
  - econs 1.
  - econs 2; eauto. econs.
    + econs. econs 2. econs; [|econs 1]; eauto.
    + ss.
Qed.


Definition SIM_TRACE :=
  forall R_src R_tgt (sim_val:SIM_VAL R_src R_tgt)
         (st1_src:(Language.state (lang R_src)))
         (st1_tgt:(Language.state (lang R_tgt))), Prop.

Definition _sim_trace
           (sim_trace:SIM_TRACE)
           R_src R_tgt
           (sim_val:SIM_VAL R_src R_tgt)
           (st1_src:(Language.state (lang R_src)))
           (st1_tgt:(Language.state (lang R_tgt))): Prop :=
  <<TERMINAL:
    forall (TERMINAL_TGT: (Language.is_terminal (lang R_tgt)) st1_tgt),
      <<FAILURE: lang_steps_failure st1_src>> \/
      exists st2_src,
        <<STEPS: rtc ((Language.step (lang R_src)) ProgramEvent.silent) st1_src st2_src>> /\
        <<TERMINAL_SRC: (Language.is_terminal (lang R_src)) st2_src>> /\
        <<TERMINAL: sim_terminal sim_val st2_src st1_tgt>> >> /\
  <<STEP:
    forall e_tgt st3_tgt
      (STEP_TGT: (Language.step (lang R_tgt)) e_tgt st1_tgt st3_tgt),
      <<FAILURE: lang_steps_failure st1_src>> \/
      exists e_src st2_src st3_src,
        <<EVT: ProgramEvent.ord e_src e_tgt>> /\
        <<STEPS: rtc ((Language.step (lang R_src)) ProgramEvent.silent) st1_src st2_src>> /\
        <<STEP_SRC: ILang.opt_step e_src st2_src st3_src>> /\
        <<SIM: sim_trace _ _ sim_val st3_src st3_tgt>> >>.

Lemma _sim_trace_mon: monotone5 _sim_trace.
Proof.
  ii. unfold _sim_trace in *. des; splits; ss.
  i. exploit STEP; eauto. i. des; eauto.
  right. esplits; eauto.
Qed.
Hint Resolve _sim_trace_mon: paco.

Definition sim_trace: SIM_TRACE := paco5 _sim_trace bot5.
(* Definition sim_trace: SIM_TRACE := paco5 _sim_trace sim_itree. *)

Lemma sim_trace_sim_thread R_src R_tgt
      sim_val
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_trace sim_val st1_src st1_tgt)
      (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt):
  @sim_thread
    (lang R_src) (lang R_tgt)
    (sim_terminal sim_val)
    st1_src lc1_src sc1_src mem1_src
    st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  revert_until sim_val. pcofix CIH. i.
  generalize SIM. i. punfold SIM0. unfold _sim_trace in SIM0. des.
  pfold. ii. splits.
  - i. exploit TERMINAL; eauto. i. des.
    + left.
      unfold lang_steps_failure, Thread.steps_failure in *. des.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
      esplits; eauto.
      hexploit sim_local_promise_consistent; eauto. i. des.
      econs 2. econs; eauto.
    + right.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; eauto. i.
      esplits; eauto.
  - i. right.
    exploit sim_local_memory_bot; eauto. i.
    esplits; eauto.
  - ii. inv STEP_TGT; inv STEP0; [|inv LOCAL0].
    + right.
      exploit sim_local_promise_bot; eauto. i. des.
      esplits; (try exact SC); eauto; ss.
      econs 2. econs 1. econs; eauto.
    + exploit STEP; eauto. i. des.
      * left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto.
      * right.
        inv SIM0; [|done].
        inv EVT. dependent destruction STEP_SRC.
        { esplits;
            (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
            (try exact SC);
            eauto; ss.
          econs 1.
        }
        { esplits;
            (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
            (try exact SC);
            eauto; ss.
          econs 2. econs 2. econs; [|econs 1]; eauto.
        }
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; ss.
      inv EVT. dependent destruction STEP_SRC.
      exploit sim_local_read; eauto. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 2]; eauto.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. dependent destruction STEP_SRC.
      hexploit sim_local_write_bot;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl; try by viewtac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 3]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. dependent destruction STEP_SRC.
      exploit Local.read_step_future; eauto. i. des.
      exploit sim_local_read; eauto; try refl. i. des.
      exploit Local.read_step_future; eauto. i. des.
      hexploit sim_local_write_bot;
        (try exact LOCAL0);
        (try exact SC);
        eauto; try refl; try by viewtac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 4]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. dependent destruction STEP_SRC.
      exploit sim_local_fence;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 5]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      right.
      inv SIM0; [|done].
      inv EVT. dependent destruction STEP_SRC.
      exploit sim_local_fence;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2.
        econs; [|econs 6]; eauto.
      * ss.
      * ss.
      * ss.
      * right. apply CIH; auto.
    + exploit STEP; eauto. i. des.
      { left.
        unfold lang_steps_failure, Thread.steps_failure in *. des.
        exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
        esplits; eauto.
        hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; eauto. }
      left.
      inv SIM0; [|done].
      inv EVT. dependent destruction STEP_SRC.
      exploit sim_local_failure;
        (try exact LOCAL);
        eauto. i. des.
      unfold Thread.steps_failure.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto).
      econs 2. econs; [|econs 7]; eauto.
Qed.

Lemma sim_trace_sim_itree R_src R_tgt
      (sim_val:SIM_VAL R_src R_tgt)
      itr_src
      itr_tgt
      (SIM: sim_trace sim_val itr_src itr_tgt):
  sim_itree sim_val
            itr_src
            itr_tgt.
Proof.
  ii. apply sim_trace_sim_thread; auto.
Qed.

Lemma sim_trace_sim_ktree R_src0 R_tgt0 R_src1 R_tgt1
      (sim_val1: SIM_VAL R_src0 R_tgt0) (sim_val2:SIM_VAL R_src1 R_tgt1)
      ktr_src
      ktr_tgt
      (SIM: forall r_src r_tgt
                   (SIM_VAL1: sim_val1 r_src r_tgt),
          sim_trace sim_val2 (ktr_src r_src) (ktr_tgt r_tgt)):
  sim_ktree sim_val1
            ktr_src
            ktr_tgt
            sim_val2.
Proof.
  ii. apply sim_trace_sim_thread; auto.
Qed.

Lemma sim_trace_ret R_src R_tgt
      (sim_val:SIM_VAL R_src R_tgt)
      r_src r_tgt
      (RET: sim_val r_src r_tgt):
  sim_trace sim_val
            (Ret r_src)
            (Ret r_tgt).
Proof.
  pfold. unfold _sim_trace. splits.
  - i. right. esplits; eauto.
    + econs; eauto.
    + econs; eauto.
  - i. inv STEP_TGT.
Qed.


(* instr *)

Lemma sim_trace_trigger R
      (i_src i_tgt: MemE.t R)
      (ORD: MemE.ord i_src i_tgt):
  sim_trace eq
            (ITree.trigger i_src)
            (ITree.trigger i_tgt).
Proof.
  unfold ITree.trigger.
  pfold. unfold _sim_trace. splits.
  { i. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
  i. ss. dependent destruction ORD; dependent destruction STEP_TGT.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. econs.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. econs.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs; eauto.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs. eauto.
    + econs 2. econs; eauto.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. ss.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. ss.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. ss.
    + left. apply sim_trace_ret. ss.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. ss.
    + left. apply sim_trace_ret. ss.
Qed.

Lemma sim_trace_choose r:
  sim_trace eq
            (ITree.trigger MemE.choose)
            (Ret r).
Proof.
  unfold ITree.trigger.
  pfold. unfold _sim_trace. splits.
  { i. right. esplits.
    { econs 2; eauto. econs; eauto. }
    { econs; eauto. }
    { econs; try refl. }
  }
  i. ss. inv STEP_TGT.
Qed.

Lemma eutt_sim_trace R_src R_tgt
      (sim_val: SIM_VAL R_src R_tgt)
      (itr_src: itree MemE.t R_src) (itr_tgt: itree MemE.t R_tgt)
      (EUTT: eutt sim_val itr_src itr_tgt)
  :
    sim_trace sim_val itr_src itr_tgt.
Proof.
  revert R_src R_tgt sim_val itr_src itr_tgt EUTT. pcofix CIH.
  i. punfold EUTT. unfold eqit_ in EUTT.
  replace itr_src with (go (observe itr_src)).
  2:{ apply bisim_is_eq. symmetry. apply itree_eta. }
  replace itr_tgt with (go (observe itr_tgt)).
  2:{ apply bisim_is_eq. symmetry. apply itree_eta. }
  revert EUTT.
  generalize (observe itr_src) as itr_src'.
  generalize (observe itr_tgt) as itr_tgt'. clear itr_src itr_tgt. i.
  induction EUTT.
  - pfold. econs.
    2:{ ii. inv STEP_TGT. }
    ii. right. esplits; eauto.
    { econs; eauto. }
    { econs; eauto. }
  - pclearbot. pfold. econs.
    { ii. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
    ii. ss. dependent destruction STEP_TGT. right.
    esplits; eauto.
    { econs. }
    econs 2. econs; eauto.
  - pclearbot. pfold. econs.
    { ii. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
    ii. ss. right.
    dependent destruction STEP_TGT.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
    + esplits; [econs; refl|eauto|econs 2|right; apply CIH; eauto]; econs; eauto.
  - admit.
  - pfold. econs.
    { ii. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
    ii. ss. right.
    dependent destruction STEP_TGT.
    esplits; [econs; refl|eauto|econs 1|]. right. eauto.
Admitted.

Lemma sim_trace_refl R (itr: itree MemE.t R):
  sim_trace eq itr itr.
Proof.
  eapply eutt_sim_trace. refl.
Qed.

Lemma sim_itree_refl R (itr: itree MemE.t R):
  sim_itree eq itr itr.
Proof.
  eapply sim_trace_sim_itree.
  eapply sim_trace_refl.
Qed.


(* replacing abort with arbitrary instructions *)

Lemma sim_trace_replace_abort R (itr: itree MemE.t R):
  sim_trace bot2
            (ITree.trigger MemE.abort)
            itr.
Proof.
  pfold. unfold _sim_trace. splits; i.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs. ss.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs. ss.
Qed.

Lemma sim_itree_replace_abort R (itr: itree MemE.t R):
  sim_itree bot2 (ITree.trigger MemE.abort) itr.
Proof.
  apply sim_trace_sim_itree. i.
  apply sim_trace_replace_abort; ss.
Qed.


(* eliminating instructions after abort *)

Lemma sim_trace_elim_after_abort R (k: ktree MemE.t _ R):
  sim_trace bot2
            (ITree.trigger MemE.abort >>= k)
            (ITree.trigger MemE.abort).
Proof.
  replace (ITree.trigger MemE.abort >>= k) with
      (Vis MemE.abort (fun r => k r)).
  2:{ unfold ITree.trigger. grind. repeat f_equal. extensionality u. grind. }
  pfold. unfold _sim_trace. splits; i.
  - inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs. econs.
Qed.

Lemma sim_itree_elim_after_abort R (k: ktree MemE.t _ R):
  sim_itree bot2
            (ITree.trigger MemE.abort >>= k)
            (ITree.trigger MemE.abort).
Proof.
  apply sim_trace_sim_itree.
  apply sim_trace_elim_after_abort; ss.
Qed.
