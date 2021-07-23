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
Require Import SimTraceCommon.

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

Variant sim_traceF (r: SIM_THREAD): SIM_THREAD :=
| sim_traceF_intro
    R_src R_tgt
    (sim_val: SIM_VAL R_src R_tgt)
    st1_src lc1_src sc1_src mem1_src
    st1_tgt lc1_tgt sc1_tgt mem1_tgt
    (SIM: paco5 _sim_trace (@_sim_itree r) _ _ sim_val st1_src st1_tgt)
    (LOCAL: sim_local SimPromises.bot lc1_src lc1_tgt):
    @sim_traceF
      r
      (lang R_src) (lang R_tgt)
      (sim_terminal sim_val)
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_trace_F_mon: monotone11 sim_traceF.
Proof.
  ii. destruct IN. econs; eauto.
  eapply paco5_mon; eauto. eapply _sim_itree_mon; eauto.
Qed.

Lemma sim_traceF_uclo:
  sim_traceF <12= gupaco11 _sim_thread (cpn11 _sim_thread).
Proof.
  eapply grespect11_uclo.
  { eauto with paco. }
  econs.
  { eapply sim_trace_F_mon. }
  ii. destruct PR.
  eapply rclo11_clo_base. econs.
  { eapply cpn11_compat. eauto with paco. }
  eapply cpn11_gupaco; eauto with paco.
  revert_until sim_val. gcofix CIH. i.
  generalize SIM. i. punfold SIM0. unfold _sim_trace in SIM0. des.
  gstep. ii. splits.
  - i. exploit TERMINAL; eauto. i. des.
    + left.
      unfold lang_steps_failure, Thread.steps_failure in *. des.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
      esplits; eauto.
      * hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; [|econs 7]; eauto.
      * ss.
    + right.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; eauto. i.
      esplits; eauto.
  - i. right.
    exploit sim_local_memory_bot; eauto. i.
    esplits; eauto.
  - ii. inv STEP_TGT; inv STEP0.
    { (* promise *)
      right.
      exploit sim_local_promise_bot; eauto. i. des.
      esplits; (try exact SC); eauto; ss.
      econs 2. econs 1. econs; eauto. gbase. eauto. }
    exploit STEP; eauto. i. des.
    { (* failure *)
      left.
      unfold lang_steps_failure, Thread.steps_failure in *. des.
      exploit rtc_lang_tau_step_rtc_thread_tau_step; try exact STEPS. i.
      esplits; eauto.
      - hexploit sim_local_promise_consistent; eauto. i. des.
        econs 2. econs; [|econs 7]; eauto.
      - ss.
    }
    inv LOCAL0; ss.
    + (* silent *)
      right.
      inv EVT. inv STEP_SRC.
      * esplits;
          (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
          (try exact SC);
          eauto; ss.
        { econs 1. }
        { ss. }
        { gbase. inv SIM0; eauto.
          { exploit H; eauto. i. eapply GF in x.
            eapply CIH0. eapply _sim_thread_mon; eauto.
            i. eapply rclo11_clo_base. right. gbase. auto.
          }
        }
      * esplits;
          (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
          (try exact SC);
          eauto; ss.
        { econs 2. econs 2. econs; [|econs 1]; eauto. }
        { ss. }
        { gbase. inv SIM0; eauto.
          { exploit H; eauto. i. eapply GF in x.
            eapply CIH0. eapply _sim_thread_mon; eauto.
            i. eapply rclo11_clo_base. right. gbase. auto.
          }
        }
    + (* read *)
      right.
      inv EVT. inv STEP_SRC.
      exploit sim_local_read; eauto. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 2]; eauto.
      * ss.
      * ss.
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* write *)
      right.
      inv EVT. inv STEP_SRC.
      hexploit sim_local_write_bot;
        (try exact LOCAL1);
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
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* update *)
      right.
      inv EVT. inv STEP_SRC.
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
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* fence *)
      right.
      inv EVT. inv STEP_SRC.
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
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* syscall *)
      right.
      inv EVT. inv STEP_SRC.
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
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* failure *)
      left.
      inv EVT. inv STEP_SRC.
      exploit sim_local_failure;
        (try exact LOCAL);
        eauto. i. des.
      unfold Thread.steps_failure.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto).
      * econs 2. econs; [|econs 7]; eauto.
      * ss.
    + (* na write *)
      right.
      inv EVT. inv STEP_SRC.
      exploit Local.write_undef_step_future; eauto. i. des.
      exploit sim_local_write_undef;
        (try exact LOCAL);
        (try exact SC);
        eauto; try refl. i. des.
      exploit Local.write_undef_step_future; eauto. i. des.
      rewrite SimPromises.unset_bot in *.
      hexploit sim_local_write_bot;
        (try exact LOCAL0);
        (try exact SC0);
        eauto; try refl; try by viewtac. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC3).
      * ss.
      * econs 2. econs 2. econs; [|econs 8]; eauto.
      * ss.
      * ss.
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* racy read*)
      right.
      inv EVT. inv STEP_SRC.
      exploit sim_local_racy_read; eauto. i. des.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * ss.
      * econs 2. econs 2. econs; [|econs 9]; eauto.
      * ss.
      * ss.
      * gbase. inv SIM0; eauto.
        { exploit H; eauto. i. eapply GF in x.
          eapply CIH0. eapply _sim_thread_mon; eauto.
          i. eapply rclo11_clo_base. right. gbase. auto.
        }
    + (* racy write *)
      left.
      inv EVT. inv STEP_SRC.
      exploit sim_local_racy_write; eauto. i. des.
      unfold Thread.steps_failure.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs; [|econs 10]; eauto.
      * ss.
    + (* racy update *)
      left.
      inv EVT. inv STEP_SRC.
      exploit sim_local_racy_update; eauto. i. des.
      unfold Thread.steps_failure.
      esplits;
        (try by apply rtc_lang_tau_step_rtc_thread_tau_step; eauto);
        (try exact SC).
      * econs 2. econs; [|econs 11]; eauto.
      * ss.
Qed.

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
  ginit. guclo sim_traceF_uclo. econs; eauto.
  eapply paco5_mon; [eapply SIM|]. ss.
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
  - left. red. esplits; eauto. econs.
  - right. esplits; eauto.
    + econs; eauto.
    + econs 2. econs. ss.
    + left. apply sim_trace_ret. ss.
  Unshelve. all: try exact ITree.spin.
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

Variant tauF_l (r: SIM_TRACE): SIM_TRACE :=
| tauF_l_intro
    R_src R_tgt
    (sim_val: SIM_VAL R_src R_tgt)
    st_src0 st_src1 st_tgt
    (STEP: ILang.step ProgramEvent.silent st_src0 st_src1)
    (SIM: r R_src R_tgt sim_val st_src1 st_tgt)
  :
    tauF_l r sim_val st_src0 st_tgt
.

Lemma tauF_l_mon: monotone5 tauF_l.
Proof.
  ii. destruct IN. econs; eauto.
Qed.

Lemma tauF_l_uclo:
  tauF_l <6= gupaco5 _sim_trace (cpn5 _sim_trace).
Proof.
  eapply cpn5_uclo; eauto with paco.
  { eapply tauF_l_mon. }
  i. destruct PR. inv SIM. econs.
  { ii. exploit H; eauto. i. des.
    { left. unfold lang_steps_failure in *. des. esplits.
      { econs 2; eauto. }
      { eauto. }
    }
    { right. esplits.
      { econs 2; eauto. }
      { eauto. }
      { eauto. }
    }
  }
  { ii. exploit H0; eauto. i. des.
    { left. unfold lang_steps_failure in *. des. esplits.
      { econs 2; eauto. }
      { eauto. }
    }
    { right. esplits.
      { eauto. }
      { econs 2; eauto. }
      { eauto. }
      { gbase. eauto. }
    }
  }
Qed.

Variant tauF_r (r: SIM_TRACE): SIM_TRACE :=
| tauF_r_intro
    R_src R_tgt
    (sim_val: SIM_VAL R_src R_tgt)
    st_src st_tgt0
    (SIM: forall st_tgt1 e
                 (STEP: ILang.step e st_tgt0 st_tgt1),
        e = ProgramEvent.silent /\ r R_src R_tgt sim_val st_src st_tgt1)
    (NRET: ~ ILang.is_terminal st_tgt0)
  :
    tauF_r r sim_val st_src st_tgt0
.

Lemma tauF_r_mon: monotone5 tauF_r.
Proof.
  ii. destruct IN. econs; eauto.
  ii. exploit SIM; eauto. i. des; eauto.
Qed.

Lemma tauF_r_uclo:
  tauF_r <6= gupaco5 _sim_trace (cpn5 _sim_trace).
Proof.
  eapply wrespect5_uclo; eauto with paco. econs.
  { eapply tauF_r_mon. }
  i. destruct PR. econs.
  { ii. ss. }
  ii. exploit SIM; eauto. i. des; clarify. right.
  esplits.
  { econs. }
  { eauto. }
  { econs 1. }
  eapply rclo5_base. eauto.
Qed.

Lemma eutt_sim_trace R_src R_tgt
      (sim_val: SIM_VAL R_src R_tgt)
      (itr_src: itree MemE.t R_src) (itr_tgt: itree MemE.t R_tgt)
      (EUTT: eutt sim_val itr_src itr_tgt)
  :
    sim_trace sim_val itr_src itr_tgt.
Proof.
  ginit.
  { eapply cpn5_wcompat. eauto with paco. }
  revert R_src R_tgt sim_val itr_src itr_tgt EUTT. gcofix CIH.
  i. punfold EUTT. unfold eqit_ in EUTT.
  replace itr_src with (go (observe itr_src)).
  2:{ apply bisim_is_eq. symmetry. apply itree_eta. }
  replace itr_tgt with (go (observe itr_tgt)).
  2:{ apply bisim_is_eq. symmetry. apply itree_eta. }
  revert EUTT.
  generalize (observe itr_src) as itr_src'.
  generalize (observe itr_tgt) as itr_tgt'. clear itr_src itr_tgt. i.
  induction EUTT.
  - gstep. econs.
    2:{ ii. inv STEP_TGT. }
    ii. right. esplits; eauto.
    { econs; eauto. }
    { econs; eauto. }
  - pclearbot. gstep. econs.
    { ii. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
    ii. ss. dependent destruction STEP_TGT. right.
    esplits; eauto.
    { econs. }
    { econs 2. econs; eauto. }
    gbase. eauto.
  - pclearbot. gstep. econs.
    { ii. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
    ii. ss. dependent destruction STEP_TGT.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + right. esplits; [econs; refl|eauto|econs 2|gbase; apply CIH; eauto]; econs; eauto.
    + left. econs. esplits; eauto. econs.
  - guclo tauF_l_uclo. econs; eauto. econs. eapply bisim_is_eq. symmetry. eapply itree_eta.
  - gstep. econs.
    { ii. inv TERMINAL_TGT. apply f_equal with (f:=observe) in H; ss. }
    ii. ss. right.
    dependent destruction STEP_TGT.
    esplits; [econs; refl|eauto|econs 1|]. gbase. eauto.
  Unshelve. all: try exact ITree.spin.
Qed.

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
    econs.
  - left.
    unfold lang_steps_failure. esplits; eauto.
    econs.
  Unshelve. all: try exact ITree.spin.
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
    econs.
  Unshelve. all: try exact ITree.spin.
Qed.

Lemma sim_itree_elim_after_abort R (k: ktree MemE.t _ R):
  sim_itree bot2
            (ITree.trigger MemE.abort >>= k)
            (ITree.trigger MemE.abort).
Proof.
  apply sim_trace_sim_itree.
  apply sim_trace_elim_after_abort; ss.
  Unshelve. all: try exact ITree.spin.
Qed.
