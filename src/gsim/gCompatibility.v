Require Import Bool.
Require Import List.

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

Require Import gSimAux.
Require Import gSimMemory.
Require Import gSimulation.
Require Import JoinedView.

Require Import Program.

Require Import ITreeLang.
Require Import ITreeLib.

Set Implicit Arguments.


Definition SIM_VAL R_src R_tgt := forall (r_src:R_src) (r_tgt:R_tgt), Prop.


Variant sim_terminal R_src R_tgt
        (sim_ret:SIM_VAL R_src R_tgt)
        (st_src: itree MemE.t R_src) (st_tgt: itree MemE.t R_tgt): Prop :=
| sim_terminal_intro
    r0 r1
    (SIMRET: sim_ret r0 r1)
    (SRC: st_src = Ret r0)
    (TGT: st_tgt = Ret r1)
.

Definition _sim_itree
           (sim_thread:SIM_THREAD world)
           R_src R_tgt
           (sim_ret:SIM_VAL R_src R_tgt)
           (itr_src: itree MemE.t R_src) (itr_tgt: itree MemE.t R_tgt): Prop :=
  forall b lc_src lc_tgt sc0_src sc0_tgt mem0_src mem0_tgt w1 views1 fin1
         (LOCAL: sim_local w1 views1 lc_src lc_tgt),
    sim_thread
      (lang R_src) (lang R_tgt)
      (sim_terminal sim_ret)
      b w1
      itr_src lc_src sc0_src mem0_src
      itr_tgt lc_tgt sc0_tgt mem0_tgt
      (views1, fin1).

Definition _sim_ktree
           (sim_thread:SIM_THREAD world)
           R_src0 R_tgt0 R_src1 R_tgt1
           (sim_ret0:SIM_VAL R_src0 R_tgt0)
           (ktr_src: R_src0 -> itree MemE.t R_src1)
           (ktr_tgt: R_tgt0 -> itree MemE.t R_tgt1)
           (sim_ret1:SIM_VAL R_src1 R_tgt1): Prop :=
  forall r_src r_tgt
         (RET: sim_ret0 r_src r_tgt),
    _sim_itree sim_thread sim_ret1 (ktr_src r_src) (ktr_tgt r_tgt).

Lemma _sim_itree_mon
      s1 s2 (S: s1 <14= s2):
  @_sim_itree s1 <5= @_sim_itree s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Lemma _sim_ktree_mon
      s1 s2 (S: s1 <14= s2):
  @_sim_ktree s1 <8= @_sim_ktree s2.
Proof.
  ii. apply S. eapply PR; eauto.
Qed.

Lemma lang_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1) e
      (STEP: ILang.step e itr0 itr1):
  ILang.step e
             (itr0 >>= k)
             (itr1 >>= k).
Proof.
  dependent destruction STEP; subst; ired; try econs; eauto.
  rewrite bind_spin. econs; eauto.
Qed.

Lemma program_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1) e
      lc1 sc1 mem1
      lc2 sc2 mem2
      (STEP: Thread.program_step
               e
               (Thread.mk (lang R0) itr0 lc1 sc1 mem1)
               (Thread.mk (lang R0) itr1 lc2 sc2 mem2)):
  Thread.program_step
    e
    (Thread.mk (lang R1) (itr0 >>= k) lc1 sc1 mem1)
    (Thread.mk (lang R1) (itr1 >>= k) lc2 sc2 mem2).
Proof.
  inv STEP; inv LOCAL; ss.
  - econs; [|econs 1]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 2]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 3]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 4]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 5]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 6]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 7]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 8]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 9]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 10]; s; eauto. apply lang_step_bind. auto.
  - econs; [|econs 11]; s; eauto. apply lang_step_bind. auto.
Qed.

Lemma step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1) pf e
      lc1 sc1 mem1
      lc2 sc2 mem2
      (STEP: Thread.step pf e
                         (Thread.mk (lang R0) itr0 lc1 sc1 mem1)
                         (Thread.mk (lang R0) itr1 lc2 sc2 mem2)):
  Thread.step pf e
              (Thread.mk (lang R1) (itr0 >>= k) lc1 sc1 mem1)
              (Thread.mk (lang R1) (itr1 >>= k) lc2 sc2 mem2).
Proof.
  inv STEP.
  - econs 1. inv STEP0. econs; eauto.
  - econs 2. apply program_step_bind. eauto.
Qed.

Lemma opt_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1) e
      lc1 sc1 mem1
      lc2 sc2 mem2
      (STEP: Thread.opt_step e
                             (Thread.mk (lang R0) itr0 lc1 sc1 mem1)
                             (Thread.mk (lang R0) itr1 lc2 sc2 mem2)):
  Thread.opt_step e
                  (Thread.mk (lang R1) (itr0 >>= k) lc1 sc1 mem1)
                  (Thread.mk (lang R1) (itr1 >>= k) lc2 sc2 mem2).
Proof.
  inv STEP.
  - econs 1.
  - econs 2. apply step_bind. eauto.
Qed.

Lemma lang_step_deseq
      R0 R1 ktr (itr1: itree MemE.t R0) (itr2: itree MemE.t R1) e
      (STEP: ILang.step e
                        (itr1 >>= ktr)
                        itr2):
  (exists r,
      itr1 = Ret r /\
      ILang.step e (ktr r) itr2) \/
  (exists itr2',
      itr2 = itr2' >>= ktr /\
      ILang.step e itr1 itr2') \/
  (itr1 = Vis MemE.abort (Empty_set_rect _) /\
   e = ProgramEvent.failure)
.
Proof.
  ides itr1.
  { rewrite bind_ret_l in STEP. left. esplits; eauto. }
  { rewrite bind_tau in STEP. dependent destruction STEP.
    right. left. esplits; eauto. econs. eauto. }
  { rewrite bind_vis in STEP.
    dependent destruction STEP; try by (right; left; esplits; eauto; econs; eauto).
    right. right. splits; auto. f_equal. f_equal. extensionality v. ss. }
Qed.

Lemma thread_step_deseq
      R0 R1 ktr (itr1: itree MemE.t R0) (itr2: itree MemE.t R1)
      pf e
      lc1 sc1 mem1
      lc2 sc2 mem2
      (STEP: Thread.step pf e
                         (Thread.mk (lang _) (itr1 >>= ktr) lc1 sc1 mem1)
                         (Thread.mk (lang _) itr2 lc2 sc2 mem2)):
  (exists r,
      itr1 = Ret r /\
      Thread.step pf e
                  (Thread.mk (lang _) (ktr r) lc1 sc1 mem1)
                  (Thread.mk (lang _) (itr2) lc2 sc2 mem2)) \/
  (exists itr2',
      itr2 = itr2' >>= ktr /\
      Thread.step pf e
                  (Thread.mk (lang _) itr1 lc1 sc1 mem1)
                  (Thread.mk (lang _) itr2' lc2 sc2 mem2)) \/
  (itr1 = Vis MemE.abort (Empty_set_rect _) /\
   e = ThreadEvent.failure)
.
Proof.
  inv STEP.
  - inv STEP0. right. left. esplits; eauto.
    econs 1. econs; eauto.
  - inv STEP0; ss.
    apply lang_step_deseq in STATE. des; clarify.
    { left. esplits; eauto. econs 2. econs; eauto. }
    { right. left. esplits; eauto. econs 2. econs; eauto. }
    { destruct e; ss; auto. }
Qed.

Lemma sim_rtc
      A B
      (sim:A -> B -> Prop)
      (rA:A -> A -> Prop)
      (rB:B -> B -> Prop)
      (SIM:
         forall a1 a2 b1 (RA: rA a1 a2) (SIM1: sim a1 b1),
         exists b2, rB b1 b2 /\ sim a2 b2)
      a1 a2 b1
      (RA: rtc rA a1 a2) (SIM1: sim a1 b1):
  exists b2, rtc rB b1 b2 /\ sim a2 b2.
Proof.
  revert b1 SIM1. induction RA; i.
  - esplits; eauto.
  - exploit SIM; eauto. i. des.
    exploit IHRA; eauto. i. des.
    esplits; [|eauto].
    econs; eauto.
Qed.

Inductive sim_bind R0 R1 (k: R0 -> itree MemE.t R1):
  forall (lhs: Thread.t (lang R0)) (rhs:Thread.t (lang R1)), Prop :=
| sim_bind_intro
    itr lc sc mem:
    sim_bind k
             (Thread.mk (lang R0) itr lc sc mem)
             (Thread.mk (lang R1) (itr >>= k) lc sc mem)
.

Lemma rtc_internal_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1)
      lc1 sc1 mem1
      lc2 sc2 mem2
      (STEP: rtc (@Thread.tau_step (lang R0))
                 (Thread.mk (lang R0) itr0 lc1 sc1 mem1)
                 (Thread.mk (lang R0) itr1 lc2 sc2 mem2)):
  rtc (@Thread.tau_step (lang R1))
      (Thread.mk (lang R1) (itr0 >>= k) lc1 sc1 mem1)
      (Thread.mk (lang R1) (itr1 >>= k) lc2 sc2 mem2).
Proof.
  exploit (sim_rtc (sim_bind k)); eauto.
  - i. inv SIM1. destruct a2. destruct local. inv RA. inv TSTEP.
    generalize (step_bind k STEP0). i.
    esplits; [|econs; eauto].
    eapply tau_intro; eauto. eapply Thread.step_nopf_intro. eauto.
  - econs; ss.
  - i. des. inv x1. auto.
Qed.


Global Hint Resolve cpn11_wcompat: paco.

Inductive ctx (sim_thread:SIM_THREAD world): SIM_THREAD world :=
| ctx_ret
    R_src R_tgt b w0 views0 fin0
    (sim_ret:SIM_VAL R_src R_tgt)
    sc0_src mem0_src
    sc0_tgt mem0_tgt
    lc_src lc_tgt (r_src: R_src) (r_tgt: R_tgt)
    (RET: sim_ret r_src r_tgt)
    (LOCAL: sim_local w0 views0 lc_src lc_tgt):
    @ctx sim_thread
         (lang R_src) (lang R_tgt)
         (sim_terminal sim_ret)
         b w0
         (Ret r_src) lc_src sc0_src mem0_src
         (Ret r_tgt) lc_tgt sc0_tgt mem0_tgt
         (views0, fin0)
| ctx_bind
    R_src0 R_tgt0 R_src1 R_tgt1 b w0 views0 fin0
    (sim_ret1:SIM_VAL R_src0 R_tgt0) (sim_ret2:SIM_VAL R_src1 R_tgt1)
    itr0 k0 lc_src sc0_src mem0_src
    itr1 k1 lc_tgt sc0_tgt mem0_tgt
    (SIM1: sim_thread (lang R_src0) (lang R_tgt0) (sim_terminal sim_ret1)
                      b w0
                      itr0 lc_src sc0_src mem0_src
                      itr1 lc_tgt sc0_tgt mem0_tgt
                      (views0, fin0))
    (SIM2: _sim_ktree sim_thread sim_ret1 k0 k1 sim_ret2):
    @ctx sim_thread
         (lang R_src1) (lang R_tgt1)
         (sim_terminal sim_ret2)
         b w0
         (itr0 >>= k0) lc_src sc0_src mem0_src
         (itr1 >>= k1) lc_tgt sc0_tgt mem0_tgt
         (views0, fin0)
| ctx_tau_iter
    I_src I_tgt R_src R_tgt b w0 views0 fin0
    (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
    sc0_src mem0_src
    sc0_tgt mem0_tgt
    lc_src lc_tgt
    (body_src: I_src -> itree MemE.t (I_src + R_src))
    (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
    (SIM: _sim_ktree sim_thread sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1))
    i_src i_tgt
    (VAL: sim_ret0 i_src i_tgt)
    (LOCAL: sim_local w0 views0 lc_src lc_tgt)
  :
    @ctx sim_thread
         (lang R_src) (lang R_tgt)
         (sim_terminal sim_ret1)
         b w0
         (tau;;(ITree.iter body_src i_src)) lc_src sc0_src mem0_src
         (tau;;(ITree.iter body_tgt i_tgt)) lc_tgt sc0_tgt mem0_tgt
         (views0, fin0)
.

Lemma ctx_mon: monotone14 ctx.
Proof.
  ii. destruct IN.
  - econs 1; eauto.
  - econs 2; eauto. ii. eapply LE. eapply SIM2; eauto.
  - econs 3; eauto. ii. eapply LE. eapply SIM; eauto.
Qed.
Hint Resolve ctx_mon.


Lemma unfold_iter_eq {E} {A B} (f: A -> itree E (A + B)) (a: A)
  :
    ITree.iter f a
    = lr <- f a;;
      match lr with
      | inl l => tau;; ITree.iter f l
      | inr r => Ret r
      end.
Proof.
  eapply bisimulation_is_eq. eapply unfold_iter.
Qed.

Definition _sim_thread := @_sim_thread world world_messages_le sim_memory sim_timemap sim_local.

Lemma _sim_thread_mon: monotone14 _sim_thread.
Proof.
  eapply _sim_thread_mon.
Qed.
Hint Resolve _sim_thread_mon: paco.
Hint Resolve cpn14_wcompat: paco.

Lemma ctx_compat:
  ctx <15= gupaco14 _sim_thread (cpn14 _sim_thread).
Proof.
  assert (MON: monotone14 _sim_thread).
  (* paco tactics do not work well without this *)
  { eapply _sim_thread_mon; eauto. }
  eapply wrespect14_uclo; auto.
  econs; auto. i. destruct PR.
  - (* ret *)
    rr. split.
    { ii. splits; s; ii.
      { right. inv TERMINAL_TGT. ss. esplits; eauto; ss.
        - econs; eauto.
        - eapply sim_future_memory_sc_future in FUTURE; eauto.
          { des. eapply sim_local_mon; eauto. }
          { typeclasses eauto. }
        - econs; eauto.
        - refl.
      }
      { right. subst. esplits; eauto. eapply sim_local_memory_bot; eauto. }
      inv STEP_TGT.
      inv STEP; try by inv STEP0; inv STATE.
      inv STEP0; ss.
      hexploit (@sim_local_promise b w1 views1 views2); eauto.
      { eapply sim_future_memory_sc_future in FUTURE; eauto.
        { des. eapply sim_local_mon; eauto. }
        { i. typeclasses eauto. }
      }
      { i. subst. eapply PROMISE; eauto. }
      i. des.
      right. esplits; try apply MEM2.
      + ss.
      + eauto.
      + econs 2. econs 1. econs; eauto.
      + eauto.
      + eapply sim_timemap_mon; eauto.
      + eapply rclo14_clo_base. eapply ctx_ret; auto.
      + auto.
    }
    { ii. subst. hexploit sim_cap; eauto.
      i. des. esplits; eauto.
      i. hexploit CAP; eauto. i. des. esplits; eauto.
      eapply rclo14_clo_base. econs; eauto.
    }
  - (* bind *)
    eapply GF in SIM1. red in SIM1. red in SIM1. des.
    red. red. split.
    { clear CAP. ii. ss.
      exploit FUTURE; try apply SC; eauto. i. des.
      splits; s; ii.
      { inv TERMINAL_TGT. ides itr1.
        2: { eapply f_equal with (f:=observe) in H. ss. }
        2: { eapply f_equal with (f:=observe) in H. ss. }
        rewrite bind_ret_l in H.
        exploit TERMINAL; (try by econs); auto. i. des.
        - left.
          unfold Thread.steps_failure in *. des.
          destruct e2, e3.
          eapply rtc_internal_step_bind in STEPS.
          eapply step_bind in STEP_FAILURE.
          esplits; eauto.
        - inv TERMINAL_SRC.
          exploit Thread.rtc_tau_step_future; eauto. s. i. des.
          inv TERMINAL0. ss.
          assert (x0 = r1).
          { eapply f_equal with (f:=observe) in SRC. ss. clarify. }
          assert (r0 = r2).
          { eapply f_equal with (f:=observe) in TGT. ss. clarify. }
          subst.
          exploit SIM2; eauto. i. eapply GF in x0.
          red in x0. red in x0. des. clear CAP. ss.
          exploit FUTURE1; try apply SC0; eauto.
          { refl. }
          { red. destruct b.
            { splits; auto. }
            { splits; try refl. auto. }
          }
          { refl. }
          i. ss. des. exploit TERMINAL0; try by econs.
          { econs. eauto. }
          i. des.
          + left.
            unfold Thread.steps_failure in *. des.
            destruct e2.
            esplits; [|eauto|eauto].
            etrans; try exact STEPS0.
            eapply rtc_internal_step_bind in STEPS.
            rewrite bind_ret_l in STEPS. eauto.
          + right.
            esplits; cycle 1; eauto.
            * rewrite bind_ret_l. eauto.
            * etrans; eauto.
              eapply world_messages_le_mon; eauto.
              i. eapply rtc_step_unchangable in STEPS; eauto.
            * etrans; [|eauto].
              eapply rtc_internal_step_bind in STEPS.
              rewrite bind_ret_l in STEPS. eauto.
      }
      { exploit PROMISES; eauto. i. des.
        - left.
          unfold Thread.steps_failure in *. des.
          destruct e2, e3.
          eapply rtc_internal_step_bind in STEPS.
          eapply step_bind in STEP_FAILURE.
          esplits; eauto.
        - right.
          destruct lc_tgt, lc2_src. ss. subst.
          esplits; [|eauto].
          + eapply rtc_internal_step_bind. apply STEPS.
          + ss.
      }
      inv STEP_TGT.
      hexploit thread_step_deseq; eauto. i. des; clarify.
      + exploit TERMINAL; (try by econs); auto. i. des.
        * left.
          unfold Thread.steps_failure in *. des.
          destruct e2, e3. ss.
          eapply rtc_internal_step_bind in STEPS.
          eapply step_bind in STEP_FAILURE.
          esplits; eauto.
        * inv TERMINAL_SRC. ss. subst.
          exploit Thread.rtc_tau_step_future; eauto. s. i. des.
          inv TERMINAL0. ss. subst.
          assert (x = r1).
          { eapply f_equal with (f:=observe) in SRC. ss. clarify. }
          assert (r0 = r2).
          { eapply f_equal with (f:=observe) in TGT. ss. clarify. }
          subst.
          exploit SIM2; eauto. i. eapply GF in x.
          red in x. red in x. des. clear CAP.
          exploit FUTURE1; try apply SC0; eauto.
          { refl. }
          { red. destruct b.
            { splits; auto. }
            { splits; try refl. auto. }
          }
          { refl. }
          i. ss. des.
          hexploit STEP1; eauto; ss. i. des.
          { left.
            unfold Thread.steps_failure in *. des.
            destruct e2, e3.
            eapply rtc_internal_step_bind in STEPS.
            esplits; try exact STEP_FAILURE; [|eauto].
            etrans; eauto. rewrite bind_ret_l. eauto. }
          { right.
            esplits; cycle 2; eauto.
            - eapply rclo14_base. auto.
            - etrans; eauto.
              eapply world_messages_le_mon; eauto.
              i. eapply rtc_step_unchangable in STEPS; eauto.
            - eapply rtc_internal_step_bind in STEPS.
              etrans; [apply STEPS|eauto].
              rewrite bind_ret_l. eauto. }
      + destruct lc3_tgt.
        hexploit STEP; eauto; ss. i. des.
        * left.
          unfold Thread.steps_failure in *. des.
          destruct e2, e3.
          eapply rtc_internal_step_bind in STEPS.
          eapply step_bind in STEP_FAILURE.
          esplits; eauto.
        * right.
          destruct lc2_src. destruct lc3_src.
          esplits; [|M|M| | | | |]; Mskip eauto.
          { eapply rtc_internal_step_bind. eauto. }
          { eapply opt_step_bind. eauto. }
          { eapply rclo14_clo_base. eapply ctx_bind; eauto.
            eapply _sim_ktree_mon; cycle 1; eauto.
          }
      + left. inv STEP0; inv STEP1. inv LOCAL. hexploit STEP; ss.
        { instantiate (6:=ThreadEvent.failure).
          econs; eauto. econs 2. ss. econs; eauto. econs; eauto.
        }
        { ss. }
        i. des; ss.
        unfold Thread.steps_failure in *. des. destruct e2, e3. esplits; [..|eauto].
        { eapply rtc_internal_step_bind; eauto. }
        { eapply step_bind; eauto. }
    }
    { ii. exploit CAP; eauto. i. des. esplits; eauto.
      i. exploit CAP0; eauto. i. des. esplits; eauto.
      eapply rclo14_clo_base. econs; eauto.
      eapply _sim_ktree_mon; [|eauto]. auto.
    }
  - (* tau iter *)
    red. red. split.
    { ii.
      splits; s; ii.
      { inv TERMINAL_TGT. eapply f_equal with (f:=observe) in H. ss. }
      { right. subst. esplits; eauto. eapply sim_local_memory_bot; eauto. }
      assert (VIEWSLE0: views_le views1 views2).
      { eapply JThread.step_future; eauto. }
      right. inv STEP_TGT. inv STEP; ss.
      + (* promise *)
        inv STEP0; ss.
        exploit sim_local_promise; try apply MEMORY; eauto.
        { eapply sim_future_memory_sc_future in FUTURE; eauto.
          2:{ typeclasses eauto. (* why? *) }
          des. eapply sim_local_mon; eauto. }
        { i. subst. eapply PROMISE; eauto. }
        i. des.
        esplits; try apply MEM2; eauto; ss.
        { econs 2. econs 1. econs; eauto. }
        { eauto. }
        { eapply sim_timemap_mon; eauto. }
        { eapply rclo14_clo_base. eapply ctx_tau_iter; eauto.
          eapply _sim_ktree_mon; cycle 1; eauto.
        }
      + (* tau *)
        inv STEP0. ss. inv LOCAL0; dependent destruction STATE.
        esplits; eauto; ss.
        { econs 2. econs 2. econs; [|econs 1]; eauto. econs; eauto. }
        { eapply sim_memory_mon; eauto. }
        { rewrite unfold_iter_eq. rewrite unfold_iter_eq.
          eapply rclo14_clo. eapply ctx_bind; eauto.
          { eapply sim_future_memory_sc_future in FUTURE; eauto.
            2:{ typeclasses eauto. (* why? *) }
            des. eapply rclo14_base. eapply LE. eapply SIM; eauto.
            eapply sim_local_mon; eauto. etrans; eauto.
          }
          ii. eapply rclo14_clo. inv RET.
          { eapply ctx_tau_iter; eauto.
            eapply _sim_ktree_mon; cycle 1; eauto.
            i. eapply rclo14_base. eauto. }
          { eapply ctx_ret; eauto. }
        }
        { refl. }
    }
    { ii. subst. hexploit sim_cap; eauto.
      i. des. esplits; eauto.
      i. hexploit CAP; eauto. i. des. esplits; eauto.
      eapply rclo14_clo. econs 3; eauto.
      eapply _sim_ktree_mon; [|eauto]. i. eapply rclo14_base. auto.
    }
Qed.

Inductive iter_ctx (sim_thread:SIM_THREAD world): SIM_THREAD world :=
| ctx_iter
    I_src I_tgt R_src R_tgt b w0 views fin
    (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
    sc0_src mem0_src
    sc0_tgt mem0_tgt
    lc_src lc_tgt
    (body_src: I_src -> itree MemE.t (I_src + R_src))
    (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
    (SIM: _sim_ktree sim_thread sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1))
    i_src i_tgt
    (VAL: sim_ret0 i_src i_tgt)
    (LOCAL: sim_local w0 views lc_src lc_tgt)
  :
    @iter_ctx sim_thread
              (lang R_src) (lang R_tgt)
              (sim_terminal sim_ret1)
              b w0
              (ITree.iter body_src i_src) lc_src sc0_src mem0_src
              (ITree.iter body_tgt i_tgt) lc_tgt sc0_tgt mem0_tgt
              (views, fin)
.

Lemma iter_ctx_mon: monotone14 iter_ctx.
Proof.
  ii. destruct IN.
  econs; eauto. ii. eapply LE. eapply SIM; eauto.
Qed.
Hint Resolve iter_ctx_mon.

Lemma iter_ctx_compat:
  iter_ctx <15= gupaco14 _sim_thread (cpn14 _sim_thread).
Proof.
  assert (MON: monotone14 _sim_thread).
  (* paco tactics do not work well without this *)
  { eapply _sim_thread_mon; eauto. }
  eapply grespect14_uclo; auto.
  econs; auto. i. destruct PR.
  eapply rclo14_clo_base. eapply cpn14_gupaco; [eauto with paco|].
  rewrite unfold_iter_eq. rewrite unfold_iter_eq.
  guclo ctx_compat. eapply ctx_bind.
  { gbase. eapply _sim_thread_mon.
    { eapply GF. eapply (@SIM i_src i_tgt); eauto. }
    { i. eapply rclo14_base. eauto. }
  }
  { ii. inv RET.
    { guclo ctx_compat. eapply ctx_tau_iter; eauto.
      eapply _sim_ktree_mon; cycle 1; eauto.
      i. gbase. eapply _sim_thread_mon; eauto.
      i. eapply rclo14_base. eauto.
    }
    { guclo ctx_compat. eapply ctx_ret; eauto. }
  }
Qed.

Definition sim_itree := @_sim_itree (sim_thread world_messages_le sim_memory sim_timemap sim_local).
Definition sim_ktree := @_sim_ktree (sim_thread world_messages_le sim_memory sim_timemap sim_local).

Lemma sim_itree_mon R_src R_tgt
      sim_ret0 sim_ret1
      itr_src itr_tgt
      (SIM01: sim_ret0 <2= sim_ret1)
      (SIM: @sim_itree R_src R_tgt sim_ret0 itr_src itr_tgt):
  sim_itree sim_ret1 itr_src itr_tgt.
Proof.
  ii. eapply sim_thread_mon; [|eauto].
  i. inv PR. econs; eauto.
Qed.

Lemma sim_itree_ret R_src R_tgt (sim_ret: SIM_VAL R_src R_tgt)
      r_src r_tgt
      (SIM: sim_ret r_src r_tgt):
  @sim_itree R_src R_tgt sim_ret (Ret r_src) (Ret r_tgt).
Proof.
  ii. ginit. guclo ctx_compat. econs 1; eauto.
Qed.

Lemma sim_itree_bind
      R_src0 R_tgt0 R_src1 R_tgt1
      (sim_ret0: SIM_VAL R_src0 R_tgt0)
      (sim_ret1: SIM_VAL R_src1 R_tgt1)
      itr_src itr_tgt k_src k_tgt
      (SIM1: sim_itree sim_ret0 itr_src itr_tgt)
      (SIM2: sim_ktree sim_ret0 k_src k_tgt sim_ret1):
  sim_itree sim_ret1 (itr_src >>= k_src) (itr_tgt >>= k_tgt).
Proof.
  ii. ginit. guclo ctx_compat. econs 2.
  - gfinal. right. apply SIM1; auto.
  - ii. gfinal. right. eapply SIM2; auto.
Qed.

Lemma sim_itree_iter
      I_src I_tgt R_src R_tgt
      (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
      (body_src: I_src -> itree MemE.t (I_src + R_src))
      (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
      (SIM: sim_ktree sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1))
      i_src i_tgt
      (VAL: sim_ret0 i_src i_tgt):
  sim_itree sim_ret1 (ITree.iter body_src i_src) (ITree.iter body_tgt i_tgt).
Proof.
  ii. ginit. guclo iter_ctx_compat. econs; eauto.
  eapply _sim_ktree_mon; cycle 1; eauto.
  ii. gfinal. right. eauto.
Qed.


Lemma sim_ktree_ret R_src R_tgt sim_ret:
  @sim_ktree R_src R_tgt R_src R_tgt sim_ret (fun r => Ret r) (fun r => Ret r) sim_ret.
Proof.
  ii. ginit. guclo ctx_compat. econs 1; eauto.
Qed.

Lemma sim_ktree_bind
      R_src0 R_tgt0 R_src1 R_tgt1 R_src2 R_tgt2
      (sim_ret0: SIM_VAL R_src0 R_tgt0)
      (sim_ret1: SIM_VAL R_src1 R_tgt1)
      (sim_ret2: SIM_VAL R_src2 R_tgt2)
      k1_src k2_src
      k1_tgt k2_tgt
      (SIM1: sim_ktree sim_ret0 k1_src k1_tgt sim_ret1)
      (SIM2: sim_ktree sim_ret1 k2_src k2_tgt sim_ret2):
  sim_ktree sim_ret0 (fun r => k1_src r >>= k2_src) (fun r => k1_tgt r >>= k2_tgt) sim_ret2.
Proof.
  ii. ginit. guclo ctx_compat. econs 2.
  - gfinal. right. eapply SIM1; auto.
  - ii. gfinal. right. eapply SIM2; auto.
Qed.

Lemma sim_ktree_iter
      I_src I_tgt R_src R_tgt
      (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
      (body_src: I_src -> itree MemE.t (I_src + R_src))
      (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
      (SIM: sim_ktree sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1)):
  sim_ktree sim_ret0 (ITree.iter body_src) (ITree.iter body_tgt) sim_ret1.
Proof.
  ii. ginit. guclo iter_ctx_compat. econs; eauto.
  eapply _sim_ktree_mon; cycle 1; eauto.
  ii. gfinal. right. eauto.
Qed.
