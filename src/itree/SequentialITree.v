From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
From ExtLib Require Export
     Data.String
     Data.Map.FMapAList
     Functor FunctorLaws
     Structures.Maps
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import List.
Require Import String.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.
Require Export ITreeLib.

Require Import Sequential.
Require Import FlagAux.
Require Import ITreeLang.



Definition SIM_VAL R_src R_tgt := forall (r_src:R_src) (r_tgt:R_tgt), Prop.

Definition SIM_TERMINAL (lang_src lang_tgt:language) :=
  forall (st_src:(Language.state lang_src)) (st_tgt:(Language.state lang_tgt)), Prop.

Variant sim_terminal R_src R_tgt
           (sim_ret:SIM_VAL R_src R_tgt)
           (st_src: itree MemE.t R_src) (st_tgt: itree MemE.t R_tgt): Prop :=
| sim_terminal_intro
    r0 r1
    (SIMRET: sim_ret r0 r1)
    (SRC: st_src = Ret r0)
    (TGT: st_tgt = Ret r1)
.

Definition SIM_SEQ :=
  forall (lang_src lang_tgt:language) (sim_terminal: SIM_TERMINAL lang_src lang_tgt)
         (p0: Perms.t) (d0: Flags.t)
         (st_src0: SeqState.t lang_src)
         (st_tgt0: SeqState.t lang_tgt), Prop.

Definition _sim_itree
           (sim_seq:SIM_SEQ)
           R_src R_tgt
           (sim_ret:SIM_VAL R_src R_tgt)
           (itr_src: itree MemE.t R_src) (itr_tgt: itree MemE.t R_tgt): Prop :=
  forall mem p,
    @sim_seq (lang R_src) (lang R_tgt) (sim_terminal sim_ret)
             p Flags.bot
             (@SeqState.mk (lang R_src) itr_src mem)
             (@SeqState.mk (lang R_tgt) itr_tgt mem).

Definition _sim_ktree
           (sim_seq:SIM_SEQ)
           R_src0 R_tgt0 R_src1 R_tgt1
           (sim_ret0:SIM_VAL R_src0 R_tgt0)
           (ktr_src: R_src0 -> itree MemE.t R_src1)
           (ktr_tgt: R_tgt0 -> itree MemE.t R_tgt1)
           (sim_ret1:SIM_VAL R_src1 R_tgt1): Prop :=
  forall r_src r_tgt
         (RET: sim_ret0 r_src r_tgt),
    _sim_itree sim_seq sim_ret1 (ktr_src r_src) (ktr_tgt r_tgt).

Lemma _sim_itree_mon
      s1 s2 (S: s1 <7= s2):
  @_sim_itree s1 <5= @_sim_itree s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Lemma _sim_ktree_mon
      s1 s2 (S: s1 <7= s2):
  @_sim_ktree s1 <8= @_sim_ktree s2.
Proof.
  ii. apply S. apply PR; auto.
Qed.

Definition sim_seq_itree := @_sim_itree sim_seq.
Definition sim_seq_ktree := @_sim_ktree sim_seq.

Arguments sim_seq_itree [_ _] _ _ _.
Arguments sim_seq_ktree [_ _ _ _] _ _ _ _.

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

Lemma na_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1)
      mem1 mem2 p e
      (STEP: SeqState.na_step
               p e
               (@SeqState.mk (lang R0) itr0 mem1)
               (@SeqState.mk (lang R0) itr1 mem2)):
  SeqState.na_step
    p e
    (@SeqState.mk (lang R1) (itr0 >>= k) mem1)
    (@SeqState.mk (lang R1) (itr1 >>= k) mem2).
Proof.
  inv STEP. econs; eauto.
  apply lang_step_bind. auto.
Qed.

Lemma na_opt_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1)
      mem1 mem2 p e
      (STEP: SeqState.na_opt_step
               p e
               (@SeqState.mk (lang R0) itr0 mem1)
               (@SeqState.mk (lang R0) itr1 mem2)):
  SeqState.na_opt_step
    p e
    (@SeqState.mk (lang R1) (itr0 >>= k) mem1)
    (@SeqState.mk (lang R1) (itr1 >>= k) mem2).
Proof.
  inv STEP.
  { econs 1; eauto. eapply na_step_bind; eauto. }
  { econs 2; eauto. }
Qed.

Lemma rtc_na_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1)
      mem1 mem2 p
      (STEP: rtc (SeqState.na_step p MachineEvent.silent)
                 (@SeqState.mk (lang R0) itr0 mem1)
                 (@SeqState.mk (lang R0) itr1 mem2)):
  rtc (SeqState.na_step p MachineEvent.silent)
      (@SeqState.mk (lang R1) (itr0 >>= k) mem1)
      (@SeqState.mk (lang R1) (itr1 >>= k) mem2).
Proof.
  remember (@SeqState.mk (lang R0) itr0 mem1).
  remember (@SeqState.mk (lang R0) itr1 mem2).
  revert itr0 itr1 mem1 mem2 Heqt Heqt0.
  induction STEP; i; clarify.
  { econs. }
  { destruct y. econs.
    { eapply na_step_bind; eauto. }
    { eapply IHSTEP; eauto. }
  }
Qed.

Lemma seq_thread_steps_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1)
      mem0 mem1 p0 p1 o0 o1 tr
      (STEPS: SeqThread.steps
                (@SeqState.na_step _) tr
                (SeqThread.mk (@SeqState.mk (lang R0) itr0 mem0) p0 o0)
                (SeqThread.mk (@SeqState.mk (lang R0) itr1 mem1) p1 o1))
  :
    SeqThread.steps
      (@SeqState.na_step _) tr
      (@SeqThread.mk (lang R1) (@SeqState.mk (lang R1) (itr0 >>= k) mem0) p0 o0)
      (@SeqThread.mk (lang R1) (@SeqState.mk (lang R1) (itr1 >>= k) mem1) p1 o1).
Proof.
  remember (SeqThread.mk (@SeqState.mk (lang R0) itr0 mem0) p0 o0).
  remember (SeqThread.mk (@SeqState.mk (lang R0) itr1 mem1) p1 o1).
  revert itr0 itr1 mem0 mem1 p0 p1 o0 o1 Heqt Heqt0.
  induction STEPS; i; clarify; ss.
  { econs 1. }
  { inv STEP. destruct st1. econs 2.
    { econs. eapply na_step_bind; eauto. }
    { eapply IHSTEPS; eauto. }
  }
  { inv STEP. econs 3.
    { econs; eauto. eapply lang_step_bind; eauto. }
    { eapply IHSTEPS; eauto. }
  }
Qed.

Lemma seq_thread_failure_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1)
      mem0 p0 o0
      (STEPS: SeqThread.failure
                (@SeqState.na_step _)
                (SeqThread.mk (@SeqState.mk (lang R0) itr0 mem0) p0 o0))
  :
    SeqThread.failure
      (@SeqState.na_step _)
      (@SeqThread.mk (lang R1) (@SeqState.mk (lang R1) (itr0 >>= k) mem0) p0 o0).
Proof.
  unfold SeqThread.failure in *. des. inv FAILURE. destruct st1.
  esplits. econs. eapply na_step_bind; eauto.
Qed.
