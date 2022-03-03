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
Require Export Program.

Require Import Simple.
Require Import FlagAux.
Require Import ITreeLang.

Require Import SimAux.
Require Import SeqAux.


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


Global Hint Resolve cpn7_wcompat: paco.

Inductive ctx (sim_seq:SIM_SEQ): SIM_SEQ :=
| ctx_ret
    R_src R_tgt
    (sim_ret:SIM_VAL R_src R_tgt)
    mem_src mem_tgt p
    (r_src: R_src) (r_tgt: R_tgt)
    (RET: sim_ret r_src r_tgt)
    (VAL: ValueMap.le mem_tgt.(SeqMemory.value_map) mem_src.(SeqMemory.value_map))
    (FLAG: Flags.le mem_tgt.(SeqMemory.flags) mem_src.(SeqMemory.flags)):
    @ctx sim_seq
         (lang R_src) (lang R_tgt)
         (sim_terminal sim_ret)
         p Flags.bot
         (@SeqState.mk (lang R_src) (Ret r_src) mem_src)
         (@SeqState.mk (lang R_tgt) (Ret r_tgt) mem_tgt)
| ctx_bind
    R_src0 R_tgt0 R_src1 R_tgt1
    (sim_ret1:SIM_VAL R_src0 R_tgt0) (sim_ret2:SIM_VAL R_src1 R_tgt1)
    p f
    itr_src ktr_src mem_src
    itr_tgt ktr_tgt mem_tgt
    (SIM1: sim_seq (lang R_src0) (lang R_tgt0) (sim_terminal sim_ret1)
                   p f
                   (@SeqState.mk (lang R_src0) itr_src mem_src)
                   (@SeqState.mk (lang R_tgt0) itr_tgt mem_tgt))
    (SIM2: _sim_ktree sim_seq sim_ret1 ktr_src ktr_tgt sim_ret2):
    @ctx sim_seq
         (lang R_src1) (lang R_tgt1)
         (sim_terminal sim_ret2)
         p f
         (@SeqState.mk (lang R_src1) (itr_src >>= ktr_src) mem_src)
         (@SeqState.mk (lang R_tgt1) (itr_tgt >>= ktr_tgt) mem_tgt)
| ctx_tau_iter
    I_src I_tgt R_src R_tgt
    (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
    p
    mem_src mem_tgt
    (body_src: I_src -> itree MemE.t (I_src + R_src))
    (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
    (SIM: _sim_ktree sim_seq sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1))
    i_src i_tgt
    (VAL: sim_ret0 i_src i_tgt)
    (VALS: ValueMap.le mem_tgt.(SeqMemory.value_map) mem_src.(SeqMemory.value_map))
    (FLAG: Flags.le mem_tgt.(SeqMemory.flags) mem_src.(SeqMemory.flags))
  :
    @ctx sim_seq
         (lang R_src) (lang R_tgt)
         (sim_terminal sim_ret1)
         p Flags.bot
         (@SeqState.mk (lang _) (tau;;(ITree.iter body_src i_src)) mem_src)
         (@SeqState.mk (lang _) (tau;;(ITree.iter body_tgt i_tgt)) mem_tgt)
.

Lemma ctx_mon: monotone7 ctx.
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


Inductive ctx_src_steps (sim_seq:SIM_SEQ): SIM_SEQ :=
| ctx_src_steps_intro
    lang_src lang_tgt sim_terminal
    th_src0 th_src1 th_tgt p f
    (STEPS: rtc (SeqState.na_step p MachineEvent.silent) th_src0 th_src1)
    (SIM: @sim_seq lang_src lang_tgt sim_terminal p f th_src1 th_tgt)
  :
    @ctx_src_steps
      sim_seq
      lang_src lang_tgt
      sim_terminal
      p f
      th_src0
      th_tgt
.

Lemma ctx_src_mon: monotone7 ctx_src_steps.
Proof.
  ii. destruct IN. econs; eauto.
Qed.
Hint Resolve ctx_src_mon.

Lemma na_steps_thread_steps lang th_src0 th_src1 th_src2 tr p0 o0
      (STEPS0: rtc (SeqState.na_step p0 MachineEvent.silent) th_src0 th_src1)
      (STEPS1: SeqThread.steps (@SeqState.na_step lang) tr
                               (@SeqThread.mk lang th_src1 p0 o0) th_src2)
  :
    SeqThread.steps (@SeqState.na_step lang) tr (@SeqThread.mk lang th_src0 p0 o0) th_src2.
Proof.
  induction STEPS0; auto. econs 2.
  { econs; eauto. }
  { eauto. }
Qed.

Lemma ctx_src_steps_compat:
  ctx_src_steps <8= gupaco7 _sim_seq (cpn7 _sim_seq).
Proof.
  assert (MON: monotone7 _sim_seq).
  (* paco tactics do not work well without this *)
  { eapply sim_seq_mon; eauto. }
  eapply grespect7_uclo; auto.
  econs; auto. i. destruct PR. eapply rclo7_base.
  eapply GF in SIM. inv SIM.
  { econs 1.
    { ii. exploit TERMINAL; eauto. i. des. esplits.
      { etrans; eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
      { eauto. }
    }
    { ii. exploit NASTEP; eauto. i. des. esplits.
      { etrans; eauto. }
      { eauto. }
      { eapply rclo7_base. auto. }
    }
    { ii. exploit ATSTEP; eauto. i. des. esplits.
      { etrans; eauto. }
      { eauto. }
      { eauto. }
      { i. exploit SIM; eauto. i. des. esplits; eauto.
        eapply rclo7_base; auto. }
    }
    { ii. exploit PARTIAL; eauto. i. des.
      { esplits; eauto. eapply na_steps_thread_steps; eauto. }
      { esplits; eauto. eapply na_steps_thread_steps; eauto. }
    }
  }
  { econs 2. ii. exploit FAILURE; eauto. i. des.
    esplits; eauto. eapply na_steps_thread_steps; eauto.
  }
Qed.

Lemma ctx_compat:
  ctx <8= gupaco7 _sim_seq (cpn7 _sim_seq).
Proof.
  assert (MON: monotone7 _sim_seq).
  (* paco tactics do not work well without this *)
  { eapply sim_seq_mon; eauto. }
  eapply grespect7_uclo; auto.
  econs; auto. i. destruct PR.
  - (* ret *)
    eapply rclo7_base. econs.
    { ii. ss. inv TERMINAL_TGT. clarify. esplits; ss.
      { refl. }
      { ss. econs; eauto. }
      { ss. econs; eauto. }
      { ss. }
      { ss. }
    }
    { ii. inv STEP_TGT. inv LANG. }
    { ii. inv STEP_TGT. }
    { ii. esplits; ss.
      { econs 1. }
      { econs. }
      { ss. left. eapply Flags.join_mon_r. auto. }
    }
  - (* bind *)
    destruct (classic (exists r, itr_tgt = Ret r)).
    { des; clarify. eapply GF in SIM1. inv SIM1; cycle 1.
      { eapply rclo7_base. econs 2. ii.
        exploit FAILURE; eauto. i. des.
        destruct th. destruct state0. esplits.
        { eapply seq_thread_steps_bind in STEPS; eauto. }
        { eauto. }
        { eapply seq_thread_failure_bind; eauto. }
      }
      exploit TERMINAL; eauto.
      { econs; eauto; ss. }
      i. des. eapply rclo7_clo.
      eapply cpn7_gupaco; eauto.
      destruct st_src1. ss. eapply rtc_na_step_bind in STEPS.
      guclo ctx_src_steps_compat. econs.
      { eauto. }
      inv TERMINAL0. clarify. rewrite bind_ret_l. rewrite bind_ret_l.
      guclo deferred_le_sf_ctx_spec. econs.
      { instantiate (1:=Flags.bot). ss. etrans; eauto.
        eapply Flags.join_ge_l.
      }
      guclo mem_le_ctx_spec. econs; ss; eauto.
      { instantiate (1:=SeqState.mk _ _ _). ss. red. splits; eauto.
        etrans; eauto. eapply Flags.join_ge_r.
      }
      { ss. }
      exploit SIM2; eauto. i.
      gbase. eapply rclo7_base. eapply GF in x.
      eapply sim_seq_mon; eauto.
      i. eapply rclo7_base. auto.
    }
    destruct (classic (sim_seq_failure_case p (@SeqState.mk (lang R_src1) (itr_src >>= ktr_src) mem_src))).
    { eapply rclo7_base. econs 2; eauto. }
    { eapply rclo7_base. eapply GF in SIM1. inv SIM1.
      { econs.
        { ii. inv TERMINAL_TGT; ss. exfalso.
          eapply f_equal with (f:=observe) in H1.
          ides itr_tgt; eauto.
        }
        { ii. inv STEP_TGT. apply lang_step_deseq in LANG. des; clarify.
          { exfalso. eauto. }
          { exploit NASTEP; eauto.
            { econs; eauto. }
            i. des. destruct st_src1, st_src2. esplits.
            { eapply rtc_na_step_bind; eauto. }
            { eapply na_opt_step_bind; eauto. }
            { eapply rclo7_clo. right.
              gbase. eapply rclo7_clo_base.
              { left. econs.
                { eauto. }
                { eapply _sim_ktree_mon; eauto. }
              }
            }
          }
          { exploit NASTEP; eauto.
            { econs; eauto. econs; eauto. }
            i. des. inv LOCAL. inv STEP.
            exfalso. eapply H0. ii.
            destruct st_src1, st_src2. exploit na_steps_thread_steps.
            { eauto. }
            { econs 1. }
            i. esplits.
            { eapply seq_thread_steps_bind; eauto. }
            { econs. }
            { econs. econs. eapply na_step_bind; eauto. }
          }
        }
        { ii. apply lang_step_deseq in STEP_TGT. des; clarify; ss.
          { exfalso. eauto. }
          exploit ATSTEP; eauto.
          i. des. destruct st_src1. esplits.
          { eapply rtc_na_step_bind; eauto. }
          { eapply lang_step_bind; eauto. }
          { eauto. }
          { i. exploit SIM; eauto. i. des. esplits; eauto.
            eapply rclo7_clo. right.
            gbase. eapply rclo7_clo_base.
            { left. econs.
              { eauto. }
              { eapply _sim_ktree_mon; eauto. }
            }
          }
        }
        { ii. exploit PARTIAL; eauto. i. des.
          { destruct th. destruct state0. ss. esplits; eauto.
            { eapply seq_thread_steps_bind; eauto. }
            { ss. left. auto. }
          }
          { destruct th. destruct state0. ss. esplits; eauto.
            { eapply seq_thread_steps_bind; eauto. }
            { ss. right. eapply seq_thread_failure_bind; eauto. }
          }
        }
      }
      { econs 2. ii. exploit FAILURE; eauto. i. des.
        destruct th. ss. destruct state0. esplits.
        { eapply seq_thread_steps_bind in STEPS; eauto. }
        { eauto. }
        { eapply seq_thread_failure_bind; eauto. }
      }
    }
  - (* iter *)
    eapply rclo7_base. econs.
    { ii. ss. inv TERMINAL_TGT. clarify. }
    { ii. inv STEP_TGT. inv LANG. inv LOCAL. esplits.
      { refl. }
      { econs 1. econs.
        { econs; eauto. }
        { econs. }
      }
      { eapply rclo7_clo. left.
        rewrite unfold_iter_eq. rewrite unfold_iter_eq. econs.
        { eapply rclo7_clo_base. right.
          guclo deferred_le_sf_ctx_spec. econs.
          { ss. }
          guclo mem_le_ctx_spec. econs.
          3:{ gbase. eapply LE. eapply SIM; eauto. }
          { ss. }
          { ss. }
        }
        { ii. inv RET.
          { eapply rclo7_clo_base. left. econs 3; eauto.
            { eapply _sim_ktree_mon; eauto. }
            { refl. }
            { refl. }
          }
          { eapply rclo7_clo_base. left. econs 1; eauto.
            { refl. }
            { refl. }
          }
        }
      }
    }
    { ii. inv STEP_TGT. ss. }
    { ii. esplits.
      { econs 1. }
      { econs. }
      { left. ss. }
    }
Qed.

Inductive iter_ctx (sim_seq:SIM_SEQ): SIM_SEQ :=
| ctx_iter
    I_src I_tgt R_src R_tgt
    (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
    p
    mem_src mem_tgt
    (body_src: I_src -> itree MemE.t (I_src + R_src))
    (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
    (SIM: _sim_ktree sim_seq sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1))
    i_src i_tgt
    (VAL: sim_ret0 i_src i_tgt)
    (VALS: ValueMap.le mem_tgt.(SeqMemory.value_map) mem_src.(SeqMemory.value_map))
    (FLAG: Flags.le mem_tgt.(SeqMemory.flags) mem_src.(SeqMemory.flags))
  :
    @iter_ctx sim_seq
              (lang R_src) (lang R_tgt)
              (sim_terminal sim_ret1)
              p Flags.bot
              (@SeqState.mk (lang _) ((ITree.iter body_src i_src)) mem_src)
              (@SeqState.mk (lang _) ((ITree.iter body_tgt i_tgt)) mem_tgt)
.

Lemma iter_ctx_mon: monotone7 iter_ctx.
Proof.
  ii. destruct IN.
  econs; eauto. ii. eapply LE. eapply SIM; eauto.
Qed.
Hint Resolve iter_ctx_mon.

Lemma iter_ctx_compat:
  iter_ctx <8= gupaco7 _sim_seq (cpn7 _sim_seq).
Proof.
  assert (MON: monotone7 _sim_seq).
  (* paco tactics do not work well without this *)
  { eapply sim_seq_mon; eauto. }
  eapply grespect7_uclo; auto.
  econs; auto. i. destruct PR.
  eapply rclo7_clo_base. eapply cpn7_gupaco; [eauto with paco|].
  rewrite unfold_iter_eq. rewrite unfold_iter_eq.
  guclo ctx_compat. eapply ctx_bind.
  { guclo mem_le_ctx_spec. econs.
    { instantiate (1:=SeqState.mk _ _ mem_tgt).
      red. splits; ss; eauto.
    }
    { ss. }
    gbase. eapply sim_seq_mon.
    { hexploit (@SIM i_src i_tgt); eauto. }
    { i. eapply rclo7_base. eauto. }
  }
  { ii. inv RET.
    { guclo ctx_compat. eapply ctx_tau_iter; eauto.
      { eapply _sim_ktree_mon; cycle 1; eauto.
        i. gbase. eapply sim_seq_mon; eauto.
        i. eapply rclo7_base. eauto.
      }
      { refl. }
      { refl. }
    }
    { guclo ctx_compat. eapply ctx_ret; eauto.
      { refl. }
      { refl. }
    }
  }
Qed.

Definition sim_seq_itree := @_sim_itree sim_seq.
Definition sim_seq_ktree := @_sim_ktree sim_seq.

Lemma sim_seq_ret_mon lang_src lang_tgt sim_terminal0 sim_terminal1
      p f th_src th_tgt
      (SIM01: sim_terminal0 <2= sim_terminal1)
      (SIM: @sim_seq lang_src lang_tgt sim_terminal0 p f th_src th_tgt):
  @sim_seq lang_src lang_tgt sim_terminal1 p f th_src th_tgt.
Proof.
  revert p f th_src th_tgt SIM. pcofix CIH. i.
  punfold SIM. pfold. inv SIM.
  { econs 1.
    { ii. exploit TERMINAL; eauto.
      i. des. esplits; eauto.
    }
    { ii. exploit NASTEP; eauto. i. des. esplits; eauto.
      pclearbot. right. eapply CIH; eauto.
    }
    { ii. exploit ATSTEP; eauto. i. des. esplits; eauto.
      i. exploit SIM; eauto. i. des. esplits; eauto.
      pclearbot. right. eapply CIH; eauto.
    }
    { ii. exploit PARTIAL; eauto. }
  }
  { econs 2. auto. }
Qed.

Lemma sim_seq_itree_mon R_src R_tgt
      sim_ret0 sim_ret1
      itr_src itr_tgt
      (SIM01: sim_ret0 <2= sim_ret1)
      (SIM: @sim_seq_itree R_src R_tgt sim_ret0 itr_src itr_tgt):
  sim_seq_itree sim_ret1 itr_src itr_tgt.
Proof.
  ii. eapply sim_seq_ret_mon.
  2:{ eauto. }
  i. inv PR. econs; eauto.
Qed.

Lemma sim_seq_all_refl lang (prog: lang.(Language.state) )
  :
    @sim_seq_all _ _ eq prog prog.
Proof.
  ii. generalize (@SeqState.mk lang prog m). revert p. clear prog m.
  pcofix CIH. pfold. econs.
  { ii. esplits; eauto.
    { refl. }
    { refl. }
  }
  { ii. esplits; eauto.
    { econs; eauto. }
  }
  { ii. esplits; eauto.
    { refl. }
    { i. esplits; eauto. eapply SeqEvent.input_match_bot. }
  }
  { ii. esplits; eauto.
    { econs. }
    { econs. }
    { left. ss. refl. }
  }
Qed.

Lemma sim_itree_refl R (itr: itree MemE.t R)
  :
    sim_seq_itree eq itr itr.
Proof.
  ii. generalize (@SeqState.mk (lang R) itr mem). revert p. clear itr mem.
  pcofix CIH. pfold. econs.
  { ii. inv TERMINAL_TGT. esplits; eauto.
    { econs; eauto. }
    { econs; eauto. }
    { refl. }
    { refl. }
  }
  { ii. esplits; eauto.
    { econs; eauto. }
  }
  { ii. esplits; eauto.
    { refl. }
    { i. esplits; eauto. eapply SeqEvent.input_match_bot. }
  }
  { ii. esplits; eauto.
    { econs. }
    { econs. }
    { left. ss. refl. }
  }
Qed.

Lemma sim_seq_itree_ret R_src R_tgt (sim_ret: SIM_VAL R_src R_tgt)
      r_src r_tgt
      (SIM: sim_ret r_src r_tgt):
  @sim_seq_itree R_src R_tgt sim_ret (Ret r_src) (Ret r_tgt).
Proof.
  ii. ginit. guclo ctx_compat. econs 1; eauto.
  { refl. }
  { refl. }
Qed.

Lemma sim_seq_itree_bind
      R_src0 R_tgt0 R_src1 R_tgt1
      (sim_ret0: SIM_VAL R_src0 R_tgt0)
      (sim_ret1: SIM_VAL R_src1 R_tgt1)
      itr_src itr_tgt k_src k_tgt
      (SIM1: sim_seq_itree sim_ret0 itr_src itr_tgt)
      (SIM2: sim_seq_ktree sim_ret0 k_src k_tgt sim_ret1):
  sim_seq_itree sim_ret1 (itr_src >>= k_src) (itr_tgt >>= k_tgt).
Proof.
  ii. ginit. guclo ctx_compat. econs 2.
  - gfinal. right. apply SIM1; auto.
  - ii. gfinal. right. apply SIM2; auto.
Qed.

Lemma sim_seq_itree_iter
      I_src I_tgt R_src R_tgt
      (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
      (body_src: I_src -> itree MemE.t (I_src + R_src))
      (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
      (SIM: sim_seq_ktree sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1))
      i_src i_tgt
      (VAL: sim_ret0 i_src i_tgt):
  sim_seq_itree sim_ret1 (ITree.iter body_src i_src) (ITree.iter body_tgt i_tgt).
Proof.
  ii. ginit. guclo iter_ctx_compat. econs; eauto.
  { eapply _sim_ktree_mon; cycle 1; eauto.
    ii. gfinal. right. eauto. }
  { refl. }
  { refl. }
Qed.

Lemma sim_seq_ktree_ret R_src R_tgt sim_ret:
  @sim_seq_ktree R_src R_tgt R_src R_tgt sim_ret (fun r => Ret r) (fun r => Ret r) sim_ret.
Proof.
  ii. ginit. guclo ctx_compat. econs 1; eauto.
  { refl. }
  { refl. }
Qed.

Lemma sim_seq_ktree_bind
      R_src0 R_tgt0 R_src1 R_tgt1 R_src2 R_tgt2
      (sim_ret0: SIM_VAL R_src0 R_tgt0)
      (sim_ret1: SIM_VAL R_src1 R_tgt1)
      (sim_ret2: SIM_VAL R_src2 R_tgt2)
      k1_src k2_src
      k1_tgt k2_tgt
      (SIM1: sim_seq_ktree sim_ret0 k1_src k1_tgt sim_ret1)
      (SIM2: sim_seq_ktree sim_ret1 k2_src k2_tgt sim_ret2):
  sim_seq_ktree sim_ret0 (fun r => k1_src r >>= k2_src) (fun r => k1_tgt r >>= k2_tgt) sim_ret2.
Proof.
  ii. ginit. guclo ctx_compat. econs 2.
  - gfinal. right. apply SIM1; auto.
  - ii. gfinal. right. apply SIM2; auto.
Qed.

Lemma sim_seq_ktree_iter
      I_src I_tgt R_src R_tgt
      (sim_ret0: SIM_VAL I_src I_tgt) (sim_ret1: SIM_VAL R_src R_tgt)
      (body_src: I_src -> itree MemE.t (I_src + R_src))
      (body_tgt: I_tgt -> itree MemE.t (I_tgt + R_tgt))
      (SIM: sim_seq_ktree sim_ret0 body_src body_tgt (sum_rel sim_ret0 sim_ret1)):
  sim_seq_ktree sim_ret0 (ITree.iter body_src) (ITree.iter body_tgt) sim_ret1.
Proof.
  ii. ginit. guclo iter_ctx_compat. econs; eauto.
  { eapply _sim_ktree_mon; cycle 1; eauto.
    ii. gfinal. right. eauto. }
  { refl. }
  { refl. }
Qed.

Lemma sim_seq_weak_mon: monotone7 sim_seq_weak.
Proof.
  ii. inv IN.
  { econs 1; eauto.
    { ii. exploit NASTEP; eauto. i. des. esplits; eauto. }
    { ii. exploit ATSTEP; eauto. i. des. esplits; eauto.
      i. exploit SIM; eauto. i. des. esplits; eauto.
    }
  }
  { econs 2; eauto. }
Qed.
Hint Resolve sim_seq_weak_mon.
