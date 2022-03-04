From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Configuration.
Require Import Behavior.

Require Import ITreeLang.
Require Import MemoryProps.
Require Import NoMix.
Require Import DelayedSimulation.
Require Import DelayedStep.
Require Import DelayedAdequacy.
Require Import NALoc.
Require Import SeqLiftSim.
Require Import Simple.
Require Import SeqCompatibility.

Set Implicit Arguments.


Section ADEQUACY.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.
  Hypothesis LOCDISJOINT: forall loc (NA: loc_na loc) (AT: loc_at loc), False.

  Theorem sequential_adequacy (progs_src progs_tgt: Threads.syntax)
          (SIM: forall tid,
              option_rel
                (fun '(existT _ lang_src prog_src) '(existT _ lang_tgt prog_tgt) =>
                   exists sim_ret, @sim_seq_all
                                     _ _ sim_ret
                                     (lang_src.(Language.init) prog_src)
                                     (lang_tgt.(Language.init) prog_tgt))
                (IdentMap.find tid progs_src)
                (IdentMap.find tid progs_tgt))
          (NOMIX_SRC: nomix_syntax loc_na loc_at progs_src)
          (NOMIX_TGT: nomix_syntax loc_na loc_at progs_tgt)
    :
      behaviors
        Configuration.step
        (Configuration.init progs_tgt)
      <2=
      behaviors
        Configuration.step
        (Configuration.init progs_src).
  Proof.
    i. eapply DelayedAdequacy.sim_init.
    { eapply SeqLiftSim.world_messages_le_PreOrder. }
    { eapply SeqLiftSim.world_messages_le_mon. }
    { i. specialize (SIM tid). unfold option_rel in *. des_ifs.
      { rewrite Heq1 in Heq0. dependent destruction Heq0.
        des. eapply SeqLiftSim.sim_lift_init; eauto.
      }
      { clarify. }
      { clarify. }
    }
    { eapply SeqLiftSim.initial_sim_memory_lift. }
    { eapply SeqLiftSim.initial_sim_timemap_lift. }
    eapply NALoc.sim_configuration_init; eauto.
    eapply DConfiguration.delayed_refinement; eauto.
    { eapply Configuration.init_wf. }
  Qed.

  Theorem sequential_adequacy_concurrent_context
          (ctx: Threads.syntax) (tid: Ident.t)
          (lang_src: language) (prog_src: lang_src.(Language.syntax))
          (lang_tgt: language) (prog_tgt: lang_tgt.(Language.syntax))
          (SIM: exists sim_ret, @sim_seq_all
                                  _ _ sim_ret
                                  (lang_src.(Language.init) prog_src)
                                  (lang_tgt.(Language.init) prog_tgt))
          (NOMIX_SRC: nomix loc_na loc_at _ (lang_src.(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ (lang_tgt.(Language.init) prog_tgt))
          (NOMIX_CTX: nomix_syntax loc_na loc_at ctx)
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ lang_tgt prog_tgt) ctx))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ lang_src prog_src) ctx)).
  Proof.
    eapply sequential_adequacy.
    { i. rewrite ! IdentMap.gsspec. des_ifs; ss.
      destruct (IdentMap.find tid0 ctx) as [[lang prog]|]; ss.
      esplits. eapply sim_seq_all_refl.
    }
    { ii. rewrite IdentMap.gsspec in FIND. des_ifs; eauto.
      dependent destruction H0. auto.
    }
    { ii. rewrite IdentMap.gsspec in FIND. des_ifs; eauto.
      dependent destruction H0. auto.
    }
  Qed.

  Inductive itree_context A: forall B, (itree MemE.t A -> itree MemE.t B) -> Prop :=
  | itree_context_id
    :
      @itree_context A A id
  | itree_context_constant
      B (c: itree MemE.t B)
      (NOMIX: nomix loc_na loc_at (@lang B) c)
    :
      @itree_context A B (fun _ => c)
  | itree_context_bind
      B C
      (f: itree MemE.t A -> itree MemE.t B)
      (g: B -> (itree MemE.t A -> itree MemE.t C))
      (CTX_F: @itree_context A B f)
      (CTX_G: forall b, @itree_context A C (g b))
    :
      @itree_context A C (fun itr => b <- (f itr);; g b itr)
  | itree_context_iter
      R I
      (body: I -> itree MemE.t A -> itree MemE.t (I + R))
      (CTX_BODY: forall i, @itree_context A (I + R) (body i))
      i
    :
      @itree_context A R (fun itr => ITree.iter (fun i0 => body i0 itr) i)
  .

  Lemma itree_nomix_spin A
    :
    nomix loc_na loc_at (@lang A) ITree.spin.
  Proof.
    pcofix CIH. pfold. ii. rewrite unfold_spin in STEP. inv STEP.
    splits; ss. right. auto.
  Qed.

  Variant itree_nomix_bind_clo (r: forall lang, lang.(Language.state) -> Prop)
    : forall lang, lang.(Language.state) -> Prop :=
  | itree_nomix_bind_clo_intro
      A B itr ktr
      (NOMIX0: r (@lang A) itr)
      (NOMIX1: forall a, r (@lang B) (ktr a))
    :
    itree_nomix_bind_clo r (@lang B) (itr >>= ktr)
  .

  Lemma itree_nomix_bind_clo_uclo
    :
    itree_nomix_bind_clo <3= gupaco2 (_nomix loc_na loc_at) (cpn2 (_nomix loc_na loc_at)).
  Proof.
    eapply grespect2_uclo; auto with paco. econs.
    { ii. dependent destruction IN. econs; eauto. }
    { i. dependent destruction PR. eapply rclo2_base. ii.
      dup STEP. eapply lang_step_deseq in STEP. des; clarify.
      { specialize (NOMIX1 r0). eapply GF in NOMIX1.
        exploit NOMIX1; eauto. i. des. splits; auto. eapply rclo2_base; auto.
      }
      { eapply GF in NOMIX0. exploit NOMIX0; eauto.
        i. des. splits; auto. eapply rclo2_clo. left. econs; eauto.
        { eapply rclo2_base; auto. }
        { i. eapply rclo2_base. auto. }
      }
      { splits; ss. inv STEP0. eapply rclo2_clo. right.
        gfinal. right. eapply paco2_mon; [eapply itree_nomix_spin|]; ss.
      }
    }
  Qed.

  Lemma itree_nomix_bind A B
        (itr: itree MemE.t A) (ktr: A -> itree MemE.t B)
        (NOMIX0: nomix loc_na loc_at (@lang A) itr)
        (NOMIX1: forall a, nomix loc_na loc_at (@lang B) (ktr a))
    :
      nomix loc_na loc_at (@lang B) (itr >>= ktr).
  Proof.
    ginit. guclo itree_nomix_bind_clo_uclo. econs; eauto.
    { gfinal. right. eapply NOMIX0. }
    { i. gfinal. right. eapply NOMIX1. }
  Qed.

  Lemma itree_nomix_iter I R
        (body: I -> itree MemE.t (I + R))
        (NOMIX: forall i, nomix loc_na loc_at (@lang (I + R)) (body i))
        i
    :
      nomix loc_na loc_at (@lang R) (ITree.iter body i).
  Proof.
    ginit. revert i. gcofix CIH. i. gstep. ii.
    dup STEP. rewrite unfold_iter_eq in STEP.
    eapply lang_step_deseq in STEP. des; clarify.
    { destruct r0; inv STEP1. splits; ss.
      gbase. eauto.
    }
    { specialize (NOMIX i). punfold NOMIX. exploit NOMIX; eauto.
      i. des. inv CONT; ss. splits; auto.
      guclo itree_nomix_bind_clo_uclo. econs; eauto.
      { gfinal. right. eapply paco2_mon; eauto. ss. }
      { i. destruct a.
        { gstep. ii. inv STEP. splits; ss. gfinal. auto. }
        { gstep. ii. inv STEP. }
      }
    }
    { splits; ss. inv STEP0.
      gfinal. right. eapply paco2_mon; [eapply itree_nomix_spin|]; ss.
    }
  Qed.

  Lemma itree_nomix_context A B itr ctx
        (CTX: itree_context ctx)
        (NOMIX: nomix loc_na loc_at (@lang A) itr)
    :
      nomix loc_na loc_at (@lang B) (ctx itr).
  Proof.
    induction CTX; i; auto.
    { eapply itree_nomix_bind; eauto. }
    { eapply itree_nomix_iter; eauto. }
  Qed.

  Lemma itree_sim_seq_context A B itr_src itr_tgt
        (ctx: itree MemE.t A -> itree MemE.t B)
        (CTX: itree_context ctx)
        (SIM: sim_seq_itree eq itr_src itr_tgt)
    :
    sim_seq_itree eq (ctx itr_src) (ctx itr_tgt).
  Proof.
    induction CTX.
    { auto. }
    { eapply sim_seq_itree_refl. }
    { eapply sim_seq_itree_bind.
      { eauto. }
      { red. red. i. subst. eapply H. }
    }
    { eapply sim_seq_itree_iter.
      { instantiate (1:=eq). red. red. i. subst.
        specialize (H r_tgt). eapply sim_seq_itree_mon in H; eauto.
        i. subst. destruct x1; ss; eauto.
      }
      { auto. }
    }
  Qed.

  Theorem sequential_adequacy_context A B
          (prog_src prog_tgt: (lang A).(Language.syntax))
          (SIM: sim_seq_itree eq prog_src prog_tgt)
          (ctx_seq: itree MemE.t A -> itree MemE.t B)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context A B ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang A).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang A).(Language.init) prog_tgt))
          (NOMIX_CTX: nomix_syntax loc_na loc_at ctx_ths)
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang B) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang B) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_concurrent_context; auto.
    { esplits. hexploit itree_sim_seq_context; eauto. ii. eapply H. }
    { clear NOMIX_TGT. exploit itree_nomix_context; eauto. }
    { clear NOMIX_SRC. exploit itree_nomix_context; eauto. }
  Qed.

  Require Import WRforwarding.
  Require Import WRforwardingProof2.

  Theorem WRforwarding_sound A
          (code: ITreeLang.block)
          (prog_src prog_tgt: (lang Const.t).(Language.syntax))
          (PROG_SRC: prog_src = eval_lang code)
          (PROG_TGT: prog_tgt = eval_lang (WRfwd_opt_alg code))
          (ctx_seq: itree MemE.t Const.t -> itree MemE.t A)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context Const.t A ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang Const.t).(Language.init) prog_tgt))
          (NOMIX_CTX: nomix_syntax loc_na loc_at ctx_ths)
    :
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_tgt)) ctx_ths))
      <2=
      behaviors
        Configuration.step
        (Configuration.init (IdentMap.add tid (existT _ (lang A) (ctx_seq prog_src)) ctx_ths)).
  Proof.
    eapply sequential_adequacy_context; eauto.

    hexploit WRforwardingProof2.WRfwd_sim; ss. i.

    unfold sim_seq_itree.
    unfold Simple.sim_seq_itree in H.
    unfold sim_seq_all in H.
    unfold _sim_itree.

Simple.sim_seq_itree in H.


  Qed.
subst. ii. eapply WRforwardingProof2.WRfwd_sim; ss.
  Qed.
x

i.
    ii. eapply H; eauto.

exploit H; eauto. i.

eapply H.

ii. eapply H.

sim_seq_itree

    i.




eval_lang

WRfwd_opt_alg

  Proof.
    eapply sequential_adequacy_concurrent_context; auto.
    { esplits. hexploit itree_sim_seq_context; eauto. ii. eapply H. }
    { clear NOMIX_TGT. exploit itree_nomix_context; eauto. }
    { clear NOMIX_SRC. exploit itree_nomix_context; eauto. }
  Qed.


End ADEQUACY.
