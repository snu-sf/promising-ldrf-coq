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

  Theorem sequential_adequcy_context (ctx: Threads.syntax) (tid: Ident.t)
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
  | itree_context_itre
      R I
      (body: I -> itree MemE.t A -> itree MemE.t (I + R))
      (CTX_BODY: forall i, @itree_context A (I + R) (body i))
      i
    :
      @itree_context A R (fun itr => ITree.iter (fun i0 => body i0 itr) i)
  .

  Lemma nomix_bind A B
        (itr: itree MemE.t A) (ktr: A -> itree MemE.t B)
        (NOMIX0: nomix loc_na loc_at (@lang A) itr)
        (NOMIX1: forall a, nomix loc_na loc_at (@lang B) (ktr a))
    :
      nomix loc_na loc_at (@lang B) (itr >>= ktr).
  Proof.
    revert itr ktr NOMIX0 NOMIX1. pcofix CIH. i. pfold. ii.
    eapply lang_step_deseq in STEP. des.
    { admit. }
  Admitted.

  Lemma itree_context_nomix A B itr ctx
        (CTX: itree_context ctx)
        (NOMIX: nomix loc_na loc_at (@lang A) itr)
    :
      nomix loc_na loc_at (@lang B) (ctx itr).
  Admitted.
End ADEQUACY.
