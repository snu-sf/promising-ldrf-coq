From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
Require Import Configuration.
Require Import Behavior.

Require Import NoMix.
Require Import DelayedSimulation.
Require Import DelayedStep.
Require Import DelayedAdequacy.
Require Import NALoc.
Require Import SeqLiftSim.
Require Import Sequential.
Require Import Program.

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
          (NOMIX_SRC:
             forall tid lang syn
                    (FIND: IdentMap.find tid progs_src = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
          (NOMIX_TGT:
             forall tid lang syn
                    (FIND: IdentMap.find tid progs_tgt = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
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
          (NOMIX_CTX:
             forall tid lang syn
                    (FIND: IdentMap.find tid ctx = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
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
End ADEQUACY.
