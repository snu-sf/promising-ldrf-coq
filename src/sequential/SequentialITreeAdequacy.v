From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

From PromisingLib Require Import Event.
Require Import Configuration.
Require Import Behavior.

Require Import ITreeLang.
Require Import NoMix.
Require Import Sequential.
Require Import SequentialITree.
Require Import SequentialCompatibility.
Require Import SequentialAdequacy.

Set Implicit Arguments.


Section ADEQUACY.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.
  Hypothesis LOCDISJOINT: forall loc (NA: loc_na loc) (AT: loc_at loc), False.

  Theorem sequential_adequacy_context A B
          (prog_src prog_tgt: (lang A).(Language.syntax))
          (SIM: sim_seq_itree eq prog_src prog_tgt)
          (ctx_seq: itree MemE.t A -> itree MemE.t B)
          (ctx_ths: Threads.syntax) (tid: Ident.t)
          (CTX: @itree_context loc_na loc_at A B ctx_seq)
          (NOMIX_SRC: nomix loc_na loc_at _ ((lang A).(Language.init) prog_src))
          (NOMIX_TGT: nomix loc_na loc_at _ ((lang A).(Language.init) prog_tgt))
          (NOMIX_CTX:
             forall tid lang syn
                    (FIND: IdentMap.find tid ctx_ths = Some (existT _ lang syn)),
               nomix loc_na loc_at lang (lang.(Language.init) syn))
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
    { eauto. }
    { esplits. hexploit itree_sim_seq_context; eauto. ii. eapply H. }
    { clear NOMIX_TGT. exploit itree_nomix_context; eauto. }
    { clear NOMIX_SRC. exploit itree_nomix_context; eauto. }
    { eauto. }
  Qed.
End ADEQUACY.
