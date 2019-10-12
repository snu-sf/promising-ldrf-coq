Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
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

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import PromotionDef.
Require Import SimCommon.
Require Import SimThreadPromotion.
Require Import SimThreadOther.
Require Import PSimulation.

Set Implicit Arguments.


Module Promotion.
  Inductive sim_conf (p: Ident.t) (l: Loc.t) (r: Reg.t) (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (TIDS: Threads.tids c_src.(Configuration.threads) = Threads.tids c_tgt.(Configuration.threads))
      (FIND_SRC: forall tid lang_src st_src lc_src
                   (FIND: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang_src st_src, lc_src)),
          lang_src = lang)
      (FIND_TGT: forall tid lang_tgt st_tgt lc_tgt
                   (FIND: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang_tgt st_tgt, lc_tgt)),
          lang_tgt = lang)
      (PROMOTION: forall st_src lc_src st_tgt lc_tgt
                    (FIND_SRC: IdentMap.find p c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
                    (FIND_TGT: IdentMap.find p c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)),
          <<SIM_THREAD: SimThreadPromotion.sim_thread_reserve
                          l r
                          (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
                          (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory))>>)
      (OTHER: forall tid st_src lc_src st_tgt lc_tgt
                (TID: tid <> p)
                (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
                (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)),
          <<SIM_THREAD: SimThreadOther.sim_thread
                          l
                          (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
                          (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory))>>)
  .
  Hint Constructors sim_conf.


  (* TODO: move to Configuration.v *)
  Lemma tids_find
        ths_src ths_tgt tid
        (TIDS: Threads.tids ths_src = Threads.tids ths_tgt):
    (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    split; i; des.
    - destruct (IdentSet.mem tid (Threads.tids ths_src)) eqn:MEM.
      + rewrite TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
    - destruct (IdentSet.mem tid (Threads.tids ths_tgt)) eqn:MEM.
      + rewrite <- TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
  Qed.

  Lemma sim_conf_find
        p l r c_src c_tgt tid
        (SIM: sim_conf p l r c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread_promotion
        p l r c_src c_tgt
        st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf p l r c_src c_tgt)
        (FIND_SRC: IdentMap.find p c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find p c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)):
    SimThreadPromotion.sim_thread_reserve
      l r
      (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
      (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory)).
  Proof.
    inv SIM. exploit PROMOTION; eauto.
  Qed.

  Lemma sim_conf_sim_thread_other
        p l r c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf p l r c_src c_tgt)
        (TID: tid <> p)
        (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)):
    SimThreadOther.sim_thread
      l
      (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
      (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory)).
  Proof.
    inv SIM. exploit OTHER; eauto.
  Qed.

  Theorem sim_conf_sim
          p l r c_src c_tgt
          (SIM: sim_conf p l r c_src c_tgt):
    sim c_src c_tgt.
  Proof.
  Admitted.
End Promotion.