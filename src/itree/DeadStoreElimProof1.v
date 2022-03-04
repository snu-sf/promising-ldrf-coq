Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

From PromisingLib Require Import Event.

Require Import FoldN.
Require Import Knowledge.
Require Import Opt2.

Require Import ITreeLang.

Require Import DeadStoreElim.





Global Program Instance le_PreOrder: PreOrder le.
Next Obligation.
Proof.
  eapply PreOrder_Reflexive. Unshelve.    
  apply (@MLattice.le_PreOrder ThreeML).
Qed.
Next Obligation.
Proof.
  eapply PreOrder_Transitive. Unshelve.
  apply (@MLattice.le_PreOrder ThreeML).
Qed.

Global Program Instance le_PartialOrder: PartialOrder eq le.
Next Obligation.
Proof.
  unfold relation_equivalence, relation_conjunction.
  unfold predicate_equivalence, predicate_intersection.
  unfold pointwise_lifting, pointwise_extension.
  i. split; i.
  - clarify. split; refl.
  - des. unfold flip in H0. eapply antisymmetry; eauto.
    Unshelve. auto. eapply partial_order_antisym.
    eapply (@MLattice.le_PartialOrder ThreeML).
Qed.



Section ANALYSIS.

  Lemma ord_inv1:
    forall o, (Ordering.le o Ordering.strong_relaxed) \/
         (Ordering.le Ordering.acqrel o).
  Proof. i. destruct o; auto. Qed.

  Lemma update_load_ord1:
    forall ul o l t
      (ORD: Ordering.le o Ordering.strong_relaxed),
      update_load ul o l t = (if (Loc.eqb ul l) then none else t).
  Proof. i. unfold update_load. des_ifs. Qed.

  Lemma update_load_ord1f:
    forall ul o mp
      (ORD: Ordering.le o Ordering.strong_relaxed),
      (fun p0: Loc.t => update_load ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then none else (mp p0)).
  Proof. i. extensionality p0. apply update_load_ord1; auto. Qed.

  Lemma update_load_ord2:
    forall ul o l t
      (ORD: Ordering.le Ordering.acqrel o),
      update_load ul o l t = (if (Loc.eqb ul l) then none else (acq_flag t)).
  Proof. i. unfold update_load. destruct o; ss; clarify. Qed.

  Lemma update_load_ord2f:
    forall ul o mp
      (ORD: Ordering.le Ordering.acqrel o),
      (fun p0: Loc.t => update_load ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then none else (acq_flag (mp p0))).
  Proof. i. extensionality p0. apply update_load_ord2; auto. Qed.


  Lemma ord_inv1':
    forall o, (Ordering.le o Ordering.na) \/
         (Ordering.le Ordering.plain o).
  Proof. i. destruct o; auto. Qed.

  Lemma update_read_ord1:
    forall ul o l t
      (ORD: Ordering.le o Ordering.na),
      update_read ul o l t = (if (Loc.eqb ul l) then none else t).
  Proof. i. unfold update_read. des_ifs. Qed.

  Lemma update_read_ord1f:
    forall ul o mp
      (ORD: Ordering.le o Ordering.na),
      (fun p0: Loc.t => update_read ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then none else (mp p0)).
  Proof. i. extensionality p0. apply update_read_ord1; auto. Qed.

  Lemma update_read_ord2:
    forall ul o l t
      (ORD: Ordering.le Ordering.plain o),
      update_read ul o l t = (if (Loc.eqb ul l) then none else (acq_flag t)).
  Proof. i. unfold update_read. destruct o; ss; clarify. Qed.

  Lemma update_read_ord2f:
    forall ul o mp
      (ORD: Ordering.le Ordering.plain o),
      (fun p0: Loc.t => update_read ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then none else (acq_flag (mp p0))).
  Proof. i. extensionality p0. apply update_read_ord2; auto. Qed.



  Lemma ord_inv2:
    forall o, (Ordering.le o Ordering.na) \/
         (Ordering.le Ordering.plain o && Ordering.le o Ordering.relaxed)%bool \/
         (Ordering.le Ordering.strong_relaxed o).
  Proof. i. destruct o; auto. Qed.

  Lemma update_store_ord1:
    forall ul o l t
      (ORD: Ordering.le o Ordering.na),
      update_store ul o l t = if (Loc.eqb ul l) then full else t.
  Proof. i. unfold update_store. des_ifs. Qed.

  Lemma update_store_ord1f:
    forall ul o mp
      (ORD: Ordering.le o Ordering.na),
      (fun p0: Loc.t => update_store ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then full else (mp p0)).
  Proof. i. extensionality p0. apply update_store_ord1; auto. Qed.

  Lemma update_store_ord2:
    forall ul o l t
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.relaxed)%bool),
      update_store ul o l t = (if (Loc.eqb ul l) then none else t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_store_ord2f:
    forall ul o mp
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.relaxed)%bool),
      (fun p0: Loc.t => update_store ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then none else (mp p0)).
  Proof. i. extensionality p0. apply update_store_ord2; auto. Qed.

  Lemma update_store_ord3:
    forall ul o l t
      (ORD: Ordering.le Ordering.strong_relaxed o),
      update_store ul o l t = (if (Loc.eqb ul l) then none else (rel_flag t)).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_store_ord3f:
    forall ul o mp
      (ORD: Ordering.le Ordering.strong_relaxed o),
      (fun p0: Loc.t => update_store ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then none else (rel_flag (mp p0))).
  Proof. i. extensionality p0. apply update_store_ord3; auto. Qed.



  Lemma ord_inv3:
    forall o, (Ordering.le o Ordering.strong_relaxed) \/
         (Ordering.le Ordering.acqrel o).
  Proof. i. destruct o; auto. Qed.

  Lemma update_fence_r_ord1:
    forall o l t
      (ORD: Ordering.le o Ordering.strong_relaxed),
      update_fence_r o l t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_fence_r_ord1f:
    forall o mp
      (ORD: Ordering.le o Ordering.strong_relaxed),
      (fun p0: Loc.t => update_fence_r o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply update_fence_r_ord1; auto. Qed.

  Lemma update_fence_r_ord2:
    forall o l t
      (ORD: (Ordering.le Ordering.acqrel o)),
      update_fence_r o l t = (acq_flag t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_fence_r_ord2f:
    forall o mp
      (ORD: (Ordering.le Ordering.acqrel o)),
      (fun p0: Loc.t => update_fence_r o p0 (mp p0)) = fun p0 => (acq_flag (mp p0)).
  Proof. i. extensionality p0. apply update_fence_r_ord2; auto. Qed.


  Lemma ord_inv3':
    forall o, (Ordering.le o Ordering.relaxed) \/
         (Ordering.le Ordering.strong_relaxed o && Ordering.le o Ordering.acqrel)%bool \/
         (Ordering.le Ordering.seqcst o).
  Proof. i. destruct o; auto. Qed.

  Lemma update_fence_w_ord1:
    forall o l t
      (ORD: Ordering.le o Ordering.relaxed),
      update_fence_w o l t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_fence_w_ord1f:
    forall o mp
      (ORD: Ordering.le o Ordering.relaxed),
      (fun p0: Loc.t => update_fence_w o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply update_fence_w_ord1; auto. Qed.

  Lemma update_fence_w_ord2:
    forall o l t
      (ORD: (Ordering.le Ordering.strong_relaxed o && Ordering.le o Ordering.acqrel)%bool),
      update_fence_w o l t = (rel_flag t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_fence_w_ord2f:
    forall o mp
      (ORD: (Ordering.le Ordering.strong_relaxed o && Ordering.le o Ordering.acqrel)%bool),
      (fun p0: Loc.t => update_fence_w o p0 (mp p0)) = fun p0 => (rel_flag (mp p0)).
  Proof. i. extensionality p0. apply update_fence_w_ord2; auto. Qed.

  Lemma update_fence_w_ord3:
    forall o l t
      (ORD: Ordering.le Ordering.seqcst o),
      update_fence_w o l t = (rel_flag (acq_flag t)).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma update_fence_w_ord3f:
    forall o mp
      (ORD: Ordering.le Ordering.seqcst o),
      (fun p0: Loc.t => update_fence_w o p0 (mp p0)) = fun p0 => (rel_flag (acq_flag (mp p0))).
  Proof. i. extensionality p0. apply update_fence_w_ord3; auto. Qed.


  Lemma rel_flag_mon:
    forall k1 k2 (LE: le k1 k2), le (rel_flag k1) (rel_flag k2).
  Proof.
    i. unfold rel_flag. des_ifs; ss; clarify.
  Qed.

  Lemma rel_flag_le:
    forall k, le (rel_flag k) k.
  Proof.
    i. unfold rel_flag. des_ifs; ss; clarify.
  Qed.

  Lemma acq_flag_mon:
    forall k1 k2 (LE: le k1 k2), le (acq_flag k1) (acq_flag k2).
  Proof.
    i. unfold acq_flag. des_ifs; ss; clarify.
  Qed.

  Lemma acq_flag_le:
    forall k, le (acq_flag k) k.
  Proof.
    i. unfold acq_flag. des_ifs; ss; clarify.
  Qed.



  Lemma update_load_kspec:
    forall l1 l2 o, knowledge_spec le bot (update_load l1 o l2).
  Proof.
    i. hexploit (ord_inv1 o). i. des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_load_ord1; auto. des_ifs.
      + rewrite ! update_load_ord1; auto. des_ifs. right; refl. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_load_ord2; auto. des_ifs. apply acq_flag_mon; auto.
      + rewrite ! update_load_ord2; auto. des_ifs. right; refl. left; apply acq_flag_le.
  Qed.

  Lemma update_read_kspec:
    forall l1 l2 o, knowledge_spec le bot (update_read l1 o l2).
  Proof.
    i. hexploit (ord_inv1' o). i. des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_read_ord1; auto. des_ifs.
      + rewrite ! update_read_ord1; auto. des_ifs. right; refl. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_read_ord2; auto. des_ifs. apply acq_flag_mon; auto.
      + rewrite ! update_read_ord2; auto. des_ifs. right; refl. left; apply acq_flag_le.
  Qed.

  Lemma update_store_kspec:
    forall l1 l2 o, knowledge_spec le bot (update_store l1 o l2).
  Proof.
    i. hexploit (ord_inv2 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_store_ord1; auto. des_ifs.
      + rewrite ! update_store_ord1; auto. des_ifs.
        right; refl. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_store_ord2; auto. des_ifs.
      + rewrite ! update_store_ord2; auto. des_ifs.
        right; refl. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_store_ord3; auto. des_ifs.
        apply rel_flag_mon; auto.
      + rewrite ! update_store_ord3; auto. des_ifs.
        right; refl. left; apply rel_flag_le; auto.
  Qed.

  Lemma update_fence_r_kspec:
    forall l o, knowledge_spec le bot (update_fence_r o l).
  Proof.
    i. hexploit (ord_inv3 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_fence_r_ord1; auto.
      + rewrite ! update_fence_r_ord1; auto. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_fence_r_ord2; auto. apply acq_flag_mon; auto.
      + rewrite ! update_fence_r_ord2; auto. left; apply acq_flag_le.
  Qed.

  Lemma update_fence_w_kspec:
    forall l o, knowledge_spec le bot (update_fence_w o l).
  Proof.
    i. hexploit (ord_inv3' o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_fence_w_ord1; auto.
      + rewrite ! update_fence_w_ord1; auto. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_fence_w_ord2; auto. apply rel_flag_mon; auto.
      + rewrite ! update_fence_w_ord2; auto. left; apply rel_flag_le.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! update_fence_w_ord3; auto. apply rel_flag_mon. apply acq_flag_mon. auto.
      + rewrite ! update_fence_w_ord3; auto. left. etrans. apply rel_flag_le. apply acq_flag_le.
  Qed.

  Lemma update_inst_kspec:
    forall (i: Inst.t) (l: Loc.t), knowledge_spec le bot (update_inst i l).
  Proof.
    i. destruct i.
    1,2,7,8,9: unfold knowledge_spec; split; red; i; ss; clarify; auto.
    all: try (left; refl).
    all: unfold update_inst; ss.
    apply update_load_kspec.
    apply update_store_kspec.
    - eapply kspec_app; eauto. apply le_PreOrder. apply bot_spec. apply update_read_kspec. apply update_store_kspec.
    - eapply kspec_app; eauto. apply le_PreOrder. apply bot_spec. apply update_fence_r_kspec. apply update_fence_w_kspec.
  Qed.

  Lemma update_inst_sspec:
    forall p k, eq (update_inst Inst.skip p k) k.
  Proof. ss. Qed.

  Lemma update_inst_mon: forall (i: Inst.t) p d1 d2 (LE: le d1 d2), le (update_inst i p d1) (update_inst i p d2).
  Proof.
    i. hexploit update_inst_kspec. i. unfold knowledge_spec in H. des. eapply MON; eauto.
  Qed.

End ANALYSIS.





Section ALG.

  Definition DSE_do_opt (mp: Data Three Loc.t) (i: Inst.t) : Prop :=
    match i with
    | Inst.store l _ o =>
      match (mp l), o with
      | half, Ordering.na
      | full, Ordering.na => True
      | _, _ => False
      end
    | _ => False
    end
  .

  Lemma do_opt_not:
    forall (i : Inst.t) (data : Data Three Loc.t)
      (NOOPT: ~ (DSE_do_opt data i)),
      DSE_opt_inst data i = i.
  Proof.
    i. destruct i; ss; clarify. des_ifs; ss; clarify.
  Qed.

  Lemma do_opt_not_skip:
    forall data, not (DSE_do_opt data Inst.skip).
  Proof. ss. Qed.



  Definition DSE_opt2: Opt2.t :=
    Opt2.mk_opt2
      ThreeML bot bot_spec level
      update_inst update_inst_mon update_inst_sspec
      DSE_opt_inst
      DSE_do_opt do_opt_not do_opt_not_skip
      strict_order half.

  Definition block_d := Opt2.block_d DSE_opt2.

  Lemma analysis_correct: update_block = block_d.
  Proof. ss. Qed.

  Lemma opt_correct: DSE_opt_block = Opt2.opt_block DSE_opt2.
  Proof. ss. Qed.

End ALG.

Section FIXPOINT.

  Definition DSE_fix2: FixOpt2.t :=
    @FixOpt2.mk_fix2
      ThreeML bot bot_spec level level_grounded
      Loc.t update_inst update_inst_kspec update_inst_sspec
      half.


  Lemma DSE_kspec2: forall blk p, knowledge_spec (MLattice.le ThreeML) bot (update_block blk p).
  Proof.
    i. eapply (@update_block_is_knowledge DSE_fix2).
  Qed.

  Theorem block_d_fix: forall blk f (FUN: f = block_d blk) p,
      @n_fix Three (MLattice.eq ThreeML) (MLattice.eq_Equiv ThreeML) (f p) (S level).
  Proof.
    i. eapply (@update_block_fix DSE_fix2). eauto.
  Qed.

  Theorem block_d_dec: forall blk p d f (FUN: f = block_d blk p), (MLattice.le ThreeML) (f (f d)) (f d).
  Proof.
    i. clarify. ss. rewrite <- analysis_correct.
    hexploit (knowledge_le_n eq_leibniz (@MLattice.le_PartialOrder ThreeML) bot_spec 1 (DSE_kspec2 blk p)).
    i; ss. eauto.
  Qed.

End FIXPOINT.
