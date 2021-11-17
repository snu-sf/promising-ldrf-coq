Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.

Require Import FoldN.
Require Import Knowledge.
Require Import Opt4.

Require Import ITreeLang.

Require Import WRforwarding.



Global Program Instance le_PreOrder: PreOrder le.
Next Obligation.
Proof.
  eapply PreOrder_Reflexive. Unshelve.    
  set (ML:= MLattice.mk_mlattice
              eq_Equiv eq_leibniz
              meet meet_comm meet_assoc meet_idem
              le le_spec).
  apply (@MLattice.le_PreOrder ML).
Qed.
Next Obligation.
Proof.
  eapply PreOrder_Transitive. Unshelve.
  set (ML:= MLattice.mk_mlattice
              eq_Equiv eq_leibniz
              meet meet_comm meet_assoc meet_idem
              le le_spec).
  apply (@MLattice.le_PreOrder ML).
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
    set (ML:= MLattice.mk_mlattice
                eq_Equiv eq_leibniz
                meet meet_comm meet_assoc meet_idem
                le le_spec).
    eapply (@MLattice.le_PartialOrder ML).
Qed.



Section ALGAUX.

  Lemma ord_inv1:
    forall o, (Ordering.le o Ordering.na) \/
         (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool \/
         (Ordering.le Ordering.acqrel o).
  Proof. i. destruct o; auto. Qed.

  Lemma WRfwd_read_ord1:
    forall ul o l t
      (ORD: Ordering.le o Ordering.na),
      WRfwd_read ul o l t = t.
  Proof. i. unfold WRfwd_read. des_ifs. Qed.

  Lemma WRfwd_read_ord1f:
    forall ul o mp
      (ORD: Ordering.le o Ordering.na),
      (fun p0: Loc.t => WRfwd_read ul o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply WRfwd_read_ord1; auto. Qed.

  Lemma WRfwd_read_ord2:
    forall ul o l t
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool),
      WRfwd_read ul o l t = (if (Loc.eqb ul l) then None else t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_read_ord2f:
    forall ul o mp
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool),
      (fun p0: Loc.t => WRfwd_read ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then None else (mp p0)).
  Proof. i. extensionality p0. apply WRfwd_read_ord2; auto. Qed.

  Lemma WRfwd_read_ord3:
    forall ul o l t
      (ORD: Ordering.le Ordering.acqrel o),
      WRfwd_read ul o l t = (if (Loc.eqb ul l) then None else (Two_elim t)).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_read_ord3f:
    forall ul o mp
      (ORD: Ordering.le Ordering.acqrel o),
      (fun p0: Loc.t => WRfwd_read ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then None else (Two_elim (mp p0))).
  Proof. i. extensionality p0. apply WRfwd_read_ord3; auto. Qed.


  Lemma ord_inv2:
    forall o, (Ordering.le o Ordering.relaxed) \/
         (Ordering.le Ordering.strong_relaxed o).
  Proof. i. destruct o; auto. Qed.

  Lemma WRfwd_write_ord1:
    forall ul o l t
      (ORD: Ordering.le o Ordering.relaxed),
      WRfwd_write ul o l t = (if (Loc.eqb ul l) then None else t).
  Proof. i. unfold WRfwd_write. des_ifs. Qed.

  Lemma WRfwd_write_ord1f:
    forall ul o mp
      (ORD: Ordering.le o Ordering.relaxed),
      (fun p0: Loc.t => WRfwd_write ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then None else (mp p0)).
  Proof. i. extensionality p0. apply WRfwd_write_ord1; auto. Qed.

  Lemma WRfwd_write_ord2:
    forall ul o l t
      (ORD: Ordering.le Ordering.strong_relaxed o),
      WRfwd_write ul o l t = (if (Loc.eqb ul l) then None else (Two_set_flag t)).
  Proof. i. unfold WRfwd_write. destruct o; ss; clarify. Qed.

  Lemma WRfwd_write_ord2f:
    forall ul o mp
      (ORD: Ordering.le Ordering.strong_relaxed o),
      (fun p0: Loc.t => WRfwd_write ul o p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then None else (Two_set_flag (mp p0))).
  Proof. i. extensionality p0. apply WRfwd_write_ord2; auto. Qed.


  Lemma ord_inv2':
    forall o, (Ordering.le o Ordering.na) \/
         (Ordering.le Ordering.plain o && Ordering.le o Ordering.relaxed)%bool \/
         (Ordering.le Ordering.strong_relaxed o).
  Proof. i. destruct o; auto. Qed.

  Lemma WRfwd_store_ord1:
    forall ul e o l t
      (ORD: Ordering.le o Ordering.na),
      WRfwd_store ul e o l t =
      (if (Loc.eqb ul l)
       then (match e with
             | Inst.expr_val c => Two_new c
             | _ => None
             end)
       else t).
  Proof. i. unfold WRfwd_store. des_ifs. Qed.

  Lemma WRfwd_store_ord1f:
    forall ul e o mp
      (ORD: Ordering.le o Ordering.na),
      (fun p0: Loc.t => WRfwd_store ul e o p0 (mp p0)) =
      fun p0 => (if (Loc.eqb ul p0)
              then (match e with
                    | Inst.expr_val c => Two_new c
                    | _ => None
                    end)
              else (mp p0)).
  Proof. i. extensionality p0. apply WRfwd_store_ord1; auto. Qed.

  Lemma WRfwd_store_ord2:
    forall ul e o l t
      (ORD: Ordering.le Ordering.plain o),
      WRfwd_store ul e o l t = WRfwd_write ul o l t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_store_ord2f:
    forall ul e o mp
      (ORD: Ordering.le Ordering.plain o),
      (fun p0: Loc.t => WRfwd_store ul e o p0 (mp p0)) = fun p0 => WRfwd_write ul o p0 (mp p0).
  Proof. i. extensionality p0. apply WRfwd_store_ord2; auto. Qed.

  Lemma ord_inv3:
    forall o, (Ordering.le o Ordering.strong_relaxed) \/ (Ordering.le Ordering.acqrel o).
  Proof. i. destruct o; auto. Qed.

  Lemma WRfwd_fence_r_ord1:
    forall o l t
      (ORD: Ordering.le o Ordering.strong_relaxed),
      WRfwd_fence_r o l t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_fence_r_ord1f:
    forall o mp
      (ORD: Ordering.le o Ordering.strong_relaxed),
      (fun p0: Loc.t => WRfwd_fence_r o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply WRfwd_fence_r_ord1; auto. Qed.

  Lemma WRfwd_fence_r_ord2:
    forall o l t
      (ORD: (Ordering.le Ordering.acqrel o)),
      WRfwd_fence_r o l t = (Two_elim t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_fence_r_ord2f:
    forall o mp
      (ORD: (Ordering.le Ordering.acqrel o)),
      (fun p0: Loc.t => WRfwd_fence_r o p0 (mp p0)) = fun p0 => (Two_elim (mp p0)).
  Proof. i. extensionality p0. apply WRfwd_fence_r_ord2; auto. Qed.


  Lemma ord_inv4:
    forall o, (Ordering.le o Ordering.relaxed) \/
         (Ordering.le Ordering.strong_relaxed o && Ordering.le o Ordering.acqrel)%bool \/
         (Ordering.le Ordering.seqcst o).
  Proof. i. destruct o; auto. Qed.

  Lemma WRfwd_fence_w_ord1:
    forall o l t
      (ORD: Ordering.le o Ordering.relaxed),
      WRfwd_fence_w o l t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_fence_w_ord1f:
    forall o mp
      (ORD: Ordering.le o Ordering.relaxed),
      (fun p0: Loc.t => WRfwd_fence_w o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply WRfwd_fence_w_ord1; auto. Qed.

  Lemma WRfwd_fence_w_ord2:
    forall o l t
      (ORD: (Ordering.le Ordering.strong_relaxed o && Ordering.le o Ordering.acqrel)%bool),
      WRfwd_fence_w o l t = (Two_set_flag t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_fence_w_ord2f:
    forall o mp
      (ORD: (Ordering.le Ordering.strong_relaxed o && Ordering.le o Ordering.acqrel)%bool),
      (fun p0: Loc.t => WRfwd_fence_w o p0 (mp p0)) = fun p0 => (Two_set_flag (mp p0)).
  Proof. i. extensionality p0. apply WRfwd_fence_w_ord2; auto. Qed.

  Lemma WRfwd_fence_w_ord3:
    forall o l t
      (ORD: Ordering.le Ordering.seqcst o),
      WRfwd_fence_w o l t = Two_set_flag (Two_elim t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma WRfwd_fence_w_ord3f:
    forall o mp
      (ORD: Ordering.le Ordering.seqcst o),
      (fun p0: Loc.t => WRfwd_fence_w o p0 (mp p0)) = fun p0 => Two_set_flag (Two_elim (mp p0)).
  Proof. i. extensionality p0. apply WRfwd_fence_w_ord3; auto. Qed.



  Lemma Two_elim_mon:
    forall k1 k2 (LE: le k1 k2), le (Two_elim k1) (Two_elim k2).
  Proof.
    i. unfold Two_elim. des_ifs; ss; clarify. des; clarify.
  Qed.

  Lemma Two_elim_le:
    forall k, le (Two_elim k) k.
  Proof.
    i. unfold Two_elim. des_ifs; ss; clarify. des; auto.
  Qed.

  Lemma Two_set_flag_mon:
    forall k1 k2 (LE: le k1 k2), le (Two_set_flag k1) (Two_set_flag k2).
  Proof.
    i. unfold Two_set_flag. des_ifs; ss; clarify. des; clarify; auto.
  Qed.

  Lemma Two_set_flag_le:
    forall k, le (Two_set_flag k) k.
  Proof.
    i. unfold Two_set_flag. des_ifs; ss; clarify. auto.
  Qed.


  Lemma WRfwd_read_kspec:
    forall l1 l2 o, knowledge_spec le bot (WRfwd_read l1 o l2).
  Proof.
    i. unfold knowledge_spec. split; red; i.
    - unfold WRfwd_read. unfold distl. des_ifs; ss; clarify.
      apply Two_elim_mon; auto.
    - unfold WRfwd_read. unfold distl. des_ifs; ss; clarify; auto.
      all: try (left; refl).
      left; apply Two_elim_le.
  Qed.

  Lemma WRfwd_write_kspec:
    forall l1 l2 o, knowledge_spec le bot (WRfwd_write l1 o l2).
  Proof.
    i. hexploit (ord_inv2 o). i. des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_write_ord1; auto. des_ifs.
      + rewrite ! WRfwd_write_ord1; auto. des_ifs. right; refl. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_write_ord2; auto. des_ifs. apply Two_set_flag_mon; auto.
      + rewrite ! WRfwd_write_ord2; auto. des_ifs. right; refl. left; apply Two_set_flag_le.
  Qed.

  Lemma WRfwd_store_kspec:
    forall l1 l2 o e, knowledge_spec le bot (WRfwd_store l1 e o l2).
  Proof.
    i. hexploit (ord_inv1 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_store_ord1; auto. des_ifs. refl.
      + rewrite ! WRfwd_store_ord1; auto. des_ifs.
        all: try (right; refl). left; refl.
    - replace (WRfwd_store l1 e o l2) with (WRfwd_write l1 o l2).
      2:{ extensionality s. rewrite WRfwd_store_ord2; auto. destruct o; ss. }
      apply WRfwd_write_kspec.
    - replace (WRfwd_store l1 e o l2) with (WRfwd_write l1 o l2).
      2:{ extensionality s. rewrite WRfwd_store_ord2; auto. destruct o; ss. }
      apply WRfwd_write_kspec.
  Qed.

  Lemma WRfwd_fence_r_kspec:
    forall l o, knowledge_spec le bot (WRfwd_fence_r o l).
  Proof.
    i. hexploit (ord_inv3 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_fence_r_ord1; auto.
      + rewrite ! WRfwd_fence_r_ord1; auto. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_fence_r_ord2; auto. apply Two_elim_mon; auto.
      + rewrite ! WRfwd_fence_r_ord2; auto. left; apply Two_elim_le.
  Qed.

  Lemma WRfwd_fence_w_kspec:
    forall l o, knowledge_spec le bot (WRfwd_fence_w o l).
  Proof.
    i. hexploit (ord_inv4 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_fence_w_ord1; auto.
      + rewrite ! WRfwd_fence_w_ord1; auto. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_fence_w_ord2; auto. apply Two_set_flag_mon; auto.
      + rewrite ! WRfwd_fence_w_ord2; auto. left; apply Two_set_flag_le.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! WRfwd_fence_w_ord3; auto. apply Two_set_flag_mon. apply Two_elim_mon; auto.
      + rewrite ! WRfwd_fence_w_ord3; auto. left. etrans. 2:apply Two_elim_le. apply Two_set_flag_le; auto.
  Qed.



  Lemma WRfwd_kspec:
    forall (i: Inst.t) (l: Loc.t), knowledge_spec le bot (WRfwd_inst i l).
  Proof.
    i. destruct i.
    1,2,7,8,9: unfold knowledge_spec; split; red; i; ss; clarify; auto.
    all: try (left; refl).
    all: unfold WRfwd_inst; ss.
    apply WRfwd_read_kspec.
    apply WRfwd_store_kspec.
    - eapply kspec_app; eauto. apply le_PreOrder. apply bot_spec. apply WRfwd_write_kspec. apply WRfwd_read_kspec.
    - eapply kspec_app; eauto. apply le_PreOrder. apply bot_spec. apply WRfwd_fence_w_kspec. apply WRfwd_fence_r_kspec.
  Qed.

  Lemma skip_d:
    forall (l: Loc.t) (k: Two), eq (WRfwd_inst Inst.skip l k) k.
  Proof.
    i. ss.
  Qed.


  Let inst_d := WRfwd_inst.

  Lemma inst_d_mon: forall (i: Inst.t) p d1 d2 (LE: le d1 d2), le (inst_d i p d1) (inst_d i p d2).
  Proof.
    i. hexploit WRfwd_kspec. i. unfold knowledge_spec in H. des. eapply MON; eauto.
  Qed.

End ALGAUX.





Section ALG.

  Definition WRfwd_do_opt (mp: Data Two Loc.t) (i: Inst.t) : Prop :=
    match i with
    | Inst.load _ l o =>
      match (mp l), o with
      | Some (_, _), Ordering.na => True
      | _, _ => False
      end
    | _ => False
    end
  .

  Lemma do_opt_not:
    forall i data, not (WRfwd_do_opt data i) -> WRfwd_opt_inst data i = i.
  Proof.
    i. destruct i; ss; clarify. des_ifs; ss; clarify.
  Qed.

  Lemma do_opt_mon:
    forall i d1 d2 (LE: forall p, le (d1 p) (d2 p)) (DO: WRfwd_do_opt d1 i),
      WRfwd_do_opt d2 i.
  Proof.
    i. destruct i; ss; clarify. des_ifs; ss; clarify.
    specialize LE with rhs. unfold le in LE.
    rewrite Heq0 in LE. rewrite Heq in LE. clarify.
  Qed.


  Definition WRfwd_opt4: Opt4.t :=
    Opt4.mk_opt4
      TwoML bot bot_spec N
      WRfwd_inst inst_d_mon skip_d
      WRfwd_opt_inst
      WRfwd_do_opt do_opt_not do_opt_mon.


  Definition block_d := Opt4.block_d WRfwd_opt4.

  Lemma analysis_correct: WRfwd_block = block_d.
  Proof. ss. Qed.

End ALG.



Section FIXPOINT.

  Lemma level_grounded: forall (t: Two), grounded eq le t N.
  Proof.
    i. econs. i. unfold lt in LT. des.
    destruct t, k'; ss; clarify; des_ifs; ss; clarify; des; clarify; ss.
    - clear.
      econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify; des_ifs; ss; clarify; des; clarify; ss.
      clear LT LT0. econs; i. unfold lt in LT. des.
      destruct k'; ss; clarify; des_ifs; ss; clarify; des; clarify; ss.
    - destruct b; ss; clarify.
      clear LT. econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify; des_ifs; ss; clarify; des; clarify; ss.
      clear LT LT0. econs; i. unfold lt in LT. des.
      destruct k'; ss; clarify; des_ifs; ss; clarify; des; clarify; ss.
    - clear.
      econs. i. unfold lt in LT. des.
      destruct k'; ss; clarify; des_ifs; ss; clarify; des; clarify; ss.
  Qed.

  Definition WRfwd_fix4: FixOpt4.t :=
    @FixOpt4.mk_fix4
      TwoML bot bot_spec N level_grounded
      (Loc.t) WRfwd_inst WRfwd_kspec skip_d.


  Lemma WRfwd_kspec2: forall blk p, knowledge_spec (MLattice.le TwoML) bot (WRfwd_block blk p).
  Proof.
    i. eapply (@update_block_is_knowledge WRfwd_fix4).
  Qed.

  Theorem block_d_fix: forall blk f (FUN: f = block_d blk) p,
      @n_fix Two (MLattice.eq TwoML) (MLattice.eq_Equiv TwoML) (f p) (S N).
  Proof.
    i. eapply (@update_block_fix WRfwd_fix4). eauto.
  Qed.

  Theorem block_d_dec: forall blk p d f (FUN: f = block_d blk p), (MLattice.le TwoML) (f (f d)) (f d).
  Proof.
    i. clarify. ss. rewrite <- analysis_correct.
    hexploit (knowledge_le_n eq_leibniz (@MLattice.le_PartialOrder TwoML) bot_spec 1 (WRfwd_kspec2 blk p)).
    i; ss. eauto.
  Qed.

End FIXPOINT.
