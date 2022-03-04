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
Require Import Opt4.

Require Import ITreeLang.

Require Import RRforwarding.





Section ALGAUX.

  Lemma ord_inv1:
    forall o, (Ordering.le o Ordering.na) \/
         (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool \/
         (Ordering.le Ordering.acqrel o).
  Proof. i. destruct o; auto. Qed.

  Lemma RRfwd_load_ord1:
    forall ul x o l t
      (ORD: Ordering.le o Ordering.na),
      RRfwd_load ul x o l t =
      if (Loc.eqb ul l)
      then (IdentSet.add x t)
      else (IdentSet.remove x t).
  Proof. i. unfold RRfwd_load. des_ifs. Qed.

  Lemma RRfwd_load_ord1f:
    forall ul x o mp
      (ORD: Ordering.le o Ordering.na),
      (fun p0: Loc.t => RRfwd_load ul x o p0 (mp p0)) =
      fun p0 => if (Loc.eqb ul p0)
             then (IdentSet.add x (mp p0))
             else (IdentSet.remove x (mp p0)).
  Proof. i. extensionality p0. apply RRfwd_load_ord1; auto. Qed.

  Lemma RRfwd_load_ord2:
    forall ul x o l t
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool),
      RRfwd_load ul x o l t =
      if (Loc.eqb ul l)
      then bot
      else (IdentSet.remove x t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_load_ord2f:
    forall ul x o mp
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool),
      (fun p0: Loc.t => RRfwd_load ul x o p0 (mp p0)) =
      fun p0 => if (Loc.eqb ul p0)
             then bot
             else (IdentSet.remove x (mp p0)).
  Proof. i. extensionality p0. apply RRfwd_load_ord2; auto. Qed.

  Lemma RRfwd_load_ord3:
    forall ul x o l t
      (ORD: Ordering.le Ordering.acqrel o),
      RRfwd_load ul x o l t = bot.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_load_ord3f:
    forall ul x o mp
      (ORD: Ordering.le Ordering.acqrel o),
      (fun p0: Loc.t => RRfwd_load ul x o p0 (mp p0)) = fun p0 => bot.
  Proof. i. extensionality p0. apply RRfwd_load_ord3; auto. Qed.


  Lemma RRfwd_write_ord:
    forall ul l t,
      RRfwd_write ul l t = (if (Loc.eqb ul l) then bot else t).
  Proof. i. unfold RRfwd_write. des_ifs. Qed.

  Lemma RRfwd_write_ordf:
    forall ul mp,
      (fun p0: Loc.t => RRfwd_write ul p0 (mp p0)) = fun p0 => (if (Loc.eqb ul p0) then bot else (mp p0)).
  Proof. i. extensionality p0. apply RRfwd_write_ord; auto. Qed.


  Lemma ord_inv2:
    forall o, (Ordering.le o Ordering.strong_relaxed) \/
         (Ordering.le Ordering.acqrel o).
  Proof. i. destruct o; auto. Qed.

  Lemma RRfwd_fence_r_ord1:
    forall o l t
      (ORD: Ordering.le o Ordering.strong_relaxed),
      RRfwd_fence_r o l t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_fence_r_ord1f:
    forall o mp
      (ORD: Ordering.le o Ordering.strong_relaxed),
      (fun p0: Loc.t => RRfwd_fence_r o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply RRfwd_fence_r_ord1; auto. Qed.

  Lemma RRfwd_fence_r_ord2:
    forall o l t
      (ORD: Ordering.le Ordering.acqrel o),
      RRfwd_fence_r o l t = bot.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_fence_r_ord2f:
    forall o mp
      (ORD: Ordering.le Ordering.acqrel o),
      (fun p0: Loc.t => RRfwd_fence_r o p0 (mp p0)) = fun p0 => bot.
  Proof. i. extensionality p0. apply RRfwd_fence_r_ord2; auto. Qed.


  Lemma ord_inv3:
    forall o, (Ordering.le o Ordering.acqrel) \/
         (Ordering.le Ordering.seqcst o).
  Proof. i. destruct o; auto. Qed.

  Lemma RRfwd_fence_w_ord1:
    forall o l t
      (ORD: Ordering.le o Ordering.acqrel),
      RRfwd_fence_w o l t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_fence_w_ord1f:
    forall o mp
      (ORD: Ordering.le o Ordering.acqrel),
      (fun p0: Loc.t => RRfwd_fence_w o p0 (mp p0)) = fun p0 => mp p0.
  Proof. i. extensionality p0. apply RRfwd_fence_w_ord1; auto. Qed.

  Lemma RRfwd_fence_w_ord2:
    forall o l t
      (ORD: Ordering.le Ordering.seqcst o),
      RRfwd_fence_w o l t = bot.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_fence_w_ord2f:
    forall o mp
      (ORD: Ordering.le Ordering.seqcst o),
      (fun p0: Loc.t => RRfwd_fence_w o p0 (mp p0)) = fun p0 => bot.
  Proof. i. extensionality p0. apply RRfwd_fence_w_ord2; auto. Qed.


  Lemma RRfwd_assign_ord:
    forall x l t,
      RRfwd_assign x l t = IdentSet.remove x t.
  Proof. i. unfold RRfwd_assign. des_ifs. Qed.

  Lemma RRfwd_assign_ordf:
    forall x mp,
      (fun p0: Loc.t => RRfwd_assign x p0 (mp p0)) = fun p0 => IdentSet.remove x (mp p0).
  Proof. i. extensionality p0. apply RRfwd_assign_ord. Qed.



  Let le := MLattice.le IdentSetML.
  Let inst_d := RRfwd_inst.

  Definition mon f := forall d1 d2 (LE: le d1 d2), le (f d1) (f d2).

  Lemma add_mon: forall x, mon (IdentSet.add x).
  Proof.
    unfold mon. i. unfold le, IdentSet.Subset in *. ss. ii.
    destruct (Ident.eqb a x) eqn:CASE.
    - rewrite Ident.eqb_eq in CASE. clarify. eapply IdentSet.Facts.add_1; eauto.
    - apply Ident.eqb_neq in CASE. eapply IdentSet.Facts.add_3 in H; eauto. eapply IdentSet.add_spec; eauto.
  Qed.

  Lemma remove_mon: forall x, mon (IdentSet.remove x).
  Proof.
    unfold mon. i. unfold le, IdentSet.Subset in *. ii.
    destruct (Ident.eqb a x) eqn:CASE.
    - rewrite Ident.eqb_eq in CASE. clarify. eapply IdentSet.Facts.remove_1 in H; eauto. clarify.
    - apply Ident.eqb_neq in CASE. eapply IdentSet.Facts.remove_3 in H; eauto. eapply IdentSet.remove_spec; eauto.
  Qed.


  Lemma RRfwd_load_mon:
    forall l1 l2 x o, mon (RRfwd_load l1 x o l2).
  Proof.
    unfold mon. i. hexploit (ord_inv1 o). i. des.
    - rewrite ! RRfwd_load_ord1; auto. des_ifs. eapply add_mon; eauto. eapply remove_mon; eauto.
    - rewrite ! RRfwd_load_ord2; auto. des_ifs. eapply remove_mon; eauto.
    - rewrite ! RRfwd_load_ord3; auto. refl.
  Qed.

  Lemma RRfwd_write_mon:
    forall l1 l2, mon (RRfwd_write l1 l2).
  Proof.
    unfold mon. i. rewrite ! RRfwd_write_ord. des_ifs.
  Qed.

  Lemma RRfwd_fence_r_mon:
    forall l o, mon (RRfwd_fence_r o l).
  Proof.
    unfold mon. i. hexploit (ord_inv2 o). i; des.
    - rewrite ! RRfwd_fence_r_ord1; auto.
    - rewrite ! RRfwd_fence_r_ord2; auto. refl.
  Qed.

  Lemma RRfwd_fence_w_mon:
    forall l o, mon (RRfwd_fence_w o l).
  Proof.
    unfold mon. i. hexploit (ord_inv3 o). i; des.
    - rewrite ! RRfwd_fence_w_ord1; auto.
    - rewrite ! RRfwd_fence_w_ord2; auto. refl.
  Qed.

  Lemma RRfwd_assign_mon:
    forall x l, mon (RRfwd_assign x l).
  Proof.
    unfold mon. i. rewrite ! RRfwd_assign_ord. eapply remove_mon; eauto.
  Qed.


  Lemma inst_d_mon: forall (i: Inst.t) p d1 d2 (LE: le d1 d2), le (inst_d i p d1) (inst_d i p d2).
  Proof.
    i. destruct i; ss.
    eapply RRfwd_assign_mon; eauto.
    eapply RRfwd_load_mon; eauto.
    eapply RRfwd_write_mon; eauto.
    eapply RRfwd_write_mon. eapply RRfwd_load_mon; eauto.
    eapply RRfwd_fence_w_mon. eapply RRfwd_fence_r_mon; eauto.
    eapply RRfwd_assign_mon; eauto.
  Qed.

  Lemma skip_d: forall p d, (MLattice.eq IdentSetML) (inst_d Inst.skip p d) d.
  Proof. ss. Qed.

End ALGAUX.



Section ALG.

  Let le := MLattice.le IdentSetML.

  Definition RRfwd_do_opt (mp: FoldN.GD IdentSet.t Loc.t) (i: Inst.t) : Prop :=
    match i with
    | Inst.load _ l o =>
      match (IdentSet.choose (mp l)), o with
      | Some y, Ordering.na => True
      | _, _ => False
      end
    | _ => False
    end
  .

  Lemma do_opt_not:
    forall i data, not (RRfwd_do_opt data i) -> RRfwd_opt_inst data i = i.
  Proof.
    i. destruct i; ss; clarify. des_ifs.
  Qed.

  Lemma do_opt_mon:
    forall i d1 d2 (LE: forall p, le (d1 p) (d2 p)) (DO: RRfwd_do_opt d1 i),
      RRfwd_do_opt d2 i.
  Proof.
    i. destruct i; ss; clarify. des_ifs; ss; clarify.
    unfold le2, Opt4.le2 in LE. specialize LE with rhs.
    ss. apply IdentSet.choose_spec1 in Heq0. apply IdentSet.choose_spec2 in Heq.
    apply LE in Heq0. apply Heq in Heq0. clarify.
  Qed.

  Definition RRfwd_opt4: Opt4.t :=
    Opt4.mk_opt4
      IdentSetML bot bot_spec N
      RRfwd_inst inst_d_mon skip_d
      RRfwd_opt_inst
      RRfwd_do_opt do_opt_not do_opt_mon.


  Definition block_d := Opt4.block_d RRfwd_opt4.

  Lemma analysis_correct: RRfwd_block = block_d.
  Proof. ss. Qed.

End ALG.





Section DATA2.

  Global Program Instance bool_eq_Equiv: Equivalence (@eq bool).
  Lemma bool_eq_leibniz : forall x y : bool, eq x y -> x = y.
  Proof. auto. Qed.


  Definition bool_le (t1 t2: bool) :=
    match t1, t2 with
    | false, _ => True
    | _, true => True
    | true, false => False
    end.

  Lemma bool_le_spec: forall t1 t2, bool_le t1 t2 <-> t1 = (andb t1 t2).
  Proof.
    i. unfold bool_le, andb. des_ifs.
  Qed.

  Definition boolML: MLattice.t :=
    MLattice.mk_mlattice
      bool_eq_Equiv bool_eq_leibniz
      andb Bool.andb_comm Bool.andb_assoc Bool.andb_diag
      bool_le bool_le_spec.

  Lemma bool_bot_spec: forall t, bool_le false t.
  Proof. i. unfold bool_le. auto. Qed.


  Lemma level_grounded: forall (t: bool), grounded eq bool_le t N.
  Proof.
    i. econs. i. unfold lt in LT. des. destruct t, k'; ss.
    clear. econs. i. unfold lt in LT. des. destruct k'; ss.
  Qed.

End DATA2.



Section ANALYSIS2.

  Definition dists {T} s1 s2 (v1 v2: T) := if (Ident.eqb s1 s2) then v1 else v2.

  Definition RRfwd_load2 (ul: Loc.t) x o : (Loc.t * Ident.t) -> (local_update bool) :=
    fun '(l, i) t =>
      if (Ordering.le o Ordering.na)
      then distl ul l (dists x i true t) (dists x i false t)
      else
        if (Ordering.le o Ordering.strong_relaxed)
        then distl ul l (false) (dists x i false t)
        else false.

  Definition RRfwd_write2 (ul: Loc.t) : (Loc.t * Ident.t) -> (local_update bool) :=
    fun '(l, _) t =>
      distl ul l false t.

  Definition RRfwd_fence_r2 o : (Loc.t * Ident.t) -> (local_update bool) :=
    fun _ t =>
      if (Ordering.le o Ordering.strong_relaxed)
      then t
      else false.

  Definition RRfwd_fence_w2 o : (Loc.t * Ident.t) -> (local_update bool) :=
    fun _ t =>
      if (Ordering.le o Ordering.acqrel)
      then t
      else false.

  Definition RRfwd_assign2 x : (Loc.t * Ident.t) -> (local_update bool) :=
    fun '(_, i) t => dists x i false t.

  Definition RRfwd_inst2 (inst: Inst.t) : (Loc.t * Ident.t) -> (local_update bool) :=
    fun li t =>
      match inst with
      | Inst.skip => t
      | Inst.assign x e => (RRfwd_assign2 x) li t

      | Inst.load x ul o => (RRfwd_load2 ul x o) li t
      | Inst.store ul _ o => (RRfwd_write2 ul) li t

      (* same as load + store *)
      | Inst.update x ul rmw or ow =>
        let ut0 := (RRfwd_load2 ul x or) li t in
        let ut1 := (RRfwd_write2 ul) li ut0 in
        ut1

      | Inst.fence or ow =>
        let ut0 := (RRfwd_fence_r2 or) li t in
        let ut1 := (RRfwd_fence_w2 ow) li ut0 in
        ut1

      | Inst.syscall x es => false
      | Inst.abort => t
      | Inst.choose x => (RRfwd_assign2 x) li t
      end
  .

  Global Program Instance le_PreOrder: PreOrder bool_le.
  Next Obligation.
  Proof.
    eapply PreOrder_Reflexive. Unshelve.    
    apply (@MLattice.le_PreOrder boolML).
  Qed.
  Next Obligation.
  Proof.
    eapply PreOrder_Transitive. Unshelve.
    apply (@MLattice.le_PreOrder boolML).
  Qed.

  Global Program Instance le_PartialOrder: PartialOrder eq bool_le.
  Next Obligation.
  Proof.
    unfold relation_equivalence, relation_conjunction.
    unfold predicate_equivalence, predicate_intersection.
    unfold pointwise_lifting, pointwise_extension.
    i. split; i.
    - clarify. split; refl.
    - des. unfold flip in H0. eapply antisymmetry; eauto.
      Unshelve. auto. eapply partial_order_antisym.
      eapply (@MLattice.le_PartialOrder boolML).
  Qed.



  Lemma RRfwd_load2_ord1:
    forall ul x o l i t
      (ORD: Ordering.le o Ordering.na),
      RRfwd_load2 ul x o (l, i) t =
      if (Loc.eqb ul l)
      then (if (Ident.eqb x i) then true else t)
      else (if (Ident.eqb x i) then false else t).
  Proof. i. unfold RRfwd_load2. des_ifs. Qed.

  Lemma RRfwd_load2_ord2:
    forall ul x o l i t
      (ORD: (Ordering.le Ordering.plain o && Ordering.le o Ordering.strong_relaxed)%bool),
      RRfwd_load2 ul x o (l, i) t =
      if (Loc.eqb ul l)
      then false
      else (if (Ident.eqb x i) then false else t).
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_load2_ord3:
    forall ul x o l i t
      (ORD: Ordering.le Ordering.acqrel o),
      RRfwd_load2 ul x o (l, i) t = false.
  Proof. i. destruct o; ss; clarify. Qed.


  Lemma RRfwd_write2_ord:
    forall ul l i t,
      RRfwd_write2 ul (l, i) t = (if (Loc.eqb ul l) then false else t).
  Proof. i. unfold RRfwd_write2. des_ifs. Qed.


  Lemma RRfwd_fence_r2_ord1:
    forall o l i t
      (ORD: Ordering.le o Ordering.strong_relaxed),
      RRfwd_fence_r2 o (l, i) t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_fence_r2_ord2:
    forall o l i t
      (ORD: Ordering.le Ordering.acqrel o),
      RRfwd_fence_r2 o (l, i) t = false.
  Proof. i. destruct o; ss; clarify. Qed.


  Lemma RRfwd_fence_w2_ord1:
    forall o l i t
      (ORD: Ordering.le o Ordering.acqrel),
      RRfwd_fence_w2 o (l, i) t = t.
  Proof. i. destruct o; ss; clarify. Qed.

  Lemma RRfwd_fence_w2_ord2:
    forall o l i t
      (ORD: Ordering.le Ordering.seqcst o),
      RRfwd_fence_w2 o (l, i) t = false.
  Proof. i. destruct o; ss; clarify. Qed.


  Lemma RRfwd_assign2_ord:
    forall x l i t,
      RRfwd_assign2 x (l, i) t = if (Ident.eqb x i) then false else t.
  Proof. i. unfold RRfwd_assign2. des_ifs. Qed.



  Lemma RRfwd_load2_kspec:
    forall l1 x o l2 i, knowledge_spec bool_le false (RRfwd_load2 l1 x o (l2, i)).
  Proof.
    i. unfold knowledge_spec. split; red; i.
    - unfold RRfwd_load2. unfold distl, dists. des_ifs; ss; clarify.
    - unfold RRfwd_load2. unfold distl, dists. des_ifs; ss; clarify; auto.
      all: try (left; refl).
  Qed.

  Lemma RRfwd_write2_kspec:
    forall l1 l2 i, knowledge_spec bool_le false (RRfwd_write2 l1 (l2, i)).
  Proof.
    i. unfold knowledge_spec. split; red; i.
    - rewrite ! RRfwd_write2_ord. des_ifs.
    - rewrite ! RRfwd_write2_ord. des_ifs.
      right; refl. left; refl.
  Qed.

  Lemma RRfwd_fence_r2_kspec:
    forall o l i, knowledge_spec bool_le false (RRfwd_fence_r2 o (l, i)).
  Proof.
    i. hexploit (ord_inv2 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! RRfwd_fence_r2_ord1; auto.
      + rewrite ! RRfwd_fence_r2_ord1; auto. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! RRfwd_fence_r2_ord2; auto. refl.
      + rewrite ! RRfwd_fence_r2_ord2; auto. right; refl.
  Qed.

  Lemma RRfwd_fence_w2_kspec:
    forall o l i, knowledge_spec bool_le false (RRfwd_fence_w2 o (l, i)).
  Proof.
    i. hexploit (ord_inv3 o). i; des.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! RRfwd_fence_w2_ord1; auto.
      + rewrite ! RRfwd_fence_w2_ord1; auto. left; refl.
    - unfold knowledge_spec. split; red; i.
      + rewrite ! RRfwd_fence_w2_ord2; auto. refl.
      + rewrite ! RRfwd_fence_w2_ord2; auto. right; refl.
  Qed.

  Lemma RRfwd_assign2_kspec:
    forall x l i, knowledge_spec bool_le false (RRfwd_assign2 x (l, i)).
  Proof.
    i. unfold knowledge_spec. split; red; i.
    - rewrite ! RRfwd_assign2_ord. des_ifs.
    - rewrite ! RRfwd_assign2_ord. des_ifs. right; refl. left; refl.
  Qed.


  Lemma RRfwd2_kspec:
    forall (inst: Inst.t) li, knowledge_spec bool_le false (RRfwd_inst2 inst li).
  Proof.
    i. destruct li. destruct inst.
    1,7,8: unfold knowledge_spec; split; red; i; ss; clarify; auto.
    all: try (left; refl).
    all: unfold RRfwd_inst2.
    1,6: apply RRfwd_assign2_kspec.
    apply RRfwd_load2_kspec.
    apply RRfwd_write2_kspec.
    - eapply kspec_app; eauto. apply le_PreOrder. apply bool_bot_spec. apply RRfwd_write2_kspec. apply RRfwd_load2_kspec.
    - eapply kspec_app; eauto. apply le_PreOrder. apply bool_bot_spec. apply RRfwd_fence_w2_kspec. apply RRfwd_fence_r2_kspec.
  Qed.

  Lemma RRfwd2_sspec:
    forall li k, eq (RRfwd_inst2 Inst.skip li k) k.
  Proof. i. ss. Qed.


  Definition RRfwd2_fix4: FixOpt4.t :=
    @FixOpt4.mk_fix4
      boolML false bool_bot_spec N level_grounded
      (Loc.t * Ident.t) RRfwd_inst2 RRfwd2_kspec RRfwd2_sspec.

  Definition RRfwd2 := @update_block RRfwd2_fix4.

  Lemma RRfwd2_kspec2: forall blk p, knowledge_spec (MLattice.le boolML) false (RRfwd2 blk p).
  Proof.
    i. eapply (@update_block_is_knowledge RRfwd2_fix4).
  Qed.

  Theorem RRfwd2_fix: forall blk f (FUN: f = RRfwd2 blk) p,
      @n_fix bool (MLattice.eq boolML) (MLattice.eq_Equiv boolML) (f p) (S N).
  Proof.
    i. eapply (@update_block_fix RRfwd2_fix4). eauto.
  Qed.

End ANALYSIS2.



Section SETAUX.

  Let union := IdentSet.union.
  Let inter := IdentSet.inter.
  Let diff := IdentSet.diff.
  Let disjoint := IdentSet.disjoint.
  Let empty := IdentSet.empty.

  Lemma union_idm: forall x, IdentSet.eq (union x x) x.
  Proof.
    ii. split.
    - i. eapply IdentSet.union_spec in H. des; auto.
    - i. eapply IdentSet.union_spec. auto.
  Qed.

  Lemma union_empty_r: forall x, union x empty = x.
  Proof.
    i. apply IdentSet.eq_leibniz. ii. split; i.
    - apply IdentSet.union_spec in H. des; auto. apply IdentSet.empty_spec in H. clarify.
    - apply IdentSet.union_spec. auto.
  Qed.

  Lemma union_empty_l: forall x, union empty x = x.
  Proof.
    i. apply IdentSet.eq_leibniz. ii. split; i.
    - apply IdentSet.union_spec in H. des; auto. apply IdentSet.empty_spec in H. clarify.
    - apply IdentSet.union_spec. auto.
  Qed.

  Lemma diff_empty: forall x, diff x empty = x.
  Proof.
    i. apply IdentSet.eq_leibniz. ii. split; i.
    - apply IdentSet.diff_spec in H. des; auto.
    - apply IdentSet.diff_spec. split; auto. apply IdentSet.empty_spec.
  Qed.



  Lemma not_in_union:
    forall a x y, ~ IdentSet.In a (union x y) -> (~ IdentSet.In a x) /\ (~ IdentSet.In a y).
  Proof.
    ii. split; ii.
    - apply H. apply IdentSet.union_spec; auto.
    - apply H. apply IdentSet.union_spec; auto.
  Qed.

  Lemma not_in_inter:
    forall a x y, ~ IdentSet.In a (inter x y) -> (~ IdentSet.In a x) \/ (~ IdentSet.In a y).
  Proof.
    ii. hexploit IdentSet.inter_spec. i. eapply not_iff_compat in H0. eapply H0 in H; clear H0.
    apply not_and_or in H. auto.
  Qed.

  Lemma not_in_diff:
    forall a x y, ~ IdentSet.In a (diff x y) -> (~ IdentSet.In a x) \/ (IdentSet.In a y).
  Proof.
    ii. hexploit IdentSet.diff_spec. i. eapply not_iff_compat in H0. eapply H0 in H; clear H0.
    apply not_and_or in H. des; auto. apply NNPP in H. auto.
  Qed.

  Lemma not_in_remove:
    forall y x s, ~ IdentSet.In y (IdentSet.remove x s) -> (~ IdentSet.In y s) \/ (y = x).
  Proof.
    ii. hexploit IdentSet.remove_spec. i. eapply not_iff_compat in H0. eapply H0 in H; clear H0.
    apply not_and_or in H. des; auto. apply NNPP in H. auto.
  Qed.

  Lemma not_in_add:
    forall y x s, ~ IdentSet.In y (IdentSet.add x s) -> (y <> x) /\ (~ IdentSet.In y s).
  Proof.
    ii. hexploit IdentSet.add_spec. i. eapply not_iff_compat in H0. eapply H0 in H; clear H0.
    apply not_or_and in H. des; auto.
  Qed.

End SETAUX.

Ltac solve_set :=
  match goal with
  | [|- _ _ (IdentSet.union _ _)] => apply IdentSet.union_spec
  | [H: _ _ (IdentSet.union _ _) |- _] => apply IdentSet.union_spec in H; des
  | [H: ~ (_ _ (IdentSet.union _ _)) |- _ ] => apply not_in_union in H; des
  | [|- _ _ (IdentSet.inter _ _)] => apply IdentSet.inter_spec; split
  | [H: _ _ (IdentSet.inter _ _) |- _] => apply IdentSet.inter_spec in H; des
  | [H: ~ (_ _ (IdentSet.inter _ _)) |- _ ] => apply not_in_inter in H; des
  | [|- _ _ (IdentSet.diff _ _)] => apply IdentSet.Facts.diff_3
  | [H: _ _ (IdentSet.diff _ _) |- _] => apply IdentSet.diff_spec in H; des
  | [H: ~ (_ _ (IdentSet.diff _ _)) |- _ ] => apply not_in_diff in H; des
  | [|- _ _ (IdentSet.remove _ _)] => apply IdentSet.remove_spec; split
  | [H: _ _ (IdentSet.remove _ _) |- _] => apply IdentSet.remove_spec in H; des
  | [H: ~ (_ _ (IdentSet.remove _ _)) |- _ ] => apply not_in_remove in H; des
  | [|- _ _ (IdentSet.add _ _)] => apply IdentSet.add_spec
  | [H: _ _ (IdentSet.add _ _) |- _] => apply IdentSet.add_spec in H; des
  | [H: ~ (_ _ (IdentSet.add _ _)) |- _ ] => apply not_in_add in H; des
  | [H: IdentSet.In _ IdentSet.empty |- _ ] => apply IdentSet.empty_spec in H; clarify
  | [|- IdentSet.mem _ _ = true] => apply IdentSet.mem_spec
  | [H: IdentSet.mem _ _ = true |- _] => apply IdentSet.mem_spec in H
  | [|- IdentSet.mem _ _ = false] => apply IdentSet.Facts.not_mem_iff
  | [H: IdentSet.mem _ _ = false |- _] => apply IdentSet.Facts.not_mem_iff in H
  end; ii; auto.

Ltac rss := repeat solve_set.



Section FIXPOINT.

  Let base1 := Loc.t.
  Let base2 := (Loc.t * Ident.t)%type.
  Let val1 := IdentSet.t.
  Let val2 := bool.

  Definition embed (s: val1): Ident.t -> val2 := fun i => IdentSet.mem i s.

  Lemma embed_eq_iff:
    forall (s1 s2: val1),
      IdentSet.eq s1 s2 <-> (forall i, (embed s1) i = (embed s2) i).
  Proof.
    i. unfold embed. split; i.
    - match goal with | [|- ?a = ?b] => destruct a eqn:MEM1; destruct b eqn:MEM2; auto end.
      + rss. apply H in MEM1; clarify.
      + rss. apply H in MEM2. clarify.
    - ii. specialize H with a.
      match goal with | [H: ?a = ?b |- _] => destruct a eqn:MEM1; destruct b eqn:MEM2; clarify end.
      + rss.
      + rss. clarify.
  Qed.

  Lemma embed_le_iff:
    forall (s1 s2: val1),
      IdentSet.Subset s1 s2 <-> (forall i, bool_le ((embed s1) i) ((embed s2) i)).
  Proof.
    i. unfold embed. split; i.
    - match goal with | [|- bool_le ?a ?b] => destruct a eqn:MEM1; destruct b eqn:MEM2; clarify; auto end.
      rss. apply H in MEM1. clarify.
    - ii. specialize H with a.
      match goal with | [H: bool_le ?a ?b |- _] => destruct a eqn:MEM1; destruct b eqn:MEM2; clarify; auto end.
      all: rss.
      clarify.
  Qed.

  Lemma embed_inter:
    forall a b, embed (IdentSet.inter a b) = fun i => andb (embed a i) (embed b i).
  Proof.
    i. unfold embed. extensionality i.
    match goal with | [|- ?a = ?b] => destruct a eqn:MEM1; destruct b eqn:MEM2; auto end.
    - rss. apply Bool.andb_false_iff in MEM2. des.
      all: rss; clarify.
    - apply andb_prop in MEM2. des. rss.
  Qed.

  Lemma embed_remove:
    forall x i s,
      embed (IdentSet.remove x s) i = (if Ident.eqb x i then false else embed s i).
  Proof.
    i. unfold embed.
    match goal with | [|- ?a = ?b] => destruct a eqn:MEM1; destruct b eqn:MEM2; auto end.
    - des_ifs.
      + rss. apply Ident.eqb_eq in Heq. clarify.
      + rss. clarify.
    - des_ifs. rss. apply Ident.eqb_neq in Heq. clarify.
  Qed.

  Lemma embed_add:
    forall x i s,
      embed (IdentSet.add x s) i = (if Ident.eqb x i then true else embed s i).
  Proof.
    i. unfold embed.
    des_ifs; rss.
    - apply Ident.eqb_eq in Heq. left; auto.
    - apply Ident.eqb_neq in Heq.
      match goal with | [|- ?a = ?b] => destruct a eqn:MEM1; destruct b eqn:MEM2; auto end.
      + rss; clarify.
      + rss; clarify.
  Qed.

  Lemma embed_empty:
    forall i, embed IdentSet.empty i = false.
  Proof. ss. Qed.



  Lemma embed_assign:
    forall x p s i, embed (RRfwd_assign x p s) i = RRfwd_assign2 x (p, i) (embed s i).
  Proof.
    i. rewrite RRfwd_assign_ord. rewrite RRfwd_assign2_ord. apply embed_remove.
  Qed.

  Lemma embed_load:
    forall rhs lhs ord p s i,
      embed (RRfwd_load rhs lhs ord p s) i = RRfwd_load2 rhs lhs ord (p, i) (embed s i).
  Proof.
    i. hexploit (ord_inv1); i; des.
    - rewrite RRfwd_load_ord1; eauto. rewrite RRfwd_load2_ord1; eauto. destruct (Loc.eqb rhs p).
      apply embed_add. apply embed_remove.
    - rewrite RRfwd_load_ord2; eauto. rewrite RRfwd_load2_ord2; eauto. destruct (Loc.eqb rhs p).
      apply embed_empty. apply embed_remove.
    - rewrite RRfwd_load_ord3; eauto. rewrite RRfwd_load2_ord3; eauto.
  Qed.

  Lemma embed_write:
    forall lhs p s i,
      embed (RRfwd_write lhs p s) i = RRfwd_write2 lhs (p, i) (embed s i).
  Proof.
    i. rewrite RRfwd_write_ord. rewrite RRfwd_write2_ord. des_ifs.
  Qed.

  Lemma embed_fence_r:
    forall ord p s i,
      embed (RRfwd_fence_r ord p s) i = RRfwd_fence_r2 ord (p, i) (embed s i).
  Proof.
    i. hexploit (ord_inv2); i; des.
    - rewrite RRfwd_fence_r_ord1; eauto. rewrite RRfwd_fence_r2_ord1; eauto.
    - rewrite RRfwd_fence_r_ord2; eauto. rewrite RRfwd_fence_r2_ord2; eauto.
  Qed.

  Lemma embed_fence_w:
    forall ord p s i,
      embed (RRfwd_fence_w ord p s) i = RRfwd_fence_w2 ord (p, i) (embed s i).
  Proof.
    i. hexploit (ord_inv3); i; des.
    - rewrite RRfwd_fence_w_ord1; eauto. rewrite RRfwd_fence_w2_ord1; eauto.
    - rewrite RRfwd_fence_w_ord2; eauto. rewrite RRfwd_fence_w2_ord2; eauto.
  Qed.



  Lemma analysis_correct_embed:
    forall blk p s, embed (RRfwd_block blk p s) = fun i => RRfwd2 blk (p, i) (embed s i).
  Proof.
    induction blk using block_ind2; i; ss.
    { rewrite IHblk. extensionality i. destruct hd; auto.
      all: f_equal.
      apply embed_assign.
      apply embed_load.
      apply embed_write.
      ss. rewrite embed_write.  rewrite embed_load. ss.
      ss. rewrite embed_fence_w. rewrite embed_fence_r. ss.
      apply embed_assign.
    }
    - rewrite IHblk3. extensionality i. rewrite embed_inter. f_equal.
      rewrite IHblk1. rewrite IHblk2. auto.
    - rewrite IHblk2. extensionality i. rewrite embed_inter. f_equal.
      do 2 rewrite IHblk1.  auto.
  Qed.


  Lemma analysis_fold_embed:
    forall n blk p i t,
      embed (fold_n (RRfwd_block blk p) n t) i = fold_n (RRfwd2 blk (p, i)) n (embed t i).
  Proof.
    induction n; i; ss.
    rewrite analysis_correct_embed. rewrite IHn. auto.
  Qed.

  Lemma embed_fix_fix:
    forall blk n p
      (FIX: forall i, @n_fix bool (MLattice.eq boolML) (MLattice.eq_Equiv boolML) (RRfwd2 blk (p, i)) n)
    ,
      @n_fix IdentSet.t (MLattice.eq IdentSetML) (MLattice.eq_Equiv IdentSetML) (block_d blk p) n.
  Proof.
    rewrite <- analysis_correct. i.
    unfold n_fix, is_fix, is_fix_point in *. i.
    ss. apply embed_eq_iff. i. rewrite fold_n_one_out.
    rewrite ! analysis_fold_embed. ss.
  Qed.

  Theorem block_d_fix: forall blk f (FUN: f = block_d blk) p,
      @n_fix IdentSet.t (MLattice.eq IdentSetML) (MLattice.eq_Equiv IdentSetML) (f p) (S N).
  Proof.
    i. clarify. ss. rewrite <- analysis_correct. eapply embed_fix_fix. i. eapply RRfwd2_fix; eauto.
  Qed.

  Theorem block_d_dec: forall blk p d f (FUN: f = block_d blk p), (MLattice.le IdentSetML) (f (f d)) (f d).
  Proof.
    i. clarify. ss. rewrite <- analysis_correct. apply embed_le_iff. i.
    match goal with | [|- bool_le ?a _] => replace a with (embed (fold_n (RRfwd_block blk p) 2 d) i) end.
    2:{ ss. }
    rewrite analysis_fold_embed. rewrite analysis_correct_embed.
    hexploit (knowledge_le_n bool_eq_leibniz (@MLattice.le_PartialOrder boolML) bool_bot_spec 1 (RRfwd2_kspec2 blk (p, i))).
    i. eauto.
  Qed.

End FIXPOINT.
