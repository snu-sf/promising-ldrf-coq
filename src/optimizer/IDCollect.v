Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Axioms.

Require Import ITreeLang.

Set Implicit Arguments.



Section ID.

  Definition id_table := Ident.t -> bool.
  Definition bot : id_table := fun _ => false.

  Definition le (t1 t2: id_table) : Prop :=
    forall i, (t1 i = true) -> (t2 i = true).

  Definition id_update (ids: id_table) (id: Ident.t) : id_table :=
    fun i => if (Ident.eqb id i) then true else (ids i).

  Definition p_join {T} (a b: T -> bool) : T -> bool :=
    fun t => (orb (a t) (b t)).

  Fixpoint id_update_expr (ids: id_table) (ex: Inst.expr) : id_table :=
    match ex with
    | Inst.expr_var id => id_update ids id
    | Inst.expr_val _ => ids
    | Inst.expr_op1 _ e => id_update_expr ids e
    | Inst.expr_op2 _ e1 e2 =>
      let ids1 := id_update_expr ids e1 in
      id_update_expr ids1 e2
    end .

  Definition id_update_exprs (ids: id_table) (exs: list Inst.expr) : id_table :=
    fold_left id_update_expr exs ids.

  Fixpoint get_id_table (ids: id_table) (blk: block) : id_table :=
    match blk with
    | nil => ids
    | cons hd tl =>
      match hd with
      | inst i =>
        match i with
        | Inst.skip
        | Inst.fence _ _
        | Inst.abort =>
          get_id_table ids tl
        | Inst.store _ ex _ =>
          let ids1 := id_update_expr ids ex in
          get_id_table ids1 tl
        | Inst.load id _ _
        | Inst.update id _ _ _ _
        | Inst.choose id =>
          let ids1 := id_update ids id in
          get_id_table ids1 tl
        | Inst.assign id ex =>
          let ids1 := id_update_expr ids ex in
          let ids2 := id_update ids1 id in
          get_id_table ids2 tl
        | Inst.syscall id exs =>
          let ids1 := id_update_exprs ids exs in
          let ids2 := id_update ids1 id in
          get_id_table ids2 tl
        end

      | ite ex b1 b2 =>
        let ids1 := get_id_table ids b1 in
        let ids2 := get_id_table ids b2 in
        let ids3 := p_join ids1 ids2 in
        let ids4 := id_update_expr ids3 ex in
        get_id_table ids4 tl
      | while ex b =>
        let ids1 := get_id_table ids b in
        let ids2 := id_update_expr ids1 ex in
        get_id_table ids2 tl
      end
    end
  .

End ID.



Global Program Instance le_PreOrder: PreOrder le.
Next Obligation.
Proof.
  ii. auto.
Qed.
Next Obligation.
Proof.
  ii. unfold le in *. eauto.
Qed.



Section IDPROOF1.

  Lemma strict_order:
    forall a b, (le a b /\ le b a) <-> a = b.
  Proof.
    split; i.
    - des. unfold le in *. extensionality i.
      destruct (a i) eqn:A; destruct (b i) eqn:B; ss; clarify.
      + apply H in A. clarify.
      + apply H0 in B. clarify.
    - rewrite H. split; refl.
  Qed.


  Lemma bot_spec:
    forall tb, le bot tb.
  Proof. ii. unfold bot in H. clarify. Qed.

  Lemma id_update_inc:
    forall tb id, le tb (id_update tb id).
  Proof. ii. unfold id_update. des_ifs. Qed.

  Lemma id_update_mon:
    forall tb1 tb2 id (LE: le tb1 tb2),
      le (id_update tb1 id) (id_update tb2 id).
  Proof.
    ii. unfold le in LE. unfold id_update in *. des_ifs. eauto.
  Qed.

  Lemma id_update_comm:
    forall tb id1 id2, id_update (id_update tb id1) id2 = id_update (id_update tb id2) id1.
  Proof.
    ii. unfold id_update. extensionality i. des_ifs.
  Qed.

  Lemma id_update_idm:
    forall tb id, id_update (id_update tb id) id = id_update tb id.
  Proof.
    ii. unfold id_update. extensionality i. des_ifs.
  Qed.

  Lemma id_update_eq_i:
    forall id tb1 tb2 i (EQ: tb1 i = tb2 i),
      id_update tb1 id i = id_update tb2 id i.
  Proof. i. unfold id_update. des_ifs. Qed.

End IDPROOF1.



Section IDPROOF2.

  Lemma p_join_inc_l:
    forall a b, le a (p_join a b).
  Proof. ii. unfold p_join. rewrite H. auto. Qed.

  Lemma p_join_inc_r:
    forall a b, le b (p_join a b).
  Proof. ii. unfold p_join. rewrite H. rewrite Bool.orb_true_r. auto. Qed.

  Lemma p_join_mon:
    forall a1 a2 b1 b2 (LE1: le a1 a2) (LE2: le b1 b2),
      le (p_join a1 b1) (p_join a2 b2).
  Proof.
    ii. unfold p_join, le in *. apply Bool.orb_prop in H. des.
    - rewrite LE1; auto.
    - rewrite LE2; auto. rewrite Bool.orb_true_r. auto.
  Qed.

  Lemma id_update_p_join_comm:
    forall a b id,
      id_update (p_join a b) id = p_join (id_update a id) (id_update b id).
  Proof.
    ii. unfold p_join, id_update. extensionality i. des_ifs.
  Qed.

  Lemma p_join_mix:
    forall {T} (a b c d: T -> bool),
      p_join (p_join a b) (p_join c d) =
      p_join (p_join a c) (p_join b d).
  Proof.
    i. extensionality i. unfold p_join.
    repeat rewrite Bool.orb_assoc. f_equal.
    repeat rewrite <- Bool.orb_assoc. f_equal.
    apply Bool.orb_comm.
  Qed.

  Lemma p_join_comm:
    forall {T} (a b: T -> bool), p_join a b = p_join b a.
  Proof. i. extensionality i. unfold p_join. apply Bool.orb_comm. Qed.

  Lemma p_join_idm:
    forall {T} (a: T -> bool), p_join a a = a.
  Proof. i. extensionality i. unfold p_join. apply Bool.orb_diag. Qed.

  Lemma p_join_max_r:
    forall a b (LE: le a b),
      p_join a b = b.
  Proof.
    i. extensionality i. unfold p_join, le in *.
    destruct (a i) eqn:A; destruct (b i) eqn:B; ss; clarify.
    apply LE in A. clarify.
  Qed.

  Lemma p_join_max_l:
    forall a b (LE: le b a),
      p_join a b = a.
  Proof.
    i. extensionality i. unfold p_join, le in *.
    destruct (a i) eqn:A; destruct (b i) eqn:B; ss; clarify.
    apply LE in B. clarify.
  Qed.

  Lemma id_update_p_join_comp:
    forall tb id1 id2,
      p_join (id_update tb id1) (id_update tb id2) =
      id_update (id_update tb id1) id2.
  Proof.
    i. extensionality i. unfold id_update, p_join. des_ifs.
    - apply Bool.orb_true_r.
    - apply Bool.orb_diag.
  Qed.

  Lemma p_join_eq_i:
    forall {T} (a b c d: T -> bool) i (EQ1: a i = c i) (EQ2: b i = d i),
      p_join a b i = p_join c d i.
  Proof.
    i. unfold p_join. rewrite EQ1; rewrite EQ2. auto.
  Qed.

  Lemma p_join_des:
    forall {T} (a b: T -> bool) i (TRUE: p_join a b i),
      (a i) \/ (b i).
  Proof.
    i. unfold p_join in TRUE. apply Bool.orb_prop in TRUE. des; auto.
  Qed.

End IDPROOF2.



Section IDPROOF3.

  Lemma id_update_expr_inc:
    forall ex tb, le tb (id_update_expr tb ex).
  Proof.
    induction ex; i; ss.
    - apply id_update_inc.
    - etrans; eauto.
  Qed.

  Lemma id_update_expr_mon:
    forall ex tb1 tb2 (LE: le tb1 tb2),
      le (id_update_expr tb1 ex) (id_update_expr tb2 ex).
  Proof.
    induction ex; i; ss; eauto.
    apply id_update_mon; auto.
  Qed.

  Lemma id_update_id_expr_comm:
    forall ex id tb,
      id_update_expr (id_update tb id) ex =
      id_update (id_update_expr tb ex) id.
  Proof.
    induction ex; i; ss; eauto.
    - apply id_update_comm.
    - rewrite IHex1. rewrite IHex2. auto.
  Qed.

  Lemma id_update_expr_comm:
    forall ex1 ex2 tb,
      id_update_expr (id_update_expr tb ex1) ex2 =
      id_update_expr (id_update_expr tb ex2) ex1.
  Proof.
    induction ex1; i; ss; eauto.
    - apply id_update_id_expr_comm.
    - rewrite IHex1_2. rewrite IHex1_1. auto.
  Qed.

  Lemma id_update_expr_idm:
    forall ex tb, id_update_expr (id_update_expr tb ex) ex = id_update_expr tb ex.
  Proof.
    induction ex; i; ss; eauto.
    - apply id_update_idm.
    - rewrite (id_update_expr_comm ex2 ex1). rewrite IHex1. rewrite IHex2. auto.
  Qed.

  Lemma id_update_expr_p_join_comm:
    forall ex a b,
      id_update_expr (p_join a b) ex = p_join (id_update_expr a ex) (id_update_expr b ex).
  Proof.
    induction ex; i; ss; eauto.
    - apply id_update_p_join_comm.
    - rewrite IHex1. rewrite IHex2. auto.
  Qed.

  Lemma id_update_expr_eq_i:
    forall ex tb1 tb2 i (EQ: tb1 i = tb2 i),
      id_update_expr tb1 ex i = id_update_expr tb2 ex i.
  Proof.
    induction ex; i; ss; auto. apply id_update_eq_i; auto.
  Qed.


  Lemma id_update_exprs_inc:
    forall exs tb, le tb (id_update_exprs tb exs).
  Proof.
    induction exs; i; ss.
    etrans. 2:eauto. apply id_update_expr_inc.
  Qed.

  Lemma id_update_exprs_mon:
    forall exs tb1 tb2 (LE: le tb1 tb2),
      le (id_update_exprs tb1 exs) (id_update_exprs tb2 exs).
  Proof.
    induction exs; i; ss; eauto.
    apply IHexs. apply id_update_expr_mon; auto.
  Qed.

  Lemma id_update_id_exprs_comm:
    forall exs id tb,
      id_update (id_update_exprs tb exs) id =
      id_update_exprs (id_update tb id) exs.
  Proof.
    induction exs; i; ss; eauto.
    rewrite IHexs. rewrite id_update_id_expr_comm. auto.
  Qed.

  Lemma id_update_expr_exprs_comm:
    forall ex exs tb,
      id_update_expr (id_update_exprs tb exs) ex =
      id_update_exprs (id_update_expr tb ex) exs.
  Proof.
    induction ex; i; ss; eauto.
    - apply id_update_id_exprs_comm.
    - rewrite IHex1. rewrite IHex2. auto.
  Qed.

  Lemma id_update_exprs_comm:
    forall exs1 exs2 tb,
      id_update_exprs (id_update_exprs tb exs1) exs2 =
      id_update_exprs (id_update_exprs tb exs2) exs1.
  Proof.
    induction exs1; i; ss; eauto.
    rewrite IHexs1. rewrite id_update_expr_exprs_comm. auto.
  Qed.

  Lemma id_update_exprs_idm:
    forall exs tb, id_update_exprs (id_update_exprs tb exs) exs = id_update_exprs tb exs.
  Proof.
    induction exs; i; ss; eauto.
    rewrite id_update_expr_exprs_comm. rewrite id_update_expr_idm. auto.
  Qed.

  Lemma id_update_exprs_p_join_comm:
    forall exs a b,
      id_update_exprs (p_join a b) exs =
      p_join (id_update_exprs a exs) (id_update_exprs b exs).
  Proof.
    induction exs; i; ss; eauto.
    rewrite id_update_expr_p_join_comm. rewrite IHexs. auto.
  Qed.

  Lemma id_update_exprs_eq_i:
    forall exs tb1 tb2 i (EQ: tb1 i = tb2 i),
      id_update_exprs tb1 exs i = id_update_exprs tb2 exs i.
  Proof.
    induction exs; i; ss; auto. apply IHexs. apply id_update_expr_eq_i; auto.
  Qed.

End IDPROOF3.



Section IDPROOF4.

  Lemma get_id_table_inc:
    forall blk tb, le tb (get_id_table tb blk).
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: etrans; [|eauto].
      2,4,6: apply id_update_inc.
      - etrans. 2: eapply id_update_inc. apply id_update_expr_inc.
      - apply id_update_expr_inc.
      - etrans. 2: eapply id_update_inc. apply id_update_exprs_inc.
    }
    - etrans. 2: eauto.
      etrans. 2: eapply id_update_expr_inc.
      etrans. 2: eapply p_join_inc_l.
      eauto.
    - etrans. 2: eauto.
      etrans. 2: eapply id_update_expr_inc.
      eauto.
  Qed.

  Lemma get_id_table_mon:
    forall blk tb1 tb2 (LE: le tb1 tb2),
      le (get_id_table tb1 blk) (get_id_table tb2 blk).
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: eapply IHblk.
      1,2,4,5,6: apply id_update_mon; auto.
      1,3: apply id_update_expr_mon; auto.
      apply id_update_exprs_mon; auto.
    }
    - apply IHblk3. apply id_update_expr_mon. apply p_join_mon; eauto.
    - apply IHblk2. apply id_update_expr_mon. eauto.
  Qed.

  Lemma get_id_table_id_comm:
    forall blk id tb,
      id_update (get_id_table tb blk) id =
      get_id_table (id_update tb id) blk.
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: rewrite IHblk.
      all: try rewrite id_update_comm.
      all: auto.
      all: try rewrite id_update_id_expr_comm.
      all: auto.
      rewrite id_update_id_exprs_comm. auto.
    }
    - rewrite IHblk3. rewrite <- id_update_id_expr_comm. do 2 f_equal.
      rewrite id_update_p_join_comm. f_equal; auto.
    - rewrite IHblk2. rewrite <- id_update_id_expr_comm. do 2 f_equal.
      auto.
  Qed.

  Lemma get_id_table_expr_comm:
    forall blk ex tb,
      id_update_expr (get_id_table tb blk) ex =
      get_id_table (id_update_expr tb ex) blk.
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: rewrite IHblk.
      all: f_equal.
      all: try rewrite id_update_id_expr_comm; auto.
      all: try rewrite id_update_expr_comm; auto.
      rewrite id_update_expr_exprs_comm; auto.
    }
    - rewrite IHblk3. rewrite <- id_update_expr_comm. do 2 f_equal.
      rewrite id_update_expr_p_join_comm. f_equal; auto.
    - rewrite IHblk2. rewrite <- id_update_expr_comm. do 2 f_equal.
      auto.
  Qed.

  Lemma get_id_table_exprs_comm:
    forall blk exs tb,
      id_update_exprs (get_id_table tb blk) exs =
      get_id_table (id_update_exprs tb exs) blk.
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: rewrite IHblk.
      all: f_equal.
      all: try rewrite id_update_id_exprs_comm; auto.
      all: try rewrite id_update_expr_exprs_comm; auto.
      all: try rewrite id_update_id_exprs_comm; auto.
      rewrite id_update_id_exprs_comm. rewrite id_update_exprs_comm. auto.
    }
    - rewrite IHblk3. rewrite <- id_update_expr_exprs_comm. do 2 f_equal.
      rewrite id_update_exprs_p_join_comm. f_equal; auto.
    - rewrite IHblk2. rewrite <- id_update_expr_exprs_comm. do 2 f_equal.
      auto.
  Qed.

  Lemma get_id_table_p_join_comm:
    forall blk a b,
      p_join (get_id_table a blk) (get_id_table b blk) =
      get_id_table (p_join a b) blk.
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: rewrite IHblk; f_equal; symmetry.
      all: try apply id_update_p_join_comm.
      all: try apply id_update_expr_p_join_comm.
      1: rewrite id_update_expr_p_join_comm; rewrite id_update_p_join_comm; auto.
      rewrite id_update_exprs_p_join_comm; rewrite id_update_p_join_comm; auto.
    }
    - rewrite IHblk3. rewrite <- id_update_expr_p_join_comm. do 2 f_equal.
      rewrite <- IHblk1. rewrite <- IHblk2. apply p_join_mix.
    - rewrite IHblk2. rewrite <- id_update_expr_p_join_comm. do 2 f_equal.
      auto.
  Qed.

  Lemma get_id_table_comm:
    forall blk1 blk2 tb,
      get_id_table (get_id_table tb blk1) blk2 =
      get_id_table (get_id_table tb blk2) blk1.
  Proof.
    induction blk1 using block_ind2; i; ss.
    { destruct hd; eauto.
      all: rewrite IHblk1; f_equal.
      all: try rewrite get_id_table_id_comm; auto.
      all: try rewrite get_id_table_expr_comm; auto.
      all: rewrite <- get_id_table_id_comm; auto.
      rewrite get_id_table_exprs_comm. auto.
    }
    - rewrite IHblk1_3. f_equal.
      rewrite <- get_id_table_expr_comm. f_equal.
      rewrite <- get_id_table_p_join_comm. f_equal; auto.
    - rewrite IHblk1_2. f_equal. rewrite <- get_id_table_expr_comm. f_equal. auto.
  Qed.

  Lemma get_id_table_add:
    forall b1 b2 tb,
      get_id_table tb (add_block b1 b2) = get_id_table (get_id_table tb b1) b2.
  Proof.
    induction b1 using block_ind2; i; ss.
    destruct hd; eauto.
  Qed.

  Lemma get_id_table_eq_i:
    forall b tb1 tb2 i (EQ: tb1 i = tb2 i),
      get_id_table tb1 b i = get_id_table tb2 b i.
  Proof.
    induction b using block_ind2; i; ss; auto.
    { destruct hd; auto.
      all: apply IHb; auto.
      all: try apply id_update_eq_i; auto.
      all: try apply id_update_expr_eq_i; auto.
      apply id_update_exprs_eq_i; auto.
    }
    - apply IHb3. apply id_update_expr_eq_i. apply p_join_eq_i; auto.
    - apply IHb2. apply id_update_expr_eq_i. auto.
  Qed.

  Lemma get_id_table_false:
    forall b tb i (FALSE: tb i = false),
      get_id_table bot b i = get_id_table tb b i.
  Proof.
    i. apply get_id_table_eq_i. auto.
  Qed.

  Lemma get_id_table_true_des:
    forall b1 b2 tb i (TRUE: get_id_table (get_id_table tb b1) b2 i = true),
      (get_id_table tb b1 i = true) \/ (get_id_table tb b2 i = true).
  Proof.
    i. destruct (get_id_table tb b1 i) eqn:CASE; auto.
    right. eapply get_id_table_false in CASE. rewrite TRUE in CASE.
    hexploit bot_spec; i.
    eapply get_id_table_mon in H. unfold le in H. specialize H with i.
    hexploit H; eauto.
  Qed.

  Lemma get_id_table_add_p_join:
    forall b1 b2 tb,
      get_id_table (get_id_table tb b1) b2 =
      p_join (get_id_table tb b1) (get_id_table tb b2).
  Proof.
    i. apply strict_order. split.
    - ii. apply get_id_table_true_des in H. unfold p_join. des.
      + rewrite H. auto.
      + rewrite H. apply Bool.orb_true_r.
    - ii. unfold p_join in H. apply Bool.orb_prop in H. des.
      + hexploit get_id_table_inc. i. unfold le in H0. specialize H0 with i.
        hexploit H0; eauto.
      + rewrite get_id_table_comm.
        hexploit get_id_table_inc. i. unfold le in H0. specialize H0 with i.
        hexploit H0; eauto.
  Qed.

  Lemma get_id_table_idm:
    forall blk tb, get_id_table (get_id_table tb blk) blk = get_id_table tb blk.
  Proof.
    induction blk using block_ind2; i; ss.
    { destruct hd; eauto.
      all: try rewrite get_id_table_id_comm.
      all: try rewrite IHblk.
      all: try rewrite id_update_idm; auto.
      all: try rewrite get_id_table_expr_comm.
      3: rewrite get_id_table_exprs_comm.
      1,3: rewrite get_id_table_id_comm.
      all: rewrite IHblk; f_equal.
      3: apply id_update_expr_idm.
      1: rewrite id_update_id_expr_comm.
      2: rewrite id_update_id_exprs_comm.
      all: rewrite id_update_idm.
      1: rewrite id_update_expr_idm; auto.
      rewrite id_update_id_exprs_comm. rewrite id_update_exprs_idm. auto.
    }
    - rewrite <- ! get_id_table_expr_comm.
      rewrite <- id_update_expr_p_join_comm.
      rewrite <- get_id_table_expr_comm. rewrite id_update_expr_idm. f_equal.
      rewrite <- get_id_table_p_join_comm.
      match goal with
      | [|- p_join ?a _ = _] =>
        replace a with
            (get_id_table (get_id_table (p_join (get_id_table tb blk1) (get_id_table tb blk2)) blk1) blk3) end.
      2:{ symmetry. rewrite get_id_table_comm. rewrite IHblk3. rewrite get_id_table_comm.
          auto.
      }
      match goal with
      | [|- p_join _ ?a = _] =>
        replace a with
            (get_id_table (get_id_table (p_join (get_id_table tb blk1) (get_id_table tb blk2)) blk2) blk3) end.
      2:{ symmetry. rewrite get_id_table_comm. rewrite IHblk3. rewrite get_id_table_comm.
          auto.
      }
      rewrite get_id_table_p_join_comm. f_equal.
      match goal with
      | [|- p_join ?a _ = ?b] => replace a with b end.
      2:{ symmetry. rewrite <- get_id_table_p_join_comm. rewrite IHblk1.
          rewrite get_id_table_comm. rewrite get_id_table_add_p_join.
          rewrite p_join_max_r; auto. apply p_join_inc_l.
      }
      match goal with
      | [|- p_join _ ?a = ?b] => replace a with b end.
      2:{ symmetry. rewrite <- get_id_table_p_join_comm. rewrite IHblk2.
          rewrite get_id_table_add_p_join.
          rewrite p_join_max_l; auto. apply p_join_inc_r.
      }
      apply p_join_idm.

    - rewrite <- ! get_id_table_expr_comm. rewrite id_update_expr_idm. f_equal.
      rewrite get_id_table_comm. rewrite IHblk2.
      rewrite get_id_table_comm. rewrite IHblk1. auto.
  Qed.

End IDPROOF4.





Section MAXID.

  Definition bot_id := ret_reg.

  Fixpoint id_max_expr (idm: Ident.t) (ex: Inst.expr) : Ident.t :=
    match ex with
    | Inst.expr_var id => Ident.max idm id
    | Inst.expr_val _ => idm
    | Inst.expr_op1 _ e => id_max_expr idm e
    | Inst.expr_op2 _ e1 e2 =>
      let idm1 := id_max_expr idm e1 in
      id_max_expr idm1 e2
    end .

  Definition id_max_exprs (idm: Ident.t) (exs: list Inst.expr) : Ident.t :=
    fold_left id_max_expr exs idm.

  Definition id_max_inst (idm: Ident.t) (i: Inst.t) : Ident.t :=
    match i with
    | Inst.skip
    | Inst.fence _ _
    | Inst.abort =>
      idm
    | Inst.store _ ex _ =>
      id_max_expr idm ex
    | Inst.load id _ _
    | Inst.update id _ _ _ _
    | Inst.choose id =>
      Ident.max idm id
    | Inst.assign id ex =>
      let idm1 := id_max_expr idm ex in
      Ident.max idm1 id
    | Inst.syscall id exs =>
      let idm1 := id_max_exprs idm exs in
      Ident.max idm1 id
    end
  .

  Fixpoint id_max_block (idm: Ident.t) (blk: block) : Ident.t :=
    match blk with
    | nil => idm
    | cons hd tl =>
      match hd with
      | inst i =>
        let idm1 := id_max_inst idm i in
        id_max_block idm1 tl

      | ite ex b1 b2 =>
        let idm1 := id_max_block idm b1 in
        let idm2 := id_max_block idm b2 in
        let idm3 := Ident.max idm1 idm2 in
        let idm4 := id_max_expr idm3 ex in
        id_max_block idm4 tl

      | while ex b =>
        let idm1 := id_max_block idm b in
        let idm2 := id_max_expr idm1 ex in
        id_max_block idm2 tl
      end
    end
  .

End MAXID.



Section MAXIDPROOF.

  Let le_g := Ident.le.
  Let bot_g := bot_id.
  Let join_g := Ident.max.
  Let expr_g := id_max_expr.
  Let exprs_g := id_max_exprs.
  Let inst_g := id_max_inst.

  Lemma bot_id_spec:
    forall gd, le_g bot_g gd.
  Proof. eapply Ident.le_1_l. Qed.


  Lemma join_id_refl:
    forall a, join_g a a = a.
  Proof. eapply Ident.max_id. Qed.

  Lemma join_le_id_l:
    forall a b, le_g a (join_g a b).
  Proof. eapply Ident.le_max_l. Qed.

  Lemma join_le_id_r:
    forall a b, le_g b (join_g a b).
  Proof. eapply Ident.le_max_r. Qed.

  Lemma join_id_mon:
    forall a b c d (LE1: le_g a c) (LE2: le_g b d), le_g (join_g a b) (join_g c d).
  Proof.
    i. eapply Ident.max_lub_iff. split.
    - etrans; eauto. eapply Ident.le_max_l.
    - etrans; eauto. eapply Ident.le_max_r.
  Qed.


  Lemma expr_id_inc:
    forall ex gd, le_g gd (expr_g gd ex).
  Proof.
    induction ex; i; ss; clarify.
    - eapply join_le_id_l.
    - refl.
    - etrans. 2: eapply IHex2. eauto.
  Qed.

  Lemma expr_id_mon:
    forall ex gd1 gd2 (LE: le_g gd1 gd2), le_g (expr_g gd1 ex) (expr_g gd2 ex).
  Proof.
    induction ex; i; ss; clarify; eauto.
    eapply join_id_mon; eauto. refl.
  Qed.

  Lemma expr_id_big:
    forall ex gd (BIG: le_g (expr_g bot_g ex) gd), expr_g gd ex = gd.
  Proof.
    induction ex; i; ss; clarify; eauto.
    - rewrite Ident.max_1_l in BIG. eapply Ident.max_l. auto.
    - erewrite IHex1.
      2:{ etrans. 2: eapply BIG. etrans. 2: eapply expr_id_inc. refl. }
      eapply IHex2. etrans. 2: eapply BIG. eapply expr_id_mon. eapply bot_id_spec.
  Qed.


  Lemma exprs_id_inc:
    forall exs gd, le_g gd (exprs_g gd exs).
  Proof.
    induction exs; i; ss; clarify. refl.
    etrans. 2: eapply IHexs. eapply expr_id_inc.
  Qed.

  Lemma exprs_id_mon:
    forall exs gd1 gd2 (LE: le_g gd1 gd2), le_g (exprs_g gd1 exs) (exprs_g gd2 exs).
  Proof.
    induction exs; i; ss; clarify; eauto.
    eapply IHexs. eapply expr_id_mon; eauto.
  Qed.

  Lemma exprs_id_big:
    forall exs gd (BIG: le_g (exprs_g bot_g exs) gd), exprs_g gd exs = gd.
  Proof.
    induction exs; i; ss; clarify; eauto.
    rewrite expr_id_big.
    2:{ etrans. 2: eapply BIG. etrans. 2: eapply exprs_id_inc. refl. }
    eapply IHexs. etrans. 2: eapply BIG. eapply exprs_id_mon. eapply bot_id_spec.
  Qed.


  Lemma inst_id_inc:
    forall gd i, le_g gd (inst_g gd i).
  Proof.
    i. destruct i; ss. all: try refl.
    all: try eapply join_le_id_l.
    - etrans. 2: eapply join_le_id_l. eapply expr_id_inc.
    - eapply expr_id_inc.
    - etrans. 2: eapply join_le_id_l. eapply exprs_id_inc.
  Qed.

  Lemma inst_id_mon:
    forall gd1 gd2 i (LE: le_g gd1 gd2), le_g (inst_g gd1 i) (inst_g gd2 i).
  Proof.
    i. destruct i; ss.
    1,2,4,5,6: eapply join_id_mon; [eauto | refl].
    1,3: eapply expr_id_mon; eauto.
    eapply exprs_id_mon; eauto.
  Qed.

  Lemma inst_id_big:
    forall gd i (BIG: le_g (inst_g bot_g i) gd), inst_g gd i = gd.
  Proof.
    i. destruct i; ss.
    2,4,6: eapply Ident.max_l; etrans; [eapply join_le_id_r | eapply BIG].
    1,2: rewrite expr_id_big; eauto.
    2:{ etrans. 2: eapply BIG. eapply join_le_id_l. }
    - eapply Ident.max_l. etrans. 2: eapply BIG. eapply join_le_id_r.
    - rewrite exprs_id_big.
      2:{ etrans. 2: eapply BIG. eapply join_le_id_l. }
      eapply Ident.max_l. etrans. 2: eapply BIG. eapply join_le_id_r.
  Qed.

  Lemma inst_id_skip:
    forall gd, inst_g gd (Inst.skip) = gd.
  Proof. ss. Qed.

End MAXIDPROOF.





Section NEWID.

  Definition nextID (id: Ident.t) := Ident.succ id.
  Definition newID (code: block) := nextID (id_max_block bot_id code).

End NEWID.



Section NEWIDPROOF.

  Lemma gt_id_not_orig:
    forall code orig id
      (ORIG: orig = get_id_table bot code)
      (GT: forall id0, (orig id0) -> (Ident.lt id0 id))
    ,
      orig id = false.
  Proof.
    induction code using block_ind2; i; ss; clarify.
    { destruct hd; ss; auto.
      - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
        exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
      - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
        exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
      - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
        exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
      - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
        exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
      - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
        exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
      - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
        exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
    }
    - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
      exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
    - match goal with | [|- ?a = _ ] => destruct a eqn:CASE; auto end.
      exfalso. eapply GT in CASE. apply Ident.lt_irrefl in CASE. auto.
  Qed.


  Lemma id_update_max:
    forall v id0 (tb: id_table) id
      (LE: forall i, (tb i) -> Ident.le i id)
      (ORIG: id_update tb v id0)
    ,
      Ident.le id0 (Ident.max id v).
  Proof.
    i. unfold id_update in ORIG. des_ifs.
    - rewrite Ident.eqb_eq in Heq. clarify. apply Ident.le_max_r.
    - apply LE in ORIG. etrans; eauto. apply Ident.le_max_l.
  Qed.

  Lemma id_update_expr_max:
    forall ex id0 (tb: id_table) id
      (LE: forall i, (tb i) -> Ident.le i id)
      (ORIG: id_update_expr tb ex id0)
    ,
      Ident.le id0 (id_max_expr id ex).
  Proof.
    induction ex; i; ss; clarify; eauto.
    eapply id_update_max; eauto.
  Qed.

  Lemma id_update_exprs_max:
    forall exs id0 (tb: id_table) id
      (LE: forall i, (tb i) -> Ident.le i id)
      (ORIG: id_update_exprs tb exs id0)
    ,
      Ident.le id0 (id_max_exprs id exs).
  Proof.
    induction exs; i; ss; clarify; eauto.
    eapply IHexs; eauto. i. eapply id_update_expr_max; eauto.
  Qed.

  Lemma maxID_ge_orig:
    forall code id0 (tb: id_table) id
      (LE: forall i, (tb i) -> Ident.le i id)
      (ORIG: (get_id_table tb code) id0)
    ,
      Ident.le id0 (id_max_block id code).
  Proof.
    induction code using block_ind2; i; ss; clarify; eauto.
    { destruct hd; ss; eauto.
      all: eapply IHcode; eauto; i.
      all: try (eapply id_update_max; eauto; i).
      1,2: eapply id_update_expr_max; eauto.
      eapply id_update_exprs_max; eauto.
    }
    - eapply IHcode3; eauto. i. eapply id_update_expr_max; eauto. i.
      apply p_join_des in H0. des.
      + etrans; eauto. apply Ident.le_max_l.
      + etrans; eauto. apply Ident.le_max_r.
    - eapply IHcode2; eauto. i. eapply id_update_expr_max; eauto.
  Qed.

  Lemma newID_gt_orig:
    forall code id0
      (ORIG: (get_id_table bot code) id0)
    ,
      Ident.lt id0 (newID code).
  Proof.
    i. unfold newID. unfold nextID. apply Ident.lt_succ_r. eapply maxID_ge_orig; eauto.
    ii. unfold bot in H. clarify.
  Qed.

  Lemma newID_not_orig0:
    forall code, get_id_table bot code (newID code) = false.
  Proof.
    i. eapply gt_id_not_orig; auto. i. eapply newID_gt_orig; eauto.
  Qed.

  Lemma newID_not_orig:
    forall code id (LE: Ident.le (newID code) id),
      get_id_table bot code id = false.
  Proof.
    i. eapply gt_id_not_orig; eauto. i. eapply Ident.lt_le_trans; eauto. eapply newID_gt_orig; eauto.
  Qed.

End NEWIDPROOF.
