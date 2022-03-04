Set Implicit Arguments.

Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import ITreeLang.





Module Opt3.

  Record t :=
    mk_opt3
      {
        gdata: Type;
        bot_g: gdata;
        expr_g: gdata -> Inst.expr -> gdata;
        inst_g: gdata -> Inst.t -> gdata;
        join_g: gdata -> gdata -> gdata;
        
        le_g: gdata -> gdata -> Prop;
        le_g_PreOrder: PreOrder le_g;
        le_g_PartialOrder: PartialOrder eq le_g;

        bot_g_spec: forall gd, le_g bot_g gd;

        expr_g_inc: forall ex gd, le_g gd (expr_g gd ex);
        expr_g_mon: forall ex gd1 gd2 (LE: le_g gd1 gd2), le_g (expr_g gd1 ex) (expr_g gd2 ex);
        expr_g_big: forall ex gd (BIG: le_g (expr_g bot_g ex) gd), expr_g gd ex = gd;

        inst_g_inc: forall gd i, le_g gd (inst_g gd i);
        inst_g_mon: forall gd1 gd2 i (LE: le_g gd1 gd2), le_g (inst_g gd1 i) (inst_g gd2 i);
        inst_g_big: forall gd i (BIG: le_g (inst_g bot_g i) gd), inst_g gd i = gd;
        inst_g_skip: forall gd, inst_g gd (Inst.skip) = gd;

        join_g_refl: forall a, join_g a a = a;
        join_le_g_l: forall a b, le_g a (join_g a b);
        join_le_g_r: forall a b, le_g b (join_g a b);
        join_g_mon: forall a b c d (LE1: le_g a c) (LE2: le_g b d), le_g (join_g a b) (join_g c d);

        datum: Type;
        data := list datum;
        analyze: block -> data;

        update_g: gdata -> datum -> gdata;
        update_g_inc: forall g d, le_g g (update_g g d);
        update_g_mon: forall a b d (LE: le_g a b), le_g (update_g a d) (update_g b d);

        intro_inst: gdata -> datum -> Inst.t;
      }
  .

  Global Program Instance le_g_PreOrder_i: forall T, PreOrder (le_g T).
  Next Obligation.
  Proof.
    eapply PreOrder_Reflexive. Unshelve. apply (le_g_PreOrder T).
  Qed.
  Next Obligation.
  Proof.
    eapply PreOrder_Transitive. Unshelve. apply (le_g_PreOrder T).
  Qed.

  Global Program Instance le_g_PartialOrder_i: forall T, PartialOrder eq (le_g T).
  Next Obligation.
  Proof.
    assert (Antisymmetric (gdata T) eq (le_g T)).
    { eapply partial_order_antisym. eapply (le_g_PartialOrder T). }
    unfold relation_equivalence, relation_conjunction.
    unfold predicate_equivalence, predicate_intersection.
    unfold pointwise_lifting, pointwise_extension.
    i. split; i.
    - split.
      + clarify. refl.
      + unfold flip. clarify. refl.
    - des. eapply antisymmetry; eauto.
  Qed.

End Opt3.



Section OPT.

  Variable O3: Opt3.t.

  Let gdata: Type := Opt3.gdata O3.
  Let bot_g: gdata := Opt3.bot_g O3.
  Let expr_g: gdata -> Inst.expr -> gdata := Opt3.expr_g O3.
  Let inst_g: gdata -> Inst.t -> gdata := Opt3.inst_g O3.
  Let join_g: gdata -> gdata -> gdata := Opt3.join_g O3.

  Fixpoint block_g (gd: gdata) (blk: block) : gdata :=
    match blk with
    | nil => gd
    | cons hd tl =>
      match hd with
      | inst i =>
        let gd1 := inst_g gd i in
        block_g gd1 tl

      | ite ex b1 b2 =>
        let gd1 := block_g gd b1 in
        let gd2 := block_g gd b2 in
        let gd3 := join_g gd1 gd2 in
        let gd4 := expr_g gd3 ex in
        block_g gd4 tl

      | while ex b =>
        let gd1 := block_g gd b in
        let gd2 := expr_g gd1 ex in
        block_g gd2 tl
      end
    end
  .


  Let le_g: gdata -> gdata -> Prop := Opt3.le_g O3.
  Let le_g_PreOrder: PreOrder le_g := Opt3.le_g_PreOrder O3.
  Let le_g_PartialOrder: PartialOrder eq le_g := Opt3.le_g_PartialOrder O3.

  Program Instance le_g_PreOrder_i: PreOrder le_g.
  Program Instance le_g_PartialOrder_i: PartialOrder eq le_g.

  Definition lt_g gd1 gd2 := (le_g gd1 gd2) /\ (gd1 <> gd2).

  Program Instance lt_g_Transitive_i: Transitive lt_g.
  Next Obligation.
  Proof.
    unfold lt_g in *. des. split.
    - etrans; eauto.
    - ii. clarify. hexploit (partial_order_antisym le_g_PartialOrder). i.
      assert (AS: y = z).
      { eapply antisymmetry; eauto. }
      apply H1; auto.
  Qed.

  Lemma le_g_lt_g:
    forall a b c (LE: le_g a b) (LT: lt_g b c), lt_g a c.
  Proof.
    i. unfold lt_g in *. des. split.
    - etrans; eauto.
    - ii. clarify. assert (AS: b = c).
      { eapply antisymmetry; eauto. }
      clarify.
  Qed.

  Lemma le_g_lt_g2:
    forall a b c (LE: lt_g a b) (LT: le_g b c), lt_g a c.
  Proof.
    i. unfold lt_g in *. des. split.
    - etrans; eauto.
    - ii. clarify. assert (AS: c = b).
      { eapply antisymmetry; eauto. }
      clarify.
  Qed.


  Let bot_g_spec: forall gd, le_g bot_g gd := Opt3.bot_g_spec O3.

  Let expr_g_inc: forall ex gd, le_g gd (expr_g gd ex) := Opt3.expr_g_inc O3.
  Let expr_g_mon: forall ex gd1 gd2 (LE: le_g gd1 gd2), le_g (expr_g gd1 ex) (expr_g gd2 ex) := Opt3.expr_g_mon O3.
  Let expr_g_big: forall ex gd (BIG: le_g (expr_g bot_g ex) gd), expr_g gd ex = gd := Opt3.expr_g_big O3.

  Let inst_g_inc: forall gd i, le_g gd (inst_g gd i) := Opt3.inst_g_inc O3.
  Let inst_g_mon: forall gd1 gd2 i (LE: le_g gd1 gd2), le_g (inst_g gd1 i) (inst_g gd2 i) := Opt3.inst_g_mon O3.
  Let inst_g_big: forall gd i (BIG: le_g (inst_g bot_g i) gd), inst_g gd i = gd := Opt3.inst_g_big O3.
  Let inst_g_skip: forall gd, inst_g gd (Inst.skip) = gd := Opt3.inst_g_skip O3.

  Let join_g_refl: forall a, join_g a a = a := Opt3.join_g_refl O3.
  Let join_le_g_l: forall a b, le_g a (join_g a b) := Opt3.join_le_g_l O3.
  Let join_le_g_r: forall a b, le_g b (join_g a b) := Opt3.join_le_g_r O3.
  Let join_g_mon: forall a b c d (LE1: le_g a c) (LE2: le_g b d), le_g (join_g a b) (join_g c d) := Opt3.join_g_mon O3.

  Lemma block_g_inst:
    forall gd (i: Inst.t) blk, block_g gd (cons i blk) = block_g (inst_g gd i) blk.
  Proof. ss. Qed.

  Lemma block_g_ite:
    forall gd ex b1 b2 blk, block_g gd (cons (ite ex b1 b2) blk) = block_g (expr_g (join_g (block_g gd b1) (block_g gd b2)) ex) blk.
  Proof. ss. Qed.

  Lemma block_g_while:
    forall gd ex b blk, block_g gd (cons (while ex b) blk) = block_g (expr_g (block_g gd b) ex) blk.
  Proof. ss. Qed.

  Lemma block_g_inc:
    forall blk gd, le_g gd (block_g gd blk).
  Proof.
    induction blk using block_ind2; i; ss; eauto.
    - refl.
    - etrans. 2: eapply IHblk. eapply inst_g_inc.
    - etrans. 2: eapply IHblk3. etrans. 2: eapply expr_g_inc. etrans. 2: eapply join_le_g_l. eauto.
    - etrans. 2: eapply IHblk2. etrans. 2: eapply expr_g_inc. eauto.
  Qed.

  Lemma block_g_mon:
    forall blk gd1 gd2 (LE: le_g gd1 gd2),
      le_g (block_g gd1 blk) (block_g gd2 blk).
  Proof.
    induction blk using block_ind2; i; ss; eauto.
    eapply IHblk3. eapply expr_g_mon. eapply join_g_mon; eauto.
  Qed.

  Lemma block_g_big:
    forall blk gd (BIG: le_g (block_g bot_g blk) gd),
      (block_g gd blk) = gd.
  Proof.
    induction blk using block_ind2; i; ss; eauto.
    - rewrite inst_g_big.
      2:{ etrans. 2: eapply BIG. eapply block_g_inc. }
      eapply IHblk. etrans. 2: eapply BIG. eapply block_g_mon. eapply bot_g_spec.
    - rewrite IHblk1.
      2:{ etrans. 2: eapply BIG. etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc. apply join_le_g_l. }
      rewrite IHblk2.
      2:{ etrans. 2: eapply BIG. etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc. apply join_le_g_r. }
      rewrite join_g_refl. rewrite expr_g_big.
      2:{ etrans. 2: eapply BIG. etrans. 2: eapply block_g_inc. eapply expr_g_mon. eapply bot_g_spec. }
      eapply IHblk3. etrans. 2: eapply BIG. eapply block_g_mon. eapply bot_g_spec.
    - rewrite IHblk1.
      2:{ etrans. 2: eapply BIG. etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc. refl. }
      rewrite expr_g_big.
      2:{ etrans. 2: eapply BIG. etrans. 2: eapply block_g_inc. eapply expr_g_mon. eapply bot_g_spec. }
      eapply IHblk2. etrans. 2: eapply BIG. eapply block_g_mon. eapply bot_g_spec.
  Qed.

  Lemma block_g_add_block:
    forall b1 b2 gd, block_g gd (add_block b1 b2) = block_g (block_g gd b1) b2.
  Proof.
    induction b1 using block_ind2; i; ss; eauto.
  Qed.


  Let datum: Type := Opt3.datum O3.
  Let data := Opt3.data O3.
  Let analyze: block -> data := Opt3.analyze O3.

  Let update_g: gdata -> datum -> gdata := Opt3.update_g O3.
  Definition update_gs: gdata -> data -> gdata :=
    fun gd ds => fold_left update_g ds gd.

  Let update_g_inc: forall g d, le_g g (update_g g d) := Opt3.update_g_inc O3.
  Let update_g_mon: forall a b d (LE: le_g a b), le_g (update_g a d) (update_g b d) := Opt3.update_g_mon O3.

  Lemma update_gs_inc: forall ds g, le_g g (update_gs g ds).
  Proof.
    induction ds; i; ss. refl.
    etrans. 2: eapply IHds. eapply update_g_inc.
  Qed.

  Lemma update_gs_mon: forall ds a b (LE: le_g a b), le_g (update_gs a ds) (update_gs b ds).
  Proof.
    induction ds; i; ss. eapply IHds. eapply update_g_mon. auto.
  Qed.


  Let intro_inst: gdata -> datum -> Inst.t := Opt3.intro_inst O3.
  Fixpoint intro_insts (g: gdata) (ds: data) : block :=
    match ds with
    | [] => nil
    | d :: tl =>
      cons (intro_inst g d) (intro_insts (update_g g d) tl)
    end.



  (* "scope" of each global data is limited to each while-body *)
  Fixpoint opt (gd: gdata) (blk: block) : block :=
    match blk with
    | nil => nil
    | cons hd tl =>
      match hd with
      | inst i =>
        let utl := opt gd tl in
        cons hd utl
      | ite c b1 b2 =>
        let ub1 := opt gd b1 in
        let ub2 := opt gd b2 in
        let utl := opt gd tl in
        cons (ite c ub1 ub2) utl
      | while c b =>
        let ds := analyze b in
        let ugd := update_gs gd ds in
        let ub := opt ugd b in
        let utl := opt gd tl in
        add_block (intro_insts gd ds) (cons (while c ub) utl)
      end
    end
  .



  Lemma opt_add_comm:
    forall b1 b2 gd,
      opt gd (add_block b1 b2) = add_block (opt gd b1) (opt gd b2).
  Proof.
    induction b1 using block_ind2; i; ss.
    - f_equal. eauto.
    - f_equal. eauto.
    - rewrite add_block_assoc. f_equal. rewrite cons_add_block_comm. f_equal. eauto.
  Qed.

  Lemma opt_eval_inst:
    forall gd blk (i: Inst.t), opt gd (cons i blk) = cons i (opt gd blk).
  Proof. ss. Qed.

  Lemma opt_eval_ite:
    forall gd e b1 b2 blk,
      opt gd (cons (ite e b1 b2) blk) =
      cons (ite e (opt gd b1) (opt gd b2)) (opt gd blk).
  Proof. ss. Qed.

  Lemma opt_eval_while:
    forall gd e b blk,
      opt gd (cons (while e b) blk) =
      add_block (intro_insts gd (analyze b))
                (cons (while e (opt (update_gs gd (analyze b)) b)) (opt gd blk)).
  Proof. ss. Qed.



  (* gdata = global data from the original code *)
  Inductive match_code3 (gd: gdata): block -> block -> Prop :=
  | match_code3_nil
    :
      match_code3 gd nil nil

  | match_code3_inst
      (i_same: Inst.t) b_src b_tgt

      (GD: le_g (inst_g gd i_same) gd)
      (MC0: match_code3 gd b_src b_tgt)
    :
      match_code3 gd (cons i_same b_src) (cons i_same b_tgt)

  | match_code3_ite
      (s_src s_tgt: stmt) b_src b_tgt
      e (sb1 sb2 tb1 tb2: block)

      (SSRC: s_src = ite e sb1 sb2)
      (STGT: s_tgt = ite e tb1 tb2)

      (MC0: match_code3 gd b_src b_tgt)
      (MCT: match_code3 gd sb1 tb1)
      (MCF: match_code3 gd sb2 tb2)
    :
      match_code3 gd (cons s_src b_src) (cons s_tgt b_tgt)

  | match_code3_while
      (s_src s_tgt: stmt) b_src b_tgt src tgt
      e (sb tb: block)

      (SSRC: s_src = while e sb)
      (STGT: s_tgt = while e tb)

      (SRC: src = cons s_src b_src)
      (TGT: tgt = cons s_tgt b_tgt)

      (MC0: match_code3 gd b_src b_tgt)
      (MCL: match_code3 (update_gs gd (analyze sb)) sb tb)
    :
      match_code3 gd src tgt

  | match_code3_opt
      src tgt
      gd1 ds

      (GD: le_g gd gd1)
      (mc0: match_code3 gd src tgt)
    :
      match_code3 gd src (add_block (intro_insts gd1 ds) tgt)
  .


  Lemma mc_add_block
        src1 src2 tgt1 tgt2 gd
        (MC1: match_code3 gd src1 tgt1)
        (MC2: match_code3 gd src2 tgt2)
    :
      match_code3 gd (add_block src1 src2) (add_block tgt1 tgt2).
  Proof.
    depgen src2. depgen tgt2. induction MC1; i; ss; clarify.
    - econs 2; eauto.
    - econs 3; eauto.
    - rewrite ! cons_add_block_comm. econs 4; eauto.
    - rewrite add_block_assoc. econs 5; eauto.
  Qed.

  Lemma mc_mon_gdata
        src tgt gd1 gd2
        (GD: le_g (block_g gd1 src) gd1)
        (LE: le_g gd1 gd2)
        (MC: match_code3 gd2 src tgt)
    :
      match_code3 gd1 src tgt.
  Proof.
    depgen gd1. induction MC; i; ss; clarify.
    - econs 1.
    - econs 2; eauto.
      { etrans. 2: eapply GD0. etrans. 2: eapply block_g_inc. refl. }
      eapply IHMC; eauto. etrans. 2: eapply GD0. eapply block_g_mon. eapply inst_g_inc.
    - econs 3; eauto.
      + eapply IHMC1; eauto. etrans. 2: eapply GD. eapply block_g_mon. etrans. 2: eapply expr_g_inc.
        etrans. 2: eapply join_le_g_l. eapply block_g_inc.
      + eapply IHMC2; eauto. etrans. 2: eapply GD. etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc.
        eapply join_le_g_l.
      + eapply IHMC3; eauto. etrans. 2: eapply GD. etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc.
        eapply join_le_g_r.
    - ss. econs 4; eauto.
      + eapply IHMC1; eauto. etrans. 2: eapply GD. eapply block_g_mon. etrans. 2: eapply expr_g_inc. eapply block_g_inc.
      + eapply IHMC2; eauto.
        * rewrite block_g_big. refl. etrans. 2: eapply update_gs_inc. etrans. 2: eapply GD.
          etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc. eapply block_g_mon. eapply bot_g_spec.
        * eapply update_gs_mon. auto.
    - econs 5; eauto. etrans; eauto.
  Qed.

  Lemma opt_mc0:
    forall src gd (GD: le_g (block_g gd src) gd), match_code3 gd src (opt gd src).
  Proof.
    induction src using block_ind2; i; ss.
    - econs 1.
    - econs 2; eauto.
      { etrans. 2: eapply GD. eapply block_g_inc. }
      eapply IHsrc. etrans. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc.
    - econs 3; eauto.
      + eapply IHsrc3. etrans. 2: eapply GD. eapply block_g_mon.
        etrans. 2: eapply expr_g_inc. etrans. 2: eapply join_le_g_l. eapply block_g_inc.
      + eapply IHsrc1. etrans. 2: eapply GD. etrans. 2: eapply block_g_inc.
        etrans. 2: eapply expr_g_inc. eapply join_le_g_l.
      + eapply IHsrc2. etrans. 2: eapply GD. etrans. 2: eapply block_g_inc.
        etrans. 2: eapply expr_g_inc. eapply join_le_g_r.
    - econs 5; eauto. refl. econs 4; eauto.
      + eapply IHsrc2. etrans. 2: eapply GD. eapply block_g_mon. etrans. 2: eapply expr_g_inc. eapply block_g_inc.
      + eapply IHsrc1. rewrite block_g_big. refl.
        etrans. 2: eapply update_gs_inc. etrans. 2: eapply GD. etrans. 2: eapply block_g_inc.
        etrans. 2: eapply expr_g_inc. eapply block_g_mon. eapply bot_g_spec.
  Qed.

  Lemma opt_mc:
    forall src gd (GD: lt_g (block_g bot_g src) gd), match_code3 gd src (opt gd src).
  Proof.
    i. eapply opt_mc0. rewrite block_g_big. refl. unfold lt_g in GD. des; auto.
  Qed.

End OPT.
