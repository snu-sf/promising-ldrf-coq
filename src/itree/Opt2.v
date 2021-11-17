Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Axioms.

Require Export Program.

Require Import FoldN.
Require Import Knowledge.
Require Import ITreeLang.

Set Implicit Arguments.



Module Opt2.

  Record t :=
    mk_opt2
      {
        M: MLattice.t;
        D := MLattice.K M;
        meet := MLattice.meet M;
        le := MLattice.le M;

        bot: D;
        bot_spec: forall d, (MLattice.le M) bot d;

        P: Type;
        N: nat;

        inst_d: Inst.t -> P -> D -> D;
        inst_d_mon: forall (i: Inst.t) p d1 d2 (LE: le d1 d2), le (inst_d i p d1) (inst_d i p d2);
        skip_d: forall (p: P) (d: D), (MLattice.eq M) (inst_d Inst.skip p d) d;

        opt_inst: (GD D P) -> Inst.t -> Inst.t;
        do_opt: (GD D P) -> Inst.t -> Prop;

        do_opt_not: forall i data, not (do_opt data i) -> opt_inst data i = i;
        do_opt_not_skip: forall data, not (do_opt data Inst.skip);

        strict_order: forall d1 d2, not (le d1 d2) -> le d2 d1;

        ti : D;

      }
  .

End Opt2.





Section THEORY.

  Variable O2: Opt2.t.

  Let ML := Opt2.M O2.
  Let D := Opt2.D O2.
  Let meet := Opt2.meet O2.

  Lemma meet_comm :
    forall d1 d2 : D, (meet d1 d2) = (meet d2 d1).
  Proof. i. eapply (MLattice.meet_comm (T:=ML)). Qed.

  Lemma meet_assoc :
    forall d1 d2 d3 : D, (meet d1 (meet d2 d3)) = (meet (meet d1 d2) d3).
  Proof. i. eapply (MLattice.meet_assoc (T:=ML)). Qed.

  Lemma meet_idem :
    forall d : D, (meet d d) = d.
  Proof. i. eapply (MLattice.meet_idem (T:=ML)). Qed.

  Let le := Opt2.le O2.
  Lemma le_spec : forall d1 d2 : D, le d1 d2 <-> d1 = (meet d1 d2).
  Proof. i. eapply (MLattice.le_spec (T:=ML)). Qed.

  Lemma le_PreOrder : PreOrder le.
  Proof. eapply (@MLattice.le_PreOrder ML). Qed.

  Lemma le_PartialOrder : PartialOrder (MLattice.eq ML) le.
  Proof. eapply (@MLattice.le_PartialOrder ML). Qed.

  Global Program Instance le_PreOrder_i: PreOrder le.

  Let bot := Opt2.bot O2.
  Let bot_spec := Opt2.bot_spec O2.

  Let P := Opt2.P O2.
  Let N := Opt2.N O2.

  Let inst_d := Opt2.inst_d O2.
  Let inst_d_mon := Opt2.inst_d_mon O2.
  Let skip_d := Opt2.skip_d O2.

  Lemma skip_d': forall (p: P) (d: D), (inst_d Inst.skip p d) = d.
  Proof.
    i. hexploit skip_d; eauto. i. eapply (MLattice.eq_leibniz ML) in H. eauto.
  Qed.





  Let meet_is_min_l := @MLattice.meet_is_min_l ML.
  Let meet_is_min_r := @MLattice.meet_is_min_r ML.

  Let meet_bot_bot_l := @MLattice.meet_bot_bot_l ML.
  Let meet_bot_bot_r := @MLattice.meet_bot_bot_r ML.

  Let meet_mon := @MLattice.meet_mon ML.


  Let ti := Opt2.ti O2.

  Fixpoint block_d (blk: block) : P -> (local_update D) :=
    fun l t =>
    match blk with
    | nil => t
    | cons hd tl =>
      match hd with
      | inst i =>
        let t1 := (block_d tl) l t in
        (inst_d i) l t1

      | ite cond blk1 blk2 =>
        let t1 := (block_d tl) l t in
        let tt := (block_d blk1) l t1 in
        let te := (block_d blk2) l t1 in
        meet tt te

      | while cond wb =>
        let t1 := (block_d tl) l t in
        let f := (block_d wb) l in
        let fp := fold_n f (S N) in
        let t2 := fp t1 in
        let t3 := fp ti in
        meet t1 (meet t2 t3)

      end
    end.

  Hypothesis block_d_dec: forall blk p d f (FUN: f = block_d blk p), le (f (f d)) (f d).
  Hypothesis block_d_fix: forall blk f (FUN: f = block_d blk) p, @n_fix D (MLattice.eq ML) (MLattice.eq_Equiv ML) (f p) (S N).

  Lemma block_d_fix': forall blk f (FUN: f = block_d blk) p, @n_fix D eq eq_equivalence (f p) (S N).
  Proof.
    ii. hexploit block_d_fix; eauto. i. unfold n_fix in H. unfold is_fix in H. unfold is_fix_point in *.
    eapply (MLattice.eq_leibniz ML) in H. eauto.
  Qed.

  Lemma block_d_mon:
    forall b p k1 k2 (LE: le k1 k2),
      le (block_d b p k1) (block_d b p k2).
  Proof.
    i. depgen k1. depgen k2. induction b using block_ind2; i; ss.
    - eapply inst_d_mon; eauto. eapply IHb; auto.
    - eapply (@MLattice.meet_mon ML); eauto.
      + apply IHb1; eauto.
      + apply IHb2; eauto.
    - eapply (@MLattice.meet_mon ML); eauto.
      + apply IHb2; auto.
      + eapply (@MLattice.meet_mon ML); ss; eauto.
        * rewrite ! fold_n_one_out. eapply fold_n_mon; eauto. i. eapply IHb1; eauto. eapply IHb2; eauto.
        * rewrite ! fold_n_one_out. eapply fold_n_mon; eauto. i. eapply IHb1; eauto. refl.
  Qed.



  Let strict_order: forall d1 d2, not (le d1 d2) -> le d2 d1 := Opt2.strict_order O2.

  Lemma block_d_meet_comm:
    forall b p d1 d2,
      block_d b p (meet d1 d2) = meet (block_d b p d1) (block_d b p d2).
  Proof.
    i. destruct (classic (le d1 d2)) as [LE | LE].
    - match goal with
      | [|- block_d _ _ (meet ?a ?b) = _ ] => replace (meet a b) with a end.
      2:{ apply (@MLattice.le_spec ML). auto. }
      match goal with
      | [|- _ = (meet ?a ?b) ] => assert (LE2: le a b) end.
      { apply block_d_mon. auto. }
      match goal with
      | [|- _ = (meet ?a ?b) ] => replace (meet a b) with a end.
      2:{ apply (@MLattice.le_spec ML). auto. }
      auto.
    - apply strict_order in LE.
      match goal with
      | [|- block_d _ _ (meet ?a ?b) = _ ] => replace (meet a b) with b end.
      2:{ rewrite (@MLattice.meet_comm ML). apply (@MLattice.le_spec ML). auto. }
      match goal with
      | [|- _ = (meet ?a ?b) ] => assert (LE2: le b a) end.
      { apply block_d_mon. auto. }
      match goal with
      | [|- _ = (meet ?a ?b) ] => replace (meet a b) with b end.
      2:{ rewrite (@MLattice.meet_comm ML). apply (@MLattice.le_spec ML). auto. }
      auto.
  Qed.


  Definition GD := GD D P.

  Lemma  eq_leibniz2 : forall x y : GD, eq x y -> x = y.
  Proof. auto. Qed.

  Definition meet2 : GD -> GD -> GD := fun gd1 gd2 => (fun p => meet (gd1 p) (gd2 p)).

  Lemma meet_comm2 :
    forall gd1 gd2 : GD, (meet2 gd1 gd2) = (meet2 gd2 gd1).
  Proof. ii. unfold meet2. extensionality p. apply meet_comm. Qed.

  Lemma meet_assoc2 :
    forall k1 k2 k3 : GD, (meet2 k1 (meet2 k2 k3)) = (meet2 (meet2 k1 k2) k3).
  Proof. ii. unfold meet2. extensionality p. apply meet_assoc. Qed.

  Lemma meet_idem2 :
    forall k : GD, (meet2 k k) = k.
  Proof. ii. unfold meet2. extensionality p. apply meet_idem. Qed.

  Definition le2 := fun d1 d2: GD => forall p, le (d1 p) (d2 p).
  Lemma le_spec2 : forall k1 k2 : GD, le2 k1 k2 <-> k1 = (meet2 k1 k2).
  Proof.
    ii. unfold meet2, le2 in *. split.
    - i. extensionality p. eapply le_spec. eauto.
    - i. eapply le_spec. eapply equal_f in H. eauto.
  Qed.


  Definition ML2 : MLattice.t :=
    @MLattice.mk_mlattice GD
                          eq eq_equivalence eq_leibniz2
                          meet2 meet_comm2 meet_assoc2 meet_idem2
                          le2 le_spec2.

  Lemma le2_PreOrder : PreOrder le2.
  Proof. eapply (@MLattice.le_PreOrder ML2). Qed.
  Global Program Instance le2_PreOrder_i: PreOrder le2.


  Definition bot2 : GD := fun _ => bot.
  Lemma bot_spec2 : forall gd : GD, le2 bot2 gd.
  Proof. unfold le2, bot2. ii. apply bot_spec. Qed.


  Definition inst_gd (i: Inst.t): GD -> GD := mk_global (inst_d i).

  Lemma inst_gd_mon: forall (i: Inst.t) d1 d2 (LE: le2 d1 d2), le2 (inst_gd i d1) (inst_gd i d2).
  Proof.
    i. unfold inst_gd, mk_global. unfold le2 in *. ii. eapply inst_d_mon; eauto. eapply LE.
  Qed.

  Lemma skip_gd: forall (gd: GD), (inst_gd Inst.skip gd) = gd.
  Proof.
    i. unfold inst_gd, mk_global. extensionality p. rewrite skip_d'. auto.
  Qed.


  Definition block_gd (b: block): GD -> GD := mk_global (block_d b).

  Lemma block_gd_dec: forall blk gd f (FUN: f = block_gd blk), le2 (f (f gd)) (f gd).
  Proof.
    i. subst f. unfold block_gd, le2. ii. eapply block_d_dec. eauto.
  Qed.

  Lemma block_gd_fix: forall blk f (FUN: f = block_gd blk), @n_fix GD eq eq_equivalence f (S N).
  Proof.
    i. subst f. unfold block_gd. eapply g_n_fix. i. eapply block_d_fix'. eauto.
  Qed.

  Lemma block_gd_mon:
    forall b d1 d2, le2 d1 d2 -> le2 (block_gd b d1) (block_gd b d2).
  Proof.
    i. ii. unfold block_gd, mk_global. eapply block_d_mon; auto.
  Qed.

  Lemma block_gd_meet_comm:
    forall b d1 d2,
      block_gd b (meet2 d1 d2) = meet2 (block_gd b d1) (block_gd b d2).
  Proof.
    i. unfold block_gd, mk_global, meet2. extensionality p. apply block_d_meet_comm.
  Qed.



  Lemma block_gd_nil_unit:
    forall d, block_gd nil d = d.
  Proof.
    i. unfold block_gd, mk_global. ss.
  Qed.

  Lemma block_d_cons_partial
        hd p b d
    :
      block_d (cons hd b) p d = block_d (cons hd nil) p (block_d b p d).
  Proof.
    ss.
  Qed.

  Lemma block_d_cons_le:
    forall i p b1 b2 d1 d2 (UP: le (block_d b1 p d1) (block_d b2 p d2)),
      le (block_d (cons i b1) p d1) (block_d (cons i b2) p d2).
  Proof.
    i. rewrite block_d_cons_partial.
    match goal with | [|- le ?a _] => set (temp:=a); rewrite block_d_cons_partial; subst temp end.
    apply block_d_mon. auto.
  Qed.

  Lemma block_d_cons_eq:
    forall i p b1 b2 d1 d2 (UP: (block_d b1 p d1) = (block_d b2 p d2)),
      (block_d (cons i b1) p d1) = (block_d (cons i b2) p d2).
  Proof.
    hexploit (partial_order_antisym le_PartialOrder). i. rename H into ASYM. unfold Antisymmetric in ASYM.
    apply (MLattice.eq_leibniz ML).
    eapply ASYM.
    - eapply block_d_cons_le; eauto. rewrite UP; refl.
    - eapply block_d_cons_le; eauto. rewrite UP; refl.
  Qed.


  Lemma dec_le_n
        n f
        (KSP: forall d, le (f (f d)) (f d))
    :
      forall k, le ((fold_n f (S n) k)) (f k).
  Proof.
    induction n; i; ss; clarify.
    { refl. }
    rewrite fold_n_one_out. rewrite <- fold_n_one_in.
    etrans. eapply IHn. eauto.
  Qed.

  Lemma dec_le_meet:
    forall k f n (DEC: forall d, le (f (f d)) (f d)),
      le (meet k (fold_n f (1 + n) k)) (meet (f k) (fold_n f (1 + n) k)).
  Proof.
    i. etrans.
    { eapply meet_is_min_r. }
    rewrite (@MLattice.meet_comm ML).
    match goal with
    | [|- le _ (MLattice.meet _ ?a ?b)] => assert (A: le a b) end.
    { eapply dec_le_n; eauto. }
    apply (@MLattice.le_spec ML) in A. rewrite <- A. refl.
  Qed.



  Lemma block_gd_cons_eq:
    forall i b1 b2 d1 d2 (UP: block_gd b1 d1 = block_gd b2 d2),
      block_gd (cons i b1) d1 = block_gd (cons i b2) d2.
  Proof.
    i. unfold block_gd, mk_global in *. extensionality p. apply block_d_cons_eq.
    eapply equal_f in UP. eauto.
  Qed.

  Lemma block_gd_add_block_partial
        s1 s2 d1 d2
        (UP1: block_gd s2 d2 = d1)
    :
      block_gd (add_block s1 s2) d2 = block_gd s1 d1.
  Proof.
    revert_until s1. induction s1 using block_ind2; i.
    - ss.
    - rewrite cons_add_block_comm. apply block_gd_cons_eq. eauto.
    - rewrite cons_add_block_comm. apply block_gd_cons_eq. eauto.
    - rewrite cons_add_block_comm. apply block_gd_cons_eq. eauto.
  Qed.

  Lemma block_gd_cons_partial
        hd b d
    :
      block_gd (cons hd b) d = block_gd (cons hd nil) (block_gd b d).
  Proof.
    ss.
  Qed.


  Lemma block_gd_le2_meet2:
    forall src data,
      le2 (meet2 data (fold_n (block_gd src) (1 + N) data))
          (meet2 (block_gd src data) (fold_n (block_gd src) (1 + N) data)).
  Proof.
    i. unfold block_gd, mk_global. ii. unfold meet2. ss.
    setoid_rewrite fold_n_curry2. rewrite fold_n_one_out.
    eapply dec_le_meet. i. eapply block_d_dec; eauto.
  Qed.

  Lemma block_gd_inst_gd:
    forall (i: Inst.t) b d, block_gd (cons i b) d = inst_gd i (block_gd b d).
  Proof.
    ss.
  Qed.

  Lemma block_gd_skip:
    forall b d, block_gd (cons Inst.skip b) d = block_gd b d.
  Proof.
    i. rewrite block_gd_inst_gd. rewrite skip_gd; auto.
  Qed.

  Lemma block_gd_ite_eval
        e b1 b2 data
    :
      (block_gd (cons (ite e b1 b2) nil) data) = (meet2 (block_gd b1 data) (block_gd b2 data)).
  Proof.
    ss.
  Qed.

  Let datai: (Data D P) := fun _ => ti.

  Lemma block_gd_while_eval
        e sb data
    :
      (block_gd (cons (while e sb) nil) data) =
      (meet2 data (meet2 (fold_n (block_gd sb) (1 + N) data) (fold_n (block_gd sb) (1 + N) datai))).
  Proof.
    unfold block_gd, mk_global. unfold meet2. ss. extensionality p.
    match goal with
    | [|- (meet _ ?a) = (meet _ ?b)] =>
      assert (A: a = b) end.
    { setoid_rewrite fold_n_curry2. refl. }
    rewrite <- A; clear A. refl.
  Qed.

  Lemma block_gd_fix_one:
    forall b d, block_gd b (fold_n (block_gd b) (1 + N) d) = fold_n (block_gd b) (1 + N) d.
  Proof.
    i. hexploit block_gd_fix; eauto. i.
    eapply n_fix_fix_eq in H. eauto.
  Qed.

  Lemma block_gd_le_n:
    forall n b d, le2 (fold_n (block_gd b) (S n) d) (block_gd b d).
  Proof.
    ii. unfold block_gd, mk_global. setoid_rewrite fold_n_curry2.
    eapply dec_le_n. i. eapply block_d_dec; eauto.
  Qed.


  Let opt_inst: (Data D P) -> Inst.t -> Inst.t := Opt2.opt_inst O2.
  Let do_opt : (Data D P) -> Inst.t -> Prop := Opt2.do_opt O2.

  Let do_opt_not:
    forall i data, not (do_opt data i) -> opt_inst data i = i := Opt2.do_opt_not O2.

  Let do_opt_not_skip:
    forall data, not (do_opt data Inst.skip) := Opt2.do_opt_not_skip O2.



  Fixpoint opt_block (data: Data D P) (blk: block) : (Data D P) * block :=
    match blk with
    | nil => (data, blk)
    | cons hd tl =>
      let '(ud, utl) := opt_block data tl in
      match hd with
      | inst i =>
        let ui := opt_inst ud i in
        let udi := inst_gd i ud in
        (udi, cons ui utl)

      | ite cond blk1 blk2 =>
        let '(udt, ubt) := opt_block ud blk1 in
        let '(ude, ube) := opt_block ud blk2 in
        (meet2 udt ude, cons (ite cond ubt ube) utl)

      | while cond wb =>
        let f := (block_gd wb) in
        let fp := fold_n f (1 + N) in
        let ud1 := fp ud in
        let ud2 := fp datai in
        let ud3 := meet2 ud (meet2 ud1 ud2) in
        let '(_, uwb) := opt_block ud3 wb in
        (ud3, cons (while cond uwb) utl)
      end
    end.

  Definition opt_alg : block -> block :=
    fun code => snd (opt_block bot2 code).


  Lemma opt_block_fst
        s d
    :
      fst (opt_block d s) = block_gd s d.
  Proof.
    depgen d. induction s using block_ind2; i.
    - ss.
    - ss. des_ifs. ss.
      match goal with
      | [|- _ = block_gd (cons ?a ?b) _] =>
        replace (cons a b) with (add_block (cons a nil) b) end.
      2: ss.
      erewrite block_gd_add_block_partial; eauto.
      erewrite <- IHs. rewrite Heq. ss.
    - ss. des_ifs. ss.
      match goal with
      | [|- _ = block_gd (cons ?a ?b) _] =>
        replace (cons a b) with (add_block (cons a nil) b) end.
      2: ss.
      erewrite block_gd_add_block_partial; eauto.
      erewrite <- IHs3. rewrite Heq. ss.
      rewrite block_gd_ite_eval. rewrite <- IHs1. rewrite <- IHs2.
      rewrite Heq0. rewrite Heq1. ss.
    - ss. des_ifs. ss.
      match goal with
      | [|- _ = block_gd (cons ?a ?b) _] =>
        replace (cons a b) with (add_block (cons a nil) b) end.
      2: ss.
      erewrite block_gd_add_block_partial; eauto.
      erewrite <- IHs2. rewrite Heq. ss.
      rewrite block_gd_while_eval. ss.
  Qed.


  Lemma opt_block_mon
        (d1 d2: Data D P) (src: block)
        (LE: le2 d1 d2)
    :
      le2 (fst (opt_block d1 src)) (fst (opt_block d2 src)).
  Proof.
    rewrite ! opt_block_fst. apply block_gd_mon; auto.
  Qed.

  Lemma opt_block_add_block_partial
        s1 s2 t2 d1 d2
        (OPT1: opt_block d1 s2 = (d2, t2))
    :
      opt_block d1 (add_block s1 s2) =
      (fst (opt_block d2 s1), add_block (snd (opt_block d2 s1)) t2).
  Proof.
    revert_until s1. induction s1 using block_ind2; i.
    - ss.
    - rewrite cons_add_block_comm. ss; clarify. des_ifs; ss; clarify.
      apply IHs1 in OPT1. rewrite OPT1 in Heq. rewrite Heq0 in Heq. ss. clarify.
    - rewrite cons_add_block_comm. specialize IHs1_3 with (s2:=s2) (t2:=t2).
      ss; clarify. des_ifs; ss; clarify.
      apply IHs1_3 in OPT1. rewrite OPT1 in Heq. rewrite Heq2 in Heq. ss. clarify.
      rewrite Heq0 in Heq3; rewrite Heq1 in Heq4. clarify.
    - rewrite cons_add_block_comm. specialize IHs1_2 with (s2:=s2) (t2:=t2).
      ss; clarify. des_ifs; ss; clarify.
      apply IHs1_2 in OPT1. rewrite OPT1 in Heq. rewrite Heq1 in Heq. ss. clarify.
      rewrite Heq0 in Heq2. clarify.
  Qed.

  Lemma opt_block_add_block
        s1 s2 t1 t2 d1 d2 d3
        (OPT2: opt_block d1 s2 = (d2, t2))
        (OPT1: opt_block d2 s1 = (d3, t1))
    :
      opt_block d1 (add_block s1 s2) = (d3, add_block t1 t2).
  Proof.
    erewrite opt_block_add_block_partial. 2: eauto. rewrite ! OPT1. ss.
  Qed.



  Let bot2 := bot2.

  Inductive match_code2: (Data D P) -> block -> block -> Prop :=
  | match_code2_nil
    :
      match_code2 bot2 nil nil

  | match_code2_inst
      (i_same: Inst.t) b_src b_tgt
      data0

      (MC0: match_code2 data0 b_src b_tgt)
      (NOOPT: not (do_opt data0 i_same))
    :
      match_code2 (inst_gd i_same data0) (cons i_same b_src) (cons i_same b_tgt)

  | match_code2_inst_opt
      (i_src i_tgt: Inst.t) b_src b_tgt
      data0

      (MC0: match_code2 data0 b_src b_tgt)
      (OPT: do_opt data0 i_src)
      (ITGT: i_tgt = opt_inst data0 i_src)
    :
      match_code2 (inst_gd i_src data0) (cons i_src b_src) (cons i_tgt b_tgt)

  | match_code2_ite
      (s_src s_tgt: stmt) b_src b_tgt
      e (sb1 sb2 tb1 tb2: block)
      data0 data1 data2

      (SSRC: s_src = ite e sb1 sb2)
      (STGT: s_tgt = ite e tb1 tb2)

      (MC0: match_code2 data0 b_src b_tgt)

      (OPT1: (data1, tb1) = opt_block data0 sb1)
      (OPT2: (data2, tb2) = opt_block data0 sb2)
    :
      match_code2 (meet2 data1 data2) (cons s_src b_src) (cons s_tgt b_tgt)

  | match_code2_while
      (s_src s_tgt: stmt) b_src b_tgt src tgt
      e (sb tb: block)
      data0 data1 data2 data

      (SSRC: s_src = while e sb)
      (STGT: s_tgt = while e tb)

      (SRC: src = cons s_src b_src)
      (TGT: tgt = cons s_tgt b_tgt)

      (MC0: match_code2 data0 b_src b_tgt)

      (DATA1: data1 = (fold_n (block_gd sb) (1 + N)) data0)
      (DATA2: data2 = (fold_n (block_gd sb) (1 + N)) datai)
      (DATA: data = meet2 data0 (meet2 data1 data2))

      (OPT: tb = snd (opt_block data sb))
    :
      match_code2 data src tgt
  .

  Lemma match_code2_opt
        d1 s t
        (OPT: opt_block bot2 s = (d1, t))
    :
      match_code2 d1 s t.
  Proof.
    move s after d1. revert_until s. induction s using block_ind2; i; clarify.
    - ss. clarify. econs 1; auto.
    - ss. des_ifs.
      destruct (classic (do_opt d hd)) as [OPT | NOOPT].
      + econs 3; eauto.
      + dup NOOPT. apply do_opt_not in NOOPT0. rewrite NOOPT0. econs 2; eauto.
    - ss. des_ifs. econs 4; eauto.
    - ss. des_ifs. rewrite ! fold_n_one_out in *. econs 5; eauto. rewrite Heq0. ss.
  Qed.

  Lemma match_code2_opt_inv
        d1 s t
        (MC: match_code2 d1 s t)
    :
      opt_block bot2 s = (d1, t).
  Proof.
    move s after d1. revert_until s. induction s using block_ind2; i; clarify.
    - ss. inv MC; ss.
    - ss. des_ifs.
      destruct (classic (do_opt d hd)) as [OPT | NOOPT].
      + inv MC; ss; clarify.
        * eapply IHs in MC0. clarify.
        * eapply IHs in MC0. clarify.
      + dup NOOPT. apply do_opt_not in NOOPT0. rewrite NOOPT0.
        inv MC; ss; clarify.
        * eapply IHs in MC0. clarify.
        * eapply IHs in MC0. clarify.
    - ss. des_ifs. inv MC; ss. clarify. apply IHs3 in MC0. inv MC0.
      rewrite Heq0 in OPT1. rewrite Heq1 in OPT2. clarify.
    - ss. des_ifs. inv MC; ss. clarify. apply IHs2 in MC0. clarify.
      rewrite ! fold_n_one_out in *. f_equal. rewrite Heq0. ss.
  Qed.


  Lemma match_code2_add_block
        s1 s2 t1 t2 d0 d1
        (MC2: match_code2 d0 s2 t2)
        (OPT1: opt_block d0 s1 = (d1, t1))
    :
      match_code2 d1 (add_block s1 s2) (add_block t1 t2).
  Proof.
    revert_until s1. induction s1 using block_ind2; i; clarify.
    - ss; clarify.
    - ss; clarify. des_ifs. rewrite cons_add_block_comm.
      destruct (classic (do_opt d hd)) as [OPT | NOOPT].
      + econs 3; auto.
        eapply IHs1; eauto.
      + dup NOOPT. apply do_opt_not in NOOPT. rewrite NOOPT.
        econs 2; auto.
        eapply IHs1; eauto.
    - ss; clarify. des_ifs.
      rewrite cons_add_block_comm.
      econs 4; eauto.
    - ss; clarify. des_ifs.
      rewrite cons_add_block_comm.
      rewrite ! fold_n_one_out in *.
      econs 5; eauto. rewrite Heq0. ss.
  Qed.

  Theorem opt_match_code2
          src tgt data
          (OPT: opt_alg src = tgt)
          (DATA: data = block_gd src bot2)
    :
      match_code2 data src tgt.
  Proof.
    ss. unfold opt_alg in OPT. clarify. eapply match_code2_opt; eauto.
    hexploit opt_block_fst; i. rewrite <- H. eapply injective_projections; ss; eauto.
  Qed.

  Lemma match_code2_skip
        src tgt data
    :
      match_code2 data src tgt <-> match_code2 data (cons Inst.skip src) (cons Inst.skip tgt).
  Proof.
    split; i.
    - replace data with (inst_gd Inst.skip data).
      2:{ apply skip_gd. }
      econs 2; eauto.
    - inv H; ss; clarify; eauto.
      + rewrite skip_gd. auto.
      + hexploit do_opt_not_skip. i. exfalso; apply H. eauto.
  Qed.

End THEORY.





Module FixOpt2.

  Record t :=
    mk_fix2
      {
        M: MLattice.t;
        D := MLattice.K M;
        meet := MLattice.meet M;
        le := MLattice.le M;

        bot: D;
        bot_spec: forall d, (MLattice.le M) bot d;

        N: nat;
        N_grounded: forall d : D, grounded (MLattice.eq M) le d N;

        GL: GLattice.t N :=
          @GLattice.mk_glattice
            N D
            (MLattice.eq M) (MLattice.eq_Equiv M) (MLattice.eq_leibniz M)
            le (@MLattice.le_PreOrder M) (@MLattice.le_PartialOrder M)
            bot bot_spec N_grounded;

        P: Type;
        inst_d: Inst.t -> P -> D -> D;
        kspec: forall (i: Inst.t) (p: P),
            @GLattice.knowledge_spec N GL (inst_d i p);
        skip_d: forall (p: P) (d: D), (MLattice.eq M) (inst_d Inst.skip p d) d;

        ti : D;

      }
  .

End FixOpt2.



Section FIX.

  Variable F : FixOpt2.t.

  Let ML : MLattice.t := FixOpt2.M F.
  Let K : Type := MLattice.K ML.

  Let eq : K -> K -> Prop := MLattice.eq ML.
  Let eq_Equiv : Equivalence eq := MLattice.eq_Equiv ML.
  Let eq_leibniz : forall x y : K, eq x y -> x = y := MLattice.eq_leibniz ML.

  Let meet := MLattice.meet ML.
  Let meet_comm_eq :
    forall k1 k2 : K, eq (meet k1 k2) (meet k2 k1) :=
    MLattice.meet_comm_eq ML.
  Let meet_assoc_eq :
    forall k1 k2 k3 : K, eq (meet k1 (meet k2 k3)) (meet (meet k1 k2) k3) :=
    MLattice.meet_assoc_eq ML.
  Let meet_idem_eq :
    forall k : K, eq (meet k k) k :=
    MLattice.meet_idem_eq ML.

  Let le : K -> K -> Prop := MLattice.le ML.
  Let le_spec_eq : forall k1 k2 : K, le k1 k2 <-> eq k1 (meet k1 k2) := MLattice.le_spec_eq ML.


  Let level: nat := FixOpt2.N F.

  Let le_PreOrder : PreOrder le := @MLattice.le_PreOrder ML.
  Let le_PartialOrder : PartialOrder eq le := @MLattice.le_PartialOrder ML.

  Let bot : K := FixOpt2.bot F.
  Let bot_spec : forall k : K, le bot k := FixOpt2.bot_spec F.

  Let N_grounded : forall k : K, grounded eq le k level := FixOpt2.N_grounded F.

  Let GL : GLattice.t level := FixOpt2.GL F.



  Global Program Instance eq_Equiv_i: Equivalence eq.
  Global Program Instance le_PartialOrder_i : PartialOrder eq le.



  Let meet_is_min_l := @MLattice.meet_is_min_l ML.
  Let meet_is_min_r := @MLattice.meet_is_min_r ML.

  Let meet_bot_bot_l := @MLattice.meet_bot_bot_l ML.
  Let meet_bot_bot_r := @MLattice.meet_bot_bot_r ML.

  Let meet_mon := @MLattice.meet_mon ML.



  Let P: Type := FixOpt2.P F.

  Global Program Instance data_Equiv: Equivalence (GLattice.data_eq (T:=GL) (P:=P)).
  Global Program Instance data_PreOrder: PreOrder (GLattice.data_le (T:=GL) (P:=P)).
  Global Program Instance data_PartialOrder :
    PartialOrder (GLattice.data_eq (T:=GL) (P:=P)) (GLattice.data_le (T:=GL) (P:=P)).
  Next Obligation.
  Proof.
    assert (Antisymmetric (Data K P)
                          (GLattice.data_eq (T:=GL) (P:=P))
                          (GLattice.data_le (T:=GL) (P:=P))).
    { eapply partial_order_antisym. eapply (@GLattice.data_PartialOrder level GL P). }
    unfold relation_equivalence, relation_conjunction.
    unfold predicate_equivalence, predicate_intersection.
    unfold pointwise_lifting, pointwise_extension.
    i. split; i.
    - split.
      + apply GLattice.data_eq_leibniz in H0. rewrite H0. refl.
      + unfold flip. apply GLattice.data_eq_leibniz in H0. rewrite H0. refl.
    - des. eapply antisymmetry; eauto.
  Qed.


  Lemma eq_K:
    forall (k1 k2: K), @Logic.eq (GLattice.K GL) k1 k2 <-> @Logic.eq (MLattice.K ML) k1 k2.
  Proof. i. split; i. rewrite H. auto. rewrite H. auto. Qed.

  Lemma le_K:
    forall (k1 k2: K), GLattice.le GL k1 k2 <-> MLattice.le ML k1 k2.
  Proof. i. split; i. rewrite H. refl. rewrite H. refl. Qed.

  Ltac emb_meet := replace meet with (MLattice.meet ML) in *; [|ss].


  Definition data_meet (d1 d2: Data K P) : Data K P :=
    fun p => (meet) (d1 p) (d2 p).

  Lemma data_meet_comm:
    forall m1 m2, data_meet m1 m2 = data_meet m2 m1.
  Proof.
    ii. unfold data_meet. extensionality p. emb_meet.
    setoid_rewrite MLattice.meet_comm at 1. refl.
  Qed.

  Lemma data_meet_assoc:
    forall m1 m2 m3, data_meet m1 (data_meet m2 m3) = data_meet (data_meet m1 m2) m3.
  Proof.
    ii. unfold data_meet. extensionality p. emb_meet.
    setoid_rewrite MLattice.meet_assoc. refl.
  Qed.

  Lemma data_meet_idem:
    forall m, data_meet m m = m.
  Proof.
    ii. unfold data_meet. extensionality p. emb_meet.
    setoid_rewrite MLattice.meet_idem. refl.
  Qed.


  Let data_le : (Data K P) -> (Data K P) -> Prop := @GLattice.data_le level GL P.

  Lemma data_meet_le_spec :
    forall (m1 m2: Data K P), (data_le m1 m2) <-> (m1 = data_meet m1 m2).
  Proof.
    ii. split.
    - ii. unfold data_le in H. unfold GLattice.data_le in H.
      unfold Knowledge.data_le in H. unfold data_meet.
      extensionality p. specialize H with p. emb_meet.
      eapply (@MLattice.le_spec ML); auto.
    - ii. unfold data_meet in H. rewrite le_K.
      eapply MLattice.le_spec. clarify. eapply equal_f in H. eapply H.
  Qed.

  Lemma data_meet_mon:
    forall (m1 m2 n1 n2: Data K P)
      (LE1: data_le m1 m2)
      (LE2: data_le n1 n2),
      data_le (data_meet m1 n1) (data_meet m2 n2).
  Proof.
    i. unfold data_le, GLattice.data_le, Knowledge.data_le in *.
    i. unfold data_meet. apply meet_mon; [apply LE1 | apply LE2].
  Qed.

  Lemma data_meet_is_min_l:
    forall m1 m2, data_le (data_meet m1 m2) m1.
  Proof. ii. unfold data_meet. apply meet_is_min_l. Qed.

  Lemma data_meet_is_min_r:
    forall m1 m2, data_le (data_meet m1 m2) m2.
  Proof. ii. unfold data_meet. apply meet_is_min_r. Qed.





  Let knowledge_spec : local_update K -> Prop := @GLattice.knowledge_spec level GL.
  Let global_spec : global_update K P -> Prop := @GLattice.global_spec level GL P.

  Let update_inst: Inst.t -> P -> K -> K := FixOpt2.inst_d F.
  Let spec: forall (i: Inst.t) (p: P), knowledge_spec (update_inst i p) :=
    FixOpt2.kspec F.
  Let spec_skip: forall (p: P) (k: K), eq (update_inst Inst.skip p k) k :=
    FixOpt2.skip_d F.

  Lemma le_meet_apply_knowledge:
    forall k f n (KSP: Knowledge.knowledge_spec le bot f), le (meet k (fold_n f (1 + n) k)) (meet (f k) (fold_n f (1 + n) k)).
  Proof.
    i. etrans.
    { eapply meet_is_min_r. }
    rewrite (@MLattice.meet_comm ML).
    match goal with
    | [|- le _ (MLattice.meet _ ?a ?b)] => assert (A: le a b) end.
    { hexploit (knowledge_le_n eq_leibniz le_PartialOrder bot_spec n); eauto. }
    apply (@MLattice.le_spec ML) in A. rewrite <- A. refl.
  Qed.



  Definition update0 (i: Inst.t): (Data K P) -> (Data K P) :=
    mk_global (update_inst i).

  Lemma update0_is_global: forall i, global_spec (update0 i).
  Proof.
    i. unfold global_spec, GLattice.global_spec, update0.
    exists (update_inst i). split; auto.
    red. unfold pointwise_spec. i. unfold local_spec. apply spec.
  Qed.

  Lemma update0_mon:
    forall i d1 d2, data_le d1 d2 -> data_le (update0 i d1) (update0 i d2).
  Proof.
    i. hexploit (update0_is_global i). i.
    eapply GLattice.global_spec_then_mon in H0; eauto.
  Qed.

  Lemma update0_skip_eval:
    forall d, update0 Inst.skip d = d.
  Proof.
    i. unfold update0, mk_global. extensionality p. hexploit spec_skip. i.
    apply eq_leibniz in H. erewrite H. ss.
  Qed.

  Fixpoint update_block (blk: block) : P -> (local_update K) :=
    fun l t =>
    match blk with
    | nil => t
    | cons hd tl =>
      match hd with
      | inst i =>
        let t1 := (update_block tl) l t in
        (update_inst i) l t1

      | ite cond blk1 blk2 =>
        let t1 := (update_block tl) l t in
        let tt := (update_block blk1) l t1 in
        let te := (update_block blk2) l t1 in
        meet tt te

      | while cond wb =>
        let t1 := (update_block tl) l t in
        let f := (update_block wb) l in
        let fp := fold_n f (1 + level) in
        let t2 := fp t1 in
        let t3 := fp (FixOpt2.ti F) in
        meet t1 (meet t2 t3)

      end
    end.



  Lemma update_block_mon:
    forall b p k1 k2 (LE: le k1 k2),
      le (update_block b p k1) (update_block b p k2).
  Proof.
    i. unfold GLattice.knowledge_spec in *. unfold knowledge_spec in *.
    depgen k1. depgen k2. induction b using block_ind2; i; ss.
    - specialize spec with hd p.
      destruct spec; clear spec. des. rename H into MON, H0 into KNOW.
      eapply MON; eauto. eapply IHb. auto.
    - eapply (@MLattice.meet_mon ML); eauto.
      + apply IHb1; eauto.
      + apply IHb2; eauto.
    - eapply (@MLattice.meet_mon ML); eauto.
      + apply IHb2; auto.
      + eapply (@MLattice.meet_mon ML); ss; eauto.
        * rewrite ! fold_n_one_out. eapply fold_n_mon; eauto. i. eapply IHb1; auto. eapply IHb2; auto.
        * rewrite ! fold_n_one_out. eapply fold_n_mon; eauto. i. eapply IHb1; auto. refl.
  Qed.

  Lemma update_block_is_knowledge:
    forall (b: block) (p: P), knowledge_spec (update_block b p).
  Proof.
    i. unfold GLattice.knowledge_spec in *.
    unfold knowledge_spec, Knowledge.knowledge_spec in *. esplits.
    { i. eapply update_block_mon; eauto. }
    pose (knowledge_spec_strong le_PartialOrder bot_spec) as STRONG.
    dup spec. rename spec0 into KSP.
    induction b using block_ind2; i; ss.
    - left; refl.
    - dup spec.
      specialize spec0 with hd p. apply STRONG in spec0; clear STRONG.
      dup spec.
      specialize spec1 with hd p.
      destruct spec1. des. rename H into MON. clear H0. rename spec0 into KNOW.
      specialize KNOW with (update_block b p k). des.
      + specialize IHb with k. des.
        * left. etrans; eauto.
        * right. eapply MON; eauto.
      + right. apply eq_leibniz in KNOW. rewrite KNOW. eapply MON. apply bot_spec.
    - clear STRONG KSP.
      specialize IHb1 with (update_block b3 p k). specialize IHb2 with (update_block b3 p k). des.
      + specialize IHb3 with k. des.
        * left. etrans. 2: eauto. etrans. 2: eapply IHb1. apply meet_is_min_l.
        * right. eapply (@MLattice.meet_mon ML).
          { apply update_block_mon; auto. }
          { apply update_block_mon; auto. }
      + specialize IHb3 with k. des.
        * left. etrans. 2: eauto. etrans. 2: eapply IHb2. apply meet_is_min_r.
        * right. eapply (@MLattice.meet_mon ML).
          { etrans; eauto. apply update_block_mon. apply bot_spec. }
          { apply update_block_mon; auto. }
      + specialize IHb3 with k. des.
        * left. etrans. 2: eauto. etrans. 2: eapply IHb1. apply meet_is_min_l.
        * right. eapply (@MLattice.meet_mon ML).
          { apply update_block_mon; auto. }
          { apply update_block_mon; auto. }
      + right. apply (@MLattice.meet_mon ML).
        * etrans; eauto. apply update_block_mon; eauto.
        * etrans; eauto. apply update_block_mon; eauto.
    - rewrite ! fold_n_one_out.
      specialize IHb2 with k. des.
      + left. etrans. 2: eapply IHb2. apply meet_is_min_l.
      + right. apply (@MLattice.meet_mon ML); eauto.
        apply (@MLattice.meet_mon ML); eauto.
        * eapply fold_n_mon; eauto. i. ss. apply update_block_mon; auto.
        * eapply fold_n_mon; eauto. i. ss. apply update_block_mon; auto. refl.
  Qed.

  Lemma update_block_is_knowledge_strong:
    forall b p k,
      (le (update_block b p k) k) \/ ((update_block b p k) = (update_block b p bot)).
  Proof.
    i. hexploit (update_block_is_knowledge b p). i.
    pose (knowledge_spec_strong le_PartialOrder bot_spec) as STRONG.
    apply STRONG in H; clear STRONG; rename H into STRONG.
    des. specialize STRONG with k. des; auto.
  Qed.


  Theorem update_block_fix: forall blk f (FUN: f = update_block blk) p,
      @n_fix K eq eq_Equiv (f p) (S level).
  Proof.
    i. eapply (knowledge_fix eq_leibniz le_PartialOrder bot_spec).
    2:{ i. eapply N_grounded. }
    clarify. apply update_block_is_knowledge.
  Qed.

End FIX.
