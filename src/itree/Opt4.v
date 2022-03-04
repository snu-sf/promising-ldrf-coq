Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

From PromisingLib Require Import Event.

Require Import Knowledge.
Require Import FoldN.

Require Import ITreeLang.





Module Opt4.

  Record t :=
    mk_opt4
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
        do_opt_mon: forall i d1 d2 (LE: forall p, le (d1 p) (d2 p)) (DO: do_opt d1 i), do_opt d2 i;

      }
  .

End Opt4.





Section OPT.

  Variable O4: Opt4.t.

  Let ML := Opt4.M O4.
  Let D := Opt4.D O4.
  Let meet := Opt4.meet O4.

  Lemma meet_comm :
    forall d1 d2 : D, (meet d1 d2) = (meet d2 d1).
  Proof. i. eapply (MLattice.meet_comm (T:=ML)). Qed.

  Lemma meet_assoc :
    forall d1 d2 d3 : D, (meet d1 (meet d2 d3)) = (meet (meet d1 d2) d3).
  Proof. i. eapply (MLattice.meet_assoc (T:=ML)). Qed.

  Lemma meet_idem :
    forall d : D, (meet d d) = d.
  Proof. i. eapply (MLattice.meet_idem (T:=ML)). Qed.

  Let le := Opt4.le O4.
  Lemma le_spec : forall d1 d2 : D, le d1 d2 <-> d1 = (meet d1 d2).
  Proof. i. eapply (MLattice.le_spec (T:=ML)). Qed.

  Lemma le_PreOrder : PreOrder le.
  Proof. eapply (@MLattice.le_PreOrder ML). Qed.

  Global Program Instance le_PreOrder_i: PreOrder le.

  Let bot := Opt4.bot O4.
  Let bot_spec := Opt4.bot_spec O4.

  Let P := Opt4.P O4.
  Let N := Opt4.N O4.

  Let inst_d := Opt4.inst_d O4.
  Let inst_d_mon := Opt4.inst_d_mon O4.
  Let skip_d := Opt4.skip_d O4.

  Lemma skip_d': forall (p: P) (d: D), (inst_d Inst.skip p d) = d.
  Proof.
    i. hexploit skip_d; eauto. i. eapply (MLattice.eq_leibniz ML) in H. eauto.
  Qed.

  Fixpoint block_d (b: block): P -> D -> D :=
    fun p d =>
      match b with
      | nil => d
      | cons hd tl =>
        match hd with
        | inst i =>
          let d0 := inst_d i p d in
          block_d tl p d0

        | ite _ b1 b2 =>
          let d1 := block_d b1 p d in
          let d2 := block_d b2 p d in
          let d3 := meet d1 d2 in
          block_d tl p d3

        | while _ wb =>
          let f := (block_d wb p) in
          let fp := fold_n f (S N) in
          let d0 := meet d (fp d) in
          block_d tl p d0
        end
      end.

  Hypothesis block_d_dec: forall blk p d f (FUN: f = block_d blk p), le (f (f d)) (f d).
  Hypothesis block_d_fix: forall blk f (FUN: f = block_d blk) p, @n_fix D (MLattice.eq ML) (MLattice.eq_Equiv ML) (f p) (S N).

  Lemma block_d_fix': forall blk f (FUN: f = block_d blk) p, @n_fix D eq eq_equivalence (f p) (S N).
  Proof.
    ii. hexploit block_d_fix; eauto. i. unfold n_fix in H. unfold is_fix in H. unfold is_fix_point in *.
    eapply (MLattice.eq_leibniz ML) in H. eauto.
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

  Lemma block_gd_nil
        gd
    :
      block_gd nil gd = gd.
  Proof. ss. Qed.

  Lemma block_gd_inst
        (hd: Inst.t) tl gd
    :
      block_gd (cons hd tl) gd = block_gd tl (inst_gd hd gd).
  Proof. ss. Qed.

  Lemma block_gd_ite
        e b1 b2 tl gd
    :
      block_gd (cons (ite e b1 b2) tl) gd = block_gd tl (meet2 (block_gd b1 gd) (block_gd b2 gd)).
  Proof. ss. Qed.

  Lemma block_gd_while
        e b tl gd
    :
      block_gd (cons (while e b) tl) gd = block_gd tl (meet2 gd (fold_n (block_gd b) (S N) gd)).
  Proof.
    unfold block_gd, mk_global. extensionality p. ss. f_equal.
    unfold meet2. f_equal. f_equal. symmetry. eapply fold_n_curry2.
  Qed.

  Lemma block_gd_add
        b1 b2 gd
    :
      block_gd (add_block b1 b2) gd = block_gd b2 (block_gd b1 gd).
  Proof.
    revert_until b1. induction b1 using block_ind2; i; ss.
    - rewrite ! block_gd_inst. eauto.
    - rewrite ! block_gd_ite. eauto.
    - rewrite ! block_gd_while. eauto.
  Qed.

  Lemma block_gd_mon
        blk d1 d2
        (LE: le2 d1 d2)
    :
      le2 (block_gd blk d1) (block_gd blk d2).
  Proof.
    revert_until blk. induction blk using block_ind2; i; ss.
    - rewrite ! block_gd_inst. eapply IHblk. eapply inst_gd_mon; eauto.
    - rewrite ! block_gd_ite. eapply IHblk3. eapply (@MLattice.meet_mon ML2); ss; eauto.
    - rewrite ! block_gd_while. eapply IHblk2. eapply (@MLattice.meet_mon ML2); ss; eauto.
      eapply IHblk1. eapply fold_n_mon; eauto.
  Qed.





  Let opt_inst := Opt4.opt_inst O4.
  Let do_opt := Opt4.do_opt O4.

  Let do_opt_not := Opt4.do_opt_not O4.
  Let do_opt_mon := Opt4.do_opt_mon O4.


  Fixpoint opt_block (data: GD) (blk: block) : GD * block :=
    match blk with
    | nil => (data, blk)
    | cons hd tl =>
      match hd with
      | inst i =>
        let i1 := opt_inst data i in
        let data1 := inst_gd i data in
        let '(data2, tl1) := opt_block data1 tl in
        (data2, cons i1 tl1)

      | ite cond blk1 blk2 =>
        let '(data1, ublk1) := opt_block data blk1 in
        let '(data2, ublk2) := opt_block data blk2 in
        let data3 := meet2 data1 data2 in
        let '(data4, tl1) := opt_block data3 tl in
        (data4, cons (ite cond ublk1 ublk2) tl1)

      | while cond wb =>
        let f := (block_gd wb) in
        let fp := fold_n f (S N) in
        let data1 := meet2 data (fp data) in
        let '(_, wb1) := opt_block data1 wb in
        let '(data2, tl1) := opt_block data1 tl in
        (data2, cons (while cond wb1) tl1)

      end
    end.

  Definition opt_alg : block -> block := fun code => snd (opt_block bot2 code).


  Lemma opt_block_fst
        s d
    :
      fst (opt_block d s) = block_gd s d.
  Proof.
    depgen d. induction s using block_ind2; i; ss.
    - des_ifs. ss. rewrite block_gd_inst.
      rewrite <- IHs. rewrite Heq. ss.
    - des_ifs. ss. rewrite block_gd_ite.
      rewrite <- IHs3. rewrite <- IHs1, <- IHs2. rewrite Heq, Heq0. ss. rewrite Heq1. ss.
    - des_ifs. ss. rewrite block_gd_while.
      rewrite <- IHs2. ss. rewrite Heq0. ss.
  Qed.

  Lemma opt_block_mon
        (d1 d2: GD) (src: block)
        (LE: le2 d1 d2)
    :
      le2 (fst (opt_block d1 src)) (fst (opt_block d2 src)).
  Proof.
    rewrite ! opt_block_fst. eapply block_gd_mon; eauto.
  Qed.

  Lemma opt_block_add_block
        s1 s2 t1 t2 d1 d2 d3
        (OPT1: opt_block d1 s1 = (d2, t1))
        (OPT2: opt_block d2 s2 = (d3, t2))
    :
      opt_block d1 (add_block s1 s2) = (d3, add_block t1 t2).
  Proof.
    revert_until s1. induction s1 using block_ind2; i.
    - ss. clarify.
    - rewrite cons_add_block_comm. specialize IHs1 with (s2:=s2).
      ss; clarify. des_ifs; ss; clarify.
      hexploit IHs1; eauto. i. rewrite Heq in H. clarify.
    - rewrite cons_add_block_comm. specialize IHs1_3 with (s2:=s2).
      ss; clarify. des_ifs; ss; clarify.
      hexploit IHs1_3; eauto. i. rewrite Heq1 in H. clarify.
    - rewrite cons_add_block_comm. specialize IHs1_2 with (s2:=s2).
      ss; clarify. des_ifs; ss; clarify.
      hexploit IHs1_2; eauto. i. rewrite Heq0 in H. clarify.
  Qed.

  Lemma opt_block_add_block_partial
        s1 s2 t1 d1 d2
        (OPT1: opt_block d1 s1 = (d2, t1))
    :
      opt_block d1 (add_block s1 s2) =
      (fst (opt_block d2 s2), add_block t1 (snd (opt_block d2 s2))).
  Proof.
    eapply opt_block_add_block; eauto. apply surjective_pairing.
  Qed.





  Inductive match_code4 : GD -> block -> block -> Prop :=
  | match_code4_nil
      gd
    :
      match_code4 gd nil nil

  | match_code4_inst
      (i_same: Inst.t) b_src b_tgt
      gd gd1

      (GD1: gd1 = inst_gd i_same gd)
      (MC: match_code4 gd1 b_src b_tgt)
    :
      match_code4 gd (cons i_same b_src) (cons i_same b_tgt)

  | match_code4_inst_opt
      (i_src i_tgt: Inst.t) b_src b_tgt
      gd gd' gd1

      (LE: le2 gd' gd)
      (OPT: do_opt gd' i_src)
      (ITGT: i_tgt = opt_inst gd' i_src)

      (GD1: gd1 = inst_gd i_src gd)
      (MC: match_code4 gd1 b_src b_tgt)
    :
      match_code4 gd (cons i_src b_src) (cons i_tgt b_tgt)

  | match_code4_ite
      b_src b_tgt
      e (sb1 sb2 tb1 tb2: block)
      gd

      (MC1: match_code4 gd sb1 tb1)
      (MC2: match_code4 gd sb2 tb2)
      (MC3: match_code4 (meet2 (block_gd sb1 gd) (block_gd sb2 gd)) b_src b_tgt)
    :
      match_code4 gd (cons (ite e sb1 sb2) b_src) (cons (ite e tb1 tb2) b_tgt)

  | match_code4_while
      b_src b_tgt
      e (sb tb: block)
      gd gd1

      (GD1: gd1 = meet2 gd (fold_n (block_gd sb) (S N) gd))

      (MC0: match_code4 gd1 sb tb)
      (MC1: match_code4 gd1 b_src b_tgt)
    :
      match_code4 gd (cons (while e sb) b_src) (cons (while e tb) b_tgt)
  .

  Lemma match_code4_mon
        d0 d1 src tgt
        (LE: le2 d0 d1)
        (MC: match_code4 d0 src tgt)
    :
      match_code4 d1 src tgt.
  Proof.
    depgen d1. induction MC; i.
    - econs 1.
    - econs 2; eauto. eapply IHMC. clarify. eapply inst_gd_mon; eauto.
    - econs 3. 2,3: eauto. all: eauto.
      { etrans. 2: eauto. auto. }
      eapply IHMC. clarify. eapply inst_gd_mon; eauto.
    - econs 4; eauto. eapply IHMC3. eapply (@MLattice.meet_mon ML2); ss.
      + eapply block_gd_mon; auto.
      + eapply block_gd_mon; auto.
    - econs 5. 1: eauto.
      + eapply IHMC1. clarify. eapply (@MLattice.meet_mon ML2); ss.
        eapply block_gd_mon. eapply fold_n_mon; eauto. eapply block_gd_mon.
      + eapply IHMC2. clarify. eapply (@MLattice.meet_mon ML2); ss.
        eapply block_gd_mon. eapply fold_n_mon; eauto. eapply block_gd_mon.
  Qed.

  Lemma match_code4_add_block
        s1 s2 t1 t2 d1 d2 ud
        (UD: block_gd s1 d1 = ud)
        (LE: le2 d2 ud)
        (MC1: match_code4 d1 s1 t1)
        (MC2: match_code4 d2 s2 t2)
    :
      match_code4 d1 (add_block s1 s2) (add_block t1 t2).
  Proof.
    depgen s2. depgen t2. depgen d2. depgen ud. induction MC1; i.
    - ss. rewrite block_gd_nil in UD. clarify. eapply match_code4_mon; eauto.
    - ss. rewrite block_gd_inst in UD. clarify. econs 2. eauto. eapply IHMC1; eauto.
    - ss. rewrite block_gd_inst in UD. clarify. econs 3. 3,4: eauto. all: eauto.
    - ss. rewrite block_gd_ite in UD. clarify. econs 4; eauto.
    - ss. rewrite block_gd_while in UD. clarify. econs 5; eauto.
  Qed.



  Lemma opt_block_match_code4
        src tgt gd
        (ALG: tgt = snd (opt_block gd src))
    :
      match_code4 gd src tgt.
  Proof.
    clarify. depgen gd. induction src using block_ind2; i.
    - ss. econs 1.
    - destruct (classic (do_opt gd hd)) as [OPT | NOOPT].
      + ss. des_ifs. ss. econs 3. 2,3,4: eauto. refl.
        match goal with | [H: ?x = (_, b) |- _] => replace b with (snd x) end.
        2:{ rewrite Heq; ss. }
        eapply IHsrc.
      + ss. des_ifs. ss. rewrite do_opt_not; eauto. econs 2; eauto.
        match goal with | [H: ?x = (_, b) |- _] => replace b with (snd x) end.
        2:{ rewrite Heq; ss. }
        eapply IHsrc.
    - ss. des_ifs. ss. econs 4; eauto.
      + match goal with | [H: ?x = (_, b) |- _] => replace b with (snd x) end.
        2:{ rewrite Heq; ss. }
        eapply IHsrc1; eauto.
      + match goal with | [H: ?x = (_, b0) |- _] => replace b0 with (snd x) end.
        2:{ rewrite Heq0; ss. }
        eapply IHsrc2; eauto.
      + match goal with | [H: ?x = (_, b1) |- _] => replace b1 with (snd x) end.
        2:{ rewrite Heq1; ss. }
        rewrite <- ! opt_block_fst. rewrite Heq, Heq0. ss.
    - ss. des_ifs. ss. econs 5; eauto.
      + match goal with | [H: ?x = (_, b) |- _] => replace b with (snd x) end.
        2:{ rewrite Heq; ss. }
        eapply IHsrc1; eauto.
      + match goal with | [H: ?x = (_, b0) |- _] => replace b0 with (snd x) end.
        2:{ rewrite Heq0; ss. }
        eapply IHsrc2; eauto.
  Qed.

  Theorem opt_match_code4
          src tgt
          (OPT: tgt = opt_alg src)
    :
      match_code4 bot2 src tgt.
  Proof.
    eapply opt_block_match_code4; eauto.
  Qed.

End OPT.





Module FixOpt4.

  Record t :=
    mk_fix4
      {
        M: MLattice.t;
        D := MLattice.K M;
        meet := MLattice.meet M;
        le := MLattice.le M;

        bot: D;
        bot_spec: forall d, (MLattice.le M) bot d;

        N: nat;
        level_grounded: forall d : D, grounded (MLattice.eq M) le d N;

        GL: GLattice.t N :=
          @GLattice.mk_glattice
            N D
            (MLattice.eq M) (MLattice.eq_Equiv M) (MLattice.eq_leibniz M)
            le (@MLattice.le_PreOrder M) (@MLattice.le_PartialOrder M)
            bot bot_spec level_grounded;

        P: Type;
        inst_d: Inst.t -> P -> D -> D;
        kspec: forall (i: Inst.t) (p: P),
            @GLattice.knowledge_spec N GL (inst_d i p);
        skip_d: forall (p: P) (d: D), (MLattice.eq M) (inst_d Inst.skip p d) d;

      }
  .

End FixOpt4.



Section FIX.

  Variable F : FixOpt4.t.

  Let ML : MLattice.t := FixOpt4.M F.
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


  Let level: nat := FixOpt4.N F.

  Let le_PreOrder : PreOrder le := @MLattice.le_PreOrder ML.
  Let le_PartialOrder : PartialOrder eq le := @MLattice.le_PartialOrder ML.

  Let bot : K := FixOpt4.bot F.
  Let bot_spec : forall k : K, le bot k := FixOpt4.bot_spec F.

  Let level_grounded : forall k : K, grounded eq le k level := FixOpt4.level_grounded F.

  Let GL : GLattice.t level := FixOpt4.GL F.



  Global Program Instance eq_Equiv_i: Equivalence eq.

  Global Program Instance le_PartialOrder_i : PartialOrder eq le.



  Let meet_is_min_l := @MLattice.meet_is_min_l ML.
  Let meet_is_min_r := @MLattice.meet_is_min_r ML.

  Let meet_bot_bot_l := @MLattice.meet_bot_bot_l ML.
  Let meet_bot_bot_r := @MLattice.meet_bot_bot_r ML.

  Let meet_mon := @MLattice.meet_mon ML.



  Let P: Type := FixOpt4.P F.

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

  Lemma date_meet_comm:
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
    forall m1 m2, data_le(data_meet m1 m2) m2.
  Proof. ii. unfold data_meet. apply meet_is_min_r. Qed.





  Let knowledge_spec : local_update K -> Prop := @GLattice.knowledge_spec level GL.
  Let global_spec : global_update K P -> Prop := @GLattice.global_spec level GL P.

  Let update_inst: Inst.t -> P -> K -> K := FixOpt4.inst_d F.
  Let spec: forall (i: Inst.t) (p: P), knowledge_spec (update_inst i p) :=
    FixOpt4.kspec F.
  Let spec_skip: forall (p: P) (k: K), eq (update_inst Inst.skip p k) k :=
    FixOpt4.skip_d F.

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



  Fixpoint update_block (b: block): P -> K -> K :=
    fun p k =>
      match b with
      | nil => k
      | cons hd tl =>
        match hd with
        | inst i =>
          let uk := update_inst i p k in
          update_block tl p uk

        | ite _ b1 b2 =>
          let k1 := update_block b1 p k in
          let k2 := update_block b2 p k in
          let uk := meet k1 k2 in
          update_block tl p uk

        | while _ wb =>
          let f := (update_block wb p) in
          let fp := fold_n f (1 + level) in
          (* by knowledge_le and knowledge_fix, this is same as (let f=fp in: meet k fk ffk fffk ...) *)
          let uk := meet k (fp k) in
          update_block tl p uk
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
      eapply IHb. eapply MON. auto.
    - eapply IHb3; clear IHb3. dup LE.
      apply IHb1 in LE0; clear IHb1; rename LE0 into LE1.
      apply IHb2 in LE; clear IHb2; rename LE into LE2.
      eapply meet_mon; eauto.
    - eapply IHb2. eapply meet_mon; eauto.
      eapply IHb1. eapply fold_n_mon; eauto.
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
      specialize KNOW with k. des.
      + specialize IHb with (update_inst hd p k). des.
        * left. etrans; eauto.
        * right. etrans; eauto. apply update_block_mon. apply bot_spec.
      + right. apply eq_leibniz in KNOW. rewrite KNOW. refl.
    - clear STRONG KSP.
      specialize IHb1 with k. specialize IHb2 with k. des.
      + specialize IHb3 with k. des.
        * left. etrans; eauto. apply update_block_mon.
          etrans. eapply meet_is_min_l. auto.
        * right. etrans.
          { instantiate (1:= (update_block b3 p k)). apply update_block_mon.
            etrans. eapply meet_is_min_l. auto. }
          assert (A: eq (update_block b3 p k) (update_block b3 p bot)).
          { eapply antisymmetry; eauto. apply update_block_mon. apply bot_spec. }
          apply eq_leibniz in A. rewrite A. apply update_block_mon. apply bot_spec.
      + specialize IHb3 with k. des.
        * left. etrans; eauto. apply update_block_mon.
          etrans. eapply meet_is_min_r. auto.
        * right. etrans.
          { instantiate (1:= (update_block b3 p k)). apply update_block_mon.
            etrans. eapply meet_is_min_r. auto. }
          assert (A: eq (update_block b3 p k) (update_block b3 p bot)).
          { eapply antisymmetry; eauto. apply update_block_mon. apply bot_spec. }
          apply eq_leibniz in A. rewrite A. apply update_block_mon. apply bot_spec.
      + specialize IHb3 with k. des.
        * left. etrans; eauto. apply update_block_mon.
          etrans. eapply meet_is_min_l. auto.
        * right. etrans.
          { instantiate (1:= (update_block b3 p k)). apply update_block_mon.
            etrans. eapply meet_is_min_l. auto. }
          assert (A: eq (update_block b3 p k) (update_block b3 p bot)).
          { eapply antisymmetry; eauto. apply update_block_mon. apply bot_spec. }
          apply eq_leibniz in A. rewrite A. apply update_block_mon. apply bot_spec.
      + right. apply update_block_mon. apply meet_mon; auto.
    - rewrite ! fold_n_one_out.
      specialize IHb2 with k. des.
      + left. etrans.
        2: eapply IHb2.
        apply update_block_mon. apply meet_is_min_l.
      + right. etrans.
        { instantiate (1:= update_block b2 p k).
          apply update_block_mon. apply meet_is_min_l. }
        etrans.
        1: eapply IHb2.
        apply update_block_mon. apply bot_spec.
  Qed.


  Definition update1 (b: block): (Data K P) -> (Data K P) :=
    mk_global (update_block b).

  Lemma update1_is_global: forall b, global_spec (update1 b).
  Proof.
    i. unfold global_spec, GLattice.global_spec, update1. exists (update_block b). split; auto.
    red. unfold pointwise_spec. i. unfold local_spec. apply update_block_is_knowledge.
  Qed.

  Lemma update1_mon:
    forall b d1 d2, data_le d1 d2 -> data_le (update1 b d1) (update1 b d2).
  Proof.
    i. hexploit (update1_is_global b). i. eapply GLattice.global_spec_then_mon in H0; eauto.
  Qed.

  Lemma update1_nil_unit:
    forall d, update1 nil d = d.
  Proof.
    i. unfold update1, mk_global. ss.
  Qed.

  Lemma update1_add_block_partial
        s1 s2 d1 d2
        (UP1: update1 s1 d1 = d2)
    :
      update1 (add_block s1 s2) d1 = update1 s2 d2.
  Proof.
    revert_until s1. induction s1 using block_ind2; i.
    - ss. clarify.
    - rewrite cons_add_block_comm. specialize IHs1 with (s2:=s2).
      ss; clarify. hexploit IHs1; eauto.
    - rewrite cons_add_block_comm. specialize IHs1_3 with (s2:=s2).
      ss; clarify. hexploit IHs1_3; eauto.
    - rewrite cons_add_block_comm. specialize IHs1_2 with (s2:=s2).
      ss; clarify.
      hexploit IHs1_2; eauto.
      Unshelve. all: ss.
  Qed.

  Lemma update1_cons_partial
        hd b d
    :
      update1 (cons hd b) d = update1 b (update1 (cons hd nil) d).
  Proof.
    hexploit update1_add_block_partial.
    { instantiate (3:= cons hd nil). instantiate (2:=d). clarify. }
    i. erewrite <- H. ss.
  Qed.


  Lemma data_le_meet_apply_knowledge:
    forall src data,
      data_le (data_meet data (fold_n (update1 src) (1 + level) data))
              (data_meet (update1 src data) (fold_n (update1 src) (1 + level) data)).
  Proof.
    i. unfold update1, mk_global. ii. unfold data_meet. ss.
    setoid_rewrite fold_n_curry2. rewrite fold_n_one_out.
    eapply le_meet_apply_knowledge. eapply update_block_is_knowledge.
  Qed.

  Lemma update1_while_fix
        e sb data
    :
      data_le (update1 (cons (while e sb) nil) data)
              (update1 (add_block sb (cons (while e sb) nil)) data).
  Proof.
    erewrite update1_add_block_partial; eauto.
    unfold update1, mk_global. ii. ss.
    rewrite ! fold_n_one_out. rewrite fold_n_one_in.
    match goal with
    | [|- FixOpt4.le F (meet _ ?a) (meet _ ?b)] =>
      assert (A: eq a b) end.
    { symmetry. ss.
      hexploit GLattice.knowledge_fix.
      { eapply (update_block_is_knowledge sb p). }
      i. unfold n_fix in H. unfold is_fix in H. unfold is_fix_point in H.
      specialize H with (data p). apply H. }
    apply eq_leibniz in A. rewrite <- A; clear A.
    eapply le_meet_apply_knowledge. eapply update_block_is_knowledge.
  Qed.

  Lemma update1_ite_eval
        e b1 b2 data
    :
      (update1 (cons (ite e b1 b2) nil) data) = (data_meet (update1 b1 data) (update1 b2 data)).
  Proof.
    assert
      (GEN: @GLattice.data_eq level GL P (update1 (cons (ite e b1 b2) nil) data) (data_meet (update1 b1 data) (update1 b2 data))).
    { ii. unfold update1, mk_global. unfold data_meet. ss. refl. }
    apply GLattice.data_eq_leibniz in GEN. auto.
  Qed.

  Lemma update1_while_eval
        e sb data
    :
      (update1 (cons (while e sb) nil) data) = (data_meet data (fold_n (update1 sb) (1 + level) data)).
  Proof.
    assert
      (GEN: @GLattice.data_eq level GL P (update1 (cons (while e sb) nil) data) (data_meet data (fold_n (update1 sb) (1 + level) data))).
    { ii. unfold update1, mk_global. unfold data_meet. ss.
      match goal with
      | [|- MLattice.eq _ (meet _ ?a) (meet _ ?b)] =>
        assert (A: eq a b) end.
      { setoid_rewrite fold_n_curry2. rewrite ! fold_n_one_out. refl. }
      apply eq_leibniz in A. rewrite <- A; clear A. refl.
    }
    apply GLattice.data_eq_leibniz in GEN. auto.
  Qed.

  Lemma update1_skip_eval:
    forall d, update1 (cons Inst.skip nil) d = d.
  Proof.
    i. unfold update1, mk_global. extensionality p. hexploit spec_skip. i.
    apply eq_leibniz in H. ss. erewrite H. ss.
  Qed.



  Theorem update_block_fix: forall blk f (FUN: f = update_block blk) p,
      @n_fix K eq eq_Equiv (f p) (S level).
  Proof.
    i. eapply (knowledge_fix eq_leibniz le_PartialOrder bot_spec).
    2:{ i. eapply level_grounded. }
    clarify. apply update_block_is_knowledge.
  Qed.

End FIX.
