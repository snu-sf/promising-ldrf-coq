From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
From ExtLib Require Export
     Data.String
     Data.Map.FMapAList
     Functor FunctorLaws
     Structures.Maps
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.
Require Export ITreeLib.
Require Export Program.

Require Import Sequential.
Require Import SimAux.

Require Import IDCollect.
Require Import Opt3.
Require Import Opt3Sim.

Require Import ITreeLangNotations.
Require Import ITreeLangProof.
Require Import ITreeLang.
Require Import SequentialITree.





Section LISTAUX.

  Definition update_T {T: Type} {eq_dec: forall x y: T, {x = y} + {x <> y}} (a: T) (l: list T) :=
    List.cons a (List.remove eq_dec a l).

  Definition updates_T {T: Type} {eq_dec: forall x y: T, {x = y} + {x <> y}}
             (l1: list T) (l2: list T) :=
    fold_right (@update_T T eq_dec) l2 l1.

  Definition update := @update_T Loc.t Loc.eq_dec.
  Definition updates := @updates_T Loc.t Loc.eq_dec.

  Goal (update (bot_id) [bot_id; bot_id]) = [bot_id].
  Proof. ss. Qed.

  Goal (update (bot_id) [Loc.succ bot_id; bot_id]) = [bot_id; Loc.succ bot_id].
  Proof. ss. Qed.

  Goal (updates [bot_id] [Loc.succ bot_id; bot_id]) = [bot_id; Loc.succ bot_id].
  Proof. ss. Qed.

  Goal (updates [bot_id; Loc.succ (Loc.succ bot_id)] [Loc.succ bot_id; bot_id]) =
                [bot_id; Loc.succ (Loc.succ bot_id); Loc.succ bot_id].
  Proof. ss. Qed.


  (* from l2, remove l1's elements *)
  Definition removes_T {T: Type} {eq_dec: forall x y: T, {x = y} + {x <> y}}
             (l1: list T) (l2: list T) :=
    fold_right (List.remove eq_dec) l2 l1.

  Definition removes := @removes_T Loc.t Loc.eq_dec.

  Goal (removes [bot_id; Loc.succ (Loc.succ bot_id)] [Loc.succ bot_id; bot_id]) =
                [Loc.succ bot_id].
  Proof. ss. Qed.

  Goal (removes [bot_id] [bot_id; Loc.succ bot_id; bot_id]) = [Loc.succ bot_id].
  Proof. ss. Qed.

  Goal (removes [bot_id; Loc.succ (Loc.succ bot_id)]
                [Loc.succ (Loc.succ bot_id); Loc.succ bot_id; bot_id]) =
                [Loc.succ bot_id].
  Proof. ss. Qed.

  Goal (removes [bot_id; Loc.succ (Loc.succ bot_id); Loc.succ bot_id]
                [Loc.succ (Loc.succ bot_id); Loc.succ bot_id; bot_id]) =
                [].
  Proof. ss. Qed.

End LISTAUX.



Section ANALYZE.

  (*
   static analysis to get all movable load-locations, out of loop
   semantics of a body of a loop = itself appended indefinitely

   collect loaded locations
   remove stored/updated locations
   reset for acq load/acq fence/syscall
   *)

  Let datum := Loc.t.
  Let data := list datum.

  Fixpoint analyze_get (blk: block) : data :=
    match blk with
    | nil => []
    | cons hd tl =>
      match hd with
      | inst i =>
        match i with
        | Inst.skip
        | Inst.assign _ _
        | Inst.abort
        | Inst.choose _ =>
          analyze_get tl

        | Inst.syscall _ _ =>
          []

        | Inst.load _ l ordr =>
          if (Ordering.le ordr Ordering.na)
          then update l (analyze_get tl)
          else
            if (Ordering.le ordr Ordering.strong_relaxed)
            then (analyze_get tl)
            else []

        | Inst.store l _ ordw =>
          analyze_get tl

        | Inst.fence ordr ordw =>
          if (Ordering.le Ordering.seqcst ordw || Ordering.le Ordering.acqrel ordr)%bool
          then []
          else analyze_get tl

        | Inst.update _ l _ ordr _ =>
          if (Ordering.le ordr Ordering.strong_relaxed)
          then (analyze_get tl)
          else []

        end

      | ite e b1 b2 =>
        let d1 := analyze_get b1 in
        let d2 := analyze_get b2 in
        let d3 := updates d1 d2 in
        updates d3 (analyze_get tl)

      | while e b =>
        let d1 := analyze_get b in
        updates d1 (analyze_get tl)

      end
    end.

  Fixpoint analyze_ban (blk: block) : data :=
    match blk with
    | nil => []
    | cons hd tl =>
      match hd with
      | inst i =>
        match i with
        | Inst.skip
        | Inst.assign _ _
        | Inst.abort
        | Inst.choose _ =>
          analyze_ban tl

        | Inst.syscall _ _ =>
          []

        | Inst.load _ l ordr =>
          if (Ordering.le ordr Ordering.na)
          then analyze_ban tl
          else
            if (Ordering.le ordr Ordering.strong_relaxed)
            then update l (analyze_ban tl)
            else []

        | Inst.store l _ ordw =>
          update l (analyze_ban tl)

        | Inst.fence ordr ordw =>
          if (Ordering.le Ordering.seqcst ordw || Ordering.le Ordering.acqrel ordr)%bool
          then []
          else analyze_ban tl

        | Inst.update _ l _ ordr _ =>
          if (Ordering.le ordr Ordering.strong_relaxed)
          then (analyze_ban tl)
          else []

        end

      | ite e b1 b2 =>
        let d1 := analyze_ban b1 in
        let d2 := analyze_ban b2 in
        let d3 := updates d1 d2 in
        updates d3 (analyze_ban tl)

      | while e b =>
        let d1 := analyze_ban b in
        updates d1 (analyze_ban tl)

      end
    end.


  Definition analyze (blk: block) : data :=
    let get := analyze_get blk in
    let ban := analyze_ban blk in
    removes ban get.

End ANALYZE.





Section UPDATEG.

  Definition update_id: Ident.t -> Loc.t -> Ident.t :=
    fun id _ => nextID id.

  Let le_g := Ident.le.
  Let update_g := update_id.

  Lemma update_id_inc:
    forall g d, le_g g (update_g g d).
  Proof.
    i. eapply Ident.lt_le_incl. eapply Ident.lt_succ_diag_r.
  Qed.

  Lemma update_id_mon:
    forall a b d (LE: le_g a b), le_g (update_g a d) (update_g b d).
  Proof.
    i. unfold update_g, update_id, nextID. unfold le_g. rewrite <- Ident.succ_le_mono. auto.
  Qed.

End UPDATEG.





Section LOADI.

  Definition LoadIntro (id: Ident.t) (l: Loc.t) : Inst.t := Inst.load id l Ordering.na.

End LOADI.



Section GDATA.

  Let bot_g := bot_id.
  Let expr_g := id_max_expr.
  Let inst_g := id_max_inst.
  Let join_g := Ident.max.
  Let le_g := Ident.le.

  Definition LoadIntroOpt3 :=
    Opt3.mk_opt3
      bot_g expr_g inst_g join_g Ident.le_partorder
      bot_id_spec
      expr_id_inc expr_id_mon expr_id_big
      inst_id_inc inst_id_mon inst_id_big inst_id_skip
      join_id_refl join_le_id_l join_le_id_r join_id_mon
      analyze
      update_id update_id_inc update_id_mon
      LoadIntro.

  Lemma block_id:
    Opt3.block_g LoadIntroOpt3 = id_max_block.
  Proof. ss. Qed.

  Let lt_g := Opt3.lt_g LoadIntroOpt3.

  Lemma lt_lt:
    forall a b (LT: Ident.lt a b), lt_g a b.
  Proof.
    i. unfold lt_g, Opt3.lt_g. split.
    - apply Ident.lt_le_incl in LT. auto.
    - ii. hexploit Ident.lt_le_incl; eauto. i. apply Ident.lt_nle in LT. clarify.
  Qed.

  Lemma lt_le_succ:
    forall a b (LT: lt_g a b), le_g (Ident.succ a) b.
  Proof.
    i. unfold lt_g, Opt3.lt_g in LT. des. eapply Ident.le_succ_l.
    eapply Ident.lt_nle. ii.
    assert (AS: a = b).
    { eapply antisymmetry; eauto. }
    clarify.
  Qed.

  Lemma lt_succ:
    forall a, lt_g a (Ident.succ a).
  Proof.
    i. apply lt_lt. eapply Ident.lt_succ_diag_r.
  Qed.

  Lemma ret_reg_min:
    forall code gd (LT: lt_g (id_max_block bot_g code) gd), gd <> ret_reg.
  Proof.
    i. unfold lt_g, Opt3.lt_g in LT. des. ss. ii. subst gd.
    apply LT0. eapply antisymmetry; eauto. apply Ident.le_1_l.
  Qed.

End GDATA.





Section OPT.

  Let le_g := Ident.le.
  Let join_g := Ident.max.
  Let expr_g := id_max_expr.
  Let exprs_g := id_max_exprs.
  Let inst_g := id_max_inst.

  Let update_g := update_id.
  Let update_gs := @Opt3.update_gs LoadIntroOpt3.
  Let intro_inst := LoadIntro.
  Let intro_insts := @Opt3.intro_insts LoadIntroOpt3.

  Fixpoint opt0 (id: Ident.t) (blk: block) : block :=
    match blk with
    | nil => nil
    | cons hd tl =>
      match hd with
      | inst i =>
        let utl := opt0 id tl in
        cons hd utl
      | ite c b1 b2 =>
        let ub1 := opt0 id b1 in
        let ub2 := opt0 id b2 in
        let utl := opt0 id tl in
        cons (ite c ub1 ub2) utl
      | while c b =>
        let ds := analyze b in
        let ugd := update_gs id ds in
        let ub := opt0 ugd b in
        let utl := opt0 id tl in
        add_block (intro_insts id ds) (cons (while c ub) utl)
      end
    end
  .

  Lemma opt0_Opt3: opt0 = @Opt3.opt LoadIntroOpt3.
  Proof. ss. Qed.

  Definition LICM_LoadIntro (src: block) := opt0 (newID src) src.

  Let match_code := @match_code3 LoadIntroOpt3.

  Lemma LICM_LoadIntro_mc:
    forall src, match_code (newID src) src (LICM_LoadIntro src).
  Proof.
    i. unfold LICM_LoadIntro. rewrite opt0_Opt3. eapply Opt3.opt_mc.
    rewrite block_id. eapply lt_succ.
  Qed.

  Let match_state := match_state LoadIntroOpt3.

  Theorem LICM_LoadIntro_ms
          src tgt src_c tgt_c mem
          (ALG: tgt_c = LICM_LoadIntro src_c)
          (SRC: src = SeqState.mk (lang _) (eval_lang src_c) mem)
          (TGT: tgt = SeqState.mk (lang _) (eval_lang tgt_c) mem)
    :
      match_state src tgt.
  Proof.
    econs; eauto. clarify. eapply LICM_LoadIntro_mc. ii. auto.
    rewrite block_id. eapply lt_succ.
  Qed.

End OPT.



Section SIM.

  Let le_g := Ident.le.
  Let bot_g := bot_id.
  Let join_g := Ident.max.
  Let expr_g := id_max_expr.
  Let inst_g := id_max_inst.

  Let lt_g := Opt3.lt_g LoadIntroOpt3.

  Let update_g := update_id.
  Let update_gs := @Opt3.update_gs LoadIntroOpt3.
  Let intro_inst := LoadIntro.
  Let intro_insts := @Opt3.intro_insts LoadIntroOpt3.

  Definition sim_val: Const.t -> Const.t -> Prop := eq.
  Lemma sim_val_refl: forall a, sim_val a a.
  Proof. refl. Qed.
  Let term := term sim_val.

  Lemma intro_inst_sim:
    forall r g p src_l tgt_l tb src_code tgt_code mem gd d ds
      (TB: tb = get_id_table bot src_code)
      (ML: match_le tb src_l tgt_l)
      (RET: src_l ret_reg = tgt_l ret_reg)
      (GD: lt_g (block_g LoadIntroOpt3 bot_g src_code) gd)
      (SIM: forall tgt_l',
          (<<ML: match_le tb src_l tgt_l'>>) ->
          (<<RET: src_l ret_reg = tgt_l' ret_reg>>) ->
          (gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term p Flags.bot
                   (build_state src_code src_l mem)
                   (build_state tgt_code tgt_l' mem)))
    ,
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p Flags.bot
             (build_state src_code src_l mem)
             (build_state (cons (intro_inst gd d) (add_block (intro_insts (update_g gd d) ds) tgt_code)) tgt_l mem).
  Proof.
    i. move ds before term. clarify. revert_until ds. induction ds; i.
    { ss. unfold build_state, itr_code. rewrite denote_block_cons. ired.
      rewrite denote_stmt_inst. unfold intro_inst. unfold LoadIntro.
      rewrite denote_inst_load. ired. rewrite bind_trigger.
      eapply sim_seq_na.
      { eapply sim_seq_partial_imm. ss. refl. }
      { do 2 eexists. split.
        - econs. econs; eauto. econs; eauto. i. refl.
        - ss.
      }
      ii. inv STEP_TGT. inv LANG. inv LOCAL. eapply inj_pair2 in H3. clarify.
      do 2 eexists. splits; ss.
      { refl. }
      { econs 2. }
      ired. eapply SIM; eauto.
      - eapply match_le_update_tgt; auto. eapply newID_not_orig.
        unfold newID. rewrite <- block_id. eapply lt_le_succ; auto.
      - red. hexploit ret_reg_min; eauto. i. unfold ITreeLang.update.
        apply Ident.eqb_neq in H. rewrite H. auto.
    }
    ss. unfold build_state, itr_code. rewrite denote_block_cons. ired.
    rewrite denote_stmt_inst. unfold intro_inst. unfold LoadIntro.
    rewrite denote_inst_load. ired. rewrite bind_trigger.
    eapply sim_seq_na.
    { eapply sim_seq_partial_imm. ss. refl. }
    { do 2 eexists. split.
      - econs. econs; eauto. econs 2; eauto. i. refl.
      - ss.
    }
    ii. inv STEP_TGT. inv LANG. eapply inj_pair2 in H3. clarify. inv LOCAL.
    do 2 eexists. splits; ss.
    { refl. }
    { econs 2. }
    red. ired.
    match goal with
    | [|- gpaco7 _ _ _ _ _ _ _ _ _ ?a _ ] => replace a with (build_state src_code src_l m1) end.
    2: ss.
    match goal with
    | [|- gpaco7 _ _ _ _ _ _ _ _ _ _ ?b ] => replace b with
          (build_state (cons (Inst.load (update_g gd d) a Ordering.na)
                             (add_block (intro_insts (update_g (update_g gd d) a) ds) tgt_code))
                       (ITreeLang.update gd val tgt_l)
                       m1) end.
    2: ss.
    eapply IHds; eauto.
    - eapply match_le_update_tgt; auto. eapply newID_not_orig.
      unfold newID. rewrite <- block_id. eapply lt_le_succ; auto.
    - hexploit ret_reg_min; eauto. i. unfold ITreeLang.update.
      apply Ident.eqb_neq in H. rewrite H. auto.
    - eapply le_g_lt_g2; eauto. eapply update_id_inc.
  Qed.

  Theorem LICM_LoadIntro_sim
          src tgt
          src_c tgt_c
          (ALG: tgt_c = LICM_LoadIntro src_c)
          (SRC: src = eval_lang src_c)
          (TGT: tgt = eval_lang tgt_c)
    :
      sim_seq_itree sim_val src tgt.
  Proof.
    unfold sim_seq_itree. ii. eapply (@match_state_sim LoadIntroOpt3).
    eapply sim_val_refl.
    eapply intro_inst_sim. eapply LICM_LoadIntro_ms; eauto.
    all: clarify; ss.
  Qed.

End SIM.





Require Import RRforwarding.

Section Test.

  Import ITreeLangNotations.
  Import BinNums.

  Local Open Scope expr_scope.
  Local Open Scope inst_scope.
  Local Open Scope stmt_scope.
  Local Open Scope block_scope.

  Let licm := fun code => RRfwd_opt_alg (LICM_LoadIntro code).

  Definition loc1 : Loc.t := xH.
  Definition loc2 : Loc.t := xO xH.
  Definition loc3 : Loc.t := xI xH.

  Definition a : Ident.t := xH.
  Definition b : Ident.t := Ident.succ a.
  Definition c : Ident.t := Ident.succ b.
  Definition d : Ident.t := Ident.succ c.

  Definition test0 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      { a =# (1: Const.t);
        b =#* loc1 Ordering.na
      }
      end#
    }
  .
  Definition test0' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      c =#* loc1 Ordering.na;
      while# (1: Const.t) do#
      { a =# (1: Const.t);
        b =# c
      }
      end#
    }
  .
  Goal (licm test0) = test0'.
  Proof. ss. Qed.

End Test.
