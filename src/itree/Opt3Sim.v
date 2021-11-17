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
Require Import String.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.
Require Export ITreeLib.
Require Export Program.

Require Import Simple.
Require Import SimAux.

Require Import Opt3.
Require Import IDCollect.

Require Import ITreeLangProof.
Require Import ITreeLang.



Section ML.

  Definition match_le (orig: id_table) (src tgt: lenv) :=
    forall i, (orig i) -> (src i = tgt i).

  Lemma match_le_update
        orig src tgt k v
        (ML: match_le orig src tgt)
    :
      match_le orig (update k v src) (update k v tgt).
  Proof.
    unfold match_le in *. unfold update. i. des_ifs. eauto.
  Qed.

  Lemma match_le_update_tgt
        orig src tgt k v
        (ML: match_le orig src tgt)
        (NEW: orig k = false)
    :
      match_le orig src (update k v tgt).
  Proof.
    unfold match_le in *. i. destruct (Ident.eqb k i) eqn:EQ.
    { rewrite Ident.eqb_eq in EQ. clarify. }
    unfold update. rewrite EQ. eapply ML. auto.
  Qed.


  Lemma ml_mon
        tb1 tb2 src tgt
        (LE: le tb1 tb2)
        (ML: match_le tb2 src tgt)
    :
      match_le tb1 src tgt.
  Proof. unfold match_le in *. i. eauto. Qed.

  Lemma ml_expr
        tb ex src tgt
        (ML: match_le (id_update_expr tb ex) src tgt)
    :
      denote_expr src ex = denote_expr tgt ex.
  Proof.
    move ex after tb. revert_until ex. induction ex; i; ss.
    - rewrite ! denote_expr_var. unfold match_le in ML. specialize ML with var.
      apply ML. unfold id_update. rewrite Ident.eqb_refl. auto.
    - rewrite ! denote_expr_op1. erewrite IHex; eauto.
    - rewrite ! denote_expr_op2. erewrite IHex1. erewrite IHex2. eauto.
      { eauto. }
      eapply ml_mon; eauto.
      eapply id_update_expr_inc.
  Qed.

  Lemma ml_exprs
        tb exs src tgt
        (ML: match_le (id_update_exprs tb exs) src tgt)
    :
      denote_exprs src exs = denote_exprs tgt exs.
  Proof.
    move exs after tb. revert_until exs. induction exs; i; ss.
    f_equal; eauto.
    eapply ml_expr; eauto.
    eapply ml_mon; eauto.
    apply id_update_exprs_inc; eauto.
  Qed.

End ML.



Section SIM.

  Variable O3: Opt3.t.

  Let gdata: Type := Opt3.gdata O3.
  Let bot_g: gdata := Opt3.bot_g O3.
  Let expr_g: gdata -> Inst.expr -> gdata := Opt3.expr_g O3.
  Let inst_g: gdata -> Inst.t -> gdata := Opt3.inst_g O3.
  Let join_g: gdata -> gdata -> gdata := Opt3.join_g O3.

  Let le_g: gdata -> gdata -> Prop := Opt3.le_g O3.
  Let le_g_PreOrder: PreOrder le_g := Opt3.le_g_PreOrder O3.
  Let le_g_PartialOrder: PartialOrder eq le_g := Opt3.le_g_PartialOrder O3.
  Program Instance le_g_PreOrder_i: PreOrder le_g.
  Program Instance le_g_PartialOrder_i: PartialOrder eq le_g.

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

  Let datum: Type := Opt3.datum O3.
  Let data := Opt3.data O3.
  Let analyze: block -> data := Opt3.analyze O3.
  Let update_g: gdata -> datum -> gdata := Opt3.update_g O3.
  Let update_g_inc: forall g d, le_g g (update_g g d) := Opt3.update_g_inc O3.
  Let update_g_mon: forall a b d (LE: le_g a b), le_g (update_g a d) (update_g b d) := Opt3.update_g_mon O3.

  Let intro_inst: gdata -> datum -> Inst.t := Opt3.intro_inst O3.

  Let lt_g := lt_g O3.
  Let match_code3 := match_code3 O3.



  Definition build_state (c: block) (le: lenv) (m: SeqMemory.t) :=
    SeqState.mk (lang _) (itr_code c le) m.

  Variant match_state (src tgt: (SeqState.t (lang _))) :=
  | match_state_intro
      src_l tgt_l mem src_code tgt_code gd
      (MC: match_code3 gd src_code tgt_code)
      (ML: match_le (get_id_table bot src_code) src_l tgt_l)
      (SRC: src = build_state src_code src_l mem)
      (TGT: tgt = build_state tgt_code tgt_l mem)
      (GD: lt_g (block_g O3 bot_g src_code) gd)
      (RET: src_l ret_reg = tgt_l ret_reg)
    :
      match_state src tgt
  .


  Variable sim_val: Const.t -> Const.t -> Prop.
  Hypothesis sim_val_refl: forall a, sim_val a a.
  Let term := term sim_val.

  Hypothesis intro_inst_sim:
    forall r g p src_l tgt_l tb src_code tgt_code mem gd d ds
      (TB: tb = get_id_table bot src_code)
      (ML: match_le tb src_l tgt_l)
      (RET: src_l ret_reg = tgt_l ret_reg)
      (GD: lt_g (block_g O3 bot_g src_code) gd)
      (SIM: forall tgt_l',
          (<<ML: match_le tb src_l tgt_l'>>) ->
          (<<RET: src_l ret_reg = tgt_l' ret_reg>>) ->
          (gupaco4 (_sim_seq term) (cpn4 (_sim_seq term)) g p Flags.bot
                   (build_state src_code src_l mem)
                   (build_state tgt_code tgt_l' mem)))
    ,
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p Flags.bot
             (build_state src_code src_l mem)
             (build_state (cons (intro_inst gd d) (add_block (intro_insts (update_g gd d) ds) tgt_code)) tgt_l mem).

  Theorem match_state_sim
          p src tgt
          (MS: match_state src tgt)
    :
      sim_seq term p Flags.bot src tgt.
  Proof.
    ginit. do 4 revert1. gcofix CIH. i. inv MS.
    induction MC; clarify; ss.
    { unfold build_state, itr_code. rewrite ! denote_block_nil. ired.
      eapply sim_seq_term.
      - ss. unfold ILang.is_terminal. eauto.
      - ii. ss. eexists. splits; ss. refl. ss.
        + eexists; eauto.
        + ss. rewrite RET. econs; eauto.
        + refl.
        + refl.
    }
    { unfold build_state, itr_code. rewrite ! denote_block_cons. rewrite ! denote_stmt_inst.
      destruct i_same; clarify.
      - rewrite ! denote_inst_skip. ired.
        eapply sim_seq_tau; eauto.
        eapply partial_same_mem; eauto.
        gbase. eapply CIH. econs. 3,4: ss. all: eauto.
        eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc.

      - rewrite ! denote_inst_assign. ired.
        eapply sim_seq_tau; eauto.
        eapply partial_same_mem; eauto.
        gbase. eapply CIH. econs. 3,4: ss. all: eauto.
        2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
        2:{ unfold update. des_ifs. eapply ml_expr; eauto. eapply ml_mon; eauto.
            etrans. 2: eapply get_id_table_inc. etrans. 2: eapply id_update_inc. refl. }
        erewrite ml_expr. eapply match_le_update.
        + eapply ml_mon; eauto. apply get_id_table_mon. apply bot_spec.
        + eapply ml_mon; eauto. etrans. 2: eapply get_id_table_inc.
          etrans. 2: eapply id_update_inc. refl.

      - rewrite ! denote_inst_load. ired.
        destruct (Ordering.le Ordering.plain ord) eqn:ORD.
        + eapply sim_seq_atomic; eauto.
          { eapply partial_same_mem; eauto. }
          { i. inv H. inv LOCAL; ss; clarify.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
          }
          { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_read; eauto. ss. }
          ii. ss.
          irw in STEP_TGT. inv STEP_TGT. ss; clarify.
          do 3 eexists. splits; ss.
          { refl. }
          { ss. rewrite bind_trigger. eapply ILang.step_read. eauto. }
          grind. eapply inj_pair2 in H0. clarify. ired.
          do 3 eexists. splits; ss; eauto.
          2:{ gbase. eapply CIH. econs. 3,4: ss. eauto.
              2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
              2:{ unfold update. des_ifs. }
              apply match_le_update. eapply ml_mon; eauto.
              apply get_id_table_mon. apply bot_spec.
          }
          eapply SeqEvent.input_match_bot.

        + eapply sim_seq_na; eauto.
          { eapply partial_same_mem; eauto. }
          { do 2 eexists. esplits.
            - econs; eauto. rewrite bind_trigger. eapply ILang.step_read; eauto.
              eapply SeqState.na_local_step_read; eauto. destruct ord; ss. i. refl.
            - ss.
          }
          ii.
          inv STEP_TGT. ss; clarify.
          rewrite bind_trigger in LANG. inv LANG. inv LOCAL.
          eapply inj_pair2 in H3. clarify. ss.
          des_ifs.
          { ired. do 2 eexists. splits; ss.
            { refl. }
            { econs 1; eauto. econs; ss; eauto.
              - rewrite bind_trigger. eapply ILang.step_read; eauto.
              - econs. eauto. i. rewrite Heq in H. simpl in H. inv H.
            }
            instantiate (1:=val). ired.
            gbase. eapply CIH. econs. 3,4: ss. eauto.
            2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
            2:{ unfold update. destruct (Ident.eqb lhs ret_reg); eauto. }
            apply match_le_update. eapply ml_mon; eauto.
            apply get_id_table_mon. apply bot_spec.
          }
          { ired. do 2 eexists. splits; ss.
            { refl. }
            { econs 1; eauto. econs; ss; eauto.
              - rewrite bind_trigger. eapply ILang.step_read; eauto.
              - econs; eauto.
            }
            ired. gbase. eapply CIH. econs. 3,4: ss. eauto.
            2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
            2:{ unfold update. destruct (Ident.eqb lhs ret_reg); eauto. }
            apply match_le_update. eapply ml_mon; eauto.
            apply get_id_table_mon. apply bot_spec.
          }

      - rewrite ! denote_inst_store. ired.
        destruct (Ordering.le Ordering.plain ord) eqn:ORD.
        + eapply sim_seq_atomic; eauto.
          eapply partial_same_mem; eauto.
          { i. inv H. inv LOCAL; ss; clarify.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des.
              (* easier way? *)
              symmetry in H. eapply simpobs in H.
              eapply eqit_inv_vis in H. des. unfold subevent in H.
              unfold resum, IFun in H. unfold ReSum_id in H. unfold id_ in H.
              unfold Id_IFun in H. clarify.
              destruct ord; ss.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
          }
          { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_write; eauto. ss. }
          ii. ss. irw in STEP_TGT.
          inv STEP_TGT. ss; clarify.
          do 3 eexists. splits; ss.
          { refl. }
          { ss. rewrite bind_trigger. erewrite (ml_expr _ _ (src:=src_l) (tgt:=tgt_l)).
            eapply ILang.step_write. eauto.
            eapply ml_mon; eauto. apply get_id_table_inc.
          }
          { ss. splits; auto. refl. }
          eapply inj_pair2 in H0. clarify. grind.
          do 3 eexists. splits; ss; eauto.
          2:{ gbase. eapply CIH. econs. 3,4: ss. eauto.
              2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
              2:{ auto. }
              eapply ml_mon; eauto. apply get_id_table_mon. apply bot_spec.
          }
          eapply SeqEvent.input_match_bot.

        + destruct (p lhs) eqn:PERM.
          { gstep. econs 2. ii. unfold SeqThread.failure.
            do 3 eexists. splits; ss. econs 1. econs 1.
            eexists. econs 1. econs.
            rewrite bind_trigger. econs; eauto.
            econs; eauto. destruct ord; ss. rewrite PERM. ss.
          }
          { eapply sim_seq_na; eauto.
            eapply partial_same_mem; eauto.
            { do 2 eexists. esplits.
              - econs; eauto. rewrite bind_trigger. eapply ILang.step_write; eauto.
                eapply SeqState.na_local_step_write; eauto. destruct ord; ss.
              - rewrite PERM. ss.
            }
            ii. inv STEP_TGT.
            rewrite bind_trigger in LANG. inv LANG. inv LOCAL.
            eapply inj_pair2 in H4. clarify. ss. rewrite PERM. ired.
            do 2 eexists. splits; ss.
            { refl. }
            { econs 1; eauto. econs; ss; eauto.
              - rewrite bind_trigger. eapply ILang.step_write; eauto.
              - econs; eauto. rewrite PERM. ss.
            }
            erewrite ml_expr.
            2:{ eapply ml_mon; eauto. apply get_id_table_inc. }
            gbase. eapply CIH. econs. 3,4: ss. eauto.
            2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
            2:{ auto. }
            eapply ml_mon; eauto. apply get_id_table_mon. apply bot_spec.
          }

      - rewrite ! denote_inst_update. grind.
        destruct (orb (Ordering.le ordr Ordering.na) (Ordering.le ordw Ordering.na)) eqn:ORD.
        + (*na case*)
          gstep. econs 1.
          { ii. ss. unfold ILang.is_terminal in TERMINAL_TGT. des.
            irw in TERMINAL_TGT. symmetry in TERMINAL_TGT.
            eapply eq_is_bisim in TERMINAL_TGT. eapply eqitree_inv_ret_vis in TERMINAL_TGT.
            clarify.
          }
          2:{ ii. ss. rewrite bind_trigger in STEP_TGT.
              apply Bool.orb_true_elim in ORD. destruct ORD as [ORD | ORD].
              - inv STEP_TGT; ss; clarify. des. destruct ordr; ss. destruct ordr; ss.
              - inv STEP_TGT; ss; clarify. des. destruct ordw; ss.
                eapply inj_pair2 in H0. clarify. ired.
                do 3 eexists. splits; ss.
                { refl. }
                { ss. rewrite bind_trigger. eapply ILang.step_update_failure; eauto. }
                ss. grind.
                do 3 eexists. splits; ss; eauto.
                2:{ gbase. eapply CIH. econs. 3,4: ss. eauto.
                    2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
                    2:{ unfold update. des_ifs. }
                    apply match_le_update. eapply ml_mon; eauto. apply get_id_table_mon.
                    apply bot_spec.
                }
                eapply SeqEvent.input_match_bot.
          }
          2:{ eapply partial_same_mem; auto. }
          ii.
          inv STEP_TGT. ss. rewrite bind_trigger in LANG.
          inv LANG.
          * inv LOCAL. ss; clarify. eapply inj_pair2 in H0. clarify. ired.
            do 2 eexists. splits; ss.
            { refl. }
            { econs; eauto. econs; eauto. ss.
              rewrite bind_trigger. eapply ILang.step_update_success; eauto.
              econs; eauto.
            }
            grind.
            gbase. eapply CIH. econs. 3,4: ss. eauto.
            2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
            2:{ unfold update. des_ifs. }
            apply match_le_update. eapply ml_mon; eauto. apply get_id_table_mon.
            apply bot_spec.
          * inv LOCAL. ss. clear ORD.
            eapply inj_pair2 in H5. subst. destruct (p loc) eqn:PERM.
            { do 2 eexists. splits; ss; i.
              { refl. }
              { econs; eauto. econs; eauto. ss. rewrite bind_trigger.
                eapply ILang.step_update_failure; eauto.
                eapply SeqState.na_local_step_read. eauto. i.
                rewrite PERM in H. ss.
              }
              ired.
              gbase. eapply CIH. econs. 3,4: ss. eauto.
              2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
              2:{ unfold update. destruct (Ident.eqb lhs ret_reg); ss. }
              apply match_le_update. eapply ml_mon; eauto. apply get_id_table_mon.
              apply bot_spec.
            }
            { do 2 eexists. splits; ss; i.
              { refl. }
              { econs; eauto. econs; eauto. ss. rewrite bind_trigger.
                eapply ILang.step_update_failure; eauto.
                eapply SeqState.na_local_step_read. eauto. i.
                auto.
              }
              ired.
              gbase. eapply CIH. econs. 3,4: ss. eauto.
              2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
              2:{ unfold update. destruct (Ident.eqb lhs ret_reg); ss. }
              apply match_le_update. eapply ml_mon; eauto. apply get_id_table_mon.
              apply bot_spec.
            }

        + apply Bool.orb_false_elim in ORD. des.
          eapply sim_seq_atomic; eauto.
          { eapply partial_same_mem; eauto. }
          { i. inv H. inv LOCAL; ss; clarify.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
            - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des.
              (* easier way? *)
              symmetry in H. eapply simpobs in H.
              eapply eqit_inv_vis in H. des. unfold subevent in H.
              unfold resum, IFun in H. unfold ReSum_id in H. unfold id_ in H.
              unfold Id_IFun in H. clarify.
              unfold __guard__ in ORD1. des; clarify.
          }
          { ss. destruct rmw.
            - do 2 eexists. esplits. rewrite bind_trigger.
              eapply ILang.step_update_success; ss; eauto.
              econs; eauto. ss.
              destruct ordr; destruct ordw; ss; clarify.
            - destruct (Const.eqb old (SeqMemory.read loc mem)) eqn:EVAL.
              + destruct b.
                * do 2 eexists. esplits. rewrite bind_trigger.
                  eapply ILang.step_update_success; ss; eauto.
                  { econs 2; eauto. rewrite EVAL. ss. }
                  destruct ordr; destruct ordw; ss; clarify.
                * do 2 eexists. esplits. rewrite bind_trigger.
                  eapply ILang.step_update_failure; ss; eauto.
                  { econs 3; eauto. rewrite EVAL. ss. }
                  destruct ordr; destruct ordw; ss; clarify.
              + do 2 eexists. esplits. rewrite bind_trigger.
                eapply ILang.step_update_failure; ss; eauto.
                { econs 3; eauto. rewrite EVAL. ss. }
                destruct ordr; destruct ordw; ss; clarify.
          }
          ii. ss. irw in STEP_TGT. inv STEP_TGT.
          { ss; clarify.
            do 3 eexists. splits; ss.
            { refl. }
            { ss. rewrite bind_trigger. eapply ILang.step_update_success; ss; eauto. }
            { ss. splits; auto. refl. }
            eapply inj_pair2 in H1. clarify. grind.
            do 3 eexists. splits; ss; eauto.
            2:{ gbase. eapply CIH. econs. 3,4: ss. eauto.
                2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
                2:{ unfold update. des_ifs. }
                apply match_le_update. eapply ml_mon; eauto.
                apply get_id_table_mon. apply bot_spec.
            }
            eapply SeqEvent.input_match_bot.
          }
          { ss; clarify.
            do 3 eexists. splits; ss.
            { refl. }
            { ss. rewrite bind_trigger. eapply ILang.step_update_failure; ss; eauto. }
            eapply inj_pair2 in H0. clarify. grind.
            do 3 eexists. splits; ss; eauto.
            2:{ gbase. eapply CIH. econs. 3,4: ss. eauto.
                2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
                2:{ unfold update. des_ifs. }
                eapply match_le_update. eapply ml_mon; eauto.
                apply get_id_table_mon. apply bot_spec.
            }
            eapply SeqEvent.input_match_bot.
          }

      - rewrite ! denote_inst_fence. ired.
        eapply sim_seq_atomic; eauto.
        { apply partial_same_mem; eauto. }
        { i. inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
        }
        { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_fence; eauto. ss. }
        ii. ss. irw in STEP_TGT. inv STEP_TGT. ss; clarify.
        do 3 eexists. splits; ss.
        { refl. }
        { ss. rewrite bind_trigger. eapply ILang.step_fence. eauto. }
        eapply inj_pair2 in H0. clarify. grind.
        do 3 eexists. splits; ss; eauto.
        2:{ gbase. eapply CIH. econs. 3,4: ss. all: eauto.
            { eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
        }
        eapply SeqEvent.input_match_bot.

      - rewrite ! denote_inst_syscall. grind.
        eapply sim_seq_atomic; eauto.
        apply partial_same_mem; auto.
        { i. inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eq_itree_inv_vis in H. des. ss.
        }
        { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_syscall; eauto. ss. }
        ii. ss. irw in STEP_TGT. inv STEP_TGT. ss; clarify.
        do 3 eexists. splits; ss.
        { refl. }
        { ss. rewrite bind_trigger. erewrite (ml_exprs _ _ (src:=src_l) (tgt:=tgt_l)).
          eapply ILang.step_syscall. eauto.
          eapply ml_mon; eauto. etrans. 2: eapply get_id_table_inc.
          eapply id_update_inc.
        }
        { ss. refl. }
        eapply inj_pair2 in H0. clarify. grind.
        do 3 eexists. splits; ss; eauto.
        2:{ gbase; eapply CIH. econs. 3,4: ss. eauto.
            2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
            2:{ unfold update. des_ifs. }
            eapply match_le_update. eapply ml_mon; eauto.
            apply get_id_table_mon. apply bot_spec.
        }
        eapply SeqEvent.input_match_bot.

      - rewrite ! denote_inst_abort. grind. apply sim_seq_ub.

      - rewrite ! denote_inst_choose. grind.
        eapply sim_seq_na; eauto.
        apply partial_same_mem; auto.
        { do 2 eexists. esplits.
          - econs; eauto. rewrite bind_trigger. eapply ILang.step_choose; eauto.
            eapply SeqState.na_local_step_silent; eauto.
          - ss.
        }
        ii. inv STEP_TGT. rewrite bind_trigger in LANG. inv LANG. inv LOCAL.
        ss; clarify.
        eapply inj_pair2 in H0. clarify. grind.
        do 2 eexists. splits; ss.
        { refl. }
        { econs 1; eauto. econs; ss; eauto.
          - rewrite bind_trigger. eapply ILang.step_choose; eauto.
          - econs; eauto.
        }
        grind. instantiate (1:=val).
        gbase; eapply CIH. econs. 3,4: ss. eauto.
        2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply inst_g_inc. }
        2:{ unfold update. des_ifs. }
        eapply match_le_update. eapply ml_mon; eauto.
        apply get_id_table_mon. apply bot_spec.

        Unshelve. all: ss. all: exact 0.
    }

    - unfold build_state, itr_code.
      rewrite ! denote_block_cons. rewrite ! denote_stmt_ite. ired.
      eapply sim_seq_na.
      { eapply sim_seq_partial_imm. ss. refl. }
      { do 2 eexists. split.
        - econs.
          + econs; eauto.
          + econs 1.
        - ss.
      }
      ii. inv STEP_TGT. inv LANG. inv LOCAL. do 2 eexists. splits; ss.
      { refl. }
      { econs 1. econs.
        - econs; eauto.
        - econs 1.
      }
      destruct (is_zero (denote_expr src_l e)) eqn:CASE.
      2:{ ired. eapply sim_seq_ub; eauto. }
      hexploit ml_expr; eauto.
      { eapply ml_mon; eauto. eapply get_id_table_inc. }
      i. rewrite <- H; clear H.
      rewrite CASE.
      gbase. eapply CIH.
      des_ifs.
      + match goal with
        | [|- match_state {| SeqState.state := ?a; SeqState.memory := _ |} _ ] =>
          replace a with (itr_code (add_block sb2 b_src) src_l) end.
        2:{ rewrite itr_code_add_block. grind. }
        match goal with
        | [|- match_state _ {| SeqState.state := ?a; SeqState.memory := _ |} ] =>
          replace a with (itr_code (add_block tb2 b_tgt) tgt_l) end.
        2:{ rewrite itr_code_add_block. grind. }
        econs.
        3,4: unfold build_state; eauto.
        { eapply mc_add_block; eauto. }
        2:{ rewrite block_g_add_block. eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon.
            etrans. 2: eapply expr_g_inc. eapply join_le_g_r.
        }
        eapply ml_mon; eauto.
        rewrite get_id_table_add. apply get_id_table_mon.
        etrans. 2:apply id_update_expr_inc.
        apply p_join_inc_r. auto.
      + match goal with
        | [|- match_state {| SeqState.state := ?a; SeqState.memory := _ |} _ ] =>
          replace a with (itr_code (add_block sb1 b_src) src_l) end.
        2:{ rewrite itr_code_add_block. grind. }
        match goal with
        | [|- match_state _ {| SeqState.state := ?a; SeqState.memory := _ |} ] =>
          replace a with (itr_code (add_block tb1 b_tgt) tgt_l) end.
        2:{ rewrite itr_code_add_block. grind. }
        econs.
        3,4: unfold build_state; eauto.
        { eapply mc_add_block; eauto. }
        2:{ rewrite block_g_add_block. eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon.
            etrans. 2: eapply expr_g_inc. eapply join_le_g_l.
        }
        eapply ml_mon; eauto.
        rewrite get_id_table_add. apply get_id_table_mon.
        etrans. 2:apply id_update_expr_inc.
        apply p_join_inc_l. auto.

    - unfold build_state, itr_code.
      rewrite ! denote_block_cons. rewrite ! denote_stmt_while2. ired.
      rewrite ! denote_block_cons. rewrite ! denote_stmt_inst.
      rewrite ! denote_inst_skip. ired.
      hexploit ml_expr; eauto.
      { eapply ml_mon; eauto. ss. eapply get_id_table_inc. }
      i. rewrite H; clear H.
      des_ifs; ired.
      + eapply sim_seq_na.
        { eapply sim_seq_partial_imm. ss. refl. }
        { do 2 eexists. split.
          - econs.
            + econs; eauto.
            + econs.
          - ss.
        }
        ii. inv STEP_TGT. inv LANG. inv LOCAL.
        do 2 eexists. splits; ss.
        { refl. }
        { econs 1. econs.
          - econs; eauto.
          - econs 1.
        }
        gbase. eapply CIH.
        rewrite ! denote_block_nil. ired.
        econs.
        3,4: unfold build_state, itr_code; eauto.
        eauto.
        2:{ eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply bot_g_spec. }
        eapply ml_mon; eauto.
        eapply get_id_table_mon. apply bot_spec. auto.

      + eapply sim_seq_na.
        { eapply sim_seq_partial_imm. ss. refl. }
        { do 2 eexists. split.
          - econs.
            + econs; eauto.
            + econs.
          - ss.
        }
        ii. inv STEP_TGT. inv LANG. inv LOCAL.
        do 2 eexists. splits; ss.
        { refl. }
        { econs 1. econs.
          - econs; eauto.
          - econs 1.
        }
        gbase. eapply CIH.
        match goal with
        | [|- match_state {| SeqState.state := ?a; SeqState.memory := _ |} _ ] =>
          replace a with
              (itr_code (add_block sb (cons Inst.skip (cons (while e sb) b_src))) src_l)
        end.
        2:{ rewrite itr_code_add_block. rewrite denote_add_block. grind.
            rewrite ! denote_block_cons. grind.
            rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind.
        }
        match goal with
        | [|- match_state _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
          replace a with
              (itr_code (add_block tb (cons Inst.skip (cons (while e tb) b_tgt))) tgt_l)
        end.
        2:{ rewrite itr_code_add_block. rewrite denote_add_block. grind.
            rewrite ! denote_block_cons. grind.
            rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind.
        }
        econs.
        3,4: unfold build_state; eauto.
        { eapply mc_add_block. instantiate (1:=gd).
          { eapply mc_mon_gdata. 3: eapply MC2. 2: eapply update_gs_inc.
            unfold lt_g in GD. des.
            rewrite block_g_big. refl.
            etrans. 2: eapply GD. etrans. 2: eapply block_g_inc. etrans. 2: eapply expr_g_inc. refl. }
          econs 2.
          { rewrite inst_g_skip. refl. }
          econs 4; eauto.
        }
        2:{ rewrite block_g_add_block. rewrite block_g_inst. rewrite inst_g_skip. rewrite block_g_while.
            eapply le_g_lt_g. 2: eapply GD. eapply block_g_mon. eapply expr_g_mon.
            rewrite block_g_big. refl. refl.
        }
        rewrite get_id_table_add. ss. rewrite get_id_table_idm. auto. auto.

      + eapply sim_seq_tau; eauto. eapply partial_same_mem; eauto. eapply sim_seq_ub.

    - destruct (intro_insts gd1 ds) eqn:INTRO; ss.
      { eauto. }
      destruct ds; ss. inv INTRO.
      eapply intro_inst_sim; eauto.
      { eapply le_g_lt_g2. 2: eapply GD0. auto. }
      i. clear ML. rename H into ML. des.
      unfold build_state, itr_code.
      gbase. eapply CIH.
      econs. 3,4: ss. all: eauto.

  Qed.

End SIM.
