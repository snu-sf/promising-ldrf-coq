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

From PromisingLib Require Import Event.
Require Export ITreeLib.
Require Export Program.

Require Import Sequential.
Require Import SimAux.

Require Import Knowledge.
Require Import FoldN.
Require Import Opt4.

Require Import ITreeLangProof.
Require Import ITreeLang.



Section SIM.

  Variable O4: Opt4.t.

  Variable match_data : (GD O4) -> Perms.t -> SeqMemory.t -> lenv -> Prop.

  Hypothesis md_mon: forall d1 d2 p m l (LE: le2 d1 d2) (MD: match_data d2 p m l), match_data d1 p m l.

  Hypothesis md_skip:
    forall mp p m le (MD: match_data mp p m le)
    ,
      match_data (inst_gd Inst.skip mp) p m le.

  Hypothesis md_assign:
    forall mp p m le (MD: match_data mp p m le)
      x v eval
      (EVAL: denote_expr le v = eval)
    ,
      match_data (inst_gd (Inst.assign x v) mp) p m (update x eval le).

  Hypothesis md_load_na:
    forall mp p m le (MD: match_data mp p m le)
      x l ord (ORD: Ordering.le ord Ordering.na)
      val (VAL: Perm.le Perm.high (p l) -> Const.le val (SeqMemory.read l m))
    ,
      match_data (inst_gd (Inst.load x l ord) mp) p m (update x val le).


  Hypothesis md_load_at:
    forall mp p m le (MD: match_data mp p m le)
      x l ord
      val ev i o p1 m1
      (EV: ev = ProgramEvent.read l val ord)
      (ATOMIC: is_atomic_event ev)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.load x l ord) mp) p1 m1 (update x val le).


  Hypothesis md_store_na:
    forall mp p m le (MD: match_data mp p m le)
      x e ord (ORD: Ordering.le ord Ordering.na)
      (PERM : (p x) = Perm.high)
      eval (EVAL: denote_expr le e = eval)
    ,
      match_data (inst_gd (Inst.store x e ord) mp) p (SeqMemory.write x eval m) le.

  Hypothesis md_store_at:
    forall mp p m le (MD: match_data mp p m le)
      x e ord
      ev i o p1 m1
      (EV: ev = ProgramEvent.write x (denote_expr le e) ord)
      (ATOMIC: is_atomic_event ev)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.store x e ord) mp) p1 m1 le.


  Hypothesis md_update_na:
    forall mp p m le (MD: match_data mp p m le)
      x l rmw ordr ordw (ORD: (Ordering.le ordr Ordering.na) \/ (Ordering.le ordw Ordering.na))
      val
    ,
      match_data (inst_gd (Inst.update x l rmw ordr ordw) mp) p m (update x val le).

  Hypothesis md_update_at_success:
    forall mp p m le (MD: match_data mp p m le)
      x l rmw ordr ordw
      ev i o p1 m1
      valr valw val
      (EV: ev = ProgramEvent.update l valr valw ordr ordw)
      (ATOMIC: is_atomic_event ev)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.update x l rmw ordr ordw) mp) p1 m1 (update x val le).

  Hypothesis md_update_at_failure:
    forall mp p m le (MD: match_data mp p m le)
      x l rmw ordr ordw
      ev i o p1 m1
      valr val
      (EV: ev = ProgramEvent.read l valr ordr)
      (ATOMIC: is_atomic_event ev)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.update x l rmw ordr ordw) mp) p1 m1 (update x val le).


  Hypothesis md_fence:
    forall mp p m le (MD: match_data mp p m le)
      ordr ordw
      ev i o p1 m1
      (EV: ev = ProgramEvent.fence ordr ordw)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.fence ordr ordw) mp) p1 m1 le.


  Hypothesis md_syscall:
    forall mp p m le (MD: match_data mp p m le)
      x es
      sys ev i o p1 m1
      (EV: ev = ProgramEvent.syscall sys)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
      val
    ,
      match_data (inst_gd (Inst.syscall x es) mp) p1 m1 (update x val le).


  Hypothesis md_choose:
    forall mp p m le (MD: match_data mp p m le)
      x val,
      match_data (inst_gd (Inst.choose x) mp) p m (update x val le).



  Definition build_state (c: block) (le: lenv) (m: SeqMemory.t) :=
    SeqState.mk (lang Const.t) (itr_code c le) m.

  Variant match_state p (src tgt: (SeqState.t (lang Const.t))) :=
  | match_state_intro
      mp le mem src_c tgt_c
      (MC: match_code4 mp src_c tgt_c)
      (MD: match_data mp p mem le)
      (SRC: src = build_state src_c le mem)
      (TGT: tgt = build_state tgt_c le mem)
    :
      match_state p src tgt
  .


  Variable sim_val: Const.t -> Const.t -> Prop.
  Hypothesis sim_val_refl: forall a, sim_val a a.
  Let term := term sim_val.

  Lemma sim_seq_inst
        r g p
        lenv mem mp
        (i: Inst.t) src tgt
        (MD: match_data mp p mem lenv)
        (src_k tgt_k: _ -> itree _ _)
        (SRC: src = @SeqState.mk (lang _) (x <- denote_stmt lenv i;; src_k x) mem)
        (TGT: tgt = @SeqState.mk (lang _) (x <- denote_stmt lenv i;; tgt_k x) mem)
        (PARTIAL: sim_seq_partial_case p Flags.bot src tgt)
        (SIM: forall up lenv1 mem1,
            (<<MD1: match_data (inst_gd i mp) up mem1 lenv1>>) ->
            gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term up Flags.bot
                    (@SeqState.mk (lang _) (src_k (lenv1, ())) mem1)
                    (@SeqState.mk (lang _) (tgt_k (lenv1, ())) mem1))
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p Flags.bot src tgt.
  Proof.
    clarify.
    destruct i; clarify.
    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. grind.
      eapply sim_seq_tau; eauto.
      eapply partial_same_mem; eauto.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_assign. grind.
      eapply sim_seq_tau; eauto.
      eapply partial_same_mem; eauto.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_load. grind.
      destruct (Ordering.le Ordering.plain ord) eqn:ORD.
      + eapply sim_seq_atomic; eauto.
        { eapply partial_same_mem; eauto. }
        { i. inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        }
        { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_read; eauto. ss. }
        ii. ss.
        irw in STEP_TGT. inv STEP_TGT. ss; clarify.
        do 3 eexists. splits; ss.
        { refl. }
        { rewrite bind_trigger. eapply ILang.step_read. eauto. }
        grind. eapply inj_pair2 in H0. clarify. grind.
        do 3 eexists. splits; eauto.
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
        ss. eapply inj_pair2 in H3. subst k.
        destruct (p rhs) eqn:PERM.
        { ired. do 2 eexists. splits; ss.
          { refl. }
          { econs 1; eauto. econs; ss; eauto.
            - rewrite bind_trigger. eapply ILang.step_read; eauto.
            - econs. eauto. i. rewrite PERM in H. simpl in H. inv H.
          }
          instantiate (1:=val). ired.
          eapply SIM; eauto. red.
          eapply md_load_na; eauto. rewrite PERM. ss.
        }
        { ired. do 2 eexists. splits; ss.
          { refl. }
          { econs 1; eauto. econs; ss; eauto.
            - rewrite bind_trigger. eapply ILang.step_read; eauto.
            - econs; eauto.
          }
          ired. eapply SIM. red.
          eapply md_load_na; eauto.
        }

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_store. grind.
      destruct (Ordering.le Ordering.plain ord) eqn:ORD.
      + eapply sim_seq_atomic; eauto.
        eapply partial_same_mem; eauto.
        { i. inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. inv H. destruct ord; ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        }
        { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_write; eauto. ss. }
        ii. ss. irw in STEP_TGT.
        inv STEP_TGT. ss; clarify.
        do 3 eexists. splits; ss.
        { refl. }
        { ss. rewrite bind_trigger. eapply ILang.step_write. eauto. }
        { ss. splits; auto. refl. }
        grind. eapply inj_pair2 in H0. clarify.
        do 3 eexists. splits; eauto.
        eapply SeqEvent.input_match_bot.

      + destruct (p lhs) eqn:PERM.
        { gstep. econs 2. ii. do 3 eexists. splits.
          econs 1. econs 1.
          rewrite bind_trigger. econs; eauto.
          econs; eauto. econs. econs; eauto. econs; eauto.
          destruct ord; ss. rewrite PERM. ss.
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
          rewrite PERM in *. ss. eapply inj_pair2 in H4. clarify.
          do 2 eexists. splits; ss.
          { refl. }
          { econs 1; eauto. econs; ss; eauto.
            - rewrite bind_trigger. eapply ILang.step_write; eauto.
            - econs; eauto. rewrite PERM; ss.
          }
          eapply SIM.
          eapply md_store_na; eauto.
        }

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_update. grind.
      destruct (orb (Ordering.le ordr Ordering.na) (Ordering.le ordw Ordering.na)) eqn:ORD.
      + (*na, success-ub, fail-read*)
        gstep. econs 1.
        { ii. ss. unfold ILang.is_terminal in TERMINAL_TGT. des.
          irw in TERMINAL_TGT. symmetry in TERMINAL_TGT. inv TERMINAL_TGT.
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
              2:{ eapply SIM. eapply md_update_at_failure; eauto. }
              eapply SeqEvent.input_match_bot.
        }
        2:{ eapply partial_same_mem; auto. }
        ii.
        inv STEP_TGT. ss. rewrite bind_trigger in LANG. inv LANG.
        * inv LOCAL. ss; clarify. eapply inj_pair2 in H0. clarify. ired.
          do 2 eexists. splits; ss.
          { refl. }
          { econs; eauto. econs; eauto. ss.
            rewrite bind_trigger. eapply ILang.step_update_success; eauto.
            econs; eauto.
          }
          grind. eapply SIM. eapply md_update_na; eauto.

        * inv LOCAL. ss. clear ORD.
          eapply inj_pair2 in H5. subst. destruct (p loc) eqn:PERM.
          { do 2 eexists. splits; ss; i.
            { refl. }
            { econs; eauto. econs; eauto. ss. rewrite bind_trigger.
              eapply ILang.step_update_failure; eauto.
              eapply SeqState.na_local_step_read. eauto. i.
              rewrite PERM in H. ss.
            }
            ired. eapply SIM. red. eapply md_update_na; eauto.
          }
          { do 2 eexists. splits; ss; i.
            { refl. }
            { econs; eauto. econs; eauto. ss. rewrite bind_trigger.
              eapply ILang.step_update_failure; eauto.
              eapply SeqState.na_local_step_read. eauto. i. eauto.
            }
            ired. eapply SIM. eapply md_update_na; eauto.
          }

      + apply Bool.orb_false_elim in ORD. des.
        eapply sim_seq_atomic; eauto.
        { eapply partial_same_mem; eauto. }
        { i. inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. inv H.
            unfold __guard__ in ORD1. des; [destruct ordr; ss | destruct ordw; ss].
        }
        { ss. destruct rmw.
          - do 2 eexists. esplits. rewrite bind_trigger.
            eapply ILang.step_update_success; ss; eauto.
            { econs; eauto. }
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
          grind. eapply inj_pair2 in H1. clarify. ired.
          do 3 eexists. splits; eauto.
          2:{ eapply SIM. eapply md_update_at_success; eauto. ss. apply andb_true_intro; auto. }
          eapply SeqEvent.input_match_bot.
        }
        { ss; clarify.
          do 3 eexists. splits; ss.
          { refl. }
          { ss. rewrite bind_trigger. eapply ILang.step_update_failure; ss; eauto. }
          grind. eapply inj_pair2 in H0. clarify. ired.
          do 3 eexists. splits; eauto.
          eapply SeqEvent.input_match_bot.
        }

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_fence. grind.
      eapply sim_seq_atomic; eauto.
      { apply partial_same_mem; eauto. }
      { i. inv H. inv LOCAL; ss; clarify.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
      }
      { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_fence; eauto. ss. }
      ii. ss. irw in STEP_TGT. inv STEP_TGT. ss; clarify.
      do 3 eexists. splits; ss.
      { refl. }
      { ss. rewrite bind_trigger. eapply ILang.step_fence. eauto. }
      grind. eapply inj_pair2 in H0. clarify.
      do 3 eexists. splits; eauto.
      eapply SeqEvent.input_match_bot.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_syscall. grind.
      eapply sim_seq_atomic; eauto.
      apply partial_same_mem; auto.
      { i. inv H. inv LOCAL; ss; clarify.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
      }
      { ss. do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_syscall; eauto. ss. }
      ii. ss. irw in STEP_TGT. inv STEP_TGT. ss; clarify.
      do 3 eexists. splits; ss.
      { refl. }
      { ss. rewrite bind_trigger. eapply ILang.step_syscall. eauto. }
      { ss. refl. }
      grind. eapply inj_pair2 in H0. clarify. ired.
      do 3 eexists. splits; eauto.
      eapply SeqEvent.input_match_bot.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_abort. grind. apply sim_seq_ub.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_choose. grind.
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
      eapply SIM; eauto.

      Unshelve. all: ss. all: exact 0.
  Qed.


  Hypothesis sim_seq_inst_opt:
    forall r g p
      lenv mem mp mp'
      (i i_opt: Inst.t) src tgt
      (MD: match_data mp p mem lenv)
      (src_k tgt_k: _ -> itree _ _)
      (SRC: src = @SeqState.mk (lang _) (x <- denote_stmt lenv i;; src_k x) mem)
      (TGT: tgt = @SeqState.mk (lang _) (x <- denote_stmt lenv i_opt;; tgt_k x) mem)
      (PARTIAL: sim_seq_partial_case p Flags.bot src tgt)
      (SIM: forall up lenv1 mem1,
          (<<MD1: match_data (inst_gd i mp) up mem1 lenv1>>) ->
          gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term up Flags.bot
                  (@SeqState.mk (lang _) (src_k (lenv1, ())) mem1)
                  (@SeqState.mk (lang _) (tgt_k (lenv1, ())) mem1))
      (LE: le2 mp' mp)
      (OPT: (Opt4.do_opt O4) mp' i)
      (IOPT: i_opt = (Opt4.opt_inst O4) mp' i),
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p Flags.bot src tgt.

  Hypothesis block_d_dec: forall blk p d f (FUN: f = @block_d O4 blk p), (Opt4.le O4) (f (f d)) (f d).
  Hypothesis block_d_fix: forall blk f (FUN: f = @block_d O4 blk) p,
      @n_fix (Opt4.D O4) (MLattice.eq (Opt4.M O4)) (MLattice.eq_Equiv (Opt4.M O4)) (f p) (S (Opt4.N O4)).


  Theorem match_state_sim
          p src tgt
          (MS: match_state p src tgt)
    :
      sim_seq term p Flags.bot src tgt.
  Proof.
    ginit. do 4 revert1. gcofix CIH. i. inv MS.
    inv MC.
    - eapply sim_seq_term; ss; eauto.
      { unfold itr_code. rewrite denote_block_nil. grind. unfold ILang.is_terminal. eauto. }
      ii. eexists. splits; ss; eauto.
      { ss. unfold itr_code; rewrite ! denote_block_nil. grind. econs; eauto. }
      refl. refl.

    - unfold build_state. unfold itr_code.
      rewrite ! denote_block_cons. grind.
      eapply sim_seq_inst; ss; eauto.
      { apply partial_same_mem; auto. }
      i. gbase. eapply CIH; eauto. econs; eauto.

    - unfold build_state. unfold itr_code.
      rewrite ! denote_block_cons. grind.
      eapply sim_seq_inst_opt; ss; eauto.
      { apply partial_same_mem; auto. }
      i. gbase; eapply CIH; eauto. econs; eauto.

    - unfold build_state. unfold itr_code.
      rewrite ! denote_block_cons. rewrite ! denote_stmt_ite. grind.
      + eapply sim_seq_tau; ss. apply partial_same_mem; auto.
        match goal with
        | [|- gupaco7 _ _ _  _ _ _ _ _ ?x _] =>
          replace x with (build_state (add_block sb2 b_src) le mem) end.
        2:{ unfold build_state, itr_code. rewrite denote_add_block. grind. }
        match goal with
        | [|- gupaco7 _ _ _ _ _ _ _ _  _ ?x] =>
          replace x with (build_state (add_block tb2 b_tgt) le mem) end.
        2:{ unfold build_state, itr_code. rewrite denote_add_block. grind. }
        gbase. eapply CIH.
        econs. 2: eauto. 2,3: eauto.
        eapply match_code4_add_block; eauto. eapply (@MLattice.meet_is_min_r (ML2 O4)).
      + eapply sim_seq_tau; ss. apply partial_same_mem; auto.
        match goal with
        | [|- gupaco7 _ _ _ _ _ _ _ _ {| SeqState.state := ?x; SeqState.memory := _ |} _] =>
          replace x with (itr_code (add_block sb1 b_src) le) end.
        2:{ unfold itr_code. rewrite denote_add_block. grind. }
        match goal with
        | [|- gupaco7 _ _ _ _ _ _ _ _  _ {| SeqState.state := ?x; SeqState.memory := _ |}] =>
          replace x with (itr_code (add_block tb1 b_tgt) le) end.
        2:{ unfold itr_code. rewrite denote_add_block. grind. }
        gbase. eapply CIH.
        econs. 2: eauto. 2,3: ss.
        eapply match_code4_add_block; eauto. eapply (@MLattice.meet_is_min_l (ML2 O4)).
      + eapply sim_seq_tau; eauto. eapply partial_same_mem; eauto. eapply sim_seq_ub.

    - unfold build_state. unfold itr_code.
      rewrite ! denote_block_cons. rewrite ! denote_stmt_while2. grind.
      + rewrite ! denote_block_cons. rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. ired.
        eapply sim_seq_tau; ss. apply partial_same_mem; auto.
        rewrite ! denote_block_nil. ired.
        gbase. eapply CIH.
        econs. 2: eauto.
        2,3: unfold build_state, itr_code; eauto.
        eapply match_code4_mon; eauto. eapply (@MLattice.meet_is_min_l (ML2 O4)).
      + rewrite ! denote_block_cons. rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. ired.
        eapply sim_seq_tau; ss. apply partial_same_mem; auto.
        match goal with
        | [|- gupaco7 _ _ _ _ _ _ _ _ ?x _] =>
          replace x with (build_state (add_block sb (cons Inst.skip (cons (while e sb) b_src))) le mem) end.
        2:{ unfold build_state, itr_code. f_equal. rewrite ! denote_add_block. grind.
            rewrite ! denote_block_cons. grind. rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind.
        }
        match goal with
        | [|- gupaco7 _ _ _ _ _ _ _ _ _ ?x] =>
          replace x with (build_state (add_block tb (cons Inst.skip (cons (while e tb) b_tgt))) le mem) end.
        2:{ unfold build_state, itr_code. f_equal. rewrite ! denote_add_block. grind.
            rewrite ! denote_block_cons. grind. rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind.
        }
        gbase. eapply CIH.
        econs. 2: eauto. 2,3: eauto.
        eapply match_code4_add_block; eauto. refl.
        { eapply match_code4_mon; eauto. eapply (@MLattice.meet_is_min_l (ML2 O4)). }
        econs 2; eauto. rewrite skip_gd. econs 5; eauto.
        * ss. rewrite fold_n_one_in. ss. rewrite fold_n_one_out in *. rewrite n_fix_fix.
          2:{ eapply block_gd_fix; eauto. }
          erewrite meet_comm2. hexploit le_spec2. i. des. clear H0. rewrite <- H.
          2:{ replace (1 + (Opt4.N O4)) with (S (Opt4.N O4)). 2: ss.
              eapply (fold_n_prop mp (block_gd sb)).
              refl. etrans; eauto. eapply block_gd_mon. i. eapply block_gd_dec; eauto.
          }
          eapply match_code4_mon; eauto. eapply (@MLattice.meet_is_min_r (ML2 O4)).
        * ss. rewrite fold_n_one_in. ss. rewrite fold_n_one_out in *. rewrite n_fix_fix.
          2:{ eapply block_gd_fix; eauto. }
          erewrite meet_comm2. hexploit le_spec2. i. des. clear H0. rewrite <- H.
          2:{ replace (1 + (Opt4.N O4)) with (S (Opt4.N O4)). 2: ss.
              eapply (fold_n_prop mp (block_gd sb)).
              refl. etrans; eauto. eapply block_gd_mon. i. eapply block_gd_dec; eauto.
          }
          eapply match_code4_mon; eauto. eapply (@MLattice.meet_is_min_r (ML2 O4)).
      + eapply sim_seq_tau; eauto. eapply partial_same_mem; eauto. eapply sim_seq_ub.

  Qed.

End SIM.
