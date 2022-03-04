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

Require Import FoldN.
Require Import Knowledge.

Require Import Sequential.
Require Import FlagAux.
Require Import SimAux.
Require Import SeqAux.

Require Import Opt2.
Require Import Opt2Sim.

Require Import ITreeLangNotations.
Require Import ITreeLangProof.
Require Import ITreeLang.

Require Import DeadStoreElim.
Require Import DeadStoreElimProof1.
Require Import DeadStoreElimProof2.

Require Import SequentialITree.
Require Export ITreeLib.





(*from 210315 commit's itree main repo, theories/Eq/Eq.v*)

Ltac inv_eq_VisF H :=
  lazymatch type of H with
  | (VisF _ _ = @VisF _ _ _ ?X ?e ?k) =>
    refine
      match H in _ = w return
            match w with
            | VisF e k => _
            | _ => False
            end
      with eq_refl => _
      end; try clear H X e k
  end.



Lemma eqit_inv_bind_vis :
  forall {A B C E X RR} b1 b2
    (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxc : X -> itree E C),
    eqit RR b1 b2 (ITree.bind ma kab) (Vis e kxc) ->
    (exists (kxa : X -> itree E A), (eqit eq b1 b2 ma (Vis e kxa)) /\
                              forall (x:X), eqit RR b1 b2 (ITree.bind (kxa x) kab) (kxc x)) \/
    (exists (a : A), eqit eq b1 b2 ma (Ret a) /\ eqit RR b1 b2 (kab a) (Vis e kxc)).
Proof.
  intros. punfold H. unfold eqit_ in H. cbn in *.
  remember (observe (ITree.bind ma kab)) as tl.
  remember (VisF e kxc) as tr.
  revert ma kab Heqtl kxc Heqtr.
  induction H; try discriminate.
  - intros. unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn:Ema; try discriminate.
    + right. exists r. split.
      * pfold; red. rewrite Ema. constructor. auto.
      * pfold; red. unfold observe at 1; unfold _observe. rewrite <- Heqtl.
        constructor; auto.
    + left.
      symmetry in Heqtl.
      revert k2 REL Heqtr. inv_eq_VisF Heqtl. intros.
      inv_eq_VisF Heqtr.
      exists k. split.
      * pfold; red. rewrite Ema. constructor. red. left. apply reflexivity.
      * pclearbot. auto.
  - intros. subst.
    unfold observe, _observe in Heqtl; cbn in Heqtl.
    destruct (observe ma) eqn: Ema; try discriminate.
    + right; exists r; split.
      * rewrite itree_eta, Ema; reflexivity.
      * pfold. red. unfold observe at 1; unfold _observe; rewrite <- Heqtl. constructor; auto.
    + inv Heqtl. specialize (IHeqitF _ _ eq_refl _ eq_refl).
      destruct IHeqitF as [(k0 & ? & ?) | (a & ? & ?)]; [left | right].
      * exists k0. split; auto.
        pfold; red; rewrite Ema; constructor; punfold H0.
      * exists a. split; auto.
        pfold; red; rewrite Ema; constructor; punfold H0.
Qed.

Lemma eutt_inv_bind_vis:
  forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxb : X -> itree E B),
    ITree.bind ma kab ≈ Vis e kxb ->
    (exists (kca : X -> itree E A), (ma ≈ Vis e kca) /\ forall (x:X), (ITree.bind (kca x) kab) ≈ (kxb x)) \/
    (exists (a : A), (ma ≈ Ret a) /\ (kab a ≈ Vis e kxb)).
Proof.
  intros. apply eqit_inv_bind_vis. auto.
Qed.

Lemma eqitree_inv_bind_vis:
  forall {A B E X} (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxb : X -> itree E B),
    ITree.bind ma kab ≅ Vis e kxb ->
    (exists (kca : X -> itree E A), (ma ≅ Vis e kca) /\ forall (x:X), (ITree.bind (kca x) kab) ≅ (kxb x)) \/
    (exists (a : A), (ma ≅ Ret a) /\ (kab a ≅ Vis e kxb)).
Proof.
  intros. apply eqit_inv_bind_vis. auto.
Qed.





Section AUX.

  Lemma oracle_step_wf:
    forall o1 o2 e i o (WF: Oracle.wf o1) (STEP: Oracle.step e i o o1 o2), Oracle.wf o2.
  Proof.
    i. punfold WF. 2: eapply Oracle.wf_mon. inv WF. hexploit WF0; eauto. i; des. pclearbot. auto.
  Qed.

  Lemma itr_code_cons
        (s: stmt) b le
    :
      itr_code (cons s b) le = '(le1, _) <- denote_stmt le s;; itr_code b le1.
  Proof.
    unfold itr_code. rewrite denote_block_cons. grind.
  Qed.


  Lemma steps_first_block_prop
        b1 b2 le sm p o th tr
        (P: SeqThread.t (lang _) -> Prop)
        (WF: Oracle.wf o)
        (STEPS: SeqThread.steps (SeqState.na_step (lang:=lang _)) tr
                                {|
                                  SeqThread.state := (@SeqState.mk (lang _) (itr_code b1 le) sm);
                                  SeqThread.perm := p;
                                  SeqThread.oracle := o
                                |} th)
        (PROP: P th)
        (BASE : forall b1 b2 le sm p o,
            P
              {|
                SeqThread.state := (@SeqState.mk (lang _) (itr_code b1 le) sm);
                SeqThread.perm := p;
                SeqThread.oracle := o
              |} ->
            P
              {|
                SeqThread.state := (@SeqState.mk (lang _) (itr_code (add_block b1 b2) le) sm);
                SeqThread.perm := p;
                SeqThread.oracle := o
              |})
    :
      exists th0,
        (SeqThread.steps (SeqState.na_step (lang:=lang _)) tr
                         {|
                           SeqThread.state := (@SeqState.mk (lang _) (itr_code (add_block b1 b2) le) sm);
                           SeqThread.perm := p;
                           SeqThread.oracle := o
                         |} th0) /\ (P th0).
  Proof.
    depgen b2.
    match goal with | [STEPS: SeqThread.steps _ _ ?a _ |- _] => remember a as th0 end.
    depgen WF. depgen PROP. depgen Heqth0. move th after b1. move th0 after b1. move STEPS after b1. move BASE after th.
    revert_until STEPS. induction STEPS; i; clarify; ss.
    { esplits. econs; eauto. eauto. }

    { clear BASE. destruct b1.
      { exfalso. unfold itr_code in STEP. rewrite denote_block_nil in STEP. irw in STEP. inv STEP. inv STEP0. inv LANG. }

      destruct hd.
      { destruct i; rewrite itr_code_cons in STEP; rewrite denote_stmt_inst in STEP.
        - rewrite denote_inst_skip in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. }
          auto. auto. i. des. exists th0; split; auto. econs 2; eauto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. ired.
          econs 1. repeat (econs; eauto).

        - rewrite denote_inst_assign in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. }
          auto. auto. i. des. exists th0; split; auto. econs 2; eauto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_assign. ired.
          econs 1. repeat (econs; eauto).

        - rewrite denote_inst_load in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL. eapply inj_pair2 in H3. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. grind. }
          auto. auto. i. des. exists th0; split; auto. econs 2; eauto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_load. ired.
          econs 1. econs.
          2:{ econs 2. eauto. eauto. }
          rewrite bind_trigger. econs 3. grind.

        - rewrite denote_inst_store in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL. eapply inj_pair2 in H4. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. }
          auto. auto. i. des. exists th0; split; auto. econs 2; eauto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_store. ired.
          econs 1. econs.
          2:{ econs 3; eauto. }
          rewrite bind_trigger. econs 4. grind.

        - rewrite denote_inst_update in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG; inv LOCAL. eapply inj_pair2 in H5. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. grind. }
          auto. auto. i. des. exists th0; split; auto. econs 2; eauto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_update. ired.
          econs 1. econs.
          2:{ econs 2; eauto. }
          rewrite bind_trigger. econs 6; eauto. grind.

        - rewrite denote_inst_fence in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL.

        - rewrite denote_inst_syscall in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL.

        - rewrite denote_inst_abort in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL.

        - rewrite denote_inst_choose in STEP. irw in STEP.
          inv STEP. inv STEP0. inv LANG. inv LOCAL. eapply inj_pair2 in H1. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. grind. }
          auto. auto. i. des. exists th0; split; auto. econs 2; eauto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_choose. ired.
          econs 1. econs.
          2:{ econs 1. }
          rewrite bind_trigger. econs 2. grind.
      }

      - rewrite itr_code_cons in STEP. rewrite denote_stmt_ite in STEP. irw in STEP.
        inv STEP. inv STEP0. inv LANG. inv LOCAL. des_ifs.
        + hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. unfold itr_code at 1; rewrite <- itr_code_add_block. ss. }
          auto. auto. i. instantiate (1:= b2) in H. des. exists th0; split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_ite. ired. rewrite Heq.
          econs 2. 2: eauto. econs 1. repeat (econs; eauto).
          unfold itr_code at 2; rewrite <- itr_code_add_block. rewrite add_block_assoc. auto.
        + hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. unfold itr_code at 1; rewrite <- itr_code_add_block. ss. }
          auto. auto. i. instantiate (1:= b2) in H. des. exists th0; split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_ite. ired. rewrite Heq.
          econs 2. 2: eauto. econs 1. repeat (econs; eauto).
          unfold itr_code at 2; rewrite <- itr_code_add_block. rewrite add_block_assoc. auto.
        + hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. instantiate (1:=le). instantiate (1:=(cons Inst.abort b1)).
            rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_abort. rewrite bind_trigger. grind. }
          auto. auto. i. instantiate (1:= b2) in H. des. exists th0; split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_ite. ired. rewrite Heq.
          econs 2. 2: eauto. econs 1. repeat (econs; eauto).
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_abort. grind.

      - rewrite itr_code_cons in STEP. rewrite denote_stmt_while3 in STEP. irw in STEP.
        inv STEP. inv STEP0. inv LANG. inv LOCAL. des_ifs.
        + hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. unfold itr_code at 1; rewrite <- itr_code_add_block. ss. }
          auto. auto. i. instantiate (1:= b2) in H. des. exists th0; split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_while3. ired. rewrite Heq.
          econs 2. 2: eauto. econs 1. repeat (econs; eauto).
          unfold itr_code at 2; rewrite <- itr_code_add_block. rewrite add_block_nil_unit. auto.
        + hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. unfold itr_code at 1; rewrite <- itr_code_add_block. ss. }
          auto. auto. i. instantiate (1:= b2) in H. des. exists th0; split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_while3. ired. rewrite Heq.
          econs 2. 2: eauto. econs 1. repeat (econs; eauto).
          unfold itr_code at 2; rewrite <- itr_code_add_block. rewrite add_block_assoc. auto.
        + hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. instantiate (1:=le). instantiate (1:=(cons Inst.abort b1)).
            rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_abort. rewrite bind_trigger. grind. }
          auto. auto. i. instantiate (1:= b2) in H. des. exists th0; split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_while3. ired. rewrite Heq.
          econs 2. 2: eauto. econs 1. repeat (econs; eauto).
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_abort. grind.
    }

    { clear BASE. destruct b1.
      { exfalso. unfold itr_code in STEP. rewrite denote_block_nil in STEP. irw in STEP. inv STEP. inv LANG. }

      destruct hd.
      { destruct i0; rewrite itr_code_cons in STEP; rewrite denote_stmt_inst in STEP.
        - rewrite denote_inst_skip in STEP. irw in STEP.
          inv STEP. inv LANG. ss.

        - rewrite denote_inst_assign in STEP. irw in STEP.
          inv STEP. inv LANG. ss.

        - rewrite denote_inst_load in STEP. irw in STEP.
          inv STEP. inv LANG. ss. eapply inj_pair2 in H3. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. grind. }
          auto.
          { eapply oracle_step_wf; eauto. }
          i. des. exists th0; split; auto. econs 3; eauto.
          rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_load. ired.
          econs; eauto. rewrite bind_trigger. econs; eauto. grind.

        - rewrite denote_inst_store in STEP. irw in STEP.
          inv STEP. inv LANG. ss. eapply inj_pair2 in H4. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. }
          auto.
          { eapply oracle_step_wf; eauto. }
          i. des. exists th0; split; auto. econs 3; eauto.
          rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_store. ired.
          econs; eauto. rewrite bind_trigger. econs; eauto.

        - rewrite denote_inst_update in STEP. irw in STEP.
          inv STEP. inv LANG; ss.
          + eapply inj_pair2 in H5. subst k.
            hexploit IHSTEPS; clear IHSTEPS.
            { do 2 f_equal. grind. }
            auto.
            { eapply oracle_step_wf; eauto. }
            i. des. exists th0; split; auto. econs 3; eauto.
            rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_update. ired.
            econs; eauto. rewrite bind_trigger. econs; eauto. grind.
          + eapply inj_pair2 in H5. clarify.
            hexploit IHSTEPS; clear IHSTEPS.
            { do 2 f_equal. grind. }
            auto.
            { eapply oracle_step_wf; eauto. }
            i. des. exists th0; split; auto. econs 3; eauto.
            rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_update. ired.
            econs; eauto. rewrite bind_trigger. econs; eauto. grind.

        - rewrite denote_inst_fence in STEP. irw in STEP.
          inv STEP. inv LANG. ss. eapply inj_pair2 in H3. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. }
          auto.
          { eapply oracle_step_wf; eauto. }
          i. des. exists th0; split; auto. econs 3; eauto.
          rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_fence. ired.
          econs; eauto. rewrite bind_trigger. econs; eauto.

        - rewrite denote_inst_syscall in STEP. irw in STEP.
          inv STEP. inv LANG. ss. eapply inj_pair2 in H2. clarify.
          hexploit IHSTEPS; clear IHSTEPS.
          { do 2 f_equal. grind. }
          auto.
          { eapply oracle_step_wf; eauto. }
          i. des. exists th0; split; auto. econs 3; eauto.
          rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_syscall. ired.
          econs; eauto. rewrite bind_trigger. econs; eauto. grind.

        - rewrite denote_inst_abort in STEP. irw in STEP.
          inv STEP. inv LANG. ss.

        - rewrite denote_inst_choose in STEP. irw in STEP.
          inv STEP. inv LANG. ss.

      }

    - rewrite itr_code_cons in STEP. rewrite denote_stmt_ite in STEP. irw in STEP. inv STEP. inv LANG. ss.

    - rewrite itr_code_cons in STEP. rewrite denote_stmt_while3 in STEP. irw in STEP. inv STEP. inv LANG. ss.

    }

  Qed.

  Lemma rtc_first_block_fail
        b1 b2 le sm p o th tr
        (WF: Oracle.wf o)
        (STEPS: SeqThread.steps (SeqState.na_step (lang:=lang _)) tr
                                {|
                                  SeqThread.state := (@SeqState.mk (lang _) (itr_code b1 le) sm);
                                  SeqThread.perm := p;
                                  SeqThread.oracle := o
                                |} th)
        (FAIL: SeqThread.failure (SeqState.na_step (lang:=lang _)) th)
    :
      exists th0,
        (SeqThread.steps (SeqState.na_step (lang:=lang _)) tr
                         {|
                           SeqThread.state := (@SeqState.mk (lang _) (itr_code (add_block b1 b2) le) sm);
                           SeqThread.perm := p;
                           SeqThread.oracle := o
                         |} th0) /\ (SeqThread.failure (SeqState.na_step (lang:=lang _)) th0).
  Proof.
    eapply steps_first_block_prop; eauto. clear.
    i. rename H into FAIL.
    unfold itr_code in *. rewrite denote_add_block. ired. inv FAIL. inv H.
    inv STEP. inv LOCAL.
    - inv LANG. des_ifs.
      symmetry in H. apply eq_is_bisim in H. eapply eqitree_inv_bind_vis in H. des.
      2:{ exfalso. destruct a. eapply eqitree_inv_ret_vis in H0. auto. }
      match goal with | [H: ?a ≅ ?b |- _] => replace a with b end.
      2:{ apply bisim_is_eq. symmetry. auto. }
      eexists. split. econs. ired. econs; eauto.
      econs; eauto. rewrite Heq; ss.

    - inv LANG.
      symmetry in H. apply eq_is_bisim in H. eapply eqitree_inv_bind_vis in H. des.
      2:{ exfalso. destruct a. eapply eqitree_inv_ret_vis in H0. auto. }
      match goal with | [H: ?a ≅ ?b |- _] => replace a with b end.
      2:{ apply bisim_is_eq. symmetry. auto. }
      eexists. split. econs. ired. econs; eauto.
      econs; eauto.

    - inv LANG.
      symmetry in H. apply eq_is_bisim in H. eapply eqitree_inv_bind_vis in H. des.
      2:{ exfalso. destruct a. eapply eqitree_inv_ret_vis in H0. auto. }
      match goal with | [H: ?a ≅ ?b |- _] => replace a with b end.
      2:{ apply bisim_is_eq. symmetry. auto. }
      eexists. split. econs. ired. econs; eauto.
      econs; eauto.
  Qed.

  Lemma rtc_first_block_mlep
        b1 b2 le sm p o th tr d w tf
        (WF: Oracle.wf o)
        (STEPS: SeqThread.steps (SeqState.na_step (lang:=lang _)) tr
                                {|
                                  SeqThread.state := (@SeqState.mk (lang _) (itr_code b1 le) sm);
                                  SeqThread.perm := p;
                                  SeqThread.oracle := o
                                |} th)
        (FLAG: Flags.le (Flags.join d tf) (Flags.join w (SeqMemory.flags (SeqState.memory (SeqThread.state th)))))
    :
      exists th0,
        (SeqThread.steps (SeqState.na_step (lang:=lang _)) tr
                         {|
                           SeqThread.state := (@SeqState.mk (lang _) (itr_code (add_block b1 b2) le) sm);
                           SeqThread.perm := p;
                           SeqThread.oracle := o
                         |} th0) /\
        (Flags.le (Flags.join d tf) (Flags.join w (SeqMemory.flags (SeqState.memory (SeqThread.state th0))))).
  Proof.
    eapply steps_first_block_prop; eauto.
  Qed.

End AUX.



Ltac unfold_flags := unfold Flags.update, Flags.add, Flags.sub, Flags.sub_opt, Flags.meet, Flags.join, Flags.minus in *.
Ltac unfold_many := unfold_flags; unfold ValueMap.write, ValueMap.acquire, Perms.acquired in *.



Section PARTIAL.

  Let D := Opt2.D DSE_opt2.
  Let opt := Opt2.opt_block DSE_opt2.
  Let dt := Opt2.GD DSE_opt2.
  Let bot := Opt2.bot DSE_opt2.
  Let inf := Opt2.ti DSE_opt2.
  Let init := Opt2.bot2 DSE_opt2.
  Let datai := (fun _ : Loc.t => inf).
  Let match_code := @Opt2.match_code2 DSE_opt2.
  Let data_le := @Opt2.le2 DSE_opt2.
  Let data_meet := @Opt2.meet2 DSE_opt2.
  Let update0 := @Opt2.inst_gd DSE_opt2.
  Let update1 := @Opt2.block_gd DSE_opt2.


  Inductive match_data: dt -> block -> Prop :=
  | match_data_nil
      data
    :
      match_data data nil

  | match_data_inst
      (i_src: Inst.t) b_src
      data0
      (MD0: match_data data0 b_src)
    :
      match_data (update0 i_src data0) (cons i_src b_src)

  | match_data_ite
      (s_src: stmt) b_src
      e (sb1 sb2: block)
      data0
      data1 data2

      (SSRC: s_src = ite e sb1 sb2)
      (MD0: match_data data0 b_src)

      (OPT1: data1 = update1 sb1 data0)
      (OPT2: data2 = update1 sb2 data0)

      (MD1: match_data data1 (add_block sb1 b_src))
      (MD2: match_data data2 (add_block sb2 b_src))
    :
      match_data (data_meet data1 data2) (cons s_src b_src)

  | match_data_while
      (s_src: stmt) b_src src
      e (sb: block)
      data0 data1 data2 data

      (SSRC: s_src = while e sb)

      (SRC: src = cons s_src b_src)

      (MD0: match_data data0 b_src)
      (MD1: match_data (update1 sb datai) sb)

      (DATA1: data1 = (fold_n (update1 sb) (1 + level)) data0)
      (DATA2: data2 = (fold_n (update1 sb) (1 + level)) datai)
      (DATA: data = data_meet data0 (data_meet data1 data2))
    :
      match_data data src
  .

  Lemma md_add_block
        src1 src2 data
        (MD: match_data (update1 src2 data) src2)
    :
      match_data (update1 src1 (update1 src2 data)) (add_block src1 src2).
  Proof.
    revert_until src1. induction src1 using block_ind2; i; ss.
    - rewrite (@block_gd_inst_gd DSE_opt2). econs 2. auto.
    - rewrite (@block_gd_cons_partial DSE_opt2).
      rewrite (@block_gd_ite_eval DSE_opt2). econs 3; eauto.
      + clear IHsrc1_2.
        assert (AS: update1 src1_3 (update1 src2 data) = update1 (add_block src1_3 src2) data).
        { erewrite <- (@block_gd_add_block_partial DSE_opt2); ss. }
        unfold update1. unfold update1 in AS. setoid_rewrite AS; clear AS.
        eapply IHsrc1_1.
        erewrite (@block_gd_add_block_partial DSE_opt2); ss.
        eapply IHsrc1_3. auto.
      + clear IHsrc1_1.
        assert (AS: update1 src1_3 (update1 src2 data) = update1 (add_block src1_3 src2) data).
        { erewrite <- (@block_gd_add_block_partial DSE_opt2); ss. }
        unfold update1. unfold update1 in AS. setoid_rewrite AS; clear AS.
        eapply IHsrc1_2.
        erewrite (@block_gd_add_block_partial DSE_opt2); ss.
        eapply IHsrc1_3. auto.
    - rewrite (@block_gd_cons_partial DSE_opt2).
      rewrite (@block_gd_while_eval DSE_opt2).
      econs 4; eauto. specialize IHsrc1_1 with (src2:=nil). hexploit IHsrc1_1.
      { econs 1. }
      i. rewrite add_block_nil_unit_r in H.
      instantiate (1:=datai) in H. ss.
  Qed.

  Lemma update1_md
        src data
    :
      match_data (update1 src data) src.
  Proof.
    revert1.
    induction src using block_ind2; i; ss.
    - econs 1.
    - rewrite (@block_gd_inst_gd DSE_opt2). econs 2. auto.
    - rewrite (@block_gd_cons_partial DSE_opt2).
      rewrite (@block_gd_ite_eval DSE_opt2). econs 3; eauto.
      + eapply md_add_block; eauto.
      + eapply md_add_block; eauto.
    - rewrite (@block_gd_cons_partial DSE_opt2).
      rewrite (@block_gd_while_eval DSE_opt2). econs 4; eauto.
  Qed.


  Let data_eq := @data_eq (Opt2.D DSE_opt2) eq (Opt2.P DSE_opt2).

  Program Instance data_le_PartialOrder: PartialOrder data_eq data_le.
  Next Obligation.
  Proof.
    unfold data_le, le2. unfold data_eq.
    eapply Knowledge.data_PartialOrder_obligation_1; eauto.
    eapply le_PartialOrder.
  Qed.


  Lemma meet_max
        a b
    :
      (meet a b = full) <-> (a = full /\ b = full).
  Proof.
    unfold meet. split.
    - des_ifs.
    - i. des. clarify.
  Qed.

  Lemma le_bot_bot
        a
    :
      (le a bot) <-> a = bot.
  Proof.
    unfold le. split.
    - des_ifs.
    - i. clarify.
  Qed.

  Lemma le_full_full
        a
    :
      (le full a) <-> a = full.
  Proof.
    unfold le. split.
    - des_ifs.
    - i. clarify.
  Qed.

  Lemma rel_flag_full
        d
        (REL: rel_flag d = full)
    :
      d = full.
  Proof.
    unfold rel_flag in REL. des_ifs.
  Qed.

  Lemma inv_three
        d
    :
      (d = none \/ d = half) \/ (d = full).
  Proof.
    destruct d; auto.
  Qed.

  Lemma des_nh
        d (P Q: Prop)
        (PROP: match d with | full => P | _ => Q end)
        (NH: d = none \/ d = half)
    :
      Q.
  Proof.
    des; clarify; eauto.
  Qed.


  Definition coherent (d: dt) :=
    forall l, le (d l) half.

  Lemma coherent_mem_le_partial_same
        d m
        (COH: coherent d)
    :
        Flags.le (Flags.join (to_deferred d) m.(SeqMemory.flags))
                 (m.(SeqMemory.flags)).
  Proof.
    ii. unfold coherent in COH. specialize COH with loc. unfold to_deferred. unfold_flags.
    destruct (d loc); ss. all: refl.
  Qed.

  Lemma load_gives_coherent
        loc ordr d
        (ORDR: Ordering.le ordr Ordering.strong_relaxed = false)
    :
      coherent (fun p => update_load loc ordr p (d p)).
  Proof.
    ii. hexploit (ord_inv1 ordr); i. des.
    { destruct ordr; ss. }
    rewrite update_load_ord2; auto. des_ifs.
    match goal with | [|- le (acq_flag ?a) _ ] => destruct a; ss end.
  Qed.

  Lemma update_gives_coherent
        loc ordr ordw d
        (ORDR: Ordering.le ordr Ordering.na = false)
    :
      coherent (fun p => update_read loc ordr p (update_store loc ordw p (d p))).
  Proof.
    ii. hexploit (ord_inv1' ordr); i. des.
    { destruct ordr; ss. }
    rewrite update_read_ord2; auto. des_ifs.
    match goal with | [|- le (acq_flag ?a) _ ] => destruct a; ss end.
  Qed.

  Lemma fence_gives_coherent
        ordr ordw d
        (ORD: (Ordering.le ordr Ordering.strong_relaxed = false) \/ (Ordering.le ordw Ordering.acqrel = false))
    :
      coherent (fun p => update_fence_r ordr p (update_fence_w ordw p (d p))).
  Proof.
    ii. des.
    - hexploit (ord_inv3 ordr); i. des.
      1: destruct ordr; ss.
      rewrite update_fence_r_ord2; auto.
      match goal with | [|- le (acq_flag ?a) _ ] => destruct a; ss end.
    - hexploit (ord_inv3' ordw); i. des.
      1,2: destruct ordw; ss.
      rewrite update_fence_w_ord3; auto.
      unfold update_fence_r. des_ifs.
      all: destruct (d l); ss.
  Qed.


  Lemma update_load_fle
        rhs ord d
    :
      Flags.le (to_deferred (fun p0 => update_load rhs ord p0 (d p0)))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    hexploit (ord_inv1 ord). i; des.
    - rewrite update_load_ord1f; auto. ii. unfold to_deferred. des_ifs. refl.
    - rewrite update_load_ord2f; auto. ii. unfold to_deferred. des_ifs. apply to_deferred0_mon. apply acq_flag_le.
  Qed.

  Lemma update_read_fle
        rhs ord d
    :
      Flags.le (to_deferred (fun p0 => update_read rhs ord p0 (d p0)))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    hexploit (ord_inv1' ord). i; des.
    - rewrite update_read_ord1f; auto. ii. unfold to_deferred. des_ifs. refl.
    - rewrite update_read_ord2f; auto. ii. unfold to_deferred. des_ifs. apply to_deferred0_mon. apply acq_flag_le.
  Qed.

  Lemma update_store_fle
        loc ord d
        (AT: Ordering.le ord Ordering.na = false)
    :
      Flags.le (to_deferred (fun p0 => update_store loc ord p0 (d p0)))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    hexploit (ord_inv2 ord). i; des.
    - destruct ord; ss.
    - rewrite update_store_ord2f; auto. ii. unfold to_deferred. des_ifs. refl.
    - rewrite update_store_ord3f; auto. ii. unfold to_deferred. des_ifs. apply to_deferred0_mon. apply rel_flag_le.
  Qed.

  Lemma update_fence_r_fle
        ordr d
    :
      Flags.le (to_deferred (fun p0 => update_fence_r ordr p0 (d p0)))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    hexploit (ord_inv3 ordr). i; des.
    - rewrite update_fence_r_ord1f; auto. ii. unfold to_deferred. refl.
    - rewrite update_fence_r_ord2f; auto. ii. unfold to_deferred. apply to_deferred0_mon. apply acq_flag_le.
  Qed.

  Lemma update_fence_w_fle
        ordw d
    :
      Flags.le (to_deferred (fun p0 => update_fence_w ordw p0 (d p0)))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    hexploit (ord_inv3' ordw). i; des.
    - rewrite update_fence_w_ord1f; auto. ii. unfold to_deferred. refl.
    - rewrite update_fence_w_ord2f; auto. ii. unfold to_deferred. apply to_deferred0_mon. apply rel_flag_le.
    - rewrite update_fence_w_ord3f; auto. ii. unfold to_deferred.
      apply to_deferred0_mon. etrans. apply rel_flag_le. apply acq_flag_le.
  Qed.

  Lemma update_update_fle
        loc ordr ordw d
        (AT: Ordering.le ordw Ordering.na = false)
    :
      Flags.le (to_deferred (fun p => update_read loc ordr p (update_store loc ordw p (d p))))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    etrans. eapply update_read_fle; eauto. ss. eapply update_store_fle; eauto.
  Qed.

  Lemma update_fence_fle
        ordr ordw d
    :
      Flags.le (to_deferred (fun p => update_fence_r ordr p (update_fence_w ordw p (d p))))
               (to_deferred (fun p0 => (d p0))).
  Proof.
    etrans. eapply update_fence_r_fle; eauto. ss. eapply update_fence_w_fle; eauto.
  Qed.

  Lemma flags_minus_le:
    forall f1 f2, Flags.le (Flags.minus f1 f2) f1.
  Proof.
    ii. unfold_flags. destruct (f1 loc), (f2 loc); ss.
  Qed.


  Lemma mmp_sim_partial_i_inst
        (i_src : Inst.t)
        (b_src : block)
        (data0 : dt)
        (IHMD : forall (p : Perms.t) (mem : SeqMemory.t) (tgt : block) (le : lenv),
            sim_seq_partial_case p (to_deferred (update1 b_src datai))
              (@SeqState.mk (lang _) (itr_code b_src le) mem)
              (@SeqState.mk (lang _) (itr_code tgt le) mem))
        (p : Perms.t)
        (mem : SeqMemory.t)
        (tgt : block)
        (le : lenv)
    :
      sim_seq_partial_case p (to_deferred (update1 (cons i_src b_src) datai))
        (@SeqState.mk (lang _) (itr_code (cons i_src b_src) le) mem)
        (@SeqState.mk (lang _) (itr_code tgt le) mem).
  Proof.
    ss. erewrite (@block_gd_inst_gd DSE_opt2) in *.
    unfold update1, block_gd, inst_gd, mk_global in *. ss.
    rewrite itr_code_cons. rewrite denote_stmt_inst.
    ii. dup WF. rename WF0 into ORACLE. punfold WF. 2: eapply Oracle.wf_mon. inv WF.
    destruct i_src.
    - clear WF0 LOAD STORE FENCE.
      rewrite denote_inst_skip. ired.
      ss.
      hexploit IHMD; eauto.
      intros SP. unfold sim_seq_partial_case in SP. hexploit SP; clear SP; eauto. i; des.
      + exists th, tr, w; splits; ss; auto.
        { econs 2; eauto. econs. repeat (econs; eauto). }
        { left. auto. }
      + exists th, tr, w; splits; ss; auto.
        { econs 2; eauto. econs. repeat (econs; eauto). }

    - clear WF0 LOAD STORE FENCE.
      rewrite denote_inst_assign. ired.
      ss.
      hexploit IHMD; eauto.
      intros SP. unfold sim_seq_partial_case in SP. hexploit SP; clear SP; eauto. i; des.
      + exists th, tr, w; splits; auto.
        { econs 2; eauto. econs. repeat (econs; eauto). }
        { left. auto. }
      + exists th, tr, w; splits; auto.
        { econs 2; eauto. econs. repeat (econs; eauto). }

    - clear STORE FENCE.
      rewrite denote_inst_load. ired.
      ss.
      hexploit (ord_inv1 ord); i; des.
      + destruct (Ordering.le ord Ordering.na) eqn:NA.
        * destruct (Perm.le Perm.high (p rhs)) eqn:PERM.
          { hexploit IHMD.
            intros SP. unfold sim_seq_partial_case in SP. hexploit SP; clear SP; eauto. i. des.
            { eexists th, tr, w; split; ss; auto.
              { econs 2; eauto. econs. econs. rewrite bind_trigger. econs 3. grind. econs; eauto. i. refl. }
              ss. splits; auto.
              left. red. etrans. 2: eauto. apply Flags.join_mon_l. apply update_load_fle.
            }
            { eexists th, tr, w; split; ss; auto.
              econs 2; eauto. econs. econs. rewrite bind_trigger. econs 3. grind. econs; eauto. i. refl.
            }
          }
          { hexploit IHMD.
            intros SP. unfold sim_seq_partial_case in SP. hexploit SP; clear SP; eauto. i; des.
            { exists th, tr, w; split; auto.
              { econs 2; eauto. econs. econs.
                2:{ econs 2. eauto. i. rewrite PERM in H0. discriminate H0. }
                rewrite bind_trigger. econs 3. grind.
              }
              ss. splits; auto.
              left. red. etrans. 2: eauto. apply Flags.join_mon_l. apply update_load_fle.
            }
            { exists th, tr, w; split; auto.
              econs 2; eauto. econs. econs.
              2:{ econs 2. eauto. i. rewrite PERM in H0. discriminate H0. }
              rewrite bind_trigger. econs 3. grind.
            }
          }

        * ss. hexploit LOAD; clear LOAD; eauto. i. des.
          instantiate (1:=ord) in H0. instantiate (1:=rhs) in H0.
          hexploit exists_input_no_acq.
          match goal with | [H: Oracle.progress ?a _ |- _] => instantiate (1:=a); ss end. destruct ord; ss.
          i. des. unfold Oracle.progress in H0. eapply H0 in H3; clear H0. des.
          hexploit H2; clear H2; eauto. i; des. hexploit WF0; clear WF0; eauto. i; des. clear WF. pclearbot.
          hexploit IHMD; clear IHMD.
          i. unfold sim_seq_partial_case in H2. hexploit H2; clear H2.
          { eapply ORACLE0. }
          i. des.
          { exists th. eexists (List.cons _ tr). eexists. splits; ss.
            - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
              { econs; eauto. ired. ss. }
              { ss. destruct ord; ss. }
              refl. refl.
            - econs; eauto. ss. destruct ord; ss.
            - left.
              hexploit red_rlx_full. 5,6: eauto. all: ss. 1,2: destruct ord; ss.
              i; des. destruct m1, mem; ss. subst value_map flags i; ss.
              ii. unfold to_deferred, SeqEvent.written. ss. unfold_many.
              rewrite update_load_ord1; auto.
              depgen FLAGS. clear; i. unfold Flags.le in FLAGS. specialize FLAGS with loc.
              rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; ss.
          }
          { exists th. eexists (List.cons _ tr). eexists. splits; ss.
            + rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
              { econs; eauto. ired. ss. }
              { ss. destruct ord; ss. }
              refl. refl.
            + econs; eauto. ss. destruct ord; ss.
            + right; eauto.
          }

      + esplits. econs 1. econs 1. ss. left. apply coherent_mem_le_partial_same.
        apply load_gives_coherent. destruct ord; ss.

    - clear LOAD FENCE.
      rewrite denote_inst_store. ired.
      ss.
      hexploit (ord_inv2 ord); i; des.
      + destruct (Perm.le Perm.high (p lhs)) eqn:PERM.
        { hexploit IHMD; clear IHMD.
          i. unfold sim_seq_partial_case in H0. hexploit H0; clear H0; eauto. i. des.
          * esplits; eauto.
            { econs 2. 2: eauto. econs. econs. rewrite bind_trigger; econs; eauto.
              econs; eauto. rewrite PERM. auto. }
            { left. ss. etrans. 2: eauto.
              unfold to_deferred. ii. unfold_flags. rewrite update_store_ord1; auto.
              rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. clear. des_ifs; ss.
              destruct (to_deferred0 (Opt2.block_d DSE_opt2 b_src lhs (datai lhs))); ss.
              refl.
            }

          * esplits; eauto.
            econs 2. 2: eauto. econs. econs. rewrite bind_trigger; econs; eauto.
            econs; eauto. rewrite PERM. auto.
        }

        esplits. econs 1. econs 1. right. econs. econs. econs.
        rewrite bind_trigger. econs; eauto. econs; eauto. rewrite PERM; auto.

      + hexploit STORE; clear STORE; eauto. i. des.
        instantiate (1:=ord) in H0. instantiate (1:=(denote_expr le rhs)) in H0.
        instantiate (1:=lhs) in H0.
        hexploit exists_input_no_acq.
        match goal with | [H: Oracle.progress ?a _ |- _] => instantiate (1:=a); ss end.
        i. des. unfold Oracle.progress in H0. eapply H0 in H2; clear H0. des.
        hexploit H1; clear H1; eauto. i; des. hexploit WF0; clear WF0; eauto. i; des. clear WF. pclearbot.
        hexploit IHMD; clear IHMD.
        i. unfold sim_seq_partial_case in H1. hexploit H1; clear H1.
        { eapply ORACLE0. }
        i. des.
        { hexploit red_rlx_full. 5,6: eauto. 1,2,3,4: ss. 1,2: destruct ord; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. destruct ord; ss. }
            refl. refl.
          - econs; eauto.
          - left. rewrite <- flags_join_assoc. etrans.
            2:{ eapply Flags.join_mon_r. eauto. }
            destruct m1, mem; ss. subst value_map flags i; ss.
            unfold to_deferred, SeqEvent.written. ss. unfold_flags.
            ii. rewrite update_store_ord2; auto.
            rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec.
            clear. des_ifs; ss. all: refl.
        }
        { hexploit red_rlx_full. 5,6: eauto. 1,2,3,4: ss. 1,2: destruct ord; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. destruct ord; ss. }
            refl. refl.
          - econs; eauto.
          - right; auto.
        }

      + hexploit STORE; clear STORE; eauto. i. des.
        instantiate (1:=ord) in H0. instantiate (1:=(denote_expr le rhs)) in H0.
        instantiate (1:=lhs) in H0.
        hexploit exists_input_no_acq.
        match goal with | [H: Oracle.progress ?a _ |- _] => instantiate (1:=a); ss end.
        i. des. unfold Oracle.progress in H0. eapply H0 in H2; clear H0. des.
        hexploit H1; clear H1; eauto. i; des. hexploit WF0; clear WF0; eauto. i; des. clear WF. pclearbot.
        hexploit IHMD; clear IHMD.
        i. unfold sim_seq_partial_case in H1. hexploit H1; clear H1.
        { eapply ORACLE0. }
        i. des.
        { hexploit red_rel_full. 5,6: eauto. 1,2,3,4: ss. destruct ord; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. destruct ord; ss. }
            refl. refl.
          - econs; eauto.
          - left. rewrite <- flags_join_assoc. etrans.
            2:{ eapply Flags.join_mon_r. eauto. }
            destruct m1, mem; ss. subst value_map flags i; ss.
            unfold to_deferred, SeqEvent.written. ss. unfold_flags.
            ii. rewrite update_store_ord3; auto.
            rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec.
            clear. des_ifs; ss.
            destruct (Opt2.block_d DSE_opt2 b_src loc (datai loc)), (flags0 loc); ss.
            destruct (Opt2.block_d DSE_opt2 b_src loc (datai loc)), (flags0 loc); ss.
        }
        { hexploit red_rel_full. 5,6: eauto. 1,2,3,4: ss. destruct ord; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. destruct ord; ss. }
            refl. refl.
          - econs; eauto.
          - right; auto.
        }

    - clear FENCE.
      rewrite denote_inst_update. ired.
      ss.
      hexploit (ord_inv1' ordr). i; des.
      { destruct rmw.
        - esplits. econs 1. econs 1. right. econs. econs. econs.
          2:{ econs 5. unfold __guard__. left; eauto. }
          rewrite bind_trigger. econs; eauto. econs; eauto.
        - destruct (Const.eqb old (SeqMemory.read loc mem)) eqn:CASE.
          + destruct b.
            * esplits. econs 1. econs 1. right. econs. econs. econs.
              2:{ econs 5. unfold __guard__. left; eauto. }
              rewrite bind_trigger. econs; eauto. econs 2; eauto. rewrite CASE. ss.
            * esplits. econs 1. econs 1. right. econs. econs. econs.
              2:{ econs 5. unfold __guard__. left; eauto. }
              rewrite bind_trigger. econs; eauto. econs 2; eauto.
              instantiate (1:=old). destruct old; ss. des_ifs.
              rewrite PeanoNat.Nat.eqb_refl. ss.
          + esplits. econs 1. econs 1. right. econs. econs. econs.
            2:{ econs 5. unfold __guard__. left; eauto. }
            rewrite bind_trigger. econs; eauto. econs 2; eauto. rewrite CASE. ss.
      }
      { esplits. econs 1. econs 1. ss. left. apply coherent_mem_le_partial_same.
        apply update_gives_coherent. destruct ordr; ss.
      }

    - clear LOAD STORE.
      rewrite denote_inst_fence. ired.
      hexploit (ord_inv3 ordr); i; des.
      2:{ esplits. econs 1. econs 1. ss. left. apply coherent_mem_le_partial_same.
        apply fence_gives_coherent. left. destruct ordr; ss.
      }

      hexploit (ord_inv3' ordw); i; des.
      3:{ esplits. econs 1. econs 1. ss. left. apply coherent_mem_le_partial_same.
        apply fence_gives_coherent. right. destruct ordw; ss.
      }
      + hexploit FENCE; clear FENCE; eauto. i.
        instantiate (1:=ordw) in H1. instantiate (1:=ordr) in H1.
        hexploit exists_input_no_acq.
        match goal with | [H: Oracle.progress ?a _ |- _] => instantiate (1:=a); ss end.
        { destruct ordr, ordw; ss. }
        i. des. unfold Oracle.progress in H1. eapply H1 in H3; clear H1. des.
        hexploit H2; clear H2; eauto. i; des. hexploit WF0; clear WF0; eauto. i; des. clear WF. pclearbot.
        hexploit IHMD; clear IHMD.
        i. unfold sim_seq_partial_case in H2. hexploit H2; clear H2.
        { eapply ORACLE0. }
        i. des.
        { hexploit red_rlx2_full. 5,6: eauto. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. }
            refl. refl.
          - econs; eauto. ss. destruct ordr, ordw; ss.
          - left. rewrite <- flags_join_assoc. etrans.
            2:{ eapply Flags.join_mon_r. eauto. }
            subst m1 i; ss.
            unfold to_deferred, SeqEvent.written. ss. unfold_flags.
            ii. rewrite update_fence_r_ord1; auto. rewrite update_fence_w_ord1; auto.
            rewrite flag_join_idem. rewrite flag_join_bot_l. refl.
        }
        { hexploit red_rlx2_full. 5,6: eauto. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. }
            refl. refl.
          - econs; eauto. ss. destruct ordr, ordw; ss.
          - right; auto.
        }
      + hexploit FENCE; clear FENCE; eauto. i.
        instantiate (1:=ordw) in H1. instantiate (1:=ordr) in H1.
        hexploit exists_input_no_acq.
        match goal with | [H: Oracle.progress ?a _ |- _] => instantiate (1:=a); ss end.
        { destruct ordr, ordw; ss. }
        i. des. unfold Oracle.progress in H1. eapply H1 in H3; clear H1. des.
        hexploit H2; clear H2; eauto. i; des. hexploit WF0; clear WF0; eauto. i; des. clear WF. pclearbot.
        hexploit IHMD; clear IHMD.
        i. unfold sim_seq_partial_case in H2. hexploit H2; clear H2.
        { eapply ORACLE0. }
        i. des.
        { hexploit red_rel2_full. 5,6: eauto. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. }
            refl. refl.
          - econs; eauto. ss. destruct ordr, ordw; ss.
          - left. rewrite <- flags_join_assoc. etrans.
            2:{ eapply Flags.join_mon_r. eauto. }
            destruct m1, mem; ss. subst value_map flags i; ss.
            unfold to_deferred, SeqEvent.written. ss. unfold_flags.
            ii. rewrite update_fence_r_ord1; auto. rewrite update_fence_w_ord2; auto.
            rewrite flag_join_bot_l. rewrite flag_join_bot_r. rewrite flag_join_comm.
            apply Flag.join_mon_r. apply to_deferred0_mon. apply rel_flag_le.
        }
        { hexploit red_rel2_full. 5,6: eauto. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss.
          i; des.
          exists th. eexists (List.cons _ tr). eexists. splits; ss.
          - rewrite bind_trigger. econs 3. 2: eapply STEPS. econs; eauto.
            { econs; eauto. }
            { ss. }
            refl. refl.
          - econs; eauto. ss. destruct ordr, ordw; ss.
          - right; auto.
        }

    - rewrite denote_inst_syscall. ired. ss.
      esplits. econs 1. econs 1. ss. left. apply coherent_mem_le_partial_same. ss.

    - rewrite denote_inst_abort. ired.
      esplits. econs 1. econs 1. ss. right. apply seq_thread_failure.

    - clear WF0 LOAD STORE FENCE.
      rewrite denote_inst_choose. ired.
      ss.
      hexploit IHMD; eauto.
      intros SP. unfold sim_seq_partial_case in SP. hexploit SP; clear SP; eauto. i; des.
      + exists th, tr, w; splits; auto.
        { econs 2; eauto. econs. rewrite bind_trigger. repeat (econs; eauto). grind. }
        { left. auto. }
      + exists th, tr, w; splits; auto.
        { econs 2; eauto. econs. rewrite bind_trigger. repeat (econs; eauto). grind. }

        Unshelve. all: ss. all: exact 0.
  Qed.


  Lemma update_ite_fle_l:
    forall data e sb1 sb2 b_src,
      Flags.le (to_deferred (update1 (cons (ite e sb1 sb2) b_src) data)) (to_deferred (update1 (add_block sb1 b_src) data)).
  Proof.
    i. rewrite (@block_gd_cons_partial DSE_opt2). rewrite (@block_gd_ite_eval DSE_opt2).
    erewrite (@block_gd_add_block_partial DSE_opt2); eauto. apply to_deferred_mon.
    ii. unfold meet2. ss. apply (MLattice.meet_is_min_l).
  Qed.

  Lemma update_ite_fle_r:
    forall data e sb1 sb2 b_src,
      Flags.le (to_deferred (update1 (cons (ite e sb1 sb2) b_src) data)) (to_deferred (update1 (add_block sb2 b_src) data)).
  Proof.
    i. rewrite (@block_gd_cons_partial DSE_opt2). rewrite (@block_gd_ite_eval DSE_opt2).
    erewrite (@block_gd_add_block_partial DSE_opt2); eauto. apply to_deferred_mon.
    ii. unfold meet2. ss. apply (MLattice.meet_is_min_r).
  Qed.

  Lemma update_while_fle_1:
    forall data e sb b_src,
      Flags.le (to_deferred (update1 (cons (while e sb) b_src) data)) (to_deferred (update1 b_src data)).
  Proof.
    i. rewrite (@block_gd_cons_partial DSE_opt2). rewrite (@block_gd_while_eval DSE_opt2).
    apply to_deferred_mon.
    ii. unfold meet2. ss. apply (MLattice.meet_is_min_l).
  Qed.

  Lemma update_while_fle_2:
    forall e sb b_src,
      Flags.le (to_deferred (update1 (cons (while e sb) b_src) datai)) (to_deferred (update1 sb datai)).
  Proof.
    i. rewrite (@block_gd_cons_partial DSE_opt2). rewrite (@block_gd_while_eval DSE_opt2).
    apply to_deferred_mon.
    ii. unfold meet2. ss.
    etrans. apply (MLattice.meet_is_min_r).
    etrans. apply (MLattice.meet_is_min_r).
    hexploit (block_gd_le_n (block_d_dec) 2 sb datai). i; ss.
  Qed.


  Lemma mmp_sim_partial_i0:
    forall src p mem tgt le
    ,
      sim_seq_partial_case
        p (to_deferred (update1 src datai))
        (@SeqState.mk (lang _) (itr_code src le) mem)
        (@SeqState.mk (lang _) (itr_code tgt le) mem).
  Proof.
    i. revert_until src. hexploit (update1_md src). intros MD.
    induction MD; i; ss.
    { ii. esplits. econs 1. econs 1. left. ss. refl. }
    { eapply mmp_sim_partial_i_inst; eauto. }

    - subst s_src. unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_ite2. grind.
      + clear IHMD2.
        replace (
            ` r : lenv * () <- denote_block le (cons Inst.skip sb2);;
                  ` x : lunit <- (let (le1, _) := r in denote_block le1 b_src);;
                        (let (le1, _) := x in Ret (le1 ret_reg))
          )
          with
            (
              ` x_ : lenv * () <- denote_block le (cons Inst.skip sb2);;
                     (let (l1, _) := x_ in
                      ` x_0 : lenv * () <- denote_block l1 b_src;;
                              (let (l1, _) := x_0 in Ret (l1 ret_reg)))
            ).
        2:{ grind. }
        rewrite <- itr_code_add_block.
        clear IHMD1.
        hexploit IHMD3; clear IHMD3.
        i. unfold sim_seq_partial_case in H. hexploit H; clear H; eauto. i; des.
        { exists th, tr, w. split; auto.
          { rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
            econs 2.
            { econs 1. repeat (econs; eauto). }
            eauto.
          }
          splits; ss.
          left. red. etrans; eauto. apply Flags.join_mon_l. apply update_ite_fle_r.
        }
        { exists th, tr, w. split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
          econs 2.
          { econs 1. repeat (econs; eauto). }
          eauto.
        }

      + clear IHMD3.
        replace (
            ` r : lenv * () <- denote_block le (cons Inst.skip sb1);;
                  ` x : lunit <- (let (le1, _) := r in denote_block le1 b_src);;
                        (let (le1, _) := x in Ret (le1 ret_reg))
          )
          with
            (
              ` x_ : lenv * () <- denote_block le (cons Inst.skip sb1);;
                     (let (l1, _) := x_ in
                      ` x_0 : lenv * () <- denote_block l1 b_src;;
                              (let (l1, _) := x_0 in Ret (l1 ret_reg)))
            ).
        2:{ grind. }
        rewrite <- itr_code_add_block.
        clear IHMD1.
        hexploit IHMD2; clear IHMD2.
        i. unfold sim_seq_partial_case in H. hexploit H; clear H; eauto. i; des.
        { exists th, tr, w. split; auto.
          { rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
            econs 2.
            { econs 1. repeat (econs; eauto). }
            eauto.
          }
          split; ss.
          left. red. etrans; eauto. apply Flags.join_mon_l. apply update_ite_fle_l.
        }
        { exists th, tr, w. split; auto.
          rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
          econs 2.
          { econs 1. repeat (econs; eauto). }
          eauto.
        }

      + esplits.
        { econs 2. 2: econs 1. econs. econs. econs. eauto. econs. }
        { econs. }
        ss. right. apply seq_thread_failure.

    - subst s_src src.
      unfold itr_code. rewrite ! denote_block_cons. rewrite ! denote_stmt_while2. grind.
      + clear IHMD2. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. ired.
        rewrite denote_block_nil. ired.
        hexploit IHMD1; eauto.
        i. unfold sim_seq_partial_case in H. hexploit H; clear H; eauto. i; des.
        { exists th, tr, w. split; eauto.
          { econs 2; eauto. econs 1. repeat (econs; eauto). }
          split; ss.
          left. red. etrans; eauto. apply Flags.join_mon_l. apply update_while_fle_1.
        }
        { exists th, tr, w. split; eauto.
          econs 2; eauto. econs 1. repeat (econs; eauto).
        }

      + replace (
            ` r : lenv * () <-
                  denote_block le (cons Inst.skip (add_block sb (cons Inst.skip (cons (while e sb) nil))));;
                  ` x : lunit <- (let (le1, _) := r in denote_block le1 b_src);;
                        (let (le1, _) := x in Ret (le1 ret_reg))
          )
          with
            (
              ` x_ : lenv * () <- denote_block le (cons Inst.skip (add_block sb (cons Inst.skip (cons (while e sb) nil))));;
                     (let (l1, _) := x_ in
                      ` x_0 : lenv * () <- denote_block l1 b_src;;
                              (let (l1, _) := x_0 in Ret (l1 ret_reg)))
            ).
        2:{ grind. }
        rewrite <- itr_code_add_block.
        clear IHMD1.
        hexploit IHMD2; eauto.
        i. unfold sim_seq_partial_case in H. hexploit H; clear H; eauto. i; des.
        { rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. ired.
          hexploit rtc_first_block_mlep. eauto. eapply STEPS. eauto. i.
          rewrite add_block_assoc.
          des. exists th0, tr, w. split; eauto.
          { econs 2; eauto. econs 1. repeat (econs; eauto). }
          split; ss.
          left. red. etrans; eauto. apply Flags.join_mon_l. apply update_while_fle_2.
        }
        { rewrite cons_add_block_comm. rewrite itr_code_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. ired.
          hexploit rtc_first_block_fail. eauto. eapply STEPS. eauto. i.
          rewrite add_block_assoc.
          des. exists th0, tr, w. split; eauto.
          econs 2; eauto. econs 1. repeat (econs; eauto).
        }

      + esplits.
        { econs 2. 2: econs 1. econs. econs. econs. eauto. econs. }
        { econs. }
        ss. right. apply seq_thread_failure.

        Unshelve. all: ss.
  Qed.


  Lemma mm_fle:
    forall data sm tm (MM: match_mem data sm tm),
      Flags.le (Flags.join (to_deferred data) (SeqMemory.flags tm))
               (Flags.join (to_deferred data) (SeqMemory.flags sm)).
  Proof.
    ii. unfold match_mem in MM. specialize MM with loc. unfold to_deferred. unfold_flags.
    destruct (data loc); ss.
    - des. rewrite MM0. refl.
    - destruct (SeqMemory.flags tm loc), (SeqMemory.flags sm loc); ss.
      hexploit MM; auto; i; des; clarify.
  Qed.

  Lemma sim_partial_fle:
    forall data p sm tm src tgt le
      (FLE: Flags.le (Flags.join data (SeqMemory.flags tm))
                     (Flags.join data (SeqMemory.flags sm)))
      (SIM: sim_seq_partial_case
              p data
              (@SeqState.mk (lang _) (itr_code src le) sm)
              (@SeqState.mk (lang _) (itr_code tgt le) sm))
    ,
      sim_seq_partial_case p data
        (@SeqState.mk (lang _) (itr_code src le) sm)
        (@SeqState.mk (lang _) (itr_code tgt le) tm).
  Proof.
    i. unfold sim_seq_partial_case in *. i. hexploit SIM; clear SIM; eauto. i; des; ss.
    - esplits; eauto. left. etrans; eauto.
    - esplits; eauto.
  Qed.

  Lemma mm_sim_partial:
    forall data p sm tm src tgt le
      (MM: match_mem data sm tm)
      (DATA: data = update1 src init)
    ,
      sim_seq_partial_case
        p (to_deferred data)
        (@SeqState.mk (lang _) (itr_code src le) sm)
        (@SeqState.mk (lang _) (itr_code tgt le) tm).
  Proof.
    i; clarify. eapply sim_partial_fle. apply mm_fle; auto.
    eapply sim_seq_partial_case_mon.
    2:{ eapply mmp_sim_partial_i0. }
    eapply to_deferred_mon. apply (@block_gd_mon DSE_opt2). ss.
  Qed.

End PARTIAL.





Section PROOF.

  Let O2 := DSE_opt2.
  Let inst_gd := @inst_gd O2.
  Let match_code := @match_code2 O2.

  Definition sim_val: Const.t -> Const.t -> Prop := eq.
  Lemma sim_val_refl: forall a, sim_val a a.
  Proof. refl. Qed.
  Let term := term sim_val.

  Lemma sim_seq_inst_opt:
    forall r g p
      le src_m tgt_m mp b_src b_tgt
      (i: Inst.t) src tgt
      (MM: match_mem (inst_gd i mp) src_m tgt_m)
      (MC: match_code (inst_gd i mp) (cons i b_src) (cons (Opt2.opt_inst O2 mp i) b_tgt))
      (MC0: match_code mp b_src b_tgt)
      (OPT: Opt2.do_opt O2 mp i)
      (SRC: src = @SeqState.mk (lang _)
                               (` r0 : lenv * () <- denote_stmt le i;;
                                       ` x : lunit <- (let (le1, _) := r0 in denote_block le1 b_src);;
                                             (let (le2, _) := x in Ret (le2 ret_reg)))
                               src_m)
      (TGT: tgt = @SeqState.mk (lang _)
                               (` r0 : lenv * () <- denote_stmt le (Opt2.opt_inst O2 mp i);;
                                       ` x : lunit <- (let (le1, _) := r0 in denote_block le1 b_tgt);;
                                             (let (le2, _) := x in Ret (le2 ret_reg)))
                               tgt_m)
      (SIM: forall up le1 sm tm,
          (<<MM1: match_mem mp sm tm>>) ->
          gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term up (to_deferred mp)
                  (@SeqState.mk (lang _) (` x : lunit <- denote_block le1 b_src;; (let (le2, _) := x in Ret (le2 ret_reg))) sm)
                  (@SeqState.mk (lang _) (` x : lunit <- denote_block le1 b_tgt;; (let (le2, _) := x in Ret (le2 ret_reg))) tm))
    ,
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p (to_deferred (inst_gd i mp)) src tgt.
  Proof.
    i. clarify; ss. destruct i; ss.
    des_ifs; ss.
    - destruct (Perm.le Perm.high (p lhs)) eqn:PERM.
      + eapply sim_seq_na.
        { replace (
              ` r0 : lenv * () <- denote_stmt le (Inst.store lhs rhs Ordering.na);;
                     ` x : lunit <- (let (le1, _) := r0 in denote_block le1 b_src);; (let (le2, _) := x in Ret (le2 ret_reg)))
            with
              (itr_code (cons (Inst.store lhs rhs Ordering.na) b_src) le).
          2:{ rewrite itr_code_cons. unfold itr_code. grind. }
          eapply mm_sim_partial; eauto.
          eapply match_code2_opt_inv in MC0. hexploit (@Opt2.opt_block_fst O2). i.
          rewrite MC0 in H. ss.
          rewrite (@block_gd_inst_gd O2). unfold Opt2.inst_gd. ss. rewrite H in MM. rewrite H. ss.
        }
        all: rewrite ! denote_stmt_inst; try rewrite denote_inst_store; try rewrite denote_inst_skip; ired.
        { do 2 eexists. split.
          - econs. econs; eauto. econs; eauto.
          - ss.
        }
        econs. inv STEP_TGT. inv LANG. inv LOCAL.
        esplits.
        { refl. }
        { econs 1. econs. rewrite bind_trigger. econs; eauto. econs; eauto. rewrite PERM. ss. }
        guclo deferred_le_sf_ctx_spec.
        econs. 2: eapply SIM.
        { ss. ii. unfold inst_gd, Opt2.inst_gd, mk_global. ss.
          unfold to_deferred. unfold_flags. rewrite update_store_ord1; auto.
          rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. clear. des_ifs; ss.
          destruct (to_deferred0 (mp lhs)); ss.
          apply Flag.join_ge_l.
        }
        red. unfold match_mem in *. i. specialize MM with l.
        unfold inst_gd, Opt2.inst_gd, mk_global in *; ss. rewrite update_store_ord1 in *; auto.
        unfold_many. rewrite Loc.eqb_sym in MM. rewrite loc_eqb_is_dec in MM.
        clear PERM SIM. des_ifs; ss. rewrite Heq. ss.

      + rewrite denote_stmt_inst. rewrite denote_inst_store. ired.
        gstep. econs 2. econs. esplits. econs 1. econs 1.
        econs. econs. econs.
        2:{ econs 3; eauto. instantiate (1:= Ordering.na). ss. rewrite PERM. ss. }
        rewrite bind_trigger. econs. ss.

    - destruct (Perm.le Perm.high (p lhs)) eqn:PERM.
      + eapply sim_seq_na.
        { replace (
              ` r0 : lenv * () <- denote_stmt le (Inst.store lhs rhs Ordering.na);;
                     ` x : lunit <- (let (le1, _) := r0 in denote_block le1 b_src);; (let (le2, _) := x in Ret (le2 ret_reg)))
            with
              (itr_code (cons (Inst.store lhs rhs Ordering.na) b_src) le).
          2:{ rewrite itr_code_cons. unfold itr_code. grind. }
          eapply mm_sim_partial; eauto.
          eapply match_code2_opt_inv in MC0. hexploit (@opt_block_fst O2). i.
          rewrite MC0 in H. ss.
          rewrite (@block_gd_inst_gd O2). rewrite H in MM. ss. rewrite H. ss.
        }
        all: rewrite ! denote_stmt_inst; try rewrite denote_inst_store; try rewrite denote_inst_skip; ired.
        { do 2 eexists. split.
          - econs. econs; eauto. econs; eauto.
          - ss.
        }
        econs. inv STEP_TGT. inv LANG. inv LOCAL.
        esplits.
        { refl. }
        { econs 1. econs. rewrite bind_trigger. econs; eauto. econs; eauto. rewrite PERM. ss. }
        guclo deferred_le_sf_ctx_spec.
        econs. 2: eapply SIM.
        { ss. ii. unfold inst_gd, Opt2.inst_gd, mk_global. ss.
          unfold to_deferred. unfold_flags. rewrite update_store_ord1; auto.
          rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. clear. des_ifs; ss.
          destruct (to_deferred0 (mp lhs)); ss.
          apply Flag.join_ge_l.
        }
        red. unfold match_mem in *. i. specialize MM with l.
        unfold inst_gd, Opt2.inst_gd, mk_global in *; ss. rewrite update_store_ord1 in *; auto.
        unfold_many. rewrite Loc.eqb_sym in MM. rewrite loc_eqb_is_dec in MM.
        clear PERM SIM. des_ifs; ss. rewrite Heq. ss.

      + rewrite denote_stmt_inst. rewrite denote_inst_store. ired.
        gstep. econs 2. econs. esplits. econs 1. econs 1.
        econs. econs. econs.
        2:{ econs 3; eauto. instantiate (1:= Ordering.na). ss. rewrite PERM. ss. }
        rewrite bind_trigger. econs. ss.

        Unshelve. all: ss.
  Qed.


  Theorem match_state_sim
          p mp src tgt
          (MS: match_state match_mem mp src tgt)
    :
      sim_seq term p (to_deferred mp) src tgt.
  Proof.
    eapply match_state_sim.
    apply to_deferred_bot. apply to_deferred_mon.
    apply to_deferred_na_sound.
    apply mm_bot. apply mm_mon.
    apply mm_sim_partial. apply mm_na. apply mm_load_same. apply mm_read_same.
    apply mm_at. apply sim_val_refl. apply block_d_dec. apply block_d_fix.
    apply sim_seq_inst_opt. auto.
  Qed.

  Theorem DSE_match_state
          src tgt
          src_c tgt_c
          m
          (ALG: tgt_c = DSE_opt_alg src_c)
          (SRC: src = SeqState.mk (lang _) (eval_lang src_c) m)
          (TGT: tgt = SeqState.mk (lang _) (eval_lang tgt_c) m)
    :
      match_state match_mem (block_gd src_c (bot2 DSE_opt2)) src tgt.
  Proof.
    econs; ss; eauto.
    - eapply opt_match_code2; eauto.
    - apply mm_refl.
  Qed.



  Theorem DSE_sim
    src tgt
    src_c tgt_c
    (ALG: tgt_c = DSE_opt_alg src_c)
    (SRC: src = eval_lang src_c)
    (TGT: tgt = eval_lang tgt_c)
  :
    sim_seq_itree sim_val src tgt.
  Proof.
    clarify. unfold sim_seq_itree. ii. ginit. eapply sim_seq_upto_deferred.
    2:{ gfinal. right. eapply match_state_sim. eapply DSE_match_state; eauto. }
    ss.
  Qed.

End PROOF.
