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
Require Import SeqAux.

Require Import FoldN.
Require Import Knowledge.
Require Import Opt2.

Require Import ITreeLangProof.
Require Import ITreeLang.





Section SIM.

  Variable O2: Opt2.t.

  Let bot := Opt2.bot O2.
  Let init := Opt2.bot2 O2.
  Let match_code := match_code2 O2.
  Let data_meet := @meet2 O2.
  Let data_le := @le2 O2.
  Let inst_gd := @inst_gd O2.
  Let GD := GD O2.

  Variable to_deferred: GD -> Flags.t.
  Hypothesis to_deferred_bot: to_deferred (Opt2.bot2 O2) = Flags.bot.
  Hypothesis to_deferred_mon: forall mp0 mp1 (LE: data_le mp0 mp1), Flags.le (to_deferred mp0) (to_deferred mp1).

  Hypothesis to_deferred_na_sound:
    forall (i: Inst.t) mp src_m val
      (NA: is_na_inst i)
    ,
      Flags.le (to_deferred (inst_gd i mp))
               (Flags.join (to_deferred mp) (update_mem_na val i src_m).(SeqMemory.flags)).


  Variable match_mem : GD -> SeqMemory.t -> SeqMemory.t -> Prop.

  Hypothesis mm_bot: forall sm tm (MM: match_mem init sm tm), sm = tm.

  Hypothesis mm_mon:
    forall sm tm mp0 mp1
      (LE: data_le mp0 mp1)
      (MM: match_mem mp0 sm tm)
    ,
      match_mem mp1 sm tm.

  Hypothesis mm_sim_partial:
    forall data p sm tm src tgt le
      (MM: match_mem data sm tm)
      (DATA: data = @block_gd O2 src init)
    ,
      sim_seq_partial_case
        p (to_deferred data)
        (@SeqState.mk (lang _) (itr_code src le) sm)
        (@SeqState.mk (lang _) (itr_code tgt le) tm).


  Hypothesis mm_na:
    forall (i: Inst.t) data sm tm
      (MM: match_mem (inst_gd i data) sm tm)
      (NA: is_na_inst i)
      val usm utm
      (USM: usm = update_mem_na val i sm)
      (UTM: utm = update_mem_na val i tm)
    ,
      match_mem data usm utm.


  Hypothesis mm_load_same:
    forall lhs rhs ord mp src_m tgt_m
      (MM: match_mem (inst_gd (Inst.load lhs rhs ord) mp) src_m tgt_m)
    ,
      SeqMemory.read rhs src_m = SeqMemory.read rhs tgt_m.

  Hypothesis mm_read_same:
    forall lhs loc rmw ordr ordw mp src_m tgt_m
      (MM: match_mem (inst_gd (Inst.update lhs loc rmw ordr ordw) mp) src_m tgt_m)
    ,
      SeqMemory.read loc src_m = SeqMemory.read loc tgt_m.


  Hypothesis mm_at:
    forall mp p src_m tgt_m inst
      (MM: match_mem (inst_gd inst mp) src_m tgt_m)
      ev
      (EVENT: match_inst_pe inst ev)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd inst mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.


  Lemma mm_load_at:
    forall mp p src_m tgt_m lhs rhs ord
      (MM : match_mem (inst_gd (Inst.load lhs rhs ord) mp) src_m tgt_m)
      val ev
      (EVENT: ev = ProgramEvent.read rhs val ord)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd (Inst.load lhs rhs ord) mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.
  Proof. i. clarify. eapply mm_at; eauto. econs. Qed.

  Lemma mm_store_at:
    forall mp p src_m tgt_m lhs rhs ord
      (MM: match_mem (inst_gd (Inst.store lhs rhs ord) mp) src_m tgt_m)
      val ev
      (EVENT: ev = ProgramEvent.write lhs val ord)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd (Inst.store lhs rhs ord) mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.
  Proof. i. clarify. eapply mm_at; eauto. econs. Qed.

  Lemma mm_update_failure_at:
    forall lhs loc rmw ordr ordw mp p src_m tgt_m
      (MM: match_mem (inst_gd (Inst.update lhs loc rmw ordr ordw) mp) src_m tgt_m)
      val ev
      (EVENT: ev = ProgramEvent.read loc val ordr)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd (Inst.update lhs loc rmw ordr ordw) mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.
  Proof. i. clarify. eapply mm_at; eauto. econs. Qed.

  Lemma mm_update_success_at:
    forall lhs loc rmw ordr ordw mp p src_m tgt_m
      (MM: match_mem (inst_gd (Inst.update lhs loc rmw ordr ordw) mp) src_m tgt_m)
      valr valw ev
      (EVENT: ev = ProgramEvent.update loc valr valw ordr ordw)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd (Inst.update lhs loc rmw ordr ordw) mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.
  Proof. i. clarify. eapply mm_at; eauto. econs. Qed.

  Lemma mm_fence:
    forall ordr ordw mp p src_m tgt_m
      (MM: match_mem (inst_gd (Inst.fence ordr ordw) mp) src_m tgt_m)
      ev
      (EVENT: ev = ProgramEvent.fence ordr ordw)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd (Inst.fence ordr ordw) mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.
  Proof. i. clarify. eapply mm_at; eauto. econs. Qed.

  Lemma mm_syscall:
    forall lhs rhses mp p src_m tgt_m
      (MM: match_mem (inst_gd (Inst.syscall lhs rhses) mp) src_m tgt_m)
      ev sev
      (EVENT: ev = ProgramEvent.syscall sev)
      (ATOMIC: is_atomic_event ev)
      i_tgt o p1 mem_tgt
      (INPUT: SeqEvent.wf_input ev i_tgt)
      (OUTPUT: Oracle.wf_output ev o)
      (STEP_TGT: SeqEvent.step i_tgt o p tgt_m p1 mem_tgt)
    ,
    exists (i_src : SeqEvent.input) (mem_src : SeqMemory.t),
      SeqEvent.step i_src o p src_m p1 mem_src /\
      SeqEvent.input_match (to_deferred (inst_gd (Inst.syscall lhs rhses) mp)) (to_deferred mp) i_src i_tgt /\
      SeqEvent.wf_input ev i_src /\
      match_mem mp mem_src mem_tgt.
  Proof. i. clarify. eapply mm_at; eauto. econs. Qed.



  Definition build_state (c: block) (le: lenv) (m: SeqMemory.t) :=
    SeqState.mk (lang _) (itr_code c le) m.

  Variant match_state mp (src tgt: (SeqState.t (lang _))) :=
  | match_state_intro
      le src_m tgt_m src_c tgt_c
      (MC: match_code mp src_c tgt_c)
      (MM: match_mem mp src_m tgt_m)
      (SRC: src = build_state src_c le src_m)
      (TGT: tgt = build_state tgt_c le tgt_m)
    :
      match_state mp src tgt
  .


  Lemma prod_fst:
    forall A B (a: A) (b: B) (c: A * B), c = (a, b) -> fst c = a.
  Proof. i. rewrite H. ss. Qed.



  Variable sim_val: Const.t -> Const.t -> Prop.
  Hypothesis sim_val_refl: forall a, sim_val a a.
  Let term := term sim_val.

  Lemma sim_seq_inst
        r g p
        le src_m tgt_m mp b_src b_tgt
        (i: Inst.t) src tgt
        (MM: match_mem (inst_gd i mp) src_m tgt_m)
        (MC: match_code (inst_gd i mp) (cons i b_src) (cons i b_tgt))
        (NOOPT: ~ Opt2.do_opt O2 mp i)
        (SRC: src = @SeqState.mk (lang _)
                                 (r0 <- denote_stmt le i;;
                                  x <- (let (le1, _) := r0 in denote_block le1 b_src);;
                                  (let (le2, _) := x in Ret (le2 ret_reg)))
                                 src_m)
        (TGT: tgt = @SeqState.mk (lang _)
                                 (r0 <- denote_stmt le i;;
                                  x <- (let (le1, _) := r0 in denote_block le1 b_tgt);;
                                  (let (le2, _) := x in Ret (le2 ret_reg)))
                                 tgt_m)
        (SIM: forall up le1 sm tm,
            (<<MM1: match_mem mp sm tm>>) ->
            gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term up (to_deferred mp)
                    (@SeqState.mk (lang _) (x <- denote_block le1 b_src;; (let (le2, _) := x in Ret (le2 ret_reg))) sm)
                    (@SeqState.mk (lang _) (x <- denote_block le1 b_tgt;; (let (le2, _) := x in Ret (le2 ret_reg))) tm))
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p (to_deferred (inst_gd i mp)) src tgt.
  Proof.
    clarify.
    dup MC. rename MC0 into UPDATE. eapply match_code2_opt_inv in UPDATE.
    apply prod_fst in UPDATE. rewrite opt_block_fst in UPDATE.
    destruct i; clarify.
    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. grind.
      eapply sim_seq_tau; eauto.
      { match goal with
        | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
          assert (TEMP: a = itr_code (cons Inst.skip b_src) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind. }
        rewrite TEMP; clear TEMP.
        match goal with
        | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
          assert (TEMP: a = itr_code (cons Inst.skip b_tgt) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind. }
        rewrite TEMP; clear TEMP.
        eapply mm_sim_partial; eauto.
      }
      guclo deferred_le_sf_ctx_spec. econs; ss.
      { hexploit (to_deferred_na_sound Inst.skip); eauto. ss. }
      eapply SIM. eapply mm_na; eauto. ss.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_assign. grind.
      eapply sim_seq_tau; eauto.
      { match goal with
        | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
          assert (TEMP: a = itr_code (cons (Inst.assign lhs rhs) b_src) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_assign. grind. }
        rewrite TEMP; clear TEMP.
        match goal with
        | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
          assert (TEMP: a = itr_code (cons (Inst.assign lhs rhs) b_tgt) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_assign. grind. }
        rewrite TEMP; clear TEMP.
        eapply mm_sim_partial; eauto.
      }
      guclo deferred_le_sf_ctx_spec. econs; ss.
      { eapply (to_deferred_na_sound (Inst.assign _ _)); eauto. ss. }
      eapply SIM. eapply mm_na; eauto. ss.

    - destruct (Ordering.le Ordering.plain ord) eqn:ORD.
      + eapply sim_seq_atomic; eauto.
        { match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons (Inst.load lhs rhs ord) b_src) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons (Inst.load lhs rhs ord) b_tgt) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          eapply mm_sim_partial; eauto.
        }
        all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_load; grind.
        { inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        }
        { do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_read; eauto. ss. }
        ss.
        irw in STEP_TGT. inv STEP_TGT. ss; clarify.
        do 3 eexists. splits; ss.
        { refl. }
        { ss. rewrite bind_trigger. eapply ILang.step_read. eauto. }
        eapply inj_pair2 in H0. clarify. grind.
        hexploit mm_load_at; eauto. i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.

      + eapply sim_seq_na; eauto.
        { match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons (Inst.load lhs rhs ord) b_src) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons (Inst.load lhs rhs ord) b_tgt) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          eapply mm_sim_partial; eauto.
        }
        all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_load; grind.
        { do 2 eexists. esplits.
          - econs; eauto. rewrite bind_trigger. eapply ILang.step_read; eauto.
            eapply SeqState.na_local_step_read; eauto. destruct ord; ss. i; refl.
          - ss.
        }
        inv STEP_TGT. ss; clarify.
        rewrite bind_trigger in LANG. inv LANG. inv LOCAL.
        eapply inj_pair2 in H3. subst k.
        destruct (p rhs) eqn:PERM.
        { do 2 eexists. splits; ss.
          { refl. }
          { econs 1; eauto. econs; ss; eauto.
            - rewrite bind_trigger. eapply ILang.step_read; eauto.
            - econs. eauto. i. rewrite PERM in H. simpl in H. inv H.
          }
          instantiate (1:=val). ired.
          guclo deferred_le_sf_ctx_spec. econs; ss.
          { eapply (to_deferred_na_sound (Inst.load lhs rhs ord)); eauto. }
          eapply SIM. eapply mm_na; eauto.
        }
        { do 2 eexists. splits; ss.
          { refl. }
          { econs 1; eauto. econs; ss; eauto.
            - rewrite bind_trigger. eapply ILang.step_read; eauto.
            - econs; eauto. i.
              assert (READ: SeqMemory.read rhs src_m = SeqMemory.read rhs m1).
              { eapply mm_load_same; eauto. }
              rewrite READ; clear READ. eapply VAL; eauto.
          }
          ss. ired.
          guclo deferred_le_sf_ctx_spec. econs; ss.
          { eapply (to_deferred_na_sound (Inst.load _ _ _)); eauto. }
          eapply SIM. eapply mm_na; eauto.
        }

    - destruct (Ordering.le Ordering.plain ord) eqn:ORD.
      + eapply sim_seq_atomic; eauto.
        { match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons (Inst.store lhs rhs ord) b_src) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons (Inst.store lhs rhs ord) b_tgt) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          eapply mm_sim_partial; eauto.
        }
        all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_store; grind.
        { inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. inv H. destruct ord; ss.
          - inv LANG. irw in H. inv H.
          - inv LANG. irw in H. inv H.
        }
        { do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_write; eauto. ss. }
        ss. irw in STEP_TGT.
        inv STEP_TGT. ss; clarify.
        do 3 eexists. splits; ss.
        { refl. }
        { ss. rewrite bind_trigger. eapply ILang.step_write. eauto. }
        { ss. splits; auto. refl. }
        grind. eapply inj_pair2 in H0. clarify.
        hexploit mm_store_at; eauto. i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.

      + destruct (p lhs) eqn:PERM.
        { rewrite ! denote_stmt_inst; rewrite ! denote_inst_store; grind.
          gstep. econs 2. ii. unfold SeqThread.failure.
          do 3 eexists. splits; ss.
          econs 1. econs 1.
          eexists. econs 1. econs.
          rewrite bind_trigger. econs; eauto.
          econs; eauto. destruct ord; ss. rewrite PERM. ss.
        }
        { eapply sim_seq_na; eauto.
          { match goal with
            | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
              assert (TEMP: a = itr_code (cons (Inst.store lhs rhs ord) b_src) le) end.
            { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
            rewrite TEMP; clear TEMP.
            match goal with
            | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
              assert (TEMP: a = itr_code (cons (Inst.store lhs rhs ord) b_tgt) le) end.
            { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
            rewrite TEMP; clear TEMP.
            eapply mm_sim_partial; eauto.
          }
          all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_store; grind.
          { do 2 eexists. esplits.
            - econs; eauto. rewrite bind_trigger. eapply ILang.step_write; eauto.
              eapply SeqState.na_local_step_write; eauto. destruct ord; ss.
            - rewrite PERM. ss.
          }
          inv STEP_TGT.
          rewrite bind_trigger in LANG. inv LANG. inv LOCAL.
          ss. eapply inj_pair2 in H4. subst k. rewrite PERM.
          do 2 eexists. splits; ss.
          { refl. }
          { econs 1; eauto. econs; ss; eauto.
            - rewrite bind_trigger. eapply ILang.step_write; eauto.
            - econs; eauto. rewrite PERM; ss.
          }
          guclo deferred_le_sf_ctx_spec. econs; ss.
          { eapply (to_deferred_na_sound (Inst.store _ _ _)); eauto. }
          eapply SIM. eapply mm_na; eauto. all: ss.
        }

    - destruct (orb (Ordering.le ordr Ordering.na) (Ordering.le ordw Ordering.na)) eqn:ORD.
      + (*na*)
        gstep. econs 1.
        4:{ match goal with
            | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
              assert (TEMP: a = itr_code (cons (Inst.update lhs loc rmw ordr ordw) b_src) le) end.
            { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
            rewrite TEMP; clear TEMP.
            match goal with
            | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
              assert (TEMP: a = itr_code (cons (Inst.update lhs loc rmw ordr ordw) b_tgt) le) end.
            { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
            rewrite TEMP; clear TEMP.
            eapply mm_sim_partial; eauto.
        }
        all:rewrite ! denote_stmt_inst; rewrite ! denote_inst_update; grind.
        { ss. unfold ILang.is_terminal in TERMINAL_TGT. des.
          irw in TERMINAL_TGT. symmetry in TERMINAL_TGT. inv TERMINAL_TGT.
        }
        2:{ ss. rewrite bind_trigger in STEP_TGT.
            apply Bool.orb_true_elim in ORD. destruct ORD as [ORD | ORD].
            - inv STEP_TGT; ss; clarify. des. destruct ordr; ss. destruct ordr; ss.
            - inv STEP_TGT; ss; clarify. des. destruct ordw; ss.
              eapply inj_pair2 in H0. clarify. grind.
              do 3 eexists. splits; ss.
              { refl. }
              { ss. rewrite bind_trigger. eapply ILang.step_update_failure; eauto. }
              ss. grind.
              hexploit mm_update_failure_at; eauto. i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.
              eapply SIM. auto.
        }
        inv STEP_TGT. ss. rewrite bind_trigger in LANG.
        inv LANG.
        * inv LOCAL. ss; clarify. eapply inj_pair2 in H0. clarify. ired.
          do 2 eexists. splits; ss.
          { refl. }
          { econs; eauto. econs; eauto. ss.
            rewrite bind_trigger. eapply ILang.step_update_success; eauto.
            econs; eauto.
          }
          ired.
          guclo deferred_le_sf_ctx_spec. econs; ss.
          { hexploit (to_deferred_na_sound (Inst.update lhs loc rmw ordr ordw)); eauto. }
          eapply SIM. eapply mm_na; eauto.

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
            guclo deferred_le_sf_ctx_spec. econs; ss.
            { hexploit (to_deferred_na_sound (Inst.update lhs loc rmw ordr ordw)); eauto. ss. auto. }
            eapply SIM. eapply mm_na; eauto. ss. auto.
          }
          { do 2 eexists. splits; ss; i.
            { refl. }
            { econs; eauto. econs; eauto. ss. rewrite bind_trigger.
              eapply ILang.step_update_failure; eauto.
              eapply SeqState.na_local_step_read. eauto. i.
              assert (READ: SeqMemory.read loc src_m = SeqMemory.read loc m1).
              { eapply mm_read_same; eauto. }
              rewrite READ; clear READ. auto.
            }
            ired.
            guclo deferred_le_sf_ctx_spec. econs; ss.
            { hexploit (to_deferred_na_sound (Inst.update lhs loc rmw ordr ordw)); eauto. ss. auto. }
            eapply SIM. eapply mm_na; eauto. ss. auto.
          }

      + apply Bool.orb_false_elim in ORD. des.
        eapply sim_seq_atomic; eauto.
        { match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons (Inst.update lhs loc rmw ordr ordw) b_src) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons (Inst.update lhs loc rmw ordr ordw) b_tgt) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
          rewrite TEMP; clear TEMP.
          eapply mm_sim_partial; eauto.
        }
        all:rewrite ! denote_stmt_inst; rewrite ! denote_inst_update; grind.
        { i. inv H. inv LOCAL; ss; clarify.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
          - inv LANG. irw in H. inv H.
            unfold __guard__ in ORD1. des; [destruct ordr; ss | destruct ordw; ss].
        }
        { destruct rmw.
          - do 2 eexists. esplits. rewrite bind_trigger.
            eapply ILang.step_update_success; ss; eauto.
            econs; eauto. ss.
            destruct ordr; destruct ordw; ss; clarify.
          - destruct (Const.eqb old (SeqMemory.read loc tgt_m)) eqn:EVAL.
            2:{ do 2 eexists. esplits. rewrite bind_trigger.
                eapply ILang.step_update_failure; ss; eauto.
                econs 3; eauto. rewrite EVAL; ss.
                destruct ordr; destruct ordw; ss; clarify.
            }
            destruct b.
            + do 2 eexists. esplits. rewrite bind_trigger.
              eapply ILang.step_update_success; ss; eauto.
              econs 2; eauto. rewrite EVAL; ss.
              destruct ordr; destruct ordw; ss; clarify.
            + do 2 eexists. esplits. rewrite bind_trigger.
              eapply ILang.step_update_failure; ss; eauto.
              econs 3; eauto. rewrite EVAL; ss.
              destruct ordr; destruct ordw; ss; clarify.
        }
        ss. irw in STEP_TGT. inv STEP_TGT.
        { ss; clarify.
          do 3 eexists. splits; ss.
          { refl. }
          { ss. rewrite bind_trigger. eapply ILang.step_update_success; ss; eauto. }
          { ss. splits; auto. refl. }
          grind. eapply inj_pair2 in H1. clarify. ired.
          hexploit mm_update_success_at; eauto.
          { ss. eapply andb_true_intro; eauto. }
          i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.
        }
        { ss; clarify.
          do 3 eexists. splits; ss.
          { refl. }
          { ss. rewrite bind_trigger. eapply ILang.step_update_failure; ss; eauto. }
          grind. eapply inj_pair2 in H0. clarify. ired.
          hexploit mm_update_failure_at; eauto.
          i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.
        }

    - eapply sim_seq_atomic; eauto.
      { match goal with
        | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
          assert (TEMP: a = itr_code (cons (Inst.fence ordr ordw) b_src) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
        rewrite TEMP; clear TEMP.
        match goal with
        | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
          assert (TEMP: a = itr_code (cons (Inst.fence ordr ordw) b_tgt) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
        rewrite TEMP; clear TEMP.
        eapply mm_sim_partial; eauto.
      }
      all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_fence; grind.
      { i. inv H. inv LOCAL; ss; clarify.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
      }
      { do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_fence; eauto. ss. }
      ss. irw in STEP_TGT. inv STEP_TGT. ss; clarify.
      do 3 eexists. splits; ss.
      { refl. }
      { ss. rewrite bind_trigger. eapply ILang.step_fence. eauto. }
      grind. eapply inj_pair2 in H0. clarify.
      hexploit mm_fence; eauto. i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.

    - eapply sim_seq_atomic; eauto.
      { match goal with
        | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
          assert (TEMP: a = itr_code (cons (Inst.syscall lhs rhses) b_src) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
        rewrite TEMP; clear TEMP.
        match goal with
        | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
          assert (TEMP: a = itr_code (cons (Inst.syscall lhs rhses) b_tgt) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
        rewrite TEMP; clear TEMP.
        eapply mm_sim_partial; eauto.
      }
      all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_syscall; grind.
      { i. inv H. inv LOCAL; ss; clarify.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
        - inv LANG. irw in H. apply eq_is_bisim in H. eapply eqitree_inv_Vis_r in H. des. ss.
      }
      { do 2 eexists. esplits. rewrite bind_trigger. eapply ILang.step_syscall; eauto. ss. }
      ss. irw in STEP_TGT. inv STEP_TGT. ss; clarify.
      do 3 eexists. splits; ss.
      { refl. }
      { ss. rewrite bind_trigger. eapply ILang.step_syscall. eauto. }
      { ss. refl. }
      grind. eapply inj_pair2 in H0. clarify. grind.
      hexploit mm_syscall; eauto. i; des. exists i_src, mem_src, (to_deferred mp). splits; auto.

    - rewrite ! denote_stmt_inst. rewrite ! denote_inst_abort. grind. apply sim_seq_ub.

    - eapply sim_seq_na; eauto.
      { match goal with
        | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
          assert (TEMP: a = itr_code (cons (Inst.choose lhs) b_src) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
        rewrite TEMP; clear TEMP.
        match goal with
        | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
          assert (TEMP: a = itr_code (cons (Inst.choose lhs) b_tgt) le) end.
        { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. grind. }
        rewrite TEMP; clear TEMP.
        eapply mm_sim_partial; eauto.
      }
      all: rewrite ! denote_stmt_inst; rewrite ! denote_inst_choose; grind.
      { do 2 eexists. esplits.
        - econs; eauto. rewrite bind_trigger. eapply ILang.step_choose; eauto.
          eapply SeqState.na_local_step_silent; eauto.
        - ss.
      }
      inv STEP_TGT. rewrite bind_trigger in LANG. inv LANG. inv LOCAL.
      ss; clarify.
      eapply inj_pair2 in H0. clarify. grind.
      do 2 eexists. splits; ss.
      { refl. }
      { econs 1; eauto. econs; ss; eauto.
        - rewrite bind_trigger. eapply ILang.step_choose; eauto.
        - econs; eauto.
      }
      grind. instantiate (1:=val).
      guclo deferred_le_sf_ctx_spec. econs; ss.
      { hexploit (to_deferred_na_sound (Inst.choose lhs)); eauto. ss. }
      eapply SIM. eapply mm_na; eauto. ss.

      Unshelve. all: ss. all: try exact 0.

  Qed.


  Hypothesis block_d_dec: forall blk p d f (FUN: f = block_d O2 blk p), Opt2.le O2 (f (f d)) (f d).
  Hypothesis block_d_fix: forall blk f (FUN: f = block_d O2 blk) p,
      @n_fix (Opt2.D O2) (MLattice.eq (Opt2.M O2)) (MLattice.eq_Equiv (Opt2.M O2)) (f p) (S (Opt2.N O2)).

  Hypothesis sim_seq_inst_opt:
    forall r g p
      le src_m tgt_m mp b_src b_tgt
      (i: Inst.t) src tgt
      (MM: match_mem (inst_gd i mp) src_m tgt_m)
      (MC: match_code (inst_gd i mp) (cons i b_src) (cons (Opt2.opt_inst O2 mp i) b_tgt))
      (MC0: match_code mp b_src b_tgt)
      (OPT: Opt2.do_opt O2 mp i)
      (SRC: src = @SeqState.mk (lang _)
                               (r0 <- denote_stmt le i;;
                                x <- (let (le1, _) := r0 in denote_block le1 b_src);;
                                (let (le2, _) := x in Ret (le2 ret_reg)))
                               src_m)
      (TGT: tgt = @SeqState.mk (lang _)
                               (r0 <- denote_stmt le (Opt2.opt_inst O2 mp i);;
                                x <- (let (le1, _) := r0 in denote_block le1 b_tgt);;
                                (let (le2, _) := x in Ret (le2 ret_reg)))
                               tgt_m)
      (SIM: forall up le1 sm tm,
          (<<MM1: match_mem mp sm tm>>) ->
          gupaco7 _sim_seq (cpn7 _sim_seq) g _ _ term up (to_deferred mp)
                  (@SeqState.mk (lang _) (x <- denote_block le1 b_src;; (let (le2, _) := x in Ret (le2 ret_reg))) sm)
                  (@SeqState.mk (lang _) (x <- denote_block le1 b_tgt;; (let (le2, _) := x in Ret (le2 ret_reg))) tm))
    ,
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p (to_deferred (inst_gd i mp)) src tgt.


  Lemma sim_seq_tau_ub
        r g p d src tgt sm tm
    :
      gpaco7 _sim_seq (cpn7 _sim_seq) r g _ _ term p d
             (@SeqState.mk (lang _) (tau;; trigger MemE.abort;; src) sm)
             (@SeqState.mk (lang _) tgt tm).
  Proof.
    gstep. econs 2. econs. do 2 eexists. splits.
    { econs 2. econs. econs. econs; eauto. econs. econs 1. }
    { econs 1. }
    eapply seq_thread_failure.
  Qed.


  Theorem match_state_sim
          p mp src tgt
          (MS: match_state mp src tgt)
    :
      sim_seq term p (to_deferred mp) src tgt.
  Proof.
    ginit. do 5 revert1. gcofix CIH. i. inv MS.
    dup MC. rename MC0 into UPDATE. eapply (@match_code2_opt_inv O2) in UPDATE.
    apply prod_fst in UPDATE. rewrite Opt2.opt_block_fst in UPDATE.
    inversion MC.
    - ss; clarify.
      eapply sim_seq_term; ss; eauto.
      { unfold itr_code. rewrite denote_block_nil. grind. eexists; eauto. }
      exists (build_state nil le src_m).
      apply mm_bot in MM. subst.
      splits; ss; auto.
      { unfold itr_code. rewrite ! denote_block_nil. ired. econs; eauto. }
      refl. rewrite to_deferred_bot. refl.

    - ss; clarify.
      unfold build_state, itr_code.
      rewrite ! denote_block_cons. ired.
      eapply sim_seq_inst.
      3,4,5: eauto.
      { unfold inst_gd. rewrite H. auto. }
      { unfold inst_gd. rewrite H. auto. }
      i. gbase. eapply CIH; eauto. ss.
      econs. 3,4: ss; eauto. all: eauto.

    - ss; clarify.
      unfold build_state. unfold itr_code.
      rewrite ! denote_block_cons. ired.
      eapply sim_seq_inst_opt.
      4,5,6: eauto.
      { unfold inst_gd. rewrite H. auto. }
      { unfold inst_gd. rewrite H. auto. }
      eauto.
      i. gbase. eapply CIH; eauto.
      econs. 3,4: ss; eauto. all: eauto.

    - ss; clarify.
      unfold build_state. unfold itr_code.
      rewrite ! denote_block_cons.
      rewrite ! denote_stmt_ite2. grind.

      + rewrite ! denote_block_cons. rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. grind.
        assert (FLAG: Flags.le (to_deferred (meet2 data1 data2)) (to_deferred data2)).
        { eapply to_deferred_mon. eapply (MLattice.meet_is_min_r (T:=ML2 O2)). }
        eapply sim_seq_tau; ss.
        { apply symmetry in OPT2. hexploit (match_code2_add_block sb2 MC0 OPT2). i.
          match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons Inst.skip (add_block sb2 b_src)) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip.
            grind. rewrite denote_add_block. grind. }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons Inst.skip (add_block tb2 b_tgt)) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip.
            grind. rewrite denote_add_block. grind. }
          rewrite TEMP; clear TEMP.
          eapply sim_seq_partial_case_mon.
          { instantiate (1:=to_deferred data2). auto. }
          eapply mm_sim_partial.
          - eapply mm_mon. 2: eapply MM.
            rewrite <- H. eapply (MLattice.meet_is_min_r (T:=ML2 O2)).
          - eapply match_code2_opt_inv in MC0; eauto.
            apply prod_fst in MC0. rewrite opt_block_fst in MC0.
            apply prod_fst in OPT2. setoid_rewrite opt_block_fst in OPT2.
            rewrite (block_gd_skip). rewrite <- OPT2.
            erewrite (block_gd_add_block_partial); eauto.
        }
        eapply sim_seq_upto_deferred.
        { instantiate (1:=to_deferred data2). auto. }
        gbase. eapply CIH.
        econs.
        3:{ unfold build_state. f_equal.
            instantiate (1:=le).
            instantiate (1:=(add_block sb2 b_src)).
            rewrite itr_code_add_block. grind. }
        3:{ unfold build_state. f_equal.
            instantiate (1:=(add_block tb2 b_tgt)).
            rewrite itr_code_add_block. grind. }
        { eapply (match_code2_add_block).
          2:{ setoid_rewrite <- OPT2. eauto. }
          eauto. }
        eapply mm_mon. 2: eauto.
        rewrite <- H. eapply (MLattice.meet_is_min_r (T:=ML2 O2)).

      + rewrite ! denote_block_cons. rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. grind.
        assert (FLAG: Flags.le (to_deferred (meet2 data1 data2)) (to_deferred data1)).
        { eapply to_deferred_mon. eapply (MLattice.meet_is_min_l (T:=ML2 O2)). }
        eapply sim_seq_tau; ss.
        { apply symmetry in OPT1. hexploit (match_code2_add_block sb1 MC0 OPT1). i.
          match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons Inst.skip (add_block sb1 b_src)) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip.
            grind. rewrite denote_add_block. grind. }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons Inst.skip (add_block tb1 b_tgt)) le) end.
          { unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip.
            grind. rewrite denote_add_block. grind. }
          rewrite TEMP; clear TEMP.
          eapply sim_seq_partial_case_mon.
          { instantiate (1:=to_deferred data1). auto. }
          eapply mm_sim_partial.
          - eapply mm_mon. 2: eapply MM.
            rewrite <- H. eapply (MLattice.meet_is_min_l (T:=ML2 O2)).
          - eapply match_code2_opt_inv in MC0; eauto.
            apply prod_fst in MC0. rewrite Opt2.opt_block_fst in MC0.
            apply prod_fst in OPT1. setoid_rewrite Opt2.opt_block_fst in OPT1.
            erewrite (block_gd_skip). rewrite <- OPT1.
            erewrite (block_gd_add_block_partial); eauto.
        }
        eapply sim_seq_upto_deferred.
        { instantiate (1:=to_deferred data1). auto. }
        gbase. eapply CIH.
        econs.
        3:{ unfold build_state. f_equal.
            instantiate (1:=le).
            instantiate (1:=(add_block sb1 b_src)).
            rewrite itr_code_add_block. grind. }
        3:{ unfold build_state. f_equal.
            instantiate (1:=(add_block tb1 b_tgt)).
            rewrite itr_code_add_block. grind. }
        { eapply (match_code2_add_block).
          2:{ setoid_rewrite <- OPT1. eauto. }
          eauto. }
        eapply mm_mon. 2: eauto.
        rewrite <- H. eapply (MLattice.meet_is_min_l (T:=ML2 O2)).

      + eapply sim_seq_tau_ub.

    - unfold build_state. unfold itr_code.
      subst src_c tgt_c s_src s_tgt.
      rewrite ! denote_block_cons. rewrite ! denote_stmt_while2. ired.
      subst src tgt.
      destruct (is_zero (denote_expr le e)) eqn:COND0.
      destruct b eqn:COND.

      + depgen UPDATE. rewrite ! denote_block_cons. rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. ired. i.
        assert (FLAG: Flags.le (to_deferred (meet2 data0 (meet2 data1 data2))) (to_deferred data0)).
        { eapply to_deferred_mon. eapply (MLattice.meet_is_min_l (T:=ML2 O2)). }
        eapply sim_seq_tau. 1,2,3: ss; eauto.
        { match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons Inst.skip b_src) le) end.
          { clear MC MM MC0 DATA1 DATA2 DATA.
            unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
            rewrite denote_block_nil. grind.
          }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons Inst.skip b_tgt) le) end.
          { clear MC MM MC0 DATA1 DATA2 DATA.
            unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
            rewrite denote_block_nil. grind.
          }
          rewrite TEMP; clear TEMP.
          subst mp.
          eapply sim_seq_partial_case_mon.
          { instantiate (1:=to_deferred data0). auto. }
          eapply mm_sim_partial.
          - eapply mm_mon. 2: eauto. eapply (MLattice.meet_is_min_l (T:=ML2 O2)).
          - eapply match_code2_opt_inv in MC0. apply prod_fst in MC0. rewrite Opt2.opt_block_fst in MC0.
            rewrite <- MC0. erewrite (block_gd_skip). auto.
        }
        rewrite ! denote_block_nil. ired. subst mp.
        eapply sim_seq_upto_deferred.
        { instantiate (1:=to_deferred data0). auto. }
        gbase. eapply CIH.
        econs. 1,3,4: ss; eauto.
        eapply mm_mon. 2: eauto. eapply (MLattice.meet_is_min_l (T:=ML2 O2)).

      + depgen UPDATE. rewrite ! denote_block_cons. rewrite ! denote_stmt_inst. rewrite ! denote_inst_skip. ired. i.
        assert (DATALE: data_le (meet2 data0 (meet2 data1 data2)) (block_gd sb data)).
        { subst mp. subst data.
          unfold block_gd. do 2 setoid_rewrite block_gd_meet_comm.
          replace (Opt2.block_gd sb data1) with data1.
          2:{ rewrite DATA1. symmetry. eapply (@block_gd_fix O2). eapply block_d_fix. eauto. }
          replace (Opt2.block_gd sb data2) with data2.
          2:{ rewrite DATA2. symmetry. eapply (@block_gd_fix O2). eapply block_d_fix. eauto. }
          match goal with
          | [|- data_le _ (meet2 ?x (meet2 ?y ?z))] =>
            replace (meet2 x (meet2 y z)) with (meet2 (meet2 x y) z) end.
          2:{ erewrite meet_assoc2. auto. }
          replace (meet2 (Opt2.block_gd sb data0) data1) with data1.
          2:{ rewrite meet_comm2. eapply (MLattice.le_spec (T:=ML2 O2)). subst data1. eapply block_gd_le_n. eapply block_d_dec. }
          eapply (MLattice.meet_is_min_r (T:=ML2 O2)).
        }
        assert (FLAG: Flags.le (to_deferred (meet2 data0 (meet2 data1 data2))) (to_deferred (block_gd sb data))).
        { eapply to_deferred_mon. auto. }
        eapply sim_seq_tau. 1,2,3: ss; eauto.
        { match goal with
          | [|- sim_seq_partial_case _ _ {| SeqState.state := ?a; SeqState.memory := _ |} _] =>
            assert (TEMP: a = itr_code (cons Inst.skip (add_block sb (cons Inst.skip (cons (while e sb) b_src)))) le) end.
          { clear MC MM MC0 DATA1 DATA2 DATA.
            unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
            rewrite ! denote_add_block. grind. rewrite ! denote_block_cons. grind. rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind.
          }
          rewrite TEMP; clear TEMP.
          match goal with
          | [|- sim_seq_partial_case _ _ _ {| SeqState.state := ?a; SeqState.memory := _ |}] =>
            assert (TEMP: a = itr_code (cons Inst.skip (add_block tb (cons Inst.skip (cons (while e tb) b_tgt)))) le) end.
          { clear MC MM MC0 DATA1 DATA2 DATA.
            unfold itr_code. rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
            rewrite ! denote_add_block. grind. rewrite ! denote_block_cons. grind. rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind.
          }
          rewrite TEMP; clear TEMP.
          subst mp.
          eapply sim_seq_partial_case_mon.
          { instantiate (1:=to_deferred (block_gd sb data)). auto. }
          eapply mm_sim_partial.
          - subst data. eapply mm_mon. 2: eauto. auto.
          - subst data.
            erewrite block_gd_skip. erewrite (block_gd_add_block_partial). ss.
            erewrite block_gd_skip. auto.
        }
        eapply sim_seq_upto_deferred.
        { instantiate (1:=to_deferred (block_gd sb mp)). subst mp. subst data. auto. }
        gbase. eapply CIH.
        econs.
        3:{ unfold build_state. f_equal.
            instantiate (1:=le).
            instantiate (1:=add_block sb (cons Inst.skip (cons (while e sb) b_src))).
            rewrite itr_code_add_block. rewrite denote_add_block.
            clear DATA1 DATA2 DATA OPT H. grind.
            rewrite ! denote_block_cons. grind.
            rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind. }
        3:{ unfold build_state. f_equal.
            instantiate (1:=add_block tb (cons Inst.skip (cons (while e tb) b_tgt))).
            rewrite itr_code_add_block. rewrite denote_add_block.
            clear DATA1 DATA2 DATA OPT H. grind.
            rewrite ! denote_block_cons. grind.
            rewrite ! denote_block_cons. grind.
            rewrite denote_block_nil. grind. }
        { eapply (match_code2_add_block).
          2:{ eapply injective_projections.
              - simpl. eapply opt_block_fst.
              - simpl. rewrite OPT. ss. }
          assert (SSPEC: forall mp, mp = inst_gd Inst.skip mp).
          { i. symmetry. eapply skip_gd. }
          specialize SSPEC with mp. rewrite SSPEC; clear SSPEC.
          econs 2; eauto.
          eapply Opt2.do_opt_not_skip.
        }
        subst mp.
        eapply mm_mon. 2: eauto. subst data. auto.

      + ired. eapply sim_seq_tau_ub.

  Qed.

End SIM.
