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

Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.

Require Import Simple.
Require Import SimAux.
Require Import SeqAux.

Require Import FoldN.
Require Import Knowledge.
Require Import Opt4.
Require Import Opt4Sim.

Require Import ITreeLangNotations.
Require Import ITreeLangProof.
Require Import ITreeLang.

Require Import RRforwarding.
Require Import RRforwardingProof1.

Require Export ITreeLib.





Section MATCH.

  Hint Resolve eq_Transitive : core.

  Ltac dest_loc l1 l2 :=
    destruct (Loc.eqb l1 l2) eqn:LOC;
    [rewrite Loc.eqb_eq in LOC; clarify; try rewrite Loc.eqb_refl; ss |
     hexploit LOC; intros DIFFL; rewrite Loc.eqb_sym in LOC; try rewrite LOC; apply Loc.eqb_neq in DIFFL; ss].

  Ltac dest_ident s1 s2 :=
    try unfold dists; destruct (Ident.eqb s1 s2) eqn:IDENT;
    [rewrite Ident.eqb_eq in IDENT; clarify; try rewrite Ident.eqb_refl; ss |
     hexploit IDENT; intros IDENT0; rewrite Ident.eqb_sym in IDENT; try rewrite IDENT;
     apply Ident.eqb_neq in IDENT0; ss; try rewrite RelDec.rel_dec_neq_false; auto].



  Let O4 := RRfwd_opt4.
  Let inst_d := RRfwd_inst.
  Let inst_gd := @inst_gd RRfwd_opt4.
  Let le2 := @le2 RRfwd_opt4.
  Let GD := GD RRfwd_opt4.

  (*need to handle undef*)
  Definition match_data : GD -> Perms.t -> SeqMemory.t -> lenv -> Prop :=
    fun mp p m le =>
      forall l id, (IdentSet.In id (mp l)) -> (p l = Perm.high) ->
              Const.le (le id) (SeqMemory.read l m).


  Lemma md_mon: forall d1 d2 p m l (LE: le2 d1 d2) (MD: match_data d2 p m l), match_data d1 p m l.
  Proof.
    i. unfold match_data in *. i. eapply MD; eauto.
    unfold le2, Opt4.le2 in LE. ss. eapply LE in H. auto.
  Qed.

  Lemma md_bot: forall p m le, match_data (fun _: Loc.t => bot) p m le.
  Proof.
    ii. unfold bot in H. rss.
  Qed.

  Lemma md_skip:
    forall mp p m le (MD: match_data mp p m le)
    ,
      match_data (inst_gd Inst.skip mp) p m le.
  Proof.
    ss.
  Qed.


  Lemma md_assign:
    forall mp p m le (MD: match_data mp p m le)
      x v eval
      (EVAL: denote_expr le v = eval)
    ,
      match_data (inst_gd (Inst.assign x v) mp) p m (update x eval le).
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_assign_ordf; auto.
    unfold match_data in *. i. specialize MD with l id.
    rss. unfold update. apply Ident.eqb_neq in H1. rewrite Ident.eqb_sym. rewrite H1.
    eauto.
  Qed.

  Lemma md_load_na:
    forall mp p m le (MD: match_data mp p m le)
      x l ord (ORD: Ordering.le ord Ordering.na)
      val (VAL: Perm.le Perm.high (p l) -> Const.le val (SeqMemory.read l m))
    ,
      match_data (inst_gd (Inst.load x l ord) mp) p m (update x val le).
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_load_ord1f; auto.
    unfold match_data in *. i. specialize MD with l0 id.
    unfold update.
    dest_ident x id.
    - dest_loc l l0.
      + apply VAL; eauto. rewrite H0; auto.
      + rss.
    - dest_loc l l0.
      + rss.
      + rss.
  Qed.

  Lemma md_load_at:
    forall mp p m le (MD: match_data mp p m le)
      x l ord
      val ev i o p1 m1
      (EV: ev = ProgramEvent.read l val ord)
      (ATOMIC: is_atomic_event ev)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.load x l ord) mp) p1 m1 (update x val le).
  Proof.
    i. clarify. ss. dup EVENT. unfold SeqEvent.wf_input in EVENT. des. ss. dup STEP. inv STEP.
    inv REL.
    2:{ hexploit RELEASE. rewrite <- H0. ss. i; clarify. }
    clear RELEASE RELEASE0.
    unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    hexploit (ord_inv1 ord). i. des.
    { destruct ord; ss. }
    - rewrite RRfwd_load_ord2f; auto.
      unfold match_data in *. i; ss.
      destruct (Loc.eqb l l0) eqn:LOC.
      { unfold bot in H2. rss. }
      specialize MD with l0 id. unfold update.
      rss. dup H4. apply Ident.eqb_neq in H5. rewrite Ident.eqb_sym in H5. rewrite H5.
      hexploit red_rlx.
      5,6: eauto.
      all: ss; auto.
      { destruct ord; ss. }
      eapply Loc.eqb_neq in LOC. eapply LOC.
      i; des. rewrite <- MEMV. eapply MD; eauto. rewrite PERM; auto.
    - rewrite RRfwd_load_ord3f; auto. apply md_bot.
  Qed.


  Lemma md_store_na:
    forall mp p m le (MD: match_data mp p m le)
      x e ord (ORD: Ordering.le ord Ordering.na)
      (PERM : (p x) = Perm.high)
      eval (EVAL: denote_expr le e = eval)
    ,
      match_data (inst_gd (Inst.store x e ord) mp) p (SeqMemory.write x eval m) le.
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_write_ordf; auto.
    unfold match_data in *. i.
    dest_loc x l.
    { unfold bot in H; rss. }
    specialize MD with l id.
    unfold ValueMap.write. rewrite Loc.eq_dec_neq; auto.
  Qed.

  Lemma md_store_at:
    forall mp p m le (MD: match_data mp p m le)
      x e ord
      ev i o p1 m1
      (EV: ev = ProgramEvent.write x (denote_expr le e) ord)
      (ATOMIC: is_atomic_event ev)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.store x e ord) mp) p1 m1 le.
  Proof.
    i. clarify. ss.
    unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_write_ordf; auto.
    unfold match_data in *. i.
    dest_loc l x.
    { rewrite Loc.eqb_refl in H. unfold bot in *; rss. }
    specialize MD with l id. rewrite LOC in H.
    dup EVENT. unfold SeqEvent.wf_input in EVENT. des. ss.
    dup STEP. inv STEP. inv REL.
    - hexploit red_rlx. 5,6: eauto. all: ss.
      { destruct (Ordering.le Ordering.strong_relaxed ord) eqn:RLX.
        { hexploit RELEASE0; auto. i. rewrite <- H2 in H1. ss. }
        destruct ord; ss.
      }
      eauto.
      i; des. rewrite <- MEMV. eapply MD; auto. rewrite PERM; auto.
    - hexploit red_rel. 5,6: eauto. all: ss; auto.
      { hexploit RELEASE. rewrite <- H2; auto. auto. }
      rename H into IN; depgen IN. depgen MD. rename H0 into PERM; depgen PERM. depgen DIFFL. clear.
      i; des. specialize H with l. hexploit H; clear H; auto. i; des.
      rewrite RELMEMV. eapply MD; eauto.
      rewrite PERM in RELPERM. hexploit perm_meet_high. erewrite RELPERM; eauto. i; des; auto.
  Qed.


  Lemma md_update_na:
    forall mp p m le (MD: match_data mp p m le)
      x l rmw ordr ordw (ORD: (Ordering.le ordr Ordering.na) \/ (Ordering.le ordw Ordering.na))
      val
    ,
      match_data (inst_gd (Inst.update x l rmw ordr ordw) mp) p m (update x val le).
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    des.
    - hexploit (ord_inv1 ordr). i. des.
      2,3: destruct ordr; ss.
      rewrite RRfwd_write_ordf.
      unfold match_data in *; i.
      rewrite RRfwd_load_ord1 in H0; auto.
      dest_loc l l0.
      { unfold bot in *; rss. }
      specialize MD with l0 id.
      unfold update. dest_ident x id.
      { rss. }
      rss.
    - rewrite RRfwd_write_ordf.
      unfold match_data in *; i.
      hexploit (ord_inv1 ordr). i. des.
      + rewrite RRfwd_load_ord1 in H; auto.
        dest_loc l l0.
        { unfold bot in *; rss. }
        specialize MD with l0 id.
        unfold update. dest_ident x id.
        { rss. }
        rss.
      + rewrite RRfwd_load_ord2 in H; auto.
        dest_loc l l0.
        { unfold bot in *; rss. }
        specialize MD with l0 id.
        unfold update. dest_ident x id.
        { rss. }
        rss.
      + rewrite RRfwd_load_ord3 in H; auto.
        dest_loc l l0.
        all: unfold bot in *; rss.
  Qed.

  Lemma md_update_at_success:
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
  Proof.
    i. clarify. ss. apply andb_prop in ATOMIC. des.
    unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_write_ordf; eauto.
    unfold match_data in *. i.
    dest_loc l0 l.
    { rewrite Loc.eqb_refl in H. unfold bot in *; rss. }
    rewrite LOC in H.
    hexploit (ord_inv1 ordr). i. des.
    { exfalso. destruct ordr; ss. }
    - rewrite RRfwd_load_ord2 in H; eauto.
      rewrite LOC in H. specialize MD with l0 id. rss.
      unfold update. destruct (Ident.eqb x id) eqn:ID.
      { rewrite Ident.eqb_eq in ID. subst x. exfalso; apply H2; auto. }
      destruct (Ordering.le ordw Ordering.relaxed) eqn:ORDW.
      + hexploit red_rlx. 5,6: eauto. all: ss; auto.
        { apply andb_true_intro. split; auto. }
        { destruct ordr; ss. }
        { destruct ordw; ss. }
        eauto.
        i. des. rewrite <- MEMV. eapply MD; eauto. rewrite PERM. auto.
      + hexploit red_rel. 5,6: eauto. all: ss; auto.
        { apply andb_true_intro. split; auto. }
        { destruct ordr; ss. }
        { destruct ordw; ss. }
        i. des. hexploit H3; clear H3; eauto. i; des.
        rewrite RELMEMV. apply MD; auto.
        rewrite H0 in RELPERM. hexploit perm_meet_high. rewrite RELPERM; auto. i; des; auto.
    - rewrite RRfwd_load_ord3 in H; eauto. unfold bot in *; rss.
  Qed.

  Lemma md_update_at_failure:
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
  Proof.
    i. clarify. ss.
    unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_write_ordf; eauto.
    unfold match_data in *. i.
    dest_loc l0 l.
    { rewrite Loc.eqb_refl in H. unfold bot in *; rss. }
    hexploit (ord_inv1 ordr). i. des.
    { exfalso. destruct ordr; ss. }
    - rewrite RRfwd_load_ord2 in H; eauto.
      rewrite LOC in H. specialize MD with l0 id. rss.
      unfold update. dest_ident x id.
      hexploit red_rlx. 5,6: eauto. all: ss; auto.
      { destruct ordr; ss. }
      eauto.
      i; des. rewrite <- MEMV. apply MD; auto. rewrite PERM; auto.
    - rewrite RRfwd_load_ord3 in H; eauto. rewrite LOC in H. unfold bot in *; rss.
  Qed.


  Lemma md_fence:
    forall mp p m le (MD: match_data mp p m le)
      ordr ordw
      ev i o p1 m1
      (EV: ev = ProgramEvent.fence ordr ordw)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
    ,
      match_data (inst_gd (Inst.fence ordr ordw) mp) p1 m1 le.
  Proof.
    i. clarify. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    hexploit (ord_inv3 ordw). i. des.
    - rewrite RRfwd_fence_w_ord1f; eauto.
      unfold match_data in *. i.
      specialize MD with l id.
      hexploit (ord_inv2 ordr). i. des.
      + rewrite RRfwd_fence_r_ord1 in H0; eauto.
        destruct (Ordering.le ordw Ordering.relaxed) eqn: ORDW.
        * hexploit red_rlx2. 5,6: eauto. all: ss; auto.
          { apply Bool.orb_false_intro. destruct ordw; ss. destruct ordr; ss. }
          { destruct ordw; ss. }
          i; des. rewrite <- MEM. apply MD; auto. rewrite PERM. auto.
        * hexploit red_rel2. 5,6: eauto. all: ss; auto.
          { apply Bool.orb_false_intro. destruct ordw; ss. destruct ordr; ss. }
          { destruct ordw; ss. }
          i; des. unfold SeqMemory.read. rewrite RELMEMV. apply MD; auto.
          eapply equal_f in RELPERM. rewrite H1 in RELPERM. hexploit perm_meet_high. eauto. i; des; auto.
      + rewrite RRfwd_fence_r_ord2 in H0; eauto. unfold bot in *; rss.
    - rewrite RRfwd_fence_w_ord2f; eauto. apply md_bot.
  Qed.

  Lemma md_syscall:
    forall mp p m le (MD: match_data mp p m le)
      x es
      sys ev i o p1 m1
      (EV: ev = ProgramEvent.syscall sys)
      (EVENT: SeqEvent.wf_input ev i)
      (STEP: SeqEvent.step i o p m p1 m1)
      val
    ,
      match_data (inst_gd (Inst.syscall x es) mp) p1 m1 (update x val le).
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss. apply md_bot.
  Qed.

  Lemma md_choose:
    forall mp p m le (MD: match_data mp p m le)
      x val,
      match_data (inst_gd (Inst.choose x) mp) p m (update x val le).
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite RRfwd_assign_ordf; auto.
    unfold match_data in *. i. specialize MD with l id.
    rss. unfold update. apply Ident.eqb_neq in H1. rewrite Ident.eqb_sym. rewrite H1.
    eauto.
  Qed.

End MATCH.



Section PROOF.

  Let O4 := RRfwd_opt4.
  Let inst_d := RRfwd_inst.
  Let inst_gd := @inst_gd RRfwd_opt4.
  Let le2 := @le2 RRfwd_opt4.
  Let GD := GD RRfwd_opt4.



  Lemma choose_subset_in:
    forall mp' mp e rhs
      (CHOOSE: IdentSet.choose (mp' rhs) = Some e)
      (LE: le2 mp' mp),
      IdentSet.In e (mp rhs).
  Proof.
    i. unfold le2, Opt4.le2 in LE. ss. apply IdentSet.choose_spec1 in CHOOSE.
    eapply LE in CHOOSE. auto.
  Qed.


  Definition sim_val: Const.t -> Const.t -> Prop := eq.
  Lemma sim_val_refl: forall a, sim_val a a.
  Proof. refl. Qed.
  Let term := term sim_val.

  Lemma sim_seq_inst_opt:
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
          gupaco4 (_sim_seq term) (cpn4 (_sim_seq term)) g up Flags.bot
                  (@SeqState.mk (lang _) (src_k (lenv1, ())) mem1)
                  (@SeqState.mk (lang _) (tgt_k (lenv1, ())) mem1))
      (LE: le2 mp' mp)
      (OPT: (Opt4.do_opt O4) mp' i)
      (IOPT: i_opt = (Opt4.opt_inst O4) mp' i),
      gpaco4 (_sim_seq term) (cpn4 (_sim_seq term)) r g p Flags.bot src tgt.
  Proof.
    i. clarify. destruct i; clarify. ss. des_ifs.
    rewrite ! denote_stmt_inst. rewrite denote_inst_load. rewrite denote_inst_assign.
    grind. clear OPT. dup MD.
    unfold match_data in MD. specialize MD with rhs e. hexploit choose_subset_in; eauto. intro IN.
    destruct (p rhs) eqn:PERM.
    - eapply sim_seq_na; ss; clarify.
      { apply partial_same_mem; auto. }
      { do 2 eexists. split.
        - econs; eauto. ss. eapply ILang.step_tau; ss. econs; ss.
        - ss.
      }
      ii. inv STEP_TGT. inv LANG. inv LOCAL.
      do 2 eexists. repeat split; try red; i.
      { refl. }
      { econs 1; eauto. econs; ss.
        - rewrite bind_trigger. eapply ILang.step_read; eauto.
        - econs. auto. i. rewrite PERM in H. discriminate H.
      }
      grind.
      eapply SIM; eauto. red. eapply md_load_na; auto. i. rewrite PERM in H. ss.
    - eapply sim_seq_na; ss; clarify.
      { apply partial_same_mem; auto. }
      { do 2 eexists. split.
        - econs; eauto. ss. eapply ILang.step_tau; ss. econs; ss.
        - ss.
      }
      ii. inv STEP_TGT. inv LANG. inv LOCAL.
      do 2 eexists. repeat split; try red; i.
      { refl. }
      { econs 1; eauto. econs; ss.
        - rewrite bind_trigger. eapply ILang.step_read; eauto.
        - econs. eauto. i. eapply MD; eauto.
      }
      grind.
      eapply SIM; eauto. red. eapply md_load_na; auto.
  Qed.


  Let match_state := Opt4Sim.match_state match_data.

  Theorem match_state_sim
          p src tgt
          (MS: match_state p src tgt)
    :
      sim_seq term p Flags.bot src tgt.
  Proof.
    eapply (@match_state_sim O4).
    eapply md_skip.
    eapply md_assign.
    eapply md_load_na.
    eapply md_load_at.
    eapply md_store_na.
    eapply md_store_at.
    eapply md_update_na.
    eapply md_update_at_success.
    eapply md_update_at_failure.
    eapply md_fence.
    eapply md_syscall.
    eapply md_choose.
    eapply sim_val_refl.
    eapply sim_seq_inst_opt.
    eapply block_d_dec. eapply block_d_fix.
    ss.
  Qed.



  Theorem RRfwd_match_state
          p src tgt
          src_c tgt_c
          m
          (ALG: tgt_c = RRfwd_opt_alg src_c)
          (SRC: src = SeqState.mk (lang _) (eval_lang src_c) m)
          (TGT: tgt = SeqState.mk (lang _) (eval_lang tgt_c) m)
    :
      match_state p src tgt.
  Proof.
    econs; ss; eauto.
    - eapply Opt4.opt_match_code4; eauto.
    - eapply md_bot.
  Qed.



  Theorem RRfwd_sim
    src tgt
    src_c tgt_c
    (ALG: tgt_c = RRfwd_opt_alg src_c)
    (SRC: src = eval_lang src_c)
    (TGT: tgt = eval_lang tgt_c)
  :
    sim_seq_itree sim_val src tgt.
  Proof.
    clarify.
    unfold sim_seq_itree. ii. eapply match_state_sim. eapply RRfwd_match_state; eauto.
  Qed.

End PROOF.
