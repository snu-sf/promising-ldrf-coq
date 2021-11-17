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

Require Import WRforwarding.
Require Import WRforwardingProof1.

Require Export ITreeLib.





Section MATCH.

  Ltac dest_loc l1 l2 :=
    destruct (Loc.eqb l1 l2) eqn:LOC;
    [rewrite Loc.eqb_eq in LOC; clarify; try rewrite Loc.eqb_refl; ss |
     hexploit LOC; intros DIFFL; rewrite Loc.eqb_sym in LOC; try rewrite LOC; apply Loc.eqb_neq in DIFFL; ss].


  Let O4 := WRfwd_opt4.
  Let inst_d := WRfwd_inst.
  Let inst_gd := @inst_gd WRfwd_opt4.
  Let le2 := @le2 WRfwd_opt4.
  Let GD := GD WRfwd_opt4.

  Definition match_data : GD -> Perms.t -> SeqMemory.t -> lenv -> Prop :=
    fun mp p m _ =>
      forall l, match (mp l) with
           | Some (v, false) =>
             (p l = Perm.high) /\ (Const.le v (SeqMemory.read l m))
           | Some (v, true) =>
             (p l = Perm.high) -> (Const.le v (SeqMemory.read l m))
           | _ => True
           end.


  Lemma md_mon: forall d1 d2 p m l (LE: le2 d1 d2) (MD: match_data d2 p m l), match_data d1 p m l.
  Proof.
    i. unfold match_data in *. i.
    unfold le2, Opt4.le2 in LE. ss. specialize LE with l0. specialize MD with l0.
    unfold Opt4.le in LE. ss. unfold le in LE.
    des_ifs; ss; i; des; clarify; eauto.
  Qed.

  Lemma md_bot: forall p m le, match_data (fun _: Loc.t => bot) p m le.
  Proof.
    ii. ss.
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
    ss.
  Qed.


  Lemma md_load_na:
    forall mp p m le (MD: match_data mp p m le)
      x l ord (ORD: Ordering.le ord Ordering.na)
      val (VAL: Perm.le Perm.high (p l) -> Const.le val (SeqMemory.read l m))
    ,
      match_data (inst_gd (Inst.load x l ord) mp) p m (update x val le).
  Proof.
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite WRfwd_read_ord1f; auto.
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
    i. clarify. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    hexploit (ord_inv1 ord). i. des.
    { destruct ord; ss. }
    - rewrite WRfwd_read_ord2f; auto.
      unfold match_data in *. i; ss.
      dest_loc l0 l.
      specialize MD with l0.
      hexploit red_rlx. 5,6: eauto. all: ss; auto.
      { destruct ord; ss. }
      eauto.
      i; des. rewrite <- ! MEMV. rewrite <- ! PERM. apply MD.
    - rewrite WRfwd_read_ord3f; auto.
      unfold match_data in *. i; ss.
      dest_loc l0 l.
      specialize MD with l0.
      hexploit red_acq. 5,6: eauto. all: ss; auto.
      i; des. hexploit H0; clear H0; eauto. i; des.
      destruct (mp l0) eqn: MPL; auto. destruct p0 as [v b]. ss. destruct b; auto.
      des. rewrite MD in ACQPERM. ss. split; auto.
      rewrite ACQMEMV; clear ACQMEMV. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
      rewrite MD. destruct (p_acq l0); ss.
  Qed.

  Lemma md_store_na:
    forall mp p m le (MD: match_data mp p m le)
      x e ord (ORD: Ordering.le ord Ordering.na)
      (PERM : (p x) = Perm.high)
      eval (EVAL: denote_expr le e = eval)
    ,
      match_data (inst_gd (Inst.store x e ord) mp) p (SeqMemory.write x eval m) le.
  Proof.
    i. clarify. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    rewrite WRfwd_store_ord1f; auto.
    unfold match_data in *. i.
    dest_loc x l.
    - des_ifs. split; auto. unfold ValueMap.write. rewrite Loc.eq_dec_eq.
      unfold Two_new in Heq. clarify. refl.
    - specialize MD with l. unfold ValueMap.write.
      rewrite Loc.eqb_sym in LOC; rewrite Loc.eqb_neq in LOC. rewrite Loc.eq_dec_neq; eauto.
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
    i. clarify. ss. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
    hexploit (ord_inv2' ord). i. des.
    { destruct ord; ss. }
    - rewrite WRfwd_store_ord2f; auto.
      rewrite WRfwd_write_ord1f; auto.
      2:{ destruct ord; ss. }
      unfold match_data in *. i; ss.
      dest_loc l x. specialize MD with l.
      hexploit red_rlx. 5,6: eauto. all: ss; auto.
      { destruct ord; ss. }
      eauto. i; des. rewrite <- ! MEMV. rewrite <- ! PERM. auto.
    - rewrite WRfwd_store_ord2f; auto.
      rewrite WRfwd_write_ord2f; auto.
      unfold match_data in *. i; ss.
      dest_loc l x. specialize MD with l.
      hexploit red_rel. 5,6: eauto. all: ss; auto.
      i; des. hexploit H0; clear H0; eauto. i; des.
      destruct (mp l) eqn:MPL; ss. destruct p0 as [v b]. i.
      rewrite RELMEMV; clear RELMEMV.
      rewrite H0 in RELPERM. hexploit perm_meet_high. rewrite RELPERM; auto. i; des. 
      des_ifs; ss; des; auto.
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
      hexploit (ord_inv2 ordw). i. des.
      + rewrite WRfwd_write_ord1f; auto.
        unfold match_data in *. i.
        dest_loc l l0.
        rewrite WRfwd_read_ord1; eauto.
        apply MD.
      + rewrite WRfwd_write_ord2f; auto.
        unfold match_data in *. i.
        dest_loc l l0.
        rewrite WRfwd_read_ord1; eauto.
        unfold Two_set_flag. specialize MD with l0. destruct (mp l0) eqn:MPL; ss.
        destruct p0. destruct b; ss. des. eauto.
    - rewrite WRfwd_write_ord1f; auto.
      2:{ destruct ordw; ss. }
      hexploit (ord_inv1 ordr). i. des.
      + unfold match_data in *. i.
        dest_loc l l0.
        rewrite WRfwd_read_ord1; eauto.
        apply MD.
      + unfold match_data in *. i.
        dest_loc l l0.
        rewrite WRfwd_read_ord2; eauto.
        rewrite Loc.eqb_sym in LOC. rewrite LOC. apply MD.
      + unfold match_data in *. i.
        dest_loc l l0.
        rewrite WRfwd_read_ord3; eauto.
        rewrite Loc.eqb_sym in LOC. rewrite LOC.
        unfold Two_elim. specialize MD with l0. destruct (mp l0) eqn:MPL; ss.
        destruct p0. destruct b; ss.
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
    hexploit (ord_inv2 ordw). i. des.
    - rewrite WRfwd_write_ord1f; eauto.
      unfold match_data in *. i.
      dest_loc l0 l.
      hexploit (ord_inv1 ordr). i. des.
      { exfalso. destruct ordr; ss. }
      + rewrite WRfwd_read_ord2; eauto.
        rewrite LOC. specialize MD with l0.
        hexploit red_rlx. 5,6: eauto. all: ss; auto.
        { apply andb_true_intro. split; auto. }
        { destruct ordr; ss. }
        { destruct ordw; ss. }
        eauto. i; des. rewrite <- ! MEMV. rewrite <- ! PERM. auto.
      + rewrite WRfwd_read_ord3; eauto.
        rewrite LOC. specialize MD with l0. unfold Two_elim.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0. destruct b; ss. des.
        hexploit red_acq. 5,6: eauto. all: ss; auto.
        { apply andb_true_intro. split; auto. }
        { destruct ordw; ss. }
        i; des. hexploit H1; clear H1. eauto. i; des.
        rewrite MD in ACQPERM. ss. split; auto.
        rewrite ACQMEMV; clear ACQMEMV. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l0); ss.
    - rewrite WRfwd_write_ord2f; eauto.
      unfold match_data in *. i.
      dest_loc l0 l.
      hexploit (ord_inv1 ordr). i. des.
      { exfalso. destruct ordr; ss. }
      + rewrite WRfwd_read_ord2; eauto.
        unfold Two_set_flag.
        rewrite LOC. specialize MD with l0.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0. hexploit red_rel. 5,6: eauto. all: ss; auto.
        { apply andb_true_intro. split; auto. }
        { destruct ordr; ss. }
        i; des. hexploit H1; clear H1. eauto. i; des.
        rewrite RELMEMV; clear RELMEMV.
        rewrite H2 in RELPERM. hexploit perm_meet_high. rewrite RELPERM; auto. i; des. 
        destruct b; ss; des; auto.
      + rewrite WRfwd_read_ord3; eauto.
        unfold Two_set_flag, Two_elim.
        rewrite LOC. specialize MD with l0.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0. destruct b; ss. des.
        hexploit red_acq_rel. 5,6: eauto. all: ss; auto.
        { apply andb_true_intro. split; auto. }
        i; des. hexploit H1; clear H1. eauto. i; des.
        clear ACQFLAG MEMF1.
        rewrite MEMV1; clear MEMV1. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l0); ss.
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
    hexploit (ord_inv2 ordw). i. des.
    - rewrite WRfwd_write_ord1f; eauto.
      unfold match_data in *. i.
      dest_loc l0 l.
      hexploit (ord_inv1 ordr). i. des.
      { exfalso. destruct ordr; ss. }
      + rewrite WRfwd_read_ord2; eauto.
        rewrite LOC. specialize MD with l0.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0.
        hexploit red_rlx. 5,6: eauto. all: ss; auto.
        { destruct ordr; ss. }
        eauto. i; des. rewrite <- ! PERM. rewrite <- ! MEMV. auto.
      + rewrite WRfwd_read_ord3; eauto.
        rewrite LOC. specialize MD with l0. unfold Two_elim.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0. destruct b; auto.
        hexploit red_acq. 5,6: eauto. all: ss; auto.
        i; des. hexploit H1; clear H1. eauto. i; des.
        rewrite MD in ACQPERM. ss. split; auto.
        rewrite ACQMEMV; clear ACQMEMV. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l0); ss.
    - rewrite WRfwd_write_ord2f; eauto.
      unfold match_data in *. i.
      dest_loc l0 l.
      hexploit (ord_inv1 ordr). i. des.
      { exfalso. destruct ordr; ss. }
      + rewrite WRfwd_read_ord2; eauto.
        unfold Two_set_flag.
        rewrite LOC. specialize MD with l0.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0. i.
        hexploit red_rlx. 5,6: eauto. all: ss; auto.
        { destruct ordr; ss. }
        eauto. i; des. rewrite <- MEMV. rewrite H1 in PERM. destruct b; des; auto.
      + rewrite WRfwd_read_ord3; eauto.
        unfold Two_set_flag, Two_elim.
        rewrite LOC. specialize MD with l0.
        destruct (mp l0) eqn:MPL; ss.
        destruct p0. destruct b; ss. des.
        hexploit red_acq. 5,6: eauto. all: ss; auto.
        i; des. hexploit H1; clear H1. eauto. i; des.
        rewrite MD in ACQPERM. ss.
        rewrite ACQMEMV; clear ACQMEMV. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l0); ss.
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
    hexploit (ord_inv4 ordw). i. des.
    - rewrite WRfwd_fence_w_ord1f; eauto.
      unfold match_data in *. i.
      specialize MD with l.
      hexploit (ord_inv3 ordr). i. des.
      + rewrite WRfwd_fence_r_ord1; eauto.
        hexploit red_rlx2. 5,6: eauto. all: ss; auto.
        { apply Bool.orb_false_intro. destruct ordw; ss. destruct ordr; ss. }
        { destruct  ordw; ss. }
        i; des. subst m1. subst p1. auto.
      + rewrite WRfwd_fence_r_ord2; eauto.
        unfold Two_elim.
        destruct (mp l) eqn:MPL; ss.
        destruct p0. destruct b; ss. des.
        hexploit red_acq2. 5,6: eauto. all: ss; auto.
        { apply Bool.orb_true_intro. auto. }
        { destruct  ordw; ss. }
        i; des. eapply equal_f in ACQPERM. unfold Perms.join in ACQPERM. rewrite MD in ACQPERM. ss.
        split; auto. unfold SeqMemory.read. rewrite ACQMEMV.
        unfold Perms.acquired, ValueMap.acquire, ValueMap.read. rewrite MD. destruct (p_acq l); ss.
    - rewrite WRfwd_fence_w_ord2f; eauto.
      unfold match_data in *. i.
      specialize MD with l.
      hexploit (ord_inv3 ordr). i. des.
      + rewrite WRfwd_fence_r_ord1; eauto.
        destruct (mp l) eqn:MPL; ss.
        destruct p0. hexploit red_rel2. 5,6: eauto. all: ss; auto.
        { apply Bool.orb_false_intro. destruct ordw; ss. destruct ordr; ss. }
        { destruct  ordw; ss. }
        i; des. unfold SeqMemory.read. rewrite RELMEMV.
        eapply equal_f in RELPERM. unfold Perms.meet in RELPERM. rewrite H2 in RELPERM. hexploit perm_meet_high.
        rewrite RELPERM; auto. i; des. destruct b; des; auto.
      + rewrite WRfwd_fence_r_ord2; eauto.
        unfold Two_elim, Two_set_flag.
        destruct (mp l) eqn:MPL; ss.
        destruct p0. destruct b; ss. des. i.
        hexploit red_acq_rel2. 5,6: eauto. all: ss; auto.
        { apply Bool.orb_true_intro. right; auto. }
        { destruct ordw; ss. }
        i; des. clear ACQFLAG MEMF1.
        unfold SeqMemory.read. rewrite MEMV1; clear MEMV1. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l); ss.
    - rewrite WRfwd_fence_w_ord3f; eauto.
      unfold match_data in *. i.
      specialize MD with l.
      hexploit (ord_inv3 ordr). i. des.
      + rewrite WRfwd_fence_r_ord1; eauto.
        unfold Two_elim.
        destruct (mp l) eqn:MPL; ss.
        destruct p0. destruct b; ss. des.
        hexploit red_acq_rel2. 5,6: eauto. all: ss; auto.
        { apply Bool.orb_true_intro. left; auto. }
        { destruct ordw; ss. }
        i; des. clear ACQFLAG MEMF1.
        unfold SeqMemory.read. rewrite MEMV1; clear MEMV1. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l); ss.
      + rewrite WRfwd_fence_r_ord2; eauto.
        unfold Two_set_flag, Two_elim.
        destruct (mp l) eqn:MPL; ss.
        destruct p0. destruct b; ss. des. i.
        hexploit red_acq_rel2. 5,6: eauto. all: ss; auto.
        { apply Bool.orb_true_intro. left; auto. }
        { destruct ordw; ss. }
        i; des. clear ACQFLAG MEMF1.
        unfold SeqMemory.read. rewrite MEMV1; clear MEMV1. unfold Perms.acquired, ValueMap.acquire, ValueMap.read.
        rewrite MD. destruct (p_acq l); ss.
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
    i. unfold inst_gd, Opt4.inst_gd, inst_d, mk_global. ss.
  Qed.

  Lemma md_choose:
    forall mp p m le (MD: match_data mp p m le)
      x val,
      match_data (inst_gd (Inst.choose x) mp) p m (update x val le).
  Proof.
    ss.
  Qed.

End MATCH.



Section PROOF.

  Let O4 := WRfwd_opt4.
  Let inst_d := WRfwd_inst.
  Let inst_gd := @inst_gd WRfwd_opt4.
  Let le2 := @le2 WRfwd_opt4.
  Let GD := GD WRfwd_opt4.



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
    grind. rewrite denote_expr_val.
    clear OPT.
    dup MD.
    unfold match_data in MD. specialize MD with rhs.
    dup LE.
    unfold le2, Opt4.le2 in LE. ss. specialize LE with rhs. unfold Opt4.le in LE; ss.
    rewrite Heq in LE. ss. destruct (mp rhs) eqn:MPVAL; ss. destruct p0 as [c2 b2].
    destruct LE. subst t. rename H0 into CASE.
    destruct (p rhs) eqn:PERM.
    - (* no perm, read any value *)
      eapply sim_seq_na; ss; clarify.
      { apply partial_same_mem; auto. }
      { do 2 eexists. split.
        - econs; eauto. ss. eapply ILang.step_tau; ss. econs; ss.
        - ss.
      }
      ii. inv STEP_TGT. inv LANG. inv LOCAL.
      do 2 eexists. repeat split; try red; i.
      { econs 2.
        econs 1; eauto.
        rewrite bind_trigger. eapply ILang.step_read; eauto.
        econs. ss. i. rewrite PERM in H. simpl in H. discriminate H.
        ired.
        econs; eauto.
      }
      { econs 2; eauto. }
      eapply SIM; eauto.

    - eapply sim_seq_na; ss; clarify.
      { apply partial_same_mem; auto. }
      { do 2 eexists. split.
        - econs; eauto. ss. eapply ILang.step_tau; ss. econs; ss.
        - ss.
      }
      ii. inv STEP_TGT. inv LANG. inv LOCAL.
      do 2 eexists. repeat split; try red; i.
      { econs 2.
        econs 1; eauto.
        rewrite bind_trigger. eapply ILang.step_read; eauto.
        econs; eauto. i.
        { instantiate (1:=c2). destruct b2.
          - eapply MD; auto.
          - des; auto.
        }
        ired. econs; eauto.
      }
      { econs 2; eauto. }
      eapply SIM; eauto.
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



  Theorem WRfwd_match_state
          p src tgt
          src_c tgt_c
          m
          (ALG: tgt_c = WRfwd_opt_alg src_c)
          (SRC: src = SeqState.mk (lang _) (eval_lang src_c) m)
          (TGT: tgt = SeqState.mk (lang _) (eval_lang tgt_c) m)
    :
      match_state p src tgt.
  Proof.
    econs; ss; eauto.
    - eapply Opt4.opt_match_code4; eauto.
    - eapply md_bot.
  Qed.


  Theorem WRfwd_sim
    src tgt
    src_c tgt_c
    (ALG: tgt_c = WRfwd_opt_alg src_c)
    (SRC: src = eval_lang src_c)
    (TGT: tgt = eval_lang tgt_c)
  :
    sim_seq_itree sim_val src tgt.
  Proof.
    clarify.
    unfold sim_seq_itree. ii. eapply match_state_sim. eapply WRfwd_match_state; eauto.
  Qed.

End PROOF.
