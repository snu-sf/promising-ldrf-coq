Set Implicit Arguments.

Require Import RelationClasses.

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

Require Import ITreeLang.

Require Import DeadStoreElim.
Require Import DeadStoreElimProof1.



Section MATCH.

  Ltac dest_loc l1 l2 :=
    destruct (Loc.eqb l1 l2) eqn:LOC;
    [rewrite Loc.eqb_eq in LOC; clarify; try rewrite Loc.eqb_refl; ss |
     hexploit LOC; intros DIFFL; rewrite Loc.eqb_sym in LOC; try rewrite LOC; apply Loc.eqb_neq in DIFFL; ss].


  Let O2: Opt2.t := DSE_opt2.

  Let bot := Opt2.bot O2.
  Let init := Opt2.bot2 O2.
  Let data_meet := @meet2 O2.
  Let data_le := @le2 O2.
  Let inst_gd := @inst_gd O2.
  Let GD := GD O2.


  Definition to_deferred0: Three -> Flag.t :=
    fun t =>
      match t with
      | none
      | half => false
      | full => true
      end.

  Definition to_deferred: GD -> Flags.t :=
    fun data => (fun l => to_deferred0 (data l)).

  Lemma to_deferred0_bot: to_deferred0 (Opt2.bot O2) = false.
  Proof. ss. Qed.

  Lemma to_deferred_bot: to_deferred (Opt2.bot2 O2) = Flags.bot.
  Proof. ss. Qed.

  Lemma to_deferred0_mon: forall mp0 mp1 (LE: le mp0 mp1), Flag.le (to_deferred0 mp0) (to_deferred0 mp1).
  Proof. i. destruct mp0, mp1; ss. Qed.

  Lemma to_deferred_mon: forall mp0 mp1 (LE: data_le mp0 mp1), Flags.le (to_deferred mp0) (to_deferred mp1).
  Proof. ii. apply to_deferred0_mon. apply LE. Qed.


  Lemma to_deferred_na_sound:
    forall (i: Inst.t) mp src_m val
      (NA: is_na_inst i)
    ,
      Flags.le (to_deferred (inst_gd i mp))
               (Flags.join (to_deferred mp) (update_mem_na val i src_m).(SeqMemory.flags)).
  Proof.
    ii. destruct i; ss.
    all: unfold inst_gd, Opt2.inst_gd, mk_global, to_deferred, Flags.join; ss.
    1,2,6,7: apply Flag.join_ge_l.
    - rewrite update_load_ord1; auto. 2: destruct ord; ss. dest_loc rhs loc. apply Flag.join_ge_l.
    - rewrite update_store_ord1; auto. dest_loc lhs loc.
      + unfold Flags.update. rewrite Loc.eq_dec_eq. destruct (to_deferred0 (mp loc)); ss.
      + apply Flag.join_ge_l.
    - des.
      + rewrite update_read_ord1; auto. dest_loc loc0 loc.
        hexploit (ord_inv2 ordw); i; des.
        * rewrite update_store_ord1; auto. rewrite Loc.eqb_sym; rewrite LOC. apply Flag.join_ge_l.
        * rewrite update_store_ord2; auto. rewrite Loc.eqb_sym; rewrite LOC. apply Flag.join_ge_l.
        * rewrite update_store_ord3; auto. rewrite Loc.eqb_sym; rewrite LOC.
          etrans. 2: apply Flag.join_ge_l. apply to_deferred0_mon. apply rel_flag_le.
      + rewrite update_store_ord1; auto. hexploit (ord_inv1' ordr); i; des.
        * rewrite update_read_ord1; auto. dest_loc loc0 loc. apply Flag.join_ge_l.
        * rewrite update_read_ord2; auto. dest_loc loc0 loc.
          etrans. 2: apply Flag.join_ge_l. apply to_deferred0_mon. apply acq_flag_le.
  Qed.



  Definition match_cell (data: Three) (sv tv: Const.t) (sf tf: Flag.t) :=
    match data with
    | none =>
      (sv = tv) /\ (sf = tf)
    | half =>
      (sf = false) -> ((sv = tv) /\ (sf = tf))
    | full =>
      True
    end.

  Definition match_mem (data: GD) (sm tm: SeqMemory.t) :=
    forall l, match_cell (data l)
                    (sm.(SeqMemory.value_map) l) (tm.(SeqMemory.value_map) l)
                    (sm.(SeqMemory.flags) l) (tm.(SeqMemory.flags) l).

  Lemma mcell_refl:
    forall d v f, match_cell d v v f f.
  Proof. i. unfold match_cell. des_ifs. Qed.

  Lemma mm_refl:
    forall d m, match_mem d m m.
  Proof. unfold match_mem. i. apply mcell_refl. Qed.


  Lemma mcell_bot:
    forall sv tv sf tf (MCELL: match_cell bot sv tv sf tf), (sv = tv) /\ (sf = tf).
  Proof.
    ii. unfold match_cell in MCELL. ss.
  Qed.

  Lemma mm_bot: forall sm tm (MM: match_mem init sm tm), sm = tm.
  Proof.
    i. unfold match_mem in MM. unfold match_cell in MM.
    destruct sm, tm. f_equal; extensionality l; specialize MM with l; ss; des; auto.
  Qed.


  Lemma mcell_mon:
    forall sv tv sf tf d0 d1
      (LE: le d0 d1)
      (MCELL: match_cell d0 sv tv sf tf)
    ,
      match_cell d1 sv tv sf tf.
  Proof.
    i. unfold match_cell in *. des_ifs.
  Qed.

  Lemma mm_mon:
    forall sm tm mp0 mp1
      (LE: data_le mp0 mp1)
      (MM: match_mem mp0 sm tm)
    ,
      match_mem mp1 sm tm.
  Proof.
    i. unfold match_mem in *. i. eapply mcell_mon; eauto. eapply LE.
  Qed.


  Lemma mm_na:
    forall (i: Inst.t) data sm tm
      (MM: match_mem (inst_gd i data) sm tm)
      (NA: is_na_inst i)
      val usm utm
      (USM: usm = update_mem_na val i sm)
      (UTM: utm = update_mem_na val i tm)
    ,
      match_mem data usm utm.
  Proof.
    i. clarify. unfold inst_gd, Opt2.inst_gd, mk_global in MM. destruct i; ss; clarify.
    - hexploit (ord_inv1 ord); i. des.
      2: destruct ord; ss.
      rewrite update_load_ord1f in MM; auto.
      eapply mm_mon. 2: eapply MM. ii. dest_loc rhs p. refl.
    - hexploit (ord_inv2 ord); i. des.
      2,3: destruct ord; ss.
      rewrite update_store_ord1f in MM; auto.
      ii. ss. unfold ValueMap.write, Flags.update. dest_loc lhs l.
      + rewrite ! Loc.eq_dec_eq. apply mcell_refl.
      + rewrite ! Loc.eq_dec_neq; auto. unfold match_mem in MM. specialize MM with l.
        rewrite Loc.eqb_sym in LOC. rewrite LOC in MM. auto.
    - des.
      + hexploit (ord_inv1' ordr); i. des.
        2:{ destruct ordr; ss. }
        rewrite update_read_ord1f in MM; auto.
        eapply mm_mon. 2: eapply MM. ii. dest_loc loc p. rewrite Loc.eqb_sym in LOC.
        hexploit (ord_inv2 ordw); i. des.
        * rewrite update_store_ord1; auto. rewrite LOC. refl.
        * rewrite update_store_ord2; auto. rewrite LOC. refl.
        * rewrite update_store_ord3; auto. rewrite LOC. apply rel_flag_le.
      + hexploit (ord_inv1' ordr); i. des.
        * rewrite update_read_ord1f in MM; auto. ii. unfold match_mem in MM. specialize MM with l.
          rewrite update_store_ord1 in MM; auto. dest_loc loc l. unfold match_cell. des_ifs.
        * rewrite update_read_ord2f in MM; auto. ii. unfold match_mem in MM. specialize MM with l.
          rewrite update_store_ord1 in MM; auto. unfold match_cell. dest_loc loc l; des_ifs.
  Qed.

  Lemma mm_load_same:
    forall lhs rhs ord mp src_m tgt_m
      (MM: match_mem (inst_gd (Inst.load lhs rhs ord) mp) src_m tgt_m)
    ,
      SeqMemory.read rhs src_m = SeqMemory.read rhs tgt_m.
  Proof.
    i. unfold inst_gd, Opt2.inst_gd, mk_global, match_mem in MM. specialize MM with rhs. ss.
    hexploit (ord_inv1 ord); i. des.
    - rewrite update_load_ord1 in MM; auto. rewrite Loc.eqb_refl in MM. ss. des; auto.
    - rewrite update_load_ord2 in MM; auto. rewrite Loc.eqb_refl in MM. ss. des; auto.
  Qed.

  Lemma mm_read_same:
    forall lhs loc rmw ordr ordw mp src_m tgt_m
      (MM: match_mem (inst_gd (Inst.update lhs loc rmw ordr ordw) mp) src_m tgt_m)
    ,
      SeqMemory.read loc src_m = SeqMemory.read loc tgt_m.
  Proof.
    i. unfold inst_gd, Opt2.inst_gd, mk_global, match_mem in MM. specialize MM with loc. ss.
    hexploit (ord_inv1' ordr); i. des.
    - rewrite update_read_ord1 in MM; auto. rewrite Loc.eqb_refl in MM. ss. des; auto.
    - rewrite update_read_ord2 in MM; auto. rewrite Loc.eqb_refl in MM. ss. des; auto.
  Qed.


  Lemma loc_eqb_is_dec:
    forall a b, Loc.eqb a b = LocSet.Facts.eq_dec a b.
  Proof.
    i. dest_loc a b; auto.
    - unfold proj_sumbool. rewrite Loc.eq_dec_eq; auto.
    - unfold proj_sumbool. rewrite Loc.eq_dec_neq; auto.
  Qed.

  Ltac unfold_flags := unfold Flags.update, Flags.add, Flags.sub, Flags.sub_opt, Flags.meet, Flags.join, Flags.minus.
  Ltac unfold_many := unfold_flags; unfold ValueMap.write, ValueMap.acquire, Perms.acquired.

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
  Proof.
    i. subst ev. hexploit (ord_inv1 ord). i; des.
    { hexploit step_rlx; eauto. ss. destruct ord; ss. i; des.
      do 2 eexists. split; eauto.
      hexploit red_rlx_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ord; ss. i; des.
      hexploit red_rlx_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ord; ss. i; des.
      clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
      unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
      rewrite update_load_ord1f in *; auto. splits; ss.
      - econs; ss; eauto.
        { unfold match_mem in MM; specialize MM with rhs. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
          econs; ss; eauto; try refl.
          unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
        }
        { econs; eauto. refl. }
        { econs; eauto. ii. unfold to_deferred. destruct (Loc.eqb rhs loc); ss. refl. }
      - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
        unfold_many.
        ii. ss. unfold match_mem in MM; specialize MM with l. depgen MM. clear.
        rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs.
        i. ss. des. apply mcell_refl.
    }
    { hexploit step_acq; eauto. ss. i; des.
      do 2 eexists. split; eauto.
      hexploit red_acq_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
      hexploit red_acq_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
      clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
      unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
      rewrite update_load_ord2f in *; auto. splits; ss.
      - econs; ss; eauto.
        { unfold match_mem in MM; specialize MM with rhs. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
          econs; ss; eauto; try refl.
          unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
        }
        2:{ econs; eauto. refl. }
        { econs; eauto. ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc.
          rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
          des_ifs. ss. unfold match_cell in MM. des_ifs; des; ss.
          - rewrite flag_join_bot_r. rewrite MM0; refl.
          - destruct (SeqMemory.flags src_m loc) eqn:SRCF, (SeqMemory.flags tgt_m loc) eqn:TGTF; ss. hexploit MM; auto; i; des; clarify.
          - destruct (mp loc); ss.
        }
      - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
        unfold_many.
        ii. ss. unfold match_mem in MM; specialize MM with l. depgen MM. clear.
        rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss.
        1,2: apply mcell_refl.
        + eapply mcell_mon; eauto. apply acq_flag_le.
        + destruct (mp l) eqn:MPL; ss; des. all: split; auto. apply MM in H. des; auto.
    }
  Qed.

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
  Proof.
    i. subst ev. hexploit (ord_inv2 ord). i; des.
    { destruct ord; ss. }
    { hexploit step_rlx; eauto. ss. destruct ord; ss. i; des.
      do 2 eexists. split; eauto.
      hexploit red_rlx_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ord; ss. i; des.
      hexploit red_rlx_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ord; ss. i; des.
      clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
      unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
      rewrite update_store_ord2f in *; auto. splits; ss.
      - econs; ss; eauto.
        { unfold match_mem in MM; specialize MM with lhs. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
          econs; ss; eauto; try refl.
          unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
        }
        { econs; eauto. refl. }
        { econs; eauto. ii. unfold to_deferred. destruct (Loc.eqb lhs loc); ss. refl. }
      - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
        unfold_many.
        ii. ss. unfold match_mem in MM; specialize MM with l. depgen MM. clear.
        rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs.
        i. ss. des. apply mcell_refl.
    }
    { hexploit step_rel; eauto. ss. i; des.
      do 2 eexists. split; eauto.
      hexploit red_rel_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
      hexploit red_rel_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
      clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
      unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
      rewrite update_store_ord3f in *; auto. splits; ss.
      - econs; ss; eauto.
        { unfold match_mem in MM; specialize MM with lhs. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
          econs; ss; eauto; try refl.
          unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
        }
        { econs; eauto. refl. }
        { econs; eauto.
          { i. unfold_many. unfold match_mem in MM. specialize MM with loc. rewrite Loc.eqb_sym in MM. rewrite loc_eqb_is_dec in MM.
            des_ifs; ss. refl. unfold to_deferred in UNDEFERRED. destruct (mp loc); ss.
            - des. rewrite MM. refl.
            - des. rewrite MM. refl.
          }
          ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc.
          rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
          des_ifs. ss. unfold match_cell in MM. des_ifs; des; ss.
          - rewrite flag_join_bot_r. rewrite MM0. apply Flag.join_ge_l.
          - destruct (SeqMemory.flags src_m loc) eqn:SRCF, (SeqMemory.flags tgt_m loc) eqn:TGTF; ss. hexploit MM; auto; i; des; clarify.
          - destruct (mp loc); ss.
            destruct (SeqMemory.flags src_m loc) eqn:SRCF, (SeqMemory.flags tgt_m loc) eqn:TGTF; ss.
        }
      - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
        unfold_many.
        ii. ss. unfold match_mem in MM; specialize MM with l. depgen MM. clear.
        rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss.
        1: apply mcell_refl.
        destruct (mp l) eqn:MPL; ss; des. all: split; auto.
    }
  Qed.

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
  Proof.
    i. subst ev. hexploit (ord_inv1' ordr). i; des.
    { destruct ordr; ss. }
    hexploit (ord_inv1 ordr). i; des.
    { hexploit step_rlx; eauto. ss. destruct ordr; ss. i; des.
      do 2 eexists. split; eauto.
      hexploit red_rlx_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr; ss. i; des.
      hexploit red_rlx_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr; ss. i; des.
      clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
      unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
      rewrite update_read_ord2f in *; auto. splits; ss.
      - econs; ss; eauto.
        { unfold match_mem in MM; specialize MM with loc. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
          econs; ss; eauto; try refl.
          unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
        }
        2:{ econs; eauto. refl. }
        { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc0.
          destruct (Loc.eqb loc loc0) eqn:LOC; ss.
          hexploit (ord_inv2 ordw). i; des.
          - rewrite update_store_ord1 in *; auto. rewrite LOC in *. apply to_deferred0_mon. apply acq_flag_le.
          - rewrite update_store_ord2 in *; auto. rewrite LOC in *. apply to_deferred0_mon. apply acq_flag_le.
          - rewrite update_store_ord3 in *; auto. rewrite LOC in *. apply to_deferred0_mon.
            etrans. eapply acq_flag_le. apply rel_flag_le.
        }
      - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
        unfold_many.
        ii. ss. unfold match_mem in MM; specialize MM with l. depgen MM. clear.
        rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss; des.
        + apply mcell_refl.
        + eapply mcell_mon; eauto. apply Loc.eqb_neq in n. rewrite Loc.eqb_sym in n. hexploit (ord_inv2 ordw). i; des.
          * rewrite update_store_ord1; auto. rewrite n. apply acq_flag_le.
          * rewrite update_store_ord2; auto. rewrite n. apply acq_flag_le.
          * rewrite update_store_ord3; auto. rewrite n. etrans. eapply acq_flag_le. apply rel_flag_le.
    }
    { hexploit step_acq; eauto. ss. i; des.
      do 2 eexists. split; eauto.
      hexploit red_acq_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
      hexploit red_acq_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
      clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
      unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
      rewrite update_read_ord2f in *; auto. splits; ss.
      - econs; ss; eauto.
        { unfold match_mem in MM; specialize MM with loc. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
          econs; ss; eauto; try refl.
          unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
        }
        2:{ econs; eauto. refl. }
        { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc0.
          unfold_flags. rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
          des_ifs. ss. apply Loc.eqb_neq in n. rewrite Loc.eqb_sym in n. rename n into LOC.
          hexploit (ord_inv2 ordw). i; des.
          - rewrite update_store_ord1 in *; auto. rewrite LOC in *. destruct (mp loc0) eqn:MPL; ss; des.
            + rewrite flag_join_bot_r. rewrite MM0. refl.
            + rewrite flag_join_bot_r. match goal with | [|- _ (Flag.le ?a ?b)] => destruct a; destruct b; ss end. hexploit MM; auto; i; des; clarify.
            + rewrite flag_join_bot_r. match goal with | [|- _ (Flag.le ?a ?b)] => destruct a; destruct b; ss end. hexploit MM; auto; i; des; clarify.
          - rewrite update_store_ord2 in *; auto. rewrite LOC in *. destruct (mp loc0) eqn:MPL; ss; des.
            + rewrite flag_join_bot_r. rewrite MM0. refl.
            + rewrite flag_join_bot_r. match goal with | [|- _ (Flag.le ?a ?b)] => destruct a; destruct b; ss end. hexploit MM; auto; i; des; clarify.
            + rewrite flag_join_bot_r. match goal with | [|- _ (Flag.le ?a ?b)] => destruct a; destruct b; ss end. hexploit MM; auto; i; des; clarify.
          - rewrite update_store_ord3 in *; auto. rewrite LOC in *. destruct (mp loc0) eqn:MPL; ss; des.
            + rewrite flag_join_bot_r. rewrite MM0. refl.
            + rewrite flag_join_bot_r. rewrite MM0. refl.
            + rewrite flag_join_bot_r. match goal with | [|- _ (Flag.le ?a ?b)] => destruct a; destruct b; ss end. hexploit MM; auto; i; des; clarify.
        }
      - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
        unfold_many.
        ii. ss. unfold match_mem in MM; specialize MM with l. depgen MM. clear.
        rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss; des.
        1,2: apply mcell_refl.
        + eapply mcell_mon; eauto. apply Loc.eqb_neq in n. rewrite Loc.eqb_sym in n. hexploit (ord_inv2 ordw). i; des.
          * rewrite update_store_ord1; auto. rewrite n. apply acq_flag_le.
          * rewrite update_store_ord2; auto. rewrite n. apply acq_flag_le.
          * rewrite update_store_ord3; auto. rewrite n. etrans. eapply acq_flag_le. apply rel_flag_le.
        + apply Loc.eqb_neq in n. rewrite Loc.eqb_sym in n. hexploit (ord_inv2 ordw). i; des.
          * rewrite update_store_ord1 in *; auto. rewrite n in *. destruct (mp l) eqn:MPL; ss; i; des; auto. apply MM in H0; des; auto.
          * rewrite update_store_ord2 in *; auto. rewrite n in *. destruct (mp l) eqn:MPL; ss; i; des; auto. apply MM in H0; des; auto.
          * rewrite update_store_ord3 in *; auto. rewrite n in *. destruct (mp l) eqn:MPL; ss; i; des; auto.
    }
  Qed.

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
  Proof.
    i. subst ev. hexploit (ord_inv1' ordr). i; des.
    { destruct ordr; ss. }
    hexploit (ord_inv1 ordr). i; des.
    { hexploit (ord_inv2 ordw). i; des.
      { apply andb_prop in ATOMIC. des. destruct ordw; ss. }
      { hexploit step_rlx; eauto. ss. destruct ordr; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_rlx_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr; ss. destruct ordw; ss. i; des.
        hexploit red_rlx_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr; ss. destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_read_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { unfold match_mem in MM; specialize MM with loc. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
            econs; ss; eauto; try refl.
            unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
          }
          2:{ econs; eauto. refl. }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc0.
            destruct (Loc.eqb loc loc0) eqn:LOC; ss.
            rewrite update_store_ord2 in *; auto. rewrite LOC in *; ss.
            apply to_deferred0_mon. apply acq_flag_le.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_store_ord2 in *; auto. depgen MM. clear.
          rewrite Loc.eqb_sym. rewrite ! loc_eqb_is_dec. des_ifs; i; ss; des.
          + apply mcell_refl.
          + eapply mcell_mon; eauto. apply acq_flag_le.
      }
      { hexploit step_rel; eauto. ss. destruct ordr; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_rel_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr; ss. i; des.
        hexploit red_rel_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_read_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { unfold match_mem in MM; specialize MM with loc. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
            econs; ss; eauto; try refl.
            unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
          }
          { econs; eauto. refl. }
          { econs; eauto.
            { i. unfold_many. unfold match_mem in MM. specialize MM with loc0.
              rewrite update_store_ord3 in *; auto.
              rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in MM. depgen UNDEFERRED. depgen MM.
              clear. des_ifs; i; ss. refl. unfold to_deferred in UNDEFERRED.
              destruct (mp loc0) eqn:MPL; ss; des.
              - rewrite MM; refl.
              - rewrite MM; refl.
            }
            ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc0.
            rewrite update_store_ord3 in *; auto.
            rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
            des_ifs. ss. destruct (mp loc0) eqn:MPL; ss; des.
            - rewrite MM0. refl.
            - rewrite MM0. refl.
            - destruct (SeqMemory.flags src_m loc0), (SeqMemory.flags tgt_m loc0); ss.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_store_ord3 in *; auto.
          depgen MM. clear. rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss.
          1: apply mcell_refl.
          destruct (mp l) eqn:MPL; ss; des. all: split; auto.
      }
    }
    { hexploit (ord_inv2 ordw). i; des.
      { apply andb_prop in ATOMIC. des. destruct ordw; ss. }
      { hexploit step_acq; eauto. ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_acq_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordw; ss. i; des.
        hexploit red_acq_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_read_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { unfold match_mem in MM; specialize MM with loc. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
            econs; ss; eauto; try refl.
            unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
          }
          2:{ econs; eauto. refl. }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc0.
            unfold_flags. rewrite update_store_ord2 in *; auto.
            rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
            des_ifs. ss. destruct (mp loc0) eqn:MPL; ss; des; auto.
            all: rewrite flag_join_bot_r.
            1: rewrite MM0; refl.
            all: match goal with | [|- _ (_ ?a ?b)] => destruct a; destruct b; ss; auto end; hexploit MM; auto; i; des; auto.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_store_ord2 in *; auto.
          depgen MM. clear. rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss; des.
          1,2: apply mcell_refl.
          + eapply mcell_mon; eauto. apply acq_flag_le.
          + destruct (mp l) eqn:MPL; ss; i; des; auto. apply MM in H; des; auto.
      }
      { hexploit step_acq_rel; eauto. ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_acq_rel_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
        hexploit red_acq_rel_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0. inv EVACC; inv EVACC0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_read_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { unfold match_mem in MM; specialize MM with loc. rewrite Loc.eqb_refl in MM. ss; des. rewrite MM; rewrite MM0.
            econs; ss; eauto; try refl.
            unfold to_deferred. rewrite Loc.eqb_refl. ss. rewrite flag_join_bot_r. refl.
          }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc0.
            unfold_flags. rewrite update_store_ord3 in *; auto.
            rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
            des_ifs. ss. destruct (mp loc0) eqn:MPL; ss; des; auto.
            all: rewrite flag_join_bot_r.
            1,2: rewrite MM0; refl.
            match goal with | [|- _ (_ ?a ?b)] => destruct a; destruct b; ss; auto end; hexploit MM; auto; i; des; auto.
          }
          { econs; eauto.
            { i. unfold_many. unfold match_mem in MM. specialize MM with loc0.
              rewrite update_store_ord3 in *; auto.
              rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in MM. depgen UNDEFERRED. depgen MM.
              clear. des_ifs; i; ss. 1,2,4: refl. unfold to_deferred in UNDEFERRED.
              destruct (mp loc0) eqn:MPL; ss; des.
              - rewrite MM; refl.
              - rewrite MM; refl.
            }
            ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc0.
            instantiate (1:=(to_deferred mp)). unfold to_deferred.
            rewrite update_store_ord3 in *; auto.
            rewrite Loc.eqb_sym in *. rewrite loc_eqb_is_dec in *. depgen MM. clear; i.
            des_ifs; ss. refl. destruct (mp loc0) eqn:MPL; ss; des.
            - rewrite MM0. refl.
            - rewrite MM0. refl.
            - destruct (SeqMemory.flags src_m loc0), (SeqMemory.flags tgt_m loc0); ss.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_store_ord3 in *; auto.
          depgen MM. clear. rewrite Loc.eqb_sym. rewrite loc_eqb_is_dec. des_ifs; i; ss; des.
          1,2: apply mcell_refl.
          + destruct (mp l) eqn:MPL; ss; i; des; auto.
          + destruct (mp l) eqn:MPL; ss; i; des; auto.
      }
    }
  Qed.

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
  Proof.
    i. subst ev. hexploit (ord_inv3 ordr). i; des.
    { hexploit (ord_inv3' ordw). i; des.
      { hexploit step_rlx2; eauto. ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_rlx2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        hexploit red_rlx2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_fence_r_ord1f in *; auto. splits; ss.
        - econs; ss; eauto.
          { econs; eauto. refl. }
          { econs; eauto. refl. }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc.
            rewrite update_fence_w_ord1 in *; auto. refl.
          }
        - destruct mem_src, mem_tgt.
          ii. ss. unfold match_mem in MM; specialize MM with l. ss.
          rewrite update_fence_w_ord1 in *; auto.
      }
      { hexploit step_rel2; eauto. ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_rel2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        hexploit red_rel2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_fence_r_ord1f in *; auto. splits; ss.
        - econs; ss; eauto.
          { econs; eauto. refl. }
          { econs; eauto. refl. }
          { econs; eauto.
            { i. unfold match_mem in MM. specialize MM with loc.
              rewrite update_fence_w_ord2 in *; auto.
              depgen UNDEFERRED. depgen MM.
              clear. i; ss. unfold to_deferred in UNDEFERRED.
              destruct (mp loc) eqn:MPL; ss; des.
              - rewrite MM; refl.
              - rewrite MM; refl.
            }
            ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc.
            rewrite update_fence_w_ord2 in *; auto. depgen MM. clear; i.
            destruct (mp loc) eqn:MPL; ss; des.
            - rewrite MM0. refl.
            - rewrite MM0. refl.
            - destruct (SeqMemory.flags src_m loc), (SeqMemory.flags tgt_m loc); ss.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_fence_w_ord2 in *; auto.
          depgen MM. clear. i; ss.
          destruct (mp l) eqn:MPL; ss; des. all: split; auto.
      }
      { hexploit step_acq_rel2; eauto. ss. destruct ordw; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_acq_rel2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. 1,2: destruct ordw; ss. i; des.
        hexploit red_acq_rel2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. 1,2: destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_fence_r_ord1f in *; auto. splits; ss.
        - econs; ss; eauto.
          { econs; eauto. refl. }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc.
            unfold_flags. rewrite update_fence_w_ord3 in *; auto. depgen MM. clear; i.
            destruct (mp loc); ss; des. all: rewrite flag_join_bot_r.
            all: rewrite MM0; refl.
          }
          { econs; eauto.
            { i. unfold_many. unfold match_mem in MM. specialize MM with loc.
              rewrite update_fence_w_ord3 in *; auto. depgen UNDEFERRED. depgen MM. clear; i.
              unfold to_deferred in *. destruct (mp loc); ss; des.
              all: rewrite MM; refl.
            }
            ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc.
            instantiate (1:=(to_deferred mp)). unfold to_deferred.
            rewrite update_fence_w_ord3 in *; auto. depgen MM. clear; i.
            destruct (mp loc) eqn:MPL; ss; des. all: rewrite MM0; refl.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_fence_w_ord3 in *; auto.
          depgen MM. clear; i. destruct (mp l) eqn:MPL; ss; des. all: split; auto. all: rewrite MM; refl.
      }
    }
    { hexploit (ord_inv3' ordw). i; des.
      { hexploit step_acq2; eauto. ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_acq2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        hexploit red_acq2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. destruct ordr, ordw; ss. destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_fence_r_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { econs; eauto. refl. }
          2:{ econs; eauto. refl. }
          { econs; eauto. unfold to_deferred. ii. unfold_flags. unfold match_mem in MM; specialize MM with loc.
            rewrite update_fence_w_ord1 in *; auto. depgen MM. clear; i.
            destruct (mp loc); ss; des. all: rewrite flag_join_bot_r. all: try by (rewrite MM0; refl).
            all: match goal with | [|- _ (_ ?a ?b)] => destruct a, b; ss end.
            all: hexploit MM; auto; i; des; clarify.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          ii. ss. unfold_many. unfold match_mem in MM; specialize MM with l.
          rewrite update_fence_w_ord1 in *; auto. depgen MM. clear; i.
          destruct (mp l); ss; des.
          + rewrite MM, MM0. split; refl.
          + i. apply MM in H; des; auto. rewrite H, H0. auto.
      }
      { hexploit step_acq_rel2; eauto. ss. destruct ordw; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_acq_rel2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. 1,2: destruct ordw; ss. i; des.
        hexploit red_acq_rel2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. 1,2: destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_fence_r_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { econs; eauto. refl. }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc.
            unfold_flags. rewrite update_fence_w_ord2 in *; auto. depgen MM. clear; i.
            destruct (mp loc); ss; des. all: rewrite flag_join_bot_r.
            all: try (rewrite MM0; refl).
            destruct (SeqMemory.flags src_m loc) eqn:SMF, (SeqMemory.flags tgt_m loc) eqn: TMF; ss. hexploit MM; auto; i; des; clarify.
          }
          { econs; eauto.
            { i. unfold_many. unfold match_mem in MM. specialize MM with loc.
              rewrite update_fence_w_ord2 in *; auto. depgen UNDEFERRED. depgen MM. clear; i.
              unfold to_deferred in *. destruct (mp loc); ss; des.
              all: rewrite MM; refl.
            }
            ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc.
            rewrite update_fence_w_ord2 in *; auto.
            instantiate (1:=(to_deferred mp)). unfold to_deferred.
            depgen MM. clear; i.
            destruct (mp loc) eqn:MPL; ss; des. all: try (rewrite MM0; refl).
            destruct (SeqMemory.flags src_m loc) eqn:SMF, (SeqMemory.flags tgt_m loc) eqn: TMF; ss.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_fence_w_ord2 in *; auto.
          depgen MM. clear; i. destruct (mp l) eqn:MPL; ss; des. all: split; auto. all: rewrite MM; refl.
      }
      { hexploit step_acq_rel2; eauto. ss. destruct ordw; ss. destruct ordw; ss. i; des.
        do 2 eexists. split; eauto.
        hexploit red_acq_rel2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. 1,2: destruct ordw; ss. i; des.
        hexploit red_acq_rel2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. 1,2: destruct ordw; ss. i; des.
        clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
        unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
        rewrite update_fence_r_ord2f in *; auto. splits; ss.
        - econs; ss; eauto.
          { econs; eauto. refl. }
          { econs; eauto. ii. unfold to_deferred. unfold match_mem in MM. specialize MM with loc.
            unfold_flags. rewrite update_fence_w_ord3 in *; auto. depgen MM. clear; i.
            destruct (mp loc); ss; des. all: rewrite flag_join_bot_r.
            all: rewrite MM0; refl.
          }
          { econs; eauto.
            { i. unfold_many. unfold match_mem in MM. specialize MM with loc.
              rewrite update_fence_w_ord3 in *; auto. depgen UNDEFERRED. depgen MM. clear; i.
              unfold to_deferred in *. destruct (mp loc); ss; des.
              all: rewrite MM; refl.
            }
            ii. unfold to_deferred. unfold_flags. unfold match_mem in MM. specialize MM with loc.
            instantiate (1:=(to_deferred mp)). unfold to_deferred.
            rewrite update_fence_w_ord3 in *; auto. depgen MM. clear; i.
            destruct (mp loc) eqn:MPL; ss; des. all: rewrite MM0; refl.
          }
        - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
          unfold_many.
          ii. ss. unfold match_mem in MM; specialize MM with l. rewrite update_fence_w_ord3 in *; auto.
          depgen MM. clear; i. destruct (mp l) eqn:MPL; ss; des. all: split; auto. all: rewrite MM; refl.
      }
    }
  Qed.

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
  Proof.
    i. subst ev.
    hexploit step_acq_rel2; eauto. ss. i; des.
    do 2 eexists. split; eauto.
    hexploit red_acq_rel2_full. 6: eapply STEP_TGT. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
    hexploit red_acq_rel2_full. 6: eapply STEP_SRC. 2: eapply ATOMIC. 1,2,3,4: ss. i; des.
    clear PERM0. subst i_src i_tgt p1. rewrite OO in OO0. inv OO0.
    unfold inst_gd, Opt2.inst_gd, mk_global in *. ss.
    apply mm_bot in MM. subst tgt_m. splits; ss.
    - econs; ss; eauto.
      { econs; eauto. refl. }
      { econs; eauto. ii. unfold to_deferred. unfold_flags. ss. rewrite flag_join_bot_r. refl. }
      { econs; eauto.
        { i. unfold_many. refl. }
        ii. refl.
      }
    - destruct mem_src, mem_tgt. ss. rewrite MEMV, MEMF, MEMV0, MEMF0; clear MEMV MEMF MEMV0 MEMF0.
      unfold_many.
      ii. ss. apply mcell_refl.
  Qed.

  Lemma mm_at:
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
  Proof.
    i. destruct ev; try by ss. all: inv EVENT.
    eapply mm_load_at; eauto. eapply mm_update_failure_at; eauto.
    eapply mm_store_at; eauto. eapply mm_update_success_at; eauto.
    eapply mm_fence; eauto. eapply mm_syscall; eauto.
  Qed.

End MATCH.
