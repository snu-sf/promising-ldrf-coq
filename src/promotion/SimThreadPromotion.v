Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Syntax.
Require Import Semantics.

Require Import PromiseConsistent.

Require Import Promotion.
Require Import SimCommon.
Require Import PromotionProgress.

Set Implicit Arguments.
Set Nested Proofs Allowed.


Module SimThreadPromotion.
  Import SimCommon.


  (* sim_state *)

  Inductive sim_state_synch (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_synch_intro
      (STMTS: st_tgt.(State.stmts) = promote_stmts l r st_src.(State.stmts))
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (REGR: st_tgt.(State.regs) r = val)
  .
  Hint Constructors sim_state_synch.

  Inductive sim_state_fa (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_fa_intro
      lhs addendum ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.fetch_add addendum) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  (Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (REGR: st_tgt.(State.regs) r = val + RegFile.eval_value st_src.(State.regs) addendum)
  .
  Hint Constructors sim_state_fa.

  Inductive sim_state_cas_success1 (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas1_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  Stmt.instr (Instr.assign r new) ::
                             Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1)))
                             :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (REGR: st_tgt.(State.regs) r = val)
      (SUCCESS: val = RegFile.eval_value st_src.(State.regs) old)
  .
  Hint Constructors sim_state_cas_success1.

  Inductive sim_state_cas_success2 (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas2_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (REGR: st_tgt.(State.regs) r = RegFile.eval_value st_src.(State.regs) new)
      (SUCCESS: val = RegFile.eval_value st_src.(State.regs) old)
  .
  Hint Constructors sim_state_cas_success2.

  Inductive sim_state_cas_fail (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas_fail_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: st_src.(State.stmts) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: st_tgt.(State.stmts) =
                  Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) st_src.(State.regs) st_tgt.(State.regs))
      (REGR: st_tgt.(State.regs) r = val)
      (FAIL: val <> RegFile.eval_value st_src.(State.regs) old)
  .
  Hint Constructors sim_state_cas_fail.

  Definition sim_state (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
    sim_state_synch l r val st_src st_tgt \/
    sim_state_fa l r val st_src st_tgt \/
    sim_state_cas_success1 l r val st_src st_tgt \/
    sim_state_cas_success2 l r val st_src st_tgt \/
    sim_state_cas_fail l r val st_src st_tgt
  .


  (* sim_thread *)

  Definition safe (l: Loc.t) (lc: Local.t) (mem: Memory.t): Prop :=
    forall from to val released
      (GET: Memory.get l to mem = Some (from, Message.full val (Some released))),
      View.le released lc.(Local.tview).(TView.cur).

  Inductive sim_thread (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      val
      (REGFREE: reg_free_stmts r e_src.(Thread.state).(State.stmts))
      (STATE: sim_state l r val e_src.(Thread.state) e_tgt.(Thread.state))
      (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
      (FULFILLABLE: fulfillable l e_src.(Thread.local).(Local.tview) e_src.(Thread.memory)
                                  e_src.(Thread.local).(Local.promises))
      (LATEST: exists from released,
          Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.memory) =
          Some (from, Message.full val released))
      (PROMISES: forall to, Memory.get l to e_src.(Thread.local).(Local.promises) = None)
      (SAFE: safe l e_src.(Thread.local) e_src.(Thread.memory))
  .
  Hint Constructors sim_thread.

  Inductive sim_thread_reserve (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_reserve_intro
      val
      (REGFREE: reg_free_stmts r e_src.(Thread.state).(State.stmts))
      (STATE: sim_state l r val e_src.(Thread.state) e_tgt.(Thread.state))
      (LOCAL: sim_local l e_src.(Thread.local) e_tgt.(Thread.local))
      (SC: sim_timemap l e_src.(Thread.sc) e_tgt.(Thread.sc))
      (MEMORY: sim_memory l e_src.(Thread.memory) e_tgt.(Thread.memory))
      (FULFILLABLE: fulfillable l e_src.(Thread.local).(Local.tview) e_src.(Thread.memory)
                                  e_src.(Thread.local).(Local.promises))
      (LATEST: exists from from' released,
          <<MEM: Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.memory) =
                 Some (from, Message.reserve)>> /\
          <<PROMISE: Memory.get l (Memory.max_ts l e_src.(Thread.memory)) e_src.(Thread.local).(Local.promises) =
                     Some (from, Message.reserve)>> /\
          <<LATEST: Memory.get l from e_src.(Thread.memory) =
                    Some (from', Message.full val released)>>)
      (PROMISES: forall to (TO: to <> Memory.max_ts l e_src.(Thread.memory)),
          Memory.get l to e_src.(Thread.local).(Local.promises) = None)
      (SAFE: safe l e_src.(Thread.local) e_src.(Thread.memory))
  .
  Hint Constructors sim_thread_reserve.


  Lemma step_sim_thread_reserve
        l r e1_src e_tgt
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (SIM1: sim_thread l r e1_src e_tgt):
    exists from to e2_src,
      <<STEP: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add)
                          e1_src e2_src>> /\
      <<SIM2: sim_thread_reserve l r e2_src e_tgt>>.
  Proof.
    destruct e1_src as [st1_src [tview1_src promises1_src] sc1_src mem1_src].
    destruct e_tgt as [st_tgt [tview_tgt promises_tgt] sc_tgt mem_tgt].
    inv SIM1. ss. des.
    dup WF1_SRC. inv WF1_SRC0. ss.
    clear TVIEW_WF TVIEW_CLOSED FINITE BOT RESERVE.
    exploit (@Memory.add_exists_max_ts mem1_src l (Time.incr (Memory.max_ts l mem1_src)) Message.reserve).
    { apply Time.incr_spec. }
    { econs. }
    i. des.
    exploit Memory.add_exists_le; eauto. i. des.
    assert (MAX: Memory.max_ts l mem2 = Time.incr (Memory.max_ts l mem1_src)).
    { exploit Memory.add_get0; try exact x0. i. des.
      exploit Memory.max_ts_spec; try exact GET0. i. des.
      inv MAX; ss.
      revert GET1. erewrite Memory.add_o; eauto. condtac; ss; try by des; ss.
      guardH o. i.
      exploit Memory.max_ts_spec; try exact GET1. i. des.
      specialize (Time.incr_spec (Memory.max_ts l mem1_src)). i.
      rewrite H in H0. timetac.
    }
    esplits.
    - econs 1. econs; ss. econs; eauto. econs 1; eauto. ss.
    - econs; s; eauto.
      + inv LOCAL. econs; ss.
        etrans; eauto. econs; i.
        * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
          { des. subst. ss. }
          { esplits; eauto. refl. }
        * erewrite Memory.add_o; eauto. condtac; ss.
          { des. subst. ss. }
          { esplits; eauto. refl. }
      + etrans; eauto. econs; i.
        * revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
          { des. subst. ss. }
          { esplits; eauto. refl. }
        * erewrite Memory.add_o; eauto. condtac; ss.
          { des. subst. ss. }
          { esplits; eauto. refl. }
      + ii. revert GETP.
        erewrite Memory.add_o; eauto. condtac; ss. i. guardH o.
        exploit FULFILLABLE; eauto. i. des. split; ss.
        unfold prev_released_le_loc in *.
        erewrite Memory.add_o; eauto. condtac; ss.
      + exploit Memory.add_get0; try exact x0. i. des.
        exploit Memory.add_get0; try exact x1. i. des.
        exploit Memory.add_get1; try exact LATEST; eauto. i.
        rewrite MAX. esplits; eauto.
      + i. rewrite MAX in *.
        erewrite Memory.add_o; eauto. condtac; ss.
        des. subst. ss.
      + ii. revert GET.
        erewrite Memory.add_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma step_reserve_sim_thread
        l r e1_src e_tgt
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (SIM1: sim_thread_reserve l r e1_src e_tgt):
    exists from to e2_src,
      <<STEP: Thread.step true (ThreadEvent.promise l from to Message.reserve Memory.op_kind_cancel)
                          e1_src e2_src>> /\
      <<SIM2: sim_thread l r e2_src e_tgt>>.
  Proof.
    destruct e1_src as [st1_src [tview1_src promises1_src] sc1_src mem1_src].
    destruct e_tgt as [st_tgt [tview_tgt promises_tgt] sc_tgt mem_tgt].
    inv SIM1. ss. des.
    dup WF1_SRC. inv WF1_SRC0. ss.
    clear TVIEW_WF TVIEW_CLOSED FINITE BOT RESERVE.
    exploit (@Memory.remove_exists promises1_src l from (Memory.max_ts l mem1_src) Message.reserve); ss.
    i. des.
    exploit Memory.remove_exists_le; eauto. i. des.
    assert (MAX: Memory.max_ts l mem0 = from).
    { exploit Memory.get_ts; try exact MEM. i. des.
      { rewrite x3 in *.
        inv CLOSED1_SRC. rewrite INHABITED in *. ss. }
      exploit Memory.remove_get0; try exact x1. i. des.
      exploit Memory.remove_get1; try exact LATEST; eauto. i. des.
      { subst. timetac. }
      exploit Memory.max_ts_spec; try exact GET2. i. des.
      inv MAX; ss.
      revert GET1. erewrite Memory.remove_o; eauto. condtac; ss.
      i. des; ss.
      exploit Memory.max_ts_spec; try exact GET1. i. des.
      exploit Memory.get_ts; try exact GET1. i. des.
      { subst. rewrite x4 in *. inv H. }
      exploit Memory.get_disjoint; [exact MEM|exact GET1|..]. i. des.
      { subst. rewrite x4 in *. congr. }
      exfalso.
      apply (x4 (Memory.max_ts l mem0)); econs; ss. refl.
    }
    esplits.
    - econs. econs; ss. econs; eauto.
    - econs; s; eauto.
      + inv LOCAL. econs; ss.
        etrans; eauto. econs; i.
        * revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
          esplits; eauto. refl.
        * erewrite Memory.remove_o; eauto. condtac; ss; try by des; ss.
          esplits; eauto. refl.
      + etrans; eauto. econs; i.
        * revert GET_SRC. erewrite Memory.remove_o; eauto. condtac; ss. i.
          esplits; eauto. refl.
        * erewrite Memory.remove_o; eauto. condtac; ss; try by des; ss.
          esplits; eauto. refl.
      + ii. revert GETP.
        erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
        exploit FULFILLABLE; eauto. i. des. split; ss.
        unfold prev_released_le_loc in *.
        erewrite Memory.remove_o; eauto. condtac; ss.
      + rewrite MAX.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst. rewrite a0 in *.
        exploit Memory.get_ts; try exact MEM. i. des; timetac.
        rewrite x2 in *.
        inv CLOSED1_SRC. rewrite INHABITED in MEM. ss.
      + i. erewrite Memory.remove_o; eauto. condtac; ss.
        apply PROMISES. des; ss.
      + ii. revert GET.
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma eq_loc_max_ts
        loc mem1 mem2
        (EQLOC: forall to, Memory.get loc to mem1 = Memory.get loc to mem2):
    Memory.max_ts loc mem1 = Memory.max_ts loc mem2.
  Proof.
    unfold Memory.max_ts.
    replace (mem1 loc) with (mem2 loc); ss.
    apply Cell.ext. eauto.
  Qed.

  Lemma sim_thread_promise_step
        l r e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (STEP_TGT: Thread.promise_step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_promise_step e_src e1_src e2_src>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
    inversion STEP_TGT. subst.
    destruct (Loc.eq_dec loc l).
    { subst. inv LOCAL; ss.
      esplits; [econs 1|]; eauto.
      inv SIM1. ss.
      exploit promise_loc; try exact PROMISE; try apply LOCAL; eauto. i. des.
      econs; ss; eauto.
      econs; ss; eauto; try apply LOCAL.
    }
    exploit promise_step; try exact LOCAL; try apply SIM1;
      try apply WF1_SRC; try apply WF1_TGT; eauto.
    i. des.
    destruct e1_src. ss.
    esplits.
    - econs 2. econs; eauto.
    - inv SIM1. inv STEP_SRC. ss.
      econs; eauto; ss; ii.
      + erewrite <- promise_eq_mem; eauto.
        erewrite <- eq_loc_max_ts; eauto.
        eapply promise_eq_mem; eauto.
      + erewrite <- promise_eq_promises; eauto.
      + erewrite <- promise_eq_mem in GET; eauto.
  Qed.

  Lemma promote_stmts_step
        l r stmt
        regs1_src stmts1_src
        e regs1_tgt stmts1_tgt st2_tgt
        (REGS1: RegFile.eq_except (RegSet.singleton r) regs1_src regs1_tgt)
        (STMTS1: stmts1_tgt = promote_stmts l r stmts1_src)
        (STMT: promote_stmt l r stmt = [stmt])
        (REGFREE: reg_free_stmt r stmt)
        (STEP_TGT: State.step e (State.mk regs1_tgt (stmt :: stmts1_tgt)) st2_tgt):
    exists st2_src,
      <<STEP_SRC: State.step e (State.mk regs1_src (stmt :: stmts1_src)) st2_src>> /\
      <<REGS2: RegFile.eq_except (RegSet.singleton r) st2_src.(State.regs) st2_tgt.(State.regs)>> /\
      <<STMTS2: st2_tgt.(State.stmts) = promote_stmts l r st2_src.(State.stmts)>>.
  Proof.
    subst. inv STEP_TGT.
    - inv REGFREE.
      exploit RegFile.eq_except_instr; eauto. i. des.
      esplits.
      + econs; eauto.
      + ss.
      + ss.
    - inv REGFREE.
      esplits.
      + econs; eauto.
      + ss.
      + s. rewrite promote_stmts_app.
        exploit RegFile.eq_except_expr; eauto. i. rewrite x0.
        repeat condtac; ss.
        * unfold promote_stmts. inv STMT.
          repeat rewrite H0. refl.
        * unfold promote_stmts. inv STMT.
          repeat rewrite H1. refl.
    - inv REGFREE.
      esplits.
      + econs; eauto.
      + ss.
      + s. rewrite promote_stmts_app.
        rewrite promote_stmts_cons.
        unfold promote_stmts. inv STMT. ss.
        repeat rewrite H0. refl.
  Qed.

  Lemma sim_thread_program_step
        l r e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.program_step e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_program_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
    destruct e1_src as [[regs1_src stmts1_src] lc1_src sc1_src mem1_src].
    destruct e1_tgt as [[regs1_tgt stmts1_tgt] lc1_tgt sc1_tgt mem1_tgt].
    dup SIM1. inv SIM0. ss.
    unfold sim_state in *. des; cycle 1.
    { (* fa *)
      inv STATE. ss. subst.
      inv STEP_TGT. inv STATE. inv INSTR.
      destruct e_tgt; ss; try by inv LOCAL0.
      exploit PromotionProgress.progress_read; try eapply LATEST; eauto.
      { destruct released; eauto using View.bot_spec. }
      i. des.
      exploit Local.read_step_future; eauto. i. des.
      exploit PromotionProgress.progress_write; try exact WF2; eauto.
      { inv STEP. ss. }
      { etrans; try eapply TVIEW_FUTURE.
        destruct released; try apply View.bot_spec.
        eapply SAFE; eauto. }
      i. des. esplits.
      - econs 2. econs; cycle 1.
        + econs 4; eauto.
        + econs. econs. ss.
      - ss.
      - inv LOCAL0. econs; ss; eauto.
        + inv REGFREE. ss.
        + left. econs; eauto. ss.
          unfold RegFun.find. rewrite REGR.
          apply RegFile.eq_except_add; ss.
        + etrans; eauto. symmetry. etrans; eauto.
        + etrans; eauto. symmetry. ss.
        + ii. inv STEP. inv LC0. ss. inv STEP0. ss.
          inv WRITE. inv PROMISE. revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          guardH o. guardH o0.
          destruct (Loc.eq_dec loc l); try by subst; congr.
          exploit FULFILLABLE; eauto. i. des. split.
          * unfold tview_released_le_loc in *.
            unfold TView.write_tview. ss.
            unfold LocFun.add. condtac; ss.
          * unfold prev_released_le_loc in *.
            erewrite Memory.add_o; eauto. condtac; ss.
            des. subst. ss.
        + ss. unfold RegFun.add. condtac; ss; eauto.
          { subst. inv REGFREE. inv H1. ss.
            symmetry in REGFREE.
            apply RegSet.disjoint_add in REGFREE. des.
            exfalso. apply REGFREE.
            eapply RegSet.Facts.singleton_2; ss. }
          unfold RegFun.find. rewrite REGR.
          inv STEP0. inv WRITE. inv PROMISE. ss.
          exploit Memory.add_get0; try exact MEM0. i. des.
          replace (Memory.max_ts l mem0) with (Time.incr (Memory.max_ts l mem1_src)); eauto.
          exploit Memory.max_ts_spec; try exact GET0. i. des. inv MAX; ss.
          revert GET1. erewrite Memory.add_o; eauto. condtac; ss; try by des.
          guardH o. i.
          exploit Memory.max_ts_spec; try exact GET1. i. des.
          exploit TimeFacts.lt_le_lt; try exact H; try exact MAX. i.
          specialize (Time.incr_spec (Memory.max_ts l mem1_src)). i.
          rewrite x0 in H0. timetac.
        + exploit Local.write_step_future; eauto. i. des.
          inv STEP0. inv WRITE. inv PROMISE. ss.
          ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          * inv GET. rewrite H2 in *. ss.
          * etrans; try eapply TVIEW_FUTURE0.
            etrans; try eapply TVIEW_FUTURE; eauto.
    }
    { (* cas_sucess1 *)
      inv STATE. ss. subst.
      inv STEP_TGT. inv STATE. inv INSTR. ss.
      destruct e_tgt; ss; inv LOCAL0.
      esplits.
      - econs 1.
      - ss.
      - econs; s; eauto.
        do 3 right. left. econs; ss.
        + etrans; eauto. symmetry.
          apply RegFile.eq_except_singleton.
        + unfold RegFun.add. condtac; ss.
          symmetry. eapply RegFile.eq_except_value; eauto.
          inv REGFREE. inv H1. ss.
          symmetry in REGFREE.
          apply RegSet.disjoint_add in REGFREE. des.
          symmetry. eapply RegSet.disjoint_union_inv_r; eauto.
    }
    { (* cas_success2 *)
      inv STATE. ss. subst.
      inv STEP_TGT. inv STATE. inv INSTR.
      destruct e_tgt; ss; try by inv LOCAL0.
      exploit PromotionProgress.progress_read; try eapply LATEST; eauto.
      { destruct released; eauto using View.bot_spec. }
      i. des.
      exploit Local.read_step_future; eauto. i. des.
      exploit PromotionProgress.progress_write; try exact WF2; eauto.
      { inv STEP. ss. }
      { etrans; try eapply TVIEW_FUTURE.
        destruct released; try apply View.bot_spec.
        eapply SAFE; eauto. }
      i. des. esplits.
      - econs 2. econs; cycle 1.
        + econs 4; eauto.
        + econs. econs. ss. condtac; ss.
      - ss.
      - inv LOCAL0. econs; ss; eauto.
        + inv REGFREE. ss.
        + left. econs; eauto. ss.
          eapply RegFile.eq_except_add; eauto.
        + etrans; eauto. symmetry. etrans; eauto.
        + etrans; eauto. symmetry. ss.
        + ii. inv STEP. inv LC0. ss. inv STEP0. ss.
          inv WRITE. inv PROMISE. revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          guardH o. guardH o0.
          destruct (Loc.eq_dec loc l); try by subst; congr.
          exploit FULFILLABLE; eauto. i. des. split.
          * unfold tview_released_le_loc in *.
            unfold TView.write_tview. ss.
            unfold LocFun.add. condtac; ss.
          * unfold prev_released_le_loc in *.
            erewrite Memory.add_o; eauto. condtac; ss.
            des. subst. ss.
        + ss. unfold RegFun.add. condtac; ss; eauto.
          { subst. inv REGFREE. inv H1. ss.
            symmetry in REGFREE.
            apply RegSet.disjoint_add in REGFREE. des.
            exfalso. apply REGFREE.
            eapply RegSet.Facts.singleton_2; ss. }
          unfold RegFun.find. rewrite REGR.
          inv STEP0. inv WRITE. inv PROMISE. ss.
          exploit Memory.add_get0; try exact MEM0. i. des.
          replace (Memory.max_ts l mem0) with (Time.incr (Memory.max_ts l mem1_src)); eauto.
          exploit Memory.max_ts_spec; try exact GET0. i. des. inv MAX; ss.
          revert GET1. erewrite Memory.add_o; eauto. condtac; ss; try by des.
          guardH o. i.
          exploit Memory.max_ts_spec; try exact GET1. i. des.
          exploit TimeFacts.lt_le_lt; try exact H; try exact MAX. i.
          specialize (Time.incr_spec (Memory.max_ts l mem1_src)). i.
          rewrite x0 in H0. timetac.
        + exploit Local.write_step_future; eauto. i. des.
          inv STEP0. inv WRITE. inv PROMISE. ss.
          ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          * inv GET. rewrite H2 in *. ss.
          * etrans; try eapply TVIEW_FUTURE0.
            etrans; try eapply TVIEW_FUTURE; eauto.
    }
    { (* cas_fail *)
      inv STATE. ss. subst.
      inv STEP_TGT. inv STATE. inv INSTR.
      destruct e_tgt; ss; try by inv LOCAL0.
      exploit PromotionProgress.progress_read; try eapply LATEST; eauto.
      { destruct released; eauto using View.bot_spec. }
      i. des. esplits.
      - econs 2. econs; cycle 1.
        + econs 2; eauto.
        + econs. econs. ss. condtac; ss. congr.
      - ss.
      - inv LOCAL0. econs; ss; eauto.
        + inv REGFREE. ss.
        + left. econs; eauto; ss.
          * apply RegFile.eq_except_add; auto.
          * unfold RegFun.add. condtac; ss.
            subst. inv REGFREE. inv H1. ss.
            symmetry in REGFREE.
            apply RegSet.disjoint_add in REGFREE. des.
            exfalso. apply REGFREE.
            apply RegSet.Facts.singleton_2; ss.
        + etrans; eauto. symmetry. ss.
        + ii. inv STEP. inv LC. ss.
          exploit FULFILLABLE; eauto.
        + inv STEP. inv LC. ss.
        + ii. etrans; try eapply SAFE; eauto.
          exploit Local.read_step_future; eauto. i. des.
          apply TVIEW_FUTURE.
    }

    (* synch *)
    inv STATE. ss.
    exploit promote_stmts_cases; eauto. i. des.
    { (* nil *)
      subst. inv STEP_TGT.
      unfold promote_stmts in *. ss. inv STATE.
    }
    { (* load *)
      rewrite STMTS_TGT in *.
      inv STEP_TGT. inv STATE. inv INSTR.
      destruct e_tgt; ss; try by inv LOCAL0.
      exploit PromotionProgress.progress_read; try eapply LATEST; eauto.
      { destruct released; eauto using View.bot_spec. }
      i. des. esplits.
      - econs 2. econs; cycle 1.
        + econs 2; eauto.
        + econs. econs.
      - ss.
      - inv LOCAL0. econs; ss; eauto.
        + inv REGFREE. ss.
        + left. econs; eauto; ss.
          * apply RegFile.eq_except_add; auto.
          * unfold RegFun.add. condtac; ss.
        + etrans; eauto. symmetry. ss.
        + ii. inv STEP. inv LC. ss.
          exploit FULFILLABLE; eauto.
        + inv STEP. inv LC. ss.
        + ii. etrans; try eapply SAFE; eauto.
          exploit Local.read_step_future; eauto. i. des.
          apply TVIEW_FUTURE.
    }
    { (* store *)
      rewrite STMTS_TGT in *.
      inv STEP_TGT. inv STATE. inv INSTR.
      destruct e_tgt; ss; try by inv LOCAL0.
      exploit PromotionProgress.progress_write; try exact WF1_SRC; try exact SC1_SRC; eauto.
      { ss. apply View.bot_spec. }
      i. des. esplits.
      - econs 2. econs; cycle 1.
        + econs 3; eauto.
        + econs. econs.
      - ss.
      - inv LOCAL0. econs; ss; eauto.
        + inv REGFREE. ss.
        + left. econs; eauto; ss.
          etrans; eauto. symmetry.
          apply RegFile.eq_except_singleton.
        + etrans; eauto. symmetry. ss.
        + etrans; eauto. symmetry. ss.
        + ii. inv STEP. inv LC. ss.
          inv WRITE. inv PROMISE. revert GETP.
          erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          guardH o. guardH o0.
          destruct (Loc.eq_dec loc l); try by subst; congr.
          exploit FULFILLABLE; eauto. i. des. split.
          * unfold tview_released_le_loc in *.
            unfold TView.write_tview. ss.
            unfold LocFun.add. condtac; ss.
          * unfold prev_released_le_loc in *.
            erewrite Memory.add_o; eauto. condtac; ss.
            des. subst. ss.
        + ss. unfold RegFun.add. condtac; ss.
          inv STEP. inv WRITE. inv PROMISE. ss.
          exploit Memory.add_get0; try exact MEM0. i. des.
          erewrite <- RegFile.eq_except_value; eauto; cycle 1.
          { inv REGFREE. inv H1. ss. }
          replace (Memory.max_ts l mem0) with (Time.incr (Memory.max_ts l mem1_src)); eauto.
          exploit Memory.max_ts_spec; try exact GET0. i. des. inv MAX; ss.
          revert GET1. erewrite Memory.add_o; eauto. condtac; ss; try by des.
          guardH o. i.
          exploit Memory.max_ts_spec; try exact GET1. i. des.
          exploit TimeFacts.lt_le_lt; try exact H; try exact MAX. i.
          specialize (Time.incr_spec (Memory.max_ts l mem1_src)). i.
          rewrite x0 in H0. timetac.
        + exploit Local.write_step_future; eauto. i. des.
          inv STEP. inv WRITE. inv PROMISE. ss.
          ii. revert GET.
          erewrite Memory.add_o; eauto. condtac; ss; i.
          * inv GET. rewrite H2 in *. ss.
          * etrans; try eapply TVIEW_FUTURE; eauto.
    }
    { (* fa *)
      ss. subst. rewrite STMTS_TGT in *.
      inv STEP_TGT. inv STATE. inv INSTR. ss.
      destruct e_tgt; ss; inv LOCAL0.
      esplits.
      - econs 1.
      - ss.
      - econs; s; eauto.
        right. left. econs; ss.
        + etrans; eauto. symmetry.
          apply RegFile.eq_except_singleton.
        + unfold RegFun.add. condtac; ss.
          erewrite <- RegFile.eq_except_value; eauto.
          inv REGFREE. inv H1. ss.
          symmetry in REGFREE.
          apply RegSet.disjoint_add in REGFREE. des.
          symmetry. ss.
    }
    { (* cas *)
      ss. subst. rewrite STMTS_TGT in *.
      inv STEP_TGT. inv STATE.
      destruct e_tgt; ss; inv LOCAL0.
      esplits.
      - econs 1.
      - ss.
      - econs; s; eauto. condtac; ss.
        + right. right. left. econs; ss.
          unfold Op2.const_eq, RegFun.find in *. des_ifs; ss.
          rewrite e. symmetry.
          eapply RegFile.eq_except_value; eauto.
          inv REGFREE. inv H2. ss.
          symmetry in REGFREE.
          apply RegSet.disjoint_add in REGFREE. des.
          symmetry. eapply RegSet.disjoint_union_inv_l; eauto.
        + do 4 right. econs; ss.
          unfold Op2.const_eq, RegFun.find in *. des_ifs; ss.
          ii. rewrite H in *. apply n.
          eapply RegFile.eq_except_value; eauto.
          inv REGFREE. inv H3. ss.
          symmetry in REGFREE.
          apply RegSet.disjoint_add in REGFREE. des.
          symmetry. eapply RegSet.disjoint_union_inv_l; eauto.
    }
    { (* ite *)
      ss. subst. rewrite STMTS_TGT in *.
      inv STEP_TGT. inv STATE.
      destruct e_tgt; ss; inv LOCAL0.
      esplits.
      - econs 2. econs; [|eauto]. econs 2.
      - ss.
      - econs; s; eauto.
        + inv REGFREE. inv H2.
          eapply Forall_app; ss. condtac; ss.
        + left. erewrite RegFile.eq_except_expr; eauto; cycle 1.
          { inv REGFREE. inv H2. ss. }
          condtac; ss.
          * econs; ss. rewrite promote_stmts_app. ss.
          * econs; ss. rewrite promote_stmts_app. ss.
    }
    { (* dowhile *)
      ss. subst. rewrite STMTS_TGT in *.
      inv STEP_TGT. inv STATE.
      destruct e_tgt; ss; inv LOCAL0.
      esplits.
      - econs 2. econs; [|eauto]. econs 3.
      - ss.
      - econs; s; eauto.
        + inv REGFREE. inv H2.
          eapply Forall_app; ss. repeat econs; ss.
        + left. econs; ss.
          rewrite promote_stmts_app. ss.
    }
    { (* locfree *)
      inv STEP_TGT.
      hexploit loc_free_step_is_accessing_loc; eauto.
      { eapply promote_stmts_loc_free. }
      intro LOC.
      exploit program_step; try eapply SIM1; try exact LOCAL; eauto. s. i. des.
      rewrite promote_stmts_cons in STMTS_TGT.
      replace (stmt :: promote_stmts l r stmts'_src) with
          ([stmt] ++ promote_stmts l r stmts'_src) in STMTS_TGT by ss.
      exploit List.app_inv_tail; try exact STMTS_TGT. i.
      rewrite promote_stmts_cons in STATE.
      rewrite x0 in STATE. ss.
      exploit promote_stmts_step; try eapply STATE; eauto; try by inv REGFREE. i. des.
      esplits.
      - econs 2. econs; try exact STEP_SRC.
        rewrite EVENT2. exact STEP_SRC0.
      - ss.
      - econs; eauto; ss.
        + eapply step_reg_free; eauto. ss.
        + left. econs; eauto.
        + assert (VAL: regs1_tgt r = st2.(State.regs) r).
          { inv STATE; ss. destruct i; inv INSTR; ss.
            - unfold RegFun.add. condtac; ss. subst.
              exfalso. inv REGFREE. inv H1. ss.
              symmetry in REGFREE.
              apply RegSet.disjoint_add in REGFREE. des.
              apply REGFREE.
              eapply RegSet.Facts.singleton_2; ss.
            - unfold RegFun.add. condtac; ss. subst.
              exfalso. inv REGFREE. inv H1. ss.
              unfold RegSet.disjoint in REGFREE.
              apply (REGFREE lhs); eauto using RegSet.Facts.singleton_2.
            - unfold RegFun.add. condtac; ss. subst.
              exfalso. inv REGFREE. inv H1. ss.
              symmetry in REGFREE.
              apply RegSet.disjoint_add in REGFREE. des.
              apply REGFREE.
              eapply RegSet.Facts.singleton_2; ss.
            - unfold RegFun.add. condtac; ss. subst.
              exfalso. inv REGFREE. inv H1. ss.
              symmetry in REGFREE.
              apply RegSet.disjoint_add in REGFREE. des.
              apply REGFREE.
              eapply RegSet.Facts.singleton_2; ss.
            - unfold RegFun.add. condtac; ss. subst.
              exfalso. inv REGFREE. inv H1. ss.
              symmetry in REGFREE.
              apply RegSet.disjoint_add in REGFREE. des.
              apply REGFREE.
              eapply RegSet.Facts.singleton_2; ss.
          }
          cut (forall to, Memory.get l to mem1_src = Memory.get l to mem2_src).
          { i. exploit eq_loc_max_ts; eauto. i.
            rewrite <- VAL. rewrite <- x1. rewrite <- H.
            inv SIM1. eauto. }
          rewrite <- ThreadEvent.eq_program_event_eq_loc in *; eauto.
          unfold ThreadEvent.is_accessing_loc in *. inv STEP_SRC; ss.
          * inv LOCAL1. inv WRITE. eapply promise_eq_mem; eauto.
          * inv LOCAL2. inv WRITE. eapply promise_eq_mem; eauto.
        + i. rewrite <- ThreadEvent.eq_program_event_eq_loc in *; eauto.
          unfold ThreadEvent.is_accessing_loc in *.
          inv STEP_SRC; ss; try by inv LOCAL1; ss.
          * inv LOCAL1. inv WRITE. ss.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite <- promise_eq_promises; eauto.
          * inv LOCAL1. inv LOCAL2. inv WRITE. ss.
            erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite <- promise_eq_promises; eauto.
        + ii. exploit Local.program_step_future; try exact STEP_SRC; eauto. i. des.
          etrans; try eapply TVIEW_FUTURE.
          inv SIM1. ss. revert GET.
          rewrite <- ThreadEvent.eq_program_event_eq_loc in *; eauto.
          unfold ThreadEvent.is_accessing_loc in *.
          inv STEP_SRC; ss; eauto; try by inv LOCAL1; ss; eauto.
          * inv LOCAL2. inv WRITE. ss.
            erewrite <- promise_eq_mem; eauto.
          * inv LOCAL2. inv LOCAL3. inv WRITE. ss.
            erewrite <- promise_eq_mem; eauto.
    }
  Qed.

  Lemma sim_thread_step
        l r e1_src
        pf e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.step pf e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
    inv STEP_TGT.
    - exploit sim_thread_promise_step; eauto. i. des.
      esplits.
      + inv STEP_SRC.
        * econs 1.
        * econs 2. econs 1; eauto.
      + inv STEP. inv STEP_SRC; ss. inv STEP. ss.
      + ss.
    - exploit sim_thread_program_step; eauto. i. des.
      esplits.
      + inv STEP_SRC.
        * econs 1.
        * econs 2. econs 2; eauto.
      + ss.
      + ss.
  Qed.

  Lemma sim_thread_opt_step
        l r e1_src
        e_tgt e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEP_TGT: Thread.opt_step e_tgt e1_tgt e2_tgt):
    exists e_src e2_src,
      <<STEP_SRC: Thread.opt_step e_src e1_src e2_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
    inv STEP_TGT.
    - esplits; eauto. econs 1.
    - exploit sim_thread_step; eauto.
  Qed.

  Lemma sim_thread_rtc_tau_step
        l r e1_src
        e1_tgt e2_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt):
    exists e2_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<SIM2: sim_thread l r e2_src e2_tgt>>.
  Proof.
    revert e1_src SIM1 WF1_SRC SC1_SRC CLOSED1_SRC.
    induction STEPS_TGT; i.
    - esplits; eauto.
    - inv H. inv TSTEP.
      exploit sim_thread_step; eauto. i. des.
      exploit Thread.step_future; try exact STEP; eauto. i. des.
      exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
      exploit IHSTEPS_TGT; eauto. i. des.
      inv STEP_SRC.
      + esplits; eauto.
      + esplits; [M|..]; eauto.
        econs; [|eauto].
        econs; [econs; eauto|]. rewrite <- EVENT. ss.
  Qed.

  Lemma sim_thread_plus_step
        l r e1_src
        e_tgt e1_tgt e2_tgt e3_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.opt_step e_tgt e2_tgt e3_tgt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread l r e3_src e3_tgt>>.
  Proof.
    exploit sim_thread_rtc_tau_step; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_TGT; eauto. i. des.
    exploit sim_thread_opt_step; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma reorder_cancel
        lang e e1 e2 e3
        l from to
        (STEP1: @Thread.step lang true e e1 e2)
        (STEP2: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add) e2 e3)
        (EVENT: ThreadEvent.get_machine_event e <> MachineEvent.silent):
    exists e2',
      <<STEP1: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add) e1 e2'>> /\
      <<STEP2: Thread.step true e e2' e3>>.
  Proof.
    destruct e; ss.
    - inv STEP1; inv STEP. inv LOCAL. inv LOCAL0. ss.
      inv STEP2. inv STEP. inv LOCAL. ss.
      esplits.
      + econs. econs; ss. econs; eauto.
      + econs 2. econs; ss. econs. econs; eauto.
        ii. inv PROMISE. ss. revert GET.
        erewrite Memory.add_o; eauto. condtac; ss; i.
        * inv GET. ss.
        * eapply RELEASE; eauto.
    - inv STEP1; inv STEP. inv LOCAL. inv LOCAL0. ss.
      inv STEP2. inv STEP. inv LOCAL. ss.
      esplits.
      + econs. econs; ss. econs; eauto.
      + econs 2. econs; ss. econs. econs; eauto.
        ii. inv PROMISE. ss. revert PROMISE0.
        erewrite Memory.add_o; eauto. condtac; ss; i.
        eapply CONSISTENT; eauto.
  Qed.

  Lemma sim_thread_plus_step_wrap
        l r e1_src
        e_tgt e1_tgt e2_tgt e3_tgt
        (SIM1: sim_thread_reserve l r e1_src e1_tgt)
        (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
        (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
        (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
        (CLOSED1_SRC: Memory.closed e1_src.(Thread.memory))
        (CLOSED1_TGT: Memory.closed e1_tgt.(Thread.memory))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.opt_step e_tgt e2_tgt e3_tgt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread_reserve l r e3_src e3_tgt>>.
  Proof.
    exploit step_reserve_sim_thread; try exact SIM1; eauto. i. des.
    exploit Thread.step_future; eauto. i. des.
    exploit sim_thread_plus_step; try exact SIM2; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
    exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
    exploit step_sim_thread_reserve; try exact SIM3; eauto. i. des.
    destruct (classic (ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)).
    - exploit Thread.tau_opt_tau; try exact STEPS_SRC; eauto; i.
      { rewrite EVENT. ss. }
      esplits.
      + econs 2; try exact x0. econs; [econs; eauto|]. ss.
      + econs 2; eauto.
      + ss.
      + ss.
    - inv STEP_SRC; try by (ss; congr).
      rewrite <- EVENT in H.
      destruct pf; cycle 1.
      { inv STEP1. inv STEP2. ss. }
      exploit reorder_cancel; try exact STEP1; eauto. i. des.
      esplits.
      + econs 2.
        * econs; [econs; eauto|]. ss.
        * eapply rtc_n1; try exact STEPS_SRC.
          econs; [econs; exact STEP2|]. ss.
      + econs 2. apply STEP3.
      + ss.
      + ss.
  Qed.
End SimThreadPromotion.
