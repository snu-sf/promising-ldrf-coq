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
Require Import CompressSteps.

Require Import PromotionDef.
Require Import SimCommon.
Require Import PromotionProgress.

Set Implicit Arguments.


Module SimThreadPromotion.
  Import SimCommon.

  (* sim_state *)

  Inductive sim_state_synch (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_synch_intro
      (STMTS: (State.stmts st_tgt) = promote_stmts l r (State.stmts st_src))
      (REGS: RegFile.eq_except (RegSet.singleton r) (State.regs st_src) (State.regs st_tgt))
      (REGR: (State.regs st_tgt) r = val)
  .
  Hint Constructors sim_state_synch.

  Inductive sim_state_fa (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_fa_intro
      lhs addendum ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: (State.stmts st_src) =
                  (Stmt.instr (Instr.update lhs l (Instr.fetch_add addendum) ordr ordw)) :: stmts_src)
      (STMTS_TGT: (State.stmts st_tgt) =
                  (Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.reg r)))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) (State.regs st_src) (State.regs st_tgt))
      (REGR: (State.regs st_tgt) r = val + RegFile.eval_value (State.regs st_src) addendum)
  .
  Hint Constructors sim_state_fa.

  Inductive sim_state_cas_success1 (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas1_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: (State.stmts st_src) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: (State.stmts st_tgt) =
                  Stmt.instr (Instr.assign r new) ::
                             Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1)))
                             :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) (State.regs st_src) (State.regs st_tgt))
      (REGR: (State.regs st_tgt) r = val)
      (SUCCESS: val = RegFile.eval_value (State.regs st_src) old)
  .
  Hint Constructors sim_state_cas_success1.

  Inductive sim_state_cas_success2 (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas2_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: (State.stmts st_src) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: (State.stmts st_tgt) =
                  Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 1))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) (State.regs st_src) (State.regs st_tgt))
      (REGR: (State.regs st_tgt) r = RegFile.eval_value (State.regs st_src) new)
      (SUCCESS: val = RegFile.eval_value (State.regs st_src) old)
  .
  Hint Constructors sim_state_cas_success2.

  Inductive sim_state_cas_fail (l: Loc.t) (r: Reg.t) (val: Const.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_cas_fail_intro
      lhs old new ordr ordw stmts_src stmts_tgt
      (STMTS_SRC: (State.stmts st_src) =
                  (Stmt.instr (Instr.update lhs l (Instr.cas old new) ordr ordw)) :: stmts_src)
      (STMTS_TGT: (State.stmts st_tgt) =
                  Stmt.instr (Instr.assign lhs (Instr.expr_val (Value.const 0))) :: stmts_tgt)
      (STMTS: stmts_tgt = promote_stmts l r stmts_src)
      (REGS: RegFile.eq_except (RegSet.singleton r) (State.regs st_src) (State.regs st_tgt))
      (REGR: (State.regs st_tgt) r = val)
      (FAIL: val <> RegFile.eval_value (State.regs st_src) old)
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
      (GET: Memory.get l to mem = Some (from, Message.concrete val (Some released))),
      View.le released (TView.cur (Local.tview lc)).

  Inductive sim_thread (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      val
      (REGFREE: reg_free_stmts r (State.stmts (Thread.state e_src)))
      (STATE: sim_state l r val (Thread.state e_src) (Thread.state e_tgt))
      (LOCAL: sim_local l (Thread.local e_src) (Thread.local e_tgt))
      (SC: sim_timemap l (Thread.sc e_src) (Thread.sc e_tgt))
      (MEMORY: sim_memory l (Thread.memory e_src) (Thread.memory e_tgt))
      (FULFILLABLE: fulfillable l (Local.tview (Thread.local e_src)) (Thread.memory e_src)
                                  (Local.promises (Thread.local e_src)))
      (LATEST: exists from released,
          Memory.get l (Memory.max_ts l (Thread.memory e_src)) (Thread.memory e_src) =
          Some (from, Message.concrete val released))
      (PROMISES: forall to, Memory.get l to (Local.promises (Thread.local e_src)) = None)
      (SAFE: safe l (Thread.local e_src) (Thread.memory e_src))
  .
  Hint Constructors sim_thread.

  Inductive sim_thread_reserve (l: Loc.t) (r: Reg.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_reserve_intro
      val
      (REGFREE: reg_free_stmts r (State.stmts (Thread.state e_src)))
      (STATE: sim_state l r val (Thread.state e_src) (Thread.state e_tgt))
      (LOCAL: sim_local l (Thread.local e_src) (Thread.local e_tgt))
      (SC: sim_timemap l (Thread.sc e_src) (Thread.sc e_tgt))
      (MEMORY: sim_memory l (Thread.memory e_src) (Thread.memory e_tgt))
      (FULFILLABLE: fulfillable l (Local.tview (Thread.local e_src)) (Thread.memory e_src)
                                  (Local.promises (Thread.local e_src)))
      (LATEST: exists from from' released,
          <<MEM: Memory.get l (Memory.max_ts l (Thread.memory e_src)) (Thread.memory e_src) =
                 Some (from, Message.reserve)>> /\
          <<PROMISE: Memory.get l (Memory.max_ts l (Thread.memory e_src)) (Local.promises (Thread.local e_src)) =
                     Some (from, Message.reserve)>> /\
          <<LATEST: Memory.get l from (Thread.memory e_src) =
                    Some (from', Message.concrete val released)>>)
      (PROMISES: forall to (TO: to <> Memory.max_ts l (Thread.memory e_src)),
          Memory.get l to (Local.promises (Thread.local e_src)) = None)
      (SAFE: safe l (Thread.local e_src) (Thread.memory e_src))
  .
  Hint Constructors sim_thread_reserve.

  Definition sim_thread_all (l: Loc.t) (r: Reg.t): forall (e_src e_tgt: Thread.t lang), Prop :=
    (sim_thread l r) \2/ (sim_thread_reserve l r).
  Hint Unfold sim_thread_all.


  Lemma step_sim_thread_reserve
        l r e1_src e_tgt
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
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
    clear TVIEW_WF TVIEW_CLOSED FINITE BOT.
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
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
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
    clear TVIEW_WF TVIEW_CLOSED FINITE BOT.
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
        (MEMLOC: forall to, Memory.get loc to mem1 = Memory.get loc to mem2):
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
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
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
      <<REGS2: RegFile.eq_except (RegSet.singleton r) (State.regs st2_src) (State.regs st2_tgt)>> /\
      <<STMTS2: (State.stmts st2_tgt) = promote_stmts l r (State.stmts st2_src)>>.
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
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
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
        + assert (VAL: regs1_tgt r = (State.regs st2) r).
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
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
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
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
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
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
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
        pf e_tgt e1_tgt e2_tgt e3_tgt
        (SIM1: sim_thread l r e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.step pf e_tgt e2_tgt e3_tgt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread l r e3_src e3_tgt>>.
  Proof.
    exploit sim_thread_rtc_tau_step; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
    exploit Thread.rtc_tau_step_future; try exact STEPS_TGT; eauto. i. des.
    exploit sim_thread_step; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma reorder_failure_cancel
        lang e1 e2 e3
        l from to
        (STEP1: @Thread.step lang true ThreadEvent.failure e1 e2)
        (STEP2: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add) e2 e3):
    exists e2',
      <<STEP1: Thread.step false (ThreadEvent.promise l from to Message.reserve Memory.op_kind_add) e1 e2'>> /\
      <<STEP2: Thread.step true ThreadEvent.failure e2' e3>>.
  Proof.
    inv STEP1; inv STEP. inv LOCAL. inv LOCAL0. ss.
    inv STEP2. inv STEP. inv LOCAL. ss.
    esplits.
    - econs. econs; ss. econs; eauto.
    - econs 2. econs; ss. econs. econs; eauto.
      ii. inv PROMISE. ss. revert PROMISE0.
      erewrite Memory.add_o; eauto. condtac; ss; i.
      eapply CONSISTENT; eauto.
  Qed.

  Lemma sim_thread_all_plus_step
        l r e1_src
        pf e_tgt e1_tgt e2_tgt e3_tgt
        (SIM1: sim_thread_all l r e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.step pf e_tgt e2_tgt e3_tgt)
        (EVENT: forall evt, e_tgt <> ThreadEvent.syscall evt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.opt_step e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread_reserve l r e3_src e3_tgt>>.
  Proof.
    inv SIM1.
    { exploit sim_thread_plus_step; try exact SIM2; eauto. i. des.
      exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
      exploit step_sim_thread_reserve; try exact SIM3; eauto. i. des.
      destruct (classic (ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)).
      - exploit Thread.tau_opt_tau; try exact STEPS_SRC; eauto; i.
        { rewrite EVENT0. ss. }
        esplits.
        + apply x0.
        + econs 2; eauto.
        + ss.
        + ss.
      - inv STEP_SRC; try by (ss; congr).
        destruct e_tgt; ss; try congr.
        rewrite <- EVENT0 in H0.
        destruct pf0; [|inv STEP0; inv STEP1; ss].
        destruct e_src; ss.
        exploit reorder_failure_cancel; try exact STEP0; eauto. i. des.
        esplits.
        + eapply rtc_n1; try exact STEPS_SRC.
          econs; [econs; eauto|]. ss.
        + econs 2. apply STEP2.
        + ss.
        + ss.
    }
    { exploit step_reserve_sim_thread; try exact H; eauto. i. des.
      exploit Thread.step_future; eauto. i. des.
      exploit sim_thread_plus_step; try exact SIM2; eauto. i. des.
      exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
      exploit step_sim_thread_reserve; try exact SIM3; eauto. i. des.
      destruct (classic (ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)).
      - exploit Thread.tau_opt_tau; try exact STEPS_SRC; eauto; i.
        { rewrite EVENT0. ss. }
        esplits.
        + econs 2; try exact x0. econs; [econs; eauto|]. ss.
        + econs 2; eauto.
        + ss.
        + ss.
      - inv STEP_SRC; try by (ss; congr).
        destruct e_tgt; ss; try congr.
        rewrite <- EVENT0 in H0.
        destruct pf0; [|inv STEP1; inv STEP2; ss].
        destruct e_src; ss.
        exploit reorder_failure_cancel; try exact STEP1; eauto. i. des.
        esplits.
        + econs 2.
          * econs; [econs; eauto|]. ss.
          * eapply rtc_n1; try exact STEPS_SRC.
            econs; [econs; eauto|]. ss.
        + econs 2. apply STEP3.
        + ss.
        + ss.
    }
  Qed.

  Lemma sim_thread_all_plus_step_syscall
        l r e1_src
        pf e_tgt e1_tgt e2_tgt e3_tgt evt
        (SIM1: sim_thread_all l r e1_src e1_tgt)
        (WF1_SRC: Local.wf (Thread.local e1_src) (Thread.memory e1_src))
        (WF1_TGT: Local.wf (Thread.local e1_tgt) (Thread.memory e1_tgt))
        (SC1_SRC: Memory.closed_timemap (Thread.sc e1_src) (Thread.memory e1_src))
        (SC1_TGT: Memory.closed_timemap (Thread.sc e1_tgt) (Thread.memory e1_tgt))
        (CLOSED1_SRC: Memory.closed (Thread.memory e1_src))
        (CLOSED1_TGT: Memory.closed (Thread.memory e1_tgt))
        (STEPS_TGT: rtc (@Thread.tau_step lang) e1_tgt e2_tgt)
        (STEP_TGT: Thread.step pf e_tgt e2_tgt e3_tgt)
        (EVENT: e_tgt = ThreadEvent.syscall evt):
    exists e_src e2_src e3_src,
      <<STEPS_SRC: rtc (@Thread.tau_step lang) e1_src e2_src>> /\
      <<STEP_SRC: Thread.step true e_src e2_src e3_src>> /\
      <<EVENT: ThreadEvent.get_machine_event e_src = ThreadEvent.get_machine_event e_tgt>> /\
      <<SIM3: sim_thread l r e3_src e3_tgt>>.
  Proof.
    inv SIM1.
    { exploit sim_thread_plus_step; eauto. i. des.
      esplits; eauto.
      destruct e_src; ss. inv STEP_SRC; ss.
      destruct pf0; [|inv STEP; inv STEP0; ss]. ss.
    }
    { subst. ss.
      exploit step_reserve_sim_thread; try exact H; eauto. i. des.
      exploit Thread.step_future; eauto. i. des.
      exploit sim_thread_plus_step; try exact SIM2; eauto. i. des.
      exploit Thread.rtc_tau_step_future; try exact STEPS_SRC; eauto. i. des.
      exploit Thread.opt_step_future; try exact STEP_SRC; eauto. i. des.
      destruct e_src; ss. inv STEP_SRC.
      destruct pf0; [|inv STEP0; inv STEP1].
      esplits.
      - econs 2; try exact STEPS_SRC. econs; [econs; eauto|]. ss.
      - eauto.
      - ss.
      - ss.
    }
  Qed.


  (* future *)

  Lemma sim_thread_future
        l r
        st_src lc_src sc1_src mem1_src sc2_src mem2_src
        st_tgt lc_tgt sc1_tgt mem1_tgt sc2_tgt mem2_tgt
        (SIM1: sim_thread l r
                          (Thread.mk lang st_src lc_src sc1_src mem1_src)
                          (Thread.mk lang st_tgt lc_tgt sc1_tgt mem1_tgt))
        (WF1_SRC: Local.wf lc_src mem1_src)
        (MEM_SRC: Memory.future mem1_src mem2_src)
        (SC: sim_timemap l sc2_src sc2_tgt)
        (MEM: sim_memory l mem2_src mem2_tgt)
        (PREV: Memory.prev_None mem1_src mem2_src)
        (MEMLOC: forall to, Memory.get l to mem1_src = Memory.get l to mem2_src):
    sim_thread l r
               (Thread.mk lang st_src lc_src sc2_src mem2_src)
               (Thread.mk lang st_tgt lc_tgt sc2_tgt mem2_tgt).
  Proof.
    inv SIM1. des. ss. econs; s; eauto.
    - ii. exploit FULFILLABLE; eauto. i. des. split; ss.
      unfold prev_released_le_loc in *. des_ifs; ss.
      + exploit Memory.future_get1; try exact Heq0; eauto. i. des.
        inv MSG_LE. inv RELEASED; try congr.
        rewrite Heq in *. inv GET.
        unnw. etrans; eauto. split; apply LE.
      + exploit Memory.future_get1; try exact Heq0; eauto. i. des.
        inv MSG_LE. inv RELEASED; try congr.
      + inv WF1_SRC. exploit PROMISES0; eauto. i.
        exploit PREV; eauto; ss. ii. congr.
      + inv WF1_SRC. exploit PROMISES0; eauto. i.
        exploit PREV; eauto; ss. ii. congr.
    - erewrite <- eq_loc_max_ts; eauto.
      rewrite MEMLOC in *.
      esplits; eauto.
    - ii. rewrite <- MEMLOC in *. eauto.
  Qed.

  Lemma sim_thread_reserve_future
        l r
        st_src lc_src sc1_src mem1_src sc2_src mem2_src
        st_tgt lc_tgt sc1_tgt mem1_tgt sc2_tgt mem2_tgt
        (SIM1: sim_thread_reserve l r
                          (Thread.mk lang st_src lc_src sc1_src mem1_src)
                          (Thread.mk lang st_tgt lc_tgt sc1_tgt mem1_tgt))
        (WF1_SRC: Local.wf lc_src mem1_src)
        (MEM_SRC: Memory.future mem1_src mem2_src)
        (SC: sim_timemap l sc2_src sc2_tgt)
        (MEM: sim_memory l mem2_src mem2_tgt)
        (PREV: Memory.prev_None mem1_src mem2_src)
        (MEMLOC: forall to, Memory.get l to mem1_src = Memory.get l to mem2_src):
    sim_thread_reserve l r
               (Thread.mk lang st_src lc_src sc2_src mem2_src)
               (Thread.mk lang st_tgt lc_tgt sc2_tgt mem2_tgt).
  Proof.
    inv SIM1. des. ss. econs; s; eauto.
    - ii. exploit FULFILLABLE; eauto. i. des. split; ss.
      unfold prev_released_le_loc in *. des_ifs; ss.
      + exploit Memory.future_get1; try exact Heq0; eauto. i. des.
        inv MSG_LE. inv RELEASED; try congr.
        rewrite Heq in *. inv GET.
        unnw. etrans; eauto. split; apply LE.
      + exploit Memory.future_get1; try exact Heq0; eauto. i. des.
        inv MSG_LE. inv RELEASED; try congr.
      + inv WF1_SRC. exploit PROMISES0; eauto. i.
        exploit PREV; eauto; ss. ii. congr.
      + inv WF1_SRC. exploit PROMISES0; eauto. i.
        exploit PREV; eauto; ss. ii. congr.
    - erewrite <- eq_loc_max_ts; eauto.
      rewrite MEMLOC in *.
      esplits; eauto.
    - erewrite <- eq_loc_max_ts; eauto.
    - ii. rewrite <- MEMLOC in *. eauto.
  Qed.

  Lemma sim_thread_all_future
        l r
        st_src lc_src sc1_src mem1_src sc2_src mem2_src
        st_tgt lc_tgt sc1_tgt mem1_tgt sc2_tgt mem2_tgt
        (SIM1: sim_thread_all l r
                          (Thread.mk lang st_src lc_src sc1_src mem1_src)
                          (Thread.mk lang st_tgt lc_tgt sc1_tgt mem1_tgt))
        (WF1_SRC: Local.wf lc_src mem1_src)
        (MEM_SRC: Memory.future mem1_src mem2_src)
        (SC: sim_timemap l sc2_src sc2_tgt)
        (MEM: sim_memory l mem2_src mem2_tgt)
        (PREV: Memory.prev_None mem1_src mem2_src)
        (MEMLOC: forall to, Memory.get l to mem1_src = Memory.get l to mem2_src):
    sim_thread_all l r
               (Thread.mk lang st_src lc_src sc2_src mem2_src)
               (Thread.mk lang st_tgt lc_tgt sc2_tgt mem2_tgt).
  Proof.
    inv SIM1.
    - left. eapply sim_thread_future; eauto.
    - right. eapply sim_thread_reserve_future; eauto.
  Qed.


  (* terminal *)

  Lemma sim_thread_promises_bot
        l r e_src e_tgt
        (SIM: sim_thread l r e_src e_tgt)
        (PROMISES_TGT: (Local.promises (Thread.local e_tgt)) = Memory.bot):
    <<PROMISES_SRC: (Local.promises (Thread.local e_src)) = Memory.bot>>.
  Proof.
    inv SIM. inv LOCAL. apply Memory.ext. i.
    rewrite Memory.bot_get.
    destruct (Loc.eq_dec loc l); subst; ss.
    symmetry in PROMISES1.
    exploit sim_memory_get_None_src; eauto.
    rewrite PROMISES_TGT. rewrite Memory.bot_get. ss.
  Qed.

  Lemma sim_thread_terminal
        l r e_src e_tgt
        (SIM: sim_thread l r e_src e_tgt)
        (TERMINAL_TGT: (Language.is_terminal lang) (Thread.state e_tgt)):
    <<TERMINAL_SRC: (Language.is_terminal lang) (Thread.state e_src)>>.
  Proof.
    unfold Language.is_terminal in *. ss.
    unfold State.is_terminal in *.
    inv SIM.
    clear - TERMINAL_TGT STATE.
    destruct e_src, e_tgt. ss.
    destruct state, state0. ss.
    unfold sim_state in *. des; inv STATE; ss.
    unfold promote_stmts in *.
    destruct stmts; ss. destruct t; ss.
    destruct i; ss; des_ifs; ss.
  Qed.


  (* certification *)

  Lemma cap_sim_thread_reserve
        l r
        st_src lc_src sc_src mem_src
        st_tgt lc_tgt sc_tgt mem_tgt
        scm_src scm_tgt
        cap_src cap_tgt
        (SIM: sim_thread_reserve l r
                                 (Thread.mk lang st_src lc_src sc_src mem_src)
                                 (Thread.mk lang st_tgt lc_tgt sc_tgt mem_tgt))
        (WF_SRC: Local.wf lc_src mem_src)
        (WF_TGT: Local.wf lc_tgt mem_tgt)
        (CLOSED_SRC: Memory.closed mem_src)
        (CLOSED_TGT: Memory.closed mem_tgt)
        (CAP_SRC: Memory.cap mem_src cap_src)
        (CAP_TGT: Memory.cap mem_tgt cap_tgt)
        (SC_SRC: Memory.max_concrete_timemap cap_src scm_src)
        (SC_TGT: Memory.max_concrete_timemap cap_tgt scm_tgt):
    exists mem1_src,
      <<REMOVE: Memory.remove cap_src l (Memory.max_ts l mem_src)
                              (Time.incr (Memory.max_ts l mem_src)) Message.reserve mem1_src>> /\
      <<SIM: sim_thread_reserve l r
                                (Thread.mk lang st_src lc_src scm_src mem1_src)
                                (Thread.mk lang st_tgt lc_tgt scm_tgt cap_tgt)>> /\
      <<WF_SRC: Local.wf lc_src mem1_src>> /\
      <<SC_SRC: Memory.closed_timemap scm_src mem1_src>> /\
      <<CLOSED_SRC: Memory.closed mem1_src>>.
  Proof.
    exploit sim_memory_cap; try eapply SIM; eauto. i. des.
    hexploit sim_memory_max_concrete_timemap; try exact x0; eauto. i. des.
    exploit (@Memory.remove_exists cap_src l (Memory.max_ts l mem_src)
                                   (Time.incr (Memory.max_ts l mem_src)) Message.reserve);
      try apply CAP_SRC.
    i. des.
    assert (MAX: Memory.max_ts l mem2 = Memory.max_ts l mem_src).
    { inv SIM. ss. des.
      dup CAP_SRC. inv CAP_SRC0.
      exploit Memory.cap_max_ts; try exact CAP_SRC; eauto.
      instantiate (1 := l). i.
      exploit SOUND; try exact MEM. i.
      exploit Memory.remove_get1; try exact x; eauto. i. des.
      { specialize (Time.incr_spec (Memory.max_ts l mem_src)). i.
        rewrite <- LOCTS0 in *. timetac. }
      exploit Memory.max_ts_spec; try exact GET2. i. des.
      apply TimeFacts.antisym; ss.
      destruct (TimeFacts.le_lt_dec (Memory.max_ts l mem2) (Memory.max_ts l mem_src)); ss.
      exfalso.
      exploit Memory.max_ts_spec; try exact GET. i. des.
      revert GET0. erewrite Memory.remove_o; eauto. condtac; ss. des; ss. i.
      exploit Memory.cap_inv; try exact GET0; try exact CAP_SRC; eauto. i. des.
      - exploit Memory.max_ts_spec; try exact x4. i. des. timetac.
      - inv x3. exploit Memory.max_ts_spec; try exact GET3. i. des.
        exploit Memory.get_ts; try exact GET3. i. des.
        { rewrite x6 in *. inv l0. }
        { exploit TimeFacts.lt_le_lt; try exact x6; try exact MAX1. i. timetac. }
      - subst. ss.
    }
    esplits; eauto.
    - inv SIM. ss. des. econs; ss; eauto.
      + inv x0. econs; i.
        * revert GET_SRC.
          erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        * erewrite Memory.remove_o; eauto. condtac; ss; eauto.
          des. subst. ss.
      + des. ii.
        exploit FULFILLABLE; eauto. i. des. splits; ss.
        unfold prev_released_le_loc in *. des_ifs; ss; revert Heq.
        * erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
          exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; congr.
        * erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
          exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; congr.
        * erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
          exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; congr.
        * erewrite Memory.remove_o; eauto. condtac; ss. i. guardH o.
          exploit Memory.cap_inv; try exact CAP_SRC; eauto. i. des; congr.
      + rewrite MAX. inv CAP_SRC.
        exploit SOUND; try exact MEM. i.
        exploit Memory.remove_get1; try exact x; eauto. i. des.
        { specialize (Time.incr_spec (Memory.max_ts l mem_src)). i.
          rewrite <- LOCTS0 in *. timetac. }
        esplits; eauto.
        instantiate (1 := released).
        instantiate (1 := from').
        erewrite Memory.remove_o; eauto. condtac; ss; eauto.
        des. subst.
        exploit Memory.get_ts; try exact MEM. i. des.
        * specialize (Time.incr_spec (Memory.max_ts l mem_src)). i.
          rewrite x3 in H0. inv H0.
        * specialize (Time.incr_spec (Memory.max_ts l mem_src)). i.
          rewrite x3 in H0. timetac.
      + i. rewrite MAX in *. eauto.
      + ii. revert GET.
        erewrite Memory.remove_o; eauto. condtac; ss. des; ss. i.
        exploit Memory.cap_inv; try exact GET; try exact CAP_SRC; eauto. i. des; ss.
        eapply SAFE; eauto.
    - exploit Local.cap_wf; try exact CAP_SRC; eauto. i.
      inv x2. econs; ii; eauto.
      + inv TVIEW_CLOSED.
        econs; i; eauto using Memory.cancel_closed_view.
      + inv WF_SRC. exploit PROMISES0; eauto. i.
        erewrite Memory.remove_o; eauto. condtac; ss; cycle 1.
        { apply CAP_SRC. ss. }
        des. subst.
        exploit Memory.max_ts_spec; try exact x. i. des.
        specialize (Time.incr_spec (Memory.max_ts l mem_src)). i.
        exploit TimeFacts.le_lt_lt; try exact MAX0; try exact H0. i. timetac.
    - hexploit Memory.max_concrete_timemap_closed; try exact SC_SRC.
      eapply Memory.cancel_closed_timemap; eauto.
    - exploit Memory.cap_closed; try exact CAP_SRC; eauto. i.
      eapply Memory.cancel_closed; eauto.
  Qed.

  Lemma cap_sim_thread
        l r e_src e_tgt
        sc_src sc_tgt
        cap_src cap_tgt
        (SIM: sim_thread_reserve l r e_src e_tgt)
        (WF_SRC: Local.wf (Thread.local e_src) (Thread.memory e_src))
        (WF_TGT: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
        (CLOSED_SRC: Memory.closed (Thread.memory e_src))
        (CLOSED_TGT: Memory.closed (Thread.memory e_tgt))
        (CAP_SRC: Memory.cap (Thread.memory e_src) cap_src)
        (CAP_TGT: Memory.cap (Thread.memory e_tgt) cap_tgt)
        (SC_SRC: Memory.max_concrete_timemap cap_src sc_src)
        (SC_TGT: Memory.max_concrete_timemap cap_tgt sc_tgt):
    exists from e2_src mem_src,
      <<STEP: Thread.step true (ThreadEvent.promise l from (Memory.max_ts l (Thread.memory e_src)) Message.reserve Memory.op_kind_cancel)
                          (Thread.mk lang (Thread.state e_src) (Thread.local e_src) sc_src cap_src) e2_src>> /\
      <<SPACE: CompressSteps.spatial_mem (Thread.memory e2_src) mem_src>> /\
      <<SIM: sim_thread l r
                        (Thread.mk lang (Thread.state e2_src) (Thread.local e2_src) (Thread.sc e2_src) mem_src)
                        (Thread.mk lang (Thread.state e_tgt) (Thread.local e_tgt) sc_tgt cap_tgt)>> /\
      <<WF_SRC: Local.wf (Thread.local e2_src) mem_src>> /\
      <<SC_SRC: Memory.closed_timemap (Thread.sc e2_src) mem_src>> /\
      <<MEM_SRC: Memory.closed mem_src>>.
  Proof.
    destruct e_src as [st1_src lc1_src sc1_src mem1_src].
    destruct e_tgt as [st1_tgt lc1_tgt sc1_tgt mem1_tgt].
    ss.
    exploit cap_sim_thread_reserve; eauto. i. des.
    exploit step_reserve_sim_thread; try exact SIM0; eauto. i. des.
    assert (to = Memory.max_ts l mem1_src); subst.
    { inv SIM. ss. des.
      inv STEP; inv STEP0; inv LOCAL; inv LOCAL0. inv PROMISE0.
      exploit Memory.remove_get0; try exact PROMISES0. i. des.
      destruct (Time.eq_dec to (Memory.max_ts l mem1_src)); ss.
      exploit PROMISES; eauto. i. congr.
    }
    destruct e2_src as [st2_src lc2_src sc2_src mem2_src]. ss.
    cut (exists mem'_src,
            <<STEP': Thread.step true (ThreadEvent.promise l from (Memory.max_ts l mem1_src) Message.reserve Memory.op_kind_cancel)
                                 (Thread.mk lang st1_src lc1_src sc_src cap_src)
                                 (Thread.mk lang st1_src lc2_src sc_src mem'_src)>> /\
            <<SPACE: CompressSteps.spatial_mem mem'_src mem2_src>>).
    { i. des.
      exploit Thread.step_future; try exact STEP; eauto. s. i. des.
      inv STEP; inv STEP0; inv LOCAL. ss.
      esplits; try exact STEP'; eauto.
    }
    inv SIM. ss. des. dup CAP_SRC. inv CAP_SRC0.
    inv STEP; inv STEP0; inv LOCAL0. inv PROMISE0. ss.
    replace from0 with from in *; cycle 1.
    { exploit SOUND; try exact MEM. i.
      exploit Memory.remove_get0; try exact MEM0. i. des.
      revert GET. erewrite Memory.remove_o; eauto. condtac; ss. i.
      rewrite GET in *. inv x. ss. }
    exploit (@Memory.remove_exists cap_src l from (Memory.max_ts l mem1_src) Message.reserve).
    { exploit SOUND; try exact MEM. ss. }
    i. des. exists mem2. split.
    - econs 1. econs; eauto.
    - move MEM0 at bottom. move REMOVE at bottom.
      exploit (@Memory.add_exists mem2_src l (Memory.max_ts l mem1_src)
                                  (Time.incr (Memory.max_ts l mem1_src)) Message.reserve).
      { ii. revert GET2.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.remove_o; eauto. condtac; ss.
        i. des; ss.
        exploit Memory.remove_get0; try exact REMOVE. i. des.
        exploit Memory.get_disjoint; [exact GET2|exact GET|..]. i. des; eauto. }
      { apply Time.incr_spec. }
      { econs. }
      i. des.
      cut (mem2 = mem0).
      { i. subst. econs; eauto.
        destruct (TimeFacts.le_lt_dec (Memory.max_ts l mem1_src) (Memory.max_ts l mem2_src)); ss.
        inv CLOSED_SRC0. clear CLOSED0.
        specialize (INHABITED l).
        exploit Memory.remove_get1; try exact INHABITED; eauto. i. des.
        { rewrite <- LOCTS0 in *.
          inv CLOSED_SRC. rewrite INHABITED0 in *. congr. }
        exploit Memory.max_ts_spec; try exact GET2. i. des.
        revert GET.
        erewrite Memory.remove_o; eauto. condtac; ss.
        erewrite Memory.remove_o; eauto. condtac; ss.
        des; ss. i.
        exploit Memory.cap_inv; try exact GET; try exact CAP_SRC; eauto. i. des.
        - exploit Memory.max_ts_spec; try exact x2. i. des.
          exploit TimeFacts.antisym; [exact l0|exact MAX0|..]. i. congr.
        - inv x3. exploit Memory.get_ts; try exact GET0. i. des.
          + subst. rewrite x3 in *. inv x4.
          + exploit Memory.max_ts_spec; try exact GET0. i. des.
            rewrite l0 in MAX0.
            exploit TimeFacts.lt_le_lt; try exact x3; try exact MAX0. i. timetac.
        - subst. rewrite x4 in *. ss.
      }
      apply Memory.ext. i.
      erewrite Memory.remove_o; eauto. condtac; ss.
      + des. subst.
        erewrite Memory.add_o; eauto. condtac; ss.
        * des. specialize (Time.incr_spec (Memory.max_ts l mem1_src)). i.
          rewrite <- a0 in *. timetac.
        * des; ss.
          exploit Memory.remove_get0; try exact MEM0. i. des. ss.
      + erewrite (@Memory.add_o mem0); eauto. condtac; ss.
        * des; ss. subst.
          exploit Memory.remove_get0; try exact REMOVE. i. des. ss.
        * erewrite (@Memory.remove_o mem2_src); eauto. condtac; ss.
          erewrite (@Memory.remove_o mem1_src0); eauto. condtac; ss.
  Qed.

  Lemma sim_thread_reserve_consistent
        l r e_src e_tgt
        (SIM: sim_thread_reserve l r e_src e_tgt)
        (WF_SRC: Local.wf (Thread.local e_src) (Thread.memory e_src))
        (WF_TGT: Local.wf (Thread.local e_tgt) (Thread.memory e_tgt))
        (SC_SRC: Memory.closed_timemap (Thread.sc e_src) (Thread.memory e_src))
        (SC_TGT: Memory.closed_timemap (Thread.sc e_tgt) (Thread.memory e_tgt))
        (CLOSED_SRC: Memory.closed (Thread.memory e_src))
        (CLOSED_TGT: Memory.closed (Thread.memory e_tgt))
        (CONSISTENT_TGT: Thread.consistent e_tgt):
    <<CONSISTENT_SRC: Thread.consistent e_src>>.
  Proof.
    exploit Memory.cap_exists; try exact CLOSED_TGT. i. des.
    exploit Memory.cap_closed; eauto. i.
    exploit Memory.max_concrete_timemap_exists; try apply x0. i. des.
    ii. rename mem1 into cap_src, mem2 into cap_tgt.
    exploit Local.cap_wf; try exact WF_SRC; eauto. intro WF_CAP_SRC.
    exploit Local.cap_wf; try exact WF_TGT; eauto. intro WF_CAP_TGT.
    hexploit Memory.max_concrete_timemap_closed; try exact x1. intro SCM_TGT.
    hexploit Memory.max_concrete_timemap_closed; try exact SC_MAX. intro SCM_SRC.
    exploit Memory.cap_closed; try exact CAP0; eauto. i.
    exploit cap_sim_thread; try exact SIM; eauto. i. des.
    exploit Thread.step_future; try exact STEP; eauto. s. i. des.
    exploit CONSISTENT_TGT; eauto. i. des.
    - left. unfold Thread.steps_failure in *. des.
      exploit sim_thread_plus_step; try exact STEPS; eauto. s. i. des.
      exploit (@CompressSteps.compress_steps_failure
                 lang e2_src
                 (Thread.mk lang (Thread.state e2_src) (Thread.local e2_src) (Thread.sc e2_src) mem_src)); eauto.
      { econs; eauto. }
      { unfold Thread.steps_failure.
        inv STEP_SRC; ss. destruct e_src0; ss.
        destruct pf; try by inv STEP0; inv STEP1.
        esplits; eauto. }
      unfold Thread.steps_failure. i. des.
      esplits; [|exact FAILURE].
      econs 2.
      + econs; [econs; exact STEP|]. ss.
      + ss.
    - right.
      exploit sim_thread_rtc_tau_step; try exact STEPS; eauto. i. des.
      exploit (@CompressSteps.compress_steps_fulfill
                 lang e2_src
                 (Thread.mk lang (Thread.state e2_src) (Thread.local e2_src) (Thread.sc e2_src) mem_src)); eauto.
      { econs; eauto. }
      { inv SIM2. apply Memory.ext. i.
        rewrite Memory.bot_get.
        destruct (Loc.eq_dec loc l); subst; ss.
        inv LOCAL. eapply sim_memory_get_None_tgt; eauto.
        rewrite PROMISES. apply Memory.bot_get. }
      i. des.
      esplits; [|exact PROMISES_SRC].
      econs 2.
      + econs; [econs; exact STEP|]. ss.
      + ss.
  Qed.
End SimThreadPromotion.
