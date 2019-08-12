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

Require Import Invariant.

Require Import GSimulation.

Set Implicit Arguments.


Section AssertInsertion.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp)
    (program: IdentMap.t {lang:language & lang.(Language.syntax)}).

  Context `{LOGIC: Logic.t S J program}.


  (* simulation relations *)

  Inductive sim_stmts (tid: Ident.t): forall (stmts_src stmts_tgt: list Stmt.t), Prop :=
  | sim_stmts_nil:
      sim_stmts tid [] []
  | sim_stmts_instr
      (i: Instr.t) stmts_src stmts_tgt
      (SIM: sim_stmts tid stmts_src stmts_tgt):
      sim_stmts tid ((Stmt.instr i)::stmts_src) ((Stmt.instr i)::stmts_tgt)
  | sim_stmts_ite
      cond
      stmts1_src stmts2_src stmts_src
      stmts1_tgt stmts2_tgt stmts_tgt
      (SIM1: sim_stmts tid stmts1_src stmts1_tgt)
      (SIM2: sim_stmts tid stmts2_src stmts2_tgt)
      (SIM: sim_stmts tid stmts_src stmts_tgt):
      sim_stmts tid
                ((Stmt.ite cond stmts1_src stmts2_src)::stmts_src)
                ((Stmt.ite cond stmts1_tgt stmts2_tgt)::stmts_tgt)
  | sim_stmts_dowhile
      cond
      stmts1_src stmts_src
      stmts1_tgt stmts_tgt
      (SIM1: sim_stmts tid stmts1_src stmts1_tgt)
      (SIM: sim_stmts tid stmts_src stmts_tgt):
      sim_stmts tid
                ((Stmt.dowhile stmts1_src cond)::stmts_src)
                ((Stmt.dowhile stmts1_tgt cond)::stmts_tgt)
  | sim_stmts_assert
      e stmts_src stmts_tgt
      (SIM: sim_stmts tid stmts_src stmts_tgt)
      (SUCCESS: forall rs (SOUND: S tid lang (State.mk rs stmts_src)),
          RegFile.eval_expr rs e <> 0):
      sim_stmts tid stmts_src ((Stmt.instr (Instr.assert e))::stmts_tgt)
  .
  Hint Constructors sim_stmts.

  Inductive sim_state (tid: Ident.t) (st_src st_tgt: State.t): Prop :=
  | sim_state_intro
      (STMTS: sim_stmts tid st_src.(State.stmts) st_tgt.(State.stmts))
      (REGS: forall reg, st_src.(State.regs) reg = st_tgt.(State.regs) reg)
  .
  Hint Constructors sim_state.

  Inductive sim_thread (tid: Ident.t) (e_src e_tgt: Thread.t lang): Prop :=
  | sim_thread_intro
      (STATE: sim_state tid e_src.(Thread.state) e_tgt.(Thread.state))
      (LOCAL: e_src.(Thread.local) = e_tgt.(Thread.local))
      (SC: e_src.(Thread.sc) = e_tgt.(Thread.sc))
      (MEMORY: e_src.(Thread.memory) = e_tgt.(Thread.memory))
  .
  Hint Constructors sim_thread.

  Inductive sim_conf (c_src c_tgt: Configuration.t): Prop :=
  | sim_conf_intro
      (SEM: sem S J c_src)
      (TIDS: Threads.tids c_src.(Configuration.threads) = Threads.tids c_tgt.(Configuration.threads))
      (FIND_SRC: forall tid l st_src lc_src
                   (FIND: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ l st_src, lc_src)),
          l = lang)
      (FIND_TGT: forall tid l st_tgt lc_tgt
                   (FIND: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ l st_tgt, lc_tgt)),
          l = lang)
      (THREADS: forall tid st_src lc_src st_tgt lc_tgt
                  (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
                  (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)),
          <<STATE: sim_state tid st_src st_tgt>> /\
          <<LOCAL: lc_src = lc_tgt>>)
      (SC: c_src.(Configuration.sc) = c_tgt.(Configuration.sc))
      (MEMORY: c_src.(Configuration.memory) = c_tgt.(Configuration.memory))
  .
  Hint Constructors sim_conf.


  (* lemmas on simulation relations *)

  Lemma tids_find
        ths_src ths_tgt tid
        (TIDS: Threads.tids ths_src = Threads.tids ths_tgt):
    (exists lang_src st_src lc_src, IdentMap.find tid ths_src = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt, IdentMap.find tid ths_tgt = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    split; i; des.
    - destruct (IdentSet.mem tid (Threads.tids ths_src)) eqn:MEM.
      + rewrite TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
    - destruct (IdentSet.mem tid (Threads.tids ths_tgt)) eqn:MEM.
      + rewrite <- TIDS in MEM.
        rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_src); ss.
        destruct p. destruct s. esplits; eauto.
      + rewrite Threads.tids_o in MEM.
        destruct (IdentMap.find tid ths_tgt); ss.
  Qed.

  Lemma sim_conf_find
        c_src c_tgt tid
        (SIM: sim_conf c_src c_tgt):
    (exists lang_src st_src lc_src,
        IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang_src st_src, lc_src)) <->
    (exists lang_tgt st_tgt lc_tgt,
        IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang_tgt st_tgt, lc_tgt)).
  Proof.
    inv SIM. destruct c_src, c_tgt. ss.
    eapply tids_find; eauto.
  Qed.

  Lemma sim_conf_sim_thread
        c_src c_tgt
        tid st_src lc_src st_tgt lc_tgt
        (SIM: sim_conf c_src c_tgt)
        (FIND_SRC: IdentMap.find tid c_src.(Configuration.threads) = Some (existT _ lang st_src, lc_src))
        (FIND_TGT: IdentMap.find tid c_tgt.(Configuration.threads) = Some (existT _ lang st_tgt, lc_tgt)):
    sim_thread tid
               (Thread.mk lang st_src lc_src c_src.(Configuration.sc) c_src.(Configuration.memory))
               (Thread.mk lang st_tgt lc_tgt c_tgt.(Configuration.sc) c_tgt.(Configuration.memory)).
  Proof.
    inv SIM. exploit THREADS; eauto. i. des.
    econs; eauto.
  Qed.


  Theorem sim_conf_sim
          c_src c_tgt
          (SIM: sim_conf c_src c_tgt):
    sim c_src c_tgt.
  Proof.
    revert c_src c_tgt SIM.
    pcofix CIH. i. pfold. econs; ii.
    { (* terminal *)
      exploit sim_conf_find; eauto. i. des.
      exploit x0; eauto. i. des.
      inv SIM. ss.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      exploit THREADS; eauto. i. des. subst.
      exploit TERMINAL_TGT; eauto. i. des.
      split; auto.
      destruct st, st_tgt; ss. inv STATE0. ss. subst.
      inv STATE. inv STMTS. ss.
    }
    inv STEP_TGT.
    { (* abort step *)
      exploit sim_conf_find; eauto. i. des.
      exploit x1; eauto. i. des. clear x0 x1.
      destruct c_src as [ths1_src sc1_src mem1_src].
      destruct c_tgt as [ths1_tgt sc1 mem1].
      dup SIM. inv SIM0. ss. subst.
      exploit FIND_SRC; eauto. i. subst.
      exploit FIND_TGT; eauto. i. subst.
      clear FIND_SRC FIND_TGT THREADS.
      exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
      admit.
    }
    (* normal step *)
    exploit sim_conf_find; eauto. i. des.
    exploit x1; eauto. i. des. clear x0 x1.
    destruct c_src as [ths1_src sc1_src mem1_src].
    destruct c_tgt as [ths1_tgt sc1 mem1].
    dup SIM. inv SIM0. ss. subst.
    exploit FIND_SRC; eauto. i. subst.
    exploit FIND_TGT; eauto. i. subst.
    clear FIND_SRC FIND_TGT THREADS.
    exploit sim_conf_sim_thread; eauto. s. intro SIM_TH.
    dup WF_TGT. inv WF_TGT0. inv WF. ss.
    exploit THREADS; try eauto. s. intro WF.
    clear DISJOINT. clear THREADS.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    exploit Memory.cap_exists; try exact CLOSED0. i. des.
    exploit Memory.cap_closed; eauto. intro CLOSED_CAP.
    exploit Local.cap_wf; try exact WF0; eauto. intro WF_CAP.
    exploit Memory.max_full_timemap_exists; try apply CLOSED_CAP. i. des.
    hexploit Memory.max_full_timemap_closed; try exact x1; eauto. intro SC_MAX.
    exploit CONSISTENT; eauto. s. i. des.
    { (* normal certification *)
      admit.
    }
    { (* abort certification *)
      admit.
    }
  Admitted.
End AssertInsertion.
