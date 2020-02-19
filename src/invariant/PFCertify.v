Require Import RelationClasses.
Require Import Coq.Lists.ListDec Decidable.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import PromiseConsistent.
Require Import MemoryMerge.

Require Import AMemory.
Require Import ALocal.
Require Import ATView.
Require Import AThread.

Require Import PFCommon.
Require Import PFStep.

Set Implicit Arguments.


Module PFCertify.
  Include PFStep.

  (* existence of sim *)

  Inductive sim_cell (promises cell_src cell_tgt: Cell.t): Prop :=
  | sim_cell_intro
      (SOUND: Cell.le cell_src cell_tgt)
      (COMPLETE1: forall to from msg
                   (GETP: Cell.get to promises = Some (from, msg))
                   (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = None>>)
      (COMPLETE2: forall to from msg
                   (GETP: Cell.get to promises = None)
                   (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = Some (from, msg)>>)
  .

  Inductive sim_cell_aux (dom: list Time.t) (promises cell_src cell_tgt: Cell.t): Prop :=
  | sim_cell_aux_intro
      (SOUND: Cell.le cell_src cell_tgt)
      (COMPLETE1: forall from to msg
                    (GETP: Cell.get to promises = Some (from, msg))
                    (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = None>>)
      (COMPLETE2: forall from to msg
                    (IN: List.In to dom)
                    (GETP: Cell.get to promises = None)
                    (GET_TGT: Cell.get to cell_tgt = Some (from, msg)),
          <<GET_SRC: Cell.get to cell_src = Some (from, msg)>>)
  .

  Definition vals_incl_cell (cell1 cell2: Cell.t): Prop :=
    forall from to val released
      (GET1: Cell.get to cell1 = Some (from, Message.concrete val released)),
    exists f t r,
      <<GET2: Cell.get t cell2 = Some (f, Message.concrete val r)>>.

  Program Instance vals_incl_cell_PreOrder: PreOrder vals_incl_cell.
  Next Obligation.
    ii. eauto.
  Qed.
  Next Obligation.
    ii. exploit H; eauto. i. des. eauto.
  Qed.

  Lemma cap_sim_cell_exists
        promises mem1_src mem1_tgt mem2_tgt
        (SIM: PFStep.sim_memory promises mem1_src mem1_tgt)
        (LE_TGT: Memory.le promises mem1_tgt)
        (FINITE_TGT: Memory.finite promises)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (CLOSED2_TGT: Memory.closed mem2_tgt)
        (CAP: Memory.cap mem1_tgt mem2_tgt):
    forall loc,
    exists cell_src,
      sim_cell (promises loc) cell_src (mem2_tgt loc) /\
      vals_incl_cell cell_src (mem1_src loc) /\
      Cell.le (mem1_src loc) cell_src.
  Proof.
    i.
    destruct (Cell.finite (mem2_tgt loc)).
    rename x into dom.
    cut (exists cell_src,
            sim_cell_aux dom (promises loc) cell_src (mem2_tgt loc) /\
            vals_incl_cell cell_src (mem1_src loc) /\
            Cell.le (mem1_src loc) cell_src).
    { i. des.
      exists cell_src. splits; auto.
      inv H0. econs; ii; eauto.
    }
    clear H. induction dom.
    { exists (mem1_src loc). splits; try refl.
      inv SIM. inv CAP. econs; ii; eauto.
      - eapply COMPLETE1; eauto.
      - ss.
    }
    des. rename a into to.
    destruct (In_decidable time_decidable to dom).
    { exists cell_src. splits; auto.
      inv IHdom. econs; ii; eauto; ss.
      inv IN; eauto.
    }
    destruct (Cell.get to (mem2_tgt loc)) as [[]|] eqn:GETT; cycle 1.
    { exists cell_src. splits; auto.
      inv IHdom. econs; ii; eauto; ss.
      inv IN; eauto. congr.
    }
    destruct (Cell.get to cell_src) as [[]|] eqn:GETS.
    { exists cell_src. splits; auto.
      inv IHdom. exploit SOUND; eauto. i.
      rewrite GETT in *. inv x.
      econs; ii; eauto; ss.
      inv IN; eauto.
      rewrite GET_TGT in *. inv GETT. ss.
    }
    destruct (Cell.get to (promises loc)) as [[]|] eqn:GETP.
    { exists cell_src. splits; auto.
      inv IHdom. econs; ii; eauto; ss.
      inv IN; eauto. congr.
    }
    destruct (Cell.get to (mem1_tgt loc)) as [[]|] eqn:GETT1.
    { inv SIM. exploit COMPLETE2; eauto. i. des.
      exploit IHdom1; eauto. i. congr.
    }
    exploit Memory.cap_inv; try exact CAP; eauto. i. des.
    { unfold Memory.get in *. congr. }
    { subst. clear x0.
      exploit (@Cell.add_exists cell_src t to Message.reserve).
      { ii. inv IHdom.
        exploit SOUND; try exact GET2. i.
        exploit Cell.get_disjoint; [exact GETT|exact x0|..]. i. des.
        - subst. congr.
        - eapply x4; eauto. }
      { exploit Cell.get_ts; try exact GETT. i. des; ss. }
      { econs. }
      i. des.
      exists cell2.
      splits; cycle 1.
      { etrans; eauto. ii. revert GET1.
        erewrite Cell.add_o; eauto. condtac; ss; eauto. }
      { ii. exploit Cell.add_get1; try exact x0; eauto. }
      inv IHdom. econs; ii; eauto; ss.
      - revert LHS.
        erewrite Cell.add_o; eauto. condtac; ss; eauto.
        i. des. subst. inv LHS. ss.
      - erewrite Cell.add_o; eauto. condtac; ss; eauto.
        des. subst. congr.
      - des.
        + subst. rewrite GET_TGT in *. inv GETT.
          erewrite Cell.add_o; eauto. condtac; ss.
        + exploit COMPLETE2; eauto. i. des.
          eapply Cell.add_get1; eauto.
    }
    { subst. clear x0.
      exploit (@Cell.add_exists cell_src (Memory.max_ts loc mem1_tgt)
                                (Time.incr (Memory.max_ts loc mem1_tgt)) Message.reserve).
      { ii. inv IHdom. exploit SOUND; try exact GET2. i.
        exploit Memory.get_disjoint; [exact GETT|exact x0|..]. i. des.
        - subst. congr.
        - eapply x2; eauto. }
      { apply Time.incr_spec. }
      { inv CLOSED2_TGT. exploit CLOSED; try exact GETT. i. des. ss. }
      i. des.
      exists cell2.
      splits; cycle 1.
      { etrans; eauto. ii. revert GET1.
        erewrite Cell.add_o; eauto. condtac; ss; eauto. }
      { ii. exploit IHdom1; eauto. i.
        eapply Cell.add_get1; eauto. }
      { inv IHdom. econs; ii; eauto; ss.
        - revert LHS.
          erewrite Cell.add_o; eauto. condtac; ss; eauto.
          i. des. subst. inv LHS. ss.
        - erewrite Cell.add_o; eauto. condtac; ss; eauto.
          des. subst. congr.
        - des.
          + subst. rewrite GET_TGT in *. inv GETT.
            erewrite Cell.add_o; eauto. condtac; ss.
          + exploit COMPLETE2; eauto. i. des.
            eapply Cell.add_get1; eauto. }
    }
  Qed.

  Lemma cap_sim_memory_exists
        promises mem1_src mem1_tgt mem2_tgt
        (SIM: sim_memory promises mem1_src mem1_tgt)
        (LE_TGT: Memory.le promises mem1_tgt)
        (FINITE_TGT: Memory.finite promises)
        (CLOSED1_TGT: Memory.closed mem1_tgt)
        (CLOSED2_TGT: Memory.closed mem2_tgt)
        (CAP: Memory.cap mem1_tgt mem2_tgt):
    exists mem2_src,
      sim_memory promises mem2_src mem2_tgt /\
      vals_incl mem2_src mem1_src.
  Proof.
    cut (exists (caps_mem: Loc.t -> Cell.t),
            forall loc,
              (fun loc cap_cell =>
                 sim_cell (promises loc) cap_cell (mem2_tgt loc) /\
                 vals_incl_cell cap_cell (mem1_src loc))
                loc (caps_mem loc)).
    { i. des.
      exists (fun loc => caps_mem loc).
      split.
      - econs; ii; eauto.
        + destruct (H loc). inv H0. eauto.
        + destruct (H loc). inv H0. eapply COMPLETE1; eauto.
        + destruct (H loc). inv H0. eauto.
      - ii. destruct (H loc). eauto.
    }
    apply choice. intro loc.
    exploit cap_sim_cell_exists; eauto. i. des.
    instantiate (1 := loc) in x1.
    exists cell_src. ss.
  Qed.

  Lemma cap_sim_thread_exists
        lang e_src e_tgt
        sc1 mem1_tgt
        (SIM: @sim_thread lang e_src e_tgt)
        (WF1_TGT: Local.wf e_tgt.(Thread.local) e_tgt.(Thread.memory))
        (SC1_TGT: Memory.closed_timemap e_tgt.(Thread.sc) e_tgt.(Thread.memory))
        (MEM1_TGT: Memory.closed e_tgt.(Thread.memory))
        (SC_TGT: Memory.max_concrete_timemap mem1_tgt sc1)
        (CAP_TGT: Memory.cap e_tgt.(Thread.memory) mem1_tgt):
    exists mem1_src,
      <<SIM: sim_thread (Thread.mk lang e_src.(Thread.state) e_src.(Thread.local) sc1 mem1_src)
                        (Thread.mk lang e_tgt.(Thread.state) e_tgt.(Thread.local) sc1 mem1_tgt)>> /\
      <<VALS: vals_incl mem1_src e_src.(Thread.memory)>>.
  Proof.
    exploit Memory.cap_closed; eauto. i.
    exploit cap_sim_memory_exists; try apply SIM; try apply WF1_TGT; eauto. i. des.
    esplits; eauto.
    econs; eauto.
    - inv SIM. ss.
    - inv SIM. ss.
  Qed.

  Lemma sim_memory_bot
        promises mem_src mem_tgt
        (SIM: sim_memory promises mem_src mem_tgt)
        (PROMISES: promises = Memory.bot):
    mem_src = mem_tgt.
  Proof.
    inv SIM. apply Memory.ext. i.
    destruct (Memory.get loc ts mem_src) as [[]|] eqn:GETS.
    { exploit SOUND; eauto. }
    destruct (Memory.get loc ts mem_tgt) as [[]|] eqn:GETT; ss.
    exploit COMPLETE2; eauto; try congr.
    apply Memory.bot_get.
  Qed.
End PFCertify.
