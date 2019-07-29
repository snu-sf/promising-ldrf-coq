Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Require Import PromiseConsistent.

Set Implicit Arguments.


Module PFStepCommon.
  Inductive sim_promises (promises_src promises_tgt: Memory.t): Prop :=
  | sim_promises_intro
      (SOUND: forall loc from to msg_src
                (GET_SRC: Memory.get loc to promises_src = Some (from, msg_src)),
          exists msg_tgt,
            <<GET_TGT: Memory.get loc to promises_tgt = Some (from, msg_tgt)>>)
      (COMPLETE: forall loc from to msg
                   (GET_TGT: Memory.get loc to promises_tgt = Some (from, msg)),
          <<GET_SRC: Memory.get loc to promises_src = Some (from, Message.half)>>)
  .

  Inductive sim_local (lc_src lc_tgt: Local.t): Prop :=
  | sim_local_intro
      (TVIEW: TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMISES: sim_promises lc_src.(Local.promises) lc_tgt.(Local.promises))
  .

  Inductive sim_message: forall (msg_src msg_tgt: Message.t), Prop :=
  | sim_message_full
      val released_src released_tgt
      (RELEASED: View.opt_le released_src released_tgt):
      sim_message (Message.full val released_src) (Message.full val released_tgt)
  | sim_message_half:
      sim_message Message.half Message.half
  .
  Hint Constructors sim_message.

  Program Instance sim_message_PreOrder: PreOrder sim_message.
  Next Obligation.
    ii. destruct x; econs; refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; econs. etrans; eauto.
  Qed.

  Definition vals_incl (mem1 mem2: Memory.t): Prop :=
    forall loc from to val released
      (GET1: Memory.get loc to mem1 = Some (from, Message.full val released)),
    exists f t v r,
      <<GET2: Memory.get loc t mem2 = Some (f, Message.full v r)>>.

  Program Instance vals_incl_PreOrder: PreOrder vals_incl.
  Next Obligation.
    ii. eauto.
  Qed.
  Next Obligation.
    ii. exploit H; eauto. i. des. eauto.
  Qed.

  Lemma sim_promises_get_src
        promises_src promises_tgt
        loc from to msg_src
        (PROMISES: sim_promises promises_src promises_tgt)
        (GET_SRC: Memory.get loc to promises_src = Some (from, msg_src)):
    exists msg_tgt,
      <<GET_TGT: Memory.get loc to promises_tgt = Some (from, msg_tgt)>> /\
      <<MSG: msg_src = Message.half>>.
  Proof.
    inv PROMISES.
    exploit SOUND; eauto. i. des.
    exploit COMPLETE; eauto. i. des.
    rewrite GET_SRC in x. inv x.
    esplits; eauto.
  Qed.


  (* lemmas on step *)

  Lemma fence_step
        lc1_src sc1_src mem1_src
        lc1_tgt sc1_tgt mem1_tgt ordr ordw lc2_tgt sc2_tgt
        (LOCAL1: sim_local lc1_src lc1_tgt)
        (SC1: TimeMap.le sc1_src sc1_tgt)
        (WF1_SRC: Local.wf lc1_src mem1_src)
        (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
        (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr ordw lc2_tgt sc2_tgt):
    exists lc2_src sc2_src,
      <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr ordw lc2_src sc2_src>> /\
      <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
      <<SC2: TimeMap.le sc2_src sc2_tgt>>.
  Proof.
    esplits.
    - econs; eauto. ii. inv LOCAL1.
      exploit sim_promises_get_src; eauto. i. des. subst. ss.
    - inv STEP_TGT. inv LOCAL1. econs; eauto. ss.
      eapply TViewFacts.write_fence_tview_mon; try refl; ss.
      + eapply TViewFacts.read_fence_tview_mon; try refl; ss.
        apply WF1_TGT.
      + eapply TViewFacts.read_fence_future; apply WF1_SRC.
    - inv STEP_TGT. inv LOCAL1.
      eapply TViewFacts.write_fence_sc_mon; try refl; ss.
      eapply TViewFacts.read_fence_tview_mon; try refl; ss.
      apply WF1_TGT.
  Qed.


  (* existence of sim_promises *)

  Inductive sim_promises_aux (dom: list (Loc.t * Time.t)) (promises_src promises_tgt: Memory.t): Prop :=
  | sim_promises_aux_intro
      (SOUND: forall loc from to msg_src
                (GET_SRC: Memory.get loc to promises_src = Some (from, msg_src)),
          List.In (loc, to) dom /\
          exists msg_tgt, Memory.get loc to promises_tgt = Some (from, msg_tgt))
      (COMPLETE: forall loc from to msg_tgt
                   (IN: List.In (loc, to) dom)
                   (GET_TGT: Memory.get loc to promises_tgt = Some (from, msg_tgt)),
          Memory.get loc to promises_src = Some (from, Message.half))
  .

  Lemma sim_promises_aux_exists
        dom promises_tgt
        (BOT: Memory.bot_none promises_tgt):
    exists promises_src,
      sim_promises_aux dom promises_src promises_tgt.
  Proof.
    induction dom.
    { exists Memory.bot. econs; ss. i.
      rewrite Memory.bot_get in *. ss. }
    des. destruct a as [loc to]. inv IHdom.
    destruct (Memory.get loc to promises_tgt) as [[from msg]|] eqn:GETT; cycle 1.
    { exists promises_src. econs; i.
      - exploit SOUND; eauto. i. des.
        esplits; eauto. econs 2. ss.
      - inv IN.
        + inv H. congr.
        + exploit COMPLETE; eauto.
    }
    destruct (Memory.get loc to promises_src) as [[from_src msg_src]|] eqn:GETS.
    - exploit SOUND; eauto. i. des.
      rewrite GETT in x0. inv x0.
      exists promises_src. econs; i.
      + exploit SOUND; try exact GET_SRC. i. des.
        esplits; eauto. econs 2. ss.
      + inv IN.
        * inv H. exploit COMPLETE; try exact GET_TGT; eauto.
        * exploit COMPLETE; try exact GET_TGT; eauto.
    - exploit (@Memory.add_exists promises_src loc from to Message.half); ii.
      { exploit SOUND; eauto. i. des.
        exploit Memory.get_disjoint; [exact GETT|exact x1|..].
        i. des; eauto; congr. }
      { exploit Memory.get_ts; try exact GETT. i. des; ss.
        subst. rewrite BOT in GETT. ss. }
      { econs. }
      des. exists mem2. econs; i.
      + revert GET_SRC. erewrite Memory.add_o; eauto. condtac; ss.
        * i. inv GET_SRC. des. subst. split; eauto.
        * i. guardH o. exploit SOUND; eauto. i. des.
          split; eauto.
      + inv IN.
        * inv H. rewrite GETT in GET_TGT. inv GET_TGT.
          exploit Memory.add_get0; eauto. i. des. ss.
        * exploit COMPLETE; eauto. i.
          erewrite Memory.add_o; eauto. condtac; ss.
          des. subst. rewrite GETT in GET_TGT. inv GET_TGT. ss.
  Qed.

  Lemma sim_promises_exists
        promises_tgt
        (BOT: Memory.bot_none promises_tgt):
    exists promises_src,
      sim_promises promises_src promises_tgt.
  Proof.
    destruct (Memory.finite promises_tgt).
    exploit (@sim_promises_aux_exists x promises_tgt); ss. i. des.
    exists promises_src. inv x1. econs; i.
    - exploit SOUND; eauto. i. des. eauto.
    - exploit COMPLETE; eauto.
  Qed.
End PFStepCommon.
