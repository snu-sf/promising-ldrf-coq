Require Import Bool.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import List.

Require Import Debt.

Set Implicit Arguments.

Program Instance option_rel_PreOrder A R `{@PreOrder A R}: PreOrder (option_rel R).
Next Obligation.
Proof.
  ii. destruct x; ss. refl.
Qed.
Next Obligation.
Proof.
  ii. destruct x, y, z; ss. etrans; eauto.
Qed.

Program Instance Forall2_PreOrder A R `{@PreOrder A R}: PreOrder (Forall2 R).
Next Obligation.
Proof.
  ii. induction x; econs; auto. refl.
Qed.
Next Obligation.
Proof.
  intros x. induction x.
  { ii. inv H0; inv H1. econs. }
  { ii. inv H0; inv H1. econs; eauto. etrans; eauto. }
Qed.


Module SeqEvent.
  Variant t: Set :=
  | read
      (loc: Loc.t) (val: Const.t) (ord: Ordering.t)
      (d: diffs) (c: SeqCell.t)
  | write
      (loc: Loc.t) (val: Const.t) (ord: Ordering.t)
      (d: diffs) (c: SeqCell.t) (m_released: option SeqMemory.t)
  | update
      (loc: Loc.t) (valr: Const.t) (valw: Const.t) (ordr: Ordering.t) (ordw: Ordering.t)
      (d: diffs) (c: SeqCell.t) (m_released: option SeqMemory.t)
  | fence
      (ordr: Ordering.t) (ordw: Ordering.t)
      (d: diffs) (m_released: option SeqMemory.t)
  | syscall
      (e: Event.t)
      (d: diffs) (f: Flags.t) (m_released: SeqMemory.t)
  .

  Definition get_event (e: ProgramEvent.t) (m: SeqMemory.t) (d: diffs) (m_released: option SeqMemory.t): option t :=
    match e with
    | ProgramEvent.silent | ProgramEvent.failure => None
    | ProgramEvent.read loc val ord =>
      Some (read loc val ord d (m loc))
    | ProgramEvent.write loc val ord =>
      let m_released := if Ordering.le Ordering.strong_relaxed ord
                        then m_released
                        else None in
      Some (write loc val ord d (m loc) m_released)
    | ProgramEvent.update loc valr valw ordr ordw =>
      let m_released := if Ordering.le Ordering.strong_relaxed ordw
                        then m_released
                        else None in
      Some (update loc valr valw ordr ordw d (m loc) m_released)
    | ProgramEvent.fence ordr ordw =>
      let m_released := if Ordering.le Ordering.strong_relaxed ordw
                        then m_released
                        else None in
      Some (fence ordr ordw d m_released)
    | ProgramEvent.syscall e =>
      let f := (SeqMemory.flags m) in
      match m_released with
      | None => None
      | Some m_released =>
        Some (syscall e d f m_released)
      end
    end.

  Variant le: t -> t -> Prop :=
  | le_read
      loc val ord d c0 c1
      (CELL: SeqCell.le c0 c1)
    :
      le (read loc val ord d c0) (read loc val ord d c1)
  | le_write
      loc val ord d c0 c1 m0 m1
      (CELL: SeqCell.le c0 c1)
      (RELEASED: option_rel SeqMemory.le m0 m1)
    :
      le (write loc val ord d c0 m0) (write loc val ord d c1 m1)
  | le_update
      loc valr valw ordr ordw d c0 c1 m0 m1
      (CELL: SeqCell.le c0 c1)
      (RELEASED: option_rel SeqMemory.le m0 m1)
    :
      le (update loc valr valw ordr ordw d c0 m0) (update loc valr valw ordr ordw d c1 m1)
  | le_fence
      ordr ordw d m0 m1
      (RELEASED: option_rel SeqMemory.le m0 m1)
    :
      le (fence ordr ordw d m0) (fence ordr ordw d m1)
  | le_syscall
      e d f0 f1 m0 m1
      (RELEASED: SeqMemory.le m0 m1)
    :
      le (syscall e d f0 m0) (syscall e d f1 m1)
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. destruct x; econs; refl.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0; econs; etrans; eauto.
  Qed.
End SeqEvent.


Module SeqTrace.
  Variant t: Set :=
  | term (es: list SeqEvent.t) (m: SeqMemory.t)
  | partial (es: list SeqEvent.t) (f: Flags.t)
  | ub (es: list SeqEvent.t)
  .

  Definition cons (e: SeqEvent.t) (tr: t): t :=
    match tr with
    | term es m => term (e::es) m
    | partial es f => partial (e::es) f
    | ub es => ub (e::es)
    end.

  Definition cons_opt (e: option SeqEvent.t) (tr: t): t :=
    match e with
    | Some e => cons e tr
    | None => tr
    end.

  Variant le: t -> t -> Prop :=
  | le_term
      es_src es_tgt m_src m_tgt
      (EVENTS: Forall2 SeqEvent.le es_tgt es_src)
      (MEMORY: SeqMemory.le m_tgt m_src)
    :
      le (term es_tgt m_tgt) (term es_src m_src)
  | le_pterm
      es_src es_tgt f_src f_tgt
      (EVENTS: exists es_hd es_tl,
          (<<APP: es_src = es_hd ++ es_tl>>) /\
          (<<FORALL: Forall2 SeqEvent.le es_tgt es_hd>>))
      (FLAGS: Flags.le f_tgt f_src)
    :
      le (partial es_tgt f_tgt) (partial es_src f_src)
  | le_ub
      es_src tr_tgt
    :
      le tr_tgt (ub es_src)
  .

  Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. destruct x.
    { econs 1; refl. }
    { econs 2; [|refl]. exists es, []. splits; [|refl].
      rewrite app_nil_r. auto. }
    { econs 3. }
  Qed.
  Next Obligation.
  Proof.
    ii. inv H; inv H0.
    { econs 1; eauto.
      { etrans; eauto. }
      { etrans; eauto. }
    }
    { econs 3. }
    { des; subst.
      eapply Forall2_app_inv_l in FORALL. des; subst.
      econs 2.
      { eexists l1', (l2' ++ es_tl). splits.
        { rewrite app_assoc. auto. }
        { etrans; eauto. }
      }
      { etrans; eauto. }
    }
    { econs 3. }
    { econs 3. }
  Qed.

  Definition incl (b0: t -> Prop) (b1: t -> Prop): Prop :=
    forall tr0, b0 tr0 -> exists tr1, b1 tr1 /\ le tr0 tr1.

  Program Instance incl_PreOrder: PreOrder incl.
  Next Obligation.
  Proof.
    ii. exists tr0. split; auto. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. apply H in H1. des. apply H0 in H1. des.
    esplits; eauto. etrans; eauto.
  Qed.
End SeqTrace.


Module SeqBehavior.
Section LANG.
  Variable lang: language.

  Inductive behavior: forall (th0: SeqThread.t lang) (tr: SeqTrace.t), Prop :=
  | behavior_term
      st m p o
      (TERMINAL: lang.(Language.is_terminal) st)
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) (SeqTrace.term [] m)
  | behavior_partial
      st m p o
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) (SeqTrace.partial [] (SeqMemory.flags m))
  | behavior_ub
      st m p o
      (FAILURE: SeqThread.failure (SeqThread.mk (SeqState.mk _ st m) p o))
    :
      behavior (SeqThread.mk (SeqState.mk _ st m) p o) (SeqTrace.ub [])
  | behavior_na_step
      th0 th1 tr
      (STEP: SeqThread.na_step MachineEvent.silent th0 th1)
      (BEHAVIOR: behavior th1 tr)
    :
      behavior th0 tr
  | behavior_at_step
      th0 th1 pe d m_released e tr
      (STEP: SeqThread.at_step pe d m_released th0 th1)
      (EVENT: SeqEvent.get_event pe th0.(SeqThread.state).(SeqState.memory) d m_released = Some e)
      (BEHAVIOR: behavior th1 tr)
    :
      behavior th0 (SeqTrace.cons e tr)
  .
End LANG.

Definition refine
           (lang_tgt lang_src: language)
           (st_tgt: lang_tgt.(Language.state)) (st_src: lang_src.(Language.state))
  : Prop :=
  forall o p vals (WF: Oracle.wf o),
    SeqTrace.incl
      (behavior (SeqThread.mk (SeqState.mk _ st_tgt (SeqMemory.init vals)) p o))
      (behavior (SeqThread.mk (SeqState.mk _ st_src (SeqMemory.init vals)) p o)) .
End SeqBehavior.


Section DETERMINISM.
  Variable lang: language.

  Definition similar (e0 e1: ProgramEvent.t): Prop :=
    e0 = e1 \/
    match e0, e1 with
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.write loc1 val1 ord1 =>
      loc0 = loc1 /\ ord0 = ord1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ ordr0 = ordr1 /\ ordw0 = ordw1 /\ (valr0 = valr1 -> valw0 = valw1)
    | ProgramEvent.read loc0 val0 ord0, ProgramEvent.update loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ val0 <> valr1
    | ProgramEvent.update loc0 valr0 valw0 ordr0 ordw0, ProgramEvent.read loc1 val1 ord1 =>
      loc0 = loc1 /\ valr0 <> val1
    | _, _ => False
    end.

  Variant _deterministic (deterministic: lang.(Language.state) -> Prop) (st0: lang.(Language.state)): Prop :=
  | deterministic_intro
      (PRESERVE:
         forall e st1 (STEP: lang.(Language.step) e st0 st1),
           deterministic st1)
      (STEP_TERMINAL:
         forall e st1 (STEP: lang.(Language.step) e st0 st1)
                (TERMINAL: lang.(Language.is_terminal) st0), False)
      (STEP_STEP:
         forall e1 st1 (STEP1: lang.(Language.step) e1 st0 st1)
                e2 st2 (STEP2: lang.(Language.step) e2 st0 st2),
           similar e1 e2 /\ (e1 = e2 -> st1 = st2))
  .

  Lemma deterministic_mon: monotone1 _deterministic.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.
  Hint Resolve deterministic_mon: paco.

  Definition deterministic := paco1 _deterministic bot1.
End DETERMINISM.
#[export] Hint Resolve deterministic_mon: paco.


Section ADEQUACY.
  Variable lang_src lang_tgt: language.

  Theorem refinement_imply_simulation
          (st_src: lang_src.(Language.state)) (st_tgt: lang_tgt.(Language.state))
          (DETERM: deterministic _ st_src)
          (REFINE: SeqBehavior.refine _ _ st_tgt st_src)
    :
      sim_seq_all _ _ (fun _ _ => True) st_src st_tgt.
  Proof.
  Admitted.
End ADEQUACY.
