Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.

Set Implicit Arguments.


Inductive opt E T (step: forall (e:option E) (tid:Ident.t) (c1 c2:T), Prop):
  forall (e:option E) (tid:Ident.t) (c1 c2:T), Prop :=
| step_none
    tid c:
    opt step None tid c c
| step_some
    e tid c1 c2
    (STEP: step e tid c1 c2):
    opt step e tid c1 c2
.
Hint Constructors opt.


Module Threads.
  Definition syntax := IdentMap.t {lang:Language.t & lang.(Language.syntax)}.
  Definition t := IdentMap.t ({lang:Language.t & lang.(Language.state)} * Local.t).

  Definition init (s:syntax): t :=
    IdentMap.map
      (fun s => (existT _ _ (s.(projT1).(Language.init) s.(projT2)), Local.init))
      s.

  Definition is_terminal (ths:t): Prop :=
    forall tid lang st lc (FIND: IdentMap.find tid ths = Some (existT Language.state lang st, lc)),
      <<STATE: lang.(Language.is_terminal) st>> /\
      <<THREAD: Local.is_terminal lc>>.

  Inductive wf (ths:t) (mem:Memory.t): Prop :=
  | wf_intro
      (DISJOINT:
         forall tid1 lang1 st1 lc1
           tid2 lang2 st2 lc2
           (TID: tid1 <> tid2)
           (TH1: IdentMap.find tid1 ths = Some (existT _ lang1 st1, lc1))
           (TH2: IdentMap.find tid2 ths = Some (existT _ lang2 st2, lc2)),
           Local.disjoint lc1 lc2)
      (THREADS: forall tid lang st lc
                  (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
          Local.wf lc mem)
  .

  Definition consistent (ths:t) (sc:TimeMap.t) (mem:Memory.t): Prop :=
    forall tid lang st lc
      (TH: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      Thread.consistent (Thread.mk lang st lc sc mem).

  Lemma init_wf syn: wf (init syn) Memory.init.
  Proof.
    econs.
    - i. unfold init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (UsualFMapPositive.UsualPositiveMap'.find tid1 syn); inv TH1.
      destruct (UsualFMapPositive.UsualPositiveMap'.find tid2 syn); inv TH2.
      econs. ss. econs. i. rewrite Memory.bot_get in *. congr.
    - i. unfold init in *. rewrite IdentMap.Facts.map_o in *.
      destruct (UsualFMapPositive.UsualPositiveMap'.find tid syn); inv TH.
      econs; ss.
      + apply TView.bot_wf.
      + apply TView.bot_closed.
      + ii. rewrite Memory.bot_get in LHS. congr.
      + apply Memory.bot_finite.
  Qed.

  Lemma init_consistent syn: consistent (init syn) TimeMap.bot Memory.init.
  Proof.
    ii. ss. esplits; eauto. s.
    unfold init in *. rewrite IdentMap.Facts.map_o in *.
    destruct (UsualFMapPositive.UsualPositiveMap'.find tid syn); inv TH. ss.
  Qed.

  Inductive is_promised tid (loc:Loc.t) (to:Time.t) (threads:t): Prop :=
  | is_promised_intro
      lang st lc from msg
      (TID: IdentMap.find tid threads = Some (existT _ lang st, lc))
      (PROMISES: Memory.get loc to lc.(Local.promises) = Some (from, msg))
  .

  Definition tids (ths: t): IdentSet.t :=
    List.fold_right (fun p s => IdentSet.add (fst p) s) IdentSet.empty (IdentMap.elements ths).

  Lemma tids_o tid ths:
    IdentSet.mem tid (tids ths) = IdentMap.find tid ths.
  Proof.
    unfold tids. rewrite IdentMap.Facts.elements_o.
    induction (IdentMap.elements ths); ss. destruct a. s.
    rewrite IdentSet.Facts.add_b, IHl.
    unfold IdentSet.Facts.eqb, IdentMap.Facts.eqb.
    repeat match goal with
           | [|- context[if ?c then true else false]] => destruct c
           end; ss; congr.
  Qed.

  Lemma tids_add
        tid lang st lc ths:
    tids (IdentMap.add tid (existT _ lang st, lc) ths) = IdentSet.add tid (tids ths).
  Proof.
    apply IdentSet.ext. i.
    rewrite IdentSet.Facts.add_b, ? tids_o.
    rewrite IdentMap.Facts.add_o. unfold IdentSet.Facts.eqb.
    repeat condtac; ss.
  Qed.

  Lemma is_terminal_spec ths:
    Threads.is_terminal ths <->
    forall tid lang st lc
      (TIDS: IdentSet.mem tid (tids ths))
      (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      lang.(Language.is_terminal) st /\ Local.is_terminal lc.
  Proof.
    unfold Threads.is_terminal. econs; i.
    - eapply H. eauto.
    - destruct (IdentMap.find tid ths) eqn:X; inv FIND.
      eapply H; eauto. rewrite tids_o, X. ss.
  Qed.
End Threads.


Module Configuration.
  Structure t := mk {
    threads: Threads.t;
    sc: TimeMap.t;
    memory: Memory.t;
  }.

  Definition init (s:Threads.syntax): t := mk (Threads.init s) TimeMap.bot Memory.init.

  Definition is_terminal (conf:t): Prop := Threads.is_terminal conf.(threads).

  Inductive wf (conf:t): Prop :=
  | wf_intro
      (WF: Threads.wf conf.(threads) conf.(memory))
      (SC: Memory.closed_timemap conf.(sc) conf.(memory))
      (MEM: Memory.closed conf.(memory))
      (HALF_WF: Memory.half_wf conf.(memory))
  .

  Definition consistent (conf:t): Prop :=
    Threads.consistent conf.(threads) conf.(sc) conf.(memory).

  Lemma init_wf syn: wf (init syn).
  Proof.
    econs.
    - apply Threads.init_wf.
    - viewtac.
    - apply Memory.init_closed.
    - apply Memory.init_half_wf.
  Qed.

  Lemma init_consistent syn: consistent (init syn).
  Proof.
    apply Threads.init_consistent.
  Qed.

  Inductive step: forall (e:option Event.t) (tid:Ident.t) (c1 c2:t), Prop :=
  | step_intro
      pf e tid c1 lang st1 lc1 e2 st3 lc3 sc3 memory3
      (TID: IdentMap.find tid c1.(threads) = Some (existT _ lang st1, lc1))
      (STEPS: rtc (@Thread.tau_step _) (Thread.mk _ st1 lc1 c1.(sc) c1.(memory)) e2)
      (STEP: Thread.step pf e e2 (Thread.mk _ st3 lc3 sc3 memory3))
      (CONSISTENT: consistent (mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(threads)) sc3 memory3)):
      step (ThreadEvent.get_event e) tid c1 (mk (IdentMap.add tid (existT _ _ st3, lc3) c1.(threads)) sc3 memory3)
  .

  Definition opt_step := opt step.

  Definition tau_step := union (step None).

  Inductive has_promise (c:t): Prop :=
  | has_promise_intro
      tid st lc loc from to msg
      (FIND: IdentMap.find tid c.(threads) = Some (st, lc))
      (GET: Memory.get loc to lc.(Local.promises) = Some (from, msg))
  .

  Ltac simplify :=
    repeat
      (try match goal with
           | [H: context[IdentMap.find _ (IdentMap.add _ _ _)] |- _] =>
             rewrite IdentMap.Facts.add_o in H
           | [H: context[if ?c then _ else _] |- _] =>
             destruct c
           | [H: Some _ = Some _ |- _] =>
             inv H
           | [H: (_, _) = (_, _) |- _] =>
             inv H
           | [H: existT ?P ?p _ = existT ?P ?p _ |- _] =>
             apply inj_pair2 in H
           | [H: existT ?P ?p _ = existT ?P ?q _ |- _] =>
             apply eq_sigT_sig_eq in H; inv H
           end;
       ss; subst).

  Lemma step_future
        e tid c1 c2
        (STEP: step e tid c1 c2)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1):
    <<WF2: wf c2>> /\
    <<CONSISTENT2: consistent c2>> /\
    <<SC_FUTURE: TimeMap.le c1.(sc) c2.(sc)>> /\
    <<MEM_FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    inv WF1. inv WF. inv STEP. s.
    exploit THREADS; ss; eauto. i.
    exploit Thread.rtc_tau_step_future; eauto. s. i. des.
    exploit Thread.step_future; eauto. s. i. des.
    splits; [|auto|by etrans; eauto|by etrans; eauto].
    econs; ss. econs.
    - i. simplify.
      + exploit THREADS; try apply TH1; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. s. i. des.
        symmetry. auto.
      + exploit THREADS; try apply TH2; eauto. i. des.
        exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
        exploit Thread.step_disjoint; eauto. i. des.
        auto.
      + eapply DISJOINT; [|eauto|eauto]. auto.
    - i. simplify.
      exploit THREADS; try apply TH; eauto. i.
      exploit Thread.rtc_tau_step_disjoint; eauto. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      auto.
  Qed.

  Lemma opt_step_future
        e tid c1 c2
        (STEP: opt_step e tid c1 c2)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1):
    <<WF2: wf c2>> /\
    <<CONSISTENT2: consistent c2>> /\
    <<SC_FUTURE: TimeMap.le c1.(sc) c2.(sc)>> /\
    <<MEM_FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    inv STEP.
    - splits; auto; refl.
    - eapply step_future; eauto.
  Qed.

  Lemma rtc_step_future
        c1 c2
        (STEPS: rtc tau_step c1 c2)
        (WF1: wf c1)
        (CONSISTENT1: consistent c1):
    <<WF2: wf c2>> /\
    <<CONSISTENT2: consistent c2>> /\
    <<SC_FUTURE: TimeMap.le c1.(sc) c2.(sc)>> /\
    <<MEM_FUTURE: Memory.future c1.(memory) c2.(memory)>>.
  Proof.
    revert CONSISTENT1. induction STEPS; i.
    - splits; auto; refl.
    - inv H.
      exploit step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des.
      splits; eauto; etrans; eauto.
  Qed.
End Configuration.
