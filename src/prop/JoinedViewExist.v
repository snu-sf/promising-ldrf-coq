Require Import Omega.
Require Import Bool.
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
Require Import Single.

Require Import SimMemory.
Require Import MemoryProps.
Require Import JoinedView.

Set Implicit Arguments.

Lemma times_sorted_split l0 l1
      (SORTED: times_sorted (l0++l1))
  :
    times_sorted l0 /\ times_sorted l1 /\
    (<<LT: forall x0 x1 (IN0: List.In x0 l0) (IN1: List.In x1 l1), Time.lt x0 x1>>).
Proof.
  remember (l0++l1). ginduction l.
  { i. destruct l0; ss. clarify. splits; auto. ss. }
  i. destruct l0; ss; clarify.
  { splits; eauto; ss. econs. }
  inv SORTED. eapply IHl in TL; ss. des. splits; auto.
  { econs; eauto.
    eapply List.Forall_forall. i. eapply List.Forall_forall in HD; eauto.
    eapply List.in_or_app; eauto.
  }
  ii. des; clarify; eauto.
  eapply List.Forall_forall; eauto. eapply List.in_or_app; eauto.
Qed.

Inductive message_from_to (mem: Memory.t) (loc: Loc.t):
  Time.t -> Time.t -> Prop :=
| message_from_to_intro
    from to val released
    (GET: Memory.get loc to mem = Some (from, Message.concrete val (Some released)))
  :
    message_from_to mem loc from to
.
Hint Constructors message_from_to.

Lemma message_from_to_ts mem (CLOSED: Memory.closed mem) loc:
  message_from_to mem loc <2= Time.lt.
Proof.
  ii. inv PR. dup GET.
  eapply memory_get_ts_strong in GET. des; clarify.
  inv CLOSED. rewrite INHABITED in GET0. ss.
Qed.

Lemma finite_sub_order_wf l
      (R: Time.t -> Time.t -> Prop) (LT: R <2= Time.lt)
      (INCL: forall ts0 ts1 (LT: R ts0 ts1), List.In ts1 l)
  :
    well_founded R.
Proof.
  revert l INCL.
  assert (forall n l
                 (LEN: length l = n)
                 (SORTED: times_sorted l)
                 (INCL: forall ts0 ts1
                               (IN: List.In ts1 l)
                               (LT: R ts0 ts1)
                               (EXIST: exists ts, R ts ts0),
                     List.In ts0 l),
             forall ts1 (IN: List.In ts1 l), Acc R ts1).
  { induction n.
    - i. destruct l; ss.
    - i. hexploit (list_match_rev l). i. des; clarify.
      erewrite List.app_length in LEN. ss.
      rewrite Nat.add_comm in LEN. ss. clarify.
      eapply times_sorted_split in SORTED. des. ss.
      econs. i. eapply NNPP.
      ii. eapply H0. econs. i. exfalso. eapply H0.
      exploit (INCL y ts1); eauto. i.
      eapply List.in_app_or in x0. ss; des; clarify.
      + eapply IHn; eauto. i. des.
        exploit (INCL ts0 ts2); eauto.
        { eapply List.in_or_app. auto. }
        { i. eapply List.in_app_or in x1. ss. des; clarify.
          exploit (LT0 ts2 ts0); eauto. i.
          eapply LT in LT1. exfalso. eapply Time.lt_strorder. etrans; eauto. }
      + eapply List.in_app_or in IN. ss. des; clarify.
        * eapply LT0 in IN; eauto. exfalso.
          eapply LT in H. eapply Time.lt_strorder. etrans; eauto.
        * eapply LT in H1. exfalso. eapply Time.lt_strorder; eauto.

  }
  i. hexploit (sorting_sorted l). i. des.
  ii. eapply NNPP. ii. eapply H0. econs. i. exfalso. eapply H0.
  eapply INCL in H1. eapply H in SORTED; eauto.
  - i. des. eapply COMPLETE; eauto.
  - eapply COMPLETE; eauto.
Qed.

Lemma message_from_to_well_founded mem (CLOSED: Memory.closed mem) loc:
  well_founded (message_from_to mem loc).
Proof.
  Local Opaque sorting.
  hexploit (cell_finite_sound_exists (mem loc)). i. des.
  eapply finite_sub_order_wf; eauto.
  { eapply message_from_to_ts; auto. }
  { i. inv LT. eapply COMPLETE. eauto. }
Qed.

Definition get_released_view_fun (c: Configuration.t) (f: Loc.t -> Time.t -> option View.t): Prop :=
  forall loc to,
    match (f loc to) with
    | None =>
      forall tid st lc from val released
             (THREAD: IdentMap.find tid (Configuration.threads c) = Some (st, lc))
             (GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))),
        False
    | Some releasedvw =>
      exists tid st lc from val released,
      (<<THREAD: IdentMap.find tid (Configuration.threads c) = Some (st, lc)>>) /\
      (<<GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))>>) /\
      (<<RELEASED: releasedvw = View.join ((TView.rel (Local.tview lc)) loc) (View.singleton_ur loc to)>>) /\
      (<<CLOSED: Memory.closed_view releasedvw (Configuration.memory c)>>) /\
      (<<WF: View.wf releasedvw>>)
    end.

Program Definition make_views (mem: Memory.t) (CLOSED: Memory.closed mem)
        (f: Loc.t -> Time.t -> option View.t): Loc.t -> Time.t -> list View.t :=
  fun loc =>
    @Fix Time.t (message_from_to mem loc) (message_from_to_well_founded CLOSED loc) (fun _ => list View.t)
         (fun to _make_views =>
            match Memory.get loc to mem with
            | Some (from, Message.concrete val (Some released)) =>
              let pview := match f loc to with
                           | Some releasedvw => [releasedvw]
                           | None => []
                           end in (pview ++ released :: List.map (View.join (View.singleton_ur loc to)) (_make_views from _))
            | _ => []
            end).
Next Obligation.
  econs; eauto.
Qed.

Lemma make_views_red mem (CLOSED: Memory.closed mem) f loc to:
  make_views CLOSED f loc to =
  match Memory.get loc to mem with
  | Some (from, Message.concrete val (Some released)) =>
    let pview := match f loc to with
                 | Some releasedvw => [releasedvw]
                 | None => []
                 end in (pview ++ released :: List.map (View.join (View.singleton_ur loc to)) (make_views CLOSED f loc from))
  | _ => []
  end.
Proof.
  unfold make_views at 1. rewrite Fix_eq at 1; des_ifs. i.
  assert (f0 = g).
  { extensionality y. extensionality p. eapply H. } clarify.
Qed.

Lemma make_views_joined_memory mem (CLOSED: Memory.closed mem) f
      (WF: forall loc ts releasedvw (EQ: f loc ts = Some releasedvw),
          Memory.closed_view releasedvw mem)
  :
    joined_memory (make_views CLOSED f) mem.
Proof.
  econs.
  - i. rewrite make_views_red. rewrite GET.
    specialize (WF loc ts). splits.
    + eapply joined_view_exact. eapply List.in_or_app.
      right. ss. auto.
    + i. eapply List.in_or_app. right. right.
      rewrite View.join_comm. eapply List.in_map. eauto.
  - i. rewrite make_views_red in SOME. des_ifs; eauto.
  - intros loc.
    eapply (well_founded_ind (message_from_to_well_founded CLOSED loc) (fun to => List.Forall (fun vw => Memory.closed_view vw mem) (make_views CLOSED f loc to))); eauto.
    intros to. i. rewrite make_views_red.
    destruct (Memory.get loc to mem) as [[from [val [released|]| |]]|] eqn:EQ; eauto.
    eapply Forall_app.
    + des_ifs. eapply WF in Heq. des; auto.
    + econs.
      { eapply CLOSED in EQ. des. inv MSG_CLOSED. inv CLOSED0. auto. }
      { eapply list_map_forall; eauto. i. ss.
        eapply Memory.join_closed_view; eauto.
        eapply Memory.singleton_ur_closed_view; eauto. eapply CLOSED. }
Qed.

Lemma make_views_wf_views mem (CLOSED: Memory.closed mem) f
      (WF: forall loc ts releasedvw (EQ: f loc ts = Some releasedvw),
          View.wf releasedvw)
  :
    wf_views (make_views CLOSED f).
Proof.
  intros loc.
  eapply (well_founded_ind (message_from_to_well_founded CLOSED loc) (fun to => List.Forall View.wf (make_views CLOSED f loc to))).
  intros to. i. rewrite make_views_red.
  destruct (Memory.get loc to mem) as [[from [val [released|]| |]]|] eqn:EQ; eauto.
  eapply Forall_app.
  + des_ifs. eapply WF in Heq; eauto.
  + econs.
    { eapply CLOSED in EQ. des. inv MSG_WF. inv WF0. eauto. }
    { eapply list_map_forall; eauto. i. eapply View.join_wf; auto.
      eapply View.singleton_ur_wf; eauto. }
Qed.

Lemma joined_view_exist (c: Configuration.t)
      (WF: Configuration.wf c)
  :
    exists views,
      JConfiguration.wf views c.
Proof.
  assert (exists f, <<FSPEC: get_released_view_fun c f>>).
  { eapply (choice (fun loc floc =>
                      forall to, match (floc to) with
                                 | None =>
                                   forall tid st lc from val released
                                          (THREAD: IdentMap.find tid (Configuration.threads c) = Some (st, lc))
                                          (GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))),
                                     False
                                 | Some releasedvw =>
                                   exists tid st lc from val released,
                                   (<<THREAD: IdentMap.find tid (Configuration.threads c) = Some (st, lc)>>) /\
                                   (<<GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))>>) /\
                                   (<<RELEASED: releasedvw = View.join ((TView.rel (Local.tview lc)) loc) (View.singleton_ur loc to)>>) /\
                                   (<<CLOSED: Memory.closed_view releasedvw (Configuration.memory c)>>) /\
                                   (<<WF: View.wf releasedvw>>)
                                 end)).
    intros loc.
    eapply (choice (fun to releasedvw =>
                      match releasedvw with
                      | None =>
                        forall tid st lc from val released
                               (THREAD: IdentMap.find tid (Configuration.threads c) = Some (st, lc))
                               (GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))),
                          False
                      | Some releasedvw =>
                        exists tid st lc from val released,
                        (<<THREAD: IdentMap.find tid (Configuration.threads c) = Some (st, lc)>>) /\
                        (<<GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))>>) /\
                        (<<RELEASED: releasedvw = View.join ((TView.rel (Local.tview lc)) loc) (View.singleton_ur loc to)>>) /\
                        (<<CLOSED: Memory.closed_view releasedvw (Configuration.memory c)>>) /\
                        (<<WF: View.wf releasedvw>>)
                      end)).
    intros to.
    destruct (classic (exists tid st lc from val released,
                          (<<THRAED: IdentMap.find tid (Configuration.threads c) = Some (st, lc)>>) /\
                          (<<GET: Memory.get loc to (Local.promises lc) = Some (from, Message.concrete val (Some released))>>))).
    { des. exists (Some (View.join ((TView.rel (Local.tview lc)) loc) (View.singleton_ur loc to))). esplits; eauto.
      - destruct st. eapply Memory.join_closed_view.
        + eapply WF; eauto.
        + eapply WF in GET; eauto. eapply Memory.singleton_ur_closed_view; eauto.
          eapply WF.
      - destruct st. eapply View.join_wf.
        + eapply WF; eauto.
        + eapply View.singleton_ur_wf. }
    { exists None. i. eapply H. esplits; eauto. }
  }
  dup WF. inv WF0.
  des. exists (make_views MEM f). econs; eauto.
  - ii. rewrite make_views_red.
    dup GET. eapply WF in GET0; eauto. rewrite GET0.
    specialize (FSPEC loc ts). des_ifs.
    + des. clarify. destruct (Ident.eq_dec tid tid0); dep_clarify; eauto. exfalso.
      destruct st0. eapply WF in n; eauto.
      inv n. inv DISJOINT. exploit DISJOINT0; eauto. i. des; ss.
      eapply memory_get_ts_strong in GET. eapply memory_get_ts_strong in GET1. des; clarify.
      eapply x0; econs; eauto; ss; try refl.
    + exfalso. eapply FSPEC; eauto.
  - eapply make_views_joined_memory.
    i. specialize (FSPEC loc ts). rewrite EQ in *. des. eauto.
  - eapply make_views_wf_views.
    i. specialize (FSPEC loc ts). rewrite EQ in *. des. eauto.
Qed.
