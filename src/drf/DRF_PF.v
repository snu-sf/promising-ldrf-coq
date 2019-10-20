Require Import Omega.
Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Cover.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import PromiseConsistent.
From PromisingLib Require Import Loc.

Require Import PF.
Require Import Race.
Require Import Behavior.
Require Import SimMemory.
Require Import yjtac.
Require Import Program.
Require Import Cell.
Require Import Time.
Require Import PredStep.

Set Implicit Arguments.


Section FORGETMEMORY.

  Inductive forget_memory P msrc mtgt : Prop :=
  | forget_memory_intro
      (COMPLETE: forall l t (NPROMS: ~ P l t),
          Memory.get l t msrc = Memory.get l t mtgt)
      (FORGET: forall l t (PROMS: P l t), Memory.get l t msrc = None)
  .

  Lemma forget_compose P0 P1 m0 m1 m2
        (FORGET0: forget_memory P0 m0 m1)
        (FORGET1: forget_memory P1 m1 m2)
    :
      forget_memory (P0 \2/ P1) m0 m2.
  Proof.
    inv FORGET0. inv FORGET1. econs; eauto.
    - ii. apply not_or_and in NPROMS. des.
      erewrite COMPLETE; eauto.
    - i. destruct (classic (P0 l t)); auto.
      des; clarify. erewrite COMPLETE; eauto.
  Qed.

  Lemma forget_compose_middle P0 P1 m0 m1 m2
        (FORGET: forget_memory (P0 \2/ P1) m0 m2)
        (FORGET1: forget_memory P1 m1 m2)
    :
      forget_memory P0 m0 m1.
  Proof.
    inv FORGET. inv FORGET1. econs; eauto.
    ii. destruct (classic (P1 l t)).
    - erewrite FORGET; eauto.
    - erewrite COMPLETE; eauto.
      + erewrite COMPLETE0; eauto.
      + ii. des; clarify.
  Qed.

  Lemma forget_memory_le P msrc mtgt
        (FORGET: forget_memory P msrc mtgt)
    :
      Memory.le msrc mtgt.
  Proof.
    inv FORGET. ii.
    destruct (classic (P loc to)).
    - exploit FORGET0; eauto.
      i. clarify.
    - exploit COMPLETE; eauto.
      i. rewrite LHS in *. auto.
  Qed.

  Inductive times_sorted: list Time.t -> Prop :=
  | times_sorted_nil
    :
      times_sorted []
  | times_sorted_cons
      hd tl
      (HD: List.Forall (Time.lt hd) tl)
      (TL: times_sorted tl)
    :
      times_sorted (hd :: tl)
  .
  Hint Constructors times_sorted.

  Fixpoint insert (to: Time.t) (l: list Time.t): list Time.t :=
    match l with
    | [] => [to]
    | hd :: tl =>
      match (Time.le_lt_dec to hd) with
      | left LE => match (Time.eq_dec to hd) with
                   | left EQ => hd :: tl
                   | right LT => to :: hd :: tl
                   end
      | right LT => hd :: (insert to tl)
      end
    end.

  Fixpoint sorting (l: list Time.t): list Time.t :=
    match l with
    | [] => []
    | hd :: tl => insert hd (sorting tl)
    end.

  Lemma insert_complete a l
    :
      forall b, List.In b (insert a l) <-> (a = b \/ List.In b l).
  Proof.
    ginduction l; ss. i. des_ifs; ss.
    - split; i; des; eauto.
    - split; i; des; eauto.
      + eapply IHl in H. des; eauto.
      + clarify. right. eapply IHl; eauto.
      + right. eapply IHl; eauto.
  Qed.

  Lemma insert_sorted a l
        (SORTED: times_sorted l)
    :
      times_sorted (insert a l).
  Proof.
    ginduction l; ss.
    - i. econs; ss.
    - i. des_ifs.
      + econs; eauto. inv SORTED. econs.
        * destruct l0; clarify.
        * eapply List.Forall_impl; cycle 1; eauto.
          i. eapply TimeFacts.le_lt_lt; eauto.
      + econs.
        * inv SORTED.
          eapply List.Forall_forall. i.
          eapply insert_complete in H. des; clarify.
          eapply List.Forall_forall in HD; eauto.
        * inv SORTED. eapply IHl; eauto.
  Qed.

  Lemma sorting_sorted l
    :
      (<<COMPLETE: forall a, List.In a l <-> List.In a (sorting l)>>) /\
      (<<SORTED: times_sorted (sorting l)>>).
  Proof.
    induction l; ss.
    - split; i; ss.
    - i. des. splits.
      + i. erewrite insert_complete.
        split; i; des; eauto.
        * right. eapply COMPLETE; eauto.
        * right. eapply COMPLETE; eauto.
      + eapply insert_sorted; eauto.
  Qed.

  Inductive disjoint_cell_msgs: list (Time.t * Time.t * Message.t) -> Prop :=
  | disjoint_cell_msgs_nil
    :
      disjoint_cell_msgs []
  | disjoint_cell_msgs_cons
      from to msg tl
      (HD: List.Forall (fun ftm =>
                          match ftm with
                          | (f, t, m) => Time.le to f
                          end) tl)
      (TL: disjoint_cell_msgs tl)
    :
      disjoint_cell_msgs ((from, to, msg) :: tl)
  .

  Definition wf_cell_msgs l :=
    (<<DISJOINT: disjoint_cell_msgs l>>) /\
    (<<MSGSWF: List.Forall (fun ftm =>
                              match ftm with
                              | (from, to, msg) =>
                                (<<MSGWF: Message.wf msg>>) /\
                                (<<TS: (from = Time.bot /\ to = Time.bot) \/ (Time.lt from to)>>)
                              end) l>>)
  .

  Lemma list_filter_exists A (P: A -> Prop) (l: list A)
    :
      exists l',
        (<<COMPLETE: forall a, ((<<IN: List.In a l>>) /\ (<<SAT: P a>>))
                               <-> (<<IN: List.In a l'>>)>>).
  Proof.
    induction l.
    - exists []. ii. split; i; des.
      + inv IN.
      + inv H.
    - des. destruct (classic (P a)).
      + exists (a :: l'). split; i; ss; des; clarify; eauto.
        * right. eapply COMPLETE; eauto.
        * eapply COMPLETE in H0. des. eauto.
      + exists l'. split; i; ss; des; clarify; eauto.
        * eapply COMPLETE; eauto.
        * eapply COMPLETE in H0. des; eauto.
  Qed.

  Lemma cell_finite_sound_exists c
    :
      exists dom,
        (<<COMPLETE: forall to,
            (List.In to dom <-> exists from msg,
                (<<GET: Cell.get to c = Some (from, msg)>>))>>).
  Proof.
    generalize (Cell.finite c). i. des.
    generalize (list_filter_exists (fun to => exists from msg, (<<GET: Cell.get to c = Some (from, msg)>>)) dom). i. des.
    exists l'. i. split; i.
    - eapply COMPLETE in H0. des. eauto.
    - eapply COMPLETE. splits; eauto.
      des. eapply H; eauto.
  Qed.

  Lemma wf_cell_msgs_exists c
    :
      exists l,
        (<<COMPLETE:
           forall from to msg,
             (<<GET: Cell.get to c = Some (from, msg)>>) <->
             (<<IN: List.In (from, to, msg) l>>)>>) /\
        (<<WFMSGS: wf_cell_msgs l>>).
  Proof.
    generalize (cell_finite_sound_exists c). i. des.
    generalize (sorting_sorted dom). i. des.
    assert (COMPLETE1: forall a, List.In a (sorting dom) <->
                                 exists from msg,
                                   (<<GET: Cell.get a c = Some (from, msg)>>)).
    { i. split; i.
      - eapply COMPLETE0 in H. eapply COMPLETE in H. eauto.
      - eapply COMPLETE0. eapply COMPLETE. eauto. }
    remember (sorting dom). clear - SORTED COMPLETE1.
    exists (List.map (fun to => match (Cell.get to c) with
                                | Some (from, msg) => (from, to, msg)
                                | None => (to, Time.bot, Message.reserve)
                                end) l).
    ginduction l; ss.
    - i. splits.
      + ii. split; clarify.
        i. eapply COMPLETE1. eauto.
      + econs.
        * econs.
        * econs.
    - i. hexploit (proj1 (COMPLETE1 a)); eauto. i. des.
      hexploit Cell.remove_exists; eauto. i. des.
      hexploit (IHl cell2).
      { inv SORTED. eauto. }
      { i. split; i.
        - hexploit (proj1 (COMPLETE1 a0)); eauto. i. des.
          exists from0, msg0. erewrite Cell.remove_o; eauto. des_ifs.
          exfalso. inv SORTED.
          eapply List.Forall_forall in H0; eauto.
          eapply Time.lt_strorder; eauto.
        - des. erewrite Cell.remove_o in GET0; eauto. des_ifs.
          hexploit (proj2 (COMPLETE1 a0)); eauto.
          i. des; clarify. }
      i. des. rewrite GET in *.
      replace (List.map
                 (fun to0 =>
                    match Cell.get to0 c with
                    | Some (from1, msg1) => (from1, to0, msg1)
                    | None => (to0, Time.bot, Message.reserve)
                    end) l) with
          (List.map
             (fun to0 =>
                match Cell.get to0 cell2 with
                | Some (from1, msg1) => (from1, to0, msg1)
                | None => (to0, Time.bot, Message.reserve)
                end) l); cycle 1.
      { eapply List.map_ext_in. i.
        erewrite (@Cell.remove_o cell2); eauto.
        des_ifs. exfalso. inv SORTED.
        eapply List.Forall_forall in H0; eauto.
        eapply Time.lt_strorder; eauto. }
      assert (COMPLETE2:
                forall from0 to msg0,
                  Cell.get to c = Some (from0, msg0) <->
                  (from, a, msg) = (from0, to, msg0) \/
                  List.In (from0, to, msg0)
                          (List.map
                             (fun to0 =>
                                match Cell.get to0 cell2 with
                                | Some (from1, msg1) => (from1, to0, msg1)
                                | None => (to0, Time.bot, Message.reserve)
                                end) l)).
      { i. split; i.
        - generalize (Cell.remove_o to H). intros GET0.
          des_ifs; eauto. right.
          rewrite H0 in GET0. eapply COMPLETE in GET0. eauto.
        - des; clarify.
          eapply (proj2 (COMPLETE from0 to msg0)) in H0.
          erewrite Cell.remove_o in H0; eauto. des_ifs. }
      splits; auto.
      unfold wf_cell_msgs in WFMSGS. des. econs; eauto.
      + econs; eauto. inv SORTED.
        eapply List.Forall_forall. i.
        eapply List.in_map_iff in H0. des.
        erewrite Cell.remove_o in H0; eauto. des_ifs.
        * dup GET. eapply Cell.get_ts in GET0. des; clarify.
          { eapply Time.bot_spec. }
          destruct (Time.le_lt_dec a t0); auto. exfalso.
          exploit Cell.get_disjoint.
          { eapply GET. }
          { eapply Heq0. }
          i. des; clarify. eapply x0.
          { instantiate (1:=a). econs; ss. refl. }
          { econs; ss.
            eapply List.Forall_forall in HD; eauto. left. auto. }
        * refl.
        * exfalso. hexploit (proj1 (COMPLETE1 t0)); eauto.
          i. des. clarify.
      + econs; eauto. splits.
        { eapply Cell.get_opt_wf; eauto. }
        { eapply Cell.get_ts; eauto. }
  Qed.

  Inductive forget_cell (P: Time.t -> Prop) cell_src cell_tgt : Prop :=
  | forget_cell_intro
      (COMPLETE: forall t (NPROMS: ~ P t),
          Cell.get t cell_src = Cell.get t cell_tgt)
      (FORGET: forall t (PROMS: P t), Cell.get t cell_src = None)
  .

  Lemma forget_exists_list l cell_tgt:
    exists cell_src,
      (<<FORGET: forget_cell (fun to => List.In to l) cell_src cell_tgt>>).
  Proof.
    induction l; ss.
    - exists cell_tgt. econs; ss.
    - des. destruct (Cell.get a cell_src) as [[from msg]|] eqn:GET.
      + exploit Cell.remove_exists; eauto. i. des. exists cell2.
        inv FORGET. econs; i.
        * erewrite Cell.remove_o; eauto. des_ifs; eauto.
          ss; des; clarify. exfalso. eauto.
        * erewrite Cell.remove_o; eauto. des_ifs; clarify.
          eapply FORGET0; eauto. ss. des; clarify; eauto.
      + exists cell_src. inv FORGET.
        econs; eauto. i. des; clarify; eauto.
  Qed.

  Lemma forget_cell_exists P cell_tgt:
    exists cell_src, (<<FORGET: forget_cell P cell_src cell_tgt>>).
  Proof.
    hexploit (cell_finite_sound_exists cell_tgt); eauto. i. des.
    hexploit (list_filter_exists P dom). i. des.
    hexploit (forget_exists_list l' cell_tgt). i. des.
    exists cell_src. inv FORGET. econs; eauto.
    - i. eapply COMPLETE1. ii. apply COMPLETE0 in H. des. clarify.
    - i. destruct (classic (List.In t dom)).
      + eapply FORGET0; eauto. eapply COMPLETE0; eauto.
      + rewrite COMPLETE1; eauto.
        * destruct (Cell.get t cell_tgt) as [[from msg]|] eqn:GET; auto.
          exfalso. eapply H. eapply COMPLETE; eauto.
        * ii. eapply COMPLETE0 in H0. des; clarify.
  Qed.

  Lemma forget_exists P mem_tgt:
    exists mem_src, (<<FORGET: forget_memory P mem_src mem_tgt>>).
  Proof.
    hexploit (choice (fun loc cell => forget_cell (P loc) cell (mem_tgt loc))).
    { i. eapply forget_cell_exists. } i. des.
    exists f. econs.
    - i. destruct (H l). eapply COMPLETE; eauto.
    - i. destruct (H l). eapply FORGET; eauto.
  Qed.

  Lemma forget_unique P mem_tgt mem_src0 mem_src1
        (FORGET0: forget_memory P mem_src0 mem_tgt)
        (FORGET1: forget_memory P mem_src1 mem_tgt)
    :
      mem_src0 = mem_src1.
  Proof.
    inv FORGET0. inv FORGET1.
    eapply Memory.ext. i. destruct (classic (P loc ts)).
    - erewrite FORGET; auto. erewrite FORGET0; auto.
    - erewrite COMPLETE; auto. erewrite COMPLETE0; auto.
  Qed.

  Lemma disjoint_equivalent from0 to0 from1 to1
    :
      (<<INTERSECT: ~ Interval.disjoint (from0, to0) (from1, to1)>>) <->
      ((<<TS0: Time.lt from0 to0>>) /\ (<<TS1: Time.lt from1 to1>>) /\
       (<<TS0: Time.lt (Time.join from0 from1) (Time.meet to0 to1)>>)).
  Proof.
    split; i. des.
    - unfold Interval.disjoint in H.
      eapply not_all_ex_not in H. des.
      dup H. eapply not_imply_elim in H. eapply not_imply_elim2 in H0.
      apply NNPP in H0.
      destruct H. destruct H0. ss. splits.
      + eapply TimeFacts.lt_le_lt; eauto.
      + eapply TimeFacts.lt_le_lt; eauto.
      + unfold Time.join, Time.meet. des_ifs.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
        * eapply TimeFacts.lt_le_lt; eauto.
    - des. ii. eapply H.
      + instantiate (1:=Time.meet to0 to1). econs; ss.
        * unfold Time.join, Time.meet in *. des_ifs.
          eapply TimeFacts.le_lt_lt; eauto.
        * eapply Time.meet_l.
      + econs; ss.
        * unfold Time.join, Time.meet in *. des_ifs.
          etrans; eauto.
        * eapply Time.meet_r.
  Qed.

  Lemma or_strengthen A B
        (OR: A \/ B)
    :
      (A \/ ((<<NOT: ~ A>>) /\ (<<SAT: B>>))).
  Proof.
    destruct (classic A); eauto. des; eauto.
  Qed.

  Lemma memory_get_ts_strong loc to mem from msg
        (GET: Memory.get loc to mem = Some (from, msg))
    :
      (from = Time.bot /\ to = Time.bot) \/
      ((<<TS: Time.lt from to>>) /\ (<<TO: to <> Time.bot>>)).
  Proof.
    apply Memory.get_ts in GET.
    destruct (classic (to = Time.bot)); clarify.
    - des; clarify; eauto.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
    - des; clarify. right. eauto.
  Qed.

  Lemma memory_get_from_inj mem loc from to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from, msg0))
        (GET1: Memory.get loc to1 mem = Some (from, msg1))
    :
      (<<TO: to0 = to1>>) \/
      (((<<BOT: to0 = Time.bot>>) \/ (<<BOT: to1 = Time.bot>>)) /\ (<<BOT: from = Time.bot>>) /\
       (<<TO: to0 <> to1>>)).
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify; eauto.
      eapply memory_get_ts_strong in GET0.
      eapply memory_get_ts_strong in GET1.
      des; clarify; eauto.
      { right. esplits; eauto. }
      { right. esplits; eauto. }
      exfalso. eapply x0.
      + instantiate (1:=Time.meet to0 to1). econs; ss; eauto.
        * unfold Time.meet. des_ifs.
        * eapply Time.meet_l.
      + econs; ss; eauto.
        * unfold Time.meet. des_ifs.
        * eapply Time.meet_r.
  Qed.

  Lemma disjoint_equivalent2 from0 to0 from1 to1
    :
      (<<DISJOINT: Interval.disjoint (from0, to0) (from1, to1)>>) <->
      ((<<TS0: ~ Time.lt from0 to0>>) \/ (<<TS1: ~ Time.lt from1 to1>>) \/
       (<<TS0: Time.le (Time.meet to0 to1) (Time.join from0 from1)>>)).
  Proof.
    set (disjoint_equivalent from0 to0 from1 to1).
    eapply not_iff_compat in i. split; i.
    - des. hexploit i.
      { ii. clarify. } i.
      apply not_and_or in H0. des; eauto.
      apply not_and_or in H0. des; eauto.
      right. right. red.
      destruct (Time.le_lt_dec (Time.meet to0 to1) (Time.join from0 from1)); eauto.
      exfalso. eauto.
    - destruct i. hexploit H1.
      { ii. des; eauto. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. }
      ii. eauto.
  Qed.

  Lemma memory_get_to_mon mem loc from0 from1 to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (TO: Time.lt from0 from1)
    :
      Time.lt to0 to1.
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify.
      + exfalso. eapply Time.lt_strorder. eauto.
      + dup GET0. dup GET1.
        eapply memory_get_ts_strong in GET0.
        eapply memory_get_ts_strong in GET1.
        des; clarify.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * hexploit (Time.bot_spec from1). i.
          destruct H; eauto.
        * eapply disjoint_equivalent2 in x0. des; clarify.
          unfold Time.meet, Time.join in *. des_ifs; eauto.
          { destruct l; eauto. destruct H; eauto. clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          { destruct l; eauto. destruct H; eauto. clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. }
          { exfalso. eapply Time.lt_strorder.
            eapply TimeFacts.le_lt_lt; eauto. }
  Qed.

  Lemma memory_get_from_mon mem loc from0 from1 to0 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
        (TO: Time.lt to0 to1)
    :
      Time.le to0 from1.
  Proof.
    exploit Memory.get_disjoint.
    - eapply GET0.
    - eapply GET1.
    - i. des; clarify.
      + exfalso. eapply Time.lt_strorder. eauto.
      + dup GET0. dup GET1.
        eapply memory_get_ts_strong in GET0.
        eapply memory_get_ts_strong in GET1.
        des; clarify.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * exfalso. eapply Time.lt_strorder.
          eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
        * apply Time.bot_spec.
        * destruct (Time.le_lt_dec to0 from1); auto. exfalso.
          eapply x0.
          { instantiate (1:=to0).
            econs; ss. refl. }
          { econs; ss. left. auto. }
  Qed.

  Lemma max_full_timemap_get mem tm loc to from val released
        (MAX: Memory.max_full_timemap mem tm)
        (GET: Memory.get loc to mem = Some (from, Message.full val released))
    :
      Time.le to (tm loc).
  Proof.
    specialize (MAX loc). inv MAX. eapply MAX0; eauto.
  Qed.

  Lemma le_inhabited mem0 mem1
        (INHABITED: Memory.inhabited mem0)
        (MLE: Memory.le mem0 mem1)
    :
      Memory.inhabited mem1.
  Proof.
    ii. eapply MLE; eauto.
  Qed.

End FORGETMEMORY.


Section MEMORYLEMMAS.

  Lemma remove_le mem0 loc from to msg mem1
        (REMOVE: Memory.remove mem0 loc from to msg mem1)
  :
    Memory.le mem1 mem0.
  Proof.
    ii. erewrite Memory.remove_o in LHS; eauto. des_ifs.
  Qed.

  Lemma step_promises_le lang (th0 th1: Thread.t lang) tf e
        (MLE: Memory.le th0.(Thread.local).(Local.promises) th0.(Thread.memory))
        (STEP: Thread.step tf e th0 th1)
  :
    Memory.le th1.(Thread.local).(Local.promises) th1.(Thread.memory).
  Proof.
    inv STEP.
    - inv STEP0. inv LOCAL. ss.
      eapply Memory.promise_le; eauto.
    - inv STEP0. inv LOCAL; ss.
      + inv LOCAL0; ss.
      + inv LOCAL0. ss. inv WRITE.
        eapply Memory.promise_le in PROMISE; eauto. red in PROMISE.
        eapply remove_le in REMOVE.
        etrans; eauto.
      + inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        eapply Memory.promise_le in PROMISE; eauto. red in PROMISE.
        eapply remove_le in REMOVE.
        etrans; eauto.
      + inv LOCAL0; ss.
      + inv LOCAL0; ss.
  Qed.

  Lemma steps_promises_le P lang (th0 th1: Thread.t lang)
        (MLE: Memory.le th0.(Thread.local).(Local.promises) th0.(Thread.memory))
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
  :
    Memory.le th1.(Thread.local).(Local.promises) th1.(Thread.memory).
  Proof.
    ginduction STEP; ss.
    i. eapply IHSTEP.
    inv H. inv TSTEP. inv STEP0. eapply step_promises_le; eauto.
  Qed.

  Lemma inhabited_future mem1 mem2
        (FUTURE: Memory.future mem1 mem2)
        (INHABITED: Memory.inhabited mem1)
  :
    Memory.inhabited mem2.
  Proof.
    induction FUTURE; auto. apply IHFUTURE.
    inv H. hexploit Memory.op_inhabited; eauto.
  Qed.

  Lemma memory_le_get_none msrc mtgt loc to
        (MLE: Memory.le msrc mtgt)
        (NONE: Memory.get loc to mtgt = None)
    :
      Memory.get loc to msrc = None.
  Proof.
    destruct (Memory.get loc to msrc) eqn:GET; auto.
    destruct p. eapply MLE in GET. clarify.
  Qed.

  Lemma memory_le_covered msrc mtgt loc to
        (MLE: Memory.le msrc mtgt)
        (COVERED: covered loc to msrc)
    :
      covered loc to mtgt.
  Proof.
    inv COVERED. econs; eauto.
  Qed.

  Lemma memory_add_cover_disjoint mem0 loc from to msg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        t
        (IN: Interval.mem (from, to) t)
    :
      ~ covered loc t mem0.
  Proof.
    ii. inv H. dup ADD. eapply Memory.add_get0 in ADD. des.
    exploit Memory.get_disjoint.
    + eapply Memory.add_get1; eauto.
    + eauto.
    + i. des; clarify. eauto.
  Qed.

  Definition not_attatched_time (mem: Memory.t) (loc: Loc.t) (to: Time.t) :=
    forall to' msg (GET: Memory.get loc to' mem = Some (to, msg)),
      False.

  Lemma write_succeed mem1 loc from1 to1 val released
        (NCOVER: forall t (COVER: covered loc t mem1),
            ~ Interval.mem (from1, to1) t)
        (TO: Time.le (View.rlx (View.unwrap released) loc) to1)
        (FROMTO: Time.lt from1 to1)
        (* (NOATTATCH: not_attatched_time mem1 loc to1) *)
        (MSGWF: Message.wf (Message.full val released))
    :
      exists mem2,
        (<<WRITE: Memory.write Memory.bot mem1 loc from1 to1 val released Memory.bot mem2 Memory.op_kind_add>>).
  Proof.
    exploit Memory.add_exists; eauto.
    { instantiate (1:=mem1). instantiate (1:=loc).
      ii. eapply NCOVER; eauto. econs; eauto. }
    i. des. exists mem2.
    exploit Memory.add_exists; eauto.
    { instantiate (1:=Memory.bot). instantiate (1:=loc).
      ii. rewrite Memory.bot_get in *. clarify. } i. des.
    econs.
    - econs; eauto; ss.
      admit.
    (* not provable *)

    - exploit Memory.remove_exists; eauto.
      { eapply Memory.add_get0 in x1. des. eauto. } i. des.
      exploit MemoryFacts.MemoryFacts.add_remove_eq; eauto.
      i. clarify.
  Admitted.

  Lemma write_disjoint promises1 mem1 loc from1 to1 val released promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (WRITE: Memory.write
                  promises1 mem1 loc from1 to1 val released promises3 mem2 kind)
        to
        (INT: Interval.mem (from1, to1) to)
    :
      (<<PROMISED: covered loc to promises1>>) \/
      (<<NEWMSG: ~ covered loc to mem1>>).
  Proof.
    inv WRITE. inv PROMISE.
    - right. ii. inv H. inv MEM. inv ADD.
      exploit DISJOINT; eauto.
    - left. dup PROMISES. eapply Memory.split_get0 in PROMISES. des.
      econs; eauto.
      inv INT. inv PROMISES0. inv SPLIT. econs; ss.
      etrans; eauto. left. auto.
    - left. dup PROMISES. eapply Memory.lower_get0 in PROMISES. des.
      econs; eauto.
    - clarify.
  Qed.

  Lemma write_msg_wf v prom v' prom'
        loc from to val releasedm released ord sc sc' mem_tgt mem_tgt' kind
        (WRITE: Local.write_step
                  (Local.mk v prom) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
    :
      (<<TLE: Time.le
                (View.rlx (View.unwrap (TView.write_released v sc loc to releasedm ord)) loc) to>>) /\
      (<<FROMTO: Time.lt from to>>) /\
      (<<MSGWF: Message.wf (Message.full val (TView.write_released v sc loc to releasedm ord))>>) /\
      (<<NOATTATCH: forall (KIND: kind = Memory.op_kind_add), not_attatched_time mem_tgt loc to>>)
  .
  Proof.
    inv WRITE. inv WRITE0. inv PROMISE.
    - inv TS. inv MEM. inv ADD. esplits; eauto. ii. eauto.
    - inv TS. inv MEM. inv SPLIT. esplits; eauto. ii. clarify.
    - inv TS. inv MEM. inv LOWER. esplits; eauto. ii. clarify.
    - clarify.
  Qed.

  Lemma memory_write_bot_add
        mem1 loc from1 to1 val released promises3 mem2 kind
        (WRITE: Memory.write
                  Memory.bot mem1 loc from1 to1 val released promises3 mem2 kind)
    :
      kind = Memory.op_kind_add.
  Proof.
    inv WRITE. inv PROMISE; auto.
    - exfalso. eapply Memory.split_get0 in PROMISES. des.
      rewrite Memory.bot_get in *. clarify.
    - exfalso. eapply Memory.lower_get0 in PROMISES. des.
      rewrite Memory.bot_get in *. clarify.
    - clarify.
  Qed.

  Lemma promise_bot_no_promise P lang (th0 th1: Thread.t lang) e
        (STEP: (@pred_step P lang) e th0 th1)
        (NOPROMISE: P <1= no_promise)
        (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
    :
      th1.(Thread.local).(Local.promises) = Memory.bot.
  Proof.
    inv STEP. eapply NOPROMISE in SAT. inv STEP0. inv STEP.
    - inv STEP0; des; clarify.
    - inv STEP0. ss. inv LOCAL; try inv LOCAL0; ss.
      + rewrite BOT in *. exploit memory_write_bot_add; eauto. i. clarify.
        exploit MemoryFacts.MemoryFacts.write_add_promises; eauto.
      + inv LOCAL1. inv LOCAL2. ss. rewrite BOT in *.
        exploit memory_write_bot_add; eauto. i. clarify.
        exploit MemoryFacts.MemoryFacts.write_add_promises; eauto.
  Qed.

  Lemma promise_bot_no_promise_rtc P lang (th0 th1: Thread.t lang)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (NOPROMISE: P <1= no_promise)
        (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
    :
      th1.(Thread.local).(Local.promises) = Memory.bot.
  Proof.
    induction STEP; auto. erewrite IHSTEP; auto.
    inv H. eapply promise_bot_no_promise; eauto.
  Qed.

  Lemma finite_least P (l: list Time.t)
    :
      (exists to,
          (<<SAT: P to>>) /\
          (<<IN: List.In to l>>) /\
          (<<LEAST: forall to'
                           (IN: List.In to' l)
                           (SAT: P to'),
              Time.le to to'>>)) \/
      (<<EMPTY: forall to (IN: List.In to l), ~ P to>>).
  Proof.
    induction l.
    - right. ii. inv IN.
    - destruct (classic (P a)).
      + des.
        * destruct (Time.le_lt_dec a to).
          { left. exists a. esplits; ss; eauto.
            i. des; clarify; eauto. refl. }
          { left. exists to. esplits; ss; eauto.
            i. des; clarify; eauto. left. eauto. }
        * left. exists a. esplits; ss; eauto.
          i. des; clarify.
          { refl. }
          { exfalso. eapply EMPTY; eauto. }
      + des.
        * left. esplits; ss; eauto.
          i. des; clarify. eapply LEAST; eauto.
        * right. ii. ss. des; clarify.
          eapply EMPTY; eauto.
  Qed.

  Lemma cell_elements_least cell P
    :
      (exists to from msg,
          (<<GET: Cell.get to cell = Some (from, msg)>>) /\
          (<<SAT: P to>>) /\
          (<<LEAST: forall to' from' msg'
                           (GET': Cell.get to' cell = Some (from', msg'))
                           (SAT: P to'),
              Time.le to to'>>)) \/
      (<<EMPTY: forall to from msg
                       (GET: Cell.get to cell = Some (from, msg)),
          ~ P to>>).
  Proof.
    hexploit (Cell.finite cell). i. des.
    hexploit (finite_least (fun to => P to /\ exists from msg, Cell.get to cell = Some (from, msg)) dom).
    i. des.
    - left. esplits; eauto. i.
      dup GET'. eapply H in GET'. eauto.
    - right. ii. dup GET. eapply H in GET0.
      eapply EMPTY in GET0. eapply GET0.
      esplits; eauto.
  Qed.


End MEMORYLEMMAS.


Section PROMISED.

  Inductive promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
  | promised_intro
      msg
      (GET: Memory.get loc to mem = Some msg)
    :
      promised mem loc to
  .

  Inductive concrete_promised (mem: Memory.t) (loc: Loc.t) (to: Time.t) : Prop :=
  | concrete_promised_intro
      from val released
      (GET: Memory.get loc to mem = Some (from, Message.full val released))
  .

  Lemma concrete_promised_increase_promise promises1 mem1 loc from to msg promises2 mem2 kind
        (STEP: Memory.promise promises1 mem1 loc from to msg promises2 mem2 kind)
    :
      concrete_promised mem1 <2= concrete_promised mem2.
  Proof.
    inv STEP.
    - ii. inv PR.
      exploit Memory.add_get1; eauto. i.
      econs; eauto.
    - ii. inv PR.
      exploit Memory.split_get1; eauto. i. des.
      econs; eauto.
    - ii. inv PR.
      exploit Memory.lower_get1; eauto. i. des.
      inv MSG_LE. econs; eauto.
    - ii. inv PR. econs; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; eauto.
      eapply Memory.remove_get0 in MEM. ss; des; clarify.
  Qed.

  Lemma concrete_promised_increase lang (th0 th1: Thread.t lang) pf e
        (STEP: Thread.step pf e th0 th1)
    :
      concrete_promised th0.(Thread.memory) <2= concrete_promised th1.(Thread.memory).
  Proof.
    i. inv STEP.
    - inv STEP0. ss. inv LOCAL.
      eapply concrete_promised_increase_promise; eauto.
    - inv STEP0; ss. inv LOCAL; ss.
      + inv LOCAL0. inv WRITE.
        eapply concrete_promised_increase_promise; eauto.
      + inv LOCAL1. inv LOCAL2. inv WRITE.
        eapply concrete_promised_increase_promise; eauto.
  Qed.

End PROMISED.

Inductive opt_pred_step P lang
  : ThreadEvent.t -> Thread.t lang -> Thread.t lang -> Prop :=
| step_none t: opt_pred_step P ThreadEvent.silent t t
| step_some
    e t0 t1
    (STEP: pred_step P e t0 t1)
  :
    opt_pred_step P e t0 t1.
Hint Constructors opt_pred_step.


Section VIEWCONSISTENT.

  Definition promise_view_consistent (prom: Loc.t -> Time.t -> Prop) (view: TimeMap.t) : Prop :=
    forall
      loc to
      (GET: prom loc to),
      Time.lt (view loc) to.

  Lemma promise_view_consistent_le v0 v1 prm
        (VLE: TimeMap.le v0 v1)
        (CONS: promise_view_consistent prm v1)
    :
      promise_view_consistent prm v0.
  Proof.
    ii. exploit CONS; eauto. i.
    eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto.
  Qed.

  (* Lemma promise_consistent_le tv0 tv1 prm *)
  (*       (VLE: TView.le tv0 tv1) *)
  (*       (CONS: promise_consistent (Local.mk tv1 prm)) *)
  (*   : *)
  (*     local_consistent (Local.mk tv0 prm). *)
  (* Proof. *)
  (*   inv VLE. inv CUR. unfold local_consistent in *. ss. *)
  (*   eapply promise_view_consistent_le; eauto. *)
  (* Qed. *)

  (* Lemma local_consistent_step lang (st0 st1: Language.state lang) lc0 lc1 *)
  (*       sc0 sc1 m0 m1 pf e *)
  (*       (WF1: Local.wf lc0 m0) *)
  (*       (SC1: Memory.closed_timemap sc0 m0) *)
  (*       (CLOSED1: Memory.closed m0) *)
  (*       (CONSISTENT: promise_consistent lc1) *)
  (*       (STEP: Thread.step pf e (Thread.mk _ st0 lc0 sc0 m0) (Thread.mk _ st1 lc1 sc1 m1)) *)
  (*   : *)
  (*     promise_consistent lc0. *)
  (* Proof. *)
  (*   hexploit step_promise_consistent; eauto. *)
  (* Qed. *)

  (* Lemma thread_consistent_view_consistent lang st lc sc mem *)
  (*       (CLOSED: Memory.closed mem) *)
  (*       (INHABITED: Memory.inhabited mem) *)
  (*       (LCWF: Local.wf lc mem) *)
  (*       (SC: Memory.closed_timemap sc mem) *)
  (*       (CONSISTENT: Thread.consistent (Thread.mk lang st lc sc mem)) *)
  (*   : *)
  (*     promise_consistent lc. *)
  (* Proof. *)
  (*   hexploit consistent_promise_consistent; eauto. *)
  (* Qed. *)

End VIEWCONSISTENT.


Section NOREADSELFPROMS.

  Lemma consistent_read_no_self_promise
        lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_tgt mem_tgt' pf e_tgt
        (LOCALWF: Local.wf (Local.mk v prom) mem_tgt)
        (CLOSED: Memory.closed mem_tgt)
        (SC: Memory.closed_timemap sc mem_tgt)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (CONSISTENT: Local.promise_consistent (Local.mk v' prom'))
        (STEP: Thread.step pf e_tgt th_tgt th_tgt')
    :
      no_read_msgs prom.(promised) e_tgt.
  Proof.
    inv STEP; ss.
    - inv STEP0. ss.
    - inv STEP0. inv LOCAL; ss.
      + ii. inv H. destruct msg as [? []].
        * hexploit promise_consistent_promise_read; eauto; ss.
          ii. timetac.
        * inv LOCAL0. ss. clarify.
          inv LOCALWF. ss. eapply PROMISES in GET. clarify.
      + ii. destruct lc2.
        inv H. destruct msg as [? []].
        * hexploit promise_consistent_promise_read; eauto; ss.
          { eapply write_step_promise_consistent; eauto. }
          { ii. timetac. }
        * inv LOCAL1. ss. clarify.
          inv LOCALWF. ss. eapply PROMISES in GET. clarify.
  Qed.

End NOREADSELFPROMS.


Section NOSC.

  Lemma no_sc_any_sc
        P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc_src sc'
        mem mem' e
        (STEP: (@pred_step P lang) e th_tgt th_tgt')
        (NOSC: P <1= no_sc)
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc_src mem)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem')
  :
    exists sc_src',
      (<<STEP: (@pred_step P lang)
                 e th_src
                 (Thread.mk lang st' (Local.mk v' prom') sc_src' mem')>>).
  Proof.
    clarify. inv STEP. dup SAT. eapply NOSC in SAT.
    inv STEP0. des. inv STEP.
    - inv STEP0. inv LOCAL. ss. clarify.
      esplits. econs; eauto. econs; eauto. econs 1; eauto. econs; eauto.
    - inv STEP0. inv LOCAL; ss.
      + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. exists sc_src.
        econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. ss.
        inv WRITABLE. econs; eauto.
      + inv LOCAL1. ss. inv LOCAL2. ss. clarify. exists sc_src.
        econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. ss.
        inv WRITABLE. econs; eauto.
      + inv LOCAL0. ss. clarify.
        esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        econs; eauto. econs; eauto. ss. f_equal.
        unfold TView.write_fence_tview. ss. des_ifs.
      + esplits. econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

  Lemma no_sc_any_sc_rtc
        P lang th_src th_tgt th_tgt' st st' lc lc' sc sc_src sc'
        mem mem'
        (STEP: rtc (tau (@pred_step P lang)) th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st lc sc_src mem)
        (TH_TGT0: th_tgt = Thread.mk lang st lc sc mem)
        (TH_TGT1: th_tgt' = Thread.mk lang st' lc' sc' mem')
        (PRED: P <1= no_sc)
    :
      exists sc_src',
        (<<STEP: rtc (tau (@pred_step P lang))
                     th_src
                     (Thread.mk lang st' lc' sc_src' mem')>>).
  Proof.
    ginduction STEP.
    - i. clarify. esplits; eauto.
    - i. clarify. destruct y. destruct local, lc, lc'. ss.
      inv H. exploit no_sc_any_sc; eauto. i. des.
      exploit IHSTEP; eauto. i. des.
      exists sc_src'0. esplits. econs; eauto.
  Qed.

  (* TODO: unused *)
  Lemma consistent_certification_no_sc
        P lang th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_tgt mem_tgt' e_tgt
        (SCMAX: ~ promise_view_consistent prom sc)
        (NOPROMISE: P <1= no_promise)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (CONSISTENT: promise_view_consistent prom v'.(TView.cur).(View.rlx))
        (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
    :
      no_sc e_tgt.
  Proof.
    inv STEP. inv STEP0; ss. inv STEP; ss.
    - inv STEP0. ss.
    - inv STEP0. inv LOCAL; ss.
      + ii. clarify. inv LOCAL0. ss. clarify. ss. eapply SCMAX.
        eapply promise_view_consistent_le; eauto. des_ifs; ss.
        eapply TViewFacts.write_fence_sc_incr.
      + ii. clarify. inv LOCAL0. ss. clarify. ss. eapply SCMAX.
        eapply promise_view_consistent_le; eauto. des_ifs; ss.
        eapply TViewFacts.write_fence_sc_incr.
  Qed.

End NOSC.



Section SELFPROMISEREMOVE.

  Lemma self_promise_remove_promise
        prom prom' mem_src mem_tgt mem_tgt' loc from to msg kind
        (MEM: forget_memory (promised prom) mem_src mem_tgt)
        (PROMISE: Memory.promise prom mem_tgt loc from to msg prom' mem_tgt' kind)
  :
    forget_memory (promised prom') mem_src mem_tgt'.
  Proof.
    dup MEM. eapply forget_memory_le in MEM0. inv MEM. inv PROMISE.
    - econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.add_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.add_get0 in PROMISES. des.
            econs; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.add_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg0.
        erewrite Memory.add_o in GET; eauto. des_ifs.
        { ss. des. clarify.
          eapply memory_le_get_none; eauto.
          apply Memory.add_get0 in MEM. des. eauto. }
        { eapply FORGET. econs; eauto. }
    - econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.split_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.split_get0 in PROMISES. des.
            econs; eauto.
          - ss. destruct a. clarify. exfalso. apply NPROMS.
            apply Memory.split_get0 in PROMISES.
            econs; des; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.split_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg0.
        erewrite Memory.split_o in GET; eauto. des_ifs.
        { ss. des. clarify.
          eapply memory_le_get_none; eauto.
          apply Memory.split_get0 in MEM. des. eauto. }
        { ss. destruct a. clarify.
          eapply FORGET. apply Memory.split_get0 in PROMISES.
          econs. des; eauto. }
        { eapply FORGET. econs; eauto. }
    - econs; eauto.
      * i. rewrite COMPLETE.
        { symmetry. erewrite Memory.lower_o; eauto. des_ifs.
          - ss. des. clarify. exfalso. apply NPROMS.
            apply Memory.lower_get0 in PROMISES. des.
            econs; eauto. }
        { ii. inv H. eapply NPROMS.
          exploit Memory.lower_o; try apply PROMISES; eauto. i.
          erewrite GET in *. des_ifs.
          - econs; eauto.
          - econs; eauto. }
      * i. inv PROMS. destruct msg1.
        erewrite Memory.lower_o in GET; eauto. des_ifs.
        { ss. des. clarify. eapply FORGET.
          apply Memory.lower_get0 in PROMISES. des. econs. eauto. }
        { eapply FORGET. apply Memory.lower_get0 in PROMISES.
          econs. des; eauto. }
    - econs; eauto.
      * i. erewrite (@Memory.remove_o mem_tgt'); eauto. des_ifs.
        { ss. des. clarify. eapply FORGET. econs; eauto.
          eapply Memory.remove_get0 in PROMISES. des. eauto. }
        { eapply COMPLETE. ii. inv H. eapply NPROMS. econs; eauto.
          erewrite Memory.remove_o; eauto.
          des_ifs; ss; des; clarify; eauto. }
      * i. inv PROMS. erewrite Memory.remove_o in GET; eauto. des_ifs.
        eapply FORGET; eauto. econs; eauto.
  Qed.

  Lemma self_promise_remove_write v prom v' prom'
        loc from to val releasedm released ord sc sc' mem_src
        mem_tgt mem_tgt' kind
        (WRITE: Local.write_step
                  (Local.mk v prom) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (MEM: forget_memory (promised prom) mem_src mem_tgt)
        (LCWF: Local.wf (Local.mk v prom) mem_tgt)
  :
    exists mem_src',
      (<<WRITE: Local.write_step
                  (Local.mk v Memory.bot) sc mem_src
                  loc from to val releasedm released ord
                  (Local.mk v' Memory.bot) sc' mem_src' Memory.op_kind_add>>) /\
      (<<MEM: forget_memory (promised prom') mem_src' mem_tgt'>>).
  Proof.
    dup MEM. eapply forget_memory_le in MEM0. inv MEM.
    inv WRITE. ss. clarify.
    (* inv WRITE0. *)
    exploit write_msg_wf; eauto. i. des.
    exploit write_succeed; eauto.
    { instantiate (1:=mem_src).
      ii. inv LCWF. exploit write_disjoint; try apply WRITE0; eauto.
      i. des.
      - inv PROMISED. inv COVER. dup GET0.
        assert (NPRM: ~ promised prom loc to1).
        { ii. erewrite FORGET in GET0; eauto. clarify. }
        erewrite COMPLETE in GET0; eauto. exploit Memory.get_disjoint.
        + eapply GET0.
        + eapply PROMISES in GET. eapply GET.
        + i. des; clarify; eauto.
          eapply NPRM. econs; eauto.
      - eapply NEWMSG. eapply memory_le_covered; try apply MEM0; eauto. }
    i. des. exists mem2. esplits; ss.
    - econs 1; ss; eauto.
      ii. rewrite Memory.bot_get in *. clarify.
    - inv WRITE0. inv WRITE. inv PROMISE0. inv PROMISE.
      + exploit MemoryFacts.MemoryFacts.add_remove_eq.
        { eapply PROMISES0. }
        { eapply REMOVE. } i. clarify.
        econs; i.
        * erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.add_o mem_tgt'); cycle 1; eauto.
          des_ifs. eauto.
        * erewrite (@Memory.add_o mem2); eauto.
          des_ifs; eauto. ss. des. clarify. exfalso.
          eapply Memory.add_get0 in PROMISES0. des. inv PROMS. clarify.
      + econs; i.
        * erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.split_o mem_tgt'); cycle 1; eauto.
          des_ifs.
          { ss. destruct a. clarify. des; clarify. exfalso. eapply NPROMS.
            eapply Memory.split_get0 in PROMISES0. des.
            econs. erewrite Memory.remove_o; eauto. des_ifs; eauto.
            des; ss; clarify. }
          { ss. eapply COMPLETE. ii. eapply NPROMS.
            inv H. econs. instantiate (1:=msg).
            erewrite Memory.remove_o; eauto.
            erewrite Memory.split_o; eauto. des_ifs; ss; des; clarify. }
        * erewrite (@Memory.add_o mem2); eauto. des_ifs.
          { ss. des. clarify. exfalso. inv PROMS.
            erewrite Memory.remove_o in GET; eauto.
            des_ifs. ss. des; clarify. }
          { eapply FORGET. inv PROMS.
            erewrite Memory.remove_o in GET; eauto.
            erewrite Memory.split_o in GET; eauto. des_ifs.
            - ss; des; clarify.
              eapply Memory.split_get0 in PROMISES0. des. econs; eauto.
            - econs; eauto. }
      + econs; i.
        * erewrite (@Memory.add_o mem2); eauto.
          erewrite (@Memory.lower_o mem_tgt'); cycle 1; eauto.
          des_ifs. eapply COMPLETE.
          ii. eapply NPROMS. inv H. econs. instantiate (1:=msg).
          erewrite Memory.remove_o; eauto.
          erewrite Memory.lower_o; eauto. des_ifs. ss; des; clarify.
        * erewrite (@Memory.add_o mem2); eauto. des_ifs.
          { ss. des. clarify. exfalso. inv PROMS.
            erewrite Memory.remove_o in GET; eauto.
            des_ifs. ss. des; clarify. }
          { eapply FORGET. inv PROMS. econs.
            erewrite Memory.remove_o in GET; eauto.
            erewrite Memory.lower_o in GET; eauto. des_ifs. eauto. }
      + clarify.
  Qed.

  Definition forget_event e_src e_tgt: Prop :=
    match e_tgt with
    | ThreadEvent.promise _ _ _ _ _ => e_src = ThreadEvent.silent
    | _ => e_src = e_tgt
    end.

  Lemma forget_event_same_machine_event
    :
      forget_event <2= same_machine_event.
  Proof.
    ii. unfold forget_event in *. des_ifs.
  Qed.

  Lemma self_promise_remove
        P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc'
        mem_src mem_tgt mem_tgt' e_tgt
        (NOREAD: P <1= no_read_msgs prom.(promised))
        (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (MEM: forget_memory (promised prom) mem_src mem_tgt)
        (LCWF: Local.wf (Local.mk v prom) mem_tgt)
        (CLOSED: Memory.closed mem_tgt)
    :
      exists mem_src' e_src,
        (<<STEP: opt_pred_step
                   (P /1\ no_promise) e_src th_src
                   (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
        (<<EVT: forget_event e_src e_tgt>>) /\
        (<<MEM: forget_memory (promised prom') mem_src' mem_tgt'>>).
  Proof.
    dup MEM. eapply forget_memory_le in MEM0.
    clarify. inv STEP. dup SAT. eapply NOREAD in SAT.
    des. inv STEP0. inv STEP.
    - inv STEP0. ss. inv LOCAL. clarify. ss.
      exists mem_src, ThreadEvent.silent. esplits; eauto.
      eapply self_promise_remove_promise; eauto.
    - inv STEP0. ss. inv LOCAL; clarify; ss.
      + exists mem_src, ThreadEvent.silent.
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto.
      + exists mem_src, (ThreadEvent.read loc ts val released ord).
        inv LOCAL0. ss. clarify.
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs 2; eauto. econs; eauto.
        inv MEM. rewrite COMPLETE; eauto.
      + exploit self_promise_remove_write; eauto. i. des.
        exists mem_src', (ThreadEvent.write loc from to val released ord).
        esplits; eauto. econs. econs; eauto. econs; eauto.
        econs 2; eauto. econs; eauto.
      + exploit Local.read_step_future; eauto. i. des.
        inv LOCAL1. ss. exploit self_promise_remove_write; eauto. i. des.
        exists mem_src',
        (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw).
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
        inv MEM. rewrite COMPLETE; eauto.
      + inv LOCAL0. ss. clarify.
        exists mem_src, (ThreadEvent.fence ordr ordw).
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
        ii. rewrite Memory.bot_get in *. clarify.
      + inv LOCAL0. ss. clarify.
        exists mem_src, (ThreadEvent.syscall e).
        esplits; eauto. econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. ss.
        ii. rewrite Memory.bot_get in *. clarify.
      + inv LOCAL0. ss. clarify.
        exists mem_src, ThreadEvent.failure. esplits; eauto.
        econs. econs; ss; eauto. econs; eauto.
        econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
        ii. ss. erewrite Memory.bot_get in *. clarify.
  Qed.


End SELFPROMISEREMOVE.


Section UNCHANGABLES.

  Inductive unchangable (mem prom: Memory.t) (l: Loc.t) (t: Time.t) (from: Time.t) (msg: Message.t): Prop :=
  | unchangable_intro
      (GET: Memory.get l t mem = Some (from, msg))
      (NPROM: Memory.get l t prom = None)
  .

  Inductive unwritable (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unwritable_intro
      to from msg
      (UNCH: unchangable mem prom l to from msg)
      (ITV: Interval.mem (from, to) t)
  .

  Inductive unchangable_ts (mem prom: Memory.t) (l: Loc.t) (t: Time.t): Prop :=
  | unchangable_ts_intro
      from msg
      (UNCH: unchangable mem prom l t from msg)
  .

  Lemma unchangable_promise mem0 prom0 loc from to msg prom1 mem1 kind
        (PROMISE: Memory.promise prom0 mem0 loc from to msg prom1 mem1 kind)
    :
      unchangable mem0 prom0 <4= unchangable mem1 prom1.
  Proof.
    ii. inv PR. inv PROMISE.
    - econs.
      + eapply Memory.add_get1; eauto.
      + eapply Memory.add_get0 in MEM. erewrite Memory.add_o; eauto.
        des_ifs. ss. des. clarify.
    - econs.
      + erewrite Memory.split_o; eauto. eapply Memory.split_get0 in MEM.
        des. des_ifs.
        * ss. des. clarify.
        * ss. destruct a. clarify. eapply Memory.split_get0 in PROMISES. des; clarify.
      + eapply Memory.split_get0 in MEM. des.
        erewrite Memory.split_o; eauto.
        eapply Memory.split_get0 in PROMISES.
        des_ifs; ss; des; clarify.
    - econs.
      + erewrite Memory.lower_o; eauto. eapply Memory.lower_get0 in MEM.
        des. des_ifs. ss. des. clarify. exfalso.
        eapply Memory.lower_get0 in PROMISES. des. clarify.
      + erewrite Memory.lower_o; eauto.
        eapply Memory.lower_get0 in PROMISES.
        des_ifs. ss. des. clarify.
    - econs.
      + erewrite Memory.remove_o; eauto. eapply Memory.remove_get0 in MEM.
        des. des_ifs. ss. des. clarify. exfalso.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
      + erewrite Memory.remove_o; eauto.
        eapply Memory.remove_get0 in PROMISES. des_ifs.
  Qed.

  Lemma unchangable_remove mem prom0 loc from to msg prom1
        (PROMISE: Memory.remove prom0 loc from to msg prom1)
    :
      unchangable mem prom0 <4= unchangable mem prom1.
  Proof.
    ii. inv PR. econs; eauto.
    erewrite Memory.remove_o; eauto. des_ifs.
  Qed.

  Lemma unchangable_increase pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
    :
      unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) <4=
      unchangable th1.(Thread.memory) th1.(Thread.local).(Local.promises).
  Proof.
    inv STEP.
    - inv STEP0; ss. inv LOCAL. i.
      hexploit unchangable_promise; eauto.
    - i. inv STEP0; ss. inv LOCAL; try inv LOCAL0; ss.
      + inv WRITE. exploit unchangable_promise; eauto.
        eapply unchangable_remove; eauto.
      + inv LOCAL1. inv LOCAL2. ss. inv WRITE.
        exploit unchangable_promise; eauto.
        eapply unchangable_remove; eauto.
  Qed.

  Lemma unchangable_rtc_increase P lang (th0 th1: Thread.t lang)
        (STEPS: rtc (tau (@pred_step P lang))th0 th1)
    :
      unchangable th0.(Thread.memory) th0.(Thread.local).(Local.promises) <4=
      unchangable th1.(Thread.memory) th1.(Thread.local).(Local.promises).
  Proof.
    ginduction STEPS; ss. i.
    eapply IHSTEPS.
    inv H. inv TSTEP. inv STEP. eapply unchangable_increase; eauto.
  Qed.

  Lemma other_promise_unchangable c tid1 tid2 st1 st2 lc1 lc2
        (CWF: Configuration.wf c)
        (TID1: IdentMap.find tid1 c.(Configuration.threads) = Some (st1, lc1))
        (TID2: IdentMap.find tid2 c.(Configuration.threads) = Some (st2, lc2))
        (DIFF: tid1 <> tid2)
        l t from msg
        (GET: Memory.get l t lc2.(Local.promises) = Some (from, msg))
    :
      unchangable c.(Configuration.memory) lc1.(Local.promises) l t from msg.
  Proof.
    inv CWF. inv WF. destruct st1, st2. econs; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF. eauto.
    - destruct (Memory.get l t (Local.promises lc1)) eqn:GET0; eauto. exfalso.
      exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ. destruct p.
      inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply Memory.get_ts in GET. eapply Memory.get_ts in GET0. des; clarify.
      eapply x1; eauto.
      + instantiate (1:=t). econs; ss; eauto. refl.
      + econs; ss; eauto. refl.
  Qed.

  Definition promise_not_in (MSGS : Loc.t -> Time.t -> Prop)
             (e : ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to _ _ =>
      forall t (IN: Interval.mem (from, to) t), ~ (MSGS loc t)
    | _ => True
    end.

  Lemma step_promise_not_in_other_msgs
        promises1 mem1 loc from1 to1 msg promises3 mem2 kind
        (PROMISE: Memory.promise promises1 mem1 loc from1 to1 msg promises3 mem2 kind)
    :
      ~ unchangable_ts mem1 promises1 loc to1.
  Proof.
    ii. inv H. inv UNCH. inv PROMISE.
    - dup GET. eapply Memory.add_get1 in GET; eauto.
      eapply Memory.add_get0 in MEM. des. clarify.
    - dup GET. eapply Memory.split_get1 in GET; eauto.
      eapply Memory.split_get0 in MEM. des. clarify.
    - dup GET. eapply Memory.lower_get1 in GET; eauto.
      eapply Memory.lower_get0 in MEM. des. clarify.
      eapply Memory.lower_get0 in PROMISES. des. clarify.
    - eapply Memory.remove_get0 in PROMISES. des. clarify.
  Qed.

  Definition unwritable2 (mem prom: Memory.t) (l: Loc.t) (t: Time.t) :=
    (<<COV: covered l t mem>>) /\
    (<<NCOV: ~ covered l t prom>>).

  Lemma unwritable_eq mem prom
        (MLE: Memory.le prom mem)
        l t
    :
      unwritable mem prom l t <-> unwritable2 mem prom l t.
  Proof.
    split; i.
    - inv H. inv UNCH. econs.
      + econs; eauto.
      + ii. inv H.
        exploit Memory.get_disjoint.
        { eapply MLE. eapply GET0. }
        { eapply GET. }
        i. des; clarify.
        eapply x0; eauto.
    - inv H. inv H0. econs; eauto. econs; eauto.
      destruct (Memory.get l to prom) eqn:GET0; auto. destruct p. exfalso.
      dup GET0. eapply MLE in GET0. clarify. eapply H1. econs; eauto.
  Qed.

  Lemma step_write_not_in_write promises1 mem1 loc from1 to1 val released promises3 mem2 kind
        (MLE: Memory.le promises1 mem1)
        (WRITE: Memory.write promises1 mem1 loc from1 to1 val released promises3 mem2 kind)
        t
        (IN: Interval.mem (from1, to1) t)
    :
      ~ unwritable mem1 promises1 loc t.
  Proof.
    rewrite unwritable_eq; auto.
    unfold unwritable2. inv WRITE. apply or_not_and. inv PROMISE.
    - left. ii. inv H. dup GET. eapply Memory.add_get1 in GET; eauto.
      eapply Memory.add_get0 in MEM. des.
      exploit Memory.get_disjoint.
      + eapply GET.
      + eapply GET2.
      + i. des; clarify. eauto.
    - right. eapply Memory.split_get0 in PROMISES. des. ii. apply H.
      econs; eauto. inv IN. econs; ss; eauto. etrans; eauto.
      inv MEM. inv SPLIT. left. eauto.
    - right. eapply Memory.lower_get0 in PROMISES. des. ii. apply H.
      econs; eauto.
    - right. eapply Memory.remove_get0 in PROMISES. des. ii. apply H.
      econs; eauto.
  Qed.

  Lemma step_write_not_in lang (th_tgt th_tgt': Thread.t lang) e_tgt pf
        (MLE: Memory.le th_tgt.(Thread.local).(Local.promises) th_tgt.(Thread.memory))
        (STEP: Thread.step pf e_tgt th_tgt th_tgt')
    :
      write_not_in (unwritable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))
                   e_tgt.
  Proof.
    inv STEP.
    - inv STEP0; ss.
    - inv STEP0; ss. inv LOCAL; ss.
      + inv LOCAL0. ii. exploit step_write_not_in_write; eauto.
      + inv LOCAL1. inv LOCAL2. ss. ii. exploit step_write_not_in_write; eauto.
  Qed.

  Lemma unwritable_increase pf e lang (th0 th1: Thread.t lang)
        (STEP: Thread.step pf e th0 th1)
    :
      unwritable th0.(Thread.memory) th0.(Thread.local).(Local.promises) <2=
      unwritable th1.(Thread.memory) th1.(Thread.local).(Local.promises).
  Proof.
    ii. inv PR.
    eapply unchangable_increase in UNCH; eauto.
    econs; eauto.
  Qed.

  Lemma rtc_unwritable_increase lang (th0 th1: Thread.t lang)
        (STEP: rtc (Thread.tau_step (lang:=lang)) th0 th1)
    :
      unwritable th0.(Thread.memory) th0.(Thread.local).(Local.promises) <2=
      unwritable th1.(Thread.memory) th1.(Thread.local).(Local.promises).
  Proof.
    induction STEP; eauto.
    i. inv H. inv TSTEP. eapply IHSTEP. eapply unwritable_increase; eauto.
  Qed.

  Lemma steps_write_not_in P lang (th_tgt th_tgt': Thread.t lang)
        (MLE: Memory.le th_tgt.(Thread.local).(Local.promises) th_tgt.(Thread.memory))
        (STEP: rtc (tau (@pred_step P lang)) th_tgt th_tgt')
    :
      rtc (tau (@pred_step (P /1\ write_not_in (unwritable th_tgt.(Thread.memory) th_tgt.(Thread.local).(Local.promises))) lang)) th_tgt th_tgt'.
  Proof.
    ginduction STEP.
    - i. refl.
    - i. inv H. inv TSTEP. econs 2.
      + econs; eauto. econs; eauto.
        split; auto. inv STEP0. eapply step_write_not_in; eauto.
      + inv STEP0. exploit IHSTEP.
        * eapply step_promises_le in MLE; eauto.
        * i. eapply pred_step_rtc_mon; eauto.
          i. ss. des. split; auto. eapply write_not_in_mon; eauto.
          i. eapply unwritable_increase; eauto.
  Qed.

  Lemma other_promise_unwritable c tid1 tid2 st1 st2 lc1 lc2
        (CWF: Configuration.wf c)
        (TID1: IdentMap.find tid1 c.(Configuration.threads) = Some (st1, lc1))
        (TID2: IdentMap.find tid2 c.(Configuration.threads) = Some (st2, lc2))
        (DIFF: tid1 <> tid2)
        l t
        (COV: covered l t lc2.(Local.promises))
    :
      unwritable c.(Configuration.memory) lc1.(Local.promises) l t.
  Proof.
    inv CWF. inv WF. inv COV. destruct st1, st2.
    rewrite unwritable_eq; cycle 1.
    { exploit THREADS; try apply TID1. i. inv x1. auto. }
    unfold unwritable2. esplits; eauto.
    - exploit THREADS; try apply TID2; eauto. intros LCWF. inv LCWF.
      econs; eauto.
    - ii. inv H. exploit DISJOINT; eauto. intros LCDISJ. inv LCDISJ.
      inv DISJOINT0. exploit DISJOINT1; eauto. i. des.
      eapply x1; eauto.
  Qed.

End UNCHANGABLES.



Section OTHERPROMISEREMOVE.

  Lemma other_promise_remove_write v v' prom'
        loc from to val releasedm released ord sc sc' mem_src
        mem_tgt mem_tgt' kind others
        (WRITE: Local.write_step
                  (Local.mk v Memory.bot) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (MEM: forget_memory others mem_src mem_tgt)
        (OTHERS: ~ others loc to)
  :
    exists mem_src',
      (<<WRITE: Local.write_step
                  (Local.mk v Memory.bot) sc mem_src
                  loc from to val releasedm released ord
                  (Local.mk v' Memory.bot) sc' mem_src' Memory.op_kind_add>>) /\
      (<<MEM: forget_memory others mem_src' mem_tgt'>>).
  Proof.
    exploit write_msg_wf; eauto. i. des.
    inv WRITE. ss. clarify. exploit memory_write_bot_add; eauto. i. clarify.
    dup WRITE0. inv WRITE0. inv PROMISE.
    exploit write_succeed; eauto.
    { instantiate (1:=mem_src). i. eapply forget_memory_le in MEM.
      eapply memory_le_covered in COVER; eauto. ii.
      exploit write_disjoint; try apply WRITE1; eauto.
      { eapply Memory.bot_le. }
      i. des; eauto. inv PROMISED.
      erewrite Memory.bot_get in GET. clarify. }
    i. des. exists mem2. econs; eauto.
    inv MEM. inv WRITE. inv PROMISE. econs; i.
    - erewrite (@Memory.add_o mem2); eauto.
      erewrite (@Memory.add_o mem_tgt'); cycle 1; eauto. des_ifs. eauto.
    - erewrite (@Memory.add_o mem2); eauto. des_ifs; eauto.
      ss. des. clarify.
  Qed.

  Lemma other_promise_remove
        P lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
        mem_src mem_tgt mem_tgt' e_tgt others
        (PRED: P <1= (no_read_msgs others /1\ write_not_in others /1\ no_promise))
        (STEP: (@pred_step P) lang e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (MEM: forget_memory others mem_src mem_tgt)
    :
      exists mem_src',
        (<<STEP: (@pred_step P lang)
                   e_tgt th_src
                   (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
        (<<MEM: forget_memory others mem_src' mem_tgt'>>).
  Proof.
    dup MEM. eapply forget_memory_le in MEM0.
    clarify. inv STEP. des. inv STEP0.
    dup SAT. eapply PRED in SAT. des. inv STEP.
    { inv STEP0. ss; clarify. }
    inv STEP0. inv LOCAL; ss.
    - exists mem_src. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify.
      exists mem_src. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto. econs; eauto. econs; eauto.
      inv MEM. erewrite COMPLETE; eauto.
    - ss. exploit other_promise_remove_write; eauto.
      { exploit write_msg_wf; eauto. i. des.
        eapply SAT2. econs; eauto. refl. }
      i. des. exists mem_src'. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - ss. inv LOCAL1. ss.
      exploit other_promise_remove_write; eauto.
      { exploit write_msg_wf; eauto. i. des.
        eapply SAT2. econs; eauto. refl. }
      i. des. exists mem_src'. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
      econs; eauto. econs; eauto. inv MEM. erewrite COMPLETE; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

End OTHERPROMISEREMOVE.


Section UNCHANGEDON.

  Inductive unchanged_on (P: Loc.t -> Time.t -> Prop) m0 m1 : Prop :=
  | unchanged_on_intro
      (NCOV: forall l t (IN: P l t) (COV: covered l t m1), covered l t m0)
      (FUTURE : Memory.le m0 m1)
  .
  Global Program Instance le_PreOrder P: PreOrder (unchanged_on P).
  Next Obligation. ii. econs; eauto. refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; eauto. etrans; eauto. Qed.

  Lemma unchanged_on_mon L0 L1
        m0 m1
        (NOTIN: unchanged_on L1 m0 m1)
        (LE: L0 <2= L1)
    :
      unchanged_on L0 m0 m1.
  Proof.
    inv NOTIN. econs; eauto.
  Qed.

  Lemma unchanged_on_write v v' prom'
        L loc from to val releasedm released ord sc sc' mem_src
        mem_tgt mem_tgt' kind
        (WRITE: Local.write_step
                  (Local.mk v Memory.bot) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (MEM: unchanged_on L mem_tgt mem_src)
        (WRITEIN: forall t (IN: Interval.mem (from, to) t), (L loc t))
    :
      exists mem_src',
        (<<WRITE: Local.write_step
                    (Local.mk v Memory.bot) sc mem_src
                    loc from to val releasedm released ord
                    (Local.mk v' Memory.bot) sc' mem_src' Memory.op_kind_add>>) /\
        (<<MEM: unchanged_on L mem_tgt' mem_src'>>).
  Proof.
    inv MEM. inv WRITE. ss. clarify. exploit memory_write_bot_add; eauto. i. clarify.
    exploit write_msg_wf; eauto. i. des.
    inv WRITE0. inv PROMISE. dup MEM. eapply Memory.add_get0 in MEM; eauto. des.
    exploit write_succeed; eauto.
    { instantiate (1:=mem_src). ii.
      exploit NCOV; eauto. intros COV. inv COV.
      exploit Memory.get_disjoint.
      - eapply GET0.
      - eapply Memory.add_get1; eauto.
      - i. des; clarify. eauto. }
    i. des.
    exists mem2. esplits; eauto.
    inv WRITE. inv PROMISE.
    econs; eauto.
    - ii. inv COV. erewrite Memory.add_o in GET1; cycle 1; eauto. des_ifs.
      + ss. des. clarify. econs; eauto.
      + exploit NCOV; eauto.
        * econs; eauto.
        * i. inv x. econs; eauto. eapply Memory.add_get1; eauto.
    - ii. erewrite Memory.add_o; eauto.
      erewrite Memory.add_o in LHS; cycle 1; eauto. des_ifs.
      eapply FUTURE; eauto.
  Qed.

  Lemma unchanged_on_step
        P L lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
        mem_src mem_tgt mem_tgt' e_tgt
        (PRED: P <1= (write_in L /1\ no_promise))
        (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (MEM: unchanged_on L mem_tgt mem_src)
    :
      exists mem_src',
        (<<STEP: (@pred_step P lang)
                   e_tgt th_src
                   (Thread.mk lang st' (Local.mk v' Memory.bot) sc' mem_src')>>) /\
        (<<MEM: unchanged_on L mem_tgt' mem_src'>>).
  Proof.
    dup MEM. inv MEM.
    clarify. inv STEP. des. inv STEP0.
    dup SAT. eapply PRED in SAT. des. inv STEP.
    { inv STEP0. ss; clarify. }
    inv STEP0. inv LOCAL; ss.
    - exists mem_src. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify.
      exists mem_src. esplits; eauto. econs; eauto. econs; eauto.
      econs 2; eauto. econs; eauto.
    - exploit unchanged_on_write; eauto. i. des. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL1. ss.
      exploit unchanged_on_write; eauto. i. des. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
    - inv LOCAL0. ss. clarify. exists mem_src. esplits; eauto.
      econs; eauto. econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

  Lemma write_not_in_unchanged_on_write L v v' prom'
        loc from to val releasedm released ord sc sc'
        mem_tgt mem_tgt' kind
        (WRITE: Local.write_step
                  (Local.mk v Memory.bot) sc mem_tgt
                  loc from to val releasedm released ord
                  (Local.mk v' prom') sc' mem_tgt' kind)
        (NOTIN: forall t (IN: Interval.mem (from, to) t), ~ (L loc t))
    :
      unchanged_on L mem_tgt mem_tgt'.
  Proof.
    inv WRITE. ss. clarify.
    exploit memory_write_bot_add; eauto. i. clarify.
    inv WRITE0. inv PROMISE. econs.
    - i. rewrite add_covered in COV; eauto. des; auto.
      clarify. exfalso. eapply NOTIN; eauto.
    - ii. eapply Memory.add_get1; eauto.
  Qed.

  Lemma write_not_in_unchanged_on P L e lang (th0 th1: Thread.t lang)
        (STEP: pred_step P e th0 th1)
        (PRED: P <1= (write_not_in L /1\ no_promise))
        (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
    :
      unchanged_on L th0.(Thread.memory) th1.(Thread.memory).
  Proof.
    inv STEP. eapply PRED in SAT. des. inv STEP0. inv STEP.
    - inv STEP0; ss; des; clarify.
    - des. inv STEP0. ss. inv LOCAL; try refl.
      + destruct lc1, lc2. ss. clarify. exploit write_not_in_unchanged_on_write; eauto.
      + inv LOCAL1. ss.
        destruct lc1, lc2. ss. clarify. exploit write_not_in_unchanged_on_write; eauto.
  Qed.

End UNCHANGEDON.

Lemma pf_step_memory_le lang (th0 th1: Thread.t lang) e
      (STEP: pred_step no_promise e th0 th1)
      (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
  :
    Memory.le th0.(Thread.memory) th1.(Thread.memory).
Proof.
  exploit write_not_in_unchanged_on; eauto.
  - i. instantiate (1:=fun _ _ => False).
    ss. splits; eauto. unfold write_not_in. des_ifs.
  - i. inv x0. auto.
Qed.


Section MAPPED.

  Variable f: Loc.t -> Time.t -> Time.t -> Prop.
  Hypothesis map_le:
    forall loc t0 t1 ft0 ft1
           (MAP0: f loc t0 ft0)
           (MAP1: f loc t1 ft1),
      Time.le t0 t1 -> Time.le ft0 ft1.
  Hypothesis map_bot:
    forall loc,
      f loc Time.bot Time.bot.
  Hypothesis map_eq:
    forall loc to ft0 ft1
           (MAP0: f loc to ft0)
           (MAP1: f loc to ft1),
      ft0 = ft1.

  Definition dom loc to: Prop :=
    exists fto, f loc to fto.

  Definition collapsed (loc: Loc.t) (t0 t1: Time.t): Prop :=
    exists ft,
      (<<MAP0: f loc t0 ft>>) /\ (<<MAP1: f loc t1 ft>>).

  (* Definition collapsed (loc: Loc.t) (t0 t1: Time.t): Prop := *)
  (*   f loc t0 = f loc t1. *)

  (* Global Program Instance collapsed_Equivalence loc: *)
  (*   Equivalence (collapsed loc). *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   unfold collapsed. ii. ss. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   unfold collapsed. ii. ss. *)
  (* Qed. *)
  (* Next Obligation. *)
  (* Proof. *)
  (*   unfold collapsed. ii. etrans; eauto. *)
  (* Qed. *)

  Lemma collapsed_inside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (CLPS: collapsed loc t0 t3)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      collapsed loc t1 t2.
  Proof.
    eapply map_le in TLE0; eauto.
    eapply map_le in TLE1; eauto.
    eapply map_le in TLE2; eauto.
    unfold collapsed in *. des.
    hexploit (map_eq MAP0 MAP4). i. subst.
    hexploit (map_eq MAP3 MAP5). i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    exploit TimeFacts.antisym; eauto. i. subst.
    esplits; eauto.
  Qed.

  Lemma not_collapsed_outside
        loc
        t0 t1 t2 t3
        ft0 ft1 ft2 ft3
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (MAP2: f loc t2 ft2)
        (MAP3: f loc t3 ft3)
        (NCLPS: ~ collapsed loc t1 t2)
        (TLE0: Time.le t0 t1)
        (TLE1: Time.le t1 t2)
        (TLE2: Time.le t2 t3)
    :
      ~ collapsed loc t0 t3.
  Proof.
    ii. apply NCLPS. eapply collapsed_inside.
    - apply MAP0.
    - apply MAP1.
    - apply MAP2.
    - apply MAP3.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma map_lt_only_if
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      Time.lt ft0 ft1 -> Time.lt t0 t1.
  Proof.
    set (DenseOrder.DenseOrderFacts.OrderTac.TO.lt_total t0 t1). des; eauto.
    - clarify. i.
      hexploit (map_eq MAP0 MAP1). i. subst.
      timetac.
    - exploit map_le.
      + eapply MAP1.
      + eapply MAP0.
      + left. eauto.
      + i. timetac.
  Qed.
  Hint Resolve map_lt_only_if.

  Definition map_eq_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      t0 = t1 <-> ft0 = ft1.
  Proof.
    split; i; clarify; eauto.
    exfalso. apply CLPS. eexists. eauto.
  Qed.
  Hint Resolve map_eq_iff.

  Definition map_lt_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i; cycle 1.
    { eapply map_lt_only_if; eauto. }
    exploit map_le.
    - eapply MAP0.
    - eapply MAP1.
    - left. eauto.
    - i. destruct x; auto. exfalso. apply CLPS.
      destruct H0. eexists. eauto.
  Qed.
  Hint Resolve map_lt_iff.

  Definition map_le_iff
             loc t0 t1 ft0 ft1
             (MAP0: f loc t0 ft0)
             (MAP1: f loc t1 ft1)
             (CLPS: ~ collapsed loc t0 t1)
    :
      Time.le t0 t1 <-> Time.le ft0 ft1.
  Proof.
    repeat rewrite DenseOrder.DenseOrder.le_lteq.
    split; i; des; clarify; eauto.
    - left. erewrite <- map_lt_iff; eauto.
    - right. eapply map_eq_iff; eauto.
  Qed.
  Hint Resolve map_le_iff.

  Definition timemap_map (tm ftm: TimeMap.t): Prop :=
    forall loc, f loc (tm loc) (ftm loc).


  Record view_map (vw fvw: View.t): Prop :=
    view_map_intro
      { map_pln: timemap_map vw.(View.pln) fvw.(View.pln);
        map_rlx: timemap_map vw.(View.rlx) fvw.(View.rlx);
      }.

  (* Inductive view_map (vw fvw: View.t): Prop := *)
  (* | view_map_intro *)
  (*     (PLN: timemap_map vw.(View.pln) fvw.(View.pln)) *)
  (*     (RLX: timemap_map vw.(View.rlx) fvw.(View.rlx)) *)
  (* . *)

  Inductive opt_view_map: option View.t -> option View.t -> Prop :=
  | opt_view_map_some
      vw fvw
      (MAP: view_map vw fvw)
    :
      opt_view_map (Some vw) (Some fvw)
  | opt_view_map_none
    :
      opt_view_map None None
  .

  Record tview_map (vw fvw: TView.t): Prop :=
    tview_map_intro
      { map_rel: forall loc, view_map (vw.(TView.rel) loc) (fvw.(TView.rel) loc);
        map_cur: view_map vw.(TView.cur) fvw.(TView.cur);
        map_acq: view_map vw.(TView.acq) fvw.(TView.acq);
      }.

  (* Inductive tview_map (vw fvw: TView.t): Prop := *)
  (* | tview_map_intro *)
  (*     (REL: forall loc, view_map (vw.(TView.rel) loc) (fvw.(TView.rel) loc)) *)
  (*     (CUR: view_map vw.(TView.cur) fvw.(TView.cur)) *)
  (*     (ACQ: view_map vw.(TView.acq) fvw.(TView.acq)) *)
  (* . *)

  Inductive msg_map: Message.t -> Message.t -> Prop :=
  | msg_map_reserve
    :
      msg_map Message.reserve Message.reserve
  | msg_map_full
      val released freleased
      (MAP: opt_view_map released freleased)
    :
      msg_map (Message.full val released) (Message.full val freleased)
  .

  Inductive tevent_map: ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | tevent_map_promise
      loc from ffrom to fto msg fmsg kind
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (MSG: msg_map msg fmsg)
    :
      tevent_map
        (ThreadEvent.promise loc from to msg kind)
        (ThreadEvent.promise loc ffrom fto fmsg kind)
  | tevent_map_read
      loc to fto val released freleased ordr
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased)
    :
      tevent_map
        (ThreadEvent.read loc to val released ordr)
        (ThreadEvent.read loc fto val freleased ordr)
  | tevent_map_write
      loc from ffrom to fto val released freleased ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASED: opt_view_map released freleased)
    :
      tevent_map
        (ThreadEvent.write loc from to val released ordw)
        (ThreadEvent.write loc ffrom fto val freleased ordw)
  | tevent_map_update
      loc from ffrom to fto valr valw releasedr freleasedr releasedw freleasedw ordr ordw
      (FROM: f loc from ffrom)
      (TO: f loc to fto)
      (RELEASEDR: opt_view_map releasedr freleasedr)
      (RELEASEDW: opt_view_map releasedw freleasedw)
    :
      tevent_map
        (ThreadEvent.update loc from to valr valw releasedr releasedr ordr ordw)
        (ThreadEvent.update loc ffrom fto valr valw freleasedr freleasedw ordr ordw)
  | tevent_map_fence
      or ow
    :
      tevent_map
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | tevent_map_syscall
      e
    :
      tevent_map
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | tevent_map_silent
    :
      tevent_map
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  .

  Definition non_collapsable (loc: Loc.t) (to: Time.t): Prop :=
    forall to' (TLE: Time.lt to' to),
      ~ collapsed loc to' to.

  Lemma map_lt_non_collapsable
        loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
        (NCLPS: non_collapsable loc t1)
    :
      Time.lt t0 t1 <-> Time.lt ft0 ft1.
  Proof.
    split; i.
    - erewrite <- map_lt_iff; eauto.
    - eapply map_lt_only_if; eauto.
  Qed.

  Inductive memory_map m fm: Prop :=
  | memory_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          exists fto ffrom fmsg' fmsg,
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg'>>) /\
            (<<MSGLE: Message.le fmsg fmsg'>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Inductive promises_map m fm: Prop :=
  | promises_map_intro
      (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)),
          exists fto ffrom fmsg,
            (<<NCLPS: non_collapsable loc to>>) /\
            (<<TO: f loc to fto>>) /\
            (<<MSG: msg_map msg fmsg>>) /\
            (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>))
      (ONLY: forall loc fto ffrom fmsg
                    (GET: Memory.get loc fto fm = Some (ffrom, fmsg)),
          exists to from msg,
            (<<TO: f loc to fto>>) /\
            (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
            (<<FROM: f loc from ffrom>>))
  .

  Lemma promises_map_memory_map m fm
        (PROMISES: promises_map m fm)
    :
      memory_map m fm.
  Proof.
    inv PROMISES. econs; eauto.
    i. exploit MAPPED; eauto. i. des.
    esplits; eauto. refl.
  Qed.
  Hint Resolve promises_map_memory_map.

  (* Inductive memory_map m fm: Prop := *)
  (* | memory_map_intro *)
  (*     (MAPPED: forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)), *)
  (*         exists fto ffrom fmsg, *)
  (*           (<<TO: f loc to fto>>) /\ *)
  (*           (<<MSG: msg_map msg fmsg>>) /\ *)
  (*           (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>)) *)
  (*     (ONLY: forall loc fto ffrom fmsg *)
  (*                   (GET: Memory.get loc fto fm = Some (ffrom, fmsg)), *)
  (*         exists to from msg, *)
  (*           (<<TO: f loc to fto>>) /\ *)
  (*           (<<GET: Memory.get loc to m = Some (from, msg)>>)) *)
  (* . *)

  (* Record promises_map (prom fprom: Memory.t): Prop := *)
  (*   promises_map_intro *)
  (*     { promises_memory_map: memory_map prom fprom; *)
  (*       promises_non_collapsable: *)
  (*         forall loc to from msg *)
  (*                (GET: Memory.get loc to prom = Some (from, msg)), *)
  (*           non_collapsable loc to; } *)
  (* . *)

  Lemma time_join_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.join t0 t1) (Time.join ft0 ft1).
  Proof.
    unfold Time.join. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma timemap_bot_map
    :
      timemap_map TimeMap.bot TimeMap.bot.
  Proof.
    ii. eapply map_bot.
  Qed.

  Lemma view_bot_map
    :
      view_map View.bot View.bot.
  Proof.
    econs.
    - eapply timemap_bot_map; eauto.
    - eapply timemap_bot_map; eauto.
  Qed.

  Lemma timemap_singleton_map loc to fto
        (MAP: f loc to fto)
    :
      timemap_map (TimeMap.singleton loc to) (TimeMap.singleton loc fto).
  Proof.
    ii. unfold TimeMap.singleton.
    setoid_rewrite LocFun.add_spec. des_ifs.
  Qed.

  Lemma singleton_ur_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur loc to) (View.singleton_ur loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    - eapply timemap_singleton_map; eauto.
    - eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_rw_map loc to fto
        (MAP: f loc to fto)
    :
      view_map (View.singleton_rw loc to) (View.singleton_rw loc fto).
  Proof.
    unfold View.singleton_ur. econs; ss.
    eapply timemap_singleton_map; eauto.
  Qed.

  Lemma singleton_ur_if_map loc to fto cond
        (MAP: f loc to fto)
    :
      view_map (View.singleton_ur_if cond loc to) (View.singleton_ur_if cond loc fto).
  Proof.
    unfold View.singleton_ur_if. des_ifs.
    - eapply singleton_ur_map; eauto.
    - eapply singleton_rw_map; eauto.
  Qed.

  Lemma timemap_join_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
    :
      timemap_map (TimeMap.join tm0 tm1) (TimeMap.join ftm0 ftm1).
  Proof.
    ii. unfold TimeMap.join.
    eapply time_join_map; eauto.
  Qed.

  Lemma timemap_le_map tm0 tm1 ftm0 ftm1
        (TM0: timemap_map tm0 ftm0)
        (TM1: timemap_map tm1 ftm1)
        (TMLE: TimeMap.le tm0 tm1)
    :
      TimeMap.le ftm0 ftm1.
  Proof.
    ii. eapply map_le; eauto.
  Qed.

  Lemma closed_timemap_map m fm tm ftm
        (MEM: memory_map m fm)
        (TM: timemap_map tm ftm)
        (CLOSED: Memory.closed_timemap tm m)
    :
      Memory.closed_timemap ftm fm.
  Proof.
    inv MEM. ii. specialize (CLOSED loc). des.
    eapply MAPPED in CLOSED. des. inv MSG.
    specialize (TM loc).
    hexploit (map_eq TM TO). i. subst.
    inv MSGLE. esplits; eauto.
  Qed.

  Lemma closed_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: view_map vw fvw)
        (CLOSED: Memory.closed_view vw m)
    :
      Memory.closed_view fvw fm.
  Proof.
    inv CLOSED. inv VIEW. econs.
    - eapply closed_timemap_map; eauto.
    - eapply closed_timemap_map; eauto.
  Qed.

  Lemma closed_opt_view_map m fm vw fvw
        (MEM: memory_map m fm)
        (VIEW: opt_view_map vw fvw)
        (CLOSED: Memory.closed_opt_view vw m)
    :
      Memory.closed_opt_view fvw fm.
  Proof.
    inv CLOSED.
    - inv VIEW. econs. eapply closed_view_map; eauto.
    - inv VIEW. econs.
  Qed.

  Lemma view_join_map v0 v1 fv0 fv1
        (VIEW0: view_map v0 fv0)
        (VIEW1: view_map v1 fv1)
    :
      view_map (View.join v0 v1) (View.join fv0 fv1).
  Proof.
    inv VIEW0. inv VIEW1.
    unfold View.join. econs; ss.
    - eapply timemap_join_map; eauto.
    - eapply timemap_join_map; eauto.
  Qed.

  Lemma tviewjoin_map tv0 tv1 ftv0 ftv1
        (TVIEW0: tview_map tv0 ftv0)
        (TVIEW1: tview_map tv1 ftv1)
    :
      tview_map (TView.join tv0 tv1) (TView.join ftv0 ftv1).
  Proof.
    inv TVIEW0. inv TVIEW1.
    unfold TView.join. econs; ss.
    - i. eapply view_join_map; eauto.
    - eapply view_join_map; eauto.
    - eapply view_join_map; eauto.
  Qed.

  Lemma unwrap_map released freleased
        (VIEW: opt_view_map released freleased)
    :
      view_map (View.unwrap released) (View.unwrap freleased).
  Proof.
    inv VIEW; ss.
  Qed.

  Lemma readable_map vw fvw loc to fto released freleased ordr
        (VIEW: view_map vw fvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
        (READABLE: TView.readable vw loc to released ordr)
    :
      TView.readable fvw loc fto freleased ordr.
  Proof.
    inv READABLE. econs.
    - eapply map_le; eauto.
      inv VIEW. eauto.
    - intros ORD. specialize (RLX ORD).
      eapply map_le; eauto.
      inv VIEW. eauto.
  Qed.

  Lemma read_tview_map tvw ftvw loc to fto released freleased ord
        (TVIEW: tview_map tvw ftvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
    :
      tview_map
        (TView.read_tview tvw loc to released ord)
        (TView.read_tview ftvw loc fto freleased ord).
  Proof.
    unfold TView.read_tview. econs; ss.
    - i. eapply map_rel; eauto.
    - eapply view_join_map.
      + eapply view_join_map.
        * eapply map_cur; eauto.
        * eapply singleton_ur_if_map; eauto.
      + des_ifs. eapply unwrap_map; eauto.
    - eapply view_join_map.
      + eapply view_join_map.
        * eapply map_acq; eauto.
        * eapply singleton_ur_if_map; eauto.
      + des_ifs. eapply unwrap_map; eauto.
  Qed.

  Lemma write_tview_map tvw ftvw sc fsc loc to fto ord
        (TVIEW: tview_map tvw ftvw)
        (TO: f loc to fto)
    :
      tview_map
        (TView.write_tview tvw sc loc to ord)
        (TView.write_tview ftvw fsc loc fto ord).
  Proof.
    unfold TView.write_tview. econs; ss.
    - i. setoid_rewrite LocFun.add_spec. des_ifs.
      + eapply view_join_map.
        * eapply map_cur; eauto.
        * eapply singleton_ur_map; eauto.
      + eapply view_join_map.
        * eapply map_rel; eauto.
        * eapply singleton_ur_map; eauto.
      + eapply map_rel in TVIEW. eauto.
    - eapply view_join_map.
      + eapply map_cur; eauto.
      + eapply singleton_ur_map; eauto.
    - eapply view_join_map.
      + eapply map_acq; eauto.
      + eapply singleton_ur_map; eauto.
  Qed.

  Lemma read_fence_tview_map tvw ftvw ord
        (TVIEW: tview_map tvw ftvw)
    :
      tview_map
        (TView.read_fence_tview tvw ord)
        (TView.read_fence_tview ftvw ord).
  Proof.
    unfold TView.read_fence_tview. econs; ss.
    - i. eapply map_rel; eauto.
    - des_ifs.
      + eapply map_acq; eauto.
      + eapply map_cur; eauto.
    - eapply map_acq; eauto.
  Qed.

  Lemma write_fence_sc_map tvw ftvw sc fsc ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
    :
      timemap_map
        (TView.write_fence_sc tvw sc ord)
        (TView.write_fence_sc ftvw fsc ord).
  Proof.
    unfold TView.write_fence_sc. des_ifs.
    eapply timemap_join_map; eauto.
    eapply map_rlx; eauto. eapply map_cur; eauto.
  Qed.

  Lemma write_fence_tview_map tvw ftvw sc fsc ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
    :
      tview_map
        (TView.write_fence_tview tvw sc ord)
        (TView.write_fence_tview ftvw fsc ord).
  Proof.
    unfold TView.write_fence_tview. econs; ss.
    - i. des_ifs.
      + econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
      + eapply map_cur; eauto.
      + eapply map_rel; eauto.
    - des_ifs.
      + econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
      + eapply map_cur; eauto.
    - eapply view_join_map.
      + eapply map_acq; eauto.
      + des_ifs. econs; ss.
        * eapply write_fence_sc_map; eauto.
        * eapply write_fence_sc_map; eauto.
  Qed.

  Lemma write_released_map tvw ftvw sc fsc loc to fto released freleased ord
        (TVIEW: tview_map tvw ftvw)
        (SC: timemap_map sc fsc)
        (TO: f loc to fto)
        (VIEW: opt_view_map released freleased)
    :
      opt_view_map
        (TView.write_released tvw sc loc to released ord)
        (TView.write_released ftvw fsc loc fto freleased ord).
  Proof.
    unfold TView.write_released. des_ifs; econs.
    eapply view_join_map; eauto.
    - eapply unwrap_map; eauto.
    - eapply map_rel; eauto. eapply write_tview_map; eauto.
  Qed.

  Lemma bot_promises_map fprom
        (MEM: promises_map Memory.bot fprom)
    :
      fprom = Memory.bot.
  Proof.
    inv MEM. eapply Memory.ext. i.
    rewrite Memory.bot_get.
    destruct (Memory.get loc ts fprom) eqn:GET; auto.
    destruct p. eapply ONLY in GET. des.
    rewrite Memory.bot_get in GET; eauto. clarify.
  Qed.

  Lemma msg_get_map m fm loc to from msg
        (MEM: memory_map m fm)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      exists ffrom fto fmsg fmsg',
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg'>>).
  Proof.
    inv MEM. eapply MAPPED in GET. des. esplits; eauto.
  Qed.

  Lemma msg_get_map_if m fm loc to fto from msg
        (MEM: memory_map m fm)
        (TO: f loc to fto)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      exists ffrom fmsg fmsg',
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg'>>).
  Proof.
    inv MEM. eapply MAPPED in GET. des.
    hexploit (map_eq TO TO0). i. subst.
    esplits; eauto.
  Qed.

  Lemma msg_get_map_only_if m fm
        (MEM: memory_map m fm)
        loc fto ffrom fmsg
        (GET: Memory.get loc fto fm = Some (ffrom, fmsg))
    :
      exists to from msg fmsg',
        (<<TO: f loc to fto>>) /\
        (<<GET: Memory.get loc to m = Some (from, msg)>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<MSG: msg_map msg fmsg'>>) /\
        (<<MSGLE: Message.le fmsg fmsg' >>)
  .
  Proof.
    inv MEM.
    dup GET. eapply ONLY in GET. des.
    dup GET. eapply MAPPED in GET1. des.
    hexploit (map_eq TO TO0). i. clarify.
    esplits; eauto.
  Qed.

  Lemma promise_consistent_map tvw ftvw prom fprom
        (TVIEW: tview_map tvw ftvw)
        (PROMS: promises_map prom fprom)
        (CONSISTENT: Local.promise_consistent (Local.mk tvw prom))
    :
      Local.promise_consistent (Local.mk ftvw fprom).
  Proof.
    ii. ss.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    inv MSG. exploit CONSISTENT; ss; eauto.
    i. erewrite <- map_lt_iff; eauto.
    eapply map_rlx. eapply map_cur. auto.
  Qed.

  Lemma nonsynch_loc_map loc prom fprom
        (PROMS: promises_map prom fprom)
        (NONSYNCH: Memory.nonsynch_loc loc prom)
    :
      Memory.nonsynch_loc loc fprom.
  Proof.
    ii. dup GET.
    inv PROMS. exploit ONLY; eauto. i. des.
    exploit MAPPED; eauto. i. des.
    hexploit (map_eq TO TO0). i. clarify.
    eapply NONSYNCH in GET1. des_ifs.
    - inv MSG. inv MAP. ss.
    - inv MSG.
  Qed.

  Lemma writable_map vw fvw sc fsc loc to fto released freleased ordw
        (VIEW: view_map vw fvw)
        (TO: f loc to fto)
        (RELEASED: opt_view_map released freleased)
        (NCLPS: non_collapsable loc to)
        (WRITABLE: TView.writable vw sc loc to ordw)
    :
      TView.writable fvw fsc loc fto ordw.
  Proof.
    inv WRITABLE. econs.
    erewrite <- map_lt_non_collapsable; eauto.
    eapply map_rlx. eauto.
  Qed.

  Lemma timemap_map_exists mem fmem tm
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      exists ftm,
        (<<TM: timemap_map tm ftm>>) /\
        (<<CLOSED: Memory.closed_timemap ftm fmem>>).
  Proof.
    hexploit (choice (fun loc to =>
                        (<<MAP: f loc (tm loc) to>>) /\
                        exists from val released,
                          Memory.get loc to fmem = Some (from, Message.full val released))).
    { intros loc. specialize (CLOSED loc). des.
      inv MEM. eapply MAPPED in CLOSED. des. inv MSG. inv MSGLE.
      esplits; eauto. }
    i. des. esplits; eauto.
    - ii. specialize (H loc). des. eauto.
    - ii. specialize (H loc). des. eauto.
  Qed.

  Lemma opt_view_map_exists mem fmem vw
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      exists fvw,
        (<<VIEW: opt_view_map vw fvw>>) /\
        (<<CLOSED: Memory.closed_opt_view fvw fmem>>).
  Proof.
    inv CLOSED.
    - inv CLOSED0.
      hexploit (timemap_map_exists MEM PLN). i. des.
      hexploit (timemap_map_exists MEM RLX). i. des.
      exists (Some (View.mk ftm ftm0)). esplits; eauto.
      econs. econs; eauto.
    - exists None. esplits; eauto. econs.
  Qed.

  Lemma msg_map_exists mem fmem msg
        (MEM: memory_map mem fmem)
        (CLOSED: Memory.closed_message msg mem)
    :
      exists fmsg,
        (<<MSG: msg_map msg fmsg>>) /\
        (<<CLOSED: Memory.closed_message fmsg fmem>>).
  Proof.
    inv CLOSED.
    - exploit opt_view_map_exists; eauto. i. des.
      exists (Message.full val fvw).
      esplits; eauto. econs; eauto.
    - exists Message.reserve.
      esplits; eauto. econs; eauto.
  Qed.

  Lemma add_succeed_wf mem1 loc from to msg mem2
        (ADD: Memory.add mem1 loc from to msg mem2)
    :
      (<<DISJOINT: forall to2 from2 msg2
                          (GET2: Memory.get loc to2 mem1 = Some (from2, msg2)),
          Interval.disjoint (from, to) (from2, to2)>>) /\
      (<<TO1: Time.lt from to>>) /\
      (<<MSG_WF: Message.wf msg>>).
  Proof.
    inv ADD. inv ADD0. esplits; eauto.
  Qed.

  Lemma lower_succeed_wf mem1 loc from to msg1 msg2 mem2
        (LOWER: Memory.lower mem1 loc from to msg1 msg2 mem2)
    :
      (<<GET: Memory.get loc to mem1 = Some (from, msg1)>>) /\
      (<<TS: Time.lt from to>>) /\
      (<<MSG_WF: Message.wf msg2>>) /\
      (<<MSG_LE: Message.le msg2 msg1>>).
  Proof.
    inv LOWER. inv LOWER0. esplits; eauto.
  Qed.

  Lemma split_succeed_wf mem1 loc ts1 ts2 ts3 msg2 msg3 mem2
        (SPLIT: Memory.split mem1 loc ts1 ts2 ts3 msg2 msg3 mem2)
    :
      (<<GET2: Memory.get loc ts3 mem1 = Some (ts1, msg3)>>) /\
      (<<TS12: Time.lt ts1 ts2>>) /\
      (<<TS23: Time.lt ts2 ts3>>) /\
      (<<MSG_WF: Message.wf msg2>>).
  Proof.
    inv SPLIT. inv SPLIT0. esplits; eauto.
  Qed.

  Lemma view_wf_map vw fvw
        (VIEW: view_map vw fvw)
        (VIEWWF: View.wf vw)
    :
      View.wf fvw.
  Proof.
    inv VIEWWF. inv VIEW.
    econs. eapply timemap_le_map; eauto.
  Qed.

  Lemma opt_view_wf_map vw fvw
        (VIEW: opt_view_map vw fvw)
        (VIEWWF: View.opt_wf vw)
    :
      View.opt_wf fvw.
  Proof.
    inv VIEWWF; inv VIEW; econs.
    eapply view_wf_map; eauto.
  Qed.

  Lemma msg_wf_map msg fmsg
        (MSG: msg_map msg fmsg)
        (MSGWF: Message.wf msg)
    :
      Message.wf fmsg.
  Proof.
    inv MSGWF.
    - inv MSG. econs; ss. eapply opt_view_wf_map; eauto.
    - inv MSG. econs.
  Qed.

  Lemma time_meet_map loc t0 t1 ft0 ft1
        (MAP0: f loc t0 ft0)
        (MAP1: f loc t1 ft1)
    :
      f loc (Time.meet t0 t1) (Time.meet ft0 ft1).
  Proof.
    unfold Time.meet. des_ifs.
    - eapply map_le in l; eauto. timetac.
    - destruct l0; auto.
      + eapply map_lt_only_if in H; eauto.
        exfalso. eapply Time.lt_strorder. etrans; eauto.
      + destruct H. auto.
  Qed.

  Lemma disjoint_map loc from0 ffrom0 to0 fto0 from1 ffrom1 to1 fto1
        (FROM0: f loc from0 ffrom0)
        (TO0: f loc to0 fto0)
        (FROM1: f loc from1 ffrom1)
        (TO1: f loc to1 fto1)
        (DISJOINT: Interval.disjoint (from0, to0) (from1, to1))
    :
      Interval.disjoint (ffrom0, fto0) (ffrom1, fto1).
  Proof.
    apply NNPP. ii. revert DISJOINT.
    apply disjoint_equivalent. apply disjoint_equivalent in H. des.
    splits.
    - eapply map_lt_only_if; eauto.
    - eapply map_lt_only_if; eauto.
    - eapply map_lt_only_if; eauto.
      + eapply time_join_map; eauto.
      + eapply time_meet_map; eauto.
  Qed.

  Lemma msg_get_promises_map m fm loc to from msg
        (MEM: promises_map m fm)
        (GET: Memory.get loc to m = Some (from, msg))
    :
      exists ffrom fto fmsg,
        (<<NCLPS: non_collapsable loc to>>) /\
        (<<GET: Memory.get loc fto fm = Some (ffrom, fmsg)>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg fmsg>>) /\
        (<<UNIQUE:
           forall to' (TO: f loc to' fto) frommsg
                  (GET: Memory.get loc to' m = Some frommsg),
             to = to'>>).
  Proof.
    inv MEM.
    exploit MAPPED; eauto. i. des.
    exploit ONLY; eauto. i. des.
    exploit MAPPED; try apply GET1; eauto. i. des.
    hexploit (map_eq TO0 TO1). i. subst.
    destruct (Time.le_lt_dec to to0); [destruct l|].
    - exfalso. exploit NCLPS0; eauto. econs; eauto.
    - destruct H. clarify. esplits; eauto.
      i. destruct frommsg. eapply MAPPED in GET. des.
      destruct (Time.le_lt_dec to to'); [destruct l|]; auto.
      + exfalso. exploit NCLPS1; eauto. econs; eauto.
      + exfalso. exploit NCLPS; eauto. econs; eauto.
    - exfalso. exploit NCLPS; eauto. econs; eauto.
  Qed.

  Lemma view_le_map vw0 vw1 fvw0 fvw1
        (VIEW0: view_map vw0 fvw0)
        (VIEW1: view_map vw1 fvw1)
        (VIEWLE: View.le vw0 vw1)
    :
      View.le fvw0 fvw1.
  Proof.
    inv VIEWLE. econs; eauto.
    - eapply timemap_le_map.
      + eapply map_pln; eauto.
      + eapply map_pln; eauto.
      + eauto.
    - eapply timemap_le_map.
      + eapply map_rlx; eauto.
      + eapply map_rlx; eauto.
      + eauto.
  Qed.

  Lemma opt_view_le_map vw0 vw1 fvw0 fvw1
        (VIEW0: opt_view_map vw0 fvw0)
        (VIEW1: opt_view_map vw1 fvw1)
        (VIEWLE: View.opt_le vw0 vw1)
    :
      View.opt_le fvw0 fvw1.
  Proof.
    inv VIEWLE.
    - inv VIEW0. econs.
    - inv VIEW0. inv VIEW1. econs.
      eapply view_le_map; eauto.
  Qed.

  Lemma msg_le_map msg0 msg1 fmsg0 fmsg1
        (MSG0: msg_map msg0 fmsg0)
        (MSG1: msg_map msg1 fmsg1)
        (MSGLE: Message.le msg1 msg0)
    :
      Message.le fmsg1 fmsg0.
  Proof.
    inv MSGLE.
    - inv MSG0. inv MSG1. econs; eauto.
      eapply opt_view_le_map; eauto.
    - inv MSG0. econs; eauto.
  Qed.

  Lemma add_promises_map mem0 fmem0 loc from ffrom to fto msg fmsg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (PROMS: promises_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg)
    :
      exists fmem1,
        (<<PROMS: promises_map mem1 fmem1>>) /\
        (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg).
    { i. dup GET2. eapply msg_get_map_only_if in GET2; eauto. des.
      eapply disjoint_map; eauto. }
    { erewrite <- map_lt_non_collapsable; eauto. }
    { eapply msg_wf_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_promises_map in GET; eauto.
        guardH o. des. unguard.
        esplits; eauto.
        eapply Memory.add_get1; eauto.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. exists to. esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_map_only_if in GET; eauto.
        guardH o. des. unguard.
        exists to0. esplits; eauto.
        eapply Memory.add_get1; eauto.
  Qed.

  Lemma lower_promises_map mem0 fmem0 loc from to msg0 msg1 fmsg1 mem1
        (LOWER: Memory.lower mem0 loc from to msg0 msg1 mem1)
        (MEM: promises_map mem0 fmem0)
        (MSG: msg_map msg1 fmsg1)
    :
      exists ffrom fto fmsg0 fmem1,
        (<<FROM: f loc from ffrom>>) /\
        (<<TO: f loc to fto>>) /\
        (<<MSG: msg_map msg0 fmsg0>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<LOWER: Memory.lower fmem0 loc ffrom fto fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.lower_get0; eauto. i. des.
    hexploit lower_succeed_wf; eauto. i. des.
    eapply msg_get_promises_map in GET; eauto. des.
    hexploit (@Memory.lower_exists fmem0 loc ffrom fto fmsg fmsg1); eauto.
    { erewrite <- map_lt_non_collapsable; eauto. }
    { eapply msg_wf_map; eauto. }
    { eapply msg_le_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.lower_get0; eauto.
      + eapply msg_get_promises_map in GET2; eauto.
        guardH o. des. unguard.
        exists fto0, ffrom0, fmsg0. esplits; eauto.
        erewrite Memory.lower_o; eauto. des_ifs.
        ss. des; clarify. exfalso. eauto.
    - i. erewrite Memory.lower_o in GET2; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
      + dup MEM. inv MEM. eapply ONLY in GET2.
        guardH o. des. unguard.
        exists to0, from0, msg.
        esplits; eauto. erewrite Memory.lower_o; eauto.
        des_ifs. ss; des; clarify.
        hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma split_promises_map mem0 fmem0 loc ts1 ts2 ts3 msg0 msg1 fmsg0 mem1 fts2
        (SPLIT: Memory.split mem0 loc ts1 ts2 ts3 msg0 msg1 mem1)
        (MEM: promises_map mem0 fmem0)
        (TS2: f loc ts2 fts2)
        (MSG: msg_map msg0 fmsg0)
        (NCLPS: non_collapsable loc ts2)
    :
      exists fts1 fts3 fmsg1 fmem1,
        (<<TS1: f loc ts1 fts1>>) /\
        (<<TS3: f loc ts3 fts3>>) /\
        (<<MSG: msg_map msg1 fmsg1>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<SPLIT: Memory.split fmem0 loc fts1 fts2 fts3 fmsg0 fmsg1 fmem1>>).
  Proof.
    exploit Memory.split_get0; eauto. i. des.
    hexploit split_succeed_wf; eauto. i. des.
    eapply msg_get_promises_map in GET3; eauto. des.
    hexploit (@Memory.split_exists fmem0 loc ffrom fts2 fto fmsg0 fmsg); eauto.
    { erewrite <- map_lt_non_collapsable; try apply TS12; eauto. }
    { erewrite <- map_lt_non_collapsable; try apply TS23; eauto. }
    { eapply msg_wf_map; eauto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      + ss. des; clarify.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      + eapply msg_get_promises_map in GET4; eauto.
        guardH o. guardH o0. des. unguard.
        exists fto0, ffrom0, fmsg1. esplits; eauto.
        erewrite Memory.split_o; eauto.
        des_ifs; ss; des; clarify.
        * exploit Memory.split_get0; eauto. i. des. clarify.
        * ss. des; clarify.
          hexploit UNIQUE0; try apply TO; eauto.
          i. clarify.
    - i. erewrite Memory.split_o in GET4; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
      + ss. des; clarify.
        esplits; eauto.
      + dup MEM. inv MEM. eapply ONLY in GET4.
        guardH o. guardH o0. des.
        esplits; eauto.
        erewrite Memory.split_o; eauto.
        unguard. ss. des_ifs; ss; eauto.
        * ss; des; clarify.
        * ss; des; clarify. exfalso.
          hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma remove_promises_map mem0 fmem0 loc from to msg mem1
        (REMOVE: Memory.remove mem0 loc from to msg mem1)
        (MEM: promises_map mem0 fmem0)
    :
      exists ffrom fto fmsg fmem1,
        (<<TO: f loc to fto>>) /\
        (<<FROM: f loc from ffrom>>) /\
        (<<MSG: msg_map msg fmsg>>) /\
        (<<MEM: promises_map mem1 fmem1>>) /\
        (<<REMOVE: Memory.remove fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    exploit Memory.remove_get0; eauto. i. des.
    eapply msg_get_promises_map in GET; eauto. des.
    hexploit (@Memory.remove_exists fmem0 loc ffrom fto fmsg); eauto.
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. ss.
      dup GET1. eapply msg_get_promises_map in GET1; eauto.
      guardH o. des. unguard.
      exists fto0, ffrom0, fmsg0. esplits; eauto.
      erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify.
      exploit UNIQUE; eauto. i. clarify.
    - i. erewrite Memory.remove_o in GET1; eauto. des_ifs.
      dup MEM. inv MEM. eapply ONLY in GET1.
      guardH o. des.
      esplits; eauto.
      erewrite Memory.remove_o; eauto.
      unguard. ss. des_ifs; ss; eauto.
      des; clarify. exfalso.
      hexploit (map_eq TO0 TO). i. clarify.
  Qed.

  Lemma add_memory_map mem0 fmem0 loc from ffrom to fto msg fmsg' fmsg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (MEM: memory_map mem0 fmem0)
        (FROM: f loc from ffrom)
        (TO: f loc to fto)
        (NCLPS: non_collapsable loc to)
        (MSG: msg_map msg fmsg')
        (MSGLE: Message.le fmsg fmsg')
        (MSGWF: Message.wf fmsg)
    :
      exists fmem1,
        (<<MEM: memory_map mem1 fmem1>>) /\
        (<<ADD: Memory.add fmem0 loc ffrom fto fmsg fmem1>>).
  Proof.
    hexploit add_succeed_wf; eauto. i. des.
    hexploit (@Memory.add_exists fmem0 loc ffrom fto fmsg).
    { i. dup GET2. eapply msg_get_map_only_if in GET2; eauto. des.
      eapply disjoint_map; eauto. }
    { erewrite <- map_lt_non_collapsable; eauto. }
    { auto. }
    i. des. esplits; eauto.
    econs.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify.
        esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_map in GET; eauto.
        guardH o. des. unguard.
        esplits; eauto.
        eapply Memory.add_get1; eauto.
    - i. erewrite Memory.add_o in GET; eauto. des_ifs.
      + ss. des; clarify. exists to. esplits; eauto.
        eapply Memory.add_get0; eauto.
      + eapply msg_get_map_only_if in GET; eauto.
        guardH o. des. unguard.
        exists to0. esplits; eauto.
        eapply Memory.add_get1; eauto.
  Qed.

  Definition mapped_time loc fto :=
    exists to, (<<MAPPED: f loc to fto>>).

  Definition wf_mappable_evt (e: ThreadEvent.t) : Prop :=
    match e with
    | ThreadEvent.promise loc from to msg kind =>
      match kind with
      | Memory.op_kind_add =>
        (<<FROM: mapped_time loc from>>) /\
        (<<TO: mapped_time loc to>>) /\
        (<<NCLPS: non_collapsable loc to>>)
      | Memory.op_kind_split _ _ =>
        (<<TO: mapped_time loc to>>) /\
        (<<NCLPS: non_collapsable loc to>>)
      | _ => True
      end
    | ThreadEvent.write loc from to val released ordw =>
      (<<FROM: mapped_time loc from>>) /\
      (<<TO: mapped_time loc to>>) /\
      (<<NCLPS: non_collapsable loc to>>)
    | ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw =>
      (<<TO: mapped_time loc to>>) /\
      (<<NCLPS: non_collapsable loc to>>)
    | _ => True
    end.

  (* Lemma step_map *)
  (*       P lang th_src th_tgt th_tgt' st st' v_src v_tgt v_tgt' prom_src prom_tgt prom_tgt' *)
  (*       sc_src sc_tgt sc_tgt' *)
  (*       mem_src mem_tgt mem_tgt' e_tgt *)
  (*       (MAPPABLE: P <1= wf_mappable_evt) *)
  (*       (* (PRED: P <1= promise_free) *) *)
  (*       (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt') *)
  (*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v_src prom_src) *)
  (*                                   sc_src mem_src) *)
  (*       (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v_tgt prom_tgt) *)
  (*                                    sc_tgt mem_tgt) *)
  (*       (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v_tgt' prom_tgt') *)
  (*                                     sc_tgt' mem_tgt') *)

  (*       (CLOSEDMAP0: Memory.closed_timemap sc_tgt mem_tgt) *)
  (*       (CLOSED0: Memory.closed mem_tgt) *)
  (*       (LCWF: Local.wf (Local.mk v_tgt prom_tgt) mem_tgt) *)
  (*       (INHABITED: Memory.inhabited mem_tgt) *)

  (*       (TVIEW: tview_map v_src v_tgt) *)
  (*       (MEM: memory_map mem_src mem_tgt) *)
  (*       (PROM: promises_map prom_src prom_tgt) *)
  (*       (SC: timemap_map sc_src sc_tgt) *)
  (*   : *)
  (*     exists e_src prom_src' v_src' sc_src' mem_src', *)
  (*       (<<STEP: Thread.step_allpf *)
  (*                  e_src th_src *)
  (*                  (Thread.mk lang st' (Local.mk v_src' prom_src') sc_src' mem_src')>>) /\ *)
  (*       (<<SC: timemap_map sc_src' sc_tgt'>>) /\ *)
  (*       (<<PROM: promises_map prom_src' prom_tgt'>>) /\ *)
  (*       (<<MEM: memory_map mem_src' mem_tgt'>>) /\ *)
  (*       (<<TVIEW: tview_map v_src' v_tgt'>>) /\ *)
  (*       (<<EVT: tevent_map e_src e_tgt>>) *)
  (* . *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma remove_memory_map mem0 fmem0 loc from to msg mem1 *)
  (*       (REMOVE: Memory.remove mem0 loc from to msg mem1) *)
  (*       (MEM: memory_map mem0 fmem0) *)
  (*   : *)
  (*     exists ffrom fto fmsg fmem1, *)
  (*       (<<TO: f loc to fto>>) /\ *)
  (*       (<<FROM: f loc from ffrom>>) /\ *)
  (*       (<<MSG: msg_map msg fmsg>>) /\ *)
  (*       (<<MEM: promises_map mem1 fmem1>>) /\ *)
  (*       (<<REMOVE: Memory.remove fmem0 loc ffrom fto fmsg fmem1>>). *)
  (* Proof. *)
  (*   exploit Memory.remove_get0; eauto. i. des. *)
  (*   eapply msg_get_promises_map in GET; eauto. des. *)
  (*   hexploit (@Memory.remove_exists fmem0 loc ffrom fto fmsg); eauto. *)
  (*   i. des. esplits; eauto. *)
  (*   econs. *)
  (*   - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. ss. *)
  (*     dup GET1. eapply msg_get_promises_map in GET1; eauto. *)
  (*     guardH o. des. unguard. *)
  (*     exists fto0, ffrom0, fmsg0. esplits; eauto. *)
  (*     erewrite Memory.remove_o; eauto. des_ifs; ss. des; clarify. *)
  (*     exploit UNIQUE; eauto. i. clarify. *)
  (*   - i. erewrite Memory.remove_o in GET1; eauto. des_ifs. *)
  (*     dup MEM. inv MEM. eapply ONLY in GET1. *)
  (*     guardH o. des. *)
  (*     esplits; eauto. *)
  (*     erewrite Memory.remove_o; eauto. *)
  (*     unguard. ss. des_ifs; ss; eauto. *)
  (*     des; clarify. exfalso. *)
  (*     hexploit (map_eq TO0 TO). i. clarify. *)
  (* Qed. *)



  (* Definition respecting_memory (P: Loc.t -> Time.t -> Prop) (m: Memory.t) := *)
  (*   forall loc to from msg (GET: Memory.get loc to m = Some (from, msg)), *)
  (*     (<<FROM: P loc from>>) /\ (<<TO: P loc to>>). *)

  (* (* Definition respecting_map (P: Loc.t -> Time.t -> Prop) (tm: TimeMap.t) := *) *)
  (* (*   forall loc, P loc (tm loc). *) *)
  (* Notation respecting_map P tm := (forall loc, P loc (tm loc)). *)

  (* Inductive respecting_view P view: Prop := *)
  (* | respecting_view_intro *)
  (*     (PLN: respecting_map P (View.pln view)) *)
  (*     (RLX: respecting_map P (View.rlx view)) *)
  (* . *)

  (* Inductive respecting_opt_view P: option View.t -> Prop := *)
  (* | respecting_opt_view_some *)
  (*     vw *)
  (*     (SOME: respecting_view P vw) *)
  (*   : *)
  (*     respecting_opt_view P (Some vw) *)
  (* | respecting_opt_view_none *)
  (*   : *)
  (*     respecting_opt_view P None *)
  (* . *)

  (* Inductive respecting_tview P tview: Prop := *)
  (* | respectin_tview_intro *)
  (*     (REL: forall loc : positive, respecting_view P (TView.rel tview loc)) *)
  (*     (CUR: respecting_view P (TView.cur tview)) *)
  (*     (ACQ: respecting_view P (TView.acq tview)) *)
  (* . *)

  (* Lemma closed_timemap_respecting P m f tm *)
  (*       (RESPECT: respecting_memory P m) *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED: Memory.closed_timemap tm m) *)
  (*   : *)
  (*     respecting_map P tm. *)
  (* Proof. *)
  (*   ii. specialize (CLOSED loc). des. *)
  (*   eapply RESPECT in CLOSED. des. eauto. *)
  (* Qed. *)

  (* Lemma closed_view_respecting P m f vw *)
  (*       (RESPECT: respecting_memory P m) *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED: Memory.closed_view vw m) *)
  (*   : *)
  (*     respecting_view P vw. *)
  (* Proof. *)
  (*   inv CLOSED. econs. *)
  (*   - eapply closed_timemap_respecting; eauto. *)
  (*   - eapply closed_timemap_respecting; eauto. *)
  (* Qed. *)

  (* Lemma closed_opt_view_respecting P m f vw *)
  (*       (RESPECT: respecting_memory P m) *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED: Memory.closed_opt_view vw m) *)
  (*   : *)
  (*     respecting_opt_view P vw. *)
  (* Proof. *)
  (*   inv CLOSED. *)
  (*   - econs. eapply closed_view_respecting; eauto. *)
  (*   - econs. *)
  (* Qed. *)

  (* Lemma closed_tview_respecting P m f tvw *)
  (*       (RESPECT: respecting_memory P m) *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED: TView.closed tvw m) *)
  (*   : *)
  (*     respecting_tview P tvw. *)
  (* Proof. *)
  (*   inv CLOSED. econs. *)
  (*   - i. eapply closed_view_respecting; eauto. *)
  (*   - eapply closed_view_respecting; eauto. *)
  (*   - eapply closed_view_respecting; eauto. *)
  (* Qed. *)

  (* Definition memory_to (m: Memory.t) (l: Loc.t) (t: Time.t): Prop := *)
  (*   exists from val released, *)
  (*     (<<GET: Memory.get l t m = Some (from, Message.full val released)>>) *)
  (* . *)

  (* Lemma memory_to_respecting P m loc to *)
  (*       (INMEMORY: respecting_memory P m) *)
  (*       (MEMORYTO: memory_to m loc to) *)
  (*   : *)
  (*     P loc to. *)
  (* Proof. *)
  (*   unfold memory_to in *. des. *)
  (*   eapply INMEMORY in GET. des. auto. *)
  (* Qed. *)

  (* Lemma map_timemap_join P f tm0 tm1 *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED0: respecting_map P tm0) *)
  (*       (CLOSED1: respecting_map P tm1) *)
  (*   : *)
  (*     timemap_map f (TimeMap.join tm0 tm1) = TimeMap.join (timemap_map f tm0) (timemap_map f tm1). *)
  (* Proof. *)
  (*   extensionality t. unfold timemap_map, TimeMap.join. *)
  (*   eapply map_time_join; eauto. *)
  (* Qed. *)

  (* Lemma map_viewjoin P f v0 v1 *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED0: respecting_view P v0) *)
  (*       (CLOSED1: respecting_view P v1) *)
  (*   : *)
  (*     view_map f (View.join v0 v1) = View.join (view_map f v0) (view_map f v1). *)
  (* Proof. *)
  (*   inv CLOSED0. inv CLOSED1. *)
  (*   unfold view_map, View.join. ss. f_equal. *)
  (*   - eapply map_timemap_join; eauto. *)
  (*   - eapply map_timemap_join; eauto. *)
  (* Qed. *)

  (* Lemma map_tviewjoin P f tv0 tv1 *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED0: respecting_tview P tv0) *)
  (*       (CLOSED1: respecting_tview P tv1) *)
  (*   : *)
  (*     tview_map f (TView.join tv0 tv1) = TView.join (tview_map f tv0) (tview_map f tv1). *)
  (* Proof. *)
  (*   inv CLOSED0. inv CLOSED1. *)
  (*   unfold tview_map, TView.join. ss. f_equal. *)
  (*   - extensionality l. eapply map_viewjoin; eauto. *)
  (*   - eapply map_viewjoin; eauto. *)
  (*   - eapply map_viewjoin; eauto. *)
  (* Qed. *)

  (* Lemma map_unwrap P f released *)
  (*       (PRSV: prsv P f) *)
  (*       (CLOSED0: respecting_opt_view P released) *)
  (*   : *)
  (*     view_map f (View.unwrap released) = *)
  (*     View.unwrap (option_map (view_map f) released). *)
  (* Proof. *)
  (*   unfold View.unwrap. des_ifs. eapply map_view_bot; eauto. *)
  (* Qed. *)

  (* Lemma map_read_tview P f m v loc to released ord *)
  (*       (PRSV: prsv P f) *)
  (*       (INMEMORY: respecting_memory P m) *)
  (*       (CLOSED0: TView.closed v m) *)
  (*       (CLOSED1: Memory.closed_opt_view released m) *)
  (*       (CLOSED2: memory_to m loc to) *)
  (*       (INHABITED: Memory.inhabited m) *)
  (*   : *)
  (*     tview_map f (TView.read_tview v loc to released ord) = *)
  (*     TView.read_tview (tview_map f v) loc (f loc to) (option_map (view_map f) released) ord. *)
  (* Proof. *)
  (*   dup CLOSED0. dup CLOSED1. dup CLOSED0. *)
  (*   eapply closed_tview_respecting in CLOSED0; eauto. *)
  (*   eapply closed_opt_view_respecting in CLOSED1; eauto. *)
  (*   eapply memory_to_respecting in CLOSED2; eauto. *)
  (*   unfold tview_map, TView.read_tview. ss. *)
  (*   repeat (erewrite <- map_unwrap; eauto). *)
  (*   repeat (erewrite map_viewjoin; eauto). *)
  (*   - erewrite map_singleton_ur_if; eauto. *)
  (*     des_ifs; f_equal; erewrite map_view_bot; eauto. *)
  (*   - inv CLOSED0. auto. *)
  (*   - eapply *)

  (*     unfold times_in_memory_to in *. des. *)
  (*     eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - eapply Memory.join_closed_view; eauto. *)
  (*     + inv CLOSED0; eauto. *)
  (*     + unfold times_in_memory_to in *. des. *)
  (*       eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - des_ifs. *)
  (*     + eapply Memory.unwrap_closed_opt_view; eauto. *)
  (*     + eapply Memory.closed_view_bot; eauto. *)
  (*   - inv CLOSED0. eauto. *)
  (*   - unfold times_in_memory_to in *. des. *)
  (*     eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - eapply Memory.join_closed_view; eauto. *)
  (*     + inv CLOSED0; eauto. *)
  (*     + unfold times_in_memory_to in *. des. *)
  (*       eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - des_ifs. *)
  (*     + eapply Memory.unwrap_closed_opt_view; eauto. *)
  (*     + eapply Memory.closed_view_bot; eauto. *)
  (* Qed. *)


  (* Definition times_in_memory (m: Memory.t) (l: Loc.t) (t: Time.t): Prop := *)
  (*   (<<OFFROM: exists to msg, *)
  (*       (<<GET: Memory.get l to m = Some (t, msg)>>)>>) \/ *)
  (*   (<<OFTO: exists from msg, *)
  (*       (<<GET: Memory.get l t m = Some (from, msg)>>)>>) *)
  (* . *)

  (* Definition times_in_memory_to (m: Memory.t) (l: Loc.t) (t: Time.t): Prop := *)
  (*   (<<OFTO: exists from val released, *)
  (*       (<<GET: Memory.get l t m = Some (from, Message.full val released)>>)>>) *)
  (* . *)

  (* Lemma times_in_memory_to_in_memory: *)
  (*   times_in_memory_to <3= times_in_memory. *)
  (* Proof. *)
  (*   i. unfold times_in_memory_to in *. des. right. eauto. *)
  (* Qed. *)
  (* Hint Resolve times_in_memory_to_in_memory. *)

  (* Lemma map_closed_timemap m f tm *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED: Memory.closed_timemap tm m) *)
  (*   : *)
  (*     forall loc, times_in_memory m loc (tm loc). *)
  (* Proof. *)
  (*   ii. right. specialize (CLOSED loc). unfold times_in_memory_to. des. eauto. *)
  (* Qed. *)

  (* Lemma map_timemap_join f m tm0 tm1 *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: Memory.closed_timemap tm0 m) *)
  (*       (CLOSED1: Memory.closed_timemap tm1 m) *)
  (*   : *)
  (*     timemap_map f (TimeMap.join tm0 tm1) = TimeMap.join (timemap_map f tm0) (timemap_map f tm1). *)
  (* Proof. *)
  (*   extensionality t. unfold timemap_map, TimeMap.join. *)
  (*   eapply map_time_join; eauto. *)
  (*   - eapply map_closed_timemap; eauto. *)
  (*   - eapply map_closed_timemap; eauto. *)
  (* Qed. *)

  (* Lemma map_viewjoin f m v0 v1 *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: Memory.closed_view v0 m) *)
  (*       (CLOSED1: Memory.closed_view v1 m) *)
  (*   : *)
  (*     view_map f (View.join v0 v1) = View.join (view_map f v0) (view_map f v1). *)
  (* Proof. *)
  (*   inv CLOSED0. inv CLOSED1. *)
  (*   unfold view_map, View.join. ss. f_equal. *)
  (*   - eapply map_timemap_join; eauto. *)
  (*   - eapply map_timemap_join; eauto. *)
  (* Qed. *)

  (* Lemma map_tviewjoin f m tv0 tv1 *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: TView.closed tv0 m) *)
  (*       (CLOSED1: TView.closed tv1 m) *)
  (*   : *)
  (*     tview_map f (TView.join tv0 tv1) = TView.join (tview_map f tv0) (tview_map f tv1). *)
  (* Proof. *)
  (*   inv CLOSED0. inv CLOSED1. *)
  (*   unfold tview_map, TView.join. ss. f_equal. *)
  (*   - extensionality l. eapply map_viewjoin; eauto. *)
  (*   - eapply map_viewjoin; eauto. *)
  (*   - eapply map_viewjoin; eauto. *)
  (* Qed. *)

  (* Lemma map_unwrap f m released *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: Memory.closed_opt_view released m) *)
  (*   : *)
  (*     view_map f (View.unwrap released) = *)
  (*     View.unwrap (option_map (view_map f) released). *)
  (* Proof. *)
  (*   unfold View.unwrap. des_ifs. eapply map_view_bot; eauto. *)
  (* Qed. *)

  (* Lemma map_read_tview f m v loc to released ord *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: TView.closed v m) *)
  (*       (CLOSED1: Memory.closed_opt_view released m) *)
  (*       (CLOSED2: times_in_memory_to m loc to) *)
  (*       (INHABITED: Memory.inhabited m) *)
  (*   : *)
  (*     tview_map f (TView.read_tview v loc to released ord) = *)
  (*     TView.read_tview (tview_map f v) loc (f loc to) (option_map (view_map f) released) ord. *)
  (* Proof. *)
  (*   unfold tview_map, TView.read_tview. ss. *)
  (*   repeat (erewrite <- map_unwrap; eauto). *)
  (*   repeat (erewrite map_viewjoin; eauto). *)
  (*   - erewrite map_singleton_ur_if; eauto. *)
  (*     des_ifs; f_equal; erewrite map_view_bot; eauto. *)
  (*   - inv CLOSED0. eauto. *)
  (*   - unfold times_in_memory_to in *. des. *)
  (*     eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - eapply Memory.join_closed_view; eauto. *)
  (*     + inv CLOSED0; eauto. *)
  (*     + unfold times_in_memory_to in *. des. *)
  (*       eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - des_ifs. *)
  (*     + eapply Memory.unwrap_closed_opt_view; eauto. *)
  (*     + eapply Memory.closed_view_bot; eauto. *)
  (*   - inv CLOSED0. eauto. *)
  (*   - unfold times_in_memory_to in *. des. *)
  (*     eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - eapply Memory.join_closed_view; eauto. *)
  (*     + inv CLOSED0; eauto. *)
  (*     + unfold times_in_memory_to in *. des. *)
  (*       eapply Memory.singleton_ur_if_closed_view; eauto. *)
  (*   - des_ifs. *)
  (*     + eapply Memory.unwrap_closed_opt_view; eauto. *)
  (*     + eapply Memory.closed_view_bot; eauto. *)
  (* Qed. *)

  (* Lemma map_step_read *)
  (*       f v v' prom_src prom_tgt prom_tgt' *)
  (*       mem_src mem_tgt loc to val released ord *)
  (*       (STEP: Local.read_step (Local.mk v prom_tgt) mem_tgt loc to val released ord *)
  (*                              (Local.mk v' prom_tgt')) *)
  (*       (INMEMORY0: map_preserving (times_in_memory mem_tgt) f) *)
  (*       (CLOSED0: Memory.closed mem_tgt) *)
  (*       (LCWF: Local.wf (Local.mk v Memory.bot) mem_tgt) *)
  (*       (MEM: memory_map f mem_src mem_tgt) *)
  (*       (INHABITED: Memory.inhabited mem_tgt) *)
  (*   : *)
  (*     (<<STEP: Local.read_step (Local.mk (tview_map f v) prom_src) mem_src loc *)
  (*                              (f loc to) val (option_map (view_map f) released) ord *)
  (*                              (Local.mk (tview_map f v') prom_src)>>). *)
  (* Proof. *)
  (*   inv STEP. ss. clarify. econs; eauto. *)
  (*   + inv MEM. exploit MAPPED; eauto. *)
  (*   + ss. inv READABLE. unfold view_map, option_map, timemap_map. des_ifs. *)
  (*     * econs; ss; eauto. *)
  (*       { eapply map_preserving_le_if; eauto. *)
  (*         - inv LCWF. ss. inv TVIEW_CLOSED. inv CUR. *)
  (*           eapply map_closed_timemap; eauto. *)
  (*         - right. eauto. } *)
  (*       { i. eapply map_preserving_le_if; eauto. *)
  (*         - inv LCWF. ss. inv TVIEW_CLOSED. inv CUR. *)
  (*           eapply map_closed_timemap; eauto. *)
  (*         - right. eauto. } *)
  (*     * econs; ss; eauto. *)
  (*       { eapply map_preserving_le_if; eauto. *)
  (*         - inv LCWF. ss. inv TVIEW_CLOSED. inv CUR. *)
  (*           eapply map_closed_timemap; eauto. *)
  (*         - right. eauto. } *)
  (*       { i. eapply map_preserving_le_if; eauto. *)
  (*         - inv LCWF. ss. inv TVIEW_CLOSED. inv CUR. *)
  (*           eapply map_closed_timemap; eauto. *)
  (*         - right. eauto. } *)
  (*   + ss. f_equal. erewrite map_read_tview; eauto. *)
  (*     * inv LCWF. ss. *)
  (*     * eapply CLOSED0 in GET. des. inv MSG_CLOSED. eauto. *)
  (*     * unfold times_in_memory_to. eauto. *)
  (* Qed. *)

  (* Lemma view_map_le f m tm0 tm1 *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: Memory.closed_timemap tm0 m) *)
  (*       (CLOSED1: Memory.closed_timemap tm1 m) *)
  (*       (LE: TimeMap.le tm0 tm1) *)
  (*   : *)
  (*     TimeMap.le (timemap_map f tm0) (timemap_map f tm1). *)
  (* Proof. *)
  (*   ii. unfold timemap_map. *)
  (*   eapply map_preserving_le_if; eauto. *)
  (*   - right. specialize (CLOSED0 loc). des. eauto. *)
  (*   - right. specialize (CLOSED1 loc). des. eauto. *)
  (* Qed. *)

  (* Lemma view_map_wf f m view *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: Memory.closed_view view m) *)
  (*       (WF : View.wf view) *)
  (*   : *)
  (*     View.wf (view_map f view). *)
  (* Proof. *)
  (*   unfold view_map. ss. econs. inv WF. *)
  (*   inv CLOSED0. eapply view_map_le in PLN_RLX; eauto. *)
  (* Qed. *)

  (* Lemma map_write_released f m v sc loc to releasedm ord *)
  (*       (INMEMORY0: map_preserving (times_in_memory m) f) *)
  (*       (INHABITED: Memory.inhabited m) *)
  (*       (CLOSED0: Memory.closed m) *)
  (*       (CLOSED1: Memory.closed_opt_view releasedm m) *)
  (*       (CLOSED2: times_in_memory_to m loc to) *)
  (*       (CLOSED3: TView.closed v m) *)
  (*       (CLOSED4: Memory.closed_timemap sc m) *)
  (*   : *)
  (*     option_map (view_map f) (TView.write_released v sc loc to releasedm ord) = *)
  (*     TView.write_released (tview_map f v) (timemap_map f sc) loc (f loc to) *)
  (*                          (option_map (view_map f) releasedm) ord. *)
  (* Proof. *)
  (*   dup CLOSED2. unfold times_in_memory_to in CLOSED2. des. *)
  (*   exploit TViewFacts.get_closed_released; eauto. *)
  (*   instantiate (1:=ord). i. *)
  (*   unfold TView.write_released in *. des_ifs. unfold option_map. *)
  (*   erewrite map_viewjoin; eauto. *)
  (*   - f_equal. erewrite map_unwrap; eauto. f_equal. *)
  (*     setoid_rewrite LocFun.add_spec_eq. *)
  (*     des_ifs. *)
  (*     + erewrite map_viewjoin; eauto. *)
  (*       * erewrite map_singleton_ur; eauto. *)
  (*       * inv CLOSED3. eauto. *)
  (*       * unfold times_in_memory_to in *. des. *)
  (*         eapply Memory.singleton_ur_closed_view; eauto. *)
  (*     + erewrite map_viewjoin; eauto. *)
  (*       * erewrite map_singleton_ur; eauto. *)
  (*       * inv CLOSED3. eauto. *)
  (*       * unfold times_in_memory_to in *. des. *)
  (*         eapply Memory.singleton_ur_closed_view; eauto. *)
  (*   - eapply Memory.unwrap_closed_opt_view; eauto. *)
  (*   - exploit TViewFacts.get_closed_tview; eauto. i. *)
  (*     inv x1. eauto. *)
  (* Qed. *)

  (* Lemma map_write_tview f m v sc ord loc to *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (INHABITED: Memory.inhabited m) *)
  (*       (CLOSED0: TView.closed v m) *)
  (*       (CLOSED1: Memory.closed_timemap sc m) *)
  (*       (CLOSED2: times_in_memory_to m loc to) *)
  (*   : *)
  (*     tview_map f (TView.write_tview v sc loc to ord) = *)
  (*     TView.write_tview (tview_map f v) (timemap_map f sc) loc (f loc to) ord. *)
  (* Proof. *)
  (*   unfold TView.write_tview. ss. unfold tview_map at 1. ss. f_equal. *)
  (*   - extensionality l. des_ifs. *)
  (*     + setoid_rewrite LocFun.add_spec. des_ifs. *)
  (*       erewrite map_viewjoin; eauto. *)
  (*       * f_equal. erewrite map_singleton_ur; eauto. *)
  (*       * inv CLOSED0. eauto. *)
  (*       * unfold times_in_memory_to in *. des. *)
  (*         eapply Memory.singleton_ur_closed_view; eauto. *)
  (*     + setoid_rewrite LocFun.add_spec. des_ifs. *)
  (*       erewrite map_viewjoin; eauto. *)
  (*       * f_equal. erewrite map_singleton_ur; eauto. *)
  (*       * inv CLOSED0. eauto. *)
  (*       * unfold times_in_memory_to in *. des. *)
  (*         eapply Memory.singleton_ur_closed_view; eauto. *)
  (*   - erewrite map_viewjoin; eauto. *)
  (*     + f_equal. erewrite map_singleton_ur; eauto. *)
  (*     + inv CLOSED0. eauto. *)
  (*     + unfold times_in_memory_to in *. des. *)
  (*       eapply Memory.singleton_ur_closed_view; eauto. *)
  (*   - erewrite map_viewjoin; eauto. *)
  (*     + f_equal. erewrite map_singleton_ur; eauto. *)
  (*     + inv CLOSED0. eauto. *)
  (*     + unfold times_in_memory_to in *. des. *)
  (*       eapply Memory.singleton_ur_closed_view; eauto. *)
  (* Qed. *)

  (* Lemma map_step_write f v v' prom' *)
  (*       loc from to val releasedm released ord sc sc' mem_src *)
  (*       mem_tgt mem_tgt' kind *)
  (*       (WRITE: Local.write_step *)
  (*                 (Local.mk v Memory.bot) sc mem_tgt *)
  (*                 loc from to val releasedm released ord *)
  (*                 (Local.mk v' prom') sc' mem_tgt' kind) *)
  (*       (INMEMORY0: map_preserving (times_in_memory mem_tgt) f) *)
  (*       (INMEMORY1: map_preserving (times_in_memory mem_tgt') f) *)
  (*       (CLOSED0: Memory.closed mem_tgt) *)
  (*       (CLOSED1: View.opt_wf releasedm) *)
  (*       (CLOSED2: Memory.closed_opt_view releasedm mem_tgt) *)
  (*       (CLOSED3: Memory.closed_timemap sc mem_tgt) *)
  (*       (LCWF: Local.wf (Local.mk v Memory.bot) mem_tgt) *)
  (*       (MEM: memory_map f mem_src mem_tgt) *)
  (*       (INHABITED: Memory.inhabited mem_tgt) *)
  (*   : *)
  (*     exists mem_src', *)
  (*       (<<WRITE: Local.write_step *)
  (*                   (Local.mk (tview_map f v) Memory.bot) *)
  (*                   (timemap_map f sc) *)
  (*                   mem_src loc (f loc from) (f loc to) val *)
  (*                   (option_map (view_map f) releasedm) *)
  (*                   (option_map (view_map f) released) ord *)
  (*                   (Local.mk (tview_map f v') Memory.bot) *)
  (*                   (timemap_map f sc') mem_src' Memory.op_kind_add>>) /\ *)
  (*       (<<MEM: memory_map f mem_src' mem_tgt'>>). *)
  (* Proof. *)
  (*   inv LCWF. exploit write_msg_wf; eauto. i. des. *)
  (*   dup WRITE. inv WRITE. ss. clarify. exploit memory_write_bot_add; eauto. i. clarify. *)
  (*   assert (CLOSEDV1: Memory.closed_opt_view (TView.write_released v sc loc to releasedm ord) mem_tgt'). *)
  (*   { inv WRITE1. inv PROMISE. ss. *)
  (*     eapply TViewFacts.write_future; eauto. } *)
  (*   exploit Local.write_step_future; eauto. i. ss. des. *)
  (*   inv WRITE1. inv PROMISE. dup MEM0. eapply Memory.add_get0 in MEM1. des. *)
  (*   exploit write_succeed. *)
  (*   { instantiate (1:=f loc to). instantiate (1:=f loc from). *)
  (*     instantiate (1:=mem_src). instantiate (1:=loc). *)
  (*     ii. inv COVER. *)
  (*     inv MEM. ss. exploit ONLY; eauto. i. des. clarify. *)
  (*     destruct msg0. dup GET2. eapply MAPPED in GET2. clarify. *)
  (*     dup GET3. eapply Memory.add_get1 in GET3; eauto. *)
  (*     destruct H. destruct ITV. ss. *)
  (*     assert (LT0: Time.lt (f loc t0) (f loc to)). *)
  (*     { eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto. } *)
  (*     assert (LT1: Time.lt (f loc from) (f loc to1)). *)
  (*     { eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto. } *)
  (*     assert (LT2: Time.lt (f loc from) (f loc to)). *)
  (*     { eapply DenseOrder.DenseOrderFacts.lt_le_lt; try apply FROM; eauto. } *)
  (*     assert (LT3: Time.lt (f loc t0) (f loc to1)). *)
  (*     { eapply DenseOrder.DenseOrderFacts.lt_le_lt; try apply FROM0; eauto. } *)
  (*     erewrite <- map_preserving_lt_iff in LT0; eauto; cycle 1. *)
  (*     { left. eauto. } *)
  (*     { right. eauto. } *)
  (*     erewrite <- map_preserving_lt_iff in LT1; eauto; cycle 1. *)
  (*     { left. eauto. } *)
  (*     { right. eauto. } *)
  (*     erewrite <- map_preserving_lt_iff in LT2; eauto; cycle 1. *)
  (*     { left. eauto. } *)
  (*     { right. eauto. } *)
  (*     erewrite <- map_preserving_lt_iff in LT3; eauto; cycle 1. *)
  (*     { left. eauto. } *)
  (*     { right. eauto. } *)
  (*     exploit Memory.get_disjoint. *)
  (*     - eapply GET3. *)
  (*     - eapply GET0. *)
  (*     - i. des; clarify. *)
  (*       exploit Time.middle_spec. *)
  (*       { instantiate (1:=Time.meet to to1). instantiate (1:=Time.join from t0). *)
  (*         unfold Time.join, Time.meet. des_ifs. } i. des. *)
  (*       eapply x0. *)
  (*       + instantiate (1:=Time.middle (Time.join from t0) (Time.meet to to1)). econs; ss. *)
  (*         * eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto. eapply Time.join_r. *)
  (*         * left. eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto. eapply Time.meet_r. *)
  (*       + econs; ss. *)
  (*         * eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto. eapply Time.join_l. *)
  (*         * left. eapply DenseOrder.DenseOrderFacts.lt_le_lt; eauto. eapply Time.meet_l. } *)
  (*   { instantiate (1:=option_map *)
  (*                       (view_map f) *)
  (*                       (TView.write_released v sc loc to releasedm ord)). *)
  (*     erewrite map_preserving_le_iff in REL_TS; try apply INMEMORY1; eauto. *)
  (*     - instantiate (1:=loc) in REL_TS. *)
  (*       setoid_rewrite <- map_unwrap; try apply INMEMORY1; eauto. *)
  (*     - right. eapply Memory.unwrap_closed_opt_view in CLOSEDV1; eauto. *)
  (*       + inv CLOSEDV1. specialize (RLX loc). des. eauto. *)
  (*       + eapply inhabited_future; eauto. *)
  (*     - right. eauto. } *)
  (*   { erewrite <- map_preserving_lt_iff; eauto. *)
  (*     - left. eauto. *)
  (*     - right. eauto. } *)
  (*   { econs. inv REL_WF; ss. econs. eapply view_map_wf; try apply INMEMORY1; eauto. *)
  (*     inv CLOSEDV1; congruence. } *)
  (*   i. des. exists mem2. esplits; eauto. *)
  (*   - econs; ss; eauto. *)
  (*     + erewrite map_write_released; try apply INMEMORY1; eauto. *)
  (*       * eapply inhabited_future; eauto. *)
  (*       * eapply Memory.future_closed_opt_view; eauto. *)
  (*       * unfold times_in_memory_to. eauto. *)
  (*       * eapply TView.future_closed; eauto. *)
  (*     + inv WRITABLE. econs. unfold view_map, timemap_map. ss. *)
  (*       erewrite <- map_preserving_lt_iff; eauto. *)
  (*       * eapply TView.future_closed in TVIEW_CLOSED; eauto. *)
  (*         inv TVIEW_CLOSED. inv CUR. specialize (RLX loc). des. *)
  (*         unfold times_in_memory. eauto. *)
  (*       * unfold times_in_memory. eauto. *)
  (*     + f_equal. eapply map_write_tview; eauto. *)
  (*       * eapply inhabited_future; eauto. *)
  (*       * eapply TView.future_closed; eauto. *)
  (*       * unfold times_in_memory_to. eauto. *)
  (*   - inv WRITE. inv PROMISE. econs. *)
  (*     + i. erewrite Memory.add_o in GET1; eauto. *)
  (*       erewrite Memory.add_o; eauto. des_ifs; ss. *)
  (*       * des; clarify. *)
  (*       * des; clarify. exfalso. *)
  (*         erewrite <- map_preserving_eq_iff in a0; eauto. *)
  (*         { right. eapply Memory.add_get1 in GET1; eauto. } *)
  (*         { right. eauto. } *)
  (*       * des; clarify. *)
  (*       * inv MEM. eauto. *)
  (*     + i. erewrite Memory.add_o in GET1; eauto. des_ifs. *)
  (*       * ss; des; clarify. esplits; eauto. *)
  (*       * inv MEM. exploit ONLY; eauto. i. *)
  (*         destruct x as [to0 [msg [FROM GET2]]]. *)
  (*         exists to0, msg. esplits; eauto. *)
  (*         erewrite Memory.add_o; eauto. des_ifs. *)
  (*         ss. des; clarify. *)
  (* Qed. *)

  (* Lemma map_read_fence_tview f v ord *)
  (*   : *)
  (*     tview_map f (TView.read_fence_tview v ord) = *)
  (*     TView.read_fence_tview (tview_map f v) ord. *)
  (* Proof. *)
  (*   unfold TView.read_fence_tview, tview_map. ss. f_equal. *)
  (*   des_ifs. *)
  (* Qed. *)

  (* Lemma map_write_fence_sc f m v sc ord *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: TView.closed v m) *)
  (*       (CLOSED1: Memory.closed_timemap sc m) *)
  (*   : *)
  (*     timemap_map f (TView.write_fence_sc v sc ord) = *)
  (*     TView.write_fence_sc (tview_map f v) (timemap_map f sc) ord. *)
  (* Proof. *)
  (*   unfold TView.write_fence_sc. ss. *)
  (*   extensionality loc. des_ifs. *)
  (*   erewrite map_timemap_join; eauto. *)
  (*   inv CLOSED0. inv CUR. eauto. *)
  (* Qed. *)

  (* Lemma map_read_fence f v ord *)
  (*   : *)
  (*     tview_map f (TView.read_fence_tview v ord) = *)
  (*     TView.read_fence_tview (tview_map f v) ord. *)
  (* Proof. *)
  (*   unfold TView.read_fence_tview, tview_map. ss. f_equal. des_ifs. *)
  (* Qed. *)

  (* Lemma write_fence_sc_closed v sc ord m *)
  (*       (CLOSED0: TView.closed v m) *)
  (*       (CLOSED1: Memory.closed_timemap sc m) *)
  (*   : *)
  (*     Memory.closed_timemap (TView.write_fence_sc v sc ord) m. *)
  (* Proof. *)
  (*   unfold TView.write_fence_sc. des_ifs. *)
  (*   eapply Memory.join_closed_timemap; eauto. *)
  (*   inv CLOSED0. inv CUR. auto. *)
  (* Qed. *)

  (* Lemma read_fence_closed tview ord m *)
  (*       (CLOSED0: TView.closed tview m) *)
  (*   : *)
  (*     TView.closed (TView.read_fence_tview tview ord) m. *)
  (* Proof. *)
  (*   unfold TView.read_fence_tview. inv CLOSED0. des_ifs. *)
  (* Qed. *)

  (* Lemma map_write_fence_tview f m v sc ord *)
  (*       (INMEMORY: map_preserving (times_in_memory m) f) *)
  (*       (CLOSED0: TView.closed v m) *)
  (*       (CLOSED1: Memory.closed_timemap sc m) *)
  (*       (INHABITED: Memory.inhabited m) *)
  (*   : *)
  (*     tview_map f (TView.write_fence_tview v sc ord) = *)
  (*     TView.write_fence_tview (tview_map f v) (timemap_map f sc) ord. *)
  (* Proof. *)
  (*   unfold TView.write_fence_tview. ss. *)
  (*   erewrite <- map_write_fence_sc; eauto. *)
  (*   unfold tview_map at 1. ss. f_equal. *)
  (*   - extensionality loc. des_ifs. *)
  (*   - des_ifs. *)
  (*   - erewrite map_viewjoin; eauto. *)
  (*     + des_ifs. erewrite map_view_bot; eauto. *)
  (*     + inv CLOSED0. inv ACQ. auto. *)
  (*     + des_ifs. *)
  (*       * econs; ss; eapply write_fence_sc_closed; eauto. *)
  (*       * eapply Memory.closed_view_bot; eauto. *)
  (* Qed. *)

  (* Lemma times_in_memory_le mem0 mem1 *)
  (*       (MLE: Memory.le mem0 mem1) *)
  (*   : *)
  (*     times_in_memory mem0 <2= times_in_memory mem1. *)
  (* Proof. *)
  (*   ii. inv PR. *)
  (*   - des. left. esplits; eauto. *)
  (*   - des. right. esplits; eauto. *)
  (* Qed. *)

  (* Lemma map_preserving_memory_le f mem0 mem1 *)
  (*       (PRSV: map_preserving (times_in_memory mem1) f) *)
  (*       (MLE: Memory.le mem0 mem1) *)
  (*   : *)
  (*     map_preserving (times_in_memory mem0) f. *)
  (* Proof. *)
  (*   inv PRSV. econs; eauto. *)
  (*   i. eapply PRSVLT; eauto. *)
  (*   - eapply times_in_memory_le; eauto. *)
  (*   - eapply times_in_memory_le; eauto. *)
  (* Qed. *)

  (* Lemma map_step *)
  (*       f lang th_src th_tgt th_tgt' st st' v v' prom' sc sc' *)
  (*       mem_src mem_tgt mem_tgt' e_tgt *)
  (*       (STEP: (@pred_step no_promise lang) e_tgt th_tgt th_tgt') *)
  (*       (TH_SRC: th_src = Thread.mk lang st (Local.mk (tview_map f v) Memory.bot) *)
  (*                                   (timemap_map f sc) mem_src) *)
  (*       (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt) *)
  (*       (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt') *)
  (*       (INMEMORY1: map_preserving (times_in_memory mem_tgt') f) *)
  (*       (CLOSEDMAP0: Memory.closed_timemap sc mem_tgt) *)
  (*       (CLOSED0: Memory.closed mem_tgt) *)
  (*       (LCWF: Local.wf (Local.mk v Memory.bot) mem_tgt) *)
  (*       (INHABITED: Memory.inhabited mem_tgt) *)
  (*       (MEM: memory_map f mem_src mem_tgt) *)
  (*   : *)
  (*     exists mem_src', *)
  (*       (<<STEP: (@pred_step no_promise lang) *)
  (*                  (tevent_map f e_tgt) th_src *)
  (*                  (Thread.mk lang st' (Local.mk (tview_map f v') Memory.bot) (timemap_map f sc') mem_src')>>) /\ *)
  (*       (<<MEM: memory_map f mem_src' mem_tgt'>>). *)
  (* Proof. *)
  (*   assert (INMEMORY0: map_preserving (times_in_memory mem_tgt) f). *)
  (*   { eapply map_preserving_memory_le; eauto. clarify. *)
  (*     hexploit pf_step_memory_le; eauto. } *)
  (*   clarify. inv STEP. inv STEP0. inv STEP; inv STEP0; ss. inv LOCAL; ss. *)
  (*   - exists mem_src. esplits; ss; eauto. *)
  (*     econs; eauto. econs; eauto. econs 2; eauto. econs; eauto. *)
  (*   - exploit map_step_read; eauto. i. des. *)
  (*     exists mem_src. esplits; eauto. econs; eauto. econs; eauto. *)
  (*     econs 2; eauto. econs; eauto. *)
  (*   - exploit map_step_write; eauto. i. des. ss. *)
  (*     exists mem_src'. esplits; eauto. econs; eauto. econs; eauto. *)
  (*     econs 2; eauto. econs; eauto. *)
  (*   - exploit Local.read_step_future; eauto. i. des. *)
  (*     destruct lc2. exploit map_step_read; eauto. i. des. *)
  (*     inv LOCAL1. ss. clarify. *)
  (*     exploit map_step_write; eauto. i. des. *)
  (*     exists mem_src'. esplits; eauto. econs; eauto. econs; eauto. *)
  (*     econs 2; eauto. econs; eauto. *)
  (*   - exists mem_src. esplits; eauto. econs; eauto. econs; eauto. *)
  (*     econs 2; eauto. econs; eauto. econs; eauto. *)
  (*     inv LOCAL0. ss. clarify. *)
  (*     erewrite map_write_fence_tview; eauto; cycle 1. *)
  (*     { eapply read_fence_closed; eauto. inv LCWF. eauto. } *)
  (*     repeat erewrite map_read_fence. econs; ss; eauto. *)
  (*     erewrite map_write_fence_sc; eauto. *)
  (*     + erewrite map_read_fence. auto. *)
  (*     + eapply read_fence_closed; eauto. inv LCWF. eauto. *)
  (*   - exists mem_src. esplits; eauto. econs; eauto. econs; eauto. *)
  (*     econs 2; eauto. econs; eauto. econs; eauto. *)
  (*     inv LOCAL0. ss. clarify. *)
  (*     erewrite map_write_fence_tview; eauto; cycle 1. *)
  (*     { eapply read_fence_closed; eauto. inv LCWF. eauto. } *)
  (*     repeat erewrite map_read_fence. econs; ss; eauto. *)
  (*     erewrite map_write_fence_sc; eauto. *)
  (*     eapply read_fence_closed; eauto. inv LCWF. eauto. *)
  (*   - exists mem_src. esplits; eauto. econs; eauto. econs; eauto. *)
  (*     econs 2; eauto. econs; eauto. econs; eauto. econs; eauto. *)
  (*     ii. ss. erewrite Memory.bot_get in *. clarify. *)
  (* Qed. *)

End MAPPED.





Section SHORTERMEMORY.

  Inductive shorter_memory (mem_src mem_tgt: Memory.t): Prop :=
  | shorter_memory_intro
      (COMPLETE: forall loc to from_tgt val released
                        (GET: Memory.get loc to mem_tgt = Some (from_tgt, Message.full val released)),
          exists from_src,
            (<<GET: Memory.get loc to mem_src = Some (from_src, Message.full val released)>>))
      (COVER: forall l t (COV: covered l t mem_src), covered l t mem_tgt)
  .
  Global Program Instance shorter_memory_PreOrder: PreOrder shorter_memory.
  Next Obligation. ii. econs; eauto. Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; eauto.
    ii. exploit COMPLETE0; eauto. i. des.
    exploit COMPLETE; eauto.
  Qed.

  Lemma shorter_memory_promise prom mem_src mem_tgt loc from1 to1 val released mem_tgt' from'
        (SHORTER: shorter_memory mem_src mem_tgt)
        (ADD: Memory.write Memory.bot mem_tgt loc from1 to1 val released prom mem_tgt' Memory.op_kind_add)
        (TO: Time.le from1 from')
        (FROM: Time.lt from' to1)
    :
      exists mem_src',
        (<<ADD: Memory.write Memory.bot mem_src loc from' to1 val released prom mem_src' Memory.op_kind_add>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv ADD. inv PROMISE.
    exploit MemoryFacts.MemoryFacts.add_remove_eq; try apply REMOVE; eauto. i. clarify.
    exploit write_succeed; eauto.
    - instantiate (1:=mem_src). instantiate (1:=loc).
      ii. eapply COVER in COVER0. inv COVER0.
      dup MEM. eapply Memory.add_get0 in MEM. des.
      dup GET. eapply Memory.add_get1 in GET; eauto.
      exploit Memory.get_disjoint.
      + eapply GET.
      + eapply GET1.
      + i. des; clarify.
        eapply x0; eauto. inv H. econs; ss; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
    - inv MEM. inv ADD. inv MSG_WF. inv TS. eauto.
    - inv MEM. inv ADD. eauto.
    - i. des. inv WRITE. inv PROMISE. esplits; eauto. econs.
      + i. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
      + i. inv COV. erewrite Memory.add_o in GET; eauto. des_ifs.
        * ss; des; clarify. eapply Memory.add_get0 in MEM. des.
          econs; eauto. inv ITV. econs; eauto.
          ss. eapply TimeFacts.le_lt_lt; eauto.
        * exploit COVER.
          { econs; eauto. }
          intros COV. inv COV. eapply Memory.add_get1 in GET0; eauto.
          econs; eauto.
  Qed.


  Lemma shorter_memory_write prom mem_src mem_tgt loc from1 to1 val released mem_tgt' from'
        (SHORTER: shorter_memory mem_src mem_tgt)
        (ADD: Memory.write Memory.bot mem_tgt loc from1 to1 val released prom mem_tgt' Memory.op_kind_add)
        (TO: Time.le from1 from')
        (FROM: Time.lt from' to1)
    :
      exists mem_src',
        (<<ADD: Memory.write Memory.bot mem_src loc from' to1 val released prom mem_src' Memory.op_kind_add>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv ADD. inv PROMISE.
    exploit MemoryFacts.MemoryFacts.add_remove_eq; try apply REMOVE; eauto. i. clarify.
    exploit write_succeed; eauto.
    - instantiate (1:=mem_src). instantiate (1:=loc).
      ii. eapply COVER in COVER0. inv COVER0.
      dup MEM. eapply Memory.add_get0 in MEM. des.
      dup GET. eapply Memory.add_get1 in GET; eauto.
      exploit Memory.get_disjoint.
      + eapply GET.
      + eapply GET1.
      + i. des; clarify.
        eapply x0; eauto. inv H. econs; ss; eauto.
        eapply TimeFacts.le_lt_lt; eauto.
    - inv MEM. inv ADD. inv MSG_WF. inv TS. eauto.
    - inv MEM. inv ADD. eauto.
    - i. des. inv WRITE. inv PROMISE. esplits; eauto. econs.
      + i. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
      + i. inv COV. erewrite Memory.add_o in GET; eauto. des_ifs.
        * ss; des; clarify. eapply Memory.add_get0 in MEM. des.
          econs; eauto. inv ITV. econs; eauto.
          ss. eapply TimeFacts.le_lt_lt; eauto.
        * exploit COVER.
          { econs; eauto. }
          intros COV. inv COV. eapply Memory.add_get1 in GET0; eauto.
          econs; eauto.
  Qed.

  Lemma shorter_memory_step
        P lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
        mem_tgt mem_tgt' mem_src e
        (PRED: P <1= no_promise)
        (STEP: (@pred_step P lang) e th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (SHORTER: shorter_memory mem_src mem_tgt)
    :
      exists mem_src',
        (<<STEP: (@pred_step P lang)
                   e th_src
                   (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv STEP.
    dup SAT. eapply PRED in SAT. inv STEP0. des. inv STEP.
    - inv STEP0. ss.
    - inv STEP0. inv LOCAL.
      + exists mem_src; eauto. econs; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. exploit COMPLETE; eauto. i. des.
        exists mem_src; eauto. econs; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + exploit write_msg_wf; eauto. i. des.
        inv LOCAL0. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        dup WRITE. exploit shorter_memory_write; eauto.
        { refl. }
        i. des. esplits; eauto. econs; eauto. econs; eauto.
        econs 2; eauto. econs; eauto.
      + inv LOCAL1. ss. exploit write_msg_wf; eauto. i. des.
        exploit COMPLETE; eauto. i. des.
        inv LOCAL2. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        dup WRITE. exploit shorter_memory_write; eauto.
        { refl. }
        i. des. esplits; eauto. econs; eauto. econs; eauto.
        econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
      + inv LOCAL0. ss. clarify. esplits; eauto. econs; eauto.
        econs; eauto. econs 2; eauto. econs; eauto.
  Qed.

  (* Lemma shorter_memory_step2 *)
  (*       P lang th_src th_tgt th_tgt' st st' v v' prom prom' sc sc' *)
  (*       mem_tgt mem_tgt' mem_src e *)
  (*       (MLETGT: Memory.le prom mem_tgt) *)
  (*       (MLESRC: Memory.le prom mem_src) *)
  (*       (STEP: (@pred_step P lang) e th_tgt th_tgt') *)
  (*       (TH_SRC: th_src = Thread.mk lang st (Local.mk v prom) sc mem_src) *)
  (*       (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v prom) sc mem_tgt) *)
  (*       (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt') *)
  (*       (SHORTER: shorter_memory mem_src mem_tgt) *)
  (*   : *)
  (*     exists mem_src', *)
  (*       (<<STEP: (@pred_step (P /1\ no_promise) lang) *)
  (*                  e th_src *)
  (*                  (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\ *)
  (*       (<<SHORTER: shorter_memory mem_src' mem_tgt'>>). *)
  (* Proof. *)
  (* Admitted. *)


End SHORTERMEMORY.


Section NOTATTATCHED.

  Definition not_attatched (L: Loc.t -> Time.t -> Prop) (m: Memory.t) :=
    forall loc to (SAT: L loc to),
      (<<GET: exists msg, <<MSG: Memory.get loc to m = Some msg>> >>) /\
      (<<NOATTATCH: exists to',
          (<<TLE: Time.lt to to'>>) /\
          (<<EMPTY: forall t (ITV: Interval.mem (to, to') t), ~ covered loc t m>>)>>).

  Lemma not_attatched_sum L0 L1 mem
        (NOATTATCH0: not_attatched L0 mem)
        (NOATTATCH1: not_attatched L1 mem)
    :
      not_attatched (L0 \2/ L1) mem.
  Proof.
    ii. des; eauto.
  Qed.

  Lemma not_attatched_mon L0 L1 mem
        (NOATTATCH0: not_attatched L0 mem)
        (LE: L1 <2= L0)
    :
      not_attatched L1 mem.
  Proof.
    ii. eauto.
  Qed.

  Lemma attached_preserve_add updates mem0 loc from to msg mem1
        (ADD: Memory.add mem0 loc from to msg mem1)
        (NOATTATCHED: not_attatched updates mem1)
        (PROMISED: updates <2= concrete_promised mem0)
    :
      not_attatched updates mem0.
  Proof.
    ii. exploit NOATTATCHED; eauto. i. des. split.
    - dup MSG. erewrite Memory.add_o in MSG; eauto. des_ifs.
      + ss. des. clarify. exfalso.
        eapply PROMISED in SAT. inv SAT.
        eapply Memory.add_get0 in ADD. des. clarify.
      + esplits; eauto.
    - esplits; eauto. ii. eapply EMPTY; eauto.
      eapply add_covered; eauto.
  Qed.

  Lemma attatched_preserve P updates lang (th0 th1: Thread.t lang) e
        (PRED: P <1= no_promise)
        (STEP: (@pred_step P lang) e th0 th1)
        (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
        (NOATTATCHED: not_attatched updates th1.(Thread.memory))
        (PROMISED: updates <2= concrete_promised th0.(Thread.memory))
    :
      not_attatched updates th0.(Thread.memory).
  Proof.
    inv STEP. inv STEP0. eapply PRED in SAT. inv STEP.
    - inv STEP0; des; clarify.
    - inv STEP0. ss. inv LOCAL; ss.
      + inv LOCAL0. destruct lc1. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE.
        eapply attached_preserve_add; eauto.
      + inv LOCAL1. inv LOCAL2. ss. destruct lc1. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        inv WRITE. inv PROMISE.
        eapply attached_preserve_add; eauto.
  Qed.

  Lemma update_not_attatched P lang (th0 th1: Thread.t lang)
        loc from to valr valw releasedr releasedw ordr ordw
        (STEP: (@pred_step P lang) (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw) th0 th1)
        (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
    :
      not_attatched (fun l t => l = loc /\ t = from) th0.(Thread.memory).
  Proof.
    inv STEP. inv STEP0. inv STEP; ss.
    - inv STEP0; des; clarify.
    - inv STEP0. ss. inv LOCAL; ss. destruct lc1, lc3, lc2.
      exploit write_msg_wf; eauto. i. des. ss. clarify.
      inv LOCAL1. inv LOCAL2. ss. clarify.
      exploit memory_write_bot_add; eauto. i. clarify.
      ii. des. clarify. esplits; eauto.
      ii. inv WRITE. inv PROMISE. eapply memory_add_cover_disjoint in MEM; eauto.
  Qed.

  Lemma attatched_preserve_rtc P updates lang (th0 th1: Thread.t lang)
        (PRED: P <1= no_promise)
        (STEP: rtc (tau (@pred_step P lang)) th0 th1)
        (BOT: th0.(Thread.local).(Local.promises) = Memory.bot)
        (NOATTATCHED: not_attatched updates th1.(Thread.memory))
        (PROMISED: updates <2= concrete_promised th0.(Thread.memory))
    :
      not_attatched updates th0.(Thread.memory).
  Proof.
    revert BOT PROMISED. induction STEP; auto.
    i. hexploit IHSTEP; eauto.
    - inv H. eapply promise_bot_no_promise; eauto.
    - i. inv H. inv TSTEP. inv STEP0. eapply concrete_promised_increase; eauto.
    - i. inv H. eapply attatched_preserve; eauto.
  Qed.

  Lemma not_attatch_write L prom mem_src loc from1 to1 val released mem_src'
        (ADD: Memory.write Memory.bot mem_src loc from1 to1 val released prom mem_src' Memory.op_kind_add)
        (NOATTATCH: not_attatched L mem_src)
        (FROM: ~ L loc from1)
    :
      (<<NOATTATCH: not_attatched L mem_src'>>).
  Proof.
    inv ADD. inv PROMISE. ii.
    exploit NOATTATCH; eauto. i. des. destruct msg.
    destruct (Loc.eq_dec loc loc0); clarify.
    - esplit; eauto.
      + eexists. eapply Memory.add_get1; eauto.
      + exists (if (Time.le_lt_dec to from1)
                then (Time.meet to' from1)
                else to'). esplits; eauto.
        * unfold Time.meet. des_ifs.
          destruct l; eauto. destruct H. clarify.
        * ii. erewrite add_covered in H; eauto. des.
          { eapply EMPTY; eauto. unfold Time.meet in *. des_ifs.
            inv ITV. econs; ss; eauto.
            left. eapply TimeFacts.le_lt_lt; eauto. }
          { clarify. unfold Time.meet in *.
            dup ITV. dup H0. inv ITV. inv H0. ss. des_ifs.
            - clear - FROM1 TO l0.
              eapply DenseOrder.DenseOrder.lt_strorder.
              instantiate (1:=from1).
              eapply TimeFacts.lt_le_lt; eauto.
            - eapply DenseOrder.DenseOrder.lt_strorder.
              instantiate (1:=from1).
              eapply TimeFacts.lt_le_lt; eauto.
            - dup MEM. eapply Memory.add_get0 in MEM. des.
              exploit Memory.get_disjoint.
              { eapply Memory.add_get1; try apply MSG; eauto. }
              { eapply GET0. }
              i. des; clarify. eapply x0.
              { instantiate (1:=to).
                exploit Memory.get_ts; eauto. i. des; clarify.
                - exfalso. eapply DenseOrder.DenseOrder.lt_strorder.
                  instantiate (1:=from1).
                  eapply TimeFacts.lt_le_lt; try apply l; eauto.
                  eapply Time.bot_spec.
                - econs; ss; eauto. refl. }
              { econs; ss; eauto. left.
                eapply TimeFacts.lt_le_lt; eauto. }
          }
    - esplits; eauto.
      + eapply Memory.add_get1; eauto.
      + ii. erewrite add_covered in H; eauto. des; clarify.
        eapply EMPTY; eauto.
  Qed.

  Inductive shorter_event: ThreadEvent.t -> ThreadEvent.t -> Prop :=
  | shorter_event_read
      loc to val released ordr
    :
      shorter_event
        (ThreadEvent.read loc to val released ordr)
        (ThreadEvent.read loc to val released ordr)
  | shorter_event_write
      loc from ffrom to val released ordw
      (FROM: Time.le from ffrom)
    :
      shorter_event
        (ThreadEvent.write loc ffrom to val released ordw)
        (ThreadEvent.write loc from to val released ordw)
  | shorter_event_update
      loc from to valr valw releasedr releasedw ordr ordw
    :
      shorter_event
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
        (ThreadEvent.update loc from to valr valw releasedr releasedw ordr ordw)
  | shorter_event_fence
      or ow
    :
      shorter_event
        (ThreadEvent.fence or ow)
        (ThreadEvent.fence or ow)
  | shorter_event_syscall
      e
    :
      shorter_event
        (ThreadEvent.syscall e)
        (ThreadEvent.syscall e)
  | shorter_event_silent
    :
      shorter_event
        (ThreadEvent.silent)
        (ThreadEvent.silent)
  | shorter_event_failure
    :
      shorter_event
        (ThreadEvent.failure)
        (ThreadEvent.failure)
  .

  Lemma shorter_event_shift L
        e_src e_tgt
        (SAT: (write_not_in L /1\ no_promise) e_tgt)
        (EVT: shorter_event e_src e_tgt)
    :
      (write_not_in L /1\ no_promise) e_src.
  Proof.
    ss. des. inv EVT; ss. split; auto. i.
    eapply SAT. inv IN. econs; ss.
    eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma no_update_on_step
        P L0 L1 lang th_src th_tgt th_tgt' st st' v v' prom' sc sc'
        mem_tgt mem_tgt' mem_src e_tgt
        (PRED: P <1= (write_not_in L0 /1\ no_update_on L1 /1\ no_promise))
        (STEP: (@pred_step P lang) e_tgt th_tgt th_tgt')
        (TH_SRC: th_src = Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v Memory.bot) sc mem_tgt)
        (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v' prom') sc' mem_tgt')
        (SHORTER: shorter_memory mem_src mem_tgt)
        (NOATTATCH: not_attatched L1 mem_src)
    :
      exists e_src mem_src',
        (<<STEP: Thread.step_allpf
                   e_src th_src
                   (Thread.mk lang st' (Local.mk v' prom') sc' mem_src')>>) /\
        (<<EVT: shorter_event e_src e_tgt>>) /\
        (<<SHORTER: shorter_memory mem_src' mem_tgt'>>) /\
        (<<NOATTATCH: not_attatched L1 mem_src'>>).
  Proof.
    dup SHORTER. inv SHORTER. inv STEP.
    eapply PRED in SAT. inv STEP0. des. inv STEP.
    - inv STEP0. ss.
    - inv STEP0. inv LOCAL.
      + eexists. exists mem_src; eauto. econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * esplits; eauto. econs.
      + inv LOCAL0. ss. clarify. exploit COMPLETE; eauto. i. des.
        exists (ThreadEvent.read loc ts val released ord). exists mem_src; eauto.
        econs; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * esplits; eauto. econs.
      + exploit write_msg_wf; eauto. i. des.
        exists (ThreadEvent.write loc (Time.middle from to) to val released ord).
        inv LOCAL0. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        dup WRITE. exploit Time.middle_spec; eauto. i. des.
        exploit shorter_memory_write.
        { eauto. }
        { eauto. }
        { instantiate (1:=Time.middle from to). left. auto. }
        { auto. }
        i. des. esplits; eauto.
        * econs; eauto.
          { econs 2; eauto. econs; eauto. }
        * econs; eauto. left. eauto.
        * eapply not_attatch_write; eauto. ii.
          exploit NOATTATCH; eauto. i. des.
          exploit memory_add_cover_disjoint; auto.
          { inv WRITE. inv PROMISE. eapply MEM. }
          { instantiate (1:=(Time.middle from to)).
            econs; eauto. ss. left. eauto. }
          { apply COVER. destruct msg. econs; eauto.
            econs; ss; eauto.
            - exploit Memory.get_ts; eauto. i. des; clarify.
              exfalso. rewrite x3 in *.
              eapply DenseOrder.DenseOrder.lt_strorder.
              instantiate (1:=Time.bot).
              eapply DenseOrder.DenseOrderFacts.le_lt_lt; eauto.
              apply Time.bot_spec.
            - refl. }
      + inv LOCAL1. ss.
        exists (ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw).
        exploit write_msg_wf; eauto. i. des.
        exploit COMPLETE; eauto. i. des.
        inv LOCAL2. ss. clarify.
        exploit memory_write_bot_add; eauto. i. clarify.
        dup WRITE. exploit shorter_memory_write; eauto.
        { refl. }
        i. des. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs; eauto.
        * eapply not_attatch_write; eauto.
      + inv LOCAL0. exists (ThreadEvent.fence ordr ordw).
        ss. clarify. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
      + inv LOCAL0. exists (ThreadEvent.syscall e).
        ss. clarify. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
      + eexists. exists mem_src; eauto. esplits; eauto.
        * econs; eauto. econs 2; eauto. econs; eauto.
        * econs.
  Qed.

End NOTATTATCHED.


Section FORGET.

  Inductive forget_statelocal:
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc1 lc2
      (TVIEW : lc1.(Local.tview) = lc2.(Local.tview))
      (PROMS : lc1.(Local.promises) = Memory.bot)
    :
      forget_statelocal (st, lc1) (st, lc2)
  .

  Inductive pf_sim_memory (proms: Loc.t -> Time.t -> Prop) (mem_src mem_tgt: Memory.t): Prop :=
  | pf_sim_memory_intro
      mem_inter
      (FORGET: forget_memory proms mem_inter mem_tgt)
      (SHORTER: shorter_memory mem_src mem_inter)
  .

  Inductive forget_thread others lang: Thread.t lang -> Thread.t lang -> Prop :=
  | forget_thread_intro
      st v prom sc mem_src mem_tgt
      (MEMP: pf_sim_memory (others \2/ promised prom) mem_src mem_tgt)
    :
      forget_thread
        others
        (Thread.mk lang st (Local.mk v Memory.bot) sc mem_src)
        (Thread.mk lang st (Local.mk v prom) sc mem_tgt)
  .

  Inductive all_promises (ths: Threads.t) (P: IdentMap.key -> Prop)
            (l: Loc.t) (t: Time.t) : Prop :=
  | all_promises_intro
      tid st lc
      (TID1: IdentMap.find tid ths = Some (st, lc))
      (PROMISED: promised lc.(Local.promises) l t)
      (SAT: P tid)
  .

  Inductive forget_config csrc ctgt : Prop :=
  | forget_configuration_intro
      (THS : forall tid, option_rel
                           forget_statelocal
                           (IdentMap.find tid csrc.(Configuration.threads))
                           (IdentMap.find tid ctgt.(Configuration.threads)))
      (SC : csrc.(Configuration.sc) = ctgt.(Configuration.sc))
      (MEM : pf_sim_memory (all_promises ctgt.(Configuration.threads) (fun _ => True))
                           (Configuration.memory csrc)
                           (Configuration.memory ctgt))
  .

End FORGET.



(* Section CAPPED. *)

(*   Inductive cap_timemap_le (cap: Loc.t -> Time.t -> option Time.t) *)
(*             (tm_src tm_tgt: TimeMap.t): Prop := *)
(*   | cap_timemap_le_intro *)
(*       (TLE: TimeMap.le tm_src tm_tgt) *)
(*       (CAPSPACE: forall loc to_src to_tgt (CAP: cap loc to_tgt = Some to_src) *)
(*                         (TLETGT: Time.le (tm_tgt loc) to_tgt), *)
(*           (<<TLESRC: Time.le (tm_src loc) to_src>>)) *)
(*   . *)

(*   Inductive cap_view_le (cap: Loc.t -> Time.t -> option Time.t) *)
(*             (vw_src vw_tgt: View.t): Prop := *)
(*   | view_le_intro *)
(*       (PLN: cap_timemap_le cap vw_src.(View.pln) vw_tgt.(View.pln)) *)
(*       (RLX: cap_timemap_le cap vw_src.(View.rlx) vw_tgt.(View.rlx)) *)
(*   . *)

(*   Inductive cap_tview_le (cap: Loc.t -> Time.t -> option Time.t) *)
(*             (tvw_src tvw_tgt: TView.t): Prop := *)
(*   | tview_le_intro *)
(*       (REL: forall loc, cap_view_le cap (tvw_src.(TView.rel) loc) (tvw_tgt.(TView.rel) loc)) *)
(*       (CUR: cap_view_le cap (tvw_src.(TView.cur)) (tvw_tgt.(TView.cur))) *)
(*       (ACQ: cap_view_le cap (tvw_src.(TView.acq)) (tvw_tgt.(TView.acq))) *)
(*   . *)

(*   Inductive option_le A B (R: A -> B -> Prop): option A -> option B -> Prop := *)
(*   | opt_le_none *)
(*       b *)
(*     : *)
(*       option_le R None b *)
(*   | opt_le_some *)
(*       a b *)
(*       (LE: R a b) *)
(*     : *)
(*       option_le R (Some a) (Some b) *)
(*   . *)

(*   Definition wf_cap (cap: Loc.t -> Time.t -> option Time.t): Prop := *)
(*     forall loc to_tgt to_src (CAP: cap loc to_tgt = Some to_src), *)
(*       (<<TLE: Time.lt to_src to_tgt>>) /\ *)
(*       (<<DISJ: forall to (ITV: Interval.mem (to_src, to_tgt) to), *)
(*           cap loc to = None>>) *)
(*   . *)

(*   Lemma wf_cap_disjoint cap loc to_tgt0 to_tgt1 to_src0 to_src1 *)
(*         (WFCAP: wf_cap cap) *)
(*         (CAP0: cap loc to_tgt0 = Some to_src0) *)
(*         (CAP1: cap loc to_tgt1 = Some to_src1) *)
(*         (TLT: Time.lt to_tgt0 to_tgt1) *)
(*     : *)
(*       Time.lt to_src0 to_src1. *)
(*   Proof. *)
(*     exploit WFCAP; try apply CAP0; eauto. i. des. *)
(*     exploit WFCAP; try apply CAP1; eauto. i. des. *)
(*     destruct (Time.le_lt_dec to_src1 to_src0); auto. *)
(*     exploit DISJ0. *)
(*     - instantiate (1:=to_tgt0). econs; ss. *)
(*       + eapply TimeFacts.le_lt_lt; eauto. *)
(*       + left. auto. *)
(*     - i. clarify. *)
(*   Qed. *)

(*   Definition wf_cap_mem (cap: Loc.t -> Time.t -> option Time.t) *)
(*              (mem_tgt: Memory.t): Prop := *)
(*     forall loc to_tgt to_src (CAP: cap loc to_tgt = Some to_src), *)
(*     exists v vw_src vw_tgt from_tgt, *)
(*       (<<TGTGET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, Message.full v vw_tgt)>>) /\ *)
(*       (<<CAPSPACE: forall t (ITV: Interval.mem (to_src, to_tgt) t), *)
(*           covered loc to_tgt mem_tgt>>) /\ *)
(*       (<<ORIGINAL: Memory.get loc to_src mem_tgt = Some (from_tgt, Message.full v vw_src)>>) *)
(*   . *)

(*   Inductive cap_memory (cap: Loc.t -> Time.t -> option Time.t) *)
(*             (mem_src mem_tgt: Memory.t): Prop := *)
(*   | cap_memory_intro *)
(*       (COVER: forall loc to (COV: covered loc to mem_src), covered loc to mem_tgt) *)
(*       (COMPLETE: *)
(*          forall loc to_tgt from_tgt v vw_tgt (TGTGET: Memory.get loc to_tgt mem_tgt = Some (from_tgt, Message.full v vw_tgt)), *)
(*            match cap loc to_tgt with *)
(*            | Some to_src => *)
(*              exists from_src vw_src, *)
(*              (<<SRCGET: Memory.get loc to_src mem_src = Some (from_src, Message.full v vw_src)>>) /\ *)
(*              (<<VLE: option_le (cap_view_le cap) vw_src vw_tgt>>) /\ *)
(*              (<<TGTUPDATABLE: *)
(*                 forall (SRCUPDATABLE: forall msg to, Memory.get loc to mem_tgt <> Some (to_tgt, msg)), *)
(*                 forall msg to, Memory.get loc to mem_src <> Some (to_src, msg)>>) *)
(*            | None => *)
(*              exists from_src vw_src, *)
(*              (<<SRCGET: Memory.get loc to_tgt mem_src = Some (from_src, Message.full v vw_src)>>) /\ *)
(*              (<<VLE: option_le (cap_view_le cap) vw_src vw_tgt>>) *)
(*            end). *)

(*   Definition cap_event (cap: Loc.t -> Time.t -> option Time.t) *)
(*              (te_src te_tgt: ThreadEvent.t): Prop := *)
(*     match te_src with *)
(*     | ThreadEvent.promise _ _ _ _ _ => False *)
(*     | ThreadEvent.read _ _ _ _ _ => False *)
(*     | ThreadEvent.write _ _ _ _ _ _ => False *)
(*     | ThreadEvent.update _ _ _ _ _ _ _ _ _ => False *)
(*     | _ => te_src = te_tgt *)
(*     end. *)

(*   Lemma wf_cap_add cap mem0 mem1 loc from to msg *)
(*         (ADD: Memory.add mem0 loc from to msg mem1) *)
(*         (WFCAP: wf_cap_mem cap mem0) *)
(*     : *)
(*       wf_cap_mem cap mem1. *)
(*   Proof. *)
(*     ii. exploit WFCAP; eauto. i. des. *)
(*     esplits; eauto. *)
(*     - eapply Memory.add_get1; eauto. *)
(*     - i. eapply add_covered; eauto. *)
(*     - eapply Memory.add_get1; eauto. *)
(*   Qed. *)

(*   Lemma cap_tview_readable_cap cap loc to_tgt to_src released_src released_tgt ord *)
(*         vw_tgt vw_src *)
(*         (READABLE: TView.readable vw_tgt loc to_tgt released_tgt ord) *)
(*         (CAP: cap loc to_tgt = Some to_src) *)
(*         (VLE: cap_view_le cap vw_src vw_tgt) *)
(*     : *)
(*       TView.readable vw_src loc to_src released_src ord. *)
(*   Proof. *)
(*     inv VLE. inv READABLE. econs. *)
(*     - inv PLN. eapply CAPSPACE; eauto. *)
(*     - inv RLX. i. specialize (RLX0 H). eapply CAPSPACE; eauto. *)
(*   Qed. *)

(*   Lemma cap_tview_readable_normal cap loc to_tgt released_src released_tgt ord *)
(*         vw_tgt vw_src *)
(*         (READABLE: TView.readable vw_tgt loc to_tgt released_tgt ord) *)
(*         (CAP: cap loc to_tgt = None) *)
(*         (VLE: cap_view_le cap vw_src vw_tgt) *)
(*     : *)
(*       TView.readable vw_src loc to_tgt released_src ord. *)
(*   Proof. *)
(*     inv VLE. inv READABLE. econs. *)
(*     - inv PLN. etrans; eauto. *)
(*     - inv RLX. i. specialize (RLX0 H). etrans; eauto. *)
(*   Qed. *)

(*   Lemma cap_tview_writable_cap cap loc to sc_tgt sc_src ord *)
(*         vw_tgt vw_src *)
(*         (READABLE: TView.writable vw_tgt sc_tgt loc to ord) *)
(*         (VLE: cap_view_le cap vw_src vw_tgt) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       TView.writable vw_src sc_src loc to ord. *)
(*   Proof. *)
(*     inv VLE. inv READABLE. econs. inv RLX. *)
(*     eapply TimeFacts.le_lt_lt; eauto. *)
(*   Qed. *)

(*   Lemma time_join_le t_src0 t_src1 t_tgt0 t_tgt1 *)
(*         (TLE0: Time.le t_src0 t_tgt0) *)
(*         (TLE1: Time.le t_src1 t_tgt1) *)
(*     : *)
(*       Time.le (Time.join t_src0 t_src1) (Time.join t_tgt0 t_tgt1). *)
(*   Proof. *)
(*     unfold Time.join. des_ifs. *)
(*     - etrans; eauto. left. auto. *)
(*     - etrans; eauto. *)
(*   Qed. *)

(*   Lemma timemap_join_le tm_src0 tm_src1 tm_tgt0 tm_tgt1 *)
(*         (VLE0: TimeMap.le tm_src0 tm_tgt0) *)
(*         (VLE1: TimeMap.le tm_src1 tm_tgt1) *)
(*     : *)
(*       TimeMap.le (TimeMap.join tm_src0 tm_src1) (TimeMap.join tm_tgt0 tm_tgt1). *)
(*   Proof. *)
(*     ii. unfold TimeMap.join. eapply time_join_le; eauto. *)
(*   Qed. *)

(*   Lemma cap_timemap_join_le cap tm_src0 tm_src1 tm_tgt0 tm_tgt1 *)
(*         (VLE0: cap_timemap_le cap tm_src0 tm_tgt0) *)
(*         (VLE1: cap_timemap_le cap tm_src1 tm_tgt1) *)
(*     : *)
(*       cap_timemap_le cap (TimeMap.join tm_src0 tm_src1) (TimeMap.join tm_tgt0 tm_tgt1). *)
(*   Proof. *)
(*     inv VLE0. inv VLE1. econs. *)
(*     - eapply timemap_join_le; eauto. *)
(*     - i. unfold TimeMap.join in *. eapply Time.join_spec. *)
(*       + eapply CAPSPACE; eauto. *)
(*         etrans; eauto. eapply Time.join_l. *)
(*       + eapply CAPSPACE0; eauto. *)
(*         etrans; eauto. eapply Time.join_r. *)
(*   Qed. *)

(*   Lemma cap_view_join_le cap v_src0 v_src1 v_tgt0 v_tgt1 *)
(*         (VLE0: cap_view_le cap v_src0 v_tgt0) *)
(*         (VLE1: cap_view_le cap v_src1 v_tgt1) *)
(*     : *)
(*       cap_view_le cap (View.join v_src0 v_src1) (View.join v_tgt0 v_tgt1). *)
(*   Proof. *)
(*     inv VLE0. inv VLE1. econs. *)
(*     - eapply cap_timemap_join_le; eauto. *)
(*     - eapply cap_timemap_join_le; eauto. *)
(*   Qed. *)

(*   Lemma cap_singleton_le_cap cap loc to_tgt to_src *)
(*         (CAP: cap loc to_tgt = Some to_src) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       cap_timemap_le cap (TimeMap.singleton loc to_src) (TimeMap.singleton loc to_tgt). *)
(*   Proof. *)
(*     econs. *)
(*     - unfold TimeMap.singleton. ii. setoid_rewrite LocFun.add_spec. des_ifs. *)
(*       + exploit WFCAP; eauto. i. des. left. eauto. *)
(*       + refl. *)
(*     - unfold TimeMap.singleton. ii. red. *)
(*       setoid_rewrite LocFun.add_spec. *)
(*       setoid_rewrite LocFun.add_spec in TLETGT. des_ifs. *)
(*       + destruct TLETGT. *)
(*         * left. eapply wf_cap_disjoint; eauto. *)
(*         * inv H. clarify. right. refl. *)
(*       + rewrite LocFun.init_spec. apply Time.bot_spec. *)
(*   Qed. *)

(*   Lemma cap_singleton_le_normal cap loc to_tgt *)
(*         (CAP: cap loc to_tgt = None) *)
(*         (SPACE: forall to to_src (CAP: cap loc to = Some to_src) (TLE: Time.lt to_tgt to), *)
(*             Time.lt to_tgt to_src) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       cap_timemap_le cap (TimeMap.singleton loc to_tgt) (TimeMap.singleton loc to_tgt). *)
(*   Proof. *)
(*     econs. *)
(*     - refl. *)
(*     - unfold TimeMap.singleton. ii. red. *)
(*       setoid_rewrite LocFun.add_spec. *)
(*       setoid_rewrite LocFun.add_spec in TLETGT. des_ifs. *)
(*       + destruct TLETGT. *)
(*         * exploit WFCAP; eauto. i. des. left. *)
(*           exploit SPACE; eauto. *)
(*         * destruct H. clarify. *)
(*       + rewrite LocFun.init_spec. apply Time.bot_spec. *)
(*   Qed. *)

(*   Lemma cap_timemap_bot_le cap tm *)
(*     : *)
(*       cap_timemap_le cap TimeMap.bot tm. *)
(*   Proof. *)
(*     econs; ss. *)
(*     - apply TimeMap.bot_spec. *)
(*     - i. red. apply Time.bot_spec. *)
(*   Qed. *)

(*   Lemma cap_view_bot_le cap v *)
(*     : *)
(*       cap_view_le cap View.bot v. *)
(*   Proof. *)
(*     econs; ss. *)
(*     - apply cap_timemap_bot_le. *)
(*     - apply cap_timemap_bot_le. *)
(*   Qed. *)

(*   Lemma cap_singleton_ur_le_cap cap loc to_tgt to_src *)
(*         (CAP: cap loc to_tgt = Some to_src) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       cap_view_le cap (View.singleton_ur loc to_src) (View.singleton_ur loc to_tgt). *)
(*   Proof. *)
(*     econs; ss. *)
(*     - eapply cap_singleton_le_cap; eauto. *)
(*     - eapply cap_singleton_le_cap; eauto. *)
(*   Qed. *)

(*   Lemma cap_singleton_rw_le_cap cap loc to_tgt to_src *)
(*         (CAP: cap loc to_tgt = Some to_src) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       cap_view_le cap (View.singleton_rw loc to_src) (View.singleton_rw loc to_tgt). *)
(*   Proof. *)
(*     econs; ss. *)
(*     - eapply cap_timemap_bot_le. *)
(*     - eapply cap_singleton_le_cap; eauto. *)
(*   Qed. *)

(*   Lemma cap_singleton_ur_le_normal cap loc to_tgt *)
(*         (CAP: cap loc to_tgt = None) *)
(*         (SPACE: forall to to_src (CAP: cap loc to = Some to_src) (TLE: Time.lt to_tgt to), *)
(*             Time.lt to_tgt to_src) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       cap_view_le cap (View.singleton_ur loc to_tgt) (View.singleton_ur loc to_tgt). *)
(*   Proof. *)
(*     econs; ss. *)
(*     - eapply cap_singleton_le_normal; eauto. *)
(*     - eapply cap_singleton_le_normal; eauto. *)
(*   Qed. *)

(*   Lemma cap_singleton_rw_le_normal cap loc to_tgt *)
(*         (CAP: cap loc to_tgt = None) *)
(*         (SPACE: forall to to_src (CAP: cap loc to = Some to_src) (TLE: Time.lt to_tgt to), *)
(*             Time.lt to_tgt to_src) *)
(*         (WFCAP: wf_cap cap) *)
(*     : *)
(*       cap_view_le cap (View.singleton_rw loc to_tgt) (View.singleton_rw loc to_tgt). *)
(*   Proof. *)
(*     econs; ss. *)
(*     - eapply cap_timemap_bot_le. *)
(*     - eapply cap_singleton_le_normal; eauto. *)
(*   Qed. *)

(*   Lemma cap_unwrap_le cap released_src released_tgt *)
(*         (RELEASEDLE : option_le (cap_view_le cap) released_src released_tgt) *)
(*     : *)
(*       cap_view_le cap (View.unwrap released_src) (View.unwrap released_tgt). *)
(*   Proof. *)
(*     inv RELEASEDLE; ss. apply cap_view_bot_le. *)
(*   Qed. *)

(*   Lemma read_tview_cap_le_cap cap loc to_tgt to_src released_src released_tgt ord *)
(*         tvw_tgt tvw_src *)
(*         (WFCAP: wf_cap cap) *)
(*         (CAP: cap loc to_tgt = Some to_src) *)
(*         (TVLE: cap_tview_le cap tvw_src tvw_tgt) *)
(*         (RELEASEDLE: option_le (cap_view_le cap) released_src released_tgt) *)
(*     : *)
(*       cap_tview_le cap (TView.read_tview tvw_src loc to_src released_src ord) *)
(*                    (TView.read_tview tvw_tgt loc to_tgt released_tgt ord). *)
(*   Proof. *)
(*     inv TVLE. econs; ss; eauto. *)
(*     - eapply cap_view_join_le. *)
(*       + eapply cap_view_join_le; eauto. *)
(*         unfold View.singleton_ur_if. des_ifs. *)
(*         * eapply cap_singleton_ur_le_cap; eauto. *)
(*         * eapply cap_singleton_rw_le_cap; eauto. *)
(*       + des_ifs. *)
(*         * eapply cap_unwrap_le; eauto. *)
(*         * eapply cap_view_bot_le. *)
(*     - eapply cap_view_join_le. *)
(*       + eapply cap_view_join_le; eauto. *)
(*         unfold View.singleton_ur_if. des_ifs. *)
(*         * eapply cap_singleton_ur_le_cap; eauto. *)
(*         * eapply cap_singleton_rw_le_cap; eauto. *)
(*       + des_ifs. *)
(*         * eapply cap_unwrap_le; eauto. *)
(*         * eapply cap_view_bot_le. *)
(*   Qed. *)

(*   Lemma read_tview_cap_le_normal cap loc to_tgt released_src released_tgt ord *)
(*         tvw_tgt tvw_src *)
(*         (WFCAP: wf_cap cap) *)
(*         (CAP: cap loc to_tgt = None) *)
(*         (SPACE: forall to to_src (CAP: cap loc to = Some to_src) (TLE: Time.lt to_tgt to), *)
(*             Time.lt to_tgt to_src) *)
(*         (TVLE: cap_tview_le cap tvw_src tvw_tgt) *)
(*         (RELEASEDLE: option_le (cap_view_le cap) released_src released_tgt) *)
(*     : *)
(*       cap_tview_le cap (TView.read_tview tvw_src loc to_tgt released_src ord) *)
(*                    (TView.read_tview tvw_tgt loc to_tgt released_tgt ord). *)
(*   Proof. *)
(*     inv TVLE. econs; ss; eauto. *)
(*     - eapply cap_view_join_le. *)
(*       + eapply cap_view_join_le; eauto. *)
(*         unfold View.singleton_ur_if. des_ifs. *)
(*         * eapply cap_singleton_ur_le_normal; eauto. *)
(*         * eapply cap_singleton_rw_le_normal; eauto. *)
(*       + des_ifs. *)
(*         * eapply cap_unwrap_le; eauto. *)
(*         * eapply cap_view_bot_le. *)
(*     - eapply cap_view_join_le. *)
(*       + eapply cap_view_join_le; eauto. *)
(*         unfold View.singleton_ur_if. des_ifs. *)
(*         * eapply cap_singleton_ur_le_normal; eauto. *)
(*         * eapply cap_singleton_rw_le_normal; eauto. *)
(*       + des_ifs. *)
(*         * eapply cap_unwrap_le; eauto. *)
(*         * eapply cap_view_bot_le. *)
(*   Qed. *)

(*   Lemma cap_step *)
(*         lang cap th_src th_tgt th_tgt' st st' v_src v_tgt v_tgt' prom' sc sc' *)
(*         mem_src mem_tgt mem_tgt' e_tgt *)
(*         (VWF: TView.wf v_src) *)
(*         (TH_SRC: th_src = Thread.mk lang st (Local.mk v_src Memory.bot) sc mem_src) *)
(*         (TH_TGT0: th_tgt = Thread.mk lang st (Local.mk v_tgt Memory.bot) sc mem_tgt) *)
(*         (TH_TGT1: th_tgt' = Thread.mk lang st' (Local.mk v_tgt' prom') sc' mem_tgt') *)
(*         (WFCAP: wf_cap cap) *)
(*         (WFCAPMEM: wf_cap_mem cap mem_tgt) *)
(*         (VIEW: cap_tview_le cap v_src v_tgt) *)
(*         (MEM: cap_memory cap mem_src mem_tgt) *)
(*         (STEP: pred_step (no_promise /1\ no_sc) e_tgt th_tgt th_tgt') *)
(*     : *)
(*       exists e_src v_src' mem_src', *)
(*         (<<STEP: (@pred_step *)
(*                     (no_promise /1\ no_sc) lang) *)
(*                    e_src th_src *)
(*                    (Thread.mk lang st' (Local.mk v_src' Memory.bot) sc mem_src')>>) /\ *)
(*         (<<VIEW: cap_tview_le cap v_src' v_tgt'>>) /\ *)
(*         (<<MEM: cap_memory cap mem_src' mem_tgt'>>) /\ *)
(*         (<<EVT: cap_event cap e_src e_tgt>>). *)
(*   Proof. *)
(*     clarify. inv STEP. inv STEP0. des. inv STEP; inv STEP0; ss. inv LOCAL; ss. *)
(*     - exists ThreadEvent.silent, v_src, mem_src. esplits; eauto. *)
(*       + econs; eauto. econs; eauto. econs 2; eauto. econs; eauto. *)
(*       + admit. *)
(*     - inv LOCAL0. ss. clarify. inv MEM. *)
(*       exploit COMPLETE; eauto. i. des_ifs. *)
(*       + des. exists (ThreadEvent.read loc t val vw_src ord). esplits. *)
(*         * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto. *)
(*           econs; eauto. econs; eauto. ss. *)
(*           inv VIEW. eapply cap_tview_readable_cap; eauto. *)
(*         * ss. eapply read_tview_cap_le_cap; eauto. *)
(*         * ss. *)
(*         * admit. *)
(*           (* event *) *)
(*       + des. exists (ThreadEvent.read loc ts val vw_src ord). esplits. *)
(*         * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto. *)
(*           econs; eauto. econs; eauto. ss. *)
(*           (* cap_view_le => Tview.readable *) *)
(*           inv VIEW. eapply cap_tview_readable_normal; eauto. *)
(*         * ss. eapply read_tview_cap_le_normal; eauto. i. *)
(*           (* difficult.. *) *)
(*           admit. *)
(*         * ss. *)
(*         * admit. *)
(*           (* event *) *)
(*     - exploit write_msg_wf; eauto. i. des. *)
(*       inv LOCAL0. ss. clarify. *)
(*       exploit memory_write_bot_add; eauto. i. clarify. inv WRITE. inv PROMISE. *)

(*       exploit write_succeed. *)
(*       + instantiate (1:=to). instantiate (1:=from). instantiate (1:=mem_src). *)
(*         instantiate (1:=loc). *)
(*         admit. *)
(*       + instantiate (1:= (TView.write_released v_src sc loc to None ord)). *)
(*         etrans; eauto. *)
(*         admit. *)
(*         (* exploit View.unwrap_opt_le. *) *)
(*         (* * eapply TViewFacts.write_released_mon. *) *)
(*         (*   { eappl *) *)
(*       + ss. *)
(*       + eapply Message.wf_view. *)
(*         exploit TViewFacts.write_future0; eauto. *)
(*         i. des. eapply WF_RELEASED. *)
(*       + i. des. *)
(*         exists (ThreadEvent.write loc from to val (TView.write_released v_src sc loc to None ord) ord). *)
(*         esplits; eauto. *)
(*         * econs; eauto. econs; eauto. econs 2; eauto. econs; eauto. econs; eauto. *)
(*           econs; eauto. ss. *)
(*           eapply TViewFacts.writable_mon; eauto. *)
(*           { inv VIEW. inv CUR. inv PLN. inv RLX. econs; eauto. } *)
(*           { refl. } *)
(*           { refl. } *)
(*         * ss. *)
(*           admit. *)
(*         * admit. *)
(*         * admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*   Admitted. *)

(* End CAPPED. *)


Inductive concrete_covered (prom mem: Memory.t) (loc: Loc.t) (ts: Time.t): Prop :=
| concrete_covered_intro
    from to val released
    (GET: Memory.get loc to prom = Some (from, Message.full val released))
    (ITV: Interval.mem (from, to) ts)
| concrete_covered_reserve
    from to
    from1 to1 val released
    (GET: Memory.get loc to prom = Some (from, Message.reserve))
    (GET1: Memory.get loc to1 mem = Some (from1, Message.full val released))
    (NOTLAST: Time.lt to to1)
    (ITV: Interval.mem (from, to) ts)
.

Lemma concrete_covered_same prom mem0 mem1
      (FUTURE: Memory.future mem0 mem1)
  :
    concrete_covered prom mem0 <2= concrete_covered prom mem1.
Proof.
  i. inv PR.
  - econs 1; eauto.
  - exploit Memory.future_get1; eauto. i. des.
    inv MSG_LE. econs 2; eauto.
Qed.

Module Inv.

  Record t mem lang (st: Language.state lang) lc
         (proms: Memory.t)
         (spaces : Loc.t -> Time.t -> Prop)
         (aupdates : Loc.t -> Time.t -> Prop)
         (updates : Loc.t -> Time.t -> Prop)
         (mlast: Memory.t): Prop :=
    {
      SPACES: forall loc ts (IN: spaces loc ts), concrete_covered proms mem loc ts;
      AUPDATES: forall loc ts (IN: aupdates loc ts),
          exists to,
            (<<GET: Memory.get loc ts proms = Some (ts, to)>>);
      PROMS: forall
          loc to m sc (PROM : concrete_promised proms loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@Thread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            ((<<WRITING : is_writing _ st' loc Ordering.relaxed>>) \/
             (<<ABORTING : is_aborting _ st'>>));
      UPDATE : forall
          loc to m sc (UPD : updates loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@Thread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_updating _ st' loc Ordering.relaxed>>);
      AUPDATE : forall
          loc to m sc (UPD : aupdates loc to)
          (FUTURE: unchanged_on spaces mlast m)
          (UNCHANGED: not_attatched (updates \2/ aupdates) m),
          exists st' lc' sc' m',
            (<<STEPS : rtc (tau (@Thread.program_step _))
                           (Thread.mk _ st lc sc m)
                           (Thread.mk _ st' lc' sc' m')>>) /\
            (<<READING : is_updating _ st' loc Ordering.seqcst>>);
    }.

End Inv.


Section SIMPF.

  Inductive thread_wf lang (th: Thread.t lang): Prop :=
  | thread_wf_intro
      (SC: Memory.closed_timemap th.(Thread.sc) th.(Thread.memory))
      (CLOSED: Memory.closed th.(Thread.memory))
      (LCWF: Local.wf th.(Thread.local) th.(Thread.memory))
  .

  Inductive sim_pf
            (mlast: Ident.t -> Memory.t)
            (spaces : Ident.t -> (Loc.t -> Time.t -> Prop))
            (updates: Ident.t -> (Loc.t -> Time.t -> Prop))
            (aupdates: Ident.t -> (Loc.t -> Time.t -> Prop))
            (c_src c_tgt: Configuration.t) : Prop :=
  | sim_pf_intro
      (FORGET: forget_config c_src c_tgt)

      (FUTURE:
         forall tid,
           unchanged_on (spaces tid) (mlast tid) c_src.(Configuration.memory))
      (NOATTATCH:
         forall tid,
           not_attatched (updates tid) c_src.(Configuration.memory))

      (INV:
         forall
           tid lang_src st_src lc_src lang_tgt st_tgt lc_tgt
           (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) =
                    Some (existT _ lang_src st_src, lc_src))
           (TIDTGT: IdentMap.find tid c_tgt.(Configuration.threads) =
                    Some (existT _ lang_tgt st_tgt, lc_tgt)),
           Inv.t c_tgt.(Configuration.memory) _ st_src lc_src lc_tgt.(Local.promises) (spaces tid) (updates tid) (aupdates tid) (mlast tid))
      (INVBOT:
         forall
           tid
           (TIDSRC: IdentMap.find tid c_src.(Configuration.threads) = None),
           (<<SPACESBOT: spaces tid <2= bot2>>) /\
           (<<UPDATESBOT: updates tid <2= bot2>>) /\
           (<<AUPDATESBOT: aupdates tid <2= bot2>>))

      (RACEFREE: pf_racefree c_src)
      (WFSRC: Configuration.wf c_src)
      (WFTGT: Configuration.wf c_tgt)
  .

  Inductive sim_pf_all c_src c_tgt: Prop :=
  | sim_pf_all_intro mlast spaces updates aupdates
                     (SIM : sim_pf mlast spaces updates aupdates c_src c_tgt)
  .

  Lemma init_pf s tid st lc
        (TID: IdentMap.find tid (Threads.init s) = Some (st, lc))
    :
      Local.promises lc = Memory.bot.
  Proof.
    unfold Threads.init in *. erewrite UsualFMapPositive.UsualPositiveMap.Facts.map_o in *.
    unfold option_map in *. des_ifs.
  Qed.

  Lemma sim_pf_init
        s
        (RACEFREE: pf_racefree (Configuration.init s))
    :
      sim_pf_all (Configuration.init s) (Configuration.init s)
  .
  Proof.
    econs.
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ _ _ => False).
    instantiate (1:=fun _ => Memory.init).
    econs; eauto; ss; i.
    - econs; i; ss.
      + unfold Threads.init in *. erewrite UsualFMapPositive.UsualPositiveMap.Facts.map_o in *.
        unfold option_map in *. des_ifs.
      + econs.
        * instantiate (1:= Memory.init). econs; ss; eauto.
          ii. inv PROMS. ss.
          exploit init_pf; eauto. i. rewrite x0 in *.
          inv PROMISED. rewrite Memory.bot_get in *. clarify.
        * refl.
    - econs; ss.
    - econs; eauto; ii; clarify.
      exploit init_pf; try apply TIDTGT; eauto. i.
      rewrite x0 in *. inv PROM.
      rewrite Memory.bot_get in *. clarify.
    - splits; ss.
    - eapply Configuration.init_wf.
    - eapply Configuration.init_wf.
  Qed.

End SIMPF.
