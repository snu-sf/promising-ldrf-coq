Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Language.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.
Require Import Progress.
Require Import Behavior.
Require Import Cover.
Require Import Pred.
Require Import Trace.

Require Import MemoryProps.

Require Import LocalDRFDef.

Set Implicit Arguments.


Section SIM.

  Variable L: Loc.t -> bool.

  Definition in_L (loc: Loc.t) (ts: Time.t) := L loc.

  Inductive sim_memory_content P (loc: Loc.t)
            (messages: Time.t -> Prop)
    : option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_none
      (NPROM: ~ P)
    :
      sim_memory_content P loc messages None None
  | sim_memory_content_normal
      from_src from_tgt msg_src msg_tgt
      (NPROM: ~ P)
      (FROM: Time.le from_tgt from_src)
      (SHORT: L loc -> ~ messages from_tgt -> Time.lt from_tgt from_src)
      (MSG: Message.le msg_src msg_tgt)
      (RESERVE: msg_src = Message.reserve -> msg_tgt = Message.reserve)
    :
      sim_memory_content P loc messages (Some (from_src, msg_src)) (Some (from_tgt, msg_tgt))
  | sim_memory_content_forget
      from_src from_tgt msg
      (PROM: P)
      (NLOC: L loc)
      (FROM: Time.le from_tgt from_src)
      (SHORT: ~ messages from_tgt -> Time.lt from_tgt from_src)
   :
      sim_memory_content P loc messages (Some (from_src, Message.reserve)) (Some (from_tgt, msg))
  .
  Hint Constructors sim_memory_content.

  Definition sim_memory P mem_src mem_tgt : Prop :=
    forall loc ts,
      sim_memory_content (P loc ts) loc (promised mem_src loc) (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt).

  Inductive sim_promise_content (loc: Loc.t) (ts: Time.t)
            (P: Prop)
            (rel_src: View.t)
    :
      option Memory.t -> option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_none
      (NPROM: ~ P)
      past
    :
      sim_promise_content loc ts P rel_src past None None
  | sim_promise_content_normal_concrete
      (NPROM: ~ P)
      (NLOC: ~ L loc)
      past from val released_src released_tgt
      (MSG: sim_opt_view past loc ts released_src released_tgt)
      (RELVIEW: forall released (MSG: released_src = Some released),
          add_weak_closed_view rel_src past loc ts)
    :
      sim_promise_content loc ts P rel_src
                          (Some past)
                          (Some (from, Message.concrete val released_src))
                          (Some (from, Message.concrete val released_tgt))
  | sim_promise_content_normal_reserve
      (NPROM: ~ P)
      (NLOC: ~ L loc)
      past from
    :
      sim_promise_content loc ts P rel_src
                          past
                          (Some (from, Message.reserve))
                          (Some (from, Message.reserve))
  | sim_promise_content_forget
      (PROM: P)
      (LOC: L loc)
      past from_src from_tgt msg
    :
      sim_promise_content loc ts P rel_src
                          past
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, msg))
  .
  Hint Constructors sim_promise_content.

  Definition sim_promise
             (self: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content loc ts (self loc ts) (rel_src loc) (pasts loc ts)
                          (Memory.get loc ts prom_src)
                          (Memory.get loc ts prom_tgt).

  Inductive sim_local (self: Loc.t -> Time.t -> Prop) (pasts: Loc.t -> Time.t -> option Memory.t)
            (lc_src lc_tgt: Local.t): Prop :=
  | forget_local_intro
      (TVIEW : TView.le lc_src.(Local.tview) lc_tgt.(Local.tview))
      (PROMS: sim_promise self lc_src.(Local.tview).(TView.rel) pasts lc_src.(Local.promises) lc_tgt.(Local.promises))
    :
      sim_local self pasts lc_src lc_tgt
  .

  Inductive sim_statelocal (self: Loc.t -> Time.t -> Prop)
            (pasts: Loc.t -> Time.t -> option Memory.t):
    sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc_src lc_tgt
      (LOCAL: sim_local self pasts lc_src lc_tgt)
    :
      sim_statelocal self pasts (st, lc_src) (st, lc_tgt)
  .

  Inductive all_promises (proms: Ident.t -> Loc.t -> Time.t -> Prop): Loc.t -> Time.t -> Prop :=
  | all_promises_intro
      tid loc ts
      (PROMS: proms tid loc ts)
    :
      all_promises proms loc ts
  .
  Hint Constructors all_promises.

  Lemma sim_read_step P self pasts lc_src lc_tgt mem_src mem_tgt loc to val released_tgt ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released_tgt ord lc_tgt')
        (NOREAD: ~ P loc to)
        (MEM: sim_memory P mem_src mem_tgt)
        (LOCAL: sim_local self pasts lc_src lc_tgt)
    :
      exists lc_src' released_src,
        (<<STEPSRC: Local.read_step lc_src mem_src loc to val released_src ord lc_src'>>) /\
        (<<SIM: sim_local self pasts lc_src' lc_tgt'>>) /\
        (<<RELEASEDMLE: View.opt_le released_src released_tgt>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_src = Some (from, Message.concrete val released_src)>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_tgt = Some (from, Message.concrete val released_tgt)>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    specialize (MEM loc to). rewrite GET in *. inv MEM; ss. inv MSG.
    esplits.
    - econs; eauto. eapply TViewFacts.readable_mon; eauto.
      + eapply TVIEW.
      + refl.
    - econs; ss; eauto. eapply read_tview_mon; eauto. refl.
    - auto.
    - eauto.
    - eauto.
  Qed.

  Lemma sim_fence_step self pasts lc_src lc_tgt sc_src sc_tgt ordr ordw
        sc_tgt' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc_tgt ordr ordw lc_tgt' sc_tgt')
        (SC: TimeMap.le sc_src sc_tgt)
        (LOCAL: sim_local self pasts lc_src lc_tgt)
    :
      exists lc_src' sc_src',
        (<<STEPSRC: Local.fence_step lc_src sc_src ordr ordw lc_src' sc_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local self pasts lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    assert (TVIEWLE:
              TView.le
                (TView.write_fence_tview
                   (TView.read_fence_tview (Local.tview lc_src) ordr) sc_src ordw)
                (TView.write_fence_tview
                   (TView.read_fence_tview (Local.tview lc_tgt) ordr) sc_tgt ordw)).
    { eapply write_fence_tview_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto. }
    esplits.
    - econs; ss; eauto. ii.
      specialize (PROMS loc t). rewrite GET in *. inv PROMS; ss.
      exploit RELEASE; eauto. ss. ii. inv MSG; ss.
    - eapply write_fence_fc_mon_same_ord; eauto.
      eapply read_fence_tview_mon_same_ord; eauto.
    - econs; ss; eauto. ii.
      specialize (PROMS loc ts). des_ifs.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
      + inv PROMS; econs; ss; eauto. i.
        exfalso. inv MSG; ss. exploit RELEASE; eauto; ss.
        destruct ordw; eauto.
  Qed.

  Lemma sim_promise_consistent prom_self pasts lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii.
    specialize (PROMS loc ts). rewrite PROMISE in *. inv PROMS.
    exploit CONSISTENT; eauto. i. eapply TimeFacts.le_lt_lt; eauto.
    inv TVIEW. inv CUR. auto.
  Qed.

  Lemma sim_failure_step prom_self pasts lc_src lc_tgt
        (STEPTGT: Local.failure_step lc_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
    :
      Local.failure_step lc_src.
  Proof.
    inv STEPTGT. econs.
    eapply sim_promise_consistent; eauto.
  Qed.

  Lemma sim_memory_others_self_wf
        P mem_src mem_tgt
        (MEMORY: sim_memory P mem_src mem_tgt)
    :
      forall loc' to', P loc' to' -> L loc'.
  Proof.
    ii. specialize (MEMORY loc' to'). inv MEMORY; clarify.
  Qed.

  Lemma sim_promise_step_normal others self pasts mem_src mem_tgt rel_src prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELWF: View.wf (rel_src loc))
        (RELCONSISTENT: forall val released (MSG: msg_tgt = Message.concrete val released),
            Time.le ((rel_src loc).(View.rlx) loc) to)
        (RELSRC: Memory.closed_view (rel_src loc) mem_src)
        (PROMISE: sim_promise self rel_src pasts prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self mem_src)
        (* (PROMSWF: forall loc' to', others loc' to' -> L loc') *)
    :
      exists msg_src kind_src pasts' prom_src' mem_src',
        (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' kind_src>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self rel_src pasts' prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>) /\
        (<<PROMATTACH: promises_not_attached self mem_src'>>) /\
        (<<CLOSED: Memory.closed_message msg_src mem_src'>>)
  .
  Proof.
    generalize (sim_memory_others_self_wf MEM). intros PROMSWF.
    inv STEPTGT.

    (* add case *)
    - hexploit (@sim_message_exists mem_src loc to msg_tgt); eauto. i. des.

      exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg_src); ss.
      { i. specialize (MEM loc to2). rewrite GET2 in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      { eapply sim_message_wf; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (ATTACHSRC: forall val released to' msg'
                                (MSG: msg_src = Message.concrete val released)
                                (GET: Memory.get loc to' mem_src = Some (to, msg')), False).
      { i. clarify. inv SIM.
        specialize (MEM loc to'). rewrite GET in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; eauto. }
        inv FROM.
        { exploit DISJOINT; auto.
          - symmetry. eapply H.
          - instantiate (1:=to). econs; ss. refl.
          - econs; ss. eapply memory_get_ts_le; eauto.
        }
        { inv H0. exploit ATTACH; eauto. }
      }

      assert (MSGTO: Memory.message_to msg_src loc to).
      { inv SIM; econs. inv TS. etrans; eauto.
        apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
        inv SIM0. auto.
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { destruct msg_src; auto.
        eapply add_closed_message_add_closed; eauto.
        eapply sim_message_closed; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists msg_src, Memory.op_kind_add,
      (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then (if msg_src then (Some mem_src) else None) else pasts loc' to'),
      prom_src', mem_src'. splits; auto.
      + ii. erewrite promised_add; eauto.
        erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * econs; eauto.
          { refl. }
          { i. clarify. }
          { eapply sim_message_le; eauto. }
          { i. clarify. inv SIM. auto. }
        * specialize (MEM loc ts). inv MEM; eauto.
      + ii. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso. eauto.
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. inv SIM; econs; eauto.
          i. eapply add_closed_add_weak_closed_view, closed_add_closed_view. auto.
        * ss. des; clarify. inv SIM; econs; eauto.
      + inv PAST. econs.
        * ii. erewrite (@Memory.add_o mem_src') in GET; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify. esplits; eauto.
            - eapply sim_message_closed in SIM. inv SIM. inv CLOSED; econs; auto.
            - i. des_ifs.
              { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
              guardH o. exploit ONLY; eauto. i. des; auto.
          }
          { guardH o. exploit COMPLETE; eauto. i. des.
            esplits; eauto. des_ifs. ss. des; clarify.
            exfalso. inv SIM. eapply ATTACHSRC; eauto.
          }
        * i. des_ifs.
          { ss. des; clarify. splits; auto.
            - econs. eapply Memory.add_get0; eauto.
            - apply Memory.future_future_weak. auto.
          }
          { guardH o. exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. apply Memory.future_future_weak. auto. }
      + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        inv PAST. apply ONLY in PAST0. des. inv CONCRETE.
        apply Memory.add_get0 in ADDMEMSRC. des. clarify.
      + ii. erewrite (@Memory.add_o mem_src' mem_src) in GET; eauto. des_ifs.
        { ss. des; clarify. exfalso. eauto. }
        eapply PROMATTACH; eauto.

    - exploit split_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc ts3). rewrite GET2 in *.
      inv PAST.
      inv PROMISE0; ss; [destruct released_src as [released_src|]|].

      (* split normal message with non-none view *)
      { exploit ONLY; eauto. i. des.
        hexploit (@sim_message_exists past loc to (Message.concrete val' released')); eauto.
        i. des.

        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val (Some released_src)))).
        { econs; eauto. inv SIM. eauto. }

        assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
        { destruct msg_src; auto.
          eapply add_closed_message_split_closed; eauto.
          eapply add_closed_message_future_add_closed; eauto.
          eapply sim_message_closed; eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 (Message.concrete val (Some released_src))),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some past)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite promised_split; eauto.
          erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto.
          des_ifs; try by (ss; des; clarify).
          { ss. des; clarify. econs; eauto.
            * refl.
            * i. clarify.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * refl.
            * i. clarify.
            * econs. eapply sim_opt_view_le; eauto.
            * i. clarify.
          }
          { specialize (MEM loc ts). inv MEM; eauto. }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. exfalso. eauto.
          * guardH o. ss. des; clarify. exfalso. eauto.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
            i. eapply add_weak_closed_view_consistent; eauto.
          * guardH o. ss. des; clarify. inv SIM.
            rewrite <- H0. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED0; econs; auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. exploit COMPLETE; eauto. i. des.
                eapply PREV in PAST; eauto. rewrite PAST0 in *. clarify.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; clarify. rewrite <- H0 in *. esplits; eauto.
              - inv MSG. econs. eapply sim_view_closed; eauto.
              - i. des_ifs.
                + refl.
                + ss. des; clarify.
            }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val0 (Some released'0)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE0.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto. des_ifs.
          * ss. des; clarify. exfalso. eauto.
          * guardH o. ss. des; clarify. exfalso. eauto.
          * eapply PROMATTACH; eauto.
      }

      (* split normal message with none view *)
      { exploit ONLY; eauto. i. des.
        hexploit (@sim_message_exists mem_src loc to (Message.concrete val' released')); eauto.

        i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val None))).
        { econs; eauto. inv SIM. eauto. }

        assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
        { destruct msg_src; auto.
          eapply add_closed_message_split_closed; eauto.
          eapply sim_message_closed; eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 (Message.concrete val None)),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some mem_src)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite promised_split; eauto.
          erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto.
          des_ifs; try by (des; ss; clarify).
          { ss. des; clarify. econs; eauto.
            * refl.
            * i. clarify.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * refl.
            * i. clarify.
            * i. clarify.
          }
          { specialize (MEM loc ts). inv MEM; eauto. }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. exfalso. eauto.
          * guardH o. ss. des; clarify. exfalso. eauto.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
            i. eapply add_closed_add_weak_closed_view, closed_add_closed_view. auto.
          * guardH o. ss. des; clarify. inv SIM.
            rewrite <- H0. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED0; econs; auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. eapply ONLY; eauto.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; clarify. esplits; eauto.
              - econs.
              - i. clarify. }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val0 (Some released'0)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE0.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto. des_ifs.
          * ss. des; clarify. exfalso. eauto.
          * guardH o. ss. des; clarify. exfalso. eauto.
          * guardH o. guardH o0. eapply PROMATTACH; eauto.
      }

      (* split reserve *)
      { hexploit (@sim_message_exists mem_src loc to (Message.concrete val' released')); eauto.

        i. des.
        hexploit (@Memory.split_exists prom_src loc from to ts3 msg_src); ss.
        { eauto. }
        { eapply sim_message_wf; eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (MSGTO: Memory.message_to msg_src loc to).
        { inv SIM; econs. inv TS. etrans; eauto.
          apply sim_opt_view_le in SIM0. apply View.unwrap_opt_le in SIM0.
          inv SIM0. auto.
        }

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 Message.reserve)).
        { econs; eauto. inv SIM. eauto. }

        assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
        { destruct msg_src; auto.
          eapply add_closed_message_split_closed; eauto.
          eapply sim_message_closed; eauto. }

        assert (FUTURE: Memory.future mem_src mem_src').
        { econs; [|refl]. econs; eauto. }

        exists msg_src, (Memory.op_kind_split ts3 Message.reserve),
        (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                         then (Some mem_src)
                         else pasts loc' to'),
        prom_src', mem_src'. splits; auto.
        + ii. erewrite promised_split; eauto.
          erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto.
          des_ifs; try by (des; ss; clarify).
          { ss. des; clarify. econs; eauto.
            * refl.
            * i. clarify.
            * eapply sim_message_le; eauto.
            * i. clarify. inv SIM.
          }
          { guardH o. ss. des; clarify. econs; eauto.
            * refl.
            * i. clarify.
          }
          { specialize (MEM loc ts). inv MEM; eauto. }
        + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
          * ss. des; clarify. exfalso. eauto.
          * guardH o. ss. des; clarify. exfalso. eauto.
        + ii. erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. inv SIM; econs; eauto.
            i. eapply add_closed_add_weak_closed_view, closed_add_closed_view. auto.
          * guardH o. ss. des; clarify. inv SIM. econs; eauto.
        + econs.
          * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. esplits; eauto.
              - eapply sim_message_closed in SIM. inv SIM. inv CLOSED; econs; auto.
              - i. des_ifs.
                { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
                guardH o. eapply ONLY; eauto.
            }
            guardH o. destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. }
            { guardH o0. exploit COMPLETE; eauto. i. des.
              esplits; eauto. i. des_ifs.
              - ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (1:=Message.concrete val (Some released'0)).
                  instantiate (1:=to0). erewrite Memory.split_o; [|eauto]. des_ifs.
                  - ss. unguard. des; clarify.
                  - ss. unguard. des; clarify. }
                { i. des; clarify.
                  - unguard. des; clarify.
                  - eapply Time.lt_strorder; eauto.
                  - eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    + eapply TS12.
                    + eapply Time.bot_spec. }
              - guardH o1. exploit COMPLETE; eauto.
            }
          * i. des_ifs.
            { ss. des; clarify. splits; auto.
              - eapply Memory.split_get0 in SPLITMEMSRC. des.
                inv SIM. econs; eauto.
              - apply Memory.future_future_weak. auto.
            }
            { guardH o. exploit ONLY; eauto. i. des. splits; auto.
              - eapply concrete_promised_increase_promise; eauto.
              - etrans; eauto. apply Memory.future_future_weak. auto. }
        + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
          ss. des; clarify. exfalso.
          apply ONLY in PAST0. des. inv CONCRETE.
          apply Memory.split_get0 in SPLITMEMSRC. des. clarify.
        + ii. erewrite (@Memory.split_o mem_src' mem_src) in GET; eauto. des_ifs.
          * ss. des; clarify. exfalso. eauto.
          * guardH o. ss. des; clarify. exfalso. eauto.
          * eapply PROMATTACH; eauto.
      }

    (* lower case *)
    - exploit lower_succeed_wf; try apply PROMISES. i. des. clarify.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PAST. inv PROMISE0; ss.

      exploit ONLY; eauto. i. des.
      hexploit (@sim_message_exists past loc to msg_tgt); eauto. i. des.

      inv MSG_LE. dup SIM. inv SIM.
      assert (VIEWLE: View.opt_le released_src0 released_src).
      { eapply sim_opt_view_max; eauto.
        - etrans; eauto. eapply sim_opt_view_le; eauto.
        - eapply sim_opt_view_closed; eauto. }

      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released_src) (Message.concrete val released_src0)); ss.
      { eapply sim_message_wf; eauto. }
      { econs; eauto. }

      intros [prom_src' LOWERPROMSRC].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (MSGTO: Memory.message_to (Message.concrete val released_src0) loc to).
      { econs. inv TS. etrans; eauto.
        apply sim_opt_view_le in SIM1. apply View.unwrap_opt_le in SIM1.
        inv SIM1. auto.
      }

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val released_src0) prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val released_src))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message (Message.concrete val released_src0) mem_src').
      { eapply add_closed_message_lower_closed; eauto.
        eapply add_closed_message_future_add_closed; eauto.
        eapply sim_message_closed; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists (Message.concrete val released_src0), (Memory.op_kind_lower (Message.concrete val released_src)), pasts, prom_src', mem_src'. splits; auto.
      + ii. erewrite promised_lower; eauto; ss.
        erewrite (@Memory.lower_o mem_src'); eauto.
        erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify. econs; eauto.
        * refl.
        * i. clarify.
        * eapply sim_message_le; eauto.
        * i. clarify.
      + ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso. eauto.
      + ii. erewrite (@Memory.lower_o prom_src'); eauto.
        erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. rewrite <- H0. econs; eauto.
        i. clarify. inv VIEWLE. eapply RELVIEW; eauto.
      + econs.
        * ii. erewrite (@Memory.lower_o mem_src') in GET0; eauto. des_ifs.
          { ss. des; clarify. esplits; eauto.
            - inv SIM1. econs.
              eapply sim_view_closed; eauto. econs.
            - i. exploit COMPLETE; eauto. i. des.
              rewrite PAST0 in *. clarify. inv VIEWLE. eauto.
          }
          { guardH o. exploit COMPLETE; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. apply Memory.future_future_weak. auto. }
      + refl.
      + ii. erewrite Memory.lower_o in GET0; eauto. des_ifs.
        * ss. des; clarify. exfalso; eauto.
        * eapply PROMATTACH; eauto.

    (* cancel case *)
    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; ss.

      hexploit (@Memory.remove_exists prom_src loc from to Message.reserve); ss.
      intros [prom_src' REMOVEPROMSRC].
      exploit Memory.remove_exists_le; try apply REMOVEPROMSRC; eauto.
      intros [mem_src' REMOVEMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      exists Message.reserve, Memory.op_kind_cancel, pasts, prom_src', mem_src'.
      splits; auto.
      + ii. erewrite promised_remove; eauto.
        erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto.
        des_ifs; try by (des; ss; clarify).
        * ss. des; clarify. econs; eauto.
        * specialize (MEM loc ts). inv MEM; eauto.
      + ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs; eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs. ii. eauto.
      + inv PAST. econs.
        * ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs.
          { exploit COMPLETE; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. apply Memory.future_future_weak. auto. }
      + refl.
      + ii. erewrite (@Memory.remove_o mem_src') in GET1; eauto. des_ifs.
        eapply PROMATTACH; eauto.
  Qed.



  Lemma sim_write_step_normal
        others self pasts lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt
        lc_tgt' sc_tgt' mem_tgt' loc from to val ord releasedm_tgt released_tgt kind_tgt
        releasedm_src
        (NLOC: ~ L loc)
        (STEPTGT: Local.write_step lc_tgt sc_tgt mem_tgt loc from to val releasedm_tgt released_tgt ord lc_tgt' sc_tgt' mem_tgt' kind_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self mem_src)
        (* (PROMSWF: forall loc' to', others loc' to' -> L loc') *)
        (CONSISTENT: Local.promise_consistent lc_tgt')

        (RELEASEDMCLOSEDPAST: forall past (PAST: pasts loc from = Some past),
            add_closed_opt_view releasedm_src past loc from)
        (RELEASEDMSOME: forall releasedm_src' (RELEASEDM: releasedm_src = Some releasedm_src'),
            exists past, <<PAST: pasts loc from = Some past>>)
        (RELEASEDMCLOSED: Memory.closed_opt_view releasedm_src mem_src)
        (RELEASEDMLE: View.opt_le releasedm_src releasedm_tgt)
        (RELEASEDMWFSRC: View.opt_wf releasedm_src)
        (RELEASEDMWFTGT: View.opt_wf releasedm_tgt)
    :
      exists pasts' lc_src' sc_src' mem_src' released_src kind_src,
        (<<STEPSRC: Local.write_step lc_src sc_src mem_src loc from to val releasedm_src released_src ord lc_src' sc_src' mem_src' kind_src>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local self pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT. inv WRITE. inv SIM. inv LOCALSRC. inv LOCALTGT.
    generalize (sim_memory_others_self_wf MEM). intros PROMSWF.

    set (msg_src := (Message.concrete val (TView.write_released (Local.tview lc_src) sc_src loc to releasedm_src ord))).
    assert (MSGWF: Message.wf msg_src).
    { unfold msg_src. econs.
      eapply TViewFacts.write_future0; eauto. }

    assert (WRITABLESRC: TView.writable (TView.cur (Local.tview lc_src)) sc_src loc to ord).
    { inv TVIEW. eapply TViewFacts.writable_mon; eauto. refl. }

    assert (RELEASESRC: Ordering.le Ordering.strong_relaxed ord -> Memory.nonsynch_loc loc (Local.promises lc_src)).
    { i. hexploit RELEASE; eauto. intros NONSYNC.
      ii. specialize (PROMS loc t).
      erewrite GET in PROMS. inv PROMS; ss.
      inv MSG; ss. exploit NONSYNC; eauto. ss. }

    assert (MSGLE: Message.le
                     msg_src
                     (Message.concrete val (TView.write_released (Local.tview lc_tgt) sc_tgt loc to releasedm_tgt ord))).
    { unfold msg_src. econs. eapply TViewFacts.write_released_mon; eauto. refl. }

    assert (CONSISTENTTGT:
              forall to' val' released' from'
                     (GET: Memory.get loc to' promises2
                           = Some (from', Message.concrete val' released')),
                Time.le to to').
    { i. exploit CONSISTENT; eauto. i. ss. left. eapply TimeFacts.le_lt_lt; eauto.
      unfold TimeMap.join, TimeMap.singleton. setoid_rewrite LocFun.add_spec_eq.
      eapply Time.join_r; eauto. }

    assert (MSGTO: Memory.message_to msg_src loc to).
    { unfold msg_src. econs. ss.
      transitivity (View.rlx
                      (View.unwrap (TView.write_released (Local.tview lc_tgt) sc_tgt loc to releasedm_tgt ord))
                      loc).
      - exploit TViewFacts.write_released_mon; eauto.
        { refl. } i. apply View.unwrap_opt_le in x0. inv x0. eauto.
      - inv PROMISE; ss; eauto.
        + inv TS. auto.
        + inv TS. auto.
        + inv TS. auto. }

    inv PROMISE.

    (* add case *)
    - exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg_src); ss.
      { i. specialize (MEM loc to2). rewrite GET2 in *. inv MEM; cycle 1.
        { exfalso. apply NLOC. des; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (ATTACHSRC: forall to' msg'
                                (GET: Memory.get loc to' mem_src = Some (to, msg')), False).
      { i. specialize (MEM loc to'). rewrite GET in *. inv MEM; cycle 1.
        { exfalso. des; eauto. }
        inv FROM.
        { exploit DISJOINT; auto.
          - symmetry. eapply H.
          - instantiate (1:=to). econs; ss. refl.
          - econs; ss. eapply memory_get_ts_le; eauto.
        }
        { inv H0. exploit ATTACH; eauto. }
      }

      assert (PROMISESRC: Memory.promise lc_src.(Local.promises) mem_src loc from to msg_src prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { unfold msg_src.
        eapply add_closed_message_add_closed; eauto. econs.
        eapply write_released_add_closed; eauto.
        - eapply closed_add_closed_opt_view; eauto.
        - refl. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      hexploit (@Memory.remove_exists prom_src' loc from to msg_src).
      { eapply Memory.add_get0; eauto. } intros [prom_src'' REMOVESRC].
      hexploit (@MemoryFacts.add_remove_eq (Local.promises lc_src) prom_src' prom_src''); eauto.
      i. subst.
      hexploit (@MemoryFacts.add_remove_eq (Local.promises lc_tgt) promises0 promises2); eauto.
      i. subst.

      eexists (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then (if msg_src then (Some mem_src) else None) else pasts loc' to'), _, _, mem_src', _, _.
      splits; auto.
      + econs; eauto.
      + ii. erewrite promised_add; eauto.
        erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs; eauto.
          { refl. }
          { i. clarify. }
          { i. unfold msg_src. clarify. }
        * specialize (MEM loc ts). inv MEM; eauto.
      + ii. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso. eauto.
      + ii. ss. erewrite (@Memory.add_o mem_src') in GET; eauto. des_ifs.
        * ss. des; clarify. exfalso. eauto.
        * exploit PROMATTACH; eauto.
      + auto.
      + econs; ss.
        * eapply TViewFacts.write_tview_mon; eauto. refl.
        * ii. specialize (PROMS loc0 ts). dup PROMS.
          setoid_rewrite LocFun.add_spec.
          destruct (LocSet.Facts.eq_dec loc0 loc); clarify.
          { destruct (loc_ts_eq_dec (loc, ts) (loc, to)).
            - ss. des; clarify.
              eapply Memory.add_get0 in PROMISES1.
              eapply Memory.add_get0 in ADDPROMSRC. des.
              erewrite GET. erewrite GET1. econs.
              ii. exfalso. eauto.
            - inv PROMS0; econs; eauto.
              i. des_ifs.
              + exfalso. exploit RELEASE; eauto.
                { destruct ord; ss. }
                ss. i. subst. inv MSG.
              + eapply join_view_add_weak_closed; eauto.
                eapply add_weak_closed_view_consistent.
                * eapply add_closed_add_weak_closed_view.
                  eapply singleton_view_add_closed; eauto.
                  inv PAST. exploit ONLY; eauto. i. des; auto.
                * apply View.singleton_ur_wf.
                * ss. unfold TimeMap.singleton.
                  setoid_rewrite LocFun.add_spec_eq. eauto.
          }
          { des_ifs. ss. des; clarify. }
      + inv PAST. econs.
        * ii. erewrite (@Memory.add_o mem_src') in GET; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify. esplits; eauto.
            - eapply write_released_add_closed; eauto; cycle 1.
              { left. eauto. }
              destruct releasedm_src; econs.
              exploit RELEASEDMSOME; eauto. i. des.
              exploit RELEASEDMCLOSEDPAST; eauto. i. inv x.
              exploit ONLY; eauto. i. des.
              eapply add_closed_view_future_add_closed; eauto.
            - i. des_ifs.
              { exfalso. ss. des; clarify. eapply Time.lt_strorder; eauto. }
              guardH o. exploit ONLY; eauto. i. des; auto.
          }
          { guardH o. exploit COMPLETE; eauto. i. des.
            esplits; eauto. des_ifs. ss. des; clarify.
            i. clarify. exfalso. eapply ATTACHSRC; eauto.
          }
        * i. des_ifs.
          { ss. des; clarify. splits; auto.
            - econs. eapply Memory.add_get0; eauto.
            - apply Memory.future_future_weak. auto.
          }
          { guardH o. exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. apply Memory.future_future_weak. auto. }
      + ii. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        inv PAST. apply ONLY in PAST0. des. inv CONCRETE.
        apply Memory.add_get0 in ADDMEMSRC. des. clarify.

    - exploit split_succeed_wf; try apply PROMISES1. i. des. clarify.
      dup PROMS. specialize (PROMS0 loc ts3). erewrite GET2 in PROMS0. inv PAST.

      assert (GETSRC: exists msg3_src,
                 Memory.get loc ts3 (Local.promises lc_src) = Some (from, msg3_src)).
      { inv PROMS0; eauto. exfalso. eauto. } des.

      hexploit (@Memory.split_exists lc_src.(Local.promises) loc from to ts3 msg_src); ss.
      { eauto. }
      intros [prom_src' SPLITPROMSRC].
      exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
      intros [mem_src' SPLITMEMSRC].

      assert (PROMISESRC: Memory.promise lc_src.(Local.promises) mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_split ts3 msg3_src)).
      { econs; eauto. unfold msg_src. eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { unfold msg_src.
        eapply add_closed_message_split_closed; eauto. econs.
        eapply write_released_add_closed; eauto.
        - eapply closed_add_closed_opt_view; eauto.
        - refl. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      hexploit (@Memory.remove_exists prom_src' loc from to msg_src).
      { eapply Memory.split_get0 in SPLITPROMSRC. des. auto. }
      intros [prom_src'' REMOVESRC].

      set (pasts' := fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to)
                                     then
                                       (match msg3_src with
                                        | Message.concrete _ (Some _) => pasts loc ts3
                                        | _ => Some mem_src
                                        end)
                                     else pasts loc' to').

      eexists pasts', _, _, mem_src', _, _.
      splits; auto.
      + econs; eauto.
      + ii. erewrite promised_split; eauto.
        erewrite (@Memory.split_o mem_src'); eauto.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        destruct (loc_ts_eq_dec (loc0, ts) (loc, to)).
        { ss. des; clarify. econs; eauto.
          * refl.
          * i. clarify.
          * unfold msg_src. i. clarify.
        }
        guardH o. destruct (loc_ts_eq_dec (loc0, ts) (loc, ts3)).
        { ss. des; clarify. specialize (MEM loc ts3).
          eapply PROMISES in GETSRC. erewrite GETSRC in *.
          eapply PROMISES0 in GET2. erewrite GET2 in *. inv MEM.
          - econs; eauto.
            + refl.
            + i. clarify.
          - exfalso. des; eauto. }
        { des_ifs. unguard. ss. des; clarify.
          specialize (MEM loc ts). inv MEM; eauto. }
      + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
        * ss. des; clarify. exfalso. eauto.
        * guardH o. ss. des; clarify. exfalso. eauto.
      + ii. erewrite (@Memory.split_o mem_src') in GET; eauto. des_ifs; eauto.
        * ss. des; clarify. exfalso. eauto.
        * guardH o. ss. des; clarify. exfalso. eauto.
      + auto.
      + econs; ss.
        * eapply TViewFacts.write_tview_mon; eauto. refl.
        * ii. dup PROMS. specialize (PROMS1 loc0 ts).
          unfold pasts'. setoid_rewrite LocFun.add_spec.
          erewrite (split_remove_shorten REMOVESRC); eauto.
          erewrite (split_remove_shorten REMOVE); eauto.
          destruct (LocSet.Facts.eq_dec loc0 loc); clarify.
          { specialize (CONSISTENTTGT ts).
            erewrite (split_remove_shorten REMOVE) in CONSISTENTTGT; eauto.
            destruct (loc_ts_eq_dec (loc, ts) (loc, ts3)).
            - ss. des; clarify. erewrite GET2 in PROMS1. erewrite GETSRC in PROMS1.
              inv PROMS1; try (econs; eauto); cycle 1.
              destruct (loc_ts_eq_dec (loc, ts3) (loc, to)).
              { ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
              ss. des; clarify. econs; eauto.
              i. des_ifs.
              + exfalso. exploit RELEASE; eauto.
                { destruct ord; ss. }
                ss. i. subst. inv MSG.
              + eapply join_view_add_weak_closed; eauto.
                eapply add_weak_closed_view_consistent.
                * eapply add_closed_add_weak_closed_view.
                  eapply singleton_view_add_closed; eauto.
                  exploit ONLY; eauto. i. des; auto.
                * apply View.singleton_ur_wf.
                * ss. unfold TimeMap.singleton.
                  setoid_rewrite LocFun.add_spec_eq.
                  exploit CONSISTENTTGT; eauto.
            - ss. des; clarify. inv PROMS1; try (econs; eauto).
              destruct (loc_ts_eq_dec (loc, ts) (loc, to)).
              { ss. des; clarify.
                apply Memory.split_get0 in SPLITPROMSRC. des. erewrite GET in *. clarify. }
              ss. des; clarify. econs; eauto.
              i. subst. des_ifs.
              + exfalso. exploit RELEASE.
                { destruct ord; ss. }
                { symmetry. eapply H2. }
                i. des_ifs. inv MSG.
              + eapply join_view_add_weak_closed; eauto.
                eapply add_weak_closed_view_consistent.
                * eapply add_closed_add_weak_closed_view.
                  eapply singleton_view_add_closed; eauto.
                  exploit ONLY; eauto. i. des; auto.
                * apply View.singleton_ur_wf.
                * ss. unfold TimeMap.singleton.
                  setoid_rewrite LocFun.add_spec_eq.
                  exploit CONSISTENTTGT; eauto.
          }
          { des_ifs; ss; des; clarify. }
      + econs.
        * ii. erewrite (@Memory.split_o mem_src') in GET; eauto.
          unfold pasts'. destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
          { ss. des; clarify.
            destruct (loc_ts_eq_dec (loc, from0) (loc, to)); ss.
            { des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
            guardH o. rewrite GETSRC in *.
            inv PROMS0; clarify; ss; [destruct released_src as [released_src|]|].
            - exploit ONLY; eauto. i. des.
              assert (ORD: Ordering.le Ordering.strong_relaxed ord = false).
              { destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD; ss.
                exfalso. exploit RELEASE; eauto. ss.
                i. inv MSG. ss. }
              exploit COMPLETE.
              { apply PROMISES. eauto. } i. des. rewrite PAST in *. clarify.
              destruct (pasts loc from0) as [past'|] eqn:PAST0.
              + exploit ONLY; eauto. i. des.
                exploit PREV; eauto. i.
                esplits; eauto.
                * eapply write_released_add_closed_relaxed; ss.
                  { inv TVIEW_WF. inv WRITABLE.
                    eapply add_weak_closed_view_consistent; eauto.
                    transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
                    - transitivity (View.rlx (TView.cur (Local.tview lc_src)) loc).
                      + specialize (REL_CUR loc). inv REL_CUR. auto.
                      + inv TVIEW. inv CUR0. auto.
                    - left. auto. }
                  { eapply add_closed_opt_view_future_add_closed; eauto. }
                  { left. auto. }
              + destruct releasedm_src as [releasedm_src|].
                { exploit RELEASEDMSOME; eauto. i. des. clarify. }
                esplits; eauto.
                eapply write_released_add_closed_relaxed; ss.
                  { inv TVIEW_WF. inv WRITABLE.
                    eapply add_weak_closed_view_consistent; eauto.
                    transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
                    - transitivity (View.rlx (TView.cur (Local.tview lc_src)) loc).
                      + specialize (REL_CUR loc). inv REL_CUR. auto.
                      + inv TVIEW. inv CUR0. auto.
                    - left. auto. }
                { econs. }
                { refl. }
            - destruct (pasts loc from0) as [past'|] eqn:PAST.
              + exploit ONLY; eauto. i. des.
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. }
                  exploit RELEASEDMCLOSEDPAST; eauto. i.
                  eapply add_closed_opt_view_future_add_closed; eauto.
                * i. clarify.
              + destruct releasedm_src as [releasedm_src|].
                { exploit RELEASEDMSOME; eauto. i. des. clarify. }
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. } econs.
                * i. clarify.
            - destruct (pasts loc from0) as [past'|] eqn:PAST.
              + exploit ONLY; eauto. i. des.
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. }
                  exploit RELEASEDMCLOSEDPAST; eauto. i.
                  eapply add_closed_opt_view_future_add_closed; eauto.
                * i. clarify.
              + destruct releasedm_src as [releasedm_src|].
                { exploit RELEASEDMSOME; eauto. i. des. clarify. }
                esplits; eauto.
                * eapply write_released_add_closed; eauto; cycle 1.
                  { left. eauto. } econs.
                * i. clarify.
          }
          { guardH o.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            - ss. des; clarify. exploit COMPLETE.
              { eapply PROMISES. eauto. } i. des.
              esplits; eauto. i.
              destruct (loc_ts_eq_dec (loc, from0) (loc, from0)); cycle 1.
              { ss. des; clarify. } des_ifs. refl.
            - guardH o0.
              exploit COMPLETE; eauto. i. des. esplits; eauto.

              i. destruct (loc_ts_eq_dec (loc0, from0) (loc, to)).
              + ss. des; clarify. exfalso.
                exploit memory_get_from_inj.
                { eapply Memory.split_get0 in SPLITMEMSRC. des. eapply GET5. }
                { instantiate (2:=to0). erewrite Memory.split_o; eauto.
                  destruct (loc_ts_eq_dec (loc, to0) (loc, to)).
                  { ss. unguard. des; clarify. }
                  destruct (loc_ts_eq_dec (loc, to0) (loc, ts3)).
                  { simpl in *. unguard. exfalso. guardH o1. des; clarify. }
                  eapply GET. }
                i. des.
                * unguard. des; clarify.
                * clarify. exfalso. eapply Time.lt_strorder; eauto.
                * clarify. exfalso. eapply Time.lt_strorder.
                  eapply TimeFacts.lt_le_lt.
                  { eapply TS12. }
                  { eapply Time.bot_spec; eauto. }
              + guardH o1. eapply PREV; eauto.
          }

        * unfold pasts'. i. des_ifs.
          { ss. des; clarify.
            exploit ONLY; eauto. i. des. splits; auto.
            - eapply Memory.split_get0 in SPLITMEMSRC. des. econs; eauto.
            - etrans; eauto. eapply Memory.future_future_weak; eauto.
          }
          { ss. des; clarify. esplits; eauto.
            - eapply Memory.split_get0 in SPLITMEMSRC. des. econs; eauto.
            - eapply Memory.future_future_weak; eauto.
          }
          { ss. des; clarify. esplits; eauto.
            - eapply Memory.split_get0 in SPLITMEMSRC. des. econs; eauto.
            - eapply Memory.future_future_weak; eauto.
          }
          { guardH o. ss.
            exploit ONLY; eauto. i. des. splits; auto.
            - eapply concrete_promised_increase_promise; eauto.
            - etrans; eauto. eapply Memory.future_future_weak; eauto.
          }

      + unfold pasts'. ii.
        destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); auto.
        ss. des; clarify. exfalso.
        exploit ONLY; eauto. i. des. inv CONCRETE.
        eapply Memory.split_get0 in SPLITMEMSRC. des. clarify.

    - exploit lower_succeed_wf; try apply PROMISES1. i. des. clarify.
      dup PROMS. specialize (PROMS0 loc to). erewrite GET in PROMS0.
      inv PAST. inv PROMS0; clarify; ss. inv MSG_LE.

      exploit COMPLETE; eauto. i. des.
      exploit ONLY; eauto. i. des. rewrite PAST in *. clarify.

      assert (RELEASEDLE:
                View.opt_le
                  (TView.write_released (Local.tview lc_src) sc_src loc to releasedm_src ord)
                  released_src).
      { destruct released_src as [released_src|].
        - eapply sim_opt_view_max; eauto.
          + etrans; eauto.
            eapply TViewFacts.write_released_mon; eauto. refl.
          + eapply write_released_add_closed_relaxed.
            * ss.
            * eapply RELVIEW; eauto.
            * instantiate (1:=from).
              destruct releasedm_src as [releasedm_src|]; [|econs].
              exploit RELEASEDMSOME; eauto. i. des.
              exploit RELEASEDMCLOSEDPAST; eauto. i.
              exploit PREV; eauto. i.
              eapply add_closed_opt_view_future_add_closed; eauto.
            * left. auto.
            * destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD; ss.
              exfalso. exploit RELEASE; eauto. ss. i. clarify. inv MSG.
        - inv MSG. etrans; eauto.
          eapply TViewFacts.write_released_mon; eauto. refl.
      }

      hexploit (@lower_remove_exists lc_src.(Local.promises) loc from to (Message.concrete val0 released_src) msg_src); ss.
      { unfold msg_src. econs; eauto. }
      intros [prom_src' [prom_src'' [LOWERPROMSRC [REMOVEPROMSRC SPEC]]]].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (PROMISESRC: Memory.promise lc_src.(Local.promises) mem_src loc from to msg_src prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val0 released_src))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg_src mem_src').
      { unfold msg_src.
        eapply add_closed_message_lower_closed; eauto. econs.
        eapply write_released_add_closed; eauto.
        - eapply closed_add_closed_opt_view; eauto.
        - refl. }

      assert (FUTURE: Memory.future mem_src mem_src').
      { econs; [|refl]. econs; eauto. }

      eexists pasts, _, _, mem_src', _, _.
      splits; auto.
      + econs; eauto.
      + ss. ii. erewrite promised_lower; eauto; ss.
        erewrite (@Memory.lower_o mem_src'); eauto.
        erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
          { refl. }
          { i. clarify. }
          { unfold msg_src. ii. clarify. }
      + ii. erewrite Memory.lower_o in GET1; eauto. des_ifs; eauto.
        ss. eapply Memory.lower_get0 in LOWERMEMSRC. des. clarify. eauto.
      + ss. ii. des.
        erewrite Memory.lower_o in GET1; eauto. des_ifs.
        * ss. des; clarify. exfalso. eauto.
        * guardH o. exploit PROMATTACH; eauto.
      + eauto.
      + econs; eauto.
        * eapply TViewFacts.write_tview_mon; eauto. refl.
        * ii. ss. dup PROMS. specialize (PROMS0 loc0 ts).
          erewrite SPEC. erewrite (@Memory.remove_o promises2); eauto.
          erewrite (@Memory.lower_o promises0); eauto.
          destruct (loc_ts_eq_dec (loc0, ts) (loc, to)); ss.
          { des; clarify. econs. ii. exfalso. eauto. }
          guardH o.
          setoid_rewrite LocFun.add_spec.
          destruct (LocSet.Facts.eq_dec loc0 loc); eauto. clarify.
          inv PROMS0; econs; eauto. i. clarify. des_ifs.
          { symmetry in H3. exploit RELEASE; try apply H3; eauto.
            { destruct ord; ss. } ss. i. clarify. inv MSG0. }
          { eapply join_view_add_weak_closed; eauto.
            eapply add_weak_closed_view_consistent.
            - eapply add_closed_add_weak_closed_view.
              eapply singleton_view_add_closed; eauto.
              exploit ONLY.
              + symmetry. eapply H1.
              + i. des. auto.
            - apply View.singleton_ur_wf.
            - ss. unfold TimeMap.singleton.
              setoid_rewrite LocFun.add_spec_eq.
              exploit CONSISTENTTGT.
              { instantiate (4:=ts).
                erewrite Memory.remove_o; eauto. erewrite Memory.lower_o; eauto.
                des_ifs.
                - exfalso. ss. unguard. des; clarify.
                - eauto. }
              ss. }
      + econs.
        * ii. erewrite Memory.lower_o in GET1; eauto. des_ifs; eauto.
          ss. des; clarify. exploit COMPLETE; eauto. i. des.
          exploit ONLY; eauto. i. des. clarify.
          destruct released_src as [released_src|].
          { esplits; eauto. eapply write_released_add_closed_relaxed.
            - auto.
            - eauto.
            - instantiate (1:=from0). destruct releasedm_src as [releasedm_src|].
              + exploit RELEASEDMSOME; eauto. i. des.
                exploit ONLY; eauto. i. des.
                eapply add_closed_opt_view_future_add_closed; eauto.
              + econs.
            - left. auto.
            - destruct (Ordering.le Ordering.strong_relaxed ord) eqn:ORD; ss.
              exfalso. exploit RELEASE; eauto. ss. i. clarify.
              clear - ORD RELEASED. destruct ord; ss; inv RELEASED.
          }
          { unfold TView.write_released in RELEASEDLE.
            destruct (Ordering.le Ordering.relaxed ord) eqn:ORD.
            - inv RELEASEDLE.
            - destruct ord; ss. esplits; eauto. }
        * i. exploit ONLY; eauto. i. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. eapply Memory.future_future_weak. econs; eauto. }
      + refl.

    - clarify.
  Qed.

  Lemma sim_thread_step others self pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ self) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self mem_src)
        (PROMSWF: forall loc' to', others loc' to' -> L loc')
        (CONSISTENT: Local.promise_consistent lc_tgt')
    :
      exists tr self' pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self' mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
    inv STEPTGT.
    - inv STEP. destruct (classic (L loc)).
      + admit.
      + inv LOCAL. inv SIM. inv LOCALSRC. inv LOCALTGT.
        exploit sim_promise_step_normal; try apply MEM; eauto.
        { inv TVIEW_WF. eauto. }
        { i. clarify. transitivity (View.rlx (TView.cur (Local.tview lc_tgt)) loc).
          - transitivity (View.rlx (TView.rel (Local.tview lc_tgt) loc) loc).
            + inv TVIEW. specialize (REL loc). inv REL. auto.
            + inv TVIEW_WF0. specialize (REL_CUR loc). inv REL_CUR. auto.
          - exploit CONSISTENT; ss; eauto.
            + eapply Memory.promise_get0 in PROMISE.
              * des. eauto.
              * inv PROMISE; clarify.
            + i. left. auto. }
        { inv TVIEW_CLOSED. eauto. }
        i. des.
        eexists [(_, ThreadEvent.promise loc from to msg_src kind_src)], self, pasts', (Local.mk _ _), _, mem_src'.
        splits; ss.
        * econs 2; [|econs 1|ss]. econs 1. econs; eauto.
        * ss.

    - inv STEP. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], self, pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released_src ord)],
        self, pasts, lc_src', sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + destruct (classic (L loc)).
        * admit.
        * hexploit sim_write_step_normal; try apply MEM; try eassumption.
          { i. instantiate (1:=None). econs. }
          { i. clarify. }
          { econs. }
          { econs. }
          { econs. }
          { econs. } i. des.
          eexists [(_, ThreadEvent.write loc from to val _ ord)], self, pasts', lc_src', _, mem_src'.
          splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + destruct (classic (L loc)).
        * admit.
        * exploit sim_read_step; eauto. i. des.
          dup PAST. inv PAST0. exploit COMPLETE; eauto. i. des.
          exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
          exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.
          hexploit sim_write_step_normal; try apply MEM; try eassumption.
          { i. clarify. }
          { i. eauto. } i. des.
          eexists [(_, ThreadEvent.update loc tsr tsw valr valw released_src released_src0 ordr ordw)],
          self, pasts', lc_src'0, sc_src', mem_src'. splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        self, pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.syscall e)],
        self, pasts, lc_src', sc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_failure_step; eauto. i. des.
        eexists [(_, ThreadEvent.failure)],
        self, pasts, lc_src, sc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
  Admitted.

  Inductive sim_promise_content_strong (loc: Loc.t) (ts: Time.t)
            (P: Prop) (messages: Time.t -> Prop)
            (rel_src: View.t)
    :
      option Memory.t -> option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_strong_none
      (NPROM: ~ P)
      past
    :
      sim_promise_content_strong loc ts P messages rel_src past None None
  | sim_promise_content_strong_normal_concrete
      (NPROM: ~ P)
      (NLOC: ~ L loc)
      past from val released_src released_tgt
      (MSG: sim_opt_view past loc ts released_src released_tgt)
      (RELVIEW: forall released (MSG: released_src = Some released),
          add_weak_closed_view rel_src past loc ts)
    :
      sim_promise_content_strong loc ts P messages rel_src
                                 (Some past)
                                 (Some (from, Message.concrete val released_src))
                                 (Some (from, Message.concrete val released_tgt))
  | sim_promise_content_strong_normal_reserve
      (NPROM: ~ P)
      (NLOC: ~ L loc)
      past from
    :
      sim_promise_content_strong loc ts P messages rel_src
                                 past
                                 (Some (from, Message.reserve))
                                 (Some (from, Message.reserve))
  | sim_promise_content_strong_forget
      (PROM: P)
      (LOC: L loc)
      past from_src from_tgt msg
      (NOTHERS: forall (MSG: messages from_tgt), from_tgt = from_src)
    :
      sim_promise_content_strong loc ts P messages rel_src
                                 past
                                 (Some (from_src, Message.reserve))
                                 (Some (from_tgt, msg))
  .
  Hint Constructors sim_promise_content_strong.

  Lemma sim_promise_content_strong_sim_promise_content
        loc ts P rel past get0 get1 messages
        (SIM: sim_promise_content_strong loc ts P messages rel past get0 get1)
    :
      sim_promise_content loc ts P rel past get0 get1.
  Proof.
    inv SIM; econs; eauto.
  Qed.

  Definition sim_promise_strong
             (self messages: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t): Prop :=
    forall loc ts,
      sim_promise_content_strong loc ts (self loc ts)
                                 (messages loc) (rel_src loc) (pasts loc ts)
                                 (Memory.get loc ts prom_src)
                                 (Memory.get loc ts prom_tgt).

  Lemma sim_promise_strong_sim_promise
        self messages rel_src pasts prom_src prom_tgt
        (SIM: sim_promise_strong self messages rel_src pasts prom_src prom_tgt)
    :
      sim_promise self rel_src pasts prom_src prom_tgt.
  Proof.
    ii. eapply sim_promise_content_strong_sim_promise_content; eauto.
  Qed.

  Definition sim_promise_list (self messages: Loc.t -> Time.t -> Prop)
             (rel_src: LocFun.t View.t)
             (pasts: Loc.t -> Time.t -> option Memory.t)
             (prom_src prom_tgt: Memory.t)
             (l: list (Loc.t * Time.t)): Prop :=
    forall loc ts,
      (<<NORMAL: sim_promise_content_strong loc ts (self loc ts) (messages loc) (rel_src loc) (pasts loc ts)
                                            (Memory.get loc ts prom_src)
                                            (Memory.get loc ts prom_tgt)>>) \/
      ((<<LIN: List.In (loc, ts) l>>) /\
       (<<WEAK: sim_promise_content loc ts (self loc ts) (rel_src loc) (pasts loc ts)
                                    (Memory.get loc ts prom_src)
                                    (Memory.get loc ts prom_tgt)>>)).

  Lemma sim_promise_list_nil self messages rel_src pasts prom_src prom_tgt
        (SIM: sim_promise_list self messages rel_src pasts prom_src prom_tgt [])
    :
      sim_promise_strong self messages rel_src pasts prom_src prom_tgt.
  Proof.
    ii. exploit SIM; eauto. i. des; eauto. ss.
  Qed.

  Lemma sim_promise_weak_list_exists self messages rel_src pasts prom_src prom_tgt
        (SIM: sim_promise self rel_src pasts prom_src prom_tgt)
        (FIN: Memory.finite prom_src)
    :
      exists l,
        (<<SIM: sim_promise_list self messages rel_src pasts prom_src prom_tgt l>>).
  Proof.
    unfold Memory.finite in *. des.
    hexploit (@list_filter_exists
                (Loc.t * Time.t)
                (fun locts =>
                   let (loc, ts) := locts in
                   ~ sim_promise_content_strong loc ts (self loc ts) (messages loc) (rel_src loc) (pasts loc ts)
                     (Memory.get loc ts prom_src)
                     (Memory.get loc ts prom_tgt))
                dom).
    i. des. exists l'.
    ii. destruct (classic (List.In (loc,ts) l')).
    - right. splits; auto.
    - left. specialize (SIM loc ts). red. inv SIM; try by (econs; eauto).
      apply NNPP. ii. exploit FIN; eauto. i.
      hexploit (proj1 (@COMPLETE (loc, ts))); auto.
      splits; auto. ii. rewrite H2 in *. rewrite H3 in *. auto.
  Qed.

  Inductive chained_messages:
    forall (mem: Memory.t) (loc: Loc.t) (ts: Time.t) (l: list (Time.t * Message.t)), Prop :=
  | chained_messages_nil
      mem loc ts
      (EMPTY: forall to msg (GET: Memory.get loc to mem = Some (ts, msg)), False)
    :
      chained_messages mem loc ts []
  | chained_messages_cons
      mem loc ts tl to msg
      (CHAIN: chained_messages mem loc to tl)
      (GET: Memory.get loc to mem = Some (ts, msg))
    :
      chained_messages mem loc ts ((to, msg)::tl)
  .

  Lemma chained_messages_exsists mem loc ts
        (NBOT: Time.lt Time.bot ts)
    :
      exists l, <<CHAIN: chained_messages mem loc ts l>>.
  Proof.
    revert ts NBOT.
    assert (LEMMA: forall
               dom
               (SORTED: times_sorted dom)
               ts
               (NBOT: Time.lt Time.bot ts)
               (COMPLETE: forall
                   to from msg
                   (GET: Memory.get loc to mem = Some (from, msg))
                   (TS: Time.lt ts to), List.In to dom),
               exists l, <<CHAIN: chained_messages mem loc ts l>>).
    { intros dom SORTED. induction SORTED.
      - i. exists []. econs. i. exploit COMPLETE; eauto.
        eapply memory_get_ts_strong in GET.
        des; auto. clarify.
      - i. destruct (Time.le_lt_dec hd ts).
        + exploit IHSORTED; eauto. i. exploit COMPLETE; eauto.
          i. ss. des; auto. clarify.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + destruct (Memory.get loc hd mem) as [[from msg]|] eqn:GET.
          * destruct (Time.eq_dec ts from).
            { clarify. hexploit (IHSORTED hd); eauto.
              { i. exploit COMPLETE; eauto.
                i. ss. des; auto. clarify.
                exfalso. eapply Time.lt_strorder; eauto. }
              { i. des. exists ((hd, msg)::l0). econs; eauto. }
            }
            { exists []. econs. i.
              exploit COMPLETE; eauto.
              { dup GET0. eapply memory_get_ts_strong in GET1. des; clarify. }
              i. ss. des; clarify.
              eapply List.Forall_forall in x; eauto.
              exploit Memory.get_disjoint.
              - eapply GET.
              - eapply GET0.
              - i. des; clarify. eapply x1.
                + instantiate (1:=hd). econs; ss; [|refl].
                  eapply memory_get_ts_strong in GET. des; auto.
                  clarify. transitivity ts; eauto.
                + econs; ss. left. auto.
            }
          * exploit IHSORTED; eauto. i. exploit COMPLETE; eauto.
            i. ss. des; auto. clarify.
    }
    i.
    hexploit (@cell_finite_sound_exists (mem loc)). i. des.
    hexploit (@sorting_sorted dom). i. des.
    exploit LEMMA; eauto. i.
    eapply COMPLETE0. eapply COMPLETE. esplits; eauto.
  Qed.

  Lemma promises_not_attached_replaces self loc ts prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self mem0)
        (SELF: self <2= promised prom0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot ts)
        (PROMISED: self loc ts)
        (* (PROMISED: promised prom0 loc ts) *)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<UNCH01: forall loc' to (TS: loc' = loc -> Time.le to ts),
            (<<MEM: Memory.get loc' to mem1 = Memory.get loc' to mem0>>) /\
            (<<PROM: Memory.get loc' to prom1 = Memory.get loc' to prom0>>)>>) /\

        (<<ATTACH: forall (SELF: self loc ts)
                          to msg (GET: Memory.get loc to mem1 = Some (ts, msg)), False>>) /\
        (* (<<ATTACH: forall to msg (GET: Memory.get loc to mem1 = Some (ts, msg)), False>>) /\ *)

        (<<MLE1: Memory.le prom1 mem1>>) /\

        (<<RESTORE:
           forall prom2 mem2
                  (UNCH12: forall loc' to (TS: loc' = loc -> Time.lt ts to),
                      (<<MEM: Memory.get loc' to mem2 = Memory.get loc' to mem1>>) /\
                      (<<PROM: Memory.get loc' to prom2 = Memory.get loc' to prom1>>))
                  (MLE2: Memory.le prom2 mem2)
           ,
           exists prom3 mem3,
             (<<FUTURE23: reserve_future_memory prom2 mem2 prom3 mem3>>) /\
             (<<UNCHANGED: forall loc' to (TS: loc' = loc -> Time.lt ts to),
                 (<<MEM: Memory.get loc' to mem3 = Memory.get loc' to mem0>>) /\
                 (<<PROM: Memory.get loc' to prom3 = Memory.get loc' to prom0>>)>>) /\
             (<<CHANGED: forall to (TS: Time.le to ts),
                 (<<MEM: Memory.get loc to mem3 = Memory.get loc to mem2>>) /\
                 (<<PROM: Memory.get loc to prom3 = Memory.get loc to prom2>>)>>) /\
             (<<MLE3: Memory.le prom3 mem3>>)
               >>).
  Proof.
    hexploit (@chained_messages_exsists prom0 loc ts); auto. i. des.
    ginduction l; i.
    { exists prom0, mem0. splits; eauto.
      - i. exploit ATTACHED; eauto. i.
        apply SELF in x. inv x. destruct msg0.
        inv CHAIN. dup GET0. eapply MLE0 in GET0. clarify. eauto.
      - i. exists prom2, mem2. splits; auto. }
    inv CHAIN. hexploit LOC; eauto. i. clarify.

    assert (TSTO: Time.lt ts to).
    { eapply memory_get_ts_strong in GET. des; auto. clarify. }

    hexploit (IHl self loc to prom0 mem0); eauto.
    i. des.

    assert (GETPROM1: Memory.get loc to prom1 = Some (ts, Message.reserve)).
    { hexploit (@UNCH01 loc to).
      - i. refl.
      - i. des. erewrite PROM. eapply GET. }
    exploit Memory.remove_exists.
    { eapply GETPROM1. }
    intros [prom1' REMOVEPROM].
    exploit Memory.remove_exists_le; eauto.
    intros [mem1' REMOVEMEM].

    assert (REMOVE: Memory.promise prom1 mem1 loc ts to Message.reserve prom1' mem1' Memory.op_kind_cancel).
    { econs; eauto. }

    exists prom1', mem1'. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. hexploit (@UNCH01 loc' to0).
      { i. etrans; eauto. left. auto. }
      i. des.
      erewrite (@Memory.remove_o mem1'); eauto.
      erewrite (@Memory.remove_o prom1'); eauto. des_ifs.
      ss. des; clarify.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    }
    { i. erewrite Memory.remove_o in GET0; eauto. des_ifs. ss. des; clarify.
      hexploit (@UNCH01 loc to0).
      { i. exploit memory_get_from_inj.
        - eapply MLE1. eapply GETPROM1.
        - eapply GET0.
        - i. des; clarify.
          + exfalso. eapply Time.lt_strorder; eauto.
          + exfalso. eapply Time.lt_strorder; eauto. } i. des.
      erewrite MEM in GET0. eapply MLE0 in GET.
      exploit memory_get_from_inj.
      { eapply GET. }
      { eapply GET0. }
      i. des; clarify.
      { eapply Time.lt_strorder; eauto. }
      { eapply Time.lt_strorder; eauto. }
    }
    { eapply promise_memory_le; eauto. }
    { i. hexploit (@Memory.add_exists mem2 loc ts to Message.reserve).
      { ii. hexploit (@UNCH12 loc to2).
        { i. inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
        i. des. rewrite H in *.
        erewrite (@Memory.remove_o mem1') in GET2; eauto. des_ifs. guardH o.
        exploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply MLE1. eapply GETPROM1. }
        i. des; clarify.
        - ss. unguard. des; clarify.
        - eapply x1; eauto.
      }
      { auto. }
      { econs. }
      intros [mem2' ADDMEM].
      hexploit (Memory.add_exists_le); eauto.
      intros [prom2' ADDPROM].

      assert (ADD: Memory.promise prom2 mem2 loc ts to Message.reserve prom2' mem2' Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      hexploit (RESTORE prom2' mem2').
      { i. erewrite (@Memory.add_o mem2'); eauto.
        erewrite (@Memory.add_o prom2'); eauto.
        hexploit (UNCH12 loc' to0); eauto.
        erewrite (@Memory.remove_o mem1'); eauto.
        erewrite (@Memory.remove_o prom1'); eauto. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
      { eapply promise_memory_le; eauto. }
      i. des.
      exists prom3, mem3. splits; auto.
      { eapply reserve_future_memory_trans; eauto. }

      { i. destruct (classic (loc' = loc -> Time.lt to to0)).
        - exploit UNCHANGED; eauto.
        - apply imply_to_and in H. des. clarify.
          hexploit (CHANGED to0).
          { destruct (Time.le_lt_dec to0 to); auto. exfalso. auto. }
          i. des. rewrite MEM. rewrite PROM.
          erewrite (@Memory.add_o mem2'); eauto.
          erewrite (@Memory.add_o prom2'); eauto. des_ifs.
          + ss. des; clarify. split; auto. symmetry. auto.
          + guardH o. exploit UNCH12; eauto. i. des.
            erewrite x. erewrite x0.
            hexploit (UNCH01 loc to0); eauto.
            { i. destruct (Time.le_lt_dec to0 to); auto. exfalso. auto. }
            i. des. rewrite <- MEM0. rewrite <- PROM0.
            erewrite (@Memory.remove_o mem1'); eauto.
            erewrite (@Memory.remove_o prom1'); eauto. des_ifs.
            ss. unguard. des; clarify.
      }
      { i. hexploit (@CHANGED to0); eauto.
        { etrans; eauto. left. auto. }
        i. des. rewrite MEM. rewrite PROM.
        erewrite (@Memory.add_o mem2'); eauto.
        erewrite (@Memory.add_o prom2'); eauto. des_ifs.
        ss. des; clarify.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
      }
    }
  Qed.

  Lemma promises_not_attached_replace_add self loc from from' to prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self mem0)
        (SELF: self <2= promised prom0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (PROMISED: self loc to)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem1 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.reserve)
            else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom1 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.reserve)
            else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit (@Memory.add_exists mem2 loc from' to Message.reserve); eauto.

    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }
    { econs. }
    intros [mem2' ADDMEM].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to Message.reserve); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM].
    assert (PROMISE1: Memory.promise prom2 mem2 loc from' to Message.reserve prom2' mem2' Memory.op_kind_add).
    { econs; eauto. i. clarify. }
    hexploit (@RESTORE prom2' mem2'); eauto.
    { i. erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.add_o prom2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des. exists prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.add_o prom2' prom2); eauto.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
  Qed.

  Lemma sim_promise_weak_stengthen others self pasts prom_src prom_tgt mem_src mem_tgt rel_src
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONE: Memory.bot_none prom_src)
        (PROM: sim_promise self rel_src pasts prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self mem_src)
        (* (SELF: self <2= promised prom_src) *)
        (EXCLUSIVE: forall loc' ts' (SELF: self loc' ts') (OTHER: others loc' ts'), False)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self mem_src'>>) /\
        (<<PROM: sim_promise_strong
                   self (concrete_promised mem_src' \2/ self)
                   (* (fun loc' ts' => concrete_promise *)
                   (*    concrete_promised prom_src' loc' ts' /\ *)
                   (*    ~ others loc' ts' *)
                   (* ) *)
                   rel_src pasts prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      - refl.
      - eapply sim_promise_list_nil; eauto. }
    i. destruct a as [loc ts].
    dup SIM. specialize (SIM0 loc ts). des.
    { exploit IHl; eauto. ii.
      destruct (loc_ts_eq_dec (loc0, ts0) (loc, ts)).
      - ss. des; clarify. left. auto.
      - specialize (SIM loc0 ts0). ss. des; auto; clarify. }

    clear LIN. inv WEAK.
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H1. rewrite <- H2. econs; eauto. }
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H. rewrite <- H2. rewrite <- H0. econs; eauto. }
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H1. rewrite <- H2. econs; eauto. }
    destruct (classic ((concrete_promised mem_src \2/ self) loc from_tgt)) as [OTHER|NOTHER]; cycle 1.
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H1. rewrite <- H2. econs; eauto. i. clarify. }
    (* destruct (classic (promised prom_src loc from_tgt /\ ~ others loc from_tgt)) as [OTHER|NOTHER]; cycle 1. *)
    (* { exploit IHl; eauto. ii. *)
    (*   specialize (SIM loc0 ts0). ss. des; auto; clarify. *)
    (*   left. rewrite <- H1. rewrite <- H2. econs; eauto. i. clarify. } des. *)
    guardH OTHER.

    symmetry in H1. rename H1 into GETSRC.
    symmetry in H2. rename H2 into GETTGT.
    assert (NBOT: Time.lt Time.bot ts).
    { destruct (Time.le_lt_dec ts Time.bot); auto. destruct l0.
      - exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      - inv H. erewrite BOTNONE in GETSRC. clarify. }

    exploit promises_not_attached_replace_add.
    { eauto. }
    { eauto. }
    { instantiate (1:=prom_src). ii. specialize (SIM x0 x1). des.
      - inv NORMAL; try by (exfalso; eauto). econs; eauto.
      - inv WEAK; try by (exfalso; eauto). econs; eauto. }
    { ii. specialize (SIM loc to). rewrite GET in SIM. des.
      - inv NORMAL; clarify.
      - inv WEAK; clarify. }
    { eauto. }
    { eapply NBOT. }
    { eauto. }
    { eauto. }
    { instantiate (1:=from_tgt).
      eapply memory_get_ts_strong in GETTGT. des; clarify. }
    { ii. inv H. specialize (MEM loc to). rewrite GET in MEM.
      inv MEM; clarify.
      - exploit Memory.get_disjoint.
        { symmetry. apply H. }
        { eapply MLETGT. eapply GETTGT. }
        i. des; clarify.
        + eapply MLESRC in GETSRC. clarify.
          inv ITV. inv ITV0. ss. clear - TO FROM1.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + eapply x0.
          * instantiate (1:=ts0). econs; ss.
            { inv ITV0. eapply TimeFacts.le_lt_lt; eauto. }
            { inv ITV0. ss. }
          * inv ITV. econs; ss. etrans; eauto.
            eapply memory_get_ts_le; eauto.
      - guardH PROM0. exploit Memory.get_disjoint.
        { symmetry. apply H. }
        { eapply MLETGT. eapply GETTGT. }
        i. des; clarify.
        + eapply MLESRC in GETSRC. clarify.
          inv ITV. inv ITV0. ss. clear - TO FROM1.
          eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
        + eapply x0.
          * instantiate (1:=ts0). econs; ss.
            { inv ITV0. eapply TimeFacts.le_lt_lt; eauto. }
            { inv ITV0. ss. }
          * inv ITV. econs; ss. etrans; eauto.
            eapply memory_get_ts_le; eauto.
    }
    i. des.
    assert (PROMISEDSAME: promised prom1 = promised prom_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite PROMSPEC in GET. des_ifs.
        + ss. des; clarify. econs; eauto.
        + econs; eauto.
      - inv H. specialize (PROMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. econs; eauto.
        + erewrite <- PROMSPEC in *. econs; eauto. }
    assert (CONCRETESAME: concrete_promised mem1 = concrete_promised mem_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite MEMSPEC in GET. des_ifs. econs; eauto.
      - inv H. specialize (MEMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. apply MLESRC in GETSRC. clarify.
        + erewrite <- MEMSPEC in *. econs; eauto. }

    assert (PROMISEDSAMEMEM: promised mem1 = promised mem_src).
    { extensionality loc'. extensionality ts'.
      apply Coq.Logic.PropExtensionality.propositional_extensionality.
      split; i.
      - inv H. erewrite MEMSPEC in GET. des_ifs.
        + ss. des; clarify. econs; eauto.
        + econs; eauto.
      - inv H. specialize (MEMSPEC loc' ts'). des_ifs.
        + ss. des; clarify. econs; eauto.
        + erewrite <- MEMSPEC in *. econs; eauto. }

    hexploit (@IHl others self pasts prom1 prom_tgt mem1 mem_tgt rel_src); eauto.
    { ii. rewrite PROMISEDSAMEMEM.
      dup MEM. specialize (MEM0 loc0 ts0). erewrite MEMSPEC. des_ifs.
      - ss. des; clarify. apply MLETGT in GETTGT. rewrite GETTGT. econs 3; eauto.
        + refl.
        + i. exfalso. eapply H. unguard. des.
          * inv OTHER. econs; eauto.
          * specialize (MEM loc from_tgt). inv MEM; try by (exfalso; eauto).
            econs; eauto. }
    { eapply reserve_future_memory_le; eauto. }
    { eapply reserve_future_memory_finite; eauto. }
    { eapply reserve_future_memory_bot_none; eauto. }
    { ii. rewrite MEMSPEC in GET. des_ifs.
      - ss. des; clarify.
      - exploit PROMATTACH; eauto. }
    { ii. erewrite PROMSPEC. des_ifs.
      - left. ss. des. clarify. erewrite GETTGT. econs 4; eauto.
      - guardH o. specialize (SIM loc0 ts0).
        ss. des; eauto.
        + left. red. inv NORMAL; eauto. econs 4; eauto.
          rewrite CONCRETESAME. auto.
        + unguard. des; clarify. }
    i. des. exists prom_src', mem_src'. splits; auto.
    - eapply reserve_future_memory_trans; eauto.
    - etrans; eauto. ii.
      erewrite MEMSPEC in GET. des_ifs.
      + ss. des; clarify. exfalso.
        specialize (MEM loc from). unguard. des.
        * inv OTHER. erewrite GET in MEM. inv MEM. eauto.
        * eauto.
      + eauto.
  Qed.

  Lemma promises_not_attached_replace_write self loc from from' to prom0 mem0 val released
        (LIN: L loc)
        (ATTACHED: promises_not_attached self mem0)
        (SELF: self <2= promised prom0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (PROMISED: self loc to)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
        (VIEWWF: View.opt_wf released)
        (MSGTO: Time.le (View.rlx (View.unwrap released) loc) to)
    :
      exists prom1 mem1 prom2 mem2 prom3 mem3,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<WRITE: Memory.write prom1 mem1 loc from' to val released prom2 mem2 Memory.op_kind_add>>) /\
        (<<FUTURE23: reserve_future_memory prom2 mem2 prom3 mem3>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem3 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then Some (from', Message.concrete val released)
            else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom3 =
            if loc_ts_eq_dec (loc', ts') (loc, to)
            then None
            else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit (@Memory.add_exists mem2 loc from' to (Message.concrete val released)); eauto.

    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }
    { econs; eauto. }
    intros [mem2' ADDMEM].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to (Message.concrete val released)); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM].

    assert (PROMISE1: Memory.write prom2 mem2 loc from' to val released prom2 mem2' Memory.op_kind_add).
    { econs; eauto.
      - econs; eauto. i.
        erewrite (@Memory.remove_o mem2) in GET0; eauto.
        des_ifs. eauto.
      - exploit Memory.remove_exists.
        { eapply Memory.add_get0 in ADDPROM. des. eapply GET1. }
        i. des.
        exploit MemoryFacts.add_remove_eq; eauto. i. subst. auto.
    }

    hexploit (@RESTORE prom2 mem2'); eauto.
    { i. erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto. }
    { eapply write_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des.
    exists prom2, mem2, prom2, mem2', prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs. guardH o. hexploit (@UNCH01 loc ts'); eauto.
        { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des; clarify.
    }
  Qed.


  Lemma promises_not_attached_replace_split self loc from from' to' to prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self mem0)
        (SELF: self <2= promised prom0)
        (PROMISED: self loc to)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (GET: Memory.get loc to prom0 = Some (from, Message.reserve))
        (FROM: Time.lt from' to')
        (TO: Time.lt to' to)
        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem0)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<MEMSPEC: forall loc' ts',
            Memory.get loc' ts' mem1 =
            if loc_ts_eq_dec (loc', ts') (loc, to')
            then Some (from', Message.reserve)
            else if loc_ts_eq_dec (loc', ts') (loc, to)
                 then Some (to', Message.reserve)
                 else Memory.get loc' ts' mem0>>) /\
        (<<PROMSPEC: forall loc' ts',
            Memory.get loc' ts' prom1 =
            if loc_ts_eq_dec (loc', ts') (loc, to')
            then Some (from', Message.reserve)
            else if loc_ts_eq_dec (loc', ts') (loc, to)
                 then Some (to', Message.reserve)
                 else Memory.get loc' ts' prom0>>).
  Proof.
    hexploit promises_not_attached_replaces; eauto.
    i. des.
    hexploit (@Memory.remove_exists prom1 loc from to Message.reserve).
    { hexploit (@UNCH01 loc to); eauto.
      { i. refl. }
      i. des. erewrite PROM. eauto. }
    intros [prom2 REMOVEPROM].
    hexploit Memory.remove_exists_le; eauto.
    intros [mem2 REMOVEMEM].
    assert (PROMISE0: Memory.promise prom1 mem1 loc from to Message.reserve prom2 mem2 Memory.op_kind_cancel).
    { econs; eauto. }
    assert (DISJOINT: forall (to2 from2 : Time.t) (msg2 : Message.t)
                             (GET2: Memory.get loc to2 mem2 = Some (from2, msg2)),
               Interval.disjoint (from', to) (from2, to2)).
    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
      hexploit (@Memory.get_disjoint loc from2 from to2 to).
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      i. ss. unguard. des; clarify.
      eapply H; eauto. inv LHS. econs; ss.
      destruct (Time.le_lt_dec x from); auto. exfalso.
      hexploit memory_get_to_mon.
      { eapply GET2. }
      { hexploit (@UNCH01 loc to).
        { i. refl. }
        i. des. rewrite MEM. eauto. }
      { inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
      i. hexploit (@UNCH01 loc to2).
      { i. left. auto. }
      i. des. erewrite MEM in *. eapply (EMPTY x).
      { econs; ss. }
      { econs; eauto. }
    }

    hexploit (@Memory.add_exists mem2 loc from' to' Message.reserve); eauto.
    { ii. eapply DISJOINT; eauto. inv LHS. econs; ss.
      etrans; eauto. left. auto. }
    { econs. }
    intros [mem2' ADDMEM0].
    hexploit (@Memory.add_exists_le prom2 mem2 loc from' to' Message.reserve); eauto.
    { eapply promise_memory_le; eauto. }
    intros [prom2' ADDPROM0].
    assert (PROMISE1: Memory.promise prom2 mem2 loc from' to' Message.reserve prom2' mem2' Memory.op_kind_add).
    { econs; eauto. i. clarify. }

    hexploit (@Memory.add_exists mem2' loc to' to Message.reserve); eauto.
    { ii. erewrite Memory.add_o in GET2; eauto. des_ifs.
      - ss. des; clarify. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
      - guardH o. eapply DISJOINT; eauto. inv LHS. econs; ss.
        etrans; eauto. }
    { econs. }
    intros [mem2'' ADDMEM1].
    hexploit (@Memory.add_exists_le prom2' mem2' loc to' to Message.reserve); eauto.
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    intros [prom2'' ADDPROM1].

    assert (PROMISE2: Memory.promise prom2' mem2' loc to' to Message.reserve prom2'' mem2'' Memory.op_kind_add).
    { econs; eauto. i. clarify. }
    hexploit (@RESTORE prom2'' mem2''); eauto.
    { i. erewrite (@Memory.add_o mem2''); eauto.
      erewrite (@Memory.add_o prom2''); eauto.
      erewrite (@Memory.add_o mem2'); eauto.
      erewrite (@Memory.add_o prom2'); eauto.
      erewrite (@Memory.remove_o mem2); eauto.
      erewrite (@Memory.remove_o prom2); eauto. des_ifs.
      - ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - guardH o. ss. des; clarify. exfalso.
        eapply Time.lt_strorder. etrans; eauto.
    }
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    i. des. exists prom3, mem3. splits; auto.
    { eapply reserve_future_memory_trans; eauto. }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite MEM. des_ifs.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite MEM.
        erewrite (@Memory.add_o mem2'' mem2'); eauto.
        erewrite (@Memory.add_o mem2' mem2); eauto.
        erewrite (@Memory.remove_o mem2 mem1); eauto.
        des_ifs.
        + ss. des; clarify.
        + guardH o. guardH o0. hexploit (@UNCH01 loc ts'); eauto.
          { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
          i. des; clarify.
    }
    { i. destruct (classic (loc' = loc -> Time.lt to ts')).
      - hexploit UNCHANGED; eauto. i. des. rewrite PROM. des_ifs.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
        + ss. des; clarify. exfalso. eapply Time.lt_strorder; eauto.
      - apply imply_to_and in H. des. clarify.
        hexploit (@CHANGED ts'); eauto.
        { destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
        i. des. rewrite PROM.
        erewrite (@Memory.add_o prom2'' prom2'); eauto.
        erewrite (@Memory.add_o prom2' prom2); eauto.
        erewrite (@Memory.remove_o prom2 prom1); eauto.
        des_ifs.
        + ss. des; clarify.
        + guardH o. hexploit (@UNCH01 loc ts'); eauto.
          { i. destruct (Time.le_lt_dec ts' to); eauto. exfalso. auto. }
          i. des; clarify.
    }
  Qed.

  Lemma sim_promise_step_forget others self pasts mem_src mem_tgt rel_src prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (LOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELWF: View.wf (rel_src loc))
        (RELSRC: Memory.closed_view (rel_src loc) mem_src)
        (PROMISE: sim_promise self rel_src pasts prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached self mem_src)
        (EXCLUSIVE: forall loc' ts' (SELF: self loc' ts') (OTHER: others loc' ts'), False)
    :
      exists prom_src' mem_src' self',
        (<<STEPSRC: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self' rel_src pasts prom_src' prom_tgt'>>) /\
        (<<PROMATTACH: promises_not_attached self' mem_src'>>) /\
        (<<EXCLUSIVSE: forall loc' ts' (SELF: self' loc' ts') (OTHER: others loc' ts'), False>>)
  .
  Proof.
    inv STEPTGT.

    - hexploit add_succeed_wf; try apply MEM0. i. des.

      assert (DISJOINTSRC:
                forall to2 from2 msg2
                       (GET2: Memory.get loc to2 mem_src = Some (from2, msg2)),
                  Interval.disjoint (Time.middle from to, to) (from2, to2)).
      { ii. specialize (MEM loc to2). inv MEM.
        - rewrite GET2 in *. clarify.
        - rewrite GET2 in *. clarify. eapply DISJOINT; eauto.
          + instantiate (1:=x). inv LHS. econs; ss.
            transitivity (Time.middle from to); auto.
            eapply Time.middle_spec; auto.
          + inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto.
        - rewrite GET2 in *. clarify. eapply DISJOINT; eauto.
          + instantiate (1:=x). inv LHS. econs; ss.
            transitivity (Time.middle from to); auto.
            eapply Time.middle_spec; auto.
          + inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      hexploit (@Memory.add_exists mem_src loc (Time.middle from to) to Message.reserve).
      { auto. }
      { eapply Time.middle_spec; auto. }
      { econs. }
      intros [mem_src' ADDMEM].
      hexploit (@Memory.add_exists_le prom_src mem_src loc (Time.middle from to) to Message.reserve); eauto.
      intros [prom_src' ADDPROM].
      assert (PROMISESRC: Memory.promise prom_src mem_src loc (Time.middle from to) to Message.reserve prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. i. clarify. }
      assert (FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src').
      { eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts').
      splits; auto.
      + ii. erewrite promised_add; eauto.
        erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs 3; eauto.
          { left. eapply Time.middle_spec; eauto. }
          { i. eapply Time.middle_spec; eauto. }
        * ss. des; clarify.
          dup MEM. specialize (MEM1 loc ts). inv MEM1; eauto.
          { econs 2; eauto. i. des_ifs.
            - eapply SHORT; eauto. }
          { econs 3; eauto. i. des_ifs.
            - eapply SHORT; eauto. }
      + ii. erewrite Memory.add_o in GET; eauto. des_ifs; eauto.
        ss. des; clarify. exfalso.
        specialize (MEM loc (Time.middle from to)). inv MEM.
        { eapply NPROM; auto. }
        { eapply NPROM; auto. }
        { guardH PROM. exploit Memory.get_disjoint.
          { eapply Memory.add_get1; try apply MEM0. symmetry. eapply H. }
          { eapply Memory.add_get0; eauto. }
          i. des.
          - subst. eapply Time.lt_strorder.
            instantiate (1:=to). rewrite <- x0 at 1.
            eapply Time.middle_spec. auto.
          - eapply x0.
            + instantiate (1:=Time.middle from to). econs; ss.
              * symmetry in H. eapply memory_get_ts_strong in H. des; auto.
                subst. eapply TimeFacts.le_lt_lt.
                { eapply Time.bot_spec. }
                { eapply Time.middle_spec in TO1. des. eauto. }
              * refl.
            + econs; ss.
              * eapply Time.middle_spec; eauto.
              * left. eapply Time.middle_spec; eauto.
        }
      + ii. erewrite (@Memory.add_o prom_src'); eauto.
        erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs 4; eauto.
      + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
        * ss. des; clarify.
          specialize (MEM loc ts1). rewrite GET in *. inv MEM.
          { assert (FROMTO: Time.lt from_tgt to).
            { destruct (Time.le_lt_dec to from_tgt); auto.
              exploit SHORT; eauto.
              { ii. inv H0. destruct msg0. exploit DISJOINTSRC; eauto.
                - instantiate (1:=to). econs; ss.
                  + eapply Time.middle_spec; eauto.
                  + refl.
                - econs; ss.
                  + apply memory_get_ts_strong in GET0. des; clarify.
                    * eapply (@TimeFacts.le_lt_lt _ from); eauto.
                      eapply Time.bot_spec.
                    * eapply TimeFacts.lt_le_lt; eauto. }
            }
            exfalso. eapply DISJOINT.
            { symmetry. eapply H. }
            { instantiate (1:=to). econs; ss. refl. }
            { econs; ss. eapply memory_get_ts_le; eauto. }
          }
          { guardH PROM. assert (FROMTO: Time.lt from_tgt to).
            { destruct (Time.le_lt_dec to from_tgt); auto.
              exploit SHORT; eauto.
              { ii. inv H0. destruct msg. exploit DISJOINTSRC; eauto.
                - instantiate (1:=to). econs; ss.
                  + eapply Time.middle_spec; eauto.
                  + refl.
                - econs; ss.
                  + apply memory_get_ts_strong in GET0. des; clarify.
                    * eapply (@TimeFacts.le_lt_lt _ from); eauto.
                      eapply Time.bot_spec.
                    * eapply TimeFacts.lt_le_lt; eauto. }
            }
            exfalso. eapply DISJOINT.
            { symmetry. eapply H. }
            { instantiate (1:=to). econs; ss. refl. }
            { econs; ss. eapply memory_get_ts_le; eauto. }
          }
        * exploit PROMATTACH; eauto.
      + i. des_ifs; eauto. ss. des; clarify.
        specialize (MEM loc to). inv MEM; eauto. guardH PROM.
        eapply Memory.add_get0 in ADDMEM. des. rewrite GET in *. clarify.

    - des. clarify.
      exploit split_succeed_wf; try apply PROMISES. i. des.
      dup GET2. apply WFTGT in GET0.
      dup PROMISE. specialize (PROMISE0 loc ts3).
      rewrite GET2 in PROMISE0. inv PROMISE0; clarify.
      rename H1 into GETSRC. symmetry in GETSRC.

      exploit (@promises_not_attached_replace_split self loc from_src (Time.middle from to) to ts3 prom_src mem_src); auto.
      { i. specialize (PROMISE x0 x1). inv PROMISE; clarify. econs; eauto. }
      { i. specialize (PROMISE loc to0). rewrite GET in *. inv PROMISE; clarify. }
      { eapply (@TimeFacts.le_lt_lt _ from); eauto. eapply Time.bot_spec. }
      { eapply Time.middle_spec; eauto. }
      { ii. inv H.
        dup MEM. specialize (MEM loc to0). rewrite GET in MEM. inv MEM.
        - exploit Memory.get_disjoint.
          { symmetry. eapply H. }
          { eapply GET0. }
          i. des; clarify.
          { apply WFSRC in GETSRC. clarify.
            inv ITV. inv ITV0. ss.
            eapply Time.lt_strorder. eapply (TimeFacts.le_lt_lt TO FROM1); eauto. }
          exploit memory_get_from_mon.
          { eapply GET. }
          { apply WFSRC. eapply GETSRC. }
          { inv ITV0. ss.
            admit. }
          admit.
        - admit.
      }

      intros [prom_src' [mem_src' ?]]. des.

      assert (PROMISEDSAMEMEM: concrete_promised mem_src' = concrete_promised mem_src).
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H. erewrite MEMSPEC in GET. des_ifs. econs; eauto.
        - inv H. specialize (MEMSPEC loc' ts'). des_ifs.
          + ss. des; clarify.
            specialize (MEM loc to). rewrite GET in MEM.
            eapply Memory.split_get0 in MEM0. des.
            rewrite GET1 in MEM. inv MEM.
          + ss. des; clarify.
            apply WFSRC in GETSRC. clarify.
          + erewrite <- MEMSPEC in *. econs; eauto. }

      assert (PROMISEDDIFF: promised mem_src' =
                            fun loc' =>
                              if (Loc.eq_dec loc' loc)
                              then fun ts' => if (Time.eq_dec ts' to) then True else promised mem_src loc' ts'
                              else promised mem_src loc').
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H. erewrite MEMSPEC in GET. des_ifs; try by (ss; des; clarify).
          + ss. des; clarify. econs; eauto.
          + ss. des; clarify. econs; eauto.
          + econs; eauto.
        - specialize (MEMSPEC loc' ts'). des_ifs; try by (ss; des; clarify).
          + econs; eauto.
          + econs; eauto.
          + inv H. erewrite <- MEMSPEC in *. econs; eauto.
          + inv H. erewrite <- MEMSPEC in *. econs; eauto. }

      (* assert (PROMISEDSAMEMEM: concrete_promised mem_src' = concrete_promised mem_src). *)
      (* { extensionality loc'. extensionality ts'. *)
      (*   apply Coq.Logic.PropExtensionality.propositional_extensionality. *)
      (*   split; i. *)
      (*   - inv H. erewrite MEMSPEC in GET. des_ifs. econs; eauto. *)
      (*   - inv H. specialize (MEMSPEC loc' ts'). des_ifs. *)
      (*     + ss. des; clarify. *)
      (*       specialize (MEM loc to). rewrite GET in MEM. *)
      (*       eapply Memory.split_get0 in MEM0. des. *)
      (*       rewrite GET1 in MEM. inv MEM. *)
      (*     + ss. des; clarify. *)
      (*       apply WFSRC in GETSRC. clarify. *)
      (*     + erewrite <- MEMSPEC in *. econs; eauto. } *)

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'). splits; auto.
      + ii. erewrite PROMISEDDIFF.
        erewrite MEMSPEC.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs 3; eauto.
          { left. apply Time.middle_spec; eauto. }
          { ii. apply Time.middle_spec; eauto. }
        * guardH o. ss. des; clarify. econs 3; eauto.
          { refl. }
          { ii. des_ifs. }
        * guardH o. guardH o0.
          specialize (MEM loc ts). inv MEM; eauto.
          { econs 2; eauto. i. des_ifs. apply SHORT; eauto. }
          { econs 3; eauto. i. des_ifs. apply SHORT; eauto. }
      + ii. erewrite MEMSPEC in GET. des_ifs.
        * ss. des; clarify. admit.
        * ss. des; clarify. admit.
        * eauto.
      + ii. erewrite PROMSPEC.
        erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. econs; eauto.
      + ii. erewrite MEMSPEC in GET. des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. admit.
        * eauto.
      + i. des_ifs; eauto. ss. des; clarify. admit.

    - dup PROMISES. apply Memory.lower_get0 in PROMISES0. des. clarify.
      dup GET. apply WFTGT in GET1.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; clarify.
      exists prom_src, mem_src, self. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify.
        specialize (MEM loc to). rewrite GET1 in *. inv MEM; eauto.
        { exfalso. eapply NPROM. auto. }
      + ii. eauto.
      + ii. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. inv MSG_LE. rewrite <- H1. econs 4; eauto.

    - hexploit Memory.remove_get0; try apply PROMISES. i. des.
      dup GET. apply WFTGT in GET1.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; clarify.

      hexploit (@Memory.remove_exists prom_src loc from_src to Message.reserve).
      { auto. }
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src loc from_src to Message.reserve); eauto.
      intros [mem_src' REMOVEMEM].
      assert (PROMISESRC: Memory.promise prom_src mem_src loc from_src to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      assert (FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src').
      { eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then False else self loc' ts').
      splits; auto.

      + ii. erewrite promised_remove; eauto.
        erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto. des_ifs; try by ss; des; clarify.
        * ss. des; clarify. econs. ii. des; auto.
          specialize (MEM loc to). inv MEM; eauto.
        * ss. des; clarify.
          specialize (MEM loc ts). inv MEM; eauto.
          { econs 2; eauto. ii. destruct FROM; auto. des_ifs; eauto.
            inv H4. eapply SHORT; eauto. }
          { econs 3; eauto. ii. destruct FROM; auto. des_ifs; eauto.
            inv H3. exploit PROMATTACH; eauto. i.

            eapply SHORT; eauto. ii. inv H3. destruct msg0.


            eauto.
            eapply SHORT; eauto.

            inv H4. eapply SHORT; eauto. }

            ii. inv H4. destruct msg. des_ifs. exploit PROMATTACH.
            - eapply PROM.
            -eapply GET2.

            des_ifs.


            admit. }
          { econs 3; eauto. i


      + ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs. ss.
      + ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto.
      + i. des_ifs. eauto.
  Qed.

  Definition aaa := 1 = true.

  Lemma sim_thread_step others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (others \2/ (in_L /2\ promised lc_src.(Local.promises))) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (others \2/ (in_L /2\ promised lc_src.(Local.promises))) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local others pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (PROMATTACH: promises_not_attached (promised lc_src.(Local.promises)) mem_src)
        (OTHERSWF: forall loc' to', others loc' to' -> L loc')
        (CONSISTENT: Local.promise_consistent lc_tgt')
    :
      exists tr pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ (in_L /2\ promised lc_src'.(Local.promises))) mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local others pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)



  Lemma split_reserve_exists prom1 mem1 loc ts1 ts2 ts3
        (MLE: Memory.le prom1 mem1)
        (GET: Memory.get loc ts3 prom1 = Some (ts1, Message.reserve))
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.lt ts2 ts3)
    :
      exists prom2 mem2,
        (<<FUTURE: reserve_future_memory prom1 mem1 prom2 mem2>>) /\
        (<<SPLITMEM:
           forall l t,
             Memory.get l t mem2 =
             (if loc_ts_eq_dec (l, t) (loc, ts2)
              then Some (ts1, Message.reserve)
              else
                if loc_ts_eq_dec (l, t) (loc, ts3)
                then Some (ts2, Message.reserve)
                else Memory.get l t mem1)>>) /\
        (<<SPLITPROM:
           forall l t,
             Memory.get l t prom2 =
             (if loc_ts_eq_dec (l, t) (loc, ts2)
              then Some (ts1, Message.reserve)
              else
                if loc_ts_eq_dec (l, t) (loc, ts3)
                then Some (ts2, Message.reserve)
                else Memory.get l t prom1)>>)
  .
  Proof.
    exploit Memory.remove_exists.
    { apply GET. } intros [prom_mid0 PROM0].
    exploit Memory.remove_exists_le; eauto. intros [mem_mid0 MEM0].
    assert (STEP0: Memory.promise prom1 mem1 loc ts1 ts3 Message.reserve prom_mid0 mem_mid0 Memory.op_kind_cancel).
    { econs; eauto. }
    hexploit promise_memory_le; eauto. intros MLE0.
    exploit (@Memory.add_exists mem_mid0 loc ts2 ts3 Message.reserve).
    { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. ss. guardH o.
      exploit Memory.get_disjoint.
      - apply MLE. apply GET.
      - apply GET2.
      - i. des; clarify.
        + unguard. des; auto.
        + eapply x1; eauto. inv LHS. econs; eauto. }
    { auto. }
    { econs. } intros [mem_mid1 MEM1].
    exploit Memory.add_exists_le; eauto. intros [prom_mid1 PROM11].
    assert (STEP1: Memory.promise prom_mid0 mem_mid0 loc ts2 ts3 Message.reserve prom_mid1 mem_mid1 Memory.op_kind_add).
    { econs; eauto. i. clarify.
    }
    hexploit promise_memory_le; eauto. intros MLE1.
    exploit (@Memory.add_exists mem_mid1 loc ts1 ts2 Message.reserve).
    { ii. erewrite Memory.add_o in GET2; eauto. des_ifs.
      { ss. des; clarify. inv LHS. inv RHS. ss.
        eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
        - apply TO.
        - apply FROM0.
      } ss. guardH o.
      erewrite Memory.remove_o in GET2; eauto. des_ifs. ss. guardH o0.
      exploit Memory.get_disjoint.
      - apply MLE. apply GET.
      - apply GET2.
      - i. des; clarify.
        + unguard. des; auto.
        + eapply x1; eauto. inv LHS. econs; eauto. etrans; eauto. left. auto.
    }
    { auto. }
    { econs. } intros [mem2 MEM2].
    exploit Memory.add_exists_le; eauto. intros [prom2 PROM2].
    assert (STEP2: Memory.promise prom_mid1 mem_mid1 loc ts1 ts2 Message.reserve prom2 mem2 Memory.op_kind_add).
    { econs; eauto. i. clarify.
    }
    assert (NEQ23: ts2 <> ts3).
    { ii. clarify. eapply Time.lt_strorder. eauto. }
    exists prom2, mem2. splits.
    - eauto.
    - i. erewrite (@Memory.add_o mem2 mem_mid1); eauto.
      erewrite (@Memory.add_o mem_mid1 mem_mid0); eauto. erewrite (@Memory.remove_o mem_mid0 mem1); eauto.
      des_ifs.
    - i. erewrite (@Memory.add_o prom2 prom_mid1); eauto.
      erewrite (@Memory.add_o prom_mid1 prom_mid0); eauto. erewrite (@Memory.remove_o prom_mid0 prom1); eauto.
      des_ifs.
  Admitted.

  Lemma sim_promise_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt' kind
        (NLOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists prom_self' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts>>)
  .
  Proof.
    inv PROMISE. inv MEM. dup STEPTGT. inv STEPTGT.
    - dup MEM. apply add_succeed_wf in MEM0. des.
      exploit Memory.add_exists; try apply TO1.
      { instantiate (1:=mem_src). instantiate (1:=loc). ii.
        exploit COVERED.
        { econs; eauto. } i. inv x0.
        eapply DISJOINT; eauto. }
      { eapply Message.wf_reserve. } i. des.
      exploit Memory.add_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src promises2 mem2).
      { econs.
        - econs 1; eauto. i. clarify.
        - econs 1. }
      destruct msg.
      { exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), promises2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.add_o in GETTGT; eauto. erewrite Memory.add_o; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite add_covered in COVERED0; eauto.
            eapply add_covered; eauto. des; auto.
        + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
          ss. des; clarify; try by (eapply ATTACH; eauto).
          exploit ATTACH0; eauto.
          admit. (* change it *)
        + econs.
          * i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { des; clarify. exfalso. auto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; try eassumption.
            des_ifs; clarify; eauto.
          * i. erewrite (@Memory.add_o promises2 prom_src); eauto.
            erewrite (@Memory.add_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exploit FORGET; eauto. des; clarify. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }
      { exists prom_self, promises2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.add_o in GETTGT; eauto. erewrite Memory.add_o; eauto.
            des_ifs; ss.
            exploit COMPLETE0; eauto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite add_covered in COVERED0; eauto.
            eapply add_covered; eauto. des; auto.
        + ii. erewrite Memory.add_o in GET; eauto. des_ifs.
          ss. des; clarify; try by (eapply ATTACH; eauto).
        + econs.
          * i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify; eauto.
          * i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; try eassumption.
            des_ifs; clarify; eauto.
          * i. erewrite (@Memory.add_o promises2 prom_src); eauto.
            erewrite (@Memory.add_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
            ss. des; clarify. exploit FORGET; eauto. i. des.
            eapply Memory.add_get0 in PROMISES. des. clarify.
        + eapply reserve_future_wf_pasts_memory; eauto.
      }

    - dup PROMISES. apply split_succeed_wf in PROMISES0. des. clarify.
      destruct (classic (prom_self loc ts3)) as [PROM|NPROM].
      { exploit FORGET; eauto. i. des. clarify.
        exploit split_reserve_exists; try apply GETSRC; eauto. i. des.
        exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), prom2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.split_o in GETTGT0; eauto. erewrite SPLITMEM; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite split_covered; cycle 1; eauto. apply COVERED.
            inv COVERED0. rewrite SPLITMEM in GET. des_ifs; des; ss; clarify; econs; eauto.
            { inv ITV. econs; eauto. ss. etrans; eauto. left. auto. }
            { inv ITV. econs; eauto. }
        + ii. erewrite SPLITMEM in GET. des_ifs. guardH o. guardH o0.
          ss. exploit ATTACH; cycle 1; eauto. des; auto. clarify. exfalso.
          exploit memory_get_ts_strong; try apply GET. i. des; clarify.
          { unguard. des; auto. }
          exfalso. exploit Memory.get_disjoint.
          * apply GET.
          * apply WFSRC. apply GETSRC.
          * i. des; clarify. specialize (x0 (Time.meet to' ts3)).
            unfold Time.meet in *. des_ifs.
            { eapply x0; eauto; econs; ss.
              - refl.
              - etrans; eauto. }
            { eapply x0; eauto; econs; ss.
              - left. auto.
              - etrans; eauto.
              - refl. }
        + econs.
          * i. erewrite SPLITPROM in GETSRC0; eauto.
            erewrite Memory.split_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { ss. des; clarify. exfalso. auto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)); clarify.
            { ss. des; clarify. exfalso. auto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.split_o in GETTGT0; eauto.
            erewrite SPLITPROM.
            des_ifs; clarify; eauto.
          * i. apply or_comm in PROM0. apply or_strengthen in PROM0.
            erewrite SPLITPROM; eauto.
            erewrite (@Memory.split_o prom_tgt' prom_tgt); eauto.
            des_ifs; des; ss; clarify; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exfalso. auto. }
            { esplits; eauto. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }
      { exploit COMPLETE; eauto. i. des.
        exploit NFORGET; eauto. i. des. des_ifs; des; clarify.
        exploit split_reserve_exists; try apply GETSRC; eauto. i. des.
        exists (fun loc' to' => prom_self loc' to' \/ (loc' = loc /\ to' = to)), prom2, mem2.
        splits; auto.
        + econs.
          * ii. erewrite Memory.split_o in GETTGT0; eauto. erewrite SPLITMEM; eauto.
            des_ifs; ss.
            { des; clarify. exfalso. auto. }
            exploit COMPLETE0; eauto. ii. apply NPROMS. des; auto.
          * i. eapply concrete_promised_increase_promise; eauto.
            apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
          * i. erewrite split_covered; cycle 1; eauto. apply COVERED.
            inv COVERED0. rewrite SPLITMEM in GET. des_ifs; des; ss; clarify; econs; eauto.
            { inv ITV. econs; eauto. ss. etrans; eauto. left. auto. }
            { inv ITV. econs; eauto. }
        + ii. erewrite SPLITMEM in GET. des_ifs. guardH o. guardH o0.
          ss. exploit ATTACH; cycle 1; eauto. des; auto. clarify. exfalso.
          exploit memory_get_ts_strong; try apply GET. i. des; clarify.
          { unguard. des; auto. }
          exfalso. exploit Memory.get_disjoint.
          * apply GET.
          * apply WFSRC. apply GETSRC.
          * i. des; clarify. specialize (x0 (Time.meet to' ts3)).
            unfold Time.meet in *. des_ifs.
            { eapply x0; eauto; econs; ss.
              - refl.
              - etrans; eauto. }
            { eapply x0; eauto; econs; ss.
              - left. auto.
              - etrans; eauto.
              - refl. }
        + econs.
          * i. erewrite SPLITPROM in GETSRC0; eauto.
            erewrite Memory.split_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
            { ss. des; clarify. exfalso. auto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)); clarify.
            { ss. des; clarify. eauto. }
            exploit NFORGET; eauto.
          * i. erewrite Memory.split_o in GETTGT0; eauto.
            erewrite SPLITPROM.
            des_ifs; clarify; eauto.
          * i. apply or_comm in PROM. apply or_strengthen in PROM.
            erewrite SPLITPROM; eauto.
            erewrite (@Memory.split_o prom_tgt' prom_tgt); eauto.
            des_ifs; des; ss; clarify; eauto.
            { ss. destruct a. clarify. esplits; eauto. }
            { exfalso. auto. }
        + eapply reserve_future_wf_pasts_memory; eauto.
      }

    - dup PROMISES. apply lower_succeed_wf in PROMISES0. des. clarify. inv MSG_LE.
      assert (PROM: prom_self loc to).
      { exploit COMPLETE; eauto. i. des.
        apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
      exploit FORGET; eauto. i. des.
      exists prom_self, prom_src, mem_src. esplits; eauto.
      + econs.
        * ii. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; ss.
          { des; clarify. exfalso. apply NPROMS. auto. }
          exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
        * i. eapply lower_covered; eauto.
      + econs.
        * i. erewrite Memory.lower_o; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify.
          { ss. des; clarify. }
          guardH o. exploit NFORGET; eauto.
        * i. erewrite Memory.lower_o in GETTGT0; eauto.
          des_ifs; clarify.
          { ss. des. clarify. eauto. }
          { guardH o. exploit COMPLETE; eauto. }
        * i. erewrite (@Memory.lower_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
          exploit FORGET; eauto. i. des. ss. clarify. esplits; eauto.

    - dup PROMISES. apply Memory.remove_get0 in PROMISES0. des.
      exploit COMPLETE; eauto. i. des. exploit NFORGET; eauto.
      { ii. exploit FORGET; eauto. i. des. rewrite GET in GETTGT. clarify. }
      i. des. rewrite GETTGT in *. clarify. des_ifs; des; clarify.
      exploit Memory.remove_exists.
      { eapply GETSRC. } i. des.
      exploit Memory.remove_exists_le; try apply x0; eauto. i. des.
      assert (FUTURE: reserve_future_memory prom_src mem_src mem2 mem0).
      { econs.
        - econs 4; eauto.
        - econs 1. }
      exists prom_self, mem2, mem0. splits; auto.
      + econs.
        * ii. erewrite Memory.remove_o in GETTGT0; eauto. erewrite Memory.remove_o; eauto.
          des_ifs. guardH o. exploit COMPLETE0; eauto.
        * i. eapply concrete_promised_increase_promise; eauto.
          apply CONCRETE. eapply reserve_future_concrete_promised; eauto.
        * i. erewrite remove_covered in COVERED0; eauto.
          eapply remove_covered; eauto. des; split; auto.
      + ii. erewrite Memory.remove_o in GET; eauto. des_ifs.
        eapply ATTACH; eauto.
      + econs.
        * i. erewrite Memory.remove_o in GETSRC0; eauto.
          erewrite Memory.remove_o; eauto.
          destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); clarify. guardH o.
          exploit NFORGET; eauto.
        * i. erewrite Memory.remove_o in GETTGT0; eauto.
          erewrite Memory.remove_o; try eassumption.
          des_ifs; clarify. guardH o.
          exploit COMPLETE; eauto.
        * i. erewrite (@Memory.remove_o mem2 prom_src); eauto.
          erewrite (@Memory.remove_o prom_tgt' prom_tgt); eauto. des_ifs; eauto.
          exploit FORGET; eauto. i. des. ss. clarify.
      + eapply reserve_future_wf_pasts_memory; eauto.
        Unshelve. all: auto.
  Admitted.

  Lemma sim_remove_step_forget prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from_tgt from_src to prom_tgt' val released_tgt released_src
        (NLOC: L loc)
        (REMOVEPROM: Memory.remove prom_tgt loc from_tgt to (Message.concrete val released_tgt) prom_tgt')
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (FROM: Time.le from_tgt from_src)
        (TO: Time.lt from_src to)
        (RELEASEDWF: View.opt_wf released_src)
        (RELEASEDLE: View.opt_le released_src released_tgt)
        (RELEASEDCLOSED: Memory.closed_opt_view released_src mem_src)
        (NREAD: ~ (prom_others \2/ prom_self) loc from_src)
        (OTHERS: forall loc to, prom_others loc to -> prom_self loc to -> False)
    :
      exists prom_mid mem_mid prom_self' pasts' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_mid mem_mid>>) /\
        (<<WRITETGT: Memory.write prom_mid mem_mid loc from_src to val released_src prom_src' mem_src' Memory.op_kind_add>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self' pasts' rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  .
  Proof.
    inv PROMISE. inv MEM.
    exploit Memory.remove_get0; eauto. i. des.
    assert (PROM: prom_self loc to).
    { exploit COMPLETE; eauto. i. des.
      apply NNPP. ii. exploit NFORGET; eauto. i. des. des_ifs. des. clarify. }
    exploit FORGET; eauto. i. des.
    i. des. rewrite GETTGT in *. clarify. des_ifs; des; clarify.
    exploit Memory.remove_exists.
    { eapply GETSRC. } i. des.
    exploit Memory.remove_exists_le; try apply x0; eauto. i. des.
    assert (FUTURE: reserve_future_memory prom_src mem_src mem2 mem0).
    { econs.
      - econs 4; eauto.
      - econs 1. }

    exploit Memory.add_exists.
    { instantiate (2:=from_src).
      ii. erewrite Memory.remove_o in GET2; eauto. des_ifs.
      exploit Memory.get_disjoint.
      - apply GET2.
      - apply WFSRC. apply GETSRC.
      - i. ss. des; clarify. eapply x3; eauto.
        inv LHS. econs; eauto. ss. eapply TimeFacts.le_lt_lt; eauto. }
    { apply TO. }
    { econs 1. apply RELEASEDWF. } intros [mem_src' ADDMEM].
    exploit Memory.add_exists_le.
    { instantiate (1:=mem0). instantiate (1:=mem2).
      ii. erewrite Memory.remove_o; eauto.
      erewrite Memory.remove_o in LHS; cycle 1; eauto. des_ifs. auto. }
    { eapply ADDMEM. } intros [prom_mid' ADDPROM].
    exploit Memory.remove_exists.
    { eapply Memory.add_get0. apply ADDPROM. } intros [prom_src' REMOVEPROMSRC].
    exists mem2, mem0, (fun loc' to' => prom_self loc' to' /\ (loc' <> loc \/ to' <> to)),
    (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then Some mem_src else pasts loc' to'), prom_src', mem_src'.
    exploit MemoryFacts.add_remove_eq.
    { apply ADDPROM. }
    { apply REMOVEPROMSRC. } i. clarify.

    assert (PROMISESRC: Memory.promise mem2 mem0 loc from_src to (Message.concrete val released_src) prom_mid' mem_src' Memory.op_kind_add).
    { econs; eauto.
      - econs. etrans.
        + apply View.unwrap_opt_le in RELEASEDLE.
          inv RELEASEDLE. apply RLX.
        + inv MEMTGT. apply WFTGT in GETTGT.
          eapply CLOSED in GETTGT. des. inv MSG_TS. auto.
      - i. destruct msg'; cycle 1.
        { admit. }
        clarify. erewrite Memory.remove_o in GET; eauto. des_ifs.
        exploit ATTACH; eauto.
    }

    assert (FUTUREMEM: Memory.future mem_src mem_src').
    { etrans.
      - eapply reserve_future_future; eauto.
      - econs; [|refl]. econs.
        + econs. apply ADDMEM.
        + econs; eauto.
          eapply Memory.promise_closed_opt_view; cycle 1.
          { apply PROMISESRC. }
          eapply Memory.promise_closed_opt_view; eauto.
        + econs. etrans.
          * apply View.unwrap_opt_le in RELEASEDLE.
            inv RELEASEDLE. apply RLX.
          * inv MEMTGT. apply WFTGT in GETTGT.
            eapply CLOSED in GETTGT. des. inv MSG_TS. auto.
    }

    splits; auto.
    - econs; eauto.
    - econs; eauto.
      + i. erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
        * ss. des; clarify. apply WFTGT in GETTGT. clarify.
          esplits; eauto.
        * exploit COMPLETE0.
          { ii. apply NPROMS. des; eauto. }
          { eauto. }
          i. guardH o. des. esplits; eauto.
      + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * eapply CONCRETE; eauto. erewrite Memory.remove_o in GET; eauto.
          des_ifs. econs; eauto.
      + i. rewrite add_covered in COVERED0; eauto.
        rewrite remove_covered in COVERED0; eauto. apply COVERED.
        apply or_comm in COVERED0. apply or_strengthen in COVERED0. des; clarify; auto.
        econs; eauto. inv COVERED1. econs; ss. eapply TimeFacts.le_lt_lt; eauto.
    - ii.
      erewrite Memory.add_o in GET; eauto.
      erewrite Memory.remove_o in GET; eauto. des_ifs.
      + ss. destruct a; clarify.
        apply NREAD. des; auto.
      + eapply ATTACH; cycle 1; eauto. des; auto.

    - econs; eauto.
      + i. erewrite Memory.remove_o in GETSRC0; try apply x0; eauto.
        erewrite Memory.remove_o; eauto. des_ifs; ss.
        * exploit NFORGET; try apply GETSRC0; eauto.
        * exploit NFORGET; try apply GETSRC0; eauto.
      + i. erewrite Memory.remove_o; try apply x0; eauto.
        erewrite Memory.remove_o in GETTGT0; cycle 1; eauto. des_ifs.
        exploit COMPLETE; eauto.
      + i. erewrite (@Memory.remove_o mem2 prom_src); eauto.
        erewrite (@Memory.remove_o prom_tgt' prom_tgt); eauto. des_ifs.
        * ss. des; clarify.
        * ss. eapply FORGET. des; auto.

    - inv PAST. econs.
      + ii. erewrite Memory.add_o in GET; eauto.
        erewrite Memory.remove_o in GET; eauto.
        destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); ss.
        * des; clarify. esplits; eauto. des_ifs.
          { ss. des; clarify. exfalso. eapply Time.lt_strorder. eauto. }
          { guardH o. i. apply ONLY in PAST. des. auto. }
        * guardH o. exploit COMPLETE1; eauto. i. des. esplits; eauto.
          i. des_ifs.
          { ss. des; clarify. unguard.
            exfalso. exploit ATTACH; eauto. }
          { exploit ONLY; eauto. }
      + ii. des_ifs.
        * ss. des; clarify. splits; auto.
          { econs; eauto. eapply Memory.add_get0; eauto. }
          { apply Memory.future_future_weak; eauto. }
        * guardH o.
          apply ONLY in PAST. des. splits; auto.
          { eapply concrete_promised_increase_promise; eauto.
            eapply concrete_promised_increase_promise; eauto. }
          { etrans; eauto. eapply Memory.future_future_weak. auto. }
    - ii. des_ifs; eauto. ss. des; clarify.
      inv PAST. eapply ONLY in PAST0. des.
      inv CONCRETE0. apply WFSRC in GETSRC. clarify.
  Admitted.

  Lemma sim_write_step_forget prom_self prom_others pasts lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt
        lc_tgt' sc_tgt' mem_tgt' loc from_tgt to val None released_tgt ord kind
        (NLOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc_tgt mem_tgt loc from_tgt to val None released_tgt ord lc_tgt' sc_tgt' mem_tgt' kind)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists prom_self' prom_src mem_src_mid pasts' lc_src' sc_src' mem_src' from_src released_src,
        (<<FUTURE: reserve_future_memory lc_src.(Local.promises) mem_src prom_src mem_src_mid>>) /\
        (<<STEPSRC: Local.write_step (Local.mk lc_src.(Local.tview) prom_src) sc_src mem_src loc from_src to val None released_src ord lc_src' sc_src' mem_src' kind>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  (* TODO: condition about event *)
  .
  Proof.
  Admitted.

  Lemma sim_thread_step prom_self prom_others pasts lang st lc_src lc_tgt sc_src sc_tgt mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc_tgt' mem_tgt'
        (STEPTGT: @Thread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc_tgt mem_tgt) (Thread.mk _ st' lc_tgt' sc_tgt' mem_tgt'))
        (NOREAD: no_read_msgs (prom_others \2/ prom_self) e_tgt)
        (SC: TimeMap.le sc_src sc_tgt)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (SCSRC: Memory.closed_timemap sc_src mem_src)
        (SCTGT: Memory.closed_timemap sc_tgt mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local prom_self pasts lc_src lc_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
    :
      exists tr prom_self' pasts' lc_src' sc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc_src mem_src) (Thread.mk _ st' lc_src' sc_src' mem_src')>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self') mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self') mem_src'>>) /\
        (<<SC: TimeMap.le sc_src' sc_tgt'>>) /\
        (<<SIM: sim_local prom_self' pasts' lc_src' lc_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
          (* TODO: condition about event *)
  .
  Proof.
  Admitted.

  Lemma sim_promise_step_normal prom_self prom_others pasts mem_src mem_tgt rel_src rel_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (prom_others \2/ prom_self) mem_src mem_tgt)
        (ATTACH: not_attached (prom_others \2/ prom_self) mem_src)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (RELSRC: forall (loc: Loc.t), Memory.closed_view (rel_src loc) mem_src)
        (RELTGT: forall (loc: Loc.t), Memory.closed_view (rel_tgt loc) mem_src)
        (PROMISE: sim_promise prom_self pasts rel_src rel_tgt prom_src prom_tgt)
        (PAST: wf_pasts_memory mem_src pasts)
        (MSGTGT: Memory.closed_message msg_tgt mem_tgt')
    :
      exists msg_src pasts' prom_src' mem_src',
        (<<STEPTGT: Memory.promise prom_src mem_src loc from to msg_src prom_src' mem_src' kind>>) /\
        (<<MSGSRC: Memory.closed_message msg_src mem_src'>>) /\
        (<<MEM: sim_memory (prom_others \2/ prom_self) mem_src' mem_tgt'>>) /\
        (<<ATTACH: not_attached (prom_others \2/ prom_self) mem_src'>>) /\
        (<<PROMISE: sim_promise prom_self pasts' rel_src rel_tgt prom_src' prom_tgt'>>) /\
        (<<PAST: wf_pasts_memory mem_src' pasts'>>) /\
        (<<PASTLE: pasts_le pasts pasts'>>)
  .
  Proof.
    exploit sim_message_exists.
    { eapply MEMSRC. }
    instantiate (1:=msg_tgt). i. des.

    inv PROMISE. inv MEM. dup STEPTGT. inv STEPTGT.
    - dup MEM. apply add_succeed_wf in MEM0. des.
      exploit Memory.add_exists; try apply TO1.
      { instantiate (1:=mem_src). instantiate (1:=loc). ii.
        exploit COVERED.
        { econs; eauto. } i. inv x0.
        eapply DISJOINT; eauto. }
      { instantiate (1:=msg_src). admit. (* Message.wf *) } intros [mem_src' ADDMEM].
      exploit Memory.add_exists_le; try apply ADDMEM; eauto. intros [prom_src' ADDPROM].
      exists msg_src. inv SIM.

      { exists (fun loc' to' => if loc_ts_eq_dec (loc', to') (loc, to) then Some mem_src else pasts loc' to')
        , prom_src', mem_src'.
        splits; auto.
        - econs; eauto.
          + econs; eauto.
            apply sim_opt_view_le in SIM0.
            apply View.unwrap_opt_le in SIM0.
            inv SIM0. inv TS. etrans; eauto.
          + i. clarify.
            admit.
        - econs.
          admit. (* Memory.closed_opt_view released_src mem_src' *)
        - econs.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; eauto. des_ifs.
            * ss; des; clarify. esplits; eauto.
              eapply sim_opt_view_le; eauto.
            * exploit COMPLETE0; eauto.
          + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
            * ss. des; clarify. econs.
              eapply Memory.add_get0; eauto.
            * exploit CONCRETE; eauto.
              { econs; eauto. } i. inv x.
              eapply Memory.add_get1 in GET0; eauto. econs; eauto.
          + i. erewrite add_covered in COVERED0; eauto.
            erewrite add_covered; cycle 1; eauto. des; auto.
        - ii.
          admit. (* change it *)
        - econs.
          + i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); eauto.
            ss. des; clarify. esplits; eauto.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
          + i. erewrite (@Memory.add_o prom_src'); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. exfalso.
              exploit FORGET; eauto. i. des. clarify.
            * exploit FORGET; eauto.
        - inv PAST. econs.
          + ii. erewrite Memory.add_o in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            * ss. des; clarify. esplits; eauto.
              { admit. (* Memory.closed_opt_view released mem_src *) }
              { i. des_ifs.
                - ss. des; clarify. refl.
                - guardH o. apply ONLY in PAST. des. auto. }
            * guardH o. exploit COMPLETE1; eauto. i. des.
              esplits; eauto. i. des_ifs.
              { ss. des; clarify. exfalso.
                exploit ATTACH0; eauto.
                admit. }
              { ss. exploit COMPLETE1; eauto. }
          + i. des_ifs.
            * ss. des; clarify. esplits; eauto.
              { econs. eapply Memory.add_get0. eauto. }
              { apply Memory.future_future_weak.
                admit. }
            * guardH o. exploit ONLY; eauto. i. des. splits; auto.
              { inv CONCRETE0. eapply Memory.add_get1 in GET; eauto. econs; eauto. }
              { etrans; eauto.
                admit. }
        - ii. des_ifs. ss. des; clarify. exfalso.
          inv PAST. exploit ONLY; eauto. i. des. inv CONCRETE0.
          apply Memory.add_get0 in ADDMEM. des. clarify.
      }

      { exists pasts, prom_src', mem_src'.
        splits; auto.
        - econs; eauto. i. clarify.
        - econs.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; eauto. des_ifs.
            exploit COMPLETE0; eauto.
          + i. inv PR. erewrite Memory.add_o in GET; eauto. des_ifs.
            exploit CONCRETE; eauto.
            { econs; eauto. } i. inv x.
            eapply Memory.add_get1 in GET0; eauto. econs; eauto.
          + i. erewrite add_covered in COVERED0; eauto.
            erewrite add_covered; cycle 1; eauto. des; auto.
        - ii.
          admit. (* change it *)
        - econs.
          + i. erewrite Memory.add_o in GETSRC; eauto.
            erewrite Memory.add_o; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)); eauto.
            ss. des; clarify. esplits; eauto.
          + i. erewrite Memory.add_o in GETTGT; eauto.
            erewrite Memory.add_o; cycle 1; eauto. des_ifs; eauto.
          + i. erewrite (@Memory.add_o prom_src'); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. exfalso.
              exploit FORGET; eauto. i. des. clarify.
            * exploit FORGET; eauto.
        - inv PAST. econs.
          + ii. erewrite Memory.add_o in GET; eauto.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            * ss.
            * guardH o. exploit COMPLETE1; eauto.
          + i. exploit ONLY; eauto. i. des. splits; auto.
            * inv CONCRETE0. eapply Memory.add_get1 in GET; eauto. econs; eauto.
            * etrans; eauto.
              apply Memory.future_future_weak. econs; [|refl]. econs; eauto.
        - refl.
      }

    - dup PROMISES. apply split_succeed_wf in PROMISES0. des. clarify.
      exploit COMPLETE; eauto. i. des.
      exploit NFORGET; eauto.
      { ii. exploit FORGET; eauto. i. des. clarify. } i. des. des_ifs.

      { des. clarify.
        exploit Memory.split_exists.
  Admitted.

End SIM.
