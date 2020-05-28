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
Require Import JoinedView.

Require Import MemoryProps.

Require Import LocalDRFDef.

Set Implicit Arguments.



Section SIM.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> list Time.t.

  Definition lb_time (l: list Time.t) (ts ts': Time.t) :=
    forall t (IN: List.In t l) (LT: Time.lt ts t),
      Time.lt ts' t.

  Lemma eq_lb_time l ts
    :
      lb_time l ts ts.
  Proof.
    ii. auto.
  Qed.

  Lemma lb_time_exists l ts
    :
      exists ts', <<TS: Time.lt ts ts'>> /\ <<LB: lb_time l ts ts'>>.
  Proof.
    induction l.
    { exists (Time.incr ts). econs; ss.
      eapply Time.incr_spec. }
    { des. destruct (Time.le_lt_dec a ts').
      { destruct (Time.le_lt_dec a ts).
        { exists ts'. split; ss. ii. ss. des.
          { subst. exfalso. eapply Time.lt_strorder.
            eapply (@TimeFacts.le_lt_lt t ts); eauto. }
          { eauto. }
        }
        { exists (Time.middle ts a). split; ss.
          { eapply Time.middle_spec; eauto. }
          { ii. ss. des.
            { subst. eapply Time.middle_spec; eauto. }
            { exploit LB; eauto. i.
              transitivity ts'; eauto.
              eapply TimeFacts.lt_le_lt; eauto.
              eapply Time.middle_spec; eauto. }
          }
        }
      }
      { exists ts'. split; ss. ii. ss. des.
        { subst. auto. }
        { eapply LB; eauto. }
      }
    }
  Qed.

  Lemma lb_time_lower l ts ts'0 ts'1
        (LB: lb_time l ts ts'0)
        (TS: Time.le ts'1 ts'0)
    :
      lb_time l ts ts'1.
  Proof.
    ii. exploit LB; eauto.
    i. eapply TimeFacts.le_lt_lt; eauto.
  Qed.



  Inductive sim_memory_content
            (F: Prop)
            (extra: Time.t -> Prop)
            (loc: Loc.t) (ts: Time.t)
    : option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_memory_content_none
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
    :
      sim_memory_content F extra loc ts None None
  | sim_memory_content_normal
      from_src from_tgt msg
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (FROM: Time.le from_tgt from_src)
      (LB: forall (LOC: L loc), lb_time (times loc) from_tgt from_src)
      (NLOC: ~ L loc -> from_src = from_tgt)
    :
      sim_memory_content F extra loc ts (Some (from_src, msg)) (Some (from_tgt, msg))
  | sim_memory_content_forget
      from_src from_tgt val released
      (PROM: F)
      (NEXTRA: forall t, ~ extra t)
      (NLOC: L loc)
      (FROM: Time.le from_tgt from_src)
      (LB: lb_time (times loc) from_tgt from_src)
    :
      sim_memory_content F extra loc ts (Some (from_src, Message.reserve)) (Some (from_tgt, Message.concrete val released))
  | sim_memory_content_extra
      from
      (PROM: ~ F)
      (EXTRA: extra from)
      (NLOC: L loc)
    :
      sim_memory_content F extra loc ts (Some (from, Message.reserve)) None
  .
  Hint Constructors sim_memory_content.

  (* Record sim_memory (forgets: Loc.t -> Time.t -> option Time.t -> Prop) *)
  (*        (mem_src mem_tgt: Memory.t) : Prop := *)
  (*   { *)
  (*     sim_memory_forgets_wf: *)
  (*       forall loc ts ts' *)
  (*              (FORGET: forgets loc ts (Some ts')), *)
  (*         (<<LB: lb_time (times loc) ts ts'>>) /\ *)
  (*         (<<LOC: L loc>>) /\ *)
  (*         (<<TS: Time.lt ts ts'>>); *)
  (*     sim_memory_forgets_message: *)
  (*       forall loc ts ts' *)
  (*              (FORGET: forgets loc ts ts'), *)
  (*       exists from val released, *)
  (*         (<<GET: Memory.get loc ts mem_tgt = Some (from, Message.concrete val released)>>); *)
  (*     sim_memory_normal: *)
  (*       forall loc ts (NLOC: L loc), Memory.get loc ts mem_src = Memory.get loc ts mem_tgt; *)
  (*     sim_memory_get: *)
  (*       forall loc ts val released *)
  (*              (LOC: L loc) *)
  (*              (NORMAL: forall ts', ~ forgets loc ts ts'), *)
  (*         (exists from, <<GET: Memory.get loc ts mem_src = Some (from, Message.concrete val released)>>) *)
  (*         <-> *)
  (*         (exists from, <<GET: Memory.get loc ts mem_tgt = Some (from, Message.concrete val released)>>); *)
  (*     sim_memory_covered: *)
  (*       forall loc ts (COVER: covered loc ts mem_src) (LOC: L loc), *)
  (*         (<<COVER: covered loc ts mem_tgt>>) \/ *)
  (*         (exists from to, *)
  (*             (<<FORGET: forgets loc to (Some from)>>) /\ *)
  (*             (<<ITV: Interval.mem (from, to) ts>>)); *)
  (*   }. *)

  Record sim_memory
         (F: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (mem_src mem_tgt: Memory.t): Prop :=
    {
      sim_memory_contents:
        forall loc ts,
          sim_memory_content (F loc ts) (extra loc ts)
                             loc ts (Memory.get loc ts mem_src) (Memory.get loc ts mem_tgt);
      sim_memory_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: F loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>) /\
          (<<UNIQUE: forall loc from' (EXTRA: extra loc ts from'),
              from' = from>>);
    }.

  Inductive sim_promise_content
            (F: Prop)
            (extra: Time.t -> Prop)
            (loc: Loc.t) (ts: Time.t)
    :
      option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_none
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (NLOC: L loc)
    :
      sim_promise_content F extra loc ts None None
  | sim_promise_content_normal
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (NLOC: ~ L loc)
      cnt
    :
      sim_promise_content F extra loc ts cnt cnt
  | sim_promise_content_reserve
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (LOC: L loc)
      from_src from_tgt
    :
      sim_promise_content F extra loc ts
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, Message.reserve))
  | sim_promise_content_forget
      (PROM: F)
      (NEXTRA: forall t, ~ extra t)
      (LOC: L loc)
      from_src from_tgt val released
    :
      sim_promise_content F extra loc ts
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, Message.concrete val released))
  | sim_promise_content_extra
      from
      (NPROM: ~ F)
      (LOC: L loc)
      (EXTRA: extra from)
    :
      sim_promise_content F extra loc ts (Some (from, Message.reserve)) None
  .
  Hint Constructors sim_promise_content.

  Record sim_promise
         (self: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (prom_src prom_tgt: Memory.t): Prop :=
    {
      sim_promise_contents:
        forall loc ts,
          sim_promise_content (self loc ts) (extra loc ts)
                              loc ts
                              (Memory.get loc ts prom_src)
                              (Memory.get loc ts prom_tgt);
      sim_promise_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: self loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>);
      sim_promise_extra:
        forall loc ts (SELF: self loc ts),
        exists to,
          (<<GET: Memory.get loc to prom_src = Some (ts, Message.reserve)>>) /\
          (<<TS: Time.lt ts to>>);
    }.

  Inductive sim_local
            (self: Loc.t -> Time.t -> Prop)
            (extra: Loc.t -> Time.t -> Time.t -> Prop)
    :
      forall (lc_src lc_tgt: Local.t), Prop :=
  | sim_local_intro
      tvw prom_src prom_tgt
      (PROMS: sim_promise self extra prom_src prom_tgt)
    :
      sim_local self extra (Local.mk tvw prom_src) (Local.mk tvw prom_tgt)
  .
  Hint Constructors sim_local.

  Inductive sim_statelocal
            (self: Loc.t -> Time.t -> Prop)
            (extra: Loc.t -> Time.t -> Time.t -> Prop)
    :
      sigT (@Language.state ProgramEvent.t) * Local.t -> sigT (@Language.state ProgramEvent.t) * Local.t -> Prop :=
  | forget_statelocal_intro
      st lc_src lc_tgt
      (LOCAL: sim_local self extra lc_src lc_tgt)
    :
      sim_statelocal self extra (st, lc_src) (st, lc_tgt)
  .

  Inductive all_promises (proms: Ident.t -> Loc.t -> Time.t -> Prop): Loc.t -> Time.t -> Prop :=
  | all_promises_intro
      tid loc ts
      (PROMS: proms tid loc ts)
    :
      all_promises proms loc ts
  .
  Hint Constructors all_promises.

  Lemma sim_read_step F extra self lc_src lc_tgt mem_src mem_tgt loc to val released ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released ord lc_tgt')
        (NOREAD: ~ F loc to)
        (MEM: sim_memory F extra mem_src mem_tgt)
        (LOCAL: sim_local self extra lc_src lc_tgt)
    :
      exists lc_src',
        (<<STEPSRC: Local.read_step lc_src mem_src loc to val released ord lc_src'>>) /\
        (<<SIM: sim_local self extra lc_src' lc_tgt'>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_src = Some (from, Message.concrete val released)>>) /\
        (<<GETTGT: exists from, Memory.get loc to mem_tgt = Some (from, Message.concrete val released)>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    set (MEM0:= MEM.(sim_memory_contents) loc to). rewrite GET in *. inv MEM0; ss.
    esplits; eauto.
  Qed.

  Lemma sim_fence_step self extra lc_src lc_tgt sc ordr ordw
        sc' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc ordr ordw lc_tgt' sc')
        (LOCAL: sim_local self extra lc_src lc_tgt)
    :
      exists lc_src',
        (<<STEPSRC: Local.fence_step lc_src sc ordr ordw lc_src' sc'>>) /\
        (<<SIM: sim_local self extra lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT. esplits.
    - econs; ss; eauto. ii.
      set (PROM:= PROMS.(sim_promise_contents) loc t).
      rewrite GET in *. inv PROM; ss.
      exploit RELEASE; eauto.
    - econs; ss; eauto.
  Qed.

  Lemma sim_promise_consistent self extra lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local self extra lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii. ss.
    set (PROM:= PROMS.(sim_promise_contents) loc ts).
    rewrite PROMISE in *. inv PROM. eauto.
  Qed.

  Lemma sim_failure_step self extra lc_src lc_tgt
        (STEPTGT: Local.failure_step lc_tgt)
        (SIM: sim_local self extra lc_src lc_tgt)
    :
      Local.failure_step lc_src.
  Proof.
    inv STEPTGT. econs.
    eapply sim_promise_consistent; eauto.
  Qed.

  Lemma sim_memory_others_self_wf
        F extra mem_src mem_tgt
        (MEMORY: sim_memory F extra mem_src mem_tgt)
    :
      forall loc' to', F loc' to' -> L loc'.
  Proof.
    ii. set (MEMORY0:=MEMORY.(sim_memory_contents) loc' to'). inv MEMORY0; clarify.
  Qed.

  Lemma sim_memory_extra_others_self_wf
        F extra mem_src mem_tgt
        (MEMORY: sim_memory F extra mem_src mem_tgt)
    :
      forall loc' from to', extra loc' to' from -> L loc'.
  Proof.
    ii. set (MEMORY0:=MEMORY.(sim_memory_contents) loc' to').
    inv MEMORY0; clarify; (exfalso; eapply NEXTRA; eauto).
  Qed.

  Lemma sim_promise_step_normal others self extra_others extra_self
        mem_src mem_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt' kind
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg prom_tgt' mem_tgt' kind)
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (SEMI: semi_closed_message msg mem_src loc to)
    :
      exists prom_src' mem_src',
        (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' kind>>) /\
        (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt'>>) /\
        (<<PROMISE: sim_promise self extra_self prom_src' prom_tgt'>>) /\
        (<<CLOSED: Memory.closed_message msg mem_src'>>)
  .
  Proof.
    generalize (sim_memory_others_self_wf MEM). intros PROMSWF.
    generalize (sim_memory_extra_others_self_wf MEM). intros EXTRAWF.
    inv STEPTGT.

    (* add case *)
    - exploit add_succeed_wf; try apply MEM0. i. des.
      hexploit (@Memory.add_exists mem_src loc from to msg); ss.
      { i. set (MEM1:= MEM.(sim_memory_contents) loc to2).
        rewrite GET2 in *. inv MEM1; cycle 1.
        { exfalso. apply NLOC. des; eauto. }
        { exfalso. apply NLOC. des; eauto. }
        ii. eapply DISJOINT; eauto.
        inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
      intros [mem_src' ADDMEMSRC].
      exploit Memory.add_exists_le; try apply ADDMEMSRC; eauto.
      intros [prom_src' ADDPROMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' Memory.op_kind_add).
      { econs; eauto. i. subst.
        set (MEM1:= MEM.(sim_memory_contents) loc to'). rewrite GET in MEM1. inv MEM1; ss.
        eapply ATTACH; eauto. erewrite NLOC0; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg mem_src').
      { destruct msg; auto.
        eapply semi_closed_message_add; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + econs.
        { ii. set (MEM1:= MEM.(sim_memory_contents) loc0 ts).
          erewrite (@Memory.add_o mem_src'); eauto.
          erewrite (@Memory.add_o mem_tgt'); eauto.
          des_ifs; try by (ss; des; clarify).
          * econs; eauto.
            { ii. ss. des; clarify; eauto. }
            { ii. ss. des; clarify; eauto. }
            { refl. }
            { i. ss. }
        }
        { eapply MEM.(sim_memory_wf); eauto. }
      + econs.
        { ii. set (PROM:= PROMISE.(sim_promise_contents) loc0 ts).
          erewrite (@Memory.add_o prom_src'); eauto.
          erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
        }
        { apply PROMISE. }
        { i. hexploit PROMISE.(sim_promise_extra); eauto. i. des.
          esplits; eauto. erewrite (@Memory.add_o prom_src'); eauto.
          des_ifs. ss. des; clarify.
          exfalso. eapply NLOC. eapply PROMSWF; eauto. }

    (* split case *)
    - exploit split_succeed_wf; try apply PROMISES. i. des. clarify.
      set (PROMISE0:= PROMISE.(sim_promise_contents) loc ts3). rewrite GET2 in *.
      inv PROMISE0; ss.
      hexploit (@Memory.split_exists prom_src loc from to ts3 (Message.concrete val' released')); ss.
      { eauto. }
      intros [prom_src' SPLITPROMSRC].
      exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
      intros [mem_src' SPLITMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val' released') prom_src' mem_src' (Memory.op_kind_split ts3 msg3)).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message (Message.concrete val' released') mem_src').
      { eapply semi_closed_message_split; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + econs.
        { ii. set (MEM1:=MEM.(sim_memory_contents) loc0 ts).
          erewrite (@Memory.split_o mem_src'); eauto.
          erewrite (@Memory.split_o mem_tgt'); eauto.
          des_ifs; try by (ss; des; clarify).
          { ss. des; clarify. econs; eauto.
            * refl.
            * i. ss. }
          { guardH o. ss. des; clarify. econs; eauto.
            * refl.
            * i. ss. }
        }
        { apply MEM.(sim_memory_wf); eauto. }
      + econs.
        { ii. set (PROM:= PROMISE.(sim_promise_contents) loc0 ts).
          erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. econs; eauto.
          * guardH o. ss. des; clarify. econs; eauto. }
        { apply PROMISE. }
        { i. hexploit PROMISE.(sim_promise_extra); eauto. i. des.
          esplits; eauto. erewrite (@Memory.split_o prom_src'); eauto. des_ifs.
          - ss. des; clarify. exfalso. eapply NLOC. eapply PROMSWF; eauto.
          - ss. des; clarify. exfalso. eapply NLOC. eapply PROMSWF; eauto. }

    (* lower case *)
    - exploit lower_succeed_wf; try apply PROMISES. i. des. clarify.
      set (PROMISE0:= PROMISE.(sim_promise_contents) loc to). rewrite GET in *. inv PROMISE0; ss.

      hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released) msg); ss.

      intros [prom_src' LOWERPROMSRC].
      exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
      intros [mem_src' LOWERMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val released))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg mem_src').
      { destruct msg; auto.
        eapply semi_closed_message_lower; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + econs.
        { ii. set (MEM1:=MEM.(sim_memory_contents) loc0 ts).
          erewrite (@Memory.lower_o mem_src'); eauto.
          erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
          * refl.
          * i. ss. }
        { apply MEM.(sim_memory_wf); eauto. }
      + econs.
        { ii. set (PROM:= PROMISE.(sim_promise_contents) loc0 ts).
          erewrite (@Memory.lower_o prom_src'); eauto.
          erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
          ss. des; clarify. econs; eauto. }
        { apply PROMISE. }
        { i. hexploit PROMISE.(sim_promise_extra); eauto. i. des.
          esplits; eauto. erewrite (@Memory.lower_o prom_src'); eauto. des_ifs.
          ss. des; clarify. }

    (* cancel case *)
    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      set (PROMISE0 := PROMISE.(sim_promise_contents) loc to). rewrite GET in *.
      inv PROMISE0; ss.

      hexploit (@Memory.remove_exists prom_src loc from to Message.reserve); ss.
      intros [prom_src' REMOVEPROMSRC].
      exploit Memory.remove_exists_le; try apply REMOVEPROMSRC; eauto.
      intros [mem_src' REMOVEMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }

      exists prom_src', mem_src'.
      splits; auto.
      + econs.
        { ii. set (MEM1:=MEM.(sim_memory_contents) loc0 ts).
          erewrite (@Memory.remove_o mem_src'); eauto.
          erewrite (@Memory.remove_o mem_tgt'); eauto.
          des_ifs; try by (des; ss; clarify).
          * ss. des; clarify. econs; eauto. }
        { apply MEM. }
      + econs.
        { ii. set (PROM:= PROMISE.(sim_promise_contents) loc0 ts).
          erewrite (@Memory.remove_o prom_src'); eauto.
          erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
          ss. des; clarify. econs 2; eauto. }
        { apply PROMISE. }
        { i. hexploit PROMISE.(sim_promise_extra); eauto. i. des.
          esplits; eauto. erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
          ss. des; clarify. exfalso. eapply NLOC. eapply PROMSWF; eauto. }
  Qed.

  Lemma sim_write_step_normal
        others self extra_others extra_self lc_src lc_tgt sc mem_src mem_tgt
        lc_tgt' sc' mem_tgt' loc from to val ord releasedm released kind
        (NLOC: ~ L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind)
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self extra_self lc_src lc_tgt)

        (RELEASEDMCLOSED: Memory.closed_opt_view releasedm mem_src)
        (RELEASEDMWF: View.opt_wf releasedm)
    :
      exists lc_src' mem_src',
        (<<STEPSRC: Local.write_step lc_src sc mem_src loc from to val releasedm released ord lc_src' sc' mem_src' kind>>) /\
        (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self extra_self lc_src' lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv WRITE. inv SIM. inv LOCALSRC. inv LOCALTGT.

    hexploit sim_promise_step_normal; eauto.
    { ss. econs. unfold TView.write_released. des_ifs; econs.
      eapply semi_closed_view_join.
      - inv MEMSRC. eapply unwrap_closed_opt_view; auto.
        eapply closed_opt_view_semi_closed. auto.
      - ss. setoid_rewrite LocFun.add_spec_eq. des_ifs.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. inv TVIEW_CLOSED. auto.
          * inv MEMSRC. eapply semi_closed_view_singleton. auto.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. inv TVIEW_CLOSED. auto.
          * inv MEMSRC. eapply semi_closed_view_singleton. auto.
    }
    i. des. ss.

    hexploit (@Memory.remove_exists
                prom_src' loc from to
                (Message.concrete val (TView.write_released tvw sc loc to releasedm ord))).
    { set (PROM:= PROMISE0.(sim_promise_contents) loc to).
      eapply Memory.remove_get0 in REMOVE. des.
      rewrite GET in *. inv PROM; ss. }
    intros [prom_src'' REMOVESRC].

    assert (NSELF: forall ts, ~ self loc ts).
    { ii. set (PROM:= PROMISE0.(sim_promise_contents) loc to). inv PROM; ss.
      eapply NLOC. eapply sim_memory_others_self_wf; eauto. ss. eauto. }

    esplits; eauto.

    - econs; ss.
      + econs; eauto.
      + ii. set (PROM:=PROMS.(sim_promise_contents) loc t).
        rewrite GET in *. inv PROM; ss.
        exploit RELEASE; eauto.

    - econs; auto. econs.
      { ii. set (PROM:=PROMISE0.(sim_promise_contents) loc0 ts).
        erewrite (@Memory.remove_o prom_src''); eauto.
        erewrite (@Memory.remove_o promises2); eauto. des_ifs.
        ss. des; subst. econs 2; eauto.
        ii. exploit sim_memory_extra_others_self_wf.
        { eapply MEM0. }
        { right. eauto. }
        { ii. ss. }
      }
      { apply PROMISE0. }
      { i. set (PROM:=PROMISE0.(sim_promise_extra) loc0 ts SELF). des.
        esplits; eauto. erewrite (@Memory.remove_o prom_src''); eauto.
        des_ifs. ss. des; clarify. exfalso. eapply NSELF; eauto. }
  Qed.


  Inductive sim_promise_content_strong
            (F: Prop)
            (extra: Time.t -> Prop)
            (extra_all: Time.t -> Time.t -> Prop)
            (loc: Loc.t) (ts: Time.t)
    :
      option (Time.t * Message.t) -> option (Time.t * Message.t) -> Prop :=
  | sim_promise_content_strong_none
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (NLOC: L loc)
    :
      sim_promise_content_strong F extra extra_all loc ts None None
  | sim_promise_content_strong_normal
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (NLOC: ~ L loc)
      cnt
    :
      sim_promise_content_strong F extra extra_all loc ts cnt cnt
  | sim_promise_content_strong_reserve
      (NPROM: ~ F)
      (NEXTRA: forall t, ~ extra t)
      (LOC: L loc)
      from_src from_tgt
      (EXTRA: from_tgt = from_src \/ extra_all from_src from_tgt)
    :
      sim_promise_content_strong F extra extra_all loc ts
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, Message.reserve))
  | sim_promise_content_strong_forget
      (PROM: F)
      (NEXTRA: forall t, ~ extra t)
      (LOC: L loc)
      from_src from_tgt val released
      (EXTRA: from_tgt = from_src \/ extra_all from_src from_tgt)
    :
      sim_promise_content_strong F extra extra_all loc ts
                          (Some (from_src, Message.reserve))
                          (Some (from_tgt, Message.concrete val released))
  | sim_promise_content_strong_extra
      from
      (NPROM: ~ F)
      (LOC: L loc)
      (EXTRA: extra from)
    :
      sim_promise_content_strong F extra extra_all loc ts (Some (from, Message.reserve)) None
  .
  Hint Constructors sim_promise_content_strong.


  Lemma sim_promise_content_strong_sim_promise_content
        loc ts F extra get0 get1 extra_all
        (SIM: sim_promise_content_strong F extra extra_all loc ts  get0 get1)
    :
      sim_promise_content F extra loc ts get0 get1.
  Proof.
    inv SIM; econs; eauto.
  Qed.

  Record sim_promise_strong
         (self: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (extra_all: Loc.t -> Time.t -> Time.t -> Prop)
         (prom_src prom_tgt: Memory.t): Prop :=
    {
      sim_promise_strong_contents:
        forall loc ts,
          sim_promise_content_strong (self loc ts) (extra loc ts) (extra_all loc)
                                     loc ts
                                     (Memory.get loc ts prom_src)
                                     (Memory.get loc ts prom_tgt);
      sim_promise_strong_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: self loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>);
      sim_promise_strong_extra:
        forall loc ts (SELF: self loc ts),
        exists to,
          (<<GET: Memory.get loc to prom_src = Some (ts, Message.reserve)>>) /\
          (<<TS: Time.lt ts to>>);
    }.

  Lemma sim_promise_strong_sim_promise
        self extra extra_all prom_src prom_tgt
        (SIM: sim_promise_strong self extra extra_all prom_src prom_tgt)
    :
      sim_promise self extra prom_src prom_tgt.
  Proof.
    econs.
    - ii. eapply sim_promise_content_strong_sim_promise_content; eauto.
      eapply SIM; eauto.
    - apply SIM.
    - apply SIM.
  Qed.

  Record sim_promise_list
         (self: Loc.t -> Time.t -> Prop)
         (extra: Loc.t -> Time.t -> Time.t -> Prop)
         (extra_all: Loc.t -> Time.t -> Time.t -> Prop)
         (prom_src prom_tgt: Memory.t)
         (l: list (Loc.t * Time.t)): Prop :=
    {
      sim_promise_list_contents:
        forall loc ts,
          (<<NORMAL: sim_promise_content_strong (self loc ts) (extra loc ts) (extra_all loc) loc ts
                                                (Memory.get loc ts prom_src)
                                                (Memory.get loc ts prom_tgt)>>) \/
          ((<<LIN: List.In (loc, ts) l>>) /\
           (<<WEAK: sim_promise_content (self loc ts) (extra loc ts) loc ts
                                        (Memory.get loc ts prom_src)
                                        (Memory.get loc ts prom_tgt)>>));
      sim_promise_list_wf:
        forall loc from ts (EXTRA: extra loc ts from),
          (<<FORGET: self loc from>>) /\
          (<<LB: lb_time (times loc) from ts>>) /\
          (<<TS: Time.lt from ts>>);
      sim_promise_list_extra:
        forall loc ts (SELF: self loc ts),
        exists to,
          (<<GET: Memory.get loc to prom_src = Some (ts, Message.reserve)>>) /\
          (<<TS: Time.lt ts to>>);
    }.

  Lemma sim_promise_list_nil self extra extra_all prom_src prom_tgt
        (SIM: sim_promise_list self extra extra_all prom_src prom_tgt [])
    :
      sim_promise_strong self extra extra_all prom_src prom_tgt.
  Proof.
    econs.
    - ii. hexploit SIM.(sim_promise_list_contents); eauto. i. des; eauto. ss.
    - apply SIM.
    - apply SIM.
  Qed.

  Lemma sim_promise_weak_list_exists self extra extra_all prom_src prom_tgt
        (SIM: sim_promise self extra prom_src prom_tgt)
        (FIN: Memory.finite prom_src)
    :
      exists l,
        (<<SIM: sim_promise_list self extra extra_all prom_src prom_tgt l>>).
  Proof.
    unfold Memory.finite in *. des.
    hexploit (@list_filter_exists
                (Loc.t * Time.t)
                (fun locts =>
                   let (loc, ts) := locts in
                   ~ sim_promise_content_strong (self loc ts) (extra loc ts) (extra_all loc) loc ts
                     (Memory.get loc ts prom_src)
                     (Memory.get loc ts prom_tgt))
                dom).
    i. des. exists l'. econs; [|apply SIM|apply SIM].
    ii. set (PROM:= SIM.(sim_promise_contents) loc ts).
    destruct (classic (List.In (loc,ts) l')).
    - right. splits; auto.
    - left. red. inv PROM; try by (econs; eauto).
      + apply NNPP. ii. exploit FIN; eauto. i.
        hexploit (proj1 (@COMPLETE (loc, ts))); auto.
        splits; auto. ii. rewrite H1 in *. rewrite H2 in *. auto.
      + apply NNPP. ii. exploit FIN; eauto. i.
        hexploit (proj1 (@COMPLETE (loc, ts))); auto.
        splits; auto. ii. rewrite H1 in *. rewrite H2 in *. auto.
  Qed.

  Lemma reserve_future_memory_unch
        prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        loc to from msg
        (GETMEM: Memory.get loc to mem0 = Some (from, msg))
        (GETPROM: Memory.get loc to prom0 = None)
    :
      (<<GETMEM: Memory.get loc to mem1 = Some (from, msg)>>) /\
      (<<GETPROM: Memory.get loc to prom1 = None>>).
  Proof.
    ginduction FUTURE; eauto. i. inv HD; clarify.
    { eapply IHFUTURE; eauto.
      - erewrite Memory.add_o; eauto. des_ifs.
        ss. des; clarify.
        eapply Memory.add_get0 in MEM. des. clarify.
      - erewrite Memory.add_o; eauto. des_ifs.
        ss. des; clarify.
        eapply Memory.add_get0 in MEM. des. clarify. }
    { apply split_succeed_wf in PROMISES. des. clarify. }
    { apply lower_succeed_wf in PROMISES. des. clarify. inv MSG_LE. }
    { eapply IHFUTURE; eauto.
      - erewrite Memory.remove_o; eauto. des_ifs.
        ss. des; clarify.
        eapply Memory.remove_get0 in PROMISES. des. clarify.
      - erewrite Memory.remove_o; eauto. des_ifs. }
  Qed.

  Lemma sim_memory_get_larger F extra mem_src mem_tgt loc from_src ts msg_src
        (MEM: sim_memory F extra mem_src mem_tgt)
        (GETSRC: Memory.get loc ts mem_src = Some (from_src, msg_src))
    :
      (exists from_tgt msg_tgt,
          (<<TS: Time.le from_tgt from_src>>) /\ (<<LB: lb_time (times loc) from_tgt from_src>>) /\
          (<<GETTGT: Memory.get loc ts mem_tgt = Some (from_tgt, msg_tgt)>>)) \/
      (<<EXTRA: extra loc ts from_src>> /\ <<FORGET: F loc from_src>>).
  Proof.
    set (MEM0 := MEM.(sim_memory_contents) loc ts).
    rewrite GETSRC in *. inv MEM0; eauto.
    { left. esplits; eauto. destruct (L loc); auto.
      rewrite NLOC; ss. }
    { left. esplits; eauto. }
    { right. esplits; eauto.
      apply MEM.(sim_memory_wf) in EXTRA. des; auto. }
  Qed.

  Lemma memory_get_disjoint_strong mem loc from0 to0 from1 to1 msg0 msg1
        (GET0: Memory.get loc to0 mem = Some (from0, msg0))
        (GET1: Memory.get loc to1 mem = Some (from1, msg1))
    :
      (to0 = to1 /\ from0 = from1 /\ msg0 = msg1) \/
      (<<TS: Time.le to0 from1>> /\ <<TS: Time.lt to0 to1>>) \/
      (<<TS: Time.le to1 from0>> /\ <<TS: Time.lt to1 to0>>).
  Proof.
    destruct (Time.le_lt_dec to0 to1).
    { destruct l.
      { dup H. eapply memory_get_from_mon in H; eauto. }
      { inv H. clarify. auto. }
    }
    { dup l. eapply memory_get_from_mon in l; eauto. }
  Qed.

  Lemma memory_forget_extra_exclusive F extra mem_src mem_tgt loc from to ts
        (MEM: sim_memory F extra mem_src mem_tgt)
        (FORGET: F loc ts)
        (EXTRA: extra loc to from)
    :
      ts <> to.
  Proof.
    ii. subst.
    set (MEM0:=MEM.(sim_memory_contents) loc to). inv MEM0; ss.
    eapply NEXTRA; eauto.
  Qed.

  Lemma promises_forget_extra_exclusive F extra mem_src mem_tgt loc from to ts
        (PROMISES: sim_promise F extra mem_src mem_tgt)
        (FORGET: F loc ts)
        (EXTRA: extra loc to from)
    :
      ts <> to.
  Proof.
    ii. subst.
    set (PROM:=PROMISES.(sim_promise_contents) loc to). inv PROM; ss.
    eapply NEXTRA; eauto.
  Qed.

  Definition memory_times_wf (mem: Memory.t): Prop :=
    forall loc to from msg
           (GET: Memory.get loc to mem = Some (from, msg)),
      (<<FROM: List.In from (times loc)>>) /\ (<<TO: List.In to (times loc)>>).

  Definition memory_times_wf_strong (mem: Memory.t): Prop :=
    forall loc to from msg
           (GET: Memory.get loc to mem = Some (from, msg)),
      (<<FROM: List.In from (times loc)>>) /\ (<<TO: List.In to (times loc)>>) /\
      (<<CAP: List.In (Time.incr to) (times loc)>>).

  Lemma memory_times_wf_strong_wf
    :
      memory_times_wf_strong <1= memory_times_wf.
  Proof.
    ii. eapply PR in GET. des. auto.
  Qed.

  Lemma sim_memory_disjoint F extra mem_src mem_tgt
        loc from_tgt to_tgt msg_tgt
        from_src to_src msg_src x
        (MEM: sim_memory F extra mem_src mem_tgt)
        (MEMWF: memory_times_wf mem_tgt)
        (GETTGT: Memory.get loc to_tgt mem_tgt = Some (from_tgt, msg_tgt))
        (GETSRC: Memory.get loc to_src mem_src = Some (from_src, msg_src))
        (ITVTGT: Interval.mem (from_tgt, to_tgt) x)
        (ITVSRC: Interval.mem (from_src, to_src) x)
    :
      (to_tgt = to_src /\ <<TS: Time.le from_tgt from_src>> /\ <<LB: lb_time (times loc) from_tgt from_src>>) \/
      (from_tgt = from_src /\
       (<<FORGET: F loc from_tgt>>) /\
       (<<EXTRA: extra loc to_src from_tgt>>) /\
       (<<TS: Time.lt to_src to_tgt>>)).
  Proof.
    hexploit sim_memory_get_larger; eauto. i. des.
    { hexploit Memory.get_disjoint.
      { eapply GETTGT0. }
      { eapply GETTGT. }
      i. des; subst; eauto. exfalso. eapply H.
      { inv ITVSRC. econs; ss; eauto.
        eapply TimeFacts.le_lt_lt; eauto. }
      { eauto. }
    }
    { set (MEM0 := MEM.(sim_memory_contents) loc from_src). inv MEM0; ss.
      symmetry in H. exploit memory_get_disjoint_strong.
      { eapply H. }
      { eapply GETTGT. }
      i. des.
      { subst. inv ITVTGT. inv ITVSRC. ss.
        exfalso. eapply Time.lt_strorder.
        eapply (@TimeFacts.lt_le_lt to_tgt x); eauto. }
      { destruct TS.
        { exfalso. eapply MEM.(sim_memory_wf) in EXTRA. des.
          eapply MEMWF in GETTGT; eauto. des.
          hexploit (LB0 from_tgt); eauto.
          i. inv ITVSRC. inv ITVTGT. ss.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply H2. } etrans.
          { left. eapply FROM2. }
          { eauto. }
        }
        { inv H1. right. splits; auto.
          set (MEM0 := MEM.(sim_memory_contents) loc to_tgt).
          rewrite GETTGT in MEM0. inv MEM0.
          { exploit memory_get_disjoint_strong.
            { symmetry in H2. eapply H2. }
            { eapply GETSRC. }
            i. des; auto.
            { subst. exfalso. eapply NEXTRA0; eauto. }
            { exfalso. dup GETTGT. apply memory_get_ts_strong in GETTGT. des.
              { subst. inv ITVTGT. ss. }
              { eapply Time.lt_strorder.
                eapply (@TimeFacts.lt_le_lt from_tgt to_tgt); eauto. }
            }
          }
          { exploit memory_get_disjoint_strong.
            { symmetry in H2. eapply H2. }
            { eapply GETSRC. }
            i. des; auto.
            { subst. exfalso. eapply NEXTRA0; eauto. }
            { exfalso. dup GETTGT. apply memory_get_ts_strong in GETTGT. des.
              { subst. inv ITVTGT. ss. timetac. }
              { eapply Time.lt_strorder.
                eapply (@TimeFacts.lt_le_lt from_tgt to_tgt); eauto. }
            }
          }
        }
      }
      { inv ITVTGT. inv ITVSRC. ss.
        exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
        { eapply TS0. } etrans.
        { left. apply FROM1. }
        { eauto. }
      }
    }
  Qed.

  Lemma sim_memory_extra_inj F extra mem_src mem_tgt
        (MEM: sim_memory F extra mem_src mem_tgt)
        loc from to0 to1
        (EXTRA0: extra loc to0 from)
        (EXTRA1: extra loc to1 from)
    :
      to0 = to1.
  Proof.
    set (MEM0:=MEM.(sim_memory_contents) loc to0).
    inv MEM0; try by (exfalso; eapply NEXTRA; eauto).
    set (MEM1:=MEM.(sim_memory_contents) loc to1).
    inv MEM1; try by (exfalso; eapply NEXTRA; eauto). clarify.
    apply MEM.(sim_memory_wf) in EXTRA0. des.
    exploit UNIQUE; eauto. i. subst.
    apply MEM.(sim_memory_wf) in EXTRA1. des.
    exploit UNIQUE0; eauto. i. subst.
    hexploit memory_get_from_inj.
    { symmetry. eapply H0. }
    { symmetry. eapply H2. }
    i. des; subst; auto.
    { timetac. }
    { timetac. }
  Qed.

  Lemma sim_memory_from_forget F extra mem_src mem_tgt
        (MEM: sim_memory F extra mem_src mem_tgt)
        loc to from_src from_tgt msg_src msg_tgt
        (GETSRC: Memory.get loc to mem_src = Some (from_src, msg_src))
        (GETTGT: Memory.get loc to mem_tgt = Some (from_tgt, msg_tgt))
        (FORGET: F loc from_src)
    :
      from_src = from_tgt.
  Proof.
    exploit sim_memory_get_larger; eauto. i. des.
    { clarify. destruct TS; eauto. exfalso.
      set (PROM:=MEM.(sim_memory_contents) loc from_src). inv PROM; ss.
      symmetry in H2.
      exploit Memory.get_disjoint.
      { apply H2. }
      { apply GETTGT0. }
      i. des; subst.
      { dup GETSRC. apply memory_get_ts_strong in GETSRC. des.
        { subst. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply H. }
          { eapply Time.bot_spec. }
        }
        { eapply Time.lt_strorder; eauto. }
      }
      { eapply x0.
        { econs; [|refl]. ss.
          eapply memory_get_ts_strong in H2. des; auto. subst.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply H. }
          { eapply Time.bot_spec. }
        }
        { econs; ss. eapply memory_get_ts_le in GETSRC; eauto. }
      }
    }
    { set (MEM0 := MEM.(sim_memory_contents) loc to).
      rewrite GETTGT in MEM0. inv MEM0; exfalso; eapply NEXTRA; eauto. }
  Qed.

  Lemma sim_memory_src_none F extra mem_src mem_tgt
        (MEM: sim_memory F extra mem_src mem_tgt)
        loc to
        (GETSRC: Memory.get loc to mem_src = None)
    :
      (<<GETTGT: Memory.get loc to mem_tgt = None>>) /\
      (<<NPROM: ~ F loc to >>) /\
      (<<NEXTRA: forall t, ~ extra loc to t>>).
  Proof.
    set (MEM0:=MEM.(sim_memory_contents) loc to).
    rewrite GETSRC in MEM0. inv MEM0. splits; auto.
  Qed.

  Lemma sim_promise_weak_stengthen others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (BOTNONETGT: Memory.bot_none prom_tgt)
        (PROM: sim_promise self extra_self prom_src prom_tgt)
        (* (SELF: self <2= promised prom_src) *)
        (MEMWF: memory_times_wf mem_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            Memory.get loc' ts' prom_src = None)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (EXTRA: extra_others loc' ts' from'),
            Memory.get loc' ts' prom_src = None)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \3/ extra_self)
                   prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      eapply sim_promise_list_nil; eauto. }
    i. destruct a as [loc ts].

    cut (sim_promise_content_strong (self loc ts) (extra_self loc ts)
                                    ((extra_others \3/ extra_self) loc)
                                    loc ts
                                    (Memory.get loc ts prom_src)
                                    (Memory.get loc ts prom_tgt) \/
         exists prom_src' mem_src',
           (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
           (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt>>) /\
           (<<PROM: sim_promise_list
                      self extra_self (extra_others \3/ extra_self)
                      prom_src' prom_tgt l>>)).
    { intros H. match goal with
                | [H:?A \/ ?B |- _ ] => cut B
                end.
      { clear H. i. des. exploit IHl.
        { eapply MEM0. }
        { eauto. }
        { eapply reserve_future_memory_le; eauto. }
        { eapply reserve_future_memory_finite; eauto. }
        { eapply reserve_future_memory_bot_none; try apply BOTNONESRC; eauto. }
        { eauto. }
        { eauto. }
        { i. set (MEM1:=MEM.(sim_memory_contents) loc' ts'). inv MEM1.
          { exfalso. eauto. }
          { eapply reserve_future_memory_unch; eauto. }
          { eapply reserve_future_memory_unch; eauto. }
          { eapply reserve_future_memory_unch; eauto. }
        }
        { i. set (MEM1:=MEM.(sim_memory_contents) loc' ts'). inv MEM1.
          { exfalso. eapply NEXTRA; eauto. }
          { eapply reserve_future_memory_unch; eauto. }
          { eapply reserve_future_memory_unch; eauto. }
          { eapply reserve_future_memory_unch; eauto. }
        }
        { eauto. }
        i. des. exists prom_src'0, mem_src'0. splits; eauto.
        eapply reserve_future_memory_trans; eauto. }
      { des; eauto. exists prom_src, mem_src. splits; auto.
        econs; [|apply SIM|apply SIM]. ii.
        set (PROM:=SIM.(sim_promise_list_contents) loc0 ts0).
        ss. des; clarify; auto. }
    }

    set (SIM0:= SIM.(sim_promise_list_contents) loc ts). des; auto.
    inv WEAK.
    { left. econs 1; eauto. }
    { left. econs 2; eauto. }
    { clear LIN. symmetry in H. symmetry in H0.
      assert (FROM: Time.le from_tgt from_src).
      { apply MLESRC in H0. apply MLETGT in H.
        set (MEM0:=MEM.(sim_memory_contents) loc ts).
        rewrite H in *. rewrite H0 in *. inv MEM0. auto. }
      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { left. exploit sim_memory_from_forget; eauto. ss. auto. }

      hexploit (@Memory.remove_exists prom_src); eauto.
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src); eauto.
      intros [mem_src' REMOVEMEM].
      assert (REMOVE: Memory.promise prom_src mem_src loc from_src ts Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      destruct (classic (exists from_src', (extra_others \3/ extra_self) loc from_src' from_tgt))
        as [[from_src' EXTRA]|].
      { guardH EXTRA.
        hexploit (@Memory.add_exists mem_src' loc from_src' ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MLETGT. eapply H. }
          { eapply GET2. }
          { instantiate (1:=x). inv LHS. econs; ss.
            transitivity from_src'; auto.
            eapply MEM.(sim_memory_wf) in EXTRA. des; auto. }
          { eauto. }
          i. destruct H1 as [EQ|[EQ [FORGET [EXTRA0 TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA0.
            hexploit sim_memory_extra_inj.
            { eapply MEM. }
            { eapply EXTRA0. }
            { eapply EXTRA. }
            i. subst. inv LHS. inv RHS. ss. timetac. }
        }
        { eapply MEM.(sim_memory_wf) in EXTRA. destruct EXTRA as [_ EXTRA]. des.
          eapply LB.
          { eapply MLETGT in H. eapply MEMWF in H. des; auto. }
          { dup H. apply memory_get_ts_strong in H. des; auto.
            subst. erewrite BOTNONETGT in H1. clarify. } }
        { econs; eauto. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_src' ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst.
            dup H. apply MLETGT in H. rewrite H.
            econs; eauto.
            { ii. des; eauto. apply EXCLUSIVE in H2. rewrite H2 in *. clarify. }
            { ii. des.
              { eapply EXCLUSIVEEXTRA in H2. rewrite H2 in *. clarify. }
              { exfalso. eapply NEXTRA; eauto. }
            }
            { left. eapply sim_memory_wf; eauto. ss. eauto. }
            { i. apply MEM.(sim_memory_wf). ss. }
            { i. ss. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite H. econs; eauto. }
            { guardH o. set (PROM:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }

      { hexploit (@Memory.add_exists mem_src' loc from_tgt ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MLETGT. eapply H. }
          { eapply GET2. }
          { instantiate (1:=x). eauto. }
          { eauto. }
          i. destruct H2 as [EQ|[EQ [FORGET [EXTRA TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA.
            eapply H1. esplits; eauto. }
        }
        { apply memory_get_ts_strong in H. des; auto. subst.
          erewrite BOTNONESRC in H0. clarify. }
        { econs. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_tgt ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst.
            dup H. apply MLETGT in H. rewrite H.
            econs; eauto.
            { ii. des; eauto. apply EXCLUSIVE in H3. rewrite H3 in *. clarify. }
            { ii. des.
              { eapply EXCLUSIVEEXTRA in H3. rewrite H3 in *. clarify. }
              { exfalso. eapply NEXTRA; eauto. }
            }
            { refl. }
            { i. apply eq_lb_time. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite H. eauto. }
            { guardH o. set (PROM:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }
    }

    { clear LIN. symmetry in H. symmetry in H0.
      assert (FROM: Time.le from_tgt from_src).
      { apply MLESRC in H0. apply MLETGT in H.
        set (MEM0:=MEM.(sim_memory_contents) loc ts).
        rewrite H in *. rewrite H0 in *. inv MEM0. auto. }
      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { left. exploit sim_memory_from_forget; eauto. ss. auto. }

      hexploit (@Memory.remove_exists prom_src); eauto.
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src); eauto.
      intros [mem_src' REMOVEMEM].
      assert (REMOVE: Memory.promise prom_src mem_src loc from_src ts Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      destruct (classic (exists from_src', (extra_others \3/ extra_self) loc from_src' from_tgt))
        as [[from_src' EXTRA]|].
      { guardH EXTRA.
        hexploit (@Memory.add_exists mem_src' loc from_src' ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MLETGT. eapply H. }
          { eapply GET2. }
          { instantiate (1:=x). inv LHS. econs; ss.
            transitivity from_src'; auto.
            eapply MEM.(sim_memory_wf) in EXTRA. des; auto. }
          { eauto. }
          i. destruct H1 as [EQ|[EQ [FORGET [EXTRA0 TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA0.
            hexploit sim_memory_extra_inj.
            { eapply MEM. }
            { eapply EXTRA0. }
            { eapply EXTRA. }
            i. subst. inv LHS. inv RHS. ss. timetac. }
        }
        { eapply MEM.(sim_memory_wf) in EXTRA. destruct EXTRA as [_ EXTRA]. des.
          eapply LB.
          { eapply MLETGT in H. eapply MEMWF in H. des; auto. }
          { dup H. apply memory_get_ts_strong in H. des; auto.
            subst. erewrite BOTNONETGT in H1. clarify. } }
        { econs; eauto. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_src' ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst.
            dup H. apply MLETGT in H. rewrite H.
            econs; eauto.
            { ii. des.
              { eapply EXCLUSIVEEXTRA in H2. rewrite H2 in *. clarify. }
              { exfalso. eapply NEXTRA; eauto. } }
            { left. eapply sim_memory_wf; eauto. ss. eauto. }
            { i. apply MEM.(sim_memory_wf). ss. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite H. econs; eauto. }
            { guardH o. set (PROM0:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM0:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }

      { hexploit (@Memory.add_exists mem_src' loc from_tgt ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MLETGT. eapply H. }
          { eapply GET2. }
          { instantiate (1:=x). eauto. }
          { eauto. }
          i. destruct H2 as [EQ|[EQ [FORGET [EXTRA TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA.
            eapply H1. esplits; eauto. }
        }
        { apply memory_get_ts_strong in H. des; auto. subst.
          erewrite BOTNONESRC in H0. clarify. }
        { econs. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_tgt ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst.
            dup H. apply MLETGT in H. rewrite H.
            econs; eauto.
            { ii. des; eauto.
              { eapply EXCLUSIVEEXTRA in H3. rewrite H3 in *. clarify. }
              { exfalso. eapply NEXTRA; eauto. } }
            { refl. }
            { apply eq_lb_time. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite H. eauto. }
            { guardH o. set (PROM0:=SIM.(sim_promise_list_contents) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM0:=SIM.(sim_promise_list_extra) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }
    }
    { left. econs 5; eauto. }
  Qed.


  Lemma sim_promise_step_forget others self extra_others extra_self
        mem_src mem_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (LOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)

        (MEMWF: memory_times_wf mem_tgt')
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            Memory.get loc' ts' prom_src = None)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (EXTRA: extra_others loc' ts' from'),
            Memory.get loc' ts' prom_src = None)
    :
      exists prom_src' mem_src' self' extra_self',
        (<<STEPSRC: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self') (extra_others \3/ extra_self') mem_src' mem_tgt'>>) /\
        (<<PROMISE: sim_promise self' extra_self' prom_src' prom_tgt'>>)
  .
  Proof.
    inv STEPTGT.

    - admit.

    - des. subst.
      exploit split_succeed_wf; try apply PROMISES. i. des.
      dup GET2. apply MLETGT in GET0.
      set (PROM:=PROMISE.(sim_promise_contents) loc ts3).
      rewrite GET2 in PROM.

      set (MEM1:=MEM.(sim_memory_contents) loc ts3). rewrite GET0 in MEM1.

      assert (exists from_src,
                 (<<GETSRC: Memory.get loc ts3 prom_src = Some (from_src, Message.reserve)>>) /\
                 (<<LB: lb_time (times loc) from from_src>>) /\
                 (<<FROM: Time.le from from_src>>)).
      { inv PROM; ss.
        { symmetry in H0. apply MLESRC in H0.
          rewrite H0 in *. inv MEM1. esplits; eauto. }
        { symmetry in H0. apply MLESRC in H0.
          rewrite H0 in *. inv MEM1. esplits; eauto. }
      } des.
      assert (TS0: Time.lt from_src to).
      { eapply LB; auto.
        apply Memory.split_get0 in MEM0. des.
        eapply MEMWF in GET4. des. auto. }

      assert (NEXTRATO: forall t, ~ (extra_others loc to t \/ extra_self loc to t)).
      { set (MEM2:=MEM.(sim_memory_contents) loc to).
        inv MEM2; ss. guardH EXTRA. exfalso.
        hexploit memory_get_disjoint_strong.
        { symmetry. apply H0. }
        { apply MLESRC. apply GETSRC. }
        i. des; subst.
        { timetac. }
        { timetac. }
        { eapply Time.lt_strorder. transitivity to; eauto. }
      }

      hexploit (@Memory.remove_exists prom_src loc from_src ts3 Message.reserve).
      { eauto. }
      intros [prom_src0 REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src loc from_src ts3 Message.reserve); eauto.
      intros [mem_src0 REMOVEMEM].
      assert (PROMISE0: Memory.promise prom_src mem_src loc from_src ts3 Message.reserve prom_src0 mem_src0 Memory.op_kind_cancel).
      { econs; eauto. }

      hexploit (@Memory.add_exists mem_src0 loc from_src to Message.reserve); auto.
      { i. erewrite Memory.remove_o in GET1; eauto. des_ifs. guardH o.
        hexploit Memory.get_disjoint.
        { eapply GET1. }
        { eapply MLESRC. eapply GETSRC. }
        i. des; clarify.
        { ss. destruct o; ss. }
        { ii. eapply H; eauto. inv LHS. econs; ss.
          etrans; eauto. left. auto. }
      }
      { econs. }
      intros [mem_src1 ADDMEM1].
      hexploit (@Memory.add_exists_le prom_src0 mem_src0 loc from_src to Message.reserve); eauto.
      { eapply promise_memory_le; try apply PROMISE0; eauto. }
      intros [prom_src1 ADDPROM1].
      assert (PROMISE1: Memory.promise prom_src0 mem_src0 loc from_src to Message.reserve prom_src1 mem_src1 Memory.op_kind_add).
      { econs; eauto. i. clarify. }
      hexploit (@Memory.add_exists mem_src1 loc to ts3 Message.reserve); auto.
      { i. erewrite Memory.add_o in GET1; eauto. des_ifs.
        { ss. des; subst. ii. inv LHS. inv RHS. ss. timetac. }
        { erewrite Memory.remove_o in GET1; eauto. des_ifs. guardH o.
          hexploit Memory.get_disjoint.
          { eapply GET1. }
          { eapply MLESRC. eapply GETSRC. }
          i. des; clarify.
          ii. eapply H; eauto. inv LHS. econs; ss.
          etrans; eauto. }
      }
      { econs. }
      intros [mem_src2 ADDMEM2].
      hexploit (@Memory.add_exists_le prom_src1 mem_src1 loc to ts3 Message.reserve); eauto.
      { eapply promise_memory_le; try apply PROMISE1; eauto.
        eapply promise_memory_le; try apply PROMISE0; eauto. }
      intros [prom_src2 ADDPROM2].
      assert (PROMISE2: Memory.promise prom_src1 mem_src1 loc to ts3 Message.reserve prom_src2 mem_src2 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      exists prom_src2, mem_src2,
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'), extra_self. splits; auto.
      { eauto. }
      { econs.
        { i. erewrite (@Memory.split_o mem_tgt'); eauto.
          erewrite (@Memory.add_o mem_src2); eauto.
          erewrite (@Memory.add_o mem_src1); eauto.
          erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
          { ss. des; subst. exfalso. eapply Time.lt_strorder; eauto. }
          { ss. des; clarify. econs 3; auto. }
          { ss. des; clarify. inv PROM; ss.
            { inv MEM1. econs 2; eauto.
              { refl. }
              { i. apply eq_lb_time. } }
            { dup H0. symmetry in H0. apply MLESRC in H0.
              rewrite H0 in *. inv MEM1.
              econs 3; eauto.
              { refl. }
              { i. apply eq_lb_time. }
            }
          }
          { eapply (MEM.(sim_memory_contents)). }
        }
        { i. dup EXTRA.
          apply (MEM.(sim_memory_wf)) in EXTRA0. des_ifs.
          destruct a. ss. subst. splits; try apply EXTRA0; auto. }
      }
      { econs.
        { i. erewrite (@Memory.split_o prom_tgt'); eauto.
          erewrite (@Memory.add_o prom_src2); eauto.
          erewrite (@Memory.add_o prom_src1); eauto.
          erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
          { ss. des; subst. exfalso. eapply Time.lt_strorder; eauto. }
          { ss. des; clarify. econs 4; auto.
            ii. eapply NEXTRATO. eauto. }
          { ss. des; clarify. inv PROM; ss.
            { inv MEM1. econs 3; eauto. }
            { econs 4; eauto. }
          }
          { eapply (PROMISE.(sim_promise_contents)). }
        }
        { i. dup EXTRA.
          apply (PROMISE.(sim_promise_wf)) in EXTRA0. des_ifs.
          destruct a. ss. subst. splits; try apply EXTRA0; auto. }
        { i. des_ifs.
          { ss. des. subst.
            eapply Memory.add_get0 in ADDPROM2. des. esplits; eauto. }
          { guardH o. apply PROMISE.(sim_promise_extra) in SELF. des.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; subst. clarify.
              eapply Memory.add_get0 in ADDPROM1. des.
              eapply Memory.add_get1 in GET3; eauto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. exfalso.
              hexploit memory_get_disjoint_strong.
              { eapply GET. }
              { eapply GETSRC. }
              i. des; clarify.
              { timetac. }
              { eapply Time.lt_strorder; eauto. }
            }
            { guardH o0. guardH o1. exists to0. splits; auto.
              erewrite (@Memory.add_o prom_src2); eauto.
              erewrite (@Memory.add_o prom_src1); eauto.
              erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
              { ss. des; subst. destruct o0; ss. }
              { ss. destruct a; subst. destruct o1; ss. }
            }
          }
        }
      }

    - des. subst.
      exploit lower_succeed_wf; try apply PROMISES. i. des. inv MSG_LE.
      rename GET into GETPROMTGT.
      dup GETPROMTGT. apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.
      set (PROM:=PROMISE.(sim_promise_contents) loc to).
      rewrite GETPROMTGT in PROM. inv PROM; ss.
      symmetry in H0. dup H0. apply MLESRC in H0.
      rename H0 into GETMEMSRC. rename H1 into GETPROMSRC.
      set (MEM1:=MEM.(sim_memory_contents) loc to).
      rewrite GETMEMSRC in MEM1. rewrite GETMEMTGT in MEM1. inv MEM1. clear PROM.

      exists prom_src, mem_src, self, extra_self. splits; auto.
      { econs.
        { i. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
          { ss. des; subst. rewrite GETMEMSRC. econs; eauto. }
          { eapply MEM.(sim_memory_contents). }
        }
        { apply MEM.(sim_memory_wf). }
      }
      { econs.
        { i. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
          { ss. des; subst. rewrite GETPROMSRC. econs; eauto. }
          { eapply PROMISE.(sim_promise_contents). }
        }
        { apply PROMISE.(sim_promise_wf). }
        { apply PROMISE.(sim_promise_extra). }
      }

    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      rename GET into GETPROMTGT.
      dup GETPROMTGT. apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.
      set (PROM:=PROMISE.(sim_promise_contents) loc to).
      rewrite GETPROMTGT in PROM. inv PROM; ss.
      symmetry in H0. dup H0. apply MLESRC in H0.
      rename H0 into GETMEMSRC. rename H1 into GETPROMSRC.
      set (MEM1:=MEM.(sim_memory_contents) loc to).
      rewrite GETMEMSRC in MEM1. rewrite GETMEMTGT in MEM1. inv MEM1.

      hexploit (@Memory.remove_exists prom_src loc from_src to Message.reserve).
      { eauto. }
      intros [prom_src0 REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src loc from_src to Message.reserve); eauto.
      intros [mem_src0 REMOVEMEM].
      assert (PROMISE0: Memory.promise prom_src mem_src loc from_src to Message.reserve prom_src0 mem_src0 Memory.op_kind_cancel).
      { econs; eauto. }

      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { exploit sim_memory_from_forget; eauto.
        { ss. auto. } i. subst.
        assert (TS: Time.lt from to).
        { apply memory_get_ts_strong in GETPROMSRC. des; auto.
          subst. clarify. }
        assert (exists ts', (<<LB: lb_time (times loc) from ts'>>) /\
                            (<<TS0: Time.lt from ts'>>) /\
                            (<<TS1: Time.lt ts' to>>)).
        { hexploit (lb_time_exists (times loc) from). i. des.
          destruct (Time.le_lt_dec ts' (Time.middle from to)).
          { exists ts'. splits; auto.
            eapply TimeFacts.le_lt_lt; eauto. eapply Time.middle_spec; eauto. }
          { exists (Time.middle from to). splits; auto.
            { eapply lb_time_lower; eauto. left. auto. }
            { eapply Time.middle_spec; eauto. }
            { eapply Time.middle_spec; eauto. }
          }
        } des.
        hexploit (@Memory.add_exists mem_src0 loc from ts' Message.reserve); eauto.
        { admit. }
        { econs. }
        intros [mem_src1 ADDMEM].
        hexploit (@Memory.add_exists_le prom_src0 mem_src0 loc from ts' Message.reserve); eauto.
        { eapply promise_memory_le; try apply PROMISE0; eauto. }
        intros [prom_src1 ADDPROM].
        assert (PROMISE1: Memory.promise prom_src0 mem_src0 loc from ts' Message.reserve prom_src1 mem_src1 Memory.op_kind_add).
        { econs; eauto. i. clarify. }

        hexploit sim_memory_src_none.
        { eauto. }
        { instantiate (1:=ts'). instantiate (1:=loc).
          destruct (Memory.get loc ts' mem_src) eqn:GET; auto. destruct p.
          hexploit memory_get_disjoint_strong.
          { eapply GET. }
          { eapply GETMEMSRC. } i. des; subst.
          { timetac. }
          { timetac. }
          { exfalso. eapply Time.lt_strorder.
            transitivity ts'; eauto. }
        } i. des.

        exists prom_src1, mem_src1, self,
        (fun l t => if (loc_ts_eq_dec (l, t) (loc, ts'))
                    then (eq from)
                    else extra_self l t). splits; eauto.
        { econs.
          { i. erewrite (@Memory.remove_o mem_tgt'); eauto.
            erewrite (@Memory.add_o mem_src1); eauto.
            erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. rewrite GETTGT. econs 4; eauto. }
            { ss. des; clarify. eauto. }
            { eapply MEM.(sim_memory_contents). }
          }
          { i. set (WF:=MEM.(sim_memory_wf) loc0 from0 ts). des_ifs.
            { destruct a. ss. clarify. des.
              { hexploit WF; eauto.  i.
                destruct H as [FORGET EXTRA0]. guardH FORGET. des.
                splits; auto. i. des_ifs.
                { admit.
                }
                { admit. }
              }
              admit.
            }
            { guardH o. eapply MEM.(sim_memory_wf) in EXTRA.
              destruct EXTRA as [FORGET EXTRA]. guardH FORGET. des. splits; auto.
              i. des_ifs.
              {


                  destruct EXTRA0; auto.
                  admit.
                }


                des_ifs; des; auto.

                des_ifs.
                { auto.

                splits; auto.

              guardH a. ss.

            apply MEM.(sim_memory_wf). }
        }
        { econs.
          { i. erewrite (@Memory.remove_o prom_tgt'); eauto.
            erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
            { ss. des; subst. eauto. }
            { eapply PROMISE.(sim_promise_contents). }
          }
          { apply PROMISE.(sim_promise_wf). }
          { i. dup SELF. apply PROMISE.(sim_promise_extra) in SELF. des.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. }
            { exists to0. splits; auto. erewrite Memory.remove_o; eauto. des_ifs.
              ss. des; clarify. }
          }
        }
      }


        {


        cycle 1; eauto. }

          admit. }
        { econs. }

          econs.





        admit. }

      { exists prom_src0, mem_src0, self, extra_self. splits; eauto.
        { econs.
          { i. erewrite (@Memory.remove_o mem_tgt'); eauto.
            erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
            { ss. des; subst. eauto. }
            { eapply MEM.(sim_memory_contents). }
          }
          { apply MEM.(sim_memory_wf). }
        }
        { econs.
          { i. erewrite (@Memory.remove_o prom_tgt'); eauto.
            erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
            { ss. des; subst. eauto. }
            { eapply PROMISE.(sim_promise_contents). }
          }
          { apply PROMISE.(sim_promise_wf). }
          { i. dup SELF. apply PROMISE.(sim_promise_extra) in SELF. des.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. }
            { exists to0. splits; auto. erewrite Memory.remove_o; eauto. des_ifs.
              ss. des; clarify. }
          }
        }
      }


      {

      assert (PROMISE0: Memory.promise prom_src mem_src loc from_src ts3 Message.reserve prom_src0 mem_src0 Memory.op_kind_cancel).
      { econs; eauto. }


      hexploit


      exists prom_src, mem_src, self, extra_self. splits; auto.
      { econs.
        { i. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
          { ss. des; subst. rewrite GETMEMSRC. econs; eauto. }
          { eapply MEM.(sim_memory_contents). }
        }
        { apply MEM.(sim_memory_wf). }
      }
      { econs.
        { i. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
          { ss. des; subst. rewrite GETPROMSRC. econs; eauto. }
          { eapply PROMISE.(sim_promise_contents). }
        }
        { apply PROMISE.(sim_promise_wf). }
        { apply PROMISE.(sim_promise_extra). }
      }


    -

      exists prom_src, mem_src, self, extra_self. splits; auto.
      { econs.
        { i. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
          { ss. des; subst.
            set (MEM1:=MEM.(sim_memory_contents) loc to).
            apply MLETGT in GET. rewrite GET in MEM1.


            inv MEM1.

            inv MEM1; eauto.
            econs 2.


            { econs; eauto.
            erewrite (@Memory.lower_get0) in MEM1.

            inv MEM1; e

            admit. }
          { eapply MEM.(sim_memory_contents). }
        }
        { apply MEM.(sim_memory_wf). }
      }
      { econs.
        { i. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
          {

            admit. }
          { eapply PROMISE.(sim_promise_contents). }
        }
        { apply PROMISE.(sim_promise_wf). }
        { apply PROMISE.(sim_promise_extra). }
      }


      i.



      exploit lower_succeed_wf; try apply PROMISES. i. des.
      rename GET into GETPROMTGT.
      dup GETPROMTGT. apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.
      set (PROM:=PROMISE.(sim_promise_contents) loc to).
      rewrite GETPROMTGT in PROM. inv PROM; ss.
      symmetry in H0. dup H0. apply WFSRC in H0.
      rename H0 into GETMEMSRC. rename H1 into GETPROMSRC.
      set (MEM1:=MEM.(sim_memory_contents) loc to).
      rewrite GETMEMSRC in MEM1. rewrite GETMEMTGT in MEM1. inv MEM1.


      inv MEM1; ss.

      assert (exists from_src,
                 (<<GETSRC: Memory.get loc ts3 prom_src = Some (from_src, Message.reserve)>>) /\
                 (<<LB: lb_time (times loc) from from_src>>) /\
                 (<<FROM: Time.le from from_src>>)).
      { inv PROM; ss.
        { symmetry in H0. apply WFSRC in H0.
          rewrite H0 in *. inv MEM1. esplits; eauto. }
        { symmetry in H0. apply WFSRC in H0.
          rewrite H0 in *. inv MEM1. esplits; eauto. }
      } des.
      assert (TS0: Time.lt from_src to).
      { eapply LB; auto.
        apply Memory.split_get0 in MEM0. des.
        eapply MEMWF in GET4. des. auto. }

      assert (NEXTRATO: forall t, ~ (extra_others loc to t \/ extra_self loc to t)).
      { set (MEM2:=MEM.(sim_memory_contents) loc to).
        inv MEM2; ss. guardH EXTRA. exfalso.
        hexploit memory_get_disjoint_strong.
        { symmetry. apply H0. }
        { apply WFSRC. apply GETSRC. }
        i. des; subst.
        { timetac. }
        { timetac. }
        { eapply Time.lt_strorder. transitivity to; eauto. }
      }

      hexploit (@Memory.remove_exists prom_src loc from_src ts3 Message.reserve).
      { eauto. }
      intros [prom_src0 REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src loc from_src ts3 Message.reserve); eauto.
      intros [mem_src0 REMOVEMEM].
      assert (PROMISE0: Memory.promise prom_src mem_src loc from_src ts3 Message.reserve prom_src0 mem_src0 Memory.op_kind_cancel).
      { econs; eauto. }

      hexploit (@Memory.add_exists mem_src0 loc from_src to Message.reserve); auto.
      { i. erewrite Memory.remove_o in GET1; eauto. des_ifs. guardH o.
        hexploit Memory.get_disjoint.
        { eapply GET1. }
        { eapply WFSRC. eapply GETSRC. }
        i. des; clarify.
        { ss. destruct o; ss. }
        { ii. eapply H; eauto. inv LHS. econs; ss.
          etrans; eauto. left. auto. }
      }
      { econs. }
      intros [mem_src1 ADDMEM1].
      hexploit (@Memory.add_exists_le prom_src0 mem_src0 loc from_src to Message.reserve); eauto.
      { eapply promise_memory_le; try apply PROMISE0; eauto. }
      intros [prom_src1 ADDPROM1].
      assert (PROMISE1: Memory.promise prom_src0 mem_src0 loc from_src to Message.reserve prom_src1 mem_src1 Memory.op_kind_add).
      { econs; eauto. i. clarify. }
      hexploit (@Memory.add_exists mem_src1 loc to ts3 Message.reserve); auto.
      { i. erewrite Memory.add_o in GET1; eauto. des_ifs.
        { ss. des; subst. ii. inv LHS. inv RHS. ss. timetac. }
        { erewrite Memory.remove_o in GET1; eauto. des_ifs. guardH o.
          hexploit Memory.get_disjoint.
          { eapply GET1. }
          { eapply WFSRC. eapply GETSRC. }
          i. des; clarify.
          ii. eapply H; eauto. inv LHS. econs; ss.
          etrans; eauto. }
      }
      { econs. }
      intros [mem_src2 ADDMEM2].
      hexploit (@Memory.add_exists_le prom_src1 mem_src1 loc to ts3 Message.reserve); eauto.
      { eapply promise_memory_le; try apply PROMISE1; eauto.
        eapply promise_memory_le; try apply PROMISE0; eauto. }
      intros [prom_src2 ADDPROM2].
      assert (PROMISE2: Memory.promise prom_src1 mem_src1 loc to ts3 Message.reserve prom_src2 mem_src2 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      exists prom_src2, mem_src2,
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'), extra_self. splits; auto.
      { eauto. }
      { econs.
        { i. erewrite (@Memory.split_o mem_tgt'); eauto.
          erewrite (@Memory.add_o mem_src2); eauto.
          erewrite (@Memory.add_o mem_src1); eauto.
          erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
          { ss. des; subst. exfalso. eapply Time.lt_strorder; eauto. }
          { ss. des; clarify. econs 3; auto. }
          { ss. des; clarify. inv PROM; ss.
            { inv MEM1. econs 2; eauto.
              { refl. }
              { i. apply eq_lb_time. } }
            { dup H0. symmetry in H0. apply WFSRC in H0.
              rewrite H0 in *. inv MEM1.
              econs 3; eauto.
              { refl. }
              { i. apply eq_lb_time. }
            }
          }
          { eapply (MEM.(sim_memory_contents)). }
        }
        { i. dup EXTRA.
          apply (MEM.(sim_memory_wf)) in EXTRA0. des_ifs.
          destruct a. ss. subst. splits; try apply EXTRA0; auto. }
      }
      { econs.
        { i. erewrite (@Memory.split_o prom_tgt'); eauto.
          erewrite (@Memory.add_o prom_src2); eauto.
          erewrite (@Memory.add_o prom_src1); eauto.
          erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
          { ss. des; subst. exfalso. eapply Time.lt_strorder; eauto. }
          { ss. des; clarify. econs 4; auto.
            ii. eapply NEXTRATO. eauto. }
          { ss. des; clarify. inv PROM; ss.
            { inv MEM1. econs 3; eauto. }
            { econs 4; eauto. }
          }
          { eapply (PROMISE.(sim_promise_contents)). }
        }
        { i. dup EXTRA.
          apply (PROMISE.(sim_promise_wf)) in EXTRA0. des_ifs.
          destruct a. ss. subst. splits; try apply EXTRA0; auto. }
        { i. des_ifs.
          { ss. des. subst.
            eapply Memory.add_get0 in ADDPROM2. des. esplits; eauto. }
          { guardH o. apply PROMISE.(sim_promise_extra) in SELF. des.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, ts3)).
            { ss. des; subst. clarify.
              eapply Memory.add_get0 in ADDPROM1. des.
              eapply Memory.add_get1 in GET3; eauto. }
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. exfalso.
              hexploit memory_get_disjoint_strong.
              { eapply GET. }
              { eapply GETSRC. }
              i. des; clarify.
              { timetac. }
              { eapply Time.lt_strorder; eauto. }
            }
            { guardH o0. guardH o1. exists to0. splits; auto.
              erewrite (@Memory.add_o prom_src2); eauto.
              erewrite (@Memory.add_o prom_src1); eauto.
              erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
              { ss. des; subst. destruct o0; ss. }
              { ss. destruct a; subst. destruct o1; ss. }
            }
          }
        }
      }



    }

              ss.

                admit. }

              erewrie


              erewr

              exists


              esplits; eauto.

            destruct

            esplits; eauto.

            esplits; eauto.
            eapply Memory.add_get0 in ADDPROM2. des.

      }


        {

          splits; auto.
          guardH EXTRA. guardH FORGET. des. ss. subst. splits; auto. }

          des_ifs.

          des_ifs.



      inv MEM1.
          rew

          clarif

          inv MEM1.

          set (MEM1:=MEM.(sim_memory_contents) loc ts3).
          rewrite

          inv MEM1; ss.

          inv MEM

          { admit. }
          eauto.

        eauto.


      { inv PROMISE0; eauto. clarify. } des. rewrite GETSRC in *.

      assert (EMPTY0: forall ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3),
                 Memory.get loc ts' mem_tgt = None).
      { i. destruct (Memory.get loc ts' mem_tgt) as [[from' msg']|] eqn:GET; auto.
        exfalso. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - eapply x0.
          + instantiate (1:=ts'). econs; ss; [|refl].
            apply memory_get_ts_strong in GET. des; clarify; auto.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            * eapply TS0.
            * eapply Time.bot_spec.
          + econs; ss. left. auto. }

      assert (EMPTY1: forall to' msg' ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3)
                             (GET: Memory.get loc to' mem_tgt = Some (ts', msg')),
                 False).
      { i. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - hexploit memory_get_to_mon.
          { eapply GET0. }
          { eapply GET. }
          { auto. } i.
          eapply x0.
          + instantiate (1:=ts3). econs; ss. left. auto.
          + econs; ss; [|refl]. etrans; eauto. }

      exploit (@promises_not_attached_replace_split self loc from_src (Time.middle from to) to ts3 prom_src mem_src); auto.
      { i. specialize (PROMISE loc to0). rewrite GET in *. inv PROMISE; clarify. }
      { eapply (@TimeFacts.le_lt_lt _ from); eauto. eapply Time.bot_spec. }
      { eapply Time.middle_spec; eauto. }
      { ii. inv H.
        assert (exists from0' msg', <<GETTGT: Memory.get loc to0 mem_tgt = Some (from0', msg')>> /\ <<TS: Time.le from0' from0>>).
        { dup MEM. specialize (MEM loc to0). rewrite GET in MEM. inv MEM; eauto. } des.
        assert (TS1: Time.lt to0 ts3).
        { eapply memory_get_to_mon; try apply GET; eauto.
          inv ITV0. inv ITV. ss. eapply TimeFacts.lt_le_lt; eauto. }
        erewrite EMPTY0 in GETTGT.
        - clarify.
        - inv ITV. inv ITV0. ss. eapply TimeFacts.lt_le_lt.
          { eapply Time.middle_spec; eauto. }
          { left. eapply TimeFacts.lt_le_lt; eauto. }
        - auto.
      }

      intros [prom_src' [mem_src' ?]]. des.

      assert (PROMISEDDIFF: promised prom_src' =
                            fun loc' =>
                              if (Loc.eq_dec loc' loc)
                              then fun ts' => if (Time.eq_dec ts' to) then True else promised prom_src loc' ts'
                              else promised prom_src loc').
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H. erewrite PROMSPEC in GET. des_ifs; try by (ss; des; clarify).
          + ss. des; clarify. econs; eauto.
          + ss. des; clarify. econs; eauto.
          + econs; eauto.
        - specialize (PROMSPEC loc' ts'). des_ifs; try by (ss; des; clarify).
          + econs; eauto.
          + econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'). splits; auto.
      + ii. erewrite MEMSPEC.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs 3; eauto.
          { left. apply Time.middle_spec; eauto. }
        * ss. des; clarify.
          specialize (MEM loc ts3). rewrite GET0 in *.
          apply WFSRC in GETSRC. rewrite GETSRC in *. inv MEM; eauto.
          { econs 2; eauto. refl. }
          { econs 3; eauto. refl. }
      + ii. erewrite MEMSPEC in GET. des_ifs.
        * ss. des; clarify. exfalso.
          specialize (MEM loc (Time.middle from to)).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H.
          { clarify. }
          { eapply Time.middle_spec; eauto. }
          { etrans; eauto. eapply Time.middle_spec; eauto. }
        * ss. des; clarify. exfalso.
          specialize (MEM loc from0).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H; auto.
          { clarify. }
        * eauto.
      + ii. erewrite PROMSPEC.
        erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. inv PROMISE0; eauto.
      + ii. erewrite MEMSPEC in GET. erewrite PROMISEDDIFF.
        des_ifs; eauto; try by (ss; des; clarify).
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. exfalso.
          exploit (@memory_get_from_inj mem_src' loc to ts1 ts3 msg Message.reserve).
          { erewrite MEMSPEC. des_ifs; ss; des; clarify. }
          { erewrite MEMSPEC. des_ifs; ss; des; clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          i. des; clarify.
          { eapply Time.lt_strorder; eauto. }


      rewrite GET2 in PROMISE0.




    - hexploit add_succeed_wf; try apply MEM0. i. des.

      destruct (classic

      assert (

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
                       then msg_tgt <> Message.reserve else self loc' ts').
      splits; auto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. destruct msg_tgt.
          { econs 3; eauto.
            - right. clarify.
            - left. eapply Time.middle_spec; eauto. }
          { econs 2; eauto.
            - ii. des; eauto. exfalso.
              specialize (MEM loc to). eapply Memory.add_get0 in ADDMEM.
              des. rewrite GET in *. inv MEM. eauto.
            - left. eapply Time.middle_spec; eauto.
            - i. clarify.
          }
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
        ss. des; clarify. destruct msg_tgt.
        * econs 4; eauto. clarify.
        * econs 3; eauto.
      + ii. erewrite promised_add; eauto.
        erewrite Memory.add_o in GET; eauto.
        destruct msg_tgt; cycle 1.
        { des_ifs; eauto; try by (ss; des; clarify). }
        des_ifs; eauto; ss; des; clarify.
        specialize (MEM loc ts1). rewrite GET in *. inv MEM.
        { exfalso. destruct FROM.
          { exploit DISJOINT.
            - symmetry. eapply H.
            - instantiate (1:=to). econs; ss. refl.
            - econs; ss. apply memory_get_ts_le in GET; eauto.
            - auto. }
          { inv H0. exfalso. eapply ATTACH; eauto. }
        }
        { exfalso. destruct FROM.
          { exploit DISJOINT.
            - symmetry. eapply H.
            - instantiate (1:=to). econs; ss. refl.
            - econs; ss. apply memory_get_ts_le in GET; eauto.
            - auto. }
          { inv H0. exfalso. eapply ATTACH; eauto. }
        }

    - des. clarify.
      exploit split_succeed_wf; try apply PROMISES. i. des.
      dup GET2. apply WFTGT in GET0.
      dup PROMISE. specialize (PROMISE0 loc ts3).
      rewrite GET2 in PROMISE0.

      assert (exists from_src, <<GETSRC: Memory.get loc ts3 prom_src = Some (from_src, Message.reserve)>>).
      { inv PROMISE0; eauto. clarify. } des. rewrite GETSRC in *.

      assert (EMPTY0: forall ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3),
                 Memory.get loc ts' mem_tgt = None).
      { i. destruct (Memory.get loc ts' mem_tgt) as [[from' msg']|] eqn:GET; auto.
        exfalso. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - eapply x0.
          + instantiate (1:=ts'). econs; ss; [|refl].
            apply memory_get_ts_strong in GET. des; clarify; auto.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            * eapply TS0.
            * eapply Time.bot_spec.
          + econs; ss. left. auto. }

      assert (EMPTY1: forall to' msg' ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3)
                             (GET: Memory.get loc to' mem_tgt = Some (ts', msg')),
                 False).
      { i. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - hexploit memory_get_to_mon.
          { eapply GET0. }
          { eapply GET. }
          { auto. } i.
          eapply x0.
          + instantiate (1:=ts3). econs; ss. left. auto.
          + econs; ss; [|refl]. etrans; eauto. }

      exploit (@promises_not_attached_replace_split self loc from_src (Time.middle from to) to ts3 prom_src mem_src); auto.
      { i. specialize (PROMISE loc to0). rewrite GET in *. inv PROMISE; clarify. }
      { eapply (@TimeFacts.le_lt_lt _ from); eauto. eapply Time.bot_spec. }
      { eapply Time.middle_spec; eauto. }
      { ii. inv H.
        assert (exists from0' msg', <<GETTGT: Memory.get loc to0 mem_tgt = Some (from0', msg')>> /\ <<TS: Time.le from0' from0>>).
        { dup MEM. specialize (MEM loc to0). rewrite GET in MEM. inv MEM; eauto. } des.
        assert (TS1: Time.lt to0 ts3).
        { eapply memory_get_to_mon; try apply GET; eauto.
          inv ITV0. inv ITV. ss. eapply TimeFacts.lt_le_lt; eauto. }
        erewrite EMPTY0 in GETTGT.
        - clarify.
        - inv ITV. inv ITV0. ss. eapply TimeFacts.lt_le_lt.
          { eapply Time.middle_spec; eauto. }
          { left. eapply TimeFacts.lt_le_lt; eauto. }
        - auto.
      }

      intros [prom_src' [mem_src' ?]]. des.

      assert (PROMISEDDIFF: promised prom_src' =
                            fun loc' =>
                              if (Loc.eq_dec loc' loc)
                              then fun ts' => if (Time.eq_dec ts' to) then True else promised prom_src loc' ts'
                              else promised prom_src loc').
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H. erewrite PROMSPEC in GET. des_ifs; try by (ss; des; clarify).
          + ss. des; clarify. econs; eauto.
          + ss. des; clarify. econs; eauto.
          + econs; eauto.
        - specialize (PROMSPEC loc' ts'). des_ifs; try by (ss; des; clarify).
          + econs; eauto.
          + econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'). splits; auto.
      + ii. erewrite MEMSPEC.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs 3; eauto.
          { left. apply Time.middle_spec; eauto. }
        * ss. des; clarify.
          specialize (MEM loc ts3). rewrite GET0 in *.
          apply WFSRC in GETSRC. rewrite GETSRC in *. inv MEM; eauto.
          { econs 2; eauto. refl. }
          { econs 3; eauto. refl. }
      + ii. erewrite MEMSPEC in GET. des_ifs.
        * ss. des; clarify. exfalso.
          specialize (MEM loc (Time.middle from to)).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H.
          { clarify. }
          { eapply Time.middle_spec; eauto. }
          { etrans; eauto. eapply Time.middle_spec; eauto. }
        * ss. des; clarify. exfalso.
          specialize (MEM loc from0).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H; auto.
          { clarify. }
        * eauto.
      + ii. erewrite PROMSPEC.
        erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. inv PROMISE0; eauto.
      + ii. erewrite MEMSPEC in GET. erewrite PROMISEDDIFF.
        des_ifs; eauto; try by (ss; des; clarify).
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. exfalso.
          exploit (@memory_get_from_inj mem_src' loc to ts1 ts3 msg Message.reserve).
          { erewrite MEMSPEC. des_ifs; ss; des; clarify. }
          { erewrite MEMSPEC. des_ifs; ss; des; clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          i. des; clarify.
          { eapply Time.lt_strorder; eauto. }

    - dup PROMISES. apply Memory.lower_get0 in PROMISES0. des. clarify.
      dup GET. apply WFTGT in GET1.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; clarify.
      exists prom_src, mem_src, self. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify.
        specialize (MEM loc to). rewrite GET1 in *. inv MSG_LE. inv MEM; eauto.
        { exfalso. eapply NPROM. auto. }
      + ii. eauto.
      + ii. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. inv MSG_LE. rewrite <- H0. econs 4; eauto.

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
      + ii. erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto.
        des_ifs; ss; des; clarify. econs. ii. des; clarify.
        eapply EXCLUSIVE; eauto. econs; eauto.
      + ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs. ss.
      + ii. erewrite Memory.remove_o in GET2; eauto.
        erewrite promised_remove; eauto. des_ifs; eauto.
        ss. des; clarify.
  Qed.


  Lemma sim_promise_fulfill others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt prom_tgt'
        loc from_tgt to val released from_src
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (BOTNONETGT: Memory.bot_none prom_tgt)
        (PROM: sim_promise self extra_self prom_src prom_tgt)

        (EMPTY: forall ts (ITV: Interval.mem (from', from) ts), ~ covered loc ts mem_src)
        (REMOVE: Memory.remove prom_tgt loc from to (Message.concrete val released) prom_tgt')

        (MEMWF: memory_times_wf mem_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            Memory.get loc' ts' prom_src = None)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (EXTRA: extra_others loc' ts' from'),
            Memory.get loc' ts' prom_src = None)
        (* (SELF: self <2= promised prom_src) *)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \3/ extra_self)
                   prom_src' prom_tgt>>).
  Proof.


  Lemma sim_write_step_normal
        others self extra_others extra_self lc_src lc_tgt sc mem_src mem_tgt
        lc_tgt' sc' mem_tgt' loc from to val ord releasedm released kind
        (NLOC: ~ L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind)
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (SIM: sim_local self extra_self lc_src lc_tgt)

        (RELEASEDMCLOSED: Memory.closed_opt_view releasedm mem_src)
        (RELEASEDMWF: View.opt_wf releasedm)

        (MEMWF: memory_times_wf mem_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            Memory.get loc' ts' prom_src = None)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (EXTRA: extra_others loc' ts' from'),
            Memory.get loc' ts' prom_src = None)
    :
      exists lc_src' mem_src',
        (<<STEPSRC: Local.write_step lc_src sc mem_src loc from to val releasedm released ord lc_src' sc' mem_src' kind>>) /\
        (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self extra_self lc_src' lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv WRITE. inv SIM. inv LOCALSRC. inv LOCALTGT.


  Lemma sim_promise_fulfill others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (BOTNONETGT: Memory.bot_none prom_tgt)
        (PROM: sim_promise self extra_self prom_src prom_tgt)
        (* (SELF: self <2= promised prom_src) *)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self) (extra_others \3/ extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \3/ extra_self)
                   prom_src' prom_tgt>>).
  Proof.

    Memory.write

  Lemma promise_replace_write self loc from from' to prom0 mem0 val released
        (LIN: L loc)
        (* (SELF: self <2= promised prom0) *)
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
    { econs; eauto. }
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




  Lemma promises_not_attached_replaces self loc ts prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (* (SELF: self <2= promised prom0) *)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot ts)
        (* (SELF: self loc ts) *)
        (PROMISED: promised prom0 loc ts)
    :
      exists prom1 mem1,
        (<<FUTURE01: reserve_future_memory prom0 mem0 prom1 mem1>>) /\
        (<<UNCH01: forall loc' to (TS: loc' = loc -> Time.le to ts),
            (<<MEM: Memory.get loc' to mem1 = Memory.get loc' to mem0>>) /\
            (<<PROM: Memory.get loc' to prom1 = Memory.get loc' to prom0>>)>>) /\

        (<<ATTACH: forall to msg (SELF: self loc ts) (GET: Memory.get loc to mem1 = Some (ts, msg)), False>>) /\
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
    destruct (classic (self loc ts)) as [SELF|NSELF]; cycle 1.
    { exists prom0, mem0. splits; eauto. i. esplits; eauto. }
    destruct (classic (exists to msg, <<GET: Memory.get loc to mem0 = Some (ts, msg)>>)); cycle 1.
    { exists prom0, mem0. splits; eauto. i. esplits; eauto. }
    des. exploit ATTACHED; eauto. i. inv x. destruct msg0 as [from msg0].
    dup GET0. apply MLE0 in GET1. clarify.
    exploit LOC; eauto. i. clarify.

    assert (TSTO: Time.lt ts to).
    { eapply memory_get_ts_strong in GET0. des; auto. clarify. }

    exploit Memory.remove_exists.
    { eapply GET0. }
    intros [prom1 REMOVEPROM].
    exploit Memory.remove_exists_le; eauto.
    intros [mem1 REMOVEMEM].

    assert (REMOVE: Memory.promise prom0 mem0 loc ts to Message.reserve prom1 mem1 Memory.op_kind_cancel).
    { econs; eauto. }
    exists prom1, mem1. splits; eauto.
    { i. erewrite (@Memory.remove_o mem1); eauto.
      erewrite (@Memory.remove_o prom1); eauto. des_ifs.
      ss. des; clarify.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
    }
    { i. erewrite Memory.remove_o in GET; eauto. des_ifs. ss. des; clarify.
      exploit memory_get_from_inj.
      { eapply GET. }
      { eapply GET1. }
      i. des; clarify.
      { eapply Time.lt_strorder; eauto. }
      { eapply Time.lt_strorder; eauto. }
    }
    { eapply promise_memory_le; eauto. }
    { i. hexploit (@Memory.add_exists mem2 loc ts to Message.reserve).
      { ii. hexploit (@UNCH12 loc to2).
        { i. inv LHS. inv RHS. ss. eapply TimeFacts.lt_le_lt; eauto. }
        i. des. rewrite H in *.
        erewrite (@Memory.remove_o mem1) in GET2; eauto. des_ifs. guardH o.
        exploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply GET1. }
        i. des; clarify.
        - ss. unguard. des; clarify.
        - eapply x1; eauto.
      }
      { auto. }
      { econs. }
      intros [mem3 ADDMEM].
      hexploit (Memory.add_exists_le); eauto.
      intros [prom3 ADDPROM].

      assert (ADD: Memory.promise prom2 mem2 loc ts to Message.reserve prom3 mem3 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      exists prom3, mem3. splits; auto.
      { eapply reserve_future_memory_trans; eauto. }

      { i. exploit UNCH12; eauto. i. des.
        erewrite (@Memory.add_o mem3); eauto.
        erewrite (@Memory.add_o prom3); eauto.
        erewrite x. erewrite x0.
        erewrite (@Memory.remove_o mem1); eauto.
        erewrite (@Memory.remove_o prom1); eauto. des_ifs.
        ss. des; clarify. }
      { i. erewrite (@Memory.add_o mem3); eauto.
        erewrite (@Memory.add_o prom3); eauto. des_ifs.
        ss. des; clarify.
        exfalso. eapply Time.lt_strorder.
        eapply (@TimeFacts.le_lt_lt to ts); eauto. }
      { eapply promise_memory_le; eauto. }
    }
  Qed.

  Lemma promises_not_attached_replace_add self loc from from' to prom0 mem0
        (LIN: L loc)
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (LOC: forall from to msg (GET: Memory.get loc to prom0 = Some (from, msg)),
            msg = Message.reserve)
        (MLE0: Memory.le prom0 mem0)
        (NBOT: Time.lt Time.bot to)
        (* (PROMISED: self loc to) *)
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
    { econs; eauto. }
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

  Lemma sim_promise_weak_stengthen others self prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONE: Memory.bot_none prom_src)
        (PROM: sim_promise self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (* (SELF: self <2= promised prom_src) *)
        (EXCLUSIVE: forall loc' ts' (SELF: self loc' ts') (OTHER: others loc' ts'), False)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self) mem_src' mem_tgt>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self (promised prom_src') mem_src'>>) /\
        (<<PROM: sim_promise_strong
                   self (concrete_promised mem_src' \2/ self)
                   (* (fun loc' ts' => concrete_promise *)
                   (*    concrete_promised prom_src' loc' ts' /\ *)
                   (*    ~ others loc' ts' *)
                   (* ) *)
                   prom_src' prom_tgt>>).
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

    clear LIN.

    destruct (Memory.get loc ts prom_src) as [[from_src [val released|]]|] eqn:GETSRC; cycle 2.
    { inv WEAK. exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H. rewrite GETSRC. econs; eauto. }
    { inv WEAK. exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite <- H. rewrite GETSRC. econs; eauto. }
    assert (exists from_tgt msg, <<GETTGT: Memory.get loc ts prom_tgt = Some (from_tgt, msg)>>).
    { inv WEAK; eauto. } des. rewrite GETTGT in *.

    destruct (classic ((concrete_promised mem_src \2/ self) loc from_tgt)) as [OTHER|NOTHER]; cycle 1.
    { exploit IHl; eauto. ii.
      specialize (SIM loc0 ts0). ss. des; auto; clarify.
      left. rewrite GETTGT. rewrite GETSRC. inv WEAK.
      - econs 2; eauto.
      - econs 3; eauto. clarify.
      - econs 4; eauto. clarify. }
    guardH OTHER.

    assert (NBOT: Time.lt Time.bot ts).
    { destruct (Time.le_lt_dec ts Time.bot); auto. destruct l0.
      - exfalso. eapply Time.lt_strorder.
        eapply TimeFacts.lt_le_lt; eauto. eapply Time.bot_spec.
      - inv H. erewrite BOTNONE in GETSRC. clarify. }

    destruct (classic (L loc)) as [LOC|NLOC]; cycle 1.
    { hexploit (@IHl others self prom_src prom_tgt mem_src mem_tgt); eauto.
      ii. specialize (SIM loc0 ts0). ss. des; eauto. clarify.
      left. inv WEAK; eauto.
      - rewrite GETSRC. rewrite GETTGT. econs 2; eauto.
      - rewrite GETSRC. rewrite GETTGT. econs 3; eauto. i. clarify.
      - rewrite GETSRC. rewrite GETTGT. econs 4; eauto. i. clarify. }

    exploit promises_not_attached_replace_add.
    { eauto. }
    { eauto. }
    { ii. specialize (SIM loc to). rewrite GET in *. des.
      - inv NORMAL; eauto; try by (exfalso; eauto).
      - inv WEAK0; eauto; try by (exfalso; eauto). }
    { eauto. }
    { eauto. }
    { eauto. }
    { instantiate (1:=from_tgt).
      apply memory_get_ts_strong in GETTGT. des; clarify. }
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
      - guardH PROM. exploit Memory.get_disjoint.
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

    hexploit (@IHl others self prom1 prom_tgt mem1 mem_tgt); eauto.
    { ii.
      dup MEM. specialize (MEM0 loc0 ts0). erewrite MEMSPEC. des_ifs.
      - ss. des; clarify. apply MLETGT in GETTGT. rewrite GETTGT.
        rewrite GETTGT in *. apply MLESRC in GETSRC. rewrite GETSRC in *.
        inv MEM0; eauto.
        + econs 2; eauto. refl.
        + econs 3; eauto. refl.
    }
    { eapply reserve_future_memory_le; eauto. }
    { eapply reserve_future_memory_finite; eauto. }
    { eapply reserve_future_memory_bot_none; eauto. }
    { ii. rewrite MEMSPEC in GET.
      erewrite PROMISEDSAME. des_ifs.
      - ss. des; clarify. econs; eauto.
      - exploit PROMATTACH; eauto. }
    { ii. erewrite PROMSPEC. des_ifs.
      - left. ss. des. clarify. erewrite GETTGT. inv WEAK; eauto.
      - guardH o. specialize (SIM loc0 ts0).
        ss. rewrite CONCRETESAME. des; eauto.
        unguard. des; clarify. }
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
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (* (SELF: self <2= promised prom0) *)
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
    { econs; eauto. }
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
        (ATTACHED: promises_not_attached self (promised prom0) mem0)
        (* (SELF: self <2= promised prom0) *)
        (* (PROMISED: self loc to) *)
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
    { econs; eauto. }
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


  Lemma sim_promise_step_forget others self mem_src mem_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (LOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (EXCLUSIVE: forall loc' ts' (SELF: promised prom_src loc' ts') (OTHER: others loc' ts'), False)
    :
      exists prom_src' mem_src' self',
        (<<STEPSRC: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self' prom_src' prom_tgt'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised prom_src') mem_src'>>)
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
                       then msg_tgt <> Message.reserve else self loc' ts').
      splits; auto.
      + ii. erewrite (@Memory.add_o mem_src'); eauto.
        erewrite (@Memory.add_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. destruct msg_tgt.
          { econs 3; eauto.
            - right. clarify.
            - left. eapply Time.middle_spec; eauto. }
          { econs 2; eauto.
            - ii. des; eauto. exfalso.
              specialize (MEM loc to). eapply Memory.add_get0 in ADDMEM.
              des. rewrite GET in *. inv MEM. eauto.
            - left. eapply Time.middle_spec; eauto.
            - i. clarify.
          }
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
        ss. des; clarify. destruct msg_tgt.
        * econs 4; eauto. clarify.
        * econs 3; eauto.
      + ii. erewrite promised_add; eauto.
        erewrite Memory.add_o in GET; eauto.
        destruct msg_tgt; cycle 1.
        { des_ifs; eauto; try by (ss; des; clarify). }
        des_ifs; eauto; ss; des; clarify.
        specialize (MEM loc ts1). rewrite GET in *. inv MEM.
        { exfalso. destruct FROM.
          { exploit DISJOINT.
            - symmetry. eapply H.
            - instantiate (1:=to). econs; ss. refl.
            - econs; ss. apply memory_get_ts_le in GET; eauto.
            - auto. }
          { inv H0. exfalso. eapply ATTACH; eauto. }
        }
        { exfalso. destruct FROM.
          { exploit DISJOINT.
            - symmetry. eapply H.
            - instantiate (1:=to). econs; ss. refl.
            - econs; ss. apply memory_get_ts_le in GET; eauto.
            - auto. }
          { inv H0. exfalso. eapply ATTACH; eauto. }
        }

    - des. clarify.
      exploit split_succeed_wf; try apply PROMISES. i. des.
      dup GET2. apply WFTGT in GET0.
      dup PROMISE. specialize (PROMISE0 loc ts3).
      rewrite GET2 in PROMISE0.

      assert (exists from_src, <<GETSRC: Memory.get loc ts3 prom_src = Some (from_src, Message.reserve)>>).
      { inv PROMISE0; eauto. clarify. } des. rewrite GETSRC in *.

      assert (EMPTY0: forall ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3),
                 Memory.get loc ts' mem_tgt = None).
      { i. destruct (Memory.get loc ts' mem_tgt) as [[from' msg']|] eqn:GET; auto.
        exfalso. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - eapply x0.
          + instantiate (1:=ts'). econs; ss; [|refl].
            apply memory_get_ts_strong in GET. des; clarify; auto.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            * eapply TS0.
            * eapply Time.bot_spec.
          + econs; ss. left. auto. }

      assert (EMPTY1: forall to' msg' ts' (TS0: Time.lt from ts') (TS1: Time.lt ts' ts3)
                             (GET: Memory.get loc to' mem_tgt = Some (ts', msg')),
                 False).
      { i. exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GET0. }
        i. des; clarify.
        - eapply Time.lt_strorder; eauto.
        - hexploit memory_get_to_mon.
          { eapply GET0. }
          { eapply GET. }
          { auto. } i.
          eapply x0.
          + instantiate (1:=ts3). econs; ss. left. auto.
          + econs; ss; [|refl]. etrans; eauto. }

      exploit (@promises_not_attached_replace_split self loc from_src (Time.middle from to) to ts3 prom_src mem_src); auto.
      { i. specialize (PROMISE loc to0). rewrite GET in *. inv PROMISE; clarify. }
      { eapply (@TimeFacts.le_lt_lt _ from); eauto. eapply Time.bot_spec. }
      { eapply Time.middle_spec; eauto. }
      { ii. inv H.
        assert (exists from0' msg', <<GETTGT: Memory.get loc to0 mem_tgt = Some (from0', msg')>> /\ <<TS: Time.le from0' from0>>).
        { dup MEM. specialize (MEM loc to0). rewrite GET in MEM. inv MEM; eauto. } des.
        assert (TS1: Time.lt to0 ts3).
        { eapply memory_get_to_mon; try apply GET; eauto.
          inv ITV0. inv ITV. ss. eapply TimeFacts.lt_le_lt; eauto. }
        erewrite EMPTY0 in GETTGT.
        - clarify.
        - inv ITV. inv ITV0. ss. eapply TimeFacts.lt_le_lt.
          { eapply Time.middle_spec; eauto. }
          { left. eapply TimeFacts.lt_le_lt; eauto. }
        - auto.
      }

      intros [prom_src' [mem_src' ?]]. des.

      assert (PROMISEDDIFF: promised prom_src' =
                            fun loc' =>
                              if (Loc.eq_dec loc' loc)
                              then fun ts' => if (Time.eq_dec ts' to) then True else promised prom_src loc' ts'
                              else promised prom_src loc').
      { extensionality loc'. extensionality ts'.
        apply Coq.Logic.PropExtensionality.propositional_extensionality.
        split; i.
        - inv H. erewrite PROMSPEC in GET. des_ifs; try by (ss; des; clarify).
          + ss. des; clarify. econs; eauto.
          + ss. des; clarify. econs; eauto.
          + econs; eauto.
        - specialize (PROMSPEC loc' ts'). des_ifs; try by (ss; des; clarify).
          + econs; eauto.
          + econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto.
          + inv H. erewrite <- PROMSPEC in *. econs; eauto. }

      exists prom_src', mem_src',
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then True else self loc' ts'). splits; auto.
      + ii. erewrite MEMSPEC.
        erewrite (@Memory.split_o mem_tgt'); eauto.
        des_ifs; try by (ss; des; clarify).
        * ss. des; clarify. econs 3; eauto.
          { left. apply Time.middle_spec; eauto. }
        * ss. des; clarify.
          specialize (MEM loc ts3). rewrite GET0 in *.
          apply WFSRC in GETSRC. rewrite GETSRC in *. inv MEM; eauto.
          { econs 2; eauto. refl. }
          { econs 3; eauto. refl. }
      + ii. erewrite MEMSPEC in GET. des_ifs.
        * ss. des; clarify. exfalso.
          specialize (MEM loc (Time.middle from to)).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H.
          { clarify. }
          { eapply Time.middle_spec; eauto. }
          { etrans; eauto. eapply Time.middle_spec; eauto. }
        * ss. des; clarify. exfalso.
          specialize (MEM loc from0).
          inv MEM; try by (exfalso; eauto). clear PROM. erewrite EMPTY0 in H; auto.
          { clarify. }
        * eauto.
      + ii. erewrite PROMSPEC.
        erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. inv PROMISE0; eauto.
      + ii. erewrite MEMSPEC in GET. erewrite PROMISEDDIFF.
        des_ifs; eauto; try by (ss; des; clarify).
        * ss. des; clarify. econs; eauto.
        * ss. des; clarify. exfalso.
          exploit (@memory_get_from_inj mem_src' loc to ts1 ts3 msg Message.reserve).
          { erewrite MEMSPEC. des_ifs; ss; des; clarify. }
          { erewrite MEMSPEC. des_ifs; ss; des; clarify.
            exfalso. eapply Time.lt_strorder; eauto. }
          i. des; clarify.
          { eapply Time.lt_strorder; eauto. }

    - dup PROMISES. apply Memory.lower_get0 in PROMISES0. des. clarify.
      dup GET. apply WFTGT in GET1.
      dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in *.
      inv PROMISE0; clarify.
      exists prom_src, mem_src, self. splits; auto.
      + ii. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
        ss. des; clarify.
        specialize (MEM loc to). rewrite GET1 in *. inv MSG_LE. inv MEM; eauto.
        { exfalso. eapply NPROM. auto. }
      + ii. eauto.
      + ii. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. inv MSG_LE. rewrite <- H0. econs 4; eauto.

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
      + ii. erewrite (@Memory.remove_o mem_src'); eauto.
        erewrite (@Memory.remove_o mem_tgt'); eauto.
        des_ifs; ss; des; clarify. econs. ii. des; clarify.
        eapply EXCLUSIVE; eauto. econs; eauto.
      + ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto.
      + ii. erewrite (@Memory.remove_o prom_src'); eauto.
        erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
        ss. des; clarify. econs. ss.
      + ii. erewrite Memory.remove_o in GET2; eauto.
        erewrite promised_remove; eauto. des_ifs; eauto.
        ss. des; clarify.
  Qed.

  Lemma sim_write_forget others self mem_src mem_tgt prom_src prom_tgt
        loc from from' to val released prom_tgt'
        (STEPTGT: Memory.remove prom_tgt loc from to (Message.concrete val released) prom_tgt')
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SELF: self loc to)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self prom_src prom_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (EXCLUSIVE: forall loc' ts' (SELF: self loc' ts') (OTHER: others loc' ts'), False)

        (FROM: Time.le from from')
        (FROMTO: Time.lt from' to)

        (ATTACHED: from = from' -> concrete_promised mem_src loc from)

        (MSGTO: Time.le (View.rlx (View.unwrap released) loc) to)

        (SEMICLOSED: semi_closed_opt_view released mem_src loc to)
        (VIEWWF: View.opt_wf released)
    :
      exists self' prom0 prom1 mem0 mem1 prom_src' mem_src',
        (<<FUTURE01: reserve_future_memory prom_src mem_src prom0 mem0>>) /\
        (<<STEPSRC: Memory.write prom0 mem0 loc from' to val released prom1 mem1 Memory.op_kind_add>>) /\
        (<<FUTURE23: reserve_future_memory prom1 mem1 prom_src' mem_src'>>) /\

        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMISE: sim_promise self' prom_src' prom_tgt'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised prom_src') mem_src'>>)
  .
  Proof.
    dup STEPTGT. eapply Memory.remove_get0 in STEPTGT0. des.
    dup PROMISE. specialize (PROMISE0 loc to). rewrite GET in PROMISE0.
    inv PROMISE0; clarify. rename H0 into GETSRC. symmetry in GETSRC.
    exploit promises_not_attached_replace_write; eauto.
    { i. specialize (PROMISE loc to0). rewrite GET1 in *.
      inv PROMISE; eauto. clarify. }
    { eapply TimeFacts.le_lt_lt; eauto. eapply Time.bot_spec. }
    { ii. inv H.
      assert (exists from_tgt msg_tgt,
                 (<<GETTGT0: Memory.get loc to0 mem_tgt = Some (from_tgt, msg_tgt)>>)).
      { dup MEM. specialize (MEM0 loc to0).
        rewrite GET1 in MEM0. inv MEM0; eauto. } des.
      exploit Memory.get_disjoint.
      { eapply GETTGT0. }
      { eapply WFTGT. eapply GET. } i. des; clarify.
      - dup GETSRC. apply WFSRC in GETSRC0. clarify.
        inv ITV. inv ITV0. ss.
        eapply Time.lt_strorder. eapply (@TimeFacts.lt_le_lt from0 ts); eauto.
      - eapply x0.
        + instantiate (1:=ts). econs; ss.
          * inv ITV. inv ITV0. ss.
            eapply TimeFacts.le_lt_lt; eauto.
            specialize (MEM loc to0).
            rewrite GET1 in *. rewrite GETTGT0 in *. inv MEM; ss.
          * inv ITV0. ss.
        + inv ITV; ss. econs; ss.
          * eapply TimeFacts.le_lt_lt; eauto.
          * etrans; eauto. eapply memory_get_ts_le; eauto. }

    i. des.

    exists (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                            then False else self loc' ts'),
    prom1, prom2, mem1, mem2, prom3, mem3. splits; eauto.
    - ii. erewrite MEMSPEC. des_ifs.
      + ss. des; clarify.
        dup GET. eapply WFTGT in GET. rewrite GET. econs 2; eauto.
        * ii. des; eauto.
        * i. clarify.
    - ii. erewrite MEMSPEC in GET1. des_ifs; eauto.
      ss. des; clarify. exfalso.
      dup MEM. specialize (MEM0 loc from0). inv MEM0; eauto.
      clear PROM0. exploit Memory.get_disjoint.
      { symmetry. eapply H. }
      { apply WFTGT. apply GET. }
      i. des; clarify.
      { exfalso. eapply Time.lt_strorder; eauto. }
      destruct FROM.
      { exfalso. eapply x0.
        - instantiate (1:=from0). econs; ss.
          + symmetry in H. apply memory_get_ts_strong in H. des; auto.
            clarify. exfalso. eapply Time.lt_strorder.
            eapply (@TimeFacts.le_lt_lt Time.bot from); eauto.
            eapply Time.bot_spec.
          + refl.
        - econs; ss. left. auto. }
      { inv H1. exploit ATTACHED; eauto. i. inv x. rewrite GET1 in *. clarify. }
    - ii. erewrite PROMSPEC. erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
      + ss. des; clarify. econs; eauto.
    - ii. erewrite MEMSPEC in GET1. des_ifs.
      + ss. des; clarify. exfalso.
        dup MEM. specialize (MEM0 loc ts0). inv MEM0; eauto.
        clear PROM0. exploit Memory.get_disjoint.
        { symmetry. eapply H. }
        { apply WFTGT. apply GET. }
        i. des; clarify.
        destruct FROM.
        { exfalso. eapply x0.
          - instantiate (1:=ts0). econs; ss.
            + symmetry in H. apply memory_get_ts_strong in H. des; auto.
              clarify. exfalso. eapply Time.lt_strorder.
              eapply (@TimeFacts.le_lt_lt Time.bot from); eauto.
              eapply Time.bot_spec.
            + refl.
          - econs; ss. left. auto. }
        { inv H1. exploit ATTACHED; eauto. i. inv x. rewrite GET1 in *. clarify. }
      + exploit PROMATTACH; eauto. i. inv x.
        specialize (PROMSPEC loc0 ts1). des_ifs.
        * ss. des; clarify.
        * erewrite <- PROMSPEC in *. econs; eauto.
  Qed.

  Lemma reserve_future_memory_steps
        lang st vw sc prom0 mem0 prom1 mem1
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      exists tr,
        (<<STEPS: Trace.steps tr
                              (Thread.mk lang st (Local.mk vw prom0) sc mem0)
                              (Thread.mk lang st (Local.mk vw prom1) sc mem1)>>).
  Proof.
    ginduction FUTURE; eauto. i. exploit IHFUTURE; eauto. i. des.
    esplits. eapply Trace.steps_trans; [|apply STEPS|ss].
    econs 1. econs; eauto.
  Qed.

  Lemma reserve_future_memory_unchangable
        prom0 mem0 prom1 mem1 loc to from msg
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (UNCH: unchangable mem0 prom0 loc to from msg)
    :
      unchangable mem1 prom1 loc to from msg.
  Proof.
    ginduction FUTURE; eauto. i. exploit IHFUTURE; eauto.
    eapply unchangable_promise; eauto.
  Qed.

  Lemma reserve_future_memory_future
        vw sc prom0 mem0 prom1 mem1
        (LOCAL: Local.wf (Local.mk vw prom0) mem0)
        (SC: Memory.closed_timemap sc mem0)
        (MEM: Memory.closed mem0)
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      (<<LOCAL: Local.wf (Local.mk vw prom1) mem1>>) /\
      (<<SC: Memory.closed_timemap sc mem1>>) /\
      (<<MEM: Memory.closed mem1>>).
  Proof.
    ginduction FUTURE; eauto. i.
    exploit Local.promise_step_future.
    { econs.
      - instantiate (9:=Local.mk vw prom0). eauto.
      - eauto.
      - eauto. }
    all: eauto. i. des. ss. eapply IHFUTURE; eauto.
  Qed.

  Lemma reserve_future_concrete_same_promise2 prom0 mem0 prom1 mem1 loc from to val released
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
        (GET: Memory.get loc to prom1 = Some (from, Message.concrete val released))
    :
      Memory.get loc to prom0 = Some (from, Message.concrete val released).
  Proof.
    ginduction FUTURE; auto. i. apply IHFUTURE in GET; auto.
    inv HD; des; clarify.
    - erewrite Memory.add_o in GET; eauto. des_ifs.
    - erewrite Memory.lower_o in GET; eauto. des_ifs.
    - erewrite Memory.remove_o in GET; eauto. des_ifs.
  Qed.

  Lemma sim_write_step_forget
        others self vw_src prom_src lc_tgt sc mem_src mem_tgt
        lc_tgt' sc' mem_tgt' loc from to val ord releasedm released kind_tgt from'
        (LOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf (Local.mk vw_src prom_src) mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self (Local.mk vw_src prom_src) lc_tgt)
        (PROMATTACH: promises_not_attached self (promised prom_src) mem_src)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src prom_src loc' ts' from msg>>)

        (FROM: Time.le from from')
        (FROMTO: Time.lt from' to)

        (ATTACHED: from = from' -> concrete_promised mem_src loc from)

        (RELEASEDMCLOSEDSRC: Memory.closed_opt_view releasedm mem_src)
        (RELEASEDMCLOSEDTGT: Memory.closed_opt_view releasedm mem_tgt)
        (RELEASEDMWF: View.opt_wf releasedm)
    :
      exists self' vw_src' prom_src' mem_src'
             prom0 prom1 mem0 mem1 kind_src,
        (<<FUTURE01: reserve_future_memory prom_src mem_src prom0 mem0>>) /\
        (<<STEPSRC: Local.write_step (Local.mk vw_src prom0) sc mem0 loc from' to val releasedm released ord (Local.mk vw_src' prom1) sc' mem1 kind_src>>) /\
        (<<FUTURE12: reserve_future_memory prom1 mem1 prom_src' mem_src'>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised prom_src') mem_src'>>) /\
        (<<SIM: sim_local self' (Local.mk vw_src' prom_src') lc_tgt'>>)
  (* TODO: condition about event *)
  .
  Proof.
    hexploit Local.write_step_future; eauto. i. des.

    inv SIM. inv LOCALSRC. inv LOCALTGT. inv STEPTGT. inv WRITE. ss.
    exploit sim_promise_step_forget; eauto.
    { i. exploit EXCLUSIVE; eauto. i. des. inv UNCH. inv SELF. clarify. }
    i. des.

    hexploit reserve_future_memory_future; try apply STEPSRC; eauto. i. des.
    inv LOCAL. ss.

    hexploit sim_write_forget.
    { eauto. }
    { eauto. }
    { specialize (PROMISE0 loc to).
      eapply Memory.remove_get0 in REMOVE. des. erewrite GET in *.
      inv PROMISE0; clarify. }
    { eauto. }
    { eauto. }
    { eauto. }
    { eapply promise_memory_le; cycle 1; eauto. }
    { eauto. }
    { eauto. }
    { ii. exploit EXCLUSIVE; eauto. i. des.
      eapply reserve_future_memory_unchangable in UNCH; eauto.
      specialize (PROMISE0 loc' ts'). inv UNCH. rewrite NPROM in *.
      inv PROMISE0; eauto. }
    { eapply FROM. }
    { eauto. }
    { i. exploit ATTACHED; eauto. i. inv x.
      eapply Memory.future_get1 in GET.
      { des. inv MSG_LE. econs; eauto. }
      { eapply reserve_future_future; eauto. }
    }
    { eauto. }
    { unfold TView.write_released. des_ifs; econs.
      eapply semi_closed_view_join.
      - inv MEM1. eapply unwrap_closed_opt_view; eauto.
        eapply closed_opt_view_semi_closed.
        eapply Memory.future_closed_opt_view.
        + eapply reserve_future_future; eauto.
        + eauto.
      - eapply semi_closed_view_future; cycle 1.
        { eapply Memory.future_future_weak.
          eapply reserve_future_future; eauto. }
        ss. inv TVIEW_CLOSED. setoid_rewrite LocFun.add_spec_eq. des_ifs.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. eauto.
          * inv MEMSRC. eapply semi_closed_view_singleton; eauto.
        + eapply semi_closed_view_join.
          * eapply closed_view_semi_closed. eauto.
          * inv MEMSRC. eapply semi_closed_view_singleton; eauto.
    }
    { eauto. }

    i. des.
    eexists self'0, _, prom_src'0, mem_src'0,
    prom0, prom1, mem0, mem1. esplits; eauto.
    { eapply reserve_future_memory_trans; eauto. }
    { econs; eauto. ss. ii. destruct msg; ss.
      eapply reserve_future_concrete_same_promise2 in GET; eauto.
      specialize (PROMISE0 loc t). rewrite GET in PROMISE0. inv PROMISE0; ss. }
    { etrans; eauto. }
  Qed.

  Lemma reserve_future_read_commute
        vw0 prom0 mem0 loc to val released ord vw1 prom' prom1 mem1
        (READ: Local.read_step (Local.mk vw0 prom0) mem0 loc to val released ord (Local.mk vw1 prom'))
        (FUTURE: reserve_future_memory prom0 mem0 prom1 mem1)
    :
      Local.read_step (Local.mk vw0 prom1) mem1 loc to val released ord (Local.mk vw1 prom1).
  Proof.
    inv READ. clarify. econs; eauto.
    eapply reserve_future_concrete_same; eauto.
  Qed.

  Lemma joined_view_semi_closed
        views view mem loc ts
        (MEM: List.Forall (fun vw => semi_closed_view vw mem loc ts) views)
        (JOINED: joined_view views view)
        (INHABITED: Memory.inhabited mem)
    :
      semi_closed_view view mem loc ts.
  Proof.
    ginduction JOINED; eauto.
    - i. eapply closed_view_semi_closed. apply Memory.closed_view_bot. auto.
    - i. eapply semi_closed_view_join; eauto.
      eapply List.Forall_forall in VIEW; [|eauto]. ss.
  Qed.

  Lemma sim_thread_step' others self lang st lc_src lc_tgt sc mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc' mem_tgt' views views'
        (STEPTGT: @JThread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc mem_tgt) (Thread.mk _ st' lc_tgt' sc' mem_tgt') views views')
        (NOREAD: no_read_msgs (others \2/ self) e_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self lc_src lc_tgt)
        (PROMATTACH: promises_not_attached self (promised lc_src.(Local.promises)) mem_src)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from msg>>)
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))
    :
      exists tr self' lc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc mem_src) (Thread.mk _ st' lc_src' sc' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SIM: sim_local self' lc_src' lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv STEP.

    - inv STEP0. destruct (classic (L loc)).
      + inv LOCAL. inv SIM. inv LOCALSRC. inv LOCALTGT.
        exploit sim_promise_step_forget; eauto.
        { i. exploit EXCLUSIVE; eauto. i. des. inv UNCH. inv SELF. clarify. }
        i. des.
        exploit reserve_future_memory_steps; eauto. i. des.
        eexists _, self', (Local.mk _ _), mem_src'. splits; eauto.
      + inv LOCAL. inv SIM. inv LOCALSRC. inv LOCALTGT.
        exploit sim_promise_step_normal; try apply MEM; eauto.
        { destruct msg; econs. hexploit PROMISE; eauto.
          i. inv H0; econs.
          destruct (classic (views' loc to = views loc to)).
          - rewrite H0 in *.
            inv MEMSRC. eapply joined_view_closed in JOINED0; eauto.
            eapply closed_view_semi_closed; eauto.
          - exploit VIEWSLE; eauto. i. des. ss.
            inv MEMSRC. eapply joined_view_semi_closed; cycle 1; eauto.
            rewrite VIEW. econs.
            + eapply semi_closed_view_join.
              * eapply closed_view_semi_closed. eapply TVIEW_CLOSED.
              * eapply semi_closed_view_singleton; eauto.
            + eapply List.Forall_forall.
              i. eapply all_join_views_in_iff in H1. des. subst.
              eapply semi_closed_view_join.
              * eapply closed_view_semi_closed.
                eapply List.Forall_forall in IN; eauto. ss.
              * eapply semi_closed_view_singleton; eauto.
        }
        i. des.
        eexists [(_, ThreadEvent.promise loc from to msg kind)], self, (Local.mk _ _), mem_src'.
        splits; ss.
        * econs 2; [|econs 1|ss]. econs 1. econs; eauto.
        * ss.
        * ss.

    - inv STEP0. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], self, lc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released ord)],
        self, lc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
        * inv STEPSRC; ss.
      + destruct (classic (L loc)).
        * assert (TS: Time.lt from to).
          { inv LOCAL0. inv WRITE. inv PROMISE0; ss.
            - eapply add_succeed_wf in MEM0. des. auto.
            - eapply split_succeed_wf in MEM0. des. auto.
            - eapply lower_succeed_wf in MEM0. des. auto. }
          assert (MIDDLE: Time.lt (Time.middle from to) to).
          { eapply Time.middle_spec; eauto. }
          destruct lc_src. hexploit sim_write_step_forget; eauto.
          { left. eapply Time.middle_spec; eauto. }
          { i. exfalso. eapply Time.lt_strorder.
            instantiate (1:=from). erewrite H0 at 2. eapply Time.middle_spec; eauto. }
          i. des.
          eapply reserve_future_memory_steps in FUTURE01. des.
          eapply reserve_future_memory_steps in FUTURE12. des.
          esplits; eauto.
          { eapply Trace.steps_app.
            { eapply STEPS. }
            eapply Trace.steps_app.
            { econs 2; [|econs 1|ss]. econs 2. econs; cycle 1.
              - econs 3. eauto.
              - ss. eauto. }
            eauto.
          }
          { ss. }
        * hexploit sim_write_step_normal; try apply MEM; try eassumption; auto. i. des.
          eexists [(_, ThreadEvent.write loc from to val _ ord)], self, lc_src', mem_src'.
          splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + destruct (classic (L loc)).
        * assert (TS: Time.lt tsr tsw).
          { inv LOCAL2. inv WRITE. inv PROMISE0; ss.
            - eapply add_succeed_wf in MEM0. des. auto.
            - eapply split_succeed_wf in MEM0. des. auto.
            - eapply lower_succeed_wf in MEM0. des. auto. }

          exploit sim_read_step; eauto. i. des.
          exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
          exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.

          dup STEPSRC. inv STEPSRC. destruct lc_src. ss. clarify.
          hexploit sim_write_step_forget; eauto.
          { refl. }
          { i. econs; eauto. }
          i. des.
          eapply reserve_future_read_commute in STEPSRC0; eauto.
          eapply reserve_future_memory_steps in FUTURE01. des.
          eapply reserve_future_memory_steps in FUTURE12. des.
          esplits; try apply MEM0; eauto.
          { eapply Trace.steps_app.
            { eapply STEPS. }
            eapply Trace.steps_app.
            { econs 2; [|econs 1|ss]. econs 2. econs; cycle 1.
              - econs 4; eauto.
              - ss. eauto. }
            eauto.
          }
          { ss. }
        * exploit sim_read_step; eauto. i. des.
          (* dup PAST. inv PAST0. exploit COMPLETE; eauto. i. des. *)
          exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
          exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.
          hexploit sim_write_step_normal; try apply MEM; try eassumption.
          { inv STEPSRC. ss. } i. des.
          eexists [(_, ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)],
          self, lc_src'0, mem_src'. splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        self, lc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
        * inv STEPSRC; ss.
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.syscall e)],
        self, lc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
        * inv STEPSRC; ss.
      + exploit sim_failure_step; eauto. i. des.
        eexists [(_, ThreadEvent.failure)],
        self, lc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * refl.
  Qed.

  Lemma traces_steps_future
        lang tr e1 e2
        (STEPS: @Trace.steps lang tr e1 e2)
        (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
        (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
        (CLOSED1: Memory.closed e1.(Thread.memory)):
    (<<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>>) /\
    (<<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>>) /\
    (<<CLOSED2: Memory.closed e2.(Thread.memory)>>) /\
    (<<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>>) /\
    (<<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>>) /\
    (<<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>)
  .
  Proof.
    ginduction STEPS.
    - i. splits; auto.
      + refl.
      + refl.
    - i. exploit Thread.step_future; eauto. i. des.
      exploit IHSTEPS; eauto. i. des. splits; auto.
      + etrans; eauto.
      + etrans; eauto.
      + etrans; eauto.
  Qed.

  Lemma sim_thread_step others self lang st lc_src lc_tgt sc mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc' mem_tgt' views views'
        (STEPTGT: @JThread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc mem_tgt) (Thread.mk _ st' lc_tgt' sc' mem_tgt') views views')
        (NOREAD: no_read_msgs (others \2/ self) e_tgt)
        (MEM: sim_memory (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self lc_src lc_tgt)
        (PROMATTACH: promises_not_attached self (promised lc_src.(Local.promises)) mem_src)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from msg>>)
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))
    :
      exists tr self' lc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc mem_src) (Thread.mk _ st' lc_src' sc' mem_src')>>) /\
        (<<MEM: sim_memory (others \2/ self') mem_src' mem_tgt'>>) /\
        (<<ATTACHEDLE: not_attached_le others mem_src mem_src'>>) /\
        (<<PROMATTACH: promises_not_attached self' (promised lc_src'.(Local.promises)) mem_src'>>) /\
        (<<SIM: sim_local self' lc_src' lc_tgt'>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src') (views' loc ts)>>)
  .
  Proof.
    exploit sim_thread_step'; eauto. i. des. esplits; eauto.
    exploit traces_steps_future; eauto. i. des. ss.

    inv STEPTGT. ss.
    i. destruct (classic (views' loc ts = views loc ts)).

    { rewrite H.
      eapply List.Forall_impl; eauto.
      i. ss. eapply Memory.future_closed_view; eauto. }

    { hexploit VIEWSLE; eauto. i. des.
      specialize (MEM0 loc ts). rewrite GET in MEM0. inv MEM0; ss.
      rewrite VIEW. econs.
      - eapply Memory.join_closed_view.
        + inv WF2. inv SIM0. ss. eapply TVIEW_CLOSED.
        + inv CLOSED2. eapply Memory.singleton_ur_closed_view; eauto.
      - apply List.Forall_forall.
        i. eapply all_join_views_in_iff in H0. des. subst.
        eapply Memory.join_closed_view.
        + eapply Memory.future_closed_view; eauto.
          eapply List.Forall_forall in IN; eauto. ss.
        + inv CLOSED2. eapply Memory.singleton_ur_closed_view; eauto. }
    Qed.

End SIM.
