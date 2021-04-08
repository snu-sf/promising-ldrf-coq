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
Require Import OrderedTimes.

Require Import PFStep.
Require Import LocalPFThread.

Set Implicit Arguments.







Section SIM.

  Variable L: Loc.t -> bool.
  Variable times: Loc.t -> Time.t -> Prop.
  Hypothesis WO: forall loc, well_ordered (times loc).

  (* sim promises *)

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
      (* (NLOC: ~ L loc) *)
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

  Lemma promises_forget_extra_exclusive F extra mem_src mem_tgt loc from to ts
        (PROMISES: sim_promise F extra mem_src mem_tgt)
        (FORGET: F loc ts)
        (EXTRA: extra loc to from)
    :
      ts <> to.
  Proof.
    ii. subst.
    set (PROM:=(sim_promise_contents PROMISES) loc to). inv PROM; ss.
    eapply NEXTRA; eauto.
  Qed.

  Lemma sim_promise_src_none F extra prom_src prom_tgt
        (PROMISE: sim_promise F extra prom_src prom_tgt)
        loc to
        (GETSRC: Memory.get loc to prom_src = None)
    :
      (<<GETTGT: Memory.get loc to prom_tgt = None>>) /\
      (<<NPROM: ~ F loc to >>) /\
      (<<NEXTRA: forall t, ~ extra loc to t>>).
  Proof.
    set (PROM:=(sim_promise_contents PROMISE) loc to).
    rewrite GETSRC in PROM. inv PROM.
    - splits; auto.
    - splits; auto.
  Qed.

  Lemma sim_promise_bot self extra prom_src prom_tgt
        (SIM: sim_promise self extra prom_src prom_tgt)
        (BOT: prom_tgt = Memory.bot)
    :
      prom_src = Memory.bot.
  Proof.
    eapply Memory.ext. i. erewrite Memory.bot_get.
    set (CNT:=(sim_promise_contents SIM) loc ts). subst.
    erewrite Memory.bot_get in CNT. inv CNT; ss.
    eapply sim_promise_wf in EXTRA; eauto. des.
    set (CNT:=(sim_promise_contents SIM) loc from).
    erewrite Memory.bot_get in CNT. inv CNT; ss.
  Qed.



  (* sim promises strong *)

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
      (* (NLOC: ~ L loc) *)
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
    - ii. hexploit (sim_promise_list_contents SIM); eauto. i. des; eauto. ss.
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
    ii. set (PROM:= (sim_promise_contents SIM) loc ts).
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

  Lemma sim_promise_weak_strengthen others self extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (PROM: sim_promise self extra_self prom_src prom_tgt)
        (MEMWF: memory_times_wf times mem_tgt)
    :
      exists prom_src' mem_src',
        (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt>>) /\
        (<<PROM: sim_promise_strong
                   self extra_self (extra_others \\3// extra_self)
                   prom_src' prom_tgt>>).
  Proof.
    exploit sim_promise_weak_list_exists; eauto. i. des.
    clear PROM. ginduction l.
    { i. exists prom_src, mem_src. splits; auto.
      { econs; eauto. }
      { eapply sim_promise_list_nil; eauto. }
    }
    i. destruct a as [loc ts].

    cut (sim_promise_content_strong (self loc ts) (extra_self loc ts)
                                    ((extra_others \\3// extra_self) loc)
                                    loc ts
                                    (Memory.get loc ts prom_src)
                                    (Memory.get loc ts prom_tgt) \/
         exists prom_src' mem_src',
           (<<FUTURE: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
           (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt>>) /\
           (<<PROM: sim_promise_list
                      self extra_self (extra_others \\3// extra_self)
                      prom_src' prom_tgt l>>)).
    { intros H. match goal with
                | [H:?A \/ ?B |- _ ] => cut B
                end.
      { clear H. i. des. exploit IHl.
        { eauto. }
        { eapply MEM0. }
        { eauto. }
        { eapply reserve_future_memory_le; eauto. }
        { eapply reserve_future_memory_finite; eauto. }
        { eapply reserve_future_memory_bot_none; try apply BOTNONESRC; eauto. }
        { eauto. }
        { eauto. }
        i. des. exists prom_src'0, mem_src'0. splits; eauto.
        eapply reserve_future_memory_trans; eauto. }
      { des; eauto. exists prom_src, mem_src. splits; auto.
        { econs; eauto. }
        econs; [|apply SIM|apply SIM]. ii.
        set (PROM:=(sim_promise_list_contents SIM) loc0 ts0).
        ss. des; clarify; auto. }
    }

    set (SIM0:= (sim_promise_list_contents SIM) loc ts). des; auto.
    inv WEAK.
    { left. econs 1; eauto. }
    { left. econs 2; eauto. }
    { clear LIN. symmetry in H. symmetry in H0.
      rename H into PROMTGT. rename H0 into PROMSRC.
      dup PROMSRC. dup PROMTGT. apply MLESRC in PROMSRC0. apply MLETGT in PROMTGT0.
      rename PROMSRC0 into MEMSRC. rename PROMTGT0 into MEMTGT.
      set (MEM0:=(sim_memory_contents MEM) loc ts).
      rewrite MEMSRC in MEM0. rewrite MEMTGT in MEM0. inv MEM0; ss.
      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { left. exploit sim_memory_from_forget; eauto. ss. right. auto. }

      hexploit (@Memory.remove_exists prom_src); eauto.
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src); eauto.
      intros [mem_src' REMOVEMEM].
      assert (REMOVE: Memory.promise prom_src mem_src loc from_src ts Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      destruct (classic (exists from_src', (extra_others \\3// extra_self) loc from_src' from_tgt))
        as [[from_src' EXTRA]|].
      { guardH EXTRA.
        hexploit (@Memory.add_exists mem_src' loc from_src' ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { apply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). inv LHS. econs; ss.
            transitivity from_src'; auto.
            eapply (sim_memory_wf MEM) in EXTRA. des; auto. }
          { eauto. }
          i. destruct H as [EQ|[EQ [FORGET [EXTRA0 TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA0.
            hexploit sim_memory_extra_inj.
            { eapply MEM. }
            { eapply EXTRA0. }
            { eapply EXTRA. }
            i. subst. inv LHS. inv RHS. ss. timetac. }
        }
        { eapply (sim_memory_wf MEM) in EXTRA. destruct EXTRA as [_ EXTRA]. des.
          eapply LB0.
          { eapply MEMWF in MEMTGT. des; auto. }
          { apply memory_get_ts_strong in MEMTGT. des; auto.
            subst. erewrite BOTNONESRC in PROMSRC. clarify. }
        }
        { econs; eauto. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_src' ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; eauto. econs; eauto. econs; eauto. }
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT. econs; eauto.
            { left. eapply sim_memory_wf; eauto. ss. eauto. }
            { i. apply (sim_memory_wf MEM). ss. }
            { i. ss. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. econs; eauto. }
            { guardH o. set (PROM:=(sim_promise_list_contents SIM) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM:=(sim_promise_list_extra SIM) loc0 ts0 SELF).
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
          { eapply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). eauto. }
          { eauto. }
          i. destruct H0 as [EQ|[EQ [FORGET [EXTRA TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA.
            eapply H. esplits; eauto. }
        }
        { apply memory_get_ts_strong in MEMTGT. des; auto. subst.
          erewrite BOTNONESRC in PROMSRC. clarify. }
        { econs. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_tgt ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; eauto. econs; eauto. econs; eauto. }
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT. econs; eauto.
            { refl. }
            { i. apply eq_lb_time. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. eauto. }
            { guardH o. set (PROM:=(sim_promise_list_contents SIM) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM:=(sim_promise_list_extra SIM) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }
    }

    { clear LIN. symmetry in H. symmetry in H0.
      rename H into PROMTGT. rename H0 into PROMSRC.
      dup PROMSRC. dup PROMTGT. apply MLESRC in PROMSRC0. apply MLETGT in PROMTGT0.
      rename PROMSRC0 into MEMSRC. rename PROMTGT0 into MEMTGT.
      set (MEM0:=(sim_memory_contents MEM) loc ts).
      rewrite MEMSRC in MEM0. rewrite MEMTGT in MEM0. inv MEM0; ss. guardH PROM0.
      destruct (classic (self loc from_src)) as [SELF|NSELF].
      { left. exploit sim_memory_from_forget; eauto. ss. right. auto. }

      hexploit (@Memory.remove_exists prom_src); eauto.
      intros [prom_src' REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom_src mem_src); eauto.
      intros [mem_src' REMOVEMEM].
      assert (REMOVE: Memory.promise prom_src mem_src loc from_src ts Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
      { econs; eauto. }
      destruct (classic (exists from_src', (extra_others \\3// extra_self) loc from_src' from_tgt))
        as [[from_src' EXTRA]|].
      { guardH EXTRA.
        hexploit (@Memory.add_exists mem_src' loc from_src' ts Message.reserve).
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit sim_memory_disjoint.
          { eauto. }
          { eauto. }
          { eapply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). inv LHS. econs; ss.
            transitivity from_src'; auto.
            eapply (sim_memory_wf MEM) in EXTRA. des; auto. }
          { eauto. }
          i. destruct H as [EQ|[EQ [FORGET [EXTRA0 TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA0.
            hexploit sim_memory_extra_inj.
            { eapply MEM. }
            { eapply EXTRA0. }
            { eapply EXTRA. }
            i. subst. inv LHS. inv RHS. ss. timetac. }
        }
        { eapply (sim_memory_wf MEM) in EXTRA. destruct EXTRA as [_ EXTRA]. des.
          eapply LB0.
          { eapply MEMWF in MEMTGT. des; auto. }
          { apply memory_get_ts_strong in MEMTGT. des; auto.
            subst. erewrite BOTNONESRC in PROMSRC. clarify. }
        }
        { econs; eauto. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_src' ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; eauto. econs; eauto. econs; eauto. }
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT.
            econs; eauto.
            { left. eapply sim_memory_wf; eauto. ss. eauto. }
            { i. apply (sim_memory_wf MEM). ss. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. econs; eauto. }
            { guardH o. set (PROM1:=(sim_promise_list_contents SIM) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM1:=(sim_promise_list_extra SIM) loc0 ts0 SELF).
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
          { eapply MEMTGT. }
          { eapply GET2. }
          { instantiate (1:=x). eauto. }
          { eauto. }
          i. destruct H0 as [EQ|[EQ [FORGET [EXTRA TS]]]].
          { des; subst. destruct o; ss. }
          { guardH FORGET. guardH EXTRA.
            eapply H. esplits; eauto. }
        }
        { apply memory_get_ts_strong in MEMTGT. des; auto. subst.
          erewrite BOTNONESRC in PROMSRC. clarify. }
        { econs. }
        intros [mem_src'' ADDMEM].
        hexploit (@Memory.add_exists_le prom_src' mem_src'); eauto.
        { eapply promise_memory_le; eauto. }
        intros [prom_src'' ADDPROM].
        assert (ADD: Memory.promise prom_src' mem_src' loc from_tgt ts Message.reserve prom_src'' mem_src'' Memory.op_kind_add).
        { econs; eauto. i. clarify. }
        right. exists prom_src'', mem_src''. splits; eauto.
        { econs; eauto. econs; eauto. econs; eauto. }
        { econs; [|apply MEM]. i.
          erewrite (@Memory.add_o mem_src''); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; subst. rewrite MEMTGT.
            econs; eauto.
            { refl. }
            { apply eq_lb_time. }
          }
          { apply MEM. }
        }
        { econs; [|apply SIM|].
          { i. erewrite (@Memory.add_o prom_src''); eauto.
            erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
            { ss. des; subst. left. rewrite PROMTGT. eauto. }
            { guardH o. set (PROM1:=(sim_promise_list_contents SIM) loc0 ts0).
              des; auto. right. splits; eauto. ss. des; auto.
              clarify. unguard. des; ss. }
          }
          { i. set (PROM1:=(sim_promise_list_extra SIM) loc0 ts0 SELF).
            des. exists to.
            erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto. des_ifs.
            ss. des; subst. clarify. }
        }
      }
    }
    { left. econs 5; eauto. }
  Qed.



  (* sim local *)

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

  Lemma sim_local_tview_le self extra lc_src lc_tgt
        (LOCAL: sim_local self extra lc_src lc_tgt)
    :
      TView.le (Local.tview lc_src) (Local.tview lc_tgt).
  Proof.
    inv LOCAL. ss. refl.
  Qed.

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


  Lemma sim_read_step self others extra_self extra_others lc_src lc_tgt mem_src mem_tgt loc to val released ord
        lc_tgt'
        (STEPTGT: Local.read_step lc_tgt mem_tgt loc to val released ord lc_tgt')
        (MEM: sim_memory L times (others \\2// self) (extra_others \3/ extra_self) mem_src mem_tgt)
        (LOCAL: sim_local self extra_self lc_src lc_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (CONSISTENT: Local.promise_consistent lc_tgt')
        (NOREAD: ~ others loc to)
    :
      exists lc_src',
        (<<STEPSRC: Local.read_step lc_src mem_src loc to val released ord lc_src'>>) /\
        (<<SIM: sim_local self extra_self lc_src' lc_tgt'>>) /\
        (<<GETSRC: exists from, Memory.get loc to mem_src = Some (from, Message.concrete val released)>>) /\
        (<<GETTGT: exists from, Memory.get loc to mem_tgt = Some (from, Message.concrete val released)>>) /\
        (<<RELEASEDMSRC: Memory.closed_opt_view released mem_src>>) /\
        (<<RELEASEDMTGT: Memory.closed_opt_view released mem_tgt>>) /\
        (<<RELEASEDMWF: View.opt_wf released>>)
        /\
        (<<NOREAD: ~ (others \\2// self) loc to>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT.
    set (MEM0:= (sim_memory_contents MEM) loc to). rewrite GET in *. inv MEM0; ss.
    { inv MEMSRC. hexploit CLOSED.
      { symmetry. eapply H0. } i. des. inv MSG_CLOSED. inv MSG_WF.
      inv MEMTGT. hexploit CLOSED1.
      { eapply GET. } i. des. inv MSG_CLOSED. inv MSG_WF.
      esplits; eauto. }
    { exfalso. destruct PROM; auto.
      set (PROM:= (sim_promise_contents PROMS) loc to). inv PROM; ss.
      symmetry in H3. eapply CONSISTENT in H3. ss.
      eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; [apply H3|].
      unfold TimeMap.join, View.singleton_ur_if, View.singleton_ur, View.singleton_rw, TimeMap.singleton.
      etrans; [|eapply Time.join_l]. etrans; [|eapply Time.join_r].
      des_ifs; ss; setoid_rewrite LocFun.add_spec_eq; refl.
    }
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
    - econs; ss; eauto.
      + ii.
        set (PROM:= (sim_promise_contents PROMS) loc t).
        rewrite GET in *. inv PROM; ss.
        exploit RELEASE; eauto.
      + i. eapply sim_promise_bot; eauto.
    - econs; ss; eauto.
  Qed.

  Lemma sim_promise_consistent self extra lc_src lc_tgt
        (CONSISTENT: Local.promise_consistent lc_tgt)
        (SIM: sim_local self extra lc_src lc_tgt)
    :
      Local.promise_consistent lc_src.
  Proof.
    inv SIM. ii. ss.
    set (PROM:= (sim_promise_contents PROMS) loc ts).
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

  Lemma sim_promise_normal others self extra_others extra_self
        mem_src mem_tgt prom_src prom_tgt
        loc from to msg prom_tgt' mem_tgt' kind
        (NLOC: ~ L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg prom_tgt' mem_tgt' kind)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (WFSRC: Memory.le prom_src mem_src)
        (WFTGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (SEMI: semi_closed_message msg mem_src loc to)
    :
      exists prom_src' mem_src',
        (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg prom_src' mem_src' kind>>) /\
        (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt'>>) /\
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
      { i. set (MEM1:= (sim_memory_contents MEM) loc to2).
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
        set (MEM1:= (sim_memory_contents MEM) loc to'). rewrite GET in MEM1. inv MEM1; ss.
        eapply ATTACH; eauto. erewrite NLOC0; eauto. }

      assert (CLOSEDMSG: Memory.closed_message msg mem_src').
      { destruct msg; auto.
        eapply semi_closed_message_add; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + econs.
        { ii. set (MEM1:= (sim_memory_contents MEM) loc0 ts).
          erewrite (@Memory.add_o mem_src'); eauto.
          erewrite (@Memory.add_o mem_tgt'); eauto.
          des_ifs; try by (ss; des; clarify).
          * econs; eauto.
            { ii. ss. des; clarify; eauto. }
            { ii. ss. des; clarify; eauto. }
            { refl. }
            { i. ss. }
        }
        { eapply (sim_memory_wf MEM); eauto. }
      + econs.
        { ii. set (PROM:= (sim_promise_contents PROMISE) loc0 ts).
          erewrite (@Memory.add_o prom_src'); eauto.
          erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
          { ii. eapply NLOC. eapply PROMSWF; ss. right. eauto. }
          { ii. eapply NLOC. eapply EXTRAWF; ss. right. eauto. }
        }
        { apply PROMISE. }
        { i. hexploit (sim_promise_extra PROMISE); eauto. i. des.
          esplits; eauto. erewrite (@Memory.add_o prom_src'); eauto.
          des_ifs. ss. des; clarify.
          exfalso. eapply NLOC. eapply PROMSWF; eauto. right. eauto. }

    (* split case *)
    - exploit split_succeed_wf; try apply PROMISES. i. des. clarify.
      set (PROMISE0:= (sim_promise_contents PROMISE) loc ts3). rewrite GET2 in *.
      inv PROMISE0; ss.
      hexploit (@Memory.split_exists prom_src loc from to ts3 (Message.concrete val'0 released'0)); ss.
      { eauto. }
      intros [prom_src' SPLITPROMSRC].
      exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
      intros [mem_src' SPLITMEMSRC].

      assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val'0 released'0) prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val' released'))).
      { econs; eauto. }

      assert (CLOSEDMSG: Memory.closed_message (Message.concrete val'0 released'0) mem_src').
      { eapply semi_closed_message_split; eauto. }

      exists prom_src', mem_src'. splits; auto.
      + econs.
        { ii. set (MEM1:=(sim_memory_contents MEM) loc0 ts).
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
        { apply (sim_memory_wf MEM); eauto. }
      + econs.
        { ii. set (PROM:= (sim_promise_contents PROMISE) loc0 ts).
          erewrite (@Memory.split_o prom_src'); eauto.
          erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
          * ss. des; clarify. econs; eauto.
            { ii. eapply NLOC. eapply PROMSWF. right. eauto. }
            { ii. eapply NLOC. eapply EXTRAWF. right. eauto. }
          * guardH o. ss. des; clarify. econs; eauto. }
        { apply PROMISE. }
        { i. hexploit (sim_promise_extra PROMISE); eauto. i. des.
          esplits; eauto. erewrite (@Memory.split_o prom_src'); eauto. des_ifs.
          - ss. des; clarify. exfalso. eapply NLOC. eapply PROMSWF; eauto. right. eauto.
          - ss. des; clarify. }

    (* lower case *)
    - exploit lower_succeed_wf; try apply PROMISES. i. des. clarify.
      set (PROMISE0:= (sim_promise_contents PROMISE) loc to). rewrite GET in *. inv PROMISE0; ss.

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
        { ii. set (MEM1:=(sim_memory_contents MEM) loc0 ts).
          erewrite (@Memory.lower_o mem_src'); eauto.
          erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
          ss. des; clarify. econs; eauto.
          * refl.
          * i. ss. }
        { apply (sim_memory_wf MEM); eauto. }
      + econs.
        { ii. set (PROM:= (sim_promise_contents PROMISE) loc0 ts).
          erewrite (@Memory.lower_o prom_src'); eauto.
          erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
          ss. des; clarify. econs; eauto. }
        { apply PROMISE. }
        { i. hexploit (sim_promise_extra PROMISE); eauto. i. des.
          esplits; eauto. erewrite (@Memory.lower_o prom_src'); eauto. des_ifs.
          ss. des; clarify. }

    (* cancel case *)
    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      set (PROMISE0 := (sim_promise_contents PROMISE) loc to). rewrite GET in *.
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
        { ii. set (MEM1:=(sim_memory_contents MEM) loc0 ts).
          erewrite (@Memory.remove_o mem_src'); eauto.
          erewrite (@Memory.remove_o mem_tgt'); eauto.
          des_ifs; try by (des; ss; clarify).
          * ss. des; clarify. econs; eauto. }
        { apply MEM. }
      + econs.
        { ii. set (PROM:= (sim_promise_contents PROMISE) loc0 ts).
          erewrite (@Memory.remove_o prom_src'); eauto.
          erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
          ss. des; clarify. econs 2; eauto. }
        { apply PROMISE. }
        { i. hexploit (sim_promise_extra PROMISE); eauto. i. des.
          esplits; eauto. erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
          ss. des; clarify. exfalso. eapply NLOC. eapply PROMSWF; eauto. right. eauto. }
  Qed.

  Lemma sim_write_step_normal
        others self extra_others extra_self lc_src lc_tgt sc mem_src mem_tgt
        lc_tgt' sc' mem_tgt' loc from to val ord releasedm released kind
        (NLOC: ~ L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
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
        (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self extra_self lc_src' lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv WRITE. inv SIM. inv LOCALSRC. inv LOCALTGT.

    hexploit sim_promise_normal; eauto.
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
    { set (PROM:= (sim_promise_contents PROMISE0) loc to).
      eapply Memory.remove_get0 in REMOVE. des.
      rewrite GET in *. inv PROM; ss. }
    intros [prom_src'' REMOVESRC].

    assert (NSELF: forall ts, ~ self loc ts).
    { ii. set (PROM:= (sim_promise_contents PROMISE0) loc to). inv PROM; ss.
      eapply NLOC. eapply sim_memory_others_self_wf; eauto. ss. right. eauto. }

    esplits; eauto.

    - econs; ss.
      + econs; eauto.
      + ii. set (PROM:=(sim_promise_contents PROMS) loc t).
        rewrite GET in *. inv PROM; ss.
        exploit RELEASE; eauto.

    - econs; auto. econs.
      { ii. set (PROM:=(sim_promise_contents PROMISE0) loc0 ts).
        erewrite (@Memory.remove_o prom_src''); eauto.
        erewrite (@Memory.remove_o promises2); eauto. des_ifs.
        ss. des; subst. econs 2; eauto.
        ii. exploit sim_memory_extra_others_self_wf.
        { eapply MEM0. }
        { right. eauto. }
        { ii. ss. }
      }
      { apply PROMISE0. }
      { i. set (PROM:=(sim_promise_extra PROMISE0) loc0 ts SELF). des.
        esplits; eauto. erewrite (@Memory.remove_o prom_src''); eauto.
        des_ifs. ss. des; clarify. exfalso. eapply NSELF; eauto. }
  Qed.

  Lemma sim_promise_step_normal others self extra_others extra_self
        mem_src mem_tgt mem_tgt' lc_src lc_tgt lc_tgt' loc from to msg kind
        (NLOC: ~ L loc)
        (STEPTGT: Local.promise_step lc_tgt mem_tgt loc from to msg lc_tgt' mem_tgt' kind)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCAL: sim_local self extra_self lc_src lc_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LCSRC: Local.wf lc_src mem_src)
        (LCTGT: Local.wf lc_tgt mem_tgt)
        (SEMI: semi_closed_message msg mem_src loc to)
    :
      exists lc_src' mem_src',
        (<<STEPSRC: Local.promise_step lc_src mem_src loc from to msg lc_src' mem_src' kind>>) /\
        (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt'>>) /\
        (<<LOCAL: sim_local self extra_self lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv LCSRC. inv LCTGT. inv STEPTGT. ss.
    hexploit sim_promise_normal; eauto. i. des.
    exists (Local.mk tvw prom_src'), mem_src'. splits; eauto.
  Qed.

  Lemma sim_promise_forget others (self: Loc.t -> Time.t -> Prop) extra_others extra_self
        mem_src mem_tgt prom_src prom_tgt
        loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt
        (LOC: L loc)
        (STEPTGT: Memory.promise prom_tgt mem_tgt loc from to msg_tgt prom_tgt' mem_tgt' kind_tgt)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (MEMWF: memory_times_wf times mem_tgt')
        (SEMI: semi_closed_message msg_tgt mem_src loc to)
    :
      (exists prom_src' mem_src' self' extra_self',
          (<<STEPSRC: reserve_future_memory prom_src mem_src prom_src' mem_src'>>) /\
          (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src' mem_tgt'>>) /\
          (<<PROMISE: sim_promise self' extra_self' prom_src' prom_tgt'>>) /\
          (<<SELF: __guard__(self' loc to \/ msg_tgt = Message.reserve)>>)) \/
      (exists prom_src' mem_src',
          (<<STEPSRC: Memory.promise prom_src mem_src loc from to msg_tgt prom_src' mem_src' kind_tgt>>) /\
          (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt'>>) /\
          (<<PROMISE: sim_promise self extra_self prom_src' prom_tgt'>>) /\
          (<<CLOSED: Memory.closed_message msg_tgt mem_src'>>) /\
          (<<SELF: ~ self loc to>>))
  .
  Proof.
    inv STEPTGT.

    - left. exploit add_succeed_wf; try apply MEM0. i. des.
      assert (exists from_src,
                 (<<FROM: Time.le from from_src>>) /\
                 (<<TO: Time.lt from_src to>>) /\
                 (<<LB: lb_time (times loc) from from_src>>) /\
                 (<<EMPTY: forall to2 from2 msg2
                                  (GET: Memory.get loc to2 mem_src = Some (from2, msg2)),
                     Interval.disjoint (from_src, to) (from2, to2)>>)).
      { destruct (classic (exists from_src,
                              (extra_others \\3// extra_self) loc from_src from)).
        { des. hexploit ((sim_memory_wf MEM) loc from from_src); eauto. i. des.
          exists from_src. splits; eauto.
          { left. eauto. }
          { eapply Memory.add_get0 in MEM0. des.
            eapply MEMWF in GET0. des.
            eapply LB in TO. auto. }
          i. hexploit sim_memory_get_larger; eauto. i. des.
          { ii. eapply DISJOINT; eauto.
            { instantiate (1:=x). inv LHS. econs; ss.
              transitivity from_src; eauto. }
            { inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
          }
          { hexploit ((sim_memory_wf MEM) loc from2 to2); eauto. i. des.
            ii. inv LHS. inv RHS. ss.
            set (MEM1:=(sim_memory_contents MEM) loc from_src).
            inv MEM1; try by (exfalso; eapply NEXTRA; eauto); ss.
            set (MEM2:=(sim_memory_contents MEM) loc to2).
            inv MEM2; try by (exfalso; eapply NEXTRA; eauto); ss.
            symmetry in H1. symmetry in H3. hexploit memory_get_disjoint_strong.
            { eapply H3. }
            { eapply H1. }
            i. des; clarify.
            { timetac. }
            { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply TS3. } etrans.
              { left. eapply FROM. }
              { eauto. }
            }
            { set (MEM3:=(sim_memory_contents MEM) loc from2). inv MEM3; ss.
              symmetry in H6. eapply DISJOINT.
              { eapply H6. }
              { instantiate (1:=from2). econs; ss.
                { eapply TimeFacts.lt_le_lt; eauto. }
                { transitivity x; auto. left. auto. }
              }
              { econs; ss.
                { apply memory_get_ts_strong in H6. des; auto.
                  subst. inv MEMSRC. rewrite INHABITED in H5. clarify. }
                { refl. }
              }
            }
          }
        }
        { exists from. splits; auto.
          { refl. }
          { apply eq_lb_time. }
          { i. hexploit sim_memory_get_larger; eauto. i. des.
            { ii. eapply DISJOINT; eauto.
              inv RHS. econs; ss. eapply TimeFacts.le_lt_lt; eauto. }
            { hexploit ((sim_memory_wf MEM) loc from2 to2); eauto. i. des.
              ii. inv LHS. inv RHS. ss.
              set (MEM1:=(sim_memory_contents MEM) loc from2).
              inv MEM1; try by (exfalso; eapply NPROM; eauto); ss.
              symmetry in H2. hexploit memory_get_disjoint_strong.
              { eapply Memory.add_get0. eapply MEM0. }
              { eapply Memory.add_get1; eauto. }
              i. des; subst.
              { eapply Memory.add_get0 in MEM0. des. clarify. }
              { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                { eapply TS2. } etrans.
                { left. eapply FROM0. }
                { eauto. }
              }
              { destruct TS1; cycle 1.
                { inv H0. eapply H. eauto. }
                { exploit LB.
                  { instantiate (1:=from).
                    eapply Memory.add_get0 in MEM0. des.
                    eapply MEMWF in GET1. des. auto. }
                  { auto. }
                  { i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                    { eapply FROM. } etrans.
                    { eapply TO0. }
                    { left. auto. }
                  }
                }
              }
            }
          }
        }
      }

      des. hexploit (@Memory.add_exists mem_src loc from_src to Message.reserve); eauto.
      { econs. }
      intros [mem_src0 ADDMEM0].
      hexploit (@Memory.add_exists_le prom_src mem_src loc from_src to Message.reserve); eauto.
      intros [prom_src0 ADDPROM0].
      assert (PROMISE0: Memory.promise prom_src mem_src loc from_src to Message.reserve prom_src0 mem_src0 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      assert (GETMEMNONE: Memory.get loc to mem_src = None).
      { eapply Memory.add_get0; eauto. }
      assert (GETPROMNONE: Memory.get loc to prom_src = None).
      { destruct (Memory.get loc to prom_src) eqn:EQ; auto.
        destruct p. apply MLESRC in EQ. clarify. }
      hexploit sim_memory_src_none.
      { eauto. }
      { eapply GETMEMNONE. } i. des.
      hexploit sim_promise_src_none.
      { eauto. }
      { eapply GETPROMNONE. } i. des.

      destruct msg_tgt as [val released|].
      { hexploit (@lb_time_exists (times loc) (@WO loc) to). i. des.
        hexploit (@Memory.add_exists mem_src0 loc to ts' Message.reserve); eauto.
        { i. erewrite Memory.add_o in GET2; eauto. des_ifs.
          { ss. des; subst. ii. inv LHS. inv RHS. ss. timetac. }
          des; ss. hexploit sim_memory_get_larger; eauto. i. des.
          { ii. inv LHS. inv RHS. ss.
            dup GETTGT1. eapply Memory.add_get1 in GETTGT1; eauto.
            hexploit memory_get_disjoint_strong.
            { eapply GETTGT1. }
            { eapply Memory.add_get0; eauto. }
            i. des; clarify.
            { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
              { eapply TS3. } etrans.
              { left. eapply FROM0. }
              { eauto. }
            }
            { destruct TS2.
              { exploit LB0.
                { instantiate (1:=from_tgt).
                  eapply MEMWF in GETTGT1. des. auto. }
                { auto. }
                { i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                  { eapply x0. } etrans.
                  { eapply TS1. } etrans.
                  { left. eapply FROM1. }
                  { eauto. }
                }
              }
              { inv H. eapply ATTACH; eauto. }
            }
          }
          { hexploit ((sim_memory_wf MEM) loc from2 to2); eauto. i. des.
            set (MEM1:=(sim_memory_contents MEM) loc from2).
            inv MEM1; ss.
            symmetry in H. hexploit memory_get_disjoint_strong.
            { eapply Memory.add_get1 in H; [|eauto]. eapply H. }
            { eapply Memory.add_get0; eauto. }
            i. des; clarify.
            { ii. inv LHS. inv RHS. ss. exploit LB1.
              { instantiate (1:=to).
                apply Memory.add_get0 in MEM0. des.
                apply MEMWF in GET0. des. auto. }
              { auto. }
              { i. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
                { eapply FROM1. } etrans.
                { eapply TO2. }
                { left. eauto. }
              }
            }
            { eapply interval_le_disjoint.
              left. eapply LB0; auto.
              eapply Memory.add_get1 in H; eauto.
              eapply MEMWF in H. des. auto. }
          }
        }
        { econs. }
        intros [mem_src1 ADDMEM1].
        hexploit (@Memory.add_exists_le prom_src0 mem_src0 loc to ts' Message.reserve); eauto.
        { eapply promise_memory_le; cycle 1; eauto. }
        intros [prom_src1 ADDPROM1].
        assert (PROMISE1: Memory.promise prom_src0 mem_src0 loc to ts' Message.reserve prom_src1 mem_src1 Memory.op_kind_add).
        { econs; eauto. i. clarify. }

        assert (GETMEMNONE0: Memory.get loc ts' mem_src = None).
        { destruct (Memory.get loc ts' mem_src) eqn:EQ; auto.
          destruct p. eapply Memory.add_get1 in EQ; eauto.
          eapply Memory.add_get0 in ADDMEM1. des. clarify. }
        assert (GETPROMNONE0: Memory.get loc ts' prom_src = None).
        { destruct (Memory.get loc ts' prom_src) eqn:EQ; auto.
          destruct p. eapply MLESRC in EQ. clarify. }
        hexploit sim_memory_src_none.
        { eauto. }
        { eapply GETMEMNONE0. } i. des.
        hexploit sim_promise_src_none.
        { eauto. }
        { eapply GETPROMNONE0. } i. des.

        exists prom_src1, mem_src1,
        (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                         then True else self loc' ts'),
        (fun l t => if (loc_ts_eq_dec (l, t) (loc, ts'))
                    then (eq to)
                    else extra_self l t). splits; eauto.
        { econs; eauto. econs; eauto. econs; eauto. }
        { econs.
          { i. erewrite (@Memory.add_o mem_src1); eauto.
            erewrite (@Memory.add_o mem_src0); eauto.
            erewrite (@Memory.add_o mem_tgt'); eauto. des_ifs.
            { ss. des; clarify. timetac. }
            { ss. des; clarify. econs 3; eauto. right. auto. }
            { ss. des; clarify. erewrite GETTGT1.
              econs 4; eauto. right. auto. }
            { eapply (sim_memory_contents MEM). }
          }
          { i. des_ifs; eauto.
            { ss. des; clarify. splits; auto.
              { right. auto. }
              { i. destruct EXTRA0; auto.
                exfalso. eapply NEXTRA1. left. eauto. }
            }
            { apply (sim_memory_wf MEM) in EXTRA. ss. des; clarify. }
            { ss. des; clarify. destruct EXTRA as [EXTRA|EQ]; subst; ss.
              hexploit ((sim_memory_wf MEM) loc from0 ts').
              { left. auto. }
              i. des. splits; auto.
              i. destruct EXTRA0 as [EXTRA0|EQ].
              { exfalso. eapply NEXTRA1. left. eauto. }
              { subst. exfalso. eapply NEXTRA1. left. eauto. }
            }
            { eapply (sim_memory_wf MEM). auto. }
          }
        }
        { econs.
          { i. erewrite (@Memory.add_o prom_src1); eauto.
            erewrite (@Memory.add_o prom_src0); eauto.
            erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
            { ss. des; clarify. timetac. }
            { ss. des; clarify. econs 4; eauto. }
            { ss. des; clarify. erewrite GETTGT2. econs 5; eauto. }
            { eapply (sim_promise_contents PROMISE). }
          }
          { i. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify.
              hexploit ((sim_promise_wf PROMISE) loc to ts); auto.
              i. des. splits; auto. }
            { ss. des; clarify. }
            { eapply (sim_promise_wf PROMISE); auto. }
          }
          { i. des_ifs.
            { ss. des; clarify. exists ts'. splits; auto.
              eapply Memory.add_get0; eauto. }
            { guardH o. eapply (sim_promise_extra PROMISE) in SELF. des.
              exists to0. splits; eauto.
              eapply Memory.add_get1; eauto. eapply Memory.add_get1; eauto. }
          }
        }
        { left. des_ifs. ss. des; clarify. }
      }

      exists prom_src0, mem_src0, self, extra_self. splits; eauto.
      { econs; eauto. econs; eauto. }
      { econs.
        { i. erewrite (@Memory.add_o mem_src0); eauto.
          erewrite (@Memory.add_o mem_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs 2; eauto. i. ss. }
          { eapply (sim_memory_contents MEM). }
        }
        { eapply (sim_memory_wf MEM). }
      }
      { econs.
        { i. erewrite (@Memory.add_o prom_src0); eauto.
          erewrite (@Memory.add_o prom_tgt'); eauto. des_ifs.
          { ss. des; clarify. econs 3; eauto. }
          { eapply (sim_promise_contents PROMISE). }
        }
        { eapply (sim_promise_wf PROMISE). }
        { i. eapply (sim_promise_extra PROMISE) in SELF. des.
          exists to0. splits; eauto. eapply Memory.add_get1; eauto.  }
      }
      { right. auto. }

    - des. subst.
      exploit split_succeed_wf; try apply PROMISES. i. des.
      dup GET2. apply MLETGT in GET0.
      set (PROM:=(sim_promise_contents PROMISE) loc ts3).
      rewrite GET2 in PROM.

      set (MEM1:=(sim_memory_contents MEM) loc ts3). rewrite GET0 in MEM1.
      destruct (classic (self loc ts3)) as [SELF|NSELF].
      2: {
        right. inv PROM; ss.
        hexploit (@Memory.split_exists prom_src loc from to ts3 (Message.concrete val'0 released'0)); ss.
        { eauto. }
        intros [prom_src' SPLITPROMSRC].
        exploit Memory.split_exists_le; try apply SPLITPROMSRC; eauto.
        intros [mem_src' SPLITMEMSRC].

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val'0 released'0) prom_src' mem_src' (Memory.op_kind_split ts3 (Message.concrete val' released'))).
        { econs; eauto. }

        assert (CLOSEDMSG: Memory.closed_message (Message.concrete val'0 released'0) mem_src').
        { eapply semi_closed_message_split; eauto. }

        assert (PROMSWF0: ~ (others loc to \/ self loc to)).
        { set (MEM2:=(sim_memory_contents MEM) loc to). inv MEM2; clarify.
          eapply Memory.split_get0 in SPLITMEMSRC. des. rewrite GET in *. clarify. }

        assert (EXTRAWF0: forall t : Time.t, ~ __guard__ (extra_others loc to t \/ extra_self loc to t)).
        { ii. set (MEM2:=(sim_memory_contents MEM) loc to). inv MEM2; clarify.
          - eapply NEXTRA0; eauto.
          - eapply NEXTRA0; eauto.
          - eapply Memory.split_get0 in SPLITMEMSRC. des. rewrite GET in *. clarify. }

        assert (PROMSWF1: ~ (others loc ts3 \/ self loc ts3)).
        { set (MEM2:=(sim_memory_contents MEM) loc ts3). inv MEM2; clarify.
          eapply Memory.split_get0 in SPLITMEMSRC. des. rewrite GET1 in *. clarify. }

        assert (EXTRAWF1: forall t : Time.t, ~ __guard__ (extra_others loc ts3 t \/ extra_self loc ts3 t)).
        { ii. set (MEM2:=(sim_memory_contents MEM) loc ts3). inv MEM2; clarify.
          - eapply NEXTRA0; eauto.
          - eapply NEXTRA0; eauto.
          - eapply Memory.split_get0 in SPLITMEMSRC. des. rewrite GET1 in *. clarify. }

        exists prom_src', mem_src'. splits; auto.
        + econs.
          { ii. set (MEM2:=(sim_memory_contents MEM) loc0 ts).
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
          { apply (sim_memory_wf MEM); eauto. }
        + econs.
          { ii. set (PROM:= (sim_promise_contents PROMISE) loc0 ts).
            erewrite (@Memory.split_o prom_src'); eauto.
            erewrite (@Memory.split_o prom_tgt'); eauto. des_ifs.
            * ss. des; clarify. econs; eauto.
              ii. eapply EXTRAWF0; eauto. right. eauto.
            * guardH o. ss. des; clarify. econs; eauto. }
          { apply PROMISE. }
          { i. hexploit (sim_promise_extra PROMISE); eauto. i. des.
            esplits; eauto. erewrite (@Memory.split_o prom_src'); eauto. des_ifs.
            - ss. des; clarify. exfalso.
              eapply Memory.split_get0 in SPLITPROMSRC. des. clarify.
            - ss. des; clarify. }
      }

      left.
      assert (exists from_src,
                 (<<GETSRC: Memory.get loc ts3 prom_src = Some (from_src, Message.reserve)>>) /\
                 (<<LB: lb_time (times loc) from from_src>>) /\
                 (<<FROM: Time.le from from_src>>)).
      { inv PROM; ss.
        { symmetry in H0. apply MLESRC in H0.
          rewrite H0 in *. inv MEM1. esplits; eauto. }
      } des.
      assert (TS0: Time.lt from_src to).
      { eapply LB; auto.
        apply Memory.split_get0 in MEM0. des.
        eapply MEMWF in GET4. des. auto. }

      assert (NEXTRATO: forall t, ~ (extra_others loc to t \/ extra_self loc to t)).
      { set (MEM2:=(sim_memory_contents MEM) loc to).
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
      { econs; eauto. econs; eauto. econs; eauto. econs; eauto. }
      { econs.
        { i. erewrite (@Memory.split_o mem_tgt'); eauto.
          erewrite (@Memory.add_o mem_src2); eauto.
          erewrite (@Memory.add_o mem_src1); eauto.
          erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
          { ss. des; subst. exfalso. eapply Time.lt_strorder; eauto. }
          { ss. des; clarify. econs 3; auto. right. auto. }
          { ss. des; clarify. inv PROM; ss.
            { dup H0. symmetry in H0. apply MLESRC in H0.
              rewrite H0 in *. inv MEM1.
              econs 3; eauto.
              { refl. }
              { i. apply eq_lb_time. }
            }
          }
          { eapply ((sim_memory_contents MEM)). }
        }
        { i. dup EXTRA.
          apply ((sim_memory_wf MEM)) in EXTRA0. des_ifs.
          destruct a. ss. subst. splits; try apply EXTRA0; auto. right. auto. }
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
            { econs 4; eauto. }
          }
          { eapply ((sim_promise_contents PROMISE)). }
        }
        { i. dup EXTRA.
          apply ((sim_promise_wf PROMISE)) in EXTRA0. des_ifs.
          destruct a. ss. subst. splits; try apply EXTRA0; auto. }
        { i. des_ifs.
          { ss. des. subst.
            eapply Memory.add_get0 in ADDPROM2. des. esplits; eauto. }
          { clear SELF. guardH o. apply (sim_promise_extra PROMISE) in SELF0. des.
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
      { left. des_ifs. ss. des; clarify. }

    - des. subst.
      exploit lower_succeed_wf; try apply PROMISES. i. des. inv MSG_LE.
      rename GET into GETPROMTGT.
      dup GETPROMTGT. apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.
      set (PROM:=(sim_promise_contents PROMISE) loc to).
      rewrite GETPROMTGT in PROM. inv PROM; ss.

      { right.
        hexploit (@Memory.lower_exists prom_src loc from to (Message.concrete val released) (Message.concrete val released0)); ss; eauto.
        intros [prom_src' LOWERPROMSRC].
        exploit Memory.lower_exists_le; try apply LOWERPROMSRC; eauto.
        intros [mem_src' LOWERMEMSRC].

        assert (PROMISESRC: Memory.promise prom_src mem_src loc from to (Message.concrete val released0) prom_src' mem_src' (Memory.op_kind_lower (Message.concrete val released))).
        { econs; eauto. }

        assert (CLOSEDMSG: Memory.closed_message (Message.concrete val released0) mem_src').
        { eapply semi_closed_message_lower; eauto. }

        assert (PROMSWF0: ~ (others loc to \/ self loc to)).
        { set (MEM2:=(sim_memory_contents MEM) loc to). inv MEM2; clarify.
          eapply Memory.lower_get0 in LOWERMEMSRC. des. rewrite GET in *. clarify. }

        assert (EXTRAWF0: forall t : Time.t, ~ __guard__ (extra_others loc to t \/ extra_self loc to t)).
        { ii. set (MEM2:=(sim_memory_contents MEM) loc to). inv MEM2; clarify.
          - eapply NEXTRA0; eauto.
          - eapply NEXTRA0; eauto.
          - eapply Memory.lower_get0 in LOWERMEMSRC. des. rewrite GET in *. clarify. }

        exists prom_src', mem_src'. splits; auto.
        + econs.
          { ii. set (MEM1:=(sim_memory_contents MEM) loc0 ts).
            erewrite (@Memory.lower_o mem_src'); eauto.
            erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
            ss. des; clarify. econs; eauto.
            * refl.
            * i. ss. }
          { apply (sim_memory_wf MEM); eauto. }
        + econs.
          { ii. set (PROM:= (sim_promise_contents PROMISE) loc0 ts).
            erewrite (@Memory.lower_o prom_src'); eauto.
            erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
            ss. des; clarify. econs; eauto. }
          { apply PROMISE. }
          { i. hexploit (sim_promise_extra PROMISE); eauto. i. des.
            esplits; eauto. erewrite (@Memory.lower_o prom_src'); eauto. des_ifs.
            ss. des; clarify. }
      }

      left. symmetry in H0. dup H0. apply MLESRC in H0.
      rename H0 into GETMEMSRC. rename H1 into GETPROMSRC.
      set (MEM1:=(sim_memory_contents MEM) loc to).
      rewrite GETMEMSRC in MEM1. rewrite GETMEMTGT in MEM1. inv MEM1. clear PROM.

      exists prom_src, mem_src, self, extra_self. splits; auto.
      { econs. }
      { econs.
        { i. erewrite (@Memory.lower_o mem_tgt'); eauto. des_ifs.
          { ss. des; subst. rewrite GETMEMSRC. econs; eauto. right. auto. }
          { eapply (sim_memory_contents MEM). }
        }
        { apply (sim_memory_wf MEM). }
      }
      { econs.
        { i. erewrite (@Memory.lower_o prom_tgt'); eauto. des_ifs.
          { ss. des; subst. rewrite GETPROMSRC. econs; eauto. }
          { eapply (sim_promise_contents PROMISE). }
        }
        { apply (sim_promise_wf PROMISE). }
        { apply (sim_promise_extra PROMISE). }
      }
      { left. auto. }

    - exploit Memory.remove_get0; try apply PROMISES. i. des.
      rename GET into GETPROMTGT.
      dup GETPROMTGT. apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.
      set (PROM:=(sim_promise_contents PROMISE) loc to).
      rewrite GETPROMTGT in PROM.

      assert (INV: exists from_src, <<NPROM: ~ self loc to>> /\ <<NEXTRA: forall t, ~ extra_self loc to t>> /\ <<H0: Some (from_src, Message.reserve) = Memory.get loc to prom_src>>).
      { inv PROM; eauto. } des. clear PROM. left.

      symmetry in H0. dup H0. apply MLESRC in H0.
      rename H0 into GETMEMSRC. rename H1 into GETPROMSRC.
      set (MEM1:=(sim_memory_contents MEM) loc to).
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
        { ss. right. auto. } i. subst.
        assert (TS: Time.lt from to).
        { apply memory_get_ts_strong in GETPROMSRC. des; auto.
          subst. clarify. }
        assert (exists ts', (<<LB: lb_time (times loc) from ts'>>) /\
                            (<<TS0: Time.lt from ts'>>) /\
                            (<<TS1: Time.lt ts' to>>)).
        { hexploit (@lb_time_exists (times loc) (@WO loc) from). i. des.
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
        { ii. erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o.
          hexploit Memory.get_disjoint.
          { eapply GET2. }
          { eapply GETMEMSRC. }
          i. des.
          { subst. destruct o; ss. }
          { eapply H.
            { eapply RHS. }
            { inv LHS. econs; ss. etrans; eauto. left. auto. }
          }
        }
        { econs. }
        intros [mem_src1 ADDMEM].
        hexploit (@Memory.add_exists_le prom_src0 mem_src0 loc from ts' Message.reserve); eauto.
        { eapply promise_memory_le; try apply PROMISE0; eauto. }
        intros [prom_src1 ADDPROM].
        assert (PROMISE1: Memory.promise prom_src0 mem_src0 loc from ts' Message.reserve prom_src1 mem_src1 Memory.op_kind_add).
        { econs; eauto. i. clarify. }

        assert (GETMEMNONE: Memory.get loc ts' mem_src = None).
        { destruct (Memory.get loc ts' mem_src) eqn:GET; auto. destruct p.
          hexploit memory_get_disjoint_strong.
          { eapply GET. }
          { eapply GETMEMSRC. } i. des; subst.
          { timetac. }
          { timetac. }
          { exfalso. eapply Time.lt_strorder.
            transitivity ts'; eauto. }
        }
        assert (GETPROMNONE: Memory.get loc ts' prom_src = None).
        { destruct (Memory.get loc ts' prom_src) eqn:EQ; auto.
          destruct p. apply MLESRC in EQ. clarify. }
        hexploit sim_memory_src_none.
        { eauto. }
        { eapply GETMEMNONE. } i. des.
        hexploit sim_promise_src_none.
        { eauto. }
        { eapply GETPROMNONE. } i. des.

        exists prom_src1, mem_src1, self,
        (fun l t => if (loc_ts_eq_dec (l, t) (loc, ts'))
                    then (eq from)
                    else extra_self l t). splits; eauto.
        { econs; eauto. econs; eauto. econs; eauto. }
        { econs.
          { i. erewrite (@Memory.remove_o mem_tgt'); eauto.
            erewrite (@Memory.add_o mem_src1); eauto.
            erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. rewrite GETTGT. econs 4; eauto. right. auto. }
            { ss. des; clarify. econs 1; eauto. }
            { eapply (sim_memory_contents MEM). }
          }
          { i. des_ifs.
            { ss. des; clarify. destruct EXTRA as [EXTRA|EQ].
              { hexploit ((sim_memory_wf MEM) loc from0 ts'); eauto.
                { left. auto. }
                i. des. splits; auto. i. des_ifs; eauto.
                ss. des; clarify. destruct EXTRA0.
                { exfalso. eapply NEXTRA1. left. eauto. }
                { subst. exfalso. eapply NEXTRA1. left. eauto. }
              }
              { subst. splits; auto.
                { right. auto. }
                { i. des_ifs. ss. des; clarify.
                  destruct EXTRA as [EXTRA|EQ]; auto.
                  exfalso. eapply NEXTRA1. left. eauto. }
              }
            }
            { hexploit ((sim_memory_wf MEM) loc0 from0 ts); eauto. }
          }
        }
        { econs.
          { i. erewrite (@Memory.remove_o prom_tgt'); eauto.
            erewrite (@Memory.add_o prom_src1); eauto.
            erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
            { ss. des; clarify. }
            { ss. des; clarify. rewrite GETTGT0. econs 5; eauto. }
            { ss. des; clarify. eauto. }
            { eapply (sim_promise_contents PROMISE). }
          }
          { i. des_ifs.
            { ss. des; clarify. }
            { eapply (sim_promise_wf PROMISE); eauto. }
          }
          { i. hexploit ((sim_promise_extra PROMISE) loc0 ts); eauto. i. des.
            destruct (loc_ts_eq_dec (loc0, ts) (loc, from)).
            { ss. des. clarify. exists ts'. splits; auto.
              eapply Memory.add_get0; eauto. }
            { exists to0. splits; auto.
              erewrite Memory.add_o; eauto. erewrite Memory.remove_o; eauto.
              des_ifs.
              { ss. des; clarify. }
              { ss. des; clarify. }
            }
          }
        }
        { right. auto. }
      }
      { exists prom_src0, mem_src0, self, extra_self. splits; eauto.
        { econs; eauto. econs; eauto. }
        { econs.
          { i. erewrite (@Memory.remove_o mem_tgt'); eauto.
            erewrite (@Memory.remove_o mem_src0); eauto. des_ifs.
            { ss. des; subst. econs 1; eauto. }
            { eapply (sim_memory_contents MEM). }
          }
          { apply (sim_memory_wf MEM). }
        }
        { econs.
          { i. erewrite (@Memory.remove_o prom_tgt'); eauto.
            erewrite (@Memory.remove_o prom_src0); eauto. des_ifs.
            { ss. des; subst. eauto. }
            { eapply (sim_promise_contents PROMISE). }
          }
          { apply (sim_promise_wf PROMISE). }
          { i. dup SELF. apply (sim_promise_extra PROMISE) in SELF. des.
            destruct (loc_ts_eq_dec (loc0, to0) (loc, to)).
            { ss. des; clarify. }
            { exists to0. splits; auto. erewrite Memory.remove_o; eauto. des_ifs.
              ss. des; clarify. }
          }
        }
        { right. auto. }
      }
  Qed.


  Lemma sim_fulfill_forget from_src' others (self: Loc.t -> Time.t -> Prop) extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt prom_tgt'
        loc from_tgt to val released
        (LOC: L loc)
        (SELF: self loc to)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (BOTNONETGT: Memory.bot_none prom_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (REMOVE: Memory.remove prom_tgt loc from_tgt to (Message.concrete val released) prom_tgt')
        (CLOSED: Memory.closed mem_tgt)

        (FROMSRC0: Time.le from_tgt from_src')
        (FROMSRC1: forall from_src msg
                          (GET: Memory.get loc to mem_src = Some (from_src, msg)),
            Time.le from_src' from_src)
        (EMPTY: forall from_src msg
                          (GET: Memory.get loc to mem_src = Some (from_src, msg))
                          ts (ITV: Interval.mem (from_src', from_src) ts),
            Memory.get loc ts mem_src = None)
        (MEMWF: memory_times_wf times mem_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src prom_src loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src prom_src loc' ts' from' Message.reserve>>))

        (CONSISTENT: forall to' from' val' released'
                            (GETTGT: Memory.get loc to' prom_tgt' = Some (from', Message.concrete val' released')),
            Time.lt to to')
    :
      exists prom_src0 mem_src0 mem_src1 prom_src2 mem_src2 self' extra_self',
        (<<FUTURE0: reserve_future_memory prom_src mem_src prom_src0 mem_src0>>) /\
        (<<WRITE: Memory.write prom_src0 mem_src0 loc from_src' to val released prom_src0 mem_src1 Memory.op_kind_add>>) /\
        (<<FROM: Time.le from_tgt from_src'>>) /\
        (<<FUTURE1: reserve_future_memory prom_src0 mem_src1 prom_src2 mem_src2>>) /\
        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src2 mem_tgt>>) /\
        (<<PROMISE: sim_promise
                      self' extra_self'
                      prom_src2 prom_tgt'>>).
  Proof.
    hexploit Memory.remove_get0; try apply REMOVE. i. des.
    rename GET into GETPROMTGT. dup GETPROMTGT.
    apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.

    set (PROM := (sim_promise_contents PROMISE) loc to).
    rewrite GETPROMTGT in PROM. inv PROM; ss.

    symmetry in H0. rename H0 into GETPROMSRC.
    dup GETPROMSRC. apply MLESRC in GETPROMSRC0. rename GETPROMSRC0 into GETMEMSRC.

    set (MEM0 := (sim_memory_contents MEM) loc to).
    rewrite GETMEMSRC in *. rewrite GETMEMTGT in *.
    inv MEM0; try by (exfalso; apply NPROM; right; auto).

    specialize (FROMSRC1 _ _ eq_refl).
    specialize (EMPTY _ _ eq_refl).
    assert (LB': lb_time (times loc) from_tgt from_src').
    { eapply lb_time_lower; eauto. }

    assert (NOTHER: ~ others loc to).
    { intros OTHER. eapply EXCLUSIVE in OTHER. des. inv UNCH. clarify. }

    hexploit ((sim_promise_extra PROMISE)); eauto. i. des.

    hexploit (@Memory.remove_exists prom_src loc to to0 Message.reserve).
    { eauto. }
    intros [prom_src' REMOVEPROM0].
    hexploit (@Memory.remove_exists_le prom_src mem_src loc to to0 Message.reserve); eauto.
    intros [mem_src' REMOVEMEM0].
    assert (PROMISE0: Memory.promise prom_src mem_src loc to to0 Message.reserve prom_src' mem_src' Memory.op_kind_cancel).
    { econs; eauto. }

    hexploit (@Memory.remove_exists prom_src' loc from_src to Message.reserve).
    { erewrite Memory.remove_o; eauto. des_ifs.
      ss. des; subst. timetac. }
    intros [prom_src0 REMOVEPROM1].
    hexploit (@Memory.remove_exists_le prom_src' mem_src' loc from_src to Message.reserve); eauto.
    { eapply promise_memory_le; cycle 1; eauto. }
    intros [mem_src0 REMOVEMEM1].
    assert (PROMISE1: Memory.promise prom_src' mem_src' loc from_src to Message.reserve prom_src0 mem_src0 Memory.op_kind_cancel).
    { econs; eauto. }

    dup GETMEMTGT. eapply CLOSED in GETMEMTGT0. des.

    hexploit (@Memory.add_exists mem_src0 loc from_src' to (Message.concrete val released)); eauto.
    { ii. inv LHS. inv RHS. ss.
      erewrite Memory.remove_o in GET2; eauto.
      erewrite Memory.remove_o in GET2; eauto. des_ifs. guardH o. guardH o0.
      destruct (Time.le_lt_dec x from_src).
      { hexploit memory_get_disjoint_strong.
        { eapply GET2. }
        { eapply GETMEMSRC. }
        i. des.
        { subst. ss. destruct o; ss. }
        { erewrite EMPTY in GET2; clarify. econs; ss.
          eapply (@TimeFacts.lt_le_lt _ x); eauto.
        }
        { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply FROM1. } etrans.
          { eapply TO. }
          { eauto. }
        }
      }
      { hexploit Memory.get_disjoint.
        { eapply GET2. }
        { eapply GETMEMSRC. }
        i. des; subst; ss.
        { destruct o; ss. }
        { eapply H; econs; eauto. }
      }
    }
    { eapply (@TimeFacts.le_lt_lt _ from_src); eauto.
      apply memory_get_ts_strong in GETMEMSRC. des; auto.
      subst. erewrite BOTNONESRC in GETPROMSRC. clarify. }
    intros [mem_src1 ADDMEM0].
    hexploit (@Memory.add_exists_le prom_src0 mem_src0 loc from_src' to (Message.concrete val released)); eauto.
    { eapply promise_memory_le; cycle 1; eauto.
      eapply promise_memory_le; cycle 1; eauto. }
    intros [prom_src1 ADDPROM0].
    assert (PROMISE2: Memory.promise prom_src0 mem_src0 loc from_src' to (Message.concrete val released) prom_src1 mem_src1 Memory.op_kind_add).
    { econs; eauto. i.
      erewrite Memory.remove_o in GET1; eauto.
      erewrite Memory.remove_o in GET1; eauto. des_ifs. guardH o. guardH o0.
      hexploit memory_get_from_inj.
      { eapply GET1. }
      { eapply MLESRC. eapply GET. }
      i. des; subst.
      { destruct o0; ss. }
      { erewrite BOTNONETGT in GETPROMTGT. clarify. }
      { erewrite BOTNONETGT in GETPROMTGT. clarify. }
    }

    hexploit (@Memory.remove_exists prom_src1 loc from_src' to (Message.concrete val released)); eauto.
    { eapply Memory.add_get0; eauto. }
    intros [prom_src2 REMOVEPROM2].
    hexploit (@MemoryFacts.add_remove_eq prom_src0 prom_src1 prom_src2); eauto.
    i. subst.

    assert (NOTHEREXTRA: forall from', ~ extra_others loc to0 from').
    { intros from' OTHER. eapply EXCLUSIVEEXTRA in OTHER. des. inv OTHER. clarify. }

    assert (WRITE: Memory.write prom_src0 mem_src0 loc from_src' to val released prom_src0 mem_src1 Memory.op_kind_add); eauto.

    destruct (classic (exists to', <<EXTRA: extra_self loc to0 to'>>)) as [?|MINE].
    { des. set (PROM1 := (sim_promise_contents PROMISE) loc to0).
      inv PROM1; try by (exfalso; eapply NEXTRA1; eauto); ss.
      rewrite GET in *. clarify.
      assert (to' = to).
      { hexploit (sim_memory_wf MEM).
        { right. eapply EXTRA0. }
        i. des. eapply UNIQUE. right. auto. } subst.
      set (MEM1 := (sim_memory_contents MEM) loc to0).
      inv MEM1; try by (exfalso; eapply NEXTRA1; right; eauto); ss.
      dup GET. apply MLESRC in GET. rewrite GET in *. clarify.

      exists prom_src0, mem_src0, mem_src1, prom_src0, mem_src1,
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then False else self loc' ts'),
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to0)
                       then (fun _ => False) else extra_self loc' ts').
      splits; eauto.
      { econs; eauto. econs; eauto. econs; eauto. }
      { econs. }
      { econs.
        { i. erewrite (@Memory.add_o mem_src1); eauto.
          erewrite (@Memory.remove_o mem_src0); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; clarify. }
          { ss. des; clarify. rewrite GETMEMTGT. econs 2; eauto.
            { intros []; ss. }
            { i. ss. }
          }
          { ss. des; clarify. rewrite <- H2. econs; eauto.
            intros ? []; ss. eapply NOTHEREXTRA; eauto. }
          { eapply (sim_memory_contents MEM). }
        }
        { i. des_ifs.
          { ss. des; clarify.
            destruct EXTRA2; ss. exfalso. eapply NOTHEREXTRA; eauto. }
          { ss. des; clarify. exfalso. eapply o.
            eapply sim_memory_extra_inj; eauto.
            { eapply EXTRA2. }
            { right. eauto. }
          }
          { ss. des; clarify.
            destruct EXTRA2; ss. exfalso. eapply NOTHEREXTRA; eauto. }
          { eapply (sim_memory_wf MEM). auto. }
        }
      }
      { econs.
        { i. erewrite (@Memory.remove_o prom_src0 prom_src'); eauto.
          erewrite (@Memory.remove_o prom_src'); eauto.
          erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
          { ss. des; clarify. }
          { ss. des; clarify. econs; eauto. }
          { ss. des; clarify. rewrite <- H. econs; eauto. }
          { apply (sim_promise_contents PROMISE). }
        }
        { i. des_ifs.
          { ss. des; clarify. exfalso. eapply o.
            eapply sim_memory_extra_inj; eauto.
            { right. eapply EXTRA2. }
            { right. eauto. }
          }
          { eapply (sim_promise_wf PROMISE); eauto. }
        }
        { i. des_ifs. guardH o. dup SELF0.
          eapply (sim_promise_extra PROMISE) in SELF1. des.
          exists to1. splits; auto.
          erewrite (@Memory.remove_o prom_src0 prom_src'); eauto.
          erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
          { ss. des; clarify. exfalso.
            set (PROM1:=(sim_promise_contents PROMISE) loc from_src).
            inv PROM1; ss.
            symmetry in H3. eapply Memory.remove_get1 in H3; eauto.
            des; subst.
            { timetac. }
            { eapply CONSISTENT in GET3. eapply Time.lt_strorder.
              transitivity from_src; eauto. }
          }
          { ss. des; clarify. destruct o; ss. }
        }
      }
    }

    { dup GET. eapply MLESRC in GET1.
      assert (NOEXTRA: forall ts', ~ (extra_others \\3// extra_self) loc ts' to).
      { ii. set (MEM1:=(sim_memory_contents MEM) loc ts').
        inv MEM1; ss; try by (exfalso; eapply NEXTRA1; eauto).
        hexploit ((sim_memory_wf MEM) loc from ts'); eauto. i. des.
        eapply UNIQUE in H. subst.
        hexploit memory_get_from_inj.
        { symmetry. eapply H1. }
        { eapply GET1. }
        i. des.
        { subst. destruct EXTRA.
          { eapply EXCLUSIVEEXTRA in H. inv H. clarify. }
          { eapply MINE; eauto. }
        }
        { subst. rewrite BOTNONESRC in GETPROMSRC. clarify. }
        { subst. rewrite BOTNONESRC in GETPROMSRC. clarify. }
      }

      hexploit (@Memory.add_exists mem_src1 loc to to0 Message.reserve); eauto.
      { i. erewrite Memory.add_o in GET2; eauto.
        erewrite Memory.remove_o in GET2; eauto.
        erewrite Memory.remove_o in GET2; eauto. des_ifs.
        { ss. des; clarify. symmetry.
          eapply Interval.disjoint_imm. }
        { guardH o. guardH o0. hexploit Memory.get_disjoint.
          { eapply MLESRC. eapply GET. }
          { eapply GET2. }
          i. des; auto. subst. destruct o0; ss. }
      }
      { econs. }
      intros [mem_src2 ADDMEM1].
      hexploit (@Memory.add_exists_le prom_src0 mem_src1 loc to to0 Message.reserve); eauto.
      { eapply write_memory_le; cycle 1; eauto.
        eapply promise_memory_le; cycle 1; eauto.
        eapply promise_memory_le; cycle 1; eauto. }
      intros [prom_src2 ADDPROM1].

      assert (PROMISE3: Memory.promise prom_src0 mem_src1 loc to to0 Message.reserve prom_src2 mem_src2 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      exists prom_src0, mem_src0, mem_src1, prom_src2, mem_src2,
      (fun loc' ts' => if loc_ts_eq_dec (loc', ts') (loc, to)
                       then False else self loc' ts'), extra_self.
      splits; eauto.
      { econs; eauto. econs; eauto. econs; eauto. }
      { econs; eauto. econs; eauto. }
      { econs.
        { i. erewrite (@Memory.add_o mem_src2); eauto.
          erewrite (@Memory.add_o mem_src1); eauto.
          erewrite (@Memory.remove_o mem_src0); eauto.
          erewrite (@Memory.remove_o mem_src'); eauto. des_ifs.
          { ss. des; clarify. timetac. }
          { ss. des; clarify. rewrite GETMEMTGT. econs 2; eauto.
            { intros []; ss. }
            { i. ss. }
          }
          { ss. des; clarify. rewrite <- GET1.
            eapply (sim_memory_contents MEM). }
          { eapply (sim_memory_contents MEM). }
        }
        { i. des_ifs.
          { ss. des; clarify. exfalso. eapply NOEXTRA; eauto. }
          { eapply (sim_memory_wf MEM). auto. }
        }
      }
      { econs.
        { i. erewrite (@Memory.add_o prom_src2); eauto.
          erewrite (@Memory.remove_o prom_src0 prom_src'); eauto.
          erewrite (@Memory.remove_o prom_src'); eauto.
          erewrite (@Memory.remove_o prom_tgt'); eauto. des_ifs.
          { ss. des; clarify. timetac. }
          { ss. des; clarify. econs; eauto. }
          { ss. des; clarify. rewrite <- GET.
            apply (sim_promise_contents PROMISE). }
          { apply (sim_promise_contents PROMISE). }
        }
        { i. des_ifs.
          { ss. des; clarify. exfalso.
            eapply NOEXTRA. right. eauto. }
          { eapply (sim_promise_wf PROMISE); eauto. }
        }
        { i. des_ifs. guardH o. dup SELF0.
          eapply (sim_promise_extra PROMISE) in SELF1. des.
          exists to1. splits; auto.
          erewrite (@Memory.add_o prom_src2); eauto.
          erewrite (@Memory.remove_o prom_src0 prom_src'); eauto.
          erewrite (@Memory.remove_o prom_src'); eauto. des_ifs.
          { ss. des; clarify. }
          { ss. des; clarify. exfalso.
            set (PROM1:=(sim_promise_contents PROMISE) loc from_src).
            inv PROM1; ss.
            symmetry in H. eapply Memory.remove_get1 in H; eauto.
            des; subst.
            { timetac. }
            { eapply CONSISTENT in GET3. eapply Time.lt_strorder.
              transitivity from_src; eauto. }
          }
        }
      }
    }
  Qed.


  Lemma sim_fulfill_forget_write others (self: Loc.t -> Time.t -> Prop) extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt prom_tgt'
        loc from_tgt to val released
        (LOC: L loc)
        (SELF: self loc to)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (BOTNONETGT: Memory.bot_none prom_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (REMOVE: Memory.remove prom_tgt loc from_tgt to (Message.concrete val released) prom_tgt')
        (CLOSED: Memory.closed mem_tgt)

        (MEMWF: memory_times_wf times mem_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src prom_src loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src prom_src loc' ts' from' Message.reserve>>))

        (CONSISTENT: forall to' from' val' released'
                            (GETTGT: Memory.get loc to' prom_tgt' = Some (from', Message.concrete val' released')),
            Time.lt to to')
    :
      exists from_src prom_src0 mem_src0 mem_src1 prom_src2 mem_src2 self' extra_self',
        (<<FUTURE0: reserve_future_memory prom_src mem_src prom_src0 mem_src0>>) /\
        (<<WRITE: Memory.write prom_src0 mem_src0 loc from_src to val released prom_src0 mem_src1 Memory.op_kind_add>>) /\
        (<<FROM: Time.le from_tgt from_src>>) /\
        (<<FUTURE1: reserve_future_memory prom_src0 mem_src1 prom_src2 mem_src2>>) /\
        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src2 mem_tgt>>) /\
        (<<PROMISE: sim_promise
                      self' extra_self'
                      prom_src2 prom_tgt'>>).
  Proof.
    hexploit Memory.remove_get0; try apply REMOVE. i. des.
    rename GET into GETPROMTGT. dup GETPROMTGT.
    apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.

    set (PROM := (sim_promise_contents PROMISE) loc to).
    rewrite GETPROMTGT in PROM. inv PROM; ss.
    symmetry in H0. rename H0 into GETPROMSRC.
    dup GETPROMSRC. apply MLESRC in GETPROMSRC0. rename GETPROMSRC0 into GETMEMSRC.

    set (MEM0 := (sim_memory_contents MEM) loc to).
    rewrite GETMEMSRC in *. rewrite GETMEMTGT in *.
    inv MEM0; try by (exfalso; apply NPROM; right; auto).

    exists from_src. eapply sim_fulfill_forget; eauto.
    { i. clarify. refl. }
    { i. clarify. inv ITV. ss. timetac. }
  Qed.

  Lemma sim_fulfill_forget_update others (self: Loc.t -> Time.t -> Prop) extra_others extra_self
        prom_src prom_tgt mem_src mem_tgt prom_tgt'
        loc from_tgt to val released
        (LOC: L loc)
        (SELF: self loc to)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (MLETGT: Memory.le prom_tgt mem_tgt)
        (MLESRC: Memory.le prom_src mem_src)
        (FIN: Memory.finite prom_src)
        (BOTNONESRC: Memory.bot_none prom_src)
        (BOTNONETGT: Memory.bot_none prom_tgt)
        (PROMISE: sim_promise self extra_self prom_src prom_tgt)
        (REMOVE: Memory.remove prom_tgt loc from_tgt to (Message.concrete val released) prom_tgt')
        (CLOSED: Memory.closed mem_tgt)
        (NOREAD: ~ others loc from_tgt)

        (MEMWF: memory_times_wf times mem_tgt)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src prom_src loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src prom_src loc' ts' from' Message.reserve>>))

        (CONSISTENT: forall to' from' val' released'
                            (GETTGT: Memory.get loc to' prom_tgt' = Some (from', Message.concrete val' released')),
            Time.lt to to')
    :
      exists prom_src0 mem_src0 mem_src1 prom_src2 mem_src2 self' extra_self',
        (<<FUTURE0: reserve_future_memory prom_src mem_src prom_src0 mem_src0>>) /\
        (<<WRITE: Memory.write prom_src0 mem_src0 loc from_tgt to val released prom_src0 mem_src1 Memory.op_kind_add>>) /\
        (<<FROM: Time.le from_tgt from_tgt>>) /\
        (<<FUTURE1: reserve_future_memory prom_src0 mem_src1 prom_src2 mem_src2>>) /\
        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src2 mem_tgt>>) /\
        (<<PROMISE: sim_promise
                      self' extra_self'
                      prom_src2 prom_tgt'>>).
  Proof.
    hexploit Memory.remove_get0; try apply REMOVE. i. des.
    rename GET into GETPROMTGT. dup GETPROMTGT.
    apply MLETGT in GETPROMTGT0. rename GETPROMTGT0 into GETMEMTGT.

    set (PROM := (sim_promise_contents PROMISE) loc to).
    rewrite GETPROMTGT in PROM. inv PROM; ss.
    symmetry in H0. rename H0 into GETPROMSRC.
    dup GETPROMSRC. apply MLESRC in GETPROMSRC0. rename GETPROMSRC0 into GETMEMSRC.

    set (MEM0 := (sim_memory_contents MEM) loc to).
    rewrite GETMEMSRC in *. rewrite GETMEMTGT in *.
    inv MEM0; try by (exfalso; apply NPROM; right; auto).

    eapply sim_fulfill_forget; eauto.
    { refl. }
    { i. clarify. }
    { i. clarify.
      destruct (Memory.get loc ts mem_src) eqn:EQ; auto. destruct p.
      eapply sim_memory_get_larger in EQ; eauto. des.
      { inv ITV. ss. hexploit Memory.get_disjoint.
        { eapply GETTGT. }
        { eapply GETMEMTGT. }
        i. des; clarify.
        { apply memory_get_ts_strong in GET. des.
          { subst. erewrite BOTNONESRC in GETPROMSRC. clarify. }
          { timetac. }
        }
        { exfalso. eapply (H ts); econs; ss.
          { apply memory_get_ts_strong in GETTGT. des; auto.
            subst. exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply FROM0. }
            { eapply Time.bot_spec. }
          }
          { refl. }
          { etrans; eauto. eapply memory_get_ts_le; eauto. }
        }
      }
      { exfalso. set (MEM1:=(sim_memory_contents MEM) loc t). inv MEM1; ss.
        hexploit ((sim_memory_wf MEM) loc t ts); eauto. i. des. inv ITV; ss.
        hexploit memory_get_disjoint_strong.
        { symmetry. eapply H. }
        { eapply GETMEMTGT. }
        i. des; clarify.
        { rewrite GET in *. clarify.
          eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS. } etrans.
          { eapply TO. }
          { eapply memory_get_ts_le; eauto. }
        }
        { exploit LB1.
          { instantiate (1:=from_tgt).
            apply MEMWF in GETMEMTGT. des. auto. }
          { destruct TS0; auto. inv H1. exfalso. destruct PROM1; eauto.
            set (PROM1:=(sim_promise_contents PROMISE) loc from_tgt). inv PROM1; ss.
            symmetry in H4. eapply Memory.remove_get1 in H4; eauto. des.
            { subst. timetac. }
            { eapply CONSISTENT in GET2. eapply Time.lt_strorder.
              etrans; [eapply GET2|]; eauto. }
          }
          { i. eapply Time.lt_strorder. etrans.
            { eapply FROM1. } eauto.
          }
        }
        { eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS1. } etrans.
          { left. eapply TS. } etrans.
          { eapply TO. }
          { eapply memory_get_ts_le; eauto. }
        }
      }
    }
  Qed.


  Lemma sim_promise_step_forget others (self: Loc.t -> Time.t -> Prop) extra_others extra_self
        mem_src mem_tgt mem_tgt' lc_src lc_tgt lc_tgt' loc from to msg kind
        (LOC: L loc)
        (STEPTGT: Local.promise_step lc_tgt mem_tgt loc from to msg lc_tgt' mem_tgt' kind)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCAL: sim_local self extra_self lc_src lc_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LCSRC: Local.wf lc_src mem_src)
        (LCTGT: Local.wf lc_tgt mem_tgt)

        (CLOSED: Memory.closed mem_tgt)

        (MEMWF: memory_times_wf times mem_tgt')
        (SEMI: semi_closed_message msg mem_src loc to)
    :
      (exists self' extra_self' prom_src' mem_src',
        (<<FUTURE: reserve_future_memory (Local.promises lc_src) mem_src prom_src' mem_src'>>) /\
        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self' extra_self' (Local.mk (Local.tview lc_src) prom_src') lc_tgt'>>) /\
        (<<SELF: __guard__(self' loc to \/ msg = Message.reserve)>>)) \/
      (exists lc_src' mem_src',
        (<<STEPSRC: Local.promise_step lc_src mem_src loc from to msg lc_src' mem_src' kind>>) /\
        (<<MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src' mem_tgt'>>) /\
        (<<LOCAL: sim_local self extra_self lc_src' lc_tgt'>>) /\
        (<<SELF: ~ self loc to>>))
  .
  Proof.
    inv STEPTGT. inv LCSRC. inv LCTGT. inv LOCAL.
    hexploit sim_promise_forget; ss; eauto. i. des.
    - left. esplits; eauto.
    - right. esplits; eauto.
  Qed.

  Lemma sim_write_step_forget others self extra_others extra_self
        mem_src mem_tgt mem_tgt' lc_src lc_tgt lc_tgt' loc from to kind_tgt sc sc' val released ord
        (LOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val None released ord lc_tgt' sc' mem_tgt' kind_tgt)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCAL: sim_local self extra_self lc_src lc_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LCSRC: Local.wf lc_src mem_src)
        (LCTGT: Local.wf lc_tgt mem_tgt)

        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)

        (CLOSED: Memory.closed mem_tgt)

        (MEMWF: memory_times_wf times mem_tgt')
        (CONSISTENT: Local.promise_consistent lc_tgt')

        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from' Message.reserve>>))
    :
      exists self' extra_self' from' lc_src' prom_src0 mem_src0 mem_src1 prom_src' mem_src' kind_src,
        (<<FUTURE0: reserve_future_memory (Local.promises lc_src) mem_src prom_src0 mem_src0>>) /\
        (<<WRITE: Local.write_step (Local.mk (Local.tview lc_src) prom_src0) sc mem_src0 loc from' to val None released ord lc_src' sc' mem_src1 kind_src>>) /\
        (<<FROM: Time.le from from'>>) /\
        (<<FUTURE1: reserve_future_memory (Local.promises lc_src') mem_src1 prom_src' mem_src'>>) /\

        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self' extra_self' (Local.mk (Local.tview lc_src') prom_src') lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv LCSRC. inv LCTGT. inv LOCAL. inv WRITE. ss.
    hexploit Memory.promise_future; try apply PROMISE; eauto.
    { econs. inv PROMISE; try by (eapply TViewFacts.op_closed_released; eauto). } i. des.

    hexploit sim_promise_forget; ss; eauto.
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
    i. des.
    { destruct SELF as [SELF|]; ss.
      hexploit reserve_future_memory_future; try apply STEPSRC; eauto.
      i. des. inv LOCAL. ss.

      hexploit sim_fulfill_forget_write; try apply SELF; try apply PROMISE0; eauto.
      { i. eapply EXCLUSIVE in OTHER. des.
        eapply reserve_future_memory_unchangable in UNCH; eauto. }
      { i. eapply EXCLUSIVEEXTRA in OTHER. des.
        eapply reserve_future_memory_unchangable in OTHER; eauto. }
      { i. eapply CONSISTENT in GETTGT. ss.
        eapply TimeFacts.le_lt_lt; [|eapply GETTGT].
        unfold TimeMap.join, TimeMap.singleton. etrans; [|eapply Time.join_r].
        setoid_rewrite LocFun.add_spec_eq. refl. }

      i. des.
      eexists self'0, extra_self'0, from_src, (Local.mk _ prom_src0), prom_src0, mem_src0, mem_src1, prom_src2, mem_src2, Memory.op_kind_add.
      splits; eauto.
      { eapply reserve_future_memory_trans; eauto. }
      { econs; eauto; ss. ii. des_ifs.
        eapply reserve_future_concrete_same_promise2 in GET; eauto.
        eapply reserve_future_concrete_same_promise2 in GET; eauto.
        set (PROM:= (sim_promise_contents PROMS) loc t).
        rewrite GET in *. inv PROM; ss. exploit RELEASE; eauto.
      }
      { econs; eauto. }
    }
    { hexploit (@Memory.remove_exists
                  prom_src' loc from to
                  (Message.concrete val (TView.write_released tvw sc loc to None ord))).
      { set (PROM:= (sim_promise_contents PROMISE0) loc to).
        eapply Memory.remove_get0 in REMOVE. des.
        rewrite GET in *. inv PROM; ss. }
      intros [prom_src'' REMOVESRC]. esplits.
      - econs 1.
      - econs; ss.
        + econs; eauto.
        + ii. set (PROM:=(sim_promise_contents PROMS) loc t).
          rewrite GET in *. inv PROM; ss.
          exploit RELEASE; eauto.
      - refl.
      - econs 1.
      - eauto.
      - econs; auto. econs.
        { ii. set (PROM:=(sim_promise_contents PROMISE0) loc0 ts).
          erewrite (@Memory.remove_o prom_src''); eauto.
          erewrite (@Memory.remove_o promises2); eauto. des_ifs.
          ss. des; subst. econs 2; eauto.
          ii. inv PROM; clarify; try by (eapply NEXTRA; eauto).
          eapply Memory.remove_get0 in REMOVESRC. des. rewrite GET in *. clarify.
        }
        { apply PROMISE0. }
        { i. set (PROM:=(sim_promise_extra PROMISE0) loc0 ts SELF0). des.
          esplits; eauto. erewrite (@Memory.remove_o prom_src''); eauto.
          des_ifs. ss. des; clarify. exfalso.
          eapply Memory.remove_get0 in REMOVESRC. des. clarify. }
    }
  Qed.

  Lemma sim_update_step_forget others self extra_others extra_self
        mem_src mem_tgt mem_tgt' lc_src lc_tgt lc_tgt' loc from to kind_tgt sc sc' val releasedm released ord
        (LOC: L loc)
        (STEPTGT: Local.write_step lc_tgt sc mem_tgt loc from to val releasedm released ord lc_tgt' sc' mem_tgt' kind_tgt)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (LOCAL: sim_local self extra_self lc_src lc_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LCSRC: Local.wf lc_src mem_src)
        (LCTGT: Local.wf lc_tgt mem_tgt)

        (NOREAD: ~ (others \\2// self) loc from)

        (RELEASEDMCLOSED: Memory.closed_opt_view releasedm mem_tgt)
        (RELEASEDMCLOSEDSRC: Memory.closed_opt_view releasedm mem_src)
        (RELEASEDMWF: View.opt_wf releasedm)

        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)

        (CLOSED: Memory.closed mem_tgt)

        (MEMWF: memory_times_wf times mem_tgt')
        (CONSISTENT: Local.promise_consistent lc_tgt')

        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from' Message.reserve>>))
    :
      exists self' extra_self' lc_src' prom_src0 mem_src0 mem_src1 prom_src' mem_src' kind_src,
        (<<FUTURE0: reserve_future_memory (Local.promises lc_src) mem_src prom_src0 mem_src0>>) /\
        (<<WRITE: Local.write_step (Local.mk (Local.tview lc_src) prom_src0) sc mem_src0 loc from to val releasedm released ord lc_src' sc' mem_src1 kind_src>>) /\
        (<<FUTURE1: reserve_future_memory (Local.promises lc_src') mem_src1 prom_src' mem_src'>>) /\

        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self' extra_self' (Local.mk (Local.tview lc_src') prom_src') lc_tgt'>>)
  .
  Proof.
    inv STEPTGT. inv LCSRC. inv LCTGT. inv LOCAL. inv WRITE. ss.
    hexploit Memory.promise_future; try apply PROMISE; eauto.
    { econs. inv PROMISE; try by (eapply TViewFacts.op_closed_released; eauto). } i. des.

    hexploit sim_promise_forget; ss; eauto.
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
    i. des.
    { destruct SELF as [SELF|]; ss.
      hexploit reserve_future_memory_future; try apply STEPSRC; eauto.
      i. des. inv LOCAL. ss.

      hexploit sim_fulfill_forget_update; try apply SELF; try apply PROMISE0; eauto.
      { ii. eapply NOREAD. left. eauto. }
      { i. eapply EXCLUSIVE in OTHER. des.
        eapply reserve_future_memory_unchangable in UNCH; eauto. }
      { i. eapply EXCLUSIVEEXTRA in OTHER. des.
        eapply reserve_future_memory_unchangable in OTHER; eauto. }
      { i. eapply CONSISTENT in GETTGT. ss.
        eapply TimeFacts.le_lt_lt; [|eapply GETTGT].
        unfold TimeMap.join, TimeMap.singleton. etrans; [|eapply Time.join_r].
        setoid_rewrite LocFun.add_spec_eq. refl. }

      i. des.
      eexists self'0, extra_self'0, (Local.mk _ prom_src0), prom_src0, mem_src0, mem_src1, prom_src2, mem_src2, Memory.op_kind_add.
      splits; eauto.
      { eapply reserve_future_memory_trans; eauto. }
      { econs; eauto; ss. ii. des_ifs.
        eapply reserve_future_concrete_same_promise2 in GET; eauto.
        eapply reserve_future_concrete_same_promise2 in GET; eauto.
        set (PROM:= (sim_promise_contents PROMS) loc t).
        rewrite GET in *. inv PROM; ss. exploit RELEASE; eauto.
      }
      { econs; eauto. }
    }
    { hexploit (@Memory.remove_exists
                  prom_src' loc from to
                  (Message.concrete val (TView.write_released tvw sc loc to releasedm ord))).
      { set (PROM:= (sim_promise_contents PROMISE0) loc to).
        eapply Memory.remove_get0 in REMOVE. des.
        rewrite GET in *. inv PROM; ss. }
      intros [prom_src'' REMOVESRC]. esplits.
      - econs 1.
      - econs; ss.
        + econs; eauto.
        + ii. set (PROM:=(sim_promise_contents PROMS) loc t).
          rewrite GET in *. inv PROM; ss.
          exploit RELEASE; eauto.
      - econs 1.
      - eauto.
      - econs; auto. econs.
        { ii. set (PROM:=(sim_promise_contents PROMISE0) loc0 ts).
          erewrite (@Memory.remove_o prom_src''); eauto.
          erewrite (@Memory.remove_o promises2); eauto. des_ifs.
          ss. des; subst. econs 2; eauto.
          ii. inv PROM; clarify; try by (eapply NEXTRA; eauto).
          eapply Memory.remove_get0 in REMOVESRC. des. rewrite GET in *. clarify.
        }
        { apply PROMISE0. }
        { i. set (PROM:=(sim_promise_extra PROMISE0) loc0 ts SELF0). des.
          esplits; eauto. erewrite (@Memory.remove_o prom_src''); eauto.
          des_ifs. ss. des; clarify. exfalso.
          eapply Memory.remove_get0 in REMOVESRC. des. clarify. }
    }
  Qed.

  Lemma reserving_trace_silent tr
        (RESERVING: reserving_trace tr)
    :
      List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr.
  Proof.
    induction RESERVING; eauto. econs; eauto.
    unfold ThreadEvent.is_reservation_event in *. des_ifs.
  Qed.

  Lemma sim_thread_step_silent' others self extra_others extra_self
        lang st lc_src lc_tgt sc mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc' mem_tgt' views views'
        (STEPTGT: @JThread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc mem_tgt) (Thread.mk _ st' lc_tgt' sc' mem_tgt') views views')
        (NOREAD: no_read_msgs others e_tgt)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self extra_self lc_src lc_tgt)

        (MEMWF: memory_times_wf times mem_tgt')
        (CONSISTENT: Local.promise_consistent lc_tgt')
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from' Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views loc ts))

        (EVENT: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)
    :
      exists tr self' extra_self' lc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc mem_src) (Thread.mk _ st' lc_src' sc' mem_src')>>) /\
        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local self' extra_self' lc_src' lc_tgt'>>) /\
        (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr>>)
  .
  Proof.
    inv STEPTGT. inv STEP; ss.
    - dup STEP0. inv STEP0.
      assert (SEMICLOSED: semi_closed_message msg mem_src loc to).
      { destruct msg; econs. hexploit PROMISE; eauto.
        i. inv H; econs.
        destruct (classic (views' loc to = views loc to)).
        - rewrite H in *.
          inv MEMSRC. eapply joined_view_semi_closed in JOINED0; eauto.
        - exploit VIEWSLE; eauto. i. des. ss.
          inv MEMSRC. eapply joined_view_semi_closed; cycle 1; eauto.
          rewrite VIEW. econs.
          + eapply semi_closed_view_join.
            * eapply closed_view_semi_closed.
              inv LOCALSRC. inv LOCAL. inv SIM. eapply TVIEW_CLOSED.
            * eapply semi_closed_view_singleton; eauto.
          + eapply List.Forall_forall.
            i. eapply all_join_views_in_iff in H0. des. subst.
            eapply List.Forall_forall in IN; eauto. ss.
            erewrite View.join_comm. eapply join_singleton_semi_closed_view; eauto.
            eapply memory_get_ts_le in GET. auto.
      }

      destruct (classic (L loc)).
      + hexploit sim_promise_step_forget; eauto. i. des.
        { destruct lc_src. ss. exploit reserve_future_memory_steps; eauto. i. des.
          eexists _, self', extra_self', (Local.mk _ _), mem_src'. splits; eauto.
          eapply reserving_trace_silent; eauto. }
        { esplits; [|eauto|eauto|].
          - econs; eauto. econs 1. econs; eauto.
          - econs; eauto.
        }
      + hexploit sim_promise_step_normal; eauto.
        i. des.
        eexists [(_, ThreadEvent.promise loc from to msg kind)],
        self, extra_self, lc_src', mem_src'.
        splits; ss.
        * econs 2; [|econs 1|ss]. econs 1. econs; eauto.
        * econs; ss.
    - inv STEP0. inv LOCAL.
      + eexists [(_, ThreadEvent.silent)], self, extra_self, lc_src, mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * econs; ss.
      + exploit sim_read_step; eauto. i. des.
        eexists [(_, ThreadEvent.read loc ts val released ord)],
        self, extra_self, lc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * econs; ss.
      + destruct (classic (L loc)).
        * exploit sim_write_step_forget; eauto. i. des.
          destruct lc_src, lc_src'. ss.
          eapply reserve_future_memory_steps in FUTURE0. des.
          eapply reserve_future_memory_steps in FUTURE1. des.
          esplits; [|eauto|eauto|].
          { eapply Trace.steps_app.
            { eapply STEPS. }
            eapply Trace.steps_app.
            { econs 2; [|econs 1|ss]. econs 2. econs; cycle 1.
              - econs 3. eauto.
              - ss. eauto. }
            eauto.
          }
          { eapply Forall_app.
            - eapply reserving_trace_silent; eauto.
            - eapply Forall_app.
              + econs; eauto.
              + eapply reserving_trace_silent; eauto.
          }
        * hexploit sim_write_step_normal; eauto. i. des.
          eexists [(_, ThreadEvent.write loc from to val _ ord)],
          self, extra_self, lc_src', mem_src'.
          splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
          { econs; ss. }
      + exploit sim_read_step; eauto.
        { eapply PromiseConsistent.write_step_promise_consistent; eauto. } i. des.
        exploit Local.read_step_future; try apply LOCAL1; eauto. i. des.
        exploit Local.read_step_future; try apply STEPSRC; eauto. i. des.
        dup STEPSRC. inv STEPSRC. ss.
        destruct (classic (L loc)).
        * hexploit sim_update_step_forget; eauto. i. des. ss.
          destruct lc_src, lc_src'.
          eapply reserve_future_read_commute in STEPSRC0; eauto.
          eapply reserve_future_memory_steps in FUTURE0. des.
          eapply reserve_future_memory_steps in FUTURE1. des.
          esplits; [|eauto|eauto|].
          { eapply Trace.steps_app.
            { eapply STEPS. }
            eapply Trace.steps_app.
            { econs 2; [|econs 1|ss]. econs 2. econs; cycle 1.
              - econs 4; eauto.
              - ss. eauto. }
            eauto.
          }
          { eapply Forall_app.
            - eapply reserving_trace_silent; eauto.
            - eapply Forall_app.
              + econs; eauto.
              + eapply reserving_trace_silent; eauto.
          }
        * hexploit sim_write_step_normal; eauto. i. des.
          eexists [(_, ThreadEvent.update loc tsr tsw valr valw releasedr releasedw ordr ordw)],
          self, extra_self, lc_src', mem_src'. splits; ss.
          { econs 2; [|econs 1|ss]. econs 2. econs; eauto. }
          { econs; ss. }
      + exploit sim_fence_step; eauto. i. des.
        eexists [(_, ThreadEvent.fence ordr ordw)],
        self, extra_self, lc_src', mem_src. splits; ss.
        * econs 2; [|econs 1|ss]. econs 2. econs; eauto.
        * econs; ss.
      + ss.
      + ss.
  Qed.

  Inductive sim_local_strong
            (self: Loc.t -> Time.t -> Prop)
            (extra extra_all: Loc.t -> Time.t -> Time.t -> Prop)
    :
      forall (lc_src lc_tgt: Local.t), Prop :=
  | sim_local_strong_intro
      tvw prom_src prom_tgt
      (PROMS: sim_promise_strong self extra extra_all prom_src prom_tgt)
    :
      sim_local_strong self extra extra_all (Local.mk tvw prom_src) (Local.mk tvw prom_tgt)
  .
  Hint Constructors sim_local_strong.

  Lemma sim_local_strong_sim_local
        self extra extra_all lc_src lc_tgt
        (SIM: sim_local_strong self extra extra_all lc_src lc_tgt)
    :
      sim_local self extra lc_src lc_tgt.
  Proof.
    inv SIM. econs; eauto. eapply sim_promise_strong_sim_promise; eauto.
  Qed.

  Lemma sim_thread_step_silent others self extra_others extra_self
        lang st lc_src lc_tgt sc mem_src mem_tgt pf e_tgt
        st' lc_tgt' sc' mem_tgt' views views'
        (STEPTGT: @JThread.step lang pf e_tgt (Thread.mk _ st lc_tgt sc mem_tgt) (Thread.mk _ st' lc_tgt' sc' mem_tgt') views views')
        (NOREAD: no_read_msgs others e_tgt)
        (MEM: sim_memory L times (others \\2// self) (extra_others \\3// extra_self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local self extra_self lc_src lc_tgt)

        (MEMWF: memory_times_wf times mem_tgt')
        (CONSISTENT: Local.promise_consistent lc_tgt')
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from msg>>)
        (EXCLUSIVEEXTRA: forall loc' ts' from' (OTHER: extra_others loc' ts' from'),
            (<<UNCH: unchangable mem_src (Local.promises lc_src) loc' ts' from' Message.reserve>>))
        (JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src loc ts) (views loc ts))

        (EVENT: ThreadEvent.get_machine_event e_tgt = MachineEvent.silent)
    :
      exists tr self' extra_self' lc_src' mem_src',
        (<<STEPSRC: Trace.steps tr (Thread.mk _ st lc_src sc mem_src) (Thread.mk _ st' lc_src' sc' mem_src')>>) /\
        (<<MEM: sim_memory L times (others \\2// self') (extra_others \\3// extra_self') mem_src' mem_tgt'>>) /\
        (<<SIM: sim_local_strong self' extra_self' (extra_others \\3// extra_self') lc_src' lc_tgt'>>) /\
        (<<JOINED: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src' loc ts) (views' loc ts)>>) /\
        (<<SILENT: List.Forall (fun lce => ThreadEvent.get_machine_event (snd lce) = MachineEvent.silent) tr>>)
  .
  Proof.
    hexploit sim_thread_step_silent'; eauto. i. des.
    exploit Thread.step_future.
    { inv STEPTGT. eauto. } all: ss. i. des.
    exploit Trace.steps_future; eauto. i. des. ss.
    exploit sim_promise_weak_strengthen; eauto.
    { eapply WF2. }
    { eapply WF0. }
    { eapply WF0. }
    { eapply WF0. }
    { inv SIM0. ss. }
    i. des. destruct lc_src'. ss.
    exploit reserve_future_memory_steps; eauto. i. des.
    exists (tr++tr0). esplits; eauto.
    { eapply Trace.steps_trans; eauto. }
    { inv SIM0. econs; eauto. }
    assert (JOINED0: forall loc ts, List.Forall (fun vw => semi_closed_view vw mem_src' loc ts) (views' loc ts)).
    { inv STEPTGT. ss.
      i. destruct (classic (views' loc ts = views loc ts)).
      { rewrite H.
        eapply List.Forall_impl; eauto.
        i. ss. eapply semi_closed_view_future; eauto. eapply Memory.future_future_weak; eauto. }
      { hexploit VIEWSLE; eauto. i. des.
        set (MEM2:=(sim_memory_contents MEM0) loc ts). rewrite GET in MEM2. inv MEM2; ss.
        { rewrite VIEW. econs.
          - eapply closed_view_semi_closed. eapply Memory.join_closed_view.
            + inv WF0. inv SIM0. ss. eapply TVIEW_CLOSED.
            + inv CLOSED0. eapply Memory.singleton_ur_closed_view; eauto.
          - apply List.Forall_forall.
            i. eapply all_join_views_in_iff in H0. des. subst.
            eapply List.Forall_forall in IN; eauto. ss.
            eapply semi_closed_view_future in IN.
            2: { eapply Memory.future_future_weak; eauto. }
            erewrite View.join_comm. eapply join_singleton_semi_closed_view; eauto.
            eapply memory_get_ts_le in GET. ss.
        }
        { rewrite VIEW. econs.
          - erewrite View.join_comm. eapply join_singleton_semi_closed_view.
            + instantiate (1:=Time.bot). eapply closed_view_semi_closed.
              inv WF0. inv SIM0. ss. eapply TVIEW_CLOSED.
            + eapply Time.bot_spec.
          - apply List.Forall_forall.
            i. eapply all_join_views_in_iff in H0. des. subst.
            eapply List.Forall_forall in IN; eauto. ss.
            eapply semi_closed_view_future in IN.
            2: { eapply Memory.future_future_weak; eauto. }
            erewrite View.join_comm. eapply join_singleton_semi_closed_view; eauto.
            eapply memory_get_ts_le in GET. ss.
        }
      }
    }
    { i. eapply List.Forall_impl; eauto.
      i. ss. eapply semi_closed_view_future in H; eauto.
      eapply Memory.future_future_weak; eauto.
      eapply reserve_future_future; eauto. }
    { eapply Forall_app; eauto.
      eapply reserving_trace_silent; eauto. }
  Qed.

  Lemma sim_fence_step_strong self extra extra_all lc_src lc_tgt sc ordr ordw
        sc' lc_tgt'
        (STEPTGT: Local.fence_step lc_tgt sc ordr ordw lc_tgt' sc')
        (LOCAL: sim_local_strong self extra extra_all lc_src lc_tgt)
    :
      exists lc_src',
        (<<STEPSRC: Local.fence_step lc_src sc ordr ordw lc_src' sc'>>) /\
        (<<SIM: sim_local_strong self extra extra_all lc_src' lc_tgt'>>)
  .
  Proof.
    inv LOCAL. inv STEPTGT. esplits.
    - econs; ss; eauto.
      + ii. set (PROM:= (sim_promise_strong_contents PROMS) loc t).
        rewrite GET in *. inv PROM; ss.
        exploit RELEASE; eauto.
      + i. eapply sim_promise_strong_sim_promise in PROMS.
        eapply sim_promise_bot in PROMS; eauto.
    - econs; ss; eauto.
  Qed.

End SIM.
