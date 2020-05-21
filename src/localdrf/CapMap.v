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
Require Import Mapping.

Require Import LocalDRFDef.
Require Import LocalDRF_PF.

Set Implicit Arguments.

Section CONCRETEIDENT.

  Definition map_ident_concrete (f: Loc.t -> Time.t -> Time.t -> Prop)
             (mem: Memory.t): Prop :=
    forall loc to
           (CONCRETE: concrete_promised mem loc to),
      f loc to to.

  Definition map_ident_concrete_bot
             f mem
             (MAP: map_ident_concrete f mem)
             (CLOSED: Memory.closed mem)
    :
      mapping_map_bot f.
  Proof.
    ii. eapply MAP. inv CLOSED. econs; eauto.
  Qed.

  Lemma map_ident_concrete_closed_timemap
        f mem tm
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_timemap tm mem)
    :
      timemap_map f tm tm.
  Proof.
    ii. eapply MAP; eauto.
    exploit CLOSED; eauto. i. des. econs; eauto.
  Qed.

  Lemma map_ident_concrete_closed_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_view vw mem)
    :
      view_map f vw vw.
  Proof.
    inv CLOSED. econs.
    - eapply map_ident_concrete_closed_timemap; eauto.
    - eapply map_ident_concrete_closed_timemap; eauto.
  Qed.

  Lemma map_ident_concrete_closed_tview
        f mem tvw
        (MAP: map_ident_concrete f mem)
        (CLOSED: TView.closed tvw mem)
    :
      tview_map f tvw tvw.
  Proof.
    inv CLOSED. econs.
    - i. eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
    - eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_opt_view
        f mem vw
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_opt_view vw mem)
    :
      opt_view_map f vw vw.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_view; eauto.
  Qed.

  Lemma map_ident_concrete_closed_message
        f mem msg
        (MAP: map_ident_concrete f mem)
        (CLOSED: Memory.closed_message msg mem)
    :
      msg_map f msg msg.
  Proof.
    inv CLOSED; econs.
    eapply map_ident_concrete_closed_opt_view; eauto.
  Qed.

  Inductive compose_map (f0 f1: Loc.t -> Time.t -> Time.t -> Prop)
    : Loc.t -> Time.t -> Time.t -> Prop :=
  | compose_map_intro
      loc ts0 ts1 ts2
      (MAP0: f0 loc ts0 ts1)
      (MAP1: f1 loc ts1 ts2)
    :
      compose_map f0 f1 loc ts0 ts2
  .
  Hint Constructors compose_map.

  Lemma compose_map_eq f0 f1
        (MAPEQ0: mapping_map_eq f0)
        (MAPEQ1: mapping_map_eq f1)
    :
      mapping_map_eq (compose_map f0 f1).
  Proof.
    unfold mapping_map_eq in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPEQ0 _ _ _ _ MAP2 MAP0); eauto. i. clarify.
    eauto.
  Qed.

  Lemma compose_map_le f0 f1
        (MAPLE0: mapping_map_le f0)
        (MAPLE1: mapping_map_le f1)
    :
      mapping_map_le (compose_map f0 f1).
  Proof.
    unfold mapping_map_le in *. i. inv MAP0. inv MAP1.
    hexploit (@MAPLE0 _ _ _ _ _ MAP2 MAP0); eauto.
  Qed.

  Lemma compose_map_bot f0 f1
        (MAPBOT0: mapping_map_bot f0)
        (MAPBOT1: mapping_map_bot f1)
    :
      mapping_map_bot (compose_map f0 f1).
  Proof.
    ii. econs; eauto.
  Qed.

  Lemma compose_map_lt f0 f1
        (MAPLT0: mapping_map_lt f0)
        (MAPLT1: mapping_map_lt f1)
    :
      mapping_map_lt (compose_map f0 f1).
  Proof.
    unfold mapping_map_lt in *. i. inv MAP0. inv MAP1.
    transitivity (Time.lt ts1 ts2); eauto.
  Qed.

  Lemma compose_map_timemap f0 f1 tm0 tm1 tm2
        (MAP0: timemap_map f0 tm0 tm1)
        (MAP1: timemap_map f1 tm1 tm2)
    :
      timemap_map (compose_map f0 f1) tm0 tm2.
  Proof.
    ii. eauto.
  Qed.

  Lemma compose_map_view f0 f1 vw0 vw1 vw2
        (MAP0: view_map f0 vw0 vw1)
        (MAP1: view_map f1 vw1 vw2)
    :
      view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - eapply compose_map_timemap; eauto.
    - eapply compose_map_timemap; eauto.
  Qed.

  Lemma compose_map_opt_view f0 f1 vw0 vw1 vw2
        (MAP0: opt_view_map f0 vw0 vw1)
        (MAP1: opt_view_map f1 vw1 vw2)
    :
      opt_view_map (compose_map f0 f1) vw0 vw2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_tview f0 f1 tvw0 tvw1 tvw2
        (MAP0: tview_map f0 tvw0 tvw1)
        (MAP1: tview_map f1 tvw1 tvw2)
    :
      tview_map (compose_map f0 f1) tvw0 tvw2.
  Proof.
    inv MAP0. inv MAP1. econs.
    - i. eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
    - eapply compose_map_view; eauto.
  Qed.

  Lemma compose_map_msg f0 f1 msg0 msg1 msg2
        (MAP0: msg_map f0 msg0 msg1)
        (MAP1: msg_map f1 msg1 msg2)
    :
      msg_map (compose_map f0 f1) msg0 msg2.
  Proof.
    inv MAP0; inv MAP1; econs.
    eapply compose_map_opt_view; eauto.
  Qed.

  Lemma compose_map_mappable f0 f1 mem0 mem1
        (MAP: memory_map f0 mem0 mem1)
        (MAPPABLE: mappable_memory f1 mem1)
    :
      mappable_memory (compose_map f0 f1) mem0.
  Proof.
    ii. inv MAP. exploit MAPPED; eauto. i. des; clarify.
    inv MSG. inv MSGLE. exploit MAPPABLE; eauto. i. inv x.
    eexists. eauto.
  Qed.

  Lemma compose_map_memory2 f0 f1 m0 m1 m2
        (MAPEQ0: mapping_map_eq f0)
        (MAPLE: mapping_map_le f1)
        (MEM0: memory_map2 f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: memory_map2 f1 m1 m2)
    :
      memory_map2 (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto.
      + subst. inv MSGLE. inv MSG. auto.
      + right. inv CLOSED0. exploit CLOSED; eauto. i. des.
        exploit closed_message_map; try apply MSG; eauto.
        { eapply memory_map2_memory_map; eauto. } intros MSG_CLOSED1.
        exploit msg_map_exists; try apply MSG_CLSOED1; eauto.
        { eapply memory_map2_memory_map; eauto. } i. des.
        esplits; [..|eauto].
        * eauto.
        * eapply compose_map_msg; eauto.
        * etrans; eauto. eapply msg_le_map; eauto.
    - i. exploit ONLY0; eauto. i. des.
      exploit ONLY; eauto. i. des. esplits; eauto.
  Qed.

  Lemma compose_map_promise f0 f1 m0 m1 m2
        (MAPLT0: mapping_map_lt f0)
        (MAPLT1: mapping_map_lt f1)
        (MEM0: promises_map f0 m0 m1)
        (CLOSED0: Memory.closed m0)
        (MEM1: promises_map f1 m1 m2)
    :
      promises_map (compose_map f0 f1) m0 m2.
  Proof.
    dup MEM0. dup MEM1.
    inv MEM0. inv MEM1. econs.
    - ii. exploit MAPPED; eauto. i. des; auto.
      exploit MAPPED0; eauto. i. des; auto. esplits; eauto.
      + eapply mapping_map_lt_non_collapsable.
        eapply compose_map_lt; eauto.
      + eapply compose_map_msg; eauto.
    - ii. exploit ONLY0; eauto. i. des.
      exploit ONLY; eauto. i. des. esplits; eauto.
  Qed.

End CONCRETEIDENT.


Section MIDDLE.

  Variable L: Loc.t -> bool.

  Lemma middle_state_exists
        others self lc_src lc_tgt sc mem_src mem_tgt
        (views: Loc.t -> Time.t -> list View.t)
        times
        (MEM: sim_memory L (others \2/ self) mem_src mem_tgt)
        (SCSRC: Memory.closed_timemap sc mem_src)
        (SCTGT: Memory.closed_timemap sc mem_tgt)
        (MEMSRC: Memory.closed mem_src)
        (MEMTGT: Memory.closed mem_tgt)
        (LOCALSRC: Local.wf lc_src mem_src)
        (LOCALTGT: Local.wf lc_tgt mem_tgt)
        (SIM: sim_local L self lc_src lc_tgt)
        (PROMATTACH: promises_not_attached self (promised lc_src.(Local.promises)) mem_src)
        (EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, <<UNCH: unchangable mem_src lc_src.(Local.promises) loc' ts' from msg>>)
        (JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw mem_src) (views loc ts))

        cap_src cap_tgt max_src max_tgt
        (CAPSRC: Memory.cap mem_src cap_src)
        (CAPTGT: Memory.cap mem_src cap_src)
        (MAXSRC: Memory.max_concrete_timemap cap_src max_src)
        (MAXTGT: Memory.max_concrete_timemap cap_tgt max_tgt)
    :
      exists f prom_src' cap_src' max_mid
             lc_mid cap_mid self'
      ,
        (<<FUTURE: reserve_future_memory lc_src.(Local.promises) cap_src prom_src' cap_src'>>) /\

        (<<SCMID: Memory.closed_timemap max_src cap_mid>>) /\
        (<<MEMMID: Memory.closed cap_mid>>) /\
        (<<LOCALMID: Local.wf lc_mid cap_mid>>) /\

        (<<COMPLETE: forall loc to (IN: List.In (loc, to) times), mappable_time f loc to>>) /\

        (<<MEMORYMAP: memory_map f cap_tgt cap_mid>>) /\
        (<<LOCALMAP: local_map f lc_tgt lc_mid>>) /\
        (<<SCMAP: timemap_map f max_tgt max_mid>>) /\
        (<<SCLE: TimeMap.le max_src max_mid>>) /\

        (<<MEM: sim_memory L (others \2/ self') cap_src' cap_mid>>) /\
        (<<SIM: sim_local L self' (Local.mk lc_src.(Local.tview) cap_src) lc_mid>>) /\

        (<<PROMATTACH: promises_not_attached self' (promised prom_src') cap_src'>>) /\
        (<<EXCLUSIVE: forall loc' ts' (OTHER: others loc' ts'),
            exists from msg, (<<UNCH: unchangable cap_src prom_src' loc' ts' from msg>>)>>) /\
        (<<JOINED: forall loc ts (NLOC: ~ L loc), List.Forall (fun vw => Memory.closed_view vw cap_src') (views loc ts)>>).
  Proof.
  Admitted.

  Record deattached_memory
         (f: Loc.t -> Time.t -> Time.t -> Prop)
         (mem mem_d: Memory.t): Prop :=
    {
      deattached_memory_get_normal:
        forall loc to
               (NMAP0: forall fto, ~ f loc to fto)
               (NMAP1: forall f_1to, ~ f loc f_1to to),
          Memory.get loc to mem = Memory.get loc to mem_d;
      deattached_memory_get_new:
        forall loc to fto
               (MAP: f loc to fto),
        exists from,
          (<<GETORIG: Memory.get loc to mem = Some (from, Message.reserve)>>) /\
          (<<GETDNEW: Memory.get loc fto mem_d = Some (from, Message.reserve)>>) /\
          (<<GETDORIG: Memory.get loc to mem_d = None>>) /\
          (<<TS0: Time.lt from fto>>) /\
          (<<TS1: Time.lt fto to>>);
    }.

  Lemma deattached_memory_map_eq
        f mem mem_d
        (DEATTACH: deattached_memory f mem mem_d)
        loc to fto0 fto1
        (MAP0: f loc to fto0)
        (MAP1: f loc to fto1)
    :
      fto0 = fto1.
  Proof.
    hexploit deattached_memory_get_new; try apply MAP0; eauto. i. des.
    hexploit deattached_memory_get_new; try apply MAP1; eauto. i. des. clarify.
    exploit Memory.get_disjoint.
    { eapply GETDNEW. }
    { eapply GETDNEW0. } i. des; subst; auto.
    exfalso. eapply x0.
    { instantiate (1:=Time.meet fto0 fto1). unfold Time.meet. des_ifs.
      - econs; ss. refl.
      - econs; ss. left. auto. }
    { unfold Time.meet. des_ifs. econs; ss. refl. }
  Qed.

  Lemma deattached_memory_map_inj
        f mem mem_d
        (DEATTACH: deattached_memory f mem mem_d)
        loc to0 to1 fto
        (MAP0: f loc to0 fto)
        (MAP1: f loc to1 fto)
    :
      to0 = to1.
  Proof.
    hexploit deattached_memory_get_new; try apply MAP0; eauto. i. des.
    hexploit deattached_memory_get_new; try apply MAP1; eauto. i. des. clarify.
    exploit Memory.get_disjoint.
    { eapply GETORIG. }
    { eapply GETORIG0. } i. des; subst; auto.
    exfalso. eapply x0.
    { instantiate (1:=fto). econs; ss. left. auto. }
    { econs; ss. left. auto. }
  Qed.

  Lemma deattached_memory_get_orig_unmap
        f mem mem_d
        (DEATTACH: deattached_memory f mem mem_d)
        loc to fto
        (MAP: f loc to fto)
    :
      Memory.get loc fto mem = None.
  Proof.
    hexploit deattached_memory_get_new; eauto. i. des.
    destruct (Memory.get loc fto mem) as [[from' msg]|] eqn:GET; auto. exfalso.
    exploit Memory.get_disjoint.
    { eapply GETORIG. }
    { eapply GET. } i. des; subst.
    - eapply Time.lt_strorder; eauto.
    - eapply x0.
      + instantiate (1:=fto). econs; ss. left. auto.
      + econs; ss.
        * eapply memory_get_ts_strong in GET. des; subst; auto.
          exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS0. }
          { eapply Time.bot_spec. }
        * refl.
  Qed.

  Lemma deattaching_promises
        (self: Loc.t -> Time.t -> Prop) mem prom
        (SELF: forall loc to (SELF: self loc to),
            exists from,
              (<<GET: Memory.get loc to prom = Some (from, Message.reserve)>>))
        (MLE: Memory.le prom mem)
        (FIN: Memory.finite prom)
        (CLOSED: Memory.closed mem)
    :
      exists f mem' prom',
        (<<FUTURE: reserve_future_memory prom mem prom' mem'>>) /\
        (<<DEATTACHMEM: deattached_memory f mem mem'>>) /\
        (<<DEATTACHPROM: deattached_memory f prom prom'>>) /\
        (<<COMPLETE: forall loc to (SELF: self loc to),
            exists fto, (<<MAP: f loc to fto>>)>>) /\
        (<<SOUND: forall loc to fto (MAP: f loc to fto), self loc to>>).
  Proof.
    assert (exists (l: list (Loc.t * Time.t)),
               (<<COMPLETE: forall loc to,
                   self loc to <-> List.In (loc, to) l>>)).
    { unfold Memory.finite in *. des.
      hexploit list_filter_exists.
      instantiate (2:=fun locto => self (fst locto) (snd locto)).
      instantiate (1:=dom). i. des. exists l'.
      i. split.
      - i. eapply COMPLETE. splits; auto.
        exploit SELF; eauto. i. des. eapply FIN; eauto.
      - i. eapply COMPLETE in H. des. auto.
    }
    des. ginduction l.
    { i. exists (fun _ _ _ => False), mem, prom. splits.
      - econs 1.
      - econs; i; ss.
      - econs; i; ss.
      - i. eapply COMPLETE in SELF0. ss.
      - i. ss. }
    { i. destruct a as [loc to].
      destruct (classic (List.In (loc, to) l)) as [IN|NIN].
      { eapply IHl; eauto. i. rewrite COMPLETE. ss.
        split; i; auto. des; auto. clarify. }
      hexploit (IHl L (fun loc' to' => (<<SELF: self loc' to'>>)
                                       /\ (<<REMOVE: (loc, to) <> (loc', to')>>))); eauto.
      { i. des. eauto. }
      { i. split; i.
        - des. eapply COMPLETE in SELF0. ss. des; auto. clarify.
        - split.
          + eapply COMPLETE. ss. auto.
          + ii. clarify. }
      i. des.

      assert (SELFTS: self loc to).
      { eapply COMPLETE. ss. auto. }
      assert (NMAP0: forall fto, ~ f loc to fto).
      { ii. eapply SOUND in H. des. clarify. }
      assert (NMAP1: forall f_1to, ~ f loc f_1to to).
      { ii. dup H. eapply SOUND in H. des.
        hexploit (DEATTACHPROM.(deattached_memory_get_new)); eauto. i. des.
        exploit SELF; try apply SELFTS. i. des.
        exploit Memory.get_disjoint.
        { eapply GET. }
        { eapply GETORIG. }
        i. des; subst; clarify. eapply x0.
        { instantiate (1:=to). econs; ss.
          - apply memory_get_ts_strong in GET. des; subst; auto.
            exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
            { eapply TS0. }
            { eapply Time.bot_spec. }
          - refl. }
        { econs; ss. left. auto. }
      }

      hexploit SELF.
      { eauto. } i. des.
      rewrite DEATTACHPROM.(deattached_memory_get_normal) in GET; eauto.
      assert (GETMEM: Memory.get loc to mem' = Some (from, Message.reserve)).
      { eapply reserve_future_memory_le; eauto. }

      assert (FROMTO: Time.lt from to).
      { apply memory_get_ts_strong in GET. des; auto. subst.
        exploit Memory.future_closed.
        { eapply reserve_future_future; eauto. }
        { eauto. }
        intros []. erewrite INHABITED in GETMEM. clarify. }
      set (fto := Time.middle from to).

      hexploit (@Memory.remove_exists prom' loc from to Message.reserve); eauto.
      intros [prom0 REMOVEPROM].
      hexploit (@Memory.remove_exists_le prom' mem' loc from to Message.reserve); eauto.
      { eapply reserve_future_memory_le; eauto. }
      intros [mem0 REMOVEMEM].

      assert (PROMISE0: Memory.promise prom' mem' loc from to Message.reserve prom0 mem0 Memory.op_kind_cancel).
      { econs; eauto. }

      hexploit (@Memory.add_exists mem0 loc from fto Message.reserve).
      { ii. exploit Memory.get_disjoint.
        { instantiate (4:=to2).
          erewrite Memory.remove_o in GET2; eauto. des_ifs. eauto. }
        { eapply GETMEM. }
        i. des; subst.
        { eapply Memory.remove_get0 in REMOVEMEM. des. clarify. }
        { eapply x1; eauto. inv LHS. econs; ss.
          transitivity fto; auto. left. eapply Time.middle_spec; auto. }
      }
      { eapply Time.middle_spec; eauto. }
      { econs. }
      intros [mem1 ADDMEM].
      hexploit (@Memory.add_exists_le prom0 mem0 loc from fto Message.reserve); eauto.
      { eapply promise_memory_le; cycle 1; eauto.
        eapply reserve_future_memory_le; eauto. }
      intros [prom1 ADDPROM].
      assert (PROMISE1: Memory.promise prom0 mem0 loc from fto Message.reserve prom1 mem1 Memory.op_kind_add).
      { econs; eauto. i. clarify. }

      assert (NMAP2: forall fto', ~ f loc fto fto').
      { i. intros MAP.
        exploit deattached_memory_get_new; try apply DEATTACHPROM; eauto. i. des.
        exploit Memory.get_disjoint.
        { eapply GETORIG. }
        { instantiate (3:=to).
          erewrite deattached_memory_get_normal; try apply DEATTACHPROM; eauto. }
        i. des.
        { exfalso. eapply Time.lt_strorder.
          instantiate (1:=to). rewrite <- x0 at 1.
          eapply Time.middle_spec; auto. }
        { eapply x0.
          { instantiate (1:=fto). econs; ss.
            - etrans; eauto.
            - refl. }
          { econs; ss.
            - eapply Time.middle_spec; auto.
            - left. eapply Time.middle_spec; auto. }
        }
      }

      assert (NMAP3: forall to', ~ f loc to' fto).
      { i. intros MAP.
        exploit deattached_memory_get_new; try apply DEATTACHPROM; eauto. i. des.
        exploit Memory.get_disjoint.
        { eapply GETORIG. }
        { instantiate (3:=to).
          erewrite deattached_memory_get_normal; try apply DEATTACHPROM; eauto. }
        i. des; subst.
        { eapply NMAP0; eauto. }
        { eapply x0.
          { instantiate (1:=fto). econs; ss. left. auto. }
          { econs; ss.
            - eapply Time.middle_spec; auto.
            - left. eapply Time.middle_spec; auto. }
        }
      }

      exists (fun l t ft => (<<ORIG: f l t ft>>) \/ (<<NEW: l = loc /\ t = to /\ ft = fto>>)),
      mem1, prom1. splits.
      { eapply reserve_future_memory_trans; eauto. }
      { econs.
        { i. erewrite (@Memory.add_o mem1); eauto.
          erewrite (@Memory.remove_o mem0); eauto. des_ifs.
          - ss. des; clarify. exfalso.
            eapply NMAP5; eauto.
          - ss. des; clarify. exfalso.
            eapply NMAP4; eauto.
          - eapply deattached_memory_get_normal; eauto.
            { ii. eapply NMAP4; eauto. }
            { ii. eapply NMAP5; eauto. }
        }
        { i. des.
          { exploit deattached_memory_get_new; try apply DEATTACHMEM; eauto. i. des. esplits; eauto.
            - erewrite (@Memory.add_o mem1); eauto.
              erewrite (@Memory.remove_o mem0); eauto. des_ifs.
              + ss. des; clarify. exfalso. eapply NMAP3; eauto.
              + ss. des; clarify. exfalso. eapply NMAP1; eauto.
            - erewrite (@Memory.add_o mem1); eauto.
              erewrite (@Memory.remove_o mem0); eauto. des_ifs.
              ss. des; clarify. exfalso. eapply NMAP2; eauto.
          }
          { subst. exists from. splits; auto.
            { erewrite deattached_memory_get_normal; try apply DEATTACHMEM; eauto. }
            { eapply Memory.add_get0; eauto. }
            { erewrite (@Memory.add_o mem1); eauto.
              erewrite (@Memory.remove_o mem0); eauto. des_ifs.
              - ss. des; clarify.
                exfalso. eapply Time.lt_strorder.
                instantiate (1:=to). rewrite a0 at 1. eapply Time.middle_spec; auto.
              - ss. des; clarify. }
            { eapply Time.middle_spec; eauto. }
            { eapply Time.middle_spec; eauto. }
          }
        }
      }
      { econs.
        { i. erewrite (@Memory.add_o prom1); eauto.
          erewrite (@Memory.remove_o prom0); eauto. des_ifs.
          - ss. des; clarify. exfalso.
            eapply NMAP5; eauto.
          - ss. des; clarify. exfalso.
            eapply NMAP4; eauto.
          - eapply deattached_memory_get_normal; eauto.
            { ii. eapply NMAP4; eauto. }
            { ii. eapply NMAP5; eauto. }
        }
        { i. des.
          { exploit deattached_memory_get_new; try apply DEATTACHPROM; eauto. i. des. esplits; eauto.
            - erewrite (@Memory.add_o prom1); eauto.
              erewrite (@Memory.remove_o prom0); eauto. des_ifs.
              + ss. des; clarify. exfalso. eapply NMAP3; eauto.
              + ss. des; clarify. exfalso. eapply NMAP1; eauto.
            - erewrite (@Memory.add_o prom1); eauto.
              erewrite (@Memory.remove_o prom0); eauto. des_ifs.
              ss. des; clarify. exfalso. eapply NMAP2; eauto.
          }
          { subst. exists from. splits; auto.
            { erewrite deattached_memory_get_normal; try apply DEATTACHPROM; eauto. }
            { eapply Memory.add_get0; eauto. }
            { erewrite (@Memory.add_o prom1); eauto.
              erewrite (@Memory.remove_o prom0); eauto. des_ifs.
              - ss. des; clarify.
                exfalso. eapply Time.lt_strorder.
                instantiate (1:=to). rewrite a0 at 1. eapply Time.middle_spec; auto.
              - ss. des; clarify. }
            { eapply Time.middle_spec; eauto. }
            { eapply Time.middle_spec; eauto. }
          }
        }
      }
      { i. destruct (classic ((loc0, to0) = (loc, to))).
        - clarify. eauto.
        - exploit COMPLETE0; eauto. i. des. eauto. }
      { i. des.
        - eapply SOUND in MAP. des. auto.
        - subst. auto. }
    }
  Qed.

  Definition attached_promises (self prom: Loc.t -> Time.t -> Prop) (mem: Memory.t)
             (loc: Loc.t) (ts0: Time.t): Prop :=
    (<<SELF: self loc ts0>>) /\
    (<<ATTACH: exists ts1 msg,
        (<<GET: Memory.get loc ts1 mem = Some (ts0, msg)>>) /\
        (<<OTHERS: ~ prom loc ts1>>)>>).

  Inductive mapped_self_promises (self: Loc.t -> Time.t -> Prop)
            (f: Loc.t -> Time.t -> Time.t -> Prop)
    :
      forall (loc: Loc.t) (ts: Time.t), Prop:=
  | mapped_self_promises_unmap
      loc ts
      (SELF: self loc ts)
      (UNMAP: forall fts, ~ f loc ts fts)
    :
      mapped_self_promises self f loc ts
  | mapped_self_promises_map
      loc ts fts
      (MAP: f loc ts fts)
      (SELF: self loc ts)
    :
      mapped_self_promises self f loc fts
  .

  Inductive mid_map (mem: Memory.t) (prom: Memory.t)
            (f: Loc.t -> Time.t -> Time.t -> Prop)
    :
      Loc.t -> Time.t -> Time.t -> Prop :=
  | mid_map_normal
      loc ts
      (NMAP: forall fts, ~ f loc ts fts)
      (PROMISED: promised mem loc ts)
    :
      mid_map mem prom f loc ts ts
  | mid_map_promise
      loc from to msg
      (NMAP: forall fts, ~ f loc to fts)
      (PROMISED: Memory.get loc to prom = Some (from, msg))
    :
      mid_map mem prom f loc from from
  | mid_map_map
      loc ts fts
      (MAP: f loc ts fts)
    :
      mid_map mem prom f loc ts fts
  .
  Hint Constructors mid_map.

  Lemma mid_map_map_bot f mem mem' prom
        (DEATTACHMEM: deattached_memory f mem mem')
        (CLOSED: Memory.closed mem)
    :
      mapping_map_bot (mid_map mem prom f).
  Proof.
    ii. econs 1.
    - ii. exploit deattached_memory_get_new; eauto. i. des.
      exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
      { eapply TS1. }
      { eapply Time.bot_spec. }
    - inv CLOSED. econs; eauto.
  Qed.

  Lemma mid_map_map_lt f mem mem' prom
        (DEATTACHMEM: deattached_memory f mem mem')
    :
      mapping_map_lt (mid_map mem prom f).
  Proof.
    ii. inv MAP0; inv MAP1.
    - auto.
    - auto.
    - exploit deattached_memory_get_new; eauto. i. des. split.
      + i. inv PROMISED. destruct msg.
        exploit memory_get_from_mon.
        { eapply GET. }
        { eapply GETORIG. }
        { eauto. }
        i. eapply TimeFacts.le_lt_lt; eauto.
      + i. etrans; eauto.
    - auto.
    - auto.
    -

      admit.
    - exploit deattached_memory_get_new; eauto. i. des. split.
      + i. etrans; eauto.
      + i. inv PROMISED. destruct msg.
        destruct (Time.le_lt_dec ft1 t0); auto. destruct l.
        { exfalso. exploit memory_get_from_mon.
          { eapply GET. }
          { eapply GETORIG. }
          { eauto. }
          i. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
          { eapply x0. }
          { transitivity ft0; auto. }
        }
        { inv H0. exfalso. eapply NMAP; eauto. }
    - admit.
    - exploit deattached_memory_get_new; try apply MAP; eauto.
      exploit deattached_memory_get_new; try apply MAP0; eauto. i. des.
      destruct (Time.le_lt_dec t0 t1); cycle 1.
      { split; i.
        - exfalso. eapply Time.lt_strorder. transitivity t0; eauto.
        - exploit memory_get_from_mon.
          { eapply GETORIG0. }
          { eapply GETORIG. }
          { eauto. }
          i. exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt.
          { eapply TS3. } etrans.
          { eapply x0. } etrans.
          { left. eapply TS0. }
          { left. auto. }
      }
      destruct l.
      { split; i; auto.
        exploit memory_get_from_mon.
        { eapply GETORIG. }
        { eapply GETORIG0. }
        { eauto. }
        i. etrans.
        { eapply TS1. } eapply TimeFacts.le_lt_lt.
        { eapply x0. }
        { eauto. }
      }
      { inv H. clarify. hexploit deattached_memory_map_eq.
        { eauto. }
        { eapply MAP. }
        { eapply MAP0. }
        i. subst. split; i; exfalso; eapply Time.lt_strorder; eauto.
      }
  Admitted.

  Lemma deattached_promises_not_attached (self: Loc.t -> Time.t -> Prop)
        f prom mem prom' mem'
        (MLE: Memory.le prom' mem')
        (DEATTACHMEM: deattached_memory f mem mem')
        (DEATTACHPROM: deattached_memory f prom prom')
        (COMPLETE: forall loc to (SELF: attached_promises self (promised prom) mem loc to),
            exists fto, (<<MAP: f loc to fto>>))
    :
      promises_not_attached (mapped_self_promises self f) (promised prom') mem'.
  Proof.
    ii. inv PROMISED.
    - admit.
    - hexploit deattached_memory_get_new; try apply DEATTACHMEM; eauto. i. des.
  Admitted.

End MIDDLE.
