Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Language.

Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import Cover.
Require Import MemorySplit.
Require Import MemoryMerge.
Require Import FulfillStep.
Require Import MemoryProps.

Require Import gSimAux.
Require Import LowerMemory.
Require Import JoinedView.

Set Implicit Arguments.

Variant max_readable (mem prom: Memory.t) (loc: Loc.t) (ts: Time.t) (val: Const.t): Prop :=
| max_readable_intro
    from released
    (GET: Memory.get loc ts mem = Some (from, Message.concrete val released))
    (NONE: Memory.get loc ts prom = None)
    (MAX: forall ts' from' msg
                 (TS: Time.lt ts ts')
                 (GET: Memory.get loc ts' mem = Some (from', msg))
                 (MSG: msg <> Message.reserve),
        Memory.get loc ts' prom = Some (from', msg))
.

Lemma max_readable_inj mem prom loc ts0 ts1 val0 val1
      (MAX0: max_readable mem prom loc ts0 val0)
      (MAX1: max_readable mem prom loc ts1 val1)
  :
    (<<TS: ts0 = ts1>>) /\ (<<VAL: val0 = val1>>).
Proof.
  inv MAX0. inv MAX1.
  assert (ts0 = ts1).
  { apply TimeFacts.antisym.
    { destruct (Time.le_lt_dec ts0 ts1); auto.
      hexploit MAX0; eauto; ss.
      i. clarify.
    }
    { destruct (Time.le_lt_dec ts1 ts0); auto.
      hexploit MAX; eauto; ss.
      i. clarify.
    }
  }
  subst. split; auto. clarify.
Qed.

Lemma read_tview_max tvw loc released
      (WF: TView.wf tvw)
  :
    TView.read_tview tvw loc (View.pln (TView.cur tvw) loc) released Ordering.na = tvw.
Proof.
  unfold TView.read_tview. des_ifs. ss.
  rewrite ! View.le_join_l.
  { destruct tvw; auto. }
  { apply View.singleton_rw_spec.
    { apply WF. }
    { transitivity (View.rlx (TView.cur tvw) loc).
      { apply WF. }
      { apply WF. }
    }
  }
  { apply View.bot_spec. }
  { apply View.singleton_rw_spec.
    { apply WF. }
    { apply WF. }
  }
  { apply View.bot_spec. }
Qed.

Lemma max_readable_read_only mem prom tvw loc ts val
      ts' val' released lc
      (MAX: max_readable mem prom loc ts val)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.read_step (Local.mk tvw prom) mem loc ts' val' released Ordering.na lc)
      (CONS: Local.promise_consistent lc)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    (<<TS: ts' = ts>>) /\ (<<VAL: val' = val>>) /\ (<<LOCAL: lc = Local.mk tvw prom>>).
Proof.
  inv READ. ss. assert (ts' = tvw.(TView.cur).(View.pln) loc).
  { apply TimeFacts.antisym.
    { destruct (Time.le_lt_dec ts' (tvw.(TView.cur).(View.pln) loc)); auto.
      inv MAX. hexploit MAX0; eauto; ss.
      i. exploit CONS; eauto; ss. i.
      des_ifs. ss.
      change (Ordering.le Ordering.relaxed Ordering.na) with false in x.
      ss. rewrite TimeMap.le_join_l in x.
      2: { eapply TimeMap.bot_spec. }
      unfold TimeMap.join, TimeMap.singleton in x.
      setoid_rewrite LocFun.add_spec_eq in x.
      exfalso. eapply Time.lt_strorder.
      eapply TimeFacts.lt_le_lt; [eapply x|].
      eapply Time.join_r.
    }
    { inv READABLE. auto. }
  }
  subst. inv MAX. clarify. splits; auto. f_equal.
  apply read_tview_max. apply WF.
Qed.

Lemma max_readable_not_read_race mem prom tvw loc ts val
      val'
      (MAX: max_readable mem prom loc ts val)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (READ: Local.racy_read_step (Local.mk tvw prom) mem loc val' Ordering.na)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    False.
Proof.
  inv READ. inv RACE. ss.
  inv MAX. exploit MAX0; eauto.
  i. clarify.
Qed.

Lemma max_readable_not_write_race mem prom tvw loc ts val
      (MAX: max_readable mem prom loc ts val)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WRITE: Local.racy_write_step (Local.mk tvw prom) mem loc Ordering.na)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    False.
Proof.
  inv WRITE. inv RACE. ss.
  inv MAX. exploit MAX0; eauto.
  { admit. }
  { red. destruct msg; ss; eauto. }
  i. clarify.
Admitted.

Lemma max_readable_read mem prom tvw loc ts val
      (MAX: max_readable mem prom loc ts val)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom) mem)
  :
    exists released,
      (<<READ: Local.read_step (Local.mk tvw prom) mem loc ts val released Ordering.na (Local.mk tvw prom)>>).
Proof.
  inv MAX. esplits. econs; eauto.
  { econs; ss. refl. }
  ss. f_equal. rewrite read_tview_max; auto. apply WF.
Qed.


Lemma non_max_readable_race mem prom tvw loc
      (MAX: forall val, ~ max_readable mem prom loc (tvw.(TView.cur).(View.pln) loc) val)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (CONS: Local.promise_consistent (Local.mk tvw prom))
  :
    exists from to msg,
      (<<GET: Memory.get loc to mem = Some (from, msg)>>) /\
      (<<NONE: Memory.get loc to prom = None>>) /\
      (<<RESERVE: msg <> Message.reserve>>) /\
      (<<TS: Time.lt (tvw.(TView.cur).(View.pln) loc) to>>).
Proof.
  inv WF. inv TVIEW_CLOSED. inv CUR. ss.
  specialize (PLN loc). des.
  apply NNPP. ii. eapply MAX. econs; eauto.
  { destruct (Memory.get loc (tvw.(TView.cur).(View.pln) loc) prom) as [[from' msg]|] eqn:EQ; auto.
    exfalso. exploit PROMISES; eauto. i. clarify.
    exploit CONS; eauto; ss. i.
    eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
    eapply TVIEW_WF.
  }
  { i. eapply NNPP. ii.
    eapply H. esplits; eauto.
    destruct (Memory.get loc ts' prom) as [[]|] eqn:EQ; auto.
    exploit PROMISES; eauto. i. clarify.
  }
Qed.

Lemma non_max_readable_read mem prom tvw loc ts val'
      (MAX: forall val, ~ max_readable mem prom loc ts val)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (CONS: Local.promise_consistent (Local.mk tvw prom))
  :
    Local.racy_read_step (Local.mk tvw prom) mem loc val' Ordering.na.
Proof.
  subst. hexploit non_max_readable_race; eauto. i. des.
  econs; eauto; ss.
Qed.

Lemma non_max_readable_write mem prom tvw loc ts
      (MAX: forall val, ~ max_readable mem prom loc ts val)
      (TS: tvw.(TView.cur).(View.pln) loc = ts)
      (WF: Local.wf (Local.mk tvw prom) mem)
      (CONS: Local.promise_consistent (Local.mk tvw prom))
  :
    Local.racy_write_step (Local.mk tvw prom) mem loc Ordering.na.
Proof.
  subst. hexploit non_max_readable_race; eauto. i. des.
  econs; eauto; ss. econs.
  admit.
Admitted.



  apply WF.



  mem loc Ordering.na
  )


    False.



Qed.

  exploit MAX0; eauto.
  {



    (<<TS: ts' = ts>>) /\ (<<VAL: val' = val>>) /\ (<<LOCAL: lc = Local.mk tvw prom>>).
Proof.


    { apply WF. }
  }

  _ View.bot).
  2:{ apply View.bot_spec. }
  rewrite (@View.le_join_l _ View.bot).
  2:{ apply View.bot_spec. }
  rewrite View.le_join_l.
  2:{ apply View.singleton_rw_spec.
      { apply WF. }
      { apply WF. }
  }
  rewrite View.le_join_l.
  2:{ apply View.singleton_rw_spec.
      { apply WF. }
      { transitivity (View.rlx (TView.cur tvw) loc).
        { apply WF. }
        { apply WF. }
      }
  }

        apply WF. }
  }


      {


  rewrite View.le_join_l.
  2:{ apply View.bot_spec. }




Local.program_step

  ss.

  splits; auto.




    (<<LOCAL:



Lemma max_readable_read mem prom tvw loc ts val
      (MAX: max_readable mem prom loc ts)
      (TS: tvw.(TView.cur).(View.rlx) loc = ts)
  :
    Local.read_step (Local.mk prom
