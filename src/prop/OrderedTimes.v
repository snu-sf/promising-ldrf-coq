Require Import RelationClasses.

From Paco Require Import paco.
From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
Require Import Time.



Fixpoint incr_time_seq (n: nat): Time.t :=
  match n with
  | O => BinNums.xI (BinNums.xH)
  | S n' => BinNums.xI (incr_time_seq n')
  end.

Lemma incr_time_seq_succesor' n
  :
    DenseOrder.DOAux.lt (incr_time_seq n) (incr_time_seq (S n)).
Proof.
  ginduction n; ss; i.
  { econs. econs. }
  { econs. eauto. }
Qed.

Lemma incr_time_seq_lt' n0 n1
      (LT: n0 < n1)
  :
    DenseOrder.DOAux.lt (incr_time_seq n0) (incr_time_seq n1).
Proof.
  ginduction LT.
  { eapply incr_time_seq_succesor'. }
  { etrans.
    { eapply IHLT. }
    { eapply incr_time_seq_succesor'. }
  }
Qed.

Lemma incr_time_seq_diverge' ts
  :
    exists n, <<LT: DenseOrder.DOAux.lt ts (incr_time_seq n)>>.
Proof.
  ginduction ts.
  { des. exists (S n). ss. econs. eauto. }
  { exists 0. ss. econs. }
  { exists 0. ss. econs. }
Qed.

Lemma incr_time_seq_lt n0 n1
      (LT: n0 < n1)
  :
    Time.lt (incr_time_seq n0) (incr_time_seq n1).
Proof.
  set (incr_time_seq_lt' n0 n1 LT). inv l; try by econs.
  destruct n0; ss.
Qed.

Lemma incr_time_seq_diverge ts
  :
    exists n, <<LT: Time.lt ts (incr_time_seq n)>>.
Proof.
  set (incr_time_seq_diverge' ts). des.
  exists n. inv LT; try by econs.
  destruct n; ss.
Qed.


Definition lb_time (times: Time.t -> Prop) (ts ts': Time.t) :=
  forall t (IN: times t) (LT: Time.lt ts t),
    Time.lt ts' t.

Lemma eq_lb_time times ts
  :
    lb_time times ts ts.
Proof.
  ii. auto.
Qed.

Lemma lb_time_lower times ts ts'0 ts'1
      (LB: lb_time times ts ts'0)
      (TS: Time.le ts'1 ts'0)
  :
    lb_time times ts ts'1.
Proof.
  ii. exploit LB; eauto.
  i. eapply TimeFacts.le_lt_lt; eauto.
Qed.

Definition well_ordered (times: Time.t -> Prop): Prop :=
  forall (sub: Time.t -> Prop)
         (SUB: sub <1= times)
         x
         (INHABITED: sub x),
  exists ts,
    (<<SAT: sub ts>>) /\
    (<<LEAST: forall ts' (IN: sub ts'), Time.le ts ts'>>).

Lemma lb_time_exists times
      (WO: well_ordered times)
      ts
  :
    exists ts', <<TS: Time.lt ts ts'>> /\ <<LB: lb_time times ts ts'>>.
Proof.
  destruct (classic (exists x, __guard__(fun x => <<IN: times x>> /\ <<LT: Time.lt ts x>>) x)).
  { des. eapply WO in H.
    { des. exists (Time.middle ts ts0). unguard. des. splits; auto.
      { eapply Time.middle_spec; auto. }
      { ii. hexploit (LEAST t).
        { splits; eauto. }
        i. eapply TimeFacts.lt_le_lt; eauto.
        eapply Time.middle_spec; auto. }
    }
    { i. unguard. ss. des. auto. }
  }
  { exists (Time.incr ts). splits; auto.
    { eapply Time.incr_spec. }
    { ii. exfalso. eapply H. unguard. esplits; eauto. }
  }
Qed.


Lemma sub_well_ordered times0 times1
      (WO: well_ordered times0)
      (SUB: times1 <1= times0)
  :
    well_ordered times1.
Proof.
  ii. exploit WO.
  { i. eapply SUB. eapply SUB0. eapply PR. }
  { eauto. }
  { i. des. exists ts. splits; eauto. }
Qed.

Lemma join_well_ordered times0 times1
      (WO0: well_ordered times0)
      (WO1: well_ordered times1)
  :
    well_ordered (times0 \1/ times1).
Proof.
  ii. exploit SUB; eauto. i. des.
  { destruct (classic (exists ts1, <<IN1: (sub /1\ times1) ts1>>)) as [?|NIN].
    { des. exploit (WO0 (sub /1\ times0)).
      { i. des; auto. }
      { instantiate (1:=x). splits; auto. } i. des.
      exploit (WO1 (sub /1\ times1)).
      { i. des; auto. }
      { instantiate (1:=ts1). splits; auto. } i. des.
      exists (Time.meet ts ts0). splits; auto.
      { unfold Time.meet. des_ifs. }
      { i. unfold Time.meet. des_ifs.
        { exploit SUB; eauto. i. des; eauto. }
        { exploit SUB; eauto. i. des; eauto.
          exploit LEAST; eauto. i.
          transitivity ts; eauto. left. auto. }
      }
    }
    { exploit (WO0 sub); eauto.
      i. exploit SUB; eauto. i. des; auto. exfalso. eauto. }
  }
  { destruct (classic (exists ts0, <<IN0: (sub /1\ times0) ts0>>)) as [?|NIN].
    { des. exploit (WO1 (sub /1\ times1)).
      { i. des; auto. }
      { instantiate (1:=x). splits; auto. } i. des.
      exploit (WO0 (sub /1\ times0)).
      { i. des; auto. }
      { instantiate (1:=ts0). splits; auto. } i. des.
      exists (Time.meet ts ts1). splits; auto.
      { unfold Time.meet. des_ifs. }
      { i. unfold Time.meet. des_ifs.
        { exploit SUB; eauto. i. des; eauto. }
        { exploit SUB; eauto. i. des; eauto.
          exploit LEAST; eauto. i.
          transitivity ts; eauto. left. auto. }
      }
    }
    { exploit (WO1 sub); eauto.
      i. exploit SUB; eauto. i. des; auto. exfalso. eauto. }
  }
Qed.

Lemma empty_well_ordered
  :
    well_ordered bot1.
Proof.
  ii. eapply SUB in INHABITED. ss.
Qed.

Lemma singleton_well_ordered ts
  :
    well_ordered (eq ts).
Proof.
  ii. exploit SUB; eauto. i. subst.
  esplits; eauto. i. eapply SUB in IN. subst. refl.
Qed.

Lemma finite_well_ordered (l: list Time.t)
  :
    well_ordered (fun ts => List.In ts l).
Proof.
  induction l.
  { ss. eapply empty_well_ordered. }
  { ss. eapply join_well_ordered; eauto.
    eapply singleton_well_ordered. }
Qed.

Lemma finite_join_well_ordered
      (sets: nat -> (Time.t -> Prop))
      (WO: forall n, well_ordered (sets n))
      n
  :
    well_ordered (fun ts => exists n', (<<LT: n' < n>>) /\ (<<SAT: sets n' ts>>)).
Proof.
  induction n.
  { eapply sub_well_ordered with (times0 := bot1).
    { eapply empty_well_ordered. }
    { i. ss. des. inv LT. }
  }
  { eapply sub_well_ordered.
    { eapply join_well_ordered.
      { eapply IHn. }
      { eapply (WO n). }
    }
    { i. des. inv LT; auto. left. exists n'; eauto. }
  }
Qed.

Lemma increasing_join_well_ordered
      (f: nat -> Time.t)
      (sets: nat -> (Time.t -> Prop))
      (MON: forall n0 n1 (LT: n0 < n1), Time.lt (f n0) (f n1))
      (DIV: forall ts, exists n, <<LT: Time.lt ts (f n)>>)
      (LB: forall n ts (SAT: sets n ts), Time.le (f n) ts)
      (WO: forall n, well_ordered (sets n))
  :
    well_ordered (fun ts => exists n, <<SAT: sets n ts>>).
Proof.
  ii. hexploit (DIV x); eauto. i. des.
  exploit SUB; eauto. i. des.
  assert (LT0: n0 < n).
  { destruct (Compare_dec.le_lt_dec n n0); auto.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
    { eapply LB. eapply SAT. } eapply TimeFacts.lt_le_lt.
    { eapply LT. }
    { eapply Lt.le_lt_or_eq in l. des.
      { left. eapply MON; eauto. }
      { subst. refl. }
    }
  }
  exploit finite_join_well_ordered.
  { eapply WO. }
  { instantiate (1:=n).
    instantiate (1:=fun ts =>
                      exists n', (<<LT: n' < n>>) /\ (<<SAT: sets n' ts>>) /\ (<<SUB: sub ts>>)).
    i. ss. des. eauto. }
  { instantiate (1:=x). ss. esplits; eauto. }
  i. des. exists ts. splits; auto.
  i. destruct (Time.le_lt_dec x ts').
  { transitivity x; auto. eapply LEAST. exists n0. splits; auto. }
  { exploit (SUB ts'); eauto. i. des. eapply LEAST; eauto.
    exists n1. splits; eauto.
    destruct (Compare_dec.le_lt_dec n n1); auto.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt.
    { eapply LB. eapply SAT1. } eapply TimeFacts.lt_le_lt.
    { eapply l. } etrans.
    { left. eapply LT. }
    { eapply Lt.le_lt_or_eq in l0. des.
      { left. eapply MON; eauto. }
      { subst. refl. }
    }
  }
Qed.

Definition incr_times (ts: Time.t):=
  exists n, incr_time_seq n = ts.

Lemma incr_times_well_ordered
  :
    well_ordered incr_times.
Proof.
  hexploit (increasing_join_well_ordered
              incr_time_seq
              (fun n => eq (incr_time_seq n))).
  { eapply incr_time_seq_lt. }
  { eapply incr_time_seq_diverge. }
  { i. subst. refl. }
  { i. apply singleton_well_ordered. }
  i. eapply sub_well_ordered; eauto.
Qed.

Lemma mapped_well_ordered
      (f: Time.t -> Time.t -> Prop)
      (times ftimes: Time.t -> Prop)
      (MAPLT: forall t0 t1 ft0 ft1
                     (MAP0: f t0 ft0)
                     (MAP1: f t1 ft1),
          Time.lt t0 t1 <-> Time.lt ft0 ft1)
      (WO: well_ordered times)
      (FTIMES: forall fts (IN: ftimes fts),
          exists ts,
            (<<MAP: f ts fts>>) /\
            (<<TIMES: times ts>>))
  :
    well_ordered ftimes.
Proof.
  ii.
  dup INHABITED. eapply SUB in INHABITED. dup INHABITED. eapply FTIMES in INHABITED. des.
  exploit (WO (fun ts => exists fts, (<<MAP: f ts fts>>) /\ (<<TIMES: sub fts>>))).
  { i. des. eapply SUB in TIMES0. eapply FTIMES in TIMES0. des.
    destruct (Time.le_lt_dec x0 ts0).
    { destruct l.
      { exploit MAPLT.
        { eapply MAP0. }
        { eapply MAP1. } i. des.
        exfalso. eapply Time.lt_strorder. eapply x1; eauto.
      }
      { inv H. auto. }
    }
    { exploit MAPLT.
      { eapply MAP1. }
      { eapply MAP0. } i. des.
      exfalso. eapply Time.lt_strorder. eapply x1; eauto.
    }
  }
  { eauto. }
  { i. des. exists fts. splits; auto. i.
    dup IN. eapply SUB in IN. dup IN. eapply FTIMES in IN. des.
    exploit LEAST; eauto. i.
    destruct (Time.le_lt_dec fts ts'); auto.
    erewrite <- MAPLT in l; eauto. timetac.
  }
Qed.
