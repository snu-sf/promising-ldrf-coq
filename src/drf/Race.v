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
Require Import Configuration.
Require Import Progress.

Require Import PF.

Set Implicit Arguments.


Definition can_step lang (st : Language.state lang) (e : ProgramEvent.t) : Prop :=
  exists st', Language.step _ e st st'.

Inductive race_condition e1 e2 ord1 ord2 : Prop :=
| race_condition_rw loc val1 val2
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, val1, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, val2, ord2))
| race_condition_ww loc val1 val2
    (EVENT1: ProgramEvent.is_writing e1 = Some (loc, val1, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, val2, ord2))
.
Hint Constructors race_condition.

Inductive race (c:Configuration.t) (ord1 ord2:Ordering.t): Prop :=
| race_intro
    tid1 e1 lang1 st1 lc1
    tid2 e2 lang2 st2 lc2
    (TID1: IdentMap.find tid1 c.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
    (TID2: IdentMap.find tid2 c.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
    (TIDDIFF: tid1 <> tid2)
    (PROEVT1: can_step _ st1 e1)
    (PROEVT2: can_step _ st2 e2)
    (RACE: race_condition e1 e2 ord1 ord2)
.
Hint Constructors race.

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
         (STEPS: rtc pftstep_all c1 c2),
    (<<RACEFREE: forall (RACE: race c2 ordr ordw),
        (<<ORDR: Ordering.le Ordering.acqrel ordr>>) /\
        (<<ORDW: Ordering.le Ordering.acqrel ordw>>)>>)
.

Lemma pf_racefree_step c1 c2
      (RACEFREE : pf_racefree c1)
      (STEP : rtc pftstep_all c1 c2) :
  pf_racefree c2.
Proof.
  intros c3 ordr ordw STEPS.
  apply (RACEFREE c3); etrans; eauto.
Qed.

Definition is_reading lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_reading e = Some (l, v, o').

Definition is_writing lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_writing e = Some (l, v, o').
