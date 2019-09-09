Require Import Omega.
Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import Loc.
Require Import Time.
Require Import Event.
From PromisingLib Require Import Language.
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


(* TODO unifiy and remove definitions in Event.v *)
Definition ProgramEvent_is_updating (e:ProgramEvent.t): option (Loc.t * Const.t * Ordering.t) :=
  match e with
  | ProgramEvent.update loc valr _ ordr _ => Some (loc, valr, ordr)
  | _ => None
  end.

Inductive pf_race_condition e1 e2: Prop :=
| pf_race_condition_rw
    loc val1 val2 ordr ordw
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, val1, ordr))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, val2, ordw))
    (ORDW: Ordering.le ordw Ordering.relaxed)
| pf_race_condition_uu
    loc val1 val2 ordu1 ordu2
    (EVENT1: ProgramEvent_is_updating e1 = Some (loc, val1, ordu1))
    (EVENT2: ProgramEvent_is_updating e2 = Some (loc, val2, ordu2))
    (ORDU: Ordering.le ordu1 Ordering.relaxed \/ Ordering.le ordu2 Ordering.relaxed)
.
Hint Constructors pf_race_condition.

Definition can_step lang (st : Language.state lang) (e : ProgramEvent.t) : Prop :=
  exists st', Language.step _ e st st'.

Inductive pf_race (c:Configuration.t): Prop :=
| race_intro
    tid1 e1 lang1 st1 lc1
    tid2 e2 lang2 st2 lc2
    (TID1: IdentMap.find tid1 c.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
    (TID2: IdentMap.find tid2 c.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
    (TIDDIFF: tid1 <> tid2)
    (PROEVT1: can_step _ st1 e1)
    (PROEVT2: can_step _ st2 e2)
    (RACE: pf_race_condition e1 e2)
.
Hint Constructors pf_race.

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2
         (STEPS: rtc pftstep_all c1 c2)
         (RACE: pf_race c2), False.

Lemma pf_racefree_step c1 c2
      (RACEFREE : pf_racefree c1)
      (STEP : rtc pftstep_all c1 c2) :
  pf_racefree c2.
Proof.
  intros c3 STEPS RACE.
  apply (RACEFREE c3); auto. etrans; eauto.
Qed.

Definition is_reading lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_reading e = Some (l, v, o').

Definition is_writing lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent.is_writing e = Some (l, v, o').

Definition is_updating lang (st : Language.state lang) l o :=
  exists e v o', can_step _ st e /\
                 Ordering.le o' o /\
                 ProgramEvent_is_updating e = Some (l, v, o').

Definition is_aborting lang (st : Language.state lang) :=
  can_step _ st ProgramEvent.failure.
