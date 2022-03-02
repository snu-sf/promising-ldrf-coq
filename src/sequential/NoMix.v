From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
Require Import Simple.

Require Import Event.

Section NOMIX.
  Variable loc_na: Loc.t -> Prop.
  Variable loc_at: Loc.t -> Prop.

  Definition _nomix
             (nomix: forall (lang: language) (st: lang.(Language.state)), Prop)
             (lang: language) (st: lang.(Language.state)): Prop :=
    forall st1 e
           (STEP: lang.(Language.step) e st st1),
      (<<NA: forall l c (NA: is_atomic_event e = false) (ACC: is_accessing e = Some (l, c)), loc_na l>>) /\
        (<<AT: forall l c (AT: is_atomic_event e = true) (ACC: is_accessing e = Some (l, c)), loc_at l>>) /\
        (<<CONT: nomix lang st1>>)
  .

  Definition nomix := paco2 _nomix bot2.
  Arguments nomix: clear implicits.

  Lemma nomix_mon: monotone2 _nomix.
  Proof.
    ii. exploit IN; eauto. i. des. splits.
    { i. hexploit NA; eauto. }
    { i. hexploit AT; eauto. }
    { auto. }
  Qed.
  #[local] Hint Resolve nomix_mon: paco.
End NOMIX.

#[export] Hint Resolve nomix_mon: paco.
#[export] Hint Resolve cpn2_wcompat: paco.
