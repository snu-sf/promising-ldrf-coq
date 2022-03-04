Require Import Lia.
Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Axioms.
From PromisingLib Require Import Basic.
From PromisingLib Require Import DataStructure.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Local.
Require Import Thread.
Require Import Configuration.

Require Import ITreeLang.

Require Import PromiseConsistent.

Set Implicit Arguments.


(* promotion *)

(* we can use interp_state, but we define it directly to avoid unnecessary taus *)
CoFixpoint promote_itree (l: Loc.t) (st: Const.t) R (itr: itree MemE.t R): itree MemE.t (Const.t * R) :=
  match (observe itr) with
  | RetF r => Ret (st, r)
  | TauF itr' => tau;;(promote_itree l st itr')
  | VisF (MemE.read loc ord) k =>
    if Loc.eq_dec loc l
    then tau;;(promote_itree l st (k st))
    else Vis (MemE.read loc ord) (fun r => promote_itree l st (k r))
  | VisF (MemE.write loc val ord) k =>
    if Loc.eq_dec loc l
    then tau;;(promote_itree l val (k tt))
    else Vis (MemE.write loc val ord) (fun r => promote_itree l st (k r))
  | VisF (MemE.update loc (MemE.fetch_add addendum) ordr ordw) k =>
    if Loc.eq_dec loc l
    then tau;;(promote_itree l (Const.add st addendum) (k (Const.add st addendum)))
    else Vis (MemE.update loc (MemE.fetch_add addendum) ordr ordw) (fun r => promote_itree l st (k r))
  | VisF (MemE.update loc (MemE.cas old new) ordr ordw) k =>
    if Loc.eq_dec loc l
    then tau;; (match Const.eqb st old with
                | Some true => promote_itree l new (k 1)
                | _ => promote_itree l st (k 0)
                end)
    else Vis (MemE.update loc (MemE.cas old new) ordr ordw) (fun r => promote_itree l st (k r))
  | VisF e k => Vis e (fun r => promote_itree l st (k r))
  end.

Lemma unfold_promote_itree l st R (itr: itree MemE.t R):
  promote_itree l st itr =
  match (observe itr) with
  | RetF r => Ret (st, r)
  | TauF itr' => tau;;(promote_itree l st itr')
  | VisF (MemE.read loc ord) k =>
    if Loc.eq_dec loc l
    then tau;;(promote_itree l st (k st))
    else Vis (MemE.read loc ord) (fun r => promote_itree l st (k r))
  | VisF (MemE.write loc val ord) k =>
    if Loc.eq_dec loc l
    then tau;;(promote_itree l val (k tt))
    else Vis (MemE.write loc val ord) (fun r => promote_itree l st (k r))
  | VisF (MemE.update loc (MemE.fetch_add addendum) ordr ordw) k =>
    if Loc.eq_dec loc l
    then tau;;(promote_itree l (Const.add st addendum) (k (Const.add st addendum)))
    else Vis (MemE.update loc (MemE.fetch_add addendum) ordr ordw) (fun r => promote_itree l st (k r))
  | VisF (MemE.update loc (MemE.cas old new) ordr ordw) k =>
    if Loc.eq_dec loc l
    then tau;; (match Const.eqb st old with
                | Some true => promote_itree l new (k 1)
                | _ => promote_itree l st (k 0)
                end)
    else Vis (MemE.update loc (MemE.cas old new) ordr ordw) (fun r => promote_itree l st (k r))
  | VisF e k => Vis e (fun r => promote_itree l st (k r))
  end.
Proof.
  apply bisim_is_eq. ginit. gstep. red. refl.
Qed.


(* loc_free *)

Definition loc_free_event (l: Loc.t) R (i: MemE.t R): Prop :=
  match i with
  | MemE.read loc _
  | MemE.write loc _ _
  | MemE.update loc _ _ _ => loc <> l
  | _ => True
  end.

Variant _loc_free_itree l (loc_free_itree: forall R, itree MemE.t R -> Prop):
  forall R, itree MemE.t R -> Prop :=
| loc_free_itree_ret
    R (r: R)
  :
    _loc_free_itree l loc_free_itree (Ret r)
| loc_free_itree_tau
    R (itr: itree MemE.t R) (LOCFREE: loc_free_itree R itr)
  :
    _loc_free_itree l loc_free_itree (tau;;itr)
| loc_free_itree_vis
    R X (e: MemE.t X) k
    (LOCFREE1: loc_free_event l e)
    (LOCFREE2: forall x, loc_free_itree R (k x))
  :
    _loc_free_itree l loc_free_itree (Vis e k)
.
#[export] Hint Constructors _loc_free_itree: core.

Lemma loc_free_itree_mon l: monotone2 (_loc_free_itree l).
Proof.
  ii. destruct IN; eauto.
Qed.
#[export] Hint Resolve loc_free_itree_mon: paco.

Definition loc_free_itree l := paco2 (_loc_free_itree l) bot2.

Lemma promote_itree_loc_free l st R (itr: itree MemE.t R):
  loc_free_itree l (promote_itree l st itr).
Proof.
  revert st itr. pcofix CIH. i. pfold. ides itr.
  { rewrite unfold_promote_itree. econs. }
  { rewrite unfold_promote_itree. econs. right. auto. }
  { rewrite unfold_promote_itree. destruct e; ss.
    { des_ifs.
      { econs. right. auto. }
      { econs; auto. }
    }
    { des_ifs.
      { econs. right. auto. }
      { econs; auto. }
    }
    { des_ifs.
      { econs. right. auto. }
      { econs; auto. }
      { econs. right. auto. }
      { econs; auto. }
      { econs; auto. }
      { econs; auto. }
    }
    { econs; auto. ss. }
    { econs; auto. ss. }
    { econs; auto. ss. }
    { econs; auto. ss. }
  }
Qed.

Lemma step_loc_free
      l e R (itr1 itr2: itree MemE.t R)
      (LOCFREE: loc_free_itree l itr1)
      (STEP: ILang.step e itr1 itr2):
  loc_free_itree l itr2.
Proof.
  punfold LOCFREE.
  destruct STEP; subst; dependent destruction LOCFREE; pclearbot; auto.
  - apply LOCFREE2.
  - apply LOCFREE2.
  - apply LOCFREE2.
  - apply LOCFREE2.
  - apply LOCFREE2.
  - apply LOCFREE2.
  - apply LOCFREE2.
  - pcofix CIH. pfold. rewrite unfold_spin. econs. auto.
Qed.

Lemma loc_free_step_is_accessing_loc
      l e R (itr1 itr2: itree MemE.t R)
      (LOCFREE: loc_free_itree l itr1)
      (STEP: ILang.step (ThreadEvent.get_program_event e) itr1 itr2):
  ~ ThreadEvent.is_accessing_loc l e.
Proof.
  punfold LOCFREE.
  inv STEP; try (by destruct e); ss;
    dependent destruction LOCFREE.
  - destruct e; ss; clarify.
  - destruct e; ss; clarify.
  - destruct e; ss; clarify.
  - destruct e; ss; clarify.
Qed.
