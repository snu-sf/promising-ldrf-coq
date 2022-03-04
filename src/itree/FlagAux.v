Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.
Require Export Program.

Require Import Sequential.


Ltac unfold_flags := unfold Flags.update, Flags.add, Flags.sub, Flags.sub_opt, Flags.meet, Flags.join, Flags.minus in *.
Ltac unfold_many := unfold_flags; unfold ValueMap.write, ValueMap.acquire, Perms.acquired in *.


Section FLAG.

  Lemma flag_join_comm:
    forall f1 f2, Flag.join f1 f2 = Flag.join f2 f1.
  Proof. destruct f1, f2; ss. Qed.

  Lemma flags_join_comm:
    forall f1 f2, Flags.join f1 f2 = Flags.join f2 f1.
  Proof. i. extensionality l. eapply flag_join_comm. Qed.

  Lemma flag_join_assoc:
    forall f1 f2 f3, Flag.join f1 (Flag.join f2 f3) = Flag.join (Flag.join f1 f2) f3.
  Proof. destruct f1, f2, f3; ss. Qed.

  Lemma flags_join_assoc:
    forall f1 f2 f3, Flags.join f1 (Flags.join f2 f3) = Flags.join (Flags.join f1 f2) f3.
  Proof. i. extensionality l. eapply flag_join_assoc. Qed.

  Lemma flag_join_idem:
    forall f, Flag.join f f = f.
  Proof. destruct f; ss. Qed.

  Lemma flags_join_idem:
    forall f, Flags.join f f = f.
  Proof. i. extensionality l. eapply flag_join_idem. Qed.


  Lemma flag_join_bot_l:
    forall f, Flag.join false f = f.
  Proof. refl. Qed.

  Lemma flags_join_bot_l:
    forall f, Flags.join Flags.bot f = f.
  Proof. refl. Qed.

  Lemma flag_join_bot_r:
    forall f, Flag.join f false = f.
  Proof. i. rewrite flag_join_comm. refl. Qed.

  Lemma flags_join_bot_r:
    forall f, Flags.join f Flags.bot = f.
  Proof. i. rewrite flags_join_comm. refl. Qed.


  Lemma flags_join_minus_l:
    forall f0 f1 f2, Flags.le (Flags.minus (Flags.join f1 f2) f0) (Flags.join (Flags.minus f1 f0) f2).
  Proof.
    ii. unfold Flags.minus, Flags.join. destruct (f0 loc); destruct (f1 loc); destruct (f2 loc); ss.
  Qed.

  Lemma flag_le_minus_join:
    forall f0 f1 f2 (LE: Flag.le f0 (Flag.join f1 f2)), Flag.le (Flag.minus f0 f1) f2.
  Proof. ii. destruct f0, f1, f2; ss. Qed.

  Lemma flags_le_minus_join:
    forall f0 f1 f2 (LE: Flags.le f0 (Flags.join f1 f2)), Flags.le (Flags.minus f0 f1) f2.
  Proof. ii. apply flag_le_minus_join. apply LE. Qed.

  Lemma flag_minus_join:
    forall f1 f2, Flag.le f1 (Flag.join (Flag.minus f1 f2) f2).
  Proof. i. destruct f1, f2; ss. Qed.

  Lemma flags_minus_join:
    forall f1 f2, Flags.le f1 (Flags.join (Flags.minus f1 f2) f2).
  Proof. ii. apply flag_minus_join. Qed.

  Lemma flags_le_bot:
    forall f (LE: Flags.le f Flags.bot), f = Flags.bot.
  Proof.
    ii. extensionality l. unfold Flags.le in LE. specialize LE with l. destruct (f l); ss.
  Qed.

End FLAG.
