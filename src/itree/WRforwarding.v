Set Implicit Arguments.

Require Import RelationClasses.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.
From PromisingLib Require Import Axioms.

Require Import Event.

Require Import FoldN.
Require Import Knowledge.

Require Import ITreeLangNotations.
Require Import ITreeLang.





Section DATA.

  Definition Two := option (Const.t * bool).

  Program Instance eq_Equiv: Equivalence (@eq Two).
  Lemma eq_leibniz : forall x y : Two, eq x y -> x = y.
  Proof. auto. Qed.


  Definition meet (t1 t2: Two) : Two :=
    match t1, t2 with
    | Some (c1, b1), Some (c2, b2) =>
      match c1, c2 with
      | Const.undef, Const.undef => Some (c1, orb b1 b2)
      | Const.num n1, Const.num n2 =>
        (if (PeanoNat.Nat.eqb n1 n2) then Some (c1, orb b1 b2) else None)
      | _, _ => None
      end
    | _, _ => None
    end
  .

  Lemma meet_comm: forall t1 t2, meet t1 t2 = meet t2 t1.
  Proof.
    i. unfold meet. des_ifs; ss; clarify.
    - rewrite PeanoNat.Nat.eqb_eq in Heq0. clarify. rewrite Bool.orb_comm. ss.
    - rewrite PeanoNat.Nat.eqb_eq in Heq. rewrite PeanoNat.Nat.eqb_neq in Heq0. clarify.
    - rewrite PeanoNat.Nat.eqb_eq in Heq0. rewrite PeanoNat.Nat.eqb_neq in Heq. clarify.
    - rewrite Bool.orb_comm. ss.
  Qed.

  Lemma meet_assoc: forall t1 t2 t3, meet t1 (meet t2 t3) = meet (meet t1 t2) t3.
  Proof.
    i. unfold meet. des_ifs; ss; clarify.
    - rewrite PeanoNat.Nat.eqb_eq in Heq0. clarify. rewrite Bool.orb_assoc. ss.
    - rewrite PeanoNat.Nat.eqb_eq in Heq0. rewrite PeanoNat.Nat.eqb_eq in Heq1. rewrite PeanoNat.Nat.eqb_neq in Heq2. clarify.
    - rewrite Bool.orb_assoc. ss.
    - rewrite PeanoNat.Nat.eqb_eq in Heq1. rewrite PeanoNat.Nat.eqb_eq in Heq2. rewrite PeanoNat.Nat.eqb_neq in Heq0. clarify.
  Qed.

  Lemma meet_idem: forall t, meet t t = t.
  Proof.
    i. unfold meet. des_ifs; ss; clarify.
    - rewrite Bool.orb_diag. ss.
    - rewrite PeanoNat.Nat.eqb_neq in Heq. clarify.
    - rewrite Bool.orb_diag. ss.
  Qed.



  Definition le (t1 t2: Two) :=
    match t1, t2 with
    | None, _ => True
    | Some (c1, b1), Some (c2, b2) => (c1 = c2) /\ ((b1 = true) \/ (b2 = false))
    | _, _ => False
    end.

  Lemma le_spec: forall t1 t2, le t1 t2 <-> t1 = (meet t1 t2).
  Proof.
    i. unfold le, meet. des_ifs.
    - rewrite PeanoNat.Nat.eqb_eq in Heq. clarify. split; i; des; destruct b0; destruct b; ss; auto.
    - rewrite PeanoNat.Nat.eqb_neq in Heq. split; i; des; exfalso; clarify.
    - split; i; des; exfalso; clarify.
    - split; i; des; exfalso; clarify.
    - split; i; des; destruct b0; destruct b; ss; auto.
  Qed.


  Definition TwoML :=
    @MLattice.mk_mlattice
      Two eq eq_Equiv eq_leibniz
      meet meet_comm meet_assoc meet_idem
      le le_spec.


  Definition bot : Two := None.
  Lemma bot_spec: forall t, le bot t.
  Proof. i. unfold le. des_ifs. Qed.

End DATA.





Section ANALYSIS.

  (**
  Simple constant write-read forwarding:

  x = c (write na); ... r = x (read na);
  ->
  x = c (write na); ... r = c (assign);

  Ordering:
  for insts in ...,

                      WR
  na               :  O
  rel(at write)    :  O
  acq(at read)     :  O
  rel-acq          :  X
  syscall          :  X

   **)

  Definition Two_new (c: Const.t) := Some (c, false).
  Definition Two_set_flag (t: Two) :=
    match t with
    | Some (c, _) => Some (c, true)
    | None => None
    end.
  Definition Two_elim (t: Two) :=
    match t with
    | Some (_, false) => t
    | _ => None
    end.



  Definition distl {T} l1 l2 (v1 v2: T) := if (Loc.eqb l1 l2) then v1 else v2.

  Definition WRfwd_read (ul: Loc.t) o : Loc.t -> (local_update Two) :=
    fun l t =>
      if (Ordering.le o Ordering.na)
      then t
      else
        if (Ordering.le o Ordering.strong_relaxed)
        then (distl ul l None t)
        else
          (distl ul l None (Two_elim t)).

  Definition WRfwd_write (ul: Loc.t) o : Loc.t -> (local_update Two) :=
    fun l t =>
      if (Ordering.le o Ordering.relaxed)
      then (distl ul l None t)
      else
        (distl ul l None (Two_set_flag t)).

  Definition WRfwd_store (ul: Loc.t) e o : Loc.t -> (local_update Two) :=
    fun l t =>
      if (Ordering.le o Ordering.na)
      then (distl ul l
                  (match e with
                   | Inst.expr_val c => Two_new c
                   | _ => None
                   end) t)
      else
        ((WRfwd_write ul o) l t).


  Definition WRfwd_fence_r o : Loc.t -> (local_update Two) :=
    fun _ t =>
      if (Ordering.le o Ordering.strong_relaxed)
      then t
      else Two_elim t.

  Definition WRfwd_fence_w o : Loc.t -> (local_update Two) :=
    fun _ t =>
      if (Ordering.le o Ordering.relaxed)
      then t
      else
        if (Ordering.le o Ordering.acqrel)
        then (Two_set_flag t)
        else (Two_set_flag (Two_elim t)).

  Definition WRfwd_inst (i: Inst.t) : Loc.t -> Two -> Two :=
    fun l t =>
      match i with
      | Inst.skip => t
      | Inst.assign x e => t

      | Inst.load _ ul o => (WRfwd_read ul o) l t
      | Inst.store ul e o => (WRfwd_store ul e o) l t

      (* same as read + write *)
      | Inst.update _ ul rmw or ow =>
        let ut0 := (WRfwd_read ul or) l t in
        let ut1 := (WRfwd_write ul ow) l ut0 in
        ut1

      | Inst.fence or ow =>
        let ut0 := (WRfwd_fence_r or) l t in
        let ut1 := (WRfwd_fence_w ow) l ut0 in
        ut1

      | Inst.syscall x es => None
      | Inst.abort => t
      | Inst.choose _ => t
      end
  .

  Definition N : nat := 2.

  Fixpoint WRfwd_block (b: block): Loc.t -> (local_update Two) :=
    fun p d =>
      match b with
      | nil => d
      | cons hd tl =>
        match hd with
        | inst i =>
          let d0 := WRfwd_inst i p d in
          WRfwd_block tl p d0

        | ite _ b1 b2 =>
          let d1 := WRfwd_block b1 p d in
          let d2 := WRfwd_block b2 p d in
          let d3 := meet d1 d2 in
          WRfwd_block tl p d3

        | while _ wb =>
          let f := (WRfwd_block wb p) in
          let fp := fold_n f (S N) in
          let d0 := meet d (fp d) in
          WRfwd_block tl p d0
        end
      end.

End ANALYSIS.





Section ALG.

  Definition WRfwd_opt_inst (mp: Data Two Loc.t) (i: Inst.t) : Inst.t :=
    match i with
    | Inst.load x l o =>
      match (mp l), o with
      | Some (c, _), Ordering.na => (Inst.assign x (Inst.expr_val c))
      | _, _ => i
      end
    | _ => i
    end
  .


  Let GD := GD Two Loc.t.
  Let inst_gd (i: Inst.t) : GD -> GD := mk_global (WRfwd_inst i).
  Let block_gd (b: block): GD -> GD := mk_global (WRfwd_block b).
  Let meet2 : GD -> GD -> GD := fun gd1 gd2 => (fun p => meet (gd1 p) (gd2 p)).

  Fixpoint WRfwd_opt_block (data: GD) (blk: block) : GD * block :=
    match blk with
    | nil => (data, blk)
    | cons hd tl =>
      match hd with
      | inst i =>
        let i1 := WRfwd_opt_inst data i in
        let data1 := inst_gd i data in
        let '(data2, tl1) := WRfwd_opt_block data1 tl in
        (data2, cons i1 tl1)

      | ite cond blk1 blk2 =>
        let '(data1, ublk1) := WRfwd_opt_block data blk1 in
        let '(data2, ublk2) := WRfwd_opt_block data blk2 in
        let data3 := meet2 data1 data2 in
        let '(data4, tl1) := WRfwd_opt_block data3 tl in
        (data4, cons (ite cond ublk1 ublk2) tl1)

      | while cond wb =>
        let f := (block_gd wb) in
        let fp := fold_n f (S N) in
        let data1 := meet2 data (fp data) in
        let '(_, wb1) := WRfwd_opt_block data1 wb in
        let '(data2, tl1) := WRfwd_opt_block data1 tl in
        (data2, cons (while cond wb1) tl1)

      end
    end.



  Let bot2 : GD := fun _ => bot.

  Definition WRfwd_opt_alg : block -> block :=
    fun code => snd (WRfwd_opt_block bot2 code).

End ALG.





Section Test.

  Import ITreeLangNotations.
  Import BinNums.

  Local Open Scope expr_scope.
  Local Open Scope inst_scope.
  Local Open Scope stmt_scope.
  Local Open Scope block_scope.

  Definition loc1 : Loc.t := xH.
  Definition loc2 : Loc.t := xO xH.
  Definition loc3 : Loc.t := xI xH.

  Definition x : Ident.t := xH.
  Definition y : Ident.t := xO xH.
  Definition z : Ident.t := xI xH.
  Definition a : Ident.t := xO (xO xH).

  Definition test0 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      x =# (1: Const.t);
      y =#* loc1 Ordering.na
    }
  .
  Definition test0' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      x =# (1: Const.t);
      y =# (5: Const.t)
    }
  .
  Goal (WRfwd_opt_alg test0) = test0'.
  Proof. ss. Qed.

  Definition test1 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
        y =#* loc1 Ordering.na
      }
      end#
    }
  .
  Definition test1' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
        y =# (5: Const.t)
      }
      end#
    }
  .
  Goal (WRfwd_opt_alg test1) = test1'.
  Proof. ss. Qed.

  Definition test2 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
        y =#* loc1 Ordering.na;
        loc1 *=# (3: Const.t) Ordering.na
      }
      end#
    }
  .
  Definition test2' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      { x =# (1: Const.t);
        y =#* loc1 Ordering.na;
        loc1 *=# (3: Const.t) Ordering.na
      }
      end#
    }
  .
  Goal (WRfwd_opt_alg test2) = test2'.
  Proof. ss. Qed.

  Definition test3 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        x =# (1: Const.t);
        y =#* loc1 Ordering.na
      }
      end#;
      z =#* loc1 Ordering.na
    }
  .
  Definition test3' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      while# (1: Const.t) do#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        x =# (1: Const.t);
        y =# (3: Const.t)
      }
      end#;
      z =#* loc1 Ordering.na
    }
  .
  Goal (WRfwd_opt_alg test3) = test3'.
  Proof. ss. Qed.


  Definition test4 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      loc2 *=# (1: Const.t) Ordering.acqrel;
      x =# (1: Const.t);
      y =#* loc1 Ordering.na
    }
  .
  Definition test4' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      loc2 *=# (1: Const.t) Ordering.acqrel;
      x =# (1: Const.t);
      y =# (5: Const.t)
    }
  .
  Goal (WRfwd_opt_alg test4) = test4'.
  Proof. ss. Qed.

  Definition test5 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      loc2 *=# (1: Const.t) Ordering.acqrel;
      x =# (1: Const.t);
      a =#* loc2 Ordering.acqrel;
      y =#* loc1 Ordering.na
    }
  .
  Definition test5' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      loc2 *=# (1: Const.t) Ordering.acqrel;
      x =# (1: Const.t);
      a =#* loc2 Ordering.acqrel;
      y =#* loc1 Ordering.na
    }
  .
  Goal (WRfwd_opt_alg test5) = test5'.
  Proof. ss. Qed.

  Definition test6 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      if# (1: Const.t)
      then#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        loc1 *=# (5: Const.t) Ordering.na;
        loc2 *=# (1: Const.t) Ordering.acqrel;
        x =# (1: Const.t)
      }
      else#
      {
        x =# (0: Const.t);
      }
      fi#;
      y =#* loc1 Ordering.na
    }
  .
  Definition test6' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      if# (1: Const.t)
      then#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        loc1 *=# (5: Const.t) Ordering.na;
        loc2 *=# (1: Const.t) Ordering.acqrel;
        x =# (1: Const.t)
      }
      else#
      {
        x =# (0: Const.t);
      }
      fi#;
      y =# (5: Const.t)
    }
  .
  Goal (WRfwd_opt_alg test6) = test6'.
  Proof. ss. Qed.

  Definition test7 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      if# (1: Const.t)
      then#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        loc2 *=# (1: Const.t) Ordering.acqrel;
        x =# (1: Const.t)
      }
      else#
      {
        x =# (0: Const.t);
      }
      fi#;
      y =#* loc1 Ordering.na
    }
  .
  Definition test7' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      if# (1: Const.t)
      then#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        loc2 *=# (1: Const.t) Ordering.acqrel;
        x =# (1: Const.t)
      }
      else#
      {
        x =# (0: Const.t);
      }
      fi#;
      y =#* loc1 Ordering.na
    }
  .
  Goal (WRfwd_opt_alg test7) = test7'.
  Proof. ss. Qed.

  Definition test8 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      if# (1: Const.t)
      then#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        loc1 *=# (5: Const.t) Ordering.na;
        loc2 *=# (1: Const.t) Ordering.acqrel;
        x =# (1: Const.t);
        a =#* loc2 Ordering.acqrel
      }
      else#
      {
        x =# (0: Const.t);
      }
      fi#;
      y =#* loc1 Ordering.na
    }
  .
  Definition test8' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      if# (1: Const.t)
      then#
      {
        loc1 *=# (3: Const.t) Ordering.na;
        loc1 *=# (5: Const.t) Ordering.na;
        loc2 *=# (1: Const.t) Ordering.acqrel;
        x =# (1: Const.t);
        a =#* loc2 Ordering.acqrel
      }
      else#
      {
        x =# (0: Const.t);
      }
      fi#;
      y =#* loc1 Ordering.na
    }
  .
  Goal (WRfwd_opt_alg test8) = test8'.
  Proof. ss. Qed.


  Definition test9 : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      loc2 *=# (1: Const.t) Ordering.acqrel;
      loc3 *=# (7: Const.t) Ordering.na;
      x =# (1: Const.t);
      a =#* loc2 Ordering.acqrel;
      y =#* loc1 Ordering.na;
      z =#* loc3 Ordering.na
    }
  .
  Definition test9' : block :=
    { loc1 *=# (5: Const.t) Ordering.na;
      loc2 *=# (1: Const.t) Ordering.acqrel;
      loc3 *=# (7: Const.t) Ordering.na;
      x =# (1: Const.t);
      a =#* loc2 Ordering.acqrel;
      y =#* loc1 Ordering.na;
      z =# (7: Const.t)
    }
  .
  Goal (WRfwd_opt_alg test9) = test9'.
  Proof. ss. Qed.

End Test.
