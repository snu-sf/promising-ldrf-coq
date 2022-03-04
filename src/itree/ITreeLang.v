From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
From ExtLib Require Export
     Functor FunctorLaws
     Structures.Maps
.

Export SumNotations.
Export ITreeNotations.
Export Monads.
Export MonadNotation.
Export FunctorNotation.
Export CatNotations.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Require Import RelationClasses.

From sflib Require Import sflib.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.
From PromisingLib Require Import Language.

From PromisingLib Require Import Event.
Require Export ITreeLib.
Require Export Program.

Set Implicit Arguments.


Module MemE.
  Variant rmw :=
  | fetch_add (addendum:Const.t)
  | cas (old new:Const.t)
  .

  Variant t: Type -> Type :=
  | read (loc: Loc.t) (ord: Ordering.t): t Const.t
  | write (loc: Loc.t) (val: Const.t) (ord: Ordering.t): t unit
  | update (loc: Loc.t) (rmw:rmw) (ordr ordw: Ordering.t): t Const.t
  | fence (ordr ordw: Ordering.t): t unit
  | syscall (args: list Const.t): t Const.t
  | abort: t void
  | choose: t Const.t
  .

  Variant ord: forall R (i_src i_tgt:t R), Prop :=
  | ord_read
      l o1 o2 (O: Ordering.le o1 o2):
      ord (read l o1) (read l o2)
  | ord_write
      l v o1 o2 (O: Ordering.le o1 o2):
      ord (write l v o1) (write l v o2)
  | ord_update
      l rmw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (update l rmw or1 ow1) (update l rmw or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (fence or1 ow1) (fence or2 ow2)
  | ord_syscall
      args:
      ord (syscall args) (syscall args)
  | ord_abort:
      ord abort abort
  | ord_choose:
      ord choose choose
  .
End MemE.


Module ILang.
  Variant eval_rmw: forall (rmw:MemE.rmw) (valr:Const.t) (valret: Const.t) (valw: option Const.t), Prop :=
  | eval_rmw_fetch_add
      addendum valr valret valw
      (VALRET: valret = Const.add valr addendum)
      (VALW: valw = Some (Const.add valr addendum)):
      eval_rmw (MemE.fetch_add addendum) valr valret valw
  | eval_rmw_cas_success
      o n valr valret valw
      (CMP: Const.eqb o valr <> Some false)
      (VALRET: valret = Const.one)
      (VALW: valw = Some n):
      eval_rmw (MemE.cas o n) valr valret valw
  | eval_rmw_cas_fail
      o n valr valret valw
      (CMP: Const.eqb o valr <> Some true)
      (VALRET: valret = Const.zero)
      (VALW: valw = None):
      eval_rmw (MemE.cas o n) valr valret valw
  .
  #[export] Hint Constructors eval_rmw.

  Definition is_terminal R (s: itree MemE.t R): Prop :=
    exists r, s = Ret r.

  Inductive step R:
    forall (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | step_tau
      (itr: itree MemE.t R)
      itr1 (EQ: itr1 = itr)
    :
      @step R ProgramEvent.silent
            (Tau itr)
            itr1
  | step_choose
      (k: Const.t -> itree MemE.t R) val
      itr1 (EQ: itr1 = k val)
    :
      @step R ProgramEvent.silent
            (Vis (MemE.choose) k)
            itr1
  | step_read
      (k: Const.t -> itree MemE.t R) loc val ord
      itr1 (EQ: itr1 = k val)
    :
      @step R (ProgramEvent.read loc val ord)
            (Vis (MemE.read loc ord) k)
            itr1
  | step_write
      (k: unit -> itree MemE.t R) loc val ord
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.write loc val ord)
            (Vis (MemE.write loc val ord) k)
            itr1
  | step_update_success
      (k: Const.t -> itree MemE.t R) loc rmw valr valw valret ordr ordw
      (RMW: eval_rmw rmw valr valret (Some valw))
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.update loc valr valw ordr ordw)
            (Vis (MemE.update loc rmw ordr ordw) k)
            itr1
  | step_update_failure
      (k: Const.t -> itree MemE.t R) loc rmw valr valret ordr ordw
      (RMW: eval_rmw rmw valr valret None)
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.read loc valr ordr)
            (Vis (MemE.update loc rmw ordr ordw) k)
            itr1
  | step_fence
      (k: unit -> itree MemE.t R) ordr ordw
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.fence ordr ordw)
            (Vis (MemE.fence ordr ordw) k)
            itr1
  | step_syscall
      (k: Const.t -> itree MemE.t R) valret args
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.syscall (Event.mk valret args))
            (Vis (MemE.syscall args) k)
            itr1
  | step_abort
      (k: void -> itree MemE.t R)
    :
      @step R (ProgramEvent.failure)
            (Vis (MemE.abort) k)
            ITree.spin
  .
  #[export] Hint Constructors step: core.

  Inductive opt_step R:
    forall (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | opt_step_none
      (st: itree MemE.t R):
      opt_step ProgramEvent.silent st st
  | opt_step_some
      e (st1 st2: itree MemE.t R)
      (STEP: step e st1 st2):
      opt_step e st1 st2
  .
End ILang.

Definition lang (R: Type): Language.t ProgramEvent.t :=
  @Language.mk
    _
    (itree MemE.t R)
    (itree MemE.t R)
    id
    (@ILang.is_terminal _)
    (@ILang.step _)
.

From Paco Require Import paco.

Lemma bind_spin E A B (k: ktree E A B):
  ITree.spin >>= k = ITree.spin.
Proof.
  apply bisim_is_eq. revert k. pcofix CIH.
  i. pfold. red.
  change (observe (ITree.spin: itree E B)) with (@TauF E B _ (ITree.spin: itree E B)).
  change (observe (ITree.spin >>= k)) with (@TauF E B _ (ITree.spin >>= k)).
  econs. right. auto.
Qed.

Lemma unfold_spin E R
  :
    (ITree.spin: itree E R) = tau;;ITree.spin.
Proof.
  apply bisim_is_eq. ginit. gstep. red. ss.
  change (observe ITree.spin) with (@TauF E R _ (ITree.spin: itree E R)).
  refl.
Qed.

Lemma lang_step_deseq
      R0 R1 ktr (itr1: itree MemE.t R0) (itr2: itree MemE.t R1) e
      (STEP: ILang.step e
                        (itr1 >>= ktr)
                        itr2):
  (exists r,
      itr1 = Ret r /\
      ILang.step e (ktr r) itr2) \/
  (exists itr2',
      itr2 = itr2' >>= ktr /\
      ILang.step e itr1 itr2') \/
  (itr1 = Vis MemE.abort (Empty_set_rect _) /\
   e = ProgramEvent.failure)
.
Proof.
  ides itr1.
  { rewrite bind_ret_l in STEP. left. esplits; eauto. }
  { rewrite bind_tau in STEP. dependent destruction STEP.
    right. left. esplits; eauto. econs. eauto. }
  { rewrite bind_vis in STEP.
    dependent destruction STEP; try by (right; left; esplits; eauto; econs; eauto).
    right. right. splits; auto. f_equal. f_equal. extensionality v. ss. }
Qed.

Lemma unfold_iter_eq {E} {A B} (f: A -> itree E (A + B)) (a: A)
  :
    ITree.iter f a
    = lr <- f a;;
      match lr with
      | inl l => tau;; ITree.iter f l
      | inr r => Ret r
      end.
Proof.
  eapply bisimulation_is_eq. eapply unfold_iter.
Qed.







Module Op1.
  Inductive t :=
  | not
  .

  Definition eval (op:t) (op1:Const.t): Const.t :=
    match op with
    | not =>
      match (Const.eqb op1 Const.zero) with
      | None => Const.undef
      | Some b =>
        if b then Const.one else Const.zero
      end
    end.

End Op1.


Module Op2.
  Inductive t :=
  | add
  | sub
  | mul
  | eq
  .

  Definition const_eq (op1 op2: Const.t): Const.t :=
    match (Const.eqb op1 op2) with
    | None => Const.undef
    | Some b =>
      if b then Const.one else Const.zero
    end.

  Definition eval (op:t): forall (op1 op2:Const.t), Const.t :=
    match op with
    | add => Const.add
    | sub => Const.sub
    | mul => Const.mul
    | eq => const_eq
    end.

End Op2.


Module Inst.
  Inductive expr :=
  | expr_var (var:Ident.t)
  | expr_val (val:Const.t)
  | expr_op1 (op:Op1.t) (op:expr)
  | expr_op2 (op:Op2.t) (op1 op2:expr)
  .

  Variant t :=
  | skip
  | assign (lhs:Ident.t) (rhs:expr)
  | load (lhs:Ident.t) (rhs:Loc.t) (ord:Ordering.t)
  | store (lhs:Loc.t) (rhs:expr) (ord:Ordering.t)
  | update (lhs:Ident.t) (loc:Loc.t) (rmw:MemE.rmw) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (lhs:Ident.t) (rhses:list expr)
  | abort
  | choose (lhs:Ident.t)
  .

End Inst.
Coercion Inst.expr_val: Const.t >-> Inst.expr.
Coercion Inst.expr_var: Ident.t >-> Inst.expr.


Section Stmt.

  Inductive stmt :=
  | inst (i:Inst.t)
  | ite (cond:Inst.expr) (c1 c2:block)
  | while (cond:Inst.expr) (c:block)
  with block :=
  | nil
  | cons (hd:stmt) (tl:block)
  .

  Lemma block_ind2
        (P: block -> Prop)
        (NIL: P nil)
        (INST: forall hd tl, P tl -> P (cons (inst hd) tl))
        (ITE: forall c b1 b2 tl, P b1 -> P b2 -> P tl -> P (cons (ite c b1 b2) tl))
        (WHILE: forall c b tl, P b -> P tl -> P (cons (while c b) tl))
    :
      forall blk, P blk.
  Proof.
    fix IH 1.
    i. destruct blk.
    { auto. }
    destruct hd.
    - eapply INST. eauto.
    - eapply ITE; eauto.
    - eapply WHILE; eauto.
  Qed.

  Fixpoint add_block (b1 b2: block) : block :=
    match b1 with
    | nil => b2
    | cons hd tl => cons hd (add_block tl b2)
    end
  .

  Lemma add_block_assoc :
    forall a b c, (add_block (add_block a b) c) = add_block a (add_block b c).
  Proof.
    induction a; i; ss; clarify. f_equal. ss.
  Qed.

  Lemma cons_add_block_comm :
    forall hd a b, add_block (cons hd a) b = cons hd (add_block a b).
  Proof.
    induction a; i; ss; clarify.
  Qed.

  Lemma add_block_nil_unit:
    forall b, add_block nil b = b.
  Proof. ss. Qed.

  Lemma add_block_nil_unit_r:
    forall b, add_block b nil = b.
  Proof.
    induction b using block_ind2; ss; clarify.
    - rewrite IHb. ss.
    - rewrite IHb3. ss.
    - rewrite IHb2. ss.
  Qed.

  Lemma cons_to_add_block:
    forall a b, cons a b = add_block (cons a nil) b.
  Proof. ss. Qed.

  Lemma cons_add_block_comm_tail:
    forall hd a b, add_block a (cons hd b) = add_block (add_block a (cons hd nil)) b.
  Proof.
    i. rewrite add_block_assoc. rewrite <- cons_to_add_block. auto.
  Qed.

  Lemma add_block_nil_nil:
    forall a b (ADD: add_block a b = nil), (a = nil) /\ (b = nil).
  Proof.
    induction a; i; ss.
  Qed.

  Lemma add_block_inv_head0:
    forall a1 a2 hd (HEAD: add_block a1 (cons hd nil) = add_block a2 (cons hd nil)), a1 = a2.
  Proof.
    induction a1; i; ss.
    { destruct a2; ss. inv HEAD. exfalso. symmetry in H1. apply add_block_nil_nil in H1.
      des. clarify.
    }
    destruct a2; ss.
    { inv HEAD. apply add_block_nil_nil in H1. des; clarify. }
    inv HEAD. f_equal. eauto.
  Qed.

  Lemma add_block_inv_head0':
    forall a1 a2 hd1 hd2 (HEAD: add_block a1 (cons hd1 nil) = add_block a2 (cons hd2 nil)),
      (a1 = a2) /\ (hd1 = hd2).
  Proof.
    induction a1; i; ss.
    { destruct a2; ss.
      { inv HEAD. auto. }
      inv HEAD. exfalso. symmetry in H1. apply add_block_nil_nil in H1.
      des. clarify.
    }
    destruct a2; ss.
    { inv HEAD. apply add_block_nil_nil in H1. des; clarify. }
    inv HEAD. hexploit IHa1; eauto. i. des. split; eauto. f_equal. eauto.
  Qed.

  Lemma add_block_inv_head:
    forall b a1 a2 (HEAD: add_block a1 b = add_block a2 b), a1 = a2.
  Proof.
    induction b; i; ss.
    { rewrite ! add_block_nil_unit_r in HEAD. auto. }
    setoid_rewrite cons_add_block_comm_tail in HEAD.
    eapply IHb in HEAD. eapply add_block_inv_head0; eauto.
  Qed.

  Lemma add_block_head_nil:
    forall a b (HEAD: add_block a b = b), a = nil.
  Proof.
    i. rewrite <- add_block_nil_unit in HEAD. apply add_block_inv_head in HEAD. auto.
  Qed.

  Lemma add_block_head_nil_cons:
    forall a b hd1 hd2 (HEAD: add_block a (cons hd1 b) = cons hd2 b), (a = nil) /\ (hd1 = hd2).
  Proof.
    i. rewrite <- add_block_nil_unit in HEAD.
    setoid_rewrite cons_add_block_comm_tail in HEAD. apply add_block_inv_head in HEAD.
    apply add_block_inv_head0' in HEAD. auto.
  Qed.

End Stmt.
Coercion inst: Inst.t >-> stmt.





Section LocalEnv.

  Definition lenv := Ident.t -> Const.t.
  Definition init_le : lenv := fun _ => Const.undef.

  Definition update (k: Ident.t) (v: Const.t) (le: lenv) : lenv :=
    fun i => if (Ident.eqb k i) then v else (le i).

End LocalEnv.



Section Denote.

  (** Denotation of expressions *)
  Fixpoint denote_expr (le: lenv) (e : Inst.expr) : Const.t :=
    match e with
    | Inst.expr_var x => (le x)
    | Inst.expr_val v => v
    | Inst.expr_op1 op a =>
      let ar := denote_expr le a in (Op1.eval op ar)
    | Inst.expr_op2 op a b =>
      let ar := denote_expr le a in
      let br := denote_expr le b in
      (Op2.eval op ar br)
    end
  .

  Definition denote_exprs (le: lenv) (es : list Inst.expr) : list Const.t :=
    List.map (denote_expr le) es.

  Context {eff : Type -> Type}.
  Context {HasMemE : MemE.t -< eff}.

  Definition lunit := (prod lenv unit).

  (** Denotation of instructions *)
  Definition denote_inst (le: lenv) (i : Inst.t) : itree eff lunit :=
    match i with
    | Inst.skip =>
      tau;; Ret (le, tt)

    | Inst.assign lhs rhs =>
      let r := denote_expr le rhs in
      tau;; Ret (update lhs r le, tt)

    | Inst.load lhs loc ord =>
      r <- trigger (MemE.read loc ord);;
      Ret (update lhs r le, tt)

    | Inst.store loc rhs ord =>
      let r := denote_expr le rhs in
      trigger (MemE.write loc r ord);; Ret (le, tt)

    | Inst.update lhs loc rmw ord1 ord2 =>
      r <- trigger (MemE.update loc rmw ord1 ord2);;
      Ret (update lhs r le, tt)

    | Inst.fence ord1 ord2 =>
      trigger (MemE.fence ord1 ord2);; Ret (le, tt)

    | Inst.syscall lhs es =>
      let args := denote_exprs le es in
      r <- trigger (MemE.syscall args);; Ret (update lhs r le, tt)

    | Inst.abort =>
      trigger (MemE.abort);; Ret (le, tt)

    | Inst.choose lhs =>
      v <- trigger (MemE.choose);;
      Ret (update lhs v le, tt)

    end
  .

  (** Denotation of statements *)
  Definition is_zero (v : Const.t) : option bool :=
    Const.eqb v Const.zero.

  Definition while_itree (le: lenv) (step: lunit -> itree eff (lunit + lunit)) : itree eff lunit :=
    ITree.iter step (le, tt).

  Fixpoint denote_stmt (le: lenv) (s : stmt) : itree eff lunit :=
    match s with
    | inst i => denote_inst le i

    | ite cond sif selse =>
      let cr := denote_expr le cond in
      let ift := denote_block le sif in
      let elset := denote_block le selse in
      tau;;
      (match (is_zero cr) with
       | None => trigger (MemE.abort);; Ret (le, tt)
       | Some b => if b then elset else ift
       end)

    | while cond swhile =>
      while_itree
        le
        (fun lu =>
           let le0 := fst lu in
           let cr := denote_expr le0 cond in
           tau;;
           (match (is_zero cr) with
            | None => trigger (MemE.abort);; Ret (inr (le0, tt))
            | Some b => if b
                       then ret (inr (le0, tt))
                       else r <- denote_block le0 swhile;; ret (inl r)
            end))

    end
  with denote_block (le: lenv) (b: block) : itree eff lunit :=
         match b with
         | nil => Ret (le, tt)
         | cons s blk => '(le1, _) <- denote_stmt le s;; denote_block le1 blk
         end
  .

End Denote.

Section Interp.

  Definition ret_reg : Ident.t := BinNums.xH.

  Definition effs := MemE.t.

  Definition itr_code (blk: block) (le: lenv) :=
    '(le1, _) <- (denote_block le blk);; Ret (le1 ret_reg).

  Definition eval_lang (body: block) : itree MemE.t Const.t :=
    '(le1, _) <- (denote_block init_le body);; Ret (le1 ret_reg).

End Interp.
