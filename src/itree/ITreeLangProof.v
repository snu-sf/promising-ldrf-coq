From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
.
Open Scope itree_scope.

Set Implicit Arguments.

From sflib Require Import sflib.

Require Import ITreeLang.



Section Proof.

  (* expr *)
  Lemma denote_expr_var
        x le
    :
      denote_expr le (Inst.expr_var x) = le x.
  Proof. ss. Qed.

  Lemma denote_expr_val
        v le
    :
      denote_expr le (Inst.expr_val v) = v.
  Proof. ss. Qed.

  Lemma denote_expr_op1
        op a le
    :
      denote_expr le (Inst.expr_op1 op a) =
      let ar := denote_expr le a in Op1.eval op ar.
  Proof. ss. Qed.

  Lemma denote_expr_op2
        op a b le
    :
      denote_expr le (Inst.expr_op2 op a b) =
      let ar := denote_expr le a in let br := denote_expr le b in Op2.eval op ar br.
  Proof. ss. Qed.


  (* inst *)
  Lemma denote_inst_skip
        le
    :
      denote_inst le (Inst.skip) = tau;; Ret (le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_assign
        lhs rhs le
    :
      denote_inst le (Inst.assign lhs rhs) =
      let r := denote_expr le rhs in tau;; Ret (update lhs r le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_load
        lhs loc ord le
    :
      denote_inst le (Inst.load lhs loc ord) =
      r <- trigger (MemE.read loc ord);; Ret (update lhs r le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_store
        loc rhs ord le
    :
      denote_inst le (Inst.store loc rhs ord) =
      let r := denote_expr le rhs in trigger (MemE.write loc r ord);; Ret (le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_update
        lhs loc rmw ord1 ord2 le
    :
      denote_inst le (Inst.update lhs loc rmw ord1 ord2) =
      r <- trigger (MemE.update loc rmw ord1 ord2);; Ret (update lhs r le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_fence
        ord1 ord2 le
    :
      denote_inst le (Inst.fence ord1 ord2) =
      trigger (MemE.fence ord1 ord2);; Ret (le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_syscall
        lhs es le
    :
      denote_inst le (Inst.syscall lhs es) =
      let args := denote_exprs le es in r <- trigger (MemE.syscall args);; Ret (update lhs r le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_abort
        le
    :
      denote_inst le (Inst.abort) =
      trigger MemE.abort;; Ret (le, ()).
  Proof. ss. Qed.

  Lemma denote_inst_choose
        lhs le
    :
      denote_inst le (Inst.choose lhs) =
      v <- trigger MemE.choose;; Ret (update lhs v le, ()).
  Proof. ss. Qed.


  (* stmt, block *)
  Lemma denote_stmt_inst
        i le
    :
      denote_stmt le (inst i) =
      denote_inst le i.
  Proof. ss. Qed.

  Lemma denote_block_nil
        le
    :
      denote_block le nil = Ret (le, ()).
  Proof. ss. Qed.

  Lemma denote_block_cons
        s b le
    :
      denote_block le (cons s b) =
      '(le1, _) <- denote_stmt le s;; denote_block le1 b.
  Proof. ss. Qed.

  Lemma denote_add_block
        b1 b2 l0
    :
      denote_block l0 (add_block b1 b2) =
      '(l1, _) <- (denote_block l0 b1);; (denote_block l1 b2).
  Proof.
    do 3 revert1. induction b1 using block_ind2; i.
    - ss. rewrite denote_block_nil. grind.
    - ss. rewrite ! denote_block_cons. grind.
    - ss. rewrite ! denote_block_cons. grind.
    - ss. rewrite ! denote_block_cons. grind.
  Qed.

  Lemma denote_stmt_ite
        c b1 b2 le
    :
      denote_stmt le (ite c b1 b2) =
      let rc := denote_expr le c in
      tau;;
      match is_zero rc with
      | Some true => denote_block le b2
      | Some false => denote_block le b1
      | None => trigger MemE.abort;; Ret (le, ())
      end.
  Proof. ss. Qed.

  Lemma denote_stmt_ite2
        c b1 b2 le
    :
      denote_stmt le (ite c b1 b2) =
      let rc := denote_expr le c in
      match is_zero rc with
      | Some true => denote_block le (cons Inst.skip b2)
      | Some false => denote_block le (cons Inst.skip b1)
      | None => tau;; trigger MemE.abort;; Ret (le, ())
      end.
  Proof.
    rewrite denote_stmt_ite. ss. grind.
  Qed.



  Lemma ext_bind
        E T1 T2 itr1 itr2 (ktr1 ktr2: T1 -> itree E T2)
        (ITR: itr1 = itr2)
        (KTR: forall x, ktr1 x = ktr2 x)
    :
      itr1 >>= ktr1 = itr2 >>= ktr2.
  Proof.
    clarify. ss. f_equal. extensionality x. apply KTR.
  Qed.

  Lemma unfold_denote_while
        c wb le
    :
      denote_stmt le (while c wb) =
      while_itree le
                  (fun lu : lunit =>
                     let le0 := fst lu in
                     let cr := denote_expr le0 c in
                     tau;; match is_zero cr with
                           | Some true => ret (inr (le0, ()))
                           | Some false =>
                             r <- denote_block le0 wb;; ret (inl r)
                           | None => trigger MemE.abort;; Ret (inr (le0, ()))
                           end).
  Proof. ss. Qed.

  Lemma denote_stmt_while
        c wb le
    :
      denote_stmt le (while c wb) =
      x_ <- (let rc := denote_expr le c in
                             tau;;
                             match is_zero rc with
                             | Some true => ret (inr (le, ()))
                             | Some false =>
                               r <- denote_block le wb;; ret (inl r)
                             | None => trigger MemE.abort;; Ret (inr (le, ()))
                             end);;
            (let lr := x_ in
             match lr with
             | inl (le1, _) => tau;; denote_stmt le1 (while c wb)
             | inr r => Ret r
             end).
  Proof.
    ss. rewrite unfold_denote_while.
    unfold while_itree.
    match goal with
    | [|- ITree.iter ?f ?i = _ ] =>
      assert (A: ITree.iter f i ≅ lr <- f i;;
                 match lr with
                 | inl l => tau;; ITree.iter f l
                 | inr r => Ret r
                 end) end.
    { rewrite unfold_iter. eapply eq_is_bisim. grind. }
    apply bisim_is_eq in A. rewrite A; clear A.
    match goal with
    | [|- ?lhs = _ ] =>
      assert (A: lhs =
                 lr <-
                        (tau;; match is_zero (denote_expr le c) with
                               | Some true => ret (inr (le, ()))
                               | Some false =>
                                 r <- denote_block le wb;; ret (inl r)
                               | None => trigger MemE.abort;; Ret (inr (le, ()))
                               end);;
                        match lr with
                        | inl l =>
                          tau;; denote_stmt (fst l) (while c wb)
                        | inr r => Ret r
                        end)
    end.
    { eapply ext_bind; ss.
      i. destruct x; ss. rewrite unfold_denote_while. unfold while_itree. grind.
      f_equal. destruct p. destruct u. ss.
    }
    rewrite A; clear A. eapply ext_bind; eauto.
    i. destruct x; eauto. grind.
  Qed.



  Lemma itr_code_add_block
        b1 b2 l0
    :
      itr_code (add_block b1 b2) l0 =
      '(l1, _) <- (denote_block l0 b1);;
      '(l2, _) <- (denote_block l1 b2);;
      Ret (l2 ret_reg).
  Proof.
    unfold itr_code. rewrite denote_add_block. grind.
  Qed.

  Lemma denote_stmt_block_cons
        s l
    :
      denote_stmt l s = denote_block l (cons s nil).
  Proof.
    rewrite denote_block_cons.
    match goal with
    | [|- ?a = _ ] =>
      replace a with (x <- denote_stmt l s;; Ret x) at 1 end.
    2:{ grind. }
    apply ext_bind; auto.
    grind. destruct u. auto.
  Qed.

  Lemma denote_stmt_while2
        c wb le
    :
      denote_stmt le (while c wb) =
      let rc := denote_expr le c in
      match is_zero rc with
      | Some true => denote_block le (cons Inst.skip nil)
      | Some false => denote_block le (add_block (cons Inst.skip wb) (cons Inst.skip (cons (while c wb) nil)))
      | None => tau;; trigger MemE.abort;; Ret (le, ())
      end.
  Proof.
    rewrite denote_stmt_while.
    Local Opaque denote_stmt.
    Local Opaque denote_block.
    grind.
    { rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind. }
    rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
    rewrite denote_add_block. grind.
    rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
    apply denote_stmt_block_cons.
    Local Transparent denote_block.
    Local Transparent denote_stmt.
  Qed.

  Lemma denote_stmt_while3
        c wb le
    :
      denote_stmt le (while c wb) =
      tau;;
      match is_zero (denote_expr le c) with
      | Some true => denote_block le nil
      | Some false => denote_block le (add_block wb (cons Inst.skip (cons (while c wb) nil)))
      | None => trigger MemE.abort;; Ret (le, ())
      end.
  Proof.
    Local Opaque denote_stmt.
    Local Opaque denote_block.
    rewrite denote_stmt_while2. grind.
    - rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
    - rewrite denote_block_cons. rewrite denote_stmt_inst. rewrite denote_inst_skip. grind.
    Local Transparent denote_block.
    Local Transparent denote_stmt.
  Qed.

End Proof.

Global Opaque denote_expr.
Global Opaque denote_inst.
Global Opaque denote_stmt.
Global Opaque denote_block.
