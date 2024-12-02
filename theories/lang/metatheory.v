From dlfactris.lang Require Export lang.

Ltac inv H := inversion H; clear H; simplify_eq.

Lemma pure_step_not_val e1 e2 :
  pure_step e1 e2 → to_val e1 = None.
Proof. by intros []. Qed.

Lemma to_val_ctx_None k e :
  ctx k → to_val e = None → to_val (k e) = None.
Proof. intros Hctx. revert e. induction Hctx as [|?? []]; eauto. Qed.

Lemma head_step_not_val e1 h1 e2 h2 es_new :
  head_step e1 h1 e2 h2 es_new → to_val e1 = None.
Proof. intros []; eauto using pure_step_not_val. Qed.

Lemma prim_step_not_val e1 h1 e2 h2 es_new :
  prim_step e1 h1 e2 h2 es_new → to_val e1 = None.
Proof. intros []; eauto using to_val_ctx_None, head_step_not_val. Qed.

Lemma head_step_prim_step e1 h1 e2 h2 es_new :
  head_step e1 h1 e2 h2 es_new → prim_step e1 h1 e2 h2 es_new.
Proof. intros. apply (Prim_step id); eauto using ctx. Qed.

Lemma head_step_reducible_or_blocked e1 h1 e2 h2 es_new :
  head_step e1 h1 e2 h2 es_new → reducible_or_blocked e1 h1.
Proof. left. eexists. eauto using head_step_prim_step. Qed.

Lemma pure_step_reducible_or_blocked e1 e2 h :
  pure_step e1 e2 → reducible_or_blocked e1 h.
Proof. eauto using head_step_reducible_or_blocked, head_step. Qed.

Lemma pure_step_no_ctx1 k e1 e2 :
  ctx1 k → pure_step (k e1) e2 → is_Some (to_val e1).
Proof. intros [] He1; inv He1; eauto. Qed.

Lemma to_val_ctx_is_Some_id k e :
  ctx k → is_Some (to_val (k e)) → k = id.
Proof. induction 1 as [|?? []]; intros [??]; naive_solver. Qed.

Lemma ctx_Val k e v :
  ctx k → k e = Val v → e = Val v.
Proof.
  intros ? Hke. assert (k = id) as ->; [|done].
  apply (to_val_ctx_is_Some_id _ e); by rewrite ?Hke.
Qed.

Lemma to_val_ctx_is_Some k e :
  ctx k → is_Some (to_val (k e)) → is_Some (to_val e).
Proof. intros. by assert (k = id) as -> by eauto using to_val_ctx_is_Some_id. Qed.

Lemma pure_step_no_ctx k e1 e2 :
  ctx k → pure_step (k e1) e2 → is_Some (to_val e1) ∨ k = id.
Proof. induction 1; eauto using to_val_ctx_is_Some, pure_step_no_ctx1. Qed.

Lemma pure_step_head_step e1 e2 e2' h h' es_new :
  pure_step e1 e2 →
  head_step e1 h e2' h' es_new →
  e2 = e2' ∧ h = h' ∧ es_new = [].
Proof.
  intros [] He2'; inv He2';
    match goal with H : pure_step _ _ |- _ => inv H end; auto.
Qed.

Lemma pure_step_prim_step e1 e2 e2' h h' es_new :
  pure_step e1 e2 →
  prim_step e1 h e2' h' es_new →
  e2 = e2' ∧ h = h' ∧ es_new = [].
Proof.
  intros Hpure Hprim; destruct Hprim as [k e1'' e2''].
  destruct (pure_step_no_ctx k e1'' e2) as [[]%not_eq_None_Some| ->];
    eauto using head_step_not_val, pure_step_head_step.
Qed.

Lemma ctx_compose k1 k2 :
  ctx k1 → ctx k2 → ctx (k1 ∘ k2).
Proof.
  intros Hk1 Hk2. induction Hk1 as [|k1 k1']; [done|].
  by apply (Ctx_compose k1).
Qed.

Lemma prim_step_ctx k e1 h1 e2 h2 es_new :
  ctx k →
  prim_step e1 h1 e2 h2 es_new →
  prim_step (k e1) h1 (k e2) h2 es_new.
Proof.
  intros Hctx Hprim. destruct Hprim as [k' e1' e2'].
  apply (Prim_step (k ∘ k')); eauto using ctx_compose.
Qed.

Lemma reducible_ctx k e h :
  ctx k → reducible e h → reducible (k e) h.
Proof.
  intros Hctx (e' & h' & es_new & ?).
  exists (k e'), h', es_new; eauto using prim_step_ctx.
Qed.

Lemma blocked_ctx k e l h :
  ctx k → blocked e l h → blocked (k e) l h.
Proof.
  intros Hctx (k' & e' & ? & -> & ?).
  exists (k ∘ k'); eauto using ctx_compose.
Qed.

Lemma blocked_chan_unique h l l' k :
  ctx k →
  blocked (k (Recv (Val (LitV (LitLoc l))))) l' h → l = l'.
Proof.
  intros Hctx (k' & e' & Hctx' & Heq & Hbl). destruct Hbl as [_ l' _].
  revert k' Heq Hctx'. induction Hctx; induction 2;
    repeat match goal with
    | _ => progress simplify_eq/=
    | H : ctx1 _ |- _ => destruct H
    | Hk : ctx ?k, H : Val _ = ?k _ |- _ => symmetry in H; apply (ctx_Val _ _ _ Hk) in H
    | Hk : ctx ?k, H : ?k _ = Val _ |- _ => apply (ctx_Val _ _ _ Hk) in H
    end; eauto.
Qed.

Definition sub_exprs : expr → list expr :=
  fix go e :=
    e :: match e with
         | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Send e1 e2 | Store e1 e2 =>
           if decide (is_Some (to_val e2)) then go e1 ++ go e2 else go e2
         | UnOp _ e | If e _ _ | LetPair e _ | Sum _ e  | MatchSum e _
                    | ForkChan e | Recv e | Alloc e | Free e | Load e=> go e
         | _ => []
         end.

Lemma to_val_Val e v : to_val e = Some v ↔ e = Val v.
Proof. split; [|by intros ->]. destruct e; naive_solver. Qed.

Lemma sub_exprs_spec e' e : e' ∈ sub_exprs e ↔ ∃ k, ctx k ∧ e = k e'.
Proof.
  split.
  - revert e'. induction e; intros e' ?;
      repeat match goal with
      | _ => progress simplify_eq/=
      | _ => case_decide
      | H : _ ∈ [] |- _ => apply elem_of_nil in H as []
      | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H as []
      | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H as []
      | H : is_Some (to_val _) |- _ => destruct H as [v ->%to_val_Val]
      | H : _ ∈ _, IH : ∀ _, _ ∈ _ → _ |- _ => apply IH in H as (?&?&?)
      end; eauto 4 using ctx, ctx1.
  - intros (k&Hk&->). induction Hk as [|k1 k Hk1 Hk IH]; simpl.
    { destruct e'; set_solver. }
    destruct Hk1; simpl; repeat case_decide; set_solver.
Qed.

Global Instance head_blocked_dec e l h : Decision (head_blocked e l h).
Proof.
  refine
    match e with
    | Recv (Val (LitV (LitLoc l'))) =>
       cast_if_and (decide (l = l')) (decide (h !! l = Some (ChanHV None)))
    | _ => right _
    end; try first [inversion 1; naive_solver|by subst; constructor].
Defined.
Local Lemma blocked_alt e l h :
  blocked e l h ↔ Exists (λ e', head_blocked e' l h) (sub_exprs e).
Proof.
  rewrite /blocked Exists_exists. setoid_rewrite sub_exprs_spec. naive_solver.
Qed.
Global Instance blocked_dec e l h : Decision (blocked e l h).
Proof.
  refine (cast_if (decide (Exists (λ e', head_blocked e' l h) (sub_exprs e))));
    by rewrite blocked_alt.
Defined.

Lemma reducible_or_blocked_ctx k e h :
  ctx k → reducible_or_blocked e h → reducible_or_blocked (k e) h.
Proof.
  intros ? [? | [l ?]]; [left|right]; eauto using reducible_ctx, blocked_ctx.
Qed.

Ltac inv_prim_step Hps :=
  inversion Hps as [?????? []];
  repeat match goal with
    | Hk : ctx ?k, H : ?k _ = Val _ |- _ => apply (ctx_Val _ _ _ Hk) in H
    | _ => progress simplify_eq/=
    | H : head_step ?e _ _ _ _ |- _ => assert_fails (is_var e); inv H
    | H : pure_step ?e _ |- _ => assert_fails (is_var e); inv H
    | H : ctx1 _ |- _ => destruct H
    end.

Lemma prim_step_ctx1_inv k e h ke' h' es_new :
  to_val e = None →
  ctx1 k →
  prim_step (k e) h ke' h' es_new →
  ∃ e', prim_step e h e' h' es_new ∧ ke' = k e'.
Proof. intros ?? Hps; inv_prim_step Hps; eauto using prim_step. Qed.

Lemma prim_step_ctx_inv k e h e' h' es_new :
  to_val e = None →
  ctx k → prim_step (k e) h e' h' es_new →
  ∃ e'', prim_step e h e'' h' es_new ∧ e' = k e''.
Proof.
  intros Htv Hctx. revert e e' h h' Htv.
  induction Hctx as [|k k' ?? IH]; intros e e' h h' Htv Hps; [by eauto|].
  eapply (prim_step_ctx1_inv k) in Hps
    as (e'' & Hps & ->); naive_solver eauto using to_val_ctx_None.
Qed.

Lemma fork_reducible_or_blocked f h :
  reducible_or_blocked (ForkChan (Val f)) h.
Proof.
  eapply head_step_reducible_or_blocked with _ (<[fresh (dom h):=ChanHV None]> h) [_].
  econstructor. apply not_elem_of_dom, is_fresh.
Qed.

Lemma reducible_step i e σ :
  σ.1 !! i = Some e →
  reducible e σ.2 →
  ∃ σ', step σ σ'.
Proof.
  destruct σ as [es h]; simpl. intros ? (e'&h'&es'&?). eauto using step.
Qed.

Fixpoint subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  destruct e; simpl; f_equal; simplify_option_eq; auto.
  select (list _) (fun tes => induction tes as [|[]]);
    simplify_eq/=; f_equal; auto with f_equal.
Qed.
Fixpoint subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. destruct e; simpl; try (by f_equal; auto).
  - simplify_option_eq; auto with f_equal.
  - f_equal. simplify_option_eq; auto with f_equal.
  - select (list _) (fun tes => induction tes as [|[]]);
      simplify_eq/=; f_equal; auto with f_equal.
Qed.

(* Parallel substitution *)
Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | LetPair e1 e2 => LetPair (subst_map vs e1) (subst_map vs e2)
  | Sum t e => Sum t (subst_map vs e)
  | MatchSum e tes =>
      MatchSum
        (subst_map vs e)
        (prod_map id (subst_map vs) <$> tes)
  | ForkChan e => ForkChan (subst_map vs e)
  | Send e1 e2 => Send (subst_map vs e1) (subst_map vs e2)
  | Recv e => Recv (subst_map vs e)
  | Alloc e => Alloc (subst_map vs e)
  | Free e => Free (subst_map vs e)
  | Load e => Load (subst_map vs e)
  | Store e1 e2 => Store (subst_map vs e1) (subst_map vs e2)
  end.

Fixpoint subst_map_empty e : subst_map ∅ e = e.
Proof.
  destruct e; simplify_map_eq; rewrite ?binder_delete_empty; f_equal; auto.
  select (list _) (fun tes => induction tes as [|[]]);
    simplify_eq/=; repeat f_equal; auto.
Qed.
Fixpoint subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. destruct e=> vs; simplify_map_eq; try f_equal; auto.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !binder_delete_insert // !binder_delete_delete; eauto with f_equal.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= binder_delete_insert // delete_insert_delete
        !binder_delete_delete delete_idemp.
  - select (list _) (fun tes => induction tes as [|[]]);
      simplify_eq/=; f_equal; auto with f_equal.
Qed.

Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.

Lemma subst_map_binder_insert_2 b1 v1 b2 v2 vs e :
  subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e)).
Proof.
  destruct b1 as [|s1], b2 as [|s2]=> /=; auto using subst_map_insert.
  rewrite subst_map_insert. destruct (decide (s1 = s2)) as [->|].
  - by rewrite delete_idemp subst_subst delete_insert_delete.
  - by rewrite delete_insert_ne // subst_map_insert subst_subst_ne.
Qed.
