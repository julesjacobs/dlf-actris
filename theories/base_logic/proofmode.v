From dlfactris.base_logic Require Export wp.
From iris.proofmode Require Import coq_tactics reduction.

(* ########################################################################## *)
(** Automation for our program logic *)
(* ########################################################################## *)

(** We provide two extensions to make WP proofs easier:

- We extend Iris's [iApply] to become smarter when applying WP lemmas:
  + We let it automatically perform pure reductions.
  + We let it automatically perform the context rule [wp_ctx].
  + We let it automatically perform framing + monotonicity, i.e., let is
    generate a wand if the postconditions do not match. If the expression is
    not a value, the wand will appear under a later, i.e., it uses
    [wp_later_wand].
  + We let it curry the postcondition.
- We provide [wp_X] tactics.

To implement these extensions, we need automation to decompose an expression
into an evaluation context and a subexpression. We implement this automation
solely using classes. Our class-based solution is less error-prone than Iris's
[Ltac]-based solution in its [reshape_expr] tactic, and works better for our
"functional evaluation contexts" since we also need to construct a proof of
[ctx k]. *)

(** The typical instances are [P := TCEq e'] to find the subterm [e'] in [e],
and [P := PureStep Φi] to find a pure redex. *)
Inductive IntoCtx (e : expr) (P : expr → Prop) (k : expr → expr) : Prop :=
  Mk_IntoCtx (e' : expr) (_ : ctx k) (_ : e = k e') (_ : P e').
Existing Class IntoCtx.
Global Hint Mode IntoCtx ! ! - : typeclass_instances.

Class DoPureStep (e1 e2 : expr) := { do_pure_step : pure_step e1 e2 }.
Global Hint Mode DoPureStep ! - : typeclass_instances.

Class DoPureSteps (n : nat) (e1 e2 : expr) :=
  { do_pure_steps : nsteps pure_ctx_step n e1 e2 }.
Global Hint Mode DoPureSteps - ! - : typeclass_instances.

Inductive DoPureStepsIntoCtx
    (e : expr) (P : expr → Prop) (n : nat) (k : expr → expr) : Prop :=
  Mk_DoPureStepsIntoCtx e' (_ : DoPureSteps n e e') (_ : IntoCtx e' P k).
Existing Class DoPureStepsIntoCtx.
Global Hint Mode DoPureStepsIntoCtx ! ! - - : typeclass_instances.

Lemma do_pure_steps_into_ctx_wp e P n k :
  DoPureStepsIntoCtx e P n k →
  ∃ e', ctx k ∧ P e' ∧ ∀ Φ, ▷^n WP e' {{ w, WP k (Val w) {{ Φ }} }} ⊢ WP e {{ Φ }}.
Proof.
  intros [? [Hsteps] [e' Hk -> HP]]. exists e'. split_and!; [done..|].
  intros Φ. rewrite wp_bind //. clear Hk HP.
  induction Hsteps as [|n' e1 e2 e3 ?? IH]; simpl; [done|].
  by rewrite IH wp_pure_step.
Qed.

(** [IntoCtx] instances *)

(** Lowest cost, since we want to traverse outside-inside and find the first
subterm that matches. *)
Global Instance into_ctx_id e (P : expr → Prop) :
  P e → IntoCtx e P (fun x => x) | 0.
Proof. exists e; eauto using ctx. Qed.

Global Instance into_ctx_app_r k e1 e2 P :
  IntoCtx e2 P k →
  IntoCtx (App e1 e2) P (fun x => App e1 (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_app_l k e1 v2 P :
  IntoCtx e1 P k →
  IntoCtx (App e1 (Val v2)) P (fun x => App (k x) (Val v2)).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, App x _)); auto using ctx1.
Qed.
Global Instance into_ctx_un_op k op e P :
  IntoCtx e P k →
  IntoCtx (UnOp op e) P (fun x => UnOp op (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_bin_op_r k op e1 e2 P :
  IntoCtx e2 P k →
  IntoCtx (BinOp op e1 e2) P (fun x => BinOp op e1 (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_bin_op_l k op e1 v2 P :
  IntoCtx e1 P k →
  IntoCtx (BinOp op e1 (Val v2)) P (fun x => BinOp op (k x) (Val v2)).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, BinOp _ x _)); auto using ctx1.
Qed.
Global Instance into_ctx_if k e e1 e2 P :
  IntoCtx e P k →
  IntoCtx (If e e1 e2) P (fun x => If (k x) e1 e2).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, If x _ _)); auto using ctx1.
Qed.
Global Instance into_ctx_pair_r k e1 e2 P :
  IntoCtx e2 P k →
  IntoCtx (Pair e1 e2) P (fun x => Pair e1 (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_pair_l k e1 v2 P :
  IntoCtx e1 P k →
  IntoCtx (Pair e1 (Val v2)) P (fun x => Pair (k x) (Val v2)).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, Pair x _)); auto using ctx1.
Qed.
Global Instance into_ctx_let_pair k e1 e2 P :
  IntoCtx e1 P k →
  IntoCtx (LetPair e1 e2) P (fun x => LetPair (k x) e2).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, LetPair x _)); auto using ctx1.
Qed.
Global Instance into_ctx_sum k t e P :
  IntoCtx e P k →
  IntoCtx (Sum t e) P (fun x => Sum t (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_match_sum k e tes P :
  IntoCtx e P k →
  IntoCtx (MatchSum e tes) P (fun x => MatchSum (k x) tes).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, MatchSum x _)); auto using ctx1.
Qed.
Global Instance into_ctx_fork_chan k e P :
  IntoCtx e P k →
  IntoCtx (ForkChan e) P (fun x => ForkChan (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_send_r k e1 e2 P :
  IntoCtx e2 P k →
  IntoCtx (Send e1 e2) P (fun x => Send e1 (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_send_l k e1 v2 P :
  IntoCtx e1 P k →
  IntoCtx (Send e1 (Val v2)) P (fun x => Send (k x) (Val v2)).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, Send x _)); auto using ctx1.
Qed.
Global Instance into_ctx_recv k e P :
  IntoCtx e P k →
  IntoCtx (Recv e) P (fun x => Recv (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_alloc k e P :
  IntoCtx e P k →
  IntoCtx (Alloc e) P (fun x => Alloc (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_free k e P :
  IntoCtx e P k →
  IntoCtx (Free e) P (fun x => Free (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_load k e P :
  IntoCtx e P k →
  IntoCtx (Load e) P (fun x => Load (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_store_r k e1 e2 P :
  IntoCtx e2 P k →
  IntoCtx (Store e1 e2) P (fun x => Store e1 (k x)).
Proof. intros [e' ? -> ?]; exists e'; eauto using ctx, ctx1. Qed.
Global Instance into_ctx_store_l k e1 v2 P :
  IntoCtx e1 P k →
  IntoCtx (Store e1 (Val v2)) P (fun x => Store (k x) (Val v2)).
Proof.
  intros [e' ? -> ?]; exists e'; [|done..].
  apply (Ctx_compose (λ x, Store x _)); auto using ctx1.
Qed.

(** [PureStep] instances *)
Global Instance do_pure_step_rec f x e :
  DoPureStep (Rec f x e) (Val (RecV f x e)).
Proof. do 2 constructor. Qed.

(** [do_pure_step_app] is not an [Instance], but a [Hint Extern] to enable
syntactic matching instead of unification-based matching. This is important
because it would otherwise unfold definitions. For example, when considering
[wp (swap ...) Φ] where [Definition swap := RecV ...], it should *not* unfold
[swap] to as to preserve abstraction barriers. *)
Lemma do_pure_step_app f x e v e' :
  TCSimpl (subst' x v (subst' f (RecV f x e) e)) e' →
  DoPureStep (App (Val (RecV f x e)) (Val v)) e'.
Proof. by do 2 constructor. Qed.
Global Hint Extern 1 (DoPureStep (App (Val (RecV _ _ _)) (Val _)) _) =>
  notypeclasses refine (do_pure_step_app _ _ _ _ _ _) : typeclass_instances.

Global Instance do_pure_step_un_op op v v' :
  TCEq (un_op_eval op v) (Some v') →
  DoPureStep (UnOp op (Val v)) (Val v').
Proof. intros ?%TCEq_eq. by do 2 constructor. Qed.

Global Instance do_pure_step_bin_op op v1 v2 v :
  TCEq (bin_op_eval op v1 v2) (Some v) →
  DoPureStep (BinOp op (Val v1) (Val v2)) (Val v).
Proof. intros ?%TCEq_eq. by do 2 constructor. Qed.

Global Instance do_pure_step_if_true e1 e2 :
  DoPureStep (If (Val (LitV (LitBool true))) e1 e2) e1.
Proof. do 2 constructor. Qed.

Global Instance do_pure_step_if_false e1 e2 :
  DoPureStep (If (Val (LitV (LitBool false))) e1 e2) e2.
Proof. do 2 constructor. Qed.

Global Instance do_pure_step_pair v1 v2 :
  DoPureStep (Pair (Val v1) (Val v2)) (Val (PairV v1 v2)).
Proof. do 2 constructor. Qed.

Global Instance do_pure_step_let_pair v1 v2 e :
  DoPureStep (LetPair (Val (PairV v1 v2)) e) (App (App e (Val v1)) (Val v2)).
Proof. do 2 constructor. Qed.

Global Instance do_pure_step_sum t v :
  DoPureStep (Sum t (Val v)) (Val (SumV t v)).
Proof. do 2 constructor. Qed.

Global Instance do_pure_step_match t v es e :
  TCEq (sum_branch t es) (Some e) →
  DoPureStep (MatchSum (Val (SumV t v)) es) (App e (Val v)).
Proof. intros ?%TCEq_eq. by do 2 constructor. Qed.

Global Instance do_pure_steps_0 e : DoPureSteps 0 e e | 100.
Proof. split. apply nsteps_O. Qed.

Global Instance do_pure_steps_S n k e1 e2 e3 :
  IntoCtx e1 (λ e1', DoPureStep e1' e2) k →
  DoPureSteps n (k e2) e3 →
  DoPureSteps (S n) e1 e3.
Proof.
  intros [e1' ? -> [?]] [?]; split. econstructor; last done.
  by apply (PureCtx_step k).
Qed.

Global Instance do_pure_steps_into_ctx_0 e k P :
  IntoCtx e P k → DoPureStepsIntoCtx e P 0 k | 0.
Proof. econstructor; [|done]. by repeat constructor. Qed.

Global Instance do_pure_steps_into_ctx_S e1 e2 e2' k k' n P :
  TCNoBackTrack (IntoCtx e1 (λ e1', DoPureStep e1' e2') k') →
  TCSimpl (k' e2') e2 →
  DoPureStepsIntoCtx e2 P n k →
  DoPureStepsIntoCtx e1 P (S n) k | 100.
Proof.
  intros [[e1' ? -> [?]]] <- [e' [?] ?]. exists e'; last done.
  split. econstructor; last done. by apply (PureCtx_step k').
Qed.

(** We now extend [iApply] and [iAssumption] to automatically use [wp_ctx] and
framing/weakening. *)

(** The class [NewPost] is used to only apply the bind rule if the postcondition
is non-trivial (i.e., not [id]). This results in simpler goals. *)
Class NewPost (k : expr → expr) (Φ Φ' : val → aProp) :=
  { new_post e : ctx k → WP e {{ Φ' }} ⊢ WP k e {{ Φ }} }.
Global Hint Mode NewPost ! ! - : typeclass_instances.

Global Instance new_post_default k Φ Φ' :
  TCIf (TCEq k id) (TCEq Φ Φ')
                   (TCEq (λ vret, WP k (Val vret) {{ Φ }})%I Φ') →
  NewPost k Φ Φ' | 10.
Proof.
  intros [-> ->|<-]; [done|].
  split=> e ?. by apply wp_bind.
Qed.

Class NormalizeWP (P : aProp) (e' : expr) (Φ' : val → aProp) :=
  { normalize_wp : WP e' {{ Φ' }} ⊢ P }.
Global Hint Mode NormalizeWP ! ! - : typeclass_instances.

Global Instance normalize_wp_here e e' k Φ Φ' :
  TCNoBackTrack (IntoCtx e (TCEq e') k) →
  NewPost k Φ Φ' →
  NormalizeWP (WP e {{ Φ }}) e' Φ' | 0.
Proof. intros [ [?? -> <-] ] [Hpost]. split. by apply Hpost. Qed.

Global Instance normalize_wp_val v Φ e' Φ' :
  NormalizeWP (Φ v) e' Φ' →
  NormalizeWP (WP Val v {{ Φ }}) e' Φ' | 1.
Proof. intros [HΦ]. split. rewrite HΦ. iApply wp_val. Qed.

Global Instance normalize_wp_step e1 e2 k e' Φ Φ' :
  TCNoBackTrack (IntoCtx e1 (λ e1', DoPureStep e1' e2) k) →
  NormalizeWP (WP k e2 {{ Φ }}) e' Φ' →
  NormalizeWP (WP e1 {{ Φ }}) e' Φ' | 10.
Proof.
  intros [ [e'' ? -> [?]] ] [Hpost]. split.
  etrans; [|by apply wp_pure_step, (PureCtx_step k); auto using pure_step].
  by rewrite -bi.later_intro.
Qed.

Class WandPost (Φ Ψ : val → aProp) (P : aProp) :=
  { wand_post : P ⊢ ∀ vret, Φ vret -∗ Ψ vret }.
Global Instance wand_post_here Φ Ψ : WandPost Φ Ψ (∀ vret, Φ vret -∗ Ψ vret) | 100.
Proof. by constructor. Qed.
Lemma wand_post_pure v Ψ :
  WandPost (λ vret, ⌜⌜ vret = v ⌝⌝)%I Ψ (Ψ v).
Proof. constructor. by iIntros "H" (vret ->). Qed.
Lemma wand_post_pure_sep v P Ψ :
  WandPost (λ vret, ⌜⌜ vret = v ⌝⌝ ∗ P)%I Ψ (P -∗ Ψ v).
Proof. constructor. iIntros "H" (vret) "[-> ?]". by iApply "H". Qed.
Lemma wand_post_exist {A} (Φ : A → val → aProp) Ψ Ψ' :
  (∀ x, WandPost (Φ x) Ψ (Ψ' x)) →
  WandPost (λ vret, ∃ x, Φ x vret)%I Ψ (∀ x, Ψ' x).
Proof.
  constructor. iIntros "H" (vret) "[%x ?]". destruct (H x) as [Hx].
  by iApply (Hx with "[H]").
Qed.
(* Not instances, to avoid unfolding definitions *)
Global Hint Extern 10 (WandPost (λ _, ⌜⌜ _ ⌝⌝)%I _ _) =>
  notypeclasses refine (wand_post_pure _ _) : typeclass_instances.
Global Hint Extern 10 (WandPost (λ _, ⌜⌜ _ ⌝⌝ ∗ _)%I _ _) =>
  notypeclasses refine (wand_post_pure_sep _ _ _) : typeclass_instances.
Global Hint Extern 10 (WandPost (λ _, ∃ _, _)%I _ _) =>
  notypeclasses refine (wand_post_exist _ _ _ _) : typeclass_instances.
Global Hint Extern 10 (WandPost (λ _, ∃.. _, _)%I _ _) =>
  progress simpl : typeclass_instances.
  (* progress makes sure telescopes are normalized, so this should terminate *)

Global Instance from_assumption_wp p e e' Φ Φ' :
  NormalizeWP (WP e {{ Φ }}) e' Φ' →
  FromAssumption p (WP e' {{ Φ' }}) (WP e {{ Φ }}) | 2.
Proof.
  intros [HΦ].
  rewrite /FromAssumption bi.intuitionistically_if_elim. by rewrite HΦ.
Qed.

Global Instance into_wand_wp_no_val p e e' Φ Ψ Ψ' Q :
  TCEq (to_val e') None →
  NormalizeWP (WP e {{ Ψ }}) e' Ψ' →
  WandPost Φ Ψ' Q →
  IntoWand p false (WP e' {{ Φ }}) (▷ Q) (WP e {{ Ψ }}) | 0.
Proof.
  intros ?%TCEq_eq [Hwp] [HQ]. rewrite /IntoWand /= bi.intuitionistically_if_elim.
  rewrite HQ -Hwp. iIntros "Hwp ?". iApply (wp_later_wand with "Hwp").
  by rewrite bool_decide_true.
Qed.

Global Instance into_wand_wp p e e' Φ Ψ Ψ' Q :
  NormalizeWP (WP e {{ Ψ }}) e' Ψ' →
  WandPost Φ Ψ' Q →
  IntoWand p false (WP e' {{ Φ }}) Q (WP e {{ Ψ }}) | 1.
Proof.
  intros [Hwp] [HQ]. rewrite /IntoWand /= bi.intuitionistically_if_elim.
  rewrite HQ -Hwp. iApply wp_wand.
Qed.

(** This instance should not be needed, but is a workaround for
https://gitlab.mpi-sws.org/iris/iris/-/issues/458 *)

Global Instance into_wand_wand_wp p q e e' P P' Φ Φ' :
  NormalizeWP (WP e {{ Φ }}) e' Φ' →
  FromAssumption q P P' →
  IntoWand p q (P' -∗ WP e' {{ Φ' }}) P (WP e {{ Φ }}).
Proof.
  rewrite /FromAssumption /IntoWand. intros [HΦ] ->; simpl.
  rewrite bi.intuitionistically_if_elim.
  apply bi.wand_mono; [done|]. by rewrite HΦ.
Qed.

(** And finally some tactics *)

Class FinalizeWP (e : expr) (Φ : val → aProp) (P : aProp) :=
  { finalize_wp : P ⊢ WP e {{ Φ }} }.
Global Hint Mode FinalizeWP ! ! - : typeclass_instances.

Global Instance finalize_wp_val Φ v : FinalizeWP (Val v) Φ (Φ v) | 0.
Proof. constructor. iApply wp_val. Qed.
Global Instance finalize_wp_val_simpl Φ e e' :
  TCSimpl e e' → FinalizeWP e Φ (WP e' {{ Φ }}) | 1.
Proof. intros ->. by constructor. Qed.

Lemma tac_wp_pure {Δ Δ' e1 e2 Φ Q} n :
  DoPureSteps n e1 e2 →
  MaybeIntoLaterNEnvs n Δ Δ' →
  FinalizeWP e2 Φ Q →
  envs_entails Δ' Q →
  envs_entails Δ (WP e1 {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> -[Hsteps] HΔ [HQ] HΔ'.
  rewrite into_laterN_env_sound HΔ' HQ {HQ HΔ HΔ'}.
  induction Hsteps as [|n' e1 e2 e3]; simpl; [done|].
  etrans; [|by apply wp_pure_step]. by f_equiv.
Qed.

Class IsAppRec (v1 v2 : val) (f x : binder) (e' : expr) (e : expr) := {
  is_app_rec_val : v1 = RecV f x e';
  is_app_rec_expr : e = App (Val v1) (Val v2);
}.
Global Hint Mode IsAppRec - - - - - ! : typeclass_instances.
Global Instance is_app_rec v1 v2 f x e :
  TCEq v1 (RecV f x e) →
  IsAppRec v1 v2 f x e (App (Val v1) (Val v2)).
Proof. rewrite TCEq_eq=> ->. by constructor. Qed.

Lemma tac_wp_rec {Δ Δ' e v1 v2 f x e' k Φ Q} :
  IntoCtx e (IsAppRec v1 v2 f x e') k →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  FinalizeWP (k (subst' x v2 (subst' f v1 e'))) Φ Q →
  envs_entails Δ' Q →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> Hctx HΔ [HQ] HΔ'.
  rewrite into_laterN_env_sound HΔ' HQ {HΔ HΔ'} /=.
  destruct Hctx as [e1' ? -> [-> ->]].
  apply wp_pure_step, (PureCtx_step k); auto using pure_step.
Qed.

Tactic Notation "wp_pures" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_pure n _ _ _ _);
       [tc_solve || fail 1 "wp_pures: no pure steps can be performed"
       |tc_solve (* into later *)
       |tc_solve (* simpl *)
       |pm_prettify]
  | |- _ => fail "wp_pures: goal not a `wp`"
  end.
Tactic Notation "wp_pure" := wp_pures 1.
Tactic Notation "wp_pures" := wp_pures (S _).

Tactic Notation "wp_rec" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_rec _ _ _ _);
       [tc_solve || fail 1 "wp_rec: no beta reduction step can be performed"
       |tc_solve (* into later *)
       |tc_solve (* simpl *)
       |pm_prettify]
  | |- _ => fail "wp_rec: goal not a `wp`"
  end.
Tactic Notation "wp_rec" "!" := wp_rec; wp_pures _.

Lemma tac_wp_alloc {Δ Δ' e n k v Φ} i :
  DoPureStepsIntoCtx e (TCEq (Alloc (Val v))) n k →
  MaybeIntoLaterNEnvs (S n) Δ Δ' →
  (∀ l, ∃ Q,
    FinalizeWP (k (Val (LitV (LitLoc l)))) Φ Q ∧
    match envs_app false (Esnoc Enil i (l ↦ v)) Δ' with
    | Some Δ'' => envs_entails Δ'' Q
    | None => False
    end) →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ? HΔ') "HΔ".
  rewrite into_laterN_env_sound /=. iApply Hwp; iNext.
  iApply wp_alloc; iIntros "!>" (l) "Hl".
  destruct (HΔ' l) as (Q & [HQ] & HΔl); clear HΔ'. iApply HQ.
  destruct (envs_app _ _ _) as [Δ''|] eqn:?; last done. iApply HΔl.
  iApply (envs_app_sound with "[$]"); first done. by iFrame.
Qed.

Lemma tac_wp_free {Δ Δ' e n k l v i Φ Q} :
  DoPureStepsIntoCtx e (TCEq (Free (Val (LitV (LitLoc l))))) n k →
  MaybeIntoLaterNEnvs (S n) Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  FinalizeWP (k (Val (LitV LitUnit))) Φ Q →
  envs_entails (envs_delete false i false Δ') Q →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ?? [HQ] HΔ') "HΔ".
  rewrite into_laterN_env_sound /= envs_lookup_sound //=.
  set (envs_delete true i false Δ') as Δ''.
  iDestruct "HΔ" as "[Hl HΔ]"; [done..|].
  iApply Hwp. iNext. iMod "Hl". iApply (wp_free with "Hl"); iNext.
  iApply HQ. by iApply HΔ'.
Qed.

Lemma tac_wp_load {Δ Δ' e n k l v i Φ Q} :
  DoPureStepsIntoCtx e (TCEq (Load (Val (LitV (LitLoc l))))) n k →
  MaybeIntoLaterNEnvs (S n) Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  FinalizeWP (k (Val v)) Φ Q →
  envs_entails Δ' Q →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ?? [HQ] HΔ') "HΔ".
  rewrite into_laterN_env_sound /=. iApply Hwp; iNext.
  iDestruct (envs_lookup_split with "HΔ") as "[Hl HΔ]"; [done|]; simpl.
  iMod "Hl". iApply (wp_load with "Hl"); iIntros "!> Hl".
  iApply HQ. iApply HΔ'. by iApply "HΔ".
Qed.

Lemma tac_wp_store {Δ Δ' e n k l v v' i Φ Q} :
  DoPureStepsIntoCtx e (TCEq (Store (Val (LitV (LitLoc l))) (Val v'))) n k →
  MaybeIntoLaterNEnvs (S n) Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  FinalizeWP (k (Val (LitV LitUnit))) Φ Q →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end →
  envs_entails Δ (WP e {{ Φ }}).
Proof.
  rewrite envs_entails_unseal.
  iIntros ((e'&?&<-%TCEq_eq&Hwp)%do_pure_steps_into_ctx_wp ?? [HQ] HΔ') "HΔ".
  rewrite into_laterN_env_sound /=. iApply Hwp; iNext.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:?; last done.
  iDestruct (envs_simple_replace_sound with "HΔ") as "[Hl HΔ]"; [done..|]; simpl.
  iMod "Hl". iApply (wp_store with "Hl"); iIntros "!> Hl".
  iApply HQ. iApply HΔ'. iApply "HΔ". by iFrame.
Qed.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  iStartProof;
  let Htmp := iFresh in
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_alloc Htmp _ _ _);
       [tc_solve || fail 1 "wp_alloc: cannot find 'alloc' subexpression"
       |tc_solve (* into laters *)
       |pm_reduce;
        first [intros l | fail 1 "wp_alloc:" l "not fresh"];
        notypeclasses refine (ex_intro _ _ (conj _ _));
          [tc_solve (* simpl *)
          |iDestructHyp Htmp as H]]
  | _ => fail "wp_alloc: goal not a 'wp'"
  end.
Tactic Notation "wp_alloc" "!" ident(l) "as" constr(H) :=
  wp_alloc l as H; wp_pures _.
Tactic Notation "wp_alloc" ident(l) := wp_alloc l as "?".
Tactic Notation "wp_alloc" "!" ident(l) := wp_alloc! l as "?".

Tactic Notation "wp_free" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_free _ _ _ _ _);
       [tc_solve || fail 1 "wp_free: cannot find 'free' subexpression"
       |tc_solve (* into laters *)
       |iAssumptionCore || fail 1 "wp_free: cannot find ↦"
       |tc_solve (* simpl *)
       |pm_reduce]
  | _ => fail "wp_free: goal not a 'wp'"
  end.
Tactic Notation "wp_free" "!" := wp_free; wp_pures _.

Tactic Notation "wp_load" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_load _ _ _ _ _);
       [tc_solve || fail 1 "wp_load: cannot find 'load' subexpression"
       |tc_solve (* into laters *)
       |iAssumptionCore || fail 1 "wp_load: cannot find ↦"
       |tc_solve (* simpl *)
       |]
  | _ => fail "wp_load: goal not a 'wp'"
  end.
Tactic Notation "wp_load" "!" := wp_load; wp_pures _.

Tactic Notation "wp_store" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (WP _ {{ _ }}) =>
     notypeclasses refine (tac_wp_store _ _ _ _ _);
       [tc_solve || fail 1 "wp_store: cannot find 'store' subexpression"
       |tc_solve (* into laters *)
       |iAssumptionCore || fail 1 "wp_store: cannot find ↦"
       |tc_solve (* simpl *)
       |pm_reduce]
  | _ => fail "wp_store: goal not a 'wp'"
  end.
Tactic Notation "wp_store" "!" := wp_store; wp_pures _.
