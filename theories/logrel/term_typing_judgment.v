(** This file contains the definitions of the semantic typing judgment
[Γ ⊨ e : A ⫤ Γ'], indicating that in context [Γ], the expression [e] has type
[A], producing a new context [Γ']. The context is allowed to change to
accomodate things like changing the type of a channel after a receive.

In addition, we use the adequacy of Iris in order to show type soundness:
programs which satisfy the semantic typing relation are safe. That is,
semantically well-typed programs do not get stuck. *)
From dlfactris.lang Require Import metatheory.
From dlfactris.base_logic Require Import adequacy.
From dlfactris.logrel Require Export term_types contexts.
From iris.proofmode Require Import proofmode.

(** The semantic typing judgment *)
Definition ltyped (Γ1 Γ2 : ctx) (e : expr) (A : ltty) : aProp :=                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=4440cd06 *)
  tc_opaque (■ ∀ vs, ctx_ltyped vs Γ1 -∗
    WP subst_map vs e {{ v, ltty_car A v ∗ ctx_ltyped vs Γ2 }})%I.

Notation "Γ1 ⊨ e : A ⫤ Γ2" := (ltyped Γ1 Γ2 e A)
  (at level 100, e at next level, A at level 200) : bi_scope.
Notation "Γ ⊨ e : A" := (Γ ⊨ e : A ⫤ Γ)%I
  (at level 100, e at next level, A at level 200) : bi_scope.

Notation "Γ1 ⊨ e : A ⫤ Γ2" := (⊢ Γ1 ⊨ e : A ⫤ Γ2)
  (at level 100, e at next level, A at level 200) : type_scope.
Notation "Γ ⊨ e : A" := (⊢ Γ ⊨ e : A ⫤ Γ)
  (at level 100, e at next level, A at level 200) : type_scope.

Section ltyped.

  Global Instance ltyped_plain Γ1 Γ2 e A : Plain (ltyped Γ1 Γ2 e A).
  Proof. rewrite /ltyped /=. apply _. Qed.
  Global Instance ltyped_absorbing Γ1 Γ2 e A : Absorbing (ltyped Γ1 Γ2 e A).
  Proof. rewrite /ltyped /=. apply _. Qed.
  Global Instance ltyped_ne n :
    Proper (dist n ==> dist n ==> (=) ==> dist n ==> dist n) ltyped.
  Proof. solve_proper. Qed.
  Global Instance ltyped_proper :
    Proper ((≡) ==> (≡) ==> (=) ==> (≡) ==> (≡)) ltyped.
  Proof. solve_proper. Qed.
  Global Instance ltyped_Permutation :
    Proper ((≡ₚ) ==> (≡ₚ) ==> (=) ==> (≡) ==> (≡)) ltyped.
  Proof.
    intros Γ1 Γ1' HΓ1 Γ2 Γ2' HΓ2 e ? <- A ? <-. rewrite /ltyped /=.
    setoid_rewrite HΓ1. by setoid_rewrite HΓ2.
  Qed.
End ltyped.

(** Expressions and values are defined mutually recursive in HeapLang,
which means that only after a step of reduction we get that e.g.
[Pair (Val v1, Val v2)] reduces to [PairV (v1,v2)].
This makes typing of values tricky, for technical reasons.
To circumvent this, we make use of the following typing judgement for values,
that lets us type check values without requiring reduction steps.
The value typing judgement subsumes the typing judgement on expressions,
as made precise by the [ltyped_val_ltyped] lemma. *)
Definition ltyped_val (v : val) (A : ltty) : aProp :=
  tc_opaque (■ ltty_car A v)%I.
Global Instance: Params (@ltyped_val) 1 := {}.
Notation "⊨ᵥ v : A" := (ltyped_val v A)
  (at level 100, v at next level, A at level 200) : bi_scope.
Notation "⊨ᵥ v : A" := (⊢ ⊨ᵥ v : A)
  (at level 100, v at next level, A at level 200) : stdpp_scope.
Arguments ltyped_val : simpl never.

Section ltyped_val.
  Global Instance ltyped_val_plain v A : Plain (ltyped_val v A).
  Proof. rewrite /ltyped_val /=. apply _. Qed.
  Global Instance ltyped_val_absorbing v A : Absorbing (ltyped_val v A).
  Proof. rewrite /ltyped_val /=. apply _. Qed.
  Global Instance ltyped_val_ne n v :
    Proper (dist n ==> dist n) (ltyped_val v).
  Proof. solve_proper. Qed.
  Global Instance ltyped_val_proper v :
    Proper ((≡) ==> (≡)) (ltyped_val v).
  Proof. solve_proper. Qed.

  Lemma ltyped_val_ltyped Γ v A : (⊨ᵥ v : A) -∗ Γ ⊨ v : A.
  Proof.
    iIntros "#HA" (vs) "!> HΓ".
    iApply wp_val. iFrame "HΓ".
    rewrite /ltyped_val /=.
    iApply "HA".
  Qed.
End ltyped_val.

Lemma ltyped_soundness e σ :                                                     (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=d4c86e7d *)
  ([] ⊨ e : any ⫤ []) →
  steps ([e],∅) σ →
  global_progress σ (* deadlock and leak freedom *) ∧
  all_progress_or_blocked σ (* conventional safety *).
Proof.
  intros He. apply adequacy.
  iDestruct (He $! ∅ with "[]") as "He"; first by rewrite /ctx_ltyped.
  iEval (rewrite -(subst_map_empty e)). iApply (wp_wand with "He"); auto.
Qed.
