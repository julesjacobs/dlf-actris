From dlfactris.lang Require Import metatheory.
From dlfactris.base_logic Require Export wp_prim.

Local Definition wp_def (e : expr) (Φ : val → aProp) : aProp :=                  (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=2d06e885 *)
  ∀ R, ▷?(bool_decide (to_val e = None)) R -∗
       wp_prim e (λ v, Φ v ∗ R).
Local Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).
Local Definition wp_unseal : wp = _ := wp_aux.(seal_eq).
Global Instance: Params (@wp) 1 := {}.

Notation "'WP' e {{ Φ } }" := (wp e Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e '/'  '[' {{  v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' x  ..  y ,  RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  '[' P  ']' } } }  '/  ' e  '/' {{{  '[' RET  pat ;  '/' Q  ']' } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }}) : stdpp_scope.

Global Instance wp_ne e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp e).
Proof. rewrite wp_unseal. solve_proper. Qed.
Global Instance wp_proper e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp e).
Proof. rewrite wp_unseal. solve_proper. Qed.
Global Instance is_except_0_wp e Φ : IsExcept0 (WP e {{ Φ }}).
Proof. rewrite /IsExcept0 wp_unseal /wp_def. by iIntros ">H". Qed.

Lemma wp_val Φ v : Φ v ⊢ WP (Val v) {{ Φ }}.                                     (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=6f2876ab *)
Proof.
  rewrite wp_unseal /wp_def /=.
  iIntros "HΦ %R HR /=". iApply wp_prim_val. iFrame.
Qed.

Lemma wp_val_inv Φ v : WP (Val v) {{ Φ }} ⊢ ◇ Φ v.
Proof.
  rewrite wp_unseal /wp_def /=. iIntros "Hwp".
  iSpecialize ("Hwp" $! emp%I with "[//]").
  by iMod (wp_prim_val_inv with "Hwp") as "[$ _]".
Qed.

Lemma wp_wp_prim e Φ : WP e {{ Φ }} ⊢ wp_prim e Φ.
Proof.
  rewrite wp_unseal /wp_def. iIntros "H".
  iApply wp_prim_mono; last by iApply ("H" $! emp%I).
  by iIntros (v) "[H _]".
Qed.

Lemma wp_later_wand e Φ Ψ :
  WP e {{ Φ }} -∗ ▷?(bool_decide (to_val e = None)) (∀ v, Φ v -∗ Ψ v) -∗
  WP e {{ Ψ }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "He HΦ %R HR /=".
  iApply (wp_prim_mono _ (λ v, Φ v ∗ (R ∗ ∀ v, Φ v -∗ Ψ v))%I).
  { iIntros (v) "(?&$&H)". by iApply "H". }
  iApply "He". iNext. iFrame.
Qed.

Global Instance wp_contractive e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp e).
Proof.
  intros He%TCEq_eq. assert (Contractive (wp e : (val -d> aProp) → _)) as Hwp.
  { apply (contractive_internal_eq (PROP:=aProp)); iIntros (Φ1 Φ2) "#HΦ".
    rewrite discrete_fun_equivI.
    iApply plainly.prop_ext_2; iIntros "!>"; iSplit; iIntros "Hwp";
      iApply (wp_later_wand with "Hwp"); rewrite He /=;
      iIntros (v) "!>"; iRewrite ("HΦ" $! v); auto. }
  intros Φ1 Φ2 HΦ. apply Hwp. dist_later_intro. apply HΦ.
Qed.

Lemma wp_wand e Φ Ψ : WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
Proof. iIntros "Hwp H". iApply (wp_later_wand with "Hwp"); auto. Qed.

Lemma wp_pure_step e1 e2 Φ :
  pure_ctx_step e1 e2 →
  ▷ WP e2 {{ Φ }} ⊢ WP e1 {{ Φ }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "%Hstep He %R HR /=".
  iApply wp_prim_pure_step; first done.
  rewrite (bool_decide_true (to_val e1 = _)) /=; last by eapply pure_ctx_step_not_val.
  iApply "He". auto.
Qed.

Lemma wp_bind k Φ e :
  ctx k →
  WP e {{ v, WP k (Val v) {{ Φ }} }} ⊢ WP k e {{ Φ }}.
Proof.
  intros Hctx. rewrite wp_unseal /wp_def. iIntros "Hwp %R HR".
  iApply wp_prim_bind; first done.
  destruct (to_val e) as [v|] eqn:He; simpl.
  { apply to_val_Val in He as ->. iApply wp_prim_val.
    iMod (wp_prim_val_inv with "(Hwp HR)") as "[Hwp HR]". by iApply "Hwp". }
  rewrite bool_decide_true; last by apply to_val_ctx_None.
  iApply (wp_prim_mono with "(Hwp HR)").
  iIntros (w) "[Hwp HR]". iApply "Hwp". by iNext.
Qed.

Lemma wp_send l v Φ :                                                            (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=50f52fc1 *)
  own_chan l (MiniProt ASend Φ) -∗ ▷ Φ v -∗
  WP Send (Val (LitV (LitLoc l))) (Val v) {{ v, ⌜⌜ v = LitV LitUnit ⌝⌝ }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "Hl HΦ %R HR".
  iApply wp_prim_send. iFrame "Hl HΦ". by iNext.
Qed.

Lemma wp_recv l Φ :
  own_chan l (MiniProt ARecv Φ) -∗
  WP Recv (Val (LitV (LitLoc l))) {{ Φ }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "Hl %R HR".
  iApply wp_prim_recv. by iFrame.
Qed.

Lemma wp_fork f p :
  ▷ (∀ l, own_chan l (dual p) -∗
           WP App (Val f) (Val (LitV (LitLoc l))) {{ _, emp }}) -∗
  WP ForkChan (Val f) {{ v,
    ∃ l, ⌜⌜ v = LitV (LitLoc l) ⌝⌝ ∗ own_chan l p }}.
Proof.
  rewrite {2}wp_unseal /wp_def. iIntros "Hf %R HR". setoid_rewrite wp_wp_prim.
  iApply wp_prim_fork. by iFrame.
Qed.

Lemma wp_alloc v :                                                               (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=1b8cb023 *)
  ⊢ WP Alloc (Val v) {{ w, ∃ l, ⌜⌜ w = LitV (LitLoc l) ⌝⌝ ∗ l ↦ v }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "%R HR".
  iApply wp_prim_alloc. by iFrame.
Qed.

Lemma wp_load l v :
  l ↦ v -∗
  WP Load (Val (LitV (LitLoc l))) {{ w, ⌜⌜ w = v ⌝⌝ ∗ l ↦ v }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "Hl %R HR".
  iApply wp_prim_load. by iFrame.
Qed.

Lemma wp_store l v' v :
  l ↦ v -∗
  WP Store (Val (LitV (LitLoc l))) (Val v') {{ w, ⌜⌜ w = LitV LitUnit ⌝⌝ ∗ l ↦ v' }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "Hl %R HR".
  iApply wp_prim_store. by iFrame.
Qed.

Lemma wp_free l v :
  l ↦ v -∗
  WP Free (Val (LitV (LitLoc l))) {{ w, ⌜⌜ w = LitV LitUnit ⌝⌝ }}.
Proof.
  rewrite wp_unseal /wp_def. iIntros "Hl %R HR".
  iApply wp_prim_free. by iFrame.
Qed.
