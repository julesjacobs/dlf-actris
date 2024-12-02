(** This file includes a specification [cmp_spec] for comparing values based on
a given interpretation [I], a relation [R] that matches up with a HeapLang
implementation [cmp]. The file also provides an instance for the [≤] relation
on integers [Z].*)
From dlfactris.lang Require Import notation.
From dlfactris.session_logic Require Import proofmode.

Definition cmp_spec {A} (I : A → val → aProp)
    (R : relation A) `{!RelDecision R} (cmp : val) : aProp :=
  □ (∀ x x' v v',
      I x v -∗ I x' v' -∗
      WP cmp v v'
      {{ w, ⌜⌜ w = #(bool_decide (R x x')) ⌝⌝ ∗ I x v ∗ I x' v' }})%I.

Definition IZ (x : Z) (v : val) : aProp := ⌜⌜ v = #x ⌝⌝%I.
Definition cmpZ : val := λ: "x" "y", "x" ≤ "y".

Lemma cmpZ_spec : ⊢ cmp_spec IZ (≤)%Z cmpZ.
Proof. rewrite /IZ. iIntros "!>" (x x' v v' -> ->). by wp_rec!. Qed.
