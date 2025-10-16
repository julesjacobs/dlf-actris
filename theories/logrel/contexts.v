(** This file contains definitions related to type contexts.
Contexts are encoded as lists of value and type pairs, for which
lifted operations are defined such as [ctx_cons x A Γ].

The following relations on contexts are defined:
- [ctx_ltyped Γ vs]: This relation indicates that the value map [vs] contains a
  value for each type in the semantic type context [Γ].
- [ctx_le Γ Γ']: This relation indicates that the context [Γ]
  subsumes that of [Γ'].

In addition, some lemmas/rules about these definitions are proved, corresponding
to the syntactic typing rules that are typically found in substructural type
systems. *)
From iris.algebra Require Export list.
From iris.bi.lib Require Import core.
From iris.proofmode Require Import proofmode.
From dlfactris.logrel Require Export term_types subtyping_rules.

Inductive ctx_item := CtxItem {
  ctx_item_name : binder;
  ctx_item_type : ltty;
}.
Add Printing Constructor ctx_item.
Global Instance: Params (@CtxItem) 1 := {}.

Section ctx_item_ofe.

  Instance ctx_item_equiv : Equiv (ctx_item) := λ xA1 xA2,
    ctx_item_name xA1 = ctx_item_name xA2 ∧ ctx_item_type xA1 ≡ ctx_item_type xA2.
  Instance ctx_item_dist : Dist (ctx_item) := λ n xA1 xA2,
    ctx_item_name xA1 = ctx_item_name xA2 ∧ ctx_item_type xA1 ≡{n}≡ ctx_item_type xA2.
  Lemma ctx_item_ofe_mixin : OfeMixin (ctx_item).
  Proof.
    by apply (iso_ofe_mixin (A:=prodO (leibnizO binder) (lttyO))
      (λ xA, (ctx_item_name xA, ctx_item_type xA))).
  Qed.
  Canonical Structure ctx_itemO := Ofe (ctx_item) ctx_item_ofe_mixin.
  Global Instance ctx_item_type_ne : NonExpansive (@ctx_item_type).
  Proof. by intros n ?? [??]. Qed.
  Global Instance ctx_item_type_proper : Proper ((≡) ==> (≡)) (@ctx_item_type).
  Proof. by intros ?? [??]. Qed.
End ctx_item_ofe.

Notation ctx := (list ctx_item).

Definition ctx_filter_eq (x : binder) : ctx → ctx :=
  filter (λ xA, x = ctx_item_name xA).
Definition ctx_filter_ne (x : binder) : ctx → ctx :=
  filter (λ xA, x ≠ ctx_item_name xA).
Arguments ctx_filter_eq !_ !_ / : simpl nomatch.
Arguments ctx_filter_ne !_ !_ / : simpl nomatch.
(** TODO: Move to std++, together with some lemmas about filter that can be
factored out. *)
Arguments filter _ _ _ _ _ !_ / : simpl nomatch.

Global Instance ctx_lookup : Lookup string ltty ctx := λ x Γ,
  match ctx_filter_eq x Γ with
  | [CtxItem _ A] => Some A
  | _ => None
  end.

Definition ctx_overwrite (b : binder) (A : ltty) (Γ : ctx) : ctx :=
  CtxItem b A :: ctx_filter_ne b Γ.

Definition ctx_anonymize (b : binder) : ctx → ctx :=
  fmap (λ xA, if decide (ctx_item_name xA = b)
              then CtxItem BAnon (ctx_item_type xA)
              else xA).

Definition ctx_cons (b : binder) (A : ltty) (Γ : ctx) : ctx :=
  CtxItem b A :: ctx_anonymize b Γ.

Definition ctx_ltyped (vs : gmap string val) (Γ : ctx) : aProp :=
  [∗ list] xA ∈ Γ, ∃ v,
    ⌜⌜if ctx_item_name xA is BNamed x then vs !! x = Some v else True⌝⌝ ∗
    ltty_car (ctx_item_type xA) v.
Global Instance: Params (@ctx_ltyped) 1 := {}.

Definition ctx_le (Γ1 Γ2 : ctx) : aProp :=
  tc_opaque (■ ∀ vs, ctx_ltyped vs Γ1 -∗ ctx_ltyped vs Γ2)%I.
Infix "<ctx:" := ctx_le (at level 70) : bi_scope.
Notation "Γ1 <ctx: Γ2" := (⊢ Γ1 <ctx: Γ2) (at level 70) : type_scope.

Section ctx.
  Implicit Types A : ltty.
  Implicit Types Γ : ctx.

  (** ctx_filter *)
  Lemma ctx_filter_eq_perm Γ x : Γ ≡ₚ ctx_filter_eq x Γ ++ ctx_filter_ne x Γ.
  Proof.
    rewrite /ctx_filter_eq /ctx_filter_ne.
    induction Γ as [|[y A] Γ IH]; simpl; [done|].
    rewrite filter_cons. case_decide.
    - rewrite filter_cons_False /=; last naive_solver. by rewrite -IH.
    - rewrite filter_cons_True /=; last naive_solver.
      by rewrite -Permutation_middle -IH.
  Qed.

  Lemma ctx_filter_eq_cons (Γ : ctx) (x:string) A :
    ctx_filter_eq x (CtxItem x A :: Γ) = CtxItem x A :: ctx_filter_eq x Γ.
  Proof. rewrite /ctx_filter_eq filter_cons_True; naive_solver. Qed.
  Lemma ctx_filter_eq_cons_ne Γ x y A :
    x ≠ y →
    ctx_filter_eq x (CtxItem y A :: Γ) = ctx_filter_eq x Γ.
  Proof. intros. rewrite /ctx_filter_eq filter_cons_False; naive_solver. Qed.

  Lemma elem_of_ctx_filter_ne Γ x y B :
    CtxItem y B ∈ ctx_filter_ne x Γ → x ≠ y.
  Proof. intros ?%list_elem_of_filter. naive_solver. Qed.

  Lemma ctx_filter_ne_cons Γ x A :
    ctx_filter_ne x (CtxItem x A :: Γ) = ctx_filter_ne x Γ.
  Proof. rewrite /ctx_filter_ne filter_cons_False; naive_solver. Qed.
  Lemma ctx_filter_ne_cons_ne Γ x y A :
    x ≠ y →
    ctx_filter_ne x (CtxItem y A :: Γ) = CtxItem y A :: ctx_filter_ne x Γ.
  Proof. intros. rewrite /ctx_filter_ne filter_cons_True; naive_solver. Qed.

  Lemma ctx_filter_ne_idemp Γ x :
    ctx_filter_ne x (ctx_filter_ne x Γ) = ctx_filter_ne x Γ.
  Proof.
    induction Γ as [|[y A] Γ HI]; [done|].
    destruct (decide (x = y)) as [->|].
    + rewrite ctx_filter_ne_cons. apply HI.
    + rewrite ctx_filter_ne_cons_ne // ctx_filter_ne_cons_ne //.
      f_equiv. apply HI.
  Qed.

  Lemma ctx_filter_eq_ne_nil (Γ : ctx) x :
    ctx_filter_eq x (ctx_filter_ne x Γ) = [].
  Proof.
    induction Γ as [|[y A] Γ HI]; [done|].
    destruct (decide (x = y)) as [-> | ].
    + rewrite ctx_filter_ne_cons. apply HI.
    + rewrite ctx_filter_ne_cons_ne // ctx_filter_eq_cons_ne //.
  Qed.

  Lemma ctx_lookup_perm Γ (x : string) A:
    Γ !! x = Some A →
    Γ ≡ₚ CtxItem x A :: ctx_filter_ne x Γ.
  Proof.
    rewrite /lookup /ctx_lookup=> ?.
    destruct (ctx_filter_eq x Γ) as [|[x' ?] [|??]] eqn:Hx; simplify_eq/=.
    assert (CtxItem x' A ∈ ctx_filter_eq x Γ)
      as [? _]%list_elem_of_filter; simplify_eq/=.
    { rewrite Hx. set_solver. }
    by rewrite {1}(ctx_filter_eq_perm Γ x) Hx.
  Qed.

  Lemma ctx_insert_lookup Γ (x : string) A :
    (CtxItem x A :: (ctx_filter_ne x Γ)) !! x = Some A.
  Proof.
    by rewrite /lookup /ctx_lookup ctx_filter_eq_cons ctx_filter_eq_ne_nil.
  Qed.

  (** ctx typing *)
  Global Instance ctx_ltyped_Permutation vs :
    Proper ((≡ₚ) ==> (⊣⊢)) (ctx_ltyped vs).
  Proof. intros Γ Γ' HΓ. by rewrite /ctx_ltyped HΓ. Qed.
  Global Instance ctx_ltyped_ne vs : NonExpansive (ctx_ltyped vs).
  Proof.
    intros n Γ Γ' HΓ. rewrite /ctx_ltyped.
    apply big_opL_gen_proper_2; [done|apply _|]. intros k.
    assert (Γ !! k ≡{n}≡ Γ' !! k) as HΓk by (by rewrite HΓ).
    case: HΓk=> // -[x1 A1] [x2 A2] [/= -> ?]. by repeat f_equiv.
  Qed.
  Global Instance ctx_ltyped_proper vs : Proper ((≡) ==> (≡)) (ctx_ltyped vs).
  Proof. apply (ne_proper _). Qed.

  Lemma ctx_ltyped_nil vs : ctx_ltyped vs [] ⊣⊢ emp.
  Proof. done. Qed.

  Lemma ctx_ltyped_app Γ1 Γ2 vs :
    ctx_ltyped vs (Γ1 ++ Γ2) ⊣⊢ ctx_ltyped vs Γ1 ∗ ctx_ltyped vs Γ2.
  Proof. apply big_opL_app. Qed.

  Lemma ctx_ltyped_cons_named Γ vs (x : string) A :
    ctx_ltyped vs (CtxItem x A :: Γ) ⊣⊢ ∃ v,
      ⌜⌜ vs !! x = Some v ⌝⌝ ∗ ltty_car A v ∗ ctx_ltyped vs Γ.
  Proof.
    iSplit; [by iIntros "[HA $]"|].
    iDestruct 1 as (v ?) "[HA $] /="; eauto.
  Qed.

  Lemma ctx_ltyped_anonymize Γ vs x v :
    ctx_ltyped vs Γ -∗
    ctx_ltyped (binder_insert x v vs) (ctx_anonymize x Γ).
  Proof.
    iInduction Γ as [|[y B] Γ] "IH"; simpl; [by rewrite !ctx_ltyped_nil; auto|].
    iIntros "[(%w&%Hq&HB) HΓ]". iSplitR "HΓ"; [|by iApply "IH"].
    case_decide; simplify_eq/=; eauto with iFrame.
    iExists w. iFrame "HB".
    destruct x, y; rewrite /= ?lookup_insert_ne //; auto with congruence.
  Qed.

  Lemma ctx_ltyped_anonymize' Γ vs x v :
    ctx_ltyped (binder_insert x v vs) Γ -∗
    ctx_ltyped vs (ctx_anonymize x Γ).
  Proof.
    iInduction Γ as [|[y B] Γ] "IH"; simpl; [by rewrite !ctx_ltyped_nil; auto|].
    iIntros "[(%w&%Hq&HB) HΓ]". iSplitR "HΓ"; [|by iApply "IH"].
    case_decide; simplify_eq/=; eauto with iFrame.
    iExists w. iFrame "HB".
    destruct x, y; revert Hq; rewrite /= ?lookup_insert_ne //; auto with congruence.
  Qed.

  Lemma ctx_ltyped_cons Γ vs x A v :
    ltty_car A v -∗
    ctx_ltyped vs Γ -∗
    ctx_ltyped (binder_insert x v vs) (ctx_cons x A Γ).
  Proof.
    iIntros "HA HΓ". rewrite /ctx_cons. iSplitL "HA".
    - iExists v. iFrame "HA". destruct x; by rewrite /= ?lookup_insert_eq.
    - by iApply ctx_ltyped_anonymize.
  Qed.

  Lemma ctx_ltyped_overwrite Γ vs x A v :
    ltty_car A v -∗
    ctx_ltyped vs (ctx_filter_ne x Γ) -∗
    ctx_ltyped (binder_insert x v vs) (ctx_overwrite x A Γ).
  Proof.
    iIntros "HA HΓ". iSplitL "HA".
    { iExists v. iFrame "HA". destruct x; by rewrite /= ?lookup_insert_eq. }
    iApply (big_sepL_impl with "HΓ").
    iIntros "!>" (k [y B] ?%list_elem_of_lookup_2%elem_of_ctx_filter_ne).
    iIntros "(%w & %Hw & HB)"; iExists w; iFrame "HB".
    destruct x, y; rewrite /= ?lookup_insert_ne; auto with congruence.
  Qed.

  (** Context subtyping *)
  Global Instance ctx_le_plain Γ1 Γ2 : Plain (Γ1 <ctx: Γ2).
  Proof. rewrite /ctx_le /=. apply _. Qed.
  Global Instance ctx_le_absorbing Γ1 Γ2 : Absorbing (Γ1 <ctx: Γ2).
  Proof. rewrite /ctx_le /=. apply _. Qed.

  Global Instance ctx_le_Permutation : Proper ((≡ₚ) ==> (≡ₚ) ==> (≡)) ctx_le.
  Proof.
    intros Γ1 Γ1' HΓ1 Γ2 Γ2' HΓ2. rewrite /ctx_le /=.
    setoid_rewrite HΓ1; by setoid_rewrite HΓ2.
  Qed.
  Global Instance ctx_le_ne : NonExpansive2 ctx_le.
  Proof. solve_proper. Qed.
  Global Instance ctx_le_proper : Proper ((≡) ==> (≡) ==> (≡)) ctx_le.
  Proof. apply (ne_proper_2 _). Qed.

  Lemma ctx_le_refl Γ : Γ <ctx: Γ.
  Proof. iIntros (vs); auto. Qed.
  Lemma ctx_le_trans Γ1 Γ2 Γ3 : Γ1 <ctx: Γ2 -∗ Γ2 <ctx: Γ3 -∗ Γ1 <ctx: Γ3.
  Proof.
    iIntros "#H1 #H2 !>" (vs) "Hvs". iApply "H2". by iApply "H1".
  Qed.
  Lemma ctx_le_app Γ1 Γ2 Γ1' Γ2' :
    Γ1 <ctx: Γ2 -∗ Γ1' <ctx: Γ2' -∗ Γ1 ++ Γ1' <ctx: Γ2 ++ Γ2'.
  Proof.
    iIntros "#H #H' !>" (vs) "Hvs".
    iDestruct (ctx_ltyped_app with "Hvs") as "[Hvs1 Hvs2]".
    iApply ctx_ltyped_app. iSplitL "Hvs1"; [by iApply "H"|by iApply "H'"].
  Qed.
  Lemma ctx_le_cons x Γ1 Γ2 A1 A2 :
    A1 <: A2 -∗ Γ1 <ctx: Γ2 -∗ CtxItem x A1 :: Γ1 <ctx: CtxItem x A2 :: Γ2.
  Proof.
    iIntros "#H #H'". iApply (ctx_le_app [_] [_] with "[H] H'").
    iIntros (vs) "!> [(%v & Hv & HA) _]". iSplitL; [|done].
    iExists v. iFrame "Hv". by iApply "H".
  Qed.
  Lemma ctx_le_cons_cons_ne x y Γ A1 A2 :
    CtxItem x A1 :: CtxItem y A2 :: Γ <ctx:
    CtxItem y A2 :: CtxItem x A1 :: Γ.
  Proof.
    iIntros (vs) "!> HΓ". rewrite /ctx_ltyped !big_sepL_cons.
    iDestruct "HΓ" as "(HA1 & HA2 & HΓ)". iFrame.
  Qed.
  Lemma ctx_le_copy x A :
    [CtxItem x A] <ctx: [CtxItem x A; CtxItem x (copy- A)].
  Proof.
    iIntros "!>" (vs) "[(%v & %Hv & HA) _]".
    iAssert (ltty_car (copy- A) v) as "#HAm".
    { iApply bi.persistent_absorbingly_affinely_2. by iApply coreP_intro. }
    iSplitL "HA"; [iExists v; by eauto|]. iSplitL; [iExists v|]; eauto.
  Qed.
  Lemma ctx_le_copyable x A :
    lty_copyable A -∗
    [CtxItem x A] <ctx: [CtxItem x A; CtxItem x A].
  Proof.
    iIntros "H". iApply ctx_le_trans; [iApply ctx_le_copy|].
    iApply ctx_le_cons; [iApply lty_le_refl|].
    iApply (ctx_le_cons with "[H]").
    - by iApply lty_le_copy_inv_elim_copyable.
    - iApply ctx_le_refl.
  Qed.
  Lemma ctx_le_drop x A :
    lty_copyable A -∗
    [CtxItem x A] <ctx: [].
  Proof.
    iIntros "#H" (vs) "!>". rewrite /ctx_ltyped /=. iIntros "[(%v&_&HA) _]".
    by iDestruct ("H" with "HA") as "_".
  Qed.

End ctx.
