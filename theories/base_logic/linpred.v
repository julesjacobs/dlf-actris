From iris.algebra Require Export cmra.
From iris.proofmode Require Export proofmode.
From iris.si_logic Require Export bi.
From dlfactris.prelude Require Export prelude.

Record linPred (M : ucmra) := LinPred {
  linPred_at : M → siProp;
  linPred_at_ne : NonExpansive linPred_at;
}.
Global Existing Instance linPred_at_ne.
Arguments LinPred {_} _ _.
Arguments linPred_at {_} _ _.
Bind Scope bi_scope with linPred.

Section ofe.
  Context {M : ucmra}.

  Definition linPred_internal_eq (P Q : linPred M) : siProp :=
    ∀ x, ✓ x → linPred_at P x ↔ linPred_at Q x.
  Local Instance linPred_dist_instance : Dist (linPred M) :=
    quotient_dist linPred_internal_eq.

  Local Definition linPred_equiv_def : Equiv (linPred M) := λ P Q,
    ⊢ linPred_internal_eq P Q.
  Local Definition linPred_equiv_aux : seal (@linPred_equiv_def).
  Proof. by eexists. Qed.
  Instance linPred_equiv_instance : Equiv (linPred M) := linPred_equiv_aux.(unseal).
  Local Definition linPred_equiv_unseal :
    equiv = linPred_equiv_def := linPred_equiv_aux.(seal_eq).

  Lemma linPred_ofe_mixin : OfeMixin (linPred M).
  Proof.
    apply quotient_ofe_mixin.
    - by rewrite linPred_equiv_unseal.
    - iIntros (P x); auto.
    - iIntros (P Q) "#H %x #Hx". iSplit; iIntros "?"; by iApply "H".
    - iIntros (P Q R) "#[H1 H2] %x #Hx". iSplit; iIntros "?".
      + iApply ("H2" with "[//]"). by iApply "H1".
      + iApply ("H1" with "[//]"). by iApply "H2".
  Qed.
  Canonical Structure linPredO : ofe := Ofe (linPred M) linPred_ofe_mixin.

  Global Instance linPred_at_proper (P : linPred M) :
    Proper ((≡) ==> (≡)) (linPred_at P).
  Proof. apply: ne_proper. Qed.

  Lemma linPred_equivI (P Q : linPred M) :
    P ≡ Q ⊣⊢ ∀ x, ✓ x → linPred_at P x ↔ linPred_at Q x.
  Proof.
    (* FIXME: using the lemma quotient_equiv is broken. *)
    change (P ≡ Q ⊣⊢ linPred_internal_eq P Q).
    rewrite /internal_eq. by siProp.unseal.
  Qed.

  (** OFE quotients do not give a COFE. We instead show that [linPredO] is a COFE
  by constructing an isomorphism to [ { P : M -n> siProp | P x ⊢ ✓ x } ]. *)
  Global Instance linPred_cofe : Cofe linPredO.
  Proof.
    set (A := M -n> siProp).
    set (ok (P : A) := ∀ x, P x ⊢ ✓ x).
    set (g (P : linPred M) (x : M) := (linPred_at P x ∧ ✓ x)%I : siProp).
    assert (∀ P, NonExpansive (g P)) by solve_proper.
    refine (iso_cofe_subtype' ok (λ P _, LinPred P _) (λ P, OfeMor (g P)) _ _ _ _).
    - iIntros (P x) "[? $]".
    - intros n P1 P2. split; apply (internal_eq_entails (PROP:=siProp));
        rewrite ofe_morO_equivI /g /=.
      + iIntros "#H" (x). iApply plainly.prop_ext; iIntros "!>".
        rewrite  linPred_equivI. iSplit; iIntros "#[? $]"; by iApply "H".
      + iIntros "H". setoid_rewrite internal_eq_iff.
        iApply linPred_equivI; iIntros (x) "#Hx"; iSplit; iIntros "HP".
        * iDestruct ("H" $! x) as "[#H _]". iDestruct ("H" with "[$]") as "[$ _]".
        * iDestruct ("H" $! x) as "[_ #H]". iDestruct ("H" with "[$]") as "[$ _]".
    - intros P Hok x. iSplit.
      + iIntros "[? _] //".
      + iIntros "?"; iSplit; [done|]. by iApply Hok.
    - apply limit_preserving_forall=> x.
      apply bi.limit_preserving_entails; solve_proper.
  Qed.
End ofe.

Arguments linPredO : clear implicits.

Program Definition linPred_map {M1 M2 : ucmra} (f : M2 -n> M1)
    `{!CmraMorphism f} (P : linPred M1) : linPred M2 :=
  {| linPred_at x := linPred_at P (f x) |}.
Next Obligation.
  intros M1 M2 f ? P. apply (ne_internal_eq (PROP:=siProp)).
  iIntros (x1 x2) "#Hx". by iRewrite "Hx".
Qed.

Global Instance linPred_map_ne {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} : NonExpansive (linPred_map f).
Proof.
  apply (ne_internal_eq (PROP:=siProp)). iIntros (P1 P2) "#HP".
  rewrite !linPred_equivI.
  iIntros (x) "#Hx"; iSplit; iIntros "?"; iApply "HP";
    try iApply cmra_morphism_validI; done.
Qed.
Lemma linPred_map_id {M : ucmra} (P : linPred M) : linPred_map cid P ≡ P.
Proof. rewrite linPred_equiv_unseal. iIntros (x) "#Hx /="; auto. Qed.
Lemma linPred_map_compose {M1 M2 M3 : ucmra} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : linPred M3) :
  linPred_map (g ◎ f) P ≡ linPred_map f (linPred_map g P).
Proof. rewrite linPred_equiv_unseal. iIntros (x) "#Hx /="; auto. Qed.
Lemma linPred_map_ext {M1 M2 : ucmra} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g} :
  (∀ x, f x ≡ g x) → ∀ x, linPred_map f x ≡ linPred_map g x.
Proof.
  rewrite linPred_equiv_unseal. iIntros (Hfg P x) "#Hx /=". rewrite Hfg. auto.
Qed.

Definition linPredO_map {M1 M2 : ucmra} (f : M2 -n> M1) `{!CmraMorphism f} :
  linPred M1 -n> linPred M2 := OfeMor (linPred_map f).
Lemma linPredO_map_ne {M1 M2 : ucmra} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → linPredO_map f ≡{n}≡ linPredO_map g.
Proof.
  revert n. apply (internal_eq_entails (PROP:=siProp)).
  iIntros "#Hfg". rewrite !ofe_morO_equivI; iIntros (P).
  iApply linPred_equivI; iIntros (x) "#Hx /=". iRewrite ("Hfg" $! x). auto.
Qed.

Program Definition linPredOF (F : urFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := linPred (urFunctor_car F B A);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    linPredO_map (urFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply linPredO_map_ne, urFunctor_map_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A ? B ? P; simpl. rewrite -{2}(linPred_map_id P).
  apply linPred_map_ext=>y. by rewrite urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' P; simpl.
  rewrite -linPred_map_compose.
  apply linPred_map_ext=>y; apply urFunctor_map_compose.
Qed.

Global Instance linPredOF_contractive F :
  urFunctorContractive F → oFunctorContractive (linPredOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply linPredO_map_ne, urFunctor_map_contractive.
  destruct HPQ as [HPQ]. constructor. intros ??.
  split; by eapply HPQ.
Qed.

(** BI canonical structure *)
Module Export linPred_defs.
Section linPred_defs.
  Context {M : ucmra}.
  Notation linPred := (linPred M).

  Local Definition linPred_entails_def (P1 P2 : linPred) := ∀ x,
    ✓ x ⊢ linPred_at P1 x → linPred_at P2 x.
  Local Definition linPred_entails_aux : seal (@linPred_entails_def).
  Proof. by eexists. Qed.
  Definition linPred_entails := linPred_entails_aux.(unseal).
  Local Definition linPred_entails_unseal :
    @linPred_entails = _ := linPred_entails_aux.(seal_eq).

  Local Definition linPred_si_pure_def (Pi : siProp) : linPred :=
    {| linPred_at _ := Pi |}.
  Local Definition linPred_si_pure_aux : seal (@linPred_si_pure_def).
  Proof. by eexists. Qed.
  Definition linPred_si_pure := linPred_si_pure_aux.(unseal).
  Local Definition linPred_si_pure_unseal :
    @linPred_si_pure = _ := linPred_si_pure_aux.(seal_eq).

  Local Definition linPred_si_emp_valid_def (P : linPred) : siProp :=
    linPred_at P ε.
  Local Definition linPred_si_emp_valid_aux : seal (@linPred_si_emp_valid_def).
  Proof. by eexists. Qed.
  Definition linPred_si_emp_valid := linPred_si_emp_valid_aux.(unseal).
  Local Definition linPred_si_emp_valid_unseal :
    @linPred_si_emp_valid = _ := linPred_si_emp_valid_aux.(seal_eq).

  Local Program Definition linPred_emp_def : linPred :=
    {| linPred_at x := (x ≡ ε)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_emp_aux : seal (@linPred_emp_def).
  Proof. by eexists. Qed.
  Definition linPred_emp := linPred_emp_aux.(unseal).
  Local Definition linPred_emp_unseal :
    @linPred_emp = _ := linPred_emp_aux.(seal_eq).

  Local Definition linPred_pure_def (φ : Prop) : linPred :=
    {| linPred_at _ := ⌜ φ ⌝%I |}.
  Local Definition linPred_pure_aux : seal (@linPred_pure_def).
  Proof. by eexists. Qed.
  Definition linPred_pure := linPred_pure_aux.(unseal).
  Local Definition linPred_pure_unseal :
    @linPred_pure = _ := linPred_pure_aux.(seal_eq).

  Local Program Definition linPred_and_def (P Q : linPred) : linPred :=
    {| linPred_at x := (linPred_at P x ∧ linPred_at Q x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_and_aux : seal (@linPred_and_def).
  Proof. by eexists. Qed.
  Definition linPred_and := linPred_and_aux.(unseal).
  Local Definition linPred_and_unseal :
    @linPred_and = _ := linPred_and_aux.(seal_eq).

  Local Program Definition linPred_or_def (P Q : linPred) : linPred :=
    {| linPred_at x := (linPred_at P x ∨ linPred_at Q x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_or_aux : seal (@linPred_or_def).
  Proof. by eexists. Qed.
  Definition linPred_or := linPred_or_aux.(unseal).
  Local Definition linPred_or_unseal : @linPred_or = _ := linPred_or_aux.(seal_eq).

  Local Program Definition linPred_impl_def (P Q : linPred) : linPred :=
    {| linPred_at x := (linPred_at P x → linPred_at Q x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_impl_aux : seal (@linPred_impl_def).
  Proof. by eexists. Qed.
  Definition linPred_impl := linPred_impl_aux.(unseal).
  Local Definition linPred_impl_unseal :
    @linPred_impl = _ := linPred_impl_aux.(seal_eq).

  Local Program Definition linPred_forall_def {A} (Φ : A → linPred) : linPred :=
    {| linPred_at x := (∀ a, linPred_at (Φ a) x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_forall_aux : seal (@linPred_forall_def).
  Proof. by eexists. Qed.
  Definition linPred_forall := linPred_forall_aux.(unseal).
  Local Definition linPred_forall_unseal :
    @linPred_forall = _ := linPred_forall_aux.(seal_eq).

  Local Program Definition linPred_exist_def {A} (Φ : A → linPred) : linPred :=
    {| linPred_at x := (∃ a, linPred_at (Φ a) x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_exist_aux : seal (@linPred_exist_def).
  Proof. by eexists. Qed.
  Definition linPred_exist := linPred_exist_aux.(unseal).
  Local Definition linPred_exist_unseal :
    @linPred_exist = _ := linPred_exist_aux.(seal_eq).

  Local Program Definition linPred_sep_def (P Q : linPred) : linPred :=
    {| linPred_at x := (∃ x1 x2, x ≡ x1 ⋅ x2 ∧
                                 linPred_at P x1 ∧ linPred_at Q x2)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_sep_aux : seal (@linPred_sep_def).
  Proof. by eexists. Qed.
  Definition linPred_sep := linPred_sep_aux.(unseal).
  Local Definition linPred_sep_unseal : @linPred_sep = _ := linPred_sep_aux.(seal_eq).

  Local Program Definition linPred_wand_def (P Q : linPred) : linPred :=
    {| linPred_at x := (∀ x', ✓ (x ⋅ x') →
                              linPred_at P x' → linPred_at Q (x ⋅ x'))%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_wand_aux : seal (@linPred_wand_def).
  Proof. by eexists. Qed.
  Definition linPred_wand := linPred_wand_aux.(unseal).
  Local Definition linPred_wand_unseal : @linPred_wand = _ := linPred_wand_aux.(seal_eq).

  Local Definition linPred_persistently_def (P : linPred) : linPred :=
    {| linPred_at x := linPred_at P ε |}.
  Local Definition linPred_persistently_aux : seal (@linPred_persistently_def).
  Proof. by eexists. Qed.
  Definition linPred_persistently := linPred_persistently_aux.(unseal).
  Local Definition linPred_persistently_unseal :
    @linPred_persistently = _ := linPred_persistently_aux.(seal_eq).

  Local Program Definition linPred_later_def (P : linPred) : linPred :=
    {| linPred_at x := (▷ linPred_at P x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_later_aux : seal linPred_later_def.
  Proof. by eexists. Qed.
  Definition linPred_later := linPred_later_aux.(unseal).
  Local Definition linPred_later_unseal :
    linPred_later = _ := linPred_later_aux.(seal_eq).

  Local Program Definition linPred_own_def (x : M) : linPred :=
    {| linPred_at y := (y ≡ x)%I |}.
  Next Obligation. solve_proper. Qed.
  Local Definition linPred_own_aux : seal (@linPred_own_def).
  Proof. by eexists. Qed.
  Definition linPred_own := linPred_own_aux.(unseal).
  Local Definition linPred_own_unseal :
    @linPred_own = _ := linPred_own_aux.(seal_eq).
End linPred_defs.

(** This is not the final collection of unsealing lemmas, below we redefine
[linPred_unseal] to also unfold the BI layer (i.e., the projections of the BI
structures/classes). *)
Definition linPred_unseal :=
  (@linPred_equiv_unseal, @linPred_entails_unseal,
   @linPred_si_pure_unseal, @linPred_si_emp_valid_unseal,
   @linPred_emp_unseal, @linPred_pure_unseal,
   @linPred_and_unseal, @linPred_or_unseal, @linPred_impl_unseal,
   @linPred_forall_unseal, @linPred_exist_unseal,
   @linPred_sep_unseal, @linPred_wand_unseal,
   @linPred_persistently_unseal, @linPred_later_unseal, @linPred_own_unseal).
End linPred_defs.

Section instances.
  Context (M : ucmra).

  Lemma linPred_bi_mixin :
    BiMixin (PROP:=linPred M)
      linPred_entails linPred_emp linPred_pure linPred_and linPred_or
      linPred_impl linPred_forall linPred_exist linPred_sep linPred_wand.
  Proof.
    split; rewrite !linPred_unseal.
    - split.
      + iIntros (P x); auto.
      + iIntros (P Q R HPQ HQR x) "#Hx #HP".
        iApply (HQR with "[//]"). by iApply HPQ.
    - intros P Q; split.
      + intros HPQ; split; iIntros (x) "#? #?"; by iApply HPQ.
      + iIntros ([H1 H2] x) "#?"; iSplit; [by iApply H1|by iApply H2].
    - iIntros (n φ1 φ2 Hφ). apply equiv_dist, (internal_eq_soundness (PROP:=siProp)).
      rewrite linPred_equivI /=. iIntros (x). rewrite Hφ; auto.
    - apply (ne_2_internal_eq (PROP:=siProp)). iIntros (P1 P2 Q1 Q2) "#[HP HQ]".
      rewrite !linPred_equivI. iIntros (x) "#Hx"; iSplit; iIntros "[??]";
        iSplit; first [by iApply "HP" | by iApply "HQ"].
    - apply (ne_2_internal_eq (PROP:=siProp)). iIntros (P1 P2 Q1 Q2) "#[HP HQ]".
      rewrite !linPred_equivI. iIntros (x) "#Hx"; iSplit; iIntros "[?|?]"; try
        first [by iLeft; iApply "HP" | by iRight; iApply "HQ"].
    - apply (ne_2_internal_eq (PROP:=siProp)). iIntros (P1 P2 Q1 Q2) "#[HP HQ]".
      rewrite !linPred_equivI. iIntros (x) "#Hx"; iSplit; iIntros "#H #?";
        iApply ("HQ" with "[//]"); iApply "H"; by iApply "HP".
    - intros A. apply (ne_internal_eq (PROP:=siProp) (A:=_ -d> _)).
      setoid_rewrite discrete_fun_equivI. setoid_rewrite linPred_equivI.
      iIntros (Φ1 Φ2) "#HΦ %x #Hx /="; iSplit; iIntros "H" (a); by iApply "HΦ".
    - intros A. apply (ne_internal_eq (PROP:=siProp) (A:=_ -d> _)).
      setoid_rewrite discrete_fun_equivI. setoid_rewrite linPred_equivI.
      iIntros (Φ1 Φ2) "#HΦ %x #Hx /="; iSplit;
        iIntros "[%a ?]"; iExists a; by iApply "HΦ".
    - apply (ne_2_internal_eq (PROP:=siProp)). iIntros (P1 P2 Q1 Q2) "#[HP HQ]".
      rewrite !linPred_equivI.
      iIntros (x) "#Hx"; iSplit; iIntros "(%x1 & %x2 & #Hxeq & ? & ?)";
        iRewrite "Hxeq" in "Hx"; iExists x1, x2;
        (iSplit; [done|]); iSplit; first [iApply "HP" | iApply "HQ"];
        first [done|by iApply cmra_validI_op_l|by iApply cmra_validI_op_r].
    - apply (ne_2_internal_eq (PROP:=siProp)). iIntros (P1 P2 Q1 Q2) "#[HP HQ]".
      rewrite !linPred_equivI. iIntros (x) "#Hx"; iSplit; iIntros "#H" (y) "#Hxy ?";
        iApply ("HQ" with "[//]"); iApply ("H" with "[//]"); iApply "HP";
        first [done|by iApply cmra_validI_op_l|by iApply cmra_validI_op_r].
    - iIntros (φ P ? x) "#Hx _ //".
    - iIntros (φ P HP x) "#Hx %Hφ". by iApply HP.
    - iIntros (P Q x) "#Hx [??] //".
    - iIntros (P Q x) "#Hx [??] //".
    - iIntros (P Q R HQ HR x) "#Hx #HP". by iSplit; [iApply HQ|iApply HR].
    - iIntros (P Q x) "#Hx ?". by iLeft.
    - iIntros (P Q x) "#Hx ?". by iRight.
    - iIntros (P Q R HQ HR x) "#Hx #[HP|HQ]"; [by iApply HQ|by iApply HR].
    - iIntros (P Q R H x) "#Hx #HP #HQ". iApply (H with "[//]"). by iSplit.
    - iIntros (P Q R H x) "#Hx #[HP HQ]". by iApply H.
    - iIntros (A P Ψ H x) "#Hx #HP %a". by iApply H.
    - iIntros (A Ψ a x) "#Hx ? //".
    - iIntros (A Ψ a x) "#Hx ?". by iExists a.
    - iIntros (A Ψ Q H x) "#Hx #[%a ?]". by iApply H.
    - iIntros (P P' Q Q' HP HQ x) "#Hx #(%x1 & %x2 & Hxeq & ? & ?)".
      iRewrite "Hxeq" in "Hx".
      iExists x1, x2. iSplit; [done|]. iSplit; [iApply HP|iApply HQ];
        first [done|by iApply cmra_validI_op_l|by iApply cmra_validI_op_r].
    - iIntros (P x) "#Hx #HP". iExists ε, x. rewrite left_id. auto.
    - iIntros (P x) "#Hx #(%x1 & %x2 & Hxeq & Hx1 & ?)".
      iRewrite "Hx1" in "Hxeq". rewrite left_id. by iRewrite "Hxeq".
    - iIntros (P Q x) "_ #(%x1 & %x2 & Hxeq & Hx1 & ?)".
      iExists x2, x1. rewrite comm. auto.
    - iIntros (P Q R x) "_ #(%x1 & %x2 & Hxeq & (%x2a & %x2b & Hx1eq & ? & ?) & ?)".
      iExists x2a, (x2b ⋅ x2).
      rewrite (assoc op). iRewrite -"Hx1eq". do 2 (iSplit; [done|]).
      iExists x2b, x2. auto.
    - iIntros (P Q R H x) "#Hx #HP %y #Hxy #HQ". iApply (H with "[//]").
      iExists x, y; auto.
    - iIntros (P Q R H x) "#Hx #(%x1 & %x2 & Hxeq & ? & ?)".
      iRewrite "Hxeq". iRewrite "Hxeq" in "Hx".
      iApply H; first [done|by iApply cmra_validI_op_l].
  Qed.

  Lemma linPred_bi_persistently_mixin :
    BiPersistentlyMixin (PROP:=linPred M)
      linPred_entails linPred_emp linPred_and linPred_exist linPred_sep
      linPred_persistently.
  Proof.
    split; rewrite !linPred_unseal.
    - apply (ne_internal_eq (PROP:=siProp)). iIntros (P1 P2) "#HP".
      rewrite !linPred_equivI. iIntros (x) "#Hx"; iSplit; iIntros "#H";
        iApply "HP"; first [done|iApply ucmra_unit_validI].
    - iIntros (P Q H x) "_". iApply H. iApply ucmra_unit_validI.
    - iIntros (P x) "_ HP //".
    - iIntros (x) "_ Hx". by iRewrite "Hx".
    - iIntros (P Q x) "_ #[??]". by iSplit.
    - iIntros (A Ψ x) "_ HΨ //".
    - iIntros (P Q x) "_ #(%x1 & %x2 & Hxeq & ? & ?) //".
    - iIntros (P Q x) "_ #[??]". iExists ε, x. rewrite left_id. auto.
  Qed.

  Lemma linPred_bi_later_mixin :
    BiLaterMixin (PROP:=linPred M)
      linPred_entails linPred_pure linPred_or linPred_impl
      linPred_forall linPred_exist linPred_sep
      linPred_persistently linPred_later.
  Proof.
    split; rewrite !linPred_unseal.
    - apply (ne_internal_eq (PROP:=siProp)). iIntros (P1 P2) "#HP".
      rewrite !linPred_equivI.
      iIntros (x) "#Hx"; iSplit; iIntros "#H !>"; by iApply "HP".
    - iIntros (P Q H x) "#Hx HP !>". by iApply H.
    - iIntros (P x) "_ HP !> //".
    - iIntros (A Φ x) "_ HΦ !> //".
    - iIntros (A Φ x) "_ H /=". by iApply bi.later_exist_false.
    - pose proof (populate ε : Inhabited M).
      iIntros (P Q x) "#Hx /= #(%x1 & %x2 & ? & ? & ?)".
      iDestruct (cmra_later_opI x x1 x2 with "[]")
        as (z1 z2) "(Hx' & Hz1 & Hz2)"; first auto.
      iExists z1, z2; iSplit; [done|].
      iSplit; iNext; [by iRewrite "Hz1"|by iRewrite "Hz2"].
    - iIntros (P Q x) "_ (%x1 & %x2 & ? & ? & ?) !> /=". auto.
    - iIntros (P x) "_ HP !> //".
    - iIntros (P x) "_ HP //".
    - iIntros (P x) "_ HP /=". by iApply bi.later_false_em.
  Qed.

  Canonical Structure linPredI : bi :=
    {| bi_ofe_mixin := linPred_ofe_mixin;
       bi_bi_mixin := linPred_bi_mixin;
       bi_bi_persistently_mixin := linPred_bi_persistently_mixin;
       bi_bi_later_mixin := linPred_bi_later_mixin |}.

  (** We restate the unsealing lemmas so that they also unfold the BI layer. The
  sealing lemmas are partially applied so that they also work under binders. *)
  Local Lemma linPred_entails_unseal :
    bi_entails = @linPred_defs.linPred_entails_def M.
  Proof. by rewrite -linPred_defs.linPred_entails_unseal. Qed.
  Local Lemma linPred_emp_unseal :
    bi_emp = @linPred_defs.linPred_emp_def M.
  Proof. by rewrite -linPred_defs.linPred_emp_unseal. Qed.
  Local Lemma linPred_pure_unseal :
    bi_pure = @linPred_defs.linPred_pure_def M.
  Proof. by rewrite -linPred_defs.linPred_pure_unseal. Qed.
  Local Lemma linPred_and_unseal :
    bi_and = @linPred_defs.linPred_and_def M.
  Proof. by rewrite -linPred_defs.linPred_and_unseal. Qed.
  Local Lemma linPred_or_unseal :
    bi_or = @linPred_defs.linPred_or_def M.
  Proof. by rewrite -linPred_defs.linPred_or_unseal. Qed.
  Local Lemma linPred_impl_unseal :
    bi_impl = @linPred_defs.linPred_impl_def M.
  Proof. by rewrite -linPred_defs.linPred_impl_unseal. Qed.
  Local Lemma linPred_forall_unseal :
    @bi_forall _ = @linPred_defs.linPred_forall_def M.
  Proof. by rewrite -linPred_defs.linPred_forall_unseal. Qed.
  Local Lemma linPred_exist_unseal :
    @bi_exist _ = @linPred_defs.linPred_exist_def M.
  Proof. by rewrite -linPred_defs.linPred_exist_unseal. Qed.
  Local Lemma linPred_sep_unseal :
    bi_sep = @linPred_defs.linPred_sep_def M.
  Proof. by rewrite -linPred_defs.linPred_sep_unseal. Qed.
  Local Lemma linPred_wand_unseal :
    bi_wand = @linPred_defs.linPred_wand_def M.
  Proof. by rewrite -linPred_defs.linPred_wand_unseal. Qed.
  Local Lemma linPred_persistently_unseal :
    bi_persistently = @linPred_defs.linPred_persistently_def M.
  Proof. by rewrite -linPred_defs.linPred_persistently_unseal. Qed.
  Local Lemma linPred_later_unseal :
    bi_later = @linPred_defs.linPred_later_def M.
  Proof. by rewrite -linPred_defs.linPred_later_unseal. Qed.

  (** This definition only includes the unseal lemmas for the [bi] connectives.
  After we have defined the right class instances, we define [linPred_unseal],
  which also includes [<si_pure>], etc. *)
  Local Definition linPred_unseal_bi :=
    (@linPred_equiv_unseal, linPred_entails_unseal,
    linPred_emp_unseal, linPred_pure_unseal, linPred_and_unseal,
    linPred_or_unseal, linPred_impl_unseal, linPred_forall_unseal,
    linPred_exist_unseal, linPred_sep_unseal, linPred_wand_unseal,
    linPred_persistently_unseal, linPred_later_unseal).

  Global Instance linPred_bi_persistently_forall :
    BiPersistentlyForall linPredI.
  Proof. intros A Φ. rewrite !linPred_unseal_bi. iIntros (x) "#Hx #H //". Qed.

  Global Instance linPred_bi_pure_forall :
    BiPureForall linPredI.
  Proof.
    intros A φ. rewrite !linPred_unseal_bi. iIntros (x) "#Hx #H /= %a //".
  Qed.

  Lemma linPred_sbi_mixin :
    SbiMixin linPredI linPred_si_pure linPred_si_emp_valid.
  Proof.
    split; rewrite /Absorbing /bi_absorbingly /bi_affinely
      /si_pure /si_emp_valid
      ?(linPred_unseal_bi, linPred_defs.linPred_si_pure_unseal,
        linPred_defs.linPred_si_emp_valid_unseal)
      /linPred_defs.linPred_si_emp_valid_def.
    - apply (ne_internal_eq (PROP:=siProp)). iIntros (Pi1 Pi2) "#HPi".
      rewrite linPred_equivI /=. iIntros (x) "_ /=". iRewrite "HPi"; auto.
    - apply (ne_internal_eq (PROP:=siProp)). iIntros (P1 P2) "#HP".
      rewrite linPred_equivI. iApply plainly.prop_ext; iIntros "!>".
      iApply "HP". iApply ucmra_unit_validI.
    - iIntros (Pi Qi H x) "_ HPi /=". by iApply H.
    - iIntros (P Q H). iApply H. iApply ucmra_unit_validI.
    - iIntros (Pi Qi x) "_ H //".
    - iIntros (A Φi x) "_ H //".
    - iIntros (Pi x) "/="; auto.
    - iIntros (Pi x) "/= _ (%x1 & %x2 & ? & ? & ?) //".
    - iIntros (P) "/="; auto.
    - iIntros (P) "/="; auto.
    - iIntros (Pi) "/="; auto.
    - iIntros (P x) "/="; auto.
  Qed.

  Lemma linPred_sbi_prop_ext_mixin :
    SbiPropExtMixin linPredI linPred_si_emp_valid.
  Proof.
    apply sbi_prop_ext_mixin_make=> P Q.
    rewrite /bi_wand_iff /si_emp_valid
      ?(linPred_unseal_bi, linPred_defs.linPred_si_emp_valid_unseal) /=.
    rewrite linPred_equivI /=. iIntros "#[H1 H2] %x #?".
    iSpecialize ("H1" $! x); iSpecialize ("H2" $! x); rewrite left_id.
    iSplit; [by iApply "H1"|by iApply "H2"].
  Qed.

  Global Instance linPred_sbi : Sbi linPredI :=
    {| sbi_sbi_mixin := linPred_sbi_mixin;
       sbi_sbi_prop_ext_mixin := linPred_sbi_prop_ext_mixin |}.

  Local Lemma linPred_si_pure_unseal :
    si_pure = @linPred_defs.linPred_si_pure_def M.
  Proof. by rewrite -linPred_defs.linPred_si_pure_unseal. Qed.
  Local Lemma linPred_si_emp_valid_unseal :
    si_emp_valid = @linPred_defs.linPred_si_emp_valid_def M.
  Proof. by rewrite -linPred_defs.linPred_si_emp_valid_unseal. Qed.
  Local Definition linPred_unseal :=
    (linPred_unseal_bi, linPred_si_pure_unseal, linPred_si_emp_valid_unseal,
     @linPred_defs.linPred_own_unseal).
  Ltac unseal := rewrite !linPred_unseal.

  Global Instance linPred_sbi_emp_valid_exist :
    SbiEmpValidExist linPredI.
  Proof. iIntros (A Φ). unseal. iIntros "[%a H] /=". by iExists a. Qed.

  Global Instance linPred_bi_persistently_impl_si_pure :
    BiPersistentlyImplSiPure linPredI.
  Proof. iIntros (A Φ). unseal. iIntros (x) "_ H //". Qed.
End instances.

Module Export linPred.
  Ltac unseal := rewrite !linPred_unseal.
End linPred.

Section bi_facts.
  Context {M : ucmra}.
  Local Notation linPred := (linPred M).
  Local Notation linPred_at := (@linPred_at M).
  Local Notation linPred_own := (@linPred_own M).
  Implicit Types P Q : linPred.

  Lemma linPred_at_pure x (φ : Prop) : linPred_at ⌜φ⌝ x ⊣⊢ ⌜φ⌝.
  Proof. by unseal. Qed.
  Lemma linPred_at_emp x : linPred_at emp x ⊣⊢ x ≡ ε.
  Proof. by unseal. Qed.
  Lemma linPred_at_and x P Q :
    linPred_at (P ∧ Q) x ⊣⊢ linPred_at P x ∧ linPred_at Q x.
  Proof. by unseal. Qed.
  Lemma linPred_at_or x P Q :
    linPred_at (P ∨ Q) x ⊣⊢ linPred_at P x ∨ linPred_at Q x.
  Proof. by unseal. Qed.
  Lemma linPred_at_impl x P Q :
    linPred_at (P → Q) x ⊣⊢ (linPred_at P x → linPred_at Q x).
  Proof. by unseal. Qed.
  Lemma linPred_at_forall {A} x (Φ : A → linPred) :
    linPred_at (∀ a, Φ a) x ⊣⊢ ∀ a, linPred_at (Φ a) x.
  Proof. by unseal. Qed.
  Lemma linPred_at_exist {A} x (Φ : A → linPred) :
    linPred_at (∃ a, Φ a) x ⊣⊢ ∃ a, linPred_at (Φ a) x.
  Proof. by unseal. Qed.
  Lemma linPred_at_sep x P Q :
    linPred_at (P ∗ Q) x ⊣⊢
      ∃ x1 x2, x ≡ x1 ⋅ x2 ∧ linPred_at P x1 ∧ linPred_at Q x2.
  Proof. by unseal. Qed.
  Lemma linPred_at_wand x P Q :
    linPred_at (P -∗ Q) x ⊣⊢
      ∀ x', ✓ (x ⋅ x') → linPred_at P x' → linPred_at Q (x ⋅ x').
  Proof. by unseal. Qed.
  Lemma linPred_at_persistently x P : linPred_at (<pers> P) x ⊣⊢ linPred_at P ε.
  Proof. by unseal. Qed.
  Lemma linPred_at_later x P : linPred_at (▷ P) x ⊣⊢ ▷ linPred_at P x.
  Proof. by unseal. Qed.
  Lemma linPred_at_laterN x n P : linPred_at (▷^n P) x ⊣⊢ ▷^n linPred_at P x.
  Proof. induction n; rewrite /= ?linPred_at_later; by f_equiv. Qed.
  Lemma linPred_at_si_pure x Pi : linPred_at (<si_pure> Pi) x ⊣⊢ Pi.
  Proof. by unseal. Qed.
  Lemma linPred_at_internal_eq {A : ofe} x (a1 a2 : A) :
    linPred_at (a1 ≡ a2) x ⊣⊢ a1 ≡ a2.
  Proof. by rewrite /internal_eq linPred_at_si_pure. Qed.
  Lemma linPred_at_si_emp_valid P : <si_emp_valid> P ⊣⊢ linPred_at P ε.
  Proof. by unseal. Qed.
  Lemma linPred_at_own x y : linPred_at (linPred_own y) x ⊣⊢ x ≡ y.
  Proof. by unseal. Qed.

  Lemma linPred_entails P Q : (P ⊢ Q) ↔ ∀ x, ✓ x ⊢ linPred_at P x → linPred_at Q x.
  Proof. by unseal. Qed.
  Lemma linPred_equiv P Q : (P ⊣⊢ Q) ↔ ∀ x, ✓ x ⊢ linPred_at P x ↔ linPred_at Q x.
  Proof.
    unseal. rewrite /linPred_equiv_def /linPred_internal_eq.
    split; iIntros (H x) "#Hx"; by iApply H.
  Qed.
  Lemma linPred_emp_valid P : (⊢ P) ↔ ⊢ linPred_at P ε.
  Proof.
    rewrite /bi_emp_valid linPred_entails. setoid_rewrite linPred_at_emp. split.
    - iIntros (H) "_". iApply H; [|done]. by iApply ucmra_unit_validI.
    - iIntros (H x) "_ #Hx". iRewrite "Hx". by iApply H.
  Qed.

  Lemma linPred_at_affinely x P :
    linPred_at (<affine> P) x ⊣⊢ x ≡ ε ∧ linPred_at P ε.
  Proof.
    rewrite /bi_affinely linPred_at_and linPred_at_emp.
    iSplit; iIntros "[Hx HP]"; (iSplit; [done|]);
      [by iRewrite "Hx" in "HP"|by iRewrite "Hx"].
  Qed.
  Lemma linPred_at_intuitionistically x P :
    linPred_at (□ P) x ⊣⊢ x ≡ ε ∧ linPred_at P ε.
  Proof. by rewrite linPred_at_affinely linPred_at_persistently. Qed.
  Lemma linPred_at_except_0 x P :
    linPred_at (◇ P) x ⊣⊢ ◇ linPred_at P x.
  Proof.
    by rewrite /bi_except_0 linPred_at_or linPred_at_later linPred_at_pure.
  Qed.
  Lemma linPred_at_plainly x P : linPred_at (■ P) x ⊣⊢ linPred_at P ε.
  Proof. by rewrite /plainly linPred_at_si_pure linPred_at_si_emp_valid. Qed.

  Lemma linPred_at_sep_2 x1 x2 P Q :
    linPred_at P x1 ∧ linPred_at Q x2 ⊢ linPred_at (P ∗ Q) (x1 ⋅ x2).
  Proof. rewrite linPred_at_sep. iIntros. iExists x1, x2. auto. Qed.

  Lemma linPred_at_sep_affinely_l x P Q :
    linPred_at (<affine> P ∗ Q) x ⊣⊢ linPred_at P ε ∧ linPred_at Q x.
  Proof.
    rewrite linPred_at_sep. setoid_rewrite linPred_at_affinely. iSplit.
    - iIntros "#(%x1 & %x2 & Hx & [Hx1 ?] & ?)".
      iRewrite "Hx". iRewrite "Hx1". rewrite left_id. auto.
    - iIntros "#[??]". iExists ε, x. rewrite left_id. auto.
  Qed.
  Lemma linPred_at_sep_affinely_r x P Q :
    linPred_at (P ∗ <affine> Q) x ⊣⊢ linPred_at P x ∧ linPred_at Q ε.
  Proof.
    rewrite linPred_at_sep. setoid_rewrite linPred_at_affinely. iSplit.
    - iIntros "#(%x1 & %x2 & Hx & ? & [Hx2 ?])".
      iRewrite "Hx". iRewrite "Hx2". rewrite right_id. auto.
    - iIntros "#[??]". iExists x, ε. rewrite right_id. auto.
  Qed.

  Global Instance linPred_emp_timeless :
    Discrete (ε : M) → Timeless (@bi_emp linPred).
  Proof.
    rewrite /Timeless linPred_entails. iIntros (? x) "#Hx Hemp".
    rewrite linPred_at_later linPred_at_except_0 linPred_at_emp. by iMod "Hemp".
  Qed.

  Global Instance linPred_own_ne : NonExpansive linPred_own.
  Proof.
    unseal. apply (ne_internal_eq (PROP:=siProp)). iIntros (x1 x2) "#Hx".
    rewrite linPred_equivI /=. iIntros (x) "_ /=". iRewrite "Hx"; auto.
  Qed.
  Global Instance linPred_own_proper : Proper ((≡) ==> (≡)) linPred_own.
  Proof. apply: ne_proper. Qed.
  Global Instance linPred_own_timeless x :
    Discrete x → Timeless (linPred_own x).
  Proof.
    rewrite /Timeless linPred_entails. iIntros (? x') "#Hx' Hown".
    rewrite linPred_at_later linPred_at_except_0 linPred_at_own. by iMod "Hown".
  Qed.

  Lemma linPred_own_unit : linPred_own ε ⊣⊢ emp.
  Proof.
    apply linPred_equiv=> x. rewrite linPred_at_own linPred_at_emp; auto.
  Qed.
  Lemma linPred_own_op x1 x2 :
    linPred_own (x1 ⋅ x2) ⊣⊢ linPred_own x1 ∗ linPred_own x2.
  Proof.
    apply linPred_equiv=> x. rewrite linPred_at_sep.
    setoid_rewrite linPred_at_own. iIntros "_"; iSplit.
    - iIntros "H". iExists x1, x2; auto.
    - iIntros "(%x1' & %x2' & ? & Hx1 & Hx2)".
      iRewrite -"Hx1". by iRewrite -"Hx2".
  Qed.
  Lemma linPred_own_valid x : linPred_own x ⊢ ✓ x.
  Proof.
    apply linPred_entails=> y. rewrite linPred_at_own. iIntros "Hy Heq".
    iRewrite "Heq" in "Hy". by rewrite /internal_cmra_valid linPred_at_si_pure.
  Qed.
End bi_facts.
