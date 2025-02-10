(** This file defines all of the semantic typing lemmas for term types. Most of
these lemmas are semantic versions of the syntactic typing judgments typically
found in a syntactic type system. *)
From iris.bi.lib Require Import core.
From dlfactris.lang Require Import metatheory.
From dlfactris.session_logic Require Import proofmode.
From dlfactris.logrel Require Export operators subtyping_rules term_typing_judgment.

Section term_typing_rules.
  Implicit Types A B : ltty.
  Implicit Types Γ : ctx.

  (** Frame rule *)
  Lemma ltyped_frame Γ Γ1 Γ2 e A :
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ++ Γ ⊨ e : A ⫤ Γ2 ++ Γ).
  Proof.
    iIntros "#He !>" (vs) "HΓ".
    iDestruct (ctx_ltyped_app with "HΓ") as "[HΓ1 HΓ]".
    iApply ("He" with "HΓ1").
    iIntros (v) "[$ HΓ2]". by iApply (ctx_ltyped_app with "[$]").
  Qed.

  (** Variable properties *)
  Lemma ltyped_var Γ (x : string) A :
    Γ !! x = Some A →
    Γ ⊨ x : A ⫤ ctx_overwrite x (copy- A) Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "!>"; iIntros (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (v Hvs) "[HA HΓ]". rewrite Hvs.
    iAssert (ltty_car (copy- A) v)%lty as "#HAm".
    { iIntros "{HΓ}". iApply bi.persistent_absorbingly_affinely_2.
      by iApply coreP_intro. }
    iApply wp_val. iFrame "HA". iApply ctx_ltyped_cons_named. eauto with iFrame.
  Qed.

  (** Subtyping *)
  Theorem ltyped_subsumption Γ1 Γ2 Γ1' Γ2' e τ τ' :
    Γ1 <ctx: Γ1' -∗ τ' <: τ -∗ Γ2' <ctx: Γ2 -∗
    (Γ1' ⊨ e : τ' ⫤ Γ2') -∗ (Γ1 ⊨ e : τ ⫤ Γ2).
  Proof.
    iIntros "#HleΓ1 #Hle #HleΓ2 #He" (vs) "!> HΓ1".
    iApply ("He" with "(HleΓ1 HΓ1)").
    iIntros (v) "[Hτ HΓ2]". iSplitL "Hτ"; [by iApply "Hle"|by iApply "HleΓ2"].
  Qed.
  (* TODO: JKH believes this is a better order for the arguments. *)
  Theorem ltyped_subsumption_alt Γ1 Γ2 Γ1' Γ2' e τ τ' :
    Γ1 <ctx: Γ1' -∗ (Γ1' ⊨ e : τ' ⫤ Γ2') -∗
    τ' <: τ -∗ Γ2' <ctx: Γ2 -∗ (Γ1 ⊨ e : τ ⫤ Γ2).
  Proof.
    iIntros "#HleΓ1 #He #Hle #HleΓ2" (vs) "!> HΓ1".
    iApply ("He" with "(HleΓ1 HΓ1)").
    iIntros (v) "[Hτ HΓ2]". iSplitL "Hτ"; [by iApply "Hle"|by iApply "HleΓ2"].
  Qed.
  Theorem ltyped_val_subsumption v τ τ' :
    τ' <: τ -∗
    (⊨ᵥ v : τ') -∗ (⊨ᵥ v : τ).
  Proof.
    iIntros "#Hle #Hv". iIntros "!>". iApply "Hle".
    rewrite /ltyped_val /=. iApply "Hv".
  Qed.

  (** Basic properties *)
  Lemma ltyped_val_unit : ⊨ᵥ #() : ().
  Proof. iIntros "!>". eauto. Qed.
  Lemma ltyped_unit Γ : Γ ⊨ #() : ().
  Proof. iApply ltyped_val_ltyped. iApply ltyped_val_unit. Qed.
  Lemma ltyped_val_bool (b : bool) : ⊨ᵥ #b : lty_bool.
  Proof. iIntros "!>". eauto. Qed.
  Lemma ltyped_bool Γ (b : bool) : Γ ⊨ #b : lty_bool.
  Proof. iApply ltyped_val_ltyped. iApply ltyped_val_bool. Qed.
  Lemma ltyped_val_int (z: Z) : ⊨ᵥ #z : lty_int.
  Proof. iIntros "!>". eauto. Qed.
  Lemma ltyped_int Γ (i : Z) : Γ ⊨ #i : lty_int.
  Proof. iApply ltyped_val_ltyped. iApply ltyped_val_int. Qed.

  (** Operations *)
  Lemma ltyped_un_op Γ1 Γ2 op e A B :
    LTyUnOp op A B →
    lty_copyable A -∗
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ⊨ UnOp op e : B ⫤ Γ2).
  Proof.
    iIntros (Hop) "#Hcopy #He !>". iIntros (vs) "HΓ1 /=".
    iApply ("He" with "[HΓ1 //]"). iIntros (v1) "[HA Hctx]".
    iDestruct ("Hcopy" with "HA") as "HA".
    iDestruct (Hop with "HA") as (w ?) "HB".
    iApply wp_pure_step.
    - apply pure_step_pure_ctx_step. by apply UnOpS.
    - iApply wp_val. iIntros "!>". iFrame.
  Qed.

  Lemma ltyped_bin_op Γ1 Γ2 Γ3 op e1 e2 A1 A2 B :
    LTyBinOp op A1 A2 B →
    lty_copyable A1 -∗
    lty_copyable A2 -∗
    (Γ1 ⊨ e2 : A2 ⫤ Γ2) -∗
    (Γ2 ⊨ e1 : A1 ⫤ Γ3) -∗
    (Γ1 ⊨ BinOp op e1 e2 : B ⫤ Γ3).
  Proof.
    iIntros (Hop) "#Hcopy1 #Hcopy2 #He2 #He1 !>". iIntros (vs) "HΓ1 /=".
    iApply ("He2" with "[HΓ1 //]"). iIntros (v2) "[HA2 HΓ2]".
    iApply ("He1" with "[HΓ2 //]"). iIntros (v1) "[HA1 HΓ3]".
    iDestruct ("Hcopy1" with "HA1") as "HA1".
    iDestruct ("Hcopy2" with "HA2") as "HA2".
    iDestruct (Hop with "HA1 HA2") as (w ?) "HB".
    iApply wp_pure_step.
    - apply pure_step_pure_ctx_step. by apply BinOpS.
    - iApply wp_val. iIntros "!>". iFrame.
  Qed.

  (** Conditionals *)
  Lemma ltyped_if Γ1 Γ2 Γ3 e1 e2 e3 A :
    (Γ1 ⊨ e1 : lty_bool ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : A ⫤ Γ3) -∗
    (Γ2 ⊨ e3 : A ⫤ Γ3) -∗
    (Γ1 ⊨ (if: e1 then e2 else e3) : A ⫤ Γ3).
  Proof.
    iIntros "#He1 #He2 #He3 !>" (v) "HΓ1 /=".
    iApply ("He1" with "[HΓ1 //]"). iIntros (b) "[Hbool HΓ2]".
    rewrite /lty_bool. iDestruct "Hbool" as ([]) "->".
    - iApply ("He2" with "[HΓ2 //]").
    - iApply ("He3" with "[HΓ2 //]").
  Qed.

  (** Arrow properties *)
  Lemma ltyped_app Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ1 ⊨ e2 : A1 ⫤ Γ2) -∗ (Γ2 ⊨ e1 : A1 ⊸ A2 ⫤ Γ3) -∗
    (Γ1 ⊨ e1 e2 : A2 ⫤ Γ3).
  Proof.
    iIntros "#H2 #H1". iIntros (vs) "!> HΓ /=".
    iApply ("H2" with "[HΓ //]"). iIntros (v) "[HA1 HΓ]".
    iApply ("H1" with "[HΓ //]"). iIntros (f) "[Hf HΓ3]".
    iApply ("Hf" $! v with "HA1").
    iIntros "!>" (w) "HA2". iFrame.
  Qed.

  Lemma ltyped_app_copy Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ1 ⊨ e2 : A1 ⫤ Γ2) -∗ (Γ2 ⊨ e1 : A1 → A2 ⫤ Γ3) -∗
    (Γ1 ⊨ e1 e2 : A2 ⫤ Γ3).
  Proof.
    iIntros "#H2 #H1". iIntros (vs) "!> HΓ /=".
    iApply ("H2" with "[HΓ //]"). iIntros (v) "[HA1 HΓ]".
    iApply ("H1" with "[HΓ //]"). iIntros (f) "[Hf HΓ]".
    iApply ("Hf" $! v with "HA1").
    iIntros "!>" (w) "HA2". iFrame.
  Qed.

  Lemma ltyped_lam Γ1 Γ2 x e A1 A2 :                                             (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=35979126 *)
    (ctx_cons x A1 Γ1 ⊨ e : A2 ⫤ []) -∗
    Γ1 ++ Γ2 ⊨ (λ: x, e) : A1 ⊸ A2 ⫤ Γ2.
  Proof.
    iIntros "#He". iIntros (vs) "!> HΓ /=". wp_pures.
    iDestruct (ctx_ltyped_app with "HΓ") as "[HΓ1 $]".
    iIntros (v) "HA1". wp_pures.
    iDestruct ("He" $! (binder_insert x v vs) with "[HA1 HΓ1]") as "He'".
    { by iApply (ctx_ltyped_cons with "HA1"). }
    rewrite subst_map_binder_insert.
    iApply "He'". by iIntros (w) "[$ _]".
  Qed.

  (* TODO: This might be derivable from rec value rule *)
  Lemma ltyped_val_lam x e A1 A2 :
    (ctx_cons x A1 [] ⊨ e : A2 ⫤ []) -∗
    ⊨ᵥ (λ: x, e) : A1 ⊸ A2.
  Proof.
    iIntros "#He !>" (v) "HA1".
    wp_pures.
    iDestruct ("He" $!(binder_insert x v ∅) with "[HA1]") as "He'".
    { iApply (ctx_ltyped_cons with "HA1"). by iApply ctx_ltyped_nil. }
    rewrite subst_map_binder_insert /= binder_delete_empty subst_map_empty.
    iApply "He'". by iIntros (w) "[$ _]".
  Qed.

  (* Typing rule for introducing copyable functions *)
  Definition ctx_copy_minus : ctx → ctx :=
    fmap (λ xA, CtxItem (ctx_item_name xA) (copy- (ctx_item_type xA))).

  Lemma ltyped_rec Γ f x e A1 A2 :
    (ctx_cons f (A1 → A2) (ctx_cons x A1 (ctx_copy_minus Γ)) ⊨ e : A2 ⫤ []) -∗
    Γ ⊨ (rec: f x := e) : A1 → A2 ⫤ Γ.
  Proof.
    iIntros "#He". iIntros (vs) "!> HΓ /=". wp_pures.
    iAssert (□ ctx_ltyped vs (ctx_copy_minus Γ))%I as "#HΓc".
    { iClear "He". iInduction Γ as [|[y B] Γ] "IHΓ" forall (vs); simpl.
      { rewrite /ctx_ltyped. by iIntros "!>". }
      iDestruct "HΓ" as "[(%v&%Hy&HB) HΓ] /=". iSplitR "HΓ"; [|by iApply "IHΓ"].
      iExists v; iSplitR; [by auto|].
      iDestruct (coreP_intro with "HB") as "{HB} #HB". by iIntros "!> !>". }
    iFrame "HΓ". iLöb as "IH". iIntros "!>" (v) "HA1". 
    wp_pures. set (r := RecV f x _).
    iDestruct ("He" $! (binder_insert f r (binder_insert x v vs))
      with "[HΓc HA1]") as "He'".
    { iApply (ctx_ltyped_cons with "IH").
      by iApply (ctx_ltyped_cons with "HA1"). }
    rewrite !subst_map_binder_insert_2.
    iApply "He'". iIntros (w) "[$ _]".
  Qed.

  Lemma ltyped_val_rec f x e A1 A2 :
    (ctx_cons f (A1 → A2) (ctx_cons x A1 []) ⊨ e : A2 ⫤ []) -∗
    ⊨ᵥ (rec: f x := e) : A1 → A2.
  Proof.
    iIntros "#He !>". iLöb as "IH". iIntros "!> %v HA1". wp_pures.
    set (r := RecV f x _).
    iDestruct ("He" $! (binder_insert f r (binder_insert x v ∅))
               with "[HA1]") as "He'".
    { iApply (ctx_ltyped_cons with "IH").
      iApply (ctx_ltyped_cons with "HA1"). by iApply ctx_ltyped_nil. }
    rewrite !subst_map_binder_insert_2 !binder_delete_empty subst_map_empty.
    iApply "He'". iIntros (w) "[$ _]".
  Qed.

  Lemma ltyped_let Γ1 Γ2 Γ3 x e1 e2 A1 A2 :
    (Γ1 ⊨ e1 : A1 ⫤ Γ2) -∗
    (ctx_overwrite x A1 Γ2 ⊨ e2 : A2 ⫤ Γ3) -∗
    (Γ1 ⊨ (let: x:=e1 in e2) : A2 ⫤ ctx_filter_eq x Γ2 ++ ctx_anonymize x Γ3).
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    iApply ("He1" with "HΓ1"); iIntros (v) "[HA1 HΓ2]". wp_pures.
    rewrite {3}(ctx_filter_eq_perm Γ2 x).
    iDestruct (ctx_ltyped_app with "HΓ2") as "[HΓ2eq HΓ2neq]".
    iDestruct ("He2" $! (binder_insert x v vs) with "[HA1 HΓ2neq]") as "He'".
    { by iApply (ctx_ltyped_overwrite with "HA1"). }
    rewrite subst_map_binder_insert. iApply "He'".
    iIntros (w) "[$ HΓ3]". iApply ctx_ltyped_app. iFrame "HΓ2eq".
    by iApply ctx_ltyped_anonymize'.
  Qed.

  Lemma ltyped_seq Γ1 Γ2 Γ3 e1 e2 A B :
    lty_copyable A -∗
    (Γ1 ⊨ e1 : A ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : B ⫤ Γ3) -∗
    (Γ1 ⊨ (e1 ;; e2) : B ⫤ Γ3).
  Proof.
    iIntros "#Hcopy #He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    iApply ("He1" with "HΓ1"); iIntros (v) "[HA HΓ2]". wp_pures.
    iDestruct ("Hcopy" with "HA") as "_". by iApply "He2".
  Qed.

  (** Product properties  *)
  Lemma ltyped_pair Γ1 Γ2 Γ3 e1 e2 A1 A2 :
    (Γ1 ⊨ e2 : A2 ⫤ Γ2) -∗ (Γ2 ⊨ e1 : A1 ⫤ Γ3) -∗
    (Γ1 ⊨ (e1,e2) : A1 * A2 ⫤ Γ3).
  Proof.
    iIntros "#H2 #H1". iIntros (vs) "!> HΓ /=".
    iApply ("H2" with "[HΓ //]"); iIntros (w2) "[HA2 HΓ]".
    iApply ("H1" with "[HΓ //]"); iIntros (w1) "[HA1 HΓ]".
    wp_pures. iFrame "HΓ". iExists w1, w2. by iFrame.
  Qed.

  (* We can give a stronger typing rule for [match] where the branches of the
  match can perform strong updates. The typing rule for [⊸] disallows that. *)
  Lemma ltyped_let_pair Γ1 Γ2 Γ3 e1 e2 A1 A2 B :
    (Γ1 ⊨ e1 : A1 * A2 ⫤ Γ2) -∗
    (Γ2 ⊨ e2 : A1 ⊸ A2 ⊸ B ⫤ Γ3) -∗
    (Γ1 ⊨ LetPair e1 e2 : B ⫤ Γ3).
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    iApply ("He1" with "HΓ1"); iIntros (v) "[(%w1&%w2&->&HA1&HA2) HΓ2]".
    iApply ("He2" with "HΓ2"); iIntros (vret) "[HB HΓ3]".
    iApply ("HB" with "HA1"); iIntros (vret') "!> HB".
    iApply ("HB" with "HA2"); iIntros (w) "!> HB". iFrame.
  Qed.

  (** Sum Properties *)
  Lemma ltyped_injl Γ1 Γ2 t e As A :
    As !! t = Some A →
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ⊨ Sum t e : lty_sum As ⫤ Γ2).
  Proof.
    iIntros (Ht) "#He %vs !> HΓ /=".
    iApply ("He" with "HΓ"); iIntros (v) "[HA HΓ]". wp_pures.
    iFrame "HΓ". iExists t, v. rewrite lookup_total_alt Ht /=. eauto with iFrame.
  Qed.

  (* Same problem as for [ltyped_let_pair] *)
  Lemma ltyped_case Γ1 Γ2 Γ3 e tes As B :
    (Γ1 ⊨ e : lty_sum As ⫤ Γ2) -∗
    ([∗ map] t ↦ A ∈ As, ∃ e,
      ⌜ sum_branch t tes = Some e ⌝ ∧ (Γ2 ⊨ e : A ⊸ B ⫤ Γ3)) -∗
    (Γ1 ⊨ MatchSum e tes : B ⫤ Γ3).
  Proof.
    iIntros "#He #Htes" (vs) "!> HΓ /=".
    iApply ("He" with "HΓ"); iIntros (v) "[(%t & %w & [%A %Ht] & -> & HA) HΓ]".
    iDestruct (big_sepM_lookup with "Htes") as (e' He') "He'"; first done.
    assert (TCEq (sum_branch t (prod_map id (subst_map vs) <$> tes))
                 (Some (subst_map vs e'))).
    { apply TCEq_eq. revert e' He'. induction tes as [|[]];
        intros; repeat (case_decide || simplify_eq/=); eauto. }
    iApply ("He'" with "HΓ"); iIntros (vret) "[HB HΓ]".
    rewrite lookup_total_alt Ht /=.
    iApply ("HB" with "HA"); iIntros (vret') "!> ?". iFrame.
  Qed.

  (** Universal Properties *)
  Lemma ltyped_tlam Γ1 Γ2 Γ' e k (C : lty k → ltty) :
    (∀ K, Γ1 ⊨ e : C K ⫤ []) -∗
    (Γ1 ++ Γ2 ⊨ (λ: <>, e) : (∀ X, C X) ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ /=". wp_pures.
    iDestruct (ctx_ltyped_app with "HΓ") as "[HΓ1 $]".
    iIntros (M) "/=". iApply ("He" with "HΓ1"). iIntros (v) "[$ _]".
  Qed.

  Lemma ltyped_tapp Γ Γ2 e k (C : lty k → ltty) K :
    (Γ ⊨ e : (∀ X, C X) ⫤ Γ2) -∗
    (Γ ⊨ e #() : C K ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    iApply ("He" with "[HΓ //]"); iIntros (w) "[HB HΓ] /=".
    iApply "HB". by iIntros "!>" (v) "$".
  Qed.

  (** Existential properties *)
  Lemma ltyped_pack Γ1 Γ2 e k (C : lty k → ltty) K :
    (Γ1 ⊨ e : C K ⫤ Γ2) -∗ Γ1 ⊨ e : (∃ X, C X) ⫤ Γ2.
  Proof.
    iIntros "#He" (vs) "!> HΓ /=".
    iApply ("He" with "[HΓ //]"); iIntros (w) "[HB $]". by iExists K.
  Qed.

  Lemma ltyped_unpack {k} Γ1 Γ2 Γ3 x e1 e2 (C : lty k → ltty) B :
    (Γ1 ⊨ e1 : (∃ X, C X) ⫤ Γ2) -∗
    (∀ K, ctx_overwrite x (C K) Γ2 ⊨ e2 : B ⫤ Γ3) -∗
    (Γ1 ⊨ (let: x := e1 in e2) : B ⫤ ctx_filter_eq x Γ2 ++ ctx_anonymize x Γ3).
  Proof.
    iIntros "#He1 #He2 !>". iIntros (vs) "HΓ1 /=".
    iApply ("He1" with "HΓ1"); iIntros (v) "[HC HΓ2]".
    iDestruct "HC" as (X) "HX". wp_pures.
    rewrite {3}(ctx_filter_eq_perm Γ2 x).
    iDestruct (ctx_ltyped_app with "HΓ2") as "[HΓ2eq HΓ2neq]".
    iDestruct ("He2" $! X (binder_insert x v vs) with "[HX HΓ2neq]") as "He'".
    { by iApply (ctx_ltyped_overwrite with "HX"). }
    rewrite subst_map_binder_insert. iApply "He'".
    iIntros (w) "[$ HΓ3]". iApply ctx_ltyped_app.
    iFrame "HΓ2eq". by iApply ctx_ltyped_anonymize'.
  Qed.

  (** Mutable Unique Reference properties *)
  Lemma ltyped_alloc Γ1 Γ2 e A :
    (Γ1 ⊨ e : A ⫤ Γ2) -∗
    (Γ1 ⊨ Alloc e : ref_uniq A ⫤ Γ2).
  Proof.
    iIntros "#He" (vs) "!> HΓ1 /=".
    iApply ("He" with "HΓ1"). iIntros (v) "[Hv HΓ2]".
    wp_alloc l as "Hl". by iFrame.
  Qed.

  Lemma ltyped_free Γ1 Γ2 e A :
    lty_copyable A -∗
    (Γ1 ⊨ e : ref_uniq A ⫤ Γ2) -∗
    (Γ1 ⊨ Free e : () ⫤ Γ2).
  Proof.
    iIntros "#Hcopy #He" (vs) "!> HΓ1 /=".
    iApply ("He" with "HΓ1"). iIntros (v) "[Hv HΓ2]".
    iDestruct "Hv" as (l w ->) "[Hl Hw]". iFrame.
    wp_free. iDestruct ("Hcopy" with "Hw") as "Hw". by iFrame.
  Qed.

  Lemma ltyped_load Γ (x : string) A :
    Γ !! x = Some (ref_uniq A)%lty →
    Γ ⊨ ! x : A ⫤ ctx_overwrite x (ref_uniq (copy- A)) Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm vs) "!> HΓ /=". rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ") as (v Hvs) "[HA HΓ]"; rewrite Hvs.
    iDestruct "HA" as (l w ->) "[Hl HA]". wp_load.
    iAssert (ltty_car (copy- A) w)%lty as "#HAm".
    { iIntros "{Hl HΓ}". iApply bi.persistent_absorbingly_affinely_2.
      by iApply coreP_intro. }
    iFrame "HA". iApply ctx_ltyped_cons_named. eauto with iFrame.
  Qed.

  Lemma ltyped_store Γ Γ' (x : string) e A B :
    Γ' !! x = Some (ref_uniq A)%lty →
    lty_copyable A -∗
    (Γ ⊨ e : B ⫤ Γ') -∗
    (Γ ⊨ x <- e : () ⫤ ctx_overwrite x (ref_uniq B) Γ').
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "#Hcopy #He"; iIntros (vs) "!> HΓ /=".
    iApply ("He" with "HΓ"). iIntros (v) "[HB HΓ']".
    rewrite {2}HΓx /=.
    iDestruct (ctx_ltyped_cons_named with "HΓ'") as (vl Hvs) "[HA HΓ']"; rewrite Hvs.
    iDestruct "HA" as (l w ->) "[? HA]". wp_store. iSplit; [done|].
    iApply ctx_ltyped_cons_named. iDestruct ("Hcopy" with "HA") as "HA".
    eauto with iFrame.
  Qed.
End term_typing_rules.
