(** This file implements a distributed version of merge sort, a specification
thereof, and its proofs. There are two variants:

- [sort_service]: a service that takes both a comparison function and a channel
  as its arguments.
- [sort_service_func]: a service that only takes a channel as its argument. The
  comparison function is sent over the channel. *)
From stdpp Require Import sorting.
From dlfactris.session_logic Require Import proofmode.
From dlfactris.examples Require Export llist compare.
Import TImp TImp.notations.

Definition lmerge : val :=
  rec: "go" "cmp" "ys" "zs" :=
    if: lisnil "ys" then lapp "ys" "zs" else
    if: lisnil "zs" then Free "zs" else
    let: "y" := lhead "ys" in
    let: "z" := lhead "zs" in
    if: "cmp" "y" "z"
    then lpop "ys";; "go" "cmp" "ys" "zs";; lcons "y" "ys"
    else lpop "zs";; "go" "cmp" "ys" "zs";; lcons "z" "ys".

Definition sort_service_cont : val :=
  rec: "go" "cmp" "c" :=
    let: "xs" := recv "c" in
    if: llength "xs" ≤ #1 then send "c" #() else
    let: "zs" := lsplit "xs" in
    let: "cy" := fork_chan (λ: "c", "go" "cmp" "c";; close "c") in
    let: "cz" := fork_chan (λ: "c", "go" "cmp" "c";; close "c") in
    send "cy" "xs";;
    send "cz" "zs";;
    recv "cy";; recv "cz";;
    lmerge "cmp" "xs" "zs";;
    wait "cy";; wait "cz";;
    send "c" #().

Definition sort_service : val :=
  λ: "cmp" "c", sort_service_cont "cmp" "c";; close "c".

Definition sort_service_func_cont : val := λ: "c",
  let: "cmp" := recv "c" in
  sort_service_cont "cmp" "c".

Definition sort_service_func : val := λ: "c",
  sort_service_func_cont "c";; close "c".

Definition sort_client_func : val := λ: "cmp" "xs",
  let: "c" := fork_chan sort_service_func in
  send "c" "cmp";; send "c" "xs";;
  recv "c";; wait "c".

Section sort.
  Definition sort_protocol_cont {A} (I : A → val → aProp)
      (R : A → A → Prop) (p : prot) : prot :=
    <! (xs : list A) (l : loc)> MSG #l {{ llist I l xs }};
    <? (xs' : list A)> MSG #() {{ ⌜⌜ Sorted R xs' ⌝⌝ ∗ ⌜⌜ xs' ≡ₚ xs ⌝⌝ ∗ llist I l xs' }};
    p.
  Global Instance sort_protocol_cont_contractive {A}
      (I : A → val → aProp) (R : A → A → Prop) :
    Contractive (sort_protocol_cont I R).
  Proof. solve_prot_contractive. Qed.

  Definition sort_protocol {A} (I : A → val → aProp) (R : A → A → Prop) : prot :=
    sort_protocol_cont I R END?.

  Definition sort_protocol_func_cont (p : prot) : prot :=
    <! A (I : A → val → aProp) (R : A → A → Prop)
        `(!RelDecision R, !Total R) (cmp : val)>
      MSG cmp {{ cmp_spec I R cmp }};
    sort_protocol_cont I R p.

  Global Instance sort_protocol_func_cont_contractive :
    Contractive (sort_protocol_func_cont).
  Proof. solve_prot_contractive. Qed.

  Definition sort_protocol_func : prot :=
    sort_protocol_func_cont END?.

  Lemma lmerge_spec {A} (I : A → val → aProp) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) l1 l2 xs1 xs2 :
    cmp_spec I R cmp -∗
    {{{ llist I l1 xs1 ∗ llist I l2 xs2 }}}
      lmerge cmp #l1 #l2
    {{{ RET #(); llist I l1 (list_merge R xs1 xs2) }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "[Hl1 Hl2] HΨ".
    iLöb as "IH" forall (l2 xs1 xs2 Ψ).
    wp_rec. iApply (lisnil_spec with "Hl1"); iIntros "!> Hl1".
    destruct xs1 as [|x1 xs1]; wp_pures.
    { iApply (lapp_spec with "Hl1 Hl2"); iIntros "!> Hl /=".
      iApply "HΨ". by rewrite list_merge_nil_l. }
    iApply (lisnil_spec with "Hl2"); iIntros "!> Hl2".
    destruct xs2 as [|x2 xs2]; wp_pures.
    { wp_free. iApply "HΨ". iFrame. }
    iApply (lhead_spec_aux with "Hl1"); iIntros "!>" (v1 l1') "[HIx1 [Hl1 Hl1']]".
    iApply (lhead_spec_aux with "Hl2"); iIntros "!>" (v2 l2') "[HIx2 [Hl2 Hl2']]".
    iApply ("Hcmp" with "HIx1 HIx2"); iIntros "!> [HIx1 HIx2] /=".
    case_bool_decide; wp_pures.
    - rewrite decide_True //.
      iApply (lpop_spec_aux with "Hl1 Hl1'"); iIntros "!> Hl1".
      iApply ("IH" $! _ _ (_ :: _) with "Hl1 [HIx2 Hl2 Hl2']").
      { iExists _, _. iFrame. }
      iIntros "!> Hl1".
      iApply (lcons_spec with "Hl1 HIx1"). iIntros "!> Hl1". iApply "HΨ". iFrame.
    - rewrite decide_False //.
      iApply (lpop_spec_aux with "Hl2 Hl2'"); iIntros "!> Hl2".
      iApply ("IH" $! _ (_ :: _) with "[HIx1 Hl1 Hl1'] Hl2").
      { iExists _, _. iFrame. }
      iIntros "!> Hl1".
      iApply (lcons_spec with "Hl1 HIx2"); iIntros "!> Hl1". iApply "HΨ". iFrame.
  Qed.

  Lemma sort_service_cont_spec {A} (I : A → val → aProp) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) c p :
    cmp_spec I R cmp -∗
    {{{ c ↣ dual (sort_protocol_cont I R p) }}}
      sort_service_cont cmp c
    {{{ RET #(); c ↣ dual p }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c p Ψ). wp_rec.
    wp_recv (xs l) as "Hl".
    iApply (llength_spec with "Hl"); iIntros "!> Hl".
    wp_pures; case_bool_decide as Hlen; wp_pures.
    { assert (Sorted R xs).
      { destruct xs as [|x1 [|x2 xs]]; simpl in *; eauto with lia. }
      wp_send with "[$Hl]"; first by auto. by iApply "HΨ". }
    iApply (lsplit_spec with "Hl"); iIntros "!>" (l2 vs1 vs2).
      iDestruct 1 as (->) "[Hl1 Hl2]".
    iApply (wp_fork_chan (sort_protocol_cont I R END?)); iIntros "!>" (cy) "Hcy".
    { iApply ("IH" with "Hcy"); iIntros "!> Hcy". rewrite dual_end. by wp_close. }
    iApply (wp_fork_chan (sort_protocol_cont I R END?)); iIntros "!>" (cz) "Hcz".
    { iApply ("IH" with "Hcz"); iIntros "!> Hcz". rewrite dual_end. by wp_close. }
    wp_send with "[$Hl1]".
    wp_send with "[$Hl2]".
    wp_recv (ys1) as "(%&%&Hl1)".
    wp_recv (ys2) as "(%&%&Hl2)".
    iApply (lmerge_spec with "Hcmp [$Hl1 $Hl2]"); iIntros "!> Hl".
    wp_wait. wp_wait. wp_send with "[$Hl]".
    - iSplit; iPureIntro.
      + by apply (Sorted_list_merge _).
      + rewrite (merge_Permutation R). by f_equiv.
    - by iApply "HΨ".
  Qed.

  Lemma sort_service_spec {A} (I : A → val → aProp) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) c :
    cmp_spec I R cmp -∗
    {{{ c ↣ dual (sort_protocol I R) }}}
      sort_service cmp c
    {{{ RET #(); emp }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". wp_rec.
    iApply (sort_service_cont_spec with "Hcmp Hc"); iIntros "!> Hc".
    rewrite dual_end. wp_close. by iApply "HΨ".
  Qed.

  Lemma sort_service_func_cont_spec c p :
    {{{ c ↣ dual (sort_protocol_func_cont p) }}}
      sort_service_func_cont c
    {{{ RET #(); c ↣ dual p }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". wp_rec.
    wp_recv (A I R ?? cmp) as "#Hcmp".
    by iApply (sort_service_cont_spec with "Hcmp Hc").
  Qed.

  Lemma sort_service_func_spec c :
    {{{ c ↣ dual sort_protocol_func }}}
      sort_service_func c
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". wp_rec.
    iApply (sort_service_func_cont_spec with "Hc"); iIntros "!> Hc".
    rewrite dual_end. wp_close. by iApply "HΨ".
  Qed.

  Lemma sort_client_func_spec {A} (I : A → val → aProp) R                        (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=77e4516f *)
       `{!RelDecision R, !Total R} cmp l (xs : list A) :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_client_func cmp #l
    {{{ ys, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗ llist I l ys }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_rec.
    iApply (wp_fork_chan (sort_protocol_func)); iIntros "!>" (c) "Hc".
    { by iApply (sort_service_func_spec with "Hc"); iIntros "!> Hc". }
    wp_send with "[$Hcmp]".
    wp_send with "[$Hl]".
    wp_recv (ys) as "(Hsorted & Hperm & Hl)". wp_wait.
    iApply "HΦ"; by iFrame.
  Qed.
End sort.
