From iris.proofmode Require Import proofmode.
From dlfactris.session_logic Require Import proofmode.
From dlfactris.examples Require Import llist.
Import TImp TImp.notations.

Definition list_rev_service : val := λ: "c",
  let: "l" := recv "c" in
  lreverse "l";; send "c" #();; close "c".

Definition list_rev_client : val := λ: "l",
  let: "c" := fork_chan list_rev_service in
  send "c" "l";; recv "c";; wait "c".

Section list_rev_example.

  Definition list_rev_prot : prot :=
    <! (l : loc) (vs : list val)> MSG #l {{ llist (λ x v, ⌜⌜x = v⌝⌝) l vs }};
    <?> MSG #() {{ llist (λ x v, ⌜⌜x = v⌝⌝) l (reverse vs) }}; END?.

  Lemma list_rev_service_spec c :
    {{{ c ↣ dual list_rev_prot }}}
      list_rev_service c
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_rec. wp_recv (l vs) as "Hl". iApply (lreverse_spec with "Hl").
    iIntros "!> Hl". wp_send with "[$Hl]". wp_close. by iApply "HΦ".
  Qed.

  Lemma llist_split {T} (IT : T → val → aProp) xs l :
    llist IT l xs ⊣⊢ ∃ vs : list val,
      llist (λ x v, ⌜⌜x = v⌝⌝) l vs ∗ [∗ list] x;v ∈ xs;vs, IT x v.
  Proof.
    iSplit.
    - iIntros "Hl".
      iInduction xs as [|x xs] "IH" forall (l).
      + iExists []. iFrame. eauto.
      + iDestruct "Hl" as (v lcons) "[HIT [Hlcons Hrec]]".
        iDestruct ("IH" with "Hrec") as (vs) "[Hvs H]".
        iExists (v::vs). iFrame.
        iExists v, lcons. eauto with iFrame.
    - iDestruct 1 as (vs) "[Hvs HIT]".
      iInduction xs as [|x xs] "IH" forall (l vs).
      + by iDestruct (big_sepL2_nil_inv_l with "HIT") as %->.
      + iDestruct (big_sepL2_cons_inv_l with "HIT") as (v vs' ->) "[HIT HITs]".
        iDestruct "Hvs" as (w lcons ->) "[Hl Hvs]".
        iExists w, lcons. iFrame "Hl HIT".
        iApply ("IH" with "Hvs HITs").
  Qed.

  Definition list_rev_protI {T} (IT : T → val → aProp) : prot :=
    <! (l : loc) (xs : list T)> MSG #l {{ llist IT l xs }};
    <?> MSG #() {{ llist IT l (reverse xs) }}; END?.

  Lemma list_rev_subprot {T} (IT : T → val → aProp) :
    ⊢ list_rev_prot ⊑ list_rev_protI IT.
  Proof.
    iIntros (l xs) "Hl".
    iDestruct (llist_split with "Hl") as (vs) "[Hl HIT]".
    iExists l, vs. iFrame "Hl".
    iModIntro. iIntros "Hl".
    iSplitL "Hl HIT".
    { iApply llist_split. rewrite big_sepL2_reverse_2.
      iExists (reverse vs). iFrame "Hl HIT". }
    done.
  Qed.

  Lemma list_rev_client_spec {T} (IT : T → val → aProp) l xs :
    {{{ llist IT l xs }}}
      list_rev_client #l
    {{{ RET #(); llist IT l (reverse xs) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_rec.
    iApply (wp_fork_chan (list_rev_prot)); iIntros "!>" (c) "Hc".
    - iApply (list_rev_service_spec with "Hc"). eauto.
    - iDestruct (own_chan_subprot _ _ (list_rev_protI IT) with "Hc []") as "Hc".
      { iApply list_rev_subprot. }
      wp_send with "[$Hl]". wp_recv as "Hl". wp_wait. by iApply "HΦ".
  Qed.

End list_rev_example.
