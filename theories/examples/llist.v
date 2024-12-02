(** This file defines a separation logic representation predicates [llist] for
mutable linked-lists. It comes with a small library of operations (head, pop,
lookup, length, append, prepend, snoc, split). *)
From dlfactris.lang Require Export notation.
From dlfactris.base_logic Require Export proofmode.

Fixpoint llist {A} (I : A → val → aProp) (l : loc) (xs : list A) : aProp :=
  match xs with
  | [] => l ↦ SumV "nil" #()
  | x :: xs => ∃ (v : val) (l' : loc), I x v ∗ l ↦ SumV "cons" (v,#l') ∗ llist I l' xs
  end%I.
Arguments llist : simpl never.

Definition lnil : val := λ: <>, Alloc (Sum "nil" #()).
Definition lcons : val := λ: "x" "l", "l" <- Sum "cons" ("x", Alloc (!"l")).

Definition lisnil : val := λ: "l",
  match: !"l" with
  | "cons" "p" => #false
  | "nil" <> => #true
  end.

Definition lhead : val := λ: "l",
  match: !"l" with
  | "cons" "p" => let: '("x", <>) := "p" in "x"
  | "nil" <> => #() #()
  end.

Definition lpop : val := λ: "l",
  match: !"l" with
  | "cons" "p" => let: '("x", "next") := "p" in "l" <- !"next";; Free "next";; "x"
  | "nil" <> => #() #()
  end.

Definition llookup : val :=
  rec: "go" "l" "n" :=
    if: "n" = #0 then lhead "l" else
    match: !"l" with
    | "cons" "p" => let: '(<>, "next") := "p" in "go" "next" ("n" - #1)
    | "nil" <> => #() #()
    end.

Definition llength : val :=
  rec: "go" "l" :=
    match: !"l" with
    | "nil" <> => #0
    | "cons" "p" => let: '(<>, "next") := "p" in #1 + "go" "next"
    end.

Definition lapp_aux : val :=
  rec: "go" "l" "k" :=
    match: !"l" with
    | "nil" <> => "l" <- !"k"
    | "cons" "p" => let: '(<>, "next") := "p" in "go" "next" "k"
    end.
Definition lapp : val := λ: "l" "k",
  lapp_aux "l" "k";; Free "k".
Definition lprep : val := λ: "l" "k",
  lapp_aux "k" "l";; "l" <- !"k";; Free "k".

Definition lsnoc : val :=
  rec: "go" "l" "x" :=
    match: !"l" with
    | "nil" <> => "l" <- Sum "cons" ("x", lnil #())
    | "cons" "p" => let: '(<>, "next") := "p" in "go" "next" "x"
    end.

Definition lsplit_at : val :=
  rec: "go" "l" "n" :=
    if: "n" ≤ #0 then
      let: "k" := Alloc (! "l") in "l" <- Sum "nil" #();; "k" else
    match: !"l" with
    | "nil" <> => lnil #()
    | "cons" "p" => let: '(<>, "next") := "p" in "go" "next" ("n" - #1)
    end.

Definition lsplit : val := λ: "l", lsplit_at "l" (llength "l" `quot` #2).

Definition lreverse_at : val :=
  rec: "go" "l" "acc" :=
    match: !"l" with
    | "nil" <> => Free "l";; "acc"
    | "cons" "p" => let: '("x", "next") := "p" in lcons "x" "acc";;
                                                  Free "l";; "go" "next" "acc"
    end.

Definition lreverse : val :=
  λ: "l", let: "l'" := Alloc (!"l") in
          let: "l''" := (lreverse_at "l'" (lnil #())) in
          "l" <- !"l''";; Free "l''".

Section lists.
Context {A} (I : A → val → aProp).
Implicit Types i : nat.
Implicit Types xs : list A.
Implicit Types l : loc.
Local Arguments llist {_} _ _ !_ /.

Lemma llist_fmap {B} (J : B → val → aProp) (f : A → B) l xs :
  □ (∀ x v, I x v -∗ J (f x) v) -∗
  llist I l xs -∗ llist J l (f <$> xs).
Proof.
  iIntros "#Hf Hll". iInduction xs as [|x xs] "IH" forall (l); csimpl; auto.
  iDestruct "Hll" as (v l') "(Hx & Hl & Hll)". iExists _, _. iFrame "Hl".
  iSplitL "Hx"; first by iApply "Hf". by iApply "IH".
Qed.

Lemma lnil_spec :
  ⊢ WP lnil #() {{ w, ∃ l:loc, ⌜⌜ w = #l ⌝⌝ ∗ llist I l [] }}.
Proof. wp_rec!. wp_alloc k; eauto. Qed.

Lemma lcons_spec l x xs v :
  llist I l xs -∗ I x v -∗ WP lcons v #l {{ w, ⌜⌜ w = #() ⌝⌝ ∗ llist I l (x :: xs) }}.
Proof.
  iIntros "Hll Hx". destruct xs as [|x' xs]; simpl; wp_rec!.
  - wp_load. wp_alloc k. wp_store. eauto with iFrame.
  - iDestruct "Hll" as (v' l') "(HIx' & Hl & Hll)".
    wp_load. wp_alloc k. wp_store. eauto 10 with iFrame.
Qed.

Lemma lisnil_spec l xs:
  llist I l xs -∗
  WP lisnil #l {{ w, ⌜⌜ w = #(if xs is [] then true else false) ⌝⌝ ∗ llist I l xs }}.
Proof.
  iIntros "Hll". destruct xs as [|x xs]; simpl; wp_rec!.
  - wp_load!. auto.
  - iDestruct "Hll" as (v l') "(HIx & Hl & Hll)". wp_load!; eauto with iFrame.
Qed.

(** Not the nicest spec, it leaks *)
Lemma lhead_spec_aux l x xs :
  llist I l (x :: xs) -∗
  WP lhead #l {{ v, ∃ l' : loc, I x v ∗ l ↦ SumV "cons" (v,#l') ∗ llist I l' xs }}.
Proof.
  iIntros "/=". iDestruct 1 as (v l') "(HIx & Hl & Hll)".
  wp_rec!. wp_load!. eauto with iFrame.
Qed.
Lemma lpop_spec_aux l l' v xs :
  l ↦ SumV "cons" (v,#l') -∗ llist I l' xs -∗
  WP lpop #l {{ v', ⌜⌜ v' = v ⌝⌝ ∗ llist I l xs }}.
Proof.
  iIntros "Hl Hll". wp_rec; wp_load. destruct xs as [|x' xs]; simpl.
  - wp_load. wp_store. wp_free!. eauto with iFrame.
  - iDestruct "Hll" as (v' l'') "(HIx' & Hl' & Hll)".
    wp_load. wp_store. wp_free!. eauto with iFrame.
Qed.

Lemma lhead_spec l x xs :
  llist I l (x :: xs) -∗
  WP lhead #l {{ v, I x v ∗ (I x v -∗ llist I l (x :: xs)) }}.
Proof.
  iIntros "Hll". iApply (lhead_spec_aux with "Hll").
  iIntros "!>" (l' w) "[$ ?] HIx /=". eauto with iFrame.
Qed.

Lemma lpop_spec l x xs :
  llist I l (x :: xs) -∗ WP lpop #l {{ v, I x v ∗ llist I l xs }}.
Proof.
  iIntros "/=". iDestruct 1 as (v l') "(HIx & Hl & Hll)".
  iApply (lpop_spec_aux with "[$] [$]"); iIntros "!> $ //".
Qed.

Lemma llookup_spec l i xs x :
  xs !! i = Some x → llist I l xs -∗
  WP llookup #l #i {{ v, I x v ∗ (I x v -∗ llist I l xs) }}.
Proof.
  iIntros (Hi) "Hll".
  iInduction xs as [|x' xs] "IH" forall (l i x Hi); [done|simpl; wp_rec!].
  destruct i as [|i]; simplify_eq/=; wp_pures.
  - iApply (lhead_spec with "Hll"); iIntros (v) "[HI Hll]".
  - iDestruct "Hll" as (v l') "(HIx' & Hl' & Hll)". wp_load!.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    iApply ("IH" with "[//] Hll"); iIntros "!>" (v') "[HIx Hll]".
    iIntros "{$HIx} HIx". iExists v, l'. iFrame. by iApply "Hll".
Qed.

Lemma llength_spec l xs :
  llist I l xs -∗ WP llength #l {{ v, ⌜⌜ v = #(length xs) ⌝⌝ ∗ llist I l xs }}.
Proof.
  iIntros "Hll".
  iInduction xs as [|x xs] "IH" forall (l); simpl; wp_rec.
  - wp_load!. iSplit; [done|]. iApply "Hll".
  - iDestruct "Hll" as (v l') "(HIx & Hl' & Hll)". wp_load!.
    iApply ("IH" with "Hll"); iIntros "!> Hll"; wp_pures.
    rewrite (Nat2Z.inj_add 1). eauto with iFrame.
Qed.

Lemma lapp_aux_spec l1 l2 xs1 xs2 :
  llist I l1 xs1 -∗ llist I l2 xs2 -∗
  WP lapp_aux #l1 #l2 {{ w, ⌜⌜ w = #() ⌝⌝ ∗ llist I l1 (xs1 ++ xs2) ∗ (∃ v, l2 ↦ v) }}.
Proof.
  iIntros "Hll1 Hll2".
  iInduction xs1 as [|x1 xs1] "IH" forall (l1); simpl; wp_rec!.
  - wp_load. wp_pures. destruct xs2 as [|x2 xs2]; simpl.
    + wp_load. wp_store. eauto with iFrame.
    + iDestruct "Hll2" as (v2 l2') "(HIx2 & Hl2 & Hll2)". wp_load. wp_store.
      iSplit; [done|]. iSplitR "Hl2"; eauto 10 with iFrame.
  - iDestruct "Hll1" as (v1 l') "(HIx1 & Hl1 & Hll1)". wp_load!.
    iApply ("IH" with "Hll1 Hll2"); iIntros "!> [HHll Hl2]".
    iSplit; [done|]. eauto 10 with iFrame.
Qed.

Lemma lapp_spec l1 l2 xs1 xs2 :
  llist I l1 xs1 -∗ llist I l2 xs2 -∗
  WP lapp #l1 #l2 {{ w, ⌜⌜ w = #() ⌝⌝ ∗ llist I l1 (xs1 ++ xs2) }}.
Proof.
  iIntros "Hll1 Hll2". wp_rec. iApply (lapp_aux_spec with "Hll1 Hll2").
  iIntros "!> [Hll1 Hll2]". iDestruct "Hll2" as (?) "?". wp_free. by eauto.
Qed.

Lemma lprep_spec l1 l2 xs1 xs2 :
  llist I l1 xs2 -∗ llist I l2 xs1 -∗
  WP lprep #l1 #l2
  {{ w, ⌜⌜ w = #() ⌝⌝ ∗ llist I l1 (xs1 ++ xs2) }}.
Proof.
  iIntros "Hll1 Hll2". wp_rec. wp_pures.
  iApply (lapp_aux_spec with "Hll2 Hll1"); iIntros "!> [Hll2 Hl1]".
  iDestruct "Hl1" as (w) "Hl1".
  destruct (xs1 ++ xs2) as [|x xs]; simpl; wp_pures.
  - wp_load. wp_store. wp_free. eauto with iFrame.
  - iDestruct "Hll2" as (v l') "(HIx & Hl2 & Hll2)". wp_load. wp_store. wp_free.
    eauto with iFrame.
Qed.

Lemma lsnoc_spec l xs x v :
  llist I l xs -∗ I x v -∗
  WP lsnoc #l v {{ w, ⌜⌜ w = #() ⌝⌝ ∗ llist I l (xs ++ [x]) }}.
Proof.
  iIntros "Hll HIx".
  iInduction xs as [|x' xs] "IH" forall (l); simpl; wp_rec; wp_pures.
  - wp_load. wp_pures. iApply lnil_spec; iIntros "!>" (l') "Hl'".
    wp_store. iSplit; [done|]; eauto with iFrame.
  - iDestruct "Hll" as (v' l') "(HIx' & Hl & Hll)". wp_load; wp_pures.
    iApply ("IH" with "Hll HIx"); iIntros "!> Hll". eauto with iFrame.
Qed.

Lemma lsplit_at_spec l xs (n : nat) :
  llist I l xs -∗
  WP lsplit_at #l #n {{ k, ∃ l', ⌜⌜ k = #l' ⌝⌝ ∗
                                llist I l (take n xs) ∗ llist I l' (drop n xs) }}.
Proof.
  iIntros "Hll".
  iInduction xs as [|x xs] "IH" forall (l n); simpl; wp_rec; wp_pures.
  - destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. wp_pures. eauto with iFrame.
    + wp_load. iApply lnil_spec; iIntros "!>" (l') "Hl'". eauto with iFrame.
  - iDestruct "Hll" as (v l') "(HIx & Hl & Hll)".
    destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. wp_pures. eauto 10 with iFrame.
    + wp_load; wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
      iApply ("IH" with "[$]"); iIntros "!>" (l'') "[Hl' Hl'']".
      eauto 10 with iFrame.
Qed.

Lemma lsplit_spec l xs :
  llist I l xs -∗
  WP lsplit #l {{ k, ∃ l' xs1 xs2, ⌜⌜ k = #l' ⌝⌝ ∗ ⌜⌜ xs = xs1 ++ xs2 ⌝⌝ ∗
                                   llist I l xs1 ∗ llist I l' xs2 }}.
Proof.
  iIntros "Hl". wp_rec.
  iApply (llength_spec with "Hl"); iIntros "!> Hl". wp_pures.
  rewrite Z.quot_div_nonneg; [|lia..]. rewrite -(Nat2Z.inj_div _ 2).
  iApply (lsplit_at_spec with "Hl"); iIntros "!>" (l') "[Hl Hk]".
  iExists _, _, _. iFrame. by rewrite take_drop.
Qed.

Lemma lreverse_at_spec l xs acc ys :
  llist I l xs -∗ llist I acc ys -∗
  WP lreverse_at #l #acc {{ k, ∃ l', ⌜⌜ k = #l' ⌝⌝ ∗
                                     llist I l' (reverse xs ++ ys) }}.
Proof.
  iIntros "Hl Hacc".
  iInduction xs as [|x xs] "IH" forall (l acc ys); simpl; wp_rec.
  - wp_load. wp_free!. eauto with iFrame.
  - iDestruct "Hl" as (v l') "[HI [Hl Hl']]".
    wp_load!. iApply (lcons_spec with "Hacc HI"); iIntros "!> Hacc".
    wp_free. iApply ("IH" with "Hl' Hacc"); iIntros "!>" (l'') "Hl''".
    rewrite reverse_cons -assoc_L. eauto with iFrame.
Qed.

Lemma lreverse_spec l xs :
  llist I l xs -∗ WP lreverse #l {{ w, ⌜⌜ w = #() ⌝⌝ ∗ llist I l (reverse xs) }}.
Proof.
  iIntros "Hl". wp_rec.
  destruct xs as [|x xs]; simpl.
  - wp_load. wp_alloc l' as "Hl'".
    iApply lnil_spec; iIntros "!>" (lnil) "Hlnil".
    iAssert (llist I l' []) with "Hl'" as "Hl'".
    iApply (lreverse_at_spec with "Hl' Hlnil"); iIntros "!>" (l'') "Hl''".
    wp_load. wp_store. rewrite right_id_L. wp_free. eauto with iFrame.
  - iDestruct "Hl" as (v lcons) "[HI [Hlcons Hrec]]".
    wp_load. wp_alloc l' as "Hl'".
    iApply lnil_spec; iIntros "!>" (lnil) "Hlnil".
    iApply (lreverse_at_spec _ (x :: xs) with "[Hl' HI Hrec] Hlnil").
    { simpl; eauto with iFrame. }
    iIntros "!>" (l'') "Hl''". rewrite right_id_L.
    destruct (reverse _) as [|y ys].
    + wp_load. wp_store. wp_free. eauto with iFrame.
    + simpl. iDestruct "Hl''" as (v' lcons') "[HI [Hcons Hrec]]".
      wp_load. wp_store. wp_free. eauto with iFrame.
Qed.

End lists.
