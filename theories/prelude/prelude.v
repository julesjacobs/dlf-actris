From stdpp Require Export ssreflect.
From iris.algebra Require Import list gmap.
From iris.bi Require Import bi.
From iris.prelude Require Export options.

(** NOTATIONS *)
Notation "⌜⌜ φ ⌝⌝" := (<affine> ⌜ φ ⌝)%I : bi_scope.
Notation "x ≡≡ y" := (<affine> (x ≡ y))%I (at level 70) : bi_scope.
Reserved Notation "c ↣ p" (at level 20, format "c  ↣  p").

(** UPSTREAM to std++ *)
Definition prod_swap {A B} : A * B → B * A := λ '(x,y), (y,x).

Lemma elem_of_set_map_prod_swap `{Countable A} (e : gset (A * A)) (x y : A) :
  (x, y) ∈@{gset _} set_map prod_swap e ↔ (y, x) ∈ e.
Proof.
  rewrite elem_of_map. split.
  - intros [[??]]; naive_solver.
  - intros. by exists (y,x).
Qed.

Lemma not_rtsc {A} {R : relation A} x y :
  (∀ y', ¬R x y' ∧ ¬R y' x) →
  rtsc R x y → x = y.
Proof. induction 2 as [|??? []]; naive_solver. Qed.

Lemma rtc_iff {A} (R1 R2 : relation A) x y :
  (∀ x y, R1 x y ↔ R2 x y) →
  rtc R1 x y ↔ rtc R2 x y.
Proof. split; apply rtc_subrel; naive_solver. Qed.

Lemma sc_or {A} (R : relation A) x y :
  sc R x y ↔ R x y ∨ R y x.
Proof. done. Qed.

Lemma lookup_take_spec {A} (xs : list A) k n :
  take n xs !! k = if decide (k < n) then xs !! k else None.
Proof. case_decide; eauto using lookup_take, lookup_take_ge with lia. Qed.

Lemma lookup_list_singleton_spec {A} k (x : A) :
  [x] !! k = if decide (k = 0) then Some x else None.
Proof. by destruct k. Qed.

Lemma lookup_app_add {A} (l1 l2 : list A) (i : nat) :
  (l1 ++ l2) !! (length l1 + i) = l2 !! i.
Proof. by induction l1. Qed.

Lemma lookup_delete_lr {A} (xs : list A) (i j : nat) :
  delete i xs !! j = if decide (j < i) then xs !! j else xs !! (S j).
Proof. case_decide; eauto using lookup_delete_lt, lookup_delete_ge with lia. Qed.

Lemma split_first {A} (xs : list A) a :
  xs !! 0 = Some a → xs = [a] ++ drop 1 xs.
Proof. destruct xs as [|? []]; naive_solver. Qed.

Lemma split_last {A} (xs : list A) a :
  last xs = Some a → xs = take (length xs - 1) xs ++ [a].
Proof.
  intros Hlst. rewrite -{1}(take_drop (length xs - 1) xs). f_equal.
  apply last_Some in Hlst as [xs' ->].
  rewrite length_app /=. replace (length xs' + 1 - 1) with (length xs') by lia.
  by rewrite drop_app_length.
Qed.

Lemma split_both {A} (xs : list A) a :
  1 < length xs → xs !! 0 = Some a → last xs = Some a →
  xs = a :: drop 1 (take (length xs - 1) xs) ++ [a].
Proof.
  intros Hlen Hfst%split_first Hlst%split_last; simplify_eq/=.
  rewrite -drop_app_le ?length_take; last lia.
  by rewrite -Hlst.
Qed.

Lemma last_take {A} i (xs : list A) :
  i < length xs → last (take (S i) xs) = xs !! i.
Proof.
  intros. rewrite last_lookup lookup_take ?length_take; last lia.
  f_equal; lia.
Qed.

Lemma last_take_Some {A} i (xs : list A) x :
  xs !! i = Some x → last (take (S i) xs) = Some x.
Proof. intros. rewrite last_take; eauto using lookup_lt_Some. Qed.

Lemma last_drop {A} (xs : list A) i :
  i < length xs → last (drop i xs) = last xs.
Proof. intros. rewrite !last_lookup lookup_drop length_drop. f_equal; lia. Qed.

Lemma lookup_update {A} i j (xs : list A) x :
  <[i:=x]> xs !! j = if decide (i = j ∧ j < length xs) then Some x else xs !! j.
Proof.
  revert i j. induction xs as [|x' xs IH]; intros [|i] [|j];
    simpl; [repeat case_decide; auto with lia..|].
  rewrite IH. repeat case_decide; auto with lia.
Qed.

Lemma lookup_insert_spec `{FinMap K M} {A} (m : M A) i j x :
  <[i:=x]> m !! j = if (decide (i = j)) then Some x else m !! j.
Proof. case_decide; subst; eauto using lookup_insert, lookup_insert_ne. Qed.

Lemma lookup_delete_spec `{FinMap K M} {A} (m : M A) i j :
  delete i m !! j = if (decide (i = j)) then None else m !! j.
Proof. case_decide; [apply lookup_delete_None|apply lookup_delete_ne]; auto. Qed.

(** UPSTREAM to Iris *)
Section quotient.
  Context `{Equiv A} (R : A → A → siProp).
  Context (Requiv : ∀ x y, x ≡ y ↔ ⊢ R x y).
  Context (Rrefl : ∀ x, ⊢ R x x).
  Context (Rsymm : ∀ x y, R x y ⊢ R y x).
  Context (Rtrans : ∀ x y z, R x y ∧ R y z ⊢ R x z).

  Local Instance quotient_dist : Dist A := λ n x y,
    siProp_holds (R x y) n.

  Lemma quotient_ofe_mixin : OfeMixin A.
  Proof using Type*.
    split; rewrite /dist /quotient_dist.
    - intros x y. rewrite Requiv. split.
      + intros HR n. apply HR. by siProp.unseal.
      + intros HR. split=> n. auto.
    - split.
      + intros x. apply Rrefl. by siProp.unseal.
      + intros x y Hxy. by apply Rsymm.
      + intros x y z ??. eapply Rtrans. siProp.unseal. by split.
    - intros n m x y ??. eapply siProp_closed; [done|]. lia.
  Qed.

  Lemma quotient_equiv (x1 x2 : Ofe A quotient_ofe_mixin) : x1 ≡ x2 ⊣⊢ R x1 x2.
  Proof. rewrite /internal_eq. by siProp.unseal. Qed.
End quotient.
