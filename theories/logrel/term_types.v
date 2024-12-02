(** This file contains the definitions of the semantic interpretations of the
term type formers of the type system. The semantic interpretation of a type
(former) is a unary Iris predicate on values [val → iProp], which determines
when a value belongs to a certain type.

The following types are defined:
- [unit], [bool], [int]: basic types for unit, Boolean and integer values,
  respectively.
- [any]: inhabited by all values.
- [A ⊸ B]: the type of affine functions from [A] to [B]. Affine functions can
  only be invoked once, since they might have captured affine resources.
- [A → B]: the type of non-affine (copyable) functions from [A] to [B]. These
  can be invoked any number of times. This is simply syntactic sugar for
  [copy (A ⊸ B)].
- [A * B], [A + B], [∀ X, A], [∃ X, A]: products, sums, universal types,
  existential types.
- [copy A]: inhabited by those values in the type [A] which are copyable. In the
  case of functions, for instance, functions (closures) which capture affine
  resources are not copyable, whereas functions that do not capture resources are.
- [copy- A]: acts as a kind of "inverse" to [copy A]. More precisely, we have
  that [copy- (copy A) :> A]. This type is used to indicate the results of
  operations that might consume a resource, but do not always do so, depending
  on whether the type [A] is copyable. Such operations result in a [copy- A],
  which can be turned into an [A] using subtyping when [A] is copyable.
- [ref_uniq A]: the type of uniquely-owned mutable references to a value of type [A].
  Since the reference is guaranteed to be unique, it is possible for the type [A]
  contained in the reference to change to a different type [B] by assigning to
  the reference.
- [chan P]: the type of channels, governed by the session type [P].

In addition, some important properties, such as contractivity and
non-expansiveness of these type formers is proved. This is important in order to
use these type formers to define recursive types. *)
From iris.bi.lib Require Import core.
From dlfactris.logrel Require Export model.

Definition lty_unit : ltty := Ltty (λ w, ⌜⌜ w = #() ⌝⌝%I).
Definition lty_bool : ltty := Ltty (λ w, ∃ b : bool, ⌜⌜ w = #b ⌝⌝)%I.
Definition lty_int : ltty := Ltty (λ w, ∃ n : Z, ⌜⌜ w = #n ⌝⌝)%I.
Definition lty_any : ltty := Ltty (λ w, emp%I).                                  (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=7109ff19 *)

Definition lty_arr (A1 A2 : ltty) : ltty := Ltty (λ w,
  ∀ v,  ▷ ltty_car A1 v -∗ WP w v {{ ltty_car A2 }})%I.
Definition lty_prod (A1 A2 : ltty) : ltty := Ltty (λ w,
  ∃ w1 w2, ⌜⌜w = (w1,w2)%V⌝⌝ ∗ ltty_car A1 w1 ∗ ltty_car A2 w2)%I.

Definition lty_sum (As : gmap string ltty) : ltty := Ltty (λ w,
  (∃ t v, ⌜⌜ is_Some (As !! t) ⌝⌝ ∗ ⌜⌜w = SumV t v⌝⌝ ∗ ltty_car (As !!! t) v))%I.

Definition lty_forall {k} (C : lty k → ltty) : ltty :=
  Ltty (λ w, ∀ X, WP w #() {{ ltty_car (C X) }})%I.
Definition lty_exist {k} (C : lty k → ltty) : ltty :=
  Ltty (λ w, ∃ X, ltty_car (C X) w)%I.

Definition lty_copy (A : ltty) : ltty := Ltty (λ w, □ ltty_car A w)%I.
Definition lty_copy_minus (A : ltty) : ltty :=
  Ltty (λ w, <affine> coreP (ltty_car A w))%I.

Definition lty_ref_uniq (A : ltty) : ltty := Ltty (λ w,
  ∃ (l : loc) (v : val), ⌜⌜w = #l⌝⌝ ∗ l ↦ v ∗ ▷ ltty_car A v)%I.

Definition lty_chan (P : lsty) : ltty :=
  Ltty (λ w, w ↣ lsty_car P)%I.

Global Instance: Params (@lty_forall) 1 := {}.
Global Instance: Params (@lty_exist) 1 := {}.
Global Instance: Params (@lty_ref_uniq) 2 := {}.

Notation any := lty_any.
Notation "()" := lty_unit : lty_scope.
Notation "'copy' A" := (lty_copy A) (at level 10) : lty_scope.
Notation "'copy-' A" := (lty_copy_minus A) (at level 10) : lty_scope.

Notation "A ⊸ B" := (lty_arr A B)
  (at level 99, B at level 200, right associativity) : lty_scope.
Notation "A → B" := (lty_copy (lty_arr A B)) : lty_scope.
Infix "*" := lty_prod : lty_scope.

Notation "∀ X1 .. Xn , C" :=
  (lty_forall (λ X1, .. (lty_forall (λ Xn, C%lty)) ..)) : lty_scope.
Notation "∃ X1 .. Xn , C" :=
  (lty_exist (λ X1, .. (lty_exist (λ Xn, C%lty)) ..)) : lty_scope.

Notation "'ref_uniq' A" := (lty_ref_uniq A) (at level 10) : lty_scope.

Notation "'chan' A" := (lty_chan A) (at level 10) : lty_scope.

Section term_types.
  Implicit Types A : ltty.

  Global Instance lty_copy_ne : NonExpansive (@lty_copy).
  Proof. solve_proper. Qed.
  Global Instance lty_copy_minus_ne : NonExpansive (@lty_copy_minus).
  Proof. solve_proper. Qed.

  Global Instance lty_arr_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) lty_arr.
  Proof.
    intros A A' ? B B' ?. apply Ltty_ne=> v. f_equiv=> w.
    f_equiv; [by f_contractive|].
    apply: wp_contractive=> v'. dist_later_intro as n' Hn'. by f_equiv.
  Qed.
  Global Instance lty_arr_ne : NonExpansive2 lty_arr.
  Proof. solve_proper. Qed.

  Global Instance lty_prod_ne : NonExpansive2 (@lty_prod).
  Proof. solve_proper. Qed.
  Global Instance lty_sum_ne : NonExpansive (@lty_sum).
  Proof. solve_proper. Qed.

  Global Instance lty_forall_contractive k n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_forall k).
  Proof.
    intros F F' A. apply Ltty_ne=> w. f_equiv=> B.
     apply: wp_contractive=> v'. specialize (A B).
    dist_later_intro as n' Hn'. by f_equiv.
  Qed.
  Global Instance lty_forall_ne k n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall k).
  Proof. solve_proper. Qed.

  Global Instance lty_exist_ne k n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_exist k).
  Proof. solve_proper. Qed.

  Global Instance lty_ref_uniq_contractive : Contractive lty_ref_uniq.
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_uniq_ne : NonExpansive lty_ref_uniq.
  Proof. solve_proper. Qed.

  Global Instance lty_chan_contractive : Contractive lty_chan.
  Proof. solve_contractive. Qed.
  Global Instance lty_chan_ne : NonExpansive lty_chan.
  Proof. solve_proper. Qed.
End term_types.
