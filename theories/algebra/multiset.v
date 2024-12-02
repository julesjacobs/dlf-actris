From iris.algebra Require Import list.
From iris.bi Require Export sbi.
From iris.proofmode Require Import tactics.
From iris.bi Require Import sbi_unfold.
From dlfactris.prelude Require Export prelude.

Record multiset A := MultiSet { multiset_car : list A }.
Arguments MultiSet {_} _.
Arguments multiset_car {_} _.

Section multiset.
  Context {A : ofe}.
  Implicit Types x y : A.
  Implicit Types X Y : multiset A.

  Global Instance multiset_dist : Dist (multiset A) := λ n X1 X2,
    ∃ xs, multiset_car X1 ≡ₚ xs ∧ xs ≡{n}≡ multiset_car X2.
  Global Instance multiset_equiv : Equiv (multiset A) := λ X1 X2,
    ∀ n, X1 ≡{n}≡ X2.
  Global Instance multiset_empty : Empty (multiset A) := MultiSet [].
  Global Instance multiset_disj_union : DisjUnion (multiset A) := λ X1 X2,
    MultiSet (multiset_car X1 ++ multiset_car X2).
  Global Instance multiset_singleton : SingletonMS A (multiset A) := λ x,
    MultiSet [x].

  Lemma multiset_ofe_mixin : OfeMixin (multiset A).
  Proof.
    split.
    - done.
    - intros n. rewrite /dist /multiset_dist. split.
      + intros X. by exists (multiset_car X).
      + intros X1 X2 (xs&?&?). by eapply dist_Permutation.
      + intros X1 X2 X3 (xs1&?&?) (xs2&?&?).
        destruct (dist_Permutation n xs1 (multiset_car X2) xs2) as (xs&?&?); [done..|].
        exists xs; split; by etrans.
    - intros n m X1 X2 (xs&?&?) ?. exists xs. split; [done|]. by eapply dist_lt.
  Qed.
  Canonical Structure multisetO := Ofe (multiset A) multiset_ofe_mixin.

  Global Instance multiset_disj_union_ne :
    NonExpansive2 (@disj_union (multiset A) _).
  Proof.
    intros n X1 X2 (xs&?&?) Y1 Y2 (ys&?&?); simpl.
    exists (xs ++ ys); simpl; split; by f_equiv.
  Qed.
  Global Instance multiset_disj_union_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@disj_union (multiset A) _).
  Proof. apply: ne_proper_2. Qed.

  Global Instance multiset_singleton_ne :
    NonExpansive (@singletonMS A (multiset A) _).
  Proof. intros n x1 x2 ?. exists [x1]; simpl. by repeat constructor. Qed.
  Global Instance multiset_singleton_proper :
    Proper ((≡) ==> (≡)) (@singletonMS A (multiset A) _).
  Proof. apply: ne_proper. Qed.

  Global Instance multiset_disj_union_comm : Comm (≡@{multiset A}) (⊎).
  Proof.
    intros X1 X2 n. exists (multiset_car (X2 ⊎ X1)).
    split; [|done]. by rewrite /= (comm (++)).
  Qed.
  Global Instance multiset_disj_union_assoc : Assoc (≡@{multiset A}) (⊎).
  Proof.
    intros X1 X2 X3 n. exists (multiset_car (X1 ⊎ (X2 ⊎ X3))).
      by rewrite /= (assoc (++)).
  Qed.
  Global Instance multiset_disj_union_left_id : LeftId (≡@{multiset A}) ∅ (⊎).
  Proof. intros X n. by exists (multiset_car X). Qed.
  Global Instance multiset_disj_union_right_id : RightId (≡@{multiset A}) ∅ (⊎).
  Proof. intros X. by rewrite comm left_id. Qed.

  Global Instance multiset_disj_union_dist_inj n X :
    Inj (dist n) (dist n) (X ⊎.).
  Proof.
    destruct X as [xs]. intros [ys1] [ys2] (ys&Hperm&Hdist); hnf; simpl in *.
    revert ys Hperm Hdist.
    induction xs as [|x xs IH]; intros ys Hperm Hdist; simpl in *.
    { by exists ys. }
    apply Permutation_cons_inv_l in Hperm as ([|y ys1']&ys2'&->&?); simpl in *;
      apply (inj2 _) in Hdist as [Hy ?]; first by eauto.
    apply (IH (ys1' ++ y :: ys2')).
    - by rewrite -Permutation_middle.
    - by rewrite Hy.
  Qed.
  Global Instance multiset_disj_union_inj X : Inj (≡) (≡) (X ⊎.).
  Proof. intros X1 X2. rewrite !equiv_dist=> ? n. by apply (inj (X ⊎.)). Qed.
  Lemma multiset_disj_union_injI `{!Sbi PROP} X X1 X2 :
    X ⊎ X1 ≡ X ⊎ X2 ⊣⊢@{PROP} X1 ≡ X2.
  Proof. sbi_unfold=> n. apply: inj_iff. Qed.

  Global Instance multiset_singleton_dist_inj n :
    Inj (dist n) (dist n) (@singletonMS A (multiset A) _).
  Proof.
    intros x1 x2 (xs&<-%Permutation_singleton_l&Hdist); simpl in *.
    by apply (inj2 cons) in Hdist as [? _].
  Qed.
  Global Instance multiset_singleton_inj :
    Inj (≡) (≡) (@singletonMS A (multiset A) _).
  Proof. intros X1 X2. rewrite !equiv_dist=> ? n. by apply (inj singleton). Qed.
  Lemma multiset_singleton_equivI `{!Sbi PROP} x1 x2 :
    {[+ x1 +]} ≡ {[+ x2 +]} ⊣⊢@{PROP} x1 ≡ x2.
  Proof. sbi_unfold=> n. apply: inj_iff. Qed.

  Lemma multiset_empty_dist_eq n X : X ≡{n}≡ ∅ ↔ X = ∅.
  Proof.
    split; [|by intros ->].
    intros (xs&Hperm&->%nil_dist_eq). apply Permutation_nil_r in Hperm.
    destruct X; naive_solver.
  Qed.
  Lemma multiset_empty_equiv_eq X : X ≡ ∅ ↔ X = ∅.
  Proof.
    split; [|by intros ->].
    rewrite equiv_dist=> /(_ 0). apply multiset_empty_dist_eq.
  Qed.
  Global Instance multiset_empty_discrete : Discrete (@empty (multiset A) _).
  Proof.
    intros ?. rewrite 2!(symmetry_iff _ ∅) multiset_empty_dist_eq=> -> //.
  Qed.

  (** No [dist], [equiv], [internal_eq] versions: Just move equalities with ∅
  to the [=] level, and use the lemmas there. *)
  Lemma multiset_singleton_neq_empty x : {[+ x +]} ≠@{multiset A} ∅.
  Proof. done. Qed.
  Lemma multiset_disj_union_eq_empty X1 X2 : X1 ⊎ X2 = ∅ ↔ X1 = ∅ ∧ X2 = ∅.
  Proof. destruct X1 as [[]], X2 as [[]]; naive_solver. Qed.

  Lemma multiset_cross_split n (Xa Xb Xc Xd : multiset A) :
    Xa ⊎ Xb ≡{n}≡ Xc ⊎ Xd ↔
    ∃ Xac Xad Xbc Xbd,
      Xa ≡{n}≡ Xac ⊎ Xad ∧ Xb ≡{n}≡ Xbc ⊎ Xbd ∧
      Xc ≡{n}≡ Xac ⊎ Xbc ∧ Xd ≡{n}≡ Xad ⊎ Xbd.
  Proof.
    split.
    - intros (xs&Hperm&(xsc&xsd&->&?&?)%app_dist_eq).
      apply Permutation_cross_split in Hperm as (xsac&xsad&xsbc&xsbd&?&?&?&?).
      exists (MultiSet xsac), (MultiSet xsad), (MultiSet xsbc), (MultiSet xsbd).
      split_and!; symmetry; by eexists.
    - intros(Xac&Xad&Xbc&Xbd&->&->&->&->).
      rewrite -!assoc. f_equiv. by rewrite !assoc (comm _ Xbc).
  Qed.
  Lemma multiset_cross_splitI `{!Sbi PROP} (Xa Xb Xc Xd : multiset A) :
    Xa ⊎ Xb ≡ Xc ⊎ Xd ⊣⊢@{PROP}
    ∃ Xac Xad Xbc Xbd,
      Xa ≡ Xac ⊎ Xad ∧ Xb ≡ Xbc ⊎ Xbd ∧
      Xc ≡ Xac ⊎ Xbc ∧ Xd ≡ Xad ⊎ Xbd.
  Proof. sbi_unfold=> n. apply multiset_cross_split. Qed.

  Lemma multiset_disj_union_singleton n X1 X2 x :
    X1 ⊎ X2 ≡{n}≡ {[+ x +]} ↔
    (X1 = ∅ ∧ X2 ≡{n}≡ {[+ x +]}) ∨ (X1 ≡{n}≡ {[+ x +]} ∧ X2 = ∅).
  Proof.
    split; [|intros [[-> ?]|[? ->]]; by rewrite ?right_id].
    destruct X1 as [xs1], X2 as [xs2].
    intros (xs&Hperm&(x'&->&?)%list_singleton_dist_eq).
    apply Permutation_singleton_r in Hperm as [[??]|[??]]%app_eq_unit;
      simplify_eq/=; [left|right]; by repeat econstructor.
  Qed.
  Lemma multiset_disj_union_singletonI `{!Sbi PROP} X1 X2 x :
    X1 ⊎ X2 ≡ {[+ x +]} ⊣⊢@{PROP}
    (⌜ X1 = ∅ ⌝ ∧ X2 ≡ {[+ x +]}) ∨ (X1 ≡ {[+ x +]} ∧ ⌜ X2 = ∅ ⌝).
  Proof. sbi_unfold=> n. apply multiset_disj_union_singleton. Qed.

  Lemma multiset_singleton_disj_union_singleton n x1 X2 y1 :
    {[+ x1 +]} ⊎ X2 ≡{n}≡ {[+ y1 +]} ↔ x1 ≡{n}≡ y1 ∧ X2 = ∅.
  Proof.
    split.
    - intros [[[]%multiset_singleton_neq_empty _]
             |[?%(inj _) ->]]%multiset_disj_union_singleton; auto.
    - intros [-> ->]. by rewrite right_id.
  Qed.
  Lemma multiset_singleton_disj_union_singletonI `{!Sbi PROP} x1 X2 y1 :
    {[+ x1 +]} ⊎ X2 ≡ {[+ y1 +]} ⊣⊢@{PROP} x1 ≡ y1 ∧ ⌜ X2 = ∅ ⌝.
  Proof. sbi_unfold=> n. apply multiset_singleton_disj_union_singleton. Qed.

  Lemma multiset_singleton_disj_union_singletons n x1 X2 y1 y2 :
    {[+ x1 +]} ⊎ X2 ≡{n}@{multiset A}≡ {[+ y1; y2 +]} ↔
    x1 ≡{n}≡ y1 ∧ X2 ≡{n}≡ {[+ y2 +]} ∨ x1 ≡{n}≡ y2 ∧ X2 ≡{n}≡ {[+ y1 +]}.
  Proof.
    split.
    - intros (Xac&Xad&Xbc&Xbd&Hx1&->&Hy1&Hy2)%multiset_cross_split.
      apply symmetry in Hx1 as [[-> Had]|[Hac ->]]%multiset_disj_union_singleton.
      + right. rewrite Had in Hy2.
        apply symmetry in Hy2 as [-> ->]%multiset_singleton_disj_union_singleton.
        by rewrite (comm (⊎)).
      + left. rewrite Hac in Hy1.
        by apply symmetry in Hy1 as [-> ->]%multiset_singleton_disj_union_singleton.
    - intros [[-> ->]|[-> ->]]; [done|by rewrite comm].
  Qed.
  Lemma multiset_singleton_disj_union_singletonsI `{!Sbi PROP} x1 X2 y1 y2 :
    {[+ x1 +]} ⊎ X2 ≡ {[+ y1; y2 +]} ⊣⊢@{PROP}
    x1 ≡ y1 ∧ X2 ≡ {[+ y2 +]} ∨ x1 ≡ y2 ∧ X2 ≡ {[+ y1 +]}.
  Proof. sbi_unfold=> n. apply multiset_singleton_disj_union_singletons. Qed.

  Lemma multiset_singleton_disj_union n x X y Y :
    {[+ x +]} ⊎ X ≡{n}@{multiset A}≡ {[+ y +]} ⊎ Y ↔
    (x ≡{n}≡ y ∧ X ≡{n}≡ Y) ∨ ∃ Z, X ≡{n}≡ {[+ y +]} ⊎ Z ∧ Y ≡{n}≡ {[+ x +]} ⊎ Z.
  Proof.
    split.
    - intros (Xac&Xad&Xbc&Xbd&Hx&HX&Hy&HY)%multiset_cross_split.
      apply symmetry in Hx as [[-> Had]|[Hac ->]]%multiset_disj_union_singleton.
      + rewrite left_id in Hy. right. exists Xbd. by rewrite HX HY Had -!Hy.
      + rewrite Hac {Hac} in Hy.
        apply symmetry in Hy as [? ->]%multiset_singleton_disj_union_singleton.
        left. by rewrite HX HY.
    - intros [[-> ->]|[Z [-> ->]]]; first done.
      by rewrite !assoc (comm _ (singletonMS _)).
  Qed.

  Lemma multiset_singleton_disj_unionI `{!Sbi PROP} x X y Y :
    {[+ x +]} ⊎ X ≡ {[+ y +]} ⊎ Y ⊣⊢@{PROP}
    (x ≡ y ∧ X ≡ Y) ∨ ∃ Z, X ≡ {[+ y +]} ⊎ Z ∧ Y ≡ {[+ x +]} ⊎ Z.
  Proof. sbi_unfold=> n. apply multiset_singleton_disj_union. Qed.
End multiset.

Global Arguments multisetO : clear implicits.
