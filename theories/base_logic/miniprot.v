From iris.bi Require Export bi.
From iris.bi Require Import sbi_unfold.
From dlfactris.prelude Require Export prelude.

Inductive action := ASend | ARecv.
Canonical Structure actionO := leibnizO action.

Record miniprot (V PROP : Type) := MiniProt {                                    (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=736af260 *)
  prot_action : action;
  prot_pred :> V → PROP;
}.
Add Printing Constructor miniprot.
Global Arguments MiniProt {_ _}.
Global Arguments prot_action {_ _}.
Global Arguments prot_pred {_ _}.
Global Instance: Params (@MiniProt) 3 := {}.
Global Instance: Params (@prot_pred) 2 := {}.

Global Instance miniprot_inhabited {A} {PROP:bi} : Inhabited (miniprot A PROP) :=
  populate (MiniProt ASend (λ _, emp%I)).

Section ofe.
  Context {V : Type} {PROP : ofe}.

  Local Instance miniprot_dist : Dist (miniprot V PROP) := λ n p1 p2,
    prot_action p1 = prot_action p2 ∧
    ∀ v, p1 v ≡{n}≡ p2 v.
  Local Instance miniprot_equiv : Equiv (miniprot V PROP) := λ p1 p2,
    prot_action p1 = prot_action p2 ∧
    ∀ v, p1 v ≡ p2 v.

  Definition miniprot_ofe_mixin : OfeMixin (miniprot V PROP).
  Proof.
    set (A := prodO actionO (V -d> PROP)).
    set (g p := (prot_action p, prot_pred p) : A).
    by apply (iso_ofe_mixin g).
  Qed.

  Canonical Structure miniprotO := Ofe (miniprot V PROP) miniprot_ofe_mixin.

  Global Instance miniprot_cofe : Cofe PROP → Cofe miniprotO.
  Proof.
    intros ?. set (A := prodO actionO (V -d> PROP)).
    set (g p := (prot_action p, prot_pred p) : A).
    set (f (p : A) := MiniProt p.1 p.2).
    by apply (iso_cofe f g).
  Qed.

  Global Instance MiniProt_ne a n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (MiniProt (V:=V) (PROP:=PROP) a).
  Proof. by split. Qed.
  Global Instance MiniProt_proper a :
    Proper (pointwise_relation _ (≡) ==> (≡)) (MiniProt (V:=V) (PROP:=PROP) a).
  Proof. by split. Qed.
  Global Instance prot_pred_ne n :
    Proper (dist n ==> (=) ==> dist n) (prot_pred (V:=V) (PROP:=PROP)).
  Proof. by intros ?? [??] ?? ->. Qed.
  Global Instance prot_pred_proper :
    Proper ((≡) ==> (=) ==> (≡)) (prot_pred (V:=V) (PROP:=PROP)).
  Proof. by intros ?? [??] ?? ->. Qed.

  Lemma miniprot_equivI `{!Sbi PROP'} (p1 p2 : miniprot V PROP) :
    p1 ≡ p2 ⊣⊢@{PROP'} ⌜ prot_action p1 = prot_action p2 ⌝ ∧ ∀ v, p1 v ≡ p2 v.
  Proof. by sbi_unfold. Qed.
End ofe.

Definition action_dual (a : action) : action :=
  match a with ASend => ARecv | ARecv => ASend end.

Definition dual {V PROP} (p : miniprot V PROP) : miniprot V PROP :=
  MiniProt (action_dual (prot_action p)) (prot_pred p).
Global Typeclasses Opaque dual.
Global Instance: Params (@dual) 2 := {}.

Section dual.
  Context {V : Type} {PROP : ofe}.

  Global Instance dual_ne : NonExpansive (@dual V PROP).
  Proof. intros ? [??] [??] [??]; by simplify_eq/=. Qed.

  Global Instance dual_proper : Proper ((≡) ==> (≡)) (@dual V PROP).
  Proof. apply: ne_proper. Qed.

  Lemma dual_dual (p : miniprot V PROP) : dual (dual p) = p.
  Proof. by destruct p as [[] ?]. Qed.

  Global Instance dual_involutive  : Involutive (≡) (@dual V PROP).
  Proof. intros S. by rewrite dual_dual. Qed.
End dual.

Global Arguments miniprotO : clear implicits.

Definition miniprot_map {V} {PROP1 PROP2 : ofe} (f : PROP1 -n> PROP2)
    (p : miniprot V PROP1) : miniprot V PROP2 :=
  MiniProt (prot_action p) (λ v, f (p v)).
Global Instance miniprot_map_ne {V} {PROP1 PROP2 : ofe} (f : PROP1 -n> PROP2) :
  NonExpansive (miniprot_map (V:=V) f).
Proof. intros n p1 p2 [??]; split; [done|]. intros v; simpl. by f_equiv. Qed.
Lemma miniprot_map_id {V} {PROP : ofe} (P : miniprot V PROP) :
  miniprot_map cid P ≡ P.
Proof. done. Qed.
Lemma miniprot_map_compose {V} {PROP1 PROP2 PROP3 : ofe}
    (f : PROP1 -n> PROP2) (g : PROP2 -n> PROP3) (p : miniprot V PROP1) :
  miniprot_map (g ◎ f) p ≡ miniprot_map g (miniprot_map f p).
Proof. done. Qed.
Lemma miniprot_map_ext {V} {PROP1 PROP2 : ofe} (f g : PROP1 -n> PROP2) :
  (∀ x, f x ≡ g x) →
  ∀ p : miniprot V PROP1, miniprot_map f p ≡ miniprot_map g p.
Proof. split; simpl; done. Qed.

Definition miniprotO_map {V} {PROP1 PROP2 : ofe} (f : PROP1 -n> PROP2) :
  miniprot V PROP1 -n> miniprot V PROP2 := OfeMor (miniprot_map f).
Lemma miniprotO_map_ne {V} {PROP1 PROP2 : ofe} (f g : PROP1 -n> PROP2) n :
  f ≡{n}≡ g → miniprotO_map (V:=V) f ≡{n}≡ miniprotO_map g.
Proof. split; simpl; done. Qed.

Program Definition miniprotOF (V : Type) (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := miniprot V (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := miniprotO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros V F A1 ? A2 ? B1 ? B2 ? n p p' Hp.
  apply miniprotO_map_ne, oFunctor_map_ne; split; by apply Hp.
Qed.
Next Obligation.
  intros V F A ? B ? p; simpl. rewrite -{2}(miniprot_map_id p).
  apply miniprot_map_ext=> y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros V F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' p; simpl.
  rewrite -miniprot_map_compose.
  apply miniprot_map_ext=> y; apply oFunctor_map_compose.
Qed.

Global Instance miniprotOF_contractive V F :
  oFunctorContractive F → oFunctorContractive (miniprotOF V F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply miniprotO_map_ne, oFunctor_map_contractive.
  destruct HPQ as [HPQ]. constructor. intros ??. split; by eapply HPQ.
Qed.
