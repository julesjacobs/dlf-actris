(** This file defines kinded telescopes, which are used for representing binders
in session types. *)
From stdpp Require Import base tactics telescopes.
From dlfactris.logrel Require Import model.
Set Default Proof Using "Type".

(** NB: This is overkill for the current setting, as there are no
dependencies between binders, hence we might have just used a list of [kind]
but might be needed for future extensions, such as for bounded polymorphism *)
(** Type Telescopes *)
Inductive ktele :=
  | KTeleO : ktele
  | KTeleS {k} : (lty k → ktele) → ktele.
Arguments ktele : clear implicits.

(** The telescope version of kind types *)
Fixpoint ktele_fun (kt : ktele) (A : Type) :=
  match kt with
  | KTeleO => A
  | KTeleS b => ∀ K, ktele_fun (b K) A
  end.

Notation "kt -k> A" :=
  (ktele_fun kt A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [ktele_fun]. *)
Definition ktele_fold {X Y kt}
    (step : ∀ {k}, (lty k → Y) → Y) (base : X → Y) : (kt -k> X) → Y :=
  (fix rec {kt} : (kt -k> X) → Y :=
     match kt as kt return (kt -k> X) → Y with
     | KTeleO => λ x : X, base x
     | KTeleS b => λ f, step (λ x, rec (f x))
     end) kt.
Arguments ktele_fold {_ _ !_} _ _ _ /.

(** A sigma-like type for an "element" of a telescope, i.e., the data it *)
Inductive ltys : ktele → Type :=
  | LTysO : ltys KTeleO
  | LTysS {k b} : ∀ K : lty k, ltys (b K) → ltys (KTeleS b).
Arguments ltys : clear implicits.

(** Inversion lemmas for [ltys] *)
Lemma ltys_inv {kt} (Ks : ltys kt) :
  match kt as kt return ltys kt → Prop with
  | KTeleO => λ Ks, Ks = LTysO
  | KTeleS f => λ Ks, ∃ K Ks', Ks = LTysS K Ks'
  end Ks.
Proof. induction Ks; eauto. Qed.
Lemma ltys_O_inv (Ks : ltys KTeleO) : Ks = LTysO.
Proof. exact (ltys_inv Ks). Qed.
Lemma ltys_S_inv {X} {f : lty X → ktele} (Ks : ltys (KTeleS f)) :
  ∃ K Ks', Ks = LTysS K Ks'.
Proof. exact (ltys_inv Ks). Qed.

Definition ktele_app {kt T} (f : kt -k> T) (Ks : ltys kt) : T :=
  (fix rec {kt} (Ks : ltys kt) : (kt -k> T) → T :=
    match Ks in ltys kt return (kt -k> T) → T with
    | LTysO => λ t : T, t
    | LTysS K Ks => λ f, rec Ks (f K)
    end) kt Ks f.
Arguments ktele_app {!_ _} _ !_ /.

Fixpoint ktele_bind {U kt} : (ltys kt → U) → kt -k> U :=
  match kt as kt return (ltys kt → U) → kt -k> U with
  | KTeleO => λ F, F LTysO
  | @KTeleS k b => λ (F : ltys (KTeleS b) → U) (K : lty k), (* b x -t> U *)
                  ktele_bind (λ Ks, F (LTysS K Ks))
  end.
Arguments ktele_bind {_ !_} _ /.

Lemma ktele_app_bind {U kt} (f : ltys kt → U) K :
  ktele_app (ktele_bind f) K = f K.
Proof.
  induction kt as [|k b IH]; simpl in *.
  - by rewrite (ltys_O_inv K).
  - destruct (ltys_S_inv K) as [K' [Ks' ->]]; simpl. by rewrite IH.
Qed.
