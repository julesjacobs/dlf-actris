(** This file defines semantic typing judgments and typing lemmas for the
operators of the language. The typing judgments for operators are expressed
using type classes, so they can easily be solved automatically. *)
From dlfactris.lang Require Import lang.
From dlfactris.logrel Require Export term_types subtyping.

(** Semantic operator typing *)
Class LTyUnOp (op : un_op) (A B : ltty) :=
  lty_un_op v :
    ltty_car (copy A) v -∗ ∃ w, ⌜⌜ un_op_eval op v = Some w ⌝⌝ ∗ ltty_car B w.

Class LTyBinOp (op : bin_op) (A1 A2 B : ltty) :=
  lty_bin_op v1 v2 :
    ltty_car (copy A1) v1 -∗ ltty_car (copy A2) v2 -∗
    ∃ w, ⌜⌜ bin_op_eval op v1 v2 = Some w ⌝⌝ ∗ ltty_car B w.

Section operators.
  Implicit Types A B : ltty.

  (** Rules for operator typing *)
  Global Instance lty_un_op_int op : LTyUnOp op lty_int lty_int.
  Proof. iIntros (?). iDestruct 1 as (i) "->". destruct op; eauto. Qed.
  Global Instance lty_un_op_bool : LTyUnOp NegOp lty_bool lty_bool.
  Proof. iIntros (?). iDestruct 1 as (i) "->". eauto. Qed.

  Global Instance lty_bin_op_eq A : LTyBinOp EqOp A A lty_bool.
  Proof.
    iIntros (v1 v2) "Hv1 Hv2". rewrite /bin_op_eval /=.
    iExists #(bool_decide (v1 = v2)). iSplit; [done|].
    iExists (bool_decide (v1 = v2)). done.
  Qed.

  Global Instance lty_bin_op_arith op :
    TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                 AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
    LTyBinOp op lty_int lty_int lty_int.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /ltty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_compare op :
    TCElemOf op [LeOp; LtOp] →
    LTyBinOp op lty_int lty_int lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /ltty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_bool op :
    TCElemOf op [AndOp; OrOp; XorOp] →
    LTyBinOp op lty_bool lty_bool lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /ltty_car /=; eauto.
  Qed.
End operators.
