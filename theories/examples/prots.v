From iris.proofmode Require Import proofmode.
From dlfactris.session_logic Require Import proofmode.
Import TImp TImp.notations.


Lemma subprot1 :                                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=14a31259 *)
  ⊢ (<!(x:nat)> MSG #x ; <?> MSG #(x+1); END?) ⊑ (<!> MSG #1 ; <?> MSG #2; END?).
Proof.
  by iExists 1.
Qed.

Lemma subprot2 :                                                                 (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=30f6f4f6 *)
  ⊢ (<?> MSG #1 ; <!> MSG #2; END?) ⊑ (<?(x:nat)> MSG #x ; <!> MSG #(x+1); END?).
Proof.
  by iExists 1.
Qed.


Lemma subprot3 (p1 p2 : prot) v P :                                              (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=3f0ccb95 *)
  p1 ⊑ p2 ⊢ (<!> MSG #v {{ P }} ; p1) ⊑ (<!> MSG #v {{ P }} ; p2).
Proof.
  iIntros "H".
  iIntros "HP". iSplitL "HP"; first done.
  by iModIntro.
Qed.

Lemma subprot4 (p1 p2 : prot) v P :
  p1 ⊑ p2 ⊢ (<?> MSG #v {{ P }} ; p1) ⊑ (<?> MSG #v {{ P }} ; p2).
Proof.
  iIntros "H".
  iIntros "HP". iSplitL "HP"; first done.
  by iModIntro.
Qed.


Lemma subprot5 (p : prot) v P1 P2 :                                              (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=fa8801ea *)
  (P1 -∗ P2) ⊢ (<!> MSG #v {{ P2 }} ; p) ⊑ (<!> MSG #v {{ P1 }} ; p).
Proof.
  iIntros "H12".
  iIntros "HP". iSplitL "HP H12"; last done.
   by iApply "H12".
Qed.

Lemma subprot6 (p : prot) v P1 P2 :
  (P1 -∗ P2) ⊢ (<?> MSG #v {{ P1 }} ; p) ⊑ (<?> MSG #v {{ P2 }} ; p).
Proof.
  iIntros "H12".
  iIntros "HP". iSplitL "HP H12"; last done.
   by iApply "H12".
Qed.


Fixpoint prot_fin n : prot :=                                                    (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=f24fb92c *)
  match n with
  | 0 => END!
  | S n' => <!> MSG #n' ; prot_fin n'
  end.


Definition prot_inf_aux (rec : nat -d> prot) : (nat -d> prot) := λ n,
  (<!> MSG #n ; rec (S n))%prot.

Instance prot_inf_aux_contractive :
  Contractive prot_inf_aux.
Proof. solve_prot_contractive. Qed.

Definition prot_inf : nat → prot :=                                              (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=be55cac3 *)
    fixpoint prot_inf_aux.


Definition prot_inf_res_aux (rec : nat -d> prot) : (nat -d> prot) := λ n,
  (<!(c:val)> MSG c {{ c ↣ (rec (S n)) }} ; END!)%prot.

Instance prot_inf_res_aux_contractive :
  Contractive prot_inf_res_aux.
Proof. solve_prot_contractive. Qed.

Definition prot_inf_res : nat → prot :=                                          (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=1eafa6d8 *)
    fixpoint prot_inf_res_aux.


Definition prot_service_aux (rec : prot) : prot :=
  (<!(n:nat)> MSG #n ; <?(b:bool)> MSG #b ; if b then END! else rec)%prot.

Instance prot_service_aux_contractive :
  Contractive prot_service_aux.
Proof. solve_prot_contractive. Qed.

Definition prot_service : prot :=                                                (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=97520ca2 *)
    fixpoint prot_service_aux.