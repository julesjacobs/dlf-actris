(** This file defines the semantic interpretations of session types as Actris
protocols. It includes session types for sending and receiving with session
polymorphism, as well as n-ary choice. Recursive protocols are defined in
the [model.v] file. *)
From iris.algebra Require Export gmap.
From dlfactris.logrel Require Export model telescopes.

Definition lmsg := msg.
Declare Scope lmsg_scope.
Delimit Scope lmsg_scope with lmsg.
Bind Scope lmsg_scope with lmsg.

Definition lty_msg_base (A : ltty) (S : lsty) : lmsg :=                          (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=ecea186d *)
  (∃ v, MSG v {{ ltty_car A v }} ; (lsty_car S))%msg.

Definition lty_msg_exist {k} (M : lty k → lmsg) : lmsg :=
  (∃ X, M X)%msg.

Definition lty_msg_texist {kt : ktele} (M : ltys kt → lmsg) : lmsg :=
  ktele_fold (@lty_msg_exist) (λ x, x) (ktele_bind M).
Arguments lty_msg_texist {!_} _%_lmsg /.

Definition lty_end (a : action) := Lsty (END@a).

Definition lty_message (a : action) (M : lmsg) : lsty :=
  Lsty (<a> M).

Definition lty_choice (a : action) (ASs : gmap string (ltty * lsty)) : lsty :=
  Lsty (<a@(t : string) (v : val)>
    MSG SumV t v {{ from_option (ltty_car ∘ fst) (const False) (ASs !! t) v }};
    lsty_car (ASs !!! t).2).

Definition lty_dual (S : lsty) : lsty :=
  Lsty (dual (lsty_car S)).

Global Instance: Params (@lty_message) 1 := {}.
Global Instance: Params (@lty_choice) 1 := {}.

Notation "'TY' A ; S" := (lty_msg_base A S)
  (at level 200, right associativity,
   format "'TY'  A ;  S") : lmsg_scope.
Notation "∃ X .. Y , M" :=
  (lty_msg_exist (λ X, .. (lty_msg_exist (λ Y, M)) ..)%lmsg) : lmsg_scope.
Notation "'∃..' X .. Y , M" :=
  (lty_msg_texist (λ X, .. (lty_msg_texist (λ Y, M)) .. )%lmsg)
  (at level 200, X binder, Y binder, right associativity,
   format "∃..  X  ..  Y ,  M") : lmsg_scope.

Notation "'END!!'" := (lty_end ASend) : lty_scope.
Notation "'END??'" := (lty_end ARecv) : lty_scope.
Notation "<!!> M" :=
  (lty_message ASend M) (at level 200, M at level 200) : lty_scope.
Notation "<!! X .. Y > M" :=
  (<!!> ∃ X, .. (∃ Y, M) ..)%lty
    (at level 200, X closed binder, Y closed binder, M at level 200,
     format "<!!  X  ..  Y >  M") : lty_scope.
Notation "<!!.. X .. Y > M" := (<!!> ∃.. X, .. (∃.. Y, M) ..)%lty
  (at level 200, X closed binder, Y closed binder, M at level 200,
   format "<!!..  X  ..  Y >  M") : lty_scope.

Notation "<??> M" :=
  (lty_message ARecv M) (at level 200, M at level 200) : lty_scope.
Notation "<?? X .. Y > M" :=
  (<??> ∃ X, .. (∃ Y, M) ..)%lty
    (at level 200, X closed binder, Y closed binder, M at level 200,
     format "<??  X  ..  Y >  M") : lty_scope.
Notation "<??.. X .. Y > M" := (<??> ∃.. X, .. (∃.. Y, M) ..)%lty
  (at level 200, X closed binder, Y closed binder, M at level 200,
   format "<??..  X  ..  Y >  M") : lty_scope.
Notation lty_select := (lty_choice ASend).
Notation lty_branch := (lty_choice ARecv).

Class LtyMsgTele {kt : ktele} (M : lmsg)
    (A : kt -k> ltty) (S : kt -k> lsty) :=
  lty_msg_tele : M ≡ (∃.. x, TY ktele_app A x; ktele_app S x)%lmsg.
Global Hint Mode LtyMsgTele - ! - - : typeclass_instances.

Section session_types.
  Global Instance lty_msg_exist_ne k n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@lty_msg_exist k).
  Proof. solve_proper. Qed.
  Global Instance lty_msg_exist_proper k :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@lty_msg_exist k).
  Proof. solve_proper. Qed.
  Global Instance lty_msg_base_ne : NonExpansive2 (@lty_msg_base).
  Proof. rewrite /lty_msg_base. solve_proper. Qed.
  Global Instance lty_msg_base_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@lty_msg_base).
  Proof. rewrite /lty_msg_base. apply ne_proper_2, _. Qed.
  Global Instance lty_msg_base_contractive n :
    Proper (dist n ==> dist_later n ==> dist n) (@lty_msg_base).
  Proof. solve_contractive. Qed.

  Global Instance lty_message_ne a : NonExpansive (@lty_message a).
  Proof. solve_proper. Qed.
  Global Instance lty_message_proper a : Proper ((≡) ==> (≡)) (@lty_message a).
  Proof. apply ne_proper, _. Qed.

  Global Instance lty_choice_ne a : NonExpansive (@lty_choice a).
  Proof. solve_proper. Qed.
  Global Instance lty_choice_proper a : Proper ((≡) ==> (≡)) (@lty_choice a).
  Proof. apply ne_proper, _. Qed.

  Global Instance lty_choice_contractive a n :
    Proper (map_relation (λ _, prod_relation (dist n) (dist_later n))
                         (λ _ _, False) (λ _ _, False) ==> dist n)
           (@lty_choice a).
  Proof.
    intros Ss Ts Heq. rewrite /lty_choice.
    do 2 f_equiv. f_equiv => t. f_equiv=> v. rewrite !lookup_total_alt.
    specialize (Heq t). destruct (Ss !! t), (Ts !! t); simplify_eq/=; [|done..].
    destruct Heq as [Ht Hs]. f_contractive; by f_equiv.
  Qed.

  Global Instance lty_dual_ne : NonExpansive (@lty_dual).
  Proof. solve_proper. Qed.
  Global Instance lty_dual_proper : Proper ((≡) ==> (≡)) (@lty_dual).
  Proof. apply ne_proper, _. Qed.
  Global Instance lty_dual_involutive : Involutive (≡) (@lty_dual).
  Proof. intros S. rewrite /lty_dual. apply dual_involutive. Qed.

  Global Instance lty_msg_tele_base (A : ltty) (S : lsty) :
    LtyMsgTele (kt:=KTeleO) (TY A ; S) A S.
  Proof. rewrite /LtyMsgTele. done. Qed.
  Global Instance lty_msg_tele_exist {k} {kt : lty k → ktele}
    (M : lty k → lmsg) A S :
    (∀ x, LtyMsgTele (kt:=kt x) (M x) (A x) (S x)) →
    LtyMsgTele (kt:=KTeleS kt) (∃ x, M x) A S.
  Proof. intros HM. rewrite /LtyMsgTele /=. f_equiv=> x. apply HM. Qed.
End session_types.
