From dlfactris.session_logic Require Export imp.

Module TImp.
  Definition fork_chan : val := Imp.fork_chan.
  Definition recv : val := Imp.recv.
  Definition send : val := Imp.send.
  Definition close : val := Imp.close.
  Definition wait := Imp.wait.

  Notation prot := Imp.prot.
  Notation dual := Imp.dual.
  Notation subprot := Imp.subprot.

  #[projections(primitive=yes)]
  Record msg := Msg { msg_car : val → later prot -n> aProp }.

  Section msg_ofe.
    Instance msg_equiv : Equiv msg := λ m1 m2, ∀ w, msg_car m1 w ≡ msg_car m2 w.
    Instance msg_dist : Dist msg := λ n m1 m2, ∀ w, msg_car m1 w ≡{n}≡ msg_car m2 w.

    Lemma msg_ofe_mixin : OfeMixin msg.
    Proof. by apply (iso_ofe_mixin (msg_car : _ → val -d> _ -n> _)). Qed.
    Canonical Structure msgO := Ofe msg msg_ofe_mixin.
  End msg_ofe.

  Declare Scope prot_scope.
  Delimit Scope prot_scope with prot.
  Bind Scope prot_scope with prot.

  Declare Scope msg_scope.
  Delimit Scope msg_scope with msg.
  Bind Scope msg_scope with msg.

  Program Definition msg_base_def (v : val) (P : aProp) (p : prot) : msg :=
    Msg (λ v', λne p', ⌜⌜ v = v' ⌝⌝ ∗ Next p ≡≡ p' ∗ P)%I.
  Next Obligation. solve_proper. Qed.
  Definition msg_base_aux : seal msg_base_def. by eexists. Qed.
  Definition msg_base := msg_base_aux.(unseal).
  Definition msg_base_unseal : msg_base = msg_base_def := msg_base_aux.(seal_eq).
  Arguments msg_base _%val_scope _%I _%prot.
  Global Instance: Params (@msg_base) 1 := {}.

  Program Definition msg_exist_def {A} (m : A → msg) : msg :=
    Msg (λ v', λne p', ∃ x, msg_car (m x) v' p')%I.
  Next Obligation. solve_proper. Qed.
  Definition msg_exist_aux : seal (@msg_exist_def). by eexists. Qed.
  Definition msg_exist := msg_exist_aux.(unseal).
  Definition msg_exist_unseal :
    @msg_exist = @msg_exist_def := msg_exist_aux.(seal_eq).
  Arguments msg_exist {_} _%msg.
  Global Instance: Params (@msg_exist) 1 := {}.

  Program Definition msg_dual_def (m : msg) : msg :=
    Msg (λ v, λne p, msg_car m v (later_map dual p)).
  Next Obligation. solve_proper. Qed.
  Definition msg_dual_aux : seal (@msg_dual_def). by eexists. Qed.
  Definition msg_dual := msg_dual_aux.(unseal).
  Definition msg_dual_unseal :
    @msg_dual = @msg_dual_def := msg_dual_aux.(seal_eq).

  Definition msg_texist {TT : tele} (m : TT → msg) : msg :=
    tele_fold (@msg_exist) (λ x, x) (tele_bind m).
  Arguments msg_texist {!_} _%msg /.

  (** * Operators *)
  Definition end_prot_def := Imp.end_prot.
  Definition end_prot_aux : seal end_prot_def. by eexists. Qed.
  Definition end_prot := end_prot_aux.(unseal).
  Definition end_prot_unseal : end_prot = end_prot_def := end_prot_aux.(seal_eq).
  Global Instance: Params (@end_prot) 1 := {}.

  Definition msg_prot_def (a : action) (m : msg) : prot :=
    Imp.msg_prot a fst (λ vp, msg_car m vp.1 (Next vp.2)) snd.
  Definition msg_prot_aux : seal msg_prot_def. by eexists. Qed.
  Definition msg_prot := msg_prot_aux.(unseal).
  Definition msg_prot_unseal : msg_prot = msg_prot_def := msg_prot_aux.(seal_eq).
  Global Instance: Params (@msg_prot) 1 := {}.

  Definition own_chan_def := Imp.own_chan.
  Definition own_chan_aux : seal own_chan_def. by eexists. Qed.
  Definition own_chan := own_chan_aux.(unseal).
  Definition own_chan_unseal : own_chan = own_chan_def := own_chan_aux.(seal_eq).

  Module Import notations.
    Notation "p ⊑ q" := (subprot p q) : bi_scope.
    Notation "c ↣ p" := (own_chan c p) : bi_scope.

    Notation "'END@' a {{ P } }" := (end_prot a P)
      (at level 200, a at level 1, format "END@ a  {{  P  } }") : prot_scope.
    Notation "'END!' {{ P } }" := (end_prot ASend P)
      (format "END!  {{  P  } }") : prot_scope.
    Notation "'END?' {{ P } }" := (end_prot ARecv P)
      (format "END?  {{  P  } }") : prot_scope.

    Notation "'END@' a" := (end_prot a emp)
      (at level 200, a at level 1, format "END@ a") : prot_scope.
    Notation "'END!'" := (end_prot ASend emp) : prot_scope.
    Notation "'END?'" := (end_prot ARecv emp) : prot_scope.

    Notation "'MSG' v {{ P } } ; p" := (msg_base v P%I p)
      (at level 200, v at level 20, right associativity,
       format "MSG  v  {{  P  } } ;  p") : msg_scope.
    Notation "'MSG' v ; p" := (msg_base v emp p)
      (at level 200, v at level 20, right associativity,
       format "MSG  v ;  p") : msg_scope.
    Notation "∃ x .. y , m" :=
      (msg_exist (λ x, .. (msg_exist (λ y, m)) ..)%msg) : msg_scope.
    Notation "'∃..' x .. y , m" :=
      (msg_texist (λ x, .. (msg_texist (λ y, m)) .. )%msg)
      (at level 200, x binder, y binder, right associativity,
       format "∃..  x  ..  y ,  m") : msg_scope.

    Notation "< a > m" := (msg_prot a m)
      (at level 200, a at level 10, m at level 200,
       format "< a >  m") : prot_scope.
    Notation "< a @ x1 .. xn > m" := (msg_prot a (∃ x1, .. (∃ xn, m) ..))
      (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
       format "< a  @  x1  ..  xn >  m") : prot_scope.
    Notation "< a @.. x1 .. xn > m" := (msg_prot a (∃.. x1, .. (∃.. xn, m) ..))
      (at level 200, a at level 10, x1 closed binder, xn closed binder, m at level 200,
       format "< a  @..  x1  ..  xn >  m") : prot_scope.

    Notation "<!> m" :=
      (<ASend> m)%prot (at level 200, m at level 200) : prot_scope.
    Notation "<! x1 .. xn > m" := (<!> ∃ x1, .. (∃ xn, m) ..)%prot
      (at level 200, x1 closed binder, xn closed binder, m at level 200,
       format "<!  x1  ..  xn >  m") : prot_scope.
    Notation "<!.. x1 .. xn > m" := (<!> ∃.. x1, .. (∃.. xn, m) ..)%prot
      (at level 200, x1 closed binder, xn closed binder, m at level 200,
       format "<!..  x1  ..  xn >  m") : prot_scope.

    Notation "<?> m" :=
      (<ARecv> m)%prot (at level 200, m at level 200) : prot_scope.
    Notation "<? x1 .. xn > m" := (<?> ∃ x1, .. (∃ xn, m) ..)%prot
      (at level 200, x1 closed binder, xn closed binder, m at level 200,
       format "<?  x1  ..  xn >  m") : prot_scope.
    Notation "<?.. x1 .. xn > m" := (<?> ∃.. x1, .. (∃.. xn, m) ..)%prot
      (at level 200, x1 closed binder, xn closed binder, m at level 200,
       format "<?..  x1  ..  xn >  m") : prot_scope.

    Notation "p1 <+> p2" := (<! (b:bool)> MSG #b; if b then p1 else p2)%prot
      (at level 85) : prot_scope.
    Notation "p1 <?> p2" := (<? (b:bool)> MSG #b; if b then p1 else p2)%prot
      (at level 85) : prot_scope.

  End notations.

  Implicit Types v : val.
  Implicit Types p pl pr : prot.
  Implicit Types m : msg.

  Lemma msg_texist_exist {TT : tele} w lp (m : TT → msg) :
    msg_car (∃.. x, m x)%msg w lp ⊣⊢ (∃.. x, msg_car (m x) w lp).
  Proof.
    rewrite /msg_texist msg_exist_unseal.
    induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. apply IH.
  Qed.

  (** ** Non-expansiveness of operators *)
  Global Instance msg_car_proper :
    Proper ((≡) ==> (=) ==> (≡) ==> (≡)) msg_car.
  Proof. intros m1 m2 Hm v1 v2 <- p1 p2 Hp. rewrite Hp. apply Hm. Qed.
  Global Instance msg_car_ne n :
    Proper (dist n ==> (=) ==> dist n ==> dist n) msg_car.
  Proof. intros m1 m2 Hm v1 v2 <- p1 p2 Hp. rewrite Hp. apply Hm. Qed.

  Global Instance msg_contractive v n :
    Proper (dist n ==> dist_later n ==> dist n) (msg_base v).
  Proof. rewrite msg_base_unseal=> P1 P2 HP p1 p2 Hp w q /=. solve_contractive. Qed.
  Global Instance msg_ne v : NonExpansive2 (msg_base v).
  Proof. rewrite msg_base_unseal=> P1 P2 HP p1 p2 Hp w q /=. solve_proper. Qed.
  Global Instance msg_proper v : Proper ((≡) ==> (≡) ==> (≡)) (msg_base v).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance msg_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@msg_exist A).
  Proof. rewrite msg_exist_unseal=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance msg_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@msg_exist A).
  Proof. rewrite msg_exist_unseal=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.

  Global Instance msg_dual_ne : NonExpansive msg_dual.
  Proof. rewrite msg_dual_unseal. intros n m1 m2 Hm v p. apply Hm. Qed.
  Global Instance msg_dual_proper : Proper ((≡) ==> (≡)) msg_dual.
  Proof. apply (ne_proper _). Qed.

  Global Instance msg_prot_ne a : NonExpansive (msg_prot a).
  Proof.
    intros n m1 m2 Hm. rewrite msg_prot_unseal /msg_prot_def.
    f_equiv=> -[v p] /=. apply Hm.
  Qed.
  Global Instance msg_prot_proper a : Proper ((≡) ==> (≡)) (msg_prot a).
  Proof. apply (ne_proper _). Qed.

  Global Instance own_chan_contractive ch : Contractive (own_chan ch).
  Proof. rewrite own_chan_unseal. solve_contractive. Qed.
  Global Instance own_chan_ne ch : NonExpansive (own_chan ch).
  Proof. solve_proper. Qed.
  Global Instance own_chan_proper ch : Proper ((≡) ==> (≡)) (own_chan ch).
  Proof. solve_proper. Qed.

  (** ** Dual *)
  Lemma dual_end a P : dual (END@a {{ P }}) ≡ (END@(action_dual a) {{ P }})%prot. (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=b266599b *)
  Proof. rewrite end_prot_unseal. done. Qed.
  Lemma dual_msg a m : dual (<a> m) ≡ (<action_dual a> msg_dual m)%prot.
  Proof.
    rewrite msg_prot_unseal msg_dual_unseal /msg_prot_def. split; [done|].
    intros v; simpl. iSplit; iIntros "(%vp & %c & -> & ? & ?)";
      iExists (vp.1, dual vp.2), c; rewrite ?later_map_Next ?dual_dual;
      iFrame; repeat (iSplit; [done|]); by destruct a.
  Qed.
  Lemma msg_dual_base v P p :
    msg_dual (MSG v {{ P }}; p) ≡ (MSG v {{ P }}; dual p)%msg.
  Proof.
    rewrite msg_base_unseal msg_dual_unseal=> v' p' /=. do 2 f_equiv. iSplit.
    - iIntros "#Hp !>". rewrite -(later_map_Next dual p).
      iEval (rewrite -(later_map_id p')).
      rewrite (later_map_ext id (dual ∘ dual)) ?later_map_compose; last first.
      { intros q. by rewrite /= dual_dual. }
      by iApply f_equivI.
    - iIntros "Hp". iEval (rewrite -(dual_dual p)). by iRewrite -"Hp".
  Qed.
  Lemma msg_dual_exist {A} (m : A → msg) :
    msg_dual (∃ x, m x) ≡ (∃ x, msg_dual (m x))%msg.
  Proof. rewrite msg_exist_unseal msg_dual_unseal=> v' p' //. Qed.
  Lemma msg_dual_texist {TT : tele} (m : TT → msg) :
    msg_dual (∃.. x, m x) ≡ (∃.. x, msg_dual (m x))%msg.
  Proof.
    induction TT as [|T TT IH]; simpl; [done|].
    rewrite msg_dual_exist. f_equiv=> x. apply IH.
  Qed.

  (* Subprotocols *)
  Notation subprot_refl := Imp.subprot_refl.
  Notation subprot_trans := Imp.subprot_trans.
  Notation subprot_dual := Imp.subprot_dual.

  Lemma subprot_dual_l p1 p2 : dual p2 ⊑ p1 ⊢ dual p1 ⊑ p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive dual p2)). by iApply subprot_dual.
  Qed.
  Lemma subprot_dual_r p1 p2 : p2 ⊑ dual p1 ⊢ p1 ⊑ dual p2.
  Proof.
    iIntros "H". iEval (rewrite -(involutive dual p1)).
    by iApply subprot_dual.
  Qed.

  Lemma subprot_end_elim_l P1 P2 :
    (P1 -∗ END? ⊑ END? {{ P2 }}) -∗ (END? {{ P1 }} ⊑ END? {{ P2 }}).
  Proof.
    rewrite end_prot_unseal /subprot /=.
    iIntros "H %w [%v HP]". by iApply ("H" with "HP").
  Qed.
  Lemma subprot_end_elim_r P1 P2 :
    (P2 -∗ END!{{ P1 }} ⊑ END!) -∗ (END! {{ P1 }} ⊑ END! {{ P2 }}).
  Proof.
    rewrite end_prot_unseal /subprot /=.
    iIntros "H %w [%v HP]". by iApply ("H" with "HP").
  Qed.
  Lemma subprot_end_intro_l P : P -∗ END! {{ P }} ⊑ END!.
  Proof. rewrite end_prot_unseal /subprot /=. by iIntros "$ %w [-> _]". Qed.
  Lemma subprot_end_intro_r P : P -∗ END? ⊑ END? {{ P }}.
  Proof. rewrite end_prot_unseal /subprot /=. by iIntros "$ %w [-> _]". Qed.

  Lemma subprot_payload_elim_l m v P p :
    (P -∗ (<?> MSG v; p) ⊑ (<?> m)) ⊢
    (<?> MSG v {{ P }}; p) ⊑ (<?> m).
  Proof.
    rewrite msg_base_unseal msg_prot_unseal /subprot /=.
    iIntros "H %w (%vp2 & %c & -> & (-> & ? & HP) & ?)".
    iApply ("H" with "HP"). eauto with iFrame.
  Qed.
  Lemma subprot_payload_elim_r m v P p :
    (P -∗ (<!> m) ⊑ (<!> MSG v; p)) ⊢
    (<!> m) ⊑ (<!> MSG v {{ P }}; p).
  Proof.
    rewrite msg_base_unseal msg_prot_unseal /subprot /=.
    iIntros "H %w (%vp2 & %c & -> & (-> & ? & HP) & ?)".
    iApply ("H" with "HP"). eauto with iFrame.
  Qed.
  Lemma subprot_payload_intro_l v P p :
    P -∗ (<!> MSG v {{ P }}; p) ⊑ (<!> MSG v; p).
  Proof.
    rewrite msg_base_unseal msg_prot_unseal /subprot /=.
    iIntros "$ %w (%vp2 & %c & -> & (-> & ? & _) & ?)". eauto with iFrame.
  Qed.
  Lemma subprot_payload_intro_r v P p :
    P -∗ (<?> MSG v; p) ⊑ (<?> MSG v {{ P }}; p).
  Proof.
    rewrite msg_base_unseal msg_prot_unseal /subprot /=.
    iIntros "$ %w (%vp2 & %c & -> & (-> & ? & _) & ?)". eauto with iFrame.
  Qed.

  Lemma subprot_exist_elim_l {A} (m1 : A → msg) m2 :
    (∀ x, (<?> m1 x) ⊑ (<?> m2)) ⊢ (<? x> m1 x) ⊑ (<?> m2).
  Proof.
    rewrite msg_exist_unseal msg_prot_unseal /subprot /=.
    iIntros "H %w (%vp2 & %c & -> & [%x ?] & ?)".
    iApply "H". eauto 10 with iFrame.
  Qed.
  Lemma subprot_exist_elim_r {A} m1 (m2 : A → msg) :
    (∀ x, (<!> m1) ⊑ (<!> m2 x)) ⊢ (<!> m1) ⊑ (<! x> m2 x).
  Proof.
    rewrite msg_exist_unseal msg_prot_unseal /subprot /=.
    iIntros "H %w (%vp2 & %c & -> & [%x ?] & ?)".
    iApply "H". eauto 10 with iFrame.
  Qed.

  Lemma subprot_exist_elim_l_inhabited `{!Inhabited A} (m : A → msg) p :
    (∀ x, (<?> m x) ⊑ p) ⊢ (<? x> m x) ⊑ p.
  Proof.
    rewrite msg_exist_unseal msg_prot_unseal /subprot /=.
    destruct (prot_action p); [eauto|].
    - iIntros "H". by unshelve iSpecialize ("H" $! inhabitant).
    - iIntros "H %w (%vp2 & %c & -> & [%x ?] & ?)".
      iApply "H". eauto 10 with iFrame.
  Qed.
  Lemma subprot_exist_elim_r_inhabited `{!Inhabited A} (m : A → msg) p :
    (∀ x, p ⊑ (<!> m x)) ⊢ p ⊑ (<! x> m x).
  Proof.
    rewrite msg_exist_unseal msg_prot_unseal /subprot /=.
    destruct (prot_action p); [eauto|].
    - iIntros "H %w (%vp2 & %c & -> & [%x ?] & ?)".
      iApply "H". eauto 10 with iFrame.
    - iIntros "H". by unshelve iSpecialize ("H" $! inhabitant).
  Qed.

  Lemma subprot_exist_intro_l {A} (m : A → msg) a :
    ⊢ (<! x> m x) ⊑ (<!> m a).
  Proof.
    rewrite msg_exist_unseal msg_prot_unseal /subprot /=.
    iIntros "%w (%vp2 & %c & -> & ? & ?)"; eauto 10 with iFrame.
  Qed.
  Lemma subprot_exist_intro_r {A} (m : A → msg) a :
    ⊢ (<?> m a) ⊑ (<? x> m x).
  Proof.
    rewrite msg_exist_unseal msg_prot_unseal /subprot /=.
    iIntros "%w (%vp2 & %c & -> & ? & ?)"; eauto 10 with iFrame.
  Qed.

  Lemma subprot_texist_elim_l {TT : tele} (m1 : TT → msg) m2 :
    (∀ x, (<?> m1 x) ⊑ (<?> m2)) ⊢
    (<?.. x> m1 x) ⊑ (<?> m2).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply subprot_exist_elim_l; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma subprot_texist_elim_r {TT : tele} m1 (m2 : TT → msg) :
    (∀ x, (<!> m1) ⊑ (<!> m2 x)) -∗
    (<!> m1) ⊑ (<!.. x> m2 x).
  Proof.
    iIntros "H". iInduction TT as [|T TT] "IH"; simpl; [done|].
    iApply subprot_exist_elim_r; iIntros (x).
    iApply "IH". iIntros (xs). iApply "H".
  Qed.
  Lemma subprot_texist_intro_l {TT : tele} (m : TT → msg) x :
    ⊢ (<!.. x> m x) ⊑ (<!> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply Imp.subprot_refl. }
    iApply Imp.subprot_trans; [by iApply subprot_exist_intro_l|]. iApply IH.
  Qed.
  Lemma subprot_texist_intro_r {TT : tele} (m : TT → msg) x :
    ⊢ (<?> m x) ⊑ (<?.. x> m x).
  Proof.
    induction x as [|T TT x xs IH] using tele_arg_ind; simpl.
    { iApply Imp.subprot_refl. }
    iApply Imp.subprot_trans; [|by iApply subprot_exist_intro_r]. iApply IH.
  Qed.

  Lemma subprot_base a v P p1 p2 :
    ▷ (p1 ⊑ p2) ⊢
    (<a> MSG v {{ P }}; p1) ⊑ (<a> MSG v {{ P }}; p2).
  Proof.
    rewrite msg_base_unseal msg_prot_unseal {2}/subprot.
    iIntros "H"; destruct a; simpl.
    - iIntros "%w (%vp2 & %c & -> & (-> & Hp & $) & ?)".
      iExists (vp2.1, p1), c; simpl; do 2 (iSplit; [auto|]).
      iApply (Sub.own_chan_subprot with "[$]"); iNext.
      iRewrite -"Hp". by iApply Imp.subprot_dual.
    - iIntros "%w (%vp2 & %c & -> & (-> & Hp & $) & ?)".
      iExists (vp2.1, p2), c; simpl; do 2 (iSplit; [auto|]).
      iApply (Sub.own_chan_subprot with "[$]"); iNext.
      by iRewrite -"Hp".
  Qed.

  Lemma own_chan_subprot c p1 p2 : c ↣ p1 -∗ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof. rewrite own_chan_unseal. apply Imp.own_chan_subprot. Qed.

  (** WPs for session channels *)
  Lemma wp_fork_chan p (f : val) :
    ▷ (∀ c, c ↣ dual p -∗
             WP f c {{ _, emp }}) -∗
    WP fork_chan f {{ c, c ↣ p }}.
  Proof. rewrite own_chan_unseal. iApply Imp.wp_fork_chan. Qed.

  Lemma wp_recv {TT : tele} c
      (v : TT → val) (P : TT → aProp) (p : TT → prot) :
    c ↣ (<?.. x> MSG v x {{ P x }}; p x) -∗
    WP recv c {{ w, ∃.. x, ⌜⌜ w = v x ⌝⌝ ∗ c ↣ p x ∗ P x }}.
  Proof.
    iIntros "Hc". rewrite msg_base_unseal msg_prot_unseal own_chan_unseal.
    iApply (Imp.wp_recv with "Hc"); iIntros "!>" (vp) "[Hc' H]".
    rewrite msg_texist_exist /=; iDestruct "H" as (x <-) "[#Hp ?]".
    iExists x. iSplit; [done|]. iFrame.
    iApply (Imp.own_chan_subprot with "Hc'"); iNext. iRewrite "Hp".
    iApply Imp.subprot_refl.
  Qed.

  Lemma wp_send c v p :
    c ↣ (<!> MSG v; p) -∗
    WP send c v {{ v, ⌜⌜ v = #() ⌝⌝ ∗ c ↣ p }}.
  Proof.
    iIntros "Hc". rewrite msg_base_unseal msg_prot_unseal own_chan_unseal.
    iApply (Imp.wp_send _ _ _ _ (v,p) with "Hc"); simpl; eauto with iFrame.
  Qed.

  Lemma wp_wait c P :
    c ↣ END? {{ P }} -∗ WP wait c {{ v, ⌜⌜ v = #() ⌝⌝ ∗ P }}.
  Proof.
    iIntros "Hc". rewrite end_prot_unseal own_chan_unseal.
    by iApply (Imp.wp_wait with "Hc").
  Qed.

  Lemma wp_close c :
    c ↣ END! -∗ WP close c {{ v, ⌜⌜ v = #() ⌝⌝ }}.
  Proof.
    iIntros "Hc". rewrite end_prot_unseal own_chan_unseal.
    by iApply (Imp.wp_close with "Hc").
  Qed.
End TImp.
