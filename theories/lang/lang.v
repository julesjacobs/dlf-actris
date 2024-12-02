(* Language with single-shot channels *)
From iris.algebra Require Export ofe.
From stdpp Require Export strings gmap binders.
From dlfactris.prelude Require Export prelude.

(* Syntax and values *)
(* ----------------- *)

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Declare Scope val_scope.
Delimit Scope val_scope with V.

Definition loc := positive.

Inductive base_lit :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).
Inductive un_op :=
  | NegOp | MinusUnOp.
Inductive bin_op :=
  (** We use "quot" and "rem" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30/-4 == 7. ("div" would return 8.) *)
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp. (* Relations *)

Inductive expr :=                                                                (* https://apndx.org/pub/icnp/dlfactris.pdf#nameddest=47a4f2ee *)
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | LetPair (e1 e2 : expr)
  (* Sums *)
  | Sum (t : string) (e : expr)
  | MatchSum (e : expr) (tes : list (string * expr))
  (* `ForkChan [f] creates a new channel,
      passes one endpoint to the function [f],
      and returns the other endpoint. *)
  | ForkChan (e : expr)
  (* ChanHVs are one-shot, which means that
     Send may only be used once per channel,
     and Recv deallocates the channel. *)
  | Send (e1 e2 : expr)
  | Recv (e : expr)
  | Alloc (e : expr)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | SumV (t : string) (v : val).

Canonical exprO := leibnizO expr.
Canonical valO := leibnizO val.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     let go' : EqDecision expr := @go in
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
        cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | LetPair e1 e2, LetPair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Sum t e, Sum t' e' => cast_if_and (decide (t = t')) (decide (e = e'))
     | MatchSum e tes, MatchSum e' tes' =>
        cast_if_and (decide (e = e')) (decide (tes = tes'))
     | ForkChan e, ForkChan e' => cast_if (decide (e = e'))
     | Send e1 e2, Send e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Recv e, Recv e' => cast_if (decide (e = e'))
     | Alloc e, Alloc e' => cast_if (decide (e = e'))
     | Free e, Free e' => cast_if (decide (e = e'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | SumV t v, SumV t' v' => cast_if_and (decide (t = t')) (decide (v = v'))
     | _, _ => right _
     end
   for go); try (try clear go'; clear go gov; abstract intuition congruence).
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

(* Operational semantics *)
(* --------------------- *)

Definition subst (x : string) (v : val) : expr → expr :=
  fix go e :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then go e else e
  | App e1 e2 => App (go e1) (go e2)
  | UnOp op e => UnOp op (go e)
  | BinOp op e1 e2 => BinOp op (go e1) (go e2)
  | If e0 e1 e2 => If (go e0) (go e1) (go e2)
  | Pair e1 e2 => Pair (go e1) (go e2)
  | LetPair e1 e2 => LetPair (go e1) (go e2)
  | Sum t e => Sum t (go e)
  | MatchSum e tes => MatchSum (go e) (prod_map id go <$> tes)
  | ForkChan e => ForkChan (go e)
  | Send e1 e2 => Send (go e1) (go e2)
  | Recv e => Recv (go e)
  | Alloc e => Alloc (go e)
  | Free e => Free (go e)
  | Load e => Load (go e)
  | Store e1 e2 => Store (go e1) (go e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | _, _ => None
    end.

(** In case of overlapping patterns (here, tags), we pick the first branch that
matches the pattern. *)
Fixpoint sum_branch (t : string) (tes : list (string * expr)) : option expr :=
  match tes with
  | [] => None
  | (t',e) :: tes => if decide (t = t') then Some e else sum_branch t tes
  end.

(* Small-step semantics *)
(* -------------------- *)

Inductive pure_step : expr → expr → Prop :=
  | RecS f x e :
      pure_step (Rec f x e) (Val $ RecV f x e)
  | AppS f x e1 v2 e' :
      e' = subst' x v2 (subst' f (RecV f x e1) e1) →
      pure_step (App (Val $ RecV f x e1) (Val v2)) e'
  | UnOpS op v v' :
      un_op_eval op v = Some v' →
      pure_step (UnOp op (Val v)) (Val v')
  | BinOpS op v1 v2 v' :
      bin_op_eval op v1 v2 = Some v' →
      pure_step (BinOp op (Val v1) (Val v2)) (Val v')
  | IfS b e1 e2 :
      pure_step (If (Val $ LitV $ LitBool b) e1 e2) (if b then e1 else e2)
  | PairS v1 v2 :
      pure_step (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2)
  | LetPairS v1 v2 e:
      pure_step (LetPair (Val $ PairV v1 v2) e) (App (App e (Val v1)) (Val v2))
  | SumS t v :
      pure_step (Sum t (Val v)) (Val $ SumV t v)
  | MatchSumS t v es e :
      sum_branch t es = Some e →
      pure_step (MatchSum (Val $ SumV t v) es) (App e (Val v)).


(* Evaluation contexts *)
(* ------------------- *)

Inductive ctx1 : (expr → expr) → Prop :=
  | Ctx_App_r e : ctx1 (λ x, App e x)
  | Ctx_App_l v : ctx1 (λ x, App x (Val v))
  | Ctx_UnOp op : ctx1 (λ x, UnOp op x)
  | Ctx_BinOp_r op e : ctx1 (λ x, BinOp op e x)
  | Ctx_BinOp_l op v : ctx1 (λ x, BinOp op x (Val v))
  | Ctx_If e1 e2 : ctx1 (λ x, If x e1 e2)
  | Ctx_Pair_r e : ctx1 (λ x, Pair e x)
  | Ctx_Pair_l v : ctx1 (λ x, Pair x (Val v))
  | Ctx_LetPair e : ctx1 (λ x, LetPair x e)
  | Ctx_Sum t : ctx1 (λ x, Sum t x)
  | Ctx_MatchSum es : ctx1 (λ x, MatchSum x es)
  | Ctx_ForkChan : ctx1 (λ x, ForkChan x)
  | Ctx_Send_r e : ctx1 (λ x, Send e x)
  | Ctx_Send_l v : ctx1 (λ x, Send x (Val v))
  | Ctx_Recv : ctx1 (λ x, Recv x)
  | Ctx_Alloc : ctx1 (λ x, Alloc x)
  | Ctx_Free : ctx1 (λ x, Free x)
  | Ctx_Load : ctx1 (λ x, Load x)
  | Ctx_Store_r e : ctx1 (λ x, Store e x)
  | Ctx_Store_l v : ctx1 (λ x, Store x (Val v)).

Inductive ctx : (expr → expr) → Prop :=
  | Ctx_id : ctx id
  | Ctx_compose k1 k2 : ctx1 k1 → ctx k2 → ctx (k1 ∘ k2).


(* Configurations *)
(* -------------- *)

Inductive heap_val := ChanHV (mv : option val) | RefHV (v : val).
Global Instance heap_val_eq_dec : EqDecision heap_val.
Proof. solve_decision. Defined.

Definition heap := gmap loc heap_val.
Definition cfg : Type := list expr * heap.

(* head_step (e1,h1) (e1,h2,es) means that:
     e1 head-steps to e2
     in initial heap h1 and final heap h2
     and spawns new threads es *)
Inductive head_step : expr → heap → expr → heap → list expr → Prop :=
  | Pure_step e1 e2 h :
      pure_step e1 e2 →
      head_step e1 h e2 h []
  | Fork_step h l f :
      h !! l = None →
      head_step (ForkChan (Val f)) h
                (Val (LitV (LitLoc l))) (<[l:=ChanHV None]> h)
                [App (Val f) (Val (LitV (LitLoc l)))]
  | Send_step h l v :
      h !! l = Some (ChanHV None) →
      head_step (Send (Val (LitV (LitLoc l))) (Val v)) h
                (Val (LitV LitUnit)) (<[l:=ChanHV (Some v)]> h) []
  | Recv_step h l v :
      h !! l = Some (ChanHV (Some v)) →
      head_step (Recv (Val (LitV (LitLoc l)))) h
                (Val v) (delete l h) []
  | AllocS h l v :
      h !! l = None →
      head_step (Alloc (Val v)) h
                (Val $ LitV $ LitLoc l) (<[l:=RefHV v]> h) []
  | FreeS h l v :
     h !! l = Some (RefHV v) →
     head_step (Free (Val $ LitV $ LitLoc l)) h
               (Val $ LitV LitUnit) (delete l h) []
  | LoadS h l v :
     h !! l = Some (RefHV v) →
     head_step (Load (Val $ LitV $ LitLoc l)) h (Val v) h []
  | StoreS h l v w :
     h !! l = Some (RefHV v) →
     head_step (Store (Val $ LitV $ LitLoc l) (Val w)) h
               (Val $ LitV LitUnit) (<[l:=RefHV w]> h) [].


Inductive prim_step : expr → heap → expr → heap → list expr → Prop :=
  | Prim_step k e1 e2 h1 h2 es :
      ctx k →
      head_step e1 h1 e2 h2 es →
      prim_step (k e1) h1 (k e2) h2 es.

Inductive step : cfg → cfg → Prop :=
  | Step e1 e2 i h1 h2 es es_new :
      es !! i = Some e1 →
      prim_step e1 h1 e2 h2 es_new →
      step (es, h1) (<[i := e2]> es ++ es_new, h2).

Definition steps := rtc step.

Inductive head_blocked : expr → loc → heap → Prop :=
  | Recv_blocked h l :
      h !! l = Some (ChanHV None) →
      head_blocked (Recv (Val (LitV (LitLoc l)))) l h.

Definition blocked (e : expr) (l : loc) (h : heap) :=
  ∃ k e', ctx k ∧ e = k e' ∧ head_blocked e' l h.

Definition reducible (e : expr) (h : heap) :=
  ∃ e' h' es, prim_step e h e' h' es.
Definition reducible_or_blocked (e : expr) (h : heap) :=
  reducible e h ∨ ∃ l, blocked e l h.
