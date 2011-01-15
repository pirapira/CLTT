Require Import List.

Definition Var := nat.

Section signature.

Parameter T : Set.
Parameter Const : Set.
Parameter Cdom: Const -> list T.
Parameter Ccod: Const -> T.

Definition Context := list T.

Definition add_var (t: T) (orig: Context) :=
  app orig (t :: nil).

(* choose either:
1. prepare raw term
2. define substitution on term derivation a the same as the derivations.
*)

Inductive RawTerm: Set :=
| Vex: Var -> RawTerm
| Cex: Const -> list RawTerm -> RawTerm.

Require Import Peano_dec.

Fixpoint substitution (v: Var) (new: RawTerm) (whole: RawTerm): RawTerm :=
  match whole with
    | Vex w =>
      if eq_nat_dec w v then new else whole
    | Cex c lst =>
      Cex c (map (substitution v new) lst)
  end.

Fixpoint substitution2
  (v0: Var) (new0: RawTerm)
  (v1: Var) (new1: RawTerm)
  (whole: RawTerm): RawTerm :=
  match whole with
    | Vex w =>
      if eq_nat_dec w v0 then new0 else
        if eq_nat_dec w v1 then new1 else whole
    | Cex c lst =>
      Cex c (map (substitution2 v0 new0 v1 new1) lst)
  end.

Inductive term_judge : Context -> RawTerm -> T -> Set :=
| identity: forall (sigma: T),
    (term_judge (cons sigma nil) (Vex 0) sigma)
| function_symbol: forall (c: Const)
  (gamma: Context) (subterms: list RawTerm),
  judgement_list gamma subterms (Cdom c) ->
  term_judge gamma (Cex c subterms) (Ccod c)
| weakening:
  forall (origC: Context) (t: T) (r: RawTerm)
    (origjudge: term_judge origC r t)
    (newtype: T),
    term_judge
    (app origC (cons newtype nil))
    r t
| contraction:
  forall (shorterC: Context) (sigma: T)
    (M: RawTerm) (tau: T)
    (origjudge: term_judge
      (add_var sigma (add_var sigma shorterC)) M tau),
    term_judge
    shorterC
    (substitution
      ((length shorterC) + 1)
      (Vex (length shorterC))
      M)
    tau
| exchange:
  forall (gamma delta: Context) (M: RawTerm) (tau: T)
    (sigmai sigmaj: T),
    term_judge
    (app gamma
      (app (sigmai :: sigmaj :: nil) delta))
    M tau
    ->
    term_judge
    (app gamma
      (app (sigmaj :: sigmai :: nil) delta))
    (substitution2
      (length gamma) (Vex (S (length gamma)))
      (S (length gamma)) (Vex (length gamma)) M)
    tau
with
  judgement_list: Context -> list RawTerm -> list T -> Set :=
| judgement_nil :
  forall (gamma: Context),
    judgement_list gamma nil nil
| judgement_cons :
  forall (gamma: Context) (thead: RawTerm) (trest: list RawTerm)
    (typeh: T) (typetl: list T),
    term_judge gamma thead typeh ->
    judgement_list gamma trest typetl ->
    judgement_list gamma (cons thead trest) (cons typeh typetl)
    .
