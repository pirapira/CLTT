Require Import List.

Definition Var := nat.

Section signature.

Variable T : Set.
Variable Const : Set.
Variable Cdom: Const -> list T.
Variable Ccod: Const -> T.

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

End signature.


Section binnat.
Inductive BinNat : Set :=
| N : BinNat
| B : BinNat.

Inductive consts : Set :=
| plus: consts
| iiff : consts.

Definition consts_dom (c: consts): list BinNat :=
  match c with
    | plus => N :: N :: nil
    | iiff => B :: N :: N :: nil
  end.

Definition consts_cod (c: consts): BinNat :=
  match c with
    | plus => N
    | iiff => N
  end.

Definition term_judge_binnat :=
  term_judge BinNat consts consts_dom consts_cod.

Lemma example_p123:
(*
   p. 123 has a type derivation.
   Below is the translation.
*)
  term_judge_binnat (B :: N :: nil)
  (Cex consts iiff
  ((Vex consts 0) :: (Vex consts 1) ::
    Cex consts plus ((Vex consts 1 :: Vex consts 1 :: nil)) :: nil))
  N .
apply function_symbol.
apply judgement_cons.
replace (B :: N :: nil)
  with (app (B ::nil) (N :: nil)).
apply weakening.
apply identity.
compute.
reflexivity.

apply judgement_cons.
replace (B :: N :: nil) with
  (app nil (app (B :: N :: nil) nil)).
Check substitution2.
replace (Vex consts 1) with
  (substitution2 consts
    0 (Vex consts (S O))
    (S 0) (Vex consts O)
    (Vex consts 0)).
apply exchange.
replace (nil ++ (N :: B :: nil) ++ nil) with
  (app (cons N nil) (cons B nil)).
apply weakening.
apply identity.
compute.
reflexivity.

compute.
reflexivity.

compute.
reflexivity.

apply judgement_cons.

replace (B :: N :: nil) with
  (app nil (app (cons B (cons N nil)) nil)).
replace
     (Cex consts plus (Vex consts 1 :: Vex consts 1 :: nil)) with
     (substitution2 consts
       O (Vex consts 1)
       (S O) (Vex consts 0)
       (Cex consts plus (Vex consts 0 :: Vex consts 0 :: nil))).
       
apply exchange.

replace (nil ++ (N :: B :: nil) ++ nil) with
  (app (N :: nil) (B :: nil)).
apply weakening.
apply function_symbol.

apply judgement_cons.
apply identity.
apply judgement_cons.
apply identity.

apply judgement_nil.
compute.
reflexivity.

compute.
reflexivity.

compute.
reflexivity.

apply judgement_nil.
Qed.

End binnat.