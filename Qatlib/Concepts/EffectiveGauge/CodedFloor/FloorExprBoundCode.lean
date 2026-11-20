/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprCodec
public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCutoffBudgetCode

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Bound Code

Coded Floor constructions for Effective Gauge.
Defines `floorExprLiteralCode`, `floorExprCodeBound`, `floorExprBoundFrom`.
Proves `floorExprLiteralCode_value`, `floorExprLiteralCode_magnitude`, `floorExprHistory_getD`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Expr Literal Code in the Coded Floor construction. -/
def floorExprLiteralCode (p : ℕ) : FloorRationalCode := ((p.unpair.1,p.unpair.2),0)

/-- The rational literal code represents the decoded signed integer, coerced to the rationals. -/
theorem floorExprLiteralCode_value (p : ℕ) :
    floorRationalCodeValue (floorExprLiteralCode p)=(floorExprInteger p : ℚ) := by
  simp [floorExprLiteralCode,floorRationalCodeValue,floorExprInteger]

/-- The ceiling of the coded literal's absolute value equals the natural absolute value of the
decoded integer. -/
theorem floorExprLiteralCode_magnitude (p : ℕ) :
    floorRationalCodeCeil (floorRationalCodeAbs (floorExprLiteralCode p))=(floorExprInteger p).natAbs := by
  rw [floorRationalCodeCeil_value,floorRationalCodeAbs_value,floorExprLiteralCode_value]
  have hz : (((floorExprInteger p).natAbs : ℕ) : ℚ)=|(floorExprInteger p : ℚ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs]
  rw [← hz]
  exact Nat.ceil_natCast _

/-- Definition of floor Expr Code Bound in the Coded Floor construction. -/
def floorExprCodeBound (n : ℕ) : ℕ := floorJetBound (floorExprDecode n)

/-- Definition of floor Expr Bound From in the Coded Floor construction. -/
def floorExprBoundFrom (n : ℕ) (history : List ℕ) : ℕ :=
  if n=0 then 0 else
    let tag := (n-1).unpair.1
    let p := (n-1).unpair.2
    let a := history.getD p.unpair.1 0
    let b := history.getD p.unpair.2 0
    let u := history.getD p 0
    [floorRationalCodeCeil (floorRationalCodeAbs (floorExprLiteralCode p)),7,1,
      floorCutoffCodeBudget p,a+b,u,a*b,1,1].getD tag 0

/-- At an index `k < n`, defaulted lookup in the list of the first `n` values of `f` returns
`f k`. -/
theorem floorExprHistory_getD (f : ℕ → ℕ) (n k : ℕ) (hk : k<n) :
    ((List.range n).map f).getD k 0=f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [List.getElem_map,List.getElem_range]

/-- With the bounds of all smaller codes supplied in order, the local bound calculation at `n`
gives the bound of the decoded expression. -/
theorem floorExprBoundFrom_correct (n : ℕ) :
    floorExprBoundFrom n ((List.range n).map floorExprCodeBound)=floorExprCodeBound n := by
  by_cases hn : n=0
  · subst n
    rw [floorExprCodeBound,floorExprDecode]
    simp [floorExprBoundFrom,floorJetBound]
  · have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
    have ha := (Nat.unpair_left_le (n-1).unpair.2).trans_lt hp
    have hb := (Nat.unpair_right_le (n-1).unpair.2).trans_lt hp
    unfold floorExprBoundFrom
    rw [ite_eq_right hn]
    simp only [floorExprHistory_getD _ n _ hp,floorExprHistory_getD _ n _ ha,
      floorExprHistory_getD _ n _ hb]
    conv_rhs =>
      unfold floorExprCodeBound
      rw [floorExprDecode,dite_eq_right hn]
    dsimp only
    generalize ht : (n-1).unpair.1=tag
    by_cases htag : tag<9
    · interval_cases tag <;>
        simp [floorExprCodeBound,floorJetBound,floorExprLiteralCode_magnitude,floorCutoffCodeBudget_value]
    · have h0 : tag≠0 := by omega
      have h1 : tag≠1 := by omega
      have h2 : tag≠2 := by omega
      have h3 : tag≠3 := by omega
      have h4 : tag≠4 := by omega
      have h5 : tag≠5 := by omega
      have h6 : tag≠6 := by omega
      have h7 : tag≠7 := by omega
      have h8 : tag≠8 := by omega
      simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,
        ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,floorJetBound,Int.natAbs_zero]
      exact List.getD_eq_default _ _ (by simp; omega)

/-- Constructing a rational literal code from the packed signed integer is primitive recursive. -/
theorem primrec_floorExprLiteralCode : Primrec floorExprLiteralCode :=
  Primrec.unpair.pair (Primrec.const 0)

/-- Computing the local bound from the expression code and the supplied bound history is primitive
recursive in both inputs. -/
theorem primrec_floorExprBoundFrom : Primrec₂ floorExprBoundFrom := by
  have hparts : Primrec (fun q : ℕ × List ℕ => (q.1-1).unpair) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
  have ht : Primrec (fun q : ℕ × List ℕ => (q.1-1).unpair.1) := Primrec.fst.comp hparts
  have hp : Primrec (fun q : ℕ × List ℕ => (q.1-1).unpair.2) := Primrec.snd.comp hparts
  have ha := (Primrec.list_getD 0).comp Primrec.snd ((Primrec.fst.comp Primrec.unpair).comp hp)
  have hb := (Primrec.list_getD 0).comp Primrec.snd ((Primrec.snd.comp Primrec.unpair).comp hp)
  have hu := (Primrec.list_getD 0).comp Primrec.snd hp
  have hc := primrec_floorRationalCodeCeil.comp
    (primrec_floorRationalCodeAbs.comp (primrec_floorExprLiteralCode.comp hp))
  have hv : Primrec (fun q : ℕ × List ℕ =>
      [floorRationalCodeCeil (floorRationalCodeAbs (floorExprLiteralCode (q.1-1).unpair.2)),7,1,
        floorCutoffCodeBudget (q.1-1).unpair.2,
        q.2.getD (q.1-1).unpair.2.unpair.1 0+q.2.getD (q.1-1).unpair.2.unpair.2 0,
        q.2.getD (q.1-1).unpair.2 0,
        q.2.getD (q.1-1).unpair.2.unpair.1 0*q.2.getD (q.1-1).unpair.2.unpair.2 0,1,1]) :=
    Primrec.list_cons.comp hc (Primrec.list_cons.comp (Primrec.const 7)
      (Primrec.list_cons.comp (Primrec.const 1) (Primrec.list_cons.comp (primrec_floorCutoffCodeBudget.comp hp)
        (Primrec.list_cons.comp (Primrec.nat_add.comp ha hb) (Primrec.list_cons.comp hu
          (Primrec.list_cons.comp (Primrec.nat_mul.comp ha hb) (Primrec.const [1,1])))))))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
    ((Primrec.list_getD 0).comp hv ht)

/-- The bound of the expression decoded from a natural number is computable. -/
theorem computable_floorExprCodeBound : Computable floorExprCodeBound := by
  have hg : Computable₂ (fun (_ : Unit) (history : List ℕ) =>
      some (floorExprBoundFrom history.length history)) :=
    (Primrec.option_some.comp (primrec_floorExprBoundFrom.comp (Primrec.list_length.comp Primrec.snd)
      Primrec.snd)).to_comp
  have hf : Computable₂ (fun (_ : Unit) (n : ℕ) => floorExprCodeBound n) :=
    Computable.nat_strong_rec _ hg (by
      intro _ n
      simp only [List.length_map,List.length_range,floorExprBoundFrom_correct])
  exact hf.comp (Computable.const ()) Computable.id

/-- Encoding a jet expression and computing its code bound gives exactly that expression's
syntactic bound. -/
theorem floorExprCodeBound_encode (e : FloorJetExpr) : floorExprCodeBound (floorExprEncode e)=floorJetBound e := by
  rw [floorExprCodeBound,floorExprDecode_encode]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
