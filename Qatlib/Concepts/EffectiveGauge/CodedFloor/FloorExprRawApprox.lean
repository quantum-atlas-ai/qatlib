/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprWordCode
public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprMachineBasis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Raw Approx

Coded Floor constructions for Effective Gauge.
Defines `floorExprHalfQuery`, `floorExprProductScale`, `floorExprProductQuery`.
Proves `floorPointCodeAt_axis_value`, `floorExprHalfQuery_tolerance`, `floorExprProductQuery_tolerance`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Expr Half Query in the Coded Floor construction. -/
def floorExprHalfQuery (q : FloorExprQueryCode) : FloorExprQueryCode :=
  floorExprQueryScale (floorRationalCodeInv (floorRationalCodeNat 2)) q

/-- Definition of floor Expr Product Scale in the Coded Floor construction. -/
def floorExprProductScale (a b : ℕ) : FloorRationalCode :=
  floorRationalCodeInv (floorRationalCodeMul (floorRationalCodeNat 2)
    (floorRationalCodeAdd (floorRationalCodeAdd (floorRationalCodeNat (floorExprCodeBound a))
      (floorRationalCodeNat (floorExprCodeBound b))) (floorRationalCodeNat 1)))

/-- Definition of floor Expr Product Query in the Coded Floor construction. -/
def floorExprProductQuery (a b : ℕ) (q : FloorExprQueryCode) : FloorExprQueryCode :=
  floorExprQueryScale (floorExprProductScale a b) q

/-- Data and hypotheses for Floor Expr Approx Ops in the Coded Floor construction. -/
structure FloorExprApproxOps where
  zero : FloorRationalCode
  literal : ℕ → FloorRationalCode
  coordinate : ℕ → FloorExprQueryCode → FloorRationalCode
  parameter : FloorExprQueryCode → FloorRationalCode
  flat : ℕ → FloorExprQueryCode → FloorRationalCode
  add : FloorRationalCode → FloorRationalCode → FloorRationalCode
  neg : FloorRationalCode → FloorRationalCode
  mul : FloorRationalCode → FloorRationalCode → FloorRationalCode
  sin : FloorRationalCode → FloorRationalCode → FloorRationalCode
  cos : FloorRationalCode → FloorRationalCode → FloorRationalCode
  half : FloorExprQueryCode → FloorExprQueryCode
  product : ℕ → ℕ → FloorExprQueryCode → FloorExprQueryCode

/-- Definition of floor Expr Raw Approx With in the Coded Floor construction. -/
def floorExprRawApproxWith (ops : FloorExprApproxOps) (n : ℕ) (q : FloorExprQueryCode) : FloorRationalCode :=
  if hn : n=0 then ops.zero else
    let tag := (n-1).unpair.1
    let p := (n-1).unpair.2
    if tag=0 then ops.literal p
    else if tag=1 then ops.coordinate p q
    else if tag=2 then ops.parameter q
    else if tag=3 then ops.flat p q
    else if tag=4 then ops.add
      (floorExprRawApproxWith ops p.unpair.1 (ops.half q))
      (floorExprRawApproxWith ops p.unpair.2 (ops.half q))
    else if tag=5 then ops.neg (floorExprRawApproxWith ops p q)
    else if tag=6 then ops.mul
      (floorExprRawApproxWith ops p.unpair.1 (ops.product p.unpair.1 p.unpair.2 q))
      (floorExprRawApproxWith ops p.unpair.2 (ops.product p.unpair.1 p.unpair.2 q))
    else if tag=7 then ops.sin (floorExprRawApproxWith ops p (ops.half q)) (ops.half q).2.2
    else if tag=8 then ops.cos (floorExprRawApproxWith ops p (ops.half q)) (ops.half q).2.2
    else ops.zero
termination_by n
decreasing_by
  all_goals
    have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
    first
    | exact (Nat.unpair_left_le _).trans_lt hp
    | exact (Nat.unpair_right_le _).trans_lt hp
    | exact hp

/-- Definition of floor Expr Approx Ops in the Coded Floor construction. -/
def floorExprApproxOps : FloorExprApproxOps where
  zero := floorRationalCodeNat 0
  literal := floorExprLiteralCode
  coordinate := fun p q => floorPointCodeAt p q.2.1
  parameter := floorExprParameterRawCode
  flat := floorExprFlatRawCode
  add := floorRationalCodeAdd
  neg := floorRationalCodeNeg
  mul := floorRationalCodeMul
  sin := fun value tolerance => floorExprSinRawCode (value,tolerance)
  cos := fun value tolerance => floorExprCosRawCode (value,tolerance)
  half := floorExprHalfQuery
  product := floorExprProductQuery

/-- Definition of floor Expr Raw Approx in the Coded Floor construction. -/
def floorExprRawApprox : ℕ → FloorExprQueryCode → FloorRationalCode :=
  floorExprRawApproxWith floorExprApproxOps

/-- Reading a coordinate from the point code and decoding it gives the decoded point at the
coordinate selected by the natural axis. -/
theorem floorPointCodeAt_axis_value (axis : ℕ) (X : FloorPointCode) :
    floorRationalCodeValue (floorPointCodeAt axis X)=floorPointCodeValue X (floorExprAxis axis) := by
  have h := floorPointCodeAt_value (floorExprAxis axis) X
  simpa [floorPointCodeAt,floorExprAxis] using h

/-- The half query represents exactly half of the original rational tolerance. -/
theorem floorExprHalfQuery_tolerance (q : FloorExprQueryCode) :
    floorRationalCodeValue (floorExprHalfQuery q).2.2=floorRationalCodeValue q.2.2/2 := by
  simp [floorExprHalfQuery,floorExprQueryScale,floorRationalCodeMul_value,
    floorRationalCodeInv_value,floorRationalCodeNat_value,div_eq_mul_inv]

/-- For factor bounds `A` and `B`, the product query divides the decoded tolerance by
`2 * (A + B + 1)`. -/
theorem floorExprProductQuery_tolerance (a b : ℕ) (q : FloorExprQueryCode) :
    floorRationalCodeValue (floorExprProductQuery a b q).2.2=
      floorRationalCodeValue q.2.2/(2*((floorExprCodeBound a : ℚ)+floorExprCodeBound b+1)) := by
  simp [floorExprProductQuery,floorExprQueryScale,floorExprProductScale,
    floorRationalCodeMul_value,floorRationalCodeInv_value,floorRationalCodeAdd_value,
    floorRationalCodeNat_value,div_eq_mul_inv]

/-- Halving the tolerance leaves the query's program code unchanged. -/
theorem floorExprHalfQuery_program (q : FloorExprQueryCode) : (floorExprHalfQuery q).1=q.1 := rfl

/-- Halving the tolerance leaves the query's point code unchanged. -/
theorem floorExprHalfQuery_point (q : FloorExprQueryCode) : (floorExprHalfQuery q).2.1=q.2.1 := rfl

/-- Rescaling the tolerance for a product of expressions leaves the program code unchanged. -/
theorem floorExprProductQuery_program (a b : ℕ) (q : FloorExprQueryCode) :
    (floorExprProductQuery a b q).1=q.1 := rfl

/-- Rescaling the tolerance for a product of expressions leaves the point code unchanged. -/
theorem floorExprProductQuery_point (a b : ℕ) (q : FloorExprQueryCode) :
    (floorExprProductQuery a b q).2.1=q.2.1 := rfl

/-- The decoded sine output is the imaginary coordinate of the rational cis value at the decoded
angle and tolerance. -/
theorem floorExprSinRawCode_value (p : FloorExpCodeParameters) :
    floorRationalCodeValue (floorExprSinRawCode p)=
      (rationalCis (floorRationalCodeValue p.1) (floorRationalCodeValue p.2)).value.2 :=
  congrArg (fun r : RationalCisResult => r.value.2) (floorRationalCisCode_value p)

/-- The decoded cosine output is the real coordinate of the rational cis value at the decoded
angle and tolerance. -/
theorem floorExprCosRawCode_value (p : FloorExpCodeParameters) :
    floorRationalCodeValue (floorExprCosRawCode p)=
      (rationalCis (floorRationalCodeValue p.1) (floorRationalCodeValue p.2)).value.1 :=
  congrArg (fun r : RationalCisResult => r.value.1) (floorRationalCisCode_value p)

/-- Decoding the raw approximation gives the rational jet approximation of the decoded expression
for the supplied program, decoded point, and decoded tolerance. -/
theorem floorExprRawApprox_value (n : ℕ) (q : FloorExprQueryCode) :
    floorRationalCodeValue (floorExprRawApprox n q)=
      floorJetApproximation q.1 (floorPointCodeValue q.2.1) (floorExprDecode n)
        (floorRationalCodeValue q.2.2) := by
  induction n using Nat.strong_induction_on generalizing q with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      rw [floorExprRawApprox,floorExprRawApproxWith,dite_eq_left rfl]
      have hz : floorExprDecode 0=FloorJetExpr.integer 0 := by rw [floorExprDecode]; simp
      rw [hz]
      simp [floorExprApproxOps,floorRationalCodeNat_value,floorJetApproximation]
    · have hp : (n-1).unpair.2<n := (Nat.unpair_right_le _).trans_lt (by omega)
      have ha := (Nat.unpair_left_le (n-1).unpair.2).trans_lt hp
      have hb := (Nat.unpair_right_le (n-1).unpair.2).trans_lt hp
      rw [floorExprRawApprox,floorExprRawApproxWith,dite_eq_right hn]
      simp only [floorExprApproxOps]
      conv_rhs => rw [floorExprDecode,dite_eq_right hn]
      dsimp only
      simp only [floorExprRawApprox,floorExprApproxOps] at ih
      generalize ht : (n-1).unpair.1=tag
      by_cases htag : tag<9
      · interval_cases tag <;>
          simp [floorJetApproximation,floorExprLiteralCode_value,floorPointCodeAt_axis_value,
            floorExprParameterRawCode_value,floorExprFlatRawCode_value,
            floorRationalCodeAdd_value,floorRationalCodeNeg_value,floorRationalCodeMul_value,
            floorExprHalfQuery_tolerance,floorExprProductQuery_tolerance,
            ih _ ha,ih _ hb,ih _ hp,floorExprCodeBound,
            floorExprSinRawCode_value,floorExprCosRawCode_value,
            floorExprHalfQuery_program,floorExprHalfQuery_point,
            floorExprProductQuery_program,floorExprProductQuery_point]
      · have h0 : tag≠0 := by omega
        have h1 : tag≠1 := by omega
        have h2 : tag≠2 := by omega
        have h3 : tag≠3 := by omega
        have h4 : tag≠4 := by omega
        have h5 : tag≠5 := by omega
        have h6 : tag≠6 := by omega
        have h7 : tag≠7 := by omega
        have h8 : tag≠8 := by omega
        simp [h0,h1,h2,h3,h4,h5,h6,h7,h8,floorRationalCodeNat_value,floorJetApproximation]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
