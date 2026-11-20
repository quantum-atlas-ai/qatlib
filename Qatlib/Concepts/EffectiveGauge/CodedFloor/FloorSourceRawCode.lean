/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorFlatApproxCode
public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorProgramAmplitude
public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorJetApproximation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Source Raw Code

Coded Floor constructions for Effective Gauge.
Defines `FloorPointCode`, `FloorExprQueryCode`, `floorPointCodeValue`.
Proves `floorPointCodeAt_value`, `floorPointCodeBumpArgument_value`, `floorProgramAmplitudePayload_den_pos`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Abbreviation for Floor Point Code in the Coded Floor construction. -/
abbrev FloorPointCode := FloorRationalCode × FloorRationalCode × FloorRationalCode
/-- Abbreviation for Floor Expr Query Code in the Coded Floor construction. -/
abbrev FloorExprQueryCode := Nat.Partrec.Code × FloorPointCode × FloorRationalCode

/-- Definition of floor Point Code Value in the Coded Floor construction. -/
def floorPointCodeValue (X : FloorPointCode) (i : Fin 3) : ℚ :=
  if i=0 then floorRationalCodeValue X.1
  else if i=1 then floorRationalCodeValue X.2.1 else floorRationalCodeValue X.2.2

/-- Definition of floor Point Code At in the Coded Floor construction. -/
def floorPointCodeAt (axis : ℕ) (X : FloorPointCode) : FloorRationalCode :=
  [X.1,X.2.1,X.2.2].getD (axis%3) (floorRationalCodeNat 0)

/-- Looking up the code at the natural representative of coordinate `i` and decoding it gives the
point's rational `i`th coordinate. -/
theorem floorPointCodeAt_value (i : Fin 3) (X : FloorPointCode) :
    floorRationalCodeValue (floorPointCodeAt i.val X)=floorPointCodeValue X i := by
  fin_cases i <;> norm_num [floorPointCodeAt,floorPointCodeValue]

/-- Definition of floor Point Code Shift Square in the Coded Floor construction. -/
def floorPointCodeShiftSquare (q : FloorRationalCode) : FloorRationalCode :=
  let u := floorRationalCodeAdd q (floorRationalCodeNeg (floorRationalCodeNat 3))
  floorRationalCodeMul u u

/-- Definition of floor Point Code Bump Argument in the Coded Floor construction. -/
def floorPointCodeBumpArgument (X : FloorPointCode) : FloorRationalCode :=
  floorRationalCodeAdd (floorRationalCodeNat 1) (floorRationalCodeNeg
    (floorRationalCodeAdd (floorPointCodeShiftSquare X.1)
      (floorRationalCodeAdd (floorPointCodeShiftSquare X.2.1) (floorPointCodeShiftSquare X.2.2))))

/-- The coded bump argument decodes to the rational bump formula evaluated at the decoded spatial
point. -/
theorem floorPointCodeBumpArgument_value (X : FloorPointCode) :
    floorRationalCodeValue (floorPointCodeBumpArgument X)=floorRationalBumpArgument (floorPointCodeValue X) := by
  simp [floorPointCodeBumpArgument,floorPointCodeShiftSquare,floorRationalCodeAdd_value,
    floorRationalCodeNeg_value,floorRationalCodeNat_value,floorRationalCodeMul_value,
    floorRationalBumpArgument,Fin.sum_univ_three,floorPointCodeValue]
  ring

/-- Definition of floor Program Amplitude Raw Code in the Coded Floor construction. -/
def floorProgramAmplitudeRawCode (c : Nat.Partrec.Code) (b : ℕ) : FloorRationalCode :=
  let p := floorProgramAmplitudePayload c b
  ((p.1,0),p.2-1)

/-- The denominator in the amplitude approximation payload is strictly positive for every program
and fuel. -/
theorem floorProgramAmplitudePayload_den_pos (c : Nat.Partrec.Code) (b : ℕ) :
    0<(floorProgramAmplitudePayload c b).2 := by
  unfold floorProgramAmplitudePayload
  split <;> dsimp only <;> positivity

/-- The raw rational code of a program amplitude decodes to the amplitude approximant at the given
budget. -/
theorem floorProgramAmplitudeRawCode_value (c : Nat.Partrec.Code) (b : ℕ) :
    floorRationalCodeValue (floorProgramAmplitudeRawCode c b)=floorProgramAmplitudeApprox c b := by
  rw [← floorProgramAmplitudePayload_value]
  unfold floorRationalCodeValue floorProgramAmplitudeRawCode
  rw [Nat.sub_add_cancel (floorProgramAmplitudePayload_den_pos c b)]
  simp

/-- Definition of floor Expr Query Scale in the Coded Floor construction. -/
def floorExprQueryScale (scale : FloorRationalCode) (q : FloorExprQueryCode) : FloorExprQueryCode :=
  (q.1,q.2.1,floorRationalCodeMul q.2.2 scale)

/-- Definition of floor Expr Parameter Raw Code in the Coded Floor construction. -/
def floorExprParameterRawCode (q : FloorExprQueryCode) : FloorRationalCode :=
  floorProgramAmplitudeRawCode q.1 (floorRationalCodeArctanFuel q.2.2)

/-- Definition of floor Expr Flat Raw Code in the Coded Floor construction. -/
def floorExprFlatRawCode (order : ℕ) (q : FloorExprQueryCode) : FloorRationalCode :=
  floorFlatApproxCode order (floorPointCodeBumpArgument q.2.1) q.2.2

/-- The decoded parameter query is the program amplitude approximant with budget given by
`arctanFuel` of the decoded query tolerance. -/
theorem floorExprParameterRawCode_value (q : FloorExprQueryCode) :
    floorRationalCodeValue (floorExprParameterRawCode q)=
      floorProgramAmplitudeApprox q.1 (arctanFuel (floorRationalCodeValue q.2.2)) := by
  rw [floorExprParameterRawCode,floorProgramAmplitudeRawCode_value,floorRationalCodeArctanFuel_value]

/-- The decoded flat query answer is the order-specific rational flat approximation at the
rational bump argument of the decoded point and the decoded tolerance. -/
theorem floorExprFlatRawCode_value (order : ℕ) (q : FloorExprQueryCode) :
    floorRationalCodeValue (floorExprFlatRawCode order q)=
      floorFlatApproximation order (floorRationalBumpArgument (floorPointCodeValue q.2.1))
        (floorRationalCodeValue q.2.2) := by
  rw [floorExprFlatRawCode,floorFlatApproxCode_value,floorPointCodeBumpArgument_value]

/-- Selecting one coordinate code from a spatial point is primitive recursive in the natural axis
and point code. -/
theorem primrec_floorPointCodeAt : Primrec₂ floorPointCodeAt := by
  have hlist : Primrec (fun q : ℕ × FloorPointCode => [q.2.1,q.2.2.1,q.2.2.2]) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const [])))
  exact (Primrec.list_getD (floorRationalCodeNat 0)).comp hlist
    (Primrec.nat_mod.comp Primrec.fst (Primrec.const 3))

/-- Subtracting three from a coded rational coordinate and squaring the result is primitive
recursive. -/
theorem primrec_floorPointCodeShiftSquare : Primrec floorPointCodeShiftSquare := by
  have hu := primrec_floorRationalCodeAdd.comp Primrec.id (Primrec.const (floorRationalCodeNeg (floorRationalCodeNat 3)))
  exact primrec_floorRationalCodeMul.comp hu hu

/-- Evaluating the coded bump argument from the three coordinate codes is primitive recursive. -/
theorem primrec_floorPointCodeBumpArgument : Primrec floorPointCodeBumpArgument :=
  primrec_floorRationalCodeAdd.comp (Primrec.const (floorRationalCodeNat 1))
    (primrec_floorRationalCodeNeg.comp (primrec_floorRationalCodeAdd.comp
      (primrec_floorPointCodeShiftSquare.comp Primrec.fst)
      (primrec_floorRationalCodeAdd.comp
        (primrec_floorPointCodeShiftSquare.comp (Primrec.fst.comp Primrec.snd))
        (primrec_floorPointCodeShiftSquare.comp (Primrec.snd.comp Primrec.snd)))))

/-- Computing the raw rational code for the amplitude approximation is primitive recursive jointly
in the program and budget. -/
theorem primrec_floorProgramAmplitudeRawCode : Primrec₂ floorProgramAmplitudeRawCode :=
  ((Primrec.fst.comp primrec_floorProgramAmplitudePayload).pair (Primrec.const 0)).pair
    (Primrec.nat_sub.comp (Primrec.snd.comp primrec_floorProgramAmplitudePayload) (Primrec.const 1))

/-- Multiplying the query tolerance by a coded scale while preserving the program and point fields
is primitive recursive in the scale and query. -/
theorem primrec_floorExprQueryScale : Primrec₂ floorExprQueryScale :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (primrec_floorRationalCodeMul.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst))

/-- The coded parameter rule is primitive recursive in the query, including the tolerance-based
fuel selection. -/
theorem primrec_floorExprParameterRawCode : Primrec floorExprParameterRawCode :=
  primrec_floorProgramAmplitudeRawCode.comp Primrec.fst
    (primrec_floorRationalCodeArctanFuel.comp (Primrec.snd.comp Primrec.snd))

/-- Given primitive-recursive routines for a point-to-argument code and a flat evaluation, their
combination on the packed order and expression query is primitive recursive. -/
private theorem floorPrimrecFlatRawAux
    (f : FloorFlatCodeInput → FloorRationalCode) (hf : Primrec f)
    (g : FloorPointCode → FloorRationalCode) (hg : Primrec g) :
    Primrec (fun q : ℕ × FloorExprQueryCode => f (q.1,g q.2.2.1,q.2.2.2)) :=
  hf.comp (Primrec.fst.pair ((hg.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

/-- The coded flat rule is primitive recursive in the derivative order and the query. -/
theorem primrec_floorExprFlatRawCode : Primrec₂ floorExprFlatRawCode :=
  floorPrimrecFlatRawAux (fun q => floorFlatApproxCode q.1 q.2.1 q.2.2)
    primrec_floorFlatApproxCode floorPointCodeBumpArgument primrec_floorPointCodeBumpArgument

end Qatlib.Concepts.EffectiveGauge.CodedFloor
