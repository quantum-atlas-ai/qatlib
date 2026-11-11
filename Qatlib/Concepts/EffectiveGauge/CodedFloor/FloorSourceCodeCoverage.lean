/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSourceCodeObstruction

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Source Code Coverage

Coded Floor constructions for Effective Gauge.
Defines `floorRationalCodeOfRat`, `floorPointCodeOfRational`, `floorSourceQueryCodeOfOriginal`.
Proves `floorRationalCodeOfRat_value`, `floorPointCodeOfRational_value`, `floorSourceQueryCodeOfOriginal_multiIndex`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The raw input covers every original rational, not a restricted subset of
physical addresses. This is a representation identity, not a runtime oracle. -/
def floorRationalCodeOfRat (q : ℚ) : FloorRationalCode :=
  ((q.num.toNat,(-q.num).toNat),q.den-1)

/-- Original `floorRationalCodeOfRat_value` guarantee for the `FloorSourceCodeCoverage` construction; the complete source hypotheses are retained. -/
theorem floorRationalCodeOfRat_value (q : ℚ) :
    floorRationalCodeValue (floorRationalCodeOfRat q)=q := by
  have hz : (q.num.toNat : ℤ)-((-q.num).toNat : ℤ)=q.num := by omega
  have hq : (q.num.toNat : ℚ)-((-q.num).toNat : ℚ)=(q.num : ℚ) := by exact_mod_cast hz
  unfold floorRationalCodeValue floorRationalCodeOfRat
  rw [Nat.sub_add_cancel q.den_pos,hq]
  simpa only [Int.cast_natCast] using
    (Rat.intCast_div_eq_divInt q.num (q.den : ℤ)).trans q.num_divInt_den

/-- Definition of floor Point Code Of Rational in the Coded Floor construction. -/
def floorPointCodeOfRational (X : Fin 3 → ℚ) : FloorPointCode :=
  (floorRationalCodeOfRat (X 0),floorRationalCodeOfRat (X 1),floorRationalCodeOfRat (X 2))

/-- Original `floorPointCodeOfRational_value` guarantee for the `FloorSourceCodeCoverage` construction; the complete source hypotheses are retained. -/
theorem floorPointCodeOfRational_value (X : Fin 3 → ℚ) :
    floorPointCodeValue (floorPointCodeOfRational X)=X := by
  funext i
  fin_cases i <;> simp [floorPointCodeValue,floorPointCodeOfRational,floorRationalCodeOfRat_value]

/-- Definition of floor Source Query Code Of Original in the Coded Floor construction. -/
def floorSourceQueryCodeOfOriginal (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ) (b : ℕ) (j : Fin 3) :
    FloorSourceQueryCode := (floorPointCodeOfRational X,(alpha 0,alpha 1,alpha 2),b,j.val)

/-- Original `floorSourceQueryCodeOfOriginal_multiIndex` guarantee for the `FloorSourceCodeCoverage` construction; the complete source hypotheses are retained. -/
theorem floorSourceQueryCodeOfOriginal_multiIndex (X : Fin 3 → ℚ) (alpha : Fin 3 → ℕ)
    (b : ℕ) (j : Fin 3) :
    floorSourceQueryMultiIndex (floorSourceQueryCodeOfOriginal X alpha b j)=alpha := by
  funext i
  fin_cases i <;> simp [floorSourceQueryMultiIndex,floorSourceQueryCodeOfOriginal]

/-- Original `floorEncodedJetSource_original_query` guarantee for the `FloorSourceCodeCoverage` construction; the complete source hypotheses are retained. -/
theorem floorEncodedJetSource_original_query (c : Nat.Partrec.Code) (X : Fin 3 → ℚ)
    (alpha : Fin 3 → ℕ) (b : ℕ) (j : Fin 3) :
    floorRationalCodeValue (floorEncodedJetSource c (floorSourceQueryCodeOfOriginal X alpha b j))=
      floorProgramJetSource c ((X,alpha),b) j := by
  rw [floorEncodedJetSource_value,floorSourceQueryCodeOfOriginal_multiIndex]
  simp only [floorSourceQueryCodeOfOriginal,floorPointCodeOfRational_value,floorExprAxis_val]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
