/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSourceSyntax
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorJetApproximation
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorReferenceMean
import Mathlib.Computability.Halting

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Program Source

Coded Floor constructions for Effective Gauge.
Defines `floorProgramJetSource`, `floorProgramReferenceMean`.
Proves `floorProgramJetSource_accurate`, `floorProgramJetSource_bounds`, `floorProgramReferenceMean_floor`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- A single finite program parameter produces every original rational multi-index query.
All evaluation is by explicit finite recursion; exact semantic amplitude is never inspected. -/
def floorProgramJetSource (c : Nat.Partrec.Code) : RationalJetSource :=
  fun query j => floorJetApproximation c query.1.1
    (floorJetWord (floorSpinExpr j) (sourceCanonicalWord query.1.2)) (2^query.2 : ℚ)⁻¹

noncomputable section

/-- Original `floorProgramJetSource_accurate` guarantee for the `FloorProgramSource` construction; the complete source hypotheses are retained. -/
theorem floorProgramJetSource_accurate (c : Nat.Partrec.Code) :
    OriginalAllJetAccurate (floorPeriodicSpin (floorProgramAmplitude c : ℝ)) (floorProgramJetSource c) := by
  intro X alpha b hX j
  have hcube : InFundamentalCube (rationalSpatialPoint X) := hX
  have h := floorJetApproximation_error
    (floorJetWord (floorSpinExpr j) (sourceCanonicalWord alpha)) c X hcube
    (2^b : ℚ)⁻¹ (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  rw [floorSourceJetExpr_correct _ alpha _ hcube j] at h
  simpa only [floorProgramJetSource,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using h

/-- Original `floorProgramJetSource_bounds` guarantee for the `FloorProgramSource` construction; the complete source hypotheses are retained. -/
theorem floorProgramJetSource_bounds (c : Nat.Partrec.Code) :
    OriginalPositiveJetBounds (floorPeriodicSpin (floorProgramAmplitude c : ℝ)) floorSourceJetBound :=
  floorSourceJetBound_correct _ (floorProgramAmplitude_abs_le_one c)

/-- Definition of floor Program Reference Mean in the Coded Floor construction. -/
def floorProgramReferenceMean (c : Nat.Partrec.Code) : ℝ :=
  floorSourceReferenceMean (floorProgramAmplitude c : ℝ)
    (originalFirstJetPair (floorProgramJetSource c) 0)
    ((floorProgramJetSource_accurate c).first.legacy)
    (floorSourceJetBound 1) (floorSourceJetBound 2)

open scoped Classical in
/-- Original `floorProgramReferenceMean_floor` guarantee for the `FloorProgramSource` construction; the complete source hypotheses are retained. -/
theorem floorProgramReferenceMean_floor (c : Nat.Partrec.Code) :
    ⌊floorProgramReferenceMean c⌋=
      if (Nat.Partrec.Code.eval c 0).Dom then (-1 : ℤ) else 0 := by
  classical
  have ha : (0 : ℝ) ≤ floorProgramAmplitude c := Rat.cast_nonneg.mpr (floorProgramAmplitude_spec c).1
  have ha1 : (floorProgramAmplitude c : ℝ) ≤ 1/16 := by
    have h : (floorProgramAmplitude c : ℝ) ≤ ((1/16 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (floorProgramAmplitude_spec c).2.1
    norm_num at h
    exact h
  unfold floorProgramReferenceMean
  rw [floorSourceReferenceMean_floor _ ha ha1]
  by_cases hh : (Nat.Partrec.Code.eval c 0).Dom
  · have hpos := (floorProgramAmplitude_pos_iff_dom c).mpr hh
    have hn : (floorProgramAmplitude c : ℝ) ≠ 0 := ne_of_gt (Rat.cast_pos.mpr hpos)
    simp only [if_pos hh,if_neg hn]
  · have hz : floorProgramAmplitude c=0 := by
      have hn := mt (floorProgramAmplitude_pos_iff_dom c).mp hh
      exact le_antisymm (le_of_not_gt hn) (floorProgramAmplitude_spec c).1
    simp only [hz,Rat.cast_zero,ite_true,if_neg hh]

/-- Original `floorProgramReferenceMean_floor_iff_halts` guarantee for the `FloorProgramSource` construction; the complete source hypotheses are retained. -/
theorem floorProgramReferenceMean_floor_iff_halts (c : Nat.Partrec.Code) :
    (⌊floorProgramReferenceMean c⌋=(-1 : ℤ)) ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  classical
  rw [floorProgramReferenceMean_floor]
  split_ifs <;> simp_all

/-- The actual reference-mean floor of this explicit source family detects the
undecidable halting predicate. A general input-code impossibility still requires
the interpreter/code-generation bridge for the complete source evaluator. -/
theorem floorProgramReferenceMean_not_computable_pred :
    ¬ComputablePred (fun c : Nat.Partrec.Code => ⌊floorProgramReferenceMean c⌋=(-1 : ℤ)) := by
  intro h
  exact ComputablePred.halting_problem 0
    (h.of_eq floorProgramReferenceMean_floor_iff_halts)

end
end Qatlib.Concepts.EffectiveGauge.CodedFloor
