/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDiskCertificate
import Mathlib.Data.Rat.Floor

set_option backward.isDefEq.respectTransparency false

/-! Actual rational coordinate truncation towards zero, as used by the root
certificate checker. This is an arithmetic specification, not a claim about
Python evaluation, encoded bit complexity or the whole phase producer. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for root Grid Truncate in the native root coordinate truncation model. -/
def rootGridTruncate (a h : ℚ) : ℚ :=
  let b := (⌊|a|/h⌋₊ : ℚ)*h
  if a<0 then -b else b

/-- The finite construction in `NativeRootCoordinateTruncation` satisfies `rootGridTruncate_spec` under the displayed hypotheses. -/
theorem rootGridTruncate_spec (a h : ℚ) (hh : 0<h) :
    |rootGridTruncate a h|≤|a| ∧ |rootGridTruncate a h-a|<h := by
  let b := (⌊|a|/h⌋₊ : ℚ)*h
  have hb0 : 0≤b := mul_nonneg (Nat.cast_nonneg _) hh.le
  have hfloor := Nat.floor_le (div_nonneg (abs_nonneg a) hh.le)
  have hnext := Nat.lt_floor_add_one (|a|/h)
  have hb : b≤|a| := by
    dsimp [b]
    exact (le_div_iff₀ hh).mp hfloor
  have hgap : |a|-b<h := by
    have he := (div_lt_iff₀ hh).mp hnext
    dsimp [b]
    nlinarith
  by_cases ha : a<0
  · have habs : |a| = -a := abs_of_neg ha
    have he : 0≤-b-a := by linarith
    simp only [rootGridTruncate,ha,ite_true]
    change |-b|≤|a| ∧ |-b-a|<h
    rw [abs_neg,abs_of_nonneg hb0,abs_of_nonneg he]
    exact ⟨hb,by linarith⟩
  · have haa : 0≤a := le_of_not_gt ha
    have habs : |a|=a := abs_of_nonneg haa
    have he : b-a≤0 := by linarith
    simp only [rootGridTruncate,ha,ite_false]
    change |b|≤|a| ∧ |b-a|<h
    rw [abs_of_nonneg hb0,abs_of_nonpos he]
    exact ⟨hb,by linarith⟩

/-- Construction for root Grid Point in the native root coordinate truncation model. -/
def rootGridPoint (c : ℚ×ℚ) (h : ℚ) : ℚ×ℚ :=
  (rootGridTruncate c.1 h,rootGridTruncate c.2 h)

/-- Construction for root Rational Coordinate in the native root coordinate truncation model. -/
def rootRationalCoordinate (c : ℚ×ℚ) : ℂ :=
  ⟨(c.1 : ℝ),(c.2 : ℝ)⟩

/-- The finite construction in `NativeRootCoordinateTruncation` satisfies `rootGridPoint_norm_le` under the displayed hypotheses. -/
theorem rootGridPoint_norm_le (c : ℚ×ℚ) (h : ℚ) (hh : 0<h) :
    ‖rootRationalCoordinate (rootGridPoint c h)‖≤‖rootRationalCoordinate c‖ := by
  apply truncated_root_coordinate_norm_le
  · have hs := (rootGridTruncate_spec c.1 h hh).1
    change |(rootGridTruncate c.1 h : ℝ)|≤|(c.1 : ℝ)|
    exact_mod_cast hs
  · have hs := (rootGridTruncate_spec c.2 h hh).1
    change |(rootGridTruncate c.2 h : ℝ)|≤|(c.2 : ℝ)|
    exact_mod_cast hs

/-- The estimate `rootGridPoint_component_error` retains the actual parameter, input-error and normalization budgets. -/
theorem rootGridPoint_component_error (c : ℚ×ℚ) (h : ℚ) (hh : 0<h) :
    |(rootRationalCoordinate (rootGridPoint c h)-rootRationalCoordinate c).re|+
      |(rootRationalCoordinate (rootGridPoint c h)-rootRationalCoordinate c).im|<
      2*(h : ℝ) := by
  have hr := (rootGridTruncate_spec c.1 h hh).2
  have hi := (rootGridTruncate_spec c.2 h hh).2
  have hs : |rootGridTruncate c.1 h-c.1|+|rootGridTruncate c.2 h-c.2|<2*h := by
    linarith
  change |(rootGridTruncate c.1 h : ℝ)-(c.1 : ℝ)|+
    |(rootGridTruncate c.2 h : ℝ)-(c.2 : ℝ)|<2*(h : ℝ)
  exact_mod_cast hs

/-- The actual eta/16 grid returns a point strictly inside whenever its
certified center is inside. No independent norm premise on q is supplied. -/
theorem rootGridPoint_inside (c : ℚ×ℚ) (eta : ℚ) (heta : 0<eta)
    (hcenter : ‖rootRationalCoordinate c‖<1) :
    ‖rootRationalCoordinate (rootGridPoint c (eta/16))‖<1 :=
  (rootGridPoint_norm_le c (eta/16) (by positivity)).trans_lt hcenter

/-- A sufficient arithmetic budget for the actual returned eta/16 point.
The general certificate consumer can also use its directly checked budget. -/
theorem rootGridPoint_error_of_disk (c : ℚ×ℚ) (z : ℂ) (r eta : ℚ)
    (heta : 0<eta) (hr : r≤7*eta/8)
    (hz : ‖z-rootRationalCoordinate c‖≤(r : ℝ)) :
    ‖rootRationalCoordinate (rootGridPoint c (eta/16))-z‖≤(eta : ℝ) := by
  apply root_disk_returned_coordinate_error (rootRationalCoordinate c) z
    (rootRationalCoordinate (rootGridPoint c (eta/16))) r eta hz
  have he := rootGridPoint_component_error c (eta/16) (by positivity)
  have hrr : (r : ℝ)≤7*(eta : ℝ)/8 := by exact_mod_cast hr
  have hpos : 0<(eta : ℝ) := by exact_mod_cast heta
  push_cast at he
  linarith

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
