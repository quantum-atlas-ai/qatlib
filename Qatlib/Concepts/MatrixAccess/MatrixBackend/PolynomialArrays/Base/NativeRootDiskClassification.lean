/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCoordinateTruncation
import Mathlib.Tactic.SplitIfs

set_option backward.isDefEq.respectTransparency false

/-! Exact rational inside/outside/annulus branches of the source verifier.
Positive radius validation stays explicit. Outside classification does not
construct a precision grid; only the inside returned-point theorem uses eta. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Same ordered tests as verify_certificate; none is the rejected annulus. -/
def rootRationalDiskClassify (c : ℚ×ℚ) (r : ℚ) : Option Bool :=
  if r<1 ∧ c.1^2+c.2^2<(1-r)^2 then some true
  else if (1+r)^2<c.1^2+c.2^2 then some false else none

/-- The finite construction in `NativeRootDiskClassification` satisfies `rootRationalDiskClassify_true` under the displayed hypotheses. -/
theorem rootRationalDiskClassify_true (c : ℚ×ℚ) (r : ℚ)
    (h : rootRationalDiskClassify c r=some true) :
    r<1 ∧ c.1^2+c.2^2<(1-r)^2 := by
  unfold rootRationalDiskClassify at h
  split_ifs at h with hi ho
  · exact hi
  · cases h

/-- The finite construction in `NativeRootDiskClassification` satisfies `rootRationalDiskClassify_false` under the displayed hypotheses. -/
theorem rootRationalDiskClassify_false (c : ℚ×ℚ) (r : ℚ)
    (h : rootRationalDiskClassify c r=some false) :
    (1+r)^2<c.1^2+c.2^2 := by
  unfold rootRationalDiskClassify at h
  split_ifs at h with hi ho
  · cases h
  · exact ho

/-- The finite construction in `NativeRootDiskClassification` satisfies `rootRationalCoordinate_sq_norm` under the displayed hypotheses. -/
theorem rootRationalCoordinate_sq_norm (c : ℚ×ℚ) :
    ‖rootRationalCoordinate c‖^2=((c.1^2+c.2^2 : ℚ) : ℝ) := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [rootRationalCoordinate,pow_two]

/-- Every point of the accepted closed disk is strictly on the computed side. -/
theorem rootRationalDiskClassify_root_side (c : ℚ×ℚ) (r : ℚ) (hr : 0<r)
    (z : ℂ) (hz : ‖z-rootRationalCoordinate c‖≤(r : ℝ)) (b : Bool)
    (h : rootRationalDiskClassify c r=some b) :
    if b then ‖z‖<1 else 1<‖z‖ := by
  cases b with
  | false =>
    change 1<‖z‖
    have hs := rootRationalDiskClassify_false c r h
    apply root_disk_outside_of_squared_test (rootRationalCoordinate c) z r
      (by exact_mod_cast hr.le) _ hz
    rw [rootRationalCoordinate_sq_norm]
    exact_mod_cast hs
  | true =>
    change ‖z‖<1
    have hs := rootRationalDiskClassify_true c r h
    apply root_disk_inside_of_squared_test (rootRationalCoordinate c) z r
      (by exact_mod_cast hs.1) _ hz
    rw [rootRationalCoordinate_sq_norm]
    exact_mod_cast hs.2

/-- Returned inside coordinates use the SAME source eta/16 truncation and the
actually checked rational L1 forward budget, not an external error guarantee. -/
theorem rootClassified_inside_return (c : ℚ×ℚ) (r eta : ℚ)
    (hr : 0<r) (heta : 0<eta) (hside : rootRationalDiskClassify c r=some true)
    (z : ℂ) (hz : ‖z-rootRationalCoordinate c‖≤(r : ℝ))
    (hbudget : r+|(rootGridPoint c (eta/16)).1-c.1|+
      |(rootGridPoint c (eta/16)).2-c.2|≤eta) :
    ‖rootRationalCoordinate (rootGridPoint c (eta/16))‖<1 ∧
      ‖rootRationalCoordinate (rootGridPoint c (eta/16))-z‖≤(eta : ℝ) := by
  have hcenter : ‖rootRationalCoordinate c‖<1 := by
    apply rootRationalDiskClassify_root_side c r hr (rootRationalCoordinate c) _ true hside
    simpa using (show (0 : ℝ)≤r by exact_mod_cast hr.le)
  refine ⟨rootGridPoint_inside c eta heta hcenter,?_⟩
  apply root_disk_returned_coordinate_error (rootRationalCoordinate c) z
    (rootRationalCoordinate (rootGridPoint c (eta/16))) r eta hz
  have hb : (r : ℝ)+|((rootGridPoint c (eta/16)).1 : ℝ)-(c.1 : ℝ)|+
      |((rootGridPoint c (eta/16)).2 : ℝ)-(c.2 : ℝ)|≤(eta : ℝ) := by
    exact_mod_cast hbudget
  simpa only [rootRationalCoordinate,Complex.sub_re,Complex.sub_im] using hb

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
