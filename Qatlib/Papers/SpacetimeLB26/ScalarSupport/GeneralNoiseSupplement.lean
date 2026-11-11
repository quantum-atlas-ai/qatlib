/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Entanglement
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.GeneralNoise

/-! # Scalar support retained from the original SpacetimeLB26 contribution

This file proves conditional arithmetic or abstract combinatorial implications. Its
hypotheses must be read literally: final overlap, survival, contraction, code existence,
distance or threshold fields are not constructions of the corresponding physical objects.
The paper metadata records these interfaces as partial support, separately from the
new native Bell and adaptive erasure producers. Fixed source: arXiv2608.26272v1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.GeneralNoise

open Qatlib.Papers.SpacetimeLB26.ScalarSupport
open Qatlib.Papers.SpacetimeLB26.ScalarSupport.GeneralNoise

open scoped BigOperators
open Finset

/-! ## Finite contraction boundary -/

/-- A positive-duration memory with zero live width has zero contraction product:
the first zero-width layer contributes the factor `1 - κ^0 = 0`. -/
theorem contractionProduct_zero_width {S : ℕ} (hS : 0 < S) (κ : ℝ) :
    contractionProduct κ (fun _ : Fin S => (0 : ℝ)) = 0 := by
  unfold contractionProduct
  apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, hS⟩)
  norm_num

/-- A constant-width schedule has the expected finite power form.  This is the
finite scalar specialization of the contraction product, with no physical
channel construction hidden in the statement. -/
theorem contractionProduct_constant_width {S : ℕ} (κ m : ℝ) :
    contractionProduct κ (fun _ : Fin S => m) = (1 - κ ^ (2 * m)) ^ S := by
  unfold contractionProduct
  simp [Finset.prod_const]

/-! ## Theorem 6 — one-qubit lower bound -/

/-! ## Proposition 7 — information-dimension lower bound -/

/-! ## Theorem 8 — layerwise circuit-size lower bound -/

/-! ## Corollary 9 — no uniform constant relative bound -/

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.GeneralNoise
