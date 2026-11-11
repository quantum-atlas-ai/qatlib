/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# LossBounds — source model for the quantum-assisted Bayesian PDE loss

Fixed source: arXiv:2608.27028v1 (D. An, Y. Li, P. Tang, Y. Xiong),
"A quantum-assisted framework for PDE-based Bayesian inverse problems".
Local PDF/txt: `prove/assets/2608.27028v1.{pdf,txt}`.

This file fixes the real vector-space vocabulary used by the deterministic error
estimates of Section 4:

* `unitVec x = ‖x‖⁻¹ • x` is the normalized amplitude vector of the terminal
  solution / observation (`|u⟩ = ‖u‖⁻¹ u`, Eq. (3.1)).
* `normalizedLoss uObs u` is the real form of the normalized quantum-state loss
  of Eq. (3.6): `2 − 2 Re⟨u_obs, u⟩/(‖u_obs‖‖u‖) = 2 − 2⟪û_obs, û⟫`.
* `physicalLoss uObs u = ‖u − u_obs‖²` is the physical loss (Eq. (3.5)/(3.6)
  core quantity, the squared L² misfit).

The general space `E` is a real inner-product space; `ℝ^{n_x}` with the Euclidean
inner product is the paper's concrete instance.
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.BayesianPDEAn26.LossBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalized vector `‖x‖⁻¹ • x` (`|x⟩` in the amplitude encoding of Eq. (3.1)).
For `x = 0` this is `0`; all uses below assume `x ≠ 0`. -/
def unitVec (x : E) : E := (‖x‖⁻¹ : ℝ) • x

/-- The normalized vector has unit norm whenever `x ≠ 0`. -/
theorem norm_unitVec {x : E} (hx : x ≠ 0) : ‖unitVec x‖ = 1 := by
  rw [unitVec, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- Real form of the normalized quantum-state loss of Eq. (3.6):
`L_norm = 2 − 2⟪û_obs, û⟫`. It is exactly
`2 − 2 Re⟨u_obs, u⟩/(‖u_obs‖‖u‖)` for real vectors. -/
def normalizedLoss (uObs u : E) : ℝ := 2 - 2 * ⟪unitVec uObs, unitVec u⟫_ℝ

/-- The physical loss: the squared L² misfit `‖u − u_obs‖²` (Section 3.1, Eq. (3.5)). -/
def physicalLoss (uObs u : E) : ℝ := ‖u - uObs‖ ^ 2

end Qatlib.Papers.BayesianPDEAn26.LossBounds
