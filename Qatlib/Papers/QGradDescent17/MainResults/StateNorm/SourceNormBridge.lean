/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.StateNorm` — the normalised-distance bridge

Kerenidis--Prakash, *Quantum gradient descent for linear systems and least
squares*, fixed arXiv:1704.04992v5.

The quantum iterative method produces unnormalised vectors `θ_τ, θ̃_τ` and reads
out the normalised states `|θ_τ⟩, |θ̃_τ⟩`.  The paper's Claim II.3 (p. 10,
eq. (6)) converts an unnormalised `ℓ²` bound into a bound on the distance of
the normalised states:

  `‖phi − phit‖ ≤ ε`, `angle(phi, phit) < π/2`  ⇒  `‖|phi⟩ − |phit⟩‖ ≤ √2 ε / ‖phi‖`.

The Lean statement below is the same implication, with the angle condition
expressed as `0 ≤ ⟪phi, phit⟫` (nonnegative cosine, equivalently angle in
`[0, π/2]`).  Nothing is weakened: the proof follows the paper's
`4 sin²(θ/2) ≤ 2 sin²θ ≤ 2ε²/‖phi‖²` chain, written in squared-norm form.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.StateNorm

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Arithmetic core of Claim II.3.  For positive `R = ‖phi‖`, `S = ‖phit‖` and
nonnegative cosine `c = ⟪phi, phit⟫`, the squared distance of the normalised
vectors is at most `2 ‖phi − phit‖² / ‖phi‖²`.

The proof is the paper's angle argument: writing `c = t R S` with `t ∈ [0,1]`,
the difference of the two squared sides is
`2 S (S − tR)² + 2 t (1 − t) R² S`, which is nonnegative. -/
theorem normalizedDistance_sq_le {R S c : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hc : 0 ≤ c) (hc_le : c ≤ R * S) :
    2 - 2 * (c / (R * S)) ≤ 2 * (R ^ 2 + S ^ 2 - 2 * c) / R ^ 2 := by
  set t : ℝ := c / (R * S) with ht_def
  have hRS : 0 < R * S := mul_pos hR hS
  have ht0 : 0 ≤ t := div_nonneg hc (le_of_lt hRS)
  have ht1 : t ≤ 1 := by
    rw [ht_def, div_le_one hRS]
    exact hc_le
  have hmul : 0 ≤ t * (1 - t) * R ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg R)
  have hsq : 0 ≤ (S - t * R) ^ 2 := sq_nonneg _
  have hct : c = t * (R * S) := by
    rw [ht_def]
    field_simp
  have hR2 : 0 < R ^ 2 := by positivity
  rw [le_div_iff₀ hR2]
  nlinarith [hmul, hsq, hct]

/-- **Claim II.3** (p. 10, eq. (6)).  If two nonzero vectors have nonnegative
inner product (angle at most `π/2`) and their unnormalised distance is `ε`,
then the distance of the normalised quantum states is at most
`√2 · ε / ‖phi‖`. -/
theorem claimII3_normalized_distance (phi phit : E) (hphi : phi ≠ 0) (hphit : phit ≠ 0)
    (hcos : 0 ≤ ⟪phi, phit⟫) (hangle : ⟪phi, phit⟫ ≤ ‖phi‖ * ‖phit‖) :
    ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ≤
      Real.sqrt 2 * ‖phi - phit‖ / ‖phi‖ := by
  set R : ℝ := ‖phi‖ with hRdef
  set S : ℝ := ‖phit‖ with hSdef
  set c : ℝ := ⟪phi, phit⟫ with hcdef
  have hR : 0 < R := by rw [hRdef]; exact norm_pos_iff.mpr hphi
  have hS : 0 < S := by rw [hSdef]; exact norm_pos_iff.mpr hphit
  have hc : 0 ≤ c := by rw [hcdef]; exact hcos
  have hc_le : c ≤ R * S := by rw [hcdef, hRdef, hSdef]; exact hangle
  -- squared norms of the normalised vectors
  have hnv : ‖NormedSpace.normalize phi‖ = 1 := NormedSpace.norm_normalize hphi
  have hnw : ‖NormedSpace.normalize phit‖ = 1 := NormedSpace.norm_normalize hphit
  have hin : ⟪NormedSpace.normalize phi, NormedSpace.normalize phit⟫ = c / (R * S) := by
    rw [hcdef, hRdef, hSdef, NormedSpace.normalize, NormedSpace.normalize,
      real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hLHS : ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2 =
      2 - 2 * (c / (R * S)) := by
    rw [norm_sub_sq_real, hnv, hnw, hin]
    ring
  have hnorm : ‖phi - phit‖ ^ 2 = R ^ 2 + S ^ 2 - 2 * c := by
    rw [norm_sub_sq_real, ← hRdef, ← hSdef, ← hcdef]
    ring
  have hRHS : (Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2 =
      2 * (R ^ 2 + S ^ 2 - 2 * c) / R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hnorm]
  have hsqle : ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2 ≤
      (Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2 := by
    rw [hLHS, hRHS]
    exact normalizedDistance_sq_le hR hS hc hc_le
  calc ‖NormedSpace.normalize phi - NormedSpace.normalize phit‖
      = Real.sqrt (‖NormedSpace.normalize phi - NormedSpace.normalize phit‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * ‖phi - phit‖ / R) ^ 2) := Real.sqrt_le_sqrt hsqle
    _ = Real.sqrt 2 * ‖phi - phit‖ / R := Real.sqrt_sq (by positivity)
    _ = Real.sqrt 2 * ‖phi - phit‖ / ‖phi‖ := by rw [hRdef]

end Qatlib.Papers.QGradDescent17.MainResults.StateNorm
