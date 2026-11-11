/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Definitions

/-!
# Trace reconstruction from normalized Kraus branches

This module proves the normalization and trace post-processing identities for the signed Kraus
construction of [CaiEtAl2026]. The trace contribution of a normalized branch is its original
contribution multiplied by the squared normalization scale.

For a positive parameter `γ`, `trace_postprocessing` shows that the signed sum of normalized
contributions, multiplied by `γ`, reproduces the trace pairing with `D.action ρ`.

## Main statements

* `trace_normalizedKraus`: extracts the scalar normalization from a branch trace.
* `trace_postprocessing`: recovers the target trace from normalized signed branches.

## References

* [Cai et al., 2026][CaiEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction

namespace SignedKraus

variable {d r : ℕ} (D : SignedKraus d r)

/-- The trace pairing of a normalized Kraus branch equals the original branch trace pairing
multiplied by `sqrtScale γ * star (sqrtScale γ)`. -/
lemma trace_normalizedKraus (γ : ℝ) (_hγ : 0 < γ) (i : Fin r) (ρ O : Op d) :
    (D.normalizedKraus γ i * ρ * (D.normalizedKraus γ i)ᴴ * O).trace =
      (sqrtScale γ * star (sqrtScale γ)) * (D.K i * ρ * (D.K i)ᴴ * O).trace := by
  unfold normalizedKraus
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- For positive `γ`, multiplying the signed sum of normalized branch trace pairings by `γ`
recovers the trace pairing with the signed Kraus action. -/
theorem trace_postprocessing (γ : ℝ) (hγ : 0 < γ) (ρ O : Op d) :
    (D.action ρ * O).trace =
      (γ : ℂ) * ∑ i, D.α i *
        (D.normalizedKraus γ i * ρ * (D.normalizedKraus γ i)ᴴ * O).trace := by
  unfold action
  rw [Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    trace_normalizedKraus D γ hγ i ρ O]
  have hs : (γ : ℂ) * (sqrtScale γ * star (sqrtScale γ)) = 1 := by
    rw [sqrtScale_mul_star γ hγ]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hγ.ne')
  calc D.α i * (D.K i * ρ * (D.K i)ᴴ * O).trace
      = ((γ : ℂ) * (sqrtScale γ * star (sqrtScale γ))) *
          (D.α i * (D.K i * ρ * (D.K i)ᴴ * O).trace) := by rw [hs, one_mul]
    _ = (γ : ℂ) * (D.α i * ((sqrtScale γ * star (sqrtScale γ)) *
          (D.K i * ρ * (D.K i)ᴴ * O).trace)) := by ring

end SignedKraus

end Qatlib.Papers.HermitianMap26.Construction
