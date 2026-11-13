/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CirculantPrec18.SVETransport.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModifiedSVE — resource specifications

**Statement only — not proved in Qatlib.**

The paper's quantum algorithm is not constructed in this module. Declarations
ending in `_statement` specify abstract output accuracy and resource targets;
they are propositions, with no existence proof or counted implementation. The singular-value recovery identity and
phase-error propagation lemmas below are proved independently.
The legacy record fields alone do not certify execution costs.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator BigOperators
open Matrix

namespace Qatlib.Papers.CirculantPrec18.SVETransport

/-- The Frobenius norm is nonnegative. -/
lemma frobeniusNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A := Real.sqrt_nonneg _

/-- SVE singular-value recovery. If `cos θ = 2σ²/σ_F² − 1` with
`0 ≤ σ ≤ σ_F` and `0 ≤ θ ≤ π`, then `σ = σ_F cos(θ/2)`, which is the formula
`σᵢ = ‖A‖_F cos(θᵢ/2)` used by the source after phase estimation. -/
lemma sve_sigma_eq_normF_mul_cos_half {σF σ θ : ℝ}
    (hF : 0 < σF) (hσ0 : 0 ≤ σ) (_hσF : σ ≤ σF)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcos : Real.cos θ = 2 * σ ^ 2 / σF ^ 2 - 1) :
    σ = σF * Real.cos (θ / 2) := by
  have hcos2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    simpa [show 2 * (θ / 2) = θ by ring] using Real.cos_two_mul (θ / 2)
  have hsq : Real.cos (θ / 2) ^ 2 = (σ / σF) ^ 2 := by
    have h1 : 2 * Real.cos (θ / 2) ^ 2 - 1 = 2 * σ ^ 2 / σF ^ 2 - 1 := by
      rw [← hcos2, hcos]
    have h2 : Real.cos (θ / 2) ^ 2 = σ ^ 2 / σF ^ 2 := by
      field_simp [hF.ne'] at h1 ⊢
      linarith
    rw [h2, div_pow]
  have hcnonneg : 0 ≤ Real.cos (θ / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith
  have hratio : 0 ≤ σ / σF := div_nonneg hσ0 hF.le
  have hc : Real.cos (θ / 2) = σ / σF := by
    calc Real.cos (θ / 2) = Real.sqrt ((Real.cos (θ / 2)) ^ 2) :=
          (Real.sqrt_sq hcnonneg).symm
      _ = Real.sqrt ((σ / σF) ^ 2) := by rw [hsq]
      _ = σ / σF := Real.sqrt_sq hratio
  calc σ = σF * (σ / σF) := by field_simp
    _ = σF * Real.cos (θ / 2) := by rw [hc]

/-- SVE error propagation. If the phase estimate `θ̂` satisfies
`|θ̂ − θ| ≤ δ`, then the singular-value estimate `σ_F cos(θ̂/2)` differs from
`σ` by at most `σ_F δ/2`. This is the `O(ε)` singular-value error obtained from
an `O(ε)` phase estimate. -/
lemma sve_sigma_error_le {σF σ θ θhat δ : ℝ}
    (hF : 0 < σF) (hσ0 : 0 ≤ σ) (hσF : σ ≤ σF)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hcos : Real.cos θ = 2 * σ ^ 2 / σF ^ 2 - 1)
    (hδ : |θhat - θ| ≤ δ) :
    |σF * Real.cos (θhat / 2) - σ| ≤ σF * (δ / 2) := by
  rw [sve_sigma_eq_normF_mul_cos_half hF hσ0 hσF hθ0 hθπ hcos]
  have habs : σF * Real.cos (θhat / 2) - σF * Real.cos (θ / 2)
      = σF * (Real.cos (θhat / 2) - Real.cos (θ / 2)) := by ring
  rw [habs, abs_mul, abs_of_pos hF]
  have hlip : |Real.cos (θhat / 2) - Real.cos (θ / 2)| ≤ |θhat / 2 - θ / 2| :=
    Real.abs_cos_sub_cos_le _ _
  have harg : |θhat / 2 - θ / 2| = |θhat - θ| / 2 := by
    rw [show θhat / 2 - θ / 2 = (θhat - θ) / 2 by ring, abs_div, abs_two]
  calc σF * |Real.cos (θhat / 2) - Real.cos (θ / 2)|
      ≤ σF * (|θhat - θ| / 2) := by
        gcongr
        rw [← harg]
        exact hlip
    _ ≤ σF * (δ / 2) := by gcongr

/-- **Statement only — not proved in Qatlib.**
Resource and accuracy specification for `source_modified_sve`.
No circuit, oracle implementation, or execution-cost theorem is supplied here.
The existential record is a specification, not evidence of an algorithm. -/
def source_modified_sve_statement
    (n : ℕ) (A U V : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ)
    (_hU : Uᵀ * U = 1) (_hV : Vᵀ * V = 1)
    (_hσnn : ∀ i, 0 ≤ σ i)
    (_hSVD : A = U * Matrix.diagonal σ * Vᵀ)
    (ε : ℝ) (hε : 0 < ε) : Prop :=
    ∃ (c : ℕ) (_hc : 0 < c) (pro : ModifiedSVE n),
      0 ≤ pro.cost ∧
      pro.cost ≤ (c : ℝ) * ((Real.log ((n : ℝ) + 1)) + 1) ^ c / ε ∧
        RealizesModifiedSVE n A σ ε pro

end Qatlib.Papers.CirculantPrec18.SVETransport
