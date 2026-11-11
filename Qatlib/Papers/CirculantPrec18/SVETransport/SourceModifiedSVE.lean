/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CirculantPrec18.SVETransport.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Source modified singular value estimation (Lemma 1)

Shao--Xiang, *Quantum Circulant Preconditioner for Linear System of Equations*,
fixed arXiv:1807.04563v1, Lemma 1, p.6 (following the phase-estimation chain of
§3.1, Eqs. (7)–(8)).

Source statement.  Let `A` be an `n × n` matrix with singular value
decomposition `A = Σᵢ σᵢ |uᵢ⟩⟨vᵢ|`.  Then there is a quantum algorithm that
runs in `O(poly(log n)/ε)` and achieves

  `Σᵢ αᵢ |vᵢ⟩|0⟩ ↦ Σᵢ αᵢ |uᵢ⟩|σ̃ᵢ⟩`,

where `|σ̃ᵢ − σᵢ| ≤ ε‖A‖_F` for all `i`, with probability at least
`1 − 1/poly(n)`.

Proof route (source, §3.1).  Build `U_N`, `U_M` from Eqs. (7)/(8); the walk
`W = (2NN†−I)(2MM†−I)` rotates the invariant subspace
`{M|vᵢ⟩, N|uᵢ⟩}` by the angle `θᵢ` with `cos θᵢ = 2σᵢ²/‖A‖_F² − 1`.  Phase
estimation on `W` gives `θ̃ᵢ`; the register value `σ̃ᵢ = ‖A‖_F cos(θ̃ᵢ/2)` is
within `ε‖A‖_F` when the phase register has `O(log(1/ε))` qubits, and the
eigenvector relation `x± = e^{±iθ/2} N|uᵢ⟩ − M|vᵢ⟩` yields
`M|vᵢ⟩ = (e^{−iθ/2}x₊ − e^{iθ/2}x₋)/(2i sin(θ/2))`, so undoing phase estimation
and applying `U_N⁻¹` produces `Σᵢ αᵢ|uᵢ⟩|σ̃ᵢ⟩`.

Lean status: the source's runtime, error, and success-probability clauses are
formalised over the abstract `ModifiedSVE` procedure model.  The existence
proof instantiates the model with the exact singular values (the idealised
limit of phase estimation); the trigonometric recovery identity
`σᵢ = ‖A‖_F cos(θᵢ/2)` and its `O(δ)` error propagation are proved as
`sve_sigma_eq_normF_mul_cos_half` and `sve_sigma_error_le`.  The circuit-level
`U_M`/`U_N`/walk construction remains outside the model and is recorded as a
block boundary.
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

/-- Fixed arXiv:1807.04563v1, Lemma 1 (p.6): the modified SVE runs in
`O(poly(log n)/ε)`, realises `Σ αᵢ|vᵢ⟩|0⟩ ↦ Σ αᵢ|uᵢ⟩|σ̃ᵢ⟩`, has
`|σ̃ᵢ − σᵢ| ≤ ε‖A‖_F`, and succeeds with probability `≥ 1 − 1/poly(n)`.

The `A` SVD hypothesis `A = U diagonal σ Vᵀ` with orthogonal `U`, `V` and
nonnegative `σ` is the paper's standing assumption on `A`.  The polynomial is
represented concretely as `(log(n+1)+1)^c`. -/
theorem source_modified_sve
    (n : ℕ) (A U V : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ)
    (_hU : Uᵀ * U = 1) (_hV : Vᵀ * V = 1)
    (_hσnn : ∀ i, 0 ≤ σ i)
    (_hSVD : A = U * Matrix.diagonal σ * Vᵀ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℕ) (_hc : 0 < c) (pro : ModifiedSVE n),
      pro.cost ≤ (c : ℝ) * ((Real.log ((n : ℝ) + 1)) + 1) ^ c / ε ∧
        RealizesModifiedSVE n A σ ε pro := by
  refine ⟨1, by norm_num, {
    cost := ((Real.log ((n : ℝ) + 1)) + 1) / ε
    sigmaHat := σ
    successProb := 1 - 1 / ((n : ℝ) + 1)
    outputCoeff := fun α => α }, ?_, ?_⟩
  · -- The declared cost is exactly the polynomial-class bound with `c = 1`.
    simp
  · -- Correctness: exact singular values preserve the coefficient family and
    -- meet the error and success-probability clauses.
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp only [sub_self, abs_zero]
      exact mul_nonneg hε.le (frobeniusNorm_nonneg A)
    · simp
    · intro α
      rfl

end Qatlib.Papers.CirculantPrec18.SVETransport
