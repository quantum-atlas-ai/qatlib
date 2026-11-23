/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.SourceTheorem1GapAmplification

/-!
# A satisfiable endpoint model

The input is the single projector `diag(0,1)`, whose nonzero gap is one.
The undoubled skeleton made its amplified matrix zero; the actual doubled
register satisfies the repaired global gap theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.SourceExamples

open Matrix
open AmplifiedRegister
open scoped BigOperators

noncomputable section

/-- The single nontrivial input projector. -/
def endpointProj : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ => Matrix.diagonal ![0, 1]

/-- The example terms are actual idempotent matrices. -/
theorem endpoint_idempotent (k : Fin 1) : endpointProj k * endpointProj k = endpointProj k := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [endpointProj, Matrix.mul_apply, Fin.sum_univ_two]

/-- The example terms are Hermitian. -/
theorem endpoint_hermitian (k : Fin 1) : (endpointProj k).IsHermitian := by
  change (Matrix.diagonal ![(0 : ℂ), 1])ᴴ = _
  simp [endpointProj]

/-- The input-gap hypothesis has a concrete, nontrivial satisfying model. -/
theorem endpoint_inputGap : InputGap (∑ k, endpointProj k) 1 1 := by
  intro lambda psi hpsi heigen
  have h0 := congrFun heigen (0 : Fin 2)
  have h1 := congrFun heigen (1 : Fin 2)
  simp [endpointProj, Matrix.mulVec_diagonal] at h0 h1
  by_cases hlambda : lambda = 0
  · subst lambda
    norm_num
  · have hp0 : psi 0 = 0 := h0.resolve_left hlambda
    have hp1 : psi 1 ≠ 0 := by
      intro hp1
      apply hpsi
      funext i
      fin_cases i
      · exact hp0
      · exact hp1
    have hc : (lambda : ℂ) = 1 := by
      apply mul_right_cancel₀ hp1
      simpa only [one_mul] using h1.symm
    have hlone : lambda = 1 := by exact_mod_cast hc
    subst lambda
    norm_num

/-- The repaired endpoint example has a genuine uniform output gap. -/
theorem endpoint_amplified_gap (mu : ℝ) (v : Fin 2 × (Fin 1 × Bool) → ℂ)
    (hv : v ≠ 0) (heigen : doubledHamiltonian endpointProj 1 *ᵥ v = (mu : ℂ) • v)
    (hmu : mu ≠ 0) : (1 : ℝ) / 2 ≤ |mu| := by
  have hground : ∀ k, endpointProj k *ᵥ ![(1 : ℂ), 0] = 0 := by
    intro k
    funext i
    fin_cases i <;> simp [endpointProj, Matrix.mulVec_diagonal]
  have h := doubled_register_gap_and_nullity endpointProj endpoint_idempotent endpoint_hermitian
    (by norm_num : 0 < Fintype.card (Fin 1)) ![(1 : ℂ), 0] hground 1 (by norm_num)
    (by simpa using endpoint_inputGap)
  have hg := h.2.1 mu v hv
  norm_num at hg
  exact hg heigen hmu

end

end Qatlib.Papers.SpectralGap11.MainResults.SourceExamples
