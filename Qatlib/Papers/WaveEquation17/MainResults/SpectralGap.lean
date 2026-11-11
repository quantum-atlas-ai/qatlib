/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# WaveEquation17.MainResults.SpectralGap

Fixed arXiv:1711.05394v4 (Costa--Jordan--Ostrander), Theorem 1, equations (53)--(55)
and the fundamental-gap argument on page 20.

The source considers the divergence operator `Div` on a bounded convex domain `Ω` and
solves `Div v = f` with `v` having no divergenceless component.  Since
`∇² = ∇†∇ = Div† Div`, the singular values of `Div` are the square roots of the
eigenvalues of the Laplacian.  The fundamental gap theorem gives the lower bound
`π²/ℓ²` for the smallest nontrivial Neumann eigenvalue, hence the smallest nonzero
singular value of `Div` is at least `π/ℓ`, and the Moore--Penrose inverse obeys
`‖Div⁻¹ f‖ ≤ (ℓ/π)‖f‖` (equation (54)).

The lattice representation used here replaces the continuum `L²(Ω)` norms by the
finite-dimensional Hilbert-space norms of the discretised fields, and states the gap
hypothesis in the equivalent singular-value form
`μ² ‖v‖² ≤ ‖Div v‖²` for `v` orthogonal to `ker Div`.  The conclusion is the same
pseudoinverse estimate (54).
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate

namespace Qatlib.Papers.WaveEquation17.MainResults

/-- Theorem 1, singular-value form: if the divergence operator `div` has no nonzero
singular value below `μ`, then every minimum-norm solution of `div v = f` (i.e. every
`v` orthogonal to `ker div`, the source's "no divergenceless component") satisfies
`‖v‖ ≤ μ⁻¹ ‖div v‖`.

The hypothesis `hgap` is the finite-dimensional form of the fundamental-gap input
cited by the source: the smallest nontrivial eigenvalue of the Laplacian is at least
`π²/ℓ²`, and the singular values of `div` are its square roots. -/
theorem theorem1_divergence_pseudoinverse_norm
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (div : E →L[ℂ] F) (μ : ℝ) (hμ : 0 < μ)
    (hgap : ∀ v : E, v ∈ (LinearMap.ker div.toLinearMap)ᗮ →
      μ ^ 2 * ‖v‖ ^ 2 ≤ ‖div v‖ ^ 2)
    (v : E) (hv : v ∈ (LinearMap.ker div.toLinearMap)ᗮ) :
    ‖v‖ ≤ μ⁻¹ * ‖div v‖ := by
  have hsq : (μ * ‖v‖) ^ 2 ≤ ‖div v‖ ^ 2 := by
    have h := hgap v hv
    nlinarith [sq_nonneg (‖v‖), sq_nonneg (‖div v‖), hμ.le]
  have hle : μ * ‖v‖ ≤ ‖div v‖ := by
    have h := sq_le_sq.mp hsq
    simpa [abs_of_nonneg (mul_nonneg hμ.le (norm_nonneg _)),
      abs_of_nonneg (norm_nonneg _)] using h
  have h1 : ‖v‖ ≤ ‖div v‖ / μ :=
    (le_div_iff₀ hμ).mpr (by linarith)
  simpa [div_eq_inv_mul] using h1

/-- Theorem 1 in the source's geometric notation: on a domain of diameter `ℓ` the
divergence inverse obeys the bound (54),
`‖Div⁻¹ f‖ ≤ (ℓ/π) ‖f‖`.

The hypothesis `hgap` is the fundamental-gap lower bound on the Laplacian transported
to the singular values of `div`; the conclusion is the pseudoinverse estimate with
`f = div v`. -/
theorem theorem1_divergence_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (div : E →L[ℂ] F) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hgap : ∀ v : E, v ∈ (LinearMap.ker div.toLinearMap)ᗮ →
      (Real.pi / ℓ) ^ 2 * ‖v‖ ^ 2 ≤ ‖div v‖ ^ 2)
    (v : E) (hv : v ∈ (LinearMap.ker div.toLinearMap)ᗮ) :
    ‖v‖ ≤ (ℓ / Real.pi) * ‖div v‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hμ : 0 < Real.pi / ℓ := div_pos hpi hℓ
  have h := theorem1_divergence_pseudoinverse_norm div (Real.pi / ℓ) hμ hgap v hv
  have hinv : (Real.pi / ℓ)⁻¹ = ℓ / Real.pi := inv_div _ _
  simpa [hinv] using h

end Qatlib.Papers.WaveEquation17.MainResults
