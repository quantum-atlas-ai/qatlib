/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

@[expose] public section


/-!
# Gaussian kernel and legacy finite-window discrepancy

Fixed source: Poulin, Qarry, Somma and Verstraete, arXiv:1102.1360v1,
Appendix B, pp. 5–6. The kernel and convolution are faithful definitions.
The legacy discrepancy restricts both propagators and the integral to [0,T].
It is retained for recovery, but is not the source full-line X(infinity):
Gaussian convolution has tails outside [0,T]. No Eq. (B2) bound is claimed.
-/

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace Qatlib.Papers.TimeDepSim11.MainResults.Smoothing

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-- The normal density of width `σ`:
`G_σ(u) = (σ√(2π))⁻¹ exp(-u²/(2σ²))`. (Appendix B, p. 5.) -/
noncomputable def gaussianKernel (σ u : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt (2 * Real.pi))) * Real.exp (-(u ^ 2) / (2 * σ ^ 2))

/-- The Gaussian smoothing kernel is even. -/
theorem kernel_even (σ u : ℝ) : gaussianKernel σ (-u) = gaussianKernel σ u := by
  simp [gaussianKernel]

/-- A positive smoothing width gives a nonnegative kernel. -/
theorem kernel_nonneg (σ u : ℝ) (hσ : 0 < σ) : 0 ≤ gaussianKernel σ u := by
  unfold gaussianKernel
  positivity

/-- The Gaussian-smoothed Hamiltonian `H̃(t) = ∫ G_σ(t-s) H(s) ds` (Appendix B, p. 5). -/
noncomputable def smoothedHamiltonian {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ : ℝ) (t : ℝ) : Matrix I I ℂ :=
  ∫ s : ℝ, gaussianKernel σ (t - s) • H s

/-- The legacy finite-window integral; this is not the full-line source discrepancy. -/
noncomputable def smoothingDiscrepancy {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ T : ℝ) : Matrix I I ℂ :=
  (-(Complex.I : ℂ)) • ∫ t in (0)..T,
    (orderedEvolution (fun u => (Complex.I : ℂ) • H u) 0 t)ᴴ
      * (H t - smoothedHamiltonian H σ t)
      * (orderedEvolution (fun u => (Complex.I : ℂ) • smoothedHamiltonian H σ u) 0 t)

/-- The finite-window discrepancy vanishes on a zero-duration window. -/
theorem discrepancy_zero {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (σ : ℝ) : smoothingDiscrepancy H σ 0 = 0 := by
  simp [smoothingDiscrepancy]

end Qatlib.Papers.TimeDepSim11.MainResults.Smoothing
