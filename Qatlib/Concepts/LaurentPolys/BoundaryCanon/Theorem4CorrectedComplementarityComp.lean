/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Theorem4CorrectedComplementarityStat
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.MetricLossEquivalenceComp
public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Downscaling and the specified Fourier construction produce a polynomial of degree at most
`d` with unit circle complementarity residual below `ε` under the stated grid threshold. -/
theorem theorem4CorrectedComplementarity : Theorem4CorrectedComplementarity := by
  intro P₀ d m ε hd hPd hε hε1 hP₀
  (try dsimp only)
  intro hm hgrid hthreshold
  have h := scaled_complement_same_fft_uniform_residual P₀ d m ε
    hd hPd hε hε1 hP₀ hm hgrid hthreshold
  exact ⟨h.1, h.2.1⟩

/-- The corrected downscaled Fourier complement has degree at most `d`, uniform residual and
unitarity defect below `ε`, and autocorrelation loss below `Real.sqrt (2*d+1) * ε`. -/
theorem theorem4CorrectedComplementarity_with_l2_and_phiTilde
    (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ)
    (hd : 0 < d) (hPd : P₀.natDegree ≤ d) (hε : 0 < ε) (hε1 : ε < 1)
    (hP₀ : ∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1) :
    let P := (1 - ε / 4 : ℂ) • P₀
    let N := 2 ^ m
    let δ := ε / 4
    let η := ε / (16 * (d + 1))
    let ρ := (1 / (1 - δ)) ^ (1 / (d : ℝ) : ℝ)
    1 ≤ m → d + 1 ≤ N →
    (Nat.ceil (2 / Real.log ρ * Real.log (8 * Real.log (1 / δ) / (ρ - 1) / η)) : ℕ) ≤ N →
    let ω := Complex.exp ((2 * Real.pi / (N : ℝ) : ℝ) * Complex.I)
    let a := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      ((Real.log (1 - ‖P.eval (ω ^ j.val)‖ ^ 2) : ℝ) : ℂ) * ω ^ (-(n * j.val : ℤ))
    let q := fun n : ℕ => (N : ℂ)⁻¹ * ∑ j : Fin N,
      Complex.exp ((2 : ℂ)⁻¹ * a 0 +
        ∑ l ∈ Finset.range (N / 2 + 1), if l = 0 then 0 else a l * ω ^ (l * j.val)) *
        ω ^ (-(n * j.val : ℤ))
    let Q := ∑ n ∈ Finset.range (d + 1), Polynomial.monomial n (q n)
    Q.natDegree ≤ d ∧
    (∀ z : ℂ, ‖z‖ = 1 → circleResidual P₀ Q z < ε) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ‖(circleCompletion P₀ Q z)ᴴ * circleCompletion P₀ Q z - 1‖ < ε) ∧
    sourcePhiUniform P₀ Q < ε ∧
    sourcePhiTilde P₀ Q d < Real.sqrt (2 * (d : ℝ) + 1) * ε := by
  (try dsimp only)
  intro hm hgrid hthreshold
  obtain ⟨hdeg, hres, hl2⟩ := scaled_complement_same_fft_uniform_residual P₀ d m ε
    hd hPd hε hε1 hP₀ hm hgrid hthreshold
  obtain ⟨z₀, hz₀, hmax⟩ := sourcePhiUniform_attained P₀
    (∑ n ∈ Finset.range (d + 1), Polynomial.monomial n _)
  have hphi : sourcePhiUniform P₀ _ < ε := hmax ▸ hres z₀ hz₀
  have htilde := (metric_loss_equivalence P₀ _ d hPd hdeg).2
  have hsqrt_pos : 0 < Real.sqrt (2 * (d : ℝ) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  refine ⟨hdeg, hres, hl2, hphi, htilde.trans_lt ?_⟩
  exact mul_lt_mul_of_pos_left hphi hsqrt_pos

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
