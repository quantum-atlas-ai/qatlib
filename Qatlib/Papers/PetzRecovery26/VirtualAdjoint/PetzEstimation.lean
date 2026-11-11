/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PetzRecovery26.VirtualAdjoint.BaseNorm
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

set_option backward.isDefEq.respectTransparency false

/-!
# Petz recovery expectation estimation (main application, pp. 5--6)

Fixed source version: arXiv:2602.05828v1 (first submitted 2026-02-05),
Section III C ("Petz map of unknown quantum channel", pp. 5--6), Fig. 3 and
Eqs. (14)--(20).

The protocol estimates `Tr[O_A P_{σ,N}(ω_B)]` for an unknown channel `N` by
sampling `M` post-selected rounds and averaging the resulting unbiased
estimates.  Each round's estimate is bounded by the base norm
`γ = d_A d_B − d_A + 1` of the virtual comb of Theorem 3 / Theorem 4, so
Hoeffding's inequality gives precision `ε` with failure probability `δ` once

  `M ≥ 2 γ² log(2/δ) / ε² = O(d_A² d_B² log(1/δ) / ε²)`,

the body's complexity in Section III C (the abstract's `Õ(d_A⁴ d_B³/ε²)` counts
the block-encoding cost of `N(σ)^{-1/2}` on top of this sampling cost; the two
differ by a `d_A² d_B` factor, an inconsistency between abstract and body that
is flagged in the claim metadata).

This file formalises the sampling/concentration core:

* `gammaBaseNorm dA dB` is the paper's base-norm scale `d_A d_B − d_A + 1`
  (Theorem 4);
* `sampleMean` is the `1/M`-weighted sample average used by the estimator;
* `petzEstimation_hoeffding` bounds the two-sided deviation of the sample
  mean from its expectation by `2 exp(−M ε²/(2γ²))`, using the frozen
  `independent_weighted_hoeffding` concentration theorem;
* `petzEstimation_sampleComplexity` converts this into the failure
  probability `δ` under the sample-size condition above;
* `petzEstimation_queryComplexity` states the result with the Theorem 4
  constant `γ = d_A d_B − d_A + 1`.

The physical block-encodings of `σ^{1/2}` and `N(σ)^{-1/2}` and the
state-preparation maps of Fig. 3 are not modelled; the estimators are treated
as the bounded random variables supplied to Hoeffding's inequality.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

namespace Qatlib.Papers.PetzRecovery26.VirtualAdjoint

/-- The `1/M`-weighted sample mean of the per-round estimates `f i (ω i)`. -/
def sampleMean {M : ℕ} {X : Fin M → Type*} (f : ∀ i, X i → ℝ)
    (ω : ∀ i, X i) : ℝ :=
  weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f ω

/-- **Hoeffding step of the Petz-estimation protocol (Section III C, p. 5).**
For `M` independent rounds with per-round estimates `f i` bounded in
`[-γ, γ]`, the sample mean deviates from its expectation by at least `ε` with
probability at most `2 exp(−M ε²/(2γ²))`.

This is the paper's "By Hoeffding's inequality, the number of samples `M`
required ... scales as `M = O(d²_A d²_B log(1/δ)/ε²)`", with the bound
`γ²` on the per-sample variance coming from the base norm of the virtual comb
(Theorem 4). -/
theorem petzEstimation_hoeffding (M : ℕ) (hM : 0 < M) {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε)
    {X : Fin M → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (f : ∀ i, X i → ℝ)
    (hf : ∀ i x, f i x ∈ Set.Icc (-γ) γ) :
    eventMass (independent p)
      (fun ω => ε ≤ |weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f ω -
        (independent p).expect (weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f)|) ≤
      2 * Real.exp (-(M : ℝ) * ε ^ 2 / (2 * γ ^ 2)) := by
  classical
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hγne : γ ≠ 0 := hγ.ne'
  have hSval :
      (∑ i : Fin M, ((M : ℝ))⁻¹ ^ 2 * (γ - -γ) ^ 2) = 4 * γ ^ 2 / (M : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hS : 0 < ∑ i : Fin M, ((M : ℝ))⁻¹ ^ 2 * (γ - -γ) ^ 2 := by
    rw [hSval]
    positivity
  have hhab : ∀ i : Fin M, -γ ≤ γ := fun _ => by linarith
  have h := independent_weighted_hoeffding (I := Fin M) p
    (fun _ : Fin M => ((M : ℝ))⁻¹) f (fun _ : Fin M => -γ) (fun _ : Fin M => γ)
    ε hhab hf hε hS
  calc
    eventMass (independent p)
        (fun ω => ε ≤ |weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f ω -
          (independent p).expect (weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f)|) ≤
        2 * Real.exp (-2 * ε ^ 2 /
          (∑ i : Fin M, ((M : ℝ))⁻¹ ^ 2 * (γ - -γ) ^ 2)) := h
    _ = 2 * Real.exp (-(M : ℝ) * ε ^ 2 / (2 * γ ^ 2)) := by
      rw [hSval]
      congr 1
      field_simp
      ring

/-- **Sample complexity of the Petz-estimation protocol (Section III C,
p. 5).**  If the number of rounds satisfies
`M ≥ 2 γ² log(2/δ)/ε²`, the sample mean is within `ε` of its expectation with
probability at least `1 − δ`. -/
theorem petzEstimation_sampleComplexity (M : ℕ) (hM : 0 < M) {γ ε δ : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hδ : 0 < δ)
    (hMδ : 2 * γ ^ 2 * Real.log (2 / δ) / ε ^ 2 ≤ (M : ℝ))
    {X : Fin M → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (f : ∀ i, X i → ℝ)
    (hf : ∀ i x, f i x ∈ Set.Icc (-γ) γ) :
    eventMass (independent p)
      (fun ω => ε ≤ |weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f ω -
        (independent p).expect (weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f)|) ≤ δ := by
  classical
  refine (petzEstimation_hoeffding M hM hγ hε p f hf).trans ?_
  have hγne : γ ≠ 0 := hγ.ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hδne : δ ≠ 0 := hδ.ne'
  have hexp : Real.exp (-(M : ℝ) * ε ^ 2 / (2 * γ ^ 2)) ≤ δ / 2 := by
    have hpos : 0 < ε ^ 2 / (2 * γ ^ 2) := by positivity
    have hlog : Real.log (2 / δ) ≤ (M : ℝ) * ε ^ 2 / (2 * γ ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hMδ (le_of_lt hpos)
      have heq : (2 * γ ^ 2 * Real.log (2 / δ) / ε ^ 2) * (ε ^ 2 / (2 * γ ^ 2)) =
          Real.log (2 / δ) := by
        field_simp
      calc Real.log (2 / δ) =
            (2 * γ ^ 2 * Real.log (2 / δ) / ε ^ 2) * (ε ^ 2 / (2 * γ ^ 2)) := heq.symm
        _ ≤ (M : ℝ) * (ε ^ 2 / (2 * γ ^ 2)) := hmul
        _ = (M : ℝ) * ε ^ 2 / (2 * γ ^ 2) := by ring
    calc Real.exp (-(M : ℝ) * ε ^ 2 / (2 * γ ^ 2))
        = Real.exp (-((M : ℝ) * ε ^ 2 / (2 * γ ^ 2))) := by
          congr 1
          ring
      _ ≤ Real.exp (-Real.log (2 / δ)) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = δ / 2 := by
          rw [Real.exp_neg, Real.exp_log (show (0 : ℝ) < 2 / δ by positivity), inv_div]
  nlinarith [hexp]

/-- **Petz recovery expectation estimation with the Theorem 4 base-norm
constant (pp. 4--6).**  With `γ = d_A d_B − d_A + 1` and
`M ≥ 2 γ² log(2/δ)/ε² = O(d_A² d_B² log(1/δ)/ε²)` rounds, the empirical mean
of the post-selected estimates of `Tr[O_A P_{σ,N}(ω_B)]` is within `ε` of its
expectation with probability at least `1 − δ`. -/
theorem petzEstimation_queryComplexity (dA dB M : ℕ) (hM : 0 < M)
    (hdA : 0 < dA) (hdB : 0 < dB) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hMδ : 2 * (gammaBaseNorm dA dB) ^ 2 * Real.log (2 / δ) / ε ^ 2 ≤ (M : ℝ))
    {X : Fin M → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (f : ∀ i, X i → ℝ)
    (hf : ∀ i x, f i x ∈ Set.Icc (-(gammaBaseNorm dA dB)) (gammaBaseNorm dA dB)) :
    eventMass (independent p)
      (fun ω => ε ≤ |weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f ω -
        (independent p).expect (weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹) f)|) ≤ δ :=
  petzEstimation_sampleComplexity M hM (gammaBaseNorm_pos hdA hdB) hε hδ hMδ p f hf

end Qatlib.Papers.PetzRecovery26.VirtualAdjoint
