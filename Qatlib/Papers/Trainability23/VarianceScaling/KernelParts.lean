/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Trainability23.VarianceScaling.Basic
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# KernelParts source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.VarianceScaling
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.VarianceScaling.KernelParts

/-- The data-dependent part `C_σ(P̃)` of the MMD variance, Eq. (237):
`Σ_{A ≠ ∅} (1−p_σ)^{2(n−|A|)} (p_σ/3)^{|A|} z_A(P̃)²`. -/
def cSigma (n : ℕ) (pσ : ℝ) (z : Finset (Fin n) → ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.Nonempty),
    (1 - pσ) ^ (2 * (n - A.card)) * (pσ / 3) ^ A.card * (z A) ^ 2

/-- The paper's `p_σ = (1 − e^{−1/(2σ)})/2` of Eq. (162)/(237). -/
def pSigmaVal (σ : ℝ) : ℝ := (1 - kernelGap σ) / 2


/-- **Supplemental Proposition 2, Eq. (236), restated over the Frozen `bSigma`.**  The
data-independent part is the difference of the two powers
`[(7+6q+2q²)/15]^n − [(4+4q+q²)/9]^n` with `q = e^{−1/(2σ)}`; this is exactly the Frozen
theorem `sN_variance_eq` for the factorized `qq` model. -/
theorem bSigma_formula (n : ℕ) (σ : ℝ) :
    bSigma n σ
      = ((7 + 6 * kernelGap σ + 2 * kernelGap σ ^ 2) / 15) ^ n
        - ((4 + 4 * kernelGap σ + kernelGap σ ^ 2) / 9) ^ n := by
  unfold bSigma bSigmaBaseA bSigmaBaseB
  rfl

/-- **Eq. (237), nonnegativity.**  Every term of `C_σ(P̃)` carries a nonnegative factor
`(1−p_σ)^{2(n−|A|)} (p_σ/3)^{|A|} z_A²`, so the data-dependent part of the variance is
nonnegative — the sanity check `B_σ + 4C_σ(P̃) ≥ B_σ` used in Theorem 2.  Proved under the range
hypothesis `0 ≤ p_σ ≤ 1` of Eq. (162). -/
theorem cSigma_nonneg (n : ℕ) (pσ : ℝ) (hp0 : 0 ≤ pσ) (hp1 : pσ ≤ 1)
    (z : Finset (Fin n) → ℝ) : 0 ≤ cSigma n pσ z := by
  unfold cSigma
  refine Finset.sum_nonneg fun A _ => ?_
  have h1 : 0 ≤ 1 - pσ := by linarith
  have h2 : 0 ≤ pσ / 3 := by linarith
  exact mul_nonneg (mul_nonneg (pow_nonneg h1 _) (pow_nonneg h2 _)) (sq_nonneg _)

end Qatlib.Papers.Trainability23.VarianceScaling.KernelParts
