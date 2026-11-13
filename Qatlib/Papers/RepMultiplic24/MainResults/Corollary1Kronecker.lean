/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.Lemma2Shots
import Qatlib.Papers.RepMultiplic24.MainResults.Lemma5DimensionBound

/-!
# Polynomial-Sample Estimation of Kronecker Coefficients for Bounded-Depth Partitions

This module proves Corollary 1 of Larocca and Havlicek: when $\mu = (n - k, \alpha_1, \alpha_2, \dots)$
with $\alpha \vdash k$ and $\alpha_1 \le n - k$, the Kronecker coefficient $g_{\mu\lambda\lambda}$
for arbitrary $\lambda \vdash n$ can be resolved with success probability at least $1/2$ using at
most $32 (k! n^k / d_\alpha)^2 + 1$ shots, polynomial in $n$ for fixed $k$.

## Main statements

* `hookDim_pos`: Positivity of the hook-length dimension $d_\mu > 0$.
* `corollary1_kronecker_poly`: Explicit polynomial shot bound for resolving $g_{\mu\lambda\lambda}$
  with success probability at least $1/2$.

## References

* [Larocca and Havlicek, 2025][LaroccaHavlicek2025]
-/

set_option autoImplicit false

namespace Qatlib.Papers.RepMultiplic24.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators unitInterval

/-- The hook-length dimension is strictly positive. -/
theorem hookDim_pos (μ : YoungDiagram) : 0 < hookDim μ := by
  have hprod : (0 : ℚ) < (hookProduct μ : ℚ) := by
    have h1 : (1 : ℚ) ≤ (hookProduct μ : ℚ) := by
      exact_mod_cast one_le_hookProduct μ
    linarith
  unfold hookDim
  exact div_pos (by exact_mod_cast Nat.factorial_pos _) hprod

/-- **Corollary 1** [LaroccaHavlicek2025]: for `μ = (n - k, α₁, α₂, …)` with `α ⊢ k` and
`α.rowLen 0 ≤ n - k`, the Kronecker multiplicity `g` is recovered with probability at least
`1 / 2` from at most `32 * (k! * n ^ k / hookDim α) ^ 2 + 1` shots. -/
theorem corollary1_kronecker_poly (n k g dlam : ℕ) (α μ : YoungDiagram)
    (hcard : α.cells.card = k) (hμ : μ.rowLens = (n - k) :: α.rowLens)
    (hα1 : α.rowLen 0 ≤ n - k) (_hdl : 0 < dlam) (_hg : 0 < g)
    (hgprob : (g : ℚ) ≤ hookDim μ) :
    ∃ N : ℕ, 0 < N ∧
      (N : ℝ) ≤ 32 * ((k.factorial : ℝ) * (n : ℝ) ^ k / (hookDim α : ℝ)) ^ 2 + 1 ∧
      probEvent
        (bernoulliLaw
          ⟨(g : ℝ) / (hookDim μ : ℝ),
            by
              have hμ0 : (0 : ℝ) < (hookDim μ : ℝ) := by exact_mod_cast hookDim_pos μ
              positivity,
            by
              have hμ0 : (0 : ℝ) < (hookDim μ : ℝ) := by exact_mod_cast hookDim_pos μ
              rw [div_le_one hμ0]
              exact_mod_cast hgprob⟩)
        (fun ω : Fin N → Bool => frequencyEstimate (1 / (hookDim μ : ℝ)) ω = g) ≥ 1 / 2 := by
  classical
  have hμ0 : (0 : ℝ) < (hookDim μ : ℝ) := by exact_mod_cast hookDim_pos μ
  have hgle : (g : ℝ) ≤ (hookDim μ : ℝ) := by exact_mod_cast hgprob
  set p : I :=
    ⟨(g : ℝ) / (hookDim μ : ℝ),
      by positivity,
      by rw [div_le_one hμ0]; exact hgle⟩ with hpdef
  have hpm : (p : ℝ) = (g : ℝ) * (1 / (hookDim μ : ℝ)) := by
    simp only [hpdef]
    field_simp
  have hε : (0 : ℝ) < 1 / (hookDim μ : ℝ) := by positivity
  obtain ⟨N, hN, hbound, hprob⟩ := shots_constant_probability p hε hpm
  refine ⟨N, hN, ?_, ?_⟩
  · have hsimple : (32 : ℝ) / (1 / (hookDim μ : ℝ)) ^ 2 + 1 =
        32 * (hookDim μ : ℝ) ^ 2 + 1 := by
      field_simp
    have hsharp : (hookDim μ : ℝ) ≤
        (k.factorial : ℝ) * (n : ℝ) ^ k / (hookDim α : ℝ) := by
      have := lemma5_dimension_bound n k α μ hcard hμ hα1
      exact_mod_cast this
    have hsq : (hookDim μ : ℝ) ^ 2 ≤
        ((k.factorial : ℝ) * (n : ℝ) ^ k / (hookDim α : ℝ)) ^ 2 := by
      have h2 := mul_self_le_mul_self (le_of_lt hμ0) hsharp
      simpa [pow_two] using h2
    nlinarith [hbound, hsimple, hsq]
  · exact hprob

end Qatlib.Papers.RepMultiplic24.MainResults
