/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound.Eq7

/-!
# Sequential spectra under permutations

The function `seqEigen` sums generator eigenvalues after a separate permutation at each step.
This module proves interval and variance bounds for that sum, derives the conditional precision
inequality, and identifies configurations with a constant selected eigenvalue. See
[GiovannettiLloydMaccone2006].

## Main statements

* `seqEigen_bounds`: If `lam` takes values in `[a, b]`, every sequential eigenvalue sum lies in
  `[N * a, N * b]`.
* `seqEigen_variance_le`: The variance of the permuted sequential eigenvalue sum is at most `(N
  * spectralSpread a b) ^ 2`.
* `sequential_error_bound_perm`: For the permuted sequential eigenvalue model, the stated
  Cramér–Rao and bounded spectrum hypotheses imply error at least `1 / (√ν * N * (b - a))`.

## References

* [Giovannetti et al., 2006][GiovannettiLloydMaccone2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound

open Qatlib.Papers.QuantumMetro05.MainResults.Source
open Qatlib.Papers.QuantumMetro05.MainResults.QuantumBound

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The sum of the values of `lam` at the coordinatewise permuted configuration `ω`. -/
def seqEigen (lam : X → ℝ) {N : ℕ} (σ : Fin N → X ≃ X) (ω : Fin N → X) : ℝ :=
  ∑ j, lam (σ j (ω j))

/-- If `lam` takes values in `[a, b]`, every sequential eigenvalue sum lies in `[N * a, N * b]`.
See [GiovannettiLloydMaccone2006]. -/
theorem seqEigen_bounds {X : Type} (lam : X → ℝ) {N : ℕ} {a b : ℝ}
    (ha : ∀ x, a ≤ lam x) (hb : ∀ x, lam x ≤ b) (σ : Fin N → X ≃ X)
    (ω : Fin N → X) :
    (N : ℝ) * a ≤ seqEigen lam σ ω ∧ seqEigen lam σ ω ≤ (N : ℝ) * b :=
  spectralSumBounds (fun j => lam (σ j (ω j)))
    (fun j => ha (σ j (ω j))) (fun j => hb (σ j (ω j)))

/-- The variance of the permuted sequential eigenvalue sum is at most `(N * spectralSpread a b)
^ 2`. See [GiovannettiLloydMaccone2006]. -/
theorem seqEigen_variance_le {N : ℕ} (p : FinDist (Fin N → X)) (lam : X → ℝ)
    {a b : ℝ} (ha : ∀ x, a ≤ lam x) (hb : ∀ x, lam x ≤ b) (σ : Fin N → X ≃ X) :
    p.variance (seqEigen lam σ) ≤ ((N : ℝ) * spectralSpread a b) ^ 2 := by
  have h := variance_le_spread_sq p (seqEigen lam σ)
    (fun ω => (seqEigen_bounds lam ha hb σ ω).1)
    (fun ω => (seqEigen_bounds lam ha hb σ ω).2)
  have hs : spectralSpread ((N : ℝ) * a) ((N : ℝ) * b)
      = (N : ℝ) * spectralSpread a b := by
    rw [spectralSpread_def, spectralSpread_def]; ring
  rwa [hs] at h

/-- For the permuted sequential eigenvalue model, the stated Cramér–Rao and bounded spectrum
hypotheses imply error at least `1 / (√ν * N * (b - a))`. See [GiovannettiLloydMaccone2006]. -/
theorem sequential_error_bound_perm {N : ℕ} (hN : 0 < N) (p : FinDist (Fin N → X))
    (lam : X → ℝ) (σ : Fin N → X ≃ X) {a b ν δφ : ℝ}
    (hν : 0 < ν) (hab : a < b) (ha : ∀ x, a ≤ lam x) (hb : ∀ x, lam x ≤ b)
    (hcr : δφ * Real.sqrt (p.variance (fun ω => ∑ j, lam (σ j (ω j))))
            ≥ 1 / (2 * Real.sqrt ν)) :
    1 / (Real.sqrt ν * (N : ℝ) * (b - a)) ≤ δφ :=
  qc_qq_error_bound (X := Fin N → X) hN p (fun j ω => lam (σ j (ω j))) hν hab
    (fun j ω => ha (σ j (ω j))) (fun j ω => hb (σ j (ω j))) hcr

/-- Choosing each coordinate as the inverse permutation image of `x` makes the sequential
eigenvalue sum equal to `N * lam x`. -/
theorem seqEigen_constEigen {X : Type} (lam : X → ℝ) {N : ℕ} (σ : Fin N → X ≃ X) (x : X) :
    seqEigen lam σ (fun j => (σ j).symm x) = (N : ℝ) * lam x := by
  unfold seqEigen
  simp only [Equiv.apply_symm_apply]
  simp

end Qatlib.Papers.QuantumMetro05.MainResults.SequentialBound
