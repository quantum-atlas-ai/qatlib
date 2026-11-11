/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagingLimit06.MainResults.FisherCore
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Intensity Fisher information and resolution bounds

`poissonPixelFisher` collects the pixel mean derivative expression for intensity measurements.
Under the stated nonvanishing and constant-intensity conditions, it equals `4N/a²`; reciprocal
variance hypotheses then give the ordinary and sub-Poissonian resolution bounds. See
[DelaubertEtAl2008] for the paper context.

## Main statements

* `poisson_intensity_fisher_value`: For nonzero pixel amplitudes with the stated
  constant-intensity and derivative-scale identities, the Poisson Fisher expression equals
  `4N/a²`.
* `poisson_intensity_quantum_limit`: Given Fisher information `4N/a²` and its reciprocal
  variance bound, the resolution is at least `a/(2√N)` for positive `N` and `a`.
* `sub_poisson_intensity_quantum_limit`: Given Fisher information `4N/(a²σ²)` and its reciprocal
  variance bound, the resolution is at least `aσ/(2√N)` for positive parameters.

## References

* [Delaubert et al., 2008][DelaubertEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QImagingLimit06.MainResults

/-- The pixel sum of the squared first mean derivative divided by the mean, minus the second
mean derivative. -/
def poissonPixelFisher {ι : Type} [Fintype ι] (nbar nbar' nbar'' : ι → ℝ) : ℝ :=
  ∑ k, ((nbar' k) ^ 2 / nbar k - nbar'' k)

/-- For nonzero pixel amplitudes with the stated constant-intensity and derivative-scale
identities, the Poisson Fisher expression equals `4N/a²`. See [DelaubertEtAl2008]. -/
theorem poisson_intensity_fisher_value {ι : Type} [Fintype ι] {N a : ℝ}
    (hN : 0 < N) (ha : 0 < a) (u du ddu : ι → ℝ)
    (hu : ∀ k, u k ≠ 0)
    (hconst : ∑ k, (du k ^ 2 + u k * ddu k) = 0)
    (ha_def : 1 / a ^ 2 = ∑ k, du k ^ 2) :
    poissonPixelFisher (fun k => N * u k ^ 2)
        (fun k => 2 * N * u k * du k)
        (fun k => 2 * N * (du k ^ 2 + u k * ddu k)) = 4 * N / a ^ 2 := by
  have hterm : ∀ k, (2 * N * u k * du k) ^ 2 / (N * u k ^ 2) -
      2 * N * (du k ^ 2 + u k * ddu k) =
      4 * N * du k ^ 2 - 2 * N * (du k ^ 2 + u k * ddu k) := by
    intro k
    have hN0 : N ≠ 0 := hN.ne'
    have huk : u k ≠ 0 := hu k
    field_simp
    ring
  have hsum1 : ∑ k, (4 * N * du k ^ 2) = 4 * N * ∑ k, du k ^ 2 := by
    rw [Finset.mul_sum]
  have hsum2 : ∑ k, (2 * N * (du k ^ 2 + u k * ddu k)) =
      2 * N * ∑ k, (du k ^ 2 + u k * ddu k) := by
    rw [Finset.mul_sum]
  unfold poissonPixelFisher
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
  rw [hsum1, hsum2, hconst, mul_zero, sub_zero, ← ha_def]
  have ha' : a ≠ 0 := ha.ne'
  field_simp

/-- Given Fisher information `4N/a²` and its reciprocal variance bound, the resolution is at
least `a/(2√N)` for positive `N` and `a`. See [DelaubertEtAl2008]. -/
theorem poisson_intensity_quantum_limit {N a Var pmin : ℝ} (hN : 0 < N)
    (ha : 0 < a) (IF : ℝ) (hIF : IF = 4 * N / a ^ 2)
    (hVar : 1 / IF ≤ Var) (hpmin : pmin = Real.sqrt Var) :
    a / (2 * Real.sqrt N) ≤ pmin := by
  have hIFpos : 0 < IF := by rw [hIF]; positivity
  have hbnd := cramerRao_bound hIFpos hVar hpmin
  rwa [hIF, resolution_intensity_fisher hN ha] at hbnd

/-- Given Fisher information `4N/(a²σ²)` and its reciprocal variance bound, the resolution is at
least `aσ/(2√N)` for positive parameters. See [DelaubertEtAl2008]. -/
theorem sub_poisson_intensity_quantum_limit {N a σ Var pmin : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hσ : 0 < σ) (IF : ℝ)
    (hIF : IF = 4 * N / (a ^ 2 * σ ^ 2))
    (hVar : 1 / IF ≤ Var) (hpmin : pmin = Real.sqrt Var) :
    a * σ / (2 * Real.sqrt N) ≤ pmin := by
  have hIFpos : 0 < IF := by rw [hIF]; positivity
  have hbnd := cramerRao_bound hIFpos hVar hpmin
  rwa [hIF, resolution_gauss_fisher hN ha hσ] at hbnd

end Qatlib.Papers.QImagingLimit06.MainResults
