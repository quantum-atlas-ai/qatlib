/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity.Theorem5Fidelity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cosine overlap bounds from phase variance

The module bounds weighted cosine overlaps by a quadratic phase-error expression. The constants
in `fidelity_of_variance_le` and `step_count_suffices` translate the variance estimate `186 / M
^ 2` into the overlap and parameter bounds used in the sine-window analysis of [Childs2010].

## Main statements

* `weighted_cos_ge`: a weighted second-moment bound on the cosine overlap.
* `fidelity_of_variance_le`: the overlap is at least `1 - 93 * t ^ 2 / M ^ 2`.
* `step_count_suffices`: a sufficient parameter choice for error at most `δ`.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Papers.ContDiscWalk08.SineReadout

variable {ι : Type*} [Fintype ι]

/-- For nonnegative weights summing to one, the weighted cosine of the sine-phase differences is
at least one minus half `t ^ 2` times the weighted squared phase error. This is an overlap
estimate for [Childs2010]. -/
theorem weighted_cos_ge (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (θ φ : ι → ℝ) (t : ℝ) :
    1 - t ^ 2 / 2 * (∑ i, p i * (θ i - φ i) ^ 2)
      ≤ ∑ i, p i * Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) := by
  have hpoint : ∀ i, p i * (1 - t ^ 2 * (θ i - φ i) ^ 2 / 2)
      ≤ p i * Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) := by
    intro i
    have hcos := Real.one_sub_sq_div_two_le_cos
      (x := t * (Real.sin (θ i) - Real.sin (φ i)))
    have hs := Real.abs_sin_sub_sin_le (θ i) (φ i)
    have hsquare : (t * (Real.sin (θ i) - Real.sin (φ i))) ^ 2
        ≤ t ^ 2 * (θ i - φ i) ^ 2 := by
      have h1 : |Real.sin (θ i) - Real.sin (φ i)| ^ 2 ≤ |θ i - φ i| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hs 2
      rw [sq_abs, sq_abs] at h1
      nlinarith [sq_nonneg t]
    have hcos' : 1 - t ^ 2 * (θ i - φ i) ^ 2 / 2
        ≤ Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) := by
      nlinarith [hcos]
    exact mul_le_mul_of_nonneg_left hcos' (hp i)
  have hsum_eq : (∑ i, p i * (1 - t ^ 2 * (θ i - φ i) ^ 2 / 2))
      = 1 - t ^ 2 / 2 * (∑ i, p i * (θ i - φ i) ^ 2) := by
    have hterm : ∀ i, p i * (1 - t ^ 2 * (θ i - φ i) ^ 2 / 2)
        = p i - (t ^ 2 / 2) * (p i * (θ i - φ i) ^ 2) := by
      intro i
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
      Finset.mul_sum, hsum]
  calc 1 - t ^ 2 / 2 * (∑ i, p i * (θ i - φ i) ^ 2)
      = ∑ i, p i * (1 - t ^ 2 * (θ i - φ i) ^ 2 / 2) := hsum_eq.symm
    _ ≤ ∑ i, p i * Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) :=
        Finset.sum_le_sum (fun i _ => hpoint i)

/-- The cosine of `t * (sin θ - sin φ)` is at least `1 - t ^ 2 * (θ - φ) ^ 2 / 2`, as used in
the readout analysis of [Childs2010]. -/
theorem cos_ge_one_sub_sq (θ φ t : ℝ) :
    1 - t ^ 2 * (θ - φ) ^ 2 / 2 ≤ Real.cos (t * (Real.sin θ - Real.sin φ)) := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := t * (Real.sin θ - Real.sin φ))
  have hs := Real.abs_sin_sub_sin_le θ φ
  have hsquare : (t * (Real.sin θ - Real.sin φ)) ^ 2 ≤ t ^ 2 * (θ - φ) ^ 2 := by
    have h1 : |Real.sin θ - Real.sin φ| ^ 2 ≤ |θ - φ| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hs 2
    rw [sq_abs, sq_abs] at h1
    nlinarith [sq_nonneg t]
  nlinarith [hcos]

/-- A weighted phase-error second moment at most `186 / M ^ 2`, with `M > 0`, gives a weighted
cosine overlap at least `1 - 93 * t ^ 2 / M ^ 2`. See [Childs2010]. -/
theorem fidelity_of_variance_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (θ φ : ι → ℝ) (t M : ℝ) (hM : 0 < M)
    (hV : ∑ i, p i * (θ i - φ i) ^ 2 ≤ 186 / M ^ 2) :
    1 - 93 * t ^ 2 / M ^ 2
      ≤ ∑ i, p i * Real.cos (t * (Real.sin (θ i) - Real.sin (φ i))) := by
  have hcore := weighted_cos_ge p hp hsum θ φ t
  have hcoef : t ^ 2 / 2 * (∑ i, p i * (θ i - φ i) ^ 2) ≤ t ^ 2 / 2 * (186 / M ^ 2) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  have harith : t ^ 2 / 2 * (186 / M ^ 2) = 93 * t ^ 2 / M ^ 2 := by
    field_simp
    ring
  nlinarith [hcore, hcoef]

/-- For positive `M` and `δ`, the lower bound `|t| * √(93 / δ) ≤ M` ensures `93 * t ^ 2 / M ^ 2
≤ δ`. This supplies a sufficient readout parameter bound for [Childs2010]. -/
theorem step_count_suffices (t δ M : ℝ) (hM : 0 < M) (hδ : 0 < δ)
    (hsteps : |t| * Real.sqrt (93 / δ) ≤ M) :
    93 * t ^ 2 / M ^ 2 ≤ δ := by
  have h93δ : 0 < 93 / δ := by positivity
  have hsquares : t ^ 2 * (93 / δ) ≤ M ^ 2 := by
    have hnonneg : 0 ≤ |t| * Real.sqrt (93 / δ) :=
      mul_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
    have hsquare := pow_le_pow_left₀ hnonneg hsteps 2
    rw [mul_pow, sq_abs, Real.sq_sqrt h93δ.le] at hsquare
    exact hsquare
  have hmul : δ * (t ^ 2 * (93 / δ)) = 93 * t ^ 2 := by
    field_simp
  have hδM : 93 * t ^ 2 ≤ δ * M ^ 2 := by
    have hmul' : δ * (t ^ 2 * (93 / δ)) ≤ δ * M ^ 2 :=
      mul_le_mul_of_nonneg_left hsquares hδ.le
    linarith [hmul, hmul']
  rw [div_le_iff₀ (by positivity : (0:ℝ) < M ^ 2)]
  linarith [hδM]

end Qatlib.Papers.ContDiscWalk08.SineReadout
