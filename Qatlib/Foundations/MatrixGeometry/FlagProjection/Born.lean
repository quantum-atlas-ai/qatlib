/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.FlagProjection.Word

/-!
# Conditional Born laws for flagged states

`conditionalBorn` divides each flagged squared amplitude by the total flagged mass and vanishes
outside the flag set. The module computes the Born law of `tail` and proves that any vector in
the source-tail span with positive flagged mass has the same conditional law as the source.

The results apply to the repeated reflection words `run` and `runFig`; their sign difference
changes neither flagged mass nor the resulting conditional law. This gives the finite-state
measurement identities associated with [PaparoEtAl2014].

## Main statements

* `span_conditional`: source-tail span states preserve the flagged conditional law when the
  relevant masses are positive.
* `run_conditional`: the repeated reflection word preserves that conditional law.
* `figure_mass`: the two sign conventions have equal flagged mass.

## References

* [Paparo et al., 2014][PaparoEtAl2014]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.FlagProjection
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The squared amplitude at `x` divided by the total flagged mass when `x ∈ S`, and zero
otherwise. -/
def conditionalBorn (S : Finset X) (v : EuclideanSpace ℂ X) (x : X) : ℝ :=
  if x ∈ S then ‖v.ofLp x‖^2 / mass S v else 0

/-- For positive flagged mass, the normalized projected tail has squared Hilbert norm one. -/
theorem tail_norm_sq (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) :
    ‖tail S v‖^2 = 1 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), tail_unit S v hp]
  norm_num

/-- For positive source flagged mass, the flagged mass of `a • v + b • tail S v` is `‖a * sqrt
(mass S v) + b‖^2`. -/
theorem mass_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    mass S (a • v + b • tail S v) = ‖a * (Real.sqrt (mass S v) : ℂ) + b‖^2 := by
  rw [← project_norm_sq, project_span S v hp, norm_smul, mul_pow, tail_norm_sq S v hp, mul_one]

omit [Fintype X] in

/-- For positive source flagged mass, the squared amplitudes of the normalized tail equal the
source's conditional Born values. -/
theorem tail_born (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v) (x : X) :
    ‖(tail S v).ofLp x‖^2 = conditionalBorn S v x := by
  by_cases hx : x ∈ S
  · simp only [tail, project, conditionalBorn, PiLp.smul_apply, if_pos hx]
    change ‖(Real.sqrt (mass S v) : ℂ)⁻¹ * v.ofLp x‖^2 =
      ‖v.ofLp x‖^2 / mass S v
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hp.le, div_eq_mul_inv,
      mul_comm]
  · simp [tail, project, conditionalBorn, hx]

/-- If both the source and its source-tail span vector have positive flagged mass, their flagged
conditional Born laws agree. This is the span-state measurement identity used in
[PaparoEtAl2014]. -/
theorem span_conditional (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) (houtput : 0 < mass S (a • v + b • tail S v)) :
    conditionalBorn S (a • v + b • tail S v) = conditionalBorn S v := by
  have hc : ‖a * (Real.sqrt (mass S v) : ℂ) + b‖^2 ≠ 0 := by
    rw [mass_span S v hp] at houtput
    exact ne_of_gt houtput
  funext x
  by_cases hx : x ∈ S
  · have hcoord := congrArg (fun q : EuclideanSpace ℂ X => q.ofLp x) (project_span S v hp a b)
    change (if x ∈ S then (a • v + b • tail S v).ofLp x else 0) =
      (a * (Real.sqrt (mass S v) : ℂ) + b) * (tail S v).ofLp x at hcoord
    rw [if_pos hx] at hcoord
    rw [conditionalBorn, if_pos hx, hcoord, norm_mul, mul_pow, mass_span S v hp]
    rw [mul_div_cancel_left₀ _ hc, tail_born S v hp]
  · simp [conditionalBorn, hx]

omit [Fintype X] [DecidableEq X] in

/-- Scaling a state by `c` multiplies its flagged mass by `‖c‖^2`. -/
theorem mass_smul (S : Finset X) (v : EuclideanSpace ℂ X) (c : ℂ) :
    mass S (c • v) = ‖c‖^2 * mass S v := by
  simp [mass, mul_pow, Finset.mul_sum]

omit [Fintype X] in

/-- Multiplication by a nonzero complex scalar leaves the conditional Born function unchanged. -/
theorem conditional_smul (S : Finset X) (v : EuclideanSpace ℂ X) (c : ℂ) (hc : c ≠ 0) :
    conditionalBorn S (c • v) = conditionalBorn S v := by
  have hn : ‖c‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  funext x
  by_cases hx : x ∈ S
  · simp only [conditionalBorn, if_pos hx, mass_smul]
    change ‖c * v.ofLp x‖^2 / (‖c‖^2 * mass S v) = ‖v.ofLp x‖^2 / mass S v
    rw [norm_mul, mul_pow, mul_div_mul_left _ _ hn]
  · simp [conditionalBorn, hx]

/-- For a unit source with positive flagged mass, every repeated reflection output with positive
flagged mass has the source's conditional Born law. -/
theorem run_conditional (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (n : ℕ) (houtput : 0 < mass S (run S v n)) :
    conditionalBorn S (run S v n) = conditionalBorn S v := by
  rw [run_coeff S v hp hu n] at houtput ⊢
  exact span_conditional S v hp _ _ houtput

/-- For a unit source with positive flagged mass, if `run S v n` has positive flagged mass, the
Figure 2 convention also has the source's conditional Born law. This transports the sign
convention to measurement in [PaparoEtAl2014]. -/
theorem figure_conditional (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (n : ℕ) (houtput : 0 < mass S (run S v n)) :
    conditionalBorn S (runFig S v n) = conditionalBorn S v := by
  rw [runFig_phase, conditional_smul S _ _ (pow_ne_zero _ (by norm_num)),
    run_conditional S v hp hu n houtput]

/-- The two repeated reflection sign conventions have equal flagged mass at every iteration, as
used in the measurement comparison for [PaparoEtAl2014]. -/
theorem figure_mass (S : Finset X) (v : EuclideanSpace ℂ X) (n : ℕ) :
    mass S (runFig S v n) = mass S (run S v n) := by
  rw [runFig_phase, mass_smul]
  simp
end Qatlib.Foundations.MatrixGeometry.FlagProjection
