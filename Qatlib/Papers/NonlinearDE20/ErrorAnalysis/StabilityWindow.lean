/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A restricted Euclidean stability window

The advantage discussion of [LloydEtAl2020] is restricted to time intervals on which mean-field
and discretization errors do not undergo strong Lyapunov amplification.  This module records two
small but genuine parts of that restriction for finite Euclidean systems.

First, if every (possibly time-dependent) forward-Euler propagator is a uniform `q`-contraction in
the Hilbert-space operator norm, with `q < 1`, then two trajectories separate by at most `qᵏ`
times their initial Euclidean separation after `k` steps.  The constant in the uniform statement
is `1` and is chosen before all dimensions, contractions, propagators, states and times.

Second, the real diagonal generator with entries `2` and `-3` has trace `-1` and `L2` operator
norm `3`. Its unit-step forward-Euler orbit also grows by `3ᵏ` along the positive eigendirection.
The estimates concern discrete linear trajectories and their initial perturbations.

## Main statements

* `contractive_linear_euler_stability`: the uniform Euclidean error-contractivity estimate on a
  nonempty finite-dimensional Euler trajectory.
* `negative_trace_expansion_counterexample`: negative trace and genuine operator-norm expansion
  coexist in dimension two.
* `negative_trace_euler_orbit_expands`: the same generator has an exponentially growing
  forward-Euler orbit.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Stability

/-- The state at step `k` obtained by applying the time-dependent propagators in order. -/
def stepOrbit {d : ℕ}
    (S : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  match k with
  | 0 => x
  | k + 1 => S k (stepOrbit S k x)

/-- Every time-dependent forward-Euler propagator is a contraction of modulus at most `q < 1`
in the Euclidean operator norm.  Then two orbits separate by the decaying factor `qᵏ`; the
constant `1` is fixed uniformly before dimension, time, propagators and states. -/
theorem contractive_linear_euler_stability :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 0 < d → ∀ q : ℝ, 0 < q → q < 1 →
        ∀ S : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
          (∀ k, ‖S k‖ ≤ q) →
          ∀ (x y : EuclideanSpace ℝ (Fin d)) (k : ℕ),
            ‖stepOrbit S k x - stepOrbit S k y‖ ≤ C * q ^ k * ‖x - y‖ := by
  refine ⟨1, zero_lt_one, fun d _hd q hq0 hq1 S hS x y k => ?_⟩
  induction k generalizing x y with
  | zero => simp [stepOrbit]
  | succ n ih =>
    have hone : (1 : ℝ) * q ^ (n + 1) * ‖x - y‖ =
        q * ((1 : ℝ) * q ^ n * ‖x - y‖) := by ring
    calc ‖stepOrbit S (n + 1) x - stepOrbit S (n + 1) y‖
        = ‖S n (stepOrbit S n x) - S n (stepOrbit S n y)‖ := rfl
      _ ≤ ‖S n‖ * ‖stepOrbit S n x - stepOrbit S n y‖ := by
          have hmap : (S n) (stepOrbit S n x) - (S n) (stepOrbit S n y) =
              (S n) (stepOrbit S n x - stepOrbit S n y) := (map_sub _ _ _).symm
          rw [hmap]
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ q * ((1 : ℝ) * q ^ n * ‖x - y‖) := by
          refine le_trans (mul_le_mul_of_nonneg_right (hS n) (norm_nonneg _)) ?_
          exact mul_le_mul_of_nonneg_left (ih x y) (le_of_lt hq0)
      _ = (1 : ℝ) * q ^ (n + 1) * ‖x - y‖ := hone.symm

/-- The diagonal two-dimensional matrix with entries `2` and `-3`.  Its trace is negative, but
one direction expands under the Euclidean operator norm. -/
def negativeTraceExpandingMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![2, -3]

/-- The diagonal generator has negative trace, yet its matrix action has `L2` operator norm
`3`, attained on the second coordinate. -/
theorem negative_trace_expansion_counterexample :
    negativeTraceExpandingMatrix.trace < 0 ∧
      2 < ‖negativeTraceExpandingMatrix‖ ∧
      ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
        ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            negativeTraceExpandingMatrix) v‖ = 3 * ‖v‖ := by
  have htrace : negativeTraceExpandingMatrix.trace = -1 := by
    rw [negativeTraceExpandingMatrix, Matrix.trace_fin_two]
    simp only [Matrix.diagonal_apply]
    norm_num
  have hnorm : ‖negativeTraceExpandingMatrix‖ = 3 := by
    rw [negativeTraceExpandingMatrix, Matrix.l2_opNorm_diagonal]
    have hupper :
        (Finset.univ.sup fun b => ‖(![2, -3] : Fin 2 → ℝ) b‖₊) ≤ 3 := by
      refine Finset.sup_le fun i _ => ?_
      fin_cases i <;> norm_num
    have hval : (‖(![2, -3] : Fin 2 → ℝ) (1 : Fin 2)‖₊) = 3 := by norm_num
    have hlower :
        (3 : NNReal) ≤
          (Finset.univ.sup fun b => ‖(![2, -3] : Fin 2 → ℝ) b‖₊) := by
      rw [← hval]
      exact Finset.le_sup
        (f := fun b => ‖(![2, -3] : Fin 2 → ℝ) b‖₊) (Finset.mem_univ (1 : Fin 2))
    rw [Pi.norm_def]
    exact_mod_cast le_antisymm hupper hlower
  refine ⟨by rw [htrace]; norm_num, by rw [hnorm]; norm_num, ?_⟩
  refine ⟨WithLp.toLp 2 ![0, 1], ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) h
    have hunit : ‖(WithLp.toLp 2 (![0, 1] : Fin 2 → ℝ))‖ = 1 := by
      simp [EuclideanSpace.norm_eq, Real.norm_eq_abs]
    rw [hunit] at h1
    simp at h1
  · simp [negativeTraceExpandingMatrix, Matrix.toEuclideanCLM_toLp,
      Matrix.mulVec_diagonal, EuclideanSpace.norm_eq, Real.norm_eq_abs]

/-- For the system with this negative-trace generator, unit-step forward Euler acts by `I + A`.
The orbit of the first coordinate unit vector has Euclidean norm `3ᵏ` after `k` steps. -/
theorem negative_trace_euler_orbit_expands :
    negativeTraceExpandingMatrix.trace < 0 ∧
      ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧ ∀ k : ℕ,
        ‖stepOrbit
          (fun _ => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            (1 + negativeTraceExpandingMatrix)) k v‖ = (3 : ℝ) ^ k := by
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
  have hv : ‖v‖ = 1 := by
    simp [v, EuclideanSpace.norm_eq, Real.norm_eq_abs]
  have hstep : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (1 + negativeTraceExpandingMatrix) v = (3 : ℝ) • v := by
    change Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (1 + negativeTraceExpandingMatrix) (WithLp.toLp 2 ![1, 0]) =
        WithLp.toLp 2 ((3 : ℝ) • (![1, 0] : Fin 2 → ℝ))
    rw [Matrix.toEuclideanCLM_toLp]
    congr 1
    funext i
    fin_cases i <;> norm_num [negativeTraceExpandingMatrix, Matrix.add_mulVec,
      Matrix.mulVec_diagonal, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have horbit (k : ℕ) :
      stepOrbit (fun _ => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (1 + negativeTraceExpandingMatrix)) k v = (3 : ℝ) ^ k • v := by
    induction k with
    | zero => simp [stepOrbit]
    | succ k ih => rw [stepOrbit, ih, map_smul, hstep, smul_smul, pow_succ]
  refine ⟨negative_trace_expansion_counterexample.1, v, hv, fun k => ?_⟩
  rw [horbit, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hv, mul_one]

end Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Stability
