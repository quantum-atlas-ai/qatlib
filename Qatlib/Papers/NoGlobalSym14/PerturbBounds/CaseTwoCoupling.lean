/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact case-two coupling identities

The case-two perturbative reduction of [JanmarkMeyerWong2014] couples the
marked vertex with the nonneighbor cell through the vector
`c = C · ((k - λ + μ) / √k, 0, 1)`. This module proves the exact algebraic
content behind that coupling: the Euclidean norm of the unnormalized vector,
the normalization constant, the exact shift identity used to rewrite
`k - λ + μ` in terms of the graph parameters alone, and the closed form of the
normalization in natural graph parameters.

All norms are the true Euclidean norm on `EuclideanSpace ℂ (Fin 3)`. The
asymptotic approximations `C ≈ (1 + (μN)²/k³)⁻¹ᐟ² ≈ k^{3/2}/(μN)` of
[JanmarkMeyerWong2014], Eq. (9), are error-control statements and remain outside
this exact finite module.

## Main statements

* `couplingVec_norm`: the Euclidean norm of the unnormalized coupling vector.
* `case2_coupling_unit`: the positive normalization constant and the unit-norm
  coupling vector.
* `shifted_coupling_identity`: the exact identity
  `k - λ + μ = (N - k - 1) * μ / k + μ + 1`.
* `case2_normalization_closed_form`: the normalization in terms of `N, k, μ`.

## References

* [Janmark et al., 2014][JanmarkMeyerWong2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoGlobalSym14.PerturbBounds

/-- The unnormalized case-two coupling vector `((k - λ + μ) / √k, 0, 1)` with
coupling parameter `a` in place of `k - λ + μ` and positive cell parameter `k`. -/
noncomputable def couplingVec (a k : ℝ) : Fin 3 → ℂ :=
  ![a / Real.sqrt k, 0, 1]

/-- The Euclidean norm of the unnormalized coupling vector is `√(1 + a² / k)`
for positive `k`. -/
theorem couplingVec_norm (a : ℝ) {k : ℝ} (hk : 0 < k) :
    ‖(WithLp.toLp 2 (couplingVec a k) : EuclideanSpace ℂ (Fin 3))‖
      = Real.sqrt (1 + a ^ 2 / k) := by
  have hk0 : Real.sqrt k ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hk)
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  have hsq : Real.sqrt (1 + a ^ 2 / k) ^ 2 = 1 + a ^ 2 / k :=
    Real.sq_sqrt (by positivity)
  rw [hsq]
  simp [Fin.sum_univ_succ, couplingVec, Matrix.cons_val_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt hk.le, sq_abs]
  field_simp
  ring

/-- The normalization constant `1 / √(1 + a² / k)` of the coupling vector is
positive for positive `k`. -/
theorem couplingNormalization_pos (a : ℝ) {k : ℝ} (hk : 0 < k) :
    0 < 1 / Real.sqrt (1 + a ^ 2 / k) := by
  positivity

/-- The case-two coupling vector with its normalization constant is a unit
vector in `EuclideanSpace ℂ (Fin 3)`. The explicit normalization constant is
the factor in the vector displayed immediately before
[JanmarkMeyerWong2014], Eq. (8). -/
theorem case2_coupling_unit (a : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧
      ‖(C : ℂ) • (WithLp.toLp 2 (couplingVec a k) : EuclideanSpace ℂ (Fin 3))‖ = 1 ∧
      C = 1 / Real.sqrt (1 + a ^ 2 / k) := by
  refine ⟨1 / Real.sqrt (1 + a ^ 2 / k), couplingNormalization_pos a hk, ?_, rfl⟩
  rw [norm_smul, couplingVec_norm a hk, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (couplingNormalization_pos a hk))]
  have hs : Real.sqrt (1 + a ^ 2 / k) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

/-- The counting identity `k * (k - λ - 1) = (N - k - 1) * μ` and positive `k`
give the exact equality in [JanmarkMeyerWong2014], Eq. (8), for the real-valued
coupling combination `k - λ + μ`. -/
theorem shifted_coupling_identity {k ℓ μ N : ℝ} (hk : 0 < k)
    (h : k * (k - ℓ - 1) = (N - k - 1) * μ) :
    k - ℓ + μ = (N - k - 1) * μ / k + μ + 1 := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have h1 : k - ℓ - 1 = (N - k - 1) * μ / k := by
    rw [eq_div_iff hk0, mul_comm]
    exact h
  linarith

/-- The shift identity in natural parameters: a finite strongly regular graph
counting identity `k * (k - λ - 1) = (N - k - 1) * μ` with the non-degeneracy
guards `λ + 1 ≤ k` and `k + 1 ≤ N` yields the real identity
`k - λ + μ = (N - k - 1) * μ / k + μ + 1`. Both guards hold for every actual
strongly regular graph with positive degree. -/
theorem shifted_coupling_identity_nat {n k ℓ μ : ℕ}
    (hparam : k * (k - ℓ - 1) = (n - k - 1) * μ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ k) (hn : k + 1 ≤ n) :
    (k : ℝ) - ℓ + μ = ((n : ℝ) - k - 1) * μ / k + μ + 1 := by
  have e1 : ((k - ℓ - 1 : ℕ) : ℝ) = (k : ℝ) - ℓ - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k - ℓ), Nat.cast_sub (show ℓ ≤ k by omega)]
    norm_num
  have e2 : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - k - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub (show k ≤ n by omega)]
    norm_num
  have hcast : (k : ℝ) * ((k : ℝ) - ℓ - 1) = ((n : ℝ) - k - 1) * μ := by
    have hc := congrArg (fun x : ℕ => (x : ℝ)) hparam
    rw [Nat.cast_mul, Nat.cast_mul, e1, e2] at hc
    exact hc
  exact shifted_coupling_identity (k := (k : ℝ)) (ℓ := (ℓ : ℝ)) (μ := (μ : ℝ))
    (N := (n : ℝ)) (by exact_mod_cast hk) hcast

/-- The closed form of the case-two normalization constant in terms of the
graph parameters alone:
`C = (1 + ((N - k - 1) * μ / k + μ + 1)² / k)⁻¹ᐟ²` in the notation of
[JanmarkMeyerWong2014], obtained by substituting the exact equality in Eq. (8)
into the normalization of the displayed vector. -/
theorem case2_normalization_closed_form {n k ℓ μ : ℕ}
    (hparam : k * (k - ℓ - 1) = (n - k - 1) * μ) (hk : 0 < k)
    (hℓ : ℓ + 1 ≤ k) (hn : k + 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ‖(C : ℂ) •
          (WithLp.toLp 2 (couplingVec ((k : ℝ) - ℓ + μ) k) : EuclideanSpace ℂ (Fin 3))‖
        = 1 ∧
      C = 1 / Real.sqrt (1 + (((n : ℝ) - k - 1) * μ / k + μ + 1) ^ 2 / k) := by
  obtain ⟨C, hCpos, hCunit, hCform⟩ :=
    case2_coupling_unit ((k : ℝ) - ℓ + μ) (by exact_mod_cast hk : (0 : ℝ) < (k : ℝ))
  refine ⟨C, hCpos, hCunit, ?_⟩
  rw [hCform, shifted_coupling_identity_nat hparam hk hℓ hn]

end Qatlib.Papers.NoGlobalSym14.PerturbBounds
