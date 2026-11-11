/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.Sqrt

/-!
# Scalar HHL cost expressions and diagonal bounds

The module defines scalar expressions for the reported HHL and AdaptHHL costs and proves their
algebraic dependence on the condition number, diagonal scale, and precision. In particular,
substituting the true minimum spectral scale yields the maximum eigenvalue form, whereas a
larger diagonal scale gives an inequality in the opposite direction.

`RayleighLowerBound` and `RayleighUpperBound` encode quadratic form bounds. Evaluating them on
basis vectors bounds every real diagonal entry, as well as any designated attained diagonal
value. See [BaskaranEtAl2023].

## Main statements

* `adaptHHLComplexity_eq_lambdaMax_form`: If `lamMin ≠ 0` and `dmin = lamMin`, substituting
  `conditionNumber lamMax lamMin` reduces the AdaptHHL cost expression to `(log2 N)^2 * s^2 *
  lamMax / eps^2`.
* `adaptHHLComplexity_ge_lambdaMax_form`: If `lamMin > 0`, `lamMax ≥ 0`, `lamMin ≤ dmin`, and
  `eps ≠ 0`, the maximum eigenvalue cost expression is at most the AdaptHHL expression with that
  diagonal scale.
* `rayleighLowerBound_le_diag`: A Rayleigh lower bound for `A` is at most the real part of each
  diagonal entry.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HHLManyBody22.HhlCost

open Matrix

/-- The real base two logarithm `log N / log 2`. -/
def log2 (N : ℕ) : ℝ := Real.log (N : ℝ) / Real.log 2

/-- The ratio `lamMax / lamMin`. -/
def conditionNumber (lamMax lamMin : ℝ) : ℝ := lamMax / lamMin

/-- The scalar AdaptHHL cost expression `(log2 N)^2 * s^2 * (kappa*dmin) / eps^2`. -/
def adaptHHLComplexity (N : ℕ) (s kappa dmin eps : ℝ) : ℝ :=
  (log2 N) ^ 2 * s ^ 2 * (kappa * dmin) / eps ^ 2

/-- The scalar HHL cost expression `(log2 N)^2 * s^2 * kappa^2 / eps`. -/
def hhlComplexity (N : ℕ) (s kappa eps : ℝ) : ℝ :=
  (log2 N) ^ 2 * s ^ 2 * kappa ^ 2 / eps

/-- For `N > 1`, `log2 N` is positive. -/
theorem log2_pos {N : ℕ} (hN : 1 < N) : 0 < log2 N := by
  unfold log2
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast hN)
  · exact Real.log_pos (by norm_num)

/-- If `lamMin ≠ 0` and `dmin = lamMin`, substituting `conditionNumber lamMax lamMin` reduces
the AdaptHHL cost expression to `(log2 N)^2 * s^2 * lamMax / eps^2`. See [BaskaranEtAl2023]. -/
theorem adaptHHLComplexity_eq_lambdaMax_form (N : ℕ) (s lamMax lamMin eps : ℝ)
    (hlamMin : lamMin ≠ 0) :
    adaptHHLComplexity N s (conditionNumber lamMax lamMin) lamMin eps =
      (log2 N) ^ 2 * s ^ 2 * lamMax / eps ^ 2 := by
  unfold adaptHHLComplexity conditionNumber
  congr 2
  field_simp

/-- For nonnegative `kappa` and nonzero precision, the AdaptHHL cost expression is monotone in
`dmin`. -/
theorem adaptHHLComplexity_mono_dmin (N : ℕ) (s kappa dmin dmin' eps : ℝ)
    (hkappa : 0 ≤ kappa) (hd : dmin ≤ dmin') (heps : eps ≠ 0) :
    adaptHHLComplexity N s kappa dmin eps ≤ adaptHHLComplexity N s kappa dmin' eps := by
  unfold adaptHHLComplexity
  have hfac : 0 ≤ (log2 N) ^ 2 * s ^ 2 / eps ^ 2 := by positivity
  calc (log2 N) ^ 2 * s ^ 2 * (kappa * dmin) / eps ^ 2
      = ((log2 N) ^ 2 * s ^ 2 / eps ^ 2) * (kappa * dmin) := by
        field_simp
    _ ≤ ((log2 N) ^ 2 * s ^ 2 / eps ^ 2) * (kappa * dmin') := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hkappa) hfac
    _ = (log2 N) ^ 2 * s ^ 2 * (kappa * dmin') / eps ^ 2 := by
        field_simp

/-- If `lamMin > 0`, `lamMax ≥ 0`, `lamMin ≤ dmin`, and `eps ≠ 0`, the maximum eigenvalue cost
expression is at most the AdaptHHL expression with that diagonal scale. -/
theorem adaptHHLComplexity_ge_lambdaMax_form (N : ℕ) (s lamMax lamMin dmin eps : ℝ)
    (hlamMin : 0 < lamMin) (hlamMax : 0 ≤ lamMax) (hd : lamMin ≤ dmin) (heps : eps ≠ 0) :
    (log2 N) ^ 2 * s ^ 2 * lamMax / eps ^ 2 ≤
      adaptHHLComplexity N s (conditionNumber lamMax lamMin) dmin eps := by
  have hkappa : 0 ≤ conditionNumber lamMax lamMin := by
    unfold conditionNumber
    exact div_nonneg hlamMax hlamMin.le
  have hmono := adaptHHLComplexity_mono_dmin N s (conditionNumber lamMax lamMin)
    lamMin dmin eps hkappa hd heps
  have heq := adaptHHLComplexity_eq_lambdaMax_form N s lamMax lamMin eps hlamMin.ne'
  rw [heq] at hmono
  exact hmono

/-- For positive `kappa` and `dmin < 1`, `kappa*dmin < kappa`. -/
theorem subKappa_coefficient (kappa dmin : ℝ) (hkappa : 0 < kappa)
    (hd1 : dmin < 1) : kappa * dmin < kappa := by
  have := mul_lt_mul_of_pos_left hd1 hkappa
  simpa using this

/-- If `N > 1`, `s` and `eps` are nonzero, `kappa > 0`, and `dmin < 1`, the AdaptHHL expression
is strictly smaller than its value at `dmin = 1`. -/
theorem adaptHHLComplexity_lt_of_subKappa (N : ℕ) (s kappa dmin eps : ℝ)
    (hN : 1 < N) (hs : s ≠ 0) (heps : eps ≠ 0) (hkappa : 0 < kappa)
    (hd1 : dmin < 1) :
    adaptHHLComplexity N s kappa dmin eps < adaptHHLComplexity N s kappa 1 eps := by
  unfold adaptHHLComplexity
  have hfac : 0 < (log2 N) ^ 2 * s ^ 2 / eps ^ 2 := by
    have hlog := log2_pos hN
    have hs2 : 0 < s ^ 2 := by positivity
    have heps2 : 0 < eps ^ 2 := by positivity
    positivity
  have hcoef := subKappa_coefficient kappa dmin hkappa hd1
  have h1 : (log2 N) ^ 2 * s ^ 2 * (kappa * dmin) / eps ^ 2
      = ((log2 N) ^ 2 * s ^ 2 / eps ^ 2) * (kappa * dmin) := by
    field_simp
  have h2 : (log2 N) ^ 2 * s ^ 2 * (kappa * 1) / eps ^ 2
      = ((log2 N) ^ 2 * s ^ 2 / eps ^ 2) * (kappa * 1) := by
    field_simp
  rw [h1, h2]
  simpa using mul_lt_mul_of_pos_left hcoef hfac

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The property that the real quadratic form of `A` is at least `l` times the squared vector
norm for every vector. -/
def RayleighLowerBound (A : Matrix N N ℂ) (l : ℝ) : Prop :=
  ∀ x : N → ℂ, l * (∑ i, ‖x i‖ ^ 2) ≤ RCLike.re (star x ⬝ᵥ (A *ᵥ x))

/-- The property that the real quadratic form of `A` is at most `u` times the squared vector
norm for every vector. -/
def RayleighUpperBound (A : Matrix N N ℂ) (u : ℝ) : Prop :=
  ∀ x : N → ℂ, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ u * (∑ i, ‖x i‖ ^ 2)

/-- The quadratic form of `A` at the `i`th standard basis vector equals `A i i`. -/
theorem dotProduct_mulVec_basis (A : Matrix N N ℂ) (i : N) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ (A *ᵥ Pi.single i (1 : ℂ)) = A i i := by
  rw [Matrix.mulVec_single_one]
  have hstar : star (Pi.single i (1 : ℂ) : N → ℂ) = (Pi.single i (1 : ℂ) : N → ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [hstar]
  simp

/-- The sum of squared norms of the entries of a standard basis vector is one. -/
theorem sum_normSq_basis (i : N) :
    (∑ j, ‖(Pi.single i (1 : ℂ) : N → ℂ) j‖ ^ 2) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A Rayleigh lower bound for `A` is at most the real part of each diagonal entry. -/
theorem rayleighLowerBound_le_diag {A : Matrix N N ℂ} {l : ℝ}
    (h : RayleighLowerBound A l) (i : N) : l ≤ RCLike.re (A i i) := by
  have hb := h (Pi.single i (1 : ℂ))
  rw [sum_normSq_basis, mul_one, dotProduct_mulVec_basis] at hb
  exact hb

/-- The real part of each diagonal entry is at most a Rayleigh upper bound for `A`. -/
theorem diag_le_rayleighUpperBound {A : Matrix N N ℂ} {u : ℝ}
    (h : RayleighUpperBound A u) (i : N) : RCLike.re (A i i) ≤ u := by
  have hb := h (Pi.single i (1 : ℂ))
  rw [sum_normSq_basis, mul_one, dotProduct_mulVec_basis] at hb
  exact hb

/-- A Rayleigh lower bound is at most any specified real diagonal value attained at `i0`. -/
theorem rayleighLowerBound_le_diagMin {A : Matrix N N ℂ} {l dmin : ℝ} {i0 : N}
    (h : RayleighLowerBound A l) (hatt : dmin = RCLike.re (A i0 i0))
    : l ≤ dmin := by
  rw [hatt]
  exact rayleighLowerBound_le_diag h i0

/-- Any specified real diagonal value attained at `i0` is at most a Rayleigh upper bound. -/
theorem diagMax_le_rayleighUpperBound {A : Matrix N N ℂ} {u dmax : ℝ} {i0 : N}
    (h : RayleighUpperBound A u) (hatt : dmax = RCLike.re (A i0 i0))
    : dmax ≤ u := by
  rw [hatt]
  exact diag_le_rayleighUpperBound h i0

end Qatlib.Papers.HHLManyBody22.HhlCost
