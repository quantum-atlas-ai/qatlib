/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HHLManyBody22.HhlCost

open Matrix

def log2 (N : ℕ) : ℝ := Real.log (N : ℝ) / Real.log 2

def conditionNumber (lamMax lamMin : ℝ) : ℝ := lamMax / lamMin

def adaptHHLComplexity (N : ℕ) (s kappa dmin eps : ℝ) : ℝ :=
  (log2 N) ^ 2 * s ^ 2 * (kappa * dmin) / eps ^ 2

def hhlComplexity (N : ℕ) (s kappa eps : ℝ) : ℝ :=
  (log2 N) ^ 2 * s ^ 2 * kappa ^ 2 / eps

theorem log2_pos {N : ℕ} (hN : 1 < N) : 0 < log2 N := by
  unfold log2
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast hN)
  · exact Real.log_pos (by norm_num)

theorem adaptHHLComplexity_eq_lambdaMax_form (N : ℕ) (s lamMax lamMin eps : ℝ)
    (hlamMin : lamMin ≠ 0) :
    adaptHHLComplexity N s (conditionNumber lamMax lamMin) lamMin eps =
      (log2 N) ^ 2 * s ^ 2 * lamMax / eps ^ 2 := by
  unfold adaptHHLComplexity conditionNumber
  congr 2
  field_simp

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

theorem subKappa_coefficient (kappa dmin : ℝ) (hkappa : 0 < kappa)
    (hd1 : dmin < 1) : kappa * dmin < kappa := by
  have := mul_lt_mul_of_pos_left hd1 hkappa
  simpa using this

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

def RayleighLowerBound (A : Matrix N N ℂ) (l : ℝ) : Prop :=
  ∀ x : N → ℂ, l * (∑ i, ‖x i‖ ^ 2) ≤ RCLike.re (star x ⬝ᵥ (A *ᵥ x))

def RayleighUpperBound (A : Matrix N N ℂ) (u : ℝ) : Prop :=
  ∀ x : N → ℂ, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤ u * (∑ i, ‖x i‖ ^ 2)

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

theorem sum_normSq_basis (i : N) :
    (∑ j, ‖(Pi.single i (1 : ℂ) : N → ℂ) j‖ ^ 2) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem rayleighLowerBound_le_diag {A : Matrix N N ℂ} {l : ℝ}
    (h : RayleighLowerBound A l) (i : N) : l ≤ RCLike.re (A i i) := by
  have hb := h (Pi.single i (1 : ℂ))
  rw [sum_normSq_basis, mul_one, dotProduct_mulVec_basis] at hb
  exact hb

theorem diag_le_rayleighUpperBound {A : Matrix N N ℂ} {u : ℝ}
    (h : RayleighUpperBound A u) (i : N) : RCLike.re (A i i) ≤ u := by
  have hb := h (Pi.single i (1 : ℂ))
  rw [sum_normSq_basis, mul_one, dotProduct_mulVec_basis] at hb
  exact hb

theorem rayleighLowerBound_le_diagMin {A : Matrix N N ℂ} {l dmin : ℝ} {i0 : N}
    (h : RayleighLowerBound A l) (hatt : dmin = RCLike.re (A i0 i0))
    : l ≤ dmin := by
  rw [hatt]
  exact rayleighLowerBound_le_diag h i0

theorem diagMax_le_rayleighUpperBound {A : Matrix N N ℂ} {u dmax : ℝ} {i0 : N}
    (h : RayleighUpperBound A u) (hatt : dmax = RCLike.re (A i0 i0))
    : dmax ≤ u := by
  rw [hatt]
  exact diag_le_rayleighUpperBound h i0

end Qatlib.Papers.HHLManyBody22.HhlCost
