/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationError

/-!
# Positive grid approximations of mixture masses

The rational approximation `gridMass` rounds each nonnegative mass upward on a grid of spacing
1/(n + 1), giving strictly positive approximate masses. Their total L1 error is at most K/(n +
1), and `gridEffective` packages this bound with a convergence modulus. These masses support
mixture sampling for the dual constructions motivated by [BrandaoSvore2017].

## Main statements

* `gridMass_error`: coordinatewise rounding error lies between zero and 1/(n + 1).
* `gridMass_l1`: the real L1 error is at most K/(n + 1).
* `gridEffective`: positive rational approximations form an effective-mass package.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Family

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib
open scoped Classical ENNReal

/-- The rational mass obtained by taking the natural floor of (n + 1) times an input mass,
adding one, and dividing by `n + 1`. -/
def gridMass {K : ℕ} (v : Fin K → ℚ) (n : ℕ) (i : Fin K) : ℚ :=
  ((Nat.floor ((n+1 : ℚ) * v i) : ℚ)+1)/(n+1 : ℚ)

/-- The integer sampling weights obtained from the positive rational grid masses by
`intWeights`. -/
def gridWeights {K : ℕ} (v : Fin K → ℚ) (n : ℕ) : Fin K → ℕ :=
  intWeights (gridMass v n)

/-- Every grid mass is strictly positive, for any rational input mass and natural grid
parameter. -/
theorem gridMass_pos {K : ℕ} (v : Fin K → ℚ) (n : ℕ) (i : Fin K) :
    0 < gridMass v n i := by
  unfold gridMass
  positivity

/-- For a nonnegative input mass, upward grid rounding has error between zero and 1/(n + 1). -/
theorem gridMass_error {K : ℕ} (v : Fin K → ℚ) (hv : ∀ i, 0 ≤ v i)
    (n : ℕ) (i : Fin K) : 0 ≤ gridMass v n i - v i ∧
      gridMass v n i - v i ≤ 1/(n+1 : ℚ) := by
  have hd : (0 : ℚ) < n+1 := by positivity
  have hlo := Nat.floor_le (mul_nonneg hd.le (hv i))
  have hhi := Nat.lt_floor_add_one ((n+1 : ℚ)*v i)
  unfold gridMass
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hd).mpr
    field_simp
    nlinarith

/-- For `K` nonnegative rational masses, the sum of absolute real errors of their grid
approximations is at most K/(n + 1). -/
theorem gridMass_l1 {K : ℕ} (v : Fin K → ℚ) (hv : ∀ i, 0 ≤ v i) (n : ℕ) :
    (∑ i, |(gridMass v n i : ℝ)-(v i : ℝ)|) ≤ (K : ℝ)/(n+1) := by
  calc
    _ ≤ ∑ _i : Fin K, (1 : ℝ)/(n+1) := by
      apply Finset.sum_le_sum
      intro i _
      have h := gridMass_error v hv n i
      have hlo : (0 : ℝ) ≤ (gridMass v n i : ℝ)-(v i : ℝ) := by exact_mod_cast h.1
      rw [abs_of_nonneg hlo]
      have hh : ((gridMass v n i - v i : ℚ) : ℝ) ≤ ((1/(n+1 : ℚ) : ℚ) : ℝ) :=
        Rat.cast_le.mpr h.2
      simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast] using hh
    _ = _ := by simp [div_eq_mul_inv]

/-- The effective-mass package for nonnegative rational masses of positive total, using positive
grid approximations with error K/(n + 1) and modulus K(k + 1). -/
noncomputable def gridEffective {K : ℕ} (v : Fin K → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hS : 0 < ∑ i, (v i : ℝ)) : EffectiveMasses K where
  value := fun i => (v i : ℝ)
  value_nonneg := fun i => by exact_mod_cast hv i
  approximate := gridMass v
  nonneg := fun n i => (gridMass_pos v n i).le
  positive := by
    intro n
    have hK : 0 < K := by
      by_contra h
      have : K=0 := by omega
      subst K
      simp at hS
    exact Finset.sum_pos (fun i _ => by exact_mod_cast gridMass_pos v n i)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hK⟩⟩)
  total_pos := hS
  error := fun n => (K : ℝ)/(n+1)
  accuracy := gridMass_l1 v hv
  modulus := fun k => K*(k+1)
  error_at_modulus := by
    intro k
    have hd : (0 : ℝ) < (K*(k+1) : ℕ)+1 := by positivity
    have hk : (0 : ℝ) < (k : ℝ)+1 := by positivity
    apply (div_le_div_iff₀ hd hk).mpr
    push_cast
    nlinarith

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
