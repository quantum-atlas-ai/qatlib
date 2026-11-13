/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.Jacobi
import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore

/-!
# Symmetry and special values of Jacobi sums

This module proves the symmetry of `jacobiSum` and evaluates the cases involving trivial or
inverse multiplicative characters. The change of variables in `sum_reflect` exchanges the two
character factors. See [VanDamSeroussi2002].

## Main statements

* `jacobiSum_symm`: The Jacobi sum is symmetric in its two multiplicative characters.
* `jacobiSum_trivial_left`: The Jacobi sum of the trivial character and a nontrivial character
  is `-1`.
* `jacobiSum_self_inv`: The Jacobi sum of a nontrivial character and its pointwise inverse is
  minus the character value at `-1`.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.JacobiPhase

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- The multiplicative character obtained by taking the pointwise complex inverse of `ψ`. -/
def invMultChar {K : Type*} [Field K] (ψ : MultChar K) : MultChar K where
  toFun x := (ψ.toFun x)⁻¹
  map_zero' := by simp [ψ.map_zero']
  map_one' := by simp [ψ.map_one']
  map_mul' x y := by rw [ψ.map_mul', mul_inv]
  norm_eq_one x hx := by rw [norm_inv, ψ.norm_eq_one x hx, inv_one]

/-- Summation over a finite field is invariant under the substitution `x ↦ 1 - x`. -/
theorem sum_reflect {K : Type*} [Field K] [Fintype K] (f : K → ℂ) :
    (∑ x : K, f (1 - x)) = ∑ y : K, f y := by
  refine Finset.sum_bij (i := fun a _ => (1 - a : K)) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a₁ _ a₂ _ h
    linear_combination -h
  · intro b _; exact ⟨1 - b, Finset.mem_univ _, by ring⟩
  · intro a _; rfl

/-- The Jacobi sum is symmetric in its two multiplicative characters [VanDamSeroussi2002]. -/
theorem jacobiSum_symm {K : Type*} [Field K] [Fintype K] (χ ψ : MultChar K) :
    jacobiSum χ ψ = jacobiSum ψ χ := by
  rw [jacobiSum, jacobiSum]
  have hcomp : (∑ x : K, χ.toFun (1 - x) * ψ.toFun x)
      = ∑ y : K, χ.toFun y * ψ.toFun (1 - y) := by
    refine Finset.sum_bij (i := fun a _ => (1 - a : K)) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro a₁ _ a₂ _ h
      linear_combination -h
    · intro b _; exact ⟨1 - b, Finset.mem_univ _, by ring⟩
    · intro a _
      congr 1
      ring
  calc (∑ x : K, χ.toFun x * ψ.toFun (1 - x))
      = ∑ x : K, χ.toFun (1 - x) * ψ.toFun x := hcomp.symm
    _ = ∑ x : K, ψ.toFun x * χ.toFun (1 - x) := by
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The Jacobi sum of two trivial characters is the complex cast of the field cardinality minus
two, with subtraction performed in `ℕ` [VanDamSeroussi2002]. -/
theorem jacobiSum_trivial_trivial {K : Type*} [Field K] [Fintype K] :
    jacobiSum (trivialMultChar K) (trivialMultChar K)
      = ((Fintype.card K - 2 : ℕ) : ℂ) := by
  classical
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  rw [jacobiSum]
  have hpt : ∀ x : K,
      (trivialMultChar K).toFun x * (trivialMultChar K).toFun (1 - x)
        = 1 - (if x = 0 then (1 : ℂ) else 0) - (if x = 1 then (1 : ℂ) else 0) := by
    intro x
    by_cases hx0 : x = 0
    · subst hx0
      simp [trivialMultChar]
    · by_cases hx1 : x = 1
      · subst hx1
        simp [trivialMultChar]
      · have h1x : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
        simp [trivialMultChar, hx0, hx1, h1x]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ (0 : K)),
    Finset.sum_ite_eq', if_pos (Finset.mem_univ (1 : K))]
  have hcast : ((Fintype.card K : ℕ) : ℂ) - 1 - 1
      = ((Fintype.card K - 2 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hcard]
    push_cast
    ring
  rw [hcast]

/-- The Jacobi sum of the trivial character and a nontrivial character is `-1`
[VanDamSeroussi2002]. -/
theorem jacobiSum_trivial_left {K : Type*} [Field K] [Fintype K] (ψ : MultChar K)
    (hψ : ψ.IsNontrivial) :
    jacobiSum (trivialMultChar K) ψ = -1 := by
  classical
  rw [jacobiSum]
  have hpt : ∀ x : K,
      (trivialMultChar K).toFun x * ψ.toFun (1 - x)
        = ψ.toFun (1 - x) - (if x = 0 then ψ.toFun 1 else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp [trivialMultChar]
    · simp [trivialMultChar, hx]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ (0 : K)),
    ψ.map_one', sum_reflect, multChar_sum_eq_zero ψ hψ]
  ring

/-- The Jacobi sum of a nontrivial character and its pointwise inverse is minus the character
value at `-1` [VanDamSeroussi2002]. -/
theorem jacobiSum_self_inv {K : Type*} [Field K] [Fintype K] (ψ : MultChar K)
    (hψ : ψ.IsNontrivial) :
    jacobiSum ψ (invMultChar ψ) = -ψ.toFun (-1) := by
  classical
  rw [jacobiSum]
  set s : Finset K := (Finset.univ.erase (0 : K)).erase (1 : K) with hs
  set t : Finset K := (Finset.univ.erase (0 : K)).erase (-1 : K) with ht
  have hbij1 : (∑ x ∈ s, ψ.toFun (x / (1 - x))) = ∑ y ∈ t, ψ.toFun y := by
    refine Finset.sum_bij (i := fun a _ => (a / (1 - a) : K)) ?_ ?_ ?_ ?_
    · intro x hx
      have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have h1x : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
      simp only [ht, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hone
        have h : x = -(1 - x) := by
          rw [div_eq_iff h1x] at hone
          linear_combination hone
        exact one_ne_zero (by linear_combination h)
      · intro hzero
        rcases div_eq_zero_iff.mp hzero with h | h
        · exact hx0 h
        · exact h1x h
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 : x₁ ≠ 1 := (Finset.mem_erase.mp hx₁).1
      have h2 : x₂ ≠ 1 := (Finset.mem_erase.mp hx₂).1
      have hd1 : (1 : K) - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have hd2 : (1 : K) - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
      field_simp [hd1, hd2] at heq
      linear_combination heq
    · intro y hy
      have hyn1 : y ≠ -1 := (Finset.mem_erase.mp hy).1
      have hy0 : y ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
      refine ⟨y / (1 + y), ?_, ?_⟩
      · have h1y : (1 : K) + y ≠ 0 := by
          intro h
          exact hyn1 (by linear_combination h)
        have hy0' : y / (1 + y) ≠ 0 := div_ne_zero hy0 h1y
        have hy1' : y / (1 + y) ≠ 1 := by
          intro h
          have hyeq : y = 1 + y := by
            rw [div_eq_iff h1y] at h
            linear_combination h
          exact one_ne_zero (by linear_combination -hyeq)
        simp only [hs, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨hy1', hy0'⟩
      · have h1y : (1 : K) + y ≠ 0 := by
          intro h
          exact hyn1 (by linear_combination h)
        have hden : (1 : K) - y / (1 + y) ≠ 0 := by
          have heq : (1 : K) - y / (1 + y) = 1 / (1 + y) := by
            field_simp [h1y]
            ring
          rw [heq]
          exact div_ne_zero one_ne_zero h1y
        rw [div_eq_iff hden]
        field_simp [h1y]
        ring
    · intro a _; rfl
  have hterm : (∑ x ∈ s, ψ.toFun (x / (1 - x)))
      = ∑ x ∈ s, ψ.toFun x * (invMultChar ψ).toFun (1 - x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
    have h1x : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
    simp only [invMultChar]
    rw [show x / (1 - x) = x * (1 - x)⁻¹ by ring, ψ.map_mul', ψ.inv_apply h1x]
  have hdom : (∑ x : K, ψ.toFun x * (invMultChar ψ).toFun (1 - x))
      = ∑ x ∈ s, ψ.toFun x * (invMultChar ψ).toFun (1 - x) := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro x _ hx
    have hcases : x = 0 ∨ x = 1 := by
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · by_cases hx1 : x = 1
        · exact Or.inr hx1
        · exact absurd (by simp [hs, Finset.mem_erase, hx0, hx1]) hx
    rcases hcases with rfl | rfl
    · simp [ψ.map_zero']
    · simp [invMultChar, ψ.map_zero']
  rw [hdom, ← hterm, hbij1]
  have hzero : (∑ y : K, ψ.toFun y) = 0 := multChar_sum_eq_zero ψ hψ
  have hsplit : (∑ y : K, ψ.toFun y)
      = (∑ y ∈ t, ψ.toFun y) + ψ.toFun 0 + ψ.toFun (-1) := by
    have h0ne : (0 : K) ≠ -1 := by
      intro h
      have h1 : (1 : K) = 0 := by
        have hneg := congrArg Neg.neg h
        simpa using hneg.symm
      exact one_ne_zero h1
    rw [← Finset.sum_erase_add (Finset.univ : Finset K) (fun y : K => ψ.toFun y)
      (Finset.mem_univ (0 : K))]
    have h2 : (∑ y ∈ t, ψ.toFun y) + ψ.toFun (-1)
        = ∑ y ∈ Finset.univ.erase (0 : K), ψ.toFun y := by
      rw [ht]
      exact Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm h0ne, Finset.mem_univ _⟩)
    rw [← h2]
    ac_rfl
  have h3 : (∑ y ∈ t, ψ.toFun y) + ψ.toFun (-1) = 0 := by
    have h := hsplit
    rw [hzero, ψ.map_zero'] at h
    rw [add_zero] at h
    exact h.symm
  have := congrArg (fun z : ℂ => z - ψ.toFun (-1)) h3
  simpa using this

end Qatlib.Papers.GaussSumEst02.JacobiPhase
