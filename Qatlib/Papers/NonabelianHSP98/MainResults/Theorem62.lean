/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting

/-!
# Transform of a normalized subgroup indicator

`dft` is the unnormalized finite transform with kernel `chi (mu x y)`. For subgroups of
cardinality at least four, `theorem_6_2` identifies the transform of the subgroup indicator
divided by its cardinality with the indicator of `perpSub U`. This development accompanies
[RoettelerBeth1998].

## Main statements

* `chi`: the complex sign character of `ZMod 2`.
* `dft`: the transform defined by the binary pairing.
* `theorem_6_2`: the normalized subgroup indicator transforms to its orthogonal-complement
  indicator.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Theorem62

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting
open Finset

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The complex sign character on `ZMod 2`, reused from the vector counting model. -/
noncomputable abbrev chi : ZMod 2 → ℂ :=
  Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting.chi

/-- The unnormalized finite transform summing `chi (mu x y) * ψ x` over all wreath-product
elements `x`. -/
noncomputable def dft (ψ : Wreath n → ℂ) : Wreath n → ℂ :=
  fun y => ∑ x : Wreath n, chi (mu x y) * ψ x

/-- For a subgroup with at least four elements, the transform of its indicator divided by its
cardinality is the indicator of its orthogonal complement. This is Theorem 6.2 of
[RoettelerBeth1998]. -/
theorem theorem_6_2 (U : Subgroup (Wreath n)) (hcard : 4 ≤ Fintype.card U) :
    dft (fun x => if x ∈ U then ((Fintype.card U : ℂ)⁻¹) else 0)
      = fun y => if y ∈ perpSub U then 1 else 0 := by
  funext y
  simp only [dft]
  let c : ℂ := ((Fintype.card U : ℂ)⁻¹)
  have hcard_ne : (Fintype.card U : ℂ) ≠ 0 := by
    have hne : Fintype.card U ≠ 0 := by omega
    exact Nat.cast_ne_zero.mpr hne

  have hsum : (∑ x : Wreath n, chi (mu x y) * (if x ∈ U then c else 0))
      = (∑ u : U, chi (mu (u : Wreath n) y)) * c := by
    have hstep1 : (∑ x : Wreath n, chi (mu x y) * (if x ∈ U then c else 0))
        = ∑ x : Wreath n, if x ∈ U then chi (mu x y) * c else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x ∈ U <;> simp [h]
    rw [hstep1, ← Finset.sum_filter]
    rw [Finset.sum_subtype (s := univ.filter (fun x : Wreath n => x ∈ U))
      (p := fun x : Wreath n => x ∈ U) (fun x => by simp)]
    rw [Finset.sum_mul]
  rw [hsum]
  by_cases hy : y ∈ perpSub U
  · simp only [if_pos hy]

    have hchi : ∀ u : U, chi (mu (u : Wreath n) y) = 1 := by
      intro u
      have h0 : mu (u : Wreath n) y = 0 := by
        rw [mu_comm]
        exact (mem_perpSub.mp hy) (u : Wreath n) u.2
      rw [h0]
      simp [Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting.chi]
    have h1 : (∑ u : U, chi (mu (u : Wreath n) y)) = (Fintype.card U : ℂ) := by
      rw [Finset.sum_congr rfl (fun u _ => hchi u)]
      simp [Finset.card_univ]
    rw [h1]
    show (Fintype.card U : ℂ) * c = 1
    dsimp only [c]
    exact mul_inv_cancel₀ hcard_ne
  · simp only [if_neg hy]

    have hsum0 : (∑ u : U, chi (mu (u : Wreath n) y)) = 0 := by
      have hne : ∃ w ∈ phiSub U, dot (phi y) w ≠ 0 := by
        have hnot : ¬ ∀ u : U, mu (u : Wreath n) y = 0 := by
          intro hu
          apply hy
          rw [mem_perpSub]
          intro v hv
          rw [mu_comm]
          exact hu ⟨v, hv⟩
        obtain ⟨u, hu⟩ := not_forall.mp hnot
        refine ⟨phi (u : Wreath n), mem_phiSub.mpr u.2, ?_⟩
        rw [dot_comm, ← phi_mu]
        exact hu
      have hzero := sum_chi_eq_zero (phiSub U) (phi y) hne
      rw [Fintype.sum_equiv (phiSubEquiv U)
        (fun u : U => chi (mu (u : Wreath n) y))
        (fun w : phiSub U => chi (dot (phi y) (w : Vec n)))
        (fun u => by
          change chi (mu (u : Wreath n) y) = chi (dot (phi y) (phi u))
          rw [phi_mu, dot_comm])]
      exact hzero
    rw [hsum0, zero_mul]

end Qatlib.Papers.NonabelianHSP98.MainResults.Theorem62
