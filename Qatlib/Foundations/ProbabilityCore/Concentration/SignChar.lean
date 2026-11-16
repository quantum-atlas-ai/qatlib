/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.SignMoments
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.LinearCombination

@[expose] public section


/-! # Actual sign-character cancellation for matrix permanent averaging

Demand: LinearOptics10 Corollary 65. A missing image coordinate is flipped
to cancel every nonpermutation assignment; permutation assignments have
character one. No unbiased estimator identity is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Foundations.ProbabilityCore.Concentration.SignChar
open SignMoments
variable {I : Type*} [Fintype I]

/-- The actual total-sign character of a row-to-column assignment. -/
def character (b : I → Bool) (f : I → I) : ℂ :=
  (∏ i, rSign (b i))*(∏ i, rSign (b (f i)))

/-- Every genuine permutation assignment has actual sign character one. -/
theorem permChar (b : I → Bool) (f : I → I) (hf : Function.Bijective f) :
    character b f = 1 := by
  let e := Equiv.ofBijective f hf
  have he : (∏ i, rSign (b (f i))) = ∏ i, rSign (b i) := by
    change (∏ i, rSign (b (e i))) = ∏ i, rSign (b i)
    exact e.prod_comp (fun i => rSign (b i))
  rw [character, he, ← Finset.prod_mul_distrib]
  simp only [signSquare, Finset.prod_const_one]

variable [DecidableEq I]

/-- Flipping one actual bit negates the product of all its signs. -/
theorem flipProd (b : I → Bool) (j : I) :
    (∏ i, rSign ((flipAt j) b i)) = -(∏ i, rSign (b i)) := by
  have he : (fun i => rSign ((flipAt j) b i)) =
      Function.update (fun i => rSign (b i)) j (-rSign (b j)) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [flipAt, signNot]
    · simp [flipAt, hi]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => rSign (b i)) (Finset.mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

/-- A missing assignment coordinate makes flipping that bit negate the entire true character. -/
theorem flipMissing (b : I → Bool) (f : I → I) (j : I) (hj : ∀ i, f i ≠ j) :
    character ((flipAt j) b) f = -character b f := by
  have he : (∏ i, rSign ((flipAt j) b (f i))) = ∏ i, rSign (b (f i)) := by
    apply Finset.prod_congr rfl
    intro i _
    simp [flipAt, hj i]
  rw [character, flipProd, he, character]
  ring

/-- The actual sum of signs cancels for every assignment missing any output coordinate. -/
theorem missingSum (f : I → I) (j : I) (hj : ∀ i, f i ≠ j) :
    (∑ b : I → Bool, character b f) = 0 := by
  have he : (∑ b : I → Bool, character b f) = -(∑ b : I → Bool, character b f) := by
    calc
      _ = ∑ b : I → Bool, character ((flipAt j) b) f := (Equiv.sum_comp (flipAt j) _).symm
      _ = ∑ b : I → Bool, -character b f := Finset.sum_congr rfl fun b _ => flipMissing b f j hj
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hz : (2 : ℂ)*(∑ b : I → Bool, character b f) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Summing actual Boolean characters selects exactly the genuine permutation assignments. -/
theorem characterSum (f : I → I) :
    (∑ b : I → Bool, character b f) =
      if Function.Bijective f then (Fintype.card (I → Bool) : ℂ) else 0 := by
  by_cases hf : Function.Bijective f
  · rw [ite_eq_left hf]
    have he (b : I → Bool) : character b f = 1 := permChar b f hf
    simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right hf]
    have hns : ¬Function.Surjective f := fun hs => hf
      ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hs, rfl⟩)
    obtain ⟨j, hj⟩ := not_forall.mp hns
    apply missingSum f j
    intro i hi
    exact hj ⟨i, hi⟩

end Qatlib.Foundations.ProbabilityCore.Concentration.SignChar
