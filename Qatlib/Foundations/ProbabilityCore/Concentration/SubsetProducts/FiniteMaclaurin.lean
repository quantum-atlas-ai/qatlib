/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Maclaurin

Finite Maclaurin constructions and identities for Probability Core.
-/

set_option autoImplicit false

namespace Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin
noncomputable section
open scoped BigOperators Classical

variable {S : Type*} [DecidableEq S]

/-- Construction for elementary in the finite maclaurin model. -/
def elementary (R : Finset S) (a : S → ℝ) (k : ℕ) : ℝ :=
  ∑ A ∈ R.powersetCard k,∏ x ∈ A,a x

omit [DecidableEq S] in
/-- Complete original `elementary_zero` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
@[simp] theorem elementary_zero (R : Finset S) (a : S → ℝ) : elementary R a 0=1 := by
  simp [elementary]

omit [DecidableEq S] in
/-- Complete original `elementary_empty` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
@[simp] theorem elementary_empty (a : S → ℝ) (k : ℕ) :
    elementary ∅ a (k+1)=0 := by
  rw [elementary,Finset.powersetCard_eq_empty.mpr (by simp)]
  simp

/-- Complete original `elementary_insert` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
theorem elementary_insert (R : Finset S) (a : S → ℝ) (x : S) (hx : x∉R) (k : ℕ) :
    elementary (insert x R) a (k+1)=elementary R a (k+1)+a x*elementary R a k := by
  have hd : Disjoint (R.powersetCard (k+1)) ((R.powersetCard k).image (insert x)) := by
    apply Finset.disjoint_left.mpr
    intro A hA hi
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hi
    exact hx ((Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self _ _))
  have hinj : ∀ A∈R.powersetCard k,∀ B∈R.powersetCard k,insert x A=insert x B → A=B := by
    intro A hA B hB h
    have hxa : x∉A := fun hh => hx ((Finset.mem_powersetCard.mp hA).1 hh)
    have hxb : x∉B := fun hh => hx ((Finset.mem_powersetCard.mp hB).1 hh)
    simpa only [Finset.erase_insert hxa,Finset.erase_insert hxb] using congrArg (Finset.erase · x) h
  unfold elementary
  rw [Finset.powersetCard_succ_insert hx,Finset.sum_union hd,Finset.sum_image hinj]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact Finset.prod_insert (fun hh => hx ((Finset.mem_powersetCard.mp hA).1 hh))

/-- Complete original `elementary_one` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
theorem elementary_one (R : Finset S) (a : S → ℝ) : elementary R a 1=∑ x ∈ R,a x := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert x R hx ih =>
    rw [elementary_insert R a x hx 0,elementary_zero,ih,Finset.sum_insert hx]
    ring

omit [DecidableEq S] in
/-- Complete original `elementary_nonneg` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
theorem elementary_nonneg (R : Finset S) (a : S → ℝ) (ha : ∀ x∈R,0≤a x) (k : ℕ) :
    0≤elementary R a k := by
  apply Finset.sum_nonneg
  intro A hA
  apply Finset.prod_nonneg
  intro x hx
  exact ha x ((Finset.mem_powersetCard.mp hA).1 hx)

/-- Complete original `deletion_sum` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
theorem deletion_sum (R : Finset S) (a : S → ℝ) (k : ℕ) :
    (∑ x ∈ R,elementary (R.erase x) a k)=((R.card : ℝ)-(k : ℝ))*elementary R a k := by
  induction R using Finset.induction_on generalizing k with
  | empty => cases k <;> simp
  | @insert x R hx ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hs : (∑ y ∈ R,elementary ((insert x R).erase y) a (k+1))=
          (∑ y ∈ R,elementary (R.erase y) a (k+1))+
            a x*(∑ y ∈ R,elementary (R.erase y) a k) := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        have hxy : x≠y := by intro h; exact hx (h.symm ▸ hy)
        rw [Finset.erase_insert_of_ne hxy,elementary_insert _ a x
          (fun hh => hx (Finset.mem_of_mem_erase hh))]
      rw [Finset.sum_insert hx,Finset.erase_insert hx,hs,ih (k+1),ih k,
        elementary_insert R a x hx k,Finset.card_insert_of_notMem hx]
      push_cast
      ring

/-- Complete original `weighted_deletion_sum` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
theorem weighted_deletion_sum (R : Finset S) (a : S → ℝ) (k : ℕ) :
    (∑ x ∈ R,a x*elementary (R.erase x) a k)=((k+1 : ℕ) : ℝ)*elementary R a (k+1) := by
  induction R using Finset.induction_on generalizing k with
  | empty => simp
  | @insert x R hx ih =>
    cases k with
    | zero => simp [elementary_one]
    | succ k =>
      have hs : (∑ y ∈ R,a y*elementary ((insert x R).erase y) a (k+1))=
          (∑ y ∈ R,a y*elementary (R.erase y) a (k+1))+
            a x*(∑ y ∈ R,a y*elementary (R.erase y) a k) := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        have hxy : x≠y := by intro h; exact hx (h.symm ▸ hy)
        rw [Finset.erase_insert_of_ne hxy,elementary_insert _ a x
          (fun hh => hx (Finset.mem_of_mem_erase hh))]
        ring
      rw [Finset.sum_insert hx,Finset.erase_insert hx,hs,ih (k+1),ih k,
        elementary_insert R a x hx (k+1)]
      push_cast
      ring

/-- Complete original `deletion_difference` guarantee for `FiniteMaclaurin`; all source hypotheses and output obligations are retained. -/
theorem deletion_difference (R : Finset S) (a : S → ℝ) (i j : S)
    (hi : i∈R) (hj : j∈R) (hij : i≠j) (k : ℕ) :
    elementary (R.erase i) a (k+1)-elementary (R.erase j) a (k+1)=
      (a j-a i)*elementary ((R.erase i).erase j) a k := by
  have hj' : j∈R.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  have hi' : i∈R.erase j := Finset.mem_erase.mpr ⟨hij,hi⟩
  have hleft := elementary_insert ((R.erase i).erase j) a j (Finset.notMem_erase _ _) k
  rw [Finset.insert_erase hj'] at hleft
  have hright := elementary_insert ((R.erase j).erase i) a i (Finset.notMem_erase _ _) k
  rw [Finset.insert_erase hi'] at hright
  have he : (R.erase j).erase i=(R.erase i).erase j := by
    ext x
    simp [and_left_comm]
  rw [he] at hright
  rw [hleft,hright]
  ring

end
end Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin

#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.elementary_insert
#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.deletion_sum
#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.weighted_deletion_sum
#print axioms Qatlib.Foundations.ProbabilityCore.Concentration.Maclaurin.deletion_difference
