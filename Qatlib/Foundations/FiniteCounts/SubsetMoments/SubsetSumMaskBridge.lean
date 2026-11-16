/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.FiniteCounts.SubsetMoments.GlobalSourceMoments

@[expose] public section


/-! # Exact subset-sum meaning of a target mask

With all observed phases set to one, a masked residue coefficient is exactly
the number of fixed-cardinality subsets hitting that residue.  This is a
combinatorial bridge, not a complexity lower bound.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteCounts.SubsetMoments
open scoped BigOperators Classical

/-- The number of fixed-cardinality subsets with a specified modular sum. -/
def subsetSumSupportCount {m N : ℕ} (labels : Fin m → ZMod N)
    (degree : ℕ) (target : ZMod N) : ℕ :=
  (Finset.powersetCard degree (Finset.univ : Finset (Fin m))).filter
    (fun S => (∑ i ∈ S, labels i) = target) |>.card

/-- With unit weights, the residue coefficient counts the fixed-cardinality subset solutions. -/
theorem sourceResidueCoefficient_one_eq_count {m N : ℕ}
    (labels : Fin m → ZMod N) (degree : ℕ) (target : ZMod N) :
    sourceResidueCoefficient labels (fun _ => (1 : ℂ)) degree target =
      (subsetSumSupportCount labels degree target : ℂ) := by
  unfold sourceResidueCoefficient subsetSumSupportCount
  simp only [Finset.prod_const_one]
  rw [Finset.sum_boole]

/-- The number of fixed-cardinality subsets with a specified natural-number sum. -/
def ordinarySubsetSumCount {m : ℕ} (weights : Fin m → ℕ)
    (degree target : ℕ) : ℕ :=
  (Finset.powersetCard degree (Finset.univ : Finset (Fin m))).filter
    (fun S => (∑ i ∈ S, weights i) = target) |>.card

/-- Under an explicit no-wrap bound, the modular subset count is the ordinary natural subset count. -/
theorem subsetSumSupportCount_nat_weights_eq {m N : ℕ}
    (weights : Fin m → ℕ) (degree target : ℕ)
    (htarget : target < N)
    (hbound : ∀ S ∈ Finset.powersetCard degree (Finset.univ : Finset (Fin m)),
      (∑ i ∈ S, weights i) < N) :
    subsetSumSupportCount (fun i => (weights i : ZMod N)) degree (target : ZMod N) =
      ordinarySubsetSumCount weights degree target := by
  unfold subsetSumSupportCount ordinarySubsetSumCount
  apply congrArg Finset.card
  apply Finset.ext
  intro S
  simp only [Finset.mem_filter]
  constructor
  · intro hmem
    have hS := hmem.1
    have hEq := hmem.2
    have hsum : (∑ i ∈ S, (weights i : ZMod N)) =
        ((∑ i ∈ S, weights i : ℕ) : ZMod N) := by
      simp only [Nat.cast_sum]
    rw [hsum, ZMod.natCast_eq_natCast_iff] at hEq
    refine ⟨hS, ?_⟩
    exact Nat.ModEq.eq_of_lt_of_lt hEq (hbound S hS) htarget
  · intro hmem
    have hS := hmem.1
    have hEq : (∑ i ∈ S, weights i) = target := hmem.2
    have hsum : (∑ i ∈ S, (weights i : ZMod N)) =
        ((∑ i ∈ S, weights i : ℕ) : ZMod N) := by
      simp only [Nat.cast_sum]
    refine ⟨hS, ?_⟩
    rw [hsum, ZMod.natCast_eq_natCast_iff]
    simpa [hEq] using (Nat.ModEq.refl (n := N) target)

/-- The fixed-cardinality modular subset-sum solution set is nonempty. -/
def subsetSumSupportExists {m N : ℕ} (labels : Fin m → ZMod N)
    (degree : ℕ) (target : ZMod N) : Prop :=
  (Finset.powersetCard degree (Finset.univ : Finset (Fin m))).filter
    (fun S => (∑ i ∈ S, labels i) = target) |>.Nonempty

/-- The unit-weight residue coefficient is nonzero exactly when the subset-sum instance has a solution. -/
theorem sourceResidueCoefficient_one_ne_zero_iff {m N : ℕ}
    (labels : Fin m → ZMod N) (degree : ℕ) (target : ZMod N) :
    sourceResidueCoefficient labels (fun _ => (1 : ℂ)) degree target ≠ 0 ↔
      subsetSumSupportExists labels degree target := by
  rw [sourceResidueCoefficient_one_eq_count]
  unfold subsetSumSupportExists subsetSumSupportCount
  rw [Nat.cast_ne_zero, Finset.card_ne_zero]

/-- The residues attained by subsets of a prescribed cardinality. -/
def subsetSumResidues {m N : ℕ} (labels : Fin m → ZMod N)
    (degree : ℕ) : Finset (ZMod N) :=
  (Finset.powersetCard degree (Finset.univ : Finset (Fin m))).image
    (fun S => ∑ i ∈ S, labels i)

/-- The subset-sum map is injective on subsets of the prescribed cardinality. -/
def subsetSumResidueInjective {m N : ℕ} (labels : Fin m → ZMod N)
    (degree : ℕ) : Prop :=
  Set.InjOn (fun S => ∑ i ∈ S, labels i)
    (Finset.powersetCard degree (Finset.univ : Finset (Fin m)) : Set (Finset (Fin m)))

/-- Injectivity makes the attained residue count equal to the binomial subset count. -/
theorem subsetSumResidues_card_eq {m N : ℕ} (labels : Fin m → ZMod N)
    (degree : ℕ) (hinj : subsetSumResidueInjective labels degree) :
    (subsetSumResidues labels degree).card = Nat.choose m degree := by
  unfold subsetSumResidues
  rw [Finset.card_image_iff.mpr hinj, Finset.card_powersetCard]
  simp

/-- Every attained residue has nonzero unit-weight coefficient. -/
theorem sourceResidueCoefficient_one_ne_zero_of_mem_residues {m N : ℕ}
    (labels : Fin m → ZMod N) (degree : ℕ) {target : ZMod N}
    (htarget : target ∈ subsetSumResidues labels degree) :
    sourceResidueCoefficient labels (fun _ => (1 : ℂ)) degree target ≠ 0 := by
  unfold subsetSumResidues at htarget
  rcases Finset.mem_image.mp htarget with ⟨S, hS, hsum⟩
  apply (sourceResidueCoefficient_one_ne_zero_iff labels degree target).2
  change (Finset.powersetCard degree (Finset.univ : Finset (Fin m))).filter
      (fun T => (∑ i ∈ T, labels i) = target) |>.Nonempty
  exact ⟨S, Finset.mem_filter.mpr ⟨hS, hsum⟩⟩

/-- The attained residues with nonzero unit-weight coefficients. -/
def sourceResidueNonzeroSet {m N : ℕ} (labels : Fin m → ZMod N)
    (degree : ℕ) : Finset (ZMod N) :=
  (subsetSumResidues labels degree).filter
    (fun target => sourceResidueCoefficient labels (fun _ => (1 : ℂ)) degree target ≠ 0)

/-- Under injectivity, the nonzero coefficient support has binomial cardinality. -/
theorem sourceResidueNonzeroSet_card_eq {m N : ℕ}
    (labels : Fin m → ZMod N) (degree : ℕ)
    (hinj : subsetSumResidueInjective labels degree) :
    (sourceResidueNonzeroSet labels degree).card = Nat.choose m degree := by
  unfold sourceResidueNonzeroSet
  rw [Finset.filter_eq_self.mpr]
  · exact subsetSumResidues_card_eq labels degree hinj
  · intro target htarget
    exact sourceResidueCoefficient_one_ne_zero_of_mem_residues labels degree htarget

/-- The support of the unit-weight residue table is exactly the attained residue set. -/
theorem sourceResidueNonzeroSet_eq_residues {m N : ℕ}
    (labels : Fin m → ZMod N) (degree : ℕ) :
    sourceResidueNonzeroSet labels degree = subsetSumResidues labels degree := by
  unfold sourceResidueNonzeroSet
  rw [Finset.filter_eq_self.mpr]
  intro target htarget
  exact sourceResidueCoefficient_one_ne_zero_of_mem_residues labels degree htarget

end Qatlib.Foundations.FiniteCounts.SubsetMoments
