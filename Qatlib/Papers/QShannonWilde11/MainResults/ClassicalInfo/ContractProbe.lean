/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.ClassicalInfo.ClosedMath

@[expose] public section


/-! # Endpoint and normalization counterexamples to old classical contracts

Real logarithms send zero to zero. The source relative entropy instead uses
support conventions; its nonnegativity and Pinsker results cannot be transported
to the old total real-valued formula at a zero denominator.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.ClassicalInfo.ContractProbe

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Papers.QShannonWilde11.MainResults.ClassicalInfo
open scoped BigOperators

/-- The old relative entropy is zero for a probability distribution against zero. -/
theorem zero_denominator_failure :
    let p : Unit → ℝ := fun _ => 1
    let q : Unit → ℝ := fun _ => 0
    IsProb p ∧ (∀ x, 0 ≤ q x) ∧ (∑ x, q x) ≤ 1 ∧
      classicalRelEnt p q = 0 ∧ p ≠ q := by
  dsimp
  refine ⟨by simp [IsProb], by simp, by simp, by simp [classicalRelEnt], ?_⟩
  intro h
  have := congrFun h ()
  norm_num at this

/-- The same zero denominator contradicts the old Pinsker bound. -/
theorem pinsker_failure :
    let p : Unit → ℝ := fun _ => 1
    let q : Unit → ℝ := fun _ => 0
    ¬ (1 / (2 * Real.log 2)) * (l1Dist p q) ^ 2 ≤ classicalRelEnt p q := by
  dsimp
  simp only [l1Dist, classicalRelEnt]
  norm_num
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- An unnormalized maximal singleton coupling violates the old second equality. -/
theorem coupling_failure :
    let p : Unit → ℝ := fun _ => 2
    let c : Unit × Unit → ℝ := fun _ => 2
    (∀ x y, 0 ≤ c (x, y)) ∧
      (∀ x, (∑ y, c (x, y)) = p x) ∧
      (∀ y, (∑ x, c (x, y)) = p y) ∧
      (∀ c' : Unit × Unit → ℝ, (∀ x, (∑ y, c' (x, y)) = p x) →
        (∀ y, (∑ x, c' (x, y)) = p y) →
        (∑ u, c' (u, u)) ≤ ∑ u, c (u, u)) ∧
      1 - ∑ u, c (u, u) ≠ (1 / 2) * l1Dist p p := by
  dsimp
  refine ⟨by norm_num, by simp, by simp, ?_, by norm_num [l1Dist]⟩
  intro c' h₁ _
  simpa using (h₁ ()).le

/-- A two-point domain cannot inject into the one-point hashing codomain. -/
theorem hashing_dimension_failure :
    ¬ ∃ g : Fin 2 → Fin 1 × Fin 1, Function.Injective g := by
  rintro ⟨g, hg⟩
  have h := Fintype.card_le_of_injective g hg
  norm_num at h

/-- Two different deterministic comparison laws refute the old arbitrary-q CMI bound. -/
theorem conditional_comparison_failure :
    let p : Fin 2 × Unit × Unit → ℝ := fun x => if x.1 = 0 then 1 else 0
    let q : Fin 2 × Unit × Unit → ℝ := fun x => if x.1 = 1 then 1 else 0
    IsProb p ∧ IsProb q ∧
      ¬ (2 / Real.log 2) * ((1 / 2) * l1Dist p q) ^ 2 ≤ classicalCondMutualInfo p := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro x
      dsimp only
      split_ifs <;> norm_num
    · rw [Fintype.sum_prod_type]
      norm_num [Fin.sum_univ_two]
  · constructor
    · intro x
      dsimp only
      split_ifs <;> norm_num
    · rw [Fintype.sum_prod_type]
      norm_num [Fin.sum_univ_two]
  · norm_num [l1Dist, classicalCondMutualInfo, classicalEntropy,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- X and Y are independent fair bits, while Z is a copy of X. -/
def copiedMarkovLaw (x : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  if x.2.2 = x.1 then 1 / 4 else 0

/-- The incorrectly indexed old Markov premise admits both old DPI counterexamples. -/
theorem markov_index_failure :
    IsProb copiedMarkovLaw ∧
      (∀ x y z, copiedMarkovLaw (x, y, z) =
        (∑ y', copiedMarkovLaw (x, y', z)) * (∑ z', copiedMarkovLaw (x, y, z')) /
          (∑ x', ∑ z', copiedMarkovLaw (x', y, z'))) ∧
      ¬ classicalMutualInfo (fun xz => ∑ y, copiedMarkovLaw (xz.1, y, xz.2)) ≤
        classicalMutualInfo (fun xy => ∑ z, copiedMarkovLaw (xy.1, xy.2, z)) ∧
      ¬ classicalCondMutualInfo copiedMarkovLaw ≤
        classicalMutualInfo (fun xy => ∑ z, copiedMarkovLaw (xy.1, xy.2, z)) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x
    simp only [copiedMarkovLaw]
    split_ifs <;> norm_num
  · norm_num [copiedMarkovLaw, Fintype.sum_prod_type, Fin.sum_univ_two]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      norm_num [copiedMarkovLaw, Fin.sum_univ_two]
  · norm_num [classicalMutualInfo, classicalCondMutualInfo, classicalEntropy,
      copiedMarkovLaw, Fintype.sum_prod_type, Fin.sum_univ_two, Real.log_div, hl4]
    constructor <;> linarith

end Qatlib.Papers.QShannonWilde11.MainResults.ClassicalInfo.ContractProbe
