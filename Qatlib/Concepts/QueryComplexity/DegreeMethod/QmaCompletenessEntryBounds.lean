/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.QmaCompleteness

/-!
# Entry bounds for clock Hamiltonian terms

This module proves entrywise norm bounds and Hermiticity for the clock projectors, hopping
matrices, and physical input, output, and propagation terms. These estimates support finite
local-Hamiltonian constructions in the circuit-to-Hamiltonian framework of
[KitaevShenVyalyi2002].

## Main statements

* `physicalPropagation_entry_norm`: Propagation entries have norm at most one when gate entries
  have norm at most two.
* `physicalPropagation_hermitian`: The physical propagation matrix is Hermitian.
* `physicalInput_hermitian`: The physical input penalty is Hermitian.
* `physicalOutput_hermitian`: The physical output penalty is Hermitian.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib Matrix
open scoped Classical
set_option autoImplicit false
noncomputable section

/-- A clock configuration cannot satisfy both `Pre i` and `Post i`. -/
theorem pre_post_impossible {m : ℕ} (i : Fin m) (c : Clock m) :
    ¬ (Pre i c ∧ Post i c) := by
  intro h
  have hf : c i = false := h.1.2.1
  have ht : c i = true := h.2.2.1
  simp [hf] at ht

/-- Every diagonal entry of a clock hopping matrix is zero. -/
theorem hop_diag_zero {m : ℕ} (i : Fin m) (c : Clock m) : hop i c c = 0 := by
  have hn : ¬ (Post i c ∧ Pre i c ∧ Outside i c c) := by
    intro h
    exact pre_post_impossible i c ⟨h.2.1, h.1⟩
  simp [hop, hn]

/-- A nonzero clock hop forces the reversed entry of the same hopping matrix to be zero. -/
theorem hop_reverse_zero {m : ℕ} (i : Fin m) (r c : Clock m)
    (h : hop i r c ≠ 0) : hop i c r = 0 := by
  have hp : Post i r ∧ Pre i c ∧ Outside i r c := by
    by_contra hn
    simp [hop, hn] at h
  have hn : ¬ (Post i c ∧ Pre i r ∧ Outside i c r) := by
    intro hr
    exact pre_post_impossible i r ⟨hr.2.1, hp.1⟩
  simp [hop, hn]

/-- Every entry of a clock hopping matrix has norm at most one. -/
theorem hop_entry_norm {m : ℕ} (i : Fin m) (r c : Clock m) :
    ‖hop i r c‖ ≤ 1 := by
  unfold hop
  split_ifs <;> norm_num

/-- Every entry of the adjoint clock hopping matrix has norm at most one. -/
theorem hop_adjoint_entry_norm {m : ℕ} (i : Fin m) (r c : Clock m) :
    ‖(hop i)ᴴ r c‖ ≤ 1 := by
  change ‖star (hop i c r)‖ ≤ 1
  simpa only [norm_star] using hop_entry_norm i c r

/-- A diagonal matrix whose entries are zero or one has all entry norms at most one. -/
theorem diagonal01_entry_norm {I : Type} [DecidableEq I]
    (P : I → Prop) (r c : I) :
    ‖(Matrix.diagonal (fun z => if P z then (1 : ℂ) else 0)) r c‖ ≤ 1 := by
  by_cases h : r = c
  · subst c
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> norm_num
  · simp [h]

/-- A diagonal matrix whose entries are zero or one is Hermitian. -/
theorem diagonal01_hermitian {I : Type} [DecidableEq I]
    (P : I → Prop) :
    Matrix.IsHermitian (Matrix.diagonal (fun z => if P z then (1 : ℂ) else 0)) := by
  change (Matrix.diagonal (fun z => if P z then (1 : ℂ) else 0))ᴴ = _
  ext r c
  by_cases h : r = c
  · subst c
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [Matrix.conjTranspose_apply, h, Ne.symm h]

/-- Every entry of the pre-transition clock projector has norm at most one. -/
theorem preProjector_entry_norm {m : ℕ} (i : Fin m) (r c : Clock m) :
    ‖preProjector i r c‖ ≤ 1 :=
  diagonal01_entry_norm (Pre i) r c

/-- Every entry of the post-transition clock projector has norm at most one. -/
theorem postProjector_entry_norm {m : ℕ} (i : Fin m) (r c : Clock m) :
    ‖postProjector i r c‖ ≤ 1 :=
  diagonal01_entry_norm (Post i) r c

/-- The pre-transition clock projector is Hermitian. -/
theorem preProjector_hermitian {m : ℕ} (i : Fin m) :
    Matrix.IsHermitian (preProjector i) := diagonal01_hermitian (Pre i)

/-- The post-transition clock projector is Hermitian. -/
theorem postProjector_hermitian {m : ℕ} (i : Fin m) :
    Matrix.IsHermitian (postProjector i) := diagonal01_hermitian (Post i)

/-- Every entry of the clock pair penalty has norm at most one. -/
theorem pairPenalty_entry_norm {m : ℕ} (i j : Fin m) (r c : Clock m) :
    ‖pairPenalty i j r c‖ ≤ 1 := by
  unfold pairPenalty
  by_cases h : r=c
  · subst c
    simp only [Matrix.diagonal_apply_eq]
    split_ifs <;> norm_num
  · simp [h]

/-- The clock pair penalty is Hermitian. -/
theorem pairPenalty_hermitian {m : ℕ} (i j : Fin m) :
    Matrix.IsHermitian (pairPenalty i j) := by
  change (pairPenalty i j)ᴴ=pairPenalty i j
  ext r c
  by_cases h : r=c
  · subst c
    simp only [Matrix.conjTranspose_apply,pairPenalty,Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [Matrix.conjTranspose_apply,pairPenalty,h,Ne.symm h]

/-- Half the product of complex numbers of norms at most one and two has norm at most one. -/
theorem half_product_bound (a z : ℂ) (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 2) :
    ‖(1 / 2 : ℂ) * (a*z)‖ ≤ 1 := by
  have hp : ‖a‖ * ‖z‖ ≤ 2 := by
    calc
      ‖a‖ * ‖z‖ ≤ (1 : ℝ) * 2 :=
        mul_le_mul ha hz (norm_nonneg z) (by norm_num)
      _ = 2 := by norm_num
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_mul, norm_mul, hhalf]
  nlinarith

/-- Every entry of the physical propagation term has norm at most one when every entry of the
gate matrix has norm at most two. -/
theorem physicalPropagation_entry_norm {m n : ℕ} (i : Fin m)
    (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : ∀ x y : Reg n, ‖U x y‖ ≤ 2)
    (p q : Clock m × Reg n) : ‖physicalPropagation i U p q‖ ≤ 1 := by
  rcases p with ⟨r,x⟩
  rcases q with ⟨c,y⟩
  change ‖(1 / 2 : ℂ) *
    (postProjector i r c * (1 : Matrix (Reg n) (Reg n) ℂ) x y +
     preProjector i r c * (1 : Matrix (Reg n) (Reg n) ℂ) x y -
     hop i r c * U x y - (hop i)ᴴ r c * Uᴴ x y)‖ ≤ 1
  by_cases hrc : r = c
  · subst c
    have hz := hop_diag_zero i r
    have hza : (hop i)ᴴ r r = 0 := by
      simp [Matrix.conjTranspose_apply, hz]
    by_cases hp : Post i r
    · have hq : ¬ Pre i r := fun hpre => pre_post_impossible i r ⟨hpre,hp⟩
      by_cases hxy : x = y <;>
        norm_num [postProjector, preProjector, clockIndicator,
          Matrix.one_apply, hz, hza, hp, hq, hxy]
    · by_cases hq : Pre i r
      · by_cases hxy : x = y <;>
          norm_num [postProjector, preProjector, clockIndicator,
            Matrix.one_apply, hz, hza, hp, hq, hxy]
      · norm_num [postProjector, preProjector, clockIndicator, hz, hza, hp, hq]
  · have hP : postProjector i r c = 0 := by
      simp [postProjector, clockIndicator, hrc]
    have hQ : preProjector i r c = 0 := by
      simp [preProjector, clockIndicator, hrc]
    rw [hP, hQ]
    simp only [zero_mul, zero_add]
    by_cases hh : hop i r c = 0
    · rw [hh]
      simp only [zero_mul, zero_sub, neg_zero]
      have hUa : ‖Uᴴ x y‖ ≤ 2 := by
        change ‖star (U y x)‖ ≤ 2
        simpa only [norm_star] using hU y x
      simpa only [mul_neg, norm_neg] using
        half_product_bound ((hop i)ᴴ r c) (Uᴴ x y)
          (hop_adjoint_entry_norm i r c) hUa
    · have hr := hop_reverse_zero i r c hh
      have ha : (hop i)ᴴ r c = 0 := by
        simp [Matrix.conjTranspose_apply, hr]
      rw [ha]
      simp only [zero_mul, sub_zero, zero_sub]
      simpa only [mul_neg, norm_neg] using
        half_product_bound (hop i r c) (U x y) (hop_entry_norm i r c) (hU x y)

/-- The physical propagation matrix is Hermitian for every complex gate matrix `U`. -/
theorem physicalPropagation_hermitian {m n : ℕ} (i : Fin m)
    (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix.IsHermitian (physicalPropagation i U) := by
  change (physicalPropagation i U)ᴴ = physicalPropagation i U
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  simp only [physicalPropagation, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    tensorGate_conjTranspose, Matrix.conjTranspose_one,
    (postProjector_hermitian i).eq, (preProjector_hermitian i).eq,
    Matrix.conjTranspose_conjTranspose, hhalf]
  congr 1
  abel

/-- A diagonal matrix selected between two complex values by a Boolean function has entry norms
at most one when both values do. -/
theorem bool_diagonal_entry_norm {I : Type} [DecidableEq I]
    (f : I→Bool) (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (r c : I) :
    ‖Matrix.diagonal (fun z => if f z then a else b) r c‖ ≤ 1 := by
  by_cases h : r=c
  · subst c
    simp only [Matrix.diagonal_apply_eq]
    split_ifs
    · exact ha
    · exact hb
  · simp [h]

/-- A Boolean-selected diagonal matrix is Hermitian when both selected values are fixed by
complex conjugation. -/
theorem bool_diagonal_hermitian {I : Type} [DecidableEq I]
    (f : I→Bool) (a b : ℂ) (ha : star a=a) (hb : star b=b) :
    Matrix.IsHermitian (Matrix.diagonal (fun z => if f z then a else b)) := by
  ext r c
  by_cases h : r=c
  · subst c
    simp only [Matrix.conjTranspose_apply,Matrix.diagonal_apply_eq]
    split_ifs
    · exact ha
    · exact hb
  · simp [Matrix.conjTranspose_apply,h,Ne.symm h]

/-- Every entry of the physical input penalty has norm at most one. -/
theorem physicalInput_entry_norm {m n : ℕ} (j : Fin n) (p q : Clock m×Reg n) :
    ‖physicalInput j p q‖ ≤ 1 := by
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  change ‖clockIndicator atStart c d*Matrix.diagonal
      (fun z : Reg n => if z j then 1 else 0) x y‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul (diagonal01_entry_norm atStart c d)
    (bool_diagonal_entry_norm (fun z : Reg n => z j) 1 0 (by norm_num) (by norm_num) x y)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- Every entry of the physical output penalty has norm at most one. -/
theorem physicalOutput_entry_norm {m n : ℕ} (j : Fin n) (p q : Clock m×Reg n) :
    ‖physicalOutput j p q‖ ≤ 1 := by
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  change ‖clockIndicator atEnd c d*Matrix.diagonal (fun z : Reg n => if z j then 0 else 1) x y‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul (diagonal01_entry_norm atEnd c d)
    (bool_diagonal_entry_norm (fun z : Reg n => z j) 0 1 (by norm_num) (by norm_num) x y)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The physical input penalty is Hermitian. -/
theorem physicalInput_hermitian {m n : ℕ} (j : Fin n) :
    Matrix.IsHermitian (physicalInput (m:=m) j) := by
  change (physicalInput j)ᴴ=physicalInput j
  simp only [physicalInput,tensorGate_conjTranspose,clockIndicator,(diagonal01_hermitian atStart).eq,
    (bool_diagonal_hermitian (fun z : Reg n => z j) 1 0 (by simp) (by simp)).eq]

/-- The physical output penalty is Hermitian. -/
theorem physicalOutput_hermitian {m n : ℕ} (j : Fin n) :
    Matrix.IsHermitian (physicalOutput (m:=m) j) := by
  change (physicalOutput j)ᴴ=physicalOutput j
  simp only [physicalOutput,tensorGate_conjTranspose,clockIndicator,(diagonal01_hermitian atEnd).eq,
    (bool_diagonal_hermitian (fun z : Reg n => z j) 0 1 (by simp) (by simp)).eq]

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod
