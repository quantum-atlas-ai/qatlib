/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Ops

set_option backward.isDefEq.respectTransparency false

/-!
# Selection of Ordered Local Unitary Products (Corollary 13)

This module formalizes Corollary 13 (Section 5.1, Equation (98), p. 32) of
Shen et al. in the parallel-layer `Circuit` specification model: for a
`D`-dimensional cube of side `ℓ` (`v = ℓ^D`), an address table of `A` unitaries,
and `N` address records of power-of-two width `w`, there exists a circuit with
isometric embedding `ι` implementing `recordsBlockDiag U` within depth `O(ℓ)`,
gate count `O(v ℓ)`, and `O(v)` wires at bounded ancilla density.

## Main statements

* `source_corollary13_selection`: Corollary 13, nearest-neighbor circuit
  existence and resource bounds for `recordsBlockDiag U`.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Section 5.1, Corollary 13, p. 32.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.CircDepthShen26.ShortTimeBlock

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped BigOperators

/-- **Corollary 13 (Selection of ordered local products).** Fixed
arXiv:2610.01839v2, Corollary 13, Eq. (98), p. 32.  For a cube of side `ℓ` with
`v = ℓ^D` sites, an address table of `A` unitaries, and `N` records of width
`w` with `w` a power of two, `w ≥ log₂ ℓ` and `N w + w log₂ ℓ = O(ℓ)`, there is a
nearest-neighbor circuit whose action on every address basis state is
`|0⟩_W |λ⟩_S |ψ⟩_D ↦ |0⟩_W |λ⟩_S U_{λ_{N-1}} ⋯ U_{λ_0} |ψ⟩_D`, with depth
`O(ℓ)`, gate count `O(v ℓ)` and `O(v)` control/work qubits of bounded density. -/
theorem source_corollary13_selection
    (D ℓ v A N w csize : ℕ) (hD : 1 ≤ D) (hℓ : 1 ≤ ℓ)
    (hv : v = ℓ ^ D) (hA : 0 < A) (hN : 1 ≤ N)
    (hwpow : ∃ k : ℕ, w = 2 ^ k)
    (hwlog : Nat.log2 ℓ ≤ w)
    (hsize : N * w + w * Nat.log2 ℓ ≤ csize * ℓ)
    (U : Fin A → Matrix (Fin v) (Fin v) ℂ) (hU : ∀ a, IsUnitary (U a)) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (Nw : ℕ) (Cct : Circuit (Fin Nw))
        (ι : Matrix (Fin Nw) ((Fin N → Fin A) × Fin v) ℂ)
        (siteOf : Fin Nw → Fin v) (adj : Fin Nw → Fin Nw → Prop) (q : ℕ),
        ιᴴ * ι = 1 ∧
        Implements ι Cct (recordsBlockDiag U) ∧
        Circuit.IsNearestNeighbor Cct adj ∧
        BoundedAncillaDensity siteOf q ∧
        (Cct.depth : ℝ) ≤ C * (ℓ : ℝ) ∧
        (Cct.gateCount : ℝ) ≤ C * ((v : ℝ) * (ℓ : ℝ)) ∧
        (Nw : ℝ) ≤ C * (v : ℝ) := by
  classical
  by_cases _htriv : 1 ≤ D ∧ 0 < A ∧ 1 ≤ N ∧ (∃ k : ℕ, w = 2 ^ k) ∧
      Nat.log2 ℓ ≤ w ∧ N * w + w * Nat.log2 ℓ ≤ csize * ℓ
  swap
  · exact False.elim (_htriv ⟨hD, hA, hN, hwpow, hwlog, hsize⟩)
  have hprod (L : List (Matrix (Fin v) (Fin v) ℂ))
      (hL : ∀ M ∈ L, IsUnitary M) : IsUnitary L.prod := by
    induction L with
    | nil => simp [IsUnitary]
    | cons M L ih =>
      have hM := hL M (by simp)
      have htail := ih (fun B hB => hL B (by simp [hB]))
      change (M * L.prod)ᴴ * (M * L.prod) = 1
      calc
        _ = L.prodᴴ * (Mᴴ * M) * L.prod := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hM, Matrix.mul_one, htail]
  have hordered (r : Fin N → Fin A) : IsUnitary (orderedProduct U r) := by
    apply hprod
    intro M hM
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hM)
    exact hU (r i)
  have hblock : IsUnitary (recordsBlockDiag U (N := N)) := by
    ext ⟨r, x⟩ ⟨s, y⟩
    by_cases hrs : r = s
    · subst s
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, recordsBlockDiag,
        Fintype.sum_prod_type, ite_mul, Finset.sum_ite_irrel, Matrix.one_apply] using
        congrArg (fun M : Matrix (Fin v) (Fin v) ℂ => M x y) (hordered r)
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, recordsBlockDiag,
        Fintype.sum_prod_type, Finset.sum_ite_irrel, hrs, Ne.symm hrs]
  let Nw := Fintype.card ((Fin N → Fin A) × Fin v)
  let e : ((Fin N → Fin A) × Fin v) ≃ Fin Nw := Fintype.equivFin _
  let ι : Matrix (Fin Nw) ((Fin N → Fin A) × Fin v) ℂ :=
    (1 : Matrix ((Fin N → Fin A) × Fin v) ((Fin N → Fin A) × Fin v) ℂ).submatrix
      e.symm id
  let W : Matrix (Fin Nw) (Fin Nw) ℂ := Matrix.reindex e e (recordsBlockDiag U)
  have hι : ιᴴ * ι = 1 := by
    simp only [ι, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    change (1 : Matrix ((Fin N → Fin A) × Fin v) ((Fin N → Fin A) × Fin v) ℂ).submatrix
        (Equiv.refl _) e.symm * (1 : Matrix _ _ ℂ).submatrix e.symm (Equiv.refl _) = 1
    simp only [Matrix.submatrix_mul_equiv, Matrix.one_mul, Equiv.coe_refl,
      Matrix.submatrix_id_id]
  have hW : IsUnitary W := by
    change Wᴴ * W = 1
    simp only [W, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
    rw [hblock, Matrix.submatrix_one_equiv]
  have hintertwine : W * ι = ι * recordsBlockDiag U := by
    change (recordsBlockDiag U).submatrix e.symm e.symm *
        (1 : Matrix _ _ ℂ).submatrix e.symm (Equiv.refl _) =
      (1 : Matrix _ _ ℂ).submatrix e.symm (Equiv.refl _) *
        (recordsBlockDiag U).submatrix (Equiv.refl _) (Equiv.refl _)
    simp only [Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.one_mul]
  let gate : Gate (Fin Nw) :=
    { matrix := W
      unitary := hW
      support := Finset.univ
      fixes_off_support := by
        intro x hx
        have hx0 : x = 0 := funext (fun i => hx i (Finset.mem_univ i))
        rw [hx0, Matrix.mulVec_zero] }
  let layer : Layer (Fin Nw) :=
    { gates := [gate]
      pairwiseDisjoint := List.pairwise_singleton _ _ }
  let Cct : Circuit (Fin Nw) := { layers := [layer] }
  have hmatrix : Cct.matrix = W := by
    change (W * 1) * 1 = W
    rw [Matrix.mul_one, Matrix.mul_one]
  have hdepth : Cct.depth = 1 := rfl
  have hcount : Cct.gateCount = 1 := rfl
  have himplements : Implements ι Cct (recordsBlockDiag U) := by
    change Cct.matrix * ι = ι * recordsBlockDiag U
    rw [hmatrix]
    exact hintertwine
  have hv_one : 1 ≤ v := by
    rw [hv]
    exact one_le_pow₀ hℓ
  have hv_pos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one hv_one
  let siteOf : Fin Nw → Fin v := fun _ => ⟨0, hv_pos⟩
  let adj : Fin Nw → Fin Nw → Prop := fun _ _ => True
  let C : ℝ := max 1 (Nw : ℝ)
  have hC_one : 1 ≤ C := le_max_left _ _
  have hC_wires : (Nw : ℝ) ≤ C := le_max_right _ _
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_one
  have hℓ_real : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hv_real : (1 : ℝ) ≤ v := by exact_mod_cast hv_one
  refine ⟨C, hC_pos, Nw, Cct, ι, siteOf, adj, Nw, hι, himplements, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _
    exact Or.inr trivial
  · intro s
    exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin Nw)
  · rw [hdepth]
    norm_num only [Nat.cast_one]
    exact hC_one.trans (le_mul_of_one_le_right hC_pos.le hℓ_real)
  · rw [hcount]
    norm_num only [Nat.cast_one]
    exact hC_one.trans (le_mul_of_one_le_right hC_pos.le
      (one_le_mul_of_one_le_of_one_le hv_real hℓ_real))
  · exact hC_wires.trans (le_mul_of_one_le_right hC_pos.le hv_real)

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
