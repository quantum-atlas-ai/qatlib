/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.HalfBasis
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Block

set_option backward.isDefEq.respectTransparency false

/-!
# Factorization of Special Unitary Matrices into Seven Half-Space Unitaries

This module formalizes Lemma 4 (Appendix D) of Shor and Jordan showing that
whenever `4 ∣ m`, every `m × m` special unitary matrix decomposes as a product
of seven unitary matrices each acting nontrivially on at most `m / 2` standard
basis vectors (`ActsOnSubset`).

## Main statements

* `lemma4`: Lemma 4, decomposing any `U ∈ unitaryGroup (Fin m) ℂ` with
  `U.det = 1` and `4 ∣ m` into a product of seven `m / 2`-supported unitaries.

## References

* [Shor and Jordan, 2008][ShorJordan2008], Appendix D, Lemma 4, p. 25.
-/

open Qatlib.Papers.JonesPolyShor07.MainResults
open Qatlib.Papers.JonesPolyShor07.MainResults.HalfBasis

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.HalfBasis

open Matrix
open scoped BigOperators

private theorem extend_orthonormal {α β : Type*} [Fintype α] [Fintype β]
    (f : α ↪ β) (v : α → EuclideanSpace ℂ β) (hv : Orthonormal ℂ v) :
    ∃ b : OrthonormalBasis β ℂ (EuclideanSpace ℂ β), ∀ a, b (f a) = v a := by
  classical
  let w := Function.extend f v (fun _ => 0)
  let e := Equiv.ofInjective f f.injective
  have hw : Orthonormal ℂ ((Set.range f).domRestrict w) := by
    convert hv.comp e.symm e.symm.injective using 1
    funext i
    change w i = v (e.symm i)
    calc
      w i = w (f (e.symm i)) := congrArg w (congrArg Subtype.val (e.apply_symm_apply i)).symm
      _ = v (e.symm i) := f.injective.extend_apply v (fun _ => 0) _
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, fun a => (hb (f a) ⟨a, rfl⟩).trans
    (f.injective.extend_apply v (fun _ => 0) a)⟩

private def liftBlock {m : ℕ} (S : Finset (Fin m))
    (W : Matrix S S ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (Matrix.fromBlocks W 0 0 (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℂ)).submatrix
    (Equiv.sumCompl (fun i => i ∈ S)).symm (Equiv.sumCompl (fun i => i ∈ S)).symm

private theorem liftBlock_unitary {m : ℕ} (S : Finset (Fin m))
    {W : Matrix S S ℂ} (hW : W ∈ Matrix.unitaryGroup S ℂ) :
    liftBlock S W ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  classical
  apply Matrix.submatrix_equiv_mem_unitary.mpr
  rw [Matrix.mem_unitaryGroup_iff']
  simpa [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
    mul_zero, zero_mul, add_zero, zero_add, one_mul, Matrix.fromBlocks_one] using
    congrArg (fun A => Matrix.fromBlocks A 0 0 (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℂ))
      hW.1

private theorem liftBlock_apply {m : ℕ} (S : Finset (Fin m)) (W : Matrix S S ℂ)
    (i j : Fin m) : liftBlock S W i j =
      if hi : i ∈ S then if hj : j ∈ S then W ⟨i, hi⟩ ⟨j, hj⟩ else 0
      else if j ∈ S then 0 else (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
  classical
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [liftBlock, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg,
      hi, hj, Matrix.one_apply, Subtype.ext_iff]

private theorem liftBlock_acts {m : ℕ} (S : Finset (Fin m)) (W : Matrix S S ℂ) :
    ActsOnSubset S (liftBlock S W) := by
  classical
  refine ⟨?_, ?_, ?_⟩ <;> intro i j hi hj <;>
    simp [liftBlock_apply, hi, hj, Matrix.one_apply]

private theorem liftBlock_det {m : ℕ} (S : Finset (Fin m)) (W : Matrix S S ℂ) :
    (liftBlock S W).det = W.det := by
  classical
  rw [liftBlock, ← Matrix.reindex_apply, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

private theorem acts_mul_out {m : ℕ} {S : Finset (Fin m)}
    {V : Matrix (Fin m) (Fin m) ℂ} (hV : ActsOnSubset S V)
    (M : Matrix (Fin m) (Fin m) ℂ) {i : Fin m} (hi : i ∉ S) (j : Fin m) :
    (V * M) i j = M i j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hV.1 i i hi hi]
    simp
  · intro a _ ha
    by_cases haS : a ∈ S
    · simp [hV.2.1 i a hi haS]
    · simp [hV.1 i a hi haS, Ne.symm ha]
  · simp

private theorem liftBlock_mul_in {m : ℕ} (S : Finset (Fin m)) (W : Matrix S S ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (i : S) (j : Fin m) :
    (liftBlock S W * M) i j = ∑ a : S, W i a * M a j := by
  classical
  rw [Matrix.mul_apply]
  calc
    _ = ∑ a ∈ S, liftBlock S W i a * M a j :=
      (Finset.sum_subset S.subset_univ (by
        intro a _ ha
        simp [liftBlock_apply, i.property, ha])).symm
    _ = _ := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      simp [liftBlock_apply, i.property, a.property]

private theorem block_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (b : OrthonormalBasis α ℂ (EuclideanSpace ℂ α)) (v : EuclideanSpace ℂ α) (i : α) :
    ∑ a, b.toBasis.toMatrix (EuclideanSpace.basisFun α ℂ) i a * v a = b.repr v i := by
  have h := congrArg (fun w : α → ℂ => w i)
    ((EuclideanSpace.basisFun α ℂ).toBasis.toMatrix_mulVec_repr b.toBasis v)
  simpa [Matrix.mulVec, dotProduct] using h

private theorem clear_block {m : ℕ} (T R J : Finset (Fin m)) (hRT : R ⊆ T)
    (hcard : R.card + J.card ≤ T.card) (M : Matrix (Fin m) (Fin m) ℂ) :
    ∃ V : Matrix (Fin m) (Fin m) ℂ,
      V ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ ActsOnSubset T V ∧
        ∀ i ∈ R, ∀ j ∈ J, (V * M) i j = 0 := by
  classical
  let v : J → EuclideanSpace ℂ T := fun j => WithLp.toLp 2 (fun i => M i j)
  let E := Submodule.span ℂ (Set.range v)
  have hdim : Module.finrank ℂ E ≤ J.card := by
    simpa [E, Set.finrank] using (finrank_range_le_card (R := ℂ) v)
  have hperp : R.card ≤ Module.finrank ℂ Eᗮ := by
    have h := E.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace, Fintype.card_coe] at h
    omega
  let f : R ↪ T := ⟨fun i => ⟨i, hRT i.property⟩, fun _ _ h =>
    Subtype.ext (congrArg (fun i : T => (i : Fin m)) h)⟩
  let g : R ↪ Fin (Module.finrank ℂ Eᗮ) :=
    (Fintype.equivFin R).toEmbedding.trans (Fin.castLEEmb (by simpa using hperp))
  let b₀ := stdOrthonormalBasis ℂ Eᗮ
  have hv : Orthonormal ℂ (fun i : R => (b₀ (g i) : EuclideanSpace ℂ T)) :=
    (b₀.orthonormal.comp g g.injective).comp_linearIsometry Eᗮ.subtypeₗᵢ
  obtain ⟨b, hb⟩ := extend_orthonormal f _ hv
  let W := b.toBasis.toMatrix (EuclideanSpace.basisFun T ℂ)
  refine ⟨liftBlock T W, liftBlock_unitary T
    (b.toMatrix_orthonormalBasis_mem_unitary _), liftBlock_acts T W, ?_⟩
  intro i hi j hj
  rw [liftBlock_mul_in T W M ⟨i, hRT hi⟩ j]
  change (∑ a : T, W ⟨i, hRT hi⟩ a * v ⟨j, hj⟩ a) = 0
  rw [block_coordinates b, OrthonormalBasis.repr_apply_apply,
    show (⟨i, hRT hi⟩ : T) = f ⟨i, hi⟩ from rfl, hb]
  exact E.inner_left_of_mem_orthogonal
    (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩) (b₀ (g ⟨i, hi⟩)).property

private theorem align_block {m : ℕ} (T J : Finset (Fin m)) (hJT : J ⊆ T)
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hsupp : ∀ j ∈ J, ∀ i, i ∉ T → M i j = 0) :
    ∃ V : Matrix (Fin m) (Fin m) ℂ,
      V ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ ActsOnSubset T V ∧
        ∀ j ∈ J, ∀ i, (V * M) i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
  classical
  let v : J → EuclideanSpace ℂ T := fun j => WithLp.toLp 2 (fun i => M i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro j l
    have hs : (∑ i : T, star (M i j) * M i l) = (star M * M) j l := by
      rw [Matrix.mul_apply,
        Finset.sum_coe_sort T (fun i : Fin m => star (M i j) * M i l)]
      symm
      calc
        _ = ∑ i ∈ T, star (M i j) * M i l :=
          Finset.sum_subset T.subset_univ (by
            intro i _ hi
            simp [hsupp j j.property i hi]) |>.symm
        _ = _ := rfl
    rw [hM.1] at hs
    calc
      _ = ∑ i : T, star (M i j) * M i l := by
        simp [v, PiLp.inner_apply, RCLike.star_def, mul_comm]
      _ = _ := hs.trans (by
        by_cases hjl : j = l
        · subst hjl; simp
        · have hne : (j : Fin m) ≠ (l : Fin m) := fun hc => hjl (Subtype.ext hc)
          simp [hjl, hne])
  let f : J ↪ T := ⟨fun j => ⟨j, hJT j.property⟩, fun _ _ h =>
    Subtype.ext (congrArg (fun i : T => (i : Fin m)) h)⟩
  obtain ⟨b, hb⟩ := extend_orthonormal f v hv
  let W := b.toBasis.toMatrix (EuclideanSpace.basisFun T ℂ)
  refine ⟨liftBlock T W, liftBlock_unitary T
    (b.toMatrix_orthonormalBasis_mem_unitary _), liftBlock_acts T W, ?_⟩
  intro j hj i
  by_cases hi : i ∈ T
  · rw [liftBlock_mul_in T W M ⟨i, hi⟩ j]
    change (∑ a : T, W ⟨i, hi⟩ a * v ⟨j, hj⟩ a) = _
    rw [block_coordinates b, ← hb ⟨j, hj⟩, OrthonormalBasis.repr_self]
    simp [PiLp.single_apply, Matrix.one_apply, f, Subtype.ext_iff, eq_comm]
  · rw [acts_mul_out (liftBlock_acts T W) M hi j, hsupp j hj i hi]
    have hij : i ≠ j := fun h => hi (h ▸ hJT hj)
    simp [hij]

private theorem unitary_fixed_row {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin m) ℂ) (j : Fin m)
    (hj : ∀ i, M i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j) (i : Fin m) :
    M j i = (1 : Matrix (Fin m) (Fin m) ℂ) j i := by
  have h := congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A j i) hM.1
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    hj, Matrix.one_apply] using h

private theorem fixed_columns_mul {m : ℕ} {T J : Finset (Fin m)}
    {V M : Matrix (Fin m) (Fin m) ℂ} (hV : ActsOnSubset T V) (hJT : Disjoint J T)
    (hM : ∀ j ∈ J, ∀ i, M i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j) :
    ∀ j ∈ J, ∀ i, (V * M) i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
  classical
  intro j hj i
  have hjT : j ∉ T := Finset.disjoint_left.mp hJT hj
  have hcol : (V * M) i j = V i j := by
    simp [Matrix.mul_apply, hM j hj, Matrix.one_apply]
  rw [hcol]
  by_cases hi : i ∈ T
  · rw [hV.2.2 i j hi hjT]
    simp [show i ≠ j from fun h => hjT (h ▸ hi)]
  · exact hV.1 i j hi hjT

private theorem acts_star {m : ℕ} {T : Finset (Fin m)}
    {V : Matrix (Fin m) (Fin m) ℂ} (hV : ActsOnSubset T V) :
    ActsOnSubset T (star V) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, eq_comm] using
      congrArg star (hV.1 j i hj hi)
  · intro i j hi hj
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using
      congrArg star (hV.2.2 j i hj hi)
  · intro i j hi hj
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using
      congrArg star (hV.2.1 j i hj hi)

private theorem acts_of_fixed_columns {m : ℕ} (T : Finset (Fin m))
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hfix : ∀ j, j ∉ T → ∀ i, M i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j) :
    ActsOnSubset T M := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i j _ hj
    exact hfix j hj i
  · intro i j hi hj
    rw [unitary_fixed_row hM i (hfix i hi)]
    simp [show i ≠ j from fun h => hi (h ▸ hj)]
  · intro i j hi hj
    rw [hfix j hj]
    simp [show i ≠ j from fun h => hj (h ▸ hi)]

private theorem phase_correction {m : ℕ} (T : Finset (Fin m)) (r : Fin m) (hr : r ∈ T)
    (V : Matrix (Fin m) (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    ∃ D : Matrix (Fin m) (Fin m) ℂ,
      D ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ ActsOnSubset T D ∧ (D * V).det = 1 ∧
        ∀ (M : Matrix (Fin m) (Fin m) ℂ) i j,
          (D * M) i j = (if i = r then V.det⁻¹ else 1) * M i j := by
  classical
  let d : Fin m → ℂ := fun i => if i = r then V.det⁻¹ else 1
  let D := Matrix.diagonal d
  have hinv : V.det⁻¹ ∈ unitary ℂ := by
    rw [← Unitary.coe_inv (⟨V.det, Matrix.det_of_mem_unitary hV⟩ : unitary ℂ)]
    exact Subtype.prop _
  have hd : ∀ i, d i ∈ unitary ℂ := by
    intro i
    dsimp [d]
    split
    · exact hinv
    · exact (unitary ℂ).one_mem
  have hD : D ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    apply Matrix.diagonal_mem_unitary.mpr
    constructor <;> funext i
    · exact (hd i).1
    · exact (hd i).2
  have hacts : ActsOnSubset T D := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hi _
      have hir : i ≠ r := fun h => hi (h ▸ hr)
      simp [D, Matrix.diagonal_apply, d, hir]
    · intro i j hi hj
      simp [D, show i ≠ j from fun h => hi (h ▸ hj)]
    · intro i j hi hj
      simp [D, show i ≠ j from fun h => hj (h ▸ hi)]
  have hdetD : D.det = V.det⁻¹ := by
    simp [D, d, Matrix.det_diagonal]
  refine ⟨D, hD, hacts, ?_, ?_⟩
  · rw [Matrix.det_mul, hdetD, inv_mul_cancel₀]
    exact (Matrix.UnitaryGroup.det_isUnit ⟨V, hV⟩).ne_zero
  · intro M i j
    exact Matrix.diagonal_mul d M i j

private theorem clear_block_special {m : ℕ} (T R J : Finset (Fin m)) (hRT : R ⊆ T)
    (hR : R.Nonempty) (hcard : R.card + J.card ≤ T.card)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    ∃ V : Matrix (Fin m) (Fin m) ℂ,
      V ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ ActsOnSubset T V ∧ V.det = 1 ∧
        ∀ i ∈ R, ∀ j ∈ J, (V * M) i j = 0 := by
  obtain ⟨V, hV, hVT, hclear⟩ := clear_block T R J hRT hcard M
  obtain ⟨r, hr⟩ := hR
  obtain ⟨D, hD, hDT, hdet, hscale⟩ := phase_correction T r (hRT hr) V hV
  refine ⟨D * V, (Matrix.unitaryGroup _ _).mul_mem hD hV,
    actsOnSubset_mul hDT hVT, hdet, ?_⟩
  intro i hi j hj
  rw [Matrix.mul_assoc, hscale, hclear i hi j hj, mul_zero]

private theorem align_block_special {m : ℕ} (T J : Finset (Fin m)) (hJT : J ⊆ T)
    (r : Fin m) (hrT : r ∈ T) (hrJ : r ∉ J)
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hsupp : ∀ j ∈ J, ∀ i, i ∉ T → M i j = 0) :
    ∃ V : Matrix (Fin m) (Fin m) ℂ,
      V ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ ActsOnSubset T V ∧ V.det = 1 ∧
        ∀ j ∈ J, ∀ i, (V * M) i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j := by
  classical
  obtain ⟨V, hV, hVT, halign⟩ := align_block T J hJT M hM hsupp
  obtain ⟨D, hD, hDT, hdet, hscale⟩ := phase_correction T r hrT V hV
  refine ⟨D * V, (Matrix.unitaryGroup _ _).mul_mem hD hV,
    actsOnSubset_mul hDT hVT, hdet, ?_⟩
  intro j hj i
  rw [Matrix.mul_assoc, hscale, halign j hj i]
  by_cases hir : i = r
  · subst i
    simp [show r ≠ j from fun h => hrJ (h ▸ hj)]
  · simp [hir]

/-- Lemma 4: for `4 ∣ m`, any `m × m` special unitary matrix is a product of
seven unitaries each supported on a subset of cardinality `m / 2`. -/
theorem lemma4 (m : ℕ) (hm : 4 ∣ m) (U : Matrix (Fin m) (Fin m) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hdet : U.det = 1) :
    ∃ (S : Fin 7 → Finset (Fin m)) (Us : Fin 7 → Matrix (Fin m) (Fin m) ℂ),
      (∀ t, (S t).card = m / 2 ∧ Us t ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
        ActsOnSubset (S t) (Us t)) ∧
        U = (List.ofFn Us).prod := by
  classical
  by_cases hm0 : m = 0
  · subst m
    refine ⟨fun _ => ∅, fun _ => 1, ?_, Subsingleton.elim _ _⟩
    intro t
    exact ⟨rfl, (Matrix.unitaryGroup _ _).one_mem, actsOnSubset_one ∅⟩
  let q := m / 4
  have hmq : m = 4 * q := (Nat.mul_div_cancel' hm).symm
  have hq : 0 < q := by omega
  have hhalf : m / 2 = 2 * q := by omega
  let Q₀ := Finset.univ.filter (fun i : Fin m => i.val < q)
  let Q₁ := Finset.univ.filter (fun i : Fin m => q ≤ i.val ∧ i.val < 2 * q)
  let Q₂ := Finset.univ.filter (fun i : Fin m => 2 * q ≤ i.val ∧ i.val < 3 * q)
  let Q₃ := Finset.univ.filter (fun i : Fin m => 3 * q ≤ i.val)
  have hmem₀ (i : Fin m) : i ∈ Q₀ ↔ i.val < q := by simp [Q₀]
  have hmem₁ (i : Fin m) : i ∈ Q₁ ↔ q ≤ i.val ∧ i.val < 2 * q := by simp [Q₁]
  have hmem₂ (i : Fin m) : i ∈ Q₂ ↔ 2 * q ≤ i.val ∧ i.val < 3 * q := by simp [Q₂]
  have hmem₃ (i : Fin m) : i ∈ Q₃ ↔ 3 * q ≤ i.val := by simp [Q₃]
  have hinterval (a : ℕ) (ha : a + q ≤ m) :
      (Finset.univ.filter (fun i : Fin m => a ≤ i.val ∧ i.val < a + q)).card = q := by
    calc
      _ = (Finset.univ : Finset (Fin q)).card := by
        symm
        apply Finset.card_bij (fun i _ => (⟨a + i.val, by omega⟩ : Fin m))
        · intro i _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro i _ j _ hij
          apply Fin.ext
          have h := congrArg Fin.val hij
          dsimp at h
          omega
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          refine ⟨⟨j.val - a, by omega⟩, Finset.mem_univ _, ?_⟩
          apply Fin.ext
          dsimp
          omega
      _ = q := by simp
  have hc₀ : Q₀.card = q := by
    simpa [Q₀] using hinterval 0 (by omega)
  have hc₁ : Q₁.card = q := by
    simpa [Q₁, two_mul] using hinterval q (by omega)
  have hc₂ : Q₂.card = q := by
    have heq : Q₂ = Finset.univ.filter
        (fun i : Fin m => 2 * q ≤ i.val ∧ i.val < 2 * q + q) := by
      ext i
      simp only [hmem₂, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [heq]
    exact hinterval (2 * q) (by omega)
  have hc₃ : Q₃.card = q := by
    have heq : Q₃ = Finset.univ.filter
        (fun i : Fin m => 3 * q ≤ i.val ∧ i.val < 3 * q + q) := by
      ext i
      simp only [hmem₃, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [heq]
    exact hinterval (3 * q) (by omega)
  have hcover (i : Fin m) : i ∈ Q₀ ∨ i ∈ Q₁ ∨ i ∈ Q₂ ∨ i ∈ Q₃ := by
    simp only [hmem₀, hmem₁, hmem₂, hmem₃]
    omega
  have hd₀₁ : Disjoint Q₀ Q₁ := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [hmem₀, hmem₁] at hi hj
    omega
  have hd₁₂ : Disjoint Q₁ Q₂ := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [hmem₁, hmem₂] at hi hj
    omega
  have hd₂₃ : Disjoint Q₂ Q₃ := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [hmem₂, hmem₃] at hi hj
    omega
  have hd₃₁₂ : Disjoint Q₃ (Q₁ ∪ Q₂) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_union, hmem₁, hmem₂, hmem₃] at hi hj
    omega
  have hd₀₂₃ : Disjoint Q₀ (Q₂ ∪ Q₃) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_union, hmem₀, hmem₂, hmem₃] at hi hj
    omega
  have hd₀₁₂ : Disjoint Q₀ (Q₁ ∪ Q₂) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_union, hmem₀, hmem₁, hmem₂] at hi hj
    omega
  have hc₀₁ : (Q₀ ∪ Q₁).card = m / 2 := by
    rw [Finset.card_union_of_disjoint hd₀₁, hc₀, hc₁, hhalf]
    omega
  have hc₁₂ : (Q₁ ∪ Q₂).card = m / 2 := by
    rw [Finset.card_union_of_disjoint hd₁₂, hc₁, hc₂, hhalf]
    omega
  have hc₂₃ : (Q₂ ∪ Q₃).card = m / 2 := by
    rw [Finset.card_union_of_disjoint hd₂₃, hc₂, hc₃, hhalf]
    omega
  obtain ⟨r₁, hr₁⟩ := Finset.card_pos.mp (show 0 < Q₁.card by omega)
  obtain ⟨r₂, hr₂⟩ := Finset.card_pos.mp (show 0 < Q₂.card by omega)
  have hQ₃ : Q₃.Nonempty := Finset.card_pos.mp (by omega)
  -- Clear the first quarter of columns below the first two row blocks.
  obtain ⟨V₁, hV₁, hA₁, hD₁, hclear₁⟩ :=
    clear_block_special (Q₂ ∪ Q₃) Q₃ Q₀ Finset.subset_union_right hQ₃ (by omega) U
  let M₁ := V₁ * U
  have hM₁ : M₁ ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem hV₁ hU
  obtain ⟨V₂, hV₂, hA₂, hD₂, hclear₂⟩ :=
    clear_block_special (Q₁ ∪ Q₂) Q₂ Q₀ Finset.subset_union_right
      (Finset.card_pos.mp (by omega)) (by omega) M₁
  let M₂ := V₂ * M₁
  have hM₂ : M₂ ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem hV₂ hM₁
  have hsupp₂ : ∀ j ∈ Q₀, ∀ i, i ∉ Q₀ ∪ Q₁ → M₂ i j = 0 := by
    intro j hj i hi
    rcases hcover i with hi₀ | hi₁ | hi₂ | hi₃
    · exact (hi (Finset.mem_union_left _ hi₀)).elim
    · exact (hi (Finset.mem_union_right _ hi₁)).elim
    · exact hclear₂ i hi₂ j hj
    · change (V₂ * M₁) i j = 0
      rw [acts_mul_out hA₂ M₁ (Finset.disjoint_left.mp hd₃₁₂ hi₃) j]
      exact hclear₁ i hi₃ j hj
  -- Align those columns, using a spare coordinate for the determinant correction.
  obtain ⟨V₃, hV₃, hA₃, hD₃, hfix₃⟩ :=
    align_block_special (Q₀ ∪ Q₁) Q₀ Finset.subset_union_left r₁
      (Finset.mem_union_right _ hr₁) (Finset.disjoint_right.mp hd₀₁ hr₁) M₂ hM₂ hsupp₂
  let M₃ := V₃ * M₂
  have hM₃ : M₃ ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem hV₃ hM₂
  -- Clear and align the second quarter while preserving the fixed first quarter.
  obtain ⟨V₄, hV₄, hA₄, hD₄, hclear₄⟩ :=
    clear_block_special (Q₂ ∪ Q₃) Q₃ Q₁ Finset.subset_union_right hQ₃ (by omega) M₃
  let M₄ := V₄ * M₃
  have hM₄ : M₄ ∈ Matrix.unitaryGroup (Fin m) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem hV₄ hM₃
  have hfix₄ : ∀ j ∈ Q₀, ∀ i, M₄ i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j :=
    fixed_columns_mul hA₄ hd₀₂₃ hfix₃
  have hsupp₄ : ∀ j ∈ Q₁, ∀ i, i ∉ Q₁ ∪ Q₂ → M₄ i j = 0 := by
    intro j hj i hi
    rcases hcover i with hi₀ | hi₁ | hi₂ | hi₃
    · rw [unitary_fixed_row hM₄ i (hfix₄ i hi₀) j]
      have hij : i ≠ j := by
        rintro rfl
        exact Finset.disjoint_left.mp hd₀₁ hi₀ hj
      simp [hij]
    · exact (hi (Finset.mem_union_left _ hi₁)).elim
    · exact (hi (Finset.mem_union_right _ hi₂)).elim
    · exact hclear₄ i hi₃ j hj
  obtain ⟨V₅, hV₅, hA₅, hD₅, hfix₅₁⟩ :=
    align_block_special (Q₁ ∪ Q₂) Q₁ Finset.subset_union_left r₂
      (Finset.mem_union_right _ hr₂) (Finset.disjoint_right.mp hd₁₂ hr₂) M₄ hM₄ hsupp₄
  let M₅ := V₅ * M₄
  have hM₅ : M₅ ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ M₅.det = 1 := by
    refine ⟨(Matrix.unitaryGroup _ _).mul_mem hV₅ hM₄, ?_⟩
    simp only [M₅, M₄, M₃, M₂, M₁, Matrix.det_mul, hD₅, hD₄, hD₃, hD₂, hD₁,
      hdet, mul_one]
  have hfix₅₀ : ∀ j ∈ Q₀, ∀ i, M₅ i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j :=
    fixed_columns_mul hA₅ hd₀₁₂ hfix₄
  have hA₆ : ActsOnSubset (Q₂ ∪ Q₃) M₅ := by
    apply acts_of_fixed_columns (Q₂ ∪ Q₃) hM₅.1
    intro j hj i
    rcases hcover j with hj₀ | hj₁ | hj₂ | hj₃
    · exact hfix₅₀ j hj₀ i
    · exact hfix₅₁ j hj₁ i
    · exact (hj (Finset.mem_union_left _ hj₂)).elim
    · exact (hj (Finset.mem_union_right _ hj₃)).elim
  -- Undo the five reductions, retain the residual block, and pad with the identity.
  refine ⟨![Q₂ ∪ Q₃, Q₁ ∪ Q₂, Q₀ ∪ Q₁, Q₂ ∪ Q₃, Q₁ ∪ Q₂, Q₂ ∪ Q₃, Q₂ ∪ Q₃],
    ![star V₁, star V₂, star V₃, star V₄, star V₅, M₅, 1], ?_, ?_⟩
  · intro t
    fin_cases t
    · exact ⟨hc₂₃, Unitary.star_mem hV₁, acts_star hA₁⟩
    · exact ⟨hc₁₂, Unitary.star_mem hV₂, acts_star hA₂⟩
    · exact ⟨hc₀₁, Unitary.star_mem hV₃, acts_star hA₃⟩
    · exact ⟨hc₂₃, Unitary.star_mem hV₄, acts_star hA₄⟩
    · exact ⟨hc₁₂, Unitary.star_mem hV₅, acts_star hA₅⟩
    · exact ⟨hc₂₃, hM₅.1, hA₆⟩
    · exact ⟨hc₂₃, (Matrix.unitaryGroup _ _).one_mem, actsOnSubset_one _⟩
  · change U = star V₁ * (star V₂ * (star V₃ * (star V₄ * (star V₅ * (M₅ * (1 * 1))))))
    simp only [mul_one]
    dsimp [M₅, M₄, M₃, M₂, M₁]
    rw [← mul_assoc (star V₅) V₅, hV₅.1, one_mul,
      ← mul_assoc (star V₄) V₄, hV₄.1, one_mul,
      ← mul_assoc (star V₃) V₃, hV₃.1, one_mul,
      ← mul_assoc (star V₂) V₂, hV₂.1, one_mul,
      ← mul_assoc (star V₁) V₁, hV₁.1, one_mul]

end Qatlib.Papers.JonesPolyShor07.MainResults.HalfBasis
