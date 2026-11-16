/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.QubitBlocks
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Maps

@[expose] public section




/-!
# The pair lemma: assembly

Towards Lemma 3: a PPT map sends every PPT operator with a qubit reference to a separable
operator. This file contains the part of the argument that is independent of how the PPT
operator is decomposed:

* `isSeparable_sym`: for a PPT map `Ψ` and a positive `τ = [[T₀₀, T₀₁], [T₁₀, T₁₁]]`, the
  symmetrized image `[[Ψ(T₀₀) + Ψ(T₁₁), 2Ψ(T₀₁)], [2Ψ(T₁₀), Ψ(T₀₀) + Ψ(T₁₁)]]` is positive with
  equal diagonal blocks, hence separable by Lemma 2 (Eq. (17) of the manuscript).
* `IsSeparable.filter`: the local filter `diag(l, 1)` on the reference preserves separability
  (Eq. (18)).
* `isSeparable_refMap_of_decomposition`: Lemma 3 from the decomposition identities (14)–(15).

Lemma 2 enters through the hypothesis `hGB`, discharged in the main development. The summands of
the decomposition need not be positive; only their images are shown to be separable.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n p : Type*}

/-! ### Positive maps and pure operators -/

/-- A completely positive map sends positive operators to positive operators. -/
theorem IsCompletelyPositive.posSemidef_apply [Finite n] {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΨ : IsCompletelyPositive Ψ) {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (Ψ X).PosSemidef := by
  have hE : (Matrix.diagonal ![(1 : ℂ), 0]).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · exact zero_le_one
    · exact le_refl (0 : ℂ)
  have h := (hΨ 2 _ (hE.kronecker hX)).submatrix (fun a : p => ((0 : Fin 2), a))
  have e : (refMap (Fin 2) Ψ (Matrix.diagonal ![(1 : ℂ), 0] ⊗ₖ X)).submatrix
      (fun a : p => ((0 : Fin 2), a)) (fun a : p => ((0 : Fin 2), a)) = Ψ X := by
    rw [refMap_kronecker]
    ext a b
    simp
  rwa [e] at h

/-- `[[X, 0], [0, 0]] = |0⟩⟨0| ⊗ X` is separable for positive `X`. -/
theorem isSeparable_qubitBlocks_corner {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    IsSeparable (qubitBlocks X 0 0 0) := by
  have hE : (Matrix.diagonal ![(1 : ℂ), 0]).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · exact zero_le_one
    · exact le_refl (0 : ℂ)
  have e : Matrix.diagonal ![(1 : ℂ), 0] ⊗ₖ X = qubitBlocks X 0 0 0 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases i <;> fin_cases j <;> simp
  rw [← e]
  exact IsSeparable.kronecker hE hX

/-- The pure operator of `|0⟩ ⊗ u + |1⟩ ⊗ v`, in block form. -/
theorem qubitBlocks_pure (u v : n → ℂ) :
    qubitBlocks (vecMulVec u (star u)) (vecMulVec u (star v)) (vecMulVec v (star u))
        (vecMulVec v (star v)) =
      pureState (fun x : Fin 2 × n => (![u, v] : Fin 2 → n → ℂ) x.1 x.2) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `posSemidef_qubitBlocks_pure`: `(qubitBlocks (vecMulVec u (star u)) (vecMulVec u (star v)) (vecMulVec v (star u)) (vecMulVec v (star v))).PosSemidef`, for the stated parameters. -/
theorem posSemidef_qubitBlocks_pure [Finite n] (u v : n → ℂ) :
    (qubitBlocks (vecMulVec u (star u)) (vecMulVec u (star v)) (vecMulVec v (star u))
        (vecMulVec v (star v))).PosSemidef := by
  rw [qubitBlocks_pure]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- Establishes `conjTranspose_vecMulVec_star`: `(vecMulVec u (star v))ᴴ = vecMulVec v (star u)`, for the stated parameters. -/
theorem conjTranspose_vecMulVec_star (u v : n → ℂ) :
    (vecMulVec u (star v))ᴴ = vecMulVec v (star u) := by
  ext a b
  simp [Matrix.vecMulVec_apply, mul_comm]

/-! ### Symmetrization (Eq. (17)) -/

/-- For a PPT map `Ψ` and a positive `τ = [[T₀₀, T₀₁], [T₁₀, T₁₁]]`, the sum of `(id ⊗ Ψ)(τ)` and
its swapped partial transpose has equal diagonal blocks and is therefore separable. -/
theorem isSeparable_sym
    (hGB : ∀ D Y : Matrix p p ℂ, (qubitBlocks D Y Yᴴ D).PosSemidef →
      IsSeparable (qubitBlocks D Y Yᴴ D))
    {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsPPTMap Ψ) (T₀₀ T₀₁ T₁₀ T₁₁ : Matrix n n ℂ)
    (hτ : (qubitBlocks T₀₀ T₀₁ T₁₀ T₁₁).PosSemidef) :
    IsSeparable (qubitBlocks (Ψ T₀₀ + Ψ T₁₁) (Ψ T₀₁ + Ψ T₀₁) (Ψ T₁₀ + Ψ T₁₀)
      (Ψ T₀₀ + Ψ T₁₁)) := by
  have hH : (qubitBlocks (Ψ T₀₀) (Ψ T₀₁) (Ψ T₁₀) (Ψ T₁₁)).PosSemidef := by
    have h := hΨ.1 2 _ hτ
    rwa [refMap_qubitBlocks] at h
  have hΓ : (qubitBlocks (Ψ T₀₀) (Ψ T₁₀) (Ψ T₀₁) (Ψ T₁₁)).PosSemidef := by
    have h := hΨ.posSemidef_partialTransposeRef_refMap hτ
    rwa [refMap_qubitBlocks, partialTransposeRef_qubitBlocks] at h
  have hS : (qubitBlocks (Ψ T₁₁) (Ψ T₀₁) (Ψ T₁₀) (Ψ T₀₀)).PosSemidef := by
    have h := hΓ.submatrix (fun x : Fin 2 × p => ((![1, 0] : Fin 2 → Fin 2) x.1, x.2))
    rwa [qubitBlocks_submatrix_swap] at h
  have hsum := hH.add hS
  rw [← qubitBlocks_add] at hsum
  have hadj : Ψ T₁₀ = (Ψ T₀₁)ᴴ := by
    have h1 := hH.isHermitian.eq
    rw [conjTranspose_qubitBlocks] at h1
    have h2 := congrArg (fun X => block X 1 0) h1
    simpa using h2.symm
  have hform : qubitBlocks (Ψ T₀₀ + Ψ T₁₁) (Ψ T₀₁ + Ψ T₀₁) (Ψ T₁₀ + Ψ T₁₀) (Ψ T₀₀ + Ψ T₁₁) =
      qubitBlocks (Ψ T₀₀ + Ψ T₁₁) (Ψ T₀₁ + Ψ T₀₁) (Ψ T₀₁ + Ψ T₀₁)ᴴ (Ψ T₀₀ + Ψ T₁₁) := by
    rw [conjTranspose_add, ← hadj]
  rw [add_comm (Ψ T₁₁) (Ψ T₀₀), hform] at hsum
  rw [hform]
  exact hGB _ _ hsum

/-! ### The local filter (Eq. (18)) -/

/-- Establishes `filter_entries`: `(!![l, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * M * (!![l, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![l * star l * M 0 0, l * M 0 1; star l * M 1 0, M 1 1]`, for the stated parameters. -/
private theorem filter_entries (l : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (!![l, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * M *
        (!![l, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      !![l * star l * M 0 0, l * M 0 1; star l * M 1 0, M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

/-- Conjugating the reference by `diag(l, 1)` preserves separability. -/
theorem IsSeparable.filter (l : ℂ) {A B C D : Matrix n n ℂ}
    (h : IsSeparable (qubitBlocks A B C D)) :
    IsSeparable (qubitBlocks ((l * star l) • A) (l • B) (star l • C) D) := by
  obtain ⟨N, a, b, ha, hb, hX⟩ := h
  have hX' : qubitBlocks A B C D = qubitBlocks (∑ i, a i 0 0 • b i) (∑ i, a i 0 1 • b i)
      (∑ i, a i 1 0 • b i) (∑ i, a i 1 1 • b i) := by
    rw [hX, qubitBlocks_sum]
    exact Finset.sum_congr rfl fun i _ => kronecker_eq_qubitBlocks _ _
  have hA : A = ∑ i, a i 0 0 • b i := by simpa using congrArg (fun X => block X 0 0) hX'
  have hB : B = ∑ i, a i 0 1 • b i := by simpa using congrArg (fun X => block X 0 1) hX'
  have hC : C = ∑ i, a i 1 0 • b i := by simpa using congrArg (fun X => block X 1 0) hX'
  have hD : D = ∑ i, a i 1 1 • b i := by simpa using congrArg (fun X => block X 1 1) hX'
  have key : qubitBlocks ((l * star l) • A) (l • B) (star l • C) D =
      ∑ i, ((!![l, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) * a i *
        (!![l, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) ⊗ₖ b i := by
    rw [hA, hB, hC, hD, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, qubitBlocks_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [filter_entries, kronecker_eq_qubitBlocks]
    simp [smul_smul]
  rw [key]
  exact isSeparable_sum_kronecker _ _ (fun i => (ha i).mul_mul_conjTranspose_same _) hb

/-- The filter `diag(l, 1)` with real `l`. -/
theorem IsSeparable.filter_real (l : ℝ) {A B C D : Matrix n n ℂ}
    (h : IsSeparable (qubitBlocks A B C D)) :
    IsSeparable (qubitBlocks (((l ^ 2 : ℝ) : ℂ) • A) ((l : ℂ) • B) ((l : ℂ) • C) D) := by
  have h' := h.filter (l : ℂ)
  have e2 : star (l : ℂ) = (l : ℂ) := Complex.conj_ofReal l
  have e1 : (l : ℂ) * star (l : ℂ) = ((l ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    push_cast
    ring
  rwa [e1, e2] at h'

/-! ### Lemma 3 from the decomposition identities -/

/-- Lemma 3, given the decomposition of Eqs. (14)–(15): if `C = ∑ (P_{u_k} + P_{v_k})`,
`B = ∑ 2 λ_k u_k v_k†` and `A = R + ∑ λ_k² (P_{u_k} + P_{v_k})` with `R ≥ 0` and real `λ_k`,
then `(id₂ ⊗ Ψ)([[A, B], [B†, C]])` is separable for every PPT map `Ψ`. -/
theorem isSeparable_refMap_of_decomposition [Finite n]
    (hGB : ∀ D Y : Matrix p p ℂ, (qubitBlocks D Y Yᴴ D).PosSemidef →
      IsSeparable (qubitBlocks D Y Yᴴ D))
    {Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsPPTMap Ψ) {A B C R : Matrix n n ℂ} {N : ℕ}
    (lam : Fin N → ℝ) (u v : Fin N → n → ℂ) (hR : R.PosSemidef)
    (hC : C = ∑ k, (vecMulVec (u k) (star (u k)) + vecMulVec (v k) (star (v k))))
    (hB : B = ∑ k, ((2 * lam k : ℝ) : ℂ) • vecMulVec (u k) (star (v k)))
    (hA : A = R + ∑ k, ((lam k ^ 2 : ℝ) : ℂ) •
      (vecMulVec (u k) (star (u k)) + vecMulVec (v k) (star (v k)))) :
    IsSeparable (refMap (Fin 2) Ψ (qubitBlocks A B Bᴴ C)) := by
  have hk : ∀ k, IsSeparable (qubitBlocks
      (((lam k ^ 2 : ℝ) : ℂ) • (Ψ (vecMulVec (u k) (star (u k))) + Ψ (vecMulVec (v k) (star (v k)))))
      ((lam k : ℂ) • (Ψ (vecMulVec (u k) (star (v k))) + Ψ (vecMulVec (u k) (star (v k)))))
      ((lam k : ℂ) • (Ψ (vecMulVec (v k) (star (u k))) + Ψ (vecMulVec (v k) (star (u k)))))
      (Ψ (vecMulVec (u k) (star (u k))) + Ψ (vecMulVec (v k) (star (v k))))) := fun k =>
    (isSeparable_sym hGB hΨ _ _ _ _ (posSemidef_qubitBlocks_pure (u k) (v k))).filter_real (lam k)
  have hsep := (IsSeparable.sum Finset.univ fun k _ => hk k).add
    (isSeparable_qubitBlocks_corner (hΨ.1.posSemidef_apply hR))
  rw [← qubitBlocks_sum, ← qubitBlocks_add] at hsep
  have hBH : Bᴴ = ∑ k, ((2 * lam k : ℝ) : ℂ) • vecMulVec (v k) (star (u k)) := by
    rw [hB, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, conjTranspose_vecMulVec_star]
    congr 1
    exact Complex.conj_ofReal _
  have two : ∀ (k : Fin N) (X : Matrix p p ℂ),
      ((2 * lam k : ℝ) : ℂ) • X = (lam k : ℂ) • (X + X) := by
    intro k X
    rw [← two_smul ℂ X, smul_smul]
    congr 1
    push_cast
    ring
  have e1 : Ψ A = ∑ k, ((lam k ^ 2 : ℝ) : ℂ) •
      (Ψ (vecMulVec (u k) (star (u k))) + Ψ (vecMulVec (v k) (star (v k)))) + Ψ R := by
    rw [hA, map_add, map_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_add]
  have e2 : Ψ B = ∑ k, (lam k : ℂ) •
      (Ψ (vecMulVec (u k) (star (v k))) + Ψ (vecMulVec (u k) (star (v k)))) + 0 := by
    rw [hB, map_sum, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, two]
  have e3 : Ψ Bᴴ = ∑ k, (lam k : ℂ) •
      (Ψ (vecMulVec (v k) (star (u k))) + Ψ (vecMulVec (v k) (star (u k)))) + 0 := by
    rw [hBH, map_sum, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, two]
  have e4 : Ψ C = ∑ k,
      (Ψ (vecMulVec (u k) (star (u k))) + Ψ (vecMulVec (v k) (star (v k)))) + 0 := by
    rw [hC, map_sum, add_zero]
    exact Finset.sum_congr rfl fun k _ => map_add _ _ _
  rw [refMap_qubitBlocks, e1, e2, e3, e4]
  exact hsep

end Qatlib.Foundations.PPTMatrix.OperatorCones
