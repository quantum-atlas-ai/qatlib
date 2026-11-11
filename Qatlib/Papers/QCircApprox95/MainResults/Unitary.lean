/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCircApprox95.MainResults.ExactRepresentation
import Qatlib.Papers.QCircApprox95.MainResults.GramExtension
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Unitary completion with a fixed subspace

Starting from a matrix with orthonormal rows, the module constructs complementary rows and a
unitary matrix extending the prescribed rows. The completion fixes a subspace of dimension m −
k, with versions for both a sum-indexed coordinate space and `Fin m`. See [Knill1995].

## Main statements

* `exists_complement_rows`: constructs orthonormal complementary rows.
* `exists_kernel_isometry`: finds an isometric column family in the kernel of the prefix
  difference.
* `lemma_three_two_completion`: extends the rows to a unitary fixing an m − k dimensional
  subspace.

## References

* [Knill, 1995][Knill1995]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QCircApprox95.MainResults

/-- If `V * Vᴴ = 1`, the rows of `V`, viewed in Euclidean space, form an orthonormal family. -/
theorem rows_orthonormal_vectors {k : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (V : Matrix (Fin k) X ℂ) (hV : V * Vᴴ = 1) :
    Orthonormal ℂ (fun i : Fin k => WithLp.toLp 2 (fun j : X => V i j)) := by
  rw [orthonormal_iff_ite]
  intro i i'
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have h : (star (fun j : X => V i j)) ⬝ᵥ (fun j : X => V i' j) = (V * Vᴴ) i' i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [mul_comm]
  rw [h, hV]
  simp [Matrix.one_apply, eq_comm]

/-- A matrix with orthonormal rows on the sum-indexed coordinate space has complementary
orthonormal rows `Y` satisfying `Vᴴ * V + Yᴴ * Y = 1`. -/
theorem exists_complement_rows (k m : ℕ) (_hk : k ≤ m)
    (V : Matrix (Fin k) (Fin k ⊕ Fin (m - k)) ℂ) (hV : V * Vᴴ = 1) :
    ∃ Y : Matrix (Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ,
      Y * Yᴴ = 1 ∧ Vᴴ * V + Yᴴ * Y = 1 := by
  classical
  let emb : Fin k → (Fin k ⊕ Fin (m - k)) := Sum.inl
  have hemb : Function.Injective emb := fun a b hab => Sum.inl_injective hab
  let w : Fin k → EuclideanSpace ℂ (Fin k ⊕ Fin (m - k)) :=
    fun i => WithLp.toLp 2 (fun q => V i q)
  have hw : Orthonormal ℂ w := rows_orthonormal_vectors V hV
  let equiv : Fin k ≃ Set.range emb := Equiv.ofInjective emb hemb
  let v : (Fin k ⊕ Fin (m - k)) → EuclideanSpace ℂ (Fin k ⊕ Fin (m - k)) := fun y =>
    if hy : y ∈ Set.range emb then w (equiv.symm ⟨y, hy⟩) else 0
  have hvapp (i : Fin k) : v (emb i) = w i := by
    have he : equiv i = (⟨emb i, Set.mem_range_self i⟩ : Set.range emb) :=
      Equiv.ofInjective_apply emb hemb i
    show (if h : emb i ∈ Set.range emb then w (equiv.symm ⟨emb i, h⟩) else 0) = w i
    rw [dif_pos (Set.mem_range_self i)]
    have h2 : (⟨emb i, _⟩ : Set.range emb) = equiv i := he.symm
    rw [h2]
    exact congrArg w (equiv.symm_apply_apply i)
  have hv : Orthonormal ℂ ((Set.range emb).restrict v) := by
    have hre : (Set.range emb).restrict v = w ∘ equiv.symm := by
      funext x
      show (if x.val ∈ Set.range emb then w (equiv.symm ⟨x.val, x.property⟩) else 0)
        = w (equiv.symm x)
      exact dif_pos x.property
    rw [hre]
    exact hw.comp equiv.symm (Equiv.injective equiv.symm)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin k ⊕ Fin (m - k)))
    (ι := Fin k ⊕ Fin (m - k))
    (card_ι := finrank_euclideanSpace (𝕜 := ℂ) (ι := Fin k ⊕ Fin (m - k))) hv
  let Y : Matrix (Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ := fun r q => b (Sum.inr r) q
  have hbrow : ∀ (i : Fin k) (q : Fin k ⊕ Fin (m - k)), b (Sum.inl i) q = V i q := by
    intro i q
    rw [hb (Sum.inl i) (Set.mem_range_self i), hvapp i]

  let M : Matrix (Fin k ⊕ Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ :=
    (EuclideanSpace.basisFun (Fin k ⊕ Fin (m - k)) ℂ).toBasis.toMatrix b
  let C : Matrix (Fin k ⊕ Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ := fun j p => b j p
  have hCM : C = Mᵀ := by
    ext j p
    rfl
  have hCeq : C = Matrix.fromRows V Y := by
    ext p q
    cases p with
    | inl i => exact hbrow i q
    | inr r => rfl
  have hM1 : M * Mᴴ = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose
      (EuclideanSpace.basisFun (Fin k ⊕ Fin (m - k)) ℂ) b
  have hM2 : Mᴴ * M = 1 :=
    OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self
      (EuclideanSpace.basisFun (Fin k ⊕ Fin (m - k)) ℂ) b
  have hCorth : Cᴴ * C = 1 := by
    have h := congrArg Matrix.transpose hM1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h

    have h1 : (Mᴴ)ᵀ = Cᴴ := by rw [hCM]; rfl
    have h2 : Mᵀ = C := hCM.symm
    rw [h1, h2] at h
    exact h
  have hCorth' : C * Cᴴ = 1 := by
    have h := congrArg Matrix.transpose hM2
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    have h1 : (Mᴴ)ᵀ = Cᴴ := by rw [hCM]; rfl
    have h2 : Mᵀ = C := hCM.symm
    rw [h1, h2] at h
    exact h
  refine ⟨Y, ?_, ?_⟩
  · ext r r'
    have h := congrFun (congrFun hCorth' (Sum.inr r)) (Sum.inr r')
    simpa [C, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Sum.inr_injective.eq_iff] using h
  · rw [← hCorth]
    rw [hCeq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]

/-- The prefix coordinate projection on `Fin k ⊕ Fin (m - k)`. -/
def prefixSum (k m : ℕ) : Matrix (Fin k) (Fin k ⊕ Fin (m - k)) ℂ :=
  fun i p => if p = Sum.inl i then 1 else 0

/-- For `k ≤ m`, there is an isometric family of `m - k` columns in the kernel of `V - prefixSum
k m`. -/
theorem exists_kernel_isometry (k m : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin k ⊕ Fin (m - k)) ℂ) :
    ∃ X : Matrix (Fin k ⊕ Fin (m - k)) (Fin (m - k)) ℂ,
      Xᴴ * X = 1 ∧ (V - prefixSum k m) * X = 0 := by
  classical
  let T : Matrix (Fin k) (Fin k ⊕ Fin (m - k)) ℂ := V - prefixSum k m
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin k ⊕ Fin (m - k))) :=
    LinearMap.ker (Matrix.toEuclideanLin T)
  have hcard : Fintype.card (Fin k ⊕ Fin (m - k)) = m := by
    rw [Fintype.card_sum]
    simp [Nat.add_sub_cancel' hk]
  have hE : Module.finrank ℂ (EuclideanSpace ℂ (Fin k ⊕ Fin (m - k))) = m := by
    rw [finrank_euclideanSpace, hcard]
  have hcod : Module.finrank ℂ (EuclideanSpace ℂ (Fin k)) = k := by
    rw [finrank_euclideanSpace]
    simp
  have hrn := LinearMap.finrank_range_add_finrank_ker (f := Matrix.toEuclideanLin T)
  have hle : Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin T)) ≤ k := by
    have h := Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin T))
    rwa [hcod] at h
  have hdim : m - k ≤ Module.finrank ℂ K := by
    change m - k ≤ Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin T))
    rw [hE] at hrn
    omega
  let b : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K := stdOrthonormalBasis ℂ K
  let e : Fin (m - k) → Fin (Module.finrank ℂ K) :=
    fun s => ⟨s.val, lt_of_lt_of_le s.isLt hdim⟩
  have he : Function.Injective e := by
    intro a b hab
    have hv : a.val = b.val :=
      congrArg (fun x : Fin (Module.finrank ℂ K) => x.val) hab
    exact Fin.ext hv
  have hxorthK : Orthonormal ℂ (fun s => b (e s)) := b.orthonormal.comp e he
  have hxorth : Orthonormal ℂ
      (fun s => (b (e s) : EuclideanSpace ℂ (Fin k ⊕ Fin (m - k)))) := by
    rw [orthonormal_iff_ite]
    intro s t
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.mp hxorthK s t
  let X : Matrix (Fin k ⊕ Fin (m - k)) (Fin (m - k)) ℂ :=
    fun p s => (b (e s) : EuclideanSpace ℂ (Fin k ⊕ Fin (m - k))) p
  refine ⟨X, ?_, ?_⟩
  · ext s t
    have h := orthonormal_iff_ite.mp hxorth s t
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [X, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, dotProduct,
      mul_comm] using h
  · ext p s
    change (T * X) p s = 0
    have hkz : Matrix.toEuclideanLin T
        (b (e s) : EuclideanSpace ℂ (Fin k ⊕ Fin (m - k))) = 0 := by
      simpa using (b (e s)).2
    have hof := congrArg WithLp.ofLp hkz
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply] at hof
    have hcol : (T * X) p s =
        (T *ᵥ WithLp.ofLp (b (e s) : EuclideanSpace ℂ (Fin k ⊕ Fin (m - k)))) p := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hcol, hof]
    simp

/-- A sum-indexed matrix with orthonormal rows extends to a unitary fixing a subspace of
dimension `m - k`, and an orthonormal family `Z` of the complementary size exists. This is
the sum-indexed completion statement associated with Lemma 3.2 of [Knill1995]. -/
theorem lemma_three_two_completion_sum (k m : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin k ⊕ Fin (m - k)) ℂ) (hV : V * Vᴴ = 1) :
    ∃ (Z : Matrix (Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ)
      (W : Matrix (Fin k ⊕ Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ),
      Z * Zᴴ = 1 ∧ W ∈ Matrix.unitaryGroup (Fin k ⊕ Fin (m - k)) ℂ ∧
      (∀ (i : Fin k) (p : Fin k ⊕ Fin (m - k)), W (Sum.inl i) p = V i p) ∧
      ∃ S : Submodule ℂ (Fin k ⊕ Fin (m - k) → ℂ),
        Module.finrank ℂ S = m - k ∧ ∀ y ∈ S, W.mulVecLin y = y := by
  classical
  obtain ⟨Y, hYorth, hVY⟩ := exists_complement_rows k m hk V hV
  obtain ⟨X, hXorth, hXker⟩ := exists_kernel_isometry k m hk V
  let X1 : Matrix (Fin k) (Fin (m - k)) ℂ := fun i s => X (Sum.inl i) s
  let X2 : Matrix (Fin (m - k)) (Fin (m - k)) ℂ := fun r s => X (Sum.inr r) s
  have hXdecomp : X = Matrix.fromRows X1 X2 := by
    ext p s
    cases p <;> rfl
  have hPX : prefixSum k m * X = X1 := by
    ext i s
    rw [Matrix.mul_apply]
    simp [prefixSum, X1]
  have hVX : V * X = X1 := by
    have h := hXker
    rw [Matrix.sub_mul, sub_eq_zero] at h
    rw [h, hPX]
  have hYV : Yᴴ * Y = 1 - Vᴴ * V := by
    rw [← hVY]
    abel
  have h1 : (Y * X)ᴴ * (Y * X) = Xᴴ * (Yᴴ * Y) * X := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h2 : Xᴴ * (Yᴴ * Y) * X = Xᴴ * X - Xᴴ * (Vᴴ * V) * X := by
    rw [hYV, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  have h3 : Xᴴ * (Vᴴ * V) * X = (V * X)ᴴ * (V * X) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h4 : Xᴴ * X = X1ᴴ * X1 + X2ᴴ * X2 := by
    rw [hXdecomp, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  have h5 : X2ᴴ * X2 = 1 - X1ᴴ * X1 := by
    have h := hXorth
    rw [h4] at h
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)
  have hGram : (Y * X)ᴴ * (Y * X) = X2ᴴ * X2 := by
    rw [h1, h2, h3, hVX, h4]
    abel
  obtain ⟨U, hU, hUX⟩ := lemma_annex_one (m - k) (m - k) (Y * X) X2 hGram
  let Z : Matrix (Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ := U * Y
  let W : Matrix (Fin k ⊕ Fin (m - k)) (Fin k ⊕ Fin (m - k)) ℂ :=
    Matrix.fromRows V Z
  have hZX : Z * X = X2 := by
    show (U * Y) * X = X2
    rw [Matrix.mul_assoc, hUX]
  have hWX : W * X = X := by
    show Matrix.fromRows V Z * X = X
    rw [Matrix.fromRows_mul, hVX, hZX, ← hXdecomp]
  have hZZ : Z * Zᴴ = 1 := by
    have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    show (U * Y) * (U * Y)ᴴ = 1
    rw [Matrix.conjTranspose_mul]
    calc (U * Y) * (Yᴴ * Uᴴ) = U * (Y * Yᴴ) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * 1 * Uᴴ := by rw [hYorth]
      _ = U * Uᴴ := by rw [Matrix.mul_one]
      _ = 1 := hU2
  have hWunit : W ∈ Matrix.unitaryGroup (Fin k ⊕ Fin (m - k)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    change Wᴴ * W = 1
    show (Matrix.fromRows V Z)ᴴ * Matrix.fromRows V Z = 1
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows]
    have hZ : Zᴴ * Z = Yᴴ * Y := by
      have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
      show (U * Y)ᴴ * (U * Y) = Yᴴ * Y
      rw [Matrix.conjTranspose_mul]
      calc (Yᴴ * Uᴴ) * (U * Y) = Yᴴ * (Uᴴ * U) * Y := by
            simp only [Matrix.mul_assoc]
        _ = Yᴴ * (1 : Matrix (Fin (m - k)) (Fin (m - k)) ℂ) * Y := by rw [hU1]
        _ = Yᴴ * Y := by rw [Matrix.mul_one]
    rw [hZ, hVY]
  refine ⟨Z, W, hZZ, hWunit, ?_, ?_⟩
  · intro i p
    rfl
  · refine ⟨LinearMap.range X.mulVecLin, ?_, ?_⟩
    · have hinj : Function.Injective X.mulVecLin := by
        intro a b hab
        have h := congrArg (fun v => Xᴴ *ᵥ v) hab
        simp only [Matrix.mulVecLin_apply] at h
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hXorth,
          Matrix.one_mulVec, Matrix.one_mulVec] at h
        exact h
      rw [LinearMap.finrank_range_of_inj hinj]
      simp
    · intro y hy
      obtain ⟨z, rfl⟩ := hy
      have hcomp : W.mulVecLin.comp X.mulVecLin = X.mulVecLin := by
        rw [← Matrix.mulVecLin_mul, hWX]
      exact congrArg (fun f => f z) hcomp

/-- For `k ≤ m`, a `k`-by-`m` matrix with orthonormal rows extends to an `m`-dimensional unitary
fixing a subspace of dimension `m - k`, and an orthonormal family `Z` of the complementary
size exists. See Lemma 3.2 of [Knill1995]. -/
theorem lemma_three_two_completion (k m : ℕ) (hk : k ≤ m)
    (V : Matrix (Fin k) (Fin m) ℂ) (hV : V * Vᴴ = 1) :
    ∃ (Z : Matrix (Fin (m - k)) (Fin m) ℂ) (W : Matrix (Fin m) (Fin m) ℂ),
      Z * Zᴴ = 1 ∧ W ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
      (∀ (i : Fin k) (j : Fin m), W ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ j = V i j) ∧
      ∃ S : Submodule ℂ (Fin m → ℂ), Module.finrank ℂ S = m - k ∧
        ∀ y ∈ S, W.mulVecLin y = y := by
  classical
  have hkm : k + (m - k) = m := Nat.add_sub_cancel' hk
  let e : Fin k ⊕ Fin (m - k) ≃ Fin m :=
    (finSumFinEquiv (m := k) (n := m - k)).trans (finCongr hkm)
  let V' : Matrix (Fin k) (Fin k ⊕ Fin (m - k)) ℂ :=
    Matrix.reindex (Equiv.refl (Fin k)) e.symm V
  have hV' : V' * V'ᴴ = 1 := by
    show Matrix.reindex (Equiv.refl (Fin k)) e.symm V *
      (Matrix.reindex (Equiv.refl (Fin k)) e.symm V)ᴴ = 1
    rw [conjTranspose_reindex]
    change V.submatrix id e * Vᴴ.submatrix e id = 1
    rw [Matrix.submatrix_mul_equiv, hV, Matrix.submatrix_id_id]
  obtain ⟨Z', W', hZZ', hWunit', hWrow', S', hS'dim, hS'fix⟩ :=
    lemma_three_two_completion_sum k m hk V' hV'
  let Z : Matrix (Fin (m - k)) (Fin m) ℂ :=
    Matrix.reindex (Equiv.refl (Fin (m - k))) e Z'
  let W : Matrix (Fin m) (Fin m) ℂ := Matrix.reindex e e W'
  have hZZ : Z * Zᴴ = 1 := by
    show Matrix.reindex (Equiv.refl (Fin (m - k))) e Z' *
      (Matrix.reindex (Equiv.refl (Fin (m - k))) e Z')ᴴ = 1
    rw [conjTranspose_reindex]
    change Z'.submatrix id e.symm * Z'ᴴ.submatrix e.symm id = 1
    rw [Matrix.submatrix_mul_equiv, hZZ', Matrix.submatrix_id_id]
  have hWW' : W' * W'ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hWunit'
    simpa [Matrix.star_eq_conjTranspose] using h
  have hWW : W * Wᴴ = 1 := by
    show Matrix.reindex e e W' * (Matrix.reindex e e W')ᴴ = 1
    rw [conjTranspose_reindex]
    change W'.submatrix e.symm e.symm * W'ᴴ.submatrix e.symm e.symm = 1
    rw [Matrix.submatrix_mul_equiv, hWW', Matrix.submatrix_one_equiv]
  have hWunit : W ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hWW
  have heinl : ∀ i : Fin k, e (Sum.inl i) = ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ := by
    intro i
    apply Fin.ext
    simp [e, finSumFinEquiv]
  have hrow : ∀ (i : Fin k) (j : Fin m),
      W ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ j = V i j := by
    intro i j
    have hsymm : e.symm ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ = Sum.inl i := by
      rw [Equiv.symm_apply_eq]
      exact (heinl i).symm
    show W' (e.symm ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) (e.symm j) = V i j
    rw [hsymm, hWrow' i (e.symm j)]
    show V i (e (e.symm j)) = V i j
    rw [Equiv.apply_symm_apply]
  refine ⟨Z, W, hZZ, hWunit, hrow, ?_⟩
  refine ⟨S'.map (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hS'dim
  · intro y hy
    obtain ⟨z, hzS, rfl⟩ := Submodule.mem_map.mp hy
    have hcancel :
        (LinearEquiv.funCongrLeft ℂ ℂ e) ((LinearEquiv.funCongrLeft ℂ ℂ e.symm) z) = z := by
      have h := LinearEquiv.symm_apply_apply (LinearEquiv.funCongrLeft ℂ ℂ e.symm) z
      rwa [LinearEquiv.funCongrLeft_symm] at h
    rw [Matrix.mulVecLin_reindex]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hcancel, hS'fix z hzS]

end Qatlib.Papers.QCircApprox95.MainResults
