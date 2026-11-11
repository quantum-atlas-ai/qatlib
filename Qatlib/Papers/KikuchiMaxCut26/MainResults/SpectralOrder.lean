/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KikuchiMaxCut26.MainResults.Definitions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false

/-!
# Rayleigh quotient bounds and Loewner monotonicity of extreme eigenvalues

Bakshi--Basu--Kothari--Li, *Sharp Bounds on the Eigenvalues of Kikuchi Graphs and
Applications to Quantum Max Cut*, fixed arXiv:2605.14994v1 (2026-05-14).
PDF SHA-256 fa5c3dd53c547fa65041c7f2b8f96fcb55cc3370746c787f54e7961abdb03afc.

The paper's Proposition 2.2 (page 3) uses two standard facts about Hermitian matrices:

* for every vector `x`, `⟨x, A x⟩ ≤ λmax(A) ‖x‖²` (Rayleigh quotient upper bound), and
* the Loewner order is monotone for extreme eigenvalues: `A ≼ B` implies
  `λmax(A) ≤ λmax(B)` and `λmin(A) ≤ λmin(B)`.

neither of which is available in Mathlib at the pinned revision.  This file proves them from
Mathlib's spectral theorem for Hermitian matrices (`Matrix.IsHermitian.eigenvectorBasis` and
`LinearMap.IsSymmetric.apply_eigenvectorBasis`) by expanding an arbitrary vector in the
orthonormal eigenbasis of the matrix.  They are the reusable analytic core of the paper-layer
proof of Proposition 2.2.

Boundary: this file proves only general linear-algebra facts; it imports no paper-specific
notion and introduces no axioms.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators RealInnerProductSpace
open Matrix

namespace Qatlib.Papers.KikuchiMaxCut26.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The index identification `Fin (card ι) ≃ ι` underlying `IsHermitian.eigenvalues`; it is the
equivalence Mathlib uses to reindex `eigenvalues₀` by the matrix index type. -/
def eigEquiv (ι : Type*) [Fintype ι] : Fin (Fintype.card ι) ≃ ι :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/-- `IsHermitian.eigenvalues` is `eigenvalues₀` reindexed by `eigEquiv`. -/
theorem eigenvalues_eq_eigenvalues₀_comp (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (i : ι) :
    hA.eigenvalues i = hA.eigenvalues₀ ((eigEquiv ι).symm i) := rfl

/-- **Rayleigh quotient upper bound.** For a Hermitian matrix `A` and every real vector `x`,
`x ⬝ᵥ (A *ᵥ x) ≤ λmax(A) * (x ⬝ᵥ x)`.

This is the analytic ingredient of the second inequality of Proposition 2.2,
arXiv:2605.14994v1, page 3.  It is proved by expanding `x` in an orthonormal eigenbasis of
`A`, where the quadratic form becomes `∑ᵢ λᵢ cᵢ² ≤ λmax · ∑ᵢ cᵢ²`. -/
theorem dotProduct_mulVec_le_lamMax (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ lamMax A hA * (x ⬝ᵥ x) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    have hx : x = 0 := funext (fun i => isEmptyElim i)
    rw [hx]
    simp [lamMax]
  · have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    let T := Matrix.toEuclideanLin A
    have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
    let b := hT.eigenvectorBasis hdim
    let lam : Fin (Fintype.card ι) → ℝ := hT.eigenvalues hdim
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 x
    have hlam0 : lamMax A hA = lam ⟨0, Nat.pos_of_ne_zero hcard⟩ := by
      rw [lamMax_eq A hA hcard]
      rfl
    have hle : ∀ i : Fin (Fintype.card ι), lam i ≤ lam ⟨0, Nat.pos_of_ne_zero hcard⟩ := fun i =>
      hT.eigenvalues_antitone hdim (Fin.zero_le i)
    have hquad : x ⬝ᵥ (A *ᵥ x) = ∑ i, lam i * (b.repr v i) ^ 2 := by
      have h1 : x ⬝ᵥ (A *ᵥ x) = inner ℝ v (T v) := by
        have hto : T v = WithLp.toLp 2 (A *ᵥ x) := rfl
        rw [hto, EuclideanSpace.inner_toLp_toLp]
        simp [v, star_trivial, dotProduct_comm]
      rw [h1]
      calc inner ℝ v (T v) = ∑ i, inner ℝ v (b i) * inner ℝ (b i) (T v) :=
              (b.sum_inner_mul_inner v (T v)).symm
        _ = ∑ i, (b.repr v i) * (lam i * b.repr v i) := by
              apply Finset.sum_congr rfl
              intro i _
              have e1 : inner ℝ v (b i) = b.repr v i :=
                (real_inner_comm v (b i)).symm.trans
                  (OrthonormalBasis.repr_apply_apply b v i).symm
              have e2 : inner ℝ (b i) (T v) = lam i * b.repr v i := by
                rw [show inner ℝ (b i) (T v) = b.repr (T v) i from
                  (OrthonormalBasis.repr_apply_apply b (T v) i).symm]
                exact LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply hT hdim v i
              rw [e1, e2]
        _ = ∑ i, lam i * (b.repr v i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              ring_nf
    have hsum_sq : (∑ i, (b.repr v i) ^ 2) = x ⬝ᵥ x := by
      calc ∑ i, (b.repr v i) ^ 2 = ∑ i, inner ℝ v (b i) * inner ℝ (b i) v := by
              apply Finset.sum_congr rfl
              intro i _
              have e1 : inner ℝ v (b i) = b.repr v i :=
                (real_inner_comm v (b i)).symm.trans
                  (OrthonormalBasis.repr_apply_apply b v i).symm
              have e2 : inner ℝ (b i) v = b.repr v i :=
                (OrthonormalBasis.repr_apply_apply b v i).symm
              rw [e1, e2]
              ring
        _ = inner ℝ v v := b.sum_inner_mul_inner v v
        _ = x ⬝ᵥ x := by
              rw [EuclideanSpace.inner_toLp_toLp]
              simp [v, star_trivial]
    calc x ⬝ᵥ (A *ᵥ x) = ∑ i, lam i * (b.repr v i) ^ 2 := hquad
      _ ≤ lam ⟨0, Nat.pos_of_ne_zero hcard⟩ * ∑ i, (b.repr v i) ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
      _ = lamMax A hA * (x ⬝ᵥ x) := by
            rw [hlam0, hsum_sq]


/-- **Rayleigh quotient lower bound.** For a Hermitian matrix `A` and every real vector `x`,
`λmin(A) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)`.

This is the analytic ingredient of the first inequality of Proposition 2.2,
arXiv:2605.14994v1, page 3. -/
theorem lamMin_le_dotProduct_mulVec (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) :
    lamMin A hA * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    have hx : x = 0 := funext (fun i => isEmptyElim i)
    rw [hx]
    simp [lamMin]
  · have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    let T := Matrix.toEuclideanLin A
    have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
    let b := hT.eigenvectorBasis hdim
    let lam : Fin (Fintype.card ι) → ℝ := hT.eigenvalues hdim
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 x
    let ilast : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
    have hlamlast : lamMin A hA = lam ilast := by
      rw [lamMin_eq A hA hcard]
      rfl
    have hle : ∀ i : Fin (Fintype.card ι), lam ilast ≤ lam i := by
      intro i
      refine hT.eigenvalues_antitone hdim ?_
      rw [Fin.le_def]
      have := i.isLt
      simp [ilast]
      omega
    have hquad : x ⬝ᵥ (A *ᵥ x) = ∑ i, lam i * (b.repr v i) ^ 2 := by
      have h1 : x ⬝ᵥ (A *ᵥ x) = inner ℝ v (T v) := by
        have hto : T v = WithLp.toLp 2 (A *ᵥ x) := rfl
        rw [hto, EuclideanSpace.inner_toLp_toLp]
        simp [star_trivial, dotProduct_comm]
      rw [h1]
      calc inner ℝ v (T v) = ∑ i, inner ℝ v (b i) * inner ℝ (b i) (T v) :=
              (b.sum_inner_mul_inner v (T v)).symm
        _ = ∑ i, (b.repr v i) * (lam i * b.repr v i) := by
              apply Finset.sum_congr rfl
              intro i _
              have e1 : inner ℝ v (b i) = b.repr v i :=
                (real_inner_comm v (b i)).symm.trans
                  (OrthonormalBasis.repr_apply_apply b v i).symm
              have e2 : inner ℝ (b i) (T v) = lam i * b.repr v i := by
                rw [show inner ℝ (b i) (T v) = b.repr (T v) i from
                  (OrthonormalBasis.repr_apply_apply b (T v) i).symm]
                exact LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply hT hdim v i
              rw [e1, e2]
        _ = ∑ i, lam i * (b.repr v i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              ring_nf
    have hsum_sq : (∑ i, (b.repr v i) ^ 2) = x ⬝ᵥ x := by
      calc ∑ i, (b.repr v i) ^ 2 = ∑ i, inner ℝ v (b i) * inner ℝ (b i) v := by
              apply Finset.sum_congr rfl
              intro i _
              have e1 : inner ℝ v (b i) = b.repr v i :=
                (real_inner_comm v (b i)).symm.trans
                  (OrthonormalBasis.repr_apply_apply b v i).symm
              have e2 : inner ℝ (b i) v = b.repr v i :=
                (OrthonormalBasis.repr_apply_apply b v i).symm
              rw [e1, e2]
              ring
        _ = inner ℝ v v := b.sum_inner_mul_inner v v
        _ = x ⬝ᵥ x := by
              rw [EuclideanSpace.inner_toLp_toLp]
              simp [star_trivial]
    calc lamMin A hA * (x ⬝ᵥ x) = lam ilast * ∑ i, (b.repr v i) ^ 2 := by
            rw [hlamlast, ← hsum_sq]
      _ = ∑ i, lam ilast * (b.repr v i) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, lam i * (b.repr v i) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
      _ = x ⬝ᵥ (A *ᵥ x) := hquad.symm

/-- A unit eigenvector attaining `λmax`, in coordinates: there is `x` with `x ⬝ᵥ x = 1` and
`λmax(A) = x ⬝ᵥ (A *ᵥ x)`. -/
theorem exists_eigenvector_lamMax (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (h : Fintype.card ι ≠ 0) :
    ∃ x : ι → ℝ, x ⬝ᵥ x = 1 ∧ lamMax A hA = x ⬝ᵥ (A *ᵥ x) := by
  classical
  let i0 : ι := (eigEquiv ι) ⟨0, Nat.pos_of_ne_zero h⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis i0), ?_, ?_⟩
  · have hb : ‖hA.eigenvectorBasis i0‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i0
    have hb2 : inner ℝ (hA.eigenvectorBasis i0) (hA.eigenvectorBasis i0) = 1 := by
      rw [real_inner_self_eq_norm_sq, hb]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hb2
    simpa [star_trivial] using hb2
  · rw [lamMax_eq A hA h]
    have hi : (eigEquiv ι).symm i0 = ⟨0, Nat.pos_of_ne_zero h⟩ := by
      dsimp only [i0]
      simp
    have hcomp := eigenvalues_eq_eigenvalues₀_comp A hA i0
    rw [hi] at hcomp
    rw [← hcomp, hA.eigenvalues_eq i0]
    simp [star_trivial]

/-- A unit eigenvector attaining `λmin`, in coordinates. -/
theorem exists_eigenvector_lamMin (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (h : Fintype.card ι ≠ 0) :
    ∃ x : ι → ℝ, x ⬝ᵥ x = 1 ∧ lamMin A hA = x ⬝ᵥ (A *ᵥ x) := by
  classical
  let i0 : ι := (eigEquiv ι) ⟨Fintype.card ι - 1, by omega⟩
  refine ⟨WithLp.ofLp (hA.eigenvectorBasis i0), ?_, ?_⟩
  · have hb : ‖hA.eigenvectorBasis i0‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i0
    have hb2 : inner ℝ (hA.eigenvectorBasis i0) (hA.eigenvectorBasis i0) = 1 := by
      rw [real_inner_self_eq_norm_sq, hb]
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hb2
    simpa [star_trivial] using hb2
  · rw [lamMin_eq A hA h]
    have hi : (eigEquiv ι).symm i0 = ⟨Fintype.card ι - 1, by omega⟩ := by
      dsimp only [i0]
      simp
    have hcomp := eigenvalues_eq_eigenvalues₀_comp A hA i0
    rw [hi] at hcomp
    rw [← hcomp, hA.eigenvalues_eq i0]
    simp [star_trivial]

/-- **Loewner monotonicity of `λmax`.** If `B - A` is positive semidefinite, then
`λmax(A) ≤ λmax(B)`. -/
theorem lamMax_mono {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) : lamMax A hA ≤ lamMax B hB := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    simp [lamMax]
  · have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    obtain ⟨x, hx1, hxA⟩ := exists_eigenvector_lamMax A hA hcard
    have hq : x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
      have h := hAB.dotProduct_mulVec_nonneg x
      rw [star_trivial, sub_mulVec, dotProduct_sub] at h
      linarith
    calc lamMax A hA = x ⬝ᵥ (A *ᵥ x) := hxA
      _ ≤ x ⬝ᵥ (B *ᵥ x) := hq
      _ ≤ lamMax B hB * (x ⬝ᵥ x) := dotProduct_mulVec_le_lamMax B hB x
      _ = lamMax B hB := by rw [hx1, mul_one]

/-- **Loewner monotonicity of `λmin`.** If `B - A` is positive semidefinite, then
`λmin(A) ≤ λmin(B)`. -/
theorem lamMin_mono {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (B - A).PosSemidef) : lamMin A hA ≤ lamMin B hB := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    simp [lamMin]
  · have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    obtain ⟨x, hx1, hxB⟩ := exists_eigenvector_lamMin B hB hcard
    have hq : x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
      have h := hAB.dotProduct_mulVec_nonneg x
      rw [star_trivial, sub_mulVec, dotProduct_sub] at h
      linarith
    calc lamMin A hA = lamMin A hA * (x ⬝ᵥ x) := by rw [hx1, mul_one]
      _ ≤ x ⬝ᵥ (A *ᵥ x) := lamMin_le_dotProduct_mulVec A hA x
      _ ≤ x ⬝ᵥ (B *ᵥ x) := hq
      _ = lamMin B hB := hxB.symm

end Qatlib.Papers.KikuchiMaxCut26.MainResults
