/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KikuchiMaxCut26.MainResults.SpectralOrder
import Mathlib.Combinatorics.SimpleGraph.IncMatrix

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2.2: adjacency eigenvalue bounds from the signed/signless Laplacian

Bakshi--Basu--Kothari--Li, *Sharp Bounds on the Eigenvalues of Kikuchi Graphs and
Applications to Quantum Max Cut*, fixed arXiv:2605.14994v1 (2026-05-14).
PDF SHA-256 fa5c3dd53c547fa65041c7f2b8f96fcb55cc3370746c787f54e7961abdb03afc.

The paper states (Proposition 2.2, page 3): for any graph `G` and level `k`,

  `-(1/2) · λmax(L_G^(k)) ≤ λmin(A_G^(k)) ≤ λmax(A_G^(k)) ≤ (1/2) · λmax(Q_G^(k))`,

where `L_G^(k) = D - A` is the signed Laplacian and `Q_G^(k) = D + A` the signless one.
The paper's proof uses the Loewner order: from `Q - L = 2A`, positivity of `L`, and
positivity of `Q` it reads off `A ≼ (1/2) Q` and `A ≽ -(1/2) L`.

We record the argument as an abstract matrix proposition (`proposition_2_2`) whose
hypotheses are exactly the ones the paper uses, and prove it using the Rayleigh-quotient
bounds and Loewner monotonicity of `SpectralOrder.lean` (Mathlib at the pinned revision
has neither).  The Kikuchi instantiation (`proposition_2_2_kikuchi`) then supplies
`Q - L = 2A` (`signless_sub_lap`), positivity of `L` (`lapMatrix_posSemidef`) and
positivity of `Q` (`signlessMatrix_posSemidef`, proved here from the incidence-matrix
factorisation `D + A = B Bᵀ`).

Boundary: this file adds the paper-layer Proposition 2.2 only; the abstract part is a
general linear-algebra statement with no paper-specific hypotheses.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KikuchiMaxCut26.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Abstract Proposition 2.2 -/

/-- **Proposition 2.2** (arXiv:2605.14994v1, page 3), abstract form.

Let `A`, `L`, `Q` be Hermitian matrices with `L` and `Q` positive semidefinite and
`Q - L = 2 • A`.  Then

  `-(1/2) λmax(L) ≤ λmin(A) ≤ λmax(A) ≤ (1/2) λmax(Q)`.

The proof follows the paper: on one hand `A = (Q - L)/2`, so evaluating the quadratic
form `xᵀAx` at a unit eigenvector of `A` for `λmax` and using `xᵀQx ≤ λmax(Q)` and
`xᵀLx ≥ 0` gives the upper bound; evaluating at a unit eigenvector for `λmin` and using
`xᵀQx ≥ 0` and `xᵀLx ≤ λmax(L)` gives the lower bound.  The middle inequality is the
Rayleigh lower bound at the `λmax` eigenvector. -/
theorem proposition_2_2 (A L Q : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hL : L.IsHermitian) (hQ : Q.IsHermitian)
    (hLpsd : L.PosSemidef) (hQpsd : Q.PosSemidef) (hrel : Q - L = (2 : ℝ) • A) :
    -(1 / 2) * lamMax L hL ≤ lamMin A hA ∧
      lamMin A hA ≤ lamMax A hA ∧
      lamMax A hA ≤ (1 / 2) * lamMax Q hQ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    simp [lamMax, lamMin]
  · have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    -- `Q - L = 2 • A` reads `xᵀQx - xᵀLx = 2 xᵀAx`
    have hident : ∀ x : ι → ℝ,
        x ⬝ᵥ (A *ᵥ x) = (x ⬝ᵥ (Q *ᵥ x) - x ⬝ᵥ (L *ᵥ x)) / 2 := by
      intro x
      have h := congrArg (fun M : Matrix ι ι ℝ => x ⬝ᵥ (M *ᵥ x)) hrel
      simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
        dotProduct_smul] at h
      rw [two_smul ℝ] at h
      linarith
    have hQnonneg : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (Q *ᵥ x) := fun x => by
      have h := hQpsd.dotProduct_mulVec_nonneg x
      simpa [star_trivial] using h
    have hLnonneg : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (L *ᵥ x) := fun x => by
      have h := hLpsd.dotProduct_mulVec_nonneg x
      simpa [star_trivial] using h
    -- upper bound: `λmax(A) ≤ (1/2) λmax(Q)`
    have hub : lamMax A hA ≤ (1 / 2) * lamMax Q hQ := by
      obtain ⟨x, hx1, hxA⟩ := exists_eigenvector_lamMax A hA hcard
      have hQbound : x ⬝ᵥ (Q *ᵥ x) ≤ lamMax Q hQ := by
        have h := dotProduct_mulVec_le_lamMax Q hQ x
        rwa [hx1, mul_one] at h
      have hL0 := hLnonneg x
      rw [hxA, hident x]
      linarith
    -- lower bound: `-(1/2) λmax(L) ≤ λmin(A)`
    have hlb : -(1 / 2) * lamMax L hL ≤ lamMin A hA := by
      obtain ⟨x, hx1, hxA⟩ := exists_eigenvector_lamMin A hA hcard
      have hLbound : x ⬝ᵥ (L *ᵥ x) ≤ lamMax L hL := by
        have h := dotProduct_mulVec_le_lamMax L hL x
        rwa [hx1, mul_one] at h
      have hQ0 := hQnonneg x
      rw [hxA, hident x]
      linarith
    -- middle inequality: `λmin(A) ≤ λmax(A)`
    have hmid : lamMin A hA ≤ lamMax A hA := by
      obtain ⟨x, hx1, hxA⟩ := exists_eigenvector_lamMax A hA hcard
      have h := lamMin_le_dotProduct_mulVec A hA x
      rw [hx1, mul_one] at h
      linarith
    exact ⟨hlb, hmid, hub⟩

/-! ## The Kikuchi adjacency matrix: Hermitian and signless Laplacian positivity -/

variable {n : ℕ}

/-- The adjacency matrix `A_G^(k)` of the level-`k` Kikuchi graph is Hermitian
(Definition 2.1, arXiv:2605.14994v1, page 3). -/
theorem adjMatrix_isHermitian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (adjMatrix G k).IsHermitian := by
  classical
  simp only [adjMatrix]
  exact SimpleGraph.isHermitian_adjMatrix (G := kikuchiGraph G k) ℝ

/-- The signless Laplacian `Q_G^(k) = D_G^(k) + A_G^(k)` is Hermitian
(Definition 2.1, arXiv:2605.14994v1, page 3). -/
theorem signlessMatrix_isHermitian (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (signlessMatrix G k).IsHermitian := by
  classical
  simp only [signlessMatrix, degMatrix, adjMatrix]
  exact (SimpleGraph.isHermitian_degMatrix ℝ (G := kikuchiGraph G k)).add
    (SimpleGraph.isHermitian_adjMatrix ℝ (G := kikuchiGraph G k))

/-- The signless Laplacian `Q_G^(k) = D_G^(k) + A_G^(k)` is positive semidefinite.

Mathlib has `SimpleGraph.posSemidef_lapMatrix` for `D - A`, but not for `D + A`.  We use
the oriented incidence-matrix factorisation `D + A = B Bᵀ`
(`SimpleGraph.incMatrix_mul_transpose`) together with the general fact that `X Xᵀ` is
positive semidefinite (`Matrix.posSemidef_self_mul_conjTranspose`).

This is the positivity of `Q_G^(k)` used in the proof of Proposition 2.2,
arXiv:2605.14994v1, page 3. -/
theorem signlessMatrix_posSemidef (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    (signlessMatrix G k).PosSemidef := by
  classical
  have hEq : signlessMatrix G k = Matrix.of (fun S T : KSub (Fin n) k =>
      if S = T then ((kikuchiGraph G k).degree S : ℝ)
      else if (kikuchiGraph G k).Adj S T then 1 else 0) := by
    ext S T
    simp only [signlessMatrix, degMatrix, adjMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix, Matrix.add_apply, Matrix.of_apply]
    by_cases hST : S = T
    · subst hST
      rw [Matrix.diagonal_apply_eq]
      simp
    · rw [Matrix.diagonal_apply_ne _ hST]
      simp [hST]
  have hEq2 : signlessMatrix G k =
      (kikuchiGraph G k).incMatrix ℝ * ((kikuchiGraph G k).incMatrix ℝ)ᵀ := by
    rw [hEq, SimpleGraph.incMatrix_mul_transpose]
  rw [hEq2]
  simpa using Matrix.posSemidef_self_mul_conjTranspose ((kikuchiGraph G k).incMatrix ℝ)

/-! ## Concrete Proposition 2.2 for Kikuchi graphs -/

/-- **Proposition 2.2** for Kikuchi graphs (arXiv:2605.14994v1, page 3):

  `-(1/2) λmax(L_G^(k)) ≤ λmin(A_G^(k)) ≤ λmax(A_G^(k)) ≤ (1/2) λmax(Q_G^(k))`. -/
theorem proposition_2_2_kikuchi (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    -(1 / 2) * lamMax (lapMatrix G k) (lapMatrix_isHermitian G k) ≤
        lamMin (adjMatrix G k) (adjMatrix_isHermitian G k) ∧
      lamMin (adjMatrix G k) (adjMatrix_isHermitian G k) ≤
        lamMax (adjMatrix G k) (adjMatrix_isHermitian G k) ∧
      lamMax (adjMatrix G k) (adjMatrix_isHermitian G k) ≤
        (1 / 2) * lamMax (signlessMatrix G k) (signlessMatrix_isHermitian G k) :=
  proposition_2_2 (adjMatrix G k) (lapMatrix G k) (signlessMatrix G k)
    (adjMatrix_isHermitian G k) (lapMatrix_isHermitian G k) (signlessMatrix_isHermitian G k)
    (lapMatrix_posSemidef G k) (signlessMatrix_posSemidef G k) (signless_sub_lap G k)

end Qatlib.Papers.KikuchiMaxCut26.MainResults
