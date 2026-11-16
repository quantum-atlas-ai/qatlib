/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.SVDComponents

@[expose] public section




/-!
# The literal PPT support-SVD witnesses, positive remainder, and decomposition.

A supported singular decomposition of the normalized off-diagonal block supplies finite singular values and two complete support bases. The lifted vectors satisfy the three exact component identities needed to decompose a qubit-reference PPT operator, without asserting that each component is itself positive.
-/

open Matrix
open scoped ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The literal manuscript witnesses are simultaneous: the same complete
support singular bases define p,q,D, all three Eq.(14) identities and the
positive Eq.(10) reserve used in Eq.(15). Only the two PPT block positivity
premises are assumed. All rank(C) slots, including zero singular values and
rank(C)=0, are retained. -/
theorem exists_ppt_svd_component_witnesses {A B C : Matrix n n ℂ}
    (h₁ : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (h₂ : (Matrix.fromBlocks A Bᴴ B C).PosSemidef) :
    ∃ (U V : Matrix n (Fin C.rank) ℂ) (s : Fin C.rank → ℝ),
      let p : Fin C.rank → n → ℂ := fun j => psqrt C *ᵥ Uᵀ j
      let q : Fin C.rank → n → ℂ := fun j => psqrt C *ᵥ Vᵀ j
      let D : Fin C.rank → Matrix n n ℂ := fun j => (1 / 2 : ℂ) •
        (vecMulVec (p j) (star (p j)) + vecMulVec (q j) (star (q j)))
      let R : Matrix n n ℂ := A - (1 / 2 : ℂ) •
        (B * pinv C * Bᴴ + Bᴴ * pinv C * B)
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      U * Uᴴ = C * pinv C ∧ V * Vᴴ = C * pinv C ∧
      (∀ j, 0 ≤ s j) ∧
      pinvSqrt C * B * pinvSqrt C = U * diagonal (fun j => (s j : ℂ)) * Vᴴ ∧
      R.PosSemidef ∧
      (∑ j, D j) = C ∧
      (∑ j, (s j : ℂ) • vecMulVec (p j) (star (q j))) = B ∧
      (∑ j, ((s j ^ 2 : ℝ) : ℂ) • D j) =
        (1 / 2 : ℂ) • (B * pinv C * Bᴴ + Bᴴ * pinv C * B) ∧
      A = R + ∑ j, ((s j ^ 2 : ℝ) : ℂ) • D j ∧
      Matrix.fromBlocks A B Bᴴ C = Matrix.fromBlocks R 0 0 0 +
        ∑ j, Matrix.fromBlocks (((s j ^ 2 : ℝ) : ℂ) • D j)
          ((s j : ℂ) • vecMulVec (p j) (star (q j)))
          ((s j : ℂ) • vecMulVec (q j) (star (p j))) (D j) := by
  obtain ⟨hC, hBP, hS₁⟩ := posSemidef_fromBlocks_pinv h₁
  have h₂' : (Matrix.fromBlocks A Bᴴ Bᴴᴴ C).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using h₂
  obtain ⟨_, hB'P, hS₂⟩ := posSemidef_fromBlocks_pinv h₂'
  rw [Matrix.conjTranspose_conjTranspose] at hS₂
  have hP : (C * pinv C)ᴴ = C * pinv C := (isHermitian_mul_pinv hC.isHermitian).eq
  have hPB : C * pinv C * B = B := by
    have h := congrArg Matrix.conjTranspose hB'P
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP] using h
  obtain ⟨U, V, s, hU, hV, hUU, hVV, hs, hsvd⟩ := exists_supported_svd B C hC
  let p : Fin C.rank → n → ℂ := fun j => psqrt C *ᵥ Uᵀ j
  let q : Fin C.rank → n → ℂ := fun j => psqrt C *ᵥ Vᵀ j
  let D : Fin C.rank → Matrix n n ℂ := fun j => (1 / 2 : ℂ) •
    (vecMulVec (p j) (star (p j)) + vecMulVec (q j) (star (q j)))
  let R : Matrix n n ℂ := A - (1 / 2 : ℂ) •
    (B * pinv C * Bᴴ + Bᴴ * pinv C * B)
  have hid := supported_svd_component_identities B C U V s hC hU hV hUU hVV hPB hBP hsvd
  change (∑ j, D j) = C ∧
    (∑ j, (s j : ℂ) • vecMulVec (p j) (star (q j))) = B ∧
    (∑ j, ((s j ^ 2 : ℝ) : ℂ) • D j) =
      (1 / 2 : ℂ) • (B * pinv C * Bᴴ + Bᴴ * pinv C * B) at hid
  have hR : R.PosSemidef := by
    have hhalf : (0 : ℂ) ≤ 1 / 2 := by
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        using (Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num))
    have h := (hS₁.add hS₂).smul hhalf
    have heq : (1 / 2 : ℂ) •
        ((A - B * pinv C * Bᴴ) + (A - Bᴴ * pinv C * B)) = R := by
      ext i j
      dsimp only [R]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rw [heq] at h
    exact h
  have hA : A = R + ∑ j, ((s j ^ 2 : ℝ) : ℂ) • D j := by
    rw [hid.2.2]
    exact (sub_add_cancel A _).symm
  have hBstar : (∑ j, (s j : ℂ) • vecMulVec (q j) (star (p j))) = Bᴴ := by
    have h := congrArg Matrix.conjTranspose hid.2.1
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_vecMulVec, star_star, Complex.star_def, Complex.conj_ofReal] using h
  have hdecomp : Matrix.fromBlocks A B Bᴴ C = Matrix.fromBlocks R 0 0 0 +
      ∑ j, Matrix.fromBlocks (((s j ^ 2 : ℝ) : ℂ) • D j)
        ((s j : ℂ) • vecMulVec (p j) (star (q j)))
        ((s j : ℂ) • vecMulVec (q j) (star (p j))) (D j) := by
    ext x y
    rcases x with i | i <;> rcases y with j | j
    · simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.fromBlocks_apply₁₁]
        using congrFun (congrFun hA i) j
    · simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, zero_add] using congrFun (congrFun hid.2.1.symm i) j
    · simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, zero_add] using congrFun (congrFun hBstar.symm i) j
    · simpa only [Matrix.add_apply, Matrix.sum_apply, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, zero_add] using congrFun (congrFun hid.1.symm i) j
  exact ⟨U, V, s, hU, hV, hUU, hVV, hs, hsvd, hR,
    hid.1, hid.2.1, hid.2.2, hA, hdecomp⟩

/-- The unchanged375 interface, now a corollary of the simultaneous literal
witness theorem rather than an independent construction. -/
theorem exists_ppt_decomposition_rank_svd {A B C : Matrix n n ℂ}
    (h₁ : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (h₂ : (Matrix.fromBlocks A Bᴴ B C).PosSemidef) :
    ∃ (s : Fin C.rank → ℝ) (u v : Fin C.rank → n → ℂ) (R : Matrix n n ℂ),
      (∀ j, 0 ≤ s j) ∧ R.PosSemidef ∧
      C = ∑ j, (vecMulVec (u j) (star (u j)) + vecMulVec (v j) (star (v j))) ∧
      B = ∑ j, ((2 * s j : ℝ) : ℂ) • vecMulVec (u j) (star (v j)) ∧
      A = R + ∑ j, ((s j ^ 2 : ℝ) : ℂ) •
        (vecMulVec (u j) (star (u j)) + vecMulVec (v j) (star (v j))) := by
  obtain ⟨U, V, s, _, _, _, _, hs, _, hR, hCsum, hBsum, _, hA, _⟩ :=
    exists_ppt_svd_component_witnesses h₁ h₂
  let p : Fin C.rank → n → ℂ := fun j => psqrt C *ᵥ Uᵀ j
  let q : Fin C.rank → n → ℂ := fun j => psqrt C *ᵥ Vᵀ j
  let D : Fin C.rank → Matrix n n ℂ := fun j => (1 / 2 : ℂ) •
    (vecMulVec (p j) (star (p j)) + vecMulVec (q j) (star (q j)))
  let R : Matrix n n ℂ := A - (1 / 2 : ℂ) •
    (B * pinv C * Bᴴ + Bᴴ * pinv C * B)
  change R.PosSemidef at hR
  change (∑ j, D j) = C at hCsum
  change (∑ j, (s j : ℂ) • vecMulVec (p j) (star (q j))) = B at hBsum
  change A = R + ∑ j, ((s j ^ 2 : ℝ) : ℂ) • D j at hA
  let a : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  have ha : a * star a = (1 / 2 : ℂ) := by
    dsimp [a]
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have houter (x y : n → ℂ) :
      vecMulVec (a • x) (star (a • y)) = (1 / 2 : ℂ) • vecMulVec x (star y) := by
    rw [star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, ha]
  let u := fun j => a • p j
  let v := fun j => a • q j
  have huv (j : Fin C.rank) :
      vecMulVec (u j) (star (u j)) + vecMulVec (v j) (star (v j)) = D j := by
    dsimp only [u, v, D]
    rw [houter, houter, smul_add]
  have huvB (j : Fin C.rank) :
      ((2 * s j : ℝ) : ℂ) • vecMulVec (u j) (star (v j)) =
        (s j : ℂ) • vecMulVec (p j) (star (q j)) := by
    dsimp only [u, v]
    rw [houter, smul_smul]
    congr 1
    push_cast
    ring
  refine ⟨s, u, v, R, hs, hR, ?_, ?_, ?_⟩
  · simpa only [huv] using hCsum.symm
  · simpa only [huvB] using hBsum.symm
  · simpa only [huv] using hA

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSVD
