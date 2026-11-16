/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtFacts
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PseudoInverse

@[expose] public section




/-!
# The lifting lemma (isometry form)

If `S` is a positive operator on `ℂ^κ ⊗ ℂ^n` and `V : ℂ² → ℂ^κ` is an isometry such that the
compression `(V ⊗ 1)ᴴ S (V ⊗ 1)` is a sum of pure product operators, then `S` is a sum of pure
operators of Schmidt rank at most `|κ| - 1` (`hasSchmidtNumberLE_of_compression`).

The proof uses the generalized Schur complement of `S` along the range of `J = V ⊗ 1`
(`exists_lift_matrix`, `exists_lifted_vectors`) and the rank criterion
`rank_lt_card_of_vecMul_eq_zero`.
-/

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

/-! ### Rank criterion -/

/-- A matrix with a nonzero left null vector does not have full row rank. -/
theorem rank_lt_card_of_vecMul_eq_zero {κ n : Type*} [Fintype κ] [Fintype n]
    {H : Matrix κ n ℂ} {u : κ → ℂ} (hu : u ≠ 0)
    (h : Matrix.vecMul (star u) H = 0) : H.rank < Fintype.card κ := by
  by_contra hlt
  have hrank : H.rank = Fintype.card κ :=
    le_antisymm (Matrix.rank_le_card_height H) (not_lt.mp hlt)
  have htop : LinearMap.range H.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hrank
  have hmem : u ∈ LinearMap.range H.mulVecLin := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨z, hz⟩ := hmem
  have hz' : u = H *ᵥ z := by
    rw [← hz, Matrix.mulVecLin_apply]
  have h0 : star u ⬝ᵥ u = 0 := by
    calc star u ⬝ᵥ u = star u ⬝ᵥ (H *ᵥ z) := congrArg (fun t => star u ⬝ᵥ t) hz'
      _ = Matrix.vecMul (star u) H ⬝ᵥ z := Matrix.dotProduct_mulVec _ _ _
      _ = 0 := by rw [h, zero_dotProduct]
  exact hu (dotProduct_star_self_eq_zero.mp h0)

/-- Every vector of `ℂ²` is orthogonal to some nonzero vector. -/
theorem exists_ne_zero_star_dotProduct_eq_zero (a : Fin 2 → ℂ) :
    ∃ c : Fin 2 → ℂ, c ≠ 0 ∧ star c ⬝ᵥ a = 0 := by
  by_cases ha : a = 0
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro hc
      have h0 : (1 : ℂ) = 0 := congrFun hc 0
      exact one_ne_zero h0
    · rw [ha, dotProduct_zero]
  · refine ⟨![star (a 1), -star (a 0)], ?_, ?_⟩
    · intro hc
      apply ha
      have h0 : star (a 1) = 0 := congrFun hc 0
      have h1 : -star (a 0) = 0 := congrFun hc 1
      have ha1 : a 1 = 0 := star_eq_zero.mp h0
      have ha0 : a 0 = 0 := star_eq_zero.mp (neg_eq_zero.mp h1)
      have hall : ∀ j : Fin 2, a j = 0 := Fin.forall_fin_two.mpr ⟨ha0, ha1⟩
      exact funext hall
    · rw [dotProduct, Fin.sum_univ_two]
      show star (star (a 1)) * a 0 + star (-star (a 0)) * a 1 = 0
      rw [star_star, star_neg, star_star]
      ring

/-! ### Pure operators and product vectors -/

/-- Pure-state operators transform by matrix congruence. `|M v⟩⟨M v| = M |v⟩⟨v| Mᴴ`. -/
theorem pureState_mulVec {p q : Type*} [Fintype q] (M : Matrix p q ℂ) (v : q → ℂ) :
    pureState (M *ᵥ v) = M * pureState v * Mᴴ := by
  unfold pureState
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- Establishes `sum_pureState_mulVec`: `∑ i, pureState (M *ᵥ f i) = M * (∑ i, pureState (f i)) * Mᴴ`, for the stated parameters. -/
theorem sum_pureState_mulVec {ι p q : Type*} [Fintype ι] [Fintype q] (M : Matrix p q ℂ)
    (f : ι → q → ℂ) :
    ∑ i, pureState (M *ᵥ f i) = M * (∑ i, pureState (f i)) * Mᴴ := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun i _ => pureState_mulVec M (f i)

/-- The product vector `a ⊗ b`. -/
def prodVec {κ n : Type*} (a : κ → ℂ) (b : n → ℂ) : κ × n → ℂ :=
  fun x => a x.1 * b x.2

/-- Establishes `coeffMatrix_prodVec`: `coeffMatrix (prodVec a b) = Matrix.vecMulVec a b`, for the stated parameters. -/
theorem coeffMatrix_prodVec {κ n : Type*} (a : κ → ℂ) (b : n → ℂ) :
    coeffMatrix (prodVec a b) = Matrix.vecMulVec a b := by
  ext i j
  simp [prodVec, Matrix.vecMulVec_apply]

/-- Establishes `pureState_prodVec`: `pureState (prodVec a b) = pureState a ⊗ₖ pureState b`, for the stated parameters. -/
theorem pureState_prodVec {κ n : Type*} (a : κ → ℂ) (b : n → ℂ) :
    pureState (prodVec a b) = pureState a ⊗ₖ pureState b :=
  pureState_eq_kronecker_of_coeffMatrix (coeffMatrix_prodVec a b)

/-- Establishes `coeffMatrix_zero`: `coeffMatrix (0 : κ × n → ℂ) = 0`, for the stated parameters. -/
theorem coeffMatrix_zero {κ n : Type*} : coeffMatrix (0 : κ × n → ℂ) = 0 := by
  ext i j
  simp

/-- The coefficient matrix of `(L ⊗ 1) x` is `L X`. -/
theorem coeffMatrix_kronecker_one_mulVec {κ κ' n : Type*} [Fintype κ] [Fintype n]
    [DecidableEq n] (L : Matrix κ' κ ℂ) (x : κ × n → ℂ) :
    coeffMatrix ((L ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ x) = L * coeffMatrix x := by
  rw [coeffMatrix_kronecker_mulVec, Matrix.transpose_one, Matrix.mul_one]

/-- If the compression `Vᴴ X` of the coefficient matrix by an isometry `V : ℂ² → ℂ^κ` has a
nonzero left null vector, then the Schmidt rank is not full. -/
theorem schmidtRank_lt_card_of_compression {κ n : Type*} [Fintype κ] [Fintype n]
    {V : Matrix κ (Fin 2) ℂ} (hV : Vᴴ * V = 1) {x : κ × n → ℂ} {c : Fin 2 → ℂ} (hc : c ≠ 0)
    (h : Matrix.vecMul (star c) (Vᴴ * coeffMatrix x) = 0) :
    schmidtRank x < Fintype.card κ := by
  have hu : V *ᵥ c ≠ 0 := by
    intro h0
    apply hc
    have h1 : (Vᴴ * V) *ᵥ c = 0 := by
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    rw [hV, Matrix.one_mulVec] at h1
    exact h1
  show (coeffMatrix x).rank < Fintype.card κ
  refine rank_lt_card_of_vecMul_eq_zero hu ?_
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul]
  exact h

/-! ### The generalized Schur complement along an isometry -/

/-- Establishes `conjTranspose_mul_one_sub`: `Jᴴ * (1 - J * Jᴴ) = 0`, for the stated parameters. -/
theorem conjTranspose_mul_one_sub {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] {J : Matrix p q ℂ} (hJ : Jᴴ * J = 1) : Jᴴ * (1 - J * Jᴴ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hJ, Matrix.one_mul, sub_self]

/-- The purely algebraic identity behind the lifting lemma. -/
theorem lift_identity {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    (S R : Matrix p p ℂ) (J : Matrix p q ℂ) (Jc : Matrix q p ℂ) (D Dp : Matrix q q ℂ)
    (hR : J * Jc = 1 - R) (hD : D = Jc * S * J)
    (E1 : S * J * (Dp * D) = S * J) (E2 : D * Dp * (Jc * S) = Jc * S)
    (E3 : Dp * D * Dp = Dp) :
    (J + R * (S * J * Dp)) * D * (Jc + Dp * (Jc * S) * R) +
      R * (S - S * J * Dp * (Jc * S)) * R = S := by
  have T1 : J * D * Jc = (1 - R) * S * (1 - R) := by
    rw [hD, ← hR]
    simp only [Matrix.mul_assoc]
  have T2 : J * D * (Dp * (Jc * S) * R) = (1 - R) * S * R := by
    calc J * D * (Dp * (Jc * S) * R) = J * (D * Dp * (Jc * S)) * R := by
          simp only [Matrix.mul_assoc]
      _ = J * (Jc * S) * R := by rw [E2]
      _ = (1 - R) * S * R := by
          rw [← hR]
          simp only [Matrix.mul_assoc]
  have T3 : R * (S * J * Dp) * D * Jc = R * S * (1 - R) := by
    calc R * (S * J * Dp) * D * Jc = R * (S * J * (Dp * D)) * Jc := by
          simp only [Matrix.mul_assoc]
      _ = R * (S * J) * Jc := by rw [E1]
      _ = R * S * (1 - R) := by
          rw [← hR]
          simp only [Matrix.mul_assoc]
  have T4 : R * (S * J * Dp) * D * (Dp * (Jc * S) * R) =
      R * (S * J * Dp * (Jc * S)) * R := by
    calc R * (S * J * Dp) * D * (Dp * (Jc * S) * R)
        = R * (S * J * (Dp * D * Dp) * (Jc * S)) * R := by
          simp only [Matrix.mul_assoc]
      _ = R * (S * J * Dp * (Jc * S)) * R := by rw [E3]
  calc (J + R * (S * J * Dp)) * D * (Jc + Dp * (Jc * S) * R) +
        R * (S - S * J * Dp * (Jc * S)) * R
      = J * D * Jc + J * D * (Dp * (Jc * S) * R) + R * (S * J * Dp) * D * Jc +
          R * (S * J * Dp) * D * (Dp * (Jc * S) * R) +
          (R * S * R - R * (S * J * Dp * (Jc * S)) * R) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul]
        abel
    _ = (1 - R) * S * (1 - R) + (1 - R) * S * R + R * S * (1 - R) +
          R * (S * J * Dp * (Jc * S)) * R +
          (R * S * R - R * (S * J * Dp * (Jc * S)) * R) := by
        rw [T1, T2, T3, T4]
    _ = S := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
        abel

/-- Generalized Schur complement of a positive `S` along an isometry `J`: there is a lift `Mh` of
the identity (`Jᴴ * Mh = 1`) such that `S - Mh (Jᴴ S J) Mhᴴ` is a positive operator supported on
the orthogonal complement of the range of `J`. -/
theorem exists_lift_matrix {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    {S : Matrix p p ℂ} (hS : S.PosSemidef) (J : Matrix p q ℂ) (hJ : Jᴴ * J = 1) :
    ∃ (Mh : Matrix p q ℂ) (Sch : Matrix p p ℂ), Sch.PosSemidef ∧ Jᴴ * Mh = 1 ∧
      Mh * (Jᴴ * S * J) * Mhᴴ + (1 - J * Jᴴ) * Sch * (1 - J * Jᴴ) = S := by
  obtain ⟨G, hG⟩ : ∃ G : Matrix p p ℂ, Gᴴ * G = S :=
    ⟨psqrt S, conjTranspose_psqrt_mul_psqrt hS⟩
  obtain ⟨D, hD⟩ : ∃ D : Matrix q q ℂ, D = Jᴴ * S * J := ⟨_, rfl⟩
  have hGJ : (G * J)ᴴ * (G * J) = D := by
    rw [hD, Matrix.conjTranspose_mul, ← hG]
    simp only [Matrix.mul_assoc]
  have hDh : D.IsHermitian := by
    rw [← hGJ]
    exact Matrix.isHermitian_conjTranspose_mul_self (G * J)
  have hDph : (pinv D).IsHermitian := isHermitian_pinv hDh
  have hA : Gᴴ * (G * J) = S * J := by
    rw [← Matrix.mul_assoc, hG]
  have hB : (G * J)ᴴ * G = Jᴴ * S := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hG]
  have hSch : (S - S * J * pinv D * (Jᴴ * S)).PosSemidef := by
    have h := posSemidef_gram_schur G (G * J)
    rw [hG, hA, hGJ, hB] at h
    exact h
  have h1 : G * J * (pinv D * D) = G * J := by
    have h := gram_mul_pinv_mul (G * J)
    rw [hGJ] at h
    exact h
  have E1 : S * J * (pinv D * D) = S * J := by
    have h2 : Gᴴ * (G * J * (pinv D * D)) = Gᴴ * (G * J) := by rw [h1]
    have h3 : Gᴴ * G * J * (pinv D * D) = Gᴴ * G * J := by
      simpa only [Matrix.mul_assoc] using h2
    rw [hG] at h3
    exact h3
  have E2 : D * pinv D * (Jᴴ * S) = Jᴴ * S := by
    have h := congrArg Matrix.conjTranspose E1
    rw [Matrix.conjTranspose_mul (S * J) (pinv D * D), Matrix.conjTranspose_mul (pinv D) D,
      Matrix.conjTranspose_mul S J, hDh.eq, hDph.eq, hS.isHermitian.eq] at h
    exact h
  have E3 : pinv D * D * pinv D = pinv D := pinv_mul_pinv hDh
  have hRh : (1 - J * Jᴴ)ᴴ = 1 - J * Jᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hKh : (S * J * pinv D)ᴴ = pinv D * (Jᴴ * S) := by
    rw [Matrix.conjTranspose_mul (S * J) (pinv D), Matrix.conjTranspose_mul S J, hDph.eq,
      hS.isHermitian.eq]
  have hMh : (J + (1 - J * Jᴴ) * (S * J * pinv D))ᴴ =
      Jᴴ + pinv D * (Jᴴ * S) * (1 - J * Jᴴ) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul (1 - J * Jᴴ) (S * J * pinv D),
      hRh, hKh]
  refine ⟨J + (1 - J * Jᴴ) * (S * J * pinv D), S - S * J * pinv D * (Jᴴ * S), hSch, ?_, ?_⟩
  · rw [Matrix.mul_add, ← Matrix.mul_assoc, conjTranspose_mul_one_sub hJ, Matrix.zero_mul,
      add_zero, hJ]
  · rw [hMh, ← hD]
    exact lift_identity S (1 - J * Jᴴ) J Jᴴ D (pinv D) (sub_sub_cancel _ _).symm hD E1 E2 E3

/-- Vector form of `exists_lift_matrix`: a decomposition of the compression `Jᴴ S J` into pure
operators lifts to a decomposition of `S` into pure operators whose vectors compress either to
the given vectors or to zero. -/
theorem exists_lifted_vectors {p q ι : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] [Fintype ι] {S : Matrix p p ℂ} (hS : S.PosSemidef) (J : Matrix p q ℂ)
    (hJ : Jᴴ * J = 1) (f : ι → q → ℂ) (hf : Jᴴ * S * J = ∑ i, pureState (f i)) :
    ∃ (g : ι → p → ℂ) (M : ℕ) (w : Fin M → p → ℂ), (∀ i, Jᴴ *ᵥ g i = f i) ∧
      (∀ β, Jᴴ *ᵥ w β = 0) ∧ S = ∑ i, pureState (g i) + ∑ β, pureState (w β) := by
  obtain ⟨Mh, Sch, hSch, hJM, hid⟩ := exists_lift_matrix hS J hJ
  obtain ⟨M, z, hz⟩ := exists_sum_vecMulVec_of_posSemidef hSch
  have hz' : Sch = ∑ β, pureState (z β) := hz
  have hRh : (1 - J * Jᴴ)ᴴ = 1 - J * Jᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  refine ⟨fun i => Mh *ᵥ f i, M, fun β => (1 - J * Jᴴ) *ᵥ z β, fun i => ?_, fun β => ?_, ?_⟩
  · show Jᴴ *ᵥ (Mh *ᵥ f i) = f i
    rw [Matrix.mulVec_mulVec, hJM, Matrix.one_mulVec]
  · show Jᴴ *ᵥ ((1 - J * Jᴴ) *ᵥ z β) = 0
    rw [Matrix.mulVec_mulVec, conjTranspose_mul_one_sub hJ, Matrix.zero_mulVec]
  · show S = ∑ i, pureState (Mh *ᵥ f i) + ∑ β, pureState ((1 - J * Jᴴ) *ᵥ z β)
    rw [sum_pureState_mulVec, sum_pureState_mulVec, ← hf, ← hz', hRh]
    exact hid.symm

/-! ### The lifting lemma -/

/-- **Lifting lemma, isometry form.** If the compression of a positive operator `S` on
`ℂ^κ ⊗ ℂ^n` by an isometry `V ⊗ 1`, `V : ℂ² → ℂ^κ`, is a sum of pure product operators, then `S`
is a sum of pure operators of Schmidt rank at most `|κ| - 1`. -/
theorem hasSchmidtNumberLE_of_compression {κ n : Type*} [Fintype κ] [DecidableEq κ] [Fintype n]
    [DecidableEq n] {S : Matrix (κ × n) (κ × n) ℂ} {V : Matrix κ (Fin 2) ℂ}
    (hS : S.PosSemidef) (hV : Vᴴ * V = 1)
    (hD : ∃ (N : ℕ) (a : Fin N → Fin 2 → ℂ) (b : Fin N → n → ℂ),
      (V ⊗ₖ (1 : Matrix n n ℂ))ᴴ * S * (V ⊗ₖ (1 : Matrix n n ℂ)) =
        ∑ i, pureState (a i) ⊗ₖ pureState (b i)) :
    HasSchmidtNumberLE (Fintype.card κ - 1) S := by
  obtain ⟨N, a, b, hab⟩ := hD
  have hJc : (V ⊗ₖ (1 : Matrix n n ℂ))ᴴ = Vᴴ ⊗ₖ (1 : Matrix n n ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_one]
  have hJJ : (V ⊗ₖ (1 : Matrix n n ℂ))ᴴ * (V ⊗ₖ (1 : Matrix n n ℂ)) = 1 := by
    rw [hJc, ← mul_kronecker_mul, hV, Matrix.one_mul, one_kronecker_one]
  have hf : (V ⊗ₖ (1 : Matrix n n ℂ))ᴴ * S * (V ⊗ₖ (1 : Matrix n n ℂ)) =
      ∑ i, pureState (prodVec (a i) (b i)) := by
    rw [hab]
    exact Finset.sum_congr rfl fun i _ => (pureState_prodVec (a i) (b i)).symm
  obtain ⟨g, M, w, hg, hw, hS'⟩ :=
    exists_lifted_vectors hS (V ⊗ₖ (1 : Matrix n n ℂ)) hJJ (fun i => prodVec (a i) (b i)) hf
  have hg' : ∀ i, (Vᴴ ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ g i = prodVec (a i) (b i) := fun i => by
    rw [← hJc]
    exact hg i
  have hw' : ∀ β, (Vᴴ ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ w β = 0 := fun β => by
    rw [← hJc]
    exact hw β
  have hrank_g : ∀ i, schmidtRank (g i) ≤ Fintype.card κ - 1 := by
    intro i
    obtain ⟨c, hc, hca⟩ := exists_ne_zero_star_dotProduct_eq_zero (a i)
    have e : Vᴴ * coeffMatrix (g i) = Matrix.vecMulVec (a i) (b i) := by
      rw [← coeffMatrix_kronecker_one_mulVec Vᴴ (g i), hg' i, coeffMatrix_prodVec]
    have hlt : schmidtRank (g i) < Fintype.card κ := by
      refine schmidtRank_lt_card_of_compression hV hc ?_
      rw [e, Matrix.vecMul_vecMulVec, hca, zero_smul]
    omega
  have hrank_w : ∀ β, schmidtRank (w β) ≤ Fintype.card κ - 1 := by
    intro β
    obtain ⟨c, hc, -⟩ := exists_ne_zero_star_dotProduct_eq_zero (0 : Fin 2 → ℂ)
    have e : Vᴴ * coeffMatrix (w β) = 0 := by
      rw [← coeffMatrix_kronecker_one_mulVec Vᴴ (w β), hw' β, coeffMatrix_zero]
    have hlt : schmidtRank (w β) < Fintype.card κ := by
      refine schmidtRank_lt_card_of_compression hV hc ?_
      rw [e, Matrix.vecMul_zero]
    omega
  rw [hS']
  exact (hasSchmidtNumberLE_sum g hrank_g).add (hasSchmidtNumberLE_sum w hrank_w)

end Qatlib.Foundations.PPTMatrix.OperatorCones
