/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PrecondQLS20.MainResults.Foundation.PrecondModel
import Mathlib.Data.Matrix.ColumnRowPartitioned

set_option backward.isDefEq.respectTransparency false

/-!
# Fast Inversion Block-Encodings for Diagonal and Normal Matrices

This module formalizes Propositions 6 and 7 of Tong, An, Wiebe, and Lin on exact
`(α'_D, m, 0)` qubit block-encodings of diagonal matrix inverses `D⁻¹` when
`α'_D ≥ 1 / min_i |D_{ii}|` and unitary frame conjugation yielding `(α'_D, m, 0)`
block-encodings of normal matrix inverses `A⁻¹ = V D⁻¹ V†`.

## Main statements

* `diagonal_inverse_normalization`: spectral-norm bound `‖D⁻¹‖ ≤ α'` from `1 ≤ α' * ‖d i‖`.
* `prop6_diagonalExistence`: Proposition 6, existence of an `(α', m, 0)` block-encoding of `D⁻¹` for `m ≥ 1`.
* `norm_le_one_of_isometry`, `norm_conj_unitary`: spectral-norm invariance under unitary conjugation.
* `normal_inverse_encoding`, `prop7_normalExistence`: Proposition 7, `(α', m, 0)` block-encoding of `A⁻¹`.

## References

* [Tong, An, Wiebe, and Lin, 2021][TongAnWiebeLin2021], Section III, Propositions 6 and 7, pp. 10--12.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLS20.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.Execution.WorkspaceCP

/- ## Proposition 6 — diagonal normalisation -/

/-- **Proposition 6, normalisation core** (p. 10).

For a diagonal `D = diagonal d` and `α'_D ≥ 1/|d_i|` for all `i` (the printed
hypothesis `α'_D ≥ 1/min_i |D_ii|`), the operator norm of `D⁻¹` is at most
`α'_D`.  This is what makes `(α'_D, ·, 0)` a valid block-encoding normalisation
for the exact inverse. -/
theorem diagonal_inverse_normalization {N : ℕ} (d : Fin N → ℂ) {α' : ℝ}
    (hαpos : 0 < α') (hα : ∀ i, 1 ≤ α' * ‖d i‖) :
    ‖(diagonal (fun i => (d i)⁻¹) : Matrix (Fin N) (Fin N) ℂ)‖ ≤ α' := by
  rw [Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg hαpos.le]
  intro i
  rw [norm_inv]
  have hdi : (0 : ℝ) < ‖d i‖ := by
    by_contra h
    push Not at h
    have h0 : ‖d i‖ = 0 := le_antisymm h (norm_nonneg _)
    have h1 := hα i
    rw [h0, mul_zero] at h1
    linarith
  rw [inv_le_iff_one_le_mul₀ hdi]
  exact hα i

/-- **Proposition 6, existence target** (p. 10, Figure 1).

Given the normalisation bound, there exists a genuine `(α'_D, m, 0)`
block-encoding of the diagonal inverse on `n` data qubits with `m ≥ 1` ancillas.
The `m'_D = O(l + polylog N)` statement of the proposition is the ancilla
bookkeeping of the explicit circuit of Figure 1.

The construction uses the scalar rotations `[[z_i, -s_i], [s_i, conj z_i]]`,
where `z_i = d_i⁻¹ / α'` and `s_i = sqrt (1 - ‖z_i‖²)`, on the coordinate
pairs `(i, i + 2^n)`. The remaining workspace coordinates carry the identity;
both frames select the first `2^n` coordinates. -/
theorem prop6_diagonalExistence {n m : ℕ} (d : Fin (2 ^ n) → ℂ) {α' : ℝ}
    (hαpos : 0 < α') (hα : ∀ i, 1 ≤ α' * ‖d i‖) (hm : 1 ≤ m) :
    Nonempty (QubitBlockEncoding n m
      (diagonal (fun i => (d i)⁻¹)) α' 0) := by
  classical
  let N := 2 ^ n
  let M := 2 ^ (n + m)
  have hdim : N + N ≤ M := by
    calc
      N + N = 2 ^ (n + 1) := by simp [N, pow_succ]; omega
      _ ≤ M := Nat.pow_le_pow_right (by decide) (by omega)
  let K := M - (N + N)
  let z : Fin N → ℂ := fun i => (d i)⁻¹ / (α' : ℂ)
  have hz : ∀ i, ‖z i‖ ≤ 1 := by
    intro i
    have hdi : 0 < ‖d i‖ := by
      have := hα i
      by_contra h
      have hzero : ‖d i‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
      rw [hzero, mul_zero] at this
      norm_num at this
    simp only [z, norm_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hαpos]
    exact (div_le_one hαpos).2 ((inv_le_iff_one_le_mul₀ hdi).2 (hα i))
  let s : Fin N → ℝ := fun i => Real.sqrt (1 - ‖z i‖ ^ 2)
  have hs : ∀ i, ‖z i‖ ^ 2 + s i ^ 2 = 1 := by
    intro i
    have hnonneg : 0 ≤ 1 - ‖z i‖ ^ 2 := by
      nlinarith [hz i, norm_nonneg (z i)]
    dsimp only [s]
    rw [Real.sq_sqrt hnonneg]
    ring
  have hrotation : ∀ i, star (z i) * z i + (s i : ℂ) * (s i : ℂ) = 1 := by
    intro i
    have hreal := hs i
    rw [Complex.sq_norm, Complex.normSq_apply] at hreal
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    · nlinarith
    · ring
  let D : Matrix (Fin N) (Fin N) ℂ := diagonal z
  let S : Matrix (Fin N) (Fin N) ℂ := diagonal (fun i => (s i : ℂ))
  have hS : Sᴴ = S := by simp [S, diagonal_conjTranspose]
  have hdiag : Dᴴ * D + S * S = 1 := by
    simp only [D, S, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_add, ← diagonal_one]
    exact congrArg diagonal (funext hrotation)
  have hcomm : D * Dᴴ = Dᴴ * D := by
    simp only [D, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDS : D * S = S * D := by
    simp only [D, S, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDaS : Dᴴ * S = S * Dᴴ := by
    simp only [D, S, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  let B := fromBlocks D (-S) S Dᴴ
  have hB : Bᴴ * B = 1 := by
    simp only [B, fromBlocks_conjTranspose, conjTranspose_neg, hS,
      conjTranspose_conjTranspose, fromBlocks_multiply, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg]
    rw [hdiag, hDaS, neg_add_cancel, hDS, neg_add_cancel, hcomm, add_comm (S * S), hdiag]
    exact fromBlocks_one
  let P : Matrix ((Fin N ⊕ Fin N) ⊕ Fin K) ((Fin N ⊕ Fin N) ⊕ Fin K) ℂ :=
    fromBlocks B 0 0 1
  have hP : Pᴴ * P = 1 := by
    simp [P, fromBlocks_conjTranspose, fromBlocks_multiply, hB, fromBlocks_one]
  let F : Matrix ((Fin N ⊕ Fin N) ⊕ Fin K) (Fin N) ℂ :=
    fromRows (fromRows 1 0) 0
  have hF : Fᴴ * F = 1 := by
    simp [F, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hcompression : Fᴴ * P * F = D := by
    simp [F, P, B, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  let e : ((Fin N ⊕ Fin N) ⊕ Fin K) ≃ Fin M :=
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin K))).trans finSumFinEquiv).trans
      (finCongr (Nat.add_sub_of_le hdim))
  let U : Matrix (Fin M) (Fin M) ℂ := P.submatrix e.symm e.symm
  let L : Matrix (Fin M) (Fin N) ℂ := F.submatrix e.symm id
  have hU : U ∈ Matrix.unitaryGroup (Fin M) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    simp [U, conjTranspose_submatrix, submatrix_mul_equiv, hP]
  have hL : IsIsometry L := by
    change Lᴴ * L = 1
    simp [L, conjTranspose_submatrix, submatrix_mul_equiv, hF]
  have hcomp : compress L U L = D := by
    simpa [compress, L, U, conjTranspose_submatrix, submatrix_mul_equiv] using
      hcompression
  refine ⟨⟨U, L, L, hU, hL, hL, hαpos, le_rfl, ?_⟩⟩
  have hscaled : α' • compress L U L = diagonal (fun i => (d i)⁻¹) := by
    rw [hcomp]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [D, diagonal_apply_eq, Matrix.smul_apply, Complex.real_smul, z]
      exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hαpos.ne')
    · simp [D, hij]
  rw [hscaled, sub_self, norm_zero]

/- ## Proposition 7 — conjugation by the diagonalising unitary -/

/-- A two-sided isometry has spectral norm at most one: from `V†V = 1`,
`‖V‖² = ‖V†V‖ = ‖1‖ ≤ 1`. -/
theorem norm_le_one_of_isometry {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV1 : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have hsq : ‖V‖ * ‖V‖ = ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self V, hV1]
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 :=
    Qatlib.Concepts.BlockEncoding.Encoding.matrix_one_norm_le
  have h0 : 0 ≤ ‖V‖ := norm_nonneg _
  nlinarith [hsq, h1, h0]

/-- Conjugating a matrix by a unitary `V` preserves the spectral norm:
`‖V X V†‖ = ‖X‖`.  This is the norm-invariance step used to transport the
block-encoding error of `D⁻¹` to `V D⁻¹ V†`. -/
theorem norm_conj_unitary {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hV1 : Vᴴ * V = 1) (hV2 : V * Vᴴ = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖V * X * Vᴴ‖ = ‖X‖ := by
  have hVnorm : ‖V‖ ≤ 1 := norm_le_one_of_isometry hV1
  have hVdnorm : ‖Vᴴ‖ ≤ 1 := by
    apply norm_le_one_of_isometry (V := Vᴴ)
    simpa only [Matrix.conjTranspose_conjTranspose] using hV2
  apply le_antisymm
  · calc
      ‖V * X * Vᴴ‖ ≤ ‖V * X‖ * ‖Vᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖V‖ * ‖X‖) * ‖Vᴴ‖ := by
            gcongr
            exact Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * ‖X‖ := by
            have hX : 0 ≤ ‖X‖ := norm_nonneg X
            calc
              (‖V‖ * ‖X‖) * ‖Vᴴ‖ ≤ (1 * ‖X‖) * 1 := by
                    apply mul_le_mul
                    · exact mul_le_mul_of_nonneg_right hVnorm hX
                    · exact hVdnorm
                    · exact norm_nonneg _
                    · exact mul_nonneg zero_le_one hX
              _ = 1 * ‖X‖ := by ring
      _ = ‖X‖ := one_mul _
  · have hXeq : Vᴴ * (V * X * Vᴴ) * V = X := by
      calc
        Vᴴ * (V * X * Vᴴ) * V = (Vᴴ * V) * X * (Vᴴ * V) := by
              noncomm_ring
        _ = 1 * X * 1 := by rw [hV1]
        _ = X := by rw [Matrix.one_mul, Matrix.mul_one]
    calc
      ‖X‖ = ‖Vᴴ * (V * X * Vᴴ) * V‖ := by rw [hXeq]
      _ ≤ ‖V * X * Vᴴ‖ := by
            calc
              ‖Vᴴ * (V * X * Vᴴ) * V‖ ≤ ‖Vᴴ * (V * X * Vᴴ)‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
              _ ≤ (‖Vᴴ‖ * ‖V * X * Vᴴ‖) * ‖V‖ := by
                    gcongr
                    exact Matrix.l2_opNorm_mul _ _
              _ ≤ ‖V * X * Vᴴ‖ := by
                    have hX : 0 ≤ ‖V * X * Vᴴ‖ := norm_nonneg _
                    calc
                      (‖Vᴴ‖ * ‖V * X * Vᴴ‖) * ‖V‖ ≤ (1 * ‖V * X * Vᴴ‖) * 1 := by
                            apply mul_le_mul
                            · exact mul_le_mul_of_nonneg_right hVdnorm hX
                            · exact hVnorm
                            · exact norm_nonneg _
                            · exact mul_nonneg zero_le_one hX
                      _ = ‖V * X * Vᴴ‖ := by ring

/-- **Proposition 7, structural core** (pp. 11–12, Eq. (10)).

If `E` is an `(α, m, ε)`-block-encoding of `D⁻¹` and `V` is unitary, then
replacing the input/output frames `L, R` by `L V†, R V†` yields an
`(α, m, ε)`-block-encoding of `V D⁻¹ V†`.  This is exactly the paper's
`U_A' = (V ⊗ I_{l+1}) U_D' (V† ⊗ I_{l+1})` written as a frame change. -/
theorem normal_inverse_encoding {n m : ℕ} {D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {α ε : ℝ}
    (hV1 : Vᴴ * V = 1) (hV2 : V * Vᴴ = 1)
    (E : QubitBlockEncoding n m D⁻¹ α ε) :
    Nonempty (QubitBlockEncoding n m (V * D⁻¹ * Vᴴ) α ε) := by
  refine ⟨⟨E.U, E.L * Vᴴ, E.R * Vᴴ, ?_⟩⟩
  refine ⟨E.encoding.unitary, ?_, ?_, E.encoding.normalization_pos,
    E.encoding.error_nonneg, ?_⟩
  · -- left isometry
    unfold IsIsometry at *
    calc
      (E.L * Vᴴ)ᴴ * (E.L * Vᴴ) = (V * E.Lᴴ) * (E.L * Vᴴ) := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = V * (E.Lᴴ * E.L) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * 1 * Vᴴ := by rw [E.encoding.left_isometry]
      _ = V * Vᴴ := by rw [Matrix.mul_one]
      _ = 1 := hV2
  · -- right isometry
    unfold IsIsometry at *
    calc
      (E.R * Vᴴ)ᴴ * (E.R * Vᴴ) = (V * E.Rᴴ) * (E.R * Vᴴ) := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = V * (E.Rᴴ * E.R) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * 1 * Vᴴ := by rw [E.encoding.right_isometry]
      _ = V * Vᴴ := by rw [Matrix.mul_one]
      _ = 1 := hV2
  · -- error transport
    have hcomp : compress (E.L * Vᴴ) E.U (E.R * Vᴴ) =
        V * compress E.L E.U E.R * Vᴴ := by
      unfold compress
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    have hkey : V * D⁻¹ * Vᴴ - α • compress (E.L * Vᴴ) E.U (E.R * Vᴴ) =
        V * (D⁻¹ - α • compress E.L E.U E.R) * Vᴴ := by
      rw [hcomp]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hkey, norm_conj_unitary hV1 hV2]
    exact E.encoding.error_le

/-- **Proposition 7** (pp. 11–12): fast inversion of a normal matrix.

Given a `(α'_D, m'_D, 0)`-block-encoding of `D⁻¹` and a normal `A = V D V†`
with `V` unitary, there is a `(α'_D, m'_D, 0)`-block-encoding of `A⁻¹` using the
same workspace and one conjugation by `V`.  The paper's oracle count
(`O_D, O_D†, V, V†` once each) follows from the construction: `V` and `V†`
appear exactly in the two frame changes. -/
theorem prop7_normalExistence {n m : ℕ} {D A V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {α' : ℝ} (hV1 : Vᴴ * V = 1) (hV2 : V * Vᴴ = 1)
    (hA : A = V * D * Vᴴ) (hD1 : D * D⁻¹ = 1) (hD2 : D⁻¹ * D = 1)
    (E : QubitBlockEncoding n m D⁻¹ α' 0) :
    Nonempty (QubitBlockEncoding n m A⁻¹ α' 0) := by
  -- `A⁻¹ = V D⁻¹ Vᴴ`
  have hAinv : A⁻¹ = V * D⁻¹ * Vᴴ := by
    have hmul : A * (V * D⁻¹ * Vᴴ) = 1 := by
      rw [hA]
      calc
        (V * D * Vᴴ) * (V * D⁻¹ * Vᴴ) = V * D * (Vᴴ * V) * D⁻¹ * Vᴴ := by noncomm_ring
        _ = V * D * 1 * D⁻¹ * Vᴴ := by rw [hV1]
        _ = V * (D * D⁻¹) * Vᴴ := by noncomm_ring
        _ = V * 1 * Vᴴ := by rw [hD1]
        _ = V * Vᴴ := by rw [Matrix.mul_one]
        _ = 1 := hV2
    have hleft : (V * D⁻¹ * Vᴴ) * A = 1 := by
      rw [hA]
      calc
        (V * D⁻¹ * Vᴴ) * (V * D * Vᴴ) = V * D⁻¹ * (Vᴴ * V) * D * Vᴴ := by
          noncomm_ring
        _ = V * D⁻¹ * 1 * D * Vᴴ := by rw [hV1]
        _ = V * (D⁻¹ * D) * Vᴴ := by noncomm_ring
        _ = V * 1 * Vᴴ := by rw [hD2]
        _ = 1 := by rw [Matrix.mul_one, hV2]
    exact (Matrix.coe_units_inv ⟨A, V * D⁻¹ * Vᴴ, hmul, hleft⟩).symm
  rw [hAinv]
  exact normal_inverse_encoding hV1 hV2 E

end Qatlib.Papers.PrecondQLS20.MainResults
