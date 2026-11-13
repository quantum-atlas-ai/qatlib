/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CircDepthShen26.ShortTimeBlock.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Full-Output Bound for One-Step Oblivious Amplitude Amplification

This module formalizes the exact output identity and operator-norm error bound for
one-step oblivious amplitude amplification of a block-encoded matrix `A / 2` by a
unitary `B` with ancilla embedding `ι`.

## Main statements

* `source_lemma14_oaa`: exact identity `U * ι = ι * A + B * ι * (1 - Aᴴ * A)` and
  operator-norm bounds `3 * ‖A - V‖ + ‖A - V‖ ^ 2` and `4 * ‖A - V‖` when `V` is
  unitary and `‖A - V‖ ≤ 1`.

## References

* [Shen et al., 2026][ShenEtAl2026CircDepth], Lemma 14, Eqs. (100)--(102), p. 18.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CircDepthShen26.ShortTimeBlock

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

private lemma oaa_isometry_norm_le_one
    {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (M : Matrix R C ℂ) (hM : Mᴴ * M = 1) : ‖M‖ ≤ 1 := by
  have hone : ‖(1 : Matrix C C ℂ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  have hsq : ‖M‖ * ‖M‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hM]
    exact hone
  nlinarith [norm_nonneg M]

/-- **Lemma 14 (Full-output bound for one-step OAA)**: for a unitary `B`, an
isometric embedding `ι` (`ιᴴ * ι = 1`), and `ιᴴ * B * ι = 2⁻¹ • A`, the
one-step oblivious amplitude-amplification operator
`U = -(B * (2 • (ι * ιᴴ) - 1) * Bᴴ * (2 • (ι * ιᴴ) - 1) * B)` satisfies
`U * ι = ι * A + B * ι * (1 - Aᴴ * A)` and approximates `ι * V` within
`3 * ‖A - V‖ + ‖A - V‖ ^ 2 ≤ 4 * ‖A - V‖` whenever `V` is unitary and
`‖A - V‖ ≤ 1`. -/
theorem source_lemma14_oaa
    {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (hB : IsUnitary B)
    (ι : Matrix I D ℂ) (hι : ιᴴ * ι = 1)
    (A : Matrix D D ℂ)
    (hA : ιᴴ * B * ι = (2 : ℂ)⁻¹ • A) :
    let U : Matrix I I ℂ :=
      -(B * (2 • (ι * ιᴴ) - 1) * Bᴴ * (2 • (ι * ιᴴ) - 1) * B)
    U * ι = ι * A + B * ι * (1 - Aᴴ * A) ∧
    (∀ (V : Matrix D D ℂ), IsUnitary V → ‖A - V‖ ≤ 1 →
      ‖U * ι - ι * V‖ ≤ 3 * ‖A - V‖ + ‖A - V‖ ^ 2 ∧
      ‖U * ι - ι * V‖ ≤ 4 * ‖A - V‖) := by
  have hBB : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  have hAH : ιᴴ * Bᴴ * ι = (2 : ℂ)⁻¹ • Aᴴ := by
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Matrix.mul_assoc]
      using congrArg Matrix.conjTranspose hA
  have h1 : (2 • (ι * ιᴴ) - 1) * (B * ι) = ι * A - B * ι := by
    calc
      (2 • (ι * ιᴴ) - 1) * (B * ι) =
          (2 : ℂ) • (ι * (ιᴴ * B * ι)) - B * ι := by
        simp [two_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
      _ = ι * A - B * ι := by
        rw [hA, Matrix.mul_smul, smul_smul]
        norm_num
  have h2 : Bᴴ * (ι * A - B * ι) = Bᴴ * ι * A - ι := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hreflect : (2 • (ι * ιᴴ) - 1) * ι = ι := by
    simp [two_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, hι]
  have hscaled : (2 • (ι * ιᴴ)) * (Bᴴ * ι * A) = ι * (Aᴴ * A) := by
    calc
      (2 • (ι * ιᴴ)) * (Bᴴ * ι * A) =
          (2 : ℂ) • (ι * (ιᴴ * Bᴴ * ι) * A) := by
        simp [two_smul, Matrix.add_mul, Matrix.mul_assoc]
      _ = ι * (Aᴴ * A) := by
        rw [hAH, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        norm_num [Matrix.mul_assoc]
  have h3 : (2 • (ι * ιᴴ) - 1) * (Bᴴ * ι * A - ι) =
      ι * (Aᴴ * A) - Bᴴ * ι * A - ι := by
    rw [Matrix.mul_sub, hreflect, Matrix.sub_mul, hscaled, Matrix.one_mul]
  dsimp only
  have hout :
      -(B * (2 • (ι * ιᴴ) - 1) * Bᴴ * (2 • (ι * ιᴴ) - 1) * B) * ι =
        ι * A + B * ι * (1 - Aᴴ * A) := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc, h1, h2, h3]
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, hBB, Matrix.one_mul, Matrix.mul_one]
    abel
  refine ⟨hout, ?_⟩
  intro V hV hδ
  have hnι : ‖ι‖ ≤ 1 := oaa_isometry_norm_le_one ι hι
  have hnB : ‖B‖ ≤ 1 := oaa_isometry_norm_le_one B hB
  have hnV : ‖V‖ ≤ 1 := oaa_isometry_norm_le_one V hV
  have hnVH : ‖Vᴴ‖ ≤ 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  let Δ : Matrix D D ℂ := A - V
  let δ : ℝ := ‖Δ‖
  have hδ0 : 0 ≤ δ := norm_nonneg Δ
  have hδ1 : δ ≤ 1 := hδ
  have hAeq : A = V + Δ := by dsimp [Δ]; abel
  have hdefect : 1 - Aᴴ * A = -(Vᴴ * Δ + Δᴴ * V + Δᴴ * Δ) := by
    rw [hAeq, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add, hV]
    abel
  have hndefect : ‖1 - Aᴴ * A‖ ≤ 2 * δ + δ ^ 2 := by
    calc
      ‖1 - Aᴴ * A‖ = ‖Vᴴ * Δ + Δᴴ * V + Δᴴ * Δ‖ := by
        rw [hdefect, norm_neg]
      _ ≤ ‖Vᴴ * Δ‖ + ‖Δᴴ * V‖ + ‖Δᴴ * Δ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖Vᴴ‖ * δ + δ * ‖V‖ + δ * δ := by
        simpa only [Matrix.l2_opNorm_conjTranspose, δ] using
          add_le_add (add_le_add (Matrix.l2_opNorm_mul Vᴴ Δ)
            (Matrix.l2_opNorm_mul Δᴴ V)) (Matrix.l2_opNorm_mul Δᴴ Δ)
      _ ≤ 1 * δ + δ * 1 + δ * δ := by
        gcongr
      _ = 2 * δ + δ ^ 2 := by ring
  have herror :
      -(B * (2 • (ι * ιᴴ) - 1) * Bᴴ * (2 • (ι * ιᴴ) - 1) * B) * ι - ι * V =
        ι * Δ + B * ι * (1 - Aᴴ * A) := by
    rw [hout, Matrix.mul_sub]
    dsimp [Δ]
    rw [Matrix.mul_sub]
    abel
  have hbound :
      ‖-(B * (2 • (ι * ιᴴ) - 1) * Bᴴ * (2 • (ι * ιᴴ) - 1) * B) * ι - ι * V‖ ≤
        3 * δ + δ ^ 2 := by
    rw [herror]
    calc
      ‖ι * Δ + B * ι * (1 - Aᴴ * A)‖ ≤
          ‖ι * Δ‖ + ‖B * ι * (1 - Aᴴ * A)‖ := norm_add_le _ _
      _ ≤ ‖ι‖ * δ + (‖B‖ * ‖ι‖) * ‖1 - Aᴴ * A‖ := by
        apply add_le_add (Matrix.l2_opNorm_mul ι Δ)
        exact (Matrix.l2_opNorm_mul (B * ι) _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul B ι) (norm_nonneg _))
      _ ≤ 1 * δ + (1 * 1) * (2 * δ + δ ^ 2) := by
        gcongr
      _ = 3 * δ + δ ^ 2 := by ring
  refine ⟨hbound, hbound.trans ?_⟩
  change 3 * δ + δ ^ 2 ≤ 4 * δ
  nlinarith

end Qatlib.Papers.CircDepthShen26.ShortTimeBlock
