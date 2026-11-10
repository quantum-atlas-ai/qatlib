/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SignalPrimitive.LCUConsumers

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def FiberPhaseGate (j₀ : J) (c : ℂ) : Matrix (J × I) (J × I) ℂ :=
  1 + (c - 1) • FiberProjector j₀

theorem fiberPhaseGate_eq (j₀ : J) (c : ℂ) :
    FiberPhaseGate (I := I) j₀ c = 1 + (c - 1) • FiberProjector j₀ := rfl

theorem fiberPhaseGate_split (j₀ : J) (c : ℂ) :
    FiberPhaseGate (I := I) j₀ c
      = (1 - FiberProjector j₀) + c • FiberProjector j₀ := by
  rw [fiberPhaseGate_eq]
  module

theorem fiberPhaseGate_mul (j₀ : J) (c : ℂ) (M : Matrix (J × I) (J × I) ℂ) :
    FiberPhaseGate (I := I) j₀ c * M = M + (c - 1) • (FiberProjector j₀ * M) := by
  rw [fiberPhaseGate_eq, Matrix.add_mul, Matrix.one_mul, smul_mul_assoc]

theorem fiberPhaseGate_mul_fiberProjector (j₀ : J) (c : ℂ) :
    FiberPhaseGate (I := I) j₀ c * FiberProjector j₀ = c • FiberProjector j₀ := by
  rw [fiberPhaseGate_eq, Matrix.add_mul, Matrix.one_mul, smul_mul_assoc,
    fiberProjector_idempotent]
  module

theorem fiberProjector_mul_fiberPhaseGate (j₀ : J) (c : ℂ) :
    FiberProjector (I := I) j₀ * FiberPhaseGate j₀ c = c • FiberProjector j₀ := by
  rw [fiberPhaseGate_eq, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    fiberProjector_idempotent]
  module

theorem fiberProjector_mul_one_sub (j₀ : J) :
    FiberProjector (I := I) j₀ * (1 - FiberProjector j₀) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, fiberProjector_idempotent, sub_self]

theorem one_sub_fiberProjector_mul_fiberProjector (j₀ : J) :
    (1 - FiberProjector (I := I) j₀) * FiberProjector j₀ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, fiberProjector_idempotent, sub_self]

theorem one_sub_fiberProjector_mul_self (j₀ : J) :
    (1 - FiberProjector (I := I) j₀) * (1 - FiberProjector j₀)
      = 1 - FiberProjector j₀ := by
  rw [Matrix.mul_sub, Matrix.mul_one, one_sub_fiberProjector_mul_fiberProjector,
    sub_zero]

theorem fiberPhaseGate_unitary (j₀ : J) {c : ℂ} (hc : c * (starRingEnd ℂ) c = 1) :
    FiberPhaseGate (I := I) j₀ c ∈ Matrix.unitaryGroup (J × I) ℂ := by
  have hct : (FiberPhaseGate (I := I) j₀ c)ᴴ
      = (1 - FiberProjector j₀) + (starRingEnd ℂ) c • FiberProjector j₀ := by
    rw [fiberPhaseGate_split, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      fiberProjector_hermitian, starRingEnd_apply]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hct,
    fiberPhaseGate_split]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, smul_mul_assoc,
    smul_smul, fiberProjector_mul_one_sub, one_sub_fiberProjector_mul_fiberProjector,
    fiberProjector_idempotent, smul_zero, add_zero, zero_add]
  rw [one_sub_fiberProjector_mul_self, hc, one_smul]
  module

theorem fiberEmbed_smul (j₀ : J) (c : ℂ) (M : Matrix I I ℂ) :
    FiberEmbed j₀ (c • M) = c • FiberEmbed j₀ M := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  simp only [fiberEmbed_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : a = j₀ ∧ b = j₀
  · simp [h]
  · simp [h]

theorem fiberEmbed_add (j₀ : J) (M N : Matrix I I ℂ) :
    FiberEmbed j₀ (M + N) = FiberEmbed j₀ M + FiberEmbed j₀ N := by
  ext ⟨a, i⟩ ⟨b, i'⟩
  simp only [fiberEmbed_apply, Matrix.add_apply]
  by_cases h : a = j₀ ∧ b = j₀
  · simp [h]
  · simp [h]

theorem fiberEmbed_mul_fiberProjector (j₀ : J) (M : Matrix I I ℂ) :
    FiberEmbed j₀ M * FiberProjector j₀ = FiberEmbed j₀ M := by
  rw [fiberProjector_eq_fiberEmbed_one, fiberEmbed_mul, mul_one]

theorem fiberEmbed_mul_one_sub_fiberProjector (j₀ : J) (M : Matrix I I ℂ) :
    FiberEmbed j₀ M * (1 - FiberProjector j₀) = 0 := by
  have h := fiberEmbed_mul_fiberProjector j₀ M
  calc FiberEmbed j₀ M * (1 - FiberProjector j₀)
      = FiberEmbed j₀ M * 1 - FiberEmbed j₀ M * FiberProjector j₀ := by
        rw [Matrix.mul_sub, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.mul_one, sub_self]

theorem fiberEmbed_mul_mul_fiberProjector (j₀ : J) (M : Matrix I I ℂ)
    (N : Matrix (J × I) (J × I) ℂ) :
    FiberEmbed j₀ M * (N * FiberProjector j₀)
      = FiberEmbed j₀ M * (FiberProjector j₀ * (N * FiberProjector j₀)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    fiberEmbed_mul_fiberProjector]

theorem projected_conjTranspose {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} (h : FiberProjector j₀ * (U * FiberProjector j₀)
      = FiberEmbed j₀ A) :
    FiberProjector j₀ * (Uᴴ * FiberProjector j₀) = FiberEmbed j₀ Aᴴ := by
  have h1 : (FiberProjector j₀ * (U * FiberProjector j₀))ᴴ
      = FiberProjector j₀ * (Uᴴ * FiberProjector j₀) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, fiberProjector_hermitian,
      Matrix.mul_assoc]
  rw [← h1, h, fiberEmbed_conjTranspose]

noncomputable def QSVTWord (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (c₀ c₁ c₂ c₃ : ℂ) :
    Matrix (J × I) (J × I) ℂ :=
  FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ * FiberPhaseGate j₀ c₁ * U
    * FiberPhaseGate j₀ c₀

theorem qsvtWord_eq (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (c₀ c₁ c₂ c₃ : ℂ) :
    QSVTWord U j₀ c₀ c₁ c₂ c₃
      = FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ * FiberPhaseGate j₀ c₁
          * U * FiberPhaseGate j₀ c₀ := rfl

set_option maxHeartbeats 400000 in

theorem qsvtWord_unitary (U : Matrix (J × I) (J × I) ℂ) (j₀ : J) (c₀ c₁ c₂ c₃ : ℂ)
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ)
    (hc₀ : c₀ * (starRingEnd ℂ) c₀ = 1) (hc₁ : c₁ * (starRingEnd ℂ) c₁ = 1)
    (hc₂ : c₂ * (starRingEnd ℂ) c₂ = 1) (hc₃ : c₃ * (starRingEnd ℂ) c₃ = 1) :
    QSVTWord U j₀ c₀ c₁ c₂ c₃ ∈ Matrix.unitaryGroup (J × I) ℂ := by
  have hstep : ∀ (X Y : Matrix (J × I) (J × I) ℂ),
      X ∈ Matrix.unitaryGroup (J × I) ℂ → Y ∈ Matrix.unitaryGroup (J × I) ℂ →
      X * Y ∈ Matrix.unitaryGroup (J × I) ℂ := by
    intro X Y hX hY
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hX hY ⊢
    calc (X * Y)ᴴ * (X * Y) = Yᴴ * (Xᴴ * X) * Y := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Yᴴ * 1 * Y := by rw [hX]
      _ = 1 := by rw [Matrix.mul_one, hY]
  have hUct : Uᴴ ∈ Matrix.unitaryGroup (J × I) ℂ := by
    have h1 : U * Uᴴ = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff).mp hU
      rwa [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact h1
  show (FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ * FiberPhaseGate j₀ c₁
      * U * FiberPhaseGate j₀ c₀) ∈ Matrix.unitaryGroup (J × I) ℂ
  have p1 : FiberPhaseGate j₀ c₃ * U ∈ Matrix.unitaryGroup (J × I) ℂ :=
    hstep _ _ (fiberPhaseGate_unitary j₀ hc₃) hU
  have p2 : FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂
      ∈ Matrix.unitaryGroup (J × I) ℂ :=
    hstep _ _ p1 (fiberPhaseGate_unitary j₀ hc₂)
  have p3 : FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ
      ∈ Matrix.unitaryGroup (J × I) ℂ := hstep _ _ p2 hUct
  have p4 : FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ
      * FiberPhaseGate j₀ c₁ ∈ Matrix.unitaryGroup (J × I) ℂ :=
    hstep _ _ p3 (fiberPhaseGate_unitary j₀ hc₁)
  have p5 : FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ
      * FiberPhaseGate j₀ c₁ * U ∈ Matrix.unitaryGroup (J × I) ℂ :=
    hstep _ _ p4 hU
  exact hstep _ _ p5 (fiberPhaseGate_unitary j₀ hc₀)

theorem qsvt_middle_corner {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} (hUUct : U * Uᴴ = 1)
    (hA : FiberProjector j₀ * (U * FiberProjector j₀) = FiberEmbed j₀ A)
    (c₂ : ℂ) :
    FiberProjector j₀ * (U * (FiberPhaseGate j₀ c₂ * Uᴴ)) * FiberProjector j₀
      = FiberEmbed j₀ (1 + (c₂ - 1) • (A * Aᴴ)) := by
  have h2 : FiberPhaseGate j₀ c₂ * Uᴴ
      = Uᴴ + (c₂ - 1) • (FiberProjector j₀ * Uᴴ) := fiberPhaseGate_mul j₀ c₂ Uᴴ
  rw [h2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.add_mul, smul_mul_assoc]
  have hfirst : FiberProjector j₀ * (U * Uᴴ) * FiberProjector j₀
      = FiberEmbed j₀ (1 : Matrix I I ℂ) := by
    rw [hUUct, Matrix.mul_one, fiberProjector_idempotent,
      fiberProjector_eq_fiberEmbed_one]
  have hsecond : FiberProjector j₀ * (U * (FiberProjector j₀ * Uᴴ))
        * FiberProjector j₀ = FiberEmbed j₀ (A * Aᴴ) := by
    have hassoc : FiberProjector j₀ * (U * (FiberProjector j₀ * Uᴴ))
          * FiberProjector j₀
        = (FiberProjector j₀ * (U * FiberProjector j₀))
            * (Uᴴ * FiberProjector j₀) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc, hA, fiberEmbed_mul_mul_fiberProjector, projected_conjTranspose hA,
      fiberEmbed_mul]
  rw [hfirst, hsecond, ← fiberEmbed_smul, ← fiberEmbed_add]

theorem qsvt_projected_corner {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} (h : IsProjectedEncoding U j₀ A 1) (c₀ c₁ c₂ c₃ : ℂ) :
    FiberProjector j₀ * (QSVTWord U j₀ c₀ c₁ c₂ c₃ * FiberProjector j₀)
      = FiberEmbed j₀ ((c₀ * c₂ * c₃) • A
          + (c₀ * (c₁ - 1) * c₃) • ((1 + (c₂ - 1) • (A * Aᴴ)) * A)) := by
  have hA : FiberProjector j₀ * (U * FiberProjector j₀) = FiberEmbed j₀ A := by
    simpa using h.2.2
  have hUUct : U * Uᴴ = 1 := by
    have h1 := (Matrix.mem_unitaryGroup_iff).mp h.1
    rwa [Matrix.star_eq_conjTranspose] at h1
  have hUctU : Uᴴ * U = 1 := by
    have h1 := (Matrix.mem_unitaryGroup_iff').mp h.1
    rwa [Matrix.star_eq_conjTranspose] at h1

  have eA : QSVTWord U j₀ c₀ c₁ c₂ c₃ * FiberProjector j₀
      = c₀ • (FiberPhaseGate j₀ c₃ * U * FiberPhaseGate j₀ c₂ * Uᴴ
          * FiberPhaseGate j₀ c₁ * U * FiberProjector j₀) := by
    rw [qsvtWord_eq, Matrix.mul_assoc, fiberPhaseGate_mul_fiberProjector,
      Matrix.mul_smul]
  have eB : FiberProjector j₀ * (c₀ • (FiberPhaseGate j₀ c₃ * U
          * FiberPhaseGate j₀ c₂ * Uᴴ * FiberPhaseGate j₀ c₁ * U
          * FiberProjector j₀))
      = (c₀ * c₃) • (FiberProjector j₀ * (U * (FiberPhaseGate j₀ c₂
          * (Uᴴ * (FiberPhaseGate j₀ c₁ * U)))) * FiberProjector j₀) := by
    rw [Matrix.mul_smul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, fiberProjector_mul_fiberPhaseGate, smul_mul_assoc,
      smul_smul]
  rw [eA, eB]

  have h1 : FiberPhaseGate j₀ c₁ * U
      = U + (c₁ - 1) • (FiberProjector j₀ * U) := fiberPhaseGate_mul j₀ c₁ U
  rw [h1, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.add_mul, smul_mul_assoc]

  have hassoc1 : FiberProjector j₀ * (U * (FiberPhaseGate j₀ c₂ * (Uᴴ * U)))
        * FiberProjector j₀
      = ((FiberProjector j₀ * (U * FiberPhaseGate j₀ c₂)) * (Uᴴ * U))
          * FiberProjector j₀ := by
    simp only [Matrix.mul_assoc]
  rw [hassoc1, hUctU, Matrix.mul_one]
  have hassoc2 : (FiberProjector j₀ * (U * FiberPhaseGate j₀ c₂))
        * FiberProjector j₀
      = (FiberProjector j₀ * U) * (FiberPhaseGate j₀ c₂ * FiberProjector j₀) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc2, fiberPhaseGate_mul_fiberProjector, Matrix.mul_smul]
  have hassoc3 : (FiberProjector j₀ * U) * FiberProjector j₀
      = FiberProjector j₀ * (U * FiberProjector j₀) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc3, hA]

  have hassoc4 : FiberProjector j₀ * (U * (FiberPhaseGate j₀ c₂
          * (Uᴴ * (FiberProjector j₀ * U)))) * FiberProjector j₀
      = (FiberProjector j₀ * (U * (FiberPhaseGate j₀ c₂ * Uᴴ))
          * FiberProjector j₀) * (U * FiberProjector j₀) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc4, qsvt_middle_corner hUUct hA c₂, fiberEmbed_mul_mul_fiberProjector,
    hA, fiberEmbed_mul]

  rw [smul_add, smul_smul, smul_smul, ← fiberEmbed_smul, ← fiberEmbed_smul,
    ← fiberEmbed_add,
    show (c₀ * c₃) * c₂ = c₀ * c₂ * c₃ from by ring,
    show (c₀ * c₃) * (c₁ - 1) = c₀ * (c₁ - 1) * c₃ from by ring]

theorem qsvt_singularValue_action {A : Matrix I I ℂ} (c₀ c₁ c₂ c₃ : ℂ)
    {v w : QState I} {σ : ℝ}
    (hv : A *ᵥ v = ((σ : ℝ) : ℂ) • w) (hw : Aᴴ *ᵥ w = ((σ : ℝ) : ℂ) • v) :
    ((c₀ * c₂ * c₃) • A + (c₀ * (c₁ - 1) * c₃) • ((1 + (c₂ - 1) • (A * Aᴴ)) * A))
      *ᵥ v
      = (c₀ * c₂ * c₃ * ((σ : ℝ) : ℂ)
          + c₀ * (c₁ - 1) * c₃ * ((1 : ℂ) + (c₂ - 1) * ((σ : ℝ) : ℂ) ^ 2)
            * ((σ : ℝ) : ℂ)) • w := by
  have hAActW : (A * Aᴴ) *ᵥ w = ((σ : ℝ) : ℂ) ^ 2 • w := by
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, hv, smul_smul, ← pow_two]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, hv, smul_smul,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAActW, smul_smul]
  module

end Qatlib.Concepts.SignalPrimitive.LCUConsumers
