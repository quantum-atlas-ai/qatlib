/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Qubitization19.MainResults.SourceQubitization
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Papers.Qubitization19.MainResults.FiberPhase

@[expose] public section

/-!
# Signal rotation from the two compressed-oracle identities

The sufficient direction of Lemma 8, arXiv:1610.06546v3, uses only the
identity corner of the squared oracle. Unitarity turns this compression
identity into an exact fixed-vector identity on the signal fiber.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Papers.Qubitization19.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

namespace Qatlib.Papers.Qubitization19.MainResults

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- Eq. (17) translates a compressed matrix into actual action followed by projection. -/
private theorem project_mulVec_signal (U : Matrix (J × I) (J × I) ℂ)
    (j₀ : J) (ψ : QState I) :
    FiberProjector j₀ *ᵥ (U *ᵥ TensorState (Ket j₀) ψ) =
      TensorState (Ket j₀) (BlockCorner U j₀ *ᵥ ψ) := by
  conv_lhs => rw [← fiberProjector_mulVec_tensorState_ket j₀ ψ, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc, fiberProjector_mul_mul_corner, fiberEmbed_mulVec_tensorState_ket]

/-- A unitary with identity corner acts identically on every vector in that fiber. -/
theorem signal_fixed_of_identity_corner (U : Matrix (J × I) (J × I) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ) (j₀ : J) (hcorner : BlockCorner U j₀ = 1)
    (ψ : QState I) :
    U *ᵥ TensorState (Ket j₀) ψ = TensorState (Ket j₀) ψ := by
  let σ := TensorState (Ket j₀) ψ
  have hPσ : FiberProjector j₀ *ᵥ σ = σ := fiberProjector_mulVec_tensorState_ket j₀ ψ
  have hPUσ : FiberProjector j₀ *ᵥ (U *ᵥ σ) = σ := by
    dsimp only [σ]
    rw [project_mulVec_signal, hcorner, Matrix.one_mulVec]
  have hl : Inner σ (U *ᵥ σ) = Inner σ σ := by
    calc Inner σ (U *ᵥ σ) =
        Inner (FiberProjector j₀ *ᵥ σ) (U *ᵥ σ) := by rw [hPσ]
      _ = Inner σ (FiberProjector j₀ *ᵥ (U *ᵥ σ)) := inner_fiberProjector_left _ _ _
      _ = Inner σ σ := by rw [hPUσ]
  have hr : Inner (U *ᵥ σ) σ = Inner σ σ := by
    calc Inner (U *ᵥ σ) σ =
        Inner (U *ᵥ σ) (FiberProjector j₀ *ᵥ σ) := by rw [hPσ]
      _ = Inner (FiberProjector j₀ *ᵥ (U *ᵥ σ)) σ := (inner_fiberProjector_left _ _ _).symm
      _ = Inner σ σ := by rw [hPUσ]
  have hu := inner_applyGate hU σ σ
  change Inner (U *ᵥ σ) (U *ᵥ σ) = Inner σ σ at hu
  let δ := U *ᵥ σ - σ
  have hz : Inner δ δ = 0 := by
    dsimp only [δ]
    rw [qInner_sub_left, qInner_sub_right, qInner_sub_right, hu, hr, hl]
    simp
  have hδ : toEuclidean_fromVec δ = 0 := by
    apply inner_self_eq_zero (𝕜 := ℂ).mp
    rwa [inner_euclidean_fromVec]
  have := congrArg toVec_fromEuclidean hδ
  change δ = 0 at this
  exact sub_eq_zero.mp this

/-- Lemma 8's walk has the input signal corner and is unitary under Eq. (17). -/
theorem eq17_walk_encoding (U : Matrix (J × I) (J × I) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hcorner : BlockCorner U j₀ = A) :
    IsBlockEncoding (FiberReflection j₀ * U) j₀ A 1 := by
  refine ⟨mul_mem (fiberReflection_unitary j₀) hU, by norm_num, ?_⟩
  rw [inv_one, Complex.ofReal_one, one_smul, ← hcorner]
  have hR : FiberReflection j₀ * U = (2 : ℂ) • (FiberProjector j₀ * U) - U := by
    rw [FiberReflection, ReflectionAbout, Matrix.sub_mul, Matrix.smul_mul, one_mul]
  ext i k
  rw [blockCorner_apply, blockCorner_apply, hR, Matrix.sub_apply, Matrix.smul_apply,
    fiberProjector_mul]
  simp
  ring

/-- On an interior normalized eigenbranch, the Eq. (17) identities give the two
orthonormal states and the two column actions of the rotation in Eq. (5). -/
theorem eq17_rotation_vectors (U : Matrix (J × I) (J × I) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hc : BlockCorner U j₀ = A) (h2 : BlockCorner (U * U) j₀ = 1)
    (ψ : QState I) (hψ : Normalized ψ) (x : ℝ) (hx : |x| < 1)
    (hAψ : A *ᵥ ψ = (x : ℂ) • ψ) :
    let σ := TensorState (Ket j₀) ψ
    let G := FiberReflection j₀ * U
    let s := Real.sqrt (1 - x ^ 2)
    ∃ χ : QState (J × I), Normalized σ ∧ Normalized χ ∧ Inner σ χ = 0 ∧
      FiberProjector j₀ *ᵥ χ = 0 ∧
      G *ᵥ σ = (x : ℂ) • σ + (s : ℂ) • χ ∧
      G *ᵥ χ = -(s : ℂ) • σ + (x : ℂ) • χ := by
  let σ := TensorState (Ket j₀) ψ
  let G := FiberReflection j₀ * U
  let s := Real.sqrt (1 - x ^ 2)
  have hx2 : x ^ 2 < 1 := by nlinarith [abs_lt.mp hx]
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hx2)
  have hss : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hx2.le)
  have hssC : (s : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by exact_mod_cast hss
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  let v := (x : ℂ) • σ - U *ᵥ σ
  let χ := (s : ℂ)⁻¹ • v
  have hsχ : (s : ℂ) • χ = v := by
    dsimp only [χ]
    rw [smul_smul, mul_inv_cancel₀ hsC, one_smul]
  have hσ : Normalized σ := normalized_tensorState (normalized_ket j₀) hψ
  have hPσ : FiberProjector j₀ *ᵥ σ = σ := fiberProjector_mulVec_tensorState_ket j₀ ψ
  have hPUσ : FiberProjector j₀ *ᵥ (U *ᵥ σ) = (x : ℂ) • σ := by
    dsimp only [σ]
    rw [project_mulVec_signal, hc, hAψ, tensorState_smul_ket_right]
  have hPv : FiberProjector j₀ *ᵥ v = 0 := by
    dsimp only [v]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hPσ, hPUσ, sub_self]
  have hPχ : FiberProjector j₀ *ᵥ χ = 0 := by
    dsimp only [χ]
    rw [Matrix.mulVec_smul, hPv, smul_zero]
  have hσ1 := (normalized_iff_inner_self σ).mp hσ
  have hσU : Inner σ (U *ᵥ σ) = (x : ℂ) := by
    calc Inner σ (U *ᵥ σ) = Inner (FiberProjector j₀ *ᵥ σ) (U *ᵥ σ) := by rw [hPσ]
      _ = Inner σ (FiberProjector j₀ *ᵥ (U *ᵥ σ)) := inner_fiberProjector_left _ _ _
      _ = (x : ℂ) := by rw [hPUσ, qInner_smul_right, hσ1, mul_one]
  have hUσ : Inner (U *ᵥ σ) σ = (x : ℂ) := by
    rw [BornBridge.inner_conj_symm, hσU, starRingEnd_ofReal]
  have hUU := (inner_applyGate hU σ σ).trans hσ1
  change Inner (U *ᵥ σ) (U *ᵥ σ) = 1 at hUU
  have hvv : Inner v v = (s : ℂ) ^ 2 := by
    dsimp only [v]
    rw [qInner_sub_left, qInner_sub_right, qInner_sub_right,
      qInner_smul_left, qInner_smul_left, qInner_smul_right, qInner_smul_right,
      hσ1, hσU, hUσ, hUU, starRingEnd_ofReal, hssC]
    ring
  have hχ : Normalized χ := by
    dsimp only [χ]
    rw [normalized_iff_inner_self, qInner_smul_left, qInner_smul_right, hvv,
      ← Complex.ofReal_inv, starRingEnd_ofReal, Complex.ofReal_inv]
    field_simp
  have hσχ : Inner σ χ = 0 := by
    rw [← hPσ, inner_fiberProjector_left, hPχ, inner_apply]
    simp
  have hRσ : FiberReflection j₀ *ᵥ σ = σ := by
    rw [fiberReflection_mulVec, hPσ, two_smul]
    abel
  have hGσ : G *ᵥ σ = (x : ℂ) • σ + (s : ℂ) • χ := by
    dsimp only [G]
    rw [← Matrix.mulVec_mulVec, fiberReflection_mulVec, hPUσ, hsχ]
    dsimp only [v]
    rw [two_smul]
    abel
  have hU2σ : U *ᵥ (U *ᵥ σ) = σ := by
    rw [Matrix.mulVec_mulVec]
    exact signal_fixed_of_identity_corner (U * U) (mul_mem hU hU) j₀ h2 ψ
  have hGχ : G *ᵥ χ = -(s : ℂ) • σ + (x : ℂ) • χ := by
    apply smul_right_injective (QState (J × I)) hsC
    dsimp only
    rw [← Matrix.mulVec_smul, hsχ]
    dsimp only [v]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    have hGUσ : G *ᵥ (U *ᵥ σ) = σ := by
      dsimp only [G]
      rw [← Matrix.mulVec_mulVec, hU2σ, hRσ]
    rw [hGUσ, hGσ, smul_add, smul_add, smul_smul, smul_smul,
      smul_smul, smul_smul, mul_neg, ← pow_two, ← pow_two, hssC]
    module
  exact ⟨χ, hσ, hχ, hσχ, hPχ, hGσ, hGχ⟩

/-- The sufficient direction of Lemma 8 for the actual oracle and signal rotation. -/
theorem lemma8_eq17_rotation (V : Matrix (J × I) (J × I) ℂ) (S : Matrix J J ℂ)
    (j₀ : J) (A : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup (J × I) ℂ)
    (hS : S ∈ Matrix.unitaryGroup J ℂ) (h17 : QubitizationConditionsEq17 V S j₀ A) :
    let G := FiberReflection j₀ * (TensorGate S (1 : Matrix I I ℂ) * V)
    IsBlockEncoding G j₀ A 1 ∧ Eq5RotationAction G A := by
  let U := TensorGate S (1 : Matrix I I ℂ) * V
  have hU : U ∈ Matrix.unitaryGroup (J × I) ℂ :=
    mul_mem (tensorGate_unitary hS (one_mem _)) hV
  obtain ⟨hc, h2⟩ : BlockCorner U j₀ = A ∧ BlockCorner (U * U) j₀ = 1 := h17
  refine ⟨eq17_walk_encoding U hU j₀ A hc, ?_⟩
  intro ψ hψ x hx hAψ
  obtain ⟨χ, hσ, hn, horth, _, h0, h1⟩ :=
    eq17_rotation_vectors U hU j₀ A hc h2 ψ hψ x hx hAψ
  let s := Real.sqrt (1 - x ^ 2)
  have hx2 : x ^ 2 < 1 := by nlinarith [abs_lt.mp hx]
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr hx2)
  have hss := Real.sq_sqrt (sub_nonneg.mpr hx2.le)
  refine ⟨TensorState (Ket j₀) ψ, -χ, s, hσ, ?_, ?_, ?_, ?_, hs, by linarith⟩
  · rw [← neg_one_smul ℂ χ, normalized_iff_inner_self, qInner_smul_left,
      qInner_smul_right, (normalized_iff_inner_self χ).mp hn]
    norm_num
  · rw [← neg_one_smul ℂ χ, qInner_smul_right, horth, mul_zero]
  · simpa only [smul_neg, sub_neg_eq_add] using h0
  · rw [Matrix.mulVec_neg, h1, neg_add, neg_smul, neg_neg, smul_neg]

/-- The rotation frame supplied by Eq. (17) also realizes the phases of Lemma 11. -/
theorem eq17_phased_frame {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix (J × I) (J × I) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hc : BlockCorner U j₀ = A) (h2 : BlockCorner (U * U) j₀ = 1)
    (ψ : QState I) (hψ : Normalized ψ) (x φ : ℝ) (hx : |x| < 1)
    (hAψ : A *ᵥ ψ = (x : ℂ) • ψ) :
    ∃ E : Matrix (J × I) (Fin 2) ℂ,
      E.col 0 = TensorState (Ket j₀) ψ ∧ Normalized (E.col 1) ∧
      FiberProjector j₀ *ᵥ E.col 1 = 0 ∧
      fiberPhasedIterate j₀ (FiberReflection j₀ * U) φ * E =
        E * !![(x : ℂ), -Complex.I * Complex.exp (-Complex.I * (φ : ℂ)) *
            ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ);
          -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) *
            ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ), (x : ℂ)] := by
  obtain ⟨χ, _, hn, _, hP, h0, h1⟩ := eq17_rotation_vectors U hU j₀ A hc h2 ψ hψ x hx hAψ
  let E : Matrix (J × I) (Fin 2) ℂ := Matrix.of fun k => ![TensorState (Ket j₀) ψ k, χ k]
  have he₀ : E.col 0 = TensorState (Ket j₀) ψ := rfl
  have he₁ : E.col 1 = χ := rfl
  refine ⟨E, he₀, he₁.symm ▸ hn, he₁.symm ▸ hP, ?_⟩
  refine fiberPhasedIterate_frame j₀ φ x (abs_lt.mp hx).1.le (abs_lt.mp hx).2.le
    (FiberReflection j₀ * U) E ψ χ hP he₀ he₁ ?_
  ext k j
  fin_cases j
  · have hh := congrFun h0 k
    simpa [E, eq5Rotation, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      mul_comm] using hh
  · have hh := congrFun h1 k
    simpa [E, eq5Rotation, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      mul_comm] using hh

end Qatlib.Papers.Qubitization19.MainResults
