/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
public import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
public import Qatlib.Concepts.SignalPrimitive.LCUConsumers.InvariantSubspaceSubgoal
public import Qatlib.Concepts.SignalPrimitive.MainResults.InvariantSubspaceSubgoal
public import Qatlib.Papers.Qubitization19.LCUConsumers.SourceLCU
public import Qatlib.Papers.Qubitization19.MainResults.SourceDefinitions

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.SignalPrimitive.LCUConsumers

open Qatlib.Papers.Qubitization19.LCUConsumers

open Qatlib.Papers.Qubitization19.MainResults

namespace Qatlib.Papers.Qubitization19.MainResults

section

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Disambiguated local name for the frozen `Inner` scalar rule (the root
`inner_smul_left` of Mathlib's abstract inner-product spaces has the same name). -/
theorem qInner_smul_left (c : ℂ) (ψ φ : QState I) :
    Inner (c • ψ) φ = (starRingEnd ℂ) c * Inner ψ φ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left c ψ φ

omit [DecidableEq I] in
/-- Disambiguated local name for the frozen right-linearity rule. -/
theorem qInner_smul_right (c : ℂ) (ψ φ : QState I) :
    Inner ψ (c • φ) = c * Inner ψ φ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right c ψ φ

omit [DecidableEq I] in
/-- Disambiguated local name for the frozen left-subtraction rule. -/
theorem qInner_sub_left (ψ φ χ : QState I) :
    Inner (ψ - φ) χ = Inner ψ χ - Inner φ χ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_left ψ φ χ

omit [DecidableEq I] in
/-- Disambiguated local name for the frozen right-subtraction rule. -/
theorem qInner_sub_right (ψ φ χ : QState I) :
    Inner ψ (φ - χ) = Inner ψ φ - Inner ψ χ :=
  Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_sub_right ψ φ χ

/-- Fixed arXiv:1610.06546v3, Theorem 2 (PDF p.6), LCU/matrix form: the frozen
`InvariantSubspaceSubgoal` contract — for a Hermitian LCU signal
`A = ∑ j, w j • U j` with unitary Hermitian summands, every normalized
eigenstate `ψ` with real eigenvalue `x`, `|x| < 1`, spans with its normalized
orthogonal remnant a two-dimensional invariant plane of the qubitized walk, on
which the walk rotates by `cos(2θ) = 2x² − 1`, `sin(2θ) = 2xy`,
`y = √(1−x²)`. Proved by `Qatlib.Concepts.SignalPrimitive.MainResults.invariantSubspaceSubgoal`
through the frozen `qubitization_invariant_subspace`. -/
theorem theorem2_lcu_walk_invariant_subspace :
    Qatlib.Concepts.SignalPrimitive.LCUConsumers.InvariantSubspaceSubgoal :=
  Qatlib.Concepts.SignalPrimitive.MainResults.invariantSubspaceSubgoal

/-- The matrix-level content of "the iterate `G` has the same signal operator in
the same basis and acts as the `θ_λ = cos⁻¹ λ` rotation on the `SU(2)` invariant
subspace": for every normalized eigenstate `ψ` of `A` with eigenvalue `x`,
`|x| < 1`, there is a normalized orthogonal remnant `ψ₁` and `y = √(1−x²)` with
`G ψ = x ψ − y ψ₁` on the eigenbranch and `G ψ₁ = y ψ + x ψ₁`. This is the
paper's Eqs. (5)–(6) in matrix form, shared by Lemma 8 and Corollary 9. -/
def Eq5RotationAction (G : Matrix (J × I) (J × I) ℂ) (A : Matrix I I ℂ) : Prop :=
  ∀ (ψ : QState I), Normalized ψ → ∀ (x : ℝ), |x| < 1 →
    A *ᵥ ψ = ((x : ℝ) : ℂ) • ψ →
    ∃ (ψ₀ ψ₁ : QState (J × I)) (y : ℝ),
      Normalized ψ₀ ∧ Normalized ψ₁ ∧ Inner ψ₀ ψ₁ = 0 ∧
      G *ᵥ ψ₀ = ((x : ℝ) : ℂ) • ψ₀ - ((y : ℝ) : ℂ) • ψ₁ ∧
      G *ᵥ ψ₁ = ((y : ℝ) : ℂ) • ψ₀ + ((x : ℝ) : ℂ) • ψ₁ ∧
      0 < y ∧ x ^ 2 + y ^ 2 = 1

/-- The conditions of Eq. (17) of arXiv:1610.06546v3 (PDF p.9) for the ansatz
`Ŵ = (2|G⟩⟨G| − I) Ŝ Û` on a flag-free workspace: the combined oracle
`Ŵ_c = (Ŝ ⊗ I) Û` has signal operator `A` and squares to the identity on the
signal fiber. -/
def QubitizationConditionsEq17 (V : Matrix (J × I) (J × I) ℂ)
    (S : Matrix J J ℂ) (j₀ : J) (A : Matrix I I ℂ) : Prop :=
  let Wc : Matrix (J × I) (J × I) ℂ := TensorGate S (1 : Matrix I I ℂ) * V
  BlockCorner Wc j₀ = A ∧ BlockCorner (Wc * Wc) j₀ = 1

/-- Fixed arXiv:1610.06546v3, Corollary 9 (PDF p.10): qubitization of
reflections. If the signal oracle `V` is a unitary involution (`V * V = 1`)
encoding a Hermitian signal `A` in standard form at scale 1, then the paper's
iterate `Ŵ = (2|G⟩⟨G| − I) V = FiberReflection j₀ * V` encodes the *same*
signal operator (`BlockCorner Ŵ j₀ = A`) and acts on each eigenbranch as the
rotation of Eq. (5) with the eigenphase `θ_λ = cos⁻¹ λ`, i.e.
`Ŵ ψ₀ = x ψ₀ − y ψ₁`, `Ŵ ψ₁ = y ψ₀ + x ψ₁`, `y = √(1−x²)`.

This is proved directly for the paper's iterate (not its square), reusing the
frozen fiber calculus (`fiberReflection_mulVec`,
`fiberProjector_mulVec_tensorState_ket`, `inner_applyGate`, and the frozen
inner-product algebra). -/
theorem corollary9_reflection_qubitization
    (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hV : IsBlockEncoding V j₀ A 1) (_hA : Aᴴ = A) (hV2 : V * V = 1) :
    BlockCorner (FiberReflection j₀ * V) j₀ = A ∧
      Eq5RotationAction (FiberReflection j₀ * V) A := by
  have hRentry : ∀ (i : I) (x : J × I),
      FiberReflection j₀ (j₀, i) x = if x = (j₀, i) then 1 else 0 := by
    intro i x
    obtain ⟨k, l⟩ := x
    by_cases h : (k, l) = (j₀, i)
    · rw [ite_eq_left h, h]
      rw [FiberReflection, Qatlib.Foundations.PureStateMath.Reflection.ReflectionAbout, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, fiberProjector_apply, ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl]
      norm_num
    · rw [ite_eq_right h]
      rw [FiberReflection, Qatlib.Foundations.PureStateMath.Reflection.ReflectionAbout, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, fiberProjector_apply]
      have h1 : ¬ (j₀ = j₀ ∧ (j₀, i) = (k, l)) := fun hh => h hh.2.symm
      have h2 : ¬ ((j₀, i) = (k, l)) := fun hh => h hh.symm
      rw [ite_eq_right h1, ite_eq_right h2]
      norm_num
  have hcorn : BlockCorner V j₀ = A := by simpa using hV.2.2
  constructor
  · ext i i'
    rw [blockCorner_apply, Matrix.mul_apply,
      Finset.sum_eq_single (j₀, i)]
    · rw [hRentry i (j₀, i), ite_eq_left rfl, one_mul, ← hcorn, blockCorner_apply]
    · intro x _ hx
      rw [hRentry i x, ite_eq_right hx, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · intro ψ hψ x hx1 hx
    have hx2lt : x ^ 2 < 1 := by
      have h1 : |x| < 1 := hx1
      have h2 : |x| ^ 2 < 1 ^ 2 := by nlinarith [abs_nonneg x, h1]
      rwa [one_pow, sq_abs] at h2
    set y : ℝ := Real.sqrt (1 - x ^ 2) with hydef
    have hy : 0 < y := Real.sqrt_pos.mpr (by nlinarith)
    have hy2 : y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
    have hy2c : (((y : ℝ) : ℂ) * ((y : ℝ) : ℂ)) = ((1 - x ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, show y * y = 1 - x ^ 2 by rw [← sq, hy2]]
    have hyne : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    set ψ₀ : QState (J × I) := TensorState (Ket j₀) ψ with hψ₀def
    set φ : QState (J × I) := V *ᵥ ψ₀ - ((x : ℝ) : ℂ) • ψ₀ with hφdef
    set ψ₁ : QState (J × I) := (((y : ℝ) : ℂ))⁻¹ • φ with hψ₁def
    have hψ₀ : Normalized ψ₀ := normalized_tensorState (normalized_ket j₀) hψ
    have hPfix : FiberProjector j₀ *ᵥ ψ₀ = ψ₀ := fiberProjector_mulVec_tensorState_ket j₀ ψ
    have hPVP : FiberProjector j₀ * (V * FiberProjector j₀) = FiberEmbed j₀ A := by
      rw [fiberProjector_mul_mul_corner, hcorn]
    have hPVψ₀ : FiberProjector j₀ *ᵥ (V *ᵥ ψ₀) = ((x : ℝ) : ℂ) • ψ₀ := by
      rw [show V *ᵥ ψ₀ = V *ᵥ (FiberProjector j₀ *ᵥ ψ₀) by rw [hPfix]]
      rw [show FiberProjector j₀ *ᵥ (V *ᵥ (FiberProjector j₀ *ᵥ ψ₀))
            = (FiberProjector j₀ * (V * FiberProjector j₀)) *ᵥ ψ₀ by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
      rw [hPVP, fiberEmbed_mulVec_tensorState_ket j₀ A ψ, hx,
        tensorState_smul_ket_right, hψ₀def]
    have hPiPhi : FiberProjector j₀ *ᵥ φ = 0 := by
      rw [hφdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hPVψ₀, hPfix]
      simp
    have h00 : Inner ψ₀ ψ₀ = 1 := (normalized_iff_inner_self ψ₀).mp hψ₀
    have h0V : Inner ψ₀ (V *ᵥ ψ₀) = ((x : ℝ) : ℂ) := by
      calc Inner ψ₀ (V *ᵥ ψ₀)
          = Inner (FiberProjector j₀ *ᵥ ψ₀) (V *ᵥ ψ₀) := by rw [hPfix]
        _ = Inner ψ₀ (FiberProjector j₀ *ᵥ (V *ᵥ ψ₀)) :=
              inner_fiberProjector_left _ _ _
        _ = Inner ψ₀ (((x : ℝ) : ℂ) • ψ₀) := by rw [hPVψ₀]
        _ = ((x : ℝ) : ℂ) * Inner ψ₀ ψ₀ := qInner_smul_right _ _ _
        _ = ((x : ℝ) : ℂ) := by rw [h00, mul_one]
    have hV0 : Inner (V *ᵥ ψ₀) ψ₀ = ((x : ℝ) : ℂ) := by
      calc Inner (V *ᵥ ψ₀) ψ₀
          = Inner (V *ᵥ ψ₀) (FiberProjector j₀ *ᵥ ψ₀) := by rw [hPfix]
        _ = Inner (FiberProjector j₀ *ᵥ (V *ᵥ ψ₀)) ψ₀ :=
              (inner_fiberProjector_left _ _ _).symm
        _ = Inner (((x : ℝ) : ℂ) • ψ₀) ψ₀ := by rw [hPVψ₀]
        _ = (starRingEnd ℂ) ((x : ℝ) : ℂ) * Inner ψ₀ ψ₀ := qInner_smul_left _ _ _
        _ = ((x : ℝ) : ℂ) := by rw [starRingEnd_ofReal, h00, mul_one]
    have hVV : Inner (V *ᵥ ψ₀) (V *ᵥ ψ₀) = 1 :=
      (inner_applyGate hV.1 ψ₀ ψ₀).trans h00
    have hφφ : Inner φ φ = ((1 - x ^ 2 : ℝ) : ℂ) := by
      rw [hφdef, qInner_sub_left, qInner_sub_right, qInner_sub_right,
        qInner_smul_right, qInner_smul_left, qInner_smul_left, qInner_smul_right,
        hVV, h0V, hV0, h00, starRingEnd_ofReal]
      push_cast
      ring
    have horth : Inner ψ₀ ψ₁ = 0 := by
      rw [hψ₁def, qInner_smul_right, hφdef, qInner_sub_right, h0V, qInner_smul_right, h00]
      rw [mul_one, sub_self, mul_zero]
    have hstar_inv : (starRingEnd ℂ) (((y : ℝ) : ℂ))⁻¹ = (((y : ℝ) : ℂ))⁻¹ := by
      rw [← Complex.ofReal_inv, starRingEnd_ofReal, Complex.ofReal_inv]
    have hψ₁norm : Normalized ψ₁ := by
      rw [normalized_iff_inner_self, hψ₁def, qInner_smul_left, qInner_smul_right, hφφ,
        hstar_inv, ← hy2c]
      rw [← mul_assoc, ← mul_inv, inv_mul_cancel₀]
      exact mul_ne_zero hyne hyne
    have hVψ₀ : V *ᵥ ψ₀ = ((x : ℝ) : ℂ) • ψ₀ + φ := by
      rw [hφdef]
      abel
    have hφψ₁ : φ = ((y : ℝ) : ℂ) • ψ₁ := by
      rw [hψ₁def, smul_smul, mul_inv_cancel₀ hyne, one_smul]
    have hRψ₀ : FiberReflection j₀ *ᵥ ψ₀ = ψ₀ := by
      rw [fiberReflection_mulVec, hPfix, two_smul]
      abel
    have hRφ : FiberReflection j₀ *ᵥ φ = -φ := by
      rw [fiberReflection_mulVec, hPiPhi, smul_zero, zero_sub]
    have hVVψ₀ : V *ᵥ (V *ᵥ ψ₀) = ψ₀ := by
      rw [Matrix.mulVec_mulVec, hV2, Matrix.one_mulVec]
    have hVφ : V *ᵥ φ = ((1 - x ^ 2 : ℝ) : ℂ) • ψ₀ - ((x : ℝ) : ℂ) • φ := by
      rw [hφdef, Matrix.mulVec_sub, Matrix.mulVec_smul, hVVψ₀, hVψ₀, smul_add, smul_smul]
      rw [show ((x : ℝ) : ℂ) * ((x : ℝ) : ℂ) = ((x ^ 2 : ℝ) : ℂ) by push_cast; ring]
      rw [show ((1 - x ^ 2 : ℝ) : ℂ) = 1 - ((x ^ 2 : ℝ) : ℂ) by push_cast; ring,
        sub_smul, one_smul]
      abel
    have hRVφ : FiberReflection j₀ *ᵥ (V *ᵥ φ)
        = ((1 - x ^ 2 : ℝ) : ℂ) • ψ₀ + ((x : ℝ) : ℂ) • φ := by
      rw [hVφ, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hRψ₀,
        hRφ, smul_neg, sub_neg_eq_add]
    refine ⟨ψ₀, ψ₁, y, hψ₀, hψ₁norm, horth, ?_, ?_, hy, by nlinarith⟩
    · calc (FiberReflection j₀ * V) *ᵥ ψ₀
          = FiberReflection j₀ *ᵥ (V *ᵥ ψ₀) := by rw [Matrix.mulVec_mulVec]
        _ = FiberReflection j₀ *ᵥ (((x : ℝ) : ℂ) • ψ₀ + φ) := by rw [hVψ₀]
        _ = FiberReflection j₀ *ᵥ (((x : ℝ) : ℂ) • ψ₀) + FiberReflection j₀ *ᵥ φ := by
              rw [Matrix.mulVec_add]
        _ = ((x : ℝ) : ℂ) • (FiberReflection j₀ *ᵥ ψ₀) + FiberReflection j₀ *ᵥ φ := by
              rw [Matrix.mulVec_smul]
        _ = ((x : ℝ) : ℂ) • ψ₀ + (-φ) := by rw [hRψ₀, hRφ]
        _ = ((x : ℝ) : ℂ) • ψ₀ - ((y : ℝ) : ℂ) • ψ₁ := by
              rw [hφψ₁, sub_eq_add_neg]
    · have hs0 : (((y : ℝ) : ℂ))⁻¹ * ((1 - x ^ 2 : ℝ) : ℂ) = ((y : ℝ) : ℂ) := by
        rw [← hy2c, ← mul_assoc, inv_mul_cancel₀ hyne, one_mul]
      have hs1 : (((y : ℝ) : ℂ))⁻¹ * ((x : ℝ) : ℂ)
          = ((x : ℝ) : ℂ) * (((y : ℝ) : ℂ))⁻¹ := mul_comm _ _
      calc (FiberReflection j₀ * V) *ᵥ ψ₁
          = FiberReflection j₀ *ᵥ (V *ᵥ ψ₁) := by rw [Matrix.mulVec_mulVec]
        _ = FiberReflection j₀ *ᵥ (V *ᵥ ((((y : ℝ) : ℂ))⁻¹ • φ)) := by rw [hψ₁def]
        _ = FiberReflection j₀ *ᵥ ((((y : ℝ) : ℂ))⁻¹ • (V *ᵥ φ)) := by
              rw [Matrix.mulVec_smul]
        _ = ((((y : ℝ) : ℂ))⁻¹) • (FiberReflection j₀ *ᵥ (V *ᵥ φ)) := by
              rw [Matrix.mulVec_smul]
        _ = ((((y : ℝ) : ℂ))⁻¹) •
              (((1 - x ^ 2 : ℝ) : ℂ) • ψ₀ + ((x : ℝ) : ℂ) • φ) := by rw [hRVφ]
        _ = ((((y : ℝ) : ℂ))⁻¹ * ((1 - x ^ 2 : ℝ) : ℂ)) • ψ₀
              + ((((y : ℝ) : ℂ))⁻¹ * ((x : ℝ) : ℂ)) • φ := by
              rw [smul_add, smul_smul, smul_smul]
        _ = ((y : ℝ) : ℂ) • ψ₀ + ((x : ℝ) : ℂ) • ψ₁ := by
              rw [hs0, hs1, ← smul_smul, ← hψ₁def]

end

end Qatlib.Papers.Qubitization19.MainResults
