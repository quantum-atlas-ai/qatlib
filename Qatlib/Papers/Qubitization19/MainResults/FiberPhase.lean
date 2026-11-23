/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Qubitization19.MainResults.PhasedIterate
public import Qatlib.Papers.Qubitization19.MainResults.SourceDefinitions
public import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

@[expose] public section

/-!
# The phase gate and the phased iterate on the signal fiber

Lemma 11 of arXiv:1610.06546v3 uses a phased reflection of the signal
ancilla. Its two eigenvalues determine the restriction of the conjugated
iterate to a rotation plane with one vector in the signal fiber.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Papers.Qubitization19.MainResults

namespace Qatlib.Papers.Qubitization19.MainResults

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- The phased reflection `Z_φ` of Eq. (20). -/
def fiberPartialReflection (j₀ : J) (φ : ℂ) : Matrix (J × I) (J × I) ℂ :=
  (1 + Complex.exp (-Complex.I * φ)) • FiberProjector j₀ - 1

/-- The signal component receives the phase, and the orthogonal component receives minus one. -/
theorem fiberPartialReflection_actions (j₀ : J) (φ : ℂ) (ψ : QState I) (χ : QState (J × I))
    (hχ : FiberProjector j₀ *ᵥ χ = 0) :
    fiberPartialReflection j₀ φ *ᵥ TensorState (Ket j₀) ψ =
        Complex.exp (-Complex.I * φ) • TensorState (Ket j₀) ψ ∧
      fiberPartialReflection j₀ φ *ᵥ χ = -χ := by
  constructor
  · rw [fiberPartialReflection, Matrix.sub_mulVec, Matrix.smul_mulVec,
      fiberProjector_mulVec_tensorState_ket, Matrix.one_mulVec, add_smul, one_smul]
    abel
  · rw [fiberPartialReflection, Matrix.sub_mulVec, Matrix.smul_mulVec, hχ, smul_zero, Matrix.one_mulVec, zero_sub]

/-- A phased reflection is diagonal with unit-modulus entries at every real phase. -/
theorem fiberPartialReflection_unitary (j₀ : J) (φ : ℝ) :
    fiberPartialReflection (I := I) j₀ φ ∈ Matrix.unitaryGroup (J × I) ℂ := by
  let d : J × I → ℂ := fun v => if v.1 = j₀ then Complex.exp (-Complex.I * (φ : ℂ)) else -1
  have he : fiberPartialReflection (I := I) j₀ φ = Matrix.diagonal d := by
    ext p q
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, k⟩
    by_cases h : (a, i) = (b, k)
    · cases h
      by_cases ha : a = j₀ <;>
        simp [fiberPartialReflection, fiberProjector_apply, d, ha]
    · simp [fiberPartialReflection, fiberProjector_apply, d, h]
  rw [he]
  apply diagonal_mem_unitaryGroup
  intro v
  by_cases h : v.1 = j₀ <;> simp [d, h, Complex.norm_exp, Complex.mul_re]

/-- The two-dimensional restriction of the phased reflection in a signal/complement frame. -/
theorem fiberPartialReflection_frame (j₀ : J) (φ : ℂ) (ψ : QState I) (χ : QState (J × I))
    (hχ : FiberProjector j₀ *ᵥ χ = 0) (E : Matrix (J × I) (Fin 2) ℂ)
    (h₀ : (fun i => E i 0) = TensorState (Ket j₀) ψ)
    (h₁ : (fun i => E i 1) = χ) :
    fiberPartialReflection j₀ φ * E = E * Matrix.diagonal ![Complex.exp (-Complex.I * φ), (-1 : ℂ)] := by
  obtain ⟨ha, hb⟩ := fiberPartialReflection_actions j₀ φ ψ χ hχ
  ext k i
  fin_cases i
  · rw [Matrix.mul_diagonal]
    have h := congrFun ha k
    rw [← h₀] at h
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
  · rw [Matrix.mul_diagonal]
    have h := congrFun hb k
    rw [← h₁] at h
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- The two shifted reflections around the workspace walk in Eq. (19). -/
def fiberPhasedIterate (j₀ : J) (W : Matrix (J × I) (J × I) ℂ) (φ : ℝ) :
    Matrix (J × I) (J × I) ℂ :=
  fiberPartialReflection j₀ ((φ : ℂ) + Real.pi / 2) * W *
    fiberPartialReflection j₀ (-((φ : ℂ) + Real.pi / 2))

/-- If the walk on the signal/complement frame is Eq. (5), the workspace composition
of Eq. (19) restricts to the phased matrix of Lemma 11. -/
theorem fiberPhasedIterate_frame (j₀ : J) (φ lam : ℝ) (hlo : -1 ≤ lam) (hhi : lam ≤ 1)
    (W : Matrix (J × I) (J × I) ℂ) (E : Matrix (J × I) (Fin 2) ℂ)
    (ψ : QState I) (χ : QState (J × I)) (hχ : FiberProjector j₀ *ᵥ χ = 0)
    (h₀ : (fun i => E i 0) = TensorState (Ket j₀) ψ)
    (h₁ : (fun i => E i 1) = χ)
    (hW : W * E = E * eq5Rotation lam) :
    fiberPhasedIterate j₀ W φ * E =
      E * !![(lam : ℂ), -Complex.I * Complex.exp (-Complex.I * (φ : ℂ)) *
          ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ);
        -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) *
          ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ), (lam : ℂ)] := by
  have hpos := fiberPartialReflection_frame j₀ ((φ : ℂ) + Real.pi / 2) ψ χ hχ E h₀ h₁
  have hneg := fiberPartialReflection_frame j₀ (-((φ : ℂ) + Real.pi / 2)) ψ χ hχ E h₀ h₁
  dsimp only [fiberPhasedIterate]
  rw [Matrix.mul_assoc (_ * W), hneg, ← Matrix.mul_assoc, Matrix.mul_assoc _ W,
    hW, ← Matrix.mul_assoc, hpos]
  simp only [Matrix.mul_assoc]
  congr 1
  simpa only [eq5Rotation, Matrix.mul_assoc] using (lemma11_phased_iterate lam φ hlo hhi).symm

end Qatlib.Papers.Qubitization19.MainResults
