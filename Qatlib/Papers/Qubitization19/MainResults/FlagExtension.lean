/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization

@[expose] public section


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Matrix

set_option autoImplicit false

namespace Qatlib.Papers.Qubitization19.MainResults

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- Adding an unused Boolean flag preserves the encoded signal and its invariant planes. -/
theorem theorem2_qubitization_construction
    (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hV : IsBlockEncoding V j₀ A 1) (hA : Aᴴ = A) :
    ∃ (j₀' : Bool × J) (V' : Matrix ((Bool × J) × I) ((Bool × J) × I) ℂ),
      IsBlockEncoding V' j₀' A 1 ∧
      (Fintype.card (Bool × J) = 2 * Fintype.card J) ∧
      ∀ (ψ : QState I), Normalized ψ → ∀ (x : ℝ), |x| < 1 →
        A *ᵥ ψ = ((x : ℝ) : ℂ) • ψ →
        ∃ (ψ₀ ψ₁ : QState ((Bool × J) × I)) (y : ℝ),
          Normalized ψ₀ ∧ Normalized ψ₁ ∧ Inner ψ₀ ψ₁ = 0 ∧
          QubitizationWalk V' j₀' *ᵥ ψ₀
            = (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₀ - (((2 * x * y : ℝ)) : ℂ) • ψ₁ ∧
          QubitizationWalk V' j₀' *ᵥ ψ₁
            = (((2 * x * y : ℝ)) : ℂ) • ψ₀ + (((2 * x ^ 2 - 1 : ℝ)) : ℂ) • ψ₁ ∧
          0 < y ∧ x ^ 2 + y ^ 2 = 1 := by
  let e : Bool × (J × I) ≃ (Bool × J) × I := (Equiv.prodAssoc Bool J I).symm
  let V' : Matrix ((Bool × J) × I) ((Bool × J) × I) ℂ :=
    Matrix.reindex e e (TensorGate (1 : Matrix Bool Bool ℂ) V)
  have hV' : IsBlockEncoding V' (false, j₀) A 1 := by
    refine ⟨unitaryGroup_reindex e (tensorGate_unitary (Submonoid.one_mem _) hV.1),
      one_pos, ?_⟩
    have hc : BlockCorner V' (false, j₀) = BlockCorner V j₀ := by
      ext i j
      simp [blockCorner_apply, V', Matrix.reindex_apply, e, tensorGate_apply]
    exact hc.trans hV.2.2
  refine ⟨(false, j₀), V', hV', ?_, ?_⟩
  · simp [Fintype.card_prod]
  · intro ψ hψ x hx1 hx
    exact qubitization_invariant_subspace V' (false, j₀) A hV' hA ψ hψ x hx hx1

end Qatlib.Papers.Qubitization19.MainResults
