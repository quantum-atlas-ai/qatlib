/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Qubitization19.MainResults.SourceQubitization

@[expose] public section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Papers.Qubitization19.MainResults

set_option autoImplicit false

namespace Qatlib.Papers.Qubitization19.MainResults
noncomputable section

/-- The old rotation predicate is vacuous when the encoded signal is the identity. -/
theorem identity_rotation_vacuous (G : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    Eq5RotationAction G (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  intro ψ hψ x hx1 hx
  have hn : ψ 0 ≠ 0 := by
    intro hzero
    simp [Normalized, hzero] at hψ
  have hx0 := congrFun hx 0
  simp only [Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at hx0
  have hxc : (1 : ℂ) = (x : ℂ) :=
    mul_right_cancel₀ hn (by simpa using hx0)
  have hxr : x = 1 := Complex.ofReal_injective hxc.symm
  norm_num [hxr] at hx1

/-- A negative ancilla twist defeats Eq. 17 despite satisfying the vacuous rotation predicate. -/
theorem lemma8_converse_counterexample :
    IsBlockEncoding (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (0 : Fin 1)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 ∧
    (-1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
    (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1 ∧
    Eq5RotationAction
      (FiberReflection (0 : Fin 1) *
        (TensorGate (-1 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ) * 1))
      (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
    ¬ QubitizationConditionsEq17
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
      (-1 : Matrix (Fin 1) (Fin 1) ℂ) (0 : Fin 1)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  have ht : TensorGate (-1 : Matrix (Fin 1) (Fin 1) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      (-1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    fin_cases a
    fin_cases b
    fin_cases c
    fin_cases d
    norm_num [tensorGate_apply]
  refine ⟨?_, ?_, Matrix.conjTranspose_one, identity_rotation_vacuous _, ?_⟩
  · refine ⟨Submonoid.one_mem _, one_pos, ?_⟩
    ext i j
    simp [blockCorner_apply, Matrix.one_apply]
  · rw [Matrix.mem_unitaryGroup_iff]
    simp
  · intro hc
    have hc0 := congrFun (congrFun hc.1 (0 : Fin 1)) (0 : Fin 1)
    norm_num [ht, blockCorner_apply] at hc0

end
end Qatlib.Papers.Qubitization19.MainResults
