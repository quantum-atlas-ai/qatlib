/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Thermalize11.MainResults.Microcanonical
public import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

@[expose] public section


/-! # The old microcanonical interface does not connect coupling to projectors. -/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Papers.Thermalize11.MainResults.SourceModel
open Qatlib.Papers.Thermalize11.MainResults.Theorem1

namespace Qatlib.Papers.Thermalize11.MainResults

/-- Distinct supports violate the zero-coupling bound when the coupling field is free. -/
theorem freeCoupling_refutes
    (G F : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) (hne : G ≠ F) :
    let M : MicrocanonicalPair 2 1 :=
      ⟨G, F, 1, 1, 0, 0, 4, 1⟩
    ¬ traceDistanceGen M.ω M.ωZero ≤ M.couplingNorm / M.eps
      + ((M.ΔΩ : ℝ) + (M.Ωε : ℝ)) / (2 * (M.Ωmax : ℝ)) := by
  dsimp [MicrocanonicalPair.ω, MicrocanonicalPair.ωZero, dephasedState,
    MicrocanonicalPair.ΔΩ, MicrocanonicalPair.Ωmax, MicrocanonicalPair.Ωmin]
  simp only [Nat.cast_one, inv_one, one_smul, Nat.max_self, Nat.min_self,
    Nat.sub_self, Nat.cast_zero, zero_div, zero_add, mul_one]
  have hpos : 0 < Matrix.traceNorm (G - F) :=
    lt_of_le_of_ne (Matrix.traceNorm_nonneg _) (fun h =>
      hne (sub_eq_zero.mp ((Matrix.traceNorm_zero_iff _).mp h.symm)))
  unfold traceDistanceGen
  linarith

/-- Two orthogonal rank-one projectors give distinct admissible support data. -/
theorem orthogonal_supports :
    ∃ G F : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ,
      (G.IsHermitian ∧ G * G = G) ∧ (F.IsHermitian ∧ F * F = F) ∧
      Matrix.trace G = 1 ∧ Matrix.trace F = 1 ∧ G ≠ F := by
  let x : Fin 2 × Fin 1 := (0, 0)
  let y : Fin 2 × Fin 1 := (1, 0)
  let G := outerProduct (Qatlib.Foundations.PureStateMath.Ket x)
  let F := outerProduct (Qatlib.Foundations.PureStateMath.Ket y)
  have hG := isOrthogonalProjector_outerProduct (normalized_ket x)
  have hF := isOrthogonalProjector_outerProduct (normalized_ket y)
  refine ⟨G, F, ⟨hG.isSelfAdjoint, hG.1⟩, ⟨hF.isSelfAdjoint, hF.1⟩, ?_, ?_, ?_⟩
  · simp [G, Matrix.trace, outerProduct, Qatlib.Foundations.PureStateMath.Ket, x]
  · simp [F, Matrix.trace, outerProduct, Qatlib.Foundations.PureStateMath.Ket, y]
  · intro h
    have hxy := congrArg (fun A : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ => A x x) h
    norm_num [G, F, outerProduct, Qatlib.Foundations.PureStateMath.Ket, x, y] at hxy

end Qatlib.Papers.Thermalize11.MainResults
