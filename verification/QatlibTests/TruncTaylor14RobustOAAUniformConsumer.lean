module

import Qatlib.Papers.TruncTaylor14.ResetDiscard.RobustOAAUniform

/-!
# Consumer checks for the uniform robust-OAA bounds (source Eq. (15))

This ordinary module instantiates the two uniform Eq. (15) theorems from
`Qatlib.Papers.TruncTaylor14.ResetDiscard.RobustOAAUniform` on concrete
non-degenerate registers with one ancilla qubit and one data qubit, each
indexed by `Fin 2`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.TruncTaylor14RobustOAAUniformConsumer

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Papers.TruncTaylor14.ResetDiscard
open scoped Matrix.Norms.L2Operator

/-- The identity workspace on `Fin 2 × Fin 2` is an exact block encoding of the
identity data block on `Fin 2` at scale one, with ancilla label `0`. -/
theorem one_blockEncoding :
    IsBlockEncoding (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (0 : Fin 2)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  refine ⟨(Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ).one_mem, one_pos, ?_⟩
  ext i i'
  simp [BlockCorner, Matrix.one_apply, Fin.ext_iff, Prod.ext_iff]

/-- The uniform robust-OAA vector bound (source Eq. (15)) applies to the
concrete instance `J = I = Fin 2`, identity workspace,
unit data block, scale `s = 1`, `δ₁ = 0`, `δ₂ = 1`, and the computational-basis
input `Ket 0`; the resulting bound is `‖·‖ ≤ C · (0 + 1)`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖toEuclidean_fromVec (FiberProjector (0 : Fin 2) *ᵥ
        (ObliviousAmplitudeAmplification (FiberProjector (0 : Fin 2))
          (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *ᵥ
          TensorState (Ket (0 : Fin 2)) (Ket (0 : Fin 2))) -
        TensorState (Ket (0 : Fin 2))
          ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ Ket (0 : Fin 2)))‖ ≤ C * (0 + 1) := by
  obtain ⟨C, hC, h⟩ := source_equation15_uniform
  refine ⟨C, hC, ?_⟩
  exact h (Fin 2) (Fin 2)
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (0 : Fin 2)
    (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (1 : ℝ) (0 : ℝ) (1 : ℝ)
    one_blockEncoding (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Ket (0 : Fin 2)) (normalized_ket (0 : Fin 2))

/-- The uniform almost-unitarity defect bound (source Eq. (15), matrix
conclusion) applies to the unit data block on `Fin 2` at `δ₁ = 0`: the defect
`‖1 · 1ᴴ - 1‖ = 0` is at most `C · 0`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose - 1‖ ≤
      C * (0 : ℝ) := by
  obtain ⟨C, hC, h⟩ := encoded_operator_defect_uniform
  exact ⟨C, hC, h (Fin 2) (1) (1) (0 : ℝ) (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
    (by simp) (by norm_num)⟩

/-- At `δ₁ = 1`, the zero data operator has a nonzero defect relative to the
unitary identity. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖(0 : Matrix (Fin 2) (Fin 2) ℂ) * (0 : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose - 1‖ ≤
      C * (1 : ℝ) := by
  obtain ⟨C, hC, h⟩ := encoded_operator_defect_uniform
  exact ⟨C, hC, h (Fin 2) 0 1 (1 : ℝ) (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
    (by simpa only [zero_sub, norm_neg] using (l2_norm_one_le (I := Fin 2)))
    (by norm_num)⟩

end QatlibTests.TruncTaylor14RobustOAAUniformConsumer
