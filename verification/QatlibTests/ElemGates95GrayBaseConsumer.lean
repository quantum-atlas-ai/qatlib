module

public import Qatlib.Papers.ElemGates95.MultiControl.GrayBase
public import Mathlib.Tactic

@[expose] public section

/-!
# Consumer regression for the three-wire Gray base case

This test instantiates the three-step Gray word at an explicit non-scalar doubly controlled
unitary. The root is the diagonal matrix with entries `1` and `i`, whose square is `PauliZ`.
On the all-true control fibre the word must multiply the target by `-1`, while on the
`|101>` control fibre it must act as the identity. The test also checks the exact three-gate
count. Nothing here is vacuous: the two fibres have different actions.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ElemGates95.MultiControl

namespace QatlibTests.ElemGates95GrayBase

/-- The diagonal unitary with entries `1` at `false` and `i` at `true`; its square is `PauliZ`. -/
noncomputable def diagRoot : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.I else 1

/-- The diagonal root squares to `PauliZ`. -/
theorem diagRoot_sq : diagRoot * diagRoot = PauliZ := by
  simp [diagRoot, PauliZ, Matrix.diagonal_mul_diagonal, Complex.I_mul_I]

/-- The diagonal root is unitary. -/
theorem diagRoot_unitary : diagRoot ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  simp [diagRoot, Matrix.diagonal, Matrix.star_apply, Matrix.mul_apply]
  cases i <;> cases j <;> simp [Complex.I_mul_I, Complex.conj_I]

/-- The word has exactly three gates. -/
theorem word_length : (grayBase3Word diagRoot).length = 3 :=
  grayBase3Word_length diagRoot

/-- On the all-true control fibre the word sends the target basis state `|1>` to `-|1>`. -/
theorem allTrue_action :
    compileSteps (2 : Fin 3) (grayBase3Word diagRoot) *ᵥ
        Ket (![true, true, true] : Reg 3) =
      (-1 : ℂ) • Ket (![true, true, true] : Reg 3) := by
  rw [grayBase3_word_exact diagRoot PauliZ diagRoot_unitary diagRoot_sq]
  rw [fullCtrlGate_mulVec_ket]
  have hall : ∀ k : Fin 3, k ≠ 2 → (![true, true, true] : Reg 3) k = true := by
    intro k _
    fin_cases k <;> rfl
  rw [ite_eq_left hall]
  have hupd : Function.update (![true, true, true] : Reg 3) 2 true = ![true, true, true] := by
    funext k
    fin_cases k <;> rfl
  simp [PauliZ, Matrix.diagonal, hupd]

/-- On the `|101>` control fibre the word acts as the identity. -/
theorem oneZero_action :
    compileSteps (2 : Fin 3) (grayBase3Word diagRoot) *ᵥ
        Ket (![true, false, true] : Reg 3) =
      Ket (![true, false, true] : Reg 3) := by
  rw [grayBase3_word_exact diagRoot PauliZ diagRoot_unitary diagRoot_sq]
  rw [fullCtrlGate_mulVec_ket]
  have hnot : ¬ ∀ k : Fin 3, k ≠ 2 → (![true, false, true] : Reg 3) k = true := by
    intro h
    have := h 1 (by decide)
    simp at this
  rw [ite_eq_right hnot]

/-- The two control fibres genuinely differ, excluding the identity reading of the word. -/
theorem not_identity :
    compileSteps (2 : Fin 3) (grayBase3Word diagRoot) *ᵥ
        Ket (![true, true, true] : Reg 3) ≠
      Ket (![true, true, true] : Reg 3) := by
  rw [allTrue_action]
  intro h
  have h' : (-1 : ℂ) = 1 := by
    have := congrFun h (![true, true, true] : Reg 3)
    simpa [Ket] using this
  norm_num at h'

end QatlibTests.ElemGates95GrayBase
