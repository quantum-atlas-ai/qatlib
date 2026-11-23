module

public import Qatlib.Papers.SpinFreeSim13.GroupFourier.CyclicReadout

/-!
# Cyclic character readout on concrete non-degenerate instances

Consumer regression for the Dev increment in
`Qatlib.Papers.SpinFreeSim13.GroupFourier.CyclicReadout`. The examples use the
regular representations of `C₂`, `C₃` and `C₅`. The order-three case uses the
character labels of the cyclic subgroup in the cyclopropenyl example of [Whitfield2013].
The order-five contraction test uses a unit vector fixed by the chosen projector.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators InnerProductSpace ComplexConjugate
open Qatlib.Papers.SpinFreeSim13.GroupFourier

namespace QatlibTests.SpinFreeSim13CyclicReadoutRegression

/-- The order-two regular readout puts unit Born weight on the trivial character
label of its own character eigenstate. -/
example : weight (N := 2) (charVec (0 : ZMod 2)) (0 : ZMod 2) = 1 := by
  simpa using weight_charVec (N := 2) (r := 0) (s := 0)

/-- The same eigenstate has zero weight on the nontrivial character label. -/
example : weight (N := 2) (charVec (0 : ZMod 2)) (1 : ZMod 2) = 0 := by
  have h : (1 : ZMod 2) ≠ 0 := by decide
  simpa [h] using weight_charVec (N := 2) (r := 1) (s := 0)

/-- The two cyclic Born weights sum to one for the trivial character vector. -/
example : (∑ r : ZMod 2, weight (N := 2) (charVec (0 : ZMod 2)) r) = 1 :=
  total_weight_unit (charVec (0 : ZMod 2)) (norm_charVec 0)

/-- The `C₃` character readout has total Born weight one on the label-one eigenstate. -/
example : (∑ r : ZMod 3, weight (N := 3) (charVec (1 : ZMod 3)) r) = 1 :=
  total_weight_unit (charVec (1 : ZMod 3)) (norm_charVec 1)

/-- The label-zero projector annihilates the unit vector fixed by the label-one projector. -/
example :
    wignerOp (N := 3) (0 : ZMod 3) (wignerOp (N := 3) (1 : ZMod 3)
      (charVec (1 : ZMod 3))) = 0 := by
  have h : (0 : ZMod 3) ≠ 1 := by decide
  exact wignerOp_orthogonal (N := 3) h (charVec (1 : ZMod 3))

/-- The `C₃` Wigner projector is Hermitian for the Euclidean inner product. -/
example (φ χ : ZMod 3 → ℂ) :
    ⟪toE (N := 3) (wignerOp (1 : ZMod 3) φ), toE χ⟫_ℂ =
      ⟪toE φ, toE (wignerOp (1 : ZMod 3) χ)⟫_ℂ :=
  wignerOp_hermitian (1 : ZMod 3) φ χ

/-- A nonzero order-two branch normalizes to a unit Euclidean vector. -/
example :
    ‖((‖toE (N := 2) (wignerOp (0 : ZMod 2) (charVec (0 : ZMod 2)))‖ : ℂ)⁻¹) •
        toE (N := 2) (wignerOp (0 : ZMod 2) (charVec (0 : ZMod 2)))‖ = 1 := by
  have hid : wignerOp (N := 2) (0 : ZMod 2) (charVec (0 : ZMod 2)) =
      charVec (0 : ZMod 2) := by
    rw [wignerOp_eq_smul_charVec, amplitude_charVec]
    simp
  apply normalizedBranch_norm
  rw [hid]
  intro h
  have hnorm := norm_charVec (N := 2) (0 : ZMod 2)
  rw [h] at hnorm
  norm_num at hnorm

/-- The five-label character vector is a nonzero Euclidean vector. -/
example : 0 < ‖toE (N := 5) (charVec (1 : ZMod 5))‖ := by
  rw [norm_charVec]
  norm_num

/-- The five-label Wigner branch is a genuine contraction in the Euclidean norm. -/
example (r : ZMod 5) :
    ‖toE (N := 5) (wignerOp r (charVec (3 : ZMod 5)))‖ ≤
      ‖toE (N := 5) (charVec (3 : ZMod 5))‖ :=
  norm_wignerOp_le r (charVec (3 : ZMod 5))

/-- The uniform bound at order five must be at least one, since the chosen branch
fixes a unit character vector. -/
example :
    ∃ C : ℝ, 1 ≤ C ∧
      ‖toE (N := 5) (wignerOp (1 : ZMod 5) (charVec (1 : ZMod 5)))‖ ≤
        C * ‖toE (N := 5) (charVec (1 : ZMod 5))‖ := by
  obtain ⟨C, _, h⟩ := uniform_contraction
  have hbound := h 5 (1 : ZMod 5) (charVec (1 : ZMod 5))
  have hfixed : wignerOp (N := 5) (1 : ZMod 5) (charVec (1 : ZMod 5)) =
      charVec (1 : ZMod 5) := by
    rw [wignerOp_eq_smul_charVec, amplitude_charVec]
    simp
  refine ⟨C, ?_, hbound⟩
  simpa only [hfixed, norm_charVec, mul_one] using hbound

/-- The Born weight is exactly the squared modulus of the Fourier amplitude at `N = 2`. -/
example : weight (N := 2) (charVec (0 : ZMod 2)) (0 : ZMod 2) =
    ‖amplitude (charVec (0 : ZMod 2)) (0 : ZMod 2)‖ ^ 2 :=
  weight_eq_amplitude (charVec (0 : ZMod 2)) (0 : ZMod 2)

end QatlibTests.SpinFreeSim13CyclicReadoutRegression
