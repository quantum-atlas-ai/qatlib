/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.QueryDefs

@[expose] public section

/-!
# The seven-gate phase-flip word

Figure 1.2 of [Itakura2005], §1.2.4 applies, from left to right, `X` to register `1`, `X` to
register `2`, `H` to register `2`, a `C-NOT` with register `1` as control, `H` again on register
`2`, and `X` on both registers. The resulting operator is stated to be `I - 2|00⟩⟨00|`.

This module verifies the word on the explicit two-qubit matrices of
`Qatlib.Papers.CommuteTest05.QueryDefs`. The product is written with the first-applied gate on the
right, as in the source circuit. Two intermediate identities are proved separately: conjugating
`C-NOT` by `H` on the target register gives the controlled-`Z` matrix, and conjugating
controlled-`Z` by `X ⊗ X` moves the negated basis state from `(1,1)` to `(0,0)`.

## Main statements

* `hSecond_mul_cnotGate_mul_hSecond`: `H₂ · C-NOT · H₂ = CZ`, the printed `H·CZ·H = C-NOT`
  identity of the same section.
* `xBoth_mul_czGate_mul_xBoth`: conjugating `CZ` by `X ⊗ X` gives the phase flip at `(0,0)`.
* `phaseFlip_seven_gate_word`: the five-factor word of Figure 1.2 equals `phaseFlip`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.CommuteTest05.GateWord

open Qatlib.Papers.CommuteTest05.QueryDefs

/-- The product of two copies of the complex coercion of `Real.sqrt 2` equals `2`. -/
theorem sqrtTwo_sq_complex : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = 2 := by
  rw [← Complex.ofReal_mul]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h]
  norm_num

/-- The inverse of the complex square root of two squares to `1 / 2`. -/
theorem inv_sqrtTwo_mul_self :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, sqrtTwo_sq_complex]

/-- Hadamard conjugation of the controlled-`NOT` on the target register gives the controlled-`Z`
matrix, the identity `H · CZ · H = C-NOT` of [Itakura2005], §1.2.4 read in the opposite
direction. -/
theorem hSecond_mul_cnotGate_mul_hSecond : hSecond * cnotGate * hSecond = czGate := by
  ext i j
  simp only [Matrix.mul_apply]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [hSecond, hGate, cnotGate, czGate, Fintype.sum_prod_type, Fin.sum_univ_two,
      inv_sqrtTwo_mul_self] <;>
    norm_num

/-- Conjugating the controlled-`Z` matrix by `X ⊗ X` moves the negative diagonal entry from `(1,1)`
to `(0,0)`, producing the phase flip used in Figure 1.2 of [Itakura2005]. -/
theorem xBoth_mul_czGate_mul_xBoth : xBoth * czGate * xBoth = phaseFlip := by
  ext i j
  simp only [Matrix.mul_apply]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [xBoth, xGate, czGate, phaseFlip, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The five-factor product of Figure 1.2 of [Itakura2005], §1.2.4 equals the phase-flip operator
`I - 2|00⟩⟨00|`. The printed seven gates collapse to five factors because the initial and final
pairs of `X` gates combine to `X ⊗ X`. -/
theorem phaseFlip_seven_gate_word :
    xBoth * hSecond * cnotGate * hSecond * xBoth = phaseFlip := by
  have hcz : hSecond * cnotGate * hSecond = czGate := hSecond_mul_cnotGate_mul_hSecond
  have hx : xBoth * czGate * xBoth = phaseFlip := xBoth_mul_czGate_mul_xBoth
  calc xBoth * hSecond * cnotGate * hSecond * xBoth
      = xBoth * (hSecond * cnotGate * hSecond) * xBoth := by simp only [mul_assoc]
    _ = xBoth * czGate * xBoth := by rw [hcz]
    _ = phaseFlip := hx

end Qatlib.Papers.CommuteTest05.GateWord
