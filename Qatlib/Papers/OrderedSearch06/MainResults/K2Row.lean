/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch06.SdpForm.Basic
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram

/-!
# An exact infeasibility certificate at size seven

Computes an explicit negative unit-circle evaluation for the coefficient vector `certCoeff`. The
stage-one generalized traces forced by `SolvesPaperSDP 7 2` coincide with this vector, giving an
exact infeasibility certificate for the two-query size-seven case in [ChildsLandahlParrilo2007].

## Main statements

* `certCoeff_eval_neg`: certifies a negative Laurent evaluation at `(5 + 12i) / 13`.
* `not_paperSDP_seven_two`: rules out the paper semidefinite program for size seven and two
  queries.

## References

* [Childs et al., 2007][ChildsLandahlParrilo2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.MainResults

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Papers.OrderedSearch06.SdpForm
open Qatlib.Papers.OrderedSearch06.LaurentDefs

/-- Expresses `(5 + 12i) / 13` as the complex number with real part `5 / 13` and imaginary part
`12 / 13`. -/
private lemma zc_eq : (((5:ℂ)+12*Complex.I)/13) = Complex.mk (5/13) (12/13) := by
  apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- The real part of the square of `(5 + 12i) / 13` is `−119 / 169`. -/
private lemma zm2 : (Complex.mk (5/13) (12/13) ^ 2).re = -119/169 := by
  rw [pow_two, Complex.mk_mul_mk]; norm_num

/-- The real part of the cube of `(5 + 12i) / 13` is `−2035 / 2197`. -/
private lemma zm3 : (Complex.mk (5/13) (12/13) ^ 3).re = -2035/2197 := by
  rw [pow_succ, pow_two, Complex.mk_mul_mk, Complex.mk_mul_mk]; norm_num

/-- The real part of the fourth power of `(5 + 12i) / 13` is `−239 / 28561`. -/
private lemma zm4 : (Complex.mk (5/13) (12/13) ^ 4).re = -239/28561 := by
  rw [pow_succ, pow_succ, pow_two, Complex.mk_mul_mk, Complex.mk_mul_mk,
    Complex.mk_mul_mk]; norm_num

/-- The real part of the fifth power of `(5 + 12i) / 13` is `341525 / 371293`. -/
private lemma zm5 : (Complex.mk (5/13) (12/13) ^ 5).re = 341525/371293 := by
  rw [pow_succ, pow_succ, pow_succ, pow_two, Complex.mk_mul_mk, Complex.mk_mul_mk,
    Complex.mk_mul_mk, Complex.mk_mul_mk]; norm_num

/-- The real part of the sixth power of `(5 + 12i) / 13` is `3455641 / 4826809`. -/
private lemma zm6 : (Complex.mk (5/13) (12/13) ^ 6).re = 3455641/4826809 := by
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_two, Complex.mk_mul_mk,
    Complex.mk_mul_mk, Complex.mk_mul_mk, Complex.mk_mul_mk, Complex.mk_mul_mk]; norm_num

/-- The real part of the integer square of `(5 + 12i) / 13` is `−119 / 169`. -/
private lemma zr2 : ((((5:ℂ)+12*Complex.I)/13) ^ (2:ℤ)).re = -119/169 := by
  rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm2

/-- The real part of the integer cube of `(5 + 12i) / 13` is `−2035 / 2197`. -/
private lemma zr3 : ((((5:ℂ)+12*Complex.I)/13) ^ (3:ℤ)).re = -2035/2197 := by
  rw [show (3:ℤ) = ((3:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm3

/-- The real part of the fourth integer power of `(5 + 12i) / 13` is `−239 / 28561`. -/
private lemma zr4 : ((((5:ℂ)+12*Complex.I)/13) ^ (4:ℤ)).re = -239/28561 := by
  rw [show (4:ℤ) = ((4:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm4

/-- The real part of the fifth integer power of `(5 + 12i) / 13` is `341525 / 371293`. -/
private lemma zr5 : ((((5:ℂ)+12*Complex.I)/13) ^ (5:ℤ)).re = 341525/371293 := by
  rw [show (5:ℤ) = ((5:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm5

/-- The real part of the sixth integer power of `(5 + 12i) / 13` is `3455641 / 4826809`. -/
private lemma zr6 : ((((5:ℂ)+12*Complex.I)/13) ^ (6:ℤ)).re = 3455641/4826809 := by
  rw [show (6:ℤ) = ((6:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm6

/-- The real part of `13 / (5 + 12i)` is `5 / 13`. -/
private lemma zrinv : ((13:ℂ)/(5+12*Complex.I)).re = 5/13 := by
  have h : (13:ℂ)/(5+12*Complex.I) = Complex.mk (5/13) (-12/13) := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  rw [h]

/-- The certificate evaluation point `(5 + 12i) / 13` has norm one. -/
theorem norm_zc : ‖(((5:ℂ)+12*Complex.I)/13)‖ = 1 := by
  have hsq : ‖(((5:ℂ)+12*Complex.I)/13)‖^2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [show Complex.normSq (((5:ℂ)+12*Complex.I)/13) = 1 from by
      rw [Complex.normSq_div]; norm_num [Complex.normSq_apply]]
  nlinarith [norm_nonneg (((5:ℂ)+12*Complex.I)/13)]

/-- The seven-entry certificate vector with constant coefficient one and entries `(7 − 2 * i) /
14` at nonzero indices. -/
def certCoeff : Fin 7 → ℝ := fun i => if (i:ℕ) = 0 then 1 else ((7:ℝ) - 2*(i:ℕ))/14

/-- The real Laurent evaluation of `certCoeff` at `(5 + 12i) / 13` equals `−2154473 / 33787663`
[ChildsLandahlParrilo2007]. -/
theorem certCoeff_eval :
    (laurentEval certCoeff (((5:ℂ)+12*Complex.I)/13)).re = -2154473/33787663 := by
  unfold certCoeff laurentEval
  simp only [Fin.sum_univ_succ]
  simp
  rw [show Complex.normSq (5 + 12*Complex.I) = 169 from by norm_num [Complex.normSq_apply]]
  norm_num
  simp only [zrinv, zc_eq, zm2, zm3, zm4, zm5, zm6]
  norm_num

/-- The real Laurent evaluation of `certCoeff` at the certificate point is strictly negative. -/
theorem certCoeff_eval_neg :
    (laurentEval certCoeff (((5:ℂ)+12*Complex.I)/13)).re < 0 := by
  rw [certCoeff_eval]; norm_num

/-- In any solution of the size-seven two-query paper program, every nonzero-offset generalized
trace of the final matrix vanishes. -/
private theorem genTrace_Q2_of_ne {Q : ℕ → Matrix (Fin 7) (Fin 7) ℂ}
    (h : SolvesPaperSDP 7 2 Q) (j : ℤ) (hj : j ≠ 0) : genTrace (Q 2) j = 0 := by
  have hqk : (Q 2) = (7:ℂ)⁻¹ • (1 : Matrix (Fin 7) (Fin 7) ℂ) := h.2.2.2.2.1
  rw [hqk, genTrace_smul]
  have hone : (1 : Matrix (Fin 7) (Fin 7) ℂ) = Matrix.diagonal (fun _ => (1:ℂ)) := by
    ext a b; simp [Matrix.one_apply, Matrix.diagonal]
  rw [hone, genTrace_diagonal]
  simp [hj]

/-- In any solution of the size-seven two-query paper program, the initial matrix has every
entry equal to `1 / 7`. -/
private theorem genTrace_Q0_of {Q : ℕ → Matrix (Fin 7) (Fin 7) ℂ}
    (h : SolvesPaperSDP 7 2 Q) :
    (Q 0) = Matrix.of (fun _ _ : Fin 7 => (7:ℂ)⁻¹) := by
  ext a b; rw [h.2.2.1 a b]; simp

/-- In any solution of the size-seven two-query paper program, the real generalized traces of
the stage-one matrix equal `certCoeff` at offsets zero through six. -/
theorem genTrace_Q1_re {Q : ℕ → Matrix (Fin 7) (Fin 7) ℂ}
    (h : SolvesPaperSDP 7 2 Q) (i : Fin 7) :
    (genTrace (Q 1) ((i:ℕ):ℤ)).re = certCoeff i := by
  have hstep := h.2.2.2.2.2
  have htrace := h.2.2.2.1
  have hQ0 := genTrace_Q0_of h
  by_cases hi : (i:ℕ) = 0
  · have hi0 : ((i:ℕ):ℤ) = 0 := by omega
    rw [hi0, genTrace_zero, htrace 1 (by norm_num)]
    simp [certCoeff, hi]
  · have hi_pos : 0 < (i:ℕ) := Nat.pos_of_ne_zero hi
    have hi_lt : (i:ℕ) < 7 := i.isLt
    have hmem : ((i:ℕ):ℤ) ∈ Finset.Ioo (0:ℤ) (7:ℤ) := by
      rw [Finset.mem_Ioo]; omega
    have e1 := hstep 1 (by norm_num) ((i:ℕ):ℤ) hmem
    have e2 := hstep 2 (by norm_num) ((i:ℕ):ℤ) hmem
    simp only [show ((7:ℕ):ℤ) = 7 from rfl, show (1:ℕ)-1 = 0 from rfl,
      show (2:ℕ)-1 = 1 from rfl] at e1 e2

    have hna : (((i:ℕ):ℤ)).natAbs = (i:ℕ) := Int.natAbs_natCast (i:ℕ)
    have hna' : (((i:ℕ):ℤ) - 7).natAbs = 7 - (i:ℕ) := by
      rw [show (((i:ℕ):ℤ) - 7) = -(((7 - (i:ℕ)) : ℕ) : ℤ) by omega,
        Int.natAbs_neg, Int.natAbs_natCast]
    have hgi : genTrace (Q 0) ((i:ℕ):ℤ) = ((((7 - (i:ℕ)) : ℕ) : ℝ) / 7 : ℝ) := by
      rw [hQ0, genTrace_const, hna]; push_cast; ring
    have hgi' : genTrace (Q 0) (((i:ℕ):ℤ) - 7) = ((((i:ℕ)) : ℝ) / 7 : ℝ) := by
      rw [hQ0, genTrace_const, hna']
      have h7 : (7 - (7 - (i:ℕ)) : ℕ) = (i:ℕ) := by omega
      rw [h7]; push_cast; ring

    have h2i : genTrace (Q 2) ((i:ℕ):ℤ) = 0 := genTrace_Q2_of_ne h _ (by omega)
    have h2i' : genTrace (Q 2) (((i:ℕ):ℤ) - 7) = 0 := genTrace_Q2_of_ne h _ (by omega)

    have h1 : genTrace (Q 1) ((i:ℕ):ℤ) - genTrace (Q 1) (((i:ℕ):ℤ) - 7)
        = ((((7 - (i:ℕ)) : ℕ) : ℝ) / 7 : ℝ) - ((((i:ℕ)) : ℝ) / 7) := by
      have := e1
      rw [hgi, hgi'] at this
      simpa using! this
    have h2 : genTrace (Q 1) ((i:ℕ):ℤ) + genTrace (Q 1) (((i:ℕ):ℤ) - 7) = 0 := by
      have := e2
      rw [h2i, h2i', mul_zero, add_zero] at this
      simpa using! this.symm

    have hsum : (2:ℂ) * genTrace (Q 1) ((i:ℕ):ℤ)
        = ((((7 - (i:ℕ)) : ℕ) : ℝ) / 7 : ℝ) - ((((i:ℕ)) : ℝ) / 7) := by
      linear_combination h1 + h2

    have hre : (genTrace (Q 1) ((i:ℕ):ℤ)).re
        = ((((7 - (i:ℕ)) : ℝ) - (i:ℝ)) / 7) / 2 := by
      have htake := congrArg Complex.re hsum
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.div_re] at htake
      norm_num at htake
      linarith
    rw [hre]
    simp only [certCoeff, hi, if_false]
    ring

/-- The size-seven two-query paper semidefinite program is infeasible
[ChildsLandahlParrilo2007]. -/
theorem not_paperSDP_seven_two : ¬ PaperSDP 7 2 := by
  rintro ⟨Q, hQ⟩

  have hfun : (fun i : Fin 7 => (genTrace (Q 1) ((i:ℕ):ℤ)).re) = certCoeff := by
    funext i; exact genTrace_Q1_re hQ i

  have hnonneg :=
      laurentEval_real_genTrace_nonneg (Q 1) (hQ.1 1) (z := (((5:ℂ)+12*Complex.I)/13)) norm_zc
  rw [hfun] at hnonneg

  have hneg := certCoeff_eval_neg
  linarith

end Qatlib.Papers.OrderedSearch06.MainResults
