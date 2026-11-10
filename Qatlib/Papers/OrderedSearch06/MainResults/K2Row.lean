/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch06.SdpForm.Basic
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.MainResults

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Papers.OrderedSearch06.SdpForm
open Qatlib.Papers.OrderedSearch06.LaurentDefs

private lemma zc_eq : (((5:ℂ)+12*Complex.I)/13) = Complex.mk (5/13) (12/13) := by
  apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]

private lemma zm2 : (Complex.mk (5/13) (12/13) ^ 2).re = -119/169 := by
  rw [pow_two, Complex.mk_mul_mk]; norm_num

private lemma zm3 : (Complex.mk (5/13) (12/13) ^ 3).re = -2035/2197 := by
  rw [pow_succ, pow_two, Complex.mk_mul_mk, Complex.mk_mul_mk]; norm_num

private lemma zm4 : (Complex.mk (5/13) (12/13) ^ 4).re = -239/28561 := by
  rw [pow_succ, pow_succ, pow_two, Complex.mk_mul_mk, Complex.mk_mul_mk,
    Complex.mk_mul_mk]; norm_num

private lemma zm5 : (Complex.mk (5/13) (12/13) ^ 5).re = 341525/371293 := by
  rw [pow_succ, pow_succ, pow_succ, pow_two, Complex.mk_mul_mk, Complex.mk_mul_mk,
    Complex.mk_mul_mk, Complex.mk_mul_mk]; norm_num

private lemma zm6 : (Complex.mk (5/13) (12/13) ^ 6).re = 3455641/4826809 := by
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_two, Complex.mk_mul_mk,
    Complex.mk_mul_mk, Complex.mk_mul_mk, Complex.mk_mul_mk, Complex.mk_mul_mk]; norm_num

private lemma zr2 : ((((5:ℂ)+12*Complex.I)/13) ^ (2:ℤ)).re = -119/169 := by
  rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm2

private lemma zr3 : ((((5:ℂ)+12*Complex.I)/13) ^ (3:ℤ)).re = -2035/2197 := by
  rw [show (3:ℤ) = ((3:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm3

private lemma zr4 : ((((5:ℂ)+12*Complex.I)/13) ^ (4:ℤ)).re = -239/28561 := by
  rw [show (4:ℤ) = ((4:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm4

private lemma zr5 : ((((5:ℂ)+12*Complex.I)/13) ^ (5:ℤ)).re = 341525/371293 := by
  rw [show (5:ℤ) = ((5:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm5

private lemma zr6 : ((((5:ℂ)+12*Complex.I)/13) ^ (6:ℤ)).re = 3455641/4826809 := by
  rw [show (6:ℤ) = ((6:ℕ):ℤ) from rfl, zpow_natCast, zc_eq]; exact zm6

private lemma zrinv : ((13:ℂ)/(5+12*Complex.I)).re = 5/13 := by
  have h : (13:ℂ)/(5+12*Complex.I) = Complex.mk (5/13) (-12/13) := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  rw [h]

theorem norm_zc : ‖(((5:ℂ)+12*Complex.I)/13)‖ = 1 := by
  have hsq : ‖(((5:ℂ)+12*Complex.I)/13)‖^2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [show Complex.normSq (((5:ℂ)+12*Complex.I)/13) = 1 from by
      rw [Complex.normSq_div]; norm_num [Complex.normSq_apply]]
  nlinarith [norm_nonneg (((5:ℂ)+12*Complex.I)/13)]

def certCoeff : Fin 7 → ℝ := fun i => if (i:ℕ) = 0 then 1 else ((7:ℝ) - 2*(i:ℕ))/14

theorem certCoeff_eval :
    (laurentEval certCoeff (((5:ℂ)+12*Complex.I)/13)).re = -2154473/33787663 := by
  unfold certCoeff laurentEval
  simp only [Fin.sum_univ_succ]
  simp
  rw [show Complex.normSq (5 + 12*Complex.I) = 169 from by norm_num [Complex.normSq_apply]]
  norm_num
  simp only [zrinv, zc_eq, zm2, zm3, zm4, zm5, zm6]
  norm_num

theorem certCoeff_eval_neg :
    (laurentEval certCoeff (((5:ℂ)+12*Complex.I)/13)).re < 0 := by
  rw [certCoeff_eval]; norm_num

private theorem genTrace_Q2_of_ne {Q : ℕ → Matrix (Fin 7) (Fin 7) ℂ}
    (h : SolvesPaperSDP 7 2 Q) (j : ℤ) (hj : j ≠ 0) : genTrace (Q 2) j = 0 := by
  have hqk : (Q 2) = (7:ℂ)⁻¹ • (1 : Matrix (Fin 7) (Fin 7) ℂ) := h.2.2.2.2.1
  rw [hqk, genTrace_smul]
  have hone : (1 : Matrix (Fin 7) (Fin 7) ℂ) = Matrix.diagonal (fun _ => (1:ℂ)) := by
    ext a b; simp [Matrix.one_apply, Matrix.diagonal]
  rw [hone, genTrace_diagonal]
  simp [hj]

private theorem genTrace_Q0_of {Q : ℕ → Matrix (Fin 7) (Fin 7) ℂ}
    (h : SolvesPaperSDP 7 2 Q) :
    (Q 0) = Matrix.of (fun _ _ : Fin 7 => (7:ℂ)⁻¹) := by
  ext a b; rw [h.2.2.1 a b]; simp

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
