/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBNormalization
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis
open scoped Matrix

noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩
noncomputable def omegaBar : ℂ := ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩

noncomputable def H : MatrixSix :=
  !![1,1,1,1,1,1;
     1,omega,omegaBar,1,omega,omegaBar;
     1,omegaBar,omega,1,omegaBar,omega;
     1,1,1,-1,-1,-1;
     1,omega,omegaBar,-1,-omega,-omegaBar;
     1,omegaBar,omega,-1,-omegaBar,-omega]

noncomputable def K : MatrixSix :=
  !![1,1,1,1,1,1;
     omega,omegaBar,1,omega,omegaBar,1;
     omega,1,omegaBar,omega,1,omegaBar;
     Complex.I,Complex.I,Complex.I,-Complex.I,-Complex.I,-Complex.I;
     Complex.I*omega,Complex.I*omegaBar,Complex.I,
       -Complex.I*omega,-Complex.I*omegaBar,-Complex.I;
     Complex.I*omega,Complex.I,Complex.I*omegaBar,
       -Complex.I*omega,-Complex.I,-Complex.I*omegaBar]

/-- The square of the real square root of three is three. -/
private theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

set_option maxHeartbeats 6000000 in

/-- The Gram matrix of `H` is six times the identity. -/
theorem H_gram : Hᴴ * H = (6 : ℂ) • (1 : MatrixSix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [H, omega, omegaBar, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt_three_sq]

set_option maxHeartbeats 6000000 in

/-- The Gram matrix of `K` is six times the identity. -/
theorem K_gram : Kᴴ * K = (6 : ℂ) • (1 : MatrixSix) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [K, omega, omegaBar, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [sqrt_three_sq]

/-- Every entry of `H` has squared norm one. -/
theorem H_entry_normSq (i j : Fin 6) : Complex.normSq (H i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [H, omega, omegaBar, Complex.normSq_apply] <;>
    nlinarith [sqrt_three_sq]

/-- Every entry of `K` has squared norm one. -/
theorem K_entry_normSq (i j : Fin 6) : Complex.normSq (K i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [K, omega, omegaBar, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt_three_sq]

set_option maxHeartbeats 6000000 in

/-- Every entry of the relative Gram matrix of `H` and `K` has squared norm six. -/
theorem HK_entry_normSq (i j : Fin 6) :
    Complex.normSq ((Hᴴ * K) i j) = 6 := by
  have h4 : (Real.sqrt 3) ^ 4 = 9 := by nlinarith [sq_nonneg ((Real.sqrt 3)^2 - 3), sqrt_three_sq]
  fin_cases i <;> fin_cases j <;>
    norm_num [H, K, omega, omegaBar, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sqrt_three_sq, h4]

noncomputable def bases : Fin 3 → Fin 6 → Qatlib.Foundations.PureStateMath.QState (Fin 6) :=
  fun r j i => if r = 0 then Qatlib.Foundations.PureStateMath.Ket j i
    else if r = 1 then normalizeHadamard H i j else normalizeHadamard K i j

/-- Each canonical basis has orthonormal columns. -/
theorem bases_orthonormal (r : Fin 3) : OrthonormalColumns (bases r) := by
  fin_cases r
  · simpa [bases] using! (orthonormalColumns_ket (d := 6))
  · simpa [bases] using! orthonormalColumns_of_unitary
      (normalizeHadamard H) ((normalizeHadamard_unitary_iff H).mpr H_gram)
  · simpa [bases] using! orthonormalColumns_of_unitary
      (normalizeHadamard K) ((normalizeHadamard_unitary_iff K).mpr K_gram)

/-- Every entry of the relative Gram matrix of normalized `H` and `K` has squared norm one
sixth. -/
theorem normalized_HK_normSq (i j : Fin 6) :
    Complex.normSq (((normalizeHadamard H)ᴴ * normalizeHadamard K) i j) = 1 / 6 := by
  rw [normSq_normalizeHadamard_relative, HK_entry_normSq]
  norm_num

/-- Vectors from distinct canonical bases, ordered by basis index, have overlap squared norm one
sixth. -/
theorem bases_ordered (r s : Fin 3) (hrs : r.val < s.val) (i j : Fin 6) :
    Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (bases r i) (bases s j)) = (1 : ℝ) / 6 := by
  fin_cases r <;> fin_cases s
  all_goals norm_num at hrs
  · change Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) (fun t => normalizeHadamard H t j)) = _
    rw [inner_ket_eq_coordinate, normSq_normalizeHadamard_entry, H_entry_normSq]
    norm_num
  · change Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) (fun t => normalizeHadamard K t j)) = _
    rw [inner_ket_eq_coordinate, normSq_normalizeHadamard_entry, K_entry_normSq]
    norm_num
  · change Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (fun t => normalizeHadamard H t i)
      (fun t => normalizeHadamard K t j)) = _
    rw [inner_matrixColumns]
    exact normalized_HK_normSq i j

/-- The canonical bases form a mutually unbiased family. -/
theorem bases_isFamily : IsFamily bases := by
  refine ⟨bases_orthonormal, ?_⟩
  intro r s hrs i j
  by_cases hlt : r.val < s.val
  · exact bases_ordered r s hlt i j
  · have hne : r.val ≠ s.val := fun h => hrs (Fin.ext h)
    rw [normSq_inner_comm]
    exact bases_ordered s r (by omega) j i

/-- There exists a family of three mutually unbiased bases in dimension six. -/
theorem threeBasesExist : ∃ B : Fin 3 → Fin 6 → Qatlib.Foundations.PureStateMath.QState (Fin 6), IsFamily B :=
  ⟨bases, bases_isFamily⟩

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
