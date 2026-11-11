/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciDensity

/-!
# Normalized Fibonacci generators in SU(2)

The matrices `Gfib` and `Hfib` are explicit special unitary normalizations of Fibonacci
generators, and `Gfib` has tenth power minus the identity and twentieth power the identity. The
predicates `generatedDense`, `FibDense`, and `GenericB3Dense` state approximation and
generic-density properties; `trivial_rep_not_dense` refutes the assertion that every special
unitary braid pair generates dense words [KauffmanLomonaco2006].

## Main statements

* `Gfib_mem_SU2`: proves that `Gfib` is special unitary.
* `Hfib_mem_SU2`: proves that `Hfib` is special unitary.
* `Gfib_pow_twenty`: gives the twentieth-power identity.
* `trivial_rep_not_dense`: refutes universal density of special unitary braid pairs.

## References

* [Kauffman and Lomonaco, 2006][KauffmanLomonaco2006]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciSU2

open Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciDensity

/-- The Fibonacci angle `7 * π / 10`. -/
def thetaFib : ℝ := 7 * Real.pi / 10

/-- The diagonal matrix with phases `exp (I * thetaFib)` and `exp (-I * thetaFib)`. -/
def Gfib : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * ((thetaFib : ℝ) : ℂ)), 0;
     0, Complex.exp (-(Complex.I * ((thetaFib : ℝ) : ℂ)))]

/-- The matrix `Fmat` multiplied by the scalar `I`. -/
def Ffib : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • Fmat

/-- The conjugate `Fmat * Gfib * Fmat` of the diagonal Fibonacci generator. -/
def Hfib : Matrix (Fin 2) (Fin 2) ℂ := Fmat * Gfib * Fmat

/-- For real `θ`, the complex phase `exp (I * θ)` has norm one. -/
lemma norm_exp_I_mul (θ : ℝ) : ‖Complex.exp (Complex.I * ((θ : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * ((θ : ℝ) : ℂ)).re = - ((θ : ℝ) : ℂ).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h, Complex.ofReal_im]
  simp

/-- For real `θ`, the complex phase `exp (-I * θ)` has norm one. -/
lemma norm_exp_neg_I_mul (θ : ℝ) :
    ‖Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (-(Complex.I * ((θ : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h]
  simp

/-- The matrix `Gfib` is unitary. -/
lemma Gfib_unitary : Gfib ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gfib, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa using mul_star_self_of_norm_one (norm_exp_I_mul thetaFib)
  · simpa using mul_star_self_of_norm_one (norm_exp_neg_I_mul thetaFib)

/-- The determinant of `Gfib` equals one. -/
lemma Gfib_det : Gfib.det = 1 := by
  rw [Matrix.det_fin_two]
  simp [Gfib, ← Complex.exp_add]

/-- The square of `Ffib` equals minus the identity matrix. -/
lemma Ffib_sq : Ffib * Ffib = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold Ffib
  rw [smul_mul_smul, F_sq]
  simp [Complex.I_mul_I]

/-- The matrix `Ffib` is unitary. -/
lemma Ffib_unitary : Ffib ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  unfold Ffib
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fmat, Matrix.mul_apply, Fin.sum_univ_two]
  · have hI : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
    have hsq : ((Real.sqrt tau : ℂ)) ^ 2 = (tau : ℂ) := by
      rw [pow_two, ← Complex.ofReal_mul, sqrt_tau_sq]
    have h : tau * tau + tau = 1 := by simpa [pow_two] using tau_sq_add
    have hc : (tau : ℂ) * (tau : ℂ) + (tau : ℂ) = 1 := by exact_mod_cast h
    ring_nf
    rw [hI, hsq]
    ring_nf
    simpa [pow_two, add_comm] using hc
  · ring
  · ring
  · have hI : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
    have hsq : ((Real.sqrt tau : ℂ)) ^ 2 = (tau : ℂ) := by
      rw [pow_two, ← Complex.ofReal_mul, sqrt_tau_sq]
    have h : tau * tau + tau = 1 := by simpa [pow_two] using tau_sq_add
    have hc : (tau : ℂ) * (tau : ℂ) + (tau : ℂ) = 1 := by exact_mod_cast h
    ring_nf
    rw [hI, hsq]
    ring_nf
    simpa [pow_two, add_comm] using hc

/-- The determinant of `Fmat` equals minus one. -/
lemma Fmat_det : Fmat.det = -1 := by
  rw [Matrix.det_fin_two]
  simp [Fmat]
  have hs : (Real.sqrt tau : ℂ) * (Real.sqrt tau : ℂ) = (tau : ℂ) := by
    rw [← Complex.ofReal_mul, sqrt_tau_sq]
  rw [hs]
  have h : tau * tau + tau = 1 := by simpa [pow_two] using tau_sq_add
  have hc : (tau : ℂ) * (tau : ℂ) + (tau : ℂ) = 1 := by exact_mod_cast h
  linear_combination -hc

/-- The determinant of `Ffib` equals one. -/
lemma Ffib_det : Ffib.det = 1 := by
  unfold Ffib
  rw [Matrix.det_smul, Fmat_det]
  rw [Fintype.card_fin]
  rw [pow_two, Complex.I_mul_I]
  norm_num

/-- The matrix `Hfib` is unitary. -/
lemma Hfib_unitary : Hfib ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  unfold Hfib
  exact mul_mem (mul_mem F_unitary Gfib_unitary) F_unitary

/-- The determinant of `Hfib` equals one. -/
lemma Hfib_det : Hfib.det = 1 := by
  unfold Hfib
  rw [Matrix.det_mul, Matrix.det_mul, Fmat_det, Gfib_det]
  norm_num

/-- The matrix `Gfib` belongs to the special unitary group on `Fin 2` [KauffmanLomonaco2006]. -/
theorem Gfib_mem_SU2 : Gfib ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Gfib_unitary, Gfib_det⟩

/-- The matrix `Hfib` belongs to the special unitary group on `Fin 2` [KauffmanLomonaco2006]. -/
theorem Hfib_mem_SU2 : Hfib ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Hfib_unitary, Hfib_det⟩

/-- The ordered product of a Boolean word in matrices `A` and `B`, with true selecting `A` and
false selecting `B`. -/
def wordProductGen (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    List Bool → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | b :: w => (if b then A else B) * wordProductGen A B w

/-- The assertion that words in `A` and `B` approximate every special unitary two-by-two matrix
to any positive entrywise tolerance. -/
def generatedDense (A B : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ ε : ℝ, 0 < ε →
    ∃ w : List Bool, ∀ i j, ‖wordProductGen A B w i j - U i j‖ < ε

/-- The assertion that words in `Gfib` and `Hfib` are dense in the special unitary group in the
entrywise approximation sense. -/
def FibDense : Prop := generatedDense Gfib Hfib

/-- The set of pairs of special unitary two-by-two matrices satisfying the braid relation `A * B
* A = B * A * B`. -/
def BraidPairSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
  {p | p.1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
       p.2 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
       p.1 * p.2 * p.1 = p.2 * p.1 * p.2}

/-- The assertion that braid pairs generating dense words form a dense subset of `BraidPairSU2`. -/
def GenericB3Dense : Prop :=
  Dense {p : BraidPairSU2 | generatedDense p.val.1 p.val.2}

/-- A natural power of `exp (I * θ)` equals `exp (I * (n * θ))`. -/
lemma exp_I_mul_pow (θ : ℝ) (n : ℕ) :
    (Complex.exp (Complex.I * ((θ : ℝ) : ℂ))) ^ n
      = Complex.exp (Complex.I * (((n : ℝ) * θ : ℝ) : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A natural power of `exp (-I * θ)` equals `exp (-I * (n * θ))`. -/
lemma exp_neg_I_mul_pow (θ : ℝ) (n : ℕ) :
    (Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))) ^ n
      = Complex.exp (-(Complex.I * (((n : ℝ) * θ : ℝ) : ℂ))) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The complex phase `exp (I * 7 * π)` equals minus one. -/
lemma exp_I_mul_seven_pi :
    Complex.exp (Complex.I * ((7 * Real.pi : ℝ) : ℂ)) = -1 := by
  have h : Complex.I * ((7 * Real.pi : ℝ) : ℂ)
      = (7 : ℕ) * (Complex.I * ((Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul]
  have hpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    have hI : Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by ring
    rw [hI, Complex.exp_pi_mul_I]
  rw [hpi]
  norm_num

/-- The complex phase `exp (I * 14 * π)` equals one. -/
lemma exp_I_mul_fourteen_pi :
    Complex.exp (Complex.I * ((14 * Real.pi : ℝ) : ℂ)) = 1 := by
  have h : Complex.I * ((14 * Real.pi : ℝ) : ℂ)
      = (2 : ℕ) * (Complex.I * ((7 * Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul, exp_I_mul_seven_pi]
  norm_num

/-- A natural power of a two-by-two diagonal matrix raises each diagonal entry to that power. -/
lemma diag2_pow (a b : ℂ) (n : ℕ) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ) ^ n = !![a ^ n, 0; 0, b ^ n] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- Ten times `thetaFib` equals `7 * π`. -/
lemma thetaFib_mul_ten : (((10 : ℕ) : ℝ) * thetaFib) = 7 * Real.pi := by
  unfold thetaFib
  push_cast
  ring

/-- Twenty times `thetaFib` equals `14 * π`. -/
lemma thetaFib_mul_twenty : (((20 : ℕ) : ℝ) * thetaFib) = 14 * Real.pi := by
  unfold thetaFib
  push_cast
  ring

/-- The tenth power of `Gfib` equals minus the identity matrix [KauffmanLomonaco2006]. -/
theorem Gfib_pow_ten : Gfib ^ 10 = -1 := by
  unfold Gfib
  rw [diag2_pow]
  have ha : Complex.exp (Complex.I * ((thetaFib : ℝ) : ℂ)) ^ 10
      = Complex.exp (Complex.I * ((7 * Real.pi : ℝ) : ℂ)) := by
    rw [exp_I_mul_pow, thetaFib_mul_ten]
  have hb : Complex.exp (-(Complex.I * ((thetaFib : ℝ) : ℂ))) ^ 10
      = Complex.exp (-(Complex.I * ((7 * Real.pi : ℝ) : ℂ))) := by
    rw [exp_neg_I_mul_pow, thetaFib_mul_ten]
  rw [ha, exp_I_mul_seven_pi, hb, Complex.exp_neg, exp_I_mul_seven_pi]
  norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]

/-- The twentieth power of `Gfib` equals the identity matrix [KauffmanLomonaco2006]. -/
theorem Gfib_pow_twenty : Gfib ^ 20 = 1 := by
  unfold Gfib
  rw [diag2_pow]
  have ha : Complex.exp (Complex.I * ((thetaFib : ℝ) : ℂ)) ^ 20
      = Complex.exp (Complex.I * ((14 * Real.pi : ℝ) : ℂ)) := by
    rw [exp_I_mul_pow, thetaFib_mul_twenty]
  have hb : Complex.exp (-(Complex.I * ((thetaFib : ℝ) : ℂ))) ^ 20
      = Complex.exp (-(Complex.I * ((14 * Real.pi : ℝ) : ℂ))) := by
    rw [exp_neg_I_mul_pow, thetaFib_mul_twenty]
  rw [ha, exp_I_mul_fourteen_pi, hb, Complex.exp_neg, exp_I_mul_fourteen_pi]
  norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- It is false that every pair of special unitary two-by-two matrices satisfying the braid
relation generates words dense in the special unitary group [KauffmanLomonaco2006]. -/
theorem trivial_rep_not_dense :
    ¬ (∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
        A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
        B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
        A * B * A = B * A * B → generatedDense A B) := by
  intro h
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    exact ⟨by rw [Matrix.mem_unitaryGroup_iff]; simp, by simp⟩
  have hbraid : (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 * 1 = 1 * 1 * 1 := rfl
  have hd := h 1 1 hone hone hbraid
  set U : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I] with hU
  have hUmem : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hU, Matrix.mul_apply, Fin.sum_univ_two,
          Complex.conj_I, Complex.I_mul_I]
    · rw [Matrix.det_fin_two]
      simp [hU, Complex.I_mul_I]
  obtain ⟨w, hw⟩ := hd U hUmem (1 / 2) (by norm_num)
  have hconst : ∀ v : List Bool, wordProductGen (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 v = 1 := by
    intro v
    induction v with
    | nil => simp [wordProductGen]
    | cons b v ih =>
        show ((if b then (1 : Matrix (Fin 2) (Fin 2) ℂ) else 1) * wordProductGen 1 1 v) = 1
        rw [ih]
        split_ifs <;> simp
  have h00 := hw 0 0
  rw [hconst w] at h00
  simp [hU] at h00
  have hsq : Complex.normSq ((1 : ℂ) - Complex.I) = 2 := by
    rw [Complex.normSq_apply]
    simp
    norm_num
  have hnorm2 : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, hsq]
  have hval : ‖(1 : ℂ) - Complex.I‖ = Real.sqrt 2 := by
    rw [show ‖(1 : ℂ) - Complex.I‖ = Real.sqrt (‖(1 : ℂ) - Complex.I‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm, hnorm2]
  have hone_le : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [hval] at h00
  linarith

end Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciSU2
