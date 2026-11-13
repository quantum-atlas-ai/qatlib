/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ParityWeights
import Qatlib.Papers.QCellAutomata96.MainResults.ParityReduction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Scalar constraints for parity-invariant weights

This module expands selected Equation (19) constraints for real amplitudes and complex phases in
reduced two-component weights. It derives the coefficient and normalization conditions and
identifies the zero-mixing specialization of Equation (24) with the nearest-neighbor weights of
Equation (17). See [Meyer1996a].

## Main statements

* `eq19_forces_d_real`: If `a ≠ 0`, unit-modulus phases and `Eq19` force `d = -b * c / a`.
* `eq19_forces_constraint`: If `a ≠ 0`, unit-modulus phases and `Eq19` imply the reduced
  normalization identity `a² + b² + c² * (1 + b² / a²) = 1`.
* `eq24_rho_zero_w0`: At `ρ = 0`, the Equation (24) on-site weight vanishes.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option autoImplicit false
noncomputable section

open Complex Qatlib.Concepts.QcaDynamics.ParityWeights

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- The reduced negative-direction weight with nonzero second column `(i * a * p, b * q)`. -/
def redWm (a b : ℝ) (p q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => match i, j with
    | 0, 1 => I * (a : ℂ) * p
    | 1, 1 => (b : ℂ) * q
    | _, _ => 0

/-- The reduced positive-direction weight with nonzero first column `(b * q, i * a * p)`. -/
def redWp (a b : ℝ) (p q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => (b : ℂ) * q
    | 1, 0 => I * (a : ℂ) * p
    | _, _ => 0

/-- The symmetric on-site weight with diagonal entry `c * r` and off-diagonal entry `i * d * s`. -/
def redW0 (c d : ℝ) (r s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => (c : ℂ) * r
    | 0, 1 => I * (d : ℂ) * s
    | 1, 0 => I * (d : ℂ) * s
    | 1, 1 => (c : ℂ) * r

/-- The complex conjugate of the imaginary unit is its negative. -/
theorem star_I_complex : star (I : ℂ) = -I := by
  rw [Complex.star_def, Complex.conj_I]

/-- The complex embedding of a real number is fixed by conjugation. -/
theorem star_real_coe (x : ℝ) : star ((x : ℂ)) = (x : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The reduced on-site weight is invariant under conjugation by the component-swap matrix. See
[Meyer1996a]. -/
theorem redW0_parity (c d : ℝ) (r s : ℂ) : P2 * redW0 c d r s * P2 = redW0 c d r s := by
  rw [parity_iff_equal_entries]
  constructor <;> simp [redW0]

/-- Conjugating the reduced positive-direction weight by the component-swap matrix gives the
negative-direction weight. See [Meyer1996a]. -/
theorem redWm_parity (a b : ℝ) (p q : ℂ) : P2 * redWp a b p q * P2 = redWm a b p q := by
  rw [P2_eq_of]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [redWm, redWp, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `(0, 1)` entry of the mixed Equation (19) expression is the displayed phase-difference
product `i * b * d * (s * star q - q * star s)`. See [Meyer1996a]. -/
theorem eq19_zero_entry01 (a b c d : ℝ) (p q r s : ℂ) :
    (redW0 c d r s * star (redWm a b p q) + redWp a b p q * star (redW0 c d r s)) 0 1 =
      I * (b : ℂ) * (d : ℂ) * (s * star q - q * star s) := by
  simp [redW0, redWm, redWp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  ring_nf

/-- The `(0, 1)` mixed-constraint entry vanishes when the on-site off-diagonal phase equals `q`. -/
theorem eq19_zero_entry01_eq (a b c d : ℝ) (p q r : ℂ) :
    (redW0 c d r q * star (redWm a b p q) + redWp a b p q * star (redW0 c d r q)) 0 1 = 0 := by
  rw [eq19_zero_entry01]
  ring

/-- The `(0, 0)` entry of the mixed Equation (19) expression equals `a * d * (s * star p) + b *
c * (q * star r)`. See [Meyer1996a]. -/
theorem eq19_zero_entry00 (a b c d : ℝ) (p q r s : ℂ) :
    (redW0 c d r s * star (redWm a b p q) + redWp a b p q * star (redW0 c d r s)) 0 0 =
      (a : ℂ) * (d : ℂ) * (s * star p) + (b : ℂ) * (c : ℂ) * (q * star r) := by
  simp [redW0, redWm, redWp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  ring_nf
  rw [show (I : ℂ) ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
  ring

/-- When the on-site phases are `p` and `q`, the `(0, 0)` mixed-constraint entry factors as `(a
* d + b * c) * (q * star p)`. -/
theorem eq19_zero_entry00_eq (a b c d : ℝ) (p q : ℂ) :
    (redW0 c d p q * star (redWm a b p q) + redWp a b p q * star (redW0 c d p q)) 0 0 =
      ((a : ℂ) * (d : ℂ) + (b : ℂ) * (c : ℂ)) * (q * star p) := by
  rw [eq19_zero_entry00]
  ring

/-- For unit-modulus phases, the `(0, 0)` normalization entry is the sum `a² + b² + c² + d²`. -/
theorem eq19_minus1_entry00 (a b c d : ℝ) (p q r s : ℂ)
    (hp : p * star p = 1) (hq : q * star q = 1)
    (hr : r * star r = 1) (hs : s * star s = 1) :
    (redWm a b p q * star (redWm a b p q) + redW0 c d r s * star (redW0 c d r s) +
      redWp a b p q * star (redWp a b p q)) 0 0 =
      ((a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2 + (d : ℂ) ^ 2) := by
  simp [redW0, redWm, redWp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  have hI : (I : ℂ) ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
  ring_nf
  rw [hI]
  simp only [mul_assoc]
  have hp' : p * (starRingEnd ℂ) p = 1 := hp
  have hq' : q * (starRingEnd ℂ) q = 1 := hq
  have hr' : r * (starRingEnd ℂ) r = 1 := hr
  have hs' : s * (starRingEnd ℂ) s = 1 := hs
  rw [hp', hq', hr', hs']
  ring

/-- With unit-modulus phases and matching on-site phases, `Eq19` forces `a * d + b * c = 0`. See
[Meyer1996a]. -/
theorem eq19_forces_d (a b c d : ℝ) (p q : ℂ)
    (hp : p * star p = 1) (hq : q * star q = 1)
    (h : Eq19 (redWm a b p q) (redW0 c d p q) (redWp a b p q)) :
    (a : ℂ) * (d : ℂ) + (b : ℂ) * (c : ℂ) = 0 := by
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hq
    exact zero_ne_one hq
  have hpne : p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hp
    exact zero_ne_one hp
  have hspne : star p ≠ 0 := fun h0 => hpne (by simpa using congrArg star h0)
  have hqsp : q * star p ≠ 0 := mul_ne_zero hqne hspne
  have h00 : (redW0 c d p q * star (redWm a b p q) +
      redWp a b p q * star (redW0 c d p q)) 0 0 = 0 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h.2.1
  rw [eq19_zero_entry00_eq] at h00
  have hmul : ((a : ℂ) * (d : ℂ) + (b : ℂ) * (c : ℂ)) * (q * star p) = 0 := by
    simpa [mul_assoc] using h00
  exact (mul_eq_zero.mp hmul).resolve_right hqsp

/-- If `a ≠ 0`, unit-modulus phases and `Eq19` force `d = -b * c / a`. See [Meyer1996a]. -/
theorem eq19_forces_d_real (a b c d : ℝ) (p q : ℂ) (ha : a ≠ 0)
    (hp : p * star p = 1) (hq : q * star q = 1)
    (h : Eq19 (redWm a b p q) (redW0 c d p q) (redWp a b p q)) :
    d = - b * c / a := by
  have hc := eq19_forces_d a b c d p q hp hq h
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hdC : (d : ℂ) = -((b : ℂ) * (c : ℂ)) / (a : ℂ) := by
    field_simp [haC]
    linear_combination hc
  have hR : ((d : ℝ) : ℂ) = ((- b * c / a : ℝ) : ℂ) := by
    rw [hdC]
    push_cast
    ring
  exact Complex.ofReal_inj.mp hR

/-- If `a ≠ 0`, unit-modulus phases and `Eq19` imply the reduced normalization identity `a² + b²
+ c² * (1 + b² / a²) = 1`. See [Meyer1996a]. -/
theorem eq19_forces_constraint (a b c d : ℝ) (p q : ℂ) (ha : a ≠ 0)
    (hp : p * star p = 1) (hq : q * star q = 1)
    (h : Eq19 (redWm a b p q) (redW0 c d p q) (redWp a b p q)) :
    a ^ 2 + b ^ 2 + c ^ 2 * (1 + b ^ 2 / a ^ 2) = 1 := by
  have hd := eq19_forces_d_real a b c d p q ha hp hq h
  have h11 : (redWm a b p q * star (redWm a b p q) +
      redW0 c d p q * star (redW0 c d p q) +
      redWp a b p q * star (redWp a b p q)) 0 0 = 1 := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h.1
  rw [eq19_minus1_entry00 a b c d p q p q hp hq hp hq] at h11
  have hsumC : ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) = 1 := by
    rw [show ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 : ℝ) : ℂ) =
        ((a : ℂ) ^ 2 + (b : ℂ) ^ 2 + (c : ℂ) ^ 2 + (d : ℂ) ^ 2) by push_cast; ring]
    simpa using h11
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
    exact Complex.ofReal_inj.mp hsumC
  have hd' : a * d + b * c = 0 := by
    rw [hd]
    field_simp
    ring
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hsq : a ^ 2 * d ^ 2 = b ^ 2 * c ^ 2 := by
    have hlin : a * d = -(b * c) := by linarith
    rw [show a ^ 2 * d ^ 2 = (a * d) ^ 2 by ring, hlin]
    ring
  field_simp [ha2]
  linear_combination (a ^ 2) * hsum - hsq

/-- The negative-direction nearest-neighbor weight of Equation (17). -/
def eq17Left (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, I * (Real.sin θ : ℂ); 0, (Real.cos θ : ℂ)]

/-- The positive-direction nearest-neighbor weight of Equation (17). -/
def eq17Right (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), 0; I * (Real.sin θ : ℂ), 0]

/-- At `ρ = 0`, the Equation (24) negative-direction weight equals `eq17Left θ`. See
[Meyer1996a]. -/
theorem eq24_rho_zero_wm (θ : ℝ) : eq24wm θ 0 = eq17Left θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eq24wm, eq17Left, Matrix.smul_apply]

/-- At `ρ = 0`, the Equation (24) positive-direction weight equals `eq17Right θ`. See
[Meyer1996a]. -/
theorem eq24_rho_zero_wp (θ : ℝ) : eq24wp θ 0 = eq17Right θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eq24wp, eq17Right, Matrix.smul_apply]

/-- At `ρ = 0`, the Equation (24) on-site weight vanishes. See [Meyer1996a]. -/
theorem eq24_rho_zero_w0 (θ : ℝ) : eq24w0 θ 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eq24w0, Matrix.smul_apply]

end Qatlib.Papers.QCellAutomata96.MainResults
