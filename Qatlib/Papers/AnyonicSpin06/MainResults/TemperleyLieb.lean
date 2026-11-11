/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Two-dimensional Temperley–Lieb matrices

The explicit matrices `TLgen1` and `TLgen2` satisfy quadratic and triple-product identities, and
suitable scalar combinations `phi1` and `phi2` satisfy the braid relation under the stated
parameter conditions. Positive generator words split into a scalar identity term and `piPart`,
yielding a trace formula for the defined closure expression `bracketClosure`
[KauffmanLomonaco2006].

## Main statements

* `phi_braid`: proves the braid relation under the parameter equations.
* `phiWord_eq_smul_add_piPart`: splits a word into scalar and correction terms.
* `bracketClosure_eq_trace_add`: relates the closure expression to the word trace.

## References

* [Kauffman and Lomonaco, 2006][KauffmanLomonaco2006]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.AnyonicSpin06.MainResults.TemperleyLieb

/-- The complex diagonal matrix with entries `d` and zero. -/
def TLgen1 (d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![d, 0; 0, 0]

/-- The symmetric complex matrix with entries `d⁻¹`, `c`, `c`, and `d * c ^ 2`. -/
def TLgen2 (d c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![d⁻¹, c; c, d * c ^ 2]

/-- The square of `TLgen1 d` equals `d` times `TLgen1 d`. -/
theorem tlgen1_sq (d : ℂ) : TLgen1 d * TLgen1 d = d • TLgen1 d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TLgen1, Matrix.mul_apply, Fin.sum_univ_two]

/-- For nonzero `d` and `c ^ 2 = 1 - d⁻¹ ^ 2`, the square of `TLgen2 d c` equals `d` times
`TLgen2 d c`. -/
theorem tlgen2_sq {d c : ℂ} (hd : d ≠ 0) (hc : c ^ 2 = 1 - d⁻¹ ^ 2) :
    TLgen2 d c * TLgen2 d c = d • TLgen2 d c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TLgen2, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp at hc ⊢
    linear_combination hc
  · field_simp at hc ⊢
    linear_combination c * hc
  · field_simp at hc ⊢
    linear_combination c * hc
  · rw [show c * c = c ^ 2 by ring, hc]
    field_simp
    ring

/-- The product `TLgen1 d * TLgen2 d c * TLgen1 d` equals `TLgen1 d`. -/
theorem tlgen1_mul_tlgen2_mul_tlgen1 (d c : ℂ) :
    TLgen1 d * TLgen2 d c * TLgen1 d = TLgen1 d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TLgen1, TLgen2, Matrix.mul_apply, Fin.sum_univ_two]

/-- For nonzero `d`, the product `TLgen2 d c * TLgen1 d * TLgen2 d c` equals `TLgen2 d c`. -/
theorem tlgen2_mul_tlgen1_mul_tlgen2 {d c : ℂ} (hd : d ≠ 0) :
    TLgen2 d c * TLgen1 d * TLgen2 d c = TLgen2 d c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TLgen1, TLgen2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    try field_simp
    try ring

/-- The trace of `TLgen1 d` equals `d`. -/
theorem trace_tlgen1 (d : ℂ) : Matrix.trace (TLgen1 d) = d := by
  simp [TLgen1, Matrix.trace, Fin.sum_univ_two]

/-- For nonzero `d` and `c ^ 2 = 1 - d⁻¹ ^ 2`, the trace of `TLgen2 d c` equals `d`. -/
theorem trace_tlgen2 {d c : ℂ} (hd : d ≠ 0) (hc : c ^ 2 = 1 - d⁻¹ ^ 2) :
    Matrix.trace (TLgen2 d c) = d := by
  simp [TLgen2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  field_simp at hc ⊢
  linear_combination hc

/-- For nonzero `d`, the trace of `TLgen1 d * TLgen2 d c` equals one. -/
theorem trace_tlgen1_mul_tlgen2 {d c : ℂ} (hd : d ≠ 0) :
    Matrix.trace (TLgen1 d * TLgen2 d c) = 1 := by
  simp [TLgen1, TLgen2, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]
  field_simp

/-- The matrix `A` times the identity plus `A⁻¹` times `TLgen1 d`. -/
def phi1 (A d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A • (1 : Matrix (Fin 2) (Fin 2) ℂ) + A⁻¹ • TLgen1 d

/-- The matrix `A` times the identity plus `A⁻¹` times `TLgen2 d c`. -/
def phi2 (A d c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  A • (1 : Matrix (Fin 2) (Fin 2) ℂ) + A⁻¹ • TLgen2 d c

/-- For nonzero `A`, `d` satisfying `c ^ 2 = 1 - d⁻¹ ^ 2` and `d = -(A ^ 2 + (A⁻¹) ^ 2)`, the
matrices `phi1` and `phi2` satisfy the braid relation. -/
theorem phi_braid {A d c : ℂ} (hA : A ≠ 0) (hd : d ≠ 0)
    (hc : c ^ 2 = 1 - d⁻¹ ^ 2) (hdA : d = -(A ^ 2 + (A⁻¹) ^ 2)) :
    phi1 A d * phi2 A d c * phi1 A d
      = phi2 A d c * phi1 A d * phi2 A d c := by
  have hrel : A ^ 4 + A ^ 2 * d + 1 = 0 := by
    rw [hdA]
    field_simp
    ring
  have h1A : 1 + A ^ 4 ≠ 0 := by
    intro h
    have h2 : A ^ 2 * d = 0 := by linear_combination hrel - h
    have hA2 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA
    exact hd (by
      rcases mul_eq_zero.mp h2 with h' | h'
      · exact absurd h' hA2
      · exact h')
  have h2A : 1 + A ^ 4 * 2 + A ^ 8 ≠ 0 := by
    rw [show 1 + A ^ 4 * 2 + A ^ 8 = (1 + A ^ 4) ^ 2 by ring]
    exact pow_ne_zero 2 h1A
  have hdsub : d = -(A ^ 4 + 1) / A ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hA)]
    linear_combination hrel
  have hcA : c ^ 2 = (A ^ 8 + A ^ 4 + 1) / (A ^ 4 + 1) ^ 2 := by
    rw [hc, hdsub]
    field_simp
    ring_nf
    rw [show 1 + A ^ 4 * 2 + A ^ 8 = (1 + A ^ 4) ^ 2 by ring]
    field_simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi1, phi2, TLgen1, TLgen2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    field_simp
    ring_nf
    (try rw [show c ^ 4 = c ^ 2 * c ^ 2 by ring])
    (try rw [show c ^ 3 = c * c ^ 2 by ring])
    rw [hcA, hdsub]
    field_simp
    ring_nf
    field_simp
    ring

/-- The trace of `phi1 A d` equals `2 * A + A⁻¹ * d`. -/
theorem trace_phi1 (A d : ℂ) : Matrix.trace (phi1 A d) = 2 * A + A⁻¹ * d := by
  simp [phi1, TLgen1, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.smul_apply]
  ring

/-- For nonzero `d` and `c ^ 2 = 1 - d⁻¹ ^ 2`, the trace of `phi2 A d c` equals `2 * A + A⁻¹ *
d`. -/
theorem trace_phi2 {A d c : ℂ} (hd : d ≠ 0) (hc : c ^ 2 = 1 - d⁻¹ ^ 2) :
    Matrix.trace (phi2 A d c) = 2 * A + A⁻¹ * d := by
  unfold phi2
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, trace_tlgen2 hd hc]
  simp [Fintype.card_fin]
  ring

/-- The ordered matrix product encoded by a Boolean word, with true selecting `phi1` and false
selecting `phi2`. -/
def phiWord (A d c : ℂ) : List Bool → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | b :: w => (if b then phi1 A d else phi2 A d c) * phiWord A d c w

/-- The exponent sum of a positive Boolean generator word, defined as its length. -/
def expSum (w : List Bool) : ℕ := w.length

/-- The correction matrix obtained by subtracting `A ^ expSum w` times the identity from
`phiWord A d c w`. -/
def piPart (A d c : ℂ) (w : List Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  phiWord A d c w - A ^ expSum w • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Every positive generator word is the sum of `A ^ expSum w` times the identity and its
correction `piPart` [KauffmanLomonaco2006]. -/
theorem phiWord_eq_smul_add_piPart (A d c : ℂ) (w : List Bool) :
    phiWord A d c w = A ^ expSum w • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + piPart A d c w := by
  simp [piPart]

/-- The closure expression `A ^ expSum w * d ^ 2 + trace (piPart A d c w)`. -/
def bracketClosure (A d c : ℂ) (w : List Bool) : ℂ :=
  A ^ expSum w * d ^ 2 + Matrix.trace (piPart A d c w)

/-- The closure expression equals `trace (phiWord A d c w) + A ^ expSum w * (d ^ 2 - 2)`
[KauffmanLomonaco2006]. -/
theorem bracketClosure_eq_trace_add (A d c : ℂ) (w : List Bool) :
    bracketClosure A d c w
      = Matrix.trace (phiWord A d c w) + A ^ expSum w * (d ^ 2 - 2) := by
  unfold bracketClosure piPart
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp [Fintype.card_fin]
  ring

end Qatlib.Papers.AnyonicSpin06.MainResults.TemperleyLieb
