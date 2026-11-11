/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Symmetric QSP in real arithmetic: the `SU(2) ↔ S²` identification and the `SO(3)` recurrence

Paper: Dong–Lin–Ni–Wang, *Robust iterative method for symmetric quantum signal
processing in all parameter regimes*, arXiv:2307.12468v1 (fixed version).

This file formalises **Claim c003** (`IterativeQSP23.MainResults`): §3.3, Eqs
(3.9)–(3.11), together with the derivation in Appendix A (Eqs (A.1)–(A.7)).

* `symMat a d α` is the symmetric QSP matrix `U = [[a+id, iα],[iα, a−id]]` of
  Eq. (3.9), with `a = p`, `d = g`, `α = √(1−x²)·q` (all real).
* `symMat_det` shows `det U = a² + d² + α²`, hence `U` is a unit-determinant
  (special unitary) matrix **iff** the vector `V = (p, g, √(1−x²)q)` lies on the
  unit sphere `S² ⊂ ℝ³` — the `SU(2) ↔ S²` identification of Eq. (3.9).
* `symMat_rotation_step` is the recurrence Eq. (3.10) / (A.4):
  appending one symmetric phase `φ_k` and conjugating by the signal matrix
  `W(x)` acts on the vector `V` by the interleaved `SO(3)` rotation
  `Rz(2φ_k) · Rx(2 arccos x)`, with `Rz`, `Rx` exactly the matrices of Eq.
  (3.11)/(A.5).

The signal matrix `W(x)` and the phase rotation `e^{iφZ}` are reused from the
Frozen concept `QuantumAlgorithm.Concepts.LcuQsvtApprox.PhaseRecovery.SignalModel`
(`SignalMatrix`, `PhaseRotation`); the bridge is `SignalMatrix_eq` below.
-/

open Matrix
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.IterativeQSP23.MainResults.SymmetricQSPReal

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
  (SignalMatrix PhaseRotation phaseRotation_apply)

/-! ## The symmetric-form matrix and the associated `S²` vector -/

/-- Eq. (3.9): the symmetric QSP matrix `U = [[p+ig, i√(1−x²)q],[i√(1−x²)q, p−ig]]`,
written with real parameters `a = p`, `d = g`, `α = √(1−x²)q`. -/
def symMat (a d α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ) + Complex.I * (d : ℂ), Complex.I * (α : ℂ);
     Complex.I * (α : ℂ), (a : ℂ) - Complex.I * (d : ℂ)]

/-- Eq. (3.9): the real vector `V = (p, g, √(1−x²)q) ∈ ℝ³` attached to `symMat`. -/
def symVec (a d α : ℝ) : Fin 3 → ℝ := ![a, d, α]

/-- Bridge to the Frozen signal model: `SignalMatrix x` is the paper's
`W(x) = e^{i arccos(x) X} = [[x, i√(1−x²)],[i√(1−x²), x]]`. -/
theorem SignalMatrix_eq (x : ℝ) :
    SignalMatrix x = !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I;
      (Real.sqrt (1 - x ^ 2) : ℂ) * Complex.I, (x : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SignalMatrix]

/-- Eq. (3.9), determinant side: `det U = p² + g² + (1−x²)q² = ‖V‖²`. -/
theorem symMat_det (a d α : ℝ) :
    (symMat a d α).det = ((a ^ 2 + d ^ 2 + α ^ 2 : ℝ) : ℂ) := by
  rw [symMat, Matrix.det_fin_two_of]
  push_cast
  ring_nf
  simp only [Complex.I_sq, Complex.I_mul_I, Complex.I_pow_three]
  ring

/-- The squared Euclidean norm of `V = symVec a d α` is `a² + d² + α²`. -/
theorem symVec_normSq (a d α : ℝ) :
    (symVec a d α 0) ^ 2 + (symVec a d α 1) ^ 2 + (symVec a d α 2) ^ 2
      = a ^ 2 + d ^ 2 + α ^ 2 := by
  simp [symVec]

/-- **Eq. (3.9), the `SU(2) ↔ S²` identification.** A symmetric QSP matrix has
unit determinant (i.e. is special unitary) exactly when its associated vector
`V = (p, g, √(1−x²)q)` lies on the unit sphere `S² ⊂ ℝ³`. -/
theorem symMat_det_one_iff_vec_unit (a d α : ℝ) :
    (symMat a d α).det = 1 ↔
      (symVec a d α 0) ^ 2 + (symVec a d α 1) ^ 2 + (symVec a d α 2) ^ 2 = 1 := by
  rw [symMat_det, symVec_normSq]
  constructor
  · intro h
    have h' : a ^ 2 + d ^ 2 + α ^ 2 = 1 := by
      exact_mod_cast h
    exact h'
  · intro h
    rw [h]; push_cast; ring

/-! ## The `SO(3)` rotation matrices of Eqs. (3.11) / (A.5) -/

/-- Eq. (3.11): `Rz(2φ)` acting on the `(p, g, α)` coordinates. -/
def Rz (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos (2 * φ), -Real.sin (2 * φ), 0;
     Real.sin (2 * φ), Real.cos (2 * φ), 0;
     0, 0, 1]

/-- Eq. (3.11): `Rx(2θ)` acting on the `(p, g, α)` coordinates. -/
def Rx (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos (2 * θ), 0, -Real.sin (2 * θ);
     0, 1, 0;
     Real.sin (2 * θ), 0, Real.cos (2 * θ)]

/-! ## Conjugating a symmetric matrix by one phase and one signal matrix -/

/-- `W(x) · M · W(x)` keeps the symmetric form; on `(a,d,α)` it acts by the
`Rx(2 arccos x)` factor of the recurrence (the `θ = arccos x` case of (3.11)).

Paper: arXiv:2307.12468v1, §3.3 / Appendix A, Eq. (A.1)–(A.3)
(the `W(x)·U·W(x)` conjugation step).  The proof expands
`W = [[x, iβ],[iβ, x]]` with `β = √(1−x²)`, multiplies twice, and collects the
symmetric form using `β² = 1−x²`. -/
theorem signal_sym_signal (a d α x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    SignalMatrix x * symMat a d α * SignalMatrix x
      = symMat ((2 * x ^ 2 - 1) * a - 2 * x * Real.sqrt (1 - x ^ 2) * α) d
               (2 * x * Real.sqrt (1 - x ^ 2) * a + (2 * x ^ 2 - 1) * α) := by
  have hβ : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have hβC : ((Real.sqrt (1 - x ^ 2) : ℂ)) ^ 2 = 1 - (x : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, hβ]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SignalMatrix_eq, symMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    push_cast <;>
    ring_nf <;>
    rw [hβC] <;>
    ring_nf <;>
    simp [Complex.I_pow_three] <;>
    ring

/-- The product `e^{iφ}·e^{iφ} = e^{i(2φ)}` of scalar phase factors. -/
theorem exp_phase_sq (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I)
      = Complex.exp (((2 * φ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  push_cast
  ring_nf

/-- The scalar phase factors cancel: `e^{iφ}·e^{−iφ} = 1`. -/
theorem exp_phase_mul_inv (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp ((-(φ : ℂ)) * Complex.I) = 1 := by
  rw [← Complex.exp_add]
  rw [show (φ : ℂ) * Complex.I + (-(φ : ℂ)) * Complex.I = 0 by ring]
  exact Complex.exp_zero

/-- `P(φ) · M · P(φ)` with `P(φ) = e^{iφZ}` acts on `(a,d,α)` by the `Rz(2φ)`
factor of the recurrence (Eq. (3.11), `α` unchanged).

Paper: arXiv:2307.12468v1, §3.3 / Appendix A, Eq. (A.4)–(A.5)
(the `e^{iφZ}·U·e^{iφZ}` step, i.e. the `Rz(2φ)` rotation).  The proof unfolds
`e^{iφZ} = diag(e^{iφ}, e^{−iφ})`, multiplies the diagonal factors on both
sides, and uses `e^{2iφ} = cos(2φ) + i sin(2φ)`. -/
theorem phase_sym_phase (a d α φ : ℝ) :
    PhaseRotation φ * symMat a d α * PhaseRotation φ
      = symMat (a * Real.cos (2 * φ) - d * Real.sin (2 * φ))
               (a * Real.sin (2 * φ) + d * Real.cos (2 * φ)) α := by
  have hneg : Complex.exp (-(↑φ * Complex.I)) =
      (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
    rw [show -(↑φ * Complex.I) = ((-φ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have htrig : Complex.sin (↑φ) ^ 2 = 1 - Complex.cos (↑φ) ^ 2 := by
    linear_combination Complex.cos_sq_add_sin_sq (↑φ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PhaseRotation, symMat, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.exp_ofReal_mul_I, hneg] <;>
    ring_nf <;>
    simp only [show (↑φ * 2 : ℂ) = 2 * (↑φ : ℂ) by ring,
      Complex.cos_two_mul', Complex.sin_two_mul, Complex.I_sq, Complex.I_pow_three, htrig] <;>
    all_goals
      try linear_combination 2 * Complex.cos_sq_add_sin_sq (↑φ)
      ring_nf

/-! ## The `Rz · Rx` action on the vector, in components -/

/-- Componentwise form of `Rx(2 arccos x)` applied to `V = (a,d,α)`:
`(a,d,α) ↦ ((2x²−1)a − 2x√(1−x²)α, d, 2x√(1−x²)a + (2x²−1)α)`
(using `cos(2θ) = 2x²−1`, `sin(2θ) = 2x√(1−x²)` for `θ = arccos x`). -/
theorem rx_arccos_components (a d α x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    (Rx (Real.arccos x)).mulVec (symVec a d α)
      = ![ (2 * x ^ 2 - 1) * a - 2 * x * Real.sqrt (1 - x ^ 2) * α,
           d,
           2 * x * Real.sqrt (1 - x ^ 2) * a + (2 * x ^ 2 - 1) * α ] := by
  ext i
  fin_cases i <;>
    simp [Rx, symVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.cos_two_mul, Real.sin_two_mul, Real.cos_arccos hx1 hx2,
      Real.sin_arccos] <;>
    ring_nf <;>
    simp

/-- Componentwise form of the full step `Rz(2φ) · Rx(2 arccos x)` on
`V = (a,d,α)` (Eq. (3.10)/(A.4)). -/
theorem rz_rx_components (a d α x φ : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    (Rz φ).mulVec ((Rx (Real.arccos x)).mulVec (symVec a d α))
      = ![ ((2 * x ^ 2 - 1) * a - 2 * x * Real.sqrt (1 - x ^ 2) * α) * Real.cos (2 * φ)
             - d * Real.sin (2 * φ),
           ((2 * x ^ 2 - 1) * a - 2 * x * Real.sqrt (1 - x ^ 2) * α) * Real.sin (2 * φ)
             + d * Real.cos (2 * φ),
           2 * x * Real.sqrt (1 - x ^ 2) * a + (2 * x ^ 2 - 1) * α ] := by
  rw [rx_arccos_components a d α x hx1 hx2]
  ext i
  fin_cases i <;>
    simp [Rz, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring_nf

/-! ## The main recurrence, Eq. (3.10) / (A.4) -/

/-- **Eq. (3.10) / (A.4), the real-arithmetic recurrence.** If the truncated
symmetric QSP matrix is `symMat` with vector `V = (a,d,α)`, then appending the
phase `φ` and conjugating by the signal matrix `W(x)` produces the symmetric
matrix whose vector is `Rz(2φ) · Rx(2 arccos x) · V`, i.e. the matrix
multiplication of symmetric QSP is equivalent to interleaved `SO(3)` rotations. -/
theorem symMat_rotation_step (a d α x φ : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    PhaseRotation φ * SignalMatrix x * symMat a d α * SignalMatrix x * PhaseRotation φ
      = symMat
          (((Rz φ).mulVec ((Rx (Real.arccos x)).mulVec (symVec a d α))) 0)
          (((Rz φ).mulVec ((Rx (Real.arccos x)).mulVec (symVec a d α))) 1)
          (((Rz φ).mulVec ((Rx (Real.arccos x)).mulVec (symVec a d α))) 2) := by
  have hassoc :
      PhaseRotation φ * SignalMatrix x * symMat a d α * SignalMatrix x * PhaseRotation φ
        = PhaseRotation φ *
            (SignalMatrix x * symMat a d α * SignalMatrix x) * PhaseRotation φ := by
    simp only [mul_assoc]
  rw [hassoc, signal_sym_signal a d α x hx1 hx2, phase_sym_phase]
  rw [rz_rx_components a d α x φ hx1 hx2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

end Qatlib.Papers.IterativeQSP23.MainResults.SymmetricQSPReal
