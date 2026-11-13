/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# RegressionSolvers

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Regression

/-- Euclidean (`ℓ²`) norm of a complex vector. -/
def l2norm {N : Type*} [Fintype N] (v : N → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (v i))

/-- Matrix-vector product. -/
def matVecMul {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (b : Fin N → ℂ) : Fin M → ℂ :=
  fun i => ∑ j, A i j * b j

/-- Normalization `v / ‖v‖`. -/
def normalize {N : Type*} [Fintype N] (v : N → ℂ) : N → ℂ :=
  fun i => v i / (l2norm v : ℂ)

/-- Existence of an `(α, ε)` block encoding of `A` on a free ancilla register. -/
def HasBlockEncodingRect {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) (α ε : ℝ) : Prop :=
  ∃ (k : ℕ) (U : Matrix (Fin k) (Fin k) ℂ)
      (L : Matrix (Fin k) O ℂ) (R : Matrix (Fin k) I ℂ),
    BlockEncoding A U L R α ε

private theorem l2norm_zero {N : Type*} [Fintype N] :
    l2norm (fun _ : N => (0 : ℂ)) = 0 := by
  unfold l2norm
  simp

/- ## c024 — Theorem 35 -/

/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem35_wls_solver`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem35_wls_solver_statement
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (b : Fin M → ℂ)
    (Realizes : (Fin N → ℂ) → ℝ → Prop)
    (ε κA μ η : ℝ)
    (hκA : 0 < κA) (hμ : 0 < μ) (hη : η < 1) (hε : 0 < ε)
    (hApinv : A * Apinv * A = A) : Prop :=
    ∃ (sol : Fin N → ℂ) (cost C d : ℝ), Realizes sol cost ∧ 0 < C ∧ 0 < d ∧
      l2norm (fun i => sol i - normalize (matVecMul Apinv b) i) ≤ ε ∧
      cost ≤ C * (κA * μ / Real.sqrt (1 - η) *
        (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)


/- ## c025 — Theorem 36 -/

/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem36_gls_solver_block_encodings`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem36_gls_solver_block_encodings_statement
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (ytilde : Fin M → ℂ)
    (Realizes : (Fin N → ℂ) → ℝ → Prop)
    (ε αX αΩ TX TΩ Ty κA κΩ η : ℝ)
    (hκA : 0 < κA) (hκΩ : 0 < κΩ) (hη : η < 1) (hε : 0 < ε)
    (hαX : 0 < αX) (hαΩ : 0 < αΩ) (hTX : 0 ≤ TX) (hTΩ : 0 ≤ TΩ) (hTy : 0 ≤ Ty)
    (hApinv : A * Apinv * A = A) : Prop :=
    ∃ (sol : Fin N → ℂ) (cost C : ℝ), Realizes sol cost ∧ 0 < C ∧
      l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
      cost ≤ C * (κA * Real.log κA / Real.sqrt (1 - η) *
        ((Real.sqrt κΩ * αX * TX + αΩ * TΩ) * (Real.log (κA / ε)) ^ 3 +
          Real.sqrt κΩ * Ty))


/- ## c026 — Corollary 37 -/

/-- **Statement only — not proved in Qatlib.** Resource specification for `cor37_wls_alternate_input`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def cor37_wls_alternate_input_statement
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (y : Fin M → ℂ)
    (Realizes : (Fin N → ℂ) → ℝ → Prop)
    (ε κA wmax μX η sXr sXc Ty : ℝ)
    (hκA : 0 < κA) (hwmax : 0 < wmax) (hμX : 0 < μX) (hη : η < 1) (hε : 0 < ε)
    (hsr : 0 ≤ sXr) (hsc : 0 ≤ sXc) (hTy : 0 ≤ Ty)
    (hApinv : A * Apinv * A = A) : Prop :=
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), Realizes sol cost ∧ 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv y) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt wmax / Real.sqrt (1 - η) * μX *
          (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)) ∧
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), Realizes sol cost ∧ 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv y) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt wmax / Real.sqrt (1 - η) *
          (Real.sqrt (sXr * sXc) + Ty) * (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d))


/- ## c027 — Corollary 38 -/

/-- **Statement only — not proved in Qatlib.** Resource specification for `cor38_gls_alternate_input`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def cor38_gls_alternate_input_statement
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (ytilde : Fin M → ℂ)
    (Realizes : (Fin N → ℂ) → ℝ → Prop)
    (ε αX αΩ TX TΩ Ty κA κΩ η : ℝ)
    (hκA : 0 < κA) (hκΩ : 0 < κΩ) (hη : η < 1) (hε : 0 < ε)
    (hαX : 0 < αX) (hαΩ : 0 < αΩ) (hTX : 0 ≤ TX) (hTΩ : 0 ≤ TΩ) (hTy : 0 ≤ Ty)
    (hApinv : A * Apinv * A = A) : Prop :=
    ∃ (sol : Fin N → ℂ) (cost C d : ℝ), Realizes sol cost ∧ 0 < C ∧ 0 < d ∧
      l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
      cost ≤ C * (κA * Real.sqrt κΩ / Real.sqrt (1 - η) *
        (αX * TX + αΩ * κΩ * TΩ + Ty) * (Real.log (1 / ε)) ^ d)


/- ## c028 — Corollary 39 -/

/-- **Statement only — not proved in Qatlib.** Resource specification for `cor39_gls_data_structure_or_sparse`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def cor39_gls_data_structure_or_sparse_statement
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (ytilde : Fin M → ℂ)
    (Realizes : (Fin N → ℂ) → ℝ → Prop)
    (ε κA κΩ η μX μΩ sXr sXc sΩ : ℝ)
    (hκA : 0 < κA) (hκΩ : 0 < κΩ) (hη : η < 1) (hε : 0 < ε)
    (hμX : 0 < μX) (hμΩ : 0 < μΩ) (hsr : 0 ≤ sXr) (hsc : 0 ≤ sXc) (hsΩ : 0 ≤ sΩ)
    (hApinv : A * Apinv * A = A) : Prop :=
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), Realizes sol cost ∧ 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt κΩ / Real.sqrt (1 - η) * (μX + μΩ * κΩ) *
          (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)) ∧
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), Realizes sol cost ∧ 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt κΩ / Real.sqrt (1 - η) *
          (Real.sqrt (sXr * sXc) + sΩ * κΩ) *
          (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d))


end Qatlib.Papers.BlockEncMatPw18.MainResults.Regression
