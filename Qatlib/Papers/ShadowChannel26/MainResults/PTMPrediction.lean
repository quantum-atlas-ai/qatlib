/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ShadowChannel26.MainResults.SourceModel
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign

@[expose] public section

/-!
# Pauli transfer matrix entries as mixed-state CSEU predictions

Section 3.2 of the paper (p. 8-9, lines 556-564) evaluates the classical-shadow prediction on the
mixed input `ρ_{p'} = (I + σ_{p'})/d` and the Pauli observable `O_p = σ_p`, and reads off the Pauli
transfer matrix entry `R_U(p,p')`. In the paper's formula this uses `tr σ_p = 0` for `p ≠ 1`,
which removes the contribution of the identity summand of `ρ_{p'}`.

This module records that computation for the `SourceModel` vocabulary: the real trace of
`σ_p U ((I + σ_q)/d) U†` is exactly `ptmEntry U p q`, provided `p` is a nonidentity Pauli word.

Boundary: only the entry identity is covered. No variance, sampling or estimation statement is
included, and the result is for `U` an arbitrary unitary; the `q = 1` case is included but not
specialized. The tracelessness input is
`Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign.trace_op_eq_zero_of_word_ne`
specialized to zero phase.

Paper: [arXiv:2606.13638v2](https://arxiv.org/abs/2606.13638v2), §3.2.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Papers.ShadowChannel26.MainResults.SourceModel

namespace Qatlib.Papers.ShadowChannel26.MainResults

/-- A nonidentity Pauli word has a nonidentity letter, so its register operator is traceless. -/
theorem trace_pauliWordOp_eq_zero {n : ℕ} (p : PauliWord n) (hp : p ≠ 1) :
    Matrix.trace (pauliWordOp n p) = 0 := by
  have hp' : ∃ i, p i ≠ Pauli1.I := by
    by_contra h
    push Not at h
    exact hp (funext h)
  have h := trace_op_eq_zero_of_word_ne n (⟨p, 0⟩ : PauliElem n) hp'
  simpa [op] using h

/-- The PTM entry `R_U(p,q)` is the mixed-state prediction on `(I + σ_q)/d` with observable
`σ_p`, for a nonidentity Pauli word `p` (§3.2). -/
theorem ptmEntry_eq_mixed_state_prediction {n : ℕ} (U : NOp n) (p q : PauliWord n)
    (hU : IsUnitary U) (hp : p ≠ 1) :
    ((pauliWordOp n p * U * (((2 : ℂ) ^ n)⁻¹ • (1 + pauliWordOp n q)) * Uᴴ).trace).re
      = ptmEntry U p q := by
  have hword : Matrix.trace (pauliWordOp n p) = 0 := trace_pauliWordOp_eq_zero p hp
  have hUU : U * Uᴴ = 1 := hU.2
  have htr : (pauliWordOp n p * U * Uᴴ).trace = 0 := by
    rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
    exact hword
  have hsplit : pauliWordOp n p * U * (1 + pauliWordOp n q) * Uᴴ
      = pauliWordOp n p * U * Uᴴ
        + pauliWordOp n p * U * pauliWordOp n q * Uᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  have hmain : (pauliWordOp n p * U * (((2 : ℂ) ^ n)⁻¹ • (1 + pauliWordOp n q)) * Uᴴ).trace
      = (pauliWordOp n p * U * pauliWordOp n q * Uᴴ).trace / (2 : ℂ) ^ n := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, hsplit, Matrix.trace_add, htr,
      zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hmain, ptmEntry]

end Qatlib.Papers.ShadowChannel26.MainResults
