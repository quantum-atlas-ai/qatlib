/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option backward.isDefEq.respectTransparency false

/-! DB-QITE circuit recursion for
"Role of Riemannian geometry in double-bracket quantum imaginary-time
evolution" (arXiv:2504.01065, 2025).

Equation (8) of the paper gives the recursive circuit synthesis of
DB-QITE:

`U_{k+1} = e^{i√s H} U_k e^{i√s |0⟩⟨0|} U_k† e^{-i√s H} U_k`,

obtained from the state recursion Equation (7)

`|ω_{k+1}⟩ = e^{i√s H} e^{i√s |ω_k⟩⟨ω_k|} e^{-i√s H} |ω_k⟩`

by pulling the rank-one projector `|ω_k⟩⟨ω_k| = U_k |0⟩⟨0| U_k†`
through the exponential.

- `outer_conj_mulVec`: the conjugated reference projector
  `U P₀ U†` is the outer product of the state `ψ = U |0⟩`.
- `exp_conj_unitary`: exponentials commute with unitary conjugation
  (`Matrix.exp_conj` specialised to `U⁻¹ = U†`).
- `dbqite_step_implements`: **the Eq. (8) circuit acting on the
  reference state `|e₀⟩` produces exactly the Eq. (7) state** — the
  correctness core of the compilation whose entangling-gate count is
  the main claim of the paper.

The paper states the recursions in prose (no theorem environment);
here `H` is an arbitrary Hamiltonian matrix (the experiments use
two-local Hamiltonians) and `t : ℂ` is the step scale (the paper's
`i√s_k`). No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.RiemannQITE25.MainResults.DBQITERecursion

open scoped Matrix
open Matrix NormedSpace

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The rank-one projector `|ψ⟩⟨ψ|` of a vector `ψ`. -/
def outer (ψ : n → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ψ i * starRingEnd ℂ (ψ j)

omit [Fintype n] [DecidableEq n] in
/-- Entrywise characterisation of the rank-one projector. -/
lemma outer_apply (ψ : n → ℂ) (i j : n) :
    outer ψ i j = ψ i * starRingEnd ℂ (ψ j) := rfl

/-- A unitary right inverse gives an invertible matrix: `U U† = 1`
forces `IsUnit U` via `|det U|² = 1`. -/
lemma unitary_isUnit (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) : IsUnit U := by
  have h1 : U.det * Uᴴ.det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  rw [Matrix.det_conjTranspose] at h1
  have hne : U.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  exact (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr hne)

/-- For a unitary `U` (in the sense `U U† = 1`) the ring inverse is
the adjoint: `U⁻¹ = U†`. -/
lemma unitary_inv (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) : U⁻¹ = Uᴴ := by
  have hdet : IsUnit U.det := by
    have h1 : U.det * Uᴴ.det = 1 := by
      rw [← Matrix.det_mul, hU, Matrix.det_one]
    rw [Matrix.det_conjTranspose] at h1
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  calc U⁻¹ = U⁻¹ * (U * Uᴴ) := by rw [hU, mul_one]
    _ = (U⁻¹ * U) * Uᴴ := (mul_assoc U⁻¹ U Uᴴ).symm
    _ = 1 * Uᴴ := by rw [Matrix.nonsing_inv_mul U hdet]
    _ = Uᴴ := one_mul Uᴴ

/-- Exponentials commute with unitary conjugation:
`exp (U A U†) = U (exp A) U†`. -/
theorem exp_conj_unitary (U A : Matrix n n ℂ) (hU : U * Uᴴ = 1) :
    NormedSpace.exp (U * A * Uᴴ) = U * NormedSpace.exp A * Uᴴ := by
  rw [← unitary_inv U hU]
  exact Matrix.exp_conj U A (unitary_isUnit U hU)

/-- The conjugated reference projector is the outer product of the
prepared state: `U |e₀⟩⟨e₀| U† = |ψ⟩⟨ψ|` with `ψ = U |e₀⟩`. -/
theorem outer_conj_mulVec (U : Matrix n n ℂ) (e₀ : n) :
    U * outer (Pi.single e₀ 1) * Uᴴ = outer (U *ᵥ (Pi.single e₀ 1)) := by
  ext i j
  simp [outer, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    Pi.single_apply, Finset.sum_ite_eq', mul_comm]

/-- **Eq. (8) implements Eq. (7)**: the DB-QITE circuit step
`e^{tH} U e^{tP₀} U† e^{-tH} U` acting on the reference state `|e₀⟩`
(with `P₀ = |e₀⟩⟨e₀|`) produces the state
`e^{tH} e^{t|ψ⟩⟨ψ|} e^{-tH} ψ` with `ψ = U |e₀⟩` — the correctness
core of the paper's Qrisp compilation, whose entangling-gate count is
the main claim. -/
theorem dbqite_step_implements (H U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (e₀ : n)
    (t : ℂ) :
    (NormedSpace.exp (t • H) * U * NormedSpace.exp (t • outer (Pi.single e₀ 1)) * Uᴴ
      * NormedSpace.exp (-t • H) * U) *ᵥ (Pi.single e₀ 1)
    = NormedSpace.exp (t • H) *ᵥ (NormedSpace.exp (t • outer (U *ᵥ (Pi.single e₀ 1))) *ᵥ
        (NormedSpace.exp (-t • H) *ᵥ (U *ᵥ (Pi.single e₀ 1)))) := by
  have hmid : U * NormedSpace.exp (t • outer (Pi.single e₀ 1)) * Uᴴ
      = NormedSpace.exp (t • outer (U *ᵥ (Pi.single e₀ 1))) := by
    have hc := exp_conj_unitary U (t • outer (Pi.single e₀ 1)) hU
    have hsm : t • (U * outer (Pi.single e₀ 1) * Uᴴ)
        = U * (t • outer (Pi.single e₀ 1)) * Uᴴ := by
      calc t • (U * outer (Pi.single e₀ 1) * Uᴴ)
          = t • (U * outer (Pi.single e₀ 1)) * Uᴴ := by rw [smul_mul_assoc]
        _ = U * (t • outer (Pi.single e₀ 1)) * Uᴴ := by rw [mul_smul_comm]
    calc U * NormedSpace.exp (t • outer (Pi.single e₀ 1)) * Uᴴ
        = NormedSpace.exp (U * (t • outer (Pi.single e₀ 1)) * Uᴴ) := hc.symm
      _ = NormedSpace.exp (t • (U * outer (Pi.single e₀ 1) * Uᴴ)) := by rw [hsm]
      _ = NormedSpace.exp (t • outer (U *ᵥ (Pi.single e₀ 1))) := by
            rw [outer_conj_mulVec U e₀]
  calc (NormedSpace.exp (t • H) * U * NormedSpace.exp (t • outer (Pi.single e₀ 1)) * Uᴴ
      * NormedSpace.exp (-t • H) * U) *ᵥ (Pi.single e₀ 1)
      = NormedSpace.exp (t • H) *ᵥ (U *ᵥ (NormedSpace.exp (t • outer (Pi.single e₀ 1)) *ᵥ
          (Uᴴ *ᵥ (NormedSpace.exp (-t • H) *ᵥ (U *ᵥ (Pi.single e₀ 1)))))) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = NormedSpace.exp (t • H) *ᵥ (NormedSpace.exp (t • outer (U *ᵥ (Pi.single e₀ 1))) *ᵥ
        (NormedSpace.exp (-t • H) *ᵥ (U *ᵥ (Pi.single e₀ 1)))) := by
        rw [show U *ᵥ (NormedSpace.exp (t • outer (Pi.single e₀ 1)) *ᵥ
              (Uᴴ *ᵥ (NormedSpace.exp (-t • H) *ᵥ (U *ᵥ (Pi.single e₀ 1)))))
            = NormedSpace.exp (t • outer (U *ᵥ (Pi.single e₀ 1))) *ᵥ
              (NormedSpace.exp (-t • H) *ᵥ (U *ᵥ (Pi.single e₀ 1))) from by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmid]]

end Qatlib.Papers.RiemannQITE25.MainResults.DBQITERecursion
