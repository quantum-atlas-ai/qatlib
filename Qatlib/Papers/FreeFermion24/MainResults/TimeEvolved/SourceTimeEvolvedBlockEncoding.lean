/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourceTimeEvolvedBlockEncoding

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.TimeEvolved

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

private theorem expIht_unitary {N s : ℕ} (h : SparseHermitian N s) (t : ℝ) :
    expIht h t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hdiag : Matrix.diagonal (fun i =>
      Complex.exp (Complex.I * (h.hermitian.eigenvalues i : ℂ) * (t : ℂ))) ∈
      Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    change starRingEnd ℂ (Complex.exp (Complex.I *
      (h.hermitian.eigenvalues i : ℂ) * (t : ℂ))) *
        Complex.exp (Complex.I * (h.hermitian.eigenvalues i : ℂ) * (t : ℂ)) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_mul]
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (Unitary.star_mem h.hermitian.eigenvectorUnitary.property) hdiag)
    h.hermitian.eigenvectorUnitary.property

/-- Exact unitary conjugation preserves the operator-norm approximation error.
This is a matrix identity; it includes no implementation or resource bound. -/
theorem timeEvolved_error {N s : ℕ} (h : SparseHermitian N s)
    (M A : Matrix (Fin N) (Fin N) ℂ) (t₁ t₂ : ℝ) :
    ‖timeEvolvedM2 h M t₁ t₂ - timeEvolvedM2 h A t₁ t₂‖ = ‖M - A‖ := by
  have heq : timeEvolvedM2 h M t₁ t₂ - timeEvolvedM2 h A t₁ t₂ =
      expIht h t₁ * (M - A) * expIht h (-t₂) := by
    simp [timeEvolvedM2, mul_sub, sub_mul]
  rw [heq, CStarRing.norm_mul_mem_unitary _ (expIht_unitary h (-t₂)),
    CStarRing.norm_mem_unitary_mul _ (expIht_unitary h t₁)]

private theorem blockCorner_mul_left {a N : ℕ}
    (L : Matrix (Fin N) (Fin N) ℂ)
    (U : Matrix (Fin a × Fin N) (Fin a × Fin N) ℂ) (j : Fin a) :
    BlockCorner (TensorGate (1 : Matrix (Fin a) (Fin a) ℂ) L * U) j =
      L * BlockCorner U j := by
  ext x y
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply]

private theorem blockCorner_mul_right {a N : ℕ}
    (U : Matrix (Fin a × Fin N) (Fin a × Fin N) ℂ)
    (R : Matrix (Fin N) (Fin N) ℂ) (j : Fin a) :
    BlockCorner (U * TensorGate (1 : Matrix (Fin a) (Fin a) ℂ) R) j =
      BlockCorner U j * R := by
  ext x y
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
    Matrix.one_apply]

/-- The logarithmic factor `log^{5/2}(α|t|/ε)` of Theorem 11 (arXiv:2409.04550, p. 7);
the `max … 1` makes it total. -/
def thm11LogFactor (α t ε : ℝ) : ℝ :=
  Real.rpow (Real.log (max (α * |t| / ε) 1)) (5 / 2 : ℝ)

/-- The oracle-call count `D(α, ε, t₁, t₂) = O(s(|t₁|+|t₂|) + log(12α(|t₁|+|t₂|)/(|t₁|ε))
+ log(12α(|t₁|+|t₂|)/(|t₂|ε)))` of Theorem 17 (arXiv:2409.04550, Eq. (E2)). -/
def thm17OracleCalls (s α ε t₁ t₂ : ℝ) : ℝ :=
  s * (|t₁| + |t₂|) +
    Real.log (12 * α * (|t₁| + |t₂|) / (|t₁| * ε)) +
    Real.log (12 * α * (|t₁| + |t₂|) / (|t₂| * ε))

/-- The logarithmic factor `log^{5/2}(2αs²(|t₁|+|t₂|)/ε)` of Theorem 17
(arXiv:2409.04550, p. 14); the `max … 1` makes it total. -/
def thm17LogFactor (s α ε t₁ t₂ : ℝ) : ℝ :=
  Real.rpow (Real.log (max (2 * α * s ^ 2 * (|t₁| + |t₂|) / ε) 1)) (5 / 2 : ℝ)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem11_blockEncoding_timeEvolvedM`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem11_blockEncoding_timeEvolvedM_statement
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε εM t : ℝ) (na : ℕ)
    (B_M : ControlledBlockEncoding (2 ^ n) M α εM)
    (hα : 0 < α) (hε : 0 < ε) : Prop :=
    ∃ B : ControlledBlockEncoding (2 ^ n) (timeEvolvedM h M t) α (ε + εM),
      B.m = n + B_M.m + 10 ∧
      B.cost.usesOfUM = 1 ∧
      BigO B.cost.oracleCalls (|t| + Real.log (α / ε)) ∧
      BigO B.cost.gates
        ((n : ℝ) * |t| + Real.log (α / ε) +
          (|t| + Real.log (α / ε)) * ((n : ℝ) + thm11LogFactor α t ε)) ∧
      BigO B.cost.ancillaryQubits ((na : ℝ) + thm11LogFactor α t ε)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem17_timeEvolvedM2_resources`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem17_timeEvolvedM2_resources_statement
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (α ε εM t₁ t₂ : ℝ) (na : ℕ)
    (B_M : ControlledBlockEncoding (2 ^ n) M α εM)
    (hα : 0 < α) (hε : 0 < ε) : Prop :=
    ∃ B : ControlledBlockEncoding (2 ^ n) (timeEvolvedM2 h M t₁ t₂) α (ε + εM),
      B.m = n + B_M.m + 10 ∧
      B.cost.usesOfUM = 1 ∧
      BigO B.cost.oracleCalls (thm17OracleCalls (s : ℝ) α ε t₁ t₂) ∧
      BigO B.cost.gates
        (((n : ℝ) + 3) *
          ((s : ℝ) * (|t₁| + |t₂|) +
            Real.log (2 * α * (|t₁| + |t₂|) / (|t₁| * ε)) +
            Real.log (2 * α * (|t₁| + |t₂|) / (|t₂| * ε)) +
            thm17OracleCalls (s : ℝ) α ε t₁ t₂ *
              ((n : ℝ) + thm17LogFactor (s : ℝ) α ε t₁ t₂))) ∧
      BigO B.cost.ancillaryQubits ((na : ℝ) + thm17LogFactor (s : ℝ) α ε t₁ t₂)

end Qatlib.Papers.FreeFermion24.MainResults.TimeEvolved
