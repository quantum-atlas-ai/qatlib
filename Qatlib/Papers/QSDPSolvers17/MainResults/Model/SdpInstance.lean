/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MatrixWeights.WeightsCore

set_option backward.isDefEq.respectTransparency false

/-!
# SDP feasibility instances (paper QSDPSolvers17, Definition 1 / App. A)

Source: arXiv:1710.02581, Appendix A, Definition 1 (p. 14): a feasibility instance is
a list of Hermitian matrices `A_1, …, A_m` with `-I ≤ A_i ≤ I` together with real numbers
`a_1, …, a_m`.  The feasible region `S_ε` consists of all density matrices `X` with
`Tr(A_i X) ≤ a_i + ε`, while `S_0` is the exact-feasibility region.

This file only fixes the vocabulary shared by all claims: the instance record, `S_0`
and `S_ε`, and the matrix-multiplicative-weights gain matrix `M_j = (I - A_j) / 2`
used in the proof of Theorem 3 (App. A).  No algorithmic content is asserted here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QSDPSolvers17.MainResults.Model

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped ComplexOrder MatrixOrder

/-- An SDP feasibility instance: Hermitian matrices `A i` and reals `a i`.
The spectral hypothesis `-I ≤ A i ≤ I` is carried by the theorems that need it. -/
structure SdpInstance (m D : ℕ) where
  /-- The constraint matrices. -/
  A : Fin m → Operator D
  /-- The constraint right-hand sides. -/
  a : Fin m → ℝ

variable {m D : ℕ}

/-- Exact feasibility `S_0`: a density matrix satisfying every constraint exactly. -/
def FeasibleAt (P : SdpInstance m D) (ρ : Operator D) : Prop :=
  IsDensityOperator ρ ∧ ∀ i : Fin m, (Matrix.trace (P.A i * ρ)).re ≤ P.a i

/-- Approximate feasibility `S_ε`: a density matrix within `ε` of every constraint. -/
def EpsFeasibleAt (P : SdpInstance m D) (ε : ℝ) (ρ : Operator D) : Prop :=
  IsDensityOperator ρ ∧ ∀ i : Fin m, (Matrix.trace (P.A i * ρ)).re ≤ P.a i + ε

/-- The exact-feasibility region `S_0`. -/
def S0 (P : SdpInstance m D) : Set (Operator D) := {ρ | FeasibleAt P ρ}

/-- The approximate-feasibility region `S_ε`. -/
def Seps (P : SdpInstance m D) (ε : ℝ) : Set (Operator D) := {ρ | EpsFeasibleAt P ε ρ}

/-- `S_0 ⊆ S_ε` for `ε ≥ 0`; this is the monotonicity used implicitly throughout App. A. -/
theorem S0_subset_Seps (P : SdpInstance m D) {ε : ℝ} (hε : 0 ≤ ε) :
    S0 P ⊆ Seps P ε := by
  intro ρ hρ
  refine ⟨hρ.1, fun i => ?_⟩
  exact le_trans (hρ.2 i) (le_add_of_nonneg_right hε)

/-- The matrix-multiplicative-weights gain matrix `M_j = (I - A_j) / 2`. -/
noncomputable def SdpInstance.gain (P : SdpInstance m D) (j : Fin m) : Operator D :=
  (1 / 2 : ℝ) • ((1 : Operator D) - P.A j)

/-- The gain matrix is positive semidefinite when `A_j ≤ I` (App. A, proof of Theorem 3). -/
theorem gain_posSemidef (P : SdpInstance m D) {j : Fin m} (hA : P.A j ≤ 1) :
    (P.gain j).PosSemidef := by
  have h : ((1 : Operator D) - P.A j).PosSemidef := Matrix.le_iff.mp hA
  exact h.smul (a := (1 / 2 : ℝ)) (by norm_num)

/-- The gain matrix is at most the identity when `-I ≤ A_j` (App. A, proof of Theorem 3). -/
theorem gain_le_one (P : SdpInstance m D) {j : Fin m} (hA : (-1 : Operator D) ≤ P.A j) :
    P.gain j ≤ 1 := by
  rw [Matrix.le_iff]
  have h : (P.A j - (-1 : Operator D)).PosSemidef := Matrix.le_iff.mp hA
  have hps : ((1 / 2 : ℝ) • (P.A j - (-1 : Operator D))).PosSemidef :=
    h.smul (a := (1 / 2 : ℝ)) (by norm_num)
  convert hps using 1
  ext i k
  simp only [SdpInstance.gain, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.neg_apply]
  by_cases h : i = k
  · simp [h]
    ring
  · simp [h]

/-- Trace identity for the gain matrix: `Tr(M_j ρ) = (Tr ρ - Tr(A_j ρ)) / 2`. -/
theorem trace_gain_mul (P : SdpInstance m D) (j : Fin m) (ρ : Operator D) :
    (Matrix.trace (P.gain j * ρ)).re =
      (1 / 2) * ((Matrix.trace ρ).re - (Matrix.trace (P.A j * ρ)).re) := by
  rw [SdpInstance.gain, Matrix.smul_mul, Matrix.trace_smul]
  simp only [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, Complex.smul_re, smul_eq_mul,
    Complex.sub_re]

/-- For a density matrix `ρ` and gain matrix `M_j`, `Tr(M_j ρ)` is nonnegative:
`Tr ρ = 1` and `Tr(A_j ρ) ≤ 1` follow from `A_j ≤ I`. -/
theorem trace_gain_mul_nonneg (P : SdpInstance m D) {j : Fin m}
    (hA : P.A j ≤ 1) {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    0 ≤ (Matrix.trace (P.gain j * ρ)).re := by
  have hM : (P.gain j).PosSemidef := gain_posSemidef P hA
  -- `Tr(M ρ) ≥ 0` because both factors are positive semidefinite.
  have h := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_trace_mul_mono D ρ (0 : Operator D) (P.gain j)
    hρ.1 (by rw [Matrix.le_iff]; simpa using hM)
  rw [Matrix.mul_zero, Matrix.trace_zero, Matrix.trace_mul_comm ρ (P.gain j)] at h
  exact h

/-- Upper bound `Tr(M_j ρ) ≤ 1` for a density matrix, when `M_j ≤ I`.
This is the step used in App. A to derive `a_j ≥ -1` from feasibility of `ρ*`. -/
theorem trace_gain_mul_le_one (P : SdpInstance m D) {j : Fin m}
    (hA : (-1 : Operator D) ≤ P.A j) {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    (Matrix.trace (P.gain j * ρ)).re ≤ 1 := by
  have hM : P.gain j ≤ 1 := gain_le_one P hA
  have h := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_trace_mul_mono D ρ (P.gain j) (1 : Operator D)
    hρ.1 hM
  rw [Matrix.mul_one, hρ.2, Matrix.trace_mul_comm ρ (P.gain j)] at h
  simpa using h

end Qatlib.Papers.QSDPSolvers17.MainResults.Model
