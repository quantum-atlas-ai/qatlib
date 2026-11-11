/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QSDPSolvers17.MainResults.Model.SdpInstance
import Qatlib.Concepts.MatrixWeights.WeightsCore

set_option backward.isDefEq.respectTransparency false

/-!
# Lower bound `Ω(√m)` for quantum-input SDP solvers (paper QSDPSolvers17,
Theorem 13, App. D.6)

Source: arXiv:1710.02581, Appendix D.6, pp. 26–27.

The proof constructs two families of SDP feasibility instances:

1. `A_j^- = 0`, `A_j^+ = |i*⟩⟨i*|` for all `j`; `a_{j*} = -1/2`, `a_j = 1/2` otherwise,
   `ε = 1/4`.  This instance is **infeasible**: any density matrix has `Tr(A X) ≥ 0`,
   contradicting `Tr(A_{j*} X) ≤ -1/2 + 1/4 = -1/4`.
2. The same `A_j`, with `a_j = 1/2` for all `j`, is **feasible**: the maximally mixed
   state `I/n` satisfies every constraint when `Tr(A_0) ≤ 1`.

For both families `B = r = 1` and `A_j^+/Tr(A_j^+) = |i*⟩⟨i*|` is the same state for
every `j`, so Oracle D.2 provides no information distinguishing the families; only
Oracle D.1 can help, and distinguishing amounts to Grover search for `j*`.  The Grover
lower bound `Ω(√m)` of [8] is kept as the explicit hypothesis `hGrover` (the reduction
step), while the instance construction, infeasibility of family 1, and feasibility of
family 2 are proved.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QSDPSolvers17.MainResults.LowerBound

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.QSDPSolvers17.MainResults.Model
open scoped ComplexOrder MatrixOrder BigOperators

variable {m n : ℕ}

/-- The maximally mixed state `I/n`. -/
noncomputable def maximallyMixed (n : ℕ) : Operator n :=
  ((n : ℝ)⁻¹) • (1 : Operator n)

/-- The maximally mixed state is a density matrix (for `n > 0`): positive semidefinite
and of trace `n · n⁻¹ = 1`. -/
theorem maximallyMixed_density {n : ℕ} (hn : 0 < n) :
    IsDensityOperator (maximallyMixed n) := by
  constructor
  · unfold maximallyMixed
    exact (Matrix.PosSemidef.one).smul (a := (n : ℝ)⁻¹) (by positivity)
  · unfold maximallyMixed
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    rw [Complex.real_smul]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    push_cast
    field_simp [hnC]

/-- Trace of `A` against the maximally mixed state: `Tr(A · I/n) = Tr(A)/n`. -/
theorem trace_mul_maximallyMixed (A : Operator n) :
    (Matrix.trace (A * maximallyMixed n)).re = (Matrix.trace A).re / n := by
  unfold maximallyMixed
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp [Complex.smul_re, smul_eq_mul]
  ring

/-- **Theorem 13, infeasible family.**  If all constraint matrices equal a PSD `A₀` and
`a_{j*} = -1/2`, then the relaxed region `S_{1/4}` is empty: every density matrix has
`Tr(A₀ X) ≥ 0 > -1/4`. -/
theorem instance_one_infeasible {m n : ℕ} (A0 : Operator n) (hA0 : A0.PosSemidef)
    (P : SdpInstance m n) (j0 : Fin m) (hA : ∀ j, P.A j = A0) (ha0 : P.a j0 = -1 / 2) :
    ¬ ∃ ρ, EpsFeasibleAt P (1 / 4) ρ := by
  rintro ⟨ρ, hρ, hcon⟩
  have h := hcon j0
  rw [hA j0, ha0] at h
  have hnonneg : 0 ≤ (Matrix.trace (A0 * ρ)).re := by
    have hm := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_trace_mul_mono n ρ
      (0 : Operator n) A0 hρ.1 (by rw [Matrix.le_iff]; simpa using hA0)
    rw [Matrix.mul_zero, Matrix.trace_zero, Matrix.trace_mul_comm ρ A0] at hm
    exact hm
  linarith

/-- **Theorem 13, feasible family.**  If all constraint matrices equal a PSD `A₀` with
`Tr(A₀) ≤ 1` and all `a_j = 1/2`, the maximally mixed state lies in `S_{1/4}`:
`Tr(A₀ I/n) = Tr(A₀)/n ≤ 1/2 ≤ 1/2 + 1/4`. -/
theorem instance_two_feasible {m n : ℕ} (hn : 2 ≤ n) (A0 : Operator n)
    (hA0 : A0.PosSemidef) (htr : (Matrix.trace A0).re ≤ 1)
    (P : SdpInstance m n) (hA : ∀ j, P.A j = A0) (ha : ∀ j, P.a j = 1 / 2) :
    ∃ ρ, EpsFeasibleAt P (1 / 4) ρ := by
  refine ⟨maximallyMixed n, maximallyMixed_density (by omega), fun j => ?_⟩
  rw [hA j, ha]
  rw [trace_mul_maximallyMixed]
  have hnR : (0 : ℝ) < n := by positivity
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (Matrix.trace A0).re / n ≤ 1 / n :=
    div_le_div_of_nonneg_right htr hnR.le
  have h2 : (1 : ℝ) / n ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hnR (by norm_num : (0 : ℝ) < 2)]
    linarith
  linarith

/-- **Oracle D.2 indistinguishability.**  When the prepared reduced states of two
instance families agree for every index `j` (as they do for the two families of
Theorem 13, both being `|i*⟩⟨i*|`), Oracle D.2 cannot distinguish them. -/
theorem oracle_d2_indistinguishable (state1 state2 : Fin m → Operator n) (A0 : Operator n)
    (h1 : ∀ j, state1 j = A0) (h2 : ∀ j, state2 j = A0) :
    ∀ j, state1 j = state2 j := by
  intro j
  rw [h1 j, h2 j]

/-- **Theorem 13 (lower bound for quantum SDP solvers)**, arXiv:1710.02581 App. D.6,
pp. 26–27.  There exist two SDP feasibility instances `P1, P2` with the same constraint
matrices (hence indistinguishable through Oracle D.2), where `P1` is infeasible at
`ε = 1/4` while `P2` is feasible; consequently any algorithm distinguishing them needs
at least `√m/4` queries to Oracle D.1.

The Grover reduction `Ω(√m)` (from [8]) enters as the explicit hypothesis `hGrover`:
any pair indistinguishable through D.2 with differing feasibility requires that many
D.1 queries. -/
theorem lower_bound_sqrt_m (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (A0 : Operator n) (hA0 : A0.PosSemidef) (htr : (Matrix.trace A0).re ≤ 1)
    (j0 : Fin m) (D1queries : SdpInstance m n → SdpInstance m n → ℝ)
    (hGrover : ∀ S1 S2 : SdpInstance m n, (∀ j, S1.A j = S2.A j) →
      (¬ ∃ ρ, EpsFeasibleAt S1 (1 / 4) ρ) → (∃ ρ, EpsFeasibleAt S2 (1 / 4) ρ) →
      Real.sqrt m / 4 ≤ D1queries S1 S2) :
    ∃ P1 P2 : SdpInstance m n,
      (∀ j, P1.A j = P2.A j) ∧
        (¬ ∃ ρ, EpsFeasibleAt P1 (1 / 4) ρ) ∧
        (∃ ρ, EpsFeasibleAt P2 (1 / 4) ρ) ∧
        Real.sqrt m / 4 ≤ D1queries P1 P2 := by
  let P1 : SdpInstance m n :=
    { A := fun _ => A0, a := fun j => if j = j0 then -1 / 2 else 1 / 2 }
  let P2 : SdpInstance m n :=
    { A := fun _ => A0, a := fun _ => 1 / 2 }
  have hA : ∀ j, P1.A j = P2.A j := fun j => rfl
  have hinf : ¬ ∃ ρ, EpsFeasibleAt P1 (1 / 4) ρ :=
    instance_one_infeasible A0 hA0 P1 j0 (fun j => rfl) (by simp [P1])
  have hfeas : ∃ ρ, EpsFeasibleAt P2 (1 / 4) ρ :=
    instance_two_feasible hn A0 hA0 htr P2 (fun j => rfl) (fun j => rfl)
  exact ⟨P1, P2, hA, hinf, hfeas, hGrover P1 P2 hA hinf hfeas⟩

end Qatlib.Papers.QSDPSolvers17.MainResults.LowerBound
