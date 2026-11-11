/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Normed

set_option backward.isDefEq.respectTransparency false

/-!
# ExponentialAdvantage — c001 of SteadyState20

Fixed source: arXiv:2008.07133v2 (Quantum **5**, 420 (2021)), Abstract and Section 1,
and the complexity summary of Section 3.1, p. 7:

> “Here, we develop an efficient quantum algorithm for the direct estimation of averaged
> expectation values of observables on the nonequilibrium steady state, thus bypassing the
> time integration of the master equation. The algorithm encodes the vectorized
> representation of the density matrix on a quantum register, and makes use of quantum
> phase estimation to approximate the eigenvector associated to the zero eigenvalue of the
> generator of the system dynamics. … Away from critical points, where the Liouvillian
> gap scales as a power law of the system size, the quantum algorithm performs with
> exponential advantage compared to exact diagonalization.”

Formalisation:

* `classicalCost N = 2^N` is the exponential cost of exact diagonalization of the
  (vectorized) Liouvillian: the vectorized density matrix has dimension `4^N` and dense
  diagonalisation is cubic in that dimension, so `2^N` is a lower-bound proxy for the
  exponential classical scaling.  This is the modelling choice for the classical side of
  the comparison (the paper does not fix a precise classical cost model).
* `registerQubits N = 2N + 1` is the qubit count of the second register: `2N` qubits for
  the vectorized density matrix of an `N`-spin system plus one ancilla for the
  `|0⟩`/`|1⟩` block label (paper Sec. 2, p. 3).
* `polynomial_lt_exponential_eventually` is the analytic separation: a polynomial
  `C (N+1)^k` is eventually smaller than `2^N` (Mathlib's
  `isLittleO_pow_const_const_pow_of_one_lt`).
* `main_result_exponential_advantage` combines it with a polynomial gate-cost bound
  (paper Eq. (13), formalised in `MainResults.GateCost`) to obtain the paper's
  exponential-advantage statement: whenever the quantum gate count is polynomial in `N`,
  it is eventually strictly below the exact-diagonalisation cost `2^N`.
* The `O(1)` repetition guarantee and the QPE register-size condition of the paper are
  formalised in the sibling paper-layer files
  `...MainResults.SuccessProbability.SourceSuccessProbability` (claim c003) and
  `...MainResults.PhaseEstimationError.SourcePhaseEstimationError` (claim c004); this file
  does not duplicate them.

Boundary: this file formalises the quantitative separation and the assembly of the
guarantee.  It does not formalise the QPE circuit construction itself (state preparation
`P`, controlled-`U^{2^j}` oracles); the circuit-level zero-phase mass is the Frozen theorem
`QuantumAlgorithm.Concepts.SpectralFilter.ZeroPhaseFilter.degenerate_detection_mass`,
and the GKSL dynamics interface is `QuantumAlgorithm.Concepts.GkslBridge.GkslBridge`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SteadyState20.MainResults.ExponentialAdvantage

/-- Classical exact-diagonalization cost proxy: exponential in the system size `N`.
The vectorized Liouvillian acts on a space of dimension `4^N`; we use `2^N` as the
(conservative, still exponential) classical lower bound. -/
def classicalCost (N : ℕ) : ℝ := (2 : ℝ) ^ N

/-- Qubit count of the second register of the NESS algorithm (paper Sec. 2, p. 3):
`2N` qubits for the vectorized density matrix of an `N`-spin system, plus one ancilla
qubit for the `|0⟩`/`|1⟩` block label of `M`. -/
def registerQubits (N : ℕ) : ℕ := 2 * N + 1

/-- `registerQubits N = 2N + 1` (paper Sec. 2, p. 3), recorded in the form used by the
asymptotic statements. -/
theorem registerQubits_eq (N : ℕ) : registerQubits N = 2 * N + 1 := rfl

/-- Paper Abstract / Sec. 3.1, p. 7: polynomial cost is eventually dominated by the
exponential exact-diagonalisation cost.  For every `C > 0` and `k`,
`C (N+1)^k < 2^N` for all sufficiently large `N`. -/
theorem polynomial_lt_exponential_eventually (C : ℝ) (hC : 0 < C) (k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, C * ((N : ℝ) + 1) ^ k < classicalCost N := by
  have hC2 : (0 : ℝ) < C * (2 : ℝ) ^ k :=
    mul_pos hC (pow_pos (by norm_num : (0 : ℝ) < 2) k)
  have hlim :=
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (by norm_num : (1 : ℝ) < 2)).tendsto_div_nhds_zero
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ k / (2 : ℝ) ^ N < 1 / (C * (2 : ℝ) ^ k) :=
    hlim.eventually (eventually_lt_nhds (one_div_pos.mpr hC2))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have h2Npos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos (by norm_num) N
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
  have hpow : ((N : ℝ) + 1) ^ k ≤ (2 : ℝ) ^ k * (N : ℝ) ^ k := by
    calc ((N : ℝ) + 1) ^ k ≤ (2 * (N : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) hle k
      _ = (2 : ℝ) ^ k * (N : ℝ) ^ k := mul_pow _ _ _
  have hstep : C * (2 : ℝ) ^ k * (N : ℝ) ^ k < (2 : ℝ) ^ N := by
    have hlt := (div_lt_iff₀ h2Npos).mp hN
    have hmul := mul_lt_mul_of_pos_left hlt hC2
    calc C * (2 : ℝ) ^ k * (N : ℝ) ^ k
          = (C * (2 : ℝ) ^ k) * (N : ℝ) ^ k := rfl
      _ < (C * (2 : ℝ) ^ k) * ((1 / (C * (2 : ℝ) ^ k)) * (2 : ℝ) ^ N) := hmul
      _ = (2 : ℝ) ^ N := by
        rw [one_div, mul_inv_cancel_left₀ (ne_of_gt hC2)]
  calc C * ((N : ℝ) + 1) ^ k ≤ C * ((2 : ℝ) ^ k * (N : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
    _ = C * (2 : ℝ) ^ k * (N : ℝ) ^ k := by ring
    _ < classicalCost N := hstep

/-- c001 main statement (arXiv:2008.07133v2, Abstract and Sec. 3.1, p. 7): if the
quantum gate count `Ng` of the NESS algorithm is polynomial in the system size
`N` (as supplied by Eq. (13) in the power-law-gap regime), then it is eventually
strictly smaller than the exponential exact-diagonalisation cost `2^N`.  This is the
paper's “exponential advantage compared to exact diagonalization”. -/
theorem main_result_exponential_advantage {Ng : ℕ → ℝ} {C : ℝ} {k : ℕ}
    (hC : 0 < C) (hcost : ∀ N, Ng N ≤ C * ((N : ℝ) + 1) ^ k) :
    ∀ᶠ N : ℕ in Filter.atTop, Ng N < classicalCost N := by
  filter_upwards [polynomial_lt_exponential_eventually C hC k] with N hN
  exact lt_of_le_of_lt (hcost N) hN

end Qatlib.Papers.SteadyState20.MainResults.ExponentialAdvantage
