/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section


/-!
# Thermalize11 reviewed Algorithm

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.Thermalize11.MainResults.Algorithm

/-- The parameters of the algorithm of p. 4: register sizes `n` (system
qubits), `m` (bath spins), `q` (measured ancilla qubits), `r` (ancilla
qubits), and the real parameters `λ > 0`, inverse temperature `β`, system
Hamiltonian norm `‖H_S‖∞`, and the bath-size correction `C`. -/
structure Parameters where
  /-- Number `n` of system qubits. -/
  n : ℕ
  /-- Number `m` of bath spin-1/2 particles. -/
  m : ℕ
  /-- Number `q` of measured ancilla qubits. -/
  q : ℕ
  /-- Number `r` of ancilla qubits (with `q ≤ r`). -/
  r : ℕ
  /-- The dimensionless parameter `λ > 0`. -/
  lambda : ℝ
  /-- The inverse temperature `β`. -/
  beta : ℝ
  /-- `‖H_S‖∞`, the operator norm of the system Hamiltonian. -/
  HSnorm : ℝ
  /-- The correction `C`, exponentially small in the bath size `m`. -/
  C : ℝ

namespace Parameters

variable (P : Parameters)

/-- `2^k` for an integer exponent `k`, so that `q − r + 2` may be negative.
This is the phase-estimation prefactor of Eq. (11). -/
def twoPowZ (k : ℤ) : ℝ := (2 : ℝ) ^ k

/-- The common exponential factor
`exp(2/λ + β‖H_S‖∞ + λ‖H_S‖∞²β²/8)` of Eqs. (11) and (13). -/
def expFactor : ℝ :=
  Real.exp (2 / P.lambda + P.beta * P.HSnorm + P.lambda * P.HSnorm ^ 2 * P.beta ^ 2 / 8)

/-- The phase-estimation prefactor `2^{q−r+2}(1 + ln(2^{r−q})/π²)` of Eq. (11). -/
def phaseErrorFactor : ℝ :=
  twoPowZ ((P.q : ℤ) - (P.r : ℤ) + 2) *
    (1 + Real.log ((2 : ℝ) ^ (P.r - P.q)) / Real.pi ^ 2)

/-- The deviation of the rectangular state from the Gibbs state, excluding the
bath-size correction `C`: the first line of Eq. (11) (equivalently Eq. (51)). -/
def rectErrorTerm : ℝ := P.phaseErrorFactor * P.expFactor

/-- The bath deviation `½(e^{2/λ} − 1)`: Eq. (4) / Eq. (50), the second
summand of Eq. (11). -/
def bathErrorTerm : ℝ := (1 / 2) * (Real.exp (2 / P.lambda) - 1)

/-- The right-hand side of Eq. (11):
`2^{q−r+2}(1 + ln(2^{r−q})/π²) e^{…} + ½(e^{2/λ} − 1) + C`. -/
def traceErrorBound : ℝ := P.rectErrorTerm + P.bathErrorTerm + P.C

/-- The right-hand side of Eq. (12):
`2^{2−q}√(λ/m) (1/‖H_S‖∞) (1 + 1/√(mλ))`. -/
def deltaBetaBound : ℝ :=
  twoPowZ (2 - (P.q : ℤ)) * Real.sqrt (P.lambda / (P.m : ℝ)) *
    (1 / P.HSnorm) * (1 + 1 / Real.sqrt ((P.m : ℝ) * P.lambda))

/-- The right-hand side of Eq. (13):
`2^q √(π/(2m)) exp(2/λ + β‖H_S‖∞ + λ‖H_S‖∞²β²/8)`. -/
def expectedRunsBound : ℝ :=
  (2 : ℝ) ^ P.q * Real.sqrt (Real.pi / (2 * (P.m : ℝ))) * P.expFactor

end Parameters

/-- The gate ledger of one run of the algorithm (p. 4): `n + 2r` Hadamard
gates, `r` controlled single-qubit gates, `n + q` single-qubit measurements,
and `2^r` controlled time evolutions. -/
structure GateLedger where
  /-- Number of Hadamard gates per run. -/
  hadamards : ℕ
  /-- Number of controlled single-qubit gates per run. -/
  controlledSingleQubit : ℕ
  /-- Number of single-qubit measurements per run. -/
  measurements : ℕ
  /-- Number of controlled time evolutions per run. -/
  controlledTimeEvolutions : ℕ

/-- The ledger recorded on p. 4 for a single run of the algorithm. -/
def algorithmLedger (P : Parameters) : GateLedger where
  hadamards := P.n + 2 * P.r
  controlledSingleQubit := P.r
  measurements := P.n + P.q
  controlledTimeEvolutions := 2 ^ P.r

namespace Parameters

variable (P : Parameters)

/-- `2^k > 0` for every integer `k`. -/
theorem twoPowZ_pos (k : ℤ) : 0 < twoPowZ k := by
  unfold twoPowZ
  exact zpow_pos (by norm_num) k

/-- The exponential factor of Eqs. (11)/(13) is strictly positive. -/
theorem expFactor_pos : 0 < P.expFactor := Real.exp_pos _

/-- In the regime `q ≤ r` the phase-estimation prefactor is nonnegative
(`ln(2^{r−q}) ≥ 0` because `2^{r−q} ≥ 1`). -/
theorem phaseErrorFactor_nonneg (_hq : P.q ≤ P.r) : 0 ≤ P.phaseErrorFactor := by
  unfold Parameters.phaseErrorFactor
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (P.r - P.q) := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
      _ ≤ (2 : ℝ) ^ (P.r - P.q) :=
        pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ (P.r - P.q)) := Real.log_nonneg hpow
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hsecond : 0 ≤ 1 + Real.log ((2 : ℝ) ^ (P.r - P.q)) / Real.pi ^ 2 := by
    have hdiv : 0 ≤ Real.log ((2 : ℝ) ^ (P.r - P.q)) / Real.pi ^ 2 :=
      div_nonneg hlog hpi.le
    linarith
  exact mul_nonneg (twoPowZ_pos _).le hsecond

/-- The rectangular-state error term of Eq. (51) is nonnegative. -/
theorem rectErrorTerm_nonneg (hq : P.q ≤ P.r) : 0 ≤ P.rectErrorTerm := by
  unfold Parameters.rectErrorTerm
  exact mul_nonneg (phaseErrorFactor_nonneg P hq) (expFactor_pos P).le

/-- The bath correction `½(e^{2/λ} − 1)` is nonnegative for `λ > 0`. -/
theorem bathErrorTerm_nonneg (hlam : 0 < P.lambda) : 0 ≤ P.bathErrorTerm := by
  unfold Parameters.bathErrorTerm
  have hexp : (1 : ℝ) ≤ Real.exp (2 / P.lambda) := by
    have h : 0 ≤ 2 / P.lambda := div_nonneg (by norm_num) hlam.le
    simpa using Real.one_le_exp h
  have : 0 ≤ Real.exp (2 / P.lambda) - 1 := by linarith
  exact mul_nonneg (by norm_num) this

/-- **Eq. (11) right-hand side is nonnegative** under the paper's hypotheses. -/
theorem traceErrorBound_nonneg (hq : P.q ≤ P.r) (hlam : 0 < P.lambda)
    (hC : 0 ≤ P.C) : 0 ≤ P.traceErrorBound := by
  unfold Parameters.traceErrorBound
  exact add_nonneg (add_nonneg (rectErrorTerm_nonneg P hq) (bathErrorTerm_nonneg P hlam)) hC

/-- **Eq. (12) right-hand side is nonnegative** for `λ > 0`, `m > 0`,
`‖H_S‖∞ > 0`. -/
theorem deltaBetaBound_nonneg (_hlam : 0 < P.lambda) (_hm : 0 < P.m)
    (hHS : 0 < P.HSnorm) : 0 ≤ P.deltaBetaBound := by
  unfold Parameters.deltaBetaBound
  have h1 : 0 ≤ twoPowZ (2 - (P.q : ℤ)) := (twoPowZ_pos _).le
  have h2 : 0 ≤ Real.sqrt (P.lambda / (P.m : ℝ)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ 1 / P.HSnorm := div_nonneg zero_le_one hHS.le
  have h4 : 0 ≤ 1 + 1 / Real.sqrt ((P.m : ℝ) * P.lambda) := by
    have h5 : 0 ≤ 1 / Real.sqrt ((P.m : ℝ) * P.lambda) :=
      div_nonneg zero_le_one (Real.sqrt_nonneg _)
    linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- **Eq. (13) right-hand side is nonnegative.** -/
theorem expectedRunsBound_nonneg : 0 ≤ P.expectedRunsBound := by
  unfold Parameters.expectedRunsBound
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
    (expFactor_pos P).le

end Parameters

/-- **Assembly of Eq. (10) into Eq. (11).** If the deviation from the
rectangular state is bounded by the phase-estimation term `rectErrorTerm` and
the deviation of the rectangular state from the Gibbs state is bounded by the
bath term `bathErrorTerm`, then their sum is bounded by the Eq. (11)
right-hand side. This is the arithmetic step "the two contributions to the
trace distance error (10) are computed in Appendices B and F" (p. 4). -/
theorem traceErrorBound_assembly (P : Parameters) {dQC dGibbs : ℝ}
    (h1 : dQC ≤ P.rectErrorTerm) (h2 : dGibbs ≤ P.bathErrorTerm)
    (hC : 0 ≤ P.C) :
    dQC + dGibbs ≤ P.traceErrorBound := by
  unfold Parameters.traceErrorBound
  linarith

/-- **Eq. (10) plus the two Appendices-B/F bounds gives Eq. (11).** If the
algorithm's trace distance satisfies the triangle decomposition of Eq. (10)
and its two summands satisfy Eqs. (51) and (50), then the Eq. (11) bound
follows. -/
theorem algorithm_trace_error_from_eq10 (P : Parameters) {dQCω dωGibbs dQC : ℝ}
    (h10 : dQC ≤ dQCω + dωGibbs)
    (h1 : dQCω ≤ P.rectErrorTerm) (h2 : dωGibbs ≤ P.bathErrorTerm)
    (hC : 0 ≤ P.C) :
    dQC ≤ P.traceErrorBound := by
  have hsum := traceErrorBound_assembly P h1 h2 hC
  linarith

/-- The outcome of one execution of the algorithm: the achieved trace distance
to the Gibbs state, the temperature error, and the average number of runs. -/
structure Outcome where
  /-- `𝒟(ω^S_QC, ρ^S_Gibbs)`. -/
  traceDistanceQC : ℝ
  /-- The temperature error `δβ`. -/
  deltaBeta : ℝ
  /-- The average number of runs `#runs`. -/
  averageRuns : ℝ




/-- **The gate ledger of one run** (p. 4): `n + 2r` Hadamard gates,
`r` controlled single-qubit gates, `n + q` single-qubit measurements, and
`2^r` controlled time evolutions. -/
theorem algorithmLedger_eq (P : Parameters) :
    algorithmLedger P =
      { hadamards := P.n + 2 * P.r
        controlledSingleQubit := P.r
        measurements := P.n + P.q
        controlledTimeEvolutions := 2 ^ P.r } := rfl

/-- Number of Hadamard gates per run: `n + 2r`. -/
theorem algorithmLedger_hadamards (P : Parameters) :
    (algorithmLedger P).hadamards = P.n + 2 * P.r := rfl

/-- Number of controlled single-qubit gates per run: `r`. -/
theorem algorithmLedger_controlledSingleQubit (P : Parameters) :
    (algorithmLedger P).controlledSingleQubit = P.r := rfl

/-- Number of single-qubit measurements per run: `n + q`. -/
theorem algorithmLedger_measurements (P : Parameters) :
    (algorithmLedger P).measurements = P.n + P.q := rfl

/-- Number of controlled time evolutions per run: `2^r`. -/
theorem algorithmLedger_controlledTimeEvolutions (P : Parameters) :
    (algorithmLedger P).controlledTimeEvolutions = 2 ^ P.r := rfl


/-- Free outcomes can exceed all three claimed bounds even for fixed parameters.
No execution semantics constrain these fields in the legacy interface. -/
theorem freeOutcome_refutes (P : Parameters) :
    ∃ O : Outcome, ¬ O.traceDistanceQC ≤ P.traceErrorBound ∧
      ¬ O.deltaBeta ≤ P.deltaBetaBound ∧ ¬ O.averageRuns ≤ P.expectedRunsBound := by
  refine ⟨⟨P.traceErrorBound + 1, P.deltaBetaBound + 1, P.expectedRunsBound + 1⟩, ?_, ?_, ?_⟩ <;>
    dsimp <;> linarith

end Qatlib.Papers.Thermalize11.MainResults.Algorithm
