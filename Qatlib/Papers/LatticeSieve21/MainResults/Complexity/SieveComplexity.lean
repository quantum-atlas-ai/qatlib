/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# LatticeSieve21 / MainResults / Complexity — the paper's exponent bookkeeping

Fixed paper version: arXiv:2105.05608v1 (12 May 2021),
André Chailloux and Johanna Loyer, *Lattice sieving via quantum random walks*.

This module formalises the *numerical resource accounting* of the paper's main
theorems (Theorems 1--6, Proposition 8, Proposition 10).  Every theorem of the
paper states that a heuristic sieving algorithm exists and that its running
time, QRAM, quantum-memory and classical-memory costs have prescribed
exponential growth in the dimension `d`.  Concretely the paper works with

  `N := (4/3)^{d/2}`     (the sieving list size; the text writes `N := (4/3)^d`
  but every numerical conversion in the paper uses `log₂ N = 0.2075·d`, i.e.
  the square-root normalisation),

and reports exponents in the `N`-basis (e.g. `T = N^{1.2384+o(1)}`) and, after
the conversion `N^τ = 2^{(τ·log₂(4/3)/2)·d}`, in the `2`-basis (e.g.
`T = 2^{0.2570d+o(d)}`).

What is formalised here is exactly the part of each theorem that is a
deterministic function of the strategy parameters: the exponent vector

  `time = max{1+c-ζ, 1+c1+ρ}`,  `QRAM = c`,  `quantum memory = c1+ρ`,
  `classical memory = 1`

(Proposition 10 and Theorem 4), the affine envelopes of the two trade-off
families (Theorems 2/5 and 3/6), and the conversion between the `N`- and
`2`-bases (both the exact real-power identity and the decimal interval
`log₂(4/3) ∈ [0.41503, 0.41505]` are proved).

The *existence of the quantum algorithm* and its heuristic correctness are
asymptotic, probabilistic statements about a physical/computational model that
is not represented in this library; they are not encoded as an uninterpreted
axiom here.  The docstrings say so at each theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LatticeSieve21.MainResults.Complexity

/-! ## The parameter/projection model -/

/-- Strategy parameters of the paper's quantum sieving algorithm: the global
list/filter parameter `c`, the two inner-walk parameters `c1, c2`, the relaxed
PRAM parameter `ρ` of Section 6 (Section 5 uses `ρ = ρ0`), the reference value
`ρ0` of Section 5.2 and the solution-density exponent `ζ`. -/
structure Params where
  c : ℝ
  c1 : ℝ
  c2 : ℝ
  rho : ℝ
  rho0 : ℝ
  zeta : ℝ

/-- The four resource exponents that the paper reports, in the `N`-basis. -/
structure ResourceExponents where
  time : ℝ
  qram : ℝ
  qmem : ℝ
  classical : ℝ

/-- Proposition 8 / Theorem 4 bookkeeping.  With `T = NB_REP·(INIT+FAS)` and
`NB_REP = max{1,N^{c-ζ}}`, `INIT = N^{1+o(1)}`, `FAS = N^{1-c}·FAS₁`, the paper
rewrites `T = N^{1+c-ζ} + N^{1+c1+ρ}`; the time exponent is therefore the
maximum of the two summands.  QRAM is `N^c`, quantum memory is `N^{c1+ρ}`
(Section 6: the vertex stores `N^{c1+ρ}` registers, and the same amount of
QRAM for insertions/deletions), classical memory is `N^1`. -/
def profile (p : Params) : ResourceExponents where
  time := max (1 + p.c - p.zeta) (1 + p.c1 + p.rho)
  qram := p.c
  qmem := p.c1 + p.rho
  classical := 1

/-! ## Proposition 10 (claim c012) -/

/-- Proposition 10 parameter set: `c ≈ 0.3300`, `c1 ≈ 0.1952`,
`c2 ≈ 0.0603`, with `ρ = ρ0 = 0.0603` and `ζ ≈ 0.0745` (p.11, lines 508--514). -/
def prop10 : Params where
  c := 33 / 100
  c1 := 1952 / 10000
  c2 := 603 / 10000
  rho := 603 / 10000
  rho0 := 603 / 10000
  zeta := 745 / 10000

/-- Proposition 10, time: `T = N^{1.2555+o(1)}` (p.11). -/
theorem prop10_time_arith : (profile prop10).time = 12555 / 10000 := by
  have h : (1 : ℝ) + 33 / 100 - 745 / 10000 ≤ 1 + 1952 / 10000 + 603 / 10000 := by
    norm_num
  simp only [profile, prop10]
  rw [max_eq_right h]
  norm_num

/-- Deprecated alias for `prop10_time_arith`. -/
@[deprecated prop10_time_arith (since := "2026-11-13")] alias prop10_time := prop10_time_arith

/-- Proposition 10, QRAM: `N^{0.3300+o(1)}` (p.11). -/
theorem prop10_qram_arith : (profile prop10).qram = 33 / 100 := by
  simp only [profile, prop10]

/-- Deprecated alias for `prop10_qram_arith`. -/
@[deprecated prop10_qram_arith (since := "2026-11-13")] alias prop10_qram := prop10_qram_arith

/-- Proposition 10, quantum memory: `N^{0.2555+o(1)}` (p.11). -/
theorem prop10_qmem_arith : (profile prop10).qmem = 2555 / 10000 := by
  simp only [profile, prop10]; norm_num

/-- Deprecated alias for `prop10_qmem_arith`. -/
@[deprecated prop10_qmem_arith (since := "2026-11-13")] alias prop10_qmem := prop10_qmem_arith

/-- Proposition 10, classical memory: `N^{1+o(1)}` (p.11). -/
theorem prop10_classical_arith : (profile prop10).classical = 1 := by
  simp only [profile, prop10]

/-- Deprecated alias for `prop10_classical_arith`. -/
@[deprecated prop10_classical_arith (since := "2026-11-13")] alias prop10_classical := prop10_classical_arith

/-! ## Theorem 4 (claim c013), and its identity with Theorem 1 (claim c001) -/

/-- Theorem 4 parameter set: `ρ → 0`, `c ≈ 0.3696`, `c1 ≈ 0.2384`, `c2 = 0`,
`ζ ≈ 0.1313`, with the paper's `ρ0 ≈ 0.107` (p.12, lines 592--604). -/
def theorem4 : Params where
  c := 3696 / 10000
  c1 := 2384 / 10000
  c2 := 0
  rho := 0
  rho0 := 107 / 1000
  zeta := 1313 / 10000

/-- Theorem 4, time: `T = N^{1.2384+o(1)}` (p.12). -/
theorem theorem4_time_arith : (profile theorem4).time = 12384 / 10000 := by
  have h : (1 : ℝ) + 3696 / 10000 - 1313 / 10000 ≤ 1 + 2384 / 10000 + 0 := by
    norm_num
  simp only [profile, theorem4]
  rw [max_eq_right h]
  norm_num

/-- Deprecated alias for `theorem4_time_arith`. -/
@[deprecated theorem4_time_arith (since := "2026-11-13")] alias theorem4_time := theorem4_time_arith

/-- Theorem 4, QRAM: `N^{0.3696}` (p.12). -/
theorem theorem4_qram_arith : (profile theorem4).qram = 3696 / 10000 := by
  simp only [profile, theorem4]

/-- Deprecated alias for `theorem4_qram_arith`. -/
@[deprecated theorem4_qram_arith (since := "2026-11-13")] alias theorem4_qram := theorem4_qram_arith

/-- Theorem 4, quantum memory: `N^{0.2384}` (p.12). -/
theorem theorem4_qmem_arith : (profile theorem4).qmem = 2384 / 10000 := by
  simp only [profile, theorem4]; norm_num

/-- Deprecated alias for `theorem4_qmem_arith`. -/
@[deprecated theorem4_qmem_arith (since := "2026-11-13")] alias theorem4_qmem := theorem4_qmem_arith

/-- Theorem 4, classical memory: `N^{1+o(1)}` (p.12). -/
theorem theorem4_classical_arith : (profile theorem4).classical = 1 := by
  simp only [profile, theorem4]

/-- Deprecated alias for `theorem4_classical_arith`. -/
@[deprecated theorem4_classical_arith (since := "2026-11-13")] alias theorem4_classical := theorem4_classical_arith

/-- The paper's Theorem 1 parameter regime is exactly Theorem 4
("Theorem 1 restated", p.12): same `c, c1, c2, ρ, ρ0, ζ`. -/
def theorem1 : Params := theorem4

/-- **Claim c001 = claim c013 on the resource vector.**  Theorem 1 and
Theorem 4 describe the same algorithmic profile; the Lean parameters are
definitionally equal. -/
theorem theorem1_profile_eq_theorem4 : profile theorem1 = profile theorem4 := rfl

/-- Theorem 1, time exponent: `T = N^{1.2384+o(1)}` (p.2, via Theorem 4 p.12). -/
theorem theorem1_time_arith : (profile theorem1).time = 12384 / 10000 := theorem4_time_arith

/-- Deprecated alias for `theorem1_time_arith`. -/
@[deprecated theorem1_time_arith (since := "2026-11-13")] alias theorem1_time := theorem1_time_arith

/-- Theorem 1, QRAM exponent: `N^{0.3696}` (p.2, via Theorem 4 p.12). -/
theorem theorem1_qram_arith : (profile theorem1).qram = 3696 / 10000 := theorem4_qram_arith

/-- Deprecated alias for `theorem1_qram_arith`. -/
@[deprecated theorem1_qram_arith (since := "2026-11-13")] alias theorem1_qram := theorem1_qram_arith

/-- Theorem 1, quantum-memory exponent: `N^{0.2384}` (p.2, via Theorem 4 p.12). -/
theorem theorem1_qmem_arith : (profile theorem1).qmem = 2384 / 10000 := theorem4_qmem_arith

/-- Deprecated alias for `theorem1_qmem_arith`. -/
@[deprecated theorem1_qmem_arith (since := "2026-11-13")] alias theorem1_qmem := theorem1_qmem_arith

/-- Theorem 1, classical-memory exponent: `N^{1+o(1)}` (p.2, via Theorem 4). -/
theorem theorem1_classical_arith : (profile theorem1).classical = 1 := theorem4_classical_arith

/-- Deprecated alias for `theorem1_classical_arith`. -/
@[deprecated theorem1_classical_arith (since := "2026-11-13")] alias theorem1_classical := theorem1_classical_arith

/-! ## The exact `N`-basis to `2`-basis conversion

The paper writes `N := (4/3)^{d/2}` and then replaces `N^τ` by
`2^{(τ·log₂(4/3)/2)·d}`.  This is an identity, not an approximation; the
approximation is only in the decimal digits of `log₂(4/3)`.
-/

/-- `log₂(4/3)`. -/
def log2FourThirds : ℝ := Real.log (4 / 3) / Real.log 2

/-- The base-2 exponent attached to an `N`-exponent `τ`:
`2^{(τ·log₂(4/3)/2)·d}`. -/
def twoExp (τ d : ℝ) : ℝ := 2 ^ (τ * log2FourThirds / 2 * d)

/-- The `N`-basis expression `N^τ` with `N = (4/3)^{d/2}`. -/
def nExp (τ d : ℝ) : ℝ := ((4 / 3 : ℝ) ^ (d / 2)) ^ τ

/-- **Exact conversion.**  `2^{(τ·log₂(4/3)/2)·d} = ((4/3)^{d/2})^τ`. -/
theorem twoExp_eq_nExp (τ d : ℝ) : twoExp τ d = nExp τ d := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h43pos : (0 : ℝ) < 4 / 3 := by norm_num
  have hNpos : (0 : ℝ) < (4 / 3 : ℝ) ^ (d / 2) := Real.rpow_pos_of_pos h43pos (d / 2)
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold twoExp nExp log2FourThirds
  rw [Real.rpow_def_of_pos h2pos, Real.rpow_def_of_pos hNpos, Real.log_rpow h43pos]
  congr 1
  field_simp

/-- Decimal evaluation of `log₂(4/3)`, used to quote the paper's
`0.2570 / 0.0767 / 0.0495 / 0.2075` digits:
`log₂(4/3) ∈ [0.41503, 0.41505]`.

Proof: `log (4/3) = 2·log 2 - log 3`, and Mathlib's decimal bounds
`Real.log_two_gt_d9`, `Real.log_two_lt_d9`, `Real.log_three_gt_d9`,
`Real.log_three_lt_d9` pin `log 2` and `log 3`; dividing by `log 2 > 0`
reduces the claim to two linear inequalities. -/
theorem log2FourThirds_bounds :
    0.41503 ≤ log2FourThirds ∧ log2FourThirds ≤ 0.41505 := by
  have h2lo : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h3lo : 1.0986122885 < Real.log 3 := Real.log_three_gt_d9
  have h3hi : Real.log 3 < 1.0986122888 := Real.log_three_lt_d9
  have h43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hL : 0 < Real.log 2 := by linarith
  unfold log2FourThirds
  constructor
  · rw [le_div_iff₀ hL, h43]
    linarith
  · rw [div_le_iff₀ hL, h43]
    linarith

/-- Theorem 4 time in the `2`-basis: `0.2570·d` (p.12, `T = 2^{0.2570d+o(d)}`). -/
theorem theorem4_time_base2_arith :
    0.25695 ≤ (profile theorem4).time * log2FourThirds / 2 ∧
      (profile theorem4).time * log2FourThirds / 2 ≤ 0.25705 := by
  rw [theorem4_time_arith]
  obtain ⟨hlo, hhi⟩ := log2FourThirds_bounds
  constructor <;> nlinarith

/-- Deprecated alias for `theorem4_time_base2_arith`. -/
@[deprecated theorem4_time_base2_arith (since := "2026-11-13")] alias theorem4_time_base2 := theorem4_time_base2_arith

/-- Theorem 4 QRAM in the `2`-basis: `0.0767·d` (p.12). -/
theorem theorem4_qram_base2_arith :
    0.07665 ≤ (profile theorem4).qram * log2FourThirds / 2 ∧
      (profile theorem4).qram * log2FourThirds / 2 ≤ 0.07675 := by
  rw [theorem4_qram_arith]
  obtain ⟨hlo, hhi⟩ := log2FourThirds_bounds
  constructor <;> nlinarith

/-- Deprecated alias for `theorem4_qram_base2_arith`. -/
@[deprecated theorem4_qram_base2_arith (since := "2026-11-13")] alias theorem4_qram_base2 := theorem4_qram_base2_arith

/-- Theorem 4 quantum memory in the `2`-basis: `0.0495·d` (p.12). -/
theorem theorem4_qmem_base2_arith :
    0.04945 ≤ (profile theorem4).qmem * log2FourThirds / 2 ∧
      (profile theorem4).qmem * log2FourThirds / 2 ≤ 0.04955 := by
  rw [theorem4_qmem_arith]
  obtain ⟨hlo, hhi⟩ := log2FourThirds_bounds
  constructor <;> nlinarith

/-- Deprecated alias for `theorem4_qmem_base2_arith`. -/
@[deprecated theorem4_qmem_base2_arith (since := "2026-11-13")] alias theorem4_qmem_base2 := theorem4_qmem_base2_arith

/-- Theorem 1 in the `2`-basis: `T = 2^{0.2570d+o(d)}` (p.2, headlines). -/
theorem theorem1_time_base2_arith :
    0.25695 ≤ (profile theorem1).time * log2FourThirds / 2 ∧
      (profile theorem1).time * log2FourThirds / 2 ≤ 0.25705 := by
  rw [theorem1_profile_eq_theorem4]
  exact theorem4_time_base2_arith

/-- Deprecated alias for `theorem1_time_base2_arith`. -/
@[deprecated theorem1_time_base2_arith (since := "2026-11-13")] alias theorem1_time_base2 := theorem1_time_base2_arith

/-- Theorem 1 QRAM in the `2`-basis: `2^{0.0767d}` (p.2). -/
theorem theorem1_qram_base2_arith :
    0.07665 ≤ (profile theorem1).qram * log2FourThirds / 2 ∧
      (profile theorem1).qram * log2FourThirds / 2 ≤ 0.07675 := by
  rw [theorem1_profile_eq_theorem4]
  exact theorem4_qram_base2_arith

/-- Deprecated alias for `theorem1_qram_base2_arith`. -/
@[deprecated theorem1_qram_base2_arith (since := "2026-11-13")] alias theorem1_qram_base2 := theorem1_qram_base2_arith

/-- Theorem 1 quantum memory in the `2`-basis: `2^{0.0495d}` (p.2). -/
theorem theorem1_qmem_base2_arith :
    0.04945 ≤ (profile theorem1).qmem * log2FourThirds / 2 ∧
      (profile theorem1).qmem * log2FourThirds / 2 ≤ 0.04955 := by
  rw [theorem1_profile_eq_theorem4]
  exact theorem4_qmem_base2_arith

/-- Deprecated alias for `theorem1_qmem_base2_arith`. -/
@[deprecated theorem1_qmem_base2_arith (since := "2026-11-13")] alias theorem1_qmem_base2 := theorem1_qmem_base2_arith

/-- Proposition 10 time in the `2`-basis: `T = 2^{0.2605d+o(d)}` (p.11). -/
theorem prop10_time_base2_arith :
    0.26045 ≤ (profile prop10).time * log2FourThirds / 2 ∧
      (profile prop10).time * log2FourThirds / 2 ≤ 0.26055 := by
  rw [prop10_time_arith]
  obtain ⟨hlo, hhi⟩ := log2FourThirds_bounds
  constructor <;> nlinarith

/-- Deprecated alias for `prop10_time_base2_arith`. -/
@[deprecated prop10_time_base2_arith (since := "2026-11-13")] alias prop10_time_base2 := prop10_time_base2_arith

/-- Proposition 10 QRAM in the `2`-basis: `N^{0.3300} = 2^{0.0685d}` (p.11). -/
theorem prop10_qram_base2_arith :
    0.06845 ≤ (profile prop10).qram * log2FourThirds / 2 ∧
      (profile prop10).qram * log2FourThirds / 2 ≤ 0.06855 := by
  rw [prop10_qram_arith]
  obtain ⟨hlo, hhi⟩ := log2FourThirds_bounds
  constructor <;> nlinarith

/-- Deprecated alias for `prop10_qram_base2_arith`. -/
@[deprecated prop10_qram_base2_arith (since := "2026-11-13")] alias prop10_qram_base2 := prop10_qram_base2_arith

/-- Proposition 10 quantum memory in the `2`-basis: `N^{0.2555} = 2^{0.0530d}`
(p.11). -/
theorem prop10_qmem_base2_arith :
    0.05295 ≤ (profile prop10).qmem * log2FourThirds / 2 ∧
      (profile prop10).qmem * log2FourThirds / 2 ≤ 0.05305 := by
  rw [prop10_qmem_arith]
  obtain ⟨hlo, hhi⟩ := log2FourThirds_bounds
  constructor <;> nlinarith

/-- Deprecated alias for `prop10_qmem_base2_arith`. -/
@[deprecated prop10_qmem_base2_arith (since := "2026-11-13")] alias prop10_qmem_base2 := prop10_qmem_base2_arith

/-! ## Theorem 2 / Theorem 5 (claims c002, c014): fixed quantum memory

The paper (Section 7.1, p.13, and Theorem 2 p.2) reports that for
`M ∈ [0, 0.0495]` the time exponent lies within `4·10⁻⁵` above and `2·10⁻⁵`
below the affine function `0.2653 - 0.1670·M`, the QRAM exponent lies in
`[0.0578 + 0.3829·M - 2·10⁻⁴, 0.0578 + 0.3829·M]`, and the quantum-memory
exponent is exactly `M`.  Theorem 5 (Section 7.1) is the same statement.
-/

/-- Affine centre of the time exponent for a fixed quantum memory `M`. -/
def tauQuantumMemoryEnvelope (M : ℝ) : ℝ := 2653 / 10000 - 1670 / 10000 * M

/-- Affine centre of the QRAM exponent for a fixed quantum memory `M`. -/
def gammaQuantumMemoryEnvelope (M : ℝ) : ℝ := 578 / 10000 + 3829 / 10000 * M

/-- Quantum-memory exponent as a function of the parameter `M`. -/
def muQuantumMemoryEnvelope (M : ℝ) : ℝ := M

/-- The trade-off data of Theorem 2/5: exponent functions on
`[0, 0.0495]` satisfying the paper's error envelopes. -/
structure QuantumMemoryTradeoff where
  /-- time exponent `τ_M` -/
  tau : ℝ → ℝ
  /-- QRAM exponent `γ_M` -/
  gamma : ℝ → ℝ
  /-- quantum-memory exponent `μ_M` -/
  mu : ℝ → ℝ
  tau_mem : ∀ M ∈ Set.Icc (0 : ℝ) (495 / 10000),
    tauQuantumMemoryEnvelope M - 2 / 100000 ≤ tau M ∧
      tau M ≤ tauQuantumMemoryEnvelope M + 4 / 100000
  gamma_mem : ∀ M ∈ Set.Icc (0 : ℝ) (495 / 10000),
    gammaQuantumMemoryEnvelope M - 2 / 10000 ≤ gamma M ∧
      gamma M ≤ gammaQuantumMemoryEnvelope M
  mu_spec : ∀ M ∈ Set.Icc (0 : ℝ) (495 / 10000), mu M = M

/-- **Theorem 2 exists**: the affine envelopes realize the stated error
intervals.  (The paper's auxiliary claim that one and the same algorithm
realizes `τ_M` and `γ_M` simultaneously is algorithmic and is not part of the
Lean model.) -/
theorem theorem2_tradeoff_exists : Nonempty QuantumMemoryTradeoff := by
  refine ⟨⟨tauQuantumMemoryEnvelope, gammaQuantumMemoryEnvelope,
      muQuantumMemoryEnvelope, ?_, ?_, ?_⟩⟩
  · intro M _; exact ⟨by linarith, by linarith⟩
  · intro M _; exact ⟨by linarith, le_rfl⟩
  · intro M _; rfl

/-- **Theorem 2 at `M = 0`**: the time exponent is Laarhoven's `0.2653` and the
QRAM exponent is `0.0578` (p.2: "for M = 0 the quantum running time of
Laarhoven's algorithm"). -/
theorem theorem2_at_zero (T : QuantumMemoryTradeoff) :
    |T.tau 0 - 2653 / 10000| ≤ 4 / 100000 ∧
      |T.gamma 0 - 578 / 10000| ≤ 2 / 10000 ∧ T.mu 0 = 0 := by
  obtain ⟨h1, h2⟩ := T.tau_mem 0 (by norm_num)
  obtain ⟨h3, h4⟩ := T.gamma_mem 0 (by norm_num)
  refine ⟨?_, ?_, T.mu_spec 0 (by norm_num)⟩
  · rw [abs_le]; constructor <;> simp only [tauQuantumMemoryEnvelope] at h1 h2 ⊢ <;> linarith
  · rw [abs_le]; constructor <;> simp only [gammaQuantumMemoryEnvelope] at h3 h4 ⊢ <;> linarith

/-- **Theorem 2 at `M = 0.0495`**: the time exponent is Theorem 1's `0.2570`,
the QRAM exponent is Theorem 1's `0.0767` and the quantum memory is `0.0495`
(p.2: "for M = 0.0495, the result of Theorem 1"). -/
theorem theorem2_at_max (T : QuantumMemoryTradeoff) :
    |T.tau (495 / 10000) - 257 / 1000| ≤ 1 / 10000 ∧
      |T.gamma (495 / 10000) - 767 / 10000| ≤ 2 / 10000 ∧
      T.mu (495 / 10000) = 495 / 10000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem (495 / 10000) (by norm_num)
  obtain ⟨h3, h4⟩ := T.gamma_mem (495 / 10000) (by norm_num)
  refine ⟨?_, ?_, T.mu_spec (495 / 10000) (by norm_num)⟩
  · rw [abs_le]
    simp only [tauQuantumMemoryEnvelope] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · rw [abs_le]
    simp only [gammaQuantumMemoryEnvelope] at h3 h4 ⊢
    constructor <;> norm_num at h3 h4 ⊢ <;> linarith

/-- **Theorem 5 (claim c014)** is the restatement of Theorem 2 (p.13); it has
the same trade-off structure and the same two endpoint values. -/
theorem theorem5_at_zero (T : QuantumMemoryTradeoff) :
    |T.tau 0 - 2653 / 10000| ≤ 4 / 100000 ∧
      |T.gamma 0 - 578 / 10000| ≤ 2 / 10000 ∧ T.mu 0 = 0 :=
  theorem2_at_zero T

/-- **Theorem 5 at `M = 0.0495`** recovers Theorem 1 (p.13). -/
theorem theorem5_at_max (T : QuantumMemoryTradeoff) :
    |T.tau (495 / 10000) - 257 / 1000| ≤ 1 / 10000 ∧
      |T.gamma (495 / 10000) - 767 / 10000| ≤ 2 / 10000 ∧
      T.mu (495 / 10000) = 495 / 10000 :=
  theorem2_at_max T

/-! ## Theorem 3 / Theorem 6 (claims c003, c015): fixed QRAM

For `M' ∈ [0, 0.0767]`, `γ_{M'} = M'` and
`μ_{M'} ∈ max{2.6356(M'-0.0579),0} + [0, 9·10⁻⁴]`.  The time envelope is
`0.2925 - 0.4647·M'` in Theorem 3 (p.2) and `0.2927 - 0.4647·M'` in Theorem 6
(p.13); both are within the paper's `6·10⁻⁴` band.
-/

/-- Time-exponent centre for a fixed QRAM `M'`, Theorem 3 reading. -/
def tauQramEnvelope3 (M : ℝ) : ℝ := 2925 / 10000 - 4647 / 10000 * M

/-- Time-exponent centre for a fixed QRAM `M'`, Theorem 6 reading. -/
def tauQramEnvelope6 (M : ℝ) : ℝ := 2927 / 10000 - 4647 / 10000 * M

/-- Quantum-memory exponent centre for a fixed QRAM `M'`. -/
def muQramEnvelope (M : ℝ) : ℝ := max (26356 / 10000 * (M - 579 / 10000)) 0

/-- The trade-off data of Theorem 3/6 for a chosen time envelope. -/
structure QramTradeoff (tauEnv : ℝ → ℝ) where
  /-- time exponent `τ_{M'}` -/
  tau : ℝ → ℝ
  /-- QRAM exponent `γ_{M'}` -/
  gamma : ℝ → ℝ
  /-- quantum-memory exponent `μ_{M'}` -/
  mu : ℝ → ℝ
  tau_mem : ∀ M ∈ Set.Icc (0 : ℝ) (767 / 10000),
    tauEnv M - 6 / 10000 ≤ tau M ∧ tau M ≤ tauEnv M
  gamma_spec : ∀ M ∈ Set.Icc (0 : ℝ) (767 / 10000), gamma M = M
  mu_mem : ∀ M ∈ Set.Icc (0 : ℝ) (767 / 10000),
    muQramEnvelope M ≤ mu M ∧ mu M ≤ muQramEnvelope M + 9 / 10000

/-- **Theorem 3 exists** in the model: the affine/`max` envelopes satisfy the
stated error intervals. -/
theorem theorem3_tradeoff_exists : Nonempty (QramTradeoff tauQramEnvelope3) := by
  refine ⟨⟨tauQramEnvelope3, fun M => M, muQramEnvelope, ?_, ?_, ?_⟩⟩
  · intro M _; exact ⟨by linarith, le_rfl⟩
  · intro M _; rfl
  · intro M _; exact ⟨le_rfl, by linarith⟩

/-- **Theorem 6 exists** in the model (same construction, `0.2927` reading). -/
theorem theorem6_tradeoff_exists : Nonempty (QramTradeoff tauQramEnvelope6) := by
  refine ⟨⟨tauQramEnvelope6, fun M => M, muQramEnvelope, ?_, ?_, ?_⟩⟩
  · intro M _; exact ⟨by linarith, le_rfl⟩
  · intro M _; rfl
  · intro M _; exact ⟨le_rfl, by linarith⟩

/-- **Theorem 3 at `M' = 0`**: the classical `[BeckerDucasGamaLaarhoven2016]` exponent `0.2925` with
no quantum resources (p.2).  The quantum-memory band at `M' = 0` is
`[0, 9·10⁻⁴]`. -/
theorem theorem3_at_zero (T : QramTradeoff tauQramEnvelope3) :
    |T.tau 0 - 2925 / 10000| ≤ 6 / 10000 ∧ T.gamma 0 = 0 ∧ |T.mu 0| ≤ 9 / 10000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem 0 (by norm_num)
  refine ⟨?_, T.gamma_spec 0 (by norm_num), ?_⟩
  · rw [abs_le]; simp only [tauQramEnvelope3] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · obtain ⟨h3, h4⟩ := T.mu_mem 0 (by norm_num)
    rw [muQramEnvelope] at h3 h4
    have hneg : (26356 / 10000 * ((0 : ℝ) - 579 / 10000)) ≤ 0 := by norm_num
    rw [max_eq_right hneg] at h3 h4
    rw [abs_le]
    constructor <;> linarith

/-- **Theorem 3 at `M' = 0.0577`**: Laarhoven's quantum exponent `0.2653`
within the paper's `6·10⁻⁴` band, with quantum memory in `[0, 9·10⁻⁴]`
(p.2). -/
theorem theorem3_at_laarhoven (T : QramTradeoff tauQramEnvelope3) :
    |T.tau (577 / 10000) - 2653 / 10000| ≤ 6 / 10000 ∧
      T.gamma (577 / 10000) = 577 / 10000 ∧ |T.mu (577 / 10000)| ≤ 9 / 10000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem (577 / 10000) (by norm_num)
  refine ⟨?_, T.gamma_spec (577 / 10000) (by norm_num), ?_⟩
  · rw [abs_le]; simp only [tauQramEnvelope3] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · obtain ⟨h3, h4⟩ := T.mu_mem (577 / 10000) (by norm_num)
    rw [muQramEnvelope] at h3 h4
    have hneg : (26356 / 10000 * ((577 / 10000 : ℝ) - 579 / 10000)) ≤ 0 := by
      norm_num
    rw [max_eq_right hneg] at h3 h4
    rw [abs_le]
    constructor <;> linarith

/-- **Theorem 3 at `M' = 0.0767`**: Theorem 1's exponents `0.2570`, QRAM
`0.0767`, quantum memory `0.0495`, all within the paper's stated bands
(p.2).  Both bands are stated with slack `10⁻³`: at `M' = 0.0767` the
time centre is `0.25686` (its own `6·10⁻⁴` band reaches `0.25626`), and the
quantum-memory centre `2.6356·(0.0767-0.0579) = 0.049549…` already sits
`5·10⁻⁵` above `0.0495` before the model's `9·10⁻⁴` slack is added. -/
theorem theorem3_at_max (T : QramTradeoff tauQramEnvelope3) :
    |T.tau (767 / 10000) - 257 / 1000| ≤ 1 / 1000 ∧
      T.gamma (767 / 10000) = 767 / 10000 ∧
      |T.mu (767 / 10000) - 495 / 10000| ≤ 1 / 1000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem (767 / 10000) (by norm_num)
  refine ⟨?_, T.gamma_spec (767 / 10000) (by norm_num), ?_⟩
  · rw [abs_le]; simp only [tauQramEnvelope3] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · obtain ⟨h3, h4⟩ := T.mu_mem (767 / 10000) (by norm_num)
    rw [muQramEnvelope] at h3 h4
    have hpos : (0 : ℝ) ≤ 26356 / 10000 * ((767 / 10000 : ℝ) - 579 / 10000) := by
      norm_num
    rw [max_eq_left hpos] at h3 h4
    rw [abs_le]
    constructor <;> norm_num at h3 h4 ⊢ <;> linarith

/-- **Theorem 6 at `M' = 0`**: the classical exponent `0.2925` up to the
`6·10⁻⁴` band of the `0.2927` reading (p.13). -/
theorem theorem6_at_zero (T : QramTradeoff tauQramEnvelope6) :
    |T.tau 0 - 2925 / 10000| ≤ 6 / 10000 ∧ T.gamma 0 = 0 ∧ |T.mu 0| ≤ 9 / 10000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem 0 (by norm_num)
  refine ⟨?_, T.gamma_spec 0 (by norm_num), ?_⟩
  · rw [abs_le]; simp only [tauQramEnvelope6] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · obtain ⟨h3, h4⟩ := T.mu_mem 0 (by norm_num)
    rw [muQramEnvelope] at h3 h4
    have : (26356 / 10000 * ((0 : ℝ) - 579 / 10000)) ≤ 0 := by norm_num
    rw [max_eq_right this] at h3 h4
    rw [abs_le]
    constructor <;> linarith

/-- **Theorem 6 at `M' = 0.0577`**: Laarhoven's `0.2653` within `6·10⁻⁴`,
quantum memory in `[0, 9·10⁻⁴]` (p.13). -/
theorem theorem6_at_laarhoven (T : QramTradeoff tauQramEnvelope6) :
    |T.tau (577 / 10000) - 2653 / 10000| ≤ 6 / 10000 ∧
      T.gamma (577 / 10000) = 577 / 10000 ∧ |T.mu (577 / 10000)| ≤ 9 / 10000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem (577 / 10000) (by norm_num)
  refine ⟨?_, T.gamma_spec (577 / 10000) (by norm_num), ?_⟩
  · rw [abs_le]; simp only [tauQramEnvelope6] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · obtain ⟨h3, h4⟩ := T.mu_mem (577 / 10000) (by norm_num)
    rw [muQramEnvelope] at h3 h4
    have hneg : (26356 / 10000 * ((577 / 10000 : ℝ) - 579 / 10000)) ≤ 0 := by
      norm_num
    rw [max_eq_right hneg] at h3 h4
    rw [abs_le]
    constructor <;> linarith

/-- **Theorem 6 at `M' = 0.0767`**: Theorem 1's exponents within the paper's
stated bands (p.13); same `10⁻³` slack for both bands as
`theorem3_at_max`. -/
theorem theorem6_at_max (T : QramTradeoff tauQramEnvelope6) :
    |T.tau (767 / 10000) - 257 / 1000| ≤ 1 / 1000 ∧
      T.gamma (767 / 10000) = 767 / 10000 ∧
      |T.mu (767 / 10000) - 495 / 10000| ≤ 1 / 1000 := by
  obtain ⟨h1, h2⟩ := T.tau_mem (767 / 10000) (by norm_num)
  refine ⟨?_, T.gamma_spec (767 / 10000) (by norm_num), ?_⟩
  · rw [abs_le]; simp only [tauQramEnvelope6] at h1 h2 ⊢
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  · obtain ⟨h3, h4⟩ := T.mu_mem (767 / 10000) (by norm_num)
    rw [muQramEnvelope] at h3 h4
    have hpos : (0 : ℝ) ≤ 26356 / 10000 * ((767 / 10000 : ℝ) - 579 / 10000) := by
      norm_num
    rw [max_eq_left hpos] at h3 h4
    rw [abs_le]
    constructor <;> norm_num at h3 h4 ⊢ <;> linarith

/-! ## Proposition 8 (claim c008): repetition and cost algebra -/

/-- `NB_REP = max{1, N^{c-ζ+o(1)}}`, as an `N`-exponent: the exponent of
`max{1, ·}` is `max 0 (c-ζ)`. -/
def nbRepExponent (c ζ : ℝ) : ℝ := max 0 (c - ζ)

/-- `INIT = N^{1+o(1)}`: exponent `1`. -/
def initExponent : ℝ := 1

/-- `FAS = N^{1-c}·FAS₁`: the factor multiplying `FAS₁` has exponent `1-c`. -/
def fasExponent (c : ℝ) : ℝ := 1 - c

/-- Total time exponent `T = NB_REP·(INIT+FAS)` in the paper's rewritten form
`T = N^{1+c-ζ} + N^{1+c1+ρ}` (p.12). -/
def totalTimeExponent (c c1 ρ ζ : ℝ) : ℝ := max (1 + c - ζ) (1 + c1 + ρ)

/-- The repetition count's exponent: the paper computes
`NB_REP = N^{1-(1-c+ζ)+o(1)} = N^{c-ζ+o(1)}` (p.9). -/
theorem prop8_nbRep_arithmetic (c ζ : ℝ) : 1 - (1 - c + ζ) = c - ζ := by ring

/-- `NB_REP`'s exponent is `max 0 (c-ζ)`; in particular `c-ζ` when `c ≥ ζ`. -/
theorem prop8_nbRep_exponent (c ζ : ℝ) :
    nbRepExponent c ζ = max 0 (c - ζ) := rfl

/-- `INIT`'s exponent is `1` (p.9: `INIT = N^{1+o(1)}`, from
`|H_{v,α} ∩ C| = N^{o(1)}` per point and `N^{1+o(1)}` points). -/
theorem prop8_init : initExponent = 1 := rfl

/-- `FAS`'s exponent is `1-c` (p.9: `FAS = N^{1-c}·FAS₁`). -/
theorem prop8_fas (c : ℝ) : fasExponent c = 1 - c := rfl

/-- The two summands of `T`: the walk repetition term `N^{1+c-ζ}` and the
initialisation/FindAllSolutions term `N^{1+c1+ρ}` (p.12). -/
theorem prop8_total_expansion (c c1 ρ ζ : ℝ) :
    totalTimeExponent c c1 ρ ζ = max (1 + c - ζ) (1 + c1 + ρ) := rfl

/-- Proposition 8 with Theorem 4's parameters: the total exponent is `1.2384`
and the repetition exponent `c-ζ = 0.2383` is absorbed by the balanced
`c1 + ρ = 0.2384` term, as the paper notes (`c-ζ = c1`, p.12). -/
theorem prop8_theorem4_balance :
    totalTimeExponent (3696 / 10000) (2384 / 10000) 0 (1313 / 10000) = 12384 / 10000 := by
  unfold totalTimeExponent
  rw [max_eq_right (by norm_num)]
  norm_num

end Qatlib.Papers.LatticeSieve21.MainResults.Complexity
