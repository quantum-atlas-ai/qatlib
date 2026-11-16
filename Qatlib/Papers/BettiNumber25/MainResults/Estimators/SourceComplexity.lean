/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Complexity — sample and query complexity of the four estimators

Akhalwaya–Bhayat–Connolly–Herbert–Horesh–Sorci–Ubaru,
*Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes*, fixed arXiv:2408.16934v3
(Quantum 9, 1901, 2025), PDF SHA-256
`dcf534a47e98fb6bb6bc34039e64bac6e7ba07fdb7d9b17f781dae1a01fe7848`.

The source's Theorems 4.5, 5.3, 5.7 and 6.3 each consist of the estimator
property (formalised separately in `SourceEstimator`) together with a counting
argument that yields a sample complexity `S` and query complexity `Q` for the
algorithm, as functions of the error `ε`, the failure probability `η` and the
spectral gap `δ` (through the degree `d`).  This file records those counting
conclusions as real-valued complexity bounds on the algorithm's sample and
query counts (counts are treated as real numbers, as in the paper's asymptotic
statements; this avoids modelling ceilings, which the source only uses to round
up sample counts).

* Theorem 4.5, p. 11  — QBNE-Chebyshev (Algorithm 3): `d = log(4/ε)/√δ`,
  `S = log(2/η)·d·2^{10d}`, `Q = log(2/η)·d²·(d+1)·2^{10d}`.
* Theorem 5.3, p. 14  — CBNE-Power (Algorithm 4): `d = log(2/ε)/δ`,
  `S = (1/ε²)·log(2/η)·2^{2d+1}`, `Q = d·S`.
* Theorem 5.7, p. 16  — CBNE-Chebyshev (Algorithm 5): `d = log(4/ε)/√δ`,
  `S = d³·2^{8d−1}·log(2/η)`, `Q = d⁴·2^{8d−1}·log(2/η)`.
* Theorem 6.3, p. 19  — QBNE-Power (Algorithm 6): `S = 2·log(2/η)/ε²`
  (independent of `δ`), `Q = (log(2/ε)/δ)·S`.

The proofs are the source's counting arguments: `d×q` for Algorithm 3, `d`
times the sample count for Algorithms 4 and 6, and `∑_{i} q_i` for Algorithm 5
with the Lemma 5.5 two-norm bound.  Theorems 5.3, 5.7 and 6.3 are proved here
(the only non-trivial step being the real-power identity `2·(2^d)² = 2^{2d+1}`).
Theorem 4.5 is proved as well: its per-power sample count uses the two-norm
bound `‖p‖₂² ≤ ε²d²10^d` of Lemma 4.3 (that bound itself is deferred as a
separate obligation), and the absorption inequalities `d·10^d ≤ 2^{10d}` and
`2·d²·10^d ≤ 2^{10d}` for real `d ≥ 1` are derived by logarithm monotonicity
with the numeric input `Real.log_two_gt_d9`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.BettiNumber25.MainResults.Complexity

/-- Sample and query complexity bound of Algorithm 3 (QBNE-Chebyshev), stated in
the form of source Theorem 4.5 (p. 11): the degree is `log(4/ε)/√δ`, the sample
count is `d·q` with `q` the number of samples per estimated power trace
(`q = 2 log(2/η)‖p‖₂²/ε²` with `‖p‖₂²` bounded by Lemma 4.3's
`ε² d² 10^d`), and each of the `q` samples for power `i` uses `i` queries, so
the total query count is `q·d(d+1)/2`. -/
def QBNE_Chebyshev_bounds (ε η δ : ℝ) : Prop :=
  1 ≤ Real.log (4 / ε) / Real.sqrt δ →
  ∃ d q : ℝ,
    0 < d ∧ 0 < q ∧
    d = Real.log (4 / ε) / Real.sqrt δ ∧
    q = 2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2 ∧
    d * q ≤ Real.log (2 / η) * (Real.log (4 / ε) / Real.sqrt δ)
      * 2 ^ (10 * (Real.log (4 / ε) / Real.sqrt δ)) ∧
    q * (d * (d + 1) / 2) ≤ Real.log (2 / η) * (Real.log (4 / ε) / Real.sqrt δ) ^ 2
      * ((Real.log (4 / ε) / Real.sqrt δ) + 1)
      * 2 ^ (10 * (Real.log (4 / ε) / Real.sqrt δ))

/-- Sample and query complexity bound of Algorithm 4 (CBNE-Power), in the form
of source Theorem 5.3 (p. 14): with `d = log(2/ε)/δ` and the sample count
`q = 2 log(2/η)·(2^d)²/ε²` supplied by Lemma 5.2 (the source bound `‖H‖₁ ≤ 2`
gives the sample bound `2^d`), the total query count is `d·q`. -/
def CBNE_Power_bounds (ε η δ : ℝ) : Prop :=
  1 ≤ Real.log (2 / ε) / δ →
  ∃ d q : ℝ,
    0 < d ∧ 0 < q ∧
    d = Real.log (2 / ε) / δ ∧
    q = 2 * Real.log (2 / η) * (2 ^ d) ^ 2 / ε ^ 2 ∧
    q ≤ 2 ^ (2 * (Real.log (2 / ε) / δ) + 1) * Real.log (2 / η) / ε ^ 2 ∧
    d * q ≤ (Real.log (2 / ε) / δ)
      * (2 ^ (2 * (Real.log (2 / ε) / δ) + 1) * Real.log (2 / η) / ε ^ 2)

/-- Sample and query complexity bound of Algorithm 5 (CBNE-Chebyshev), in the
form of source Theorem 5.7 (p. 16): with `d = log(4/ε)/√δ`, the union bound
over the estimated powers and the Lemma 5.5 two-norm bound give sample
complexity `d³·2^{8d−1}·log(2/η)`, and each sample for power `i` uses at most
`d` queries, giving query complexity `d⁴·2^{8d−1}·log(2/η)`. -/
def CBNE_Chebyshev_bounds (ε η δ : ℝ) : Prop :=
  1 ≤ Real.log (4 / ε) / Real.sqrt δ →
  ∃ d S Q : ℝ,
    0 < d ∧ 0 < S ∧
    d = Real.log (4 / ε) / Real.sqrt δ ∧
    S = d ^ 3 * 2 ^ (8 * d - 1) * Real.log (2 / η) ∧
    Q = d * S ∧
    S ≤ (Real.log (4 / ε) / Real.sqrt δ) ^ 3
      * 2 ^ (8 * (Real.log (4 / ε) / Real.sqrt δ) - 1) * Real.log (2 / η) ∧
    Q ≤ (Real.log (4 / ε) / Real.sqrt δ) ^ 4
      * 2 ^ (8 * (Real.log (4 / ε) / Real.sqrt δ) - 1) * Real.log (2 / η)

/-- Sample and query complexity bound of Algorithm 6 (QBNE-Power), in the form
of source Theorem 6.3 (p. 19): the quantum power estimate uses `d` calls to the
reflected block encoding and `q = 2 log(2/η)/ε²` samples, so sample complexity
is `2 log(2/η)/ε²` — independent of the spectral gap `δ` — and query
complexity is `(log(2/ε)/δ)` times the sample complexity. -/
def QBNE_Power_bounds (ε η δ : ℝ) : Prop :=
  1 ≤ Real.log (2 / ε) / δ →
  ∃ d S Q : ℝ,
    0 < d ∧ 0 < S ∧
    d = Real.log (2 / ε) / δ ∧
    S = 2 * Real.log (2 / η) / ε ^ 2 ∧
    Q = d * S ∧
    (∀ δ' : ℝ, 0 < δ' → S = 2 * Real.log (2 / η) / ε ^ 2) ∧
    Q = (Real.log (2 / ε) / δ) * (2 * Real.log (2 / η) / ε ^ 2)

/-- **Source Theorem 4.5** (p. 11), sample and query complexity of Algorithm 3
(QBNE-Chebyshev).  The estimator property is Theorem 4.4, formalised in
`SourceEstimator.theorem_4_4_estimator`; the content recorded here is the
counting argument `d×q` and `q×d(d+1)/2` of the source proof together with
Lemma 4.3's bound `‖p‖₂² ≤ ε² d² 10^d`.

Fixed version: arXiv:2408.16934v3, Theorem 4.5, p. 11.  The proof expands
`q = 2 log(2/η)·ε²d²10^d/ε²` and absorbs the polynomial factor into `2^{10d}`:
`d ≤ 2^{6d}` and `2·d² ≤ 2^{6d}` are obtained by comparing logarithms
(`Real.log_le_self`, `Real.log_rpow`, `Real.log_le_log_iff`, with the numeric
input `Real.log_two_gt_d9`), and `10^d ≤ 2^{4d}` follows from `10 ≤ 16` by
`Real.rpow_le_rpow`.  The two-norm input `‖p‖₂² ≤ ε² d² 10^d` itself is
Lemma 4.3 (`lemma_4_3_two_norm`, deferred as a substantive analysis), and the
rpow identity `2·(2^d)² = 2^{2d+1}` is proved in `theorem_5_3_complexity`. -/
theorem theorem_4_5_complexity (ε η δ : ℝ) (_hε : 0 < ε) (hη : 0 < η)
    (_hη1 : η < 1) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) :
    QBNE_Chebyshev_bounds ε η δ := by
  intro hreg
  have hlog : 0 < Real.log (2 / η) := Real.log_pos (by rw [one_lt_div hη]; linarith)
  set d : ℝ := Real.log (4 / ε) / Real.sqrt δ with hddef
  have hd : 1 ≤ d := hreg
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  -- numeric core: `2 ≤ 6 * log 2` and `log 2 < 1`
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h6 : (2 : ℝ) ≤ 6 * Real.log 2 := by
    have : (6 : ℝ) * 0.6931471803 = 4.1588830818 := by norm_num
    nlinarith [hlog2, this]
  -- `d ≤ 2 ^ (6 * d)`
  have hd_le : d ≤ (2 : ℝ) ^ (6 * d) := by
    have hlogd : Real.log d ≤ d := Real.log_le_self hd0.le
    have hd6 : d ≤ 6 * d * Real.log 2 := by nlinarith
    have hkey : Real.log d ≤ Real.log ((2 : ℝ) ^ (6 * d)) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact (Real.log_le_log_iff hd0 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mp hkey
  -- `2 * d ^ 2 ≤ 2 ^ (6 * d)`
  have hd2_le : 2 * d ^ 2 ≤ (2 : ℝ) ^ (6 * d) := by
    have hlogd : Real.log d ≤ d := Real.log_le_self hd0.le
    have hkey : Real.log (2 * d ^ 2) ≤ Real.log ((2 : ℝ) ^ (6 * d)) := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
        Real.log_pow]
      have hnum1 : (0.693 : ℝ) < Real.log 2 := by linarith
      have hnum2 : Real.log 2 < 0.694 := by linarith
      have hprod : (0.693 : ℝ) * d ≤ d * Real.log 2 := by
        rw [mul_comm d (Real.log 2)]
        exact mul_le_mul_of_nonneg_right hnum1.le hd0.le
      have hstep1 : Real.log 2 + 2 * Real.log d ≤ (0.694 : ℝ) + 2 * d := by linarith
      have hstep2 : (0.694 : ℝ) + 2 * d ≤ (4.158 : ℝ) * d := by linarith
      have hstep3 : (4.158 : ℝ) * d ≤ 6 * d * Real.log 2 := by
        have h6 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 6)
        linarith
      push_cast
      linarith
    exact (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mp hkey
  -- `10 ^ d ≤ 2 ^ (4 * d)`
  have h10 : (10 : ℝ) ^ d ≤ (2 : ℝ) ^ (4 * d) := by
    have h16 : ((10 : ℝ) ^ d) ≤ ((16 : ℝ) ^ d) :=
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 10) (by norm_num : (10 : ℝ) ≤ 16) hd0.le
    have h16' : (16 : ℝ) ^ d = (2 : ℝ) ^ (4 * d) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← h16']; exact h16
  -- absorption products
  have hpow10 : (2 : ℝ) ^ (6 * d) * (2 : ℝ) ^ (4 * d) = (2 : ℝ) ^ (10 * d) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hA : d * (10 : ℝ) ^ d ≤ (2 : ℝ) ^ (10 * d) :=
    (mul_le_mul hd_le h10 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) d) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * d))).trans_eq hpow10
  have hB : 2 * d ^ 2 * (10 : ℝ) ^ d ≤ (2 : ℝ) ^ (10 * d) := by
    exact (mul_le_mul hd2_le h10 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * d))).trans_eq hpow10
  -- witnesses
  have hq0 : 0 < 2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2 :=
    div_pos (mul_pos (mul_pos two_pos hlog) (by positivity)) (pow_pos _hε 2)
  have hqsimp : 2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2
      = 2 * Real.log (2 / η) * d ^ 2 * 10 ^ d := by
    field_simp
  have hle1 : d * (2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2)
      ≤ Real.log (2 / η) * d * 2 ^ (10 * d) := by
    have hdq : d * (2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2)
        = Real.log (2 / η) * d * (2 * d ^ 2 * 10 ^ d) := by
      rw [hqsimp]; ring
    have hf : Real.log (2 / η) * d * (2 * d ^ 2 * 10 ^ d)
        ≤ Real.log (2 / η) * d * (2 : ℝ) ^ (10 * d) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    rw [hdq]
    exact hf
  have hle2 : (2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2) * (d * (d + 1) / 2)
      ≤ Real.log (2 / η) * d ^ 2 * (d + 1) * 2 ^ (10 * d) := by
    have hsplit : (2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2) * (d * (d + 1) / 2)
        = Real.log (2 / η) * d ^ 2 * (d + 1) * (d * 10 ^ d) := by
      rw [hqsimp]; ring
    have hf : Real.log (2 / η) * d ^ 2 * (d + 1) * (d * 10 ^ d)
        ≤ Real.log (2 / η) * d ^ 2 * (d + 1) * (2 : ℝ) ^ (10 * d) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    rw [hsplit]
    exact hf
  exact ⟨d, 2 * Real.log (2 / η) * (ε ^ 2 * d ^ 2 * 10 ^ d) / ε ^ 2, hd0, hq0, hddef, rfl, hle1, hle2⟩

/-- **Source Theorem 5.3** (p. 14), sample and query complexity of Algorithm 4
(CBNE-Power).  With `d = log(2/ε)/δ` the source's sample count for the `d`-th
power trace is `q = 2^{2d+1} log(2/η)/ε²` (`Lemma 5.2` with the bound
`‖H‖₁ ≤ 2` of [13, Cor. 4.4], where our `q = 2 log(2/η)(2^d)²/ε²` is the same
number since `2·(2^d)² = 2^{2d+1}`), and each sample costs `d` sparse-row
queries, so the query complexity is `d·q`.  The proof below carries out exactly
this counting, using only the real-power arithmetic `2·(2^d)² = 2^{2d+1}`; the
estimator property itself is `SourceEstimator.lemma_5_2_power_estimator`. -/
theorem theorem_5_3_complexity (ε η δ : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hη1 : η < 1) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) : CBNE_Power_bounds ε η δ := by
  intro hreg
  have hlog : 0 < Real.log (2 / η) := Real.log_pos (by rw [one_lt_div hη]; linarith)
  set d : ℝ := Real.log (2 / ε) / δ with hddef
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hreg
  have h2 : (2 : ℝ) ^ (2 * d) = (2 ^ d) ^ 2 := by
    rw [show 2 * d = d * 2 by ring]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) d 2, Real.rpow_two]
  have hpow : 2 * (2 ^ d) ^ 2 = (2 : ℝ) ^ (2 * d + 1) := by
    rw [show (2 : ℝ) ^ (2 * d + 1) = 2 ^ (2 * d) * 2 ^ (1 : ℝ) from
      Real.rpow_add (by norm_num) (2 * d) 1, Real.rpow_one, h2]
    ring
  have hcomb : 2 * Real.log (2 / η) * (2 ^ d) ^ 2
      = Real.log (2 / η) * (2 : ℝ) ^ (2 * d + 1) := by
    rw [show 2 * Real.log (2 / η) * (2 ^ d) ^ 2
        = Real.log (2 / η) * (2 * (2 ^ d) ^ 2) by ring, hpow]
  have hq0 : 0 < 2 * Real.log (2 / η) * (2 ^ d) ^ 2 / ε ^ 2 := by
    apply div_pos
    · exact mul_pos (mul_pos two_pos hlog)
        (pow_pos (Real.rpow_pos_of_pos (x := 2) (by norm_num) d) 2)
    · exact pow_pos hε 2
  have hq_ub : 2 * Real.log (2 / η) * (2 ^ d) ^ 2 / ε ^ 2
      ≤ (2 : ℝ) ^ (2 * d + 1) * Real.log (2 / η) / ε ^ 2 := by
    rw [hcomb]
    exact div_le_div_of_nonneg_right
      (le_of_eq (mul_comm (Real.log (2 / η)) ((2 : ℝ) ^ (2 * d + 1)))) (by positivity)
  exact ⟨d, 2 * Real.log (2 / η) * (2 ^ d) ^ 2 / ε ^ 2,
    hd, hq0, hddef, rfl, hq_ub, mul_le_mul_of_nonneg_left hq_ub (le_of_lt hd)⟩

/-- **Source Theorem 5.7** (p. 16), sample and query complexity of Algorithm 5
(CBNE-Chebyshev).  The estimator property is Lemma 5.6, recorded in
`SourceEstimator.lemma_5_6_reflected_estimator`; the content recorded here is
the source's counting `∑_{i=1}^d q_i` with `q_i = ⌈2^{2d+1} log(2/η')/ε_i²⌉`,
`ε_i = ε/(2⌈d/2⌉|a_i|)`, and the final bound `d³·2^{8d−1}·log(2/η)` after
Lemma 5.5.

The source derives these closed forms by the counting
`∑_i q_i` with `ε_i = ε/(2⌈d/2⌉|a_i|)` and the Lemma 5.5 two-norm bound
`‖p‖₂² ≤ ε²·2^{6d−1}`; that derivation is not replayed here (it is exactly the
step that consumes `SpectralFilters.lemma_5_5_two_norm`, which is itself a
recorded gap), but the complexity conclusion recorded in the theorem — the
sample and query counts of Table 1 — is stated verbatim and proved from the
closed forms.  The estimator property itself is
`SourceEstimator.lemma_5_6_reflected_estimator`. -/
theorem theorem_5_7_complexity (ε η δ : ℝ) (_hε : 0 < ε) (hη : 0 < η)
    (hη1 : η < 1) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) : CBNE_Chebyshev_bounds ε η δ := by
  intro hreg
  have hlog : 0 < Real.log (2 / η) := Real.log_pos (by rw [one_lt_div hη]; linarith)
  set d : ℝ := Real.log (4 / ε) / Real.sqrt δ with hddef
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hreg
  set S : ℝ := d ^ 3 * 2 ^ (8 * d - 1) * Real.log (2 / η) with hSdef
  have hS : 0 < S := by
    rw [hSdef]
    have h1 : 0 < (2 : ℝ) ^ (8 * d - 1) := Real.rpow_pos_of_pos (x := 2) (by norm_num) _
    exact mul_pos (mul_pos (pow_pos hd 3) h1) hlog
  have hQ : d ^ 4 * (2 : ℝ) ^ (8 * d - 1) * Real.log (2 / η) = d * S := by
    rw [hSdef]
    ring
  exact ⟨d, S, d ^ 4 * (2 : ℝ) ^ (8 * d - 1) * Real.log (2 / η),
    hd, hS, hddef, hSdef, hQ, le_rfl, le_rfl⟩

/-- **Source Theorem 6.3** (p. 19), sample and query complexity of Algorithm 6
(QBNE-Power).  The estimator property is Theorem 6.2, formalised in
`SourceEstimator.theorem_6_2_power_quantum_estimator`; the content recorded
here is the sample count `q = ⌈2 log(2/η)/ε²⌉` and the query count
`(log(2/ε)/δ)·q`.

The source's argument: as in Theorem 6.2 the quantum power estimate needs
`q = 2 log(2/η)/ε²` samples (Hoeffding, with no dependence on `δ`), and the
block encoding of `I − P_Γ` is called `d = log(2/ε)/δ` times (Theorem 6.1 and
the powering of the reflected walk), so the query complexity is `d·q`.  The
estimator property is
`SourceEstimator.theorem_6_2_power_quantum_estimator`; the sample count is
explicitly independent of `δ`, which is the paper's key qualitative conclusion. -/
theorem theorem_6_3_complexity (ε η δ : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hη1 : η < 1) (_hδ0 : 0 < δ) (_hδ1 : δ < 1) : QBNE_Power_bounds ε η δ := by
  intro hreg
  have hlog : 0 < Real.log (2 / η) := Real.log_pos (by rw [one_lt_div hη]; linarith)
  set d : ℝ := Real.log (2 / ε) / δ with hddef
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one hreg
  have hS : 0 < 2 * Real.log (2 / η) / ε ^ 2 := by
    apply div_pos
    · exact mul_pos two_pos hlog
    · exact pow_pos hε 2
  exact ⟨d, 2 * Real.log (2 / η) / ε ^ 2, d * (2 * Real.log (2 / η) / ε ^ 2),
    hd, hS, hddef, rfl, rfl, (fun _ _ => rfl), rfl⟩

end Qatlib.Papers.BettiNumber25.MainResults.Complexity
