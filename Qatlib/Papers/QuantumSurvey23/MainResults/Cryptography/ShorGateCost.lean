/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c010 — Shor's algorithm: gate counts and the asymptotic separation

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 6.1 (arXiv source lines 5547–5553).

Source conclusion: Shor's algorithm uses `Õ(n²)` gates with fast multiplication
(and `O(n³)` with schoolbook multiplication) for an `n`-bit modulus.  Factoring
is superpolynomial for the best known classical algorithms, and elliptic-curve
discrete logarithms are exponential classically.  The survey also notes that no
tight *lower* bounds are known; we do not formalize absence of lower bounds.

Formalization notes:
* `shorFastGates n = n² · (log₂ n + 1)`,
* `shorPlainGates n = n³`,
* `superpolyCost n = n^n` (a representative superpolynomial classical cost).

The substantive theorems are `fast_gates_within_cubic` (`Õ(n²) ≤ O(n³)`),
`superpolynomial_speedup` (any fixed power of the Shor cost is eventually below
`n^n`), and `exponential_speedup_ecdlp` (any fixed power of the Shor cost is
eventually below `2^n`, the ECDLP scale).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Cryptography

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Gate count of Shor with fast multiplication: `Õ(n²)`. -/
def shorFastGates (n : ℕ) : ℕ := n ^ 2 * (Nat.log2 n + 1)

/-- Gate count of Shor with schoolbook multiplication: `O(n³)`. -/
def shorPlainGates (n : ℕ) : ℕ := n ^ 3

/-- A representative superpolynomial classical factoring cost: `n^n`. -/
def superpolyCost (n : ℕ) : ℕ := n ^ n

/-- **c010a (Section 6.1).** With fast multiplication the Shor gate count
is `Õ(n²)` and therefore within the cubic schoolbook bound. -/
theorem fast_gates_within_cubic (n : ℕ) (hn : 2 ≤ n) :
    shorFastGates n ≤ shorPlainGates n := by
  unfold shorFastGates shorPlainGates
  have hlog : Nat.log2 n + 1 ≤ n := by
    have h : Nat.log2 n < n := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_self 2 (by omega)
    omega
  calc n ^ 2 * (Nat.log2 n + 1) ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hlog
    _ = n ^ 3 := by ring

/-- **c010b (Section 6.1).** Factoring is superpolynomial: for every fixed
power `k` and constant `C` there is a modulus size `n` at which the classical
cost `n^n` exceeds `C` times the `k`-th power of the Shor gate count. -/
theorem superpolynomial_speedup (C k : ℕ) :
    ∃ n : ℕ, C * (shorPlainGates n) ^ k < superpolyCost n := by
  refine ⟨C + 3 * k + 2, ?_⟩
  set n : ℕ := C + 3 * k + 2 with hn_def
  have hn3 : 3 * k + 1 ≤ n := by omega
  have hnC : C < n := by omega
  have hnpos : 0 < n := by omega
  have h4 : shorPlainGates n ^ k = n ^ (3 * k) := by
    unfold shorPlainGates
    rw [← pow_mul]
  have h1 : C * n ^ (3 * k) < n * n ^ (3 * k) :=
    Nat.mul_lt_mul_of_pos_right hnC (pow_pos hnpos (3 * k))
  have h2 : n * n ^ (3 * k) = n ^ (3 * k + 1) := by
    rw [pow_succ]
    ring
  have h3 : n ^ (3 * k + 1) ≤ n ^ n := Nat.pow_le_pow_right (by omega : 0 < n) hn3
  show C * (shorPlainGates n) ^ k < superpolyCost n
  unfold superpolyCost
  rw [h4]
  calc C * n ^ (3 * k) < n * n ^ (3 * k) := h1
    _ = n ^ (3 * k + 1) := h2
    _ ≤ n ^ n := h3

/-- **c010c (Section 6.1).** Elliptic-curve discrete logarithms are
exponential classically: for every fixed power of the Shor gate count and every
constant `C`, some modulus size beats the exponential classical cost `2^n`. -/
theorem exponential_speedup_ecdlp (C k : ℕ) :
    ∃ n : ℕ, C * (shorPlainGates n) ^ k < expCost n := by
  obtain ⟨N, hN⟩ := expCost_dominates_poly C (3 * k)
  refine ⟨N, ?_⟩
  have h4 : shorPlainGates N ^ k = N ^ (3 * k) := by
    unfold shorPlainGates
    rw [← pow_mul]
  rw [h4]
  have hle : C * N ^ (3 * k) ≤ polyCost C (3 * k) N := by
    unfold polyCost
    exact Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega : N ≤ N + 1) (3 * k))
  exact lt_of_le_of_lt hle (hN N le_rfl)

/-- **c010 (Section 6.1), combined assessment.** Fast multiplication
keeps Shor within `O(n³)`; factoring is superpolynomial, and ECDLP exponential,
relative to any fixed power of the Shor gate count. -/
theorem shor_gate_assessment (n C k : ℕ) (hn : 2 ≤ n) :
    shorFastGates n ≤ shorPlainGates n ∧
    (∃ m, C * (shorPlainGates m) ^ k < expCost m) :=
  ⟨fast_gates_within_cubic n hn, exponential_speedup_ecdlp C k⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Cryptography
