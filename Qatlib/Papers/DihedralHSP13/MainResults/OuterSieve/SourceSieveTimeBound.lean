/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Kuperberg 2013, Proposition 4.5: the 2^{O(√n)} outer sieve

Source: Greg Kuperberg, *Another subexponential-time quantum algorithm for the dihedral
hidden subgroup problem*, arXiv:1112.3333v1 (TQC 2013), Proposition 4.5, Section 4.6,
page 9 (txt line 556, PDF p. 9), proved on pages 9–10 (txt lines 558–600).

The proposition: the modified form of Algorithm 4.4 uses quantum time and classical space
`2^{O(√n)}`, and quantum space `O(log n)`, where `n = m²` is the height of the initial phase
vector (`n = log N`) and `m` is the stage parameter of the sieve.

The paper's proof has two layers:

1. *Heuristics*: the algorithm runs `√n = m` stages, each collimating phase vectors of the
   `2^{O(m)}`-entry phase-multiplier table; the per-stage quantum time is therefore `2^{O(m)}`,
   giving `2^{O(√n)}` in total, and only a `⌈log₂ n⌉`-qubit residual qudit is kept, giving
   `O(log n)` quantum space.
2. *Rigor*: the modified algorithm succeeds at every stage with probability bounded away from
   `0`, because each local failure mode (too-short intermediate vector, too-short final
   remnant, trivial final phase multiplier) has failure probability at most `1/4`, `1/4`,
   and `1/3` respectively: "with probability at least `3/4`, [the bucket] has size
   `ℓ₁ ≥ ℓ₀`; then the trimming measurement produces a phase vector of length exactly `ℓ₀`
   with probability at least `1/2`", and at the last stage "a qudit of length `ℓ₂ ≥ 2` with
   probability at least `3/4`; the trimming measurement produces a qubit with probability at
   least `2/3`".  Hence the overall success probability is at least `(3/4)·(1/2)·(2/3) = 1/4`
   per attempt, and a constant number of repetitions (absorbed into the `2^{O(√n)}` time)
   succeeds.

## Contents

* `SieveParams`: the sieve parameters — height `n`, stage parameter `m`, and the paper's
  relation `n = m * m`.
* `SieveLedger`, `modifiedAlgorithm44`: the resource interface and the `2^{O(√n)}` ledger of
  the modified Algorithm 4.4 (`m` stages of `2^{O(m)}` quantum time, a `2^{O(m)}`-bit
  classical table, and an `O(log n)`-qubit residual register).
* `succ_le_two_pow_succ`: the elementary `m + 1 ≤ 2^{m+1}` used to absorb the stage count
  into the exponent.
* `prop45_modified_algorithm44`: `∃ C > 0`, for every sieve instance, quantum time and
  classical space at most `2^{C·(√n + 1)}` and quantum space at most `C·(log n + 1)`
  (proved, with the explicit constant `C = 3`).

The modelling boundary is the same as for Proposition 4.2: the ledger is the paper's
accounting, not a resource count extracted from a Lean implementation of Algorithm 4.4, and
the success-probability analysis (the `3/4`, `1/2`, `2/3` bounds) is not formalized; it is
documented above and in the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DihedralHSP13.MainResults.OuterSieve

/-- The parameters of the outer sieve: `n = m * m` is the height of the initial phase vector
(`n = log N`) and `m = √n` is the stage parameter of Algorithm 4.4 (§4.6). -/
structure SieveParams where
  /-- The height `n` of the phase vector, i.e. `n = log N`. -/
  height : ℕ
  /-- The stage parameter `m = √n`. -/
  m : ℕ
  /-- The paper's choice `n = m²`. -/
  square : height = m * m

/-- The resource ledger of the outer sieve. -/
structure SieveLedger where
  /-- Quantum computation time (elementary quantum gates). -/
  quantumTime : ℕ
  /-- Classical space (bits). -/
  classicalSpace : ℕ
  /-- Quantum space (qubits). -/
  quantumSpace : ℕ

/-- The resource ledger of the modified Algorithm 4.4 (§4.6): `m + 1` stages, each with a
phase-multiplier table of `2^{m+1}` entries (`O(m)` bits per entry, so `2^{O(m)}` classical
bits), each stage costing `2^{O(m)}` quantum time (the collimation of `2^{m+1}` entries), and
the whole computation keeping only the `O(log n)`-qubit residual register. -/
def modifiedAlgorithm44 (S : SieveParams) : SieveLedger where
  quantumTime := (S.m + 1) * 2 ^ (S.m + 1)
  classicalSpace := 2 ^ (2 * (S.m + 1))
  quantumSpace := 2 * (Nat.log 2 S.height + 1)

/-- `m + 1 ≤ 2^{m+1}`: the stage count is absorbed into the exponent, the step that turns
`m · 2^{O(m)}` into `2^{O(m)}`. -/
theorem succ_le_two_pow_succ (m : ℕ) : m + 1 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    have h1 : k + 1 + 1 ≤ 2 * (k + 1) := by omega
    have h2 : 2 * (k + 1) ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
    calc k + 1 + 1 ≤ 2 * (k + 1) := h1
      _ ≤ 2 * 2 ^ (k + 1) := h2
      _ = 2 ^ (k + 1 + 1) := by rw [Nat.pow_succ]; ring

/-- **Proposition 4.5** (Kuperberg 2013, §4.6, p. 9, txt line 556).  The modified form of
Algorithm 4.4 uses quantum time and classical space `2^{O(√n)}` and quantum space
`O(log n)`. -/
theorem prop45_modified_algorithm44 :
    ∃ C : ℕ, 0 < C ∧ ∀ S : SieveParams,
      (modifiedAlgorithm44 S).quantumTime ≤ 2 ^ (C * (Nat.sqrt S.height + 1)) ∧
        (modifiedAlgorithm44 S).classicalSpace ≤ 2 ^ (C * (Nat.sqrt S.height + 1)) ∧
          (modifiedAlgorithm44 S).quantumSpace ≤ C * (Nat.log 2 S.height + 1) := by
  refine ⟨3, by norm_num, ?_⟩
  intro S
  have hsq : Nat.sqrt S.height = S.m := by rw [S.square, Nat.sqrt_eq]
  refine ⟨?_, ?_, ?_⟩
  · -- quantum time: `(m + 1) · 2^{m+1} ≤ 2^{m+1} · 2^{m+1} = 2^{2(m+1)} ≤ 2^{3(√n+1)}`
    show (S.m + 1) * 2 ^ (S.m + 1) ≤ 2 ^ (3 * (Nat.sqrt S.height + 1))
    rw [hsq]
    calc (S.m + 1) * 2 ^ (S.m + 1) ≤ 2 ^ (S.m + 1) * 2 ^ (S.m + 1) :=
          Nat.mul_le_mul_right _ (succ_le_two_pow_succ S.m)
      _ = 2 ^ ((S.m + 1) + (S.m + 1)) := (Nat.pow_add 2 (S.m + 1) (S.m + 1)).symm
      _ = 2 ^ (2 * (S.m + 1)) := by rw [two_mul]
      _ ≤ 2 ^ (3 * (S.m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- classical space: `2^{2(m+1)} ≤ 2^{3(m+1)}`
    show 2 ^ (2 * (S.m + 1)) ≤ 2 ^ (3 * (Nat.sqrt S.height + 1))
    rw [hsq]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · -- quantum space: `2 · (log n + 1) ≤ 3 · (log n + 1)`
    show 2 * (Nat.log 2 S.height + 1) ≤ 3 * (Nat.log 2 S.height + 1)
    omega

end Qatlib.Papers.DihedralHSP13.MainResults.OuterSieve
