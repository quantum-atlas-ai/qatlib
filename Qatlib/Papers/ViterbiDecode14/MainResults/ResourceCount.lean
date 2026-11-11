/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ResourceCount — the QVA's gate and time accounting

Grice--Meyer, *A quantum algorithm for Viterbi decoding of classical convolutional
codes*, fixed arXiv:1405.7479v2 (PDF dated 2015-06-20):

* Section 1, printed p. 2: "A single iteration of the QVA will be shown to have gate
  complexity `O(N |Q| F (log F)^2)` and time complexity `O(N log F)`, if `|Q|` quantum
  systems can be manipulated simultaneously.";
* Section 2.2, printed p. 5: the course (6) "implements `N` of the `V_y` blocks, each of
  which are composed of `Q` controlled operations, for a gate complexity of
  `O(NQF (log F)^2)`", and the improved `G_φ` as `H_{F^N}`, `F^N` commuting marking
  operators and `G_{F^N}`, each implementable "with gate complexity `log(F^N)`";
* Section 2.3, printed p. 8: implementing `V` needs `K ≤ F` rotation operators plus
  subspace-changing logic costing `f^2 2^f` operations per `V` (with `F = 2^f`), "or
  `F (log F)^2`";
* Section 1, printed pp. 2-3: "the number of iterations in general can be up to
  `O(√L)` as in Grover's algorithm", and p. 4: "up to `Real.pi/4 √L` lattice building and
  amplifications steps, where `L = F^N` is the number of states to search", so that
  "if using the maximal amount of parallelism, the QVA decodes the convolutional code in
  time `O(√(F^N) N log F)`".

This module formalizes that accounting for the binary convolutional codes of Section 3,
where the fanout is `F = 2^f` (`f` = number of message bits):

* `grayLogicCost` / `fanoutCost` and `fanoutCost_eq` — the source's two spellings
  `f^2 2^f` and `F (log F)^2` are the same number;
* `iterationGateCost_eq` — one iteration costs exactly `N |Q| F (log F)^2`
  (`N` blocks of Eq. (6), `|Q|` controlled gates per block of Eq. (5), the Gray-code
  subspace-change logic per `U_ψ`);
* `layerDepth_eq` — the improved `G_φ` leaves `log(F^N) = N log F` gates per layer,
  which is the source's per-iteration time `O(N log F)` under `|Q|`-fold parallelism;
* `decodeTime_le` / `decodeTime_le_const` — with the source's `Real.pi/4 √(F^N)` amplification
  count, the total time is at most `(Real.pi/4 + 1) √(F^N) · N log F`.

Boundary. These are the source's own counting arguments, formalized as arithmetic
identities and explicit bounds on the step count. There is no gate-level circuit model in
this module: the identity `iterationGateCost_eq` counts the source's declared building
blocks (`|Q|` controlled `U_ψ` gates per block, each `U_ψ` priced at the source's
Gray-code logic), it does not re-derive the Gray-code synthesis itself. The asymptotic
`O(·)` statements are therefore recorded as the explicit inequalities
`decodeTime ≤ (Real.pi/4 + 1) · √(F^N) · N log F` rather than as asymptotics over a family of
circuits, and the `+1` layer of the ceiling is kept visible instead of being absorbed.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ViterbiDecode14.MainResults

/-- The binary fanout `F = 2^f` of Section 2.3: `f` is the number of bits in a message
block, so a state of the hidden Markov model branches to at most `2^f` successors. -/
def fanout (f : ℕ) : ℕ := 2 ^ f

/-- The source's Gray-code subspace-change cost `f^2 2^f` for one `U_ψ` (Section 2.3,
printed p. 8), obtained from Nielsen--Chuang's universal Gray-code construction. -/
def grayLogicCost (f : ℕ) : ℕ := f ^ 2 * 2 ^ f

/-- The source's other spelling `F (log F)^2` of the per-`V` subspace-change cost. -/
def fanoutCost (F : ℕ) : ℕ := F * (Nat.log2 F) ^ 2

/-- Section 2.3: for the binary fanout `F = 2^f`, `F (log F)^2` is exactly `f^2 2^f`. -/
theorem fanoutCost_eq (f : ℕ) : fanoutCost (fanout f) = grayLogicCost f := by
  unfold fanoutCost fanout grayLogicCost
  rw [Nat.log2_two_pow]
  exact mul_comm _ _

/-- One `V_y` block of Eq. (5) is a bundle of `|Q|` controlled `U_ψ` operations
(Section 2.1, printed p. 5). -/
def blockGateCost (Q f : ℕ) : ℕ := Q * grayLogicCost f

/-- One QVA iteration: the `N` blocks of the course (6). -/
def iterationGateCost (N Q f : ℕ) : ℕ := N * blockGateCost Q f

/-- Section 1 / Section 2.2, gate side: one QVA iteration costs exactly
`N |Q| F (log F)^2` gates for the binary fanout `F = 2^f`. -/
theorem iterationGateCost_eq (N Q f : ℕ) :
    iterationGateCost N Q f = N * Q * fanout f * (Nat.log2 (fanout f)) ^ 2 := by
  unfold iterationGateCost blockGateCost grayLogicCost fanout
  rw [Nat.log2_two_pow]
  ring

/-- Section 2.2's improved `G_φ`: `H_{F^N}`, the marking layer and the inversion are
each implementable with `log(F^N)` gates, and they are a single layer of the circuit. -/
def layerDepth (N f : ℕ) : ℕ := Nat.log2 (fanout f ^ N)

/-- Section 1 / Section 2.2, time side: `log(F^N) = N log F = N f` for the binary
fanout, which is the source's per-iteration time `O(N log F)` once the `|Q|` controlled
operations are performed in parallel. -/
theorem layerDepth_eq (N f : ℕ) : layerDepth N f = N * f := by
  unfold layerDepth fanout
  rw [← pow_mul, Nat.log2_two_pow]
  exact mul_comm _ _

/-- The source's maximal-parallelism amplification count `Real.pi/4 √L` with `L = F^N`
(printed p. 4), rounded up because a number of steps is a natural number. -/
def iterationCount (N f : ℕ) : ℕ := Nat.ceil ((Real.pi / 4) * Real.sqrt ((fanout f : ℝ) ^ N))

/-- The source's quantum speedup at maximal parallelism: `O(√L)` iterations, so at most
`Real.pi/4 √(F^N)` plus the rounding layer. -/
theorem iterationCount_le (N f : ℕ) :
    (iterationCount N f : ℝ) ≤ (Real.pi / 4) * Real.sqrt ((fanout f : ℝ) ^ N) + 1 := by
  unfold iterationCount
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (Real.pi / 4) * Real.sqrt ((fanout f : ℝ) ^ N) by
    positivity)
  linarith

/-- Total decoding time with maximal parallelism: the source's amplification count times
the per-iteration time `N log F`. -/
def decodeTime (N f : ℕ) : ℝ := (iterationCount N f : ℝ) * (N * (f : ℝ))

/-- Section 1, p. 2: with the maximal amount of parallelism the QVA decodes the
convolutional code in time `O(√(F^N) N log F)`; the explicit bound keeps the ceiling's
extra layer. -/
theorem decodeTime_le (N f : ℕ) :
    decodeTime N f ≤ ((Real.pi / 4) * Real.sqrt ((fanout f : ℝ) ^ N) + 1) * (N * (f : ℝ)) := by
  unfold decodeTime
  have h := iterationCount_le N f
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) * (f : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right h hnonneg

/-- Section 1, p. 2 with the rounding layer absorbed into the constant: whenever the
search space has at least one state the decoding time is at most
`(Real.pi/4 + 1) √(F^N) · N log F`. -/
theorem decodeTime_le_const (N f : ℕ)
    (hL : 1 ≤ Real.sqrt ((fanout f : ℝ) ^ N)) :
    decodeTime N f ≤
      (Real.pi / 4 + 1) * (Real.sqrt ((fanout f : ℝ) ^ N) * (N * (f : ℝ))) := by
  have h := decodeTime_le N f
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) * (f : ℝ) := by positivity
  have hstep : (Real.pi / 4) * Real.sqrt ((fanout f : ℝ) ^ N) + 1 ≤
      (Real.pi / 4 + 1) * Real.sqrt ((fanout f : ℝ) ^ N) := by
    nlinarith
  have := mul_le_mul_of_nonneg_right hstep hnonneg
  calc decodeTime N f
      ≤ ((Real.pi / 4) * Real.sqrt ((fanout f : ℝ) ^ N) + 1) * (N * (f : ℝ)) := h
    _ ≤ ((Real.pi / 4 + 1) * Real.sqrt ((fanout f : ℝ) ^ N)) * (N * (f : ℝ)) := this
    _ = (Real.pi / 4 + 1) * (Real.sqrt ((fanout f : ℝ) ^ N) * (N * (f : ℝ))) := by ring

end Qatlib.Papers.ViterbiDecode14.MainResults
