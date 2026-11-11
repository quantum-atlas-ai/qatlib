/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermEigState17.MainResults.CostModel.SourceCostModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# FermEigState17 Claim c002 — quantum Fisher–Yates antisymmetrization

Fixed paper version: **arXiv:1711.10460**, Appendix C (p. 13), with the
resource summary also stated in Section II (p. 4).

The alternative antisymmetrization performs `η − 1` quantum Fisher–Yates blocks
on an `η`-element array of `log N`-bit registers.  The paper's step-by-step cost
table (Appendix C, p. 13) is:

* Step 1 (initialization): `O(η log η)` gates, depth `O(1)`;
* Step 2 (prepare choice): `O(η)` gates and the same depth complexity;
* Step 3 (execute swap): `O(η log N)` gates and depth `O(η log N)`;
* Step 4 (reset choice): `O(η log η)` gates, depth `O(log η)`;
* Steps 2–4 are repeated `η − 1` times;
* Step 6 (disentangle index/input): `O(η² log N)` gates and depth
  `O(η² [log log N + log η])`.

Since Steps 2–4 run `η − 1` times, the total gate count is `O(η² log N)`, and
because most gates are sequential the overall circuit depth is also
`O(η² log N)`.  This file freezes that per-step profile and proves the stated
composition, encoding `O` with the positive representatives of `CostModel`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermEigState17.MainResults.FisherYatesCost

open Qatlib.Papers.FermEigState17.MainResults.CostModel

/-- Cost profile of the quantum Fisher–Yates antisymmetrization (Appendix C).
`step2`–`step4` are one-shot per block; the algorithm repeats them `η − 1`
times.  All fields are nonnegative. -/
structure FisherYatesProfile where
  /-- gates / depth of the initialization (Step 1) -/
  step1Gates : ℝ
  step1Depth : ℝ
  /-- gates / depth of "prepare choice" per block (Step 2) -/
  step2Gates : ℝ
  step2Depth : ℝ
  /-- gates / depth of "execute swap" per block (Step 3) -/
  step3Gates : ℝ
  step3Depth : ℝ
  /-- gates / depth of "reset choice" per block (Step 4) -/
  step4Gates : ℝ
  step4Depth : ℝ
  /-- gates / depth of the final disentangling step (Step 6) -/
  step6Gates : ℝ
  step6Depth : ℝ
  step1Gates_nonneg : 0 ≤ step1Gates
  step1Depth_nonneg : 0 ≤ step1Depth
  step2Gates_nonneg : 0 ≤ step2Gates
  step2Depth_nonneg : 0 ≤ step2Depth
  step3Gates_nonneg : 0 ≤ step3Gates
  step3Depth_nonneg : 0 ≤ step3Depth
  step4Gates_nonneg : 0 ≤ step4Gates
  step4Depth_nonneg : 0 ≤ step4Depth
  step6Gates_nonneg : 0 ≤ step6Gates
  step6Depth_nonneg : 0 ≤ step6Depth

/-- Total gates: Step 1 + `(η − 1)` repetitions of Steps 2–4 + Step 6. -/
def FisherYatesProfile.totalGates (η : ℝ) (p : FisherYatesProfile) : ℝ :=
  p.step1Gates + (η - 1) * (p.step2Gates + p.step3Gates + p.step4Gates)
    + p.step6Gates

/-- Total depth: Step 1 + `(η − 1)` repetitions of Steps 2–4 + Step 6; the
blocks are performed sequentially. -/
def FisherYatesProfile.totalDepth (η : ℝ) (p : FisherYatesProfile) : ℝ :=
  p.step1Depth + (η - 1) * (p.step2Depth + p.step3Depth + p.step4Depth)
    + p.step6Depth

/-- `η² ≤ η² (1 + log N)` for `N ≥ 1`. -/
lemma etaSq_le_etaSqTarget {η N : ℝ} (hη : 1 ≤ η) (hN : 1 ≤ N) :
    η ^ 2 ≤ etaSqTarget η N := by
  unfold etaSqTarget
  have h1 : 0 ≤ η ^ 2 := by positivity
  have h2 : 1 ≤ 1 + Real.log N := by
    have := Real.log_nonneg hN
    linarith
  calc η ^ 2 = η ^ 2 * 1 := by ring
    _ ≤ η ^ 2 * (1 + Real.log N) := mul_le_mul_of_nonneg_left h2 h1

/-- **Claim c002 (arXiv:1711.10460 Appendix C p. 13).**  With Steps 1/2/3/4 at
gates `O(η log η) / O(η) / O(η log N) / O(η log η)` and depths
`O(1) / O(η) / O(η log N) / O(log η)`, repeated `η − 1` times, and with
Step 6 at `O(η² log N)` gates and `O(η²(log log N + log η))` depth, the whole
quantum Fisher–Yates shuffle has both gate count and circuit depth
`O(η² log N)`. -/
theorem fisherYates_gate_and_depth_bounds
    (η N : ℝ) (hη : 2 ≤ η) (hηN : η ≤ N)
    (p : FisherYatesProfile)
    (hG1 : IsO p.step1Gates (etaGate η))
    (hD1 : IsO p.step1Depth 1)
    (hG2 : IsO p.step2Gates η)
    (hD2 : IsO p.step2Depth η)
    (hG3 : IsO p.step3Gates (η * onePlusLog N))
    (hD3 : IsO p.step3Depth (η * onePlusLog N))
    (hG4 : IsO p.step4Gates (etaGate η))
    (hD4 : IsO p.step4Depth (onePlusLog η))
    (hG6 : IsO p.step6Gates (etaSqTarget η N))
    (hD6 : IsO p.step6Depth (η ^ 2 * (onePlusLogLog N + onePlusLog η))) :
    IsO (p.totalGates η) (etaSqTarget η N) ∧
      IsO (p.totalDepth η) (etaSqTarget η N) := by
  obtain ⟨K1, hK10, hg1⟩ := hG1
  obtain ⟨Kd1, hKd10, hd1⟩ := hD1
  obtain ⟨K2, hK20, hg2⟩ := hG2
  obtain ⟨Kd2, hKd20, hd2⟩ := hD2
  obtain ⟨K3, hK30, hg3⟩ := hG3
  obtain ⟨Kd3, hKd30, hd3⟩ := hD3
  obtain ⟨K4, hK40, hg4⟩ := hG4
  obtain ⟨Kd4, hKd40, hd4⟩ := hD4
  obtain ⟨K6, hK60, hg6⟩ := hG6
  obtain ⟨Kd6, hKd60, hd6⟩ := hD6
  have hη1 : (1 : ℝ) ≤ η := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hηpos : 0 < η := by linarith
  have hηm1_nonneg : 0 ≤ η - 1 := by linarith
  have hηm1_le : η - 1 ≤ η := by linarith
  have hlogN1 : 0 ≤ onePlusLog N := onePlusLog_nonneg hN1
  have hlog1 : 1 ≤ onePlusLog N := by
    unfold onePlusLog
    have := Real.log_nonneg hN1
    linarith
  have hlog_le : onePlusLog η ≤ onePlusLog N := onePlusLog_le_onePlusLog hη1 hηN
  have hT1 : 1 ≤ etaSqTarget η N := one_le_etaSqTarget hη1 hN1
  have hTSq : η ^ 2 ≤ etaSqTarget η N := etaSq_le_etaSqTarget hη1 hN1
  have hEtaSqNonneg : 0 ≤ η ^ 2 := by positivity
  -- ------------------------------------------------------------------
  -- Gate count
  -- ------------------------------------------------------------------
  -- Step 1
  have hG1' : p.step1Gates ≤ K1 * etaSqTarget η N := by
    calc p.step1Gates ≤ K1 * etaGate η := hg1
      _ ≤ K1 * etaSqTarget η N :=
          mul_le_mul_of_nonneg_left (etaGate_le_etaSqTarget hη hηN) hK10
  -- Step 2 repeated η−1 times: η·(K2 η) = K2 η² ≤ K2 η²(1+log N)
  have hG2' : (η - 1) * p.step2Gates ≤ K2 * etaSqTarget η N := by
    have hmul : (η - 1) * p.step2Gates ≤ η * (K2 * η) :=
      mul_le_mul hηm1_le hg2 p.step2Gates_nonneg (le_of_lt hηpos)
    have hηsq : η * (K2 * η) = K2 * η ^ 2 := by ring
    rw [hηsq] at hmul
    calc (η - 1) * p.step2Gates ≤ K2 * η ^ 2 := hmul
      _ ≤ K2 * etaSqTarget η N := mul_le_mul_of_nonneg_left hTSq hK20
  -- Step 3 repeated: η·(K3 η(1+log N)) = K3 η²(1+log N)*
  have hG3' : (η - 1) * p.step3Gates ≤ K3 * etaSqTarget η N := by
    have hmul : (η - 1) * p.step3Gates
        ≤ η * (K3 * (η * onePlusLog N)) :=
      mul_le_mul hηm1_le hg3 p.step3Gates_nonneg (le_of_lt hηpos)
    have heq : η * (K3 * (η * onePlusLog N)) = K3 * etaSqTarget η N := by
      unfold etaSqTarget
      ring
    rwa [heq] at hmul
  -- Step 4 repeated: η·(K4 η(1+log η)) = K4 η²(1+log η) ≤ K4 η²(1+log N)
  have hG4' : (η - 1) * p.step4Gates ≤ K4 * etaSqTarget η N := by
    have hmul : (η - 1) * p.step4Gates ≤ η * (K4 * etaGate η) :=
      mul_le_mul hηm1_le hg4 p.step4Gates_nonneg (le_of_lt hηpos)
    have hstep : η * (K4 * etaGate η) ≤ K4 * etaSqTarget η N := by
      have hcoef : 0 ≤ K4 * η ^ 2 := mul_nonneg hK40 hEtaSqNonneg
      calc η * (K4 * etaGate η) = (K4 * η ^ 2) * onePlusLog η := by
            unfold etaGate
            ring
        _ ≤ (K4 * η ^ 2) * onePlusLog N :=
            mul_le_mul_of_nonneg_left hlog_le hcoef
        _ = K4 * etaSqTarget η N := by
            unfold etaSqTarget
            ring
    exact le_trans hmul hstep
  -- Step 6
  have hG6' : p.step6Gates ≤ K6 * etaSqTarget η N := hg6
  have hGate : p.totalGates η ≤
      (K1 + K2 + K3 + K4 + K6) * etaSqTarget η N := by
    have hsum : p.totalGates η
        ≤ K1 * etaSqTarget η N + K2 * etaSqTarget η N
          + K3 * etaSqTarget η N + K4 * etaSqTarget η N
          + K6 * etaSqTarget η N := by
      unfold FisherYatesProfile.totalGates
      linarith [hG1', hG2', hG3', hG4', hG6']
    calc p.totalGates η
        ≤ K1 * etaSqTarget η N + K2 * etaSqTarget η N
          + K3 * etaSqTarget η N + K4 * etaSqTarget η N
          + K6 * etaSqTarget η N := hsum
      _ = (K1 + K2 + K3 + K4 + K6) * etaSqTarget η N := by ring
  -- ------------------------------------------------------------------
  -- Circuit depth
  -- ------------------------------------------------------------------
  -- Step 1: O(1) ⊆ O(η² log N)
  have hD1' : p.step1Depth ≤ Kd1 * etaSqTarget η N := by
    have hd : p.step1Depth ≤ Kd1 := by simpa using hd1
    calc p.step1Depth ≤ Kd1 := hd
      _ = Kd1 * 1 := by ring
      _ ≤ Kd1 * etaSqTarget η N := mul_le_mul_of_nonneg_left hT1 hKd10
  -- Step 2 repeated: η·(Kd2 η) = Kd2 η² ⊆ Kd2 η²(1+log N)
  have hD2' : (η - 1) * p.step2Depth ≤ Kd2 * etaSqTarget η N := by
    have hmul : (η - 1) * p.step2Depth ≤ η * (Kd2 * η) :=
      mul_le_mul hηm1_le hd2 p.step2Depth_nonneg (le_of_lt hηpos)
    have hηsq : η * (Kd2 * η) = Kd2 * η ^ 2 := by ring
    rw [hηsq] at hmul
    calc (η - 1) * p.step2Depth ≤ Kd2 * η ^ 2 := hmul
      _ ≤ Kd2 * etaSqTarget η N := mul_le_mul_of_nonneg_left hTSq hKd20
  -- Step 3 repeated
  have hD3' : (η - 1) * p.step3Depth ≤ Kd3 * etaSqTarget η N := by
    have hmul : (η - 1) * p.step3Depth
        ≤ η * (Kd3 * (η * onePlusLog N)) :=
      mul_le_mul hηm1_le hd3 p.step3Depth_nonneg (le_of_lt hηpos)
    have heq : η * (Kd3 * (η * onePlusLog N)) = Kd3 * etaSqTarget η N := by
      unfold etaSqTarget
      ring
    rwa [heq] at hmul
  -- Step 4 repeated: η·(Kd4(1+log η)) ≤ Kd4 η²(1+log N)
  have hD4' : (η - 1) * p.step4Depth ≤ Kd4 * etaSqTarget η N := by
    have hmul : (η - 1) * p.step4Depth ≤ η * (Kd4 * onePlusLog η) :=
      mul_le_mul hηm1_le hd4 p.step4Depth_nonneg (le_of_lt hηpos)
    have hstep : η * (Kd4 * onePlusLog η) ≤ Kd4 * etaSqTarget η N := by
      have hcoef : 0 ≤ Kd4 * η := mul_nonneg hKd40 (le_of_lt hηpos)
      -- η(1+log η) ≤ η²(1+log N) because (1+log η) ≤ η(1+log N)
      have hfac : onePlusLog η ≤ η * onePlusLog N := by
        have h2 : onePlusLog N ≤ η * onePlusLog N := by
          calc onePlusLog N = 1 * onePlusLog N := by ring
            _ ≤ η * onePlusLog N :=
                mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ η) hlogN1
        linarith
      calc η * (Kd4 * onePlusLog η) = (Kd4 * η) * onePlusLog η := by ring
        _ ≤ (Kd4 * η) * (η * onePlusLog N) :=
            mul_le_mul_of_nonneg_left hfac hcoef
        _ = Kd4 * etaSqTarget η N := by
            unfold etaSqTarget
            ring
    exact le_trans hmul hstep
  -- Step 6: η²(log log N + log η) ≤ 2 η²(1+log N)
  have hD6' : p.step6Depth ≤ Kd6 * (2 * etaSqTarget η N) := by
    have hsum_le : onePlusLogLog N + onePlusLog η ≤ 2 * onePlusLog N := by
      have h1 : onePlusLogLog N ≤ onePlusLog N := onePlusLogLog_le_onePlusLog hN1
      linarith [hlog_le]
    calc p.step6Depth
        ≤ Kd6 * (η ^ 2 * (onePlusLogLog N + onePlusLog η)) := hd6
      _ ≤ Kd6 * (η ^ 2 * (2 * onePlusLog N)) := by
          apply mul_le_mul_of_nonneg_left _ hKd60
          apply mul_le_mul_of_nonneg_left hsum_le hEtaSqNonneg
      _ = Kd6 * (2 * etaSqTarget η N) := by
          unfold etaSqTarget
          ring
  have hD6'' : p.step6Depth ≤ (2 * Kd6) * etaSqTarget η N := by
    calc p.step6Depth ≤ Kd6 * (2 * etaSqTarget η N) := hD6'
      _ = (2 * Kd6) * etaSqTarget η N := by ring
  have hDepth : p.totalDepth η ≤
      (Kd1 + Kd2 + Kd3 + Kd4 + 2 * Kd6) * etaSqTarget η N := by
    have hsum : p.totalDepth η
        ≤ Kd1 * etaSqTarget η N + Kd2 * etaSqTarget η N
          + Kd3 * etaSqTarget η N + Kd4 * etaSqTarget η N
          + (2 * Kd6) * etaSqTarget η N := by
      unfold FisherYatesProfile.totalDepth
      linarith [hD1', hD2', hD3', hD4', hD6'']
    calc p.totalDepth η
        ≤ Kd1 * etaSqTarget η N + Kd2 * etaSqTarget η N
          + Kd3 * etaSqTarget η N + Kd4 * etaSqTarget η N
          + (2 * Kd6) * etaSqTarget η N := hsum
      _ = (Kd1 + Kd2 + Kd3 + Kd4 + 2 * Kd6) * etaSqTarget η N := by ring
  refine ⟨⟨K1 + K2 + K3 + K4 + K6, ?_, hGate⟩,
          ⟨Kd1 + Kd2 + Kd3 + Kd4 + 2 * Kd6, ?_, hDepth⟩⟩
  · linarith
  · linarith

end Qatlib.Papers.FermEigState17.MainResults.FisherYatesCost
