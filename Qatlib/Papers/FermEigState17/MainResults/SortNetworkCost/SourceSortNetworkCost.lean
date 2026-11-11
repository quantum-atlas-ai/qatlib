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
# FermEigState17 Claim c001 — antisymmetrization via a sorting network

Fixed paper version: **arXiv:1711.10460**, Section II, pp. 2–4, Eq. (1).

The paper antisymmetrizes a sorted, repetition-free array of `η` registers of
`log N` bits by running a sorting network forward to record the comparators
(Steps 1–3) and then reversing the network on the target (Step 4).  Under the
assumption that the sorting network is asymptotically optimal, the paper states
(§II summary, and the paragraph "Our quoted asymptotic runtime and gate
complexity scalings assume the use of sorting networks that are asymptotically
optimal"):

* gate complexity `O(η log η log N)`;
* circuit depth `O(log η log log N)`.

The derivation is a composition of the per-comparator costs proved in
Appendix B: the network has `O(η log η)` comparators arranged in `O(log η)`
parallel rounds; each Step-4 comparator has complexity `O(log N)` and depth
`O(log log N)`, while each Step-2 comparator has complexity `O(log η)` and depth
`O(log log η)` (smaller because `η < N`).  Step 1 costs `O(η log η)` gates at
`O(1)` depth; Step 3 costs `O(η log η)` gates at `O(log η)` depth.

This file freezes that cost profile and proves the composition lemma: the
stated per-step asymptotic magnitudes of the algorithm force the paper's final
gate and depth bounds.  The `O(·)` statements are encoded with the positive
representatives `1 + log ·`, `1 + log(1 + log ·)` from `CostModel`, which do not
change the asymptotic class.  No step of the paper's resource argument is
dropped; the result is a genuine explicit-constant `O`-composition, not an
assumption of the conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermEigState17.MainResults.SortNetworkCost

open Qatlib.Papers.FermEigState17.MainResults.CostModel

/-- Cost profile of the four-step sorting-network antisymmetrization of §II.
All fields are nonnegative resource counts / depths. -/
structure SortProfile where
  /-- number of comparators in the sorting network (shared by Steps 2 and 4) -/
  comparators : ℝ
  /-- number of parallel comparator rounds of the network -/
  rounds : ℝ
  /-- gate cost of one Step-2 comparator -/
  step2ComparatorCost : ℝ
  /-- depth of one Step-2 comparator -/
  step2ComparatorDepth : ℝ
  /-- gate cost of one Step-4 comparator -/
  step4ComparatorCost : ℝ
  /-- depth of one Step-4 comparator -/
  step4ComparatorDepth : ℝ
  /-- gates of the constant-depth seed-preparation Step 1 -/
  step1Gates : ℝ
  /-- depth of Step 1 -/
  step1Depth : ℝ
  /-- gates of the collision-detection Step 3 -/
  step3Gates : ℝ
  /-- depth of Step 3 -/
  step3Depth : ℝ
  comparators_nonneg : 0 ≤ comparators
  rounds_nonneg : 0 ≤ rounds
  step2ComparatorCost_nonneg : 0 ≤ step2ComparatorCost
  step2ComparatorDepth_nonneg : 0 ≤ step2ComparatorDepth
  step4ComparatorCost_nonneg : 0 ≤ step4ComparatorCost
  step4ComparatorDepth_nonneg : 0 ≤ step4ComparatorDepth
  step1Gates_nonneg : 0 ≤ step1Gates
  step1Depth_nonneg : 0 ≤ step1Depth
  step3Gates_nonneg : 0 ≤ step3Gates
  step3Depth_nonneg : 0 ≤ step3Depth

/-- Total gate count: Step 1 + Step 2 + Step 3 + Step 4, where Steps 2 and 4
each run over all comparators of the network. -/
def SortProfile.totalGates (p : SortProfile) : ℝ :=
  p.step1Gates + p.comparators * p.step2ComparatorCost
    + p.step3Gates + p.comparators * p.step4ComparatorCost

/-- Total circuit depth: Step 1 + Step 2 + Step 3 + Step 4, where the
comparators of Steps 2 and 4 are parallelized into `rounds` rounds. -/
def SortProfile.totalDepth (p : SortProfile) : ℝ :=
  p.step1Depth + p.rounds * p.step2ComparatorDepth
    + p.step3Depth + p.rounds * p.step4ComparatorDepth

/-- **Claim c001 (arXiv:1711.10460 §II, pp. 2–4).**  For an asymptotically
optimal sorting network (`comparators = O(η log η)`, `rounds = O(log η)`, each
Step-4 comparator `O(log N)` gates / `O(log log N)` depth, each Step-2
comparator `O(log η)` gates / `O(log log η)` depth) with the cheap Steps 1 and 3
at their stated magnitudes, the total circuit of the antisymmetrization
algorithm has `O(η log η log N)` gates and `O(log η log log N)` depth. -/
theorem sortingNetwork_gate_and_depth_bounds
    (η N : ℝ) (hη : 2 ≤ η) (hηN : η ≤ N)
    (p : SortProfile)
    (hComp : IsO p.comparators (etaGate η))
    (hRounds : IsO p.rounds (onePlusLog η))
    (hS2c : IsO p.step2ComparatorCost (onePlusLog η))
    (hS2d : IsO p.step2ComparatorDepth (onePlusLogLog η))
    (hS4c : IsO p.step4ComparatorCost (onePlusLog N))
    (hS4d : IsO p.step4ComparatorDepth (onePlusLogLog N))
    (hG1 : IsO p.step1Gates (etaGate η))
    (hD1 : IsO p.step1Depth 1)
    (hG3 : IsO p.step3Gates (etaGate η))
    (hD3 : IsO p.step3Depth (onePlusLog η)) :
    IsO p.totalGates (sortGateTarget η N) ∧
      IsO p.totalDepth (sortDepthTarget η N) := by
  obtain ⟨Kc, hKc0, hc⟩ := hComp
  obtain ⟨Kr, hKr0, hr⟩ := hRounds
  obtain ⟨Ks2c, hKs2c0, hs2c⟩ := hS2c
  obtain ⟨Ks2d, hKs2d0, hs2d⟩ := hS2d
  obtain ⟨Ks4c, hKs4c0, hs4c⟩ := hS4c
  obtain ⟨Ks4d, hKs4d0, hs4d⟩ := hS4d
  obtain ⟨K1, hK10, hg1⟩ := hG1
  obtain ⟨Kd1, hKd10, hd1⟩ := hD1
  obtain ⟨K3, hK30, hg3⟩ := hG3
  obtain ⟨Kd3, hKd30, hd3⟩ := hD3
  have hη1 : (1 : ℝ) ≤ η := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hEtaNonneg : 0 ≤ etaGate η := etaGate_nonneg hη1
  -- ------------------------------------------------------------------
  -- Gate count
  -- ------------------------------------------------------------------
  -- Step 2: (O(η log η) comparators) × (O(log η) gates each)
  have hS2prod : p.comparators * p.step2ComparatorCost
      ≤ (Kc * Ks2c) * sortGateTarget η N := by
    have hmul : p.comparators * p.step2ComparatorCost
        ≤ (Kc * etaGate η) * (Ks2c * onePlusLog η) :=
      mul_le_mul hc hs2c p.step2ComparatorCost_nonneg
        (mul_nonneg hKc0 hEtaNonneg)
    have hfac : onePlusLog η ≤ onePlusLog N :=
      onePlusLog_le_onePlusLog hη1 hηN
    have hcoef : 0 ≤ Kc * Ks2c * etaGate η :=
      mul_nonneg (mul_nonneg hKc0 hKs2c0) hEtaNonneg
    have hstep : (Kc * etaGate η) * (Ks2c * onePlusLog η)
        ≤ (Kc * Ks2c) * sortGateTarget η N := by
      calc (Kc * etaGate η) * (Ks2c * onePlusLog η)
          = (Kc * Ks2c * etaGate η) * onePlusLog η := by ring
        _ ≤ (Kc * Ks2c * etaGate η) * onePlusLog N :=
            mul_le_mul_of_nonneg_left hfac hcoef
        _ = (Kc * Ks2c) * sortGateTarget η N := by
            unfold sortGateTarget
            ring
    exact le_trans hmul hstep
  -- Step 4: (O(η log η) comparators) × (O(log N) gates each)
  have hS4prod : p.comparators * p.step4ComparatorCost
      ≤ (Kc * Ks4c) * sortGateTarget η N := by
    have hmul : p.comparators * p.step4ComparatorCost
        ≤ (Kc * etaGate η) * (Ks4c * onePlusLog N) :=
      mul_le_mul hc hs4c p.step4ComparatorCost_nonneg
        (mul_nonneg hKc0 hEtaNonneg)
    have heq : (Kc * etaGate η) * (Ks4c * onePlusLog N)
        = (Kc * Ks4c) * sortGateTarget η N := by
      unfold sortGateTarget
      ring
    rwa [heq] at hmul
  -- Step 1: O(η log η) ⊆ O(η log η log N)
  have hG1' : p.step1Gates ≤ K1 * sortGateTarget η N := by
    have hle : etaGate η ≤ sortGateTarget η N :=
      etaGate_le_sortGateTarget hη1 hηN
    calc p.step1Gates ≤ K1 * etaGate η := hg1
      _ ≤ K1 * sortGateTarget η N := mul_le_mul_of_nonneg_left hle hK10
  -- Step 3: O(η log η) ⊆ O(η log η log N)
  have hG3' : p.step3Gates ≤ K3 * sortGateTarget η N := by
    have hle : etaGate η ≤ sortGateTarget η N :=
      etaGate_le_sortGateTarget hη1 hηN
    calc p.step3Gates ≤ K3 * etaGate η := hg3
      _ ≤ K3 * sortGateTarget η N := mul_le_mul_of_nonneg_left hle hK30
  have hGate : p.totalGates ≤
      (K1 + Kc * Ks2c + K3 + Kc * Ks4c) * sortGateTarget η N := by
    have hsum : p.totalGates
        ≤ K1 * sortGateTarget η N + (Kc * Ks2c) * sortGateTarget η N
          + K3 * sortGateTarget η N + (Kc * Ks4c) * sortGateTarget η N := by
      unfold SortProfile.totalGates
      linarith [hS2prod, hS4prod, hG1', hG3']
    calc p.totalGates
        ≤ K1 * sortGateTarget η N + (Kc * Ks2c) * sortGateTarget η N
          + K3 * sortGateTarget η N + (Kc * Ks4c) * sortGateTarget η N := hsum
      _ = (K1 + Kc * Ks2c + K3 + Kc * Ks4c) * sortGateTarget η N := by ring
  -- ------------------------------------------------------------------
  -- Circuit depth
  -- ------------------------------------------------------------------
  -- Step 2: (O(log η) rounds) × (O(log log η) depth each)
  have hS2dprod : p.rounds * p.step2ComparatorDepth
      ≤ (Kr * Ks2d) * sortDepthTarget η N := by
    have hmul : p.rounds * p.step2ComparatorDepth
        ≤ (Kr * onePlusLog η) * (Ks2d * onePlusLogLog η) :=
      mul_le_mul hr hs2d p.step2ComparatorDepth_nonneg
        (mul_nonneg hKr0 (onePlusLog_nonneg hη1))
    have hfac : onePlusLogLog η ≤ onePlusLogLog N :=
      onePlusLogLog_le_of_le hη1 hηN
    have hcoef : 0 ≤ Kr * Ks2d * onePlusLog η :=
      mul_nonneg (mul_nonneg hKr0 hKs2d0) (onePlusLog_nonneg hη1)
    have hstep : (Kr * onePlusLog η) * (Ks2d * onePlusLogLog η)
        ≤ (Kr * Ks2d) * sortDepthTarget η N := by
      calc (Kr * onePlusLog η) * (Ks2d * onePlusLogLog η)
          = (Kr * Ks2d * onePlusLog η) * onePlusLogLog η := by ring
        _ ≤ (Kr * Ks2d * onePlusLog η) * onePlusLogLog N :=
            mul_le_mul_of_nonneg_left hfac hcoef
        _ = (Kr * Ks2d) * sortDepthTarget η N := by
            unfold sortDepthTarget
            ring
    exact le_trans hmul hstep
  -- Step 4: (O(log η) rounds) × (O(log log N) depth each)
  have hS4dprod : p.rounds * p.step4ComparatorDepth
      ≤ (Kr * Ks4d) * sortDepthTarget η N := by
    have hmul : p.rounds * p.step4ComparatorDepth
        ≤ (Kr * onePlusLog η) * (Ks4d * onePlusLogLog N) :=
      mul_le_mul hr hs4d p.step4ComparatorDepth_nonneg
        (mul_nonneg hKr0 (onePlusLog_nonneg hη1))
    have heq : (Kr * onePlusLog η) * (Ks4d * onePlusLogLog N)
        = (Kr * Ks4d) * sortDepthTarget η N := by
      unfold sortDepthTarget
      ring
    rwa [heq] at hmul
  -- Step 1: O(1) ⊆ O(log η log log N)
  have hD1' : p.step1Depth ≤ Kd1 * sortDepthTarget η N := by
    have hD11 : p.step1Depth ≤ Kd1 * 1 := hd1
    have h1t : (1 : ℝ) ≤ sortDepthTarget η N :=
      one_le_sortDepthTarget hη1 hN1
    have : p.step1Depth ≤ Kd1 := by simpa using hD11
    calc p.step1Depth ≤ Kd1 := this
      _ = Kd1 * 1 := by ring
      _ ≤ Kd1 * sortDepthTarget η N := mul_le_mul_of_nonneg_left h1t hKd10
  -- Step 3: O(log η) ⊆ O(log η log log N)
  have hD3' : p.step3Depth ≤ Kd3 * sortDepthTarget η N := by
    have hle : onePlusLog η ≤ sortDepthTarget η N :=
      onePlusLog_le_sortDepthTarget hη1 hN1
    calc p.step3Depth ≤ Kd3 * onePlusLog η := hd3
      _ ≤ Kd3 * sortDepthTarget η N := mul_le_mul_of_nonneg_left hle hKd30
  have hDepth : p.totalDepth ≤
      (Kd1 + Kr * Ks2d + Kd3 + Kr * Ks4d) * sortDepthTarget η N := by
    have hsum : p.totalDepth
        ≤ Kd1 * sortDepthTarget η N + (Kr * Ks2d) * sortDepthTarget η N
          + Kd3 * sortDepthTarget η N + (Kr * Ks4d) * sortDepthTarget η N := by
      unfold SortProfile.totalDepth
      linarith [hS2dprod, hS4dprod, hD1', hD3']
    calc p.totalDepth
        ≤ Kd1 * sortDepthTarget η N + (Kr * Ks2d) * sortDepthTarget η N
          + Kd3 * sortDepthTarget η N + (Kr * Ks4d) * sortDepthTarget η N := hsum
      _ = (Kd1 + Kr * Ks2d + Kd3 + Kr * Ks4d) * sortDepthTarget η N := by ring
  refine ⟨⟨K1 + Kc * Ks2c + K3 + Kc * Ks4c, ?_, hGate⟩,
          ⟨Kd1 + Kr * Ks2d + Kd3 + Kr * Ks4d, ?_, hDepth⟩⟩
  · have h1 : 0 ≤ Kc * Ks2c := mul_nonneg hKc0 hKs2c0
    have h2 : 0 ≤ Kc * Ks4c := mul_nonneg hKc0 hKs4c0
    linarith
  · have h1 : 0 ≤ Kr * Ks2d := mul_nonneg hKr0 hKs2d0
    have h2 : 0 ≤ Kr * Ks4d := mul_nonneg hKr0 hKs4d0
    linarith

end Qatlib.Papers.FermEigState17.MainResults.SortNetworkCost
