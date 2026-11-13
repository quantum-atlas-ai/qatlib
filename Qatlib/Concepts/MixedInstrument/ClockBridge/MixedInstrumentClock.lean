/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.FairRandomBits.GeometricRetry
import Qatlib.Concepts.MixedInstrument.ClockBridge.UnboundedInstrumentLoop

/-!
# Mixed-instrument clocks and completely positive limits

This module defines costed instrument transitions and finite halting maps indexed by output and
accumulated charge. It identifies their traces with execution event probabilities and proves
stabilization at fixed charge when all branch prices are positive.

The auxiliary `MixedClockSeries.cpSeriesLimit` constructs a completely positive limit from a
trace-bounded series. It yields output-indexed unbounded halting maps whose total trace on a
density operator is at most one. The instrument and completely positive map background is
described in [Watrous2018].

## Main statements

* `mixed_instrument_finite_halt_cp_bridge`: relates finite halting maps to exact receipt
  probabilities.
* `mixed_instrument_positive_clock_stabilization`: proves stabilization at fixed charge.
* `mixed_instrument_unbounded_output_cp_limit`: constructs unbounded output maps.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.MixedInstrument.ClockBridge
open Matrix
open scoped ComplexOrder Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The subtype of operators in dimension `D` that are density operators. -/
abbrev ClockDensity (D : ℕ) := {ρ : Operator D // IsDensityOperator ρ}

/-- The conditional density operator for outcome `l` when its probability is positive, with the
input density operator used for zero-probability outcomes. -/
noncomputable def clockConditional {L : Type} [Fintype L] {D : ℕ}
    (I : Instrument L D D) (ρ : ClockDensity D) (l : L) : ClockDensity D :=
  if h : 0 < instrumentProb I ρ.val l then
    ⟨I.conditionalState ρ.val l h,I.isDensityOperator_conditionalState ρ.property l h⟩ else ρ

/-- The probability mass function of an instrument outcome, its conditional density operator,
and its branch price at a classical state. -/
noncomputable def mixedReceipt {C L : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (price : C→L→ℕ) (s : C×ClockDensity D) :
    PMF (L×ClockDensity D×ℕ) :=
  (instrumentPMF (I s.1) s.2.property).map (fun l => (l,clockConditional (I s.1) s.2 l,price s.1 l))

/-- The costed transition law that routes an instrument outcome to a halting output or a new
classical state while retaining the conditional density operator. -/
noncomputable def mixedNext {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ) :
    C×ClockDensity D → PMF (((O×ClockDensity D)⊕(C×ClockDensity D))×ℕ) :=
  fun s => (mixedReceipt I price s).map (fun z =>
    ((dest s.1 z.1).map (fun o => (o,z.2.1)) (fun c => (c,z.2.1)),z.2.2))

/-- The finite-fuel linear map for halting at output `o` with exact accumulated charge `k`,
obtained by summing instrument branch compositions. -/
noncomputable def mixedHaltMap {C L O : Type} [Fintype L] [DecidableEq O] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ) :
    ℕ→C→O→ℕ→(Operator D→ₗ[ℂ]Operator D)
  | 0,_,_,_ => 0
  | n+1,c,o,k => ∑ l : L,
      if price c l≤k then
        match dest c l with
        | .inl out => if out=o ∧ price c l=k then (I c).branch l else 0
        | .inr c' => (mixedHaltMap I dest price n c' o (k-price c l)).comp ((I c).branch l)
      else 0

/-- An instrument branch with zero outcome probability on a density operator has zero
unnormalized output. -/
theorem mixed_instrument_actual_receipt_and_state :
    ∀ (L : Type) [Fintype L] (D : ℕ) (I : Instrument L D D)
      (ρ : ClockDensity D) (l : L),
      instrumentProb I ρ.val l = 0 → I.branch l ρ.val = 0 := by
  intro L _ D I ρ l h
  exact (instrumentProb_eq_zero_iff I ρ.property.1 l).mp h

/-- With strictly positive branch prices, the halting map at exact charge `k` stabilizes once
the fuel is at least `k`. -/
theorem mixed_instrument_positive_clock_stabilization :
    ∀ (C L O : Type) [Fintype C] [Fintype L] [Fintype O] [DecidableEq O]
      (D : ℕ) (I : C → Instrument L D D) (dest : C → L → O ⊕ C)
      (price : C → L → ℕ),
      (∀ c l, 0 < price c l) → ∀ (n k : ℕ) (c : C) (o : O), k ≤ n →
      mixedHaltMap I dest price n c o k = mixedHaltMap I dest price k c o k := by
  intro C L O _ _ _ _ D I dest price hp n k
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    intro c o hn
    cases k with
    | zero =>
      cases n with
      | zero => rfl
      | succ n =>
        simp only [mixedHaltMap]
        apply Finset.sum_eq_zero
        intro l _
        rw [if_neg (by have := hp c l; omega)]
    | succ k =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [mixedHaltMap]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs with hfit
      · cases he : dest c l with
        | inl out => rfl
        | inr c' =>
          have hpos := hp c l
          (try dsimp only)
          rw [ih (k + 1 - price c l) (by omega) m c' o (by omega),
            ih (k + 1 - price c l) (by omega) k c' o (by omega)]
      · rfl

/-- Under strictly positive branch prices, every transition of nonzero probability has charge at
least one. -/
theorem mixedNext_positive {C L O : Type} [Fintype L] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (hp : ∀ c l, 0 < price c l) :
    ∀ s cfg k, mixedNext I dest price s (cfg, k) ≠ 0 → 1 ≤ k := by
  intro s cfg k hm
  have hs := (PMF.mem_support_iff _ _).mpr hm
  obtain ⟨z, hz, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  obtain ⟨l, hl, he'⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  have hk : price s.1 l = k := by
    have h := congrArg Prod.snd he
    rw [← he'] at h
    exact h
  rw [← hk]
  exact hp s.1 l

/-- The zero linear map on operators is completely positive. -/
private theorem mixed_cp_zero {D : ℕ} :
    CompletelyPositive (0 : Operator D →ₗ[ℂ] Operator D) := by
  intro r A _
  have h : ChannelAmplification (0 : Operator D →ₗ[ℂ] Operator D) r A = 0 := by
    ext x y
    simp [ChannelAmplification]
  rw [h]
  exact Matrix.PosSemidef.zero

/-- Every finite-fuel halting map at a fixed output and charge is completely positive and trace
non-increasing. -/
theorem mixedHaltMap_cp_tni {C L O : Type} [Fintype L] [DecidableEq O] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (n : ℕ) (c : C) (o : O) (k : ℕ) :
    CompletelyPositive (mixedHaltMap I dest price n c o k) ∧
      TraceNonIncreasing (mixedHaltMap I dest price n c o k) := by
  induction n generalizing c k with
  | zero =>
    refine ⟨mixed_cp_zero, ?_⟩
    intro A hA
    simpa [mixedHaltMap] using (RCLike.nonneg_iff.mp hA.trace_nonneg).1
  | succ n ih =>
    let T : L → (Operator D →ₗ[ℂ] Operator D) := fun l =>
      if price c l ≤ k then
        match dest c l with
        | .inl out => if out = o ∧ price c l = k then (I c).branch l else 0
        | .inr c' => (mixedHaltMap I dest price n c' o (k-price c l)).comp ((I c).branch l)
      else 0
    have hT (l : L) : CompletelyPositive (T l) := by
      dsimp [T]
      split_ifs
      · cases dest c l with
        | inl out =>
          (try dsimp only)
          split_ifs
          · exact (I c).cp l
          · exact mixed_cp_zero
        | inr c' => exact (ih c' (k-price c l)).1.comp ((I c).cp l)
      · exact mixed_cp_zero
    refine ⟨CompletelyPositive.sum (fun l _ => hT l), ?_⟩
    intro A hA
    change (Matrix.trace ((∑ l, T l) A)).re ≤ _
    rw [LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum]
    have hb (l : L) : (Matrix.trace (T l A)).re ≤ instrumentProb (I c) A l := by
      have hnn := instrumentProb_nonneg (I c) hA l
      dsimp [T]
      split_ifs
      · cases dest c l with
        | inl out =>
          (try dsimp only)
          split_ifs
          · exact le_rfl
          · simpa using hnn
        | inr c' => exact (ih c' (k-price c l)).2 (((I c).cp l).positive hA)
      · simpa using hnn
    exact (Finset.sum_le_sum fun l _ => hb l).trans_eq (sum_instrumentProb (I c) A)

/-- Adding charge `a` shifts an exact-charge event from `k` to `k - a` when `a ≤ k`, and gives
zero mass otherwise. -/
theorem mixed_event_charge {α : Type} (p : CostedLaw α) (a k : ℕ) (E : α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge a p) (fun z => z.2 = k ∧ E z.1) =
      if a ≤ k then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.2 = k-a ∧ E z.1) else 0 := by
  classical
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  (try dsimp only)
  by_cases h : a ≤ k
  · rw [if_pos h]
    congr 1
    funext z
    have he : a + z.2 = k ↔ z.2 = k-a := by omega
    simp only [he]
    split_ifs <;> rfl
  · rw [if_neg h]
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
    convert (tsum_zero : (∑' _ : α × ℕ, (0 : ℝ≥0∞)) = 0) using 1
    apply tsum_congr
    intro z
    simp only [if_neg (show ¬ (a + z.2 = k ∧ E z.1) by omega), mul_zero]

/-- Multiplying a conditional density operator by its outcome probability reconstructs the
unnormalized instrument branch output. -/
theorem clockConditional_reconstruct {L : Type} [Fintype L] {D : ℕ}
    (I : Instrument L D D) (ρ : ClockDensity D) (l : L) :
    (instrumentProb I ρ.val l : ℂ) • (clockConditional I ρ l).val = I.branch l ρ.val := by
  classical
  unfold clockConditional
  split_ifs with h
  · (try dsimp only)
    have hn : (instrumentProb I ρ.val l : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt h
    rw [Instrument.conditionalState, smul_smul, mul_inv_cancel₀ hn, one_smul]
  · have h0 : instrumentProb I ρ.val l = 0 :=
      le_antisymm (not_lt.mp h) (instrumentProb_nonneg I ρ.property.1 l)
    rw [h0, Complex.ofReal_zero, zero_smul,
      mixed_instrument_actual_receipt_and_state L D I ρ l h0]

/-- The probability of halting at a fixed output and charge with `n + 1` fuel is the sum over
first outcomes of their probabilities times the corresponding residual halting events. -/
theorem mixedHaltEvent_succ {C L O : Type} [Fintype L] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (n k : ℕ) (c : C) (o : O) (ρ : ClockDensity D) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) (n+1) (.inr (c,ρ)))
      (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl (o,ρ')) =
    ∑ l : L, ENNReal.ofReal (instrumentProb (I c) ρ.val l) *
      (if price c l ≤ k then
        match dest c l with
        | .inl out => if out=o ∧ price c l=k then 1 else 0
        | .inr c' => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
            (branchCostRun (mixedNext I dest price) n (.inr (c',clockConditional (I c) ρ l)))
            (fun z => z.2=k-price c l ∧ ∃ ρ' : ClockDensity D, z.1=.inl (o,ρ'))
      else 0) := by
  classical
  simp only [branchCostRun, branchCostTick,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp only [mixedNext, mixedReceipt,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
      instrumentPMF_apply]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge (price c l)
      (branchCostRun (mixedNext I dest price) n
        ((dest c l).map (fun out => (out,clockConditional (I c) ρ l))
          (fun c' => (c',clockConditional (I c) ρ l)))))
    (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl (o,ρ')) = _
  rw [mixed_event_charge _ (price c l) k (fun cfg : (O × ClockDensity D) ⊕ (C × ClockDensity D) => ∃ ρ' : ClockDensity D, cfg=Sum.inl (o,ρ'))]
  split_ifs with hfit
  · cases dest c l with
    | inl out =>
      simp [Sum.map, branchCostRun_halted, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
        show k-price c l=0 ↔ price c l=k by omega, eq_comm, and_comm]
    | inr c' => rfl
  · rfl

/-- The real trace of the finite halting map on a density operator, embedded in ℝ≥0∞, equals the
corresponding exact-output, exact-charge event mass. -/
theorem mixedHaltMap_event {C L O : Type} [Fintype L] [DecidableEq O] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (n k : ℕ) (c : C) (o : O) (ρ : ClockDensity D) :
    ENNReal.ofReal ((Matrix.trace (mixedHaltMap I dest price n c o k ρ.val)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) n (.inr (c,ρ)))
        (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl (o,ρ')) := by
  classical
  induction n generalizing c k ρ with
  | zero =>
    simp [mixedHaltMap, branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
  | succ n ih =>
    rw [mixedHaltEvent_succ]
    simp only [mixedHaltMap, LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum]
    have hpos (l : L) : 0 ≤
        (Matrix.trace ((if price c l ≤ k then
          match dest c l with
          | .inl out => if out=o ∧ price c l=k then (I c).branch l else 0
          | .inr c' => (mixedHaltMap I dest price n c' o (k-price c l)).comp ((I c).branch l)
          else 0) ρ.val)).re := by
      split_ifs
      · cases dest c l with
        | inl out =>
          (try dsimp only)
          split_ifs
          · exact instrumentProb_nonneg (I c) ρ.property.1 l
          · simp
        | inr c' =>
          exact (RCLike.nonneg_iff.mp
            (((mixedHaltMap_cp_tni I dest price n c' o (k-price c l)).1.positive
              (((I c).cp l).positive ρ.property.1)).trace_nonneg)).1
      · simp
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => hpos l)]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with hfit
    · cases dest c l with
      | inl out =>
        (try dsimp only)
        split_ifs <;> simp [instrumentProb]
      | inr c' =>
        (try dsimp only)
        rw [← ih (k-price c l) c' (clockConditional (I c) ρ l)]
        simp only [LinearMap.comp_apply]
        rw [← clockConditional_reconstruct (I c) ρ l, map_smul, Matrix.trace_smul]
        have htrace :
            (((instrumentProb (I c) ρ.val l : ℂ) *
              Matrix.trace (mixedHaltMap I dest price n c' o (k-price c l)
                (clockConditional (I c) ρ l).val))).re =
              instrumentProb (I c) ρ.val l *
                (Matrix.trace (mixedHaltMap I dest price n c' o (k-price c l)
                  (clockConditional (I c) ρ l).val)).re := by
          simp [Complex.mul_re]
        rw [smul_eq_mul, htrace, ENNReal.ofReal_mul (instrumentProb_nonneg (I c) ρ.property.1 l)]
    · simp

/-- Finite halting maps are completely positive and trace non-increasing, and their traces
recover the corresponding joint output and charge event probabilities. -/
theorem mixed_instrument_finite_halt_cp_bridge :
    ∀ (C L O : Type) [Fintype C] [Fintype L] [Fintype O] [DecidableEq O]
      (D : ℕ) (I : C → Instrument L D D) (dest : C → L → O ⊕ C)
      (price : C → L → ℕ) (n k : ℕ) (c : C) (o : O) (ρ : ClockDensity D),
      CompletelyPositive (mixedHaltMap I dest price n c o k) ∧
      TraceNonIncreasing (mixedHaltMap I dest price n c o k) ∧
      ENNReal.ofReal ((Matrix.trace (mixedHaltMap I dest price n c o k ρ.val)).re) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) n (.inr (c,ρ)))
          (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl (o,ρ')) := by
  intro C L O _ _ _ _ D I dest price n k c o ρ
  exact ⟨(mixedHaltMap_cp_tni I dest price n c o k).1,
    (mixedHaltMap_cp_tni I dest price n c o k).2,
    mixedHaltMap_event I dest price n k c o ρ⟩

/-- With positive prices, the sum of halting traces over all outputs and charges below `N` is at
most one on a density operator. -/
theorem mixedHaltMap_density_partial_bound {C L O : Type} [Fintype C] [Fintype L]
    [Fintype O] [DecidableEq O] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (hp : ∀ c l, 0 < price c l) (c : C) (ρ : ClockDensity D) (N : ℕ) :
    (∑ o : O, ∑ k ∈ Finset.range N,
      (Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re) ≤ 1 := by
  classical
  have hn o k : 0 ≤ (Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re :=
    (RCLike.nonneg_iff.mp
      (((mixedHaltMap_cp_tni I dest price k c o k).1.positive ρ.property.1).trace_nonneg)).1
  have hb : (∑ o : O, ∑ k ∈ Finset.range N,
      ENNReal.ofReal ((Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re)) ≤ 1 := by
    have he : (∑ o : O, ∑ k ∈ Finset.range N,
        ENNReal.ofReal ((Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re)) =
        ∑ o : O, ∑ k ∈ Finset.range N,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) N (.inr (c,ρ)))
            (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl (o,ρ')) := by
      apply Finset.sum_congr rfl
      intro o _
      apply Finset.sum_congr rfl
      intro k hk
      rw [← mixed_instrument_positive_clock_stabilization C L O D I dest price hp N k c o
        (Nat.le_of_lt (Finset.mem_range.mp hk)), mixedHaltMap_event]
    rw [he]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
        ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_sum]
    rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const
      (branchCostRun (mixedNext I dest price) N (.inr (c,ρ))) 1]
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
    apply ENNReal.tsum_le_tsum
    intro z
    apply mul_le_mul_right
    rcases z with ⟨cfg, t⟩
    cases cfg with
    | inr s => simp
    | inl out =>
      rcases out with ⟨out,σ⟩
      have hex : ∀ o : O, (∃ ρ' : ClockDensity D, out=o ∧ σ=ρ') ↔ out=o := by
        intro o
        simp
      simp only [Sum.inl.injEq, Prod.mk.injEq, hex]
      have hsame : ∀ o : O,
          (∑ k ∈ Finset.range N, if t=k ∧ out=o then (1 : ℝ≥0∞) else 0) =
          if out=o then (if t ∈ Finset.range N then 1 else 0) else 0 := by
        intro o
        by_cases ho : out=o
        · simp [ho]
        · simp [ho]
      simp only [mul_one, PMF.tsum_coe, hsame]
      simp only [Finset.mem_range]
      split_ifs <;> simp
  have he : ENNReal.ofReal (∑ o : O, ∑ k ∈ Finset.range N,
      (Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re) =
      ∑ o : O, ∑ k ∈ Finset.range N,
      ENNReal.ofReal ((Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => Finset.sum_nonneg (fun k _ => hn o k))]
    apply Finset.sum_congr rfl
    intro o _
    exact ENNReal.ofReal_sum_of_nonneg (fun k _ => hn o k)
  rw [← he] at hb
  exact (ENNReal.ofReal_le_one).mp hb

/-- With positive prices, the sum of halting traces over all outputs and charges below `N` is at
most the input trace for positive semidefinite inputs. -/
theorem mixedHaltMap_partial_bound {C L O : Type} [Fintype C] [Fintype L]
    [Fintype O] [DecidableEq O] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (hp : ∀ c l, 0 < price c l) (c : C) (N : ℕ) {P : Operator D}
    (hP : P.PosSemidef) :
    (∑ o : O, ∑ k ∈ Finset.range N,
      (Matrix.trace (mixedHaltMap I dest price k c o k P)).re) ≤ (Matrix.trace P).re := by
  classical
  let t : ℝ := (Matrix.trace P).re
  have hτ : 0 ≤ t ∧ (Matrix.trace P).im = 0 :=
    RCLike.nonneg_iff.mp hP.trace_nonneg
  have htr : Matrix.trace P = (t : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hτ.2)
  by_cases hz : t = 0
  · have h0 : P = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hP).mp
      (htr.trans (by rw [hz, Complex.ofReal_zero]))
    simp [h0]
  · have ht : 0 < t := lt_of_le_of_ne hτ.1 (Ne.symm hz)
    let ρ : ClockDensity D := ⟨((t⁻¹ : ℝ) : ℂ) • P, by
      constructor
      · apply hP.smul
        exact RCLike.nonneg_iff.mpr ⟨inv_nonneg.mpr hτ.1, rfl⟩
      · rw [Matrix.trace_smul, htr, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hz]
        rfl⟩
    have hr : (t : ℂ) • ρ.val = P := by
      change (t : ℂ) • (((t⁻¹ : ℝ) : ℂ) • P) = P
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hz]
      simp
    have hb := mixedHaltMap_density_partial_bound I dest price hp c ρ N
    have hs : (∑ o : O, ∑ k ∈ Finset.range N,
        (Matrix.trace (mixedHaltMap I dest price k c o k P)).re) =
        (Matrix.trace P).re * (∑ o : O, ∑ k ∈ Finset.range N,
          (Matrix.trace (mixedHaltMap I dest price k c o k ρ.val)).re) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      conv_lhs => rw [← hr]
      rw [map_smul, Matrix.trace_smul, smul_eq_mul]
      simp [Complex.mul_re, t]
    rw [hs]
    simpa using mul_le_mul_of_nonneg_left hb hτ.1

namespace MixedClockSeries

/-- The predicate that every finite partial sum of the output traces of `T` on a positive
semidefinite input is bounded by that input's trace. -/
def TraceSeriesBound {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D)) : Prop :=
  ∀ N (P : Operator D), P.PosSemidef →
    (∑ k ∈ Finset.range N, (Matrix.trace (T k P)).re) ≤ (Matrix.trace P).re

/-- The norm of any entry of a positive semidefinite operator is bounded by the real part of its
trace. -/
private theorem posSemidef_abs_entry_le_trace {D : ℕ} {N : Operator D}
    (hN : N.PosSemidef) (i j : Fin D) :
    ‖N i j‖ ≤ (Matrix.trace N).re := by
  have hdiag : ∀ k : Fin D, (0 : ℂ) ≤ N k k := fun _ => hN.diag_nonneg
  have hA : (0 : ℝ) ≤ (N i i).re := (RCLike.nonneg_iff.mp (hdiag i)).1
  have hB : (0 : ℝ) ≤ (N j j).re := (RCLike.nonneg_iff.mp (hdiag j)).1
  have hT : (0 : ℝ) ≤ (Matrix.trace N).re := (RCLike.nonneg_iff.mp hN.trace_nonneg).1
  have htracere : (Matrix.trace N).re = ∑ k : Fin D, (N k k).re := by
    simp [Matrix.trace]
  have hminor : ‖N i j‖ ^ 2 ≤ (N i i).re * (N j j).re := by
    have h := posSemidef_abs_sq_le hN i j
    rwa [← Complex.sq_norm] at h
  have ham : (N i i).re * (N j j).re ≤ (((N i i).re + (N j j).re) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((N i i).re - (N j j).re)]
  have hAT : (N i i).re ≤ (Matrix.trace N).re := by
    rw [htracere]
    exact Finset.single_le_sum (fun k _ => (RCLike.nonneg_iff.mp (hdiag k)).1)
      (Finset.mem_univ i)
  have hBT : (N j j).re ≤ (Matrix.trace N).re := by
    rw [htracere]
    exact Finset.single_le_sum (fun k _ => (RCLike.nonneg_iff.mp (hdiag k)).1)
      (Finset.mem_univ j)
  have hmid : ‖N i j‖ ≤ ((N i i).re + (N j j).re) / 2 := by
    have h2 : ‖N i j‖ ^ 2 ≤ (((N i i).re + (N j j).re) / 2) ^ 2 := le_trans hminor ham
    have h3 : |‖N i j‖| ≤ |((N i i).re + (N j j).re) / 2| := sq_le_sq.mp h2
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h3
  calc ‖N i j‖ ≤ ((N i i).re + (N j j).re) / 2 := hmid
    _ ≤ (Matrix.trace N).re := by linarith

/-- The coordinate vector that is one at `i` and zero at every other index. -/
private def unitVector {D : ℕ} (i : Fin D) : Fin D → ℂ := Pi.single i 1

/-- The outer product of `u` with its conjugate, forming a positive semidefinite
rank-at-most-one operator. -/
private noncomputable def psdUnitVec {D : ℕ} (u : Fin D → ℂ) : Operator D := vecMulVec u (star u)

/-- The outer product `psdUnitVec u` is positive semidefinite. -/
private theorem psdUnitVec_posSemidef {D : ℕ} (u : Fin D → ℂ) :
    (psdUnitVec u).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star u

/-- A coordinate of `unitVector p` is one when its index is `p` and zero otherwise. -/
private theorem unitVector_apply {D : ℕ} (p a : Fin D) :
    unitVector p a = if p = a then (1 : ℂ) else 0 := by
  by_cases h : p = a
  · subst h
    simp [unitVector]
  · have h' : a ≠ p := fun he => h he.symm
    simp [unitVector, h, h']

/-- The `(a, b)` entry of `psdUnitVec u` is `u a` times the conjugate of `u b`. -/
private theorem psdUnitVec_apply {D : ℕ} (u : Fin D → ℂ) (a b : Fin D) :
    psdUnitVec u a b = u a * (starRingEnd ℂ) (u b) := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in

/-- A matrix unit is a complex linear combination of four positive semidefinite outer products
of coordinate vectors and their sums. -/
private theorem matrixUnit_eq_pieces {D : ℕ} (p q : Fin D) :
    (Matrix.single p q (1 : ℂ) : Operator D) =
      (1 / 2 : ℂ) • psdUnitVec (unitVector p + unitVector q)
      + (Complex.I / 2) • psdUnitVec (unitVector p + Complex.I • unitVector q)
      - ((1 + Complex.I) / 2) • psdUnitVec (unitVector p)
      - ((1 + Complex.I) / 2) • psdUnitVec (unitVector q) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases hpa : p = a <;> by_cases hqa : q = a <;>
      simp [psdUnitVec_apply, unitVector_apply, hpa, hqa,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Pi.add_apply, Pi.smul_apply, map_add, map_one,
        map_zero] <;>
      refine Complex.ext ?_ ?_ <;> norm_num [Complex.add_re, Complex.mul_re,
        Complex.sub_re, Complex.add_im, Complex.mul_im, Complex.sub_im]
  · by_cases hpa : p = a <;> by_cases hqa : q = a <;> by_cases hpb : p = b <;>
      by_cases hqb : q = b <;>
      simp_all [psdUnitVec_apply, unitVector_apply,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Pi.add_apply, Pi.smul_apply, map_add, map_one,
        map_zero] <;>
      refine Complex.ext ?_ ?_ <;> norm_num [Complex.add_re, Complex.mul_re,
        Complex.sub_re, Complex.add_im, Complex.mul_im, Complex.sub_im]

/-- Every operator is the sum of its matrix units scaled by the corresponding entries. -/
private theorem eq_sum_matrixUnit {D : ℕ} (X : Operator D) :
    X = ∑ p : Fin D, ∑ q : Fin D,
      ((X p q : ℂ) • (Matrix.single p q (1 : ℂ) : Operator D)) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    apply_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a (fun p _ hp => by
      apply Finset.sum_eq_zero
      intro q _
      have hn : ¬(p = a ∧ q = b) := fun h => hp h.1
      simp [hn])
    (fun hb => absurd (Finset.mem_univ a) hb),
    Finset.sum_eq_single b (fun q _ hq => by
      simp [fun h => hq h])
    (fun hb => absurd (Finset.mem_univ b) hb)]
  simp

/-- A finite sum of summable complex sequences is summable. -/
private theorem summable_finset_sum' {ι : Type} (s : Finset ι) (f : ι → ℕ → ℂ)
    (h : ∀ p ∈ s, Summable (f p)) : Summable fun k => ∑ p ∈ s, f p k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [summable_zero]
  | insert p s hp ih =>
      simp only [Finset.sum_insert hp]
      exact (h p (Finset.mem_insert_self p s)).add
        (ih fun q hq => h q (Finset.mem_insert_of_mem hq))

/-- For a completely positive series satisfying `TraceSeriesBound`, each output entry is
summable on positive semidefinite inputs. -/
private theorem halt_entry_summable_psd {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T)
    {P : Operator D} (hP : P.PosSemidef) (i j : Fin D) :
    Summable fun k => T k P i j := by
  have hbound : ∀ k, ‖T k P i j‖ ≤ (Matrix.trace (T k P)).re :=
    fun k => posSemidef_abs_entry_le_trace ((hc k).positive hP) i j
  have hnonneg : ∀ k, (0 : ℝ) ≤ (Matrix.trace (T k P)).re := fun k =>
    complex_re_nonneg_of_le ((hc k).positive hP).trace_nonneg
  have hseries : Summable fun k => (Matrix.trace (T k P)).re := by
    refine summable_of_sum_range_le (c := (Matrix.trace P).re) hnonneg fun n => ?_
    exact hb n P hP
  exact Summable.of_norm (hseries.of_nonneg_of_le (fun k => norm_nonneg _) hbound)

/-- For a completely positive series satisfying `TraceSeriesBound`, each output entry is
summable on a scalar multiple of a matrix unit. -/
private theorem halt_entry_summable_single {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T) (c : ℂ)
    (p q : Fin D) (i j : Fin D) :
    Summable fun k => T k
      (c • (Matrix.single p q (1 : ℂ) : Operator D)) i j := by
  have hEq : ∀ k, T k (c • (Matrix.single p q (1 : ℂ) : Operator D)) i j
      = c * T k (Matrix.single p q (1 : ℂ) : Operator D) i j := by
    intro k
    rw [map_smul]
    rfl
  have hcomb : ∀ k, T k (Matrix.single p q (1 : ℂ) : Operator D) i j
      = (1 / 2 : ℂ) * T k (psdUnitVec (unitVector p + unitVector q)) i j
        + (Complex.I / 2)
            * T k (psdUnitVec (unitVector p + Complex.I • unitVector q)) i j
        - ((1 + Complex.I) / 2) * T k (psdUnitVec (unitVector p)) i j
        - ((1 + Complex.I) / 2) * T k (psdUnitVec (unitVector q)) i j := by
    intro k
    have h1 : T k (Matrix.single p q (1 : ℂ) : Operator D)
        = (1 / 2 : ℂ) • T k (psdUnitVec (unitVector p + unitVector q))
          + (Complex.I / 2)
              • T k (psdUnitVec (unitVector p + Complex.I • unitVector q))
          - ((1 + Complex.I) / 2) • T k (psdUnitVec (unitVector p))
          - ((1 + Complex.I) / 2) • T k (psdUnitVec (unitVector q)) := by
      rw [matrixUnit_eq_pieces p q]
      simp [map_add, map_sub, map_smul]
    rw [h1]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hgoal : (fun k => T k
      (c • (Matrix.single p q (1 : ℂ) : Operator D)) i j)
      = fun k => c * ((1 / 2 : ℂ) * T k (psdUnitVec (unitVector p + unitVector q)) i j
        + (Complex.I / 2)
            * T k (psdUnitVec (unitVector p + Complex.I • unitVector q)) i j
        - ((1 + Complex.I) / 2) * T k (psdUnitVec (unitVector p)) i j
        - ((1 + Complex.I) / 2) * T k (psdUnitVec (unitVector q)) i j) := by
    funext k
    rw [hEq k, hcomb k]
  rw [hgoal]
  have h1 : Summable fun k => (1 / 2 : ℂ)
      * T k (psdUnitVec (unitVector p + unitVector q)) i j :=
    ((halt_entry_summable_psd T hc hb (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  have h2 : Summable fun k => (Complex.I / 2)
      * T k (psdUnitVec (unitVector p + Complex.I • unitVector q)) i j :=
    ((halt_entry_summable_psd T hc hb (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  have h3 : Summable fun k => ((1 + Complex.I) / 2)
      * T k (psdUnitVec (unitVector p)) i j :=
    ((halt_entry_summable_psd T hc hb (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  have h4 : Summable fun k => ((1 + Complex.I) / 2)
      * T k (psdUnitVec (unitVector q)) i j :=
    ((halt_entry_summable_psd T hc hb (psdUnitVec_posSemidef _) i j).hasSum.mul_left _).summable
  exact ((((h1.add h2).sub h3).sub h4).hasSum.mul_left c).summable

/-- For a completely positive series satisfying `TraceSeriesBound`, each output entry is
summable on every operator. -/
theorem cpSeries_entry_summable {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T) (X : Operator D)
    (i j : Fin D) : Summable fun k => T k X i j := by
  have hsplit : (fun k => T k X i j)
      = fun k => ∑ p : Fin D, ∑ q : Fin D,
          T k (((X p q : ℂ)) • (Matrix.single p q (1 : ℂ) : Operator D)) i j := by
    funext k
    conv_lhs => rw [eq_sum_matrixUnit X]
    simp only [map_sum, Matrix.sum_apply]
  rw [hsplit]
  refine summable_finset_sum' _ _ fun p _ =>
    summable_finset_sum' _ _ fun q _ => halt_entry_summable_single T hc hb _ p q i j

/-- The complex-linear map obtained by summing a completely positive series entrywise under
`TraceSeriesBound`. -/
noncomputable def cpSeriesLimit {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T) :
    Operator D →ₗ[ℂ] Operator D where
  toFun X := fun i j => ∑' k, T k X i j
  map_add' X Y := by
    funext i j
    have hx : HasSum (fun k => T k X i j) _ :=
      (cpSeries_entry_summable T hc hb X i j).hasSum
    have hy : HasSum (fun k => T k Y i j) _ :=
      (cpSeries_entry_summable T hc hb Y i j).hasSum
    have hcomb := (hx.add hy).tsum_eq
    simpa [map_add, Matrix.add_apply] using hcomb
  map_smul' c X := by
    funext i j
    have hx : HasSum (fun k => T k X i j) _ :=
      (cpSeries_entry_summable T hc hb X i j).hasSum
    have hcomb := (hx.mul_left c).tsum_eq
    simpa [map_smul, Matrix.smul_apply, smul_eq_mul] using hcomb

/-- Each entry of `cpSeriesLimit` equals the infinite sum of the corresponding output entries. -/
theorem cpSeriesLimit_apply {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T) (X : Operator D)
    (i j : Fin D) :
    cpSeriesLimit T hc hb X i j = ∑' k, T k X i j := rfl

/-- The series limit of the completely positive maps preserves positive semidefiniteness. -/
theorem cpSeriesLimit_posSemidef {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T)
    {X : Operator D} (hX : X.PosSemidef) :
    (cpSeriesLimit T hc hb X).PosSemidef :=
  posSemidef_of_tsum_entries (fun k => (hc k).positive hX)
    (fun i j => cpSeries_entry_summable T hc hb X i j)

/-- The finite partial sums of the completely positive series converge on every input to
`cpSeriesLimit`. -/
theorem cpSeriesLimit_tendsto {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T) (X : Operator D) :
    Filter.Tendsto (fun n => (∑ k ∈ Finset.range n, T k X)) Filter.atTop
      (nhds (cpSeriesLimit T hc hb X)) := by
  rw [tendsto_matrix_iff_entrywise]
  intro i j
  have hEq : (fun n => (∑ k ∈ Finset.range n, T k X) i j)
      = fun n => ∑ k ∈ Finset.range n, T k X i j := by
    funext n
    rw [Matrix.sum_apply]
  rw [hEq]
  exact (cpSeries_entry_summable T hc hb X i j).hasSum.tendsto_sum_nat

/-- The entrywise series limit of completely positive maps satisfying `TraceSeriesBound` is
completely positive. -/
theorem cpSeriesLimit_completelyPositive {D : ℕ} (T : ℕ → (Operator D →ₗ[ℂ] Operator D))
    (hc : ∀ k, CompletelyPositive (T k)) (hb : TraceSeriesBound T) :
    CompletelyPositive (cpSeriesLimit T hc hb) := by
  intro r A hA
  have hpsd : ∀ k, (ChannelAmplification (T k) r A).PosSemidef := fun k =>
    (hc k) r A hA
  have hsum : ∀ x y : Fin r × Fin D,
      Summable fun k => ChannelAmplification (T k) r A x y := by
    intro x y
    exact cpSeries_entry_summable T hc hb
      (fun i j => A (x.1, i) (y.1, j)) x.2 y.2
  have hcore := posSemidef_of_tsum_entries hpsd hsum
  have hEq : ChannelAmplification (cpSeriesLimit T hc hb) r A
      = Matrix.of fun x y => ∑' k, ChannelAmplification (T k) r A x y := by
    ext x y
    simp only [ChannelAmplification, cpSeriesLimit_apply, Matrix.of_apply]
  rw [hEq]
  exact hcore

end MixedClockSeries

/-- With positive branch prices, the charge-indexed halting maps at a fixed output satisfy
`MixedClockSeries.TraceSeriesBound`. -/
theorem mixedHaltMap_series_bound {C L O : Type} [Fintype C] [Fintype L]
    [Fintype O] [DecidableEq O] {D : ℕ}
    (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ)
    (hp : ∀ c l, 0 < price c l) (c : C) (o : O) :
    MixedClockSeries.TraceSeriesBound (fun k => mixedHaltMap I dest price k c o k) := by
  intro N P hP
  apply le_trans _ (mixedHaltMap_partial_bound I dest price hp c N hP)
  apply Finset.single_le_sum _ (Finset.mem_univ o)
  intro out _
  apply Finset.sum_nonneg
  intro k _
  exact (RCLike.nonneg_iff.mp
    (((mixedHaltMap_cp_tni I dest price k c out k).1.positive hP).trace_nonneg)).1

/-- With positive branch prices, there are output-indexed completely positive, trace
non-increasing halting maps given on density operators by limits of charge partial sums.
Their total output trace is at most one. -/
theorem mixed_instrument_unbounded_output_cp_limit :
    ∀ (C L O : Type) [Fintype C] [Fintype L] [Fintype O] [DecidableEq O]
      (D : ℕ) (I : C → Instrument L D D) (dest : C → L → O ⊕ C)
      (price : C → L → ℕ),
      (∀ c l, 0 < price c l) → ∀ c : C,
      ∃ Halt : O → (Operator D →ₗ[ℂ] Operator D),
        (∀ o, CompletelyPositive (Halt o) ∧ TraceNonIncreasing (Halt o)) ∧
        (∀ ρ : ClockDensity D, (∑ o, (Matrix.trace (Halt o ρ.val)).re) ≤ 1 ∧
          ∀ o, Filter.Tendsto
            (fun N => ∑ k ∈ Finset.range N, mixedHaltMap I dest price k c o k ρ.val)
            Filter.atTop (nhds (Halt o ρ.val))) := by
  intro C L O _ _ _ _ D I dest price hp c
  let T : O → ℕ → (Operator D →ₗ[ℂ] Operator D) :=
    fun o k => mixedHaltMap I dest price k c o k
  have hc : ∀ o k, CompletelyPositive (T o k) :=
    fun o k => (mixedHaltMap_cp_tni I dest price k c o k).1
  have hb : ∀ o, MixedClockSeries.TraceSeriesBound (T o) :=
    fun o => mixedHaltMap_series_bound I dest price hp c o
  let Halt : O → (Operator D →ₗ[ℂ] Operator D) :=
    fun o => MixedClockSeries.cpSeriesLimit (T o) (hc o) (hb o)
  have hlim (o : O) (X : Operator D) : Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, T o k X) Filter.atTop (nhds (Halt o X)) :=
    MixedClockSeries.cpSeriesLimit_tendsto (T o) (hc o) (hb o) X
  have htrace (o : O) (X : Operator D) : Filter.Tendsto
      (fun N => (Matrix.trace (∑ k ∈ Finset.range N, T o k X)).re)
      Filter.atTop (nhds (Matrix.trace (Halt o X)).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp (tendsto_matrix_trace (hlim o X))
  refine ⟨Halt, ?_, ?_⟩
  · intro o
    refine ⟨MixedClockSeries.cpSeriesLimit_completelyPositive (T o) (hc o) (hb o), ?_⟩
    intro X hX
    apply le_of_tendsto (htrace o X)
    apply Filter.Eventually.of_forall
    intro N
    simpa only [Matrix.trace_sum, Complex.re_sum] using hb o N X hX
  · intro ρ
    refine ⟨?_, fun o => hlim o ρ.val⟩
    apply le_of_tendsto (tendsto_finsetSum _ (fun o _ => htrace o ρ.val))
    apply Filter.Eventually.of_forall
    intro N
    simpa only [Matrix.trace_sum, Complex.re_sum] using
      mixedHaltMap_density_partial_bound I dest price hp c ρ N

end Qatlib.Concepts.MixedInstrument.ClockBridge
