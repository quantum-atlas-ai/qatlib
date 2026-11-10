/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanRecoveryProbability
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

theorem booleanSampleCandidate_eq_iff_hits_outside {n m : ℕ}
    (H : AddSubgroup (BooleanVec n)) (samples : Fin m → BooleanVec n)
    (hsupported : ∀ i, samples i ∈ booleanOrthogonal H) :
    booleanSampleCandidate samples = H ↔
      ∀ x : BooleanVec n, x ∉ H → ∃ i, booleanDot x (samples i) ≠ 0 := by
  classical
  have hcomm (x a : BooleanVec n) : booleanDot x a = booleanDot a x := by
    simp only [booleanDot, mul_comm]
  have hHle : H ≤ booleanSampleCandidate samples :=
    (le_booleanSampleCandidate_iff H samples).2 hsupported
  constructor
  · intro heq x hxH
    by_contra hmiss
    push Not at hmiss
    have hxcand : x ∈ booleanSampleCandidate samples := by
      rw [mem_booleanSampleCandidate]
      intro i
      rw [hcomm]
      exact hmiss i
    rw [heq] at hxcand
    exact hxH hxcand
  · intro hhit
    apply le_antisymm ?_ hHle
    intro x hxcand
    by_contra hxH
    obtain ⟨i, hi⟩ := hhit x hxH
    have hzero := (mem_booleanSampleCandidate samples x).1 hxcand i
    rw [hcomm] at hzero
    exact hi hzero

variable {n : ℕ} {R : Type*}
  [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem hiddenSubgroupSampleDist_boolean_recovery_success_eq_hit_event
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) = H) =
      (hiddenSubgroupSampleDist f e).probEvent
        (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∀ x : BooleanVec n, x ∉ H →
            ∃ i, booleanDot x (booleanDecodedSamples xs i) ≠ 0) := by
  apply hiddenSubgroupSampleDist_boolean_event_congr f H hf e m
  intro xs hs
  exact booleanSampleCandidate_eq_iff_hits_outside H (booleanDecodedSamples xs) hs

theorem hiddenSubgroupFreshSamples_boolean_recovery_success_eq_hit_event
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H)
    (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) = H),
      hiddenSubgroupFreshSamples f e m xs) =
      ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∀ x : BooleanVec n, x ∉ H →
            ∃ i, booleanDot x (booleanDecodedSamples xs i) ≠ 0),
        hiddenSubgroupFreshSamples f e m xs := by
  rw [hiddenSubgroupFreshSamples_event, hiddenSubgroupFreshSamples_event,
    hiddenSubgroupSampleDist_boolean_recovery_success_eq_hit_event f H hf e m]

end Qatlib.Concepts.HspRecovery.ReductionCore
