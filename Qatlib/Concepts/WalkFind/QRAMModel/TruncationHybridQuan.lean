/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.QRAMModel.TruncationHybridStat
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Hybrid bound for truncated unitary evolution

This module proves the hybrid estimate `TruncationHybrid` for two finite sequences of unitary
gates. Agreement away from specified bad components bounds the final state discrepancy by twice
the sum of their Euclidean norms.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `one_step_bad`: bounds the increase of error in one unitary step.
* `truncationHybrid_answer`: proves the accumulated hybrid bound.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.QRAMModel

open Matrix
open scoped BigOperators

/-- Executing a gate-list prefix of length `n + 1` equals applying gate `n` after executing the
prefix of length `n`. -/
private theorem prefix_step {H : Type} [Fintype H] [DecidableEq H]
    {T : ℕ} (U : Fin T → Matrix H H ℂ) (ψ : QState H) (n : ℕ) (hn : n < T) :
    Run 1 (((List.ofFn U).take (n+1)).map Step.gate) ψ =
      U ⟨n, hn⟩ *ᵥ Run 1 (((List.ofFn U).take n).map Step.gate) ψ := by
  rw [List.take_succ_eq_append_getElem (by simpa using! hn), List.map_append, run_append]
  simp [ApplyGate]

/-- If two unitary gates agree on the ideal state minus its bad component, the next discrepancy
is at most twice the bad-component norm plus the previous discrepancy. -/
private theorem one_step_bad {H : Type} [Fintype H] [DecidableEq H]
    (U V : Matrix H H ℂ) (ideal actual bad : QState H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hgood : U *ᵥ (ideal-bad) = V *ᵥ (ideal-bad)) :
    ‖toEuclidean_fromVec (U *ᵥ ideal - V *ᵥ actual)‖ ≤
      2*‖toEuclidean_fromVec bad‖ + ‖toEuclidean_fromVec (ideal-actual)‖ := by
  have heq : U *ᵥ ideal - V *ᵥ actual =
      (U *ᵥ bad - V *ᵥ bad) + V *ᵥ (ideal-actual) := by
    simp only [mulVec_sub] at hgood ⊢
    ext i
    have hh := congrFun hgood i
    simp only [Pi.sub_apply, Pi.add_apply] at hh ⊢
    linear_combination hh
  rw [heq]
  have hadd : ∀ a b : QState H, toEuclidean_fromVec (a+b) =
      toEuclidean_fromVec a + toEuclidean_fromVec b := fun _ _ => rfl
  have hsub : ∀ a b : QState H, toEuclidean_fromVec (a-b) =
      toEuclidean_fromVec a - toEuclidean_fromVec b := fun _ _ => rfl
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have hdiff := norm_sub_le (toEuclidean_fromVec (U *ᵥ bad))
    (toEuclidean_fromVec (V *ᵥ bad))
  rw [← hsub] at hdiff
  change ‖toEuclidean_fromVec (ApplyGate U bad - ApplyGate V bad)‖ ≤
    ‖toEuclidean_fromVec (ApplyGate U bad)‖ +
    ‖toEuclidean_fromVec (ApplyGate V bad)‖ at hdiff
  rw [norm_applyGate_of_mem_unitaryGroup hU,
    norm_applyGate_of_mem_unitaryGroup hV] at hdiff
  change ‖toEuclidean_fromVec (U *ᵥ bad - V *ᵥ bad)‖ ≤
    ‖toEuclidean_fromVec bad‖ + ‖toEuclidean_fromVec bad‖ at hdiff
  change ‖toEuclidean_fromVec (U *ᵥ bad - V *ᵥ bad)‖ +
    ‖toEuclidean_fromVec (ApplyGate V (ideal-actual))‖ ≤ _
  rw [norm_applyGate_of_mem_unitaryGroup hV]
  linarith

/-- The final discrepancy of the two unitary evolutions is at most twice the sum of the
specified bad-component norms [Ambainis2007ElementDistinctness]. -/
theorem truncationHybrid_answer : TruncationHybrid := by
  intro H _ _ T U V bad ψ hU hV hgood
  let cost : ℕ → ℝ := fun n => if h : n < T then 2*‖toEuclidean_fromVec (bad ⟨n,h⟩)‖ else 0
  have hprefix : ∀ n, n ≤ T →
      ‖toEuclidean_fromVec (Run 1 (((List.ofFn U).take n).map Step.gate) ψ -
        Run 1 (((List.ofFn V).take n).map Step.gate) ψ)‖ ≤
        ∑ i ∈ Finset.range n, cost i := by
    intro n
    induction n with
    | zero => intro _; simp [toEuclidean_fromVec]
    | succ n ih =>
      intro hn
      have hlt : n < T := by omega
      rw [prefix_step U ψ n hlt, prefix_step V ψ n hlt, Finset.sum_range_succ]
      have hstep := one_step_bad (U ⟨n,hlt⟩) (V ⟨n,hlt⟩)
        (Run 1 (((List.ofFn U).take n).map Step.gate) ψ)
        (Run 1 (((List.ofFn V).take n).map Step.gate) ψ)
        (bad ⟨n,hlt⟩) (hU _) (hV _) (hgood ⟨n,hlt⟩)
      have hprev := ih (by omega)
      simp only [cost, dif_pos hlt]
      linarith
  have h := hprefix T le_rfl
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at h
  convert! h using 1
  rw [← Fin.sum_univ_eq_sum_range]
  simp [cost]

end Qatlib.Concepts.WalkFind.QRAMModel
