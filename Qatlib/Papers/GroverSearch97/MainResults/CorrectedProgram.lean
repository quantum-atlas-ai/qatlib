/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverSearch96.MainResults.LocalImplementation
import Qatlib.Papers.GroverSearch96.MainResults.GainConvergence

/-!
# An initialized local Grover search program

`corrected_initialized_search` packages singleton search as a unitary local circuit initialized
in the zero basis state with clean ancillary registers. For at least two qubits, it realizes the
embedded Grover state and has success probability strictly above one half for every target.

The same iteration count satisfies both the strict square root bound and the `(π/4) * sqrt
(2^n)` bound, with explicit query and local gate counts. See [Grover1997].

## Main statements

* `corrected_initialized_search`: For `n ≥ 2`, there is a unitary initialized local search
  circuit with `k < sqrt (2^n)` and `k ≤ (π/4) * sqrt (2^n)`, exactly `k` queries, and at most
  `(34*k+1)*n` gates. Its normalized output is the embedded Grover state and finds every
  singleton target with probability strictly above `1/2`.

## References

* [Grover, 1997][Grover1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile

namespace Qatlib.Papers.GroverSearch97.MainResults

/-- For `n ≥ 2`, there is a unitary initialized local search circuit with `k < sqrt (2^n)` and
`k ≤ (π/4) * sqrt (2^n)`, exactly `k` queries, and at most `(34*k+1)*n` gates. Its
normalized output is the embedded Grover state and finds every singleton target with
probability strictly above `1/2`. See [Grover1997]. -/
theorem corrected_initialized_search (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, (k : ℝ) < Real.sqrt (2 ^ n : ℝ) ∧
      (k : ℝ) ≤ Real.pi / 4 * Real.sqrt (2 ^ n : ℝ) ∧
      QueryCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) = k ∧
      GateCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) ≤
        (34 * k + 1) * n ∧
      IsUnitaryCircuit (localPreparedAACircuit n (localHadamardReflectionSteps n) k) ∧
      Normalized (reflectionEmbed n (Ket (ZeroStr n))) ∧
      ∀ w : Reg n,
        Run (reflectionLift n (SetOracle {w}))
          (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
          (reflectionEmbed n (Ket (ZeroStr n))) = reflectionEmbed n (GroverState {w} k) ∧
        Normalized (Run (reflectionLift n (SetOracle {w}))
          (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
          (reflectionEmbed n (Ket (ZeroStr n)))) ∧
        (1 / 2 : ℝ) < MeasureProb (Run (reflectionLift n (SetOracle {w}))
          (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
          (reflectionEmbed n (Ket (ZeroStr n))))
          (Finset.univ.filter (fun z => (reflectionSplit n z).1 = w)) := by
  have hN4 : 4 ≤ Fintype.card (Reg n) := by
    rw [card_reg]
    calc 4 = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let k := groverIterations (knownCountAngle ((1 : ℝ) / Fintype.card (Reg n)))
  have hb := knownCount_query_budget (I := Reg n) (m := 1)
    (by norm_num) (by omega : 1 < Fintype.card (Reg n))
  simp only [Nat.cast_one] at hb
  rw [Qatlib.Papers.GroverSearch96.MainResults.budget_rewrite] at hb
  have hcost := Qatlib.Papers.GroverSearch96.MainResults.local_source_grover_state_and_cost n k ∅
  refine ⟨k, ?_, hb, hcost.2.1, hcost.2.2.1, hcost.2.2.2,
    Qatlib.Papers.GroverSearch96.MainResults.normalized_clean_embed n _ (normalized_ket _), ?_⟩
  · have hs : 0 < Real.sqrt (2 ^ n : ℝ) := by positivity
    have hp : Real.pi / 4 < 1 := by linarith [Real.pi_lt_d2]
    exact hb.trans_lt (by nlinarith)
  · intro w
    refine ⟨(Qatlib.Papers.GroverSearch96.MainResults.local_source_grover_state_and_cost n k {w}).1, ?_, ?_⟩
    · rw [(Qatlib.Papers.GroverSearch96.MainResults.local_source_grover_state_and_cost n k {w}).1]
      exact Qatlib.Papers.GroverSearch96.MainResults.normalized_clean_embed n _
        (normalized_groverState Fintype.card_pos {w} k)
    · have hr := Qatlib.Papers.GroverSearch96.MainResults.local_source_readout n k ({w} : Finset (Reg n))
      simp only [Finset.mem_singleton] at hr
      rw [hr]
      have hs := knownCount_success (I := Reg n) Fintype.card_pos ({w} : Finset (Reg n))
        (m := 1) (by simp) (by norm_num) (by omega : 1 < Fintype.card (Reg n))
      simp only [Nat.cast_one] at hs
      have hq : (1 : ℝ) / Fintype.card (Reg n) ≤ 1 / 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        exact_mod_cast hN4
      exact (show (1 / 2 : ℝ) < 1 - (1 : ℝ) / Fintype.card (Reg n) by linarith).trans_le hs

end Qatlib.Papers.GroverSearch97.MainResults
