/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchBoyer96.MainResults.ActualSearch
import Qatlib.Papers.QSearchBoyer96.MainResults.CountingSampler
import Qatlib.Concepts.SearchStopping.PaidRestart.Section31ExactSuccessTigh

/-!
# Known-count search and dyadic counting endpoints

This module gathers actual-circuit guarantees for the known-count Grover iteration choice, the
quarter-density case, and dyadic Fourier counting. The statements combine success or counting
accuracy with exact query counts, and the dyadic endpoint also records its gate count and
normalized output state.

The source paper is [BoyerEtAl1998].

## Main statements

* `actual_known_count_budget`: For a nonempty marked set and the stated angle conditions, the
  floor-iteration Grover circuit has failure at most the marked density and exact query count
  `groverIterations θ`, bounded by (π/4)√(N/t).
* `actual_quarter_density`: When the marked set has exactly one quarter of a nonempty finite
  search space, one Grover iteration uses one query and succeeds with probability one.
* `actual_dyadic_counting`: For N > 0 and k ≥ 1, the dyadic counting circuit has 2ᵏ − 1 queries,
  5(2ᵏ − 1) + 3 gates, and a normalized source output. Its actual Born probabilities assign mass
  at least 8/π² to the stated count-error window with precision 2ᵏ.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SearchStopping.PaidRestart

namespace Qatlib.Papers.QSearchBoyer98.MainResults

/-- For a nonempty marked set and the stated angle conditions, the floor-iteration Grover
circuit has failure at most the marked density and exact query count `groverIterations θ`,
bounded by (π/4)√(N/t) [BoyerEtAl1998]. -/
theorem actual_known_count_budget {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hA : 0 < A.card)
    (hθ : (Real.sin θ)^2 = (A.card : ℝ)/(Fintype.card I : ℝ))
    (hs : 0 < Real.sin θ) (hc : Real.cos θ ≠ 0)
    (hθpos : 0 < θ) (hθhalf : θ ≤ Real.pi/2) :
    1 - MeasureProb (Run (SetOracle A) (GroverCircuit I (groverIterations θ))
      (Uniform I)) A ≤ (A.card : ℝ)/(Fintype.card I : ℝ) ∧
    QueryCount (GroverCircuit I (groverIterations θ)) = groverIterations θ ∧
    (QueryCount (GroverCircuit I (groverIterations θ)) : ℝ) ≤
      Real.pi/4 * Real.sqrt ((Fintype.card I : ℝ)/(A.card : ℝ)) :=
  Qatlib.Papers.QSearchBoyer96.MainResults.actual_floor_success_and_cost
    hN A θ hA hθ hs hc hθpos hθhalf

/-- When the marked set has exactly one quarter of a nonempty finite search space, one Grover
iteration uses one query and succeeds with probability one [BoyerEtAl1998]. -/
theorem actual_quarter_density {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I)
    (hquarter : 4 * A.card = Fintype.card I) :
    QueryCount (GroverCircuit I 1) = 1 ∧
    MeasureProb (Run (SetOracle A) (GroverCircuit I 1) (Uniform I)) A = 1 :=
  ⟨queryCount_groverCircuit 1, quarterDensity_success hN A hquarter⟩

/-- For k ≥ 1, the dyadic register size 2ᵏ is at least two. -/
theorem source_dyadic_guard (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- For N > 0 and k ≥ 1, the dyadic counting circuit has 2ᵏ − 1 queries, 5(2ᵏ − 1) + 3 gates,
and a normalized source output. Its actual Born probabilities assign mass at least 8/π² to
the stated count-error window with precision 2ᵏ [BoyerEtAl1998]. -/
theorem actual_dyadic_counting (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k)
    (S : Finset (Fin N)) :
    QueryCount (countedAECircuit (2^k) (QFTMatrix N) (⟨0,hN⟩ : Fin N)) = 2^k-1 ∧
    GateCount (countedAECircuit (2^k) (QFTMatrix N) (⟨0,hN⟩ : Fin N)) = 5*(2^k-1)+3 ∧
    Normalized (Qatlib.Papers.QSearchBoyer96.MainResults.sourceCountingOutput
      N (2^k) hN (source_dyadic_guard k hk) S) ∧
    (8/Real.pi^2:ℝ) ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin (2^k) =>
        |(N:ℝ)*aeEstimate (2^k) z-(S.card:ℝ)| ≤
          2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^k:ℕ)+
            Real.pi^2*(N:ℝ)/(2^k:ℕ)^2),
        MeasureProb (Qatlib.Papers.QSearchBoyer96.MainResults.sourceCountingOutput
          N (2^k) hN (source_dyadic_guard k hk) S) {p | p.1 = z} := by
  have hcost := Qatlib.Papers.QSearchBoyer96.MainResults.actual_counted_fourier_sampling_support
    N (2^k) hN (source_dyadic_guard k hk) S
  exact ⟨hcost.1, hcost.2.1,
    (Qatlib.Papers.QSearchBoyer96.MainResults.source_counting_actual_born
      N (2^k) hN (source_dyadic_guard k hk) S).1,
    Qatlib.Papers.QSearchBoyer96.MainResults.source_counting_born_accuracy
      N (2^k) hN (source_dyadic_guard k hk) S⟩

end Qatlib.Papers.QSearchBoyer98.MainResults
