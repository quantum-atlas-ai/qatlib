/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorConsumers

set_option backward.isDefEq.respectTransparency false

/-!
# Source p. 3–4 — the truncated-Taylor Hamiltonian simulation (main result)

arXiv:1412.4687v1, main theorem (p. 1 abstract and p. 3 "Hamiltonian
simulation algorithm"): for a Hamiltonian `H = Σ_j h_j U_j` written as a real
combination of unitaries with `Σ_j |h_j| ≤ Λ`, and `|t| ≤ T`, the truncated
Taylor algorithm simulates `e^{-iHt}` to error `ε = 2^{-k}` with

* a well-formed actual query circuit `cs` (all inverse calls paid),
* `3·s·K` queries and `s·(6K+13)` known-matrix gates, where
  `s = max 1 (2ΛT)` is the number of segments and
  `K = factorialTaylorCutoff (factorialTaylorPrecision s k)` the Taylor order,
* workspace error `≤ (1/2)^k ‖ψ‖` for every input state `ψ`.

The `O(log(T/ε)/loglog(T/ε))` order of `K` is Eq. (18)
(`...FactorialTaylor.LogLogCutoff.source_equation18`); here the second theorem
records the resulting query-count rate.

Library definitions and theorems:
* `Qatlib.Concepts.CoherentSim.FactorialTaylor.factorial_taylor_actual_simulation_and_paid_inverse`
  (well-formedness, exact query/gate counts, and the coherent workspace error);
* `factorialTaylorCutoff`, `factorialTaylorPrecision`, `factorialTaylorWord`,
  `taylorSegments`, `taylorFrame`, `taylorQuery`,
  `factorial_taylor_native_cutoff_and_rate`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.TaylorBounds
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.TruncTaylor14.MainResults.MainAlgorithm

/-- arXiv:1412.4687v1 main theorem: the actual truncated-Taylor word simulates
`e^{-iHt}` to workspace error `2^{-k}` with explicitly counted queries and
gates. -/
theorem source_main_result
    (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (t : ℝ) (Λ T k : ℕ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ ∧ (U j).IsHermitian)
    (hΛ : (∑ j, |h j|) ≤ Λ) (hT : |t| ≤ T) :
    let s := taylorSegments Λ T
    let K := factorialTaylorCutoff (factorialTaylorPrecision s k)
    let cs := factorialTaylorWord (I := I) h j₀ t Λ T k
    WellFormedAdjointCircuit cs ∧
      adjointQueryCount cs = 3 * s * K ∧ adjointGateCount cs = s * (6 * K + 13) ∧
      adjointQueryCount (adjointCircuit cs) = 3 * s * K ∧
      adjointGateCount (adjointCircuit cs) = s * (6 * K + 13) ∧
      (∀ ψ : QState I, ‖toEuclidean_fromVec
        (evaluate (taylorQuery U K) cs *ᵥ (taylorFrame j₀ K *ᵥ ψ) -
          taylorFrame j₀ K *ᵥ (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t *ᵥ ψ))‖ ≤
        (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec ψ‖) :=
  factorial_taylor_actual_simulation_and_paid_inverse J I h U j₀ t Λ T k hU hΛ hT

/-- The native-cutoff rate in divided form (cf. Eq. (18)). -/
private theorem cutoff_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      (factorialTaylorCutoff m : ℝ) ≤
        C * (m : ℝ) / (Nat.log 2 m : ℝ) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ :=
    factorial_taylor_native_cutoff_and_rate.2
  refine ⟨C, max m₀ 2, hC, le_max_right _ _, ?_⟩
  intro m hm
  have hm0 : m₀ ≤ m := (le_max_left _ _).trans hm
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hlogpos : 0 < Nat.log 2 m := Nat.log_pos (by norm_num) hm2
  have hcast : (factorialTaylorCutoff m : ℝ) * (Nat.log 2 m : ℝ) ≤ C * (m : ℝ) := by
    exact_mod_cast hrate m hm0
  rw [le_div_iff₀ (by exact_mod_cast hlogpos)]
  exact hcast

/-- Main-result complexity, p. 1/3: with `K` of Eq. (18) order, the query count
`3·s·K` is `O(s · log(T/ε)/loglog(T/ε))` (`m = factorialTaylorPrecision s k`
is the `Θ(log(T/ε))` precision parameter). -/
theorem source_main_result_query_complexity :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (s k : ℕ), m₀ ≤ factorialTaylorPrecision s k →
      (3 * s * factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
        C * (s : ℝ) * (factorialTaylorPrecision s k : ℝ) /
          (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := by
  obtain ⟨D, n₀, hD, hn₀, hrate⟩ := cutoff_rate
  refine ⟨3 * D, max n₀ 2, by positivity, le_max_right _ _, ?_⟩
  intro s k hm
  have hm0 : n₀ ≤ factorialTaylorPrecision s k := (le_max_left _ _).trans hm
  have hK := hrate _ hm0
  have hc : (0 : ℝ) ≤ 3 * (s : ℝ) := by positivity
  have hcast : (3 * s * factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) =
      (3 : ℝ) * (s : ℝ) * (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) := by
    ring
  rw [hcast]
  have hstep : (3 : ℝ) * (s : ℝ) * (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
      (3 : ℝ) * (s : ℝ) *
        (D * (factorialTaylorPrecision s k : ℝ) /
          (Nat.log 2 (factorialTaylorPrecision s k) : ℝ)) :=
    mul_le_mul_of_nonneg_left hK hc
  refine hstep.trans (le_of_eq ?_)
  have hlogpos : (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) ≠ 0 := by
    have := Nat.log_pos (by norm_num : 1 < 2)
      ((le_max_right _ _).trans hm : 2 ≤ factorialTaylorPrecision s k)
    exact_mod_cast ne_of_gt this
  rw [div_eq_mul_inv, div_eq_mul_inv]
  push_cast
  ring

end Qatlib.Papers.TruncTaylor14.MainResults.MainAlgorithm
