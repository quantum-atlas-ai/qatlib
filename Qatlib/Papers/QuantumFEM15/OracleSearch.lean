/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchConsumers
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Oracle search reductions for finite elements

This module states a threshold criterion for recovering a search decision from an approximate
half integral. It also transfers the workspace oracle search lower bound to unitary circuits
whose decoded marked output succeeds with probability at least two thirds. See
[MontanaroPallister2016].

## Main statements

* `half_integral_decides_search`: If the half integral is at least `C` below `N / 2` and zero
  above it, a uniform approximation with error `ε` and `2 * ε < C` decides `y₀ < N / 2` by
  testing whether its value exceeds `ε`.
* `oracular_fem_query_lower_bound`: For `n ≥ 3`, a normalized unitary workspace oracle circuit
  that identifies every marked register with probability at least `2 / 3` uses at least `√(card
  (Reg n)) / 8` queries.

## References

* [Montanaro and Pallister, 2016][MontanaroPallister2016]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Real
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Papers.QuantumFEM15.OracleSearch

/-- If the half integral is at least `C` below `N / 2` and zero above it, a uniform
approximation with error `ε` and `2 * ε < C` decides `y₀ < N / 2` by testing whether its
value exceeds `ε`. See [MontanaroPallister2016]. -/
theorem half_integral_decides_search
    (N : ℕ) (halfIntegral : ℕ → ℝ) (C ε : ℝ) (_hC : 0 < C) (_hε0 : 0 < ε)
    (hε : 2 * ε < C)
    (hsmall : ∀ y₀, y₀ < N / 2 → C ≤ halfIntegral y₀)
    (hzero : ∀ y₀, N / 2 ≤ y₀ → halfIntegral y₀ = 0)
    (approx : ℕ → ℝ) (happrox : ∀ y₀, |approx y₀ - halfIntegral y₀| ≤ ε) :
    ∀ y₀, (y₀ < N / 2 ↔ ε < approx y₀) := by
  intro y₀
  constructor
  · intro hy
    have hge : C ≤ halfIntegral y₀ := hsmall y₀ hy
    have := (abs_le.mp (happrox y₀)).1

    nlinarith
  · intro hgt
    by_contra hcon
    push Not at hcon
    have hy : N / 2 ≤ y₀ := by omega
    have hz : halfIntegral y₀ = 0 := hzero y₀ hy
    have := (abs_le.mp (happrox y₀)).2

    nlinarith

/-- For `n ≥ 3`, a normalized unitary workspace oracle circuit that identifies every marked
register with probability at least `2 / 3` uses at least `√(card (Reg n)) / 8` queries. See
[MontanaroPallister2016]. -/
theorem oracular_fem_query_lower_bound {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (C : Circuit ((Reg n × Bool) × W))
    (ψ : QState ((Reg n × Bool) × W))
    (decode : ((Reg n × Bool) × W) → Option (Reg n))
    (hn : 3 ≤ n) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hmark : ∀ x : Reg n, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x))) C ψ)
        (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    Real.sqrt (Fintype.card (Reg n) : ℝ) / 8 ≤ (QueryCount C : ℝ) := by

  have hlb : (Fintype.card (Reg n) : ℝ) ≤ 64 * (QueryCount C : ℝ) ^ 2 :=
    (Qatlib.Concepts.QueryComplexity.AdversarySearch.workspace_search_matching_actual_consumer
      n w C ψ decode hn hC hψ hmark).1
  have hm : (0 : ℝ) ≤ (QueryCount C : ℝ) := by positivity
  have hN : (0 : ℝ) ≤ (Fintype.card (Reg n) : ℝ) := by positivity

  have hsqrt : Real.sqrt (Fintype.card (Reg n) : ℝ) ≤ 8 * (QueryCount C : ℝ) := by
    calc Real.sqrt (Fintype.card (Reg n) : ℝ)
        ≤ Real.sqrt (64 * (QueryCount C : ℝ) ^ 2) := Real.sqrt_le_sqrt hlb
      _ = 8 * (QueryCount C : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64),
              Real.sqrt_sq hm]
          norm_num

  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 8)]
  nlinarith [hsqrt]

end Qatlib.Papers.QuantumFEM15.OracleSearch
