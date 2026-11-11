/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.SequentialReadout

/-!
# Exact query comparison for the two executed words

This module compares the source-access counts of the explicit nested and previous sequential
words in the Monte Carlo construction associated with [KanekoEtAl2020]. With positive inner and
outer sizes, cancellation of the shared outer factor reduces the strict count comparison to `M ≤
D`.

For the instantiated body circuit and `2^d` terms, `actual_program_comparison` identifies the
exact threshold `M ≤ 2^d`.

## Main statements

* `integer_comparison`: Reduce the natural-number count inequality to `M ≤ D`.
* `actual_program_comparison`: Apply the arithmetic threshold to the explicit program counts.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Papers.MonteCarloInt20.MainResults.NestedWord
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerOracle
open Qatlib.Papers.MonteCarloInt20.MainResults.InnerCircuit
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.MonteCarloInt20.CostModels.ExecutedComparison

/-- For positive `M` and `N`, the inequality `2 * ((2 * N - 1) * (2 * M - 1)) < 4 * D * (2 * N -
1)` holds exactly when `M ≤ D`. -/
theorem integer_comparison (M N D : ℕ) (hM : 0 < M) (hN : 0 < N) :
    2*((2*N-1)*(2*M-1)) < 4*D*(2*N-1) ↔ M ≤ D := by
  have hn : 0 < 2*(2*N-1) := by omega
  rw [show 2*((2*N-1)*(2*M-1)) = (2*(2*N-1))*(2*M-1) by ring,
    show 4*D*(2*N-1) = (2*(2*N-1))*(2*D) by ring,
    Nat.mul_lt_mul_left hn]
  omega

/-- For positive `M` and `N`, the nested source-access count multiplied by the body query count
is strictly below the previous word's total source-access count exactly when `M ≤ 2^d`; see
[KanekoEtAl2020]. -/
theorem actual_program_comparison {n s d p : ℕ} (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : (ZMod (2^n))ˣ) (c seed : ZMod (2^n))
    (code : Reg s → Reg d → ZMod (2^n) → Fin (2^p+1)) (g : ℝ → ℝ) :
    (accessCount .inputForward (nestedWord s M N hM (innerBody a c seed code)
        (bodySeed n s d p seed) (fun _ => Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested.bodyGood n s d p) ((2:ℝ)^d) g)+
      accessCount .inputBackward (nestedWord s M N hM (innerBody a c seed code)
        (bodySeed n s d p seed) (fun _ => Qatlib.Papers.MonteCarloInt20.MainResults.ActualNested.bodyGood n s d p) ((2:ℝ)^d) g))*
      QueryCount (bodyCircuit (d:=d) (p:=p) a c seed (ZeroStr s)) <
      accessCount .inputForward (previousOuterWord N a c seed code g)+
        accessCount .inputBackward (previousOuterWord N a c seed code g) ↔ M ≤ 2^d := by
  have h := actual_two_program_counts M N hM hN a c seed code g
  rw [h.1,h.2]
  exact integer_comparison M N (2^d) hM hN

end Qatlib.Papers.MonteCarloInt20.CostModels.ExecutedComparison
