/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary

/-!
# Lower bounds for adaptive observed circuits

This module applies polynomial representations and history purification to lower bounds for
observed circuits. It proves parity bounds for general well formed adaptive circuits and for a
single projective branch followed by queries.

It also transfers negative adversary inequalities to these models using ordinary circuits with
the same query count. The parity argument uses the polynomial method of [BealsEtAl2001]; the
adversary statements retain the explicit error dependent prefactor of [HoyerLeeSpalek2007].

## Main statements

* `observed_actual_adaptive_parity_query_lower_bound`: bounded error parity requires at least
  half as many queries as input bits.
* `observed_actual_adaptive_negative_adversary_lower_bound`: the negative adversary inequality
  for well formed adaptive circuits.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Matrix
open scoped Matrix.Norms.L2Operator

/-- A well formed observed circuit computing parity of `n` positive input bits with error at
most one third satisfies `n ≤ 2 * observedQueryDepth P`. This is the adaptive parity
consequence of [Beals et al., Proposition 6.4][BealsEtAl2001]. -/
theorem observed_actual_adaptive_parity_query_lower_bound
    (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (hn : 0 < n) (hP : observedWellFormed P) (hψ : Normalized ψ)
    (hyp : ∀ f : Fin n → Bool,
      |observedAcceptance (workspaceBitOracle (W := W) f) P ψ -
        (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)| ≤ 1/3) :
    n ≤ 2 * observedQueryDepth P := by
  obtain ⟨p, hd, _, he⟩ :=
    observed_actual_multilinear_acceptance_polynomial n W P ψ hn hP hψ
  have hdeg := parity_boolean_approximation_degree p (fun f => by rw [he f]; exact hyp f)
  simpa only [Fintype.card_fin] using hdeg.trans hd

/-- A projective branch circuit whose acceptance approximates parity within one third satisfies
`n ≤ 2 * observedQueryDepth (observedProjectQueryBranch P a b k)`. -/
theorem observed_project_query_branch_parity_lower_bound
    (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (hP : IsOrthogonalProjector P) (a b : Bool) (k : ℕ)
    (ψ : QState ((Fin n × Bool) × W))
    (hyp : ∀ f : Fin n → Bool,
      |observedAcceptance (workspaceBitOracle (W := W) f) (observedProjectQueryBranch P a b k) ψ -
        (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)| ≤ 1/3) :
    n ≤ 2 * observedQueryDepth (observedProjectQueryBranch P a b k) := by
  obtain ⟨p, hd, _, he⟩ := observed_project_query_branch_multilinear_polynomial P hP a b k ψ
  have hdeg := parity_boolean_approximation_degree p (fun f => by rw [he f]; exact hyp f)
  simpa only [Fintype.card_fin] using hdeg.trans hd

/-- For an orthogonal projective branch circuit computing with error `ε ∈ [0, 1/2]`, the
negative adversary quantity `(1 - 2√(ε(1 - ε)))‖Γ‖` is at most twice the query depth times
`advFilterBound input Γ`, under the stated Hermitian and output separation hypotheses. -/
theorem observed_project_query_branch_negative_adversary_lower_bound
    (X W : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype W] [DecidableEq W] (n : ℕ)
    (input : X → Fin n → Bool) (Γ : Matrix X X ℂ) (f : X → Bool)
    (P : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ)
    (hP : IsOrthogonalProjector P) (a b : Bool) (k : ℕ)
    (ψ : QState ((Fin n × Bool) × W)) (ε : ℝ)
    (hΓ : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hψ : Normalized ψ) (he₀ : 0 ≤ ε) (he₁ : ε ≤ 1/2)
    (hsuccess : ∀ x, if f x then
      1-ε ≤ observedAcceptance (workspaceBitOracle (W := W) (input x)) (observedProjectQueryBranch P a b k) ψ
      else observedAcceptance (workspaceBitOracle (W := W) (input x)) (observedProjectQueryBranch P a b k) ψ ≤ ε) :
    (1-2*Real.sqrt (ε*(1-ε))) * ‖Γ‖ ≤
      2 * observedQueryDepth (observedProjectQueryBranch P a b k) * advFilterBound input Γ := by
  let C := adaptiveProjectQueryBranchCircuit P k
  let φ := deferredObservedInput (R := 1) ψ
  let E := adaptiveBinaryHistoryEvent (n := n) (W := W) a b
  have hcost := adaptiveProjectQueryBranchCircuit_cost_and_unitary hP k
  have hφ : Normalized φ := deferredObservedInput_normalized hψ
  have hs : ∀ x, 1-ε ≤ MeasureProb
      (Run (workspaceBitOracle (W := W × Fin 2 × Bool) (input x)) C φ) (if f x then E else Eᶜ) := by
    intro x
    have ht := observed_project_query_branch_acceptance_transport P a b k (input x) ψ
    change MeasureProb (Run (workspaceBitOracle (W := W × Fin 2 × Bool) (input x)) C φ) E = _ at ht
    have hx := hsuccess x
    cases hf : f x
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      have hn := hcost.1.normalized_run (workspaceBitOracle_unitary (input x)) hφ
      have hm : MeasureProb (Run (workspaceBitOracle (W := W × Fin 2 × Bool) (input x)) C φ) E +
          MeasureProb (Run (workspaceBitOracle (W := W × Fin 2 × Bool) (input x)) C φ) Eᶜ = 1 := by
        rw [← measureProb_union _ disjoint_compl_right, Finset.union_compl, measureProb_univ hn]
      linarith
    · simp only [hf, ↓reduceIte] at hx ⊢
      exact ht.symm ▸ hx
  have hb := negative_adversary_actual_bounded_error_circuit_lower_bound
    X (W × Fin 2 × Bool) n input Γ f C φ E ε hΓ hz hcost.1 hφ he₀ he₁ hs
  simpa only [C, hcost.2.1, observedProjectQueryBranch_depth] using hb

/-- For a well formed observed circuit computing with error `ε ∈ [0, 1/2]` from a normalized
state, `(1 - 2√(ε(1 - ε)))‖Γ‖` is at most twice the query depth times `advFilterBound input
Γ`, under the stated Hermitian and output separation hypotheses. This transfers the Boolean
output adversary bound of [Hoyer, Lee, and Spalek, Theorem 2][HoyerLeeSpalek2007]. -/
theorem observed_actual_adaptive_negative_adversary_lower_bound
    (X W : Type) [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype W] [DecidableEq W] [Nonempty W] (n : ℕ)
    (input : X → Fin n → Bool) (Γ : Matrix X X ℂ) (f : X → Bool)
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)) (ε : ℝ)
    (hn : 0 < n) (hΓ : Γ.IsHermitian) (hz : ∀ x y, f x = f y → Γ x y = 0)
    (hP : observedWellFormed P) (hψ : Normalized ψ) (he₀ : 0 ≤ ε) (he₁ : ε ≤ 1/2)
    (hsuccess : ∀ x, if f x then
      1-ε ≤ observedAcceptance (workspaceBitOracle (W := W) (input x)) P ψ
      else observedAcceptance (workspaceBitOracle (W := W) (input x)) P ψ ≤ ε) :
    (1-2*Real.sqrt (ε*(1-ε))) * ‖Γ‖ ≤
      2 * observedQueryDepth P * advFilterBound input Γ := by
  obtain ⟨R, C, hC, hcount, _, hfull⟩ :=
    observed_query_same_cost_full_branch_purification n W P hn hP
  let φ := deferredObservedInput (R := R) ψ
  let E := adaptiveObservedHistoryEvent P R
  have hφ : Normalized φ := deferredObservedInput_normalized hψ
  have hs : ∀ x, 1-ε ≤ MeasureProb
      (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C φ)
      (if f x then E else Eᶜ) := by
    intro x
    have ht := observed_full_history_acceptance_transport P R C (input x) ψ
      (hfull (input x) ψ).1 (hfull (input x) ψ).2
    change MeasureProb
        (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C φ) E = _ at ht
    have hx := hsuccess x
    cases hf : f x
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      have hn := hC.normalized_run (workspaceBitOracle_unitary (input x)) hφ
      have hm : MeasureProb (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C φ) E +
          MeasureProb (Run (workspaceBitOracle (W := W × Fin (R + 1) × Bool) (input x)) C φ) Eᶜ = 1 := by
        rw [← measureProb_union _ disjoint_compl_right, Finset.union_compl, measureProb_univ hn]
      linarith
    · simp only [hf, ↓reduceIte] at hx ⊢
      exact ht.symm ▸ hx
  have hb := negative_adversary_actual_bounded_error_circuit_lower_bound
    X (W × Fin (R + 1) × Bool) n input Γ f C φ E ε hΓ hz hC hφ he₀ he₁ hs
  simpa only [hcount] using hb

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
