/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.ProjectorBalance

/-!
# Parity balance for event acceptance

The event acceptance function `parityAcceptance` has zero correlation with parity when twice the
circuit's query count is less than the number of input bits. The resulting equality of the even-
and odd-parity acceptance sums is stated by `parity_acceptance_sum_balance`. These results
support the parity analysis of [FarhiEtAl1998].

## Main statements

* `parity_signed_acceptance_sum_eq_zero`: If `2 * QueryCount C < n`, the sum of event acceptance
  weighted by the parity sign vanishes.
* `parity_acceptance_sum_balance`: If `2 * QueryCount C < n`, the event acceptance sums over
  even- and odd-parity inputs are equal.

## References

* [Farhi et al., 1998][FarhiEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- If `2 * QueryCount C < n`, the sum of event acceptance weighted by the parity sign vanishes.
See [Farhi et al., 1998][FarhiEtAl1998]. -/
theorem parity_signed_acceptance_sum_eq_zero {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (E : Finset (PolynomialWorkspace (Fin n) W))
    (h2k : 2 * QueryCount C < n) :
    ∑ f : Fin n → Bool, boolSign f * parityAcceptance C ψ E f = 0 := by
  exact cube_degree_signed_sum _
    (Qatlib.Concepts.ProbabilityCore.Concentration.circuit_cube_degree n W C ψ E) h2k

/-- If `2 * QueryCount C < n`, the event acceptance sums over even- and odd-parity inputs are
equal. -/
theorem parity_acceptance_sum_balance {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (E : Finset (PolynomialWorkspace (Fin n) W))
    (h2k : 2 * QueryCount C < n) :
    (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = false), parityAcceptance C ψ E f) =
      ∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), parityAcceptance C ψ E f :=
  sum_balance_of_signed_sum_zero _ (parity_signed_acceptance_sum_eq_zero C ψ E h2k)

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
