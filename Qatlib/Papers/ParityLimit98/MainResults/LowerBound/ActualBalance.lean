/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.ProjectorBalance
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

theorem parity_signed_acceptance_sum_eq_zero {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (E : Finset (PolynomialWorkspace (Fin n) W))
    (h2k : 2 * QueryCount C < n) :
    ∑ f : Fin n → Bool, boolSign f * parityAcceptance C ψ E f = 0 := by
  exact cube_degree_signed_sum _
    (Qatlib.Concepts.ProbabilityCore.Concentration.circuit_cube_degree n W C ψ E) h2k

theorem parity_acceptance_sum_balance {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (E : Finset (PolynomialWorkspace (Fin n) W))
    (h2k : 2 * QueryCount C < n) :
    (∑ f ∈ Finset.univ.filter (fun f => parityOddB f = false), parityAcceptance C ψ E f) =
      ∑ f ∈ Finset.univ.filter (fun f => parityOddB f = true), parityAcceptance C ψ E f :=
  sum_balance_of_signed_sum_zero _ (parity_signed_acceptance_sum_eq_zero C ψ E h2k)

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
