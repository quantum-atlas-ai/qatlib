/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.CubeQueryInterfaces

/-!
# Polynomial representation of query acceptance probabilities

`actual_query_acceptance_polynomial` represents the measurement probability of an actual Boolean
bit-oracle circuit by a real multivariate polynomial on Boolean inputs. The total degree is at
most twice the number of queries, as in the polynomial method of [BealsEtAl2001]. The statement
allows an arbitrary initial state vector and a finite measurement event.

## Main statements

* `actual_query_acceptance_polynomial`: an acceptance polynomial of degree at most `2 *
  QueryCount C`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.Concentration
open scoped Classical BigOperators
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- The measurement probability of the Boolean bit-oracle circuit is represented on Boolean
inputs by a real multivariate polynomial of total degree at most twice its query count
[BealsEtAl2001]. -/
theorem actual_query_acceptance_polynomial {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (psi : QState (PolynomialWorkspace (Fin n) W)) (E : Finset (PolynomialWorkspace (Fin n) W)) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 2 * QueryCount C ∧
      ∀ X : Fin n → Bool, MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) P =
        MeasureProb (Run (TensorGate (BitOracleOn X) 1) C psi) E := by
  obtain ⟨c,hc,hf⟩ :=
    Qatlib.Concepts.ProbabilityCore.Concentration.circuit_cube_degree n W C psi E
  let P : MvPolynomial (Fin n) ℝ :=
    ∑ S : Finset (Fin n), MvPolynomial.C (c S)*∏ i ∈ S, MvPolynomial.X i
  refine ⟨P,?_,?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro S _
    by_cases hs : 2 * QueryCount C < S.card
    · simp [hc S hs]
    · have hp : (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree ≤ S.card := by
        apply (MvPolynomial.totalDegree_finsetProd S _).trans
        simp
      have he := MvPolynomial.totalDegree_mul (MvPolynomial.C (c S)) (∏ i ∈ S, MvPolynomial.X i)
      simp only [MvPolynomial.totalDegree_C,zero_add] at he
      exact he.trans (hp.trans (Nat.le_of_not_gt hs))
  · intro X
    simp only [P,MvPolynomial.eval_sum,MvPolynomial.eval_mul,MvPolynomial.eval_C,
      MvPolynomial.eval_prod,MvPolynomial.eval_X]
    exact (hf X).symm

end Qatlib.Concepts.ProbabilityCore.Concentration
