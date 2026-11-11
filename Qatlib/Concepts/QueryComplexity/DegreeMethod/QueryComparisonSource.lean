/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryComparisonSourceDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparison

/-!
# Polynomial and query-model comparison results

This module collects Hamming-layer symmetrization, finite-class query minima, and the exact
polynomial degree of OR. The results connect the polynomial method of [BealsEtAl2001] to
concrete circuit and classical decision-tree formulations.

The OR comparison supplies the bound `Fintype.card I ≤ 2 * QueryCount P.circuit` under
`ZeroErrorFor`, together with the classical scan characterization. Each statement retains the
conventions and hypotheses of its underlying program model.

## Main statements

* `clause64_symmetrisation`: Layer averages are represented by a univariate polynomial of
  bounded degree.
* `clause67_complete`: Collects minimality, exact attainment, and the exact-degree query bound.
* `clause70_complete`: OR has exact degree equal to the size of a nonempty input index type.
* `clause69_lower`: Gives the stated OR query lower bound in the comparison model.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- For every real polynomial on `Fin n`, permutation and layer averages agree at valid weights
and are represented by a univariate polynomial of no greater degree [BealsEtAl2001]. -/
theorem clause64_complete :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
      (∀ k : ℕ, k ≤ n → Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage n p k
            = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k) ∧
        ∃ q : Polynomial ℝ,
          Polynomial.natDegree q ≤ MvPolynomial.totalDegree p ∧
            ∀ k : ℕ, k ≤ n → Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k = Polynomial.eval (k : ℝ) q :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryCore.stageB_query_comparison_clause64

/-- The layer averages of a real polynomial agree with its permutation averages and with
evaluations of a univariate polynomial whose degree is at most its total degree
[BealsEtAl2001]. -/
theorem clause64_symmetrisation (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (∀ k : ℕ, k ≤ n → Qatlib.Concepts.QueryComplexity.DegreeMethod.permLayerAverage n p k
          = Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k) ∧
      ∃ q : Polynomial ℝ,
        Polynomial.natDegree q ≤ MvPolynomial.totalDegree p ∧
          ∀ k : ℕ, k ≤ n → Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k = Polynomial.eval (k : ℝ) q :=
  clause64_complete n p

/-- For nonempty feasible count sets, the exact, bounded, success, and zero-error minima bound
the corresponding programs' query counts; the exact minimum is attained and bounds half the
exact polynomial degree. -/
theorem clause67_complete (M : MachineClass I W) (f : (I → Bool) → Bool)
    (hE : ∃ n, n ∈ M.exactCountSet f)
    (hB : ∃ n, n ∈ M.boundedCountSet f)
    (hS : ∃ n, n ∈ M.successCountSet f)
    (hZ : ∃ n, n ∈ M.zeroErrorCountSet f) :
    (∀ Q ∈ M.programs, Q.ExactFor f → M.minExactQueries f hE ≤ QueryCount Q.circuit) ∧
      (∃ Q ∈ M.programs, Q.ExactFor f ∧ QueryCount Q.circuit = M.minExactQueries f hE) ∧
      (∀ Q ∈ M.programs, Q.BoundedFor f → M.minBoundedQueries f hB ≤ QueryCount Q.circuit) ∧
      (∀ Q ∈ M.programs, Q.SuccessFor f → M.minSuccessQueries f hS ≤ QueryCount Q.circuit) ∧
      (∀ Q ∈ M.programs, Q.ZeroErrorFor f → M.minZeroErrorQueries f hZ ≤ QueryCount Q.circuit) ∧
      Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree (I := I) f ≤ 2 * M.minExactQueries f hE := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ hQf
    exact M.minExactQueries_le hQ hQf
  · exact M.minExactQueries_attained (h := hE)
  · intro Q hQ hQf
    exact M.minBoundedQueries_le hQ hQf
  · intro Q hQ hQf
    exact M.minSuccessQueries_le hQ hQf
  · intro Q hQ hQf
    exact M.minZeroErrorQueries_le hQ hQf
  · exact Qatlib.Concepts.QueryComplexity.DegreeMethod.minExactQueries_degree_bound (h := hE)

/-- OR on a nonempty finite Boolean index type has exact polynomial degree equal to the number
of indices [BealsEtAl2001]. -/
theorem clause70_complete (hcard : 0 < Fintype.card I) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree (I := I) orFunction = Fintype.card I := by
  have horMem : orPolynomial ∈
      {p : MvPolynomial I ℝ | ∀ g : I → Bool,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p g = if orFunction g then (1 : ℝ) else 0} := by
    intro g
    exact orPolynomial_represents g
  have hupper : Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree (I := I) orFunction
      ≤ Fintype.card I := by
    refine le_trans ?_ (orPolynomial_totalDegree_le)
    unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree
    apply csInf_le'
    exact (Set.mem_image (fun p : MvPolynomial I ℝ => p.totalDegree)
      {p : MvPolynomial I ℝ | ∀ g : I → Bool,
        Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval p g = if orFunction g then (1 : ℝ) else 0} _).2
      ⟨orPolynomial, horMem, rfl⟩
  have hlower : Fintype.card I
      ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree (I := I) orFunction := by
    unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegree
    refine le_csInf (Set.image_nonempty.mpr ⟨orPolynomial, horMem⟩) ?_
    intro b hb
    obtain ⟨p, hp, hpdeg⟩ := hb
    have hp' : ∀ g : I → Bool,
        MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p
          = if (∃ i, g i = true) then (1 : ℝ) else 0 := by
      intro g
      have hmem := hp g
      unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.boolEval at hmem
      simpa [orFunction] using hmem
    exact (Qatlib.Concepts.QueryComplexity.DegreeMethod.boolean_multilinear_or_totalDegree p hcard hp').trans_eq hpdeg
  exact le_antisymm hupper hlower

/-- A decision program satisfying `ZeroErrorFor` for OR on a nonempty index type satisfies
`Fintype.card I ≤ 2 * QueryCount P.circuit` [BealsEtAl2001]. -/
theorem clause69_lower {P : DecisionProgram I W} (hZ : P.ZeroErrorFor orFunction)
    (hcard : 0 < Fintype.card I) :
    Fintype.card I ≤ 2 * QueryCount P.circuit := by
  have hE : P.ExactFor orFunction := hZ
  have hdeg := Qatlib.Concepts.QueryComplexity.DegreeMethod.exactDegreeQueryLowerBound I W P.circuit
    P.initial P.accept orFunction hE
  rw [clause70_complete hcard] at hdeg
  exact hdeg

/-- Scanning all indices returns true exactly when there is a listed true bit, with the scan
tree's maximum query count equal to the number of indices. -/
theorem clause69_classical_upper (g : I → Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run g (orScanTree (allElements I))).1 = true ↔
        ∃ i, i ∈ allElements I ∧ g i = true ∧
          Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries (orScanTree (allElements I)) = Fintype.card I := by
  have hrun := orScanTree_run (allElements I) g
  have hmax : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries (orScanTree (allElements I)) = Fintype.card I := by
    rw [orScanTree_maxQueries, allElements_length]
  constructor
  · intro h
    obtain ⟨i, hi, hgi⟩ := (hrun.mp h)
    exact ⟨i, hi, hgi, hmax⟩
  · rintro ⟨i, hi, hgi, hmax'⟩
    exact hrun.mpr ⟨i, hi, hgi⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
