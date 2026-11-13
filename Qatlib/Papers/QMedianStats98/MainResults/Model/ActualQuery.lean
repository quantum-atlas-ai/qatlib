/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.Basic
import Qatlib.Concepts.ProbabilityCore.Concentration.CubeQueryInterfaces
import Qatlib.Concepts.ProbabilityCore.Concentration.ActualPolynomial

/-!
# Boolean-oracle query experiments and acceptance polynomials

This module models an actual Boolean-oracle experiment by a unitary circuit, a normalized
initial state, and a measured acceptance event. Acceptance is the probability of that event
after running the circuit with the bit oracle acting trivially on the ancillary workspace.

The module connects circuit semantics to the polynomial method in [NayakWu1998]: a `T`-query
experiment has a real acceptance polynomial of degree at most `2*T` on every Boolean input,
including a multilinear witness, and a promise computation yields an approximating polynomial.

## Main statements

- `QueryExperiment`: records a circuit and its state and measurement data.
- `QueryExperiment.acceptance_range`: bounds the actual probability between zero and one.
* `QueryExperiment.actual_multilinear_polynomial`: gives the multilinear acceptance polynomial
  of Lemma 2.6.
* `QueryExperiment.actual_approximating_polynomial`: transfers promise correctness to polynomial
  approximation.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMedianStats98.MainResults.Model
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- A Boolean-oracle query experiment consisting of a circuit on the query and ancillary
workspace, an initial state, and an acceptance event, together with circuit unitarity and
initial-state normalization. -/
structure QueryExperiment (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] where

  word : Circuit (PolynomialWorkspace (Fin n) W)

  initial : QState (PolynomialWorkspace (Fin n) W)

  event : Finset (PolynomialWorkspace (Fin n) W)

  unitary : IsUnitaryCircuit word

  normalized : Normalized initial

/-- The number of oracle-query instructions in the experiment's circuit. -/
def QueryExperiment.queries {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) : ℕ := QueryCount A.word

/-- The probability of the acceptance event after the experiment is run with the Boolean bit
oracle for input `X`, tensored with the identity on the ancillary workspace. -/
def QueryExperiment.acceptance {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (X : Fin n → Bool) : ℝ :=
  MeasureProb (Run (TensorGate (BitOracleOn X) 1) A.word A.initial) A.event

/-- The Boolean bit oracle for any input, tensored with the identity on the finite ancillary
workspace, is a unitary matrix. -/
theorem actual_oracle_unitary {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (X : Fin n → Bool) :
    TensorGate (BitOracleOn X) (1 : Matrix W W ℂ) ∈
      Matrix.unitaryGroup (PolynomialWorkspace (Fin n) W) ℂ := by
  apply tensorGate_unitary
  · apply permMatrix_unitary
    rintro ⟨i,b⟩
    cases h : X i <;> cases b <;> simp [BitFlip,h]
  · exact (Matrix.unitaryGroup W ℂ).one_mem

/-- The actual acceptance probability of a query experiment lies in `[0, 1]` for every Boolean
input. -/
theorem QueryExperiment.acceptance_range {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (X : Fin n → Bool) :
    A.acceptance X ∈ Set.Icc (0 : ℝ) 1 := by
  have hn := A.unitary.normalized_run (actual_oracle_unitary X) A.normalized
  refine ⟨measureProb_nonneg _ _, ?_⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A.event)
    (fun i _ _ => bornProb_nonneg (Run (TensorGate (BitOracleOn X) 1) A.word A.initial) i)
  exact hle.trans_eq (measureProb_univ hn)

/-- The experiment's acceptance function on the Boolean cube has degree at most twice its number
of oracle queries. -/
theorem QueryExperiment.actual_cube_degree {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) : CubeDegreeLE (2 * A.queries) A.acceptance :=
  Qatlib.Concepts.ProbabilityCore.Concentration.circuit_cube_degree n W
    A.word A.initial A.event

/-- The experiment computes the two-weight promise with error `error` when its acceptance
probability is within `error` of one on weight `lo` and within `error` of zero on weight
`hi`. -/
def QueryExperiment.ComputesPromise {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) (lo hi : ℕ) (error : ℝ) : Prop :=
  (∀ X, weight X = lo → |A.acceptance X - 1| ≤ error) ∧
    (∀ X, weight X = hi → |A.acceptance X| ≤ error)

/-- There is a real multivariate polynomial of total degree at most twice the query count that
agrees with the actual acceptance probability on every Boolean input. This is the
acceptance-polynomial property underlying Lemma 2.6 of [NayakWu1998]. -/
theorem QueryExperiment.actual_polynomial {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryExperiment n W) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 2 * A.queries ∧
      ∀ X, evalBool P X = A.acceptance X :=
  Qatlib.Concepts.ProbabilityCore.Concentration.actual_query_acceptance_polynomial
    A.word A.initial A.event

/-- There is a real multilinear polynomial of total degree at most twice the query count that
agrees with the actual acceptance probability on every Boolean input. This is the
multilinear acceptance-polynomial statement of Lemma 2.6 in [NayakWu1998]. -/
theorem QueryExperiment.actual_multilinear_polynomial {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (A : QueryExperiment n W) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 2 * A.queries ∧
      (∀ m : Fin n →₀ ℕ, P.coeff m ≠ 0 → ∀ i, m i ≤ 1) ∧
      ∀ X, evalBool P X = A.acceptance X := by
  obtain ⟨hdeg, hmulti, heval⟩ :=
    Qatlib.Concepts.QueryWordCore.QueryMachinery.acceptance_boolean_multilinearization_preserves_run
      A.word A.initial A.event
  exact ⟨Qatlib.Concepts.QueryWordCore.QueryMachinery.booleanAcceptancePolynomial
    A.word A.initial A.event, hdeg, hmulti, fun X => heval X⟩

/-- If an experiment computes the two-weight promise with nonnegative error, it yields a
polynomial satisfying `ApproximatesWithin` whose total degree is at most twice the query
count. -/
theorem QueryExperiment.actual_approximating_polynomial {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (A : QueryExperiment n W)
    (lo hi : ℕ) (error : ℝ) (he : 0 ≤ error) (hc : A.ComputesPromise lo hi error) :
    ∃ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ 2 * A.queries ∧
      ApproximatesWithin P lo hi error := by
  obtain ⟨P,hP,hactual⟩ := A.actual_polynomial
  refine ⟨P,hP,?_,?_,?_⟩
  · intro X
    rw [hactual]
    have hb := A.acceptance_range X
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  · intro X hX
    rw [hactual]
    exact hc.1 X hX
  · intro X hX
    rw [hactual]
    exact hc.2 X hX

end Qatlib.Papers.QMedianStats98.MainResults.Model
