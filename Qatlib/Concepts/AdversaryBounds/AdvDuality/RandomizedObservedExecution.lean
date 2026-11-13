/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Randomized observed circuits as quantum instruments

`randomizedObservedLeaf` weights each leaf operator by the square root of its circuit-selection
probability. For a unitary oracle and well-formed circuits, these operators satisfy Kraus
completeness and define `randomizedObservedInstrument`. This uses the instrument formalism
developed in [Watrous2018].

The branch maps and branch probabilities scale by the selection probabilities, and their
query-weighted sum is the corresponding mixture of expected query counts.

## Main statements

* `randomizedObservedLeaf_complete`: The weighted leaf operators satisfy Kraus completeness.
* `randomized_observed_branch_law`: Branch maps and probabilities scale by the seed probability.
* `randomized_observed_expected_cost`: Expected query cost is the weighted sum over selected
  circuits.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix

variable {J : Type} [Fintype J] {D : ℕ}

/-- The leaf operator for circuit `P ji.1`, scaled by the square root of its selection
probability under `d`. -/
noncomputable def randomizedObservedLeaf (d : FinDist J) (O : Operator D)
    (P : J → ObservedCircuit (Fin D)) (ji : Σ j, Fin (observedLeafCount (P j))) :
    Operator D :=
  ((Real.sqrt (d.prob ji.1) : ℂ) • (observedLeaf O (P ji.1) ji.2).operator)

/-- For a unitary oracle and well-formed component circuits, the randomized leaf operators
satisfy the Kraus completeness identity. -/
theorem randomizedObservedLeaf_complete (d : FinDist J) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : J → ObservedCircuit (Fin D))
    (hP : ∀ j, observedWellFormed (P j)) :
    ∑ ji : Σ j, Fin (observedLeafCount (P j)),
      (randomizedObservedLeaf d O P ji).conjTranspose * randomizedObservedLeaf d O P ji = 1 := by
  have key : ∀ ji : Σ j, Fin (observedLeafCount (P j)),
      (randomizedObservedLeaf d O P ji).conjTranspose * randomizedObservedLeaf d O P ji
      = (d.prob ji.1 : ℂ) •
        ((observedLeaf O (P ji.1) ji.2).operator.conjTranspose *
          (observedLeaf O (P ji.1) ji.2).operator) := by
    intro ji
    rw [randomizedObservedLeaf, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    congr 1
    rw [show star ((Real.sqrt (d.prob ji.1) : ℂ)) = ((Real.sqrt (d.prob ji.1) : ℂ)) from
        Complex.conj_ofReal _,
      show ((Real.sqrt (d.prob ji.1) : ℂ)) * ((Real.sqrt (d.prob ji.1) : ℂ))
        = ((Real.sqrt (d.prob ji.1) * Real.sqrt (d.prob ji.1) : ℝ) : ℂ) from
        (Complex.ofReal_mul _ _).symm,
      Real.mul_self_sqrt (d.nonneg ji.1)]
  calc ∑ ji : Σ j, Fin (observedLeafCount (P j)),
        (randomizedObservedLeaf d O P ji).conjTranspose * randomizedObservedLeaf d O P ji
      = ∑ j, ∑ i : Fin (observedLeafCount (P j)),
          (d.prob j : ℂ) •
            ((observedLeaf O (P j) i).operator.conjTranspose *
              (observedLeaf O (P j) i).operator) := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => key ⟨j, i⟩
    _ = ∑ j, (d.prob j : ℂ) •
          ∑ i : Fin (observedLeafCount (P j)),
            (observedLeaf O (P j) i).operator.conjTranspose *
              (observedLeaf O (P j) i).operator := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.smul_sum]
    _ = ∑ j, (d.prob j : ℂ) • (1 : Operator D) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [observedLeaf_complete O hO (P j) (hP j)]
    _ = ((∑ j, d.prob j : ℝ) : ℂ) • (1 : Operator D) := by
        rw [← Finset.sum_smul,
          show (∑ j, ((d.prob j : ℝ) : ℂ)) = ((∑ j, d.prob j : ℝ) : ℂ) from
            (Complex.ofReal_sum Finset.univ (fun j => d.prob j)).symm]
    _ = 1 := by
        rw [show (∑ j, d.prob j : ℝ) = 1 from d.sum_one]
        simp


/-- The quantum instrument whose outcomes pair a selected circuit with one of its leaves and
whose Kraus operators are `randomizedObservedLeaf`. -/
noncomputable def randomizedObservedInstrument {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (d : FinDist J) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : J → ObservedCircuit (Fin D))
    (hP : ∀ j, observedWellFormed (P j)) :
    Instrument (Σ j, Fin (observedLeafCount (P j))) D D :=
  Instrument.ofKraus (randomizedObservedLeaf d O P)
    (randomizedObservedLeaf_complete d O hO P hP)


/-- Each randomized branch map equals its component branch map scaled by `d.prob j`, and its
branch probability is scaled by the same real factor. -/
theorem randomized_observed_branch_law {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : J → ObservedCircuit (Fin D))
    (hP : ∀ j, observedWellFormed (P j)) (ρ : Operator D) (j : J)
    (i : Fin (observedLeafCount (P j))) :
    (randomizedObservedInstrument d O hO P hP).branch ⟨j, i⟩ ρ
      = (d.prob j : ℂ) • (observedInstrument O hO (P j) (hP j)).branch i ρ ∧
      instrumentProb (randomizedObservedInstrument d O hO P hP) ρ ⟨j, i⟩
        = d.prob j * instrumentProb (observedInstrument O hO (P j) (hP j)) ρ i := by
  have hL : (randomizedObservedInstrument d O hO P hP).branch ⟨j, i⟩ ρ
      = randomizedObservedLeaf d O P ⟨j, i⟩ * ρ
        * (randomizedObservedLeaf d O P ⟨j, i⟩).conjTranspose :=
    Instrument.ofKraus_branch _ _ _ ρ
  have hR : (observedInstrument O hO (P j) (hP j)).branch i ρ
      = (observedLeaf O (P j) i).operator * ρ * (observedLeaf O (P j) i).operator.conjTranspose :=
    Instrument.ofKraus_branch _ _ _ ρ
  have hbranch : (randomizedObservedInstrument d O hO P hP).branch ⟨j, i⟩ ρ
      = (d.prob j : ℂ) • (observedInstrument O hO (P j) (hP j)).branch i ρ := by
    rw [hL, hR, randomizedObservedLeaf, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    rw [show star ((Real.sqrt (d.prob j) : ℂ)) = ((Real.sqrt (d.prob j) : ℂ)) from
        Complex.conj_ofReal _,
      show ((Real.sqrt (d.prob j) : ℂ)) * ((Real.sqrt (d.prob j) : ℂ))
        = ((Real.sqrt (d.prob j) * Real.sqrt (d.prob j) : ℝ) : ℂ) from
        (Complex.ofReal_mul _ _).symm,
      Real.mul_self_sqrt (d.nonneg j)]
  refine ⟨hbranch, ?_⟩
  rw [instrumentProb, hbranch, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  rfl


/-- The query-weighted branch sum of the randomized instrument equals the `d`-weighted sum of
the component mixed-state expected query counts. -/
theorem randomized_observed_expected_cost {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d : FinDist J) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (P : J → ObservedCircuit (Fin D))
    (hP : ∀ j, observedWellFormed (P j)) (ρ : Operator D) :
    (∑ ji : Σ j, Fin (observedLeafCount (P j)),
      instrumentProb (randomizedObservedInstrument d O hO P hP) ρ ji
        * (observedLeaf O (P ji.1) ji.2).queries)
      = ∑ j, d.prob j * mixedExpectedQueries O (P j) ρ := by
  have hexp :
    (∑ ji : Σ j, Fin (observedLeafCount (P j)),
      instrumentProb (randomizedObservedInstrument d O hO P hP) ρ ji
        * (observedLeaf O (P ji.1) ji.2).queries)
    = ∑ j, ∑ i : Fin (observedLeafCount (P j)),
        instrumentProb (randomizedObservedInstrument d O hO P hP) ρ ⟨j, i⟩
          * (observedLeaf O (P j) i).queries :=
    Fintype.sum_sigma (fun ji =>
      instrumentProb (randomizedObservedInstrument d O hO P hP) ρ ji
        * (observedLeaf O (P ji.1) ji.2).queries)
  rw [hexp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mixedExpectedQueries_eq_instrumentProb O hO (P j) (hP j) ρ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(randomized_observed_branch_law d O hO P hP ρ j i).2]
  ring

end Qatlib.Concepts.AdversaryBounds.AdvDuality
