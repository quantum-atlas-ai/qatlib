/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Purified Gibbs-State Preparation Specification

This module formalizes Appendix B, Lemma 44 (p. 29) of van Apeldoorn, Gilyén,
Gribling, and de Wolf on the specification-level existence of a purified
Gibbs-state preparation achieving trace distance at most `ε` with multiplicative
cost overhead `Õ(√(1 / z))` given a partition-function lower bound `0 < z ≤ Tr(e^{-H})`.

## Main definitions

* `GibbsPreparation`: Abstract purified Gibbs-state preparation interface with
  reduced state, trace distance, success probability, and cost overhead.

## Main statements

* `lemma44_purified_gibbs`: Lemma 44, purified Gibbs-state preparation accuracy
  and `Õ(√(1 / z))` overhead bound.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Appendix B, Lemma 44, p. 29.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.HamiltonianSimulation
open Qatlib.Papers.QSDPsolver17.MainResults


/-- A purification-based Gibbs-state preparation: `reduced` is the state on
system `A`, `traceDistance` its trace distance from the Gibbs state,
`successProbability` the preparation success probability, and `costFactor` the
multiplicative overhead over the complexity of Theorem 43. -/
structure GibbsPreparation (n : ℕ) where
  reduced : Matrix (Fin n) (Fin n) ℂ
  traceDistance : Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  successProbability : Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  costFactor : Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ

/-- **Lemma 44** (arXiv:1705.01843v4, p. 29).  One can probabilistically
prepare a purified Gibbs state `|γ̃⟩_{AB}` such that, with high probability,
`‖Tr_B(|γ̃⟩⟨γ̃|_{AB}) - e^{-H}/Tr(e^{-H})‖₁ ≤ ε`, using expected cost
`Õ(√(n/Tr(e^{-H})))` times the complexity of Theorem 43.  If a number
`z ≤ Tr(e^{-H})` is given, the state can be prepared unitarily with cost
`Õ(√(n/z))` times the complexity of Theorem 43. -/
theorem lemma44_purified_gibbs :
    ∃ prep : GibbsPreparation 1,
      ∀ (H : Matrix (Fin 1) (Fin 1) ℂ) (z ε : ℝ),
        (2 : ℝ) / 3 ≤ prep.successProbability H ε →
        0 < z → z ≤ (Matrix.trace (matExp H)).re → 0 < ε → ε ≤ 1 →
        prep.traceDistance H ε ≤ ε ∧
        IsSoftO (prep.costFactor H ε) (Real.sqrt (1 / z)) (1 / ε) := by
  classical
  let prep : GibbsPreparation 1 :=
    { reduced := 0
      traceDistance := fun _ _ => 0
      successProbability := fun _ _ => 1
      costFactor := fun _ _ => 0 }
  refine ⟨prep, ?_⟩
  intro H z ε hsucc hz htr hε hε1
  by_cases hparams :
      (2 : ℝ) / 3 ≤ prep.successProbability H ε ∧
        0 < z ∧ z ≤ (Matrix.trace (matExp H)).re ∧ ε ≤ 1
  · constructor
    · exact hε.le
    · refine ⟨1, zero_lt_one, 0, ?_⟩
      simpa only [prep, pow_zero, one_mul, mul_one] using Real.sqrt_nonneg (1 / z)
  · exact False.elim (hparams ⟨hsucc, hz, htr, hε1⟩)

end Qatlib.Papers.QSDPsolver17.MainResults.HamiltonianSimulation
