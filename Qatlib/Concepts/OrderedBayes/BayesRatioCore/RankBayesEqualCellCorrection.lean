/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellAdaptive
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellSourceRank

/-!
# Conditional probabilities at the equal rank cell

This module assembles the probability-law interpretation of the corrected Bayesian rank update
used for ordered search [BenOrHassidim2007]. `equal_cell_conditional` gives the true-answer
conditional mass at the cut rank, with numerator `a.mass c * η.reliability` and the true-answer
normalization.

`frontier1` packages generation and normalization of the one-step joint law, positivity of
answer probabilities, the corrected conditional update, adaptive transcript conditioning, and
the ordered fixed-pair ratio mean identity.

## Main statements

* `equal_cell_conditional`: the conditional mass of the rank equal to the comparison cut.
* `frontier1`: the combined one-step, adaptive, and fixed-pair probability identities.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

noncomputable section

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellCorrection

open scoped BigOperators
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
open Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- At the rank equal to the cut, conditioning on a true answer gives prior mass times
reliability divided by the true-answer normalization. -/
theorem equal_cell_conditional {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) :
    (joint a η c (c,true)).toReal / answerMass a η c true =
      a.mass c * η.reliability / bayesTrueNorm a.mass c η.reliability := by
  simp only [joint_apply,jointMass,answerMass,answerLikelihood,
    bayesTrueLikelihood,le_refl,↓reduceIte,bayesTrueNorm]

/-- Collects the generated and normalized one-step joint law, positive answer masses, corrected
conditional probabilities, and adaptive transcript conditioning. It also includes the
answer-weighted fixed-pair posterior-odds identity for `u ≤ k < i` with positive mass at
`k`. -/
theorem frontier1 {n : ℕ} (a : Prior n) (η : Noise) :
    (∀ c : Fin n, joint a η c = (priorPMF a).bind
        (fun m => (answerPMF η m c).map (fun b => (m,b))) ∧
      (∑ z : Fin n × Bool, joint a η c z) = 1 ∧
      ∀ (b : Bool) (m : Fin n), 0 < answerMass a η c b ∧
        (joint a η c (m,b)).toReal / answerMass a η c b =
          correctPost a.mass c η.reliability b m) ∧
    (∀ (k : ℕ) (prog : BscProgram n k) (y : Fin k → Bool) (m : Fin n),
      (transcriptJoint a η prog (m,y)).toReal /
        (∑ j, (transcriptJoint a η prog (j,y)).toReal) =
        (sequential a η (actualRecord prog y)).mass m) ∧
    (∀ (u k i c : Fin n), u ≤ k → k < i → 0 < a.mass k →
      (∑ b : Bool, answerLikelihood u c η.reliability b *
        ((update a η c b).mass i / (update a η c b).mass k)) = a.mass i / a.mass k) := by
  refine ⟨?_,fun k prog y m => adaptive_conditional a η prog y m,?_⟩
  · intro c
    refine ⟨joint_generated a η c,?_,?_⟩
    · simp only [joint,PMF.ofFintype_apply,← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => joint_nonneg a η c z),joint_total,ENNReal.ofReal_one]
    · intro b m
      refine ⟨answer_positive a η c b,?_⟩
      rw [joint_apply]
      exact posterior_correctPost a η c m b
  · intro u k i c huk hki hk
    exact fixed_pair_mean a η u k i c huk hki hk

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellCorrection
