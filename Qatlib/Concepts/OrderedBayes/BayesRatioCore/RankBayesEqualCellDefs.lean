/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Probability laws for Bayesian rank updates

`Prior` packages a normalized nonnegative mass function on finitely many ranks, and `Noise`
packages a comparison reliability strictly between zero and one. `jointMass`, `answerMass`,
`joint`, and `posterior` describe a rank together with one noisy threshold answer, forming a
finite probability model for Bayesian ordered search [BenOrHassidim2007].

`update` turns the conditional mass into a new prior. The module verifies the corrected
posterior formula, normalization, preservation of support, disintegration, and the
representation of the joint law by sampling a prior rank followed by its answer.

## Main statements

* `posterior_correctPost`: agreement with the corrected posterior formula.
* `conditional_joint`: the conditional joint mass is the updated prior mass.
* `posterior_mean` and `posterior_support`: mean preservation and exact preservation of zero
  masses.
* `joint_generated`: construction of the joint law by prior sampling and an answer channel.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators ENNReal
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
/-- A real mass function on finitely many ranks with nonnegative entries summing to one. -/
structure Prior (n : ℕ) where
  mass : Fin n → ℝ
  nonneg : ∀ m, 0 ≤ mass m
  total : ∑ m, mass m = 1

/-- Two priors are equal whenever their mass functions are equal. -/
@[ext] theorem Prior.ext {n : ℕ} {a b : Prior n} (h : a.mass = b.mass) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Every prior assigns strictly positive mass to at least one rank. -/
theorem Prior.has_positive {n : ℕ} (a : Prior n) : ∃ m, 0 < a.mass m := by
  by_contra h
  have hz : ∑ m, a.mass m = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    exact le_antisymm (not_lt.mp (not_exists.mp h m)) (a.nonneg m)
  linarith [a.total]

/-- A comparison reliability parameter strictly between zero and one. -/
structure Noise where
  reliability : ℝ
  positive : 0 < reliability
  below_one : reliability < 1

/-- The joint real mass of a rank and one comparison answer, obtained by multiplying the prior
mass by the answer likelihood. -/
def jointMass {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (z : Fin n × Bool) : ℝ :=
  a.mass z.1 * answerLikelihood z.1 c η.reliability z.2

/-- The marginal probability of a comparison answer, obtained by summing the joint real mass
over all ranks. -/
def answerMass {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (b : Bool) : ℝ :=
  ∑ m, jointMass a η c (m,b)

/-- Every joint rank-answer mass is nonnegative. -/
theorem joint_nonneg {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (z : Fin n × Bool) :
    0 ≤ jointMass a η c z :=
  mul_nonneg (a.nonneg z.1)
    (answerLikelihood_pos z.1 c η.reliability z.2 η.positive η.below_one).le

/-- Summing the joint mass over both answers recovers the prior mass of the fixed rank. -/
theorem rank_marginal {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) :
    (∑ b : Bool, jointMass a η c (m,b)) = a.mass m := by
  simp only [jointMass,Fintype.sum_bool,← mul_add,answerLikelihood_sum,mul_one]

/-- The joint masses of all rank-answer pairs sum to one. -/
theorem joint_total {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) :
    (∑ z : Fin n × Bool, jointMass a η c z) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [rank_marginal]
  exact a.total

/-- The marginal masses of the two comparison answers sum to one. -/
theorem answer_total {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) :
    (∑ b : Bool, answerMass a η c b) = 1 := by
  unfold answerMass
  rw [Finset.sum_comm]
  simp_rw [rank_marginal]
  exact a.total

/-- Both comparison answers have strictly positive marginal probability for every prior and
noise parameter. -/
theorem answer_positive {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (b : Bool) :
    0 < answerMass a η c b := by
  have hp := bayes_answer_probabilities a.mass c η.reliability a.nonneg a.total
    η.positive η.below_one
  cases b with
  | false => exact hp.1
  | true => exact hp.2.1

/-- The probability mass function of a prior rank paired with its noisy comparison answer. -/
def joint {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) : PMF (Fin n × Bool) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (jointMass a η c z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => joint_nonneg a η c z),joint_total]
    simp)

/-- Converting a joint probability mass to a real number recovers its defining `jointMass`. -/
@[simp] theorem joint_apply {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (z : Fin n × Bool) :
    (joint a η c z).toReal = jointMass a η c z :=
  ENNReal.toReal_ofReal (joint_nonneg a η c z)

/-- The conditional rank mass after observing an answer, defined as joint mass divided by the
answer marginal. -/
def posterior {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (b : Bool) : Fin n → ℝ :=
  fun m => jointMass a η c (m,b) / answerMass a η c b

/-- The conditional rank mass agrees with the corrected Bayesian posterior `correctPost`. -/
theorem posterior_correctPost {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) (b : Bool) :
    posterior a η c b m = correctPost a.mass c η.reliability b m := by
  rw [correctPost_eq]
  rfl

/-- Every conditional rank mass is nonnegative. -/
theorem posterior_nonneg {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) (b : Bool) :
    0 ≤ posterior a η c b m :=
  div_nonneg (joint_nonneg a η c (m,b)) (answer_positive a η c b).le

/-- The conditional rank masses sum to one for either observed answer. -/
theorem posterior_total {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (b : Bool) :
    (∑ m, posterior a η c b m) = 1 := by
  simp only [posterior,← Finset.sum_div]
  exact div_self (answer_positive a η c b).ne'

/-- The prior obtained by conditioning on one noisy comparison answer. -/
def update {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) (b : Bool) : Prior n :=
  ⟨posterior a η c b,fun m => posterior_nonneg a η c m b,posterior_total a η c b⟩

/-- Dividing the joint probability of a rank-answer pair by the answer marginal gives the
updated prior mass of that rank. -/
theorem conditional_joint {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) (b : Bool) :
    (joint a η c (m,b)).toReal / (∑ j, (joint a η c (j,b)).toReal) =
      (update a η c b).mass m := by
  simp only [joint_apply,update,posterior,answerMass]

/-- The answer marginal multiplied by the corresponding posterior rank mass equals the joint
rank-answer mass. -/
theorem disintegration {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) (b : Bool) :
    answerMass a η c b * (update a η c b).mass m = jointMass a η c (m,b) := by
  dsimp only [update,posterior]
  field_simp [(answer_positive a η c b).ne']

/-- Averaging the updated mass of a fixed rank over the answer distribution recovers its prior
mass. -/
theorem posterior_mean {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) :
    (∑ b : Bool, answerMass a η c b * (update a η c b).mass m) = a.mass m := by
  simp_rw [disintegration]
  exact rank_marginal a η c m

/-- A rank has zero updated mass exactly when it has zero prior mass. -/
theorem posterior_support {n : ℕ} (a : Prior n) (η : Noise) (c m : Fin n) (b : Bool) :
    (update a η c b).mass m = 0 ↔ a.mass m = 0 := by
  have h := (answerLikelihood_pos m c η.reliability b η.positive η.below_one).ne'
  simp [update,posterior,jointMass,div_eq_zero_iff,mul_eq_zero,h,(answer_positive a η c b).ne']

/-- The probability mass function associated with the real masses of a `Prior`. -/
def priorPMF {n : ℕ} (a : Prior n) : PMF (Fin n) :=
  PMF.ofFintype (fun m => ENNReal.ofReal (a.mass m)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => a.nonneg m),a.total]
    simp)

/-- The Bernoulli probability mass function of the noisy threshold answer for a fixed rank and
cut. -/
def answerPMF {n : ℕ} (η : Noise) (m c : Fin n) : PMF Bool :=
  PMF.bernoulli (truthAnswerProb m c η.reliability) (clampProb_le _)

/-- The answer-channel probability equals the nonnegative extended-real embedding of the answer
likelihood. -/
theorem answerPMF_apply {n : ℕ} (η : Noise) (m c : Fin n) (b : Bool) :
    answerPMF η m c b=ENNReal.ofReal (answerLikelihood m c η.reliability b) := by
  have hθ : (truthAnswerProb m c η.reliability:ℝ)=bayesTrueLikelihood c m η.reliability :=
    zoo_bayes_truth_answer_prob m c η.reliability η.positive.le η.below_one.le
  cases b with
  | true =>
    simp only [answerPMF,PMF.bernoulli_apply,Bool.cond_true]
    calc
      (truthAnswerProb m c η.reliability:ℝ≥0∞)=
          ENNReal.ofReal (truthAnswerProb m c η.reliability:ℝ) :=
        ENNReal.ofReal_coe_nnreal.symm
      _=ENNReal.ofReal (answerLikelihood m c η.reliability true) := by
        rw [hθ]
        rfl
  | false =>
    simp only [answerPMF,PMF.bernoulli_apply,Bool.cond_false]
    have hfalse : 1-(truthAnswerProb m c η.reliability:ℝ)=
        answerLikelihood m c η.reliability false := by
      rw [hθ]
      by_cases h : c.val ≤ m.val
      · simp [answerLikelihood,bayesTrueLikelihood,bayesFalseLikelihood,h]
      · simp [answerLikelihood,bayesTrueLikelihood,bayesFalseLikelihood,h]
    calc
      (1:ℝ≥0∞)-(truthAnswerProb m c η.reliability:ℝ≥0∞)=
          ENNReal.ofReal (1-(truthAnswerProb m c η.reliability:ℝ)) := by
        rw [ENNReal.ofReal_sub 1 (NNReal.coe_nonneg _),ENNReal.ofReal_one,
          ENNReal.ofReal_coe_nnreal]
      _=ENNReal.ofReal (answerLikelihood m c η.reliability false) := congrArg _ hfalse

/-- Pairing an answer-channel sample with a fixed rank gives its answer probability at that rank
and zero at every other rank. -/
theorem answerPair_apply {n : ℕ} (η : Noise) (r c m : Fin n) (b : Bool) :
    ((answerPMF η r c).map (fun d => (r,d))) (m,b)=
      if r=m then answerPMF η m c b else 0 := by
  by_cases h : r=m
  · subst r
    simp [PMF.map_apply,tsum_fintype,Prod.mk.injEq]
  · simp [PMF.map_apply,tsum_fintype,Prod.mk.injEq,h,Ne.symm h]

/-- The joint law is generated by sampling a rank from the prior and then sampling its
comparison answer while retaining the rank. -/
theorem joint_generated {n : ℕ} (a : Prior n) (η : Noise) (c : Fin n) :
    joint a η c = (priorPMF a).bind
      (fun m => (answerPMF η m c).map (fun b => (m,b))) := by
  symm
  apply PMF.ext
  intro z
  rcases z with ⟨m,b⟩
  rw [PMF.bind_apply,tsum_fintype]
  simp only [priorPMF,PMF.ofFintype_apply,answerPair_apply,mul_ite,mul_zero,
    joint,PMF.ofFintype_apply]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [answerPMF_apply,← ENNReal.ofReal_mul (a.nonneg m)]
  rfl

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
