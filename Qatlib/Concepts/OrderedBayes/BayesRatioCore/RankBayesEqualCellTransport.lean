/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellDefs

/-!
# Bayesian conditioning along comparison records

`pathWeight` multiplies a prior rank mass by its comparison-record likelihood, and `evidence`
sums these weights. `conditioned` normalizes them, while `sequential` repeatedly applies the
one-step update, providing equivalent record semantics for Bayesian ordered search
[BenOrHassidim2007].

The module proves this equivalence and transports posterior odds through one observation or a
whole record. `fixed_pair_mean` gives the answer-weighted ratio identity for ordered ranks `u ≤
k < i` when the denominator rank has positive prior mass.

## Main statements

* `evidence_positive`: every record has strictly positive evidence.
* `update_conditioned` and `sequential_conditioned`: sequential updates equal conditioning on
  the complete record.
* `step_odds` and `conditioned_odds`: likelihood-ratio formulas for posterior odds.
* `fixed_pair_mean`: the ordered fixed-pair ratio mean identity.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
/-- The unnormalized rank mass after a comparison record, given by prior mass times record
likelihood. -/
def pathWeight {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (m : Fin n) : ℝ :=
  a.mass m * recordLikelihood t m η.reliability

/-- The marginal likelihood of a comparison record, obtained by summing its unnormalized rank
weights. -/
def evidence {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) : ℝ := ∑ m, pathWeight a η t m

/-- Every unnormalized rank weight along a comparison record is nonnegative. -/
theorem path_nonneg {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (m : Fin n) :
    0 ≤ pathWeight a η t m :=
  mul_nonneg (a.nonneg m) (recordLikelihood_pos _ η.positive η.below_one t m).le

/-- Every finite comparison record has strictly positive evidence under a prior and noise
reliability strictly between zero and one. -/
theorem evidence_positive {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) :
    0 < evidence a η t :=
  sum_mul_pos_of_pos a.mass (fun m => recordLikelihood t m η.reliability) a.nonneg
    (fun m => recordLikelihood_pos _ η.positive η.below_one t m) a.has_positive

/-- The prior obtained by normalizing the path weights of a complete comparison record by its
evidence. -/
def conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) : Prior n where
  mass m := pathWeight a η t m / evidence a η t
  nonneg m := div_nonneg (path_nonneg a η t m) (evidence_positive a η t).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (evidence_positive a η t).ne'

/-- Conditioning on the empty comparison record leaves the prior unchanged. -/
theorem conditioned_nil {n : ℕ} (a : Prior n) (η : Noise) : conditioned a η [] = a := by
  apply Prior.ext
  funext m
  simp [conditioned,pathWeight,evidence,recordLikelihood,a.total]

/-- Appending one observation multiplies each path weight by that observation's answer
likelihood. -/
theorem path_snoc {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (c m : Fin n) (b : Bool) :
    pathWeight a η (t++[(c,b)]) m = pathWeight a η t m * answerLikelihood m c η.reliability b := by
  rw [pathWeight,recordLikelihood_append]
  simp only [pathWeight,recordLikelihood,List.foldr_cons,List.foldr_nil,mul_one]
  ring

/-- The predictive answer mass after conditioning on a record is the evidence of the extended
record divided by the original evidence. -/
theorem answer_conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (c : Fin n) (b : Bool) :
    answerMass (conditioned a η t) η c b = evidence a η (t++[(c,b)]) / evidence a η t := by
  simp only [answerMass,jointMass,conditioned,path_snoc,evidence]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

/-- Updating the prior conditioned on a record with one further observation equals conditioning
on the record with that observation appended. -/
theorem update_conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (c : Fin n) (b : Bool) :
    update (conditioned a η t) η c b = conditioned a η (t++[(c,b)]) := by
  apply Prior.ext
  funext m
  change (pathWeight a η t m / evidence a η t * answerLikelihood m c η.reliability b) /
    answerMass (conditioned a η t) η c b = pathWeight a η (t++[(c,b)]) m / evidence a η (t++[(c,b)])
  rw [answer_conditioned,path_snoc]
  field_simp [(evidence_positive a η t).ne',(evidence_positive a η (t++[(c,b)])).ne']

/-- The prior produced by applying the Bayesian update to each observation of a record in order. -/
def sequential {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) : Prior n :=
  t.foldl (fun w obs => update w η obs.1 obs.2) a

/-- Sequential Bayesian updates along a record equal conditioning the original prior on the
complete record. -/
theorem sequential_conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) :
    sequential a η t = conditioned a η t := by
  induction t using List.reverseRecOn with
  | nil => exact (conditioned_nil a η).symm
  | append_singleton t obs ih =>
      simp only [sequential,List.foldl_append,List.foldl_cons,List.foldl_nil] at ih ⊢
      rw [ih]
      exact update_conditioned a η t obs.1 obs.2

/-- When rank `k` has positive prior mass, the posterior odds of `i` against `k` equal the prior
odds multiplied by the answer likelihood of `i` divided by that of `k`. -/
theorem step_odds {n : ℕ} (a : Prior n) (η : Noise) (c k i : Fin n) (b : Bool)
    (hk : 0 < a.mass k) :
    (update a η c b).mass i / (update a η c b).mass k =
      (a.mass i / a.mass k) *
        (answerLikelihood i c η.reliability b / answerLikelihood k c η.reliability b) := by
  dsimp only [update,posterior,jointMass]
  have hL := (answerLikelihood_pos k c η.reliability b η.positive η.below_one).ne'
  field_simp [hk.ne',hL,(answer_positive a η c b).ne']

/-- For `u ≤ k < i` and positive prior mass at `k`, averaging the updated odds of `i` against
`k` with answer likelihoods under `u` gives the original odds. -/
theorem fixed_pair_mean {n : ℕ} (a : Prior n) (η : Noise) (u k i c : Fin n)
    (huk : u ≤ k) (hki : k < i) (hk : 0 < a.mass k) :
    (∑ b : Bool, answerLikelihood u c η.reliability b *
      ((update a η c b).mass i / (update a η c b).mass k)) = a.mass i / a.mass k := by
  simp_rw [step_odds a η c k i _ hk]
  simp_rw [show ∀ b : Bool, answerLikelihood u c η.reliability b *
      (a.mass i / a.mass k * (answerLikelihood i c η.reliability b /
        answerLikelihood k c η.reliability b)) = a.mass i / a.mass k *
        (answerLikelihood u c η.reliability b * (answerLikelihood i c η.reliability b /
          answerLikelihood k c η.reliability b)) from fun b => by ring]
  rw [← Finset.mul_sum]
  rw [three_cell_one_step_ratio_mean u k i c η.reliability η.positive η.below_one huk hki]
  ring

/-- For a rank `u` with positive prior mass, conditioning on a record multiplies the prior odds
of `v` against `u` by the record likelihood ratio. -/
theorem conditioned_odds {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (u v : Fin n)
    (hu : 0 < a.mass u) :
    (conditioned a η t).mass v / (conditioned a η t).mass u =
      (a.mass v/a.mass u) * recordRatio t u v η.reliability := by
  dsimp only [conditioned,pathWeight,recordRatio]
  have hL := (recordLikelihood_pos η.reliability η.positive η.below_one t u).ne'
  field_simp [hu.ne',hL,(evidence_positive a η t).ne']

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
