/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellDefs
set_option warningAsError false

noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
def pathWeight {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (m : Fin n) : ℝ :=
  a.mass m * recordLikelihood t m η.reliability

def evidence {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) : ℝ := ∑ m, pathWeight a η t m

theorem path_nonneg {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (m : Fin n) :
    0 ≤ pathWeight a η t m :=
  mul_nonneg (a.nonneg m) (recordLikelihood_pos _ η.positive η.below_one t m).le

theorem evidence_positive {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) :
    0 < evidence a η t :=
  sum_mul_pos_of_pos a.mass (fun m => recordLikelihood t m η.reliability) a.nonneg
    (fun m => recordLikelihood_pos _ η.positive η.below_one t m) a.has_positive

def conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) : Prior n where
  mass m := pathWeight a η t m / evidence a η t
  nonneg m := div_nonneg (path_nonneg a η t m) (evidence_positive a η t).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (evidence_positive a η t).ne'

theorem conditioned_nil {n : ℕ} (a : Prior n) (η : Noise) : conditioned a η [] = a := by
  apply Prior.ext
  funext m
  simp [conditioned,pathWeight,evidence,recordLikelihood,a.total]

theorem path_snoc {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (c m : Fin n) (b : Bool) :
    pathWeight a η (t++[(c,b)]) m = pathWeight a η t m * answerLikelihood m c η.reliability b := by
  rw [pathWeight,recordLikelihood_append]
  simp only [pathWeight,recordLikelihood,List.foldr_cons,List.foldr_nil,mul_one]
  ring

theorem answer_conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (c : Fin n) (b : Bool) :
    answerMass (conditioned a η t) η c b = evidence a η (t++[(c,b)]) / evidence a η t := by
  simp only [answerMass,jointMass,conditioned,path_snoc,evidence]
  simp_rw [div_mul_eq_mul_div]
  rw [Finset.sum_div]

theorem update_conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (c : Fin n) (b : Bool) :
    update (conditioned a η t) η c b = conditioned a η (t++[(c,b)]) := by
  apply Prior.ext
  funext m
  change (pathWeight a η t m / evidence a η t * answerLikelihood m c η.reliability b) /
    answerMass (conditioned a η t) η c b = pathWeight a η (t++[(c,b)]) m / evidence a η (t++[(c,b)])
  rw [answer_conditioned,path_snoc]
  field_simp [(evidence_positive a η t).ne',(evidence_positive a η (t++[(c,b)])).ne']

def sequential {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) : Prior n :=
  t.foldl (fun w obs => update w η obs.1 obs.2) a

theorem sequential_conditioned {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) :
    sequential a η t = conditioned a η t := by
  induction t using List.reverseRecOn with
  | nil => exact (conditioned_nil a η).symm
  | append_singleton t obs ih =>
      simp only [sequential,List.foldl_append,List.foldl_cons,List.foldl_nil] at ih ⊢
      rw [ih]
      exact update_conditioned a η t obs.1 obs.2

theorem step_odds {n : ℕ} (a : Prior n) (η : Noise) (c k i : Fin n) (b : Bool)
    (hk : 0 < a.mass k) :
    (update a η c b).mass i / (update a η c b).mass k =
      (a.mass i / a.mass k) *
        (answerLikelihood i c η.reliability b / answerLikelihood k c η.reliability b) := by
  dsimp only [update,posterior,jointMass]
  have hL := (answerLikelihood_pos k c η.reliability b η.positive η.below_one).ne'
  field_simp [hk.ne',hL,(answer_positive a η c b).ne']

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

theorem conditioned_odds {n : ℕ} (a : Prior n) (η : Noise) (t : Record n) (u v : Fin n)
    (hu : 0 < a.mass u) :
    (conditioned a η t).mass v / (conditioned a η t).mass u =
      (a.mass v/a.mass u) * recordRatio t u v η.reliability := by
  dsimp only [conditioned,pathWeight,recordRatio]
  have hL := (recordLikelihood_pos η.reliability η.positive η.below_one t u).ne'
  field_simp [hu.ne',hL,(evidence_positive a η t).ne']

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
