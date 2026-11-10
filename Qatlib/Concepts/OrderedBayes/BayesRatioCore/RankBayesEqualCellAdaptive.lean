/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellTransport
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearchRefined
import Mathlib.Algebra.BigOperators.Fin
set_option warningAsError false

noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
open Qatlib.Concepts.OrderedBayes.BayesRatioCore

def actualRecord {n k : ℕ} (prog : BscProgram n k) (y : Fin k → Bool) : Record n :=
  List.ofFn (fun i => (prog.cuts i (answerPrefix y i),y i))

theorem answer_bsc {n : ℕ} (m c : Fin n) (p : ℝ) (b : Bool) :
    answerLikelihood m c p b = bscProb p (truthBit m c) b := by
  cases b <;> by_cases h : c.val ≤ m.val <;>
    simp [answerLikelihood,bayesTrueLikelihood,bayesFalseLikelihood,bscProb,truthBit,h]

theorem record_product {n : ℕ} (η : Noise) (m : Fin n) (t : Record n) :
    recordLikelihood t m η.reliability =
      (t.map (fun obs => answerLikelihood m obs.1 η.reliability obs.2)).prod := by
  induction t with
  | nil => rfl
  | cons obs t ih =>
      change answerLikelihood m obs.1 η.reliability obs.2 * recordLikelihood t m η.reliability = _
      rw [List.map_cons,List.prod_cons,ih]

theorem actual_likelihood {n k : ℕ} (prog : BscProgram n k) (η : Noise)
    (m : Fin n) (y : Fin k → Bool) :
    recordLikelihood (actualRecord prog y) m η.reliability = bscLik prog η.reliability m y := by
  rw [record_product]
  simp only [actualRecord,List.map_ofFn,List.prod_ofFn,bscLik]
  apply Finset.prod_congr rfl
  intro i _
  exact answer_bsc _ _ _ _

def transcriptMass {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k)
    (z : Fin n × (Fin k → Bool)) : ℝ := a.mass z.1 * bscLik prog η.reliability z.1 z.2

theorem transcript_nonneg {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k)
    (z : Fin n × (Fin k → Bool)) : 0 ≤ transcriptMass a η prog z :=
  mul_nonneg (a.nonneg _) (bscLik_nonneg prog η.reliability η.positive.le η.below_one.le _ _)

theorem transcript_total {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k) :
    (∑ z : Fin n × (Fin k → Bool), transcriptMass a η prog z) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [transcriptMass,← Finset.mul_sum,← bscLikPre_eq_bscLik,bscLikPre_sum_one,mul_one]
  exact a.total

def transcriptJoint {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k) :
    PMF (Fin n × (Fin k → Bool)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (transcriptMass a η prog z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => transcript_nonneg a η prog z),transcript_total]
    simp)

@[simp] theorem transcriptJoint_apply {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k)
    (z : Fin n × (Fin k → Bool)) : (transcriptJoint a η prog z).toReal = transcriptMass a η prog z :=
  ENNReal.toReal_ofReal (transcript_nonneg a η prog z)

theorem transcript_evidence {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k)
    (y : Fin k → Bool) :
    (∑ m, (transcriptJoint a η prog (m,y)).toReal) = evidence a η (actualRecord prog y) := by
  simp only [transcriptJoint_apply,transcriptMass,evidence,pathWeight,actual_likelihood]

theorem adaptive_conditional {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k)
    (y : Fin k → Bool) (m : Fin n) :
    (transcriptJoint a η prog (m,y)).toReal /
      (∑ j, (transcriptJoint a η prog (j,y)).toReal) =
      (sequential a η (actualRecord prog y)).mass m := by
  rw [transcriptJoint_apply,transcript_evidence,sequential_conditioned]
  simp only [transcriptMass,conditioned,pathWeight,actual_likelihood]

theorem adaptive_support_positive {n k : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n k)
    (y : Fin k → Bool) (m : Fin n) (hm : 0 < a.mass m) :
    0 < (sequential a η (actualRecord prog y)).mass m := by
  rw [sequential_conditioned]
  exact div_pos (mul_pos hm (recordLikelihood_pos _ η.positive η.below_one _ m))
    (evidence_positive a η _)

theorem adaptive_fixed_pair {n steps : ℕ} (a : Prior n) (η : Noise) (prog : BscProgram n steps)
    (y : Fin steps → Bool) (u k i c : Fin n) (huk : u ≤ k) (hki : k < i)
    (hk : 0 < a.mass k) :
    let w := sequential a η (actualRecord prog y)
    (∑ b : Bool, answerLikelihood u c η.reliability b *
      ((update w η c b).mass i / (update w η c b).mass k)) = w.mass i / w.mass k := by
  exact fixed_pair_mean _ η u k i c huk hki (adaptive_support_positive a η prog y k hk)

def prefixProgram {n k : ℕ} (prog : BscProgram n (k+1)) : BscProgram n k where
  cuts i h := prog.cuts i.castSucc h
  guess y := prog.guess (tExt y false)

theorem transcript_split {n k : ℕ} (a : Prior n) (η : Noise)
    (prog : BscProgram n (k+1)) (m : Fin n) (y : Fin k → Bool) (b : Bool) :
    transcriptMass a η prog (m,tExt y b)=
      transcriptMass a η (prefixProgram prog) (m,y) *
        answerLikelihood m (prog.cuts (Fin.last k) y) η.reliability b := by
  simp only [transcriptMass,← bscLikPre_eq_bscLik]
  rw [bscLikPre_split]
  change a.mass m *
      (bscLikPre (prefixProgram prog).cuts η.reliability m y *
        bscProb η.reliability (truthBit m (prog.cuts (Fin.last k) y)) b) =
    (a.mass m*bscLikPre (prefixProgram prog).cuts η.reliability m y)*
      answerLikelihood m (prog.cuts (Fin.last k) y) η.reliability b
  rw [answer_bsc]
  ring

theorem transcriptJoint_split {n k : ℕ} (a : Prior n) (η : Noise)
    (prog : BscProgram n (k+1)) (m : Fin n) (y : Fin k → Bool) (b : Bool) :
    (transcriptJoint a η prog (m,tExt y b)).toReal =
      (transcriptJoint a η (prefixProgram prog) (m,y)).toReal *
        (answerPMF η m (prog.cuts (Fin.last k) y) b).toReal := by
  rw [transcriptJoint_apply,transcriptJoint_apply,answerPMF_apply,
    ENNReal.toReal_ofReal
      (answerLikelihood_pos m (prog.cuts (Fin.last k) y) η.reliability b
        η.positive η.below_one).le]
  exact transcript_split a η prog m y b

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
