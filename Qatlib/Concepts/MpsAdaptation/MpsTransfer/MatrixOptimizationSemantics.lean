/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationReceipt

/-!
# Operational semantics of weighted program mixtures

This module identifies receipt probabilities and costs with pure-state evaluations of the
corresponding hybrid programs. `Family.continuation` connects selector configurations to the
selected program or a timeout return.

`Family.cappedProgram_receipt` proves agreement of successful output probabilities, while
`Family.cappedProgram_counts` expands count-sensitive evaluation over coin paths. The pure-state
and instrument semantics follow the quantum-computation setting of [NielsenChuang2010].

## Main statements

* `coin_paths_expectation`: Finite coin-path sums agree with expectations under the induced law.
* `Family.output_pure_eval`: Leaf output probabilities agree with pure-state program evaluation.
* `Family.cappedProgram_receipt`: The capped hybrid program has the successful output
  probabilities specified by receipts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Family

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Qatlib
open scoped ENNReal Classical

/-- The weighted sum of a nonnegative function over coin paths equals its expectation under the
induced outcome-and-length law, converted to a real number. -/
theorem coin_paths_expectation {A : Type} (p : CoinCode A) (g : A × ℕ → ℝ)
    (hg : ∀ z, 0 ≤ g z) :
    (p.paths.map (fun z => CoinCode.wordWeight z.2 * g (z.1,z.2.length))).sum =
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p.law (fun z => ENNReal.ofReal (g z))).toReal := by
  have he := congrArg ENNReal.toReal (p.paths_real_expectation g hg)
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (CoinCode.wordWeight_nonneg _) (hg _)))] at he
  rw [← he]
  have hlist : p.paths.map (fun z => CoinCode.wordWeight z.2 * g (z.1,z.2.length)) =
      List.ofFn (fun i => CoinCode.wordWeight (p.paths.get i).2 *
        g ((p.paths.get i).1,(p.paths.get i).2.length)) := by
    have h := congrArg (List.map (fun z : A × List Bool =>
      CoinCode.wordWeight z.2 * g (z.1,z.2.length))) (List.ofFn_get p.paths)
    simpa only [List.map_ofFn, Function.comp_def] using h.symm
  rw [hlist, List.sum_ofFn]

/-- The probability of the equality event at a point equals the probability mass at that point. -/
theorem pmf_event_value {A : Type} (p : PMF A) (i : A) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun j => j = i) = p i := by
  classical
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq i p

namespace Family

variable {K D m : ℕ}

/-- For a pure input density operator, a family member's output mass equals its
branch-mass-weighted pure-state evaluation. -/
theorem output_pure_eval (F : Family K D m) (ψ : QState (Fin D))
    (hstate : F.state = outerProduct ψ) (u : Fin K) (i : Fin m) :
    (F.output u i).toReal =
      (F.program u).eval F.oracle ψ (fun j φ => branchMass φ * if j = i then 1 else 0) := by
  classical
  unfold output
  rw [map_apply_event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype]
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
    ((F.leaves u).apply_ne_top j) (by split_ifs <;> simp))]
  simp only [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_one,
    ENNReal.toReal_zero, leaves, instrumentPMF_apply,
    ENNReal.toReal_ofReal (instrumentProb_nonneg _ F.density.1 _)]
  rw [hstate]
  exact (F.program u).eval_instrument F.oracle F.oracle_unitary (F.legal u) ψ
    (fun j => if j = i then 1 else 0)

/-- The hybrid continuation that executes the selected family member and wraps its output in
`some`, returning `none` on timeout. -/
def continuation (F : Family K D m) (z : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration
    (ℕ × ℕ) (Fin K × ℕ × ℕ) × ℕ) : HybridProgram D (Option (Fin m)) :=
  match rejectionOutcome z.1 with
  | .inl u => (F.program u).bind fun i => .ret (some i)
  | .inr _ => .ret none

/-- For a pure input density operator, expected leaf cost equals count-sensitive program
evaluation from zero counts. -/
theorem leaf_cost_pure (F : Family K D m) (ψ : QState (Fin D))
    (hstate : F.state = outerProduct ψ) (u : Fin K) (g : HybridCounts → ℕ) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
      (fun i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞))).toReal =
      (F.program u).evalCounts F.oracle ψ HybridCounts.zero
        (fun _ φ c => branchMass φ * (g c : ℝ)) := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top
    ((F.leaves u).apply_ne_top i) (by simp))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, leaves, instrumentPMF_apply,
    ENNReal.toReal_ofReal (instrumentProb_nonneg _ F.density.1 _)]
  rw [hstate]
  exact (F.program u).evalCounts_instrument F.oracle F.oracle_unitary (F.legal u) ψ
    (fun _ c => (g c : ℝ))

/-- On a pure input state, the capped program's probability of a successful output agrees with
the corresponding capped receipt probability. -/
theorem cappedProgram_receipt (F : Family K D m) (ψ : QState (Fin D))
    (hstate : F.state = outerProduct ψ) (w : Fin K → ℕ) (b fuel : ℕ) (i : Fin m) :
    (F.cappedProgram w b fuel).eval F.oracle ψ
      (fun j φ => branchMass φ * if j = some i then 1 else 0) =
      (((F.capped w b fuel).map F.cappedValue) (some i)).toReal := by
  classical
  let g : SelectorResult K → ℝ := fun z =>
    (F.continuation z.1).eval F.oracle ψ
      (fun j φ => branchMass φ * if j = some i then 1 else 0)
  have hg : ∀ z, 0 ≤ g z := by
    intro z
    apply HybridProgram.eval_nonneg
    intro j φ
    split_ifs
    · exact mul_nonneg (branchMass_nonneg φ) (by norm_num)
    · simp
  have hn (z : SelectorResult K) : ENNReal.ofReal (g z) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (F.cappedNext z) (fun r => F.cappedValue r = some i) := by
    cases h : selected z with
    | inl u =>
        have h' : rejectionOutcome z.1.1 = .inl u := h
        simp only [g, continuation, h', HybridProgram.eval_bind, HybridProgram.eval,
          Option.some.injEq, cappedNext, h, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, cappedValue]
        rw [← F.output_pure_eval ψ hstate u i, ENNReal.ofReal_toReal ((F.output u).apply_ne_top i)]
        exact map_apply_event (F.leaves u)
          (fun j => ((F.program u).leaf F.oracle j).value) i
    | inr v =>
        have h' : rejectionOutcome z.1.1 = .inr v := h
        simp [g, continuation, h', HybridProgram.eval, cappedNext, h,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, cappedValue]
  change (HybridProgram.ofCoins (weightedSampler w b fuel) F.continuation).eval
    F.oracle ψ _ = _
  rw [HybridProgram.eval_ofCoins]
  change ((weightedSampler w b fuel).paths.map (fun z =>
    CoinCode.wordWeight z.2 * g (z.1,z.2.length))).sum = _
  rw [coin_paths_expectation _ g hg]
  congr 1
  rw [map_apply_event, capped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  apply congrArg
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler w b fuel).law)
  funext z
  exact hn z

/-- Count-sensitive evaluation of the capped program is the weighted sum over selector coin
paths, adding each path's bit length before evaluating its continuation. -/
theorem cappedProgram_counts (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (ψ : QState (Fin D)) (c : HybridCounts)
    (g : Option (Fin m) → QState (Fin D) → HybridCounts → ℝ) :
    (F.cappedProgram w b fuel).evalCounts F.oracle ψ c g =
      ((weightedSampler w b fuel).paths.map (fun z => CoinCode.wordWeight z.2 *
        (F.continuation z.1).evalCounts F.oracle ψ (c.plus ⟨0,0,0,z.2.length⟩) g)).sum :=
  HybridProgram.evalCounts_ofCoins _ _ _ _ _ _

end Family

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
