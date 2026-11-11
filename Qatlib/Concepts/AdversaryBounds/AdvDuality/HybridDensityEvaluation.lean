/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainder

/-!
# Density Operator Evaluation of Hybrid Programs

This module evaluates hybrid programs by propagating unnormalized density operators through
gates, oracle calls, and measurement branches, and averaging fair coin choices. The construction
follows the operator description of quantum operations in [Kraus1971] and [Watrous2018].
`HybridProgram.evalDensity` evaluates terminal functionals, while
`HybridProgram.evalDensityCounts` also carries operation counts.

Leaf expansions connect these recursive evaluators to the instrument associated with a legal
program. The pure-state compatibility result identifies density evaluation on an outer product
with the existing pure-state evaluator.

## Main statements

* `evalDensity_bind` and `evalDensityCounts_bind` describe evaluation under sequential
  composition.
* `evalDensity_leaves` and `evalDensityCounts_leaves` expand evaluation as weighted sums over
  leaves.
* `evalDensity_instrument` and `evalDensityCounts_instrument` identify trace-weighted evaluation
  with instrument expectations.
* `evalDensity_pure` establishes compatibility with pure-state evaluation.

## References

* [Kraus, 1971][Kraus1971], General state changes in quantum theory.
* [Watrous, 2018][Watrous2018], The Theory of Quantum Information.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib
open scoped Classical ENNReal ComplexOrder
variable {D : ℕ} {A B : Type}

/-- Conjugation by a product of operators is the composition of their conjugation maps in the
same order. -/
theorem density_conj_mul (M N : Operator D) (ρ : Operator D) :
    conjBranch (M*N) ρ = conjBranch M (conjBranch N ρ) := by
  simp only [conjBranch_apply,Matrix.conjTranspose_mul,Matrix.mul_assoc]

namespace HybridProgram

/-- Evaluates a terminal functional by propagating unnormalized density operators through a
hybrid program, averaging fair coin choices and summing measurement branches. -/
def evalDensity (O : Operator D) : HybridProgram D A → Operator D →
    (A → Operator D → ℝ) → ℝ
  | .ret a,ρ,F => F a ρ
  | .step (.gate U) p,ρ,F => p.evalDensity O (conjBranch U ρ) F
  | .step .query p,ρ,F => p.evalDensity O (conjBranch O ρ) F
  | .bit p q,ρ,F => (1/2:ℝ)*(p.evalDensity O ρ F+q.evalDensity O ρ F)
  | .measure n label k,ρ,F => ∑ i : Fin n,
      (k i).evalDensity O (conjBranch (Projector (Finset.univ.filter fun x => label x=i)) ρ) F
  | .project P p q,ρ,F => p.evalDensity O (conjBranch (1-P) ρ) F + q.evalDensity O (conjBranch P ρ) F

/-- Evaluates a hybrid program on a density operator while accumulating query, gate,
measurement, and coin counts for the terminal functional. -/
def evalDensityCounts (O : Operator D) : HybridProgram D A → Operator D → HybridCounts →
    (A → Operator D → HybridCounts → ℝ) → ℝ
  | .ret a,ρ,c,F => F a ρ c
  | .step (.gate U) p,ρ,c,F => p.evalDensityCounts O (conjBranch U ρ) (c.plus ⟨0,1,0,0⟩) F
  | .step .query p,ρ,c,F => p.evalDensityCounts O (conjBranch O ρ) (c.plus ⟨1,0,0,0⟩) F
  | .bit p q,ρ,c,F => (1/2:ℝ)*(p.evalDensityCounts O ρ (c.plus ⟨0,0,0,1⟩) F+
      q.evalDensityCounts O ρ (c.plus ⟨0,0,0,1⟩) F)
  | .measure n label k,ρ,c,F => ∑ i : Fin n,
      (k i).evalDensityCounts O (conjBranch (Projector (Finset.univ.filter fun x => label x=i)) ρ)
        (c.plus ⟨0,0,1,0⟩) F
  | .project P p q,ρ,c,F => p.evalDensityCounts O (conjBranch (1-P) ρ) (c.plus ⟨0,0,1,0⟩) F+
      q.evalDensityCounts O (conjBranch P ρ) (c.plus ⟨0,0,1,0⟩) F

end HybridProgram

/-- Density evaluation of a sequential composition equals evaluation of the first program with
the continuation evaluator as its terminal functional. -/
theorem evalDensity_bind (O : Operator D) (p : HybridProgram D A) (k : A → HybridProgram D B)
    (ρ : Operator D) (F : B → Operator D → ℝ) :
    (p.bind k).evalDensity O ρ F = p.evalDensity O ρ (fun a σ => (k a).evalDensity O σ F) := by
  induction p generalizing ρ with
  | ret a => rfl
  | step s p ih => cases s <;> simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensity,ih]
  | bit p q hp hq => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensity,hp,hq]
  | measure n label k ih => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensity,ih]
  | project P p q hp hq => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensity,hp,hq]

/-- Expands density evaluation as the sum of terminal functionals on leaf-conjugated states,
weighted by the corresponding coin-word weights. -/
theorem evalDensity_leaves (O : Operator D) (p : HybridProgram D A) (ρ : Operator D)
    (F : A → Operator D → ℝ) :
    p.evalDensity O ρ F = ((p.leaves O).map (fun t => CoinCode.wordWeight t.coins *
      F t.value (conjBranch t.operator ρ))).sum := by
  induction p generalizing ρ with
  | ret a => simp [evalDensity,leaves,CoinCode.wordWeight]
  | step s p ih => cases s <;>
      simp only [evalDensity,leaves,ih,List.map_map,Function.comp_def,HybridLeaf.quantum,density_conj_mul]
  | bit p q hp hq =>
      simp only [evalDensity,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.coin,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left]
  | measure n label k ih =>
      simp only [evalDensity,leaves,List.map_flatten,List.sum_flatten,List.map_ofFn,
        Function.comp_def,List.map_map,List.sum_ofFn,HybridLeaf.quantum,density_conj_mul,ih]
  | project P p q hp hq =>
      simp only [evalDensity,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.quantum,density_conj_mul]

/-- For a legal hybrid program and a unitary oracle, the instrument-weighted sum of a function
of the returned value equals density evaluation of its trace-weighted terminal functional. -/
theorem evalDensity_instrument (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ρ : Operator D) (f : A → ℝ) :
    (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) ρ i * f (p.leaf O i).value) =
      p.evalDensity O ρ (fun a σ => (Matrix.trace σ).re * f a) := by
  rw [evalDensity_leaves,← p.leaf_ofFn O,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [p.probability_law]
  exact mul_assoc _ _ _

/-- Density evaluation on the outer product of a pure state agrees with pure-state evaluation
after applying the outer product to each terminal state. -/
theorem evalDensity_pure (O : Operator D) (p : HybridProgram D A) (ψ : QState (Fin D))
    (F : A → Operator D → ℝ) :
    p.evalDensity O (outerProduct ψ) F = p.eval O ψ (fun a φ => F a (outerProduct φ)) := by
  rw [evalDensity_leaves,eval_leaves]
  simp only [conjBranch_outerProduct,ApplyGate]

/-- Density evaluation of a program selected by `CoinCode` is the sum of the continuation
evaluations over coin paths, weighted by their word weights. -/
theorem evalDensity_ofCoins (O : Operator D) (p : CoinCode B) (k : B → HybridProgram D A)
    (ρ : Operator D) (F : A → Operator D → ℝ) :
    (ofCoins p k).evalDensity O ρ F =
      (p.paths.map (fun z => CoinCode.wordWeight z.2 * (k z.1).evalDensity O ρ F)).sum := by
  induction p with
  | ret a => simp [ofCoins,CoinCode.paths,CoinCode.wordWeight]
  | bit p q hp hq =>
      simp only [ofCoins,evalDensity,CoinCode.paths,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left,hp,hq]

/-- Counted density evaluation respects sequential composition by passing the intermediate
value, density operator, and accumulated counts to the continuation. -/
theorem evalDensityCounts_bind (O : Operator D) (p : HybridProgram D A) (k : A → HybridProgram D B)
    (ρ : Operator D) (c : HybridCounts) (F : B → Operator D → HybridCounts → ℝ) :
    (p.bind k).evalDensityCounts O ρ c F =
      p.evalDensityCounts O ρ c (fun a σ c' => (k a).evalDensityCounts O σ c' F) := by
  induction p generalizing ρ c with
  | ret a => rfl
  | step s p ih => cases s <;> simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensityCounts,ih]
  | bit p q hp hq => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensityCounts,hp,hq]
  | measure n label k ih => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensityCounts,ih]
  | project P p q hp hq => simp only [Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.bind,evalDensityCounts,hp,hq]

/-- Expands counted density evaluation into a coin-weighted sum over leaves, adding each leaf's
operation counts to the initial counts. -/
theorem evalDensityCounts_leaves (O : Operator D) (p : HybridProgram D A) (ρ : Operator D)
    (c : HybridCounts) (F : A → Operator D → HybridCounts → ℝ) :
    p.evalDensityCounts O ρ c F = ((p.leaves O).map (fun t => CoinCode.wordWeight t.coins *
      F t.value (conjBranch t.operator ρ) (c.plus t.counts))).sum := by
  induction p generalizing ρ c with
  | ret a => simp [evalDensityCounts,leaves,CoinCode.wordWeight,HybridLeaf.counts,HybridCounts.plus]
  | step s p ih => cases s <;>
      simp only [evalDensityCounts,leaves,ih,List.map_map,Function.comp_def,HybridLeaf.counts_quantum,
        HybridCounts.plus_shuffle,HybridLeaf.quantum_value,HybridLeaf.quantum_coins,
        HybridLeaf.quantum_operator,density_conj_mul]
  | bit p q hp hq =>
      simp only [evalDensityCounts,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.counts_coin,HybridCounts.plus_shuffle,HybridLeaf.coin_value,
        HybridLeaf.coin_coins,HybridLeaf.coin_operator,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left]
  | measure n label k ih =>
      simp only [evalDensityCounts,leaves,List.map_flatten,List.sum_flatten,List.map_ofFn,
        Function.comp_def,List.map_map,List.sum_ofFn,HybridLeaf.counts_quantum,
        HybridCounts.plus_shuffle,HybridLeaf.quantum_value,HybridLeaf.quantum_coins,
        HybridLeaf.quantum_operator,density_conj_mul,ih]
  | project P p q hp hq =>
      simp only [evalDensityCounts,leaves,hp,hq,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,HybridLeaf.counts_quantum,HybridCounts.plus_shuffle,
        HybridLeaf.quantum_value,HybridLeaf.quantum_coins,HybridLeaf.quantum_operator,density_conj_mul]

/-- The instrument-weighted sum of a function of returned values and leaf counts equals counted
density evaluation from zero counts with a trace-weighted terminal functional. -/
theorem evalDensityCounts_instrument (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ρ : Operator D) (f : A → HybridCounts → ℝ) :
    (∑ i : Fin p.leafCount, instrumentProb (p.instrument O hO hp) ρ i *
      f (p.leaf O i).value (p.leaf O i).counts) =
      p.evalDensityCounts O ρ HybridCounts.zero (fun a σ c => (Matrix.trace σ).re * f a c) := by
  rw [evalDensityCounts_leaves,← p.leaf_ofFn O,List.map_ofFn,List.sum_ofFn]
  simp only [HybridCounts.zero_plus]
  apply Finset.sum_congr rfl
  intro i _
  rw [p.probability_law]
  exact mul_assoc _ _ _

/-- Counted density evaluation of `ofCoins` is a weighted sum over coin paths, with each path
length added to the accumulated coin count. -/
theorem evalDensityCounts_ofCoins (O : Operator D) (p : CoinCode B) (k : B → HybridProgram D A)
    (ρ : Operator D) (c : HybridCounts) (F : A → Operator D → HybridCounts → ℝ) :
    (ofCoins p k).evalDensityCounts O ρ c F =
      (p.paths.map (fun z => CoinCode.wordWeight z.2 *
        (k z.1).evalDensityCounts O ρ (c.plus ⟨0,0,0,z.2.length⟩) F)).sum := by
  induction p generalizing c with
  | ret a => simp [ofCoins,CoinCode.paths,CoinCode.wordWeight,HybridCounts.plus]
  | bit p q hp hq =>
      simp only [ofCoins,evalDensityCounts,hp,hq,CoinCode.paths,List.map_append,List.sum_append,
        List.map_map,Function.comp_def,Qatlib.Concepts.AdversaryBounds.AdvDuality.wordWeight_cons,HybridCounts.read_cons,mul_assoc]
      rw [mul_add,List.sum_map_mul_left,List.sum_map_mul_left]

/-- A legal hybrid program with a unitary oracle has nonnegative trace-weighted density
evaluation on a positive semidefinite input and a nonnegative terminal function. -/
theorem evalDensity_trace_nonneg (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (p : HybridProgram D A) (hp : p.Legal) (ρ : Operator D) (hρ : ρ.PosSemidef)
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ p.evalDensity O ρ (fun a σ => (Matrix.trace σ).re * f a) := by
  rw [← evalDensity_instrument O hO p hp ρ f]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (instrumentProb_nonneg _ hρ _) (hf _)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
