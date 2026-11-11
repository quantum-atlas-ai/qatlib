/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.GeneralAdversaryDefs
import Qatlib.Concepts.ConversionCore.AdversaryValue.GeneralAdversaryValueIdentQuan
import Qatlib.Concepts.ConversionCore.AdversaryValue.GeneralAdversaryValueIdentStat

/-!
# General adversary and execution accounting

`clause21` bundles general adversary value identification with probability-mass conservation, a
cost-overflow bound, and existence statements for the accompanying computation models. The
concrete examples include a zero-round alphabet computation, a finite-cost sequence of costed
laws, and an already halted configuration with zero nontermination mass.

The adversary component belongs to the state conversion framework of [LeeEtAl2011]; the other
statements supply execution and resource bookkeeping.

## Main statements

* `trivial_alphabet_adaptive`: a zero-round computation satisfying parameter positivity.
* `zeno_unit_run` and `zero_tail`: elementary cost and tail examples.
* `clause21`: the combined identification and accounting statement.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.ConversionCore.AdversaryValue
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.ConversionCore.WitnessCompile

open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ConversionCore.AdversaryValue Qatlib.Concepts.ConversionCore.WitnessCompile
open scoped Classical ENNReal

/-- For positive coordinate count and state dimension, there exists an alphabet-adaptive object
satisfying `AlphabetAdaptive.Correct`. -/
theorem trivial_alphabet_adaptive (n D : ℕ) (O : Type) [Fintype O]
    (hn : 0 < n) (hD : 0 < D) :
    ∃ s : AlphabetAdaptive O n D, AlphabetAdaptive.Correct s := by
  refine ⟨⟨0, (fun x : Fin 0 => nomatch x), 1⟩, ?_⟩
  exact ⟨by norm_num, hn, hD⟩

/-- There exists a state sequence whose costed step laws have nonempty supports and finite total
expected cost, as required by `ZenoRun`. -/
theorem zeno_unit_run :
    ∃ (S : Type) (step : S → CostedLaw S) (s : ℕ → S), ZenoRun step s := by
  refine ⟨Unit, fun _ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (), fun _ => (), ?_⟩
  refine ⟨?_, ?_⟩
  · intro k
    show (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret ()).support.Nonempty
    rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret () = (PMF.pure (((), 0) : Unit × ℕ)) from rfl,
      PMF.support_pure]
    exact Set.singleton_nonempty _
  · have hsum : (∑' k : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret ())) = 0 := by simp
    rw [hsum]
    exact bot_lt_top

/-- For every extended nonnegative tolerance, there exists a singleton-state unbounded adversary
and a configuration whose nontermination mass is at most that tolerance. -/
theorem zero_tail :
    ∀ tol : ℝ≥0∞,
      ∃ (u : UnboundedAdversary (Fin 1) (Fin 1))
        (cfg : Configuration (Fin 1) (Fin 1)),
        u.TailTruncated cfg tol := by
  intro tol
  refine ⟨⟨fun _ => PMF.pure (Sum.inl 0)⟩, Sum.inl 0, ?_⟩
  have hp : ∀ fuel : ℕ,
      pendingMass (fun _ => PMF.pure (Sum.inl (0 : Fin 1)))
        (Sum.inl (0 : Fin 1) : Configuration (Fin 1) (Fin 1)) fuel = 0 := by
    intro fuel
    show (∑ s : Fin 1, ∑ k ∈ Finset.range (fuel + 1),
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.runFor _ fuel
        (Sum.inl (0 : Fin 1) : Configuration (Fin 1) (Fin 1)) (Sum.inr s, k)) = 0
    rw [runFor_halted]
    refine Finset.sum_eq_zero fun s _ => ?_
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_apply]
  have h0 : nonterminationMass (fun _ => PMF.pure (Sum.inl (0 : Fin 1)))
      (Sum.inl (0 : Fin 1) : Configuration (Fin 1) (Fin 1)) = 0 := by
    have hle := iInf_le
      (fun fuel => pendingMass (fun _ => PMF.pure (Sum.inl (0 : Fin 1)))
        (Sum.inl (0 : Fin 1) : Configuration (Fin 1) (Fin 1)) fuel) 0
    rw [show pendingMass (fun _ => PMF.pure (Sum.inl (0 : Fin 1)))
        (Sum.inl (0 : Fin 1) : Configuration (Fin 1) (Fin 1)) 0 = 0 from hp 0] at hle
    exact le_antisymm hle bot_le
  show nonterminationMass _ _ ≤ tol
  rw [h0]
  exact bot_le

/-- General adversary value identification holds together with unbounded-execution mass
identities, the overflow-cost bound, and the stated existence results for adaptive objects,
finite-cost sequences, tail bounds, resource records, and polynomial-time machine families. -/
theorem clause21 :

  (∀ (n D : ℕ) (O : Type) [Fintype O], 0 < n → 0 < D →
    ∃ s : AlphabetAdaptive O n D, AlphabetAdaptive.Correct s) ∧

  (Qatlib.Concepts.ConversionCore.AdversaryValue.GeneralAdversaryValueIdentification) ∧

  (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (Configuration S O)) (cfg : Configuration S O),
    (∑' z : Option (O × ℕ), unboundedMass next cfg z) = 1) ∧

  (∀ (S O : Type) [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
      (next : S → PMF (Configuration S O)) (cfg : Configuration S O),
    (∑' o : O, ∑' k : ℕ, haltJoint next cfg o k) + nonterminationMass next cfg = 1) ∧

  (∀ (α : Type) (p : CostedLaw α) (budget : ℕ),
    ((budget + 1 : ℝ≥0∞)) * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.overflow p budget ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost p) ∧

  (∃ (S : Type) (step : S → CostedLaw S) (s : ℕ → S), ZenoRun step s) ∧

  (∀ tol : ℝ≥0∞,
    ∃ (u : UnboundedAdversary (Fin 1) (Fin 1))
      (cfg : Configuration (Fin 1) (Fin 1)),
      u.TailTruncated cfg tol) ∧

  (∀ len : ℕ, ∃ x : AdversaryResources, x.inputLen = len ∧ AdversaryResources.PolyBounded x) ∧

  (∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] [Fintype Γ] [Fintype Λ],
    ∃ f : NativeTMFamily Γ Λ, f.UniformPolyTime) ∧

  (fixedTreeNotGeneralEndpoint) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n D O _inst hn hD
    exact trivial_alphabet_adaptive n D O hn hD
  · exact generalAdversaryValueIdentification
  · intro S O _a _b _c _d next cfg
    exact unboundedMass_tsum next cfg
  · intro S O _a _b _c _d next cfg
    exact haltJoint_tsum_add_nonterminationMass next cfg
  · intro α p budget
    exact Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.overflow_mul_le_expectedCost p budget
  · exact zeno_unit_run
  · exact zero_tail
  · intro len
    refine ⟨⟨len, 0, 0⟩, rfl, ⟨1, 0, ?_, ?_⟩⟩
    · show (0 : ℕ) ≤ 1 * (len + 1) ^ 0
      norm_num
    · show (0 : ℕ) ≤ 1 * (len + 1) ^ 0
      norm_num
  · intro Γ Λ _iΓ _iΛ _fΓ _fΛ
    refine ⟨⟨fun _ _ _ => none⟩, 1, 0, ?_⟩
    intro len input _hlen
    refine ⟨0, ?_, Turing.TM0.init input, rfl, ?_⟩
    · show (0 : ℕ) ≤ 1 * len ^ 0 + 1
      norm_num
    · show Turing.TM0.step (fun _ _ => none) (Turing.TM0.init input) = none
      rfl
  · intro n D O _inst hn hD
    exact trivial_alphabet_adaptive n D O hn hD

end Qatlib.Concepts.ConversionCore.WitnessCompile
