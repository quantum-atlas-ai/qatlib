/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryDefs
import Mathlib.Algebra.Order.Floor.Semiring
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitCompile
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedRelabel
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPairedExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.AdversaryBounds.AdvDuality.KrausCircuitMixed
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.Execution.CircuitCompile.InstrumentCircuitTransport
import Qatlib.Concepts.AdversaryBounds.AdvDuality.VariableKrausStatistics
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryPhaseOracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
noncomputable section

theorem instrument_final_progress {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] {D E : ℕ}
    (I : Instrument Y D E) (G : Matrix X X ℂ) (f : X → Y) (eps : ℝ)
    (weight : QState X) (states : X → QState (Fin D)) (hG : G.IsHermitian)
    (hw : Normalized weight) (hs : ∀ x, Normalized (states x))
    (hz : ∀ x y, f x = f y → G x y = 0) (he0 : 0 ≤ eps) (he1 : eps ≤ 1/2)
    (hsuccess : ∀ x, 1 - eps ≤ (Matrix.trace (I.branch (f x) (outerProduct (states x)))).re) :
    |advProgress G weight states| ≤ (2 * Real.sqrt (eps * (1-eps)) + 2*eps) * ‖G‖ := by
  apply povm_final_progress G f (instrumentReadout I) eps weight states hG hw hs hz he0 he1
    (instrumentReadout_isPovm I)
  intro x
  rw [instrumentReadout_prob]
  exact hsuccess x
end
noncomputable section

theorem composed_probability_family {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (pf : (Fin k → Bool) → Fin k → ℝ)
    (pg : ∀ i, X i → Fin (n i) → ℝ)
    (hf : IsProbabilityFamily pf) (hg : ∀ i, IsProbabilityFamily (pg i)) :
    IsProbabilityFamily (composeMinimaxWitness g pf pg) := by
  constructor
  · intro x c
    exact mul_nonneg (hf.1 _ _) ((hg c.1).1 _ _)
  · intro x
    simp only [composeMinimaxWitness, Fintype.sum_sigma, ← Finset.mul_sum]
    simp only [fun i => (hg i).2 (x i), mul_one]
    exact hf.2 _
end
noncomputable section

theorem composed_minimax_term {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (pf : (Fin k → Bool) → Fin k → ℝ) (pg : ∀ i, X i → Fin (n i) → ℝ)
    (hf : IsProbabilityFamily pf)
    (x y : (i : Fin k) → X i) :
    advMinimaxTerm (composedInput gin) alpha (composeMinimaxWitness g pf pg) x y =
      ∑ i, Real.sqrt (pf (fun j => g j (x j)) i * pf (fun j => g j (y j)) i) *
        advMinimaxTerm (gin i) (fun j => alpha ⟨i, j⟩) (pg i) (x i) (y i) := by
  simp only [advMinimaxTerm, Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (if gin i (x i) j ≠ gin i (y i) j then _ else 0) = _
  by_cases hd : gin i (x i) j = gin i (y i) j
  · simp [hd]
  · simp only [ne_eq, hd, not_false_eq_true, ite_true, composeMinimaxWitness]
    have he : (pf (fun j => g j (x j)) i * pg i (x i) j) *
        (pf (fun j => g j (y j)) i * pg i (y i) j) =
        (pf (fun j => g j (x j)) i * pf (fun j => g j (y j)) i) *
          (pg i (x i) j * pg i (y i) j) := by ring
    rw [he, Real.sqrt_mul (mul_nonneg (hf.1 _ _) (hf.1 _ _))]
    ring
end
noncomputable section

theorem composed_minimax_term_lower {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (alpha : ((i : Fin k) × Fin (n i)) → ℝ) (beta : Fin k → ℝ)
    (pf : (Fin k → Bool) → Fin k → ℝ) (pg : ∀ i, X i → Fin (n i) → ℝ)
    (hf : IsProbabilityFamily pf) (ha : ∀ c, 0 ≤ alpha c)
    (x y : (i : Fin k) → X i)
    (hblock : ∀ i, g i (x i) ≠ g i (y i) →
      1 / beta i ≤ advMinimaxTerm (gin i) (fun j => alpha ⟨i,j⟩) (pg i) (x i) (y i)) :
    advMinimaxTerm (fun u : Fin k → Bool => u) beta pf
        (fun i => g i (x i)) (fun i => g i (y i)) ≤
      advMinimaxTerm (composedInput gin) alpha (composeMinimaxWitness g pf pg) x y := by
  rw [composed_minimax_term gin g alpha pf pg hf]
  unfold advMinimaxTerm
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : g i (x i) = g i (y i)
  · simp only [ne_eq, hi, not_true_eq_false, ite_false]
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact Finset.sum_nonneg fun j _ => by
      by_cases h : gin i (x i) j = gin i (y i) j
      · simp [h]
      · simp only [ne_eq, h, not_false_eq_true, ite_true]
        exact div_nonneg (Real.sqrt_nonneg _) (ha ⟨i,j⟩)
  · rw [if_pos hi]
    calc
      _ = Real.sqrt (pf (fun j => g j (x j)) i * pf (fun j => g j (y j)) i) * (1 / beta i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hblock i hi) (Real.sqrt_nonneg _)
end
noncomputable section

theorem probability_family_closed {X K : Type} [Fintype X] [Fintype K] [DecidableEq K] :
    IsClosed {p : X → K → ℝ | IsProbabilityFamily p} := by
  have ha : IsClosed {p : X → K → ℝ | ∀ x i, 0 ≤ p x i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun i =>
      isClosed_le continuous_const ((continuous_apply i).comp (continuous_apply x))
  have hb : IsClosed {p : X → K → ℝ | ∀ x, ∑ i, p x i = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_eq
      (continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_apply x)) continuous_const
  exact ha.inter hb
end
noncomputable section

theorem probability_family_compact {X K : Type} [Fintype X] [Fintype K] [DecidableEq K] :
    IsCompact {p : X → K → ℝ | IsProbabilityFamily p} := by
  apply (isCompact_Icc (a := (0 : X → K → ℝ)) (b := 1)).of_isClosed_subset probability_family_closed
  intro p hp
  constructor
  · exact hp.1
  · intro x i
    exact (Finset.single_le_sum (fun j _ => hp.1 x j) (Finset.mem_univ i)).trans_eq (hp.2 x)
end
noncomputable section

theorem minimax_pair_continuous {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
    (input : X → K → Bool) (alpha : K → ℝ) (x y : X) :
    Continuous (fun p : X → K → ℝ => advMinimaxTerm input alpha p x y) := by
  apply continuous_finsetSum
  intro i _
  by_cases h : input x i = input y i
  · simp only [h, ne_eq, not_true_eq_false, ite_false]
    exact continuous_const
  · simp only [ne_eq, h, not_false_eq_true, ite_true]
    have hx : Continuous (fun p : X → K → ℝ => p x i) :=
      (continuous_apply i).comp (continuous_apply x)
    have hy : Continuous (fun p : X → K → ℝ => p y i) :=
      (continuous_apply i).comp (continuous_apply y)
    exact (Real.continuous_sqrt.comp (hx.mul hy)).div_const _
end
noncomputable section

theorem minimax_optimal_exists {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (hne : ∃ x y, f x ≠ f y) :
    ∃ p : X → K → ℝ, IsMinimaxOptimal input f alpha p := by
  let P : Set (X → K → ℝ) := {p | IsProbabilityFamily p}
  have hp : P.Nonempty := by
    refine ⟨fun _ _ => (Fintype.card K : ℝ)⁻¹, ?_⟩
    constructor
    · intro x i; positivity
    · intro x
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  let J := {xy : X × X // f xy.1 ≠ f xy.2}
  haveI : Nonempty J := let ⟨x,y,h⟩ := hne; ⟨⟨(x,y),h⟩⟩
  let obj (p : X → K → ℝ) : ℝ :=
    ⨅ xy : J, advMinimaxTerm input alpha p xy.1.1 xy.1.2
  have hcont : Continuous obj := by
    have h := Continuous.finset_inf'_apply (s := Finset.univ) (Finset.univ_nonempty (α := J))
      (fun xy _ => minimax_pair_continuous input alpha xy.1.1 xy.1.2)
    simpa only [Finset.inf'_univ_eq_ciInf] using! h
  obtain ⟨p, hP, hmax⟩ := probability_family_compact.exists_isMaxOn hp hcont.continuousOn
  refine ⟨p, hP, ?_⟩
  unfold minimaxWitnessValue minimaxAlpha
  congr 1
  apply le_antisymm
  · exact le_iSup_of_le ⟨p,hP⟩ le_rfl
  · apply iSup_le
    intro t
    apply ENNReal.ofReal_le_ofReal
    exact hmax t.property
end
noncomputable section

theorem minimax_value_le_witness {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K] (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (p : X → K → ℝ) (hp : IsProbabilityFamily p) :
    minimaxAlpha input f alpha ≤ minimaxWitnessValue input f alpha p := by
  unfold minimaxAlpha minimaxWitnessValue
  exact ENNReal.inv_le_inv.mpr (le_iSup_of_le ⟨p,hp⟩ le_rfl)
end
noncomputable section

theorem composed_minimax_witness_bound {k : ℕ} {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (beta : Fin k → ℝ) (pf : (Fin k → Bool) → Fin k → ℝ)
    (pg : ∀ i, X i → Fin (n i) → ℝ) (hf : IsProbabilityFamily pf)
    (ha : ∀ c, 0 ≤ alpha c)
    (hne : ∃ x y, composedFunction g f x ≠ composedFunction g f y)
    (hblock : ∀ i a b, g i a ≠ g i b →
      1 / beta i ≤ advMinimaxTerm (gin i) (fun j => alpha ⟨i,j⟩) (pg i) a b) :
    minimaxWitnessValue (composedInput gin) (composedFunction g f) alpha
        (composeMinimaxWitness g pf pg) ≤
      minimaxWitnessValue (fun u : Fin k → Bool => u) f beta pf := by
  let Jh := {xy : ((i : Fin k) → X i) × ((i : Fin k) → X i) //
    composedFunction g f xy.1 ≠ composedFunction g f xy.2}
  let Jf := {uv : (Fin k → Bool) × (Fin k → Bool) // f uv.1 ≠ f uv.2}
  haveI : Nonempty Jh := let ⟨x,y,h⟩ := hne; ⟨⟨(x,y),h⟩⟩
  unfold minimaxWitnessValue
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.ofReal_le_ofReal
  apply le_ciInf
  intro xy
  let uv : Jf := ⟨((fun i => g i (xy.1.1 i)), fun i => g i (xy.1.2 i)),xy.2⟩
  apply (ciInf_le (Set.finite_range _).bddBelow uv).trans
  exact composed_minimax_term_lower gin g alpha beta pf pg hf ha xy.1.1 xy.1.2
    (fun i h => hblock i _ _ h)
end
noncomputable section

theorem optimal_minimax_denominator {X K : Type} [Fintype X] [DecidableEq X]
    [Fintype K] [DecidableEq K] (input : X → K → Bool) (f : X → Bool)
    (alpha : K → ℝ) (p : X → K → ℝ) (beta : ℝ)
    (ha : ∀ i, 0 ≤ alpha i) (hne : ∃ x y, f x ≠ f y)
    (hp : minimaxWitnessValue input f alpha p = ENNReal.ofReal beta) (hb : 0 ≤ beta)
    (x y : X) (hxy : f x ≠ f y) :
    1 / beta ≤ advMinimaxTerm input alpha p x y := by
  let J := {xy : X × X // f xy.1 ≠ f xy.2}
  haveI : Nonempty J := let ⟨x,y,h⟩ := hne; ⟨⟨(x,y),h⟩⟩
  have hnon : 0 ≤ ⨅ xy : J, advMinimaxTerm input alpha p xy.1.1 xy.1.2 := by
    apply le_ciInf
    intro xy
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : input xy.1.1 i = input xy.1.2 i
    · simp [hi]
    · simp only [ne_eq, hi, not_false_eq_true, ite_true]
      exact div_nonneg (Real.sqrt_nonneg _) (ha i)
  change (ENNReal.ofReal (⨅ xy : J, advMinimaxTerm input alpha p xy.1.1 xy.1.2))⁻¹ =
    ENNReal.ofReal beta at hp
  have he := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hnon, ENNReal.toReal_ofReal hb] at he
  have hi := congrArg Inv.inv he
  rw [inv_inv] at hi
  rw [one_div, ← hi]
  exact ciInf_le (Set.finite_range _).bddBelow (⟨(x,y),hxy⟩ : J)
end
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
noncomputable section

theorem minimax_composition_upper {k : ℕ} [Nonempty (Fin k)]
    {X : Fin k → Type} {n : Fin k → ℕ}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [∀ i, Nonempty (Fin (n i))]
    (gin : ∀ i, X i → Fin (n i) → Bool) (g : ∀ i, X i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (beta : Fin k → ℝ) (ha : ∀ c, 0 ≤ alpha c) (hb : ∀ i, 0 ≤ beta i)
    (hne : ∃ x y, composedFunction g f x ≠ composedFunction g f y)
    (hgne : ∀ i, ∃ a b, g i a ≠ g i b)
    (hbeta : ∀ i, minimaxAlpha (gin i) (g i) (fun j => alpha ⟨i,j⟩) = ENNReal.ofReal (beta i)) :
    minimaxAlpha (composedInput gin) (composedFunction g f) alpha ≤
      minimaxAlpha (fun u : Fin k → Bool => u) f beta := by
  have hfne : ∃ u v, f u ≠ f v := by
    obtain ⟨x,y,hxy⟩ := hne
    exact ⟨fun i => g i (x i), fun i => g i (y i), hxy⟩
  obtain ⟨pf,hpf⟩ := minimax_optimal_exists (fun u : Fin k → Bool => u) f beta hfne
  choose pg hpg using fun i => minimax_optimal_exists (gin i) (g i)
    (fun j => alpha ⟨i,j⟩) (hgne i)
  calc
    _ ≤ minimaxWitnessValue (composedInput gin) (composedFunction g f) alpha
        (composeMinimaxWitness g pf pg) :=
      minimax_value_le_witness _ _ _ _ (composed_probability_family g pf pg hpf.1 (fun i => (hpg i).1))
    _ ≤ minimaxWitnessValue (fun u : Fin k → Bool => u) f beta pf := by
      apply composed_minimax_witness_bound gin g f alpha beta pf pg hpf.1 ha hne
      intro i a b hab
      exact optimal_minimax_denominator (gin i) (g i) (fun j => alpha ⟨i,j⟩) (pg i)
        (beta i) (fun j => ha ⟨i,j⟩) (hgne i) ((hpg i).2.trans (hbeta i)) (hb i) a b hab
    _ = _ := hpf.2
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
