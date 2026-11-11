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
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryInstrumentMinimax

/-!
# Optimizers for cost-weighted nonnegative adversaries

Defines `CostAdversaryFeasible` for real symmetric entrywise nonnegative witnesses and proves
that its feasible set is compact when outputs are observable from the input encoding and costs
are nonnegative. Normalization then yields optimal witnesses for positive costs and nonconstant
functions.

`OutputObservable` separates finite optima from collisions that force infinite adversary value.
The module also establishes simultaneous adversary and minimax optimizer existence, supporting
the weighted adversary framework of [HoyerLeeSpalek2007].

## Main statements

* `costAdversary_norm_max_exists`: a feasible matrix attains the maximum norm.
* `advAlphaR_optimal_exists`: a nonzero source witness attains the weighted adversary value.
* `adversary_minimax_optimizers_exist`: simultaneous existence of optimal adversary and minimax
  witnesses.
* `advAlphaR_finite_iff_observable`: finiteness is equivalent to output observability under the
  stated hypotheses.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal ComplexConjugate
open Qatlib
open Qatlib

open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false
variable {X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
variable {n q : ℕ} [NeZero q]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000
variable {n q : ℕ} [NeZero q] {W H : Type}
variable {n q : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {n q d s : ℕ} [NeZero q] {W : Type} [Fintype W]
variable {d : ℕ}
variable {X K : Type} [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
noncomputable section

/-- A real symmetric entrywise nonnegative matrix vanishing on equal Boolean outputs whose
coordinate filter norms are bounded by the specified costs. -/
def CostAdversaryFeasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (Gamma : Matrix X X ℝ) : Prop :=
  Gamma.IsSymm ∧ (∀ x y, 0 ≤ Gamma x y) ∧ (∀ x y, f x = f y → Gamma x y = 0) ∧
    ∀ i, ‖genAdvFilter input Gamma i‖ ≤ alpha i
end
noncomputable section

/-- The absolute value of every entry of a real matrix is bounded by its operator norm. -/
theorem real_operator_entry_bound (M : Matrix X X ℝ) (x y : X) : ‖M x y‖ ≤ ‖M‖ := by
  let v : EuclideanSpace ℝ X := PiLp.single 2 y 1
  let w : EuclideanSpace ℝ X := (EuclideanSpace.equiv X ℝ).symm (M *ᵥ v)
  have he : w x = M x y := by simp [w,v]
  have hv : ‖v‖ = 1 := by simp [v,PiLp.norm_single]
  calc
    ‖M x y‖ = ‖w x‖ := by rw [he]
    _ ≤ ‖w‖ := PiLp.norm_apply_le w x
    _ ≤ ‖M‖*‖v‖ := Matrix.l2_opNorm_mulVec M v
    _ = ‖M‖ := by rw [hv,mul_one]
end
noncomputable section

/-- The condition that every pair with different Boolean outputs is separated by at least one
input coordinate. -/
def OutputObservable (input : X → K → Bool) (f : X → Bool) : Prop :=
  ∀ x y, f x ≠ f y → ∃ i, input x i ≠ input y i
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- The zero matrix is a feasible cost-weighted nonnegative adversary whenever all coordinate
costs are nonnegative. -/
theorem costAdversary_zero (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 ≤ alpha i) : CostAdversaryFeasible input f alpha 0 := by
  refine ⟨by rfl,by simp,by simp,?_⟩
  intro i
  have hz : genAdvFilter input (0 : Matrix X X ℝ) i = 0 := by
    ext x y
    change (if input x i ≠ input y i then (0 : ℝ) else 0) = 0
    split_ifs <;> rfl
  rw [hz,norm_zero]
  exact ha i
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- The set of feasible cost-weighted nonnegative adversary matrices is closed. -/
theorem costAdversary_closed (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) :
    IsClosed {Gamma : Matrix X X ℝ | CostAdversaryFeasible input f alpha Gamma} := by
  have hc (i : K) : Continuous (fun G : Matrix X X ℝ => genAdvFilter input G i) := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    change Continuous (fun G : Matrix X X ℝ => if input x i ≠ input y i then G x y else 0)
    by_cases h : input x i ≠ input y i
    · simpa only [if_pos h] using! (show Continuous (fun G : Matrix X X ℝ => G x y) by fun_prop)
    · simpa only [if_neg h] using! (continuous_const : Continuous (fun _ : Matrix X X ℝ => (0 : ℝ)))
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop : Continuous (fun G : Matrix X X ℝ => G.transpose)) continuous_id
  apply IsClosed.inter
  · convert! isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_le continuous_const (show Continuous (fun G : Matrix X X ℝ => G x y) by fun_prop))) using 1
    ext G
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
  apply IsClosed.inter
  · have hs (x y : X) : IsClosed {G : Matrix X X ℝ | f x = f y → G x y = 0} := by
      by_cases h : f x = f y
      · simpa only [h,forall_const] using! isClosed_eq
          (show Continuous (fun G : Matrix X X ℝ => G x y) by fun_prop) continuous_const
      · simp [h]
    convert! isClosed_iInter (fun x => isClosed_iInter (hs x)) using 1
    ext G
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
  · convert! isClosed_iInter (fun i => isClosed_le (continuous_norm.comp (hc i))
      (continuous_const : Continuous (fun _ : Matrix X X ℝ => alpha i))) using 1
    ext G
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs and nonnegative costs, each entry of a feasible adversary is bounded
in absolute value by the sum of the costs. -/
theorem costAdversary_entry_bound (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 ≤ alpha i) (hobs : OutputObservable input f)
    (Gamma : Matrix X X ℝ) (hG : CostAdversaryFeasible input f alpha Gamma) (x y : X) :
    ‖Gamma x y‖ ≤ ∑ i, alpha i := by
  by_cases hf : f x = f y
  · rw [hG.2.2.1 x y hf,norm_zero]
    exact Finset.sum_nonneg (fun i _ => ha i)
  · obtain ⟨i,hi⟩ := hobs x y hf
    have hh := (real_operator_entry_bound (genAdvFilter input Gamma i) x y).trans (hG.2.2.2 i)
    change ‖if input x i ≠ input y i then Gamma x y else 0‖ ≤ alpha i at hh
    rw [if_pos hi] at hh
    exact hh.trans (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs and nonnegative costs, the feasible cost-weighted nonnegative
adversary set is compact. -/
theorem costAdversary_compact (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 ≤ alpha i) (hobs : OutputObservable input f) :
    IsCompact {Gamma : Matrix X X ℝ | CostAdversaryFeasible input f alpha Gamma} := by
  let R := ∑ i, alpha i
  let B : Set (Matrix X X ℝ) := Set.pi Set.univ
    (fun _ : X => Set.pi Set.univ (fun _ : X => Metric.closedBall (0 : ℝ) R))
  have hb : IsCompact B := isCompact_univ_pi (fun _ => isCompact_univ_pi
    (fun _ => isCompact_closedBall 0 R))
  apply hb.of_isClosed_subset (costAdversary_closed input f alpha)
  intro G hG
  change ∀ x ∈ Set.univ, ∀ y ∈ Set.univ, G x y ∈ Metric.closedBall (0 : ℝ) R
  intro x _ y _
  simpa only [Metric.mem_closedBall,dist_zero_right] using!
      costAdversary_entry_bound input f alpha ha hobs G hG x y
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs and nonnegative costs, some feasible adversary matrix maximizes the
operator norm over the feasible set. -/
theorem costAdversary_norm_max_exists (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 ≤ alpha i) (hobs : OutputObservable input f) :
    ∃ Gamma : Matrix X X ℝ, CostAdversaryFeasible input f alpha Gamma ∧
      ∀ H, CostAdversaryFeasible input f alpha H → ‖H‖ ≤ ‖Gamma‖ := by
  exact (costAdversary_compact input f alpha ha hobs).exists_isMaxOn
    ⟨0,costAdversary_zero input f alpha ha⟩ continuous_norm.continuousOn
end
noncomputable section
omit [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K] in

/-- Adversary filtering of real matrices commutes with real scalar multiplication. -/
theorem genAdvFilter_real_smul (input : X → K → Bool) (Gamma : Matrix X X ℝ) (c : ℝ) (i : K) :
    genAdvFilter input (c • Gamma) i = c • genAdvFilter input Gamma i := by
  ext x y
  change (if input x i ≠ input y i then c*Gamma x y else 0) =
    c*(if input x i ≠ input y i then Gamma x y else 0)
  split_ifs <;> simp_all only [mul_zero]
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- For observable outputs, a nonzero real matrix vanishing on equal outputs has a coordinate
filter with positive norm. -/
theorem nonzero_adversary_filter (input : X → K → Bool) (f : X → Bool)
    (hobs : OutputObservable input f) (Gamma : Matrix X X ℝ)
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0) :
    ∃ i, 0 < ‖genAdvFilter input Gamma i‖ := by
  obtain ⟨x,y,hxy⟩ : ∃ x y, Gamma x y ≠ 0 := by
    by_contra h
    apply hne
    ext x y
    exact not_not.mp (not_exists.mp (not_exists.mp h x) y)
  have hf : f x ≠ f y := fun he => hxy (hz x y he)
  obtain ⟨i,hi⟩ := hobs x y hf
  refine ⟨i,norm_pos_iff.mpr ?_⟩
  intro he
  have hh := congrArg (fun G : Matrix X X ℝ => G x y) he
  change (if input x i ≠ input y i then Gamma x y else 0) = 0 at hh
  rw [if_pos hi] at hh
  exact hxy hh
end
noncomputable section

/-- With positive costs and observable outputs, a nonzero symmetric nonnegative supported
witness can be normalized to a nonzero feasible matrix whose norm bounds its weighted
witness value. -/
theorem costAdversary_normalize (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f)
    (Gamma : Matrix X X ℝ) (hs : Gamma.IsSymm) (hp : ∀ x y, 0 ≤ Gamma x y)
    (hz : ∀ x y, f x = f y → Gamma x y = 0) (hne : Gamma ≠ 0) :
    ∃ H : Matrix X X ℝ, CostAdversaryFeasible input f alpha H ∧ H ≠ 0 ∧
      advAlphaWitnessR input alpha Gamma ≤ ENNReal.ofReal ‖H‖ := by
  obtain ⟨i0,hi0⟩ := nonzero_adversary_filter input f hobs Gamma hz hne
  letI : Nonempty K := ⟨i0⟩
  let r : K → ℝ := fun i => ‖genAdvFilter input Gamma i‖ / alpha i
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hr : 0 < r j := (div_pos hi0 (ha i0)).trans_le (hj i0 (Finset.mem_univ i0))
  have hjpos : 0 < ‖genAdvFilter input Gamma j‖ := by
    by_contra h
    have h0 := le_antisymm (not_lt.mp h) (norm_nonneg (genAdvFilter input Gamma j))
    simp only [r,h0,zero_div] at hr
    exact (lt_irrefl 0) hr
  let c := alpha j / ‖genAdvFilter input Gamma j‖
  have hc : 0 < c := div_pos (ha j) hjpos
  have hnorm : ‖c • Gamma‖ = c*‖Gamma‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  refine ⟨c • Gamma,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_⟩
    · change (c • Gamma).transpose = c • Gamma
      rw [Matrix.transpose_smul,hs]
    · intro x y
      exact mul_nonneg hc.le (hp x y)
    · intro x y hf
      change c*Gamma x y = 0
      rw [hz x y hf,mul_zero]
    · intro i
      rw [genAdvFilter_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
      have hratio := (div_le_div_iff₀ (ha i) (ha j)).mp (hj i (Finset.mem_univ i))
      dsimp only [c]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hjpos).mpr
      nlinarith
  · intro h0
    have hn := norm_pos_iff.mpr hne
    have hh := congrArg (fun H : Matrix X X ℝ => ‖H‖) h0
    change ‖c • Gamma‖ = ‖(0 : Matrix X X ℝ)‖ at hh
    rw [hnorm,norm_zero] at hh
    nlinarith
  · calc
      advAlphaWitnessR input alpha Gamma ≤
          ENNReal.ofReal (alpha j)*ENNReal.ofReal ‖Gamma‖ /
            ENNReal.ofReal ‖genAdvFilter input Gamma j‖ := iInf_le _ j
      _ = ENNReal.ofReal (c*‖Gamma‖) := by
        rw [← ENNReal.ofReal_mul (ha j).le,← ENNReal.ofReal_div_of_pos hjpos]
        congr 1
        dsimp only [c]
        ring
      _ = ENNReal.ofReal ‖c • Gamma‖ := by rw [hnorm]
end
noncomputable section

/-- With positive costs, the norm of a feasible nonnegative adversary matrix is bounded by its
weighted witness value. -/
theorem costAdversary_norm_le_witness (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (Gamma : Matrix X X ℝ)
    (hG : CostAdversaryFeasible input f alpha Gamma) :
    ENNReal.ofReal ‖Gamma‖ ≤ advAlphaWitnessR input alpha Gamma := by
  apply le_iInf
  intro i
  by_cases hn : ‖Gamma‖ = 0
  · simp [hn]
  have hnp : 0 < ‖Gamma‖ := lt_of_le_of_ne (norm_nonneg Gamma) (Ne.symm hn)
  by_cases hz : ‖genAdvFilter input Gamma i‖ = 0
  · rw [hz,ENNReal.ofReal_zero]
    have hnum : ENNReal.ofReal (alpha i)*ENNReal.ofReal ‖Gamma‖ ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (ha i)) (ENNReal.ofReal_ne_zero_iff.mpr hnp)
    rw [ENNReal.div_zero hnum]
    exact le_top
  have hp : 0 < ‖genAdvFilter input Gamma i‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  rw [← ENNReal.ofReal_mul (ha i).le,← ENNReal.ofReal_div_of_pos hp]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hp).mpr
  nlinarith [hG.2.2.2 i]
end
noncomputable section

/-- The real matrix equal to one on the two ordered edges joining `a` and `b`, and zero
elsewhere. -/
def adversaryEdge (a b : X) : Matrix X X ℝ :=
  fun x y => if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then 1 else 0
end
noncomputable section
omit [Fintype X] [Fintype K] [DecidableEq K] in

/-- Inputs with different Boolean outputs determine a nonzero symmetric nonnegative edge matrix
vanishing on equal-output pairs. -/
theorem adversaryEdge_source (f : X → Bool) (a b : X) (hab : f a ≠ f b) :
    (adversaryEdge a b).IsSymm ∧ (∀ x y, 0 ≤ adversaryEdge a b x y) ∧
      (∀ x y, f x = f y → adversaryEdge a b x y = 0) ∧ adversaryEdge a b ≠ 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · ext x y
    change (if (y=a ∧ x=b) ∨ (y=b ∧ x=a) then (1 : ℝ) else 0) =
      (if (x=a ∧ y=b) ∨ (x=b ∧ y=a) then 1 else 0)
    congr 1
    apply propext
    tauto
  · intro x y
    unfold adversaryEdge
    split_ifs <;> norm_num
  · intro x y hxy
    by_cases he : (x=a ∧ y=b) ∨ (x=b ∧ y=a)
    · rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (hab hxy).elim
      · exact (hab hxy.symm).elim
    · simp [adversaryEdge,he]
  · intro hz
    have h := congrArg (fun G : Matrix X X ℝ => G a b) hz
    simp [adversaryEdge] at h
end
noncomputable section

/-- For a nonconstant function with observable outputs and positive costs, a nonzero feasible
matrix attains `advAlphaR`, and this value equals its norm. -/
theorem advAlphaR_optimal_exists_of_observable
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f) (hnc : ∃ a b, f a ≠ f b) :
    ∃ Gamma : Matrix X X ℝ, CostAdversaryFeasible input f alpha Gamma ∧ Gamma ≠ 0 ∧
      advAlphaWitnessR input alpha Gamma = advAlphaR input f alpha ∧
      advAlphaR input f alpha = ENNReal.ofReal ‖Gamma‖ := by
  obtain ⟨Gamma,hG,hmax⟩ := costAdversary_norm_max_exists input f alpha (fun i => (ha i).le) hobs
  obtain ⟨a,b,hab⟩ := hnc
  have hedge := adversaryEdge_source f a b hab
  obtain ⟨H,hH,hHne,_⟩ := costAdversary_normalize input f alpha ha hobs (adversaryEdge a b)
    hedge.1 hedge.2.1 hedge.2.2.1 hedge.2.2.2
  have hpos : 0 < ‖Gamma‖ := (norm_pos_iff.mpr hHne).trans_le (hmax H hH)
  have hGne : Gamma ≠ 0 := norm_pos_iff.mp hpos
  have hupper : advAlphaR input f alpha ≤ ENNReal.ofReal ‖Gamma‖ := by
    unfold advAlphaR
    apply iSup_le
    intro G
    obtain ⟨N,hN,_,hb⟩ := costAdversary_normalize input f alpha ha hobs G.val G.property.1
      G.property.2.1 G.property.2.2.1 G.property.2.2.2
    exact hb.trans (ENNReal.ofReal_le_ofReal (hmax N hN))
  have hsource : advAlphaWitnessR input alpha Gamma ≤ advAlphaR input f alpha :=
    le_iSup_of_le ⟨Gamma,hG.1,hG.2.1,hG.2.2.1,hGne⟩ le_rfl
  have hlower := costAdversary_norm_le_witness input f alpha ha Gamma hG
  have heq : advAlphaR input f alpha = ENNReal.ofReal ‖Gamma‖ :=
    le_antisymm hupper (hlower.trans hsource)
  refine ⟨Gamma,hG,hGne,?_,heq⟩
  exact le_antisymm hsource (heq.symm ▸ hlower)
end
noncomputable section

/-- An injective Boolean input encoding makes every Boolean output function observable. -/
theorem outputObservable_of_injective {A J : Type} (input : A → J → Bool) (f : A → Bool)
    (hi : Function.Injective input) : OutputObservable input f := by
  intro x y hxy
  by_contra h
  have he : input x = input y := by
    funext i
    exact not_not.mp (not_exists.mp h i)
  exact hxy (congrArg f (hi he))
end
noncomputable section

/-- For a nonconstant function on a domain of Boolean words with positive costs, a nonzero
feasible matrix attains the real nonnegative adversary value as its norm. -/
theorem advAlphaR_word_optimal_exists (D : Set (K → Bool)) (f : D → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ a b, f a ≠ f b) :
    ∃ Gamma : Matrix D D ℝ, CostAdversaryFeasible (fun x : D => x.val) f alpha Gamma ∧ Gamma ≠ 0 ∧
      advAlphaWitnessR (fun x : D => x.val) alpha Gamma = advAlphaR (fun x : D => x.val) f alpha ∧
      advAlphaR (fun x : D => x.val) f alpha = ENNReal.ofReal ‖Gamma‖ := by
  exact advAlphaR_optimal_exists_of_observable (fun x : D => x.val) f alpha ha
    (outputObservable_of_injective _ _ Subtype.val_injective) hnc
end
noncomputable section
omit [Fintype X] [Fintype K] [DecidableEq K] in

/-- If two encoded inputs agree at every coordinate, all coordinate filters of their edge matrix
vanish. -/
theorem adversaryEdge_filter_zero (input : X → K → Bool) (a b : X)
    (hinput : ∀ i, input a i = input b i) (i : K) :
    genAdvFilter input (adversaryEdge a b) i = 0 := by
  ext x y
  change (if input x i ≠ input y i then
    (if (x=a ∧ y=b) ∨ (x=b ∧ y=a) then (1 : ℝ) else 0) else 0) = 0
  by_cases h : (x=a ∧ y=b) ∨ (x=b ∧ y=a)
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp only [hinput i,ne_eq,not_true_eq_false,↓reduceIte]
    · simp only [hinput i,ne_eq,not_true_eq_false,↓reduceIte]
  · rw [if_neg h]
    split_ifs <;> rfl
end
noncomputable section

/-- With positive costs, identically encoded inputs with different outputs yield an edge witness
of infinite value and force `advAlphaR` to be infinite. -/
theorem advAlphaR_infinite_of_collision (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (a b : X) (hab : f a ≠ f b)
    (hinput : ∀ i, input a i = input b i) :
    advAlphaWitnessR input alpha (adversaryEdge a b) = ⊤ ∧ advAlphaR input f alpha = ⊤ := by
  have hs := adversaryEdge_source f a b hab
  have hn := norm_pos_iff.mpr hs.2.2.2
  have hw : advAlphaWitnessR input alpha (adversaryEdge a b) = ⊤ := by
    unfold advAlphaWitnessR
    have hi (i : K) : ENNReal.ofReal (alpha i)*ENNReal.ofReal ‖adversaryEdge a b‖ /
        ENNReal.ofReal ‖genAdvFilter input (adversaryEdge a b) i‖ = ⊤ := by
      rw [adversaryEdge_filter_zero input a b hinput,norm_zero,ENNReal.ofReal_zero]
      exact ENNReal.div_zero (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (ha i))
        (ENNReal.ofReal_ne_zero_iff.mpr hn))
    simp only [hi]
    exact le_antisymm le_top (le_iInf (fun _ => le_rfl))
  refine ⟨hw,top_unique ?_⟩
  rw [← hw]
  exact le_iSup_of_le ⟨adversaryEdge a b,hs⟩ le_rfl
end
noncomputable section

/-- For a nonconstant Boolean function with positive costs, a nonzero symmetric nonnegative
matrix supported on different outputs attains the weighted real adversary value. -/
theorem advAlphaR_optimal_exists (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ a b, f a ≠ f b) :
    ∃ Gamma : Matrix X X ℝ, Gamma.IsSymm ∧ (∀ x y, 0 ≤ Gamma x y) ∧
      (∀ x y, f x = f y → Gamma x y = 0) ∧ Gamma ≠ 0 ∧
      advAlphaWitnessR input alpha Gamma = advAlphaR input f alpha := by
  by_cases hobs : OutputObservable input f
  · obtain ⟨Gamma,hG,hne,he,_⟩ := advAlphaR_optimal_exists_of_observable input f alpha ha hobs hnc
    exact ⟨Gamma,hG.1,hG.2.1,hG.2.2.1,hne,he⟩
  · have hex : ∃ a b, f a ≠ f b ∧ ∀ i, input a i = input b i := by
      unfold OutputObservable at hobs
      push Not at hobs
      exact hobs
    obtain ⟨a,b,hab,hinput⟩ := hex
    have hs := adversaryEdge_source f a b hab
    have hi := advAlphaR_infinite_of_collision input f alpha ha a b hab hinput
    exact ⟨adversaryEdge a b,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hi.1.trans hi.2.symm⟩
end
noncomputable section

/-- For a nonconstant function with positive costs and nonempty coordinate type, both an optimal
nonzero symmetric nonnegative adversary matrix and an optimal minimax probability family
exist. -/
theorem adversary_minimax_optimizers_exist [Nonempty K]
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ a b, f a ≠ f b) :
    ∃ (Gamma : Matrix X X ℝ) (p : X → K → ℝ),
      (Gamma.IsSymm ∧ (∀ x y, 0 ≤ Gamma x y) ∧ (∀ x y, f x = f y → Gamma x y = 0) ∧
        Gamma ≠ 0 ∧ advAlphaWitnessR input alpha Gamma = advAlphaR input f alpha) ∧
      IsMinimaxOptimal input f alpha p := by
  obtain ⟨Gamma,hG⟩ := advAlphaR_optimal_exists input f alpha ha hnc
  obtain ⟨p,hp⟩ := minimax_optimal_exists input f alpha hnc
  exact ⟨Gamma,p,hG,hp⟩
end
noncomputable section

/-- For a nonconstant function on a domain of Boolean words with positive costs, optimal
nonnegative adversary and minimax witnesses exist simultaneously. -/
theorem adversary_minimax_word_optimizers_exist (D : Set (K → Bool)) (f : D → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ a b, f a ≠ f b) :
    ∃ (Gamma : Matrix D D ℝ) (p : D → K → ℝ),
      (Gamma.IsSymm ∧ (∀ x y, 0 ≤ Gamma x y) ∧ (∀ x y, f x = f y → Gamma x y = 0) ∧
        Gamma ≠ 0 ∧ advAlphaWitnessR (fun x : D => x.val) alpha Gamma =
          advAlphaR (fun x : D => x.val) f alpha) ∧
      IsMinimaxOptimal (fun x : D => x.val) f alpha p := by
  have hobs := outputObservable_of_injective (fun x : D => x.val) f Subtype.val_injective
  obtain ⟨a,b,hab⟩ := hnc
  obtain ⟨i,_⟩ := hobs a b hab
  letI : Nonempty K := ⟨i⟩
  exact adversary_minimax_optimizers_exist (fun x : D => x.val) f alpha ha ⟨a,b,hab⟩
end
noncomputable section

/-- For a nonconstant function with positive costs, the real nonnegative adversary value is
finite exactly when outputs are observable from the input encoding. -/
theorem advAlphaR_finite_iff_observable (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hnc : ∃ a b, f a ≠ f b) :
    advAlphaR input f alpha < ⊤ ↔ OutputObservable input f := by
  constructor
  · intro hfin
    by_contra hobs
    unfold OutputObservable at hobs
    push Not at hobs
    obtain ⟨a,b,hab,hinput⟩ := hobs
    exact hfin.ne (advAlphaR_infinite_of_collision input f alpha ha a b hab hinput).2
  · intro hobs
    obtain ⟨Gamma,_,_,_,he⟩ := advAlphaR_optimal_exists_of_observable input f alpha ha hobs hnc
    rw [he]
    exact ENNReal.ofReal_lt_top
end
noncomputable section

/-- For a nonconstant function with observable outputs and positive costs, the real nonnegative
adversary value is bounded by the minimax value. -/
theorem advAlphaR_le_minimax_of_observable (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i, 0 < alpha i) (hobs : OutputObservable input f) (hnc : ∃ a b, f a ≠ f b) :
    advAlphaR input f alpha ≤ minimaxAlpha input f alpha := by
  obtain ⟨a,b,hab⟩ := hnc
  obtain ⟨i0,_⟩ := hobs a b hab
  letI : Nonempty K := ⟨i0⟩
  obtain ⟨Gamma,hG,hne,_,he⟩ :=
      advAlphaR_optimal_exists_of_observable input f alpha ha hobs ⟨a,b,hab⟩
  have hpos := norm_pos_iff.mpr hne
  rw [he,minimaxAlpha,ENNReal.le_inv_iff_mul_le,ENNReal.mul_iSup]
  apply iSup_le
  intro p
  obtain ⟨x,y,hxy,hweak⟩ := advNonneg_witness_le_minimaxTerm input f alpha ha Gamma hG.1 hG.2.1
    hG.2.2.1 hpos p.val p.property.1 p.property.2
  have hr : (⨆ i, ‖advFilterR input Gamma i‖/(‖Gamma‖*alpha i)) ≤ 1/‖Gamma‖ := by
    apply ciSup_le
    intro i
    apply (div_le_iff₀ (mul_pos hpos (ha i))).mpr
    calc
      ‖advFilterR input Gamma i‖ ≤ alpha i := hG.2.2.2 i
      _ = (1/‖Gamma‖)*(‖Gamma‖*alpha i) := by field_simp
  have hp : (⨅ xy : {xy : X × X // f xy.1 ≠ f xy.2},
      advMinimaxTerm input alpha p.val xy.val.1 xy.val.2) ≤ 1/‖Gamma‖ :=
    (ciInf_le (Set.finite_range _).bddBelow ⟨(x,y),hxy⟩).trans (hweak.trans hr)
  calc
    _ ≤ ENNReal.ofReal ‖Gamma‖ * ENNReal.ofReal (1/‖Gamma‖) :=
      mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hp) bot_le
    _ = ENNReal.ofReal (‖Gamma‖*(1/‖Gamma‖)) := (ENNReal.ofReal_mul (norm_nonneg Gamma)).symm
    _ = 1 := by
      rw [mul_one_div_cancel hpos.ne']
      exact ENNReal.ofReal_one
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
