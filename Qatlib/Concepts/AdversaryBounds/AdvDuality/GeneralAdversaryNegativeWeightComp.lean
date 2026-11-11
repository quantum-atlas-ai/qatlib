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
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversarySourceOptimizers
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryIteration

/-!
# Cost-weighted Hermitian adversary composition

Proves compactness and existence of optimal Hermitian adversary matrices with strictly positive
coordinate costs when outputs are observable from the input encoding.
`CostHermitianAdversaryFeasible` supplies the normalized feasible set used to construct these
optimizers.

The module combines optimal outer and inner witnesses to prove a negative-weight composition
lower bound in the framework of [HoyerLeeSpalek2007]. It also proves a composition endpoint
under nonconstancy and finiteness hypotheses and refutes the unrestricted `clause18Prop` using
constant blocks.

## Main statements

* `advAlphaPm_optimal_exists_of_observable`: existence of an optimal nonzero feasible Hermitian
  witness.
* `source_optimized_adversary_composition`: construct optimal outer and inner matrices with a
  composed witness bound.
* `source_negative_adversary_composition_lower`: the cost-weighted negative-weight composition
  lower bound.
* `clause18_raw_constant_block_counterexample`: failure of the unrestricted composition
  proposition.

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
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.QueryWordCore.QueryMachinery

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
variable {X K : Type} [Fintype X] [Fintype K] [DecidableEq K]
variable [DecidableEq X]
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace
open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
set_option maxRecDepth 100000 in
noncomputable section

/-- A Hermitian matrix vanishing on equal Boolean outputs whose coordinate filter norms are
bounded by the specified real costs. -/
def CostHermitianAdversaryFeasible (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (G : Matrix X X ℂ) : Prop :=
  G.IsHermitian ∧ (∀ x y,f x=f y → G x y=0) ∧
    (∀ i,‖genAdvFilter input G i‖≤alpha i)
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- The magnitude of each entry of a complex matrix is bounded by its operator norm. -/
theorem complex_operator_entry_bound (M : Matrix X X ℂ) (x y : X) : ‖M x y‖≤‖M‖ := by
  let v : EuclideanSpace ℂ X := PiLp.single 2 y 1
  let w : EuclideanSpace ℂ X := (EuclideanSpace.equiv X ℂ).symm (M *ᵥ v)
  have he : w x=M x y := by simp [w,v]
  have hv : ‖v‖=1 := by simp [v,PiLp.norm_single]
  calc
    ‖M x y‖=‖w x‖ := by rw [he]
    _ ≤ ‖w‖ := PiLp.norm_apply_le w x
    _ ≤ ‖M‖*‖v‖ := Matrix.l2_opNorm_mulVec M v
    _ = ‖M‖ := by rw [hv,mul_one]
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- The zero matrix is a feasible cost-weighted Hermitian adversary when all costs are
nonnegative. -/
theorem costHermitianAdversary_zero (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0≤alpha i) : CostHermitianAdversaryFeasible input f alpha 0 := by
  refine ⟨by simp,by simp,?_⟩
  intro i
  have hz : genAdvFilter input (0 : Matrix X X ℂ) i=0 := by
    ext x y
    change (if input x i≠input y i then (0 : ℂ) else 0)=0
    split_ifs <;> rfl
  rw [hz,norm_zero]
  exact ha i
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- The set of feasible cost-weighted Hermitian adversary matrices is closed. -/
theorem costHermitianAdversary_closed (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ) :
    IsClosed {G : Matrix X X ℂ | CostHermitianAdversaryFeasible input f alpha G} := by
  have hc (i : K) : Continuous (fun G : Matrix X X ℂ => genAdvFilter input G i) := by
    apply continuous_pi
    intro x
    apply continuous_pi
    intro y
    change Continuous (fun G : Matrix X X ℂ => if input x i≠input y i then G x y else 0)
    by_cases h : input x i≠input y i
    · simpa only [if_pos h] using! (show Continuous (fun G : Matrix X X ℂ => G x y) by fun_prop)
    · simpa only [if_neg h] using! (continuous_const : Continuous (fun _ : Matrix X X ℂ => (0 : ℂ)))
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop : Continuous (fun G : Matrix X X ℂ => Gᴴ)) continuous_id
  apply IsClosed.inter
  · have hs (x y : X) : IsClosed {G : Matrix X X ℂ | f x=f y → G x y=0} := by
      by_cases h : f x=f y
      · simpa only [h,forall_const] using! isClosed_eq
          (show Continuous (fun G : Matrix X X ℂ => G x y) by fun_prop) continuous_const
      · simp [h]
    convert! isClosed_iInter (fun x => isClosed_iInter (hs x)) using 1
    ext G
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
  · convert! isClosed_iInter (fun i => isClosed_le (continuous_norm.comp (hc i))
      (continuous_const : Continuous (fun _ : Matrix X X ℂ => alpha i))) using 1
    ext G
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    rfl
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs and nonnegative costs, every entry of a feasible Hermitian adversary
is bounded in magnitude by the sum of the costs. -/
theorem costHermitianAdversary_entry_bound (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0≤alpha i) (hobs : OutputObservable input f)
    (G : Matrix X X ℂ) (hG : CostHermitianAdversaryFeasible input f alpha G) (x y : X) :
    ‖G x y‖≤∑ i,alpha i := by
  by_cases hf : f x=f y
  · rw [hG.2.1 x y hf,norm_zero]
    exact Finset.sum_nonneg (fun i _ => ha i)
  · obtain ⟨i,hi⟩ := hobs x y hf
    have hh := (complex_operator_entry_bound (genAdvFilter input G i) x y).trans (hG.2.2 i)
    change ‖if input x i≠input y i then G x y else 0‖≤alpha i at hh
    rw [if_pos hi] at hh
    exact hh.trans (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs and nonnegative costs, the feasible cost-weighted Hermitian adversary
set is compact. -/
theorem costHermitianAdversary_compact (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0≤alpha i) (hobs : OutputObservable input f) :
    IsCompact {G : Matrix X X ℂ | CostHermitianAdversaryFeasible input f alpha G} := by
  let R := ∑ i,alpha i
  let B : Set (Matrix X X ℂ) := Set.pi Set.univ
    (fun _ : X => Set.pi Set.univ (fun _ : X => Metric.closedBall (0 : ℂ) R))
  have hb : IsCompact B :=
      isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 R))
  apply hb.of_isClosed_subset (costHermitianAdversary_closed input f alpha)
  intro G hG
  change ∀ x∈Set.univ,∀ y∈Set.univ,G x y∈Metric.closedBall (0 : ℂ) R
  intro x _ y _
  simpa only [Metric.mem_closedBall,dist_zero_right] using!
      costHermitianAdversary_entry_bound input f alpha ha hobs G hG x y
end
noncomputable section
omit [DecidableEq K] in

/-- For observable outputs and nonnegative costs, a feasible Hermitian adversary matrix attains
the maximum operator norm. -/
theorem costHermitianAdversary_norm_max_exists (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0≤alpha i) (hobs : OutputObservable input f) :
    ∃ G : Matrix X X ℂ,CostHermitianAdversaryFeasible input f alpha G ∧
      ∀ H,CostHermitianAdversaryFeasible input f alpha H → ‖H‖≤‖G‖ := by
  exact (costHermitianAdversary_compact input f alpha ha hobs).exists_isMaxOn
    ⟨0,costHermitianAdversary_zero input f alpha ha⟩ continuous_norm.continuousOn
end
noncomputable section
omit [Fintype K] [DecidableEq K] in

/-- For observable outputs, a nonzero complex matrix vanishing on equal outputs has a coordinate
filter with positive norm. -/
theorem nonzero_complex_adversary_filter (input : X → K → Bool) (f : X → Bool)
    (hobs : OutputObservable input f) (G : Matrix X X ℂ)
    (hz : ∀ x y,f x=f y → G x y=0) (hne : G≠0) : ∃ i,0<‖genAdvFilter input G i‖ := by
  obtain ⟨x,y,hxy⟩ : ∃ x y,G x y≠0 := by
    by_contra h
    apply hne
    ext x y
    exact not_not.mp (not_exists.mp (not_exists.mp h x) y)
  have hf : f x≠f y := fun he => hxy (hz x y he)
  obtain ⟨i,hi⟩ := hobs x y hf
  refine ⟨i,norm_pos_iff.mpr ?_⟩
  intro he
  have hh := congrArg (fun H : Matrix X X ℂ => H x y) he
  change (if input x i≠input y i then G x y else 0)=0 at hh
  rw [if_pos hi] at hh
  exact hxy hh
end
noncomputable section

/-- With positive costs and observable outputs, a nonzero Hermitian witness vanishing on equal
outputs can be replaced by a nonzero feasible matrix whose norm bounds its weighted witness
value. -/
theorem costHermitianAdversary_normalize (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0<alpha i) (hobs : OutputObservable input f)
    (G : Matrix X X ℂ) (hG : G.IsHermitian) (hz : ∀ x y,f x=f y → G x y=0) (hne : G≠0) :
    ∃ H : Matrix X X ℂ,CostHermitianAdversaryFeasible input f alpha H ∧ H≠0 ∧
      advAlphaPmWitness input (fun i => ENNReal.ofReal (alpha i)) G≤ENNReal.ofReal ‖H‖ := by
  obtain ⟨i0,hi0⟩ := nonzero_complex_adversary_filter input f hobs G hz hne
  letI : Nonempty K := ⟨i0⟩
  let r : K → ℝ := fun i => ‖genAdvFilter input G i‖/alpha i
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hr : 0<r j := (div_pos hi0 (ha i0)).trans_le (hj i0 (Finset.mem_univ i0))
  have hjpos : 0<‖genAdvFilter input G j‖ := by
    by_contra h
    have h0 := le_antisymm (not_lt.mp h) (norm_nonneg (genAdvFilter input G j))
    simp only [r,h0,zero_div] at hr
    exact (lt_irrefl 0) hr
  let c := alpha j/‖genAdvFilter input G j‖
  have hc : 0<c := div_pos (ha j) hjpos
  have hnorm : ‖c • G‖=c*‖G‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
  refine ⟨c • G,?_,?_,?_⟩
  · refine ⟨hG.smul (show IsSelfAdjoint c by simp [IsSelfAdjoint]),?_,?_⟩
    · intro x y hf
      change c • G x y=0
      rw [hz x y hf,smul_zero]
    · intro i
      rw [genAdvFilter_complex_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
      have hratio := (div_le_div_iff₀ (ha i) (ha j)).mp (hj i (Finset.mem_univ i))
      dsimp only [c]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hjpos).mpr
      nlinarith
  · intro h0
    have hn := norm_pos_iff.mpr hne
    have hh := congrArg (fun H : Matrix X X ℂ => ‖H‖) h0
    change ‖c • G‖=‖(0 : Matrix X X ℂ)‖ at hh
    rw [hnorm,norm_zero] at hh
    nlinarith
  · calc
      advAlphaPmWitness input (fun i => ENNReal.ofReal (alpha i)) G ≤
          ENNReal.ofReal (alpha j)*ENNReal.ofReal ‖G‖/ENNReal.ofReal ‖genAdvFilter input G j‖ := iInf_le _ j
      _ = ENNReal.ofReal (c*‖G‖) := by
        rw [← ENNReal.ofReal_mul (ha j).le,← ENNReal.ofReal_div_of_pos hjpos]
        congr 1
        dsimp only [c]
        ring
      _ = ENNReal.ofReal ‖c • G‖ := by rw [hnorm]
end
noncomputable section

/-- With positive costs, the norm of a feasible Hermitian adversary is bounded by its weighted
witness value. -/
theorem costHermitianAdversary_norm_le_witness (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0<alpha i) (G : Matrix X X ℂ) (hG : CostHermitianAdversaryFeasible input f alpha G) :
    ENNReal.ofReal ‖G‖≤advAlphaPmWitness input (fun i => ENNReal.ofReal (alpha i)) G := by
  apply le_iInf
  intro i
  by_cases hn : ‖G‖=0
  · simp [hn]
  have hnp : 0<‖G‖ := lt_of_le_of_ne (norm_nonneg G) (Ne.symm hn)
  by_cases hz : ‖genAdvFilter input G i‖=0
  · rw [hz,ENNReal.ofReal_zero]
    have hnum : ENNReal.ofReal (alpha i)*ENNReal.ofReal ‖G‖≠0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (ha i)) (ENNReal.ofReal_ne_zero_iff.mpr hnp)
    rw [ENNReal.div_zero hnum]
    exact le_top
  have hp : 0<‖genAdvFilter input G i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  rw [← ENNReal.ofReal_mul (ha i).le,← ENNReal.ofReal_div_of_pos hp]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hp).mpr
  nlinarith [hG.2.2 i]
end
noncomputable section

/-- The complex matrix equal to one on the two ordered edges joining `a` and `b`, and zero
elsewhere. -/
def complexAdversaryEdge (a b : X) : Matrix X X ℂ :=
  fun x y => if (x=a ∧ y=b) ∨ (x=b ∧ y=a) then 1 else 0
end
noncomputable section
omit [Fintype X] [Fintype K] [DecidableEq K] in

/-- Inputs with different outputs determine a nonzero Hermitian edge matrix vanishing on
equal-output pairs. -/
theorem complexAdversaryEdge_source (f : X → Bool) (a b : X) (hab : f a≠f b) :
    (complexAdversaryEdge a b).IsHermitian ∧
      (∀ x y,f x=f y → complexAdversaryEdge a b x y=0) ∧ complexAdversaryEdge a b≠0 := by
  refine ⟨?_,?_,?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    change star (if (y=a ∧ x=b) ∨ (y=b ∧ x=a) then (1 : ℂ) else 0)=
      if (x=a ∧ y=b) ∨ (x=b ∧ y=a) then 1 else 0
    by_cases h : (x=a ∧ y=b) ∨ (x=b ∧ y=a)
    · have h' : (y=a ∧ x=b) ∨ (y=b ∧ x=a) := by tauto
      simp only [if_pos h,if_pos h',star_one]
    · have h' : ¬((y=a ∧ x=b) ∨ (y=b ∧ x=a)) := by tauto
      simp only [if_neg h,if_neg h',star_zero]
  · intro x y hxy
    by_cases he : (x=a ∧ y=b) ∨ (x=b ∧ y=a)
    · rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (hab hxy).elim
      · exact (hab hxy.symm).elim
    · simp [complexAdversaryEdge,he]
  · intro hz
    have h := congrArg (fun G : Matrix X X ℂ => G a b) hz
    simp [complexAdversaryEdge] at h
end
noncomputable section

/-- For a nonconstant function with observable outputs and positive costs, a nonzero feasible
Hermitian matrix attains the weighted negative adversary value, which equals its norm. -/
theorem advAlphaPm_optimal_exists_of_observable
    (input : X → K → Bool) (f : X → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0<alpha i) (hobs : OutputObservable input f) (hnc : ∃ a b,f a≠f b) :
    ∃ G : Matrix X X ℂ,CostHermitianAdversaryFeasible input f alpha G ∧ G≠0 ∧
      advAlphaPmWitness input (fun i => ENNReal.ofReal (alpha i)) G=
        advAlphaPmENN input f (fun i => ENNReal.ofReal (alpha i)) ∧
      advAlphaPmENN input f (fun i => ENNReal.ofReal (alpha i))=ENNReal.ofReal ‖G‖ := by
  obtain ⟨G,hG,hmax⟩ :=
      costHermitianAdversary_norm_max_exists input f alpha (fun i => (ha i).le) hobs
  obtain ⟨a,b,hab⟩ := hnc
  have hedge := complexAdversaryEdge_source f a b hab
  obtain ⟨H,hH,hHne,_⟩ := costHermitianAdversary_normalize input f alpha ha hobs
    (complexAdversaryEdge a b) hedge.1 hedge.2.1 hedge.2.2
  have hpos : 0<‖G‖ := (norm_pos_iff.mpr hHne).trans_le (hmax H hH)
  have hGne : G≠0 := norm_pos_iff.mp hpos
  have hupper : advAlphaPmENN input f (fun i => ENNReal.ofReal (alpha i))≤ENNReal.ofReal ‖G‖ := by
    unfold advAlphaPmENN
    apply iSup_le
    intro A
    obtain ⟨N,hN,_,hb⟩ := costHermitianAdversary_normalize input f alpha ha hobs A.val
      A.property.1 A.property.2.1 A.property.2.2
    exact hb.trans (ENNReal.ofReal_le_ofReal (hmax N hN))
  have hsource : advAlphaPmWitness input (fun i => ENNReal.ofReal (alpha i)) G≤
      advAlphaPmENN input f (fun i => ENNReal.ofReal (alpha i)) :=
    le_iSup_of_le ⟨G,hG.1,hG.2.1,hGne⟩ le_rfl
  have hlower := costHermitianAdversary_norm_le_witness input f alpha ha G hG
  have heq : advAlphaPmENN input f (fun i => ENNReal.ofReal (alpha i))=ENNReal.ofReal ‖G‖ :=
    le_antisymm hupper (hlower.trans hsource)
  exact ⟨G,hG,hGne,le_antisymm hsource (heq.symm ▸ hlower),heq⟩
end
noncomputable section

/-- For a nonconstant function on a domain of Boolean words with positive costs, a nonzero
feasible Hermitian matrix attains the weighted negative adversary value as its norm. -/
theorem advAlphaPm_word_optimal_exists (D : Set (K → Bool)) (f : D → Bool) (alpha : K → ℝ)
    (ha : ∀ i,0<alpha i) (hnc : ∃ a b,f a≠f b) :
    ∃ G : Matrix D D ℂ,CostHermitianAdversaryFeasible (fun x : D => x.val) f alpha G ∧ G≠0 ∧
      advAlphaPmWitness (fun x : D => x.val) (fun i => ENNReal.ofReal (alpha i)) G=
        advAlphaPmENN (fun x : D => x.val) f (fun i => ENNReal.ofReal (alpha i)) ∧
      advAlphaPmENN (fun x : D => x.val) f (fun i => ENNReal.ofReal (alpha i))=ENNReal.ofReal ‖G‖ :=
  advAlphaPm_optimal_exists_of_observable _ f alpha ha (outputObservable_of_injective _ _ Subtype.val_injective) hnc
end
noncomputable section

/-- Nonzero feasible outer and inner Hermitian matrices with positive coordinate costs generate
a composition witness whose weighted value is at least the outer matrix norm. -/
theorem generated_cost_composition {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i,Fintype (Y i)] [∀ i,DecidableEq (Y i)]
    (gin : ∀ i,Y i → Fin (n i) → Bool) (g : ∀ i,Y i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (A : Matrix (Fin k → Bool) (Fin k → Bool) ℂ) (B : ∀ i,Matrix (Y i) (Y i) ℂ)
    (ha : ∀ c,0<alpha c)
    (hA : CostHermitianAdversaryFeasible (fun u : Fin k → Bool => u) f (fun i => ‖B i‖) A)
    (hAN : A≠0)
    (hB : ∀ i,CostHermitianAdversaryFeasible (gin i) (g i) (fun j => alpha ⟨i,j⟩) (B i))
    (hBN : ∀ i,B i≠0) :
    GeneratedCompositionWitness g f A B ∧
      ENNReal.ofReal ‖A‖≤advAlphaPmWitness (composedInput gin) (fun c => ENNReal.ofReal (alpha c))
        (composedAdversary g f A B) := by
  let C := composedAdversary g f A B
  let P : ℝ := ∏ i,‖B i‖
  have hBP (i : Fin k) : 0<‖B i‖ := norm_pos_iff.mpr (hBN i)
  have hP : 0<P := Finset.prod_pos (fun i _ => hBP i)
  have hAP : 0<‖A‖ := norm_pos_iff.mpr hAN
  have hN : ‖C‖=‖A‖*P :=
      weightedAdvGamma_norm_eq g f A B hA.1 (fun i => (hB i).1) (fun i => (hB i).2.1)
  have hCN : C≠0 := norm_pos_iff.mp (by rw [hN]; exact mul_pos hAP hP)
  have hC : C.IsHermitian := weightedAdvGamma_isHermitian g f A B hA.1 (fun i => (hB i).1)
  have hzC : ∀ x y,composedFunction g f x=composedFunction g f y → C x y=0 :=
    weightedAdvGamma_same_output_zero g f A B hA.2.1
  refine ⟨⟨hA.1,hA.2.1,hAN,(fun i => (hB i).1),(fun i => (hB i).2.1),hBN,hC,hzC,hCN⟩,?_⟩
  apply le_iInf
  intro c
  obtain ⟨p,q⟩ := c
  have hfilter : ‖genAdvFilter (composedInput gin) C ⟨p,q⟩‖≤alpha ⟨p,q⟩*P := by
    have hh := weightedAdvGamma_filter_norm_eq g f A B gin hA.1 (fun i => (hB i).1)
      hA.2.1 (fun i => (hB i).2.1) p q
    change ‖weightedAdvFilter (weightedAdvInput gin) (weightedAdvGamma g f A B) ⟨p,q⟩‖≤_
    rw [hh]
    have hp : ‖B p‖*(∏ i ∈ Finset.univ.erase p,‖B i‖)=P :=
      Finset.mul_prod_erase Finset.univ (fun i => ‖B i‖) (Finset.mem_univ p)
    calc
      ‖advFilter id A p‖*‖advFilter (gin p) (B p) q‖*(∏ i ∈ Finset.univ.erase p,‖B i‖) ≤
          (‖B p‖*alpha ⟨p,q⟩)*(∏ i ∈ Finset.univ.erase p,‖B i‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hA.2.2 p) ((hB p).2.2 q) (norm_nonneg _) (norm_nonneg _))
          (Finset.prod_nonneg (fun i _ => norm_nonneg (B i)))
      _ = alpha ⟨p,q⟩*P := by rw [mul_assoc,mul_comm ‖B p‖,mul_assoc,← hp]; ring
  by_cases hz : ‖genAdvFilter (composedInput gin) C ⟨p,q⟩‖=0
  · rw [hz,ENNReal.ofReal_zero]
    have hn : ENNReal.ofReal (alpha ⟨p,q⟩)*ENNReal.ofReal ‖C‖≠0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (ha ⟨p,q⟩)) (ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hCN))
    rw [ENNReal.div_zero hn]
    exact le_top
  have hf : 0<‖genAdvFilter (composedInput gin) C ⟨p,q⟩‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  rw [← ENNReal.ofReal_mul (ha ⟨p,q⟩).le,← ENNReal.ofReal_div_of_pos hf]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hf).mpr
  rw [hN]
  have hh := mul_le_mul_of_nonneg_left hfilter hAP.le
  nlinarith
end
noncomputable section

/-- For nonconstant outer and inner functions, observable inner outputs, and positive costs,
optimal outer and inner negative adversary matrices exist and their composition has witness
value at least the outer optimum. -/
theorem source_optimized_adversary_composition {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i,Fintype (Y i)] [∀ i,DecidableEq (Y i)]
    (gin : ∀ i,Y i → Fin (n i) → Bool) (g : ∀ i,Y i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (ha : ∀ c,0<alpha c) (hfn : ∃ u v,f u≠f v)
    (hgn : ∀ i,∃ a b,g i a≠g i b) (hobs : ∀ i,OutputObservable (gin i) (g i)) :
    ∃ (A : Matrix (Fin k → Bool) (Fin k → Bool) ℂ) (B : ∀ i,Matrix (Y i) (Y i) ℂ),
      GeneratedCompositionWitness g f A B ∧
      advAlphaPmWitness (fun u : Fin k → Bool => u) (blockCostsPm gin g alpha) A=
        advAlphaPmENN (fun u : Fin k → Bool => u) f (blockCostsPm gin g alpha) ∧
      (∀ i,advAlphaPmWitness (gin i) (fun j => ENNReal.ofReal (alpha ⟨i,j⟩)) (B i)=
        advAlphaPmENN (gin i) (g i) (fun j => ENNReal.ofReal (alpha ⟨i,j⟩))) ∧
      advAlphaPmWitness (fun u : Fin k → Bool => u) (blockCostsPm gin g alpha) A≤
        advAlphaPmWitness (composedInput gin) (fun c => ENNReal.ofReal (alpha c)) (composedAdversary g f A B) := by
  choose B hB hBN hBO hBV using (fun i => advAlphaPm_optimal_exists_of_observable
    (gin i) (g i) (fun j => alpha ⟨i,j⟩) (fun j => ha ⟨i,j⟩) (hobs i) (hgn i))
  have hb (i : Fin k) : 0<‖B i‖ := norm_pos_iff.mpr (hBN i)
  obtain ⟨A,hA,hAN,hAO,hAV⟩ := advAlphaPm_optimal_exists_of_observable
    (fun u : Fin k → Bool => u) f (fun i => ‖B i‖) hb (outputObservable_of_injective _ _ Function.injective_id) hfn
  have hcost : blockCostsPm gin g alpha=(fun i => ENNReal.ofReal ‖B i‖) := by
    funext i
    exact hBV i
  have hgen := generated_cost_composition gin g f alpha A B ha hA hAN hB hBN
  refine ⟨A,B,hgen.1,?_,hBO,?_⟩
  · rw [hcost]
    exact hAO
  · rw [hcost,hAO,hAV]
    exact hgen.2
end
noncomputable section

/-- A Boolean-valued function taking two different values is surjective. -/
theorem bool_surjective_of_nonconstant {Z : Type} (g : Z → Bool) (h : ∃ a b,g a≠g b) :
    Function.Surjective g := by
  obtain ⟨a,b,hab⟩ := h
  intro c
  by_cases ha : g a=c
  · exact ⟨a,ha⟩
  · refine ⟨b,?_⟩
    cases hga : g a <;> cases hgb : g b <;> cases c <;> simp_all
end
noncomputable section

/-- Composing a nonconstant Boolean outer function with nonconstant Boolean inner functions
yields a nonconstant function. -/
theorem composedFunction_nonconstant {k : ℕ} {Y : Fin k → Type}
    (g : ∀ i,Y i → Bool) (f : (Fin k → Bool) → Bool)
    (hfn : ∃ u v,f u≠f v) (hgn : ∀ i,∃ a b,g i a≠g i b) :
    ∃ x y,composedFunction g f x≠composedFunction g f y := by
  obtain ⟨u,v,huv⟩ := hfn
  choose x hx using (fun i => bool_surjective_of_nonconstant (g i) (hgn i) (u i))
  choose y hy using (fun i => bool_surjective_of_nonconstant (g i) (hgn i) (v i))
  refine ⟨x,y,?_⟩
  change f (fun i => g i (x i))≠f (fun i => g i (y i))
  simpa only [hx,hy] using! huv
end
noncomputable section

/-- Under positive costs, nonconstant outer and inner functions, and finite inner nonnegative
adversary costs, proves the nonnegative composition upper bound and constructs optimal
negative adversary matrices and minimax witnesses with the stated composition inequalities. -/
theorem stageA_general_adversary_clause18_source_complete {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i,Fintype (Y i)] [∀ i,DecidableEq (Y i)]
    (gin : ∀ i,Y i → Fin (n i) → Bool) (g : ∀ i,Y i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (ha : ∀ c,0<alpha c) (hfn : ∃ u v,f u≠f v)
    (hgn : ∀ i,∃ a b,g i a≠g i b) (hfin : ∀ i,blockCosts gin g alpha i<⊤) :
    advAlphaENN (composedInput gin) (composedFunction g f) (fun c => ENNReal.ofReal (alpha c))≤
      advAlphaENN (fun u : Fin k → Bool => u) f (blockCosts gin g alpha) ∧
    (∃ (A : Matrix (Fin k → Bool) (Fin k → Bool) ℂ) (B : ∀ i,Matrix (Y i) (Y i) ℂ),
      GeneratedCompositionWitness g f A B ∧
      advAlphaPmWitness (fun u : Fin k → Bool => u) (blockCostsPm gin g alpha) A=
        advAlphaPmENN (fun u : Fin k → Bool => u) f (blockCostsPm gin g alpha) ∧
      (∀ i,advAlphaPmWitness (gin i) (fun j => ENNReal.ofReal (alpha ⟨i,j⟩)) (B i)=
        advAlphaPmENN (gin i) (g i) (fun j => ENNReal.ofReal (alpha ⟨i,j⟩))) ∧
      advAlphaPmWitness (fun u : Fin k → Bool => u) (blockCostsPm gin g alpha) A≤
        advAlphaPmWitness (composedInput gin) (fun c => ENNReal.ofReal (alpha c)) (composedAdversary g f A B)) ∧
    (∃ (pf : (Fin k → Bool) → Fin k → ℝ) (pg : ∀ i,Y i → Fin (n i) → ℝ),
      IsMinimaxOptimal (fun u : Fin k → Bool => u) f (fun i => (blockCosts gin g alpha i).toReal) pf ∧
      (∀ i,IsMinimaxOptimal (gin i) (g i) (fun j => alpha ⟨i,j⟩) (pg i)) ∧
      IsProbabilityFamily (composeMinimaxWitness g pf pg) ∧
      minimaxWitnessValue (composedInput gin) (composedFunction g f) alpha (composeMinimaxWitness g pf pg)≤
        minimaxWitnessValue (fun u : Fin k → Bool => u) f (fun i => (blockCosts gin g alpha i).toReal) pf) := by
  have hobs (i : Fin k) : OutputObservable (gin i) (g i) :=
    (advAlphaR_finite_iff_observable (gin i) (g i) (fun j => alpha ⟨i,j⟩)
      (fun j => ha ⟨i,j⟩) (hgn i)).mp (hfin i)
  haveI : Nonempty (Fin k) := by
    obtain ⟨u,v,huv⟩ := hfn
    have hn : u≠v := fun he => huv (congrArg f he)
    obtain ⟨i,_⟩ := Function.ne_iff.mp hn
    exact ⟨i⟩
  haveI : ∀ i,Nonempty (Fin (n i)) := fun i => by
    obtain ⟨a,b,hab⟩ := hgn i
    obtain ⟨j,_⟩ := hobs i a b hab
    exact ⟨j⟩
  have hcn := composedFunction_nonconstant g f hfn hgn
  choose R hR hRN hRO hRV using (fun i => advAlphaR_optimal_exists_of_observable
    (gin i) (g i) (fun j => alpha ⟨i,j⟩) (fun j => ha ⟨i,j⟩) (hobs i) (hgn i))
  let beta : Fin k → ℝ := fun i => ‖R i‖
  have hb (i : Fin k) : 0<beta i := norm_pos_iff.mpr (hRN i)
  have hcost : blockCosts gin g alpha=(fun i => ENNReal.ofReal (beta i)) := by
    funext i
    exact hRV i
  have hbeta (i : Fin k) :
      advAlphaR (gin i) (g i) (fun j => alpha ⟨i,j⟩)=ENNReal.ofReal (beta i) := hRV i
  have hbetar : (fun i => (blockCosts gin g alpha i).toReal)=beta := by
    rw [hcost]
    funext i
    exact ENNReal.toReal_ofReal (hb i).le
  have hMM (i : Fin k) : minimaxAlpha (gin i) (g i) (fun j => alpha ⟨i,j⟩)=ENNReal.ofReal (beta i) :=
    (advAlphaR_eq_minimax _ _ _ (fun j => ha ⟨i,j⟩) (hgn i)).symm.trans (hbeta i)
  obtain ⟨pf,hpf⟩ := minimax_optimal_exists (fun u : Fin k → Bool => u) f beta hfn
  choose pg hpg using (fun i => minimax_optimal_exists (gin i) (g i) (fun j => alpha ⟨i,j⟩) (hgn i))
  refine ⟨?_,source_optimized_adversary_composition gin g f alpha ha hfn hgn hobs,?_⟩
  · rw [hcost]
    exact source_adversary_composition_upper gin g f alpha beta ha hcn hgn hbeta
  · refine ⟨pf,pg,?_,hpg,composed_probability_family g pf pg hpf.1 (fun i => (hpg i).1),?_⟩
    · rw [hbetar]
      exact hpf
    · rw [hbetar]
      apply composed_minimax_witness_bound gin g f alpha beta pf pg hpf.1 (fun c => (ha c).le) hcn
      intro i a b hab
      exact optimal_minimax_denominator (gin i) (g i) (fun j => alpha ⟨i,j⟩) (pg i)
        (beta i) (fun j => (ha ⟨i,j⟩).le) (hgn i) ((hpg i).2.trans (hMM i)) (hb i).le a b hab
end
noncomputable section

/-- The cost-weighted nonnegative adversary value of a constant Boolean function is zero. -/
theorem advAlphaENN_constant_zero {Z J : Type} [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
    (input : Z → J → Bool) (b : Bool) (cost : J → ℝ≥0∞) :
    advAlphaENN input (fun _ => b) cost=0 := by
  apply le_antisymm _ bot_le
  unfold advAlphaENN
  apply iSup_le
  intro A
  have hz : A.val=0 := by
    ext x y
    exact A.property.2.2.1 x y rfl
  exact (A.property.2.2.2 hz).elim
end
noncomputable section

/-- The unrestricted composition statement `clause18Prop` is false. -/
theorem clause18_raw_constant_block_counterexample : ¬Qatlib.Concepts.AdversaryBounds.AdvDuality.clause18Prop := by
  intro h
  have hfin : ∀ i : Fin 1,blockCosts (fun (_ : Fin 1) (x : Bool) (_ : Fin 1) => x)
      (fun (_ : Fin 1) (_ : Bool) => false) (fun _ => (1 : ℝ)) i<⊤ := by
    intro i
    change advAlphaENN (fun (x : Bool) (_ : Fin 1) => x) (fun _ => false)
        (fun _ => ENNReal.ofReal (1 : ℝ))<⊤
    rw [advAlphaENN_constant_zero]
    exact ENNReal.zero_lt_top
  have hh := h 1 (fun _ => Bool) (fun _ => 1) (fun _ x _ => x) (fun _ _ => false)
    (fun u => u 0) (fun _ => (1 : ℝ)) (by intro c; norm_num)
    ⟨fun _ => false,fun _ => true,by decide⟩ hfin
  obtain ⟨A,B,hgen,_⟩ := hh.2.1
  have hz : B 0=0 := by
    ext x y
    exact hgen.2.2.2.2.1 0 x y rfl
  exact hgen.2.2.2.2.2.1 0 hz
end
noncomputable section

/-- For positive costs and nonconstant functions with observable inner outputs, the outer
negative adversary value at the inner adversary costs is bounded by the negative adversary
value of the composition, as in [HoyerLeeSpalek2007]. -/
theorem source_negative_adversary_composition_lower {k : ℕ} {Y : Fin k → Type} {n : Fin k → ℕ}
    [∀ i,Fintype (Y i)] [∀ i,DecidableEq (Y i)]
    (gin : ∀ i,Y i → Fin (n i) → Bool) (g : ∀ i,Y i → Bool)
    (f : (Fin k → Bool) → Bool) (alpha : ((i : Fin k) × Fin (n i)) → ℝ)
    (ha : ∀ c,0<alpha c) (hfn : ∃ u v,f u≠f v)
    (hgn : ∀ i,∃ a b,g i a≠g i b) (hobs : ∀ i,OutputObservable (gin i) (g i)) :
    advAlphaPmENN (fun u : Fin k → Bool => u) f (blockCostsPm gin g alpha)≤
      advAlphaPmENN (composedInput gin) (composedFunction g f) (fun c => ENNReal.ofReal (alpha c)) := by
  obtain ⟨A,B,hgen,hAO,_,hbound⟩ :=
      source_optimized_adversary_composition gin g f alpha ha hfn hgn hobs
  rcases hgen with ⟨_,_,_,_,_,_,hC,hzC,hCN⟩
  rw [← hAO]
  exact hbound.trans (le_iSup_of_le ⟨composedAdversary g f A B,hC,hzC,hCN⟩ le_rfl)
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality
