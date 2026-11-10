/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.ZeroCostLimit.FirstHitMass
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AdaptiveCP.BranchTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open scoped ENNReal
open scoped ComplexOrder
open scoped BigOperators

variable {S O X : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype O]
  [DecidableEq O] [Fintype X] [DecidableEq X]
variable {D E : ℕ}

theorem ofReal_finset_sum {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      exact Complex.ofReal_add _ _

theorem ofReal_triple_sum {ι κ ν : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [DecidableEq ν]
    (s : Finset ν) (f : ι → κ → ν → ℝ) :
    ((∑ i : ι, ∑ j : κ, ∑ m ∈ s, f i j m : ℝ) : ℂ)
      = ∑ i : ι, ∑ j : κ, ∑ m ∈ s, ((f i j m : ℝ) : ℂ) := by
  rw [ofReal_finset_sum Finset.univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ofReal_finset_sum Finset.univ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ofReal_finset_sum s]

theorem smul_ofReal_mul (c p : ℝ) :
    ((c : ℝ) : ℂ) • ((p : ℝ) : ℂ) = ((c * p : ℝ) : ℂ) := by
  rw [smul_eq_mul, ← Complex.ofReal_mul]

theorem toReal_finset_sum_mul {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ≥0∞)
    (h : ∀ i, a i * b i ≠ ∞) :
    (∑ i : ι, a i * b i).toReal = ∑ i : ι, (a i).toReal * (b i).toReal := by
  rw [ENNReal.toReal_sum (fun i _ => h i)]
  exact Finset.sum_congr rfl (fun i _ => ENNReal.toReal_mul)

theorem transitionProb_le_one (P : JointProgram S O X D E) (s : S) (d : O ⊕ S) :
    (P.next s d).toReal ≤ 1 := by
  have hle : P.next s d ≤ ∑' x, P.next s x := ENNReal.le_tsum (f := P.next s) d
  rw [PMF.tsum_coe] at hle
  have hne : P.next s d ≠ ∞ := ne_top_of_le_ne_top (by simp) hle
  exact (ENNReal.toReal_le_toReal hne (by simp)).mpr hle

theorem transitionProb_ne_top (P : JointProgram S O X D E) (s : S) (d : O ⊕ S) :
    P.next s d ≠ ∞ := by
  have hle : P.next s d ≤ ∑' x, P.next s x := ENNReal.le_tsum (f := P.next s) d
  rw [PMF.tsum_coe] at hle
  exact ne_top_of_le_ne_top (by simp) hle

theorem trace_finset_sum_map {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ι → (Operator D →ₗ[ℂ] Operator E)) (ρ : Operator D) :
    Matrix.trace ((∑ d : ι, T d) ρ) = ∑ d : ι, Matrix.trace (T d ρ) := by
  have h : (∑ d : ι, T d) ρ = ∑ d : ι, T d ρ := LinearMap.sum_apply Finset.univ (fun d => T d) ρ
  rw [h]
  exact Matrix.trace_sum Finset.univ (fun d => T d ρ)

theorem CompletelyPositive.smul {T : Operator D →ₗ[ℂ] Operator E}
    (hT : CompletelyPositive T) (c : ℝ) (hc : 0 ≤ c) :
    CompletelyPositive (((c : ℝ) : ℂ) • T) := by
  intro r A hA
  have hAmp : ChannelAmplification (((c : ℝ) : ℂ) • T) r A
      = ((c : ℝ) : ℂ) • ChannelAmplification T r A := by
    ext x y
    simp [ChannelAmplification, LinearMap.smul_apply]
  rw [hAmp]
  exact Matrix.PosSemidef.smul (hT r A hA) (RCLike.ofReal_nonneg.mpr hc)

theorem CompletelyPositive.zero' :
    CompletelyPositive (0 : Operator D →ₗ[ℂ] Operator E) := by
  rw [Qatlib.Concepts.ChannelTheory.Stinespring.completelyPositive_iff_physlib]
  exact MatrixMap.IsCompletelyPositive.zero (Fin D) (Fin E)

theorem jointStopMap_cp (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ),
      CompletelyPositive (jointStopMap P fuel cfg o x k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg o x k
      cases cfg with
      | inl o0 =>
          simp only [jointStopMap_zero]
          by_cases h : o0 = o ∧ k = 0
          · simp only [h, and_self, if_true]
            exact P.instrument.cp x
          · simp only [h, if_false]
            exact CompletelyPositive.zero'
      | inr s =>
          simp only [jointStopMap_zero]
          exact CompletelyPositive.zero'
  | succ fuel ih =>
      intro cfg o x k
      cases cfg with
      | inl o0 =>
          simp only [jointStopMap_succ]
          by_cases h : o0 = o ∧ k = 0
          · simp only [h, and_self, if_true]
            exact P.instrument.cp x
          · simp only [h, if_false]
            exact CompletelyPositive.zero'
      | inr s =>
          simp only [jointStopMap_succ]
          by_cases hk : P.cost s ≤ k
          · simp only [hk, if_true]
            refine CompletelyPositive.sum (fun d _ => ?_)
            refine CompletelyPositive.smul ?_ (transitionProb P s d) ?_
            · exact (CompletelyPositive.comp (ih d o x (k - P.cost s))
                (P.channel s).completelyPositive)
            · exact ENNReal.toReal_nonneg
          · simp only [hk, if_false]
            exact CompletelyPositive.zero'

theorem isDensityOperator_channel {D E : ℕ} (C : QuantumChannel D E) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) : IsDensityOperator (C.map ρ) := by
  refine ⟨C.completelyPositive.positive hρ.1, ?_⟩
  rw [C.tracePreserving]
  exact hρ.2

theorem jointProb_trace (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) (ρ : Operator D),
      IsDensityOperator ρ →
      Matrix.trace (jointStopMap P fuel cfg o x k ρ) =
        ((jointProb P ρ fuel cfg o x k : ℝ) : ℂ) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg o x k ρ hρ
      cases cfg with
      | inl o0 =>
          simp only [jointStopMap_zero, jointProb_zero]
          by_cases h : o0 = o ∧ k = 0
          · simp only [h, and_self, if_true]
            rw [trace_branch_eq P.instrument hρ.1 x]
          · simp only [h, if_false]
            simp [Matrix.trace]
      | inr s =>
          simp only [jointStopMap_zero, jointProb_zero]
          simp [Matrix.trace]
  | succ fuel ih =>
      intro cfg o x k ρ hρ
      cases cfg with
      | inl o0 =>
          simp only [jointStopMap_succ, jointProb_succ]
          by_cases h : o0 = o ∧ k = 0
          · simp only [h, and_self, if_true]
            rw [trace_branch_eq P.instrument hρ.1 x]
          · simp only [h, if_false]
            simp [Matrix.trace]
      | inr s =>
          simp only [jointStopMap_succ, jointProb_succ]
          by_cases hk : P.cost s ≤ k
          · simp only [hk, if_true]
            have hmem : IsDensityOperator ((P.channel s).map ρ) :=
              isDensityOperator_channel (P.channel s) hρ
            calc
              Matrix.trace
                  ((∑ d : O ⊕ S, ((transitionProb P s d : ℝ) : ℂ) •
                    (jointStopMap P fuel d o x (k - P.cost s)).comp (P.channel s).map) ρ)
                  = ∑ d : O ⊕ S, Matrix.trace
                    ((((transitionProb P s d : ℝ) : ℂ) •
                      (jointStopMap P fuel d o x (k - P.cost s)).comp (P.channel s).map) ρ) :=
                trace_finset_sum_map _ _
              _ = ∑ d : O ⊕ S, ((transitionProb P s d : ℝ) : ℂ) *
                    Matrix.trace (jointStopMap P fuel d o x (k - P.cost s)
                      ((P.channel s).map ρ)) := by
                refine Finset.sum_congr rfl (fun d _ => ?_)
                rw [LinearMap.smul_apply, Matrix.trace_smul, smul_eq_mul]
                rfl
              _ = ∑ d : O ⊕ S, ((transitionProb P s d : ℝ) : ℂ) *
                    ((jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s) : ℝ) : ℂ) := by
                refine Finset.sum_congr rfl (fun d _ => ?_)
                rw [ih d o x (k - P.cost s) ((P.channel s).map ρ) hmem]
              _ = ∑ d : O ⊕ S, ((transitionProb P s d * jointProb P ((P.channel s).map ρ) fuel d o x
                    (k - P.cost s) : ℝ) : ℂ) :=
                Finset.sum_congr rfl (fun d _ => smul_ofReal_mul _ _)
              _ = ((∑ d : O ⊕ S, transitionProb P s d *
                    jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s) : ℝ) : ℂ) := by
                symm
                exact ofReal_finset_sum Finset.univ _
          · simp only [hk, if_false]
            simp [Matrix.trace]

theorem jointClassicalMass_eq_weightedRunFor (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ),
      jointClassicalMass P fuel cfg o k =
        weightedRunFor P.next P.cost fuel cfg (.inl o, k) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg o k
      cases cfg with
      | inl o0 =>
          simp only [jointClassicalMass_zero, weightedRunFor_zero]
          simp [CostedLaw.ret, PMF.pure_apply, eq_comm]
      | inr s =>
          simp only [jointClassicalMass_zero, weightedRunFor_zero]
          simp [CostedLaw.ret, PMF.pure_apply]
  | succ fuel ih =>
      intro cfg o k
      cases cfg with
      | inl o0 =>
          simp only [jointClassicalMass_succ, weightedRunFor_halted]
          simp [CostedLaw.ret, PMF.pure_apply, eq_comm]
      | inr s =>
          simp only [jointClassicalMass_succ, weightedRunFor_succ_running_point]
          by_cases hk : P.cost s ≤ k
          · simp only [hk, if_true]
            rw [tsum_fintype (L := SummationFilter.unconditional _)]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            rw [ih d o (k - P.cost s)]
          · simp only [hk, if_false]

theorem jointClassicalMass_ne_top (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S)
    (o : O) (k : ℕ) : jointClassicalMass P fuel cfg o k ≠ ∞ := by
  rw [jointClassicalMass_eq_weightedRunFor]
  have hle : weightedRunFor P.next P.cost fuel cfg (.inl o, k) ≤ 1 := by
    have hle' : weightedRunFor P.next P.cost fuel cfg (.inl o, k)
        ≤ ∑' x, weightedRunFor P.next P.cost fuel cfg x :=
      ENNReal.le_tsum (f := weightedRunFor P.next P.cost fuel cfg) (.inl o, k)
    rw [PMF.tsum_coe] at hle'
    exact hle'
  exact ne_top_of_le_ne_top (by simp) hle

theorem jointProb_charge_layer (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ) (ρ : Operator D), IsDensityOperator ρ →
      (∑ x : X, jointProb P ρ fuel cfg o x k) =
        (jointClassicalMass P fuel cfg o k).toReal := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg o k ρ hρ
      cases cfg with
      | inl o0 =>
          simp only [jointProb_zero, jointClassicalMass_zero]
          by_cases h : o0 = o ∧ k = 0
          · simp only [h, and_self, if_true]
            rw [sum_instrumentProb P.instrument ρ]
            simp [hρ.2]
          · simp only [h, if_false]
            simp
      | inr s =>
          simp only [jointProb_zero, jointClassicalMass_zero]
          simp
  | succ fuel ih =>
      intro cfg o k ρ hρ
      cases cfg with
      | inl o0 =>
          simp only [jointProb_succ, jointClassicalMass_succ]
          by_cases h : o0 = o ∧ k = 0
          · simp only [h, and_self, if_true]
            rw [sum_instrumentProb P.instrument ρ]
            simp [hρ.2]
          · simp only [h, if_false]
            simp
      | inr s =>
          simp only [jointProb_succ, jointClassicalMass_succ]
          by_cases hk : P.cost s ≤ k
          · simp only [hk, if_true]
            have hmem : IsDensityOperator ((P.channel s).map ρ) :=
              isDensityOperator_channel (P.channel s) hρ
            have hlayer : ∀ d : O ⊕ S,
                (∑ x : X, jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s))
                  = (jointClassicalMass P fuel d o (k - P.cost s)).toReal :=
              fun d => ih d o (k - P.cost s) ((P.channel s).map ρ) hmem
            have hswap : (∑ x : X, ∑ d : O ⊕ S, transitionProb P s d *
                  jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s))
                = ∑ d : O ⊕ S, transitionProb P s d *
                  (∑ x : X, jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s)) := by
              calc
                (∑ x : X, ∑ d : O ⊕ S, transitionProb P s d *
                    jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s))
                    = ∑ d : O ⊕ S, ∑ x : X, transitionProb P s d *
                        jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s) := Finset.sum_comm
                _ = ∑ d : O ⊕ S, transitionProb P s d *
                    (∑ x : X, jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s)) := by
                      refine Finset.sum_congr rfl (fun d _ => ?_)
                      exact (Finset.mul_sum Finset.univ
                        (fun x => jointProb P ((P.channel s).map ρ) fuel d o x (k - P.cost s))
                        (transitionProb P s d)).symm
            have hfin : ∀ d : O ⊕ S,
                P.next s d * jointClassicalMass P fuel d o (k - P.cost s) ≠ ∞ := by
              intro d
              exact ENNReal.mul_ne_top (transitionProb_ne_top P s d)
                (jointClassicalMass_ne_top P fuel d o (k - P.cost s))
            rw [hswap]
            rw [toReal_finset_sum_mul (fun d => P.next s d)
              (fun d => jointClassicalMass P fuel d o (k - P.cost s)) hfin]
            refine Finset.sum_congr rfl (fun d _ => ?_)
            rw [hlayer d]
            rfl
          · simp only [hk, if_false]
            simp

theorem CompletelyPositive.finset_sum' {ι : Type} [DecidableEq ι]
    {T : ι → (Operator D →ₗ[ℂ] Operator E)} (s : Finset ι)
    (h : ∀ i ∈ s, CompletelyPositive (T i)) :
    CompletelyPositive (Finset.sum s (fun i => T i)) := by
  induction s using Finset.induction_on with
  | empty => exact CompletelyPositive.zero'
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact CompletelyPositive.add (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem jointEventMap_cp (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev],
      CompletelyPositive (jointEventMap P fuel cfg Ev) := by
  intro fuel cfg Ev
  unfold jointEventMap
  refine CompletelyPositive.sum (fun o _ => ?_)
  refine CompletelyPositive.sum (fun x _ => ?_)
  refine CompletelyPositive.finset_sum' _ (fun k _ => ?_)
  by_cases h : Ev (o, x, k)
  · simp only [h, if_true]
    exact jointStopMap_cp P fuel cfg o x k
  · simp only [h, if_false]
    exact CompletelyPositive.zero'

theorem psd_eq_zero_of_trace_zero {n : ℕ} {A : Operator n} (hA : A.PosSemidef)
    (h : Matrix.trace A = 0) : A = 0 := by
  have hre : (Matrix.trace A).re = 0 := by rw [h]; simp
  have him : (Matrix.trace A).im = 0 := (RCLike.nonneg_iff.mp hA.trace_nonneg).2
  exact (Matrix.PosSemidef.trace_eq_zero_iff hA).mp (Complex.ext hre him)

theorem trace_finset_sum_map' {ι : Type} (s : Finset ι)
    (T : ι → (Operator D →ₗ[ℂ] Operator E)) (ρ : Operator D) :
    Matrix.trace ((∑ i ∈ s, T i) ρ) = ∑ i ∈ s, Matrix.trace (T i ρ) := by
  rw [LinearMap.sum_apply s (fun i => T i) ρ]
  exact Matrix.trace_sum s (fun i => T i ρ)

theorem jointEventMap_trace (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D),
      IsDensityOperator ρ →
      Matrix.trace (jointEventMap P fuel cfg Ev ρ) =
        ((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ) := by
  intro fuel cfg Ev _ ρ hρ
  have hleaf : ∀ (o : O) (x : X) (k : ℕ),
      Matrix.trace ((if Ev (o, x, k) then jointStopMap P fuel cfg o x k else 0) ρ)
        = ((if Ev (o, x, k) then jointProb P ρ fuel cfg o x k else 0 : ℝ) : ℂ) := by
    intro o x k
    by_cases h : Ev (o, x, k)
    · simp only [h, if_true]
      exact jointProb_trace P fuel cfg o x k ρ hρ
    · simp only [h, if_false]
      simp
  unfold jointEventMap jointEventProb
  simp only [LinearMap.sum_apply]
  simp only [Matrix.trace_sum]
  rw [ofReal_triple_sum (jointChargeRange P fuel)
    (fun o x k => if Ev (o, x, k) then jointProb P ρ fuel cfg o x k else 0)]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Finset.sum_congr rfl (fun k _ => hleaf o x k)

theorem jointNormalizedPost_isDensity (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D),
      IsDensityOperator ρ → 0 < jointEventProb P ρ fuel cfg Ev →
      IsDensityOperator (jointNormalizedPost P ρ fuel cfg Ev) := by
  intro fuel cfg Ev _ ρ hρ hpos
  have hpsd : (jointEventMap P fuel cfg Ev ρ).PosSemidef :=
    (jointEventMap_cp P fuel cfg Ev).positive hρ.1
  have htr : Matrix.trace (jointEventMap P fuel cfg Ev ρ) =
      ((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ) :=
    jointEventMap_trace P fuel cfg Ev ρ hρ
  have hne : ((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hinv : (0 : ℂ) ≤ (((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hpos.le)
  rw [jointNormalizedPost, if_pos hpos]
  refine ⟨Matrix.PosSemidef.smul hpsd hinv, ?_⟩
  rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ hne]

theorem jointEventMap_zero_of_prob_zero (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] (ρ : Operator D),
      IsDensityOperator ρ → jointEventProb P ρ fuel cfg Ev = 0 →
      jointEventMap P fuel cfg Ev ρ = 0 := by
  intro fuel cfg Ev _ ρ hρ hzero
  have hpsd : (jointEventMap P fuel cfg Ev ρ).PosSemidef :=
    (jointEventMap_cp P fuel cfg Ev).positive hρ.1
  have htr : Matrix.trace (jointEventMap P fuel cfg Ev ρ)
      = ((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ) :=
    jointEventMap_trace P fuel cfg Ev ρ hρ
  have hz : Matrix.trace (jointEventMap P fuel cfg Ev ρ) = 0 := by
    rw [htr]
    have : ((jointEventProb P ρ fuel cfg Ev : ℝ) : ℂ) = 0 := by
      apply Complex.ext
      · simp [hzero]
      · simp
    exact this
  exact psd_eq_zero_of_trace_zero hpsd hz

theorem jointProb_nonneg (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) (ρ : Operator D),
      IsDensityOperator ρ → 0 ≤ jointProb P ρ fuel cfg o x k := by
  intro fuel cfg o x k ρ hρ
  have hpos : (jointStopMap P fuel cfg o x k ρ).PosSemidef :=
    (jointStopMap_cp P fuel cfg o x k).positive hρ.1
  have h := (RCLike.nonneg_iff.mp hpos.trace_nonneg).1
  rw [jointProb_trace P fuel cfg o x k ρ hρ] at h
  simpa using! h

theorem jointStopMap_zero_of_prob_zero (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) (ρ : Operator D),
      IsDensityOperator ρ → jointProb P ρ fuel cfg o x k = 0 →
      jointStopMap P fuel cfg o x k ρ = 0 := by
  intro fuel cfg o x k ρ hρ hzero
  have hpsd : (jointStopMap P fuel cfg o x k ρ).PosSemidef :=
    (jointStopMap_cp P fuel cfg o x k).positive hρ.1
  have htr : Matrix.trace (jointStopMap P fuel cfg o x k ρ)
      = ((jointProb P ρ fuel cfg o x k : ℝ) : ℂ) :=
    jointProb_trace P fuel cfg o x k ρ hρ
  have hz : Matrix.trace (jointStopMap P fuel cfg o x k ρ) = 0 := by
    rw [htr]
    have : ((jointProb P ρ fuel cfg o x k : ℝ) : ℂ) = 0 := by
      apply Complex.ext
      · simp [hzero]
      · simp
    exact this
  exact psd_eq_zero_of_trace_zero hpsd hz

theorem jointLabelPost_isDensity (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) (ρ : Operator D),
      IsDensityOperator ρ → 0 < jointProb P ρ fuel cfg o x k →
      IsDensityOperator (jointLabelPost P ρ fuel cfg o x k) := by
  intro fuel cfg o x k ρ hρ hpos
  have hpsd : (jointStopMap P fuel cfg o x k ρ).PosSemidef :=
    (jointStopMap_cp P fuel cfg o x k).positive hρ.1
  have htr : Matrix.trace (jointStopMap P fuel cfg o x k ρ)
      = ((jointProb P ρ fuel cfg o x k : ℝ) : ℂ) :=
    jointProb_trace P fuel cfg o x k ρ hρ
  have hne : ((jointProb P ρ fuel cfg o x k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hinv : (0 : ℂ) ≤ (((jointProb P ρ fuel cfg o x k : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hpos.le)
  rw [jointLabelPost, if_pos hpos]
  refine ⟨Matrix.PosSemidef.smul hpsd hinv, ?_⟩
  rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ hne]

theorem tensorLeft_trace {D E R : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    Matrix.trace (tensorLeft T ρ) = Matrix.trace (T (PartialTrace ρ)) := by
  have hlin : ∀ (f : Fin R → (Fin D → Fin D → ℂ)) (a : Fin E),
      T (fun i j => ∑ r : Fin R, f r i j) a a = ∑ r : Fin R, T (fun i j => f r i j) a a := by
    intro f a
    have h := congrArg (fun M : Operator E => M a a)
      (map_sum T (fun r => fun i j => f r i j) Finset.univ)
    have hfun : (∑ x : Fin R, fun i j => f x i j) = (fun i j => ∑ x : Fin R, f x i j) := by
      funext i j
      simp [Finset.sum_apply]
    rw [hfun] at h
    simp only [Matrix.sum_apply] at h
    exact h
  have hL : Matrix.trace (tensorLeft T ρ)
      = ∑ r : Fin R, ∑ a : Fin E, T (fun i j => ρ (i, r) (j, r)) a a := by
    show (∑ p : Fin E × Fin R, T (fun i j => ρ (i, p.2) (j, p.2)) p.1 p.1)
      = ∑ r : Fin R, ∑ a : Fin E, T (fun i j => ρ (i, r) (j, r)) a a
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hR : Matrix.trace (T (PartialTrace ρ))
      = ∑ r : Fin R, ∑ a : Fin E, T (fun i j => ρ (i, r) (j, r)) a a := by
    show (∑ a : Fin E, T (fun i j => ∑ r : Fin R, ρ (i, r) (j, r)) a a)
      = ∑ r : Fin R, ∑ a : Fin E, T (fun i j => ρ (i, r) (j, r)) a a
    have h1 : (∑ a : Fin E, T (fun i j => ∑ r : Fin R, ρ (i, r) (j, r)) a a)
        = ∑ a : Fin E, ∑ r : Fin R, T (fun i j => ρ (i, r) (j, r)) a a := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      exact hlin (fun r => fun i j => ρ (i, r) (j, r)) a
    rw [h1, Finset.sum_comm]
  rw [hL, hR]

theorem jointReferenceStopMap_trace (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) (R : ℕ)
      (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      Matrix.trace (tensorLeft (jointStopMap P fuel cfg o x k) ρ)
        = Matrix.trace (jointStopMap P fuel cfg o x k (jointMemoryMarginal D R ρ)) := by
  intro fuel cfg o x k R ρ
  exact tensorLeft_trace _ _

theorem jointReferenceStopMap_trace_prob (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (x : X) (k : ℕ) (R : ℕ)
      (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      IsDensityOperator (jointMemoryMarginal D R ρ) →
      Matrix.trace (tensorLeft (jointStopMap P fuel cfg o x k) ρ)
        = ((jointProb P (jointMemoryMarginal D R ρ) fuel cfg o x k : ℝ) : ℂ) := by
  intro fuel cfg o x k R ρ hρ
  rw [jointReferenceStopMap_trace]
  exact jointProb_trace P fuel cfg o x k (jointMemoryMarginal D R ρ) hρ

theorem tensorLeft_sum {D E R : ℕ} {ι : Type} (s : Finset ι)
    (T : ι → (Operator D →ₗ[ℂ] Operator E))
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (∑ i ∈ s, T i) ρ = ∑ i ∈ s, tensorLeft (T i) ρ := by
  ext x y
  change (∑ i ∈ s, T i) (fun i j => ρ (i, x.2) (j, y.2)) x.1 y.1 = _
  rw [LinearMap.sum_apply]
  simp only [Matrix.sum_apply]
  rfl

theorem tensorLeft_zero {D E R : ℕ}
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (0 : Operator D →ₗ[ℂ] Operator E) ρ = 0 := by
  ext x y
  simp [tensorLeft]

theorem jointReferenceEventMap_trace (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (Ev : O × X × ℕ → Prop) [DecidablePred Ev] {R : ℕ}
      (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      IsDensityOperator (jointMemoryMarginal D R ρ) →
      Matrix.trace (jointReferenceEventMap P fuel cfg Ev ρ)
        = ((jointEventProb P (jointMemoryMarginal D R ρ) fuel cfg Ev : ℝ) : ℂ) := by
  intro fuel cfg Ev _ R ρ hρ
  have hleaf : ∀ (o : O) (x : X) (k : ℕ),
      Matrix.trace (tensorLeft (if Ev (o, x, k) then jointStopMap P fuel cfg o x k else 0) ρ)
        = ((if Ev (o, x, k) then
              jointProb P (jointMemoryMarginal D R ρ) fuel cfg o x k else 0 : ℝ) : ℂ) := by
    intro o x k
    by_cases h : Ev (o, x, k)
    · simp only [h, if_true]
      rw [tensorLeft_trace]
      exact jointProb_trace P fuel cfg o x k (jointMemoryMarginal D R ρ) hρ
    · simp only [h, if_false]
      rw [tensorLeft_zero]
      simp
  unfold jointReferenceEventMap jointEventMap jointEventProb
  simp only [tensorLeft_sum]
  simp only [Matrix.trace_sum]
  rw [ofReal_triple_sum (jointChargeRange P fuel)
    (fun o x k => if Ev (o, x, k) then
      jointProb P (jointMemoryMarginal D R ρ) fuel cfg o x k else 0)]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Finset.sum_congr rfl (fun k _ => hleaf o x k)

theorem jointClassicalMass_zero_of_charge_gt (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ),
      fuel * maxCharge P < k → jointClassicalMass P fuel cfg o k = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg o k h
      rw [jointClassicalMass_zero]
      cases cfg with
      | inl o0 =>
          by_cases hc : o0 = o ∧ k = 0
          · simp only [if_pos hc]
            exact absurd hc.2 (Nat.ne_of_gt (by simpa using! h))
          · simp only [if_neg hc]
      | inr s => rfl
  | succ fuel ih =>
      intro cfg o k h
      rw [jointClassicalMass_succ]
      cases cfg with
      | inl o0 =>
          by_cases hc : o0 = o ∧ k = 0
          · simp only [if_pos hc]
            exact absurd hc.2 (Nat.ne_of_gt (by have h2 := h; omega))
          · simp only [if_neg hc]
      | inr s =>
          by_cases hk : P.cost s ≤ k
          · simp only [if_pos hk]
            refine Finset.sum_eq_zero (fun d _ => ?_)
            have hcost : P.cost s ≤ maxCharge P := Finset.le_sup (Finset.mem_univ s)
            have hlt : fuel * maxCharge P < k - P.cost s := by
              have hsum : fuel * maxCharge P + P.cost s
                  ≤ fuel * maxCharge P + maxCharge P :=
                Nat.add_le_add_left hcost (fuel * maxCharge P)
              have h2 : fuel * maxCharge P + maxCharge P < k := by
                have h3 := h
                rw [Nat.succ_mul] at h3
                exact h3
              omega
            rw [ih d o (k - P.cost s) hlt]
            simp
          · simp only [if_neg hk]

theorem jointNonZenoCheck_iff (P : JointProgram S O X D E) :
    Qatlib.Concepts.StoppingCore.InterruptBridge.nonZenoCheck P.cost = true
      ↔ Qatlib.Concepts.StoppingCore.InterruptBridge.positiveCharge P.cost :=
  clause14_nonZenoCheck_iff S P.cost

theorem jointClassicalMass_stable_of_positive_charge (P : JointProgram S O X D E)
    (hc : ∀ s, 0 < P.cost s) (fuel : ℕ) (cfg : O ⊕ S) (o : O) (k : ℕ) (hk : k ≤ fuel) :
    jointClassicalMass P fuel cfg o k = weightedHaltJoint P.next P.cost cfg o k := by
  rw [jointClassicalMass_eq_weightedRunFor]
  exact clause14_charge_stable S O P.next P.cost
      (fun s => by have hs := hc s; omega) cfg o k fuel hk

theorem jointClassicalMass_tendsto (P : JointProgram S O X D E) (cfg : O ⊕ S)
    (o : O) (k : ℕ) (hpos : 0 < Qatlib.Concepts.ZeroCostLimit.FirstHitMass.haltMass P.next P.cost cfg o k) :
    Filter.Tendsto (fun fuel => jointClassicalMass P fuel cfg o k) Filter.atTop
      (nhds (Qatlib.Concepts.ZeroCostLimit.FirstHitMass.haltMass P.next P.cost cfg o k)) := by
  have hfun : (fun fuel => jointClassicalMass P fuel cfg o k)
      = fun fuel => weightedRunFor P.next P.cost fuel cfg (.inl o, k) := by
    funext fuel
    exact jointClassicalMass_eq_weightedRunFor P fuel cfg o k
  rw [hfun]
  exact (clause14_first_stop_joint S O P.next P.cost cfg o k).2.2 hpos

theorem maxCharge_fairBit (k m : ℕ) (I : Instrument X D E) :
    maxCharge (fairBitProgram k m I) = k := by
  simp [maxCharge, Finset.sup_singleton, fairBitProgram]

theorem fairBit_joint_charge_bound (k m : ℕ) (I : Instrument X D E) (fuel : ℕ)
    (cfg : Fin m ⊕ Unit) (o : Fin m) (c : ℕ) (hc : fuel * k < c) :
    jointClassicalMass (fairBitProgram k m I) fuel cfg o c = 0 := by
  apply jointClassicalMass_zero_of_charge_gt (fairBitProgram k m I) fuel cfg o c
  rw [maxCharge_fairBit k m I]
  exact hc

theorem fairBitProgram_next (k m : ℕ) (I : Instrument X D E) :
    (fairBitProgram k m I).next () = finiteCoinNext k m () := rfl

theorem fairBitProgram_cost (k m : ℕ) (I : Instrument X D E) :
    (fairBitProgram k m I).cost () = k := rfl

theorem jointPendingMass_fairBit (k m : ℕ) (hm : m ≤ 2 ^ k) (fuel : ℕ)
    (I : Instrument X D E) :
    jointPendingMass (fairBitProgram k m I) fuel (.inr ()) = coinRejectMass k m ^ fuel := by
  rw [jointPendingMass, pendingMass_eq_finiteSurvival]
  simp only [finiteSurvival]
  have hnext : (fairBitProgram k m I).next = finiteCoinNext k m := by
    funext u
    exact fairBitProgram_next k m I
  rw [hnext]
  have hev : CostedLaw.event (RandomizedExecution.runFor (finiteCoinNext k m) fuel (.inr ()))
      (fun x : (Fin m ⊕ Unit) × ℕ => ∃ s : Unit, x.1 = Sum.inr s)
      = CostedLaw.event (RandomizedExecution.runFor (finiteCoinNext k m) fuel (.inr ()))
      (fun x : (Fin m ⊕ Unit) × ℕ => x.1 = Sum.inr ()) := by
    refine CostedLaw.event_congr (fun y => ?_)
    constructor
    · rintro ⟨s, h⟩
      have hs : s = () := Subsingleton.elim _ _
      rw [h, hs]
    · intro h
      exact ⟨(), h⟩
  rw [hev]
  exact finiteCoinRun_pending k m fuel hm

theorem jointTruncationLaw (P : JointProgram S O X D E) :
    ∀ (fuel : ℕ) (cfg : O ⊕ S),
      (∑' o : O, ∑' k : ℕ, jointClassicalMass P fuel cfg o k) +
        jointPendingMass P fuel cfg = 1 := by
  intro fuel cfg
  simp only [jointClassicalMass_eq_weightedRunFor]
  exact weightedRunFor_partition P.next P.cost cfg fuel

theorem jointNeverMass_eq (P : JointProgram S O X D E) (cfg : O ⊕ S) :
    jointNeverMass P cfg = nonterminationMass P.next cfg := rfl

theorem jointClassicalMass_range_eq_tsum (P : JointProgram S O X D E)
    (fuel : ℕ) (cfg : O ⊕ S) :
    (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k)
      = ∑' o : O, ∑' k : ℕ, jointClassicalMass P fuel cfg o k := by
  have hconv (o : O) : (∑' k : ℕ, jointClassicalMass P fuel cfg o k)
      = ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k := by
    refine tsum_eq_sum (α := ENNReal)
      (f := fun k : ℕ => jointClassicalMass P fuel cfg o k)
      (L := SummationFilter.unconditional ℕ) (s := jointChargeRange P fuel) ?_
    intro b hb
    apply jointClassicalMass_zero_of_charge_gt P fuel cfg o b
    have hnot : ¬ (b < fuel * maxCharge P + 1) := by
      intro hlt
      exact hb (Finset.mem_range.mpr hlt)
    omega
  rw [tsum_eq_sum (α := ENNReal)
      (f := fun o : O => ∑' k : ℕ, jointClassicalMass P fuel cfg o k)
      (L := SummationFilter.unconditional O) (s := Finset.univ)]
  · exact Finset.sum_congr rfl (fun o _ => (hconv o).symm)
  · intro b hb
    exact (hb (Finset.mem_univ b)).elim

theorem jointTruncationLaw_range (P : JointProgram S O X D E) (fuel : ℕ) (cfg : O ⊕ S) :
    (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k)
      + jointPendingMass P fuel cfg = 1 := by
  rw [jointClassicalMass_range_eq_tsum]
  exact jointTruncationLaw P fuel cfg

theorem jointTotalProb_eq_classical (P : JointProgram S O X D E) (ρ : Operator D)
    (fuel : ℕ) (cfg : O ⊕ S) (hρ : IsDensityOperator ρ) :
    jointTotalProb P ρ fuel cfg
      = (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k).toReal := by
  have hmass : ∀ (o : O) (k : ℕ), jointClassicalMass P fuel cfg o k ≤ 1 := by
    intro o k
    rw [jointClassicalMass_eq_weightedRunFor]
    exact PMF.coe_le_one _ _
  have hfo : ∀ o : O, (∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k) ≠ ∞ := by
    intro o
    have h1 : (∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k)
        ≤ ∑ _ ∈ jointChargeRange P fuel, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum (fun k _ => hmass o k)
    rw [Finset.sum_const] at h1
    exact ne_of_lt (lt_of_le_of_lt h1 (by simp))
  have hswap : (∑ o : O, ∑ x : X, ∑ k ∈ jointChargeRange P fuel,
          jointProb P ρ fuel cfg o x k)
        = ∑ o : O, ∑ k ∈ jointChargeRange P fuel, (jointClassicalMass P fuel cfg o k).toReal := by
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact jointProb_charge_layer P fuel cfg o k ρ hρ
  unfold jointTotalProb
  rw [hswap]
  rw [ENNReal.toReal_sum (fun o _ => hfo o)]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  rw [ENNReal.toReal_sum (fun k _ => jointClassicalMass_ne_top P fuel cfg o k)]

theorem jointTotalProb_truncation (P : JointProgram S O X D E) (ρ : Operator D)
    (fuel : ℕ) (cfg : O ⊕ S) (hρ : IsDensityOperator ρ) :
    jointTotalProb P ρ fuel cfg + (jointPendingMass P fuel cfg).toReal = 1 := by
  rw [jointTotalProb_eq_classical P ρ fuel cfg hρ]
  have hleA : (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k) ≤ 1 := by
    have hbot : (0 : ℝ≥0∞) ≤ jointPendingMass P fuel cfg := bot_le
    calc (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k)
        = (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k) + 0 := by simp
      _ ≤ (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k)
          + jointPendingMass P fuel cfg :=
        add_le_add_right hbot (∑ o : O, ∑ k ∈ jointChargeRange P fuel,
          jointClassicalMass P fuel cfg o k)
      _ = 1 := jointTruncationLaw_range P fuel cfg
  have hleP : jointPendingMass P fuel cfg ≤ 1 := by
    have hbot : (0 : ℝ≥0∞)
        ≤ (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k) := bot_le
    calc jointPendingMass P fuel cfg = jointPendingMass P fuel cfg + 0 := by simp
      _ ≤ jointPendingMass P fuel cfg
          + (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k) :=
        add_le_add_right hbot _
      _ = 1 := (add_comm _ _).trans (jointTruncationLaw_range P fuel cfg)
  have hA : (∑ o : O, ∑ k ∈ jointChargeRange P fuel, jointClassicalMass P fuel cfg o k) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hleA (by simp))
  have hp : jointPendingMass P fuel cfg ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hleP (by simp))
  rw [← ENNReal.toReal_add hA hp]
  rw [jointTruncationLaw_range P fuel cfg]
  simp

theorem fairBit_effective_error (k m : ℕ) (I : Instrument X D E) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (fuel : ℕ) :
    1 - jointTotalProb (fairBitProgram k m I) ρ fuel (.inr ())
      = (jointPendingMass (fairBitProgram k m I) fuel (.inr ())).toReal := by
  have h := jointTotalProb_truncation (fairBitProgram k m I) ρ fuel (.inr ()) hρ
  linarith

theorem clause14_complete : Clause14JointFirstStop := by
  intro S O X _ _ _ _ _ _ _ D E
  exact ⟨jointStopMap_cp, jointProb_trace, jointClassicalMass_eq_weightedRunFor,
    jointProb_charge_layer, jointTruncationLaw, jointNeverMass_eq,
    jointNonZenoCheck_iff, jointClassicalMass_stable_of_positive_charge,
    jointClassicalMass_tendsto, jointTotalProb_truncation⟩

theorem walkGoal_complete : PaidWalkReferenceEvents := by
  intro S O X _ _ _ _ _ _ _ D E
  exact ⟨jointEventMap_cp, jointEventMap_trace, jointNormalizedPost_isDensity,
    jointEventMap_zero_of_prob_zero, jointReferenceEventMap_trace,
    jointReferenceStopMap_trace, jointReferenceStopMap_trace_prob,
    jointLabelPost_isDensity, jointStopMap_zero_of_prob_zero⟩

theorem clause16_complete : Clause16EffectiveSampling := by
  intro X _ _ D E
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k m I
    exact ⟨fairBitProgram_next k m I, fairBitProgram_cost k m I⟩
  · intro k m hm fuel I
    exact jointPendingMass_fairBit k m hm fuel I
  · intro k m I fuel cfg o c hc
    exact fairBit_joint_charge_bound k m I fuel cfg o c hc
  · intro k m I ρ fuel hρ
    exact fairBit_effective_error k m I ρ hρ fuel

end Qatlib.Concepts.MixedInstrument.ClockBridge
