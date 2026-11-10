/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.StoppingReference
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MixedInstrument.ClockBridge
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference
open Matrix
open scoped Classical ComplexOrder BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

variable {S O : Type}

def receiptEmbed (z : (O⊕S)×ℕ) : (O×ℕ)⊕(S×ℕ) :=
  z.1.map (fun o => (o,z.2)) (fun s => (s,z.2))

def receiptMacroNext (next : S→PMF ((O⊕S)×ℕ)) (s : S×ℕ) : PMF ((O×ℕ)⊕(S×ℕ)) :=
  (next s.1).map (fun z => receiptEmbed (z.1,s.2+z.2))

theorem receipt_macro_projection (next : S→PMF ((O⊕S)×ℕ)) (n : ℕ) (cfg : O⊕S) (a : ℕ) :
    (runFor (receiptMacroNext next) n (receiptEmbed (cfg,a))).map Prod.fst =
      (branchCostRun next n cfg).map (fun z => receiptEmbed (z.1,a+z.2)) := by
  induction n generalizing cfg a with
  | zero => simp [runFor,branchCostRun,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,PMF.pure_map]
  | succ n ih =>
    cases cfg with
    | inl o => simp [receiptEmbed,runFor_halted,branchCostRun_halted,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,PMF.pure_map]
    | inr s =>
      simp only [receiptEmbed,Sum.map_inr,runFor,tick,receiptMacroNext,branchCostRun,branchCostTick,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,PMF.map_bind,PMF.bind_map,PMF.map_comp,Function.comp_def]
      congr 1
      funext z
      obtain ⟨cfg,b⟩ := z
      change (runFor (receiptMacroNext next) n (receiptEmbed (cfg,a+b))).map Prod.fst = _
      rw [ih]
      congr 1
      funext z
      simp only [Nat.add_assoc,receiptEmbed]

def receiptUnboundedLaw (next : S→PMF ((O⊕S)×ℕ)) (s : S) : PMF (Option (O×ℕ)) :=
  (generalUnboundedLaw (receiptMacroNext next) (.inr (s,0))).map (Option.map Prod.fst)

theorem tsum_option_ennreal {α : Type} (F : Option α→ℝ≥0∞) :
    (∑' z : Option α, F z)=F none+∑' a : α, F (some a) := by
  let e := Equiv.optionEquivSumPUnit α
  calc
    _ = ∑' z : α⊕PUnit, F (e.symm z) := (e.symm.tsum_eq F).symm
    _ = (∑' a : α, F (some a))+F none := by
      rw [tsum_sum_type']
      simp [e]
    _ = _ := add_comm _ _

theorem receiptUnboundedLaw_never (next : S→PMF ((O⊕S)×ℕ)) (s : S) :
    receiptUnboundedLaw next s none = generalNeverMass (receiptMacroNext next) (.inr (s,0)) := by
  rw [receiptUnboundedLaw,PMF.map_apply,tsum_option_ennreal]
  simp [generalUnboundedLaw_apply,generalUnboundedMass]

theorem receiptUnboundedLaw_some (next : S→PMF ((O⊕S)×ℕ)) (s : S) (o : O) (k : ℕ) :
    receiptUnboundedLaw next s (some (o,k)) =
      ∑' t : ℕ, haltJoint (receiptMacroNext next) (.inr (s,0)) (o,k) t := by
  rw [receiptUnboundedLaw,PMF.map_apply,tsum_option_ennreal]
  simp only [Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq,if_false,zero_add]
  rw [tsum_prod_type']
  rw [tsum_eq_single (o,k)]
  · simp only [if_true,generalUnboundedLaw_apply,generalUnboundedMass]
  · intro z hz
    simp [Ne.symm hz]

theorem receiptUnboundedLaw_conservation (next : S→PMF ((O⊕S)×ℕ)) (s : S) :
    (∑' z : O×ℕ, receiptUnboundedLaw next s (some z)) +
      generalNeverMass (receiptMacroNext next) (.inr (s,0)) = 1 := by
  rw [← receiptUnboundedLaw_never]
  have h := (receiptUnboundedLaw next s).tsum_coe
  rw [tsum_option_ennreal] at h
  simpa only [add_comm] using! h

def quantumReceiptLaw {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ) (c : C) (ρ : ClockDensity D) :
    PMF (Option ((O×ClockDensity D)×ℕ)) :=
  receiptUnboundedLaw (mixedNext I dest price) (c,ρ)

theorem quantumReceiptLaw_conservation {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ) (c : C) (ρ : ClockDensity D) :
    (∑' z : (O×ClockDensity D)×ℕ, quantumReceiptLaw I dest price c ρ (some z)) +
      generalNeverMass (receiptMacroNext (mixedNext I dest price)) (.inr ((c,ρ),0)) = 1 :=
  receiptUnboundedLaw_conservation (mixedNext I dest price) (c,ρ)

theorem finite_event_trace {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : Operator D) (Ev : (O⊕C)×ℕ→Prop) :
    (Matrix.trace (finiteEventMap I dest price n c Ev ρ)).re=finiteEventProb I dest price n c ρ Ev :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.eventBranchMap_trace_re _ _ _

def compiledReceiptLaw {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) : CostedLaw (O⊕C) :=
  (instrumentPMF (pathInstrument I dest n c) ρ.property).map (leafRecord dest price n c)

theorem compiled_event_mass {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (Ev : (O⊕C)×ℕ→Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (compiledReceiptLaw I dest price n c ρ) Ev =
      ENNReal.ofReal (finiteEventProb I dest price n c ρ.val Ev) := by
  rw [compiledReceiptLaw,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype]
  simp only [instrumentPMF_apply,finiteEventProb,Qatlib.Concepts.StoppingCore.InterruptBridge.eventProb]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun p _ => instrumentProb_nonneg (pathInstrument I dest n c) ρ.property.1 p)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases he : Ev (leafRecord dest price n c p) <;> simp [he]

def forgetPostReceipt {C O Q : Type} (z : ((O×Q)⊕(C×Q))×ℕ) : (O⊕C)×ℕ :=
  (z.1.map Prod.fst Prod.fst,z.2)

theorem forgetPost_halt_point {C O Q : Type} (p : CostedLaw ((O×Q)⊕(C×Q))) (o : O) (k : ℕ) :
    (p.map forgetPostReceipt) (.inl o,k) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.2=k ∧ ∃ q : Q, z.1=.inl (o,q)) := by
  rw [← GeneralExecution.event_point_mass,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro z
  obtain ⟨cfg,a⟩ := z
  cases cfg with
  | inl out =>
    obtain ⟨out,q⟩ := out
    simp [forgetPostReceipt,Prod.mk.injEq,eq_comm,and_comm]
  | inr c => simp [forgetPostReceipt]

theorem compiled_halt_point {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (o : O) (k : ℕ) :
    compiledReceiptLaw I dest price n c ρ (.inl o,k) =
      ((branchCostRun (mixedNext I dest price) n (.inr (c,ρ))).map forgetPostReceipt) (.inl o,k) := by
  classical
  rw [forgetPost_halt_point,← mixedHaltMap_event I dest price n k c o ρ]
  rw [← GeneralExecution.event_point_mass,compiled_event_mass,← finite_event_trace,
    finite_event_mixedHaltMap]

theorem event_halt_decompose (p : CostedLaw (O⊕S)) (E : O×ℕ→Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (haltPredicate E) =
      ∑' o : O, ∑' k : ℕ, if E (o,k) then p (.inl o,k) else 0 := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_prod_type',tsum_sum_type']
  simp only [haltPredicate,if_false,mul_zero,tsum_zero,add_zero]
  apply tsum_congr
  intro o
  apply tsum_congr
  intro k
  by_cases he : E (o,k) <;> simp [he]

theorem finiteHaltEvent_probability {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (E : O×ℕ→Prop) :
    ENNReal.ofReal ((Matrix.trace (finiteHaltEvent I dest price n c E ρ.val)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) n (.inr (c,ρ)))
        (fun z => haltPredicate E (forgetPostReceipt z)) := by
  rw [finiteHaltEvent,finite_event_trace,← compiled_event_mass]
  rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map (branchCostRun (mixedNext I dest price) n (.inr (c,ρ)))
    forgetPostReceipt (haltPredicate E)]
  rw [event_halt_decompose,event_halt_decompose]
  apply tsum_congr
  intro o
  apply tsum_congr
  intro k
  by_cases he : E (o,k) <;> simp only [he,if_true,if_false]
  exact compiled_halt_point I dest price n c ρ o k

def optionEvent {A : Type} (E : A→Prop) (z : Option A) : Prop := z.elim False E

theorem option_event_mass {A : Type} (p : PMF (Option A)) (E : A→Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (optionEvent E) = ∑' a, if E a then p (some a) else 0 := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_option_ennreal]
  simp only [optionEvent,Option.elim_none,if_false,mul_zero,zero_add,Option.elim_some]
  apply tsum_congr
  intro a
  by_cases he : E a <;> simp [he]

theorem receipt_event_mass (next : S→PMF ((O⊕S)×ℕ)) (s : S) (E : O×ℕ→Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (receiptUnboundedLaw next s) (optionEvent E) =
      ∑' out : O×ℕ, if E out then
        ∑' t, haltJoint (receiptMacroNext next) (.inr (s,0)) out t else 0 := by
  rw [option_event_mass]
  apply tsum_congr
  intro out
  obtain ⟨o,k⟩ := out
  rw [receiptUnboundedLaw_some]

theorem macro_event_tendsto (next : S→PMF (O⊕S)) (cfg : O⊕S) (E : O→Prop) :
    Filter.Tendsto
      (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next N cfg) (fun z => ∃ o, z.1=.inl o ∧ E o))
      Filter.atTop (nhds (∑' o, if E o then ∑' t, haltJoint next cfg o t else 0)) := by
  have hfinite (N : ℕ) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor next N cfg) (fun z => ∃ o, z.1=.inl o ∧ E o) =
        ∑ t ∈ Finset.range (N+1), ∑' o, if E o then haltJoint next cfg o t else 0 := by
    rw [costClock_finite_event]
    calc
      _ = ∑' o, ∑ t ∈ Finset.range (N+1), if E o then haltJoint next cfg o t else 0 := by
        apply tsum_congr
        intro o
        by_cases he : E o <;> simp [he]
      _ = _ := Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
  have hinfinite : (∑' o, if E o then ∑' t, haltJoint next cfg o t else 0) =
      ∑' t, ∑' o, if E o then haltJoint next cfg o t else 0 := by
    calc
      _ = ∑' o, ∑' t, if E o then haltJoint next cfg o t else 0 := by
        apply tsum_congr
        intro o
        by_cases he : E o <;> simp [he]
      _ = _ := ENNReal.tsum_comm
  simp_rw [hfinite,hinfinite]
  exact (ENNReal.tendsto_nat_tsum (fun t => ∑' o, if E o then haltJoint next cfg o t else 0)).comp
    (Filter.tendsto_add_atTop_nat 1)

theorem receipt_finite_event (next : S→PMF ((O⊕S)×ℕ)) (s : S) (N : ℕ) (E : O×ℕ→Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (receiptMacroNext next) N (.inr (s,0)))
      (fun z => ∃ out, z.1=.inl out ∧ E out) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun next N (.inr s)) (haltPredicate E) := by
  let P : (O×ℕ)⊕(S×ℕ)→Prop := fun cfg => ∃ out, cfg=.inl out ∧ E out
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (receiptMacroNext next) N (receiptEmbed (.inr s,0)))
    (fun z => P z.1) = _
  rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map _ Prod.fst P,receipt_macro_projection,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
  intro z
  obtain ⟨cfg,k⟩ := z
  cases cfg <;> simp [P,receiptEmbed,haltPredicate]

theorem receipt_event_tendsto (next : S→PMF ((O⊕S)×ℕ)) (s : S) (E : O×ℕ→Prop) :
    Filter.Tendsto
      (fun N => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun next N (.inr s)) (haltPredicate E))
      Filter.atTop (nhds (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (receiptUnboundedLaw next s) (optionEvent E))) := by
  rw [receipt_event_mass]
  have h := macro_event_tendsto (receiptMacroNext next) (.inr (s,0)) E
  simpa only [receipt_finite_event] using! h

theorem haltEventLimit_probability {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (ρ : ClockDensity D) (E : O×ℕ→Prop) :
    ENNReal.ofReal ((Matrix.trace (haltEventLimit I dest price c E ρ.val)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (quantumReceiptLaw I dest price c ρ)
        (optionEvent (fun out => E (out.1.1,out.2))) := by
  have hcp := ENNReal.tendsto_ofReal (Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_matrix_trace (haltEventLimit_tendsto I dest price c E ρ.val)))
  have hlaw := receipt_event_tendsto (mixedNext I dest price) (c,ρ)
    (fun out => E (out.1.1,out.2))
  have heq (N : ℕ) :
      ENNReal.ofReal ((Matrix.trace (finiteHaltEvent I dest price N c E ρ.val)).re) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) N (.inr (c,ρ)))
          (haltPredicate (fun out => E (out.1.1,out.2))) := by
    rw [finiteHaltEvent_probability]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
    intro z
    obtain ⟨cfg,k⟩ := z
    cases cfg <;> rfl
  exact tendsto_nhds_unique hcp (hlaw.congr' (Filter.Eventually.of_forall fun N => (heq N).symm))

theorem stateCost_check_iff {C : Type} [Fintype C] [DecidableEq C] (cost : C→ℕ) :
    Qatlib.Concepts.StoppingCore.InterruptBridge.nonZenoCheck cost=true ↔ ∀ c, 0 < cost c :=
  Qatlib.Concepts.AdversaryBounds.AdvDuality.clause14_nonZenoCheck_iff C cost

theorem stateCost_positive_stabilization {C L O : Type} [Fintype C] [DecidableEq C] [Fintype L]
    [Fintype O] [DecidableEq O] {D : ℕ} (I : C→Instrument L D D) (dest : C→L→O⊕C) (cost : C→ℕ)
    (hc : Qatlib.Concepts.StoppingCore.InterruptBridge.nonZenoCheck cost=true)
    (n k : ℕ) (c : C) (o : O) (hk : k≤n) :
    mixedHaltMap I dest (fun c _ => cost c) n c o k = mixedHaltMap I dest (fun c _ => cost c) k c o k :=
  mixed_instrument_positive_clock_stabilization C L O D I dest (fun c _ => cost c)
    (fun c _ => (stateCost_check_iff cost).mp hc c) n k c o hk

def normalizeJoint {J : Type} [Fintype J] (A : Matrix J J ℂ) : Matrix J J ℂ :=
  if 0 < (Matrix.trace A).re then ((Matrix.trace A).re : ℂ)⁻¹ • A else 0

theorem psd_trace_real {J : Type} [Fintype J] [DecidableEq J] (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    Matrix.trace A = ((Matrix.trace A).re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (RCLike.nonneg_iff.mp hA.trace_nonneg).2

theorem psd_re_trace_zero {J : Type} [Fintype J] [DecidableEq J] (A : Matrix J J ℂ)
    (hA : A.PosSemidef) (h0 : (Matrix.trace A).re=0) : A=0 := by
  apply (Matrix.PosSemidef.trace_eq_zero_iff hA).mp
  rw [psd_trace_real A hA,h0,Complex.ofReal_zero]

theorem normalizeJoint_reconstruct {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : A.PosSemidef) :
    ((Matrix.trace A).re : ℂ) • normalizeJoint A = A := by
  by_cases hp : 0 < (Matrix.trace A).re
  · rw [normalizeJoint,if_pos hp,smul_smul,mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hp),one_smul]
  · have hz : (Matrix.trace A).re=0 := le_antisymm (not_lt.mp hp) (RCLike.nonneg_iff.mp hA.trace_nonneg).1
    rw [psd_re_trace_zero A hA hz]
    simp

theorem normalizeJoint_positive {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : A.PosSemidef) (hp : 0 < (Matrix.trace A).re) :
    (normalizeJoint A).PosSemidef ∧ Matrix.trace (normalizeJoint A)=1 := by
  rw [normalizeJoint,if_pos hp]
  constructor
  · apply hA.smul
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hp.le)
  · rw [Matrix.trace_smul,smul_eq_mul,psd_trace_real A hA]
    simp only [Complex.ofReal_re]
    exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hp)

theorem normalizeJoint_zero {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hA : A.PosSemidef) (h0 : (Matrix.trace A).re=0) :
    A=0 ∧ normalizeJoint A=0 := by
  have hz := psd_re_trace_zero A hA h0
  exact ⟨hz,by simp [normalizeJoint,h0]⟩

theorem tensorLeft_partialTrace {D E R : ℕ} (T : Operator D→ₗ[ℂ]Operator E)
    (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    PartialTrace (tensorLeft T X)=T (PartialTrace X) :=
  Qatlib.Concepts.TensorRegisters.RegisterModel.traceRight_local_linear T X

theorem tensorLeft_trace_marginal {D E R : ℕ} (T : Operator D→ₗ[ℂ]Operator E)
    (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    Matrix.trace (tensorLeft T X)=Matrix.trace (T (PartialTrace X)) := by
  rw [← trace_partialTrace (tensorLeft T X),tensorLeft_partialTrace]

theorem normalizeJoint_mixture {J K : Type} [Fintype J] [DecidableEq J] [DecidableEq K]
    (s : Finset K) (A : K→Matrix J J ℂ) (hA : ∀ i∈s, (A i).PosSemidef)
    (hq : 0 < (Matrix.trace (∑ i∈s,A i)).re) :
    normalizeJoint (∑ i∈s,A i) = ∑ i∈s,
      if 0 < (Matrix.trace (A i)).re then
        (((Matrix.trace (A i)).re / (Matrix.trace (∑ j∈s,A j)).re : ℝ) : ℂ) • normalizeJoint (A i)
      else 0 := by
  rw [normalizeJoint,if_pos hq,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : 0 < (Matrix.trace (A i)).re
  · rw [if_pos hp]
    calc
      _ = ((Matrix.trace (∑ j∈s,A j)).re : ℂ)⁻¹ •
          (((Matrix.trace (A i)).re : ℂ) • normalizeJoint (A i)) :=
        congrArg (fun B => ((Matrix.trace (∑ j∈s,A j)).re : ℂ)⁻¹ • B)
          (normalizeJoint_reconstruct (A i) (hA i hi)).symm
      _ = _ := by
        rw [smul_smul]
        congr 1
        push_cast
        ring
  · have hz : (Matrix.trace (A i)).re=0 :=
      le_antisymm (not_lt.mp hp) (RCLike.nonneg_iff.mp (hA i hi).trace_nonneg).1
    rw [if_neg hp,psd_re_trace_zero (A i) (hA i hi) hz,smul_zero]

theorem normalizeJoint_partialTrace {D R : ℕ} (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    PartialTrace (normalizeJoint X)=normalizeJoint (PartialTrace X) := by
  unfold normalizeJoint
  rw [trace_partialTrace]
  split_ifs
  · exact Matrix.traceRight_smul (A := X) (((Matrix.trace X).re : ℂ)⁻¹)
  · exact partialTrace_zero

theorem normalizeJoint_finiteEvent {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : Operator D) (Ev : (O⊕C)×ℕ→Prop) :
    normalizeJoint (finiteEventMap I dest price n c Ev ρ)=finitePost I dest price n c ρ Ev := by
  rw [normalizeJoint,finite_event_trace]
  rfl

theorem reference_event_mass {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    (Matrix.trace (tensorLeft (finiteEventMap I dest price n c Ev) X)).re =
      finiteEventProb I dest price n c (PartialTrace X) Ev := by
  rw [tensorLeft_trace_marginal,finite_event_trace]

theorem referencePost_memory {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    PartialTrace (normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X)) =
      finitePost I dest price n c (PartialTrace X) Ev := by
  rw [normalizeJoint_partialTrace,tensorLeft_partialTrace,normalizeJoint_finiteEvent]

theorem referencePost_path_mixture {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (htrace : Matrix.trace X=1)
    (hq : 0 < finiteEventProb I dest price n c (PartialTrace X) Ev) :
    normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X) =
      ∑ p ∈ Finset.univ.filter (fun p => Ev (leafRecord dest price n c p)),
        if 0 < pathProbability I dest n c ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ p then
          ((pathProbability I dest n c ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ p /
            finiteEventProb I dest price n c (PartialTrace X) Ev : ℝ) : ℂ) •
              normalizeJoint (tensorLeft ((pathInstrument I dest n c).branch p) X)
        else 0 := by
  let s := Finset.univ.filter (fun p => Ev (leafRecord dest price n c p))
  have hs : tensorLeft (finiteEventMap I dest price n c Ev) X =
      ∑ p∈s, tensorLeft ((pathInstrument I dest n c).branch p) X := by
    ext a b
    simp only [s,finiteEventMap,Qatlib.Concepts.StoppingCore.InterruptBridge.eventBranchMap,tensorLeft,
      LinearMap.sum_apply,Matrix.sum_apply]
  have hq' : 0 < (Matrix.trace (∑ p∈s, tensorLeft ((pathInstrument I dest n c).branch p) X)).re := by
    rw [← hs,reference_event_mass]
    exact hq
  have hmix := normalizeJoint_mixture s (fun p => tensorLeft ((pathInstrument I dest n c).branch p) X)
    (fun p _ => tensorLeft_posSemidef ((pathInstrument I dest n c).cp p) hX) hq'
  rw [← hs] at hmix
  have hp (p : Leaf dest n c) :
      (Matrix.trace (tensorLeft ((pathInstrument I dest n c).branch p) X)).re =
        pathProbability I dest n c ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ p := by
    rw [tensorLeft_trace_marginal]
    exact (pathProbability_eq I dest n c ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ p).symm
  simpa only [hp,reference_event_mass] using! hmix

theorem referencePost_zero {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (hq : finiteEventProb I dest price n c (PartialTrace X) Ev=0) :
    tensorLeft (finiteEventMap I dest price n c Ev) X=0 ∧
      normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X)=0 :=
  normalizeJoint_zero _ (tensorLeft_posSemidef (finite_event_cp I dest price n c Ev) hX)
    ((reference_event_mass I dest price n c Ev X).trans hq)

theorem referencePost_positive {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (hq : 0 < finiteEventProb I dest price n c (PartialTrace X) Ev) :
    (normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X)).PosSemidef ∧
      Matrix.trace (normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X))=1 :=
  normalizeJoint_positive _ (tensorLeft_posSemidef (finite_event_cp I dest price n c Ev) hX)
    (by rw [reference_event_mass]; exact hq)

theorem reference_event_reconstruct {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) :
    tensorLeft (finiteEventMap I dest price n c Ev) X =
      (finiteEventProb I dest price n c (PartialTrace X) Ev : ℂ) •
        normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X) := by
  have h :=
      normalizeJoint_reconstruct _ (tensorLeft_posSemidef (finite_event_cp I dest price n c Ev) hX)
  rw [reference_event_mass] at h
  exact h.symm

theorem reference_downstream {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (Ev : (O⊕C)×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef)
    (T : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ →ₗ[ℂ] Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) :
    T (tensorLeft (finiteEventMap I dest price n c Ev) X) =
      (finiteEventProb I dest price n c (PartialTrace X) Ev : ℂ) •
        T (normalizeJoint (tensorLeft (finiteEventMap I dest price n c Ev) X)) := by
  have h := congrArg T (reference_event_reconstruct I dest price n c Ev X hX)
  simpa only [map_smul] using! h

theorem normalizeJoint_tendsto {J : Type} [Fintype J] [DecidableEq J]
    (F : ℕ→Matrix J J ℂ) (A : Matrix J J ℂ)
    (h : Filter.Tendsto F Filter.atTop (nhds A)) (hq : 0 < (Matrix.trace A).re) :
    Filter.Tendsto (fun n => normalizeJoint (F n)) Filter.atTop (nhds (normalizeJoint A)) := by
  have hm := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_matrix_trace h)
  have he : ∀ᶠ n in Filter.atTop, 0 < (Matrix.trace (F n)).re :=
    hm.eventually (eventually_gt_nhds hq)
  have hc : Filter.Tendsto (fun n => ((Matrix.trace (F n)).re : ℂ)⁻¹) Filter.atTop
      (nhds (((Matrix.trace A).re : ℂ)⁻¹)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hm).inv₀ (by exact_mod_cast ne_of_gt hq)
  have hh : Filter.Tendsto (fun n => normalizeJoint (F n)) Filter.atTop
      (nhds (((Matrix.trace A).re : ℂ)⁻¹ • A)) := by
    apply (hc.smul h).congr'
    filter_upwards [he] with n hn
    rw [normalizeJoint,if_pos hn]
  simpa only [normalizeJoint,if_pos hq] using! hh

theorem referencePost_limit_tendsto {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hq : 0 < (Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re) :
    Filter.Tendsto (fun n => normalizeJoint (tensorLeft (finiteHaltEvent I dest price n c E) X)) Filter.atTop
      (nhds (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X))) :=
  normalizeJoint_tendsto _ _ (haltEventLimit_reference_tendsto I dest price c E R X) hq

theorem referencePost_limit_zero {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) (hX : X.PosSemidef)
    (hq : (Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re=0) :
    tensorLeft (haltEventLimit I dest price c E) X=0 ∧
      normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X)=0 :=
  normalizeJoint_zero _ (tensorLeft_posSemidef (haltEventLimit_cp I dest price c E) hX) hq

theorem referencePost_limit_positive {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ) (hX : X.PosSemidef)
    (hq : 0 < (Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re) :
    (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X)).PosSemidef ∧
      Matrix.trace (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X))=1 :=
  normalizeJoint_positive _ (tensorLeft_posSemidef (haltEventLimit_cp I dest price c E) hX) hq

namespace FullLaw

theorem sigma_pushforward_bind {A Z : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)]
    (p : PMF ((a : A) × B a)) (q : PMF A) (r : ∀ a, PMF (B a))
    (h : ∀ a b, p ⟨a,b⟩ = q a * r a b)
    (f : ((a : A) × B a) → Z) :
    p.map f = q.bind (fun a => (r a).map (fun b => f ⟨a,b⟩)) := by
  apply PMF.ext
  intro z
  simp only [PMF.map_apply,PMF.bind_apply,tsum_fintype]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hz : z = f ⟨a,b⟩ <;> simp [hz,h a b]

theorem feedForward_clock_mass {A : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)] {D : ℕ}
    (I : Instrument A D D) (J : ∀ a, Instrument (B a) D D)
    (ρ : ClockDensity D) (a : A) (b : B a) :
    instrumentProb (I.feedForward J) ρ.val ⟨a,b⟩ =
      instrumentProb I ρ.val a *
        instrumentProb (J a) (clockConditional I ρ a).val b := by
  rw [instrumentProb_feedForward,← clockConditional_reconstruct I ρ a,
    instrumentProb_smul_ofReal]

theorem feedForward_pmf_map {A Z : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)] {D : ℕ}
    (I : Instrument A D D) (J : ∀ a, Instrument (B a) D D)
    (ρ : ClockDensity D) (f : ((a : A) × B a) → Z) :
    (instrumentPMF (I.feedForward J) ρ.property).map f =
      (instrumentPMF I ρ.property).bind (fun a =>
        (instrumentPMF (J a) (clockConditional I ρ a).property).map
          (fun b => f ⟨a,b⟩)) := by
  apply sigma_pushforward_bind
  intro a b
  simp only [instrumentPMF_apply]
  rw [feedForward_clock_mass,
    ENNReal.ofReal_mul (instrumentProb_nonneg I ρ.property.1 a)]

theorem identity_pmf {D : ℕ} (ρ : ClockDensity D) :
    instrumentPMF (identityInstrument D) ρ.property = PMF.pure () := by
  apply PMF.ext
  intro u
  cases u
  simp [instrumentPMF_apply,instrumentProb,identityInstrument_branch,ρ.property.2]

variable {C L O : Type} [Fintype L] {D : ℕ}

def fullPathRecord (I : C → Instrument L D D) (dest : C → L → O⊕C)
    (price : C → L → ℕ) (n : ℕ) (c : C) (ρ : ClockDensity D)
    (p : Leaf dest n c) : ((O×ClockDensity D)⊕(C×ClockDensity D))×ℕ :=
  ((leafResult dest n c p).map
      (fun o => (o,pathPost I dest n c ρ p))
      (fun c' => (c',pathPost I dest n c ρ p)),
    leafCharge dest price n c p)

def fullPathLaw (I : C → Instrument L D D) (dest : C → L → O⊕C)
    (price : C → L → ℕ) (n : ℕ) (c : C) (ρ : ClockDensity D) :
    CostedLaw ((O×ClockDensity D)⊕(C×ClockDensity D)) :=
  (instrumentPMF (pathInstrument I dest n c) ρ.property).map
    (fullPathRecord I dest price n c ρ)

theorem mixed_run_succ (I : C → Instrument L D D) (dest : C → L → O⊕C)
    (price : C → L → ℕ) (n : ℕ) (c : C) (ρ : ClockDensity D) :
    branchCostRun (mixedNext I dest price) (n+1) (.inr (c,ρ)) =
      (instrumentPMF (I c) ρ.property).bind (fun l =>
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge (price c l)
          (branchCostRun (mixedNext I dest price) n
            ((dest c l).map (fun o => (o,clockConditional (I c) ρ l))
              (fun c' => (c',clockConditional (I c) ρ l))))) := by
  simp only [branchCostRun,branchCostTick,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,mixedNext,mixedReceipt,
    PMF.bind_map,Function.comp_def]

theorem fullPathLaw_eq (I : C → Instrument L D D) (dest : C → L → O⊕C)
    (price : C → L → ℕ) (n : ℕ) (c : C) (ρ : ClockDensity D) :
    fullPathLaw I dest price n c ρ =
      branchCostRun (mixedNext I dest price) n (.inr (c,ρ)) := by
  induction n generalizing c ρ with
  | zero =>
      change (instrumentPMF (identityInstrument D) ρ.property).map
        (fullPathRecord I dest price 0 c ρ) = PMF.pure (.inr (c,ρ),0)
      rw [identity_pmf ρ]
      exact PMF.pure_map _ _
  | succ n ih =>

      let J : (b : O⊕C) →
          @Instrument (match b with | .inl _ => Unit | .inr c' => Leaf dest n c')
            (childFintype dest n b) D D :=
        fun b => match b with
          | .inl _ => identityInstrument D
          | .inr c' => pathInstrument I dest n c'
      letI : ∀ l : L, Fintype
          (match dest c l with | .inl _ => Unit | .inr c' => Leaf dest n c') :=
        fun l => childFintype dest n (dest c l)
      rw [fullPathLaw]
      change (instrumentPMF ((I c).feedForward (fun l => J (dest c l))) ρ.property).map
          (fullPathRecord I dest price (n+1) c ρ) = _
      refine (feedForward_pmf_map (I c) (fun l => J (dest c l)) ρ
        (fullPathRecord I dest price (n+1) c ρ)).trans ?_
      rw [mixed_run_succ]
      congr 1
      funext l
      let σ : ClockDensity D := clockConditional (I c) ρ l
      let P : (b : O⊕C) →
          (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ClockDensity D :=
        fun b => match (motive := ∀ b : O⊕C,
            (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ClockDensity D) b with
          | .inl _ => fun _ => σ
          | .inr c' => pathPost I dest n c' σ
      let R : (b : O⊕C) →
          (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → O⊕C :=
        fun b => match (motive := ∀ b : O⊕C,
            (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → O⊕C) b with
          | .inl out => fun _ => .inl out
          | .inr c' => leafResult dest n c'
      let K : (b : O⊕C) →
          (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℕ :=
        fun b => match (motive := ∀ b : O⊕C,
            (match b with | .inl _ => Unit | .inr c' => Leaf dest n c') → ℕ) b with
          | .inl _ => fun _ => 0
          | .inr c' => leafCharge dest price n c'
      have hchild (b : O⊕C) :
          (@instrumentPMF D D (match b with | .inl _ => Unit | .inr c' => Leaf dest n c')
            (childFintype dest n b) (J b) σ.val σ.property).map (fun p =>
            ((R b p).map (fun o => (o,P b p)) (fun c' => (c',P b p)),
              price c l + K b p)) =
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge (price c l)
              (branchCostRun (mixedNext I dest price) n
                (b.map (fun o => (o,σ)) (fun c' => (c',σ)))) := by
        cases b with
        | inl out =>
            simp [J,P,R,K,identity_pmf σ,branchCostRun_halted,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,PMF.pure_map]
        | inr c' =>
            calc
              _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge (price c l) (fullPathLaw I dest price n c' σ) := by
                simp only [fullPathLaw,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge,PMF.map_comp,Function.comp_def,
                  fullPathRecord,J,P,R,K]
              _ = _ := congrArg (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge (price c l)) (ih c' σ)

      simpa only [fullPathRecord,leafResult,leafCharge,pathPost,P,R,K,σ]
        using! hchild (dest c l)

end FullLaw

theorem compiledReceiptLaw_projection {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) :
    (FullLaw.fullPathLaw I dest price n c ρ).map forgetPostReceipt =
      compiledReceiptLaw I dest price n c ρ := by
  simp only [FullLaw.fullPathLaw,compiledReceiptLaw,PMF.map_comp]
  congr 1
  funext p
  unfold Function.comp forgetPostReceipt FullLaw.fullPathRecord leafRecord
  cases leafResult dest n c p <;> rfl

theorem finite_event_probability {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (ρ : ClockDensity D) (Ev : (O⊕C)×ℕ→Prop) :
    ENNReal.ofReal ((Matrix.trace (finiteEventMap I dest price n c Ev ρ.val)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedNext I dest price) n (.inr (c,ρ)))
        (fun z => Ev (forgetPostReceipt z)) := by
  rw [finite_event_trace,← compiled_event_mass,← compiledReceiptLaw_projection,
    FullLaw.fullPathLaw_eq,Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]

def budgetAccepted {C O : Type} (B : ℕ) (z : (O⊕C)×ℕ) : Prop :=
  match z.1 with | .inl _ => z.2≤B | .inr _ => False

def budgetOverflow {C O : Type} (B : ℕ) (z : (O⊕C)×ℕ) : Prop :=
  match z.1 with | .inl _ => B<z.2 | .inr _ => False

def pendingEvent {C O : Type} (z : (O⊕C)×ℕ) : Prop :=
  match z.1 with | .inl _ => False | .inr _ => True

theorem budget_partition {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (B : ℕ) (ρ : Operator D) :
    finiteEventMap I dest price n c (budgetAccepted B) ρ +
      finiteEventMap I dest price n c (budgetOverflow B) ρ +
        finiteEventMap I dest price n c pendingEvent ρ =
          (pathInstrument I dest n c).forget.map ρ := by
  simp only [finiteEventMap,Qatlib.Concepts.StoppingCore.InterruptBridge.eventBranchMap,
    LinearMap.sum_apply,Finset.sum_filter,Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  obtain ⟨cfg,k⟩ := leafRecord dest price n c p
  cases cfg <;> simp only [budgetAccepted,budgetOverflow,pendingEvent]
  · by_cases hk : k≤B
    · simp [hk,Nat.not_lt.mpr hk]
    · simp [hk,Nat.lt_of_not_ge hk]
  · simp

theorem budget_partition_probability {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (B : ℕ) (ρ : ClockDensity D) :
    finiteEventProb I dest price n c ρ.val (budgetAccepted B) +
      finiteEventProb I dest price n c ρ.val (budgetOverflow B) +
        finiteEventProb I dest price n c ρ.val pendingEvent = 1 := by
  have hh := congrArg (fun A : Operator D => (Matrix.trace A).re)
    (budget_partition I dest price n c B ρ.val)
  simpa only [Matrix.trace_add,Complex.add_re,finite_event_trace,
    Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.forget_apply,(pathInstrument I dest n c).total,ρ.property.2,Complex.one_re] using! hh

theorem haltEventLimit_reference_probability {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (htrace : Matrix.trace X=1) :
    ENNReal.ofReal ((Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (quantumReceiptLaw I dest price c
        ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩)
        (optionEvent (fun out => E (out.1.1,out.2))) := by
  rw [tensorLeft_trace_marginal]
  exact haltEventLimit_probability I dest price c
    ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ E

theorem reference_limit_downstream {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) {J : Type} [Fintype J]
    (T : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ→ₗ[ℂ]Matrix J J ℂ) :
    T (tensorLeft (haltEventLimit I dest price c E) X) =
      (((Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re : ℝ) : ℂ) •
        T (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X)) := by
  have h := congrArg T (normalizeJoint_reconstruct _
    (tensorLeft_posSemidef (haltEventLimit_cp I dest price c E) hX))
  simpa only [map_smul] using! h.symm

def referencePathMixture {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (htrace : Matrix.trace X=1) : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ :=
  ∑ p ∈ Finset.univ.filter (fun p => haltPredicate E (leafRecord dest price n c p)),
    if 0 < pathProbability I dest n c ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ p then
      ((pathProbability I dest n c ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩ p /
        finiteEventProb I dest price n c (PartialTrace X) (haltPredicate E) : ℝ) : ℂ) •
          normalizeJoint (tensorLeft ((pathInstrument I dest n c).branch p) X)
    else 0

theorem referencePathMixture_tendsto {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (htrace : Matrix.trace X=1)
    (hq : 0 < (Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re) :
    Filter.Tendsto (fun n => referencePathMixture I dest price n c E X hX htrace) Filter.atTop
      (nhds (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X))) := by
  have hmass := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_matrix_trace (haltEventLimit_reference_tendsto I dest price c E R X))
  have he : ∀ᶠ n in Filter.atTop,
      0 < finiteEventProb I dest price n c (PartialTrace X) (haltPredicate E) := by
    filter_upwards [hmass.eventually (eventually_gt_nhds hq)] with n hn
    change 0 < (Matrix.trace (tensorLeft (finiteHaltEvent I dest price n c E) X)).re at hn
    simpa only [finiteHaltEvent,reference_event_mass] using! hn
  apply (referencePost_limit_tendsto I dest price c E X hq).congr'
  filter_upwards [he] with n hn
  exact referencePost_path_mixture I dest price n c (haltPredicate E) X hX htrace hn

theorem haltEventLimit_total_never {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (ρ : ClockDensity D) :
    ENNReal.ofReal ((Matrix.trace (haltEventLimit I dest price c (fun _ => True) ρ.val)).re) +
      generalNeverMass (receiptMacroNext (mixedNext I dest price)) (.inr ((c,ρ),0)) = 1 := by
  rw [haltEventLimit_probability,option_event_mass]
  simpa only [if_true] using! quantumReceiptLaw_conservation I dest price c ρ

theorem finiteHaltEvent_never {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (step : C→L→C) (price : C→L→ℕ)
    (n : ℕ) (c : C) (E : O×ℕ→Prop) :
    finiteHaltEvent I (fun c l => .inr (step c l)) price n c E=0 := by
  induction n generalizing c E with
  | zero => exact finiteHaltEvent_zero I _ price c E
  | succ n ih =>
    rw [finiteHaltEvent_succ]
    apply Finset.sum_eq_zero
    intro l _
    simp only [ih,LinearMap.zero_comp]

theorem haltEventLimit_never {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (step : C→L→C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) :
    haltEventLimit I (fun c l => .inr (step c l)) price c E=0 := by
  apply LinearMap.ext
  intro ρ
  have h := haltEventLimit_tendsto I (fun c l => Sum.inr (step c l)) price c E ρ
  have hz : Filter.Tendsto
      (fun n => finiteHaltEvent I (fun c l => Sum.inr (step c l)) price n c E ρ)
      Filter.atTop (nhds (0 : Operator D)) := by
    simpa only [finiteHaltEvent_never,LinearMap.zero_apply] using!
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : Operator D)) Filter.atTop (nhds 0))
  exact tendsto_nhds_unique h hz

theorem quantum_never_loop {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (step : C→L→C) (price : C→L→ℕ)
    (c : C) (ρ : ClockDensity D) :
    @generalNeverMass ((C×ClockDensity D)×ℕ) ((O×ClockDensity D)×ℕ)
      (receiptMacroNext (mixedNext I (fun c l => .inr (step c l)) price)) (.inr ((c,ρ),0)) = 1 := by
  have h := @haltEventLimit_total_never C L O _ D I (fun c l => .inr (step c l)) price c ρ
  simpa only [haltEventLimit_never,LinearMap.zero_apply,Matrix.trace_zero,Complex.zero_re,
    ENNReal.ofReal_zero,zero_add] using! h

def retryDest (_ : Unit) (b : Bool) : Unit⊕Unit := if b then .inl () else .inr ()

theorem loopContinueMap_shift {D : ℕ} (I : Instrument Bool D D) (n : ℕ) (ρ : Operator D) :
    loopContinueMap I n (I.branch false ρ)=loopContinueMap I (n+1) ρ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [loopContinueMap_succ_apply] using! congrArg (I.branch false) ih

theorem retry_exact_layer {D : ℕ} (I : Instrument Bool D D) (price : Unit→Bool→ℕ) (n : ℕ) :
    exactEventLayer (fun _ => I) retryDest price n () (fun _ => True)=loopHaltAt I n := by
  apply LinearMap.ext
  intro ρ
  induction n generalizing ρ with
  | zero =>
    simp [exactEventLayer,retryDest,loopHaltAt,loopContinueMap]
  | succ n ih =>
    simp only [exactEventLayer,LinearMap.sum_apply]
    simp only [Fintype.sum_bool,retryDest,Bool.false_eq_true,if_false,if_true,
      LinearMap.comp_apply,LinearMap.zero_apply,zero_add]
    rw [ih,loopHaltAt_apply,loopHaltAt_apply,loopContinueMap_shift]

theorem retry_finite_map {D : ℕ} (I : Instrument Bool D D) (price : Unit→Bool→ℕ) (n : ℕ) :
    finiteHaltEvent (fun _ => I) retryDest price n () (fun _ => True)=loopPartialMap I n := by
  rw [← exactEventLayer_sum]
  simp only [retry_exact_layer,loopPartialMap]

theorem retry_limit_map {D : ℕ} (I : Instrument Bool D D) (price : Unit→Bool→ℕ) :
    haltEventLimit (fun _ => I) retryDest price () (fun _ => True)=loopTerminalMap I := by
  apply LinearMap.ext
  intro ρ
  have h := haltEventLimit_tendsto (fun _ => I) retryDest price () (fun _ => True) ρ
  simp only [retry_finite_map] at h
  exact tendsto_nhds_unique h (loopTerminalMap_tendsto I ρ)

theorem frontier1 {C L O : Type} [Fintype L] {D : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (ρ : ClockDensity D) (E : O×ℕ→Prop) :
    (∀ n, FullLaw.fullPathLaw I dest price n c ρ =
      branchCostRun (mixedNext I dest price) n (.inr (c,ρ))) ∧
    CompletelyPositive (haltEventLimit I dest price c E) ∧
    TraceNonIncreasing (haltEventLimit I dest price c E) ∧
    Filter.Tendsto (fun n => finiteHaltEvent I dest price n c E ρ.val) Filter.atTop
      (nhds (haltEventLimit I dest price c E ρ.val)) ∧
    ENNReal.ofReal ((Matrix.trace (haltEventLimit I dest price c E ρ.val)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (quantumReceiptLaw I dest price c ρ)
        (optionEvent (fun out => E (out.1.1,out.2))) ∧
    ENNReal.ofReal ((Matrix.trace (haltEventLimit I dest price c (fun _ => True) ρ.val)).re) +
      generalNeverMass (receiptMacroNext (mixedNext I dest price)) (.inr ((c,ρ),0)) = 1 :=
  ⟨fun n => FullLaw.fullPathLaw_eq I dest price n c ρ,
    haltEventLimit_cp I dest price c E,haltEventLimit_tni I dest price c E,
    haltEventLimit_tendsto I dest price c E ρ.val,haltEventLimit_probability I dest price c ρ E,
    haltEventLimit_total_never I dest price c ρ⟩

theorem frontier2 {C L O : Type} [Fintype L] {D R : ℕ}
    (I : C→Instrument L D D) (dest : C→L→O⊕C) (price : C→L→ℕ)
    (c : C) (E : O×ℕ→Prop) (X : Matrix (Fin D×Fin R) (Fin D×Fin R) ℂ)
    (hX : X.PosSemidef) (htrace : Matrix.trace X=1)
    (hq : 0 < (Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re) :
    ENNReal.ofReal ((Matrix.trace (tensorLeft (haltEventLimit I dest price c E) X)).re) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (quantumReceiptLaw I dest price c
        ⟨PartialTrace X,isDensityOperator_partialTrace hX htrace⟩)
        (optionEvent (fun out => E (out.1.1,out.2))) ∧
    (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X)).PosSemidef ∧
    Matrix.trace (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X))=1 ∧
    Filter.Tendsto (fun n => referencePathMixture I dest price n c E X hX htrace) Filter.atTop
      (nhds (normalizeJoint (tensorLeft (haltEventLimit I dest price c E) X))) :=
  ⟨haltEventLimit_reference_probability I dest price c E X hX htrace,
    (referencePost_limit_positive I dest price c E X hX hq).1,
    (referencePost_limit_positive I dest price c E X hX hq).2,
    referencePathMixture_tendsto I dest price c E X hX htrace hq⟩

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference
