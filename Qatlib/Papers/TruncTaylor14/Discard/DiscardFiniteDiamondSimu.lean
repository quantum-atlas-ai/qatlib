/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TruncTaylor14.Discard.DiscardFiniteDiamondStat
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Mathlib.Data.ENNReal.Inv
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
noncomputable section
namespace Qatlib.Papers.TruncTaylor14.DiscardCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator

local instance (priority := 10000) sourceAnswerProdProdFast {α β γ : Type} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] : DecidableEq ((α × β) × γ) :=
  @instDecidableEqProd (α × β) γ (@instDecidableEqProd α β _ _) _

private theorem sourceDiscardLinearIterate_channel {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (W : Matrix (J × Fin D) (J × Fin D) ℂ) (j₀ : J)
    (hW : W ∈ Matrix.unitaryGroup (J × Fin D) ℂ) (n : ℕ) :
    CompletelyPositive (sourceDiscardLinearIterate W j₀ n) ∧
      TracePreserving (sourceDiscardLinearIterate W j₀ n) := by
  have hs := sourceDiscardLinearMap_channel J D W j₀ hW
  induction n with
  | zero => exact ⟨(QuantumChannel.id D).completelyPositive, (QuantumChannel.id D).tracePreserving⟩
  | succ n ih =>
    refine ⟨ih.1.comp hs.1, ?_⟩
    intro X
    change Matrix.trace (sourceDiscardLinearIterate W j₀ n (sourceDiscardLinearMap W j₀ X)) = _
    rw [ih.2, hs.2]

theorem sourceDiscardFiniteDiamond : SourceDiscardFiniteDiamond := by
  intro J _ _ D h U j₀ t Λ k hU hHer hΛ ht
  (try simp only [])
  set r := max 1 (Nat.ceil (Λ * t / Real.log 2)) with hrdef
  have hrNat : 1 ≤ r := le_max_left _ _
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hrNat)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hτ0 : 0 ≤ t / (r : ℝ) := div_nonneg ht hrpos.le
  have hceil : Λ * t / Real.log 2 ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (Λ * t / Real.log 2))))
  have hsmall : (∑ j, |h j|) * |t / (r : ℝ)| ≤ Real.log 2 := by
    rw [abs_of_nonneg hτ0, ← mul_div_assoc, div_le_iff₀ hrpos]
    exact ((mul_le_mul_of_nonneg_right hΛ ht).trans
      ((div_le_iff₀ hlog).mp hceil)).trans_eq (mul_comm _ _)
  have hwf := (taylor_lcu_actual_prepare_select_and_counts_ln2 (I := Fin D) h j₀
    (t / (r : ℝ)) (sourceDiscardCutoffKey r k) hsmall).2.1
  have hW : sourceTaylorDiscardWorkspace h U j₀ (t / (r : ℝ))
      (sourceDiscardCutoffKey r k) ∈ Matrix.unitaryGroup _ ℂ :=
    relabelGate_mem_unitary (hwf.evaluate_unitary (taylorQuery_unitary U hU _)) _
  have hc := sourceDiscardLinearIterate_channel _
    (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)) hW r
  let T := sourceTaylorDiscardChannel h U j₀ t Λ k
  let V := conjBranch (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) t)
  have hε : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hdensity : ∀ (ref : ℕ) (ρ : Matrix (Fin D × Fin ref) (Fin D × Fin ref) ℂ),
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Matrix.traceNorm (tensorLeft (T - V) ρ) ≤ (1 / 2 : ℝ) ^ k := by
    intro ref ρ hρ htr
    have heH : (∑ j, (h j : ℂ) • TensorGate (U j) (1 : Operator ref)) =
        TensorGate (∑ j, (h j : ℂ) • U j) (1 : Operator ref) := by
      ext a b
      simp [TensorGate, Matrix.sum_apply, Finset.sum_mul, mul_assoc]
    have hu : ∀ j, TensorGate (U j) (1 : Operator ref) ∈ Matrix.unitaryGroup _ ℂ :=
      fun j => tensorGate_unitary (hU j) (Matrix.unitaryGroup _ ℂ).one_mem
    have hh : (∑ j, (h j : ℂ) • TensorGate (U j) (1 : Operator ref)).IsHermitian := by
      rw [heH]
      change (TensorGate _ _)ᴴ = _
      rw [tensorGate_conjTranspose, hHer.eq, Matrix.conjTranspose_one]
    have hm := (sourceDiscardActualSimulation J (Fin D × Fin ref) h
      (fun j => TensorGate (U j) (1 : Operator ref)) j₀ t Λ k hu hh hΛ ht).2.2 ρ hρ htr
    change Matrix.traceNorm ((ResetDiscardStepCorrected
      (sourceTaylorDiscardWorkspace h (fun j => TensorGate (U j) (1 : Operator ref)) j₀
        (t / (r : ℝ)) (sourceDiscardCutoffKey r k))
      (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀)))^[r] ρ -
      hamiltonianEvolution (∑ j, (h j : ℂ) • TensorGate (U j) (1 : Operator ref)) t * ρ *
      (hamiltonianEvolution (∑ j, (h j : ℂ) • TensorGate (U j) (1 : Operator ref)) t)ᴴ) ≤ _ at hm
    rw [sourceTaylorDiscardWorkspace_reference, heH, sourceTaylorReferenceEvolution,
      ← (sourceDiscardLinearMap_semantics _ D
        (sourceTaylorDiscardWorkspace h U j₀ (t / (r : ℝ)) (sourceDiscardCutoffKey r k))
        (taylorEmptyLabel J (sourceDiscardCutoffKey r k), (false, j₀))).2 ref r ρ] at hm
    change Matrix.traceNorm (tensorLeft T ρ - tensorLeft V ρ) ≤ _
    rw [tensorLeft_conjBranch]
    exact hm
  have hraw := finite_reference_density_error_to_raw D D (T - V) ((1 / 2 : ℝ) ^ k) hε hdensity
  have hdiam := (finiteDiamondNorm_le_iff_uniform D D (T - V)
    (2 * (1 / 2 : ℝ) ^ k) (mul_nonneg zero_le_two hε)).mpr hraw
  have hdist : finiteDiamondDistance T V ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    unfold finiteDiamondDistance
    apply (mul_le_mul_right hdiam (1 / 2 : ℝ≥0∞)).trans
    rw [ENNReal.ofReal_mul zero_le_two]
    norm_num only [ENNReal.ofReal_ofNat, one_div]
    rw [ENNReal.inv_mul_cancel_left (by norm_num) (by simp)]
  have hsource := sourceDiscardActualSimulation J (Fin D) h U j₀ t Λ k hU hHer hΛ ht
  exact ⟨hc.1, hc.2, hdist, hraw, hsource.1.1, hsource.1.2.1, hsource.1.2.2⟩

end Qatlib.Papers.TruncTaylor14.DiscardCore
