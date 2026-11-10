/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.StateConversion
import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveCompilation
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QueryComplexity.StateConversion
open scoped BigOperators Classical Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
set_option maxHeartbeats 300000 in
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option maxHeartbeats 400000 in
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.ModelSemantics Qatlib.Concepts.QueryComplexity.StateConversion
open MeasureTheory Set Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator Topology
set_option maxHeartbeats 600000 in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable section

def sourceAdaptiveDecodedCoherentSuccess {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (ρ σ : X → QState H) (ε : ℝ) (T : SourceAdaptive (SourceSpace n q H r))
    (U : Matrix (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r)
      (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r) ℂ) : Prop :=
  ∀ x, (Qatlib.Foundations.PureStateMath.Inner (U *ᵥ sourceAdaptivePure (sourceAlphabetOracle input x) T
    (sourceClean n q r hr false (ρ x)))
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin (max 1 (sourceAdaptiveLeaves T))))
      (sourceClean n q r hr true (σ x)))).re ≥ Real.sqrt (1-ε)
end
noncomputable section

theorem sourceAdaptive_decoded_resource_compilation :
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    let L := max 1 (sourceAdaptiveLeaves T)
    ∀ U : Matrix (Fin L × SourceSpace n q H r) (Fin L × SourceSpace n q H r) ℂ,
      U ∈ Matrix.unitaryGroup _ ℂ →
    ∃ (R : ℕ) (_hR : 0<R) (C : SourceWord (SourceSpace n q H R)),
      R = L*r*(n+1) ∧ L*r ≤ R ∧ sourceWordLegal C ∧
      sourceWordCalls C ≤ 2*sourceAdaptiveCalls T ∧
      sourceWordKnown C ≤ 2+2*sourceAdaptiveCalls T ∧
      let F := sourceTreeFrame (H := H) n q r L R
      Fᴴ*F=1 ∧ ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
      sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        (F *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by dsimp [L]; omega⟩ : Fin L)) ψ)=
      F *ᵥ (U *ᵥ sourceAdaptivePure (sourceAlphabetOracle input x) T ψ) := by
  intro X H _ _ _ _ _ n q r hr input T hT
  (try dsimp only)
  intro U hU
  obtain ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,hSim⟩ :=
    sourceAdaptive_resource_compilation X H n q r hr input T hT
  let F := sourceTreeFrame (H := H) n q r (max 1 (sourceAdaptiveLeaves T)) R
  have hFU : (F*U)ᴴ*(F*U)=1 := by
    rw [Matrix.conjTranspose_mul,← Matrix.mul_assoc,Matrix.mul_assoc Uᴴ Fᴴ F,hIso,
      Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  obtain ⟨G,hG,hGF⟩ := sourcePublic_isometry_transport F (F*U) hIso hFU
  refine ⟨R,hR,C++[.inl G],hReq,hsize,
    sourceWordLegal_append C [.inl G] hC ?_,?_,?_,hIso,?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hG
  · rw [sourceWordCalls_append]
    simpa [sourceWordCalls] using! hcalls
  · have hcount : sourceWordKnown (C++[.inl G]) = sourceWordKnown C+1 := by
      simp [sourceWordKnown,List.countP_append]
    rw [hcount]
    omega
  · intro x ψ
    rw [sourceWordMatrix_append]
    have hsingle : sourceWordMatrix (sourceAlphabetOracle input x) [.inl G] = G := by
      simp [sourceWordMatrix]
    rw [hsingle,← Matrix.mulVec_mulVec,(hSim x ψ).1,Matrix.mulVec_mulVec,hGF,
      ← Matrix.mulVec_mulVec]
end
noncomputable section

theorem sourceAdaptiveDecodedCoherentQ_le_twice_calls {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (T : SourceAdaptive (SourceSpace n q H r)) (hT : sourceAdaptiveLegal T)
    (U : Matrix (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r)
      (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r) ℂ)
    (hU : U ∈ Matrix.unitaryGroup _ ℂ)
    (hSuccess : sourceAdaptiveDecodedCoherentSuccess hr input ρ σ ε T U) :
    sourceCoherentQ input ρ σ ε ≤ (2*sourceAdaptiveCalls T : ℕ) := by
  obtain ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,hSim⟩ :=
    sourceAdaptive_decoded_resource_compilation X H n q r hr input T hT U hU
  apply le_trans (sourceCoherentQ_le_calls hR input ρ σ ε C hC ?_)
  · exact_mod_cast hcalls
  intro x
  have hL : 0 < max 1 (sourceAdaptiveLeaves T) := by omega
  have hin := sourceTreeFrame_clean n q r _ R hr hL hR hsize false (ρ x)
  have hout := sourceTreeFrame_clean n q r _ R hr hL hR hsize true (σ x)
  have hs := hSim x (sourceClean n q r hr false (ρ x))
  rw [hin] at hs
  change (Qatlib.Foundations.PureStateMath.Inner _ _).re ≥ _
  rw [hs,← hout,sourceTreeFrame_inner n q r _ R hsize]
  exact hSuccess x
end
noncomputable section
def sourceAdaptiveDecodedCoherentCost {X H : Type} [Fintype H] [DecidableEq H]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (r : ℕ) (hr : 0<r) (T : SourceAdaptive (SourceSpace n q H r))
    (_ : sourceAdaptiveLegal T)
    (U : Matrix (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r)
      (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r) ℂ)
    (_ : U ∈ Matrix.unitaryGroup _ ℂ)
    (_ : sourceAdaptiveDecodedCoherentSuccess hr input ρ σ ε T U),
    (sourceAdaptiveCalls T : ℝ≥0∞)
end
noncomputable section

theorem sourceAdaptiveDecodedCoherentCost_le_sourceCoherentQ {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceAdaptiveDecodedCoherentCost input ρ σ ε ≤ sourceCoherentQ input ρ σ ε := by
  apply le_sInf
  rintro b ⟨r,hr,C,hb,hC,hs⟩
  rw [hb]
  unfold sourceAdaptiveDecodedCoherentCost
  apply iInf_le_of_le r
  apply iInf_le_of_le hr
  apply iInf_le_of_le (sourceWordAdaptive C)
  apply iInf_le_of_le (sourceWordAdaptive_legal C hC)
  apply iInf_le_of_le 1
  apply iInf_le_of_le (show (1 : Matrix _ _ ℂ) ∈ Matrix.unitaryGroup _ ℂ from by simp)
  have hsuccess : sourceAdaptiveDecodedCoherentSuccess hr input ρ σ ε (sourceWordAdaptive C) 1 := by
    intro x
    simpa only [Matrix.one_mulVec] using! sourceWordAdaptive_coherent_success hr input ρ σ ε C hs x
  apply iInf_le_of_le hsuccess
  rw [sourceWordAdaptive_calls]
end
noncomputable section

theorem sourceCoherentQ_le_twice_decodedAdaptiveCost {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceCoherentQ input ρ σ ε ≤ 2*sourceAdaptiveDecodedCoherentCost input ρ σ ε := by
  unfold sourceAdaptiveDecodedCoherentCost
  simp_rw [ENNReal.mul_iInf_of_ne (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp)]
  refine le_iInf fun r => le_iInf fun hr => le_iInf fun T => le_iInf fun hT =>
    le_iInf fun U => le_iInf fun hU => le_iInf fun hs => ?_
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using!
    sourceAdaptiveDecodedCoherentQ_le_twice_calls hr input ρ σ ε T hT U hU hs
end
noncomputable section

def sourceRetainedRecordSwapEquiv (S : Type) [Fintype S] [DecidableEq S] :
    (Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))) × S) ≃
      (Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))) × S) :=
  (Equiv.swap ⟨0,by simp [sourceRetainedRecordTree_leaves]⟩
    ⟨1,by simp [sourceRetainedRecordTree_leaves]⟩).prodCongr (Equiv.refl S)
end
noncomputable section
def sourceRetainedRecordSwap (S : Type) [Fintype S] [DecidableEq S] :=
  permMatrix (sourceRetainedRecordSwapEquiv S)
end
noncomputable section

theorem sourceRetainedRecordSwap_unitary (S : Type) [Fintype S] [DecidableEq S] :
    sourceRetainedRecordSwap S ∈ Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary_of_injective (Equiv.injective _)
end
noncomputable section

theorem sourceRetainedRecordSwap_clear (S : Type) [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (ψ : QState S) :
    sourceRetainedRecordSwap S *ᵥ sourceAdaptivePure O (sourceRetainedRecordTree S) ψ =
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by simp [sourceRetainedRecordTree_leaves]⟩ :
        Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))))) ψ := by
  rw [sourceRetainedRecordSwap,sourcePermMatrix_equiv_mulVec]
  ext ⟨l,s⟩
  have hl : l.val < 2 := by
    simpa only [sourceRetainedRecordTree_leaves,Nat.max_eq_right (by decide : 1≤2)] using! l.isLt
  have hc : l = ⟨0,by simp [sourceRetainedRecordTree_leaves]⟩ ∨
      l = ⟨1,by simp [sourceRetainedRecordTree_leaves]⟩ := by
    have hv : l.val=0 ∨ l.val=1 := by omega
    exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  rcases hc with rfl | rfl <;>
    simp [sourceRetainedRecordSwapEquiv,sourceRetainedRecordTree_pure,TensorState,Qatlib.Foundations.PureStateMath.Ket]
end
noncomputable section

theorem sourceRetainedRecordSwap_overlap (S : Type) [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (ψ : QState S) (hψ : Normalized ψ) :
    Qatlib.Foundations.PureStateMath.Inner (sourceRetainedRecordSwap S *ᵥ sourceAdaptivePure O (sourceRetainedRecordTree S) ψ)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by simp [sourceRetainedRecordTree_leaves]⟩ :
        Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree S))))) ψ) = 1 := by
  rw [sourceRetainedRecordSwap_clear]
  exact (normalized_iff_inner_self _).mp (normalized_tensorState (normalized_ket _) hψ)
end
noncomputable section

def sourceRetainedRecordConversionTree {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) : SourceAdaptive (SourceSpace n q H r) :=
  .known (sourceFlipDataGate n q r 1) (sourceRetainedRecordTree (SourceSpace n q H r))
end
noncomputable section

theorem sourceRetainedRecordConversion_decoded {X H : Type} [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (ρ : X → QState H) (hρ : ∀ x,Normalized (ρ x)) :
    sourceAdaptiveLegal (sourceRetainedRecordConversionTree (H := H) n q r) ∧
    sourceAdaptiveCalls (sourceRetainedRecordConversionTree (H := H) n q r) = 0 ∧
    sourceRetainedRecordSwap (SourceSpace n q H r) ∈ Matrix.unitaryGroup _ ℂ ∧
    sourceAdaptiveDecodedCoherentSuccess hr input ρ ρ 0
      (sourceRetainedRecordConversionTree n q r) (sourceRetainedRecordSwap (SourceSpace n q H r)) := by
  refine ⟨⟨sourceFlipDataGate_unitary n q r 1 (by simp),sourceRetainedRecordTree_legal _⟩,
    sourceRetainedRecordTree_calls _,sourceRetainedRecordSwap_unitary _,?_⟩
  intro x
  change (Qatlib.Foundations.PureStateMath.Inner (sourceRetainedRecordSwap (SourceSpace n q H r) *ᵥ
    sourceAdaptivePure (sourceAlphabetOracle input x) (sourceRetainedRecordTree (SourceSpace n q H r))
      (sourceFlipDataGate n q r 1 *ᵥ sourceClean n q r hr false (ρ x)))
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by simp [sourceRetainedRecordTree_leaves]⟩ :
      Fin (max 1 (sourceAdaptiveLeaves (sourceRetainedRecordTree (SourceSpace n q H r))))))
      (sourceClean n q r hr true (ρ x)))).re ≥ Real.sqrt (1-0)
  rw [sourceFlipDataGate_clean,Matrix.one_mulVec,sourceRetainedRecordSwap_overlap _ _ _
    (sourceClean_normalized n q r hr true (ρ x) (hρ x))]
  norm_num
end
noncomputable section

theorem sourceAdaptiveDecoded_normalized_comparison {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hρ : ∀ x,Normalized (ρ x)) :
    sourceAdaptiveDecodedCoherentCost input ρ σ ε ≤ sourceCoherentQ input ρ σ ε ∧
      sourceCoherentQ input ρ σ ε ≤ 2*sourceAdaptiveDecodedCoherentCost input ρ σ ε := by
  refine ⟨sourceAdaptiveDecodedCoherentCost_le_sourceCoherentQ input ρ σ ε,?_⟩
  cases isEmpty_or_nonempty X with
  | inl hX =>
    letI := hX
    rw [(sourceWordCosts_empty_input input ρ σ ε).1]
    exact bot_le
  | inr hX =>
    letI := hX
    haveI : Nonempty H := by
      by_contra hn
      haveI : IsEmpty H := not_nonempty_iff.mp hn
      have hnρ := hρ (Classical.choice hX)
      simp [Normalized] at hnρ
    exact sourceCoherentQ_le_twice_decodedAdaptiveCost input ρ σ ε
end
noncomputable section

theorem sourceCoherent_raw_from_output {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q r : ℕ}
    (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (out : X → QState (SourceSpace n q H r)) (δ η : ℝ)
    (hOut : ∀ x, Normalized (out x)) (hσ : ∀ x, Normalized (σ x))
    (hδ : 0≤δ) (hδ1 : δ≤1) (hbound : 2*Real.sqrt (2*δ)≤η)
    (hSuccess : ∀ x, (Qatlib.Foundations.PureStateMath.Inner (out x) (sourceClean n q r hr true (σ x))).re ≥ Real.sqrt (1-δ)) :
    sourceQDelta input η (gramStateMatrix ρ) (gramStateMatrix σ) ≤
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix out) (sourceAlphabetDelta input) := by
  have hnear : sourceUnfiltered (gramStateMatrix out-gramStateMatrix σ) ≤ ENNReal.ofReal η := by
    rw [← sourceGram_clean_gram n q r hr true σ]
    exact (generalOutputGramBridges.2.1 X (SourceSpace n q H r) out
      (fun x => sourceClean n q r hr true (σ x)) δ
      (fun x => ⟨hOut x,sourceClean_normalized n q r hr true _ (hσ x)⟩)
      hδ hδ1 hSuccess).trans (ENNReal.ofReal_le_ofReal hbound)
  let τ : {T : Matrix X X ℂ // T.PosSemidef ∧
      sourceUnfiltered (T-gramStateMatrix σ) ≤ ENNReal.ofReal η} :=
    ⟨gramStateMatrix out,gramStateMatrix_posSemidef out,hnear⟩
  exact iInf_le (fun T : {T : Matrix X X ℂ // T.PosSemidef ∧
      sourceUnfiltered (T-gramStateMatrix σ) ≤ ENNReal.ofReal η} =>
      sourceRectValue (gramStateMatrix ρ-T.1) (sourceAlphabetDelta input)) τ
end
noncomputable section

theorem sourceNoncoherent_raw_from_output {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q r : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (out : X → QState (SourceSpace n q H r)) (δ η : ℝ)
    (hOut : ∀ x, Normalized (out x)) (hσ : ∀ x, Normalized (σ x))
    (hδ : 0≤δ) (hδ1 : δ≤1) (hbound : 2*Real.sqrt (2*δ)≤η)
    (hSuccess : ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ Real.sqrt (1-δ) ≤ ‖Qatlib.Foundations.PureStateMath.Inner (out x) (sourceGarbageTarget n q r (σ x) ξ)‖) :
    sourceQNoncoherentDelta input η (gramStateMatrix ρ) (gramStateMatrix σ) ≤
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix out) (sourceAlphabetDelta input) := by
  choose ξ hξ hOver using hSuccess
  let χ := fun x => sourceGarbageTarget n q r (σ x) (ξ x)
  let a := fun x => overlapPhase (Qatlib.Foundations.PureStateMath.Inner (out x) (χ x))
  let ξ' := fun x p => a x*ξ x p
  let χ' := fun x => sourceGarbageTarget n q r (σ x) (ξ' x)
  have hξ' (x : X) : Normalized (ξ' x) := normalized_phase (ξ x) (hξ x) (a x) (overlapPhase_norm _)
  have hχ' (x : X) : Normalized (χ' x) := sourceGarbageTarget_normalized (σ x) (ξ' x) (hσ x) (hξ' x)
  have hPhase (x : X) : Qatlib.Foundations.PureStateMath.Inner (out x) (χ' x)=(‖Qatlib.Foundations.PureStateMath.Inner (out x) (χ x)‖ : ℂ) := by
    calc
      _ = a x*Qatlib.Foundations.PureStateMath.Inner (out x) (χ x) := by
        simp only [Qatlib.Foundations.PureStateMath.inner_apply,χ',χ,ξ',sourceGarbageTarget]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = _ := overlapPhase_mul _
  have hOverlap (x : X) : (Qatlib.Foundations.PureStateMath.Inner (out x) (χ' x)).re≥Real.sqrt (1-δ) := by
    rw [hPhase,Complex.ofReal_re]
    exact hOver x
  let K := gramStateMatrix ξ'
  have hnear : sourceUnfiltered (gramStateMatrix out-gramStateMatrix σ ⊙ K)≤ENNReal.ofReal η := by
    rw [← sourceGarbageTarget_gram σ ξ']
    exact (generalOutputGramBridges.2.1 X (SourceSpace n q H r) out χ' δ
      (fun x => ⟨hOut x,hχ' x⟩) hδ hδ1 hOverlap).trans (ENNReal.ofReal_le_ofReal hbound)
  have hKPSD : K.PosSemidef := gramStateMatrix_posSemidef ξ'
  have hKdiag (x : X) : K x x=1 := (normalized_iff_inner_self _).mp (hξ' x)
  refine (iInf_le _ ⟨gramStateMatrix out,gramStateMatrix_posSemidef out⟩).trans ?_
  refine (iInf_le _ ⟨K,hKPSD,hKdiag⟩).trans ?_
  rw [if_pos hnear]
end
noncomputable section

theorem sourceCoherent_fixed_third_raw_upper {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) :
    sourceCoherentQ input ρ σ (1/3) ≤ (309237645312:ℝ≥0∞)*
      sourceQDelta input ((1/3:ℝ)^4/16) (gramStateMatrix ρ) (gramStateMatrix σ) := by
  set D := sourceQDelta input ((1/3:ℝ)^4/16) (gramStateMatrix ρ) (gramStateMatrix σ)
  by_cases hD : D=⊤
  · simp [hD]
  have hW : 0≤D.toReal := ENNReal.toReal_nonneg
  obtain ⟨r,hr,C,hC,hreal,hok⟩ := sourceCoherent_raw_budget_word input ρ σ (1/3) D.toReal
    hn (by norm_num) (by norm_num) hW (by rw [ENNReal.ofReal_toReal hD])
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hreal' : (sourceWordCalls C:ℝ) ≤ 309237645312*D.toReal := by
    norm_num at hreal hlog
    nlinarith [mul_le_mul_of_nonneg_left hlog hW]
  apply (sourceCoherentQ_le_calls hr input ρ σ (1/3) C hC hok).trans
  apply (sourceCalls_le_ofReal hreal').trans
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤309237645312),ENNReal.ofReal_toReal hD]
  norm_num
end
noncomputable section

theorem sourceNoncoherent_fixed_third_raw_upper {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) :
    sourceNoncoherentQ input ρ σ (1/3) ≤ (309237645312:ℝ≥0∞)*
      sourceQNoncoherentDelta input ((1/3:ℝ)^4/16) (gramStateMatrix ρ) (gramStateMatrix σ) := by
  set D := sourceQNoncoherentDelta input ((1/3:ℝ)^4/16) (gramStateMatrix ρ) (gramStateMatrix σ)
  by_cases hD : D=⊤
  · simp [hD]
  have hW : 0≤D.toReal := ENNReal.toReal_nonneg
  obtain ⟨r,hr,C,hC,hreal,hok⟩ := sourceNoncoherent_raw_budget_word input ρ σ (1/3) D.toReal
    hn (by norm_num) (by norm_num) hW (by rw [ENNReal.ofReal_toReal hD])
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : 0<(3:ℝ))
  have hreal' : (sourceWordCalls C:ℝ) ≤ 309237645312*D.toReal := by
    norm_num at hreal hlog
    nlinarith [mul_le_mul_of_nonneg_left hlog hW]
  apply (sourceNoncoherentQ_le_calls hr input ρ σ (1/3) C hC hok).trans
  apply (sourceCalls_le_ofReal hreal').trans
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤309237645312),ENNReal.ofReal_toReal hD]
  norm_num
end
noncomputable section

theorem source_fixed_error_radius :
    (2:ℝ)*Real.sqrt (2*(1/13436928)) ≤ (1/3:ℝ)^4/16 := by
  rw [show (2*(1/13436928):ℝ)=(1/2592:ℝ)^2 by norm_num,Real.sqrt_sq_eq_abs]
  norm_num
end
noncomputable section

theorem sourceCoherent_fixed_third_from_output {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ}
    (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (out : X → QState (SourceSpace n q H r))
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hOut : ∀ x, Normalized (out x))
    (hSuccess : ∀ x, (Qatlib.Foundations.PureStateMath.Inner (out x) (sourceClean n q r hr true (σ x))).re ≥ Real.sqrt (1-1/13436928)) :
    sourceCoherentQ input ρ σ (1/3) ≤ (309237645312:ℝ≥0∞)*
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix out) (sourceAlphabetDelta input) := by
  apply (sourceCoherent_fixed_third_raw_upper input ρ σ hn).trans
  exact mul_le_mul_of_nonneg_left (sourceCoherent_raw_from_output hr input ρ σ out
    (1/13436928) ((1/3)^4/16) hOut (fun x => (hn x).2)
    (by norm_num) (by norm_num) source_fixed_error_radius hSuccess) bot_le
end
noncomputable section

theorem sourceNoncoherent_fixed_third_from_output {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (out : X → QState (SourceSpace n q H r))
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) (hOut : ∀ x, Normalized (out x))
    (hSuccess : ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ Real.sqrt (1-1/13436928) ≤ ‖Qatlib.Foundations.PureStateMath.Inner (out x) (sourceGarbageTarget n q r (σ x) ξ)‖) :
    sourceNoncoherentQ input ρ σ (1/3) ≤ (309237645312:ℝ≥0∞)*
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix out) (sourceAlphabetDelta input) := by
  apply (sourceNoncoherent_fixed_third_raw_upper input ρ σ hn).trans
  exact mul_le_mul_of_nonneg_left (sourceNoncoherent_raw_from_output input ρ σ out
    (1/13436928) ((1/3)^4/16) hOut (fun x => (hn x).2)
    (by norm_num) (by norm_num) source_fixed_error_radius hSuccess) bot_le
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
