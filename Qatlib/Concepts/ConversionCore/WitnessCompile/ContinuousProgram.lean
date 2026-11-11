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
import Qatlib.Concepts.ConversionCore.WitnessCompile.ContinuousAnalysis
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveCompilation
import Qatlib.Concepts.ConversionCore.WitnessCompile.DecodedRecords
import Qatlib.Concepts.ConversionCore.WitnessCompile.ConversionBridges

/-!
# Continuous source programs and discrete query costs

Legal continuous source programs preserve normalization and have filtered Gram change at most
`1+π²` times their total query time. The proof telescopes the corresponding one-step bound
across the program.

The module also identifies compiled adaptive mixed-state channels and compares continuous state
conversion with discrete query complexity at explicit fixed errors. These bridges implement the
query-model comparisons studied in [LeeEtAl2011].

## Main statements

* `continuousConversion_source_program_distance`: the total-time filtered Gram bound.
* `sourceAdaptive_compiled_mixed_channel`: recovery of the adaptive channel after compilation.
* `stageB_state_conversion_clause93`: continuous and discrete complexity comparisons.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

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
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

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

/-- The matrix of a continuous source program beginning with `s` is the remaining-program matrix
multiplied by the single-step matrix. -/
theorem continuousConversion_source_cons {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (s : SourceContinuousStep S) (C : List (SourceContinuousStep S)) :
    sourceContinuousMatrix O (s :: C) = sourceContinuousMatrix O C * sourceContinuousMatrix O [s] := by
  simp [sourceContinuousMatrix,List.reverse_cons,List.prod_append]
end
noncomputable section

/-- A legal single continuous source step evaluated with the logarithmic alphabet oracle is
unitary. -/
theorem continuousConversion_source_single_unitary {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (s : SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W))
    (hs : sourceContinuousLegal [s]) :
    sourceContinuousMatrix (sourceLogOracle input x) [s] ∈ Matrix.unitaryGroup _ ℂ := by
  have h := hs s (List.mem_singleton_self s)
  cases s with
  | known U => simpa [sourceContinuousMatrix] using! h
  | evolve K T adj =>
    obtain ⟨hT,hKi,hKh⟩ := h
    have hO := (sourceLogOracle_hermitian_norm X W input x).1
    have hL : ∀ t ∈ Set.Icc 0 T,
        (K t + (if adj then -sourceLogOracle (W := W) input x else sourceLogOracle input x)).IsHermitian := by
      intro t ht
      cases adj
      · exact (hKh t ht).add hO
      · exact (hKh t ht).add hO.neg
    have hi : ∀ i j, IntervalIntegrable
        (fun t => (K t + (if adj then -sourceLogOracle (W := W) input x else sourceLogOracle input x)) i j)
        MeasureTheory.volume 0 T := by
      intro i j
      exact (hKi i j).add intervalIntegrable_const
    have hu := (volterraAndOracleLogSemantics.1 _
      (fun t => K t + (if adj then -sourceLogOracle (W := W) input x else sourceLogOracle input x))
      T hT hi hL).2
    simpa [sourceContinuousMatrix] using! hu
end
noncomputable section

/-- A legal continuous source program evaluated with the logarithmic alphabet oracle is unitary. -/
theorem continuousConversion_source_unitary {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (C : List (SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W)))
    (hC : sourceContinuousLegal C) :
    sourceContinuousMatrix (sourceLogOracle input x) C ∈ Matrix.unitaryGroup _ ℂ := by
  induction C with
  | nil => simp [sourceContinuousMatrix]
  | cons s C ih =>
    have ht : sourceContinuousLegal C := fun t ht => hC t (List.mem_cons_of_mem s ht)
    have hs : sourceContinuousLegal [s] :=
        fun t ht => hC t (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp ht)))
    rw [continuousConversion_source_cons]
    exact (Matrix.unitaryGroup _ ℂ).mul_mem (ih ht)
        (continuousConversion_source_single_unitary input x s hs)
end
noncomputable section

/-- A legal continuous source program has nonnegative total query time. -/
theorem continuousConversion_source_time_nonneg {S : Type}
    (C : List (SourceContinuousStep S)) [Fintype S] [DecidableEq S]
    (hC : sourceContinuousLegal C) : 0 ≤ sourceContinuousTime C := by
  unfold sourceContinuousTime
  apply List.sum_nonneg
  intro a ha
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
  cases s with
  | known U => exact le_rfl
  | evolve K T adj => exact (hC _ hs).1
end
noncomputable section

/-- A filtered Gram-change bound of `B` times query time for every legal single step extends to
every legal continuous source program. -/
theorem continuousConversion_source_telescope {X W : Type}
    [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (B : ℝ) (hB : 0 ≤ B)
    (hsingle : ∀ (s : SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W)),
      sourceContinuousLegal [s] →
      ∀ (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)), (∀ x, Normalized (ψ x)) →
      sourceRectValue (gramStateMatrix ψ - gramStateMatrix
        (fun x => sourceContinuousMatrix (sourceLogOracle input x) [s] *ᵥ ψ x))
        (sourceAlphabetDelta input) ≤ ENNReal.ofReal (B * sourceContinuousTime [s]))
    (C : List (SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W)))
    (hC : sourceContinuousLegal C)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    sourceRectValue (gramStateMatrix ψ - gramStateMatrix
      (fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ ψ x))
      (sourceAlphabetDelta input) ≤ ENNReal.ofReal (B * sourceContinuousTime C) := by
  induction C generalizing ψ with
  | nil => simp [sourceContinuousMatrix,sourceContinuousTime,sourceRectValue_zero]
  | cons s C ih =>
    have ht : sourceContinuousLegal C := fun t ht => hC t (List.mem_cons_of_mem s ht)
    have hs : sourceContinuousLegal [s] :=
        fun t ht => hC t (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp ht)))
    let φ := fun x => sourceContinuousMatrix (sourceLogOracle input x) [s] *ᵥ ψ x
    have hφ : ∀ x, Normalized (φ x) := fun x =>
      normalized_applyGate (continuousConversion_source_single_unitary input x s hs) (hψ x)
    have h₁ := hsingle s hs ψ hψ
    have h₂ := ih ht φ hφ
    have he : (gramStateMatrix ψ - gramStateMatrix
        (fun x => sourceContinuousMatrix (sourceLogOracle input x) (s::C) *ᵥ ψ x)) =
        (gramStateMatrix ψ - gramStateMatrix φ) +
        (gramStateMatrix φ - gramStateMatrix
          (fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ φ x)) := by
      have hr (x : X) : sourceContinuousMatrix (sourceLogOracle input x) (s::C) *ᵥ ψ x =
          sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ φ x := by
        rw [continuousConversion_source_cons,Matrix.mulVec_mulVec]
      rw [show (fun x => sourceContinuousMatrix (sourceLogOracle input x) (s::C) *ᵥ ψ x) =
        (fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ φ x) from funext hr]
      abel
    rw [he]
    apply (sourceRectValue_add_le _ _ _).trans
    apply (add_le_add h₁ h₂).trans
    rw [← ENNReal.ofReal_add (mul_nonneg hB (continuousConversion_source_time_nonneg [s] hs))
      (mul_nonneg hB (continuousConversion_source_time_nonneg C ht))]
    apply le_of_eq
    congr 1
    simp [sourceContinuousTime,mul_add]
end
noncomputable section

/-- Negating the target matrix leaves its rectangular filtered value unchanged. -/
theorem continuousConversion_source_neg_value {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) :
    sourceRectValue (-A) Z = sourceRectValue A Z := by
  simpa only [neg_one_smul, norm_neg, norm_one, ENNReal.ofReal_one, one_mul] using!
    sourceRectValue_smul A Z (-1 : ℂ)
end
noncomputable section

/-- For normalized input states, a legal continuous source program changes the Gram matrix by
filtered value at most `1+π²` times its total query time. -/
theorem continuousConversion_source_program_distance {X W : Type}
    [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (C : List (SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W)))
    (hC : sourceContinuousLegal C)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    sourceRectValue (gramStateMatrix ψ - gramStateMatrix
      (fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ ψ x))
      (sourceAlphabetDelta input) ≤ ENNReal.ofReal ((1+Real.pi^2) * sourceContinuousTime C) := by
  apply continuousConversion_source_telescope input (1+Real.pi^2) (by positivity) ?_ C hC ψ hψ
  intro s hs φ hφ
  have h := hs s (List.mem_singleton_self s)
  cases s with
  | known U =>
    have hg : gramStateMatrix (fun x => sourceContinuousMatrix (sourceLogOracle input x)
        [SourceContinuousStep.known U] *ᵥ φ x) = gramStateMatrix φ := by
      ext x y
      simpa only [sourceContinuousMatrix, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, Matrix.mul_one,
        gramStateMatrix, ApplyGate] using! Qatlib.Foundations.PureStateMath.inner_applyGate h (φ x) (φ y)
    rw [hg, sub_self, sourceRectValue_zero]
    exact zero_le
  | evolve K T adj =>
    obtain ⟨hT,hKi,hKh⟩ := h
    have hb := continuousConversion_source_evolve_distance input K T adj hT hKi hKh φ hφ
    have hn := continuousConversion_source_neg_value
      (gramStateMatrix (fun x => sourceVolterraMatrix (fun t => K t +
        (if adj then -sourceLogOracle input x else sourceLogOracle input x)) T *ᵥ φ x) -
        gramStateMatrix φ) (sourceAlphabetDelta input)
    rw [neg_sub] at hn
    simpa only [sourceContinuousMatrix, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, Matrix.mul_one,
      sourceContinuousTime, List.sum_cons, List.sum_nil, add_zero] using! hn.trans_le hb
end
noncomputable section

/-- The matrix map summing `A*D*Aᴴ` over all adaptive branch operators. -/
def sourceAdaptiveMixedChannel {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (T : SourceAdaptive S) (D : Matrix S S ℂ) : Matrix S S ℂ :=
  ((sourceAdaptiveOperators O T).map (fun A => A*D*Aᴴ)).sum
end
noncomputable section

/-- Tracing out the record after applying the adaptive pure matrix to an input matrix gives the
adaptive mixed channel. -/
theorem sourceAdaptive_trace_mixed_channel {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (T : SourceAdaptive S) (D : Matrix S S ℂ) :
    conversionTraceRecord (sourceAdaptivePureMatrix O T * D * (sourceAdaptivePureMatrix O T)ᴴ) =
      sourceAdaptiveMixedChannel O T D := by
  rw [conversionTraceRecord_frame]
  change (∑ i : Fin (max 1 (sourceAdaptiveLeaves T)),
    ((sourceAdaptiveOperators O T).getD i.val 0)*D*((sourceAdaptiveOperators O T).getD i.val 0)ᴴ) =
      ((sourceAdaptiveOperators O T).map (fun A => A*D*Aᴴ)).sum
  exact sourceList_sum_getD (sourceAdaptiveOperators O T) (0 : Matrix S S ℂ)
    (fun A => A*D*Aᴴ) (by simp) _
    (by rw [sourceAdaptive_operators_length]; exact le_max_right _ _)
end
noncomputable section

/-- Every legal adaptive computation has a resource-bounded word compilation whose output, after
pulling back through the tree frame and tracing out records, equals its mixed channel on
every input matrix. -/
theorem sourceAdaptive_compiled_mixed_channel :
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    let L := max 1 (sourceAdaptiveLeaves T)
    ∃ (R : ℕ) (_hR : 0<R) (C : SourceWord (SourceSpace n q H R)),
      R = L*r*(n+1) ∧ L*r ≤ R ∧ sourceWordLegal C ∧
      sourceWordCalls C ≤ 2*sourceAdaptiveCalls T ∧
      sourceWordKnown C ≤ 1+2*sourceAdaptiveCalls T ∧
      let F := sourceTreeFrame (H := H) n q r L R
      let J := sourceRecordInit (S := SourceSpace n q H r) L (by dsimp [L]; omega)
      Fᴴ*F=1 ∧ ∀ (x : X) (D : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ),
        let M := sourceWordMatrix (sourceAlphabetOracle input x) C
        conversionTraceRecord (Fᴴ*(M*((F*J)*D*(F*J)ᴴ)*Mᴴ)*F) =
          sourceAdaptiveMixedChannel (sourceAlphabetOracle input x) T D := by
  intro X H _ _ _ _ _ n q r hr input T hT
  obtain ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,hSim⟩ :=
    sourceAdaptive_resource_mixed_compilation X H n q r hr input T hT
  refine ⟨R,hR,C,hReq,hsize,hC,hcalls,hknown,hIso,?_⟩
  intro x D
  (try dsimp only)
  rw [(hSim x).2 D]
  rw [conversionTraceRecord_pullback _ hIso,← conversionTraceRecord_frame,
    sourceAdaptive_trace_mixed_channel]
end
noncomputable section

/-- The extended nonnegative constant `ENNReal.ofReal (309237645312*(1+π²))` used in
continuous-to-discrete fixed-error comparisons. -/
def sourceFixedContinuousOverhead : ℝ≥0∞ :=
  ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))
end
noncomputable section

/-- Multiplication of the time bound by `309237645312` factors through
`sourceFixedContinuousOverhead`. -/
theorem sourceFixedContinuousOverhead_mul_time (t : ℝ) :
    (309237645312:ℝ≥0∞)*ENNReal.ofReal ((1+Real.pi^2)*t) =
      sourceFixedContinuousOverhead*ENNReal.ofReal t := by
  unfold sourceFixedContinuousOverhead
  rw [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1+Real.pi^2),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤309237645312)]
  norm_num
  rw [mul_assoc]
end
noncomputable section

/-- A legal continuous program achieving coherent error `1/13436928` bounds coherent discrete
query complexity at error `1/3` by its total time times `sourceFixedContinuousOverhead`. -/
theorem sourceCoherent_fixed_continuous_program {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ}
    (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x))
    (C : List (SourceContinuousStep (SourceSpace n q H r))) (hC : sourceContinuousLegal C)
    (hSuccess : ∀ x, (Qatlib.Foundations.PureStateMath.Inner
      (sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ sourceClean n q r hr false (ρ x))
      (sourceClean n q r hr true (σ x))).re ≥ Real.sqrt (1-1/13436928)) :
    sourceCoherentQ input ρ σ (1/3) ≤ sourceFixedContinuousOverhead*ENNReal.ofReal (sourceContinuousTime C) := by
  let out :=
      fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ sourceClean n q r hr false (ρ x)
  have hnorm (x : X) : Normalized (out x) := normalized_applyGate
    (continuousConversion_source_unitary input x C hC)
    (sourceClean_normalized n q r hr false (ρ x) (hn x).1)
  have hQ := sourceCoherent_fixed_third_from_output hr input ρ σ out hn hnorm hSuccess
  have hD := continuousConversion_source_program_distance input C hC
    (fun x => sourceClean n q r hr false (ρ x))
    (fun x => sourceClean_normalized n q r hr false (ρ x) (hn x).1)
  rw [sourceGram_clean_gram] at hD
  exact (hQ.trans (mul_le_mul_of_nonneg_left hD bot_le)).trans_eq
    (sourceFixedContinuousOverhead_mul_time _)
end
noncomputable section

/-- A legal continuous program achieving noncoherent error `1/13436928` bounds noncoherent
discrete query complexity at error `1/3` by its total time times
`sourceFixedContinuousOverhead`. -/
theorem sourceNoncoherent_fixed_continuous_program {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ}
    (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x))
    (C : List (SourceContinuousStep (SourceSpace n q H r))) (hC : sourceContinuousLegal C)
    (hSuccess : ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ Real.sqrt (1-1/13436928) ≤ ‖Qatlib.Foundations.PureStateMath.Inner
        (sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ sourceClean n q r hr false (ρ x))
        (sourceGarbageTarget n q r (σ x) ξ)‖) :
    sourceNoncoherentQ input ρ σ (1/3) ≤ sourceFixedContinuousOverhead*ENNReal.ofReal (sourceContinuousTime C) := by
  let out :=
      fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ sourceClean n q r hr false (ρ x)
  have hnorm (x : X) : Normalized (out x) := normalized_applyGate
    (continuousConversion_source_unitary input x C hC)
    (sourceClean_normalized n q r hr false (ρ x) (hn x).1)
  have hQ := sourceNoncoherent_fixed_third_from_output input ρ σ out hn hnorm hSuccess
  have hD := continuousConversion_source_program_distance input C hC
    (fun x => sourceClean n q r hr false (ρ x))
    (fun x => sourceClean_normalized n q r hr false (ρ x) (hn x).1)
  rw [sourceGram_clean_gram] at hD
  exact (hQ.trans (mul_le_mul_of_nonneg_left hD bot_le)).trans_eq
    (sourceFixedContinuousOverhead_mul_time _)
end
noncomputable section

/-- For nonempty payload space and normalized states, coherent discrete query complexity at
error `1/3` is at most `sourceFixedContinuousOverhead` times coherent continuous complexity
at error `1/13436928`. -/
theorem sourceCoherent_fixed_continuousQ_nonempty {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) :
    sourceCoherentQ input ρ σ (1/3) ≤
      sourceFixedContinuousOverhead*sourceContinuousCoherentQ input ρ σ (1/13436928) := by
  unfold sourceContinuousCoherentQ
  rw [sInf_eq_iInf]
  have hc0 : sourceFixedContinuousOverhead ≠ 0 := ne_of_gt
    (ENNReal.ofReal_pos.mpr (by positivity : (0:ℝ)<309237645312*(1+Real.pi^2)))
  have hctop : sourceFixedContinuousOverhead ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun b => le_iInf fun hb => ?_
  rcases hb with ⟨r,hr,C,hb,hC,hs⟩
  rw [hb]
  exact sourceCoherent_fixed_continuous_program hr input ρ σ hn C hC hs
end
noncomputable section

/-- For nonempty payload space and normalized states, noncoherent discrete query complexity at
error `1/3` is at most `sourceFixedContinuousOverhead` times noncoherent continuous
complexity at error `1/13436928`. -/
theorem sourceNoncoherent_fixed_continuousQ_nonempty {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) :
    sourceNoncoherentQ input ρ σ (1/3) ≤
      sourceFixedContinuousOverhead*sourceContinuousNoncoherentQ input ρ σ (1/13436928) := by
  unfold sourceContinuousNoncoherentQ
  rw [sInf_eq_iInf]
  have hc0 : sourceFixedContinuousOverhead ≠ 0 := ne_of_gt
    (ENNReal.ofReal_pos.mpr (by positivity : (0:ℝ)<309237645312*(1+Real.pi^2)))
  have hctop : sourceFixedContinuousOverhead ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  refine le_iInf fun b => le_iInf fun hb => ?_
  rcases hb with ⟨r,hr,C,hb,hC,hs⟩
  rw [hb]
  exact sourceNoncoherent_fixed_continuous_program hr input ρ σ hn C hC hs
end
noncomputable section

/-- For normalized state families, coherent discrete complexity at error `1/3` is bounded by
coherent continuous complexity at error `1/13436928` times `ENNReal.ofReal
(309237645312*(1+π²))`. -/
theorem sourceCoherent_fixed_continuousQ {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) :
    sourceCoherentQ input ρ σ (1/3) ≤
      ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))*
        sourceContinuousCoherentQ input ρ σ (1/13436928) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
    letI := hX
    rw [(sourceWordCosts_empty_input input ρ σ (1/3)).1]
    exact bot_le
  | inr hX =>
    letI := hX
    haveI : Nonempty H := by
      by_contra hnH
      haveI : IsEmpty H := not_nonempty_iff.mp hnH
      have hnorm := (hn (Classical.choice hX)).1
      simp [Normalized] at hnorm
    exact sourceCoherent_fixed_continuousQ_nonempty input ρ σ hn
end
noncomputable section

/-- For normalized state families, noncoherent discrete complexity at error `1/3` is bounded by
noncoherent continuous complexity at error `1/13436928` times `ENNReal.ofReal
(309237645312*(1+π²))`. -/
theorem sourceNoncoherent_fixed_continuousQ {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x,Normalized (ρ x)∧Normalized (σ x)) :
    sourceNoncoherentQ input ρ σ (1/3) ≤
      ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))*
        sourceContinuousNoncoherentQ input ρ σ (1/13436928) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
    letI := hX
    rw [(sourceWordCosts_empty_input input ρ σ (1/3)).2]
    exact bot_le
  | inr hX =>
    letI := hX
    haveI : Nonempty H := by
      by_contra hnH
      haveI : IsEmpty H := not_nonempty_iff.mp hnH
      have hnorm := (hn (Classical.choice hX)).1
      simp [Normalized] at hnorm
    exact sourceNoncoherent_fixed_continuousQ_nonempty input ρ σ hn
end
noncomputable section

/-- For normalized initial states, decoded coherent adaptive cost and noncoherent adaptive cost
each compare with the corresponding word query cost within a factor of two. -/
theorem stageB_state_conversion_clause91 {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (hρ : ∀ x, Normalized (ρ x)) :
    (sourceAdaptiveDecodedCoherentCost input ρ σ ε ≤ sourceCoherentQ input ρ σ ε ∧
      sourceCoherentQ input ρ σ ε ≤ 2*sourceAdaptiveDecodedCoherentCost input ρ σ ε) ∧
    (sourceAdaptiveNoncoherentCost input ρ σ ε ≤ sourceNoncoherentQ input ρ σ ε ∧
      sourceNoncoherentQ input ρ σ ε ≤ 2*sourceAdaptiveNoncoherentCost input ρ σ ε) :=
  ⟨sourceAdaptiveDecoded_normalized_comparison input ρ σ ε hρ,
    (sourceAdaptive_normalized_complexity_comparison input ρ σ ε hρ).2⟩
end
noncomputable section

/-- A legal continuous source program has filtered Gram change at most `ENNReal.ofReal
((1+π²)*sourceContinuousTime C)`. -/
theorem stageB_state_conversion_clause92 {X W : Type}
    [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (C : List (SourceContinuousStep ((Fin (n+1) × Fin (q+1)) × W)))
    (hC : sourceContinuousLegal C)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    sourceRectValue (gramStateMatrix ψ - gramStateMatrix
      (fun x => sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ ψ x))
      (sourceAlphabetDelta input) ≤ ENNReal.ofReal ((1+Real.pi^2) * sourceContinuousTime C) :=
  continuousConversion_source_program_distance input C hC ψ hψ
end
noncomputable section

/-- For normalized state families, continuous query complexity is at most discrete query
complexity at every error, in both conversion models. Conversely, discrete complexity at
error `1/3` is bounded by continuous complexity at error `1/13436928` with factor
`ENNReal.ofReal (309237645312*(1+π²))`. -/
theorem stageB_state_conversion_clause93 {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (hn : ∀ x, Normalized (ρ x) ∧ Normalized (σ x)) :
    (∀ ε : ℝ, sourceContinuousCoherentQ input ρ σ ε ≤ sourceCoherentQ input ρ σ ε) ∧
    (∀ ε : ℝ, sourceContinuousNoncoherentQ input ρ σ ε ≤ sourceNoncoherentQ input ρ σ ε) ∧
    sourceCoherentQ input ρ σ (1/3) ≤
      ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))*
        sourceContinuousCoherentQ input ρ σ (1/13436928) ∧
    sourceNoncoherentQ input ρ σ (1/3) ≤
      ENNReal.ofReal ((309237645312:ℝ)*(1+Real.pi^2))*
        sourceContinuousNoncoherentQ input ρ σ (1/13436928) :=
  ⟨continuousConversion_source_coherent input ρ σ,
    continuousConversion_source_noncoherent input ρ σ,
    sourceCoherent_fixed_continuousQ input ρ σ hn,
    sourceNoncoherent_fixed_continuousQ input ρ σ hn⟩
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
