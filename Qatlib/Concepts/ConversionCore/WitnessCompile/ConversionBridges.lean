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

/-!
# Bridges between source conversion models

The source fractional Boolean oracle agrees with the fractional phase oracle, and one fractional
query has filtered Gram cost at most `λ*π*sqrt 2`. Continuous conversion programs translate to
source programs without changing legality, time, or matrix semantics.

The module establishes that continuous query costs do not exceed discrete word costs and
supplies a purification identity for mixed inputs. The fractional-query estimate corresponds to
[LeeEtAl2011].

## Main statements

* `source_single_step_distance`: the fractional-query Gram bound.
* `continuousConversion_source_word_matrix`: exact embedding of source words.
* `mixed_input_kraus_consumer`: purification and Kraus action for density operators.

## References

* [Lee et al., 2011, Lemma B.1][LeeEtAl2011]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

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

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
noncomputable section

/-- The source fractional Boolean oracle equals the fractional phase oracle at the same
parameter. -/
theorem source_fractional_eq {X W : Type} [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (x : X) (lam : ℝ) :
    sourceFractionalOracle (W := W) input x lam = fractionalPhaseOracle (input x) lam := by
  unfold sourceFractionalOracle fractionalPhaseOracle
  congr 1
  funext p
  unfold fractionalQueryPhase
  split
  · split <;> simp_all [fractionalBooleanPhase, mul_assoc, Complex.ofReal_mul]
  · simp
end
noncomputable section

/-- For nonnegative `lam`, one fractional Boolean query changes a normalized state's Gram matrix
by filtered value at most `lam*π*sqrt 2`. This is [Lee et al., Lemma B.1][LeeEtAl2011]. -/
theorem source_single_step_distance {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n : ℕ}
    (input : X → Fin n → Bool) (lam : ℝ) (hlam : 0 ≤ lam)
    (ρ : X → QState ((Fin (n + 1) × Fin 2) × W)) (hρ : ∀ x, Normalized (ρ x)) :
    sourceRectValue (gramStateMatrix ρ - gramStateMatrix
      (fun x => sourceFractionalOracle input x lam *ᵥ ρ x))
      (sourceAlphabetDelta (fun x j => sourceBooleanSymbol (input x j))) ≤
      ENNReal.ofReal (lam * Real.pi * Real.sqrt 2) := by
  simp_rw [source_fractional_eq]
  rw [sourceBooleanDelta_eq, sourceSquareValue_eq]
  exact (filteredGamma2_budget_boundary X n _ _ _ (by positivity)).mpr
    (stageB_state_conversion_clause97 input lam hlam ρ hρ)
end
noncomputable section
set_option maxHeartbeats 300000 in

/-- Evolving for unit time under the negative logarithmic source oracle gives the adjoint
alphabet oracle. -/
theorem continuousConversion_source_inverse {X S : Type} [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    sourceVolterraMatrix (fun _ => -sourceLogOracle (W := S) input x) 1 =
      (sourceAlphabetOracle (W := S) input x)ᴴ := by
  obtain ⟨E, Θ, hE, _, hL, hexp⟩ := sourceLogOracle_frame X S input x
  have hneg : -sourceLogOracle (W := S) input x =
      E * Matrix.diagonal (fun t => ((-Θ t : ℝ) : ℂ)) * Eᴴ := by
    rw [hL]
    simp only [Complex.ofReal_neg]
    rw [← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]
  rw [hneg]
  have he := sourceVolterraMatrix_eq
    (fun _ => E * Matrix.diagonal (fun h => ((-Θ h : ℝ) : ℂ)) * Eᴴ) 1 zero_le_one
    (fun _ _ => continuous_const.intervalIntegrable 0 1)
    (fun t => E * Matrix.diagonal (fun h => Complex.exp (-Complex.I*t*(-Θ h : ℝ))) * Eᴴ)
    (sourceVolterra_const_spectral E (fun t => -Θ t) hE 1 zero_le_one)
  rw [he]
  rw [← hexp, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose]
  (try dsimp only)
  rw [Matrix.mul_assoc]
  apply congrArg (fun D => E * (D * Eᴴ))
  apply congrArg Matrix.diagonal
  funext t
  simp [RCLike.star_def, ← Complex.exp_conj]
end
set_option maxHeartbeats 300000 in
noncomputable section
/-- The source continuous program obtained by translating each known gate and evolution step of
a continuous conversion program. -/
def continuousConversion_source_steps {H : Type} (C : List (ContinuousConversionStep H)) :
    List (SourceContinuousStep H) := C.map (fun s => match s with
      | .known U => .known U
      | .evolve K T adj => .evolve K T adj)
end
noncomputable section

/-- Translating a legal continuous conversion program yields a legal source continuous program. -/
theorem continuousConversion_source_legal {H : Type} [Fintype H] [DecidableEq H]
    (C : List (ContinuousConversionStep H))
    (hC : continuousConversionLegal C) :
    sourceContinuousLegal (continuousConversion_source_steps C) := by
  intro s hs
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hs
  cases v <;> exact hC _ hv
end
noncomputable section

/-- Translation to a source continuous program preserves total query time. -/
theorem continuousConversion_source_time {H : Type} (C : List (ContinuousConversionStep H)) :
    sourceContinuousTime (continuousConversion_source_steps C) = continuousConversionTime C := by
  unfold sourceContinuousTime continuousConversion_source_steps continuousConversionTime
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  cases s <;> rfl
end
noncomputable section

/-- Translation to a source continuous program preserves its matrix semantics for every oracle
matrix. -/
theorem continuousConversion_source_matrix {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (C : List (ContinuousConversionStep H)) :
    sourceContinuousMatrix O (continuousConversion_source_steps C) =
      continuousConversionMatrix O C := by
  unfold sourceContinuousMatrix continuousConversion_source_steps continuousConversionMatrix
  rw [List.map_map]
  congr 2
  apply List.map_congr_left
  intro s _
  cases s <;> rfl
end
noncomputable section
set_option maxHeartbeats 300000 in

/-- The source continuous embedding of a source word evaluates to the original word matrix. -/
theorem continuousConversion_source_word_matrix {X S : Type} [Fintype S] [DecidableEq S]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (C : SourceWord ((Fin (n+1) × Fin (q+1)) × S)) :
    sourceContinuousMatrix (sourceLogOracle input x)
      (continuousConversion_source_steps (continuousConversionWord C)) =
      sourceWordMatrix (sourceAlphabetOracle input x) C := by
  rw [continuousConversion_source_matrix]
  apply continuousConversionWord_matrix
  · exact (volterraAndOracleLogSemantics.2.2 X S n q input x).2.2
  · exact continuousConversion_source_inverse input x
end
noncomputable section

/-- Coherent continuous source query complexity is at most coherent discrete source-word query
complexity at the same error. -/
theorem continuousConversion_source_coherent {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceContinuousCoherentQ input ρ σ ε ≤ sourceCoherentQ input ρ σ ε := by
  unfold sourceContinuousCoherentQ sourceCoherentQ
  refine le_sInf (fun b hb => ?_)
  obtain ⟨r,hr,C,rfl,hC,hs⟩ := hb
  apply sInf_le
  refine ⟨r,hr,continuousConversion_source_steps (continuousConversionWord C),?_,?_,?_⟩
  · rw [continuousConversion_source_time,continuousConversionWord_time]
    simp [sourceWordCalls]; rfl
  · exact continuousConversion_source_legal _ (continuousConversionWord_legal C hC)
  · simpa only [continuousConversion_source_word_matrix] using! hs
end
noncomputable section

/-- Noncoherent continuous source query complexity is at most noncoherent discrete source-word
query complexity at the same error. -/
theorem continuousConversion_source_noncoherent {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceContinuousNoncoherentQ input ρ σ ε ≤ sourceNoncoherentQ input ρ σ ε := by
  unfold sourceContinuousNoncoherentQ sourceNoncoherentQ
  refine le_sInf (fun b hb => ?_)
  obtain ⟨r,hr,C,rfl,hC,hs⟩ := hb
  apply sInf_le
  refine ⟨r,hr,continuousConversion_source_steps (continuousConversionWord C),?_,?_,?_⟩
  · rw [continuousConversion_source_time,continuousConversionWord_time]
    simp [sourceWordCalls]; rfl
  · exact continuousConversion_source_legal _ (continuousConversionWord_legal C hC)
  · simpa only [continuousConversion_source_word_matrix] using! hs
end
noncomputable section

/-- Every density operator possesses a normalized bipartite purification whose record marginal
is the density operator and whose recorded Kraus output has marginal `∑ k, A k*ρ*(A k)ᴴ`. -/
theorem mixed_input_kraus_consumer {d m : ℕ} (ρ : Operator d)
    (hρ : IsDensityOperator ρ) (A : Fin m → Operator d) :
    ∃ v : QState (Fin d × Fin d), Normalized v ∧ conversionRecordMarginal v = ρ ∧
      conversionRecordMarginal (conversionRecordKraus A v) =
        ∑ k, A k * ρ * (A k)ᴴ := by
  obtain ⟨ψ, hψ, htrace⟩ := density_purification_normalized ρ hρ
  let v : QState (Fin d × Fin d) := fun p => ψ (p.2,p.1)
  have hv : Normalized v := by
    have hn := hψ
    simp only [Normalized,Fintype.sum_prod_type] at hn ⊢
    rw [Finset.sum_comm]
    exact hn
  have hm : conversionRecordMarginal v = ρ := by
    rw [← htrace]
    rfl
  refine ⟨v, hv, hm, ?_⟩
  rw [conversionRecordKraus_marginal, hm]
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
