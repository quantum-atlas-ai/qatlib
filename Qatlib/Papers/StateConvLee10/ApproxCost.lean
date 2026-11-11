/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedReturnedWordConsumersQuan

/-!
# Approximate state-conversion costs and output frames

This module constructs a unitary output-tag flip and relates its action to clean targets and
legal query words. It expresses coherent and noncoherent conversion costs as infima over words
and supplies optimized cost bounds and witnessing programs for normalized state families, in the
framework of [LeeEtAl2011].

## Main statements

* `source_output_frame_word`: appending the output flip preserves legality and query count.
* `source_optimized_cost_bounds`: optimized Gram quantities bound coherent and noncoherent
  costs.
* `source_optimized_programs`: finite optimized bounds yield legal words with controlled overlap
  and query count.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.QueryComplexity.StateConversion

namespace Qatlib.Papers.StateConvLee10.ApproxCost

/-- The permutation of the source space that flips the Boolean output tag. -/
def source_output_tag_flip {H : Type} (n q r : ℕ)
    (p : SourceSpace n q H r) : SourceSpace n q H r :=
  (p.1, ((!p.2.1.1, p.2.1.2), p.2.2))

/-- Flipping the output tag twice returns the original source-space index. -/
theorem source_output_tag_involutive {H : Type} (n q r : ℕ) :
    Function.Involutive (source_output_tag_flip (H := H) n q r) := by
  intro p
  simp [source_output_tag_flip]

/-- The permutation matrix implementing the output-tag flip. -/
def source_output_gate {H : Type} [Fintype H] [DecidableEq H] (n q r : ℕ) :
    Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ :=
  permMatrix (source_output_tag_flip n q r)

/-- The output-tag flip matrix is unitary. -/
theorem source_output_gate_unitary {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) : source_output_gate (H := H) n q r ∈ Matrix.unitaryGroup _ ℂ := by
  exact permMatrix_unitary (source_output_tag_involutive n q r)

/-- Applying the output gate to a clean tagged state flips its tag and preserves its payload
[LeeEtAl2011]. -/
theorem source_output_gate_clean {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0 < r) (tag : Bool) (ψ : QState H) :
    ApplyGate (source_output_gate n q r) (sourceClean n q r hr tag ψ) =
      sourceClean n q r hr (!tag) ψ := by
  ext p
  change ApplyGate (permMatrix (source_output_tag_flip n q r))
    (sourceClean n q r hr tag ψ) p = _
  rw [applyGate_permMatrix (source_output_tag_involutive n q r)]
  cases tag <;> cases h : p.2.1.1 <;>
    simp [source_output_tag_flip, sourceClean, TensorState, Ket, h]

/-- The overlap of an output-flipped state with a false-tagged clean target equals its original
overlap with the true-tagged target [LeeEtAl2011]. -/
theorem source_output_frame_overlap {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0 < r) (out : QState (SourceSpace n q H r)) (σ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner
      (ApplyGate (source_output_gate n q r) out) (sourceClean n q r hr false σ) =
    Qatlib.Foundations.PureStateMath.Inner out (sourceClean n q r hr true σ) := by
  have h := inner_applyGate (source_output_gate_unitary n q r) out
    (sourceClean n q r hr true σ)
  simpa only [source_output_gate_clean, Bool.not_true] using! h

/-- Appending the output gate preserves word legality and query count, and applies the output
flip after the original word [LeeEtAl2011]. -/
theorem source_output_frame_word {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (O : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ)
    (C : SourceWord (SourceSpace n q H r)) (hC : sourceWordLegal C) :
    sourceWordLegal (C ++ [.inl (source_output_gate n q r)]) ∧
    sourceWordCalls (C ++ [.inl (source_output_gate n q r)]) = sourceWordCalls C ∧
    ∀ ψ, sourceWordMatrix O (C ++ [.inl (source_output_gate n q r)]) *ᵥ ψ =
      ApplyGate (source_output_gate n q r) (sourceWordMatrix O C *ᵥ ψ) := by
  have hG : sourceWordLegal [.inl (source_output_gate (H := H) n q r)] := by
    intro s hs
    have he : s = .inl (source_output_gate (H := H) n q r) := List.mem_singleton.mp hs
    subst s
    exact source_output_gate_unitary n q r
  refine ⟨sourceWordLegal_append _ _ hC hG, ?_, ?_⟩
  · rw [sourceWordCalls_append]
    simp [sourceWordCalls]
  · intro ψ
    rw [sourceWordMatrix_append]
    simp [sourceWordMatrix, ApplyGate, Matrix.mulVec_mulVec]

/-- The property that `C` is legal and its outputs have real overlap at least `sqrt (1 - ε)`
with the true-tagged clean targets [LeeEtAl2011]. -/
def source_coherent_output {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)) : Prop :=
  sourceWordLegal C ∧ ∀ x,
    (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
        Real.sqrt (1-ε)

/-- The property that `C` is legal and each output has overlap norm at least `sqrt (1 - ε)` with
a target carrying some normalized auxiliary state [LeeEtAl2011]. -/
def source_noncoherent_output {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ)
    (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)) : Prop :=
  sourceWordLegal C ∧ ∀ x,
    ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
      Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceGarbageTarget n q r (σ x) ξ p‖ ≥
          Real.sqrt (1-ε)

/-- The coherent conversion cost is the infimum of query counts of words satisfying
`source_coherent_output` [LeeEtAl2011]. -/
theorem source_coherent_cost_eq {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceCoherentQ input ρ σ ε =
      sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
        b = (sourceWordCalls C : ℝ≥0∞) ∧ source_coherent_output input ρ σ ε r hr C} := by
  rfl

/-- The noncoherent conversion cost is the infimum of query counts of words satisfying
`source_noncoherent_output` [LeeEtAl2011]. -/
theorem source_noncoherent_cost_eq {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ) :
    sourceNoncoherentQ input ρ σ ε =
      sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
        b = (sourceWordCalls C : ℝ≥0∞) ∧
          source_noncoherent_output input ρ σ ε r hr C} := by
  rfl

/-- For normalized families and `0 < ε ≤ 1 / 3`, a universal positive constant gives the
displayed lower and upper comparisons between optimized Gram quantities and coherent and
noncoherent query costs [LeeEtAl2011]. -/
theorem source_optimized_cost_bounds :
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0<ε → ε ≤ 1/3 →
    let R := gramStateMatrix ρ
    let S := gramStateMatrix σ
    sourceQDelta input (2*Real.sqrt (2*ε)) R S ≤ c*sourceCoherentQ input ρ σ ε ∧
    sourceCoherentQ input ρ σ ε ≤ c*ENNReal.ofReal (Real.log (1/ε)/ε^2)*
      sourceQDelta input (ε^4/16) R S ∧
    sourceQNoncoherentDelta input (2*Real.sqrt (2*ε)) R S ≤ c*sourceNoncoherentQ input ρ σ ε ∧
    sourceNoncoherentQ input ρ σ ε ≤ c*ENNReal.ofReal (Real.log (1/ε)/ε^2)*
      sourceQNoncoherentDelta input (ε^4/16) R S := by
  exact Qatlib.Concepts.QueryComplexity.StateConversion.optimizedConversionEndpoints

/-- For normalized families and `0 < ε ≤ 1 / 3`, a finite optimized Gram bound `W ≥ 0` yields
legal coherent or noncoherent words using at most `ceil (c * W * log (1 / ε) / ε²)` queries
and satisfying the stated target-overlap guarantees [LeeEtAl2011]. -/
theorem source_optimized_programs :
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε W : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0<ε → ε ≤ 1/3 → 0 ≤ W →
    (sourceQDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ) ≤ ENNReal.ofReal W →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*W*Real.log (1/ε)/ε^2) ∧
        ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥
            Real.sqrt (1-ε)) ∧
    (sourceQNoncoherentDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ) ≤
        ENNReal.ofReal W →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*W*Real.log (1/ε)/ε^2) ∧
        ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
          Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
            sourceClean n q r hr false (ρ x)) p)*sourceGarbageTarget n q r (σ x) ξ p‖ ≥
              Real.sqrt (1-ε)) := by
  exact Qatlib.Concepts.QueryComplexity.StateConversion.optimizedReturnedWordConsumers

end Qatlib.Papers.StateConvLee10.ApproxCost
