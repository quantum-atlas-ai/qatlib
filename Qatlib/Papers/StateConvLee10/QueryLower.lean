/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Papers.StateConvLee10.QueryLower

theorem source_query_gram_bounds :
  (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ : X → QState H)
      (C : SourceWord (SourceSpace n q H r)),
      (∀ x, Normalized (ρ x)) → sourceWordLegal C →
      let out := fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix out) (sourceAlphabetDelta input) ≤
        ENNReal.ofReal (2*sourceWordCalls C)) ∧
  (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      (ρ σ : X → QState H) (ε : ℝ),
      (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ ε → ε ≤ 1 →
      (∀ x, (∑ p, star (ρ x p)*σ x p).re ≥ Real.sqrt (1-ε)) →
      sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ) ≤
        ENNReal.ofReal (2*Real.sqrt (2*ε))) ∧
  (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
      (ρ σ : X → QState H) (δ : ℝ),
      (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ δ →
      sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ) ≤ ENNReal.ofReal δ →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace 0 0 H r)),
        sourceWordLegal C ∧ sourceWordCalls C=0 ∧ ∀ x,
        ‖toEuclidean_fromVec (sourceWordMatrix (1 : Matrix _ _ ℂ) C *ᵥ
          sourceClean 0 0 r hr false (ρ x)-sourceClean 0 0 r hr true (σ x))‖ ≤ Real.sqrt (2*δ)) := by
  exact Qatlib.Concepts.GramQueryCore.LowerBoundTools.generalOutputGramBridges

theorem source_bit_query_certificate {X : Type} [Fintype X] [DecidableEq X]
    {n R : ℕ} (input : X → Fin n → Bool)
    {ψ : X → QState ((Fin n × Bool) × Fin R)} (hψ : ∀ x, Normalized (ψ x)) :
    gramFilteredCert
      (gramStateMatrix ψ - gramStateMatrix
        (fun x => ApplyGate (workspaceBitOracle (W := Fin R) (input x)) (ψ x)))
      (gramFilterDelta input) 2 := by
  exact Qatlib.Concepts.GramQueryCore.LowerBoundTools.gram_one_query_filteredCert (X := X) (n := n)
      (R := R) (input := input) (ψ := ψ) (hψ := hψ)

end Qatlib.Papers.StateConvLee10.QueryLower
