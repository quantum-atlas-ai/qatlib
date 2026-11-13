/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.QueryDistanceLowerBound

/-!
# Query lower bounds through Gram changes

This module bounds the filtered Gram change of legal query words and relates approximate state
overlaps to unfiltered Gram distance. It also constructs a zero-query conversion from an
unfiltered Gram bound and records the budget-two certificate for one Boolean oracle query, in
the setting of [LeeEtAl2011].

## Main statements

* `source_query_gram_bounds`: query count, state overlap, and zero-query conversion satisfy the
  displayed Gram bounds.
* `source_bit_query_certificate`: one Boolean query has filtered certificate budget two.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

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

/-- Legal words on normalized families have filtered Gram change at most twice their query
count; the stated overlap condition bounds unfiltered Gram distance, and an unfiltered bound
`δ ≥ 0` yields a legal zero-query word with state error at most `sqrt (2 * δ)`
[LeeEtAl2011]. -/
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

/-- One workspace Boolean oracle query on a normalized family yields a filtered certificate of
budget two for the resulting Gram-matrix difference. -/
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
