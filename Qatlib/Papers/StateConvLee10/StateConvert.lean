/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapQuan
import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessSpectralMassesQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan

/-!
# State-conversion algorithms and spectral estimates

This module supplies a legal approximate state-conversion word from a finite filtered Gram
budget and proves the accompanying effective spectral gap and witness-mass estimates. The bounds
control the query count, target overlap, and small-phase components used in the construction of
[LeeEtAl2011].

## Main statements

* `source_state_conversion`: a filtered Gram bound yields a legal word with the stated query and
  approximation guarantees.
* `source_effective_gap`: a product of reflections controls the small-phase part of a projected
  vector.
* `source_witness_masses`: factorization witnesses give the stated plus and minus spectral-mass
  bounds.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding.EncodingCore
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.QueryComplexity.StateConversion

namespace Qatlib.Papers.StateConvLee10.StateConvert

/-- For normalized families, a filtered Gram budget `W ≥ 0` and `0 < ε ≤ 1 / 3` yield a legal
word using at most `c * ceil (W * log (2 / ε) / ε²)` queries with the stated target overlap,
zero-query cases, and conditional norm-error guarantee [LeeEtAl2011]. -/
theorem source_state_conversion :
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ W →
    sourceRectValue (gramStateMatrix ρ-gramStateMatrix σ) (sourceAlphabetDelta input) ≤
      ENNReal.ofReal W → 0<ε → ε ≤ 1/3 →
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
      sourceWordLegal C ∧
      sourceWordCalls C ≤ c*Nat.ceil (W*Real.log (2/ε)/ε^2) ∧
      ((W=0 ∨ n=0 ∨ q=0) → sourceWordCalls C=0) ∧
      (∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥
          Real.sqrt (1-ε)) ∧
      (ε ≤ W → ∀ x, ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖ < 4*ε) := by
  exact Qatlib.Concepts.QueryComplexity.StateConversion.realBudgetConversionAlgorithm

/-- For the displayed spectral decomposition of a product of projector reflections, if `L w = 0`
and `Θ ≥ 0`, the small-phase component of `P w` has norm at most `(Θ / 2) * ‖w‖`
[LeeEtAl2011]. -/
theorem source_effective_gap
    (H : Type) [Fintype H] [DecidableEq H] (P L V : Matrix H H ℂ)
    (angles : H → ℝ) (Θ : ℝ) (w : QState H)
    (_hP : IsOrthogonalProjector P) (_hL : IsOrthogonalProjector L)
    (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (_hangles : ∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi)
    (hU : ReflectionAbout P * ReflectionAbout L =
      V * Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) * Vᴴ)
    (hΘ : 0 ≤ Θ) (hLw : L *ᵥ w = 0) :
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ (P *ᵥ w))‖ ≤
      Θ/2*‖toEuclidean_fromVec w‖ := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.effectiveSpectralGap (H := H) (P := P)
      (L := L) (V := V) (angles := angles) (Θ := Θ) (w := w) (_hP := _hP) (_hL := _hL) (hV := hV)
      (_hangles := _hangles) (hU := hU) (hΘ := hΘ) (hLw := hLw)

/-- Under the stated normalization, factorization, and witness-budget hypotheses, the plus
vector has zero-phase mass at least `1 - ε²`, and the minus vector has small-phase mass at
most `(Θ² / 4) * (W² / ε² + 1)` for `Θ ≥ 0` [LeeEtAl2011]. -/
theorem source_witness_masses :
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n q m : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u v : X → Fin n → QState (Fin m)) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0<q → 0<W → 0<ε →
    (∀ y x, (gramStateMatrix ρ-gramStateMatrix σ) y x=
      ∑ j, sourceAlphabetDelta input j y x*∑ k, star (u y j k)*v x j k) →
    (∀ x, (∑ j, ‖toEuclidean_fromVec (u x j)‖^2) ≤ W ∧
      (∑ j, ‖toEuclidean_fromVec (v x j)‖^2) ≤ W) →
    ∀ (x : X) (V : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ)
      (angles : SourceGeometry n q m H → ℝ),
    V ∈ Matrix.unitaryGroup _ ℂ → (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) →
    ReflectionAbout (sourceKeep input x) * ReflectionAbout (sourceComplement input ρ σ u W ε)=
      V * Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) * Vᴴ →
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles 0 *ᵥ sourcePlus (ρ x) (σ x))‖^2 ≥
      1-ε^2 ∧ ∀ Θ : ℝ, 0 ≤ Θ →
      ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ sourceMinus (ρ x) (σ x))‖^2 ≤
        Θ^2/4*(W^2/ε^2+1) := by
  exact Qatlib.Concepts.ConversionCore.WitnessCompile.witnessSpectralMasses

end Qatlib.Papers.StateConvLee10.StateConvert
