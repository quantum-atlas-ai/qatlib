/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value

/-!
# Specifications for rational witnesses and native conversion

`RationalGamma2Instance` and `RationalGamma2Factorization` describe rational filtered γ₂ data
and its witness budgets. The remaining predicates specify coherent and noncoherent word
accuracy, adaptive-to-word bridges, local synthesis, and rational or numerically accessible
native compilation.

These are specification predicates: their fields record the requested accuracy and resource
ledgers in the state-conversion framework of [LeeEtAl2011].

## Main statements

* `Gamma2WitnessCompilerSpec`: specifies near-optimal rational certificates and a polynomial
  runtime bound.
* `AdaptiveBridgeSpec`: bundles purification, query accounting, and reverse simulation
  requirements.
* `RationalToNativeSpec`: specifies native legality, overlap guarantees, and resource bounds.

## References

* [Lee et al., 2011][LeeEtAl2011]
* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.ConversionCore.WitnessCompile

open Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- Rational target-matrix and filter-matrix data for a square filtered γ₂ problem. -/
structure RationalGamma2Instance (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) where

  A : Matrix X X ℚ

  Z : Fin n → Matrix X X ℚ

/-- The size ledger consisting of the number of filters, the index cardinality, and the encoded
rational matrix entries. -/
def rationalGamma2Bits {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (inst : RationalGamma2Instance X n) : ℕ :=
  n + Fintype.card X +
    (∑ x, ∑ y, (sourceRatBits (inst.A x y)).length) +
    ∑ j, ∑ x, ∑ y, (sourceRatBits (inst.Z j x y)).length

/-- The rational instance's target matrix embedded entrywise into the complex numbers. -/
noncomputable def rationalGamma2ComplexA {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (inst : RationalGamma2Instance X n) : Matrix X X ℂ :=
  fun x y => ((inst.A x y : ℚ) : ℂ)

/-- The rational instance's filter matrices embedded entrywise into the complex numbers. -/
noncomputable def rationalGamma2ComplexZ {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (inst : RationalGamma2Instance X n) : Fin n → Matrix X X ℂ :=
  fun j x y => ((inst.Z j x y : ℚ) : ℂ)

/-- Rational witness vectors over a finite auxiliary type together with a rational budget for
the given instance. -/
structure RationalGamma2Factorization (X : Type) [Fintype X] [DecidableEq X]
    {n : ℕ} (inst : RationalGamma2Instance X n) where

  Q : Type

  [fintypeQ : Fintype Q]

  u : Fin n → X → Q → ℚ

  v : Fin n → X → Q → ℚ

  budget : ℚ

/-- Requires both families of witness masses to be bounded by the budget and the filtered
factorization identity to hold exactly. -/
def RationalFactorizationValid {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (inst : RationalGamma2Instance X n) (F : RationalGamma2Factorization X inst) : Prop :=
  haveI : Fintype F.Q := F.fintypeQ
  (∀ x : X, ∑ j, ∑ q, ((F.u j x q * F.u j x q : ℚ) : ℝ) ≤ (F.budget : ℝ)) ∧
  (∀ y : X, ∑ j, ∑ q, ((F.v j y q * F.v j y q : ℚ) : ℝ) ≤ (F.budget : ℝ)) ∧
  ∀ x y : X, ((inst.A x y : ℚ) : ℂ) =
    ∑ j, ((inst.Z j x y : ℚ) : ℂ) * ∑ q, ((F.u j x q * F.v j y q : ℚ) : ℂ)

/-- Specifies near-optimal rational filtered γ₂ certificates with two value comparisons and an
existential polynomial runtime ledger. -/
def Gamma2WitnessCompilerSpec : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) (inst : RationalGamma2Instance X n)
    (ε : ℝ), 0 < ε → ε ≤ 1 →
    filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) < ⊤ →
      ∃ (F : RationalGamma2Factorization X inst) (runtime : ℕ),
        RationalFactorizationValid inst F ∧
        (F.budget : ℝ) ≤ (filteredGamma2 (rationalGamma2ComplexA inst)
          (rationalGamma2ComplexZ inst)).toReal + ε ∧
        filteredGamma2 (rationalGamma2ComplexA inst) (rationalGamma2ComplexZ inst) ≤
          ENNReal.ofReal ((F.budget : ℝ) + ε) ∧
        runtime ≤ (rationalGamma2Bits inst + Fintype.card X + n + Nat.ceil (1 / ε) + 8) ^ 7

/-- Requires the real overlap of the word's clean output with the clean target to be at least
`Real.sqrt (1 - ε)` for every input. -/
def sourceWordCoherentAt {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    {n q r : ℕ} (hr : 0 < r) (input : X → Fin n → Fin (q + 1))
    (C : SourceWord (SourceSpace n q H r)) (ρ σ : X → QState H) (ε : ℝ) : Prop :=
  ∀ x : X, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
    Real.sqrt (1 - ε)

/-- Requires a normalized garbage state for each input giving target-overlap magnitude at least
`Real.sqrt (1 - ε)`. -/
def sourceWordNoncoherentAt {X H : Type} [Fintype X] [DecidableEq X] [Fintype H]
    [DecidableEq H] {n q r : ℕ} (hr : 0 < r) (input : X → Fin n → Fin (q + 1))
    (C : SourceWord (SourceSpace n q H r)) (ρ σ : X → QState H) (ε : ℝ) : Prop :=
  ∀ x : X, ∃ ξ : QState ((Fin (n + 1) × Fin (q + 1)) × (Bool × Fin r)), Normalized ξ ∧
    ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceGarbageTarget n q r (σ x) ξ p‖ ≥
      Real.sqrt (1 - ε)

/-- Specifies a legal word realizing an adaptive tree's purification with an isometric frame and
at most twice the adaptive query count. It also requires branch normalization and recovery
of the adaptive density matrix. -/
def AdaptiveBridgeForwardSpec : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0 < r) (input : X → Fin n → Fin (q + 1))
    (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    let leaves := max 1 (sourceAdaptiveLeaves T)
    ∃ (R : ℕ) (hR : 0 < R) (C : SourceWord (SourceSpace n q H R)),
      leaves * r ≤ R ∧ sourceWordLegal C ∧ sourceWordCalls C ≤ 2 * sourceAdaptiveCalls T ∧
      let F := sourceTreeFrame (H := H) n q r leaves R
      Fᴴ * F = 1 ∧ ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
        sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          (F *ᵥ TensorState (Ket (⟨0, by dsimp only [leaves]; omega⟩ : Fin leaves)) ψ) =
        F *ᵥ sourceAdaptivePure (sourceAlphabetOracle input x) T ψ ∧
        (Normalized ψ →
          ((sourceAdaptiveBranches (sourceAlphabetOracle input x) T ψ).map
            (fun φ => ‖toEuclidean_fromVec φ‖ ^ 2)).sum = 1) ∧
        (∀ p t, sourceAdaptiveDensity (sourceAlphabetOracle input x) T ψ p t =
          ∑ i : Fin leaves, sourceAdaptivePure (sourceAlphabetOracle input x) T ψ (i, p) *
            star (sourceAdaptivePure (sourceAlphabetOracle input x) T ψ (i, t)))

/-- Specifies coherent and noncoherent query-complexity upper bounds from the query count of any
legal word satisfying the respective overlap condition. -/
def SourceWordAccountingSpec : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] (n q : ℕ)
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) (ε : ℝ)
    (r : ℕ) (hr : 0 < r) (C : SourceWord (SourceSpace n q H r)),
    sourceWordLegal C →
    (sourceWordCoherentAt hr input C ρ σ ε →
      sourceCoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞)) ∧
    (sourceWordNoncoherentAt hr input C ρ σ ε →
      sourceNoncoherentQ input ρ σ ε ≤ (sourceWordCalls C : ℝ≥0∞))

/-- Specifies an adaptive realization of each legal word with no larger query count and the same
output density matrix on pure inputs. -/
def AdaptiveBridgeReverseSpec : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (C : SourceWord S), sourceWordLegal C →
    ∃ T : SourceAdaptive S, sourceAdaptiveLegal T ∧ sourceAdaptiveCalls T ≤ sourceWordCalls C ∧
      ∀ (O : Matrix S S ℂ) (ψ : QState S) (p t : S),
        sourceAdaptiveDensity O T ψ p t =
          (sourceWordMatrix O C *ᵥ ψ) p * star ((sourceWordMatrix O C *ᵥ ψ) t)

/-- The conjunction of forward adaptive purification, word query accounting, and reverse
adaptive simulation specifications. -/
def AdaptiveBridgeSpec : Prop :=
  AdaptiveBridgeForwardSpec ∧ SourceWordAccountingSpec ∧ AdaptiveBridgeReverseSpec

/-- The matrix obtained by evaluating a list of local QFT gates. -/
noncomputable def localGateWordMatrix {w : ℕ} (word : List (LocalQFTGate w)) :
    Matrix (Reg w) (Reg w) ℂ :=
  localProgramMatrix word

/-- Specifies fixed-gate approximation of a local gate to error at most `2⁻ᵏ`, with a polynomial
word-length bound and a synthesis-compiler time condition. -/
def LocalSynthesisSpec : Prop :=
  ∀ (w k : ℕ), 0 < k → ∀ g : LocalQFTGate w,
    ∃ (word : List (LocalQFTGate w))
        (build : {w' : ℕ} → LocalQFTGate w' → ℕ → SourceNativeProgram),
      (∀ h ∈ word, sourceFixedGate h) ∧
      ‖localGateWordMatrix word - localGateMatrix g‖ ≤ (1 / 2 : ℝ) ^ k ∧
      word.length ≤ (w + k + 8) ^ 6 ∧
      sourceSynthesisCompilerTime build (w + k) 7

/-- Embeds a target state on the true branch and the false-branch coordinates of `ξ` through the
native frame. -/
noncomputable def sourceNativeGarbageTarget (d : SourceRationalProblem) (w : ℕ)
    (ψ : QState (Fin d.dimension)) (ξ : QState (Bool × Fin d.dimension)) :
    QState (Reg w) :=
  sourceNativeFrame d w *ᵥ (fun t => if t.1 then ψ t.2 else ξ t)

/-- Specifies a compiler for rational problems with native legality, coherent and
garbage-assisted overlap guarantees, query accounting, and width and gate bounds. -/
def RationalToNativeSpec : Prop :=
  ∀ (d : SourceRationalProblem) (k : ℕ), 0 < k →
    ∃ (build : SourceRationalProblem → ℕ → SourceNativeProgram) (C D : ℕ),
      sourceNativeCompilerTime build C D ∧
      sourceNativeLegal d (build d k) ∧
      (∀ x : Fin d.count,
        (∑ q, star ((sourceNativeMatrix d x (build d k) *ᵥ
            sourceNativeClean d (build d k).width false
              (sourceRationalState (d.start x))) q) *
          sourceNativeClean d (build d k).width true (sourceRationalState (d.target x)) q).re ≥
          Real.sqrt (1 - (1 / 2 : ℝ) ^ k)) ∧
      (∀ x : Fin d.count, ∃ ξ : QState (Bool × Fin d.dimension), Normalized ξ ∧
        ‖∑ q, star ((sourceNativeMatrix d x (build d k) *ᵥ
            sourceNativeClean d (build d k).width false
              (sourceRationalState (d.start x))) q) *
          (sourceNativeGarbageTarget d (build d k).width
            (sourceRationalState (d.target x)) ξ) q‖ ≥
          Real.sqrt (1 - (1 / 2 : ℝ) ^ k)) ∧
      (sourceCoherentQ d.input (fun x => sourceRationalState (d.start x))
          (fun x => sourceRationalState (d.target x)) ((1 / 2 : ℝ) ^ k) ≤
        (sourceNativeCalls (build d k) : ℝ≥0∞) ∧
        sourceNoncoherentQ d.input (fun x => sourceRationalState (d.start x))
          (fun x => sourceRationalState (d.target x)) ((1 / 2 : ℝ) ^ k) ≤
        (sourceNativeCalls (build d k) : ℝ≥0∞)) ∧
      (build d k).width ≤ (sourceProblemBits d).length + d.dimension + k + 8 ∧
      sourceNativeGates (build d k) ≤ ((sourceProblemBits d).length + k + 8) ^ 9

/-- Specifies native compilation of numerically accessible real problems with dyadic overlap
guarantees and query, width, gate, and compiler-time bounds. -/
def NumericalToNativeSpec : Prop :=
  ∀ (d : SourceRealProblem), sourceRealAccess d → ∀ k : ℕ, 0 < k →
    ∃ (build : SourceRealProblem → ℕ → SourceNativeProgram) (C D : ℕ),
      sourceGeneralCompilerTime build C D ∧
      sourceNativeLegal (sourceRealHeader d) (build d k) ∧
      (∀ x : Fin d.count,
        (∑ q, star ((sourceNativeMatrix (sourceRealHeader d) x (build d k) *ᵥ
            sourceNativeClean (sourceRealHeader d) (build d k).width false (d.start x)) q) *
          sourceNativeClean (sourceRealHeader d) (build d k).width true (d.target x) q).re ≥
          Real.sqrt (1 - (1 / 2 : ℝ) ^ k)) ∧
      (∀ x : Fin d.count, ∃ ξ : QState (Bool × Fin d.dimension), Normalized ξ ∧
        ‖∑ q, star ((sourceNativeMatrix (sourceRealHeader d) x (build d k) *ᵥ
            sourceNativeClean (sourceRealHeader d) (build d k).width false (d.start x)) q) *
          (sourceNativeGarbageTarget (sourceRealHeader d) (build d k).width
            (d.target x) ξ) q‖ ≥
          Real.sqrt (1 - (1 / 2 : ℝ) ^ k)) ∧
      sourceNativeCalls (build d k) ≤ sourceRealSize d + k ∧
      (build d k).width ≤ sourceRealSize d + k + 8 ∧
      sourceNativeGates (build d k) ≤
        (sourceRealSize d + k + sourceEvaluationWork d (sourceRealSize d + k + 8)) ^ 9

end Qatlib.Concepts.ConversionCore.WitnessCompile
