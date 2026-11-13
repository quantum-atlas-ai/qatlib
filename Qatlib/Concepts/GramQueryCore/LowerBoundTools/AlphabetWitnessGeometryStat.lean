/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Alphabet witness geometry specification

Defines `AlphabetWitnessGeometry`, packaging bounded filtered Gram witnesses together with their
alphabet vectors and orthogonal projection geometry. It requires positive alphabet, budget, and
error parameters and normalized input and output states.

The specification includes the pairing identities, common fixed vectors, forbidden-vector
annihilation, and norm estimates used in the state conversion construction of [LeeEtAl2011].

## Main statements

* `AlphabetWitnessGeometry`: specifies bounded witness extraction and its projection geometry.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The proposition that a filtered Gram value bounded by `W` yields witnesses with budget `W`,
normalized alphabet vectors with prescribed pairings, and the complement and keep projection
identities and quantitative error bounds. -/
def AlphabetWitnessGeometry : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n q : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) →
    0<q → 0<W → 0<ε →
    sourceRectValue (gramStateMatrix ρ-gramStateMatrix σ) (sourceAlphabetDelta input) ≤
      ENNReal.ofReal W →
    ∃ (m : ℕ) (u v : X → Fin n → QState (Fin m)),
      (∀ y x, (gramStateMatrix ρ-gramStateMatrix σ) y x=
        ∑ j, sourceAlphabetDelta input j y x*∑ k, star (u y j k)*v x j k) ∧
      (∀ x, (∑ j, ‖toEuclidean_fromVec (u x j)‖^2) ≤ W ∧
        (∑ j, ‖toEuclidean_fromVec (v x j)‖^2) ≤ W) ∧
      (∀ a : Fin (q+1), Normalized (sourceMu q a) ∧ Normalized (sourceNu q a)) ∧
      (∀ a b : Fin (q+1), (∑ k, star (sourceMu q a k)*sourceNu q b k)=
        if a=b then 0 else ((q+1)/(2*q) : ℂ)) ∧
      let L := sourceComplement input ρ σ u W ε
      IsOrthogonalProjector L ∧ ∀ x,
      IsOrthogonalProjector (sourceKeep (m := m) (H := H) input x) ∧
      L *ᵥ sourceForbidden input ρ σ u W ε x=0 ∧
      L *ᵥ sourceFixed input ρ σ v W ε x=sourceFixed input ρ σ v W ε x ∧
      sourceKeep input x *ᵥ sourceFixed input ρ σ v W ε x=sourceFixed input ρ σ v W ε x ∧
      sourceKeep input x *ᵥ sourceForbidden input ρ σ u W ε x=
        ((ε/Real.sqrt W : ℝ) : ℂ) • sourceMinus (ρ x) (σ x) ∧
      ‖toEuclidean_fromVec (sourceFixed input ρ σ v W ε x-sourcePlus (ρ x) (σ x))‖^2 ≤ ε^2 ∧
      ‖toEuclidean_fromVec (((Real.sqrt W/ε : ℝ) : ℂ) •
        sourceForbidden input ρ σ u W ε x)‖^2 ≤ W^2/ε^2+1
end Qatlib.Concepts.GramQueryCore.LowerBoundTools
