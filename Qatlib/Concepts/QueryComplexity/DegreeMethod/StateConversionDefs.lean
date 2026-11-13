/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Definitions for fractional and continuous state conversion

This module defines fractional Boolean phase oracles, a bit-query embedding, and record
projections and marginals for state conversion. It also defines continuous query instructions,
their Volterra integral equation, legality conditions, duration, and endpoint-product semantics.

The record Kraus construction and tangent witnesses provide concrete objects for filtered Gram
certificates in the framework of [LeeEtAl2011]. The endpoint definition selects a Volterra
solution when one exists and otherwise returns the identity.

## Main definitions

* `fractionalPhaseOracle`: the padded diagonal fractional query.
* `continuousConversionVolterra`: the integral equation defining an evolution.
* `continuousConversionMatrix`: evaluation of a continuous instruction word.
* `conversionRecordKraus`: the record extension storing a Kraus index.
* `continuousConversionTangent`: the mixed-inner-product tangent matrix.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped BigOperators Classical

/-- The phase `exp (i * pi * lam)` on a true Boolean input and one on a false input. -/
def fractionalBooleanPhase (lam : ℝ) (b : Bool) : ℂ :=
  if b then Complex.exp (Complex.I * (Real.pi * lam : ℝ)) else 1

/-- The fractional phase of an active input position, extended by phase one at the final idle
position. -/
def fractionalQueryPhase {n : ℕ} (input : Fin n → Bool) (lam : ℝ)
    (i : Fin (n + 1)) : ℂ :=
  if h : i.val < n then fractionalBooleanPhase lam (input ⟨i.val, h⟩) else 1

/-- The diagonal fractional phase oracle acting on the query index and trivially on the
remaining registers. -/
def fractionalPhaseOracle {W : Type} {n : ℕ} [DecidableEq W]
    (input : Fin n → Bool) (lam : ℝ) :
    Matrix ((Fin (n + 1) × Fin 2) × W) ((Fin (n + 1) × Fin 2) × W) ℂ :=
  Matrix.diagonal (fun p => fractionalQueryPhase input lam p.1.1)

/-- Extends a Boolean input by one final position with value `false`. -/
def fractionalPaddedInput {n : ℕ} (input : Fin n → Bool) (i : Fin (n + 1)) : Bool :=
  if h : i.val < n then input ⟨i.val, h⟩ else false

/-- Embeds a state into a bit-query register by adjoining a `Minus` state and rearranging the
other registers. -/
def fractionalBitFrame {W : Type} {n : ℕ}
    (ψ : QState ((Fin (n + 1) × Fin 2) × W)) :
    QState ((Fin (n + 1) × Bool) × (Fin 2 × W)) :=
  fun p => ψ ((p.1.1,p.2.1),p.2.2) * Minus p.1.2

/-- Projects each record slice of a joint pure-state vector against a specified system vector. -/
def conversionRecordProjection {R H : Type} [Fintype H]
    (v : QState (R × H)) (σ : QState H) : QState R :=
  fun r => Inner σ (fun h => v (r, h))

/-- The system matrix obtained by tracing out the record register of a pure-state outer product. -/
def conversionRecordMarginal {R H : Type} [Fintype R]
    (v : QState (R × H)) : Matrix H H ℂ :=
  fun h k => ∑ r, v (r, h) * star (v (r, k))

/-- A continuous conversion instruction consisting of a known matrix or a timed evolution with a
time-dependent driver and an oracle-sign flag. -/
inductive ContinuousConversionStep (H : Type) where
  | known : Matrix H H ℂ → ContinuousConversionStep H
  | evolve : (ℝ → Matrix H H ℂ) → ℝ → Bool → ContinuousConversionStep H

/-- The Volterra integral equation for an evolution starting at the identity, together with
continuity on the time interval. -/
def continuousConversionVolterra {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) (U : ℝ → Matrix H H ℂ) : Prop :=
  U 0 = 1 ∧ ContinuousOn U (Set.Icc 0 T) ∧
  ∀ t ∈ Set.Icc 0 T, U t = 1 + Matrix.of (fun i j =>
    ∫ s in (0 : ℝ)..t, ((-Complex.I) • (K s * U s)) i j)

/-- Selects the final value of a solution to the Volterra equation when one exists, and returns
the identity otherwise. -/
def continuousConversionEndpoint {H : Type} [Fintype H] [DecidableEq H]
    (K : ℝ → Matrix H H ℂ) (T : ℝ) : Matrix H H ℂ :=
  if h : ∃ U, continuousConversionVolterra K T U then Classical.choose h T else 1

/-- Embeds known matrices and signed query symbols into continuous instructions, assigning unit
duration and zero driver to each query. -/
def continuousConversionWord {H : Type} (C : List (Matrix H H ℂ ⊕ Bool)) :
    List (ContinuousConversionStep H) :=
  C.map (fun s => match s with
    | .inl U => .known U
    | .inr adj => .evolve (fun _ => 0) 1 adj)

/-- Requires known matrices to be unitary and evolution segments to have nonnegative durations,
integrable entries, and Hermitian drivers. -/
def continuousConversionLegal {H : Type} [Fintype H] [DecidableEq H]
    (C : List (ContinuousConversionStep H)) : Prop :=
  ∀ s ∈ C, match s with
    | .known U => U ∈ Matrix.unitaryGroup H ℂ
    | .evolve K T _ => 0 ≤ T ∧
        (∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T) ∧
        ∀ t ∈ Set.Icc 0 T, (K t).IsHermitian

/-- The sum of evolution durations in a continuous conversion word, with zero duration for known
matrices. -/
def continuousConversionTime {H : Type} (C : List (ContinuousConversionStep H)) : ℝ :=
  (C.map (fun s => match s with | .known _ => 0 | .evolve _ T _ => T)).sum

/-- The reverse-ordered product of known matrices and evolution endpoints with the chosen
positive or negative oracle contribution. -/
def continuousConversionMatrix {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (C : List (ContinuousConversionStep H)) : Matrix H H ℂ :=
  (C.map (fun s => match s with
    | .known U => U
    | .evolve K T adj => continuousConversionEndpoint
        (fun t => K t + (if adj then -O else O)) T)).reverse.prod

/-- Applies a family of matrices to each record slice and stores the matrix index in an
additional record register. -/
def conversionRecordKraus {K R H : Type} [Fintype H]
    (A : K → Matrix H H ℂ) (v : QState (R × H)) : QState ((K × R) × H) :=
  fun p => (A p.1.1 *ᵥ (fun h => v (p.1.2, h))) p.2

/-- The matrix formed by summing `i` times the difference of the two mixed inner products over
query positions. -/
def continuousConversionTangent {X H : Type} [Fintype H] {n : ℕ}
    (ψ χ : X → Fin n → QState H) : Matrix X X ℂ :=
  fun x y => ∑ j, Complex.I * (Inner (χ x j) (ψ y j) - Inner (ψ x j) (χ y j))

/-- Combines the state and tangent vectors into the false and true components of a Boolean
register. -/
def continuousConversionTangentLeft {X H : Type} {n : ℕ}
    (ψ χ : X → Fin n → QState H) (j : Fin n) (x : X) : QState (Bool × H) :=
  fun p => if p.1 then χ x j p.2 else ψ x j p.2

/-- Combines the tangent and state vectors into a Boolean register with respective factors `-i`
and `i`. -/
def continuousConversionTangentRight {X H : Type} {n : ℕ}
    (ψ χ : X → Fin n → QState H) (j : Fin n) (x : X) : QState (Bool × H) :=
  fun p => if p.1 then Complex.I * ψ x j p.2 else -Complex.I * χ x j p.2

/-- The partial trace over the record index of a matrix on the joint record and system space. -/
def conversionTraceRecord {R H : Type} [Fintype R]
    (D : Matrix (R × H) (R × H) ℂ) : Matrix H H ℂ :=
  fun h k => ∑ r, D (r,h) (r,k)

/-- The matrix block obtained by fixing the record coordinate of the row index. -/
def conversionRecordBlock {R H S : Type} (V : Matrix (R × H) S ℂ) (r : R) :
    Matrix H S ℂ := fun h s => V (r,h) s

end Qatlib.Concepts.QueryComplexity.DegreeMethod
