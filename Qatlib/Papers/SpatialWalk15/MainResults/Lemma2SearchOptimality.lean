/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialWalk15.MainResults.Lemma2TopOverlap
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Uniform eigenvectors and almost-sure overlap bounds

This module proves the action of a regular graph's adjacency matrix on the uniform state and
computes the residual after subtracting its rank-one projector. It also lifts a deterministic
eigenvector-overlap estimate to almost every sample under explicit concentration hypotheses, in
the setting of [ChakrabortyEtAl2016].

## Main statements

* `adjMatrix_regular_uniform_eigenvector`: the uniform state has adjacency eigenvalue equal to
  the degree.
* `regular_lemma2_top_overlap_identity`: exact squared residual for the uniform state.
* `lemma2_top_overlap_almost_surely`: almost-sure squared-overlap lower bound.

## References

* [Chakraborty et al., 2016][ChakrabortyEtAl2016]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.SpatialWalk15.MainResults.Lemma2TopOverlap
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.SpatialWalk15.MainResults.Lemma2SearchOptimality

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in

/-- The adjacency matrix of a graph regular of degree `d` maps the uniform state to `d` times
that state. -/
theorem adjMatrix_regular_uniform_eigenvector (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : G.IsRegularOfDegree d) :
    G.adjMatrix ℂ *ᵥ Uniform V = (d : ℂ) • Uniform V := by
  ext v
  rw [show (G.adjMatrix ℂ *ᵥ Uniform V) v =
      (G.adjMatrix ℂ *ᵥ Function.const V
        (((Real.sqrt (Fintype.card V) : ℂ))⁻¹)) v from rfl]
  rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (G := G) (d := d) hd]
  rw [Pi.smul_apply, Uniform]
  ring

/-- On a finite vertex type of positive cardinality, the inner product of the uniform state with
itself has norm one. -/
theorem regular_uniform_overlap (hN : 0 < Fintype.card V) :
    ‖Inner (Uniform V) (Uniform V)‖ = 1 := by
  have h : Inner (Uniform V) (Uniform V) = 1 :=
    (normalized_iff_inner_self (Uniform V)).1 (normalized_uniform hN)
  rw [h, norm_one]

/-- For a regular graph of degree `d` on a vertex type of positive cardinality, applying its
adjacency matrix minus the uniform-state projector to the uniform state gives squared
Euclidean norm `(d - 1) ^ 2` [ChakrabortyEtAl2016]. -/
theorem regular_lemma2_top_overlap_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : G.IsRegularOfDegree d) (hN : 0 < Fintype.card V) :
    ‖toEuclidean_fromVec ((G.adjMatrix ℂ - rankOneProjector (Uniform V)) *ᵥ Uniform V)‖ ^ 2 =
      ((d : ℝ) - 1) ^ 2 := by
  have hx : Normalized (Uniform V) := normalized_uniform hN
  have heig : G.adjMatrix ℂ *ᵥ Uniform V = ((d : ℝ) : ℂ) • Uniform V := by
    rw [adjMatrix_regular_uniform_eigenvector G hd]
    push_cast
    rfl
  have hid := lemma2_top_overlap_identity (G.adjMatrix ℂ) (Uniform V) (Uniform V)
    ((d : ℕ) : ℝ) hx hx heig
  rw [hid]
  have hinner : Inner (Uniform V) (Uniform V) = 1 := (normalized_iff_inner_self _).1 hx
  rw [hinner]
  norm_num

/-- If almost every matrix is within matrix norm `η ≤ δ` of the projector onto normalized `s`
and possesses a normalized eigenvector with real eigenvalue at least `1 - δ`, then almost
every matrix possesses such an eigenvector with squared overlap at least `1 - 2 * δ` with
`s` [ChakrabortyEtAl2016]. -/
theorem lemma2_top_overlap_almost_surely
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Mof : Ω → Matrix V V ℂ) (s : QState V) (hs : Normalized s)
    (δ η : ℝ) (hη0 : 0 ≤ η) (hηδ : η ≤ δ)
    (hae : ∀ᵐ ω ∂μ, ∃ x : QState V, Normalized x ∧
        ∃ ℓ : ℝ, 1 - δ ≤ ℓ ∧ Mof ω *ᵥ x = (ℓ : ℂ) • x ∧
          ‖Mof ω - rankOneProjector s‖ ≤ η) :
    ∀ᵐ ω ∂μ, ∃ x : QState V, Normalized x ∧
      (∃ ℓ : ℝ, 1 - δ ≤ ℓ ∧ Mof ω *ᵥ x = (ℓ : ℂ) • x) ∧
      1 - 2 * δ ≤ ‖Inner s x‖ ^ 2 := by
  filter_upwards [hae] with ω hω
  obtain ⟨x, hx, ℓ, hℓ, heig, hconc⟩ := hω
  exact ⟨x, hx, ⟨ℓ, hℓ, heig⟩,
    lemma2_top_overlap_from_concentration (Mof ω) s x ℓ δ η
      hs hx heig hη0 hconc hηδ hℓ⟩

/-- For a regular graph of degree `d` on a vertex type of positive cardinality, its adjacency
matrix minus the uniform-state projector maps the uniform state to `(d - 1)` times that
state. -/
theorem regular_perturbation_acts_as_scalar (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : G.IsRegularOfDegree d) (hN : 0 < Fintype.card V) :
    (G.adjMatrix ℂ - rankOneProjector (Uniform V)) *ᵥ Uniform V =
      (((d : ℝ) - 1 : ℝ) : ℂ) • Uniform V := by
  have hx : Normalized (Uniform V) := normalized_uniform hN
  have hself : Inner (Uniform V) (Uniform V) = 1 := (normalized_iff_inner_self _).1 hx
  rw [Matrix.sub_mulVec, adjMatrix_regular_uniform_eigenvector G hd, rankOneProjector_mulVec,
    hself]
  ext v
  simp only [Pi.sub_apply, Pi.smul_apply]
  push_cast
  ring

end Qatlib.Papers.SpatialWalk15.MainResults.Lemma2SearchOptimality
