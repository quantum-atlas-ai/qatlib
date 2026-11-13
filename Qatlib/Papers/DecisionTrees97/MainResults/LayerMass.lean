/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DecisionTrees97.MainResults.ClassicalMass

/-!
# Endpoint transfer from a layer of targets

This module extracts a target with sufficiently large classical kernel mass from a finite target
set. It then applies the endpoint transfer estimate to obtain a bounded-time quantum measurement
witness, with explicit dependence on the number of targets.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `exists_level_mass_ge`: extracts a target with at least the average required signal.
* `finite_multileaf_endpoint_transfer`: transfers total target mass to a quantum endpoint
  witness.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LchsSimulation.StaticLchs.FinitePassage
open Qatlib.Concepts.GraphLaplacian.LaplacianPsd
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.DecisionTrees97.MainResults

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If the total real classical-kernel mass on a nonempty finite target set is at least `p`, one
target has mass at least `p / targets.card`. See [FarhiGutmann1998]. -/
theorem exists_level_mass_ge (T p : ℝ) (hp : 0 < p) (targets : Finset V)
    (hne : targets.Nonempty) (start : V)
    (hsignal : p ≤ ∑ x ∈ targets, (sourceClassicalKernel G T x start).re) :
    ∃ x ∈ targets,
      p / (targets.card : ℝ) ≤ (sourceClassicalKernel G T x start).re := by
  have hcard : (0 : ℝ) < (targets.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hconst : (∑ _y ∈ targets, p / (targets.card : ℝ)) = p := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hle : (∑ _y ∈ targets, p / (targets.card : ℝ)) ≤
      ∑ y ∈ targets, (sourceClassicalKernel G T y start).re := by
    rw [hconst]
    exact hsignal
  exact Finset.exists_le_of_sum_le hne hle

/-- A total classical signal at least `p` on a nonempty finite target set yields a target and a
unitary evolution time at most `33 * T * targets.card / p`, with normalized state and target
probability at least `(p / targets.card) ^ 2 / 16`. See [FarhiGutmann1998]. -/
theorem finite_multileaf_endpoint_transfer (T p : ℝ) (hT : 0 ≤ T)
    (hp : 0 < p) (hp1 : p ≤ 1) (targets : Finset V) (hne : targets.Nonempty)
    (start : V)
    (hsignal : p ≤ ∑ x ∈ targets, (sourceClassicalKernel G T x start).re) :
    ∃ x ∈ targets, ∃ t : ℝ, 0 ≤ t ∧
      t ≤ 33 * T * (targets.card : ℝ) / p ∧
      hamiltonianEvolution (G.lapMatrix ℂ) t ∈ Matrix.unitaryGroup V ℂ ∧
      Normalized (ApplyGate (hamiltonianEvolution (G.lapMatrix ℂ) t) (Ket start)) ∧
      (p / (targets.card : ℝ)) ^ 2 / 16 ≤ MeasureProb
        (ApplyGate (hamiltonianEvolution (G.lapMatrix ℂ) t) (Ket start)) {x} := by
  have hcard : (0 : ℝ) < (targets.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hcpos : 0 < p / (targets.card : ℝ) := div_pos hp hcard
  have hcard1 : (1 : ℝ) ≤ (targets.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hcle : p / (targets.card : ℝ) ≤ 1 := by
    rw [div_le_one hcard]
    exact hp1.trans hcard1
  obtain ⟨x, hx, hxle⟩ := exists_level_mass_ge G T p hp targets hne start hsignal
  obtain ⟨t, ht0, htT, huni, hnorm, hborn⟩ :=
    finite_unique_endpoint_transfer G T (p / (targets.card : ℝ)) hT hcpos hcle x start hxle
  refine ⟨x, hx, t, ht0, ?_, huni, hnorm, hborn⟩
  have hpne : p ≠ 0 := ne_of_gt hp
  have hccne : (targets.card : ℝ) ≠ 0 := ne_of_gt hcard
  calc t ≤ 33 * T / (p / (targets.card : ℝ)) := htT
    _ = 33 * T * (targets.card : ℝ) / p := by
        field_simp

end Qatlib.Papers.DecisionTrees97.MainResults
