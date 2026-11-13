/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.AdiabaticTheorem
import Qatlib.Papers.LocalHam06.MainResults.QmaComplete

/-!
# Operator-path estimates and endpoint energy promises

This module bounds the quadratic operator path `pathOp`, its derivative expressions, and its
variation on the unit interval. It also gives a norm decomposition and a matrix path ending at
the padded history Hamiltonian with the yes/no energy promises used in the construction of
[KempeKitaevRegev2006].

## Main statements

* `path_norm_bounds`: Bounds the quadratic path and its derivative expressions.
* `path_lipschitz`: Controls variation of the path on the unit interval.
* `adiabatic_simulation_two_local`: Constructs a path with the stated endpoint energy
  guarantees.

## References

* [Kempe et al., 2006][KempeKitaevRegev2006]
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

set_option maxHeartbeats 800000

open scoped Classical BigOperators Kronecker ComplexOrder
open InnerProductSpace Matrix

namespace Qatlib.Papers.LocalHam06.MainResults.AdiabaticSimulation

open Qatlib.Papers.LocalHam06.MainResults Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Papers.LocalHam06.MainResults.OperatorDefs
open Qatlib.Papers.LocalHam06.MainResults.AdiabaticTheorem
open Qatlib.Papers.LocalHam06.MainResults.QmaComplete
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Nontrivial E]

/-- The quadratic operator path `A + s • B + s^2 • Cp`. -/
def pathOp (A B Cp : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  A + s • B + s ^ 2 • Cp

/-- On the unit interval, the quadratic path has norm at most `‖A‖ + ‖B‖ + ‖Cp‖`, its first
derivative expression has norm at most `‖B‖ + 2 * ‖Cp‖`, and its second derivative
expression has norm `2 * ‖Cp‖` [KempeKitaevRegev2006]. -/
theorem path_norm_bounds (A B Cp : E →L[ℂ] E) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖pathOp A B Cp s‖ ≤ ‖A‖ + ‖B‖ + ‖Cp‖ ∧
      ‖B + (2 * s) • Cp‖ ≤ ‖B‖ + 2 * ‖Cp‖ ∧
      ‖(2 : ℝ) • Cp‖ = 2 * ‖Cp‖ := by
  have hs : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, hs1⟩
  have hs2 : ‖s ^ 2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
    nlinarith
  have h2s : ‖(2 * s : ℝ)‖ ≤ 2 := by
    have hs' := abs_le.mp hs
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hs'.1, hs'.2]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ‖pathOp A B Cp s‖ ≤ ‖A‖ + ‖s • B‖ + ‖s ^ 2 • Cp‖ := by
      unfold pathOp
      calc ‖A + s • B + s ^ 2 • Cp‖ ≤ ‖A + s • B‖ + ‖s ^ 2 • Cp‖ := norm_add_le _ _
        _ ≤ ‖A‖ + ‖s • B‖ + ‖s ^ 2 • Cp‖ := by
            linarith [norm_add_le A (s • B)]
    rw [norm_smul, norm_smul] at h1
    have hB : ‖s‖ * ‖B‖ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg B)
    have hC : ‖s ^ 2‖ * ‖Cp‖ ≤ 1 * ‖Cp‖ :=
      mul_le_mul_of_nonneg_right hs2 (norm_nonneg Cp)
    linarith
  · have h1 : ‖B + (2 * s) • Cp‖ ≤ ‖B‖ + ‖(2 * s) • Cp‖ := norm_add_le _ _
    rw [norm_smul] at h1
    have hm : ‖(2 * s : ℝ)‖ * ‖Cp‖ ≤ 2 * ‖Cp‖ :=
      mul_le_mul_of_nonneg_right h2s (norm_nonneg Cp)
    linarith
  · rw [norm_smul]
    norm_num

/-- Given bounds `pA`, `pB`, and `pC` on the three coefficient norms, the path and its first two
derivative expressions satisfy the corresponding sum bounds on the unit interval
[KempeKitaevRegev2006]. -/
theorem path_polynomial_bounds (A B Cp : E →L[ℂ] E) (pA pB pC : ℝ)
    (hA : ‖A‖ ≤ pA) (hB : ‖B‖ ≤ pB) (hC : ‖Cp‖ ≤ pC)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖pathOp A B Cp s‖ ≤ pA + pB + pC ∧
      ‖B + (2 * s) • Cp‖ ≤ pB + 2 * pC ∧
      ‖(2 : ℝ) • Cp‖ ≤ 2 * pC := by
  obtain ⟨h1, h2, h3⟩ := path_norm_bounds A B Cp hs0 hs1
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [h3]
    linarith

/-- The difference of two path values is `(s - t) • B + (s^2 - t^2) • Cp`. -/
theorem pathOp_sub (A B Cp : E →L[ℂ] E) (s t : ℝ) :
    pathOp A B Cp s - pathOp A B Cp t =
      (s - t) • B + (s ^ 2 - t ^ 2) • Cp := by
  unfold pathOp
  module

/-- On the unit interval, the quadratic path varies by at most `(‖B‖ + 2 * ‖Cp‖) * |s - t|`
[KempeKitaevRegev2006]. -/
theorem path_lipschitz (A B Cp : E →L[ℂ] E) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖pathOp A B Cp s - pathOp A B Cp t‖ ≤
      (‖B‖ + 2 * ‖Cp‖) * |s - t| := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  have hst : |s + t| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hsum : |s ^ 2 - t ^ 2| = |s - t| * |s + t| := by
    have : s ^ 2 - t ^ 2 = (s - t) * (s + t) := by ring
    rw [this, abs_mul]
  have hdiff : pathOp A B Cp s - pathOp A B Cp t =
      (s - t) • B + (s ^ 2 - t ^ 2) • Cp := pathOp_sub A B Cp s t
  rw [hdiff]
  calc
    ‖(s - t) • B + (s ^ 2 - t ^ 2) • Cp‖ ≤
        ‖(s - t) • B‖ + ‖(s ^ 2 - t ^ 2) • Cp‖ := norm_add_le _ _
    _ = |s - t| * ‖B‖ + |s ^ 2 - t ^ 2| * ‖Cp‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = |s - t| * ‖B‖ + (|s - t| * |s + t|) * ‖Cp‖ := by rw [hsum]
    _ = |s - t| * (‖B‖ + |s + t| * ‖Cp‖) := by ring
    _ ≤ |s - t| * (‖B‖ + 2 * ‖Cp‖) := by
        have habs : 0 ≤ |s - t| := abs_nonneg _
        have hcoef : ‖B‖ + |s + t| * ‖Cp‖ ≤ ‖B‖ + 2 * ‖Cp‖ := by
          have hC : |s + t| * ‖Cp‖ ≤ 2 * ‖Cp‖ :=
            mul_le_mul_of_nonneg_right hst (norm_nonneg Cp)
          linarith
        exact mul_le_mul_of_nonneg_left hcoef habs
    _ = (‖B‖ + 2 * ‖Cp‖) * |s - t| := by ring

/-- For a unit vector `w`, the squared norm of `v` is the squared magnitude of its coefficient
along `w` plus the squared norm of its orthogonal remainder [KempeKitaevRegev2006]. -/
theorem norm_sq_decompose (w v : E) (hw : ‖w‖ = 1) :
    ‖v‖ ^ 2 = ‖inner ℂ w v‖ ^ 2 + ‖v - (inner ℂ w v) • w‖ ^ 2 := by
  set c : ℂ := inner ℂ w v with hc
  have hww : inner ℂ w w = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    norm_num
  have hwrest : inner ℂ w (v - c • w) = 0 := by
    rw [inner_sub_right, inner_smul_right, hww, hc]
    ring
  have horth : inner ℂ (c • w) (v - c • w) = 0 := by
    rw [inner_smul_left, hwrest, mul_zero]
  have hdecomp : v = c • w + (v - c • w) := by abel
  calc
    ‖v‖ ^ 2 = ‖c • w + (v - c • w)‖ ^ 2 := by
        conv_lhs => rw [hdecomp]
    _ = ‖c • w‖ ^ 2 + ‖v - c • w‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • w) (v - c • w) horth
    _ = ‖c‖ ^ 2 + ‖v - c • w‖ ^ 2 := by rw [norm_smul, hw, mul_one]

/-- Under the stated completeness and soundness parameter bounds, there exists a matrix path
from zero to the padded history Hamiltonian whose endpoint satisfies the specified yes/no
energy promises [KempeKitaevRegev2006]. -/
theorem adiabatic_simulation_two_local
    (C : QmaHistoryCircuit) (a ε : ℝ)
    (hε : ε ≤ 1 / 4)
    (ha : 1 - a ≤ 1 / ((2 : ℝ) ^ 14 * (((paid64 C).gates.length : ℝ) + 1) ^ 2)) :
    ∃ H : ℝ → Matrix (Phys (paid64 C)) (Phys (paid64 C)) ℂ,
      H 0 = 0 ∧ H 1 = fullHamiltonian (paid64 C) ∧
        (YesWitness C a →
          ∃ η : QState (Phys (paid64 C)),
            Normalized η ∧ energy (H 1) η ≤ yesCut (paid64 C)) ∧
        (NoSound C ε →
          ∀ η : QState (Phys (paid64 C)),
            Normalized η → noCut (paid64 C) ≤ energy (H 1) η) := by
  have h := padded_full_contract C a ε hε ha
  refine ⟨fun s => (s : ℂ) • fullHamiltonian (paid64 C), ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro hy
    simpa using h.1 hy
  · intro hno
    simpa using h.2.1 hno

end Qatlib.Papers.LocalHam06.MainResults.AdiabaticSimulation
