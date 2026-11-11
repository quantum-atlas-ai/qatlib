/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QMLAdvances15 — Appendix B, Lemma 1: probabilistic distance in the quantum SVM

Fixed source: arXiv:1512.02900v1 [quant-ph] (9 Dec 2015), "Advances in quantum machine
learning", J. C. Adcock et al.

Appendix B ("Probabilistic Distance in the Quantum SVM", pp. 35-36) encodes two real
vectors `u` and `vᵢ` as the kets `|u⟩ = u/|u|` and `|vᵢ⟩ = vᵢ/|vᵢ|` (eq. 24), prepares
`|ψ⟩ = (|0⟩|u⟩ + |1⟩|vᵢ⟩)/√2` (eq. 25) and projects the ancilla onto
`|φ⟩ = (|u||0⟩ − |vᵢ||1⟩)/√Z` with `Z = |u|² + |vᵢ|²` (eq. 26). Steps 3 and the proof
of Lemma 1 (eqs. 27-32) show that the success probability is

`p = (1/(2Z)) (|u|² + |vᵢ|² − 2 u·vᵢ) = (1/(2Z)) Dᵢ²`   (eq. 30)

for the Euclidean distance `Dᵢ = |u − vᵢ|` (eq. 31), hence `Dᵢ = √(2pZ)` (eq. 27/32).

We formalise the classical distance identity and the vector-valued ancilla
projection in a real Euclidean space of dimension `n`. The partial projection
leaves `projectedData`, whose norm square includes the data-register cross term
and yields eq. (30). The physical preparation/projection circuits and repeated
estimation of `p` are not implemented here; they are inputs to the lemma rather
than part of its algebraic statement. -/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace

namespace Qatlib.Papers.QMLAdvances15.MainResults

/-- Fixed arXiv:1512.02900v1, eq. (30), p. 35: writing the overlap
`|⟨φ|ψ⟩|²` of eq. (29) in terms of the vector data gives
`p = (1/(2Z)) (‖u‖² + ‖v‖² − 2⟪u, v⟫_ℝ)`, which is `(1/(2Z))` times the squared
Euclidean distance by eq. (31). This records the paper's expansion of the success
probability into the distance form used in eq. (32). -/
theorem success_probability_distance_form {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    (1 / (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))) *
        (‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * ⟪u, v⟫_ℝ)
      = (1 / (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))) * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real]
  ring

/-- Fixed arXiv:1512.02900v1, Lemma 1, eqs. (27) and (32), pp. 35-36: with
`Z = ‖u‖² + ‖v‖² > 0` and success probability `p = (1/(2Z))‖u − v‖²` as derived in
eq. (30), the Euclidean distance can be computed classically as `D = √(2pZ)`, i.e.
`√(2 p Z) = ‖u − v‖`. The positivity hypothesis `Z > 0` is automatic for the
nontrivial vectors used by the source (it excludes the degenerate `u = v = 0`), and
`‖u − v‖ ≥ 0` is the square-root branch used in the paper. -/
theorem source_lemma_one {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hZ : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2) :
    Real.sqrt (2 * ((1 / (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))) * ‖u - v‖ ^ 2) *
        (‖u‖ ^ 2 + ‖v‖ ^ 2)) = ‖u - v‖ := by
  have hZne : ‖u‖ ^ 2 + ‖v‖ ^ 2 ≠ 0 := ne_of_gt hZ
  have harg : 2 * ((1 / (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))) * ‖u - v‖ ^ 2) *
      (‖u‖ ^ 2 + ‖v‖ ^ 2) = ‖u - v‖ ^ 2 := by
    field_simp
  rw [harg, Real.sqrt_sq (norm_nonneg _)]

/-- Fixed arXiv:1512.02900v1, eq. (32), p. 36: the equivalent squared form
`p = D²/(2Z)` stated in the paper's final line, written without division on the
right-hand side. -/
theorem success_probability_squared_distance {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    (‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * ⟪u, v⟫_ℝ) = ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real]
  ring

/-- The normalized real vector denoted by `|u⟩` in eq. (24), defined for a
nonzero input vector. -/
def normalizedVector {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (‖u‖⁻¹ : ℝ) • u

/-- A normalized vector has real inner product one with itself. -/
theorem normalizedVector_self_inner {n : ℕ} {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) : ⟪normalizedVector u, normalizedVector u⟫_ℝ = 1 := by
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  rw [real_inner_self_eq_norm_sq]
  simp only [normalizedVector, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u)]
  field_simp [ne_of_gt hnorm]

/-- Multiplying the normalized state `|u⟩` by the classically known norm
recovers the unnormalized data vector `u`. -/
theorem norm_smul_normalizedVector {n : ℕ} {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) : ‖u‖ • normalizedVector u = u := by
  rw [normalizedVector, smul_smul, mul_inv_cancel₀ (ne_of_gt (norm_pos_iff.mpr hu)),
    one_smul]

/-- The data-register vector left by the ancilla projection in eqs. (28)-(29).
The partial inner product with the ancilla `φ` of eq. (26) produces
`(|u||u⟩ - |v||v⟩)/√(2Z)`; it is not a scalar inner product. -/
def projectedData {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)))⁻¹ •
    (‖u‖ • normalizedVector u - ‖v‖ • normalizedVector v)

/-- The projected data vector is precisely `(u-v)/√(2Z)`. -/
theorem projectedData_eq_sub {n : ℕ} {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    projectedData u v = (Real.sqrt (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)))⁻¹ • (u - v) := by
  rw [projectedData, norm_smul_normalizedVector hu, norm_smul_normalizedVector hv]

/-- Eq. (30): the squared norm left by the ancilla projection is
`‖u-v‖²/(2Z)`, including the data-register cross term. -/
theorem projectedData_norm_sq {n : ℕ} {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖projectedData u v‖ ^ 2 =
      (1 / (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))) * ‖u - v‖ ^ 2 := by
  have hZ : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have hsqrt : 0 < Real.sqrt (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [projectedData_eq_sub hu hv]
  calc
    ‖(Real.sqrt (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)))⁻¹ • (u - v)‖ ^ 2 =
        ((Real.sqrt (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)))⁻¹ * ‖u - v‖) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
    _ = (Real.sqrt (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) ^ 2)⁻¹ * ‖u - v‖ ^ 2 := by
      rw [mul_pow, inv_pow]
    _ = (1 / (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))) * ‖u - v‖ ^ 2 := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))]
      ring

/-- Lemma 1 with its success probability computed from the ancilla projection:
`√(2·‖projectedData‖²·Z) = ‖u-v‖`. This includes eqs. (29)-(32), rather than
assuming the printed probability formula at the outset. -/
theorem source_lemma_one_from_projection {n : ℕ} {u v : EuclideanSpace ℝ (Fin n)}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sqrt (2 * ‖projectedData u v‖ ^ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) =
      ‖u - v‖ := by
  rw [projectedData_norm_sq hu hv]
  exact source_lemma_one u v (by
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity)

end Qatlib.Papers.QMLAdvances15.MainResults
