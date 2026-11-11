/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Ring.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Operator model for the discrete adiabatic theorem

Berry--Costa--Sanders--Tessler--Babbush--Neven--Wiebe,
*Optimal scaling quantum linear systems solver via discrete adiabatic theorem*,
fixed arXiv:2111.08152.

This file fixes the paper-level vocabulary shared by all claims of the block:

* Definition 1 (Eq. (8)): the finite differences `D` and `D^(2)`;
* Eq. (10): the neighbour maximum `ĉ_k(s)`;
* Eq. (14): the neighbour minimum `Δ̌(s)`;
* Eq. (81): the auxiliary functions `D₁`, `D₂`, `D₃`;
* Eqs. (82)--(85): the coefficient functions `G_{T,1}`, …, `G_{T,4}`;
* Eq. (114): the schedule function `f`, Eq. (112): the gap lower bound `Δ₀`,
  and Eq. (H19): the normalisation constant `d_p`.

Operators are modelled as elements of a unital C*-algebra `R` (for the paper,
the bounded operators on the walk Hilbert space). `IsUnitary` is the paper's
"unitary operator" predicate and `norm_conj_eq` records that conjugation by a
unitary preserves the operator norm, which is the form of unitarity used in
Lemma 11 (Eq. (61)).

Two encoding conventions are used in the scalar definitions and are harmless
for the paper's ranges `0 ≤ s ≤ 1`:

* `ĉ_k` is the maximum of `c_k` over the valid neighbours and `0` otherwise
  (the paper's maximum over `{s−1/T, s, s+1/T} ∩ [0, 1−k/T]`);
* `Δ̌` is the minimum of `Δ` over the valid neighbours and `1` otherwise,
  which agrees with the paper's minimum because the gaps are at most `1`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.AdiabaticQLS21.MainResults.Setup

/-! ## Finite differences (Definition 1, Eq. (8)) -/

/-- Definition 1, Eq. (8): the first finite difference
`D W_T(s) = W_T(s + 1/T) - W_T(s)` of a sequence of operators. -/
def diff {R : Type*} [Ring R] (T : ℝ) (W : ℝ → R) (s : ℝ) : R :=
  W (s + 1 / T) - W s

/-- Definition 1, Eq. (8): the second finite difference
`D^(2) W_T(s) = D W_T(s + 1/T) - D W_T(s)`. -/
def diff2 {R : Type*} [Ring R] (T : ℝ) (W : ℝ → R) (s : ℝ) : R :=
  diff T W (s + 1 / T) - diff T W s

/-! ## Bounded-operator vocabulary -/

/-- The complement `Q_T = I - P_T` of a spectral projector. -/
def compl {R : Type*} [Ring R] (P : R) : R :=
  1 - P

/-- A unitary: `u† u = 1` and `u u† = 1`. -/
def IsUnitary {R : Type*} [Ring R] [StarRing R] (u : R) : Prop :=
  star u * u = 1 ∧ u * star u = 1

section Unitary

variable {R : Type*} [NormedRing R] [NormOneClass R] [StarRing R] [CStarRing R]

/-- A unitary element of a C*-algebra has norm one. -/
lemma IsUnitary.norm_eq_one {u : R} (hu : IsUnitary u) : ‖u‖ = 1 := by
  have h1 : ‖u‖ * ‖u‖ = 1 := by
    have h := CStarRing.norm_star_mul_self (x := u)
    rw [hu.1, norm_one] at h
    exact h.symm
  nlinarith [norm_nonneg u]

/-- The adjoint of a unitary is a unitary. -/
lemma IsUnitary.star {u : R} (hu : IsUnitary u) : IsUnitary (star u) := by
  constructor
  · rw [star_star]
    exact hu.2
  · rw [star_star]
    exact hu.1

/-- Conjugation by a unitary preserves the operator norm (used for Eq. (61)). -/
lemma norm_conj_eq {u x : R} (hu : IsUnitary u) : ‖u * x * star u‖ = ‖x‖ := by
  have hu1 : ‖u‖ = 1 := hu.norm_eq_one
  have hus : ‖star u‖ = ‖u‖ := norm_star u
  apply le_antisymm
  · calc ‖u * x * star u‖ ≤ ‖u * x‖ * ‖star u‖ := norm_mul_le _ _
      _ ≤ (‖u‖ * ‖x‖) * ‖star u‖ := by
          gcongr
          exact norm_mul_le _ _
      _ = ‖x‖ := by rw [hus, hu1]; ring
  · have hx : star u * (u * x * star u) * u = x := by
      calc star u * (u * x * star u) * u = (star u * u) * x * (star u * u) := by
            noncomm_ring
        _ = 1 * x * 1 := by rw [hu.1]
        _ = x := by simp
    conv_lhs => rw [← hx]
    calc ‖star u * (u * x * star u) * u‖ ≤ ‖star u * (u * x * star u)‖ * ‖u‖ := norm_mul_le _ _
      _ ≤ (‖star u‖ * ‖u * x * star u‖) * ‖u‖ := by
          gcongr
          exact norm_mul_le _ _
      _ = ‖u * x * star u‖ := by rw [hus, hu1]; ring

end Unitary

/-! ## Projector algebra (Eqs. (21)--(23)) -/

section Projectors

variable {R : Type*} [Ring R]

/-- The reflection `2 P - I`, written as `P + P - I` so that all identities are
statements in the ring language (Eq. (48) uses `2P_T(s) - I`). -/
def refl (P : R) : R := P + P - 1

/-- The complement of a projector is a projector. -/
lemma compl_mul_compl {P : R} (hP : P * P = P) :
    compl P * compl P = compl P := by
  unfold compl
  noncomm_ring [hP]

/-- A projector is orthogonal to its complement. -/
lemma mul_compl {P : R} (hP : P * P = P) : P * compl P = 0 := by
  unfold compl
  noncomm_ring [hP]

/-- The complement of a projector is orthogonal to the projector. -/
lemma compl_mul {P : R} (hP : P * P = P) : compl P * P = 0 := by
  unfold compl
  noncomm_ring [hP]

/-- The step operator `S_T(s + 1/T, s) = P_T(s+1/T) P_T(s) + Q_T(s+1/T) Q_T(s)`
of Eq. (21), in the argument order used in the proof of Lemma 7
(Eq. (47): `V_T(s) = [I - (P_T(s) - P_T(s+1/T))²]^{-1/2} S_T(s+1/T, s)`). -/
def Sstep (P : ℝ → R) (T : ℝ) (s : ℝ) : R :=
  P (s + 1 / T) * P s + compl (P (s + 1 / T)) * compl (P s)

/-- Algebraic core of Lemma 7 (Eqs. (45)--(47)): using only `P² = P` of the
current projector, `S_T(s+1/T, s) = I + DP_T(s) · (2 P_T(s) - I)`.  In the
argument order of `Sstep` the new factor `P_T(s+1/T)` multiplies on the left,
which is exactly the order appearing in Eq. (47); no commutation between
`P_T(s)` and `P_T(s+1/T)` is required. -/
lemma Sstep_eq {P P' : R} (hP : P * P = P) :
    P' * P + compl P' * compl P = 1 + (P' - P) * refl P := by
  unfold compl refl
  noncomm_ring [hP]

end Projectors

/-! ## Scalar paper functions -/

/-- Eq. (10): `ĉ_k(s)` is the maximum of `c_k` over the neighbours
`s - 1/T, s, s + 1/T` that lie in `[0, 1 - k/T]` (out-of-range neighbours
contribute `0`). -/
def chat (T : ℝ) (c : ℝ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  max (if 0 ≤ s - 1 / T ∧ s - 1 / T ≤ 1 - (k : ℝ) / T then c (s - 1 / T) else 0)
    (max (if 0 ≤ s ∧ s ≤ 1 - (k : ℝ) / T then c s else 0)
      (if 0 ≤ s + 1 / T ∧ s + 1 / T ≤ 1 - (k : ℝ) / T then c (s + 1 / T) else 0))

/-- Eq. (14): `Δ̌(s)` is the minimum of `Δ` over the neighbours
`s - 1/T, s, s + 1/T` that lie in `[0, 1]`; out-of-range neighbours contribute
the neutral value `1` (the gaps are at most `1`). -/
def DeltaCheck (T : ℝ) (Δ : ℝ → ℝ) (s : ℝ) : ℝ :=
  min (if 0 ≤ s - 1 / T ∧ s - 1 / T ≤ 1 then Δ (s - 1 / T) else 1)
    (min (if 0 ≤ s ∧ s ≤ 1 then Δ s else 1)
      (if 0 ≤ s + 1 / T ∧ s + 1 / T ≤ 1 then Δ (s + 1 / T) else 1))

/-- Eq. (81): `D₁(z) = 1/√(1 - z²)`. -/
def Dfun1 (z : ℝ) : ℝ := 1 / Real.sqrt (1 - z ^ 2)

/-- Eq. (81): `D₂(z) = √((1+z)/(1-z)) - 1`. -/
def Dfun2 (z : ℝ) : ℝ := Real.sqrt ((1 + z) / (1 - z)) - 1

/-- Eq. (81): `D₃(z) = z/(1 - z²)^(3/2)`. -/
def Dfun3 (z : ℝ) : ℝ := z / (1 - z ^ 2) ^ (3 / 2 : ℝ)

/-- Eq. (82): the coefficient `G_{T,1}(s)`. -/
def GT1 (T : ℝ) (c1 c2 Δ2 : ℝ → ℝ) (s : ℝ) : ℝ :=
  (c1 s ^ 2 + c1 s * c1 (s + 1 / T)) / (Real.pi * (1 - Real.cos (Δ2 s / 2))) +
    2 * c2 s / Δ2 s

/-- Eq. (83): the coefficient `G_{T,2}(s)`. -/
def GT2 (T : ℝ) (c1 Δ1 : ℝ → ℝ) (G1 : ℝ → ℝ) (s : ℝ) : ℝ :=
  G1 s * Dfun3 (max (2 * c1 (s + 1 / T) / (T * Δ1 (s + 1 / T)))
    (2 * c1 s / (T * Δ1 s)))

/-- Eq. (84): the coefficient `G_{T,3}(s)`. -/
def GT3 (T : ℝ) (c1 Δ1 : ℝ → ℝ) (G1 G2 : ℝ → ℝ) (s : ℝ) : ℝ :=
  G2 s * (1 + 2 * c1 s / (T * Δ1 s)) +
    Dfun1 (2 * c1 s / (T * Δ1 s)) * (G1 s + 8 * c1 s ^ 2 / Δ1 s ^ 2)

/-- Eq. (85): the coefficient `G_{T,4}(s)`. -/
def GT4 (T : ℝ) (c1 : ℝ → ℝ) (G3 : ℝ → ℝ) (s : ℝ) : ℝ :=
  G3 s / T + c1 s

/-- Eq. (114): the schedule function
`f(s) = κ/(κ-1) · (1 - (1 + s(κ^(p-1) - 1))^(1/(1-p)))`. -/
def schedule (κ p s : ℝ) : ℝ :=
  κ / (κ - 1) * (1 - (1 + s * (κ ^ (p - 1) - 1)) ^ (1 / (1 - p)))

/-- Eq. (112): the gap lower bound `Δ₀(s) = 1 - f(s) + f(s)/κ`. -/
def gap0 (κ p s : ℝ) : ℝ :=
  1 - schedule κ p s + schedule κ p s / κ

/-- Eq. (113) and Eq. (H19): the normalisation constant
`d_p = 2^(p/2) · κ/((p-1)(κ-1)) · (κ^(p-1) - 1)`. -/
def dp (κ p : ℝ) : ℝ :=
  2 ^ (p / 2) * κ / ((p - 1) * (κ - 1)) * (κ ^ (p - 1) - 1)

end Qatlib.Papers.AdiabaticQLS21.MainResults.Setup
