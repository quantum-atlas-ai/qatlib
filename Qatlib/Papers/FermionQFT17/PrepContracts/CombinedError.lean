/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Combined Rabi state-preparation error (source Section IV, Eqs. (26)--(27))

Source: Ali Hamed Moosavian and Stephen Jordan, *Faster quantum algorithm to simulate
Fermionic Quantum Field Theory*, fixed version arXiv:1711.04006v3 (23 Oct 2019),
Section IV, Eqs. (26)--(27), and Section IV C.

Section IV states that the success probability of the driven state-preparation step obeys

  `P = 1 - O(λ/δ + λ² t/δ + λ²/ω²)`  (Eq. (26))

and that, because the Rabi rotation to the target one-particle state takes time `t = π/λ`,
the middle term collapses into the first:

  `P = 1 - O(λ/δ + λ²/ω²)`  (Eq. (27)).

This module formalises that collapse exactly. At `t = π/λ` the term `λ² t/δ` equals
`π λ/δ`, so Eq. (26) becomes `(1 + π) λ/δ + λ²/ω²`, which is dominated by
`(1 + π)(λ/δ + λ²/ω²)`. It also shows that the Theorem 1 coefficient `(2νλ + 3νλ²t)/δ` of
Eq. (28) reduces at `t = π/λ` to the linear-in-λ form `ν(2 + 3π) λ/δ` that Section IV C uses
for `2 ε₁`, and converts a deficit `d` of the overlap into the success probability
`(1 - d)² ≥ 1 - 2d`.

Boundary: the paper's `O(·)` hides constants; this module keeps them explicit. The constants
`1 + π` and `2` are the ones produced by the displayed algebra and are not claimed optimal.
The derivation of Eq. (26) from Theorem 1 and Theorem 2 (Section IV C) is formalised
separately in `MainResults.TotalError`; this module covers the `t = π/λ` reduction itself.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.FermionQFT17.PrepContracts.CombinedError

/-- Source Eq. (26): the three-term deficit `λ/δ + λ²t/δ + λ²/ω²` of the Rabi
state-preparation success probability. -/
def combinedDeficit (lam δ t ω : ℝ) : ℝ :=
  lam / δ + lam ^ 2 * t / δ + lam ^ 2 / ω ^ 2

/-- Source Eqs. (26)--(27): at the Rabi pulse time `t = π/λ` the term `λ²t/δ` equals
`π λ/δ`. -/
theorem deficit_at_pulse_time (lam δ ω : ℝ) (hlam : lam ≠ 0) (hδ : δ ≠ 0) :
    combinedDeficit lam δ (Real.pi / lam) ω =
      (1 + Real.pi) * lam / δ + lam ^ 2 / ω ^ 2 := by
  unfold combinedDeficit
  have hmid : lam ^ 2 * (Real.pi / lam) / δ = Real.pi * lam / δ := by
    field_simp
  rw [hmid]
  ring

/-- Source Eq. (27): at `t = π/λ` the three-term deficit of Eq. (26) is bounded by the
two-term deficit `(1 + π)(λ/δ + λ²/ω²)`, i.e. the `λ²t/δ` term is absorbed. -/
theorem deficit_le_two_term (lam δ ω : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hω : 0 < ω) :
    combinedDeficit lam δ (Real.pi / lam) ω ≤
      (1 + Real.pi) * (lam / δ + lam ^ 2 / ω ^ 2) := by
  rw [deficit_at_pulse_time lam δ ω hlam.ne' hδ.ne']
  have hsq : (0 : ℝ) ≤ lam ^ 2 / ω ^ 2 := by positivity
  have hpile : (1 : ℝ) ≤ 1 + Real.pi := by linarith [Real.pi_pos]
  have h2 : lam ^ 2 / ω ^ 2 ≤ (1 + Real.pi) * (lam ^ 2 / ω ^ 2) := by
    nlinarith [hsq, hpile]
  calc (1 + Real.pi) * lam / δ + lam ^ 2 / ω ^ 2
      ≤ (1 + Real.pi) * lam / δ + (1 + Real.pi) * (lam ^ 2 / ω ^ 2) := by linarith [h2]
    _ = (1 + Real.pi) * (lam / δ + lam ^ 2 / ω ^ 2) := by ring

/-- Source Eq. (28) at the pulse time, Section IV C: the Theorem 1 coefficient
`(2νλ + 3νλ²t)/δ` evaluated at `t = π/λ` is `ν(2 + 3π) λ/δ`, so the few-level error is
linear in `λ/δ` at pulse time. -/
theorem fewLevel_coefficient_at_pulse (ν lam δ : ℝ) (hlam : lam ≠ 0) (hδ : δ ≠ 0) :
    (2 * ν * lam + 3 * ν * lam ^ 2 * (Real.pi / lam)) / δ =
      ν * (2 + 3 * Real.pi) * lam / δ := by
  field_simp

/-- Section IV C: if the overlap deficit is `d`, the success probability — the squared
overlap — is at least `1 - 2d`. -/
theorem success_probability_lower (d : ℝ) : 1 - 2 * d ≤ (1 - d) ^ 2 := by
  nlinarith [sq_nonneg d]

/-- Source Eqs. (26)--(27): with the overlap deficit given by Eq. (26) evaluated at the pulse
time `t = π/λ`, the preparation success probability obeys the Eq. (27) lower bound with an
explicit constant, `1 - 2(1 + π)(λ/δ + λ²/ω²)`. -/
theorem prep_success_bound (lam δ ω : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hω : 0 < ω) :
    1 - 2 * (1 + Real.pi) * (lam / δ + lam ^ 2 / ω ^ 2) ≤
      (1 - combinedDeficit lam δ (Real.pi / lam) ω) ^ 2 := by
  have hd0 : 0 ≤ combinedDeficit lam δ (Real.pi / lam) ω := by
    unfold combinedDeficit
    positivity
  have hsq := success_probability_lower (combinedDeficit lam δ (Real.pi / lam) ω)
  have hmono := deficit_le_two_term lam δ ω hlam hδ hω
  nlinarith [hsq, hmono]

end Qatlib.Papers.FermionQFT17.PrepContracts.CombinedError
