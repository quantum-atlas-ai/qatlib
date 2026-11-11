/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs

/-!
# Lemma 10 exact phase arithmetic

This module proves the exact phase power identities `lemma10_phase_power` and
`lemma10_phase_power_neg` and bounds a step count specified by an inverse sine formula. Given an
odd integer satisfying that formula, `lemma10_exact_pi_over_two` packages the exact angle
`Real.pi / 2`, both phase powers, and the scalar step bound.

These conditional identities support the exact phase analysis of Lemma 10 in [BerryChilds2012].

## Main statements

* `lemma10_phase_power` and `lemma10_phase_power_neg` give the conditional exact phase
  identities.
* `lemma10_exact_pi_over_two` collects the identities and step bound for a supplied odd integer
  witness.

## References

* [Berry and Childs, 2012][BerryChilds2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Unitary

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

/-- If `d * θ = Real.pi / 2`, then the natural power `(exp (θ * I)) ^ d` equals `I`. See [Berry
and Childs, Lemma 10][BerryChilds2012]. -/
theorem lemma10_phase_power {θ : ℝ} {d : ℕ} (hd : (d : ℝ) * θ = Real.pi / 2) :
    (Complex.exp (θ * Complex.I)) ^ d = Complex.I := by
  rw [← Complex.exp_nat_mul]
  have harg : (↑d : ℂ) * (↑θ * Complex.I) = (↑Real.pi / 2) * Complex.I := by
    have : (↑d : ℂ) * (↑θ * Complex.I) = ((d : ℝ) * θ : ℝ) * Complex.I := by
      push_cast
      ring
    rw [this, hd]
    push_cast
    ring
  rw [harg, Complex.exp_pi_div_two_mul_I]

/-- If `d * θ = Real.pi / 2` and `d` is odd, then `(-exp (θ * I)) ^ d` equals `-I`. See [Berry
and Childs, Lemma 10][BerryChilds2012]. -/
theorem lemma10_phase_power_neg {θ : ℝ} {d : ℕ} (hd : (d : ℝ) * θ = Real.pi / 2)
    (hodd : Odd d) :
    (-Complex.exp (θ * Complex.I)) ^ d = -Complex.I := by
  rw [Odd.neg_pow hodd, lemma10_phase_power hd]

/-- For nonzero `arcsin (ε / Λ1)`, a natural step count equal to `Real.pi / (2 * arcsin (ε /
Λ1))` satisfies the exact angle identity. -/
theorem lemma10_d_mul_arcsin {ε Λ1 : ℝ} {d : ℕ}
    (harc : Real.arcsin (ε / Λ1) ≠ 0)
    (hd : (d : ℝ) = Real.pi / (2 * Real.arcsin (ε / Λ1))) :
    (d : ℝ) * Real.arcsin (ε / Λ1) = Real.pi / 2 := by
  rw [hd]
  field_simp

/-- For `0 < x ≤ 1`, the inverse sine satisfies `x ≤ arcsin x`. See [Berry and Childs, Lemma
10][BerryChilds2012]. -/
theorem lemma10_arcsin_ge_self {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x ≤ Real.arcsin x := by
  have hsin : Real.sin x ≤ x := Real.sin_le hx0.le
  have hmono : Real.arcsin (Real.sin x) ≤ Real.arcsin x := Real.arcsin_le_arcsin hsin
  have hxπ : x ≤ Real.pi / 2 := by nlinarith [Real.two_le_pi]
  have hxneg : -(Real.pi / 2) ≤ x := by nlinarith [Real.two_le_pi]
  have hsinarc : Real.arcsin (Real.sin x) = x := Real.arcsin_sin hxneg hxπ
  linarith

/-- For positive `ε ≤ Λ1`, a step count equal to `Real.pi / (2 * arcsin (ε / Λ1))` is at most
`(Real.pi / 2) * (Λ1 / ε)`. See [Berry and Childs, Lemma 10][BerryChilds2012]. -/
theorem lemma10_steps_le {ε Λ1 : ℝ} {d : ℕ} (hε0 : 0 < ε) (hΛ1 : 0 < Λ1) (hεΛ : ε ≤ Λ1)
    (hd : (d : ℝ) = Real.pi / (2 * Real.arcsin (ε / Λ1))) :
    (d : ℝ) ≤ (Real.pi / 2) * (Λ1 / ε) := by
  have hx0 : 0 < ε / Λ1 := div_pos hε0 hΛ1
  have hx1 : ε / Λ1 ≤ 1 := by
    rw [div_le_one hΛ1]
    exact hεΛ
  have harc := lemma10_arcsin_ge_self hx0 hx1
  have hden : 0 < 2 * Real.arcsin (ε / Λ1) := by linarith
  have hden2 : 0 < 2 * (ε / Λ1) := by linarith
  rw [hd, div_le_iff₀ hden]
  have hkey : Real.pi ≤ (Real.pi / 2 * (Λ1 / ε)) * (2 * Real.arcsin (ε / Λ1)) := by
    have heq : (Real.pi / 2 * (Λ1 / ε)) * (2 * (ε / Λ1)) = Real.pi := by
      field_simp
    have hmono : (Real.pi / 2 * (Λ1 / ε)) * (2 * (ε / Λ1)) ≤
        (Real.pi / 2 * (Λ1 / ε)) * (2 * Real.arcsin (ε / Λ1)) := by
      have hc : 0 ≤ Real.pi / 2 * (Λ1 / ε) := by positivity
      nlinarith [harc, hc]
    calc Real.pi = (Real.pi / 2 * (Λ1 / ε)) * (2 * (ε / Λ1)) := heq.symm
      _ ≤ (Real.pi / 2 * (Λ1 / ε)) * (2 * Real.arcsin (ε / Λ1)) := hmono
  exact hkey

/-- Under the stated black box hypotheses and the existence of an odd integer satisfying the
prescribed inverse sine formula, obtain that integer with exact phase powers `I` and `-I`
and the step bound `(Real.pi / 2) * (Λ1 / ε)`. This is the conditional phase arithmetic for
Lemma 10 of [BerryChilds2012]. -/
theorem lemma10_exact_pi_over_two
    (BB : BlackBox ι D L) {Λ1 ε : ℝ}
    (hsp : IsColumnSparse BB.H D)
    (hΛ1 : colSumNorm BB.H ≤ Λ1) (hΛ1pos : 0 < Λ1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεΛ : ε ≤ Λ1)
    (hsq : BB.H.mat * BB.H.mat = 1)
    (hodd : ∃ d : ℕ, Odd d ∧ (d : ℝ) = Real.pi / (2 * Real.arcsin (ε / Λ1))) :
    ∃ d : ℕ, Odd d ∧ (d : ℝ) * Real.arcsin (ε / Λ1) = Real.pi / 2 ∧
      (Complex.exp (Real.arcsin (ε / Λ1) * Complex.I)) ^ d = Complex.I ∧
      (-Complex.exp (Real.arcsin (ε / Λ1) * Complex.I)) ^ d = -Complex.I ∧
      (d : ℝ) ≤ (Real.pi / 2) * (Λ1 / ε) := by
  obtain ⟨d, hodd, hd⟩ := hodd
  have hx0 : 0 < ε / Λ1 := div_pos hε0 hΛ1pos
  have harc : Real.arcsin (ε / Λ1) ≠ 0 :=
    ne_of_gt ((Real.arcsin_pos).mpr hx0)
  have hdmul := lemma10_d_mul_arcsin harc hd
  exact ⟨d, hodd, hdmul, lemma10_phase_power hdmul,
    lemma10_phase_power_neg hdmul hodd, lemma10_steps_le hε0 hΛ1pos hεΛ hd⟩

end Qatlib.Papers.BlackBoxHam09.MainResults.Unitary
