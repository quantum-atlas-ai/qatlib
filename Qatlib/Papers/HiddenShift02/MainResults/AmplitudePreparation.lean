/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Amplitude states and a two-query circuit

This module defines the support fraction `supportProb` and the support-scaled amplitude function
`amplitudeState`. It proves normalization for functions of unit norm on a nonempty support and
records the evaluation and resource counts of `lemma1Circuit`.

The development follows [VanDamHallgrenIp2006].

## Main statements

* `amplitudeState_normalized`: If `f` has nonempty support and unit norm at every nonzero value,
  `amplitudeState f` is normalized.
* `run_lemma1Circuit`: Running `lemma1Circuit` applies the oracle, then the phase gate, then the
  oracle again to the input state.
* `source_lemma1`: Combines the uniform support-measurement probability, normalization of the
  support-scaled amplitude state, and the two-query, one-gate counts under the stated support
  and unit-norm hypotheses.

## References

* [van Dam et al., 2006][VanDamHallgrenIp2006]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

namespace Qatlib.Papers.HiddenShift02.MainResults.AmplitudePreparation

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- The cardinality of the set on which the complex-valued function `f` is nonzero. -/
noncomputable def supportCard (f : G → ℂ) : ℕ :=
  Fintype.card {x : G // f x ≠ 0}

/-- The fraction of elements of `G` at which `f` is nonzero. -/
noncomputable def supportProb (f : G → ℂ) : ℝ :=
  (supportCard f : ℝ) / (Fintype.card G : ℝ)

/-- The amplitude function obtained by dividing `f` by the square root of its support
cardinality. -/
noncomputable def amplitudeState (f : G → ℂ) : QState G :=
  fun x => f x / (Real.sqrt (supportCard f : ℝ) : ℂ)

/-- The support cardinality equals the cardinality of the corresponding filter of the universal
finite set. -/
theorem supportCard_eq_card_filter (f : G → ℂ) :
    supportCard f = (Finset.univ.filter (fun x => f x ≠ 0)).card := by
  classical
  unfold supportCard
  rw [Fintype.card_subtype]

/-- For nonempty finite `G`, measuring the support of `f` in the uniform state has probability
`supportProb f` ([Lemma 1][VanDamHallgrenIp2006]). -/
theorem prep_success_prob (f : G → ℂ) (hG : 0 < Fintype.card G) :
    MeasureProb (Uniform G) (Finset.univ.filter (fun x => f x ≠ 0)) = supportProb f := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr hG
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card G) := Real.sqrt_pos_of_pos hcard
  have hpt : ∀ x : G, BornProb (Uniform G) x = (Fintype.card G : ℝ)⁻¹ := by
    intro x
    unfold BornProb Uniform
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le, inv_pow,
      Real.sq_sqrt hcard.le]
  unfold MeasureProb supportProb supportCard
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_const, nsmul_eq_mul,
    Fintype.card_subtype]
  field_simp

/-- A function that is nonzero somewhere has positive support cardinality. -/
theorem supportCard_pos {f : G → ℂ} (h : ∃ x, f x ≠ 0) : 0 < supportCard f := by
  classical
  unfold supportCard
  exact Fintype.card_pos_iff.mpr ⟨⟨Classical.choose h, Classical.choose_spec h⟩⟩

/-- If `f` has nonempty support and unit norm at every nonzero value, `amplitudeState f` is
normalized ([Lemma 1][VanDamHallgrenIp2006]). -/
theorem amplitudeState_normalized (f : G → ℂ)
    (hunit : ∀ x, f x ≠ 0 → ‖f x‖ = 1) (hne : ∃ x, f x ≠ 0) :
    Normalized (amplitudeState f) := by
  classical
  have hn : 0 < supportCard f := supportCard_pos hne
  have hnR : (0 : ℝ) < (supportCard f : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt : (0 : ℝ) < Real.sqrt (supportCard f : ℝ) := Real.sqrt_pos_of_pos hnR
  unfold Normalized amplitudeState
  have hnorm : ‖(Real.sqrt (supportCard f : ℝ) : ℂ)‖ = Real.sqrt (supportCard f : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
  have hterm : ∀ x : G, ‖f x / (Real.sqrt (supportCard f : ℝ) : ℂ)‖ ^ 2 =
      if f x ≠ 0 then ((supportCard f : ℝ))⁻¹ else 0 := by
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · rw [if_pos hx, norm_div, div_pow, hnorm, hunit x hx, one_pow,
        Real.sq_sqrt hnR.le, one_div]
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, ← supportCard_eq_card_filter]
  have hne' : (supportCard f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [mul_inv_cancel₀ hne']

/-- Expresses the amplitude state pointwise as `f` multiplied by the inverse square root of its
support cardinality ([Lemma 1][VanDamHallgrenIp2006]). -/
theorem amplitudeState_eq_superposition (f : G → ℂ) :
    amplitudeState f = fun x => f x * ((Real.sqrt (supportCard f : ℝ) : ℂ))⁻¹ := by
  funext x
  unfold amplitudeState
  rw [div_eq_mul_inv]

/-- The circuit consisting of an oracle query, the supplied phase gate, and a second oracle
query. -/
def lemma1Circuit (phaseGate : Matrix G G ℂ) : Circuit G :=
  [Step.query, Step.gate phaseGate, Step.query]

/-- The amplitude-preparation circuit contains two oracle queries ([Lemma
1][VanDamHallgrenIp2006]). -/
@[simp] theorem lemma1Circuit_queryCount (phaseGate : Matrix G G ℂ) :
    QueryCount (lemma1Circuit phaseGate) = 2 := rfl

/-- The amplitude-preparation circuit contains one explicit gate. -/
@[simp] theorem lemma1Circuit_gateCount (phaseGate : Matrix G G ℂ) :
    GateCount (lemma1Circuit phaseGate) = 1 := rfl

/-- Running `lemma1Circuit` applies the oracle, then the phase gate, then the oracle again to
the input state ([Lemma 1][VanDamHallgrenIp2006]). -/
theorem run_lemma1Circuit (oracle phaseGate : Matrix G G ℂ) (ψ : QState G) :
    Run oracle (lemma1Circuit phaseGate) ψ =
      ApplyGate oracle (ApplyGate phaseGate (ApplyGate oracle ψ)) := by
  simp [lemma1Circuit, Run, ApplyGate]

/-- Combines the uniform support-measurement probability, normalization of the support-scaled
amplitude state, and the two-query, one-gate counts under the stated support and unit-norm
hypotheses ([Lemma 1][VanDamHallgrenIp2006]). -/
theorem source_lemma1 (f : G → ℂ) (hG : 0 < Fintype.card G)
    (hunit : ∀ x, f x ≠ 0 → ‖f x‖ = 1) (hne : ∃ x, f x ≠ 0)
    (phaseGate : Matrix G G ℂ) :
    MeasureProb (Uniform G) (Finset.univ.filter (fun x => f x ≠ 0)) = supportProb f ∧
      Normalized (amplitudeState f) ∧
      QueryCount (lemma1Circuit phaseGate) = 2 ∧
      GateCount (lemma1Circuit phaseGate) = 1 :=
  ⟨prep_success_prob f hG, amplitudeState_normalized f hunit hne, rfl, rfl⟩

end Qatlib.Papers.HiddenShift02.MainResults.AmplitudePreparation
