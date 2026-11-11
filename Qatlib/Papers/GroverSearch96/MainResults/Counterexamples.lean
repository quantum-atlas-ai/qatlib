/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroverSearch96.MainResults.DiffusionAmplitudes
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.SearchStopping.KnownCount.Theorem3Counterexample
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary21Counterexample

/-!
# Small register counterexamples for Grover search

This module relates real two amplitude data to normalized register states and computes their
actual Grover updates. It records two and four state examples relevant to the scope of the
amplitude gain, positivity, and strict success claims.

`two_state_no_strict_success` shows that the uniform two state search remains at success
probability one half for every iteration count. See [Grover1996].

## Main statements

* `theorem3_actual_two_state_counterexample`: The normalized two state amplitudes `3/5` and
  `4/5` satisfy the displayed positivity and threshold conditions, but one Grover step gives
  `4/5` and `-3/5` with gain at most `1 / (2 * sqrt 2)`.
* `corollary21_actual_four_state_counterexample`: There are normalized four state amplitudes
  with `k < 0 < l` and `|k/l| < sqrt 4` whose ordinary amplitude becomes negative under
  diffusion.
* `two_state_no_strict_success`: For a single marked state in a two state register, every Grover
  iteration count has success probability exactly `1/2`.

## References

* [Grover, 1996][Grover1996]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
namespace Qatlib.Papers.GroverSearch96.MainResults

/-- A singleton marked vector with real amplitudes is normalized exactly when its two amplitude
mass on `2^n` states is one. -/
theorem normalized_singleton_real_iff (n : ℕ) (w : Reg n) (k l : ℝ) :
    Normalized (MarkedVector {w} (k : ℂ) (l : ℂ)) ↔
      twoAmplitudeMass (2^n) k l = 1 := by
  rw [normalized_markedVector_iff]
  simp [twoAmplitudeMass, Complex.normSq_ofReal, pow_two]

/-- A Grover step on a singleton marked vector first negates its marked amplitude and then
applies the two diffusion amplitude formulas. See [Grover1996]. -/
theorem run_singleton_real_step (n : ℕ) (w : Reg n) (k l : ℝ) :
    Run (SetOracle {w}) (GroverStep (Reg n)) (MarkedVector {w} (k : ℂ) (l : ℂ)) =
      MarkedVector {w} (distinguishedAfter (2^n) (-k) l : ℂ)
        (ordinaryAfter (2^n) (-k) l : ℂ) := by
  simp only [GroverStep, run_query, run_gate, run_nil]
  rw [applyGate_setOracle_markedVector]
  simpa only [Complex.ofReal_neg] using theorem2_markedRegister n w (-k) l

/-- The normalized two state amplitudes `3/5` and `4/5` satisfy the displayed positivity and
threshold conditions, but one Grover step gives `4/5` and `-3/5` with gain at most `1 / (2 *
sqrt 2)`. See [Grover1996]. -/
theorem theorem3_actual_two_state_counterexample (w : Reg 1) :
    Normalized (MarkedVector {w} ((3/5 : ℝ) : ℂ) ((4/5 : ℝ) : ℂ)) ∧
      (0 : ℝ) < 3/5 ∧ (3/5 : ℝ) < 1 / Real.sqrt 2 ∧ (0 : ℝ) < 4/5 ∧
      Run (SetOracle {w}) (GroverStep (Reg 1))
        (MarkedVector {w} ((3/5 : ℝ) : ℂ) ((4/5 : ℝ) : ℂ)) =
          MarkedVector {w} ((4/5 : ℝ) : ℂ) ((-3/5 : ℝ) : ℂ) ∧
      (4/5 - 3/5 : ℝ) ≤ 1 / (2 * Real.sqrt 2) := by
  have h := theorem3Counterexample.1
  refine ⟨?_,h.1,h.2.1,h.2.2.1,?_,?_⟩
  · exact (normalized_singleton_real_iff 1 w (3/5) (4/5)).mpr
      (by norm_num [twoAmplitudeMass])
  · rw [run_singleton_real_step]
    norm_num [distinguishedAfter, ordinaryAfter]
  · have hb := h.2.2.2.2.2.1
    norm_num [distinguishedAfter] at hb ⊢
    exact hb

/-- The normalized uniform four state vector has amplitude `1/2` everywhere and becomes the
marked basis state after one Grover step. See [Grover1996]. -/
theorem theorem3_actual_uniform_four_state_counterexample (w : Reg 2) :
    Normalized (MarkedVector {w} ((1/2 : ℝ) : ℂ) ((1/2 : ℝ) : ℂ)) ∧
      (∀ x, MarkedVector {w} ((1/2 : ℝ) : ℂ) ((1/2 : ℝ) : ℂ) x = 1/2) ∧
      Run (SetOracle {w}) (GroverStep (Reg 2))
        (MarkedVector {w} ((1/2 : ℝ) : ℂ) ((1/2 : ℝ) : ℂ)) = Ket w := by
  refine ⟨?_,?_,?_⟩
  · exact (normalized_singleton_real_iff 2 w (1/2) (1/2)).mpr
      (by norm_num [twoAmplitudeMass])
  · intro x
    simp [MarkedVector]
  · rw [run_singleton_real_step]
    norm_num [distinguishedAfter, ordinaryAfter]
    funext x
    simp [MarkedVector, Ket]

/-- There are normalized four state amplitudes with `k < 0 < l` and `|k/l| < sqrt 4` whose
ordinary amplitude becomes negative under diffusion. See [Grover1996]. -/
theorem corollary21_actual_four_state_counterexample (w : Reg 2) :
    ∃ k l : ℝ, k < 0 ∧ 0 < l ∧
      Normalized (MarkedVector {w} (k : ℂ) (l : ℂ)) ∧
      |k/l| < Real.sqrt 4 ∧ ordinaryAfter 4 k l < 0 ∧
      ApplyGate (Diffusion (Reg 2)) (MarkedVector {w} (k : ℂ) (l : ℂ)) =
        MarkedVector {w} (distinguishedAfter 4 k l : ℂ) (ordinaryAfter 4 k l : ℂ) := by
  obtain ⟨N,k,l,hN,hk,hl,hmass,hratio,hbad⟩ := corollary2_1Counterexample
  subst N
  refine ⟨k,l,hk,hl,?_,hratio,hbad,?_⟩
  · exact (normalized_singleton_real_iff 2 w k l).mpr hmass
  · exact theorem2_markedRegister 2 w k l

/-- For a single marked state in a two state register, every Grover iteration count has success
probability exactly `1/2`. See [Grover1996]. -/
theorem two_state_no_strict_success (w : Reg 1) (j : ℕ) :
    MeasureProb (GroverState ({w} : Finset (Reg 1)) j) {w} = 1/2 := by
  have hsqrt : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsin : Real.sin (Real.pi/4)^2 =
      (({w} : Finset (Reg 1)).card : ℝ) / Fintype.card (Reg 1) := by
    rw [Real.sin_pi_div_four]
    norm_num
    nlinarith
  have hs : Real.sin (Real.pi/4) ≠ 0 := by
    rw [Real.sin_pi_div_four]
    positivity
  have hc : Real.cos (Real.pi/4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  rw [measureProb_groverState Fintype.card_pos _ (Real.pi/4) hsin hs hc]
  have hdouble : 2 * ((2*(j:ℝ)+1)*(Real.pi/4)) = (j:ℝ)*Real.pi+Real.pi/2 := by ring
  have hcos : Real.cos (2 * ((2*(j:ℝ)+1)*(Real.pi/4))) = 0 := by
    rw [hdouble, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
  rw [Real.cos_two_mul] at hcos
  nlinarith [Real.sin_sq_add_cos_sq ((2*(j:ℝ)+1)*(Real.pi/4))]

end Qatlib.Papers.GroverSearch96.MainResults
