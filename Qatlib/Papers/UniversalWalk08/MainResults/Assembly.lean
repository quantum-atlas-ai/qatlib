/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.Basic
import Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
import Qatlib.Papers.UniversalWalk08.MainResults.AmplitudeStatistics
import Qatlib.Papers.UniversalWalk08.MainResults.Composition
import Qatlib.Papers.UniversalWalk08.MainResults.Parameters.RunParameters
import Qatlib.Papers.UniversalWalk08.MainResults.Gadgets.GateWidgets
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Circuit statistics and quantum-walk resource bounds

This module assembles normalization, proportionality, success-probability, and time estimates
for the quantum-walk simulation of [Childs2009]. It proves unitarity of `circuitEval`, transfers
circuit output statistics to proportional walk amplitudes, and bounds the selected walk time.

## Main statements

* `conditioned_output_statistics`: Proportional walk and circuit amplitudes yield the same
  conditioned statistics.
* `output_probability_ge_inv_pow_four`: Transfer an inverse-fourth-power scale bound to the
  output probability sum.
* `walkTime_le_two_pow_four`: Bound the selected walk time by `2 * m ^ 4`.

## References

* [Childs, 2009][Childs2009]
-/

set_option warningAsError false

namespace Qatlib.Papers.UniversalWalk08.MainResults.Assembly

open Matrix
open scoped BigOperators

open Qatlib.Papers.UniversalWalk08.MainResults.WalkDefsCore
open Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
open Qatlib.Papers.UniversalWalk08.MainResults.Parameters

set_option autoImplicit false

/-- The product of a list of unitary matrices on the `n`-qubit basis is unitary. -/
theorem list_prod_mem_unitaryGroup {n : ℕ}
    {l : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)}
    (h : ∀ g ∈ l, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    l.prod ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction l with
  | nil => simp
  | cons g gs ih =>
    rw [List.prod_cons]
    exact Submonoid.mul_mem _ (h g (by simp))
      (ih (fun x hx => h x (by simp [hx])))

/-- The matrix evaluating a `GateCircuit` is unitary [Childs2009]. -/
theorem circuitEval_mem_unitaryGroup {n : ℕ} (C : GateCircuit n) :
    circuitEval C ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  list_prod_mem_unitaryGroup C.gates_unitary

/-- The conjugate transpose of a circuit evaluation multiplied by that evaluation is the
identity. -/
theorem circuitEval_conjTranspose_mul {n : ℕ} (C : GateCircuit n) :
    (circuitEval C)ᴴ * circuitEval C = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp (circuitEval_mem_unitaryGroup C)
  simpa [Matrix.star_eq_conjTranspose] using h

/-- The squared moduli of the circuit amplitudes from the zero basis state sum to one
[Childs2009]. -/
theorem sum_normSq_circuitEval_eq_one {n : ℕ} (C : GateCircuit n) :
    ∑ s, Complex.normSq (circuitEval C s (zeroBasis n)) = 1 := by
  have hunit := circuitEval_conjTranspose_mul C
  have hentry := congrFun (congrFun hunit (zeroBasis n)) (zeroBasis n)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at hentry
  have hsumC :
      (∑ d, (((Complex.normSq (circuitEval C d (zeroBasis n))) : ℝ) : ℂ)) = 1 := by
    rw [← hentry]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Matrix.conjTranspose_apply]
  have hre := congrArg Complex.re hsumC
  simpa using hre

/-- Scaling a normalized amplitude family by `scale` makes its total squared amplitude equal to
`Complex.normSq scale`. -/
theorem sum_normSq_of_proportional {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (scale : ℂ)
    (hb : ∑ s, Complex.normSq (b s) = 1)
    (hprop : ∀ s, a s = scale * b s) :
    ∑ s, Complex.normSq (a s) = Complex.normSq scale := by
  have hstep : ∑ s, Complex.normSq (a s) =
      ∑ s, Complex.normSq scale * Complex.normSq (b s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hprop s, Complex.normSq_mul]
  rw [hstep]
  rw [← Finset.mul_sum, hb, mul_one]

/-- If output amplitudes are proportional to a circuit column and the squared scale is at least
`1 / m ^ 4`, their squared moduli sum to at least `1 / m ^ 4` [Childs2009]. -/
theorem success_probability_ge_inv_pow_four {n : ℕ} (C : GateCircuit n)
    (amp : Fin (2 ^ n) → ℂ) (scale : ℂ) {m : ℕ}
    (hprop : ∀ s, amp s = scale * circuitEval C s (zeroBasis n))
    (hscale : 1 / (m : ℝ) ^ 4 ≤ Complex.normSq scale) :
    1 / (m : ℝ) ^ 4 ≤ ∑ s, Complex.normSq (amp s) := by
  rw [sum_normSq_of_proportional amp
    (fun s => circuitEval C s (zeroBasis n)) scale
    (sum_normSq_circuitEval_eq_one C) hprop]
  exact hscale

/-- If walk amplitudes at the designated outputs are proportional to a circuit column with
squared scale at least `1 / m ^ 4`, the sum of their walk probabilities has the same lower
bound [Childs2009]. -/
theorem output_probability_ge_inv_pow_four {n : ℕ} (C : GateCircuit n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (t : ℝ) (start : V) (out : Fin (2 ^ n) → V)
    (scale : ℂ) {m : ℕ}
    (hprop : ∀ s, walkAmplitude A t (out s) start =
      scale * circuitEval C s (zeroBasis n))
    (hscale : 1 / (m : ℝ) ^ 4 ≤ Complex.normSq scale) :
    1 / (m : ℝ) ^ 4 ≤ ∑ s, walkProbability A t (out s) start := by
  have h := success_probability_ge_inv_pow_four C
    (fun s => walkAmplitude A t (out s) start) scale hprop hscale
  simpa [walkProbability] using h

/-- Walk output amplitudes proportional by a nonzero factor to a circuit column have the same
conditioned output statistics as that column [Childs2009]. -/
theorem conditioned_output_statistics {n : ℕ} (C : GateCircuit n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (t : ℝ) (start : V) (out : Fin (2 ^ n) → V)
    (scale : ℂ) (hscale : scale ≠ 0)
    (hprop : ∀ s, walkAmplitude A t (out s) start =
      scale * circuitEval C s (zeroBasis n)) :
    ∀ s, walkProbability A t (out s) start /
        (∑ r, walkProbability A t (out r) start) =
      Complex.normSq (circuitEval C s (zeroBasis n)) /
        (∑ r, Complex.normSq (circuitEval C r (zeroBasis n))) := by
  intro s
  have hb : ∑ r, Complex.normSq (circuitEval C r (zeroBasis n)) ≠ 0 := by
    rw [sum_normSq_circuitEval_eq_one C]
    norm_num
  have h := AmplitudeStatistics.conditioned_statistics_of_proportional
    (fun s => walkAmplitude A t (out s) start)
    (fun s => circuitEval C s (zeroBasis n)) scale hscale hprop hb s
  simpa [walkProbability] using h

/-- For `x + l ≥ 0`, the selected walk time lies at or below `(x + l) / √2` and less than `π`
below it [Childs2009]. -/
theorem walkTime_bounds {x l : ℝ} (hxl : 0 ≤ x + l) :
    walkTime x l ≤ (x + l) / Real.sqrt 2 ∧
      (x + l) / Real.sqrt 2 < walkTime x l + Real.pi :=
  ⟨Parameters.walkTime_le hxl, Parameters.lt_walkTime_add_pi x l⟩

/-- For `m ≥ 1`, the selected time with `x = m ^ 4` and `l = m` is at most `2 * m ^ 4`
[Childs2009]. -/
theorem walkTime_le_two_pow_four {m : ℕ} (hm : 1 ≤ m) :
    walkTime ((m : ℝ) ^ 4) (m : ℝ) ≤ 2 * (m : ℝ) ^ 4 :=
  Parameters.walkTime_le_two_pow_four hm

/-- The complex phases with frequencies `2` and `-2` agree at the selected walk time
[Childs2009]. -/
theorem bound_state_phases_equal (x l : ℝ) :
    Complex.exp (((2 * walkTime x l : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * walkTime x l) : ℝ) : ℂ) * Complex.I) :=
  Parameters.bound_state_phases_equal x l

end Qatlib.Papers.UniversalWalk08.MainResults.Assembly
