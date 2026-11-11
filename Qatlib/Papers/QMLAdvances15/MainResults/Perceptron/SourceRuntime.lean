/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QMLAdvances15 — Appendix A.2, quantum perceptron total runtime

Fixed source: arXiv:1512.02900v1 [quant-ph] (9 Dec 2015), "Advances in quantum machine
learning", J. C. Adcock et al.

Appendix A.2 ("Quantum Speedup", pp. 32-34) states that the "weights in states"
perceptron trains by solving `A w = ỹ` with HHL (eq. 18). The HHL stage runs in
`O(log N · log(1/ε))` (eq. 19) and the classical conjugate-gradient stage in
`O(N · log(1/ε))` (eq. 20); both classification stages run linearly in the weight
count `W`, giving the total runtimes

* quantum:   `O(W + log N · log(1/ε))`   (eq. 21),
* classical: `O(W + N · log(1/ε))`       (eq. 22).

The claim's content is the comparison of these two cost expressions: with `N ≫ W`
the quantum total is no larger, and when the number of training instances is
exponential in the number of weights (`N = 2^m` with `m = W`) the classical total
exceeds the quantum one by a factor exponential in `W`. We formalise the paper's
own cost accounting (the HHL and classification cost expressions are taken as the
paper's granted subroutine bounds, as in eqs. 19-22); no separate algorithm cost
model is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMLAdvances15.MainResults

/-- Fixed arXiv:1512.02900v1, eq. (21), p. 33: total quantum runtime of the
`W`-weight perceptron, `W + log N · log(1/ε)`, where `N` is the number of training
instances and `ε` the HHL weight-vector error. The `W` term is the linear
classification cost and the logarithmic term is the HHL training stage (eq. 19). -/
def quantumPerceptronCost (W N ε : ℝ) : ℝ :=
  W + Real.log N * Real.log (1 / ε)

/-- Fixed arXiv:1512.02900v1, eq. (22), p. 33: total classical runtime of the
`W`-weight perceptron, `W + N · log(1/ε)`, with the `N · log(1/ε)` conjugate-gradient
training bound of eq. (20) and the linear classification cost `W`. -/
def classicalPerceptronCost (W N ε : ℝ) : ℝ :=
  W + N * Real.log (1 / ε)

/-- Fixed arXiv:1512.02900v1, eq. (21) with `N = 2^m`: the quantum total runtime
depends on the instance count through `log N = m · log 2`, i.e. only on the number
of bits of `N` — the "exponential improvement in N" inherited from HHL stated after
eq. (20) on p. 33. -/
theorem source_hhl_runtime_logarithmic_in_instances (W ε : ℝ) (m : ℕ) :
    quantumPerceptronCost W ((2 : ℝ) ^ m) ε =
      W + (m : ℝ) * Real.log 2 * Real.log (1 / ε) := by
  simp [quantumPerceptronCost, Real.log_pow]

/-- Fixed arXiv:1512.02900v1, eqs. (21)-(22), p. 33: for at least two training
instances and a nonnegative precision factor, the quantum total runtime
`W + log N · log(1/ε)` is at most the classical `W + N · log(1/ε)`, because
`log N ≤ N`. The source's exponential-instance comparison is proved separately. -/
theorem source_quantum_no_worse_than_classical (W N ε : ℝ)
    (hN : 2 ≤ N) (hL : 0 ≤ Real.log (1 / ε)) :
    quantumPerceptronCost W N ε ≤ classicalPerceptronCost W N ε := by
  have hNpos : 0 < N := by linarith
  have hlogN : Real.log N ≤ N := by
    have h := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hL0 : 0 ≤ Real.log (1 / ε) := by linarith
  have hmul : Real.log N * Real.log (1 / ε) ≤ N * Real.log (1 / ε) :=
    mul_le_mul_of_nonneg_right hlogN hL0
  simp only [quantumPerceptronCost, classicalPerceptronCost]
  linarith

/-- Fixed arXiv:1512.02900v1, last paragraph of Appendix A.2, p. 33: "exponentially
more training instances than weights already gives an exponential speedup". With
`m` weights and `N = 2^m` instances, for `m ≥ 1` and `log(1/ε) ≥ 1` the classical
total runtime is at least a factor `2^m/(2m)` (exponential in `m`) times the quantum
total, written without division as `2m · classical ≥ 2^m · quantum`. -/
theorem source_exponential_speedup_with_exponential_instances (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hL : 1 ≤ Real.log (1 / ε)) :
    2 * (m : ℝ) * classicalPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε ≥
      (2 : ℝ) ^ m * quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε := by
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL0 : 0 ≤ Real.log (1 / ε) := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  -- Quantum side: `m + m·log 2·L ≤ 2m·L`.
  have hq : quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
      ≤ 2 * (m : ℝ) * Real.log (1 / ε) := by
    simp only [quantumPerceptronCost, Real.log_pow]
    have hL' : Real.log 2 * Real.log (1 / ε) ≤ Real.log (1 / ε) := by
      calc Real.log 2 * Real.log (1 / ε)
          ≤ 1 * Real.log (1 / ε) := mul_le_mul_of_nonneg_right hlog2 hL0
        _ = Real.log (1 / ε) := one_mul _
    have hmul : (m : ℝ) * (Real.log 2 * Real.log (1 / ε))
        ≤ (m : ℝ) * Real.log (1 / ε) :=
      mul_le_mul_of_nonneg_left hL' hmR
    have hmL : (m : ℝ) ≤ (m : ℝ) * Real.log (1 / ε) := by
      calc (m : ℝ) = (m : ℝ) * 1 := by ring
        _ ≤ (m : ℝ) * Real.log (1 / ε) := mul_le_mul_of_nonneg_left hL hmR
    nlinarith [hmul, hmL]
  -- Classical side: `classical ≥ 2^m·L`.
  have hc : (2 : ℝ) ^ m * Real.log (1 / ε)
      ≤ classicalPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε := by
    simp only [classicalPerceptronCost]
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ m * Real.log (1 / ε) :=
      mul_nonneg (by positivity) hL0
    linarith
  have h2m : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  have h2mpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hstep : (2 : ℝ) ^ m * quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
      ≤ 2 * (m : ℝ) * ((2 : ℝ) ^ m * Real.log (1 / ε)) := by
    calc (2 : ℝ) ^ m * quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
        ≤ (2 : ℝ) ^ m * (2 * (m : ℝ) * Real.log (1 / ε)) :=
          mul_le_mul_of_nonneg_left hq h2mpow.le
      _ = 2 * (m : ℝ) * ((2 : ℝ) ^ m * Real.log (1 / ε)) := by ring
  have hfinal := mul_le_mul_of_nonneg_left hc h2m
  linarith

/-- For `0 < ε < 1`, the logarithmic precision factor `log(1/ε)` is positive. -/
theorem log_inv_pos_of_pos_of_lt_one {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < Real.log (1 / ε) := by
  apply Real.log_pos
  exact (lt_div_iff₀ hε0).2 (by simpa using hε1)

/-- Eq. (21) is bounded by eq. (22) for every `N ≥ 2` and every `0 < ε < 1`;
no restriction `log(1/ε) ≥ 1` is needed for this comparison. -/
theorem source_quantum_no_worse_of_pos_error (W N ε : ℝ)
    (hN : 2 ≤ N) (hε0 : 0 < ε) (hε1 : ε < 1) :
    quantumPerceptronCost W N ε ≤ classicalPerceptronCost W N ε := by
  exact source_quantum_no_worse_than_classical W N ε hN
    (log_inv_pos_of_pos_of_lt_one hε0 hε1).le

/-- General positive-error form of the exponential-instance comparison on p. 33.
For `m ≥ 1` weights, `N = 2^m` instances and `L = log(1/ε) > 0`, the classical
runtime is at least `2^m L / (2m(1+L)²)` times the quantum runtime. The factor is
exponential in `m` up to a positive constant determined by the fixed error `ε`.
The statement avoids division by the quantum runtime. -/
theorem source_exponential_speedup_of_pos_log (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hL : 0 < Real.log (1 / ε)) :
    (2 : ℝ) ^ m * Real.log (1 / ε) * quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
      ≤ 2 * (m : ℝ) * (1 + Real.log (1 / ε)) ^ 2 *
        classicalPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε := by
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hscale_one : 1 ≤ (1 + Real.log (1 / ε)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (1 / ε))]
  have hscale_log : Real.log (1 / ε) ≤ (1 + Real.log (1 / ε)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (1 / ε))]
  have hlogscale : Real.log 2 * Real.log (1 / ε) ≤ (1 + Real.log (1 / ε)) ^ 2 := by
    calc
      Real.log 2 * Real.log (1 / ε) ≤ 1 * Real.log (1 / ε) :=
        mul_le_mul_of_nonneg_right hlog2 hL.le
      _ = Real.log (1 / ε) := one_mul _
      _ ≤ (1 + Real.log (1 / ε)) ^ 2 := hscale_log
  have hq : quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
      ≤ 2 * (m : ℝ) * (1 + Real.log (1 / ε)) ^ 2 := by
    simp only [quantumPerceptronCost, Real.log_pow]
    have hlogmul := mul_le_mul_of_nonneg_left hlogscale hmR
    have honemul := mul_le_mul_of_nonneg_left hscale_one hmR
    nlinarith [hlogmul, honemul]
  have hc : (2 : ℝ) ^ m * Real.log (1 / ε)
      ≤ classicalPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε := by
    simp only [classicalPerceptronCost]
    have hterm0 : 0 ≤ (2 : ℝ) ^ m * Real.log (1 / ε) :=
      mul_nonneg (by positivity) hL.le
    linarith
  calc
    (2 : ℝ) ^ m * Real.log (1 / ε) * quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
      ≤ (2 : ℝ) ^ m * Real.log (1 / ε) *
          (2 * (m : ℝ) * (1 + Real.log (1 / ε)) ^ 2) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg (by positivity) hL.le)
    _ ≤ 2 * (m : ℝ) * (1 + Real.log (1 / ε)) ^ 2 *
          classicalPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε := by
        have hfinal := mul_le_mul_of_nonneg_left hc
          (show 0 ≤ 2 * (m : ℝ) * (1 + Real.log (1 / ε)) ^ 2 by positivity)
        nlinarith [hfinal]

/-- The positive-error exponential comparison specialized to `0 < ε < 1`. -/
theorem source_exponential_speedup_of_pos_error (m : ℕ) (hm : 1 ≤ m)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (2 : ℝ) ^ m * Real.log (1 / ε) * quantumPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε
      ≤ 2 * (m : ℝ) * (1 + Real.log (1 / ε)) ^ 2 *
        classicalPerceptronCost (m : ℝ) ((2 : ℝ) ^ m) ε := by
  exact source_exponential_speedup_of_pos_log m hm ε
    (log_inv_pos_of_pos_of_lt_one hε0 hε1)

end Qatlib.Papers.QMLAdvances15.MainResults
