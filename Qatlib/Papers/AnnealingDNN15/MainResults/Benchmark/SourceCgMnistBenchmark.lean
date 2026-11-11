/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# CG-MNIST training comparison (c001)

Source: *Application of Quantum Annealing to Training of Deep Neural Networks*,
arXiv:1510.06356 (2015), fixed local PDF
`1510.06356.pdf` (SHA-256 `7c273ebf6340223d2ddbc2f0684298e9a16ed3cc89253d212008ae3e3e945f72`).
Abstract (p. 1) and Section 4 "Experimental Results", pp. 13–16 (Figures 7–10),
Conclusions p. 17.

The paper reports: on the coarse-grained MNIST data set, the quantum
sampling-based generative training "achieves comparable or better accuracy with
significantly fewer iterations of generative training than conventional CD-based
training", and more concretely (Sec. 4, p. 16): "quantum networks trained with
only 20 pre-training and 100 backprop iterations were more accurate than
classical networks trained for 50 pre-training and 800 backprop iterations".

This is an *empirical* comparison.  The figures do not publish scalar accuracy
values, only curves.  The Lean statement below therefore models one reported
comparison as a pair of training runs with the paper's iteration counts, and
keeps the measured accuracy ordering as an explicit hypothesis `hAcc`.  What is
proved is the paper's asserted comparison of iteration budgets and accuracy for
that report; the measurement itself is the paper's experimental input, not a
derived fact.  No `sorry`, no extra axiom.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AnnealingDNN15.MainResults.Benchmark

/-- One training configuration of the CG-MNIST study: the number of generative
(pre-training) iterations, the number of discriminative (backpropagation)
iterations, and the resulting test-set accuracy. -/
structure TrainingRun where
  pretrainIters : ℕ
  backpropIters : ℕ
  testAccuracy : ℝ

/-- **c001 — comparable accuracy with fewer generative-training iterations.**

There exist a quantum sampling-based run and a classical CD run with the
paper's reported iteration counts (20 pre-training / 100 backprop versus
50 pre-training / 800 backprop) such that the classical accuracy is at most the
quantum accuracy and the quantum run uses strictly fewer generative and
discriminative iterations.

`hAcc` is the paper's measured accuracy ordering (Section 4, p. 16: the
quantum runs "were more accurate than" the classical runs); it is the empirical
input of the claim. -/
theorem c001_comparable_accuracy_fewer_iterations
    (quantumAccuracy classicalAccuracy : ℝ)
    (hAcc : classicalAccuracy ≤ quantumAccuracy) :
    ∃ q c : TrainingRun,
      q.pretrainIters = 20 ∧ q.backpropIters = 100 ∧
      c.pretrainIters = 50 ∧ c.backpropIters = 800 ∧
      q.pretrainIters < c.pretrainIters ∧ q.backpropIters < c.backpropIters ∧
      c.testAccuracy ≤ q.testAccuracy := by
  exact ⟨⟨20, 100, quantumAccuracy⟩, ⟨50, 800, classicalAccuracy⟩,
    rfl, rfl, rfl, rfl, by norm_num, by norm_num, hAcc⟩

/-- The concrete iteration counts of the reported comparison: the quantum run
uses `2 * 20 ≤ 50` generative and `2 * 100 ≤ 800` discriminative iterations,
i.e. less than half of the classical budget in both phases ("significantly
fewer iterations"). -/
theorem c001_iteration_budget_savings :
    2 * (20 : ℕ) ≤ 50 ∧ 2 * (100 : ℕ) ≤ 800 := by
  norm_num

/-- **c001, general form.**  For any reported pair of runs in which the quantum
run uses strictly fewer generative iterations, no more discriminative
iterations, and achieves at least the classical accuracy, the paper's
conclusion holds.  This packages the comparison independently of the particular
20/100 vs 50/800 numbers. -/
theorem c001_of_reported_run (q c : TrainingRun)
    (hgen : q.pretrainIters < c.pretrainIters)
    (hdis : q.backpropIters ≤ c.backpropIters)
    (hacc : c.testAccuracy ≤ q.testAccuracy) :
    q.pretrainIters < c.pretrainIters ∧
      q.backpropIters ≤ c.backpropIters ∧
      c.testAccuracy ≤ q.testAccuracy :=
  ⟨hgen, hdis, hacc⟩

end Qatlib.Papers.AnnealingDNN15.MainResults.Benchmark
