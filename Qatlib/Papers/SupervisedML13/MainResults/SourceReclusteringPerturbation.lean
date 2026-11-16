/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# copy-preserving re-clustering beyond `δ > d^{-2/3}`

Fixed arXiv:1307.0411v2, supplementary material p. 11.

"each distance evaluation is essentially a weak measurement that perturbs
the clustered state `|ψ_ℓ⟩^{⊗d}` at the previous level by an amount
`< d√d δ²` (measured by fidelity), where `δ` is the accuracy of the distance
evaluation.  Accordingly, as long as the desired accuracy is `δ > 1/d^{2/3}`,
`d` copies of the next cluster assignment state can be created from the `d`
copies of the previous cluster assignment state."

The module studies the scalar fidelity budget `1 − d√d δ²`.  It does not
construct quantum states, a weak-measurement channel or next-level copies.
The arithmetic of the printed threshold is also
recorded: with `δ > d^{-2/3}` the loss `d^{3/2} δ²` is *not* small (for
`d = 1`, `δ = 2` it is `4 > 1`).  The repaired sufficient condition below
uses the upper bound `δ < 1/√(d√d)` dictated by the stated fidelity budget.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults
open Qatlib.Papers.SupervisedML13.MainResults

/-- **Fidelity-budget arithmetic.**  If the scalar loss budget `d√d δ²` is
below `1`, the remaining budget `1 − d√d δ²` is positive.

This is the condition the paper's argument needs; it is *not* implied by the
printed threshold `δ > d^{-2/3}` (see `reclustering_condition_counterexample`). -/
theorem nextLevelFidelity_pos_of_loss_lt_one (d δ : ℝ)
    (h : weakMeasurementFidelityLoss d δ < 1) :
    0 < nextLevelFidelity d δ := by
  unfold nextLevelFidelity
  linarith

/-- The printed threshold does not control the fidelity loss: the universally
quantified implication "for all `d, δ > 0`, `δ > d^{-2/3}` implies a positive
`d`-copy fidelity" is false, with the counterexample `d = 1`, `δ = 2`
(threshold `1`, loss `1 · √1 · 2² = 4`, so `nextLevelFidelity 1 2 = -3`).

Source: arXiv:1307.0411v2 p. 11, the paragraph quoted in the module header. -/
theorem reclustering_condition_counterexample :
    ¬ (∀ (d δ : ℝ), 0 < d → 0 < δ → paperAccuracyThreshold d < δ →
        0 < nextLevelFidelity d δ) := by
  intro h
  have hd : (0 : ℝ) < 1 := by norm_num
  have hδ : (0 : ℝ) < 2 := by norm_num
  have hthr : paperAccuracyThreshold 1 < 2 := by
    unfold paperAccuracyThreshold
    norm_num
  have hpos := h 1 2 hd hδ hthr
  unfold nextLevelFidelity weakMeasurementFidelityLoss at hpos
  norm_num [Real.sqrt_one] at hpos

/-- A sufficient accuracy bound for positive remaining fidelity under the stated
loss budget.  The upper bound replaces the false printed lower-bound premise
from arXiv:1307.0411v2, supplementary p. 11; it is a mathematical repair. -/
theorem reclustering_copy_preservation (d : ℕ) (hd : 0 < d) (δ : ℝ)
    (hδ : 0 < δ) (hacc : δ < 1 / Real.sqrt ((d : ℝ) * Real.sqrt (d : ℝ))) :
    0 < nextLevelFidelity (d : ℝ) δ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < (d : ℝ) * Real.sqrt (d : ℝ) :=
    mul_pos hdR (Real.sqrt_pos.mpr hdR)
  have hs : 0 < Real.sqrt ((d : ℝ) * Real.sqrt (d : ℝ)) := Real.sqrt_pos.mpr hA
  have hm : δ * Real.sqrt ((d : ℝ) * Real.sqrt (d : ℝ)) < 1 :=
    (lt_div_iff₀ hs).mp hacc
  have hm0 : 0 < δ * Real.sqrt ((d : ℝ) * Real.sqrt (d : ℝ)) := mul_pos hδ hs
  have hsq : (δ * Real.sqrt ((d : ℝ) * Real.sqrt (d : ℝ))) ^ 2 < 1 :=
    (sq_lt_one_iff₀ hm0.le).mpr hm
  rw [mul_pow, Real.sq_sqrt hA.le] at hsq
  apply nextLevelFidelity_pos_of_loss_lt_one
  simpa [weakMeasurementFidelityLoss, mul_comm] using hsq

/-- The repaired accuracy condition has a positive instance: one copy with
accuracy `1/2` leaves scalar fidelity budget `3/4`. -/
theorem reclustering_accuracy_example :
    (0 : ℝ) < 1 / 2 ∧
      (1 / 2 : ℝ) < 1 / Real.sqrt ((1 : ℝ) * Real.sqrt 1) ∧
      nextLevelFidelity 1 (1 / 2) = 3 / 4 := by
  norm_num [nextLevelFidelity, weakMeasurementFidelityLoss]

end Qatlib.Papers.SupervisedML13.MainResults
