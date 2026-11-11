/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Squared overlap and the ratio of averages

Source: Wecker, Hastings, Troyer, *Training A Quantum Optimizer*,
fixed arXiv:1605.05370v1.

* Sec. III, p. 4: the figure of merit is the squared overlap
  `|⟨ΨF|Ψ0⟩|^2` of the prepared state `ΨF` with the true ground state `Ψ0`;
  the learned schedule is compared with the best per-instance anneal through
  "the ratio of the squared overlap of the learned schedule to that of the
  per-instance optimized anneal".
* Sec. III, p. 4 and Tables II–IV, p. 5–6: the published number is a **ratio of
  averages**, i.e. `(Σ_i overlap_learned(i)) / (Σ_i overlap_anneal(i))` over a
  finite test set, not an average of pointwise ratios.

This module records those two finite quantities and the elementary bridge:
if every instance's anneal overlap is smaller than the learned overlap, the
ratio of averages exceeds one (`ratioOfAverages_gt_one_of_pointwise`). The
paper's reported table values are stated in the sibling `SourceClaims`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrainQOptim16.MainResults.Ratio

open scoped BigOperators

/-- The Hilbert-space inner product `⟨ψ|φ⟩ = Σ_i conj(ψ i) * φ i` on the
finite computational basis of `N` qubits. -/
def innerOverlap {N : ℕ} (ψ φ : Fin N → ℂ) : ℂ :=
  ∑ i, starRingEnd ℂ (ψ i) * φ i

/-- The squared overlap `|⟨ΨF|Ψ0⟩|^2`, the figure of merit of Sec. III. -/
def squaredOverlap {N : ℕ} (ψ φ : Fin N → ℂ) : ℝ :=
  ‖innerOverlap ψ φ‖ ^ 2

/-- A squared overlap is nonnegative. -/
theorem squaredOverlap_nonneg {N : ℕ} (ψ φ : Fin N → ℂ) :
    0 ≤ squaredOverlap ψ φ := sq_nonneg _

/-- The paper's "ratio of averages": the sum of the learned-schedule overlaps
divided by the sum of the reference anneal overlaps over a finite test set. -/
def ratioOfAverages {ι : Type*} (learned anneal : ι → ℝ) (s : Finset ι) : ℝ :=
  (∑ i ∈ s, learned i) / (∑ i ∈ s, anneal i)

/-- The ratio of averages is at least `c` as soon as every per-instance
learned overlap dominates `c` times the reference overlap (the elementary
bridge from pointwise improvement to the reported table quantity). -/
theorem ratioOfAverages_ge_of_pointwise {ι : Type*} (s : Finset ι)
    (learned anneal : ι → ℝ) (c : ℝ) (hs : s.Nonempty)
    (hpos : ∀ i ∈ s, 0 < anneal i)
    (h : ∀ i ∈ s, c * anneal i ≤ learned i) :
    c ≤ ratioOfAverages learned anneal s := by
  have hsum : 0 < ∑ i ∈ s, anneal i := Finset.sum_pos hpos hs
  unfold ratioOfAverages
  rw [le_div_iff₀ hsum]
  calc
    c * ∑ i ∈ s, anneal i = ∑ i ∈ s, c * anneal i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, learned i := Finset.sum_le_sum h

/-- If every instance's learned overlap strictly exceeds its reference
overlap, then the paper's ratio of averages is strictly larger than one. -/
theorem ratioOfAverages_gt_one_of_pointwise {ι : Type*} (s : Finset ι)
    (learned anneal : ι → ℝ) (hs : s.Nonempty)
    (hpos : ∀ i ∈ s, 0 < anneal i)
    (h : ∀ i ∈ s, anneal i < learned i) :
    1 < ratioOfAverages learned anneal s := by
  have hsum : 0 < ∑ i ∈ s, anneal i := Finset.sum_pos hpos hs
  have hlt : (∑ i ∈ s, anneal i) < ∑ i ∈ s, learned i :=
    Finset.sum_lt_sum (fun i hi => le_of_lt (h i hi))
      (let ⟨i, hi⟩ := hs
       ⟨i, hi, h i hi⟩)
  unfold ratioOfAverages
  rw [lt_div_iff₀ hsum]
  simpa using hlt

end Qatlib.Papers.TrainQOptim16.MainResults.Ratio
