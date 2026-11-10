/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteCounts.OffsetWord.UniformRun

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {I A : Type*} [Fintype I]

noncomputable def jointLaw (p : PMF I) (q : PMF A) : PMF (I × A) :=
  p.bind (fun i => q.map (fun a => (i,a)))

theorem joint_error_le (p : PMF I) (q : PMF A) (E : Set (I × A)) (C : ℝ)
    (hC : ∀ i, (q.toOuterMeasure {a | (i,a) ∈ E}).toReal ≤ C) :
    ((jointLaw p q).toOuterMeasure E).toReal ≤ C := by
  have hfin : ∀ i, p i * (q.map (fun a => (i,a))).toOuterMeasure E ≠ ⊤ := by
    intro i
    apply ENNReal.mul_ne_top (p.apply_ne_top i)
    rw [PMF.toOuterMeasure_map_apply, q.toOuterMeasure_apply]
    exact q.tsum_coe_indicator_ne_top _
  rw [jointLaw, PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq hfin]
  simp only [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply, tsum_fintype]
  have hs : ∑ i, (p i).toReal = 1 := by
    calc
      _ = ∑' i : I, (p i).toReal := (tsum_fintype _).symm
      _ = (∑' i : I, p i).toReal := (ENNReal.tsum_toReal_eq (fun i => p.apply_ne_top i)).symm
      _ = 1 := by rw [p.tsum_coe]; rfl
  calc
    _ ≤ ∑ i, (p i).toReal * C := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hC i) ENNReal.toReal_nonneg
    _ = C := by rw [← Finset.sum_mul, hs, one_mul]

variable [Fintype A]

omit [Fintype I] in

theorem joint_event_reverse (p : PMF I) (q : PMF A) (E : Set (I × A)) :
    ((jointLaw p q).toOuterMeasure E).toReal =
      ∑ a, (q a).toReal * (p.toOuterMeasure {i | (i,a) ∈ E}).toReal := by
  have he : jointLaw p q = q.bind (fun a => p.map (fun i => (i,a))) :=
    PMF.bind_comm p q (fun i a => PMF.pure (i,a))
  have hfin : ∀ a, q a * (p.map (fun i => (i,a))).toOuterMeasure E ≠ ⊤ := by
    intro a
    apply ENNReal.mul_ne_top (q.apply_ne_top a)
    rw [PMF.toOuterMeasure_map_apply, p.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top _
  rw [he, PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq hfin]
  simp only [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply, tsum_fintype]
  rfl

end Qatlib.Concepts.FiniteCounts.OffsetWord
