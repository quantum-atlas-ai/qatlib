/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Qatlib.Papers.ShortPathOpt18.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# ShortPathOpt18 — Lemma 3 (Jensen inequality for products)

Hastings, fixed arXiv:1802.10124, Lemma 3, p. 10.

The paper proves, for positive random variables `x₁,…,x_k` that need not be
independent,
`E[∏ᵢ xᵢ⁻¹] ≥ ∏ᵢ (E[xᵢ])⁻¹`, using convexity of `exp` and concavity of `log`.

The Lean statement below is the finite probability-space version: `w` is a
probability mass function on a finite outcome type `Ω`, and `x ω i` is the
value of the `i`-th positive random variable at outcome `ω`.  The proof
follows the paper's two convexity steps literally.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShortPathOpt18.MainResults

/-- Source Lemma 3, p. 10: for positive random variables `x₁,…,x_k` (not
necessarily independent), `E[∏ᵢ xᵢ⁻¹] ≥ ∏ᵢ (E[xᵢ])⁻¹`.  Finite
probability-space form with weights `w`. -/
theorem source_lemma3 {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    {k : ℕ} (x : Ω → Fin k → ℝ) (hx : ∀ (ω : Ω) (i : Fin k), 0 < x ω i) :
    ∑ ω, w ω * ∏ i, (x ω i)⁻¹ ≥ ∏ i, (∑ ω, w ω * x ω i)⁻¹ := by
  classical
  -- the log-weight of an outcome
  set y : Ω → ℝ := fun ω => ∑ i, Real.log (x ω i) with hy
  -- positivity of each weighted mean
  have hposmean : ∀ i : Fin k, 0 < ∑ ω, w ω * x ω i := by
    intro i
    have hex : ∃ ω, 0 < w ω := by
      by_contra h
      push_neg at h
      have hzero : ∀ ω, w ω = 0 := fun ω => le_antisymm (h ω) (hw0 ω)
      have hsum0 : (∑ ω, w ω) = 0 := by simp [hzero]
      linarith
    obtain ⟨ω0, hω0⟩ := hex
    exact Finset.sum_pos'
      (fun ω _ => mul_nonneg (hw0 ω) (le_of_lt (hx ω i)))
      ⟨ω0, Finset.mem_univ _, mul_pos hω0 (hx ω0 i)⟩
  -- Jensen for the convex exponential
  have hjensen : Real.exp (∑ ω, w ω * (-y ω)) ≤ ∑ ω, w ω * Real.exp (-y ω) := by
    have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset Ω)) (w := w)
      (p := fun ω => -y ω) (fun ω _ => hw0 ω) (by simpa using hw1)
      (fun ω _ => Set.mem_univ _)
    simpa [smul_eq_mul] using h
  -- concavity of `log` for each coordinate
  have hlog : ∀ i : Fin k,
      ∑ ω, w ω * Real.log (x ω i) ≤ Real.log (∑ ω, w ω * x ω i) := by
    intro i
    have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum
      (t := (Finset.univ : Finset Ω)) (w := w) (p := fun ω => x ω i)
      (fun ω _ => hw0 ω) (by simpa using hw1)
      (fun ω _ => (Set.mem_Ioi).mpr (hx ω i))
    simpa [smul_eq_mul] using h
  -- rewriting the product of reciprocals as an exponential
  have hprod : ∀ ω, ∏ i, (x ω i)⁻¹ = Real.exp (-y ω) := by
    intro ω
    calc ∏ i, (x ω i)⁻¹ = ∏ i, Real.exp (-Real.log (x ω i)) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [Real.exp_neg, Real.exp_log (hx ω i)]
      _ = Real.exp (∑ i, -Real.log (x ω i)) := (Real.exp_sum _ _).symm
      _ = Real.exp (-y ω) := by rw [hy, Finset.sum_neg_distrib]
  -- the exponential lower bound
  have hexp_arg : Real.exp (∑ ω, w ω * (-y ω)) ≥
      ∏ i, (∑ ω, w ω * x ω i)⁻¹ := by
    have harg : ∑ ω, w ω * (-y ω) = -∑ i, ∑ ω, w ω * Real.log (x ω i) := by
      rw [hy]
      simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [harg]
    rw [show Real.exp (-∑ i, ∑ ω, w ω * Real.log (x ω i)) =
        ∏ i, Real.exp (-(∑ ω, w ω * Real.log (x ω i))) by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]]
    apply Finset.prod_le_prod₀
    · intro i _
      exact inv_nonneg.mpr (le_of_lt (hposmean i))
    · intro i _
      have hi := hlog i
      have hpos := hposmean i
      calc (∑ ω, w ω * x ω i)⁻¹
          = Real.exp (-(Real.log (∑ ω, w ω * x ω i))) := by
              rw [Real.exp_neg, Real.exp_log hpos]
        _ ≤ Real.exp (-(∑ ω, w ω * Real.log (x ω i))) := by
              apply Real.exp_le_exp.mpr
              linarith
  calc ∑ ω, w ω * ∏ i, (x ω i)⁻¹
      = ∑ ω, w ω * Real.exp (-y ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [hprod ω]
    _ ≥ Real.exp (∑ ω, w ω * (-y ω)) := hjensen
    _ ≥ ∏ i, (∑ ω, w ω * x ω i)⁻¹ := hexp_arg

end Qatlib.Papers.ShortPathOpt18.MainResults
