/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option backward.isDefEq.respectTransparency false

/-! Metric distributions for
"The Quantum Decoding Problem: Tight Achievability Bounds and
Application to Regev's Reduction" (arXiv:2509.24796v2, 2025).

Lemma 14 of the paper: for every metric `r(α) = q^{-λ|α|}` on the
graded set there is a unique `λ > 0` turning it into a probability
distribution, i.e. `Σ_α q^{-λ|α|} = 1`.

The paper's existence argument is the intermediate value theorem on
`F(λ) = Σ_α q^{-λ|α|}`: `F` is continuous and strictly decreasing,
`F(0) = |A| > 1`, and `F(λ) → 0` as `λ → ∞`.

The paper is ambiguous about zero weights (a weight-`0` point keeps
`F ≥ 1` forever, so no `λ` normalises the family); here the statement
is faithful to the proof under strictly positive weights `w a > 0`
and at least two points, which is the regime the decoding metrics of
the paper live in. `exists_unique_metric_distribution` is **Lemma 14**
in that reading: both existence (IVT between `0` and a large `lam0`,
using the minimum weight) and uniqueness (strict monotonicity of
`q^{-λ w}` term by term) are proved in full.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.QDecoding25.MainResults.MetricDistribution

/-- **Lemma 14**: for a finite set `A` with at least two points, an
integer `q ≥ 2` and strictly positive weights `w : A → ℝ`, there is a
unique `lam > 0` such that `Σ_a q ^ (-lam * w a) = 1`; the normalising
parameter of the metric distribution `r(a) = q ^ (-lam * w a)`. -/
theorem exists_unique_metric_distribution {A : Type} [Fintype A] (q : ℕ) (hq : 2 ≤ q)
    (w : A → ℝ) (hw : ∀ a, 0 < w a) (hcard : 2 ≤ Fintype.card A) :
    ∃! lam : ℝ, 0 < lam ∧ ∑ a, (q : ℝ) ^ (-(lam) * w a) = 1 := by
  classical
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hqnn : 0 ≤ (q : ℝ) := by positivity
  have hcardpos : (1 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hcard
  -- the minimum weight m is positive and bounds every w a from below
  have hcardA : 0 < Fintype.card A := by omega
  haveI : Nonempty A := Fintype.card_pos_iff.mp hcardA
  have hne : (Finset.univ.image w).Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  set m := (Finset.univ.image w).min' hne with hmdef
  have hmle : ∀ a, m ≤ w a := fun a =>
    Finset.min'_le (Finset.univ.image w) (w a)
      (Finset.mem_image_of_mem w (Finset.mem_univ a))
  have hm0 : 0 < m := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image w) hne)
    rw [hmdef, ← ha]; exact hw a
  -- the weight-sum is continuous and strictly decreasing in lam
  have hcont : Continuous (fun lam : ℝ => ∑ a, (q : ℝ) ^ (-lam * w a)) := by
    exact continuous_finsetSum Finset.univ fun a _ =>
      Continuous.rpow continuous_const (by continuity) (fun _ => Or.inl hq0)
  have hstrict : ∀ lam1 lam2 : ℝ, lam1 < lam2 →
      ∑ a, (q : ℝ) ^ (-lam2 * w a) < ∑ a, (q : ℝ) ^ (-lam1 * w a) := by
    intro lam1 lam2 hlam
    have hterm : ∀ a, (q : ℝ) ^ (-lam2 * w a) < (q : ℝ) ^ (-lam1 * w a) := by
      intro a
      refine (Real.rpow_lt_rpow_left_iff hq1).mpr ?_
      have hwlam : lam1 * w a < lam2 * w a := mul_lt_mul_of_pos_right hlam (hw a)
      rw [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul]
      exact neg_lt_neg hwlam
    exact Finset.sum_lt_sum (fun a _ => le_of_lt (hterm a))
      ⟨Classical.arbitrary A, Finset.mem_univ _, hterm _⟩
  -- at lam = 0 the sum is the cardinality, which exceeds 1
  have hF0 : ∑ a, (q : ℝ) ^ (-(0 : ℝ) * w a) = (Fintype.card A : ℝ) := by
    simp [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, neg_zero, zero_mul]
  have hF0gt : (1 : ℝ) < ∑ a, (q : ℝ) ^ (-(0 : ℝ) * w a) := by
    rw [hF0]; exact hcardpos
  -- at lam0 = card A / m the sum drops below 1
  have hNpos : 0 < Fintype.card A := by omega
  have hlam0pos : (0 : ℝ) < (Fintype.card A : ℝ) / m :=
    div_pos (by exact_mod_cast hNpos) hm0
  have hmul : ((Fintype.card A : ℝ) / m) * m = (Fintype.card A : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt hm0)
  have hterm : ∀ a, (q : ℝ) ^ (-((Fintype.card A : ℝ) / m) * w a)
      ≤ (q : ℝ) ^ (-((Fintype.card A : ℝ) / m) * m) := by
    intro a
    refine (Real.rpow_le_rpow_left_iff hq1).mpr ?_
    rw [← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hmle a) (le_of_lt hlam0pos))
  have hexp : -((Fintype.card A : ℝ) / m) * m = -((Fintype.card A : ℝ)) := by
    rw [← neg_mul_eq_neg_mul, hmul]
  have hqm : (q : ℝ) ^ (-((Fintype.card A : ℝ) / m) * m)
      = ((q ^ (Fintype.card A) : ℕ) : ℝ)⁻¹ := by
    rw [hexp, Real.rpow_neg hqnn, Real.rpow_natCast, ← Nat.cast_pow]
  have hqN : Fintype.card A < q ^ (Fintype.card A) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq _)
  have hqp : (0 : ℝ) < ((q ^ (Fintype.card A) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_pos (by omega)
  have hFlam0 : ∑ a, (q : ℝ) ^ (-((Fintype.card A : ℝ) / m) * w a) < 1 := by
    have hsumle : ∑ a, (q : ℝ) ^ (-((Fintype.card A : ℝ) / m) * w a)
        ≤ ∑ a ∈ Finset.univ, ((q ^ (Fintype.card A) : ℕ) : ℝ)⁻¹ :=
      Finset.sum_le_sum fun a _ => (hterm a).trans (le_of_eq hqm)
    rw [Finset.sum_const, nsmul_eq_mul] at hsumle
    calc ∑ a, (q : ℝ) ^ (-((Fintype.card A : ℝ) / m) * w a)
        ≤ (Fintype.card A : ℝ) * ((q ^ (Fintype.card A) : ℕ) : ℝ)⁻¹ := hsumle
      _ < ((q ^ (Fintype.card A) : ℕ) : ℝ) * ((q ^ (Fintype.card A) : ℕ) : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_right (by exact_mod_cast hqN) (inv_pos.mpr hqp)
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hqp)
  -- intermediate value theorem between 0 and lam0
  obtain ⟨x, hxmem, hFx⟩ :=
    (show IsPreconnected (Set.Icc (0 : ℝ) ((Fintype.card A : ℝ) / m)) from
      isPreconnected_Icc).intermediate_value₂
      (Set.mem_Icc.2 ⟨le_refl 0, le_of_lt hlam0pos⟩)
      (Set.mem_Icc.2 ⟨le_of_lt hlam0pos, le_refl ((Fintype.card A : ℝ) / m)⟩)
      (continuousOn_const) (hcont.continuousOn)
      (le_of_lt hF0gt) (le_of_lt hFlam0)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, hF0] at hFx
    exact absurd hFx.symm (ne_of_gt hcardpos)
  refine ⟨x, ⟨lt_of_le_of_ne (Set.mem_Icc.1 hxmem).1 (Ne.symm hx0), hFx.symm⟩, fun y hy => ?_⟩
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with h | h
  · have hlt := hstrict y x h
    rw [← hFx, hy.2] at hlt
    exact absurd hlt (lt_irrefl 1)
  · have hlt := hstrict x y h
    rw [← hFx, hy.2] at hlt
    exact absurd hlt (lt_irrefl 1)

end Qatlib.Papers.QDecoding25.MainResults.MetricDistribution
