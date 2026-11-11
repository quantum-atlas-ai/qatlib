/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Modified Marriott–Watrous gap amplification: Theorem 9

Harrow--Lin--Montanaro, *Sequential measurements, disturbance and property
testing*, fixed arXiv:1607.03236v3 (21 Oct 2016).  Theorem 9, Section 2, page 9
(proof on pages 9--10).

Theorem 9.  Let `pacc(N)` be the acceptance probability of Algorithm 1 applied
to a measurement operator `Λ` and a state `ρ`, and let `P_{≥δ}` project onto the
span of eigenvectors of `Λ` with eigenvalue at least `δ`.  Then

  `(1 - e⁻¹) tr P_{≥1/(2N)} ρ ≤ pacc(N) ≤ 2N tr Λρ`.

The proof decomposes a pure input `ρ = |ψ⟩⟨ψ|` in an eigenbasis
`|ψ⟩ = Σ_i α_i |ψ_i⟩`, `Λ|ψ_i⟩ = λ_i |ψ_i⟩`, and computes

  `pacc(N) = 1 - Σ_i |α_i|² (1 - λ_i)^{2N}`.

The lower bound uses `(1-a)^{1/a} < e⁻¹` (equivalently
`(1-a)^{2N} ≤ e^{-2N a} ≤ e⁻¹` for `a ≥ 1/(2N)`), the upper bound uses the
Bernoulli inequality `1 - (1-λ)^{2N} ≤ 2N λ`.  Convexity extends the pure-state
computation to mixed `ρ`; the formal statement below is the pure-state
eigenbasis content, with `w i = |α_i|²`.  The mixed case follows by writing a
density matrix as a convex combination of its eigenvectors (documented, not
re-proved here because it only uses linearity of trace and probability).

This file contains a complete tactic proof of both inequalities.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.SeqMeasure16.MainResults.ModifiedMW

/-- Acceptance probability of Algorithm 1 on a pure input, written in the
eigenbasis of `Λ`: `pacc(N) = 1 - Σ_i w_i (1-λ_i)^{2N}`, where
`w_i = |α_i|²` is the squared overlap with the `i`-th eigenvector and `λ_i`
the corresponding eigenvalue (arXiv:1607.03236v3, page 9). -/
def mwAcceptanceProb {ι : Type*} [Fintype ι] (w lam : ι → ℝ) (N : ℕ) : ℝ :=
  1 - ∑ i, w i * (1 - lam i) ^ (2 * N)

/-- Elementary exponential bound used in the lower half of Theorem 9:
for `0 ≤ a ≤ 1` and any `m`, `(1-a)^m ≤ e^{-m a}`. -/
theorem one_sub_pow_le_exp_neg {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (m : ℕ) :
    (1 - a) ^ m ≤ Real.exp (-(m * a)) := by
  have hbase : 1 - a ≤ Real.exp (-a) := Real.one_sub_le_exp_neg a
  have hnonneg : 0 ≤ 1 - a := by linarith
  calc
    (1 - a) ^ m ≤ (Real.exp (-a)) ^ m := pow_le_pow_left₀ hnonneg hbase m
    _ = Real.exp (m * (-a)) := (Real.exp_nat_mul (-a) m).symm
    _ = Real.exp (-(m * a)) := by rw [show m * (-a) = -(m * a) by ring]

/-- Rewriting step: if the weights sum to one then the acceptance probability
`1 - Σ w_i x_i` equals `Σ w_i (1 - x_i)`. -/
theorem one_sub_sum_eq_sum_one_sub {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∑ i, w i = 1) :
    1 - ∑ i, w i * x i = ∑ i, w i * (1 - x i) := by
  calc
    1 - ∑ i, w i * x i = (∑ i, w i) - ∑ i, w i * x i := by rw [hw]
    _ = ∑ i, (w i - w i * x i) := (Finset.sum_sub_distrib w (fun i => w i * x i)).symm
    _ = ∑ i, w i * (1 - x i) := Finset.sum_congr rfl (fun i _ => by ring)

/-- **Theorem 9, lower bound** (arXiv:1607.03236v3, page 9): for a pure state
with eigenbasis weights `w` and eigenvalues `lam ∈ [0,1]`, the acceptance
probability of Algorithm 1 for `N ≥ 1` is at least `(1-e⁻¹)` times the mass of
the eigenvectors with eigenvalue `≥ 1/(2N)`. -/
theorem source_modified_mw_lower {ι : Type*} [Fintype ι]
    (w lam : ι → ℝ) (N : ℕ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1) (hN : 0 < N) :
    (1 - Real.exp (-1)) *
        ∑ i ∈ Finset.univ.filter (fun i => (1 : ℝ) / (2 * N) ≤ lam i), w i ≤
      mwAcceptanceProb w lam N := by
  rw [mwAcceptanceProb, one_sub_sum_eq_sum_one_sub w (fun i => (1 - lam i) ^ (2 * N)) hw1]
  let S := Finset.univ.filter (fun i => (1 : ℝ) / (2 * N) ≤ lam i)
  have hNpos : (0 : ℝ) < 2 * N := by positivity
  -- On the filtered set each term is at least `(1-e⁻¹) w_i`.
  have hS : ∑ i ∈ S, w i * (1 - Real.exp (-1)) ≤
      ∑ i ∈ S, w i * (1 - (1 - lam i) ^ (2 * N)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left ?_ (hw0 i)
    have hf : (1 : ℝ) / (2 * N) ≤ lam i := (Finset.mem_filter.mp hi).2
    have hexp : (1 - lam i) ^ (2 * N) ≤ Real.exp (-1) := by
      calc
        (1 - lam i) ^ (2 * N) ≤ Real.exp (-(((2 * N : ℕ) : ℝ) * lam i)) :=
          one_sub_pow_le_exp_neg (hlam0 i) (hlam1 i) (2 * N)
        _ ≤ Real.exp (-1) := by
          apply Real.exp_le_exp.mpr
          have h1 : (1 : ℝ) ≤ ((2 * N : ℕ) : ℝ) * lam i := by
            have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
            rw [hcast]
            have hone : 2 * (N : ℝ) * (1 / (2 * N)) = 1 := by
              field_simp
            have hm := mul_le_mul_of_nonneg_left hf hNpos.le
            linarith
          linarith
    linarith
  -- Extend the sum from `S` to all indices, the extra terms being nonnegative.
  have hmono : ∑ i ∈ S, w i * (1 - (1 - lam i) ^ (2 * N)) ≤
      ∑ i, w i * (1 - (1 - lam i) ^ (2 * N)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _
    apply mul_nonneg (hw0 i)
    have hb : (1 - lam i) ^ (2 * N) ≤ 1 :=
      pow_le_one₀ (by linarith [hlam1 i]) (by linarith [hlam0 i])
    linarith
  have hEq : (1 - Real.exp (-1)) * ∑ i ∈ S, w i =
      ∑ i ∈ S, w i * (1 - Real.exp (-1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hEq]
  exact hS.trans hmono

/-- **Theorem 9, upper bound** (arXiv:1607.03236v3, page 9): the acceptance
probability of Algorithm 1 for `N` rounds is at most `2N tr Λρ`; in the
eigenbasis this is `2N Σ_i w_i λ_i`. -/
theorem source_modified_mw_upper {ι : Type*} [Fintype ι]
    (w lam : ι → ℝ) (N : ℕ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1) :
    mwAcceptanceProb w lam N ≤ 2 * N * ∑ i, w i * lam i := by
  rw [mwAcceptanceProb, one_sub_sum_eq_sum_one_sub w (fun i => (1 - lam i) ^ (2 * N)) hw1]
  calc
    ∑ i, w i * (1 - (1 - lam i) ^ (2 * N))
        ≤ ∑ i, w i * (2 * (N : ℝ) * lam i) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left ?_ (hw0 i)
          have hbern : 1 + (2 * N : ℕ) * (-lam i) ≤ (1 + (-lam i)) ^ (2 * N) :=
            one_add_mul_le_pow (by linarith [hlam1 i]) (2 * N)
          have hlin : (1 : ℝ) - 2 * N * lam i ≤ (1 - lam i) ^ (2 * N) := by
            have hcast : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
            rw [hcast] at hbern
            simpa only [mul_neg, sub_eq_add_neg] using hbern
          linarith
    _ = 2 * N * ∑ i, w i * lam i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- **Theorem 9** (arXiv:1607.03236v3, page 9), pure-state eigenbasis form:
for a normalized pure state decomposed in an eigenbasis of the measurement
operator `Λ` with eigenvalues `0 ≤ λ_i ≤ 1` and weights `w_i = |α_i|² ≥ 0`
summing to one, and for any `N ≥ 1`,

`(1-e⁻¹) tr P_{≥1/(2N)} ρ ≤ pacc(N) ≤ 2N tr Λρ`.

Both inequalities are proved in `source_modified_mw_lower` and
`source_modified_mw_upper`; the mixed-state extension is by convexity
(arXiv:1607.03236v3, page 10: "Finally, if ρ is mixed, the claim follows from
convexity"). -/
theorem source_modified_mw_bounds {ι : Type*} [Fintype ι]
    (w lam : ι → ℝ) (N : ℕ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∀ i, lam i ≤ 1) (hN : 0 < N) :
    (1 - Real.exp (-1)) *
        ∑ i ∈ Finset.univ.filter (fun i => (1 : ℝ) / (2 * N) ≤ lam i), w i ≤
        mwAcceptanceProb w lam N ∧
      mwAcceptanceProb w lam N ≤ 2 * N * ∑ i, w i * lam i :=
  ⟨source_modified_mw_lower w lam N hw0 hw1 hlam0 hlam1 hN,
   source_modified_mw_upper w lam N hw0 hw1 hlam0 hlam1⟩

end Qatlib.Papers.SeqMeasure16.MainResults.ModifiedMW
