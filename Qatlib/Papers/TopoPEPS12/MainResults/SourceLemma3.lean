/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan
import Mathlib.Algebra.Order.Field.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma3 — failure probability of the back-and-forth measurement sequence

Schwarz--Cubitt--Temme--Verstraete--Pérez-García,
*Preparing topological PEPS on a quantum computer*, fixed arXiv:1211.4050v1 (16 Nov 2012),
PRA 88, 032321 (2013). Source location: Lemma 3 (p. 4, right column, Eq. (8)) with the proof
Eqs. (9)--(10) on p. 4, right column; Fig. 1 on p. 4.

Lemma 3 (paper): the measurement sequence of `{P_t, P_t^⊥}` and `{P_{t+1}, P_{t+1}^⊥}`
depicted in Fig. 1 has failure probability `p_fail(m) < 1/(2 d_min m)` after `m` subsequent
measurement steps, where `d_min = min_k d_k` is the minimal overlap between the eigenstates of
`P_t` and `P_{t+1}`.

Formalisation boundary. The concrete quantum instrument (the projectors `P_t`, `P_{t+1}` and the
intermediate states) is not rebuilt. The paper reduces the chain in Eq. (9) to its diagonal form
Eq. (10), `p_fail(m) = Σ_k |c_k|² (1-d_k)(1-2 d_k(1-d_k))^m`, over the Jordan blocks of
Lemma 1 with weights `c_k` (`Σ_k |c_k|² = 1`) and overlaps `d_k ∈ [0,1]`. We formalise Eq. (10)
with `w k = |c_k|²` and prove the stated bound Eq. (8). The per-block scalar estimate is obtained
by reusing `rejection_scalar_bound` from the shared library
(`Qatlib.Concepts.MixedInstrument.RewindAlgebra.rejection_scalar_bound`, itself the
geometric estimate `t(1-t)(t²+(1-t)²)^n ≤ 1/(2(n+1))`), applied with `t = 1 - d_k`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TopoPEPS12.MainResults

/-- Paper Lemma 3, Eq. (10), per-block scalar estimate: for `d ∈ (0,1]` and `m ≥ 1`,
`(1-d)(1-2d(1-d))^m ≤ 1/(2 d m)`. This is the term of the diagonalised failure probability
Eq. (10) after using `(1-x) ≤ e^{-x}` and `y e^{-y} ≤ e^{-1} < 1` (paper p. 4). -/
theorem perBlock_failure_bound (d : ℝ) (hd0 : 0 < d) (hd1 : d ≤ 1) (m : ℕ) (hm : 0 < m) :
    (1 - d) * (1 - 2 * d * (1 - d)) ^ m ≤ 1 / (2 * d * m) := by
  -- apply the scalar geometric estimate with `t = 1 - d`
  have ht : (1 - d) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h :=
    Qatlib.Concepts.MixedInstrument.RewindAlgebra.rejection_scalar_bound
      (1 - d) ht m
  -- expand the scalar estimate into the paper's block form
  have hbase : ((1 - d) ^ 2 + (1 - (1 - d)) ^ 2) = 1 - 2 * d * (1 - d) := by ring
  have hone : (1 - (1 - d)) = d := by ring
  rw [hbase, hone] at h
  -- h : (1-d) * d * (1 - 2 d (1-d))^m ≤ 1/(2*(m+1))
  -- multiply both sides by `2(m+1)` and rearrange to divide by `d`
  have hm1 : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
  have step : (1 - d) * (1 - 2 * d * (1 - d)) ^ m * (2 * d * ((m : ℝ) + 1)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h (le_of_lt hm1)
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hm1)] at this
    calc (1 - d) * (1 - 2 * d * (1 - d)) ^ m * (2 * d * ((m : ℝ) + 1))
        = ((1 - d) * d * (1 - 2 * d * (1 - d)) ^ m) * (2 * ((m : ℝ) + 1)) := by ring
      _ ≤ 1 := this
  -- conclude `≤ 1/(2 d (m+1))`, then weaken to `1/(2 d m)`
  have htight : (1 - d) * (1 - 2 * d * (1 - d)) ^ m ≤ 1 / (2 * d * ((m : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d * ((m : ℝ) + 1))]
    calc (1 - d) * (1 - 2 * d * (1 - d)) ^ m * (2 * d * ((m : ℝ) + 1))
        = (1 - d) * (1 - 2 * d * (1 - d)) ^ m * (2 * d * ((m : ℝ) + 1)) := rfl
      _ ≤ 1 := step
  have hmono : 1 / (2 * d * ((m : ℝ) + 1)) ≤ 1 / (2 * d * (m : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * d * (m : ℝ))
    push_cast
    nlinarith [hd0]
  exact le_trans htight hmono

/-- **Paper Lemma 3** (p. 4, right column, Eq. (8)). After `m ≥ 1` back-and-forth measurement
steps the failure probability, in the diagonalised form Eq. (10)
`p_fail(m) = Σ_k w_k (1-d_k)(1-2 d_k(1-d_k))^m` with normalised weights `w_k = |c_k|²`,
is at most `1/(2 d_min m)`, where `d_min = min_k d_k` is the minimal overlap. -/
theorem lemma3_failure_bound {ι : Type*} [Fintype ι]
    (w d : ι → ℝ) (m : ℕ) (hm : 0 < m)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (hd1 : ∀ k, d k ≤ 1)
    (hwpos : ∀ k, w k ≠ 0 → 0 < d k)
    (dmin : ℝ) (hdminpos : 0 < dmin) (hdmin : ∀ k, w k ≠ 0 → dmin ≤ d k) :
    ∑ k, w k * ((1 - d k) * (1 - 2 * d k * (1 - d k)) ^ m) ≤ 1 / (2 * dmin * m) := by
  have hterm : ∀ k ∈ (Finset.univ : Finset ι),
      w k * ((1 - d k) * (1 - 2 * d k * (1 - d k)) ^ m)
        ≤ w k * (1 / (2 * dmin * m)) := by
    intro k _
    by_cases hwk : w k = 0
    · rw [hwk, zero_mul, zero_mul]
    · have hdk0 : 0 < d k := hwpos k hwk
      have hdk1 : d k ≤ 1 := hd1 k
      have hpb := perBlock_failure_bound (d k) hdk0 hdk1 m hm
      have hfrac : 1 / (2 * d k * m) ≤ 1 / (2 * dmin * m) := by
        apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * dmin * (m : ℝ))
        have := hdmin k hwk
        nlinarith [this, hdminpos, hdk0, hm]
      exact mul_le_mul_of_nonneg_left (le_trans hpb hfrac) (hw k)
  calc ∑ k, w k * ((1 - d k) * (1 - 2 * d k * (1 - d k)) ^ m)
      ≤ ∑ k, w k * (1 / (2 * dmin * m)) := Finset.sum_le_sum hterm
    _ = (∑ k, w k) * (1 / (2 * dmin * m)) := by rw [Finset.sum_mul]
    _ = 1 / (2 * dmin * m) := by rw [hsum, one_mul]

end Qatlib.Papers.TopoPEPS12.MainResults
