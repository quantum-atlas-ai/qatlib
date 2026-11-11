/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4: the largest eigenvalue of `A^{(m,l)}` is `o(m)` for `l = o(m)` (paper p.9)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Lemma 4, Section 2.3, p.9.

> **Lemma 4.** For matrices `A^{(m,l)}` with `l = o(m)`, `λmax(A^{(m,l)}) = o(m)`.

**Paper proof** (p.9). `A^{(m,l)}` is nonnegative, so `λmax(A^{(m,l)}) ≤ √m · λmax(B^{(l)})`,
where `B^{(l)}` is tridiagonal with `√k` on the off-diagonals. `B^{(l)}/√2` is the Jacobi matrix of
the monic Hermite recurrence, so its largest eigenvalue is the largest zero of the degree-`(l+1)`
monic Hermite polynomial, which is `O(√l)`; hence `λmax(A^{(m,l)}) = O(√(ml)) = o(m)`.

**Formalisation route used here.** Instead of the Hermite-zero bounds we use the elementary
Gershgorin row-sum bound `λmax(A^{(m,l)}) ≤ 2√(ml)` (every off-diagonal entry is at most `√(ml)`
and every row has at most two off-diagonal entries). This gives the same conclusion
`λmax/m ≤ 2√(l/m) → 0`; the paper's Hermite argument yields the same `O(√(ml))` order. The
per-matrix row-sum bound is proved below (`maxEigenvalue_dijMatrix_le`); the final asymptotic
statement is `lemma4_eigenvalue_sublinear`.
-/

open scoped BigOperators
open Filter Matrix
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Lemma4

/-! ## 1. Entrywise and row-sum bounds for `A^{(m,l)}` -/

/-- Each coefficient `a_k = √(k(m-k+1))` is nonnegative. -/
lemma dijCoeff_nonneg (m k : ℕ) : 0 ≤ dijCoeff m k := Real.sqrt_nonneg _

/-- For `1 ≤ k ≤ l ≤ m`, the coefficient `a_k = √(k(m-k+1))` is at most `√(m·l)`. -/
lemma dijCoeff_le_sqrt (m l k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ l) (hlm : l ≤ m) :
    dijCoeff m k ≤ Real.sqrt ((m : ℝ) * (l : ℝ)) := by
  unfold dijCoeff
  apply Real.sqrt_le_sqrt
  have hkR : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hk
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := by positivity
  have hmk : ((m : ℝ) - (k : ℝ) + 1) ≤ (m : ℝ) := by linarith
  have hmk0 : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) + 1 := by
    have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans hk hlm
    linarith
  calc (k : ℝ) * ((m : ℝ) - (k : ℝ) + 1) ≤ (l : ℝ) * (m : ℝ) :=
        mul_le_mul hkR hmk hmk0 hl0
    _ = (m : ℝ) * (l : ℝ) := by ring

/-- `A^{(m,l)}` is a symmetric real matrix, hence Hermitian (needed to speak of eigenvalues). -/
lemma dijMatrix_isHermitian (m l : ℕ) : (dijMatrix m l).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [dijMatrix, star_trivial]
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos (or_comm.mpr h), if_pos h, min_comm]
  · rw [if_neg (fun hh => h (or_comm.mpr hh)), if_neg h]

/-- A nonzero entry of `A^{(m,l)}` off the diagonal sits in an adjacent column. -/
lemma dijMatrix_offdiag_support (m l : ℕ) {i j : Fin (l + 1)} (_hji : j ≠ i)
    (h : dijMatrix m l i j ≠ 0) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  unfold dijMatrix at h
  split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

/-- Every off-diagonal entry of `A^{(m,l)}` is at most `√(m·l)`. -/
lemma dijMatrix_offdiag_le (m l : ℕ) (hlm : l ≤ m) {i j : Fin (l + 1)} (hji : j ≠ i)
    (h : dijMatrix m l i j ≠ 0) :
    ‖dijMatrix m l i j‖ ≤ Real.sqrt ((m : ℝ) * (l : ℝ)) := by
  obtain hcond := dijMatrix_offdiag_support m l hji h
  have hk1 : 1 ≤ Nat.min i.val j.val + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hk : Nat.min i.val j.val + 1 ≤ l := by
    have hjlt : j.val < l + 1 := j.isLt
    have hilt : i.val < l + 1 := i.isLt
    rcases hcond with hc | hc
    · have hmin : Nat.min i.val j.val = i.val := Nat.min_eq_left (by omega)
      omega
    · have hmin : Nat.min i.val j.val = j.val := Nat.min_eq_right (by omega)
      omega
  have hbound := dijCoeff_le_sqrt m l (Nat.min i.val j.val + 1) hk1 hk hlm
  unfold dijMatrix
  rw [if_pos hcond, Real.norm_eq_abs, abs_of_nonneg (dijCoeff_nonneg m (Nat.min i.val j.val + 1))]
  exact hbound

/-- Each row of `A^{(m,l)}` (off the diagonal) has at most two nonzero entries, so its
Gershgorin radius `∑_{j ≠ i} ‖A i j‖` is at most `2√(m·l)`. -/
lemma dijMatrix_row_sum_le (m l : ℕ) (hlm : l ≤ m) (i : Fin (l + 1)) :
    ∑ j ∈ Finset.univ.erase i, ‖dijMatrix m l i j‖
      ≤ 2 * Real.sqrt ((m : ℝ) * (l : ℝ)) := by
  set b : ℝ := Real.sqrt ((m : ℝ) * (l : ℝ)) with hbdef
  have hb : 0 ≤ b := by rw [hbdef]; exact Real.sqrt_nonneg _
  -- The support of row `i` inside `univ.erase i`.
  set S : Finset (Fin (l + 1)) :=
    (Finset.univ.erase i).filter (fun j => dijMatrix m l i j ≠ 0) with hSdef
  have hmem : ∀ j ∈ S, j ∈ Finset.univ.erase i ∧ dijMatrix m l i j ≠ 0 := by
    intro j hj
    rw [hSdef] at hj
    exact Finset.mem_filter.mp hj
  have hji : ∀ j ∈ S, j ≠ i := fun j hj => (Finset.mem_erase.mp (hmem j hj).1).1
  have hA : ∀ j ∈ S, dijMatrix m l i j ≠ 0 := fun j hj => (hmem j hj).2
  have hsum : ∑ j ∈ Finset.univ.erase i, ‖dijMatrix m l i j‖
      = ∑ j ∈ S, ‖dijMatrix m l i j‖ := by
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hAj : dijMatrix m l i j = 0
    · simp [hAj]
    · simp [hAj]
  -- At most one supporting index below `i` and at most one above.
  have hlt : (S.filter (fun j => j.val < i.val)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha c hc
    simp only [Finset.mem_filter] at ha hc
    have hcond := dijMatrix_offdiag_support m l (hji a ha.1) (hA a ha.1)
    have hcondc := dijMatrix_offdiag_support m l (hji c hc.1) (hA c hc.1)
    have haeq : a.val + 1 = i.val := by
      rcases hcond with hh | hh <;> omega
    have hceq : c.val + 1 = i.val := by
      rcases hcondc with hh | hh <;> omega
    exact Fin.ext (by omega)
  have hgt : (S.filter (fun j => i.val < j.val)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha c hc
    simp only [Finset.mem_filter] at ha hc
    have hcond := dijMatrix_offdiag_support m l (hji a ha.1) (hA a ha.1)
    have hcondc := dijMatrix_offdiag_support m l (hji c hc.1) (hA c hc.1)
    have haeq : i.val + 1 = a.val := by
      rcases hcond with hh | hh <;> omega
    have hceq : i.val + 1 = c.val := by
      rcases hcondc with hh | hh <;> omega
    exact Fin.ext (by omega)
  have hcover : S ⊆ S.filter (fun j => j.val < i.val) ∪ S.filter (fun j => i.val < j.val) := by
    intro j hj
    have hne : j ≠ i := hji j hj
    have hval : j.val ≠ i.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hval with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, h⟩)
  have hcard : S.card ≤ 2 := by
    calc S.card ≤ (S.filter (fun j => j.val < i.val)
            ∪ S.filter (fun j => i.val < j.val)).card := Finset.card_le_card hcover
      _ ≤ (S.filter (fun j => j.val < i.val)).card
            + (S.filter (fun j => i.val < j.val)).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add hlt hgt
      _ = 2 := rfl
  have hterm : ∀ j ∈ S, ‖dijMatrix m l i j‖ ≤ b := by
    intro j hj
    have hb' := dijMatrix_offdiag_le m l hlm (hji j hj) (hA j hj)
    rw [hbdef]
    exact hb'
  calc ∑ j ∈ Finset.univ.erase i, ‖dijMatrix m l i j‖
      = ∑ j ∈ S, ‖dijMatrix m l i j‖ := hsum
    _ ≤ S.card • b := Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * b := by rw [nsmul_eq_mul]
    _ ≤ 2 * b := by
        have h2 : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right h2 hb

/-! ## 2. Spectral bound and the asymptotic conclusion -/

/-- Membership in the matrix spectrum as an eigenvalue of the associated linear map. -/
lemma hasEigenvalue_toLin' (m l : ℕ) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (dijMatrix m l)) :
    Module.End.HasEigenvalue (Matrix.toLin' (dijMatrix m l)) μ :=
  Module.End.HasEigenvalue.of_mem_spectrum (Matrix.spectrum_toLin' (dijMatrix m l) ▸ hμ)

/-- The diagonal of `A^{(m,l)}` vanishes. -/
lemma dijMatrix_diag (m l : ℕ) (i : Fin (l + 1)) : dijMatrix m l i i = 0 := by
  unfold dijMatrix
  rw [if_neg (by omega)]

/-- Gershgorin's circle theorem specialised to `A^{(m,l)}`: every eigenvalue lies within the
Gershgorin radius of its row, and that radius is bounded by `2√(m·l)`. -/
lemma abs_eigenvalue_le (m l : ℕ) (hlm : l ≤ m) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (dijMatrix m l)) :
    |μ| ≤ 2 * Real.sqrt ((m : ℝ) * (l : ℝ)) := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (hasEigenvalue_toLin' m l hμ)
  have hball : |μ| ≤ ∑ j ∈ Finset.univ.erase k, ‖dijMatrix m l k j‖ := by
    simpa [dijMatrix_diag, Real.dist_0_eq_abs] using hk
  exact hball.trans (dijMatrix_row_sum_le m l hlm k)

/-- Every real eigenvalue of `A^{(m,l)}` is at most `2√(m·l)` (Gershgorin's circle theorem,
using that the diagonal vanishes and each row has at most two nonzero off-diagonal entries). -/
lemma eigenvalue_le (m l : ℕ) (hlm : l ≤ m) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (dijMatrix m l)) :
    μ ≤ 2 * Real.sqrt ((m : ℝ) * (l : ℝ)) := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (hasEigenvalue_toLin' m l hμ)
  have hball : |μ| ≤ ∑ j ∈ Finset.univ.erase k, ‖dijMatrix m l k j‖ := by
    simpa [dijMatrix_diag, Real.dist_0_eq_abs] using hk
  calc μ ≤ |μ| := le_abs_self μ
    _ ≤ ∑ j ∈ Finset.univ.erase k, ‖dijMatrix m l k j‖ := hball
    _ ≤ 2 * Real.sqrt ((m : ℝ) * (l : ℝ)) := dijMatrix_row_sum_le m l hlm k

/-- Every real eigenvalue of `A^{(m,l)}` is at least `-2√(m·l)`. -/
lemma neg_eigenvalue_le (m l : ℕ) (hlm : l ≤ m) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (dijMatrix m l)) :
    -(2 * Real.sqrt ((m : ℝ) * (l : ℝ))) ≤ μ := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (hasEigenvalue_toLin' m l hμ)
  have hball : |μ| ≤ ∑ j ∈ Finset.univ.erase k, ‖dijMatrix m l k j‖ := by
    simpa [dijMatrix_diag, Real.dist_0_eq_abs] using hk
  have hrow := dijMatrix_row_sum_le m l hlm k
  have h1 : -|μ| ≤ μ := neg_abs_le μ
  linarith

/-- The spectrum of `A^{(m,l)}` is nonempty (it is a symmetric real matrix, so it has a real
eigenvalue). -/
lemma spectrum_nonempty (m l : ℕ) : (spectrum ℝ (dijMatrix m l)).Nonempty := by
  have hH := dijMatrix_isHermitian m l
  exact ⟨hH.eigenvalues ⟨0, Nat.succ_pos l⟩, hH.eigenvalues_mem_spectrum_real ⟨0, Nat.succ_pos l⟩⟩

/-- **Gershgorin bound for Lemma 4**: `λmax(A^{(m,l)}) ≤ 2√(m·l)` for `l ≤ m`. -/
lemma maxEigenvalue_dijMatrix_le (m l : ℕ) (hlm : l ≤ m) :
    maxEigenvalue (dijMatrix m l) ≤ 2 * Real.sqrt ((m : ℝ) * (l : ℝ)) := by
  unfold maxEigenvalue
  refine csSup_le (spectrum_nonempty m l) ?_
  intro μ hμ
  exact eigenvalue_le m l hlm hμ

/-- **Lemma 4** (Parekh, arXiv:2509.19966v2, Lemma 4, p.9), in sequence form: for a family of
degrees `l(m)` with `l(m) = o(m)` (and eventually `l(m) ≤ m`), the largest eigenvalue of
`A^{(m,l(m))}` is `o(m)`:
`λmax(A^{(m,l(m))}) / m → 0`.

**Proof.** The per-matrix Gershgorin bounds `maxEigenvalue_dijMatrix_le` and `neg_eigenvalue_le`
give `|λmax| ≤ 2√(m·l(m))` eventually. Dividing by `m > 0`,
`|λmax|/m ≤ 2√(m·l(m))/m = 2√(l(m)/m)`, and `l(m)/m → 0` together with continuity of `Real.sqrt`
makes the right-hand side tend to `0`. `squeeze_zero'` finishes. This proves the same
`O(√(ml)) = o(m)` order as the paper's Hermite-zero argument. -/
theorem lemma4_eigenvalue_sublinear (l : ℕ → ℕ)
    (hl : Tendsto (fun m : ℕ => (l m : ℝ) / (m : ℝ)) atTop (nhds 0))
    (hlm : ∀ᶠ m : ℕ in atTop, l m ≤ m) :
    Tendsto (fun m : ℕ => maxEigenvalue (dijMatrix m (l m)) / (m : ℝ)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun m : ℕ => Real.sqrt ((l m : ℝ) / (m : ℝ))) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hl
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  have hbound : Tendsto (fun m : ℕ => 2 * Real.sqrt ((l m : ℝ) / (m : ℝ)))
      atTop (nhds 0) := by
    simpa using hsq.const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hbound
  filter_upwards [hlm, eventually_ge_atTop 1] with m hm hm1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hbdd : BddAbove (spectrum ℝ (dijMatrix m (l m))) :=
    ⟨2 * Real.sqrt ((m : ℝ) * (l m : ℝ)), fun x hx =>
      (abs_le.mp (abs_eigenvalue_le m (l m) hm hx)).2⟩
  obtain ⟨μ, hμ⟩ := spectrum_nonempty m (l m)
  have hμle : μ ≤ maxEigenvalue (dijMatrix m (l m)) := le_csSup hbdd hμ
  have hμge : -(2 * Real.sqrt ((m : ℝ) * (l m : ℝ))) ≤ μ :=
    neg_eigenvalue_le m (l m) hm hμ
  have hupper : maxEigenvalue (dijMatrix m (l m)) ≤ 2 * Real.sqrt ((m : ℝ) * (l m : ℝ)) :=
    maxEigenvalue_dijMatrix_le m (l m) hm
  have hlower : -(2 * Real.sqrt ((m : ℝ) * (l m : ℝ))) ≤
      maxEigenvalue (dijMatrix m (l m)) := le_trans hμge hμle
  have hnorm : ‖maxEigenvalue (dijMatrix m (l m))‖ ≤
      2 * Real.sqrt ((m : ℝ) * (l m : ℝ)) := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hdiv : ‖maxEigenvalue (dijMatrix m (l m)) / (m : ℝ)‖ =
      ‖maxEigenvalue (dijMatrix m (l m))‖ / (m : ℝ) := by
    rw [norm_div, Real.norm_of_nonneg (le_of_lt hmR)]
  rw [hdiv]
  have hsqrt : Real.sqrt ((m : ℝ) * (l m : ℝ)) / (m : ℝ) =
      Real.sqrt ((l m : ℝ) / (m : ℝ)) := by
    calc Real.sqrt ((m : ℝ) * (l m : ℝ)) / (m : ℝ)
        = Real.sqrt ((m : ℝ) * (l m : ℝ)) / Real.sqrt ((m : ℝ) ^ 2) := by
            rw [Real.sqrt_sq (le_of_lt hmR)]
      _ = Real.sqrt (((m : ℝ) * (l m : ℝ)) / (m : ℝ) ^ 2) := by
            rw [Real.sqrt_div (by positivity)]
      _ = Real.sqrt ((l m : ℝ) / (m : ℝ)) := by
            congr 1
            field_simp
  calc ‖maxEigenvalue (dijMatrix m (l m))‖ / (m : ℝ)
      ≤ 2 * Real.sqrt ((m : ℝ) * (l m : ℝ)) / (m : ℝ) :=
        div_le_div_of_nonneg_right hnorm (le_of_lt hmR)
    _ = 2 * Real.sqrt ((l m : ℝ) / (m : ℝ)) := by rw [mul_div_assoc, hsqrt]

end Lemma4

end Qatlib.Papers.DQIAdvantage25.MainResults
