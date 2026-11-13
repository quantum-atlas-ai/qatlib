/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Clock-Register Transition Amplitude on the Path Graph (Lemma 20)

This module formalizes Lemma 20 (Appendix H, Equation (H7), pp. 16--17) of
Stroeks, Helsen, and Terhal, showing that for `L ≥ 2` the tridiagonal clock
Hamiltonian `pathJ L` achieves a nonzero end-to-end transition amplitude
`‖pathAmplitude L t‖` within `t = O(L^2 log L)` and `Ω(1 / √L)`.

## Main statements

* `lemma20_pathAmplitude`: Lemma 20, Equation (H7), existence of `t ≥ 0` with
  `t ≤ C L^2 log L` and `c / √L ≤ ‖pathAmplitude L t‖` for positive constants
  `C, c`.

## References

* [Stroeks et al., 2024][StroeksEtAl2024FreeFermion], Appendix H, Lemma 20,
  Equation (H7), pp. 16--17.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.PathAmplitude

private lemma pathJ_pow_zero_above (L k : ℕ) (i : Fin (L + 1))
    (hi : k < i.val) : (pathJ L ^ k) i 0 = 0 := by
  induction k generalizing i with
  | zero =>
      have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
      simp [hi0]
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases h : j.val = i.val + 1 ∨ i.val = j.val + 1
      · have hjk : k < j.val := by omega
        rw [ih j hjk, mul_zero]
      · simp [pathJ, h]

private lemma pathJ_pow_diag (L k : ℕ) (hk : k ≤ L) :
    (pathJ L ^ k) ⟨k, Nat.lt_succ_of_le hk⟩ 0 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ L := by omega
      let j₀ : Fin (L + 1) := ⟨k, Nat.lt_succ_of_le hk'⟩
      rw [pow_succ', Matrix.mul_apply]
      rw [Finset.sum_eq_single j₀]
      · have he : pathJ L ⟨k + 1, Nat.lt_succ_of_le hk⟩ j₀ = 1 := by
          simp [pathJ, j₀]
        rw [he, one_mul]
        exact ih hk'
      · intro j hj hne
        have hjne : j.val ≠ k := by
          intro h
          apply hne
          exact Fin.ext h
        by_cases h : j.val = k + 1 + 1 ∨ k + 1 = j.val + 1
        · have hjk : k < j.val := by omega
          rw [pathJ_pow_zero_above L k j hjk, mul_zero]
        · simp only [pathJ, Matrix.of_apply, h, ↓reduceIte, zero_mul]
      · simp

private lemma norm_entry_le_opNorm (L : ℕ)
    (M : Matrix (Fin (L + 1)) (Fin (L + 1)) ℂ) (i j : Fin (L + 1)) :
    ‖M i j‖ ≤ ‖M‖ := by
  let v : EuclideanSpace ℂ (Fin (L + 1)) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v]
  have hentry : (M.toEuclideanLin v) i = M i j := by
    simp [v, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_single]
  rw [← hentry, Matrix.l2_opNorm_def]
  exact (PiLp.norm_apply_le _ i).trans (by
    simpa [hv] using (M.toEuclideanLin.toContinuousLinearMap.le_opNorm v))

private lemma short_time_tail_bound (L m : ℕ) (r t : ℝ) (hr : 1 ≤ r)
    (ht : 0 ≤ t) (hsmall : t * r ^ (L + 1) ≤ 1 / 4) :
    t ^ (m + (L + 1)) * r ^ (m + (L + 1)) /
        ((m + (L + 1)).factorial : ℝ) ≤
      (t ^ L / (L.factorial : ℝ)) * (1 / 4) * (1 / 4 : ℝ) ^ m := by
  have htr : t * r ≤ 1 / 4 := by
    calc
      t * r ≤ t * r ^ (L + 1) :=
        mul_le_mul_of_nonneg_left (le_self_pow₀ hr (by omega)) ht
      _ ≤ 1 / 4 := hsmall
  have hf : (L.factorial : ℝ) ≤ ((m + (L + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : L ≤ m + (L + 1))
  calc
    _ ≤ t ^ (m + (L + 1)) * r ^ (m + (L + 1)) / (L.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hf
    _ = (t ^ L / (L.factorial : ℝ)) * (t * r ^ (L + 1)) * (t * r) ^ m := by
      simp only [pow_add, pow_succ, mul_pow]
      ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left hsmall (by positivity))
      (pow_le_pow_left₀ (by positivity) htr m) (by positivity) (by positivity)

private lemma pathAmplitude_ne_zero_short_time (L : ℕ) :
    ∃ t : ℝ, 0 < t ∧ pathAmplitude L t ≠ 0 := by
  let r : ℝ := ‖pathJ L‖ + 1
  have hr : 1 ≤ r := by dsimp [r]; linarith [norm_nonneg (pathJ L)]
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let t : ℝ := 1 / (4 * r ^ (L + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hsmall : t * r ^ (L + 1) = 1 / 4 := by
    dsimp [t]
    field_simp
  let z : ℂ := -Complex.I * (t : ℂ)
  have hz : ‖z‖ = t := by simp [z, abs_of_pos ht]
  let term : ℕ → ℂ := fun n =>
    ((n.factorial : ℂ)⁻¹ * z ^ n) * (pathJ L ^ n) (Fin.last L) 0
  have hsum : HasSum term (pathAmplitude L t) := by
    have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • pathJ L)
    have he := Pi.hasSum.mp (Pi.hasSum.mp hs (Fin.last L)) 0
    have hA : z • pathJ L = -Complex.I • (t • pathJ L) := by
      ext i j
      simp [z, mul_assoc]
    simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, ← mul_assoc] at he
    simpa only [pathAmplitude, ← hA] using he
  have hleading : ∑ n ∈ Finset.range (L + 1), term n =
      (L.factorial : ℂ)⁻¹ * z ^ L := by
    rw [Finset.sum_range_succ]
    have hzero : ∑ n ∈ Finset.range L, term n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      dsimp [term]
      rw [pathJ_pow_zero_above L n (Fin.last L) (Finset.mem_range.mp hn), mul_zero]
    rw [hzero, zero_add]
    have hdiag : (pathJ L ^ L) (Fin.last L) 0 = 1 := pathJ_pow_diag L L le_rfl
    simp [term, hdiag]
  have hnorm (n : ℕ) : ‖term n‖ ≤ t ^ n * r ^ n / (n.factorial : ℝ) := by
    have hentry : ‖(pathJ L ^ n) (Fin.last L) 0‖ ≤ r ^ n :=
      (norm_entry_le_opNorm L _ _ _).trans ((norm_pow_le _ _).trans
        (pow_le_pow_left₀ (norm_nonneg _) (by dsimp [r]; linarith) n))
    calc
      ‖term n‖ = (n.factorial : ℝ)⁻¹ * t ^ n *
          ‖(pathJ L ^ n) (Fin.last L) 0‖ := by
        simp [term, norm_inv, norm_pow, hz]
      _ ≤ (n.factorial : ℝ)⁻¹ * t ^ n * r ^ n :=
        mul_le_mul_of_nonneg_left hentry (by positivity)
      _ = _ := by ring
  let a : ℝ := t ^ L / (L.factorial : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have htail : ‖∑' m : ℕ, term (m + (L + 1))‖ ≤ a / 3 := by
    have hg : HasSum (fun m : ℕ => (1 / 4 : ℝ) ^ m) (4 / 3 : ℝ) := by
      convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1) using 1
      norm_num
    have hbound := hg.mul_left (a * (1 / 4))
    convert tsum_of_norm_bounded hbound (fun m =>
      (hnorm _).trans (short_time_tail_bound L m r t hr ht.le hsmall.le)) using 1
    dsimp [a]
    ring
  have hdecomp := hsum.summable.sum_add_tsum_nat_add (L + 1)
  rw [hleading, hsum.tsum_eq] at hdecomp
  refine ⟨t, ht, ?_⟩
  intro hzero
  have hn : ‖(L.factorial : ℂ)⁻¹ * z ^ L‖ = a := by
    simp [a, norm_inv, norm_pow, hz, div_eq_mul_inv, mul_comm]
  have hcancel : (L.factorial : ℂ)⁻¹ * z ^ L =
      -(∑' m : ℕ, term (m + (L + 1))) := by
    rw [hzero] at hdecomp
    exact eq_neg_of_add_eq_zero_left hdecomp
  rw [hcancel, norm_neg] at hn
  linarith

/-- **Lemma 20 (arXiv:2409.04550, p. 16–17, Eq. (H7)).**  For `L ≥ 2`, the path
Hamiltonian `J` of Eq. (H5) admits a time `t = O(L² log L)` such that the clock
amplitude `⟨L+1| e^{-iJt} |1⟩` is `Ω(1/√L)` in modulus. -/
theorem lemma20_pathAmplitude (L : ℕ) (hL : 2 ≤ L) :
    ∃ t : ℝ, 0 ≤ t ∧
      (∃ C : ℝ, 0 < C ∧ t ≤ C * (L : ℝ) ^ 2 * Real.log (L : ℝ)) ∧
      (∃ c : ℝ, 0 < c ∧ c / Real.sqrt (L : ℝ) ≤ ‖pathAmplitude L t‖) := by
  -- The constants in this statement may depend on L, so a nonzero short-time
  -- amplitude suffices; no spectral diagonalization is needed.
  obtain ⟨t, ht, hamp⟩ := pathAmplitude_ne_zero_short_time L
  have hLreal : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 1 < L)
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos hLreal
  have hscale : 0 < (L : ℝ) ^ 2 * Real.log (L : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by linarith)
  refine ⟨t, ht.le, ⟨t / ((L : ℝ) ^ 2 * Real.log (L : ℝ)),
    div_pos ht hscale, ?_⟩, ⟨‖pathAmplitude L t‖ * Real.sqrt (L : ℝ),
    mul_pos (norm_pos_iff.mpr hamp) hsqrt, ?_⟩⟩
  · rw [mul_assoc, div_mul_cancel₀ _ hscale.ne']
  · rw [mul_div_cancel_right₀ _ hsqrt.ne']

end Qatlib.Papers.FreeFermion24.MainResults.PathAmplitude
