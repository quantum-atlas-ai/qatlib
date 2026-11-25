/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ClawFinding07.MainResults.Spectral.ProductJohnsonGap

@[expose] public section

/-!
# Two-sided Johnson product gap bounds for matrix verification

The single-element containment indicators differ by a first nonconstant
Johnson mode. Making the mode independent of the second vertex preserves
its eigenvalue on the product walk. Testing contraction on that mode
bounds the admissible gap from above.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.ClawFinding07.MainResults.Spectral

namespace Qatlib.Papers.MatProdVerify04.MainResults

/-- On the range `2 ≤ k ≤ n/2`, the product walk has contraction gap at
least `1/k`, and every admissible gap is at most `n/(k(n-k)) ≤ 2/k`. -/
theorem product_johnson_gap_bounds {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    SpectralGapAtLeast (chainProduct (johnsonChain n k) (johnsonChain n k)) (1 / (k : ℝ)) ∧
    ∀ δ : ℝ, δ ≤ 1 →
      SpectralGapAtLeast (chainProduct (johnsonChain n k) (johnsonChain n k)) δ →
      δ ≤ (n : ℝ) / ((k : ℝ) * ((n : ℝ) - k)) ∧ δ ≤ 2 / (k : ℝ) := by
  classical
  refine ⟨productJohnson_spectralGap_inv_right hk hkn hk hkn le_rfl, ?_⟩
  intro δ hδ hgap
  let J := JohnsonVertex n k
  let P := johnsonChain n k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hklt : k < n := by omega
  have hkr : (k : ℝ) < n := by exact_mod_cast hklt
  have hnr : (0 : ℝ) < n := hkpos.trans hkr
  let d := (k : ℝ) * ((n : ℝ) - k)
  have hd : 0 < d := mul_pos hkpos (sub_pos.mpr hkr)
  let μ := 1 - (n : ℝ) / d
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨k, hklt⟩
  let v : J → ℝ := fun S => johnsonInd {a} S - johnsonInd {b} S
  let s : J := ⟨Finset.univ.map (Fin.castLEEmb hklt.le), by simp⟩
  have ha : a ∈ s.1 := Finset.mem_map.mpr
    ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
  have hb : b ∉ s.1 := by
    intro hb
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hb
    have hval : i.val = k := congrArg Fin.val hi
    exact (Nat.ne_of_lt i.isLt) hval
  have hvs : v s = 1 := by simp [v, johnsonInd, ha, hb]
  have hind (z : Fin n) (S : J) :
      johnsonAct (johnsonInd {z}) S =
        johnsonTheta n k 1 * johnsonInd {z} S + k := by
    have h := johnsonOp_ind ({z} : Finset (Fin n)) S hklt.le (by simpa using (show 1 ≤ k by omega))
    have hs : (∑ t ∈ ({z} : Finset (Fin n)), johnsonInd (({z} : Finset (Fin n)).erase t) S) = 1 := by
      rw [Finset.sum_singleton]
      rw [show ({z} : Finset (Fin n)).erase z = ∅ by simp]
      simp [johnsonInd]
    rw [Finset.card_singleton, johnsonOp, hs, Nat.cast_one, sub_add_cancel, mul_one] at h
    linarith
  have hmode (S : J) : act P v S = μ * v S := by
    change act (johnsonChain n k) v S = _
    rw [johnsonChain_eq_johnsonNorm]
    change (johnsonNorm n k).mulVec v S = _
    rw [johnsonNorm_mulVec, ← johnsonAct_adjW]
    have hsub : johnsonAct v S =
        johnsonAct (johnsonInd {a}) S - johnsonAct (johnsonInd {b}) S := by
      simp only [johnsonAct, v, Finset.sum_sub_distrib]
    rw [hsub, hind, hind, show johnsonTheta n k 1 = d - n by simp [d, johnsonTheta]; ring]
    dsimp only [μ, v]
    field_simp
    ring
  have hP := johnsonChain_spectralGap hk hkn
  have hrow (S : J) : (∑ T : J, P S T) = 1 := hP.1.2 S
  have hcol (S : J) : (∑ T : J, P T S) = 1 := by
    calc
      _ = ∑ T : J, P S T := Finset.sum_congr rfl fun T _ => hP.2.1 T S
      _ = 1 := hrow S
  have hsum : ∑ S : J, v S = 0 := by
    have h := sum_act hcol v
    simp only [hmode, ← Finset.mul_sum] at h
    have hμ : μ - 1 ≠ 0 := by dsimp [μ]; linarith [div_pos hnr hd]
    exact (mul_eq_zero.mp (show (μ - 1) * (∑ S : J, v S) = 0 by linarith)).resolve_left hμ
  let u : J × J → ℝ := fun pair => v pair.1
  have hmean : ∑ x : J × J, u x = 0 := by
    simp only [Fintype.sum_prod_type, u, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, hsum, mul_zero]
  have hprod (x : J × J) : act (chainProduct P P) u x = μ * u x := by
    change (∑ y : J × J, (P x.1 y.1 * P x.2 y.2) * v y.1) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ S : J, (P x.1 S * v S) * (∑ T : J, P x.2 T) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T _ => by ring)
      _ = act P v x.1 := by
        simp [hrow, act]
        rfl
      _ = _ := hmode x.1
  have hnz : 0 < sqNorm u := by
    have hone : (1 : ℝ) ≤ sqNorm u := by
      unfold sqNorm
      have h := Finset.single_le_sum (f := fun x : J × J => u x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ (s,s))
      simpa only [u, hvs, one_pow] using h
    linarith
  have hcontract := hgap.2.2 u hmean
  change sqNorm (act (chainProduct P P) u) ≤ _ at hcontract
  have hscale : sqNorm (act (chainProduct P P) u) = μ ^ 2 * sqNorm u := by
    unfold sqNorm
    simp only [hprod, mul_pow, Finset.mul_sum]
    rfl
  rw [hscale] at hcontract
  have hδbound : δ ≤ (n : ℝ) / d := by
    by_contra! hnδ
    have hlt : 1 - δ < μ := by dsimp [μ]; linarith
    have hsq := mul_self_lt_mul_self (sub_nonneg.mpr hδ) hlt
    have hpow : (1 - δ) ^ 2 < μ ^ 2 := by simpa only [pow_two] using hsq
    exact (not_lt_of_ge hcontract) (mul_lt_mul_of_pos_right hpow hnz)
  refine ⟨hδbound, hδbound.trans ?_⟩
  have hhalf : 2 * (k : ℝ) ≤ n := by exact_mod_cast hkn
  apply (div_le_div_iff₀ hd hkpos).mpr
  dsimp [d]
  nlinarith [mul_nonneg hkpos.le (show 0 ≤ (n : ℝ) - 2 * k by linarith)]

/-- On at least three vertices the singleton Johnson chain contracts every
mean-zero vector by a factor at most one half. -/
theorem johnson_singleton_gap {n : ℕ} (hn : 3 ≤ n) :
    SpectralGapAtLeast (johnsonChain n 1) (1 / 2 : ℝ) := by
  classical
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨⟨johnsonChain_nonneg n 1 (by omega), ?_⟩, johnsonChain_symm n 1, ?_⟩
  · intro s
    rw [johnsonChain_eq_johnsonNorm]
    exact johnsonNorm_rowsum (by decide) (by omega) s
  · intro v hv
    let c := ((n : ℝ) - 1)⁻¹
    have hc0 : 0 ≤ c := inv_nonneg.mpr (by linarith)
    have hc : c ≤ (1 : ℝ) / 2 := by
      simpa only [c, one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ n - 1 by linarith))
    have hentry (s t : JohnsonVertex n 1) :
        johnsonChain n 1 s t = c - (if t = s then c else 0) := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp t.2
      have ht : t = s ↔ b = a := by
        rw [Subtype.ext_iff, hb, ha, Finset.singleton_inj]
      simp only [ht, johnsonChain, johnsonAdj, ha, hb, Finset.sdiff_singleton_eq_erase]
      by_cases hab : b = a
      · subst b
        simp
      · have hmem : b ∉ ({a} : Finset (Fin n)) := by simpa using hab
        rw [Finset.erase_eq_of_notMem hmem]
        simp [hab, c]
    have haction (s : JohnsonVertex n 1) :
        (∑ t, johnsonChain n 1 s t * v t) = -(c * v s) := by
      simp only [hentry, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hv, mul_zero,
        ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_sub]
    have hnonneg : 0 ≤ sqNorm v := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      _ = c ^ 2 * sqNorm v := by
        unfold sqNorm
        simp only [haction, neg_pow_two, mul_pow, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_self_le_mul_self hc0 hc]) hnonneg

/-- Lemma 4's two-sided order bound on the nondegenerate source range
`n ≥ 3` and `1 ≤ k ≤ n/2`, with normalized contraction parameters. -/
theorem product_johnson_gap_order {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    SpectralGapAtLeast (chainProduct (johnsonChain n k) (johnsonChain n k))
      (1 / (2 * (k : ℝ))) ∧
    ∀ δ : ℝ, δ ≤ 1 →
      SpectralGapAtLeast (chainProduct (johnsonChain n k) (johnsonChain n k)) δ →
      δ ≤ 2 / (k : ℝ) := by
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · have := johnsonVertex_nonempty (by omega : 1 ≤ n)
    have h := johnson_singleton_gap hn
    refine ⟨?_, fun δ hδ _ => hδ.trans (by norm_num)⟩
    simpa only [Nat.cast_one, mul_one, min_self] using
      spectralGap_chainProduct (δ₁ := 1 / 2) (δ₂ := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) h h
  · obtain ⟨hlo,hhi⟩ := product_johnson_gap_bounds hk2 hkn
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨spectralGap_mono hlo (by positivity) ?_ ?_, fun δ hδ hg => (hhi δ hδ hg).2⟩
    · exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk'

end Qatlib.Papers.MatProdVerify04.MainResults
