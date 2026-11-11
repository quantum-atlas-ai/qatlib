/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts

/-!
# Arithmetic bounds for corrected walk costs

This module supplies integer subset-size windows and arithmetic estimates for graph-search
resource bounds. `correctedSubsetWindow` brackets a positive integer by consecutive powers,
while logarithm and division lemmas transfer discrete cost expressions to real inequalities.

`corrected_hAlg_real_cost` bounds the graph-search subroutine cost, and `corrected_gc_budget`
specializes a collision budget at a cube-root window. These estimates support quantitative
analyses in the quantum-walk search setting [MagniezNayakRolandSantha2011].

## Main statements

* `correctedSubsetWindow`: an integer power window.
* `corrected_hAlg_real_cost`: a real cost bound for the graph subroutine.
* `corrected_gc_budget`: the explicit `n^(2/3)` collision budget.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

/-- For positive `N` and `k`, there is a positive integer `r` whose `k`th power is at least `N`
while `(r - 1)^k` is below `N`. -/
theorem correctedSubsetWindow (N k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    ∃ r : ℕ, 1 ≤ r ∧ N ≤ r ^ k ∧ (r - 1) ^ k < N := by
  have hex : ∃ r : ℕ, N ≤ r ^ k := ⟨N, Nat.le_self_pow hk.ne' N⟩
  let r := Nat.find hex
  have hp : N ≤ r ^ k := Nat.find_spec hex
  have hr : 0 < r := by
    by_contra h
    have hz : r = 0 := by omega
    rw [hz, zero_pow hk.ne'] at hp
    omega
  refine ⟨r, hr, hp, ?_⟩
  exact Nat.lt_of_not_ge (Nat.find_min hex (show r - 1 < r by omega))

/-- For positive `n`, `Nat.log 2 (n + 1) + 2` is at most twice `Nat.log 2 n + 2`. -/
theorem corrected_log_succ_le (n : ℕ) (hn : 0 < n) :
    Nat.log 2 (n + 1) + 2 ≤ 2 * (Nat.log 2 n + 2) := by
  have h := Nat.log_mono_right (b := 2) (show n + 1 ≤ n * 2 by omega)
  rw [Nat.log_mul_base (by decide) hn.ne'] at h
  omega

/-- For positive `r`, natural-number division `n / r`, cast to the reals, is at most the real
quotient. -/
theorem corrected_cast_div_le (n r : ℕ) (hr : 0 < r) :
    ((n / r : ℕ) : ℝ) ≤ (n : ℝ) / r := by
  apply (le_div_iff₀ (by exact_mod_cast hr)).mpr
  exact_mod_cast Nat.div_mul_le_self n r

/-- For positive graph size and `r ≥ 1`, bound the real-valued cost of `hAlg` by the stated
cubic-logarithmic factor times its setup, collision, and verification terms. -/
theorem corrected_hAlg_real_cost {n k : ℕ} (hn : 0 < n)
    (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (kcs : KCollisionSolver) (r qH : ℕ) (hr : 1 ≤ r) (stape : ℕ → kcs.seed) :
    ((hAlg adj H hv kcs r qH stape).2 : ℝ) ≤
      (2 ^ 16 : ℕ) * kcs.κ * ((Nat.log 2 n + 2 : ℕ) ^ 3) *
        ((r : ℝ) ^ 2 + ((n : ℝ) / r) ^ ((k - 1) / 2) *
          ((qH : ℝ) + (Nat.sqrt r : ℝ) * r) + (qH : ℝ) + (n : ℝ)) := by
  have hc := kcs.charges r (hCandRel adj H hv) (r*r) r qH (stape 0)
  have hraw : (hAlg adj H hv kcs r qH stape).2 ≤
      kcs.κ * (Nat.log 2 (n+1)+2) *
        (r*r+(n/r)^((k-1)/2)*(qH+Nat.sqrt r*r)) := by
    cases he : kcs.run r (hCandRel adj H hv) (r*r) r qH (stape 0) with
    | none => simpa only [hAlg, he] using hc
    | some K => simp only [hAlg, he]; split_ifs <;> exact hc
  have hdiv := corrected_cast_div_le n r (by omega)
  have hp := pow_le_pow_left₀ (show 0 ≤ ((n/r : ℕ) : ℝ) by positivity) hdiv ((k-1)/2)
  have hlog : ((Nat.log 2 (n+1)+2 : ℕ) : ℝ) ≤
      2 * ((Nat.log 2 n+2 : ℕ) : ℝ) := by
    exact_mod_cast corrected_log_succ_le n hn
  have hL : (2 : ℝ) ≤ ((Nat.log 2 n+2 : ℕ) : ℝ) := by norm_cast; omega
  have hfactor : (kcs.κ : ℝ) * ((Nat.log 2 (n+1)+2 : ℕ) : ℝ) ≤
      (2^16 : ℕ) * (kcs.κ : ℝ) * (((Nat.log 2 n+2 : ℕ) : ℝ)^3) := by
    have hpoly : 2 * ((Nat.log 2 n+2 : ℕ) : ℝ) ≤
        (2^16 : ℕ) * (((Nat.log 2 n+2 : ℕ) : ℝ)^3) := by
      have hh : 0 ≤ ((Nat.log 2 n+2 : ℕ) : ℝ) *
          ((((Nat.log 2 n+2 : ℕ) : ℝ)^2) - 1) :=
        mul_nonneg (by positivity) (by nlinarith)
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) kcs.κ]
  have hsum : (((r*r+(n/r)^((k-1)/2)*(qH+Nat.sqrt r*r)) : ℕ) : ℝ) ≤
      ((r : ℝ)^2 + ((n : ℝ)/r)^((k-1)/2) *
        ((qH : ℝ)+(Nat.sqrt r : ℝ)*r)+(qH : ℝ)+(n : ℝ)) := by
    push_cast
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ (qH : ℝ) + (Nat.sqrt r : ℝ)*r by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) qH, Nat.cast_nonneg (α := ℝ) n]
  have hrawR : ((hAlg adj H hv kcs r qH stape).2 : ℝ) ≤
      (kcs.κ : ℝ) * ((Nat.log 2 (n+1)+2 : ℕ) : ℝ) *
        (((r*r+(n/r)^((k-1)/2)*(qH+Nat.sqrt r*r)) : ℕ) : ℝ) := by
    exact_mod_cast hraw
  exact hrawR.trans (mul_le_mul hfactor hsum (by positivity) (by positivity))

/-- When `r` brackets the cube root of `n^2`, the stated integer collision-cost bound implies a
real cost at most `2 * κ * (Nat.log 2 n + 2)^2 * n^(2/3)`. -/
theorem corrected_gc_budget (n r κ q : ℕ) (hn : 0 < n) (hr : 1 ≤ r) (hκ : 1 ≤ κ)
    (hl : n^2 ≤ r^3) (hu : (r-1)^3 < n^2)
    (hq : q ≤ κ*(Nat.log 2 (n+1)+2)*(r+(n/r)*Nat.sqrt r)+2) :
    (q : ℝ) ≤ (2*κ : ℕ)*((Nat.log 2 n+2 : ℕ)^2)*((n : ℝ)^(2/3 : ℝ)) := by
  have hrn : r ≤ n := by
    by_contra hh
    have hh' : n ≤ r-1 := by omega
    have hp := Nat.pow_le_pow_left hh' 3
    have hn23 : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by decide)
    omega
  by_cases hn1 : n = 1
  · subst n
    have hr1 : r = 1 := by omega
    subst r
    norm_num at hq ⊢
    have hqR : (q : ℝ) ≤ (κ : ℝ)*3*2+2 := by exact_mod_cast hq
    have hκR : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    nlinarith
  let a : ℝ := (n : ℝ)^(2/3 : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < a := Real.rpow_pos_of_pos hnR _
  have ha1 : 1 ≤ a := Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have ha3 : a^3 = (n : ℝ)^2 := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hnR.le (2/3 : ℝ) 3]
    norm_num [Real.rpow_natCast]
  have cubeRoot (x : ℕ) : (((x : ℝ)^3)^(1/3 : ℝ)) = x := by
    rw [← Real.rpow_natCast_mul (by positivity) 3]
    norm_num
  have nRoot : (((n : ℝ)^2)^(1/3 : ℝ)) = a := by
    rw [← Real.rpow_natCast_mul (by positivity) 2]
    norm_num [a]
  have har : a ≤ (r : ℝ) := by
    have hb : (n : ℝ)^2 ≤ (r : ℝ)^3 := by exact_mod_cast hl
    have hh := Real.rpow_le_rpow (by positivity) hb (show 0 ≤ (1/3 : ℝ) by norm_num)
    simpa only [cubeRoot, nRoot] using hh
  have hra : (r : ℝ) ≤ a+1 := by
    have hb : ((r-1 : ℕ) : ℝ)^3 ≤ (n : ℝ)^2 := by exact_mod_cast hu.le
    have hh := Real.rpow_le_rpow (by positivity) hb (show 0 ≤ (1/3 : ℝ) by norm_num)
    rw [cubeRoot, nRoot, Nat.cast_sub hr] at hh
    norm_num only [Nat.cast_one] at hh
    linarith
  let d : ℝ := ((n/r : ℕ) : ℝ)
  let s : ℝ := (Nat.sqrt r : ℝ)
  have hd : 0 ≤ d := by positivity
  have hs : 0 ≤ s := by positivity
  have hrR : 0 ≤ (r : ℝ) := by positivity
  have hdr : d*(r : ℝ) ≤ n := by dsimp [d]; exact_mod_cast Nat.div_mul_le_self n r
  have hs2 : s^2 ≤ (r : ℝ) := by dsimp [s]; exact_mod_cast Nat.sqrt_le' r
  have hdr2 := pow_le_pow_left₀ (mul_nonneg hd hrR) hdr 2
  have hprod := mul_le_mul_of_nonneg_left hs2 (mul_nonneg (sq_nonneg d) hrR)
  have hdsr : (d*s)^2 * (r : ℝ) ≤ (n : ℝ)^2 := by nlinarith [hprod]
  have hdsa := mul_le_mul_of_nonneg_left har (sq_nonneg (d*s))
  have hds2 : (d*s)^2 ≤ a^2 := by
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith [hdsr, hdsa, ha3]
  have hds : d*s ≤ a := (sq_le_sq₀ (mul_nonneg hd hs) ha.le).mp hds2
  have hsum : ((r+(n/r)*Nat.sqrt r : ℕ) : ℝ) ≤ 3*a := by
    push_cast
    change (r : ℝ) + d*s ≤ 3*a
    linarith
  let L : ℝ := ((Nat.log 2 n+2 : ℕ) : ℝ)
  have hlogN : Nat.log 2 (n+1)+2 ≤ Nat.log 2 n+3 := by
    have hh := Nat.log_mono_right (b := 2) (show n+1 ≤ n*2 by omega)
    rw [Nat.log_mul_base (by decide) hn.ne'] at hh
    omega
  have hlog : ((Nat.log 2 (n+1)+2 : ℕ) : ℝ) ≤ L+1 := by
    dsimp [L]; norm_cast
  have hL : 3 ≤ L := by
    have hh : 1 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) hn.ne').mpr (by omega)
    dsimp [L]; norm_cast; omega
  have hcoef : 3*(L+1)+2 ≤ 2*L^2 := by nlinarith
  have hκR : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hκa : 1 ≤ (κ : ℝ)*a := by nlinarith
  have htotal := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (κ : ℝ)*a by positivity)
  have hqR : (q : ℝ) ≤ (κ : ℝ)*((Nat.log 2 (n+1)+2 : ℕ) : ℝ)*
      ((r+(n/r)*Nat.sqrt r : ℕ) : ℝ)+2 := by exact_mod_cast hq
  have hprod' := mul_le_mul hlog hsum (by positivity) (by linarith : 0 ≤ L+1)
  have hcharge := mul_le_mul_of_nonneg_left hprod' (show 0 ≤ (κ : ℝ) by positivity)
  have hfinal : (q : ℝ) ≤ 2*(κ : ℝ)*L^2*a := by nlinarith [hqR, hcharge, htotal]
  simpa only [L, a, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow] using hfinal

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
