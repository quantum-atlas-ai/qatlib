/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.Spectral
import Mathlib.Order.Interval.Finset.Nat

/-!
# Centered lattice coordinates and box counts

This module equips periodic lattice indices with absolute centered coordinates and a maximum
coordinate norm. It compares dispersion with this norm and bounds the number of lattice points
in a centered box, providing estimates for the lattice sums in [ChildsGoldstone2004].

It also defines reciprocal-square differences and proves their telescoping and decay bounds.

## Main statements

* `dispersion_ge_maxNorm_sq` and `inv_dispersion_le`: dispersion estimates in terms of the
  maximum coordinate norm.
* `telescope` and `dfun_le`: reciprocal-square telescoping and cubic decay.
* `card_le_box`: at most `(2 * s + 1) ^ d` lattice indices have maximum norm at most `s`.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

/-- The natural absolute values of the centered integer representatives of a periodic lattice
index. -/
def coordNat (n : ℕ) (m : Fin d → ZMod n) : Fin d → ℕ := fun j => (m j).valMinAbs.natAbs

/-- The maximum absolute centered coordinate of a periodic lattice index, with value zero when
there are no coordinates. -/
def maxNorm (n : ℕ) (m : Fin d → ZMod n) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup (fun j => coordNat n m j)

/-- Each absolute centered coordinate is bounded by the maximum coordinate norm. -/
theorem coordNat_le_maxNorm (n : ℕ) (m : Fin d → ZMod n) (j : Fin d) :
    coordNat n m j ≤ maxNorm n m :=
  Finset.le_sup (Finset.mem_univ j)

/-- For nonzero side length, the maximum coordinate norm vanishes exactly at the zero lattice
index. -/
theorem maxNorm_eq_zero_iff {n : ℕ} [NeZero n] (m : Fin d → ZMod n) :
    maxNorm n m = 0 ↔ m = 0 := by
  constructor
  · intro h
    funext j
    have hc : coordNat n m j = 0 := by
      have := coordNat_le_maxNorm n m j
      omega
    have hz : (m j).valMinAbs = 0 := by
      exact Int.natAbs_eq_zero.mp (by simpa [coordNat] using hc)
    exact (ZMod.valMinAbs_eq_zero (m j)).mp hz
  · intro h
    subst h
    show (Finset.univ.sup (fun j => coordNat n (0 : Fin d → ZMod n) j)) = 0
    apply (Finset.sup_eq_bot_iff (fun j => coordNat n (0 : Fin d → ZMod n) j) Finset.univ).mpr
    intro j _
    simp [coordNat]

/-- For nonzero side length and dimension, twice the maximum absolute centered coordinate is at
most the side length. -/
theorem maxNorm_le_half {n : ℕ} [NeZero n] [NeZero d] (m : Fin d → ZMod n) :
    2 * maxNorm n m ≤ n := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun j => coordNat n m j)
  have hmax : maxNorm n m = coordNat n m j := hj
  rw [hmax]
  have hc0 := (m j).natAbs_valMinAbs_le
  rw [Nat.le_div_iff_mul_le (by norm_num)] at hc0
  have hc : coordNat n m j * 2 ≤ n := hc0
  omega

/-- For nonzero side length and dimension, the maximum coordinate norm is at most the side
length. -/
theorem maxNorm_le_n {n : ℕ} [NeZero n] [NeZero d] (m : Fin d → ZMod n) : maxNorm n m ≤ n := by
  have := maxNorm_le_half m
  omega

/-- A nonzero lattice index has maximum coordinate norm at least one when the side length is
nonzero. -/
theorem maxNorm_pos_of_ne_zero {n : ℕ} [NeZero n] {m : Fin d → ZMod n} (hm : m ≠ 0) :
    1 ≤ maxNorm n m := by
  rcases Nat.eq_zero_or_pos (maxNorm n m) with h | h
  · exact absurd (maxNorm_eq_zero_iff m |>.mp h) hm
  · exact h

/-- In nonzero dimension, the square of the maximum coordinate norm is at most the sum of the
squared absolute centered coordinates. -/
theorem sq_maxNorm_le_sum [NeZero d] (n : ℕ) (m : Fin d → ZMod n) :
    ((maxNorm n m : ℝ)) ^ 2 ≤ ∑ j, ((coordNat n m j : ℕ) : ℝ) ^ 2 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    ⟨⟨0, hd⟩, Finset.mem_univ _⟩ (fun j => coordNat n m j)
  have hmem : j₀ ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ ((coordNat n m i : ℕ) : ℝ) ^ 2 := by
    intro i _; positivity
  have := Finset.single_le_sum (f := fun i => ((coordNat n m i : ℕ) : ℝ) ^ 2) hnonneg hmem
  have hmax : maxNorm n m = coordNat n m j₀ := hj₀
  rw [hmax]
  exact this

/-- The square of a wave-vector coordinate equals `4 * Real.pi ^ 2 / n ^ 2` times the square of
its absolute centered lattice coordinate. -/
theorem waveVector_sq (n : ℕ) (m : Fin d → ZMod n) (j : Fin d) :
    (waveVector n m j) ^ 2
      = (4 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ((coordNat n m j : ℕ) : ℝ) ^ 2 := by
  unfold waveVector coordNat
  have hc : ((m j).valMinAbs.natAbs : ℝ) = |((m j).valMinAbs : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hc, sq_abs]
  field_simp
  ring

/-- For positive side length and nonzero dimension, the dispersion at a lattice wave vector is
at least `16 / n ^ 2` times the square of the maximum coordinate norm. -/
theorem dispersion_ge_maxNorm_sq {n : ℕ} [NeZero d] (hn : 0 < n) (m : Fin d → ZMod n) :
    (16 / (n : ℝ) ^ 2) * ((maxNorm n m : ℝ)) ^ 2 ≤ dispersion (waveVector n m) := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hbase : (4 / Real.pi ^ 2) * ∑ j, (waveVector n m j) ^ 2
      ≤ dispersion (waveVector n m) :=
    dispersion_ge_sum_sq _ (fun j => abs_waveVector_le_pi hn m j)
  have hsum : (4 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ∑ j, ((coordNat n m j : ℕ) : ℝ) ^ 2
      = ∑ j, (waveVector n m j) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => (waveVector_sq n m j).symm)
  have hmin : ((maxNorm n m : ℝ)) ^ 2 ≤ ∑ j, ((coordNat n m j : ℕ) : ℝ) ^ 2 :=
    sq_maxNorm_le_sum n m
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hcoef : (0:ℝ) < 4 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by positivity
  have h1 : (16 / (n : ℝ) ^ 2) * ((maxNorm n m : ℝ)) ^ 2
      = (4 / Real.pi ^ 2) * ((4 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ((maxNorm n m : ℝ)) ^ 2) := by
    field_simp
    ring
  rw [h1]
  calc (4 / Real.pi ^ 2) * ((4 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ((maxNorm n m : ℝ)) ^ 2)
      ≤ (4 / Real.pi ^ 2) * ((4 * Real.pi ^ 2 / (n : ℝ) ^ 2) *
          ∑ j, ((coordNat n m j : ℕ) : ℝ) ^ 2) := by
        gcongr
    _ = (4 / Real.pi ^ 2) * ∑ j, (waveVector n m j) ^ 2 := by rw [hsum]
    _ ≤ dispersion (waveVector n m) := hbase

/-- At a nonzero lattice index with positive side length and nonzero dimension, the inverse
dispersion is at most `n ^ 2 / (16 * maxNorm n m ^ 2)`. -/
theorem inv_dispersion_le {n : ℕ} [NeZero d] (hn : 0 < n) {m : Fin d → ZMod n} (hm : m ≠ 0) :
    (dispersion (waveVector n m))⁻¹
      ≤ (n : ℝ) ^ 2 / (16 * ((maxNorm n m : ℝ)) ^ 2) := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hr : (1:ℝ) ≤ (maxNorm n m : ℝ) := by exact_mod_cast maxNorm_pos_of_ne_zero hm
  have hrpos : (0:ℝ) < (maxNorm n m : ℝ) := by linarith
  have hkey : (0:ℝ) < 16 / (n : ℝ) ^ 2 * ((maxNorm n m : ℝ)) ^ 2 := by positivity
  have hle := dispersion_ge_maxNorm_sq (d := d) hn m
  have hle' : 16 / (n : ℝ) ^ 2 * ((maxNorm n m : ℝ)) ^ 2 ≤ dispersion (waveVector n m) := hle
  have := inv_anti₀ hkey hle'
  have heq : (16 / (n : ℝ) ^ 2 * ((maxNorm n m : ℝ)) ^ 2)⁻¹
      = (n : ℝ) ^ 2 / (16 * ((maxNorm n m : ℝ)) ^ 2) := by
    field_simp
  rwa [heq] at this

/-- The square of the real reciprocal of a natural index, using the totalized reciprocal at
zero. -/
def gfun (s : ℕ) : ℝ := ((s : ℝ))⁻¹ ^ 2

/-- The difference between consecutive values of the reciprocal-square function `gfun`. -/
def dfun (s : ℕ) : ℝ := gfun s - gfun (s + 1)

/-- The reciprocal-square function `gfun` is nonnegative at every natural index. -/
theorem gfun_nonneg (s : ℕ) : 0 ≤ gfun s := by unfold gfun; positivity

/-- The value of `gfun s` is `1 / (s : ℝ) ^ 2`. -/
theorem gfun_eq (s : ℕ) : gfun s = 1 / (s : ℝ) ^ 2 := by
  unfold gfun
  rw [inv_pow, one_div]

/-- For `r ≤ n`, summing `dfun` over the inclusive interval from `r` to `n` gives `gfun r - gfun
(n + 1)`. -/
theorem telescope {r n : ℕ} (hrn : r ≤ n) :
    ∑ s ∈ Finset.Icc r n, dfun s = gfun r - gfun (n + 1) := by
  have h := Finset.sum_Icc_sub (f := gfun) hrn
  calc ∑ s ∈ Finset.Icc r n, dfun s
      = ∑ s ∈ Finset.Icc r n, (-(gfun (s + 1) - gfun s)) := by
        refine Finset.sum_congr rfl ?_
        intro s _
        unfold dfun
        ring
    _ = -(∑ s ∈ Finset.Icc r n, (gfun (s + 1) - gfun s)) := by
        rw [Finset.sum_neg_distrib]
    _ = -(gfun (n + 1) - gfun r) := by rw [h]
    _ = gfun r - gfun (n + 1) := by ring

/-- For `s ≥ 1`, the consecutive reciprocal-square difference is `(2 * s + 1) / (s ^ 2 * (s + 1)
^ 2)` over the reals. -/
theorem dfun_eq (s : ℕ) (hs : 1 ≤ s) :
    dfun s = (2 * (s : ℝ) + 1) / ((s : ℝ) ^ 2 * ((s : ℝ) + 1) ^ 2) := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have h1 : (0:ℝ) < (s:ℝ) + 1 := by linarith
  unfold dfun gfun
  rw [inv_pow, inv_pow]
  push_cast
  field_simp
  ring

/-- For `s ≥ 1`, the reciprocal-square difference `dfun s` is at most `3 / (s : ℝ) ^ 3`. -/
theorem dfun_le (s : ℕ) (hs : 1 ≤ s) : dfun s ≤ 3 / (s : ℝ) ^ 3 := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have h1 : (0:ℝ) < (s:ℝ) + 1 := by linarith
  rw [dfun_eq s hs]
  have hp1 : (0:ℝ) < (s:ℝ) ^ 2 * ((s:ℝ) + 1) ^ 2 := by positivity
  have hp2 : (0:ℝ) < (s:ℝ) ^ 2 * (s:ℝ) ^ 2 := by positivity
  have hden : (s:ℝ) ^ 2 * (s:ℝ) ^ 2 ≤ (s:ℝ) ^ 2 * ((s:ℝ) + 1) ^ 2 := by
    gcongr
    linarith
  calc (2 * (s : ℝ) + 1) / ((s : ℝ) ^ 2 * ((s : ℝ) + 1) ^ 2)
      ≤ (3 * (s : ℝ)) / ((s : ℝ) ^ 2 * ((s : ℝ) + 1) ^ 2) := by
        exact div_le_div₀ (by positivity) (by linarith) hp1 (le_refl _)
    _ ≤ (3 * (s : ℝ)) / ((s : ℝ) ^ 2 * (s : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_left (by positivity) hp2 hden
    _ = 3 / (s : ℝ) ^ 3 := by
        field_simp

/-- If a lattice index has maximum coordinate norm at most `s`, adding `s` to any centered
integer coordinate gives a nonnegative integer. -/
theorem coord_add_nonneg (n s : ℕ) (m : Fin d → ZMod n) (hm : maxNorm n m ≤ s) (j : Fin d) :
    0 ≤ (m j).valMinAbs + (s : ℤ) := by
  have hc : ((m j).valMinAbs.natAbs : ℕ) ≤ s := le_trans (coordNat_le_maxNorm n m j) hm
  have hc' : ((m j).valMinAbs.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hc
  have habs : |(m j).valMinAbs| ≤ (s : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact hc'
  have := (abs_le.mp habs).1
  linarith

/-- Encode a centered coordinate shifted by `s` as an element of `Fin (2 * s + 1)` when the
maximum norm is at most `s`, and return zero otherwise. -/
def finOfCoord (n s : ℕ) (m : Fin d → ZMod n) (j : Fin d) : Fin (2 * s + 1) :=
  if h : maxNorm n m ≤ s then
    ⟨((m j).valMinAbs + (s : ℤ)).toNat, by
      have hc : ((m j).valMinAbs.natAbs : ℕ) ≤ s := le_trans (coordNat_le_maxNorm n m j) h
      have hc' : ((m j).valMinAbs.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hc
      have habs : |(m j).valMinAbs| ≤ (s : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact hc'
      have hup : (m j).valMinAbs + (s : ℤ) ≤ 2 * (s : ℤ) := by
        have := (abs_le.mp habs).2
        linarith
      have ht : ((m j).valMinAbs + (s : ℤ)).toNat ≤ 2 * s := by
        have h2 : ((m j).valMinAbs + (s : ℤ)).toNat ≤ (2 * (s:ℤ)).toNat :=
          Int.toNat_le_toNat hup
        simpa using h2
      omega⟩
  else 0

/-- Two lattice indices of maximum norm at most `s` are equal if their `finOfCoord` encodings
agree at every coordinate. -/
theorem finOfCoord_injOn (n s : ℕ) {x y : Fin d → ZMod n}
    (hx : maxNorm n x ≤ s) (hy : maxNorm n y ≤ s)
    (hxy : (fun j : Fin d => finOfCoord n s x j) = (fun j : Fin d => finOfCoord n s y j)) :
    x = y := by
  have hx' : maxNorm n x ≤ s := hx
  have hy' : maxNorm n y ≤ s := hy
  funext j
  have hval : ((x j).valMinAbs + (s : ℤ)).toNat = ((y j).valMinAbs + (s : ℤ)).toNat := by
    have hcongr' : finOfCoord n s x j = finOfCoord n s y j := congrFun hxy j
    have hxr : finOfCoord n s x j = ⟨((x j).valMinAbs + (s : ℤ)).toNat, by
        have hc : ((x j).valMinAbs.natAbs : ℕ) ≤ s := le_trans (coordNat_le_maxNorm n x j) hx'
        have hc' : ((x j).valMinAbs.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hc
        have habs : |(x j).valMinAbs| ≤ (s : ℤ) := by rw [Int.abs_eq_natAbs]; exact hc'
        have hup : (x j).valMinAbs + (s : ℤ) ≤ 2 * (s : ℤ) := by
          have := (abs_le.mp habs).2; linarith
        have ht : ((x j).valMinAbs + (s : ℤ)).toNat ≤ 2 * s := by
          have h2 : ((x j).valMinAbs + (s : ℤ)).toNat ≤ (2 * (s:ℤ)).toNat :=
            Int.toNat_le_toNat hup
          simpa using h2
        omega⟩ := by
      unfold finOfCoord
      rw [dif_pos hx']
    have hyr : finOfCoord n s y j = ⟨((y j).valMinAbs + (s : ℤ)).toNat, by
        have hc : ((y j).valMinAbs.natAbs : ℕ) ≤ s := le_trans (coordNat_le_maxNorm n y j) hy'
        have hc' : ((y j).valMinAbs.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hc
        have habs : |(y j).valMinAbs| ≤ (s : ℤ) := by rw [Int.abs_eq_natAbs]; exact hc'
        have hup : (y j).valMinAbs + (s : ℤ) ≤ 2 * (s : ℤ) := by
          have := (abs_le.mp habs).2; linarith
        have ht : ((y j).valMinAbs + (s : ℤ)).toNat ≤ 2 * s := by
          have h2 : ((y j).valMinAbs + (s : ℤ)).toNat ≤ (2 * (s:ℤ)).toNat :=
            Int.toNat_le_toNat hup
          simpa using h2
        omega⟩ := by
      unfold finOfCoord
      rw [dif_pos hy']
    rw [hxr, hyr] at hcongr'
    exact congrArg Fin.val hcongr'
  have hnx := coord_add_nonneg n s x hx' j
  have hny := coord_add_nonneg n s y hy' j
  have hint : (x j).valMinAbs + (s : ℤ) = (y j).valMinAbs + (s : ℤ) := by
    rw [← Int.toNat_of_nonneg hnx, ← Int.toNat_of_nonneg hny, hval]
  have : (x j).valMinAbs = (y j).valMinAbs := by linarith
  exact ZMod.valMinAbs_inj.mp this

/-- For nonzero side length, at most `(2 * s + 1) ^ d` periodic lattice indices have maximum
coordinate norm at most `s`. -/
theorem card_le_box {n : ℕ} [NeZero n] (s : ℕ) :
    (Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s)).card ≤ (2 * s + 1) ^ d := by
  have hmaps : Set.MapsTo (fun (m : Fin d → ZMod n) (j : Fin d) => finOfCoord n s m j)
      ↑(Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s))
      ↑(Finset.univ : Finset (Fin d → Fin (2 * s + 1))) := by
    intro m _
    exact Finset.mem_univ _
  have hinj : Set.InjOn (fun (m : Fin d → ZMod n) (j : Fin d) => finOfCoord n s m j)
      ↑(Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s)) := by
    intro x hx y hy hxy
    have hxf : maxNorm n x ≤ s := by
      have hmem : x ∈ Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s) := by
        simpa using hx
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    have hyf : maxNorm n y ≤ s := by
      have hmem : y ∈ Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s) := by
        simpa using hy
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    exact finOfCoord_injOn n s hxf hyf hxy
  have hle := Finset.card_le_card_of_injOn (fun (m : Fin d → ZMod n) (j : Fin d) => finOfCoord n s m j)
    hmaps hinj
  calc (Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s)).card
      ≤ (Finset.univ : Finset (Fin d → Fin (2 * s + 1))).card := hle
    _ = (2 * s + 1) ^ d := by simp

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
