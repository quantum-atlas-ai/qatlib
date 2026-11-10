/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.Spectral
import Mathlib.Order.Interval.Finset.Nat
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

def coordNat (n : ℕ) (m : Fin d → ZMod n) : Fin d → ℕ := fun j => (m j).valMinAbs.natAbs

def maxNorm (n : ℕ) (m : Fin d → ZMod n) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup (fun j => coordNat n m j)

theorem coordNat_le_maxNorm (n : ℕ) (m : Fin d → ZMod n) (j : Fin d) :
    coordNat n m j ≤ maxNorm n m :=
  Finset.le_sup (Finset.mem_univ j)

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

theorem maxNorm_le_n {n : ℕ} [NeZero n] [NeZero d] (m : Fin d → ZMod n) : maxNorm n m ≤ n := by
  have := maxNorm_le_half m
  omega

theorem maxNorm_pos_of_ne_zero {n : ℕ} [NeZero n] {m : Fin d → ZMod n} (hm : m ≠ 0) :
    1 ≤ maxNorm n m := by
  rcases Nat.eq_zero_or_pos (maxNorm n m) with h | h
  · exact absurd (maxNorm_eq_zero_iff m |>.mp h) hm
  · exact h

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

theorem waveVector_sq (n : ℕ) (m : Fin d → ZMod n) (j : Fin d) :
    (waveVector n m j) ^ 2
      = (4 * Real.pi ^ 2 / (n : ℝ) ^ 2) * ((coordNat n m j : ℕ) : ℝ) ^ 2 := by
  unfold waveVector coordNat
  have hc : ((m j).valMinAbs.natAbs : ℝ) = |((m j).valMinAbs : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hc, sq_abs]
  field_simp
  ring

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

def gfun (s : ℕ) : ℝ := ((s : ℝ))⁻¹ ^ 2

def dfun (s : ℕ) : ℝ := gfun s - gfun (s + 1)

theorem gfun_nonneg (s : ℕ) : 0 ≤ gfun s := by unfold gfun; positivity

theorem gfun_eq (s : ℕ) : gfun s = 1 / (s : ℝ) ^ 2 := by
  unfold gfun
  rw [inv_pow, one_div]

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

theorem dfun_eq (s : ℕ) (hs : 1 ≤ s) :
    dfun s = (2 * (s : ℝ) + 1) / ((s : ℝ) ^ 2 * ((s : ℝ) + 1) ^ 2) := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have h1 : (0:ℝ) < (s:ℝ) + 1 := by linarith
  unfold dfun gfun
  rw [inv_pow, inv_pow]
  push_cast
  field_simp
  ring

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

theorem coord_add_nonneg (n s : ℕ) (m : Fin d → ZMod n) (hm : maxNorm n m ≤ s) (j : Fin d) :
    0 ≤ (m j).valMinAbs + (s : ℤ) := by
  have hc : ((m j).valMinAbs.natAbs : ℕ) ≤ s := le_trans (coordNat_le_maxNorm n m j) hm
  have hc' : ((m j).valMinAbs.natAbs : ℤ) ≤ (s : ℤ) := by exact_mod_cast hc
  have habs : |(m j).valMinAbs| ≤ (s : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact hc'
  have := (abs_le.mp habs).1
  linarith

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
