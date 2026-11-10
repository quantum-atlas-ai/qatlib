/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.Proposition6GeneratedInclusion
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.GroupTheory.OrderOfElement
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p r : ℕ}

theorem exists_zpowers_pow_of_le_zpowers {G : Type*} [Group G] (z : G) {N : ℕ} (hN : 0 < N)
    (hzN : orderOf z = N) (H : Subgroup G) (hH : H ≤ Subgroup.zpowers z) :
    ∃ d : ℕ, 0 < d ∧ d ∣ N ∧ H = Subgroup.zpowers (z ^ d) := by
  classical
  have hzN1 : z ^ N = 1 := by rw [← hzN]; exact pow_orderOf_eq_one z
  have hex : ∃ k : ℕ, 0 < k ∧ z ^ k ∈ H := ⟨N, hN, by rw [hzN1]; exact H.one_mem⟩
  set d := Nat.find hex with hd
  have hdpos : 0 < d := (Nat.find_spec hex).1
  have hdmem : z ^ d ∈ H := (Nat.find_spec hex).2
  have hdmin : ∀ k : ℕ, 0 < k → z ^ k ∈ H → d ≤ k :=
    fun k hk hkm => Nat.find_min' hex ⟨hk, hkm⟩
  have hdvd : d ∣ N := by
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases Nat.eq_zero_or_pos (N % d) with h0 | hpos
    · exact h0
    · exfalso
      have hEq : (z ^ d) ^ (N / d) * z ^ (N % d) = z ^ N := by
        rw [← pow_mul, ← pow_add]
        congr 1
        exact Nat.div_add_mod N d
      have h1 : (z ^ d) ^ (N / d) * z ^ (N % d) = 1 := by rw [hEq, hzN1]
      have hA : (z ^ d) ^ (N / d) ∈ H := Subgroup.pow_mem H hdmem _
      have hB : z ^ (N % d) = ((z ^ d) ^ (N / d))⁻¹ :=
        (inv_eq_of_mul_eq_one_right h1).symm
      have hmem : z ^ (N % d) ∈ H := by rw [hB]; exact Subgroup.inv_mem H hA
      have hle := hdmin (N % d) hpos hmem
      have hlt := Nat.mod_lt N hdpos
      omega
  refine ⟨d, hdpos, hdvd, le_antisymm ?_ ?_⟩
  · intro h hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hH hh)
    set q : ℤ := m / (d : ℤ) with hq
    set rr : ℤ := m % (d : ℤ) with hrr
    have hdm : (d : ℤ) * q + rr = m := by
      rw [hq, hrr]
      exact Int.mul_ediv_add_emod m (d : ℤ)
    have hdecomp : z ^ m = (z ^ d) ^ q * z ^ rr := by
      rw [← hdm, zpow_add, zpow_mul, zpow_natCast]
    have hzrr : z ^ rr = ((z ^ d) ^ q)⁻¹ * h := by
      have h2 : (z ^ d) ^ q * z ^ rr = h := by rw [← hdecomp, hm]
      calc z ^ rr = ((z ^ d) ^ q)⁻¹ * ((z ^ d) ^ q * z ^ rr) := by
            rw [inv_mul_cancel_left]
        _ = ((z ^ d) ^ q)⁻¹ * h := by rw [h2]
    have hrr0 : rr = 0 := by
      have hnn : (0 : ℤ) ≤ rr := Int.emod_nonneg m (by exact_mod_cast hdpos.ne')
      have hlt : rr < (d : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hdpos)
      rcases eq_or_ne rr 0 with h | hne
      · exact h
      · exfalso
        have hpos : 0 < rr := lt_of_le_of_ne hnn (Ne.symm hne)
        have htoNat : ((rr.toNat : ℕ) : ℤ) = rr := Int.toNat_of_nonneg hnn
        have hmem : z ^ rr.toNat ∈ H := by
          rw [← zpow_natCast, htoNat, hzrr]
          exact Subgroup.mul_mem H
            (Subgroup.inv_mem H (Subgroup.zpow_mem H hdmem q)) hh
        have hposNat : 0 < rr.toNat := by omega
        have hle := hdmin rr.toNat hposNat hmem
        have hlt' : rr.toNat < d := by omega
        omega
    refine ⟨q, ?_⟩
    have h1 : 1 = ((z ^ d) ^ q)⁻¹ * h := by rw [← hzrr, hrr0, zpow_zero]
    calc (z ^ d) ^ q = (z ^ d) ^ q * 1 := (mul_one _).symm
      _ = (z ^ d) ^ q * (((z ^ d) ^ q)⁻¹ * h) := by rw [h1]
      _ = h := by rw [mul_inv_cancel_left]
  · rw [Subgroup.zpowers_le]
    exact hdmem

theorem dvd_two_mul_prime_pow (hp : p.Prime) {d : ℕ} (hdpos : 0 < d)
    (hd : d ∣ 2 * p ^ r) :
    ∃ t s : ℕ, t ≤ 1 ∧ s ≤ r ∧ d = 2 ^ t * p ^ s := by
  by_cases h2 : 2 ∣ d
  · obtain ⟨d', rfl⟩ := h2
    have hd' : d' ∣ p ^ r := by
      obtain ⟨k, hk⟩ := hd
      refine ⟨k, ?_⟩
      have hEq : 2 * p ^ r = 2 * (d' * k) := by rw [hk]; ring
      exact Nat.mul_left_cancel (by norm_num) hEq
    obtain ⟨s, hsle, hs⟩ := (Nat.dvd_prime_pow hp).mp hd'
    exact ⟨1, s, by omega, hsle, by rw [hs, pow_one]⟩
  · have hcop : Nat.Coprime d 2 :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr h2).symm
    have hdp : d ∣ p ^ r :=
      hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hd)
    obtain ⟨s, hsle, hs⟩ := (Nat.dvd_prime_pow hp).mp hdp
    exact ⟨0, s, by omega, hsle, by rw [hs, pow_zero, one_mul]⟩

theorem element_eq_genX_pow_mul_genY
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    [NeZero p] [NeZero (2 * p ^ r)] (g : SDP p r φ) :
    g = genX p r φ ^ (ZMod.val g.left.toAdd) * genY p r φ ^ (ZMod.val g.right.toAdd) := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  rw [genX_pow, genY_pow]
  refine SemidirectProduct.ext ?_ ?_ <;> simp

theorem exists_y_part (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    {H : Subgroup (SDP p r φ)} {a b : ℕ} (_ha : a ≤ 2 * p ^ r - 1) (hb0 : b ≠ 0)
    (hb : b ≤ p - 1) (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    (hgen : genX p r φ ^ a * genY p r φ ^ b ∈ H) :
    ∃ c : ℕ, genX p r φ ^ c * genY p r φ ∈ H := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hbne : (b : ZMod p) ≠ 0 := by
    intro h
    have hpdvd : p ∣ b := (ZMod.natCast_eq_zero_iff b p).mp h
    have hle' := Nat.le_of_dvd (by omega) hpdvd
    omega
  have hbcop : Nat.Coprime b p := by
    have hnp : ¬ p ∣ b := by
      intro hdiv
      have hle' := Nat.le_of_dvd (by omega) hdiv
      omega
    exact ((hp.coprime_iff_not_dvd).mpr hnp).symm
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime b hbcop with hu
  have hu_coe : ((u : ZMod p)) = (b : ZMod p) := ZMod.coe_unitOfCoprime b hbcop
  set i : ℕ := ZMod.val (((u⁻¹ : (ZMod p)ˣ) : ZMod p)) with hi
  have hi_coe : ((i : ℕ) : ZMod p) = ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    rw [hi]; exact ZMod.natCast_zmod_val _
  have hib : ((b * i : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, hi_coe, ← hu_coe]
    exact Units.mul_inv u
  have hi_pos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso
      have hb1 : ((b * i : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using hib
      rw [h0, Nat.mul_zero] at hb1
      have hzero : ((1 : ℕ) : ZMod p) = 0 := by simpa using hb1.symm
      have hpdvd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp hzero
      have hle' := Nat.le_of_dvd (by norm_num) hpdvd
      omega
    · exact hpos
  refine ⟨a * i * ((i - 1) * b * p ^ (r - 1) + 1), ?_⟩
  have hpow : (genX p r φ ^ a * genY p r φ ^ b) ^ i =
      genX p r φ ^ (a * i * ((i - 1) * b * p ^ (r - 1) + 1)) *
        genY p r φ ^ (b * i) :=
    pow_genX_mul_genY hp hr φ hφ a b i
  have hy1 : genY p r φ ^ (b * i) = genY p r φ := by
    rw [genY_pow, hib]
    rfl
  have hmem : (genX p r φ ^ a * genY p r φ ^ b) ^ i ∈ H := Subgroup.pow_mem H hgen i
  rw [hpow, hy1] at hmem
  exact hmem

theorem le_closure_of_data {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr)
    [NeZero p] [NeZero (2 * p ^ r)]
    {H : Subgroup (SDP p r φ)} {t s h : ℕ}
    (ht : t ≤ 1) (hsr : s ≤ r) (hh : h ≤ p - 1) (hs0 : s = 0 → h = 0)
    (hHe : genX p r φ ^ (2 ^ t * p ^ s) ∈ H)
    (hHy : genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ ∈ H)
    (hHx : H ⊓ Subgroup.zpowers (genX p r φ) =
      Subgroup.zpowers (genX p r φ ^ (2 ^ t * p ^ s))) :
    H ≤ Subgroup.closure
      ({genX p r φ ^ (2 ^ t * p ^ s),
        genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ} : Set (SDP p r φ)) := by
  intro g hg
  set a := ZMod.val g.left.toAdd with ha
  set b := ZMod.val g.right.toAdd with hb
  have hgdec : g = genX p r φ ^ a * genY p r φ ^ b := by
    rw [ha, hb]; exact element_eq_genX_pow_mul_genY φ g
  have hb_le : b ≤ p - 1 := by
    have := ZMod.val_lt g.right.toAdd
    omega
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · have hgx : genX p r φ ^ a ∈ H := by
      rw [hgdec, hb0, pow_zero, mul_one] at hg
      exact hg
    have hmem : genX p r φ ^ a ∈
        Subgroup.zpowers (genX p r φ ^ (2 ^ t * p ^ s)) := by
      have h1 : genX p r φ ^ a ∈ H ⊓ Subgroup.zpowers (genX p r φ) :=
        Subgroup.mem_inf.mpr ⟨hgx, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) a⟩
      rwa [hHx] at h1
    rw [hgdec, hb0, pow_zero, mul_one]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hmem
  · set ee : ℕ := (b * h % p) * 2 ^ t * p ^ (s - 1) with hee
    have hE : genX p r φ ^ ee * genY p r φ ^ b ∈
        Subgroup.closure
          ({genX p r φ ^ (2 ^ t * p ^ s),
            genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ} :
              Set (SDP p r φ)) :=
      proposition6_generated_inclusion hp hr φ hφ ht hsr hh hs0 (b := b) hb_le
    have hEcl : Subgroup.closure
        ({genX p r φ ^ (2 ^ t * p ^ s),
          genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ} :
            Set (SDP p r φ)) ≤ H := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hHe
      · exact hHy
    have hEH : genX p r φ ^ ee * genY p r φ ^ b ∈ H := hEcl hE
    have hdiff : g * (genX p r φ ^ ee * genY p r φ ^ b)⁻¹ =
        genX p r φ ^ a * (genX p r φ ^ ee)⁻¹ := by
      rw [hgdec]; group
    have hdiffH : genX p r φ ^ a * (genX p r φ ^ ee)⁻¹ ∈ H := by
      rw [← hdiff]
      exact Subgroup.mul_mem H hg (Subgroup.inv_mem H hEH)
    have hdiffZp : genX p r φ ^ a * (genX p r φ ^ ee)⁻¹ ∈
        Subgroup.zpowers (genX p r φ ^ (2 ^ t * p ^ s)) := by
      have h1 : genX p r φ ^ a * (genX p r φ ^ ee)⁻¹ ∈
          Subgroup.zpowers (genX p r φ) := by
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨(a : ℤ) - (ee : ℤ), ?_⟩
        rw [zpow_sub, zpow_natCast, zpow_natCast]
      have h2 : genX p r φ ^ a * (genX p r φ ^ ee)⁻¹ ∈
          H ⊓ Subgroup.zpowers (genX p r φ) := Subgroup.mem_inf.mpr ⟨hdiffH, h1⟩
      rwa [hHx] at h2
    have hmem : genX p r φ ^ a * (genX p r φ ^ ee)⁻¹ ∈
        Subgroup.closure
          ({genX p r φ ^ (2 ^ t * p ^ s),
            genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ} :
              Set (SDP p r φ)) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hdiffZp
    have hg_eq : g = (genX p r φ ^ a * (genX p r φ ^ ee)⁻¹) *
        (genX p r φ ^ ee * genY p r φ ^ b) := by
      rw [← hdiff]; group
    rw [hg_eq]
    exact Subgroup.mul_mem _ hmem hE

theorem proposition5_subgroup_classification
    {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hodd : p ≠ 2)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr) :
    ∀ H : Subgroup (SDP p r φ),
      ∃ t s h : ℕ, t ≤ 1 ∧ s ≤ r ∧ h ≤ p - 1 ∧ (s = 0 → h = 0) ∧
        (H = Subgroup.zpowers (genX p r φ ^ (2 ^ t * p ^ s)) ∨
          H = Subgroup.closure
            ({genX p r φ ^ (2 ^ t * p ^ s),
              genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ} :
              Set (SDP p r φ))) := by
  classical
  intro H
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (2 * p ^ r) :=
    ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero)⟩
  have hNpos : 0 < 2 * p ^ r := Nat.mul_pos (by norm_num) (pow_pos hp.pos r)
  set x : SDP p r φ := genX p r φ with hx
  set y : SDP p r φ := genY p r φ with hy
  set Hx : Subgroup (SDP p r φ) := H ⊓ Subgroup.zpowers x with hHx
  have hxN : orderOf x = 2 * p ^ r := by rw [hx]; exact orderOf_genX hp hr φ
  obtain ⟨d, hdpos, hddvd, hHxeq⟩ :=
    exists_zpowers_pow_of_le_zpowers x hNpos hxN Hx inf_le_right
  obtain ⟨t, s, ht, hs, hdeq⟩ := dvd_two_mul_prime_pow hp hdpos hddvd
  have hde : x ^ d = x ^ (2 ^ t * p ^ s) := by rw [hdeq]
  have hHxG : H ⊓ Subgroup.zpowers (genX p r φ) =
      Subgroup.zpowers (genX p r φ ^ (2 ^ t * p ^ s)) := by
    rw [← hx, ← hHx, hHxeq, hde]
  have hHe : genX p r φ ^ (2 ^ t * p ^ s) ∈ H := by
    have h1 : genX p r φ ^ (2 ^ t * p ^ s) ∈
        H ⊓ Subgroup.zpowers (genX p r φ) := by
      rw [hHxG]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.mem_inf.mp h1).1
  by_cases hle : H ≤ Subgroup.zpowers x
  · refine ⟨t, s, 0, ht, hs, Nat.zero_le _, fun _ => rfl, Or.inl ?_⟩
    have hHeq : Hx = H := by rw [hHx]; exact inf_eq_left.mpr hle
    rw [← hHeq, hHxeq, hde, hx]
  · obtain ⟨g, hgH, hgnot⟩ := Set.not_subset.mp hle
    set a := ZMod.val g.left.toAdd with ha
    set b := ZMod.val g.right.toAdd with hb
    have hgdec : g = x ^ a * y ^ b := by
      rw [ha, hb, hx, hy]; exact element_eq_genX_pow_mul_genY φ g
    have hb_ne : b ≠ 0 := by
      intro hb0
      apply hgnot
      rw [hgdec, hb0, pow_zero, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) a
    have hb_le : b ≤ p - 1 := by
      have := ZMod.val_lt g.right.toAdd
      omega
    have ha_le : a ≤ 2 * p ^ r - 1 := by
      have := ZMod.val_lt g.left.toAdd
      omega
    have hgen : genX p r φ ^ a * genY p r φ ^ b ∈ H := by
      rw [hgdec] at hgH
      simpa [hx, hy] using hgH
    obtain ⟨c, hxy⟩ := exists_y_part (H := H) (a := a) (b := b) hp hr φ ha_le hb_ne hb_le hφ hgen
    have hxp : x ^ (c * p) ∈ H := by
      have hpp : (x ^ c * y) ^ p = x ^ (c * p) := by
        rw [hx, hy]
        simpa using pow_p_eq hp hr hodd φ hφ c 1
      rw [← hpp]
      exact Subgroup.pow_mem H hxy p
    have hmem_e : x ^ (c * p) ∈ Subgroup.zpowers (x ^ (2 ^ t * p ^ s)) := by
      have h1 : x ^ (c * p) ∈ Hx := by
        rw [hHx]
        exact Subgroup.mem_inf.mpr
          ⟨hxp, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _⟩
      rw [← hde, ← hHxeq]
      exact h1
    have he_dvd_cp : (2 ^ t * p ^ s) ∣ c * p := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem_e
      have hm_z : x ^ (((2 ^ t * p ^ s : ℕ) : ℤ) * m) = x ^ (((c * p : ℕ)) : ℤ) := by
        rw [zpow_mul, zpow_natCast]
        exact hm
      have hz1 : x ^ ((((2 ^ t * p ^ s : ℕ) : ℤ) * m) - ((c * p : ℕ) : ℤ)) = 1 := by
        rw [sub_eq_add_neg, zpow_add, zpow_neg, hm_z]
        exact mul_inv_cancel _
      have hNdiv : (((2 * p ^ r : ℕ)) : ℤ) ∣
          ((((2 ^ t * p ^ s : ℕ) : ℤ) * m) - ((c * p : ℕ) : ℤ)) := by
        have h := orderOf_dvd_iff_zpow_eq_one.mpr hz1
        rwa [hxN] at h
      have hedvdN : (((2 ^ t * p ^ s : ℕ)) : ℤ) ∣ (((2 * p ^ r : ℕ)) : ℤ) := by
        have hn : (2 ^ t * p ^ s) ∣ (2 * p ^ r) := by rw [← hdeq]; exact hddvd
        exact_mod_cast hn
      have h1' : (((2 ^ t * p ^ s : ℕ)) : ℤ) ∣
          ((((2 ^ t * p ^ s : ℕ) : ℤ) * m) - ((c * p : ℕ) : ℤ)) :=
        dvd_trans hedvdN hNdiv
      have h2' : (((2 ^ t * p ^ s : ℕ)) : ℤ) ∣
          (((2 ^ t * p ^ s : ℕ) : ℤ) * m) := dvd_mul_right _ _
      have h3' : (((2 ^ t * p ^ s : ℕ)) : ℤ) ∣ (((c * p : ℕ)) : ℤ) := by
        have hsub := dvd_sub h2' h1'
        have heq : (((2 ^ t * p ^ s : ℕ) : ℤ) * m) -
            ((((2 ^ t * p ^ s : ℕ) : ℤ) * m) - ((c * p : ℕ) : ℤ)) =
            ((c * p : ℕ) : ℤ) := by ring
        rwa [heq] at hsub
      exact_mod_cast h3'
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · subst hs0
      have hdvd_c : 2 ^ t ∣ c := by
        have h : 2 ^ t ∣ c * p := by simpa only [pow_zero, mul_one] using he_dvd_cp
        have h2p : ¬ 2 ∣ p := by
          intro hdiv
          obtain ⟨k, hk⟩ := hdiv
          have hmod : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hodd
          omega
        have hcop : Nat.Coprime (2 ^ t) p :=
          Nat.Coprime.pow_left t ((Nat.prime_two.coprime_iff_not_dvd).mpr h2p)
        exact hcop.dvd_of_dvd_mul_right h
      have h2t : x ^ (2 ^ t) ∈ H := by
        rw [hx]
        have hpow0 : 2 ^ t * p ^ 0 = 2 ^ t := by rw [pow_zero, mul_one]
        rw [← hpow0]
        exact hHe
      have hxc : x ^ c ∈ H := by
        obtain ⟨k, hk⟩ := hdvd_c
        rw [hk, pow_mul]
        exact Subgroup.pow_mem H h2t k
      have hyH : y ∈ H := by
        have h1 : (x ^ c)⁻¹ * (x ^ c * y) ∈ H :=
          Subgroup.mul_mem H (Subgroup.inv_mem H hxc) hxy
        rwa [inv_mul_cancel_left] at h1
      have hHy' : genX p r φ ^ (0 * 2 ^ t * p ^ (0 - 1)) * genY p r φ ∈ H := by
        simp only [Nat.zero_mul, pow_zero, one_mul]
        exact hyH
      refine ⟨t, 0, 0, ht, by omega, Nat.zero_le _, fun _ => rfl, Or.inr ?_⟩
      refine le_antisymm ?_ ?_
      · exact le_closure_of_data hp hr φ hφ ht (by omega) (Nat.zero_le _)
          (fun _ => rfl) hHe hHy' hHxG
      · rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hHe
        · exact hHy'
    · have hps : p ^ s = p ^ (s - 1) * p := by
        rw [← pow_succ]
        congr 1
        omega
      set f : ℕ := 2 ^ t * p ^ (s - 1) with hf
      have hf_dvd_c : f ∣ c := by
        have hef : 2 ^ t * p ^ s = f * p := by rw [hf, hps]; ring
        have h := he_dvd_cp
        rw [hef] at h
        exact Nat.dvd_of_mul_dvd_mul_right hp.pos h
      set q : ℕ := c / f with hqdef
      have hc_eq : c = q * f := (Nat.div_mul_cancel hf_dvd_c).symm
      set h : ℕ := q % p with hhdef
      have hh_le : h ≤ p - 1 := by
        have hlt : h < p := by rw [hhdef]; exact Nat.mod_lt _ hp.pos
        omega
      set qq : ℕ := q / p with hqq
      have hq_eq : q = p * qq + h := by
        rw [hhdef, hqq]
        exact (Nat.div_add_mod q p).symm
      have hpf : p * f = 2 ^ t * p ^ s := by rw [hf, hps]; ring
      have hc_decomp : c = h * f + qq * (2 ^ t * p ^ s) := by
        rw [hc_eq, hq_eq, ← hpf]
        ring
      have hHy' : genX p r φ ^ (h * 2 ^ t * p ^ (s - 1)) * genY p r φ ∈ H := by
        have hfeq : h * 2 ^ t * p ^ (s - 1) = h * f := by rw [hf]; ring
        rw [hfeq]
        have hE : genX p r φ ^ ((2 ^ t * p ^ s) * qq) ∈ H := by
          rw [pow_mul]
          exact Subgroup.pow_mem H hHe qq
        have hpow : (genX p r φ ^ ((2 ^ t * p ^ s) * qq))⁻¹ * genX p r φ ^ c =
            genX p r φ ^ (h * f) := by
          have h1 : (genX p r φ ^ ((2 ^ t * p ^ s) * qq))⁻¹ =
              genX p r φ ^ (-((((2 ^ t * p ^ s) * qq : ℕ)) : ℤ)) := by
            rw [← zpow_natCast, zpow_neg]
          have h2 : genX p r φ ^ c = genX p r φ ^ ((c : ℕ) : ℤ) :=
            (zpow_natCast _ _).symm
          have h3 : genX p r φ ^ (h * f) = genX p r φ ^ (((h * f : ℕ)) : ℤ) :=
            (zpow_natCast _ _).symm
          rw [h1, h2, h3, ← zpow_add]
          congr 1
          rw [hc_decomp]
          push_cast
          ring
        have heq2 : genX p r φ ^ (h * f) * genY p r φ =
            (genX p r φ ^ ((2 ^ t * p ^ s) * qq))⁻¹ *
              (genX p r φ ^ c * genY p r φ) := by
          rw [← hpow, ← mul_assoc]
        rw [heq2]
        exact Subgroup.mul_mem H (Subgroup.inv_mem H hE) hxy
      refine ⟨t, s, h, ht, hs, hh_le, fun hzero => absurd hzero (by omega), Or.inr ?_⟩
      refine le_antisymm ?_ ?_
      · exact le_closure_of_data hp hr φ hφ ht hs hh_le
          (fun hzero => absurd hzero (by omega)) hHe hHy' hHxG
      · rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hHe
        · exact hHy'

end Qatlib.Papers.SemiDirectHSP06.MainResults
