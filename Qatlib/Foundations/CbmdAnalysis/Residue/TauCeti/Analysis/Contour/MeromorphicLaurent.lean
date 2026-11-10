/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Residue.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

def meromorphicPolarOrderAt (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  (-(meromorphicOrderAt f s).untop₀).toNat

theorem meromorphicPolarOrderAt_eq_of_order_eq {f : ℂ → ℂ} {s : ℂ}
    {n : ℤ} (h : meromorphicOrderAt f s = n) :
    meromorphicPolarOrderAt f s = (-n).toNat := by
  rw [meromorphicPolarOrderAt, h, WithTop.untop₀_coe]

theorem meromorphicPolarOrderAt_eq_one {f : ℂ → ℂ} {s : ℂ} (h : meromorphicOrderAt f s = -1) :
    meromorphicPolarOrderAt f s = 1 := by
  rw [meromorphicPolarOrderAt_eq_of_order_eq h]
  rfl

theorem neg_meromorphicPolarOrderAt_le (f : ℂ → ℂ) (s : ℂ) :
    (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
  rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [← WithTop.coe_untop₀_of_ne_top h]
    rw [show (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) =
        ((-(meromorphicPolarOrderAt f s : ℤ) : ℤ) : WithTop ℤ) by norm_cast,
      WithTop.coe_le_coe, meromorphicPolarOrderAt]
    omega

theorem meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos {f : ℂ → ℂ} {s : ℂ}
    (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicOrderAt f s = (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) := by
  rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
  · rw [meromorphicPolarOrderAt, h] at h_pos
    simp at h_pos
  · rw [← WithTop.coe_untop₀_of_ne_top h]
    rw [meromorphicPolarOrderAt] at h_pos ⊢
    norm_cast
    omega

theorem meromorphicOrderAt_lt_neg_one_of_one_lt_meromorphicPolarOrderAt {f : ℂ → ℂ} {s : ℂ}
    (h : 1 < meromorphicPolarOrderAt f s) :
    meromorphicOrderAt f s < (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos (by omega)]
  exact_mod_cast WithTop.coe_lt_coe.mpr (by omega)

@[simp]
theorem meromorphicPolarOrderAt_le_one_iff {f : ℂ → ℂ} {s : ℂ} :
    meromorphicPolarOrderAt f s ≤ 1 ↔
      ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
  constructor
  · intro h
    have hneg : (-1 : ℤ) ≤ -(meromorphicPolarOrderAt f s : ℤ) := by omega
    exact (WithTop.coe_le_coe.mpr hneg).trans (neg_meromorphicPolarOrderAt_le f s)
  · intro h
    by_contra hle
    have hlt : meromorphicOrderAt f s < ((-1 : ℤ) : WithTop ℤ) :=
      meromorphicOrderAt_lt_neg_one_of_one_lt_meromorphicPolarOrderAt (by omega)
    exact (not_lt_of_ge h) hlt

private theorem analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) (k : ℕ) :
    ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧
      ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => w + s) 0 := analyticAt_id.add analyticAt_const
  have hg0 : AnalyticAt ℂ (fun w => g (w + s)) 0 := by
    have := AnalyticAt.comp (f := fun w : ℂ => w + s) (x := (0 : ℂ)) (by simpa using hg) h1
    exact this
  obtain ⟨F, hF_an, hF_eq⟩ := hg0.exists_eventuallyEq_sum_add_pow_mul k
  have h2 : AnalyticAt ℂ (fun z : ℂ => z - s) s := analyticAt_id.sub analyticAt_const
  have hF_comp : AnalyticAt ℂ (fun z => F (z - s)) s := by
    have := AnalyticAt.comp (f := fun z : ℂ => z - s) (x := s) (by simpa using hF_an) h2
    exact this
  refine ⟨fun j => iteratedDeriv j.val (fun w => g (w + s)) 0 / j.val.factorial,
    fun z => F (z - s), hF_comp, ?_⟩
  have h_tend : Filter.Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
    simpa using (continuous_sub_right s).tendsto s
  filter_upwards [h_tend.eventually hF_eq] with z hz
  have hz' : g z = ∑ i ∈ Finset.range k,
      ((z - s) ^ i / (i.factorial : ℂ)) • iteratedDeriv i (fun w => g (w + s)) 0 +
        (z - s) ^ k • F (z - s) := by simpa using hz
  rw [hz', smul_eq_mul, mul_comm ((z - s) ^ k)]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => iteratedDeriv j (fun w => g (w + s)) 0 /
    (j.factorial : ℂ) * (z - s) ^ j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  ring

private theorem pow_div_pow_neg {w : ℂ} (hw : w ≠ 0) {k j : ℕ} (hjk : j < k) :
    w ^ j * (w ^ k)⁻¹ = (w ^ (k - j))⁻¹ := by
  have h_exp : (k - j) + j = k := by omega
  rw [show (w ^ k)⁻¹ = (w ^ ((k - j) + j))⁻¹ by rw [h_exp], pow_add]
  field_simp

private theorem reindex_sum_fin_neg {k : ℕ} (c : Fin k → ℂ) (w : ℂ) :
    (∑ j : Fin k, c j / w ^ (k - j.val)) =
      ∑ i : Fin k,
        c ⟨k - 1 - i.val, by have := i.isLt; omega⟩ / w ^ (i.val + 1) := by
  let σ : Fin k → Fin k := fun j => ⟨k - 1 - j.val, by have := j.isLt; omega⟩
  have hσ_invol : Function.Involutive σ := fun j => by
    ext
    have := j.isLt
    simp only [σ]
    omega
  have h_sum_eq : (∑ i : Fin k, c (σ i) / w ^ (k - (σ i).val)) =
      ∑ j : Fin k, c j / w ^ (k - j.val) :=
    Equiv.sum_comp ⟨σ, σ, hσ_invol.leftInverse, hσ_invol.rightInverse⟩
      (fun j => c j / w ^ (k - j.val))
  rw [← h_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [σ]
  omega

private theorem laurent_data_of_zpow_factor {f g₀ : ℂ → ℂ} {s : ℂ} (k : ℕ)
    (hg₀_an : AnalyticAt ℂ g₀ s) (hg₀_eq : ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(k : ℤ)) • g₀ z) :
    ∃ (a : Fin k → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ i : Fin k, a i / (z - s) ^ (i.val + 1) := by
  obtain ⟨c, R, hR_an, hR_eq⟩ := analyticAt_taylor_decomp hg₀_an k
  refine ⟨fun i : Fin k => c ⟨k - 1 - i.val, by have := i.isLt; omega⟩, R, hR_an, ?_⟩
  filter_upwards [hg₀_eq, nhdsWithin_le_nhds hR_eq, self_mem_nhdsWithin]
    with z hf_eq hR_eq_z hz_ne
  have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
  rw [hf_eq, hR_eq_z, smul_eq_mul, zpow_neg, zpow_natCast, mul_add]
  have h1 : ((z - s) ^ k)⁻¹ * ((z - s) ^ k * R z) = R z := by field_simp
  rw [h1, add_comm]
  congr 1
  rw [Finset.mul_sum, show ∑ j : Fin k, ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
      ∑ j : Fin k, c j / (z - s) ^ (k - j.val) from
    Finset.sum_congr rfl fun j _ => by
      rw [div_eq_mul_inv, show ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
          c j * ((z - s) ^ j.val * ((z - s) ^ k)⁻¹) by ring,
        pow_div_pow_neg hz_sub j.isLt]]
  exact reindex_sum_fin_neg c (z - s)

theorem exists_laurent_data_of_meromorphicAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ∃ (a : Fin (meromorphicPolarOrderAt f s) → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s,
        f z = g z + ∑ k : Fin (meromorphicPolarOrderAt f s), a k / (z - s) ^ (k.val + 1) := by
  obtain ⟨g₀, hg₀_an, hg₀_eq⟩ :=
    exists_analyticAt_eventuallyEq_zpow_smul hMero (neg_meromorphicPolarOrderAt_le f s)
  exact laurent_data_of_zpow_factor _ hg₀_an hg₀_eq

def meromorphicPolarCoeffAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (k : Fin (meromorphicPolarOrderAt f s)) : ℂ :=
  (exists_laurent_data_of_meromorphicAt hMero).choose k

def meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ k : Fin (meromorphicPolarOrderAt f s), meromorphicPolarCoeffAt hMero k / (z - s) ^ (k.val + 1)

def meromorphicAnalyticPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) : ℂ → ℂ :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose

theorem meromorphicAnalyticPartAt_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : AnalyticAt ℂ (meromorphicAnalyticPartAt hMero) s :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1

theorem eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∀ᶠ z in 𝓝[≠] s, f z = meromorphicAnalyticPartAt hMero z + meromorphicPolarPartAt hMero z :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2

theorem meromorphicPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) :
    meromorphicPolarPartAt hMero z =
      ∑ k : Fin (meromorphicPolarOrderAt f s),
        meromorphicPolarCoeffAt hMero k / (z - s) ^ (k.val + 1) := by
  unfold meromorphicPolarPartAt
  rfl

theorem meromorphicPolarPartAt_analyticAt_of_ne {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) :
    AnalyticAt ℂ (meromorphicPolarPartAt hMero) w := by
  unfold meromorphicPolarPartAt
  refine Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

theorem meromorphicPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have hres := residue_of_laurent_expansion
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2
  rw [dif_pos h_pos] at hres
  exact hres.symm

private theorem coeff_top_eq_zero_of_eventuallyEq {s : ℂ} {N : ℕ} {c : ℕ → ℂ}
    {g : ℂ → ℂ} (hg : ContinuousAt g s) (h_eq : ∀ᶠ z in 𝓝[≠] s,
      ∑ k ∈ Finset.range (N + 1), c k / (z - s) ^ (k + 1) = g z) :
    c N = 0 := by
  have h_mul : ∀ᶠ z in 𝓝[≠] s,
      ∑ k ∈ Finset.range (N + 1), c k * (z - s) ^ (N - k) = g z * (z - s) ^ (N + 1) := by
    filter_upwards [h_eq, self_mem_nhdsWithin] with z hz hz_ne
    have hw : z - s ≠ 0 := sub_ne_zero.mpr hz_ne
    rw [← hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkN : k + 1 ≤ N + 1 := Finset.mem_range.mp hk
    have h_sub : N + 1 - (k + 1) = N - k := by omega
    rw [div_mul_eq_mul_div, mul_div_assoc, div_eq_mul_inv ((z - s) ^ (N + 1)),
      ← pow_sub₀ (z - s) hw hkN, h_sub]
  have h_lhs : Tendsto (fun z => ∑ k ∈ Finset.range (N + 1), c k * (z - s) ^ (N - k))
      (𝓝[≠] s) (𝓝 (c N)) := by
    have h_cont : Tendsto (fun z => ∑ k ∈ Finset.range (N + 1), c k * (z - s) ^ (N - k))
        (𝓝 s) (𝓝 (∑ k ∈ Finset.range (N + 1), c k * ((s : ℂ) - s) ^ (N - k))) :=
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_id.sub continuous_const).pow _)).tendsto s
    have h_eval : ∑ k ∈ Finset.range (N + 1), c k * ((s : ℂ) - s) ^ (N - k) = c N := by
      rw [sub_self, Finset.sum_eq_single N
        (fun k hk hne => by
          rw [zero_pow (by
            have := Finset.mem_range.mp hk
            omega : N - k ≠ 0), mul_zero])
        (fun h => absurd (Finset.self_mem_range_succ N) h),
        Nat.sub_self, pow_zero, mul_one]
    exact h_eval ▸ h_cont.mono_left nhdsWithin_le_nhds
  have h_rhs : Tendsto (fun z => g z * (z - s) ^ (N + 1)) (𝓝[≠] s) (𝓝 0) := by
    have h_sub : Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
      simpa using (continuous_sub_right s).tendsto s
    have h_pow : Tendsto (fun z : ℂ => (z - s) ^ (N + 1)) (𝓝 s) (𝓝 0) := by
      simpa [zero_pow (Nat.succ_ne_zero N)] using h_sub.pow (N + 1)
    have h0 := (hg.tendsto.mul h_pow).mono_left
      (nhdsWithin_le_nhds (s := {s}ᶜ))
    simpa using h0
  exact tendsto_nhds_unique (h_lhs.congr' h_mul) h_rhs

private theorem laurent_coeff_eq_zero_of_eventuallyEq {s : ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g s) :
    ∀ {N : ℕ} {c : ℕ → ℂ},
      (∀ᶠ z in 𝓝[≠] s, ∑ k ∈ Finset.range N, c k / (z - s) ^ (k + 1) = g z) →
      ∀ k < N, c k = 0 := by
  intro N
  induction N with
  | zero => exact fun _ k hk => absurd hk (Nat.not_lt_zero k)
  | succ N IH =>
    intro c h_eq k hk
    have h_top : c N = 0 := coeff_top_eq_zero_of_eventuallyEq hg h_eq
    have h_eq' : ∀ᶠ z in 𝓝[≠] s,
        ∑ k ∈ Finset.range N, c k / (z - s) ^ (k + 1) = g z := by
      filter_upwards [h_eq] with z hz
      rwa [Finset.sum_range_succ, h_top, zero_div, add_zero] at hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · exact IH h_eq' k hk'
    · exact h_top

private theorem sum_fin_div_pow_eq_sum_range {s : ℂ} {N L : ℕ} (hNL : N ≤ L)
    (a : Fin N → ℂ) (z : ℂ) :
    ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
      = ∑ k ∈ Finset.range L,
        (if hk : k < N then a ⟨k, hk⟩ else 0) / (z - s) ^ (k + 1) := by
  have h₁ : ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
      = ∑ k ∈ Finset.range N,
        (if hk : k < N then a ⟨k, hk⟩ else 0) / (z - s) ^ (k + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => by rw [dif_pos k.isLt]
  rw [h₁]
  exact Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNL))
    fun k _ hk => by
    rw [dif_neg (Finset.mem_range.not.mp hk), zero_div]

theorem laurent_coeff_unique {s : ℂ} {N M : ℕ} {a : Fin N → ℂ} {b : Fin M → ℂ}
    {g h : ℂ → ℂ} (hg : ContinuousAt g s) (hh : ContinuousAt h s) (h_eq : ∀ᶠ z in 𝓝[≠] s,
      g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
        = h z + ∑ k : Fin M, b k / (z - s) ^ (k.val + 1)) (k : ℕ) :
    (if hk : k < N then a ⟨k, hk⟩ else 0) = (if hk : k < M then b ⟨k, hk⟩ else 0) := by
  rcases lt_or_ge k (max N M) with hk_lt | hk_ge
  · have h_diff : ∀ᶠ z in 𝓝[≠] s,
        ∑ j ∈ Finset.range (max N M),
          ((if hj : j < N then a ⟨j, hj⟩ else 0) - (if hj : j < M then b ⟨j, hj⟩ else 0))
            / (z - s) ^ (j + 1)
          = h z - g z := by
      filter_upwards [h_eq] with z hz
      rw [sum_fin_div_pow_eq_sum_range (le_max_left N M) a z,
        sum_fin_div_pow_eq_sum_range (le_max_right N M) b z] at hz
      rw [Finset.sum_congr rfl fun j _ =>
        sub_div (if hj : j < N then a ⟨j, hj⟩ else 0)
          (if hj : j < M then b ⟨j, hj⟩ else 0) ((z - s) ^ (j + 1)),
        Finset.sum_sub_distrib]
      linear_combination hz
    exact sub_eq_zero.mp
      (laurent_coeff_eq_zero_of_eventuallyEq (hh.sub hg) h_diff k hk_lt)
  · rw [dif_neg (by omega : ¬ k < N), dif_neg (by omega : ¬ k < M)]

theorem laurent_coeff_eq_meromorphicPolarCoeffAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {N : ℕ} {a : Fin N → ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g s)
    (h_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) (k : ℕ) :
    (if hk : k < N then a ⟨k, hk⟩ else 0)
      = (if hk : k < meromorphicPolarOrderAt f s then
          meromorphicPolarCoeffAt hMero ⟨k, hk⟩ else 0) := by
  refine laurent_coeff_unique hg
    (meromorphicAnalyticPartAt_analyticAt hMero).continuousAt ?_ k
  filter_upwards [h_eq, eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt
    hMero] with z hz hz'
  rw [← hz, hz', meromorphicPolarPartAt_eq_sum]

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
