/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SpinChainMix26.RapidMixing
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped BigOperators

/-!
# Counting cyclic blocks (Proposition 3.3)

Paper layer for *Rapid mixing of quantum spin chains at any finite temperature*
(arXiv:2610.01190v1, fixed PDF SHA256
`444509dfd74293454797e2ed9e1a45905a1c463ecc999312ed947c91ab037e29`),
Proposition 3.3 (§3.1, Eq. (38)):

* exactly `ℓ` of the `n` cyclic blocks `B_{n,ℓ}` of length `ℓ` contain a fixed site
  `i` (the erasure side of Figure 2);
* for every `r ≥ 1` at most two blocks satisfy `i ∉ B` and `dist(i, B) = r` (one in
  each direction along the cycle), so the total exterior influence is at most
  `a_η = 2 Σ_{r≥1} η(r)`.

The blocks are the source's `B_s = {s, …, s+ℓ-1}` along the periodic chain of
`n` sites, i.e. the model's `cyclicBlock n ℓ s`.
-/

namespace Qatlib.Papers.SpinChainMix26.RapidMixing
namespace BlockCounting

set_option autoImplicit false

/-! ## Modular bookkeeping -/

/-- A residue-zero natural number below `2n` is either `0` or `n`. -/
lemma mod_eq_zero_cases {x n : ℕ} (_hn : 0 < n) (hx : x < 2 * n) (h : x % n = 0) :
    x = 0 ∨ x = n := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  have hk2 : k < 2 := by
    have hx' : n * k < n * 2 := by
      rw [hk] at hx
      rw [Nat.mul_comm 2 n] at hx
      exact hx
    exact Nat.lt_of_mul_lt_mul_left hx'
  interval_cases k
  · left; omega
  · right; omega

/-- The cyclic membership predicate `(i + n − s) % n < ℓ` in terms of the clockwise
offset `u = (s + n − i) % n` from `i` to the block start `s`: either `u = 0` (the
block starts at `i`) or the counter-clockwise gap `n − u` is below `ℓ`. -/
lemma membership_aux {n : ℕ} (hn : 0 < n) (i s : Fin n) :
    (i.val + n - s.val) % n = if i = s then 0 else n - (s.val + n - i.val) % n := by
  set A := i.val + n - s.val with hA
  set U := s.val + n - i.val with hU
  have hAU : A + U = 2 * n := by omega
  have hAlt : A < 2 * n := by omega
  have hsumlt : A % n + U % n < 2 * n := by
    have h1 := Nat.mod_lt A hn
    have h2 := Nat.mod_lt U hn
    omega
  have hmod : (A % n + U % n) % n = 0 := by
    rw [← Nat.add_mod, hAU]
    simp
  rcases mod_eq_zero_cases hn hsumlt hmod with hzero | hn'
  · have ha0 : A % n = 0 := by omega
    have hAn : A = n := by
      rcases mod_eq_zero_cases hn hAlt ha0 with h | h
      · omega
      · exact h
    have hi := i.isLt
    have hs := s.isLt
    have his : i = s := by
      have hval : i.val = s.val := by omega
      exact Fin.ext hval
    rw [if_pos his]
    omega
  · have hne : i ≠ s := by
      intro hsub
      have hA' : A = n := by rw [hA, hsub]; omega
      have hU' : U = n := by rw [hU, hsub]; omega
      rw [hA', hU', Nat.mod_self] at hn'
      omega
    rw [if_neg hne]
    have h1 := Nat.mod_lt A hn
    have h2 := Nat.mod_lt U hn
    omega

/-! ## Offsets, membership and distance -/

/-- Clockwise offset `u = (s + n − i) % n` from site `i` to the start `s` of the
cyclic block `B_s`. -/
def blockOffset {n : ℕ} (i s : Fin n) : ℕ := (s.val + n - i.val) % n

/-- The offset rewritten in terms of the block-membership residue. -/
lemma blockOffset_apply {n : ℕ} (hn : 0 < n) (i s : Fin n) :
    blockOffset i s = if i = s then 0 else n - (i.val + n - s.val) % n := by
  unfold blockOffset
  have := membership_aux hn s i
  rw [this]
  by_cases h : s = i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- The offset map is injective: distinct block starts have distinct clockwise
offsets from `i`. -/
lemma blockOffset_injective {n : ℕ} (_hn : 0 < n) (i : Fin n) :
    Function.Injective (blockOffset (n := n) i) := by
  have hg : ∀ s : Fin n, ((blockOffset i s + i.val) % n) = s.val := by
    intro s
    unfold blockOffset
    have h1 : (s.val + n - i.val) + i.val = s.val + n := by omega
    calc (((s.val + n - i.val) % n) + i.val) % n
        = (((s.val + n - i.val) % n) + i.val % n) % n := by
          rw [Nat.mod_eq_of_lt i.isLt]
      _ = ((s.val + n - i.val) + i.val) % n := (Nat.add_mod _ _ _).symm
      _ = (s.val + n) % n := by rw [h1]
      _ = s.val := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt s.isLt]
  intro s1 s2 h
  have h1 := hg s1
  rw [h] at h1
  have h2 := hg s2
  exact Fin.ext (by rw [← h1, h2])

/-- The site `i` is outside the block `B_s` exactly when its offset lies in
`[1, n − ℓ]`: the block starts strictly ahead of `i` and does not wrap past it. -/
lemma notMem_cyclicBlock_iff {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (i s : Fin n) :
    i ∉ cyclicBlock n ℓ s.val ↔ (1 ≤ blockOffset i s ∧ blockOffset i s + ℓ ≤ n) := by
  have hi := i.isLt
  have hs := s.isLt
  have hmem : i ∈ cyclicBlock n ℓ s.val ↔ (i.val + n - s.val) % n < ℓ := by
    simp [cyclicBlock]
  have hoff := blockOffset_apply hn i s
  have hBlt : (i.val + n - s.val) % n < n := Nat.mod_lt _ hn
  by_cases h : i = s
  · have hoff0 : blockOffset i s = 0 := by rw [hoff, if_pos h]
    have hA : i.val + n - s.val = n := by omega
    rw [hoff0, hmem, hA, Nat.mod_self]
    constructor
    · intro hnot
      exact absurd hℓ hnot
    · intro hcon
      omega
  · have hBpos : (i.val + n - s.val) % n ≠ 0 := by
      intro hB
      have hApos : 0 < i.val + n - s.val := by omega
      have hAlt : i.val + n - s.val < 2 * n := by omega
      rcases mod_eq_zero_cases hn hAlt hB with hz | hn'
      · omega
      · omega
    have hoff' : blockOffset i s = n - (i.val + n - s.val) % n := by
      rw [hoff, if_neg h]
    rw [hoff', hmem]
    constructor
    · intro hnot
      constructor
      · omega
      · omega
    · intro hcon hlt
      omega

/-- Distance from the site `i` to the cyclic block `B_s` of length `ℓ` when `i` is
outside the block: the minimum of the clockwise distance to the block start and
the counter-clockwise distance to the block end. -/
def blockDist {n : ℕ} (ℓ : ℕ) (i s : Fin n) : ℕ :=
  min (blockOffset i s) (n - (blockOffset i s + ℓ) + 1)

/-! ## Proposition 3.3 -/

/-- **Proposition 3.3, first count.** Exactly `ℓ` of the `n` cyclic blocks of
length `ℓ` contain the site `i`. -/
lemma card_blocks_containing {n ℓ : ℕ} (hn : 0 < n) (_hℓ : 0 < ℓ) (hle : ℓ ≤ n) (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun s => i ∈ cyclicBlock n ℓ s.val)).card = ℓ := by
  have hinv : ∀ s : Fin n, ((i.val + n - (i.val + n - s.val) % n) % n) = s.val := by
    intro s
    have h := siteUpdateRate_aux n i.val s.val (by omega : s.val ≤ i.val + n)
    rw [Nat.mod_eq_of_lt s.isLt] at h
    exact h
  have hsum : (∑ s : Fin n, if i ∈ cyclicBlock n ℓ s.val then (1 : ℕ) else 0)
      = ∑ u : Fin n, if u.val < ℓ then (1 : ℕ) else 0 := by
    refine Finset.sum_nbij' (fun s : Fin n => ⟨(i.val + n - s.val) % n, Nat.mod_lt _ hn⟩)
      (fun u : Fin n => ⟨(i.val + n - u.val) % n, Nat.mod_lt _ hn⟩)
      (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a _
      exact Fin.ext (hinv a)
    · intro a _
      exact Fin.ext (hinv a)
    · intro a _
      have hmem : i ∈ cyclicBlock n ℓ a.val ↔ (i.val + n - a.val) % n < ℓ := by
        simp [cyclicBlock]
      by_cases hc : (i.val + n - a.val) % n < ℓ
      · rw [if_pos (hmem.mpr hc), if_pos hc]
      · rw [if_neg (fun h => hc (hmem.mp h)), if_neg hc]
  have hcount : (∑ u : Fin n, if u.val < ℓ then (1 : ℕ) else 0) = ℓ := by
    rw [Finset.sum_boole]
    have himg : (Finset.univ.filter (fun u : Fin n => u.val < ℓ))
        = Finset.image (Fin.castLE hle) (Finset.univ : Finset (Fin ℓ)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hu
        exact ⟨⟨u.val, hu⟩, Fin.ext rfl⟩
      · rintro ⟨v, rfl⟩
        exact v.isLt
    rw [himg, Finset.card_image_of_injective]
    · simp
    · intro a b h
      exact Fin.ext (by simpa using congrArg Fin.val h)
  rw [Finset.card_filter]
  rw [hsum, hcount]

/-- **Proposition 3.3, second count.** For every `r ≥ 1` at most two cyclic blocks
of length `ℓ` miss the site `i` and sit at distance exactly `r` from it (one block
on each side of `i` along the cycle). -/
lemma card_blocks_at_dist_le_two {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (_hle : ℓ ≤ n)
    (i : Fin n) (r : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun s => i ∉ cyclicBlock n ℓ s.val ∧ blockDist ℓ i s = r)).card ≤ 2 := by
  classical
  set I₁ : Finset (Fin n) := Finset.univ.filter (fun s => blockOffset i s = r) with hI₁
  set I₂ : Finset (Fin n) :=
    Finset.univ.filter (fun s => blockOffset i s = n - r - ℓ + 1) with hI₂
  have hsub : (Finset.univ.filter
      (fun s => i ∉ cyclicBlock n ℓ s.val ∧ blockDist ℓ i s = r)) ⊆ I₁ ∪ I₂ := by
    intro s hs
    obtain ⟨-, hnot, hdist⟩ := Finset.mem_filter.mp hs
    have hoff := (notMem_cyclicBlock_iff hn hℓ i s).mp hnot
    have hu1 : 1 ≤ blockOffset i s := hoff.1
    have hu2 : blockOffset i s + ℓ ≤ n := hoff.2
    have hv : n - (blockOffset i s + ℓ) + 1 = n - blockOffset i s - ℓ + 1 := by omega
    have hmin : min (blockOffset i s) (n - (blockOffset i s + ℓ) + 1) = r := by
      simpa [blockDist] using hdist
    rw [Finset.mem_union]
    rcases le_total (blockOffset i s) (n - (blockOffset i s + ℓ) + 1) with hle' | hle'
    · left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [min_eq_left hle'] at hmin; exact hmin⟩
    · right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [min_eq_right hle'] at hmin
      omega
  have hcard₁ : I₁.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' : blockOffset i a = r := (Finset.mem_filter.mp ha).2
    have hb' : blockOffset i b = r := (Finset.mem_filter.mp hb).2
    exact blockOffset_injective hn i (by rw [ha', hb'])
  have hcard₂ : I₂.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' : blockOffset i a = n - r - ℓ + 1 := (Finset.mem_filter.mp ha).2
    have hb' : blockOffset i b = n - r - ℓ + 1 := (Finset.mem_filter.mp hb).2
    exact blockOffset_injective hn i (by rw [ha', hb'])
  calc (Finset.univ.filter
        (fun s => i ∉ cyclicBlock n ℓ s.val ∧ blockDist ℓ i s = r)).card
      ≤ (I₁ ∪ I₂).card := Finset.card_le_card hsub
    _ ≤ I₁.card + I₂.card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-! ## The exterior-influence sum (Eq. (38)) -/

/-- Outside the block, the distance from `i` to the block is at least one: the
block is entirely ahead of `i` along the cycle, so neither the clockwise distance
to its start nor the counter-clockwise distance to its end vanishes. -/
lemma one_le_blockDist_of_notMem {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) {i s : Fin n}
    (h : i ∉ cyclicBlock n ℓ s.val) : 1 ≤ blockDist ℓ i s := by
  obtain ⟨h1, h2⟩ := (notMem_cyclicBlock_iff hn hℓ i s).mp h
  unfold blockDist
  rw [le_min_iff]
  exact ⟨h1, by omega⟩

/-- The distance from `i` to a cyclic block never exceeds the chain length. -/
lemma blockDist_le {n : ℕ} (hn : 0 < n) (ℓ : ℕ) (i s : Fin n) : blockDist ℓ i s ≤ n := by
  have h1 : blockDist ℓ i s ≤ blockOffset i s := by
    unfold blockDist
    exact min_le_left _ _
  have h2 : blockOffset i s < n := by
    unfold blockOffset
    exact Nat.mod_lt _ hn
  omega

/-- Exterior-influence sum of a profile over the blocks that miss the fixed site
`i`: `Σ_{s : i ∉ B_s} η(dist(i, B_s))`, with the summand set to zero on the blocks
that contain `i`. -/
noncomputable def exteriorInfluence {n ℓ : ℕ} (η : InfluenceProfile) (i : Fin n) : ℝ :=
  ∑ s : Fin n, if i ∈ cyclicBlock n ℓ s.val then 0 else η.eta (blockDist ℓ i s)

/-- **Proposition 3.3, exterior-influence sum (Eq. (38)).** The total influence of
the exterior sites on the blocks missing a fixed site `i` is at most
`a_η = 2 Σ_{r≥1} η(r)`: each distance `r ≥ 1` is attained by at most two blocks
(Proposition 3.3's second count), so summing the profile over the blocks costs at
most `2 η(r)` per shell. -/
lemma exteriorInfluence_le_aEta {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (hle : ℓ ≤ n)
    (η : InfluenceProfile) (hsum : Summable (fun r : ℕ => η.eta (r + 1)))
    (i : Fin n) : exteriorInfluence (ℓ := ℓ) η i ≤ aEta η := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun s => i ∉ cyclicBlock n ℓ s.val) with hS
  have hEx : exteriorInfluence (ℓ := ℓ) η i = ∑ s ∈ S, η.eta (blockDist ℓ i s) := by
    unfold exteriorInfluence
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro s _
    by_cases h : i ∈ cyclicBlock n ℓ s.val <;> simp [h]
  rw [hEx]
  have hfiber : ∑ s ∈ S, η.eta (blockDist ℓ i s)
      = ∑ r ∈ S.image (blockDist ℓ i),
          ∑ s ∈ S.filter (fun s => blockDist ℓ i s = r), η.eta (blockDist ℓ i s) :=
    (Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_image_of_mem _ hs) _).symm
  have hinner : ∀ r ∈ S.image (blockDist ℓ i),
      ∑ s ∈ S.filter (fun s => blockDist ℓ i s = r), η.eta (blockDist ℓ i s)
        ≤ 2 * η.eta r := by
    intro r _
    have hconst : ∑ s ∈ S.filter (fun s => blockDist ℓ i s = r), η.eta (blockDist ℓ i s)
        = ∑ s ∈ S.filter (fun s => blockDist ℓ i s = r), η.eta r := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    rw [hconst]
    have hcard : (S.filter (fun s => blockDist ℓ i s = r)).card ≤ 2 := by
      have heq : S.filter (fun s => blockDist ℓ i s = r)
          = Finset.univ.filter (fun s : Fin n =>
              i ∉ cyclicBlock n ℓ s.val ∧ blockDist ℓ i s = r) := by
        rw [hS]
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq]
      exact card_blocks_at_dist_le_two hn hℓ hle i r
    calc ∑ s ∈ S.filter (fun s => blockDist ℓ i s = r), η.eta r
        = (S.filter (fun s => blockDist ℓ i s = r)).card • η.eta r := Finset.sum_const _
      _ = ((S.filter (fun s => blockDist ℓ i s = r)).card : ℝ) * η.eta r := by
          rw [nsmul_eq_mul]
      _ ≤ 2 * η.eta r := by
          have hc : ((S.filter (fun s => blockDist ℓ i s = r)).card : ℝ) ≤ 2 := by
            exact_mod_cast hcard
          nlinarith [η.nonneg r]
  have himg_sub : S.image (blockDist ℓ i) ⊆ Finset.Icc 1 n := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    have hs' := (Finset.mem_filter.mp hs).2
    exact Finset.mem_Icc.mpr ⟨one_le_blockDist_of_notMem hn hℓ hs', blockDist_le hn ℓ i s⟩
  have hshift : ∑ r ∈ Finset.Icc 1 n, η.eta r ≤ ∑' j : ℕ, η.eta (j + 1) := by
    have heq : Finset.Icc 1 n = (Finset.range n).image (fun j => j + 1) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨r - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        omega
    rw [heq, Finset.sum_image]
    · exact Summable.sum_le_tsum (Finset.range n) (fun j _ => η.nonneg (j + 1)) hsum
    · intro a _ b _ hab
      simp only at hab
      omega
  calc ∑ s ∈ S, η.eta (blockDist ℓ i s)
      = ∑ r ∈ S.image (blockDist ℓ i),
          ∑ s ∈ S.filter (fun s => blockDist ℓ i s = r), η.eta (blockDist ℓ i s) := hfiber
    _ ≤ ∑ r ∈ S.image (blockDist ℓ i), 2 * η.eta r := Finset.sum_le_sum hinner
    _ = 2 * ∑ r ∈ S.image (blockDist ℓ i), η.eta r := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ r ∈ Finset.Icc 1 n, η.eta r := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
        exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub (fun r _ _ => η.nonneg r)
    _ ≤ 2 * ∑' j : ℕ, η.eta (j + 1) := by
        refine mul_le_mul_of_nonneg_left hshift (by norm_num : (0 : ℝ) ≤ 2)
    _ = aEta η := by simp [aEta]

end BlockCounting
end Qatlib.Papers.SpinChainMix26.RapidMixing
