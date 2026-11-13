/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Mathlib.Data.Finset.Powerset

/-!
# Fourier moments of uniformly sampled distinct noise sites

`distinctNoiseSets` and `distinctNoiseMean` describe uniform sampling of size-`L` subsets of the
whole cyclic register. Exact inclusion counts yield the mean and second moment of
`distinctNoiseFourier` at nonzero frequency.

The normalized Fourier consumer gives the corresponding second-moment formula and verifies the
cardinality and unit-modulus marking phases of each sampled set. These averages use the whole
register as their sampling universe.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `distinct_noise_actual_inclusion_law`: single-site and pair inclusion means.
* `distinct_noise_fourier_mean_second_moment`: zero mean and exact second moment.
* `distinct_noise_marked_fourier_consumer`: normalized moment and marking-phase properties.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open Matrix
open scoped Classical BigOperators

/-- The finite family of all size-`L` subsets of `ZMod N`. -/
noncomputable def distinctNoiseSets (N L : ℕ) [NeZero N] : Finset (Finset (ZMod N)) :=
  Finset.univ.powersetCard L

/-- The uniform complex-valued mean over all size-`L` subsets of `ZMod N`. -/
noncomputable def distinctNoiseMean (N L : ℕ) [NeZero N] (f : Finset (ZMod N) → ℂ) : ℂ :=
  ((distinctNoiseSets N L).card : ℂ)⁻¹*∑ S ∈ distinctNoiseSets N L, f S

/-- The unnormalized additive-character Fourier sum of the finite set `S` at frequency `y`. -/
noncomputable def distinctNoiseFourier {N : ℕ} [NeZero N] (S : Finset (ZMod N)) (y : ZMod N) : ℂ :=
  ∑ x ∈ S, ZMod.stdAddChar (x*y)

/-- The vector with amplitude `1 / sqrt S.card` on `S` and zero outside `S`. -/
noncomputable def distinctNoiseState {N : ℕ} [NeZero N] (S : Finset (ZMod N)) : ZMod N → ℂ :=
  fun x => if x∈S then (Real.sqrt (S.card : ℝ) : ℂ)⁻¹ else 0

/-- There are `N.choose L` subsets of `ZMod N` of cardinality `L`. -/
theorem distinct_noise_sets_card (N L : ℕ) [NeZero N] : (distinctNoiseSets N L).card = N.choose L := by
  simp [distinctNoiseSets, Finset.card_powersetCard, ZMod.card]

/-- The sum of complex indicators over a finite set equals the complex cast of the filtered
cardinality. -/
private theorem distinctNoise_sum_indicator {α : Type} [DecidableEq α] (T : Finset α) (p : α → Prop)
    [DecidablePred p] : (∑ x ∈ T, if p x then (1 : ℂ) else 0) = ((T.filter p).card : ℂ) := by
  rw [← Finset.sum_filter]
  simp

/-- For positive `N` and `L`, counting subsets through one distinguished element gives `N *
choose (N - 1) (L - 1) = choose N L * L`. -/
private theorem distinctNoise_choose_one (N L : ℕ) (hN : 0 < N) (hL : 0 < L) :
    N*((N-1).choose (L-1)) = (N.choose L)*L := by
  have hh := Nat.add_one_mul_choose_eq (N-1) (L-1)
  simpa only [Nat.sub_add_cancel hN, Nat.sub_add_cancel hL] using hh

/-- For `L ≤ N`, a specified residue belongs to a uniformly chosen size-`L` subset with mean
indicator `L / N`. -/
private theorem distinctNoise_single_inclusion (N L : ℕ) [NeZero N] (hLN : L ≤ N) (x : ZMod N) :
    distinctNoiseMean N L (fun S => if x∈S then 1 else 0) = (L : ℂ)/N := by
  by_cases hL : L = 0
  · subst L; simp [distinctNoiseMean, distinctNoiseSets, Finset.powersetCard_zero]
  have hLp : 0 < L := Nat.pos_of_ne_zero hL
  have hc := Finset.card_filter_powersetCard_subset ({x} : Finset (ZMod N)) Finset.univ L
    (Finset.subset_univ _) (by simpa using! hLp)
  simp only [Finset.singleton_subset_iff, Finset.card_singleton, Finset.card_univ, ZMod.card] at hc
  change ((distinctNoiseSets N L).filter (fun S => x∈S)).card = (N-1).choose (L-1) at hc
  rw [distinctNoiseMean, distinctNoise_sum_indicator, hc, distinct_noise_sets_card]
  have hC : (N.choose L : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hLN).ne'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hh : (N : ℂ)*((N-1).choose (L-1) : ℂ) = (N.choose L : ℂ)*(L : ℂ) := by
    exact_mod_cast distinctNoise_choose_one N L (NeZero.pos N) hLp
  apply (eq_div_iff hN).mpr
  calc
    _ = (N.choose L : ℂ)⁻¹*((N : ℂ)*((N-1).choose (L-1) : ℂ)) := by ring
    _ = (N.choose L : ℂ)⁻¹*((N.choose L : ℂ)*(L : ℂ)) := by rw [hh]
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]

/-- For `N` and `L` at least two, counting subsets through a distinguished pair gives the
corresponding two-element binomial coefficient identity. -/
private theorem distinctNoise_choose_two (N L : ℕ) (hN : 2 ≤ N) (hL : 2 ≤ L) :
    N*(N-1)*((N-2).choose (L-2)) = (N.choose L)*L*(L-1) := by
  have h1 := distinctNoise_choose_one N L (by omega) (by omega)
  have h2 := distinctNoise_choose_one (N-1) (L-1) (by omega) (by omega)
  simp only [Nat.sub_sub, show (1 : ℕ)+1 = 2 from rfl] at h2
  calc
    _ = N*((N-1)*((N-2).choose (L-2))) := by ring
    _ = N*(((N-1).choose (L-1))*(L-1)) := by rw [h2]
    _ = (N*((N-1).choose (L-1)))*(L-1) := by ring
    _ = _ := by rw [h1]

/-- For `L ≤ N` and `1 < N`, two distinct residues have joint mean inclusion indicator `L * (L -
1) / (N * (N - 1))`. -/
private theorem distinctNoise_pair_inclusion (N L : ℕ) [NeZero N] (hLN : L ≤ N) (x y : ZMod N)
    (hxy : x ≠ y) (hN : 1 < N) :
    distinctNoiseMean N L (fun S => if x∈S ∧ y∈S then 1 else 0) =
      (L : ℂ)*(L-1)/(N*(N-1)) := by
  by_cases hL : 2 ≤ L
  · have hc := Finset.card_filter_powersetCard_subset ({x,y} : Finset (ZMod N)) Finset.univ L
      (Finset.subset_univ _) (by simpa [hxy] using hL)
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.card_pair hxy,
      Finset.card_univ, ZMod.card] at hc
    change ((distinctNoiseSets N L).filter (fun S => x∈S ∧ y∈S)).card = (N-2).choose (L-2) at hc
    rw [distinctNoiseMean, distinctNoise_sum_indicator, hc, distinct_noise_sets_card]
    have hC : (N.choose L : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hLN).ne'
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hn1 : (N : ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show N ≠ 1 by omega))
    have hh : (N : ℂ)*((N-1 : ℕ) : ℂ)*((N-2).choose (L-2) : ℂ) =
        (N.choose L : ℂ)*(L : ℂ)*((L-1 : ℕ) : ℂ) := by
      exact_mod_cast distinctNoise_choose_two N L (by omega) hL
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one] at hh
    apply (eq_div_iff (mul_ne_zero hn hn1)).mpr
    calc
      _ = (N.choose L : ℂ)⁻¹*((N : ℂ)*(N-1)*((N-2).choose (L-2) : ℂ)) := by ring
      _ = (N.choose L : ℂ)⁻¹*((N.choose L : ℂ)*(L : ℂ)*(L-1)) := by rw [hh]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  · have he : ∀ S∈distinctNoiseSets N L, ¬(x∈S ∧ y∈S) := by
      intro S hS hmem
      have hc : S.card = L := (Finset.mem_powersetCard.mp hS).2
      have hsub : ({x,y} : Finset (ZMod N)) ⊆ S := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hmem
      have hh := Finset.card_le_card hsub
      rw [Finset.card_pair hxy, hc] at hh
      omega
    have hm : distinctNoiseMean N L (fun S => if x∈S ∧ y∈S then 1 else 0) = 0 := by
      unfold distinctNoiseMean
      rw [Finset.sum_eq_zero (fun S hS => if_neg (he S hS))]
      simp
    rw [hm]
    have hcases : L = 0 ∨ L = 1 := by omega
    rcases hcases with rfl | rfl <;> simp

/-- Combine the subset-family cardinality and exact single-site and distinct-pair inclusion
means for uniform size-`L` noise subsets, as used in the Fourier analysis of [Cornwell2014]. -/
theorem distinct_noise_actual_inclusion_law (N L : ℕ) [NeZero N] (hLN : L ≤ N) :
    (distinctNoiseSets N L).card = N.choose L ∧
    (∀ x : ZMod N, distinctNoiseMean N L (fun S => if x∈S then 1 else 0) = (L : ℂ)/N) ∧
    (∀ x y : ZMod N, x ≠ y → 1 < N → distinctNoiseMean N L (fun S => if x∈S ∧ y∈S then 1 else 0) =
      (L : ℂ)*(L-1)/(N*(N-1))) :=
  ⟨distinct_noise_sets_card N L, distinctNoise_single_inclusion N L hLN, distinctNoise_pair_inclusion N L hLN⟩

/-- A constant complex factor can be pulled out of the uniform fixed-cardinality mean. -/
@[simp] theorem distinctNoiseMean_mul_left (N L : ℕ) [NeZero N] (c : ℂ) (f : Finset (ZMod N) → ℂ) :
    distinctNoiseMean N L (fun S => c*f S) = c*distinctNoiseMean N L f := by
  simp [distinctNoiseMean, ← Finset.mul_sum, mul_left_comm]

/-- The uniform fixed-cardinality mean commutes with a sum over a finite type. -/
private theorem distinctNoiseMean_sum {A : Type} [Fintype A] (N L : ℕ) [NeZero N]
    (f : A → Finset (ZMod N) → ℂ) :
    distinctNoiseMean N L (fun S => ∑ x, f x S) = ∑ x, distinctNoiseMean N L (f x) := by
  unfold distinctNoiseMean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Write the set Fourier sum as a sum over all residues multiplied by membership indicators. -/
private theorem distinctNoise_fourier_expand {N : ℕ} [NeZero N] (S : Finset (ZMod N)) (y : ZMod N) :
    distinctNoiseFourier S y = ∑ x : ZMod N, ZMod.stdAddChar (x*y)*(if x∈S then 1 else 0) := by
  have he (x : ZMod N) : ZMod.stdAddChar (x*y)*(if x∈S then 1 else 0) =
      if x∈S then ZMod.stdAddChar (x*y) else 0 := by split_ifs <;> simp
  simp_rw [he]
  simp [distinctNoiseFourier, Finset.sum_ite_mem]

/-- Expand the Fourier squared modulus as a double character sum weighted by joint membership
indicators. -/
private theorem distinctNoise_fourier_square_expand {N : ℕ} [NeZero N] (S : Finset (ZMod N)) (y : ZMod N) :
    distinctNoiseFourier S y*star (distinctNoiseFourier S y) =
      ∑ x : ZMod N, ∑ w : ZMod N, (ZMod.stdAddChar (x*y)*star (ZMod.stdAddChar (w*y)))*
        (if x∈S ∧ w∈S then 1 else 0) := by
  rw [distinctNoise_fourier_expand, star_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hx : x∈S <;> by_cases hw : w∈S <;> simp [hx,hw]

/-- At nonzero frequency with `1 < N` and `L ≤ N`, the uniform size-`L` Fourier mean is zero and
its second moment is `L * (N - L) / (N - 1)`; see [Cornwell2014]. -/
theorem distinct_noise_fourier_mean_second_moment (N L : ℕ) [NeZero N] (y : ZMod N)
    (hN : 1 < N) (hLN : L ≤ N) (hy : y ≠ 0) :
    distinctNoiseMean N L (fun S => distinctNoiseFourier S y) = 0 ∧
    distinctNoiseMean N L (fun S => distinctNoiseFourier S y*star (distinctNoiseFourier S y)) =
      (L : ℂ)*(N-L)/(N-1) := by
  let χ := fun x : ZMod N => ZMod.stdAddChar (x*y)
  let p : ℂ := (L : ℂ)/N
  let q : ℂ := (L : ℂ)*(L-1)/(N*(N-1))
  obtain ⟨_,hi,hij⟩ := distinct_noise_actual_inclusion_law N L hLN
  have hs : ∑ x : ZMod N, χ x = 0 := by
    dsimp only [χ]
    simp_rw [mul_comm _ y]
    rw [sum_stdAddChar_mul]
    simp [hy]
  have hbar : ∑ x : ZMod N, star (χ x) = 0 := by
    simpa only [map_sum, map_zero] using! congrArg (starRingEnd ℂ) hs
  have hu (x : ZMod N) : χ x*star (χ x) = 1 := by
    dsimp only [χ]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_stdAddChar]
    norm_num
  have hp (x : ZMod N) : distinctNoiseMean N L (fun S => if x∈S then 1 else 0) = p := hi x
  have hpq (x w : ZMod N) : distinctNoiseMean N L (fun S => if x∈S ∧ w∈S then 1 else 0) =
      if x=w then p else q := by
    by_cases hxw : x=w
    · subst w; simpa only [and_self, eq_self_iff_true, ite_true] using hp x
    · rw [if_neg hxw]; exact hij x w hxw hN
  constructor
  · simp_rw [distinctNoise_fourier_expand]
    rw [distinctNoiseMean_sum]
    simp_rw [distinctNoiseMean_mul_left, hp]
    change (∑ x : ZMod N, χ x*p) = 0
    rw [← Finset.sum_mul, hs, zero_mul]
  · simp_rw [distinctNoise_fourier_square_expand]
    rw [distinctNoiseMean_sum]
    simp_rw [distinctNoiseMean_sum, distinctNoiseMean_mul_left, hpq]
    have hrow (x : ZMod N) :
        (∑ w : ZMod N, (χ x*star (χ w))*(if x=w then p else q)) = p-q := by
      have he (w : ZMod N) : (χ x*star (χ w))*(if x=w then p else q) =
          q*(χ x*star (χ w))+(if w=x then (p-q)*(χ x*star (χ w)) else 0) := by
        by_cases hw : w=x
        · subst w; simp only [ite_true]; ring
        · simp only [if_neg hw, if_neg (Ne.symm hw), add_zero]; ring
      simp_rw [he]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [hbar, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hu]
      ring
    change (∑ x : ZMod N, ∑ w : ZMod N, (χ x*star (χ w))*(if x=w then p else q)) = _
    simp_rw [hrow]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hn1 : (N : ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show N ≠ 1 by omega))
    dsimp [p,q]
    field_simp
    ring

/-- For `0 < L ≤ N`, `1 < N`, and nonzero frequency, the normalized Fourier second moment is `(N
- L) / (N * (N - 1))`, and each sampled set has size `L` with unit-modulus marking phases;
see [Cornwell2014]. -/
theorem distinct_noise_marked_fourier_consumer (N L : ℕ) [NeZero N] (y : ZMod N)
    (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N) (hy : y ≠ 0) :
    distinctNoiseMean N L (fun S => ((N*L : ℂ)⁻¹)*(distinctNoiseFourier S y*star (distinctNoiseFourier S y))) =
      (N-L : ℂ)/(N*(N-1)) ∧
    (∀ S∈distinctNoiseSets N L, S.card = L ∧
      ∀ x : ZMod N, (if x∈S then (-1 : ℂ) else 1)*star (if x∈S then (-1 : ℂ) else 1) = 1) := by
  constructor
  · rw [distinctNoiseMean_mul_left, (distinct_noise_fourier_mean_second_moment N L y hN hLN hy).2]
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hl : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hn1 : (N : ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show N ≠ 1 by omega))
    field_simp
  · intro S hS
    refine ⟨(Finset.mem_powersetCard.mp hS).2, fun x => ?_⟩
    split_ifs <;> norm_num

end Qatlib.Concepts.AmpTransform.ErrorStream
