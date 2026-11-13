/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem13K2WindowQuan

/-!
# Success and expected cost of exact counting

`bhmt_theorem17_exact_count` proves the success and expected-cost specification for the adaptive
exact-counting procedure in [BrassardEtAl2002]. Preliminary concentration bounds control the
final grid, and a half-integer rounding window gives success probability at least 2/3.

## Main statements

* `bhmt_exact_count_zero_success`: certainty for an empty marked set.
* `bhmt_theorem17_exact_count`: the exact-counting success and cost contract.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false

/-- For an empty marked set, the amplitude-estimation law is concentrated at the zero grid
label. -/
private theorem zero_count_prob {N : ℕ} (hN : 0<N) (S : Finset (Fin N))
    (hS : S.card=0) (M : ℕ) (hM : 2≤M) (z : Fin M) :
    (aeLaw M (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hM).prob z =
      if z=⟨0,by omega⟩ then 1 else 0 := by
  have ha : MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) S=0 := by
    rw [prepared_qft_mark_mass,hS,Nat.cast_zero,zero_div]
  rw [aeLaw_zero_mass M hM _ _ _ _ ha]
  have hk := (offgrid_phase_geometric_and_periodic M 0 z (by omega)).2.2
    (⟨0,by omega⟩:Fin M)
  norm_num at hk
  rw [hk]
  by_cases hz : z=⟨0,by omega⟩ <;> simp [Ket,hz,eq_comm]

/-- Exact counting returns zero with probability one when the marked set is empty. -/
theorem bhmt_exact_count_zero_success {N : ℕ} (hN : 0<N) (S : Finset (Fin N))
    (hS : S.card=0) (hM₀ : 2≤exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2≤exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :
    exactCountSuccessMass hN S hM₀ hM = 1 := by
  classical
  simp [exactCountSuccessMass,zero_count_prob hN S hS,exactCountOutput,aeEstimate,hS]
  norm_num

/-- For an empty marked set, the expected cost is twice the preliminary grid size plus the final
grid size selected by two zero estimates. -/
theorem bhmt_exact_count_zero_cost_eq {N : ℕ} (hN : 0<N) (S : Finset (Fin N))
    (hS : S.card=0) (hM₀ : 2≤exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2≤exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :
    exactCountCostMass hN S hM₀ hM = 2*(exactCountM₀ N:ℝ)+(exactCountGrid N 0 0:ℝ) := by
  classical
  simp [exactCountCostMass,zero_count_prob hN S hS,aeEstimate]

/-- For an empty marked set, the expected cost is at most `1000 * sqrt (N + 1)`. -/
theorem bhmt_exact_count_zero_cost_bound {N : ℕ} (hN : 0<N) (S : Finset (Fin N))
    (hS : S.card=0) (hM₀ : 2≤exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2≤exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :
    exactCountCostMass hN S hM₀ hM ≤ 1000*Real.sqrt ((N:ℝ)+1) := by
  rw [bhmt_exact_count_zero_cost_eq hN S hS]
  have hN0 : (0:ℝ)≤N := by positivity
  have hB0 := Real.sqrt_nonneg ((N:ℝ)+1)
  have hB2 := Real.sq_sqrt (show 0≤(N:ℝ)+1 by positivity)
  have hB1 : 1≤Real.sqrt ((N:ℝ)+1) := by nlinarith
  have hmono : Real.sqrt (N:ℝ) ≤ Real.sqrt ((N:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
  have hA0 : 0≤14*Real.pi*Real.sqrt (N:ℝ) := by positivity
  have hceil := (Nat.ceil_lt_add_one hA0).le
  have hceilB := (Nat.ceil_lt_add_one
    (show 0≤30*Real.sqrt ((N:ℝ)+1) by positivity)).le
  have hpi : 14*Real.pi*Real.sqrt (N:ℝ) ≤ 56*Real.sqrt ((N:ℝ)+1) := by
    calc
      _ ≤ 14*4*Real.sqrt (N:ℝ) := by gcongr; exact Real.pi_lt_four.le
      _ ≤ _ := by nlinarith
  dsimp [exactCountM₀,exactCountGrid,exactCountRough]
  simp only [zero_add,sub_zero,one_mul,min_self]
  nlinarith

/-- The corrected final estimation error constant `2 * π * sqrt 2 / 30 + 4 * π^2 / 30^2` is
strictly less than 1/2. -/
theorem bhmt_exact_count_corrected_window :
    2*Real.pi*Real.sqrt 2/30+4*Real.pi^2/30^2 < (1:ℝ)/2 := by
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt (2:ℝ) ≤ 3/2 := by nlinarith
  have hp := Real.pi_lt_four
  have hprod : Real.pi*Real.sqrt 2 ≤ 4*(3/2) :=
    mul_le_mul hp.le hs hs0 (by norm_num)
  have hp2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos]
  nlinarith

/-- An estimate at distance strictly less than 1/2 from a natural number rounds to that number
under `floor (x + 1/2)`. -/
theorem bhmt_exact_count_round (t : ℕ) (x : ℝ) (hx : |x-(t:ℝ)|<(1:ℝ)/2) :
    (⌊x+1/2⌋:ℤ)=(t:ℤ) := by
  apply Int.floor_eq_iff.mpr
  obtain ⟨hl,hu⟩ := abs_lt.mp hx
  push_cast
  constructor <;> linarith
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
open scoped Classical
set_option autoImplicit false

/-- The real constant `π` is strictly less than `22/7`. -/
private theorem ec_pi_lt_22_7 : Real.pi < 22/7 :=
  lt_trans Real.pi_lt_d6 (by norm_num)

/-- The preliminary grid size is at least `14 * π * sqrt N`. -/
private theorem ec_m0_ge (N : ℕ) :
    14*Real.pi*Real.sqrt (N:ℝ) ≤ (exactCountM₀ N : ℝ) :=
  Nat.le_ceil _

/-- For positive `N`, the preliminary grid size is positive. -/
private theorem ec_m0_pos (N : ℕ) (hN : 0 < N) : 0 < (exactCountM₀ N : ℝ) := by
  refine lt_of_lt_of_le ?_ (ec_m0_ge N)
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.sqrt_pos.mpr (by exact_mod_cast hN))

/-- The square of the preliminary grid size is at least `196 * π^2 * N`. -/
private theorem ec_m0_sq (N : ℕ) :
    196*Real.pi^2*(N:ℝ) ≤ ((exactCountM₀ N : ℝ))^2 := by
  have h0 : 0 ≤ 14*Real.pi*Real.sqrt (N:ℝ) := by positivity
  have h1 : (14*Real.pi*Real.sqrt (N:ℝ))^2 ≤ ((exactCountM₀ N : ℝ))^2 :=
    sq_le_sq' (by linarith [h0, ec_m0_ge N]) (ec_m0_ge N)
  rw [show (14*Real.pi*Real.sqrt (N:ℝ))^2 = 196*Real.pi^2*(N:ℝ) from by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; ring] at h1
  exact h1

/-- Every scaled amplitude-estimation readout lies in the interval `[0, N]`. -/
private theorem ec_readout_mem (N M : ℕ) (z : Fin M) :
    0 ≤ (N:ℝ)*aeEstimate M z ∧ (N:ℝ)*aeEstimate M z ≤ (N:ℝ) := by
  have h1 : (Real.sin (Real.pi*(z.val : ℝ)/(M:ℝ)))^2 ≤ 1 := Real.sin_sq_le_one _
  rw [show aeEstimate M z = (Real.sin (Real.pi*(z.val : ℝ)/(M:ℝ)))^2 from rfl]
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _),
    by nlinarith [h1, (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]⟩

/-- The real-valued cardinality of a subset of `Fin N` is at most `N`. -/
private theorem ec_card_le {N : ℕ} (S : Finset (Fin N)) : (S.card : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast (show S.card ≤ N by simpa using S.card_le_univ)

/-- For `x ∈ [0, N]`, the rough-scale radicand `(x + 1) * (N - x + 1)` is at least `N + 1`. -/
private theorem ec_rough_sq_ge (N : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hxN : x ≤ (N:ℝ)) :
    (N:ℝ)+1 ≤ (x+1)*((N:ℝ)-x+1) := by
  have h1 : 0 ≤ x*((N:ℝ)-x) := mul_nonneg hx0 (by linarith)
  have h2 : (x+1)*((N:ℝ)-x+1) = (N:ℝ)+1 + x*((N:ℝ)-x) := by ring
  rw [h2]
  linarith

/-- If the target lies within two of either endpoint, every readout in `[0, N]` gives
rough-scale radicand at least `t * (N - t) / 2`. -/
private theorem ec_near_R (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (htN : t ≤ (N:ℝ))
    (hnear : t ≤ 2 ∨ (N:ℝ)-t ≤ 2) (x : ℝ) (hx0 : 0 ≤ x) (hxN : x ≤ (N:ℝ)) :
    t*((N:ℝ)-t)/2 ≤ (x+1)*((N:ℝ)-x+1) := by
  have h1 := ec_rough_sq_ge N x hx0 hxN
  have hD2 : t*((N:ℝ)-t) ≤ 2*(N:ℝ) := by
    rcases hnear with h | h
    · nlinarith [mul_le_mul_of_nonneg_left (by linarith) ht0]
    · nlinarith [mul_le_mul_of_nonneg_right h ht0]
  nlinarith

/-- For a target at least three from either endpoint, the stated preliminary error window
ensures rough-scale radicand at least `t * (N - t) / 2`. -/
private theorem ec_far_R (N : ℕ) (hN : 0 < N) (t : ℝ) (ht0 : 0 ≤ t) (htN : t ≤ (N:ℝ))
    (hfar : 3 ≤ t ∧ 3 ≤ (N:ℝ)-t)
    (x : ℝ) (_hx0 : 0 ≤ x) (_hxN : x ≤ (N:ℝ))
    (hδ : |x-t| ≤ Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)) + 1/4) :
    t*((N:ℝ)-t)/2 ≤ (x+1)*((N:ℝ)-x+1) := by
  have hnN : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hmins : t*((N:ℝ)-t)/(N:ℝ) ≤ min t ((N:ℝ)-t) := by
    refine le_min ?_ ?_
    · rw [div_le_iff₀ hnN]
      have h1 : (N:ℝ)-t ≤ (N:ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left h1 ht0
    · rw [div_le_iff₀ hnN]
      have h1 : 0 ≤ (N:ℝ)-t := by linarith
      calc t*((N:ℝ)-t) ≤ (N:ℝ)*((N:ℝ)-t) := mul_le_mul_of_nonneg_right htN h1
        _ = ((N:ℝ)-t)*(N:ℝ) := by ring
  have hs3m : 3 ≤ min t ((N:ℝ)-t) := le_min hfar.1 hfar.2
  have hs0 : 0 ≤ min t ((N:ℝ)-t) := le_min ht0 (by linarith)
  have hsq : min t ((N:ℝ)-t) ≤ ((2*(min t ((N:ℝ)-t))+1)/4)^2 := by
    have hnn : 0 ≤ 4*(min t ((N:ℝ)-t))*((min t ((N:ℝ)-t))-3) :=
      mul_nonneg (mul_nonneg (by norm_num) hs0) (by linarith)
    nlinarith [hnn]
  have hsqr : Real.sqrt (min t ((N:ℝ)-t)) ≤ (2*(min t ((N:ℝ)-t))+1)/4 := by
    refine (Real.sqrt_le_sqrt hsq).trans_eq ?_
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have habs : |x-t| ≤ (min t ((N:ℝ)-t)+1)/2 := by
    have h1 : Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)) ≤ Real.sqrt (min t ((N:ℝ)-t)) :=
      Real.sqrt_le_sqrt hmins
    have h2 := hδ.trans (add_le_add h1 (le_refl (1/4)))
    have h3 : Real.sqrt (min t ((N:ℝ)-t)) + 1/4 ≤ (min t ((N:ℝ)-t)+1)/2 := by
      have h3' : (2*(min t ((N:ℝ)-t))+1)/4 + 1/4 = (min t ((N:ℝ)-t)+1)/2 := by ring
      exact (add_le_add hsqr (le_refl (1/4))).trans_eq h3'
    exact h2.trans h3
  rcases le_or_gt 0 (x-t) with hδ0 | hδ0
  · have hx1 : t+1 ≤ x+1 := by linarith
    have hNx1 : ((N:ℝ)-t+1)/2 ≤ (N:ℝ)-x+1 := by
      have hle : x-t ≤ (min t ((N:ℝ)-t)+1)/2 := (abs_le.mp habs).2
      have hmin2 : min t ((N:ℝ)-t) ≤ (N:ℝ)-t := min_le_right _ _
      linarith
    have hprod : (t+1)*(((N:ℝ)-t+1)/2) ≤ (x+1)*((N:ℝ)-x+1) :=
      mul_le_mul hx1 hNx1 (by linarith) (by linarith)
    have hle2 : t*((N:ℝ)-t)/2 ≤ (t+1)*(((N:ℝ)-t+1)/2) := by
      have h : (t+1)*(((N:ℝ)-t+1)/2) - t*((N:ℝ)-t)/2 = ((N:ℝ)+1)/2 := by ring
      linarith
    linarith
  · have hNx1 : (N:ℝ)-t+1 ≤ (N:ℝ)-x+1 := by linarith
    have hx1 : (t+1)/2 ≤ x+1 := by
      have hle : -(x-t) ≤ (min t ((N:ℝ)-t)+1)/2 := (neg_le_abs (x-t)).trans habs
      have hmin1 : min t ((N:ℝ)-t) ≤ t := min_le_left _ _
      linarith
    have hprod : ((t+1)/2)*((N:ℝ)-t+1) ≤ (x+1)*((N:ℝ)-x+1) :=
      mul_le_mul hx1 hNx1 (by linarith) (by linarith)
    have hle2 : t*((N:ℝ)-t)/2 ≤ ((t+1)/2)*((N:ℝ)-t+1) := by
      have h : ((t+1)/2)*((N:ℝ)-t+1) - t*((N:ℝ)-t)/2 = ((N:ℝ)+1)/2 := by ring
      linarith
    linarith

/-- For integer `k ≥ 2`, the preliminary estimate lies in the stated `k`-dependent count-error
window with probability at least `1 - 1 / (2 * (k - 1))`. -/
private theorem ec_window_mass (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountM₀ N) (k : ℕ) (hk : 2 ≤ k) :
    1 - 1/(2*((k:ℝ)-1)) ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin (exactCountM₀ N) =>
        |(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
          (k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) + (k:ℝ)^2),
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z := by
  have hD : 0 ≤ (S.card:ℝ)*((N:ℝ)-S.card) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [ec_card_le S])
  have hmass := bhmt_counting_k2_window N (exactCountM₀ N) S hN hM₀ k hk
  refine hmass.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
    have hstep : 2*Real.pi*(k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(exactCountM₀ N : ℝ)
        ≤ 2*Real.pi*(k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/
            (14*Real.pi*Real.sqrt (N:ℝ)) := by
      rw [div_le_div_iff₀ (ec_m0_pos N hN) (by positivity)]
      exact mul_le_mul_of_nonneg_left (ec_m0_ge N) (by positivity)
    have heq : 2*Real.pi*(k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/
        (14*Real.pi*Real.sqrt (N:ℝ))
        = (k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ))/7 := by
      rw [Real.sqrt_div hD]
      field_simp
      ring
    have h1 : 2*Real.pi*(k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(exactCountM₀ N : ℝ)
        ≤ (k:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) := by
      refine hstep.trans ?_
      rw [heq]
      exact div_le_self (mul_nonneg hk0 (Real.sqrt_nonneg _)) (by norm_num)
    have hstep2 : Real.pi^2*(k:ℝ)^2*(N:ℝ)/((exactCountM₀ N : ℝ)^2)
        ≤ Real.pi^2*(k:ℝ)^2*(N:ℝ)/(196*Real.pi^2*(N:ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left (ec_m0_sq N) (by positivity)
    have heq2 : Real.pi^2*(k:ℝ)^2*(N:ℝ)/(196*Real.pi^2*(N:ℝ)) = (k:ℝ)^2/196 := by
      field_simp
    have h2 : Real.pi^2*(k:ℝ)^2*(N:ℝ)/((exactCountM₀ N : ℝ)^2) ≤ (k:ℝ)^2 := by
      refine hstep2.trans ?_
      rw [heq2]
      exact div_le_self (sq_nonneg _) (by norm_num)
    linarith
  · intro z _ _
    exact (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).nonneg z

/-- The preliminary estimate lies within `sqrt (t * (N - t) / N) + 1/4` of the marked
cardinality `t` with probability at least `11/12`. -/
private theorem ec_good_mass (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountM₀ N) :
    11/12 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin (exactCountM₀ N) =>
        |(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
          Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) + 1/4),
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z := by
  have hD : 0 ≤ (S.card:ℝ)*((N:ℝ)-S.card) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [ec_card_le S])
  have hmass := bhmt_counting_k2_window N (exactCountM₀ N) S hN hM₀ 7 (by norm_num)
  have hnum : (1:ℝ) - 1/(2*(((7:ℕ):ℝ)-1)) = 11/12 := by norm_num
  rw [hnum] at hmass
  refine hmass.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    norm_num at hz
    rw [← Real.sqrt_mul (Nat.cast_nonneg (S.card : ℕ)) ((N:ℝ)-(S.card:ℝ))] at hz
    have hstep : 2*Real.pi*(7:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/
        (exactCountM₀ N : ℝ)
        ≤ 2*Real.pi*(7:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/
            (14*Real.pi*Real.sqrt (N:ℝ)) := by
      rw [div_le_div_iff₀ (ec_m0_pos N hN) (by positivity)]
      exact mul_le_mul_of_nonneg_left (ec_m0_ge N) (by positivity)
    have heq : 2*Real.pi*(7:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/
        (14*Real.pi*Real.sqrt (N:ℝ))
        = Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) := by
      rw [Real.sqrt_div hD]
      field_simp
      ring
    have h1 : 2*Real.pi*(7:ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/
        (exactCountM₀ N : ℝ) ≤ Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) := by
      refine hstep.trans ?_
      rw [heq]
    have hstep2 : Real.pi^2*(7:ℝ)^2*(N:ℝ)/((exactCountM₀ N : ℝ)^2)
        ≤ Real.pi^2*(7:ℝ)^2*(N:ℝ)/(196*Real.pi^2*(N:ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left (ec_m0_sq N) (by positivity)
    have heq2 : Real.pi^2*(7:ℝ)^2*(N:ℝ)/(196*Real.pi^2*(N:ℝ)) = (49:ℝ)/196 := by
      field_simp
      ring
    have h2 : Real.pi^2*(7:ℝ)^2*(N:ℝ)/((exactCountM₀ N : ℝ)^2) ≤ 1/4 := by
      refine hstep2.trans ?_
      rw [heq2]
      norm_num
    linarith
  · intro z _ _
    exact (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).nonneg z

/-- The final estimate rounds to the exact marked cardinality when its error and grid size
satisfy the stated bounds. -/
private theorem ec_final_window_output {N : ℕ} (S : Finset (Fin N))
    {M : ℕ} (hM : 2 ≤ M) (y : Fin M)
    (hD9 : 900*(S.card:ℝ)*((N:ℝ)-S.card) ≤ 2*((M:ℝ)^2))
    (hN9 : 900*(N:ℝ) ≤ 4*((M:ℝ)^2))
    (hy : |(N:ℝ)*aeEstimate M y-(S.card:ℝ)| ≤
        2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(M:ℝ)+
          Real.pi^2*(N:ℝ)/((M:ℝ)^2)) :
    exactCountOutput N y = ((S.card : ℕ) : ℤ) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hD : 0 ≤ (S.card:ℝ)*((N:ℝ)-S.card) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [ec_card_le S])
  have hw : (Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)))^2
      = (S.card:ℝ)*((N:ℝ)-S.card) := Real.sq_sqrt hD
  have hsq1 : (2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))*30)^2
      = 3600*Real.pi^2*((S.card:ℝ)*((N:ℝ)-S.card)) := by
    rw [mul_pow, mul_pow, mul_pow, hw]; ring
  have hsq2 : (2*Real.pi*Real.sqrt 2*(M:ℝ))^2 = 8*Real.pi^2*((M:ℝ)^2) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have habs : (2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)))*30
      ≤ 2*Real.pi*Real.sqrt 2*(M:ℝ) := by
    have hA : (0:ℝ) ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))*30 := by positivity
    have hB : (0:ℝ) ≤ 2*Real.pi*Real.sqrt 2*(M:ℝ) := by positivity
    have hsqpre : (2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))*30)^2
        ≤ (2*Real.pi*Real.sqrt 2*(M:ℝ))^2 := by
      rw [hsq1]
      have hD9' : 900*((S.card:ℝ)*((N:ℝ)-S.card)) ≤ 2*((M:ℝ)^2) := by
        rw [show 900*((S.card:ℝ)*((N:ℝ)-S.card))
            = 900*(S.card:ℝ)*((N:ℝ)-S.card) from by ring]
        exact hD9
      have hstep' : 900*((S.card:ℝ)*((N:ℝ)-S.card))*(4*Real.pi^2)
          ≤ 2*((M:ℝ)^2)*(4*Real.pi^2) :=
        mul_le_mul_of_nonneg_right hD9' (by positivity)
      calc 3600*Real.pi^2*((S.card:ℝ)*((N:ℝ)-S.card))
          = 900*((S.card:ℝ)*((N:ℝ)-S.card))*(4*Real.pi^2) := by ring
        _ ≤ 2*((M:ℝ)^2)*(4*Real.pi^2) := hstep'
        _ = (2*Real.pi*Real.sqrt 2*(M:ℝ))^2 := by rw [hsq2]; ring
    have hsq := sq_le_sq.mp hsqpre
    rw [abs_of_nonneg hA, abs_of_nonneg hB] at hsq
    exact hsq
  have ht1 : 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(M:ℝ)
      ≤ 2*Real.pi*Real.sqrt 2/30 := by
    rw [div_le_div_iff₀ hM0 (by norm_num : (0:ℝ) < 30)]
    linarith [habs]
  have ht2 : Real.pi^2*(N:ℝ)/((M:ℝ)^2) ≤ 4*Real.pi^2/30^2 := by
    rw [div_le_div_iff₀ (pow_pos hM0 2) (by norm_num : (0:ℝ) < (30:ℝ)^2)]
    have h := mul_le_mul_of_nonneg_left hN9 (show (0:ℝ) ≤ Real.pi^2 by positivity)
    nlinarith [h]
  have hlt := bhmt_exact_count_corrected_window
  have hfin := hy.trans (add_le_add ht1 ht2)
  exact bhmt_exact_count_round S.card ((N:ℝ)*aeEstimate M y) (lt_of_le_of_lt hfin hlt)

/-- If both preliminary rough radicands are sufficiently large, the conditional final
exact-counting success probability is at least `8 / π^2`. -/
private theorem ec_conditional_final {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (_hM₀ : 2 ≤ exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂))
    (z₁ z₂ : Fin (exactCountM₀ N))
    (hR₁ : (S.card:ℝ)*((N:ℝ)-S.card)/2 ≤
      (((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)+1)*
        ((N:ℝ)-((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)+1))
    (hR₂ : (S.card:ℝ)*((N:ℝ)-S.card)/2 ≤
      (((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)+1)*
        ((N:ℝ)-((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)+1)) :
    8/Real.pi^2 ≤ ∑ y ∈ Finset.univ.filter
        (fun y : Fin (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
          ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) =>
          exactCountOutput N y = ((S.card : ℕ) : ℤ)),
      (aeLaw (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (hM z₁ z₂)).prob y := by
  have hD : 0 ≤ (S.card:ℝ)*((N:ℝ)-S.card) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [ec_card_le S])
  have hx₁ := ec_readout_mem N (exactCountM₀ N) z₁
  have hx₂ := ec_readout_mem N (exactCountM₀ N) z₂
  have hN1₁ : (N:ℝ)+1 ≤ (((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)+1)*
      ((N:ℝ)-((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)+1) :=
    ec_rough_sq_ge N _ hx₁.1 hx₁.2
  have hN1₂ : (N:ℝ)+1 ≤ (((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)+1)*
      ((N:ℝ)-((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)+1) :=
    ec_rough_sq_ge N _ hx₂.1 hx₂.2
  have hminD : Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/2) ≤
      min (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁))
        (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :=
    le_min (Real.sqrt_le_sqrt hR₁) (Real.sqrt_le_sqrt hR₂)
  have hminN : Real.sqrt ((N:ℝ)+1) ≤
      min (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁))
        (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :=
    le_min (Real.sqrt_le_sqrt hN1₁) (Real.sqrt_le_sqrt hN1₂)
  have hceil : 30*(min (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁))
      (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂))) ≤
    ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hstepD : 30*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/2) ≤
    ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hminD (by norm_num)).trans hceil
  have hD2 : 0 ≤ (S.card:ℝ)*((N:ℝ)-S.card)/2 := div_nonneg hD (by norm_num)
  have hD9 : 900*(S.card:ℝ)*((N:ℝ)-S.card) ≤ 2*((exactCountGrid N
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)^2 := by
    have hsq : (30*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/2))^2
        = 450*((S.card:ℝ)*((N:ℝ)-S.card)) := by
      rw [mul_pow, Real.sq_sqrt hD2]
      ring
    have hle : (30*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/2))^2 ≤
        ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
          ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)^2 := by
      nlinarith [hstepD, Real.sqrt_nonneg ((S.card:ℝ)*((N:ℝ)-S.card)/2),
        (show (0:ℝ) ≤ ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
          ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) from Nat.cast_nonneg _)]
    rw [hsq] at hle
    linarith
  have hstepN : 30*Real.sqrt ((N:ℝ)+1) ≤
    ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hminN (by norm_num)).trans hceil
  have hN9 : 900*(N:ℝ) ≤ 4*((exactCountGrid N
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)^2 := by
    have hsq : (30*Real.sqrt ((N:ℝ)+1))^2 = 900*((N:ℝ)+1) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (N:ℝ)+1)]
      norm_num
    have hle : (30*Real.sqrt ((N:ℝ)+1))^2 ≤
        ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
          ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)^2 := by
      nlinarith [hstepN, Real.sqrt_nonneg ((N:ℝ)+1),
        (show (0:ℝ) ≤ ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
          ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) from Nat.cast_nonneg _)]
    rw [hsq] at hle
    nlinarith [hle, sq_nonneg (((exactCountGrid N ((N:ℝ)*aeEstimate
      (exactCountM₀ N) z₁) ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ))]
  have hmass := amplitude_counting_actual_consumer N (exactCountGrid N
    ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂))
    hN (hM z₁ z₂) S
  refine hmass.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy' ⊢
    exact ec_final_window_output S (hM z₁ z₂) y hD9 hN9 hy'
  · intro y _ _
    exact (aeLaw (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (hM z₁ z₂)).nonneg y

/-- A double sum of products over the same finite set factors into the product of the two sums. -/
private theorem ec_double_sum_prod {M : ℕ} (s : Finset (Fin M)) (f g : Fin M → ℝ) :
    ∑ z₁ ∈ s, ∑ z₂ ∈ s, f z₁ * g z₂ = (∑ z ∈ s, f z)*(∑ z ∈ s, g z) := by
  rw [Finset.sum_mul_sum]

/-- A constant averaged against two normalized copies of a finite weight function equals that
constant. -/
private theorem ec_double_sum_const {M : ℕ} (pp : Fin M → ℝ) (hp1 : ∑ z, pp z = 1) (a : ℝ) :
    ∑ z₁, ∑ z₂, pp z₁*(pp z₂*a) = a := by
  have hinner : ∀ z₁ : Fin M, ∑ z₂, pp z₁*(pp z₂*a) = pp z₁*a := by
    intro z₁
    have hshape : ∑ z₂, pp z₁*(pp z₂*a) = ∑ z₂, pp z₂*(pp z₁*a) :=
      Finset.sum_congr rfl (fun z₂ _ => by ring)
    rw [hshape, ← Finset.sum_mul, hp1, one_mul]
  rw [Finset.sum_congr rfl (fun z₁ _ => hinner z₁), ← Finset.sum_mul, hp1, one_mul]

/-- Interchanges a finite sum of layers with the two finite readout sums. -/
private theorem ec_sum_swap3 {M : ℕ} (f : Fin M → Fin M → ℕ → ℝ) (s : Finset ℕ) :
    ∑ z₁, ∑ z₂, ∑ j ∈ s, f z₁ z₂ j = ∑ j ∈ s, ∑ z₁, ∑ z₂, f z₁ z₂ j := by
  have hinner : ∀ z₁ : Fin M, (∑ z₂, ∑ j ∈ s, f z₁ z₂ j) = ∑ j ∈ s, ∑ z₂, f z₁ z₂ j :=
    fun z₁ => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun z₁ _ => hinner z₁), Finset.sum_comm]

/-- A lower bound `1 - b` on an event's mass gives an upper bound `b` on the complementary mass
for normalized weights. -/
private theorem ec_complement_mass {M : ℕ} (pp : Fin M → ℝ) (hp1 : ∑ z, pp z = 1)
    (P : Fin M → Prop) [DecidablePred P] (b : ℝ)
    (hmass : 1 - b ≤ ∑ z ∈ Finset.univ.filter P, pp z) :
    ∑ z ∈ Finset.univ.filter (fun z => ¬ P z), pp z ≤ b := by
  have hsplit : ∑ z ∈ Finset.univ.filter P, pp z
      + ∑ z ∈ Finset.univ.filter (fun z => ¬P z), pp z = ∑ z, pp z := by
    rw [Finset.sum_filter P pp, Finset.sum_filter (fun z => ¬P z) pp,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ => by split_ifs <;> ring)
  rw [hp1] at hsplit
  linarith

/-- Two preliminary good events of mass at least `11/12`, together with conditional success at
least `8 / π^2`, give the corresponding product lower bound on joint success. -/
private theorem ec_joint_assembly {M : ℕ} (p : Fin M → ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (_hp1 : ∑ z, p z = 1) (G : Finset (Fin M))
    (mG : 11/12 ≤ ∑ z ∈ G, p z) (q : Fin M → Fin M → ℝ) (hq0 : ∀ z₁ z₂, 0 ≤ q z₁ z₂)
    (hqG : ∀ z₁ ∈ G, ∀ z₂ ∈ G, 8/Real.pi^2 ≤ q z₁ z₂) :
    (11/12)*(11/12)*(8/Real.pi^2) ≤ ∑ z₁, ∑ z₂, p z₁ * p z₂ * q z₁ z₂ := by
  have hstep1 : ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂
      ≤ ∑ z₁ : Fin M, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
      (fun z₁ _ _ => Finset.sum_nonneg (fun z₂ _ =>
        mul_nonneg (mul_nonneg (hp0 z₁) (hp0 z₂)) (hq0 z₁ z₂)))
  have h1 : ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂
      ≤ ∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁ * p z₂ * q z₁ z₂ :=
    hstep1.trans (Finset.sum_le_sum (fun z₁ _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        (fun z₂ _ _ => mul_nonneg (mul_nonneg (hp0 z₁) (hp0 z₂)) (hq0 z₁ z₂))))
  have hpt : ∀ z₁ ∈ G, ∀ z₂ ∈ G,
      (8/Real.pi^2)*(p z₁ * p z₂) ≤ p z₁ * p z₂ * q z₁ z₂ := by
    intro z₁ hz₁ z₂ hz₂
    have h := mul_le_mul_of_nonneg_right (hqG z₁ hz₁ z₂ hz₂)
      (mul_nonneg (hp0 z₁) (hp0 z₂))
    rwa [mul_comm (q z₁ z₂) (p z₁ * p z₂)] at h
  have h2 : (8/Real.pi^2)*(∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂)
      ≤ ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ := by
    calc (8/Real.pi^2)*(∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂)
        = ∑ z₁ ∈ G, ∑ z₂ ∈ G, (8/Real.pi^2)*(p z₁ * p z₂) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z₁ _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ :=
          Finset.sum_le_sum (fun z₁ hz₁ => Finset.sum_le_sum (fun z₂ hz₂ => hpt z₁ hz₁ z₂ hz₂))
  have h3 : ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ = (∑ z ∈ G, p z)*(∑ z ∈ G, p z) :=
    ec_double_sum_prod G p p
  have hGG : (11/12)*(11/12) ≤ (∑ z ∈ G, p z)*(∑ z ∈ G, p z) :=
    mul_le_mul mG mG (show (0:ℝ) ≤ 11/12 by norm_num)
      (Finset.sum_nonneg (fun z _ => hp0 z))
  have hfin : (11/12)*(11/12)*(8/Real.pi^2)
      ≤ (8/Real.pi^2)*((∑ z ∈ G, p z)*(∑ z ∈ G, p z)) := by
    calc (11/12)*(11/12)*(8/Real.pi^2) = (8/Real.pi^2)*((11/12)*(11/12)) := by ring
      _ ≤ (8/Real.pi^2)*((∑ z ∈ G, p z)*(∑ z ∈ G, p z)) :=
          mul_le_mul_of_nonneg_left hGG (by positivity)
  calc (11/12)*(11/12)*(8/Real.pi^2)
      ≤ (8/Real.pi^2)*(∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂) := hfin.trans_eq (by rw [h3])
    _ ≤ ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ := h2
    _ ≤ ∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁ * p z₂ * q z₁ z₂ := h1

/-- The product `(11/12)^2 * (8 / π^2)` is at least `2/3`. -/
private theorem ec_success_constant : 2/3 ≤ (11/12)*(11/12)*(8/Real.pi^2) := by
  have hpi : Real.pi ≤ 22/7 := ec_pi_lt_22_7.le
  have hpisq : Real.pi^2 ≤ ((22:ℝ)/7)^2 := by nlinarith [Real.pi_pos, hpi]
  rw [show ((22:ℝ)/7)^2 = (484:ℝ)/49 from by norm_num] at hpisq
  have hstep : ((49:ℝ)/72)*Real.pi^2 ≤ ((121:ℝ)/144)*8 := by
    nlinarith [mul_le_mul_of_nonneg_left hpisq (by norm_num : (0:ℝ) ≤ 49/72)]
  have h72 : 2/3 ≤ ((49:ℝ)/72) := by norm_num
  refine h72.trans ?_
  rw [show ((11:ℝ)/12)*((11:ℝ)/12) = ((121:ℝ)/144) from by norm_num,
    show ((121:ℝ)/144)*(8/Real.pi^2) = (((121:ℝ)/144)*8)/Real.pi^2 from by ring,
    le_div_iff₀ (by positivity : (0:ℝ) < Real.pi^2)]
  exact hstep

/-- The adaptive exact-counting success mass is at least `2/3` for valid preliminary and final
grids. -/
private theorem ec_success_positive {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :
    2/3 ≤ exactCountSuccessMass hN S hM₀ hM := by
  classical
  have hR : ∀ z : Fin (exactCountM₀ N), z ∈ Finset.univ.filter
      (fun z : Fin (exactCountM₀ N) =>
        |(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
          Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) + 1/4) →
      (S.card:ℝ)*((N:ℝ)-S.card)/2 ≤
        (((N:ℝ)*aeEstimate (exactCountM₀ N) z)+1)*
          ((N:ℝ)-((N:ℝ)*aeEstimate (exactCountM₀ N) z)+1) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hx := ec_readout_mem N (exactCountM₀ N) z
    by_cases hn : 3 ≤ S.card ∧ S.card + 3 ≤ N
    · refine ec_far_R N hN (S.card:ℝ) (Nat.cast_nonneg _) (ec_card_le S) ?_
        _ hx.1 hx.2 hz
      refine ⟨by exact_mod_cast hn.1, ?_⟩
      have h3r : ((S.card:ℕ)+3 : ℝ) ≤ (N:ℝ) := by exact_mod_cast hn.2
      have hcard : (S.card:ℝ) ≤ (N:ℝ) := ec_card_le S
      linarith
    · have hn2 : S.card ≤ 2 ∨ N ≤ S.card + 2 := by omega
      refine ec_near_R N (S.card:ℝ) (Nat.cast_nonneg _) (ec_card_le S) ?_
        _ hx.1 hx.2
      rcases hn2 with h | h
      · exact Or.inl (by exact_mod_cast h)
      · refine Or.inr ?_
        have hr : (N:ℝ) ≤ (S.card:ℝ)+2 := by exact_mod_cast h
        have hcard : (S.card:ℝ) ≤ (N:ℝ) := ec_card_le S
        linarith
  simp only [exactCountSuccessMass]
  exact ec_success_constant.trans (ec_joint_assembly
    (fun z : Fin (exactCountM₀ N) =>
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z)
    (fun z => (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).nonneg z)
    (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).sum_one
    (Finset.univ.filter (fun z : Fin (exactCountM₀ N) =>
      |(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
        Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) + 1/4))
    (ec_good_mass N hN S hM₀)
    (fun z₁ z₂ => ∑ y ∈ Finset.univ.filter
      (fun y : Fin (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) =>
        exactCountOutput N y = ((S.card : ℕ) : ℤ)),
      (aeLaw (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (hM z₁ z₂)).prob y)
    (fun z₁ z₂ => Finset.sum_nonneg (fun y _ =>
      (aeLaw (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (hM z₁ z₂)).nonneg y))
    (fun z₁ hz₁ z₂ hz₂ => ec_conditional_final hN S hM₀ hM z₁ z₂ (hR z₁ hz₁) (hR z₂ hz₂)))

/-- Bounds a nonnegative integer by a base term and the dyadic layers below a finite cap. -/
private theorem ec_dyadic_layer (c : ℝ) (hc : 0 ≤ c) (m J : ℕ) (hm : (m:ℝ) ≤ c*(2:ℝ)^J) :
    (m:ℝ) ≤ 2*c + ∑ j ∈ Finset.range J,
      (if c*(2:ℝ)^j < (m:ℝ) then 2*c*(2:ℝ)^j else 0) := by
  have htermnn : ∀ j : ℕ, (0:ℝ) ≤ (if c*(2:ℝ)^j < (m:ℝ) then 2*c*(2:ℝ)^j else 0) := by
    intro j
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hc)
        (pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) j)
    · exact le_rfl
  induction J generalizing m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have h1 : (m:ℝ) ≤ c*(2:ℝ)^0 := hm
    simp only [pow_zero, mul_one] at h1
    linarith
  | succ J ih =>
    rw [Finset.sum_range_succ]
    by_cases hmJ : (m:ℝ) ≤ c*(2:ℝ)^J
    · rw [if_neg (not_lt.mpr hmJ)]
      have hstep := ih m hmJ htermnn
      have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.range J,
          (if c*(2:ℝ)^j < (m:ℝ) then 2*c*(2:ℝ)^j else 0) :=
        Finset.sum_nonneg (fun j _ => htermnn j)
      linarith
    · have hlt : c*(2:ℝ)^J < (m:ℝ) := lt_of_not_ge hmJ
      rw [if_pos hlt]
      have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.range J,
          (if c*(2:ℝ)^j < (m:ℝ) then 2*c*(2:ℝ)^j else 0) :=
        Finset.sum_nonneg (fun j _ => htermnn j)
      have hterm : (m:ℝ) ≤ 2*c*(2:ℝ)^J := by
        rwa [show c*(2:ℝ)^(J+1) = 2*c*(2:ℝ)^J from by rw [pow_succ]; ring] at hm
      linarith

/-- The first `J` terms of the geometric series with ratio 1/2 sum to `2 - 2 * (1/2)^J`. -/
private theorem ec_half_pow_sum (J : ℕ) :
    ∑ j ∈ Finset.range J, (1/2:ℝ)^j = 2 - 2*((1/2:ℝ)^J) := by
  induction J with
  | zero => norm_num
  | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- The square of the reciprocal of `2^j` equals `(1/4)^j`. -/
private theorem ec_one_half_sq (j : ℕ) :
    ((1:ℝ)/((2:ℝ)^j))*((1:ℝ)/((2:ℝ)^j)) = ((1:ℝ)/4)^j := by
  have h1 : (1:ℝ)/((2:ℝ)^j) = ((1:ℝ)/2)^j := by rw [one_div, ← inv_pow, one_div]
  rw [h1, ← pow_add, show ((1:ℝ)/4) = ((1:ℝ)/2)*((1:ℝ)/2) from by norm_num, mul_pow]
  exact pow_add _ j j

/-- The product `2^j * (1/4)^j` equals `(1/2)^j`. -/
private theorem ec_two_four (j : ℕ) : (2:ℝ)^j*((1:ℝ)/4)^j = ((1:ℝ)/2)^j := by
  rw [← mul_pow]
  norm_num

/-- A dyadic tail bound of `(1/4)^j` and a finite cap bound the expected integer-valued cost by
`6 * c`. -/
private theorem ec_dyadic_expectation {M : ℕ} (p : Fin M → ℝ)
    (F : Fin M → Fin M → ℕ) (c : ℝ) (hc : 0 ≤ c)
    (h0 : ∀ z, 0 ≤ p z) (h1 : ∑ z, p z = 1) (J : ℕ)
    (ht : ∀ j : ℕ, ∑ z₁, ∑ z₂, p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0))
          ≤ ((1:ℝ)/4)^j)
    (hcap : ∀ z₁ z₂, (F z₁ z₂ : ℝ) ≤ c*(2:ℝ)^J) :
    ∑ z₁, ∑ z₂, p z₁*(p z₂*((F z₁ z₂ : ℝ))) ≤ 6*c := by
  classical
  have hlayer : ∀ z₁ z₂, (F z₁ z₂ : ℝ) ≤ 2*c + ∑ j ∈ Finset.range J,
      (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0) :=
    fun z₁ z₂ => ec_dyadic_layer c hc _ _ (hcap z₁ z₂)
  have hmono : ∀ z₁ z₂ : Fin M, p z₁*(p z₂*((F z₁ z₂ : ℝ)))
      ≤ p z₁*(p z₂*(2*c + ∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))) :=
    fun z₁ z₂ => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hlayer z₁ z₂) (h0 z₂)) (h0 z₁)
  have hsplit : ∀ z₁ z₂ : Fin M, p z₁*(p z₂*(2*c + ∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0)))
      = p z₁*(p z₂*(2*c)) + p z₁*(p z₂*(∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))) := fun z₁ z₂ => by ring
  have hconst : ∀ (j : ℕ) (z₁ z₂ : Fin M),
      p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))
      = 2*c*(2:ℝ)^j*(p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0))) := by
    intro j z₁ z₂
    by_cases hE : c*(2:ℝ)^j < (F z₁ z₂ : ℝ)
    · rw [if_pos hE, if_pos hE]; ring
    · rw [if_neg hE, if_neg hE]; ring
  have hstep2 : (∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁*(p z₂*(2*c + ∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))))
      = (∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁*(p z₂*(2*c))) +
        (∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁*(p z₂*(∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0)))) := by
    rw [Finset.sum_congr rfl (fun z₁ _ =>
      Finset.sum_congr rfl (fun z₂ _ => hsplit z₁ z₂))]
    simp only [Finset.sum_add_distrib]
  have hstep4 : (∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁*(p z₂*(∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))))
      = ∑ j ∈ Finset.range J, 2*c*(2:ℝ)^j*(∑ z₁ : Fin M, ∑ z₂ : Fin M,
          p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0))) := by
    have hshape : ∀ z₁ z₂ : Fin M, p z₁*(p z₂*(∑ j ∈ Finset.range J,
        (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0)))
        = ∑ j ∈ Finset.range J,
          (p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))) := by
      intro z₁ z₂
      rw [Finset.mul_sum, Finset.mul_sum]
    have hswap : (∑ z₁ : Fin M, ∑ z₂ : Fin M, ∑ j ∈ Finset.range J,
          (p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))))
        = ∑ j ∈ Finset.range J, ∑ z₁ : Fin M, ∑ z₂ : Fin M,
          (p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))) :=
      ec_sum_swap3 (fun z₁ z₂ j =>
        p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))) (Finset.range J)
    have hpull2 : ∀ j : ℕ, (∑ z₁ : Fin M, ∑ z₂ : Fin M,
          (p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))))
        = 2*c*(2:ℝ)^j*(∑ z₁ : Fin M, ∑ z₂ : Fin M,
          p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0))) := by
      intro j
      have hinner : ∀ z₁ : Fin M, (∑ z₂ : Fin M,
          (2*c*(2:ℝ)^j*(p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0)))))
          = 2*c*(2:ℝ)^j*(∑ z₂ : Fin M,
          (p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0)))) := by
        intro z₁
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun z₁ _ =>
          Finset.sum_congr rfl (fun z₂ _ => hconst j z₁ z₂)),
        Finset.sum_congr rfl (fun z₁ _ => hinner z₁)]
      simp only [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun z₁ _ => Finset.sum_congr rfl (fun z₂ _ => hshape z₁ z₂)),
      hswap, Finset.sum_congr rfl (fun j _ => hpull2 j)]
  calc ∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁*(p z₂*((F z₁ z₂ : ℝ)))
      ≤ ∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁*(p z₂*(2*c + ∑ j ∈ Finset.range J,
          (if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then 2*c*(2:ℝ)^j else 0))) :=
        Finset.sum_le_sum (fun z₁ _ => Finset.sum_le_sum (fun z₂ _ => hmono z₁ z₂))
    _ = 2*c + ∑ j ∈ Finset.range J, 2*c*(2:ℝ)^j*(∑ z₁ : Fin M, ∑ z₂ : Fin M,
          p z₁*(p z₂*(if c*(2:ℝ)^j < (F z₁ z₂ : ℝ) then (1:ℝ) else 0))) := by
          rw [hstep2, ec_double_sum_const p h1 (2*c), hstep4]
    _ ≤ 2*c + ∑ j ∈ Finset.range J, 2*c*(2:ℝ)^j*((1:ℝ)/4)^j := by
          refine add_le_add le_rfl (Finset.sum_le_sum (fun j _ => ?_))
          exact mul_le_mul_of_nonneg_left (ht j)
            (mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hc)
              (pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) j))
    _ = 2*c + ∑ j ∈ Finset.range J, 2*c*((1:ℝ)/2)^j := by
          apply congrArg
          apply Finset.sum_congr rfl
          intro j _
          rw [show 2*c*(2:ℝ)^j*((1:ℝ)/4)^j = 2*c*((2:ℝ)^j*((1:ℝ)/4)^j) from by ring,
            ec_two_four j]
    _ = 6*c - 4*c*((1/2:ℝ)^J) := by
          have hgeom := ec_half_pow_sum J
          rw [← Finset.mul_sum, hgeom]
          ring
    _ ≤ 6*c := by
          have hnn : (0:ℝ) ≤ 4*c*((1/2:ℝ)^J) :=
            mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) hc)
              (pow_nonneg (show (0:ℝ) ≤ (1/2:ℝ) by norm_num) J)
          linarith

/-- A preliminary estimate in the stated `k`-window has rough scale at most `3 * k * sqrt ((t +
1) * (N - t + 1))`. -/
private theorem ec_rough_R_bound (N : ℕ) (hN : 0 < N) (t : ℝ) (ht0 : 0 ≤ t)
    (htN : t ≤ (N:ℝ)) (k : ℝ) (hk1 : 1 ≤ k) (x : ℝ) (hx0 : 0 ≤ x) (hxN : x ≤ (N:ℝ))
    (hwin : |x-t| ≤ k*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)) + k^2) :
    exactCountRough N x ≤ 3*k*Real.sqrt ((t+1)*((N:ℝ)-t+1)) := by
  have hk2 : (0:ℝ) ≤ k := by linarith [hk1]
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hD : 0 ≤ t*((N:ℝ)-t) := mul_nonneg ht0 (by linarith)
  have hB := Real.sqrt_nonneg ((t+1)*((N:ℝ)-t+1))
  have hid : (t+1)*((N:ℝ)-t+1) = (N:ℝ)+1 + t*((N:ℝ)-t) := by ring
  have hBsq : (Real.sqrt ((t+1)*((N:ℝ)-t+1)))^2 = (t+1)*((N:ℝ)-t+1) :=
    Real.sq_sqrt (by linarith [hid, hD, hNnn])
  have hBnn : (0:ℝ) ≤ (t+1)*((N:ℝ)-t+1) := by linarith [hid, hD, hNnn]
  have hNB : (N:ℝ) ≤ (t+1)*((N:ℝ)-t+1) := by linarith [hid, hD, hNnn]
  have hDB : t*((N:ℝ)-t) ≤ (t+1)*((N:ℝ)-t+1) := by linarith [hid, hD, hNnn]
  have hnn : (0:ℝ) ≤ (N:ℝ)*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hNDsq : (N:ℝ)*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)) ≤ (t+1)*((N:ℝ)-t+1) := by
    have hsq : ((N:ℝ)*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)))^2 = (N:ℝ)*(t*((N:ℝ)-t)) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hD (Nat.cast_nonneg _))]
      field_simp
    have hXX : ((t+1)*((N:ℝ)-t+1))*((t+1)*((N:ℝ)-t+1))
        = ((t+1)*((N:ℝ)-t+1))^2 := by ring
    have hND4' : ((N:ℝ)*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)))^2
        ≤ ((t+1)*((N:ℝ)-t+1))^2 := by
      rw [hsq, ← hXX]
      exact mul_le_mul hNB hDB hD hBnn
    have habs := sq_le_sq.mp hND4'
    rwa [abs_of_nonneg hnn, abs_of_nonneg hBnn] at habs
  have hRsq : (x+1)*((N:ℝ)-x+1) ≤ (t+1)*((N:ℝ)-t+1) + (N:ℝ)*|x-t| := by
    have h1 : ((N:ℝ)-2*t)*(x-t) ≤ (N:ℝ)*|x-t| := by
      have h2 := le_abs_self (((N:ℝ)-2*t)*(x-t))
      rw [abs_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_nonneg _))
    have hid2 : (x+1)*((N:ℝ)-x+1)
        = (t+1)*((N:ℝ)-t+1) + ((N:ℝ)-2*t)*(x-t) - (x-t)*(x-t) := by ring
    have hE : (0:ℝ) ≤ (x-t)*(x-t) := mul_self_nonneg (x-t)
    linarith [h1, hE]
  have hNabs : (N:ℝ)*|x-t| ≤ (k+k^2)*((t+1)*((N:ℝ)-t+1)) := by
    have e1 : ((N:ℝ)*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)))*k
        ≤ ((t+1)*((N:ℝ)-t+1))*k :=
      mul_le_mul_of_nonneg_right hNDsq (show (0:ℝ) ≤ k by linarith [hk1])
    have e2 : ((N:ℝ))*(k^2) ≤ ((t+1)*((N:ℝ)-t+1))*(k^2) :=
      mul_le_mul_of_nonneg_right hNB (sq_nonneg k)
    calc (N:ℝ)*|x-t| ≤ (N:ℝ)*(k*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ)) + k^2) :=
          mul_le_mul_of_nonneg_left hwin hNnn
      _ = k*((N:ℝ)*Real.sqrt (t*((N:ℝ)-t)/(N:ℝ))) + k^2*(N:ℝ) := by ring
      _ ≤ k*((t+1)*((N:ℝ)-t+1)) + k^2*((t+1)*((N:ℝ)-t+1)) := by linarith
      _ = (k+k^2)*((t+1)*((N:ℝ)-t+1)) := by ring
  have hkp : (0:ℝ) ≤ k*(k-1) := mul_nonneg hk2 (show (0:ℝ) ≤ k-1 by linarith [hk1])
  have hid1 : (k-1)*(k+1) = k^2-1 := by ring
  have hid2k : k*(k-1) = k^2-k := by ring
  have h81 : (0:ℝ) ≤ 8*(k^2)-k-1 := by
    have hk11 : 0 ≤ (k-1)*(k+1) := mul_nonneg (by linarith [hk1]) (by linarith [hk1])
    linarith [hid1, hid2k, hk11, hkp, hk1]
  have hR2 : (x+1)*((N:ℝ)-x+1) ≤ (3*k*Real.sqrt ((t+1)*((N:ℝ)-t+1)))^2 := by
    have heq : (3*k*Real.sqrt ((t+1)*((N:ℝ)-t+1)))^2
        = 9*(k^2)*((t+1)*((N:ℝ)-t+1)) := by
      rw [mul_pow, mul_pow, hBsq]
      ring
    rw [heq]
    have hmid : (x+1)*((N:ℝ)-x+1) ≤ (1+k+k^2)*((t+1)*((N:ℝ)-t+1)) := by
      have hexp : (1+k+k^2)*((t+1)*((N:ℝ)-t+1))
          = ((t+1)*((N:ℝ)-t+1)) + (k+k^2)*((t+1)*((N:ℝ)-t+1)) := by ring
      rw [hexp]
      linarith [hRsq, hNabs]
    have hfin2 : (1+k+k^2)*((t+1)*((N:ℝ)-t+1)) ≤ 9*(k^2)*((t+1)*((N:ℝ)-t+1)) := by
      have hid3 : 9*(k^2)*((t+1)*((N:ℝ)-t+1))
          = (1+k+k^2)*((t+1)*((N:ℝ)-t+1)) + (8*(k^2)-k-1)*((t+1)*((N:ℝ)-t+1)) := by ring
      rw [hid3]
      have hnn2 : (0:ℝ) ≤ (8*(k^2)-k-1)*((t+1)*((N:ℝ)-t+1)) :=
        mul_nonneg h81 hBnn
      linarith
    exact hmid.trans hfin2
  have hRnn : 0 ≤ exactCountRough N x := Real.sqrt_nonneg _
  have hRsqid : (exactCountRough N x)^2 = (x+1)*((N:ℝ)-x+1) :=
    Real.sq_sqrt (mul_nonneg (by linarith [hx0]) (by linarith [hx0, hxN]))
  have hfinal : exactCountRough N x ≤ 3*k*Real.sqrt ((t+1)*((N:ℝ)-t+1)) := by
    have h9 : (exactCountRough N x)^2 ≤ (3*k*Real.sqrt ((t+1)*((N:ℝ)-t+1)))^2 := by
      rw [hRsqid]
      exact hR2
    have habs := sq_le_sq.mp h9
    rwa [abs_of_nonneg hRnn, abs_of_nonneg
      (mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 3 by norm_num) hk2) hB)] at habs
  exact hfinal

/-- If the first preliminary estimate lies in its `k`-window, the adaptive grid is at most `120
* k` times the target rough scale. -/
private theorem ec_grid_le_of_window (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
    (k : ℝ) (hk1 : 1 ≤ k) (z₁ z₂ : Fin (exactCountM₀ N))
    (hwin : |(N:ℝ)*aeEstimate (exactCountM₀ N) z₁-(S.card:ℝ)| ≤
      k*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) + k^2) :
    ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)
      ≤ 120*k*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
  have hB := Real.sqrt_nonneg (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))
  have hcard : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hgap : (0:ℝ) ≤ (N:ℝ)-(S.card:ℝ) := by linarith [ec_card_le S]
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hB1 : 1 ≤ Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    refine Real.one_le_sqrt.mpr ?_
    have hid : ((S.card:ℝ)+1)*((N:ℝ)-(S.card:ℝ)+1)
        = (N:ℝ)+1+(S.card:ℝ)*((N:ℝ)-(S.card:ℝ)) := by ring
    linarith [hid, mul_nonneg hcard hgap, hNnn]
  have hR₁ := ec_rough_R_bound N hN (S.card:ℝ) (Nat.cast_nonneg _) (ec_card_le S) k hk1
    ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
    (ec_readout_mem N (exactCountM₀ N) z₁).1 (ec_readout_mem N (exactCountM₀ N) z₁).2 hwin
  have hmin : min (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁))
      (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂))
      ≤ exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) := min_le_left _ _
  have h30 : 30*(min (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁))
      (exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)))
      ≤ 30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) :=
    mul_le_mul_of_nonneg_left hmin (by norm_num)
  have hc1 : exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)
      ≤ Nat.ceil (30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)) :=
    Nat.ceil_le_ceil h30
  have hc2 : ((Nat.ceil (30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)) : ℕ) : ℝ)
      ≤ 30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) + 1 :=
    (Nat.ceil_lt_add_one (show (0:ℝ) ≤ 30*exactCountRough N
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) from mul_nonneg (by norm_num)
        (Real.sqrt_nonneg _))).le
  have h90 : 30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ≤ 90*k*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    have h3 := mul_le_mul_of_nonneg_left hR₁ (show (0:ℝ) ≤ 3 by norm_num)
    linarith
  calc ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
      ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)
      ≤ ((Nat.ceil (30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)) : ℕ) : ℝ) :=
        by exact_mod_cast hc1
    _ ≤ 30*exactCountRough N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) + 1 := hc2
    _ ≤ 90*k*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) + 1 := by linarith [h90]
    _ ≤ 120*k*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
        nlinarith [hk1, hB1, hB]

/-- A natural-valued function on a finite type has a uniform dyadic upper bound. -/
private theorem ec_exists_dyadic_cap {ι : Type} [Fintype ι] (F : ι → ℕ) :
    ∃ J : ℕ, ∀ z : ι, (F z : ℝ) ≤ (2:ℝ)^J := by
  refine ⟨Finset.sup Finset.univ F, fun z => ?_⟩
  have h1 : (F z : ℝ) ≤ ((Finset.sup Finset.univ F : ℕ) : ℝ) := by
    exact_mod_cast Finset.le_sup (Finset.mem_univ z)
  have h3 : ((Finset.sup Finset.univ F : ℕ) : ℝ)
      ≤ ((2^(Finset.sup Finset.univ F) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := Finset.sup Finset.univ F)).le
  have h4 : ((2^(Finset.sup Finset.univ F) : ℕ) : ℝ)
      = (2:ℝ)^(Finset.sup Finset.univ F) := by
    push_cast
    rfl
  rw [h4] at h3
  linarith

/-- The exact-counting expected cost is at most `1000 * sqrt ((S.card + 1) * (N - S.card + 1))`
for valid grids. -/
private theorem ec_cost_positive {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ exactCountM₀ N)
    (hM : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) :
    exactCountCostMass hN S hM₀ hM ≤
      1000*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
  classical
  have hcard : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
  have hgap : (0:ℝ) ≤ (N:ℝ)-(S.card:ℝ) := by linarith [ec_card_le S]
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hBnn : (0:ℝ) ≤ ((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1) := by
    have hid : ((S.card:ℝ)+1)*((N:ℝ)-(S.card:ℝ)+1)
        = (N:ℝ)+1+(S.card:ℝ)*((N:ℝ)-(S.card:ℝ)) := by ring
    linarith [hid, mul_nonneg hcard hgap, hNnn]
  have hB := Real.sqrt_nonneg (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))
  have hB1 : 1 ≤ Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    refine Real.one_le_sqrt.mpr ?_
    have hid : ((S.card:ℝ)+1)*((N:ℝ)-(S.card:ℝ)+1)
        = (N:ℝ)+1+(S.card:ℝ)*((N:ℝ)-(S.card:ℝ)) := by ring
    linarith [hid, mul_nonneg hcard hgap, hNnn]
  have hc1 : (1:ℝ) ≤ 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    nlinarith [hB1]
  have hp0 : ∀ z : Fin (exactCountM₀ N), 0 ≤ (aeLaw (exactCountM₀ N) (QFTMatrix N)
      (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM₀).prob z := fun z =>
    (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).nonneg z
  have hp1 : ∑ z : Fin (exactCountM₀ N), (aeLaw (exactCountM₀ N) (QFTMatrix N)
      (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM₀).prob z = 1 :=
    (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).sum_one
  obtain ⟨J, hJcap⟩ := ec_exists_dyadic_cap
    (fun pr : Fin (exactCountM₀ N) × Fin (exactCountM₀ N) =>
      exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) pr.1)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) pr.2))
  have hcap : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)
        ≤ 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^J := by
    intro z₁ z₂
    have h1 := hJcap (z₁, z₂)
    exact h1.trans (le_mul_of_one_le_left
      (pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) J) hc1)
  have ht : ∀ j : ℕ, (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₁*
      ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₂*
      (if 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^j <
          ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
            ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) then (1:ℝ) else 0)))
        ≤ ((1:ℝ)/4)^j := by
    intro j
    by_cases hj : 1 ≤ j
    · have hk2 : (2:ℕ) ≤ 2^j := by
        have h1 : (2:ℕ)^1 ≤ 2^j :=
          Nat.pow_le_pow_right (show (2:ℕ) > 0 by norm_num) (show (1:ℕ) ≤ j by omega)
        simpa using h1
      have hkc : ((2^j : ℕ):ℝ) = (2:ℝ)^j := by
        push_cast
        rfl
      have hg : ∀ z : Fin (exactCountM₀ N), (0:ℝ) ≤
          (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
            ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
              ((2^j : ℕ):ℝ)^2) then
            (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
              (qftMatrix_unitary hN) hM₀).prob z else 0) := by
        intro z
        split_ifs
        · exact le_rfl
        · exact hp0 z
      have hq : (∑ z : Fin (exactCountM₀ N),
          (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
            ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
              ((2^j : ℕ):ℝ)^2) then
            (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
              (qftMatrix_unitary hN) hM₀).prob z else 0))
          ≤ 1/((2^j : ℕ):ℝ) := by
        rw [← Finset.sum_filter]
        have hwm := ec_window_mass N hN S hM₀ (2^j) hk2
        have hcm := ec_complement_mass
          (fun z : Fin (exactCountM₀ N) => (aeLaw (exactCountM₀ N) (QFTMatrix N)
            (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM₀).prob z) hp1
          (fun z : Fin (exactCountM₀ N) => |(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
            ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
              ((2^j : ℕ):ℝ)^2)
          (1/(2*(((2^j : ℕ):ℝ)-1))) hwm
        have hu : (2:ℝ) ≤ ((2^j : ℕ):ℝ) := by exact_mod_cast hk2
        have hconv : 1/(2*(((2^j : ℕ):ℝ)-1)) ≤ 1/((2^j : ℕ):ℝ) := by
          rw [div_le_div_iff₀ (by nlinarith [hu] : (0:ℝ) < 2*(((2^j : ℕ):ℝ)-1))
            (by nlinarith [hu] : (0:ℝ) < ((2^j : ℕ):ℝ))]
          nlinarith [hu]
        exact hcm.trans hconv
      have hpt : ∀ z₁ z₂ : Fin (exactCountM₀ N),
          (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₁*
          ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₂*
          (if 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^j <
              ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) then (1:ℝ) else 0))
          ≤ (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z₁-(S.card:ℝ)| ≤
              ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                ((2^j : ℕ):ℝ)^2) then
            (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
              (qftMatrix_unitary hN) hM₀).prob z₁ else 0)*
            (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z₂-(S.card:ℝ)| ≤
              ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                ((2^j : ℕ):ℝ)^2) then
            (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
              (qftMatrix_unitary hN) hM₀).prob z₂ else 0) := by
        intro z₁ z₂
        by_cases hE : 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^j <
            ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
              ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)
        · have hw₁ : ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z₁-(S.card:ℝ)| ≤
              ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                ((2^j : ℕ):ℝ)^2) := by
            intro hwin
            have hle := ec_grid_le_of_window N hN S ((2^j : ℕ):ℝ)
              (by rw [hkc]; exact one_le_pow₀ (by norm_num)) z₁ z₂ hwin
            rw [hkc] at hle
            linarith
          have hw₂ : ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z₂-(S.card:ℝ)| ≤
              ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                ((2^j : ℕ):ℝ)^2) := by
            intro hwin
            have hle := ec_grid_le_of_window N hN S ((2^j : ℕ):ℝ)
              (by rw [hkc]; exact one_le_pow₀ (by norm_num)) z₂ z₁ hwin
            rw [hkc] at hle
            have hswap : ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁) : ℕ) : ℝ)
                = ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) := by
              have hnat : (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)
                  ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁))
                  = (exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                  ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂)) := by
                unfold exactCountGrid
                rw [min_comm]
              rw [hnat]
            rw [hswap] at hle
            linarith
          rw [if_pos hE, if_pos hw₁, if_pos hw₂, mul_one]
        · rw [if_neg hE, mul_zero, mul_zero]
          exact mul_nonneg (hg z₁) (hg z₂)
      calc (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
          (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₁*
          ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₂*
          (if 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^j <
              ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) then (1:ℝ) else 0)))
          ≤ (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
              (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z₁-(S.card:ℝ)| ≤
                ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                  ((2^j : ℕ):ℝ)^2) then
                (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                  (qftMatrix_unitary hN) hM₀).prob z₁ else 0)*
              (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z₂-(S.card:ℝ)| ≤
                ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                  ((2^j : ℕ):ℝ)^2) then
                (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                  (qftMatrix_unitary hN) hM₀).prob z₂ else 0)) :=
            Finset.sum_le_sum (fun z₁ _ => Finset.sum_le_sum (fun z₂ _ => hpt z₁ z₂))
        _ = (∑ z : Fin (exactCountM₀ N),
              (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
                ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                  ((2^j : ℕ):ℝ)^2) then
              (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                (qftMatrix_unitary hN) hM₀).prob z else 0))*
            (∑ z : Fin (exactCountM₀ N),
              (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
                ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                  ((2^j : ℕ):ℝ)^2) then
              (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                (qftMatrix_unitary hN) hM₀).prob z else 0)) :=
            ec_double_sum_prod Finset.univ _ _
        _ ≤ (1/((2^j : ℕ):ℝ))*(1/((2^j : ℕ):ℝ)) := by
            have hnn0 : (0:ℝ) ≤ (∑ z : Fin (exactCountM₀ N),
                (if ¬ (|(N:ℝ)*aeEstimate (exactCountM₀ N) z-(S.card:ℝ)| ≤
                  ((2^j : ℕ):ℝ)*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)/(N:ℝ)) +
                    ((2^j : ℕ):ℝ)^2) then
                  (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                    (qftMatrix_unitary hN) hM₀).prob z else 0)) :=
              Finset.sum_nonneg (fun z _ => hg z)
            exact mul_le_mul hq hq hnn0
              (show (0:ℝ) ≤ 1/((2^j : ℕ):ℝ) by
                exact div_nonneg zero_le_one (Nat.cast_nonneg _))
        _ = ((1:ℝ)/4)^j := by rw [hkc]; exact ec_one_half_sq j
    · have hj0 : j = 0 := by omega
      subst hj0
      have hle : ∀ z₁ z₂ : Fin (exactCountM₀ N),
          (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₁*
          ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₂*
          (if 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^0 <
              ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) then (1:ℝ) else 0))
          ≤ (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₁*
            ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
              (qftMatrix_unitary hN) hM₀).prob z₂*(1:ℝ)) := by
        intro z₁ z₂
        have hind : (if 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^0 <
              ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) then (1:ℝ) else 0) ≤ 1 := by
          split_ifs
          · exact le_rfl
          · norm_num
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hind (hp0 z₂)) (hp0 z₁)
      calc (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
          (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₁*
          ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
            (qftMatrix_unitary hN) hM₀).prob z₂*
          (if 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))*(2:ℝ)^0 <
              ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
                ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) then (1:ℝ) else 0)))
          ≤ (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
              (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                (qftMatrix_unitary hN) hM₀).prob z₁*
              ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
                (qftMatrix_unitary hN) hM₀).prob z₂*(1:ℝ))) :=
            Finset.sum_le_sum (fun z₁ _ => Finset.sum_le_sum (fun z₂ _ => hle z₁ z₂))
        _ = (1:ℝ) := ec_double_sum_const _ hp1 1
        _ = ((1:ℝ)/4)^0 := (pow_zero _).symm
  have hc120 : (0:ℝ) ≤ 120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    nlinarith [hB1]
  have hdy6 : (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₁*
      ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₂*
      ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)))
      ≤ 6*(120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1))) :=
    ec_dyadic_expectation
      (fun z : Fin (exactCountM₀ N) => (aeLaw (exactCountM₀ N) (QFTMatrix N)
        (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM₀).prob z)
      (fun z₁ z₂ => exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂))
      (120*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)))
      hc120 hp0 hp1 J ht hcap
  have hdy : (∑ z₁ : Fin (exactCountM₀ N), ∑ z₂ : Fin (exactCountM₀ N),
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₁*
      ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₂*
      ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)))
      ≤ 720*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    linarith [hdy6]
  have hM₀lt : ((exactCountM₀ N : ℝ)) < 14*Real.pi*Real.sqrt (N:ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsN : Real.sqrt (N:ℝ) ≤ Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    refine Real.sqrt_le_sqrt ?_
    have hid : ((S.card:ℝ)+1)*((N:ℝ)-(S.card:ℝ)+1)
        = (N:ℝ)+1+(S.card:ℝ)*((N:ℝ)-(S.card:ℝ)) := by ring
    linarith [hid, mul_nonneg hcard hgap, hNnn]
  have hπN : 28*Real.pi*Real.sqrt (N:ℝ) ≤ 88*Real.sqrt (N:ℝ) := by
    nlinarith [ec_pi_lt_22_7,
      mul_nonneg (by norm_num : (0:ℝ) ≤ 28) (Real.sqrt_nonneg (N:ℝ))]
  have hM₀b : 2*((exactCountM₀ N : ℝ)) ≤
      90*Real.sqrt (((S.card : ℝ)+1)*((N : ℝ)-(S.card : ℝ)+1)) := by
    nlinarith [hM₀lt, hπN, hsN, hB1]
  simp only [exactCountCostMass]
  have hcast : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      (((2*(exactCountM₀ N : ℕ) + exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ))
      = 2*((exactCountM₀ N : ℝ)) + ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ) := by
    intro z₁ z₂
    push_cast
    ring
  have hshape : ∀ z₁ z₂ : Fin (exactCountM₀ N),
      ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₁*
      (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z₂)*
      (((2*(exactCountM₀ N : ℕ) + exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
        ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ))
      = (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).prob z₁*
        ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).prob z₂*(2*((exactCountM₀ N : ℝ))))
        + (aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).prob z₁*
        ((aeLaw (exactCountM₀ N) (QFTMatrix N) (⟨0,hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).prob z₂*
        ((exactCountGrid N ((N:ℝ)*aeEstimate (exactCountM₀ N) z₁)
          ((N:ℝ)*aeEstimate (exactCountM₀ N) z₂) : ℕ) : ℝ)) := by
    intro z₁ z₂
    rw [hcast z₁ z₂]
    ring
  rw [Finset.sum_congr rfl (fun z₁ _ => Finset.sum_congr rfl (fun z₂ _ => hshape z₁ z₂))]
  simp only [Finset.sum_add_distrib]
  rw [ec_double_sum_const (fun z : Fin (exactCountM₀ N) => (aeLaw (exactCountM₀ N)
      (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM₀).prob z) hp1
      (2*((exactCountM₀ N : ℝ)))]
  linarith [hdy, hM₀b, hB]

/-- Establishes exact-counting success probability at least `2/3` and the explicit expected-cost
bound in `Theorem17Spec.expected` [Brassard et al., Theorem 17][BrassardEtAl2002]. -/
theorem bhmt_theorem17_exact_count :
    Theorem17Spec.expected := by
  intro N hN S hM₀ hM
  by_cases hS : S.card = 0
  · refine ⟨?_, ?_⟩
    · rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.bhmt_exact_count_zero_success
        hN S hS hM₀ hM]
      norm_num
    · refine le_trans
        (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.bhmt_exact_count_zero_cost_bound
        hN S hS hM₀ hM) ?_
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      have hcard : (0:ℝ) ≤ (S.card:ℝ) := Nat.cast_nonneg _
      have hgap : (0:ℝ) ≤ (N:ℝ)-(S.card:ℝ) := by
        linarith [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ec_card_le S]
      have hid : ((S.card:ℝ)+1)*((N:ℝ)-(S.card:ℝ)+1)
          = (N:ℝ)+1+(S.card:ℝ)*((N:ℝ)-(S.card:ℝ)) := by ring
      have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
      linarith [hid, mul_nonneg hcard hgap, hNnn]
  · exact ⟨Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ec_success_positive hN S hM₀ hM,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ec_cost_positive hN S hM₀ hM⟩

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
