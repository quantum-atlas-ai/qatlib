/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical BigOperators

theorem basicApproxCountPrefixWeight_sum {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω) = 1 := by
  unfold basicApproxCountPrefixWeight
  have he : (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      ∏ l, (basicApproxCountLoopLaw hN S l).prob (ω l)) =
      ∑ ω ∈ Fintype.piFinset (fun l : Fin (basicApproxCountLoopCap N) =>
        (Finset.univ : Finset (Fin (2 * 2 ^ l.val)))),
          ∏ l, (basicApproxCountLoopLaw hN S l).prob (ω l) :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [he, ← Finset.prod_univ_sum]
  rw [Finset.prod_congr rfl (fun l _ => (basicApproxCountLoopLaw hN S l).sum_one)]
  simp

theorem basicApproxCountFinalZero_eq_one {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : S.card = 0) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    basicApproxCountFinalZero hN S ε ω hω = 1 := by
  let M := basicApproxCountFinalM ε (basicApproxCountStop N ω)
  let z : Fin M := ⟨0, by omega⟩
  let p := basicApproxCountFinalLaw hN S ε ω hω
  have ha : MeasureProb (preparedAAState (QFTMatrix N) ⟨0, hN⟩) S = 0 := by
    rw [prepared_qft_mark_mass, hS, Nat.cast_zero, zero_div]
  have hp : p.prob z = 1 :=
    (prepared_ae_bhmt_error_and_endpoints M hω (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN)).2.1 ha
  have hz : basicApproxCountOutput N ε ω z = 0 := by
    norm_num [basicApproxCountOutput, aeEstimate, z]
  unfold basicApproxCountFinalZero
  have hlow : 1 ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin M => basicApproxCountOutput N ε ω y = 0),
      p.prob y := by
    rw [← hp]
    exact Finset.single_le_sum (fun y _ => p.nonneg y) (by simp [hz])
  have hupp : (∑ y ∈ Finset.univ.filter (fun y : Fin M => basicApproxCountOutput N ε ω y = 0),
      p.prob y) ≤ 1 := by
    rw [← p.sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun y _ _ => p.nonneg y)
  exact le_antisymm hupp hlow

theorem bhmt_basic_approx_count_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : S.card = 0)
    (ε : ℝ) (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω * basicApproxCountFinalZero hN S ε ω (hω ω)) = 1 := by
  simp only [basicApproxCountFinalZero_eq_one hN S hS, mul_one]
  exact basicApproxCountPrefixWeight_sum hN S

theorem basicApproxCount_round_relative (t : ℕ) (ε x : ℝ) (hε : 0 < ε)
    (hx : |x - (t : ℝ)| ≤ ε * t / 3) :
    |((⌊x + 1 / 2⌋ : ℤ) : ℝ) - t| ≤ ε * t := by
  have hfloor0 := Int.floor_le (x + 1 / 2)
  have hfloor1 := Int.lt_floor_add_one (x + 1 / 2)
  by_cases hbig : 1 ≤ ε * t
  · have hr : |((⌊x + 1 / 2⌋ : ℤ) : ℝ) - x| ≤ 1 / 2 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hh := (abs_sub_le ((⌊x + 1 / 2⌋ : ℤ) : ℝ) x (t : ℝ)).trans (add_le_add hr hx)
    linarith
  · have he : (⌊x + 1 / 2⌋ : ℤ) = (t : ℤ) := by
      apply Int.floor_eq_iff.mpr
      have hxb := abs_le.mp hx
      have het : ε * t < 1 := lt_of_not_ge hbig
      push_cast
      constructor <;> linarith
    rw [he]
    norm_cast
    simp
    positivity

theorem basicApproxCountFinalGood_of_precision {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : 0 < S.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω))
    (hprec : 8 * Real.pi * Real.sqrt (N : ℝ) ≤
      ε * basicApproxCountFinalM ε (basicApproxCountStop N ω) * Real.sqrt (S.card : ℝ)) :
    8 / Real.pi ^ 2 ≤ basicApproxCountFinalGood hN S ε ω hω := by
  let M := basicApproxCountFinalM ε (basicApproxCountStop N ω)
  let t : ℝ := S.card
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ht : 0 < t := by dsimp only [t]; exact_mod_cast hS
  have htN : t ≤ N := by
    dsimp only [t]
    exact_mod_cast (show S.card ≤ N by simpa only [Fintype.card_fin] using! S.card_le_univ)
  change 8 * Real.pi * Real.sqrt (N : ℝ) ≤ ε * (M : ℝ) * Real.sqrt t at hprec
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hroott : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hd : 0 ≤ t * ((N : ℝ) - t) := mul_nonneg ht.le (sub_nonneg.mpr htN)
  have hR := Real.sqrt_nonneg (t * ((N : ℝ) - t))
  have hRsq := Real.sq_sqrt hd
  have hNsql := Real.sq_sqrt hNr.le
  have htsql := Real.sq_sqrt ht.le
  have hRbound : Real.sqrt (t * ((N : ℝ) - t)) ≤ Real.sqrt t * Real.sqrt (N : ℝ) := by
    have he : (Real.sqrt t * Real.sqrt (N : ℝ)) ^ 2 = t * N := by rw [mul_pow, htsql, hNsql]
    nlinarith [mul_nonneg hroott.le hrootN.le]
  have hfirst : 2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t)) / M ≤ ε * t / 4 := by
    apply (div_le_iff₀ hMr).mpr
    have hs := mul_le_mul_of_nonneg_right hprec hroott.le
    rw [mul_assoc (ε * (M : ℝ)), ← pow_two, htsql] at hs
    have hr := mul_le_mul_of_nonneg_left hRbound (by positivity : 0 ≤ 8 * Real.pi)
    nlinarith

  have hsecond : Real.pi ^ 2 * N / (M : ℝ) ^ 2 ≤ ε * t / 64 := by
    apply (div_le_iff₀ (sq_pos_of_pos hMr)).mpr
    have hp := pow_le_pow_left₀ (by positivity) hprec 2
    simp only [mul_pow, hNsql, htsql] at hp
    have he := mul_le_mul_of_nonneg_right hε1 (by positivity : 0 ≤ ε * t * (M : ℝ) ^ 2)
    nlinarith
  have hwindow : 2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t)) / M +
      Real.pi ^ 2 * N / (M : ℝ) ^ 2 ≤ ε * t / 3 := by
    have hep := mul_pos hε ht
    linarith
  have hgood := amplitude_counting_actual_consumer N M hN hω S
  unfold basicApproxCountFinalGood
  apply hgood.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    apply basicApproxCount_round_relative S.card ε _ hε
    exact hy.trans hwindow
  · intro y _ _
    exact (basicApproxCountFinalLaw hN S ε ω hω).nonneg y

theorem basicApproxCountLoopCap_power (N : ℕ) (hN : 0 < N) :
    2 * Real.sqrt (N : ℝ) ≤ (2 : ℝ) ^ basicApproxCountLoopCap N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < 2 * Real.sqrt (N : ℝ) := by positivity
  have hceil : Real.logb 2 (2 * Real.sqrt (N : ℝ)) ≤ (basicApproxCountLoopCap N : ℝ) :=
      Nat.le_ceil _
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hceil
  simpa only [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hp,
    Real.rpow_natCast] using! h

theorem basicApproxCountStop_pos (N : ℕ) (hN : 0 < N)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
    0 < basicApproxCountStop N ω := by
  have hcap : 0 < basicApproxCountLoopCap N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hN1
    have hpower := basicApproxCountLoopCap_power N hN
    by_contra h
    have hc : basicApproxCountLoopCap N = 0 := Nat.eq_zero_of_not_pos h
    rw [hc, pow_zero] at hpower
    linarith
  unfold basicApproxCountStop
  split
  · omega
  · exact hcap

theorem basicApproxCount_kernel_zero_lower (M : ℕ) (hM : 0 < M) (φ : ℝ) (hφ : φ ≠ 0) :
    (Real.sin (Real.pi * M * φ) / (Real.pi * M * φ)) ^ 2 ≤
      ‖qpeKernel M φ ⟨0, hM⟩‖ ^ 2 := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have h := qpeKernel_neighbour_lower M φ ⟨0, hM⟩ hM 0 0 ((M : ℝ) * φ) ((M : ℝ) * φ)
    (by simp) (by simp; field_simp) (mul_ne_zero hMr hφ)
  convert! h using 1
  rw [div_pow]
  congr 1
  · congr 1
    ring
  · ring

theorem basicApproxCount_loop_zero_lower {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : (S.card : ℝ) / N = Real.sin θ ^ 2)
    (l : Fin (basicApproxCountLoopCap N))
    (hsmall : (2 * 2 ^ l.val : ℝ) * θ ≤ 1 / 5) :
    1 - ((2 * 2 ^ l.val : ℝ) * θ) ^ 2 / 2 ≤
      (basicApproxCountLoopLaw hN S l).prob ⟨0, by positivity⟩ := by
  let M : ℕ := 2 * 2 ^ l.val
  have hM : 2 ≤ M := by
    dsimp [M]
    have hp : 0 < (2 : ℕ) ^ l.val := by positivity
    omega
  have hMp : 0 < M := by omega
  let x := (M : ℝ) * θ
  have hx : 0 < x := by dsimp [x]; positivity
  have hxsmall : x ≤ 1 / 5 := by
    simpa only [x, M, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using! hsmall
  have hsin : x - x ^ 3 / 4 < Real.sin x := by
    linarith [Real.sin_gt_sub_cube hx, pow_nonneg hx.le 3]
  have hr : 1 - x ^ 2 / 4 ≤ Real.sin x / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith
  have hsq := pow_le_pow_left₀ (by nlinarith : 0 ≤ 1 - x ^ 2 / 4) hr 2
  have henv : 1 - x ^ 2 / 2 ≤ (Real.sin x / x) ^ 2 := by nlinarith [sq_nonneg (x ^ 2)]
  have hplus :=
      basicApproxCount_kernel_zero_lower M hMp (θ / Real.pi) (div_ne_zero hθ0.ne' Real.pi_ne_zero)
  have hminus :=
      basicApproxCount_kernel_zero_lower M hMp (-θ / Real.pi)
      (div_ne_zero (neg_ne_zero.mpr hθ0.ne') Real.pi_ne_zero)
  have hπplus : Real.pi * (M : ℝ) * (θ / Real.pi) = x := by dsimp [x]; field_simp
  have hπminus : Real.pi * (M : ℝ) * (-θ / Real.pi) = -x := by dsimp [x]; field_simp
  rw [hπplus] at hplus
  rw [hπminus, Real.sin_neg, neg_div_neg_eq] at hminus
  have hmass : MeasureProb (preparedAAState (QFTMatrix N) ⟨0, hN⟩) S = Real.sin θ ^ 2 := by
    rw [prepared_qft_mark_mass, ha]
  have hdist := prepared_ae_two_phase_distribution M hM (QFTMatrix N) ⟨0, hN⟩ S
    (qftMatrix_unitary hN) θ hθ0 hθ1 hmass (⟨0, hMp⟩ : Fin M)
  change _ ≤ (aeLaw M (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN) hM).prob ⟨0, hMp⟩
  have hex : (2 * 2 ^ l.val : ℝ) * θ = x := by
    simp only [x, M, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [hex]
  rw [hdist]
  nlinarith

theorem basicApproxCount_product_defect {X : Type*} [DecidableEq X]
    (s : Finset X) (p : X → ℝ) (hp0 : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∀ x ∈ s, p x ≤ 1) :
    1 - ∑ x ∈ s, (1 - p x) ≤ ∏ x ∈ s, p x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hprod0 : 0 ≤ ∏ x ∈ s, p x :=
        Finset.prod_nonneg (fun x hx => hp0 x (Finset.mem_insert_of_mem hx))
    have hprod1 : (∏ x ∈ s, p x) ≤ 1 := Finset.prod_le_one₀
      (fun x hx => hp0 x (Finset.mem_insert_of_mem hx)) (fun x hx => hp1 x (Finset.mem_insert_of_mem hx))
    have hbase := ih (fun x hx => hp0 x (Finset.mem_insert_of_mem hx))
      (fun x hx => hp1 x (Finset.mem_insert_of_mem hx))
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hpa0 := hp0 a (Finset.mem_insert_self _ _)
    have hpa1 := hp1 a (Finset.mem_insert_self _ _)
    nlinarith

private noncomputable def loopZeroMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (l : Fin (basicApproxCountLoopCap N)) : ℝ :=
  ∑ z : Fin (2 * 2 ^ l.val),
    if (N : ℝ) * aeEstimate (2 * 2 ^ l.val) z = 0 then (basicApproxCountLoopLaw hN S l).prob z else 0

private theorem loopZeroMass_bounds {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (l : Fin (basicApproxCountLoopCap N)) : 0 ≤ loopZeroMass hN S l ∧ loopZeroMass hN S l ≤ 1 := by
  let p := basicApproxCountLoopLaw hN S l
  constructor
  · exact Finset.sum_nonneg (fun z _ => by split_ifs <;> first | exact p.nonneg z | exact le_rfl)
  · rw [← p.sum_one]
    apply Finset.sum_le_sum
    intro z _
    split_ifs <;> first | exact le_rfl | exact p.nonneg z

private theorem loopZeroMass_ge_label_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (l : Fin (basicApproxCountLoopCap N)) :
    (basicApproxCountLoopLaw hN S l).prob ⟨0, by positivity⟩ ≤ loopZeroMass hN S l := by
  unfold loopZeroMass
  have hz : (N : ℝ) * aeEstimate (2 * 2 ^ l.val) (⟨0, by positivity⟩ : Fin (2 * 2 ^ l.val)) = 0 := by
    simp [aeEstimate]
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun z : Fin (2 * 2 ^ l.val) => if (N : ℝ) * aeEstimate (2 * 2 ^ l.val) z = 0
      then (basicApproxCountLoopLaw hN S l).prob z else 0)
    (fun z _ => by (try dsimp only); split_ifs <;> first | exact (basicApproxCountLoopLaw hN S l).nonneg z | exact le_rfl)
    (show (⟨0, by positivity⟩ : Fin (2 * 2 ^ l.val)) ∈ Finset.univ by simp)
  simpa only [if_pos hz] using! h

private noncomputable def prefixZero (N n : ℕ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : Prop :=
  ∀ l : Fin (basicApproxCountLoopCap N), l.val < n → basicApproxCountObserved N ω l = 0

theorem basicApproxCount_prefix_zero_factor {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (n : ℕ) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      if prefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0) =
      ∏ l : Fin (basicApproxCountLoopCap N), if l.val < n then loopZeroMass hN S l else 1 := by
  let q := fun (l : Fin (basicApproxCountLoopCap N)) (z : Fin (2 * 2 ^ l.val)) =>
    (basicApproxCountLoopLaw hN S l).prob z *
      if l.val < n → (N : ℝ) * aeEstimate (2 * 2 ^ l.val) z = 0 then (1 : ℝ) else 0
  have he (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
      (if prefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0) = ∏ l, q l (ω l) := by
    dsimp [q]
    rw [Finset.prod_mul_distrib, Fintype.prod_boole]
    unfold basicApproxCountPrefixWeight prefixZero basicApproxCountObserved
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun ω _ => he ω)]
  have hswap : (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val), ∏ l, q l (ω l)) =
      ∑ ω ∈ Fintype.piFinset (fun l : Fin (basicApproxCountLoopCap N) =>
        (Finset.univ : Finset (Fin (2 * 2 ^ l.val)))), ∏ l, q l (ω l) :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [hswap, ← Finset.prod_univ_sum]
  apply Finset.prod_congr rfl
  intro l _
  by_cases hl : l.val < n
  · simp only [if_pos hl]
    unfold loopZeroMass
    apply Finset.sum_congr rfl
    intro z _
    dsimp [q]
    simp only [hl, true_implies]
    split_ifs <;> simp
  · simp only [if_neg hl]
    have hsum := (basicApproxCountLoopLaw hN S l).sum_one
    simpa [q, hl] using! hsum

private theorem fin_prefix_sum (L n : ℕ) (hn : n ≤ L) (f : ℕ → ℝ) :
    (∑ l : Fin L, if l.val < n then f l.val else 0) = ∑ l ∈ Finset.range n, f l := by
  change (∑ l : Fin L, (fun k : ℕ => if k < n then f k else 0) l.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < n then f k else 0), ← Finset.sum_filter]
  have he : (Finset.range L).filter (fun l => l < n) = Finset.range n := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]

private theorem sum_doubling_squares (n : ℕ) (θ : ℝ) :
    (∑ l ∈ Finset.range n, ((2 * 2 ^ l : ℝ) * θ) ^ 2) ≤ 2 * ((2 : ℝ) ^ n * θ) ^ 2 := by
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ (2 : ℝ) n]
    nlinarith [sq_nonneg ((2 : ℝ) ^ n * θ)]

theorem basicApproxCount_prefix_zero_lower {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : (S.card : ℝ) / N = Real.sin θ ^ 2)
    (n : ℕ) (hn : n ≤ basicApproxCountLoopCap N)
    (hsmall : (2 : ℝ) ^ n * θ ≤ 1 / 5) :
    (7 / 8 : ℝ) ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      if prefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0 := by
  let p := fun l : Fin (basicApproxCountLoopCap N) => if l.val < n then loopZeroMass hN S l else 1
  have hp0 (l : Fin (basicApproxCountLoopCap N)) : 0 ≤ p l := by
    dsimp [p]
    split_ifs <;> first | exact (loopZeroMass_bounds hN S l).1 | norm_num
  have hp1 (l : Fin (basicApproxCountLoopCap N)) : p l ≤ 1 := by
    dsimp [p]
    split_ifs <;> first | exact (loopZeroMass_bounds hN S l).2 | exact le_rfl
  have hprod := basicApproxCount_product_defect Finset.univ p (fun l _ => hp0 l) (fun l _ => hp1 l)
  have herr (l : Fin (basicApproxCountLoopCap N)) :
      1 - p l ≤ if l.val < n then ((2 * 2 ^ l.val : ℝ) * θ) ^ 2 / 2 else 0 := by
    by_cases hl : l.val < n
    · have hpow : (2 * 2 ^ l.val : ℝ) ≤ (2 : ℝ) ^ n := by
        rw [← pow_succ']
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hθsmall : (2 * 2 ^ l.val : ℝ) * θ ≤ 1 / 5 :=
        (mul_le_mul_of_nonneg_right hpow hθ0.le).trans hsmall
      have hlabel := basicApproxCount_loop_zero_lower hN S θ hθ0 hθ1 ha l hθsmall
      have hz := loopZeroMass_ge_label_zero hN S l
      simp only [p, if_pos hl]
      linarith
    · simp [p, hl]
  have hsum := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => herr l)
  have hsum_eq := fin_prefix_sum (basicApproxCountLoopCap N) n hn
    (fun l => ((2 * 2 ^ l : ℝ) * θ) ^ 2 / 2)
  rw [hsum_eq] at hsum
  have hg := sum_doubling_squares n θ
  have hx : 0 ≤ (2 : ℝ) ^ n * θ := by positivity
  have hsq : ((2 : ℝ) ^ n * θ) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ hx hsmall 2
  have he : (∑ l ∈ Finset.range n, ((2 * 2 ^ l : ℝ) * θ) ^ 2 / 2) =
      (∑ l ∈ Finset.range n, ((2 * 2 ^ l : ℝ) * θ) ^ 2) / 2 := by rw [Finset.sum_div]
  rw [he] at hsum
  rw [basicApproxCount_prefix_zero_factor]
  change (7 / 8 : ℝ) ≤ ∏ l, p l
  nlinarith

theorem basicApproxCountStop_of_prefix {N n : ℕ} (hn : n + 1 ≤ basicApproxCountLoopCap N)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hz : prefixZero N n ω) : n + 1 ≤ basicApproxCountStop N ω := by
  unfold basicApproxCountStop
  split
  · rename_i l hl
    have hm := Fin.mem_find?_iff.mp hl
    have hnonzero : basicApproxCountObserved N ω l ≠ 0 := by simpa using! hm.1
    have hnle : n ≤ l.val := by
      by_contra h
      exact hnonzero (hz l (by omega))
    omega
  · exact hn

theorem basicApproxCount_precision_of_stop {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hangle : θ * Real.sqrt (N : ℝ) ≤ Real.pi / 2 * Real.sqrt (S.card : ℝ))
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hstop : (1 / 5 : ℝ) ≤ (2 : ℝ) ^ basicApproxCountStop N ω * θ) :
    8 * Real.pi * Real.sqrt (N : ℝ) ≤
      ε * basicApproxCountFinalM ε (basicApproxCountStop N ω) * Real.sqrt (S.card : ℝ) := by
  let M := basicApproxCountFinalM ε (basicApproxCountStop N ω)
  have hc : 20 * Real.pi ^ 2 / ε * (2 : ℝ) ^ basicApproxCountStop N ω ≤ (M : ℝ) := Nat.le_ceil _
  have hc' := mul_le_mul_of_nonneg_left hc hε.le
  have hcancel : ε * (20 * Real.pi ^ 2 / ε * (2 : ℝ) ^ basicApproxCountStop N ω) =
      20 * Real.pi ^ 2 * (2 : ℝ) ^ basicApproxCountStop N ω := by field_simp
  rw [hcancel] at hc'
  have hct := mul_le_mul_of_nonneg_right hc' hθ.le
  have hs := mul_le_mul_of_nonneg_left hstop (by positivity : 0 ≤ 20 * Real.pi ^ 2)
  have hlow : 4 * Real.pi ^ 2 ≤ ε * (M : ℝ) * θ := by nlinarith
  have hN0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hNpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hmul := mul_le_mul_of_nonneg_right hlow hN0
  have hang := mul_le_mul_of_nonneg_left hangle (by positivity : 0 ≤ ε * (M : ℝ))
  have hh : Real.pi * (8 * Real.pi * Real.sqrt (N : ℝ)) ≤
      Real.pi * (ε * (M : ℝ) * Real.sqrt (S.card : ℝ)) := by nlinarith
  exact le_of_mul_le_mul_left hh Real.pi_pos

theorem basicApproxCount_angle {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (hS : 0 < S.card) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ Real.pi / 2 ∧ (S.card : ℝ) / N = Real.sin θ ^ 2 ∧
      1 ≤ θ * Real.sqrt (N : ℝ) ∧
      θ * Real.sqrt (N : ℝ) ≤ Real.pi / 2 * Real.sqrt (S.card : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htr : (0 : ℝ) < S.card := by exact_mod_cast hS
  have htN : (S.card : ℝ) ≤ N := by exact_mod_cast
    (show S.card ≤ N by simpa only [Fintype.card_fin] using! S.card_le_univ)
  let a := (S.card : ℝ) / N
  have ha0 : 0 < a := div_pos htr hNr
  have ha1 : a ≤ 1 := (div_le_one hNr).mpr htN
  have hs0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hs1 : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha1
  let θ := Real.arcsin (Real.sqrt a)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr hs0
  have hθ1 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin θ = Real.sqrt a := Real.sin_arcsin (by linarith) hs1
  have he : Real.sin θ * Real.sqrt (N : ℝ) = Real.sqrt (S.card : ℝ) := by
    rw [hsin, show Real.sqrt a = Real.sqrt (S.card : ℝ) / Real.sqrt (N : ℝ) by
      dsimp [a]; rw [Real.sqrt_div (Nat.cast_nonneg _)]]
    exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hNr).ne'
  refine ⟨θ, hθ0, hθ1, ?_, ?_, ?_⟩
  · rw [hsin, Real.sq_sqrt ha0.le]
  · have hb := mul_le_mul_of_nonneg_right (Real.sin_le hθ0.le) (Real.sqrt_nonneg (N : ℝ))
    rw [he] at hb
    have ht1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS
    exact (Real.one_le_sqrt.mpr ht1).trans hb
  · have hj := Real.mul_le_sin hθ0.le hθ1
    have hj' := mul_le_mul_of_nonneg_left hj (Real.pi_div_two_pos.le)
    have hc : Real.pi / 2 * (2 / Real.pi * θ) = θ := by field_simp
    rw [hc] at hj'
    have hh := mul_le_mul_of_nonneg_right hj' (Real.sqrt_nonneg (N : ℝ))
    simpa only [mul_assoc, he] using! hh

theorem basicApproxCount_threshold (N : ℕ) (hN : 0 < N) (θ : ℝ)
    (hθ : 0 < θ) (hroot : 1 ≤ θ * Real.sqrt (N : ℝ)) :
    ∃ n : ℕ, n + 1 ≤ basicApproxCountLoopCap N ∧
      (1 / 5 : ℝ) < (2 : ℝ) ^ (n + 1) * θ ∧
      (n = 0 ∨ (2 : ℝ) ^ n * θ ≤ 1 / 5) := by
  let L := basicApproxCountLoopCap N
  have hcap := basicApproxCountLoopCap_power N hN
  have hcapθ := mul_le_mul_of_nonneg_right hcap hθ.le
  have hreach : (1 / 5 : ℝ) < (2 : ℝ) ^ L * θ := by dsimp [L]; nlinarith
  have hL : 0 < L := by
    by_contra h
    have hL0 : L = 0 := Nat.eq_zero_of_not_pos h
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs := Real.one_le_sqrt.mpr hN1
    change 2 * Real.sqrt (N : ℝ) ≤ (2 : ℝ) ^ L at hcap
    rw [hL0, pow_zero] at hcap
    linarith
  have hw : (1 / 5 : ℝ) < (2 : ℝ) ^ ((L - 1) + 1) * θ := by
    simpa only [Nat.sub_add_cancel hL] using! hreach
  have hex : ∃ k : ℕ, (1 / 5 : ℝ) < (2 : ℝ) ^ (k + 1) * θ := ⟨L - 1, hw⟩
  let n := Nat.find hex
  have hnL : n ≤ L - 1 := Nat.find_min' hex hw
  refine ⟨n, by dsimp [L] at *; omega, Nat.find_spec hex, ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    have hh := Nat.find_min hex (show n - 1 < Nat.find hex by dsimp [n] at *; omega)
    have he : n - 1 + 1 = n := by omega
    rw [he] at hh
    exact le_of_not_gt hh

theorem bhmt_basic_approx_count_positive {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : 0 < S.card) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    (2 / 3 : ℝ) ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω * basicApproxCountFinalGood hN S ε ω (hω ω) := by
  obtain ⟨θ, hθ0, hθ1, ha, hroot, hangle⟩ := basicApproxCount_angle hN S hS
  obtain ⟨n, hn, hcross, hnsmall⟩ := basicApproxCount_threshold N hN θ hθ0 hroot
  have hmass : (7 / 8 : ℝ) ≤
      ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        if prefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0 := by
    rcases hnsmall with hn0 | hnsmall
    · rw [hn0]
      have hz (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
          prefixZero N 0 ω := by intro l hl; omega
      simp only [if_pos (hz _), basicApproxCountPrefixWeight_sum]
      norm_num
    · have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hθsmall : θ ≤ 1 / 5 := by nlinarith
      have hstrict : θ < Real.pi / 2 := by linarith [Real.pi_gt_three]
      exact basicApproxCount_prefix_zero_lower hN S θ hθ0 hstrict ha n (by omega) hnsmall
  have hp0 (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
      0 ≤ basicApproxCountPrefixWeight hN S ω :=
    Finset.prod_nonneg (fun l _ => (basicApproxCountLoopLaw hN S l).nonneg (ω l))
  have hpoint (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) :
      (if prefixZero N n ω then basicApproxCountPrefixWeight hN S ω else 0) * (8 / Real.pi ^ 2) ≤
        basicApproxCountPrefixWeight hN S ω * basicApproxCountFinalGood hN S ε ω (hω ω) := by
    by_cases hz : prefixZero N n ω
    · rw [if_pos hz]
      have hstop := basicApproxCountStop_of_prefix hn ω hz
      have hp : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ basicApproxCountStop N ω :=
        pow_le_pow_right₀ (by norm_num) hstop
      have hstopθ : (1 / 5 : ℝ) ≤ (2 : ℝ) ^ basicApproxCountStop N ω * θ :=
        hcross.le.trans (mul_le_mul_of_nonneg_right hp hθ0.le)
      have hprec := basicApproxCount_precision_of_stop hN S ε θ hε hθ0 hangle ω hstopθ
      exact mul_le_mul_of_nonneg_left
        (basicApproxCountFinalGood_of_precision hN S hS ε hε hε1 ω (hω ω) hprec) (hp0 ω)
    · rw [if_neg hz, zero_mul]
      exact mul_nonneg (hp0 ω) (Finset.sum_nonneg
        (fun y _ => (basicApproxCountFinalLaw hN S ε ω (hω ω)).nonneg y))
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
  rw [← Finset.sum_mul] at hsum
  have hmass' := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 8 / Real.pi ^ 2)
  have hconst : (2 / 3 : ℝ) ≤ 7 / 8 * (8 / Real.pi ^ 2) := by
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hpisq : Real.pi ^ 2 ≤ 21 / 2 := by nlinarith
    field_simp
    nlinarith
  exact hconst.trans (hmass'.trans hsum)

theorem bhmt_basic_approx_count_success :
    Theorem15ApproxCountSpec.expected := by
  intro N S hN ε hε hε1 hω
  constructor
  · intro hS
    exact bhmt_basic_approx_count_zero hN S hS ε hω
  · intro hS
    exact bhmt_basic_approx_count_positive hN S hS ε hε hε1 hω

theorem bhmt_basic_approx_count_success_contract :
    Theorem15ApproxCountSpec.expected :=
  bhmt_basic_approx_count_success

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
