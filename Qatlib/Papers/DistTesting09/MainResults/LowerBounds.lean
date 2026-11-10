/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistTesting09.MainResults.Defs
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.DistTesting09.MainResults.Defs
set_option warningAsError false

namespace Qatlib.Papers.DistTesting09.MainResults.LowerBounds

variable {N : ℕ}

theorem theorem4_orthogonality_lower_bound (N : ℕ) (c : ℝ) (hc : 0 < c)
    (QC collQC : ℝ) (hred : collQC ≤ QC)
    (hcoll : c * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ collQC) :
    c * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ QC := by
  linarith

theorem lemma9_average_acceptance (S : ℕ) (Pacc : (Fin S → Fin S) → ℝ)
    (hacc : ∀ σ, (2 : ℝ) / 3 ≤ Pacc σ) :
    (2 : ℝ) / 3 ≤ (1 / (S.factorial : ℝ)) *
      ∑ σ : Equiv.Perm (Fin S), Pacc σ := by
  have hcardNat : 0 < Fintype.card (Equiv.Perm (Fin S)) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcard : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin S)) : ℝ) := by
    exact_mod_cast hcardNat
  have hsum : (2 : ℝ) / 3 * (Fintype.card (Equiv.Perm (Fin S)) : ℝ)
      ≤ ∑ σ : Equiv.Perm (Fin S), Pacc σ := by
    have h1 : (2 : ℝ) / 3 * (Fintype.card (Equiv.Perm (Fin S)) : ℝ)
        = ∑ _σ : Equiv.Perm (Fin S), (2 : ℝ) / 3 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring
    rw [h1]
    exact Finset.sum_le_sum fun σ _ => hacc σ
  have hfac : (S.factorial : ℝ) = (Fintype.card (Equiv.Perm (Fin S)) : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [hfac, one_div, inv_mul_eq_div, le_div_iff₀ hcard]
  exact hsum

theorem lemma9_classical_to_sampling (S : ℕ) (Pacc : (Fin S → Fin S) → ℝ)
    (Psamp η : ℝ) (hη : 0 ≤ η)
    (hacc : ∀ σ, (2 : ℝ) / 3 ≤ Pacc σ)
    (hclose : |Psamp - (1 / (S.factorial : ℝ)) *
      ∑ σ : Equiv.Perm (Fin S), Pacc σ| ≤ η) :
    (2 : ℝ) / 3 - η ≤ Psamp := by
  have havg := lemma9_average_acceptance S Pacc hacc
  have hle := (abs_le.mp hclose).1
  linarith

theorem l1_eq_two_sub_two_mul_min (p q : Dist N) :
    l1 p q = 2 - 2 * ∑ i, min (p.prob i) (q.prob i) := by
  have hpt : ∀ i : Fin N, |p.prob i - q.prob i|
      = p.prob i + q.prob i - 2 * min (p.prob i) (q.prob i) := by
    intro i
    by_cases h : p.prob i ≤ q.prob i
    · rw [abs_of_nonpos (by linarith), min_eq_left h]
      ring
    · have h' : q.prob i ≤ p.prob i := le_of_not_ge h
      rw [abs_of_nonneg (by linarith), min_eq_right h']
      ring
  unfold l1
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    p.sum_one, q.sum_one]
  ring

theorem lemma10_two_to_one (p q : Dist N) : l1 p q ≤ 2 := by
  rw [l1_eq_two_sub_two_mul_min]
  have hmin : (0 : ℝ) ≤ ∑ i, min (p.prob i) (q.prob i) :=
    Finset.sum_nonneg fun i _ => le_min (p.nonneg i) (q.nonneg i)
  linarith

theorem l1_hard_uniform [NeZero N] (p : Dist N)
    (hp : ∀ i : Fin N, p.prob i = if (i : ℕ) < N / 2 then 2 / (N : ℝ) else 0) :
    l1 p (uniform N) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hterm : ∀ i : Fin N, |p.prob i - (uniform N).prob i| = (N : ℝ)⁻¹ := by
    intro i
    rw [hp i, uniform_prob]
    by_cases h : (i : ℕ) < N / 2
    · rw [if_pos h]
      have hdiff : (2 : ℝ) / (N : ℝ) - (N : ℝ)⁻¹ = (N : ℝ)⁻¹ := by
        field_simp
        ring
      rw [hdiff, abs_of_nonneg (by positivity)]
    · rw [if_neg h]
      rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
  unfold l1
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hN

def moment (p : Dist N) (k : ℕ) : ℝ := ∑ i, p.prob i ^ k

theorem moment_uniform [NeZero N] (k : ℕ) (hk : 1 ≤ k) :
    moment (uniform N) k = 1 / (N : ℝ) ^ (k - 1) := by
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hk'' : k = (k-1)+1 := by omega
  unfold moment
  simp only [uniform_prob]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow]
  have hpow : (N:ℝ)^k = (N:ℝ)^(k-1) * (N:ℝ) := by
    conv_lhs => rw [hk'', pow_succ]
  rw [hpow, mul_inv_rev]
  rw [show (N:ℝ) * ((N:ℝ)⁻¹ * ((N:ℝ)^(k-1))⁻¹) = 1 * ((N:ℝ)^(k-1))⁻¹ by
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]]
  rw [div_eq_mul_inv]

def hardMoment (N k : ℕ) : ℝ := (2:ℝ) ^ (k - 1) / (N:ℝ) ^ (k - 1)

def unifMoment (N k : ℕ) : ℝ := 1 / (N:ℝ) ^ (k - 1)

def Mfive (N : ℕ) : ℝ := (1/32) * Real.sqrt (N:ℝ)

theorem Mfive_eq (N : ℕ) : Mfive N = (32:ℝ)⁻¹ * Real.sqrt (N:ℝ) := by
  unfold Mfive; rw [one_div]

theorem hard_moment_scaled_five (N k : ℕ) (hk : 2 ≤ k) (hN : 1 ≤ N) :
    (Mfive N) ^ k * hardMoment N k ≤ (1:ℝ) / 512 := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNr : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  have hsN : (Real.sqrt (N:ℝ))^2 = (N:ℝ) := Real.sq_sqrt hNr
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (N:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  have hsqrtpos : (0:ℝ) < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNpos
  unfold Mfive hardMoment
  rw [mul_pow]
  have hfrac : (Real.sqrt (N:ℝ))^k / (N:ℝ)^(k-1) ≤ 1 := by
    have hNp : (N:ℝ)^(k-1) = (Real.sqrt (N:ℝ))^(2*(k-1)) := by
      conv_lhs => rw [← hsN]
      exact (pow_mul (Real.sqrt (N:ℝ)) 2 (k-1)).symm
    rw [hNp, div_le_one (pow_pos hsqrtpos _)]
    apply pow_le_pow_right₀ hsqrt1
    omega
  have hA : ((1/32:ℝ))^k * (2:ℝ)^(k-1) ≤ (1:ℝ)/512 := by
    have hk'' : k = (k-1)+1 := by omega
    have hpow : ((1/32:ℝ))^k = (1/32)^(k-1) * (1/32) := by
      conv_lhs => rw [hk'', pow_succ]
    have hstep : ((1/32:ℝ))^k * (2:ℝ)^(k-1) = (1/32) * ((1/16:ℝ))^(k-1) := by
      rw [hpow]
      rw [show ((1/32:ℝ)^(k-1) * (1/32)) * (2:ℝ)^(k-1)
            = (1/32) * (((1/32:ℝ))^(k-1) * (2:ℝ)^(k-1)) by ring]
      rw [← mul_pow (1/32:ℝ) 2 (k-1)]
      norm_num
    rw [hstep]
    have hle : ((1/16:ℝ))^(k-1) ≤ (1/16)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_one] at hle
    nlinarith
  calc ((1/32:ℝ))^k * (Real.sqrt (N:ℝ))^k * ((2:ℝ)^(k-1)/(N:ℝ)^(k-1))
      = (((1/32:ℝ))^k * (2:ℝ)^(k-1)) * ((Real.sqrt (N:ℝ))^k / (N:ℝ)^(k-1)) := by ring
    _ ≤ ((1:ℝ)/512) * 1 := by
        apply mul_le_mul hA hfrac (by positivity) (by norm_num)
    _ = 1/512 := by ring

theorem unifMoment_le_hardMoment (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    unifMoment N k ≤ hardMoment N k := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  unfold unifMoment hardMoment
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ ((N:ℝ)^(k-1))⁻¹)
  have h0 : (0:ℕ) ≤ k-1 := by omega
  calc (1:ℝ) = (2:ℝ)^0 := by norm_num
    _ ≤ (2:ℝ)^(k-1) := pow_le_pow_right₀ (by norm_num) h0

def valiantTerm (N k : ℕ) : ℝ :=
  (Mfive N)^k * (hardMoment N k - unifMoment N k) /
    (((k/2).factorial : ℝ) * Real.sqrt (1 + (Mfive N)^k * hardMoment N k))

theorem valiantTerm_nonneg (N k : ℕ) (hN : 1 ≤ N) (hk : 2 ≤ k) :
    0 ≤ valiantTerm N k := by
  have hMk : (0:ℝ) ≤ (Mfive N)^k := by
    apply pow_nonneg; unfold Mfive; positivity
  have hdiff : 0 ≤ hardMoment N k - unifMoment N k := by
    have := unifMoment_le_hardMoment N k hN (by omega); linarith
  unfold valiantTerm
  apply div_nonneg
  · exact mul_nonneg hMk hdiff
  · apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact Real.sqrt_nonneg _

theorem valiantTerm_le (N k : ℕ) (hN : 1 ≤ N) (hk : 2 ≤ k) :
    valiantTerm N k ≤ (1:ℝ) / 512 / ((k/2).factorial : ℝ) := by
  have hfpos : (0:ℝ) < ((k/2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hMk : (0:ℝ) ≤ (Mfive N)^k := by
    apply pow_nonneg; unfold Mfive; positivity
  have hnum : (Mfive N)^k * (hardMoment N k - unifMoment N k) ≤ (1:ℝ)/512 := by
    have h1 : (Mfive N)^k * (hardMoment N k - unifMoment N k)
        ≤ (Mfive N)^k * hardMoment N k := by
      apply mul_le_mul_of_nonneg_left _ hMk
      nlinarith [show (0:ℝ) ≤ unifMoment N k by unfold unifMoment; positivity]
    exact le_trans h1 (hard_moment_scaled_five N k hk hN)
  have hprod : 0 ≤ (Mfive N)^k * hardMoment N k :=
    mul_nonneg hMk (by unfold hardMoment; positivity)
  have hbas : (0:ℝ) < 1 + (Mfive N)^k * hardMoment N k := by linarith
  have hs1 : (1:ℝ) ≤ Real.sqrt (1 + (Mfive N)^k * hardMoment N k) :=
    Real.one_le_sqrt.mpr (by linarith)
  have hs0 : (0:ℝ) < Real.sqrt (1 + (Mfive N)^k * hardMoment N k) :=
    Real.sqrt_pos.mpr hbas
  unfold valiantTerm
  rw [div_le_iff₀ (mul_pos hfpos hs0)]
  have heq : (1:ℝ)/512/((k/2).factorial : ℝ) * (((k/2).factorial : ℝ)
      * Real.sqrt (1 + (Mfive N)^k * hardMoment N k))
      = (1:ℝ)/512 * Real.sqrt (1 + (Mfive N)^k * hardMoment N k) := by
    field_simp
  rw [heq]
  have hnn : (0:ℝ) ≤ (1:ℝ)/512 := by norm_num
  calc (Mfive N)^k * (hardMoment N k - unifMoment N k)
      ≤ (1:ℝ)/512 := hnum
    _ ≤ (1:ℝ)/512 * Real.sqrt (1 + (Mfive N)^k * hardMoment N k) := by
        nth_rewrite 1 [show (1:ℝ)/512 = (1:ℝ)/512 * 1 by ring]
        exact mul_le_mul_of_nonneg_left hs1 hnn

theorem tsum_half_factorial :
    (∑' k : ℕ, (1:ℝ) / ((k.factorial : ℝ))) = Real.exp 1 := by
  have h := congrFun (Real.exp_eq_exp_ℝ.trans (NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ))) 1
  simp only [smul_eq_mul, one_pow, mul_one] at h
  rw [h]; apply tsum_congr; intro n; rw [div_eq_mul_inv, one_mul]

theorem summable_half_factorial :
    Summable (fun k : ℕ => (1:ℝ) / ((k.factorial : ℝ))) := by
  simpa only [one_pow] using! Real.summable_pow_div_factorial (1:ℝ)

theorem tsum_paired_factorial :
    (∑' k : ℕ, (1:ℝ) / (((k / 2).factorial : ℝ))) = 2 * Real.exp 1 := by
  have heven : (∑' k : ℕ, (1:ℝ) / (((2*k) / 2).factorial : ℝ))
      = ∑' k : ℕ, (1:ℝ) / ((k.factorial : ℝ)) := by
    apply tsum_congr; intro k; rw [show (2*k)/2 = k by omega]
  have hodd : (∑' k : ℕ, (1:ℝ) / (((2*k + 1) / 2).factorial : ℝ))
      = ∑' k : ℕ, (1:ℝ) / ((k.factorial : ℝ)) := by
    apply tsum_congr; intro k; rw [show (2*k + 1)/2 = k by omega]
  rw [← tsum_even_add_odd]
  · rw [heven, hodd, tsum_half_factorial]; ring
  · have : (fun k : ℕ => (1:ℝ) / (((2*k) / 2).factorial : ℝ)) = (fun k : ℕ => (1:ℝ) / ((k.factorial : ℝ))) := by
      funext k; rw [show (2*k)/2 = k by omega]
    rw [this]; exact summable_half_factorial
  · have : (fun k : ℕ => (1:ℝ) / (((2*k + 1) / 2).factorial : ℝ)) = (fun k : ℕ => (1:ℝ) / ((k.factorial : ℝ))) := by
      funext k; rw [show (2*k+1)/2 = k by omega]
    rw [this]; exact summable_half_factorial

theorem summable_paired :
    Summable (fun k : ℕ => (1:ℝ) / (((k / 2).factorial : ℝ))) := by
  apply Summable.even_add_odd
  · have : (fun k : ℕ => (1:ℝ) / (((2*k) / 2).factorial : ℝ)) = (fun k : ℕ => (1:ℝ) / ((k.factorial : ℝ))) := by
      funext k; rw [show (2*k)/2 = k by omega]
    rw [this]; exact summable_half_factorial
  · have : (fun k : ℕ => (1:ℝ) / (((2*k + 1) / 2).factorial : ℝ)) = (fun k : ℕ => (1:ℝ) / ((k.factorial : ℝ))) := by
      funext k; rw [show (2*k+1)/2 = k by omega]
    rw [this]; exact summable_half_factorial

theorem tsum_paired_shift :
    (∑' k : ℕ, (1:ℝ) / (((k + 2) / 2).factorial : ℝ)) = 2 * Real.exp 1 - 2 := by
  have hA := Summable.tsum_eq_zero_add
    (f := fun k : ℕ => (1:ℝ) / (((k) / 2).factorial : ℝ)) summable_paired
  have hS1 : Summable (fun k : ℕ => (1:ℝ) / (((k+1) / 2).factorial : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => (1:ℝ) / (((k) / 2).factorial : ℝ)) 1).mpr summable_paired
  have hB := Summable.tsum_eq_zero_add
    (f := fun k : ℕ => (1:ℝ) / (((k+1) / 2).factorial : ℝ)) hS1
  have h0 : (1:ℝ) / (((0) / 2).factorial : ℝ) = 1 := by norm_num
  have h01 : (1:ℝ) / (((0+1) / 2).factorial : ℝ) = 1 := by norm_num
  (try simp only at hA); (try simp only at hB)
  have hA' : (∑' b : ℕ, (1:ℝ) / (((b+1) / 2).factorial : ℝ)) = 2 * Real.exp 1 - 1 := by
    rw [tsum_paired_factorial, h0] at hA; linarith
  have hB' : (∑' b : ℕ, (1:ℝ) / ((((b+1)+1) / 2).factorial : ℝ)) = 2 * Real.exp 1 - 2 := by
    rw [hA', h01] at hB; linarith
  calc (∑' k : ℕ, (1:ℝ) / (((k + 2) / 2).factorial : ℝ))
      = ∑' b : ℕ, (1:ℝ) / ((((b+1)+1) / 2).factorial : ℝ) := by
        apply tsum_congr; intro b; rw [show b + 2 = (b+1)+1 by omega]
    _ = 2 * Real.exp 1 - 2 := hB'

theorem factorial_pair_series_le_four :
    (∑' k : ℕ, (1:ℝ) / (((k + 2) / 2).factorial : ℝ)) ≤ 4 := by
  rw [tsum_paired_shift]
  have := Real.exp_one_lt_three
  linarith

theorem summable_valiantTerm (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => valiantTerm N (k+2)) := by
  have hg : Summable (fun k : ℕ => (1:ℝ) / 512 / (((k+2)/2).factorial : ℝ)) := by
    have hshift : Summable (fun k : ℕ => (1:ℝ) / (((k+2)/2).factorial : ℝ)) :=
      (summable_nat_add_iff (f := fun k : ℕ => (1:ℝ) / ((k/2).factorial : ℝ)) 2).mpr summable_paired
    have := hshift.mul_left ((1:ℝ)/512)
    simpa only [div_eq_mul_inv, mul_one, one_mul] using! this
  exact Summable.of_nonneg_of_le
    (fun k => valiantTerm_nonneg N (k+2) hN (by omega))
    (fun k => valiantTerm_le N (k+2) hN (by omega)) hg

theorem valiantSum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' k : ℕ, valiantTerm N (k+2)) ≤ (1:ℝ) / 128 := by
  have hcmp : ∀ k : ℕ, valiantTerm N (k+2) ≤ (1:ℝ)/512 / (((k+2)/2).factorial : ℝ) :=
    fun k => valiantTerm_le N (k+2) hN (by omega)
  have hg : Summable (fun k : ℕ => (1:ℝ) / 512 / (((k+2)/2).factorial : ℝ)) := by
    have hshift : Summable (fun k : ℕ => (1:ℝ) / (((k+2)/2).factorial : ℝ)) :=
      (summable_nat_add_iff (f := fun k : ℕ => (1:ℝ) / ((k/2).factorial : ℝ)) 2).mpr summable_paired
    have := hshift.mul_left ((1:ℝ)/512)
    simpa only [div_eq_mul_inv, mul_one, one_mul] using! this
  have hmain : (∑' k : ℕ, valiantTerm N (k+2))
      ≤ ∑' k : ℕ, (1:ℝ)/512 / (((k+2)/2).factorial : ℝ) :=
    Summable.tsum_le_tsum hcmp (summable_valiantTerm N hN) hg
  have hval : (∑' k : ℕ, (1:ℝ)/512 / (((k+2)/2).factorial : ℝ))
      = (1:ℝ)/512 * (∑' k : ℕ, (1:ℝ) / (((k+2)/2).factorial : ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro k; simp only [div_eq_mul_inv, one_mul]
  rw [hval, tsum_paired_shift] at hmain
  have hfour : 2 * Real.exp 1 - 2 ≤ 4 := by
    rw [← tsum_paired_shift]; exact factorial_pair_series_le_four
  have hb : (1:ℝ)/512 * (2 * Real.exp 1 - 2) ≤ (1:ℝ)/512 * 4 :=
    mul_le_mul_of_nonneg_left hfour (by norm_num)
  nlinarith [hmain, hb]

theorem corollary1_distance_lt (N : ℕ) (hN : 1 ≤ N) (δ D : ℝ)
    (hδ : δ ≤ 1/10000)
    (hL12 : D ≤ 40*δ + 10*(∑' k : ℕ, valiantTerm N (k+2))) :
    D < 1/12 := by
  have hsum := valiantSum_le N hN
  have h40 : 40*δ ≤ 40*(1/10000:ℝ) := by nlinarith
  have h10 : 10 * (∑' k : ℕ, valiantTerm N (k+2)) ≤ 10 * ((1:ℝ)/128) := by
    nlinarith [hsum]
  have : D ≤ 40*(1/10000:ℝ) + 10*(1/128:ℝ) := by linarith
  have hnum : 40*(1/10000:ℝ) + 10*(1/128:ℝ) < 1/12 := by norm_num
  linarith

theorem corollary1_not_testable (N : ℕ) (hN : 1 ≤ N) (δ D : ℝ) (P : Prop)
    (hδ : δ ≤ 1/10000)
    (hL12 : D ≤ 40*δ + 10*(∑' k : ℕ, valiantTerm N (k+2)))
    (hlemma11 : D < 1/12 → P) : P :=
  hlemma11 (corollary1_distance_lt N hN δ D hδ hL12)

theorem card_filter_lt (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter (fun i : Fin N => (i:ℕ) < m)).card = m := by
  rw [← Fintype.card_coe]
  have h : Fintype.card {i : Fin N // (i:ℕ) < m} = m := by
    conv_rhs => rw [← Fintype.card_fin m]
    apply Fintype.card_congr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a; exact ⟨a.1.val, a.2⟩
    · intro b; exact ⟨⟨b.val, b.isLt.trans_le hm⟩, b.isLt⟩
    · intro a; apply Subtype.ext; apply Fin.ext; rfl
    · intro b; apply Fin.ext; rfl
  simpa using! h

def hardDist (N : ℕ) [NeZero N] (hN2 : 2 * (N / 2) = N) : Dist N where
  prob i := if (i:ℕ) < N / 2 then 2 / (N:ℝ) else 0
  nonneg i := by
    by_cases h : (i:ℕ) < N / 2
    · simp only [if_pos h]; positivity
    · simp only [if_neg h]; exact le_refl 0
  sum_one := by
    have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hcard := card_filter_lt N (N/2) (Nat.div_le_self N 2)
    have hsum : (∑ i : Fin N, (if (i:ℕ) < N/2 then 2/(N:ℝ) else 0))
        = ∑ _i ∈ Finset.univ.filter (fun i : Fin N => (i:ℕ) < N/2), (2/(N:ℝ)) := by
      rw [← Finset.sum_filter]
    rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul]
    have hcast : ((N/2:ℕ):ℝ) = (N:ℝ)/2 := by
      have h : (N:ℝ) = 2 * ((N/2:ℕ):ℝ) := by
        conv_lhs => rw [← hN2]
        push_cast; ring
      linarith
    rw [hcast, show (N:ℝ)/2 * (2/(N:ℝ)) = 1 by field_simp]

theorem moment_hard (N k : ℕ) [NeZero N] (hN2 : 2 * (N/2) = N) (hk : 1 ≤ k) :
    moment (hardDist N hN2) k = hardMoment N k := by
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcard := card_filter_lt N (N/2) (Nat.div_le_self N 2)
  unfold moment hardMoment
  have hpt : ∀ i : Fin N,
      (hardDist N hN2).prob i ^ k
        = if (i:ℕ) < N/2 then (2/(N:ℝ))^k else 0 := by
    intro i
    show (if (i:ℕ) < N/2 then 2/(N:ℝ) else 0)^k = _
    by_cases h : (i:ℕ) < N/2
    · simp only [if_pos h]
    · simp only [if_neg h, zero_pow (by omega : k ≠ 0)]
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hcast : ((N/2:ℕ):ℝ) = (N:ℝ)/2 := by
    have h : (N:ℝ) = 2 * ((N/2:ℕ):ℝ) := by
      conv_lhs => rw [← hN2]
      push_cast; ring
    linarith
  rw [hcast]
  have hfac : (N:ℝ)/2 * (2/(N:ℝ)) = 1 := by field_simp
  have hk'' : k = (k-1)+1 := by omega
  calc (N:ℝ)/2 * (2/(N:ℝ))^k
      = (N:ℝ)/2 * ((2/(N:ℝ))^(k-1) * (2/(N:ℝ))) := by conv_lhs => rw [hk'', pow_succ]
    _ = ((N:ℝ)/2 * (2/(N:ℝ))) * (2/(N:ℝ))^(k-1) := by ring
    _ = (2/(N:ℝ))^(k-1) := by rw [hfac, one_mul]
    _ = (2:ℝ)^(k-1)/(N:ℝ)^(k-1) := by rw [div_pow]

end Qatlib.Papers.DistTesting09.MainResults.LowerBounds
