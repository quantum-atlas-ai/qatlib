/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Spectral moment separation for diagonal entries

This module defines two finite cosine spectra with endpoint weights and proves their odd-moment
sign relation. It combines a lower bound from a distinguished unit eigenvalue with a
cosine-power decay estimate to obtain a signed inverse-polynomial gap under the stated mass and
spectral assumptions.

These constructions accompany the results of [JanzingWocjan2006a].

## Main statements

* `E1moment_eq_neg`: relates the two moments for odd spectrum size and odd exponent.
* `cos_pow_decay_strict`: bounds the cosine raised to the cubic exponent.
* `moment_separation`: derives a moment gap from the supplied spectral and weight conditions.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006a]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.Hardness

/-- The natural index bound `(M - 1) / 2 + 1` for the finite cosine spectra. -/
def halfIdx (M : ℕ) : ℕ := (M - 1) / 2 + 1

/-- The weight `1 / M` at the zero index and `2 / M` at the other indices. -/
def mass0 (M : ℕ) (l : Fin (halfIdx M)) : ℝ :=
  if (l : ℕ) = 0 then 1 / (M : ℝ) else 2 / (M : ℝ)

/-- The weight `1 / M` at the final index and `2 / M` at the other indices. -/
def mass1 (M : ℕ) (l : Fin (halfIdx M)) : ℝ :=
  if (l : ℕ) = (M - 1) / 2 then 1 / (M : ℝ) else 2 / (M : ℝ)

/-- The cosine value `cos (2 * π * l / M)` in the first spectrum. -/
def lam0 (M : ℕ) (l : Fin (halfIdx M)) : ℝ :=
  Real.cos (2 * Real.pi * (l : ℝ) / (M : ℝ))

/-- The cosine value `cos (π * (2 * l + 1) / M)` in the second spectrum. -/
def lam1 (M : ℕ) (l : Fin (halfIdx M)) : ℝ :=
  Real.cos (Real.pi * (2 * (l : ℝ) + 1) / (M : ℝ))

/-- The weighted `m`th moment of the first finite cosine spectrum. -/
def E0moment (M m : ℕ) : ℝ := ∑ l, mass0 M l * (lam0 M l) ^ m

/-- The weighted `m`th moment of the second finite cosine spectrum. -/
def E1moment (M m : ℕ) : ℝ := ∑ l, mass1 M l * (lam1 M l) ^ m

/-- Reversing the index of the first weight family gives the second weight family. See
[JanzingWocjan2006a]. -/
theorem mass1_eq_mass0_rev (M : ℕ) (l : Fin (halfIdx M)) :
    mass1 M l = mass0 M (Fin.rev l) := by
  unfold mass1 mass0
  rw [Fin.val_rev]
  by_cases h : (l : ℕ) = (M - 1) / 2
  · have h0 : halfIdx M - ((l : ℕ) + 1) = 0 := by
      have hl := l.isLt
      unfold halfIdx at hl
      unfold halfIdx
      omega
    rw [if_pos h, if_pos h0]
  · have h0 : ¬ (halfIdx M - ((l : ℕ) + 1) = 0) := by
      intro hc
      have hl := l.isLt
      unfold halfIdx at hl hc
      have hle : (M - 1) / 2 + 1 ≤ (l : ℕ) + 1 := by omega
      have hl2 : (l : ℕ) ≤ (M - 1) / 2 := by omega
      omega
    rw [if_neg h, if_neg h0]

/-- For odd `M`, the second cosine spectrum equals the negative of the first spectrum with
reversed indices. See [JanzingWocjan2006a]. -/
theorem lam1_eq_neg_lam0 (M : ℕ) (hM : Odd M) (l : Fin (halfIdx M)) :
    lam1 M l = - lam0 M (Fin.rev l) := by
  obtain ⟨k, hk⟩ := hM
  have hn : (M - 1) / 2 = k := by omega
  have hnR : (((M - 1) / 2 : ℕ) : ℝ) = (k : ℝ) := by rw [hn]
  have hMk : (M : ℝ) = 2 * (k : ℝ) + 1 := by rw [hk]; push_cast; ring
  have hval : ((Fin.rev l : Fin (halfIdx M)) : ℝ) = (k : ℝ) - (l : ℝ) := by
    change ((Fin.rev l : Fin ((M - 1) / 2 + 1)) : ℝ) = (k : ℝ) - (l : ℝ)
    rw [Fin.val_rev]
    have hle : (l : ℕ) + 1 ≤ (M - 1) / 2 + 1 := by
      have hl := l.isLt
      unfold halfIdx at hl
      omega
    rw [Nat.cast_sub hle]
    push_cast
    rw [hnR]
    ring
  unfold lam1 lam0
  rw [hval, hMk, ← Real.cos_pi_sub]
  congr 1
  have hMpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  field_simp
  ring

/-- For odd `M` and odd `m`, the second weighted moment is the negative of the first. See
[JanzingWocjan2006a]. -/
theorem E1moment_eq_neg (M m : ℕ) (hM : Odd M) (hm : Odd m) :
    E1moment M m = - E0moment M m := by
  unfold E1moment E0moment
  calc ∑ l, mass1 M l * (lam1 M l) ^ m
      = ∑ l, mass0 M (Fin.rev l) * (-(lam0 M (Fin.rev l))) ^ m := by
          apply Finset.sum_congr rfl
          intro l _
          rw [mass1_eq_mass0_rev M l, lam1_eq_neg_lam0 M hM l]
    _ = ∑ l, mass0 M l * (-(lam0 M l)) ^ m := by
          have h := Equiv.sum_comp (Fin.revPerm (n := halfIdx M))
            (fun l : Fin (halfIdx M) => mass0 M l * (-(lam0 M l)) ^ m)
          simpa [Fin.revPerm_apply] using h
    _ = ∑ l, -(mass0 M l * (lam0 M l) ^ m) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hm.neg_pow]
          ring
    _ = - ∑ l, mass0 M l * (lam0 M l) ^ m := by
          rw [Finset.sum_neg_distrib]

/-- For odd `M` and odd `m`, a linear combination of the two moments equals the coefficient
difference times the first moment. See [JanzingWocjan2006a]. -/
theorem moment_sign_split (M m : ℕ) (hM : Odd M) (hm : Odd m) (α0 α1 : ℝ) :
    α0 * E0moment M m + α1 * E1moment M m = (α0 - α1) * E0moment M m := by
  rw [E1moment_eq_neg M m hM hm]
  ring

/-- For nonnegative weights with remaining total mass at most one, a distinguished unit spectral
value and a negative lower spectral bound give the stated lower bound on an odd weighted
moment. See [JanzingWocjan2006a]. -/
theorem moment_lower_bound_of_min {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P lam : ι → ℝ) (i0 : ι) (lamMin : ℝ) (m : ℕ)
    (hP : ∀ i, 0 ≤ P i) (hlam0 : lam i0 = 1)
    (hmin : ∀ i, lamMin ≤ lam i) (hlamNeg : lamMin < 0) (hm : Odd m)
    (htail : ∑ i ∈ Finset.univ.erase i0, P i ≤ 1) :
    P i0 + lamMin ^ m ≤ ∑ i, P i * (lam i) ^ m := by
  classical
  rw [← Finset.sum_erase_add (Finset.univ) (fun i => P i * (lam i) ^ m)
    (Finset.mem_univ i0)]
  have hlam0m : (lam i0) ^ m = 1 := by rw [hlam0]; simp
  have hmpos : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  have hneg : lamMin ^ m < 0 := by
    have h := hm.strictMono_pow hlamNeg
    simpa [zero_pow hmpos.ne'] using h
  have hmono : ∀ i, lamMin ^ m ≤ (lam i) ^ m := fun i =>
    (hm.strictMono_pow.monotone (hmin i))
  have hterm : ∀ i ∈ Finset.univ.erase i0, P i * lamMin ^ m ≤ P i * (lam i) ^ m := by
    intro i _
    exact mul_le_mul_of_nonneg_left (hmono i) (hP i)
  have h1 : (∑ i ∈ Finset.univ.erase i0, P i) * lamMin ^ m
      ≤ ∑ i ∈ Finset.univ.erase i0, P i * (lam i) ^ m := by
    calc (∑ i ∈ Finset.univ.erase i0, P i) * lamMin ^ m
        = ∑ i ∈ Finset.univ.erase i0, P i * lamMin ^ m := by rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ Finset.univ.erase i0, P i * (lam i) ^ m := Finset.sum_le_sum hterm
  have h2 : 1 * lamMin ^ m ≤ (∑ i ∈ Finset.univ.erase i0, P i) * lamMin ^ m :=
    mul_le_mul_of_nonpos_right htail (le_of_lt hneg)
  have hchain : lamMin ^ m ≤ ∑ i ∈ Finset.univ.erase i0, P i * (lam i) ^ m := by
    simpa using le_trans h2 h1
  rw [hlam0m, mul_one]
  linarith [hchain]

/-- Under the supplied zero-index, mass, tail, and spectral assumptions, the first odd moment is
at least `1 / M + lamMin ^ m`. See [JanzingWocjan2006a]. -/
theorem E0moment_lower_of_min (M m : ℕ) (l0 : Fin (halfIdx M)) (lamMin : ℝ)
    (h0 : (l0 : ℕ) = 0) (hm : Odd m) (hmin : ∀ l, lamMin ≤ lam0 M l)
    (hlamNeg : lamMin < 0)
    (hmass0 : mass0 M l0 = 1 / (M : ℝ))
    (htail : ∑ l ∈ (Finset.univ.erase l0), mass0 M l ≤ 1)
    (hP : ∀ l, 0 ≤ mass0 M l) :
    1 / (M : ℝ) + lamMin ^ m ≤ E0moment M m := by
  have hlam0 : lam0 M l0 = 1 := by
    unfold lam0
    rw [h0]
    simp
  unfold E0moment
  have h := moment_lower_bound_of_min (mass0 M) (lam0 M) l0 lamMin m hP hlam0
    hmin hlamNeg hm htail
  rwa [hmass0] at h

/-- For `M ≥ 3`, `cos (π / M)` is positive. -/
theorem cos_pi_div_pos (M : ℕ) (hM : 3 ≤ M) :
    0 < Real.cos (Real.pi / (M : ℝ)) := by
  have hMpos : (0:ℝ) < (M:ℝ) := by positivity
  have h2M : (2:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 2 < M)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hpos : (0:ℝ) < Real.pi / (M:ℝ) := by positivity
    linarith [Real.pi_pos, hpos]
  · rw [div_lt_div_iff₀ hMpos (by norm_num)]
    nlinarith [Real.pi_pos]

/-- For `M ≥ 2`, `cos (π / M)` is at most `1 - 2 / M ^ 2`. -/
theorem cos_pi_div_le_one_sub (M : ℕ) (hM : 2 ≤ M) :
    Real.cos (Real.pi / (M : ℝ)) ≤ 1 - 2 / (M : ℝ) ^ 2 := by
  have hM0 : (0:ℝ) < (M:ℝ) := by positivity
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have habs : |Real.pi / (M:ℝ)| ≤ Real.pi := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ hM0]
    nlinarith [Real.pi_pos, hM1]
  have h := Real.cos_le_one_sub_mul_cos_sq habs
  have heq : 2 / Real.pi ^ 2 * (Real.pi / (M : ℝ)) ^ 2 = 2 / (M : ℝ) ^ 2 := by
    field_simp
  rw [heq] at h
  exact h

/-- For `M ≥ 2`, raising `1 - 1 / M ^ 2` to `M ^ 2` gives a value strictly less than `exp (-1)`. -/
theorem one_sub_sq_pow_lt_exp_neg (M : ℕ) (hM : 2 ≤ M) :
    (1 - 1/(M:ℝ)^2) ^ (M^2) < Real.exp (-1) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by positivity
  have hMsq : (1:ℝ) < (M:ℝ)^2 := by
    have h1 : (1:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 1 < M)
    nlinarith
  have hbasepos : (0:ℝ) < 1 - 1/(M:ℝ)^2 := by
    have hle : 1/(M:ℝ)^2 < 1 := by
      rw [div_lt_one (by positivity)]
      exact hMsq
    linarith
  have hbase_ne : (1 - 1/(M:ℝ)^2) ≠ 1 := by
    intro hc
    have hzero : (1:ℝ) / (M:ℝ)^2 = 0 := by linarith
    have hne : ((M:ℝ)^2) ≠ 0 := by positivity
    rcases (div_eq_zero_iff).mp hzero with h | h
    · exact one_ne_zero h
    · exact hne h
  have hlog : Real.log (1 - 1/(M:ℝ)^2) < -(1/(M:ℝ)^2) := by
    have h := Real.log_lt_sub_one_of_pos hbasepos hbase_ne
    linarith
  have hlogpow : Real.log ((1 - 1/(M:ℝ)^2)^(M^2)) < ((M:ℝ)^2) * (-(1/(M:ℝ)^2)) := by
    rw [Real.log_pow, Nat.cast_pow]
    exact mul_lt_mul_of_pos_left hlog (pow_pos hM0 2)
  have hval : ((M:ℝ)^2) * (-(1/(M:ℝ)^2)) = -1 := by
    field_simp
  have hpowpos : 0 < (1 - 1/(M:ℝ)^2)^(M^2) := pow_pos hbasepos _
  calc (1 - 1/(M:ℝ)^2)^(M^2)
      = Real.exp (Real.log ((1 - 1/(M:ℝ)^2)^(M^2))) := (Real.exp_log hpowpos).symm
    _ < Real.exp (((M:ℝ)^2) * (-(1/(M:ℝ)^2))) := Real.exp_lt_exp.mpr hlogpow
    _ = Real.exp (-1) := by rw [hval]

/-- For positive natural `M`, `exp (-(2 * M))` is at most `1 / (4 * M)`. -/
theorem exp_neg_two_mul_le (M : ℕ) (hM : 0 < M) :
    Real.exp (-(2*(M:ℝ))) ≤ 1/(4*(M:ℝ)) := by
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have h1 : (M:ℝ) + 1 ≤ Real.exp (M:ℝ) := Real.add_one_le_exp _
  have h2 : ((M:ℝ)+1)^2 ≤ (Real.exp (M:ℝ))^2 := pow_le_pow_left₀ (by positivity) h1 2
  have h4 : 4*(M:ℝ) ≤ ((M:ℝ)+1)^2 := by nlinarith [sq_nonneg ((M:ℝ)-1)]
  have he : (Real.exp (M:ℝ))^2 = Real.exp (2*(M:ℝ)) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hexpge : 4*(M:ℝ) ≤ Real.exp (2*(M:ℝ)) := by
    rw [← he]; exact le_trans h4 h2
  have heq : Real.exp (-(2*(M:ℝ))) = 1 / Real.exp (2*(M:ℝ)) := by
    rw [Real.exp_neg, one_div]
  rw [heq]
  exact one_div_le_one_div_of_le (by positivity) hexpge

/-- For `M ≥ 3`, `cos (π / M) ^ (M ^ 3)` is strictly less than `1 / (4 * M)`. See
[JanzingWocjan2006a]. -/
theorem cos_pow_decay_strict (M : ℕ) (hM : 3 ≤ M) :
    (Real.cos (Real.pi / (M:ℝ))) ^ (M^3) < 1/(4*(M:ℝ)) := by
  have hMpos : (0:ℝ) < (M:ℝ) := by positivity
  have hcospos : 0 < Real.cos (Real.pi/(M:ℝ)) := cos_pi_div_pos M hM
  have hcos : Real.cos (Real.pi/(M:ℝ)) ≤ 1 - 2/(M:ℝ)^2 := cos_pi_div_le_one_sub M (by omega)
  have hsq : 1 - 2/(M:ℝ)^2 ≤ (1 - 1/(M:ℝ)^2)^2 := by
    have h : (1 - 1/(M:ℝ)^2)^2 = 1 - 2/(M:ℝ)^2 + (1/(M:ℝ)^2)^2 := by ring
    rw [h]
    have hnn : (0:ℝ) ≤ (1/(M:ℝ)^2)^2 := sq_nonneg _
    linarith
  have hbase_nonneg : (0:ℝ) ≤ 1 - 1/(M:ℝ)^2 := by
    have hMsq : (1:ℝ) ≤ (M:ℝ)^2 := by
      have h1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
      nlinarith
    have : 1/(M:ℝ)^2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hMsq
    linarith
  have hpow : (Real.cos (Real.pi/(M:ℝ)))^(M^3) ≤ ((1 - 1/(M:ℝ)^2)^2)^(M^3) :=
    pow_le_pow_left₀ hcospos.le (le_trans hcos hsq) _
  have hexp : ((1 - 1/(M:ℝ)^2)^2)^(M^3) = ((1 - 1/(M:ℝ)^2)^(M^2))^(2*M) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hloglt := one_sub_sq_pow_lt_exp_neg M (by omega : 2 ≤ M)
  have hstep : ((1 - 1/(M:ℝ)^2)^(M^2))^(2*M) < (Real.exp (-1))^(2*M) := by
    apply pow_lt_pow_left₀ hloglt (pow_nonneg hbase_nonneg _)
    omega
  have hexp2 : (Real.exp (-1))^(2*M) = Real.exp (-(2*(M:ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfin := exp_neg_two_mul_le M (by omega : 0 < M)
  calc (Real.cos (Real.pi/(M:ℝ)))^(M^3)
      ≤ ((1 - 1/(M:ℝ)^2)^2)^(M^3) := hpow
    _ = ((1 - 1/(M:ℝ)^2)^(M^2))^(2*M) := hexp
    _ < (Real.exp (-1))^(2*M) := hstep
    _ = Real.exp (-(2*(M:ℝ))) := hexp2
    _ ≤ 1/(4*(M:ℝ)) := hfin

/-- For `M ≥ 3`, `cos (π / M) ^ (M ^ 3)` is at most `1 / (4 * M)`. See [JanzingWocjan2006a]. -/
theorem cos_pow_decay (M : ℕ) (hM : 3 ≤ M) :
    (Real.cos (Real.pi / (M : ℝ))) ^ (M ^ 3) ≤ 1 / (4 * (M : ℝ)) :=
  (cos_pow_decay_strict M hM).le

/-- An odd-power lower estimate with cosine tail strictly below `1 / (4 * M)` forces `E0` to
exceed `3 / (4 * M)` for positive `M`. See [JanzingWocjan2006a]. -/
theorem E0_exceeds_three_quarters_inv (M m : ℕ) (hMpos : 0 < M) (hm : Odd m)
    (E0 : ℝ)
    (hE0 : 1 / (M : ℝ) + (-(Real.cos (Real.pi / (M : ℝ)))) ^ m ≤ E0)
    (hcos : (Real.cos (Real.pi / (M : ℝ))) ^ m < 1 / (4 * (M : ℝ))) :
    3 / (4 * (M : ℝ)) < E0 := by
  have hpow : (-(Real.cos (Real.pi / (M : ℝ)))) ^ m
      = - ((Real.cos (Real.pi / (M : ℝ))) ^ m) := hm.neg_pow _
  have hkey : 3 / (4 * (M : ℝ)) < 1 / (M : ℝ)
      - (Real.cos (Real.pi / (M : ℝ))) ^ m := by
    have h4 : 1 / (M : ℝ) - 1 / (4 * (M : ℝ)) = 3 / (4 * (M : ℝ)) := by
      have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      field_simp
      ring
    linarith [hcos, h4]
  rw [hpow] at hE0
  linarith [hE0, hkey]

/-- If `E0 > 3 / (4 * M)` and the coefficient difference is signed one third, their product is
above `1 / (4 * M)` or below its negative. See [JanzingWocjan2006a]. -/
theorem diagonal_entry_sign_gap (M : ℕ) (E0 α0 α1 : ℝ) (hM : 0 < M)
    (hE0 : 3 / (4 * (M : ℝ)) < E0)
    (hcase : α0 - α1 = 1 / 3 ∨ α0 - α1 = -(1 / 3)) :
    (1 / (4 * (M : ℝ)) < (α0 - α1) * E0) ∨
      ((α0 - α1) * E0 < -(1 / (4 * (M : ℝ)))) := by
  have hc : (1 / 3 : ℝ) * (3 / (4 * (M : ℝ))) = 1 / (4 * (M : ℝ)) := by
    have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    field_simp
  rcases hcase with h | h
  · left
    rw [h]
    nlinarith [hE0, hc]
  · right
    rw [h]
    nlinarith [hE0, hc]

/-- For odd `M ≥ 3`, the given spectral lower bound, endpoint mass, tail bound, nonnegative
weights, and signed-one-third coefficient gap force the cubic moment combination outside the
interval with endpoints `±1 / (4 * M)`. See [JanzingWocjan2006a]. -/
theorem moment_separation (M : ℕ) (hM : 3 ≤ M) (hModd : Odd M)
    (l0 : Fin (halfIdx M)) (h0 : (l0 : ℕ) = 0)
    (hmin : ∀ l, -(Real.cos (Real.pi / (M:ℝ))) ≤ lam0 M l)
    (hmass0 : mass0 M l0 = 1 / (M:ℝ))
    (htail : ∑ l ∈ (Finset.univ.erase l0), mass0 M l ≤ 1)
    (hP : ∀ l, 0 ≤ mass0 M l) (α0 α1 : ℝ)
    (hcase : α0 - α1 = 1/3 ∨ α0 - α1 = -(1/3)) :
    (1 / (4*(M:ℝ)) < (α0 - α1) * E0moment M (M^3)) ∨
      ((α0 - α1) * E0moment M (M^3) < -(1 / (4*(M:ℝ)))) := by
  have hm : Odd (M^3) := hModd.pow
  have hcospos : 0 < Real.cos (Real.pi/(M:ℝ)) := cos_pi_div_pos M hM
  have hlamNeg : -(Real.cos (Real.pi/(M:ℝ))) < 0 := by linarith
  have hE0 := E0moment_lower_of_min M (M^3) l0 (-(Real.cos (Real.pi/(M:ℝ))))
    h0 hm hmin hlamNeg hmass0 htail hP
  have hcos := cos_pow_decay_strict M hM
  have hgt := E0_exceeds_three_quarters_inv M (M^3) (by omega) hm
    (E0moment M (M^3)) hE0 hcos
  exact diagonal_entry_sign_gap M (E0moment M (M^3)) α0 α1 (by omega) hgt hcase

end Qatlib.Papers.DiagPowerBQP06.MainResults.Hardness
