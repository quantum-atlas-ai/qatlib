/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CorrWalkSim16.MainResults.CorrectionSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option backward.isDefEq.respectTransparency false

/-!
# CorrWalkSim16, Lemmas 4, 5 and 7: coefficient and tail bounds

Berry--Novo, arXiv:1606.03443v3.

This file formalizes the `s`-weight estimates that turn the Neumann series of
the correction into the query schedule.

* `lemma5_coeff_abs_le`: Eq. (82) in sharp form.  Writing
  `V_C^+(x) = ∑ m, |a_m| x^m` for the correction coefficients (`x ≥ 1`), the
  single coefficient bound `|a_m| ≤ V_C^+(x) x^{-m}` holds, and with the
  symmetry of Lemma 3 it becomes `|a_m| ≤ V_C^+(x) x^{-|m|}`
  (`lemma5_coeff_abs_le_symm`).
* `geomTail_nat`: the one-sided geometric tail
  `∑_{k>N} ρ^k = ρ^{N+1}/(1-ρ)`.
* `lemma4_tail_le`: Eq. (65)/(73) of Lemma 4, the two-sided tail bound
  `∑_{|m|>N} |a_m| ≤ 2 C ρ^{N+1}/(1-ρ)` for coefficients with `|a_m| ≤ C ρ^{|m|}`.
  This is the sharp form of `≲ 2^{r+1}(zζ/M)^{N+1}` with `C = 2^r` and
  `ρ = zζ/M`; the paper's `≲` absorbs the factor `(1-ρ)^{-1}`.
* `lemma7_tail_le`: Eq. (97) of Lemma 7, the same tail bound for the
  second-round coefficients with `ρ' = zζζ' 2^{1/M}/M` and `N'`.

The two-sided geometric sum is computed by splitting `ℤ` at `0` with
`tsum_int_rec` into the nonnegative branch `k ↦ N < k` and the negative branch
`k ↦ N < k + 1`, which is the same reduction the paper performs after
Eq. (66) using the symmetry `|a_m| = |a_{-m}|`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.CorrWalkSim16.MainResults

open scoped BigOperators

/-- The `x`-weighted `ℓ¹` mass `V_C^+(x) = ∑ m, |a_m| x^m` of Eq. (66). -/
def absExpSum (a : ℤ → ℂ) (x : ℝ) : ℝ := ∑' m : ℤ, ‖a m‖ * x ^ (m : ℤ)

/-- Lemma 5, Eq. (82): from the weighted mass bound `V_C^+(x) ≤ C` with `x ≥ 1`,
each coefficient is bounded by `C x^{-m}`. -/
theorem lemma5_coeff_abs_le (a : ℤ → ℂ) (C x : ℝ) (hx : 1 ≤ x)
    (hsum : Summable fun m : ℤ => ‖a m‖ * x ^ (m : ℤ)) (hbound : absExpSum a x ≤ C)
    (m : ℤ) : ‖a m‖ ≤ C * x ^ (-(m : ℤ)) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hterm : ‖a m‖ * x ^ (m : ℤ) ≤ C := by
    refine le_trans (hsum.le_tsum m (fun b _ => ?_)) hbound
    exact mul_nonneg (norm_nonneg _) (le_of_lt (zpow_pos hxpos _))
  have hone : x ^ (m : ℤ) * x ^ (-(m : ℤ)) = 1 := by
    rw [← zpow_add₀ (ne_of_gt hxpos)]
    rw [show (m : ℤ) + -(m : ℤ) = 0 by ring, zpow_zero]
  calc ‖a m‖ = ‖a m‖ * 1 := (mul_one _).symm
    _ = ‖a m‖ * (x ^ (m : ℤ) * x ^ (-(m : ℤ))) := by rw [hone]
    _ = (‖a m‖ * x ^ (m : ℤ)) * x ^ (-(m : ℤ)) := by ring
    _ ≤ C * x ^ (-(m : ℤ)) :=
        mul_le_mul_of_nonneg_right hterm (le_of_lt (zpow_pos hxpos _))

/-- Lemma 5 with the symmetry of Lemma 3: the coefficient bound is
`|a_m| ≤ C x^{-|m|}`, which is Eq. (82) with `x = M/(zζ)`. -/
theorem lemma5_coeff_abs_le_symm (a : ℤ → ℂ) (hsym : WalkSymmetric a) (C x : ℝ)
    (hx : 1 ≤ x) (hsum : Summable fun m : ℤ => ‖a m‖ * x ^ (m : ℤ))
    (hbound : absExpSum a x ≤ C) (m : ℤ) :
    ‖a m‖ ≤ C * x ^ (-((m.natAbs : ℕ) : ℤ)) := by
  by_cases hm : m < 0
  · have hk : 0 ≤ -m := by omega
    have hnorm : ‖a m‖ = ‖a (-m)‖ := by
      have h := hsym (-m)
      have harg : -(-m) = m := by ring
      rw [harg] at h
      rw [h, norm_mul]
      have hone : ‖(-1 : ℂ) ^ (-m)‖ = 1 := by
        rw [neg_one_zpow_eq_natAbs]
        simp
      rw [hone, one_mul]
    rw [hnorm]
    have h := lemma5_coeff_abs_le a C x hx hsum hbound (-m)
    have hexp : -(((-m) : ℤ)) = -(((m.natAbs : ℕ)) : ℤ) := by
      have h1 : ((m.natAbs : ℕ) : ℤ) = -m := by
        rw [← Int.natAbs_neg m]
        exact Int.natAbs_of_nonneg (by omega)
      rw [h1]
    rw [hexp] at h
    exact h
  · have hm' : 0 ≤ m := by omega
    have h := lemma5_coeff_abs_le a C x hx hsum hbound m
    have hnn : ((m.natAbs : ℕ) : ℤ) = m := Int.natAbs_of_nonneg hm'
    rw [hnn]
    exact h

/-- The one-sided geometric tail is summable. -/
theorem summable_geomTail (ρ : ℝ) (hρpos : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    Summable fun k : ℕ => (if N < k then ρ ^ (k : ℤ) else 0) := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρpos
  have hgeom : Summable fun k : ℕ => ρ ^ k := summable_geometric_of_lt_one hρ0 hρ1
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hgeom
  · split
    · exact le_of_lt (zpow_pos hρpos _)
    · exact le_rfl
  · split
    · rw [zpow_natCast]
    · exact pow_nonneg hρ0 k

/-- The one-sided geometric tail: `∑_{k>N} ρ^k = ρ^{N+1}/(1-ρ)`. -/
theorem geomTail_nat (ρ : ℝ) (hρpos : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    (∑' k : ℕ, (if N < k then ρ ^ (k : ℤ) else 0))
      = ρ ^ ((N : ℤ) + 1) / (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := le_of_lt hρpos
  have htail : Summable fun k : ℕ => (if N < k then ρ ^ (k : ℤ) else 0) :=
    summable_geomTail ρ hρpos hρ1 N
  have hsplit := htail.sum_add_tsum_nat_add (N + 1)
  have hfirst : (∑ i ∈ Finset.range (N + 1), (if N < i then ρ ^ (i : ℤ) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
  rw [hfirst, zero_add] at hsplit
  have hshift : (∑' k : ℕ, (if N < k + (N + 1) then ρ ^ ((k + (N + 1) : ℕ) : ℤ) else 0))
      = ∑' k : ℕ, ρ ^ ((k + (N + 1) : ℕ) : ℤ) := by
    refine tsum_congr fun k => ?_
    rw [if_pos (by omega)]
  rw [hshift] at hsplit
  have hfac : ∀ k : ℕ, ρ ^ ((k + (N + 1) : ℕ) : ℤ) = ρ ^ (k : ℤ) * ρ ^ ((N : ℤ) + 1) := by
    intro k
    have h1 : ((k + (N + 1) : ℕ) : ℤ) = (k : ℤ) + ((N : ℤ) + 1) := by push_cast; ring
    rw [h1, zpow_add₀ (ne_of_gt hρpos)]
  have hz : (∑' k : ℕ, ρ ^ (k : ℤ)) = (1 - ρ)⁻¹ := by
    have hfun : (fun k : ℕ => ρ ^ (k : ℤ)) = fun k => ρ ^ k := by
      funext k
      rw [zpow_natCast]
    rw [hfun]
    exact tsum_geometric_of_lt_one hρ0 hρ1
  calc (∑' k : ℕ, (if N < k then ρ ^ (k : ℤ) else 0))
      = ∑' k : ℕ, ρ ^ ((k + (N + 1) : ℕ) : ℤ) := hsplit.symm
    _ = ∑' k : ℕ, ρ ^ (k : ℤ) * ρ ^ ((N : ℤ) + 1) := tsum_congr hfac
    _ = (∑' k : ℕ, ρ ^ (k : ℤ)) * ρ ^ ((N : ℤ) + 1) := tsum_mul_right
    _ = (1 - ρ)⁻¹ * ρ ^ ((N : ℤ) + 1) := by rw [hz]
    _ = ρ ^ ((N : ℤ) + 1) / (1 - ρ) := by ring


/-- The one-sided pieces of the two-sided geometric tail. -/
theorem summable_geomTail_int_pieces (C ρ : ℝ) (hρpos : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    Summable (fun k : ℕ => if N < k then C * ρ ^ (k : ℤ) else 0) ∧
    Summable (fun k : ℕ => if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0) := by
  classical
  have hbase : Summable fun j : ℕ => (if N < j then ρ ^ (j : ℤ) else 0) :=
    summable_geomTail ρ hρpos hρ1 N
  have hf : Summable fun k : ℕ => if N < k then C * ρ ^ (k : ℤ) else 0 := by
    have hpt : (fun k : ℕ => if N < k then C * ρ ^ (k : ℤ) else 0)
        = fun k => C * (if N < k then ρ ^ (k : ℤ) else 0) := by
      funext k
      by_cases h : N < k <;> simp [h]
    rw [hpt]
    exact hbase.mul_left C
  have hg : Summable fun k : ℕ => if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0 := by
    have hshift : Summable fun k : ℕ => (if N < k + 1 then ρ ^ ((k + 1 : ℕ) : ℤ) else 0) := by
      have h := hbase.comp_injective (i := fun k : ℕ => k + 1)
        (by intro a b hab; exact Nat.add_right_cancel hab)
      show Summable ((fun j : ℕ => (if N < j then ρ ^ (j : ℤ) else 0)) ∘ fun k => k + 1)
      exact h
    have hpt : (fun k : ℕ => if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0)
        = fun k => C * (if N < k + 1 then ρ ^ ((k + 1 : ℕ) : ℤ) else 0) := by
      funext k
      by_cases h : N < k + 1 <;> simp [h]
    rw [hpt]
    exact hshift.mul_left C
  exact ⟨hf, hg⟩

/-- The two-sided geometric tail is summable. -/
theorem summable_geomTail_int (C ρ : ℝ) (hρpos : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    Summable fun m : ℤ =>
      (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then C * ρ ^ (((m.natAbs : ℕ)) : ℤ) else 0) := by
  classical
  obtain ⟨hf, hg⟩ := summable_geomTail_int_pieces C ρ hρpos hρ1 N
  have hfun : (fun m : ℤ =>
      (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then C * ρ ^ (((m.natAbs : ℕ)) : ℤ) else 0))
      = Int.rec (fun k : ℕ => if N < k then C * ρ ^ (k : ℤ) else 0)
          (fun k : ℕ => if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0) := by
    funext m
    rcases m with n | k
    · simp
    · rw [Int.natAbs_negSucc]
      show (if (N : ℤ) < ((k.succ : ℕ) : ℤ) then C * ρ ^ (((k.succ : ℕ)) : ℤ) else 0)
        = (if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0)
      by_cases h : N ≤ k
      · rw [if_pos (by omega : (N : ℤ) < ((k.succ : ℕ) : ℤ)),
          if_pos (by omega : N < k + 1)]
      · rw [if_neg (by omega : ¬ (N : ℤ) < ((k.succ : ℕ) : ℤ)),
          if_neg (by omega : ¬ N < k + 1)]
  rw [hfun]
  exact Summable.int_rec hf hg

/-- The two-sided geometric tail `∑_{|m|>N} C ρ^{|m|} = 2 C ρ^{N+1}/(1-ρ)`. -/
theorem geomTail_int (C ρ : ℝ) (hρpos : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    (∑' m : ℤ, (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then C * ρ ^ (((m.natAbs : ℕ)) : ℤ) else 0))
      = 2 * (C * ρ ^ ((N : ℤ) + 1) / (1 - ρ)) := by
  classical
  obtain ⟨hf, hg⟩ := summable_geomTail_int_pieces C ρ hρpos hρ1 N
  have hfun : (fun m : ℤ =>
      (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then C * ρ ^ (((m.natAbs : ℕ)) : ℤ) else 0))
      = Int.rec (fun k : ℕ => if N < k then C * ρ ^ (k : ℤ) else 0)
          (fun k : ℕ => if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0) := by
    funext m
    rcases m with n | k
    · simp
    · rw [Int.natAbs_negSucc]
      show (if (N : ℤ) < ((k.succ : ℕ) : ℤ) then C * ρ ^ (((k.succ : ℕ)) : ℤ) else 0)
        = (if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0)
      by_cases h : N ≤ k
      · rw [if_pos (by omega : (N : ℤ) < ((k.succ : ℕ) : ℤ)),
          if_pos (by omega : N < k + 1)]
      · rw [if_neg (by omega : ¬ (N : ℤ) < ((k.succ : ℕ) : ℤ)),
          if_neg (by omega : ¬ N < k + 1)]
  rw [hfun, tsum_int_rec hf hg]
  have hfval : (∑' k : ℕ, (if N < k then C * ρ ^ (k : ℤ) else 0))
      = C * (∑' k : ℕ, (if N < k then ρ ^ (k : ℤ) else 0)) := by
    have hpt : (fun k : ℕ => if N < k then C * ρ ^ (k : ℤ) else 0)
        = fun k => C * (if N < k then ρ ^ (k : ℤ) else 0) := by
      funext k
      by_cases h : N < k <;> simp [h]
    rw [hpt, tsum_mul_left]
  have hgval : (∑' k : ℕ, (if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0))
      = C * (∑' k : ℕ, (if N < k then ρ ^ (k : ℤ) else 0)) := by
    have hpt : (fun k : ℕ => if N < k + 1 then C * ρ ^ ((k + 1 : ℕ) : ℤ) else 0)
        = fun k => C * (if N < k + 1 then ρ ^ ((k + 1 : ℕ) : ℤ) else 0) := by
      funext k
      by_cases h : N < k + 1 <;> simp [h]
    rw [hpt, tsum_mul_left]
    congr 1
    have hbase : Summable fun j : ℕ => (if N < j then ρ ^ (j : ℤ) else 0) :=
      summable_geomTail ρ hρpos hρ1 N
    have h := hbase.sum_add_tsum_nat_add 1
    have h0 : (if N < 0 then ρ ^ ((0 : ℕ) : ℤ) else 0) = 0 := by simp
    rw [Finset.sum_range_one, h0, zero_add] at h
    exact h
  rw [hfval, hgval, geomTail_nat ρ hρpos hρ1 N]
  ring

/-- Lemma 4, Eqs. (65) and (73): the truncated correction loses at most
`2 C ρ^{N+1}/(1-ρ)` of weight beyond power `N`, for coefficients decaying like
`C ρ^{|m|}`.  With `C = 2^r` and `ρ = zζ/M` this is the paper's
`≲ 2^{r+1} (zζ/M)^{N+1}`. -/
theorem lemma4_tail_le (a : ℤ → ℂ) (C ρ : ℝ)
    (hρpos : 0 < ρ) (hρ1 : ρ < 1)
    (hdecay : ∀ m : ℤ, ‖a m‖ ≤ C * ρ ^ (((m.natAbs : ℕ)) : ℤ)) (N : ℕ) :
    (∑' m : ℤ, (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then ‖a m‖ else 0))
      ≤ 2 * (C * ρ ^ ((N : ℤ) + 1) / (1 - ρ)) := by
  classical
  have hgeomS := summable_geomTail_int C ρ hρpos hρ1 N
  have hle : ∀ m : ℤ, (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then ‖a m‖ else 0)
      ≤ (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then C * ρ ^ (((m.natAbs : ℕ)) : ℤ) else 0) := by
    intro m
    by_cases h : (N : ℤ) < ((m.natAbs : ℕ) : ℤ)
    · rw [if_pos h, if_pos h]
      exact hdecay m
    · rw [if_neg h, if_neg h]
  have hsumS : Summable fun m : ℤ =>
      (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then ‖a m‖ else 0) :=
    Summable.of_nonneg_of_le (fun m => by split <;> simp) hle hgeomS
  calc (∑' m : ℤ, (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then ‖a m‖ else 0))
      ≤ ∑' m : ℤ, (if (N : ℤ) < ((m.natAbs : ℕ) : ℤ) then C * ρ ^ (((m.natAbs : ℕ)) : ℤ) else 0) :=
        hsumS.tsum_le_tsum hle hgeomS
    _ = 2 * (C * ρ ^ ((N : ℤ) + 1) / (1 - ρ)) := geomTail_int C ρ hρpos hρ1 N

/-- Lemma 7, Eq. (97): the same tail bound in the second round, with
`ρ' = zζζ' 2^{1/M}/M` and cutoff `N'`. -/
theorem lemma7_tail_le (a' : ℤ → ℂ) (C ρ' : ℝ)
    (hρpos : 0 < ρ') (hρ1 : ρ' < 1)
    (hdecay : ∀ m : ℤ, ‖a' m‖ ≤ C * ρ' ^ (((m.natAbs : ℕ)) : ℤ)) (N' : ℕ) :
    (∑' m : ℤ, (if (N' : ℤ) < ((m.natAbs : ℕ) : ℤ) then ‖a' m‖ else 0))
      ≤ 2 * (C * ρ' ^ ((N' : ℤ) + 1) / (1 - ρ')) :=
  lemma4_tail_le a' C ρ' hρpos hρ1 hdecay N'

end Qatlib.Papers.CorrWalkSim16.MainResults
