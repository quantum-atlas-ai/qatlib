/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Counted continued fraction decoding

Defines rational continued fraction convergents with a recursion count, a logarithmic depth
bound, and the candidate decoder `cfRationalDecode`. The decoder records both candidate scans
and convergent generation work.

Proves stabilization, soundness, and recovery of a reduced fraction within a `1 / M` window when
`2 * B ^ 2 < M`. This is the continued fraction postprocessing used in order finding [Shor1997].

## Main statements

* `rational_convergent_logarithmic_stabilization`: bounds the depth needed to recover a rational
  input.
* `continued_fraction_unique_window_decode_and_counts`: proves window recovery with explicit
  work bounds.
* `cfRationalDecode_eq_bounded`: identifies the decoded result with bounded rational search.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.OrderRecovery

namespace Qatlib.Concepts.HspRecovery.CfOrder
open scoped Classical
set_option maxHeartbeats 2000000

/-- Computes a rational continued fraction convergent together with the number of recursive
stages used. -/
def ratConvergentCounted : ℚ → ℕ → ℚ × ℕ
  | q, 0 => (⌊q⌋, 1)
  | q, k + 1 => let s := ratConvergentCounted (q - (⌊q⌋ : ℚ))⁻¹ k
                ((⌊q⌋ : ℚ) + s.1⁻¹, s.2 + 1)

/-- The continued fraction depth bound `2 * (Nat.log 2 M + 1) + 2`. -/
def cfDepth (M : ℕ) : ℕ := 2 * (Nat.log 2 M + 1) + 2

/-- Lists convergents of `y / M` through `cfDepth M` whose canonical numerator is nonnegative
and smaller than their denominator, with denominator at most `B`. -/
def cfCandidates (B M y : ℕ) : List (ℕ × ℕ) :=
  (List.range (cfDepth M + 1)).filterMap (fun k =>
    let q := (ratConvergentCounted ((y : ℚ) / M) k).1
    if 0 ≤ q.num ∧ q.num.toNat < q.den ∧ q.den ≤ B then some (q.num.toNat, q.den) else none)

/-- The total recursion count for generating every convergent through depth `cfDepth M`. -/
def cfGenerationWork (M y : ℕ) : ℕ :=
  ((List.range (cfDepth M + 1)).map (fun k => (ratConvergentCounted ((y : ℚ) / M) k).2)).sum

/-- Scans the bounded continued fraction candidates for a rational reconstruction and returns
the result, scan count, and generation work. A zero modulus returns no result and zero
counts. -/
def cfRationalDecode (B M y : ℕ) : Option (ℕ × ℕ) × ℕ × ℕ :=
  if M = 0 then (none, 0, 0) else
    let s := boundedRationalScan M y (cfCandidates B M y)
    (s.1, s.2, cfGenerationWork M y)

/-- The computed rational convergent agrees with `Real.convergent` after casting to the reals,
and its recursion count is `k + 1`. -/
theorem rational_convergent_cast_and_actual_work (q : ℚ) (k : ℕ) :
    ((ratConvergentCounted q k).1 : ℝ) = (Real.convergent (q : ℝ) k : ℝ) ∧
    (ratConvergentCounted q k).2 = k + 1 := by
  induction k generalizing q with
  | zero => simp [ratConvergentCounted, Rat.floor_cast]
  | succ k ih =>
    have hi := ih (q - (⌊q⌋ : ℚ))⁻¹
    have hnext : (((q - (⌊q⌋ : ℚ))⁻¹ : ℚ) : ℝ) = (Int.fract (q : ℝ))⁻¹ := by
      simp only [Rat.cast_inv, Rat.cast_sub, Rat.cast_intCast, Int.fract, Rat.floor_cast]
    constructor
    · simp only [ratConvergentCounted, Rat.cast_add, Rat.cast_intCast, Rat.cast_inv,
        hi.1, hnext, Real.convergent_succ, Rat.floor_cast]
    · simp only [ratConvergentCounted, hi.2]

/-- Every counted continued fraction convergent of zero has value zero. -/
private theorem cf_zero (k : ℕ) : (ratConvergentCounted 0 k).1 = 0 := by
  induction k with
  | zero => simp [ratConvergentCounted]
  | succ k ih => simpa [ratConvergentCounted] using! ih

/-- The reciprocal fractional part of `a / b` equals `b / (a % b)` in the rationals. -/
private theorem cf_fraction_next (a b : ℕ) :
    ((a : ℚ) / b - (⌊(a : ℚ) / b⌋ : ℚ))⁻¹ = (b : ℚ) / (a % b : ℕ) := by
  by_cases hb : b = 0
  · simp [hb]
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hf : ⌊(a : ℚ) / b⌋ = ((a / b : ℕ) : ℤ) := by
    rw [Rat.floor_natCast_div_natCast, Int.natCast_ediv]
  rw [hf, Int.cast_natCast]
  have he : (a : ℚ) / b - (a / b : ℕ) = (a % b : ℕ) / (b : ℚ) := by
    apply (eq_div_iff hbQ).mpr
    have hd : (b : ℚ) * (a / b : ℕ) + (a % b : ℕ) = a := by
      exact_mod_cast Nat.div_add_mod a b
    field_simp
    nlinarith [hd]
  rw [he, inv_div]

/-- For positive `b`, reassembling the integral part of `a / b` with the reciprocal of `b / (a %
b)` recovers `a / b`. -/
private theorem cf_fraction_reassemble (a b : ℕ) (_hb : 0 < b) :
    (⌊(a : ℚ) / b⌋ : ℚ) + ((b : ℚ) / (a % b : ℕ))⁻¹ = (a : ℚ) / b := by
  rw [← cf_fraction_next, inv_inv]
  ring

/-- Two successive Euclidean remainder steps reduce a positive denominator by more than a factor
of two when the first remainder is positive. -/
private theorem cf_two_rem_half (a b : ℕ) (hb : 0 < b) (hr : 0 < a % b) :
    2 * (b % (a % b)) < b := by
  have hlt := Nat.mod_lt a hb
  have hlt' := Nat.mod_lt b hr
  by_cases hhalf : 2 * (a % b) ≤ b
  · omega
  · have hd : b / (a % b) = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    have he := Nat.div_add_mod b (a % b)
    rw [hd] at he
    omega

/-- For `b < 2 ^ t`, every counted convergent of `a / b` at depth at least `2 * t` equals `a /
b`. -/
private theorem cf_fraction_stable_pow (t a b k : ℕ)
    (hb : b < 2 ^ t) (hk : 2 * t ≤ k) :
    (ratConvergentCounted ((a : ℚ) / b) k).1 = (a : ℚ) / b := by
  induction t generalizing a b k with
  | zero =>
    have hz : b = 0 := by simpa using! hb
    simp [hz, cf_zero]
  | succ t ih =>
    by_cases hb0 : b = 0
    · simp [hb0, cf_zero]
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    obtain ⟨k, rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
    by_cases hr : a % b = 0
    · simp only [ratConvergentCounted]
      rw [cf_fraction_next]
      simp only [hr, Nat.cast_zero, div_zero, Int.floor_zero, Int.cast_zero,
        sub_zero, inv_zero, cf_zero, add_zero]
      simpa [hr] using! cf_fraction_reassemble a b hbpos
    · have hhalf := cf_two_rem_half a b hbpos (Nat.pos_of_ne_zero hr)
      have hb' : b % (a % b) < 2 ^ t := by
        rw [pow_succ] at hb
        omega
      have hi := ih (a % b) (b % (a % b)) k hb' (by omega)
      simp only [ratConvergentCounted]
      rw [cf_fraction_next, cf_fraction_next, hi, cf_fraction_reassemble b (a % b) (Nat.pos_of_ne_zero hr),
        cf_fraction_reassemble a b hbpos]

/-- For positive `M` and `y < M`, convergents of `y / M` stabilize by depth `cfDepth M`. -/
theorem rational_convergent_logarithmic_stabilization (M y k : ℕ)
    (_hM : 0 < M) (_hy : y < M) (hk : cfDepth M ≤ k) :
    (ratConvergentCounted ((y : ℚ) / M) k).1 = (y : ℚ) / M := by
  apply cf_fraction_stable_pow (Nat.log 2 M + 1)
  · exact Nat.lt_pow_of_log_lt (by decide) (by omega)
  · dsimp [cfDepth] at hk
    omega

/-- The total convergent generation work is `(cfDepth M + 1) * (cfDepth M + 2) / 2`. -/
theorem cfGenerationWork_eq (M y : ℕ) :
    cfGenerationWork M y = (cfDepth M + 1) * (cfDepth M + 2) / 2 := by
  unfold cfGenerationWork
  simp_rw [(rational_convergent_cast_and_actual_work _ _).2]
  have hh (n : ℕ) : ((List.range n).map (fun k => k + 1)).sum * 2 = n * (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero]
      nlinarith
  rw [← hh (cfDepth M + 1), Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Every candidate has a positive denominator at most `B`, a smaller numerator, and coprime
numerator and denominator. -/
private theorem cfCandidates_bounds (B M y p q : ℕ) (h : (p, q) ∈ cfCandidates B M y) :
    0 < q ∧ q ≤ B ∧ p < q ∧ Nat.Coprime p q := by
  simp only [cfCandidates, List.mem_filterMap] at h
  obtain ⟨k, _, hk⟩ := h
  split at hk
  · rename_i hh
    obtain ⟨hn, hp, hB⟩ := hh
    cases Option.some.inj hk
    refine ⟨Rat.den_pos _, hB, hp, ?_⟩
    have he' : ((ratConvergentCounted ((y : ℚ) / M) k).1).num.natAbs =
        ((ratConvergentCounted ((y : ℚ) / M) k).1).num.toNat := by omega
    simpa only [he'] using! ((ratConvergentCounted ((y : ℚ) / M) k).1).reduced
  · simp at hk

/-- Bounds the decoder's scan and generation counts and shows that every returned pair is
reduced, has denominator at most `B`, and satisfies `|y * q - p * M| ≤ q` [Shor1997]. -/
theorem continued_fraction_bad_output_soundness_and_work (B M y : ℕ) :
    (cfRationalDecode B M y).2.1 ≤ cfDepth M + 1 ∧
    (cfRationalDecode B M y).2.2 ≤ (cfDepth M + 1) * (cfDepth M + 2) / 2 ∧
    ∀ p q, (cfRationalDecode B M y).1 = some (p, q) →
      0 < q ∧ q ≤ B ∧ p < q ∧ Nat.Coprime p q ∧ |(y : ℤ) * q - (p : ℤ) * M| ≤ q := by
  have hc : (boundedRationalScan M y (cfCandidates B M y)).2 ≤ cfDepth M + 1 :=
    (boundedRationalScan_count _ _ _).trans (by
      simpa [cfCandidates] using! List.length_filterMap_le
        (fun k => let r := (ratConvergentCounted ((y : ℚ) / M) k).1
          if 0 ≤ r.num ∧ r.num.toNat < r.den ∧ r.den ≤ B then some (r.num.toNat, r.den) else none)
        (List.range (cfDepth M + 1)))
  unfold cfRationalDecode
  split
  · simp
  · (try dsimp only)
    refine ⟨hc, (cfGenerationWork_eq M y).le, ?_⟩
    intro p q hpq
    obtain ⟨hmem, ha⟩ := boundedRationalScan_sound M y _ (p, q) hpq
    obtain ⟨hq, hB, hp, hcop⟩ := cfCandidates_bounds B M y p q hmem
    have hh : Nat.Coprime p q ∧ |(y : ℤ) * q - (p : ℤ) * M| ≤ q := by
      simpa [boundedRationalAccept] using! ha
    exact ⟨hq, hB, hp, hcop, hh.2⟩

/-- A reduced nonnegative fraction with positive denominator has canonical numerator `p` and
denominator `q`. -/
private theorem cf_target_num_den (p q : ℕ) (hq : 0 < q) (hc : Nat.Coprime p q) :
    ((p : ℚ) / q).num = (p : ℤ) ∧ ((p : ℚ) / q).den = q := by
  have hn := Rat.num_div_eq_of_coprime (a := (p : ℤ)) (b := (q : ℤ))
    (by exact_mod_cast hq) (by simpa using! hc)
  have hd := Rat.den_div_eq_of_coprime (a := (p : ℤ)) (b := (q : ℤ))
    (by exact_mod_cast hq) (by simpa using! hc)
  refine ⟨by simpa using! hn, ?_⟩
  apply Int.natCast_inj.mp
  simpa only [Int.cast_natCast] using! hd

/-- A reduced proper fraction of denominator at most `B` within `1 / M` of `y / M` occurs among
the candidates when `2 * B ^ 2 < M` and `y < M`. -/
private theorem cf_window_candidate (B M y p q : ℕ) (hq : 0 < q) (hqB : q ≤ B)
    (hp : p < q) (hc : Nat.Coprime p q) (hsize : 2 * B ^ 2 < M) (hy : y < M)
    (hw : |(y : ℚ) / M - (p : ℚ) / q| ≤ 1 / (M : ℚ)) :
    (p, q) ∈ cfCandidates B M y := by
  have hM : 0 < M := by omega
  have ht := cf_target_num_den p q hq hc
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwR : |(y : ℝ) / M - (((p : ℚ) / q : ℚ) : ℝ)| ≤ 1 / (M : ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hw
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one] using! hh
  have hbound : 1 / (M : ℝ) < 1 / (2 * (q : ℝ) ^ 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    have hqBR : (q : ℝ) ≤ B := by exact_mod_cast hqB
    have hsizeR : 2 * (B : ℝ) ^ 2 < M := by exact_mod_cast hsize
    nlinarith [sq_nonneg ((B : ℝ) - q)]
  have hleg : |((y : ℚ) / M : ℝ) - (((p : ℚ) / q : ℚ) : ℝ)| <
      1 / (2 * (((p : ℚ) / q).den : ℝ) ^ 2) := by
    simpa only [Rat.cast_div, Rat.cast_natCast, ht.2] using! hwR.trans_lt hbound
  obtain ⟨j, hj⟩ := Real.exists_rat_eq_convergent hleg
  have hcf : (ratConvergentCounted ((y : ℚ) / M) j).1 = (p : ℚ) / q := by
    apply Rat.cast_injective (α := ℝ)
    rw [(rational_convergent_cast_and_actual_work _ _).1]
    simpa only [Rat.cast_div, Rat.cast_natCast] using!
      congrArg (fun r : ℚ => (r : ℝ)) hj.symm
  have hex : ∃ k, k ≤ cfDepth M ∧ (ratConvergentCounted ((y : ℚ) / M) k).1 = (p : ℚ) / q := by
    by_cases hjD : j ≤ cfDepth M
    · exact ⟨j, hjD, hcf⟩
    · have hs := rational_convergent_logarithmic_stabilization M y j hM hy (by omega)
      have he : (p : ℚ) / q = (y : ℚ) / M := hcf.symm.trans hs
      exact ⟨cfDepth M, le_rfl,
        (rational_convergent_logarithmic_stabilization M y (cfDepth M) hM hy le_rfl).trans he.symm⟩
  obtain ⟨k, hk, he⟩ := hex
  apply List.mem_filterMap.mpr
  refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
  (try dsimp only)
  rw [he, ht.1, ht.2]
  simp [hp, hqB]

/-- The continued fraction decoder recovers a reduced proper fraction in the `1 / M` window when
`2 * B ^ 2 < M`, with the stated scan bound and exact generation count [Shor1997]. -/
theorem continued_fraction_unique_window_decode_and_counts (B M y p q : ℕ)
    (hq : 0 < q) (hqB : q ≤ B) (hp : p < q) (hc : Nat.Coprime p q)
    (hsize : 2 * B ^ 2 < M) (hy : y < M)
    (hw : |(y : ℚ) / M - (p : ℚ) / q| ≤ 1 / (M : ℚ)) :
    (cfRationalDecode B M y).1 = some (p, q) ∧
    (cfRationalDecode B M y).2.1 ≤ cfDepth M + 1 ∧
    (cfRationalDecode B M y).2.2 = (cfDepth M + 1) * (cfDepth M + 2) / 2 := by
  have hM : 0 < M := by omega
  have hz := (boundedRational_window_iff M y p q hM hq).mp hw
  have hmem := cf_window_candidate B M y p q hq hqB hp hc hsize hy hw
  have hdecode : (boundedRationalScan M y (cfCandidates B M y)).1 = some (p, q) := by
    apply boundedRationalScan_unique M y _ _ hmem
    · exact decide_eq_true ⟨hc, hz⟩
    · rintro ⟨u, v⟩ hmem ha
      obtain ⟨hv, hvB, _, hcop⟩ := cfCandidates_bounds B M y u v hmem
      have ha' : Nat.Coprime u v ∧ |(y : ℤ) * v - (u : ℤ) * M| ≤ v := by
        simpa [boundedRationalAccept] using! ha
      exact (boundedRational_accept_unique B M y p q u v hq hv hqB hvB hc hcop
        hsize hz ha'.2).symm
  refine ⟨?_, (continued_fraction_bad_output_soundness_and_work B M y).1, ?_⟩
  · simpa [cfRationalDecode, hM.ne'] using! hdecode
  · simp [cfRationalDecode, hM.ne', cfGenerationWork_eq]

/-- When `2 * B ^ 2 < M` and `y < M`, continued fraction decoding and bounded rational decoding
return the same optional pair. -/
theorem cfRationalDecode_eq_bounded (B M y : ℕ) (hsize : 2 * B ^ 2 < M) (hy : y < M) :
    (cfRationalDecode B M y).1 = (boundedRationalDecode B M y).1 := by
  have hM : 0 < M := by omega
  cases ho : (boundedRationalDecode B M y).1 with
  | none =>
    cases hn : (cfRationalDecode B M y).1 with
    | none => rfl
    | some r =>
      obtain ⟨p, q⟩ := r
      obtain ⟨hq, hqB, hp, hc, hz⟩ :=
        (continued_fraction_bad_output_soundness_and_work B M y).2.2 p q hn
      have hw := (boundedRational_window_iff M y p q hM hq).mpr hz
      have hh := (bounded_rational_actual_decoder_unique_recovery B M y p q hq hqB
        hp hc hsize hy hw).1
      rw [ho] at hh
      simp at hh
  | some r =>
    obtain ⟨p, q⟩ := r
    obtain ⟨hq, hqB, hp, ha⟩ := boundedRationalDecode_sound B M y p q ho
    have ha' : Nat.Coprime p q ∧ |(y : ℤ) * q - (p : ℤ) * M| ≤ q := by
      simpa [boundedRationalAccept] using! ha
    exact (continued_fraction_unique_window_decode_and_counts B M y p q hq hqB hp ha'.1
      hsize hy ((boundedRational_window_iff M y p q hM hq).mpr ha'.2)).1
end Qatlib.Concepts.HspRecovery.CfOrder
