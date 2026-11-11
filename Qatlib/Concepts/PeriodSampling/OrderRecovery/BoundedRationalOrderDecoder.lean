/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.ModularOrderPhaseReadout

/-!
# Bounded rational decoding for modular orders

This module defines `boundedRationalDecode`, which scans reduced fractions with denominator at
most a prescribed bound, and `verifiedOrderDecode`, which checks a decoded denominator by
modular exponentiation. The rational approximation step follows the order-finding framework of
[Shor1997].

Uniqueness holds when `2 * B ^ 2 < M`; the scan examines at most `B * (B + 1) / 2` candidates.
The verified decoder also has an explicit success probability bound under `modularOrderLaw`.

## Main statements

* `bounded_rational_actual_decoder_unique_recovery`: unique recovery from a sufficiently narrow
  rational window, with a scan bound.
* `modular_order_actual_verified_success_lower_bound`: a lower bound of `8 / π² * φ(r) / r` for
  recovering the order.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery

/-- The list of pairs `(p, q)` with `1 ≤ q ≤ B` and `p < q`, ordered first by denominator. -/
def boundedRationalPairs (B : ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 B).flatMap fun q => (List.range q).map fun p => (p, q)

/-- Tests coprimality of a candidate numerator and denominator and the integer window inequality
`|y * q - p * M| ≤ q`. -/
def boundedRationalAccept (M y : ℕ) (c : ℕ × ℕ) : Bool :=
  decide (Nat.Coprime c.1 c.2 ∧ |(y : ℤ) * c.2 - (c.1 : ℤ) * M| ≤ c.2)

/-- Scans candidates for the first accepted rational pair and returns it together with the
number of candidates tested. -/
def boundedRationalScan (M y : ℕ) : List (ℕ × ℕ) → Option (ℕ × ℕ) × ℕ
  | [] => (none, 0)
  | c :: cs => if boundedRationalAccept M y c then (some c, 1)
      else let rest := boundedRationalScan M y cs; (rest.1, rest.2 + 1)

/-- Scans `boundedRationalPairs B` for a rational approximation to `y / M`, returning failure
with zero work when `M = 0`. -/
def boundedRationalDecode (B M y : ℕ) : Option (ℕ × ℕ) × ℕ :=
  if M = 0 then (none, 0) else boundedRationalScan M y (boundedRationalPairs B)

/-- The number of tests performed by `boundedRationalScan` is at most the length of the
candidate list. -/
theorem boundedRationalScan_count (M y : ℕ) (cs : List (ℕ × ℕ)) :
    (boundedRationalScan M y cs).2 ≤ cs.length := by
  induction cs with
  | nil => simp [boundedRationalScan]
  | cons c cs ih =>
    simp only [boundedRationalScan]
    split <;> simp_all

/-- A pair returned by `boundedRationalScan` belongs to the candidate list and passes
`boundedRationalAccept`. -/
theorem boundedRationalScan_sound (M y : ℕ) (cs : List (ℕ × ℕ)) (c : ℕ × ℕ)
    (h : (boundedRationalScan M y cs).1 = some c) :
    c ∈ cs ∧ boundedRationalAccept M y c = true := by
  induction cs with
  | nil => simp [boundedRationalScan] at h
  | cons d cs ih =>
    simp only [boundedRationalScan] at h
    split at h
    · cases Option.some.inj h
      exact ⟨List.mem_cons_self, by assumption⟩
    · obtain ⟨hc, ha⟩ := ih h
      exact ⟨List.mem_cons_of_mem d hc, ha⟩

/-- Membership of `(p, q)` in `boundedRationalPairs B` is equivalent to `0 < q`, `q ≤ B`, and `p
< q`. -/
theorem mem_boundedRationalPairs (B : ℕ) (p q : ℕ) :
    (p, q) ∈ boundedRationalPairs B ↔ 0 < q ∧ q ≤ B ∧ p < q := by
  simp only [boundedRationalPairs, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨d, hd, n, hn, he⟩
    cases he
    have hd' := List.mem_range'_1.mp hd
    omega
  · rintro ⟨hq, hB, hp⟩
    exact ⟨q, List.mem_range'_1.mpr ⟨hq, by omega⟩, p, hp, rfl⟩

/-- Twice the length of `boundedRationalPairs B` equals `B * (B + 1)`. -/
theorem boundedRationalPairs_length_two (B : ℕ) :
    (boundedRationalPairs B).length * 2 = B * (B + 1) := by
  have hlen : (boundedRationalPairs B).length = (List.range' 1 B).sum := by
    simp [boundedRationalPairs, List.length_flatMap]
  rw [hlen]
  exact sum_range'_one_mul_two B

/-- The bounded rational decoder tests at most `B * (B + 1) / 2` candidates. -/
theorem boundedRationalDecode_count (B M y : ℕ) :
    (boundedRationalDecode B M y).2 ≤ B * (B + 1) / 2 := by
  have hlen := boundedRationalPairs_length_two B
  have hc := boundedRationalScan_count M y (boundedRationalPairs B)
  unfold boundedRationalDecode
  split
  · simp
  · omega

/-- A returned rational pair has a positive denominator at most `B`, numerator below its
denominator, and passes the acceptance test. -/
theorem boundedRationalDecode_sound (B M y p q : ℕ)
    (h : (boundedRationalDecode B M y).1 = some (p, q)) :
    0 < q ∧ q ≤ B ∧ p < q ∧ boundedRationalAccept M y (p, q) = true := by
  unfold boundedRationalDecode at h
  split at h
  · simp at h
  · obtain ⟨hm, ha⟩ := boundedRationalScan_sound M y _ _ h
    obtain ⟨hq, hB, hp⟩ := (mem_boundedRationalPairs B p q).mp hm
    exact ⟨hq, hB, hp, ha⟩

/-- For positive `M` and `q`, the rational approximation window of radius `1 / M` is equivalent
to `|y * q - p * M| ≤ q` over the integers. -/
theorem boundedRational_window_iff (M y p q : ℕ) (hM : 0 < M) (hq : 0 < q) :
    |(y : ℚ) / M - (p : ℚ) / q| ≤ 1 / (M : ℚ) ↔
    |(y : ℤ) * q - (p : ℤ) * M| ≤ q := by
  have hMQ : (0 : ℚ) < M := by exact_mod_cast hM
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have he : (y : ℚ) / M - (p : ℚ) / q =
      ((y : ℚ) * q - (p : ℚ) * M) / ((M : ℚ) * q) := by
    field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hMQ hqQ), div_le_iff₀ (mul_pos hMQ hqQ)]
  have hc : (1 / (M : ℚ)) * ((M : ℚ) * q) = q := by field_simp
  rw [hc]
  exact_mod_cast (Iff.rfl :
    |(y : ℤ) * q - (p : ℤ) * M| ≤ q ↔ |(y : ℤ) * q - (p : ℤ) * M| ≤ q)

/-- Two reduced fractions with positive denominators at most `B` satisfying the integer
acceptance window coincide when `2 * B ^ 2 < M`. -/
theorem boundedRational_accept_unique (B M y p q u v : ℕ)
    (hq : 0 < q) (hv : 0 < v) (hqB : q ≤ B) (hvB : v ≤ B)
    (hpq : Nat.Coprime p q) (huv : Nat.Coprime u v) (hsize : 2 * B ^ 2 < M)
    (hp : |(y : ℤ) * q - (p : ℤ) * M| ≤ q)
    (hu : |(y : ℤ) * v - (u : ℤ) * M| ≤ v) : (p, q) = (u, v) := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hvZ : (0 : ℤ) < v := by exact_mod_cast hv
  have hqBZ : (q : ℤ) ≤ B := by exact_mod_cast hqB
  have hvBZ : (v : ℤ) ≤ B := by exact_mod_cast hvB
  have hsizeZ : 2 * (B : ℤ) ^ 2 < M := by exact_mod_cast hsize
  obtain ⟨hpL, hpU⟩ := abs_le.mp hp
  obtain ⟨huL, huU⟩ := abs_le.mp hu
  have hprod : (q : ℤ) * v ≤ (B : ℤ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqBZ) (sub_nonneg.mpr hvBZ),
      mul_nonneg (sub_nonneg.mpr hqBZ) (by positivity : (0 : ℤ) ≤ v),
      mul_nonneg (sub_nonneg.mpr hvBZ) (by positivity : (0 : ℤ) ≤ q)]
  have hdetU : (M : ℤ) * ((p : ℤ) * v - (u : ℤ) * q) ≤ 2 * (q : ℤ) * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpL) hvZ.le,
      mul_nonneg (sub_nonneg.mpr huU) hqZ.le]
  have hdetL : -(2 * (q : ℤ) * v) ≤ (M : ℤ) * ((p : ℤ) * v - (u : ℤ) * q) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpU) hvZ.le,
      mul_nonneg (sub_nonneg.mpr huL) hqZ.le]
  have hdet : (p : ℤ) * v - (u : ℤ) * q = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hg
    · have hh : (p : ℤ) * v - (u : ℤ) * q ≤ -1 := by omega
      nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ M)
        (by omega : 0 ≤ -1 - ((p : ℤ) * v - (u : ℤ) * q))]
    · have hh : 1 ≤ (p : ℤ) * v - (u : ℤ) * q := by omega
      nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ M)
        (by omega : 0 ≤ ((p : ℤ) * v - (u : ℤ) * q) - 1)]
  have he : ((p : ℤ) : ℚ) / (q : ℤ) = ((u : ℤ) : ℚ) / (v : ℤ) := by
    apply (div_eq_div_iff (by exact_mod_cast hq.ne') (by exact_mod_cast hv.ne')).mpr
    exact_mod_cast (sub_eq_zero.mp hdet)
  have hinj := Rat.div_int_inj hqZ hvZ (by simpa using! hpq) (by simpa using! huv) he
  have hp' : p = u := by exact_mod_cast hinj.1
  have hq' : q = v := by exact_mod_cast hinj.2
  simp [hp', hq']

/-- If a candidate is accepted and every accepted candidate equals it, the scan returns that
candidate. -/
theorem boundedRationalScan_unique (M y : ℕ) (cs : List (ℕ × ℕ)) (c : ℕ × ℕ)
    (hc : c ∈ cs) (ha : boundedRationalAccept M y c = true)
    (hu : ∀ d ∈ cs, boundedRationalAccept M y d = true → d = c) :
    (boundedRationalScan M y cs).1 = some c := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    simp only [boundedRationalScan]
    split
    · have he := hu d List.mem_cons_self (by assumption)
      simp [he]
    · apply ih
      · rcases List.mem_cons.mp hc with h | h
        · subst d
          contradiction
        · exact h
      · exact fun e he => hu e (List.mem_cons_of_mem d he)

/-- Under `2 * B ^ 2 < M`, a reduced fraction with denominator at most `B` within `1 / M` of `y
/ M` is recovered with at most `B * (B + 1) / 2` tests, assuming `y < M` and numerator below
denominator. This is the bounded rational recovery step for order finding [Shor1997]. -/
theorem bounded_rational_actual_decoder_unique_recovery :
    ∀ (B M y p q : ℕ), 0 < q → q ≤ B → p < q → Nat.Coprime p q →
      2 * B ^ 2 < M → y < M →
      |(y : ℚ) / (M : ℚ) - (p : ℚ) / (q : ℚ)| ≤ 1 / (M : ℚ) →
      (boundedRationalDecode B M y).1 = some (p, q) ∧
        (boundedRationalDecode B M y).2 ≤ B * (B + 1) / 2 := by
  intro B M y p q hq hqB hpq hc hsize _hy hw
  have hM : 0 < M := by omega
  have hwZ := (boundedRational_window_iff M y p q hM hq).mp hw
  refine ⟨?_, boundedRationalDecode_count B M y⟩
  unfold boundedRationalDecode
  rw [if_neg hM.ne']
  apply boundedRationalScan_unique
  · exact (mem_boundedRationalPairs B p q).mpr ⟨hq, hqB, hpq⟩
  · exact decide_eq_true ⟨hc, hwZ⟩
  · rintro ⟨u, v⟩ hmem ha
    obtain ⟨hv, hvB, _⟩ := (mem_boundedRationalPairs B u v).mp hmem
    have ha' : Nat.Coprime u v ∧ |(y : ℤ) * v - (u : ℤ) * M| ≤ v := by
      simpa [boundedRationalAccept] using! ha
    exact (boundedRational_accept_unique B M y p q u v hq hv hqB hvB
      hc ha'.1 hsize hwZ ha'.2).symm

/-- Computes the product of `q` copies of the modular unit `a` by successive multiplication. -/
def orderVerificationProduct (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : ℕ → (ZMod N)ˣ
  | 0 => 1
  | q + 1 => orderVerificationProduct N a q * a

/-- The successive multiplication product `orderVerificationProduct N a q` equals `a ^ q`. -/
theorem orderVerificationProduct_eq_pow (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (q : ℕ) :
    orderVerificationProduct N a q = a ^ q := by
  induction q with
  | zero => simp [orderVerificationProduct]
  | succ q ih => simp [orderVerificationProduct, ih, pow_succ]

/-- Decodes a bounded rational denominator and returns it only if its verification product is
one, recording scan and multiplication counts. -/
def verifiedOrderDecode (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y : Fin M) :
    Option ℕ × (ℕ × ℕ) :=
  let decoded := boundedRationalDecode N M y.val
  match decoded.1 with
  | none => (none, (decoded.2, 0))
  | some (_, q) =>
    (if orderVerificationProduct N a q = 1 then some q else none, (decoded.2, q))

/-- The verified decoder uses at most `N * (N + 1) / 2` rational tests and `N` verification
multiplications; every returned exponent satisfies `a ^ q = 1`. -/
theorem verifiedOrderDecode_sound_and_work (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (y : Fin M) :
    (verifiedOrderDecode N M a y).2.1 ≤ N * (N + 1) / 2 ∧
    (verifiedOrderDecode N M a y).2.2 ≤ N ∧
    ∀ q, (verifiedOrderDecode N M a y).1 = some q → a ^ q = 1 := by
  have hc := boundedRationalDecode_count N M y.val
  unfold verifiedOrderDecode
  (try dsimp only)
  cases hd : (boundedRationalDecode N M y.val).1 with
  | none => simp [hc]
  | some c =>
    obtain ⟨p, q⟩ := c
    have hq := (boundedRationalDecode_sound N M y.val p q hd).2.1
    (try dsimp only)
    refine ⟨hc, hq, ?_⟩
    intro k hk
    split at hk
    · cases Option.some.inj hk
      simpa [orderVerificationProduct_eq_pow] using! ‹orderVerificationProduct N a q = 1›
    · simp at hk

/-- The multiplicative order of a unit modulo `N` is at most `N`. -/
theorem modular_order_le_modulus (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : orderOf a ≤ N := by
  calc orderOf a ≤ Fintype.card (ZMod N)ˣ := orderOf_le_card_univ
    _ ≤ Fintype.card (ZMod N) :=
      Fintype.card_le_of_injective (fun u : (ZMod N)ˣ => (u : ZMod N))
        (fun _ _ h => Units.ext h)
    _ = N := ZMod.card N

/-- A circular phase window gives the ordinary absolute difference bound when the center lies
more than `ε` from both endpoints and the sample lies in `[0, 1)`. -/
theorem phaseDistance_window_unwrap (x t ε : ℝ) (hx : ε < x) (hx' : x < 1 - ε)
    (ht : 0 ≤ t) (ht' : t < 1) (hw : phaseDistance x t ≤ ε) : |t - x| ≤ ε := by
  let n : ℤ := ⌊x - t + 1 / 2⌋
  change |x - t - (n : ℝ)| ≤ ε at hw
  obtain ⟨hL, hU⟩ := abs_le.mp hw
  have hn : n = 0 := by
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have hz : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith
    · exact hn
    · have hz : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith
  rw [hn, Int.cast_zero, sub_zero] at hw
  simpa [abs_sub_comm] using! hw

/-- If the order exceeds one, `2 * N ^ 2 < M`, and a sample lies within circular distance `1 /
M` of a coprime order phase, the verified decoder returns the exact order. -/
theorem verifiedOrderDecode_of_coprime_window (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M) (s : Fin (orderOf a))
    (hs : Nat.Coprime s.val (orderOf a)) (y : Fin M)
    (hw : phaseDistance ((s.val : ℝ) / (orderOf a : ℝ)) ((y.val : ℝ) / M) ≤
      1 / (M : ℝ)) : (verifiedOrderDecode N M a y).1 = some (orderOf a) := by
  have hrN := modular_order_le_modulus N a
  have hM : 0 < M := by omega
  have hrM : orderOf a < M := by nlinarith
  have hs0 : 0 < s.val := by
    by_contra h
    have hz : s.val = 0 := by omega
    rw [hz, Nat.coprime_zero_left] at hs
    omega
  have hrr : (0 : ℝ) < orderOf a := by exact_mod_cast (modular_order_pos N a)
  have hMM : (0 : ℝ) < M := by exact_mod_cast hM
  have heps : 1 / (M : ℝ) < 1 / (orderOf a : ℝ) :=
    one_div_lt_one_div_of_lt hrr (by exact_mod_cast hrM)
  have hs1 : (1 : ℝ) ≤ s.val := by exact_mod_cast hs0
  have hsr : (s.val : ℝ) + 1 ≤ orderOf a := by exact_mod_cast s.isLt
  have hx : 1 / (M : ℝ) < (s.val : ℝ) / (orderOf a : ℝ) := by
    exact heps.trans_le ((div_le_div_iff_of_pos_right hrr).mpr hs1)
  have hx' : (s.val : ℝ) / (orderOf a : ℝ) < 1 - 1 / (M : ℝ) := by
    have hle : (s.val : ℝ) / (orderOf a : ℝ) ≤ 1 - 1 / (orderOf a : ℝ) := by
      apply (div_le_iff₀ hrr).mpr
      field_simp
      linarith
    linarith
  have ht : 0 ≤ (y.val : ℝ) / (M : ℝ) := by positivity
  have ht' : (y.val : ℝ) / (M : ℝ) < 1 :=
    (div_lt_one hMM).mpr (by exact_mod_cast y.isLt)
  have hordinary := phaseDistance_window_unwrap _ _ _ hx hx' ht ht' hw
  have hQ : |(y.val : ℚ) / M - (s.val : ℚ) / (orderOf a : ℚ)| ≤ 1 / (M : ℚ) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa using! hordinary
  have hsizeR : 2 * N ^ 2 < M := hsize
  have hd := (bounded_rational_actual_decoder_unique_recovery N M y.val s.val
    (orderOf a) (modular_order_pos N a) hrN s.isLt hs hsizeR y.isLt hQ).1
  unfold verifiedOrderDecode
  simp only [hd]
  rw [orderVerificationProduct_eq_pow, pow_orderOf_eq_one]
  simp

/-- The number of indices in `Fin r` coprime to `r` equals `Nat.totient r`. -/
theorem card_coprime_order_indices (r : ℕ) :
    (Finset.univ.filter (fun s : Fin r => Nat.Coprime s.val r)).card = Nat.totient r := by
  rw [Nat.totient_eq_card_coprime, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  simpa only [Nat.coprime_comm] using!
    (Fin.sum_univ_eq_sum_range (fun i => if Nat.Coprime i r then (1 : ℕ) else 0) r)

/-- For nontrivial modulus and order with `2 * N ^ 2 < M`, the probability that the verified
decoder returns the exact order is at least `8 / π² * φ(r) / r`. Here `r = orderOf a` and
samples follow `modularOrderLaw` [Shor1997]. -/
theorem modular_order_actual_verified_success_lower_bound :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M),
      1 < N → 1 < orderOf a → 2 * N ^ 2 < M →
      (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        (verifiedOrderDecode N M a y).1 = some (orderOf a)),
        (modularOrderLaw N M a hM).prob y) ≥
          8 / Real.pi ^ 2 * (Nat.totient (orderOf a) : ℝ) / (orderOf a : ℝ) := by
  intro N M _ a hM hN hr hsize
  classical
  let good := Finset.univ.filter (fun y : Fin M =>
    (verifiedOrderDecode N M a y).1 = some (orderOf a))
  let cop := Finset.univ.filter (fun s : Fin (orderOf a) => Nat.Coprime s.val (orderOf a))
  let mass := fun s : Fin (orderOf a) =>
    ∑ y ∈ good, ‖qpeKernel M ((s.val : ℝ) / (orderOf a : ℝ)) y‖ ^ 2
  have hm : ∀ s ∈ cop, 8 / Real.pi ^ 2 ≤ mass s := by
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    have hsub : Finset.univ.filter (fun y : Fin M =>
      phaseDistance ((s.val : ℝ) / (orderOf a : ℝ)) ((y.val : ℝ) / M) ≤ 1 / (M : ℝ)) ⊆ good := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        verifiedOrderDecode_of_coprime_window N M a hr hsize s hs' y (Finset.mem_filter.mp hy).2⟩
    exact (offgrid_phase_window_probability M ((s.val : ℝ) / (orderOf a : ℝ))
      (by nlinarith)).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro y _ _
        positivity))
  have hmass : (Nat.totient (orderOf a) : ℝ) * (8 / Real.pi ^ 2) ≤ ∑ s, mass s := by
    calc (Nat.totient (orderOf a) : ℝ) * (8 / Real.pi ^ 2)
        = ∑ _s ∈ cop, (8 / Real.pi ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          exact_mod_cast (card_coprime_order_indices (orderOf a)).symm
      _ ≤ ∑ s ∈ cop, mass s := Finset.sum_le_sum hm
      _ ≤ ∑ s, mass s := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro s _ _
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have he : (∑ y ∈ good, (modularOrderLaw N M a hM).prob y) =
      (1 / (orderOf a : ℝ)) * ∑ s, mass s := by
    simp_rw [modular_order_born_uniform_orbit_spectrum N M a hM _ hN]
    rw [← Finset.mul_sum, Finset.sum_comm]
  change _ ≤ ∑ y ∈ good, (modularOrderLaw N M a hM).prob y
  rw [he]
  have hpos : 0 ≤ 1 / (orderOf a : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left hmass hpos
  convert! h using 1
  ring

end Qatlib.Concepts.PeriodSampling.OrderRecovery
