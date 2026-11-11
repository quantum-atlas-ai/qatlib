/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The source-window rational decoder (guard `B² < q`)

Fixed source: `quant-ph/9508027v2` §5, printed pp.19–20, Eqs. (5.11)–(5.13).

The paper chooses a power of two `q` with `n² ≤ q < 2n²`, and claims that when
`|{r c}_q| ≤ r/2`, i.e. when `2|r c - d q| ≤ r` for the nearest integer `d`,
there is at most one reduced fraction `d/r` with `r < n` in that window.  The
installed frozen decoder (`boundedRationalDecode`) instead uses the wider `1/M`
window and therefore needs the stronger guard `2B² < M`; that guard is *not*
implied by the source window `n² ≤ q < 2n²`.

This module supplies the missing half-window decoder.  It searches exactly the
same candidate list as the frozen decoder and accepts a pair `(p, q)` when
`2 |y*q - p*M| ≤ q`, which is equivalent to the paper's
`|y/M - p/q| ≤ 1/(2M)`.  The uniqueness proof is the rational-separation
argument: two accepted reduced fractions with denominators at most `B`
differ by at least `1/B²`, while both lie within `1/(2M)` of the reading, so
`B² < M` forces them to coincide.  Since the source window gives `(n-1)² < n² ≤ q`,
the guard holds with `B = n - 1`.

Everything here is about the *classical* rational decoder and the paper's
inequality (5.13).  It does not implement a continued-fraction program, does not
prove the Born lower bound, and does not account for bit-level cost.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.OrderRecovery

open Qatlib.Concepts.PeriodSampling.OrderRecovery

/-! ## §1. Acceptance test and the source-window uniqueness argument -/

/-- The paper's half-window acceptance test.  The pair is `(p, q)` with `p` the
numerator and `q` the denominator; `M` is the clock and `y` the readout.  It is
the exact integer form of `|y/M - p/q| ≤ 1/(2M)`. -/
def sourceRationalAccept (M y : ℕ) (c : ℕ × ℕ) : Bool :=
  decide (Nat.Coprime c.1 c.2 ∧
    2 * |(y : ℤ) * (c.2 : ℤ) - (c.1 : ℤ) * (M : ℤ)| ≤ (c.2 : ℤ))

/-- **Rational separation at the source window.**  If two reduced fractions with
positive denominators at most `B` both lie in the paper's `1/(2M)` window, and
`B² < M`, then they are the same fraction.  This is the half-window analogue of
`boundedRational_accept_unique`, which needs the stronger `2B² < M`. -/
theorem sourceRational_accept_unique (B M y p q u v : ℕ)
    (hq : 0 < q) (hv : 0 < v) (hqB : q ≤ B) (hvB : v ≤ B)
    (hpq : Nat.Coprime p q) (huv : Nat.Coprime u v) (hsize : B ^ 2 < M)
    (hp : 2 * |(y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)| ≤ (q : ℤ))
    (hu : 2 * |(y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)| ≤ (v : ℤ)) :
    (p, q) = (u, v) := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hvZ : (0 : ℤ) < (v : ℤ) := by exact_mod_cast hv
  have hqBZ : (q : ℤ) ≤ (B : ℤ) := by exact_mod_cast hqB
  have hvBZ : (v : ℤ) ≤ (B : ℤ) := by exact_mod_cast hvB
  have hsizeZ : (B : ℤ) ^ 2 < (M : ℤ) := by exact_mod_cast hsize
  have hMZ : (0 : ℤ) ≤ (M : ℤ) := by positivity
  -- Product bound `q v ≤ B²`.
  have hprod : (q : ℤ) * (v : ℤ) ≤ (B : ℤ) ^ 2 := by
    have := mul_le_mul hqBZ hvBZ (by positivity : (0 : ℤ) ≤ (v : ℤ))
      (by positivity : (0 : ℤ) ≤ (B : ℤ))
    nlinarith [this]
  -- Multiply the two window inequalities by the opposite denominator.
  have hpv : 2 * (v : ℤ) * |(y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)| ≤
      (q : ℤ) * (v : ℤ) := by
    have := mul_le_mul_of_nonneg_right hp hvZ.le
    nlinarith [this]
  have huq : 2 * (q : ℤ) * |(y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)| ≤
      (q : ℤ) * (v : ℤ) := by
    have := mul_le_mul_of_nonneg_right hu hqZ.le
    nlinarith [this]
  -- The determinant is controlled by the two windows.
  have hdet : (M : ℤ) * |(u : ℤ) * (q : ℤ) - (p : ℤ) * (v : ℤ)| ≤
      (q : ℤ) * (v : ℤ) := by
    have hid : (M : ℤ) * ((u : ℤ) * (q : ℤ) - (p : ℤ) * (v : ℤ)) =
        ((y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)) * (v : ℤ) -
          ((y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)) * (q : ℤ) := by
      ring
    calc
      (M : ℤ) * |(u : ℤ) * (q : ℤ) - (p : ℤ) * (v : ℤ)|
          = |(M : ℤ) * ((u : ℤ) * (q : ℤ) - (p : ℤ) * (v : ℤ))| := by
            rw [abs_mul, abs_of_nonneg hMZ]
      _ = |((y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)) * (v : ℤ) -
            ((y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)) * (q : ℤ)| := by rw [hid]
      _ ≤ |((y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)) * (v : ℤ)| +
            |((y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)) * (q : ℤ)| := abs_sub _ _
      _ = |(y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)| * (v : ℤ) +
            |(y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)| * (q : ℤ) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hvZ.le, abs_of_nonneg hqZ.le]
      _ ≤ (q : ℤ) * (v : ℤ) := by nlinarith [hpv, huq]
  -- A nonzero integer determinant is at least one, forcing `M ≤ B²`.
  have hw : (u : ℤ) * (q : ℤ) - (p : ℤ) * (v : ℤ) = 0 := by
    by_contra hne
    have h1 : (1 : ℤ) ≤ |(u : ℤ) * (q : ℤ) - (p : ℤ) * (v : ℤ)| := by
      have := abs_pos.mpr hne
      omega
    have := mul_le_mul_of_nonneg_left h1 hMZ
    nlinarith [hdet, hprod, hsizeZ, this]
  have hdet0 : (u : ℤ) * (q : ℤ) = (p : ℤ) * (v : ℤ) := by
    linear_combination hw
  have hfrac : ((p : ℤ) : ℚ) / ((q : ℤ) : ℚ) = ((u : ℤ) : ℚ) / ((v : ℤ) : ℚ) := by
    have hv' : ((v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
    have hq' : ((q : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [div_eq_div_iff hq' hv']
    exact_mod_cast hdet0.symm
  have hinj := Rat.div_int_inj hqZ hvZ (by simpa using hpq) (by simpa using huv) hfrac
  have hp' : p = u := by exact_mod_cast hinj.1
  have hq' : q = v := by exact_mod_cast hinj.2
  simp [hp', hq']

/-! ## §2. The executable scanner -/

/-- First accepted pair of a generic Boolean test, together with the number of
actual predicate evaluations. -/
def scanAccept (accept : ℕ × ℕ → Bool) : List (ℕ × ℕ) → Option (ℕ × ℕ) × ℕ
  | [] => (none, 0)
  | c :: cs =>
    if accept c then (some c, 1)
    else let rest := scanAccept accept cs; (rest.1, rest.2 + 1)

/-- The scanner never evaluates more pairs than its input length. -/
theorem scanAccept_count (accept : ℕ × ℕ → Bool) (cs : List (ℕ × ℕ)) :
    (scanAccept accept cs).2 ≤ cs.length := by
  induction cs with
  | nil => simp [scanAccept]
  | cons c cs ih =>
    simp only [scanAccept]
    split <;> simp_all

/-- A scanner result is an accepted member of its actual input list. -/
theorem scanAccept_sound (accept : ℕ × ℕ → Bool) (cs : List (ℕ × ℕ)) (c : ℕ × ℕ)
    (h : (scanAccept accept cs).1 = some c) :
    c ∈ cs ∧ accept c = true := by
  induction cs with
  | nil => simp [scanAccept] at h
  | cons d cs ih =>
    simp only [scanAccept] at h
    split at h
    · cases Option.some.inj h
      exact ⟨List.mem_cons_self, by assumption⟩
    · obtain ⟨hc, ha⟩ := ih h
      exact ⟨List.mem_cons_of_mem d hc, ha⟩

/-- If an accepted pair is unique in the list, the scanner returns it. -/
theorem scanAccept_unique (accept : ℕ × ℕ → Bool) (cs : List (ℕ × ℕ)) (c : ℕ × ℕ)
    (hc : c ∈ cs) (ha : accept c = true)
    (hu : ∀ d ∈ cs, accept d = true → d = c) :
    (scanAccept accept cs).1 = some c := by
  induction cs with
  | nil => simp at hc
  | cons e es ih =>
    simp only [scanAccept]
    split
    · have := hu e List.mem_cons_self (by assumption)
      simp [this]
    · apply ih
      · rcases List.mem_cons.mp hc with h | h
        · subst e; contradiction
        · exact h
      · exact fun d hd => hu d (List.mem_cons_of_mem e hd)

/-- The source-window decoder: scan the same bounded candidate list with the
half-window acceptance test.  A zero clock returns no candidate. -/
def sourceRationalDecode (B M y : ℕ) : Option (ℕ × ℕ) × ℕ :=
  if M = 0 then (none, 0) else scanAccept (sourceRationalAccept M y) (boundedRationalPairs B)

/-- The source-window decoder never exceeds the triangular comparison count. -/
theorem sourceRationalDecode_count (B M y : ℕ) :
    (sourceRationalDecode B M y).2 ≤ B * (B + 1) / 2 := by
  have hlen := boundedRationalPairs_length_two B
  have hc := scanAccept_count (sourceRationalAccept M y) (boundedRationalPairs B)
  unfold sourceRationalDecode
  split
  · simp
  · omega

/-- Soundness of the source-window decoder: it returns a reduced pair with
denominator at most `B` that satisfies the paper's window inequality. -/
theorem sourceRationalDecode_sound (B M y p q : ℕ)
    (h : (sourceRationalDecode B M y).1 = some (p, q)) :
    0 < q ∧ q ≤ B ∧ p < q ∧
      2 * |(y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)| ≤ (q : ℤ) := by
  unfold sourceRationalDecode at h
  split at h
  · simp at h
  · obtain ⟨hm, ha⟩ := scanAccept_sound (sourceRationalAccept M y) _ _ h
    obtain ⟨hq, hB, hp⟩ := (mem_boundedRationalPairs B p q).mp hm
    have ha' : Nat.Coprime p q ∧
        2 * |(y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)| ≤ (q : ℤ) := by
      simpa [sourceRationalAccept] using ha
    exact ⟨hq, hB, hp, ha'.2⟩

/-- **Main source-window recovery theorem.**  If the reading `y` lies within
`1/(2M)` of a reduced fraction `p/q` with `q ≤ B` and `B² < M`, the executable
source-window decoder returns exactly `(p, q)`, and the actual comparison count
is at most `B(B+1)/2`.  This matches the paper's guard `q > n²` with
`B = n - 1`. -/
theorem source_rational_actual_decoder_unique_recovery (B M y p q : ℕ)
    (hq : 0 < q) (hqB : q ≤ B) (hpq : Nat.Coprime p q) (hpq' : p < q)
    (hsize : B ^ 2 < M)
    (hw : 2 * |(y : ℤ) * (q : ℤ) - (p : ℤ) * (M : ℤ)| ≤ (q : ℤ)) :
    (sourceRationalDecode B M y).1 = some (p, q) ∧
      (sourceRationalDecode B M y).2 ≤ B * (B + 1) / 2 := by
  have hM : 0 < M := by
    have hb : 0 ≤ B ^ 2 := Nat.zero_le _
    omega
  refine ⟨?_, sourceRationalDecode_count B M y⟩
  unfold sourceRationalDecode
  rw [if_neg hM.ne']
  apply scanAccept_unique
  · exact (mem_boundedRationalPairs B p q).mpr ⟨hq, hqB, hpq'⟩
  · exact decide_eq_true ⟨hpq, hw⟩
  · rintro ⟨u, v⟩ hmem ha
    obtain ⟨hv, hvB, _⟩ := (mem_boundedRationalPairs B u v).mp hmem
    have ha' : Nat.Coprime u v ∧
        2 * |(y : ℤ) * (v : ℤ) - (u : ℤ) * (M : ℤ)| ≤ (v : ℤ) := by
      simpa [sourceRationalAccept] using ha
    exact (sourceRational_accept_unique B M y p q u v hq hv hqB hvB
      hpq ha'.1 hsize hw ha'.2).symm

/-! ## §3. Bridges to the paper's source window and inequality (5.13) -/

/-- The source power-of-two clock satisfies the half-window guard with the
denominator bound `B = n - 1`: from `n² ≤ q` we get `(n-1)² < q`. -/
theorem source_clock_halfwindow_guard (N t : ℕ) (hN : 0 < N) (hlo : N ^ 2 ≤ 2 ^ t) :
    (N - 1) ^ 2 < 2 ^ t := by
  have hlt : N - 1 < N := Nat.sub_one_lt (by omega)
  have hpow : (N - 1) ^ 2 < N ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  omega

/-- The paper's condition (5.12) `|r c - d q| ≤ r/2` implies inequality (5.13)
`|c/q - d/r| ≤ 1/(2q)`.  This is the bridge from the residue window to the
rational window used by the decoder. -/
theorem residue_window_implies_rational_window (r c d q : ℕ) (hr : 0 < r) (hq : 0 < q)
    (h : 2 * |(r : ℤ) * (c : ℤ) - (d : ℤ) * (q : ℤ)| ≤ (r : ℤ)) :
    |(c : ℚ) / (q : ℚ) - (d : ℚ) / (r : ℚ)| ≤ 1 / (2 * (q : ℚ)) := by
  have hrQ : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hQ : (2 : ℚ) * |(r : ℚ) * (c : ℚ) - (d : ℚ) * (q : ℚ)| ≤ (r : ℚ) := by
    have hZ : (2 * |(r : ℤ) * (c : ℤ) - (d : ℤ) * (q : ℤ)| : ℤ) ≤ (r : ℤ) := h
    have hcast : ((2 * |(r : ℤ) * (c : ℤ) - (d : ℤ) * (q : ℤ)| : ℤ) : ℚ) ≤ ((r : ℤ) : ℚ) := by
      exact_mod_cast hZ
    push_cast at hcast
    exact hcast
  have hnum : |(c : ℚ) * (r : ℚ) - (d : ℚ) * (q : ℚ)| ≤ (r : ℚ) / 2 := by
    have he : |(c : ℚ) * (r : ℚ) - (d : ℚ) * (q : ℚ)| =
        |(r : ℚ) * (c : ℚ) - (d : ℚ) * (q : ℚ)| := by ring_nf
    rw [he]
    nlinarith [hQ]
  have hdecomp : (c : ℚ) / (q : ℚ) - (d : ℚ) / (r : ℚ) =
      ((c : ℚ) * (r : ℚ) - (d : ℚ) * (q : ℚ)) / ((q : ℚ) * (r : ℚ)) := by
    field_simp
  rw [hdecomp, abs_div, abs_of_pos (mul_pos hqQ hrQ)]
  have hstep : |(c : ℚ) * (r : ℚ) - (d : ℚ) * (q : ℚ)| / ((q : ℚ) * (r : ℚ)) ≤
      ((r : ℚ) / 2) / ((q : ℚ) * (r : ℚ)) := by
    apply div_le_div_of_nonneg_right hnum
    positivity
  have heq : ((r : ℚ) / 2) / ((q : ℚ) * (r : ℚ)) = 1 / (2 * (q : ℚ)) := by
    field_simp
  rwa [heq] at hstep

/-- **End-to-end source decoder.**  If the readout `c` satisfies the paper's
condition (5.12) `|r c - d q| ≤ r/2` for a reduced fraction `d/r` with
`r ≤ B`, and the clock satisfies `B² < q`, then the executable source-window
decoder returns exactly `d/r` with at most `B(B+1)/2` comparisons.  The integer
acceptance test of `sourceRationalAccept` is literally the same inequality, so
this chain connects the paper's residue window directly to decoded output. -/
theorem residue_window_actual_decoder_recovery
    (B q r c d : ℕ) (hr : 0 < r) (hrB : r ≤ B)
    (hcop : Nat.Coprime d r) (hdr : d < r) (hsize : B ^ 2 < q)
    (h : 2 * |(r : ℤ) * (c : ℤ) - (d : ℤ) * (q : ℤ)| ≤ (r : ℤ)) :
    (sourceRationalDecode B q c).1 = some (d, r) ∧
      (sourceRationalDecode B q c).2 ≤ B * (B + 1) / 2 := by
  refine source_rational_actual_decoder_unique_recovery B q c d r hr hrB hcop hdr hsize ?_
  have he : |(c : ℤ) * (r : ℤ) - (d : ℤ) * (q : ℤ)| =
      |(r : ℤ) * (c : ℤ) - (d : ℤ) * (q : ℤ)| := by ring_nf
  rw [he]
  exact h

/-- **Source clock plus residue window.**  Composing the paper's power-of-two
clock choice `n² ≤ q = 2^t` with the end-to-end decoder: for any reduced `d/r`
with `r < n` whose readout satisfies (5.12), the source-window decoder with
denominator bound `B = n - 1` recovers `d/r`. -/
theorem source_clock_residue_window_actual_decoder_recovery
    (N t r c d : ℕ) (hN : 0 < N) (hr : 0 < r) (hrN : r ≤ N - 1)
    (hcop : Nat.Coprime d r) (hdr : d < r) (hlo : N ^ 2 ≤ 2 ^ t)
    (h : 2 * |(r : ℤ) * (c : ℤ) - (d : ℤ) * ((2 ^ t : ℕ) : ℤ)| ≤ (r : ℤ)) :
    (sourceRationalDecode (N - 1) (2 ^ t) c).1 = some (d, r) ∧
      (sourceRationalDecode (N - 1) (2 ^ t) c).2 ≤ (N - 1) * ((N - 1) + 1) / 2 := by
  exact residue_window_actual_decoder_recovery (N - 1) (2 ^ t) r c d hr hrN hcop hdr
    (source_clock_halfwindow_guard N t hN hlo) h

end Qatlib.Papers.ShorFactoring97.OrderRecovery
