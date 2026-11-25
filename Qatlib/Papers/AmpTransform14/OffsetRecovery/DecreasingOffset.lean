/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
public import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression

@[expose] public section

/-!
# The decreasing-offset descent of step 2'

Step 2' of [Cornwell2014], Chapter 2, Section 2.12.3, printed pp. 52-53, locates the offset of the
marked progression by moving backwards from a known marked index `x1 = s + r1 * P`. The candidate
offsets `x1 - P, x1 - 2P, ..., x1 - r1 * P = s` strictly decrease, and each is fed to the
three-point membership verifier `Qatlib.Concepts.AmpTransform.SuccessRatio.aqVerify`, which
accepts exactly the true offset and period. Since the descent reaches the true offset, the
procedure always succeeds; it charges at most three membership queries per candidate, hence at
most `(r1 + 1) * (aqRounds N M + 3)` queries when each candidate is paired with one amplified run
of `aqRounds N M` queries. The expected `O(log M)` halving under a uniformly random starting index
is not proved here.

## Main statements

* `aqDescentOffsets_mem_iff`: the candidates emitted by the descent are exactly
  `x1 - (k + 1) * P` for `k < r1`.
* `aqDescentOffsets_value_lt`: the emitted candidate values strictly decrease with `k`.
* `aqDescentOffsets_pairwise`: the descent list is strictly decreasing entry by entry.
* `aqDecreasingOffset_sound`: the scan returns only the true offset with the true period.
* `aqDecreasingOffsetRun_spec`: on the promised input the scan returns the true offset and period
  and costs at most `(r1 + 1) * (aqRounds N M + 3)` oracle and membership calls.

## References

* [Cornwell, 2014][Cornwell2014], Chapter 2, Section 2.12.3, printed pp. 52-53,
  [arXiv:1406.0190](https://arxiv.org/abs/1406.0190)
-/

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.OffsetRecovery

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio

open scoped BigOperators

/-- The candidate offsets emitted by the descent starting at the marked index `x1`: `x1 - P` first
and `x1 - r1 * P` last, so that the last candidate is the true offset when `x1 = s + r1 * P`. -/
def aqDescentOffsets (x1 P : ℕ) : ℕ → List ℕ
  | 0 => []
  | r1 + 1 => aqDescentOffsets x1 P r1 ++ [x1 - (r1 + 1) * P]

/-- The descent emits exactly `r1` candidate offsets. -/
@[simp]
theorem aqDescentOffsets_length (x1 P r1 : ℕ) : (aqDescentOffsets x1 P r1).length = r1 := by
  induction r1 with
  | zero => rfl
  | succ r1 ih => simp [aqDescentOffsets, ih]

/-- The emitted candidates are exactly the values `x1 - (k + 1) * P` with `k < r1`. -/
theorem aqDescentOffsets_mem_iff (x1 P r1 a : ℕ) :
    a ∈ aqDescentOffsets x1 P r1 ↔ ∃ k, k < r1 ∧ a = x1 - (k + 1) * P := by
  induction r1 with
  | zero => simp [aqDescentOffsets]
  | succ r1 ih =>
    rw [aqDescentOffsets, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, rfl⟩
      · exact ⟨r1, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · exact Or.inl ⟨k, hlt, rfl⟩
      · exact Or.inr (by rw [heq])

/-- In the exact regime `k + 1 <= r1`, the candidate `x1 - (k + 1) * P` at `x1 = s + r1 * P` is
`s + (r1 - (k + 1)) * P`; in particular no natural-number truncation occurs. -/
theorem aqDescentOffsets_value (s P r1 k : ℕ) (hk : k + 1 ≤ r1) :
    s + r1 * P - (k + 1) * P = s + (r1 - (k + 1)) * P := by
  have hle : (k + 1) * P ≤ r1 * P := Nat.mul_le_mul_right P hk
  rw [Nat.sub_mul]
  omega

/-- The candidate values strictly decrease with the descent step: for `k < l < r1` the candidate
at `l` is strictly smaller than the candidate at `k`. -/
theorem aqDescentOffsets_value_lt (s P r1 k l : ℕ) (hP : 0 < P) (hkl : k < l) (hl : l < r1) :
    s + r1 * P - (l + 1) * P < s + r1 * P - (k + 1) * P := by
  have hkr : k + 1 ≤ r1 := by omega
  have hlr : l + 1 ≤ r1 := by omega
  rw [aqDescentOffsets_value s P r1 l hlr, aqDescentOffsets_value s P r1 k hkr]
  have hsub : r1 - (l + 1) < r1 - (k + 1) := by omega
  have hmul : (r1 - (l + 1)) * P < (r1 - (k + 1)) * P :=
    Nat.mul_lt_mul_of_pos_right hsub hP
  omega

/-- The true offset is emitted by the descent: starting at `x1 = s + r1 * P` with `r1 > 0`, the
last candidate is `s`. -/
theorem s_mem_aqDescentOffsets (x1 P r1 s : ℕ) (hr : 0 < r1) (hx1 : x1 = s + r1 * P) :
    s ∈ aqDescentOffsets x1 P r1 := by
  rw [aqDescentOffsets_mem_iff]
  refine ⟨r1 - 1, by omega, ?_⟩
  rw [hx1, show r1 - 1 + 1 = r1 from by omega]
  exact (Nat.add_sub_cancel_right s (r1 * P)).symm

/-- Appending a single element below all entries of a decreasing list keeps it decreasing. -/
private theorem pairwise_append_singleton {l : List ℕ} {v : ℕ} {R : ℕ → ℕ → Prop}
    (hl : l.Pairwise R) (hv : ∀ a ∈ l, R a v) : (l ++ [v]).Pairwise R := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hltail⟩ := List.pairwise_cons.mp hl
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with hbl | hbv
      · exact ha b hbl
      · rw [List.mem_singleton] at hbv
        subst hbv
        exact hv a List.mem_cons_self
    · exact ih hltail (fun a' ha' => hv a' (List.mem_cons_of_mem a ha'))

/-- A later candidate of the descent is strictly smaller than an earlier one, as long as the
whole descent stays inside the natural range. -/
private theorem descent_step_lt (x1 P r1 k : ℕ) (hP : 0 < P) (hx : (r1 + 1) * P ≤ x1)
    (hk : k < r1) : x1 - (r1 + 1) * P < x1 - (k + 1) * P := by
  have hsteps : (k + 1) * P < (r1 + 1) * P :=
    Nat.mul_lt_mul_of_pos_right (by omega) hP
  omega

/-- The descent list is strictly decreasing: every entry is larger than every later entry. -/
theorem aqDescentOffsets_pairwise (P : ℕ) (hP : 0 < P) :
    ∀ (r1 x1 : ℕ), r1 * P ≤ x1 → (aqDescentOffsets x1 P r1).Pairwise (fun a b => b < a) := by
  intro r1
  induction r1 with
  | zero => intro x1 _; simp [aqDescentOffsets]
  | succ r1 ih =>
    intro x1 hx
    have htail : r1 * P ≤ x1 :=
      (Nat.mul_le_mul_right P (by omega : r1 ≤ r1 + 1)).trans hx
    refine pairwise_append_singleton (ih x1 htail) ?_
    intro a ha
    rw [aqDescentOffsets_mem_iff] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact descent_step_lt x1 P r1 k hP hx hk

/-- The descent scan: verify the candidate offsets in the given order, returning the first offset
that passes the three-point verifier together with the period, and the accumulated number of
membership queries. -/
def aqDecreasingOffset {N : ℕ} (f : Fin N → Bool) (M P : ℕ) : List ℕ → Option (ℕ × ℕ) × ℕ
  | [] => (none, 0)
  | x :: xs =>
    match (aqVerify f x M P).1 with
    | true => (some (x, P), (aqVerify f x M P).2)
    | false =>
      let a := aqDecreasingOffset f M P xs
      (a.1, a.2 + (aqVerify f x M P).2)

/-- Under the marked-progression promise, the descent scan returns either nothing or the true
offset with the true period. -/
theorem aqDecreasingOffset_sound {N : ℕ} (f : Fin N → Bool) (s M P : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hb : s + (M - 1) * P < N) (hf : AQMarkPromise f s M P)
    (candidates : List ℕ) :
    (aqDecreasingOffset f M P candidates).1 = none ∨
      (aqDecreasingOffset f M P candidates).1 = some (s, P) := by
  induction candidates with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    have hv := aqVerify_sound f s M P x P hM hP hb hf
    cases hx : (aqVerify f x M P).1 with
    | true =>
      have hxs : x = s := (hv.mp hx).1
      refine Or.inr ?_
      have hstep : aqDecreasingOffset f M P (x :: xs) = (some (x, P), (aqVerify f x M P).2) := by
        simp only [aqDecreasingOffset, hx]
      rw [hstep, hxs]
    | false =>
      rcases ih with h | h
      · exact Or.inl (by simp only [aqDecreasingOffset, hx, h])
      · exact Or.inr (by simp only [aqDecreasingOffset, hx, h])

/-- The descent scan finds the true offset and period whenever the true offset is among the
candidates. -/
theorem aqDecreasingOffset_complete {N : ℕ} (f : Fin N → Bool) (s M P : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hb : s + (M - 1) * P < N) (hf : AQMarkPromise f s M P)
    (candidates : List ℕ) (hmem : s ∈ candidates) :
    (aqDecreasingOffset f M P candidates).1 = some (s, P) := by
  induction candidates with
  | nil => simp at hmem
  | cons x xs ih =>
    have hv := aqVerify_sound f s M P x P hM hP hb hf
    cases hx : (aqVerify f x M P).1 with
    | true =>
      have hxs : x = s := (hv.mp hx).1
      have hstep : aqDecreasingOffset f M P (x :: xs) = (some (x, P), (aqVerify f x M P).2) := by
        simp only [aqDecreasingOffset, hx]
      rw [hstep, hxs]
    | false =>
      have hmem' : s ∈ xs := by
        rcases List.mem_cons.mp hmem with he | hh
        · exact absurd (hv.mpr ⟨he.symm, rfl⟩) (by rw [hx]; exact Bool.false_ne_true)
        · exact hh
      simp only [aqDecreasingOffset, hx]
      exact ih hmem'

/-- Each candidate costs at most three membership queries, so the descent scan costs at most
three queries per candidate. -/
theorem aqDecreasingOffset_cost {N : ℕ} (f : Fin N → Bool) (M P : ℕ) (candidates : List ℕ) :
    (aqDecreasingOffset f M P candidates).2 ≤ 3 * candidates.length := by
  induction candidates with
  | nil => simp [aqDecreasingOffset]
  | cons x xs ih =>
    have hc := aqVerify_cost f x M P
    cases hx : (aqVerify f x M P).1 with
    | true =>
      simp only [aqDecreasingOffset, hx, List.length_cons]
      omega
    | false =>
      simp only [aqDecreasingOffset, hx, List.length_cons]
      omega

/-- The descent scan started at the marked index `x1 = s + r1 * P` on the promised progression
returns the true offset and period, and it uses at most `(r1 + 1) * (aqRounds N M + 3)` oracle and
membership calls. -/
theorem aqDecreasingOffsetRun_spec {N : ℕ} (f : Fin N → Bool) (s M P r1 : ℕ) (x1 : Fin N)
    (hM : 2 ≤ M) (hP : 0 < P) (hb : s + (M - 1) * P < N) (hf : AQMarkPromise f s M P)
    (hr : 0 < r1) (hx1 : x1.val = s + r1 * P) :
    (aqDecreasingOffset f M P (aqDescentOffsets x1.val P r1)).1 = some (s, P) ∧
    (aqDecreasingOffset f M P (aqDescentOffsets x1.val P r1)).2 ≤
      (r1 + 1) * (aqRounds N M + 3) := by
  have hmem : s ∈ aqDescentOffsets x1.val P r1 := s_mem_aqDescentOffsets x1.val P r1 s hr hx1
  constructor
  · exact aqDecreasingOffset_complete f s M P hM hP hb hf _ hmem
  · have hcost := aqDecreasingOffset_cost f M P (aqDescentOffsets x1.val P r1)
    rw [aqDescentOffsets_length] at hcost
    have hk : 3 ≤ aqRounds N M + 3 := by omega
    calc (aqDecreasingOffset f M P (aqDescentOffsets x1.val P r1)).2
        ≤ 3 * r1 := hcost
      _ = r1 * 3 := by ring
      _ ≤ (r1 + 1) * (aqRounds N M + 3) := Nat.mul_le_mul (by omega) hk

end Qatlib.Papers.AmpTransform14.OffsetRecovery
