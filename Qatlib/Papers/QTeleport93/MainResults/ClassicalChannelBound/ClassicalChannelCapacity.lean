/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic

/-!
# Exact transmission through a finite classical channel

`StochasticChannel` models a channel with finite output alphabet, and
`StochasticChannel.ExactThrough` requires a deterministic encoder and decoder to recover every
source symbol with probability one. Exact transmission makes encoded output supports disjoint
and forces the encoder to be injective.

The resulting alphabet and zero error code bounds provide classical counting tools for the
communication argument in [BennettEtAl1993Teleportation]. Specializations to `Fin n × Fin n`
give `n * n` message labels and the corresponding ceiling logarithm bound.

## Main statements

* `StochasticChannel.exact_support_disjoint` separates supports for distinct source symbols.
* `StochasticChannel.exact_message_count` bounds source cardinality by the input alphabet size.
* `StochasticChannel.exact_zero_error_capacity_card` constructs a zero error code of the source
  cardinality.
* `StochasticChannel.exact_capacity_qudit` and `StochasticChannel.qubit_exact_two_bits` give bit
  bounds.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound

open scoped BigOperators

/-- A classical channel with real nonnegative output probabilities summing to one for each input
and a finite output alphabet. -/
structure StochasticChannel (M Y : Type) [Fintype Y] where

  prob : M → Y → ℝ

  prob_nonneg : ∀ m y, 0 ≤ prob m y

  sum_prob : ∀ m, ∑ y, prob m y = 1

namespace StochasticChannel

variable {M Y S : Type} [Fintype Y]

/-- The finite set of outputs with nonzero probability for the channel input `m`. -/
noncomputable def support (ch : StochasticChannel M Y) (m : M) : Finset Y := by
  classical
  exact Finset.univ.filter (fun y => ch.prob m y ≠ 0)

/-- An output belongs to the channel support exactly when its conditional probability is
nonzero. -/
@[simp] theorem mem_support {ch : StochasticChannel M Y} {m : M} {y : Y} :
    y ∈ ch.support m ↔ ch.prob m y ≠ 0 := by
  classical
  simp [support]

/-- An output outside the support of a channel input has probability zero for that input. -/
theorem prob_eq_zero_of_not_mem_support (ch : StochasticChannel M Y) (m : M) {y : Y}
    (hy : y ∉ ch.support m) : ch.prob m y = 0 := by
  by_contra h
  exact hy (mem_support.mpr h)

/-- The output support of every channel input is nonempty because its probabilities sum to one. -/
theorem support_nonempty (ch : StochasticChannel M Y) (m : M) :
    (ch.support m).Nonempty := by
  classical
  rcases (ch.support m).eq_empty_or_nonempty with h | h
  · exfalso
    have hzero : ∀ y, ch.prob m y = 0 :=
      fun y => prob_eq_zero_of_not_mem_support ch m (by rw [h]; simp)
    have hsum : ∑ y, ch.prob m y = 0 := Finset.sum_eq_zero (fun y _ => hzero y)
    rw [ch.sum_prob m] at hsum
    exact zero_ne_one hsum.symm
  · exact h

/-- The condition that encoding by `e`, passing through the channel, and decoding by `D`
recovers each source symbol with probability one. -/
noncomputable def ExactThrough (ch : StochasticChannel M Y) (e : S → M) (D : Y → S) :
    Prop := by
  classical
  exact ∀ s, ∑ y, (if D y = s then ch.prob (e s) y else 0) = 1

/-- Under exact transmission, every output with nonzero probability from an encoded source
symbol decodes to that symbol. -/
theorem exact_support_decodes (ch : StochasticChannel M Y) (e : S → M) (D : Y → S)
    (h : ch.ExactThrough e D) (s : S) {y : Y} (hy : ch.prob (e s) y ≠ 0) :
    D y = s := by
  classical
  by_contra hne
  have hsum :
      ∑ y', (ch.prob (e s) y' - (if D y' = s then ch.prob (e s) y' else 0)) = 0 := by
    rw [Finset.sum_sub_distrib, ch.sum_prob (e s), h s, sub_self]
  have hnonneg : ∀ y' ∈ Finset.univ,
      0 ≤ ch.prob (e s) y' - (if D y' = s then ch.prob (e s) y' else 0) := by
    intro y' _
    split_ifs with hd
    · simp
    · simpa using ch.prob_nonneg (e s) y'
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum y (Finset.mem_univ y)
  rw [if_neg (by simpa using hne), sub_zero] at hzero
  exact hy hzero

/-- Exact transmission makes the output supports of two distinct encoded source symbols
disjoint. -/
theorem exact_support_disjoint (ch : StochasticChannel M Y) (e : S → M) (D : Y → S)
    (h : ch.ExactThrough e D) {s s' : S} (hss' : s ≠ s') :
    Disjoint (ch.support (e s)) (ch.support (e s')) := by
  classical
  rw [Finset.disjoint_left]
  intro y hy hy'
  have hy1 : ch.prob (e s) y ≠ 0 := mem_support.mp hy
  have hy2 : ch.prob (e s') y ≠ 0 := mem_support.mp hy'
  have h1 := exact_support_decodes ch e D h s hy1
  have h2 := exact_support_decodes ch e D h s' hy2
  exact hss' (h1.symm.trans h2)

/-- An encoder with exact decoding through the channel is injective. -/
theorem exact_encoder_injective (ch : StochasticChannel M Y) (e : S → M) (D : Y → S)
    (h : ch.ExactThrough e D) : Function.Injective e := by
  classical
  intro s s' hEq
  by_contra hne
  have hdisj := exact_support_disjoint ch e D h hne
  rw [hEq] at hdisj
  have hempty : ch.support (e s') = ∅ :=
    (Finset.disjoint_self_iff_empty _).mp hdisj
  exact (support_nonempty ch (e s')).ne_empty hempty

/-- Exact transmission through a finite channel requires at least as many input labels as source
symbols, giving the counting bound used in [BennettEtAl1993Teleportation]. -/
theorem exact_message_count (ch : StochasticChannel M Y) (e : S → M) (D : Y → S)
    (h : ch.ExactThrough e D) [Fintype S] [Fintype M] :
    Fintype.card S ≤ Fintype.card M :=
  Fintype.card_le_of_injective e (exact_encoder_injective ch e D h)

/-- A finite set of channel inputs whose distinct elements have disjoint output supports. -/
def ZeroErrorCode (ch : StochasticChannel M Y) (A : Finset M) : Prop :=
  ∀ m ∈ A, ∀ m' ∈ A, m ≠ m' → Disjoint (ch.support m) (ch.support m')

/-- The image of a finite source alphabet under an exactly decodable encoder is a zero error
code. -/
theorem exact_zero_error_code (ch : StochasticChannel M Y) (e : S → M) (D : Y → S)
    (h : ch.ExactThrough e D) [Fintype S] [DecidableEq M] :
    ZeroErrorCode ch (Finset.univ.image e) := by
  classical
  intro m hm m' hm' hne
  rw [Finset.mem_image] at hm hm'
  obtain ⟨s, _, rfl⟩ := hm
  obtain ⟨s', _, rfl⟩ := hm'
  exact exact_support_disjoint ch e D h (fun hss => hne (by rw [hss]))

/-- Exact transmission produces a zero error code with cardinality equal to the source alphabet,
supporting the communication requirement of [BennettEtAl1993Teleportation]. -/
theorem exact_zero_error_capacity_card (ch : StochasticChannel M Y) (e : S → M)
    (D : Y → S) (h : ch.ExactThrough e D) [Fintype S] [DecidableEq M] :
    ∃ A : Finset M, A.card = Fintype.card S ∧ ZeroErrorCode ch A := by
  classical
  refine ⟨Finset.univ.image e, ?_, exact_zero_error_code ch e D h⟩
  rw [Finset.card_image_of_injective _ (exact_encoder_injective ch e D h)]
  simp

/-- If the channel input alphabet has `2 ^ b` elements, exact transmission requires `Nat.clog 2
(Fintype.card S) ≤ b`, as in the counting argument of [BennettEtAl1993Teleportation]. -/
theorem exact_capacity_bits (ch : StochasticChannel M Y) (e : S → M) (D : Y → S)
    (h : ch.ExactThrough e D) [Fintype S] [Fintype M] {b : ℕ}
    (hM : Fintype.card M = 2 ^ b) :
    Nat.clog 2 (Fintype.card S) ≤ b := by
  apply Nat.clog_le_of_le_pow
  rw [← hM]
  exact exact_message_count ch e D h

/-- Exact transmission of labels in `Fin n × Fin n` requires at least `n * n` channel input
symbols. -/
theorem exact_message_count_qudit (ch : StochasticChannel M Y) (n : ℕ)
    (e : Fin n × Fin n → M) (D : Y → Fin n × Fin n) (h : ch.ExactThrough e D)
    [Fintype M] :
    n * n ≤ Fintype.card M := by
  simpa using exact_message_count ch e D h

/-- Exact transmission of qudit outcome pairs through an input alphabet of size `2 ^ b` requires
`Nat.clog 2 (n * n) ≤ b` [BennettEtAl1993Teleportation]. -/
theorem exact_capacity_qudit (ch : StochasticChannel M Y) (n : ℕ)
    (e : Fin n × Fin n → M) (D : Y → Fin n × Fin n) (h : ch.ExactThrough e D)
    [Fintype M] {b : ℕ} (hM : Fintype.card M = 2 ^ b) :
    Nat.clog 2 (n * n) ≤ b := by
  have hc : Fintype.card (Fin n × Fin n) = n * n := by simp
  rw [← hc]
  exact exact_capacity_bits ch e D h hM

/-- Exact transmission of the four labels in `Fin 2 × Fin 2` requires at least four channel
input symbols. -/
theorem qubit_exact_four_messages (ch : StochasticChannel M Y)
    (e : Fin 2 × Fin 2 → M) (D : Y → Fin 2 × Fin 2) (h : ch.ExactThrough e D)
    [Fintype M] :
    4 ≤ Fintype.card M := by
  simpa using exact_message_count_qudit ch 2 e D h

/-- Exact transmission of four qubit outcome labels through an input alphabet of size `2 ^ b`
requires at least two bits [BennettEtAl1993Teleportation]. -/
theorem qubit_exact_two_bits (ch : StochasticChannel M Y)
    (e : Fin 2 × Fin 2 → M) (D : Y → Fin 2 × Fin 2) (h : ch.ExactThrough e D)
    [Fintype M] {b : ℕ} (hM : Fintype.card M = 2 ^ b) :
    2 ≤ b := by
  have h2 := exact_capacity_qudit ch 2 e D h hM
  have hclog : Nat.clog 2 (2 * 2) = 2 := by
    rw [show (2 * 2 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.clog_pow 2 2 (by norm_num)
  rwa [hclog] at h2

/-- No encoder and decoder transmit every source symbol exactly when the channel input alphabet
is smaller than the source alphabet [BennettEtAl1993Teleportation]. -/
theorem not_exact_of_small_alphabet (ch : StochasticChannel M Y) [Fintype S]
    [Fintype M] (hsmall : Fintype.card M < Fintype.card S) :
    ¬ ∃ (e : S → M) (D : Y → S), ch.ExactThrough e D := by
  rintro ⟨e, D, h⟩
  have hle := exact_message_count ch e D h
  omega

end StochasticChannel

end Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
