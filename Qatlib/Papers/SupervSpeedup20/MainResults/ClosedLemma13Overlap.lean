/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

@[expose] public section


/-!
# Lemma 13 — the large-margin geometry of the feature/halfspace states

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020), Lemma 13, p. 19–20,
with the feature state `|φ(x)⟩` of Eq. (D9) and the halfspace state
`|φ_s⟩` of Eq. (D10).

The lemma has two layers:

* **Exact geometry.**  For log-offsets in the interior of the concept
  half-interval, the feature interval `[t, t + 2^k)` lies entirely inside the
  halfspace interval `[s, s + (p-1)/2]`; for offsets in the interior of the
  complement, the two intervals are disjoint.  Hence the Hilbert–Schmidt
  inner product of the corresponding rank-one states is `Δ` resp. `0`
  (`lemma13_positive_bulk`, `lemma13_negative_bulk`).  Under the Pauli-basis
  identification — the Pauli coefficient vector inner product equals the
  Hilbert–Schmidt inner product — this gives exactly the paper's
  `⟨w_s, x̂⟩ + b` values with `b = -Δ/2`.

* **Fraction.**  The paper states that the identities hold for a `1 - Δ`
  fraction of the positive (resp. negative) examples.  The positive direction
  is proved by an explicit interval count (`positive_bad_fraction_le`); the
  negative direction is proved with the literal two-boundary estimate
  (`negative_bad_fraction_le_double`), giving a `2Δ` boundary loss. The source
  absorbs this constant factor in `Δ = O(n^{-t})`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset DlogWorld
open scoped BigOperators

variable (W : DlogWorld)

/-! ## Interval containment -/

/-- Bulk positive offsets: the feature interval `[t, t+2^k)` is contained in
the concept interval `[s, s+(N-1)/2]` when `t = s+j` and `2^k ≤ j` with
`j+2^k ≤ N/2`. -/
theorem phi_support_subset_half {s t : ZMod W.N} {k j : ℕ}
    (ht : t = s + (j : ZMod W.N)) (hj0p : 2 ^ k ≤ j) (hjr : j + 2 ^ k ≤ W.N / 2) :
    cyclicInterval W.N t (2 ^ k) ⊆ cyclicInterval W.N s (W.N / 2) := by
  intro u hu
  have _huse := hj0p
  rw [mem_cyclicInterval] at hu ⊢
  obtain ⟨i, hi, rfl⟩ := hu
  refine ⟨j + i, by omega, ?_⟩
  rw [ht, Nat.cast_add]
  ring

/-- Bulk positive intersection has exactly `2^k` elements. -/
theorem inter_card_bulk_pos {s t : ZMod W.N} {k j : ℕ}
    (ht : t = s + (j : ZMod W.N)) (hj0p : 2 ^ k ≤ j) (hjr : j + 2 ^ k ≤ W.N / 2) :
    (cyclicInterval W.N t (2 ^ k) ∩ cyclicInterval W.N s (W.N / 2)).card = 2 ^ k := by
  rw [Finset.inter_eq_left.mpr (phi_support_subset_half W ht hj0p hjr)]
  exact cyclicInterval_card (by omega)

/-- Bulk negative offsets: when `t = s+j` with `N/2 + 2^k ≤ j` and
`j + 2^k ≤ N`, the feature interval and the concept interval are disjoint. -/
theorem phi_support_disjoint_half {s t : ZMod W.N} {k j : ℕ}
    (ht : t = s + (j : ZMod W.N)) (hj1 : W.N / 2 + 2 ^ k ≤ j)
    (hj2 : j + 2 ^ k ≤ W.N) :
    cyclicInterval W.N t (2 ^ k) ∩ cyclicInterval W.N s (W.N / 2) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  rw [Finset.mem_inter, mem_cyclicInterval, mem_cyclicInterval] at hu
  obtain ⟨⟨i, hi, hui⟩, ⟨j', hj', huj⟩⟩ := hu
  have hEq : (s + (j' : ZMod W.N)) = (s + (j : ZMod W.N)) + (i : ZMod W.N) := by
    rw [← huj, hui, ht]
  have hcast : (j' : ZMod W.N) = ((j + i : ℕ) : ZMod W.N) := by
    have h' : s + (j' : ZMod W.N) = s + (((j + i : ℕ)) : ZMod W.N) := by
      simpa [Nat.cast_add, add_assoc] using hEq
    exact add_left_cancel h'
  have hji : j + i < W.N := by omega
  have hj'N : j' < W.N := by omega
  have heq : j' = j + i := by
    have hmod := (ZMod.natCast_eq_natCast_iff' j' (j + i) W.N).mp hcast
    rw [Nat.mod_eq_of_lt hj'N, Nat.mod_eq_of_lt hji] at hmod
    exact hmod
  omega

/-! ## A sum-of-indicators identity -/

/-- The Euclidean inner product is symmetric. -/
theorem euclidInner_comm (u v : ZMod W.N → ℝ) :
    W.euclidInner u v = W.euclidInner v u := by
  simp only [euclidInner]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- The inner product of two constant-on-a-set vectors is the constant product
times the cardinality of the intersection. -/
theorem sum_indicator_mul_indicator {α : Type} [Fintype α] [DecidableEq α]
    (B A : Finset α) (c d : ℝ) :
    (∑ u, (if u ∈ B then c else 0) * (if u ∈ A then d else 0)) =
      c * d * ((B ∩ A).card : ℝ) := by
  have h : ∀ u, (if u ∈ B then c else 0) * (if u ∈ A then d else 0) =
      (if u ∈ B ∩ A then c * d else 0) := by
    intro u
    by_cases hb : u ∈ B <;> by_cases ha : u ∈ A <;>
      simp [hb, ha, Finset.mem_inter]
  calc (∑ u, (if u ∈ B then c else 0) * (if u ∈ A then d else 0))
      = ∑ u, (if u ∈ B ∩ A then c * d else 0) :=
        Finset.sum_congr rfl (fun u _ => h u)
    _ = ∑ u ∈ B ∩ A, c * d := by
        rw [← Finset.sum_filter]
        congr 1
        ext u
        simp
    _ = c * d * ((B ∩ A).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- A pure square-root coefficient identity. -/
theorem sq_sqrt_inv_mul (X Y c : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    ((Real.sqrt X)⁻¹ * (Real.sqrt Y)⁻¹ * c) ^ 2 = c ^ 2 / (X * Y) := by
  have hx : (Real.sqrt X)⁻¹ ^ 2 = X⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hX.le]
  have hy : (Real.sqrt Y)⁻¹ ^ 2 = Y⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hY.le]
  rw [mul_pow, mul_pow, hx, hy, div_eq_mul_inv, mul_inv_rev, mul_comm Y⁻¹ X⁻¹]
  ring

/-! ## Exact bulk values -/

/-- **Lemma 13, positive bulk.**  For `t = s+j` with `2^k ≤ j` and
`j + 2^k ≤ (p-1)/2`, the Pauli-vector inner product of `w_s` and `x̂` equals
`Δ`; with `b = -Δ/2` this is `⟨w_s,x̂⟩ + b = Δ/2` (source Lemma 13, first
bullet). -/
theorem lemma13_positive_bulk {s t : ZMod W.N} {k j : ℕ}
    (ht : t = s + (j : ZMod W.N)) (hj0p : 2 ^ k ≤ j) (hjr : j + 2 ^ k ≤ W.N / 2) :
    W.hsInner (W.rankOne (W.halfVec s)) (W.rankOne (W.phiVec k t)) + (-(W.delta k) / 2)
      = W.delta k / 2 := by
  rw [W.hsInner_rankOne, euclidInner_comm W (W.halfVec s) (W.phiVec k t)]
  have hinner : W.euclidInner (W.phiVec k t) (W.halfVec s) =
      (Real.sqrt (((2 ^ k : ℕ)) : ℝ))⁻¹ *
        (Real.sqrt (((W.N / 2 : ℕ)) : ℝ))⁻¹ * (((2 ^ k : ℕ)) : ℝ) := by
    simp only [euclidInner, phiVec, halfVec]
    rw [sum_indicator_mul_indicator
      (cyclicInterval W.N t (2 ^ k)) (cyclicInterval W.N s (W.N / 2))
      (Real.sqrt (((2 ^ k : ℕ)) : ℝ))⁻¹ (Real.sqrt (((W.N / 2 : ℕ)) : ℝ))⁻¹]
    rw [inter_card_bulk_pos W ht hj0p hjr]
  rw [hinner]
  have h2k : (0 : ℝ) < (((2 ^ k : ℕ)) : ℝ) := by positivity
  have hY : (0 : ℝ) < (((W.N / 2 : ℕ)) : ℝ) := by
    exact_mod_cast W.N_div_two_pos
  rw [sq_sqrt_inv_mul _ _ _ h2k hY]
  unfold delta
  have h2kne : (((2 ^ k : ℕ)) : ℝ) ≠ 0 := ne_of_gt h2k
  field_simp
  ring

/-- **Lemma 13, negative bulk.**  For `t = s+j` with `N/2 + 2^k ≤ j` and
`j + 2^k ≤ N`, the Pauli-vector inner product is `0`; with `b = -Δ/2` this is
`⟨w_s,x̂⟩ + b = -Δ/2` (source Lemma 13, second bullet). -/
theorem lemma13_negative_bulk {s t : ZMod W.N} {k j : ℕ}
    (ht : t = s + (j : ZMod W.N)) (hj1 : W.N / 2 + 2 ^ k ≤ j)
    (hj2 : j + 2 ^ k ≤ W.N) :
    W.hsInner (W.rankOne (W.halfVec s)) (W.rankOne (W.phiVec k t)) + (-(W.delta k) / 2)
      = -(W.delta k) / 2 := by
  rw [W.hsInner_rankOne, euclidInner_comm W (W.halfVec s) (W.phiVec k t)]
  have hinner : W.euclidInner (W.phiVec k t) (W.halfVec s) = 0 := by
    simp only [euclidInner, phiVec, halfVec]
    rw [sum_indicator_mul_indicator
      (cyclicInterval W.N t (2 ^ k)) (cyclicInterval W.N s (W.N / 2))
      (Real.sqrt (((2 ^ k : ℕ)) : ℝ))⁻¹ (Real.sqrt (((W.N / 2 : ℕ)) : ℝ))⁻¹]
    rw [phi_support_disjoint_half W ht hj1 hj2]
    simp
  rw [hinner]
  ring

/-! ## The `1 - Δ` counting statement -/

/-- Positive log-offsets whose feature interval is strictly inside the
concept interval (the paper's `1 - Δ` bulk). -/
def goodOffsetsPos (k : ℕ) : Finset ℕ :=
  (Finset.range (W.N / 2)).filter (fun j => j + 2 ^ k ≤ W.N / 2)

/-- The positive bad offsets are contained in the last `2^k` offsets. -/
theorem badOffsetsPos_card_le (k : ℕ) (h2k : 2 ^ k ≤ W.N / 2) :
    ((Finset.range (W.N / 2)).filter (fun j => ¬ j + 2 ^ k ≤ W.N / 2)).card ≤ 2 ^ k := by
  have hsub : (Finset.range (W.N / 2)).filter (fun j => ¬ j + 2 ^ k ≤ W.N / 2)
      ⊆ Finset.Ico (W.N / 2 - 2 ^ k) (W.N / 2) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_Ico]
    omega
  calc
    ((Finset.range (W.N / 2)).filter (fun j => ¬ j + 2 ^ k ≤ W.N / 2)).card
        ≤ (Finset.Ico (W.N / 2 - 2 ^ k) (W.N / 2)).card := Finset.card_le_card hsub
    _ = 2 ^ k := by rw [Nat.card_Ico]; exact Nat.sub_sub_self h2k

/-- **Lemma 13, positive fraction.**  At most a `Δ` fraction of the positive
examples fall outside the bulk, where `Δ = 2^k/((p-1)/2)`. -/
theorem positive_bad_fraction_le (k : ℕ) (h2k : 2 ^ k ≤ W.N / 2) :
    (((Finset.range (W.N / 2)).filter (fun j => ¬ j + 2 ^ k ≤ W.N / 2)).card : ℝ) /
        (((W.N / 2 : ℕ)) : ℝ) ≤ W.delta k := by
  have hY : (0 : ℝ) < (((W.N / 2 : ℕ)) : ℝ) := by
    exact_mod_cast W.N_div_two_pos
  have hb : (((Finset.range (W.N / 2)).filter
      (fun j => ¬ j + 2 ^ k ≤ W.N / 2)).card : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast badOffsetsPos_card_le W k h2k
  rw [div_le_iff₀ hY]
  have hd : W.delta k * (((W.N / 2 : ℕ)) : ℝ) = (((2 ^ k : ℕ)) : ℝ) := by
    unfold delta
    exact div_mul_cancel₀ _ (ne_of_gt hY)
  rw [hd]
  exact hb

/-- Negative log-offsets whose feature interval is disjoint from the concept
interval.  The two boundary strips have total width `2·2^k`. -/
def goodOffsetsNeg (k : ℕ) : Finset ℕ :=
  (Finset.Ico (W.N / 2) W.N).filter
    (fun j => W.N / 2 + 2 ^ k ≤ j ∧ j + 2 ^ k ≤ W.N)

/-- The negative bad offsets lie in the two boundary strips. -/
theorem badOffsetsNeg_card_le (k : ℕ) (h2k : 2 ^ k ≤ W.N / 2) :
    ((Finset.Ico (W.N / 2) W.N).filter
        (fun j => ¬ (W.N / 2 + 2 ^ k ≤ j ∧ j + 2 ^ k ≤ W.N))).card ≤ 2 * 2 ^ k := by
  have hsub : (Finset.Ico (W.N / 2) W.N).filter
      (fun j => ¬ (W.N / 2 + 2 ^ k ≤ j ∧ j + 2 ^ k ≤ W.N))
      ⊆ Finset.Ico (W.N / 2) (W.N / 2 + 2 ^ k) ∪
        Finset.Ico (W.N - 2 ^ k) W.N := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hlo, hhi⟩, hbad⟩ := hj
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
    by_cases hleft : W.N / 2 + 2 ^ k ≤ j
    · right
      constructor
      · omega
      · exact hhi
    · left
      constructor
      · exact hlo
      · omega
  have hcard := Finset.card_union_le (Finset.Ico (W.N / 2) (W.N / 2 + 2 ^ k))
    (Finset.Ico (W.N - 2 ^ k) W.N)
  rw [Nat.card_Ico, Nat.card_Ico] at hcard
  have h1 : W.N / 2 + 2 ^ k - W.N / 2 = 2 ^ k := Nat.add_sub_cancel_left _ _
  have h2 : W.N - (W.N - 2 ^ k) = 2 ^ k :=
    Nat.sub_sub_self (le_trans h2k (Nat.div_le_self _ _))
  rw [h1, h2] at hcard
  calc
    ((Finset.Ico (W.N / 2) W.N).filter
        (fun j => ¬ (W.N / 2 + 2 ^ k ≤ j ∧ j + 2 ^ k ≤ W.N))).card
        ≤ (Finset.Ico (W.N / 2) (W.N / 2 + 2 ^ k) ∪
            Finset.Ico (W.N - 2 ^ k) W.N).card := Finset.card_le_card hsub
    _ ≤ 2 ^ k + 2 ^ k := hcard
    _ = 2 * 2 ^ k := by ring

/-- **Lemma 13, negative fraction (literal two-boundary count).**  At most a
`2Δ` fraction of the negative examples fall outside the bulk.  The source
states `1-Δ`; the factor two is the two boundary strips of the cyclic
interval, absorbed by the source's `Δ = O(n^{-t})` accounting. -/
theorem negative_bad_fraction_le_double (k : ℕ) (h2k : 2 ^ k ≤ W.N / 2) :
    (((Finset.Ico (W.N / 2) W.N).filter
        (fun j => ¬ (W.N / 2 + 2 ^ k ≤ j ∧ j + 2 ^ k ≤ W.N))).card : ℝ) /
        (((W.N / 2 : ℕ)) : ℝ) ≤ 2 * W.delta k := by
  have hY : (0 : ℝ) < (((W.N / 2 : ℕ)) : ℝ) := by
    exact_mod_cast W.N_div_two_pos
  have hb : (((Finset.Ico (W.N / 2) W.N).filter
      (fun j => ¬ (W.N / 2 + 2 ^ k ≤ j ∧ j + 2 ^ k ≤ W.N))).card : ℝ) ≤
      ((2 * 2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast badOffsetsNeg_card_le W k h2k
  rw [div_le_iff₀ hY]
  have hd : 2 * W.delta k * (((W.N / 2 : ℕ)) : ℝ) = ((2 * 2 ^ k : ℕ) : ℝ) := by
    have hYne : (((W.N / 2 : ℕ)) : ℝ) ≠ 0 := ne_of_gt hY
    unfold delta
    rw [Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [hd]
  exact hb

end Qatlib.Papers.SupervSpeedup20.MainResults
