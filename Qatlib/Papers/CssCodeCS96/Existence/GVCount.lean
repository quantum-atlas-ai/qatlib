/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The finite Gilbert--Varshamov count

The existence lemma of the fixed source counts incidences between nonzero low-weight binary
vectors and a finite family of codes of a fixed dimension. If every vector of a given family
appears in the same number `W` of codes, and the total number of incidences is smaller than the
family size, then one member of the family has no nonzero word below the target distance. The
argument is a finite double count; no limit or asymptotic rate statement is involved.

## Main statements

* `card_low_weight_le`: the number of binary vectors of weight below `d` is at most the binomial
  prefix `∑ j < d, choose n j`, because a vector is determined by its support.
* `gv_finite_count`: the finite double-counting existence statement.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996]
-/

namespace Qatlib.Papers.CssCodeCS96.Existence

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix
open scoped Classical

variable {n : ℕ}

/-- Over the binary field every element is zero or one. -/
theorem binary_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- The support of a binary vector: the set of coordinates where it does not vanish. -/
def support (v : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => v i ≠ 0

/-- The support has the cardinality of the Hamming weight. -/
theorem card_support (v : Fin n → ZMod 2) : (support v).card = bitWeight v := rfl

/-- A binary vector is determined by its support, since every nonzero coordinate carries the value
one. -/
theorem eq_of_support_eq {v w : Fin n → ZMod 2} (h : support v = support w) : v = w := by
  classical
  funext i
  by_cases hi : v i = 0
  · have hout : i ∉ support v := by simp [support, hi]
    have hout' : i ∉ support w := by rw [← h]; exact hout
    have hw : w i = 0 := by simpa [support] using hout'
    rw [hi, hw]
  · have hin : i ∈ support v := by simp [support, hi]
    have hin' : i ∈ support w := by rw [← h]; exact hin
    have hw : w i ≠ 0 := by simpa [support] using hin'
    have hv1 : v i = 1 := (binary_eq_zero_or_one (v i)).resolve_left hi
    have hw1 : w i = 1 := (binary_eq_zero_or_one (w i)).resolve_left hw
    rw [hv1, hw1]

/-- The number of binary vectors of weight below `d` is at most the binomial prefix
`∑ j < d, choose n j`. Every such vector is determined by its support, and the supports of weight
below `d` are counted by the binomial coefficients. -/
theorem card_low_weight_le (n d : ℕ) :
    (Finset.univ.filter (fun v : Fin n → ZMod 2 => bitWeight v < d)).card ≤
      ∑ j ∈ Finset.range d, Nat.choose n j := by
  classical
  have hT : (Finset.univ.filter (fun s : Finset (Fin n) => s.card < d)) =
      (Finset.range d).biUnion (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · intro hs
      exact ⟨s.card, hs, Finset.subset_univ s, rfl⟩
    · rintro ⟨j, hj, -, hcard⟩
      omega
  have hdisj : (Finset.range d : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro s hsi hsj
    rw [Finset.mem_powersetCard] at hsi hsj
    exact hij (hsi.2.symm.trans hsj.2)
  have hsub : (Finset.univ.filter (fun v : Fin n → ZMod 2 => bitWeight v < d)).image support ⊆
      Finset.univ.filter (fun s : Finset (Fin n) => s.card < d) := by
    intro s hs
    rw [Finset.mem_image] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rwa [card_support]
  have hinj : ∀ v ∈ Finset.univ.filter (fun v : Fin n → ZMod 2 => bitWeight v < d),
      ∀ w ∈ Finset.univ.filter (fun v : Fin n → ZMod 2 => bitWeight v < d),
      support v = support w → v = w := by
    intro v _ w _ h
    exact eq_of_support_eq h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  refine hcard.trans_eq ?_
  rw [hT, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The finite double-counting form of the Gilbert--Varshamov existence argument. For a finite
family `Φ` of binary codes of common dimension `k`, if every nonzero vector is a word of exactly
`W` members of the family and `W` times the number of vectors of weight below `d` is smaller than
the family size, then some member has all nonzero words of weight at least `d`.

The hypothesis `_hdim` of equal dimension records the fixed-dimension setting of the source; the
counting argument itself only uses the incidence bounds. -/
theorem gv_finite_count {n k d : ℕ}
    (Φ : Finset (Submodule (ZMod 2) (Fin n → ZMod 2))) (W : ℕ)
    (_hdim : ∀ c ∈ Φ, Module.finrank (ZMod 2) c = k)
    (huni : ∀ v, v ≠ 0 → (Φ.filter fun c => v ∈ c).card = W)
    (hcount : W * (∑ j ∈ Finset.range d, Nat.choose n j) < Φ.card) :
    ∃ c ∈ Φ, ∀ v ∈ c, v ≠ 0 → d ≤ bitWeight v := by
  classical
  by_contra h
  push Not at h
  set B : Finset (Fin n → ZMod 2) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ bitWeight v < d) with hBdef
  have hlow : Φ.card ≤ ∑ c ∈ Φ, (B.filter (fun v => v ∈ c)).card := by
    calc Φ.card = ∑ c ∈ Φ, 1 := by simp
      _ ≤ ∑ c ∈ Φ, (B.filter (fun v => v ∈ c)).card := by
        refine Finset.sum_le_sum fun c hc => ?_
        obtain ⟨v, hvc, hvne, hvd⟩ := h c hc
        refine Finset.card_pos.mpr ⟨v, ?_⟩
        rw [Finset.mem_filter]
        exact ⟨by
          rw [hBdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvne, by omega⟩, hvc⟩
  have hup : (∑ v ∈ B, (Φ.filter (fun c => v ∈ c)).card) = B.card * W := by
    rw [show (∑ v ∈ B, (Φ.filter (fun c => v ∈ c)).card) = ∑ v ∈ B, W from by
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [hBdef] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [huni v hv.1]]
    rw [Finset.sum_const, Nat.nsmul_eq_mul]
  have hswap : (∑ v ∈ B, (Φ.filter (fun c => v ∈ c)).card)
      = ∑ c ∈ Φ, (B.filter (fun v => v ∈ c)).card := by
    have hin : (∑ v ∈ B, (Φ.filter (fun c => v ∈ c)).card)
        = ∑ v ∈ B, ∑ c ∈ Φ, (if v ∈ c then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.card_filter]
    rw [hin, Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => by rw [Finset.card_filter]
  have hBc : B.card ≤ ∑ j ∈ Finset.range d, Nat.choose n j := by
    have hsub : B ⊆ Finset.univ.filter (fun v : Fin n → ZMod 2 => bitWeight v < d) := by
      intro v hv
      rw [hBdef] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.2
    exact (Finset.card_le_card hsub).trans (card_low_weight_le n d)
  have hle : Φ.card ≤ W * (∑ j ∈ Finset.range d, Nat.choose n j) := by
    calc Φ.card ≤ ∑ c ∈ Φ, (B.filter (fun v => v ∈ c)).card := hlow
      _ = ∑ v ∈ B, (Φ.filter (fun c => v ∈ c)).card := hswap.symm
      _ = B.card * W := hup
      _ ≤ (∑ j ∈ Finset.range d, Nat.choose n j) * W := Nat.mul_le_mul_right W hBc
      _ = W * (∑ j ∈ Finset.range d, Nat.choose n j) := by ring
  omega

end Qatlib.Papers.CssCodeCS96.Existence
