/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.Spectral.JohnsonGap
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Johnson spectrum and norm contraction

This module analyzes the finite Johnson adjacency operator through containment indicators and
products of shifted operators. It places every eigenvalue among the values `johnsonTheta n k j`,
identifies the top eigenspace as constant functions, and derives the normalized contraction
estimate needed in [Tani2009].

## Main statements

* `johnsonAnn_ind`: annihilation of containment indicators by shifted operators.
* `johnsonEigenvalue_mem`: classification of eigenvalues of `johnsonAct`.
* `johnsonNorm_contract'` and `johnsonChain_spectralGap`: squared-norm contraction and a gap
  lower bound of `1/k` under the stated size assumptions.

## References

* [Tani, 2009][Tani2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.Spectral

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower (IsTransitionMatrix)
open scoped BigOperators

/-- Replaces a specified element of a Johnson vertex by an element outside it, preserving its
cardinality. -/
def johnsonSwap {n k : ℕ} (S : JohnsonVertex n k) (i j : Fin n)
    (hi : i ∈ S.1) (hj : j ∉ S.1) : JohnsonVertex n k :=
  ⟨insert j (S.1.erase i), by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_erase_of_mem hi]
      have hk : 0 < k := by
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      have hS : S.1.card = k := S.2
      omega
    · rw [Finset.mem_erase]; exact fun h => hj h.2⟩

/-- The unnormalized Johnson adjacency operator, summing over all single-element replacements of
a vertex. -/
def johnsonAct {n k : ℕ} (g : JohnsonVertex n k → ℝ) : JohnsonVertex n k → ℝ :=
  fun S => ∑ i ∈ S.1.attach, ∑ j ∈ (Finset.univ \ S.1).attach,
    g (johnsonSwap S i.1 j.1 i.2 (Finset.mem_sdiff.mp j.2).2)

/-- The real indicator of the Johnson vertices containing a specified finite set. -/
def johnsonInd {n k : ℕ} (T : Finset (Fin n)) : JohnsonVertex n k → ℝ :=
  fun S => if T ⊆ S.1 then 1 else 0

/-- An element belongs to a swapped vertex exactly when it is the inserted element or an
original element distinct from the removed one. -/
theorem mem_swap_iff {n k : ℕ} (S : JohnsonVertex n k) {i j x : Fin n}
    (hi : i ∈ S.1) (hj : j ∉ S.1) :
    x ∈ (johnsonSwap S i j hi hj).1 ↔ x = j ∨ (x ∈ S.1 ∧ x ≠ i) := by
  unfold johnsonSwap
  simp only [Finset.mem_insert, Finset.mem_erase]
  tauto

/-- A finite set is contained in a swapped vertex exactly when it excludes the removed element
and its elements outside the original vertex lie in the inserted singleton. -/
theorem subset_swap_iff {n k : ℕ} (T : Finset (Fin n)) (S : JohnsonVertex n k) {i j : Fin n}
    (hi : i ∈ S.1) (hj : j ∉ S.1) :
    T ⊆ (johnsonSwap S i j hi hj).1 ↔ i ∉ T ∧ T \ S.1 ⊆ {j} := by
  constructor
  · intro h
    constructor
    · intro hiT
      have h1 := h hiT
      rw [mem_swap_iff S hi hj] at h1
      rcases h1 with h1 | ⟨_, h1'⟩
      · exact hj (h1 ▸ hi)
      · exact h1' rfl
    · intro x hx
      rw [Finset.mem_singleton]
      obtain ⟨hxT, hxS⟩ := Finset.mem_sdiff.mp hx
      have h1 := h hxT
      rw [mem_swap_iff S hi hj] at h1
      rcases h1 with h1 | ⟨h1, _⟩
      · exact h1
      · exact absurd h1 hxS
  · intro ⟨hiT, hTS⟩ x hxT
    rw [mem_swap_iff S hi hj]
    by_cases hxj : x = j
    · exact Or.inl hxj
    · refine Or.inr ⟨?_, fun hxi => hiT (hxi ▸ hxT)⟩
      by_contra hxS
      have hmem : x ∈ T \ S.1 := Finset.mem_sdiff.mpr ⟨hxT, hxS⟩
      have h3 := hTS hmem
      rw [Finset.mem_singleton] at h3
      exact hxj h3

/-- Counts, as a real number, the elements outside a vertex whose singleton contains the part of
`T` outside that vertex. -/
def johnsonInner {n k : ℕ} (T : Finset (Fin n)) (S : JohnsonVertex n k) : ℝ :=
  ∑ j ∈ (Finset.univ \ S.1), if T \ S.1 ⊆ {j} then (1 : ℝ) else 0

/-- For `k ≤ n`, evaluates `johnsonInner T S` as `n-k`, one, or zero according as `T` has zero,
one, or more elements outside `S`. -/
theorem johnsonInner_eq {n k : ℕ} {T : Finset (Fin n)} {S : JohnsonVertex n k}
    (hk : k ≤ n) :
    johnsonInner T S
      = if T \ S.1 = ∅ then ((n - k : ℕ) : ℝ)
        else if (T \ S.1).card = 1 then 1 else 0 := by
  unfold johnsonInner
  set U := T \ S.1 with hU
  by_cases h0 : U = ∅
  · rw [if_pos h0]
    have hsub : ∀ j ∈ (Finset.univ \ S.1), (U ⊆ {j}) := by
      intro j _; rw [h0]; exact Finset.empty_subset _
    have hcongr : (∑ j ∈ (Finset.univ \ S.1), (if U ⊆ {j} then (1 : ℝ) else 0))
        = ∑ _j ∈ (Finset.univ \ S.1), (1 : ℝ) :=
      Finset.sum_congr rfl fun j hj => by rw [if_pos (hsub j hj)]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ \ S.1).card : ℝ) = ((n - k : ℕ) : ℝ) := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, S.2]
    rw [hcard, mul_one]
  · by_cases h1 : U.card = 1
    · rw [if_neg h0, if_pos h1]
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
      have hbS : b ∉ S.1 := by
        have : b ∈ U := by rw [hb]; exact Finset.mem_singleton_self b
        exact (Finset.mem_sdiff.mp this).2
      have hiff : ∀ j ∈ (Finset.univ \ S.1), (U ⊆ {j} ↔ j = b) := by
        intro j _
        rw [hb]
        simp [eq_comm]
      have hcongr : (∑ j ∈ (Finset.univ \ S.1), (if U ⊆ {j} then (1 : ℝ) else 0))
          = ∑ j ∈ (Finset.univ \ S.1), (if j = b then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun j hj => by
          by_cases hjb : U ⊆ {j}
          · rw [if_pos hjb, if_pos ((hiff j hj).mp hjb)]
          · have : ¬ (j = b) := fun h => hjb ((hiff j hj).mpr h)
            rw [if_neg hjb, if_neg this]
      rw [hcongr, Finset.sum_ite_eq']
      simp [hbS]
    · rw [if_neg h0, if_neg h1]
      have h2 : 2 ≤ U.card := by
        have hpos : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        omega
      have hsub : ∀ j ∈ (Finset.univ \ S.1), ¬ (U ⊆ {j}) := by
        intro j _ hsub
        have hle : U.card ≤ ({j} : Finset (Fin n)).card := Finset.card_le_card hsub
        simp at hle
        omega
      have hcongr : (∑ j ∈ (Finset.univ \ S.1), (if U ⊆ {j} then (1 : ℝ) else 0))
          = ∑ _j ∈ (Finset.univ \ S.1), (0 : ℝ) :=
        Finset.sum_congr rfl fun j hj => by rw [if_neg (hsub j hj)]
      rw [hcongr, Finset.sum_const_zero]

/-- Expresses the Johnson adjacency action on a containment indicator using `johnsonInner` and
the size of the intersection. -/
theorem johnsonAct_ind {n k : ℕ} (T : Finset (Fin n)) (S : JohnsonVertex n k) :
    johnsonAct (johnsonInd T) S
      = ((k : ℝ) - ((S.1 ∩ T).card : ℝ)) * johnsonInner T S := by
  unfold johnsonAct
  have hinner : ∀ i ∈ S.1.attach,
      (∑ j ∈ (Finset.univ \ S.1).attach,
        johnsonInd T (johnsonSwap S i.1 j.1 i.2 (Finset.mem_sdiff.mp j.2).2))
        = if i.1 ∈ T then 0 else johnsonInner T S := by
    intro i _
    simp only [johnsonInd]
    by_cases hiT : i.1 ∈ T
    · rw [if_pos hiT]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro hsub
      exact ((subset_swap_iff T S i.2 (Finset.mem_sdiff.mp j.2).2).mp hsub).1 hiT
    · rw [if_neg hiT]
      have hcongr : (∑ j ∈ (Finset.univ \ S.1).attach,
          if T ⊆ (johnsonSwap S i.1 j.1 i.2 (Finset.mem_sdiff.mp j.2).2).1 then (1 : ℝ) else 0)
          = ∑ j ∈ (Finset.univ \ S.1).attach,
            (if T \ S.1 ⊆ {j.1} then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : T ⊆ (johnsonSwap S i.1 j.1 i.2 (Finset.mem_sdiff.mp j.2).2).1
        · rw [if_pos h, if_pos ((subset_swap_iff T S i.2 (Finset.mem_sdiff.mp j.2).2).mp h).2]
        · rw [if_neg h,
            if_neg (fun hc => h ((subset_swap_iff T S i.2 (Finset.mem_sdiff.mp j.2).2).mpr ⟨hiT, hc⟩))]
      rw [hcongr]
      have hattach := Finset.sum_attach (s := Finset.univ \ S.1)
        (f := fun x : Fin n => if T \ S.1 ⊆ ({x} : Finset (Fin n)) then (1 : ℝ) else 0)
      rw [hattach]
      rfl
  rw [Finset.sum_congr rfl hinner]
  have hattach2 := Finset.sum_attach (s := S.1)
    (f := fun x : Fin n => if x ∈ T then (0 : ℝ) else johnsonInner T S)
  rw [hattach2, Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((S.1.filter (fun i => ¬ i ∈ T)).card : ℝ) = (k : ℝ) - ((S.1 ∩ T).card : ℝ) := by
    have : S.1.filter (fun i => ¬ i ∈ T) = S.1 \ T := by
      ext x; simp
    rw [this, Finset.card_sdiff, Finset.inter_comm, S.2]
    rw [Nat.cast_sub (show (S.1 ∩ T).card ≤ k by
      calc (S.1 ∩ T).card ≤ S.1.card := Finset.card_le_card Finset.inter_subset_left
        _ = k := S.2)]
  rw [hcard]

/-- The unnormalized Johnson eigenvalue expression `(k-m)*(n-k-m)-m` for natural parameters. -/
def johnsonTheta (n k m : ℕ) : ℝ := ((k : ℝ) - m) * ((n : ℝ) - k - m) - m

/-- The Johnson adjacency operator shifted by the scalar `c` times the identity. -/
def johnsonOp {n k : ℕ} (c : ℝ) (g : JohnsonVertex n k → ℝ) : JohnsonVertex n k → ℝ :=
  fun S => johnsonAct g S - c * g S

/-- For `u ∈ T`, the set `T.erase u` is contained in `S` exactly when every element of `T`
outside `S` equals `u`. -/
theorem erase_subset_iff {n : ℕ} {T S : Finset (Fin n)} {u : Fin n} (hu : u ∈ T) :
    T.erase u ⊆ S ↔ T \ S ⊆ {u} := by
  constructor
  · intro h x hx
    obtain ⟨hxT, hxS⟩ := Finset.mem_sdiff.mp hx
    rw [Finset.mem_singleton]
    by_contra hxu
    exact hxS (h (Finset.mem_erase.mpr ⟨hxu, hxT⟩))
  · intro h x hx
    obtain ⟨hxu, hxT⟩ := Finset.mem_erase.mp hx
    by_contra hxS
    have hmem : x ∈ T \ S := Finset.mem_sdiff.mpr ⟨hxT, hxS⟩
    have hx1 : x ∈ ({u} : Finset (Fin n)) := h hmem
    rw [Finset.mem_singleton] at hx1
    exact hxu hx1

/-- Evaluates the containment indicator of `T.erase u` using whether `T` outside the vertex is
contained in `{u}`. -/
theorem johnsonInd_erase {n k : ℕ} (T : Finset (Fin n)) (S : JohnsonVertex n k)
    {u : Fin n} (hu : u ∈ T) :
    johnsonInd (T.erase u) S = if T \ S.1 ⊆ {u} then (1 : ℝ) else 0 := by
  unfold johnsonInd
  by_cases h : T.erase u ⊆ S.1
  · rw [if_pos h, if_pos ((erase_subset_iff hu).mp h)]
  · rw [if_neg h, if_neg (fun hc => h ((erase_subset_iff hu).mpr hc))]

/-- Counts the single-element erasures of `T` contained in a vertex, according to the
cardinality of `T` outside that vertex. -/
theorem sum_ind_erase {n k : ℕ} (T : Finset (Fin n)) (S : JohnsonVertex n k) :
    (∑ u ∈ T, johnsonInd (T.erase u) S)
      = if T \ S.1 = ∅ then ((T.card : ℕ) : ℝ)
        else if (T \ S.1).card = 1 then 1 else 0 := by
  have hcongr : (∑ u ∈ T, johnsonInd (T.erase u) S)
      = ∑ u ∈ T, (if T \ S.1 ⊆ {u} then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [johnsonInd_erase T S hu]
  rw [hcongr]
  by_cases h0 : T \ S.1 = ∅
  · rw [if_pos h0]
    have hsub : ∀ u ∈ T, (T \ S.1 ⊆ {u}) := by
      intro u _; rw [h0]; exact Finset.empty_subset _
    have hcongr2 : (∑ u ∈ T, (if T \ S.1 ⊆ {u} then (1 : ℝ) else 0))
        = ∑ _u ∈ T, (1 : ℝ) :=
      Finset.sum_congr rfl fun u hu => by rw [if_pos (hsub u hu)]
    rw [hcongr2, Finset.sum_const, nsmul_eq_mul, mul_one]
  · by_cases h1 : (T \ S.1).card = 1
    · rw [if_neg h0, if_pos h1]
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h1
      have hbT : b ∈ T := (Finset.mem_sdiff.mp (by rw [hb]; exact Finset.mem_singleton_self b)).1
      have hiff : ∀ u ∈ T, (T \ S.1 ⊆ {u} ↔ u = b) := by
        intro u _
        rw [hb]
        simp [eq_comm]
      have hcongr2 : (∑ u ∈ T, (if T \ S.1 ⊆ {u} then (1 : ℝ) else 0))
          = ∑ u ∈ T, (if u = b then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun u hu => by
          by_cases h : T \ S.1 ⊆ {u}
          · rw [if_pos h, if_pos ((hiff u hu).mp h)]
          · rw [if_neg h, if_neg (fun hb' => h ((hiff u hu).mpr hb'))]
      rw [hcongr2, Finset.sum_ite_eq', if_pos hbT]
    · rw [if_neg h0, if_neg h1]
      have h2 : 2 ≤ (T \ S.1).card := by
        have hpos : 0 < (T \ S.1).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
        omega
      have hsub : ∀ u ∈ T, ¬ (T \ S.1 ⊆ {u}) := by
        intro u _ hsub
        have hle : (T \ S.1).card ≤ ({u} : Finset (Fin n)).card := Finset.card_le_card hsub
        simp at hle
        omega
      have hcongr2 : (∑ u ∈ T, (if T \ S.1 ⊆ {u} then (1 : ℝ) else 0))
          = ∑ _u ∈ T, (0 : ℝ) :=
        Finset.sum_congr rfl fun u hu => by rw [if_neg (hsub u hu)]
      rw [hcongr2, Finset.sum_const_zero]

/-- For `T.card ≤ k ≤ n`, the Johnson operator shifted by `johnsonTheta n k T.card` sends the
containment indicator of `T` to `(k-T.card+1)` times the sum of its erasure indicators. -/
theorem johnsonOp_ind {n k : ℕ} (T : Finset (Fin n)) (S : JohnsonVertex n k)
    (hk : k ≤ n) (hT : T.card ≤ k) :
    johnsonOp (johnsonTheta n k T.card) (johnsonInd T) S
      = ((k : ℝ) - T.card + 1) * ∑ u ∈ T, johnsonInd (T.erase u) S := by
  unfold johnsonOp
  rw [johnsonAct_ind, sum_ind_erase T S]
  have hn : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by rw [Nat.cast_sub hk]
  have hUle : (T \ S.1).card ≤ T.card := Finset.card_le_card Finset.sdiff_subset
  by_cases h0 : T \ S.1 = ∅
  · have hsub : T ⊆ S.1 := Finset.sdiff_eq_empty_iff_subset.mp h0
    have hinter : (S.1 ∩ T).card = T.card := by
      rw [Finset.inter_eq_right.mpr hsub]
    have hin : johnsonInner T S = ((n - k : ℕ) : ℝ) := by
      rw [johnsonInner_eq hk, if_pos h0]
    have hind : johnsonInd T S = 1 := by
      unfold johnsonInd; rw [if_pos hsub]
    rw [if_pos h0, hin, hind, hinter, hn]
    simp only [johnsonTheta]
    ring
  · have hne : T \ S.1 ≠ ∅ := h0
    have hnonempty : (T \ S.1).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hind : johnsonInd T S = 0 := by
      unfold johnsonInd
      rw [if_neg (fun hsub => hne (Finset.sdiff_eq_empty_iff_subset.mpr hsub))]
    by_cases h1 : (T \ S.1).card = 1
    · have hcardS : (S.1 ∩ T).card = T.card - 1 := by
        have h := Finset.card_sdiff (s := S.1) (t := T)
        rw [h1] at h
        have hle : (S.1 ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
        omega
      have hm1 : 1 ≤ T.card := by
        have := Finset.card_pos.mpr hnonempty
        omega
      have hin : johnsonInner T S = 1 := by
        rw [johnsonInner_eq hk, if_neg hne, if_pos h1]
      rw [if_neg hne, if_pos h1, hin, hind, hcardS, Nat.cast_sub hm1]
      simp only [johnsonTheta]
      ring
    · have h2 : 2 ≤ (T \ S.1).card := by
        have := Finset.card_pos.mpr hnonempty
        omega
      have hin : johnsonInner T S = 0 := by
        rw [johnsonInner_eq hk, if_neg hne, if_neg h1]
      rw [if_neg hne, if_neg h1, hin, hind]
      ring

/-- The Johnson adjacency operator preserves pointwise addition. -/
theorem johnsonAct_add {n k : ℕ} (g h : JohnsonVertex n k → ℝ) :
    johnsonAct (fun S => g S + h S) = fun S => johnsonAct g S + johnsonAct h S := by
  funext S
  unfold johnsonAct
  simp only [Finset.sum_add_distrib]

/-- The Johnson adjacency operator commutes with real scalar multiplication. -/
theorem johnsonAct_smul {n k : ℕ} (a : ℝ) (g : JohnsonVertex n k → ℝ) :
    johnsonAct (fun S => a * g S) = fun S => a * johnsonAct g S := by
  funext S
  unfold johnsonAct
  simp only [Finset.mul_sum]

/-- The shifted Johnson operator preserves pointwise addition. -/
theorem johnsonOp_add {n k : ℕ} (c : ℝ) (g h : JohnsonVertex n k → ℝ) :
    johnsonOp c (fun S => g S + h S)
      = fun S => johnsonOp c g S + johnsonOp c h S := by
  funext S
  unfold johnsonOp
  rw [johnsonAct_add]
  ring

/-- The shifted Johnson operator commutes with real scalar multiplication. -/
theorem johnsonOp_smul {n k : ℕ} (c a : ℝ) (g : JohnsonVertex n k → ℝ) :
    johnsonOp c (fun S => a * g S) = fun S => a * johnsonOp c g S := by
  funext S
  unfold johnsonOp
  rw [johnsonAct_smul]
  ring

/-- The shifted Johnson operator sends the zero function to zero. -/
theorem johnsonOp_zero {n k : ℕ} (c : ℝ) :
    johnsonOp (n := n) (k := k) c (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  funext S
  unfold johnsonOp
  simp [johnsonAct]

/-- The composite of the shifted Johnson operators with shifts `johnsonTheta n k j` for indices
from zero through `m`. -/
def johnsonAnn {n k : ℕ} : ℕ → (JohnsonVertex n k → ℝ) → (JohnsonVertex n k → ℝ)
  | 0, g => johnsonOp (johnsonTheta n k 0) g
  | (m+1), g => johnsonAnn m (johnsonOp (johnsonTheta n k (m+1)) g)

/-- Unfolds the last shifted-operator factor in `johnsonAnn (m+1)`. -/
theorem johnsonAnn_succ {n k : ℕ} (m : ℕ) (g : JohnsonVertex n k → ℝ) :
    johnsonAnn (m+1) g = johnsonAnn m (johnsonOp (johnsonTheta n k (m+1)) g) := rfl

/-- Every Johnson annihilator operator preserves pointwise addition. -/
theorem johnsonAnn_add {n k : ℕ} :
    ∀ (m : ℕ) (g h : JohnsonVertex n k → ℝ),
      johnsonAnn m (fun S => g S + h S)
        = fun S => johnsonAnn m g S + johnsonAnn m h S
  | 0, g, h => johnsonOp_add _ g h
  | (m+1), g, h => by
      rw [johnsonAnn_succ, johnsonAnn_succ, johnsonAnn_succ, johnsonOp_add]
      exact johnsonAnn_add m _ _

/-- Every Johnson annihilator operator commutes with real scalar multiplication. -/
theorem johnsonAnn_smul {n k : ℕ} :
    ∀ (m : ℕ) (a : ℝ) (g : JohnsonVertex n k → ℝ),
      johnsonAnn m (fun S => a * g S) = fun S => a * johnsonAnn m g S
  | 0, a, g => johnsonOp_smul _ a g
  | (m+1), a, g => by
      rw [johnsonAnn_succ, johnsonAnn_succ, johnsonOp_smul]
      exact johnsonAnn_smul m a _

/-- Every Johnson annihilator operator sends the zero function to zero. -/
theorem johnsonAnn_zero {n k : ℕ} :
    ∀ (m : ℕ), johnsonAnn (n := n) (k := k) m (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ)
  | 0 => johnsonOp_zero _
  | (m+1) => by
      rw [johnsonAnn_succ, johnsonOp_zero]
      exact johnsonAnn_zero m

/-- The Johnson annihilator operator commutes with finite sums of functions. -/
theorem johnsonAnn_sum {n k : ℕ} {ι : Type*} (s : Finset ι) (m : ℕ)
    (f : ι → JohnsonVertex n k → ℝ) :
    johnsonAnn m (fun S => ∑ a ∈ s, f a S)
      = fun S => ∑ a ∈ s, johnsonAnn m (f a) S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact johnsonAnn_zero m
  | insert a s ha ih =>
      have hterm : (fun S => ∑ b ∈ insert a s, f b S)
          = (fun S => f a S + (fun S => ∑ b ∈ s, f b S) S) := by
        funext S; rw [Finset.sum_insert ha]
      have hterm2 : (fun S => ∑ b ∈ insert a s, johnsonAnn m (f b) S)
          = (fun S => johnsonAnn m (f a) S
              + (fun S => ∑ b ∈ s, johnsonAnn m (f b) S) S) := by
        funext S; rw [Finset.sum_insert ha]
      rw [hterm, hterm2, johnsonAnn_add, ih]

/-- For `T.card ≤ m ≤ k ≤ n`, the operator `johnsonAnn m` annihilates the containment indicator
of `T`. -/
theorem johnsonAnn_ind {n k : ℕ} (hk : k ≤ n) :
    ∀ (m : ℕ) (T : Finset (Fin n)), T.card ≤ m → m ≤ k →
      johnsonAnn (n := n) (k := k) m (johnsonInd (n := n) (k := k) T) = fun _ => (0 : ℝ) := by
  intro m
  induction m with
  | zero =>
      intro T hT _
      have hT0 : T.card = 0 := Nat.le_zero.mp hT
      have hTe : T = ∅ := Finset.card_eq_zero.mp hT0
      funext S
      show johnsonOp (johnsonTheta n k 0) (johnsonInd T) S = 0
      rw [show johnsonTheta n k 0 = johnsonTheta n k T.card by rw [hT0]]
      rw [johnsonOp_ind T S hk (by omega : T.card ≤ k)]
      simp [hTe]
  | succ m ih =>
      intro T hT hmk
      rw [johnsonAnn_succ]
      have hTk : T.card ≤ k := by omega

      have hop : johnsonAnn (n := n) (k := k) m
          (johnsonOp (n := n) (k := k) (johnsonTheta n k T.card)
            (johnsonInd (n := n) (k := k) T))
          = fun _ => (0 : ℝ) := by
        have hfun : (johnsonOp (johnsonTheta n k T.card) (johnsonInd T) : JohnsonVertex n k → ℝ)
            = fun S => ((k : ℝ) - T.card + 1) * ∑ u ∈ T, johnsonInd (T.erase u) S := by
          funext S
          rw [johnsonOp_ind T S hk hTk]
        rw [hfun]
        have hfun2 : ((fun S => ((k : ℝ) - T.card + 1) * ∑ u ∈ T, johnsonInd (T.erase u) S) : JohnsonVertex n k → ℝ)
            = (fun S => ∑ u ∈ T,
                (((k : ℝ) - T.card + 1) * johnsonInd (T.erase u) S)) := by
          funext S; rw [Finset.mul_sum]
        rw [hfun2, johnsonAnn_sum]
        funext S
        apply Finset.sum_eq_zero
        intro u hu
        rw [johnsonAnn_smul]
        have hcu : (T.erase u).card ≤ m := by
          rw [Finset.card_erase_of_mem hu]; omega
        rw [ih (T.erase u) hcu (by omega)]
        simp
      by_cases hc : T.card = m+1
      · rw [show johnsonTheta n k (m+1) = johnsonTheta n k T.card by rw [hc]]
        exact hop
      · have hcm : T.card ≤ m := by omega
        have hfun : (johnsonOp (johnsonTheta n k (m+1)) (johnsonInd T) : JohnsonVertex n k → ℝ)
            = fun S => johnsonOp (johnsonTheta n k T.card) (johnsonInd T) S
                + (fun S =>
                    (johnsonTheta n k T.card - johnsonTheta n k (m+1)) * johnsonInd T S) S := by
          funext S; unfold johnsonOp; ring
        rw [hfun, johnsonAnn_add, hop, johnsonAnn_smul, ih T hcm (by omega)]
        funext S
        simp

/-- The elements of the original vertex absent from a swapped vertex form exactly the singleton
of the removed element. -/
theorem swap_sdiff_left {n k : ℕ} (S : JohnsonVertex n k) {i j : Fin n}
    (hi : i ∈ S.1) (hj : j ∉ S.1) :
    S.1 \ (johnsonSwap S i j hi hj).1 = {i} := by
  ext x
  rw [Finset.mem_sdiff, mem_swap_iff S hi hj, Finset.mem_singleton]
  constructor
  · rintro ⟨hxS, hnot⟩
    by_contra hxi
    exact hnot (Or.inr ⟨hxS, hxi⟩)
  · rintro rfl
    refine ⟨hi, ?_⟩
    rintro (h | ⟨_, hxi⟩)
    · exact hj (h ▸ hi)
    · exact hxi rfl

/-- The elements of a swapped vertex absent from the original vertex form exactly the singleton
of the inserted element. -/
theorem swap_sdiff_right {n k : ℕ} (S : JohnsonVertex n k) {i j : Fin n}
    (hi : i ∈ S.1) (hj : j ∉ S.1) :
    (johnsonSwap S i j hi hj).1 \ S.1 = {j} := by
  ext x
  rw [Finset.mem_sdiff, mem_swap_iff S hi hj, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxS⟩
    rcases hx with hxj | ⟨hxS', _⟩
    · exact hxj
    · exact absurd hxS' hxS
  · rintro rfl
    exact ⟨Or.inl rfl, hj⟩

/-- Vertices whose two set differences are specified singletons are related by the corresponding
single-element swap. -/
theorem swap_of_sdiff_eq {n k : ℕ} (S S' : JohnsonVertex n k) {x y : Fin n}
    (hxS : x ∈ S.1) (hyS : y ∉ S.1)
    (hx : S.1 \ S'.1 = {x}) (hy : S'.1 \ S.1 = {y}) :
    johnsonSwap S x y hxS hyS = S' := by
  have hyS' : y ∈ S'.1 := by
    have hmem : y ∈ S'.1 \ S.1 := by rw [hy]; exact Finset.mem_singleton_self y
    exact (Finset.mem_sdiff.mp hmem).1
  apply Subtype.ext
  ext z
  rw [mem_swap_iff S hxS hyS]
  constructor
  · rintro (hzy | ⟨hzS, hzx⟩)
    · rw [hzy]; exact hyS'
    · by_contra hzS'
      have hmem : z ∈ S.1 \ S'.1 := Finset.mem_sdiff.mpr ⟨hzS, hzS'⟩
      rw [hx, Finset.mem_singleton] at hmem
      exact hzx hmem
  · intro hzS'
    by_cases hzS : z ∈ S.1
    · refine Or.inr ⟨hzS, ?_⟩
      intro hzx
      have hxS' : x ∉ S'.1 := by
        have hmem : x ∈ S.1 \ S'.1 := by rw [hx]; exact Finset.mem_singleton_self x
        exact (Finset.mem_sdiff.mp hmem).2
      exact hxS' (hzx ▸ hzS')
    · have hmem : z ∈ S'.1 \ S.1 := Finset.mem_sdiff.mpr ⟨hzS', hzS⟩
      rw [hy, Finset.mem_singleton] at hmem
      exact Or.inl hmem

/-- Expresses the Johnson adjacency action as a sum over all vertices weighted by the adjacency
indicator. -/
theorem johnsonAct_eq_adj_sum {n k : ℕ} (g : JohnsonVertex n k → ℝ) (S : JohnsonVertex n k) :
    johnsonAct g S
      = ∑ S' : JohnsonVertex n k, (if (S.1 \ S'.1).card = 1 then (1 : ℝ) else 0) * g S' := by
  classical
  let P : Finset (↥S.1 × ↥(Finset.univ \ S.1)) :=
    S.1.attach ×ˢ (Finset.univ \ S.1).attach
  let f : ↥S.1 × ↥(Finset.univ \ S.1) → JohnsonVertex n k :=
    fun p => johnsonSwap S p.1.1 p.2.1 p.1.2 (Finset.mem_sdiff.mp p.2.2).2
  have hinj : ∀ p ∈ P, ∀ q ∈ P, f p = f q → p = q := by
    intro p hp q hq heq
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
    obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := q
    have h1 : S.1 \ (f (⟨i, hi⟩, ⟨j, hj⟩)).1 = {i} :=
      swap_sdiff_left S hi (Finset.mem_sdiff.mp hj).2
    have h2 : S.1 \ (f (⟨i', hi'⟩, ⟨j', hj'⟩)).1 = {i'} :=
      swap_sdiff_left S hi' (Finset.mem_sdiff.mp hj').2
    rw [heq] at h1
    rw [h2] at h1
    have hii : i = i' := Finset.singleton_inj.mp h1.symm
    have g1 : (f (⟨i, hi⟩, ⟨j, hj⟩)).1 \ S.1 = {j} :=
      swap_sdiff_right S hi (Finset.mem_sdiff.mp hj).2
    have g2 : (f (⟨i', hi'⟩, ⟨j', hj'⟩)).1 \ S.1 = {j'} :=
      swap_sdiff_right S hi' (Finset.mem_sdiff.mp hj').2
    rw [heq] at g1
    rw [g2] at g1
    have hjj : j = j' := Finset.singleton_inj.mp g1.symm
    subst hii hjj
    rfl
  have himage : P.image f = Finset.univ.filter (fun S' => (S.1 \ S'.1).card = 1) := by
    ext S'
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [swap_sdiff_left S p.1.2 (Finset.mem_sdiff.mp p.2.2).2]
      exact Finset.card_singleton _
    · rintro ⟨_, hadj⟩
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hadj
      have hxS : x ∈ S.1 :=
        (Finset.mem_sdiff.mp (by rw [hx]; exact Finset.mem_singleton_self x)).1
      have hsymm : (S'.1 \ S.1).card = 1 := johnsonAdj_symm hadj
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hsymm
      have hyS : y ∉ S.1 :=
        (Finset.mem_sdiff.mp (by rw [hy]; exact Finset.mem_singleton_self y)).2
      have hyU : y ∈ Finset.univ \ S.1 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyS⟩
      refine ⟨(⟨x, hxS⟩, ⟨y, hyU⟩), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_attach S.1 ⟨x, hxS⟩, Finset.mem_attach _ ⟨y, hyU⟩⟩
      · exact swap_of_sdiff_eq S S' hxS hyS hx hy
  have hprod : (∑ p ∈ P, g (f p))
      = ∑ i ∈ S.1.attach, ∑ j ∈ (Finset.univ \ S.1).attach,
          g (johnsonSwap S i.1 j.1 i.2 (Finset.mem_sdiff.mp j.2).2) := by
    rw [Finset.sum_product]
  unfold johnsonAct
  rw [← hprod, ← Finset.sum_image hinj]
  rw [himage, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S' _
  by_cases h : (S.1 \ S'.1).card = 1
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- The Johnson adjacency operator is self-adjoint for the finite real dot product. -/
theorem johnsonAct_inner_symm {n k : ℕ} (v w : JohnsonVertex n k → ℝ) :
    (∑ S, johnsonAct v S * w S) = ∑ S, v S * johnsonAct w S := by
  classical
  have hL : ∀ S : JohnsonVertex n k, johnsonAct v S * w S
      = ∑ S' : JohnsonVertex n k,
          (if (S.1 \ S'.1).card = 1 then (1 : ℝ) else 0) * v S' * w S := by
    intro S
    rw [johnsonAct_eq_adj_sum, Finset.sum_mul]
  have hR : ∀ S : JohnsonVertex n k, v S * johnsonAct w S
      = ∑ S' : JohnsonVertex n k,
          (if (S.1 \ S'.1).card = 1 then (1 : ℝ) else 0) * v S * w S' := by
    intro S
    rw [johnsonAct_eq_adj_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S' _
    ring
  rw [Finset.sum_congr rfl (fun S _ => hL S), Finset.sum_congr rfl (fun S _ => hR S)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have hs : (if (q.1 \ p.1).card = 1 then (1 : ℝ) else 0)
      = (if (p.1 \ q.1).card = 1 then (1 : ℝ) else 0) := by
    by_cases h : (q.1 \ p.1).card = 1
    · have hpq : (p.1 \ q.1).card = 1 := johnsonAdj_symm h
      rw [if_pos h, if_pos hpq]
    · have hpq : ¬ (p.1 \ q.1).card = 1 := fun hc => h (johnsonAdj_symm hc)
      rw [if_neg h, if_neg hpq]
  rw [hs]

/-- Pairing a Johnson annihilator applied to `g` with an eigenvector multiplies the original
pairing by the product of the corresponding shifted eigenvalues. -/
theorem johnsonAnn_pairing {n k : ℕ} (v : JohnsonVertex n k → ℝ) (lam : ℝ)
    (hv : johnsonAct v = fun S => lam * v S) :
    ∀ (m : ℕ) (g : JohnsonVertex n k → ℝ),
      (∑ S, johnsonAnn m g S * v S)
        = (∏ j ∈ Finset.range (m+1), (lam - johnsonTheta n k j))
            * ∑ S, g S * v S := by
  have hstep : ∀ (c : ℝ) (g : JohnsonVertex n k → ℝ),
      (∑ S, johnsonOp c g S * v S) = (lam - c) * ∑ S, g S * v S := by
    intro c g
    have h1 : (∑ S, johnsonOp c g S * v S)
        = ∑ S, (johnsonAct g S * v S - c * (g S * v S)) := by
      apply Finset.sum_congr rfl
      intro S _
      unfold johnsonOp
      ring
    rw [h1, Finset.sum_sub_distrib, johnsonAct_inner_symm g v, hv]
    have hA : (∑ S, g S * (lam * v S)) = lam * ∑ S, g S * v S := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    have hB : (∑ S, c * (g S * v S)) = c * ∑ S, g S * v S := by
      rw [Finset.mul_sum]
    rw [hA, hB]
    ring
  intro m
  induction m with
  | zero =>
      intro g
      show (∑ S, johnsonOp (johnsonTheta n k 0) g S * v S)
          = (∏ j ∈ Finset.range (0+1), (lam - johnsonTheta n k j))
              * ∑ S, g S * v S
      rw [hstep]
      simp [Finset.prod_range_succ]
  | succ m ih =>
      intro g
      show (∑ S, johnsonAnn m (johnsonOp (johnsonTheta n k (m+1)) g) S * v S)
          = (∏ j ∈ Finset.range (m+1+1), (lam - johnsonTheta n k j))
              * ∑ S, g S * v S
      rw [ih, hstep]
      rw [Finset.prod_range_succ (f := fun j => lam - johnsonTheta n k j) (n := m+1)]
      ring

/-- Every real eigenvalue of the Johnson adjacency action with a nonzero eigenvector equals
`johnsonTheta n k j` for some `j ≤ k`, when `k ≤ n`. -/
theorem johnsonEigenvalue_mem {n k : ℕ} (hk : k ≤ n) (v : JohnsonVertex n k → ℝ)
    (lam : ℝ) (hv : johnsonAct v = fun S => lam * v S) (hv0 : v ≠ 0) :
    ∃ j ∈ Finset.range (k+1), lam = johnsonTheta n k j := by
  classical
  have hex : ∃ S0 : JohnsonVertex n k, v S0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext fun S => h S)
  obtain ⟨S0, hS0⟩ := hex
  have hann := johnsonAnn_ind hk k S0.1 (by rw [S0.2]) (le_refl k)
  have hp := johnsonAnn_pairing v lam hv k (johnsonInd S0)
  have hleft : (∑ S, johnsonAnn k (johnsonInd S0) S * v S) = 0 := by
    rw [hann]
    simp
  rw [hleft] at hp
  have hsum : (∑ S, johnsonInd S0 S * v S) = v S0 := by
    rw [Finset.sum_eq_single S0]
    · simp [johnsonInd]
    · intro S _ hS
      have hnot : ¬ (S0.1 ⊆ S.1) := by
        intro hsub
        have heq : S0.1 = S.1 :=
          Finset.eq_of_subset_of_card_le hsub (by rw [S.2, S0.2])
        exact hS (Subtype.ext heq).symm
      simp [johnsonInd, hnot]
    · intro hS0not
      exact absurd (Finset.mem_univ S0) hS0not
  rw [hsum] at hp
  have hprod0 : (∏ j ∈ Finset.range (k+1), (lam - johnsonTheta n k j)) = 0 := by
    have hz : (∏ j ∈ Finset.range (k+1), (lam - johnsonTheta n k j)) * v S0 = 0 := hp.symm
    exact (mul_eq_zero.mp hz).resolve_right hS0
  obtain ⟨j, hj, hzero⟩ := Finset.prod_eq_zero_iff.mp hprod0
  exact ⟨j, hj, sub_eq_zero.mp hzero⟩

/-- The real adjacency indicator of a Johnson vertex, equal to one on its neighbors and zero
elsewhere. -/
def johnsonW {n k : ℕ} (S : JohnsonVertex n k) : JohnsonVertex n k → ℝ :=
  fun T => if (S.1 \ T.1).card = 1 then (1 : ℝ) else 0

/-- Expresses the Johnson adjacency action using the weights `johnsonW`. -/
theorem johnsonAct_adjW {n k : ℕ} (g : JohnsonVertex n k → ℝ) (S : JohnsonVertex n k) :
    johnsonAct g S = ∑ T, johnsonW S T * g T := by
  rw [johnsonAct_eq_adj_sum]
  simp only [johnsonW]

/-- The existence of a Johnson vertex implies `k ≤ n`. -/
theorem johnsonCard_le {n k : ℕ} (S : JohnsonVertex n k) : k ≤ n := by
  have h := Finset.card_le_univ S.1
  rw [S.2, Fintype.card_fin] at h
  exact h

/-- The unnormalized Johnson eigenvalue expression at index zero is `k*(n-k)`. -/
theorem johnsonTheta_zero_eq {n k : ℕ} :
    johnsonTheta n k 0 = (k : ℝ) * ((n : ℝ) - k) := by
  unfold johnsonTheta
  norm_num

/-- Applying the Johnson adjacency operator to the constant function one gives the degree
`k*(n-k)`. -/
theorem johnsonAct_one {n k : ℕ} (S : JohnsonVertex n k) :
    johnsonAct (fun _ => (1 : ℝ)) S = (k : ℝ) * ((n : ℝ) - k) := by
  have h : (fun _ : JohnsonVertex n k => (1 : ℝ)) = johnsonInd (∅ : Finset (Fin n)) := by
    funext T
    unfold johnsonInd
    rw [if_pos (Finset.empty_subset _)]
  rw [h, johnsonAct_ind]
  have h1 : (S.1 ∩ (∅ : Finset (Fin n))).card = 0 := by simp
  have h2 : johnsonInner (∅ : Finset (Fin n)) S = ((n - k : ℕ) : ℝ) := by
    rw [johnsonInner_eq (johnsonCard_le S), if_pos (by simp)]
  rw [h1, h2, Nat.cast_sub (johnsonCard_le S)]
  ring

/-- The sum of the adjacency weights at any Johnson vertex equals `k*(n-k)`. -/
theorem johnsonadj_deg {n k : ℕ} (S : JohnsonVertex n k) :
    (∑ T : JohnsonVertex n k, johnsonW S T) = (k : ℝ) * ((n : ℝ) - k) := by
  have h := johnsonAct_adjW (n := n) (k := k) (fun _ => (1 : ℝ)) S
  simp only [mul_one] at h
  rw [johnsonAct_one S] at h
  exact h.symm

/-- When the removed element lies outside `A`, the part of `A` absent from the swapped vertex is
obtained by removing the inserted element from `A` outside the original vertex. -/
theorem swap_sdiff_in {n k : ℕ} (A T : JohnsonVertex n k) {x y : Fin n}
    (hx : x ∈ T.1) (hy : y ∉ T.1) (hxA : x ∉ A.1) :
    A.1 \ (johnsonSwap T x y hx hy).1 = (A.1 \ T.1) \ {y} := by
  ext z
  rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_sdiff,
    mem_swap_iff T hx hy, Finset.mem_singleton]
  constructor
  · rintro ⟨hzA, hzU⟩
    have hzy : z ≠ y := by
      rintro rfl
      exact hzU (Or.inl rfl)
    have hzT : z ∉ T.1 := by
      rintro hzT
      exact hzU (Or.inr ⟨hzT, fun hzx => hxA (hzx ▸ hzA)⟩)
    exact ⟨⟨hzA, hzT⟩, hzy⟩
  · rintro ⟨⟨hzA, hzT⟩, hzy⟩
    refine ⟨hzA, ?_⟩
    rintro (hzy' | ⟨h, -⟩)
    · exact hzy hzy'
    · exact hzT h

/-- When the inserted element belongs to `A`, the part of the swapped vertex outside `A` is
obtained by removing the deleted element from the original vertex outside `A`. -/
theorem swap_sdiff_out {n k : ℕ} (T A : JohnsonVertex n k) {x y : Fin n}
    (hx : x ∈ T.1) (hy : y ∉ T.1) (hyA : y ∈ A.1) :
    (johnsonSwap T x y hx hy).1 \ A.1 = (T.1 \ A.1) \ {x} := by
  ext z
  rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_sdiff,
    mem_swap_iff T hx hy, Finset.mem_singleton]
  constructor
  · rintro ⟨hzU, hzA⟩
    have hzx : z ≠ x := by
      rintro rfl
      rcases hzU with hzy | ⟨-, hxx⟩
      · subst hzy; exfalso; exact hzA hyA
      · exact hxx rfl
    have hzT : z ∈ T.1 := by
      rcases hzU with hzy | ⟨hzT, -⟩
      · subst hzy; exfalso; exact hzA hyA
      · exact hzT
    exact ⟨⟨hzT, hzA⟩, hzx⟩
  · rintro ⟨⟨hzT, hzA⟩, hzx⟩
    refine ⟨?_, hzA⟩
    exact Or.inr ⟨hzT, hzx⟩

/-- A top-eigenvalue eigenfunction takes the same value at a global maximum and any adjacent
vertex, assuming `k ≤ n`. -/
theorem johnson_eq_of_max_adj {n k : ℕ} (hk : k ≤ n)
    (g : JohnsonVertex n k → ℝ)
    (hg : ∀ S, johnsonAct g S = johnsonTheta n k 0 * g S)
    {S S' : JohnsonVertex n k} (hadj : johnsonAdj S S')
    (hmax : ∀ T, g T ≤ g S) : g S' = g S := by
  classical
  have hdiff : (∑ T ∈ (Finset.univ : Finset (JohnsonVertex n k)),
        johnsonW S T * (g S - g T))
      = (∑ T ∈ (Finset.univ : Finset (JohnsonVertex n k)), johnsonW S T * g S)
        - (∑ T ∈ (Finset.univ : Finset (JohnsonVertex n k)), johnsonW S T * g T) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  have hsum : (∑ T ∈ (Finset.univ : Finset (JohnsonVertex n k)),
      johnsonW S T * (g S - g T)) = 0 := by
    rw [hdiff]
    have hgT : (∑ T ∈ (Finset.univ : Finset (JohnsonVertex n k)), johnsonW S T * g T)
        = johnsonAct g S := by
      rw [johnsonAct_adjW]
    have hc : (∑ T ∈ (Finset.univ : Finset (JohnsonVertex n k)), johnsonW S T * g S)
        = ((k : ℝ) * ((n : ℝ) - k)) * g S := by
      rw [← Finset.sum_mul, johnsonadj_deg S]
    rw [hgT, hc, hg S, johnsonTheta_zero_eq]
    ring
  have hnonneg : ∀ T ∈ (Finset.univ : Finset (JohnsonVertex n k)),
      0 ≤ johnsonW S T * (g S - g T) := by
    intro T _
    have hw : 0 ≤ johnsonW S T := by
      unfold johnsonW
      split_ifs with h
      · exact zero_le_one
      · exact le_refl 0
    have hgt : 0 ≤ g S - g T := by linarith [hmax T]
    exact mul_nonneg hw hgt
  have hterm : johnsonW S S' * (g S - g S') = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum S' (Finset.mem_univ S')
  have hwS' : johnsonW S S' = 1 := by
    unfold johnsonW
    rw [if_pos (show (S.1 \ S'.1).card = 1 from hadj)]
  rw [hwS', one_mul] at hterm
  exact (sub_eq_zero.mp hterm).symm

/-- For `k ≤ n`, every eigenfunction of the Johnson adjacency operator with eigenvalue
`johnsonTheta n k 0` is constant. -/
theorem johnson_const_of_eigen {n k : ℕ} (hk : k ≤ n) (g : JohnsonVertex n k → ℝ)
    (hg : ∀ S, johnsonAct g S = johnsonTheta n k 0 * g S) :
    ∃ c : ℝ, g = fun _ => c := by
  classical
  haveI : Nonempty (JohnsonVertex n k) := by
    have h1 : k ≤ (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact hk
    obtain ⟨t, -, ht⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := k) h1
    exact ⟨⟨t, ht⟩⟩
  obtain ⟨S0, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (JohnsonVertex n k)) g Finset.univ_nonempty
  refine ⟨g S0, funext fun T => ?_⟩
  have key : ∀ N (T : JohnsonVertex n k), (S0.1 \ T.1).card ≤ N → g T = g S0 := by
    intro N
    induction N with
    | zero =>
        intro T hN
        have hempty : S0.1 \ T.1 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hN)
        have hsub : S0.1 ⊆ T.1 := Finset.sdiff_eq_empty_iff_subset.mp hempty
        have heq : S0.1 = T.1 :=
          Finset.eq_of_subset_of_card_le hsub (by rw [T.2, S0.2])
        rw [Subtype.ext heq.symm]
    | succ N ih =>
        intro T hN
        by_cases hTS : T = S0
        · rw [hTS]
        · have hne : S0.1 \ T.1 ≠ ∅ := by
            intro h
            exact hTS (Subtype.ext
              (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp h)
                (by rw [T.2, S0.2])).symm)
          obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          have hyS0 : y ∈ S0.1 := (Finset.mem_sdiff.mp hy).1
          have hyT : y ∉ T.1 := (Finset.mem_sdiff.mp hy).2
          have hne2 : T.1 \ S0.1 ≠ ∅ := by
            intro h
            exact hTS (Subtype.ext
              (Finset.eq_of_subset_of_card_le (Finset.sdiff_eq_empty_iff_subset.mp h)
                (by rw [S0.2, T.2])))
          obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne2
          have hxT : x ∈ T.1 := (Finset.mem_sdiff.mp hx).1
          have hxS0 : x ∉ S0.1 := (Finset.mem_sdiff.mp hx).2
          have hadj : johnsonAdj T (johnsonSwap T x y hxT hyT) := by
            show (T.1 \ (johnsonSwap T x y hxT hyT).1).card = 1
            rw [swap_sdiff_left T hxT hyT]
            simp
          have hcard : (S0.1 \ (johnsonSwap T x y hxT hyT).1).card
              = (S0.1 \ T.1).card - 1 := by
            rw [swap_sdiff_in S0 T hxT hyT hxS0, Finset.sdiff_singleton_eq_erase,
              Finset.card_erase_of_mem hy]
          have hU : g (johnsonSwap T x y hxT hyT) = g S0 := ih _ (by omega)
          have hUT : johnsonAdj (johnsonSwap T x y hxT hyT) T := johnsonAdj_symm hadj
          have hmaxU : ∀ V, g V ≤ g (johnsonSwap T x y hxT hyT) := fun V => by
            rw [hU]
            exact hmax V (Finset.mem_univ V)
          rw [johnson_eq_of_max_adj hk g hg hUT hmaxU, hU]
  exact key (S0.1 \ T.1).card T (le_refl _)

/-- The difference between `johnsonTheta n k 0` and `johnsonTheta n k m` is `m*(n+1-m)`. -/
theorem johnsonTheta_sub_zero {n k m : ℕ} :
    johnsonTheta n k 0 - johnsonTheta n k m
      = (m : ℝ) * ((n : ℝ) + 1 - m) := by
  unfold johnsonTheta
  ring

/-- For `1 ≤ m ≤ k ≤ n`, the value `johnsonTheta n k m` is strictly below `johnsonTheta n k 0`. -/
theorem johnsonTheta_pos_gap {n k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hk : k ≤ n) :
    johnsonTheta n k m < johnsonTheta n k 0 := by
  have hsub := johnsonTheta_sub_zero (n := n) (k := k) (m := m)
  have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h2 : (0 : ℝ) < (n : ℝ) + 1 - m := by
    have : (m : ℝ) ≤ n := by exact_mod_cast le_trans hmk hk
    linarith
  have hpos : (0 : ℝ) < (m : ℝ) * ((n : ℝ) + 1 - m) := mul_pos h1 h2
  linarith [hsub]

/-- For `1 ≤ m ≤ k`, `k ≥ 2`, and `2*k ≤ n`, bounds the absolute unnormalized eigenvalue
expression by `(k-1)*(n-k)`. -/
theorem johnsonTheta_abs_le {n k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k)
    (hk2 : 2 ≤ k) (hkn : 2 * k ≤ n) :
    |johnsonTheta n k m| ≤ ((k : ℝ) - 1) * ((n : ℝ) - k) := by
  have hk : k ≤ n := by omega
  rw [abs_le]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hmk' : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hnk : (k : ℝ) ≤ (n : ℝ) - k := by
    have h : (k : ℝ) + k ≤ (n : ℝ) := by
      have h' : k + k ≤ n := by omega
      exact_mod_cast h'
    linarith
  have hmu : (k : ℝ) ≤ ((k : ℝ) - 1) * ((n : ℝ) - k) := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ (n : ℝ) - k := by linarith
    have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have h4 : (k : ℝ) ≤ ((k : ℝ) - 1) * (k : ℝ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 2)
        (by linarith : (0 : ℝ) ≤ (k : ℝ))]
    have h5 : ((k : ℝ) - 1) * (k : ℝ) ≤ ((k : ℝ) - 1) * ((n : ℝ) - k) :=
      mul_le_mul_of_nonneg_left hnk h1
    linarith
  constructor
  · have hlow : -(m : ℝ) ≤ johnsonTheta n k m := by
      unfold johnsonTheta
      have h1 : (0 : ℝ) ≤ (k : ℝ) - m := by linarith
      have h2 : (0 : ℝ) ≤ (n : ℝ) - k - m := by
        have h2' : (m : ℝ) + k ≤ (n : ℝ) := by
          have h : m + k ≤ 2 * k := by omega
          have h'' : m + k ≤ n := le_trans h hkn
          exact_mod_cast h''
        linarith
      nlinarith [mul_nonneg h1 h2]
    linarith
  · have hsub := johnsonTheta_sub_zero (n := n) (k := k) (m := m)
    have hmn : (n : ℝ) ≤ (m : ℝ) * ((n : ℝ) + 1 - m) := by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h2 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hmk hk
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 1)
        (by linarith : (0 : ℝ) ≤ (n : ℝ) - m)]
    have h0 : johnsonTheta n k 0 = (k : ℝ) * ((n : ℝ) - k) := johnsonTheta_zero_eq
    have hle : (k : ℝ) * ((n : ℝ) - k) - n ≤ ((k : ℝ) - 1) * ((n : ℝ) - k) := by
      nlinarith
    linarith

/-- The real adjacency matrix of the Johnson graph. -/
def johnsonMat (n k : ℕ) : Matrix (JohnsonVertex n k) (JohnsonVertex n k) ℝ :=
  fun S T => johnsonW S T

/-- The Johnson adjacency weights are symmetric. -/
theorem johnsonW_symm {n k : ℕ} (S T : JohnsonVertex n k) :
    johnsonW S T = johnsonW T S := by
  unfold johnsonW
  have h : (S.1 \ T.1).card = (T.1 \ S.1).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, S.2, T.2]
    rw [Finset.inter_comm (s₁ := S.1) (s₂ := T.1)]
  rw [h]

/-- The real Johnson adjacency matrix is Hermitian. -/
theorem johnsonMat_herm (n k : ℕ) : (johnsonMat n k).IsHermitian := by
  ext S T
  rw [Matrix.conjTranspose_apply]
  exact johnsonW_symm T S

/-- Multiplication by the Johnson adjacency matrix agrees with `johnsonAct`. -/
theorem johnsonMat_mulVec {n k : ℕ} (v : JohnsonVertex n k → ℝ) :
    (johnsonMat n k).mulVec v = johnsonAct v := by
  funext S
  rw [johnsonAct_adjW]
  rfl

/-- The Hermitian eigenvector basis of the Johnson adjacency matrix satisfies the eigenvector
equation for `johnsonAct`. -/
theorem johnson_eigen_bridge {n k : ℕ} (j : JohnsonVertex n k) :
    johnsonAct ((johnsonMat_herm n k).eigenvectorBasis j).ofLp
      = fun S => (johnsonMat_herm n k).eigenvalues j
          * ((johnsonMat_herm n k).eigenvectorBasis j).ofLp S := by
  funext S
  have h := congrFun ((johnsonMat_herm n k).mulVec_eigenvectorBasis j) S
  rw [johnsonMat_mulVec] at h
  simpa using h

/-- For `k ≤ n`, every eigenvalue in the Hermitian spectral decomposition equals `johnsonTheta n
k i` for some `i ≤ k`. -/
theorem johnson_eigenvalue_mem' {n k : ℕ} (hk : k ≤ n) (j : JohnsonVertex n k) :
    ∃ i ∈ Finset.range (k + 1),
      (johnsonMat_herm n k).eigenvalues j = johnsonTheta n k i := by
  have hbridge := johnson_eigen_bridge (n := n) (k := k) j
  have hne : ((johnsonMat_herm n k).eigenvectorBasis j).ofLp
      ≠ (0 : JohnsonVertex n k → ℝ) := by
    intro h
    have hb : (johnsonMat_herm n k).eigenvectorBasis j = 0 := by
      rw [← WithLp.toLp_ofLp 2 ((johnsonMat_herm n k).eigenvectorBasis j), h]
      rfl
    have hone := (johnsonMat_herm n k).eigenvectorBasis.inner_eq_ite j j
    rw [hb] at hone
    simp at hone
  exact johnsonEigenvalue_mem hk _ _ hbridge hne

/-- For `k ≤ n`, a spectral-basis eigenvector with eigenvalue `johnsonTheta n k 0` is constant. -/
theorem johnson_eigen_const {n k : ℕ} (hk : k ≤ n) (j : JohnsonVertex n k)
    (h0 : (johnsonMat_herm n k).eigenvalues j = johnsonTheta n k 0) :
    ∃ c : ℝ, ((johnsonMat_herm n k).eigenvectorBasis j).ofLp = fun _ => c := by
  refine johnson_const_of_eigen hk _ (fun S => ?_)
  have hb := johnson_eigen_bridge (n := n) (k := k) j
  rw [h0] at hb
  exact congrFun hb S

/-- Applying `johnsonAct` multiplies each coefficient in the Hermitian eigenvector basis by its
associated eigenvalue. -/
theorem johnson_coeff {n k : ℕ} (x : JohnsonVertex n k → ℝ) (i : JohnsonVertex n k) :
    inner ℝ ((johnsonMat_herm n k).eigenvectorBasis i)
        (WithLp.toLp 2 (johnsonAct x))
      = (johnsonMat_herm n k).eigenvalues i
        * inner ℝ ((johnsonMat_herm n k).eigenvectorBasis i) (WithLp.toLp 2 x) := by
  have hL : inner ℝ ((johnsonMat_herm n k).eigenvectorBasis i)
      (WithLp.toLp 2 (johnsonAct x))
      = ∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * johnsonAct x S := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro S _
    rw [Real.inner_apply, WithLp.ofLp_toLp]
  have hR : inner ℝ ((johnsonMat_herm n k).eigenvectorBasis i) (WithLp.toLp 2 x)
      = ∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * x S := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro S _
    rw [Real.inner_apply, WithLp.ofLp_toLp]
  rw [hL, hR]
  have hdist : (∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * johnsonAct x S)
      = ∑ S, ∑ T, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S
          * (johnsonW S T * x T) := by
    apply Finset.sum_congr rfl
    intro S _
    rw [johnsonAct_adjW, Finset.mul_sum]
  rw [hdist, Finset.sum_comm]
  have hinner : ∀ T, (∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S
        * (johnsonW S T * x T))
      = ((johnsonMat_herm n k).eigenvalues i
          * ((johnsonMat_herm n k).eigenvectorBasis i).ofLp T) * x T := by
    intro T
    have hfac : (∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S
          * (johnsonW S T * x T))
        = (∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * johnsonW S T) * x T := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      ring
    rw [hfac]
    have hsym : (∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * johnsonW S T)
        = ∑ S, johnsonW T S * ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [johnsonW_symm T S]
      ring
    have h2 : (∑ S, johnsonW T S * ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S)
        = (johnsonMat_herm n k).eigenvalues i
          * ((johnsonMat_herm n k).eigenvectorBasis i).ofLp T := by
      rw [← johnsonAct_adjW, johnson_eigen_bridge]
    rw [hsym, h2]
  have hsum : (∑ T, ∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S
        * (johnsonW S T * x T))
      = ∑ T, ((johnsonMat_herm n k).eigenvalues i
          * ((johnsonMat_herm n k).eigenvectorBasis i).ofLp T) * x T :=
    Finset.sum_congr rfl (fun T _ => hinner T)
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  ring

/-- For `k ≥ 2` and `2*k ≤ n`, the Johnson adjacency operator contracts the squared norm of
vectors whose entries sum to zero by at most `((k-1)*(n-k))^2`. -/
theorem johnson_contract {n k : ℕ} (hk2 : 2 ≤ k) (hkn : 2 * k ≤ n)
    (x : JohnsonVertex n k → ℝ) (hx : ∑ S, x S = 0) :
    (∑ S, (∑ T, johnsonW S T * x T)^2)
      ≤ (((k : ℝ) - 1) * ((n : ℝ) - k))^2 * (∑ S, (x S)^2) := by
  classical
  have hk : k ≤ n := by omega
  set mu : ℝ := ((k : ℝ) - 1) * ((n : ℝ) - k) with hmu
  have hmu0 : 0 ≤ mu := by
    rw [hmu]
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have h2 : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    exact mul_nonneg (by linarith) (by linarith)
  set b : OrthonormalBasis (JohnsonVertex n k) ℝ (EuclideanSpace ℝ (JohnsonVertex n k)) :=
    (johnsonMat_herm n k).eigenvectorBasis with hb
  set lam : JohnsonVertex n k → ℝ := (johnsonMat_herm n k).eigenvalues with hlam
  set X : EuclideanSpace ℝ (JohnsonVertex n k) := WithLp.toLp 2 x with hX
  set Y : EuclideanSpace ℝ (JohnsonVertex n k) := WithLp.toLp 2 (johnsonAct x) with hY
  have hYlp : Y.ofLp = johnsonAct x := rfl
  have hXlp : X.ofLp = x := rfl
  have hcoeff : ∀ i, inner ℝ (b i) Y = lam i * inner ℝ (b i) X := by
    intro i
    rw [hY, hX, hb, hlam]
    exact johnson_coeff x i
  have hterm : ∀ i, ‖inner ℝ (b i) Y‖^2 ≤ mu^2 * ‖inner ℝ (b i) X‖^2 := by
    intro i
    obtain ⟨p, hp, hpe⟩ := johnson_eigenvalue_mem' hk i
    have hd2 : ‖inner ℝ (b i) Y‖^2 = (lam i)^2 * ‖inner ℝ (b i) X‖^2 := by
      rw [hcoeff i, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
    by_cases hp0 : p = 0
    · rw [hp0] at hpe
      have hz : inner ℝ (b i) X = 0 := by
        have hform : inner ℝ (b i) X
            = ∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * x S := by
          rw [hX, hb, PiLp.inner_apply]
          apply Finset.sum_congr rfl
          intro S _
          rw [Real.inner_apply, WithLp.ofLp_toLp]
        rw [hform]
        obtain ⟨cc, hcc⟩ := johnson_eigen_const hk i hpe
        have hpt : ∀ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S = cc := by
          intro S
          rw [hcc]
        calc (∑ S, ((johnsonMat_herm n k).eigenvectorBasis i).ofLp S * x S)
            = ∑ S, cc * x S := by
              apply Finset.sum_congr rfl
              intro S _
              rw [hpt S]
          _ = cc * ∑ S, x S := by rw [Finset.mul_sum]
          _ = 0 := by rw [hx, mul_zero]
      rw [hd2, hz]
      simp
    · have hp1 : 1 ≤ p := by omega
      have hpk : p ≤ k := by
        have h := Finset.mem_range.mp hp
        omega
      have hsq : (lam i)^2 ≤ mu^2 := by
        have ha : |lam i| ≤ mu := by
          rw [hlam]
          rw [hpe]
          rw [hmu]
          exact johnsonTheta_abs_le hp1 hpk hk2 hkn
        exact (sq_le_sq (a := lam i) (b := mu)).mpr (by rwa [abs_of_nonneg hmu0])
      rw [hd2]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hYsq : (∑ i, ‖inner ℝ (b i) Y‖^2) = ‖Y‖^2 := b.sum_sq_norm_inner_right Y
  have hXsq : (∑ i, ‖inner ℝ (b i) X‖^2) = ‖X‖^2 := b.sum_sq_norm_inner_right X
  have hmain : ‖Y‖^2 ≤ mu^2 * ‖X‖^2 := by
    calc ‖Y‖^2 = ∑ i, ‖inner ℝ (b i) Y‖^2 := hYsq.symm
      _ ≤ ∑ i, mu^2 * ‖inner ℝ (b i) X‖^2 := Finset.sum_le_sum (fun i _ => hterm i)
      _ = mu^2 * ∑ i, ‖inner ℝ (b i) X‖^2 := by rw [Finset.mul_sum]
      _ = mu^2 * ‖X‖^2 := by rw [hXsq]
  have hnormX : ‖X‖^2 = ∑ S, (x S)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [hXlp, Real.norm_eq_abs, sq_abs]
  have hnormY : ‖Y‖^2 = ∑ S, (∑ T, johnsonW S T * x T)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro S _
    rw [hYlp, johnsonAct_adjW, Real.norm_eq_abs, sq_abs]
  rw [← hnormX, ← hnormY]
  exact hmain

/-- The Johnson adjacency matrix divided by the degree `k*(n-k)`. -/
def johnsonNorm (n k : ℕ) : Matrix (JohnsonVertex n k) (JohnsonVertex n k) ℝ :=
  fun S T => johnsonW S T / ((k : ℝ) * ((n : ℝ) - k))

/-- The normalized Johnson matrix is symmetric. -/
theorem johnsonNorm_symm {n k : ℕ} (S T : JohnsonVertex n k) :
    johnsonNorm n k S T = johnsonNorm n k T S := by
  unfold johnsonNorm
  rw [johnsonW_symm S T]

/-- For `k ≤ n`, the normalized Johnson matrix has nonnegative entries. -/
theorem johnsonNorm_nonneg {n k : ℕ} (hk : k ≤ n) (S T : JohnsonVertex n k) :
    0 ≤ johnsonNorm n k S T := by
  unfold johnsonNorm
  have hd : 0 ≤ (k : ℝ) * ((n : ℝ) - k) := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) - k := by
      have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      linarith
    exact mul_nonneg h1 h2
  apply div_nonneg _ hd
  unfold johnsonW
  split_ifs <;> norm_num

/-- For `0 < k < n`, each row of the normalized Johnson matrix sums to one. -/
theorem johnsonNorm_rowsum {n k : ℕ} (hk1 : 0 < k) (hkn : k < n) (S : JohnsonVertex n k) :
    (∑ T, johnsonNorm n k S T) = 1 := by
  unfold johnsonNorm
  rw [← Finset.sum_div, johnsonadj_deg]
  have hne : ((k : ℝ) * ((n : ℝ) - k)) ≠ 0 := by
    have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have h2 : (0 : ℝ) < (n : ℝ) - k := by
      have hkn' : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
      linarith
    exact ne_of_gt (mul_pos h1 h2)
  exact div_self hne

/-- Expresses multiplication by the normalized Johnson matrix as adjacency action divided by
`k*(n-k)`. -/
theorem johnsonNorm_mulVec {n k : ℕ} (x : JohnsonVertex n k → ℝ) (S : JohnsonVertex n k) :
    (johnsonNorm n k).mulVec x S
      = (∑ T, johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)) := by
  rw [Matrix.mulVec, dotProduct]
  rw [show (∑ T, johnsonNorm n k S T * x T)
      = ∑ T, (johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)) from by
    unfold johnsonNorm
    apply Finset.sum_congr rfl
    intro T _
    ring]
  rw [← Finset.sum_div]

/-- For `k ≥ 2` and `2*k ≤ n`, the normalized Johnson matrix contracts squared norms on vectors
whose entries sum to zero by at most `((k-1)/k)^2`. -/
theorem johnsonNorm_contract {n k : ℕ} (hk2 : 2 ≤ k) (hkn : 2 * k ≤ n)
    (x : JohnsonVertex n k → ℝ) (hx : ∑ S, x S = 0) :
    (∑ S, (∑ T, johnsonNorm n k S T * x T)^2)
      ≤ (((k : ℝ) - 1) / (k : ℝ))^2 * (∑ S, (x S)^2) := by
  have hraw := johnson_contract hk2 hkn x hx
  have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h2 : (0 : ℝ) < (n : ℝ) - k := by
    have hkn' : (k : ℝ) < (n : ℝ) := by exact_mod_cast (show k < n by omega)
    linarith
  have hkey : (1 / ((k : ℝ) * ((n : ℝ) - k)))^2
        * ((((k : ℝ) - 1) * ((n : ℝ) - k)))^2
      = (((k : ℝ) - 1) / (k : ℝ))^2 := by
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt h1
    have hnk : ((n : ℝ) - k) ≠ 0 := ne_of_gt h2
    field_simp
  have hpt : ∀ S, (∑ T, johnsonNorm n k S T * x T)
      = (∑ T, johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)) := by
    intro S
    unfold johnsonNorm
    rw [show (∑ T, johnsonW S T / ((k : ℝ) * ((n : ℝ) - k)) * x T)
        = ∑ T, (johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)) from by
      apply Finset.sum_congr rfl
      intro T _
      ring]
    rw [← Finset.sum_div]
  rw [show (∑ S, (∑ T, johnsonNorm n k S T * x T)^2)
      = ∑ S, ((∑ T, johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)))^2 from by
    apply Finset.sum_congr rfl
    intro S _
    rw [hpt S]]
  have hfac : (∑ S, ((∑ T, johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)))^2)
      = (1 / ((k : ℝ) * ((n : ℝ) - k)))^2
        * (∑ S, (∑ T, johnsonW S T * x T)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow]
    ring
  calc (∑ S, ((∑ T, johnsonW S T * x T) / ((k : ℝ) * ((n : ℝ) - k)))^2)
      = (1 / ((k : ℝ) * ((n : ℝ) - k)))^2
        * (∑ S, (∑ T, johnsonW S T * x T)^2) := hfac
    _ ≤ (1 / ((k : ℝ) * ((n : ℝ) - k)))^2
        * ((((k : ℝ) - 1) * ((n : ℝ) - k))^2 * (∑ S, (x S)^2)) := by
        apply mul_le_mul_of_nonneg_left hraw
        exact sq_nonneg _
    _ = (((k : ℝ) - 1) / (k : ℝ))^2 * (∑ S, (x S)^2) := by
        rw [← mul_assoc, hkey]

/-- For `k ≥ 2` and `2*k ≤ n`, expresses the normalized Johnson contraction bound with factor
`(1-1/k)^2`. -/
theorem johnsonNorm_contract' {n k : ℕ} (hk2 : 2 ≤ k) (hkn : 2 * k ≤ n)
    (x : JohnsonVertex n k → ℝ) (hx : ∑ S, x S = 0) :
    (∑ S, (∑ T, johnsonNorm n k S T * x T)^2)
      ≤ (1 - 1 / (k : ℝ))^2 * (∑ S, (x S)^2) := by
  have h := johnsonNorm_contract hk2 hkn x hx
  have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have heq : (1 - 1 / (k : ℝ)) = ((k : ℝ) - 1) / (k : ℝ) := by
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt h1
    field_simp
  rw [heq]
  exact h

/-- The Johnson-chain matrix equals the normalized Johnson adjacency matrix; see [Tani2009]. -/
theorem johnsonChain_eq_johnsonNorm {n k : ℕ} :
    johnsonChain n k = johnsonNorm n k := by
  funext a b
  by_cases h : (a.1 \ b.1).card = 1
  · simp [johnsonChain, johnsonNorm, johnsonW, johnsonAdj, h, one_div]
  · simp [johnsonChain, johnsonNorm, johnsonW, johnsonAdj, h]

/-- For `k ≥ 2` and `2*k ≤ n`, the Johnson chain satisfies `SpectralGapAtLeast` with parameter
`1/k`, providing the gap estimate used in [Tani2009]. -/
theorem johnsonChain_spectralGap {n k : ℕ} (hk2 : 2 ≤ k) (hkn : 2 * k ≤ n) :
    SpectralGapAtLeast (johnsonChain n k) (1 / (k : ℝ)) := by
  have hkn' : k ≤ n := by omega
  have hk0 : 0 < k := by omega
  have hklt : k < n := by omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    rw [johnsonChain_eq_johnsonNorm]
    exact johnsonNorm_nonneg hkn' a b
  · intro a
    rw [johnsonChain_eq_johnsonNorm]
    exact johnsonNorm_rowsum hk0 hklt a
  · intro a b
    rw [johnsonChain_eq_johnsonNorm]
    exact johnsonNorm_symm a b
  · intro v hv
    simp only [sqNorm]
    rw [johnsonChain_eq_johnsonNorm]
    exact johnsonNorm_contract' hk2 hkn v hv

end Qatlib.Papers.ClawFinding07.MainResults.Spectral
