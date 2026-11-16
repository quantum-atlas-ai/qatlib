/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StarDecompSim10.ForestColors.WidthRounds
public import Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition.SourceForestDecomposition

@[expose] public section

/-! # Preserved closed source mathematics with the full recurrence proved

Fixed1003.3683v2. Algebra and finite ancestor locality are certified;
no coherent quantum simulator or precision/runtime bridge is asserted.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.StarDecompSim10.ForestColors.WidthSupport
open Finset
open scoped BigOperators
open Qatlib.Papers.StarDecompSim10.MainResults.ForestDecomposition
open Qatlib.Papers.StarDecompSim10.ForestColors
open Qatlib.Papers.StarDecompSim10.ForestColors.WidthRounds
variable {N d : ℕ}

/-- A genuinely set most-significant bit bounds the integer below by its power of two. -/
theorem msbPower (n : ℕ) (hn : n≠0) : 2^msb n ≤ n := by
  by_contra h
  have hf := Nat.testBit_lt_two_pow (Nat.lt_of_not_ge h)
  rw [msbBit n hn] at hf
  contradiction

/-- Preserved complete msb_above_false mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem msbAbove (n : ℕ) (h : n ≠ 0) {j : ℕ} (hj : msb n < j) :
    n.testBit j = false := by
  unfold msb at hj
  rw [dite_eq_right h] at hj
  exact (Classical.choose_spec (Nat.exists_most_significant_bit h)).2 j hj

/-- Preserved complete BelowBits mathematics or explicit conditional locality; no source quantum program is certified. -/
def BelowBits (L : ℕ) (κ : Fin N → ℕ) : Prop := ∀ v, κ v < 2 ^ L

/-- Preserved complete nextBits_pos mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem nextPositive (L : ℕ) : 0 < nextBits L := by
  unfold nextBits; omega

/-- Preserved complete refineVal_lt_nextBits mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem refineWidth (parent : Fin N → Option (Fin N)) {L : ℕ}
    {κ : Fin N → ℕ} (hκ : BelowBits L κ) (v : Fin N) :
    refineVal parent κ v < 2 ^ nextBits L := by
  unfold refineVal
  cases h : parent v with
  | none =>
      change bitVal (κ v) 0 < 2 ^ nextBits L
      have hb : bitVal (κ v) 0 < 2 := bitLtTwo _ _
      have hpow : 2 ≤ 2 ^ nextBits L := by
        have hpos := nextPositive L
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ nextBits L := Nat.pow_le_pow_right (by norm_num) hpos
      omega
  | some p =>
      change 2 * topDiff (κ v) (κ p) + bitVal (κ v) (topDiff (κ v) (κ p)) < 2 ^ nextBits L
      set k := topDiff (κ v) (κ p) with hkdef
      by_cases hx0 : κ v ^^^ κ p = 0
      · have hk0 : k = 0 := by simp [hkdef, topDiff, msb, hx0]
        have hb0 : bitVal (κ v) 0 < 2 := bitLtTwo _ _
        have hpow : 2 ≤ 2 ^ nextBits L := by
          have hpos := nextPositive L
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ nextBits L := Nat.pow_le_pow_right (by norm_num) hpos
        rw [hk0]
        omega
      · have hvx : κ v < 2 ^ L := hκ v
        have hpx : κ p < 2 ^ L := hκ p
        have hxorlt : (κ v ^^^ κ p) < 2 ^ L := Nat.xor_lt_two_pow hvx hpx
        have hbound : 2 ^ k ≤ κ v ^^^ κ p := by
          exact msbPower _ hx0
        have hkL : k < L := by
          by_contra hnot
          have hge : L ≤ k := le_of_not_gt hnot
          have hmono : 2 ^ L ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
          omega
        have hk_le : k ≤ L - 1 := by omega
        have hb : bitVal (κ v) k < 2 := bitLtTwo _ _
        have hval : 2 * k + bitVal (κ v) k ≤ 2 * L - 1 := by omega
        have hxpos : 2 * L - 1 ≠ 0 := by omega
        have hlt : 2 * L - 1 < 2 ^ nextBits L := by
          unfold nextBits
          exact ((Nat.log2_eq_iff hxpos).mp rfl).2
        omega

/-! ## Iterating the refinement -/

/-- Preserved complete colorAt_belowBits mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem colorWidth (parent : Fin N → Option (Fin N)) :
    ∀ j, BelowBits (Nat.iterate nextBits j (Nat.log2 N + 1)) (colorAt parent j) := by
  intro j
  induction j with
  | zero =>
      intro v
      simp only [colorAt]
      show v.val < 2 ^ Nat.iterate nextBits 0 (Nat.log2 N + 1)
      rw [Function.iterate_zero]
      change v.val < 2 ^ (Nat.log2 N + 1)
      have h1 : v.val < N := v.isLt
      have h2 : N < 2 ^ (Nat.log2 N + 1) := by
        by_cases hN : N = 0
        · subst hN; simp
        · exact ((Nat.log2_eq_iff hN).mp rfl).2
      omega
  | succ j ih =>
      intro v
      have hstep : Nat.iterate nextBits (j + 1) (Nat.log2 N + 1) =
          nextBits (Nat.iterate nextBits j (Nat.log2 N + 1)) := by
        rw [Function.iterate_succ_apply']
      rw [hstep]
      exact refineWidth parent ih v

/-- Preserved complete refineVal_lt_six mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem refineSix (parent : Fin N → Option (Fin N)) {κ : Fin N → ℕ}
    (hκ : BelowBits 3 κ) (v : Fin N) : refineVal parent κ v < 6 := by
  unfold refineVal
  cases h : parent v with
  | none =>
      change bitVal (κ v) 0 < 6
      have := bitLtTwo (κ v) 0
      omega
  | some p =>
      change 2 * topDiff (κ v) (κ p) + bitVal (κ v) (topDiff (κ v) (κ p)) < 6
      by_cases hx0 : κ v ^^^ κ p = 0
      · have hk0 : topDiff (κ v) (κ p) = 0 := by simp [topDiff, msb, hx0]
        have := bitLtTwo (κ v) 0
        rw [hk0]
        omega
      · have hvx : κ v < 2 ^ 3 := hκ v
        have hpx : κ p < 2 ^ 3 := hκ p
        have hxorlt : (κ v ^^^ κ p) < 2 ^ 3 := Nat.xor_lt_two_pow hvx hpx
        have hbound : 2 ^ topDiff (κ v) (κ p) ≤ κ v ^^^ κ p := by
          exact msbPower _ hx0
        have hkL : topDiff (κ v) (κ p) < 3 := by
          by_contra hnot
          have hge : 3 ≤ topDiff (κ v) (κ p) := le_of_not_gt hnot
          have hmono : 2 ^ 3 ≤ 2 ^ topDiff (κ v) (κ p) :=
            Nat.pow_le_pow_right (by norm_num) hge
          omega
        have := bitLtTwo (κ v) (topDiff (κ v) (κ p))
        omega

/-- Preserved complete colorAt_logStar_belowBits mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem threeBits (parent : Fin N → Option (Fin N)) :
    BelowBits 3 (colorAt parent (logStar N)) := by
  have h := colorWidth parent (logStar N)
  intro v
  have hv := h v
  have hle := wholeOriginal N
  have : (2 : ℕ) ^ Nat.iterate nextBits (logStar N) (Nat.log2 N + 1) ≤ 2 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) hle
  omega

/-- Preserved complete colorAt_logStar_succ_lt_six mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem sixColors (parent : Fin N → Option (Fin N)) (v : Fin N) :
    colorAt parent (logStar N + 1) v < 6 := by
  have h3 : BelowBits 3 (colorAt parent (logStar N)) := threeBits parent
  have hstep : colorAt parent (logStar N + 1) v =
      refineVal parent (colorAt parent (logStar N)) v := rfl
  rw [hstep]
  exact refineSix parent h3 v

/-! ## Query locality: only the ancestor chain is read -/

/-- Preserved complete reach_mono mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem reachMono (parent : Fin N → Option (Fin N)) :
    ∀ (v : Fin N) {i j : ℕ}, i ≤ j → reach parent i v ⊆ reach parent j v := by
  intro v i j hij
  induction j generalizing i v with
  | zero =>
      have h0 : i = 0 := by omega
      subst h0
      exact Finset.Subset.refl _
  | succ j ih =>
      by_cases hji : i = j + 1
      · subst hji
        exact Finset.Subset.refl _
      · have hij' : i ≤ j := by omega
        cases i with
        | zero => simp [reach]
        | succ i =>
            cases h : parent v with
            | none =>
                have hnone : reach parent (j + 1) v = {v} := by simp [reach, h]
                have hnone' : reach parent (i + 1) v = {v} := by simp [reach, h]
                rw [hnone', hnone]
            | some p =>
                simp only [reach, h]
                exact Finset.insert_subset_insert v (ih (v := p) (i := i) (by omega))

/-- Preserved complete colorAt_congr mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem colorCongr {parent parent' : Fin N → Option (Fin N)} (j : ℕ) (v : Fin N)
    (h : ∀ u ∈ reach parent j v, parent' u = parent u) :
    colorAt parent' j v = colorAt parent j v := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
      have hv_mem : v ∈ reach parent (j + 1) v := by simp [reach]
      have hv : parent' v = parent v := h v hv_mem
      have hstep' : colorAt parent' (j + 1) v = refineVal parent' (colorAt parent' j) v := rfl
      have hstep : colorAt parent (j + 1) v = refineVal parent (colorAt parent j) v := rfl
      rw [hstep', hstep]
      unfold refineVal
      rw [hv]
      cases hp : parent v with
      | none =>
          -- the whole chain collapses to `v`
          have hvsub : reach parent j v ⊆ reach parent (j + 1) v :=
            reachMono parent v (by omega)
          have h' : ∀ u ∈ reach parent j v, parent' u = parent u :=
            fun u hu => h u (hvsub hu)
          change bitVal (colorAt parent' j v) 0 = bitVal (colorAt parent j v) 0
          rw [ih v h']
      | some p =>
          have hsubj : reach parent j v ⊆ reach parent (j + 1) v :=
            reachMono parent v (by omega)
          have hsubp : reach parent j p ⊆ reach parent (j + 1) v := by
            intro u hu
            simp only [reach, hp]
            exact Finset.mem_insert_of_mem hu
          have h'v : ∀ u ∈ reach parent j v, parent' u = parent u :=
            fun u hu => h u (hsubj hu)
          have h'p : ∀ u ∈ reach parent j p, parent' u = parent u :=
            fun u hu => h u (hsubp hu)
          change 2 * topDiff (colorAt parent' j v) (colorAt parent' j p) +
              bitVal (colorAt parent' j v) (topDiff (colorAt parent' j v) (colorAt parent' j p)) =
            2 * topDiff (colorAt parent j v) (colorAt parent j p) +
              bitVal (colorAt parent j v) (topDiff (colorAt parent j v) (colorAt parent j p))
          rw [ih v h'v, ih p h'p]

/-! ## Lemma 2, bundled -/

/-- Preserved complete vertex_coloring_six mathematics or explicit conditional locality; no source quantum program is certified. -/
theorem fullColoring {parent : Fin N → Option (Fin N)}
    (hpar : ∀ v w, parent v = some w → w < v) :
    ∃ χ : Fin N → Fin 6,
      (∀ v w, parent v = some w → χ v ≠ χ w) ∧
      (∀ v, (χ v).val = colorAt parent (logStar N + 1) v) ∧
      (∀ v, (reach parent (logStar N + 1) v).card ≤ logStar N + 2) ∧
      (∀ (parent' : Fin N → Option (Fin N)) (v : Fin N),
        (∀ u ∈ reach parent (logStar N + 1) v, parent' u = parent u) →
          colorAt parent' (logStar N + 1) v = colorAt parent (logStar N + 1) v) := by
  refine ⟨fun v => ⟨colorAt parent (logStar N + 1) v, sixColors parent v⟩,
    ?_, ?_, ?_⟩
  · intro v w hvw heq
    exact colorProper hpar (logStar N + 1) v w hvw (congrArg Fin.val heq)
  · intro v; rfl
  · refine ⟨fun v => reachBound parent (logStar N + 1) v, ?_⟩
    intro parent' v h
    exact colorCongr (logStar N + 1) v h

end Qatlib.Papers.StarDecompSim10.ForestColors.WidthSupport
