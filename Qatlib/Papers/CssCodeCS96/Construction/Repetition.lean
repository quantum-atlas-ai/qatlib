/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.CssBuild.Classical
import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# The classical repetition code as a bounded consumer

The length-`n+1` repetition code is the simplest classical consumer of the
shared linear-code component: exact parameters `[n+1, 1, n+1]`, a majority
decoder correct for every error weight `t` with `2 * t < n + 1`, and an
explicit tie rule (ties pick the zero-seeded candidate).
-/

namespace Qatlib.Papers.CssCodeCS96.Construction

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix

/-- Every element of the binary field is zero or one. -/
theorem zmod2_eq01 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h01 : ZMod.val a = 0 ∨ ZMod.val a = 1 := by omega
  rcases h01 with h | h
  · have hval : ZMod.val a = ZMod.val (0 : ZMod 2) := by
      rw [ZMod.val_zero]; exact h
    exact Or.inl (ZMod.val_injective 2 hval)
  · have hval : ZMod.val a = ZMod.val (1 : ZMod 2) := by
      rw [ZMod.val_one]; exact h
    exact Or.inr (ZMod.val_injective 2 hval)

/-- Doubling is zero in the binary field. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_eq01 a with h | h <;> rw [h] <;> decide

/-- Two binary elements summing to zero are equal. -/
theorem zmod2_eq_of {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rcases zmod2_eq01 a with ha | ha <;> rcases zmod2_eq01 b with hb | hb
  · rw [ha, hb]
  · rw [ha, hb] at h; exact absurd h (by decide)
  · rw [ha, hb] at h; exact absurd h (by decide)
  · rw [ha, hb]

/-- The all-ones word, generator of the repetition code. -/
def repOnes (n : ℕ) : Fin (n+1) → ZMod 2 := fun _ => 1

/-- Each repetition check adds an adjacent pair of coordinates. -/
def repH (n : ℕ) : Matrix (Fin n) (Fin (n+1)) (ZMod 2) :=
  Matrix.of fun i j =>
    if j = Fin.castSucc i then 1 else if j = Fin.succ i then 1 else 0

/-- The length-`n+1` repetition code as a shared-component consumer. -/
def repCode (n : ℕ) : ClCode (Fin (n+1)) (Fin n) where
  h := repH n

/-- The parity-check rows evaluate as adjacent coordinate sums. -/
theorem repH_mulVec (n : ℕ) (v : Fin (n+1) → ZMod 2) (i : Fin n) :
    (repH n *ᵥ v) i = v (Fin.castSucc i) + v (Fin.succ i) := by
  have hsplit : ∀ j : Fin (n+1), ((if j = Fin.castSucc i then (1 : ZMod 2)
      else if j = Fin.succ i then 1 else 0) * v j)
      = ((if j = Fin.castSucc i then v j else 0)
      + if j = Fin.succ i then v j else 0) := by
    intro j
    by_cases h1 : j = Fin.castSucc i
    · subst h1
      have hne : (Fin.castSucc i : Fin (n+1)) ≠ Fin.succ i := by
        simp [Fin.ext_iff]
      simp [hne]
    · by_cases h2 : j = Fin.succ i
      · subst h2
        simp [h1]
      · simp [h1, h2]
  simp only [Matrix.mulVec, dotProduct, repH, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (Fin.castSucc i) v,
    Finset.sum_ite_eq' Finset.univ (Fin.succ i) v]
  simp

/-- Any vector annihilated by the checks is constant across coordinates. -/
theorem repH_const (n : ℕ) {v : Fin (n+1) → ZMod 2} (h : repH n *ᵥ v = 0) :
    ∀ k : ℕ, ∀ hk : k < n + 1, v ⟨k, hk⟩ = v ⟨0, by omega⟩ := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    have hstep : v ⟨k, by omega⟩ + v ⟨k+1, hk⟩ = 0 := by
      have hfun := congrFun h ⟨k, by omega⟩
      simp only [repH_mulVec, Pi.zero_apply] at hfun
      exact hfun
    rw [(zmod2_eq_of hstep).symm, ih (by omega)]

/-- Every repetition codeword is a multiple of the all-ones word. -/
theorem rep_words_mem (n : ℕ) {v : Fin (n+1) → ZMod 2} (hv : v ∈ codeWords (repCode n)) :
    ∃ b : ZMod 2, v = b • repOnes n := by
  refine ⟨v ⟨0, by omega⟩, funext fun j => ?_⟩
  have h := repH_const n ((mem_words _ _).mp hv) (j : ℕ) j.isLt
  simp only [repOnes, Pi.smul_apply, smul_eq_mul, mul_one]
  exact h

/-- The all-ones word is a nonzero codeword of every repetition code. -/
theorem rep_ones_mem (n : ℕ) : repOnes n ∈ codeWords (repCode n) ∧ repOnes n ≠ 0 := by
  constructor
  · refine (mem_words _ _).mpr (funext fun i => ?_)
    show (repH n *ᵥ repOnes n) i = (0 : Fin n → ZMod 2) i
    rw [repH_mulVec]
    simp only [repOnes, Pi.zero_apply]
    exact zmod2_add_self _
  · intro h
    have hfun := congrFun h ⟨0, by omega⟩
    simp [repOnes] at hfun

/-- The repetition codeword space is the span of the all-ones word. -/
theorem rep_span (n : ℕ) :
    codeWords (repCode n) = Submodule.span (ZMod 2) {repOnes n} := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨b, hb⟩ := rep_words_mem n hv
    rw [hb]
    exact Submodule.mem_span_singleton.mpr ⟨b, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl : x = repOnes n)
    exact (rep_ones_mem n).1

/-- The all-ones word has full support. -/
theorem rep_ones_wt (n : ℕ) : bitWeight (repOnes n) = n + 1 := by
  have hfilter : Finset.univ.filter (fun i => repOnes n i ≠ 0) = Finset.univ := by
    ext i
    simp [repOnes]
  simp only [bitWeight]
  rw [hfilter]
  simp

/-- The repetition code has exact parameters `[n+1, 1, n+1]`. -/
theorem rep_params (n : ℕ) :
    Fintype.card (Fin (n+1)) = n + 1 ∧ codeDim (repCode n) = 1
      ∧ minDist (repCode n) = ((n+1 : ℕ) : ℕ∞) := by
  refine ⟨by simp, ?_, ?_⟩
  · unfold codeDim
    rw [rep_span]
    exact finrank_span_singleton (rep_ones_mem n).2
  · refine dist_eq (repCode n) (n+1) (rep_ones_mem n).1 (rep_ones_mem n).2
      (rep_ones_wt n) ?_
    intro v hv hne
    obtain ⟨b, hb⟩ := rep_words_mem n hv
    have hb1 : b = 1 := by
      rcases zmod2_eq01 b with h | h
      · exfalso
        apply hne
        rw [hb, h]
        simp
      · exact h
    rw [hb, hb1, one_smul, rep_ones_wt]

/-- Pad a syndrome to all of `ℕ` by zeros above the block length. -/
def repPad (n : ℕ) (s : Fin n → ZMod 2) (k : ℕ) : ZMod 2 :=
  if h : k < n then s ⟨k, h⟩ else 0

/-- Below the block length the padded syndrome agrees with the original. -/
theorem repPad_lt (n : ℕ) (s : Fin n → ZMod 2) (k : ℕ) (hk : k < n) :
    repPad n s k = s ⟨k, hk⟩ := by
  show (if h : k < n then s ⟨k, h⟩ else 0) = s ⟨k, hk⟩
  split
  · rfl
  · next h => exact absurd hk h

/-- The zero-seeded candidate error for a syndrome, built by prefix sums. -/
def repCand (n : ℕ) (s : Fin n → ZMod 2) : Fin (n+1) → ZMod 2 :=
  fun j => ∑ k ∈ Finset.range (j : ℕ), repPad n s k

/-- The candidate satisfies exactly the given syndrome. -/
theorem repCand_syn (n : ℕ) (s : Fin n → ZMod 2) : repH n *ᵥ repCand n s = s := by
  funext i
  rw [repH_mulVec]
  have hstep : repCand n s (Fin.succ i) = repCand n s (Fin.castSucc i) + s i := by
    simp only [repCand, Fin.val_succ, Fin.val_castSucc, Finset.sum_range_succ]
    rw [repPad_lt n s (i : ℕ) i.isLt]
  rw [hstep, ← add_assoc, zmod2_add_self, zero_add]

/-- The all-ones word is self-inverse. -/
theorem rep_ones_flip (n : ℕ) : repOnes n + repOnes n = 0 := by
  funext i
  exact zmod2_add_self _

/-- Two vectors with equal syndrome differ by zero or the ones word. -/
theorem rep_syn_eq (n : ℕ) {x y : Fin (n+1) → ZMod 2} (h : repH n *ᵥ x = repH n *ᵥ y) :
    x = y ∨ x = y + repOnes n := by
  have hmem : x + y ∈ codeWords (repCode n) := by
    refine (mem_words _ _).mpr (funext fun i => ?_)
    show (repH n *ᵥ (x + y)) i = (0 : Fin n → ZMod 2) i
    simp only [Matrix.mulVec_add, Pi.add_apply, Pi.zero_apply]
    rw [congrFun h i, zmod2_add_self]
  rw [rep_span] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  rcases zmod2_eq01 c with hc0 | hc0
  · left
    have hzero : x + y = 0 := by rw [← hc, hc0]; simp
    funext i
    have hi := congrFun hzero i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    exact zmod2_eq_of hi
  · right
    have hones : x + y = repOnes n := by rw [← hc, hc0]; simp
    funext i
    simp only [Pi.add_apply, repOnes]
    have hi := congrFun hones i
    simp only [Pi.add_apply, repOnes] at hi
    have hxi : x i = 1 + y i := by
      calc x i = x i + (y i + y i) := by rw [zmod2_add_self, add_zero]
        _ = (x i + y i) + y i := (add_assoc _ _ _).symm
        _ = 1 + y i := by rw [hi]
    rw [hxi, add_comm]

/-- Flipping every coordinate complements the weight. -/
theorem weight_flip (n : ℕ) (v : Fin (n+1) → ZMod 2) :
    bitWeight (v + repOnes n) = n + 1 - bitWeight v := by
  have hne : ∀ i : Fin (n+1), (v i + (1 : ZMod 2) ≠ 0) = (v i = 0) := by
    intro i
    rcases zmod2_eq01 (v i) with h | h <;> rw [h] <;> decide
  have hunion : (Finset.univ.filter fun i => v i + (1 : ZMod 2) ≠ 0) ∪
      (Finset.univ.filter fun i => v i ≠ 0) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    rcases zmod2_eq01 (v i) with h | h
    · left
      rw [h]
      decide
    · right
      rw [h]
      decide
  have hdisj : Disjoint (Finset.univ.filter fun i => v i + (1 : ZMod 2) ≠ 0)
      (Finset.univ.filter fun i => v i ≠ 0) := by
    refine Finset.disjoint_left.mpr fun i hi hi2 => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi2
    rcases zmod2_eq01 (v i) with h | h
    · exact absurd h hi2
    · rw [h] at hi
      exact absurd hi (by decide)
  have hcard : (Finset.univ.filter fun i => v i = 0).card
      + (Finset.univ.filter fun i => v i ≠ 0).card = n + 1 := by
    have h2 := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h2
    simp only [hne] at h2
    omega
  simp only [bitWeight, Pi.add_apply, repOnes, hne]
  omega

/-- Majority decode: take the lighter of the two syndrome candidates. -/
def repDecode (n : ℕ) : (Fin n → ZMod 2) → (Fin (n+1) → ZMod 2) :=
  fun s => if bitWeight (repCand n s) ≤ bitWeight (repCand n s + repOnes n)
    then repCand n s else repCand n s + repOnes n

/-- Majority decoding corrects every error below half the block length.
Ties pick the zero-seeded candidate; correctable errors never tie because
one candidate weighs strictly less than half the block. -/
theorem rep_correct (n t : ℕ) (ht : 2 * t < n + 1) :
    BoundDecode (repCode n) (repDecode n) t := by
  intro e he
  have h2 : 2 * bitWeight e < n + 1 := by omega
  obtain hcand | hcand := rep_syn_eq n
    ((repCand_syn n (repH n *ᵥ e)).symm)
  · have hw : bitWeight (repCand n (repH n *ᵥ e)) ≤
        bitWeight (repCand n (repH n *ᵥ e) + repOnes n) := by
      rw [← hcand, weight_flip]
      omega
    show (repDecode n (repH n *ᵥ e)) = e
    simp only [repDecode]
    split
    · exact hcand.symm
    · rename_i hcond
      exact absurd hw hcond
  · have hce : repCand n (repH n *ᵥ e) = e + repOnes n := by
      calc repCand n (repH n *ᵥ e)
          = (repCand n (repH n *ᵥ e) + repOnes n) + repOnes n := by
            rw [add_assoc, rep_ones_flip, add_zero]
        _ = e + repOnes n := by rw [← hcand]
    have hw : ¬(bitWeight (repCand n (repH n *ᵥ e))
        ≤ bitWeight (repCand n (repH n *ᵥ e) + repOnes n)) := by
      rw [hce, add_assoc, rep_ones_flip, add_zero, weight_flip]
      omega
    show (repDecode n (repH n *ᵥ e)) = e
    simp only [repDecode]
    split
    · rename_i hcond
      exact absurd hcond hw
    · exact hcand.symm

end Qatlib.Papers.CssCodeCS96.Construction
