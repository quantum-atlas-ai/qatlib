/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Papers.WeighMatrix00.MainResults.SLSLegendre
import Qatlib.Papers.WeighMatrix00.MainResults.Lemma3SLSLowerBound
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def sPlus (S : Finset F) (i : F) : Finset F :=
  S.filter (fun j => quadraticChar F (i + j) = 1)

def sMinus (S : Finset F) (i : F) : Finset F :=
  S.filter (fun j => quadraticChar F (i + j) = -1)

def sZero (S : Finset F) (i : F) : Finset F :=
  S.filter (fun j => quadraticChar F (i + j) = 0)

def wVec (S : Finset F) (i : F) : ℤ :=
  S.sum (fun j => quadraticChar F (i + j))

theorem wVec_eq_card_diff (S : Finset F) (i : F) :
    wVec S i = ((sPlus S i).card : ℤ) - ((sMinus S i).card : ℤ) := by
  have hterm : ∀ j : F, quadraticChar F (i + j) =
      (if quadraticChar F (i + j) = 1 then (1 : ℤ) else 0) -
        (if quadraticChar F (i + j) = -1 then (1 : ℤ) else 0) := by
    intro j
    by_cases h0 : i + j = 0
    · rw [h0, quadraticChar_zero]
      simp
    · rcases quadraticChar_dichotomy h0 with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
  have h1 : S.sum (fun j => (if quadraticChar F (i + j) = 1 then (1 : ℤ) else 0)) =
      ((sPlus S i).card : ℤ) := by
    rw [sPlus, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have h2 : S.sum (fun j => (if quadraticChar F (i + j) = -1 then (1 : ℤ) else 0)) =
      ((sMinus S i).card : ℤ) := by
    rw [sMinus, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc wVec S i
      = S.sum (fun j => (if quadraticChar F (i + j) = 1 then (1 : ℤ) else 0) -
          (if quadraticChar F (i + j) = -1 then (1 : ℤ) else 0)) := by
        rw [wVec]
        exact Finset.sum_congr rfl (fun j _ => hterm j)
    _ = S.sum (fun j => (if quadraticChar F (i + j) = 1 then (1 : ℤ) else 0)) -
          S.sum (fun j => (if quadraticChar F (i + j) = -1 then (1 : ℤ) else 0)) := by
        rw [Finset.sum_sub_distrib]
    _ = ((sPlus S i).card : ℤ) - ((sMinus S i).card : ℤ) := by rw [h1, h2]

theorem card_partition (S : Finset F) (i : F) :
    (sPlus S i).card + (sMinus S i).card + (sZero S i).card = S.card := by
  have hterm : ∀ j ∈ S,
      (if quadraticChar F (i + j) = 1 then (1 : ℕ) else 0) +
        (if quadraticChar F (i + j) = -1 then (1 : ℕ) else 0) +
        (if quadraticChar F (i + j) = 0 then (1 : ℕ) else 0) = 1 := by
    intro j _
    by_cases h0 : i + j = 0
    · rw [h0, quadraticChar_zero]
      simp
    · rcases quadraticChar_dichotomy h0 with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  rw [← Finset.card_filter (p := fun j : F => quadraticChar F (i + j) = 1),
    ← Finset.card_filter (p := fun j : F => quadraticChar F (i + j) = -1),
    ← Finset.card_filter (p := fun j : F => quadraticChar F (i + j) = 0)] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  simpa [sPlus, sMinus, sZero] using hsum

theorem sum_wVec_sq (hF : ringChar F ≠ 2) (S : Finset F) :
    ∑ i : F, (wVec S i) ^ 2 =
      (Fintype.card F : ℤ) * (S.card : ℤ) - (S.card : ℤ) ^ 2 := by
  have hexp : ∀ i : F, (wVec S i) ^ 2 =
      S.sum (fun j => S.sum (fun k => quadraticChar F (i + j) * quadraticChar F (i + k))) := by
    intro i
    rw [wVec, pow_two, Finset.sum_mul_sum]
  have hgram : ∀ j k : F,
      (∑ i : F, quadraticChar F (i + j) * quadraticChar F (i + k)) =
      if j = k then (Fintype.card F : ℤ) - 1 else -1 := by
    intro j k
    simpa [mul_comm] using fact5_nearOrthogonality hF j k
  have hinner : ∀ j ∈ S,
      S.sum (fun k => (if j = k then (Fintype.card F : ℤ) - 1 else -1)) =
      (Fintype.card F : ℤ) - (S.card : ℤ) := by
    intro j hj
    have hstep : S.sum (fun k => (if j = k then (Fintype.card F : ℤ) - 1 else -1)) =
        S.sum (fun k => (-1 : ℤ) + (if j = k then (Fintype.card F : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : j = k
      · subst h; simp; ring
      · simp [h]
    rw [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq, if_pos hj,
      nsmul_eq_mul]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hmain : (∑ j ∈ S, ∑ i : F, ∑ k ∈ S,
      quadraticChar F (i + j) * quadraticChar F (i + k)) =
      S.sum (fun _ => (Fintype.card F : ℤ) - (S.card : ℤ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm, ← hinner j hj]
    apply Finset.sum_congr rfl
    intro k _
    exact hgram j k
  rw [hmain, Finset.sum_const, nsmul_eq_mul]
  ring

theorem exists_shrinking_index (hF : ringChar F ≠ 2) (S : Finset F) (hS : 4 ≤ S.card) :
    ∃ i : F, 4 * (sPlus S i).card < 3 * S.card ∧
      4 * (sMinus S i).card < 3 * S.card ∧
      4 * (sZero S i).card < 3 * S.card := by
  haveI : Nonempty F := ⟨0⟩
  have hq : (0 : ℤ) < (Fintype.card F : ℤ) := by
    exact_mod_cast Fintype.card_pos
  have hSpos : (0 : ℤ) < (S.card : ℤ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hS)
  have hSge : (4 : ℤ) ≤ (S.card : ℤ) := by exact_mod_cast hS

  have hex : ∃ i : F, 4 * (wVec S i) ^ 2 < (S.card : ℤ) ^ 2 := by
    by_contra h
    push_neg at h
    have hle : ∑ i : F, (S.card : ℤ) ^ 2 ≤ ∑ i : F, 4 * (wVec S i) ^ 2 :=
      Finset.sum_le_sum (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
    have hsum4 : (∑ i : F, 4 * (wVec S i) ^ 2) = 4 * ∑ i : F, (wVec S i) ^ 2 := by
      rw [Finset.mul_sum]
    rw [hsum4, sum_wVec_sq hF S] at hle

    have hSsq : 4 * (S.card : ℤ) ≤ (S.card : ℤ) * (S.card : ℤ) := by
      have h : (0 : ℤ) ≤ ((S.card : ℤ) - 4) * (S.card : ℤ) :=
        mul_nonneg (by linarith) (le_of_lt hSpos)
      nlinarith
    have hfac : (0 : ℤ) ≤ (Fintype.card F : ℤ) + 4 := by linarith
    have hprod : 4 * (S.card : ℤ) * ((Fintype.card F : ℤ) + 4) ≤
        (S.card : ℤ) * (S.card : ℤ) * ((Fintype.card F : ℤ) + 4) := by
      have := mul_le_mul_of_nonneg_right hSsq hfac
      simpa [mul_assoc] using this
    have hle' : (S.card : ℤ) * (S.card : ℤ) * ((Fintype.card F : ℤ) + 4) ≤
        4 * (Fintype.card F : ℤ) * (S.card : ℤ) := by nlinarith [hle]
    have h16 : (16 : ℤ) * (S.card : ℤ) ≤ 0 := by nlinarith [hprod, hle']
    nlinarith [h16, hSpos]
  obtain ⟨i, hi⟩ := hex

  have hw2 : 2 * |wVec S i| < (S.card : ℤ) := by
    have hsq : (2 * wVec S i) ^ 2 < (S.card : ℤ) ^ 2 := by nlinarith [hi]
    have habs : |2 * wVec S i| < |(S.card : ℤ)| := sq_lt_sq.mp hsq
    rwa [abs_mul, abs_two, abs_of_nonneg (le_of_lt hSpos)] at habs

  set N : ℤ := (S.card : ℤ) with hN
  set P : ℤ := ((sPlus S i).card : ℤ) with hP
  set M : ℤ := ((sMinus S i).card : ℤ) with hM
  set Z : ℤ := ((sZero S i).card : ℤ) with hZ
  have hpart : P + M + Z = N := by
    have hc := card_partition (F := F) S i
    have hcast : (((sPlus S i).card + (sMinus S i).card + (sZero S i).card : ℕ) : ℤ) =
        (S.card : ℤ) := by exact_mod_cast hc
    push_cast at hcast
    simpa [hP, hM, hZ, hN] using hcast
  have hw : wVec S i = P - M := by
    have hc := wVec_eq_card_diff (F := F) S i
    simpa [hP, hM] using hc
  have hZnn : (0 : ℤ) ≤ Z := by rw [hZ]; exact Int.natCast_nonneg _
  have h2abs : 2 * |wVec S i| < N := by rw [hN]; exact hw2
  have hPbound : 4 * P < 3 * N := by
    have hwle : wVec S i ≤ |wVec S i| := le_abs_self _
    nlinarith [hpart, hw, hZnn, hwle, h2abs]
  have hMbound : 4 * M < 3 * N := by
    have hwle : -wVec S i ≤ |wVec S i| := neg_le_abs _
    nlinarith [hpart, hw, hZnn, hwle, h2abs]
  have hZbound : 4 * Z < 3 * N := by
    have hZle : (sZero S i).card ≤ 1 := by
      rw [sZero]
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      have ha' : i + a = 0 := quadraticChar_eq_zero_iff.mp ha.2
      have hb' : i + b = 0 := quadraticChar_eq_zero_iff.mp hb.2
      have hab : a - b = 0 := by linear_combination ha' - hb'
      exact sub_eq_zero.mp hab
    have hZle' : Z ≤ 1 := by rw [hZ]; exact_mod_cast hZle
    have hNge : (4 : ℤ) ≤ N := by rw [hN]; exact hSge
    nlinarith
  refine ⟨i, ?_, ?_, ?_⟩
  · have h : 4 * ((sPlus S i).card : ℤ) < 3 * (S.card : ℤ) := by
      simpa [hP, hN] using hPbound
    exact_mod_cast h
  · have h : 4 * ((sMinus S i).card : ℤ) < 3 * (S.card : ℤ) := by
      simpa [hM, hN] using hMbound
    exact_mod_cast h
  · have h : 4 * ((sZero S i).card : ℤ) < 3 * (S.card : ℤ) := by
      simpa [hZ, hN] using hZbound
    exact_mod_cast h

def SLSTree.Solves (t : SLSTree F) : Prop := ∀ s : F, t.eval s = s

def SLSTree.SolvesOn (t : SLSTree F) (S : Finset F) : Prop := ∀ s ∈ S, t.eval s = s

noncomputable def shrinkIndex' (hF : ringChar F ≠ 2) (S : Finset F) : F :=
  if h : 4 ≤ S.card then (exists_shrinking_index hF S h).choose else 0

theorem shrinkIndex'_spec (hF : ringChar F ≠ 2) (S : Finset F) (h : 4 ≤ S.card) :
    4 * (sPlus S (shrinkIndex' hF S)).card < 3 * S.card ∧
      4 * (sMinus S (shrinkIndex' hF S)).card < 3 * S.card ∧
      4 * (sZero S (shrinkIndex' hF S)).card < 3 * S.card := by
  unfold shrinkIndex'
  rw [dif_pos h]
  exact (exists_shrinking_index hF S h).choose_spec

theorem shrink_card_bound {m n k : ℕ} (hm : 4 * m < 3 * n)
    (hn : n * 3 ^ (k + 1) ≤ 4 ^ (k + 2)) : m * 3 ^ k ≤ 4 ^ (k + 1) := by
  have h3 : 0 < 3 ^ k := pow_pos (by norm_num) k
  have step : 4 * (m * 3 ^ k) < 4 * 4 ^ (k + 1) := by
    have h1 : 4 * m * 3 ^ k < 3 * n * 3 ^ k := by nlinarith
    have h2 : 3 * n * 3 ^ k = n * 3 ^ (k + 1) := by rw [pow_succ]; ring
    have h3' : 4 ^ (k + 2) = 4 * 4 ^ (k + 1) := by rw [pow_succ]; ring
    calc 4 * (m * 3 ^ k) = 4 * m * 3 ^ k := by ring
      _ < 3 * n * 3 ^ k := h1
      _ = n * 3 ^ (k + 1) := h2
      _ ≤ 4 ^ (k + 2) := hn
      _ = 4 * 4 ^ (k + 1) := h3'
  nlinarith [step]

def bruteFuel : ℕ → Finset F → SLSTree F
  | 0, _ => SLSTree.leaf 0
  | k + 1, S =>
      if h : S.Nonempty then
        SLSTree.node (-h.choose) (bruteFuel k (sMinus S (-h.choose)))
          (bruteFuel k (sPlus S (-h.choose)))
      else SLSTree.leaf 0

theorem bruteFuel_solves :
    ∀ (k : ℕ) (S : Finset F), S.card ≤ k → (bruteFuel k S).SolvesOn S := by
  intro k
  induction k with
  | zero =>
    intro S h
    have hzero : S.card = 0 := Nat.le_zero.mp h
    have hempty : S = ∅ := Finset.card_eq_zero.mp hzero
    intro s hs
    rw [hempty] at hs
    exact absurd hs (Finset.notMem_empty s)
  | succ k ih =>
    intro S h
    by_cases hne : S.Nonempty
    · have hdef : bruteFuel (k + 1) S =
          SLSTree.node (-hne.choose) (bruteFuel k (sMinus S (-hne.choose)))
            (bruteFuel k (sPlus S (-hne.choose))) := by
        simp only [bruteFuel, dif_pos hne]
      have hmem : hne.choose ∈ S := hne.choose_spec
      intro s hs
      rw [hdef]
      by_cases hseq : s = hne.choose
      · subst hseq
        have hzero : quadraticChar F (-hne.choose + hne.choose) = 0 := by
          rw [neg_add_cancel, quadraticChar_zero]
        rw [SLSTree.eval_node_zero _ _ _ _ hzero]
        simp
      · have h0 : -hne.choose + s ≠ 0 := by
          intro hc
          exact hseq (by
            have h1 : -hne.choose = -s := add_eq_zero_iff_eq_neg.mp hc
            exact (neg_injective h1).symm)
        have hchi0 : quadraticChar F (-hne.choose + s) ≠ 0 :=
          fun hz => h0 (quadraticChar_eq_zero_iff.mp hz)
        rcases quadraticChar_dichotomy h0 with hone | hneg
        · rw [SLSTree.eval_node_plus _ _ _ _ hchi0 hone]
          refine ih (sPlus S (-hne.choose)) ?_ s (Finset.mem_filter.mpr ⟨hs, hone⟩)
          have hsub : sPlus S (-hne.choose) ⊆ S.erase hne.choose := by
            intro x hx
            simp only [sPlus, Finset.mem_filter] at hx
            rw [Finset.mem_erase]
            exact ⟨fun hxeq => by
              subst hxeq
              rw [neg_add_cancel, quadraticChar_zero] at hx
              exact absurd hx.2 (by norm_num), hx.1⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hmem] at hc
          omega
        · rw [SLSTree.eval_node_minus _ _ _ _ hchi0 (by rw [hneg]; norm_num)]
          refine ih (sMinus S (-hne.choose)) ?_ s (Finset.mem_filter.mpr ⟨hs, hneg⟩)
          have hsub : sMinus S (-hne.choose) ⊆ S.erase hne.choose := by
            intro x hx
            simp only [sMinus, Finset.mem_filter] at hx
            rw [Finset.mem_erase]
            exact ⟨fun hxeq => by
              subst hxeq
              rw [neg_add_cancel, quadraticChar_zero] at hx
              exact absurd hx.2 (by norm_num), hx.1⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hmem] at hc
          omega
    · have hempty : S = ∅ :=
        (Finset.not_nonempty_iff_eq_empty.mp hne)
      intro s hs
      rw [hempty] at hs
      exact absurd hs (Finset.notMem_empty s)

theorem bruteFuel_depth : ∀ (k : ℕ) (S : Finset F), (bruteFuel k S).depth ≤ k := by
  intro k
  induction k with
  | zero => intro S; simp [bruteFuel, SLSTree.depth]
  | succ k ih =>
    intro S
    by_cases hne : S.Nonempty
    · have hdef : bruteFuel (k + 1) S =
          SLSTree.node (-hne.choose) (bruteFuel k (sMinus S (-hne.choose)))
            (bruteFuel k (sPlus S (-hne.choose))) := by
        simp only [bruteFuel, dif_pos hne]
      rw [hdef, SLSTree.depth]
      have h1 := ih (sMinus S (-hne.choose))
      have h2 := ih (sPlus S (-hne.choose))
      omega
    · have hdef : bruteFuel (k + 1) S = SLSTree.leaf 0 := by
        simp only [bruteFuel, dif_neg hne]
      rw [hdef, SLSTree.depth]
      omega

def buildFuel (hF : ringChar F ≠ 2) : ℕ → Finset F → SLSTree F
  | 0, S => bruteFuel 4 S
  | k + 1, S =>
      if h4 : S.card ≤ 4 then bruteFuel 4 S
      else
        SLSTree.node (shrinkIndex' hF S) (buildFuel hF k (sMinus S (shrinkIndex' hF S)))
          (buildFuel hF k (sPlus S (shrinkIndex' hF S)))

theorem buildFuel_solves (hF : ringChar F ≠ 2) :
    ∀ (k : ℕ) (S : Finset F), S.card * 3 ^ k ≤ 4 ^ (k + 1) →
      (buildFuel hF k S).SolvesOn S := by
  intro k
  induction k with
  | zero =>
    intro S hcard
    have h4 : S.card ≤ 4 := by simpa using hcard
    simpa [buildFuel] using bruteFuel_solves 4 S (by omega)
  | succ k ih =>
    intro S hcard
    by_cases h4 : S.card ≤ 4
    · simpa [buildFuel, dif_pos h4] using bruteFuel_solves 4 S (by omega)
    · have hdef : buildFuel hF (k + 1) S =
          SLSTree.node (shrinkIndex' hF S) (buildFuel hF k (sMinus S (shrinkIndex' hF S)))
            (buildFuel hF k (sPlus S (shrinkIndex' hF S))) := by
        simp only [buildFuel, dif_neg h4]
      have hspec := shrinkIndex'_spec hF S (by omega)
      intro s hs
      rw [hdef]
      by_cases hzero : quadraticChar F (shrinkIndex' hF S + s) = 0
      · rw [SLSTree.eval_node_zero _ _ _ _ hzero]
        have hz : shrinkIndex' hF S + s = 0 := quadraticChar_eq_zero_iff.mp hzero
        have hs' : s = -shrinkIndex' hF S := by
          rw [eq_neg_iff_add_eq_zero]
          rwa [add_comm]
        exact hs'.symm
      · have hchi0 : quadraticChar F (shrinkIndex' hF S + s) ≠ 0 := hzero
        have h0 : shrinkIndex' hF S + s ≠ 0 := by
          intro hc
          exact hzero (by rw [hc, quadraticChar_zero])
        rcases quadraticChar_dichotomy h0 with hone | hneg
        · rw [SLSTree.eval_node_plus _ _ _ _ hchi0 hone]
          exact ih (sPlus S (shrinkIndex' hF S)) (shrink_card_bound hspec.1 hcard) s
            (Finset.mem_filter.mpr ⟨hs, hone⟩)
        · rw [SLSTree.eval_node_minus _ _ _ _ hchi0 (by rw [hneg]; norm_num)]
          exact ih (sMinus S (shrinkIndex' hF S)) (shrink_card_bound hspec.2.1 hcard) s
            (Finset.mem_filter.mpr ⟨hs, hneg⟩)

theorem buildFuel_depth (hF : ringChar F ≠ 2) :
    ∀ (k : ℕ) (S : Finset F), S.card * 3 ^ k ≤ 4 ^ (k + 1) →
      (buildFuel hF k S).depth ≤ k + 4 := by
  intro k
  induction k with
  | zero =>
    intro S hcard
    have h4 : S.card ≤ 4 := by simpa using hcard
    simpa [buildFuel] using bruteFuel_depth 4 S
  | succ k ih =>
    intro S hcard
    by_cases h4 : S.card ≤ 4
    · have hdef : buildFuel hF (k + 1) S = bruteFuel 4 S := by
        simp only [buildFuel, dif_pos h4]
      rw [hdef]
      have := bruteFuel_depth 4 S
      omega
    · have hdef : buildFuel hF (k + 1) S =
          SLSTree.node (shrinkIndex' hF S) (buildFuel hF k (sMinus S (shrinkIndex' hF S)))
            (buildFuel hF k (sPlus S (shrinkIndex' hF S))) := by
        simp only [buildFuel, dif_neg h4]
      have hspec := shrinkIndex'_spec hF S (by omega)
      rw [hdef, SLSTree.depth]
      have h1 := ih (sMinus S (shrinkIndex' hF S)) (shrink_card_bound hspec.2.1 hcard)
      have h2 := ih (sPlus S (shrinkIndex' hF S)) (shrink_card_bound hspec.1 hcard)
      omega

theorem source_lemma4_slsProtocol (hF : ringChar F ≠ 2) :
    ∃ t : SLSTree F, t.Solves ∧
      (t.depth : ℝ) ≤ Real.log (Fintype.card F : ℝ) / Real.log (4 / 3) + 3 := by
  haveI : Nonempty F := ⟨0⟩
  have hlog43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  by_cases hq4 : Fintype.card F ≤ 4
  · refine ⟨bruteFuel 4 (Finset.univ : Finset F),
      fun s => bruteFuel_solves 4 (Finset.univ : Finset F) (by simpa using hq4) s (Finset.mem_univ s), ?_⟩
    have hd : ((bruteFuel 4 (Finset.univ : Finset F)).depth : ℝ) ≤ 4 := by
      exact_mod_cast bruteFuel_depth 4 (Finset.univ : Finset F)
    have hq2 : (4 / 3 : ℝ) ≤ (Fintype.card F : ℝ) := by
      have h : 1 < Fintype.card F :=
        Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
      have h2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h
      linarith
    have hratio : (1 : ℝ) ≤ Real.log (Fintype.card F : ℝ) / Real.log (4 / 3 : ℝ) := by
      rw [le_div_iff₀ hlog43]
      linarith [Real.log_le_log (by norm_num : (0:ℝ) < 4/3) hq2]
    linarith
  · push_neg at hq4
    set q : ℕ := Fintype.card F with hqdef
    have hq5 : 5 ≤ q := hq4
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    set x : ℝ := (Real.log (q : ℝ) - Real.log 4) / Real.log (4 / 3) with hxdef
    set k : ℕ := Nat.ceil x with hkdef
    have hxpos : 0 ≤ x := by
      apply div_nonneg
      · have h4q : (4 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 4 < q)
        have := Real.log_lt_log (by norm_num : (0:ℝ) < 4) h4q
        linarith
      · exact le_of_lt hlog43

    have hxle : x ≤ (k : ℝ) := Nat.le_ceil x
    have hstep : Real.log (q : ℝ) - Real.log 4 ≤ (k : ℝ) * Real.log (4 / 3 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hxle (le_of_lt hlog43)
      rwa [hxdef, div_mul_cancel₀ _ (ne_of_gt hlog43)] at hmul
    have hlogkey : Real.log (q : ℝ) + (k : ℝ) * Real.log 3 ≤ ((k : ℝ) + 1) * Real.log 4 := by
      have hsplit : Real.log (4 / 3 : ℝ) = Real.log 4 - Real.log 3 :=
        Real.log_div (by norm_num) (by norm_num)
      rw [hsplit] at hstep
      nlinarith [hstep]
    have hpow : (q : ℝ) * 3 ^ k ≤ 4 ^ (k + 1) := by
      have hpos1 : 0 < (q : ℝ) * 3 ^ k := by positivity
      have hpos2 : 0 < (4 : ℝ) ^ (k + 1) := by positivity
      rw [← Real.log_le_log_iff hpos1 hpos2,
        Real.log_mul (ne_of_gt hqpos) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      convert hlogkey using 2 <;> ring
    have hpowN : q * 3 ^ k ≤ 4 ^ (k + 1) := by exact_mod_cast hpow
    refine ⟨buildFuel hF k (Finset.univ : Finset F),
      fun s => buildFuel_solves hF k (Finset.univ : Finset F) (by simpa using hpowN) s (Finset.mem_univ s), ?_⟩
    have hd := buildFuel_depth hF k (Finset.univ : Finset F) (by simpa using hpowN)
    have hkbound : (k : ℝ) ≤ x + 1 := le_of_lt (Nat.ceil_lt_add_one hxpos)
    have hxexpr : x = Real.log (q : ℝ) / Real.log (4 / 3 : ℝ) -
        Real.log 4 / Real.log (4 / 3 : ℝ) := by
      rw [hxdef]; ring
    have hlog4ge2 : (2 : ℝ) ≤ Real.log 4 / Real.log (4 / 3 : ℝ) := by
      rw [le_div_iff₀ hlog43]
      have h16 : (2 : ℝ) * Real.log (4 / 3 : ℝ) = Real.log ((4 / 3 : ℝ) ^ 2) := by
        rw [Real.log_pow]; ring
      rw [h16]
      exact Real.log_le_log (by norm_num : (0:ℝ) < (4/3)^2) (by norm_num)
    have hdepth : (k : ℝ) + 4 ≤ Real.log (q : ℝ) / Real.log (4 / 3 : ℝ) + 3 := by
      nlinarith [hkbound, hxexpr, hlog4ge2]
    have hqeq : (q : ℝ) = (Fintype.card F : ℝ) := by rw [hqdef]
    calc ((buildFuel hF k (Finset.univ : Finset F)).depth : ℝ) ≤ ((k : ℝ) + 4) := by
          exact_mod_cast hd
      _ ≤ Real.log (q : ℝ) / Real.log (4 / 3 : ℝ) + 3 := hdepth
      _ = Real.log (Fintype.card F : ℝ) / Real.log (4 / 3 : ℝ) + 3 := by rw [hqeq]

end Qatlib.Papers.WeighMatrix00.MainResults
