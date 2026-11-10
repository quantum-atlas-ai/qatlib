/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PrincIdeal09.MainResults.Framework
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.PrincIdeal09.MainResults

def windowStart (M : RegPeriodModel) (g : M.Form) (k : ℤ) : ℤ :=
  ⌈4 * (M.d g + (k : ℝ) * M.R)⌉

def windowRun (M : RegPeriodModel) (g : M.Form) (k : ℤ) : ℤ :=
  ⌈4 * (M.d (M.succ g) + (k : ℝ) * M.R) - ((windowStart M g k : ℤ) : ℝ)⌉ - 1

theorem windowStart_spec (M : RegPeriodModel) (g : M.Form) (k : ℤ) :
    M.d g + (k : ℝ) * M.R ≤ ((windowStart M g k : ℤ) : ℝ) / 4 ∧
      ((windowStart M g k : ℤ) : ℝ) / 4 < M.d g + (k : ℝ) * M.R + 1 / 4 := by
  have hle := Int.le_ceil (4 * (M.d g + (k : ℝ) * M.R))
  have hlt := Int.ceil_lt_add_one (4 * (M.d g + (k : ℝ) * M.R))
  dsimp only [windowStart]
  constructor <;> linarith

theorem abs_ceil_sub_ceil_le_one {p q : ℝ} (h : |p - q| < 1) : |⌈p⌉ - ⌈q⌉| ≤ 1 := by
  rw [abs_lt] at h
  have hq : p < q + 1 := by linarith [h.2]
  have hp : q < p + 1 := by linarith [h.1]
  have h1 : ⌈p⌉ ≤ ⌈q⌉ + 1 := by
    rw [Int.ceil_le]
    push_cast
    have hq2 : q ≤ (⌈q⌉ : ℝ) := Int.le_ceil q
    linarith
  have h2 : ⌈q⌉ ≤ ⌈p⌉ + 1 := by
    rw [Int.ceil_le]
    push_cast
    have hp2 : p ≤ (⌈p⌉ : ℝ) := Int.le_ceil p
    linarith
  rw [abs_le]
  omega

theorem lemma1_period_entry (M : RegPeriodModel) (g : M.Form) :
    ∃ y : ℝ, y = 4 * M.delta g + 1 / 2 ∧
      ∀ k : ℤ, ∃ ε : ℝ, |ε| ≤ 1 ∧ ∃ x : ℤ,
        (x : ℝ) = y + 4 * (k : ℝ) * M.R + ε ∧
          M.reg x = g ∧ M.reg (x - 1) = M.pred g := by
  refine ⟨4 * M.delta g + 1 / 2, rfl, ?_⟩
  intro k
  refine ⟨((windowStart M g k : ℤ) : ℝ) - (4 * M.delta g + 1 / 2 + 4 * (k : ℝ) * M.R),
    ?_, windowStart M g k, ?_, ?_, ?_⟩
  · have hwin := windowStart_spec M g k
    have hd := M.approx g
    have hε : ((windowStart M g k : ℤ) : ℝ) - (4 * M.delta g + 1 / 2 + 4 * (k : ℝ) * M.R)
        = (((windowStart M g k : ℤ) : ℝ) - 4 * (M.d g + (k : ℝ) * M.R))
            + 4 * (M.d g - M.delta g) - 1 / 2 := by ring
    rw [hε, abs_le]
    rw [abs_lt] at hd
    constructor <;> linarith [hwin.1, hwin.2, hd.1, hd.2]
  · ring
  · refine (M.reg_spec _ _).mpr ⟨k, ?_, ?_⟩
    · exact (windowStart_spec M g k).1
    · have hg := M.succ_gap g
      nlinarith [(windowStart_spec M g k).2, hg]
  · refine (M.reg_spec _ _).mpr ⟨k, ?_, ?_⟩
    · have hp := M.pred_gap g
      have hcast : (((windowStart M g k - 1 : ℤ) : ℤ) : ℝ)
          = ((windowStart M g k : ℤ) : ℝ) - 1 := by push_cast; ring
      rw [hcast]
      nlinarith [(windowStart_spec M g k).1, hp]
    · have hcast : (((windowStart M g k - 1 : ℤ) : ℤ) : ℝ)
          = ((windowStart M g k : ℤ) : ℝ) - 1 := by push_cast; ring
      rw [hcast, M.succ_pred]
      nlinarith [(windowStart_spec M g k).2]

theorem lemma2_run (M : RegPeriodModel) (Δ : ℝ)
    (hΔ : 0 < Δ) (hR : 5 * Real.log Δ < M.R) (g : M.Form) (k : ℤ)
    (hwin : (1 / 2 : ℝ) < M.d (M.succ g) - M.d g)
    (hcount : 4 * (M.d (M.succ g) - M.d g) ≤ Real.log Δ + 3) :
    1 ≤ windowRun M g k ∧ (windowRun M g k : ℝ) < Real.log Δ + 3 ∧
      M.reg (windowStart M g k + windowRun M g k + 1) = M.succ g ∧
      (∀ j : ℤ, 0 ≤ j → j ≤ windowRun M g k → M.reg (windowStart M g k + j) = g) ∧
      (∀ k' : ℤ, |windowRun M g k - windowRun M g k'| ≤ 4) := by
  set s : ℤ := windowStart M g k with hs
  set a : ℝ := M.d g + (k : ℝ) * M.R with ha
  set b : ℝ := M.d (M.succ g) + (k : ℝ) * M.R with hb
  set w : ℝ := M.d (M.succ g) - M.d g with hw
  set C : ℝ := 4 * b - (s : ℝ) with hC
  have hstart : a ≤ (s : ℝ) / 4 ∧ (s : ℝ) / 4 < a + 1 / 4 := by
    have h := windowStart_spec M g k
    rw [← hs, ← ha] at h
    exact h
  have hw_pos : (1 / 2 : ℝ) < w := by rw [hw]; exact hwin
  have hcount' : 4 * w ≤ Real.log Δ + 3 := by rw [hw]; exact hcount
  have hb_eq : b = a + w := by rw [hb, ha, hw]; ring
  have hC_eq : C = 4 * (b - (s : ℝ) / 4) := by rw [hC]; ring
  have hC_lo : 4 * w - 1 < C := by
    have h1 := hstart.1
    have h2 := hstart.2
    rw [hC_eq, hb_eq]
    nlinarith
  have hC_hi : C ≤ 4 * w := by
    have h1 := hstart.1
    rw [hC_eq, hb_eq]
    nlinarith
  have hrun : windowRun M g k = ⌈C⌉ - 1 := by
    unfold windowRun
    have h1 : (4 * (M.d (M.succ g) + (k : ℝ) * M.R) - ((windowStart M g k : ℤ) : ℝ)) = C := by
      rw [hC, ← hs, ← hb]
    rw [h1]
  have hceil_lt : (⌈C⌉ : ℝ) < C + 1 := Int.ceil_lt_add_one C
  have hceil_ge : C ≤ (⌈C⌉ : ℝ) := Int.le_ceil C
  have hmval : (windowRun M g k : ℝ) = (⌈C⌉ : ℝ) - 1 := by
    rw [hrun]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun]
    have hCgt : (1 : ℝ) < C := by linarith [hC_lo, hw_pos]
    have h2z : (2 : ℤ) ≤ ⌈C⌉ := by
      have h1z : (1 : ℤ) < ⌈C⌉ := by
        rw [Int.lt_ceil]
        simpa using hCgt
      omega
    linarith
  · rw [hmval]
    have hCb : C ≤ Real.log Δ + 3 := by linarith [hC_hi, hcount']
    linarith [hceil_lt, hCb]
  · refine (M.reg_spec _ _).mpr ⟨k, ?_, ?_⟩
    · rw [← hb]
      have hcast : (((s + windowRun M g k + 1 : ℤ) : ℤ) : ℝ)
          = (s : ℝ) + (windowRun M g k : ℝ) + 1 := by push_cast; ring
      rw [hcast, hmval]
      have hge := hceil_ge
      rw [hC] at hge
      nlinarith [hge]
    · have hcast : (((s + windowRun M g k + 1 : ℤ) : ℤ) : ℝ)
          = (s : ℝ) + (windowRun M g k : ℝ) + 1 := by push_cast; ring
      rw [hcast, hmval]
      have hlt := hceil_lt
      rw [hC] at hlt
      have hgap2 := M.succ_gap (M.succ g)
      have hb' : M.d (M.succ (M.succ g)) + (k : ℝ) * M.R
          = b + (M.d (M.succ (M.succ g)) - M.d (M.succ g)) := by rw [hb]; ring
      rw [hb']
      nlinarith [hlt, hgap2]
  · intro j hj0 hjm
    refine (M.reg_spec _ _).mpr ⟨k, ?_, ?_⟩
    · rw [← ha]
      have hcast : (((s + j : ℤ) : ℤ) : ℝ) = (s : ℝ) + (j : ℝ) := by push_cast; ring
      rw [hcast]
      have hj0' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
      nlinarith [hstart.1]
    · rw [← hb]
      have hcast : (((s + j : ℤ) : ℤ) : ℝ) = (s : ℝ) + (j : ℝ) := by push_cast; ring
      rw [hcast]
      have hjm' : (j : ℝ) ≤ (windowRun M g k : ℝ) := by exact_mod_cast hjm
      have hjC : (j : ℝ) < C := by linarith [hjm', hmval, hceil_lt]
      have hCq : C = 4 * b - (s : ℝ) := hC
      nlinarith [hjC, hCq]
  · intro k'
    set a' : ℝ := M.d g + (k' : ℝ) * M.R with ha'
    set b' : ℝ := M.d (M.succ g) + (k' : ℝ) * M.R with hb'
    set s' : ℤ := windowStart M g k' with hs'
    set C' : ℝ := 4 * b' - (s' : ℝ) with hC'
    have hstart' : a' ≤ (s' : ℝ) / 4 ∧ (s' : ℝ) / 4 < a' + 1 / 4 := by
      have h := windowStart_spec M g k'
      rw [← hs', ← ha'] at h
      exact h
    have hb'_eq : b' = a' + w := by rw [hb', ha', hw]; ring
    have hC'_eq : C' = 4 * (b' - (s' : ℝ) / 4) := by rw [hC']; ring
    have hdiff : |C - C'| < 1 := by
      have hCv : C = 4 * w - ((s : ℝ) - 4 * a) := by rw [hC_eq, hb_eq]; ring
      have hC'v : C' = 4 * w - ((s' : ℝ) - 4 * a') := by rw [hC'_eq, hb'_eq]; ring
      have h1 : 0 ≤ (s : ℝ) - 4 * a := by linarith [hstart.1]
      have h2 : (s : ℝ) - 4 * a < 1 := by linarith [hstart.2]
      have h1' : 0 ≤ (s' : ℝ) - 4 * a' := by linarith [hstart'.1]
      have h2' : (s' : ℝ) - 4 * a' < 1 := by linarith [hstart'.2]
      rw [abs_lt]
      constructor <;> linarith [hCv, hC'v, h1, h2, h1', h2']
    have hrun' : windowRun M g k' = ⌈C'⌉ - 1 := by
      unfold windowRun
      have h1 : (4 * (M.d (M.succ g) + (k' : ℝ) * M.R) - ((windowStart M g k' : ℤ) : ℝ)) = C' := by
        rw [hC', ← hs', ← hb']
      rw [h1]
    rw [hrun, hrun']
    have hceil_diff : |⌈C⌉ - ⌈C'⌉| ≤ 1 := abs_ceil_sub_ceil_le_one hdiff
    calc |⌈C⌉ - 1 - (⌈C'⌉ - 1)| = |⌈C⌉ - ⌈C'⌉| := by ring_nf
      _ ≤ 1 := hceil_diff
      _ ≤ 4 := by norm_num

end Qatlib.Papers.PrincIdeal09.MainResults
