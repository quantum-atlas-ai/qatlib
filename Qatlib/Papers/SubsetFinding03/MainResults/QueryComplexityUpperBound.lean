/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SubsetFinding03.MainResults.QueryComplexityUpperBound

def subsetFindingMemory (N L : ℕ) : ℕ :=
  ⌊((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)))⌋₊

def roundNearest (x : ℝ) : ℕ :=
  ⌊x + 1 / 2⌋₊

def subsetFindingWalkSteps (N L : ℕ) : ℕ :=
  roundNearest ((Real.pi / 2) * Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ)))

def subsetFindingIterations (N L : ℕ) : ℕ :=
  roundNearest
    ((Real.pi / 2) * (((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)))

def subsetFindingQueryCount (N L : ℕ) : ℕ :=
  subsetFindingMemory N L + 2 * subsetFindingWalkSteps N L * subsetFindingIterations N L

lemma roundNearest_le (x : ℝ) (hx : 0 ≤ x) : (roundNearest x : ℝ) ≤ x + 1 / 2 := by
  exact Nat.floor_le (by linarith)

lemma subsetFindingMemory_le (N L : ℕ) (hN : 0 ≤ (N : ℝ)) :
    (subsetFindingMemory N L : ℝ) ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by
  exact Nat.floor_le (Real.rpow_nonneg hN _)

lemma rpow_subsetFinding_ge_two (N L : ℕ) (hL : 1 ≤ L) (hN : 4 ≤ N) :
    2 ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by
  have hLpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hhalf : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 1) := by
    rw [le_div_iff₀ hLpos]
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf
  have hNe : (4 : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) ≤
      (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by
    apply Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) ?_ (by positivity)
    exact_mod_cast hN
  have h41 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  linarith

lemma subsetFindingMemory_ge_half (N L : ℕ) (hL : 1 ≤ L) (hN : 4 ≤ N) :
    (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) / 2 ≤ (subsetFindingMemory N L : ℝ) := by
  have hx2 : 2 ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) :=
    rpow_subsetFinding_ge_two N L hL hN
  have hle := subsetFindingMemory_le N L (by positivity : (0 : ℝ) ≤ (N : ℝ))
  have hlt : (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) < (subsetFindingMemory N L : ℝ) + 1 := by
    simpa [subsetFindingMemory] using
      Nat.lt_floor_add_one ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)))
  linarith

lemma subsetFindingMemory_pos (N L : ℕ) (hL : 1 ≤ L) (hN : 4 ≤ N) :
    1 ≤ subsetFindingMemory N L := by
  unfold subsetFindingMemory
  apply Nat.le_floor
  have h := rpow_subsetFinding_ge_two N L hL hN
  norm_num
  linarith

lemma N_div_memory_le (N L : ℕ) (hL : 1 ≤ L) (hN : 4 ≤ N) :
    (N : ℝ) / (subsetFindingMemory N L : ℝ) ≤
      2 * (N : ℝ) ^ (1 / ((L : ℝ) + 1)) := by
  set x : ℝ := (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) with hxdef
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hx2 : 2 ≤ x := rpow_subsetFinding_ge_two N L hL hN
  have hxpos : 0 < x := by linarith
  have hMge : x / 2 ≤ (subsetFindingMemory N L : ℝ) :=
    subsetFindingMemory_ge_half N L hL hN
  have hMpos : (0 : ℝ) < (subsetFindingMemory N L : ℝ) := by linarith
  have hstep : (N : ℝ) / (subsetFindingMemory N L : ℝ) ≤ 2 * (N : ℝ) / x := by
    have h1 : (N : ℝ) / (subsetFindingMemory N L : ℝ) ≤ (N : ℝ) / (x / 2) :=
      div_le_div_of_nonneg_left hN0 (by linarith) hMge
    have h2 : (N : ℝ) / (x / 2) = 2 * (N : ℝ) / x := by
      have hxne : x ≠ 0 := by linarith
      field_simp
    linarith
  have hNdivx : (N : ℝ) / x = (N : ℝ) ^ (1 / ((L : ℝ) + 1)) := by
    have h1 : (N : ℝ) / x = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by
      rw [hxdef, Real.rpow_one]
    have h2 : (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))
        = (N : ℝ) ^ ((1 : ℝ) - (L : ℝ) / ((L : ℝ) + 1)) :=
      (Real.rpow_sub hNpos 1 _).symm
    have hexp : (1 : ℝ) - (L : ℝ) / ((L : ℝ) + 1) = 1 / ((L : ℝ) + 1) := by
      have hLpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
      field_simp
      ring
    rw [h1, h2, hexp]
  calc (N : ℝ) / (subsetFindingMemory N L : ℝ) ≤ 2 * (N : ℝ) / x := hstep
    _ = 2 * ((N : ℝ) / x) := by rw [mul_div_assoc]
    _ = 2 * (N : ℝ) ^ (1 / ((L : ℝ) + 1)) := by rw [hNdivx]

theorem theorem1_cost_arithmetic (L : ℕ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (subsetFindingQueryCount N L : ℝ) ≤
        C * ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))) := by
  refine ⟨20 * (2 : ℝ) ^ (L : ℝ) + 8, by positivity, 4, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLposR : (0 : ℝ) < (L : ℝ) := by linarith
  set e : ℝ := (L : ℝ) / ((L : ℝ) + 1) with he
  set x : ℝ := (N : ℝ) ^ e with hxdef
  set M : ℕ := subsetFindingMemory N L with hMdef
  set s : ℝ := x ^ ((1 : ℝ) / 2) with hsdef
  have hxge := subsetFindingMemory_ge_half N L hL hN
  have hxle := subsetFindingMemory_le N L hN0
  have hx2 : 2 ≤ x := rpow_subsetFinding_ge_two N L hL hN
  have hx1 : 1 ≤ x := by linarith
  have hs1 : 1 ≤ s := by
    rw [hsdef]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 2) := (Real.one_rpow _).symm
      _ ≤ x ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
  have hs0 : 0 ≤ s := by linarith
  have hs2 : s ^ 2 = x := by
    rw [hsdef, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (by linarith)
  have hM : (M : ℝ) ≤ x := hxle

  have ht1 : ((subsetFindingWalkSteps N L : ℕ) : ℝ) ≤ (5 / 2) * s := by
    change ((roundNearest
      ((Real.pi / 2) * Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ))) : ℕ) : ℝ)
      ≤ (5 / 2) * s
    have h := roundNearest_le ((Real.pi / 2) * Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ)))
      (by positivity : (0 : ℝ) ≤ (Real.pi / 2) * Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ)))
    have hsqrt : Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ)) ≤ s := by
      rw [hsdef, ← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hLposR]
      have hx0 : 0 ≤ x := by linarith
      nlinarith [hxle, hL1R, hx0]
    have hpi : Real.pi / 2 ≤ 2 := by
      have := Real.pi_le_four
      linarith
    have hstep : (Real.pi / 2) * Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ)) + 1 / 2
        ≤ (5 / 2) * s := by
      have hsqa : 0 ≤ Real.sqrt ((subsetFindingMemory N L : ℝ) / (L : ℝ)) := Real.sqrt_nonneg _
      have hp : 0 ≤ Real.pi / 2 := by positivity
      nlinarith [hpi, hsqrt, hsqa, hp, hs1]
    linarith

  have hNM := N_div_memory_le N L hL hN
  have hNM0 : (0 : ℝ) ≤ (N : ℝ) / (subsetFindingMemory N L : ℝ) := by positivity
  have hb : ((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)
      ≤ (2 : ℝ) ^ (L : ℝ) * s := by
    have hm : ((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)
        ≤ (2 * (N : ℝ) ^ (1 / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2) :=
      Real.rpow_le_rpow hNM0 hNM (by positivity)
    have hsplit : (2 * (N : ℝ) ^ (1 / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2)
        = (2 : ℝ) ^ ((L : ℝ) / 2) *
            ((N : ℝ) ^ (1 / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0 _)]
    have hmul : ((N : ℝ) ^ (1 / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2)
        = (N : ℝ) ^ ((1 / ((L : ℝ) + 1)) * ((L : ℝ) / 2)) := by
      rw [Real.rpow_mul hN0]
    have hexp : (1 / ((L : ℝ) + 1)) * ((L : ℝ) / 2) = e / 2 := by
      rw [he]
      field_simp
    have htoS : (N : ℝ) ^ ((1 / ((L : ℝ) + 1)) * ((L : ℝ) / 2)) = s := by
      rw [hexp, hsdef, hxdef, ← Real.rpow_mul hN0]
      congr 1
      ring
    have h2L : (2 : ℝ) ^ ((L : ℝ) / 2) ≤ (2 : ℝ) ^ (L : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc ((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)
        ≤ (2 * (N : ℝ) ^ (1 / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2) := hm
      _ = (2 : ℝ) ^ ((L : ℝ) / 2) * s := by rw [hsplit, hmul, htoS]
      _ ≤ (2 : ℝ) ^ (L : ℝ) * s :=
          mul_le_mul_of_nonneg_right h2L hs0
  have ht2 : ((subsetFindingIterations N L : ℕ) : ℝ) ≤ (5 / 2) * ((2 : ℝ) ^ (L : ℝ) * s) := by
    change ((roundNearest
      ((Real.pi / 2) * (((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2))) : ℕ) : ℝ)
      ≤ (5 / 2) * ((2 : ℝ) ^ (L : ℝ) * s)
    have h := roundNearest_le
      ((Real.pi / 2) * (((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)))
      (by positivity : (0 : ℝ) ≤
        (Real.pi / 2) * (((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)))
    have hpi : Real.pi / 2 ≤ 2 := by
      have := Real.pi_le_four
      linarith
    have hbM : ((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)
        ≤ (2 : ℝ) ^ (L : ℝ) * s := hb
    have hb0 : 0 ≤ ((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hstep : (Real.pi / 2) * (((N : ℝ) / (subsetFindingMemory N L : ℝ)) ^ ((L : ℝ) / 2)) + 1 / 2 ≤
        (5 / 2) * ((2 : ℝ) ^ (L : ℝ) * s) := by
      have hp : 0 ≤ Real.pi / 2 := by positivity
      have h2Ls : 0 ≤ (2 : ℝ) ^ (L : ℝ) * s := by positivity
      have h2L1 : (1 : ℝ) ≤ (2 : ℝ) ^ (L : ℝ) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      nlinarith [hpi, hbM, hb0, hp, h2Ls, h2L1, hs1]
    linarith

  have hQ : (subsetFindingQueryCount N L : ℝ)
      ≤ x + 2 * ((5 / 2) * s) * ((5 / 2) * ((2 : ℝ) ^ (L : ℝ) * s)) := by
    unfold subsetFindingQueryCount
    push_cast
    have h2t : 2 * ((subsetFindingWalkSteps N L : ℕ) : ℝ) * ((subsetFindingIterations N L : ℕ) : ℝ)
        ≤ 2 * ((5 / 2) * s) * ((5 / 2) * ((2 : ℝ) ^ (L : ℝ) * s)) := by
      have hA0 : (0 : ℝ) ≤ ((subsetFindingWalkSteps N L : ℕ) : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ ((subsetFindingIterations N L : ℕ) : ℝ) := by positivity
      nlinarith [ht1, ht2]
    linarith [hM, h2t]

  have hbound : x + 2 * ((5 / 2) * s) * ((5 / 2) * ((2 : ℝ) ^ (L : ℝ) * s))
      ≤ (20 * (2 : ℝ) ^ (L : ℝ) + 8) * x := by
    have h2L1 : (1 : ℝ) ≤ (2 : ℝ) ^ (L : ℝ) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hx0 : 0 ≤ x := by linarith
    nlinarith [hs2, hs1, h2L1, hs0, hx0]
  linarith [hQ, hbound]

end Qatlib.Papers.SubsetFinding03.MainResults.QueryComplexityUpperBound
