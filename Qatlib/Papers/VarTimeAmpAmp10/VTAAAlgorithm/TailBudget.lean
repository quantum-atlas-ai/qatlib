/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # The exact truncated historical stopping budget

The old Lemma7 target sums only stages below `n+2`. Its complete finite bound
holds with the uniform constant2, independently of the supplied tail decay.
This does not prove the paper's infinite-tail stopping-time identity or its
algorithmic realization; the distinction is kept explicit.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.TailBudget

/-- A branch's genuine finite stopping moment is bounded using its actual mass law. -/
theorem branchBound (n : ℕ) (p : ℕ → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hm : ∑ s ∈ Finset.range (n+2), p s ≤ 1) :
    ∑ s ∈ Finset.range (n+2), p s * ((2 : ℝ)^s)^2 ≤ 4*(2 : ℝ)^(2*n) := by
  have hpow (s : ℕ) (hs : s ∈ Finset.range (n+2)) :
      ((2 : ℝ)^s)^2 ≤ 4*(2 : ℝ)^(2*n) := by
    have hsn : s ≤ n+1 := by have := Finset.mem_range.mp hs; omega
    have he : ((2 : ℝ)^(n+1))^2 = 4*(2 : ℝ)^(2*n) := by
      rw [mul_comm 2 n,pow_mul,pow_succ]
      ring
    rw [← he]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hsn)
  calc
    _ ≤ ∑ s ∈ Finset.range (n+2), p s*(4*(2 : ℝ)^(2*n)) :=
      Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hpow s hs) (hp s)
    _ = (∑ s ∈ Finset.range (n+2), p s)*(4*(2 : ℝ)^(2*n)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 1*(4*(2 : ℝ)^(2*n)) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := one_mul _

/-- The whole original truncated target holds with one explicit constant for every family. -/
theorem uniformBudget {ι : Type} [Fintype ι]
    (α : ι → ℝ) (n : ι → ℕ) (pstop : ι → ℕ → ℝ) (Tav kuniq : ℝ)
    (hp0 : ∀ i s, 0 ≤ pstop i s) (hk : 0 ≤ kuniq)
    (hp1 : ∀ i, ∑ s ∈ Finset.range (n i+2), pstop i s ≤ 1)
    (hTav : Tav^2 = (∑ i, α i^2 *
      (∑ s ∈ Finset.range (n i+2), pstop i s*((2 : ℝ)^s)^2))*kuniq^2) :
    Tav ≤ 2*kuniq*Real.sqrt (∑ i, α i^2*(2 : ℝ)^(2*n i)) := by
  let S := ∑ i, α i^2*(2 : ℝ)^(2*n i)
  have hs : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hb : (∑ i, α i^2 *
      (∑ s ∈ Finset.range (n i+2), pstop i s*((2 : ℝ)^s)^2)) ≤ 4*S := by
    calc
      _ ≤ ∑ i, α i^2*(4*(2 : ℝ)^(2*n i)) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (branchBound (n i) (pstop i) (hp0 i) (hp1 i)) (sq_nonneg _)
      _ = 4*S := by simp only [S,Finset.mul_sum]; congr 1; funext i; ring
  have hsq := mul_le_mul_of_nonneg_right hb (sq_nonneg kuniq)
  have hroot := Real.sq_sqrt hs
  have hnonneg : 0 ≤ 2*kuniq*Real.sqrt S := by positivity
  change Tav ≤ 2*kuniq*Real.sqrt S
  rw [← hTav] at hsq
  nlinarith [sq_nonneg (Tav-2*kuniq*Real.sqrt S)]

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.TailBudget
