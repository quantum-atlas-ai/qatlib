/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Qatlib.Papers.AnyCircuit08.MainResults.Assembly

/-!
# Fourth moments and dispersing circuits

The last step of [HallgrenHarrow2008], Theorem 12 and Appendix A, converts a uniform
fourth-moment estimate into a probability of dispersing. This finite-ensemble version
gets row normalization from the circuit isometries and proves the denominator is
positive for the repaired parameter range `0 < α < 1`.

[arXiv:0805.0007v2](https://arxiv.org/abs/0805.0007v2)
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.AnyCircuit08.MainResults

open Qatlib.Papers.AnyCircuit08.MainResults

/-- The amplitudes in the row indexed by `a`, obtained from the adjoint circuit on the
computational basis vector for `a`. -/
def circuitRow {X : Type} [Fintype X]
    (U : EuclideanSpace ℂ X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X) (a x : X) : ℂ :=
  star (U.symm (EuclideanSpace.basisFun X ℂ a) x)

/-- Collision probability of the computational-basis measurement of the adjoint circuit's
output on basis input `a`. -/
def rowFourthMoment {X : Type} [Fintype X]
    (U : EuclideanSpace ℂ X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X) (a : X) : ℝ :=
  ∑ x, ‖circuitRow U a x‖ ^ 4

open scoped Classical in
/-- For a finite uniform ensemble of circuits satisfying the Appendix A fourth-moment estimate
for every basis input, the fraction that are dispersing is at least the probability bound in
[HallgrenHarrow2008], Theorem 12. The estimate is the output of the mixing analysis. -/
theorem fraction_dispersing_of_mean_fourthMoment {Ω X : Type} [Fintype Ω] [Fintype X]
    [DecidableEq X] (U : Ω → EuclideanSpace ℂ X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X) {n : ℕ}
    (hn : 0 < n) (hX : Fintype.card X = 2 ^ n) (hΩ : 0 < Fintype.card Ω)
    {α β : ℝ} (_hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hmean : ∀ a, (∑ ω, rowFourthMoment (U ω) a) / (Fintype.card Ω : ℝ)
      ≤ 2 * (2 : ℝ) ^ (-(n : ℝ))) :
    1 - (2 * β ^ 2) / (1 - (2 : ℝ) ^ (-(n : ℝ) * (1 - α))) ≤
      (∑ ω, if IsDispersing (circuitRow (U ω)) α β then (1 : ℝ) else 0) /
        (Fintype.card Ω : ℝ) := by
  classical
  have hX1 : 1 ≤ Fintype.card X := by rw [hX]; exact Nat.one_le_pow n 2 (by decide)
  have hN : (Fintype.card X : ℝ) = (2 : ℝ) ^ (n : ℝ) := by
    rw [hX, Real.rpow_natCast]
    norm_cast
  have hNpos : (0 : ℝ) < Fintype.card X := by
    exact_mod_cast Nat.zero_lt_of_lt hX1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let s := 1 - (2 : ℝ) ^ (-(n : ℝ) * (1 - α))
  have hs : 0 < s := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos (neg_neg_of_pos hn')
      (sub_pos.mpr hα1)))
  have hfrac : (2 : ℝ) ^ (-(n : ℝ) * (1 - α)) =
      (Fintype.card X : ℝ) ^ α / (Fintype.card X : ℝ) := by
    rw [hN, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hsize : (Fintype.card X : ℝ) - s * (Fintype.card X : ℝ) =
      (Fintype.card X : ℝ) ^ α := by
    dsimp [s]
    rw [hfrac]
    have hc := div_mul_cancel₀ ((Fintype.card X : ℝ) ^ α) hNpos.ne'
    linarith
  let t := (2 : ℝ) ^ (-(n : ℝ)) / β ^ 2
  have ht : t = 1 / ((Fintype.card X : ℝ) * β ^ 2) := by
    dsimp [t]
    rw [hN, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hbase : (2 : ℝ) ^ (n : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp [hbase, hβ.ne']
  let bad (ω : Ω) (a : X) : Bool := decide (t ≤ rowFourthMoment (U ω) a)
  refine fraction_dispersing_ge (fun ω => circuitRow (U ω)) bad hβ hX1 hs hsize.ge ?_ hΩ ?_ ?_
  · intro a
    have hnonneg (ω : Ω) : 0 ≤ rowFourthMoment (U ω) a := by
      unfold rowFourthMoment
      positivity
    simpa [bad, t] using markov_qt_bad_fraction _ hnonneg hβ.ne' hΩ (hmean a)
  · intro ω a _
    simp only [circuitRow, norm_star, ← EuclideanSpace.norm_sq_eq, (U ω).symm.norm_map]
    rw [(EuclideanSpace.basisFun X ℂ).orthonormal.norm_eq_one a, one_pow]
  · intro ω a hbad
    have hgood : rowFourthMoment (U ω) a < t := by
      simpa [bad, not_le] using hbad
    rw [← ht]
    exact hgood.le

end Qatlib.Papers.AnyCircuit08.MainResults
