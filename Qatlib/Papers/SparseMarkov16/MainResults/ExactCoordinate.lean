/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseMarkov16.MainResults.Model.SparseMarkovModel
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring

@[expose] public section


/-! The exact exponential of an entrywise identical-coordinate generator. -/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Papers.SparseMarkov16.MainResults.Model
namespace Qatlib.Papers.SparseMarkov16.MainResults.ExactCoordinate

/-- Every iterate of an entrywise scalar multiplier is the corresponding scalar power. -/
theorem coordinate_iterate {N : ℕ} (a c : Fin N → ℝ)
    (ρ : Op N) (k : ℕ) (u v : Fin N) :
    ((identCoordLindbladApply a c)^[k] ρ) u v =
      (if u = v then (0 : ℂ)
        else (-((a u + a v - 2 * (c u + c v) : ℝ)) : ℂ)) ^ k * ρ u v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases huv : u = v
    · simp [identCoordLindbladApply, huv]
    · simp only [identCoordLindbladApply, ite_eq_right huv, ih, pow_succ]
      ring

/-- The source power-series semigroup is the coordinatewise real exponential. -/
theorem identical_coordinate_exact {N : ℕ} (a c : Fin N → ℝ) (t : ℝ)
    (ρ : Op N) :
    superExp (identCoordLindbladApply a c) t ρ = identCoordEvolve a c t ρ := by
  let rate : Fin N → Fin N → ℂ := fun u v =>
    if u = v then 0 else (-((a u + a v - 2 * (c u + c v) : ℝ)) : ℂ)
  have hiter (k : ℕ) (u v : Fin N) :
      ((identCoordLindbladApply a c)^[k] ρ) u v = rate u v ^ k * ρ u v :=
    coordinate_iterate a c ρ k u v
  have hsum : HasSum
      (fun k : ℕ => ((t : ℂ) ^ k / k.factorial) •
        ((identCoordLindbladApply a c)^[k] ρ))
      (fun u v => Complex.exp ((t : ℂ) * rate u v) * ρ u v) := by
    apply Pi.hasSum.mpr
    intro u
    apply Pi.hasSum.mpr
    intro v
    have hs := NormedSpace.expSeries_div_hasSum_exp ((t : ℂ) * rate u v)
    have hm := HasSum.mul_right (ρ u v) hs
    convert hm using 1
    · ext k
      change ((t : ℂ) ^ k / (k.factorial : ℂ)) *
          (((identCoordLindbladApply a c)^[k] ρ) u v) =
        (((t : ℂ) * rate u v) ^ k / (k.factorial : ℂ)) * ρ u v
      rw [hiter, mul_pow]
      ring
    · rw [Complex.exp_eq_exp_ℂ]
  change (∑' k : ℕ, ((t : ℂ) ^ k / k.factorial) •
      ((identCoordLindbladApply a c)^[k] ρ)) = _
  rw [hsum.tsum_eq]
  ext u v
  by_cases huv : u = v
  · simp [rate, huv, identCoordEvolve]
  · simp only [rate, ite_eq_right huv, identCoordEvolve]
    rw [Complex.ofReal_exp]
    congr 2
    push_cast
    ring

end Qatlib.Papers.SparseMarkov16.MainResults.ExactCoordinate
