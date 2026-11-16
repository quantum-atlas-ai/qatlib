/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MultivInterp17.MainResults.Model.InterpolationModel
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.MultivInterp17.MainResults

open MeasureTheory
open Qatlib.Papers.MultivInterp17.MainResults.Model

/-- The retained almost-everywhere completeness contract still needs an analytic realization in L2. -/
def AeComplete {σ : Type*} [Fintype σ] (S : Set (σ → ℝ))
    (Λ : AddSubgroup (σ → ℝ)) : Prop :=
  (∀ c ∈ (Λ : Set (σ → ℝ)), ∀ c' ∈ (Λ : Set (σ → ℝ)),
      ∫ z in S, basisState S c' z * star (basisState S c z) ∂volume
        = if c = c' then 1 else 0) ∧
  (∀ f : (σ → ℝ) → ℂ,
      (∀ c ∈ (Λ : Set (σ → ℝ)),
          ∫ z in S, star (basisState S c z) * f z ∂volume = 0) →
      f =ᵐ[volume.restrict S] 0)

/-- The finite-field query bound equals the Pascal ratio in Corollary 3.13. -/
theorem finiteQueryBound_eq_ratio (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (finiteQueryBound n d : ℚ) = (d : ℚ) / (n + d) * (monomialCount n d : ℚ) := by
  have hnat := Nat.add_one_mul_choose_eq (n + d - 1) (d - 1)
  have h1 : n + d - 1 + 1 = n + d := by omega
  have h2 : d - 1 + 1 = d := by omega
  rw [h1, h2] at hnat
  have hq : ((n + d : ℕ) : ℚ) * ((n + d - 1).choose (d - 1) : ℚ)
      = ((n + d).choose d : ℚ) * (d : ℚ) := by exact_mod_cast hnat
  unfold finiteQueryBound monomialCount
  have hnd : ((n + d : ℕ) : ℚ) ≠ 0 := by positivity
  have hcast : ((n : ℚ) + (d : ℚ)) = ((n + d : ℕ) : ℚ) := by push_cast; ring
  rw [hcast, div_mul_eq_mul_div, eq_div_iff hnd]
  linear_combination hq

/-- Normalizing by an infinite measure makes the legacy success ratio zero. -/
theorem successRatio_infinite {V : Type*} [MeasurableSpace V]
    (μ : Measure V) (R S : Set V) (hS : μ S = ⊤) : successRatio μ R S = 0 := by
  simp [successRatio, hS]

/-- The real-line instance already rules out strict increase on an unbounded window. -/
theorem unbounded_not_strict (R : ℕ → Set ℝ) :
    ¬ StrictMonoOn (fun k => successRatio volume (R k) Set.univ) (Set.Icc 0 1) := by
  intro h
  have h01 := h (by simp : 0 ∈ Set.Icc (0 : ℕ) 1)
    (by simp : 1 ∈ Set.Icc (0 : ℕ) 1) (by omega : (0 : ℕ) < 1)
  simp [successRatio] at h01

end Qatlib.Papers.MultivInterp17.MainResults
