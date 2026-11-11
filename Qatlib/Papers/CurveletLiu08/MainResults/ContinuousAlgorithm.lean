/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CurveletLiu08.MainResults.RadialVariance

/-!
# Continuous curvelet algorithm estimates

This module defines the candidate points `alg1Guess` and `alg2Guess` and proves conditional
success estimates for continuous curvelet algorithms. The probability theorems combine assumed
event bounds and accuracy implications into positive success probabilities.

These constructions accompany the results of [Liu2009].

## Main statements

* `norm_alg1Guess_sub_le`: bounds the error of the first candidate point.
* `source_theorem5`: derives a positive multiple of the cube of the accuracy parameter as a
  success bound.
* `source_theorem7`: combines iteration failure bounds with an accuracy implication.

## References

* [Liu, 2009][Liu2009]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace BigOperators

namespace Qatlib.Papers.CurveletLiu08.MainResults

/-- The candidate point obtained by adding `(u * Q3 * βtilde) • θ` to `b`. -/
def alg1Guess {n : ℕ} (b θ : EuclideanSpace ℝ (Fin n)) (u Q3 βtilde : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  b + (u * Q3 * βtilde) • θ

/-- The candidate point on the line through `b₁` in direction `θ₁`, with displacement computed
from the inner products of both directions and `b₁ - b₂`. -/
def alg2Guess {n : ℕ} (b₁ θ₁ b₂ θ₂ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  let r : ℝ := ⟪θ₁, θ₂⟫
  let s : ℝ := ⟪θ₁, b₁ - b₂⟫
  let t : ℝ := ⟪θ₂, b₁ - b₂⟫
  (-(s + r * t) / (1 - r ^ 2)) • θ₁ + b₁

/-- For a unit direction, bounds the distance from the first candidate to `b + t • θ + e` by the
scalar displacement error plus the norm of `e`. See [Liu2009]. -/
theorem norm_alg1Guess_sub_le {n : ℕ} (b θ e : EuclideanSpace ℝ (Fin n))
    (u Q3 βtilde t : ℝ) (hθ : ‖θ‖ = 1) :
    ‖alg1Guess b θ u Q3 βtilde - (b + t • θ + e)‖
      ≤ |u * Q3 * βtilde - t| + ‖e‖ := by
  have hdiff : alg1Guess b θ u Q3 βtilde - (b + t • θ + e)
      = (u * Q3 * βtilde - t) • θ - e := by
    unfold alg1Guess
    module
  rw [hdiff]
  calc ‖(u * Q3 * βtilde - t) • θ - e‖
      ≤ ‖(u * Q3 * βtilde - t) • θ‖ + ‖e‖ := norm_sub_le _ _
    _ = |u * Q3 * βtilde - t| + ‖e‖ := by
        rw [norm_smul, hθ, mul_one, Real.norm_eq_abs]

/-- The assumed initial-event and relative-loss bounds yield a success probability at least a
positive multiple of `ν ^ 3`. This is the probability-combination step for Theorem 5 of
[Liu2009]. -/
theorem source_theorem5
    (n : ℕ) (hn : 4 ≤ n) (ν : ℝ) (hν : 0 < ν) (_hν1 : ν < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B C succ : Set Ω) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hsub : A ∩ B ∩ C ⊆ succ)
    (hA : Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24 * ν ^ 2 ≤ P.real A)
    (hAB : P.real (A \ B) ≤ (1 - (2 / 3 : ℝ)) * P.real A)
    (hBC : P.real ((A ∩ B) \ C) ≤ (1 - ν / 100) * P.real (A ∩ B)) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 * ν ^ 3 ≤ P.real succ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h1n : 0 < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hnpos]
    exact_mod_cast (by omega : 1 < n)
  have hcA : 0 < Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24 := by positivity
  have hp : 0 < Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24 * ν ^ 2 :=
    mul_pos hcA (pow_pos hν 2)
  have hmain := prob_inter_inter_ge_of_relative (P := P) (A := A) (B := B) (C := C)
    (p := Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24 * ν ^ 2) (q := 2 / 3) (r := ν / 100)
    hB hC hp (by norm_num) (by positivity) hA hAB hBC
  have hsucc : P.real (A ∩ B ∩ C) ≤ P.real succ :=
    measureReal_mono hsub (by finiteness)
  refine ⟨(2 / 3) * (1 / 100) * (Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24), by positivity, ?_⟩
  calc (2 / 3) * (1 / 100) * (Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24) * ν ^ 3
      = (2 / 3) * (ν / 100) * (Real.exp 1 / 14 * (1 - 1 / (n : ℝ)) / 24 * ν ^ 2) := by ring
    _ ≤ P.real (A ∩ B ∩ C) := hmain
    _ ≤ P.real succ := hsucc

/-- The assumed initial-event and relative-loss bounds yield a positive constant lower bound on
success probability, as used for Theorem 6 of [Liu2009]. -/
theorem source_theorem6
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B C succ : Set Ω) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hsub : A ∩ B ∩ C ⊆ succ)
    (hA : (81 / 40000 : ℝ) ≤ P.real A)
    (hAB : P.real (A \ B) ≤ (1 - (2 / 3 : ℝ)) * P.real A)
    (hBC : P.real ((A ∩ B) \ C) ≤ (1 - (1 / 2 : ℝ)) * P.real (A ∩ B)) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ P.real succ := by
  have hmain := prob_inter_inter_ge_of_relative (P := P) (A := A) (B := B) (C := C)
    (p := (81 / 40000 : ℝ)) (q := 2 / 3) (r := 1 / 2)
    hB hC (by norm_num) (by norm_num) (by norm_num) hA hAB hBC
  have hsucc : P.real (A ∩ B ∩ C) ≤ P.real succ :=
    measureReal_mono hsub (by finiteness)
  refine ⟨(2 / 3) * (1 / 2) * (81 / 40000), by norm_num, ?_⟩
  calc (2 / 3) * (1 / 2) * (81 / 40000)
      = (2 / 3) * (1 / 2) * (81 / 40000) := rfl
    _ ≤ P.real (A ∩ B ∩ C) := hmain
    _ ≤ P.real succ := hsucc

/-- If each iteration fails with probability at most `2 / S` and all successful iterations imply
final error at most `μ`, the final accuracy event has a positive constant lower bound when
`S = 9.4 ^ niter`. This is the iteration-combination step for Theorem 7 of [Liu2009]. -/
theorem source_theorem7
    (n : ℕ) (hn : 4 ≤ n) (μ : ℝ) (hμ : 0 < μ)
    (niter : ℕ) (hniter : 0 < niter) (S : ℝ) (hS : 1 ≤ S)
    (hSdef : S = (9.4 : ℝ) ^ niter)
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin n)) (final : Ω → EuclideanSpace ℝ (Fin n))
    (good : Fin niter → Set Ω)
    (hmeas : ∀ k, MeasurableSet (good k))
    (hgood : ∀ k, P.real (good k)ᶜ ≤ 2 / S)
    (hacc : ∀ ω, (∀ k, ω ∈ good k) → ‖final ω - c‖ ≤ μ) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ P.real {ω | ‖final ω - c‖ ≤ μ} := by
  have hSpos : 0 < S := by
    rw [hSdef]
    positivity
  have hbern : 1 + (niter : ℝ) * 8.4 ≤ S := by
    rw [hSdef]
    have h := one_add_mul_le_pow (a := (8.4 : ℝ)) (by norm_num) niter
    simpa [show (9.4 : ℝ) = 1 + 8.4 by norm_num] using h
  have hniter0 : (0 : ℝ) ≤ (niter : ℝ) := by positivity
  have h2n : 2 * (niter : ℝ) < S := by nlinarith
  have hfrac : 2 * (niter : ℝ) / S < 1 := (div_lt_one hSpos).mpr h2n
  have hunion := prob_iInter_ge_sub (P := P) good hmeas (fun _ => 2 / S) hgood
  have hsum : (∑ _k : Fin niter, (2 / S : ℝ)) = 2 * (niter : ℝ) / S := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum, probReal_univ] at hunion

  have hsub : (⋂ k, good k) ⊆ {ω | ‖final ω - c‖ ≤ μ} := by
    intro ω hω
    simp only [Set.mem_iInter] at hω
    exact hacc ω hω
  have hfinal : P.real (⋂ k, good k) ≤ P.real {ω | ‖final ω - c‖ ≤ μ} :=
    measureReal_mono hsub (by finiteness)
  exact ⟨1 - 2 * (niter : ℝ) / S, by linarith, le_trans hunion hfinal⟩

end Qatlib.Papers.CurveletLiu08.MainResults
