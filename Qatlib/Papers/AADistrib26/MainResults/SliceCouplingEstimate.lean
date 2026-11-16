/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeHammingMoments
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceCloseness

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Analytic ingredient of the slice/product coupling (arXiv:2609.35327v1, Lemma 3.9)

Lemma 3.9 of Girish--Mittal--Nehoran--Raz, fixed at arXiv:2609.35327v1,
constructs a coupling `(X, Y)` with `X ~ ν_{n,p}` and `Y ~ μ_{n,p}` and bounds
the conditional disagreement probability by `4/√(a n)`, `a = min(p, 1-p)`.
Its proof uses the Hamming weight `W ~ Binomial(n,p)` of the product sample and
the estimate `E|W - ⌊pn⌋| ≤ 1 + √(a n)`.

This file proves that scalar estimate from the frozen Hamming moments. It is
recorded as partial support: the coupling construction itself, its marginals
and the conditional disagreement bound are not formalized here.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Lemma 3.9, analytic ingredient: under `μ_{n,p}`, the expected distance of
the Hamming weight from `⌊pn⌋` is at most `1 + √(n p (1-p))`. -/
theorem lemma39_expected_hamming_deviation {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    cubeExpect n (muWeight p n)
        (fun x => |(cubeHamming x : ℝ) - (Nat.floor (p * (n : ℝ)) : ℝ)|) ≤
      1 + Real.sqrt ((n : ℝ) * p * (1 - p)) := by
  let w := muWeight p n
  let g : (Fin n → Bool) → ℝ := fun x => (cubeHamming x : ℝ)
  let c : ℝ := (Nat.floor (p * (n : ℝ)) : ℝ)
  let a : ℝ := p * (1 - p)
  have hw := muWeight_cubeWeight hp0 hp1 n
  have hvar := cube_mu_hamming_variance hp0 hp1 n
  have hmean := cube_mu_hamming_mean p n
  have hvar' : cubeVar n w g = (n : ℝ) * p * (1 - p) := by
    simpa only [w, g] using hvar
  have hmean' : cubeExpect n w g = (n : ℝ) * p := by
    simpa only [w, g] using hmean
  have hsecond : cubeExpect n w (fun x => (g x - c) ^ 2) =
      cubeExpect n w (fun x => g x ^ 2) - 2 * c * cubeExpect n w g + c ^ 2 := by
    have hpt : (fun x => (g x - c) ^ 2) =
        fun x => (g x ^ 2 - (2 * c) * g x) + c ^ 2 := by
      ext x
      ring
    rw [hpt, cube_expect_add, cube_expect_sub, cube_expect_const_mul]
    have hconst : (∑ x : Fin n → Bool, w x * c ^ 2) = c ^ 2 := by
      rw [← Finset.sum_mul, hw.2, one_mul]
    simp only [w, cubeExpect] at hconst ⊢
    rw [hconst]
  have hsecond_moment : cubeExpect n w (fun x => g x ^ 2) =
      (n : ℝ) * a + ((n : ℝ) * p) ^ 2 := by
    have hv := hvar'
    rw [cube_var_eq_second_moment_sub_sq n hw g, hmean'] at hv
    dsimp [a] at hv ⊢
    linarith
  have hfloor : |(n : ℝ) * p - c| ≤ 1 := by
    have h0 := Nat.floor_le (show 0 ≤ p * (n : ℝ) by positivity)
    have h1 := Nat.lt_floor_add_one (p * (n : ℝ))
    have hnonneg : 0 ≤ (n : ℝ) * p - c := by
      dsimp [c]
      nlinarith
    rw [abs_of_nonneg hnonneg]
    dsimp [c]
    linarith
  have hfloor_sq : ((n : ℝ) * p - c) ^ 2 ≤ 1 := by
    have h := abs_le.1 hfloor
    nlinarith only [h.1, h.2]
  have hsquare : cubeExpect n w (fun x => (g x - c) ^ 2) ≤ (n : ℝ) * a + 1 := by
    rw [hsecond, hsecond_moment, hmean']
    nlinarith only [hfloor_sq]
  have hjensen : (cubeExpect n w (fun x => |g x - c|)) ^ 2 ≤
      cubeExpect n w (fun x => (g x - c) ^ 2) := by
    have hv := cubeVar_nonneg n hw (fun x => |g x - c|)
    rw [cube_var_eq_second_moment_sub_sq n hw] at hv
    have hsq : cubeExpect n w (fun x => |g x - c| ^ 2) =
        cubeExpect n w (fun x => (g x - c) ^ 2) := by
      congr 1
      ext x
      exact sq_abs (g x - c)
    rw [hsq] at hv
    nlinarith
  have hnonneg : 0 ≤ cubeExpect n w (fun x => |g x - c|) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (abs_nonneg _)
  have hsq : (cubeExpect n w (fun x => |g x - c|)) ^ 2 ≤ (n : ℝ) * a + 1 :=
    le_trans hjensen hsquare
  have hroot : cubeExpect n w (fun x => |g x - c|) ≤ Real.sqrt ((n : ℝ) * a + 1) :=
    Real.le_sqrt_of_sq_le hsq
  have hsplit : Real.sqrt ((n : ℝ) * a + 1) ≤ Real.sqrt ((n : ℝ) * a) + 1 := by
    have h0 : 0 ≤ (n : ℝ) * a := by positivity
    have h1 : 0 ≤ Real.sqrt ((n : ℝ) * a) := Real.sqrt_nonneg _
    have hs := Real.sq_sqrt h0
    have hs' : (Real.sqrt ((n : ℝ) * a)) ^ 2 = (n : ℝ) * a := hs
    have hmono : ((n : ℝ) * a + 1) ≤ (Real.sqrt ((n : ℝ) * a) + 1) ^ 2 := by
      nlinarith [hs', h1]
    calc Real.sqrt ((n : ℝ) * a + 1) ≤ Real.sqrt ((Real.sqrt ((n : ℝ) * a) + 1) ^ 2) :=
          Real.sqrt_le_sqrt hmono
      _ = Real.sqrt ((n : ℝ) * a) + 1 := by
          rw [Real.sqrt_sq (by linarith)]
  calc cubeExpect n w (fun x => |g x - c|) ≤ Real.sqrt ((n : ℝ) * a + 1) := hroot
    _ ≤ Real.sqrt ((n : ℝ) * a) + 1 := hsplit
    _ = 1 + Real.sqrt ((n : ℝ) * p * (1 - p)) := by
      dsimp [a]
      ring_nf

end Qatlib.Papers.AADistrib26.MainResults
