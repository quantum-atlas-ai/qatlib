/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceContinuity
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceCloseness
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceMoments

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Slice and product-slice approximation (arXiv:2609.35327v1, §4.2)

Paper-layer statements of Lemma 4.9, Lemma 4.10 and Corollary 4.11 of
Girish--Mittal--Nehoran--Raz, fixed at arXiv:2609.35327v1.

`sliceWeight n t` is the uniform distribution on the Hamming-weight-`t` slice,
`muWeight p n` is `μ_{n,p}` and `nuWeight p n` is `ν_{n,p}`. The constants
`4d²/n`, `8d²/√n` and `48d²/√n` are those printed in the paper.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Lemma 4.9: slice expectations of a `[0,1]`-valued degree-`d` function are
`4d²/n`-Lipschitz in the Hamming level, for levels `t, u ≤ n`. -/
theorem lemma49_slice_expectation_lipschitz {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (t u : ℕ) (ht : t ≤ n) (hu : u ≤ n) :
    |cubeExpect n (sliceWeight n t) f - cubeExpect n (sliceWeight n u) f| ≤
      (4 * (d : ℝ) ^ 2 / (n : ℝ)) * |(t : ℝ) - (u : ℝ)| :=
  cube_slice_expectation_lipschitz hb hd t u ht hu

/-- Lemma 4.9, adjacent-level form: consecutive slice expectations differ by at
most `4d²/n`. -/
theorem lemma49_adjacent_slice_expectation_le {n d k : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (hk0 : 0 < k) (hk : k ≤ n) :
    |cubeExpect n (sliceWeight n k) f - cubeExpect n (sliceWeight n (k - 1)) f| ≤
      4 * (d : ℝ) ^ 2 / (n : ℝ) :=
  cube_slice_adjacent_expectation_bound hb hd hk0 hk

/-- Lemma 4.10: the `μ_{n,p}` and `ν_{n,p}` expectations of a `[0,1]`-valued
degree-`d` function differ by at most `8d²/√n`. -/
theorem lemma410_product_slice_expectation_error {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1)
    (hd : CubeDegreeLE d f) :
    |cubeExpect n (muWeight p n) f - cubeExpect n (nuWeight p n) f| ≤
      8 * (d : ℝ) ^ 2 / Real.sqrt (n : ℝ) :=
  cube_product_slice_expectation_error hp0 hp1 hb hd

/-- Corollary 4.11: both the variance and every coordinate influence of a
`[0,1]`-valued degree-`d` function differ between `μ_{n,p}` and `ν_{n,p}` by at
most `48d²/√n`. -/
theorem corollary411_product_slice_moment_error {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {n d : ℕ} {f : (Fin n → Bool) → ℝ} (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1)
    (hd : CubeDegreeLE d f) :
    |cubeVar n (muWeight p n) f - cubeVar n (nuWeight p n) f| ≤
        48 * (d : ℝ) ^ 2 / Real.sqrt (n : ℝ) ∧
      ∀ i : Fin n,
        |cubeInf n (muWeight p n) f i - cubeInf n (nuWeight p n) f i| ≤
          48 * (d : ℝ) ^ 2 / Real.sqrt (n : ℝ) :=
  cube_product_slice_moment_error hp0 hp1 hb hd

end Qatlib.Papers.AADistrib26.MainResults
