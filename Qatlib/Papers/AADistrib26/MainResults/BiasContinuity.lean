/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeBiasContinuity

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Bias continuity of variance and influence (arXiv:2609.35327v1, §4.1)

Paper-layer statements of Lemma 4.6 of Girish--Mittal--Nehoran--Raz, fixed at
arXiv:2609.35327v1: for a `[0,1]`-valued degree-`d` function the variance and
every coordinate influence under `μ_{n,p}` are Lipschitz in the bias `p`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Lemma 4.6, variance half, with the paper's constant `8d²`: the frozen
estimate is the stronger `4d²` bound. -/
theorem lemma46_variance_bias_lipschitz {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    {q r : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |cubeVar n (muWeight q n) f - cubeVar n (muWeight r n) f| ≤
      8 * (d : ℝ) ^ 2 * |q - r| := by
  have h := cube_mu_variance_bias_lipschitz hb hd hq hr
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hab : (0 : ℝ) ≤ |q - r| := abs_nonneg _
  nlinarith only [h, hd2, hab]

/-- Lemma 4.6, influence half, at the constant `16d²` actually available from
the frozen polynomial-in-bias route. The paper states `8d²`; the gap is the
same factor-two Markov constant as Corollary 2.9. -/
theorem lemma46_influence_bias_lipschitz_sixteen {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (i : Fin n) {q r : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    |cubeInf n (muWeight q n) f i - cubeInf n (muWeight r n) f i| ≤
      16 * (d : ℝ) ^ 2 * |q - r| :=
  cube_mu_influence_bias_lipschitz hb hd i hq hr

end Qatlib.Papers.AADistrib26.MainResults
