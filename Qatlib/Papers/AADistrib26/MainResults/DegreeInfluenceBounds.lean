/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSwapInfluence
import Qatlib.Concepts.ProbabilityCore.DistributionAA.DegreeInfluenceBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Degree and influence bounds (arXiv:2609.35327v1, §2.4)

Paper-layer statements of Lemma 2.6, Lemma 2.10, Lemma 2.11 and Lemma 2.12 of
Girish--Mittal--Nehoran--Raz, *Distributional Variants of the
Aaronson--Ambainis Conjecture*, fixed at arXiv:2609.35327v1.

The Boolean cube is the frozen representation `Fin n → Bool`; `nuWeight p n`
is the uniform slice `ν_{n,p}` at Hamming weight `⌊p n⌋`, `cubeInf` is the
coordinate influence of Definition 2.5 and `cubeTotalInf` its total influence.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Lemma 2.6, first inequality: for the slice distribution `ν_{n,p}`, the
squared swap difference of coordinates `i` and `j` is at most twice the sum of
their two coordinate influences. -/
theorem lemma26_swap_influence_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (Fin n → Bool) → ℝ) (i j : Fin n) :
    cubeExpect n (nuWeight p n) (fun x => (f x - f (cubeSwap x i j)) ^ 2) ≤
      2 * (cubeInf n (nuWeight p n) f i + cubeInf n (nuWeight p n) f j) :=
  cube_swap_influence_le hp0 hp1 i j

/-- Lemma 2.6, second inequality: the swap-influence is at most four times the
maximum coordinate influence. -/
theorem lemma26_swap_influence_le_four_max {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) (f : (Fin n → Bool) → ℝ) (i j : Fin n) :
    cubeExpect n (nuWeight p n) (fun x => (f x - f (cubeSwap x i j)) ^ 2) ≤
      4 * (Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (fun k : Fin n => cubeInf n (nuWeight p n) f k)) := by
  let H : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let M := Finset.univ.sup' H (fun k : Fin n => cubeInf n (nuWeight p n) f k)
  have h := lemma26_swap_influence_le hp0 hp1 f i j
  have hw := nuWeight_cubeWeight hp0 hp1 n
  have hi : cubeInf n (nuWeight p n) f i ≤ M := by
    simpa only [M] using Finset.le_sup' (fun k : Fin n => cubeInf n (nuWeight p n) f k)
      (Finset.mem_univ i)
  have hj : cubeInf n (nuWeight p n) f j ≤ M := by
    simpa only [M] using Finset.le_sup' (fun k : Fin n => cubeInf n (nuWeight p n) f k)
      (Finset.mem_univ j)
  have hi0 := cubeInf_nonneg n hw f i
  have hj0 := cubeInf_nonneg n hw f j
  have hM : 0 ≤ M := le_trans hi0 hi
  nlinarith only [h, hi, hj, hi0, hj0, hM]

/-- Lemma 2.10: for a `[0,1]`-valued multilinear degree-`d` function, the sum
of flip differences over any coordinate set has absolute value at most `2d²`. -/
theorem lemma210_flip_sum_le_two {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (x : Fin n → Bool) (A : Finset (Fin n)) :
    |∑ i ∈ A, (f x - f (cubeFlip x i))| ≤ 2 * (d : ℝ) ^ 2 :=
  cube_flip_sum_le_two hb hd x A

/-- Lemma 2.11: under any distribution on `{0,1}^n`, a `[0,1]`-valued degree-`d`
function has total influence at most `4d²`. This sharpens the frozen
`cube_total_inf_le` (constant `8d²`) by keeping the pointwise estimate. -/
theorem lemma211_total_influence_le {n d : ℕ} {w : (Fin n → Bool) → ℝ}
    (hw : CubeWeight n w) {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x : Fin n → Bool, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) :
    cubeTotalInf n w f ≤ 4 * (d : ℝ) ^ 2 := by
  unfold cubeTotalInf cubeInf cubeExpect
  rw [Finset.sum_comm]
  calc
    _ = ∑ x, w x * (∑ i, (f x - f (cubeFlip x i)) ^ 2) := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, w x * (4 * (d : ℝ) ^ 2) :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (cube_point_flip_square_sum_le hb hd x) (hw.1 x)
    _ = 4 * (d : ℝ) ^ 2 := by rw [← Finset.sum_mul, hw.2, one_mul]

/-- Lemma 2.12: for `λ_n` equal to either `μ_{n,p}` or `ν_{n,p}`, some
coordinate has influence at least `Var(λ_n)[f] / (2n²)`. -/
theorem lemma212_exists_influence_ge_var_div_two_n_sq {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hn : 0 < n) (f : (Fin n → Bool) → ℝ) :
    (∃ i : Fin n,
        cubeVar n (muWeight p n) f / (2 * (n : ℝ) ^ 2) ≤ cubeInf n (muWeight p n) f i) ∧
      (∃ i : Fin n,
        cubeVar n (nuWeight p n) f / (2 * (n : ℝ) ^ 2) ≤ cubeInf n (nuWeight p n) f i) := by
  have hpos : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by positivity
  obtain ⟨hm, hn'⟩ := exists_inf_ge_var_div_two_n_sq hp0 hp1 hn (f := f)
  constructor
  · obtain ⟨i, hi⟩ := hm
    refine ⟨i, (div_le_iff₀ hpos).2 ?_⟩
    calc cubeVar n (muWeight p n) f ≤ 2 * (n : ℝ) ^ 2 * cubeInf n (muWeight p n) f i := hi
      _ = cubeInf n (muWeight p n) f i * (2 * (n : ℝ) ^ 2) := by ring
  · obtain ⟨i, hi⟩ := hn'
    refine ⟨i, (div_le_iff₀ hpos).2 ?_⟩
    calc cubeVar n (nuWeight p n) f ≤ 2 * (n : ℝ) ^ 2 * cubeInf n (nuWeight p n) f i := hi
      _ = cubeInf n (nuWeight p n) f i * (2 * (n : ℝ) ^ 2) := by ring

end Qatlib.Papers.AADistrib26.MainResults
