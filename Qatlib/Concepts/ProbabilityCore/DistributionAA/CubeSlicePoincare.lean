/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubePermutationAverage
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSwapInfluence
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductPoincare

/-!
# Slice Poincaré bounds from permutations

The module embeds weighted cube functions into a Euclidean space and controls permutation
differences by decomposing permutations into coordinate swaps. An upper bound on every
coordinate flip influence then bounds every permutation energy.

Averaging gives a coordinate influence estimate for uniform slices and combines it with the
product cube estimate. These finite variance bounds support the analysis of Boolean functions in
the polynomial query setting of [BealsEtAl2001].

## Main statements

* `cube_permutation_energy_le`: permutation energy is at most `4 * n² * M` under a uniform
  influence bound.
* `cube_nu_exists_large_influence`: slice variance is at most `2 * n²` times some coordinate
  influence.
* `cube_both_exists_large_influence`: corresponding existence statements for product and slice
  weights.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- The Euclidean vector with coordinate `x` equal to `Real.sqrt (w x) * f x`. -/
def cubeWeightedVector {n : ℕ} (w : (Fin n → Bool) → ℝ) (f : (Fin n → Bool) → ℝ) :
    EuclideanSpace ℝ (Fin n → Bool) := WithLp.toLp 2 (fun x => Real.sqrt (w x)*f x)

/-- The weighted vector construction preserves subtraction of functions. -/
theorem cube_weighted_vector_sub {n : ℕ} (w : (Fin n → Bool) → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeWeightedVector w (fun x => f x-g x)=cubeWeightedVector w f-cubeWeightedVector w g := by
  ext x
  simp [cubeWeightedVector,mul_sub]

/-- Under a cube probability weight, the squared Euclidean norm of the weighted vector equals
the weighted second moment. -/
theorem cube_weighted_vector_norm_sq {n : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    (f : (Fin n → Bool) → ℝ) : ‖cubeWeightedVector w f‖^2=cubeExpect n w (fun x => f x^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change (Real.sqrt (w x)*f x)^2=w x*f x^2
  rw [mul_pow,Real.sq_sqrt (hw.1 x)]

/-- For `0 < p < 1`, permuting coordinates of a function preserves its weighted vector norm
under `nuWeight p n`. -/
theorem cube_weighted_permutation_norm {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (e : Equiv.Perm (Fin n)) (f : (Fin n → Bool) → ℝ) :
    ‖cubeWeightedVector (nuWeight p n) (fun x => f (cubePermute e x))‖ =
      ‖cubeWeightedVector (nuWeight p n) f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [cube_weighted_vector_norm_sq (nuWeight_cubeWeight hp0 hp1 n),
    cube_weighted_vector_norm_sq (nuWeight_cubeWeight hp0 hp1 n)]
  exact cube_expect_permutation p e (fun x => f x^2)

/-- The swap factor list produced from a list containing every moved point has length at most
that list's length. -/
theorem cube_swap_factors_length {α : Type} [DecidableEq α] (l : List α) (e : Equiv.Perm α)
    (he : ∀ {x}, e x ≠ x → x ∈ l) : (Equiv.Perm.swapFactorsAux l e he).val.length ≤ l.length := by
  induction l generalizing e with
  | nil => simp [Equiv.Perm.swapFactorsAux]
  | cons x l ih =>
    unfold Equiv.Perm.swapFactorsAux
    split_ifs with hx
    · have hf : ∀ {y}, e y ≠ y → y ∈ l := fun {y} hy =>
        List.mem_of_ne_of_mem (fun h : y=x => by simp [h,hx.symm] at hy) (he hy)
      exact (ih e hf).trans (Nat.le_succ _)
    · have hf : ∀ {y}, (Equiv.swap x (e x)*e) y ≠ y → y ∈ l := fun {y} hy =>
        List.mem_of_ne_of_mem (Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy).2
          (he (Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy).1)
      simpa only [List.length_cons] using Nat.succ_le_succ (ih _ hf)

/-- For `0 < p < 1`, if all slice coordinate influences are bounded by `M ≥ 0`, every
permutation has expected squared function difference at most `4 * n² * M`. -/
theorem cube_permutation_energy_le {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (Fin n → Bool) → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i, cubeInf n (nuWeight p n) f i ≤ M) (e : Equiv.Perm (Fin n)) :
    cubeExpect n (nuWeight p n) (fun x => (f x-f (cubePermute e x))^2) ≤ 4*(n : ℝ)^2*M := by
  let w := nuWeight p n
  have hw := nuWeight_cubeWeight hp0 hp1 n
  let L := (Equiv.Perm.swapFactors e).val
  have hL : L.length ≤ n := by
    have he :=
        cube_swap_factors_length (Finset.univ.sort) e
        (fun {_ _} => (Finset.mem_sort _).2 (Finset.mem_univ _))
    simpa [L,Equiv.Perm.swapFactors] using he
  have hprod : L.prod=e := (Equiv.Perm.swapFactors e).property.1
  have hswaps : ∀ g ∈ L, Equiv.Perm.IsSwap g := (Equiv.Perm.swapFactors e).property.2
  have hswap (g : Equiv.Perm (Fin n)) (hg : Equiv.Perm.IsSwap g) :
      ‖cubeWeightedVector w (fun x => f x-f (cubePermute g x))‖ ≤ 2*Real.sqrt M := by
    obtain ⟨i,j,_hij,rfl⟩ := hg
    have he := cube_swap_influence_le hp0 hp1 (f := f) i j
    have hn := cube_weighted_vector_norm_sq hw (fun x => f x-f (cubePermute (Equiv.swap i j) x))
    have hpnt : (fun x => f x-f (cubePermute (Equiv.swap i j) x)) = (fun x => f x-f (cubeSwap x i j)) := by
      funext x
      rw [cube_swap_as_permutation]
      rfl
    have heE : cubeExpect n (nuWeight p n) (fun x => (f x-f (cubePermute (Equiv.swap i j) x))^2) =
        cubeExpect n (nuWeight p n) (fun x => (f x-f (cubeSwap x i j))^2) := by
      congr 1
      funext x
      rw [cube_swap_as_permutation]
      rfl
    have hb : ‖cubeWeightedVector w (fun x => f x-f (cubePermute (Equiv.swap i j) x))‖^2 ≤ 4*M := by
      rw [hn,heE]
      linarith [hM i,hM j]
    nlinarith only [hb,Real.sq_sqrt hM0,Real.sqrt_nonneg M,
      norm_nonneg (cubeWeightedVector w (fun x => f x-f (cubePermute (Equiv.swap i j) x)))]
  have hpath (l : List (Equiv.Perm (Fin n))) (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) :
      ‖cubeWeightedVector w (fun x => f x-f (cubePermute l.prod x))‖ ≤ (l.length : ℝ)*(2*Real.sqrt M) := by
    induction l with
    | nil =>
      have hz : cubeWeightedVector w (fun x => f x-f (cubePermute ([] : List (Equiv.Perm (Fin n))).prod x))=0 := by
        ext x
        change Real.sqrt (w x)*(f x-f x)=0
        ring
      rw [hz]
      simp
    | cons g l ih =>
      have h0 := hswap g (hl g (by simp))
      have h1 := ih (fun r hr => hl r (List.mem_cons_of_mem _ hr))
      have hre : (fun x => f x-f (cubePermute (g*l.prod) x)) =
          (fun x => (f x-f (cubePermute g x))+(f (cubePermute g x)-f (cubePermute l.prod (cubePermute g x)))) := by
        funext x
        have hc : cubePermute (g*l.prod) x=cubePermute l.prod (cubePermute g x) := by
          ext i; rfl
        rw [hc]
        ring
      have hvec : cubeWeightedVector w (fun x => (f x-f (cubePermute g x))+
          (f (cubePermute g x)-f (cubePermute l.prod (cubePermute g x)))) =
          cubeWeightedVector w (fun x => f x-f (cubePermute g x))+
            cubeWeightedVector w (fun x => (fun y => f y-f (cubePermute l.prod y)) (cubePermute g x)) := by
        ext x
        change Real.sqrt (w x)*((f x-f (cubePermute g x))+
          (f (cubePermute g x)-f (cubePermute l.prod (cubePermute g x)))) =
          Real.sqrt (w x)*(f x-f (cubePermute g x))+
          Real.sqrt (w x)*(f (cubePermute g x)-f (cubePermute l.prod (cubePermute g x)))
        ring
      simp only [List.prod_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      rw [hre,hvec]
      apply (norm_add_le _ _).trans
      rw [cube_weighted_permutation_norm hp0 hp1 g (fun x => f x-f (cubePermute l.prod x))]
      linarith only [h0,h1]
  have hp := hpath L hswaps
  rw [hprod] at hp
  have hlen : (L.length : ℝ) ≤ n := by exact_mod_cast hL
  have hbound := hp.trans (mul_le_mul_of_nonneg_right hlen (by positivity))
  rw [← cube_weighted_vector_norm_sq hw]
  have hs := Real.sq_sqrt hM0
  have hsq :=
      mul_self_le_mul_self
      (norm_nonneg (cubeWeightedVector w (fun x => f x-f (cubePermute e x)))) hbound
  nlinarith only [hsq,hs]

/-- For `n > 0` and `0 < p < 1`, the variance on the selected uniform slice is at most `2 * n²`
times some coordinate flip influence. -/
theorem cube_nu_exists_large_influence {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) (f : (Fin n → Bool) → ℝ) :
    ∃ i : Fin n, cubeVar n (nuWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (nuWeight p n) f i := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => cubeInf n (nuWeight p n) f i) Finset.univ_nonempty
  let M := cubeInf n (nuWeight p n) f i
  have hM0 : 0 ≤ M := cubeInf_nonneg n (nuWeight_cubeWeight hp0 hp1 n) f i
  have he (e) := cube_permutation_energy_le hp0 hp1 f M hM0 (fun j => hmax j (Finset.mem_univ j)) e
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => he e)
  have havg :=
      mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ by positivity)
  rw [cube_permutation_pair_energy hp0 hp1 f] at havg
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,← mul_assoc,inv_mul_cancel₀ hc,one_mul] at havg
  exact ⟨i,by dsimp [M] at havg; linarith only [havg]⟩

/-- For `n > 0` and `0 < p < 1`, both product and slice variances are bounded by `2 * n²` times
a coordinate influence, with a coordinate chosen separately for each law. -/
theorem cube_both_exists_large_influence {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) (f : (Fin n → Bool) → ℝ) :
    (∃ i : Fin n, cubeVar n (muWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (muWeight p n) f i) ∧
    (∃ i : Fin n, cubeVar n (nuWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (nuWeight p n) f i) :=
  ⟨cube_mu_exists_large_influence hp0 hp1 hn f,cube_nu_exists_large_influence hp0 hp1 hn f⟩

end Qatlib.Concepts.ProbabilityCore.DistributionAA
