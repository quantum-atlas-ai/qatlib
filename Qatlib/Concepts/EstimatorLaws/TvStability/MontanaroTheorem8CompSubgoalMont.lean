/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroTheorem8CompSubgoalStat
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound

/-!
# Composition of relative factor estimates

Proves that accurate factor estimates give an accurate product, then combines the individual
failure probabilities using a union bound. This isolates the multiplicative error step of the
partition-function estimator in Theorem 8 of [Montanaro2015].

## Main statements

* `product_accuracy` turns per-factor relative error `ε / (2 * ℓ)` into relative product error
  at most `ε`.
* `montanaroTheorem8CompositionSubgoal` bounds the product failure probability by one quarter
  when each factor fails with probability at most `1 / (4 * ℓ)`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib
open scoped Classical BigOperators
set_option autoImplicit false

/-- Bounds the relative error of a product by `ε` when its positive target factors each have
relative error at most `ε / (2 * ℓ)`, with `ℓ > 0` and `0 < ε < 1`. -/
private theorem product_accuracy (ℓ : ℕ) (hℓ : 0 < ℓ) (v μ : Fin ℓ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hμ : ∀ i, 0 < μ i)
    (hgood : ∀ i, |v i - μ i| ≤ (ε/(2*ℓ))*μ i) :
    |∏ i, v i - ∏ i, μ i| ≤ ε*∏ i, μ i := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  let a := ε/(2*ℓ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have he : (ℓ : ℝ)*a = ε/2 := by dsimp [a]; field_simp
  have hl : 1-ε/2 ≤ (1-a)^ℓ := by
    have hh := one_add_mul_le_pow (show (-2 : ℝ) ≤ -a by linarith) ℓ
    simpa only [mul_neg, ← sub_eq_add_neg, he] using! hh
  have hu : (1+a)^ℓ ≤ 1+ε := by
    have hi : (1-a) ≤ (1+a)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 1+a)]
      nlinarith [sq_nonneg a]
    have hb := one_add_mul_sub_le_pow
      (show (-1 : ℝ) ≤ (1+a)⁻¹ from le_trans
        (show (-1 : ℝ) ≤ 0 by norm_num) (show 0 ≤ (1+a)⁻¹ by positivity)) ℓ
    have hmul := mul_le_mul_of_nonneg_left hi (le_of_lt hℓ0)
    have hbase : 1-ε/2 ≤ ((1+a)^ℓ)⁻¹ := by
      rw [← inv_pow]
      nlinarith
    have hY : (0 : ℝ) < (1+a)^ℓ := pow_pos (by positivity) _
    have hx := mul_le_mul_of_nonneg_right hbase (le_of_lt hY)
    rw [inv_mul_cancel₀ (ne_of_gt hY)] at hx
    have hd : 0 < 1-ε/2 := by linarith
    apply (mul_le_mul_iff_right₀ hd).1
    nlinarith
  have hv (i : Fin ℓ) : μ i*(1-a) ≤ v i ∧ v i ≤ μ i*(1+a) := by
    have hh := abs_le.mp (hgood i)
    change - (a*μ i) ≤ v i-μ i ∧ v i-μ i ≤ a*μ i at hh
    constructor <;> nlinarith [hh.1, hh.2]
  have hv0 (i : Fin ℓ) : 0 ≤ v i :=
    (mul_nonneg (le_of_lt (hμ i)) (by linarith : 0 ≤ 1-a)).trans (hv i).1
  have hlo : (1-a)^ℓ * ∏ i, μ i ≤ ∏ i, v i := by
    have hp := Finset.prod_le_prod₀
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) =>
        mul_nonneg (le_of_lt (hμ i)) (by linarith : 0 ≤ 1-a))
      (fun i _ => (hv i).1)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_comm] using! hp
  have hhi : ∏ i, v i ≤ (1+a)^ℓ * ∏ i, μ i := by
    have hp := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => hv0 i) (fun i _ => (hv i).2)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_comm] using! hp
  have hP : 0 ≤ ∏ i, μ i := Finset.prod_nonneg fun i _ => le_of_lt (hμ i)
  have hl' := mul_le_mul_of_nonneg_right hl hP
  have hu' := mul_le_mul_of_nonneg_right hu hP
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Expresses an event on a single sample as the expectation of its indicator under the finite
law. -/
private theorem event_one_expect {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) [DecidablePred E] :
    p.probEvent (fun ω : Fin 1 → X => E (ω 0)) = p.expect (fun x => if E x then 1 else 0) := by
  let e : (Fin 1 → X) ≃ X :=
    { toFun := fun ω => ω 0
      invFun := fun x _ => x
      left_inv := by
        intro ω
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := fun _ => rfl }
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter,
    ← e.symm.sum_comp (fun ω => if E (ω 0) then p.probOf ω else 0)]
  simp only [e, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf, Fin.prod_univ_one,
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_ite, mul_one, mul_zero]
  rfl

/-- Shows that implication between events on a single sample implies the corresponding
inequality between their probabilities. -/
private theorem event_mono {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (E F : (Fin 1 → X) → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) : p.probEvent E ≤ p.probEvent F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩
  · intro ω _ _
    exact Finset.prod_nonneg fun _ _ => p.nonneg _

/-- Proves the relative product-composition contract used in Theorem 8 of [Montanaro2015], using
deterministic product accuracy and a union bound over factor failures. -/
theorem montanaroTheorem8CompositionSubgoal : MontanaroTheorem8CompositionSubgoal := by
  intro X _ _ ℓ ps obs means hℓ ε hε hε1 _hmean hmeans hfail
  let E := fun (i : Fin ℓ) (ω : Fin 1 → Fin ℓ → X) =>
    (ε/(2*ℓ))*means i < |obs i (ω 0 i)-means i|
  have hsub (ω : Fin 1 → Fin ℓ → X)
      (hb : ε*∏ i, means i < |∏ i, obs i (ω 0 i)-∏ i, means i|) : ∃ i, E i ω := by
    by_contra h
    have hg (i : Fin ℓ) : |obs i (ω 0 i)-means i| ≤ (ε/(2*ℓ))*means i :=
      le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact (not_lt_of_ge (product_accuracy ℓ hℓ (fun i => obs i (ω 0 i))
      means ε hε hε1 hmeans hg)) hb
  have hmarg (i : Fin ℓ) : (independentSampleLaw ps).probEvent (E i) =
      (ps i).probEvent (fun ω : Fin 1 → X => (ε/(2*ℓ))*means i < |obs i (ω 0)-means i|) := by
    dsimp only [E]
    rw [event_one_expect (independentSampleLaw ps)
      (fun u : Fin ℓ → X => (ε/(2*ℓ))*means i < |obs i (u i)-means i|),
      event_one_expect (ps i) (fun x => (ε/(2*ℓ))*means i < |obs i x-means i|)]
    exact independentSampleLaw_expect_coord ps i
      (fun x => if (ε/(2*ℓ))*means i < |obs i x-means i| then 1 else 0)
  calc
    _ ≤ (independentSampleLaw ps).probEvent (fun ω => ∃ i, E i ω) :=
      event_mono _ _ _ hsub
    _ ≤ ∑ i, (independentSampleLaw ps).probEvent (E i) := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.union_bound _ E
    _ ≤ ∑ _i : Fin ℓ, (1 : ℝ)/(4*ℓ) :=
      Finset.sum_le_sum fun i _ => (by rw [hmarg]; exact hfail i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
      field_simp

end Qatlib.Concepts.EstimatorLaws.TvStability
