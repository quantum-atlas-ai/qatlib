/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroThm8ExactSamplingSubgoalStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroTheorem8FactorSubgoalMont

/-!
# Exact-sampling partition-function estimator

Proves the exact-Gibbs-sampling form of the partition-function estimator in Theorem 8 of
[Montanaro2015]. Exponential ratio observables have partition-function moments; the
cooling-schedule inequality bounds relative variance, amplified factor estimates compose by a
union bound, and their target ratios telescope to the final partition function.

## Main statements

* `theorem8_product_failure` turns the factor failure budgets into a product failure bound of
  one quarter.
* `theorem8_ratio_product` proves the finite telescoping identity for positive successive
  ratios.
* `montanaroTheorem8ExactSamplingSubgoal` proves relative error at most `ε` except with
  probability at most one quarter.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.AmplitudeCore.PayoffMedian

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib
open scoped Classical BigOperators
set_option warningAsError false

/-- Bounds the relative error of a product by `ε` when each positive target factor is estimated
to relative error at most `ε / (2 * ℓ)`, for `ℓ > 0` and `0 < ε < 1`. -/
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

/-- Expresses the probability of an event on one sample as the expectation of its indicator. -/
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

/-- Shows that pointwise implication between events on one sample preserves the ordering of
their probabilities. -/
private theorem event_mono {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (E F : (Fin 1 → X) → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) : p.probEvent E ≤ p.probEvent F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩
  · intro ω _ _
    exact Finset.prod_nonneg fun _ _ => p.nonneg _

/-- Bounds product relative-error failure by `1 / 4` from per-factor failure bounds `1 / (4 *
ℓ)` at relative tolerance `ε / (2 * ℓ)` under the independent product law. -/
theorem theorem8_product_failure {X : Type} [Fintype X] [DecidableEq X]
    (ℓ : ℕ) (ps : Fin ℓ → FinDist X) (obs : Fin ℓ → X → ℝ)
    (means : Fin ℓ → ℝ) (hℓ : 0 < ℓ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hmeans : ∀ i, 0 < means i)
    (hfail : ∀ i, (ps i).probEvent (fun ω : Fin 1 → X =>
      (ε/(2*ℓ))*means i < |obs i (ω 0)-means i|) ≤ 1/(4*ℓ)) :
    (independentSampleLaw ps).probEvent (fun ω : Fin 1 → Fin ℓ → X =>
      ε*∏ i, means i < |∏ i, obs i (ω 0 i)-∏ i, means i|) ≤ 1/4 := by
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

/-- Proves that multiplying the initial positive value by all successive ratios yields the final
value of a finite sequence. -/
theorem theorem8_ratio_product (ℓ : ℕ) (z : Fin (ℓ+1) → ℝ) (hz : ∀ i, 0 < z i) :
    z 0 * (∏ i : Fin ℓ, z i.succ / z i.castSucc) = z (Fin.last ℓ) := by
  have hden : (∏ i : Fin ℓ, z i.castSucc) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _ => hz i.castSucc)
  rw [Finset.prod_div_distrib, ← mul_div_assoc]
  apply (div_eq_iff hden).mpr
  have h := (Fin.prod_univ_succ z).symm.trans (Fin.prod_univ_castSucc z)
  simpa only [mul_comm] using! h

/-- Proves the exact-sampling form of Theorem 8 of [Montanaro2015] under the stated
Gibbs-preparation, cooling-schedule, and estimator-accuracy assumptions. The
cardinality-scaled product of factor medians has relative-error failure probability at most
`1 / 4`. -/
theorem montanaroTheorem8ExactSamplingSubgoal : MontanaroTheorem8ExactSamplingSubgoal := by
  intro Ω _ _ H ℓ β As js B ε N k r hℓ hβ0 hβ hAs hB hε hε1 hN hk hwindow hr hZ hBorn hCheb
  let Y := fun (i : Fin ℓ) (x : Ω) => Real.exp (-((β i.succ-β i.castSucc)*(H x : ℝ)))
  let p := fun i : Fin ℓ => signedMeanSource (As i) (js i) (hAs i)
  let z := fun i : Fin (ℓ+1) => partitionFn H (β i)
  let μ := fun i : Fin ℓ => z i.succ / z i.castSucc
  let ps := fun i : Fin ℓ => theorem6FactorLaw (As i) (js i) (Y i) B N k r
    (hAs i) (fun _ => (Real.exp_pos _).le)
  let obs := fun i : Fin ℓ => theorem6FactorMedian (Y i) B N k r
  have hmeans (i : Fin ℓ) : (p i).expect (Y i) = μ i := by
    have hi := (montanaroChebyshevProductIdentitySubgoal Ω H (β i.castSucc) (β i.succ)
      (hβ i).1 (hβ i).2 (hZ i.castSucc) (hZ i.succ)).1
    change (∑ x, BornProb (ApplyGate (As i) (Ket (js i))) x * Y i x) = _
    simp_rw [hBorn i, div_mul_eq_mul_div, ← Finset.sum_div]
    exact hi
  have hsecond (i : Fin ℓ) : (p i).expect (fun x => (Y i x)^2) =
      partitionFn H (2*β i.succ-β i.castSucc) / z i.castSucc := by
    have hi := (montanaroChebyshevProductIdentitySubgoal Ω H (β i.castSucc) (β i.succ)
      (hβ i).1 (hβ i).2 (hZ i.castSucc) (hZ i.succ)).2
    change (∑ x, BornProb (ApplyGate (As i) (Ket (js i))) x * (Y i x)^2) = _
    simp_rw [hBorn i, div_mul_eq_mul_div, ← Finset.sum_div]
    exact hi
  have hμ (i : Fin ℓ) : 0 < μ i := div_pos (hZ i.succ) (hZ i.castSucc)
  have hvar (i : Fin ℓ) : (p i).variance (Y i) ≤ B*(μ i)^2 := by
    have he := SignedMean.shifted_second_moment (p i) (Y i) 0
    simp only [sub_zero] at he
    change (p i).expect (fun x => (Y i x)^2) = _ at he
    rw [hsecond, hmeans] at he
    have hraw : partitionFn H (2*β i.succ-β i.castSucc) / z i.castSucc ≤ B*(μ i)^2 := by
      dsimp [μ]
      rw [div_pow, ← mul_div_assoc]
      apply (div_le_div_iff₀ (hZ i.castSucc) (sq_pos_of_pos (hZ i.castSucc))).mpr
      have hh := mul_le_mul_of_nonneg_right (hCheb i) (hZ i.castSucc).le
      dsimp [z] at *
      nlinarith
    nlinarith [sq_nonneg (μ i)]
  have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hη : 0 < ε/(2*(ℓ : ℝ)) := div_pos hε (by positivity)
  have hη1 : ε/(2*(ℓ : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2*(ℓ : ℝ))).mpr
    have hl : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hfail (i : Fin ℓ) : (ps i).probEvent (fun ω : Fin 1 → _ =>
      (ε/(2*ℓ))*μ i < |obs i (ω 0)-μ i|) ≤ 1/(4*ℓ) := by
    have hi := montanaroTheorem8FactorSubgoal Ω (As i) (js i) (Y i) B (ε/(2*ℓ)) N k r
      (hAs i) (fun _ => (Real.exp_pos _).le) hB hη hη1 hN hk hwindow
    change 0 < (p i).expect (Y i) →
      (p i).variance (Y i) ≤ B*((p i).expect (Y i))^2 → _ at hi
    rw [hmeans] at hi
    have hi' := (hi (hμ i) (hvar i)).trans hr
    change (ps i).probEvent (fun ω : Fin 1 → _ =>
      (ε/(2*ℓ))*(p i).expect (Y i) < |obs i (ω 0)-(p i).expect (Y i)|) ≤ 1/(4*ℓ) at hi'
    rw [hmeans] at hi'
    exact hi'
  have hp := theorem8_product_failure ℓ ps obs μ hℓ ε hε hε1 hμ hfail
  have hz0 : z 0 = (Fintype.card Ω : ℝ) := by simp [z, partitionFn, hβ0]
  have ht : z (Fin.last ℓ) = (Fintype.card Ω : ℝ)*∏ i, μ i := by
    rw [← theorem8_ratio_product ℓ z hZ, hz0]
  have hc : 0 < (Fintype.card Ω : ℝ) := by rw [← hz0]; exact hZ 0
  apply le_trans _ hp
  apply event_mono
  intro ω hω
  change ε*z (Fin.last ℓ) < |(Fintype.card Ω : ℝ)*∏ i, obs i (ω 0 i)-z (Fin.last ℓ)| at hω
  rw [ht, ← mul_sub, abs_mul, abs_of_pos hc] at hω
  apply (mul_lt_mul_iff_right₀ hc).mp
  simpa only [mul_assoc, mul_left_comm] using! hω

end Qatlib.Concepts.EstimatorLaws.TvStability
