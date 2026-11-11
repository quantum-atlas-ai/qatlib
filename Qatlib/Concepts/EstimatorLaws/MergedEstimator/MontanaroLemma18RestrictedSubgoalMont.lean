/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.MergedEstimator.MontanaroLemma18RestrictedSubgoalStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroLemma18AELawTVSubgoalMont
import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport

/-!
# Restricted signed-estimator transport

Proves the restricted Lemma 18 transport bound for the native signed rational estimator. The
proof compresses its initial sample to a payoff value, controls each centered
amplitude-estimation record, and transfers the median failure event through independent product
laws, following the stability argument of [Montanaro2015].

## Main statements

* `montanaroLemma18RestrictedSubgoal` bounds failure under the first preparation around the
  second preparation's mean by intrinsic median failure plus explicit terms in `γ` and `sqrt γ`.
* `layer_ae_l1`, `centered_layer_l1`, and `compressed_record_l1` propagate payoff-value
  perturbations through the estimator records.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeSearch.NativeMean
open Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.MonteCarloMean.PayoffEncoding
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.EstimatorLaws.MergedEstimator
open Matrix
open scoped Classical BigOperators
set_option warningAsError false

/-- Bounds the difference of expectations of a test valued in `[0, 1]` by half the L1 distance
between two finite probability laws. -/
private theorem bounded_test_tv {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1) :
    |p.expect w - q.expect w| ≤ (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x| := by
  have he : p.expect w - q.expect w =
      ∑ x, (p.prob x - q.prob x) * (w x - 1 / 2) := by
    simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_sub, sub_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, p.sum_one, q.sum_one, one_mul, sub_self, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ x, |(p.prob x - q.prob x) * (w x - 1 / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |p.prob x - q.prob x| * (1 / 2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [(hw x).1], by linarith [(hw x).2]⟩
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Identifies the expectation of a test on independent samples from a pushforward law with its
expectation after applying the map coordinatewise to independent source samples. -/
private theorem fresh_pushforward_test {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (p : FinDist X) (q : FinDist Y) (g : X → Y)
    (hq : ∀ y, q.prob y = ∑ x, if g x = y then p.prob x else 0)
    (n : ℕ) (w : (Fin n → Y) → ℝ) :
    (independentSampleLaw (fun _ : Fin n => q)).expect w =
      (independentSampleLaw (fun _ : Fin n => p)).expect
        (fun ξ => w (fun i => g (ξ i))) := by
  apply Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.expect_eq_of_pushforward
  intro η
  have hpoint (ξ : Fin n → X) :
      (if (fun i => g (ξ i)) = η then ∏ i, p.prob (ξ i) else 0) =
        ∏ i, if g (ξ i) = η i then p.prob (ξ i) else 0 := by
    by_cases h : (fun i => g (ξ i)) = η
    · simp only [congrFun h, if_true]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, g (ξ i) ≠ η i := by
        by_contra hn
        exact h (funext (fun i => by simpa using! (not_exists.mp hn) i))
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg hi
  change (∏ i : Fin n, q.prob (η i)) =
    ∑ ξ : Fin n → X, if (fun i => g (ξ i)) = η then ∏ i, p.prob (ξ i) else 0
  simp_rw [hpoint]
  have hswap : (∑ ξ : Fin n → X, ∏ i, if g (ξ i) = η i then p.prob (ξ i) else 0) =
      ∑ ξ ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset X)),
        ∏ i, if g (ξ i) = η i then p.prob (ξ i) else 0 :=
    Finset.sum_congr rfl (fun _ _ => rfl)
  rw [hswap]
  calc
    _ = ∏ i : Fin n, (∑ x : X, if g x = η i then p.prob x else 0) :=
      Finset.prod_congr rfl (fun i _ => hq (η i))
    _ = _ := Finset.prod_univ_sum (t := fun _ : Fin n => (Finset.univ : Finset X))
      (f := fun i x => if g x = η i then p.prob x else 0)

/-- The finite subtype of rational values attained by the payoff function. -/
private abbrev Values {I : Type} [Fintype I] (f : I → ℚ) :=
  ↥(Finset.image f Finset.univ)

/-- Maps a basis outcome to its payoff value in the finite image subtype. -/
private def valueMap {I : Type} [Fintype I] (f : I → ℚ) (i : I) : Values f :=
  ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- Regroups a finite weighted payoff sum into sums over fibers of the payoff function. -/
private theorem value_fiber_sum {I : Type} [Fintype I] [DecidableEq I]
    (f : I → ℚ) (p : I → ℝ) (w : ℚ → ℝ) :
    (∑ i, p i * w (f i)) = ∑ v ∈ Finset.image f Finset.univ,
      (∑ i ∈ Finset.univ.filter (fun i => f i = v), p i) * w v := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.image f Finset.univ) (g := f)
    (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) (fun i => p i * w (f i))]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Bounds the change of a `[0, 1]`-valued payoff test by the unhalved payoff-value L1 distance
between two preparations. -/
private theorem value_weight_shift {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (w : ℚ → ℝ)
    (hw : ∀ v, 0 ≤ w v ∧ w v ≤ 1) :
    |(∑ i, BornProb (ApplyGate A₁ (Ket j)) i * w (f i)) -
      (∑ i, BornProb (ApplyGate A₂ (Ket j)) i * w (f i))| ≤ payoffValueL1Dist A₁ A₂ j f := by
  rw [value_fiber_sum, value_fiber_sum, ← Finset.sum_sub_distrib]
  unfold payoffValueL1Dist
  calc
    _ ≤ ∑ v ∈ Finset.image f Finset.univ,
        |(∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₁ (Ket j)) i) * w v -
          (∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₂ (Ket j)) i) * w v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      rw [← sub_mul, abs_mul, abs_of_nonneg (hw v).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hw v).2

/-- The native layered law for the nonnegative positive or negative part of a payoff centered at
`v` and divided by `4 * σ`. -/
private noncomputable def centeredLayerLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (v : ℚ) (positive : Bool) : FinDist (LayerRecord k) :=
  nativeLayerLaw A j (fun i => max 0
    ((if positive then f i - v else v - f i) / (4 * σ))) k
    (fun l => nativeLayerPrepare_unitary A _ k l hA (fun _ => le_max_left _ _))

/-- The native signed law using the standard unitarity proofs for its positive and negative
centered layer preparations. -/
private noncomputable def canonicalSignedLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :=
  nativeSignedLaw A j f σ k hA
    (fun x l => nativeLayerPrepare_unitary A (fun i => max 0 ((f i - f x) / (4 * σ))) k l hA (fun _ => le_max_left _ _))
    (fun x l => nativeLayerPrepare_unitary A (fun i => max 0 ((f x - f i) / (4 * σ))) k l hA (fun _ => le_max_left _ _))

/-- Replaces the initial basis index in a signed estimator record by its payoff value while
retaining both layer records. -/
private def recordValueMap {I : Type} [Fintype I] (f : I → ℚ) (k : ℕ)
    (ω : I × (LayerRecord k × LayerRecord k)) : Values f × (LayerRecord k × LayerRecord k) :=
  (valueMap f ω.1, ω.2)

/-- Factors the probability of a compressed signed record into the measurement mass of its
payoff fiber and the two centered layer probabilities. -/
private theorem native_value_record_fiber {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (q : FinDist (Values f × (LayerRecord k × LayerRecord k)))
    (hq : ∀ y, q.prob y = ∑ x, if recordValueMap f k x = y then
      (canonicalSignedLaw A j f σ k hA).prob x else 0)
    (v : Values f) (u w : LayerRecord k) :
    q.prob (v, (u, w)) =
      (∑ i ∈ Finset.univ.filter (fun i => f i = v.val), BornProb (ApplyGate A (Ket j)) i) *
        (centeredLayerLaw A j f σ k hA v.val true).prob u *
        (centeredLayerLaw A j f σ k hA v.val false).prob w := by
  have hv (i : I) : valueMap f i = v ↔ f i = v.val := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact fun h => Subtype.ext h
  rw [hq]
  simp only [Fintype.sum_prod_type, recordValueMap, Prod.mk.injEq]
  have ht (i : I) :
      (∑ a : LayerRecord k, ∑ b : LayerRecord k,
        if valueMap f i = v ∧ a = u ∧ b = w then
          (canonicalSignedLaw A j f σ k hA).prob (i, (a, b)) else 0) =
      if f i = v.val then
        BornProb (ApplyGate A (Ket j)) i *
          (centeredLayerLaw A j f σ k hA v.val true).prob u *
          (centeredLayerLaw A j f σ k hA v.val false).prob w else 0 := by
    by_cases hi : f i = v.val
    · simp only [hv, hi, true_and]
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_const_zero]
      simp only [canonicalSignedLaw, nativeSignedLaw, centeredLayerLaw, hi, Bool.false_eq_true,
        if_true, if_false, ApplyGate]
    · simp only [hv, hi, false_and, if_false, Finset.sum_const_zero]
  simp_rw [ht]
  rw [Finset.sum_filter]
  simp only [Finset.sum_mul, ite_mul, zero_mul]

/-- Rewrites the square-root transport coefficient as `π² / sqrt 6 * sqrt γ`. -/
private theorem transport_constant (γ : ℝ) :
    (Real.pi ^ 2 / (2 * Real.sqrt 3)) * Real.sqrt (2 * γ) =
      (Real.pi ^ 2 / Real.sqrt 6) * Real.sqrt γ := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), h6]
  have h2ne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have h3ne : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [congrArg (fun x : ℝ => x * Real.sqrt γ) h2]

/-- Bounds the L1 distance between corresponding native amplitude-estimation layer laws when the
payoff-value L1 distance is at most `2 * γ`. This is a single-layer transport step for Lemma
18 of [Montanaro2015]. -/
private theorem layer_ae_l1 {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (g : ℚ → ℚ)
    (k l : ℕ) (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ)
    (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ) (hg : ∀ v, 0 ≤ g v)
    (γ : ℝ) (_hγ : 0 ≤ γ) (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ) :
    let B₁ := nativeLayerPrepare A₁ (fun i => g (f i)) k l
    let B₂ := nativeLayerPrepare A₂ (fun i => g (f i)) k l
    let P := aeLaw (layerGrid k) B₁ (j, false) (nativeLayerEvent I)
      (nativeLayerPrepare_unitary A₁ _ k l hA₁ (fun i => hg (f i))) (layerGrid_ge_two k)
    let Q := aeLaw (layerGrid k) B₂ (j, false) (nativeLayerEvent I)
      (nativeLayerPrepare_unitary A₂ _ k l hA₂ (fun i => hg (f i))) (layerGrid_ge_two k)
    (∑ z, |P.prob z - Q.prob z|) ≤
      2 * (Real.pi ^ 2 / Real.sqrt 6) * (layerGrid k : ℝ) * Real.sqrt γ := by
  (try dsimp only)
  let wt := fun v => (rationalPayoffValue (nativeLayerPayoff g l v) (nativeLayerBits k) : ℝ)
  have hw (v : ℚ) : 0 ≤ wt v ∧ wt v ≤ 1 := by
    have hp := native_layered_payoff_exact_partition ℚ g hg l v
    have h := (rationalPayoffCS_probability _ (nativeLayerBits k) hp.1 hp.2.1).2.2
    dsimp only [wt]
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have htab (i : I) : nativeLayerPayoff (fun i => g (f i)) l i = nativeLayerPayoff g l (f i) := by
    cases l <;> rfl
  have hm (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
      MeasureProb (preparedAAState (nativeLayerPrepare A (fun i => g (f i)) k l) (j, false))
        (nativeLayerEvent I) = ∑ i, BornProb (ApplyGate A (Ket j)) i * wt (f i) := by
    have h := (rational_payoff_preparation_mass A j (nativeLayerPayoff (fun i => g (f i)) l)
      (nativeLayerBits k) hA (fun i => by
        have hh := native_layered_payoff_exact_partition I (fun i => g (f i))
          (fun i => hg (f i)) l i
        exact ⟨hh.1, hh.2.1⟩)).2.1
    simpa only [preparedAAState, nativeLayerPrepare, nativeLayerEvent, ApplyGate, htab] using! h
  have ht := montanaroLemma18AELawTVSubgoal (I × Bool) (layerGrid k) (layerGrid_ge_two k)
    (nativeLayerPrepare A₁ (fun i => g (f i)) k l)
    (nativeLayerPrepare A₂ (fun i => g (f i)) k l) (j, false) (j, false)
    (nativeLayerEvent I) (nativeLayerEvent I)
    (nativeLayerPrepare_unitary A₁ _ k l hA₁ (fun i => hg (f i)))
    (nativeLayerPrepare_unitary A₂ _ k l hA₂ (fun i => hg (f i))) _ _ (hm A₁ hA₁) (hm A₂ hA₂)
  have hshift := (value_weight_shift A₁ A₂ j f wt hw).trans hd
  have hsqrt := Real.sqrt_le_sqrt hshift
  have hb := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ (Real.pi ^ 2 / (2 * Real.sqrt 3)) * (layerGrid k : ℝ) by positivity)
  have he : (Real.pi ^ 2 / (2 * Real.sqrt 3)) * (layerGrid k : ℝ) * Real.sqrt (2 * γ) =
      (Real.pi ^ 2 / Real.sqrt 6) * (layerGrid k : ℝ) * Real.sqrt γ := by
    nlinarith [transport_constant γ]
  rw [he] at hb
  linarith

/-- Bounds the L1 distance between centered layered records by the number of
amplitude-estimation trials times the single-trial perturbation bound. -/
private theorem centered_layer_l1 {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ)
    (v : ℚ) (positive : Bool) (γ : ℝ) (hγ : 0 ≤ γ)
    (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ) :
    (∑ ω, |(centeredLayerLaw A₁ j f σ k hA₁ v positive).prob ω -
      (centeredLayerLaw A₂ j f σ k hA₂ v positive).prob ω|) ≤
      ((k + 2) * (2 * layerRepetitions k + 1) : ℕ) *
        (2 * (Real.pi ^ 2 / Real.sqrt 6) * (layerGrid k : ℝ) * Real.sqrt γ) := by
  let g : ℚ → ℚ := fun t => max 0 ((if positive then t - v else v - t) / (4 * σ))
  let hP₁ := fun l : Fin (k + 2) => nativeLayerPrepare_unitary A₁
    (fun i => g (f i)) k l hA₁ (fun _ => le_max_left _ _)
  let hP₂ := fun l : Fin (k + 2) => nativeLayerPrepare_unitary A₂
    (fun i => g (f i)) k l hA₂ (fun _ => le_max_left _ _)
  let p := nativeLayerTrialLaw A₁ j (fun i => g (f i)) k hP₁
  let q := nativeLayerTrialLaw A₂ j (fun i => g (f i)) k hP₂
  have hcoord (l : Fin (k + 2)) : (∑ u, |(p l).prob u - (q l).prob u|) ≤
      (2 * layerRepetitions k + 1 : ℕ) *
        (2 * (Real.pi ^ 2 / Real.sqrt 6) * (layerGrid k : ℝ) * Real.sqrt γ) := by
    have ht := native_product_l1 (2 * layerRepetitions k + 1)
      (fun _ => aeLaw (layerGrid k) (nativeLayerPrepare A₁ (fun i => g (f i)) k l)
        (j, false) (nativeLayerEvent I) (hP₁ l) (layerGrid_ge_two k))
      (fun _ => aeLaw (layerGrid k) (nativeLayerPrepare A₂ (fun i => g (f i)) k l)
        (j, false) (nativeLayerEvent I) (hP₂ l) (layerGrid_ge_two k))
    apply ht.trans
    have he := layer_ae_l1 A₁ A₂ j f g k l hA₁ hA₂ (fun _ => le_max_left _ _) γ hγ hd
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (2 * layerRepetitions k + 1))))
      (fun _ _ => he)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using! hs
  have he₁ : centeredLayerLaw A₁ j f σ k hA₁ v positive = independentSampleLaw p := by
    dsimp only [centeredLayerLaw, nativeLayerLaw, p, g, hP₁]
  have he₂ : centeredLayerLaw A₂ j f σ k hA₂ v positive = independentSampleLaw q := by
    dsimp only [centeredLayerLaw, nativeLayerLaw, q, g, hP₂]
  rw [he₁, he₂]
  dsimp only [independentSampleLaw]
  apply (native_product_l1 (k + 2) p q).trans
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (k + 2)))) (fun l _ => hcoord l)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, mul_assoc] using! hs

/-- Bounds the L1 difference of two conditional pair laws by the L1 difference of their outer
weights plus a uniform conditional error. The second outer weight is assumed nonnegative and
normalized. -/
private theorem conditional_joint_l1 {V X : Type} [Fintype V] [DecidableEq V]
    [Fintype X] [DecidableEq X] (p q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v)
    (hqsum : ∑ v, q v = 1) (P₁ P₂ N₁ N₂ : V → FinDist X)
    (δ : ℝ) (hδ : ∀ v, (∑ u, ∑ w,
      |(P₁ v).prob u * (N₁ v).prob w - (P₂ v).prob u * (N₂ v).prob w|) ≤ δ) :
    (∑ v, ∑ u, ∑ w,
      |p v * (P₁ v).prob u * (N₁ v).prob w - q v * (P₂ v).prob u * (N₂ v).prob w|) ≤
      (∑ v, |p v - q v|) + δ := by
  calc
    _ ≤ ∑ v, ∑ u, ∑ w,
        (|p v - q v| * (P₁ v).prob u * (N₁ v).prob w +
          q v * |(P₁ v).prob u * (N₁ v).prob w - (P₂ v).prob u * (N₂ v).prob w|) := by
      apply Finset.sum_le_sum; intro v _
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro w _
      have h := abs_sub_le (p v * (P₁ v).prob u * (N₁ v).prob w)
        (q v * (P₁ v).prob u * (N₁ v).prob w)
        (q v * (P₂ v).prob u * (N₂ v).prob w)
      simpa only [← sub_mul, mul_assoc, ← mul_sub, abs_mul,
        abs_of_nonneg ((P₁ v).nonneg u), abs_of_nonneg ((N₁ v).nonneg w),
        abs_of_nonneg (hq0 v)] using! h
    _ = ∑ v, (|p v - q v| + q v * (∑ u, ∑ w,
        |(P₁ v).prob u * (N₁ v).prob w - (P₂ v).prob u * (N₂ v).prob w|)) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, (N₁ v).sum_one,
        mul_one, (P₁ v).sum_one]
    _ ≤ ∑ v, (|p v - q v| + q v * δ) := Finset.sum_le_sum
      (fun v _ => add_le_add le_rfl (mul_le_mul_of_nonneg_left (hδ v) (hq0 v)))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hqsum, one_mul]

/-- Bounds the L1 distance between compressed signed records by the initial payoff-value
perturbation plus the errors of both centered layer records. -/
private theorem compressed_record_l1 {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ)
    (γ : ℝ) (hγ : 0 ≤ γ) (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ)
    (q₁ q₂ : FinDist (Values f × (LayerRecord k × LayerRecord k)))
    (hq₁ : ∀ y, q₁.prob y = ∑ x, if recordValueMap f k x = y then
      (canonicalSignedLaw A₁ j f σ k hA₁).prob x else 0)
    (hq₂ : ∀ y, q₂.prob y = ∑ x, if recordValueMap f k x = y then
      (canonicalSignedLaw A₂ j f σ k hA₂).prob x else 0) :
    (∑ ω, |q₁.prob ω - q₂.prob ω|) ≤
      2 * γ + 2 * ((k + 2) * (2 * layerRepetitions k + 1) : ℕ) *
        (2 * (Real.pi ^ 2 / Real.sqrt 6) * (layerGrid k : ℝ) * Real.sqrt γ) := by
  let c₁ := fun v : Values f => ∑ i ∈ Finset.univ.filter (fun i => f i = v.val),
    BornProb (ApplyGate A₁ (Ket j)) i
  let c₂ := fun v : Values f => ∑ i ∈ Finset.univ.filter (fun i => f i = v.val),
    BornProb (ApplyGate A₂ (Ket j)) i
  let P₁ := fun v : Values f => centeredLayerLaw A₁ j f σ k hA₁ v.val true
  let P₂ := fun v : Values f => centeredLayerLaw A₂ j f σ k hA₂ v.val true
  let N₁ := fun v : Values f => centeredLayerLaw A₁ j f σ k hA₁ v.val false
  let N₂ := fun v : Values f => centeredLayerLaw A₂ j f σ k hA₂ v.val false
  have hf₁ (v : Values f) (u w : LayerRecord k) :
      q₁.prob (v, (u, w)) = c₁ v * (P₁ v).prob u * (N₁ v).prob w :=
    native_value_record_fiber A₁ j f σ k hA₁ q₁ hq₁ v u w
  have hf₂ (v : Values f) (u w : LayerRecord k) :
      q₂.prob (v, (u, w)) = c₂ v * (P₂ v).prob u * (N₂ v).prob w :=
    native_value_record_fiber A₂ j f σ k hA₂ q₂ hq₂ v u w
  have hc₂0 (v : Values f) : 0 ≤ c₂ v :=
    Finset.sum_nonneg (fun i _ => bornProb_nonneg _ i)
  have hc₂sum : ∑ v, c₂ v = 1 := by
    have hs := q₂.sum_one
    simp only [Fintype.sum_prod_type] at hs
    simp_rw [hf₂] at hs
    have he (v : Values f) : (∑ u, ∑ w, c₂ v * (P₂ v).prob u * (N₂ v).prob w) = c₂ v := by
      simp only [← Finset.mul_sum, (N₂ v).sum_one, mul_one, (P₂ v).sum_one]
    simpa only [he] using! hs
  have hc : (∑ v : Values f, |c₁ v - c₂ v|) ≤ 2 * γ := by
    change (∑ v : ↥(Finset.image f Finset.univ),
      |(∑ i ∈ Finset.univ.filter (fun i => f i = v.val), BornProb (ApplyGate A₁ (Ket j)) i) -
        (∑ i ∈ Finset.univ.filter (fun i => f i = v.val), BornProb (ApplyGate A₂ (Ket j)) i)|) ≤ _
    rw [Finset.sum_coe_sort (Finset.image f Finset.univ) (fun v : ℚ =>
      |(∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₁ (Ket j)) i) -
        (∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₂ (Ket j)) i)|)]
    exact hd
  let δ := 2 * ((k + 2) * (2 * layerRepetitions k + 1) : ℕ) *
    (2 * (Real.pi ^ 2 / Real.sqrt 6) * (layerGrid k : ℝ) * Real.sqrt γ)
  have hδ (v : Values f) : (∑ u, ∑ w,
      |(P₁ v).prob u * (N₁ v).prob w - (P₂ v).prob u * (N₂ v).prob w|) ≤ δ := by
    apply (native_pair_record_l1 (P₁ v) (P₂ v) (N₁ v) (N₂ v)).trans
    have hp := centered_layer_l1 A₁ A₂ j f σ k hA₁ hA₂ v.val true γ hγ hd
    have hn := centered_layer_l1 A₁ A₂ j f σ k hA₁ hA₂ v.val false γ hγ hd
    change _ ≤ δ
    dsimp only [δ]
    linarith
  simp only [Fintype.sum_prod_type]
  simp_rw [hf₁, hf₂]
  exact (conditional_joint_l1 c₁ c₂ hc₂0 hc₂sum P₁ P₂ N₁ N₂ δ hδ).trans
    (add_le_add hc le_rfl)

/-- Expresses an event probability on independent samples as the expectation of its indicator
under the independent sample law. -/
private theorem probEvent_as_test {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (n : ℕ) (E : (Fin n → X) → Prop) :
    p.probEvent E = (independentSampleLaw (fun _ : Fin n => p)).expect
      (fun ξ => if E ξ then (1 : ℝ) else 0) := by
  simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.sum_filter,
    independentSampleLaw, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf, mul_ite, mul_one, mul_zero]

/-- Proves the restricted signed-estimator stability statement associated with Lemma 18 of
[Montanaro2015]. A payoff-value L1 bound and a variance bound for the second preparation
yield the stated median failure bound under the first preparation. -/
theorem montanaroLemma18RestrictedSubgoal : MontanaroLemma18RestrictedSubgoal := by
  intro I _ _ A₁ A₂ j f σ k r γ hA₁ hA₂ hk hσ hγ hd
  (try dsimp only)
  intro hvar
  let μ₂ := ∑ i, BornProb (ApplyGate A₂ (Ket j)) i * (f i : ℝ)
  let p₁ := canonicalSignedLaw A₁ j f σ k hA₁
  let p₂ := canonicalSignedLaw A₂ j f σ k hA₂
  let E₀ := fun ξ : Fin (2 * r + 1) → I × (LayerRecord k × LayerRecord k) =>
    9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k < |(nativeSignedOutputMedian f σ k r ξ : ℝ) - μ₂|
  change p₁.probEvent E₀ ≤ _
  have hintrinsic : p₂.probEvent E₀ ≤ (143 / 144 : ℝ) ^ r :=
    (native_signed_rational_trial_and_median I A₂ j f σ k r hA₂ hk hσ hvar).2.1
  obtain ⟨q₁, hq₁⟩ :=
      Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pushforward p₁ (recordValueMap f k)
  obtain ⟨q₂, hq₂⟩ :=
      Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pushforward p₂ (recordValueMap f k)
  let E := fun ξ : Fin (2 * r + 1) → Values f × (LayerRecord k × LayerRecord k) =>
    9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k <
      |(nativeSignedOutputMedian (fun v : Values f => v.val) σ k r ξ : ℝ) - μ₂|
  let w := fun ξ => if E ξ then (1 : ℝ) else 0
  have he₁ : p₁.probEvent E₀ = (independentSampleLaw (fun _ : Fin (2 * r + 1) => q₁)).expect w := by
    rw [probEvent_as_test, fresh_pushforward_test p₁ q₁ (recordValueMap f k) hq₁]
    rfl
  have he₂ : p₂.probEvent E₀ = (independentSampleLaw (fun _ : Fin (2 * r + 1) => q₂)).expect w := by
    rw [probEvent_as_test, fresh_pushforward_test p₂ q₂ (recordValueMap f k) hq₂]
    rfl
  have htest := bounded_test_tv (independentSampleLaw (fun _ : Fin (2 * r + 1) => q₁))
    (independentSampleLaw (fun _ : Fin (2 * r + 1) => q₂)) w
    (fun ξ => by dsimp only [w]; split <;> norm_num)
  rw [← he₁, ← he₂] at htest
  have hjoint := compressed_record_l1 A₁ A₂ j f σ k hA₁ hA₂ γ hγ hd q₁ q₂ hq₁ hq₂
  have hproduct := native_product_l1 (2 * r + 1) (fun _ => q₁) (fun _ => q₂)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hproduct
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (2 * r + 1))))
    (fun _ _ => hjoint)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have htv := mul_le_mul_of_nonneg_left (hproduct.trans hsum) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hb := htest.trans htv
  have hupper := (abs_le.mp hb).2
  push_cast at hupper ⊢
  linear_combination hupper + hintrinsic

end Qatlib.Concepts.EstimatorLaws.MergedEstimator
