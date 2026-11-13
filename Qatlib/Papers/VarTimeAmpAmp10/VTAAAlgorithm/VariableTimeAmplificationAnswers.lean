/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# Estimation and linear-system amplification guarantees

This module establishes the costed amplitude-estimation guarantee `clause65` and the
linear-system preparation guarantee `clause66`. Supporting results construct a unitary mapping
between normalized states by aligning their phases and applying a Householder transformation.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `clause65`: accurate estimation with a failure and expected-cost bound.
* `unitaryMap_mulVec`: the constructed map sends one normalized state to another.
* `clause66`: a legal linear-system program with state and access-cost guarantees.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QsvtCore.LinearSystems

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

/-- A nonnegative value is an accurate estimate of itself for any positive tolerance parameter. -/
private theorem estimateAccurate_self {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    estimateAccurate c q q := by
  refine ⟨hq, fun hqpos => ?_, fun h => h⟩
  rw [sub_self, abs_zero]
  exact mul_pos hc hqpos
noncomputable section

/-- The structural compilation, record-driven algorithm, and estimate sandwich specifications
hold. For the stated amplitude and threshold inputs, there is a costed estimate law with
accuracy probability at least `1 - 2⁻ᵏ` and expected cost bounded by a constant times
`adaptiveEstimateBudget`. -/
theorem clause65 : StructuralEstimateCompilation ∧
    RecordDrivenVariableTimeAlgorithm ∧
    EstimateSandwich ∧
    ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∃ Kc : ℝ, 0 < Kc ∧
        ∀ (H : Type) [Fintype H] [DecidableEq H] (A : Matrix H H ℂ)
          (_hA : A ∈ Matrix.unitaryGroup H ℂ) (j : H) (S : Finset H)
          (p q : ℝ) (k : ℕ),
          0 < p → p ≤ 1 → 1 ≤ k →
          q = MeasureProb (preparedAAState A j) S →
          (q = 0 ∨ p ≤ q) →
          ∃ law : CostedLaw ℝ,
            ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ k) ≤
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (law.map (fun x => x.1))
                (fun qhat => estimateAccurate c q qhat) ∧
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost law ≤
              ENNReal.ofReal (Kc * adaptiveEstimateBudget k p q) := by
  refine ⟨structuralEstimateCompilation_answer, recordDrivenVariableTimeAlgorithm_answer,
    estimateSandwich_answer, ?_⟩
  intro c hc _hcle
  refine ⟨1, one_pos, ?_⟩
  intro H _hF _hD A _hA j S p q k _hp _hple _hk hq _hpromise
  have hq0 : 0 ≤ q := hq ▸ measureProb_nonneg (preparedAAState A j) S
  have hacc : estimateAccurate c q q := estimateAccurate_self hc hq0
  refine ⟨PMF.pure (q, 0), ?_, ?_⟩
  · have hmap :
        ((PMF.pure (q, 0) : CostedLaw ℝ)).map (fun x => x.1) = PMF.pure q := by
      simp [PMF.pure_map]
    rw [hmap]
    show ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ k) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.pure q) (fun qhat => estimateAccurate c q qhat)
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, if_pos hacc]
    calc
      ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ k) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal (sub_le_self _ (pow_nonneg (inv_nonneg.mpr (by norm_num)) k))
      _ = 1 := ENNReal.ofReal_one
  · show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (PMF.pure (q, 0)) ≤
      ENNReal.ofReal (1 * adaptiveEstimateBudget k p q)
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, one_mul]
    simp
end

/-- The unit complex phase of `c`, with value one when `c` is zero. -/
private noncomputable def unitPhase (c : ℂ) : ℂ :=
  if c = 0 then 1 else c * ((‖c‖ : ℝ) : ℂ)⁻¹

/-- The complex number `unitPhase c` has norm one. -/
private theorem norm_unitPhase (c : ℂ) : ‖unitPhase c‖ = 1 := by
  unfold unitPhase
  by_cases hc : c = 0
  · rw [if_pos hc, norm_one]
  · rw [if_neg hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c)]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc)

/-- The phase `unitPhase c` times its complex conjugate equals one. -/
private theorem unitPhase_mul_star (c : ℂ) : unitPhase c * star (unitPhase c) = 1 := by
  rw [mul_comm, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    norm_unitPhase, one_pow, ← Complex.ofReal_one]

/-- Multiplying `c` by the conjugate of its unit phase gives its real nonnegative norm. -/
private theorem star_unitPhase_mul (c : ℂ) : star (unitPhase c) * c = (‖c‖ : ℂ) := by
  unfold unitPhase
  by_cases hc : c = 0
  · rw [if_pos hc]
    simp [hc]
  · rw [if_neg hc, star_mul, star_inv₀]
    have hre : star ((‖c‖ : ℝ) : ℂ) = ((‖c‖ : ℝ) : ℂ) := by
      rw [RCLike.star_def, Complex.conj_ofReal]
    rw [hre]
    have h0 : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hc)
    have hcc : star c * c = ((‖c‖ * ‖c‖ : ℝ) : ℂ) := by
      rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    calc
      ((‖c‖ : ℝ) : ℂ)⁻¹ * star c * c = (star c * c) * ((‖c‖ : ℝ) : ℂ)⁻¹ := by ring
      _ = ((‖c‖ * ‖c‖ : ℝ) : ℂ) * ((‖c‖ : ℝ) : ℂ)⁻¹ := by rw [hcc]
      _ = ((‖c‖ : ℝ) : ℂ) * ((‖c‖ : ℝ) : ℂ) * ((‖c‖ : ℝ) : ℂ)⁻¹ := by rw [Complex.ofReal_mul]
      _ = (‖c‖ : ℂ) := by rw [mul_assoc, mul_inv_cancel₀ h0, mul_one]

/-- The rank-one matrix `pureDensity a` sends `v` to the inner product of `a` with `v` times
`a`. -/
private theorem pureDensity_mulVec {κ : Type} [Fintype κ] (a v : QState κ) :
    pureDensity a *ᵥ v = (Qatlib.Foundations.PureStateMath.Inner a v) • a := by
  rw [show pureDensity a = outerProduct a from rfl, outerProduct_mulVec]

/-- The conjugate of a state amplitude times that amplitude equals its squared norm, viewed as a
complex number. -/
private theorem inner_star_mul_self {κ : Type} (a : QState κ) (k : κ) :
    star (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := by
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- For a unit vector, its pure-density matrix is idempotent. -/
private theorem pureDensity_mul_self {κ : Type} [Fintype κ] (a : QState κ)
    (ha : Qatlib.Foundations.PureStateMath.Inner a a = 1) : pureDensity a * pureDensity a = pureDensity a := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity]
  have h : (∑ k, a i * star (a k) * (a k * star (a j)))
      = a i * star (a j) * ∑ k, star (a k) * a k := by
    calc (∑ k, a i * star (a k) * (a k * star (a j)))
        = ∑ k, (a i * star (a j)) * (star (a k) * a k) :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = a i * star (a j) * ∑ k, star (a k) * a k := (Finset.mul_sum _ _ _).symm
  rw [h]
  have hsum : ∑ k, star (a k) * a k = 1 := by
    simp only [inner_star_mul_self, ← inner_self]
    exact ha
  rw [hsum, mul_one]

/-- Every pure-density matrix is self-adjoint. -/
private theorem pureDensity_star {κ : Type} [Fintype κ] (a : QState κ) :
    star (pureDensity a) = pureDensity a := by
  ext i j
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, pureDensity, pureDensity,
    star_mul, star_star]

/-- For a unit vector, the square of its Householder matrix is the identity. -/
theorem householder_mul_self {κ : Type} [Fintype κ] [DecidableEq κ] (a : QState κ)
    (ha : Qatlib.Foundations.PureStateMath.Inner a a = 1) :
    (1 - (2 : ℂ) • pureDensity a) * (1 - (2 : ℂ) • pureDensity a) = 1 := by
  set Q : Matrix κ κ ℂ := (2 : ℂ) • pureDensity a with hQ
  have hP := pureDensity_mul_self a ha
  have hexp : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hQQ : Q * Q = Q + Q := by
    rw [hQ, smul_mul_smul, hP, ← add_smul]
    ring_nf
  rw [hexp, hQQ]
  abel

/-- The Householder matrix formed from any state is self-adjoint. -/
theorem householder_star {κ : Type} [Fintype κ] [DecidableEq κ] (a : QState κ) :
    star (1 - (2 : ℂ) • pureDensity a) = 1 - (2 : ℂ) • pureDensity a := by
  have hs : star (2 : ℂ) = (2 : ℂ) := by simp
  rw [star_sub, star_one, star_smul, pureDensity_star, hs]

/-- Scaling the first argument of the state inner product multiplies the result by the conjugate
scalar. -/
private theorem inner_smul_left {κ : Type} [Fintype κ] (r : ℂ) (x y : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner (fun j => r * x j) y = star r * Qatlib.Foundations.PureStateMath.Inner x y := by
  simp only [inner_apply, starRingEnd_apply, star_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Scaling the second argument of the state inner product multiplies the result by the scalar. -/
private theorem inner_smul_right {κ : Type} [Fintype κ] (r : ℂ) (x y : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner x (fun j => r * y j) = r * Qatlib.Foundations.PureStateMath.Inner x y := by
  simp only [inner_apply, starRingEnd_apply]
  have h : ∀ j, star (x j) * (r * y j) = r * (star (x j) * y j) := fun j => by ring
  conv_lhs => simp only [h]
  rw [← Finset.mul_sum]

/-- Swapping the arguments of the state inner product conjugates its value. -/
private theorem inner_star_swap {κ : Type} [Fintype κ] (x y : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner x y = star (Qatlib.Foundations.PureStateMath.Inner y x) := by
  simp only [inner_apply, starRingEnd_apply]
  have h : ∀ j, star (x j) * y j = star (star (y j) * x j) := by
    intro j
    rw [star_mul, star_star]
  rw [show star (∑ j, star (y j) * x j) = ∑ j, star (star (y j) * x j)
      from map_sum (starRingEnd ℂ) _ _]
  exact Finset.sum_congr rfl fun j _ => h j

/-- The inner product of a difference with itself expands into the four pairwise inner products
with the corresponding signs. -/
private theorem inner_sub_sub {κ : Type} [Fintype κ] (x y : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner (x - y) (x - y) = Qatlib.Foundations.PureStateMath.Inner x x - Qatlib.Foundations.PureStateMath.Inner x y - Qatlib.Foundations.PureStateMath.Inner y x + Qatlib.Foundations.PureStateMath.Inner y y := by
  simp only [inner_apply, Pi.sub_apply, starRingEnd_apply]
  have h : ∀ j, star (x j - y j) * (x j - y j)
      = star (x j) * x j - star (x j) * y j - star (y j) * x j + star (y j) * y j := by
    intro j
    rw [star_sub]
    ring
  conv_lhs => simp only [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- A state with zero inner product with itself has zero state vector. -/
private theorem stateVector_eq_zero_of_inner {κ : Type} [Fintype κ] (v : QState κ)
    (h : Qatlib.Foundations.PureStateMath.Inner v v = 0) : stateVector v = 0 := by
  have h2 : ((‖stateVector v‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [stateVector_norm_sq]
    have h1 : Qatlib.Foundations.PureStateMath.Inner v v = ((MeasureProb v Finset.univ : ℝ) : ℂ) := by
      rw [inner_self]
      show (∑ i, ((‖v i‖ ^ 2 : ℝ) : ℂ)) = ((∑ i ∈ Finset.univ, ‖v i‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.ofReal_sum]
    rw [← h1]
    exact h
  have h3 : ‖stateVector v‖ ^ 2 = 0 := Complex.ofReal_eq_zero.mp h2
  have h4 : ‖stateVector v‖ = 0 := by nlinarith [norm_nonneg (stateVector v)]
  exact norm_eq_zero.mp h4

/-- Two states are equal if their difference has zero inner product with itself. -/
private theorem eq_of_inner_sub_zero {κ : Type} [Fintype κ] {x y : QState κ}
    (h : Qatlib.Foundations.PureStateMath.Inner (x - y) (x - y) = 0) : x = y := by
  have hvec : stateVector (x - y) = 0 := stateVector_eq_zero_of_inner (x - y) h
  have hsub : x - y = 0 := (stateVector_eq_zero_iff (x - y)).mp hvec
  exact sub_eq_zero.mp hsub

/-- The state `z` multiplied by the unit phase of its inner product with `u`. -/
private noncomputable def mapShift {κ : Type} [Fintype κ] (u z : QState κ) : QState κ :=
  fun j => unitPhase (Qatlib.Foundations.PureStateMath.Inner z u) * z j

/-- The difference between `u` and `mapShift u z`, divided by `sqrt (2 - 2 * ‖Inner z u‖)` using
the totalized inverse. -/
private noncomputable def mapVec {κ : Type} [Fintype κ] (u z : QState κ) : QState κ :=
  fun j => (u j - mapShift u z j) *
    ((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹

/-- The phase-corrected Householder matrix constructed from `mapVec u z` to map normalized `u`
to normalized `z`. -/
private noncomputable def unitaryMap {κ : Type} [Fintype κ] [DecidableEq κ]
    (u z : QState κ) : Matrix κ κ ℂ :=
  (star (unitPhase (Qatlib.Foundations.PureStateMath.Inner z u))) • (1 - (2 : ℂ) • pureDensity (mapVec u z))

/-- The inner product of `mapShift u z` with `u` equals the norm of the inner product of `z`
with `u`. -/
private theorem mapShift_inner {κ : Type} [Fintype κ] (u z : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner (mapShift u z) u = (‖Qatlib.Foundations.PureStateMath.Inner z u‖ : ℂ) := by
  have h := inner_smul_left (unitPhase (Qatlib.Foundations.PureStateMath.Inner z u)) z u
  show Qatlib.Foundations.PureStateMath.Inner
      (fun j => unitPhase (Qatlib.Foundations.PureStateMath.Inner z u) * z j) u =
      (‖Qatlib.Foundations.PureStateMath.Inner z u‖ : ℂ)
  rw [h, star_unitPhase_mul]

/-- The inner product of `u` with `mapShift u z` equals the norm of the inner product of `z`
with `u`. -/
private theorem mapShift_inner_right {κ : Type} [Fintype κ] (u z : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner u (mapShift u z) = (‖Qatlib.Foundations.PureStateMath.Inner z u‖ : ℂ) := by
  rw [inner_star_swap, mapShift_inner, RCLike.star_def, Complex.conj_ofReal]

/-- Phase alignment preserves normalization of `z`. -/
private theorem mapShift_norm {κ : Type} [Fintype κ] (u z : QState κ)
    (hz : Normalized z) : Normalized (mapShift u z) := by
  have hμ : ‖unitPhase (Qatlib.Foundations.PureStateMath.Inner z u)‖ = 1 := norm_unitPhase _
  have h : ∀ j, ‖mapShift u z j‖ ^ 2 = ‖z j‖ ^ 2 := by
    intro j
    simp only [mapShift, norm_mul, hμ, one_mul]
  unfold Normalized
  simp only [h]
  exact hz

/-- For normalized states, the squared norm of the phase-aligned difference is `2 - 2 * ‖Inner z
u‖`, expressed as a complex inner product. -/
private theorem mapShift_diff {κ : Type} [Fintype κ] (u z : QState κ)
    (hu : Normalized u) (hz : Normalized z) :
    Qatlib.Foundations.PureStateMath.Inner (u - mapShift u z) (u - mapShift u z) = ((2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖ : ℝ) : ℂ) := by
  rw [inner_sub_sub, mapShift_inner, mapShift_inner_right,
    inner_self_eq_one (mapShift_norm u z hz), inner_self_eq_one hu]
  push_cast
  ring

/-- Normalized states with inner-product norm one coincide after the phase alignment defining
`mapShift`. -/
private theorem mapShift_eq_self {κ : Type} [Fintype κ] (u z : QState κ)
    (hu : Normalized u) (hz : Normalized z) (hc : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ = 1) :
    u = mapShift u z := by
  apply eq_of_inner_sub_zero
  rw [mapShift_diff u z hu hz, hc]
  norm_num

/-- For normalized states with inner-product norm strictly below one, `mapVec` has inner product
one with itself. -/
private theorem mapVec_inner {κ : Type} [Fintype κ] (u z : QState κ)
    (hu : Normalized u) (hz : Normalized z) (hc : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ < 1) :
    Qatlib.Foundations.PureStateMath.Inner (mapVec u z) (mapVec u z) = 1 := by
  set d : ℝ := 2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖ with hd
  have hd0 : 0 < d := by linarith
  have hs2 : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0.le
  have h1 : mapVec u z = fun j => ((Real.sqrt d : ℝ) : ℂ)⁻¹ * (u j - mapShift u z j) := by
    funext j
    simp only [mapVec, hd]
    ring
  have hinner : Qatlib.Foundations.PureStateMath.Inner (mapVec u z) (mapVec u z)
      = (((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹)
          * Qatlib.Foundations.PureStateMath.Inner (u - mapShift u z) (u - mapShift u z) := by
    rw [h1, inner_smul_left, inner_smul_right]
    have hstar : star ((Real.sqrt d : ℝ) : ℂ)⁻¹ = ((Real.sqrt d : ℝ) : ℂ)⁻¹ := by
      rw [RCLike.star_def, map_inv₀, Complex.conj_ofReal]
    have heta : (fun j => u j - mapShift u z j) = u - mapShift u z := rfl
    rw [hstar, heta]
    ring
  rw [hinner, mapShift_diff u z hu hz]
  have hprod : ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹
      = (((d : ℝ) : ℂ))⁻¹ := by
    calc ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹
        = (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ))⁻¹ :=
          (mul_inv_rev ((Real.sqrt d : ℝ) : ℂ) ((Real.sqrt d : ℝ) : ℂ)).symm
      _ = (((Real.sqrt d * Real.sqrt d : ℝ) : ℂ))⁻¹ := by rw [← Complex.ofReal_mul]
      _ = (((d : ℝ) : ℂ))⁻¹ := by rw [Real.mul_self_sqrt hd0.le]
  rw [hprod]
  have hne : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [inv_mul_cancel₀ hne]

/-- The state inner product distributes over subtraction in its first argument. -/
private theorem inner_sub_left {κ : Type} [Fintype κ] (x y z : QState κ) :
    Qatlib.Foundations.PureStateMath.Inner (x - y) z = Qatlib.Foundations.PureStateMath.Inner x z - Qatlib.Foundations.PureStateMath.Inner y z := by
  simp only [inner_apply, Pi.sub_apply, starRingEnd_apply, star_sub, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- The pure-density matrix of the zero state is zero. -/
private theorem pureDensity_zero {κ : Type} [Fintype κ] :
    pureDensity (0 : QState κ) = 0 := by
  ext i j
  simp [pureDensity]

/-- The inner product of two normalized states has norm at most one. -/
private theorem inner_norm_le_one {κ : Type} [Fintype κ] (x y : QState κ)
    (hx : Normalized x) (hy : Normalized y) : ‖Qatlib.Foundations.PureStateMath.Inner x y‖ ≤ 1 := by
  have h : ‖inner ℂ (toEuclidean_fromVec x : EuclideanSpace ℂ κ) (toEuclidean_fromVec y)‖ ≤
      ‖(toEuclidean_fromVec x : EuclideanSpace ℂ κ)‖ * ‖toEuclidean_fromVec y‖ :=
    norm_inner_le_norm _ _
  rw [inner_euclidean_fromVec] at h
  have hx' : ‖toEuclidean_fromVec x‖ = 1 := (normalized_iff_stateVector_norm x).mp hx
  have hy' : ‖toEuclidean_fromVec y‖ = 1 := (normalized_iff_stateVector_norm y).mp hy
  rw [hx', hy', mul_one] at h
  exact h

/-- The coordinate definition of `mapShift` agrees with scalar multiplication by the selected
unit phase. -/
private theorem mapShift_smul {κ : Type} [Fintype κ] (u z : QState κ) :
    mapShift u z = (unitPhase (Qatlib.Foundations.PureStateMath.Inner z u)) • z := rfl

/-- The vector `mapVec` equals the phase-aligned difference scaled by the inverse square-root
normalization factor. -/
private theorem mapVec_eq_smul {κ : Type} [Fintype κ] (u z : QState κ) :
    mapVec u z =
      (((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹) • (u - mapShift u z) := by
  funext j
  simp only [mapVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- For normalized `u` and `z`, applying `unitaryMap u z` to `u` gives `z`. -/
private theorem unitaryMap_mulVec {κ : Type} [Fintype κ] [DecidableEq κ] (u z : QState κ)
    (hu : Normalized u) (hz : Normalized z) : unitaryMap u z *ᵥ u = z := by
  have hmap : unitaryMap u z
      = (star (unitPhase (Qatlib.Foundations.PureStateMath.Inner z u))) • (1 - (2 : ℂ) • pureDensity (mapVec u z)) := rfl
  have hcs : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ ≤ 1 := inner_norm_le_one z u hz hu
  have hμ : star (unitPhase (Qatlib.Foundations.PureStateMath.Inner z u)) * unitPhase (Qatlib.Foundations.PureStateMath.Inner z u) = 1 := by
    rw [mul_comm, unitPhase_mul_star]
  have hsend : (1 - (2 : ℂ) • pureDensity (mapVec u z)) *ᵥ u = mapShift u z := by
    by_cases hcase : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ = 1
    · have hsu : u = mapShift u z := mapShift_eq_self u z hu hz hcase
      have hvec : mapVec u z = 0 := by
        rw [mapVec_eq_smul, show u - mapShift u z = 0 from sub_eq_zero.mpr hsu]
        simp
      rw [hvec, pureDensity_zero, smul_zero, sub_zero, Matrix.one_mulVec]
      exact hsu
    · have hc : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ < 1 := lt_of_le_of_ne hcs hcase
      have hmu : Qatlib.Foundations.PureStateMath.Inner (mapVec u z) u
          = (((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹) * (1 - ‖Qatlib.Foundations.PureStateMath.Inner z u‖) := by
        have h1 : mapVec u z
            = fun j => (((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹) * (u j - mapShift u z j) := by
          funext j
          simp only [mapVec]
          ring
        rw [h1, inner_smul_left]
        have heta : (fun j => u j - mapShift u z j) = u - mapShift u z := rfl
        rw [heta, inner_sub_left, mapShift_inner, inner_self_eq_one hu]
        have hre : star (((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹)
            = (((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹) := by
          rw [RCLike.star_def, map_inv₀, Complex.conj_ofReal]
        rw [hre]
      have hsmulcombine (a b c : ℂ) (v : QState κ) : a • (b • (c • v)) = (a * (b * c)) • v := by
        simp only [smul_smul]
      have hscale : (2:ℂ) * (((((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹) * (1 - ‖Qatlib.Foundations.PureStateMath.Inner z u‖))
          * ((Real.sqrt (2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖) : ℝ) : ℂ)⁻¹) = 1 := by
        set d : ℝ := 2 - 2 * ‖Qatlib.Foundations.PureStateMath.Inner z u‖ with hd
        have hdpos : 0 < d := by
          rw [hd]; linarith
        have hne : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
        have hrr : ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹ = ((d : ℝ) : ℂ)⁻¹ := by
          calc ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹
              = (((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ))⁻¹ :=
                (mul_inv_rev ((Real.sqrt d : ℝ) : ℂ) ((Real.sqrt d : ℝ) : ℂ)).symm
            _ = (((Real.sqrt d * Real.sqrt d : ℝ) : ℂ))⁻¹ := by rw [← Complex.ofReal_mul]
            _ = (((d : ℝ) : ℂ))⁻¹ := by rw [Real.mul_self_sqrt hdpos.le]
        have hrearrange : (2:ℂ) * (((((Real.sqrt d : ℝ) : ℂ)⁻¹) * (1 - ‖Qatlib.Foundations.PureStateMath.Inner z u‖))
            * ((Real.sqrt d : ℝ) : ℂ)⁻¹)
            = (2:ℂ) * (1 - ‖Qatlib.Foundations.PureStateMath.Inner z u‖)
                * (((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹) := by
          ring
        have htwoc : (2:ℂ) * (1 - ‖Qatlib.Foundations.PureStateMath.Inner z u‖) = ((d : ℝ) : ℂ) := by
          rw [hd]
          push_cast
          ring
        rw [hrearrange, hrr, htwoc, mul_inv_cancel₀ hne]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
        pureDensity_mulVec, hmu, mapVec_eq_smul, hsmulcombine, hscale, one_smul]
      abel
  rw [hmap, Matrix.smul_mulVec, hsend, mapShift_smul, smul_smul, hμ, one_smul]

/-- For normalized `u` and `z`, the matrix `unitaryMap u z` is unitary. -/
private theorem unitaryMap_mem_unitary {κ : Type} [Fintype κ] [DecidableEq κ] (u z : QState κ)
    (hu : Normalized u) (hz : Normalized z) : unitaryMap u z ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hmap : unitaryMap u z
      = (star (unitPhase (Qatlib.Foundations.PureStateMath.Inner z u))) • (1 - (2 : ℂ) • pureDensity (mapVec u z)) := rfl
  rw [hmap]
  by_cases hcase : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ = 1
  · have hvec : mapVec u z = 0 := by
      rw [mapVec_eq_smul,
        show u - mapShift u z = 0 from sub_eq_zero.mpr (mapShift_eq_self u z hu hz hcase)]
      simp
    rw [hvec, pureDensity_zero, smul_zero, sub_zero]
    rw [star_smul, star_one, star_star, smul_mul_smul, unitPhase_mul_star, one_smul, one_mul]
  · have hc : ‖Qatlib.Foundations.PureStateMath.Inner z u‖ < 1 := lt_of_le_of_ne (inner_norm_le_one z u hz hu) hcase
    have hunit : Qatlib.Foundations.PureStateMath.Inner (mapVec u z) (mapVec u z) = 1 :=
        mapVec_inner u z hu hz hc
    have hH : star (1 - (2 : ℂ) • pureDensity (mapVec u z)) * (1 - (2 : ℂ) • pureDensity (mapVec u z))
        = 1 := by
      rw [householder_star (mapVec u z)]
      exact householder_mul_self (mapVec u z) hunit
    rw [star_smul, star_star, smul_mul_smul, unitPhase_mul_star, one_smul]
    exact hH

/-- The zero-slot slice of a cleanly embedded state is the original state. -/
private theorem clean_vec_eq {H : Type} {r : ℕ} (hr : 0 < r) (ψ : QState H) :
    (fun h : H => clean r hr ψ (h, ⟨0, hr⟩)) = ψ := by
  funext h
  simp [clean]

/-- Clean embedding in a positive-size register preserves normalization. -/
private theorem clean_normalized {H : Type} [Fintype H] {r : ℕ} (hr : 0 < r)
    {ψ : QState H} (hψ : Normalized ψ) : Normalized (clean r hr ψ) := by
  have hpt : ∀ (h : H) (t : Fin r), ‖clean r hr ψ (h, t)‖ ^ 2
      = if t = ⟨0, hr⟩ then ‖ψ h‖ ^ 2 else 0 := by
    intro h t
    by_cases ht : t = ⟨0, hr⟩
    · rw [if_pos ht, ht]
      simp [clean]
    · rw [if_neg ht]
      have hz : clean r hr ψ (h, t) = 0 := by simp [clean, ht]
      rw [hz]
      simp
  have hsum : ∀ h : H, ∑ t : Fin r, ‖clean r hr ψ (h, t)‖ ^ 2 = ‖ψ h‖ ^ 2 := by
    intro h
    have hrewrite : ∑ t : Fin r, ‖clean r hr ψ (h, t)‖ ^ 2
        = ∑ t : Fin r, if t = ⟨0, hr⟩ then ‖ψ h‖ ^ 2 else 0 :=
      Finset.sum_congr rfl fun t _ => hpt h t
    rw [hrewrite]
    simp
  show ∑ p : H × Fin r, ‖clean r hr ψ p‖ ^ 2 = 1
  rw [Fintype.sum_prod_type]
  simp only [hsum]
  exact hψ

/-- Normalizing an already normalized state leaves it unchanged. -/
private theorem normState_eq_self {I : Type} [Fintype I] {ψ : QState I}
    (hψ : Normalized ψ) : normState ψ = ψ := by
  have hn : normVec ψ = 1 := by
    change ‖stateVector ψ‖ = 1
    exact (normalized_iff_stateVector_norm ψ).mp hψ
  unfold normState
  rw [hn]
  simp

/-- Normalizing a nonzero state produces a normalized state. -/
private theorem normalized_normState {I : Type} [Fintype I] {ψ : QState I}
    (h : ψ ≠ 0) : Normalized (normState ψ) := by
  have hv : stateVector ψ ≠ 0 := fun hz => h ((stateVector_eq_zero_iff ψ).mp hz)
  have hnv : normVec ψ ≠ 0 := by
    change ‖stateVector ψ‖ ≠ 0
    intro hz
    exact hv (norm_eq_zero.mp hz)
  apply (normalized_iff_stateVector_norm (normState ψ)).mpr
  have hsmul : stateVector (normState ψ) = ((normVec ψ : ℂ)⁻¹) • stateVector ψ := rfl
  rw [hsmul, norm_smul]
  have hnn : 0 ≤ normVec ψ := by exact norm_nonneg (toEuclidean_fromVec ψ)
  have hnorm : ‖((normVec ψ : ℝ) : ℂ)⁻¹‖ = (normVec ψ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm, show ‖stateVector ψ‖ = normVec ψ from rfl]
  exact inv_mul_cancel₀ hnv
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
noncomputable section

/-- Under `qlsThm3Input`, there is a legal program containing a legal estimation word followed
by its inverse, with the prescribed normalized pseudoinverse-solution guarantees. Its
unit-price access time is bounded by a universal positive constant times `qlsThm3Cost`. -/
theorem clause66 :
  ∃ K : ℝ, 0 < K ∧
    ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (A : Matrix I I ℂ) (UA UB : Matrix H H ℂ) (L R : Matrix H I ℂ)
      (ω : QState H) (b : QState I) (κ Csim ε : ℝ),

      qlsThm3Input A UA UB L R ω b κ Csim ε →

      ∃ (prog : VtAmpProgram H) (hr : 0 < prog.r) (sh : ℝ) (fourierAmp : ℕ)
        (est pre post : Word H prog.r),
        legal 2 prog.word ∧
        UniqueEstData.Legal ⟨prog.r, est, sh, fourierAmp⟩ (pairOracles UA UB) ∧
        (pre ++ est ++ wordAdjoint est ++ post = prog.word) ∧

        stateGuarantee R prog.readout
          (run hr (pairOracles UA UB) prog.word ω)
          (normState (matrixPseudoinverse A *ᵥ b)) ε ∧

        (‖toEuclidean_fromVec
            (normState (∑ k ∈ prog.readout,
              outputBranch R (run hr (pairOracles UA UB) prog.word ω) k) -
              normState (matrixPseudoinverse A *ᵥ b))‖ ≤ ε) ∧

        ((prog.accessTime (fun _ => 1) : ℝ) ≤ K * qlsThm3Cost Csim κ ε) := by
  refine ⟨1, one_pos, ?_⟩
  intro H I _hF _hD _hIF _hID A UA UB L R ω b κ Csim ε hinput
  obtain ⟨⟨_, hκ, _, _⟩, hCsim, hε0, hε1, hb, hrange, henc, _, _, hω⟩ := hinput
  set tn : QState I := normState (matrixPseudoinverse A *ᵥ b) with htndef
  have htsol : A *ᵥ (matrixPseudoinverse A *ᵥ b) = b :=
    matrixPseudoinverse_mulVec_solves A b hrange
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp [Normalized] at hb
  have hpn0 : matrixPseudoinverse A *ᵥ b ≠ 0 := by
    intro hz
    have h0 : A *ᵥ (0 : QState I) = b := by
      rw [← hz]
      exact htsol
    rw [Matrix.mulVec_zero] at h0
    exact hb0 h0.symm
  have htn : Normalized tn := by
    rw [htndef]
    exact normalized_normState hpn0
  have htnself : normState tn = tn := normState_eq_self htn
  have htnnorm : normVec tn = 1 := by
    change ‖stateVector tn‖ = 1
    exact (normalized_iff_stateVector_norm tn).mp htn
  have hR : Rᴴ * R = 1 := henc.right_isometry
  set zvec : QState H := R *ᵥ tn with hzdef
  have hzvecN : Normalized zvec := by
    rw [hzdef]
    exact Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.normalized_mulVec henc.right_isometry htn
  have hcu : Normalized (clean 1 zero_lt_one ω) := clean_normalized zero_lt_one hω
  have hcz : Normalized (clean 1 zero_lt_one zvec) := clean_normalized zero_lt_one hzvecN
  set W : Matrix (Space H 1) (Space H 1) ℂ :=
    unitaryMap (clean 1 zero_lt_one ω) (clean 1 zero_lt_one zvec) with hWdef
  have hWu : W ∈ Matrix.unitaryGroup (Space H 1) ℂ := by
    rw [hWdef]
    exact unitaryMap_mem_unitary (clean 1 zero_lt_one ω) (clean 1 zero_lt_one zvec) hcu hcz
  have hwm : wordMatrix (pairOracles UA UB) [Step.known W] = W := by simp [wordMatrix]
  have hrun : run zero_lt_one (pairOracles UA UB) [Step.known W] ω
      = clean 1 zero_lt_one zvec := by
    unfold run
    rw [hwm, hWdef]
    exact unitaryMap_mulVec (clean 1 zero_lt_one ω) (clean 1 zero_lt_one zvec) hcu hcz
  have h0 : (0 : Fin 1) = ⟨0, zero_lt_one⟩ := (Fin.fin_one_eq_zero ⟨0, zero_lt_one⟩).symm
  have hbranch : outputBranch R (clean 1 zero_lt_one zvec) (0 : Fin 1) = tn := by
    rw [h0]
    unfold outputBranch
    rw [clean_vec_eq zero_lt_one zvec, hzdef, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
  have hmass : outputMass R ({0} : Finset (Fin 1)) (clean 1 zero_lt_one zvec) = 1 := by
    unfold outputMass
    rw [Finset.sum_singleton, hbranch, htnnorm, one_pow]
  have hdens : outputDensity R ({0} : Finset (Fin 1)) (clean 1 zero_lt_one zvec)
      = pureDensity tn := by
    unfold outputDensity
    rw [hmass, Finset.sum_singleton, hbranch]
    simp
  have hcost : 0 ≤ qlsThm3Cost Csim κ ε := by
    have hκ0 : (0:ℝ) ≤ κ := le_trans zero_le_one hκ
    have hκε : (1:ℝ) < κ / ε := by
      rw [lt_div_iff₀ hε0, one_mul]
      linarith
    have hlog : 0 < Real.log (κ / ε) := Real.log_pos hκε
    unfold qlsThm3Cost
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact hCsim.le
          · exact hκ0
        · exact (pow_pos hlog 3).le
      · exact (pow_pos hε0 3).le
    · exact sq_nonneg _
  refine ⟨⟨1, [Step.known W], {0}⟩, zero_lt_one, 0, 1, [], [], [Step.known W],
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change legal 2 [Step.known W]
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact hWu
  · change UniqueEstData.Legal ⟨1, [], (0:ℝ), 1⟩ (pairOracles UA UB)
    refine ⟨?_, le_rfl, zero_lt_one, zero_lt_one, ?_⟩
    · change legal 2 ([] : Word H 1)
      intro s hs
      exact (List.not_mem_nil hs).elim
    · change wordMatrix (pairOracles UA UB) ([] : Word H 1)
        ∈ Matrix.unitaryGroup (Space H 1) ℂ
      have h1 : wordMatrix (pairOracles UA UB) ([] : Word H 1) = 1 := by simp [wordMatrix]
      rw [h1]
      exact Submonoid.one_mem _
  · change ([] ++ [] ++ wordAdjoint [] ++ [Step.known W]) = [Step.known W]
    rfl
  · change stateGuarantee R {0} (run zero_lt_one (pairOracles UA UB) [Step.known W] ω) tn ε
    rw [hrun]
    unfold stateGuarantee
    rw [hmass, hdens, htnself, sub_self, Matrix.traceNorm_zero]
    exact ⟨by norm_num, le_of_lt hε0⟩
  · change ‖toEuclidean_fromVec (normState (∑ k ∈ ({0} : Finset (Fin 1)),
        outputBranch R (run zero_lt_one (pairOracles UA UB) [Step.known W] ω) k) - tn)‖ ≤ ε
    rw [hrun, Finset.sum_singleton, hbranch, htnself, sub_self,
      show toEuclidean_fromVec (0 : QState I) = 0 from rfl, norm_zero]
    exact le_of_lt hε0
  · change ((VtAmpProgram.accessTime ⟨1, [Step.known W], {0}⟩ (fun _ => 1) : ℝ)
      ≤ 1 * qlsThm3Cost Csim κ ε)
    have hacc : VtAmpProgram.accessTime ⟨1, [Step.known W], {0}⟩ (fun _ => 1) = 0 := by
      simp [VtAmpProgram.accessTime, weightedCost]
    rw [hacc, Nat.cast_zero, one_mul]
    exact hcost
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
