/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InteractHybrid.HybridObservableRepresentationStat
import Qatlib.Concepts.LchsSimulation.InteractHybrid.HybridObservableReprCounterexample
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Hybrid observable representation in forward time

The vector-valued Cauchy integral identity yields the double-integral representation of an
observable quadratic form. The theorem `hybridObservableRepresentation` applies for nonnegative
final time and arbitrary observable matrices. See [AnLiuLin2023] for the mathematical setting.

## Main statements

* `hybridObservableRepresentation`: For nonnegative final time, the evolved observable quadratic
  form equals the double-Cauchy integral of the corresponding unitary-family matrix elements.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InteractHybrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For `s ≤ t`, the Cauchy-weighted unitary evolution applied to a vector is integrable and its
integral equals the dissipative ordered evolution applied to that vector. -/
private theorem cauchy_integral_action {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (s t : ℝ) (hst : s ≤ t) (v : QState I) :
    Integrable (fun k : ℝ => (1/(Real.pi*(1+k^2))) •
      (orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t *ᵥ v)) ∧
    (∫ k : ℝ, (1/(Real.pi*(1+k^2))) •
      (orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t *ᵥ v)) =
      orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ v := by
  have h := time_dependent_lchs_entire_parameter I L H s t hL hH hPSD hHerm hst
  let F := fun z : ℂ => orderedEvolution (fun u => z • L u+Complex.I • H u) s t
  have hw : Integrable (fun k : ℝ => 1/(Real.pi*(1+k^2))) := by
    simpa [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm] using!
      integrable_inv_one_add_sq.const_mul Real.pi⁻¹
  have hc : Continuous (fun k : ℝ => F ((k : ℂ)*Complex.I)) :=
    h.1.continuous.comp (Complex.continuous_ofReal.mul (continuous_const (y := Complex.I)))
  have hn (k : ℝ) : ‖F ((k : ℂ)*Complex.I)‖ ≤ 1 := h.2 _ (by simp)
  have hi := hw.smul_bdd 1 hc.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  have hb (k : ℝ) : F ((k : ℂ)*Complex.I) =
      orderedEvolution (fun u => Complex.I • (H u+k • L u)) s t := by
    dsimp [F]
    congr 1
    funext u
    rw [smul_add, ← Complex.coe_smul, smul_smul, mul_comm]
    exact add_comm _ _
  let m : Matrix I I ℂ →L[ℝ] QState I :=
    (LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℂ ℂ).flip v)).restrictScalars ℝ
  have hm := m.integral_comp_comm hi
  have he := (time_dependent_lchs_cauchy_representation I L H s t hL hH hPSD hHerm hst).2
  change (∫ k : ℝ, m ((1/(Real.pi*(1+k^2))) • F ((k : ℂ)*Complex.I))) =
    m (∫ k : ℝ, (1/(Real.pi*(1+k^2))) • F ((k : ℂ)*Complex.I)) at hm
  simp only [hb] at hm
  rw [he] at hm
  have hmapply (X : Matrix I I ℂ) : m X = X *ᵥ v := rfl
  constructor
  · simpa only [Pi.smul_apply', hb, hmapply, Matrix.smul_mulVec] using! m.integrable_comp hi
  · simpa only [hmapply, Matrix.smul_mulVec] using! hm

/-- For nonnegative final time, the evolved observable quadratic form equals the double-Cauchy
integral of the corresponding unitary-family matrix elements. See [AnLiuLin2023]. -/
theorem hybridObservableRepresentation : HybridObservableRepresentation := by
  intro I _ _ L H O u₀ t hL hH hPSD hHerm ht
  (try dsimp only)
  let β := fun k : ℝ => 1 / (Real.pi * (1 + k^2))
  let V := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u+k • L u)) 0 t
  let U := orderedEvolution (fun u => L u+Complex.I • H u) 0 t
  let e : QState I →L[ℝ] EuclideanSpace ℂ I :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℂ)).symm.toContinuousLinearMap
  let f := fun k : ℝ => e (β k • (V k *ᵥ u₀))
  let M := Matrix.toEuclideanCLM (𝕜 := ℂ) O
  obtain ⟨hi, he⟩ := cauchy_integral_action L H hL hH hPSD hHerm 0 t ht u₀
  have hfi : Integrable f := e.integrable_comp hi
  have hfint : (∫ k : ℝ, f k) = toEuclidean_fromVec (U *ᵥ u₀) := by
    have hh := e.integral_comp_comm hi
    rw [he] at hh
    exact hh
  have hf (k : ℝ) : f k = (β k : ℂ) • toEuclidean_fromVec (V k *ᵥ u₀) := by
    simp only [f, map_smul]
    rw [Complex.coe_smul]
    rfl
  have hMf (k : ℝ) : M (f k) =
      (β k : ℂ) • toEuclidean_fromVec (O *ᵥ (V k *ᵥ u₀)) := by
    rw [hf, map_smul]
    exact congrArg (fun x => (β k : ℂ) • x) (toEuclideanCLM_applyGate O (V k *ᵥ u₀))
  have hM : M (toEuclidean_fromVec (U *ᵥ u₀)) =
      toEuclidean_fromVec (O *ᵥ (U *ᵥ u₀)) := toEuclideanCLM_applyGate O (U *ᵥ u₀)
  rw [← inner_euclidean_fromVec, ← hM, ← hfint]
  have hl := (innerSLFlip ℂ (M (∫ k : ℝ, f k))).integral_comp_commSL
    (by intro r x; simp) hfi
  have hl' : (∫ k : ℝ, inner ℂ (f k) (M (∫ z : ℝ, f z))) =
      inner ℂ (∫ k : ℝ, f k) (M (∫ z : ℝ, f z)) := by
    simpa only [innerSLFlip_apply_apply] using! hl
  rw [← hl']
  apply integral_congr_ae
  filter_upwards [] with k
  have hr := ((innerSL ℂ (f k)).comp M).integral_comp_comm hfi
  have hr' : (∫ k' : ℝ, inner ℂ (f k) (M (f k'))) =
      inner ℂ (f k) (M (∫ z : ℝ, f z)) := by
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using! hr
  rw [← hr']
  apply integral_congr_ae
  filter_upwards [] with k'
  rw [hf, hMf, inner_smul_left, inner_smul_right, inner_euclidean_fromVec]
  simp only [Complex.conj_ofReal, smul_eq_mul]
  have hweights : 1/(Real.pi*(1+k^2)) * 1/(Real.pi*(1+k'^2)) = β k * β k' := by
    dsimp [β]
    ring
  rw [hweights, Complex.ofReal_mul]
  dsimp only [V]
  ring

end Qatlib.Concepts.LchsSimulation.InteractHybrid
