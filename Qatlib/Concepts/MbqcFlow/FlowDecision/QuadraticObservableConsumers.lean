/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.QuadraticObservableShadows

/-!
# A degenerate quadratic Pauli shadow example

Specializes quadratic shadow estimation to `TensorGate pauliZ pauliZ` on the maximally mixed
qubit. The kernel factors into two Pauli Z snapshot values, and its conditional mean vanishes,
yielding an exact second-moment formula for the pairwise statistic.

The module also computes fresh-measurement, pair-evaluation, and median-processing counts. The
quadratic-estimator variance setting is developed in [HuangKuengPreskill2020].

## Main statements

* `quadratic_z_square_degenerate_variance_consumer`: zero mean and exact second moment `18 / (m
  * (m - 1))`.
* `quadratic_z_actual_resources`: measurement and classical processing counts.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open Matrix
open scoped Classical BigOperators ComplexOrder
set_option autoImplicit false

/-- The one-qubit tensor Pauli word supported on the Z axis is `pauliZ`. -/
private theorem quadratic_z_word : tensorPauliWord 1 (fun _ => some (2 : Fin 3)) = pauliZ := by
  have h0 : (bitVecEquiv 1).symm 0 = (fun _ => false) := by
    apply (bitVecEquiv 1).injective
    rw [Equiv.apply_symm_apply]
    rfl
  have h1 : (bitVecEquiv 1).symm 1 = (fun _ => true) := by
    apply (bitVecEquiv 1).injective
    rw [Equiv.apply_symm_apply]
    rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tensorPauliWord, tensorPauliWordFactor, tensorPauliProduct, relabelGate,
      pauliProductDensity, Fin.prod_univ_one, h0, h1, boolEquivFin2,
      pauliMatrix_two, pauliZ]

/-- The quadratic shadow kernel for `pauliZ ⊗ pauliZ` factors into the two one-qubit Pauli Z
snapshot values. -/
theorem quadratic_z_kernel (a b : Fin 1 → Fin 3 × Bool) :
    quadraticShadowKernel 1 (TensorGate pauliZ pauliZ) a b =
      tensorPauliValue (fun _ => some (2 : Fin 3)) a *
        tensorPauliValue (fun _ => some (2 : Fin 3)) b := by
  rw [quadraticShadowKernel, quadratic_symmetric_trace,
    tensorGate_mul, tensorGate_mul]
  simp only [TensorGate, Matrix.trace_kronecker]
  rw [← quadratic_z_word, tensorPauliValue_trace, tensorPauliValue_trace]
  simp [Complex.mul_re]
  ring

/-- The trace pairing of Pauli Z with the maximally mixed qubit is zero. -/
private theorem quadratic_z_target :
    Matrix.trace (pauliZ * ((1/2:ℂ) • (1:Operator 2))) = 0 := by
  norm_num [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace,
    Fin.sum_univ_two, pauliZ]

/-- For the maximally mixed qubit, averaging the quadratic Z kernel over its second record gives
zero for every first record. -/
theorem quadratic_z_conditional_zero
    (hρ : IsDensityOperator ((1/2:ℂ) • (1:Operator 2)))
    (a : Fin 1 → Fin 3 × Bool) :
    (∑ b, (tensorPauliLaw 1 ((1/2:ℂ) • (1:Operator 2)) hρ).prob b *
      quadraticShadowKernel 1 (TensorGate pauliZ pauliZ) a b) = 0 := by
  rw [quadraticShadowKernel_conditional, quadratic_symmetric_trace,
    tensorGate_mul, tensorGate_mul]
  simp only [TensorGate, Matrix.trace_kronecker]
  rw [quadratic_z_target]
  simp

/-- For at least two records from the maximally mixed qubit, the quadratic Z U-statistic has
mean zero and second moment `18 / (m * (m - 1))`. This is a concrete degenerate-kernel
variance example in the setting of [HuangKuengPreskill2020]. -/
theorem quadratic_z_square_degenerate_variance_consumer (m : ℕ)
    (hρ : IsDensityOperator ((1/2:ℂ) • (1:Operator 2))) (hm : 2 ≤ m) :
    let ρ : Operator (2^1) := (1/2:ℂ) • 1
    let O := TensorGate pauliZ pauliZ
    (∑ ω : Fin m → Fin 1 → Fin 3 × Bool,
      (tensorPauliLaw 1 ρ hρ).probOf ω * quadraticShadowU 1 m O ω) = 0 ∧
    (∑ ω : Fin m → Fin 1 → Fin 3 × Bool,
      (tensorPauliLaw 1 ρ hρ).probOf ω * quadraticShadowU 1 m O ω ^ 2) =
        18/((m:ℝ)*(m-1:ℕ)) := by
  (try dsimp only)
  let ρ : Operator 2 := (1/2:ℂ) • 1
  let O := TensorGate pauliZ pauliZ
  let p := tensorPauliLaw 1 ρ hρ
  let f := tensorPauliValue (fun _ : Fin 1 => some (2 : Fin 3))
  have hO : O.IsHermitian := by
    unfold O Matrix.IsHermitian
    rw [tensorGate_conjTranspose]
    have hz : pauliZᴴ = pauliZ := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [pauliZ, Matrix.conjTranspose_apply]
    rw [hz]
  have ht : (Matrix.trace (O * TensorGate ρ ρ)).re = 0 := by
    rw [tensorGate_mul]
    simp only [TensorGate, Matrix.trace_kronecker, ρ, quadratic_z_target, mul_zero, Complex.zero_re]
  have hf : (∑ a, p.prob a * f a) = 0 := by
    have hh := tensorPauliValue_mean 1 ρ hρ (fun _ => some (2 : Fin 3))
    rw [quadratic_z_word] at hh
    change (∑ a, p.prob a * f a) = _ at hh
    rw [show Matrix.trace (pauliZ * ρ) = 0 from quadratic_z_target, Complex.zero_re] at hh
    exact hh
  have hf2 : (∑ a, p.prob a * f a ^ 2) = 3 := by
    have hh := tensorPauliValue_second_moment 1 ρ hρ (fun _ => some (2 : Fin 3))
    simpa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, tensorPauliWeight] using hh
  have hmean : pairKernelMean p (quadraticShadowKernel 1 O) = 0 := by
    rw [quadraticShadowKernel_mean, ht]
  have hc : pairConditionalVariance p (quadraticShadowKernel 1 O) = 0 := by
    simp only [pairConditionalVariance, hmean, sub_zero]
    change (∑ a,
        p.prob a * (∑ b, p.prob b * quadraticShadowKernel 1 (TensorGate pauliZ pauliZ) a b)^2) = 0
    simp_rw [quadratic_z_kernel]
    change (∑ a, p.prob a * (∑ b, p.prob b * (f a * f b))^2) = 0
    simp_rw [show ∀ a b, p.prob b * (f a * f b) = f a * (p.prob b * f b)
      from fun a b => by ring, ← Finset.mul_sum, hf]
    simp
  have hp : pairKernelVariance p (quadraticShadowKernel 1 O) = 9 := by
    simp only [pairKernelVariance, hmean, sub_zero]
    change (∑ a, ∑ b,
        p.prob a * p.prob b * quadraticShadowKernel 1 (TensorGate pauliZ pauliZ) a b ^ 2) = 9
    simp_rw [quadratic_z_kernel, mul_pow]
    change (∑ a, ∑ b, p.prob a * p.prob b * (f a ^ 2 * f b ^ 2)) = 9
    simp_rw [show ∀ a b, p.prob a * p.prob b * (f a ^ 2 * f b ^ 2) =
      (p.prob a * f a ^ 2) * (p.prob b * f b ^ 2) from fun a b => by ring,
      ← Finset.mul_sum, hf2]
    rw [← Finset.sum_mul, hf2]
    norm_num
  constructor
  · rw [quadratic_shadow_actual_u_unbiased 1 m ρ hρ O hm hO, ht]
  · have hh := quadratic_shadow_exact_covariance_from_same_records 1 m ρ hρ O hm hO
    dsimp only at hh
    simp only [ht, sub_zero] at hh
    rw [hc, hp, mul_zero, zero_add] at hh
    calc _ = 2/((m:ℝ)*(m-1:ℕ))*9 := hh
      _ = _ := by ring

/-- Gives the exact quantum resource and pair-evaluation counts for `2 * r + 1` blocks of `m`
one-qubit records, together with the median read count and quadratic comparison bound. -/
theorem quadratic_z_actual_resources (m r : ℕ)
    (ω : Fin (2*r+1) → Fin m → Fin 1 → Fin 3 × Bool) :
    tensorPauliFreshResourceCounts 1 m (2*r+1) ω =
      ((2*r+1)*m, 2*((2*r+1)*m), (2*r+1)*m, 0) ∧
    (∑ b, (pairUCounted (quadraticShadowKernel 1 (TensorGate pauliZ pauliZ)) (ω b)).2) =
      (2*r+1)*m.choose 2 ∧
    (quadraticShadowMedianCounted 1 m r (TensorGate pauliZ pauliZ) ω).2.1 = 2*r+1 ∧
    (quadraticShadowMedianCounted 1 m r (TensorGate pauliZ pauliZ) ω).2.2 ≤ (2*r+1)^2 := by
  have h := quadratic_shadow_actual_quantum_and_pair_ledger 1 m r (TensorGate pauliZ pauliZ) ω
  have hs := quadraticShadowMedianCounted_spec 1 m r (TensorGate pauliZ pauliZ) ω
  exact ⟨by simpa only [mul_one, one_mul] using h.1, h.2, hs.2⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision
