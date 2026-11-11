/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.DistinctFourierNoise
import Mathlib.Data.Finset.Powerset
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Fourier measurements of distinct noise sets

This module computes forward and inverse Fourier amplitudes for `distinctNoiseState`, the
normalized uniform state on a finite set. It also verifies a marking query followed by a Fourier
gate and computes the mean probability at a nonzero frequency over fixed-size subsets.

These statements describe the uniform subset Fourier model related to [Cornwell2014]; the
formulas here concern the set state and its marked circuit.

## Main statements

* `distinct_noise_actual_quantum_fourier_born`: gives the Fourier Born probability.
* `distinct_noise_actual_marked_fourier_circuit`: verifies unitarity, counts, and output state.
* `distinct_noise_actual_record_fourier_born_mean`: computes the nonzero-frequency mean.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false


open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The uniform state on a set of positive cardinality `L` has Euclidean norm one. -/
theorem distinct_noise_uniform_set_state_norm {N L : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hL : 0 < L) (hS : S.card = L) : ‖toEuclidean_fromVec (distinctNoiseState S)‖ = 1 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hsqrt : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos_of_pos hLp
  have hs : ‖((Real.sqrt (L : ℝ) : ℂ))⁻¹‖ = (Real.sqrt (L : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hsqrt.le]
  have hh := norm_toEuclidean_fromVec_sq (distinctNoiseState S)
  simp only [distinctNoiseState, hS, apply_ite norm, norm_zero, ite_pow,
    zero_pow (by norm_num : 2 ≠ 0), hs] at hh
  rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, hS, inv_pow,
    Real.sq_sqrt hLp.le, mul_inv_cancel₀ hLp.ne'] at hh
  nlinarith [norm_nonneg (toEuclidean_fromVec (distinctNoiseState S))]

/-- The forward Fourier amplitude of a set state is `distinctNoiseFourier S y` divided by the
square roots of `N` and `L`. -/
theorem distinct_noise_actual_fourier_amplitude {N L : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hS : S.card = L) (y : ZMod N) :
    (zmodQFTGate.mulVec (distinctNoiseState S)) y =
      ((Real.sqrt (N : ℝ) : ℂ)⁻¹*(Real.sqrt (L : ℝ) : ℂ)⁻¹)*distinctNoiseFourier S y := by
  simp only [Matrix.mulVec, dotProduct, zmodQFTGate_apply, distinctNoiseState, hS]
  have he (x : ZMod N) : (Real.sqrt (N : ℝ) : ℂ)⁻¹*ZMod.stdAddChar (y*x)*
      (if x∈S then (Real.sqrt (L : ℝ) : ℂ)⁻¹ else 0) =
      if x∈S then ((Real.sqrt (N : ℝ) : ℂ)⁻¹*(Real.sqrt (L : ℝ) : ℂ)⁻¹)*ZMod.stdAddChar (x*y) else 0 := by
    split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]
  simp_rw [he]
  rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rfl

/-- For a set of positive cardinality `L`, the state is normalized and its forward Fourier Born
probability is `‖distinctNoiseFourier S y‖^2 / (N * L)`. This is the uniform set-state model
associated with [Cornwell2014]. -/
theorem distinct_noise_actual_quantum_fourier_born (N L : ℕ) [NeZero N] (S : Finset (ZMod N)) (y : ZMod N)
    (hL : 0 < L) (hS : S.card = L) :
    ‖toEuclidean_fromVec (distinctNoiseState S)‖ = 1 ∧
    ‖(zmodQFTGate.mulVec (distinctNoiseState S)) y‖^2 =
      ‖distinctNoiseFourier S y‖^2/((N : ℝ)*L) := by
  refine ⟨distinct_noise_uniform_set_state_norm S hL hS, ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  rw [distinct_noise_actual_fourier_amplitude S hS y]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt hNp.le, Real.sq_sqrt hLp.le]
  ring

/-- The inverse Fourier amplitude of a set state is the conjugate of `distinctNoiseFourier S y`
divided by the square roots of `N` and `L`. -/
theorem distinct_noise_actual_inverse_fourier_amplitude {N L : ℕ} [NeZero N] (S : Finset (ZMod N))
    (hS : S.card = L) (y : ZMod N) :
    ((zmodQFTGate (N := N))ᴴ.mulVec (distinctNoiseState S)) y =
      ((Real.sqrt (N : ℝ) : ℂ)⁻¹*(Real.sqrt (L : ℝ) : ℂ)⁻¹)*star (distinctNoiseFourier S y) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, zmodQFTGate_apply,
    distinctNoiseState, hS]
  have he (x : ZMod N) : star ((Real.sqrt (N : ℝ) : ℂ)⁻¹*ZMod.stdAddChar (x*y))*
      (if x∈S then (Real.sqrt (L : ℝ) : ℂ)⁻¹ else 0) =
      if x∈S then ((Real.sqrt (N : ℝ) : ℂ)⁻¹*(Real.sqrt (L : ℝ) : ℂ)⁻¹)*star (ZMod.stdAddChar (x*y)) else 0 := by
    split_ifs <;> simp [star_mul, mul_assoc, mul_comm, mul_left_comm]
  simp_rw [he]
  rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rw [distinctNoiseFourier, star_sum]

/-- For a set of positive cardinality `L`, the inverse Fourier Born probability is
`‖distinctNoiseFourier S y‖^2 / (N * L)`. -/
theorem distinct_noise_actual_inverse_quantum_fourier_born (N L : ℕ) [NeZero N] (S : Finset (ZMod N)) (y : ZMod N)
    (hL : 0 < L) (hS : S.card = L) :
    ‖((zmodQFTGate (N := N))ᴴ.mulVec (distinctNoiseState S)) y‖^2 =
      ‖distinctNoiseFourier S y‖^2/((N : ℝ)*L) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  rw [distinct_noise_actual_inverse_fourier_amplitude S hS y]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    norm_star, mul_pow, inv_pow, Real.sq_sqrt hNp.le, Real.sq_sqrt hLp.le]
  ring

/-- A circuit consisting of one query followed by the forward or inverse cyclic Fourier gate. -/
noncomputable def distinctNoiseFourierCircuit {N : ℕ} [NeZero N] (inverse : Bool) : Circuit (ZMod N) :=
  [.query, .gate (if inverse then (zmodQFTGate (N := N))ᴴ else zmodQFTGate)]

/-- The set marking oracle acts as multiplication by `-1` on its own set state. -/
private theorem distinctNoise_mark_input {N : ℕ} [NeZero N] (S : Finset (ZMod N)) :
    ApplyGate (SetOracle S) (distinctNoiseState S) = -(distinctNoiseState S) := by
  ext x
  change ApplyGate (PhaseOracle (fun x => decide (x∈S))) (distinctNoiseState S) x = _
  rw [applyGate_phaseOracle]
  by_cases hx : x∈S <;> simp [distinctNoiseState, hx]

/-- The marking oracle and Fourier circuit are unitary, the circuit uses one query and one gate,
and its output is the negative of the selected Fourier transform of the set state. -/
theorem distinct_noise_actual_marked_fourier_circuit (N : ℕ) [NeZero N] (S : Finset (ZMod N)) (inverse : Bool) :
    SetOracle S ∈ Matrix.unitaryGroup (ZMod N) ℂ ∧
    IsUnitaryCircuit (distinctNoiseFourierCircuit (N := N) inverse) ∧
    QueryCount (distinctNoiseFourierCircuit (N := N) inverse) = 1 ∧
    GateCount (distinctNoiseFourierCircuit (N := N) inverse) = 1 ∧
    Run (SetOracle S) (distinctNoiseFourierCircuit inverse) (distinctNoiseState S) =
      -(if inverse then ((zmodQFTGate (N := N))ᴴ.mulVec (distinctNoiseState S))
          else (zmodQFTGate.mulVec (distinctNoiseState S))) := by
  have hW := zmodQFTGate_unitary (N := N) (NeZero.pos N)
  have hWa : (zmodQFTGate (N := N))ᴴ ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').mp hW
  refine ⟨setOracle_unitary S, ?_, by simp [distinctNoiseFourierCircuit],
    by simp [distinctNoiseFourierCircuit], ?_⟩
  · cases inverse <;> simp [distinctNoiseFourierCircuit, hW, hWa]
  · simp only [distinctNoiseFourierCircuit, run_query, run_gate, run_nil, distinctNoise_mark_input]
    cases inverse <;> simp [ApplyGate, Matrix.mulVec_neg]

/-- The marked Fourier circuit has Born probability `‖distinctNoiseFourier S y‖^2 / (N * L)` for
either Fourier direction. -/
theorem distinct_noise_actual_marked_circuit_born (N L : ℕ) [NeZero N] (S : Finset (ZMod N)) (y : ZMod N)
    (inverse : Bool) (hL : 0 < L) (hS : S.card = L) :
    ‖(Run (SetOracle S) (distinctNoiseFourierCircuit inverse) (distinctNoiseState S)) y‖^2 =
      ‖distinctNoiseFourier S y‖^2/((N : ℝ)*L) := by
  rw [(distinct_noise_actual_marked_fourier_circuit N S inverse).2.2.2.2]
  cases inverse
  · simpa only [Bool.false_eq_true, if_false, Pi.neg_apply, norm_neg] using
      (distinct_noise_actual_quantum_fourier_born N L S y hL hS).2
  · simpa only [if_true, Pi.neg_apply, norm_neg] using
      distinct_noise_actual_inverse_quantum_fourier_born N L S y hL hS

/-- For a nonzero frequency, the mean marked-circuit Born probability over all `L`-element
subsets is `(N - L) / (N * (N - 1))`. Each such circuit has normalized input and output, a
unitary oracle, and one query and one gate. -/
theorem distinct_noise_actual_record_fourier_born_mean (N L : ℕ) [NeZero N] (y : ZMod N)
    (inverse : Bool) (hN : 1 < N) (hL : 0 < L) (hLN : L ≤ N) (hy : y ≠ 0) :
    distinctNoiseMean N L (fun S =>
      ((‖(Run (SetOracle S) (distinctNoiseFourierCircuit inverse) (distinctNoiseState S)) y‖^2 : ℝ) : ℂ)) =
      (N-L : ℂ)/(N*(N-1)) ∧
    ∀ S∈distinctNoiseSets N L,
      ‖toEuclidean_fromVec (distinctNoiseState S)‖ = 1 ∧
      SetOracle S ∈ Matrix.unitaryGroup (ZMod N) ℂ ∧
      IsUnitaryCircuit (distinctNoiseFourierCircuit (N := N) inverse) ∧
      QueryCount (distinctNoiseFourierCircuit (N := N) inverse) = 1 ∧
      GateCount (distinctNoiseFourierCircuit (N := N) inverse) = 1 ∧
      ‖toEuclidean_fromVec (Run (SetOracle S) (distinctNoiseFourierCircuit inverse) (distinctNoiseState S))‖ = 1 := by
  obtain ⟨hmean,hrecord⟩ := distinct_noise_marked_fourier_consumer N L y hN hL hLN hy
  constructor
  · have he : distinctNoiseMean N L (fun S =>
        ((‖(Run (SetOracle S) (distinctNoiseFourierCircuit inverse) (distinctNoiseState S)) y‖^2 : ℝ) : ℂ)) =
        distinctNoiseMean N L (fun S =>
          ((N*L : ℂ)⁻¹)*(distinctNoiseFourier S y*star (distinctNoiseFourier S y))) := by
      unfold distinctNoiseMean
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      (try dsimp only)
      rw [distinct_noise_actual_marked_circuit_born N L S y inverse hL (hrecord S hS).1]
      simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    exact he.trans hmean
  · intro S hS
    have hcard := (hrecord S hS).1
    have hn := (distinct_noise_actual_quantum_fourier_born N L S y hL hcard).1
    obtain ⟨hO,hC,hq,hg,_⟩ := distinct_noise_actual_marked_fourier_circuit N S inverse
    refine ⟨hn,hO,hC,hq,hg,?_⟩
    exact (normalized_iff_norm_toEuclidean_fromVec _).mp
      (hC.normalized_run hO ((normalized_iff_norm_toEuclidean_fromVec _).mpr hn))

end Qatlib.Concepts.HspRecovery.ReductionCore
