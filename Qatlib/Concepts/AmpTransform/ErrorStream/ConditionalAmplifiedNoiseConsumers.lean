/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ConditionalAmplifiedNoise
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# Conditional noise means for actual amplified QFT circuits

`conditionalAmplifiedQFTCircuit` performs prepared amplitude amplification followed by the QFT.
At nonzero frequency, `conditional_amplified_qft_born` expresses its Born probability using
`conditionalAmplifiedGain` and the marked-set Fourier sum.

The conditional-noise results combine this identity with exact complement moments and record
unitarity and circuit costs. For a subgroup-coset signal, the resulting formula separates
frequencies by membership in the annihilator.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `conditional_amplified_qft_born`: the actual nonzero-frequency probability formula.
* `conditional_noise_actual_amplified_qft`: fixed-cardinality conditional Born means.
* `conditional_periodic_noise_actual_qft`: the subgroup-coset specialization.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open Matrix
open scoped Classical BigOperators

/-- The prepared amplitude-amplification circuit with `k` rounds followed by a QFT on `ZMod N`. -/
def conditionalAmplifiedQFTCircuit (N k : ℕ) [NeZero N] : Circuit (ZMod N) :=
  preparedAACircuit (zmodQFTGate (N := N)) 0 k ++ [.gate zmodQFTGate]

/-- The difference of the marked and unmarked amplification coefficients, `sin ((2 * k + 1) * θ)
/ sin θ - cos ((2 * k + 1) * θ) / cos θ`. -/
def conditionalAmplifiedGain (k : ℕ) (θ : ℝ) : ℝ :=
  Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ -
    Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ

/-- The QFT-prepared state from `Ket 0` has constant amplitude equal to the inverse square root
of `N`. -/
private theorem conditional_uniform_entry (N : ℕ) [NeZero N] (x : ZMod N) :
    preparedAAState (zmodQFTGate (N := N)) 0 x = (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by
  simp [preparedAAState, ApplyGate, Matrix.mulVec, dotProduct, Ket, zmodQFTGate_apply]

/-- The prepared uniform state assigns probability `S.card / N` to the set `S`. -/
private theorem conditional_uniform_mass (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    MeasureProb (preparedAAState (zmodQFTGate (N := N)) 0) S = (S.card : ℝ)/N := by
  simp only [MeasureProb, BornProb, conditional_uniform_entry, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), Finset.sum_const, nsmul_eq_mul]
  ring

/-- The QFT of the unnormalized restriction of the prepared uniform state to `S` has amplitude
`N⁻¹ * distinctNoiseFourier S y`. -/
private theorem conditional_qft_selected (N : ℕ) [NeZero N]
    (S : Finset (ZMod N)) (y : ZMod N) :
    ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) S) y =
      (N : ℂ)⁻¹*distinctNoiseFourier S y := by
  have hs : (Real.sqrt (N : ℝ) : ℂ)⁻¹*(Real.sqrt (N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  simp only [ApplyGate, Matrix.mulVec, dotProduct, zmodQFTGate_apply,
    collapse_apply, conditional_uniform_entry]
  have he (x : ZMod N) : (Real.sqrt (N : ℝ) : ℂ)⁻¹*ZMod.stdAddChar (y*x)*
      (if x ∈ S then (Real.sqrt (N : ℝ) : ℂ)⁻¹ else 0) =
      if x ∈ S then (N : ℂ)⁻¹*ZMod.stdAddChar (x*y) else 0 := by
    by_cases hx : x ∈ S
    · simp only [if_pos hx]
      rw [mul_right_comm, hs, mul_comm y x]
    · simp [hx]
  simp_rw [he]
  rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rfl

/-- The Fourier sum over all of `ZMod N` vanishes at every nonzero frequency. -/
theorem conditional_full_fourier_zero (N : ℕ) [NeZero N] (y : ZMod N) (hy : y ≠ 0) :
    distinctNoiseFourier Finset.univ y = 0 := by
  unfold distinctNoiseFourier
  simp_rw [mul_comm _ y]
  rw [sum_stdAddChar_mul, if_neg hy]

/-- At a nonzero frequency, the QFT of the prepared uniform state has amplitude zero. -/
private theorem conditional_qft_uniform_zero (N : ℕ) [NeZero N]
    (y : ZMod N) (hy : y ≠ 0) :
    ApplyGate zmodQFTGate (preparedAAState (zmodQFTGate (N := N)) 0) y = 0 := by
  have hc : Collapse (preparedAAState (zmodQFTGate (N := N)) 0) Finset.univ =
      preparedAAState (zmodQFTGate (N := N)) 0 := by
    ext x; simp [collapse_apply]
  rw [← hc, conditional_qft_selected, conditional_full_fourier_zero N y hy, mul_zero]

/-- For a nonzero frequency and a marked-density angle in `(0, π / 2)`, the actual amplified-QFT
Born probability equals the squared amplification gain times the marked Fourier squared norm
divided by `N ^ 2`. -/
theorem conditional_amplified_qft_born (N k : ℕ) [NeZero N]
    (B : Finset (ZMod N)) (y : ZMod N) (θ : ℝ) (hy : y ≠ 0)
    (hθ : 0 < θ) (hθp : θ < Real.pi/2)
    (hm : (Real.sin θ)^2 = (B.card : ℝ)/N) :
    BornProb (Run (preparedMark B) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) y =
      (conditionalAmplifiedGain k θ)^2/(N : ℝ)^2 * ‖distinctNoiseFourier B y‖^2 := by
  have hr := prepared_aa_actual_rotation (zmodQFTGate (N := N)) 0 B θ k
    (zmodQFTGate_unitary (NeZero.pos N)) hθ hθp
    ((conditional_uniform_mass N B).trans hm.symm)
  have ha : Run (preparedMark B) (conditionalAmplifiedQFTCircuit N k) (Ket 0) y =
      (Complex.ofReal (conditionalAmplifiedGain k θ)/(N : ℂ))*distinctNoiseFourier B y := by
    rw [conditionalAmplifiedQFTCircuit, run_append, run_gate, run_nil, hr]
    simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    change Complex.ofReal (Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ)*
        (ApplyGate zmodQFTGate (preparedAAState (zmodQFTGate (N := N)) 0) y -
          ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) B) y) +
      Complex.ofReal (Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ)*
        ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) B) y = _
    rw [conditional_qft_uniform_zero N y hy, conditional_qft_selected]
    simp only [conditionalAmplifiedGain, Complex.ofReal_sub]
    ring
  rw [BornProb, ha, norm_mul, norm_div, Complex.norm_real, Complex.norm_natCast,
    mul_pow, div_pow, Real.norm_eq_abs, sq_abs]

/-- For feasible fixed-cardinality complement noise with nonsaturated positive marked size,
establish circuit unitarity and costs and the exact nonzero-frequency mean Born probability
from the mixed Fourier moment; see [Cornwell, Section 3.4.4][Cornwell2014]. -/
theorem conditional_noise_actual_amplified_qft :
    ∀ (N L k : ℕ) [NeZero N] (A : Finset (ZMod N)) (y : ZMod N) (θ : ℝ),
      let C := Finset.univ \ A
      2 ≤ C.card → L ≤ C.card → 0 < A.card+L → A.card+L < N → y ≠ 0 →
      0 < θ → θ < Real.pi/2 → (Real.sin θ)^2 = ((A.card+L : ℕ) : ℝ)/N →
      let T := C.powersetCard L
      let w := preparedAACircuit (zmodQFTGate (N := N)) 0 k ++ [.gate zmodQFTGate]
      let a := distinctNoiseFourier A y
      let c := distinctNoiseFourier C y
      let p₂ := (L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1))
      let g := Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ -
        Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ
      IsUnitaryCircuit w ∧ QueryCount w = k ∧ GateCount w = 3*k+2 ∧
      (∀ S ∈ T, Disjoint A S ∧ (A ∪ S).card = A.card+L) ∧
      ((T.card : ℝ)⁻¹ * ∑ S ∈ T, BornProb
        (Run (preparedMark (A ∪ S)) w (Ket 0)) y) =
        g^2/(N : ℝ)^2 *
          (‖a‖^2+2*(L : ℝ)/C.card*(a*star c).re+L+p₂*(‖c‖^2-C.card)) := by
  intro N L k _ A y θ C hC hL _ _ hy hθ hθp hm
  (try dsimp only)
  have hU := zmodQFTGate_unitary (N := N) (NeZero.pos N)
  have hw := prepared_aa_actual_circuit (zmodQFTGate (N := N)) 0 A k hU
  have hsets : ∀ S ∈ C.powersetCard L, Disjoint A S ∧ (A ∪ S).card = A.card+L := by
    intro S hS
    exact conditional_noise_record A S L hS
  refine ⟨by simp [hw.1, hU], by simp [queryCount_append, hw.2.1],
    by simp [gateCount_append, hw.2.2.1], hsets, ?_⟩
  change conditionalNoiseMean C L (fun S => BornProb
    (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) y) = _
  have he : conditionalNoiseMean C L (fun S => BornProb
      (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) y) =
      conditionalNoiseMean C L (fun S => (conditionalAmplifiedGain k θ)^2/(N : ℝ)^2 *
        ‖distinctNoiseFourier (A ∪ S) y‖^2) := by
    unfold conditionalNoiseMean
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    (try dsimp only)
    apply conditional_amplified_qft_born N k (A ∪ S) y θ hy hθ hθp
    rw [(hsets S hS).2]
    exact hm
  have hmoment := (conditional_signal_noise_mixed_second_moment N L A y hC hL).2
  change conditionalNoiseMean C L (fun S => ‖distinctNoiseFourier (A ∪ S) y‖^2) = _ at hmoment
  rw [he, conditionalNoiseMean_mul_left, hmoment]
  rfl

/-- At a nonzero frequency, the Fourier sum of the complement of `A` is the negative of the
Fourier sum of `A`. -/
theorem conditional_complement_fourier (N : ℕ) [NeZero N]
    (A : Finset (ZMod N)) (y : ZMod N) (hy : y ≠ 0) :
    distinctNoiseFourier (Finset.univ \ A) y = -distinctNoiseFourier A y := by
  have hdis : Disjoint A (Finset.univ \ A) := Finset.disjoint_left.mpr
    fun _ hx hc => (Finset.mem_sdiff.mp hc).2 hx
  have hs : distinctNoiseFourier A y+distinctNoiseFourier (Finset.univ \ A) y = 0 := by
    unfold distinctNoiseFourier
    rw [← Finset.sum_union hdis, Finset.union_sdiff_of_subset (Finset.subset_univ A)]
    exact conditional_full_fourier_zero N y hy
  exact eq_neg_of_add_eq_zero_right hs

/-- The finite coset `s + H` of an additive subgroup of `ZMod N`. -/
def conditionalPeriodicSignal {N : ℕ} [NeZero N]
    (H : AddSubgroup (ZMod N)) [Fintype H] (s : ZMod N) : Finset (ZMod N) :=
  Finset.univ.image (fun h : H => s+(h : ZMod N))

/-- The periodic signal coset has cardinality `Fintype.card H`. -/
theorem conditional_periodic_signal_card {N : ℕ} [NeZero N]
    (H : AddSubgroup (ZMod N)) [Fintype H] (s : ZMod N) :
    (conditionalPeriodicSignal H s).card = Fintype.card H := by
  rw [conditionalPeriodicSignal, Finset.card_image_of_injective]
  · simp
  · intro x y h
    exact Subtype.ext (add_left_cancel h)

/-- The squared Fourier norm of a subgroup coset is the squared subgroup cardinality on its
annihilator and zero elsewhere. -/
theorem conditional_periodic_signal_fourier {N : ℕ} [NeZero N]
    (H : AddSubgroup (ZMod N)) [Fintype H] (s y : ZMod N) :
    ‖distinctNoiseFourier (conditionalPeriodicSignal H s) y‖^2 =
      if y ∈ annihilatorOf H then (Fintype.card H : ℝ)^2 else 0 := by
  have hinj : Function.Injective (fun h : H => s+(h : ZMod N)) := by
    intro x y h; exact Subtype.ext (add_left_cancel h)
  have hf : distinctNoiseFourier (conditionalPeriodicSignal H s) y =
      ZMod.stdAddChar (s*y)*(if y ∈ annihilatorOf H then (Fintype.card H : ℂ) else 0) := by
    rw [distinctNoiseFourier, conditionalPeriodicSignal, Finset.sum_image (fun x _ z _ h => hinj h)]
    simp only [add_mul, AddChar.map_add_eq_mul]
    rw [← Finset.mul_sum]
    simp_rw [mul_comm _ y]
    rw [sum_stdAddChar_subgroup]
  by_cases hy : y ∈ annihilatorOf H
  · simp only [hf, if_pos hy, norm_mul, norm_stdAddChar, one_mul, Complex.norm_natCast]
  · simp [hf, hy]

/-- For a subgroup-coset signal and feasible complement noise, compute the conditional
amplified-QFT mean Born probability by annihilator membership, with circuit and disjointness
guarantees under the stated density-angle assumptions; see [Cornwell2014]. -/
theorem conditional_periodic_noise_actual_qft (N L k : ℕ) [NeZero N]
    (H : AddSubgroup (ZMod N)) [Fintype H] (s y : ZMod N) (θ : ℝ)
    (hC : 2 ≤ (Finset.univ \ conditionalPeriodicSignal H s).card)
    (hL : L ≤ (Finset.univ \ conditionalPeriodicSignal H s).card)
    (hpos : 0 < Fintype.card H+L) (hlt : Fintype.card H+L < N)
    (hy : y ≠ 0) (hθ : 0 < θ) (hθp : θ < Real.pi/2)
    (hm : (Real.sin θ)^2 = ((Fintype.card H+L : ℕ) : ℝ)/N) :
    let A := conditionalPeriodicSignal H s
    let C := Finset.univ \ A
    let q := (L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1))
    IsUnitaryCircuit (conditionalAmplifiedQFTCircuit N k) ∧
    QueryCount (conditionalAmplifiedQFTCircuit N k) = k ∧
    GateCount (conditionalAmplifiedQFTCircuit N k) = 3*k+2 ∧
    (∀ S ∈ C.powersetCard L, Disjoint A S ∧ (A ∪ S).card = Fintype.card H+L) ∧
    conditionalNoiseMean C L (fun S => BornProb
      (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) y) =
      (conditionalAmplifiedGain k θ)^2/(N : ℝ)^2 *
        ((1-2*(L : ℝ)/C.card+q)*
          (if y ∈ annihilatorOf H then (Fintype.card H : ℝ)^2 else 0)+L-q*C.card) := by
  have hc := conditional_periodic_signal_card H s
  have hall := conditional_noise_actual_amplified_qft N L k
    (conditionalPeriodicSignal H s) y θ hC hL (by simpa [hc] using hpos)
    (by simpa [hc] using hlt) hy hθ hθp (by simpa [hc] using hm)
  dsimp only at hall ⊢
  refine ⟨hall.1, hall.2.1, hall.2.2.1, ?_, ?_⟩
  · intro S hS
    simpa only [hc] using hall.2.2.2.1 S hS
  · have hborn := hall.2.2.2.2
    change conditionalNoiseMean (Finset.univ \ conditionalPeriodicSignal H s) L _ = _ at hborn
    simp only [conditionalAmplifiedQFTCircuit]
    rw [hborn, conditional_complement_fourier N _ y hy]
    simp only [norm_neg, star_neg, mul_neg, Complex.neg_re, Complex.star_def,
      Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [conditional_periodic_signal_fourier]
    unfold conditionalAmplifiedGain
    ring

end Qatlib.Concepts.AmpTransform.ErrorStream
