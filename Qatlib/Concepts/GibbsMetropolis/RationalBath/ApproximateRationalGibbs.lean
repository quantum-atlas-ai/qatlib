/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalBoltzmannWeights
import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalHeatBathChannel

/-!
# Rational approximation of diagonal Gibbs states

`rationalEnergyGibbsDensity` is the diagonal Gibbs target for rational energies at unit inverse
temperature. The module compares it with the heat-bath state built from integer-scaled Taylor
weights, using an explicit trace-norm error.

The final estimate includes an arbitrary finite reference register and bounds one heat-bath
application at the selected precision. See [TemmeEtAl2011] for background.

## Main statements

* `rational_energy_gibbs_target_and_trace_accuracy`: For a nonempty system with energies in `[0,
  1]`, the Gibbs target is a density operator and its integer-weight heat-bath approximation has
  trace-norm error at most `4 * (1 / 2) ^ K`.
* `rational_energy_gibbs_actual_reference_precision`: For positive semidefinite system-reference
  inputs and energies in `[0, 1]`, the specified Taylor precision and rejection cutoff give one
  heat-bath step error at most `(1 / 2) ^ k` times the input trace norm.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The diagonal matrix with normalized weights `exp (-E i)` for rational energies `E`. -/
noncomputable def rationalEnergyGibbsDensity {N : ℕ} (E : Fin N → ℚ) : Operator N :=
  Matrix.diagonal fun i => Complex.ofReal (Real.exp (-(E i:ℝ)) / ∑ j, Real.exp (-(E j:ℝ)))

/-- The trace norm of a real diagonal complex matrix is the sum of the absolute values of its
diagonal entries. -/
theorem real_diagonal_traceNorm {N : ℕ} (d : Fin N → ℝ) :
    Matrix.traceNorm (Matrix.diagonal fun i => (d i : ℂ)) = ∑ i, |d i| := by
  open MatrixOrder in
  have hs : CFC.sqrt ((Matrix.diagonal fun i => (d i:ℂ))ᴴ *
      (Matrix.diagonal fun i => (d i:ℂ))) = Matrix.diagonal fun i => ((|d i|:ℝ):ℂ) := by
    apply CFC.sqrt_unique
    · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
        ← Complex.ofReal_mul]
      congr 1
      nlinarith [sq_abs (d i)]
    · apply Matrix.PosSemidef.nonneg
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast abs_nonneg (d i)
  unfold Matrix.traceNorm
  rw [hs]
  simp

/-- The trace norm of a positive semidefinite complex matrix equals the real part of its trace. -/
theorem rationalGibbs_psd_traceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.PosSemidef) : Matrix.traceNorm X = (Matrix.trace X).re := by
  simpa using congrArg Complex.re hX.traceNorm_eq_trace

/-- Tensoring a real diagonal matrix with a positive semidefinite matrix has trace norm at most
the diagonal absolute sum times the latter trace norm. -/
theorem real_diagonal_tensor_traceNorm_le {N r : ℕ} (d : Fin N → ℝ)
    (Y : Operator r) (hY : Y.PosSemidef) :
    Matrix.traceNorm (TensorGate (Matrix.diagonal fun i => (d i:ℂ)) Y) ≤
      (∑ i, |d i|) * Matrix.traceNorm Y := by
  let P (i : Fin N) : Operator N := Matrix.diagonal fun j => if j=i then 1 else 0
  have hP (i : Fin N) : IsDensityOperator (P i) := by
    constructor
    · rw [Matrix.posSemidef_diagonal_iff]
      intro j
      split_ifs <;> norm_num
    · simp [P, Matrix.trace_diagonal]
  have hn (i : Fin N) : Matrix.traceNorm (TensorGate (P i) Y) = Matrix.traceNorm Y := by
    rw [rationalGibbs_psd_traceNorm _ (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate (hP i).1 hY),
      rationalGibbs_psd_traceNorm Y hY, Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate, (hP i).2, one_mul]
  have he : TensorGate (Matrix.diagonal fun i => (d i:ℂ)) Y =
      ∑ i, (d i:ℂ) • TensorGate (P i) Y := by
    ext a b
    simp [TensorGate, Matrix.kroneckerMap_apply, Matrix.sum_apply, P,
      Matrix.diagonal_apply, Matrix.smul_apply]
  rw [he]
  calc
    _ ≤ ∑ i, Matrix.traceNorm ((d i:ℂ) • TensorGate (P i) Y) := by
      have hsum (s : Finset (Fin N)) :
          Matrix.traceNorm (∑ i ∈ s, (d i:ℂ) • TensorGate (P i) Y) ≤
            ∑ i ∈ s, Matrix.traceNorm ((d i:ℂ) • TensorGate (P i) Y) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
          simp only [Finset.sum_insert hi]
          exact (Matrix.traceNorm_add_le _ _).trans (add_le_add_right ih _)
      exact hsum Finset.univ
    _ = (∑ i, |d i|) * Matrix.traceNorm Y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.traceNorm_smul, hn, Complex.norm_real, Real.norm_eq_abs]

/-- On a nonempty finite index set, if `1 ≤ a i ≤ b i` and each weight increment is at most `δ`,
the normalized weight vectors differ in l1 norm by at most `2 * δ`. -/
theorem normalized_positive_weights_l1 {N : ℕ} (hN : 0 < N)
    (a b : Fin N → ℝ) (δ : ℝ) (ha : ∀ i, 1 ≤ a i)
    (hb : ∀ i, a i ≤ b i) (he : ∀ i, b i-a i ≤ δ) :
    (∑ i, |a i / ∑ j, a j - b i / ∑ j, b j|) ≤ 2*δ := by
  let A := ∑ i, a i
  let B := ∑ i, b i
  have ha0 (i : Fin N) : 0 < a i := lt_of_lt_of_le zero_lt_one (ha i)
  have hb0 (i : Fin N) : 0 < b i := (ha0 i).trans_le (hb i)
  have hA : 0 < A := Finset.sum_pos' (fun i _ => (ha0 i).le)
    ⟨⟨0,hN⟩, Finset.mem_univ _, ha0 _⟩
  have hB : 0 < B := Finset.sum_pos' (fun i _ => (hb0 i).le)
    ⟨⟨0,hN⟩, Finset.mem_univ _, hb0 _⟩
  have hAB : A ≤ B := Finset.sum_le_sum fun i _ => hb i
  have hδ : 0 ≤ δ := (sub_nonneg.mpr (hb ⟨0,hN⟩)).trans (he _)
  have hBn : (N:ℝ) ≤ B := by
    calc
      _ = ∑ i : Fin N, (1:ℝ) := by simp
      _ ≤ B := Finset.sum_le_sum fun i _ => (ha i).trans (hb i)
  have hBA : B-A ≤ (N:ℝ)*δ := by
    calc
      _ = ∑ i, (b i-a i) := by simp [A, B, Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin N, δ := Finset.sum_le_sum fun i _ => he i
      _ = _ := by simp [mul_comm]
  have hi (i : Fin N) : |a i/A-b i/B| ≤ a i*(B-A)/(A*B)+(b i-a i)/B := by
    have hid : a i/A-b i/B = a i*(B-A)/(A*B) + (-(b i-a i)/B) := by
      field_simp; ring
    rw [hid]
    calc
      _ ≤ |a i*(B-A)/(A*B)| + |-(b i-a i)/B| := abs_add_le _ _
      _ = _ := by
        rw [abs_of_nonneg (by exact div_nonneg (mul_nonneg (ha0 i).le (sub_nonneg.mpr hAB)) (mul_pos hA hB).le),
          abs_of_nonpos (by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (hb i))) hB.le)]
        ring
  calc
    _ ≤ ∑ i, (a i*(B-A)/(A*B)+(b i-a i)/B) := Finset.sum_le_sum fun i _ => hi i
    _ = 2*(B-A)/B := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
        ← Finset.sum_div, Finset.sum_sub_distrib]
      change A*(B-A)/(A*B)+(B-A)/B = _
      field_simp; ring
    _ ≤ 2*δ := by
      apply (div_le_iff₀ hB).2
      nlinarith [mul_le_mul_of_nonneg_right hBn hδ]

/-- Adding one to every Boltzmann exponent leaves the normalized rational-energy Gibbs density
unchanged. -/
theorem rationalEnergyGibbsDensity_shift {N : ℕ} (E : Fin N → ℚ) :
    rationalEnergyGibbsDensity E = Matrix.diagonal fun i =>
      Complex.ofReal (Real.exp (1-(E i:ℝ)) / ∑ j, Real.exp (1-(E j:ℝ))) := by
  unfold rationalEnergyGibbsDensity
  congr 1
  funext i
  simp only [sub_eq_add_neg, Real.exp_add, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero 1)]

/-- For a nonempty energy index set, the rational-energy Gibbs matrix is a density operator. -/
theorem rationalEnergyGibbsDensity_isDensity {N : ℕ} (E : Fin N → ℚ) (hN : 0 < N) :
    IsDensityOperator (rationalEnergyGibbsDensity E) := by
  have hs : 0 < ∑ j, Real.exp (-(E j:ℝ)) := Finset.sum_pos'
    (fun j _ => (Real.exp_pos _).le) ⟨⟨0,hN⟩, Finset.mem_univ _, Real.exp_pos _⟩
  constructor
  · rw [rationalEnergyGibbsDensity, Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast (div_nonneg (Real.exp_nonneg _) hs.le)
  · simp only [rationalEnergyGibbsDensity, Matrix.trace_diagonal, ← Complex.ofReal_sum,
      ← Finset.sum_div, div_self hs.ne', Complex.ofReal_one]

/-- For energies in `[0, 1]`, the heat-bath density from integer Boltzmann weights is the
diagonal of the normalized Taylor weights. -/
theorem rationalHeatBathDensity_taylor {N K : ℕ} (E : Fin N → ℚ)
    (hW : 0 < weightTotal (boltzmannIntegerWeights K E)) (hN : 0 < N)
    (hE : ∀ i, 0 ≤ E i ∧ E i ≤ 1) :
    rationalHeatBathDensity (boltzmannIntegerWeights K E) hW =
      Matrix.diagonal fun i => Complex.ofReal ((rationalBoltzmannTaylor K (E i):ℝ) /
        ∑ j, (rationalBoltzmannTaylor K (E j):ℝ)) := by
  unfold rationalHeatBathDensity
  congr 1
  funext i
  rw [(rational_boltzmann_exact_integer_normalization N K E hN hE).2 i]

/-- For energies in `[0, 1]`, normalized degree-`K` Taylor weights approximate normalized
exponential weights within `4 * (1 / 2) ^ K` in l1 norm. -/
theorem rationalEnergyGibbs_l1 {N : ℕ} (K : ℕ) (E : Fin N → ℚ) (hN : 0 < N)
    (hE : ∀ i, 0 ≤ E i ∧ E i ≤ 1) :
    (∑ i, |(rationalBoltzmannTaylor K (E i):ℝ) / ∑ j, (rationalBoltzmannTaylor K (E j):ℝ) -
      Real.exp (1-(E i:ℝ)) / ∑ j, Real.exp (1-(E j:ℝ))|) ≤ 4*(1/2:ℝ)^K := by
  have h := normalized_positive_weights_l1 hN
    (fun i => (rationalBoltzmannTaylor K (E i):ℝ)) (fun i => Real.exp (1-(E i:ℝ)))
    (2*(1/2:ℝ)^K) (fun i => by
      change (1:ℝ) ≤ (rationalBoltzmannTaylor K (E i):ℝ)
      exact_mod_cast (rational_boltzmann_computed_positive_tail K (E i) (hE i).1 (hE i).2).1)
    (fun i => sub_nonneg.mp (rational_boltzmann_computed_positive_tail K (E i) (hE i).1 (hE i).2).2.1)
    (fun i => (rational_boltzmann_computed_positive_tail K (E i) (hE i).1 (hE i).2).2.2)
  linarith

/-- For a nonempty system with energies in `[0, 1]`, the Gibbs target is a density operator and
its integer-weight heat-bath approximation has trace-norm error at most `4 * (1 / 2) ^ K`. -/
theorem rational_energy_gibbs_target_and_trace_accuracy :
    ∀ (N K : ℕ) (E : Fin N → ℚ) (hW : 0 < weightTotal (boltzmannIntegerWeights K E)),
      0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) → IsDensityOperator (rationalEnergyGibbsDensity E) ∧
      Matrix.traceNorm (rationalHeatBathDensity (boltzmannIntegerWeights K E) hW -
        rationalEnergyGibbsDensity E) ≤ 4*(1/2:ℝ)^K := by
  intro N K E hW hN hE
  refine ⟨rationalEnergyGibbsDensity_isDensity E hN, ?_⟩
  rw [rationalHeatBathDensity_taylor E hW hN hE, rationalEnergyGibbsDensity_shift,
    Matrix.diagonal_sub]
  simpa only [Pi.sub_apply, ← Complex.ofReal_sub, real_diagonal_traceNorm] using
    rationalEnergyGibbs_l1 K E hN hE

/-- For positive semidefinite system-reference inputs and energies in `[0, 1]`, the specified
Taylor precision and rejection cutoff give one heat-bath step error at most `(1 / 2) ^ k`
times the input trace norm. -/
theorem rational_energy_gibbs_actual_reference_precision :
    ∀ (N k r : ℕ) (E : Fin N → ℚ)
      (hW : 0 < weightTotal (boltzmannIntegerWeights (k+3) E))
      (X : Matrix (Fin N × Fin r) (Fin N × Fin r) ℂ),
      0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) → X.PosSemidef →
      Matrix.traceNorm (tensorLeft (rationalHeatBathPower (boltzmannIntegerWeights (k+3) E)
        hW (k+2) 1).map X - TensorGate (rationalEnergyGibbsDensity E) (Matrix.traceLeft X)) ≤
        (1/2:ℝ)^k * Matrix.traceNorm X := by
  intro N k r E hW X hN hE hX
  let w := boltzmannIntegerWeights (k+3) E
  let Y := Matrix.traceLeft X
  have hn : Matrix.traceNorm Y = Matrix.traceNorm X := by
    rw [rationalGibbs_psd_traceNorm Y hX.traceLeft, rationalGibbs_psd_traceNorm X hX,
      Matrix.traceLeft_trace]
  have hmix := (rational_heat_bath_derived_reference_mixing_budget N (k+2) 1 (k+1) r w hW X
    (by omega) hX).2 (by omega)
  have htarget : Matrix.traceNorm (TensorGate (rationalHeatBathDensity w hW - rationalEnergyGibbsDensity E) Y) ≤
      (4*(1/2:ℝ)^(k+3))*Matrix.traceNorm X := by
    rw [rationalHeatBathDensity_taylor E hW hN hE, rationalEnergyGibbsDensity_shift,
      Matrix.diagonal_sub]
    simp only [Pi.sub_apply, ← Complex.ofReal_sub]
    exact (real_diagonal_tensor_traceNorm_le _ Y hX.traceLeft).trans
      (by
        rw [hn]
        exact mul_le_mul_of_nonneg_right (rationalEnergyGibbs_l1 (k+3) E hN hE)
          (Matrix.traceNorm_nonneg X))
  have heq : tensorLeft (rationalHeatBathPower w hW (k+2) 1).map X -
      TensorGate (rationalEnergyGibbsDensity E) Y =
      (tensorLeft (rationalHeatBathPower w hW (k+2) 1).map X - TensorGate (rationalHeatBathDensity w hW) Y) +
      TensorGate (rationalHeatBathDensity w hW - rationalEnergyGibbsDensity E) Y := by
    rw [← tensorGate_sub_left]
    abel
  rw [heq]
  exact (Matrix.traceNorm_add_le _ _).trans ((add_le_add hmix htarget).trans_eq (by
    norm_num [pow_add, pow_succ]; ring))
end Qatlib.Concepts.GibbsMetropolis.RationalBath
