/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceExponential
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.QuantumSVM13.TraceReadout

open Matrix
open Qatlib.Foundations.PureStateMath

variable {M : ℕ}

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i = j then 0 else 1

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

noncomputable def traceHamiltonian (x : Fin M → ℝ) :
    Matrix (Fin 2 × Fin M) (Fin 2 × Fin M) ℂ :=
  Matrix.blockDiagonal (fun j => ((|x j| : ℝ) : ℂ) • pauliX)

noncomputable def uniformTraceState (_hM : 0 < M) : QState (Fin 2 × Fin M) :=
  fun p => if p.1 = 0 then (1 / (Real.sqrt (M : ℝ) : ℂ)) else 0

noncomputable def traceEvolvedState (x : Fin M → ℝ) (t : ℝ) : QState (Fin 2 × Fin M) :=
  fun p =>
    if p.1 = 0 then
      (Real.cos (|x p.2| * t) : ℂ) * (1 / (Real.sqrt (M : ℝ) : ℂ))
    else
      -(Complex.I * (Real.sin (|x p.2| * t) : ℂ)) * (1 / (Real.sqrt (M : ℝ) : ℂ))

theorem blockDiagonal_mulVec_apply (v : Fin M → Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : Fin 2 × Fin M → ℂ) (i : Fin 2) (k : Fin M) :
    (Matrix.blockDiagonal v *ᵥ ψ) (i, k) = ∑ i', v k i i' * ψ (i', k) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.sum_eq_single k]
  · rw [Matrix.blockDiagonal_apply_eq]
  · intro k' _ hk'
    rw [Matrix.blockDiagonal_apply_ne v i i' (Ne.symm hk'), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem exp_smul_pauliX (c : ℝ) :
    NormedSpace.exp ((-Complex.I * (c : ℂ)) • pauliX)
      = (Real.cos c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        - (Complex.I * (Real.sin c : ℂ)) • pauliX := by
  have hc : (-Complex.I * (c : ℂ)) = (-(c : ℂ)) * Complex.I := by ring
  rw [hc, Qatlib.Papers.ThermalDrift26.ThermalSampling.reflection_exp pauliX pauliX_mul_self]
  rw [show Complex.cosh (-(c : ℂ) * Complex.I) = (Real.cos c : ℂ) by
    rw [Complex.cosh_mul_I, Complex.cos_neg, Complex.ofReal_cos]]
  rw [show Complex.sinh (-(c : ℂ) * Complex.I) = -(Complex.I * (Real.sin c : ℂ)) by
    rw [Complex.sinh_mul_I, Complex.sin_neg, Complex.ofReal_sin]
    ring]
  rw [neg_smul]
  abel

theorem traceEvolution_matrix (x : Fin M → ℝ) (t : ℝ) :
  HamiltonianEvolution (traceHamiltonian x) t
    = Matrix.blockDiagonal (fun j =>
        (Real.cos (|x j| * t) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          - (Complex.I * (Real.sin (|x j| * t) : ℂ)) • pauliX) := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  unfold HamiltonianEvolution traceHamiltonian
  rw [← Matrix.blockDiagonal_smul,Matrix.exp_blockDiagonal]
  congr 1
  funext j
  rw [Pi.coe_exp]
  simp only [Pi.smul_apply,smul_smul]
  rw [show (-Complex.I*(t:ℂ))*((|x j|:ℝ):ℂ) = -Complex.I*((|x j| * t:ℝ):ℂ) by push_cast;ring]
  exact exp_smul_pauliX _

theorem traceEvolvedState_eq (x : Fin M → ℝ) (t : ℝ) (hM : 0 < M) :
  ApplyGate (HamiltonianEvolution (traceHamiltonian x) t) (uniformTraceState hM)
    = traceEvolvedState (M := M) x t := by
  rw [traceEvolution_matrix]
  funext p
  rcases p with ⟨i,j⟩
  rw [ApplyGate,blockDiagonal_mulVec_apply]
  fin_cases i <;> simp [traceEvolvedState,uniformTraceState,pauliX,Matrix.one_apply]

theorem traceSuccessProb_eq (x : Fin M → ℝ) (t : ℝ) (hM : 0 < M) :
    (∑ p ∈ Finset.univ.filter (fun p : Fin 2 × Fin M => p.1 = 1),
        BornProb (traceEvolvedState (M := M) x t) p)
      = (1 / (M : ℝ)) * ∑ j, (Real.sin (|x j| * t)) ^ 2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hterm (j : Fin M) :
      BornProb (traceEvolvedState (M := M) x t) ((1 : Fin 2), j)
        = (1 / (M : ℝ)) * (Real.sin (|x j| * t)) ^ 2 := by
    unfold BornProb traceEvolvedState
    rw [if_neg (by decide : ¬ (1 : Fin 2) = 0)]
    have hc : ‖((1 / (Real.sqrt (M : ℝ) : ℂ)))‖ ^ 2 = 1 / (M : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt (M : ℝ))]
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
    have hs : ‖-(Complex.I * (Real.sin (|x j| * t) : ℂ))‖
        = |Real.sin (|x j| * t)| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, mul_pow, hs, hc, sq_abs]
    ring
  have hsingle : (∑ a : Fin 2, ∑ j : Fin M,
        (if a = 1 then BornProb (traceEvolvedState (M := M) x t) (a, j) else 0))
      = ∑ j : Fin M, BornProb (traceEvolvedState (M := M) x t) ((1 : Fin 2), j) := by
    rw [Finset.sum_eq_single (1 : Fin 2)]
    · apply Finset.sum_congr rfl
      intro j _
      rw [if_pos rfl]
    · intro a _ ha
      simp [ha]
    · intro h1
      exact absurd (Finset.mem_univ (1 : Fin 2)) h1
  rw [hsingle]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.mul_sum]

theorem sin_sq_sub_sq_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    |Real.sin u ^ 2 - u ^ 2| ≤ u ^ 4 := by
  rcases h0.eq_or_lt with rfl | hu0
  · simp
  · have hgt : u - u ^ 3 / 4 < Real.sin u := by
      linarith [Real.sin_gt_sub_cube hu0, pow_nonneg hu0.le 3]
    have hsin_le : Real.sin u ≤ u := Real.sin_le hu0.le
    have hsin_nonneg : 0 ≤ Real.sin u := by nlinarith [sq_nonneg u, h0, h1]
    have hdiff_le : u - Real.sin u ≤ u ^ 3 / 4 := by linarith
    have hdiff_nonneg : 0 ≤ u - Real.sin u := by linarith
    have hsum_le : u + Real.sin u ≤ 2 * u := by linarith
    have hsum_nonneg : 0 ≤ u + Real.sin u := by linarith
    have hmain : u ^ 2 - Real.sin u ^ 2 ≤ u ^ 4 := by
      calc u ^ 2 - Real.sin u ^ 2 = (u - Real.sin u) * (u + Real.sin u) := by ring
        _ ≤ (u ^ 3 / 4) * (2 * u) :=
            mul_le_mul hdiff_le hsum_le hsum_nonneg (by positivity)
        _ = u ^ 4 / 2 := by ring
        _ ≤ u ^ 4 := by nlinarith [sq_nonneg (u ^ 2)]
    have hnonpos : Real.sin u ^ 2 - u ^ 2 ≤ 0 := by nlinarith
    rw [abs_of_nonpos hnonpos, neg_sub]
    exact hmain

theorem traceSuccessProb_error (x : Fin M → ℝ) (t : ℝ) (hM : 0 < M)
    (hx : ∀ j, |x j| * t ≤ 1) (ht : 0 ≤ t) :
    |(∑ p ∈ Finset.univ.filter (fun p : Fin 2 × Fin M => p.1 = 1),
        BornProb (traceEvolvedState (M := M) x t) p)
      - t ^ 2 / (M : ℝ) * ∑ j, (x j) ^ 2|
      ≤ t ^ 4 / (M : ℝ) * ∑ j, (x j) ^ 4 := by
  rw [traceSuccessProb_eq x t hM]
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hterm (j : Fin M) :
      |(Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2| ≤ (|x j| * t) ^ 4 := by
    apply sin_sq_sub_sq_le
    · exact mul_nonneg (abs_nonneg _) ht
    · exact hx j
  have habs : |(1 / (M : ℝ)) * ∑ j, (Real.sin (|x j| * t)) ^ 2
      - t ^ 2 / (M : ℝ) * ∑ j, (x j) ^ 2|
      = (1 / (M : ℝ)) * |∑ j, ((Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2)| := by
    have h1 : (1 / (M : ℝ)) * ∑ j, (Real.sin (|x j| * t)) ^ 2
        - t ^ 2 / (M : ℝ) * ∑ j, (x j) ^ 2
        = (1 / (M : ℝ)) * ∑ j, ((Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2) := by
      have hsum : (∑ j, ((Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2))
          = (∑ j, (Real.sin (|x j| * t)) ^ 2) - ∑ j, (|x j| * t) ^ 2 :=
        Finset.sum_sub_distrib (s := Finset.univ)
          (f := fun j => (Real.sin (|x j| * t)) ^ 2)
          (g := fun j => (|x j| * t) ^ 2)
      have hsquares : (∑ j, (|x j| * t) ^ 2) = t ^ 2 * ∑ j, (x j) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow, sq_abs]
        ring
      rw [hsum, hsquares]
      ring
    rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (M : ℝ))]
  rw [habs]
  have hbound : |∑ j, ((Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2)|
      ≤ ∑ j, (|x j| * t) ^ 4 := by
    calc |∑ j, ((Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2)|
        ≤ ∑ j, |(Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (|x j| * t) ^ 4 := Finset.sum_le_sum fun j _ => hterm j
  have hright : (∑ j, (|x j| * t) ^ 4) = t ^ 4 * ∑ j, (x j) ^ 4 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hx4 : |x j| ^ 4 = (x j) ^ 4 := by
      rw [show |x j| ^ 4 = (|x j| ^ 2) ^ 2 by ring, sq_abs]
      ring
    rw [mul_pow, hx4]
    ring
  calc (1 / (M : ℝ)) * |∑ j, ((Real.sin (|x j| * t)) ^ 2 - (|x j| * t) ^ 2)|
      ≤ (1 / (M : ℝ)) * ∑ j, (|x j| * t) ^ 4 :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = t ^ 4 / (M : ℝ) * ∑ j, (x j) ^ 4 := by
        rw [hright]
        ring

theorem pauliX_hermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX,Matrix.conjTranspose_apply]

theorem traceHamiltonian_hermitian (x : Fin M → ℝ) : (traceHamiltonian x).IsHermitian := by
  apply Matrix.isHermitian_blockDiagonal_iff.mpr
  intro j
  exact pauliX_hermitian.smul (by simp [IsSelfAdjoint])

theorem traceHamiltonian_unitary (x : Fin M → ℝ) (t : ℝ) :
    HamiltonianEvolution (traceHamiltonian x) t ∈ Matrix.unitaryGroup (Fin 2×Fin M) ℂ :=
  hamiltonianEvolution_unitary (traceHamiltonian_hermitian x) t

theorem uniformTraceState_normalized (hM : 0<M) : Normalized (uniformTraceState hM) := by
  have hM0 : (0:ℝ)<M := by exact_mod_cast hM
  unfold Normalized uniformTraceState
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  simp
  exact div_self hM0.ne'

theorem traceEvolvedState_normalized (x : Fin M → ℝ) (t : ℝ) (hM : 0<M) :
    Normalized (traceEvolvedState x t) := by
  rw [← traceEvolvedState_eq x t hM]
  exact normalized_applyGate (traceHamiltonian_unitary x t) (uniformTraceState_normalized hM)

end Qatlib.Papers.QuantumSVM13.TraceReadout
