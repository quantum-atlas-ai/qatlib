/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.Measurement
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

def jointBorn {A B : Type*} [Fintype A] [Fintype B]
    (ψ : QState (A × B)) (a : A) (b : B) : ℝ :=
  BornProb ψ (a, b)

def marginalLeft {A B : Type*} [Fintype A] [Fintype B]
    (ψ : QState (A × B)) (a : A) : ℝ :=
  ∑ b, jointBorn ψ a b

theorem marginalLeft_sum {A B : Type*} [Fintype A] [Fintype B]
    {ψ : QState (A × B)} (hψ : Normalized ψ) :
    ∑ a, marginalLeft ψ a = 1 := by
  unfold marginalLeft jointBorn BornProb
  rw [← Fintype.sum_prod_type (fun z : A × B => ‖ψ z‖ ^ 2)]
  exact hψ

def bellAmp : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def bell : QState (Bool × Bool) := fun x => if x.1 = x.2 then bellAmp else 0

theorem bell_normalized : Normalized bell := by
  have hs : ‖bellAmp‖ ^ 2 = (1 / 2 : ℝ) := by
    unfold bellAmp
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold Normalized
  simp [bell, hs, Fintype.sum_prod_type]
  norm_num

theorem bell_correlated :
    jointBorn bell false false = (1 / 2 : ℝ) ∧
      marginalLeft bell false = (1 / 2 : ℝ) ∧
      jointBorn bell false false ≠
        marginalLeft bell false * marginalLeft bell false := by
  have hs : ‖bellAmp‖ ^ 2 = (1 / 2 : ℝ) := by
    unfold bellAmp
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hjoint : jointBorn bell false false = (1 / 2 : ℝ) := by
    unfold jointBorn BornProb bell
    simp [hs]
  have hmarg : marginalLeft bell false = (1 / 2 : ℝ) := by
    unfold marginalLeft jointBorn BornProb bell
    simp [Fintype.sum_bool, hs]
  refine ⟨hjoint, hmarg, ?_⟩
  rw [hjoint, hmarg]
  norm_num

def plusState : QState Bool := fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def minusState : QState Bool := fun b =>
  if b then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else -(((Real.sqrt 2 : ℝ) : ℂ)⁻¹)

theorem minusState_normalized : Normalized minusState := by
  have hs : ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold Normalized
  simp [minusState, hs]
  norm_num

theorem born_indistinguishable (b : Bool) :
    BornProb plusState b = BornProb minusState b := by
  have hs : ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  cases b <;> simp [BornProb, plusState, minusState, hs]

def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def productWeight {N : ℕ} (p : ℝ) (b : Fin N → Bool) : ℝ :=
  ∏ i, bitWeight p (b i)

theorem productWeight_sum {N : ℕ} (p : ℝ) :
    ∑ b : Fin N → Bool, productWeight p b = (p + (1 - p)) ^ N := by
  have hsum : p + (1 - p) = ∑ a : Bool, bitWeight p a := by
    rw [Fintype.sum_bool]
    simp [bitWeight]
  rw [hsum, Fintype.sum_pow]
  unfold productWeight
  rfl

theorem productWeight_sum_one {N : ℕ} (p : ℝ) :
    ∑ b : Fin N → Bool, productWeight p b = 1 := by
  rw [productWeight_sum]
  ring

theorem chebyshev_finite {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (h₀ : ∀ i, 0 ≤ w i) (μ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Finset.univ.filter (fun i => ε ≤ |X i - μ|)).sum w ≤
      (∑ i, w i * (X i - μ) ^ 2) / ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have htail :
      (Finset.univ.filter (fun i => ε ≤ |X i - μ|)).sum w ≤
        (Finset.univ.filter (fun i => ε ≤ |X i - μ|)).sum
          (fun i => w i * (X i - μ) ^ 2 / ε ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    have hle : ε ≤ |X i - μ| := (Finset.mem_filter.mp hi).2
    have hsq : ε ^ 2 ≤ (X i - μ) ^ 2 := by
      have h1 : ε ^ 2 ≤ |X i - μ| ^ 2 := by
        rw [sq, sq]
        exact mul_le_mul hle hle hε.le (abs_nonneg _)
      rwa [sq_abs] at h1
    have hmul : w i * ε ^ 2 ≤ w i * (X i - μ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (h₀ i)
    rw [le_div_iff₀ hε2]
    exact hmul
  have hmono :
      (Finset.univ.filter (fun i => ε ≤ |X i - μ|)).sum
          (fun i => w i * (X i - μ) ^ 2 / ε ^ 2) ≤
        ∑ i, w i * (X i - μ) ^ 2 / ε ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact div_nonneg (mul_nonneg (h₀ i) (sq_nonneg _)) hε2.le
  calc (Finset.univ.filter (fun i => ε ≤ |X i - μ|)).sum w
      ≤ (Finset.univ.filter (fun i => ε ≤ |X i - μ|)).sum
          (fun i => w i * (X i - μ) ^ 2 / ε ^ 2) := htail
    _ ≤ ∑ i, w i * (X i - μ) ^ 2 / ε ^ 2 := hmono
    _ = (∑ i, w i * (X i - μ) ^ 2) / ε ^ 2 := by rw [Finset.sum_div]

theorem samples_from_inverse_square {N ε : ℝ} (hN : 0 < N) (hε : 0 < ε)
    (h : 1 / (4 * ε ^ 2) ≤ N) : 1 / (4 * N) ≤ ε ^ 2 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * N)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ε ^ 2)] at h
  nlinarith

theorem momentum_basis_change (N : ℕ) [NeZero N] :
    Function.Bijective (fun φ : ZMod N → ℂ => ZMod.dft (E := ℂ) φ) :=
  (ZMod.dft (E := ℂ) : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ)).bijective

end Qatlib.Papers.ManyBodyFermi97.MainResults.Measurement
