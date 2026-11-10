/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Matrix
open Qatlib

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def GroverStep (I : Type*) [Fintype I] [DecidableEq I] : Circuit I :=
  [Step.query, Step.gate (Diffusion I)]

noncomputable def GroverCircuit (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) : Circuit I :=
  RepeatCircuit (GroverStep I) j

noncomputable def GroverState (A : Finset I) (j : ℕ) : QState I :=
  Run (SetOracle A) (GroverCircuit I j) (Uniform I)

theorem isUnitaryCircuit_groverStep (hN : 0 < Fintype.card I) :
    IsUnitaryCircuit (GroverStep I) := by
  simp [GroverStep, diffusion_unitary hN]

theorem isUnitaryCircuit_groverCircuit (hN : 0 < Fintype.card I) (j : ℕ) :
    IsUnitaryCircuit (GroverCircuit I j) :=
  (isUnitaryCircuit_groverStep hN).repeatCircuit j

theorem normalized_groverState (hN : 0 < Fintype.card I) (A : Finset I) (j : ℕ) :
    Normalized (GroverState A j) :=
  (isUnitaryCircuit_groverCircuit hN j).normalized_run
    (setOracle_unitary A) (normalized_uniform hN)

theorem queryCount_groverStep : QueryCount (GroverStep I) = 1 := rfl

theorem queryCount_groverCircuit (j : ℕ) : QueryCount (GroverCircuit I j) = j := by
  rw [GroverCircuit, queryCount_repeatCircuit, queryCount_groverStep, mul_one]

theorem applyGate_setOracle_markedVector (A : Finset I) (a b : ℂ) :
    ApplyGate (SetOracle A) (MarkedVector A a b) = MarkedVector A (-a) b := by
  funext i
  rw [SetOracle, applyGate_phaseOracle]
  by_cases hi : i ∈ A <;> simp [MarkedVector, hi]

theorem run_groverStep_markedVector (hN : 0 < Fintype.card I) (A : Finset I) (a b : ℂ) :
    Run (SetOracle A) (GroverStep I) (MarkedVector A a b) =
      MarkedVector A
        ((1 - 2 * (A.card : ℂ) / (Fintype.card I : ℂ)) * a +
          2 * (1 - (A.card : ℂ) / (Fintype.card I : ℂ)) * b)
        ((1 - 2 * (A.card : ℂ) / (Fintype.card I : ℂ)) * b -
          2 * (A.card : ℂ) / (Fintype.card I : ℂ) * a) := by
  simp only [GroverStep, run_query, run_gate, run_nil]
  rw [applyGate_setOracle_markedVector]
  funext i
  rw [applyGate_diffusion, sum_markedVector]
  simp only [MarkedVector]
  have hn : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  split_ifs <;> field_simp <;> ring

theorem rotation_scalar (θ x u : ℝ) (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    (1 - 2 * (Real.sin θ) ^ 2) * (u * Real.sin x / Real.sin θ) +
        2 * (1 - (Real.sin θ) ^ 2) * (u * Real.cos x / Real.cos θ) =
      u * Real.sin (x + 2 * θ) / Real.sin θ ∧
    (1 - 2 * (Real.sin θ) ^ 2) * (u * Real.cos x / Real.cos θ) -
        2 * (Real.sin θ) ^ 2 * (u * Real.sin x / Real.sin θ) =
      u * Real.cos (x + 2 * θ) / Real.cos θ := by
  have hcos : Real.cos (2 * θ) = 1 - 2 * (Real.sin θ) ^ 2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Real.sin_add, Real.cos_add, hcos, Real.sin_two_mul]
  constructor
  · rw [hsq]
    field_simp
  · field_simp

theorem run_groverCircuit_markedVector (hN : 0 < Fintype.card I) (A : Finset I) (θ u : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) (x : ℝ) :
    Run (SetOracle A) (GroverCircuit I j)
        (MarkedVector A (u * Real.sin x / Real.sin θ : ℂ) (u * Real.cos x / Real.cos θ : ℂ)) =
      MarkedVector A (u * Real.sin (x + 2 * j * θ) / Real.sin θ : ℂ)
        (u * Real.cos (x + 2 * j * θ) / Real.cos θ : ℂ) := by
  have hstep (x : ℝ) :
      Run (SetOracle A) (GroverStep I)
          (MarkedVector A (u * Real.sin x / Real.sin θ : ℂ) (u * Real.cos x / Real.cos θ : ℂ)) =
        MarkedVector A (u * Real.sin (x + 2 * θ) / Real.sin θ : ℂ)
          (u * Real.cos (x + 2 * θ) / Real.cos θ : ℂ) := by
    rw [run_groverStep_markedVector hN]
    have hrot := rotation_scalar θ x u hs hc
    rw [hθ] at hrot
    apply congrArg₂ (MarkedVector A)
    · have h := congrArg (fun y : ℝ => (y : ℂ)) hrot.1
      simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
        Complex.ofReal_div, Complex.ofReal_natCast] at h
      simpa only [mul_div_assoc] using! h
    · have h := congrArg (fun y : ℝ => (y : ℂ)) hrot.2
      simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
        Complex.ofReal_natCast] at h
      simpa only [mul_div_assoc] using! h
  induction j generalizing x with
  | zero => simp [GroverCircuit, RepeatCircuit]
  | succ j ih =>
    rw [GroverCircuit, RepeatCircuit, run_append, hstep]
    simp only [GroverCircuit] at ih
    rw [ih]
    have ha : (x + 2 * θ) + 2 * (j : ℝ) * θ = x + 2 * (j + 1 : ℕ) * θ := by
      push_cast
      ring
    rw [ha]

theorem groverState_eq (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) :
    GroverState A j =
      MarkedVector A
        ((Real.sqrt (Fintype.card I))⁻¹ * Real.sin ((2 * j + 1) * θ) / Real.sin θ : ℂ)
        ((Real.sqrt (Fintype.card I))⁻¹ * Real.cos ((2 * j + 1) * θ) / Real.cos θ : ℂ) := by
  let u : ℝ := (Real.sqrt (Fintype.card I))⁻¹
  have hi : Uniform I = MarkedVector A (u * Real.sin θ / Real.sin θ : ℂ)
      (u * Real.cos θ / Real.cos θ : ℂ) := by
    have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
    have hcC : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc
    funext i
    simp only [MarkedVector, Uniform]
    split_ifs
    · simp only [mul_div_assoc, div_self hsC, mul_one, u, Complex.ofReal_inv]
    · simp only [mul_div_assoc, div_self hcC, mul_one, u, Complex.ofReal_inv]
  unfold GroverState
  rw [hi, run_groverCircuit_markedVector hN A θ u hθ hs hc]
  have ha : θ + 2 * (j : ℝ) * θ = (2 * j + 1) * θ := by ring
  rw [ha]

theorem measureProb_groverState (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) :
    MeasureProb (GroverState A j) A = (Real.sin ((2 * j + 1) * θ)) ^ 2 := by
  have hNreal : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have heach (i : I) (hi : i ∈ A) : BornProb (GroverState A j) i =
      (Fintype.card I : ℝ)⁻¹ * (Real.sin ((2 * j + 1) * θ)) ^ 2 / (Real.sin θ) ^ 2 := by
    rw [groverState_eq hN A θ hθ hs hc]
    simp only [BornProb, MarkedVector, if_pos hi, norm_div, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, div_pow, mul_pow, inv_pow, sq_abs,
      Real.sq_sqrt hNreal]
  have hsum : MeasureProb (GroverState A j) A =
      (A.card : ℝ) *
        ((Fintype.card I : ℝ)⁻¹ * (Real.sin ((2 * j + 1) * θ)) ^ 2 / (Real.sin θ) ^ 2) := by
    unfold MeasureProb
    calc
      _ = ∑ _i ∈ A,
          ((Fintype.card I : ℝ)⁻¹ * (Real.sin ((2 * j + 1) * θ)) ^ 2 / (Real.sin θ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact heach i hi
      _ = _ := by simp
  rw [hsum]
  have hscale : (A.card : ℝ) * (Fintype.card I : ℝ)⁻¹ = (Real.sin θ) ^ 2 := by
    simpa only [div_eq_mul_inv] using hθ.symm
  calc
    _ = ((A.card : ℝ) * (Fintype.card I : ℝ)⁻¹) / (Real.sin θ) ^ 2 *
        (Real.sin ((2 * j + 1) * θ)) ^ 2 := by ring
    _ = _ := by rw [hscale, div_self (pow_ne_zero 2 hs), one_mul]

theorem grover_exists_circuit (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) :
    ∃ C : Circuit I, QueryCount C = j ∧
      MeasureProb (Run (SetOracle A) C (Uniform I)) A = (Real.sin ((2 * j + 1) * θ)) ^ 2 :=
  ⟨GroverCircuit I j, queryCount_groverCircuit j, measureProb_groverState hN A θ hθ hs hc j⟩

end Qatlib.Concepts.SearchStopping.KnownCount
