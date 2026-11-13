/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreeFermion24.MainResults.SourceModel
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# SourceGreenBlockEncoding

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

open Qatlib.Papers.FreeFermion24.MainResults.Model

namespace Qatlib.Papers.FreeFermion24.MainResults.Green

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding (BlockCorner)

private lemma resolvent_norm_le (δ r : ℝ) (hδ : 0 < δ) :
    ‖(Complex.I * (δ : ℂ) + (r : ℂ))⁻¹‖ ≤ δ⁻¹ := by
  rw [norm_inv]
  apply inv_anti₀ hδ
  simpa [Complex.mul_im, abs_of_pos hδ] using
    Complex.abs_im_le_norm (Complex.I * (δ : ℂ) + (r : ℂ))

private lemma greenScalar_norm_le (δ β ω y : ℝ) (hδ : 0 < δ) :
    ‖gDeltaBetaOmega 1 δ β ω y‖ ≤ 1 := by
  let f := 1 / (1 + Real.exp (β * y))
  have hf0 : 0 ≤ f := by dsimp [f]; positivity
  have hf1 : f ≤ 1 := by
    dsimp [f]
    exact (div_le_one (by positivity)).2 (by linarith [Real.exp_pos (β * y)])
  have hm := resolvent_norm_le δ (-(y + ω)) hδ
  have hp := resolvent_norm_le δ (y + ω) hδ
  simp only [Complex.ofReal_neg, ← sub_eq_add_neg] at hm
  have hscalar : gDeltaBetaOmega 1 δ β ω y = ((δ / 8 : ℝ) : ℂ) *
      (((1 - f : ℝ) : ℂ) * (Complex.I * (δ : ℂ) - ((y + ω : ℝ) : ℂ))⁻¹ +
        (f : ℂ) * (Complex.I * (δ : ℂ) + ((y + ω : ℝ) : ℂ))⁻¹) := by
    simp [gDeltaBetaOmega, f]
  rw [hscalar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (δ / 8) * (‖((1 - f : ℝ) : ℂ) *
          (Complex.I * (δ : ℂ) - ((y + ω : ℝ) : ℂ))⁻¹‖ +
        ‖(f : ℂ) * (Complex.I * (δ : ℂ) + ((y + ω : ℝ) : ℂ))⁻¹‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (δ / 8) * ((1 - f) * δ⁻¹ + f * δ⁻¹) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hf0, abs_of_nonneg (sub_nonneg.mpr hf1)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hf1))
          (mul_le_mul_of_nonneg_left hp hf0)) (by positivity)
    _ = 1 / 8 := by field_simp; ring
    _ ≤ 1 := by norm_num

private def scalarDilation {J : Type*} [DecidableEq J]
    (j₀ j₁ : J) (z : ℂ) : Matrix J J ℂ :=
  fun a b =>
    if a = j₀ then
      if b = j₀ then z else if b = j₁ then (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) else 0
    else if a = j₁ then
      if b = j₀ then (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) else if b = j₁ then -star z else 0
    else if a = b then 1 else 0

private lemma scalarDilation_unitary {J : Type*} [Fintype J] [DecidableEq J]
    (j₀ j₁ : J) (h01 : j₀ ≠ j₁) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    scalarDilation j₀ j₁ z ∈ Matrix.unitaryGroup J ℂ := by
  have hs : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hs2 : (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) *
      (Real.sqrt (1 - ‖z‖ ^ 2) : ℂ) = 1 - (‖z‖ : ℂ) ^ 2 := by
    exact_mod_cast Real.mul_self_sqrt hs
  have hsum (u v : ℂ) :
      (∑ x : J, if x = j₀ then u else if x = j₁ then v else 0) = u + v := by
    calc
      _ = ∑ x : J, ((if x = j₀ then u else 0) + (if x = j₁ then v else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h0 : x = j₀ <;> by_cases h1 : x = j₁ <;> simp_all
      _ = u + v := by simp [Finset.sum_add_distrib]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext a b
  by_cases ha0 : a = j₀ <;> by_cases ha1 : a = j₁ <;>
    by_cases hb0 : b = j₀ <;> by_cases hb1 : b = j₁ <;>
    simp_all [Matrix.mul_apply, Matrix.conjTranspose_apply, scalarDilation,
      Matrix.one_apply, mul_ite, Complex.conj_mul']
  all_goals try ring1
  all_goals try exact Ne.symm hb0
  all_goals try exact Ne.symm hb1
  · rw [mul_comm z, Complex.conj_mul']
    ring
  by_cases hab : a = b
  · subst b
    rw [Finset.sum_eq_single a]
    · simp_all
    · intro k hk hka
      simp_all
    · simp
  · simp [hab, Ne.symm hab]

private lemma corner_tensor_conjugate {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] (j₀ : J) (A B : Matrix I I ℂ)
    (D : Matrix (J × I) (J × I) ℂ) :
    BlockCorner (TensorGate 1 A * D * TensorGate 1 B) j₀ =
      A * BlockCorner D j₀ * B := by
  ext i j
  simp [BlockCorner, Matrix.mul_apply, Fintype.sum_prod_type, TensorGate,
    Matrix.one_apply, Finset.sum_mul, mul_assoc]

/-- The logarithmic factor `log^{5/2}(16 s^9 (β^4 + 1/δ^4)^2/(ε_PA^2 ε_p(h)^2))` of
Theorem 19 (arXiv:2409.04550, Eq. (F4)/(F5)); the `max … 1` makes it total. -/
def thm19LogFactor (s : ℕ) (β δ εPA εp : ℝ) : ℝ :=
  Real.rpow
    (Real.log (max (16 * (s : ℝ) ^ 9 * (β ^ 4 + 1 / δ ^ 4) ^ 2 / (εPA ^ 2 * εp ^ 2)) 1))
    (5 / 2 : ℝ)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem10_blockEncoding_greenG`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem10_blockEncoding_greenG_statement
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s) (δ β ω ε : ℝ) (na : ℕ)
    (hδpos : 0 < δ) (hβpos : 0 < β) (hε : 0 < ε)
    (hβ : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ β ≤ P.eval (n : ℝ))
    (hδ : ∃ P : Polynomial ℝ, IsNatNonnegPoly P ∧ 1 / δ ≤ P.eval (n : ℝ)) : Prop :=
    ∃ B : ControlledBlockEncoding (2 ^ n) (greenGQuarter h δ β ω) 1 ε,
      B.m = n + 5 ∧
      PolyOverEps B.cost.oracleCalls n ε ∧
      AncillaShape B.cost.ancillaryQubits n na ε ∧
      GateShape B.cost.gates n ε ∧
      ClassicalShape B.cost.classicalTime n ε

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem19_greenG_resources`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem19_greenG_resources_statement
    (n : ℕ) (s : ℕ) (h : SparseHermitian (2 ^ n) s) (δ β ω εPA εp δc : ℝ) (na : ℕ)
    (hδ : 0 < δ) (hβ : 0 < β) (hεPA : 0 < εPA) (hεp : 0 ≤ εp) (hδc : 0 < δc) : Prop :=
    ∃ B : ControlledBlockEncoding (2 ^ n) (greenGQuarter h δ β ω) 1 (εPA + εp + δc),
      B.m = n + 5 ∧
      ThetaBound B.cost.oracleCalls
        ((if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
              (β * (s : ℝ)) ^ 4 / εPA
            else
              (β * (s : ℝ)) ^ 2 / εPA) +
          (if 1 ≤ 2 * (s : ℝ) / δ then
              (s : ℝ) ^ 4 / (δ ^ 4 * εPA)
            else
              (s : ℝ) ^ 2 / (δ ^ 2 * εPA)))
        ((if 1 ≤ β * (s : ℝ) / (2 * Real.pi) then
              (β * (s : ℝ)) ^ 4 / εPA
            else
              (β * (s : ℝ)) ^ 2 / εPA) +
          (if 1 ≤ 2 * (s : ℝ) / δ then
              (s : ℝ) ^ 4 / (δ ^ 4 * εPA)
            else
              (s : ℝ) ^ 2 / (δ ^ 2 * εPA))) ∧
      BigO B.cost.ancillaryQubits
        ((s : ℝ) * (n : ℝ) + (na : ℝ) + thm19LogFactor s β δ εPA εp) ∧
      BigO B.cost.gates
        ((n : ℝ) + ((n : ℝ) + 4) * (β ^ 4 * (s : ℝ) ^ 4 + (s : ℝ) ^ 4 / δ ^ 4) / εPA +
          thm19LogFactor s β δ εPA εp) ∧
      PolyTwo B.cost.classicalTime
        ((β ^ 4 * (s : ℝ) ^ 4 + (s : ℝ) ^ 4 / δ ^ 4) / εPA) (Real.log (1 / δc))

end Qatlib.Papers.FreeFermion24.MainResults.Green
