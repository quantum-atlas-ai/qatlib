/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorSimulationDefs

/-!
# Coefficient normalization for Taylor simulation

This module proves coefficient-mass and preparation identities for a finite time-grid Taylor
construction. The linear-combination method is described in [ChildsWiebe2012], and
time-dependent Hamiltonian simulation is treated in [BerryEtAl2020Dyson].

Under the stated short-time scaling condition, two cancelling padding coefficients bring the
total coefficient mass to two. The resulting `cubeAmplitude` values are normalized, and the
phase and preparation matrices are unitary.

## Main statements

* `cube_total_mass_eq_two`: computes the padded coefficient mass.
* `cube_amplitude_sq_sum`: proves normalization of the preparation amplitudes.
* `cubePrepare_unitary`: proves unitarity of the preparation matrix.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
* [Berry et al., 2020][BerryEtAl2020Dyson]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.CoherentSim.TaylorEncoding

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib
open Matrix
open Classical
open scoped BigOperators

/-- Summing products over all length-`n` choices from a finite type equals the `n`th power of
the sum of the individual weights. -/
private lemma sum_prod_fun {κ : Type} [Fintype κ] (n : ℕ) (f : κ → ℝ) :
    ∑ p : Fin n → κ, ∏ i, f (p i) = (∑ a, f a) ^ n := by
  have h := Finset.sum_pow' (Finset.univ : Finset κ) f n
  rw [Fintype.piFinset_univ] at h
  simpa using! h.symm

/-- Summing products of absolute coefficient values over time-grid words equals the
corresponding grid-weight sum raised to the word length. -/
private lemma sum_prod_grid {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (n : ℕ) :
    ∑ u : Fin n → (Fin M × J), ∏ a, |h (gridTime τ M (u a).1) (u a).2|
      = (∑ p : Fin M × J, |h (gridTime τ M p.1) p.2|) ^ n := by
  have h := Finset.sum_pow' (Finset.univ : Finset (Fin M × J))
    (fun p => |h (gridTime τ M p.1) p.2|) n
  rw [Fintype.piFinset_univ] at h
  simpa using! h.symm

/-- The product `(a^l / c^l) * b^l` equals `(a * (b / c))^l`. -/
private lemma pow_div_mul (a b c : ℝ) (l : ℕ) :
    (a ^ l / c ^ l) * b ^ l = (a * (b / c)) ^ l := by
  calc a ^ l / c ^ l * b ^ l = (a ^ l * b ^ l) / c ^ l := by ring
    _ = ((a * b) ^ l) / c ^ l := by rw [mul_pow]
    _ = (a * b / c) ^ l := by rw [← div_pow]
    _ = (a * (b / c)) ^ l := by rw [show a * b / c = a * (b / c) from by ring]

/-- A Taylor word coefficient has norm equal to its time-power and factorial factor times the
product of sampled absolute coefficients, divided by the grid-size power. -/
theorem cubeCoeff_norm_inl {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ)
    (w : Σ l : Fin (K + 1), Fin l.val → (Fin M × J)) :
    ‖cubeCoeff h τ M K (Sum.inl w)‖ =
      (|τ| ^ (w.1.val : ℕ) / w.1.val.factorial) *
        (∏ a, |h (gridTime τ M (w.2 a).1) (w.2 a).2|) / (M : ℝ) ^ (w.1.val : ℕ) := by
  have h1 : ‖(-Complex.I * (τ : ℂ)) ^ (w.1.val : ℕ)‖ = |τ| ^ (w.1.val : ℕ) := by
    rw [norm_pow, show -Complex.I * (τ : ℂ) = -(Complex.I * (τ : ℂ)) from by ring, norm_neg,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((w.1.val.factorial : ℕ) : ℂ)‖ = (w.1.val.factorial : ℝ) := by
    rw [Complex.norm_natCast]
  have h3 : ‖∏ a, (h (gridTime τ M (w.2 a).1) (w.2 a).2 : ℂ) / (M : ℂ)‖
      = (∏ a, |h (gridTime τ M (w.2 a).1) (w.2 a).2|) / (M : ℝ) ^ (w.1.val : ℕ) := by
    rw [Complex.norm_prod]
    have hval : ∀ a : Fin w.1.val,
        ‖(h (gridTime τ M (w.2 a).1) (w.2 a).2 : ℂ) / (M : ℂ)‖
          = |h (gridTime τ M (w.2 a).1) (w.2 a).2| / (M : ℝ) := by
      intro a
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    rw [Finset.prod_congr rfl fun a _ => hval a, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [cubeCoeff, norm_mul, norm_div, h1, h2, h3]
  ring

/-- The sum of absolute coefficient values over all time-grid and term-index pairs equals
`cubeLambda`. -/
private lemma cubeLambda_eq_prod {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) :
    (∑ p : Fin M × J, |h (gridTime τ M p.1) p.2|) = cubeLambda h τ M := by
  rw [Fintype.sum_prod_type]
  unfold cubeLambda
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => rfl

/-- For a positive grid size, summing coefficient norms over words of a fixed order gives
`cubeOrderMass`. -/
theorem cubeOrderMass_eq {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ)
    (hM : 0 < M) (l : Fin (K + 1)) :
    ∑ u : Fin l.val → (Fin M × J), ‖cubeCoeff h τ M K (Sum.inl ⟨l, u⟩)‖
      = cubeOrderMass h τ M l.val := by
  calc ∑ u : Fin l.val → (Fin M × J), ‖cubeCoeff h τ M K (Sum.inl ⟨l, u⟩)‖
      = ∑ u : Fin l.val → (Fin M × J),
          ((|τ| ^ (l.val : ℕ) / l.val.factorial) / (M : ℝ) ^ (l.val : ℕ)) *
            (∏ a, |h (gridTime τ M (u a).1) (u a).2|) := by
        exact Finset.sum_congr rfl fun u _ => by
          rw [cubeCoeff_norm_inl]; ring
    _ = ((|τ| ^ (l.val : ℕ) / l.val.factorial) / (M : ℝ) ^ (l.val : ℕ)) *
          (∑ p : Fin M × J, |h (gridTime τ M p.1) p.2|) ^ (l.val : ℕ) := by
        rw [← Finset.mul_sum, sum_prod_grid]
    _ = cubeOrderMass h τ M l.val := by
        rw [cubeLambda_eq_prod, cubeOrderMass]
        unfold cubeScale
        have hfact : (0 : ℝ) < l.val.factorial := by positivity
        have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
        have hMp : (0 : ℝ) < (M : ℝ) ^ (l.val : ℕ) := by positivity
        calc
          ((|τ| ^ (l.val : ℕ) / l.val.factorial) / (M : ℝ) ^ (l.val : ℕ)) *
                (cubeLambda h τ M) ^ (l.val : ℕ)
              = ((|τ| ^ (l.val : ℕ) / (M : ℝ) ^ (l.val : ℕ)) * (cubeLambda h τ M) ^ (l.val : ℕ)) /
                  l.val.factorial := by ring
          _ = ((|τ| * (cubeLambda h τ M / (M : ℝ))) ^ (l.val : ℕ)) / l.val.factorial := by
              rw [pow_div_mul]
          _ = (|τ| * cubeScale h τ M) ^ (l.val : ℕ) / l.val.factorial := by
              unfold cubeScale; rfl

/-- For a positive grid size, the total unpadded Taylor coefficient mass equals `cubeS0`. -/
theorem cubeS0_eq {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ)
    (hM : 0 < M) :
    ∑ w : Σ l : Fin (K + 1), Fin l.val → (Fin M × J), ‖cubeCoeff h τ M K (Sum.inl w)‖
      = cubeS0 h τ M K := by
  calc ∑ w : Σ l : Fin (K + 1), Fin l.val → (Fin M × J), ‖cubeCoeff h τ M K (Sum.inl w)‖
      = ∑ l : Fin (K + 1), cubeOrderMass h τ M l.val := by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun l _ => cubeOrderMass_eq h τ M K hM l
    _ = ∑ l ∈ Finset.range (K + 1), cubeOrderMass h τ M l := by
        exact Fin.sum_univ_eq_sum_range (fun l => cubeOrderMass h τ M l) (K + 1)
    _ = cubeS0 h τ M K := rfl

/-- Under nonnegative scale and the short-time condition, the unpadded mass is at most `2 -
(1/2)^K`. -/
theorem cubeS0_le_two {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ)
    (hscale : 0 ≤ cubeScale h τ M) (hτ : |τ| * cubeScale h τ M ≤ 1 / 2) :
    cubeS0 h τ M K ≤ 2 - (1 / 2 : ℝ) ^ K := by
  have hpos : 0 ≤ |τ| * cubeScale h τ M := mul_nonneg (abs_nonneg _) hscale
  have hfact : ∀ l : ℕ, (1 : ℝ) ≤ (l.factorial : ℝ) :=
    fun l => by exact_mod_cast l.factorial_pos
  have hterm : ∀ l ∈ Finset.range (K + 1),
      (|τ| * cubeScale h τ M) ^ l / l.factorial ≤ (1 / 2 : ℝ) ^ l := by
    intro l _
    refine (div_le_iff₀ (by positivity : (0 : ℝ) < (l.factorial : ℝ))).2 ?_
    refine le_trans (pow_le_pow_left₀ hpos hτ l) ?_
    exact le_mul_of_one_le_right (by positivity) (hfact l)
  calc cubeS0 h τ M K = ∑ l ∈ Finset.range (K + 1), (|τ| * cubeScale h τ M) ^ l / l.factorial :=
        rfl
    _ ≤ ∑ l ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ l := Finset.sum_le_sum hterm
    _ = 2 - (1 / 2 : ℝ) ^ K := by
        rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
        field_simp
        ring

/-- The false padding label has coefficient equal to minus half the deficit of the unpadded mass
from two. -/
private lemma cubeCoeff_padding_false {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) :
    cubeCoeff h τ M K (Sum.inr false) = -(((2 - cubeS0 h τ M K) / 2 : ℝ) : ℂ) := by
  simp only [cubeCoeff]
  push_cast
  ring

/-- The true padding label has coefficient equal to half the deficit of the unpadded mass from
two. -/
private lemma cubeCoeff_padding_true {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) :
    cubeCoeff h τ M K (Sum.inr true) = (((2 - cubeS0 h τ M K) / 2 : ℝ) : ℂ) := by
  simp only [cubeCoeff]
  push_cast
  ring

/-- For a positive grid size and the stated short-time scale bounds, the padded Taylor
coefficient mass is exactly two. -/
theorem cube_total_mass_eq_two {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) (hM : 0 < M) (hscale : 0 ≤ cubeScale h τ M)
    (hτ : |τ| * cubeScale h τ M ≤ 1 / 2) :
    ∑ x, ‖cubeCoeff h τ M K x‖ = 2 := by
  have hs0 := cubeS0_le_two h τ M K hscale hτ
  have hs0lt : cubeS0 h τ M K < 2 := by
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
    linarith
  have hpos : 0 ≤ 2 - cubeS0 h τ M K := by linarith
  have hhalf : 0 ≤ (2 - cubeS0 h τ M K) / 2 := by linarith
  have hpad : ∑ b : Bool, ‖cubeCoeff h τ M K (Sum.inr b)‖ = 2 - cubeS0 h τ M K := by
    have hval : ∀ b : Bool, ‖cubeCoeff h τ M K (Sum.inr b)‖ = (2 - cubeS0 h τ M K) / 2 := by
      intro b
      cases b with
      | false =>
          rw [cubeCoeff_padding_false, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hhalf]
      | true =>
          rw [cubeCoeff_padding_true, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hhalf]
    rw [Fintype.sum_bool, hval false, hval true]
    ring
  rw [Fintype.sum_sum_type, cubeS0_eq h τ M K hM, hpad]
  linarith

/-- For a positive grid size and the stated short-time scale bounds, the squared preparation
amplitudes sum to one. -/
theorem cube_amplitude_sq_sum {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) (hM : 0 < M) (hscale : 0 ≤ cubeScale h τ M)
    (hτ : |τ| * cubeScale h τ M ≤ 1 / 2) :
    ∑ x, (cubeAmplitude h τ M K x) ^ 2 = 1 := by
  simp only [cubeAmplitude, Real.sq_sqrt (div_nonneg (norm_nonneg _) zero_le_two)]
  rw [← Finset.sum_div, cube_total_mass_eq_two h τ M K hM hscale hτ]
  norm_num

/-- Every padded Taylor coefficient factors as twice the squared amplitude times its coefficient
phase. -/
theorem cubeCoeff_split {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ)
    (x : CubeLabel J M K) :
    cubeCoeff h τ M K x =
      2 * (cubeAmplitude h τ M K x) ^ 2 * coefficientPhase (cubeCoeff h τ M K x) := by
  by_cases hz : cubeCoeff h τ M K x = 0
  · simp [hz, cubeAmplitude, coefficientPhase]
  · have hn : (0 : ℝ) < ‖cubeCoeff h τ M K x‖ := norm_pos_iff.mpr hz
    rw [cubeAmplitude, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity),
      coefficientPhase, if_neg hz]
    have hcast : (2 : ℂ) * ((‖cubeCoeff h τ M K x‖ / 2 : ℝ) : ℂ)
        = (‖cubeCoeff h τ M K x‖ : ℂ) := by
      push_cast
      ring
    rw [hcast]
    exact (mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hn))).symm

/-- The diagonal coefficient-phase gate is unitary. -/
theorem cubePhaseGate_unitary {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ)
    (K : ℕ) :
    cubePhaseGate h τ M K ∈ Matrix.unitaryGroup (CubeLabel J M K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, cubePhaseGate,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  exact coefficientPhase_unit _

/-- For a positive grid size and the stated short-time scale bounds, the Taylor preparation
matrix is unitary. -/
theorem cubePrepare_unitary {J : Type} [Fintype J] (h : ℝ → J → ℝ) (τ : ℝ)
    (M : ℕ) (K : ℕ) (hM : 0 < M) (hscale : 0 ≤ cubeScale h τ M)
    (hτ : |τ| * cubeScale h τ M ≤ 1 / 2) :
    cubePrepare h τ M K ∈ Matrix.unitaryGroup (CubeLabel J M K) ℂ :=
  nonnegativePrepare_unitary _ _ (fun _ => Real.sqrt_nonneg _)
    (cube_amplitude_sq_sum h τ M K hM hscale hτ)

/-- Under the preparation hypotheses, the preparation matrix times its adjoint is the identity. -/
theorem cubePrepare_star_mul_one {J : Type} [Fintype J]
    (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) (hM : 0 < M)
    (hscale : 0 ≤ cubeScale h τ M) (hτ : |τ| * cubeScale h τ M ≤ 1 / 2) :
    cubePrepare h τ M K * star (cubePrepare h τ M K) = 1 := by
  have hunit := cubePrepare_unitary h τ M K hM hscale hτ
  show cubePrepare h τ M K * star (cubePrepare h τ M K) = 1
  rw [Matrix.mem_unitaryGroup_iff] at hunit
  exact hunit

/-- The coefficient-phase gate times its adjoint is the identity. -/
theorem cubePhaseGate_star_mul_one {J : Type} [Fintype J]
    (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) :
    cubePhaseGate h τ M K * star (cubePhaseGate h τ M K) = 1 := by
  have hunit := cubePhaseGate_unitary h τ M K
  show cubePhaseGate h τ M K * star (cubePhaseGate h τ M K) = 1
  rw [Matrix.mem_unitaryGroup_iff] at hunit
  exact hunit

end Qatlib.Concepts.RandCompile.ChannelBudget
