/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.PerturbationDyson
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Mixed Dyson terms

This module constructs Dyson integrals with independently varying perturbation arguments for the
perturbative analysis surrounding [AftabAnTrivisa2026]. The recursive `iterate` is multilinear,
and `mixedMap` packages the resulting terms as continuous real multilinear maps.

Factorial norm bounds control these maps, and constant perturbation tuples recover
`PerturbationDyson.term`.

## Main statements

* `mixedMap_norm`: a factorial bound in the perturbation norms.
* `mixedMap_constant`: identification with ordinary perturbative Dyson terms.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MixedDyson

open Matrix Set
open scoped BigOperators Classical Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The ordered iterated integral of a tuple of perturbations conjugated by the exponential of
`A`, with the empty tuple giving the identity. -/
def iterate (A : Matrix I I ℂ) : (n : ℕ) → (Fin n → Matrix I I ℂ) → ℝ → Matrix I I ℂ
  | 0, _, _ => 1
  | n + 1, B, t => ∫ u in 0..t, pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u

/-- Exponential conjugation of a fixed matrix is continuous as a function of the negated time
parameter. -/
theorem conjugation_continuous (A B : Matrix I I ℂ) :
    Continuous (fun u : ℝ => pfConjExp A B (-u)) := by
  have h : Continuous (fun u : ℝ => -PerturbationDyson.interaction A B u) := by
    have := PerturbationDyson.interaction_continuous A B
    fun_prop
  simpa only [PerturbationDyson.interaction, neg_neg] using! h

/-- The mixed ordered integral is continuous in its terminal time. -/
theorem iterate_continuous (A : Matrix I I ℂ) (n : ℕ) (B : Fin n → Matrix I I ℂ) :
    Continuous (iterate A n B) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (intervalIntegral.differentiable_integral_of_continuous
      ((conjugation_continuous A (B 0)).mul (ih (Fin.tail B)))).continuous

/-- Exponential conjugation distributes over addition of matrices. -/
theorem conjugation_add (A X Y : Matrix I I ℂ) (u : ℝ) :
    pfConjExp A (X + Y) u = pfConjExp A X u + pfConjExp A Y u := by
  simp only [pfConjExp, mul_add, add_mul]

/-- Exponential conjugation commutes with real scalar multiplication. -/
theorem conjugation_smul (A X : Matrix I I ℂ) (c u : ℝ) :
    pfConjExp A (c • X) u = c • pfConjExp A X u := by
  simp only [pfConjExp, Matrix.mul_smul, Matrix.smul_mul]

/-- The mixed ordered integral is additive in each perturbation argument. -/
theorem iterate_update_add (A : Matrix I I ℂ) (n : ℕ) (B : Fin n → Matrix I I ℂ)
    (i : Fin n) (X Y : Matrix I I ℂ) (t : ℝ) :
    iterate A n (Function.update B i (X + Y)) t =
      iterate A n (Function.update B i X) t + iterate A n (Function.update B i Y) t := by
  induction n generalizing t with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [iterate, Function.update_self, Fin.tail_update_zero]
      simp_rw [conjugation_add, add_mul]
      exact intervalIntegral.integral_add
        (((conjugation_continuous A X).mul (iterate_continuous A n (Fin.tail B))).intervalIntegrable _ _)
        (((conjugation_continuous A Y).mul (iterate_continuous A n (Fin.tail B))).intervalIntegrable _ _)
    | succ i =>
      simp only [iterate, Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.tail_update_succ]
      simp_rw [ih, mul_add]
      exact intervalIntegral.integral_add
        (((conjugation_continuous A (B 0)).mul
          (iterate_continuous A n (Function.update (Fin.tail B) i X))).intervalIntegrable _ _)
        (((conjugation_continuous A (B 0)).mul
          (iterate_continuous A n (Function.update (Fin.tail B) i Y))).intervalIntegrable _ _)

/-- The mixed ordered integral commutes with real scalar multiplication in each perturbation
argument. -/
theorem iterate_update_smul (A : Matrix I I ℂ) (n : ℕ) (B : Fin n → Matrix I I ℂ)
    (i : Fin n) (c : ℝ) (X : Matrix I I ℂ) (t : ℝ) :
    iterate A n (Function.update B i (c • X)) t = c • iterate A n (Function.update B i X) t := by
  induction n generalizing t with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [iterate, Function.update_self, Fin.tail_update_zero]
      simp_rw [conjugation_smul, Matrix.smul_mul]
      exact intervalIntegral.integral_smul c _
    | succ i =>
      simp only [iterate, Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.tail_update_succ]
      simp_rw [ih, Matrix.mul_smul]
      exact intervalIntegral.integral_smul c _

/-- The mixed ordered integral packaged as a multilinear map over the real numbers. -/
def iterateMultilinear (A : Matrix I I ℂ) (n : ℕ) (t : ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => Matrix I I ℂ) (Matrix I I ℂ) where
  toFun B := iterate A n B t
  map_update_add' := by
    intro dec B i X Y
    cases Subsingleton.elim dec (instDecidableEqFin n)
    exact iterate_update_add A n B i X Y t
  map_update_smul' := by
    intro dec B i c X
    cases Subsingleton.elim dec (instDecidableEqFin n)
    exact iterate_update_smul A n B i c X t

/-- A constant tuple of perturbations yields the ordered Dyson term for
`PerturbationDyson.interaction`. -/
theorem iterate_constant (A B : Matrix I I ℂ) (n : ℕ) (t : ℝ) :
    iterate A n (fun _ => B) t = orderedDysonTerm (PerturbationDyson.interaction A B) 0 n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [iterate, orderedDysonTerm, PerturbationDyson.interaction, neg_mul, neg_neg]
    apply intervalIntegral.integral_congr
    intro u _
    change pfConjExp A B (-u) * iterate A n (fun _ => B) u =
      pfConjExp A B (-u) * orderedDysonTerm (PerturbationDyson.interaction A B) 0 n u
    rw [ih]

/-- For skew-Hermitian `A`, the mixed ordered integral is bounded by the product of perturbation
norms times `|t|ⁿ / n!`. -/
theorem iterate_norm (A : Matrix I I ℂ) (hA : Aᴴ = -A)
    (n : ℕ) (B : Fin n → Matrix I I ℂ) (t : ℝ) :
    ‖iterate A n B t‖ ≤ (∏ i, ‖B i‖) * |t| ^ n / (n.factorial : ℝ) := by
  induction n generalizing t with
  | zero => simpa only [iterate, Fin.prod_univ_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, div_one] using! (l2_norm_one_le (I := I))
  | succ n ih =>
    let g : ℝ → ℝ := fun u =>
      (‖B 0‖ * ∏ i : Fin n, ‖Fin.tail B i‖) / (n.factorial : ℝ) * |u - 0| ^ n
    have hg : Continuous g := by fun_prop
    have hb : ∀ u ∈ uIoc 0 t,
        ‖pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u‖ ≤ g u := by
      intro u _
      calc
        _ ≤ ‖pfConjExp A (B 0) (-u)‖ * ‖iterate A n (Fin.tail B) u‖ := norm_mul_le _ _
        _ ≤ ‖B 0‖ * ((∏ i, ‖Fin.tail B i‖) * |u| ^ n / (n.factorial : ℝ)) :=
          mul_le_mul (pfConjExp_norm_skew A (B 0) (-u) hA) (ih (Fin.tail B) u)
            (norm_nonneg _) (norm_nonneg _)
        _ = g u := by dsimp only [g]; rw [sub_zero]; ring
    calc
      _ ≤ ∫ u in uIoc 0 t, ‖pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ u in uIoc 0 t, g u := by
        apply MeasureTheory.integral_mono_ae
        · exact (((conjugation_continuous A (B 0)).mul
            (iterate_continuous A n (Fin.tail B))).norm.intervalIntegrable 0 t).def'
        · exact (hg.intervalIntegrable 0 t).def'
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc hb
      _ = _ := by
        rw [show g = fun u => (‖B 0‖ * ∏ i : Fin n, ‖Fin.tail B i‖) /
          (n.factorial : ℝ) * |u - 0| ^ n from rfl,
          MeasureTheory.integral_const_mul, integral_pow_abs_sub_uIoc]
        rw [Fin.prod_univ_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          sub_zero]
        field_simp
        simp only [Fin.tail]
        ring

/-- The mixed ordered integral multiplied on the left by `exp (t • A)`, packaged as a real
multilinear map. -/
def mixedMultilinear (A : Matrix I I ℂ) (n : ℕ) (t : ℝ) :
    MultilinearMap ℝ (fun _ : Fin n => Matrix I I ℂ) (Matrix I I ℂ) :=
  (ContinuousLinearMap.mul ℝ (Matrix I I ℂ) (NormedSpace.exp (t • A))).toLinearMap.compMultilinearMap
    (iterateMultilinear A n t)

/-- For skew-Hermitian `A`, the mixed Dyson multilinear map satisfies the factorial bound `|t|ⁿ
/ n!` times the product of argument norms. -/
theorem mixed_norm (A : Matrix I I ℂ) (hA : Aᴴ = -A)
    (n : ℕ) (B : Fin n → Matrix I I ℂ) (t : ℝ) :
    ‖mixedMultilinear A n t B‖ ≤ |t| ^ n / (n.factorial : ℝ) * ∏ i, ‖B i‖ := by
  change ‖NormedSpace.exp (t • A) * iterate A n B t‖ ≤ _
  calc
    _ ≤ ‖NormedSpace.exp (t • A)‖ * ‖iterate A n B t‖ := norm_mul_le _ _
    _ ≤ 1 * ((∏ i, ‖B i‖) * |t| ^ n / (n.factorial : ℝ)) :=
      mul_le_mul (l2_norm_unitary_le_one (general_trotter_exp_unitary A t hA))
        (iterate_norm A hA n B t) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- The mixed Dyson term packaged as a continuous real multilinear map for skew-Hermitian `A`. -/
def mixedMap (A : Matrix I I ℂ) (hA : Aᴴ = -A) (n : ℕ) (t : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Matrix I I ℂ) (Matrix I I ℂ) :=
  (mixedMultilinear A n t).mkContinuous (|t| ^ n / (n.factorial : ℝ))
    (fun B => mixed_norm A hA n B t)

/-- The mixed Dyson map with no perturbation arguments equals `exp (t • A)`. -/
theorem mixedMap_zero (A : Matrix I I ℂ) (hA : Aᴴ = -A) (t : ℝ)
    (B : Fin 0 → Matrix I I ℂ) : mixedMap A hA 0 t B = NormedSpace.exp (t • A) := by
  change NormedSpace.exp (t • A) * 1 = _
  exact mul_one _

/-- The continuous mixed Dyson map is bounded by `|t|ⁿ / n!` times the product of perturbation
norms. -/
theorem mixedMap_norm (A : Matrix I I ℂ) (hA : Aᴴ = -A)
    (n : ℕ) (t : ℝ) (B : Fin n → Matrix I I ℂ) :
    ‖mixedMap A hA n t B‖ ≤ |t| ^ n / (n.factorial : ℝ) * ∏ i, ‖B i‖ :=
  mixed_norm A hA n B t

/-- The mixed Dyson map satisfies the recursive Duhamel integral formula, inserting the first
perturbation and integrating the remaining arguments. -/
theorem mixedMap_succ (A : Matrix I I ℂ) (hA : Aᴴ = -A) (n : ℕ)
    (t : ℝ) (B : Fin (n + 1) → Matrix I I ℂ) :
    mixedMap A hA (n + 1) t B =
      ∫ u in 0..t, NormedSpace.exp ((t - u) • A) * B 0 * mixedMap A hA n u (Fin.tail B) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := .restrictScalars ℚ ℝ _
  have hi := ((conjugation_continuous A (B 0)).mul
    (iterate_continuous A n (Fin.tail B))).intervalIntegrable (μ := MeasureTheory.volume) 0 t
  have h := (ContinuousLinearMap.mul ℝ (Matrix I I ℂ)
    (NormedSpace.exp (t • A))).intervalIntegral_comp_comm hi
  change (∫ u in 0..t, NormedSpace.exp (t • A) *
    (pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u)) =
      NormedSpace.exp (t • A) * (∫ u in 0..t,
        pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u) at h
  change NormedSpace.exp (t • A) * (∫ u in 0..t,
    pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u) = _
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  have hc : Commute (t • A) ((-u) • A) :=
    ((Commute.refl A).smul_left t).smul_right (-u)
  have he : NormedSpace.exp (t • A) * NormedSpace.exp ((-u) • A) =
      NormedSpace.exp ((t - u) • A) := by
    calc
      _ = NormedSpace.exp (t • A + (-u) • A) := (NormedSpace.exp_add_of_commute hc).symm
      _ = _ := by rw [← add_smul, ← sub_eq_add_neg]
  change NormedSpace.exp (t • A) * (pfConjExp A (B 0) (-u) * iterate A n (Fin.tail B) u) =
    NormedSpace.exp ((t - u) • A) * B 0 * (NormedSpace.exp (u • A) * iterate A n (Fin.tail B) u)
  rw [← he]
  simp only [pfConjExp, neg_neg]
  noncomm_ring

/-- Evaluating the mixed Dyson map on a constant tuple gives the corresponding
`PerturbationDyson.term`. -/
theorem mixedMap_constant (A B : Matrix I I ℂ) (hA : Aᴴ = -A) (n : ℕ) (t : ℝ) :
    mixedMap A hA n t (fun _ => B) = PerturbationDyson.term A B n t := by
  change NormedSpace.exp (t • A) * iterate A n (fun _ => B) t = _
  rw [iterate_constant]
  rfl

end Qatlib.Papers.CommutLCHS26.MainResults.MixedDyson
