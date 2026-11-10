/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionEffectiveDefs
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularSchurDualityQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ConversionCore.WitnessCompile.PartialPermutation
open Qatlib.Concepts.ConversionCore.WitnessCompile.RationalRectFactorization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionEffective

open Qatlib
open Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Concepts.NumericalWord.MixedWordError
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem ratCast_normSq (t : ℚ) : Complex.normSq ((t : ℚ) : ℂ) = ((t * t : ℚ) : ℝ) := by
  simp [Complex.normSq_apply]

theorem ratCast_normSq' (t : ℚ) : ‖((t : ℚ) : ℂ)‖ ^ 2 = ((t * t : ℚ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, ratCast_normSq]

theorem star_mul_rat_complex (a b : ℚ) :
    star ((a : ℚ) : ℂ) * ((b : ℚ) : ℂ) = ((a * b : ℚ) : ℂ) := by
  rw [star_ratCast, ← Rat.cast_mul]

theorem cast_sum_real {ι : Type} [Fintype ι] (f : ι → ℚ) :
    (∑ i, (f i : ℝ)) = (((∑ i, f i) : ℚ) : ℝ) := by
  exact_mod_cast rfl

theorem rectFactorization_sourceCert {R S : Type} [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S] {n m : ℕ} {A : Matrix R S ℚ} {Z : Fin n → Matrix R S ℚ}
    (F : RationalRectFactorization n m A Z) (h : F.certValid) :
    sourceRectCert n (rectComplex A) (rectComplexZ Z) (F.budget : ℝ) := by
  refine ⟨m, fun r j => fun q => ((F.u j r q : ℚ) : ℂ),
    fun s j => fun q => ((F.v j s q : ℚ) : ℂ), ?_, ?_, ?_⟩
  · intro r s
    have hpt : ∀ (j : Fin n) (k : Fin m),
        star ((F.u j r k : ℚ) : ℂ) * ((F.v j s k : ℚ) : ℂ) =
          ((F.u j r k * F.v j s k : ℚ) : ℂ) := by
      intro j k
      exact star_mul_rat_complex _ _
    have hres := h.2.2 r s
    simp only [rectComplex, rectComplexZ]
    simp_rw [hpt]
    have hres' : ((A r s : ℚ) : ℂ) =
        ∑ j, ((Z j r s : ℚ) : ℂ) * ∑ k, ((F.u j r k * F.v j s k : ℚ) : ℂ) :=
      sub_eq_zero.mp hres
    exact hres'
  · intro r
    have hmass := h.1 r
    calc ∑ j, ‖toEuclidean_fromVec ((fun r j => fun q => ((F.u j r q : ℚ) : ℂ)) r j)‖ ^ 2
        = ∑ j, ∑ q, ((F.u j r q * F.u j r q : ℚ) : ℝ) := by
          simp only [norm_toEuclidean_fromVec_sq, ratCast_normSq']
      _ ≤ (F.budget : ℝ) := by
        exact hmass
  · intro s
    have hmass := h.2.1 s
    calc ∑ j, ‖toEuclidean_fromVec ((fun s j => fun q => ((F.v j s q : ℚ) : ℂ)) s j)‖ ^ 2
        = ∑ j, ∑ q, ((F.v j s q * F.v j s q : ℚ) : ℝ) := by
          simp only [norm_toEuclidean_fromVec_sq, ratCast_normSq']
      _ ≤ (F.budget : ℝ) := by
        exact hmass

theorem diagonalRectFactorization_certValid {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (t : ℚ) (ht : 0 < t) (hbound : ∀ r, |(a r : ℝ)| ≤ (t : ℝ)^2) :
    (diagonalRectFactorization a t).certValid := by
  have ht0 : (t : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  have habs : ∀ r, |a r| ≤ t * t := by
    intro r
    have hreal : |(a r : ℝ)| ≤ (t : ℝ) * (t : ℝ) := by
      simpa [pow_two] using! hbound r
    exact_mod_cast hreal
  have hsq : ∀ r, (a r / t) * (a r / t) ≤ t * t := by
    intro r
    have h1 : (a r / t) * (a r / t) = (a r * a r) / (t * t) := by
      rw [← pow_two, div_pow]
      ring
    have h2 : (a r * a r) ≤ (t * t) * (t * t) := by
      calc (a r * a r) = |a r * a r| := (abs_of_nonneg (mul_self_nonneg (a r))).symm
        _ = |a r| * |a r| := abs_mul _ _
        _ ≤ (t * t) * (t * t) :=
          mul_le_mul (habs r) (habs r) (abs_nonneg _) (by positivity)
    have h3 : 0 < t * t := by positivity
    have h4 : (a r * a r) / (t * t) ≤ ((t * t) * (t * t)) / (t * t) :=
      (div_le_div_iff_of_pos_right h3).mpr h2
    have h5 : ((t * t) * (t * t)) / (t * t) = t * t := by field_simp
    calc (a r / t) * (a r / t) = (a r * a r) / (t * t) := h1
      _ ≤ ((t * t) * (t * t)) / (t * t) := h4
      _ = t * t := h5
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [RationalRectFactorization.massU]
    simp only [Fin.sum_univ_one, Fin.sum_univ_one]
    exact_mod_cast hsq r
  · intro s
    rw [RationalRectFactorization.massV]
    simp only [Fin.sum_univ_one, Fin.sum_univ_one]
    exact_mod_cast (show (t : ℚ) * (t : ℚ) ≤ t * t from le_rfl)
  · intro r s
    rw [RationalRectFactorization.residual]
    by_cases h : r = s
    · subst h
      have hcancel : ((a r / t) * t : ℚ) = a r := by
        field_simp
      simp [diagonalRectInstance, Matrix.diagonal, diagonalRectFactorization, hcancel]
    · simp [diagonalRectInstance, Matrix.diagonal, diagonalRectFactorization, h]

theorem abs_entry_le_diagonalScaleReal {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (r : X) : |(a r : ℝ)| ≤ diagonalScaleReal a := by
  have h1 : ‖(fun r => ((a r : ℚ) : ℂ)) r‖ ≤ ‖(fun r => ((a r : ℚ) : ℂ))‖ :=
    norm_le_pi_norm (fun r : X => ((a r : ℚ) : ℂ)) r
  simpa [diagonalScaleReal] using! h1

def diagonalDualMatrix {X : Type} [Fintype X] [DecidableEq X] : Matrix X X ℂ :=
  Matrix.diagonal (fun _ => (1 : ℂ))

theorem diagonalDual_feasible {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) :
    (∀ j : Fin 1, ‖(rectComplexZ (diagonalRectInstance a).Z j).hadamard
        (diagonalDualMatrix (X := X))‖ ≤ 1) := by
  intro j
  have hj : j = 0 := by ext; simp
  subst hj
  have hhad : (rectComplexZ (diagonalRectInstance a).Z 0).hadamard
        (diagonalDualMatrix (X := X)) = Matrix.diagonal (fun _ => (1 : ℂ)) := by
    ext i j'
    by_cases h : i = j'
    · simp [rectComplexZ, rectComplex, diagonalRectInstance, diagonalDualMatrix,
        Matrix.hadamard_apply, h]
    · simp [rectComplexZ, rectComplex, diagonalRectInstance, diagonalDualMatrix,
        Matrix.hadamard_apply, h]
  rw [hhad, Matrix.l2_opNorm_diagonal]
  have hle : ‖(fun _ : X => (1 : ℂ))‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    simp
  omega

theorem diagonal_value_lower_bound {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) :
    ENNReal.ofReal (diagonalScaleReal a) ≤
      sourceRectValue (rectComplex (diagonalRectInstance a).A)
        (rectComplexZ (diagonalRectInstance a).Z) := by
  have hdual : sourceRectValue (rectComplex (diagonalRectInstance a).A)
        (rectComplexZ (diagonalRectInstance a).Z) = sourceRectDual
        (rectComplex (diagonalRectInstance a).A)
        (rectComplexZ (diagonalRectInstance a).Z) :=
    (rectangularSchurDuality X X 1 (rectComplex (diagonalRectInstance a).A)
      (rectComplexZ (diagonalRectInstance a).Z)).1
  rw [hdual]
  have hnorm : ‖(rectComplex (diagonalRectInstance a).A).hadamard
      (diagonalDualMatrix (X := X))‖ = diagonalScaleReal a := by
    have hhad : (rectComplex (diagonalRectInstance a).A).hadamard
        (diagonalDualMatrix (X := X)) = Matrix.diagonal (fun r => ((a r : ℚ) : ℂ)) := by
      ext i j'
      by_cases h : i = j'
      · simp [rectComplex, diagonalRectInstance, diagonalDualMatrix,
          Matrix.hadamard_apply, h]
      · simp [rectComplex, diagonalRectInstance, diagonalDualMatrix,
          Matrix.hadamard_apply, h]
    rw [hhad, Matrix.l2_opNorm_diagonal]
    rfl
  have hle : ENNReal.ofReal (diagonalScaleReal a) ≤
      ENNReal.ofReal ‖(rectComplex (diagonalRectInstance a).A).hadamard
        (diagonalDualMatrix (X := X))‖ :=
    ENNReal.ofReal_le_ofReal hnorm.symm.le
  exact le_iSup_of_le ⟨diagonalDualMatrix, diagonalDual_feasible a⟩ hle

theorem diagonal_value_upper_bound {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (t : ℚ) (ht : 0 < t) (hbound : ∀ r, |(a r : ℝ)| ≤ (t : ℝ)^2) :
    sourceRectValue (rectComplex (diagonalRectInstance a).A)
        (rectComplexZ (diagonalRectInstance a).Z) ≤ ENNReal.ofReal ((t : ℝ)^2) := by
  have hcert : sourceRectCert 1 (rectComplex (diagonalRectInstance a).A)
      (rectComplexZ (diagonalRectInstance a).Z) ((t : ℝ)^2) := by
    have h := rectFactorization_sourceCert (diagonalRectFactorization a t)
      (diagonalRectFactorization_certValid a t ht hbound)
    have hbud : (diagonalRectFactorization a t).budget = t * t := rfl
    rw [hbud] at h
    have hcast : ((t : ℝ)^2) = ((t * t : ℚ) : ℝ) := by
      push_cast
      ring
    rw [← hcast] at h
    exact h
  have hw : 0 ≤ (t : ℝ)^2 := by positivity
  exact (sourceRectValue_budget_boundary (rectComplex (diagonalRectInstance a).A)
    (rectComplexZ (diagonalRectInstance a).Z) ((t : ℝ)^2) hw).mpr hcert

theorem clause90_diagonal_near_optimal {X : Type} [Fintype X] [DecidableEq X]
    (a : X → ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (t : ℚ) (F : RationalRectFactorization 1 1 (diagonalRectInstance a).A
        (diagonalRectInstance a).Z),
      0 < t ∧
      (∀ r, |(a r : ℝ)| ≤ (t : ℝ)^2) ∧
      ((t : ℝ)^2 ≤ diagonalScaleReal a + ε) ∧
      F.certValid ∧
      ENNReal.ofReal (diagonalScaleReal a) ≤
        sourceRectValue (rectComplex (diagonalRectInstance a).A)
          (rectComplexZ (diagonalRectInstance a).Z) ∧
      sourceRectValue (rectComplex (diagonalRectInstance a).A)
          (rectComplexZ (diagonalRectInstance a).Z) ≤ ENNReal.ofReal ((t : ℝ)^2) := by
  have hM : 0 ≤ diagonalScaleReal a := norm_nonneg _
  have hMε : diagonalScaleReal a < diagonalScaleReal a + ε := by linarith
  have hsqrt : Real.sqrt (diagonalScaleReal a) <
      Real.sqrt (diagonalScaleReal a + ε) := by
    rw [Real.sqrt_lt' (by positivity : 0 < Real.sqrt (diagonalScaleReal a + ε))]
    rw [Real.sq_sqrt (by linarith : 0 ≤ diagonalScaleReal a + ε)]
    exact hMε
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (K := ℝ) hsqrt
  have ht0R : 0 < (t : ℝ) := by
    have hsq : 0 ≤ Real.sqrt (diagonalScaleReal a) :=
      Real.sqrt_nonneg (diagonalScaleReal a)
    linarith
  have ht0 : 0 < t := by exact_mod_cast ht0R
  have hsq_lo : diagonalScaleReal a < (t : ℝ)^2 := by
    have h1 : (Real.sqrt (diagonalScaleReal a)) ^ 2 = diagonalScaleReal a :=
      Real.sq_sqrt hM
    have h2 : 0 ≤ Real.sqrt (diagonalScaleReal a) := Real.sqrt_nonneg _
    have h3 : 0 < (t : ℝ) := by exact_mod_cast ht0
    have h4 : 0 < (t : ℝ) - Real.sqrt (diagonalScaleReal a) := by linarith
    have h5 : 0 < (t : ℝ) + Real.sqrt (diagonalScaleReal a) := by linarith
    have h6 : 0 < ((t : ℝ) - Real.sqrt (diagonalScaleReal a)) *
        ((t : ℝ) + Real.sqrt (diagonalScaleReal a)) := mul_pos h4 h5
    nlinarith
  have hsq_hi : (t : ℝ)^2 < diagonalScaleReal a + ε := by
    have h1 : (Real.sqrt (diagonalScaleReal a + ε)) ^ 2 = diagonalScaleReal a + ε :=
      Real.sq_sqrt (by linarith : 0 ≤ diagonalScaleReal a + ε)
    have h2 : 0 ≤ Real.sqrt (diagonalScaleReal a + ε) := Real.sqrt_nonneg _
    have h3 : 0 < (t : ℝ) := by exact_mod_cast ht0
    have h4 : 0 < Real.sqrt (diagonalScaleReal a + ε) - (t : ℝ) := by linarith
    have h5 : 0 < Real.sqrt (diagonalScaleReal a + ε) + (t : ℝ) := by linarith
    have h6 : 0 < (Real.sqrt (diagonalScaleReal a + ε) - (t : ℝ)) *
        (Real.sqrt (diagonalScaleReal a + ε) + (t : ℝ)) := mul_pos h4 h5
    nlinarith
  have hbound : ∀ r, |(a r : ℝ)| ≤ (t : ℝ)^2 := by
    intro r
    have hle := abs_entry_le_diagonalScaleReal a r
    linarith
  refine ⟨t, diagonalRectFactorization a t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast ht0
  · exact hbound
  · linarith
  · exact diagonalRectFactorization_certValid a t (by exact_mod_cast ht0) hbound
  · exact diagonal_value_lower_bound a
  · exact diagonal_value_upper_bound a t (by exact_mod_cast ht0) hbound

theorem norm_ratCast_complex (a : ℚ) : ‖((a : ℚ) : ℂ)‖ = |(a : ℝ)| := by
  have h1 : ‖((a : ℚ) : ℂ)‖ ^ 2 = ((a * a : ℚ) : ℝ) := ratCast_normSq' a
  have h2 : |(a : ℝ)| ^ 2 = ((a * a : ℚ) : ℝ) := by
    rw [sq_abs]
    norm_cast
    ring
  have hsq : ‖((a : ℚ) : ℂ)‖ ^ 2 = |(a : ℝ)| ^ 2 := by rw [h1, h2]
  have hnonneg : 0 ≤ ‖((a : ℚ) : ℂ)‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ |(a : ℝ)| := abs_nonneg _
  nlinarith

theorem partialPerm_mulVec {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (v : QState S) (r : R) :
    (P.complexMatrix *ᵥ v) r = (if r ∈ P.support then v (P.col r) else 0) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [PartialPermutation.complexMatrix]
  by_cases hr : r ∈ P.support
  · have h1 : (∑ s, (if r ∈ P.support ∧ P.col r = s then 1 else 0) * v s)
        = ∑ s, if s = P.col r then v s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [hr, true_and]
      by_cases hc : P.col r = s
      · rw [if_pos hc, if_pos hc.symm]
        simp only [one_mul]
      · rw [if_neg hc, zero_mul, if_neg (fun h => hc h.symm)]
    rw [h1, sum_ite_single, if_pos hr]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro s _
    simp [hr]

theorem partialPerm_l2_opNorm_le {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S)
    (hinj : ∀ r1 ∈ P.support, ∀ r2 ∈ P.support, P.col r1 = P.col r2 → r1 = r2) :
    ‖P.complexMatrix‖ ≤ 1 := by
  apply l2_opNorm_le_of_mulVec_le (by norm_num) _
  intro v
  have hsq : ‖toEuclidean_fromVec (P.complexMatrix *ᵥ v)‖ ^ 2
      ≤ ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    have hsq' : ∀ r, ‖(P.complexMatrix *ᵥ v) r‖ ^ 2
        = if r ∈ P.support then ‖v (P.col r)‖ ^ 2 else 0 := by
      intro r
      rw [partialPerm_mulVec]
      by_cases hr : r ∈ P.support
      · rw [if_pos hr, if_pos hr]
      · rw [if_neg hr, if_neg hr]
        simp
    rw [Finset.sum_congr rfl (fun r _ => hsq' r)]
    have h1 : (∑ r, (if r ∈ P.support then ‖v (P.col r)‖ ^ 2 else 0))
        = ∑ r ∈ P.support, ‖v (P.col r)‖ ^ 2 := by
      have h := Finset.sum_ite_mem (Finset.univ : Finset R) P.support
        (fun r => ‖v (P.col r)‖ ^ 2)
      simpa using! h
    rw [h1]
    have h2 : (∑ r ∈ P.support, ‖v (P.col r)‖ ^ 2)
        = ∑ y ∈ P.support.image P.col, ‖v y‖ ^ 2 := by
      refine Finset.sum_bij (fun a _ => P.col a)
        (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) ?_ ?_ ?_
      · intro r1 hr1 r2 hr2 h
        exact hinj r1 hr1 r2 hr2 h
      · intro y hy
        obtain ⟨r, hr, hry⟩ := Finset.mem_image.mp hy
        exact ⟨r, hr, hry⟩
      · intro r _
        rfl
    rw [h2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ => sq_nonneg _)
  have hle : ‖toEuclidean_fromVec (P.complexMatrix *ᵥ v)‖
      ≤ ‖toEuclidean_fromVec v‖ := by
    have hnonneg : 0 ≤ ‖toEuclidean_fromVec (P.complexMatrix *ᵥ v)‖ := norm_nonneg _
    have hnonneg2 : 0 ≤ ‖toEuclidean_fromVec v‖ := norm_nonneg _
    nlinarith
  simpa only [one_mul] using! hle

theorem partialMonomial_mulVec {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℂ) (v : QState S) (r : R) :
    (P.complexMonomial amp *ᵥ v) r
      = (if r ∈ P.support then amp r * v (P.col r) else 0) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [PartialPermutation.complexMonomial]
  by_cases hr : r ∈ P.support
  · have h1 : (∑ s, (if r ∈ P.support ∧ P.col r = s then amp r else 0) * v s)
        = ∑ s, if s = P.col r then amp r * v s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [hr, true_and]
      by_cases hc : P.col r = s
      · rw [if_pos hc, if_pos hc.symm]
      · rw [if_neg hc, zero_mul, if_neg (fun h => hc h.symm)]
    rw [h1, sum_ite_single, if_pos hr]
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro s _
    simp [hr]

theorem partialMonomial_l2_opNorm_ge {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℂ)
    (hinj : ∀ r1 ∈ P.support, ∀ r2 ∈ P.support, P.col r1 = P.col r2 → r1 = r2)
    (r : R) (hr : r ∈ P.support) :
    ‖amp r‖ ≤ ‖P.complexMonomial amp‖ := by
  set v : QState S := Pi.single (P.col r) 1 with hv
  have hcol : ∀ r2 ∈ P.support, r2 ≠ r → P.col r2 ≠ P.col r := by
    intro r2 hr2 hne h
    exact hne (hinj r2 hr2 r hr h)
  have hmul : ∀ r2 : R,
      (P.complexMonomial amp *ᵥ v) r2 = (if r2 = r then amp r else 0) := by
    intro r2
    rw [partialMonomial_mulVec]
    by_cases hr2 : r2 ∈ P.support
    · by_cases heq : r2 = r
      · have hr' : r ∈ P.support := heq ▸ hr2
        rw [heq, if_pos hr', if_pos rfl]
        rw [hv, Pi.single_apply, if_pos rfl]
        simp
      · rw [if_neg heq, if_pos hr2]
        have hne : P.col r2 ≠ P.col r := hcol r2 hr2 heq
        rw [hv, Pi.single_apply, if_neg hne]
        simp
    · rw [if_neg hr2]
      by_cases heq : r2 = r
      · exfalso
        exact hr2 (heq ▸ hr)
      · rw [if_neg heq]
  have hnormv : ‖toEuclidean_fromVec v‖ = 1 := by
    have h : ‖toEuclidean_fromVec v‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq]
      have h' : ∑ i : S, ‖v i‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single (P.col r)]
        · simp [hv]
        · intro b _ hb
          simp [hv, hb]
        · intro h
          exact absurd h (by simp)
      rw [h']
    nlinarith [norm_nonneg (toEuclidean_fromVec v)]
  have hmulnorm : ‖toEuclidean_fromVec (P.complexMonomial amp *ᵥ v)‖ = ‖amp r‖ := by
    have hsq : ‖toEuclidean_fromVec (P.complexMonomial amp *ᵥ v)‖ ^ 2
        = ‖amp r‖ ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq]
      have h : ∀ r2 : R, ‖(P.complexMonomial amp *ᵥ v) r2‖ ^ 2
          = (if r2 = r then ‖amp r‖ ^ 2 else 0) := by
        intro r2
        rw [hmul r2]
        by_cases heq : r2 = r
        · rw [if_pos heq, if_pos heq]
        · rw [if_neg heq, if_neg heq]
          simp
      rw [Finset.sum_congr rfl (fun r2 _ => h r2)]
      simp
    nlinarith [norm_nonneg (toEuclidean_fromVec (P.complexMonomial amp *ᵥ v)),
      norm_nonneg (amp r)]
  have hle := l2_norm_mulVec_fromVec_le (P.complexMonomial amp) v
  rw [hnormv, hmulnorm, mul_one] at hle
  exact hle

theorem monomialRectFactorization_certValid {R S : Type} [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ) (t : ℚ)
    (ht : 0 < t) (hbound : ∀ r ∈ P.support, |(amp r : ℝ)| ≤ (t : ℝ)^2) :
    (monomialRectFactorization P amp t).certValid := by
  have ht0 : (t : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  have habs : ∀ r ∈ P.support, |amp r| ≤ t * t := by
    intro r hr
    have hreal : |(amp r : ℝ)| ≤ (t : ℝ) * (t : ℝ) := by
      simpa [pow_two] using! hbound r hr
    exact_mod_cast hreal
  have hsq : ∀ r ∈ P.support, ((amp r / t : ℚ) * (amp r / t : ℚ)) ≤ t * t := by
    intro r hr
    have h1 : (amp r / t) * (amp r / t) = (amp r * amp r) / (t * t) := by
      rw [← pow_two, div_pow]
      ring
    have h2 : (amp r * amp r) ≤ (t * t) * (t * t) := by
      calc amp r * amp r = |amp r * amp r| := (abs_of_nonneg (mul_self_nonneg (amp r))).symm
        _ = |amp r| * |amp r| := abs_mul _ _
        _ ≤ (t * t) * (t * t) := mul_le_mul (habs r hr) (habs r hr) (abs_nonneg _) (by positivity)
    have h3 : 0 < t * t := by positivity
    have h4 : (amp r * amp r) / (t * t) ≤ ((t * t) * (t * t)) / (t * t) :=
      (div_le_div_iff_of_pos_right h3).mpr h2
    have h5 : ((t * t) * (t * t)) / (t * t) = t * t := by field_simp
    calc (amp r / t) * (amp r / t) = (amp r * amp r) / (t * t) := h1
      _ ≤ ((t * t) * (t * t)) / (t * t) := h4
      _ = t * t := h5
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [RationalRectFactorization.massU]
    simp only [Fin.sum_univ_one, Fin.sum_univ_one]
    simp only [monomialRectFactorization]
    by_cases hr : r ∈ P.support
    · simp only [if_pos hr]
      exact_mod_cast hsq r hr
    · simp only [if_neg hr, mul_zero]
      have : (0 : ℚ) ≤ t * t := by positivity
      exact_mod_cast this
  · intro s
    rw [RationalRectFactorization.massV]
    simp only [Fin.sum_univ_one, Fin.sum_univ_one]
    exact_mod_cast (show (t : ℚ) * (t : ℚ) ≤ t * t from le_rfl)
  · intro r s
    rw [RationalRectFactorization.residual]
    by_cases hr : r ∈ P.support
    · by_cases hcs : P.col r = s
      · have hcancel : ((amp r / t) * t : ℚ) = amp r := by
          field_simp
        simp [monomialRectInstance, PartialPermutation.monomial, PartialPermutation.matrix,
          monomialRectFactorization, hr, hcs, hcancel]
      · simp [monomialRectInstance, PartialPermutation.monomial, PartialPermutation.matrix,
          monomialRectFactorization, hr, hcs]
    · simp [monomialRectInstance, PartialPermutation.monomial, PartialPermutation.matrix,
        monomialRectFactorization, hr]

def monomialDualMatrix {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (P : PartialPermutation R S) : Matrix R S ℂ := P.complexMatrix

theorem monomialDual_feasible {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ)
    (hinj : ∀ r1 ∈ P.support, ∀ r2 ∈ P.support, P.col r1 = P.col r2 → r1 = r2) :
    (∀ j : Fin 1, ‖(rectComplexZ (monomialRectInstance P amp).Z j).hadamard
        (monomialDualMatrix P)‖ ≤ 1) := by
  intro j
  have hj : j = 0 := by ext; simp
  subst hj
  have hhad : (rectComplexZ (monomialRectInstance P amp).Z 0).hadamard (monomialDualMatrix P)
      = P.complexMatrix := by
    ext r s
    by_cases h1 : r ∈ P.support
    · by_cases h2 : P.col r = s
      · simp [rectComplexZ, rectComplex, monomialRectInstance, PartialPermutation.matrix,
          PartialPermutation.complexMatrix, monomialDualMatrix, h1, h2]
      · simp [rectComplexZ, rectComplex, monomialRectInstance, PartialPermutation.matrix,
          PartialPermutation.complexMatrix, monomialDualMatrix, h1, h2]
    · simp [rectComplexZ, rectComplex, monomialRectInstance, PartialPermutation.matrix,
        PartialPermutation.complexMatrix, monomialDualMatrix, h1]
  rw [hhad]
  exact partialPerm_l2_opNorm_le P hinj

theorem monomial_value_lower_bound {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ)
    (hinj : ∀ r1 ∈ P.support, ∀ r2 ∈ P.support, P.col r1 = P.col r2 → r1 = r2) :
    ENNReal.ofReal (monomialScaleReal P amp) ≤
      sourceRectValue (rectComplex (monomialRectInstance P amp).A)
        (rectComplexZ (monomialRectInstance P amp).Z) := by
  have hdual : sourceRectValue (rectComplex (monomialRectInstance P amp).A)
        (rectComplexZ (monomialRectInstance P amp).Z) = sourceRectDual
      (rectComplex (monomialRectInstance P amp).A)
      (rectComplexZ (monomialRectInstance P amp).Z) :=
    (rectangularSchurDuality R S 1 (rectComplex (monomialRectInstance P amp).A)
      (rectComplexZ (monomialRectInstance P amp).Z)).1
  rw [hdual]
  have hhad : (rectComplex (monomialRectInstance P amp).A).hadamard (monomialDualMatrix P)
      = P.complexMonomial (fun r => (amp r : ℂ)) := by
    ext r s
    by_cases h1 : r ∈ P.support
    · by_cases h2 : P.col r = s
      · simp [rectComplex, monomialRectInstance, PartialPermutation.monomial,
          PartialPermutation.complexMatrix, PartialPermutation.complexMonomial,
          monomialDualMatrix, h1, h2]
      · simp [rectComplex, monomialRectInstance, PartialPermutation.monomial,
          PartialPermutation.complexMatrix, PartialPermutation.complexMonomial,
          monomialDualMatrix, h1, h2]
    · simp [rectComplex, monomialRectInstance, PartialPermutation.monomial,
        PartialPermutation.complexMatrix, PartialPermutation.complexMonomial,
        monomialDualMatrix, h1]
  have hnorm : ‖(rectComplex (monomialRectInstance P amp).A).hadamard
      (monomialDualMatrix P)‖ = ‖P.complexMonomial (fun r => (amp r : ℂ))‖ := by
    rw [hhad]
  have hscale_le : monomialScaleReal P amp
      ≤ ‖P.complexMonomial (fun r => (amp r : ℂ))‖ := by
    unfold monomialScaleReal
    apply (pi_norm_le_iff_of_nonneg
      (by positivity : (0 : ℝ) ≤ ‖P.complexMonomial (fun r => (amp r : ℂ))‖)).mpr
    intro r
    by_cases hr : r ∈ P.support
    · rw [if_pos hr]
      exact partialMonomial_l2_opNorm_ge P (fun r => (amp r : ℂ)) hinj r hr
    · rw [if_neg hr]
      calc ‖(0 : ℂ)‖ = 0 := by simp
        _ ≤ ‖P.complexMonomial (fun r => (amp r : ℂ))‖ := by positivity
  have hle : ENNReal.ofReal (monomialScaleReal P amp)
      ≤ ENNReal.ofReal ‖(rectComplex (monomialRectInstance P amp).A).hadamard
        (monomialDualMatrix P)‖ := by
    rw [hnorm]
    exact ENNReal.ofReal_le_ofReal hscale_le
  exact le_iSup_of_le ⟨monomialDualMatrix P, monomialDual_feasible P amp hinj⟩ hle

theorem monomial_value_upper_bound {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ) (t : ℚ) (ht : 0 < t)
    (hbound : ∀ r ∈ P.support, |(amp r : ℝ)| ≤ (t : ℝ)^2) :
    sourceRectValue (rectComplex (monomialRectInstance P amp).A)
        (rectComplexZ (monomialRectInstance P amp).Z) ≤ ENNReal.ofReal ((t : ℝ)^2) := by
  have hcert : sourceRectCert 1 (rectComplex (monomialRectInstance P amp).A)
      (rectComplexZ (monomialRectInstance P amp).Z) ((t : ℝ)^2) := by
    have h := rectFactorization_sourceCert (monomialRectFactorization P amp t)
      (monomialRectFactorization_certValid P amp t ht hbound)
    have hbud : (monomialRectFactorization P amp t).budget = t * t := rfl
    rw [hbud] at h
    have hcast : ((t : ℝ)^2) = ((t * t : ℚ) : ℝ) := by
      push_cast
      ring
    rw [← hcast] at h
    exact h
  have hw : 0 ≤ (t : ℝ)^2 := by positivity
  exact (sourceRectValue_budget_boundary (rectComplex (monomialRectInstance P amp).A)
    (rectComplexZ (monomialRectInstance P amp).Z) ((t : ℝ)^2) hw).mpr hcert

theorem clause90_monomial_near_optimal {R S : Type} [Fintype R] [DecidableEq R] [Fintype S]
    [DecidableEq S] (P : PartialPermutation R S) (amp : R → ℚ)
    (hinj : ∀ r1 ∈ P.support, ∀ r2 ∈ P.support, P.col r1 = P.col r2 → r1 = r2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (t : ℚ) (F : RationalRectFactorization 1 1 (monomialRectInstance P amp).A
        (monomialRectInstance P amp).Z),
      0 < t ∧
      (∀ r ∈ P.support, |(amp r : ℝ)| ≤ (t : ℝ)^2) ∧
      ((t : ℝ)^2 ≤ monomialScaleReal P amp + ε) ∧
      F.certValid ∧
      ENNReal.ofReal (monomialScaleReal P amp) ≤
        sourceRectValue (rectComplex (monomialRectInstance P amp).A)
          (rectComplexZ (monomialRectInstance P amp).Z) ∧
      sourceRectValue (rectComplex (monomialRectInstance P amp).A)
          (rectComplexZ (monomialRectInstance P amp).Z)
        ≤ ENNReal.ofReal ((t : ℝ)^2) := by
  have hM : 0 ≤ monomialScaleReal P amp := by
    unfold monomialScaleReal
    positivity
  have hMε : monomialScaleReal P amp < monomialScaleReal P amp + ε := by linarith
  have hsqrt : Real.sqrt (monomialScaleReal P amp) <
      Real.sqrt (monomialScaleReal P amp + ε) := by
    rw [Real.sqrt_lt' (by positivity : 0 < Real.sqrt (monomialScaleReal P amp + ε))]
    rw [Real.sq_sqrt (by linarith : 0 ≤ monomialScaleReal P amp + ε)]
    exact hMε
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (K := ℝ) hsqrt
  have ht0R : 0 < (t : ℝ) := by
    have hsq : 0 ≤ Real.sqrt (monomialScaleReal P amp) :=
      Real.sqrt_nonneg (monomialScaleReal P amp)
    linarith
  have ht0 : 0 < t := by exact_mod_cast ht0R
  have hsq_lo : monomialScaleReal P amp < (t : ℝ)^2 := by
    have h1 : (Real.sqrt (monomialScaleReal P amp)) ^ 2 = monomialScaleReal P amp :=
      Real.sq_sqrt hM
    have h2 : 0 ≤ Real.sqrt (monomialScaleReal P amp) := Real.sqrt_nonneg _
    have h3 : 0 < (t : ℝ) := by exact_mod_cast ht0
    have h4 : 0 < (t : ℝ) - Real.sqrt (monomialScaleReal P amp) := by linarith
    have h5 : 0 < (t : ℝ) + Real.sqrt (monomialScaleReal P amp) := by linarith
    have h6 : 0 < ((t : ℝ) - Real.sqrt (monomialScaleReal P amp)) *
        ((t : ℝ) + Real.sqrt (monomialScaleReal P amp)) := mul_pos h4 h5
    nlinarith
  have hsq_hi : (t : ℝ)^2 < monomialScaleReal P amp + ε := by
    have h1 : (Real.sqrt (monomialScaleReal P amp + ε)) ^ 2 = monomialScaleReal P amp + ε :=
      Real.sq_sqrt (by linarith : 0 ≤ monomialScaleReal P amp + ε)
    have h2 : 0 ≤ Real.sqrt (monomialScaleReal P amp + ε) := Real.sqrt_nonneg _
    have h3 : 0 < (t : ℝ) := by exact_mod_cast ht0
    have h4 : 0 < Real.sqrt (monomialScaleReal P amp + ε) - (t : ℝ) := by linarith
    have h5 : 0 < Real.sqrt (monomialScaleReal P amp + ε) + (t : ℝ) := by linarith
    have h6 : 0 < (Real.sqrt (monomialScaleReal P amp + ε) - (t : ℝ)) *
        (Real.sqrt (monomialScaleReal P amp + ε) + (t : ℝ)) := mul_pos h4 h5
    nlinarith
  have hbound : ∀ r ∈ P.support, |(amp r : ℝ)| ≤ (t : ℝ)^2 := by
    intro r hr
    have hle : |(amp r : ℝ)| ≤ monomialScaleReal P amp := by
      have hnorm := norm_le_pi_norm (fun r : R => (if r ∈ P.support then (amp r : ℂ) else 0)) r
      have hval : (if r ∈ P.support then (amp r : ℂ) else 0) = (amp r : ℂ) := by
        rw [if_pos hr]
      rw [hval] at hnorm
      simpa [norm_ratCast_complex] using! hnorm
    linarith
  refine ⟨t, monomialRectFactorization P amp t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast ht0
  · exact hbound
  · linarith
  · exact monomialRectFactorization_certValid P amp t (by exact_mod_cast ht0) hbound
  · exact monomial_value_lower_bound P amp hinj
  · exact monomial_value_upper_bound P amp t (by exact_mod_cast ht0) hbound

theorem synthWordNativeProgram_legal (d : SourceRationalProblem) (p : SynthWord)
    (h : synthWordLegal p) : sourceNativeLegal d (synthWordNativeProgram p) := by
  intro s hs
  have hs' : ∃ g, g ∈ p.letters ∧ SourceNativeStep.local g = s := by
    have hmem : s ∈ p.letters.map (fun g => SourceNativeStep.local g) := hs
    exact List.mem_map.mp hmem
  obtain ⟨g, hg, rfl⟩ := hs'
  have hg' := h g hg
  rw [isFixedPrimitive_iff_sourceFixedGate] at hg'
  exact hg'

theorem synthWordNativeProgram_calls (p : SynthWord) :
    sourceNativeCalls (synthWordNativeProgram p) = 0 := by
  simp [synthWordNativeProgram, sourceNativeCalls]

theorem synthWordNativeProgram_gates (p : SynthWord) :
    sourceNativeGates (synthWordNativeProgram p) = synthWordGates p := by
  simp [synthWordNativeProgram, sourceNativeGates, synthWordGates]

theorem synthWordNativeProgram_knownMatrix (p : SynthWord) :
    sourceNativeKnownMatrix (synthWordNativeProgram p) = localProgramMatrix p.letters := by
  simp [synthWordNativeProgram, sourceNativeKnownMatrix]

def gatePrecision {w : ℕ} : LocalQFTGate w → ℕ
  | .h _ => 0
  | .swap _ _ => 0
  | .cp _ _ k _ => k

theorem gatePrecision_nativeStep {w : ℕ} (g : LocalQFTGate w) :
    (match SourceNativeStep.local g with
      | .local (.cp _ _ k _) => k
      | _ => 0) = gatePrecision g := by
  cases g <;> rfl

theorem fixedPrimitive_precision_le {w : ℕ} (g : LocalQFTGate w) (hg : IsFixedPrimitive g) :
    gatePrecision g ≤ 3 := by
  cases g with
  | h a => simp [gatePrecision]
  | swap a c => simp [gatePrecision]
  | cp a c k neg =>
      rw [gatePrecision]
      exact hg

theorem foldl_max_le_three (l : List ℕ) (h : ∀ x ∈ l, x ≤ 3) : l.foldl max 0 ≤ 3 := by
  have aux : ∀ (l : List ℕ) (init : ℕ), (∀ x ∈ l, x ≤ 3) → init ≤ 3 → l.foldl max init ≤ 3 := by
    intro l
    induction l with
    | nil => intro init _ hinit; simpa using! hinit
    | cons a l ih =>
        intro init hl hinit
        have ha : a ≤ 3 := hl a (by simp)
        have hl' : ∀ x ∈ l, x ≤ 3 := fun x hx => hl x (by simp [hx])
        have hmax : max init a ≤ 3 := by
          rcases le_total init a with h | h
          · rw [max_eq_right h]; exact ha
          · rw [max_eq_left h]; exact hinit
        simp only [List.foldl_cons]
        exact ih (max init a) hl' hmax
  exact aux l 0 h (by norm_num)

theorem clause94_fixed_primitive_padded_error {w : ℕ} (g : LocalQFTGate w) :
    localProgramMatrix [g] * padClean w w - padClean w w * localGateMatrix g = 0 := by
  rw [localProgramMatrix_singleton, padClean_self, Matrix.mul_one, Matrix.one_mul, sub_self]

theorem clause94_engine_emit {w : ℕ} (g : LocalQFTGate w) (k : ℕ) (hg : IsFixedPrimitive g) :
    partialCompiler.emit w g k = [g] := partialCompiler_emit_primitive g k hg

theorem clause94_uniform_ledger :
    ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
      (partialCompiler.emit w g k).length ≤ C * (1 + synthInputBits w g k + k) ^ D ∧
      partialCompiler.anc w g k ≤ C * (1 + synthInputBits w g k + k) ^ D :=
  partialCompiler_uniform

theorem nativeFlipWord_fixed {w a : ℕ} (ha : a < w) :
    ∀ g ∈ nativeFlipWord w a ha, sourceFixedGate g := by
  intro g hg
  have hg' := hg
  simp only [nativeFlipWord, List.mem_cons] at hg'
  rcases hg' with rfl | rfl | rfl | hnil
  · simp [sourceFixedGate]
  · simp [sourceFixedGate]
  · simp [sourceFixedGate]
  · simp at hnil

theorem nativeTagWire_lt (d : SourceRationalProblem) (k : ℕ) :
    nativeTagWire d < nativeFrameWidth d + k := by
  simp [nativeTagWire, nativeFrameWidth]
  omega

theorem rationalToNativeProgram_steps (d : SourceRationalProblem) (k : ℕ) :
    (rationalToNativeProgram d k).steps
      = (nativeFlipWord (nativeFrameWidth d + k) (nativeTagWire d)
          (nativeTagWire_lt d k)).map
          (fun g => SourceNativeStep.local g) := rfl

theorem rationalToNativeProgram_legal (d : SourceRationalProblem) (k : ℕ) :
    sourceNativeLegal d (rationalToNativeProgram d k) := by
  intro s hs
  have hs' : ∃ g : LocalQFTGate (nativeFrameWidth d + k),
      g ∈ nativeFlipWord (nativeFrameWidth d + k) (nativeTagWire d) (nativeTagWire_lt d k) ∧
        s = SourceNativeStep.local g := by
    have hmem : s ∈ (rationalToNativeProgram d k).steps := hs
    have hmem' : s ∈ (nativeFlipWord (nativeFrameWidth d + k) (nativeTagWire d)
        (nativeTagWire_lt d k)).map (fun g => SourceNativeStep.local g) := hmem
    obtain ⟨g, hg, hgs⟩ := List.mem_map.mp hmem'
    exact ⟨g, hg, hgs.symm⟩
  obtain ⟨g, hg, rfl⟩ := hs'
  exact nativeFlipWord_fixed (nativeTagWire_lt d k) g hg

theorem rationalToNativeProgram_calls (d : SourceRationalProblem) (k : ℕ) :
    sourceNativeCalls (rationalToNativeProgram d k) = 0 := by
  simp [rationalToNativeProgram, nativeFlipWord, sourceNativeCalls]

theorem rationalToNativeProgram_gates (d : SourceRationalProblem) (k : ℕ) :
    sourceNativeGates (rationalToNativeProgram d k) = 3 := by
  simp [rationalToNativeProgram, nativeFlipWord, sourceNativeGates]

theorem rationalToNativeProgram_width (d : SourceRationalProblem) (k : ℕ) :
    (rationalToNativeProgram d k).width = nativeFrameWidth d + k := rfl

theorem rationalToNativeProgram_knownMatrix (d : SourceRationalProblem) (k : ℕ) :
    sourceNativeKnownMatrix (rationalToNativeProgram d k)
      = localProgramMatrix ((rationalToNativeProgram d k).steps.filterMap
          (fun s => match s with | .local g => some g | _ => none)) := rfl

theorem realToNativeProgram_steps (d : SourceRealProblem) (hacc : sourceRealAccess d) (k : ℕ) :
    (realToNativeProgram d hacc k).steps
      = (rationalToNativeProgram (rationalizeReal d hacc k) k).steps := rfl

theorem rationalizeReal_input (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    (rationalizeReal d hacc R).input = d.input := rfl

theorem rationalizeReal_count (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    (rationalizeReal d hacc R).count = d.count := rfl

theorem rationalizeReal_alphabet (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    (rationalizeReal d hacc R).alphabet = d.alphabet := rfl

theorem rationalizeReal_error (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ)
    (x : Fin d.count) (h : Fin d.dimension) (target : Bool) :
    ∃ a b : ℚ,
      ‖((a : ℂ) + (b : ℂ) * Complex.I) - (if target then d.target x h else d.start x h)‖
        ≤ (1 / 2 : ℝ) ^ R :=
  sourceCoordinateAfter_pair (Classical.choose_spec (hacc x h target R))

theorem clause96_gram_instance (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    (rationalGramInstance d hacc R).A = rationalGram d hacc R ∧
      (rationalGramInstance d hacc R).Z = (fun _ => 1) :=
  ⟨rfl, rfl⟩

theorem clause96_gram_generator {d : SourceRealProblem} {hacc : sourceRealAccess d} {R : ℕ}
    (t : ℚ) (ht : 0 < t)
    (hbound : ∀ x, |((rationalGram d hacc R) x x : ℝ)| ≤ (t : ℝ) ^ 2) :
    (diagonalRectFactorization (fun x => (rationalGram d hacc R) x x) t).certValid ∧
      ENNReal.ofReal (diagonalScaleReal (fun x => (rationalGram d hacc R) x x))
        ≤ sourceRectValue (rectComplex (diagonalRectInstance
              (fun x => (rationalGram d hacc R) x x)).A)
          (rectComplexZ (diagonalRectInstance
              (fun x => (rationalGram d hacc R) x x)).Z) ∧
      sourceRectValue (rectComplex (diagonalRectInstance
              (fun x => (rationalGram d hacc R) x x)).A)
          (rectComplexZ (diagonalRectInstance
              (fun x => (rationalGram d hacc R) x x)).Z)
        ≤ ENNReal.ofReal ((t : ℝ) ^ 2) :=
  ⟨diagonalRectFactorization_certValid _ t ht hbound,
    diagonal_value_lower_bound _,
    diagonal_value_upper_bound _ t ht hbound⟩

theorem realCoordinateAfter_error {d : SourceRealProblem} {x : Fin d.count}
    {h : Fin d.dimension} {target : Bool} {r : ℕ} {t : ℕ}
    (hc : sourceCoordinateAfter d x h target r t) :
    ∃ a b : ℚ,
      ‖((a : ℂ) + (b : ℂ) * Complex.I) - (if target then d.target x h else d.start x h)‖
        ≤ (1 / 2 : ℝ)^r :=
  sourceCoordinateAfter_pair hc

theorem nativeTagWire_eq_tagWire (d : SourceRationalProblem) :
    nativeTagWire d = tagWire d := rfl

theorem rationalToNativeProgram_matrix (d : SourceRationalProblem) (k : ℕ) (x : Fin d.count) :
    sourceNativeMatrix d x (rationalToNativeProgram d k)
      = localGateMatrix (.h ⟨tagWire d, nativeTagWire_lt d k⟩) *
        (localGateMatrix (.cp ⟨tagWire d, nativeTagWire_lt d k⟩ ⟨tagWire d, nativeTagWire_lt d k⟩ 1 true) *
          localGateMatrix (.h ⟨tagWire d, nativeTagWire_lt d k⟩)) := by
  unfold sourceNativeMatrix rationalToNativeProgram nativeFlipWord
  simp only [List.map_cons, List.map_nil, List.map_reverse, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_nil, List.append_assoc,
    List.cons_append, List.prod_cons, List.prod_nil,
    List.prod_singleton,
    sourceNativeStepMatrix, Matrix.mul_one]
  rfl

theorem rationalToNativeProgram_frame (d : SourceRationalProblem) (k : ℕ)
    (x : Fin d.count) (ψ : QState (Fin d.dimension)) :
    sourceNativeMatrix d x (rationalToNativeProgram d k) *ᵥ
        (sourceNativeClean d (rationalToNativeProgram d k).width false ψ)
      = sourceNativeClean d (rationalToNativeProgram d k).width true ψ := by
  rw [rationalToNativeProgram_matrix d k x, ← Matrix.mul_assoc]
  have hw : tagWire d < (rationalToNativeProgram d k).width := by
    rw [rationalToNativeProgram_width]
    exact nativeTagWire_lt d k
  exact nativeTagFlip_frame d (rationalToNativeProgram d k).width hw ψ

theorem rationalToNative_coherent_overlap (d : SourceRationalProblem) (k : ℕ)
    (x : Fin d.count) :
    (∑ q, star ((sourceNativeMatrix d x (rationalToNativeProgram d k) *ᵥ
        sourceNativeClean d (rationalToNativeProgram d k).width false
          (sourceRationalState (d.start x))) q) *
        (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.target x))) q).re
      = (∑ q, star (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.start x)) q) *
        (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.target x))) q).re := by
  rw [rationalToNativeProgram_frame d k x (sourceRationalState (d.start x))]

theorem rationalToNative_noncoherent_overlap (d : SourceRationalProblem) (k : ℕ)
    (x : Fin d.count) (ξ : QState (Bool × Fin d.dimension)) :
    ‖∑ q, star ((sourceNativeMatrix d x (rationalToNativeProgram d k) *ᵥ
        sourceNativeClean d (rationalToNativeProgram d k).width false
          (sourceRationalState (d.start x))) q) *
        (sourceNativeGarbageTarget d (rationalToNativeProgram d k).width
          (sourceRationalState (d.target x)) ξ) q‖
      = ‖∑ q, star (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.start x)) q) *
        (sourceNativeGarbageTarget d (rationalToNativeProgram d k).width
          (sourceRationalState (d.target x)) ξ) q‖ := by
  rw [rationalToNativeProgram_frame d k x (sourceRationalState (d.start x))]

theorem rationalToNative_coherent_overlap_numeric (d : SourceRationalProblem) (k : ℕ)
    (x : Fin d.count) :
    (∑ q, star ((sourceNativeMatrix d x (rationalToNativeProgram d k) *ᵥ
        sourceNativeClean d (rationalToNativeProgram d k).width false
          (sourceRationalState (d.start x))) q) *
        (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.target x))) q)
      = ∑ h, star (sourceRationalState (d.start x) h) * sourceRationalState (d.target x) h := by
  rw [rationalToNativeProgram_frame d k x (sourceRationalState (d.start x))]
  exact clean_overlap_same (frameFaithful_native d k) _ _

theorem rationalToNative_branch_orthogonal (d : SourceRationalProblem) (k : ℕ)
    (x : Fin d.count) :
    (∑ q, star (sourceNativeClean d (rationalToNativeProgram d k).width false
          (sourceRationalState (d.start x)) q) *
        (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.target x)) q)) = 0 :=
  clean_overlap_diff (frameFaithful_native d k) _ _

theorem rationalToNative_coherent_re_eq (d : SourceRationalProblem) (k : ℕ) (x : Fin d.count) :
    (∑ q, star ((sourceNativeMatrix d x (rationalToNativeProgram d k) *ᵥ
        sourceNativeClean d (rationalToNativeProgram d k).width false
          (sourceRationalState (d.start x))) q) *
        (sourceNativeClean d (rationalToNativeProgram d k).width true
          (sourceRationalState (d.target x))) q).re
      = (∑ h, star (sourceRationalState (d.start x) h) * sourceRationalState (d.target x) h).re := by
  rw [rationalToNative_coherent_overlap_numeric d k x]

end Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionEffective
