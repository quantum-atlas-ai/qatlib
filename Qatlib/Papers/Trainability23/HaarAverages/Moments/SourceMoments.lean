/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Single-Qubit Haar Moments and Product-State Pauli Variance

This module formalizes the single-qubit Haar moment identities Eqs. (205)--(208)
and Lemma 1, Eq. (210) of Rudolph et al.: for any `n`-qubit observable
`O = ∑_σ λ_σ σ` expanded in the Pauli string basis with real coefficients `λ_σ`,
the expectation variance over independent single-qubit Haar-random product states
equals `∑_{σ ≠ I^{⊗n}} λ_σ² / 3^{|s(σ)|}`.

## Main statements

* `eq205_haar_one_copy` -- `eq208_haar_four_copy`: 1-, 2-, 3-, and 4-copy
  single-qubit Haar integration formulas.
* `lemma1_pauli_variance_of_product_states`: Lemma 1, Eq. (210), exact variance of
  `O` over single-qubit Haar-random product states.

## References

* [Rudolph et al., 2024][RudolphEtAl2024], Supplementary Note, Lemma 1,
  Eqs. (205)--(233), pp. 43--44.
-/

set_option autoImplicit false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.HaarAverages

namespace Qatlib.Papers.Trainability23.HaarAverages.Moments

open scoped BigOperators Matrix

noncomputable section

/-- Measurable structure on `Matrix m n ℂ` transported from its entry product space. -/
local instance instMeasurableSpaceMatrix (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) := by
  cases ‹Fintype m›
  cases ‹Fintype n›
  exact inferInstanceAs (MeasurableSpace (m → n → ℂ))

/-- **Eq. (205)**: in dimension two, `∫ dV (V i 0) (V j 0)* = ((1 / 2) • 1) i j`. -/
theorem eq205_haar_one_copy (i j : Fin 2) :
    MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (V : Matrix (Fin 2) (Fin 2) ℂ) i 0 * star ((V : Matrix (Fin 2) (Fin 2) ℂ) j 0))
      = ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) i j := by
  rw [haar_entryPair_eq]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.trace_single_eq_same,
      Fintype.card_fin]
    norm_num
  · simp [hij]

/-- **Eq. (206)**: two-copy Haar average `(1 / 6) (1 ⊗ 1 + S₁₂)` of `|00⟩⟨00|`. -/
theorem eq206_haar_two_copy :
    haarKroneckerAverage
        (Matrix.single ((0, 0) : Fin 2 × Fin 2) ((0, 0) : Fin 2 × Fin 2) (1 : ℂ))
      = (1 / 6 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + (1 / 6 : ℂ) • swapOp (Fin 2) := by
  refine haarKroneckerAverage_eq_one_plus_swap _ ?_ ?_
  · rw [Matrix.trace_single_eq_same]
  · rw [Matrix.trace_single_mul]
    simp [swapOp, permMatrix, Matrix.of_apply]

/-- **Eq. (207)**: three-copy Haar average `(1 / 24) ∑_{σ ∈ S₃} P_σ` of `|000⟩⟨000|`. -/
theorem eq207_haar_three_copy :
    haarTensorAverage 3 (zeroProj 3)
      = ((24 : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin 3), tensorPerm 3 σ := by
  have h := haarTensorAverage_three_eq_permSum
  rw [h]
  norm_num

/-- **Eq. (208)**: four-copy Haar average `(1 / 120) ∑_{σ ∈ S₄} P_σ` of `|0000⟩⟨0000|`. -/
theorem eq208_haar_four_copy :
    haarTensorAverage 4 (zeroProj 4)
      = ((120 : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin 4), tensorPerm 4 σ := by
  have h := haarTensorAverage_four_eq_permSum
  rw [h]
  norm_num

/-- The four single-qubit Pauli labels `I, X, Y, Z`. -/
inductive Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Fintype, Repr

/-- The single-qubit Pauli matrices as `2 × 2` complex matrices. -/
noncomputable def pauliMat : Pauli → Matrix (Fin 2) (Fin 2) ℂ
  | Pauli.I => 1
  | Pauli.X => !![(0 : ℂ), 1; 1, 0]
  | Pauli.Y => !![(0 : ℂ), -Complex.I; Complex.I, 0]
  | Pauli.Z => !![(1 : ℂ), 0; 0, -1]

/-- The `n`-qubit Pauli string `σ₁ ⊗ ⋯ ⊗ σₙ`. -/
noncomputable def pauliString (n : ℕ) (σ : Fin n → Pauli) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, pauliMat (σ i) (x i) (y i)

/-- The non-identity qubit support `s(σ)` of a Pauli string. -/
def pauliSupport (n : ℕ) (σ : Fin n → Pauli) : Finset (Fin n) :=
  Finset.univ.filter fun i => σ i ≠ Pauli.I

/-- The Pauli Hamming weight `|s(σ)|`. -/
def pauliWeight (n : ℕ) (σ : Fin n → Pauli) : ℕ := (pauliSupport n σ).card

/-- The observable `O = ∑_σ λ_σ σ` with real Pauli coefficients `λ`. -/
noncomputable def pauliObservable (n : ℕ) (lam : (Fin n → Pauli) → ℝ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ σ : Fin n → Pauli, (lam σ : ℂ) • pauliString n σ

/-- The `n`-fold product Haar measure on single-qubit unitaries. -/
noncomputable def prodHaarMeasure (n : ℕ) :
    MeasureTheory.Measure (Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :=
  MeasureTheory.Measure.pi fun _ => haarUnitaryGroup (Fin 2)

/-- The pure-state density matrix `|ψ(U)⟩⟨ψ(U)|` of `|ψ(U)⟩ = ⊗ᵢ Uᵢ |0⟩`. -/
noncomputable def prodStateDensity (n : ℕ) (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y =>
    ∏ i, (U i : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
      * star ((U i : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)

/-- Product-Haar expectation `E[⟨ψ| O |ψ⟩]`. -/
noncomputable def pauliExpectation (n : ℕ) (lam : (Fin n → Pauli) → ℝ) : ℝ :=
  MeasureTheory.integral (prodHaarMeasure n)
    fun U => ((pauliObservable n lam * prodStateDensity n U).trace).re

/-- Product-Haar variance `Var[⟨ψ| O |ψ⟩] = E[⟨O⟩²] - (E[⟨O⟩])²`. -/
noncomputable def pauliVar (n : ℕ) (lam : (Fin n → Pauli) → ℝ) : ℝ :=
  MeasureTheory.integral (prodHaarMeasure n)
      (fun U => ((pauliObservable n lam * prodStateDensity n U).trace).re ^ 2)
    - pauliExpectation n lam ^ 2

local instance : MeasureTheory.IsProbabilityMeasure (haarUnitaryGroup (Fin 2)) :=
  ⟨haarUnitaryGroup_univ (Fin 2)⟩

local instance : BorelSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℂ))

private lemma continuous_entry (a b : Fin 2) :
    Continuous fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (V : Matrix (Fin 2) (Fin 2) ℂ) a b := by
  have ha : Continuous fun M : Fin 2 → Fin 2 → ℂ => M a := continuous_apply a
  have hb : Continuous fun v : Fin 2 → ℂ => v b := continuous_apply b
  exact (hb.comp ha).comp continuous_subtype_val

private def g1 (P : Pauli) (V : Matrix.unitaryGroup (Fin 2) ℂ) : ℂ :=
  ∑ a : Fin 2, ∑ b : Fin 2, pauliMat P a b *
    ((V : Matrix (Fin 2) (Fin 2) ℂ) b 0 * star ((V : Matrix (Fin 2) (Fin 2) ℂ) a 0))

private def f1 (P : Pauli) (V : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ := (g1 P V).re

private lemma pauliMat_star (P : Pauli) (a b : Fin 2) :
    star (pauliMat P b a) = pauliMat P a b := by
  cases P <;> fin_cases a <;> fin_cases b <;> simp [pauliMat]

private lemma g1_real (P : Pauli) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    g1 P V = (f1 P V : ℂ) := by
  have hs : star (g1 P V) = g1 P V := by
    unfold g1
    simp only [star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [star_mul, star_mul, star_star, pauliMat_star]
    ring
  have hi := congrArg Complex.im hs
  apply Complex.ext
  · rfl
  · simp only [Complex.star_def, Complex.conj_im] at hi
    simpa only [Complex.ofReal_im] using (show (g1 P V).im = 0 by linarith)

private lemma continuous_g1 (P : Pauli) : Continuous (g1 P) := by
  unfold g1
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact continuous_const.mul
    ((continuous_entry b 0).mul (continuous_entry a 0).star)

private lemma continuous_f1 (P : Pauli) : Continuous (f1 P) :=
  Complex.continuous_re.comp (continuous_g1 P)

private lemma integrable_g1 (P : Pauli) :
    MeasureTheory.Integrable (g1 P) (haarUnitaryGroup (Fin 2)) :=
  (continuous_g1 P).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma trace_pauliString (n : ℕ) (σ : Fin n → Pauli)
    (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :
    (pauliString n σ * prodStateDensity n U).trace =
      ((∏ i, f1 (σ i) (U i) : ℝ) : ℂ) := by
  calc
    _ = ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2,
        ∏ i, pauliMat (σ i) (x i) (y i) *
          ((U i : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0 *
            star ((U i : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0)) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pauliString,
        prodStateDensity, Matrix.of_apply, Finset.prod_mul_distrib]
    _ = ∏ i, g1 (σ i) (U i) := by
      simp only [g1, Fintype.prod_sum]
    _ = _ := by simp only [g1_real, Complex.ofReal_prod]

private lemma trace_pauliObservable (n : ℕ) (lam : (Fin n → Pauli) → ℝ)
    (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :
    ((pauliObservable n lam * prodStateDensity n U).trace).re =
      ∑ σ, lam σ * ∏ i, f1 (σ i) (U i) := by
  simp only [pauliObservable, Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, trace_pauliString, smul_eq_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re]

private lemma integral_f1 (P : Pauli) :
    MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (f1 P) =
      if P = Pauli.I then 1 else 0 := by
  have hint (a b : Fin 2) := (haarIntegrable_entryPair (Fin 2) 0 0 b a).const_mul
    (pauliMat P a b)
  have hg : MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (g1 P) =
      ∑ a : Fin 2, ∑ b : Fin 2, pauliMat P a b *
        ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) b a := by
    unfold g1
    rw [MeasureTheory.integral_finsetSum _ (fun a _ =>
      MeasureTheory.integrable_finsetSum _ fun b _ => hint a b)]
    congr 1
    funext a
    rw [MeasureTheory.integral_finsetSum _ (fun b _ => hint a b)]
    simp only [MeasureTheory.integral_const_mul, eq205_haar_one_copy]
  change MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (fun V => (g1 P V).re) = _
  have hreal : MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (fun V => (g1 P V).re) =
      (MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (g1 P)).re :=
    integral_re (𝕜 := ℂ) (integrable_g1 P)
  rw [hreal, hg]
  cases P <;> norm_num [pauliMat, Fin.sum_univ_two, Matrix.smul_apply]

private lemma integral_entry_four (a b c d : Fin 2) :
    MeasureTheory.integral (haarUnitaryGroup (Fin 2))
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ((V : Matrix (Fin 2) (Fin 2) ℂ) b 0 * (V : Matrix (Fin 2) (Fin 2) ℂ) d 0) *
          star ((V : Matrix (Fin 2) (Fin 2) ℂ) a 0 *
            (V : Matrix (Fin 2) (Fin 2) ℂ) c 0)) =
      (1 / 6 : ℂ) * ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (b, d) (a, c) +
        swapOp (Fin 2) (b, d) (a, c)) := by
  calc
    _ = haarKroneckerAverage
        (Matrix.single ((0, 0) : Fin 2 × Fin 2) ((0, 0) : Fin 2 × Fin 2) (1 : ℂ))
        (b, d) (a, c) := by
      unfold haarKroneckerAverage
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun V => by
        exact (conj_single_apply (unitaryKronecker V) (0, 0) (0, 0) (b, d) (a, c)).symm
    _ = _ := by
      rw [eq206_haar_two_copy]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add]

private lemma integral_f1_mul (P Q : Pauli) :
    MeasureTheory.integral (haarUnitaryGroup (Fin 2)) (fun V => f1 P V * f1 Q V) =
      if P = Q then (if P = Pauli.I then 1 else 1 / 3) else 0 := by
  have hexpand (V : Matrix.unitaryGroup (Fin 2) ℂ) :
      g1 P V * g1 Q V = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        (pauliMat P a b * pauliMat Q c d) *
          (((V : Matrix (Fin 2) (Fin 2) ℂ) b 0 * (V : Matrix (Fin 2) (Fin 2) ℂ) d 0) *
            star ((V : Matrix (Fin 2) (Fin 2) ℂ) a 0 *
              (V : Matrix (Fin 2) (Fin 2) ℂ) c 0)) := by
    unfold g1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [star_mul]
    ring
  have hint (a b c d : Fin 2) : MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (pauliMat P a b * pauliMat Q c d) *
          (((V : Matrix (Fin 2) (Fin 2) ℂ) b 0 * (V : Matrix (Fin 2) (Fin 2) ℂ) d 0) *
            star ((V : Matrix (Fin 2) (Fin 2) ℂ) a 0 *
              (V : Matrix (Fin 2) (Fin 2) ℂ) c 0))) (haarUnitaryGroup (Fin 2)) :=
    (continuous_const.mul (((continuous_entry b 0).mul (continuous_entry d 0)).mul
      ((continuous_entry a 0).mul (continuous_entry c 0)).star)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hg : MeasureTheory.integral (haarUnitaryGroup (Fin 2))
      (fun V => g1 P V * g1 Q V) =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        (pauliMat P a b * pauliMat Q c d) * ((1 / 6 : ℂ) *
          ((1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (b, d) (a, c) +
            swapOp (Fin 2) (b, d) (a, c))) := by
    simp_rw [hexpand]
    rw [MeasureTheory.integral_finsetSum _ (fun a _ =>
      MeasureTheory.integrable_finsetSum _ fun b _ =>
        MeasureTheory.integrable_finsetSum _ fun c _ =>
          MeasureTheory.integrable_finsetSum _ fun d _ => hint a b c d)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun b _ =>
      MeasureTheory.integrable_finsetSum _ fun c _ =>
        MeasureTheory.integrable_finsetSum _ fun d _ => hint a b c d)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun c _ =>
      MeasureTheory.integrable_finsetSum _ fun d _ => hint a b c d)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun d _ => hint a b c d)]
    simp only [MeasureTheory.integral_const_mul, integral_entry_four]
  simp_rw [g1_real, ← Complex.ofReal_mul] at hg
  rw [integral_complex_ofReal] at hg
  have hr := congrArg Complex.re hg
  simp only [Complex.ofReal_re] at hr
  rw [hr]
  cases P <;> cases Q <;>
    norm_num [pauliMat, Fin.sum_univ_two, swapOp, permMatrix, Matrix.of_apply]

private lemma integrable_prod_f1 (n : ℕ) (σ : Fin n → Pauli) :
    MeasureTheory.Integrable
      (fun U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => ∏ i, f1 (σ i) (U i))
      (prodHaarMeasure n) :=
  MeasureTheory.Integrable.fintype_prod
    (μ := fun _ : Fin n => haarUnitaryGroup (Fin 2))
    (f := fun i => f1 (σ i))
    (fun i => (continuous_f1 (σ i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private lemma integrable_prod_f1_mul (n : ℕ) (σ τ : Fin n → Pauli) :
    MeasureTheory.Integrable
      (fun U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
        ∏ i, (f1 (σ i) (U i) * f1 (τ i) (U i))) (prodHaarMeasure n) := by
  exact MeasureTheory.Integrable.fintype_prod
    (μ := fun _ : Fin n => haarUnitaryGroup (Fin 2))
    (f := fun i V => f1 (σ i) V * f1 (τ i) V)
    (fun i => ((continuous_f1 (σ i)).mul (continuous_f1 (τ i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private lemma integral_prod_f1 (n : ℕ) (σ : Fin n → Pauli) :
    MeasureTheory.integral (prodHaarMeasure n)
      (fun U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => ∏ i, f1 (σ i) (U i)) =
      if σ = (fun _ => Pauli.I) then 1 else 0 := by
  rw [prodHaarMeasure, MeasureTheory.integral_fintype_prod_eq_prod (fun i => f1 (σ i))]
  simp only [integral_f1, Fintype.prod_ite_zero, Finset.prod_const_one]
  simp only [funext_iff]

private lemma integral_prod_f1_mul (n : ℕ) (σ τ : Fin n → Pauli) :
    MeasureTheory.integral (prodHaarMeasure n)
      (fun U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
        ∏ i, (f1 (σ i) (U i) * f1 (τ i) (U i))) =
      if σ = τ then (1 / 3 : ℝ) ^ pauliWeight n σ else 0 := by
  rw [prodHaarMeasure, MeasureTheory.integral_fintype_prod_eq_prod
    (fun i V => f1 (σ i) V * f1 (τ i) V)]
  simp only [integral_f1_mul, Fintype.prod_ite_zero]
  have hw : (∏ i : Fin n, if σ i = Pauli.I then (1 : ℝ) else 1 / 3) =
      (1 / 3 : ℝ) ^ pauliWeight n σ := by
    simp only [pauliWeight, pauliSupport, ← Finset.prod_const]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : σ i = Pauli.I <;> simp [hi]
  rw [hw]
  by_cases h : ∀ i, σ i = τ i <;> simp only [funext_iff, h, ↓reduceIte]

private lemma pauliExpectation_eq (n : ℕ) (lam : (Fin n → Pauli) → ℝ) :
    pauliExpectation n lam = lam (fun _ => Pauli.I) := by
  unfold pauliExpectation
  simp_rw [trace_pauliObservable]
  rw [MeasureTheory.integral_finsetSum _ (fun σ _ =>
    (integrable_prod_f1 n σ).const_mul (lam σ))]
  simp only [MeasureTheory.integral_const_mul, integral_prod_f1]
  simp

private lemma pauli_second_moment (n : ℕ) (lam : (Fin n → Pauli) → ℝ) :
    MeasureTheory.integral (prodHaarMeasure n)
      (fun U => ((pauliObservable n lam * prodStateDensity n U).trace).re ^ 2) =
      ∑ σ : Fin n → Pauli, (lam σ) ^ 2 * (1 / 3 : ℝ) ^ pauliWeight n σ := by
  have hexpand (U : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) :
      ((pauliObservable n lam * prodStateDensity n U).trace).re ^ 2 =
      ∑ σ : Fin n → Pauli, ∑ τ : Fin n → Pauli,
        (lam σ * lam τ) * ∏ i, (f1 (σ i) (U i) * f1 (τ i) (U i)) := by
    rw [trace_pauliObservable, pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hexpand]
  rw [MeasureTheory.integral_finsetSum _ (fun σ _ =>
    MeasureTheory.integrable_finsetSum _ fun τ _ =>
      (integrable_prod_f1_mul n σ τ).const_mul (lam σ * lam τ))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun τ _ =>
    (integrable_prod_f1_mul n σ τ).const_mul (lam σ * lam τ))]
  simp only [MeasureTheory.integral_const_mul, integral_prod_f1_mul]
  simp [← pow_two]

/-- **Lemma 1, Eq. (210)**: variance of `O = ∑_σ λ_σ σ` over single-qubit
Haar-random product states. -/
theorem lemma1_pauli_variance_of_product_states (n : ℕ) (lam : (Fin n → Pauli) → ℝ) :
    pauliVar n lam
      = ∑ σ : Fin n → Pauli,
          if σ = fun _ => Pauli.I then 0
          else (lam σ) ^ 2 / (3 : ℝ) ^ pauliWeight n σ := by
  classical
  rw [pauliVar, pauli_second_moment, pauliExpectation_eq]
  have hw : pauliWeight n (fun _ => Pauli.I) = 0 := by
    simp [pauliWeight, pauliSupport]
  have hsum : (∑ σ : Fin n → Pauli,
      if σ = (fun _ => Pauli.I) then (lam σ) ^ 2 else 0) =
      (lam (fun _ => Pauli.I)) ^ 2 := by simp
  rw [← hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : σ = (fun _ => Pauli.I)
  · subst σ
    simp [hw]
  · simp [hσ, div_eq_mul_inv]

end

end Qatlib.Papers.Trainability23.HaarAverages.Moments
