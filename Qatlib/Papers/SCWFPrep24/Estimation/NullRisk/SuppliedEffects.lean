/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.GramEffects
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PhysicalPriors
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.GridParity

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Supplied Effects

The actual supplied full-register vector retains the common hidden phase and the original 1/sqrt(M) normalization.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
open Matrix
open Qatlib.Concepts.SpinorSampling.Model
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The actual supplied full-register vector retains the common hidden phase and the original 1/sqrt(M) normalization. -/
def phasedFieldState {A : Type*} [Fintype A] (v : A → Fin 2 → ℂ)
    (ω : A → Fin 4) (z : A × Fin 2) : ℂ :=
  fourthPhase (ω z.1)*v z.1 z.2/(Real.sqrt (Fintype.card A : ℝ) : ℂ)

/-- The same physical field in the original source's Bool spin coordinates. -/
def phasedFieldSpinor {A : Type*} (v : A → Fin 2 → ℂ) (ω : A → Fin 4)
    (x : A) (spin : Bool) : ℂ := fourthPhase (ω x)*v x (boolEquivFin2 spin)

/-- The full-register vector is exactly the original suppliedSpinState after the fixed spin-label equivalence. -/
theorem phasedFieldState_original {A : Type*} [Fintype A] (v : A → Fin 2 → ℂ)
    (ω : A → Fin 4) (z : A × Fin 2) :
    phasedFieldState v ω z = suppliedSpinState (real0 (phasedFieldSpinor v ω))
      (imag0 (phasedFieldSpinor v ω)) (real1 (phasedFieldSpinor v ω))
      (imag1 (phasedFieldSpinor v ω)) (boolEquivFin2.symm z.2) z.1 := by
  rw [suppliedSpinState, complexSpinor_parts]
  simp only [phasedFieldState, phasedFieldSpinor, Equiv.apply_symm_apply]

/-- Every hidden-phase realization is an actual normalized supplied state when each point spinor is normalized. -/
theorem phasedFieldState_normalized {A : Type*} [Fintype A] [Nonempty A]
    (v : A → Fin 2 → ℂ) (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1)
    (ω : A → Fin 4) : Normalized (phasedFieldState v ω) := by
  have hM : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hden : Complex.normSq (Real.sqrt (Fintype.card A : ℝ) : ℂ) =
      (Fintype.card A : ℝ) := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp only [Normalized, Complex.sq_norm, phasedFieldState, Complex.normSq_div,
    Complex.normSq_mul, fourthPhase_normSq, one_mul, hden, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_div, hv]
  simp [nsmul_eq_mul, hM]

/-- A complete-address row of a genuine full-register matrix, without measuring or fixing the unknown address. -/
def fullRowBlock {A R : Type*} (B : Matrix R (A × Fin 2) ℂ) (row : R)
    (x : A) (i : Fin 2) : ℂ := B row (x,i)

/-- The actual coherent full-register row amplitude is the already proved shared-phase amplitude with the same source normalization. -/
theorem phasedFieldState_row_amplitude {A R : Type*} [Fintype A]
    (B : Matrix R (A × Fin 2) ℂ) (row : R) (v : A → Fin 2 → ℂ) (ω : A → Fin 4) :
    (∑ z, B row z*phasedFieldState v ω z) =
      phaseAmplitude (fieldCoefficients v (fullRowBlock B row)) ω /
        (Real.sqrt (Fintype.card A : ℝ) : ℂ) := by
  simp only [phasedFieldState, phaseAmplitude, fieldCoefficients, fullRowBlock,
    Fintype.sum_prod_type, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual positive-effect Born weight is the finite sum of normalized coherent row amplitudes; the Gram factor is constructed, not assumed. -/
theorem phasedFieldState_effectWeight {A : Type*} [Fintype A] [DecidableEq A]
    (E : HermitianMat (A × Fin 2) ℂ) (hE : 0 ≤ E)
    (v : A → Fin 2 → ℂ) (ω : A → Fin 4) :
    effectWeight E (phasedFieldState v ω) =
      (∑ row, Complex.normSq (phaseAmplitude
        (fieldCoefficients v (fullRowBlock (psdGramFactor E) row)) ω))/(Fintype.card A : ℝ) := by
  have hden : Complex.normSq (Real.sqrt (Fintype.card A : ℝ) : ℂ) =
      (Fintype.card A : ℝ) := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [effectWeight_eq_gram_rows E hE]
  simp_rw [phasedFieldState_row_amplitude, Complex.normSq_div, hden]
  rw [Finset.sum_div]

/-- The actual real phase average commutes with every finite effect-row sum. -/
theorem phaseMeanReal_sum {A R : Type*} [Fintype A] [Fintype R]
    (f : R → (A → Fin 4) → ℝ) :
    phaseMeanReal (fun ω => ∑ r, f r ω) = ∑ r, phaseMeanReal (f r) := by
  unfold phaseMeanReal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The fixed source normalization factors out of the actual real phase average, including zero denominators by the field convention. -/
theorem phaseMeanReal_div {A : Type*} [Fintype A]
    (f : (A → Fin 4) → ℝ) (c : ℝ) :
    phaseMeanReal (fun ω => f ω/c) = phaseMeanReal f/c := by
  unfold phaseMeanReal
  simp only [mul_div_assoc, Finset.sum_div]

/-- The two-copy effect weight uses the same actual supplied state in both factors. -/
def fieldProductWeight {A : Type*} [Fintype A]
    (E F : HermitianMat (A × Fin 2) ℂ) (v : A → Fin 2 → ℂ) : ℝ :=
  phaseMeanReal (fun ω => effectWeight E (phasedFieldState v ω)*
    effectWeight F (phasedFieldState v ω))

/-- The actual null spin field uses one common Pauli frame on the whole periodic input. -/
def nullField {A : Type*} (parity : A → Bool) (axis : Fin 3) (sign : Bool)
    (x : A) (i : Fin 2) : ℂ := sixPauliState axis (sign ^^ parity x) i

/-- The full-register null effect prior averages its six actual spin frames and the actual shared local phases. -/
def nullProductWeight {A : Type*} [Fintype A]
    (E F : HermitianMat (A × Fin 2) ℂ) (parity : A → Bool) : ℝ :=
  (∑ θ : Fin 3 × Bool, fieldProductWeight E F (nullField parity θ.1 θ.2))/6

/-- Actual arbitrary positive effects decompose into the proved row-product phase numerators with the full original 1/M² scale. -/
theorem fieldProductWeight_eq_gram_priors {A : Type*} [Fintype A] [DecidableEq A]
    (E F : HermitianMat (A × Fin 2) ℂ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (v : A → Fin 2 → ℂ) :
    fieldProductWeight E F v =
      (∑ r, ∑ s, fieldProductNumerator v (fullRowBlock (psdGramFactor E) r)
        (fullRowBlock (psdGramFactor F) s))/(Fintype.card A : ℝ)^2 := by
  unfold fieldProductWeight
  simp_rw [phasedFieldState_effectWeight E hE, phasedFieldState_effectWeight F hF,
    div_mul_div_comm, ← pow_two, Finset.sum_mul_sum, Finset.sum_div,
    phaseMeanReal_sum, phaseMeanReal_div]
  rfl

/-- The complete null effect prior is exactly the row-wise actual six-frame prior, with the same source normalization. -/
theorem nullProductWeight_eq_gram_priors {A : Type*} [Fintype A] [DecidableEq A]
    (E F : HermitianMat (A × Fin 2) ℂ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (parity : A → Bool) :
    nullProductWeight E F parity =
      (∑ r, ∑ s, nullProductNumerator parity (fullRowBlock (psdGramFactor E) r)
        (fullRowBlock (psdGramFactor F) s))/(Fintype.card A : ℝ)^2 := by
  let f := fun (θ : Fin 3 × Bool) (r s : A × Fin 2) =>
    fieldProductNumerator (nullField parity θ.1 θ.2)
      (fullRowBlock (psdGramFactor E) r) (fullRowBlock (psdGramFactor F) s)
  have hswap : (∑ θ : Fin 3 × Bool, ∑ r : A × Fin 2, ∑ s : A × Fin 2, f θ r s) =
      ∑ r : A × Fin 2, ∑ s : A × Fin 2, ∑ θ : Fin 3 × Bool, f θ r s := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    exact Finset.sum_comm
  have hcoeff (axis : Fin 3) (sign : Bool) (row : A → Fin 2 → ℂ) :
      fieldCoefficients (nullField parity axis sign) row = nullCoefficients parity row axis sign := by
    funext x
    rfl
  have hsmall (r s : A × Fin 2) : (∑ θ : Fin 3 × Bool, f θ r s)/6 =
      nullProductNumerator parity (fullRowBlock (psdGramFactor E) r)
        (fullRowBlock (psdGramFactor F) s) := by
    simp only [f, Fintype.sum_prod_type, fieldProductNumerator,
      nullProductNumerator, hcoeff]
  unfold nullProductWeight
  simp_rw [fieldProductWeight_eq_gram_priors E F hE hF]
  change (∑ θ : Fin 3 × Bool, (∑ r, ∑ s, f θ r s)/(Fintype.card A : ℝ)^2)/6 = _
  rw [← Finset.sum_div, hswap]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [← hsmall]
  simp_rw [← Finset.sum_div]
  ring

/-- Every pair of arbitrary positive full-register effects obeys the actual finite physical-prior domination, with no address-first restriction or supplied factorization/likelihood bound. -/
theorem actual_positive_effect_prior_domination {A : Type*} [Fintype A] [DecidableEq A]
    (E F : HermitianMat (A × Fin 2) ℂ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (parity : A → Bool) (v : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1) :
    fieldProductWeight E F v ≤ 24*nullProductWeight E F parity := by
  rw [fieldProductWeight_eq_gram_priors E F hE hF,
    nullProductWeight_eq_gram_priors E F hE hF, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => actual_rank_one_prior_domination parity v
    (fullRowBlock (psdGramFactor E) r) (fullRowBlock (psdGramFactor F) s) hv

/-- Every finite positive sum of complete-register product effects obeys the same literal physical-prior domination. -/
theorem actual_finite_product_sum_prior_domination {A K : Type*} [Fintype A]
    [DecidableEq A] [Fintype K] (E F : K → HermitianMat (A × Fin 2) ℂ)
    (hE : ∀ k, 0 ≤ E k) (hF : ∀ k, 0 ≤ F k)
    (parity : A → Bool) (v : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1) :
    (∑ k, fieldProductWeight (E k) (F k) v) ≤
      24*(∑ k, nullProductWeight (E k) (F k) parity) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ =>
    actual_positive_effect_prior_domination (E k) (F k) (hE k) (hF k) parity v hv

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
