/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.EffectFrames
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PauliStates
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.BornMoments

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Priors

The literal coefficient of a complete-address effect row against one fixed null spin frame.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The literal coefficient of a complete-address effect row against one fixed null spin frame. -/
def nullCoefficients {A : Type*} (parity : A → Bool)
    (a : A → Fin 2 → ℂ) (axis : Fin 3) (sign : Bool) (x : A) : ℂ :=
  ∑ i, a x i*sixPauliState axis (sign ^^ parity x) i

/-- The literal coefficient against an arbitrary pointwise normalized spin field. -/
def fieldCoefficients {A : Type*} (v a : A → Fin 2 → ℂ) (x : A) : ℂ := ∑ i, a x i*v x i

/-- Complete squared row norm, including all coherent address blocks. -/
def rowEnergy {A : Type*} [Fintype A] (a : A → Fin 2 → ℂ) : ℝ :=
  ∑ x, ∑ i, Complex.normSq (a x i)

/-- The six literal vectors realize the canonical Hermitian prior densities. -/
theorem sixPauliState_density (axis : Fin 3) (sign : Bool) :
    rowEffect (star (sixPauliState axis sign)) = pauliPriorDensity axis sign := by
  apply HermitianMat.ext
  simp only [rowEffect, HermitianMat.mat_mk, star_star, pauliPriorDensity]
  exact sixPauliState_projector axis sign

/-- The actual coefficient energy equals the null spin effect evaluated in the actual shared Pauli frame. -/
theorem nullCoefficients_energy {A : Type*} [Fintype A] (parity : A → Bool)
    (a : A → Fin 2 → ℂ) (axis : Fin 3) (sign : Bool) :
    (∑ x, Complex.normSq (nullCoefficients parity a axis sign x)) =
      inner ℝ (pauliPriorDensity axis sign) (nullSpinEffect parity a) := by
  rw [nullSpinEffect, inner_sum]
  apply Finset.sum_congr rfl
  intro x _
  unfold nullCoefficients
  rw [← rowEffect_eval_vector, sixPauliState_density]
  cases parity x
  · simp only [Bool.xor_false, Bool.false_eq_true, ite_false]
  · simp only [Bool.xor_true, ite_true]
    rw [qubitTraceComplement_pauli_duality]

/-- The null prior average retains one shared phase assignment for both actual full-address amplitudes. -/
def nullProductNumerator {A : Type*} [Fintype A] (parity : A → Bool)
    (a b : A → Fin 2 → ℂ) : ℝ :=
  (∑ axis : Fin 3, ∑ sign : Bool,
    phaseMeanReal (fun ω => Complex.normSq (phaseAmplitude (nullCoefficients parity a axis sign) ω)*
      Complex.normSq (phaseAmplitude (nullCoefficients parity b axis sign) ω)))/6

/-- The alternative prior uses the same fourth-root phase once per address and shares it between copies. -/
def fieldProductNumerator {A : Type*} [Fintype A] (v a b : A → Fin 2 → ℂ) : ℝ :=
  phaseMeanReal (fun ω => Complex.normSq (phaseAmplitude (fieldCoefficients v a) ω)*
    Complex.normSq (phaseAmplitude (fieldCoefficients v b) ω))

/-- The actual null full-address product average dominates the full row trace product by one twelfth. -/
theorem nullProductNumerator_lower {A : Type*} [Fintype A] [DecidableEq A]
    (parity : A → Bool) (a b : A → Fin 2 → ℂ) :
    rowEnergy a*rowEnergy b/12 ≤ nullProductNumerator parity a b := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun axis _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Bool)) (fun sign _ =>
      phaseMeanReal_product_lower (nullCoefficients parity a axis sign)
        (nullCoefficients parity b axis sign)))
  simp_rw [nullCoefficients_energy, ← Finset.sum_div] at hs
  have ht := nullSpinEffect_six_moment parity a b
  unfold rowEnergy nullProductNumerator
  linarith

/-- The actual amplitude coefficient at every address obeys the complete row norm bound. -/
theorem fieldCoefficients_normSq_le {A : Type*} (v a : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1) (x : A) :
    Complex.normSq (fieldCoefficients v a x) ≤ ∑ i, Complex.normSq (a x i) := by
  have h := overlap_normSq_le_energy_product (a x) (star (v x))
  simpa only [fieldCoefficients, Pi.star_apply, star_star, Complex.star_def, Complex.conj_conj,
    Complex.normSq_conj, hv, mul_one] using h

/-- Every normalized spin field obeys the two-product upper bound under the actual shared-phase prior. -/
theorem fieldProductNumerator_upper {A : Type*} [Fintype A] [DecidableEq A]
    (v a b : A → Fin 2 → ℂ) (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1) :
    fieldProductNumerator v a b ≤ 2*rowEnergy a*rowEnergy b := by
  have ha : (∑ x, Complex.normSq (fieldCoefficients v a x)) ≤ rowEnergy a :=
    Finset.sum_le_sum fun x _ => fieldCoefficients_normSq_le v a hv x
  have hb : (∑ x, Complex.normSq (fieldCoefficients v b x)) ≤ rowEnergy b :=
    Finset.sum_le_sum fun x _ => fieldCoefficients_normSq_le v b hv x
  have hz : 0 ≤ ∑ x, Complex.normSq (fieldCoefficients v b x) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hrow : 0 ≤ rowEnergy a := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hm := mul_le_mul ha hb hz hrow
  have hu := phaseMeanReal_product_upper (fieldCoefficients v a) (fieldCoefficients v b)
  unfold fieldProductNumerator
  nlinarith

/-- The factor 24 follows from the actual finite physical phase/Pauli averages for arbitrary coherent full-address rank-one product effects. -/
theorem actual_rank_one_prior_domination {A : Type*} [Fintype A] [DecidableEq A]
    (parity : A → Bool) (v a b : A → Fin 2 → ℂ)
    (hv : ∀ x, ∑ i, Complex.normSq (v x i) = 1) :
    fieldProductNumerator v a b ≤ 24*nullProductNumerator parity a b := by
  have hl := nullProductNumerator_lower parity a b
  have hu := fieldProductNumerator_upper v a b hv
  linarith

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
