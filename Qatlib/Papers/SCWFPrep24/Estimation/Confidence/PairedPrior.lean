/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PairInformation
import Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
import Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Paired Prior

Both hypotheses average the actual original complete input over one fixed sign field and one fixed local phase field.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder
open scoped Classical BigOperators Matrix
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

/-- Both hypotheses average the actual original complete input over one fixed sign field and one fixed local phase field. -/
def physicalPrior {E : Type*} [Fintype E] [DecidableEq E] (b ρ : ℝ) (Q : ℕ) :
    Matrix (Fin Q → (E × Bool) × Bool) (Fin Q → (E × Bool) × Bool) ℂ :=
  fun z w => ∑ κ : E → Fin 4,(pairedSignLaw ρ κ : ℂ)*
    phaseMean Q (fun ω => originalSuppliedCopies (pairedWeakSpin b κ) Q ω z*
      star (originalSuppliedCopies (pairedWeakSpin b κ) Q ω w))

/-- Conjugating a literal pure density transports the same complete unknown vector. -/
theorem conjugate_pure {I O : Type*} [Fintype I] (K : Matrix O I ℂ) (v : I → ℂ) :
    K*outerProduct v*K.conjTranspose=outerProduct (K*ᵥv) := by
  change K*Matrix.vecMulVec v (fun i => star (v i))*K.conjTranspose=
    Matrix.vecMulVec (K*ᵥv) (fun i => star ((K*ᵥv) i))
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul]
  congr 1
  funext j
  simp [Matrix.vecMul,Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,mul_comm]

/-- Averaging the exact coherent lift reproduces the complete original shared-phase and fixed-sign prior. -/
theorem physicalPrior_isometric {E : Type*} [Fintype E] [DecidableEq E] (b ρ : ℝ) (Q : ℕ) :
    physicalPrior (E := E) b ρ Q=
      ∑ y : Fin Q → E × Bool,(1/(Fintype.card (E × Bool) : ℂ)^Q) •
        (fullOrbitMatrix y*conditionalDensity b y ρ*(fullOrbitMatrix y).conjTranspose) := by
  have he (y : Fin Q → E × Bool) :
      fullOrbitMatrix y*conditionalDensity b y ρ*(fullOrbitMatrix y).conjTranspose=
        ∑ κ : E → Fin 4,(pairedSignLaw ρ κ : ℂ) •
          outerProduct (fullOrbitMatrix y*ᵥ(fun s : Fin Q → Bool =>
            copyAmplitude (pairedWeakSpin b κ) Q (fun j => (y j,s j)))) := by
    simp only [conditionalDensity,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
      conjugate_pure]
  ext z w
  simp only [physicalPrior,original_input_count_lift_entry,he,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,outerProduct,Matrix.of_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro κ _
  simp only [Complex.star_def]
  ring

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput

open scoped ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift
open Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The literal full prior is a positive trace-one matrix, derived from its same physical conditional inputs and exact address law. -/
theorem physicalPrior_legal {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (b ρ : ℝ) (Q : ℕ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1) :
    (physicalPrior (E := E) b ρ Q).PosSemidef ∧ (physicalPrior (E := E) b ρ Q).trace=1 := by
  let p := uniformCopyLaw (E × Bool) Q
  have hw (y : Fin Q → E × Bool) : (1/(Fintype.card (E × Bool) : ℂ)^Q)=(p.prob y : ℂ) := by
    rw [uniformCopyLaw_prob]
    push_cast
    rfl
  have heq : physicalPrior (E := E) b ρ Q=
      ∑ y : Fin Q → E × Bool,(p.prob y : ℂ) •
        (fullOrbitMatrix y*conditionalDensity b y ρ*(fullOrbitMatrix y).conjTranspose) := by
    rw [physicalPrior_isometric]
    apply Finset.sum_congr rfl
    intro y _
    rw [hw y]
  rw [heq]
  constructor
  · apply Matrix.posSemidef_sum
    intro y _
    exact ((conditionalDensity_legal b hb0 hb1 y ρ hlo hhi).1.mul_mul_conjTranspose_same
      (fullOrbitMatrix y)).smul (by exact_mod_cast p.nonneg y)
  · have ht (y : Fin Q → E × Bool) :
        (fullOrbitMatrix y*conditionalDensity b y ρ*(fullOrbitMatrix y).conjTranspose).trace=1 := by
      rw [Matrix.trace_mul_comm _ (fullOrbitMatrix y).conjTranspose]
      rw [←Matrix.mul_assoc,fullOrbitMatrix_isometry,Matrix.one_mul]
      exact (conditionalDensity_legal b hb0 hb1 y ρ hlo hhi).2
    simp only [Matrix.trace_sum,Matrix.trace_smul,ht,smul_eq_mul,mul_one]
    exact_mod_cast p.sum_one

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture

/-- Actual optimized pair purifications give full-register conditional amplitudes and their genuine fidelity product, without an input overlap certificate. -/
theorem exists_actual_conditional_amplitudes {E : Type} [Fintype E] [DecidableEq E]
    {Q : ℕ} (N : ℕ) (hN : 256≤N) (y : Fin Q → E × Bool) :
    ∃ X Z : Matrix (Fin Q → Bool) (E → Fin (Fintype.card (Fin Q → Bool))) ℂ,
      X*X.conjTranspose=conditionalDensity (128/((N : ℝ)^2)) y (3/4) ∧
      Z*Z.conjTranspose=conditionalDensity (128/((N : ℝ)^2)) y (-3/4) ∧
      ‖(X.conjTranspose*Z).trace‖=actualPairProduct N y := by
  let J (e : E) := Fin (Fintype.card (PairBasis (multiplicity y (e,false)) (multiplicity y (e,true))))
  let C := Fin (Fintype.card (Fin Q → Bool))
  have h (e : E) : ∃ ψ φ : QState (J e × C),
      IsPurification ψ (physicalPairMixture (128/((N : ℝ)^2))
        (multiplicity y (e,false)) (multiplicity y (e,true)) (3/4)) ∧
      IsPurification φ (physicalPairMixture (128/((N : ℝ)^2))
        (multiplicity y (e,false)) (multiplicity y (e,true)) (-3/4)) ∧
      ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖=
        Froot (physicalPairMixture (128/((N : ℝ)^2))
          (multiplicity y (e,false)) (multiplicity y (e,true)) (3/4))
        (physicalPairMixture (128/((N : ℝ)^2))
          (multiplicity y (e,false)) (multiplicity y (e,true)) (-3/4)) := by
    exact (g2 _ _ (pair_dimension_le_whole y e) _ _
      (original_pair_density N _ _ hN (3/4) (by norm_num) (by norm_num))
      (original_pair_density N _ _ hN (-3/4) (by norm_num) (by norm_num))).2
  choose ψ φ hψ hφ hf using h
  let A (e : E) : Matrix (J e) C ℂ := fun i j => ψ e (i,j)
  let B (e : E) : Matrix (J e) C ℂ := fun i j => φ e (i,j)
  have hA (e : E) : A e*(A e).conjTranspose=physicalPairMixture (128/((N : ℝ)^2))
      (multiplicity y (e,false)) (multiplicity y (e,true)) (3/4) := (hψ e).2
  have hB (e : E) : B e*(B e).conjTranspose=physicalPairMixture (128/((N : ℝ)^2))
      (multiplicity y (e,false)) (multiplicity y (e,true)) (-3/4) := (hφ e).2
  have hi (e : E) : Qatlib.Foundations.PureStateMath.Inner (ψ e) (φ e)=
      ((A e).conjTranspose*B e).trace := by
    simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply,
      Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,A,B]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  refine ⟨tensorAmplitude (pairCoordinates y) A,tensorAmplitude (pairCoordinates y) B,?_,?_,?_⟩
  · ext s t
    rw [tensorAmplitude_gram (pairCoordinates y) A s t]
    simp_rw [hA]
    exact (conditionalDensity_entry (128/((N : ℝ)^2)) y (3/4) s t).symm
  · ext s t
    rw [tensorAmplitude_gram (pairCoordinates y) B s t]
    simp_rw [hB]
    exact (conditionalDensity_entry (128/((N : ℝ)^2)) y (-3/4) s t).symm
  · rw [tensorAmplitude_overlap (pairCoordinates y) A B,norm_prod]
    apply Finset.prod_congr rfl
    intro e _
    rw [←hi e]
    exact hf e

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
open Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
open Qatlib.Concepts.MixedFidelity.FidelityMetric.IsometricMixture
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The full environment is derived from complete basis equivalences and actual nonempty pair factors. -/
theorem whole_environment_dimension {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (Q : ℕ) :
    Fintype.card (Fin Q → (E × Bool) × Bool)≤
      Fintype.card ((Fin Q → E × Bool) × (E → Fin (Fintype.card (Fin Q → Bool)))) := by
  calc
    _ = Fintype.card (Fin Q → E × Bool)*Fintype.card (Fin Q → Bool) := by
      rw [←Fintype.card_prod]
      exact Fintype.card_congr (Equiv.arrowProdEquivProdArrow (Fin Q) (fun _ => E × Bool) (fun _ => Bool))
    _ ≤ Fintype.card (Fin Q → E × Bool)*
        Fintype.card (E → Fin (Fintype.card (Fin Q → Bool))) :=
      Nat.mul_le_mul_left _ (product_environment_card Q)
    _ = _ := by rw [Fintype.card_prod]

/-- The original complete two-hypothesis priors have actual purifications whose overlap is the true address average of genuine pair fidelities. -/
theorem exists_actual_whole_amplitudes {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (N Q : ℕ) (hN : 256≤N) :
    ∃ A B : Matrix (Fin Q → (E × Bool) × Bool)
      ((Fin Q → E × Bool) × (E → Fin (Fintype.card (Fin Q → Bool)))) ℂ,
      A*A.conjTranspose=physicalPrior (128/((N : ℝ)^2)) (3/4) Q ∧
      B*B.conjTranspose=physicalPrior (128/((N : ℝ)^2)) (-3/4) Q ∧
      (A.conjTranspose*B).trace=
        ((uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N) : ℂ) := by
  let p := uniformCopyLaw (E × Bool) Q
  have hc (y : Fin Q → E × Bool) := exists_actual_conditional_amplitudes N hN y
  choose X Z hX hZ hnorm using hc
  let W (y : Fin Q → E × Bool) := overlapPhase (((X y).conjTranspose*Z y).trace) • Z y
  have hW (y : Fin Q → E × Bool) : W y*(W y).conjTranspose=
      conditionalDensity (128/((N : ℝ)^2)) y (-3/4) :=
    (aligned_amplitude (X y) (Z y)).1.trans (hZ y)
  have hO (y : Fin Q → E × Bool) : ((X y).conjTranspose*W y).trace=(actualPairProduct N y : ℂ) := by
    change ((X y).conjTranspose*(overlapPhase (((X y).conjTranspose*Z y).trace) • Z y)).trace=_
    rw [(aligned_amplitude (X y) (Z y)).2,hnorm y]
  have hw (y : Fin Q → E × Bool) : (p.prob y : ℂ)=1/(Fintype.card (E × Bool) : ℂ)^Q := by
    rw [uniformCopyLaw_prob]
    push_cast
    rfl
  have hm (ρ : ℝ) : physicalPrior (E := E) (128/((N : ℝ)^2)) ρ Q=
      ∑ y : Fin Q → E × Bool,(p.prob y : ℂ) •
        (fullOrbitMatrix y*conditionalDensity (128/((N : ℝ)^2)) y ρ*(fullOrbitMatrix y).conjTranspose) := by
    rw [physicalPrior_isometric]
    apply Finset.sum_congr rfl
    intro y _
    rw [hw y]
  refine ⟨amplitude p.prob fullOrbitMatrix X,amplitude p.prob fullOrbitMatrix W,?_,?_,?_⟩
  · rw [amplitude_gram p.prob p.nonneg fullOrbitMatrix X]
    simp_rw [hX]
    exact (hm (3/4)).symm
  · rw [amplitude_gram p.prob p.nonneg fullOrbitMatrix W]
    simp_rw [hW]
    exact (hm (-3/4)).symm
  · rw [amplitude_overlap p.prob p.nonneg fullOrbitMatrix fullOrbitMatrix_isometry X W]
    simp_rw [hO]
    simp only [p,FinDist.expect,Complex.ofReal_sum,Complex.ofReal_mul]

open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- The original complete physical prior in one fixed known finite basis, without discarding any coordinate. -/
def encodedPhysicalPrior {E : Type} [Fintype E] [DecidableEq E] (b ρ : ℝ) (Q : ℕ) :
    Qatlib.Foundations.PureStateMath.Operator (Fintype.card (Fin Q → (E × Bool) × Bool)) :=
  (physicalPrior (E := E) b ρ Q).submatrix
    (Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm
    (Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm

/-- The complete original quantum input retains at least the true mean of actual conditional pair fidelities. -/
theorem original_weak_full_froot_mean {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (N Q : ℕ) (hN : 256≤N) :
    (uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N)≤
      Froot (encodedPhysicalPrior (E := E) (128/((N : ℝ)^2)) (3/4) Q)
        (encodedPhysicalPrior (E := E) (128/((N : ℝ)^2)) (-3/4) Q) := by
  have hb := original_weak_excitation N hN
  have hb1 : 128/((N : ℝ)^2)≤1 := hb.2.trans (by norm_num)
  have hp := physicalPrior_legal (E := E) (128/((N : ℝ)^2)) (3/4) Q hb.1 hb1 (by norm_num) (by norm_num)
  have hq := physicalPrior_legal (E := E) (128/((N : ℝ)^2)) (-3/4) Q hb.1 hb1 (by norm_num) (by norm_num)
  have hn : 0≤(uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N) :=
    (Real.exp_pos _).le.trans (actualPairProduct_expect_exp (E := E) N Q hN)
  obtain ⟨A,B,hA,hB,hO⟩ := exists_actual_whole_amplitudes (E := E) N Q hN
  have hnorm : ‖(A.conjTranspose*B).trace‖=(uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N) := by
    rw [hO,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  have hf := finite_purification_lower
    (R := Fin Q → (E × Bool) × Bool)
    (C := (Fin Q → E × Bool) × (E → Fin (Fintype.card (Fin Q → Bool))))
    (whole_environment_dimension (E := E) Q)
    (physicalPrior (E := E) (128/((N : ℝ)^2)) (3/4) Q)
    (physicalPrior (E := E) (128/((N : ℝ)^2)) (-3/4) Q) hp.2 hq.2 A B hA hB
  exact hnorm.symm.le.trans hf

/-- The exact original shared-phase weak-input priors satisfy the source's full squared-fidelity exponent for every actual copy budget, including zero and one. -/
theorem original_weak_full_fidelity {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (N Q : ℕ) (hN : 256≤N) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/(Fintype.card (E × Bool) : ℝ)))≤
    (Froot (encodedPhysicalPrior (E := E) (128/((N : ℝ)^2)) (3/4) Q)
      (encodedPhysicalPrior (E := E) (128/((N : ℝ)^2)) (-3/4) Q))^2 := by
  have hn : 0≤(uniformCopyLaw (E × Bool) Q).expect (actualPairProduct N) :=
    (Real.exp_pos _).le.trans (actualPairProduct_expect_exp (E := E) N Q hN)
  exact (actualPairProduct_squared_scale (E := E) N Q hN).trans
    (pow_le_pow_left₀ hn (original_weak_full_froot_mean (E := E) N Q hN) 2)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
