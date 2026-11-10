/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementGeneralLocc
import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
import Qatlib.Concepts.QuditTeleport.ResourceIff.MeasurementPatterns
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability.LoccAverageEntropy

open Qatlib
open Qatlib.Concepts.Entanglement.Separability
open Qatlib.Concepts.Entanglement.Separability
open scoped BigOperators ComplexOrder

variable {D E : ℕ}

structure TwoOutcomeInstrument (D : ℕ) where

  op0 : Operator D

  op1 : Operator D

  hcomplete : op0.conjTranspose * op0 + op1.conjTranspose * op1 = 1

def twoOutcomeOp (I : TwoOutcomeInstrument D) (i : Fin 2) : Operator D :=
  if i.val = 0 then I.op0 else I.op1

def TwoOutcomeInstrument.toKraus (I : TwoOutcomeInstrument D) : KrausInstrument D 2 where
  op := twoOutcomeOp I
  hcomplete := by
    have hsum : (∑ i, (twoOutcomeOp I i).conjTranspose * (twoOutcomeOp I i))
        = I.op0.conjTranspose * I.op0 + I.op1.conjTranspose * I.op1 := by
      rw [Fin.sum_univ_two]
      simp only [twoOutcomeOp, if_true, if_false, show (0 : Fin 2).val = 0 from rfl,
        show ¬((1 : Fin 2).val = 0) by simp]
    rw [hsum]
    exact I.hcomplete

theorem TwoOutcomeInstrument.op_eq_toKraus (I : TwoOutcomeInstrument D) (i : Fin 2) :
    I.toKraus.op i = if i.val = 0 then I.op0 else I.op1 := rfl

theorem TwoOutcomeInstrument.hcomplete_toKraus (I : TwoOutcomeInstrument D) :
    (∑ i, (I.toKraus.op i).conjTranspose * (I.toKraus.op i)) = 1 := I.toKraus.hcomplete

noncomputable def branchState (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) : QState (Fin D × Fin E) :=
  krausBranch ψ I.toKraus i

noncomputable def branchMass (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) : ℝ :=
  krausBranchMass ψ I.toKraus i

theorem branchMass_nonneg (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) : 0 ≤ branchMass I ψ i :=
  krausBranchMass_nonneg ψ I.toKraus i

theorem branchMass_sum_eq_one (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) : (∑ i, branchMass I ψ i) = 1 :=
  krausBranchMass_sum_eq_one ψ I.toKraus hψ

theorem branchMass_eq_zero_iff (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) :
    branchMass I ψ i = 0 ↔ ∀ j, branchState I ψ i j = 0 :=
  krausBranchMass_eq_zero_iff ψ I.toKraus i

theorem branchMass_eq_trace (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) :
    branchMass I ψ i = (Matrix.trace (krausBranchReduced ψ I.toKraus i)).re :=
  krausBranchMass_eq_trace ψ I.toKraus i

noncomputable def normalizedBranchState (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) (hp : 0 < branchMass I ψ i) :
    QState (Fin D × Fin E) :=
  ((Real.sqrt (branchMass I ψ i))⁻¹ : ℝ) • branchState I ψ i

theorem normalizedBranchState_normalized (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) (hp : 0 < branchMass I ψ i) :
    Normalized (normalizedBranchState I ψ i hp) := by
  have hp0 : 0 < Real.sqrt (branchMass I ψ i) := Real.sqrt_pos.2 hp
  have hnorm : (∑ j, ‖branchState I ψ i j‖ ^ 2) = branchMass I ψ i := rfl
  have hsq : ∀ j, ‖((Real.sqrt (branchMass I ψ i))⁻¹ : ℝ) • branchState I ψ i j‖ ^ 2
      = ((Real.sqrt (branchMass I ψ i))⁻¹) ^ 2 * (‖branchState I ψ i j‖ ^ 2) := by
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp0), pow_two]
    ring
  unfold Normalized normalizedBranchState
  calc (∑ j, ‖((Real.sqrt (branchMass I ψ i))⁻¹ : ℝ) • branchState I ψ i j‖ ^ 2)
      = ∑ j, ((Real.sqrt (branchMass I ψ i))⁻¹) ^ 2 * (‖branchState I ψ i j‖ ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => hsq j
    _ = ((Real.sqrt (branchMass I ψ i))⁻¹) ^ 2 * (∑ j, ‖branchState I ψ i j‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ = ((Real.sqrt (branchMass I ψ i))⁻¹) ^ 2 * branchMass I ψ i := by rw [hnorm]
    _ = 1 := by
        rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ (ne_of_gt hp)]

theorem normalizedBranchState_eq_smul (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) (hp : 0 < branchMass I ψ i) :
    normalizedBranchState I ψ i hp
      = ((Real.sqrt (branchMass I ψ i))⁻¹ : ℝ) • branchState I ψ i := rfl

noncomputable def branchEntropy (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) (hp : 0 < branchMass I ψ i) : ℝ :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy (normalizedBranchState I ψ i hp)
    (normalizedBranchState_normalized I ψ i hp)

theorem branchEntropy_eq_schmidtEntropy (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) (hp : 0 < branchMass I ψ i) :
    branchEntropy I ψ i hp
      = Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs.schmidtEntropy (normalizedBranchState I ψ i hp)
        (normalizedBranchState_normalized I ψ i hp) :=
  EntanglementLOCC.entropy_eq_schmidtEntropy _ _

theorem branchEntropy_nonneg (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E))
    (i : Fin 2) (hp : 0 < branchMass I ψ i) : 0 ≤ branchEntropy I ψ i hp :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy_nonneg _ _

theorem secondMarginal_sum_branch (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (b c : Fin E) :
    (∑ i, secondMarginalState (branchState I ψ i) b c) = secondMarginalState ψ b c := by
  have hsplit : secondMarginal (krausAverageState ψ I.toKraus) b c
      = ∑ i, secondMarginalState (branchState I ψ i) b c := by
    simp only [krausAverageState, branchState, secondMarginalState, secondMarginal,
      Matrix.sum_apply, outerProduct_apply]
    rw [@Finset.sum_comm (Fin D) ℂ (Fin 2)]
  rw [← hsplit]
  exact secondMarginal_krausAverageState ψ I.toKraus b c

theorem secondMarginal_average_eq_input (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (b c : Fin E) :
    secondMarginal (krausAverageState ψ I.toKraus) b c = secondMarginalState ψ b c :=
  secondMarginal_krausAverageState ψ I.toKraus b c

noncomputable def branchConditionalEntropy (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) : ℝ :=
  if h : branchMass I ψ i = 0 then 0
  else ∑ j, Real.negMulLog (krausBranchSpectrum ψ I.toKraus i j / branchMass I ψ i)

def GeneralTwoOutcomeAverageEntropy (D E : ℕ) : Prop :=
  ∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
    (∑ i, branchMass I ψ i * branchConditionalEntropy I ψ i)
      ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ

theorem frontier1 :
    (∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
      (∑ i, branchMass I ψ i) = 1) ∧
    (∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (i : Fin 2),
      0 ≤ branchMass I ψ i) ∧
    (∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (i : Fin 2),
      branchMass I ψ i = 0 ↔ ∀ j, branchState I ψ i j = 0) ∧
    (∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (i : Fin 2),
      (hp : 0 < branchMass I ψ i) → Normalized (normalizedBranchState I ψ i hp)) ∧
    (∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (i : Fin 2),
      (hp : 0 < branchMass I ψ i) → 0 ≤ branchEntropy I ψ i hp) ∧
    (∀ (I : TwoOutcomeInstrument D) (ψ : QState (Fin D × Fin E)) (b c : Fin E),
      (∑ i, secondMarginalState (branchState I ψ i) b c) = secondMarginalState ψ b c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I ψ hψ
    exact branchMass_sum_eq_one I ψ hψ
  · intro I ψ i
    exact branchMass_nonneg I ψ i
  · intro I ψ i
    exact branchMass_eq_zero_iff I ψ i
  · intro I ψ i hp
    exact normalizedBranchState_normalized I ψ i hp
  · intro I ψ i hp
    exact branchEntropy_nonneg I ψ i hp
  · intro I ψ b c
    exact secondMarginal_sum_branch I ψ b c

open HermitianMat
open IsMaximalSelfAdjoint
open scoped InnerProductSpace RealInnerProductSpace

noncomputable def secondMarginalOperator {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    HermitianMat (Fin E) ℂ :=
  ⟨secondMarginalState ψ, secondMarginalState_hermitian ψ⟩

noncomputable def secondMarginalMixed {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) : MState (Fin E) :=
  (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceLeft

theorem secondMarginalMixed_m {D E : ℕ} (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (secondMarginalMixed ψ hψ).m = secondMarginalState ψ := by
  unfold secondMarginalMixed
  have hket : (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).m
      = fun i j => ψ i * star (ψ j) := by
    rw [Qatlib.Foundations.PureStateMath.BornBridge.pure_normalizedStateEquivKet_m]
  have htrace : ((MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceLeft).m
      = (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).m.traceLeft := by
    rfl
  rw [htrace, hket]
  ext b c
  simp [Matrix.traceLeft, secondMarginalState, secondMarginal, outerProduct_apply]

theorem entropy_eq_secondMarginalMixed {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) :
    Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ = Sᵥₙ (secondMarginalMixed ψ hψ) := by
  show Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ
      = Sᵥₙ ((MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceLeft)
  exact Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy_eq_complement ψ hψ

theorem secondMarginalState_smul {D E : ℕ} (c : ℝ) (ψ : QState (Fin D × Fin E)) :
    secondMarginalState (c • ψ) = c ^ 2 • secondMarginalState ψ := by
  have hstar : ∀ (z : ℂ), (starRingEnd ℂ) ((algebraMap ℝ ℂ) c * z)
      = (algebraMap ℝ ℂ) c * (starRingEnd ℂ) z := by
    intro z
    rw [map_mul (starRingEnd ℂ) (algebraMap ℝ ℂ c) z]
    simp
  apply Matrix.ext
  intro b c'
  simp only [secondMarginalState, secondMarginal, outerProduct_apply, Algebra.smul_def,
    Pi.mul_apply, Pi.algebraMap_apply, Matrix.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hstar]
  have halg : ∀ x : ℝ, (algebraMap ℝ ℂ) x = (x : ℂ) := fun _ => rfl
  simp only [halg]
  rw [pow_two, Complex.ofReal_mul c c]
  ring

variable {n : ℕ}

noncomputable def normalizedKrausBranch {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (hp : 0 < krausBranchMass ψ K i) :
    QState (Fin D × Fin E) :=
  ((Real.sqrt (krausBranchMass ψ K i))⁻¹ : ℝ) • krausBranch ψ K i

theorem normalizedKrausBranch_normalized {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (hp : 0 < krausBranchMass ψ K i) :
    Normalized (normalizedKrausBranch ψ K i hp) := by
  have hp0 : 0 < Real.sqrt (krausBranchMass ψ K i) := Real.sqrt_pos.2 hp
  have hnorm : (∑ j, ‖krausBranch ψ K i j‖ ^ 2) = krausBranchMass ψ K i := rfl
  have hsq : ∀ j, ‖((Real.sqrt (krausBranchMass ψ K i))⁻¹ : ℝ) • krausBranch ψ K i j‖ ^ 2
      = ((Real.sqrt (krausBranchMass ψ K i))⁻¹) ^ 2 * (‖krausBranch ψ K i j‖ ^ 2) := by
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp0), pow_two]
    ring
  unfold Normalized normalizedKrausBranch
  calc (∑ j, ‖((Real.sqrt (krausBranchMass ψ K i))⁻¹ : ℝ) • krausBranch ψ K i j‖ ^ 2)
      = ∑ j, ((Real.sqrt (krausBranchMass ψ K i))⁻¹) ^ 2 * (‖krausBranch ψ K i j‖ ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => hsq j
    _ = ((Real.sqrt (krausBranchMass ψ K i))⁻¹) ^ 2 * (∑ j, ‖krausBranch ψ K i j‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ = ((Real.sqrt (krausBranchMass ψ K i))⁻¹) ^ 2 * krausBranchMass ψ K i := by rw [hnorm]
    _ = 1 := by
        rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ (ne_of_gt hp)]

noncomputable def branchSecondMarginalMixed {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (hp : 0 < krausBranchMass ψ K i) :
    MState (Fin E) :=
  secondMarginalMixed (normalizedKrausBranch ψ K i hp)
    (normalizedKrausBranch_normalized ψ K i hp)

theorem branchSecondMarginalMixed_m {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (hp : 0 < krausBranchMass ψ K i) :
    (branchSecondMarginalMixed ψ K i hp).m
      = (krausBranchMass ψ K i)⁻¹ • secondMarginalState (krausBranch ψ K i) := by
  simp only [branchSecondMarginalMixed]
  rw [secondMarginalMixed_m]
  unfold normalizedKrausBranch
  rw [secondMarginalState_smul]
  have hreal : ((Real.sqrt (krausBranchMass ψ K i))⁻¹ : ℝ) ^ 2
      = (krausBranchMass ψ K i)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hp.le]
  rw [hreal]

noncomputable def krausBranchEntropy {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (hp : 0 < krausBranchMass ψ K i) : ℝ :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy (normalizedKrausBranch ψ K i hp)
    (normalizedKrausBranch_normalized ψ K i hp)

theorem krausBranchEntropy_eq_secondMarginalMixed {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (hp : 0 < krausBranchMass ψ K i) :
    krausBranchEntropy ψ K i hp = Sᵥₙ (branchSecondMarginalMixed ψ K i hp) :=
  entropy_eq_secondMarginalMixed _ _

theorem secondMarginal_sum_krausBranch {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (b c : Fin E) :
    (∑ i, secondMarginalState (krausBranch ψ K i) b c) = secondMarginalState ψ b c := by
  have hsplit : secondMarginal (krausAverageState ψ K) b c
      = ∑ i, secondMarginalState (krausBranch ψ K i) b c := by
    simp only [krausAverageState, secondMarginalState, secondMarginal, Matrix.sum_apply,
      outerProduct_apply]
    rw [@Finset.sum_comm (Fin D) ℂ (Fin n)]
  rw [← hsplit]
  exact secondMarginal_krausAverageState ψ K b c

theorem secondMarginal_sum_krausBranch_matrix {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) :
    (∑ i, secondMarginalState (krausBranch ψ K i)) = secondMarginalState ψ := by
  apply Matrix.ext
  intro b c
  simp only [Matrix.sum_apply]
  exact secondMarginal_sum_krausBranch ψ K b c

theorem secondMarginal_krausBranch_eq_zero {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) (h : krausBranchMass ψ K i = 0) :
    secondMarginalState (krausBranch ψ K i) = 0 := by
  have hzero : ∀ j, krausBranch ψ K i j = 0 := (krausBranchMass_eq_zero_iff ψ K i).mp h
  ext b c
  simp only [secondMarginalState, secondMarginal]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp only [outerProduct_apply]
  rw [hzero (a, b), hzero (a, c)]
  simp

noncomputable def branchSecondMarginalFamily {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (hψ : Normalized ψ) (i : Fin n) : MState (Fin E) :=
  if hp : 0 < krausBranchMass ψ K i then branchSecondMarginalMixed ψ K i hp
  else secondMarginalMixed ψ hψ

noncomputable def krausAverageBranchEntropy {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) : ℝ :=
  ∑ i, krausBranchMass ψ K i *
    (if hp : 0 < krausBranchMass ψ K i then krausBranchEntropy ψ K i hp else 0)

def VonNeumannEntropyConcaveForMixtures (D : ℕ) : Prop :=
  ∀ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → MState (Fin D)) (ρ : MState (Fin D)),
    (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
    ρ.m = ∑ i, p i • (σ i).m →
    (∑ i, p i * Sᵥₙ (σ i)) ≤ Sᵥₙ ρ

theorem secondMarginal_mix {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (hψ : Normalized ψ) :
    (∑ i, krausBranchMass ψ K i • (branchSecondMarginalFamily ψ K hψ i).m)
      = (secondMarginalMixed ψ hψ).m := by
  calc (∑ i, krausBranchMass ψ K i • (branchSecondMarginalFamily ψ K hψ i).m)
      = ∑ i, secondMarginalState (krausBranch ψ K i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hp : 0 < krausBranchMass ψ K i
        · have hfam : branchSecondMarginalFamily ψ K hψ i = branchSecondMarginalMixed ψ K i hp := by
            simp [branchSecondMarginalFamily, hp]
          rw [hfam, branchSecondMarginalMixed_m]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hp), one_smul]
        · have hz : krausBranchMass ψ K i = 0 :=
            le_antisymm (le_of_not_gt hp) (krausBranchMass_nonneg ψ K i)
          have hfam : branchSecondMarginalFamily ψ K hψ i = secondMarginalMixed ψ hψ := by
            simp [branchSecondMarginalFamily, hp]
          rw [hfam, hz, zero_smul]
          rw [secondMarginal_krausBranch_eq_zero ψ K i hz]
    _ = secondMarginalState ψ := secondMarginal_sum_krausBranch_matrix ψ K
    _ = (secondMarginalMixed ψ hψ).m := (secondMarginalMixed_m ψ hψ).symm

theorem krausAverageBranchEntropy_le_of_concavity {D E : ℕ}
    (hconc : VonNeumannEntropyConcaveForMixtures E) (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (hψ : Normalized ψ) :
    krausAverageBranchEntropy ψ K ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ := by
  have hmix : (∑ i, krausBranchMass ψ K i • (branchSecondMarginalFamily ψ K hψ i).m)
      = (secondMarginalMixed ψ hψ).m := secondMarginal_mix ψ K hψ
  have hconc' : (∑ i, krausBranchMass ψ K i * Sᵥₙ (branchSecondMarginalFamily ψ K hψ i))
      ≤ Sᵥₙ (secondMarginalMixed ψ hψ) :=
    hconc n (krausBranchMass ψ K) (branchSecondMarginalFamily ψ K hψ) (secondMarginalMixed ψ hψ)
      (krausBranchMass_nonneg ψ K) (krausBranchMass_sum_eq_one ψ K hψ) hmix.symm
  have hsum : (∑ i, krausBranchMass ψ K i *
      (if hp : 0 < krausBranchMass ψ K i then krausBranchEntropy ψ K i hp else 0))
      = ∑ i, krausBranchMass ψ K i * Sᵥₙ (branchSecondMarginalFamily ψ K hψ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : 0 < krausBranchMass ψ K i
    · simp only [hp, dif_pos]
      have hfam : branchSecondMarginalFamily ψ K hψ i = branchSecondMarginalMixed ψ K i hp := by
        simp [branchSecondMarginalFamily, hp]
      rw [hfam, krausBranchEntropy_eq_secondMarginalMixed]
    · have hz : krausBranchMass ψ K i = 0 :=
        le_antisymm (le_of_not_gt hp) (krausBranchMass_nonneg ψ K i)
      have hd : (if hp : 0 < krausBranchMass ψ K i
          then krausBranchEntropy ψ K i hp else 0) = 0 := by
        rw [dif_neg hp]
      rw [hd, hz, zero_mul, zero_mul]
  rw [krausAverageBranchEntropy, hsum]
  exact hconc'.trans_eq (entropy_eq_secondMarginalMixed ψ hψ).symm

def GeneralKrausAverageEntropyBound (D E : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : QState (Fin D × Fin E)) (K : KrausInstrument D n) (hψ : Normalized ψ),
    krausAverageBranchEntropy ψ K ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ

theorem M_eq_sum_smul {n : ℕ} (p : Fin n → ℝ) (σ : Fin n → MState (Fin D))
    (ρ : MState (Fin D)) (h : ρ.m = ∑ i, p i • (σ i).m) :
    ρ.M = ∑ i, p i • (σ i).M := by
  apply HermitianMat.ext
  calc ρ.M.mat = ρ.m := MState.mat_M ρ
    _ = ∑ i, p i • (σ i).m := h
    _ = ∑ i, (p i • (σ i).M).mat := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [HermitianMat.mat_smul, MState.mat_M]
    _ = (∑ i, p i • (σ i).M).mat := (HermitianMat.mat_finset_sum _ _).symm

theorem inner_finset_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → HermitianMat (Fin D) ℂ) (C : HermitianMat (Fin D) ℂ) :
    ⟪Finset.sum s f, C⟫ = Finset.sum s fun i => ⟪f i, C⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianMat.inner_add_left, ih]

theorem ker_mixture_le {n : ℕ} (p : Fin n → ℝ) (σ : Fin n → MState (Fin D))
    (ρ : MState (Fin D)) (hp : ∀ i, 0 ≤ p i)
    (hmix : ρ.M = ∑ i, p i • (σ i).M) (i : Fin n) (hpi : 0 < p i) :
    ρ.M.ker ≤ (σ i).M.ker := by
  have hpsd : ∀ j, 0 ≤ p j • (σ j).M := by
    intro j
    rw [HermitianMat.zero_le_iff, HermitianMat.mat_smul]
    exact (HermitianMat.zero_le_iff.mp (σ j).nonneg).smul (hp j)
  have hsub : (∑ j, p j • (σ j).M).ker ≤ (σ i).M.ker := by
    rw [HermitianMat.ker_sum _ hpsd]
    intro x hx
    have hxi : x ∈ (p i • (σ i).M).ker :=
      Iff.mp (Submodule.mem_iInf (fun j : Fin n => (p j • (σ j).M).ker)) hx i
    rw [HermitianMat.ker_pos_smul (σ i).M (ne_of_gt hpi)] at hxi
    exact hxi
  rw [hmix]
  exact hsub

theorem vonNeumannEntropy_concave_mixture {n : ℕ} (p : Fin n → ℝ)
    (σ : Fin n → MState (Fin D)) (ρ : MState (Fin D))
    (hp : ∀ i, 0 ≤ p i) (hmix : ρ.m = ∑ i, p i • (σ i).m) :
    (∑ i, p i * Sᵥₙ (σ i)) ≤ Sᵥₙ ρ := by
  have hM : ρ.M = ∑ i, p i • (σ i).M := M_eq_sum_smul p σ ρ hmix
  have hker : ∀ i, 0 < p i → ρ.M.ker ≤ (σ i).M.ker :=
    fun i hpi => ker_mixture_le p σ ρ hp hM i hpi
  have hgibbs : ∀ i (hpi : 0 < p i),
      0 ≤ ⟪(σ i).M, (σ i).M.log - ρ.M.log⟫ := by
    intro i hpi
    exact inner_log_sub_log_nonneg (ρ := σ i) (σ := ρ) (hker i hpi)
  have hgsum : (∑ i, p i * ⟪(σ i).M, (σ i).M.log - ρ.M.log⟫) ≥ 0 := by
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases hpi : 0 < p i
    · exact mul_nonneg (hp i) (hgibbs i hpi)
    · have hpi0 : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp i)
      rw [hpi0, zero_mul]
  have h2 : (∑ i, p i * ⟪(σ i).M, (σ i).M.log⟫)
      - (∑ i, p i * ⟪(σ i).M, ρ.M.log⟫) ≥ 0 := by
    calc (∑ i, p i * ⟪(σ i).M, (σ i).M.log⟫)
        - (∑ i, p i * ⟪(σ i).M, ρ.M.log⟫)
        = ∑ i, (p i * ⟪(σ i).M, (σ i).M.log⟫ - p i * ⟪(σ i).M, ρ.M.log⟫) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ i, p i * ⟪(σ i).M, (σ i).M.log - ρ.M.log⟫ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [HermitianMat.inner_sub_left]
          ring
      _ ≥ 0 := hgsum
  have hlin : (∑ i, p i * ⟪(σ i).M, ρ.M.log⟫) = ⟪ρ.M, ρ.M.log⟫ := by
    have h1 : ⟪∑ i, p i • (σ i).M, ρ.M.log⟫
        = ∑ i, p i * ⟪(σ i).M, ρ.M.log⟫ := by
      rw [inner_finset_sum_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact HermitianMat.inner_smul_left (σ i).M ρ.M.log (p i)
    calc (∑ i, p i * ⟪(σ i).M, ρ.M.log⟫)
        = ⟪∑ i, p i • (σ i).M, ρ.M.log⟫ := h1.symm
        _ = ⟪ρ.M, ρ.M.log⟫ := by rw [hM]
  have hcomb : (∑ i, p i * ⟪(σ i).M, (σ i).M.log⟫) ≥ ⟪ρ.M, ρ.M.log⟫ := by
    rw [hlin] at h2
    linarith
  have hS : ∀ i, Sᵥₙ (σ i) = -⟪(σ i).M, (σ i).M.log⟫ := by
    intro i
    rw [Sᵥₙ_eq_neg_trace_log, HermitianMat.inner_comm]
  have hSρ : Sᵥₙ ρ = -⟪ρ.M, ρ.M.log⟫ := by
    rw [Sᵥₙ_eq_neg_trace_log, HermitianMat.inner_comm]
  calc (∑ i, p i * Sᵥₙ (σ i))
      = -∑ i, p i * ⟪(σ i).M, (σ i).M.log⟫ := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hS i]
        ring
      _ ≤ -⟪ρ.M, ρ.M.log⟫ := by
        linarith
      _ = Sᵥₙ ρ := hSρ.symm

theorem vonNeumannEntropyConcaveForMixtures (D : ℕ) : VonNeumannEntropyConcaveForMixtures D := by
  intro n p σ ρ hp hsum hmix
  exact vonNeumannEntropy_concave_mixture p σ ρ hp hmix

theorem generalKrausAverageEntropyBound (D E : ℕ) : GeneralKrausAverageEntropyBound D E := by
  intro n ψ K hψ
  exact krausAverageBranchEntropy_le_of_concavity (vonNeumannEntropyConcaveForMixtures E) ψ K hψ

noncomputable def firstMarginalState {D E : ℕ} (ψ : QState (Fin D × Fin E)) : Operator D :=
  PartialTrace (outerProduct ψ)

theorem firstMarginalState_smul {D E : ℕ} (c : ℝ) (ψ : QState (Fin D × Fin E)) :
    firstMarginalState (c • ψ) = c ^ 2 • firstMarginalState ψ := by
  have hstar : ∀ (z : ℂ), (starRingEnd ℂ) ((algebraMap ℝ ℂ) c * z)
      = (algebraMap ℝ ℂ) c * (starRingEnd ℂ) z := by
    intro z
    rw [map_mul (starRingEnd ℂ) (algebraMap ℝ ℂ c) z]
    simp
  apply Matrix.ext
  intro i j
  simp only [firstMarginalState, PartialTrace, outerProduct_apply, Algebra.smul_def,
    Pi.mul_apply, Pi.algebraMap_apply, Matrix.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hstar]
  have halg : ∀ x : ℝ, (algebraMap ℝ ℂ) x = (x : ℂ) := fun _ => rfl
  simp only [halg]
  rw [pow_two, Complex.ofReal_mul c c]
  ring

theorem sum_negMulLog_eigenvalues_smul {n : ℕ} (A : HermitianMat (Fin n) ℂ) (c : ℝ)
    (hc : c ≠ 0) :
    (∑ j, Real.negMulLog (A.H.eigenvalues j / c))
      = (∑ j, Real.negMulLog ((c⁻¹ • A).H.eigenvalues j)) := by
  have hcongr : A.cfc (fun u : ℝ ↦ Real.negMulLog (u / c))
      = A.cfc (fun u : ℝ ↦ Real.negMulLog (c⁻¹ * u)) := by
    refine HermitianMat.cfc_congr ?_
    intro u hu
    have hdiv : u / c = c⁻¹ * u := (div_eq_mul_inv u c).trans (mul_comm u c⁻¹)
    show Real.negMulLog (u / c) = Real.negMulLog (c⁻¹ * u)
    rw [hdiv]
  have hcomp : (A.cfc (fun x : ℝ ↦ c⁻¹ * x)).cfc Real.negMulLog
      = A.cfc (fun u : ℝ ↦ Real.negMulLog (c⁻¹ * u)) := by
    rw [← HermitianMat.cfc_comp]
    rfl
  have hcfc : c⁻¹ • A = A.cfc (fun x : ℝ ↦ c⁻¹ * x) :=
    (HermitianMat.cfc_const_mul_id A c⁻¹).symm
  calc (∑ j, Real.negMulLog (A.H.eigenvalues j / c))
      = (A.cfc (fun u : ℝ ↦ Real.negMulLog (u / c))).trace := by
        have h := HermitianMat.trace_cfc_eq A (fun u : ℝ ↦ Real.negMulLog (u / c))
        rw [h]
    _ = (A.cfc (fun u : ℝ ↦ Real.negMulLog (c⁻¹ * u))).trace := by rw [hcongr]
    _ = ((A.cfc (fun x : ℝ ↦ c⁻¹ * x)).cfc Real.negMulLog).trace := by rw [hcomp]
    _ = ((c⁻¹ • A).cfc Real.negMulLog).trace := by rw [hcfc]
    _ = ∑ j, Real.negMulLog ((c⁻¹ • A).H.eigenvalues j) := by
        have h := HermitianMat.trace_cfc_eq (c⁻¹ • A) Real.negMulLog
        rw [h]

theorem branchConditionalEntropy_eq_branchEntropy (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) (hp : 0 < branchMass I ψ i) :
    branchConditionalEntropy I ψ i = branchEntropy I ψ i hp := by
  have hp' : 0 < krausBranchMass ψ I.toKraus i := hp
  let A : HermitianMat (Fin D) ℂ :=
    ⟨krausBranchReduced ψ I.toKraus i, krausBranchReduced_hermitian ψ I.toKraus i⟩
  let φ : QState (Fin D × Fin E) := normalizedBranchState I ψ i hp
  let hφ : Normalized φ := normalizedBranchState_normalized I ψ i hp

  have hval : (krausBranchMass ψ I.toKraus i)⁻¹ • A.mat = PartialTrace (outerProduct φ) := by
    have hreal : ((Real.sqrt (krausBranchMass ψ I.toKraus i))⁻¹ : ℝ) ^ 2
        = (krausBranchMass ψ I.toKraus i)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hp'.le]
    show (krausBranchMass ψ I.toKraus i)⁻¹ • krausBranchReduced ψ I.toKraus i
      = PartialTrace (outerProduct (((Real.sqrt (krausBranchMass ψ I.toKraus i))⁻¹ : ℝ)
          • krausBranch ψ I.toKraus i))
    rw [show PartialTrace (outerProduct (((Real.sqrt (krausBranchMass ψ I.toKraus i))⁻¹ : ℝ)
          • krausBranch ψ I.toKraus i))
        = firstMarginalState (((Real.sqrt (krausBranchMass ψ I.toKraus i))⁻¹ : ℝ)
          • krausBranch ψ I.toKraus i) from rfl]
    rw [firstMarginalState_smul, hreal]
    rfl

  have hM : (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity φ hφ)).M
      = (krausBranchMass ψ I.toKraus i)⁻¹ • A := by
    apply HermitianMat.ext
    rw [MState.mat_M, Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m,
        Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity_val]
    exact hval.symm

  have hent : branchEntropy I ψ i hp
      = ∑ j, Real.negMulLog (((krausBranchMass ψ I.toKraus i)⁻¹ • A).H.eigenvalues j) := by
    show Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy φ hφ
        = ∑ j, Real.negMulLog (((krausBranchMass ψ I.toKraus i)⁻¹ • A).H.eigenvalues j)
    have h1 : Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy φ hφ
        = Sᵥₙ (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity φ hφ)) := rfl
    have h2 : Sᵥₙ (Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity φ hφ))
        = ((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity φ hφ)).M.cfc
          Real.negMulLog).trace := Sᵥₙ_eq_trace_cfc_negMulLog _
    have h3 : ((Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity φ hφ)).M.cfc
          Real.negMulLog).trace
        = (((krausBranchMass ψ I.toKraus i)⁻¹ • A).cfc Real.negMulLog).trace := by rw [hM]
    have h4 : (((krausBranchMass ψ I.toKraus i)⁻¹ • A).cfc Real.negMulLog).trace
        = ∑ j, Real.negMulLog (((krausBranchMass ψ I.toKraus i)⁻¹ • A).H.eigenvalues j) := by
      have h := HermitianMat.trace_cfc_eq ((krausBranchMass ψ I.toKraus i)⁻¹ • A)
        Real.negMulLog
      rw [h]
    rw [h1, h2, h3, h4]

  have hspec : branchConditionalEntropy I ψ i
      = ∑ j, Real.negMulLog (A.H.eigenvalues j / krausBranchMass ψ I.toKraus i) := by
    show (if h : branchMass I ψ i = 0 then 0
        else ∑ j, Real.negMulLog (krausBranchSpectrum ψ I.toKraus i j / branchMass I ψ i))
        = ∑ j, Real.negMulLog (A.H.eigenvalues j / krausBranchMass ψ I.toKraus i)
    rw [dif_neg hp.ne']
    refine Finset.sum_congr rfl fun j _ => ?_
    have hspecj : krausBranchSpectrum ψ I.toKraus i j = A.H.eigenvalues j := by rfl
    rw [hspecj]
    rfl
  rw [hspec]
  rw [sum_negMulLog_eigenvalues_smul A (krausBranchMass ψ I.toKraus i)
    (ne_of_gt hp')]
  exact hent.symm

theorem branchConditionalEntropy_eq_secondMarginalMixed (I : TwoOutcomeInstrument D)
    (ψ : QState (Fin D × Fin E)) (i : Fin 2) (hp : 0 < branchMass I ψ i) :
    branchConditionalEntropy I ψ i
      = Sᵥₙ (branchSecondMarginalMixed ψ I.toKraus i hp) := by
  rw [branchConditionalEntropy_eq_branchEntropy I ψ i hp]
  show Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy (normalizedBranchState I ψ i hp)
      (normalizedBranchState_normalized I ψ i hp)
      = Sᵥₙ (branchSecondMarginalMixed ψ I.toKraus i hp)
  exact krausBranchEntropy_eq_secondMarginalMixed ψ I.toKraus i hp

theorem generalTwoOutcomeAverageEntropy (D E : ℕ) : GeneralTwoOutcomeAverageEntropy D E := by
  intro I ψ hψ
  have hsum : (∑ i, branchMass I ψ i * branchConditionalEntropy I ψ i)
      = krausAverageBranchEntropy ψ I.toKraus := by
    unfold krausAverageBranchEntropy
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hpi : 0 < krausBranchMass ψ I.toKraus i
    · have hp : 0 < branchMass I ψ i := hpi
      have hbc : branchConditionalEntropy I ψ i
          = krausBranchEntropy ψ I.toKraus i hpi := by
        rw [branchConditionalEntropy_eq_branchEntropy I ψ i hp]
        rfl
      rw [hbc, dif_pos hpi]
      rfl
    · have hz : krausBranchMass ψ I.toKraus i = 0 :=
        le_antisymm (le_of_not_gt hpi) (krausBranchMass_nonneg ψ I.toKraus i)
      have hz' : branchMass I ψ i = 0 := hz
      have hbc : branchConditionalEntropy I ψ i = 0 := by
        show (if h : branchMass I ψ i = 0 then 0
            else ∑ j, Real.negMulLog (krausBranchSpectrum ψ I.toKraus i j / branchMass I ψ i))
            = 0
        rw [dif_pos hz']
      rw [hbc, dif_neg hpi, hz]
      simp
  calc (∑ i, branchMass I ψ i * branchConditionalEntropy I ψ i)
      = krausAverageBranchEntropy ψ I.toKraus := hsum
    _ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ :=
      krausAverageBranchEntropy_le_of_concavity (vonNeumannEntropyConcaveForMixtures E)
        ψ I.toKraus hψ

inductive GeneralLoccTree (D : ℕ) : Type

  | halt : GeneralLoccTree D

  | node (n : ℕ) (K : KrausInstrument D n) (next : Fin n → GeneralLoccTree D) :
      GeneralLoccTree D

noncomputable def generalTreeAverageEntropy {D E : ℕ} (T : GeneralLoccTree D)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  match T with
  | .halt => Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ
  | .node n K next =>
      ∑ i, krausBranchMass ψ K i *
        (if hp : 0 < krausBranchMass ψ K i then
            generalTreeAverageEntropy (next i) (normalizedKrausBranch ψ K i hp)
              (normalizedKrausBranch_normalized ψ K i hp)
          else 0)

theorem generalTreeAverageEntropy_le : ∀ (T : GeneralLoccTree D)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
    generalTreeAverageEntropy T ψ hψ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ := by
  intro T
  induction T with
  | halt =>
      intro ψ hψ
      exact le_rfl
  | @node n K next ih =>
      intro ψ hψ
      simp only [generalTreeAverageEntropy]
      calc (∑ i, krausBranchMass ψ K i *
            (if hp : 0 < krausBranchMass ψ K i then
                generalTreeAverageEntropy (next i) (normalizedKrausBranch ψ K i hp)
                  (normalizedKrausBranch_normalized ψ K i hp)
              else 0))
          ≤ ∑ i, krausBranchMass ψ K i *
            (if hp : 0 < krausBranchMass ψ K i then
                krausBranchEntropy ψ K i hp
              else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hp : 0 < krausBranchMass ψ K i
            · simp only [hp, dif_pos]
              have hle : generalTreeAverageEntropy (next i) (normalizedKrausBranch ψ K i hp)
                    (normalizedKrausBranch_normalized ψ K i hp)
                  ≤ krausBranchEntropy ψ K i hp := by
                exact ih i _ _
              exact mul_le_mul_of_nonneg_left hle (krausBranchMass_nonneg ψ K i)
            · simp only [hp]
              exact le_rfl
        _ = krausAverageBranchEntropy ψ K := rfl
        _ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ :=
          krausAverageBranchEntropy_le_of_concavity (vonNeumannEntropyConcaveForMixtures E)
            ψ K hψ

theorem generalTreeAverageEntropy_zeroMass {D E : ℕ} (n : ℕ) (K : KrausInstrument D n)
    (next : Fin n → GeneralLoccTree D) (ψ : QState (Fin D × Fin E))
    (i : Fin n) (hzero : krausBranchMass ψ K i = 0) :
    krausBranchMass ψ K i *
        (if hp : 0 < krausBranchMass ψ K i then
            generalTreeAverageEntropy (next i) (normalizedKrausBranch ψ K i hp)
              (normalizedKrausBranch_normalized ψ K i hp)
          else 0) = 0 := by
  by_cases hp : 0 < krausBranchMass ψ K i
  · rw [hzero] at hp
    exact (lt_irrefl _ hp).elim
  · rw [dif_neg hp]
    exact mul_zero _

noncomputable def generalTreeAverageEntropy_bits {D E : ℕ} (T : GeneralLoccTree D)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  generalTreeAverageEntropy T ψ hψ / Real.log 2

theorem generalTreeAverageEntropy_bits_le {D E : ℕ} (T : GeneralLoccTree D)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    generalTreeAverageEntropy_bits T ψ hψ
      ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ / Real.log 2 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := generalTreeAverageEntropy_le T ψ hψ
  rw [generalTreeAverageEntropy_bits]
  exact div_le_div_of_nonneg_right h (le_of_lt hlog)

noncomputable def generalTreeCommunicationBits {D : ℕ} : GeneralLoccTree D → ℕ
  | .halt => 0
  | .node n _ next =>
      outcomeCostBits n + Finset.univ.sup fun i => generalTreeCommunicationBits (next i)

noncomputable def generalTreeToProtocol {D E : ℕ} : GeneralLoccTree D →
    Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E
  | .halt => .halt
  | .node n K next => .stepA n K.op (fun i => generalTreeToProtocol (next i))

theorem generalTreeToProtocol_complete {D E : ℕ} (T : GeneralLoccTree D) :
    Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccComplete
      (generalTreeToProtocol (D := D) (E := E) T) := by
  induction T with
  | halt => trivial
  | node n K next ih =>
      refine ⟨?_, fun i => ih i⟩
      show (∑ i, Matrix.conjTranspose (K.op i) * K.op i) = 1
      exact K.hcomplete

theorem generalTreeCommunicationBits_eq_loccBits {D E : ℕ} (T : GeneralLoccTree D) :
    generalTreeCommunicationBits T
      = Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccBits
          (generalTreeToProtocol (D := D) (E := E) T) := by
  induction T with
  | halt => rfl
  | node n K next ih =>
      show outcomeCostBits n + (Finset.univ.sup fun i => generalTreeCommunicationBits (next i))
        = Nat.ceil (Real.log ((n : ℝ)) / Real.log 2)
          + (Finset.univ.sup fun i =>
              Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccBits
                (generalTreeToProtocol (D := D) (E := E) (next i)))
      rw [show outcomeCostBits n = Nat.ceil (Real.log ((n : ℝ)) / Real.log 2) from rfl]
      congr 1
      exact Finset.sup_congr rfl fun i _ => ih i

noncomputable def generalTreeOutcomePaths {D : ℕ} : GeneralLoccTree D → ℕ
  | .halt => 1
  | .node n _ next => ∑ i, generalTreeOutcomePaths (next i)

theorem generalTreeOutcomePaths_eq_loccLeafCount {D E : ℕ} (T : GeneralLoccTree D) :
    generalTreeOutcomePaths T
      = Qatlib.Concepts.QuditTeleport.ResourceIff.LoccLeafCount
          (generalTreeToProtocol (D := D) (E := E) T) := by
  induction T with
  | halt => rfl
  | node n K next ih =>
      show (∑ i, generalTreeOutcomePaths (next i))
        = ∑ i, Qatlib.Concepts.QuditTeleport.ResourceIff.LoccLeafCount
            (generalTreeToProtocol (D := D) (E := E) (next i))
      exact Finset.sum_congr rfl fun i _ => ih i

theorem generalTreeOutcomePaths_le_two_pow_communication {D E : ℕ} (T : GeneralLoccTree D) :
    generalTreeOutcomePaths T ≤ 2 ^ generalTreeCommunicationBits T := by
  rw [generalTreeOutcomePaths_eq_loccLeafCount T, generalTreeCommunicationBits_eq_loccBits T]
  exact Qatlib.Concepts.QuditTeleport.ResourceIff.loccLeafCount_le_two_pow_loccBits
    (generalTreeToProtocol (D := D) (E := E) T)

noncomputable def generalTreeTotalProbability {D E : ℕ} (T : GeneralLoccTree D)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  match T with
  | .halt => 1
  | .node n K next =>
      ∑ i, if hp : 0 < krausBranchMass ψ K i then
          krausBranchMass ψ K i *
            generalTreeTotalProbability (next i) (normalizedKrausBranch ψ K i hp)
              (normalizedKrausBranch_normalized ψ K i hp)
        else 0

theorem generalTreeTotalProbability_eq_one {D E : ℕ} (T : GeneralLoccTree D)
    (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    generalTreeTotalProbability T ψ hψ = 1 := by
  induction T generalizing ψ with
  | halt => rfl
  | @node n K next ih =>
      show (∑ i, if hp : 0 < krausBranchMass ψ K i then
            krausBranchMass ψ K i *
              generalTreeTotalProbability (next i) (normalizedKrausBranch ψ K i hp)
                (normalizedKrausBranch_normalized ψ K i hp)
          else 0) = 1
      calc (∑ i, if hp : 0 < krausBranchMass ψ K i then
            krausBranchMass ψ K i *
              generalTreeTotalProbability (next i) (normalizedKrausBranch ψ K i hp)
                (normalizedKrausBranch_normalized ψ K i hp)
          else 0)
          = ∑ i, krausBranchMass ψ K i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hp : 0 < krausBranchMass ψ K i
            · rw [dif_pos hp]
              rw [ih i (normalizedKrausBranch ψ K i hp)
                (normalizedKrausBranch_normalized ψ K i hp)]
              ring
            · have hz : krausBranchMass ψ K i = 0 :=
                le_antisymm (le_of_not_gt hp) (krausBranchMass_nonneg ψ K i)
              rw [dif_neg hp, hz]
        _ = 1 := krausBranchMass_sum_eq_one ψ K hψ

end Qatlib.Concepts.Entanglement.Separability.LoccAverageEntropy
