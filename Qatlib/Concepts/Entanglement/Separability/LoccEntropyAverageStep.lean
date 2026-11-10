/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.LoccAverageEntropy
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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

namespace Qatlib.Concepts.Entanglement.Separability.LoccEntropyAverageStep

open Qatlib
open Qatlib.Concepts.Entanglement.Separability
open Qatlib
open Qatlib.Concepts.Entanglement.Separability
open Qatlib.Concepts.Entanglement.Separability
open Qatlib.Concepts.Entanglement.Separability.LoccAverageEntropy
open scoped BigOperators ComplexOrder Matrix

variable {D E n : ℕ}

noncomputable def rightKrausBranch (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (1 : Operator D) (K.op i)) ψ

noncomputable def rightKrausBranchMass (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) : ℝ :=
  ∑ j, ‖rightKrausBranch ψ K i j‖ ^ 2

theorem rightKrausBranchMass_nonneg (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) : 0 ≤ rightKrausBranchMass ψ K i := by
  unfold rightKrausBranchMass
  exact Finset.sum_nonneg fun j _ => by positivity

theorem rightKrausBranchMass_eq_branchMassB (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) :
    rightKrausBranchMass ψ K i = Qatlib.Concepts.FiniteLocc.LOCCProgram.branchMassB (K.op i) (outerProduct ψ) := by
  rw [Qatlib.Concepts.FiniteLocc.LOCCProgram.branchMassB, ← outerProduct_applyGate_matrix,
      trace_outerProduct]
  rfl

theorem rightKrausBranchMass_sum_eq_one (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (hψ : Normalized ψ) :
    (∑ i, rightKrausBranchMass ψ K i) = 1 := by
  have htrace := trace_tensorRight_instrument (D := D) K.op K.hcomplete (outerProduct ψ)
  have hmass : ∀ i, rightKrausBranchMass ψ K i =
      (Matrix.trace (TensorGate (1 : Operator D) (K.op i) * outerProduct ψ *
        (TensorGate (1 : Operator D) (K.op i))ᴴ)).re := by
    intro i
    exact rightKrausBranchMass_eq_branchMassB ψ K i
  calc (∑ i, rightKrausBranchMass ψ K i)
      = ∑ i, (Matrix.trace (TensorGate (1 : Operator D) (K.op i) * outerProduct ψ *
          (TensorGate (1 : Operator D) (K.op i))ᴴ)).re :=
        Finset.sum_congr rfl fun i _ => hmass i
    _ = (∑ i, Matrix.trace (TensorGate (1 : Operator D) (K.op i) * outerProduct ψ *
          (TensorGate (1 : Operator D) (K.op i))ᴴ)).re := by rw [← Complex.re_sum]
    _ = (Matrix.trace (outerProduct ψ)).re := by rw [htrace]
    _ = 1 := by
        rw [trace_outerProduct]
        have hnorm : (∑ j, ‖ψ j‖ ^ 2 : ℝ) = 1 := hψ
        rw [hnorm]
        norm_num

theorem rightKrausBranchMass_eq_zero_iff (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) :
    rightKrausBranchMass ψ K i = 0 ↔ ∀ j, rightKrausBranch ψ K i j = 0 := by
  unfold rightKrausBranchMass
  constructor
  · intro h j
    have hz : ‖rightKrausBranch ψ K i j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun x => ‖rightKrausBranch ψ K i x‖ ^ 2)
        (fun x _ => by positivity)).mp h j (Finset.mem_univ j)
    exact norm_eq_zero.mp (by simpa using hz)
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun x => ‖rightKrausBranch ψ K i x‖ ^ 2)
      (fun x _ => by positivity)).mpr
    intro j _
    simp [h j]

noncomputable def normalizedRightKrausBranch (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (hp : 0 < rightKrausBranchMass ψ K i) :
    QState (Fin D × Fin E) :=
  ((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹ : ℝ) • rightKrausBranch ψ K i

theorem normalizedRightKrausBranch_normalized (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (hp : 0 < rightKrausBranchMass ψ K i) :
    Normalized (normalizedRightKrausBranch ψ K i hp) := by
  have hp0 : 0 < Real.sqrt (rightKrausBranchMass ψ K i) := Real.sqrt_pos.2 hp
  have hnorm : (∑ j, ‖rightKrausBranch ψ K i j‖ ^ 2) = rightKrausBranchMass ψ K i := rfl
  have hsq : ∀ j, ‖((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹ : ℝ) •
      rightKrausBranch ψ K i j‖ ^ 2 =
      ((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹) ^ 2 *
        (‖rightKrausBranch ψ K i j‖ ^ 2) := by
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp0), pow_two]
    ring
  unfold Normalized normalizedRightKrausBranch
  calc (∑ j, ‖((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹ : ℝ) •
        rightKrausBranch ψ K i j‖ ^ 2)
      = ∑ j, ((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹) ^ 2 *
          (‖rightKrausBranch ψ K i j‖ ^ 2) :=
        Finset.sum_congr rfl fun j _ => hsq j
    _ = ((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹) ^ 2 *
        (∑ j, ‖rightKrausBranch ψ K i j‖ ^ 2) := by rw [Finset.mul_sum]
    _ = ((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹) ^ 2 *
        rightKrausBranchMass ψ K i := by rw [hnorm]
    _ = 1 := by
        rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ (ne_of_gt hp)]

noncomputable def rightKrausBranchEntropy (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (hp : 0 < rightKrausBranchMass ψ K i) : ℝ :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy (normalizedRightKrausBranch ψ K i hp)
    (normalizedRightKrausBranch_normalized ψ K i hp)

noncomputable def rightKrausAverageBranchEntropy (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) : ℝ :=
  ∑ i, rightKrausBranchMass ψ K i *
    (if hp : 0 < rightKrausBranchMass ψ K i then rightKrausBranchEntropy ψ K i hp else 0)

noncomputable def firstMarginalMixed (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) : MState (Fin D) :=
  Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity ψ hψ)

theorem firstMarginalMixed_m (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (firstMarginalMixed ψ hψ).m = firstMarginalState ψ := by
  rw [firstMarginalMixed, Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m,
    Qatlib.Concepts.UnbiasedBases.ThreeBasis.reducedDensity_val]
  rfl

theorem entropy_eq_firstMarginalMixed (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) :
    Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ = Sᵥₙ (firstMarginalMixed ψ hψ) := rfl

noncomputable def rightBranchFirstMarginalMixed (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (hp : 0 < rightKrausBranchMass ψ K i) :
    MState (Fin D) :=
  firstMarginalMixed (normalizedRightKrausBranch ψ K i hp)
    (normalizedRightKrausBranch_normalized ψ K i hp)

theorem rightBranchFirstMarginalMixed_m (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (hp : 0 < rightKrausBranchMass ψ K i) :
    (rightBranchFirstMarginalMixed ψ K i hp).m =
      (rightKrausBranchMass ψ K i)⁻¹ • firstMarginalState (rightKrausBranch ψ K i) := by
  simp only [rightBranchFirstMarginalMixed]
  rw [firstMarginalMixed_m]
  unfold normalizedRightKrausBranch
  rw [firstMarginalState_smul]
  have hreal : ((Real.sqrt (rightKrausBranchMass ψ K i))⁻¹ : ℝ) ^ 2 =
      (rightKrausBranchMass ψ K i)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hp.le]
  rw [hreal]

theorem rightKrausBranchEntropy_eq_firstMarginalMixed (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (hp : 0 < rightKrausBranchMass ψ K i) :
    rightKrausBranchEntropy ψ K i hp = Sᵥₙ (rightBranchFirstMarginalMixed ψ K i hp) :=
  entropy_eq_firstMarginalMixed _ _

theorem firstMarginal_sum_rightKrausBranch_matrix (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) :
    (∑ i, firstMarginalState (rightKrausBranch ψ K i)) = firstMarginalState ψ := by
  simp only [firstMarginalState, rightKrausBranch, outerProduct_applyGate_matrix]
  rw [← partialTrace_sum]
  exact partialTrace_right_instrument K.op K.hcomplete (outerProduct ψ)

theorem firstMarginal_rightKrausBranch_eq_zero (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (i : Fin n) (h : rightKrausBranchMass ψ K i = 0) :
    firstMarginalState (rightKrausBranch ψ K i) = 0 := by
  have hzero : ∀ j, rightKrausBranch ψ K i j = 0 :=
    (rightKrausBranchMass_eq_zero_iff ψ K i).mp h
  ext a b
  simp only [firstMarginalState, PartialTrace]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [outerProduct_apply]
  rw [hzero (a, c), hzero (b, c)]
  simp

noncomputable def rightBranchFirstMarginalFamily (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (hψ : Normalized ψ) (i : Fin n) : MState (Fin D) :=
  if hp : 0 < rightKrausBranchMass ψ K i then rightBranchFirstMarginalMixed ψ K i hp
  else firstMarginalMixed ψ hψ

theorem firstMarginal_mix_rightKrausBranch (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (hψ : Normalized ψ) :
    (∑ i, rightKrausBranchMass ψ K i • (rightBranchFirstMarginalFamily ψ K hψ i).m) =
      (firstMarginalMixed ψ hψ).m := by
  calc (∑ i, rightKrausBranchMass ψ K i • (rightBranchFirstMarginalFamily ψ K hψ i).m)
      = ∑ i, firstMarginalState (rightKrausBranch ψ K i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hp : 0 < rightKrausBranchMass ψ K i
        · have hfam : rightBranchFirstMarginalFamily ψ K hψ i =
              rightBranchFirstMarginalMixed ψ K i hp := by
            simp [rightBranchFirstMarginalFamily, hp]
          rw [hfam, rightBranchFirstMarginalMixed_m, smul_smul,
            mul_inv_cancel₀ (ne_of_gt hp), one_smul]
        · have hz : rightKrausBranchMass ψ K i = 0 :=
            le_antisymm (le_of_not_gt hp) (rightKrausBranchMass_nonneg ψ K i)
          have hfam : rightBranchFirstMarginalFamily ψ K hψ i = firstMarginalMixed ψ hψ := by
            simp [rightBranchFirstMarginalFamily, hp]
          rw [hfam, hz, zero_smul, firstMarginal_rightKrausBranch_eq_zero ψ K i hz]
    _ = firstMarginalState ψ := firstMarginal_sum_rightKrausBranch_matrix ψ K
    _ = (firstMarginalMixed ψ hψ).m := (firstMarginalMixed_m ψ hψ).symm

theorem rightKrausAverageBranchEntropy_le_of_concavity
    (hconc : VonNeumannEntropyConcaveForMixtures D) (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (hψ : Normalized ψ) :
    rightKrausAverageBranchEntropy ψ K ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ := by
  have hmix : (∑ i, rightKrausBranchMass ψ K i •
      (rightBranchFirstMarginalFamily ψ K hψ i).m) = (firstMarginalMixed ψ hψ).m :=
    firstMarginal_mix_rightKrausBranch ψ K hψ
  have hconc' : (∑ i, rightKrausBranchMass ψ K i *
      Sᵥₙ (rightBranchFirstMarginalFamily ψ K hψ i)) ≤ Sᵥₙ (firstMarginalMixed ψ hψ) :=
    hconc n (rightKrausBranchMass ψ K) (rightBranchFirstMarginalFamily ψ K hψ)
      (firstMarginalMixed ψ hψ) (rightKrausBranchMass_nonneg ψ K)
      (rightKrausBranchMass_sum_eq_one ψ K hψ) hmix.symm
  have hsum : (∑ i, rightKrausBranchMass ψ K i *
      (if hp : 0 < rightKrausBranchMass ψ K i then rightKrausBranchEntropy ψ K i hp else 0)) =
      ∑ i, rightKrausBranchMass ψ K i * Sᵥₙ (rightBranchFirstMarginalFamily ψ K hψ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : 0 < rightKrausBranchMass ψ K i
    · simp only [hp, dif_pos]
      have hfam : rightBranchFirstMarginalFamily ψ K hψ i =
          rightBranchFirstMarginalMixed ψ K i hp := by
        simp [rightBranchFirstMarginalFamily, hp]
      rw [hfam, rightKrausBranchEntropy_eq_firstMarginalMixed]
    · have hz : rightKrausBranchMass ψ K i = 0 :=
        le_antisymm (le_of_not_gt hp) (rightKrausBranchMass_nonneg ψ K i)
      have hd : (if hp : 0 < rightKrausBranchMass ψ K i
          then rightKrausBranchEntropy ψ K i hp else 0) = 0 := by rw [dif_neg hp]
      rw [hd, hz, zero_mul, zero_mul]
  rw [rightKrausAverageBranchEntropy, hsum]
  exact hconc'.trans_eq (entropy_eq_firstMarginalMixed ψ hψ).symm

theorem rightKrausAverageEntropyBound (D E n : ℕ) (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument E n) (hψ : Normalized ψ) :
    rightKrausAverageBranchEntropy ψ K ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ :=
  rightKrausAverageBranchEntropy_le_of_concavity
    (vonNeumannEntropyConcaveForMixtures D) ψ K hψ

inductive LoccParty where
  | alice
  | bob

inductive AlternatingLoccTree (D E : ℕ) : LoccParty → Type where
  | halt {side : LoccParty} : AlternatingLoccTree D E side
  | stepA (n : ℕ) (K : KrausInstrument D n)
      (next : Fin n → AlternatingLoccTree D E .bob) : AlternatingLoccTree D E .alice
  | stepB (n : ℕ) (K : KrausInstrument E n)
      (next : Fin n → AlternatingLoccTree D E .alice) : AlternatingLoccTree D E .bob

noncomputable def alternatingTreeToProtocol {D E : ℕ} {side : LoccParty} :
    AlternatingLoccTree D E side → Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E
  | .halt => .halt
  | .stepA n K next => .stepA n K.op (fun i => alternatingTreeToProtocol (next i))
  | .stepB n K next => .stepB n K.op (fun i => alternatingTreeToProtocol (next i))

theorem alternatingTreeToProtocol_complete {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) :
    Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccComplete (alternatingTreeToProtocol T) := by
  induction T with
  | halt => trivial
  | @stepA n K next ih => exact ⟨K.hcomplete, fun i => ih i⟩
  | @stepB n K next ih => exact ⟨K.hcomplete, fun i => ih i⟩

noncomputable def alternatingTreeAverageEntropy {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) : ℝ :=
  match T with
  | .halt => Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ
  | .stepA n K next =>
      ∑ i, krausBranchMass ψ K i *
        (if hp : 0 < krausBranchMass ψ K i then
            alternatingTreeAverageEntropy (next i) (normalizedKrausBranch ψ K i hp)
              (normalizedKrausBranch_normalized ψ K i hp)
          else 0)
  | .stepB n K next =>
      ∑ i, rightKrausBranchMass ψ K i *
        (if hp : 0 < rightKrausBranchMass ψ K i then
            alternatingTreeAverageEntropy (next i) (normalizedRightKrausBranch ψ K i hp)
              (normalizedRightKrausBranch_normalized ψ K i hp)
          else 0)

theorem alternatingTreeAverageEntropy_le {D E : ℕ} {side : LoccParty} :
    ∀ (T : AlternatingLoccTree D E side) (ψ : QState (Fin D × Fin E))
      (hψ : Normalized ψ),
      alternatingTreeAverageEntropy T ψ hψ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ := by
  intro T
  induction T with
  | halt =>
      intro ψ hψ
      exact le_rfl
  | @stepA n K next ih =>
      intro ψ hψ
      simp only [alternatingTreeAverageEntropy]
      calc (∑ i, krausBranchMass ψ K i *
            (if hp : 0 < krausBranchMass ψ K i then
                alternatingTreeAverageEntropy (next i) (normalizedKrausBranch ψ K i hp)
                  (normalizedKrausBranch_normalized ψ K i hp)
              else 0))
          ≤ ∑ i, krausBranchMass ψ K i *
            (if hp : 0 < krausBranchMass ψ K i then krausBranchEntropy ψ K i hp else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hp : 0 < krausBranchMass ψ K i
            · simp only [hp, dif_pos]
              exact mul_le_mul_of_nonneg_left (ih i _ _)
                (krausBranchMass_nonneg ψ K i)
            · simp only [hp]
              exact le_rfl
        _ = krausAverageBranchEntropy ψ K := rfl
        _ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ :=
          generalKrausAverageEntropyBound D E n ψ K hψ
  | @stepB n K next ih =>
      intro ψ hψ
      simp only [alternatingTreeAverageEntropy]
      calc (∑ i, rightKrausBranchMass ψ K i *
            (if hp : 0 < rightKrausBranchMass ψ K i then
                alternatingTreeAverageEntropy (next i) (normalizedRightKrausBranch ψ K i hp)
                  (normalizedRightKrausBranch_normalized ψ K i hp)
              else 0))
          ≤ ∑ i, rightKrausBranchMass ψ K i *
            (if hp : 0 < rightKrausBranchMass ψ K i then
                rightKrausBranchEntropy ψ K i hp else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hp : 0 < rightKrausBranchMass ψ K i
            · simp only [hp, dif_pos]
              exact mul_le_mul_of_nonneg_left (ih i _ _)
                (rightKrausBranchMass_nonneg ψ K i)
            · simp only [hp]
              exact le_rfl
        _ = rightKrausAverageBranchEntropy ψ K := rfl
        _ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ :=
          rightKrausAverageEntropyBound D E n ψ K hψ

noncomputable def alternatingTreeCommunicationBits {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) : ℕ :=
  Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccBits (alternatingTreeToProtocol T)

noncomputable def alternatingTreeOutcomePaths {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) : ℕ :=
  Qatlib.Concepts.QuditTeleport.ResourceIff.LoccLeafCount (alternatingTreeToProtocol T)

theorem alternatingTreeOutcomePaths_le_two_pow_communication {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) :
    alternatingTreeOutcomePaths T ≤ 2 ^ alternatingTreeCommunicationBits T :=
  Qatlib.Concepts.QuditTeleport.ResourceIff.loccLeafCount_le_two_pow_loccBits (alternatingTreeToProtocol T)

noncomputable def pureStateBornMass {I : Type*} [Fintype I] (ψ : QState I) : ℝ :=
  ∑ j, ‖ψ j‖ ^ 2

theorem pureStateBornMass_nonneg {I : Type*} [Fintype I] (ψ : QState I) :
    0 ≤ pureStateBornMass ψ := by
  unfold pureStateBornMass
  exact Finset.sum_nonneg fun j _ => by positivity

theorem pureStateBornMass_eq_zero_iff {I : Type*} [Fintype I] (ψ : QState I) :
    pureStateBornMass ψ = 0 ↔ ∀ j, ψ j = 0 := by
  unfold pureStateBornMass
  constructor
  · intro h j
    have hz : ‖ψ j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (f := fun x => ‖ψ x‖ ^ 2)
        (fun x _ => by positivity)).mp h j (Finset.mem_univ j)
    exact norm_eq_zero.mp (by simpa using hz)
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg (f := fun x => ‖ψ x‖ ^ 2)
      (fun x _ => by positivity)).mpr
    intro j _
    simp [h j]

noncomputable def normalizedPureState {I : Type*} [Fintype I] (ψ : QState I)
    (hp : 0 < pureStateBornMass ψ) : QState I :=
  ((Real.sqrt (pureStateBornMass ψ))⁻¹ : ℝ) • ψ

theorem normalizedPureState_normalized {I : Type*} [Fintype I] (ψ : QState I)
    (hp : 0 < pureStateBornMass ψ) : Normalized (normalizedPureState ψ hp) := by
  have hp0 : 0 < Real.sqrt (pureStateBornMass ψ) := Real.sqrt_pos.2 hp
  have hnorm : (∑ j, ‖ψ j‖ ^ 2) = pureStateBornMass ψ := rfl
  have hsq : ∀ j, ‖((Real.sqrt (pureStateBornMass ψ))⁻¹ : ℝ) • ψ j‖ ^ 2 =
      ((Real.sqrt (pureStateBornMass ψ))⁻¹) ^ 2 * (‖ψ j‖ ^ 2) := by
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp0), pow_two]
    ring
  unfold Normalized normalizedPureState
  calc (∑ j, ‖((Real.sqrt (pureStateBornMass ψ))⁻¹ : ℝ) • ψ j‖ ^ 2)
      = ∑ j, ((Real.sqrt (pureStateBornMass ψ))⁻¹) ^ 2 * (‖ψ j‖ ^ 2) :=
        Finset.sum_congr rfl fun j _ => hsq j
    _ = ((Real.sqrt (pureStateBornMass ψ))⁻¹) ^ 2 * (∑ j, ‖ψ j‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ = ((Real.sqrt (pureStateBornMass ψ))⁻¹) ^ 2 * pureStateBornMass ψ := by rw [hnorm]
    _ = 1 := by rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ (ne_of_gt hp)]

theorem pureStateBornMass_eq_trace_outerProduct {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    pureStateBornMass ψ = (Matrix.trace (outerProduct ψ)).re := by
  rw [trace_outerProduct]
  rfl

noncomputable def protocolLeafStates {D E : ℕ} (P : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E)
    (ψ : QState (Fin D × Fin E)) : List (QState (Fin D × Fin E)) :=
  (Qatlib.Concepts.QuditTeleport.ResourceIff.loccLeafOps P).map fun p => ApplyGate (TensorGate p.1 p.2) ψ

noncomputable def protocolLeafBornWeights {D E : ℕ} (P : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E)
    (ψ : QState (Fin D × Fin E)) : List ℝ :=
  (protocolLeafStates P ψ).map pureStateBornMass

noncomputable def alternatingTreeLeafStates {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) (ψ : QState (Fin D × Fin E)) :
    List (QState (Fin D × Fin E)) :=
  protocolLeafStates (alternatingTreeToProtocol T) ψ

noncomputable def alternatingTreeLeafBornWeights {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) (ψ : QState (Fin D × Fin E)) : List ℝ :=
  protocolLeafBornWeights (alternatingTreeToProtocol T) ψ

theorem loccChannel_outerProduct_eq_sum_protocolLeafStates {D E : ℕ}
    (P : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E) (ψ : QState (Fin D × Fin E)) :
    Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccChannel P (outerProduct ψ) =
      ((protocolLeafStates P ψ).map fun φ => outerProduct φ).sum := by
  rw [Qatlib.Concepts.QuditTeleport.ResourceIff.loccChannel_eq_sum_leafOps]
  simp only [protocolLeafStates, List.map_map]
  congr 1
  exact List.map_congr_left fun (p : Operator D × Operator E) _ =>
    (outerProduct_applyGate_matrix (TensorGate p.1 p.2) ψ).symm

theorem protocolLeafBornWeights_sum_eq_one {D E : ℕ} (P : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E)
    (hP : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccComplete P) (ψ : QState (Fin D × Fin E))
    (hψ : Normalized ψ) : (protocolLeafBornWeights P ψ).sum = 1 := by
  have htrace_list : ∀ l : List (QState (Fin D × Fin E)),
      (((l.map pureStateBornMass).sum : ℝ) : ℂ) =
        Matrix.trace ((l.map outerProduct).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons φ l ih =>
        simp only [List.map_cons, List.sum_cons, Complex.ofReal_add, ih,
          Matrix.trace_add, trace_outerProduct, pureStateBornMass]
  have hinput : Matrix.trace (outerProduct ψ) = 1 := by
    rw [trace_outerProduct]
    have hnorm : (∑ j, ‖ψ j‖ ^ 2 : ℝ) = 1 := hψ
    rw [hnorm]
    norm_num
  have hcast : (((protocolLeafBornWeights P ψ).sum : ℝ) : ℂ) = 1 := by
    unfold protocolLeafBornWeights
    rw [htrace_list, ← loccChannel_outerProduct_eq_sum_protocolLeafStates,
      trace_loccChannel P hP, hinput]
  exact_mod_cast hcast

noncomputable def alternatingTreeExecutionStates {D E : ℕ} {side : LoccParty}
    (T : AlternatingLoccTree D E side) (ψ : QState (Fin D × Fin E)) :
    List (QState (Fin D × Fin E)) :=
  match T with
  | .halt => [ψ]
  | .stepA n K next => Finset.univ.toList.flatMap fun i =>
      alternatingTreeExecutionStates (next i) (krausBranch ψ K i)
  | .stepB n K next => Finset.univ.toList.flatMap fun i =>
      alternatingTreeExecutionStates (next i) (rightKrausBranch ψ K i)

theorem alternatingTreeExecutionStates_eq_leafStates {D E : ℕ} {side : LoccParty} :
    ∀ (T : AlternatingLoccTree D E side) (ψ : QState (Fin D × Fin E)),
      alternatingTreeExecutionStates T ψ = alternatingTreeLeafStates T ψ := by
  intro T
  induction T with
  | halt =>
      intro ψ
      simp [alternatingTreeExecutionStates, alternatingTreeLeafStates, protocolLeafStates,
        alternatingTreeToProtocol, Qatlib.Concepts.QuditTeleport.ResourceIff.loccLeafOps, tensorGate_one,
        applyGate_one]
  | @stepA n K next ih =>
      intro ψ
      simp only [alternatingTreeExecutionStates, alternatingTreeLeafStates,
        protocolLeafStates, alternatingTreeToProtocol, Qatlib.Concepts.QuditTeleport.ResourceIff.loccLeafOps,
        List.map_flatMap, List.map_map]
      apply List.flatMap_congr
      intro i hi
      rw [ih i (krausBranch ψ K i)]
      apply List.map_congr_left
      intro p hp
      simp only [krausBranch, Function.comp_apply, ← applyGate_mul, tensorGate_mul,
        Matrix.mul_one]
  | @stepB n K next ih =>
      intro ψ
      simp only [alternatingTreeExecutionStates, alternatingTreeLeafStates,
        protocolLeafStates, alternatingTreeToProtocol, Qatlib.Concepts.QuditTeleport.ResourceIff.loccLeafOps,
        List.map_flatMap, List.map_map]
      apply List.flatMap_congr
      intro i hi
      rw [ih i (rightKrausBranch ψ K i)]
      apply List.map_congr_left
      intro p hp
      simp only [rightKrausBranch, Function.comp_apply, ← applyGate_mul, tensorGate_mul,
        Matrix.mul_one]

theorem frontier1 (D E : ℕ) :
    (∀ (n : ℕ) (ψ : QState (Fin D × Fin E)) (K : KrausInstrument E n)
      (hψ : Normalized ψ),
      rightKrausAverageBranchEntropy ψ K ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ) ∧
    (∀ (side : LoccParty) (T : AlternatingLoccTree D E side)
      (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
      alternatingTreeAverageEntropy T ψ hψ ≤ Qatlib.Concepts.UnbiasedBases.ThreeBasis.entropy ψ hψ) ∧
    (∀ (side : LoccParty) (T : AlternatingLoccTree D E side),
      Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccComplete (alternatingTreeToProtocol T)) ∧
    (∀ (side : LoccParty) (T : AlternatingLoccTree D E side)
      (ψ : QState (Fin D × Fin E)),
      alternatingTreeExecutionStates T ψ = alternatingTreeLeafStates T ψ) ∧
    (∀ (side : LoccParty) (T : AlternatingLoccTree D E side)
      (ψ φ : QState (Fin D × Fin E)), φ ∈ alternatingTreeLeafStates T ψ →
      ∀ (hp : 0 < pureStateBornMass φ), Normalized (normalizedPureState φ hp)) ∧
    (∀ (side : LoccParty) (T : AlternatingLoccTree D E side)
      (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ),
      (alternatingTreeLeafBornWeights T ψ).sum = 1) ∧
    (∀ (P : Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccProtocol D E) (ψ : QState (Fin D × Fin E)),
      Qatlib.Concepts.FiniteLocc.LOCCProgram.LoccChannel P (outerProduct ψ) =
        ((protocolLeafStates P ψ).map fun φ => outerProduct φ).sum) ∧
    (∀ (side : LoccParty) (T : AlternatingLoccTree D E side),
      alternatingTreeOutcomePaths T ≤ 2 ^ alternatingTreeCommunicationBits T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n ψ K hψ
    exact rightKrausAverageEntropyBound D E n ψ K hψ
  · intro side T ψ hψ
    exact alternatingTreeAverageEntropy_le T ψ hψ
  · intro side T
    exact alternatingTreeToProtocol_complete T
  · intro side T ψ
    exact alternatingTreeExecutionStates_eq_leafStates T ψ
  · intro side T ψ φ hφ hp
    exact normalizedPureState_normalized φ hp
  · intro side T ψ hψ
    exact protocolLeafBornWeights_sum_eq_one _ (alternatingTreeToProtocol_complete T) ψ hψ
  · intro P ψ
    exact loccChannel_outerProduct_eq_sum_protocolLeafStates P ψ
  · intro side T
    exact alternatingTreeOutcomePaths_le_two_pow_communication T

end Qatlib.Concepts.Entanglement.Separability.LoccEntropyAverageStep
