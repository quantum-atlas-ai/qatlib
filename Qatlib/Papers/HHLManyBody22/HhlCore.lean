/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.NormalizedEnergy
import Qatlib.Papers.HHLManyBody22.AdaptHhl.ActualGrid

/-!
# Combining exact grid HHL with HOM energy readout

The module connects conditional state normalization and exact grid HHL scaling to the tensor HOM
circuit. Reindexing identities allow a finite excitation basis to be represented by bit strings
while preserving state mass and the overlap readout.

Under the stated Hermitian block, invertibility, and nonzero coupling hypotheses,
`actual_hhl_hom_lcc_readout` combines the HHL output and success probability with the magnitude
of the projected LCC energy. `actual_hhl_hom_probability_law` verifies nonnegative Born weights
summing to one for the corresponding normalized circuit inputs. See [BaskaranEtAl2023].

## Main statements

* `actual_hhl_hom_lcc_readout`: For a Hermitian LCC matrix with zero reference diagonal, the
  stated exact grid excitation block, and nonzero coupling, identifies the HHL output and
  probability and reconstructs the projected energy magnitude from the normalized inverse
  solution's HOM parity readout.
* `actual_hhl_hom_probability_law`: For nonzero input and an invertible rescaled grid matrix
  with positive `d`, the HOM circuit on the normalized input and inverse solution has
  nonnegative Born weights summing to one.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.HhlCore
open Matrix
open Qatlib.Papers.HHLManyBody22.HomOverlap
open Qatlib.Papers.HHLManyBody22.LccEnergy
open Qatlib.Papers.HHLManyBody22.AdaptHhl
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

/-- The HOM mass of a finite state equals its total Born probability. -/
theorem homMass_eq_measureProb {I : Type} [Fintype I] (w : I→ℂ) :
    homMass w=MeasureProb w Finset.univ := by
  simp only [homMass,MeasureProb,BornProb,Complex.normSq_eq_norm_sq]

/-- Normalizing a nonzero state with `homNormalize` gives a nonzero state. -/
theorem homNormalize_ne_zero {I : Type} [Fintype I] (w : I→ℂ) (hw : w≠0) :
    homNormalize w≠0 := by
  intro hz
  have hm := homNormalize_mass w hw
  rw [hz] at hm
  simp [homMass] at hm

/-- For a nonzero state, `ConditionalState` returns `some (homNormalize w)`. -/
theorem conditionalState_homNormalize {I : Type} [Fintype I] [DecidableEq I]
    (w : I→ℂ) (hw : w≠0) : ConditionalState w=some (homNormalize w) := by
  have hp : 0<MeasureProb w Finset.univ := by
    rw [← homMass_eq_measureProb]
    exact Real.sqrt_pos.mp (homNorm_pos w hw)
  rw [ConditionalState,if_pos hp]
  congr 1
  funext i
  simp [PostMeasure,homNormalize,homNorm,homMass_eq_measureProb,Collapse,projector_univ,ApplyGate,Matrix.one_mulVec]

/-- Reindexing two states by a bit string equivalence makes the tensor HOM parity weighted Born
sum equal the squared norm of their original inner product. -/
theorem hom_actual_reindexed_overlap {I : Type} [Fintype I] (n : ℕ)
    (e : I≃(Fin n→Bool)) (u v : I→ℂ) :
    (∑z,homParity n z*Complex.normSq ((homTensor n*ᵥ
      homJoint n (u∘e.symm) (v∘e.symm)) z))=Complex.normSq (star u ⬝ᵥ v) := by
  rw [hom_actual_born_overlap]
  congr 1
  exact e.symm.sum_comp (fun i => star (u i)*v i)

/-- For positive `d`, an invertible grid HHL matrix gives an invertible `adaptGridMatrix`. -/
theorem adapt_physical_det_isUnit {D : ℕ} (nr : ℕ) (d : ℝ) (hd : 0<d)
    (label : Fin D→Fin (2^nr)) (V : Matrix (Fin D) (Fin D) ℂ)
    (hG : IsUnit (gridHHLMatrix label V).det) : IsUnit (adaptGridMatrix nr d label V).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [adaptGridMatrix,Matrix.det_smul]
  apply mul_ne_zero
  · apply pow_ne_zero
    exact_mod_cast (ne_of_gt (mul_pos (by positivity) hd))
  · exact isUnit_iff_ne_zero.mp hG

/-- An invertible matrix sends the normalization of a nonzero vector to a nonzero inverse
solution. -/
theorem hom_actual_inverse_ne_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : IsUnit A.det) (b : I→ℂ) (hb : b≠0) :
    A⁻¹*ᵥhomNormalize b≠0 := by
  intro hz
  have hm := congrArg (fun x => A*ᵥx) hz
  (try dsimp only at hm)
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hA,Matrix.one_mulVec,
    Matrix.mulVec_zero] at hm
  exact homNormalize_ne_zero b hb hm

/-- For a Hermitian LCC matrix with zero reference diagonal, the stated exact grid excitation
block, and nonzero coupling, identifies the HHL output and probability and reconstructs the
projected energy magnitude from the normalized inverse solution's HOM parity readout. See
[BaskaranEtAl2023]. -/
theorem actual_hhl_hom_lcc_readout {D : ℕ} (n nr : ℕ) (e : Fin D≃(Fin n→Bool))
    (d : ℝ) (hd : 0<d) (label : Fin D→Fin (2^nr))
    (V : Matrix (Fin D) (Fin D) ℂ) (hV : V∈Matrix.unitaryGroup (Fin D) ℂ)
    (hG : IsUnit (gridHHLMatrix label V).det)
    (H : Matrix (Option (Fin D)) (Option (Fin D)) ℂ) (hH : H.IsHermitian)
    (hzero : H none none=0) (hblock : excitationBlock H=adaptGridMatrix nr d label V)
    (hb : lccCoupling H≠0) :
    let u := homNormalize (lccCoupling H)
    let x := (adaptGridMatrix nr d label V)⁻¹*ᵥu
    gridHHLOutput label V (hhlCoefficient nr) u=some (homNormalize x) ∧
    gridHHLProbability label V (hhlCoefficient nr) u=d^2*homMass x ∧
    ‖projectedLccEnergy H (physicalLccAmplitudes H)‖=
      homNorm (lccCoupling H)^2*homNorm x*
        Real.sqrt (∑z,homParity n z*Complex.normSq ((homTensor n*ᵥ
          homJoint n (u∘e.symm) ((homNormalize x)∘e.symm)) z)) := by
  (try dsimp only)
  have hA := adapt_physical_det_isUnit nr d hd label V hG
  have hx := hom_actual_inverse_ne_zero _ hA _ hb
  obtain ⟨hp,ho⟩ :=
      adapt_actual_probability_output nr d hd label V hV hG (homNormalize (lccCoupling H))
  refine ⟨ho.trans (conditionalState_homNormalize _ hx),?_,?_⟩
  · simpa only [homMass_eq_measureProb] using! hp
  · have hHA : IsUnit (excitationBlock H).det := hblock.symm ▸ hA
    rw [(actual_lcc_energy_producer H hH hzero hHA).2,lccCorrelationEnergy,norm_neg,hblock,
      hom_normalized_inverse_pairing _ _ hb hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (show 0≤homNorm _ from Real.sqrt_nonneg _)),
      hom_actual_reindexed_overlap,Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

/-- The HOM mass of the joint tensor input is the product of the two input masses. -/
theorem homJoint_actual_mass (n : ℕ) (u v : (Fin n→Bool)→ℂ) :
    homMass (homJoint n u v)=homMass u*homMass v := by
  simp only [homMass,homJoint,Complex.normSq_mul]
  change (∑y,(fun p : ((Fin n→Bool)×(Fin n→Bool)) =>
    Complex.normSq (u p.1)*Complex.normSq (v p.2)) (homPairEquiv n y)) = _
  rw [Equiv.sum_comp (homPairEquiv n) (fun p : ((Fin n→Bool)×(Fin n→Bool)) =>
    Complex.normSq (u p.1)*Complex.normSq (v p.2)),Fintype.sum_prod_type,Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- If both HOM inputs have mass one, the circuit's total Born mass is one. -/
theorem hom_actual_born_total (n : ℕ) (u v : (Fin n→Bool)→ℂ)
    (hu : homMass u=1) (hv : homMass v=1) :
    (∑z,Complex.normSq ((homTensor n*ᵥhomJoint n u v) z))=1 := by
  have hpair : homMass (homJoint n u v)=1 := by rw [homJoint_actual_mass,hu,hv,one_mul]
  have hn : Normalized (homJoint n u v) := by
    simpa only [homMass,Normalized,Complex.normSq_eq_norm_sq] using! hpair
  have hout := normalized_applyGate (homTensor_unitary n) hn
  simpa only [Normalized,ApplyGate,Complex.normSq_eq_norm_sq] using! hout

/-- Reindexing a state along an equivalence preserves its HOM mass. -/
theorem homMass_reindex {I J : Type} [Fintype I] [Fintype J] (e : I≃J) (w : I→ℂ) :
    homMass (w∘e.symm)=homMass w :=
  e.symm.sum_comp (fun i => Complex.normSq (w i))

/-- For nonzero input and an invertible rescaled grid matrix with positive `d`, the HOM circuit
on the normalized input and inverse solution has nonnegative Born weights summing to one.
See [BaskaranEtAl2023]. -/
theorem actual_hhl_hom_probability_law {D : ℕ} (n nr : ℕ) (e : Fin D≃(Fin n→Bool))
    (d : ℝ) (hd : 0<d) (label : Fin D→Fin (2^nr))
    (V : Matrix (Fin D) (Fin D) ℂ) (hG : IsUnit (gridHHLMatrix label V).det)
    (b : Fin D→ℂ) (hb : b≠0) :
    let u := homNormalize b
    let v := homNormalize ((adaptGridMatrix nr d label V)⁻¹*ᵥu)
    (∀z,0≤Complex.normSq ((homTensor n*ᵥhomJoint n (u∘e.symm) (v∘e.symm)) z)) ∧
    (∑z,Complex.normSq ((homTensor n*ᵥhomJoint n (u∘e.symm) (v∘e.symm)) z))=1 := by
  (try dsimp only)
  refine ⟨fun z => Complex.normSq_nonneg _,?_⟩
  have hx := hom_actual_inverse_ne_zero _ (adapt_physical_det_isUnit nr d hd label V hG) b hb
  apply hom_actual_born_total
  · rw [homMass_reindex,homNormalize_mass b hb]
  · rw [homMass_reindex,homNormalize_mass _ hx]

end Qatlib.Papers.HHLManyBody22.HhlCore
