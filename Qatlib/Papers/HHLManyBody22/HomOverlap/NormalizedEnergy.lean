/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.HomOverlap.BornReadout
import Qatlib.Papers.HHLManyBody22.LccEnergy.ActualLcc

/-!
# Normalized overlaps and the magnitude of LCC energy

The finite state quantities `homMass`, `homNorm`, and `homNormalize` provide normalization
identities for the HOM circuit. `hom_normalized_inverse_pairing` factors an inverse quadratic
form into input and solution norms and a normalized overlap.

`hom_actual_lcc_energy_magnitude` combines this factorization with the actual parity readout,
while `hom_actual_lcc_energy_sign` supplies a negative real part under positive definiteness and
nonzero coupling. See [BaskaranEtAl2023].

## Main statements

* `hom_normalized_inverse_pairing`: For nonzero `b` and nonzero inverse solution to its
  normalization, the inverse quadratic form factors as `homNorm b` squared times the normalized
  inverse solution norm times the overlap of the normalized vectors.
* `hom_actual_lcc_energy_magnitude`: For a Hermitian LCC matrix with zero reference diagonal,
  invertible excitation block, nonzero coupling, and nonzero normalized inverse solution, the
  projected energy magnitude equals the displayed product of norms and the square root of the
  HOM parity weighted Born sum.
* `hom_actual_lcc_energy_sign`: For a Hermitian LCC matrix with zero reference diagonal,
  positive definite excitation block, and nonzero coupling, the physical projected energy has
  strictly negative real part.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace Qatlib.Papers.HHLManyBody22.HomOverlap
open Matrix
open Qatlib.Papers.HHLManyBody22.LccEnergy

/-- The sum of the squared complex magnitudes of a finite state. -/
def homMass {I : Type} [Fintype I] (w : I→ℂ) : ℝ := ∑i,Complex.normSq (w i)

/-- The square root of `homMass w`. -/
def homNorm {I : Type} [Fintype I] (w : I→ℂ) : ℝ := Real.sqrt (homMass w)

/-- The vector `w` scaled by the reciprocal of its HOM norm. -/
def homNormalize {I : Type} [Fintype I] (w : I→ℂ) : I→ℂ :=
  ((homNorm w:ℂ)⁻¹) • w

/-- The HOM mass of a state is nonnegative. -/
theorem homMass_nonneg {I : Type} [Fintype I] (w : I→ℂ) : 0≤homMass w :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (w i))

/-- A nonzero state has strictly positive HOM norm. -/
theorem homNorm_pos {I : Type} [Fintype I] (w : I→ℂ) (hw : w≠0) : 0<homNorm w := by
  have hex : ∃i,w i≠0 := by
    by_contra! h
    exact hw (funext h)
  obtain ⟨i,hi⟩ := hex
  apply Real.sqrt_pos.mpr
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (w j))
    ⟨i,Finset.mem_univ i,Complex.normSq_pos.mpr hi⟩

/-- Normalizing a nonzero state gives HOM mass one. -/
theorem homNormalize_mass {I : Type} [Fintype I] (w : I→ℂ) (hw : w≠0) :
    homMass (homNormalize w)=1 := by
  have hn := homNorm_pos w hw
  have hn2 : homNorm w^2=homMass w := Real.sq_sqrt (homMass_nonneg w)
  simp only [homMass,homNormalize,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,
    Complex.normSq_inv,Complex.normSq_ofReal,← Finset.mul_sum]
  rw [← pow_two]
  change (homNorm w^2)⁻¹*homMass w=1
  rw [← hn2,inv_mul_cancel₀ (pow_ne_zero _ hn.ne')]

/-- The inner product of two normalized vectors is their original inner product divided by the
product of their HOM norms. -/
theorem homNormalize_pairing {I : Type} [Fintype I] (u v : I→ℂ) :
    star (homNormalize u) ⬝ᵥ homNormalize v=
      ((homNorm u:ℂ)*(homNorm v:ℂ))⁻¹*(star u ⬝ᵥ v) := by
  simp only [homNormalize,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    dotProduct_smul,smul_dotProduct,smul_eq_mul,_root_.mul_inv_rev]
  ring

/-- For nonzero `b` and nonzero inverse solution to its normalization, the inverse quadratic
form factors as `homNorm b` squared times the normalized inverse solution norm times the
overlap of the normalized vectors. -/
theorem hom_normalized_inverse_pairing {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (b : I→ℂ)
    (hb : b≠0) (hx : A⁻¹*ᵥhomNormalize b≠0) :
    star b ⬝ᵥ (A⁻¹*ᵥb)=
      (((homNorm b)^2*homNorm (A⁻¹*ᵥhomNormalize b):ℝ):ℂ) *
        (star (homNormalize b) ⬝ᵥ homNormalize (A⁻¹*ᵥhomNormalize b)) := by
  have hb0 : (homNorm b:ℂ)≠0 := by exact_mod_cast (homNorm_pos b hb).ne'
  have hx0 : (homNorm (A⁻¹*ᵥhomNormalize b):ℂ)≠0 := by exact_mod_cast (homNorm_pos _ hx).ne'
  rw [homNormalize_pairing]
  have hsol : star b ⬝ᵥ (A⁻¹*ᵥhomNormalize b)=
      (homNorm b:ℂ)⁻¹*(star b ⬝ᵥ (A⁻¹*ᵥb)) := by
    rw [homNormalize,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  rw [hsol]
  push_cast
  field_simp

/-- For a Hermitian LCC matrix with zero reference diagonal, invertible excitation block,
nonzero coupling, and nonzero normalized inverse solution, the projected energy magnitude
equals the displayed product of norms and the square root of the HOM parity weighted Born
sum. -/
theorem hom_actual_lcc_energy_magnitude (n : ℕ)
    (H : Matrix (Option (Fin n→Bool)) (Option (Fin n→Bool)) ℂ)
    (hH : H.IsHermitian) (hzero : H none none=0) (hA : IsUnit (excitationBlock H).det)
    (hb : lccCoupling H≠0)
    (hx : (excitationBlock H)⁻¹*ᵥhomNormalize (lccCoupling H)≠0) :
    ‖projectedLccEnergy H (physicalLccAmplitudes H)‖=
      (homNorm (lccCoupling H))^2*homNorm ((excitationBlock H)⁻¹*ᵥhomNormalize (lccCoupling H))*
        Real.sqrt (∑z,homParity n z*Complex.normSq ((homTensor n*ᵥ
          homJoint n (homNormalize (lccCoupling H))
            (homNormalize ((excitationBlock H)⁻¹*ᵥhomNormalize (lccCoupling H)))) z)) := by
  rw [(actual_lcc_energy_producer H hH hzero hA).2,lccCorrelationEnergy,norm_neg,
    hom_normalized_inverse_pairing _ _ hb hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (show 0≤homNorm ((excitationBlock H)⁻¹*ᵥhomNormalize (lccCoupling H)) from Real.sqrt_nonneg _)),hom_actual_born_overlap,
    Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

/-- For a Hermitian LCC matrix with zero reference diagonal, positive definite excitation block,
and nonzero coupling, the physical projected energy has strictly negative real part. -/
theorem hom_actual_lcc_energy_sign (n : ℕ)
    (H : Matrix (Option (Fin n→Bool)) (Option (Fin n→Bool)) ℂ)
    (hH : H.IsHermitian) (hzero : H none none=0) (hA : (excitationBlock H).PosDef)
    (hb : lccCoupling H≠0) :
    (projectedLccEnergy H (physicalLccAmplitudes H)).re<0 :=
  (actual_lcc_energy_real_negative H hH hzero hA hb).2

end Qatlib.Papers.HHLManyBody22.HomOverlap
