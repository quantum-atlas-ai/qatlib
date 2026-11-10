/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.LccEnergy.CorrelationEnergy
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
namespace Qatlib.Papers.HHLManyBody22.LccEnergy
open Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

def excitationBlock (H : Matrix (Option I) (Option I) ℂ) : Matrix I I ℂ :=
  fun i j => H (some i) (some j)

def lccCoupling (H : Matrix (Option I) (Option I) ℂ) : I→ℂ :=
  fun i => H (some i) none

def lccLinearState (t : I→ℂ) : Option I→ℂ := Option.elim' 1 t

def physicalLccAmplitudes (H : Matrix (Option I) (Option I) ℂ) : I→ℂ :=
  -(excitationBlock H)⁻¹ *ᵥ lccCoupling H

def projectedLccEnergy (H : Matrix (Option I) (Option I) ℂ) (t : I→ℂ) : ℂ :=
  (H *ᵥ lccLinearState t) none

omit [DecidableEq I] in

theorem lcc_excited_projection (H : Matrix (Option I) (Option I) ℂ) (t : I→ℂ) (i : I) :
    (H *ᵥ lccLinearState t) (some i)=lccCoupling H i+(excitationBlock H *ᵥ t) i := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_option,lccLinearState,Option.elim'_none,
    Option.elim'_some,mul_one,lccCoupling,excitationBlock]

omit [Fintype I] [DecidableEq I] in

theorem excitationBlock_hermitian (H : Matrix (Option I) (Option I) ℂ) (hH : H.IsHermitian) :
    (excitationBlock H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact hH.apply (some i) (some j)

theorem physical_lcc_residual_zero (H : Matrix (Option I) (Option I) ℂ)
    (hA : IsUnit (excitationBlock H).det) (i : I) :
    (H *ᵥ lccLinearState (physicalLccAmplitudes H)) (some i)=0 := by
  rw [lcc_excited_projection,physicalLccAmplitudes,Matrix.neg_mulVec,Matrix.mulVec_neg,
    Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hA,Matrix.one_mulVec]
  simp

omit [DecidableEq I] in

theorem projectedLccEnergy_pairing (H : Matrix (Option I) (Option I) ℂ) (hH : H.IsHermitian)
    (t : I→ℂ) : projectedLccEnergy H t=H none none+star (lccCoupling H) ⬝ᵥ t := by
  simp only [projectedLccEnergy,Matrix.mulVec,dotProduct,Fintype.sum_option,lccLinearState,
    Option.elim'_none,Option.elim'_some,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h := hH.apply none (some i)
  change H none (some i)*t i=star (H (some i) none)*t i
  rw [h]

theorem actual_lcc_energy_producer (H : Matrix (Option I) (Option I) ℂ) (hH : H.IsHermitian)
    (hzero : H none none=0) (hA : IsUnit (excitationBlock H).det) :
    (∀i,(H *ᵥ lccLinearState (physicalLccAmplitudes H)) (some i)=0) ∧
    projectedLccEnergy H (physicalLccAmplitudes H)=lccCorrelationEnergy (excitationBlock H) (lccCoupling H) := by
  refine ⟨physical_lcc_residual_zero H hA,?_⟩
  rw [projectedLccEnergy_pairing H hH,hzero,zero_add,physicalLccAmplitudes,Matrix.neg_mulVec,
    dotProduct_neg,lccCorrelationEnergy]

theorem actual_lcc_energy_real_negative (H : Matrix (Option I) (Option I) ℂ) (hH : H.IsHermitian)
    (hzero : H none none=0) (hA : (excitationBlock H).PosDef) (hb : lccCoupling H≠0) :
    star (projectedLccEnergy H (physicalLccAmplitudes H))=projectedLccEnergy H (physicalLccAmplitudes H) ∧
      (projectedLccEnergy H (physicalLccAmplitudes H)).re<0 := by
  have hunit : IsUnit (excitationBlock H).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  rw [(actual_lcc_energy_producer H hH hzero hunit).2]
  exact ⟨conj_lccCorrelationEnergy_eq_self hA.isHermitian hunit _,
    re_lccCorrelationEnergy_neg_of_posDef hA _ hb⟩

theorem actual_lcc_zero_coupling (H : Matrix (Option I) (Option I) ℂ)
    (hzero : H none none=0) (hb : lccCoupling H=0) :
    physicalLccAmplitudes H=0 ∧ projectedLccEnergy H (physicalLccAmplitudes H)=0 := by
  have ht : physicalLccAmplitudes H=0 := by simp [physicalLccAmplitudes,hb]
  refine ⟨ht,?_⟩
  rw [ht]
  simp only [projectedLccEnergy,Matrix.mulVec,dotProduct,Fintype.sum_option,lccLinearState,
    Option.elim'_none,Option.elim'_some,Pi.zero_apply,mul_one,mul_zero,Finset.sum_const_zero,add_zero,hzero]

end Qatlib.Papers.HHLManyBody22.LccEnergy
