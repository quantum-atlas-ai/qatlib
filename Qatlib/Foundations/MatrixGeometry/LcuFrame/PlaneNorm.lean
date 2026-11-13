/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Normalization

/-!
# The orthogonal companion in an LCU plane

Proves `phi1_orthonormal`: the residual state `phi1` is normalized and orthogonal to `phi0` when
constructed from a normalized Hamiltonian eigenstate with `E² < 1`. The block matrices are
assumed Hermitian and involutory, and the weights have unit squared sum. See [PoulinEtAl2018]
for related background.

## Main statements

* `phi1_orthonormal`: For normalized weights and a normalized eigenstate with `E² < 1`,
  Hermitian involutory blocks make `phi1` normalized and give `Inner (phi0 β φ) (phi1 β P φ E) =
  0`.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- For normalized weights and a normalized eigenstate with `E² < 1`, Hermitian involutory
blocks make `phi1` normalized and give `Inner (phi0 β φ) (phi1 β P φ E) = 0`. -/
theorem phi1_orthonormal (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hφ : Normalized φ)
    (hPH : ∀ j, (P j)ᴴ=P j) (hP2 : ∀ j, P j*P j=1)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    Normalized (phi1 β P φ E) ∧ Inner (phi0 β φ) (phi1 β P φ E)=0 := by
  have h00 : Inner (phi0 β φ) (phi0 β φ)=1 :=
    (normalized_iff_inner _).1 (phi0_normalized β φ hβ hφ)
  have h01 : Inner (phi0 β φ) (Vphi0 β P φ)=(E : ℂ) := by
    rw [← embedding_mulVec,inner_mulVec_left_rect,embedding_adjoint_Vphi0,heig,
      inner_smul_right', (normalized_iff_inner _).1 hφ,mul_one]
  have h10 : Inner (Vphi0 β P φ) (phi0 β φ)=(E : ℂ) := by
    rw [← inner_conj_symm',h01,star_ofReal']
  have h11 : Inner (Vphi0 β P φ) (Vphi0 β P φ)=1 := by
    rw [← select_phi0,inner_mulVec_left_rect,select_adjoint P hPH,
      Matrix.mulVec_mulVec,select_square P hP2,Matrix.one_mulVec,h00]
  let c : ℂ := (Real.sqrt (1-E^2) : ℂ)⁻¹
  have hd : 0<1-E^2 := by nlinarith
  have hcc : (starRingEnd ℂ) c*c= (((1-E^2 : ℝ) : ℂ))⁻¹ := by
    dsimp [c]
    rw [map_inv₀,star_ofReal',← Complex.ofReal_inv,← Complex.ofReal_mul,← mul_inv,
      Real.mul_self_sqrt hd.le,Complex.ofReal_inv]
  have hphi : phi1 β P φ E=c • (Vphi0 β P φ-(E : ℂ) • phi0 β φ) := rfl
  have hz : (1 : ℂ)-(E : ℂ)^2 ≠ 0 := by exact_mod_cast hd.ne'
  constructor
  · apply (normalized_iff_inner _).2
    rw [hphi,inner_smul_left',inner_smul_right',← mul_assoc,hcc,
      inner_sub_left',inner_sub_right',inner_sub_right',inner_smul_left',inner_smul_left',
      inner_smul_right',inner_smul_right',star_ofReal',h00,h01,h10,h11]
    push_cast
    field_simp [hz]
    ring
  · rw [hphi,inner_smul_right',inner_sub_right',inner_smul_right',h01,h00]
    ring

end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
