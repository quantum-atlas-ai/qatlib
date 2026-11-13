/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Walk

/-!
# Eigenphases of the LCU walk

Computes the action of `walk` on `phiP` and `phiM`, with eigenvalues `E ± i√(1 - E²)`. The
theorem `actual_eigenphase` expresses these scalars as exponentials with phases `± arccos E`;
`full_walk_eigenvectors` packages unitarity and normalized eigenvectors under the stated
hypotheses. See [PoulinEtAl2018] for related background.

## Main statements

* `actual_eigenphase`: When `E² < 1`, the scalars `E ± i√(1 - E²)` equal `exp(± i arccos E)`.
* `full_walk_eigenvectors`: For normalized weights and a normalized eigenstate of the
  Hamiltonian with Hermitian involutory blocks and `E² < 1`, the walk is unitary and the two
  phase states have unit Hilbert norm and eigenvalues `exp(± i arccos E)`; also `cos (arccos E)
  = E` [PoulinEtAl2018].

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- For normalized weights, involutory blocks, and a Hamiltonian eigenstate with `E² < 1`, the
walk acts on `phiP` by the scalar `E + i√(1 - E²)`. -/
theorem walk_phiP (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hP2 : ∀ j, P j*P j=1)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    walk β P *ᵥ phiP β P φ E =
      ((E : ℂ)+Complex.I*(Real.sqrt (1-E^2) : ℂ)) • phiP β P φ E := by
  change walk β P *ᵥ (invSqrt2 • (phi0 β φ + Complex.I • phi1 β P φ E)) = _
  rw [Matrix.mulVec_smul,Matrix.mulVec_add,Matrix.mulVec_smul,
    walk_phi0 β P φ E hβ heig hE,walk_phi1 β P φ E hβ hP2 heig hE]
  ext i
  simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,phiP,smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- For normalized weights, involutory blocks, and a Hamiltonian eigenstate with `E² < 1`, the
walk acts on `phiM` by the scalar `E - i√(1 - E²)`. -/
theorem walk_phiM (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hP2 : ∀ j, P j*P j=1)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    walk β P *ᵥ phiM β P φ E =
      ((E : ℂ)-Complex.I*(Real.sqrt (1-E^2) : ℂ)) • phiM β P φ E := by
  change walk β P *ᵥ (invSqrt2 • (phi0 β φ - Complex.I • phi1 β P φ E)) = _
  rw [Matrix.mulVec_smul,Matrix.mulVec_sub,Matrix.mulVec_smul,
    walk_phi0 β P φ E hβ heig hE,walk_phi1 β P φ E hβ hP2 heig hE]
  ext i
  simp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,phiM,smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

omit [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] in

/-- When `E² < 1`, the scalars `E ± i√(1 - E²)` equal `exp(± i arccos E)`. -/
theorem actual_eigenphase (E : ℝ) (hE : E^2<1) :
    (E : ℂ)+Complex.I*(Real.sqrt (1-E^2) : ℂ) =
      Complex.exp ((Real.arccos E : ℂ)*Complex.I) ∧
    (E : ℂ)-Complex.I*(Real.sqrt (1-E^2) : ℂ) =
      Complex.exp (-(Real.arccos E : ℂ)*Complex.I) := by
  have hlo : -1 ≤ E := by nlinarith
  have hhi : E ≤ 1 := by nlinarith
  constructor
  · rw [Complex.exp_ofReal_mul_I,Real.cos_arccos hlo hhi,Real.sin_arccos]
    ring
  · rw [show -(Real.arccos E : ℂ)*Complex.I=((-Real.arccos E : ℝ) : ℂ)*Complex.I by push_cast;ring,
      Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg,Real.cos_arccos hlo hhi,Real.sin_arccos]
    push_cast
    ring

/-- For normalized weights and a normalized eigenstate of the Hamiltonian with Hermitian
involutory blocks and `E² < 1`, the walk is unitary and the two phase states have unit
Hilbert norm and eigenvalues `exp(± i arccos E)`; also `cos (arccos E) = E`
[PoulinEtAl2018]. -/
theorem full_walk_eigenvectors (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hφ : Normalized φ)
    (hPH : ∀ j, (P j)ᴴ=P j) (hP2 : ∀ j, P j*P j=1)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    walk β P ∈ Matrix.unitaryGroup (J × I) ℂ ∧
      ‖toHilbert (phiP β P φ E)‖=1 ∧ ‖toHilbert (phiM β P φ E)‖=1 ∧
      walk β P *ᵥ phiP β P φ E = Complex.exp ((Real.arccos E : ℂ)*Complex.I) • phiP β P φ E ∧
      walk β P *ᵥ phiM β P φ E = Complex.exp (-(Real.arccos E : ℂ)*Complex.I) • phiM β P φ E ∧
      Real.cos (Real.arccos E)=E := by
  have hn := phiPM_normalized β P φ E hβ hφ hPH hP2 heig hE
  refine ⟨walk_unitary β P hβ hPH hP2, (normalized_iff_hilbert _).1 hn.1,
    (normalized_iff_hilbert _).1 hn.2, ?_, ?_, Real.cos_arccos (by nlinarith) (by nlinarith)⟩
  · rw [walk_phiP β P φ E hβ hP2 heig hE,(actual_eigenphase E hE).1]
  · rw [walk_phiM β P φ E hβ hP2 heig hE,(actual_eigenphase E hE).2]

end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
