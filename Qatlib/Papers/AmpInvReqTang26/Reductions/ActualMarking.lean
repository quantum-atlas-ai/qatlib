/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.MarkingOracle
import Qatlib.Papers.AmpInvReqTang26.AccessModel.ActualAccess
import Qatlib.Papers.AmpInvReqTang26.BiasedFourier.UnbiasedGram

/-!
# Preparation circuits for normalized traces

The Fourier preparation matrix `sourcePreparation` supplies uniform and phase-weighted columns.
The circuits `tracePreparation` and `twoTracePreparation` mark selected coordinates after
conjugating a diagonal oracle, exposing normalized traces as their good output amplitudes. This
development supports the treatment in [TangWright2025].

## Main statements

* `tracePreparation_amplitude`: the good amplitude is the normalized trace magnitude.
* `twoTracePreparation_unitary`: unitarity of the two-coordinate marking circuit.
* `twoTracePreparation_good_entry`: explicit ordinary and phase-weighted trace entries.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.Reductions
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Concepts.QueryComplexity.MarkingOracle
set_option warningAsError false

/-- The zero-bias Fourier preparation matrix `Ftilde 0 d`. -/
def sourcePreparation (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Ftilde 0 d

/-- The source preparation matrix is unitary for positive dimension. -/
theorem sourcePreparation_unitary (d : ℕ) (hd : 0<d) :
    sourcePreparation d ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext i j
  simpa only [sourcePreparation,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    Ftilde,fourierUnitVec] using! unbiased_column_gram d hd i j

/-- The first column of the source preparation matrix is the uniform coefficient vector. -/
theorem sourcePreparation_first (d : ℕ) (hd : 0<d) (i : Fin d) :
    sourcePreparation d i ⟨0,hd⟩=(uniformCoefficient (Fin d):ℂ) := by
  simp [sourcePreparation,Ftilde,muEpsWeight,uniformCoefficient,Real.sqrt_inv]

/-- For dimension greater than one, the second preparation column is the uniform coefficient
multiplied by the root phase. -/
theorem sourcePreparation_second (d : ℕ) (hd : 1<d) (i : Fin d) :
    sourcePreparation d i ⟨1,hd⟩=(uniformCoefficient (Fin d):ℂ)*phase d i := by
  simp [sourcePreparation,Ftilde,muEpsWeight,uniformCoefficient,Real.sqrt_inv]

/-- A diagonal matrix whose entries all have norm one belongs to the unitary group. -/
theorem sourceDiagonal_unitary (d : ℕ) (u : Fin d → ℂ) (hu : ∀i,‖u i‖=1) :
    Matrix.diagonal u ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (Matrix.diagonal u)ᴴ*Matrix.diagonal u=1
  ext i j
  simp only [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hu]
    norm_num
  · simp [hij]

/-- The flagged circuit that conjugates a diagonal assignment by the source preparation and
marks the zero data coordinate. -/
def tracePreparation (d : ℕ) (hd : 0<d) (u : Fin d → ℂ) :
    Matrix (Fin d×Bool) (Fin d×Bool) ℂ :=
  zeroGoodCircuit (fun i => decide (i=(⟨0,hd⟩:Fin d))) (sourcePreparation d) (Matrix.diagonal u)

/-- The trace preparation circuit is unitary when every diagonal entry has norm one. -/
theorem tracePreparation_unitary (d : ℕ) (hd : 0<d) (u : Fin d → ℂ) (hu : ∀i,‖u i‖=1) :
    tracePreparation d hd u ∈ Matrix.unitaryGroup (Fin d×Bool) ℂ :=
  zeroGoodCircuit_unitary _ _ _ (sourcePreparation_unitary d hd) (sourceDiagonal_unitary d u hu)

/-- The basis vector at `(i0, false)` equals the data basis vector at `i0` embedded with the
zero flag. -/
private theorem single_zeroFlag {d : ℕ} (i0 : Fin d) :
    (Pi.single (i0,false) (1:ℂ) : Fin d×Bool → ℂ)=zeroFlag (Pi.single i0 1) := by
  funext x
  rcases x with ⟨i,b⟩
  cases b <;> simp [Pi.single_apply,zeroFlag]

/-- From the prescribed initial basis state, the false-flag output is supported at data index
zero with amplitude equal to the normalized sum of `u`. -/
theorem tracePreparation_good_entry (d : ℕ) (hd : 0<d) (u : Fin d → ℂ) (i : Fin d) :
    tracePreparation d hd u (i,false) (⟨0,hd⟩,false)=
      if i=(⟨0,hd⟩:Fin d) then (d:ℂ)⁻¹*∑k,u k else 0 := by
  have h := zeroGoodCircuit_amplitude (fun j => decide (j=(⟨0,hd⟩:Fin d)))
    (sourcePreparation d) (Matrix.diagonal u) (Pi.single ⟨0,hd⟩ 1) i
  rw [← single_zeroFlag,Matrix.mulVec_single_one,Matrix.mulVec_single_one] at h
  change tracePreparation d hd u (i,false) (⟨0,hd⟩,false)=_ at h
  rw [h]
  by_cases hi : i=(⟨0,hd⟩:Fin d)
  · subst i
    simp only [decide_true,if_true]
    simpa only [Fintype.card_fin] using! conjugated_uniform_mean (sourcePreparation d) u ⟨0,hd⟩
      (sourcePreparation_first d hd)
  · simp [hi]

/-- The marked preparation amplitude is the norm of the normalized sum of the diagonal entries. -/
theorem tracePreparation_amplitude (d : ℕ) (hd : 0<d) (u : Fin d → ℂ) :
    preparationAmplitude (⟨0,hd⟩,false) (fun x : Fin d×Bool => !x.2) (tracePreparation d hd u)=
      ‖(d:ℂ)⁻¹*∑k,u k‖ := by
  unfold preparationAmplitude preparationGoodMass
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Bool.not_true,Bool.not_false,
    Bool.false_eq_true,if_false,if_true,zero_add,tracePreparation_good_entry]
  simp only [apply_ite norm,ite_pow,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Real.sqrt_sq_eq_abs,abs_norm]

/-- The flagged conjugation circuit marking both data indices zero and one. -/
def twoTracePreparation (d : ℕ) (hd : 1<d) (u : Fin d → ℂ) :
    Matrix (Fin d×Bool) (Fin d×Bool) ℂ :=
  zeroGoodCircuit (fun i => decide (i=(⟨0,by omega⟩:Fin d) ∨ i=(⟨1,hd⟩:Fin d)))
    (sourcePreparation d) (Matrix.diagonal u)

/-- For dimension greater than one, the two-coordinate trace preparation is unitary when all
diagonal entries have norm one [TangWright2025]. -/
theorem twoTracePreparation_unitary (d : ℕ) (hd : 1<d) (u : Fin d → ℂ) (hu : ∀i,‖u i‖=1) :
    twoTracePreparation d hd u ∈ Matrix.unitaryGroup (Fin d×Bool) ℂ :=
  zeroGoodCircuit_unitary _ _ _ (sourcePreparation_unitary d (by omega)) (sourceDiagonal_unitary d u hu)

/-- The marked output entries of the two-coordinate preparation are the normalized ordinary
trace and the normalized conjugate-phase-weighted trace at indices zero and one, and zero
elsewhere [TangWright2025]. -/
theorem twoTracePreparation_good_entry (d : ℕ) (hd : 1<d) (u : Fin d → ℂ) (i : Fin d) :
    twoTracePreparation d hd u (i,false) (⟨0,by omega⟩,false)=
      if i=(⟨0,by omega⟩:Fin d) then (d:ℂ)⁻¹*∑k,u k
      else if i=(⟨1,hd⟩:Fin d) then (d:ℂ)⁻¹*∑k,star (phase d k)*u k else 0 := by
  have h := zeroGoodCircuit_amplitude
    (fun j => decide (j=(⟨0,by omega⟩:Fin d) ∨ j=(⟨1,hd⟩:Fin d)))
    (sourcePreparation d) (Matrix.diagonal u) (Pi.single ⟨0,by omega⟩ 1) i
  rw [← single_zeroFlag,Matrix.mulVec_single_one,Matrix.mulVec_single_one] at h
  change twoTracePreparation d hd u (i,false) (⟨0,by omega⟩,false)=_ at h
  rw [h]
  by_cases hi0 : i=(⟨0,by omega⟩:Fin d)
  · subst i
    simp only [true_or,decide_true,if_true]
    simpa only [Fintype.card_fin] using! conjugated_uniform_mean (sourcePreparation d) u ⟨0,by omega⟩
      (sourcePreparation_first d (by omega))
  · by_cases hi1 : i=(⟨1,hd⟩:Fin d)
    · subst i
      simp only [or_true,decide_true,if_true,if_neg hi0]
      simpa only [Fintype.card_fin] using! conjugated_phase_mean (sourcePreparation d) u (phase d)
        ⟨0,by omega⟩ ⟨1,hd⟩ (sourcePreparation_first d (by omega)) (sourcePreparation_second d hd)
    · simp [hi0,hi1]

end Qatlib.Papers.AmpInvReqTang26.Reductions
