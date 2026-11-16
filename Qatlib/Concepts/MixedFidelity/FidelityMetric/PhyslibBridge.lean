/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
public import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
public import QuantumInfo.States.Mixed.TraceDistance

@[expose] public section


/-! # Clean mixed-state distance and channel bridges

The public library already proves the matrix Fuchs–van de Graaf bounds and
fidelity data processing. These interfaces transport those results to Physlib
mixed states without using its unfinished channel-fidelity theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open scoped MatrixOrder ComplexOrder

/-- Physlib's positive Hermitian square root is the matrix functional-calculus square root. -/
theorem mstate_sqrt_mat {I : Type*} [Fintype I] [DecidableEq I] (ρ : MState I) :
    ρ.M.sqrt.mat = CFC.sqrt ρ.m := by
  rw [HermitianMat.sqrt, HermitianMat.mat_cfc,
    CFC.sqrt_eq_real_sqrt ρ.m ρ.psd.nonneg, cfcₙ_eq_cfc]
  rfl

/-- Physlib root fidelity is the public matrix root fidelity with the factors reversed. -/
theorem fidelity_eq_froot {D : ℕ} (ρ σ : MState (Fin D)) :
    MState.fidelity ρ σ = Froot σ.m ρ.m := by
  rw [MState.fidelity_eq_traceNorm_sqrt_mul_sqrt, mstate_sqrt_mat,
    mstate_sqrt_mat]
  rfl

/-- Physlib trace distance agrees with the public half-trace-norm convention. -/
theorem trDistance_eq_traceDistance {D : ℕ} (ρ σ : MState (Fin D)) :
    TrDistance ρ σ = traceDistance ρ.m σ.m := by
  simp only [TrDistance, traceDistance]
  ring

/-- The lower Fuchs–van de Graaf bound for bundled mixed states on finite coordinates. -/
private theorem one_sub_fidelity_le_trDistance_fin {D : ℕ} (ρ σ : MState (Fin D)) :
    1 - MState.fidelity ρ σ ≤ TrDistance ρ σ := by
  rw [MState.fidelity_symm ρ σ, fidelity_eq_froot, trDistance_eq_traceDistance]
  exact one_sub_froot_le_traceDistance ⟨ρ.psd, ρ.tr'⟩ ⟨σ.psd, σ.tr'⟩

/-- The upper Fuchs–van de Graaf bound for bundled mixed states on finite coordinates. -/
private theorem trDistance_le_sqrt_one_sub_fidelity_sq_fin {D : ℕ} (ρ σ : MState (Fin D)) :
    TrDistance ρ σ ≤ Real.sqrt (1 - (MState.fidelity ρ σ) ^ 2) := by
  rw [MState.fidelity_symm ρ σ, fidelity_eq_froot, trDistance_eq_traceDistance]
  exact traceDistance_le_sqrt_one_sub_froot_sq ⟨ρ.psd, ρ.tr'⟩ ⟨σ.psd, σ.tr'⟩

/-- A Physlib completely positive trace-preserving map cannot decrease root fidelity. -/
private theorem fidelity_channel_nondecreasing_fin {D E : ℕ} (ρ σ : MState (Fin D))
    (Λ : CPTPMap (Fin D) (Fin E)) :
    MState.fidelity ρ σ ≤ MState.fidelity (Λ ρ) (Λ σ) := by
  rw [fidelity_eq_froot, fidelity_eq_froot]
  exact froot_channel_le
    (Qatlib.Concepts.ChannelTheory.Stinespring.ofPhyslib Λ) ⟨σ.psd, σ.tr'⟩ ⟨ρ.psd, ρ.tr'⟩

/-- Simultaneous relabeling preserves the fidelity of arbitrary finite mixed states. -/
theorem fidelity_relabel {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] (ρ σ : MState d) (f : e ≃ d) :
    MState.fidelity (ρ.relabel f) (σ.relabel f) = MState.fidelity ρ σ := by
  simp only [MState.fidelity, MState.relabel_M, HermitianMat.sqrt,
    HermitianMat.cfc_reindex, HermitianMat.mat_reindex,
    HermitianMat.reindex_conj, Matrix.reindex_apply,
    Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_symm,
    Equiv.apply_symm_apply, id_eq]
  rw [HermitianMat.conj_submatrix]
  simp
  rfl

/-- Relabeling both indices by an equivalence preserves the trace norm of a square matrix. -/
theorem traceNorm_submatrix_equiv {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] (A : Matrix d d ℂ) (f : e ≃ d) :
    (A.submatrix f f).traceNorm = A.traceNorm := by
  unfold Matrix.traceNorm
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  have hs : CFC.sqrt ((A.conjTranspose * A).submatrix f f) =
      (CFC.sqrt (A.conjTranspose * A)).submatrix f f := by
    rw [CFC.sqrt_eq_real_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self A |>.submatrix f).nonneg,
      CFC.sqrt_eq_real_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg]
    rw [cfcₙ_eq_cfc, cfcₙ_eq_cfc]
    simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
      (Matrix.cfc_reindex (𝕜 := ℂ) (A := A.conjTranspose * A) Real.sqrt f.symm)
  rw [hs, Matrix.trace_submatrix]

/-- Simultaneous relabeling preserves the trace distance of finite mixed states. -/
theorem trDistance_relabel {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] (ρ σ : MState d) (f : e ≃ d) :
    TrDistance (ρ.relabel f) (σ.relabel f) = TrDistance ρ σ := by
  change (1 / 2 : ℝ) * ((ρ.m - σ.m).submatrix f f).traceNorm = _
  rw [traceNorm_submatrix_equiv]
  rfl

/-- The lower Fuchs–van de Graaf bound holds for Physlib mixed states on every finite index type. -/
theorem one_sub_fidelity_le_trDistance {d : Type*} [Fintype d] [DecidableEq d]
    (ρ σ : MState d) : 1 - MState.fidelity ρ σ ≤ TrDistance ρ σ := by
  have h := one_sub_fidelity_le_trDistance_fin
    (ρ.relabel (Fintype.equivFin d).symm) (σ.relabel (Fintype.equivFin d).symm)
  simpa only [fidelity_relabel, trDistance_relabel] using h

/-- The upper Fuchs–van de Graaf bound holds for Physlib mixed states on every finite index type. -/
theorem trDistance_le_sqrt_one_sub_fidelity_sq {d : Type*} [Fintype d] [DecidableEq d]
    (ρ σ : MState d) : TrDistance ρ σ ≤ Real.sqrt (1 - (MState.fidelity ρ σ) ^ 2) := by
  have h := trDistance_le_sqrt_one_sub_fidelity_sq_fin
    (ρ.relabel (Fintype.equivFin d).symm) (σ.relabel (Fintype.equivFin d).symm)
  simpa only [fidelity_relabel, trDistance_relabel] using h

/-- Every Physlib completely positive trace-preserving map increases root fidelity. -/
theorem fidelity_channel_nondecreasing {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e] (ρ σ : MState d) (Λ : CPTPMap d e) :
    MState.fidelity ρ σ ≤ MState.fidelity (Λ ρ) (Λ σ) := by
  let fd := Fintype.equivFin d
  let fe := Fintype.equivFin e
  let T : CPTPMap (Fin (Fintype.card d)) (Fin (Fintype.card e)) :=
    CPTPMap.ofEquiv fe ∘ₘ (Λ ∘ₘ CPTPMap.ofEquiv fd.symm)
  have h := fidelity_channel_nondecreasing_fin (ρ.relabel fd.symm) (σ.relabel fd.symm) T
  simpa only [T, CPTPMap.compose_eq, CPTPMap.ofEquiv_apply, MState.relabel_relabel,
    Equiv.symm_symm, Equiv.self_trans_symm, MState.relabel_refl, fidelity_relabel] using h

end Qatlib.Concepts.MixedFidelity.FidelityMetric
