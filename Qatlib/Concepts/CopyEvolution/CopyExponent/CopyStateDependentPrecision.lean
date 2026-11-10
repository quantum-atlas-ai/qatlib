/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.CopyExponent
open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option autoImplicit false

private theorem split_pos {I : Type*} [Fintype I] [DecidableEq I]
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX).PosSemidef := by
  unfold Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart
  exact (Matrix.posSemidef_diagonal_iff.mpr fun i =>
    RCLike.ofReal_nonneg.mpr (le_max_right _ _)).mul_mul_conjTranspose_same _

private theorem split_neg {I : Type*} [Fintype I] [DecidableEq I]
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX).PosSemidef := by
  unfold Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart
  exact (Matrix.posSemidef_diagonal_iff.mpr fun i =>
    RCLike.ofReal_nonneg.mpr (le_max_right _ _)).mul_mul_conjTranspose_same _

private theorem run_sub {D r : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (angles : List ℝ) (X Y : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    freshCopyReferenceRun ρ angles r (X-Y) =
      freshCopyReferenceRun ρ angles r X - freshCopyReferenceRun ρ angles r Y := by
  rw [← (fresh_copy_protocol_cptp_reference ρ hρ angles r (X-Y)).1,
    tensorLeft_sub, (fresh_copy_protocol_cptp_reference ρ hρ angles r X).1,
    (fresh_copy_protocol_cptp_reference ρ hρ angles r Y).1]

private theorem hermitian_global {D r : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (t : ℝ) (n : ℕ) (hn : 0 < n)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hX : X.IsHermitian) :
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r X -
      TensorGate (HamiltonianEvolution ρ t) (1:Operator r)*X*
        (TensorGate (HamiltonianEvolution ρ t) (1:Operator r))ᴴ) ≤
      8*t^2/(n:ℝ)*Matrix.traceNorm X := by
  let P := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX
  let N := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX
  let U := TensorGate (HamiltonianEvolution ρ t) (1:Operator r)
  have hP := copy_fresh_actual_global_exponential_error D r ρ t n P hρ (split_pos hX) hn
  have hN := copy_fresh_actual_global_exponential_error D r ρ t n N hρ (split_neg hX) hn
  have hs : P-N = X :=
      Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.sub_posPart_negPart hX
  have hnrm : Matrix.traceNorm X = Matrix.traceNorm P + Matrix.traceNorm N :=
    Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.traceNorm_sub_posPart_negPart hX
  have he : freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r X - U*X*Uᴴ =
      (freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r P - U*P*Uᴴ) -
      (freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r N - U*N*Uᴴ) := by
    rw [← hs, run_sub ρ hρ, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [he]
  exact (traceNorm_sub_le _ _).trans (by rw [hnrm]; nlinarith [hP,hN])

private theorem reset_step {D r : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (θ : ℝ) (Y : Operator r) :
    partialSwapReferenceOutput ρ θ r (TensorGate ρ Y) = TensorGate ρ Y := by
  have ht : Matrix.traceLeft (TensorGate ρ Y) = Y := by
    ext i j
    simp only [Matrix.traceLeft, tensorGate_apply, ← Finset.sum_mul]
    change (Matrix.trace ρ)*Y i j = Y i j
    rw [hρ.2, one_mul]
  rw [(partial_swap_reference_output_formula ρ hρ θ r (TensorGate ρ Y)).1,
    ht, tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.mul_one, sub_self,
    smul_zero, sub_zero, ← add_smul]
  have htrig : ((Real.cos θ)^2 : ℂ) + ((Real.sin θ)^2 : ℂ) = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [htrig, one_smul]

private theorem reset_run {D r : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (angles : List ℝ) (Y : Operator r) :
    freshCopyReferenceRun ρ angles r (TensorGate ρ Y) = TensorGate ρ Y := by
  induction angles with
  | nil => rfl
  | cons θ rest ih =>
    change freshCopyReferenceRun ρ rest r
      (partialSwapReferenceOutput ρ θ r (TensorGate ρ Y)) = _
    rw [reset_step ρ hρ, ih]

private theorem reset_ideal {D r : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (t : ℝ) (Y : Operator r) :
    TensorGate (HamiltonianEvolution ρ t) (1:Operator r) * TensorGate ρ Y *
      (TensorGate (HamiltonianEvolution ρ t) (1:Operator r))ᴴ = TensorGate ρ Y := by
  have hc : HamiltonianEvolution ρ t * ρ = ρ * HamiltonianEvolution ρ t :=
    ((Commute.refl ρ).smul_left (-Complex.I*(t:ℂ))).exp_left.eq
  have hu := (Matrix.mem_unitaryGroup_iff).mp (hamiltonianEvolution_unitary hρ.1.isHermitian t)
  simp only [Matrix.star_eq_conjTranspose] at hu
  rw [tensorGate_conjTranspose, tensorGate_mul, tensorGate_mul, Matrix.one_mul,
    Matrix.conjTranspose_one, Matrix.mul_one, hc, Matrix.mul_assoc, hu, Matrix.mul_one]

theorem copy_state_dependent_fresh_global_error (D r : ℕ) (ρ : Operator D) (t : ℝ)
    (n : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hρ : IsDensityOperator ρ)
    (hX : X.PosSemidef) (hn : 0 < n) :
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r X -
      TensorGate (HamiltonianEvolution ρ t) (1:Operator r)*X*
        (TensorGate (HamiltonianEvolution ρ t) (1:Operator r))ᴴ) ≤
      8*t^2/(n:ℝ)*Matrix.traceNorm (X-TensorGate ρ (Matrix.traceLeft X)) := by
  let R := TensorGate ρ (Matrix.traceLeft X)
  have hR : R.PosSemidef :=
      Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hρ.1 hX.traceLeft
  have hZ : (X-R).IsHermitian := hX.isHermitian.sub hR.isHermitian
  have hb := hermitian_global ρ hρ t n hn (X-R) hZ
  rw [run_sub ρ hρ, reset_run ρ hρ, Matrix.mul_sub, Matrix.sub_mul,
    reset_ideal ρ hρ] at hb
  have he : (freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r X - R) -
      (TensorGate (HamiltonianEvolution ρ t) (1:Operator r)*X*
        (TensorGate (HamiltonianEvolution ρ t) (1:Operator r))ᴴ - R) =
      freshCopyReferenceRun ρ (List.replicate n (t/(n:ℝ))) r X -
        TensorGate (HamiltonianEvolution ρ t) (1:Operator r)*X*
          (TensorGate (HamiltonianEvolution ρ t) (1:Operator r))ᴴ := by abel
  rwa [he] at hb
end Qatlib.Concepts.CopyEvolution.CopyExponent
