/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.SketchPerturb.TruncatedSketchIsometryStat
import Mathlib.LinearAlgebra.Lagrange
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SketchSpectral.SketchPerturb
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem truncatedSketchIsometry_inverse_norm
    (RS CT : Type) [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (Cc : Matrix RS CT ℂ) (τ : ℝ) (hτ : 0 < τ) :
    ‖oddSingularTransform Ccᴴ (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0)‖ ≤ 1/τ := by
  apply oddSingularTransform_norm_le _ _ (by positivity)
  intro i
  split_ifs with h
  · have hn : 0 < matrixSingularValues Ccᴴ i := hτ.trans_le h
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le]
    simpa only [one_div] using one_div_le_one_div_of_le hτ h
  · simp only [norm_zero]
    positivity

theorem truncatedSketchIsometry_sandwich_error
    (C RS CT : Type) [Fintype C] [DecidableEq C] [Fintype RS] [DecidableEq RS]
    [Fintype CT] [DecidableEq CT] (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ)
    (τ α η : ℝ) (hτ : 0 < τ) (_hα : 0 ≤ α) (hη : 0 ≤ η)
    (hclose : spectralFrobenius (Cc*Ccᴴ-R*Rᴴ) ≤ η) (hbound : η ≤ τ*τ*α) :
    let P := oddSingularTransform Ccᴴ (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0)
    ‖P*R*(P*R)ᴴ-P*Cc*Ccᴴ*Pᴴ‖ ≤ α := by
  (try dsimp only)
  let P := oddSingularTransform Ccᴴ (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0)
  have hP := truncatedSketchIsometry_inverse_norm RS CT Cc τ hτ
  have hΔ : ‖R*Rᴴ-Cc*Ccᴴ‖ ≤ η := by
    rw [norm_sub_rev]
    exact (spectral_operator_norm_le_frobenius _).trans hclose
  have he : P*R*(P*R)ᴴ-P*Cc*Ccᴴ*Pᴴ = P*(R*Rᴴ-Cc*Ccᴴ)*Pᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [he]
  calc
    _ ≤ (‖P‖*‖R*Rᴴ-Cc*Ccᴴ‖)*‖Pᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1/τ)*η*(1/τ) := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = η/(τ*τ) := by ring
    _ ≤ α := (div_le_iff₀ (mul_pos hτ hτ)).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)

theorem truncatedSketchIsometry_product_projector
    (RS CT : Type) [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (Cc : Matrix RS CT ℂ) (τ : ℝ) (hτ : 0 < τ) :
    IsOrthogonalProjector
      (oddSingularTransform Ccᴴ (fun x => if τ ≤ x then (x:ℂ)⁻¹ else 0)*Cc) := by
  let B := Ccᴴ
  let L := leftSingularColumns B
  let V := basisColumns (rightSingularBasis B)
  let g : Fin (Fintype.card RS) → ℂ := fun i =>
    if τ ≤ matrixSingularValues B i then (matrixSingularValues B i:ℂ)⁻¹ else 0
  let e : Fin (Fintype.card RS) → ℂ := fun i =>
    if τ ≤ matrixSingularValues B i then 1 else 0
  have hB : B = L*diagonal (fun i : Fin (Fintype.card RS) => (matrixSingularValues B i:ℂ))*Vᴴ :=
    (oddSingularTransform_id B).symm
  have hs (i : Fin (Fintype.card RS)) : g i*(matrixSingularValues B i:ℂ) = e i := by
    dsimp [g,e]
    split_ifs with h
    · have hpos : 0 < matrixSingularValues B i := hτ.trans_le h
      rw [inv_mul_cancel₀ (by exact_mod_cast hpos.ne')]
    · simp
  have he₀ (i : Fin (Fintype.card RS)) : e i*(if matrixSingularValues B i=0 then (0:ℂ) else 1)*e i = e i := by
    by_cases h : τ ≤ matrixSingularValues B i
    · have hz : matrixSingularValues B i ≠ 0 := (hτ.trans_le h).ne'
      simp only [e,if_pos h,if_neg hz,mul_one]
    · simp only [e,if_neg h,zero_mul,mul_zero]
  have hea : (diagonal e : Matrix (Fin (Fintype.card RS)) (Fin (Fintype.card RS)) ℂ)ᴴ = diagonal e := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.conjTranspose_apply,Matrix.diagonal_apply_eq]
      unfold e
      split_ifs <;> simp
    · simp [Matrix.conjTranspose_apply,hij,Ne.symm hij]
  have hd : diagonal e * (Lᴴ*L) * diagonal e = diagonal e := by
    rw [leftSingularColumns_gram,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1
    exact funext he₀
  have hp : oddSingularTransform Ccᴴ (fun x => if τ ≤ x then (x:ℂ)⁻¹ else 0)*Cc = L*diagonal e*Lᴴ := by
    have hc : Cc = V*diagonal (fun i : Fin (Fintype.card RS) => (matrixSingularValues B i:ℂ))*Lᴴ := by
      have hh := congrArg Matrix.conjTranspose hB
      simp only [Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_mul,Matrix.diagonal_conjTranspose] at hh
      have hr : star (fun i : Fin (Fintype.card RS) => (matrixSingularValues B i:ℂ)) =
          (fun i : Fin (Fintype.card RS) => (matrixSingularValues B i:ℂ)) := by
        funext i
        simp
      rw [hr] at hh
      simpa only [B,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc] using hh
    conv_lhs => arg 2; rw [hc]
    change (L*diagonal g*Vᴴ)*(V*diagonal _*Lᴴ) = _
    calc
      _ = L*(diagonal g*(Vᴴ*V)*diagonal (fun i : Fin (Fintype.card RS) => (matrixSingularValues B i:ℂ)))*Lᴴ := by simp only [Matrix.mul_assoc]
      _ = L*diagonal e*Lᴴ := by
        rw [basisColumns_adjoint_mul,Matrix.mul_one,Matrix.diagonal_mul_diagonal]
        exact congrArg (fun D => L*D*Lᴴ) (congrArg diagonal (funext hs))
  rw [hp]
  constructor
  · change (L*diagonal e*Lᴴ)*(L*diagonal e*Lᴴ) = _
    calc
      _ = L*(diagonal e*(Lᴴ*L)*diagonal e)*Lᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hd]
  · change (L*diagonal e*Lᴴ)ᴴ = L*diagonal e*Lᴴ
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hea,Matrix.mul_assoc]

private theorem rectangular_gram_polynomial (I O : Type) [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (p : Polynomial ℂ) :
    A*aeval (Aᴴ*A) p = aeval (A*Aᴴ) p*A := by
  have hpow (n : ℕ) : A*(Aᴴ*A)^n = (A*Aᴴ)^n*A := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,pow_succ,← Matrix.mul_assoc,ih]; simp only [Matrix.mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Matrix.mul_add,Matrix.add_mul,hp,hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial,Algebra.algebraMap_eq_smul_one,Matrix.smul_mul,
      Matrix.one_mul,Matrix.mul_smul,hpow]

private theorem interpolation_cutoff (nodes : Finset ℂ) (τ x : ℝ) (hτ : 0 < τ)
    (hx : 0 ≤ x) (hnode : (x:ℂ)^2 ∈ nodes) :
    (Lagrange.interpolate nodes id (fun z : ℂ => if τ^2 ≤ z.re then z⁻¹ else 0)).eval ((x:ℂ)^2) =
      (if τ ≤ x then ((x:ℂ)^2)⁻¹ else 0) := by
  have hn := Lagrange.eval_interpolate_at_node (s := nodes) (v := id)
    (fun z : ℂ => if τ^2 ≤ z.re then z⁻¹ else 0) (Function.injective_id.injOn) hnode
  dsimp only [id] at hn
  rw [hn]
  rw [← Complex.ofReal_pow]
  simp only [Complex.ofReal_re]
  have he : τ^2 ≤ x^2 ↔ τ ≤ x := (sq_le_sq₀ hτ.le hx)
  simp only [he]

theorem truncatedSketchIsometry_projection_identity
    (RS CT : Type) [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (Cc : Matrix RS CT ℂ) (τ : ℝ) (hτ : 0 < τ) :
    let P := oddSingularTransform Ccᴴ (fun x => if τ ≤ x then (x:ℂ)⁻¹ else 0)
    P*Cc*Ccᴴ*Pᴴ = basisColumns (rightSingularBasis Cc) *
      diagonal (fun i : Fin (Fintype.card CT) => if τ ≤ matrixSingularValues Cc i then (1:ℂ) else 0) *
      (basisColumns (rightSingularBasis Cc))ᴴ := by
  (try dsimp only)
  let B := Ccᴴ
  let P := oddSingularTransform B (fun x => if τ ≤ x then (x:ℂ)⁻¹ else 0)
  let nodes : Finset ℂ :=
    (Finset.univ.image (fun i : Fin (Fintype.card RS) => (matrixSingularValues B i:ℂ)^2)) ∪
    (Finset.univ.image (fun i : Fin (Fintype.card CT) => (matrixSingularValues Cc i:ℂ)^2))
  let q := Lagrange.interpolate nodes id (fun z : ℂ => if τ^2 ≤ z.re then z⁻¹ else 0)
  have hqB (i : Fin (Fintype.card RS)) : q.eval ((matrixSingularValues B i:ℂ)^2) =
      (if τ ≤ matrixSingularValues B i then ((matrixSingularValues B i:ℂ)^2)⁻¹ else 0) := by
    apply interpolation_cutoff nodes τ _ hτ (matrixSingularValues_nonneg B _)
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hqA (i : Fin (Fintype.card CT)) : q.eval ((matrixSingularValues Cc i:ℂ)^2) =
      (if τ ≤ matrixSingularValues Cc i then ((matrixSingularValues Cc i:ℂ)^2)⁻¹ else 0) := by
    apply interpolation_cutoff nodes τ _ hτ (matrixSingularValues_nonneg Cc _)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hP : P = B*aeval (Bᴴ*B) q := by
    rw [mul_gram_aeval_eq_oddSingularTransform]
    unfold P
    apply oddSingularTransform_congr_positive
    intro i hi
    rw [hqB]
    split_ifs
    · field_simp
    · simp
  have hQ : P*Cc = basisColumns (rightSingularBasis Cc) *
      diagonal (fun i : Fin (Fintype.card CT) => if τ ≤ matrixSingularValues Cc i then (1:ℂ) else 0) *
      (basisColumns (rightSingularBasis Cc))ᴴ := by
    rw [hP,rectangular_gram_polynomial]
    have he : aeval (B*Bᴴ) q*B*Cc = aeval (Ccᴴ*Cc) (q*X) := by
      simp only [B,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc,map_mul,aeval_X]
    rw [he,gram_aeval_eq_rightSingularTransform]
    unfold rightSingularTransform spectralDiagonal
    apply congrArg
        (fun D => basisColumns (rightSingularBasis Cc)*D*(basisColumns (rightSingularBasis Cc))ᴴ)
    apply congrArg diagonal
    funext i
    (try dsimp only)
    rw [Polynomial.eval_mul,Polynomial.eval_X,hqA]
    split_ifs with h
    · have hp : 0 < matrixSingularValues Cc i := hτ.trans_le h
      exact inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.ne'))
    · simp
  have hproj := truncatedSketchIsometry_product_projector RS CT Cc τ hτ
  change IsOrthogonalProjector (P*Cc) at hproj
  have hsa : (P*Cc)ᴴ = P*Cc := hproj.2
  have he : P*Cc*Ccᴴ*Pᴴ = (P*Cc)*(P*Cc)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  change P*Cc*Ccᴴ*Pᴴ = _
  rw [he,hsa,hproj.1,hQ]

theorem truncatedSketchIsometry : TruncatedSketchIsometry := by
  intro C RS CT _ _ _ _ _ _ R Cc τ α η hτ hα hη hclose hbound
  exact ⟨truncatedSketchIsometry_sandwich_error C RS CT R Cc τ α η hτ hα hη hclose hbound,
    truncatedSketchIsometry_projection_identity RS CT Cc τ hτ⟩

end Qatlib.Concepts.SketchSpectral.SketchPerturb
