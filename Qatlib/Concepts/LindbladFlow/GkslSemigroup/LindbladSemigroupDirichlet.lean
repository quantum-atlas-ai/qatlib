/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import QuantumInfo.Channels.Unbundled
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.Entropy.DPI
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

/-!
# Heisenberg duality and Lindblad Dirichlet identities

`gkslHeisenbergMap` is the trace-dual generator on observables. The module proves that it
annihilates the identity and that KMS self-adjointness with respect to a positive semidefinite
reference implies stationarity of that reference. It also computes the exact evolution and norm
of a generator eigenmode.

The carré-du-champ identity expresses the product-rule defect as a sum of jump-commutator
products. For a stationary Hermitian reference this gives a Dirichlet trace formula, nonnegative
when the reference is positive semidefinite, in the generator framework of [Lindblad1976].

## Main statements

* `lindblad_heisenberg_trace_dual`: relate Schrödinger and Heisenberg generators.
* `stationary_of_heisenberg_kmsSelfAdjoint`: deduce reference stationarity.
* `gkslHeisenbergMap_carre`: compute the carré-du-champ identity.
* `gkslHeisenberg_dirichlet_trace_nonneg`: prove nonnegativity of the stationary Dirichlet
  trace.

## References

* [Lindblad, 1976][Lindblad1976]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false

open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Filter
open scoped Topology

/-- The Heisenberg-picture GKSL generator as a complex-linear map on observables. -/
noncomputable def gkslHeisenbergMap {D : ℕ} (G : GKSL D) : Operator D →ₗ[ℂ] Operator D :=
  Complex.I • (LinearMap.mulLeft ℂ G.ham - LinearMap.mulRight ℂ G.ham) +
    ∑ j, ((LinearMap.mulLeft ℂ (G.jumps j)ᴴ).comp (LinearMap.mulRight ℂ (G.jumps j)) -
      (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ ((G.jumps j)ᴴ * G.jumps j) +
        LinearMap.mulRight ℂ ((G.jumps j)ᴴ * G.jumps j)))

/-- Expands the Heisenberg generator into its Hamiltonian commutator and adjoint-jump
dissipators. -/
theorem gkslHeisenbergMap_apply {D : ℕ} (G : GKSL D) (X : Operator D) :
    gkslHeisenbergMap G X = Complex.I • (G.ham * X - X * G.ham) +
      ∑ j, ((G.jumps j)ᴴ * X * G.jumps j -
        (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * X + X * (G.jumps j)ᴴ * G.jumps j)) := by
  simp only [gkslHeisenbergMap, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Matrix.mul_assoc]

/-- The Heisenberg generator annihilates the identity observable. -/
theorem gkslHeisenbergMap_one {D : ℕ} (G : GKSL D) : gkslHeisenbergMap G 1 = 0 := by
  rw [gkslHeisenbergMap_apply]
  simp only [Matrix.mul_one, Matrix.one_mul, sub_self, smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  module

/-- The Schrödinger and Heisenberg generators are dual under the bilinear trace pairing. -/
theorem lindblad_heisenberg_trace_dual {D : ℕ} (G : GKSL D) (ρ X : Operator D) :
    Matrix.trace (lindbladApply G ρ * X) = Matrix.trace (ρ * gkslHeisenbergMap G X) := by
  rw [gkslHeisenbergMap_apply]
  simp only [lindbladApply, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  have hham : (-Complex.I) * (Matrix.trace (G.ham * ρ * X) - Matrix.trace (ρ * G.ham * X)) =
      Complex.I * (Matrix.trace (ρ * (G.ham * X)) - Matrix.trace (ρ * (X * G.ham))) := by
    rw [Matrix.mul_assoc G.ham ρ X, Matrix.trace_mul_comm G.ham (ρ * X)]
    simp only [Matrix.mul_assoc]
    ring
  have hj (j : Fin (D * D)) :
      Matrix.trace (G.jumps j * ρ * (G.jumps j)ᴴ * X) -
        (1 / 2 : ℂ) * (Matrix.trace ((G.jumps j)ᴴ * G.jumps j * ρ * X) +
          Matrix.trace (ρ * (G.jumps j)ᴴ * G.jumps j * X)) =
        Matrix.trace (ρ * ((G.jumps j)ᴴ * X * G.jumps j)) -
          (1 / 2 : ℂ) * (Matrix.trace (ρ * ((G.jumps j)ᴴ * G.jumps j * X)) +
            Matrix.trace (ρ * (X * (G.jumps j)ᴴ * G.jumps j))) := by
    have hc : Matrix.trace ((G.jumps j)ᴴ * G.jumps j * ρ * X) =
        Matrix.trace (ρ * (X * (G.jumps j)ᴴ * G.jumps j)) := by
      rw [Matrix.mul_assoc ((G.jumps j)ᴴ * G.jumps j) ρ X,
        Matrix.trace_mul_comm ((G.jumps j)ᴴ * G.jumps j) (ρ * X)]
      simp only [Matrix.mul_assoc]
    have hd : Matrix.trace (G.jumps j * ρ * (G.jumps j)ᴴ * X) =
        Matrix.trace (ρ * ((G.jumps j)ᴴ * X * G.jumps j)) := by
      rw [Matrix.mul_assoc (G.jumps j * ρ) (G.jumps j)ᴴ X,
        Matrix.mul_assoc (G.jumps j) ρ ((G.jumps j)ᴴ * X),
        Matrix.trace_mul_comm (G.jumps j) (ρ * ((G.jumps j)ᴴ * X))]
      simp only [Matrix.mul_assoc]
    simp only [Matrix.mul_assoc] at hc hd ⊢
    rw [hd, hc]
    ring
  simp only [Matrix.mul_assoc] at hham hj ⊢
  rw [hham]
  congr 1
  exact Finset.sum_congr rfl fun j _ => hj j

/-- A positive semidefinite reference for which the Heisenberg generator is KMS-self-adjoint is
annihilated by the Schrödinger generator. -/
theorem lindbladApply_eq_zero_of_heisenberg_kmsSelfAdjoint {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (hρ : ρ.PosSemidef) (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) :
    lindbladApply G ρ = 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  simp only [Matrix.zero_mul, Matrix.trace_zero]
  rw [lindblad_heisenberg_trace_dual, Matrix.trace_mul_comm]
  rw [← kmsInner_one_left ρ _ hρ.nonneg, hself, gkslHeisenbergMap_one]
  simp [kmsInner]

/-- A positive semidefinite reference for which the Heisenberg generator is KMS-self-adjoint is
stationary under Lindblad evolution. -/
theorem stationary_of_heisenberg_kmsSelfAdjoint {D : ℕ} (G : GKSL D) (ρ : Operator D)
    (hρ : ρ.PosSemidef) (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) : IsStationary G ρ :=
  stationary_of_generator_zero G ρ (lindbladApply_eq_zero_of_heisenberg_kmsSelfAdjoint G ρ hρ hself)

/-- A generator eigenmode with eigenvalue `z` evolves by the scalar `exp(t * z)`. -/
theorem lindbladSemigroup_eigenmode {D : ℕ} (G : GKSL D) (ρ : Operator D) (z : ℂ)
    (h : lindbladApply G ρ = z • ρ) (t : ℝ) :
    lindbladSemigroup G t ρ = Complex.exp ((t : ℂ) * z) • ρ := by
  have hit (k : ℕ) : ((lindbladMap G)^[k]) ρ = z ^ k • ρ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [map_smul]
      change z ^ k • lindbladApply G ρ = _
      rw [h, smul_smul, pow_succ]
  have hs := NormedSpace.expSeries_div_hasSum_exp ((t : ℂ) * z)
  have hm := hs.smul_const ρ
  have hterm (k : ℕ) :
      (((t : ℂ) * z) ^ k / (k.factorial : ℂ)) • ρ =
        ((t : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) ρ := by
    rw [hit, smul_smul, mul_pow]
    congr 1
    ring
  simp only [hterm, ← Complex.exp_eq_exp_ℂ] at hm
  exact (lindbladSemigroup_hasSum G t ρ).unique hm

/-- The norm of a generator eigenmode evolves by the factor `exp(t * z.re)`. -/
theorem norm_lindbladSemigroup_eigenmode {D : ℕ} (G : GKSL D) (ρ : Operator D) (z : ℂ)
    (h : lindbladApply G ρ = z • ρ) (t : ℝ) :
    ‖lindbladSemigroup G t ρ‖ = Real.exp (t * z.re) * ‖ρ‖ := by
  rw [lindbladSemigroup_eigenmode G ρ z h t, norm_smul, Complex.norm_exp]
  simp

/-- The product-rule defect of a single Heisenberg dissipator is the product of its two jump
commutators. -/
private theorem dissipator_carre {D : ℕ} (L X Y : Operator D) :
    (Lᴴ * (Xᴴ * Y) * L - (1 / 2 : ℂ) • (Lᴴ * L * (Xᴴ * Y) + (Xᴴ * Y) * Lᴴ * L)) -
      (Lᴴ * X * L - (1 / 2 : ℂ) • (Lᴴ * L * X + X * Lᴴ * L))ᴴ * Y -
      Xᴴ * (Lᴴ * Y * L - (1 / 2 : ℂ) • (Lᴴ * L * Y + Y * Lᴴ * L)) =
        (L * X - X * L)ᴴ * (L * Y - Y * L) := by
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Complex.star_def,
    map_div₀, map_one, map_ofNat]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, Matrix.mul_assoc]
  module

/-- The Hamiltonian part of the Heisenberg generator has zero product-rule defect. -/
private theorem hamiltonian_carre {D : ℕ} (G : GKSL D) (X Y : Operator D) :
    Complex.I • (G.ham * (Xᴴ * Y) - (Xᴴ * Y) * G.ham) -
      (Complex.I • (G.ham * X - X * G.ham))ᴴ * Y -
        Xᴴ * (Complex.I • (G.ham * Y - Y * G.ham)) = 0 := by
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    G.hamHermitian.eq, Complex.star_def, Complex.conj_I]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    smul_sub, Matrix.mul_assoc]
  module

/-- The Heisenberg generator's carré-du-champ expression is the sum of products of jump
commutators [Lindblad1976]. -/
theorem gkslHeisenbergMap_carre {D : ℕ} (G : GKSL D) (X Y : Operator D) :
    gkslHeisenbergMap G (Xᴴ * Y) - (gkslHeisenbergMap G X)ᴴ * Y -
      Xᴴ * gkslHeisenbergMap G Y =
        ∑ j, (G.jumps j * X - X * G.jumps j)ᴴ * (G.jumps j * Y - Y * G.jumps j) := by
  let H (Z : Operator D) := Complex.I • (G.ham * Z - Z * G.ham)
  let J (j : Fin (D * D)) (Z : Operator D) :=
    (G.jumps j)ᴴ * Z * G.jumps j -
      (1 / 2 : ℂ) • ((G.jumps j)ᴴ * G.jumps j * Z + Z * (G.jumps j)ᴴ * G.jumps j)
  have hG (Z : Operator D) : gkslHeisenbergMap G Z = H Z + ∑ j, J j Z :=
    gkslHeisenbergMap_apply G Z
  rw [hG, hG, hG]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.add_mul,
    Matrix.mul_add, Matrix.sum_mul, Matrix.mul_sum]
  calc
    _ = (H (Xᴴ * Y) - (H X)ᴴ * Y - Xᴴ * H Y) +
        ∑ j, (J j (Xᴴ * Y) - (J j X)ᴴ * Y - Xᴴ * J j Y) := by
      simp only [Finset.sum_sub_distrib]
      abel
    _ = _ := by
      have hh : H (Xᴴ * Y) - (H X)ᴴ * Y - Xᴴ * H Y = 0 := hamiltonian_carre G X Y
      rw [hh, zero_add]
      exact Finset.sum_congr rfl fun j _ => dissipator_carre (G.jumps j) X Y

/-- The diagonal carré-du-champ expression of the Heisenberg generator is positive semidefinite. -/
theorem gkslHeisenbergMap_carre_posSemidef {D : ℕ} (G : GKSL D) (X : Operator D) :
    (gkslHeisenbergMap G (Xᴴ * X) - (gkslHeisenbergMap G X)ᴴ * X -
      Xᴴ * gkslHeisenbergMap G X).PosSemidef := by
  rw [gkslHeisenbergMap_carre]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg fun j _ =>
    (Matrix.posSemidef_conjTranspose_mul_self (G.jumps j * X - X * G.jumps j)).nonneg

/-- For a Hermitian weight, the real weighted trace pairing is symmetric in its two operator
arguments. -/
private theorem trace_pair_re_symm {D : ℕ} {ρ : Operator D} (hρ : ρ.IsHermitian)
    (X Y : Operator D) :
    (Matrix.trace (ρ * Xᴴ * Y)).re = (Matrix.trace (ρ * Yᴴ * X)).re := by
  have hh := Matrix.trace_conjTranspose (ρ * Xᴴ * Y)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hρ.eq] at hh
  have hr := congrArg Complex.re hh
  simp only [Complex.star_def, Complex.conj_re] at hr
  rw [← Matrix.mul_assoc Yᴴ X ρ, Matrix.trace_mul_comm (Yᴴ * X) ρ] at hr
  simpa only [Matrix.mul_assoc] using! hr.symm

/-- For a stationary Hermitian reference, the negative real generator pairing equals half the
sum of the weighted squared jump-commutator traces. -/
theorem gkslHeisenberg_dirichlet_trace {D : ℕ} (G : GKSL D) {ρ : Operator D}
    (hρ : ρ.IsHermitian) (hstationary : lindbladApply G ρ = 0) (X : Operator D) :
    -(Matrix.trace (ρ * Xᴴ * gkslHeisenbergMap G X)).re =
      (1 / 2 : ℝ) * ∑ j,
        (Matrix.trace (ρ * (G.jumps j * X - X * G.jumps j)ᴴ *
          (G.jumps j * X - X * G.jumps j))).re := by
  have hcarre := congrArg (fun A : Operator D => (Matrix.trace (ρ * A)).re)
    (gkslHeisenbergMap_carre G X X)

  have hzero : Matrix.trace (ρ * gkslHeisenbergMap G (Xᴴ * X)) = 0 := by
    rw [← lindblad_heisenberg_trace_dual, hstationary, Matrix.zero_mul, Matrix.trace_zero]
  have hsym := trace_pair_re_symm hρ (gkslHeisenbergMap G X) X
  have hleft :
      (Matrix.trace (ρ * (gkslHeisenbergMap G (Xᴴ * X) -
        (gkslHeisenbergMap G X)ᴴ * X - Xᴴ * gkslHeisenbergMap G X))).re =
      -(Matrix.trace (ρ * (gkslHeisenbergMap G X)ᴴ * X)).re -
        (Matrix.trace (ρ * Xᴴ * gkslHeisenbergMap G X)).re := by
    simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Matrix.mul_assoc,
      hzero, zero_sub, Complex.neg_re]
  rw [hleft, hsym] at hcarre
  have hright :
      (Matrix.trace (ρ * ∑ j, (G.jumps j * X - X * G.jumps j)ᴴ *
        (G.jumps j * X - X * G.jumps j))).re =
        ∑ j, (Matrix.trace (ρ * (G.jumps j * X - X * G.jumps j)ᴴ *
          (G.jumps j * X - X * G.jumps j))).re := by
    rw [Matrix.mul_sum, Matrix.trace_sum, complex_re_sum]
    simp only [Matrix.mul_assoc]
  rw [hright] at hcarre
  linarith

/-- The stationary Dirichlet trace is nonnegative for a positive semidefinite reference. -/
theorem gkslHeisenberg_dirichlet_trace_nonneg {D : ℕ} (G : GKSL D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (hstationary : lindbladApply G ρ = 0) (X : Operator D) :
    0 ≤ -(Matrix.trace (ρ * Xᴴ * gkslHeisenbergMap G X)).re := by
  rw [gkslHeisenberg_dirichlet_trace G hρ.isHermitian hstationary]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  let C := G.jumps j * X - X * G.jumps j
  have hp : (C * ρ * Cᴴ).PosSemidef := hρ.mul_mul_conjTranspose_same C
  have heq : Matrix.trace (C * ρ * Cᴴ) = Matrix.trace (ρ * Cᴴ * C) := by
    rw [Matrix.trace_mul_cycle C ρ Cᴴ]
    rw [Matrix.trace_mul_comm (Cᴴ * C) ρ]
    rw [Matrix.mul_assoc]
  have hr := trace_nonneg_of_nonneg hp.nonneg
  rw [heq] at hr
  exact (Complex.le_def.mp hr).1
end Qatlib.Concepts.LindbladFlow.GkslSemigroup
