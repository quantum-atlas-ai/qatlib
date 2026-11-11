/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.SharpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Unitary evolutions and partial integration

The generators of the physical and adiabatic matrix evolutions are written as `Complex.I` times
Hermitian matrices, yielding unitarity of `Uτ` and `UτA`. The module also proves the matrix
product integration formula and the scaled `partial_integration_identity` used in the partial
integration argument of [JansenRuskaiSeiler2007].

## Main statements

* `adiHerm_isHermitian`: the Hermitian form of the adiabatic generator.
* `UτA_mem_unitary` and `Uτ_mem_unitary`: unitarity of the two evolutions.
* `partial_integration_identity`: the boundary and integral terms arising from partial
  integration.

## References

* [Jansen et al., 2007][JansenRuskaiSeiler2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open scoped Matrix.Norms.L2Operator ComplexOrder Interval

namespace Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

local instance sourceMatrixENormedAddCommMonoid (m : Type) [Fintype m] [DecidableEq m] :
    ENormedAddCommMonoid (Matrix m m ℂ) :=
  @NormedAddCommGroup.toENormedAddCommMonoid _ Matrix.instL2OpNormedAddCommGroup

local instance sourceMatrixPseudoMetrizable (m : Type) [Fintype m] [DecidableEq m] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m m ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (m → m → ℂ)
  infer_instance

/-- The physical generator is `Complex.I` times the Hamiltonian scaled by the real parameter
`τ`. -/
theorem realGenerator_eq_I_smul (τ : ℝ) (H : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    realGenerator τ H = fun u => Complex.I • ((τ : ℂ) • H u) := by
  funext u
  rw [realGenerator, smul_smul]

/-- The adiabatic generator is `Complex.I` times the sum of the scaled Hamiltonian and the
Hermitian correction `Complex.I • (Pdot * P - P * Pdot)`. -/
theorem adiGenerator_eq_I_smul (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    adiGenerator τ H P Pdot
      = fun u => Complex.I •
          ((τ : ℂ) • H u + Complex.I • (Pdot u * P u - P u * Pdot u)) := by
  funext u
  simp only [adiGenerator, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [sub_eq_add_neg]

/-- A real number embedded in `ℂ` is self-adjoint. -/
theorem isSelfAdjoint_ofReal (τ : ℝ) : IsSelfAdjoint (τ : ℂ) := by
  show star (τ : ℂ) = (τ : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The commutator `Pdot * P - P * Pdot` of two Hermitian matrices is skew-Hermitian. -/
theorem skew_of_hermitian (P Pdot : Matrix (Fin n) (Fin n) ℂ)
    (hP : Pᴴ = P) (hPd : Pdotᴴ = Pdot) :
    (Pdot * P - P * Pdot)ᴴ = -(Pdot * P - P * Pdot) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP, hPd]
  rw [neg_sub]

/-- Multiplying a skew-Hermitian matrix by `Complex.I` gives a Hermitian matrix. -/
theorem complexI_smul_hermitian (C : Matrix (Fin n) (Fin n) ℂ) (hC : Cᴴ = -C) :
    (Complex.I • C).IsHermitian := by
  show (Complex.I • C)ᴴ = Complex.I • C
  rw [Matrix.conjTranspose_smul, hC]
  have hstar : star (Complex.I) = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  rw [hstar, show -C = (-1 : ℂ) • C by simp, smul_smul]
  rw [show (-Complex.I) * (-1) = Complex.I by ring]

/-- The matrix function `τ H + i[Pdot, P]` whose multiplication by `Complex.I` gives the
adiabatic generator. -/
def adiHerm (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    ℝ → Matrix (Fin n) (Fin n) ℂ :=
  fun u => (τ : ℂ) • H u + Complex.I • (Pdot u * P u - P u * Pdot u)

/-- The function `adiHerm τ H P Pdot` is pointwise Hermitian when `H`, `P`, and `Pdot` are
pointwise Hermitian. -/
theorem adiHerm_isHermitian (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ s, (H s).IsHermitian)
    (hP : ∀ s, (P s)ᴴ = P s) (hPd : ∀ s, (Pdot s)ᴴ = Pdot s) :
    ∀ s, (adiHerm τ H P Pdot s).IsHermitian := by
  intro s
  exact ((hH s).smul (isSelfAdjoint_ofReal τ)).add
    (complexI_smul_hermitian _ (skew_of_hermitian (P s) (Pdot s) (hP s) (hPd s)))

/-- The adiabatic generator equals `Complex.I` times `adiHerm` at every parameter value. -/
theorem adiGenerator_eq_I_adiHerm (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ) :
    adiGenerator τ H P Pdot = fun u => Complex.I • adiHerm τ H P Pdot u :=
  adiGenerator_eq_I_smul τ H P Pdot

/-- The adiabatic evolution is unitary at every real time when `H`, `P`, and `Pdot` are
continuous and pointwise Hermitian. -/
theorem UτA_mem_unitary (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ s, (H s).IsHermitian)
    (hP : ∀ s, (P s)ᴴ = P s) (hPd : ∀ s, (Pdot s)ᴴ = Pdot s)
    (hHc : Continuous H) (hPc : Continuous P) (hPdc : Continuous Pdot) (s : ℝ) :
    UτA τ H P Pdot s ∈ unitaryGroup (Fin n) ℂ := by
  have hcont : Continuous (adiHerm τ H P Pdot) := by
    unfold adiHerm
    fun_prop
  have hunit : orderedEvolution (fun u => Complex.I • adiHerm τ H P Pdot u) 0 s
      ∈ unitaryGroup (Fin n) ℂ :=
    ordered_evolution_hermitian_unitary (Fin n) (adiHerm τ H P Pdot) hcont
      (adiHerm_isHermitian τ H P Pdot hH hP hPd) 0 s
  rwa [UτA, adiGenerator_eq_I_adiHerm]

/-- The physical evolution is unitary at every real time for a continuous, pointwise Hermitian
Hamiltonian. -/
theorem Uτ_mem_unitary (τ : ℝ) (H : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ s, (H s).IsHermitian) (hHc : Continuous H) (s : ℝ) :
    Uτ τ H s ∈ unitaryGroup (Fin n) ℂ := by
  have hcont : Continuous (fun u => (τ : ℂ) • H u) := by fun_prop
  have hherm : ∀ u, ((τ : ℂ) • H u).IsHermitian :=
    fun u => (hH u).smul (isSelfAdjoint_ofReal τ)
  have hunit : orderedEvolution (fun u => Complex.I • ((τ : ℂ) • H u)) 0 s
      ∈ unitaryGroup (Fin n) ℂ :=
    ordered_evolution_hermitian_unitary (Fin n) (fun u => (τ : ℂ) • H u) hcont hherm 0 s
  rwa [Uτ, realGenerator_eq_I_smul]

/-- The conjugate transpose of a unitary matrix multiplied by that matrix is the identity. -/
theorem unitary_conjTranspose_mul {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hU

/-- A unitary matrix multiplied by its conjugate transpose is the identity. -/
theorem unitary_mul_conjTranspose {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp hU

/-- The interval integral of `FDot * Y + F * YDot` equals the endpoint difference of `F * Y`,
assuming the stated derivatives and their interval integrability. See
[JansenRuskaiSeiler2007]. -/
theorem matrix_integral_deriv_mul_eq_sub
    {F FDot Y YDot : ℝ → Matrix (Fin n) (Fin n) ℂ} {a b : ℝ}
    (hF : ∀ x ∈ [[a, b]], HasDerivAt F (FDot x) x)
    (hY : ∀ x ∈ [[a, b]], HasDerivAt Y (YDot x) x)
    (hFi : IntervalIntegrable FDot volume a b)
    (hYi : IntervalIntegrable YDot volume a b) :
    ∫ x in a..b, FDot x * Y x + F x * YDot x = F b * Y b - F a * Y a :=
  intervalIntegral.integral_deriv_mul_eq_sub hF hY hFi hYi

/-- For nonzero `τ`, the relation `iτ(P0 * Xadj * Q0) = FDot - G` yields an integral identity
with factor `-i/τ`, the endpoint difference of `F * Y`, and the two correction integrals.
See [JansenRuskaiSeiler2007]. -/
theorem partial_integration_identity
    (τ : ℝ) (hτ : τ ≠ 0)
    (P0 Q0 : Matrix (Fin n) (Fin n) ℂ)
    (Xadj G : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (F FDot Y YDot : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hF : ∀ x, HasDerivAt F (FDot x) x)
    (hY : ∀ x, HasDerivAt Y (YDot x) x)
    (hFc : Continuous F) (hFDc : Continuous FDot)
    (hYc : Continuous Y) (hYDc : Continuous YDot) (hGc : Continuous G)
    (hrel : ∀ x, (Complex.I * (τ : ℂ)) • (P0 * Xadj x * Q0) = FDot x - G x) :
    (∫ x in (0 : ℝ)..t, (P0 * Xadj x * Q0) * Y x)
      = -(Complex.I / (τ : ℂ)) •
          ((F t * Y t - F 0 * Y 0)
            - (∫ x in (0 : ℝ)..t, F x * YDot x)
            - (∫ x in (0 : ℝ)..t, G x * Y x)) := by
  have hne : Complex.I * (τ : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hτ)
  have hFi : IntervalIntegrable FDot volume (0 : ℝ) t := hFDc.intervalIntegrable _ _
  have hYi : IntervalIntegrable YDot volume (0 : ℝ) t := hYDc.intervalIntegrable _ _
  have hIBP := matrix_integral_deriv_mul_eq_sub
    (a := (0 : ℝ)) (b := t) (fun x _ => hF x) (fun x _ => hY x) hFi hYi
  have hscalar : (Complex.I * (τ : ℂ))⁻¹ = -(Complex.I / (τ : ℂ)) := by
    rw [mul_inv, Complex.inv_I, div_eq_mul_inv]
    ring
  have hPX : ∀ x, P0 * Xadj x * Q0 = (Complex.I * (τ : ℂ))⁻¹ • (FDot x - G x) := by
    intro x
    rw [← hrel x, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hpt : ∀ x, (P0 * Xadj x * Q0) * Y x
      = (Complex.I * (τ : ℂ))⁻¹ • ((FDot x - G x) * Y x) := by
    intro x
    rw [hPX x, Algebra.smul_mul_assoc]
  have hIntEq : (∫ x in (0 : ℝ)..t, (P0 * Xadj x * Q0) * Y x)
      = (Complex.I * (τ : ℂ))⁻¹ •
          ∫ x in (0 : ℝ)..t, (FDot x - G x) * Y x := by
    rw [show (fun x => (P0 * Xadj x * Q0) * Y x)
          = (fun x => (Complex.I * (τ : ℂ))⁻¹ • ((FDot x - G x) * Y x)) from funext hpt,
      intervalIntegral.integral_smul]
  have hsplit : (∫ x in (0 : ℝ)..t, (FDot x - G x) * Y x)
      = (∫ x in (0 : ℝ)..t, FDot x * Y x) - ∫ x in (0 : ℝ)..t, G x * Y x := by
    rw [show (fun x => (FDot x - G x) * Y x)
          = (fun x => FDot x * Y x - G x * Y x) from funext fun x => sub_mul _ _ _]
    exact intervalIntegral.integral_sub (f := fun x => FDot x * Y x)
      (g := fun x => G x * Y x) (μ := volume) (a := (0 : ℝ)) (b := t)
      ((hFDc.mul hYc).intervalIntegrable _ _)
      ((hGc.mul hYc).intervalIntegrable _ _)
  have hIBP' : (∫ x in (0 : ℝ)..t, FDot x * Y x)
      = (F t * Y t - F 0 * Y 0) - ∫ x in (0 : ℝ)..t, F x * YDot x := by
    rw [eq_sub_iff_add_eq]
    exact (intervalIntegral.integral_add ((hFDc.mul hYc).intervalIntegrable _ _)
      ((hFc.mul hYDc).intervalIntegrable _ _)).symm.trans hIBP
  rw [hIntEq, hsplit, hIBP', hscalar]

end Qatlib.Papers.AdiabBounds06.MainResults
