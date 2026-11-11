/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.FiniteBudget
import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalWord
import Qatlib.Papers.LowEnergyProd24.RetainedBound.RetainedIntegral
import Qatlib.Papers.LowEnergyProd24.RetainedBound.SectorSplit

/-!
# Retained-error calculus for physical Hamiltonians

This module transports the Duhamel identity, retained-error integral, and spectral-sector
decomposition to `PhysicalHamiltonian`. It also gives repeated-step and normalized-state error
estimates for the original product word in the low-energy analysis of [HejaziZiniArrazola2024].

## Main statements

* `retained_integral`: Bounds the retained error by compressed-defect and leakage integrals.
* `state_tail`: Adds twice the input high-energy tail to a repeated-step low-energy bound.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedBound.Physical
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The product word for `h.asBounded` equals the original physical product word. -/
theorem original_word_representation (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t : ℝ) :
    ProductError.approximate h.asBounded stages t=CenterTransport.approximate h stages t := rfl

/-- The Hamiltonian defect of the physical product word, defined as `Complex.I` times the
difference between its instantaneous generator and the total generator. -/
def hamiltonianDefect (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  Complex.I • (generator (stages.map (CenterTransport.stageGenerator h)) t-CenterTransport.totalGenerator h)

/-- The original physical product-formula error satisfies the Duhamel identity with the
Hamiltonian defect and phase `-Complex.I` [HejaziZiniArrazola2024]. -/
theorem duhamel (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    CenterTransport.approximate h stages t-evolve h.total t =
      ∫ s in (0 : ℝ)..t, evolve h.total (t-s)*((-Complex.I) • hamiltonianDefect h stages s)*CenterTransport.approximate h stages s :=
  RetainedBound.actual_duhamel_phased h.asBounded stages t

/-- For nonnegative time, the error between the output cutoff `Λ` and input cutoff `Δ` is
bounded by the compressed-defect integral plus the defect-weighted leakage integral
[HejaziZiniArrazola2024]. -/
theorem retained_integral (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) (ht : 0 ≤ t) :
    ‖low h.total h.total_hermitian Λ*(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      (∫ s in (0 : ℝ)..t, ‖low h.total h.total_hermitian Λ*hamiltonianDefect h stages s*low h.total h.total_hermitian Λ‖)+
      (∫ s in (0 : ℝ)..t, ‖hamiltonianDefect h stages s‖*
        ‖high h.total h.total_hermitian Λ*CenterTransport.approximate h stages s*low h.total h.total_hermitian Δ‖) :=
  RetainedBound.actual_source_retained_integral h.asBounded stages t Δ Λ ht

/-- When `Δ ≤ Λ`, the error on the input low-energy sector is bounded by its retained part below
`Λ` plus product-word leakage above `Λ` [HejaziZiniArrazola2024]. -/
theorem error_sector_split (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) (hΔ : Δ ≤ Λ) :
    ‖(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      ‖low h.total h.total_hermitian Λ*(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖+
      ‖high h.total h.total_hermitian Λ*CenterTransport.approximate h stages t*low h.total h.total_hermitian Δ‖ :=
  RetainedBound.actual_error_sector_split h.asBounded (CenterTransport.approximate h stages t) t Δ Λ hΔ

/-- The error after `r` powers, restricted to the low-energy input sector, is at most `r` times
the corresponding one-step error. -/
theorem repeated_error (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) :
    ‖(CenterTransport.approximate h stages t^r-evolve h.total t^r)*low h.total h.total_hermitian Δ‖ ≤
      (r : ℝ)*‖(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ :=
  ProductError.actual_repeated_error h.asBounded stages t Δ r

/-- For a unit vector, the error after `r` powers is bounded by `r` times the low-energy
one-step operator error plus twice the norm of its high-energy component. -/
theorem state_tail (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) (ψ : EuclideanSpace ℂ (Register N)) (hψ : ‖ψ‖=1) :
    ‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (CenterTransport.approximate h stages t^r-evolve h.total t^r) ψ‖ ≤
      (r : ℝ)*‖(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖+
      2*‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (high h.total h.total_hermitian Δ) ψ‖ :=
  RetainedBound.actual_state_tail_bound h.asBounded stages t Δ r ψ hψ
end Qatlib.Papers.LowEnergyProd24.RetainedBound.Physical
