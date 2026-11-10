/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.FiniteBudget
import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalWord
import Qatlib.Papers.LowEnergyProd24.RetainedBound.RetainedIntegral
import Qatlib.Papers.LowEnergyProd24.RetainedBound.SectorSplit
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

theorem original_word_representation (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t : ℝ) :
    ProductError.approximate h.asBounded stages t=CenterTransport.approximate h stages t := rfl

def hamiltonianDefect (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  Complex.I • (generator (stages.map (CenterTransport.stageGenerator h)) t-CenterTransport.totalGenerator h)

theorem duhamel (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    CenterTransport.approximate h stages t-evolve h.total t =
      ∫ s in (0 : ℝ)..t, evolve h.total (t-s)*((-Complex.I) • hamiltonianDefect h stages s)*CenterTransport.approximate h stages s :=
  RetainedBound.actual_duhamel_phased h.asBounded stages t

theorem retained_integral (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) (ht : 0 ≤ t) :
    ‖low h.total h.total_hermitian Λ*(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      (∫ s in (0 : ℝ)..t, ‖low h.total h.total_hermitian Λ*hamiltonianDefect h stages s*low h.total h.total_hermitian Λ‖)+
      (∫ s in (0 : ℝ)..t, ‖hamiltonianDefect h stages s‖*
        ‖high h.total h.total_hermitian Λ*CenterTransport.approximate h stages s*low h.total h.total_hermitian Δ‖) :=
  RetainedBound.actual_source_retained_integral h.asBounded stages t Δ Λ ht

theorem error_sector_split (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) (hΔ : Δ ≤ Λ) :
    ‖(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      ‖low h.total h.total_hermitian Λ*(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖+
      ‖high h.total h.total_hermitian Λ*CenterTransport.approximate h stages t*low h.total h.total_hermitian Δ‖ :=
  RetainedBound.actual_error_sector_split h.asBounded (CenterTransport.approximate h stages t) t Δ Λ hΔ

theorem repeated_error (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) :
    ‖(CenterTransport.approximate h stages t^r-evolve h.total t^r)*low h.total h.total_hermitian Δ‖ ≤
      (r : ℝ)*‖(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ :=
  ProductError.actual_repeated_error h.asBounded stages t Δ r

theorem state_tail (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) (ψ : EuclideanSpace ℂ (Register N)) (hψ : ‖ψ‖=1) :
    ‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (CenterTransport.approximate h stages t^r-evolve h.total t^r) ψ‖ ≤
      (r : ℝ)*‖(CenterTransport.approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖+
      2*‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (high h.total h.total_hermitian Δ) ψ‖ :=
  RetainedBound.actual_state_tail_bound h.asBounded stages t Δ r ψ hψ
end Qatlib.Papers.LowEnergyProd24.RetainedBound.Physical
