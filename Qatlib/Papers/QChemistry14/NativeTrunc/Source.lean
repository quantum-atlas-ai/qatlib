/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.NativeTrunc.Fock
import Qatlib.Foundations.MatrixGeometry.OperatorCutoff.Cutoff
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Papers.QChemistry14.NativeTrunc
open Qatlib.Foundations.MatrixGeometry.OperatorCutoff

abbrev Term (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n × Fin n × Fin n)

def termWord {n : ℕ} : Term n → List (Fin n × Bool)
  | .inl (p,q) => [(p,true),(q,false)]
  | .inr (p,q,r,s) => [(p,true),(q,true),(r,false),(s,false)]

def termOperator {n : ℕ} (t : Term n) : Fock n →L[ℂ] Fock n := monomial (termWord t)

theorem termOperator_norm {n : ℕ} (t : Term n) : ‖termOperator t‖ ≤ 1 :=
  monomial_norm_le_one (termWord t)

def sourceCoefficient {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) : Term n → ℂ
  | .inl (p,q) => h₁ p q
  | .inr (p,q,r,s) => h₂ p q r s / 2

def sourceHamiltonian {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) : Fock n →L[ℂ] Fock n :=
  hamiltonian (sourceCoefficient h₁ h₂) termOperator

def sourceCutoff {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ) : Fock n →L[ℂ] Fock n :=
  cutoff (sourceCoefficient h₁ h₂) termOperator δ

theorem source_cutoff_opNorm {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ) :
    ‖sourceHamiltonian h₁ h₂ - sourceCutoff h₁ h₂ δ‖ ≤
      removedMass (sourceCoefficient h₁ h₂) δ :=
  cutoff_opNorm (E := Fock n) (ι := Term n) (sourceCoefficient h₁ h₂)
    (termOperator (n := n)) δ (termOperator_norm (n := n))

theorem source_cutoff_energy {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ)
    (ψ : Fock n) (hψ : ‖ψ‖ = 1) :
    |energy (sourceHamiltonian h₁ h₂) ψ - energy (sourceCutoff h₁ h₂ δ) ψ| ≤
      removedMass (sourceCoefficient h₁ h₂) δ :=
  cutoff_energy (E := Fock n) (ι := Term n) (sourceCoefficient h₁ h₂)
    (termOperator (n := n)) δ (termOperator_norm (n := n)) ψ hψ

theorem source_cutoff_count {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ)
    (ψ : Fock n) (hψ : ‖ψ‖ = 1) :
    |energy (sourceHamiltonian h₁ h₂) ψ - energy (sourceCutoff h₁ h₂ δ) ψ| ≤
      ((Finset.univ.filter (fun t => ‖sourceCoefficient h₁ h₂ t‖ < δ)).card : ℝ) * δ :=
  (source_cutoff_energy h₁ h₂ δ ψ hψ).trans (removedMass_le_count _ δ)

theorem source_cutoff_precision {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ ε : ℝ)
    (hbudget : removedMass (sourceCoefficient h₁ h₂) δ ≤ ε)
    (ψ : Fock n) (hψ : ‖ψ‖ = 1) :
    |energy (sourceHamiltonian h₁ h₂) ψ - energy (sourceCutoff h₁ h₂ δ) ψ| ≤ ε :=
  (source_cutoff_energy h₁ h₂ δ ψ hψ).trans hbudget
end Qatlib.Papers.QChemistry14.NativeTrunc
