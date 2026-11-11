/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.NativeTrunc.Fock
import Qatlib.Foundations.MatrixGeometry.OperatorCutoff.Cutoff

/-!
# Coefficient cutoff bounds for Fock Hamiltonians

This module constructs finite one-body and two-body Hamiltonian sums from concrete Fock ladder
monomials, including the factor of one half in the two-body coefficients. It bounds cutoff error
in operator norm and in the real energy expectation of the same normalized state by the deleted
coefficient mass. See [McCleanEtAl2014].

## Main statements

* `source_cutoff_opNorm`: The operator norm of the full Hamiltonian minus its coefficient cutoff
  is at most the total mass of the removed coefficients.
* `source_cutoff_energy`: For a normalized Fock state, the absolute difference of the full and
  cutoff energy expectations in that same state is at most the removed coefficient mass.
* `source_cutoff_precision`: If the removed coefficient mass is at most `ε`, then every
  normalized Fock state has absolute same-state energy change at most `ε` under the cutoff.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Papers.QChemistry14.NativeTrunc
open Qatlib.Foundations.MatrixGeometry.OperatorCutoff

/-- The disjoint union of one-body mode pairs and two-body mode quadruples. -/
abbrev Term (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n × Fin n × Fin n)

/-- The ordered creation-annihilation word for a one-body term or a two-body term. -/
def termWord {n : ℕ} : Term n → List (Fin n × Bool)
  | .inl (p,q) => [(p,true),(q,false)]
  | .inr (p,q,r,s) => [(p,true),(q,true),(r,false),(s,false)]

/-- The Fock-space ladder monomial corresponding to a Hamiltonian term label. -/
def termOperator {n : ℕ} (t : Term n) : Fock n →L[ℂ] Fock n := monomial (termWord t)

/-- Every one-body or two-body term operator has operator norm at most one. -/
theorem termOperator_norm {n : ℕ} (t : Term n) : ‖termOperator t‖ ≤ 1 :=
  monomial_norm_le_one (termWord t)

/-- The one-body coefficient `h₁ p q` or the two-body coefficient `h₂ p q r s / 2`, according to
the term label. -/
def sourceCoefficient {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) : Term n → ℂ
  | .inl (p,q) => h₁ p q
  | .inr (p,q,r,s) => h₂ p q r s / 2

/-- The finite Fock-space Hamiltonian sum with the supplied one-body and halved two-body
coefficients. -/
def sourceHamiltonian {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) : Fock n →L[ℂ] Fock n :=
  hamiltonian (sourceCoefficient h₁ h₂) termOperator

/-- The coefficient-thresholded Fock Hamiltonian at cutoff `δ`. -/
def sourceCutoff {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ) : Fock n →L[ℂ] Fock n :=
  cutoff (sourceCoefficient h₁ h₂) termOperator δ

/-- The operator norm of the full Hamiltonian minus its coefficient cutoff is at most the total
mass of the removed coefficients. See [McCleanEtAl2014]. -/
theorem source_cutoff_opNorm {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ) :
    ‖sourceHamiltonian h₁ h₂ - sourceCutoff h₁ h₂ δ‖ ≤
      removedMass (sourceCoefficient h₁ h₂) δ :=
  cutoff_opNorm (E := Fock n) (ι := Term n) (sourceCoefficient h₁ h₂)
    (termOperator (n := n)) δ (termOperator_norm (n := n))

/-- For a normalized Fock state, the absolute difference of the full and cutoff energy
expectations in that same state is at most the removed coefficient mass. See
[McCleanEtAl2014]. -/
theorem source_cutoff_energy {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ)
    (ψ : Fock n) (hψ : ‖ψ‖ = 1) :
    |energy (sourceHamiltonian h₁ h₂) ψ - energy (sourceCutoff h₁ h₂ δ) ψ| ≤
      removedMass (sourceCoefficient h₁ h₂) δ :=
  cutoff_energy (E := Fock n) (ι := Term n) (sourceCoefficient h₁ h₂)
    (termOperator (n := n)) δ (termOperator_norm (n := n)) ψ hψ

/-- For a normalized Fock state, the absolute same-state energy change is at most the number of
coefficients of norm below `δ` multiplied by `δ`. See [McCleanEtAl2014]. -/
theorem source_cutoff_count {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ : ℝ)
    (ψ : Fock n) (hψ : ‖ψ‖ = 1) :
    |energy (sourceHamiltonian h₁ h₂) ψ - energy (sourceCutoff h₁ h₂ δ) ψ| ≤
      ((Finset.univ.filter (fun t => ‖sourceCoefficient h₁ h₂ t‖ < δ)).card : ℝ) * δ :=
  (source_cutoff_energy h₁ h₂ δ ψ hψ).trans (removedMass_le_count _ δ)

/-- If the removed coefficient mass is at most `ε`, then every normalized Fock state has
absolute same-state energy change at most `ε` under the cutoff. See [McCleanEtAl2014]. -/
theorem source_cutoff_precision {n : ℕ} (h₁ : Fin n → Fin n → ℂ)
    (h₂ : Fin n → Fin n → Fin n → Fin n → ℂ) (δ ε : ℝ)
    (hbudget : removedMass (sourceCoefficient h₁ h₂) δ ≤ ε)
    (ψ : Fock n) (hψ : ‖ψ‖ = 1) :
    |energy (sourceHamiltonian h₁ h₂) ψ - energy (sourceCutoff h₁ h₂ δ) ψ| ≤ ε :=
  (source_cutoff_energy h₁ h₂ δ ψ hψ).trans hbudget
end Qatlib.Papers.QChemistry14.NativeTrunc
