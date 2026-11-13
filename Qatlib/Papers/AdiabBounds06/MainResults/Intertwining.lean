/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.Defs

/-!
# Intertwining for an adiabatic comparison evolution

Differentiating a projector identity gives the commutator relation between the
projector and the adiabatic comparison generator. Under the stated continuity,
differentiability, and Hamiltonian-commutation hypotheses, the comparison
propagator transports the initial projector to the current projector. ODE
uniqueness proves the intertwining identity.

The adiabatic approximation framework is [JansenRuskaiSeiler2007]. This is the
comparison-evolution identity, prior to any final approximation-error estimate.
-/
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabBounds06.MainResults

variable {n : ℕ}

/-- If a differentiable idempotent family commutes with `H`, its commutator with the adiabatic
generator satisfies `P * adiGenerator - adiGenerator * P = Pdot`. -/
theorem P_comm_adiGenerator (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hComm : ∀ s, H s * P s = P s * H s)
    (hProj : ∀ s, P s * P s = P s)
    (hder : ∀ s, HasDerivAt P (Pdot s) s) (s : ℝ) :
    P s * adiGenerator τ H P Pdot s - adiGenerator τ H P Pdot s * P s = Pdot s := by
  have hsand : P s * Pdot s * P s = 0 := Pdot_sandwich_eq_zero P Pdot hProj hder s
  have hCP : (Pdot s * P s - P s * Pdot s) * P s = Pdot s * P s := by
    rw [sub_mul]
    have h1 : (Pdot s * P s) * P s = Pdot s * P s := by rw [mul_assoc, hProj s]
    have h2 : (P s * Pdot s) * P s = 0 := hsand
    rw [h1, h2, sub_zero]
  have hPC : P s * (Pdot s * P s - P s * Pdot s) = -(P s * Pdot s) := by
    rw [mul_sub]
    have h1 : P s * (Pdot s * P s) = 0 := by simpa only [mul_assoc] using! hsand
    have h2 : P s * (P s * Pdot s) = P s * Pdot s := by rw [← mul_assoc, hProj s]
    rw [h1, h2]
    abel
  have hcommC :
      (Pdot s * P s - P s * Pdot s) * P s - P s * (Pdot s * P s - P s * Pdot s)
        = Pdot s := by
    rw [hCP, hPC, sub_neg_eq_add]
    exact (Pdot_eq_offdiag P Pdot hProj hder s).symm
  have hkey :
      (Complex.I * (τ : ℂ)) • (P s * H s)
          - P s * (Pdot s * P s - P s * Pdot s)
          - ((Complex.I * (τ : ℂ)) • (H s * P s)
              - (Pdot s * P s - P s * Pdot s) * P s) = Pdot s := by
    rw [hComm s]
    have hcancel :
        (Complex.I * (τ : ℂ)) • (P s * H s)
            - P s * (Pdot s * P s - P s * Pdot s)
            - ((Complex.I * (τ : ℂ)) • (P s * H s)
                - (Pdot s * P s - P s * Pdot s) * P s)
          = (Pdot s * P s - P s * Pdot s) * P s
              - P s * (Pdot s * P s - P s * Pdot s) := by
      abel
    rw [hcancel, hcommC]
  simp only [adiGenerator]
  rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  exact hkey

/-- The adiabatic comparison propagator intertwines `P 0` and `P s`, as used in
[Jansen, Ruskai & Seiler][JansenRuskaiSeiler2007]. -/
theorem intertwining (τ : ℝ) (H P Pdot : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hComm : ∀ s, H s * P s = P s * H s)
    (hProj : ∀ s, P s * P s = P s)
    (hder : ∀ s, HasDerivAt P (Pdot s) s)
    (hHc : Continuous H) (hPc : Continuous P) (hPdc : Continuous Pdot) :
    ∀ s, UτA τ H P Pdot s * P 0 = P s * UτA τ H P Pdot s := by
  have hAgen : Continuous (adiGenerator τ H P Pdot) := by
    unfold adiGenerator
    fun_prop
  have hU : ∀ t, HasDerivAt (UτA τ H P Pdot)
      (-(adiGenerator τ H P Pdot t * UτA τ H P Pdot t)) t := by
    intro t
    simpa only [UτA] using!
      orderedEvolution_hasDerivAt (adiGenerator τ H P Pdot) hAgen 0 t
  have hf : ∀ t, HasDerivAt (fun u => UτA τ H P Pdot u * P 0)
      (-(adiGenerator τ H P Pdot t * (UτA τ H P Pdot t * P 0))) t := by
    intro t
    have h2 := (hU t).mul_const (P 0)
    convert! h2 using 1
    noncomm_ring
  have hg : ∀ t, HasDerivAt (fun u => P u * UτA τ H P Pdot u)
      (-(adiGenerator τ H P Pdot t * (P t * UτA τ H P Pdot t))) t := by
    intro t
    have hPU : HasDerivAt (fun u => P u * UτA τ H P Pdot u)
        (Pdot t * UτA τ H P Pdot t
          + P t * (-(adiGenerator τ H P Pdot t * UτA τ H P Pdot t))) t :=
      (hder t).mul (hU t)
    have hcomm := P_comm_adiGenerator τ H P Pdot hComm hProj hder t
    convert! hPU using 1
    rw [← hcomm]
    noncomm_ring
  have huniq := ordered_matrix_ode_unique (adiGenerator τ H P Pdot) hAgen
    (fun u => UτA τ H P Pdot u * P 0)
    (fun u => P u * UτA τ H P Pdot u) 0
    (by simp only [UτA, orderedEvolution_self, one_mul, mul_one]) hf hg
  intro s
  exact congrFun huniq s

end Qatlib.Papers.AdiabBounds06.MainResults
