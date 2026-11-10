/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualPolynomial
import Qatlib.Papers.AmpInvReqTang26.RootLaws.Lemma23
import Qatlib.Foundations.MatrixAlgebra.TorusMoments.RootMoments
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.RootLaws
open Qatlib.Foundations.MatrixAlgebra.TorusMoments

def circuitDensity {q d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (z : (Fin d → Fin q) → Fin d → ℂ) : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  fun x y => (Fintype.card (Fin d → Fin q) : ℂ)⁻¹ *
    ∑ u : Fin d → Fin q, run id Alg n (z u) x * star (run id Alg n (z u) y)

theorem circuitDensity_polynomial {q d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (z : (Fin d → Fin q) → Fin d → ℂ) :
    circuitDensity Alg n z = polynomialDensity (queryPolynomial Alg n) z := by
  ext x y
  simp only [circuitDensity, polynomialDensity]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have hx := queryPolynomial_eval id Alg n (z u) x
  have hy := queryPolynomial_eval id Alg n (z u) y
  change (MvPolynomial.eval (z u)) (queryPolynomial Alg n x) = _ at hx
  change (MvPolynomial.eval (z u)) (queryPolynomial Alg n y) = _ at hy
  rw [hx, hy]

theorem actual_circuit_density_twist {q d a : ℕ} (hq : 0<q)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q)
    (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1) :
    circuitDensity (q := q) Alg n (fun u i => D i * phase q (u i)) =
      circuitDensity (q := q) Alg n (fun u i => phase q (u i)) := by
  rw [circuitDensity_polynomial, circuitDensity_polynomial]
  exact polynomialDensity_twist hq (omega q) (omega_isPrimitiveRoot q hq) D hD
    (queryPolynomial Alg n) (fun x h hh i => queryPolynomial_support_lt Alg n q hn x h hh i)

theorem actual_problem41_unbiased_invariance {q d a : ℕ} (hq : 0<q)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q) :
    circuitDensity (q := q) Alg n (fun u i => phase d i * phase q (u i)) =
      circuitDensity (q := q) Alg n (fun u i => phase q (u i)) :=
  actual_circuit_density_twist hq Alg n hn (phase d) (norm_phase d)

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
