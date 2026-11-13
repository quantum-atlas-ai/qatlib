/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualPolynomial
import Qatlib.Papers.AmpInvReqTang26.RootLaws.Lemma23
import Qatlib.Foundations.MatrixAlgebra.TorusMoments.RootMoments

/-!
# Actual circuit densities and phase-twist invariance

Defines `circuitDensity` as the uniform average of the output outer products of a forward-query
circuit and identifies it with the density obtained from its query polynomials. For fewer than
`q` queries, averaging over independent `q`th-root phases is invariant under fixed
coordinatewise unit-modulus twists, including the twist used for the unbiased ensemble in
Problem 4.1. See [TangWright2025].

## Main statements

* `circuitDensity_polynomial`: the actual and polynomial density descriptions agree.
* `actual_circuit_density_twist`: uniform root averaging is invariant under coordinatewise phase
  twists when `n < q`.
* `actual_problem41_unbiased_invariance`: the specialized twist invariance for Problem 4.1.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.RootLaws
open Qatlib.Foundations.MatrixAlgebra.TorusMoments

/-- The uniform average over `u : Fin d → Fin q` of the output outer-product matrices for the
oracle phase vector `z u`. -/
def circuitDensity {q d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (z : (Fin d → Fin q) → Fin d → ℂ) : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  fun x y => (Fintype.card (Fin d → Fin q) : ℂ)⁻¹ *
    ∑ u : Fin d → Fin q, run id Alg n (z u) x * star (run id Alg n (z u) y)

/-- The averaged circuit density equals the polynomial density of the circuit's query-polynomial
family. -/
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

/-- For positive `q` and `n < q`, multiplying each uniformly sampled root phase by a fixed
unit-modulus coordinate factor leaves the averaged circuit density unchanged. -/
theorem actual_circuit_density_twist {q d a : ℕ} (hq : 0<q)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q)
    (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1) :
    circuitDensity (q := q) Alg n (fun u i => D i * phase q (u i)) =
      circuitDensity (q := q) Alg n (fun u i => phase q (u i)) := by
  rw [circuitDensity_polynomial, circuitDensity_polynomial]
  exact polynomialDensity_twist hq (omega q) (omega_isPrimitiveRoot q hq) D hD
    (queryPolynomial Alg n) (fun x h hh i => queryPolynomial_support_lt Alg n q hn x h hh i)

/-- For positive `q` and `n < q`, twisting the sampled `q`th-root phases by `phase d` leaves the
averaged circuit density unchanged [Tang and Wright, Problem 4.1][TangWright2025]. -/
theorem actual_problem41_unbiased_invariance {q d a : ℕ} (hq : 0<q)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q) :
    circuitDensity (q := q) Alg n (fun u i => phase d i * phase q (u i)) =
      circuitDensity (q := q) Alg n (fun u i => phase q (u i)) :=
  actual_circuit_density_twist hq Alg n hn (phase d) (norm_phase d)

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
