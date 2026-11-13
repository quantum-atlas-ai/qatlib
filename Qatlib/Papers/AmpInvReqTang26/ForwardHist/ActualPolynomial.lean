/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous polynomials for forward-query circuits

The recursion `queryPolynomial` represents each circuit amplitude as a multivariate polynomial
in the oracle phases. Evaluation recovers `run`, and homogeneity fixes the total degree to the
number of forward queries, bounding every supported exponent. This development supports the
treatment in [TangWright2025].

## Main statements

* `queryPolynomial_eval`: evaluation agrees with the circuit.
* `queryPolynomial_homogeneous`: total degree `n` after `n` queries.
* `queryPolynomial_support_lt`: supported exponents are below `q` when `n < q`.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix MvPolynomial
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The multivariate polynomial for an output amplitude, built recursively by alternating
interleaving matrices with multiplication by the queried phase variable. -/
def queryPolynomial {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) :
    ℕ → (Fin d × Fin a) → MvPolynomial (Fin d) ℂ
  | 0, x => C ((Alg.step 0 *ᵥ Alg.init) x)
  | n+1, x => ∑ y, C (Alg.step (n+1) x y) * (X y.1 * queryPolynomial Alg n y)

/-- Evaluating the query polynomial at the oracle phases gives the actual forward-query circuit
amplitude. -/
theorem queryPolynomial_eval {d a : ℕ} {S : Type} (phi : S → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (U : Fin d → S) (x : Fin d × Fin a) :
    MvPolynomial.eval (fun i => phi (U i)) (queryPolynomial Alg n x) = run phi Alg n U x := by
  induction n generalizing x with
  | zero => simp [queryPolynomial, run]
  | succ n ih =>
    simp only [queryPolynomial, map_sum, map_mul, eval_C, eval_X, ih,
      run, queryMat, Matrix.mulVec, dotProduct]
    simp [Matrix.diagonal]

/-- Every output-coordinate query polynomial after `n` forward queries is homogeneous of degree
`n`. -/
theorem queryPolynomial_homogeneous {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (x : Fin d × Fin a) : (queryPolynomial Alg n x).IsHomogeneous n := by
  induction n generalizing x with
  | zero => exact isHomogeneous_C _ _
  | succ n ih =>
    apply IsHomogeneous.sum
    intro y _
    have h := ((isHomogeneous_X ℂ y.1).mul (ih y)).C_mul (Alg.step (n+1) x y)
    simpa only [Nat.add_comm] using! h

/-- Every coordinate exponent of a supported monomial is at most the number of queries. -/
theorem queryPolynomial_support_le {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (x : Fin d × Fin a) (h : Fin d →₀ ℕ)
    (hh : h ∈ (queryPolynomial Alg n x).support) (i : Fin d) : h i ≤ n :=
  (MvPolynomial.monomial_le_degreeOf i hh).trans
    ((degreeOf_le_totalDegree _ i).trans (queryPolynomial_homogeneous Alg n x).totalDegree_le)

/-- If `n < q`, every coordinate exponent of a monomial in the query-polynomial support is below
`q` [TangWright2025]. -/
theorem queryPolynomial_support_lt {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n < q) (x : Fin d × Fin a) (h : Fin d →₀ ℕ)
    (hh : h ∈ (queryPolynomial Alg n x).support) (i : Fin d) : h i < q :=
  (queryPolynomial_support_le Alg n x h hh i).trans_lt hn

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
