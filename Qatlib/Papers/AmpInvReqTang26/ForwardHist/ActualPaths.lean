/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualPolynomial

/-!
# Histogram expansion of forward-query amplitudes

The finite set `pathSupport` collects the monomials appearing in the circuit amplitudes. When `n
< q`, `pathHistogram` embeds their exponent vectors into `Fin q`, and `actual_path_expansion`
reconstructs the circuit from the coefficient matrix `pathCoefficient`. This development
supports the treatment in [TangWright2025].

## Main statements

* `pathHistogram_injective`: distinct supported monomials give distinct histograms.
* `pathHistogram_mass`: each supported histogram has total mass `n`.
* `actual_path_expansion`: the circuit amplitude as a sum over supported histograms.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The union of the monomial supports of all output-coordinate query polynomials after `n`
queries. -/
def pathSupport {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : Finset (Fin d →₀ ℕ) := by
  classical
  exact Finset.univ.biUnion (fun x => (queryPolynomial Alg n x).support)

/-- Every exponent vector in `pathSupport` occurs in the query polynomial of some output
coordinate. -/
theorem pathSupport_member {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (h : pathSupport Alg n) : ∃ x, h.val ∈ (queryPolynomial Alg n x).support := by
  classical
  simpa only [pathSupport,Finset.mem_biUnion,Finset.mem_univ,true_and] using! h.property

/-- The exponent vector of a supported monomial, regarded coordinatewise as an element of `Fin
q` using `n < q`. -/
def pathHistogram {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n q : ℕ) (hn : n<q)
    (h : pathSupport Alg n) : Fin d → Fin q := fun i => ⟨h.val i,by
  obtain ⟨x,hx⟩ := pathSupport_member Alg n h
  exact queryPolynomial_support_lt Alg n q hn x h.val hx i⟩

/-- Embedding supported exponent vectors into `Fin q` preserves their distinctness. -/
theorem pathHistogram_injective {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) : Function.Injective (pathHistogram Alg n q hn) := by
  intro h k heq
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact congrArg Fin.val (congrFun heq i)

/-- Every supported histogram has total mass equal to the number `n` of forward queries
[TangWright2025]. -/
theorem pathHistogram_mass {d a : ℕ} (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) (h : pathSupport Alg n) :
    ∑i,(pathHistogram Alg n q hn h i:ℕ)=n := by
  obtain ⟨x,hx⟩ := pathSupport_member Alg n h
  have hd := (queryPolynomial_homogeneous Alg n x).degree_eq_sum_deg_support hx
  have hf := Finsupp.sum_fintype h.val (fun (_ : Fin d) (v : ℕ) => v) (by intro i; rfl)
  change ∑i,h.val i=n
  exact hf.symm.trans hd.symm

/-- The matrix of query-polynomial coefficients, indexed by output coordinates and supported
exponent vectors. -/
def pathCoefficient {d a : ℕ} (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    Matrix (Fin d × Fin a) (pathSupport Alg n) ℂ := fun x h =>
  (queryPolynomial Alg n x).coeff h.val

/-- Each circuit amplitude is the sum of its supported histogram coefficients multiplied by the
corresponding products of oracle phases [TangWright2025]. -/
theorem actual_path_expansion {d a : ℕ} {S : Type} (phi : S → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n q : ℕ) (hn : n<q)
    (U : Fin d → S) (x : Fin d × Fin a) :
    run phi Alg n U x = ∑ h : pathSupport Alg n,
      pathCoefficient Alg n x h * ∏i, phi (U i) ^ (pathHistogram Alg n q hn h i:ℕ) := by
  classical
  rw [← queryPolynomial_eval phi Alg n U x,MvPolynomial.eval_eq']
  change (∑h ∈ (queryPolynomial Alg n x).support,
      (queryPolynomial Alg n x).coeff h * ∏i, phi (U i)^h i) =
    ∑h : pathSupport Alg n,(queryPolynomial Alg n x).coeff h.val * ∏i,phi (U i)^h.val i
  rw [Finset.sum_coe_sort (pathSupport Alg n) (fun h => (queryPolynomial Alg n x).coeff h * ∏i,phi (U i)^h i)]
  apply Finset.sum_subset
  · intro h hh
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hh⟩
  · intro h _ hh
    simp only [MvPolynomial.mem_support_iff,not_not] at hh
    rw [hh,zero_mul]

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
