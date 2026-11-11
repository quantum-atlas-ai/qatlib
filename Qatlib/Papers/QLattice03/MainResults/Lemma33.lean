/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Defs

/-!
# QLattice03 — Lemma 3.3: coefficient bound for the shortest vector

Paper: Oded Regev, *Quantum Computation and Lattice Problems*,
arXiv:cs/0304005v1, Section 3.2, Lemma 3.3 (page 6).

> Lemma 3.3  Consider the representation of the shortest vector
> `ū = Σᵢ uᵢ b̄ᵢ` in the LLL-reduced lattice basis.  Then `|uᵢ| ≤ 2^{2n}`
> for `i ∈ [n]`.

The proof (p. 6) changes to the orthonormal basis `b̄*ᵢ/‖b̄*ᵢ‖`, uses
`‖b̄*ᵢ‖ ≥ 2^{-(i-1)/2}‖b̄*₁‖ ≥ 2^{-n}‖ū‖` and the size-reduction bound
`|b_{ij}| ≤ ½‖b̄*ⱼ‖`, and inducts downwards: `|uₙ| ≤ 2ⁿ` and
`|u_k| ≤ 2^{2n-k}`.

This file fixes the LLL-reducedness hypothesis as explicit structural data
(the Gram–Schmidt lengths and coefficients with the two LLL axioms) and records
the coefficient bound as an *open obligation*.

## Status and modelling gap

`shortestVector_coeff_bound` below is a `def … : Prop`; it is **not** asserted
as a theorem.  Moreover the abstraction is not yet adequate to the paper: the
structure `LLLData` records the LLL axioms for `beta`, `mu` but does not relate
them to the basis `b` (no Gram–Schmidt expansion of `b`, hence no link between
`u` and the coefficients).  Consequently the proposition below is *not* the
paper's true lemma and must not be read as established.  Closing the gap
requires formalising Gram–Schmidt orthogonalisation of an integer basis and the
coordinate identity `u = Σᵢ (Σ_{j≥i} u_j μ_{j,i}) b*ᵢ/‖b*ᵢ‖`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

open Qatlib.Papers.QLattice03.MainResults

/-- Structural data of an LLL-reduced basis, exactly the facts recalled in
Regev (2003), §3.2: Gram–Schmidt lengths `βᵢ = ‖b̄*ᵢ‖`, the coefficients `μᵢⱼ`
of `b̄ᵢ` in the Gram–Schmidt basis (with `μᵢᵢ = 1`), size reduction
`|μᵢⱼ| ≤ ½`, and the Lovász condition `βᵢ ≤ 2βᵢ₊₁`. -/
structure LLLData {n : ℕ} (b : LatticeBasis n) where
  /-- Gram–Schmidt lengths `‖b̄*ᵢ‖`. -/
  beta : Fin n → ℝ
  /-- Coefficients of `b̄ᵢ` in the Gram–Schmidt basis. -/
  mu : Fin n → Fin n → ℝ
  beta_pos : ∀ i, 0 < beta i
  diag : ∀ i, mu i i = 1
  size_reduced : ∀ i j, j < i → |mu i j| ≤ (1 / 2 : ℝ)
  lovasz : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n,
    beta i ≤ 2 * beta ⟨(i : ℕ) + 1, h⟩

/-- A basis is LLL-reduced when it carries LLL structural data. -/
def IsLLLReduced {n : ℕ} (b : LatticeBasis n) : Prop := Nonempty (LLLData b)

/-- `u` is a shortest nonzero lattice vector of the lattice spanned by `b`. -/
def IsShortestVector {n : ℕ} (b : LatticeBasis n) (u : Fin n → ℤ) : Prop :=
  IsLatticeVector b u ∧ u ≠ 0 ∧ ∀ v : Fin n → ℤ, IsLatticeVector b v → v ≠ 0 → normsq u ≤ normsq v

/-- **Lemma 3.3** (open obligation): in an LLL-reduced basis, the shortest
vector has a representation whose coefficients are all bounded by `2^{2n}` in
absolute value.  See the module docstring: this abstraction of
LLL-reducedness does not yet constrain the basis, so this is a specification
placeholder rather than the paper's lemma. -/
def shortestVector_coeff_bound {n : ℕ} (b : LatticeBasis n) (u : Fin n → ℤ)
    (hLLL : IsLLLReduced b) (hu : IsShortestVector b u) : Prop :=
  ∃ c : Fin n → ℤ, (∀ j, u j = ∑ i : Fin n, c i * b i j) ∧
    ∀ i, |c i| ≤ (2 : ℤ) ^ (2 * n)

end Qatlib.Papers.QLattice03.MainResults
