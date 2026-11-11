/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Pi
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Taylor polynomials for ordered exponential products

This module defines `expProductGenerator`, the generator −iaⱼHⱼ, and `expProductMul`, an ordered
product indexed by a finite type. The polynomial `expProductTaylor` sums the ordered
exponential-series coefficients over multi-indices of total degree at most the truncation order.
See [ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `expProductGenerator`: The matrix generator −i aⱼ Hⱼ for the j-th scaled Hamiltonian
  evolution.
* `expProductMul`: The ordered product of the matrices in A, using the order of their finite
  indices.
* `expProductTaylor`: The total-degree-ℓ truncation of the ordered product of exponential
  series, summing t^(∑ pⱼ) times the ordered products of Aⱼ^pⱼ / pⱼ! over multi-indices with ∑
  pⱼ ≤ ℓ.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds

open scoped Matrix.Norms.L2Operator

/-- The matrix generator −i aⱼ Hⱼ for the j-th scaled Hamiltonian evolution. -/
noncomputable def expProductGenerator {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (a : Fin M → ℝ) (H : Fin M → Matrix I I ℂ) (j : Fin M) : Matrix I I ℂ :=
  (-(Complex.I * (a j : ℂ))) • H j

/-- The ordered product of the matrices in A, using the order of their finite indices. -/
noncomputable def expProductMul {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (A : Fin M → Matrix I I ℂ) : Matrix I I ℂ :=
  (List.ofFn fun j => A j).prod

/-- The total-degree-ℓ truncation of the ordered product of exponential series, summing t^(∑ pⱼ)
times the ordered products of Aⱼ^pⱼ / pⱼ! over multi-indices with ∑ pⱼ ≤ ℓ. -/
noncomputable def expProductTaylor {I : Type} [Fintype I] [DecidableEq I] {M : ℕ}
    (A : Fin M → Matrix I I ℂ) (t : ℝ) (ℓ : ℕ) : Matrix I I ℂ :=
  ∑ p ∈ (Fintype.piFinset fun _ : Fin M => Finset.range (ℓ + 1)).filter
      (fun p => (∑ j, p j) ≤ ℓ),
    ((t ^ (∑ j, p j) : ℝ) : ℂ) • expProductMul (fun j => ((p j).factorial : ℂ)⁻¹ • A j ^ (p j))

end Qatlib.Papers.HamLCUSim12.TaylorBounds
