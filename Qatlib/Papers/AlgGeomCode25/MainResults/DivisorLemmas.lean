/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-! Divisor-group lemmas for
"Algebraic Geometry Codes and Decoded Quantum Interferometry"
(arXiv:2510.06603, 2025).

- `divisorDegree` realizes the degree of a divisor as the sum of
  coefficients of a concrete `Finsupp` divisor group `X →₀ ℤ`;
  `divisorDegree_add` and `divisorDegree_neg` record its additivity.
- `riemann_roch_corollary` is Corollary 1 of the paper: assuming the
  Riemann–Roch relation `l D − l (K − D) = deg D − g + 1` and the
  vanishing of `l` on divisors of negative degree, any divisor with
  `deg D > 2g − 2` satisfies `l (K − D) = 0` and
  `l D = deg D − g + 1`. The Riemann–Roch space dimension `l`, the
  canonical divisor `K` and the genus `g` enter as an abstract interface
  (Riemann–Roch itself is standard background cited by the paper, not
  available in Mathlib); the divisor group and its degree are the
  concrete `Finsupp` ones.

-/
set_option autoImplicit false

namespace Qatlib.Papers.AlgGeomCode25.MainResults.DivisorLemmas

/-! ## Divisors as finitely supported integer-valued functions -/

/-- The degree of a divisor: the sum of its (finitely many) coefficients.
Here the divisor group of the curve is realized concretely as `X →₀ ℤ`,
the free abelian group on the set of points. -/
def divisorDegree {X : Type} (D : X →₀ ℤ) : ℤ :=
  D.sum fun _ c => c

/-- The degree map is additive: `deg (D + E) = deg D + deg E`. -/
theorem divisorDegree_add {X : Type} (D E : X →₀ ℤ) :
    divisorDegree (D + E) = divisorDegree D + divisorDegree E := by
  rw [divisorDegree, divisorDegree, divisorDegree,
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]

/-- The degree map is odd: `deg (−D) = −deg D`. -/
theorem divisorDegree_neg {X : Type} (D : X →₀ ℤ) :
    divisorDegree (-D) = -divisorDegree D := by
  have h0 : (-D : X →₀ ℤ) = (0 : X →₀ ℤ) - D := by rw [zero_sub]
  rw [divisorDegree, divisorDegree, h0, Finsupp.sum_sub_index (fun _ _ _ => rfl)]
  simp

/-- The degree map subtracts: `deg (D − E) = deg D − deg E`. -/
theorem divisorDegree_sub {X : Type} (D E : X →₀ ℤ) :
    divisorDegree (D - E) = divisorDegree D - divisorDegree E := by
  rw [divisorDegree, divisorDegree, divisorDegree, Finsupp.sum_sub_index (fun _ _ _ => rfl)]

/-! ## Corollary 1: the beyond-canonical Riemann–Roch dimension -/

/-- **Corollary 1 (Riemann–Roch corollary), restricted abstract form**.
Let the divisor group be the concrete `X →₀ ℤ` with its degree. Assume
the Riemann–Roch relation for an abstract Riemann–Roch dimension
`l : (X →₀ ℤ) → ℤ`, a canonical divisor `K` with `deg K = 2g − 2`, and
the standard vanishing `l E = 0` for divisors `E` of negative degree.
Then for every divisor `D` with `deg D > 2g − 2` one has
`l (K − D) = 0` and `l D = deg D − g + 1`, exactly as in the paper. -/
theorem riemann_roch_corollary {X : Type}
    (l : (X →₀ ℤ) → ℤ) (K : X →₀ ℤ) (g : ℤ)
    (hdegK : divisorDegree K = 2 * g - 2)
    (hRR : ∀ D : X →₀ ℤ, l D - l (K - D) = divisorDegree D - g + 1)
    (hvan : ∀ E : X →₀ ℤ, divisorDegree E < 0 → l E = 0)
    (D : X →₀ ℤ) (hD : 2 * g - 2 < divisorDegree D) :
    l (K - D) = 0 ∧ l D = divisorDegree D - g + 1 := by
  have hneg : divisorDegree (K - D) < 0 := by
    rw [divisorDegree_sub, hdegK]
    omega
  refine ⟨hvan _ hneg, ?_⟩
  have hrel := hRR D
  rw [hvan _ hneg] at hrel
  linarith

end Qatlib.Papers.AlgGeomCode25.MainResults.DivisorLemmas
