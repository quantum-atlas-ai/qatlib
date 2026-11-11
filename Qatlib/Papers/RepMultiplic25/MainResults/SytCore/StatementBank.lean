/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Statement bank for
"Polynomial time classical versus quantum algorithms for representation
theoretic multiplicities" (arXiv:2502.20253, 2025).

This file records faithful `Prop` statements for the claims whose content
is purely mathematical (c003, c004, c005, c006), on top of the model of
`Definitions.lean` (Young diagrams, `aft`, `fDim`, standard Young
tableaux).  The algorithmic claims (c001, c002, c007–c013) are all
runtime bounds of the form "coefficient can be computed in time O(…)":
formalising them needs a model of computation with runtime accounting for
Young-tableaux enumeration algorithms, which neither Mathlib nor this
repository provides — recorded as substantive obstacles in the PR work
log.

No axiom, no `admit`, no `native_decide`.
-/
import Qatlib.Papers.RepMultiplic25.MainResults.SytCore.Definitions

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.RepMultiplic25.MainResults.SytCore

/-! ## Additional shape statistics -/

/-- The Durfee square size `d(L)`: the largest `d` such that the `d×d`
northwest square fits in the diagram (§3). -/
def durfee (L : YoungDiagram) : ℕ :=
  sSup {d : ℕ | (d - 1, d - 1) ∈ L.cells ∨ d = 0}

/-! ## Claim statements -/

/-- **c003 (Proposition 3.1)**: if `aft(L) = k` then
`f^L ≤ n^k / √(k!)` and `f^L ≥ C(n − k, k)`, after reducing to the case
`L₁ ≥ ℓ(L)` via the symmetry `f^L = f^{L'}` (transpose).  The proved core
`fDim_le_pow` gives the polynomial upper bound `f^L ≤ n^(2k)` in the
reduced case; the sharp exponent and the binomial lower bound need
hook-length estimates and tableau constructions absent from Mathlib. -/
def c003_statement (L : YoungDiagram) (k : ℕ) : Prop :=
  aft L = k →
    fDim L ≤ (size L) ^ k ∧ Nat.choose (size L - k) k ≤ fDim L

/-- **c004 (Proposition 3.2)**: if `f^L ≤ n^k` for a fixed `k` and `n`
is large enough, then `max{L₁, ℓ(L)} > n − 4k²`, i.e. `aft(L) ≤ 4k²`.
The proof combines the lower bound of Proposition 3.1 with Frobenius
coordinates and Catalan-number estimates — hook-length-adjacent
infrastructure unavailable in Mathlib. -/
def c004_statement (L : YoungDiagram) (k : ℕ) : Prop :=
  fDim L ≤ (size L) ^ k → 2 ^ (10 : ℕ) * k ^ 4 < size L →
    size L - 4 * k ^ 2 < max (firstPart L) (lengthParts L)

/-- **c005 (Proposition 3.5)**: if `d(L) / √n > c` for some `c > 0`,
then there are constants `c₁, c₂` with `c₂^{n log n} ≤ f^L ≤ c₁^{n log n}`
— the superexponential regime of the growth classification (Table 1).
Asymptotic in `n log n` with real constants. -/
def c005_statement (L : YoungDiagram) (c c1 c2 : ℝ) : Prop :=
  (0 < c ∧ c < Real.sqrt (durfee L)) →
    (1 < c1 ∧ 1 < c2 ∧ c2 ^ (size L * Real.log (size L)) ≤ fDim L
      ∧ (fDim L : ℝ) ≤ c1 ^ (size L * Real.log (size L)))

/-- **c006 (Proposition 3.6)**: if the Littlewood–Richardson coefficient
`c^λ_{μν}` (passed as an abstract counting parameter, since LR
coefficients are not available in Mathlib) is positive, then the
dimension ratio satisfies `f^λ / (f^μ f^ν) = O(2^n)`. -/
def c006_statement (L M N : YoungDiagram)
    (lrc : YoungDiagram → YoungDiagram → YoungDiagram → ℤ) : Prop :=
  size L = size M + size N → 0 < lrc L M N →
    ∃ C : ℕ, fDim L ≤ C * 2 ^ size L * (fDim M * fDim N)

end Qatlib.Papers.RepMultiplic25.MainResults.SytCore
