/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AlgGeomCode25.MainResults.DivisorLemmas
import Qatlib.Papers.AlgGeomCode25.MainResults.HopiFraction

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Algebraic Geometry Codes and Decoded Quantum Interferometry"
(arXiv:2510.06603v1, 2025).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Two cores are proved in this
block: `DivisorLemmas.riemann_roch_corollary` (c004, Corollary 1 over
the concrete `Finsupp` divisor group) and
`HopiFraction.satisfaction_fraction_le_one` (the arithmetic core of
c001/c007, Theorem 1).

The remaining claims are recorded as abstract statements:
- c001/c007 (Theorem 1, DQI for HOPI): the paper states the result
  without proof, reducing it to the semicircle law of the DQI reference
  (Jordan et al.); no DQI solver, decoder, or HOPI instance model exists
  in Mathlib or in this repository (the frozen `DqiOptimization` blocks
  only provide decoder-capacity counting prerequisites).
- c002 (Theorem 2, degree of a principal divisor): needs the product
  formula for function fields of curves; Mathlib has no divisor theory
  of curves (`FunctionField` is only the stalk at the generic point).
- c003 (Theorem 3, Riemann–Roch): the paper cites Stichtenoth's
  textbook; Riemann–Roch is far beyond current Mathlib.
- c005 (Theorem 4, AG-code duality) and c006 (Theorem 5, Hermitian-code
  duality): need algebraic-geometric codes `C_L(X, P, G)`, differentials
  and residue pairings, none of which exist in Mathlib.

No axiom, no `admit`, no `native_decide`.
-/
set_option autoImplicit false

namespace Qatlib.Papers.AlgGeomCode25.MainResults

open Qatlib.Papers.AlgGeomCode25.MainResults.DivisorLemmas

/-! ## Claim statements -/

/-- **c001/c007 (Theorem 1, DQI performance for HOPI), formula shape**:
with `n = q³` Hermitian-curve constraints, constraint-set size `r`,
alphabet `F_{q²}`, and decoding radius `l` (the paper derives this from
the DQI semicircle law), the expected satisfaction fraction of the
solver output is the branch value below — the squared-Hellinger
expression in the regime `r/q² ≤ 1 − l/n` and `1` otherwise. The solver,
its decoder, and the HOPI instance model are abstracted away; see the
file docstring. -/
def c001_statement (l n r q expected : ℝ) : Prop :=
  (r / q ^ 2 ≤ 1 - l / n →
      expected = (Real.sqrt (l / n * (1 - r / q ^ 2))
        + Real.sqrt (r / q ^ 2 * (1 - l / n))) ^ 2) ∧
    (1 - l / n < r / q ^ 2 → expected = 1)

/-- **c002 (Theorem 2, degree-zero property), abstract valuation shape**:
the divisor map `v` (sending a nonzero rational function on the curve to
its principal divisor, abstractly) lands in degree zero for every
nonzero function. Proving this needs the product formula for function
fields; recorded here over the concrete `Finsupp` divisor group with an
abstract `v`. -/
def c002_statement {X F : Type} [Zero F] (v : F → (X →₀ ℤ)) : Prop :=
  ∀ f : F, f ≠ 0 → divisorDegree (v f) = 0

/-- **c003 (Theorem 3, Riemann–Roch), interface shape**: the
Riemann–Roch relation for an abstract Riemann–Roch dimension `l`, a
canonical divisor `K` of degree `2g − 2`, and the genus `g`, over the
concrete `Finsupp` divisor group. This is exactly the interface consumed
by the proved `riemann_roch_corollary` (c004). -/
def c003_statement {X : Type} (l : (X →₀ ℤ) → ℤ) (K : X →₀ ℤ) (g : ℤ) : Prop :=
  divisorDegree K = 2 * g - 2 ∧
    ∀ D : X →₀ ℤ, l D - l (K - D) = divisorDegree D - g + 1

/-- **c005 (Theorem 4, AG-code duality), abstract pairing shape**: for
a code family `code` indexed by divisors, the dual code with respect to
a pairing `b` (the residue pairing on differentials, abstracted) is
again a member of the family, at an explicitly computable divisor. The
`C_L(X, P, G)` construction, differentials and residues are abstracted
away. -/
def c005_statement {δ F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (b : V → V → F) (code : δ → Submodule F V) (G : δ) : Prop :=
  ∃ G' : δ, {x : V | ∀ y ∈ code G, b x y = 0} = (code G' : Set V)

/-- **c006 (Theorem 5, Hermitian-code duality), abstract pairing shape**:
for the Hermitian code family `C` indexed by the integer `t`, the dual
with respect to the pairing `b` is the family member at
`t' = q³ + q(q−1) − 2 − t` (equivalently `q³ + 2g − 2 − t` with genus
`g = q(q−1)/2` of the Hermitian curve over `F_{q²}`). The Hermitian
curve, its code construction and the Stichtenoth duality theorem are
abstracted away. -/
def c006_statement {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (b : V → V → F) (C : ℤ → Submodule F V) (q : ℕ) (t : ℤ) : Prop :=
  ∃ t' : ℤ, t' = (q : ℤ) ^ 3 + (q : ℤ) * ((q : ℤ) - 1) - 2 - t ∧
    {x : V | ∀ y ∈ C t, b x y = 0} = (C t' : Set V)

end Qatlib.Papers.AlgGeomCode25.MainResults
