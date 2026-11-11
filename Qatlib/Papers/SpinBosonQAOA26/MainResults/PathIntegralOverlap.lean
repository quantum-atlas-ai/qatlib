/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceStates

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 — path-integral representation of the state overlaps

Fixed source: arXiv:2505.07929v2, Proposition 1, PDF p. 12 (main statement, eqs. (41),
(42)) and p. 25–26 (restated form, eqs. (120)–(123)).

The statement formalised here is the restated form (120): for the `Z`-inserted states
`|Ψ_l⟩` of eqs. (39), (40) the overlap is

  `⟨Ψ_k|Ψ_j⟩ = ∑_{a ∈ {±1}^{2p+1}} a_k a_{-j} f(a) H(a)`,

where `H(a) = exp(-½ ∑_{r,s} G_{r,s} Γ_r Γ_s a_r a_s)` with the four-block matrix `G`
assembled from `G^(sym)` and `G^(herm)` by eqs. (116)–(119), and `f` is the two-sided
`f` tensor of Definition 10 / eq. (123).  The path sum is `pathOverlapCplx`; the weight
is `pathWeightCplx`; the state is `psi` from `SourceStates`.

The `O(2^{2p+1})` sum is written over `SpinConfig (2p+1) = Fin (2p+1) → Bool`, and the
spin values enter through `spinVec`.
Proposition 1 is not formalized here: it needs the full path-integral computation of the
`Z`-inserted spin–boson overlaps.  The path-weight and path-overlap definitions
`pathWeightCplx`, `pathOverlapCplx` are kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.PathIntegralOverlap

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- The path-integral weight `H(a) = exp(-½ ∑_{r,s} G_{r,s} Γ_r Γ_s a_r a_s)` of
eqs. (42), (120), (71).  It is kept complex-valued because the four-block matrix `G`
of eqs. (116)–(119) is built from the complex matrices `G^(sym)`, `G^(herm)`. -/
def pathWeightCplx {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (Γ a : Fin n → ℝ) : ℂ :=
  Complex.exp (-(1 / 2) * ∑ r : Fin n, ∑ s : Fin n,
    G r s * (Γ r * Γ s * a r * a s : ℝ))

/-- The right-hand side of Proposition 1, eq. (120):

  `∑_a a_k a_{-j} f(a) H(a)`,

with `a_k = a` evaluated at the positive slot `k` (eq. (121)) and `a_{-j}` at the
negative slot `j`. -/
def pathOverlapCplx {p : ℕ} (G : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℂ)
    (Γ : Fin (2 * p + 1) → ℝ) (f : SpinConfig (2 * p + 1) → ℂ) (j k : Fin p) : ℂ :=
  ∑ a : SpinConfig (2 * p + 1),
    ((spinOf (a (posIdx p k)) * spinOf (a (negIdx p j)) : ℝ) : ℂ) *
      f a * pathWeightCplx G Γ (spinVec a)


end Qatlib.Papers.SpinBosonQAOA26.MainResults.PathIntegralOverlap
