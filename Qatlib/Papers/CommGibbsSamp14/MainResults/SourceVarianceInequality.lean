/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommGibbsSamp14.MainResults.Framework.ProjectionCalculus

set_option backward.isDefEq.respectTransparency false

/-!
# Commuting Gibbs samplers — the variance inequality of Proposition 20

Fixed source: M. J. Kastoryano and F. G. S. L. Brandão, *Quantum Gibbs Samplers: the
commuting case*, arXiv:1409.3435v3 (7 June 2016), Proposition 20, p. 20,
Eqs. (61)–(65).

Proposition 20 is the only analytic ingredient of the paper's main theorems whose proof
uses nothing but general Hilbert-space properties of the conditional expectations (the
remark after Eq. (65) stresses that no Gibbs form of `ρ` and no locality is used).  It is
therefore fully provable in the abstract `L²(ρ)` model, and is proved here in complete
tactic form, with the paper's notation `E_A`, `E_B`, `E_{A∪B}` and constants `ε`,
`(1 − 2ε)⁻¹` as in Eq. (62).
-/

set_option autoImplicit false

namespace Qatlib.Papers.CommGibbsSamp14.MainResults

open Qatlib.Papers.CommGibbsSamp14.MainResults.Framework
open scoped InnerProductSpace

variable {V Region : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Proposition 20** (arXiv:1409.3435v3, p. 20, Eqs. (61)–(62)).

Let `ρ ∈ S_Λ^+`, let `A, B ⊆ Λ` overlap, and let `E ∈ {E^ρ, E^L}` be one of the
paper's conditional-expectation families.  Write `E_A`, `E_B`, `E_{A∪B}` for `E` on the
corresponding regions and, as in Eq. (61), suppose that for every observable `f`

`Cov_{A∪B}(E_A f, E_B f) ≤ ε Var_{A∪B}(f)`.

Then for every `f`, Eq. (62) holds:
`Var_{A∪B}(f) ≤ (1 − 2ε)⁻¹ (Var_A(f) + Var_B(f))`.

The absorption hypotheses `hAbsA`, `hAbsB` are the nestedness of the conditional
expectations (`E_{A∪B} ∘ E_A = E_{A∪B} = E_{A∪B} ∘ E_B`) used in the paper's proof via
Eq. (63); they are the only structural facts about `E` that the argument needs, as noted
in the paper right after Eq. (65). -/
theorem proposition20_variance_inequality
    [RegionOps Region] (S : PaperSetup V Region) (E : Region → V → V)
    (hE : E = S.Eρ ∨ E = S.EL) (A B : Region) (eps : ℝ)
    (hAbsA : ∀ f : V, E (RegionOps.union A B) (E A f) = E (RegionOps.union A B) f)
    (hAbsB : ∀ f : V, E (RegionOps.union A B) (E B f) = E (RegionOps.union A B) f)
    (hBound : ∀ f : V,
      condCov (E (RegionOps.union A B)) (E A f) (E B f) ≤
        eps * condVar (E (RegionOps.union A B)) f)
    (heps : 2 * eps < 1) :
    ∀ f : V,
      condVar (E (RegionOps.union A B)) f ≤
        (1 - 2 * eps)⁻¹ * (condVar (E A) f + condVar (E B) f) := by
  intro f
  exact Framework.prop20_variance_inequality (E A) (E B) (E (RegionOps.union A B)) eps
    hAbsA hAbsB hBound heps f

end Qatlib.Papers.CommGibbsSamp14.MainResults
