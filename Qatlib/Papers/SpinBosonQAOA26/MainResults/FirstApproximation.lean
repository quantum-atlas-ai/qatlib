/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4 — the QAOA state in the large-`D` limit: a first approximation

Fixed source: arXiv:2505.07929v2, Lemma 4, Appendix VI, PDF pp. 39–40,
eqs. (B131)–(B133).

For the depth-`Δ`, degree-`D` tree the QAOA state satisfies (eq. (B132))

  `|Ψ^{(Δ,D)}⟩ = ∑_{a_{1:p+1}} f_{1:p}(a) |a_{p+1}⟩ ⊗ ( (1 - ∑_l γ_l²/(2D)) |Ψ^{(Δ-1,D)}⟩
      + ∑_l (-i γ_l a_l/√D) |Ψ_l^{(Δ-1,D)}⟩
      + ∑_{l<m} (-γ_l γ_m a_l a_m/D) |Ψ_{l,m}^{(Δ-1,D)}⟩ )^{⊗D}
    + O_{‖·‖₂}(D^{-1/2})`,

where `|Ψ_l⟩` and `|Ψ_{l,m}⟩` are the `Z_∅`-inserted states of eq. (B131) and the tensor
power is ordered as in (B133).

The tree Hilbert space and its tensor-power decomposition are not modelled in this file;
the parenthesised combination of (B132) is `branchCombination`, and the state, the
subtree states and the `∑_a f(a) |a_{p+1}⟩ ⊗ (·)^{⊗D}` assembly are the data of the
statement.
The approximation bound is not formalized: `state`, `assemble`, `subtree`, `subtree1` and
`subtree2` are arbitrary data in the former statement, so no uniform constant `C` can exist
(e.g. shift `state` by a fixed nonzero vector).  `branchCombination` is kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.FirstApproximation

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

/-- The parenthesised combination of eq. (B132): the subtree state dressed by the
`1 - ∑ γ²/(2D)` factor, the single-`Z`-inserted states with amplitudes `-i γ_l a_l/√D`,
and the double-inserted states with amplitudes `-γ_l γ_m a_l a_m/D`. -/
def branchCombination {H : Type*} [AddCommGroup H] [Module ℂ H] {p : ℕ} (γ : Fin p → ℝ)
    (D : ℕ) (a : Fin (p + 1) → Bool) (Ψprev : H) (Ψl : Fin p → H)
    (Ψlm : Fin p → Fin p → H) : H :=
  ((1 - (∑ l : Fin p, γ l ^ 2 / (2 * (D : ℝ))) : ℝ) : ℂ) • Ψprev
    + ∑ l : Fin p,
        ((-Complex.I * (γ l : ℂ) * (spinOf (a (Fin.castSucc l)) : ℂ)) /
          ((Real.sqrt D : ℝ) : ℂ)) • Ψl l
    + ∑ l : Fin p, ∑ m : Fin p,
        if l < m then
          ((-(γ l * γ m) * (spinOf (a (Fin.castSucc l)) * spinOf (a (Fin.castSucc m))) : ℝ) /
            ((D : ℝ) : ℂ) : ℂ) • Ψlm l m
        else 0


end Qatlib.Papers.SpinBosonQAOA26.MainResults.FirstApproximation
