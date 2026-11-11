/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5 — the QAOA state in the large-`D` limit: a second approximation

Fixed source: arXiv:2505.07929v2, Lemma 5, Appendix VI, PDF p. 41, eq. (B155).

With the notation of Lemma 4, the depth-`Δ` QAOA state on the degree-`D` tree also obeys

  `|Ψ^{(Δ,D)}⟩ = ∑_{a_{1:p+1}} f_{1:p}(a)
      exp(-½ ∑_{j,k} G^{(sym,Δ-1,D)}_{j,k} γ_j γ_k a_j a_k)
      |a_{p+1}⟩ ⊗ ( |Ψ^{(Δ-1,D)}⟩ + ∑_l (-i γ_l a_l/√D) |Ψ_l^{(Δ-1,D)}⟩ )^{⊗D}
    + O_{‖·‖₂}(D^{-1/2})`,

i.e. the dressing factor is the symmetric Gram matrix of the previous depth, and only the
single-insertion branch survives at order `D^{-1/2}`.
The approximation bound is not formalized: `state`, `assemble`, `Gsym`, `subtree` and
`subtree1` are arbitrary data in the former statement, so no uniform constant `C` can exist.
`branchCombination` and `dressingFactor` are kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.SecondApproximation

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

/-- The parenthesised combination of eq. (B155): the subtree state dressed by the
single-`Z`-inserted states with amplitudes `-i γ_l a_l/√D`. -/
def branchCombination {H : Type*} [AddCommGroup H] [Module ℂ H] {p : ℕ} (γ : Fin p → ℝ)
    (D : ℕ) (a : Fin (p + 1) → Bool) (Ψprev : H) (Ψl : Fin p → H) : H :=
  Ψprev + ∑ l : Fin p,
    ((-Complex.I * (γ l : ℂ) * (spinOf (a (Fin.castSucc l)) : ℂ)) /
      ((Real.sqrt D : ℝ) : ℂ)) • Ψl l

/-- The exponential dressing factor
`exp(-½ ∑_{j,k} G^{(sym,Δ-1,D)}_{j,k} γ_j γ_k a_j a_k)` of eq. (B155). -/
def dressingFactor {p : ℕ} (Gsym : Matrix (Fin p) (Fin p) ℂ) (γ : Fin p → ℝ)
    (a : Fin (p + 1) → Bool) : ℂ :=
  Complex.exp ((-(1 / 2) : ℂ) *
    ∑ j : Fin p, ∑ k : Fin p,
      Gsym j k * (γ j * γ k * spinOf (a (Fin.castSucc j)) * spinOf (a (Fin.castSucc k))))


end Qatlib.Papers.SpinBosonQAOA26.MainResults.SecondApproximation
