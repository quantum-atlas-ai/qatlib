/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceStates

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2 — spin path integral representation of the generalized QAOA state

Fixed source: arXiv:2505.07929v2, Proposition 2, Appendix V, PDF p. 33, eqs. (A39)–(A42).

The generalized QAOA state of eq. (A39),
`|Ψ⟩ = ∏←_{t=1}^{p} exp(-i β_t X) D(-i γ_t Z L_{:,t}) |0⟩_{C²} ⊗ |0⟩^{⊗p'}`,
admits the spin path-integral representation (A40)–(A41)

  `|Ψ⟩ = ∑_{a_{1:p+1} ∈ {±1}^{p+1}} f_{1:p+1}(a)
     exp(-(1/2) ∑_{r,s} i Im G^(sym)_{r,s} γ_r γ_s a_r a_s)
     |a_{p+1}⟩ ⊗ | -i ∑_t γ_t a_t L_{:,t} ⟩`,

with the one-sided `f` tensor of eq. (A42) and the coherent state
`| -i ∑_t γ_t a_t L_{:,t} ⟩ = D(-i ∑_t γ_t a_t L_{:,t}) |0⟩^{⊗p'}` (eq. (A25)).

In the two-component spin–boson encoding of `SourceStates`, the state is an element of
`SBState B = Fin 2 → B`; `spinKet` produces the `|a_{p+1}⟩ ⊗ b` summand.
Proposition 2 is not formalized here: it needs the layer-by-layer path expansion of the
generalized QAOA state.  `symPhase` and the imported state definitions are kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.QaoaPathIntegral

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- The phase `exp(-½ i ∑_{r,s} Im G^(sym)_{r,s} γ_r γ_s a_r a_s)` of eqs. (A40), (A41):
the phase of Lemma 1 (eq. (A24)) evaluated on the spin values `a`. -/
def symPhase {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (γ a : Fin p → ℝ) : ℂ :=
  Complex.exp ((-(1 / 2) : ℂ) * Complex.I *
    ((∑ r : Fin p, ∑ s : Fin p,
      (gramSym p' p L r s).im * (γ r * γ s * a r * a s)) : ℝ))


end Qatlib.Papers.SpinBosonQAOA26.MainResults.QaoaPathIntegral
