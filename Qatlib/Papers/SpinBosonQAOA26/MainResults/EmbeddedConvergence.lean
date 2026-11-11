/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceDefinitions
import Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions.SourceStates
import Qatlib.Papers.SpinBosonQAOA26.MainResults.SymmetricBasisExpansion

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4 — convergence of the embedded symmetric-basis expansion

Fixed source: arXiv:2505.07929v2, Proposition 4, Appendix VI, PDF pp. 43–44,
eqs. (B208)–(B210).

Embedding the symmetric-basis expansion of Lemma 6 into the full Hilbert space and summing
over the occupation vectors, the depth-`Δ` state of the degree-`D` tree converges in norm as
`D → ∞` to the state `Φ_Δ` of eqs. (B208)–(B210),

  `Φ_Δ = ∑_{a_{p+1}} ∑_{(n_l)} f_{1:p}(a) exp(-½ ∑_{j,k} G^{(sym,Δ-1)}_{j,k} γ_j γ_k a_j a_k)
      (∏_l (1/√(n_l!)) c_l^{n_l}) |a_{p+1}⟩ ⊗ |n_1, …, n_p⟩`,

with `c_l = -i ∑_j L_{l,j} γ_j a_j` (eq. (B208)) — the coefficients being exactly the
`D → ∞` limits of Lemma 6, and the sums absolutley convergent (eq. (B210)).

The number states `|n_1, …, n_p⟩` are not modelled in this paper layer; they enter the
statement as a parameter `numberState : (Fin p' → ℕ) → B` of the cavity Hilbert space, in the
spirit of the abstract `WeylFock` interface.
The convergence conclusion is not formalized: `PhiTilde` is an arbitrary sequence of
states in the former statement, so neither convergence nor the stated `HasSum`
identification follows without the tree construction (a constant or divergent sequence is a
counterexample).  `limitCoefficient` is kept.

-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.EmbeddedConvergence

open Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions
open Qatlib.Papers.SpinBosonQAOA26.MainResults.SymmetricBasisExpansion

/-- The `D → ∞` limit coefficient of the number state `|n_1, …, n_{p'}⟩` in the embedded
expansion, eq. (B208): summing Lemma 6's limit `∏_l (1/√(n_l!)) c_l^{n_l}` over the spins
`a_{1:p}` of the cavity, weighted by the one-sided `f` tensor and the exponential dressing
factor `exp(-½ ∑_{j,k} G^{(sym,Δ-1)}_{j,k} γ_j γ_k a_j a_k)`. -/
def limitCoefficient {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (γ : Fin p → ℝ)
    (f : (Fin (p + 1) → Bool) → ℂ) (Gsym : Matrix (Fin p) (Fin p) ℂ)
    (a : Bool) (n : Fin p' → ℕ) : ℂ :=
  ∑ a1p : Fin p → Bool,
    f (@Fin.snoc p (fun _ => Bool) a1p a) *
      Complex.exp ((-(1 / 2) : ℂ) *
        ∑ j : Fin p, ∑ k : Fin p,
          Gsym j k * (γ j * γ k * spinOf (a1p j) * spinOf (a1p k))) *
      ∏ l : Fin p',
        (((Real.sqrt ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
          (modeAmplitude L γ (fun j => spinOf (a1p j)) l) ^ (n l)


end Qatlib.Papers.SpinBosonQAOA26.MainResults.EmbeddedConvergence
