/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.FourierData

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Theorem 3 (XQUATH is false at low depth)

Fixed arXiv:2211.03999v1, Theorem 3, p.23, Eqs. (54)--(56).

The paper exhibits the algorithm `q(C,0^n) := 2^{-n} + f(C,\tilde s_*,0^n)` with
`\tilde s_* = 2^{-n/2} Z_1 ⊗ I^{⊗(n-1)}`, so that

  `XQ = 2^{2n} E_C[ (p(C,0^n) - 2^{-n})^2 - (p(C,0^n) - q(C,0^n))^2 ]`
     `= 2^{2n} E_C[ f(C,\tilde s_*,0^n)^2 ] = (1/15)^d`,

using the Pauli-path expansion, orthogonality (Lemma 3), and the single-path Haar value.
The Lean statement isolates the algebraic identity: the orthogonality cancellation is
proved here, while the Haar value of the distinguished path is the standard computation of
Lemma 1 (15 choices per two-qubit gate) supplied as `hstar`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.XEB

open BigOperators
open scoped BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

variable {Ω Path : Type*}

/-- Fixed arXiv:2211.03999v1, Theorem 3, p.23, Eqs. (54)--(56):
given the two Pauli-path expansions of the algorithm's output deviations and the
Haar value of the distinguished path, the cross-entropy benchmark satisfies
`XQ = (1/15)^d`. -/
theorem source_theorem3_xquath_refutation [Fintype Path] [DecidableEq Path]
    (n d : ℕ) (E : Expectation Ω) (f : Ω → Path → ℝ)
    (p q : Ω → ℝ) (sStar : Path) (XQ : ℝ)
    (horth : Orthogonality E f)
    (hp : ∀ C, p C - ((2 : ℝ) ^ n)⁻¹ = ∑ s, f C s)
    (hq : ∀ C, p C - q C = ∑ s ∈ Finset.univ.erase sStar, f C s)
    (hXQ : XQ = (2 : ℝ) ^ (2 * n) *
      (E (fun C => (p C - ((2 : ℝ) ^ n)⁻¹) ^ 2) -
        E (fun C => (p C - q C) ^ 2)))
    (hstar : (2 : ℝ) ^ (2 * n) * E (fun C => (f C sStar) ^ 2) = (1 / 15) ^ d) :
    XQ = (1 / 15) ^ d := by
  rw [hXQ]
  simp_rw [hp, hq]
  rw [second_moment_diff E f horth sStar]
  exact hstar

end Qatlib.Papers.NoisyCircuit22.MainResults.XEB
