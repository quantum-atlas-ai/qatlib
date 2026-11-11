/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.FourierData

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Theorem 5 (classical XEB)

Fixed arXiv:2211.03999v1, Theorem 5, p.25, Eqs. (61)--(63).

The classical sampler `q(C,x) = 2^{-n} + f(C,\tilde s_*,x)` (which only touches the first
qubit) satisfies `XEB = (1/15)^d`.  The proof expands `p` in the Pauli basis,
`p(C,x) = ∑_s f(C,s,x)`, applies orthogonality (Lemma 3) to keep only `s = \tilde s_*`, and
uses Eq. (14) to replace `f(C,s,x)^2` by `f(C,s,0^n)^2`.  The Lean statement proves the
orthogonality and `x`-summation steps; the Haar value of the distinguished path is supplied
as `hstar`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.XEB

open BigOperators
open scoped BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

variable {Ω Path : Type*}

/-- Fixed arXiv:2211.03999v1, Theorem 5, p.25, Eq. (62):
the classical XEB value equals the single-path Haar weight `(1/15)^d`. -/
theorem source_theorem5_classical_xeb [Fintype Path] [DecidableEq Path]
    (n d : ℕ) (E : Expectation Ω) (f : Ω → Path → ℝ)
    (p : Ω → (Fin n → Bool) → ℝ) (sStar : Path) (XEB : ℝ)
    (horth : Orthogonality E f)
    (hp : ∀ C x, p C x = ∑ s, f C s)
    (hXEB : XEB = (2 : ℝ) ^ n * ∑ x : Fin n → Bool,
      E (fun C => p C x * f C sStar))
    (hstar : (2 : ℝ) ^ (2 * n) * E (fun C => (f C sStar) ^ 2) = (1 / 15) ^ d) :
    XEB = (1 / 15) ^ d := by
  rw [hXEB]
  have hx : ∀ x : Fin n → Bool, E (fun C => p C x * f C sStar) =
      E (fun C => (f C sStar) ^ 2) := by
    intro x
    have hfun : (fun C => p C x * f C sStar) =
        (fun C => (∑ s, f C s) * f C sStar) := by
      funext C
      rw [hp C x]
    rw [hfun]
    have hexp : (fun C => (∑ s, f C s) * f C sStar) =
        ∑ s, fun C => f C s * f C sStar := by
      funext C
      rw [Finset.sum_mul]
      simp only [Finset.sum_apply]
    rw [hexp, map_sum]
    rw [Finset.sum_eq_single sStar]
    · simp [pow_two]
    · intro s _ hne
      exact horth s sStar hne
    · intro hnot
      simp at hnot
  simp_rw [hx, Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [hcard]
  simp only [nsmul_eq_mul]
  push_cast
  have hpow : (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show 2 * n = n + n by ring, pow_add]
  rw [← mul_assoc, ← hpow]
  exact hstar

end Qatlib.Papers.NoisyCircuit22.MainResults.XEB
