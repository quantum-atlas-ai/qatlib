/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The scaled minimal witness has norm one

Ito--Jeffery, *Approximate Span Programs*, arXiv:1507.00432v1, Theorem 2.14 and
Appendix A, Lemma A.1.

The paper rescales a normalised span program by `β`, with `N = ‖|w₀⟩‖² = N₊(P)` the
squared norm of the minimal positive witness, and records three changes in the witness
sizes: `w₊(x, P^β) = β⁻² w₊(x, P) + β² / (β² + N)`, `N₊(P^β) = β² / (β² + N)` and
`w₋(x, P^β) = β² w₋(x, P) + 1`.  The minimal witness `|w₀^β⟩` of `P^β` then has norm
one; written out in the orthonormal triple `(|0̂⟩, |1̂⟩, w₀)` whose third component `w₀`
satisfies `‖w₀‖² = N`, that is the scalar identity
`(β / (β² + N))² N + (N / (β² + N))² + (β / √(β² + N))² = 1` proved below.

The identity is the arithmetic core of Lemma A.1.  The operator-level statement — that
`|w₀^β⟩` is the minimal positive witness of the scaled program, and therefore that the
scaling achieves `N₊ = 1` — is not part of this module: it needs the witness-size
formulae above, which the paper layer records only through the `sInf` definitions
`Qatlib.Papers.ApproxSpan15.MainResults.SpanProgram.wPlus` and `Nplus`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ApproxSpan15.MainResults

/-- **arXiv:1507.00432v1, Theorem 2.14 and Lemma A.1.**  For a scaling
parameter `β > 0` and a squared minimal-witness norm `N ≥ 0`, the vector with components
`β / (β² + N)` on `|0̂⟩`, `N / (β² + N)` on `|1̂⟩` and `β / √(β² + N)` on the direction of
`w₀` has squared norm one.  This is the arithmetic content of the claim that the scaled
minimal witness `|w₀^β⟩` is a unit vector. -/
theorem scaledMinimalWitness_normSq (N β : ℝ) (hN : 0 ≤ N) (hβ : 0 < β) :
    (β / (β ^ 2 + N)) ^ 2 * N + (N / (β ^ 2 + N)) ^ 2 +
      (β / Real.sqrt (β ^ 2 + N)) ^ 2 = 1 := by
  have hs : (0 : ℝ) < β ^ 2 + N := by positivity
  have hsq : Real.sqrt (β ^ 2 + N) ^ 2 = β ^ 2 + N := Real.sq_sqrt hs.le
  rw [div_pow, div_pow, div_pow, hsq]
  have hne : β ^ 2 + N ≠ 0 := ne_of_gt hs
  field_simp
  ring

end Qatlib.Papers.ApproxSpan15.MainResults
