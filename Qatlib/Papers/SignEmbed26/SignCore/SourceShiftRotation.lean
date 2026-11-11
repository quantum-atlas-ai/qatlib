/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Qatlib.Papers.SignEmbed26.SignCore.SourceSignEmbedding

set_option backward.isDefEq.respectTransparency false

/-!
# Shift-rotation invariance of the Sylvester sign embedding

Source: Y. Wang and J.-P. Liu, *Sign Embedding Quantum Algorithms for Matrix Equations and
Matrix Functions*, arXiv:2604.25333v2, Lemma 3.4 (Section 3.3).

For `|η| = 1`, `ω ∈ ℂ` and `λ > 0`, the source sets

`A' = λη(A - ωI)`, `B' = λη(B + ωI)`, `C' = ληC`

and proves that `X` solves `A X + X B = C` if and only if it solves `A' X + X B' = C'`, that the
augmented matrices satisfy `M' = λη(M - ωI)`, and that consequently the `(1,2)` block of
`sign(M')` is again `2X` whenever `sign(M')` is defined.

The file formalizes the two algebraic claims over an arbitrary field, for a nonzero scalar
`λη`: the equation transform (both directions) and the block identity `M' = λη(M - ωI)`.  The
last sentence is recorded as a corollary: `!![I, 2X; 0, -I]` is again an involution commuting with
the transformed augmented matrix, so it plays the role of `sign(M')`.
-/

namespace Qatlib.Papers.SignEmbed26.SignCore

open Matrix

set_option autoImplicit false

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lemma 3.4, equation transform.**  For a nonzero scalar product `λη`, the shifted and
rescaled matrices satisfy the same Sylvester equation as `A`, `B`, `C`: `X` solves
`λη(A - ωI) X + X (λη(B + ωI)) = λη C` exactly when `A X + X B = C`.  The two added terms `-ωX`
and `Xω` cancel, and the common nonzero factor `λη` may be cancelled. -/
theorem shiftRotation_sylvester_iff (A B C X : Matrix n n 𝕜) {lam eta om : 𝕜}
    (hlameta : lam * eta ≠ 0) :
    (lam * eta) • (A - om • 1) * X + X * ((lam * eta) • (B + om • 1)) = (lam * eta) • C ↔
      A * X + X * B = C := by
  have expand :
      (lam * eta) • (A - om • 1) * X + X * ((lam * eta) • (B + om • 1)) - (lam * eta) • C =
        (lam * eta) • (A * X + X * B - C) := by
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, smul_add, smul_sub]
    abel
  have cancel : ∀ Z : Matrix n n 𝕜, (lam * eta) • Z = 0 ↔ Z = 0 := by
    intro Z
    rw [smul_eq_zero]
    exact ⟨fun h => h.resolve_left hlameta, fun h => Or.inr h⟩
  constructor
  · intro h
    have h0 : (lam * eta) • (A * X + X * B - C) = 0 := by rw [← expand, h, sub_self]
    have := (cancel _).mp h0
    rwa [sub_eq_zero] at this
  · intro h
    have h0 : A * X + X * B - C = 0 := by rw [h, sub_self]
    rw [← sub_eq_zero, expand, h0, smul_zero]

omit [Fintype n] in
/-- **Lemma 3.4, augmented block identity.**  With `A' = λη(A - ωI)`, `B' = λη(B + ωI)` and
`C' = ληC`, the augmented matrices satisfy `M' = λη(M - ωI)`. -/
theorem shiftRotation_augmented (A B C : Matrix n n 𝕜) (lam eta om : 𝕜) :
    augmented ((lam * eta) • (A - om • 1)) ((lam * eta) • C) ((lam * eta) • (B + om • 1)) =
      (lam * eta) • (augmented A C B - om • 1) := by
  have hone : (1 : Matrix (n ⊕ n) (n ⊕ n) 𝕜) = fromBlocks (1 : Matrix n n 𝕜) 0 0 1 :=
    fromBlocks_one.symm
  rw [hone]
  ext (i | i) (j | j) <;>
    simp only [augmented, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply]
  all_goals (try split_ifs) <;> ring

/-- **Lemma 3.4, the `(1,2)` block survives the shift-rotation.**  If `X` solves the original
Sylvester equation then `!![I, 2X; 0, -I]` is again an involution commuting with the transformed
augmented matrix `M' = λη(M - ωI)`; by Theorem 3.3 the `(1,2)` block of `sign(M')` is therefore
`2X`.  The identification of `!![I, 2X; 0, -I]` with `sign(M')` itself is the holomorphic
functional calculus step, as in `SourceSignEmbedding`. -/
theorem shiftRotation_signEmbedding (A B C X : Matrix n n 𝕜) {lam eta om : 𝕜}
    (hlameta : lam * eta ≠ 0) (h2 : (2 : 𝕜) ≠ 0) (hX : A * X + X * B = C) :
    signEmbedding X * signEmbedding X = 1 ∧
      signEmbedding X * augmented ((lam * eta) • (A - om • 1)) ((lam * eta) • C)
          ((lam * eta) • (B + om • 1)) =
        augmented ((lam * eta) • (A - om • 1)) ((lam * eta) • C) ((lam * eta) • (B + om • 1)) *
          signEmbedding X := by
  refine ⟨signEmbedding_mul_self X, (signEmbedding_commute_iff _ _ _ _ h2).mpr ?_⟩
  exact (shiftRotation_sylvester_iff A B C X hlameta).mpr hX

end Qatlib.Papers.SignEmbed26.SignCore
