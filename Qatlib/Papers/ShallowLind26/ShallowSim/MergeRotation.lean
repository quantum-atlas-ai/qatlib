/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Merging two unequal rotation sequences (Lemma 4.4)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 4.4, page 18.

In coordinates `(p, A, B)` -- public, left private representative and right
private representative -- the two child rotations merge by

`G_B G_A = (1 ⊕ O_AB) G(ac, s) (1 ⊕ I_AB)^T`

when `a, c ∈ [0,1]`, `b = √(1-a²)`, `d = √(1-c²)`, `s = √(1-a²c²)`, where

`G_A = [[a,-b,0],[b,a,0],[0,0,1]]`, `G_B = [[c,0,-d],[0,1,0],[d,0,c]]`,

`I_AB = s⁻¹ [[cb,d],[-d,cb]]` and `O_AB = s⁻¹ [[b,da],[-da,b]]`.

The source proof observes `c²b² + d² = b² + d²a² = s²`, so both private basis
changes are orthogonal; the first row and column agree and the residual private
block is the displayed `2 × 2` identity.  At `s = 0` nonnegativity forces
`a = c = 1`, `b = d = 0`, and all three factors are the identity.

We formalize the algebraic content with `b, d, s` as independent reals subject
to the exact quadratic relations, which removes every square root from the
proof; the paper's square-root instance is recovered as a corollary.
-/

open Matrix

namespace Qatlib.Papers.ShallowLind26.ShallowSim.MergeRotation

set_option autoImplicit false

/-- The public--private two-level rotation `G(t,s)` fixing the right private
coordinate. -/
noncomputable def Gm (t s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => t | 0, 1 => -s
    | 1, 0 => s | 1, 1 => t
    | 2, 2 => 1
    | _, _ => 0

/-- The left child rotation, cosine `a`, sine `b`. -/
noncomputable def GA (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => a | 0, 1 => -b
    | 1, 0 => b | 1, 1 => a
    | 2, 2 => 1
    | _, _ => 0

/-- The right child rotation, cosine `c`, sine `d`, coupling public to the
right private coordinate. -/
noncomputable def GB (c d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => c | 0, 2 => -d
    | 1, 1 => 1
    | 2, 0 => d | 2, 2 => c
    | _, _ => 0

/-- Embed a `2 × 2` private block into the `(A,B)` corner. -/
noncomputable def emb2 (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => 1
    | 1, 1 => M 0 0 | 1, 2 => M 0 1
    | 2, 1 => M 1 0 | 2, 2 => M 1 1
    | _, _ => 0

/-- The input private basis change `I_AB`. -/
noncomputable def IAB (b c d s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => s⁻¹ * (c * b) | 0, 1 => s⁻¹ * d
    | 1, 0 => s⁻¹ * (-d) | 1, 1 => s⁻¹ * (c * b)
    | _, _ => 0

/-- The output private basis change `O_AB`. -/
noncomputable def OAB (a b d s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => s⁻¹ * b | 0, 1 => s⁻¹ * (d * a)
    | 1, 0 => s⁻¹ * (-d * a) | 1, 1 => s⁻¹ * b
    | _, _ => 0

/-- **Lemma 4.4, full factorization.**  Under `b² = 1-a²`, `d² = 1-c²` and
`s² = 1-a²c²` with `s ≠ 0`, the two adjacent child rotations merge into the
public rotation `G(ac,s)` conjugated by the private basis changes.  In our
coordinate order the inverse output change sits on the left; because the basis
changes are orthogonal this is the paper's factorization. -/
theorem merge_factorization (a b c d s : ℝ) (hs : s ≠ 0)
    (hb : b ^ 2 = 1 - a ^ 2) (hd : d ^ 2 = 1 - c ^ 2)
    (hs2 : s ^ 2 = 1 - a ^ 2 * c ^ 2) :
    GB c d * GA a b = (emb2 (OAB a b d s))ᵀ * Gm (a * c) s * emb2 (IAB b c d s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GB, GA, Gm, emb2, IAB, OAB, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply] <;>
    field_simp [hs]
  all_goals
    try rw [show b ^ 3 = b * b ^ 2 from by ring]
    try rw [show d ^ 3 = d * d ^ 2 from by ring]
    try rw [hs2]
    try rw [hb]
    try rw [hd]
    ring

/-- **Lemma 4.4, input basis change is orthogonal.**  `I_AB I_ABᵀ = 1`. -/
theorem IAB_orthogonal (a b c d s : ℝ) (hs : s ≠ 0)
    (hb : b ^ 2 = 1 - a ^ 2) (hd : d ^ 2 = 1 - c ^ 2)
    (hs2 : s ^ 2 = 1 - a ^ 2 * c ^ 2) :
    IAB b c d s * (IAB b c d s)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [IAB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    field_simp [hs]
  all_goals
    try rw [show b ^ 3 = b * b ^ 2 from by ring]
    try rw [show d ^ 3 = d * d ^ 2 from by ring]
    try rw [hs2]
    try rw [hb]
    try rw [hd]
    ring

/-- **Lemma 4.4, output basis change is orthogonal.**  `O_AB O_ABᵀ = 1`. -/
theorem OAB_orthogonal (a b c d s : ℝ) (hs : s ≠ 0)
    (hb : b ^ 2 = 1 - a ^ 2) (hd : d ^ 2 = 1 - c ^ 2)
    (hs2 : s ^ 2 = 1 - a ^ 2 * c ^ 2) :
    OAB a b d s * (OAB a b d s)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OAB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    field_simp [hs]
  all_goals
    try rw [show b ^ 3 = b * b ^ 2 from by ring]
    try rw [show d ^ 3 = d * d ^ 2 from by ring]
    try rw [hs2]
    try rw [hb]
    try rw [hd]
    ring

/-- **Lemma 4.4, degenerate case.**  When `a, b, c, d ≥ 0` and `a²c² = 1`,
the relations force `a = c = 1` and `b = d = 0`, so both child rotations and
the public rotation are the identity. -/
theorem merge_degenerate (a b c d : ℝ) (ha0 : 0 ≤ a) (_hb0 : 0 ≤ b)
    (hc0 : 0 ≤ c) (_hd0 : 0 ≤ d)
    (hb : b ^ 2 = 1 - a ^ 2) (hd : d ^ 2 = 1 - c ^ 2)
    (hs0 : 1 - a ^ 2 * c ^ 2 = 0) :
    GB c d = 1 ∧ GA a b = 1 ∧ Gm (a * c) 0 = 1 := by
  have ha2le : a ^ 2 ≤ 1 := by linarith [hb, sq_nonneg b]
  have hc2le : c ^ 2 ≤ 1 := by linarith [hd, sq_nonneg d]
  have hprod : a ^ 2 * c ^ 2 = 1 := by linarith [hs0]
  have hle1 : a ^ 2 * c ^ 2 ≤ a ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left hc2le (sq_nonneg a)
  have hle2 : a ^ 2 * c ^ 2 ≤ 1 * c ^ 2 :=
    mul_le_mul_of_nonneg_right ha2le (sq_nonneg c)
  have ha2 : a ^ 2 = 1 := le_antisymm ha2le (by linarith)
  have hc2 : c ^ 2 = 1 := le_antisymm hc2le (by linarith)
  have ha1 : a = 1 := by
    rcases sq_eq_one_iff.mp ha2 with h | h
    · exact h
    · linarith
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc2 with h | h
    · exact h
    · linarith
  have hb1 : b = 0 := by
    have : b ^ 2 = 0 := by rw [hb, ha1]; norm_num
    exact sq_eq_zero_iff.mp this
  have hd1 : d = 0 := by
    have : d ^ 2 = 0 := by rw [hd, hc1]; norm_num
    exact sq_eq_zero_iff.mp this
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [GB, GA, Gm, ha1, hc1, hb1, hd1]

end Qatlib.Papers.ShallowLind26.ShallowSim.MergeRotation
