/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Weights-in-states perceptron construction

Fixed source: arXiv:1512.02900v1, Appendix A, pp.29-34, eqs. (14), (17)-(18)
and Figure 17.

We model the real training system and the computational-basis classifier. The
Toffoli bank preserves both control registers and XORs each weight/feature
conjunction into its own ancilla. It is involutive and hence reversible, and
starting with zero ancillas gives the paper's OR classification rule. For binary
weights and zero bias this rule agrees with a positive real perceptron score.
These are computational-basis semantics, not an implementation of the HHL
training operator or a gate-complexity theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMLAdvances15.MainResults

/-- A real feature or weight vector with `W` coordinates. -/
abbrev RealVec (W : ℕ) := Fin W → ℝ

/-- A computational-basis register with `W` bits. -/
abbrev BitVec (W : ℕ) := Fin W → Bool

/-- The real value of a computational-basis bit. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

/-- Embed a computational-basis register into a real vector. -/
def realOfBits {W : ℕ} (x : BitVec W) : RealVec W := fun j => bitValue (x j)

/-- The perceptron score in eq. (14). -/
def perceptronScore {W : ℕ} (x w : RealVec W) (b : ℝ) : ℝ :=
  ∑ j, x j * w j + b

/-- The matrix whose row `t` is the training vector `X t` in eq. (18). -/
def trainingMatrix {N W : ℕ} (X : Fin N → RealVec W) : Matrix (Fin N) (Fin W) ℝ :=
  Matrix.of X

/-- Eq. (18), `Aw = y-b`, is equivalent to the rowwise training equations (17),
`xₜ·w + bₜ = yₜ`. No invertibility or training-data consistency is assumed. -/
theorem trainingEquation_iff_rows {N W : ℕ} (X : Fin N → RealVec W)
    (w : RealVec W) (y b : Fin N → ℝ) :
    (trainingMatrix X).mulVec w = y - b ↔
      ∀ t, perceptronScore (X t) w (b t) = y t := by
  constructor
  · intro h t
    have ht := congr_fun h t
    simp [trainingMatrix, Matrix.mulVec, dotProduct, perceptronScore] at ht ⊢
    linarith
  · intro h
    funext t
    have ht := h t
    simp [trainingMatrix, Matrix.mulVec, dotProduct, perceptronScore] at ht ⊢
    linarith

/-- The reversible computational-basis Toffoli bank from Figure 17. Each target
ancilla receives the XOR of its old value with one weight/feature conjunction. -/
def basisClassify {W : ℕ} (x w a : BitVec W) : BitVec W × BitVec W × BitVec W :=
  (x, w, fun j => a j ^^ (x j && w j))

/-- The Toffoli bank is its own inverse, so it does not destroy the input,
weights or ancillas and is reversible on every computational-basis state. -/
theorem basisClassify_involutive {W : ℕ} :
    Function.Involutive (fun p : BitVec W × BitVec W × BitVec W =>
      basisClassify p.1 p.2.1 p.2.2) := by
  rintro ⟨x, w, a⟩
  simp only [basisClassify]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext j
      cases hx : x j <;> cases hw : w j <;> cases ha : a j <;>
        simp [hx, hw, ha]

/-- The weight register is unchanged by the classification Toffoli bank. -/
theorem basisClassify_preserves_weights {W : ℕ} (x w a : BitVec W) :
    (basisClassify x w a).2.1 = w := rfl

/-- The feature register is also unchanged by classification. -/
theorem basisClassify_preserves_inputs {W : ℕ} (x w a : BitVec W) :
    (basisClassify x w a).1 = x := rfl

/-- Starting with zero ancillas leaves exactly the conjunction bits `xⱼ ∧ wⱼ`. -/
theorem basisClassify_zero_ancilla {W : ℕ} (x w : BitVec W) :
    (basisClassify x w (fun _ => false)).2.2 = fun j => x j && w j := by
  funext j
  simp [basisClassify]

/-- The classical readout is true exactly when at least one conjunction bit is
set, as in the Figure 17 classification rule. -/
def basisVote {W : ℕ} (x w : BitVec W) : Bool :=
  decide (∃ j, x j = true ∧ w j = true)

/-- The OR of the conjunction bits is true iff some feature and weight are both
one. -/
theorem basisVote_eq_true_iff {W : ℕ} (x w : BitVec W) :
    basisVote x w = true ↔ ∃ j, x j = true ∧ w j = true := by
  simp [basisVote]

/-- The conjunction score is always nonnegative for computational-basis data. -/
theorem binary_score_nonneg {W : ℕ} (x w : BitVec W) :
    0 ≤ perceptronScore (realOfBits x) (realOfBits w) 0 := by
  simp only [perceptronScore, add_zero]
  apply Finset.sum_nonneg
  intro j _hj
  simp [realOfBits, bitValue]
  split_ifs <;> norm_num

/-- The binary dot product vanishes exactly when no conjunction bit is set. -/
theorem binary_score_eq_zero_iff_no_product {W : ℕ} (x w : BitVec W) :
    perceptronScore (realOfBits x) (realOfBits w) 0 = 0 ↔
      ∀ j, ¬ (x j = true ∧ w j = true) := by
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin W)),
      0 ≤ realOfBits x j * realOfBits w j := by
    intro j _hj
    simp [realOfBits, bitValue]
    split_ifs <;> norm_num
  simp only [perceptronScore, add_zero]
  rw [Finset.sum_eq_zero_iff_of_nonneg hnonneg]
  simp only [Finset.mem_univ, true_implies]
  apply forall_congr'
  intro j
  cases hx : x j <;> cases hw : w j <;> simp [hx, hw, realOfBits, bitValue]

/-- The zero-bias real score is positive iff the computational-basis OR vote is
true, identifying eq. (14) with Figure 17 for binary features and weights. -/
theorem binary_score_pos_iff_vote {W : ℕ} (x w : BitVec W) :
    0 < perceptronScore (realOfBits x) (realOfBits w) 0 ↔
      basisVote x w = true := by
  have hzero : perceptronScore (realOfBits x) (realOfBits w) 0 = 0 ↔
      basisVote x w = false := by
    rw [binary_score_eq_zero_iff_no_product]
    simp [basisVote]
  by_cases hz : perceptronScore (realOfBits x) (realOfBits w) 0 = 0
  · have hv := hzero.mp hz
    simp [hz, hv]
  · have hp := lt_of_le_of_ne (binary_score_nonneg x w) (Ne.symm hz)
    have hv : basisVote x w = true := by
      cases hb : basisVote x w
      · exact False.elim (hz (hzero.mpr hb))
      · rfl
    simp [hp, hv]

/-- The OR of the ancillas after a zero-initialized Toffoli bank is the required
classification vote. -/
def ancillaVote {W : ℕ} (a : BitVec W) : Bool :=
  decide (∃ j, a j = true)

/-- Zero-initialized classification followed by the ancilla OR implements the
paper's binary perceptron decision without changing the weight register. -/
theorem basisClassify_zero_vote {W : ℕ} (x w : BitVec W) :
    ancillaVote ((basisClassify x w (fun _ => false)).2.2) = basisVote x w := by
  simp [ancillaVote, basisVote, basisClassify]

/-- The positive-score condition is equivalent to an ancilla being measured as
one after the zero-initialized reversible classification. -/
theorem binary_score_pos_iff_ancilla_vote {W : ℕ} (x w : BitVec W) :
    0 < perceptronScore (realOfBits x) (realOfBits w) 0 ↔
      ancillaVote ((basisClassify x w (fun _ => false)).2.2) = true := by
  rw [basisClassify_zero_vote]
  exact binary_score_pos_iff_vote x w

end Qatlib.Papers.QMLAdvances15.MainResults
