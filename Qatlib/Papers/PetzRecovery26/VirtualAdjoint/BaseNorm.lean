/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PetzRecovery26.VirtualAdjoint.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Base norm equals diamond norm for 1-slot virtual combs (Lemma 2)

Fixed source version: arXiv:2602.05828v1 (first submitted 2026-02-05),
Lemma 2 (p. 4) and its proof in Appendix A, Eqs. (A1)--(A3) (pp. 9--10).

Lemma 2 states that for any `n`-slot virtual comb `C̃`, the base norm
`‖C̃‖_♦` equals the diamond norm `‖C̃‖_♢`.  Appendix A proves this by exhibiting
an affine bijection between the feasible sets of the two SDPs (A2) and (A3):

  `(α⁺, α⁻, C⁺, C⁻) = ((p+1)/2, (p−1)/2, (S+C̃)/2, (S−C̃)/2)`.

This file formalises the `n = 1` instance, where the comb-symmetry
constraints of (A2)/(A3) (the conditions indexed by
`k ∈ {1, …, n−1}`) are vacuous.  The two norms are defined as the infima of
the explicit value sets of the paper's SDPs, and the paper's affine
transformation is used to show that those value sets are *equal*, which is
strictly stronger than the equality of the optimal values.

* `baseNormValues C d` is the base-norm value set of (A3): the weights
  `Tr(C⁺)/d + Tr(C⁻)/d` over PSD decompositions `C = C⁺ − C⁻`.
* `diamondNormValues C d` is the diamond-norm dual value set of (A2): the
  weights `Tr(S)/d` over `S ⪰ 0` with `−S ⪯ C ⪯ S`.
* `baseNormValues_eq_diamondNormValues` proves the two sets coincide;
  `lemma2_baseNorm_eq_diamondNorm` concludes `‖C‖_♦ = ‖C‖_♢`.

The general `n`-slot statement with the non-trivial comb-symmetry constraints
is not formalised here; for `n = 1` the constraints are vacuous, so this file
covers the exact instance needed by Theorems 3 and 4 of the paper.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.PetzRecovery26.VirtualAdjoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The base-norm value set (Eq. (A3)) -/

/-- The base-norm value set of Eq. (A3) for a 1-slot Choi operator `C` with
normalisation `d`: the weights `Tr(C⁺)/d + Tr(C⁻)/d` over positive
semidefinite decompositions `C = C⁺ − C⁻`.  For `n = 1` the comb-symmetry
constraints `F C^± = O F C^±` of (A3) are vacuous. -/
def baseNormValues (C : Matrix ι ι ℂ) (d : ℝ) : Set ℝ :=
  {v | ∃ C₁ C₂ : Matrix ι ι ℂ,
        C₁.PosSemidef ∧ C₂.PosSemidef ∧ C = C₁ - C₂ ∧
        v = (C₁.trace).re / d + (C₂.trace).re / d}

/-- The base norm `‖C‖_♦` of a 1-slot virtual comb: the infimum of the
base-norm value set of Eq. (A3). -/
def baseNorm (C : Matrix ι ι ℂ) (d : ℝ) : ℝ := sInf (baseNormValues C d)

/-! ## The diamond-norm dual value set (Eq. (A2)) -/

/-- The diamond-norm dual value set of Eq. (A2) for a 1-slot Choi operator
`C` with normalisation `d`: the weights `Tr(S)/d` over positive semidefinite
`S` with `−S ⪯ C ⪯ S`.  The conditions `−S ⪯ C ⪯ S` are written in terms of
positive semidefiniteness of `S ± C`. -/
def diamondNormValues (C : Matrix ι ι ℂ) (d : ℝ) : Set ℝ :=
  {v | ∃ S : Matrix ι ι ℂ,
        S.PosSemidef ∧ (S + C).PosSemidef ∧ (S - C).PosSemidef ∧
        v = (S.trace).re / d}

/-- The diamond norm `‖C‖_♢` of a 1-slot virtual comb: the infimum of the
diamond-norm dual value set of Eq. (A2). -/
def diamondNorm (C : Matrix ι ι ℂ) (d : ℝ) : ℝ := sInf (diamondNormValues C d)

/-! ## The affine transformation of Appendix A -/

omit [Fintype ι] [DecidableEq ι] in
/-- `(1/2)(X + Y) − (1/2)(X − Y) = Y`. -/
theorem half_smul_sub {X Y : Matrix ι ι ℂ} :
    ((1 / 2 : ℝ) • (X + Y)) - ((1 / 2 : ℝ) • (X - Y)) = Y := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `(1/2)(X + Y) + (1/2)(X − Y) = X`. -/
theorem half_smul_add {X Y : Matrix ι ι ℂ} :
    ((1 / 2 : ℝ) • (X + Y)) + ((1 / 2 : ℝ) • (X - Y)) = X := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  push_cast
  ring

/-- **Lemma 2, Appendix A, Eqs. (A2)--(A3).**  The base-norm value set of (A3)
and the diamond-norm dual value set of (A2) coincide for any 1-slot Choi
operator: the paper's affine transformation
`(α⁺, α⁻, C⁺, C⁻) = ((p+1)/2, (p−1)/2, (S+C̃)/2, (S−C̃)/2)` is a bijection
between feasible points, and both objectives evaluate to the same real number
(`Tr(S)/d = Tr(C⁺)/d + Tr(C⁻)/d`). -/
theorem baseNormValues_eq_diamondNormValues (C : Matrix ι ι ℂ) (d : ℝ) :
    baseNormValues C d = diamondNormValues C d := by
  ext v
  constructor
  · rintro ⟨C₁, C₂, h₁, h₂, hC, rfl⟩
    have hSC : (C₁ + C₂) + C = C₁ + C₁ := by rw [hC]; abel
    have hSC' : (C₁ + C₂) - C = C₂ + C₂ := by rw [hC]; abel
    refine ⟨C₁ + C₂, h₁.add h₂, ?_, ?_, ?_⟩
    · rw [hSC]; exact h₁.add h₁
    · rw [hSC']; exact h₂.add h₂
    · rw [Matrix.trace_add, Complex.add_re]
      ring
  · rintro ⟨S, hS, hSC, hSC', rfl⟩
    refine ⟨(1 / 2 : ℝ) • (S + C), (1 / 2 : ℝ) • (S - C),
      Matrix.PosSemidef.smul hSC (a := (1 / 2 : ℝ)) (by norm_num),
      Matrix.PosSemidef.smul hSC' (a := (1 / 2 : ℝ)) (by norm_num),
      (half_smul_sub (X := S) (Y := C)).symm, ?_⟩
    have htr :
        (((1 / 2 : ℝ) • (S + C)).trace + ((1 / 2 : ℝ) • (S - C)).trace) = S.trace := by
      rw [Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub]
      simp only [Complex.real_smul]
      push_cast
      ring
    have hrs : (((1 / 2 : ℝ) • (S + C)).trace).re +
        (((1 / 2 : ℝ) • (S - C)).trace).re = (S.trace).re := by
      have := congrArg Complex.re htr
      simpa [Complex.add_re] using this
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← hrs]
    ring

/-- **Lemma 2 (p. 4), `n = 1` instance.**  For every 1-slot virtual-comb Choi
operator `C`, the base norm `‖C‖_♦` of Eq. (A3) equals the diamond norm
`‖C‖_♢` of Eq. (A2), both being the common optimal value of the two SDPs. -/
theorem lemma2_baseNorm_eq_diamondNorm (C : Matrix ι ι ℂ) (d : ℝ) :
    baseNorm C d = diamondNorm C d := by
  unfold baseNorm diamondNorm
  rw [baseNormValues_eq_diamondNormValues]

/-! ## The optimal base-norm constant of Theorem 4 -/

/-- The base-norm constant `γ(d_A, d_B) = d_A d_B − d_A + 1` that Theorem 4
identifies as the minimum base norm of a 1-slot virtual comb implementing the
complex conjugate (p. 5, and Eq. (A4) in Appendix A). -/
def gammaBaseNorm (dA dB : ℕ) : ℝ :=
  (dA : ℝ) * (dB : ℝ) - (dA : ℝ) + 1

/-- The constant `γ(d_A, d_B) = d_A d_B − d_A + 1` is positive for positive
dimensions. -/
theorem gammaBaseNorm_pos {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB) :
    0 < gammaBaseNorm dA dB := by
  unfold gammaBaseNorm
  have hA : (0 : ℝ) < (dA : ℝ) := by exact_mod_cast hdA
  have hB : (1 : ℝ) ≤ (dB : ℝ) := by exact_mod_cast hdB
  have hmul : (dA : ℝ) ≤ (dA : ℝ) * (dB : ℝ) := by
    calc (dA : ℝ) = (dA : ℝ) * 1 := by ring
      _ ≤ (dA : ℝ) * (dB : ℝ) := by gcongr
  linarith

end Qatlib.Papers.PetzRecovery26.VirtualAdjoint
