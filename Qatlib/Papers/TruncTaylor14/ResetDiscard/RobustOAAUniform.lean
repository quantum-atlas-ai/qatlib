/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation15Bridge.SourceEquation15
public import Qatlib.Foundations.OperatorErrors.OperatorError
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (15) — uniform robust-OAA constant on non-degenerate registers

[BerryEtAl2015Taylor], Eq. (15), p. 3 of
[arXiv:1412.4687v1](https://arxiv.org/abs/1412.4687v1).
The success block of the unitary encoding `W` is `X / s`. The encoded operator
`X` is `δ₁`-close to a unitary `U`, and the scale defect satisfies
`|s - 2| ≤ δ₂`, and concludes the two order estimates

* `‖ X X† - 1 ‖ = O(δ₁)` (the almost-unitarity of the encoded block), and
* `‖ P A |0⟩|ψ⟩ - |0⟩ U |ψ⟩ ‖ = O(δ)` for `δ = max(δ₁, δ₂)`,

for every normalized input `ψ`.  The frozen quantitative identity is
`Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation15Bridge.source_equation15`,
which proves the explicit bound `(15 + 12 δ₁ + 4 δ₁²) δ₁ + 15 δ₂` in the genuine
Euclidean vector norm, with the Euclidean operator norm on `‖ X - U ‖`.

This module makes the source's big-`O` conclusion uniform.  It isolates a single
absolute constant for each estimate outside the universal quantifiers. Both
the ancilla index type `J` and the data index type `I` are
required to be nonempty, which is exactly positivity of the register
cardinality (`0 < Fintype.card J`, `0 < Fintype.card I`).  No `Pi` maximum norm
is used anywhere: the vector error is measured by `toEuclidean_fromVec` into
`EuclideanSpace ℂ _`, and the operator defects are measured by the
`Matrix.Norms.L2Operator` spectral norm.

The two theorems remain conditional source-level bridges: they assume the
supplied block encoding and do not construct the Taylor PREPARE/SELECT word.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.CoherentSim.ResetDiscard
open Qatlib.Foundations.OperatorErrors.OperatorError
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.TruncTaylor14.ResetDiscard

/-- Projected robust-OAA vector error with an absolute constant outside all
quantifiers.

There is an absolute constant `C` such that, on every non-degenerate pair of
registers (nonempty ancilla type `J` and data type `I`), every scale-`s` block
encoding `W` whose encoded operator `X` is `δ₁`-close to a unitary `U` and
whose scale satisfies `|s - 2| ≤ δ₂`, amplifies so that the projected success
fibre of the amplified word is `C · (δ₁ + δ₂)`-close in the Euclidean norm to
`|0⟩ U |ψ⟩`, for every normalized input `ψ` and every `δ₁ ≤ 1`, `δ₂ ≤ 1`.

This is the paper's `‖ P A |0⟩|ψ⟩ - |0⟩ U_r |ψ⟩ ‖ = O(δ)` statement (source
Eq. (15) of arXiv:1412.4687v1, p. 3) with the constant made absolute and placed
outside all quantifiers.  The explicit coefficient `(15 + 12 δ₁ + 4 δ₁²) δ₁ +
15 δ₂` of the frozen identity is at most `31 (δ₁ + δ₂)` on the stated range, so
the uniform constant `C = 31` witnesses the existential. Since
`δ₁ + δ₂ ≤ 2 · max(δ₁, δ₂)`, this also gives a bound with constant `62` for the
maximum of the two defects. -/
theorem source_equation15_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J I : Type) [Fintype J] [DecidableEq J] [Nonempty J]
        [Fintype I] [DecidableEq I] [Nonempty I]
        (W : Matrix (J × I) (J × I) ℂ) (j₀ : J) (X U : Matrix I I ℂ) (s δ₁ δ₂ : ℝ),
        IsBlockEncoding W j₀ X s →
        U ∈ Matrix.unitaryGroup I ℂ →
        ‖X - U‖ ≤ δ₁ → δ₁ ≤ 1 → 1 ≤ s → |s - 2| ≤ δ₂ → δ₂ ≤ 1 →
        ∀ ψ : QState I, Normalized ψ →
        ‖toEuclidean_fromVec (FiberProjector j₀ *ᵥ
            (ObliviousAmplitudeAmplification (FiberProjector j₀) W *ᵥ
              TensorState (Ket j₀) ψ) - TensorState (Ket j₀) (U *ᵥ ψ))‖ ≤
          C * (δ₁ + δ₂) := by
  refine ⟨31, by norm_num, ?_⟩
  intro J I _ _ _ _ _ _ W j₀ X U s δ₁ δ₂ hW hU hXU hδ₁ hs hδ₂ hδ₂1 ψ hψ
  have hmain := Qatlib.Papers.TruncTaylor14.ResetDiscard.Equation15Bridge.source_equation15
    J I W j₀ X U s δ₁ δ₂ hW hU hXU hs hδ₂ hδ₂1 ψ hψ
  have hδ₁0 : 0 ≤ δ₁ := (norm_nonneg _).trans hXU
  have hδ₂0 : 0 ≤ δ₂ := (abs_nonneg _).trans hδ₂
  have hsq : δ₁ ^ 2 ≤ δ₁ := by nlinarith [hδ₁0, hδ₁]
  have hcube : δ₁ ^ 3 ≤ δ₁ := by nlinarith [hδ₁0, hδ₁, hsq]
  have hbound : (15 + 12 * δ₁ + 4 * δ₁ ^ 2) * δ₁ + 15 * δ₂ ≤ 31 * (δ₁ + δ₂) := by
    nlinarith [hsq, hcube, hδ₂0]
  exact hmain.trans hbound

/-- Almost-unitarity defect of an encoded near-unitary operator, with an
absolute constant outside all quantifiers.

There is an absolute constant `C` such that, on every non-degenerate register
(nonempty data index type `I`), every matrix `X` that is `δ₁`-close in the
Euclidean operator norm to a unitary `U` has almost-unitary Hermitian defect at
most `C · δ₁`, for every `δ₁ ≤ 1`.

This is the paper's `‖ Ũ Ũ† - 1 ‖ = O(δ)` statement (source Eq. (15) of
arXiv:1412.4687v1, p. 3) with the constant made absolute and placed outside all
quantifiers.  Writing `1 = U U†` and factoring `X X† - U U† = (X - U) X† + U
(X - U)†` gives the defect at most `δ₁ (1 + δ₁) + δ₁ ≤ 3 δ₁` on `0 ≤ δ₁ ≤ 1`,
so the uniform constant `C = 3` witnesses the existential.  Only the
`Matrix.Norms.L2Operator` spectral norm is used. -/
theorem encoded_operator_defect_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
        (X U : Matrix I I ℂ) (δ₁ : ℝ),
        U ∈ Matrix.unitaryGroup I ℂ → ‖X - U‖ ≤ δ₁ → δ₁ ≤ 1 →
        ‖X * X.conjTranspose - 1‖ ≤ C * δ₁ := by
  refine ⟨3, by norm_num, ?_⟩
  intro I _ _ _ X U δ₁ hU hXU hδ₁
  have hUU : U * U.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  have hkey : X * X.conjTranspose - 1 =
      (X - U) * X.conjTranspose + U * (X - U).conjTranspose := by
    have h1 : (X - U) * X.conjTranspose + U * (X - U).conjTranspose =
        X * X.conjTranspose - U * U.conjTranspose := by
      rw [Matrix.sub_mul, Matrix.conjTranspose_sub, Matrix.mul_sub]
      abel
    rw [h1, ← hUU]
  have h1 : ‖(X - U) * X.conjTranspose‖ ≤ ‖X - U‖ * ‖X‖ := by
    have h := Matrix.l2_opNorm_mul (X - U) X.conjTranspose
    rwa [Matrix.l2_opNorm_conjTranspose] at h
  have h2 : ‖U * (X - U).conjTranspose‖ ≤ ‖U‖ * ‖X - U‖ := by
    have h := Matrix.l2_opNorm_mul U (X - U).conjTranspose
    rwa [Matrix.l2_opNorm_conjTranspose] at h
  have hU1 : ‖U‖ ≤ 1 := l2_norm_unitary_le_one hU
  have hX1 : ‖X‖ ≤ 1 + δ₁ := l2_norm_le_one_add_error hU hXU
  have hδ₁0 : 0 ≤ δ₁ := (norm_nonneg _).trans hXU
  calc ‖X * X.conjTranspose - 1‖
      ≤ ‖(X - U) * X.conjTranspose‖ + ‖U * (X - U).conjTranspose‖ := by
        rw [hkey]; exact norm_add_le _ _
    _ ≤ ‖X - U‖ * ‖X‖ + ‖U‖ * ‖X - U‖ := add_le_add h1 h2
    _ ≤ δ₁ * (1 + δ₁) + 1 * δ₁ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hXU hX1 (norm_nonneg _) hδ₁0
        · exact mul_le_mul hU1 hXU (norm_nonneg _) zero_le_one
    _ ≤ 3 * δ₁ := by nlinarith [hδ₁0, hδ₁]

end Qatlib.Papers.TruncTaylor14.ResetDiscard
