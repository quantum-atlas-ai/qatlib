/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# ContourMatFun21 — paper-layer block-encoding vocabulary

Fixed arXiv:2106.08076v2 (Takahira, Ohashi, Sogabe, Usuda).
This file re-states the two source definitions used throughout the paper:

* `IsApproxBlockEncoding U j₀ A α ε` — paper Definition 1 (p. 4, Eq. (3)):
  `U` is unitary, `α > 0`, and `‖A − α·⟨0ᵃ|U|0ᵃ⟩‖ ≤ ε` where `⟨0ᵃ|U|0ᵃ⟩` is the
  defined `BlockCorner U j₀` (the all-zero ancilla corner in the abstract ancilla
  type `J`).
* `IsStatePrepPair VL VR j₀ μ δ v` — paper Definition 2 (p. 4): the pair
  `(VL, VR)` prepares the (unnormalised) vector `v` up to ℓ¹ error `δ` at
  normalisation `μ`.

The shared library carries the *exact* (`ε = 0`) notion `IsBlockEncoding`
(`Qatlib.Papers.Qubitization19.LCUConsumers.IsBlockEncoding`).  The
paper's results are all stated with the error `ε ≥ 0`, so the paper layer keeps
the approximate form above and connects the two with
`isApproxBlockEncoding_zero_iff`.

The gate-count statements of the source (`O(d)` uses of `U_A`, `O((a+1)d)`
single- and two-qubit gates) are complexity facts about a circuit model; the
matrix-semantics layer of this library does not carry a gate count, so the
formal statements record the *matrix-level* content (normalisation `α`, ancilla
count, operator-norm error `ε`) and note the cost claim in the docstring.  No
query or gate count is asserted here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ContourMatFun21.MainResults

variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- Paper Definition 1 (arXiv:2106.08076v2, p. 4, Eq. (3)): `U` is an
`(α, a, ε)`-block-encoding of `A` when `U` is unitary on `J × I` (ancilla `J`,
system `I`), `α > 0`, and the `j₀`-corner obeys
`‖A − α·(⟨j₀| ⊗ I)U(|j₀⟩ ⊗ I)‖ ≤ ε`.  Here the corner `⟨j₀|U|j₀⟩` is the shared
`BlockCorner U j₀`. -/
def IsApproxBlockEncoding (U : Matrix (J × I) (J × I) ℂ) (j₀ : J)
    (A : Matrix I I ℂ) (α ε : ℝ) : Prop :=
  U ∈ Matrix.unitaryGroup (J × I) ℂ ∧ 0 < α ∧
    ‖A - ((α : ℂ)) • BlockCorner U j₀‖ ≤ ε

/-- The exact (`ε = 0`) block encoding of Definition 1 is the shared
`IsBlockEncoding` (`Qatlib.Papers.Qubitization19.LCUConsumers`). -/
theorem isApproxBlockEncoding_zero_iff {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} {α : ℝ} :
    IsApproxBlockEncoding U j₀ A α 0 ↔ IsBlockEncoding U j₀ A α := by
  unfold IsApproxBlockEncoding IsBlockEncoding
  constructor
  · rintro ⟨hU, hα, hnorm⟩
    refine ⟨hU, hα, ?_⟩
    rw [norm_le_zero_iff, sub_eq_zero] at hnorm
    rw [hnorm]
    rw [show ((α⁻¹ : ℝ) : ℂ) = (α : ℂ)⁻¹ by rw [Complex.ofReal_inv]]
    rw [inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hα.ne')]
  · rintro ⟨hU, hα, hcorner⟩
    refine ⟨hU, hα, ?_⟩
    rw [hcorner, smul_smul, norm_le_zero_iff, sub_eq_zero]
    rw [show ((α : ℂ) * ((α⁻¹ : ℝ) : ℂ)) = 1 by
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hα.ne')],
      one_smul]

/-- An exact block encoding is an approximate one with `ε = 0`. -/
theorem isApproxBlockEncoding_of_exact {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} {α : ℝ} (h : IsBlockEncoding U j₀ A α) :
    IsApproxBlockEncoding U j₀ A α 0 :=
  isApproxBlockEncoding_zero_iff.mpr h

/-- Monotonicity in the error: a `(α, a, ε)`-encoding is an `(α, a, ε')`-encoding
for every `ε' ≥ ε`. -/
theorem IsApproxBlockEncoding.mono_err {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} {α ε ε' : ℝ} (h : IsApproxBlockEncoding U j₀ A α ε)
    (hε : ε ≤ ε') : IsApproxBlockEncoding U j₀ A α ε' :=
  ⟨h.1, h.2.1, le_trans h.2.2 hε⟩

/-- Scaling the encoded operator scales both the normalisation and the error
(paper §2.1, "If `U` is an `(α,a,ε)`-block-encoding of `A`, then `U` is also the
`(cα, a, cε)`-block-encoding of `cA`"). -/
theorem IsApproxBlockEncoding.scale {U : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {A : Matrix I I ℂ} {α ε : ℝ} (h : IsApproxBlockEncoding U j₀ A α ε)
    {c : ℝ} (hc : 0 < c) :
    IsApproxBlockEncoding U j₀ ((c : ℂ) • A) (c * α) (c * ε) := by
  refine ⟨h.1, mul_pos hc h.2.1, ?_⟩
  have hcast : (((c * α : ℝ)) : ℂ) = (c : ℂ) * (α : ℂ) := Complex.ofReal_mul c α
  rw [hcast, ← smul_smul, ← smul_sub, norm_smul]
  have hcabs : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [hcabs]
  exact mul_le_mul_of_nonneg_left h.2.2 hc.le

/-- Paper Definition 2 (arXiv:2106.08076v2, p. 4): `(VL, VR)` is a
`(μ, m, δ)`-state-preparation pair for the vector `v` when both are unitary on
the ancilla `J`, `μ ≥ 0`, and the diagonal of `μ·(VL|j₀⟩)(VR|j₀⟩)†` (i.e.
`μ·c̄ⱼdⱼ`) is within ℓ¹ distance `δ` of `v`: `Σⱼ ‖μ c̄ⱼ dⱼ − vⱼ‖ ≤ δ`, where
`c = VL|j₀⟩`, `d = VR|j₀⟩`.  The trailing-zero clause of Definition 2 is
encoded by taking `vⱼ = 0` beyond the support of `v`. -/
def IsStatePrepPair (VL VR : Matrix J J ℂ) (j₀ : J) (μ δ : ℝ) (v : J → ℂ) : Prop :=
  VL ∈ Matrix.unitaryGroup J ℂ ∧ VR ∈ Matrix.unitaryGroup J ℂ ∧ 0 ≤ μ ∧
    ∑ j, ‖((μ : ℂ) * star ((VL *ᵥ Ket j₀) j)) * ((VR *ᵥ Ket j₀) j) - v j‖ ≤ δ

/-- The prepared vector of a state-preparation pair, `cⱼ = (VL|j₀⟩)ⱼ`. -/
def prepVec (VL : Matrix J J ℂ) (j₀ : J) : J → ℂ := VL *ᵥ Ket j₀

/-- Block-diagonal matrix `diag(B₀, B₁, …)` on `M × I` with `k`-th diagonal block
`Bfam k : Matrix I I ℂ` — the paper's `𝗔 = diag(A₀,…,A_{M−1})`. -/
def blockDiag {M : Type*} [Fintype M] [DecidableEq M] (Bfam : M → Matrix I I ℂ) :
    Matrix (M × I) (M × I) ℂ :=
  Matrix.of fun (k, i) (k', i') => if k = k' then Bfam k i i' else 0

/-- Unfolding the state-preparation-pair error as an ℓ¹ bound. -/
theorem IsStatePrepPair.le {VL VR : Matrix J J ℂ} {j₀ : J} {μ δ : ℝ} {v : J → ℂ}
    (h : IsStatePrepPair VL VR j₀ μ δ v) :
    ∑ j, ‖((μ : ℂ) * star (prepVec VL j₀ j)) * (prepVec VR j₀ j) - v j‖ ≤ δ :=
  h.2.2.2

end Qatlib.Papers.ContourMatFun21.MainResults
