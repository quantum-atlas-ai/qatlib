/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false

/-!
# Perturbation of quadratic forms under approximate block encodings

Source: Jiang and An, "Contour-integral based quantum eigenvalue transformation: analysis and
applications", fixed arXiv:2601.11959v3 (2026-09-20).  Theorem 12 (Appendix C, p. 35) is the
single-ancilla LCU perturbation bound: if `‖P - Q‖ ≤ ξ` and `U_Q` is an `(α, a, 0)` block encoding
of `Q`, then the quadratic forms `⟨ψ|P†OP|ψ⟩` and `α²⟨ψ̃|U_Q†ÕU_Q|ψ̃⟩` differ by at most
`3‖O‖‖P‖ξ`.

The formalization works with matrices in the L2 operator norm.  The observable `O` is a matrix
`M` on the system space and its lift to the workspace is `L M Lᴴ`, where `L` is the isometric
frame of the block encoding (for the standard choice `L = |0^a⟩ ⊗ I` this is exactly
`|0^a⟩⟨0^a| ⊗ M`).  The proof reuses the paper's decomposition
`PρP† - QρQ† = (P-Q)ρ(P-Q)† + Qρ(P-Q)† + (P-Q)ρQ†` at the level of quadratic forms and its
Hölder-type estimate `‖PᴴMP - QᴴMQ‖ ≤ ξ‖M‖(2‖P‖ + ξ)`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.Execution.WorkspaceCP

namespace Qatlib.Papers.ContourQET26.EigenTransform

/-- Quadratic form `⟨v, M v⟩` of a square matrix `M` evaluated at a Euclidean-space vector `v`. -/
def qform {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℂ n)
    (M : Matrix n n ℂ) : ℂ :=
  inner ℂ v (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M v)

/-- The same quadratic form written with matrix-vector products; this form is convenient for the
algebraic identities, since rectangular factors are allowed. -/
def qformFn {n : Type*} [Fintype n] (x : n → ℂ) (M : Matrix n n ℂ) : ℂ :=
  star x ⬝ᵥ (M *ᵥ x)

/-- Basic bound `‖⟨v, M v⟩‖ ≤ ‖M‖ ‖v‖²` used throughout the perturbation estimate. -/
lemma norm_qform_le {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℂ n)
    (M : Matrix n n ℂ) : ‖qform v M‖ ≤ ‖M‖ * ‖v‖ ^ 2 := by
  unfold qform
  calc ‖inner ℂ v (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M v)‖
      ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := by
        gcongr
        have h := ContinuousLinearMap.le_opNorm
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M) v
        rwa [Matrix.l2_opNorm_toEuclideanCLM] at h
    _ = ‖M‖ * ‖v‖ ^ 2 := by ring

/-- Quadratic forms are additive in the matrix. -/
lemma qform_sub {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℂ n)
    (A B : Matrix n n ℂ) : qform v (A - B) = qform v A - qform v B := by
  simp [qform, map_sub, ContinuousLinearMap.sub_apply, inner_sub_right]

/-- Conversion of the two quadratic-form presentations. -/
lemma qform_eq_qformFn {n : Type*} [Fintype n] [DecidableEq n] (v : EuclideanSpace ℂ n)
    (M : Matrix n n ℂ) : qform v M = qformFn (WithLp.ofLp v) M := by
  simp only [qform, qformFn]
  rw [show v = WithLp.toLp 2 (WithLp.ofLp v) by simp]
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

/-- Conjugation identity: `⟨x, A† M A x⟩ = ⟨A x, M (A x)⟩`, valid for rectangular `A`. -/
lemma qformFn_conj {m n : Type*} [Fintype m] [Fintype n] (x : m → ℂ)
    (A : Matrix n m ℂ) (M : Matrix n n ℂ) :
    qformFn x (Aᴴ * M * A) = qformFn (A *ᵥ x) M := by
  unfold qformFn
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [dotProduct_mulVec]
  rw [vecMul_conjTranspose, star_star]

/-- Scaling of a vector by a real number scales the quadratic form by its square. -/
lemma qformFn_smul_real {n : Type*} [Fintype n] (c : ℝ) (x : n → ℂ)
    (M : Matrix n n ℂ) :
    qformFn ((c : ℂ) • x) M = ((c ^ 2 : ℝ) : ℂ) * qformFn x M := by
  unfold qformFn
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  rw [smul_smul]
  have hstarc : star ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = ((c ^ 2 : ℝ) : ℂ) := by
    rw [show star ((c : ℝ) : ℂ) = ((c : ℝ) : ℂ) from by
        rw [Complex.ext_iff]; constructor <;> simp,
      ← Complex.ofReal_mul]
    congr 1
    ring
  rw [hstarc]
  ring

/-- Scaling of the matrix by a scalar scales the quadratic form by the same scalar. -/
lemma qformFn_smul_matrix {n : Type*} [Fintype n] (c : ℂ) (x : n → ℂ)
    (M : Matrix n n ℂ) : qformFn x (c • M) = c * qformFn x M := by
  unfold qformFn
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rfl

set_option maxHeartbeats 6000000 in
/-- **Theorem 12, norm estimate (C.8) in quadratic-form language.**  If `ξ ≤ 1 ≤ ‖P‖` and
`‖P - Q‖ ≤ ξ`, then the two quadratic forms are `3‖M‖‖P‖ξ`-close.  This is the analytic heart of
Theorem 12; it does not use any quantum data. -/
theorem qform_perturb_bound {N : Type*} [Fintype N] [DecidableEq N]
    (P Q M : Matrix N N ℂ) (ξ : ℝ) (hPQ : ‖P - Q‖ ≤ ξ) (hξ : ξ ≤ 1) (hP : 1 ≤ ‖P‖)
    (v : EuclideanSpace ℂ N) (hv : ‖v‖ = 1) :
    ‖qform v (Pᴴ * M * P) - qform v (Qᴴ * M * Q)‖ ≤ 3 * ‖M‖ * ‖P‖ * ξ := by
  have hsub : qform v (Pᴴ * M * P) - qform v (Qᴴ * M * Q)
      = qform v (Pᴴ * M * P - Qᴴ * M * Q) := by
    rw [qform_sub]
  rw [hsub]
  have hdecomp : Pᴴ * M * P - Qᴴ * M * Q = (P - Q)ᴴ * M * P + Qᴴ * M * (P - Q) := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  have hQnorm : ‖Q‖ ≤ ‖P‖ + ξ := by
    calc ‖Q‖ = ‖P - (P - Q)‖ := by congr 1; abel
      _ ≤ ‖P‖ + ‖P - Q‖ := norm_sub_le _ _
      _ ≤ ‖P‖ + ξ := add_le_add le_rfl hPQ
  have hξn : 0 ≤ ξ := le_trans (norm_nonneg (P - Q)) hPQ
  have h1 : ‖(P - Q)ᴴ * M * P‖ ≤ ξ * ‖M‖ * ‖P‖ := by
    have e2' : ‖(P - Q)ᴴ * M‖ ≤ ‖P - Q‖ * ‖M‖ := by
      rw [show ‖P - Q‖ * ‖M‖ = ‖(P - Q)ᴴ‖ * ‖M‖ from by
        rw [Matrix.l2_opNorm_conjTranspose]]
      exact Matrix.l2_opNorm_mul _ _
    have e0' : ‖(P - Q)ᴴ * M * P‖ ≤ ‖(P - Q)ᴴ * M‖ * ‖P‖ := Matrix.l2_opNorm_mul _ _
    calc ‖(P - Q)ᴴ * M * P‖ ≤ ‖(P - Q)ᴴ * M‖ * ‖P‖ := e0'
      _ ≤ (‖P - Q‖ * ‖M‖) * ‖P‖ := by
          exact mul_le_mul_of_nonneg_right e2' (norm_nonneg _)
      _ ≤ (ξ * ‖M‖) * ‖P‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hPQ (norm_nonneg _)) (norm_nonneg _)
      _ = ξ * ‖M‖ * ‖P‖ := by ring
  have h2 : ‖Qᴴ * M * (P - Q)‖ ≤ (‖P‖ + ξ) * ‖M‖ * ξ := by
    have e2h : ‖Qᴴ * M‖ ≤ ‖Q‖ * ‖M‖ := by
      rw [show ‖Q‖ * ‖M‖ = ‖Qᴴ‖ * ‖M‖ from by rw [Matrix.l2_opNorm_conjTranspose]]
      exact Matrix.l2_opNorm_mul _ _
    have e0h : ‖Qᴴ * M * (P - Q)‖ ≤ ‖Qᴴ * M‖ * ‖P - Q‖ := Matrix.l2_opNorm_mul _ _
    calc ‖Qᴴ * M * (P - Q)‖ ≤ ‖Qᴴ * M‖ * ‖P - Q‖ := e0h
      _ ≤ (‖Q‖ * ‖M‖) * ‖P - Q‖ := by
          exact mul_le_mul_of_nonneg_right e2h (norm_nonneg _)
      _ ≤ ((‖P‖ + ξ) * ‖M‖) * ‖P - Q‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hQnorm (norm_nonneg _)) (norm_nonneg _)
      _ ≤ ((‖P‖ + ξ) * ‖M‖) * ξ := by
          exact mul_le_mul_of_nonneg_left hPQ
            (mul_nonneg (add_nonneg (norm_nonneg P) hξn) (norm_nonneg M))
      _ = (‖P‖ + ξ) * ‖M‖ * ξ := by ring
  have hsum : ‖(P - Q)ᴴ * M * P + Qᴴ * M * (P - Q)‖
      ≤ ξ * ‖M‖ * ‖P‖ + (‖P‖ + ξ) * ‖M‖ * ξ := by
    calc ‖(P - Q)ᴴ * M * P + Qᴴ * M * (P - Q)‖
        ≤ ‖(P - Q)ᴴ * M * P‖ + ‖Qᴴ * M * (P - Q)‖ := norm_add_le _ _
      _ ≤ ξ * ‖M‖ * ‖P‖ + (‖P‖ + ξ) * ‖M‖ * ξ := by gcongr
  have hξ2 : ξ ^ 2 ≤ ‖P‖ * ξ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (le_trans hξ hP) hξn
  calc ‖qform v (Pᴴ * M * P - Qᴴ * M * Q)‖
      ≤ ‖Pᴴ * M * P - Qᴴ * M * Q‖ * ‖v‖ ^ 2 := norm_qform_le v _
    _ = ‖Pᴴ * M * P - Qᴴ * M * Q‖ := by rw [hv]; ring
    _ = ‖(P - Q)ᴴ * M * P + Qᴴ * M * (P - Q)‖ := by rw [hdecomp]
    _ ≤ ξ * ‖M‖ * ‖P‖ + (‖P‖ + ξ) * ‖M‖ * ξ := hsum
    _ ≤ 3 * ‖M‖ * ‖P‖ * ξ := by nlinarith [norm_nonneg M, norm_nonneg P]


set_option maxHeartbeats 6000000 in
/-- **Theorem 12, source statement (C.1), block-encoding form.**  Let `U` be an `(α, a, 0)` block
encoding of `Q` between isometric frames `L, R`; let `M` be the observable on the system space,
lifted to the workspace as `L M Lᴴ`.  Then
`α²⟨Rψ|U†(L M Lᴴ)U|Rψ⟩ = ⟨ψ|Q†MQ|ψ⟩`.  This is eq. (C.4) of the paper, where the paper's
`|0^a⟩⟨0^a| ⊗ O` is `L M Lᴴ` for the computational-basis frame `L`. -/
theorem qform_encoding_eq {O H : Type*} [Fintype O] [DecidableEq O] [Fintype H] [DecidableEq H]
    (Q M : Matrix O O ℂ) (U : Matrix H H ℂ) (L R : Matrix H O ℂ) (α : ℝ)
    (hBE : BlockEncoding Q U L R α 0) (ψ : EuclideanSpace ℂ O) :
    ((α ^ 2 : ℝ) : ℂ) * qform (Matrix.toEuclideanLin R ψ) (Uᴴ * (L * M * Lᴴ) * U)
      = qform ψ (Qᴴ * M * Q) := by
  have hQ : Q = α • (Lᴴ * U * R) := by
    have hz : ‖Q - α • compress L U R‖ = 0 :=
      le_antisymm hBE.error_le (norm_nonneg _)
    have h0 : Q - α • compress L U R = 0 := norm_eq_zero.mp hz
    simpa [compress] using sub_eq_zero.mp h0
  have hRL : WithLp.ofLp (Matrix.toEuclideanLin R ψ) = R *ᵥ WithLp.ofLp ψ := by
    simp
  have hα : ((α : ℂ) * (α : ℂ)) = ((α ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, sq]
  calc ((α ^ 2 : ℝ) : ℂ) * qform (Matrix.toEuclideanLin R ψ) (Uᴴ * (L * M * Lᴴ) * U)
      = ((α ^ 2 : ℝ) : ℂ) * qformFn (R *ᵥ WithLp.ofLp ψ) (Uᴴ * (L * M * Lᴴ) * U) := by
          rw [qform_eq_qformFn, hRL]
    _ = ((α ^ 2 : ℝ) : ℂ) * qformFn (U *ᵥ (R *ᵥ WithLp.ofLp ψ)) (L * M * Lᴴ) := by
          rw [qformFn_conj]
    _ = ((α ^ 2 : ℝ) : ℂ) * qformFn (Lᴴ *ᵥ (U *ᵥ (R *ᵥ WithLp.ofLp ψ))) M := by
          congr 1
          rw [← qformFn_conj (x := U *ᵥ (R *ᵥ WithLp.ofLp ψ)) (A := Lᴴ) (M := M)]
          simp [Matrix.conjTranspose_conjTranspose]
    _ = ((α ^ 2 : ℝ) : ℂ) * qformFn ((Lᴴ * U * R) *ᵥ WithLp.ofLp ψ) M := by
          congr 2
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = qformFn (WithLp.ofLp ψ) (Qᴴ * M * Q) := by
          rw [hQ]
          have hmat : (α • (Lᴴ * U * R))ᴴ * M * (α • (Lᴴ * U * R))
              = ((α ^ 2 : ℝ) : ℂ) • ((Lᴴ * U * R)ᴴ * M * (Lᴴ * U * R)) := by
            have hstar : star (α : ℝ) = α := star_trivial _
            have hbridge : ∀ Y : Matrix O O ℂ, (α : ℝ) • Y = ((α : ℂ)) • Y := by
              intro Y
              rw [← algebraMap_smul (R := ℝ) (A := ℂ), RCLike.algebraMap_eq_ofReal]
              rfl
            rw [Matrix.conjTranspose_smul, hstar, hbridge, hbridge, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.smul_mul, smul_smul, hα]
          rw [hmat, qformFn_smul_matrix, ← qformFn_conj (x := WithLp.ofLp ψ)
            (A := Lᴴ * U * R) (M := M)]
    _ = qform ψ (Qᴴ * M * Q) := by
          rw [← qform_eq_qformFn]

set_option maxHeartbeats 6000000 in
/-- **Theorem 12 (Appendix C, p. 35), source statement.**  For an exact `(α, a, 0)` block
encoding `U_Q` of `Q`, states `|ψ⟩`, an observable `O` lifted to `Õ = L O Lᴴ`, and `‖P - Q‖ ≤ ξ`
with `ξ ≤ 1 ≤ ‖P‖`, one has
`|⟨ψ|P†OP|ψ⟩ - α²⟨ψ̃|U_Q†ÕU_Q|ψ̃⟩| ≤ 3‖O‖‖P‖ξ` (eq. (C.1)). -/
theorem theorem12_perturbation {O H : Type*} [Fintype O] [DecidableEq O] [Fintype H]
    [DecidableEq H] (P Q M : Matrix O O ℂ) (U : Matrix H H ℂ) (L R : Matrix H O ℂ)
    (α ξ : ℝ) (hBE : BlockEncoding Q U L R α 0) (hPQ : ‖P - Q‖ ≤ ξ) (hξ : ξ ≤ 1)
    (hP : 1 ≤ ‖P‖) (ψ : EuclideanSpace ℂ O) (hψ : ‖ψ‖ = 1) :
    ‖qform ψ (Pᴴ * M * P)
        - ((α ^ 2 : ℝ) : ℂ) * qform (Matrix.toEuclideanLin R ψ) (Uᴴ * (L * M * Lᴴ) * U)‖
      ≤ 3 * ‖M‖ * ‖P‖ * ξ := by
  rw [qform_encoding_eq Q M U L R α hBE ψ]
  exact qform_perturb_bound P Q M ξ hPQ hξ hP ψ hψ

end Qatlib.Papers.ContourQET26.EigenTransform
