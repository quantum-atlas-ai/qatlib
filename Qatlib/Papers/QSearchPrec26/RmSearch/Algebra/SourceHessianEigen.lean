/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.Algebra — Theorem 3: the Riemannian gradient is a Hessian eigenvector

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Theorem 3 (p. 6–7).

The paper works on `U(N)`: for a Hamiltonian `H = H† = H²` (an orthogonal projector) and a
pure state `ψ = |ψ⟩⟨ψ|`, it sets `q := Tr(Hψ) ∈ [0,1]`, `g := [H,ψ]` and
`L(Ω) := ½([H,[Ω,ψ]] + [[H,Ω],ψ])`, and proves `L(g) = (1 - 2q) g`.  Consequently `g` is an
eigenvector of the Riemannian Hessian with eigenvalue `1 - 2q`, so the Newton direction is
collinear with the gradient (hence needs no Hessian inverse).

The core is a purely associative-ring identity: `H² = H`, `ψ² = ψ`, `ψHψ = qψ` and `q` central.
We state and prove that identity generically (`commutator_hessian_identity`), then specialize it
to complex matrices and to the paper's `L` (`hessian_gradient_eigen`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.Algebra

open Matrix

/-- The commutator `[A,B] = AB - BA`, the Lie bracket of `u(N)`. -/
def commutator {A : Type*} [Mul A] [Sub A] (a b : A) : A := a * b - b * a

/-- Associative-ring Jacobi-type identity, specialized at a gradient: with `g = [H,ψ]` the
two terms of `L(g)` coincide, `[H,[g,ψ]] = [[H,g],ψ]`.  This is the step
`[H,[g,ψ]] = [[H,g],ψ] + [g,[H,ψ]] = [[H,g],ψ]` in the proof of Theorem 3 (p. 7), where
`[g,[H,ψ]] = [g,g] = 0`. -/
theorem commutator_jacobi_self {A : Type*} [Ring A] (H ψ : A) :
    commutator H (commutator (commutator H ψ) ψ)
      = commutator (commutator H (commutator H ψ)) ψ := by
  unfold commutator
  noncomm_ring

/-- **Theorem 3, core ring identity** (arXiv:2603.26039v3, p. 7): for an orthogonal projector
`H` (`H² = H`), a pure state `ψ` (`ψ² = ψ`), `q := Tr(Hψ)` (so `ψHψ = qψ`) with `q` central,
and `g := [H,ψ]`, one has `[H,[g,ψ]] = (1-2q)g`.

This is exactly the computation `L(g) = [[H,g],ψ] = (1-2q)g` in the paper's proof. -/
theorem commutator_hessian_identity {A : Type*} [Ring A]
    (H ψ q : A) (hH : H * H = H) (hψ : ψ * ψ = ψ)
    (hqψ : ψ * H * ψ = q * ψ)
    (hqH : q * H = H * q) (hqψ' : q * ψ = ψ * q) :
    commutator H (commutator (commutator H ψ) ψ) = (1 - 2 * q) * commutator H ψ := by
  -- `[g,ψ] = Hψ - 2 q ψ + ψH` where `g = Hψ - ψH`.
  have h_inner : commutator (commutator H ψ) ψ = H * ψ - (q * ψ + q * ψ) + ψ * H := by
    unfold commutator
    calc
      (H * ψ - ψ * H) * ψ - ψ * (H * ψ - ψ * H)
          = H * (ψ * ψ) - ψ * H * ψ - ψ * H * ψ + (ψ * ψ) * H := by
            noncomm_ring
      _ = H * ψ - q * ψ - q * ψ + ψ * H := by rw [hψ, hqψ]
      _ = H * ψ - (q * ψ + q * ψ) + ψ * H := by noncomm_ring
  rw [h_inner]
  have hexp : commutator H (H * ψ - (q * ψ + q * ψ) + ψ * H)
      = H * H * ψ - (H * (q * ψ) + H * (q * ψ))
          + ((q * ψ) * H + (q * ψ) * H) - ψ * (H * H) := by
    unfold commutator
    noncomm_ring
  have hHq : H * (q * ψ) = q * (H * ψ) := by
    rw [hqψ', ← mul_assoc q H ψ, hqH, mul_assoc H q ψ, hqψ']
  have hqH' : (q * ψ) * H = q * (ψ * H) := by
    rw [hqψ', ← mul_assoc q ψ H, hqψ']
  rw [hexp, hHq, hqH', hH]
  unfold commutator
  noncomm_ring

/-- Scalar matrices act by scalar multiplication on the left: writing the scalar matrix as a
scalar multiple of the identity, `(1 - 2·scalar q) * M = (1 - 2q) • M`. -/
theorem scalar_one_sub_mul {n : Type*} [Fintype n] [DecidableEq n] (q : ℂ)
    (M : Matrix n n ℂ) :
    (1 - (2 : Matrix n n ℂ) * Matrix.scalar n q) * M = (1 - 2 * q) • M := by
  have hsc : Matrix.scalar n q = q • (1 : Matrix n n ℂ) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have h2 : (2 : Matrix n n ℂ) = (2 : ℂ) • (1 : Matrix n n ℂ) := by
    rw [two_smul]
    norm_num
  rw [hsc, h2, Matrix.sub_mul, sub_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, smul_smul,
    one_smul]
  rw [mul_comm q 2]

/-- **Theorem 3** (arXiv:2603.26039v3, p. 6–7).  For an orthogonal projector `H` and a pure
state `ψ` with `ψHψ = q • ψ` (i.e. `q = Tr(Hψ)`), the linear map
`L(Ω) = ½([H,[Ω,ψ]] + [[H,Ω],ψ])` satisfies `L(g) = (1 - 2q) • g` at `g = [H,ψ]`.
Thus the Riemannian gradient `g` is an eigenvector of the Riemannian Hessian with eigenvalue
`1 - 2q`. -/
theorem hessian_gradient_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (H ψ : Matrix n n ℂ) (q : ℂ)
    (hH : H * H = H) (hψ : ψ * ψ = ψ)
    (hq : ψ * H * ψ = q • ψ) :
    (2 : ℂ)⁻¹ • (commutator H (commutator (commutator H ψ) ψ)
        + commutator (commutator H (commutator H ψ)) ψ)
      = (1 - 2 * q) • commutator H ψ := by
  have hscalar : ψ * H * ψ = Matrix.scalar n q * ψ := by
    rw [hq, Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]
  have hqH : Matrix.scalar n q * H = H * Matrix.scalar n q :=
    (Matrix.scalar_commute q (fun r' => Commute.all _ _) H).eq
  have hqψ : Matrix.scalar n q * ψ = ψ * Matrix.scalar n q :=
    (Matrix.scalar_commute q (fun r' => Commute.all _ _) ψ).eq
  have hkey := commutator_hessian_identity H ψ (Matrix.scalar n q) hH hψ hscalar hqH hqψ
  have hJac := commutator_jacobi_self H ψ
  rw [hJac] at hkey ⊢
  rw [← two_smul ℂ (commutator (commutator H (commutator H ψ)) ψ)]
  rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [hkey, scalar_one_sub_mul]

/-- The paper's `L` applied at `g`, in the original notation of Theorem 3. -/
def hessianMap {n : Type*} [Fintype n] [DecidableEq n] (H ψ Ω : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (commutator H (commutator Ω ψ) + commutator (commutator H Ω) ψ)

/-- **Theorem 3, restated through `hessianMap`**: `L(g) = (1-2q)g`. -/
theorem hessianMap_gradient {n : Type*} [Fintype n] [DecidableEq n]
    (H ψ : Matrix n n ℂ) (q : ℂ)
    (hH : H * H = H) (hψ : ψ * ψ = ψ)
    (hq : ψ * H * ψ = q • ψ) :
    hessianMap H ψ (commutator H ψ) = (1 - 2 * q) • commutator H ψ := by
  simpa [hessianMap] using hessian_gradient_eigen H ψ q hH hψ hq

/-! ### Lemma 7: Newton cancellation (arXiv:2603.26039v3, p. 16–17)

Lemma 7 upgrades the identity of Theorem 3 to the cancellation of the first-order term of the
gradient map `G(U) = [H, Uψ₀U†]`: for `q > 1/2` and `γ = (2q-1)⁻¹`, the full modified Newton
direction `η = γ g_U U` satisfies `G(U) + DG(U)[η] = 0`.  The two ingredients are Eq. (B11)
(identical to the ring identity proved above) and the directional-derivative formula Eq. (B7). -/

/-- **Lemma 7, Eq. (B11)** (arXiv:2603.26039v3, p. 16): `[H,[g,ψ]] = (1-2q)g` at `g = [H,ψ]`. -/
theorem newton_cancellation {n : Type*} [Fintype n] [DecidableEq n]
    (H ψ : Matrix n n ℂ) (q : ℂ)
    (hH : H * H = H) (hψ : ψ * ψ = ψ)
    (hq : ψ * H * ψ = q • ψ) :
    commutator H (commutator (commutator H ψ) ψ) = (1 - 2 * q) • commutator H ψ := by
  have hscalar : ψ * H * ψ = Matrix.scalar n q * ψ := by
    rw [hq, Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]
  have hqH : Matrix.scalar n q * H = H * Matrix.scalar n q :=
    (Matrix.scalar_commute q (fun r' => Commute.all _ _) H).eq
  have hqψ : Matrix.scalar n q * ψ = ψ * Matrix.scalar n q :=
    (Matrix.scalar_commute q (fun r' => Commute.all _ _) ψ).eq
  have hkey := commutator_hessian_identity H ψ (Matrix.scalar n q) hH hψ hscalar hqH hqψ
  rwa [scalar_one_sub_mul] at hkey

/-- Composing the commutator with `H` is `ℂ`-linear. -/
theorem commutator_smul_left {n : Type*} [Fintype n] [DecidableEq n]
    (γ : ℂ) (H A : Matrix n n ℂ) :
    commutator H (γ • A) = γ • commutator H A := by
  unfold commutator
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Scaling the first commutator argument scales the commutator. -/
theorem commutator_smul_arg {n : Type*} [Fintype n] [DecidableEq n]
    (γ : ℂ) (A B : Matrix n n ℂ) :
    commutator (γ • A) B = γ • commutator A B := by
  unfold commutator
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- **Lemma 7, cancellation identity** (arXiv:2603.26039v3, p. 16–17).  Let `ψ_U` be a pure state,
`q = Tr(Hψ_U)`, `g_U = [H,ψ_U]`, and let the full Newton direction be `Ω = γ g_U` with
`γ = (2q-1)⁻¹` (so `q ≠ 1/2`).  Then `G(U) + DG(U)[ΩU] = g_U + [H,[Ω,ψ_U]] = 0`, which is the
statement `G(U)+DG(U)[γ g_U U] = 0` of Lemma 7. -/
theorem newton_full_step_cancels {n : Type*} [Fintype n] [DecidableEq n]
    (H ψU : Matrix n n ℂ) (q γ : ℂ)
    (hH : H * H = H) (hψU : ψU * ψU = ψU)
    (hq : ψU * H * ψU = q • ψU)
    (hγ : γ = (2 * q - 1)⁻¹) (hne : 2 * q - 1 ≠ 0) :
    commutator H ψU + commutator H (commutator (γ • commutator H ψU) ψU) = 0 := by
  have hγ' : γ * (1 - 2 * q) = -1 := by
    rw [hγ]
    have h1 : (1 : ℂ) - 2 * q = -(2 * q - 1) := by ring
    rw [h1, mul_neg, inv_mul_cancel₀ hne]
  have hkey := newton_cancellation H ψU q hH hψU hq
  rw [commutator_smul_arg γ (commutator H ψU) ψU, commutator_smul_left γ H
      (commutator (commutator H ψU) ψU), hkey, smul_smul, hγ']
  rw [neg_smul, one_smul]
  abel

end Qatlib.Papers.QSearchPrec26.RmSearch.Algebra
