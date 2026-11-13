/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import Qatlib.Papers.PersistentHom22.MainResults.PersistentDiracOperator

/-!
# Eigenspace Correspondence Between the Persistent Dirac Operator and Laplacian

This module establishes the spectral correspondence between the persistent Dirac operator
$B_k$ and the persistent combinatorial Laplacian $\mathcal{L}_k$. In particular, for any
nonzero shift $\xi \neq 0$, the $\lambda = \xi$ eigenspace of $B_k$ (with even component
in the persistent chain group) is in explicit bijection with $\ker \mathcal{L}_k \cap \mathrm{im}\, P_k$.

## Main statements

* `dirac_eigenvector_laplacian_eigenvector`: An eigenvector of $B_k$ with eigenvalue $\lambda$
  and $P_k$-invariant even part yields an eigenvector of $\mathcal{L}_k$ with eigenvalue
  $\lambda^2 - \xi^2$.
* `laplacian_kernel_iff_xi_shifted`: Characterization of $\ker \mathcal{L}_k$ on $P_k$-invariant
  chains as the $\xi^2$-eigenspace of $\mathcal{L}_k + \xi^2 P_k$.
* `xi_eigenspace_equiv_laplacian_kernel`: Explicit bijection between the persistent kernel
  of $\mathcal{L}_k$ and the $\xi$-eigenspace of $B_k$ when $\xi \neq 0$.

## References

* [Ameneyro, Maroulas, and Siopsis, 2022][AmeneyroMaroulasSiopsis2022]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.PersistentHom22.MainResults

section Projections

variable {Vm V0 Vp : Type*}

/-- Even (`C_k`) component of a state on `(Vm ⊕ Vp) ⊕ V0`. -/
def evenPart (x : ((Vm ⊕ Vp) ⊕ V0) → ℝ) : V0 → ℝ := fun j => x (Sum.inr j)

/-- Odd (`C_{k-1} ⊕ C_{k+1}`) component of a state on `(Vm ⊕ Vp) ⊕ V0`. -/
def oddPart (x : ((Vm ⊕ Vp) ⊕ V0) → ℝ) : Vm ⊕ Vp → ℝ := fun i => x (Sum.inl i)

/-- Evaluation of `evenPart` at a chain basis index `j : V0`. -/
@[simp] lemma evenPart_apply (x : ((Vm ⊕ Vp) ⊕ V0) → ℝ) (j : V0) :
    evenPart x j = x (Sum.inr j) := rfl

/-- Evaluation of `oddPart` at a chain basis index `i : Vm ⊕ Vp`. -/
@[simp] lemma oddPart_apply (x : ((Vm ⊕ Vp) ⊕ V0) → ℝ) (i : Vm ⊕ Vp) :
    oddPart x i = x (Sum.inl i) := rfl

/-- Scaling commutes with taking the even component. -/
lemma evenPart_smul (c : ℝ) (x : ((Vm ⊕ Vp) ⊕ V0) → ℝ) :
    evenPart (c • x) = c • evenPart x := by
  funext j
  rfl

private lemma diracOperator_eq_fromBlocks
    (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) (ξ : ℝ) :
    diracOperator Pm P0 Pp A C ξ =
      fromBlocks
        (-(ξ • (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp)))
        (oddEvenMap A C)
        (oddEvenMap A C)ᵀ
        (ξ • P0) := by
  unfold diracOperator diracOddEven diracProjector
  rw [fromBlocks_smul]
  ext i j
  cases i <;> cases j <;> simp [sub_eq_add_neg]

end Projections

/-- At `ξ = 0`, the `+ξ` and `-ξ` branches coincide, explaining why `ξ ≠ 0` is required for the
eigenspace bijection. -/
theorem xi_zero_branches_coincide : (-(0 : ℝ)) = 0 := neg_zero

section KernelShift

variable {Vm V0 Vp : Type*} [Fintype Vm] [Fintype V0] [Fintype Vp]

/-- For a state `y` in the persistent chain group (`P0 *ᵥ y = y`), `y` lies in the kernel of
`L_k` iff it is an eigenvector of `L_k + ξ² P0` with eigenvalue `ξ²`
[AmeneyroMaroulasSiopsis2022]. -/
theorem laplacian_kernel_iff_xi_shifted
    (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) (P0 : Matrix V0 V0 ℝ)
    (ξ : ℝ) (y : V0 → ℝ) (hy : P0 *ᵥ y = y) :
    persistentLaplacian A C *ᵥ y = 0 ↔
      (persistentLaplacian A C + (ξ * ξ) • P0) *ᵥ y = (ξ * ξ) • y := by
  constructor
  · intro h
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hy, h, zero_add]
  · intro h
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, hy] at h
    have hh : persistentLaplacian A C *ᵥ y + (ξ * ξ) • y = (0 : V0 → ℝ) + (ξ * ξ) • y := by
      rw [zero_add]
      exact h
    exact add_right_cancel hh

end KernelShift

section Correspondence

variable {Vm V0 Vp : Type*}
  [Fintype Vm] [Fintype V0] [Fintype Vp]
  [DecidableEq Vm] [DecidableEq V0] [DecidableEq Vp]

/-- If `v` is an eigenvector of the persistent Dirac operator `B_k` with eigenvalue `lam`
and its even component is fixed by `P0`, then `evenPart v` is an eigenvector of the persistent
combinatorial Laplacian `L_k` with eigenvalue `lam * lam - ξ * ξ`
[AmeneyroMaroulasSiopsis2022]. -/
theorem dirac_eigenvector_laplacian_eigenvector
    (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (hPm : Pm * Pm = Pm) (hP0 : P0 * P0 = P0) (hPp : Pp * Pp = Pp)
    (hPmH : Pmᵀ = Pm) (hP0H : P0ᵀ = P0) (hPpH : Ppᵀ = Pp)
    (hAL : Pm * A = A) (hAR : A * P0 = A) (hCL : P0 * C = C) (hCR : C * Pp = C)
    (ξ lam : ℝ) (v : ((Vm ⊕ Vp) ⊕ V0) → ℝ)
    (hv : diracOperator Pm P0 Pp A C ξ *ᵥ v = lam • v)
    (hmid : P0 *ᵥ evenPart v = evenPart v) :
    persistentLaplacian A C *ᵥ evenPart v = (lam * lam - ξ * ξ) • evenPart v := by
  have h1 : (diracOperator Pm P0 Pp A C ξ * diracOperator Pm P0 Pp A C ξ) *ᵥ v
      = (lam * lam) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul]
  have hBB := persistentDiracOperator_sq A C Pm P0 Pp hPm hP0 hPp hPmH hP0H hPpH
    hAL hAR hCL hCR ξ
  have h3 : evenPart ((diracOperator Pm P0 Pp A C ξ * diracOperator Pm P0 Pp A C ξ) *ᵥ v)
      = (persistentLaplacian A C + (ξ * ξ) • P0) *ᵥ evenPart v := by
    rw [hBB, Matrix.fromBlocks_mulVec]
    funext j
    have hcomp : evenPart v = v ∘ Sum.inr := rfl
    simp [evenPart, Matrix.zero_mulVec, hcomp]
  have h2 : evenPart ((diracOperator Pm P0 Pp A C ξ * diracOperator Pm P0 Pp A C ξ) *ᵥ v)
      = (lam * lam) • evenPart v := by
    rw [h1, evenPart_smul]
  have hA : (persistentLaplacian A C + (ξ * ξ) • P0) *ᵥ evenPart v
      = (lam * lam) • evenPart v := by
    rw [← h3, h2]
  have h4 : persistentLaplacian A C *ᵥ evenPart v + (ξ * ξ) • evenPart v
      = (lam * lam) • evenPart v := by
    rw [← hA, Matrix.add_mulVec, Matrix.smul_mulVec, hmid]
  rw [sub_smul]
  exact eq_sub_iff_add_eq.mpr h4

/-- For `ξ ≠ 0`, the `λ = ξ` eigenspace of the persistent Dirac operator `B_k` (with even
component fixed by `P0`) is in bijection with the persistent kernel of the combinatorial
Laplacian `L_k` [AmeneyroMaroulasSiopsis2022]. -/
theorem xi_eigenspace_equiv_laplacian_kernel
    (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (hPm : Pm * Pm = Pm) (hP0 : P0 * P0 = P0) (hPp : Pp * Pp = Pp)
    (hPmH : Pmᵀ = Pm) (hP0H : P0ᵀ = P0) (hPpH : Ppᵀ = Pp)
    (hAL : Pm * A = A) (hAR : A * P0 = A) (hCL : P0 * C = C) (hCR : C * Pp = C)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    Nonempty ({y : V0 → ℝ // persistentLaplacian A C *ᵥ y = 0 ∧ P0 *ᵥ y = y} ≃
      {v : ((Vm ⊕ Vp) ⊕ V0) → ℝ //
        diracOperator Pm P0 Pp A C ξ *ᵥ v = ξ • v ∧ P0 *ᵥ evenPart v = evenPart v}) := by
  let Q : Matrix (Vm ⊕ Vp) (Vm ⊕ Vp) ℝ :=
    fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp
  let M : Matrix (Vm ⊕ Vp) V0 ℝ := oddEvenMap A C
  have hB : diracOperator Pm P0 Pp A C ξ = fromBlocks (-(ξ • Q)) M Mᵀ (ξ • P0) :=
    diracOperator_eq_fromBlocks Pm P0 Pp A C ξ
  have hQQ : Q * Q = Q := by
    dsimp [Q]
    rw [fromBlocks_multiply]
    simp [hPm, hPp]
  have hQM : Q * M = M := diag_mul_oddEvenMap A C Pm Pp hAL hCR hPpH
  have hMtM : Mᵀ * M = persistentLaplacian A C := by
    dsimp [M]
    rw [oddEvenMap_transpose_mul_self, persistentLaplacian]
  refine ⟨{
    toFun := fun ⟨y, hLy, hP0y⟩ =>
      ⟨Sum.elim ((1 / (2 * ξ)) • (M *ᵥ y)) y, ?_, hP0y⟩
    invFun := fun ⟨v, hv, hmid⟩ =>
      ⟨evenPart v, ?_, hmid⟩
    left_inv := fun ⟨y, _, _⟩ => Subtype.ext rfl
    right_inv := fun ⟨v, hv, hmid⟩ => ?_
  }⟩
  · rw [hB, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have hQx : Q *ᵥ ((1 / (2 * ξ)) • (M *ᵥ y)) = (1 / (2 * ξ)) • (M *ᵥ y) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQM]
    have hodd :
        (-(ξ • Q)) *ᵥ ((1 / (2 * ξ)) • (M *ᵥ y)) + M *ᵥ y =
          ξ • ((1 / (2 * ξ)) • (M *ᵥ y)) := by
      rw [Matrix.neg_mulVec, Matrix.smul_mulVec, hQx]
      ext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have heven :
        Mᵀ *ᵥ ((1 / (2 * ξ)) • (M *ᵥ y)) + (ξ • P0) *ᵥ y = ξ • y := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMtM, hLy, smul_zero, zero_add,
        Matrix.smul_mulVec, hP0y]
    rw [hodd, heven]
    ext z
    cases z <;> rfl
  · have h := dirac_eigenvector_laplacian_eigenvector A C Pm P0 Pp hPm hP0 hPp
      hPmH hP0H hPpH hAL hAR hCL hCR ξ ξ v hv hmid
    simpa using h
  · apply Subtype.ext
    have hv_split : Sum.elim (oddPart v) (evenPart v) = v := by
      ext z
      cases z <;> rfl
    have hv' : fromBlocks (-(ξ • Q)) M Mᵀ (ξ • P0) *ᵥ Sum.elim (oddPart v) (evenPart v) =
        ξ • Sum.elim (oddPart v) (evenPart v) := by
      rwa [hv_split, ← hB]
    rw [Matrix.fromBlocks_mulVec] at hv'
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hv'
    have hodd_eq : (-(ξ • Q)) *ᵥ oddPart v + M *ᵥ evenPart v = ξ • oddPart v := by
      ext i
      exact congrFun hv' (Sum.inl i)
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec] at hodd_eq
    have hMy : M *ᵥ evenPart v = ξ • oddPart v + ξ • (Q *ᵥ oddPart v) := by
      ext i
      have hi := congrFun hodd_eq i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
      linarith
    have hQMy : Q *ᵥ (M *ᵥ evenPart v) = M *ᵥ evenPart v := by
      rw [Matrix.mulVec_mulVec, hQM]
    have hQrhs : Q *ᵥ (M *ᵥ evenPart v) = ξ • (Q *ᵥ oddPart v) + ξ • (Q *ᵥ oddPart v) := by
      rw [hMy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, hQQ]
    have hQx_eq : Q *ᵥ oddPart v = oddPart v := by
      ext i
      have h1 := congrFun hMy i
      have h2 := congrFun (hQMy.symm.trans hQrhs) i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
      have h3 : ξ * ((Q *ᵥ oddPart v) i - oddPart v i) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h0 | h0
      · exact (hξ h0).elim
      · linarith
    have hx_sol : (1 / (2 * ξ)) • (M *ᵥ evenPart v) = oddPart v := by
      rw [hMy, hQx_eq]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      field_simp
      ring
    ext z
    cases z with
    | inl i => exact congrFun hx_sol i
    | inr j => rfl

end Correspondence

end Qatlib.Papers.PersistentHom22.MainResults
