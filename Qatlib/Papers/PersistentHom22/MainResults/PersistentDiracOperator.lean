/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block

set_option backward.isDefEq.respectTransparency false

/-!
# PersistentHom22.MainResults.PersistentDiracOperator

Paper-layer Lean for **PersistentHom22** = *Quantum Persistent Homology*
(Ameneyro-Maroulas-Siopsis, arXiv:2202.12965), fixed at the prefetched PDF
`2202.12965.pdf` (text dump `2202.12965.txt`). Claim **c002**.

Source anchors (page numbers are arXiv PDF pages):

* Eq. (15), p.7 -- definition of the `k`-th persistent Dirac operator
  `B_k = [[0, dt_k, 0], [dt_k^T, 0, dt_{k+1}], [0, dt_{k+1}^T, 0]] - xi * diag(P_{k-1}, -P_k, P_{k+1})`.
* Eq. (16), p.7 -- its square is block form with the middle block being the `k`-th
  persistent combinatorial Laplacian `L_k` shifted by `xi^2`.

The three chain spaces are `C_{k-1}` (`Vm`), `C_k` (`V0`) and `C_{k+1}` (`Vp`).  The
persistent boundary maps are the compressed operators `dt_k = P_{k-1} d_k P_k` and
`dt_{k+1} = P_k d_{k+1} P_{k+1}` (paper Eq. (14), p.7); `P_*` are the orthogonal
projectors of Eq. (12).  We use the (odd | even) splitting `(Vm + Vp) + V0`, the
reordering of Eq. (16) that isolates `L_k` as the even (central) block.

Boundary note: chain coordinates are over `R` (boundary matrices have entries in `{0, +-1}`),
so the Hermitian adjoint `dag` of the paper is the plain transpose `T`; we therefore phrase
self-adjointness as transpose-symmetry.  QRAM/Grover cost is not modelled here; that is the
algorithmic-complexity part of claim c001.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.PersistentHom22.MainResults

variable {Vm V0 Vp : Type*}
  [Fintype Vm] [Fintype V0] [Fintype Vp]
  [DecidableEq Vm] [DecidableEq V0] [DecidableEq Vp]

/-- Paper Eq. (14), p.7: the restricted boundary map `dt = P_left d P_right`. -/
def restrictedBoundary (Pleft : Matrix Vm Vm ℝ) (Pright : Matrix V0 V0 ℝ)
    (d : Matrix Vm V0 ℝ) : Matrix Vm V0 ℝ :=
  Pleft * d * Pright

/-- A restricted boundary map is fixed on the left by its left projector (idempotence). -/
lemma restrictedBoundary_left (Pleft : Matrix Vm Vm ℝ) (Pright : Matrix V0 V0 ℝ)
    (d : Matrix Vm V0 ℝ) (h : Pleft * Pleft = Pleft) :
    Pleft * restrictedBoundary Pleft Pright d = restrictedBoundary Pleft Pright d := by
  unfold restrictedBoundary
  rw [show Pleft * (Pleft * d * Pright) = Pleft * d * Pright by
    rw [Matrix.mul_assoc Pleft d Pright, ← Matrix.mul_assoc Pleft Pleft (d * Pright), h]]

/-- A restricted boundary map is fixed on the right by its right projector (idempotence). -/
lemma restrictedBoundary_right (Pleft : Matrix Vm Vm ℝ) (Pright : Matrix V0 V0 ℝ)
    (d : Matrix Vm V0 ℝ) (h : Pright * Pright = Pright) :
    restrictedBoundary Pleft Pright d * Pright = restrictedBoundary Pleft Pright d := by
  unfold restrictedBoundary
  rw [show Pleft * d * Pright * Pright = Pleft * d * Pright by
    rw [Matrix.mul_assoc (Pleft * d) Pright Pright, h]]

/-- The off-diagonal part of `B_k` in Eq. (15): the map
`V0 -> Vm + Vp`, `Y |-> (dt_k Y, dt_{k+1}^T Y)` (here `C^T = dt_{k+1}^T`). -/
def oddEvenMap (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) : Matrix (Vm ⊕ Vp) V0 ℝ :=
  Matrix.of (fun i j => Sum.elim (fun a => A a j) (fun c => Cᵀ c j) i)

/-- Odd Even Map inl: the paper model identity or bound. -/
lemma oddEvenMap_inl (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) (a : Vm) (j : V0) :
    oddEvenMap A C (Sum.inl a) j = A a j := rfl

/-- Odd Even Map inr: the paper model identity or bound. -/
lemma oddEvenMap_inr (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) (c : Vp) (j : V0) :
    oddEvenMap A C (Sum.inr c) j = Cᵀ c j := rfl

/-- The even block of `(B_k)^2`, Eq. (16), p.7:
`M^T M = dt_k^T dt_k + dt_{k+1} dt_{k+1}^T`, the persistent Laplacian of Eq. (8), p.5. -/
lemma oddEvenMap_transpose_mul_self (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) :
    (oddEvenMap A C)ᵀ * oddEvenMap A C = Aᵀ * A + C * Cᵀ := by
  ext i j
  simp [Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type, oddEvenMap,
    transpose_apply, mul_comm]

/-- The `k`-th persistent combinatorial Laplacian `L_k` (paper Eq. (8), p.5):
`L_k = dt_k^T dt_k + dt_{k+1} dt_{k+1}^T`. -/
def persistentLaplacian (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) : Matrix V0 V0 ℝ :=
  Aᵀ * A + C * Cᵀ

/-- The off-diagonal (`xi`-independent) block operator of Eq. (15), p.7:
`D = [[0, dt_k, 0], [dt_k^T, 0, dt_{k+1}], [0, dt_{k+1}^T, 0]]` in the (odd | even) layout. -/
def diracOddEven (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) :
    Matrix ((Vm ⊕ Vp) ⊕ V0) ((Vm ⊕ Vp) ⊕ V0) ℝ :=
  fromBlocks (0 : Matrix (Vm ⊕ Vp) (Vm ⊕ Vp) ℝ) (oddEvenMap A C) (oddEvenMap A C)ᵀ
    (0 : Matrix V0 V0 ℝ)

/-- The signed projector `diag(P_{k-1}, -P_k, P_{k+1})` of Eq. (15), p.7,
in the (odd | even) layout. -/
def diracProjector (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ) :
    Matrix ((Vm ⊕ Vp) ⊕ V0) ((Vm ⊕ Vp) ⊕ V0) ℝ :=
  fromBlocks (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp)
    (0 : Matrix (Vm ⊕ Vp) V0 ℝ) (0 : Matrix V0 (Vm ⊕ Vp) ℝ) (-P0)

/-- The unsigned projector `diag(P_{k-1}, P_k, P_{k+1})` occurring on the right of Eq. (16). -/
def diracProjectorAbs (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ) :
    Matrix ((Vm ⊕ Vp) ⊕ V0) ((Vm ⊕ Vp) ⊕ V0) ℝ :=
  fromBlocks (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp)
    (0 : Matrix (Vm ⊕ Vp) V0 ℝ) (0 : Matrix V0 (Vm ⊕ Vp) ℝ) P0

/-- The `k`-th persistent Dirac operator `B_k` of paper Eq. (15), p.7. -/
def diracOperator (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) (ξ : ℝ) :
    Matrix ((Vm ⊕ Vp) ⊕ V0) ((Vm ⊕ Vp) ⊕ V0) ℝ :=
  diracOddEven A C - ξ • diracProjector Pm P0 Pp

/-- `M P_k = M` from the right-compression of both restricted boundaries. -/
lemma oddEvenMap_mul_projector (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (P0 : Matrix V0 V0 ℝ) (hAR : A * P0 = A) (hCL : P0 * C = C) (hP0 : P0ᵀ = P0) :
    oddEvenMap A C * P0 = oddEvenMap A C := by
  have hC : Cᵀ * P0 = Cᵀ := by
    have h := congrArg transpose hCL
    rw [transpose_mul, hP0] at h
    exact h
  ext i j
  rw [Matrix.mul_apply]
  cases i with
  | inl a =>
    simp only [oddEvenMap_inl]
    simpa [Matrix.mul_apply] using congrFun (congrFun hAR a) j
  | inr c =>
    simp only [oddEvenMap_inr]
    simpa [Matrix.mul_apply] using congrFun (congrFun hC c) j

/-- `P_{k-1} + P_{k+1}` fixes `M = oddEvenMap` on the left. -/
lemma diag_mul_oddEvenMap (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (Pm : Matrix Vm Vm ℝ) (Pp : Matrix Vp Vp ℝ)
    (hAL : Pm * A = A) (hCR : C * Pp = C) (hPp : Ppᵀ = Pp) :
    (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp :
        Matrix (Vm ⊕ Vp) (Vm ⊕ Vp) ℝ) * oddEvenMap A C = oddEvenMap A C := by
  have hC : Pp * Cᵀ = Cᵀ := by
    have h := congrArg transpose hCR
    rw [transpose_mul, hPp] at h
    exact h
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  cases i with
  | inl a =>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, oddEvenMap_inl, oddEvenMap_inr,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    simpa [Matrix.mul_apply] using congrFun (congrFun hAL a) j
  | inr c =>
    simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, oddEvenMap_inl, oddEvenMap_inr,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    simpa [Matrix.mul_apply] using congrFun (congrFun hC c) j

/-- `diracProjector^2 = diag(P_{k-1}, P_k, P_{k+1}) = diracProjectorAbs` (paper Eq. (16)). -/
lemma diracProjector_sq (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (hPm : Pm * Pm = Pm) (hP0 : P0 * P0 = P0) (hPp : Pp * Pp = Pp) :
    diracProjector Pm P0 Pp * diracProjector Pm P0 Pp = diracProjectorAbs Pm P0 Pp := by
  unfold diracProjector diracProjectorAbs
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [neg_mul_neg, hPm, hPp, hP0]

/-- The signed projector is symmetric. -/
lemma diracProjector_transpose (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ)
    (Pp : Matrix Vp Vp ℝ) (hPm : Pmᵀ = Pm) (hP0 : P0ᵀ = P0) (hPp : Ppᵀ = Pp) :
    (diracProjector Pm P0 Pp)ᵀ = diracProjector Pm P0 Pp := by
  unfold diracProjector
  rw [fromBlocks_transpose, fromBlocks_transpose]
  simp [hPm, hP0, hPp, transpose_neg]

/-- The off-diagonal Dirac block is symmetric (`B_k` is self-adjoint). -/
lemma diracOddEven_transpose (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) :
    (diracOddEven A C)ᵀ = diracOddEven A C := by
  unfold diracOddEven
  rw [fromBlocks_transpose]
  simp

/-- `D^2` has the persistent Laplacian as its even block (paper Eq. (16), p.7). -/
lemma diracOddEven_sq (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ) :
    diracOddEven A C * diracOddEven A C =
      fromBlocks (oddEvenMap A C * (oddEvenMap A C)ᵀ) 0 0 (persistentLaplacian A C) := by
  unfold diracOddEven persistentLaplacian
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [oddEvenMap_transpose_mul_self]

/-- The cross term `D . diag(P,-P,P) + diag(P,-P,P) . D` vanishes: compression of the
boundary maps (Eq. (14)) makes `D` and the signed projector anticommute. -/
lemma diracEven_mul_projector (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (hAL : Pm * A = A) (hAR : A * P0 = A) (hCL : P0 * C = C) (hCR : C * Pp = C)
    (hPmH : Pmᵀ = Pm) (hP0H : P0ᵀ = P0) (hPpH : Ppᵀ = Pp) :
    diracOddEven A C * diracProjector Pm P0 Pp +
        diracProjector Pm P0 Pp * diracOddEven A C = 0 := by
  have hMP : oddEvenMap A C * (-P0) = -oddEvenMap A C := by
    rw [Matrix.mul_neg, oddEvenMap_mul_projector A C P0 hAR hCL hP0H]
  have hEM : (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp :
        Matrix (Vm ⊕ Vp) (Vm ⊕ Vp) ℝ) * oddEvenMap A C = oddEvenMap A C :=
    diag_mul_oddEvenMap A C Pm Pp hAL hCR hPpH
  have hEM' : (oddEvenMap A C)ᵀ * (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp :
        Matrix (Vm ⊕ Vp) (Vm ⊕ Vp) ℝ) = (oddEvenMap A C)ᵀ := by
    have h := congrArg transpose hEM
    rw [transpose_mul, fromBlocks_transpose] at h
    rw [hPmH, hPpH] at h
    simpa using h
  have hMP' : P0 * (oddEvenMap A C)ᵀ = (oddEvenMap A C)ᵀ := by
    have h := congrArg transpose (oddEvenMap_mul_projector A C P0 hAR hCL hP0H)
    rw [transpose_mul, hP0H] at h
    exact h
  unfold diracOddEven diracProjector
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
  simp only [Matrix.mul_zero, Matrix.zero_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [hMP, hEM, Matrix.neg_mul, hEM', hMP']
  simp

/-- **Main c002 result** -- paper Eq. (16), p.7: the square of the `k`-th persistent Dirac
operator `B_k` is, in block form, the off-diagonal square plus `xi^2` times the unsigned
projector `diag(P_{k-1}, P_k, P_{k+1})`. -/
theorem persistentDiracOperator_sq (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (hPm : Pm * Pm = Pm) (hP0 : P0 * P0 = P0) (hPp : Pp * Pp = Pp)
    (hPmH : Pmᵀ = Pm) (hP0H : P0ᵀ = P0) (hPpH : Ppᵀ = Pp)
    (hAL : Pm * A = A) (hAR : A * P0 = A) (hCL : P0 * C = C) (hCR : C * Pp = C)
    (ξ : ℝ) :
    diracOperator Pm P0 Pp A C ξ * diracOperator Pm P0 Pp A C ξ =
      fromBlocks (oddEvenMap A C * (oddEvenMap A C)ᵀ
          + (ξ * ξ) • (fromBlocks Pm (0 : Matrix Vm Vp ℝ) (0 : Matrix Vp Vm ℝ) Pp :
              Matrix (Vm ⊕ Vp) (Vm ⊕ Vp) ℝ))
        0 0 (persistentLaplacian A C + (ξ * ξ) • P0) := by
  have hcross := diracEven_mul_projector A C Pm P0 Pp hAL hAR hCL hCR hPmH hP0H hPpH
  have hz : ξ • (diracOddEven A C * diracProjector Pm P0 Pp)
      + ξ • (diracProjector Pm P0 Pp * diracOddEven A C) = 0 := by
    rw [← smul_add, hcross, smul_zero]
  have hsq : diracOperator Pm P0 Pp A C ξ * diracOperator Pm P0 Pp A C ξ =
      diracOddEven A C * diracOddEven A C
        - ξ • (diracOddEven A C * diracProjector Pm P0 Pp)
        - ξ • (diracProjector Pm P0 Pp * diracOddEven A C)
        + (ξ * ξ) • (diracProjector Pm P0 Pp * diracProjector Pm P0 Pp) := by
    unfold diracOperator
    simp only [sub_mul, mul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    abel
  rw [hsq, sub_sub, hz]
  simp only [sub_zero, zero_add]
  rw [diracProjector_sq Pm P0 Pp hPm hP0 hPp, diracOddEven_sq]
  unfold diracProjectorAbs
  rw [fromBlocks_smul, fromBlocks_add]
  simp

/-- **c002, central block.**  The even (central) block of `(B_k)^2` is exactly the
persistent combinatorial Laplacian `L_k` shifted by `xi^2 P_k` -- the precise content of
"one of the blocks being the kth persistent combinatorial Laplacian shifted by xi^2"
(Eq. (16), p.7). -/
theorem persistentDiracOperator_sq_center (A : Matrix Vm V0 ℝ) (C : Matrix V0 Vp ℝ)
    (Pm : Matrix Vm Vm ℝ) (P0 : Matrix V0 V0 ℝ) (Pp : Matrix Vp Vp ℝ)
    (hPm : Pm * Pm = Pm) (hP0 : P0 * P0 = P0) (hPp : Pp * Pp = Pp)
    (hPmH : Pmᵀ = Pm) (hP0H : P0ᵀ = P0) (hPpH : Ppᵀ = Pp)
    (hAL : Pm * A = A) (hAR : A * P0 = A) (hCL : P0 * C = C) (hCR : C * Pp = C)
    (ξ : ℝ) :
    Matrix.toBlocks₂₂ (diracOperator Pm P0 Pp A C ξ * diracOperator Pm P0 Pp A C ξ)
      = persistentLaplacian A C + (ξ * ξ) • P0 := by
  rw [persistentDiracOperator_sq A C Pm P0 Pp hPm hP0 hPp hPmH hP0H hPpH hAL hAR hCL hCR ξ]
  rw [toBlocks_fromBlocks₂₂]

end Qatlib.Papers.PersistentHom22.MainResults
