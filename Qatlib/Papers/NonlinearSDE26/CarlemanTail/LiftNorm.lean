/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanError17.MainResults.Core.SourceModel
public import Qatlib.Papers.QEigenProc24.MainResults.BlockMatrix
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
public import Qatlib.Foundations.OperatorErrors.OperatorError

@[expose] public section

/-!
# Operator norm of the Carleman lift

In arXiv:2603.12398v1, Definition 3 and Eqs. (273)–(276), each row
degree has its own tensor space. Each of the three bands has one
possible block per row and per column. Applying the block row/column
bound to each band keeps the total estimate linear in the order.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator Kronecker
open Matrix
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Papers.CarlemanError17.MainResults.Core
open Qatlib.Papers.QEigenProc24.MainResults.BlockMatrix

namespace Qatlib.Papers.NonlinearSDE26.CarlemanTail

variable {n r : ℕ}

/-- Pulling a vector back by a bijection preserves its Euclidean norm. -/
private theorem norm_fromVec_comp_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (v : Y → ℂ) :
    ‖toEuclidean_fromVec (v ∘ e)‖ = ‖toEuclidean_fromVec v‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map (toEuclidean_fromVec v)

/-- Reindexing both axes of a rectangular matrix by bijections does not increase its norm. -/
private theorem norm_submatrix_equiv_le {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y'] [DecidableEq Y] [DecidableEq Y']
    (A : Matrix X Y ℂ) (e : X' ≃ X) (f : Y' ≃ Y) :
    ‖A.submatrix e f‖ ≤ ‖A‖ := by
  apply l2_opNorm_le_of_mulVec_le (norm_nonneg _)
  intro v
  have hv : (A.submatrix e f) *ᵥ v = (A *ᵥ (v ∘ f.symm)) ∘ e := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
    simpa only [Equiv.symm_apply_apply] using
      f.sum_comp (fun j => A (e i) j * v (f.symm j))
  rw [hv, norm_fromVec_comp_equiv]
  have h := l2_norm_mulVec_fromVec_le A (v ∘ f.symm)
  rwa [norm_fromVec_comp_equiv] at h

/-- Tensor products with row and column indices concatenated in paper order. -/
def kronTransfer {a b c d : ℕ} (A : Matrix (TP n a) (TP n b) ℂ)
    (B : Matrix (TP n c) (TP n d) ℂ) : Matrix (TP n (a + c)) (TP n (b + d)) ℂ :=
  (A ⊗ₖ B).submatrix (Fin.appendEquiv a c).symm (Fin.appendEquiv b d).symm

/-- The Kronecker product estimate is unchanged by concatenating the tensor indices. -/
private theorem norm_kronTransfer_le {a b c d : ℕ} (A : Matrix (TP n a) (TP n b) ℂ)
    (B : Matrix (TP n c) (TP n d) ℂ) : ‖kronTransfer A B‖ ≤ ‖A‖ * ‖B‖ :=
  (norm_submatrix_equiv_le _ _ _).trans (l2_norm_kronecker_le A B)

/-- The sum of insertions of an arity-`r` coefficient in a tensor with
`k+1` output positions. Appending the last position splits the sum
into earlier insertions tensored with identity and the final insertion. -/
def tensorTransfer (F : Matrix (TP n 1) (TP n r) ℂ) :
    (k : ℕ) → Matrix (TP n (k + 1)) (TP n (k + r)) ℂ
  | 0 => F.submatrix (Equiv.refl _) (tpCast (Nat.zero_add r))
  | k + 1 =>
    (kronTransfer (tensorTransfer F k) (1 : Matrix (TP n 1) (TP n 1) ℂ)).submatrix
      (Equiv.refl _) (tpCast (by omega)) +
    kronTransfer (1 : Matrix (TP n (k + 1)) (TP n (k + 1)) ℂ) F

/-- Each insertion contributes at most the norm of the original coefficient. -/
theorem norm_tensorTransfer_le (F : Matrix (TP n 1) (TP n r) ℂ) (k : ℕ) :
    ‖tensorTransfer F k‖ ≤ (k + 1 : ℕ) * ‖F‖ := by
  induction k with
  | zero =>
    simpa only [tensorTransfer, Nat.zero_add, Nat.cast_one, one_mul] using
      norm_submatrix_equiv_le F (Equiv.refl _) (tpCast (Nat.zero_add r))
  | succ k ih =>
    rw [tensorTransfer]
    have hleft :=
      (norm_submatrix_equiv_le (kronTransfer (tensorTransfer F k)
        (1 : Matrix (TP n 1) (TP n 1) ℂ)) (Equiv.refl _) (tpCast (by omega : k + 1 + r = k + r + 1))).trans
        ((norm_kronTransfer_le _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) l2_norm_one_le))
    have hright := (norm_kronTransfer_le (1 : Matrix (TP n (k + 1)) (TP n (k + 1)) ℂ) F).trans
      (mul_le_of_le_one_left (norm_nonneg _) l2_norm_one_le)
    calc
      _ ≤ ‖tensorTransfer F k‖ + ‖F‖ := (norm_add_le _ _).trans (add_le_add hleft hright)
      _ ≤ (k + 1 : ℕ) * ‖F‖ + ‖F‖ := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

/-- The arity-`r` transfer block is placed only in the column whose
tensor degree is the output degree minus one plus `r`. -/
def carlemanBandBlock (F : Matrix (TP n 1) (TP n r) ℂ) {N : ℕ}
    (j k : Fin N) : Matrix (TP n (j.val + 1)) (TP n (k.val + 1)) ℂ :=
  if h : k.val + 1 = j.val + r then
    (tensorTransfer F j.val).submatrix (Equiv.refl _) (tpCast h)
  else 0

/-- Indices of the truncated direct sum of tensor degrees one through `N`. -/
abbrev LiftIndex (n N : ℕ) := Σ j : Fin N, TP n (j.val + 1)

/-- Assemble a transfer band on the direct sum of the actual tensor spaces. -/
def carlemanBand (N : ℕ) (F : Matrix (TP n 1) (TP n r) ℂ) :
    Matrix (LiftIndex n N) (LiftIndex n N) ℂ :=
  blockMatrix (fun j : Fin N => TP n (j.val + 1)) (fun j : Fin N => TP n (j.val + 1)) (carlemanBandBlock F)

/-- A nonnegative constant summed over at most one index is at most the constant. -/
private theorem sum_single_band_le {K : Type} [Fintype K] (P : K → Prop) [DecidablePred P]
    (c : ℝ) (hc : 0 ≤ c) (huniq : ∀ x y, P x → P y → x = y) :
    (∑ i, if P i then c else 0) ≤ c := by
  have hcard : (Finset.univ.filter P).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact huniq a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_of_le_one_left hc (by exact_mod_cast hcard)

/-- Each row and each column of a fixed arity band has at most one
nonzero block, so its norm is bounded by `N‖F‖`. -/
theorem norm_carlemanBand_le (N : ℕ) (hN : 0 < N) (F : Matrix (TP n 1) (TP n r) ℂ) :
    ‖carlemanBand N F‖ ≤ (N : ℝ) * ‖F‖ := by
  let _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let c := (N : ℝ) * ‖F‖
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hb (j k : Fin N) : ‖carlemanBandBlock F j k‖ ≤
      if k.val + 1 = j.val + r then c else 0 := by
    by_cases h : k.val + 1 = j.val + r
    · rw [carlemanBandBlock, dite_eq_left h, ite_eq_left h]
      exact (norm_submatrix_equiv_le _ _ _).trans
        ((norm_tensorTransfer_le F j.val).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast j.isLt) (norm_nonneg _)))
    · simp [carlemanBandBlock, h]
  have hcol (k : Fin N) : ∑ j, ‖carlemanBandBlock F j k‖ ≤ c :=
    (Finset.sum_le_sum fun j _ => hb j k).trans
      (sum_single_band_le _ c hc (fun j j' h h' => Fin.ext (by omega)))
  have hrow (j : Fin N) : ∑ k, ‖carlemanBandBlock F j k‖ ≤ c :=
    (Finset.sum_le_sum fun k _ => hb j k).trans
      (sum_single_band_le _ c hc (fun k k' h h' => Fin.ext (by omega)))
  have h := block_matrix_spectral_norm_bound (fun j : Fin N => TP n (j.val + 1))
    (fun j : Fin N => TP n (j.val + 1)) (carlemanBandBlock F)
  refine h.trans ?_
  calc
    _ ≤ Real.sqrt c * Real.sqrt c :=
      mul_le_mul (Real.sqrt_le_sqrt (Finset.sup'_le _ _ (fun k _ => hcol k)))
        (Real.sqrt_le_sqrt (Finset.sup'_le _ _ (fun j _ => hrow j))) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = c := Real.mul_self_sqrt hc

/-- The truncated coefficient matrix from Definition 3, excluding
the order-zero column which appears as the inhomogeneous forcing. -/
def carlemanBlockLift (N : ℕ) (F₀ : Matrix (TP n 1) (TP n 0) ℂ)
    (F₁ : Matrix (TP n 1) (TP n 1) ℂ) (F₂ : Matrix (TP n 1) (TP n 2) ℂ) :
    Matrix (LiftIndex n N) (LiftIndex n N) ℂ :=
  carlemanBand N F₀ + carlemanBand N F₁ + carlemanBand N F₂

/-- Equation (273): the full Carleman coefficient matrix obeys the
linear-in-order bound with no extra normalization of its coefficients. -/
theorem carleman_block_lift_norm_le (N : ℕ) (hN : 0 < N)
    (F₀ : Matrix (TP n 1) (TP n 0) ℂ) (F₁ : Matrix (TP n 1) (TP n 1) ℂ)
    (F₂ : Matrix (TP n 1) (TP n 2) ℂ) :
    ‖carlemanBlockLift N F₀ F₁ F₂‖ ≤ (N : ℝ) * (‖F₀‖ + ‖F₁‖ + ‖F₂‖) := by
  unfold carlemanBlockLift
  apply (norm_add_le _ _).trans
  have hleft := (norm_add_le (carlemanBand N F₀) (carlemanBand N F₁)).trans
    (add_le_add (norm_carlemanBand_le N hN F₀) (norm_carlemanBand_le N hN F₁))
  simpa only [mul_add] using add_le_add hleft (norm_carlemanBand_le N hN F₂)

/-- The same norm bound applies to each realized time-dependent forcing. -/
theorem pathwise_carleman_block_lift_norm_le {Ω : Type} (N : ℕ) (hN : 0 < N)
    (F₀ : Ω → ℝ → Matrix (TP n 1) (TP n 0) ℂ)
    (F₁ : Matrix (TP n 1) (TP n 1) ℂ) (F₂ : Matrix (TP n 1) (TP n 2) ℂ) (ω : Ω) (t : ℝ) :
    ‖carlemanBlockLift N (F₀ ω t) F₁ F₂‖ ≤ (N : ℝ) * (‖F₀ ω t‖ + ‖F₁‖ + ‖F₂‖) :=
  carleman_block_lift_norm_le N hN _ F₁ F₂

end Qatlib.Papers.NonlinearSDE26.CarlemanTail
