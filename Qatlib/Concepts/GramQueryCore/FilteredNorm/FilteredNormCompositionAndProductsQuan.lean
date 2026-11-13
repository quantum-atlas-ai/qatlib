/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormClosureLawsQuan
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Composition and products of filtered norms

This module proves a guarded composition bound for `sourceRectValue`, the maximum formula for
block direct sums, and multiplicativity for tensor products with tensor-product filters. The
proofs combine certificate constructions with Schur multiplier duality, as used in the filtered
γ₂ calculus of [LeeEtAl2011].

## Main statements

* `sourceRectValue_composition`: The rectangular filtered value is bounded by its value relative
  to intermediate filters times the supremum of their values relative to the final filters,
  under the stated finiteness or nonzero guard.

* `sourceRectValue_directSum`: The rectangular filtered value of a direct sum with matching
  direct-sum filters is the maximum of the two component values.

* `sourceRectValue_tensor`: The rectangular filtered value is multiplicative under tensor
  products with tensor-product filters.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- Every dual-feasible multiplier gives an operator-norm lower bound on the rectangular
filtered value. -/
theorem sourceRectValue_dual_norm_le {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (M : Matrix R S ℂ) (hM : ∀ j, ‖Z j ⊙ M‖ ≤ 1) :
    ENNReal.ofReal ‖A ⊙ M‖ ≤ sourceRectValue A Z := by
  rw [(rectangularSchurDuality R S n A Z).1]
  exact le_iSup (fun N : {N : Matrix R S ℂ // ∀ j, ‖Z j ⊙ N‖ ≤ 1} =>
    ENNReal.ofReal ‖A ⊙ N.val‖) ⟨M,hM⟩

/-- An upper bound for the operator norm of every dual-feasible entrywise product bounds the
rectangular filtered value. -/
theorem sourceRectValue_le_of_dual_norm_bound {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (b : ℝ≥0∞)
    (h : ∀ M : Matrix R S ℂ, (∀ j, ‖Z j ⊙ M‖ ≤ 1) → ENNReal.ofReal ‖A ⊙ M‖ ≤ b) :
    sourceRectValue A Z ≤ b := by
  rw [(rectangularSchurDuality R S n A Z).1]
  exact iSup_le fun M => h M.val M.property

/-- The rectangular filtered value is bounded by its value relative to intermediate filters
times the supremum of their values relative to the final filters, under the stated
finiteness or nonzero guard. -/
theorem sourceRectValue_composition {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n m : ℕ} (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ)
    (Z : Fin n → Matrix R S ℂ)
    (h : sourceRectValue A Y < ⊤ ∨ (⨆ j, sourceRectValue (Y j) Z) ≠ 0) :
    sourceRectValue A Z ≤ sourceRectValue A Y * ⨆ j, sourceRectValue (Y j) Z := by
  let a := sourceRectValue A Y
  let b := ⨆ j, sourceRectValue (Y j) Z
  by_cases ha0 : a = 0
  · have hA : A = 0 := (sourceRectValue_zero_iff A Y).mp ha0
    simp [hA, sourceRectValue_zero]
  by_cases hb0 : b = 0
  · have hY : Y = 0 := by
      funext j
      apply (sourceRectValue_zero_iff (Y j) Z).mp
      exact le_antisymm ((le_iSup (fun j => sourceRectValue (Y j) Z) j).trans (le_of_eq hb0)) bot_le
    have ha : a < ⊤ := h.resolve_right (fun hh => hh hb0)
    have hs := (sourceRectValue_finite_iff A Y).mp ha
    have hA : A = 0 := by
      ext r s
      by_contra he
      obtain ⟨j,hj⟩ := hs r s he
      exact hj (by simp [hY])
    simp [hA, sourceRectValue_zero]
  by_cases hat : a = ⊤
  · simp only [a, b, hat, ENNReal.top_mul hb0, le_top]
  by_cases hbt : b = ⊤
  · simp only [a, b, hbt, ENNReal.mul_top ha0, le_top]
  have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  have hbreal : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hbt
  apply sourceRectValue_le_of_dual_norm_bound
  intro M hM
  have hy (j : Fin m) : ‖Y j ⊙ M‖ ≤ b.toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hbt).mp
    exact (sourceRectValue_dual_norm_le (Y j) Z M hM).trans
        (le_iSup (fun j => sourceRectValue (Y j) Z) j)
  let c : ℂ := (b.toReal : ℂ)⁻¹
  have hc : ‖c‖ = b.toReal⁻¹ := by simp [c, abs_of_pos hbpos]
  have hfeas : ∀ j, ‖Y j ⊙ (c • M)‖ ≤ 1 := by
    intro j
    rw [Matrix.hadamard_smul, norm_smul, hc]
    exact (mul_le_mul_of_nonneg_left (hy j) (inv_nonneg.mpr hbpos.le)).trans
      (by rw [inv_mul_cancel₀ hbpos.ne'])
  have hbound := sourceRectValue_dual_norm_le A Y (c • M) hfeas
  have he : ENNReal.ofReal ‖A ⊙ (c • M)‖ * b = ENNReal.ofReal ‖A ⊙ M‖ := by
    rw [Matrix.hadamard_smul, norm_smul, hc]
    calc
      ENNReal.ofReal (b.toReal⁻¹*‖A ⊙ M‖)*b =
          ENNReal.ofReal (b.toReal⁻¹*‖A ⊙ M‖)*ENNReal.ofReal b.toReal := by rw [hbreal]
      _ = ENNReal.ofReal ((b.toReal⁻¹*‖A ⊙ M‖)*b.toReal) :=
        (ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hbpos.le) (norm_nonneg _))).symm
      _ = ENNReal.ofReal ‖A ⊙ M‖ := by congr 1; field_simp
  rw [← he]
  exact mul_le_mul hbound le_rfl zero_le zero_le

/-- A block direct sum acts independently on the two components of a vector indexed by a sum
type. -/
theorem sourceDirectSum_mulVec {R S U V : Type}
    [Fintype S] [Fintype V] (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (v : QState (S ⊕ V)) :
    sourceDirectSum A B *ᵥ v = Sum.elim (A *ᵥ (v ∘ Sum.inl)) (B *ᵥ (v ∘ Sum.inr)) := by
  ext r
  cases r <;> simp [sourceDirectSum, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

/-- Embedding a vector into the left component of a direct sum with zero right component
preserves its Euclidean norm. -/
theorem sourceSumState_norm_left {S V : Type} [Fintype S] [Fintype V]
    (v : QState S) : ‖toEuclidean_fromVec (Sum.elim v (0 : QState V))‖ = ‖toEuclidean_fromVec v‖ := by
  have hs := rectangularSumState_norm_sq v (0 : QState V)
  have hz : ‖toEuclidean_fromVec (0 : QState V)‖^2 = 0 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp
  rw [hz,add_zero] at hs
  nlinarith [norm_nonneg (toEuclidean_fromVec (Sum.elim v (0 : QState V))),norm_nonneg (toEuclidean_fromVec v)]

/-- Embedding a vector into the right component of a direct sum with zero left component
preserves its Euclidean norm. -/
theorem sourceSumState_norm_right {S V : Type} [Fintype S] [Fintype V]
    (v : QState V) : ‖toEuclidean_fromVec (Sum.elim (0 : QState S) v)‖ = ‖toEuclidean_fromVec v‖ := by
  have hs := rectangularSumState_norm_sq (0 : QState S) v
  have hz : ‖toEuclidean_fromVec (0 : QState S)‖^2 = 0 := by
    rw [norm_toEuclidean_fromVec_sq]
    simp
  rw [hz,zero_add] at hs
  nlinarith [norm_nonneg (toEuclidean_fromVec (Sum.elim (0 : QState S) v)),norm_nonneg (toEuclidean_fromVec v)]

/-- The operator norm of a block direct sum is the maximum of the norms of its two blocks. -/
theorem sourceDirectSum_norm {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (A : Matrix R S ℂ) (B : Matrix U V ℂ) :
    ‖sourceDirectSum A B‖ = max ‖A‖ ‖B‖ := by
  have hsplit (v : QState (S ⊕ V)) :
      ‖toEuclidean_fromVec v‖^2 =
        ‖toEuclidean_fromVec (v ∘ Sum.inl)‖^2+‖toEuclidean_fromVec (v ∘ Sum.inr)‖^2 := by
    have hv : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by ext s; cases s <;> rfl
    conv_lhs => rw [hv]
    exact rectangularSumState_norm_sq _ _
  have houtput (v : QState (S ⊕ V)) :
      ‖toEuclidean_fromVec (sourceDirectSum A B *ᵥ v)‖^2 =
        ‖toEuclidean_fromVec (A *ᵥ (v ∘ Sum.inl))‖^2+
        ‖toEuclidean_fromVec (B *ᵥ (v ∘ Sum.inr))‖^2 := by
    rw [sourceDirectSum_mulVec, rectangularSumState_norm_sq]
  apply le_antisymm
  · apply l2_opNorm_le_of_mulVec_le (le_trans (norm_nonneg A) (le_max_left _ _))
    intro v
    have ha := (l2_norm_mulVec_fromVec_le A (v ∘ Sum.inl)).trans
      (mul_le_mul_of_nonneg_right (le_max_left ‖A‖ ‖B‖) (norm_nonneg _))
    have hb := (l2_norm_mulVec_fromVec_le B (v ∘ Sum.inr)).trans
      (mul_le_mul_of_nonneg_right (le_max_right ‖A‖ ‖B‖) (norm_nonneg _))
    have ha2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans (norm_nonneg A) (le_max_left _ _)) (norm_nonneg _))).mpr ha
    have hb2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans (norm_nonneg A) (le_max_left _ _)) (norm_nonneg _))).mpr hb
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (le_trans (norm_nonneg A) (le_max_left _ _)) (norm_nonneg _))).mp
    rw [houtput, mul_pow, hsplit]
    nlinarith only [ha2,hb2]
  · apply max_le
    · apply l2_opNorm_le_of_mulVec_le (norm_nonneg _)
      intro v
      let pad : QState (S ⊕ V) := Sum.elim v (fun _ => 0)
      have hin : ‖toEuclidean_fromVec pad‖ = ‖toEuclidean_fromVec v‖ := sourceSumState_norm_left v
      have hout : ‖toEuclidean_fromVec (sourceDirectSum A B *ᵥ pad)‖ = ‖toEuclidean_fromVec (A *ᵥ v)‖ := by
        rw [sourceDirectSum_mulVec]
        change ‖toEuclidean_fromVec (Sum.elim (A *ᵥ v) (B *ᵥ 0))‖ = _
        rw [Matrix.mulVec_zero]
        exact sourceSumState_norm_left _
      have hh := l2_norm_mulVec_fromVec_le (sourceDirectSum A B) pad
      simpa only [hin,hout] using! hh
    · apply l2_opNorm_le_of_mulVec_le (norm_nonneg _)
      intro v
      let pad : QState (S ⊕ V) := Sum.elim (fun _ => 0) v
      have hin : ‖toEuclidean_fromVec pad‖ = ‖toEuclidean_fromVec v‖ := sourceSumState_norm_right v
      have hout : ‖toEuclidean_fromVec (sourceDirectSum A B *ᵥ pad)‖ = ‖toEuclidean_fromVec (B *ᵥ v)‖ := by
        rw [sourceDirectSum_mulVec]
        change ‖toEuclidean_fromVec (Sum.elim (A *ᵥ 0) (B *ᵥ v))‖ = _
        rw [Matrix.mulVec_zero]
        exact sourceSumState_norm_right _
      have hh := l2_norm_mulVec_fromVec_le (sourceDirectSum A B) pad
      simpa only [hin,hout] using! hh

/-- Entrywise multiplication of a block direct sum depends only on the corresponding diagonal
blocks of the multiplier. -/
theorem sourceDirectSum_hadamard {R S U V : Type} (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (M : Matrix (R ⊕ U) (S ⊕ V) ℂ) :
    sourceDirectSum A B ⊙ M = sourceDirectSum (A ⊙ M.submatrix Sum.inl Sum.inl)
      (B ⊙ M.submatrix Sum.inr Sum.inr) := by
  ext r s
  cases r <;> cases s <;> simp [sourceDirectSum, Matrix.hadamard_apply]

/-- The rectangular filtered value of a direct sum with matching direct-sum filters is the
maximum of the two component values. -/
theorem sourceRectValue_directSum {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {n : ℕ} (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (Y : Fin n → Matrix R S ℂ) (Z : Fin n → Matrix U V ℂ) :
    sourceRectValue (sourceDirectSum A B) (fun j => sourceDirectSum (Y j) (Z j)) =
      max (sourceRectValue A Y) (sourceRectValue B Z) := by
  apply le_antisymm
  · apply sourceRectValue_le_of_dual_norm_bound
    intro M hM
    have hf (j : Fin n) := hM j
    simp only [sourceDirectSum_hadamard, sourceDirectSum_norm] at hf
    rw [sourceDirectSum_hadamard, sourceDirectSum_norm, ENNReal.ofReal_max]
    exact max_le_max (sourceRectValue_dual_norm_le A Y _ (fun j => (max_le_iff.mp (hf j)).1))
      (sourceRectValue_dual_norm_le B Z _ (fun j => (max_le_iff.mp (hf j)).2))
  · apply max_le
    · have hh := sourceRectValue_submatrix_le (sourceDirectSum A B)
        (fun j => sourceDirectSum (Y j) (Z j)) Sum.inl Sum.inl
      simpa [sourceDirectSum, Matrix.submatrix] using! hh
    · have hh := sourceRectValue_submatrix_le (sourceDirectSum A B)
        (fun j => sourceDirectSum (Y j) (Z j)) Sum.inr Sum.inr
      simpa [sourceDirectSum, Matrix.submatrix] using! hh

/-- The operator norm of a tensor product is the product of the operator norms. -/
theorem sourceTensor_norm {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (A : Matrix R S ℂ) (B : Matrix U V ℂ) : ‖sourceTensor A B‖ = ‖A‖*‖B‖ :=
  l2_norm_kronecker A B

/-- The entrywise product of two tensor products is the tensor product of the corresponding
entrywise products. -/
theorem sourceTensor_hadamard {R S U V : Type}
    (A M : Matrix R S ℂ) (B N : Matrix U V ℂ) :
    sourceTensor A B ⊙ sourceTensor M N = sourceTensor (A ⊙ M) (B ⊙ N) := by
  ext r s
  simp only [sourceTensor,Matrix.hadamard_apply]
  ring

/-- A sum over `Fin (n * m)` can be written as an iterated sum using `finProdFinEquiv`. -/
theorem sourceFinProd_sum {n m : ℕ} {α : Type} [AddCommMonoid α]
    (f : Fin n → Fin m → α) :
    (∑ i : Fin (n*m), f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) = ∑ j, ∑ k, f j k := by
  calc
    _ = ∑ p : Fin n × Fin m, f p.1 p.2 := finProdFinEquiv.symm.sum_comp (fun p => f p.1 p.2)
    _ = _ := Fintype.sum_prod_type _

/-- Reindexing by `finProdFinEquiv` expresses a sum over `Fin (n * m)` as a sum over `Fin n` and
`Fin m`. -/
theorem sourceFinProd_sum_apply {n m : ℕ} {α : Type} [AddCommMonoid α]
    (f : Fin (n*m) → α) : (∑ i, f i) = ∑ j : Fin n, ∑ k : Fin m, f (finProdFinEquiv (j,k)) := by
  calc
    _ = ∑ p : Fin n × Fin m, f (finProdFinEquiv p) := (finProdFinEquiv.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

/-- Tensoring two rectangular filtered certificates with nonnegative budgets gives a certificate
with the product budget. -/
theorem sourceRectCert_tensor {R S U V : Type} {n m : ℕ}
    {A : Matrix R S ℂ} {B : Matrix U V ℂ}
    {Y : Fin n → Matrix R S ℂ} {Z : Fin m → Matrix U V ℂ}
    {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hA : sourceRectCert n A Y a) (hB : sourceRectCert m B Z b) :
    sourceRectCert (n*m) (sourceTensor A B) (sourceFilterTensor Y Z) (a*b) := by
  obtain ⟨p,u,v,heA,hu,hv⟩ := hA
  obtain ⟨q,x,y,heB,hx,hy⟩ := hB
  apply sourceRectCert_of_finiteWitness
    (fun r j (k : Fin p × Fin q) => u r.1 (finProdFinEquiv.symm j).1 k.1 * x r.2 (finProdFinEquiv.symm j).2 k.2)
    (fun s j (k : Fin p × Fin q) => v s.1 (finProdFinEquiv.symm j).1 k.1 * y s.2 (finProdFinEquiv.symm j).2 k.2)
  · intro r s
    conv_rhs => rw [sourceFinProd_sum_apply (n := n) (m := m)]
    simp only [sourceTensor,sourceFilterTensor,Equiv.symm_apply_apply,Fintype.sum_prod_type,star_mul]
    rw [heA,heB,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    rw [show (Y j r.1 s.1 * ∑ k, star (u r.1 j k)*v s.1 j k)*
        (Z l r.2 s.2 * ∑ h, star (x r.2 l h)*y s.2 l h) =
        (Y j r.1 s.1*Z l r.2 s.2)*((∑ k, star (u r.1 j k)*v s.1 j k)*
        (∑ h, star (x r.2 l h)*y s.2 l h)) by ring, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro h _
    ring
  · intro r
    have hum := hu r.1
    have hxm := hx r.2
    simp only [norm_toEuclidean_fromVec_sq, ← Complex.normSq_eq_norm_sq] at hum hxm
    have he : (∑ j : Fin (n*m), ∑ k : Fin p × Fin q,
        Complex.normSq (u r.1 (finProdFinEquiv.symm j).1 k.1*x r.2 (finProdFinEquiv.symm j).2 k.2)) =
        (∑ j, ∑ k, Complex.normSq (u r.1 j k))*(∑ j, ∑ k, Complex.normSq (x r.2 j k)) := by
      rw [sourceFinProd_sum_apply (n := n) (m := m)]
      simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,Complex.normSq_mul]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul_sum]
    rw [he]
    exact mul_le_mul hum hxm
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ha
  · intro s
    have hvm := hv s.1
    have hym := hy s.2
    simp only [norm_toEuclidean_fromVec_sq, ← Complex.normSq_eq_norm_sq] at hvm hym
    have he : (∑ j : Fin (n*m), ∑ k : Fin p × Fin q,
        Complex.normSq (v s.1 (finProdFinEquiv.symm j).1 k.1*y s.2 (finProdFinEquiv.symm j).2 k.2)) =
        (∑ j, ∑ k, Complex.normSq (v s.1 j k))*(∑ j, ∑ k, Complex.normSq (y s.2 j k)) := by
      rw [sourceFinProd_sum_apply (n := n) (m := m)]
      simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,Complex.normSq_mul]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul_sum]
    rw [he]
    exact mul_le_mul hvm hym
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ha

/-- The product of the component rectangular filtered values is bounded by the value of the
tensor product with tensor-product filters. -/
theorem sourceRectValue_tensor_ge {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {n m : ℕ} (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    sourceRectValue A Y*sourceRectValue B Z ≤
      sourceRectValue (sourceTensor A B) (sourceFilterTensor Y Z) := by
  rw [(rectangularSchurDuality R S n A Y).1, (rectangularSchurDuality U V m B Z).1]
  unfold sourceRectDual
  rw [ENNReal.iSup_mul]
  apply iSup_le
  intro M
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro N
  have hf (j : Fin (n*m)) : ‖sourceFilterTensor Y Z j ⊙ sourceTensor M.val N.val‖ ≤ 1 := by
    unfold sourceFilterTensor
    rw [sourceTensor_hadamard,sourceTensor_norm]
    exact (mul_le_mul (M.property _) (N.property _) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hh := sourceRectValue_dual_norm_le (sourceTensor A B) (sourceFilterTensor Y Z)
    (sourceTensor M.val N.val) hf
  rw [sourceTensor_hadamard,sourceTensor_norm,ENNReal.ofReal_mul (norm_nonneg _)] at hh
  exact hh

/-- The rectangular filtered value is multiplicative under tensor products with tensor-product
filters. -/
theorem sourceRectValue_tensor {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {n m : ℕ} (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    sourceRectValue (sourceTensor A B) (sourceFilterTensor Y Z) =
      sourceRectValue A Y*sourceRectValue B Z := by
  apply le_antisymm _ (sourceRectValue_tensor_ge A B Y Z)
  by_cases ha0 : sourceRectValue A Y = 0
  · have hA : A = 0 := (sourceRectValue_zero_iff A Y).mp ha0
    have ht : sourceTensor A B = 0 := by ext r s; simp [sourceTensor,hA]
    simp [ht,ha0,sourceRectValue_zero]
  by_cases hb0 : sourceRectValue B Z = 0
  · have hB : B = 0 := (sourceRectValue_zero_iff B Z).mp hb0
    have ht : sourceTensor A B = 0 := by ext r s; simp [sourceTensor,hB]
    simp [ht,hb0,sourceRectValue_zero]
  by_cases hat : sourceRectValue A Y = ⊤
  · simp [hat,ENNReal.top_mul hb0]
  by_cases hbt : sourceRectValue B Z = ⊤
  · simp [hbt,ENNReal.mul_top ha0]
  have hAc : sourceRectCert n A Y (sourceRectValue A Y).toReal :=
    ((rectangularBudgetRealization R S n A Y).2.1 _ ENNReal.toReal_nonneg).mp
      (le_of_eq (ENNReal.ofReal_toReal hat).symm)
  have hBc : sourceRectCert m B Z (sourceRectValue B Z).toReal :=
    ((rectangularBudgetRealization U V m B Z).2.1 _ ENNReal.toReal_nonneg).mp
      (le_of_eq (ENNReal.ofReal_toReal hbt).symm)
  have hh := sourceRectValue_le_of_cert
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (sourceRectCert_tensor ENNReal.toReal_nonneg ENNReal.toReal_nonneg hAc hBc)
  simpa only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hat,ENNReal.ofReal_toReal hbt] using! hh

/-- The rectangular filtered value satisfies the bundled composition bound, direct-sum formula,
and tensor multiplicativity from [LeeEtAl2011]. -/
theorem filteredNormCompositionAndProducts : FilteredNormCompositionAndProducts := by
  refine ⟨?_,?_,?_⟩
  · intro R S _ _ _ _ n m A Y Z h
    exact sourceRectValue_composition A Y Z h
  · intro R S U V _ _ _ _ _ _ _ _ n A B Y Z
    exact sourceRectValue_directSum A B Y Z
  · intro R S U V _ _ _ _ _ _ _ _ n m A B Y Z
    exact sourceRectValue_tensor A B Y Z

end Qatlib.Concepts.GramQueryCore.FilteredNorm
