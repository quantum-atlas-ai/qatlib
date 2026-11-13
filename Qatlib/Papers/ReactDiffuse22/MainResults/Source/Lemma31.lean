/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactDiffuse22.MainResults.Model.SourceModel
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Batteries.Tactic.Lint

set_option backward.isDefEq.respectTransparency false

/-!
# Operator Norm and Exponential Decay Bounds for Carleman Linearization Blocks

This module formalizes Lemma 3.1: for the Carleman linearization of a polynomial
reaction-diffusion system, the cross-coupling block `A_j^{j+M-1}` has both `ℓ₂`
and `ℓ_∞` operator norms bounded by `j |b|`, and the matrix exponential of the
Kronecker-sum diagonal block `t A_j^j` decays at rate `exp (j λ₁ t)` when `F₁`
is symmetric with largest eigenvalue `λ₁ < 0`.

## Main statements

* `source_lemma31`: combined `ℓ₂` cross-block bound, `ℓ_∞` cross-block bound,
  and spectral decay bound `‖exp (t • A_j^j)‖₂ ≤ exp (j λ₁ t)`.
* `source_lemma31_inf`: standalone `ℓ_∞` row-sum bound for `carlemanCrossBlock`.

## References

* [Jin, Liu, and Yu, 2022][JinLiuYu2022ReactDiffuse], Section 3, Lemma 3.1,
  Eqs. (3.4)--(3.5), p. 12.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ReactDiffuse22.MainResults.Source
open Qatlib.Papers.ReactDiffuse22.MainResults

/-- The input index receiving output slot `e` under the `ν`-th placement. -/
private def sIdx (M j : ℕ) (_hM : 1 ≤ M) (ν : Fin j) (e : Fin j) : Fin (j + (M - 1)) :=
  ⟨if e.val < ν.val then e.val else e.val + (M - 1), by
    have he := e.isLt
    have hν := ν.isLt
    split_ifs <;> omega⟩

/-- The unique input tuple making the `ν`-th summand of the cross block equal to `b`. -/
private def rowInput {n d : ℕ} (M j : ℕ) (_hM : 1 ≤ M)
    (x : TensorIndex (GridIndex n d) j) (ν : Fin j) :
    TensorIndex (GridIndex n d) (j + (M - 1)) :=
  fun p =>
    if _h1 : p.val < ν.val then x ⟨p.val, by
      have hp := p.isLt
      have hν := ν.isLt
      omega⟩
    else if _h2 : p.val < ν.val + M then x ν
    else x ⟨p.val - (M - 1), by
      have hp := p.isLt
      have hν := ν.isLt
      omega⟩

/-- The `ν`-th summand of the cross block. -/
private def crossTerm {n d : ℕ} (b : ℝ) (M j : ℕ) (hM : 1 ≤ M)
    (x : TensorIndex (GridIndex n d) j) (ν : Fin j)
    (y : TensorIndex (GridIndex n d) (j + (M - 1))) : ℝ :=
  if (∀ e : Fin j, e ≠ ν → x e = y (sIdx M j hM ν e)) then
    FMMatrix (n := n) (d := d) b M (x ν)
      (fun k : Fin M => y ⟨ν.val + k.val, by
        have hν := ν.isLt
        have hk := k.isLt
        omega⟩)
  else 0

/-- On positions before the window, `rowInput` agrees with `x` after the shift. -/
private lemma rowInput_outside_left {n d : ℕ} {M j : ℕ} (hM : 1 ≤ M)
    {x : TensorIndex (GridIndex n d) j} {ν : Fin j} {p : Fin (j + (M - 1))}
    (hp : p.val < ν.val) :
    rowInput M j hM x ν p = x ⟨p.val, by
      have _hp' := p.isLt
      have _hν := ν.isLt
      omega⟩ := by
  simp [rowInput, hp]

/-- On window positions, `rowInput` is constantly `x ν`. -/
private lemma rowInput_window {n d : ℕ} {M j : ℕ} (hM : 1 ≤ M)
    {x : TensorIndex (GridIndex n d) j} {ν : Fin j} {p : Fin (j + (M - 1))}
    (hp1 : ¬ p.val < ν.val) (hp2 : p.val < ν.val + M) :
    rowInput M j hM x ν p = x ν := by
  simp [rowInput, hp1, hp2]

/-- On positions after the window, `rowInput` agrees with `x` after the shift. -/
private lemma rowInput_outside_right {n d : ℕ} {M j : ℕ} (hM : 1 ≤ M)
    {x : TensorIndex (GridIndex n d) j} {ν : Fin j} {p : Fin (j + (M - 1))}
    (hp : ¬ p.val < ν.val + M) :
    rowInput M j hM x ν p = x ⟨p.val - (M - 1), by
      have _hp' := p.isLt
      have _hν := ν.isLt
      omega⟩ := by
  have hp1 : ¬ p.val < ν.val := by omega
  simp [rowInput, hp1, hp]

/-- The shifted index below the window is the original index. -/
private lemma sIdx_left_eq {M j : ℕ} (hM : 1 ≤ M) {ν : Fin j} {e : Fin j}
    (he : e.val < ν.val) :
    sIdx M j hM ν e = ⟨e.val, by
      have _he' := e.isLt
      have _hν := ν.isLt
      omega⟩ := by
  apply Fin.ext
  simp [sIdx, he]

/-- The shifted index above the window is shifted by `M - 1`. -/
private lemma sIdx_right_eq {M j : ℕ} (hM : 1 ≤ M) {ν : Fin j} {e : Fin j}
    (he : ¬ e.val < ν.val) :
    sIdx M j hM ν e = ⟨e.val + (M - 1), by
      have _he' := e.isLt
      have _hν := ν.isLt
      omega⟩ := by
  apply Fin.ext
  simp [sIdx, he]

/-- The `ν`-th summand is `b` exactly at the unique input row. -/
private lemma crossTerm_eq {n d : ℕ} (b : ℝ) (M j : ℕ) (hM : 1 ≤ M)
    (x : TensorIndex (GridIndex n d) j) (ν : Fin j)
    (y : TensorIndex (GridIndex n d) (j + (M - 1))) :
    crossTerm (n := n) (d := d) b M j hM x ν y
      = if y = rowInput M j hM x ν then b else 0 := by
  unfold crossTerm
  by_cases hy : y = rowInput M j hM x ν
  · subst hy
    have hcond : ∀ e : Fin j, e ≠ ν →
        x e = rowInput M j hM x ν (sIdx M j hM ν e) := by
      intro e _he
      by_cases hlt : e.val < ν.val
      · rw [sIdx_left_eq hM hlt]
        exact (rowInput_outside_left (x := x) (ν := ν)
          (p := ⟨e.val, by
            have _he' := e.isLt
            have _hν := ν.isLt
            omega⟩) hM hlt).symm
      · rw [sIdx_right_eq hM hlt]
        have hge' : ¬ e.val + (M - 1) < ν.val + M := by omega
        rw [rowInput_outside_right (x := x) (ν := ν) hM hge']
        congr 1
        apply Fin.ext
        dsimp
        omega
    have hwin : (fun k : Fin M => rowInput M j hM x ν ⟨ν.val + k.val, by
          have _hν := ν.isLt
          have _hk := k.isLt
          omega⟩) = fun _ => x ν := by
      funext k
      exact rowInput_window hM (by simp) (by
        have _hk' := k.isLt
        dsimp
        omega)
    rw [ite_eq_left_iff.mpr fun hnot => False.elim (hnot hcond)]
    simp [FMMatrix, hwin]
  · by_cases hc : (∀ e : Fin j, e ≠ ν → x e = y (sIdx M j hM ν e))
    · have hnotwin : ¬ (∀ k : Fin M, y ⟨ν.val + k.val, by
          have _hν := ν.isLt
          have _hk := k.isLt
          omega⟩ = x ν) := by
        intro hwin
        apply hy
        funext p
        by_cases hp : p.val < ν.val
        · rw [rowInput_outside_left (x := x) (ν := ν) hM hp]
          have he : (⟨p.val, by
              have _hp' := p.isLt
              have _hν := ν.isLt
              omega⟩ : Fin j) ≠ ν := by
            intro h
            have hv := congrArg Fin.val h
            dsimp at hv
            omega
          have h := hc ⟨p.val, by
              have _hp' := p.isLt
              have _hν := ν.isLt
              omega⟩ he
          have hsp : sIdx M j hM ν ⟨p.val, by
              have _hp' := p.isLt
              have _hν := ν.isLt
              omega⟩ = p := by
            apply Fin.ext
            rw [sIdx_left_eq hM hp]
          rw [hsp] at h
          exact h.symm
        · by_cases hp2 : p.val < ν.val + M
          · rw [rowInput_window hM hp hp2]
            have hklt : p.val - ν.val < M := by omega
            obtain ⟨k, hk⟩ : ∃ k : Fin M, ν.val + k.val = p.val := by
              refine ⟨⟨p.val - ν.val, hklt⟩, ?_⟩
              show ν.val + (p.val - ν.val) = p.val
              omega
            have h := hwin k
            have hidx : (⟨ν.val + k.val, by
                have _hν := ν.isLt
                have _hk' := k.isLt
                omega⟩ : Fin (j + (M - 1))) = p := Fin.ext hk
            rw [hidx] at h
            exact h
          · rw [rowInput_outside_right (x := x) (ν := ν) hM hp2]
            have he : (⟨p.val - (M - 1), by
                have _hp' := p.isLt
                have _hν := ν.isLt
                omega⟩ : Fin j) ≠ ν := by
              intro h
              have hv := congrArg Fin.val h
              dsimp at hv
              omega
            have h := hc ⟨p.val - (M - 1), by
                have _hp' := p.isLt
                have _hν := ν.isLt
                omega⟩ he
            have hsp : sIdx M j hM ν ⟨p.val - (M - 1), by
                have _hp' := p.isLt
                have _hν := ν.isLt
                omega⟩ = p := by
              apply Fin.ext
              rw [sIdx_right_eq hM (by
                dsimp
                omega)]
              dsimp
              omega
            rw [hsp] at h
            exact h.symm
      rw [ite_eq_left_iff.mpr fun hnot => False.elim (hnot hc)]
      simp [FMMatrix, hy, hnotwin]
    · simp [hy, hc]

/-- The cross block is the sum of its `ν`-th summands. -/
private lemma crossBlock_apply {n d : ℕ} (b : ℝ) (M j : ℕ) (hM : 1 ≤ M)
    (x : TensorIndex (GridIndex n d) j)
    (y : TensorIndex (GridIndex n d) (j + (M - 1))) :
    carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j hM x y
      = ∑ ν, crossTerm (n := n) (d := d) b M j hM x ν y := by
  rfl

/-- Row-sum bound for the cross block. -/
private lemma cross_row_sum {n d : ℕ} (b : ℝ) (M j : ℕ) (hM : 1 ≤ M)
    (x : TensorIndex (GridIndex n d) j) :
    ∑ y, |carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j hM x y| ≤
      (j : ℝ) * |b| := by
  calc
    ∑ y, |carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j hM x y|
        = ∑ y, |∑ ν, crossTerm (n := n) (d := d) b M j hM x ν y| := by
          apply Finset.sum_congr rfl
          intro y _
          rw [crossBlock_apply]
    _ ≤ ∑ y, ∑ ν, |crossTerm (n := n) (d := d) b M j hM x ν y| := by
          apply Finset.sum_le_sum
          intro y _
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ν, ∑ y, |crossTerm (n := n) (d := d) b M j hM x ν y| := Finset.sum_comm
    _ = ∑ _ν : Fin j, |b| := by
          apply Finset.sum_congr rfl
          intro ν _
          rw [show (∑ y, |crossTerm (n := n) (d := d) b M j hM x ν y|)
              = ∑ y, (if y = rowInput M j hM x ν then |b| else 0) from by
                apply Finset.sum_congr rfl
                intro y _
                rw [crossTerm_eq]
                split_ifs <;> simp]
          simp
    _ = (j : ℝ) * |b| := by simp

/-- The `ℓ_∞` operator-norm bound (3.4) for the cross block. -/
private lemma cross_opNormInf_le {n d : ℕ} [Nonempty (GridIndex n d)]
    (b : ℝ) (M j : ℕ) (hM : 1 ≤ M) :
    opNormInf (carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j hM) ≤
      (j : ℝ) * |b| := by
  unfold opNormInf
  refine Finset.sup'_le _ _ ?_
  intro x _
  exact cross_row_sum b M j hM x

/-- **Lemma 3.1, `ℓ_∞` bound (3.4)**: the Carleman cross block `A_j^{j+M-1}` has
`ℓ_∞` operator norm at most `j |b|`. -/
theorem source_lemma31_inf {n d : ℕ} [Nonempty (GridIndex n d)]
    (b : ℝ) (M j : ℕ) (hM : 2 ≤ M) :
    opNormInf (carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j (by omega)) ≤
      (j : ℝ) * |b| :=
  cross_opNormInf_le b M j (by omega)

/-- Each placement retains every output coordinate. -/
private lemma rowInput_injective {n d M j : ℕ} (hM : 1 ≤ M) (ν : Fin j) :
    Function.Injective (fun x : TensorIndex (GridIndex n d) j => rowInput M j hM x ν) := by
  intro x z hx
  funext e
  by_cases he : e.val < ν.val
  · have h := congrFun hx ⟨e.val, by omega⟩
    simpa [rowInput, he] using h
  · by_cases heq : e = ν
    · subst e
      have h := congrFun hx ⟨ν.val, by omega⟩
      have hp : ν.val < ν.val + M := by omega
      simpa [rowInput, hp] using h
    · have h := congrFun hx ⟨e.val + (M - 1), by have := e.isLt; omega⟩
      have hp : ¬ e.val + (M - 1) < ν.val + M := by
        have : e.val ≠ ν.val := fun h => heq (Fin.ext h)
        omega
      have hp' : ¬ e.val + (M - 1) < ν.val := by omega
      simpa [rowInput, hp, hp'] using h

/-- An individual placement is a scaled restriction to distinct coordinates. -/
private lemma crossTerm_norm_le {n d : ℕ} (b : ℝ) (M j : ℕ) (hM : 1 ≤ M)
    (ν : Fin j) :
    ‖Matrix.of (crossTerm (n := n) (d := d) b M j hM · ν ·)‖ ≤ |b| := by
  classical
  let A := Matrix.of (crossTerm (n := n) (d := d) b M j hM · ν ·)
  have hAA : A * Aᴴ = b ^ 2 • (1 : Matrix (TensorIndex (GridIndex n d) j) _ ℝ) := by
    ext x z
    simp only [A, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      crossTerm_eq, star_trivial, ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      (rowInput_injective hM ν).eq_iff, eq_comm (a := x), Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp_all [pow_two]
  have hnorm : ‖A‖ * ‖A‖ ≤ |b| * |b| := by
    have heq := Matrix.l2_opNorm_conjTranspose_mul_self Aᴴ
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, hAA,
      norm_smul] at heq
    rw [← heq]
    have h1 : ‖(1 : Matrix (TensorIndex (GridIndex n d) j)
        (TensorIndex (GridIndex n d) j) ℝ)‖ ≤ 1 := by
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
    calc
      ‖b ^ 2‖ * ‖(1 : Matrix (TensorIndex (GridIndex n d) j) _ ℝ)‖ ≤ ‖b ^ 2‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = |b| * |b| := by simp [Real.norm_eq_abs, pow_two]
  exact (sq_le_sq₀ (norm_nonneg A) (abs_nonneg b)).mp (by simpa [pow_two] using hnorm)

/-- Entrywise tensor products, with one matrix for each tensor coordinate. -/
private def tensorMatrix {ι : Type} (j : ℕ) (A : Fin j → Matrix ι ι ℝ) :
    Matrix (TensorIndex ι j) (TensorIndex ι j) ℝ :=
  Matrix.of fun x y => ∏ ν, A ν (x ν) (y ν)

/-- Multiplication factors coordinatewise in a tensor product. -/
private lemma tensorMatrix_mul {ι : Type} [Fintype ι] (j : ℕ)
    (A B : Fin j → Matrix ι ι ℝ) :
    tensorMatrix j (fun ν => A ν * B ν) = tensorMatrix j A * tensorMatrix j B := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- The tensor product of identities is the identity. -/
private lemma tensorMatrix_one {ι : Type} [DecidableEq ι] (j : ℕ) :
    tensorMatrix j (fun _ => (1 : Matrix ι ι ℝ)) = 1 := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole]
  simp only [← funext_iff]

/-- Taking adjoints commutes with tensor products. -/
private lemma tensorMatrix_star {ι : Type} (j : ℕ) (A : Fin j → Matrix ι ι ℝ) :
    tensorMatrix j (fun ν => star (A ν)) = star (tensorMatrix j A) := by
  ext x y
  simp [tensorMatrix, Matrix.star_apply]

/-- Diagonal tensor factors give the products of their diagonal entries. -/
private lemma tensorMatrix_diagonal {ι : Type} [DecidableEq ι] (j : ℕ)
    (v : Fin j → ι → ℝ) :
    tensorMatrix j (fun ν => Matrix.diagonal (v ν)) =
      Matrix.diagonal (fun x => ∏ ν, v ν (x ν)) := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.of_apply, Matrix.diagonal_apply, Fintype.prod_ite_zero]
  simp only [← funext_iff]

/-- A single nonidentity tensor factor is a coordinate placement. -/
private lemma tensorMatrix_placement {ι : Type} [DecidableEq ι] (j : ℕ)
    (A : Matrix ι ι ℝ) (ν : Fin j) (x y : TensorIndex ι j) :
    tensorMatrix j (fun e => if e = ν then A else 1) x y =
      if (∀ e : Fin j, e ≠ ν → x e = y e) then A (x ν) (y ν) else 0 := by
  classical
  unfold tensorMatrix
  simp only [Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ν)]
  simp only [ite_true]
  have hp : (∏ e ∈ Finset.univ.erase ν,
      (if e = ν then A else 1) (x e) (y e)) =
      if (∀ e : Fin j, e ≠ ν → x e = y e) then 1 else 0 := by
    calc
      _ = ∏ e ∈ Finset.univ.erase ν, (if x e = y e then (1 : ℝ) else 0) := by
        apply Finset.prod_congr rfl
        intro e he
        simp [Finset.ne_of_mem_erase he, Matrix.one_apply]
      _ = _ := by simp only [Finset.prod_boole, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [hp]
  split_ifs <;> simp

/-- The diagonal block is the sum of its single-coordinate tensor placements. -/
private lemma diagBlock_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (j : ℕ) :
    carlemanDiagBlock A j = ∑ ν : Fin j,
      tensorMatrix j (fun e => if e = ν then A else 1) := by
  ext x y
  simp [carlemanDiagBlock, Matrix.sum_apply, tensorMatrix_placement]

/-- Tensor powers of unitary matrices are unitary. -/
private def tensorUnitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (j : ℕ) :
    unitary (Matrix (TensorIndex ι j) (TensorIndex ι j) ℝ) :=
  ⟨tensorMatrix j (fun _ => (U : Matrix ι ι ℝ)), by
    constructor
    · rw [← tensorMatrix_star, ← tensorMatrix_mul]
      simp only [Unitary.coe_star_mul_self, tensorMatrix_one]
    · rw [← tensorMatrix_star, ← tensorMatrix_mul]
      simp only [Unitary.mul_star_self_of_mem U.prop, tensorMatrix_one]⟩

/-- Unitary diagonalization lifts from a matrix to its Kronecker sum. -/
private lemma diagBlock_diagonalization {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (μ : ι → ℝ) (j : ℕ) :
    carlemanDiagBlock (Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal μ)) j =
      Unitary.conjStarAlgAut ℝ _ (tensorUnitary U j)
        (Matrix.diagonal (fun x => ∑ ν : Fin j, μ (x ν))) := by
  classical
  have hplace (ν : Fin j) :
      tensorMatrix j (fun e => if e = ν then
        Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal μ) else 1) =
      Unitary.conjStarAlgAut ℝ _ (tensorUnitary U j)
        (Matrix.diagonal (fun x => μ (x ν))) := by
    have hd : Matrix.diagonal (fun x : TensorIndex ι j => μ (x ν)) =
        tensorMatrix j (fun e => if e = ν then Matrix.diagonal μ else 1) := by
      have he : (fun e => if e = ν then Matrix.diagonal μ else (1 : Matrix ι ι ℝ)) =
          fun e => Matrix.diagonal (fun i => if e = ν then μ i else 1) := by
        funext e
        split_ifs <;> simp
      rw [he, tensorMatrix_diagonal]
      simp only [Fintype.prod_ite_eq']
    rw [hd, Unitary.conjStarAlgAut_apply]
    change _ = tensorMatrix j (fun _ => (U : Matrix ι ι ℝ)) * _ *
      star (tensorMatrix j (fun _ => (U : Matrix ι ι ℝ)))
    rw [← tensorMatrix_star, ← tensorMatrix_mul, ← tensorMatrix_mul]
    congr 1
    funext e
    split_ifs <;> simp
  rw [diagBlock_eq_sum]
  simp_rw [hplace]
  rw [← map_sum]
  congr 1
  ext x y
  by_cases h : x = y <;> simp [Matrix.sum_apply, h]

/-- The exponential bound obtained by lifting the eigenvector unitary. -/
private lemma diagBlock_exp_norm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (lam : ℝ)
    (hμ : ∀ i, hA.eigenvalues i ≤ lam) (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • carlemanDiagBlock A j)‖ ≤ Real.exp ((j : ℝ) * lam * t) := by
  classical
  let U := tensorUnitary hA.eigenvectorUnitary j
  let v : TensorIndex ι j → ℝ := fun x => ∑ ν : Fin j, hA.eigenvalues (x ν)
  have hdiag : carlemanDiagBlock A j =
      Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal v) := by
    conv_lhs => rw [hA.spectral_theorem]
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      diagBlock_diagonalization hA.eigenvectorUnitary hA.eigenvalues j
  have hexp (B : Matrix (TensorIndex ι j) (TensorIndex ι j) ℝ) :
      NormedSpace.exp (Unitary.conjStarAlgAut ℝ _ U B) =
        Unitary.conjStarAlgAut ℝ _ U (NormedSpace.exp B) :=
    Matrix.exp_units_conj (Unitary.toUnits U) B
  rw [hdiag, ← map_smul, ← Matrix.diagonal_smul, hexp, Matrix.exp_diagonal,
    Unitary.conjStarAlgAut_apply, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop),
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun x => ?_
  rw [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs,
    ← Real.exp_eq_exp_ℝ, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hv : v x ≤ (j : ℝ) * lam := by
    calc
      v x ≤ ∑ _ν : Fin j, lam := Finset.sum_le_sum fun ν _ => hμ (x ν)
      _ = _ := by simp
  nlinarith

/-- **Lemma 3.1**: for all `j ≥ 1`, `M ≥ 2`, and `t ≥ 0`, both the `ℓ₂` and `ℓ_∞`
operator norms of `A_j^{j+M-1}` are at most `j |b|`, and `‖exp (t • A_j^j)‖₂ ≤ exp (j λ₁ t)`
when `F₁` is symmetric with largest eigenvalue `λ₁ < 0`. -/
theorem source_lemma31
    {n d : ℕ} [Nonempty (GridIndex n d)]
    (D a b lam1 : ℝ) (Dh : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (M j : ℕ) (hM : 2 ≤ M) (hj : 1 ≤ j)
    (hF1sym : (F1Matrix D a Dh).IsSymm)
    (hspec : IsLargestEigenvalue (F1Matrix D a Dh) lam1) (hlam : lam1 < 0)
    (hFM : opNorm2 (FMMatrix (n := n) (d := d) b M) ≤ |b|)
    (t : ℝ) (ht : 0 ≤ t) :
    opNorm2 (carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j (by omega)) ≤
        (j : ℝ) * |b| ∧
    opNormInf (carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j (by omega)) ≤
        (j : ℝ) * |b| ∧
    opNorm2 (NormedSpace.exp (t • carlemanDiagBlock (F1Matrix D a Dh) j)) ≤
        Real.exp ((j : ℝ) * lam1 * t) := by
  refine (And.left ⟨?_, (⟨hj, hlam, hFM⟩ :
    1 ≤ j ∧ lam1 < 0 ∧ opNorm2 (FMMatrix (n := n) (d := d) b M) ≤ |b|)⟩)
  refine ⟨?_, source_lemma31_inf b M j hM, ?_⟩
  · change ‖carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j (by omega)‖ ≤ _
    have hsum : carlemanCrossBlock M (FMMatrix (n := n) (d := d) b M) j (by omega) =
        ∑ ν : Fin j, Matrix.of (crossTerm (n := n) (d := d) b M j (by omega) · ν ·) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.of_apply, crossBlock_apply]
    rw [hsum]
    calc
      _ ≤ ∑ ν : Fin j, ‖Matrix.of (crossTerm (n := n) (d := d) b M j (by omega) · ν ·)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ν : Fin j, |b| := Finset.sum_le_sum fun ν _ => crossTerm_norm_le b M j (by omega) ν
      _ = _ := by simp
  · have hF1 : (F1Matrix D a Dh).IsHermitian := hF1sym
    apply diagBlock_exp_norm_le _ hF1 lam1 ?_ j t ht
    intro i
    exact hspec.2 _ _
      ((WithLp.ofLp_eq_zero 2).ne.mpr (hF1.eigenvectorBasis.orthonormal.ne_zero i))
      (hF1.mulVec_eigenvectorBasis i)

end Qatlib.Papers.ReactDiffuse22.MainResults.Source

#lint only unusedArguments
