/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.GramReadout

/-!
# Indexed column loading and Gram marginals

A `ColumnOracle` supplies normalized columns with nonnegative weights whose squares sum to one.
The loaded state's index marginal equals the transpose of `paperMatrix`; real columns or
conjugated access give direct access to `paperMatrix`, and list based loading passes record
explicit load counts. See [LloydMohseniRebentrost2014].

## Main statements

* `marginal_eq_paperMatrix_transpose`: The index marginal of the loaded state equals the
  transpose of `paperMatrix O`.
* `conjugateAccess_marginal`: The index marginal prepared using conjugated columns equals the
  original paper Gram matrix.
* `copyLoad_length`: The concatenation of `n` loading passes on `m` columns has length `n * m`.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCA14.InputAccess

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.CopyEvolution.GramReadout
  (gramColumn gramFirstRegisterDensity gramMatrix gramState)
open Qatlib.Foundations.PureStateMath.Reflection (outerProduct)
open Qatlib.Foundations.PureStateMath
  (IsDensityOperator Normalized Operator PartialTrace QState)

/-- Indexed normalized column states with nonnegative column norms whose squared sum is one. -/
structure ColumnOracle (m d : ℕ) where

  col : Fin m → QState (Fin d)

  normalized : ∀ i, Normalized (col i)

  norm : Fin m → ℝ

  norm_nonneg : ∀ i, 0 ≤ norm i

  norm_sq_sum : (∑ i, (norm i) ^ 2) = 1

/-- The weighted Gram matrix with entry `norm i * norm j * ⟨col i, col j⟩`. -/
noncomputable def paperMatrix {m d : ℕ} (O : ColumnOracle m d) : Operator m :=
  fun i j =>
    ((O.norm i : ℂ) * (O.norm j : ℂ)) *
      ∑ x, (starRingEnd ℂ) (O.col i x) * O.col j x

/-- The weighted joint index and column state `gramState O.col O.norm`. -/
noncomputable def loadState {m d : ℕ} (O : ColumnOracle m d) :
    QState (Fin m × Fin d) :=
  gramState O.col O.norm

/-- The index register marginal of the outer product of `loadState O`. -/
noncomputable def marginal {m d : ℕ} (O : ColumnOracle m d) : Operator m :=
  PartialTrace (outerProduct (loadState O))

/-- The joint state prepared from a `ColumnOracle` is normalized. -/
theorem loadState_normalized {m d : ℕ} (O : ColumnOracle m d) :
    Normalized (loadState O) :=
  (gramFirstRegisterDensity m d O.col O.normalized O.norm O.norm_nonneg
    O.norm_sq_sum).1

/-- The index marginal of the loaded state equals `gramMatrix O.col O.norm`. See
[LloydMohseniRebentrost2014]. -/
theorem marginal_eq_gramMatrix {m d : ℕ} (O : ColumnOracle m d) :
    marginal O = gramMatrix O.col O.norm :=
  (gramFirstRegisterDensity m d O.col O.normalized O.norm O.norm_nonneg
    O.norm_sq_sum).2.1

/-- The index marginal of the loaded state equals the transpose of `paperMatrix O`. -/
theorem marginal_eq_paperMatrix_transpose {m d : ℕ} (O : ColumnOracle m d) :
    marginal O = (paperMatrix O)ᵀ := by
  rw [marginal_eq_gramMatrix]
  ext i j
  simp only [gramMatrix, gramColumn, paperMatrix, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, map_mul, Complex.conj_ofReal,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The index marginal of a loaded column state is a density operator. -/
theorem marginal_isDensity {m d : ℕ} (O : ColumnOracle m d) :
    IsDensityOperator (marginal O) := by
  rw [marginal_eq_gramMatrix]
  exact (gramFirstRegisterDensity m d O.col O.normalized O.norm O.norm_nonneg
    O.norm_sq_sum).2.2

/-- The real diagonal entry of the marginal at `i` equals the square of the column norm at `i`. -/
theorem marginal_diagonal {m d : ℕ} (O : ColumnOracle m d) (i : Fin m) :
    ((marginal O) i i).re = (O.norm i) ^ 2 := by
  rw [marginal_eq_paperMatrix_transpose, Matrix.transpose_apply]
  have hsum : (∑ x, (starRingEnd ℂ) (O.col i x) * O.col i x) = 1 := by
    have hcast :
        (∑ x, (starRingEnd ℂ) (O.col i x) * O.col i x) =
          ((∑ x, ‖O.col i x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_comm]
      simpa only [Complex.normSq_eq_norm_sq] using Complex.mul_conj (O.col i x)
    rw [hcast, O.normalized i]
    norm_num
  simp only [paperMatrix, hsum, mul_one]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Column oracles with equal column states and weights prepare the same joint state. -/
theorem loadState_congr {m d : ℕ} {O₁ O₂ : ColumnOracle m d}
    (hcol : ∀ i, O₁.col i = O₂.col i) (hnorm : ∀ i, O₁.norm i = O₂.norm i) :
    loadState O₁ = loadState O₂ := by
  funext p
  simp only [loadState, gramState, hcol p.1, hnorm p.1]

/-- Equality of a marginal diagonal entry implies equality of the corresponding nonnegative
column norms. -/
theorem norm_eq_of_marginal_diagonal {m d : ℕ} {O₁ O₂ : ColumnOracle m d}
    (i : Fin m) (h : (marginal O₁) i i = (marginal O₂) i i) :
    O₁.norm i = O₂.norm i := by
  have h₁ := marginal_diagonal O₁ i
  have h₂ := marginal_diagonal O₂ i
  rw [h] at h₁
  have hsq : (O₁.norm i) ^ 2 = (O₂.norm i) ^ 2 := by rw [← h₁, h₂]
  have hfac : (O₁.norm i - O₂.norm i) * (O₁.norm i + O₂.norm i) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith [O₁.norm_nonneg i, O₂.norm_nonneg i]

/-- The property that every column amplitude has zero imaginary part. -/
def RealColumns {m d : ℕ} (O : ColumnOracle m d) : Prop :=
  ∀ i x, (O.col i x).im = 0

/-- For real column amplitudes, `paperMatrix O` equals its transpose. -/
theorem paperMatrix_real_eq {m d : ℕ} (O : ColumnOracle m d) (hR : RealColumns O) :
    paperMatrix O = (paperMatrix O)ᵀ := by
  have hconj : ∀ (i : Fin m) (x : Fin d),
      (starRingEnd ℂ) (O.col i x) = O.col i x := by
    intro i x
    apply Complex.ext
    · simp [Complex.conj_re]
    · simp [Complex.conj_im, hR i x]
  ext i j
  simp only [paperMatrix, Matrix.transpose_apply]
  have hs : (∑ x, (starRingEnd ℂ) (O.col i x) * O.col j x) =
      (∑ x, (starRingEnd ℂ) (O.col j x) * O.col i x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hconj i x, hconj j x]
    ring
  rw [hs]
  ring

/-- The weighted paper Gram matrix is a density operator when all column amplitudes are real. -/
theorem paperMatrix_isDensity_of_real {m d : ℕ} (O : ColumnOracle m d)
    (hR : RealColumns O) : IsDensityOperator (paperMatrix O) := by
  rw [paperMatrix_real_eq O hR, ← marginal_eq_paperMatrix_transpose]
  exact marginal_isDensity O

/-- The column oracle obtained by conjugating every amplitude and preserving the column norms. -/
noncomputable def conjugateOracle {m d : ℕ} (O : ColumnOracle m d) :
    ColumnOracle m d where
  col i := fun x => (starRingEnd ℂ) (O.col i x)
  normalized i := by
    have hnorm : ∀ x : Fin d, ‖(starRingEnd ℂ) (O.col i x)‖ = ‖O.col i x‖ :=
      fun x => by simp
    simp only [Normalized] at O ⊢
    rw [show (∑ x : Fin d, ‖(starRingEnd ℂ) (O.col i x)‖ ^ 2) =
      (∑ x : Fin d, ‖O.col i x‖ ^ 2) from Finset.sum_congr rfl (by
        intro x _; rw [hnorm x])]
    exact O.normalized i
  norm := O.norm
  norm_nonneg := O.norm_nonneg
  norm_sq_sum := O.norm_sq_sum

/-- Conjugating the column oracle transposes its paper Gram matrix. -/
theorem paperMatrix_conjugateOracle {m d : ℕ} (O : ColumnOracle m d) :
    paperMatrix (conjugateOracle O) = (paperMatrix O)ᵀ := by
  ext i j
  simp only [paperMatrix, conjugateOracle, Matrix.transpose_apply]
  have hdouble : ∀ x : Fin d,
      (starRingEnd ℂ) ((starRingEnd ℂ) (O.col i x)) = O.col i x := fun x => by simp
  have hs : (∑ x, (starRingEnd ℂ) ((starRingEnd ℂ) (O.col i x)) *
        (starRingEnd ℂ) (O.col j x)) =
      (∑ x, (starRingEnd ℂ) (O.col j x) * O.col i x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hdouble x]
    ring
  rw [hs]
  ring

/-- The index marginal prepared using conjugated columns equals the original paper Gram matrix. -/
theorem conjugateAccess_marginal {m d : ℕ} (O : ColumnOracle m d) :
    marginal (conjugateOracle O) = paperMatrix O := by
  rw [marginal_eq_paperMatrix_transpose, paperMatrix_conjugateOracle,
    Matrix.transpose_transpose]

/-- The paper Gram matrix of any column oracle is a density operator. -/
theorem conjugateAccess_isDensity {m d : ℕ} (O : ColumnOracle m d) :
    IsDensityOperator (paperMatrix O) := by
  rw [← conjugateAccess_marginal O]
  exact marginal_isDensity (conjugateOracle O)

/-- The ceiling base two logarithm of the number of column indices. -/
def addressBits (m : ℕ) : ℕ := Nat.clog 2 m

/-- The list containing every column index in its natural order. -/
def loadPass (m : ℕ) : List (Fin m) := List.ofFn (fun i => i)

/-- The concatenation of `n` complete column loading passes. -/
def copyLoad (n m : ℕ) : List (Fin m) := (List.replicate n (loadPass m)).flatten

/-- Every column index occurs in a complete loading pass. -/
theorem mem_loadPass {m : ℕ} (i : Fin m) : i ∈ loadPass m := by
  simp [loadPass]

/-- A complete loading pass has length `m`. -/
theorem loadPass_length (m : ℕ) : (loadPass m).length = m := by
  simp [loadPass]

/-- A complete loading pass contains no repeated indices. -/
theorem loadPass_nodup (m : ℕ) : (loadPass m).Nodup :=
  List.nodup_ofFn.mpr Function.injective_id

/-- The concatenation of `n` loading passes on `m` columns has length `n * m`. See
[LloydMohseniRebentrost2014]. -/
theorem copyLoad_length (n m : ℕ) : (copyLoad n m).length = n * m := by
  simp [copyLoad, List.length_flatten, List.sum_replicate, loadPass_length]

/-- The number of indices `m` is at most `2 ^ addressBits m`. -/
theorem le_pow_addressBits (m : ℕ) : m ≤ 2 ^ addressBits m := by
  simpa [addressBits] using Nat.le_pow_clog (by decide : 1 < 2) m

/-- More than one column index requires a positive number of address bits. -/
theorem addressBits_pos {m : ℕ} (hm : 1 < m) : 0 < addressBits m := by
  rcases Nat.eq_zero_or_pos (addressBits m) with h | h
  · exfalso
    have hp := le_pow_addressBits m
    rw [h] at hp
    have h1 : m ≤ 1 := by simpa using hp
    omega
  · exact h

end Qatlib.Papers.QuantumPCA14.InputAccess
