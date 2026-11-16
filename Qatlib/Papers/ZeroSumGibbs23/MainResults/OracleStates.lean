/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel
public import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic

@[expose] public section


/-!
# OracleStates deterministic core

This module preserves closed algebraic and finite-dimensional source results
from arXiv:2301.03763v1. It does not assert a circuit implementation, concentration
bound, or end-to-end algorithmic complexity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.OracleStates
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model
variable {m n N : ℕ}

/-- The amplitude vector of Lemma 7 (p.21): `|0⟩|i⟩` carries `√(x_i/β)`, the
`|1⟩`-branch carries the normalisation slack `√(1 − ‖x‖₁/β)` on the garbage
basis state `|0⟩`. -/
def samplerTreeAmp (x : Fin m → ℝ) (β : ℝ) : Fin 2 × Fin m → ℂ :=
  fun p => if p.1 = 0 then (Real.sqrt (x p.2 / β) : ℂ)
           else if p.2.val = 0 then (Real.sqrt (1 - l1Norm x / β) : ℂ)
           else 0

/-- `samplerTreeAmp` is a normalised state: the squared amplitudes sum to one.
This is the amplitude identity of Lemma 7 (p.21). -/
theorem tree_normalized (x : Fin m → ℝ) (β : ℝ) (hm : 0 < m)
    (hx : ∀ i, 0 ≤ x i) (hβ : 0 < β) (hβx : l1Norm x ≤ β) :
    ∑ p : Fin 2 × Fin m, Complex.normSq (samplerTreeAmp x β p) = 1 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 : (∑ i : Fin m, Complex.normSq (samplerTreeAmp x β (0, i))) = l1Norm x / β := by
    have hterm : ∀ i : Fin m, Complex.normSq (samplerTreeAmp x β (0, i)) = x i / β := by
      intro i
      unfold samplerTreeAmp
      rw [ite_eq_left rfl, Complex.normSq_ofReal]
      simpa [pow_two] using Real.sq_sqrt (div_nonneg (hx i) hβ.le)
    simp_rw [hterm]
    calc
      (∑ i : Fin m, x i / β) = (∑ i : Fin m, x i) / β := by
        simp_rw [div_eq_mul_inv, Finset.sum_mul]
      _ = l1Norm x / β := by
        have hsum : (∑ i : Fin m, x i) = l1Norm x := by
          unfold l1Norm
          exact (Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx i)).symm
        rw [hsum]
  have h1 : (∑ i : Fin m, Complex.normSq (samplerTreeAmp x β (1, i))) = 1 - l1Norm x / β := by
    have hsingle : ∀ i : Fin m, i.val ≠ 0 → samplerTreeAmp x β (1, i) = 0 := by
      intro i hi
      unfold samplerTreeAmp
      have h1ne : ¬ ((1 : Fin 2) = 0) := by decide
      rw [ite_eq_right h1ne, ite_eq_right hi]
    rw [Finset.sum_eq_single ⟨0, hm⟩]
    · unfold samplerTreeAmp
      have h1ne : ¬ ((1 : Fin 2) = 0) := by decide
      rw [ite_eq_right h1ne, ite_eq_left rfl, Complex.normSq_ofReal]
      have hle1 : 0 ≤ 1 - l1Norm x / β := by
        rw [sub_nonneg]
        exact (div_le_one hβ).mpr hβx
      simpa [pow_two] using Real.sq_sqrt hle1
    · intro i _ hi
      rw [hsingle i (fun hv => hi (Fin.ext hv))]
      simp
    · intro h
      exact absurd (Finset.mem_univ (⟨0, hm⟩ : Fin m)) h
  rw [h0, h1]
  ring

/-- The amplitude vector of Corollary 4 (p.21), with the sign of `A_{ij}`
carried in the amplitude (Section 2, p.7): the `|0⟩|i⟩` branch carries
`sign(A_{ij}) √(|A_{ij}| x_i/β)`, whose squared modulus is `|A_{ij}| x_i/β`. -/
def cor4Amp (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (β : ℝ)
    (j : Fin n) : Fin 2 × Fin m → ℂ :=
  fun p => if p.1 = 0 then
             (((if 0 ≤ A p.2 j then (1 : ℝ) else -1) *
               Real.sqrt (|A p.2 j| * x p.2 / β) : ℝ) : ℂ)
           else if p.2.val = 0 then
             (Real.sqrt (1 - l1Norm (fun i => |A i j| * x i) / β) : ℂ)
           else 0

/-- The squared amplitudes of `cor4Amp` equal those of the sampler-tree state
with vector `i ↦ |A_{ij}| x_i`; the sign of `A_{ij}` drops out. -/
theorem loaded_sq (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (β : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hβ : 0 < β) (j : Fin n) (p : Fin 2 × Fin m) :
    Complex.normSq (cor4Amp A x β j p) =
      Complex.normSq (samplerTreeAmp (fun i => |A i j| * x i) β p) := by
  rcases p with ⟨a, i⟩
  have hr : 0 ≤ |A i j| * x i / β :=
    div_nonneg (mul_nonneg (abs_nonneg _) (hx i)) hβ.le
  have hs2 : (if 0 ≤ A i j then (1 : ℝ) else -1) ^ 2 = 1 := by
    split_ifs <;> norm_num
  have hsq : Real.sqrt (|A i j| * x i / β) ^ 2 = |A i j| * x i / β := Real.sq_sqrt hr
  by_cases ha : a = 0
  · rw [ha]
    dsimp only [cor4Amp, samplerTreeAmp]
    rw [ite_eq_left rfl, ite_eq_left rfl, Complex.normSq_ofReal, Complex.normSq_ofReal]
    have hss : (if 0 ≤ A i j then (1 : ℝ) else -1) *
        (if 0 ≤ A i j then (1 : ℝ) else -1) = 1 := by
      rw [← pow_two]; exact hs2
    nlinarith [hss, hsq]
  · dsimp only [cor4Amp, samplerTreeAmp]
    rw [ite_eq_right ha, ite_eq_right ha]

/-- `cor4Amp` is a normalised state. -/
theorem load_normalized (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (β : ℝ)
    (hm : 0 < m) (hx : ∀ i, 0 ≤ x i) (hβ : 0 < β) (hβx : l1Norm x ≤ β)
    (hA : MaxEntryBound A 1) (j : Fin n) :
    ∑ p : Fin 2 × Fin m, Complex.normSq (cor4Amp A x β j p) = 1 := by
  have hle : l1Norm (fun i => |A i j| * x i) ≤ l1Norm x := by
    unfold l1Norm
    calc
      ∑ i, |(|A i j| * x i)| = ∑ i, |A i j| * x i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (abs_nonneg _), abs_of_nonneg (hx i)]
      _ ≤ ∑ i, 1 * x i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hA i j) (hx i)
      _ = ∑ i, x i := by simp
      _ = ∑ i, |x i| := by
        exact (Finset.sum_congr rfl fun i _ => abs_of_nonneg (hx i)).symm
  simp_rw [loaded_sq A x β hx hβ j]
  exact tree_normalized (fun i => |A i j| * x i) β hm
    (fun i => mul_nonneg (abs_nonneg _) (hx i)) hβ (le_trans hle hβx)

/-- The block-encoded matrix of Corollary 6: the diagonal matrix
`diag(Aᵀx/β)` acting on the `|j⟩` register. -/
def cor6Diag (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (β : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => ((colSum A x j / β : ℝ) : ℂ)

/-- The corner identity of Corollary 6 (p.25): the `|00⟩`-corner of the
block-encoding `U` is `δ_{jj'} (Aᵀx)_j/β`. Unpacked from the Frozen concept
`IsBlockEncoding`. -/
theorem block_corner
    (U : Matrix ((Fin 2 × Fin 2 × Fin m) × Fin n) ((Fin 2 × Fin 2 × Fin m) × Fin n) ℂ)
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (β : ℝ) (hm : 0 < m)
    (hU : Qatlib.Concepts.BlockEncoding.StateBlockEncoding.IsBlockEncoding U
      ((0, 0, ⟨0, hm⟩) : Fin 2 × Fin 2 × Fin m) (cor6Diag A x β) 1) (j j' : Fin n) :
    U (((0, 0, ⟨0, hm⟩), j)) (((0, 0, ⟨0, hm⟩), j')) =
      if j = j' then ((colSum A x j / β : ℝ) : ℂ) else 0 := by
  have hc := hU.2.2
  have h := congrFun (congrFun hc j) j'
  rw [Qatlib.Concepts.BlockEncoding.StateBlockEncoding.blockCorner_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hone : (((1 : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by norm_num
  rw [hone, one_mul]
  simp [cor6Diag, Matrix.diagonal]

end Qatlib.Papers.ZeroSumGibbs23.MainResults.OracleStates
