/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputationDefs

/-!
# Quantized matrices and frame resource bounds

This module bounds entrywise, Frobenius, operator, and spectral errors for rational
approximations of matrices, including symmetrization of Hermitian inputs. The spectral
perturbation estimates use the matrix analysis framework of [Bhatia1997].

It also defines a resource ledger for `FrameData` and proves the corresponding symbolic gate
counts, ancilla counts, time costs, and budget equivalence.

## Main statements

* `tunableGoal_frobenius_error` and `tunableGoal_operator_error`: bound quantization errors.
* `tunableGoal_same_word_margin`: preserves a positive eigenvalue gap above the error threshold.
* `tunableGoal_endpoint` and `optGoal_endpoint`: collect the approximation and frame ledger
  statements.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb
namespace MatrixComputation

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real precision unit `ratUnitR p` is nonnegative. -/
theorem ratUnitR_nonneg (p : ℕ) : 0 ≤ ratUnitR p := by
  unfold ratUnitR
  positivity

/-- Complex conjugation preserves the norm. -/
theorem norm_star (z : ℂ) : ‖star z‖ = ‖z‖ := by
  rw [Complex.star_def, Complex.norm_def, Complex.norm_def]
  congr 1
  simp

/-- Complex conjugation distributes over subtraction. -/
theorem star_sub (a b : ℂ) : star (a - b) = star a - star b := by
  rw [Complex.star_def, map_sub, starRingEnd_apply]

/-- The finite record containing the rational approximation at precision `p`, the error value
`ratUnitR p`, and the bit count `p`. -/
noncomputable def quantise (x : CauchyReal) (p : ℕ) : FiniteReal where
  value := x.approx p
  error := ratUnitR p
  bits := p

/-- The complex matrix obtained by casting each rational approximation entry at precision `p`. -/
noncomputable def quantiseMatrix (A : CauchyComplexMatrix I) (p : ℕ) :
    Matrix I I ℂ :=
  fun i j => (A.approx p i j : ℚ)

/-- The Hermitian symmetrization `(1 / 2 : ℂ) • (M + Mᴴ)`. -/
noncomputable def sym (M : Matrix I I ℂ) : Matrix I I ℂ :=
  (1 / 2 : ℂ) • (M + Mᴴ)

/-- Quantizing at `digitsFor k` gives error at most `ratUnitR k`, with the recorded bit count
and value equal to the chosen precision and approximation. -/
theorem tunableGoal_digits (x : CauchyReal) (k : ℕ) :
    (quantise x (digitsFor k)).error ≤ ratUnitR k ∧
    (quantise x (digitsFor k)).bits = digitsFor k ∧
    (quantise x (digitsFor k)).value = x.approx (digitsFor k) := by
  refine ⟨?_, rfl, rfl⟩
  have hmain : ratUnitR (digitsFor k) ≤ ratUnitR k := by
    have htwo : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [htwo]
      have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
      nlinarith
    unfold ratUnitR digitsFor
    rw [htwo, div_mul_eq_div_div]
    calc (1 : ℝ) / (2 : ℝ) ^ k / 2 = (1 : ℝ) / (2 : ℝ) ^ k * (1 / 2) := by ring
      _ ≤ (1 : ℝ) / (2 : ℝ) ^ k * 1 :=
          mul_le_mul_of_nonneg_left (by norm_num)
            (show (0 : ℝ) ≤ 1 / (2 : ℝ) ^ k by positivity)
      _ = (1 : ℝ) / (2 : ℝ) ^ k := by ring
  exact hmain

/-- Every entry of the quantized matrix differs from the corresponding original entry by at most
`ratUnitR p`. -/
theorem tunableGoal_entry_error (A : CauchyComplexMatrix I) (p : ℕ) (i j : I) :
    ‖quantiseMatrix A p i j - A.data i j‖ ≤ ratUnitR p :=
  A.error p i j

/-- If every entry norm is at most `ratUnitR p`, the Frobenius norm is at most `Fintype.card I *
ratUnitR p`. -/
theorem tunableGoal_frobenius_of_entrywise (M : Matrix I I ℂ) (p : ℕ)
    (h : ∀ i j, ‖M i j‖ ≤ ratUnitR p) :
    spectralFrobenius M ≤ (Fintype.card I : ℝ) * ratUnitR p := by
  have hsq : spectralFrobenius M ^ 2 ≤ ((Fintype.card I : ℝ) * ratUnitR p) ^ 2 := by
    rw [spectralFrobenius_sq]
    have hentry : ∀ i j : I, Complex.normSq (M i j) ≤ (ratUnitR p) ^ 2 := by
      intro i j
      have h1 : Complex.normSq (M i j) = ‖M i j‖ ^ 2 := (Complex.sq_norm _).symm
      rw [h1]
      have hsq' := ((sq_le_sq₀ (norm_nonneg _) (ratUnitR_nonneg p)).mpr (h i j))
      simpa using hsq'
    calc (∑ i : I, ∑ j : I, Complex.normSq (M i j))
        ≤ ∑ _i : I, ∑ _j : I, (ratUnitR p) ^ 2 := by
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
      _ = ((Fintype.card I : ℝ) * ratUnitR p) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
  have hnonneg : 0 ≤ spectralFrobenius M := spectralFrobenius_nonneg _
  have hnonneg2 : 0 ≤ (Fintype.card I : ℝ) * ratUnitR p :=
    mul_nonneg (Nat.cast_nonneg _) (ratUnitR_nonneg p)
  nlinarith

/-- The Frobenius error of matrix quantization is at most the matrix dimension times `ratUnitR
p`. -/
theorem tunableGoal_frobenius_error (A : CauchyComplexMatrix I) (p : ℕ) :
    spectralFrobenius (quantiseMatrix A p - A.data) ≤ (Fintype.card I : ℝ) * ratUnitR p :=
  tunableGoal_frobenius_of_entrywise _ p fun i j => tunableGoal_entry_error A p i j

/-- The operator norm error of matrix quantization is at most the matrix dimension times
`ratUnitR p`. -/
theorem tunableGoal_operator_error (A : CauchyComplexMatrix I) (p : ℕ) :
    ‖quantiseMatrix A p - A.data‖ ≤ (Fintype.card I : ℝ) * ratUnitR p :=
  le_trans (spectral_operator_norm_le_frobenius _) (tunableGoal_frobenius_error A p)

/-- For a Hermitian input, the symmetrization error is the average of the quantization error and
its conjugate transpose. -/
theorem tunableGoal_sym_error_key (A : CauchyComplexMatrix I) (p : ℕ)
    (hA : A.data.IsHermitian) :
    sym (quantiseMatrix A p) - A.data
      = (1 / 2 : ℂ) • ((quantiseMatrix A p - A.data)
        + (quantiseMatrix A p - A.data)ᴴ) := by
  ext i j
  have hAij : star (A.data j i) = A.data i j := by
    have h := congrFun (congrFun hA i) j
    simpa using h
  simp only [sym, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.conjTranspose_apply, star_sub]
  rw [hAij]
  ring

/-- Symmetrizing a quantized Hermitian matrix preserves the dimension-scaled operator error
bound and the entrywise precision bound. -/
theorem tunableGoal_sym_error (A : CauchyComplexMatrix I) (p : ℕ)
    (hA : A.data.IsHermitian) :
    ‖sym (quantiseMatrix A p) - A.data‖ ≤ (Fintype.card I : ℝ) * ratUnitR p ∧
    ∀ i j, ‖(sym (quantiseMatrix A p) - A.data) i j‖ ≤ ratUnitR p := by
  have hkey := tunableGoal_sym_error_key A p hA
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div]
    norm_num
  have hstar : ∀ i j, ‖(quantiseMatrix A p - A.data) i j‖ ≤ ratUnitR p :=
    fun i j => tunableGoal_entry_error A p i j
  have hstar2 : ∀ i j, ‖star ((quantiseMatrix A p - A.data) j i)‖ ≤ ratUnitR p := by
    intro i j
    rw [norm_star]
    exact hstar j i
  have hentry : ∀ i j, ‖(sym (quantiseMatrix A p) - A.data) i j‖ ≤ ratUnitR p := by
    intro i j
    rw [hkey]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.conjTranspose_apply]
    calc ‖(1 / 2 : ℂ) * ((quantiseMatrix A p - A.data) i j
        + star ((quantiseMatrix A p - A.data) j i))‖
        = ‖(1 / 2 : ℂ)‖ * ‖(quantiseMatrix A p - A.data) i j
            + star ((quantiseMatrix A p - A.data) j i)‖ := norm_mul _ _
      _ ≤ (1 / 2 : ℝ) * (‖(quantiseMatrix A p - A.data) i j‖
            + ‖star ((quantiseMatrix A p - A.data) j i)‖) := by
          rw [hhalf]
          have h := norm_add_le ((quantiseMatrix A p - A.data) i j)
            (star ((quantiseMatrix A p - A.data) j i))
          exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (ratUnitR p + ratUnitR p) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add (hstar i j) (hstar2 i j)
          · norm_num
      _ = ratUnitR p := by ring
  have hfro : spectralFrobenius (sym (quantiseMatrix A p) - A.data)
      ≤ (Fintype.card I : ℝ) * ratUnitR p :=
    tunableGoal_frobenius_of_entrywise _ p hentry
  refine ⟨?_, hentry⟩
  calc ‖sym (quantiseMatrix A p) - A.data‖
      ≤ spectralFrobenius (sym (quantiseMatrix A p) - A.data) :=
        spectral_operator_norm_le_frobenius _
    _ ≤ (Fintype.card I : ℝ) * ratUnitR p := hfro

/-- The sum of squared ordered eigenvalue errors after Hermitian symmetrization is at most the
square of the dimension-scaled precision bound. -/
theorem tunableGoal_gram_error (A : CauchyComplexMatrix I) (p : ℕ)
    (hA : A.data.IsHermitian) (hÃ : (sym (quantiseMatrix A p)).IsHermitian) :
    (∑ i : Fin (Fintype.card I), (orderedHermitianValues hA i
        - orderedHermitianValues hÃ i) ^ 2) ≤ ((Fintype.card I : ℝ) * ratUnitR p) ^ 2 := by
  have hhw := ordered_hermitian_hoffman_wielandt A.data (sym (quantiseMatrix A p)) hA hÃ
  have hkey := tunableGoal_sym_error A p hA
  have hneg : A.data - sym (quantiseMatrix A p)
      = -(sym (quantiseMatrix A p) - A.data) := by simp only [neg_sub]
  have hfroeq : spectralFrobenius (A.data - sym (quantiseMatrix A p))
      = spectralFrobenius (sym (quantiseMatrix A p) - A.data) := by
    rw [hneg]
    have h1 : (spectralFrobenius (-(sym (quantiseMatrix A p) - A.data))) ^ 2
        = (spectralFrobenius (sym (quantiseMatrix A p) - A.data)) ^ 2 := by
      rw [spectralFrobenius_sq, spectralFrobenius_sq]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.sub_apply, Matrix.neg_apply]
      have hn : Complex.normSq (-(sym (quantiseMatrix A p) i j - A.data i j))
          = Complex.normSq (sym (quantiseMatrix A p) i j - A.data i j) := by
        rw [← Complex.sq_norm, ← Complex.sq_norm, norm_neg]
      rw [hn]
    exact (sq_eq_sq₀ (spectralFrobenius_nonneg _) (spectralFrobenius_nonneg _)).mp h1
  have hfro : spectralFrobenius (A.data - sym (quantiseMatrix A p))
      ≤ (Fintype.card I : ℝ) * ratUnitR p := by
    rw [hfroeq]
    exact tunableGoal_frobenius_of_entrywise (sym (quantiseMatrix A p) - A.data) p hkey.2
  have hnonneg : 0 ≤ spectralFrobenius (A.data - sym (quantiseMatrix A p)) :=
    spectralFrobenius_nonneg _
  have hnonneg2 : 0 ≤ (Fintype.card I : ℝ) * ratUnitR p :=
    mul_nonneg (Nat.cast_nonneg _) (ratUnitR_nonneg p)
  have hsq : spectralFrobenius (A.data - sym (quantiseMatrix A p)) ^ 2
      ≤ ((Fintype.card I : ℝ) * ratUnitR p) ^ 2 := by nlinarith
  have hhw' : (∑ i : Fin (Fintype.card I), (orderedHermitianValues hA i
        - orderedHermitianValues hÃ i) ^ 2)
      ≤ spectralFrobenius (A.data - sym (quantiseMatrix A p)) ^ 2 := by
    simpa [Matrix.norm_conjTranspose] using hhw
  exact le_trans hhw' hsq

/-- The original ordered eigenvalue gap minus the symmetrized approximation's gap is at most
twice the dimension-scaled precision bound. -/
theorem tunableGoal_spectral_gap (A : CauchyComplexMatrix I) (p : ℕ)
    (hA : A.data.IsHermitian) (hÃ : (sym (quantiseMatrix A p)).IsHermitian)
    (i j : Fin (Fintype.card I)) :
    (orderedHermitianValues hA i - orderedHermitianValues hA j)
      - (orderedHermitianValues hÃ i - orderedHermitianValues hÃ j)
        ≤ 2 * (Fintype.card I : ℝ) * ratUnitR p := by
  have h1 : orderedHermitianValues hA i - orderedHermitianValues hÃ i
      ≤ ‖A.data - sym (quantiseMatrix A p)‖ :=
    orderedHermitian_sub_le_norm A.data (sym (quantiseMatrix A p)) hA hÃ i
  have h2 : orderedHermitianValues hÃ j - orderedHermitianValues hA j
      ≤ ‖sym (quantiseMatrix A p) - A.data‖ :=
    orderedHermitian_sub_le_norm (sym (quantiseMatrix A p)) A.data hÃ hA j
  have h3 : ‖A.data - sym (quantiseMatrix A p)‖ ≤ (Fintype.card I : ℝ) * ratUnitR p := by
    have h := (tunableGoal_sym_error A p hA).1
    rw [show A.data - sym (quantiseMatrix A p)
        = -(sym (quantiseMatrix A p) - A.data) by simp only [neg_sub]]
    rw [norm_neg]
    exact h
  have h4 : ‖sym (quantiseMatrix A p) - A.data‖ ≤ (Fintype.card I : ℝ) * ratUnitR p :=
    (tunableGoal_sym_error A p hA).1
  linarith

/-- An original ordered eigenvalue gap larger than twice the dimension-scaled precision remains
positive after symmetrized quantization, with the stated one-sided gap error bound. -/
theorem tunableGoal_same_word_margin (A : CauchyComplexMatrix I) (p : ℕ)
    (hA : A.data.IsHermitian) (hÃ : (sym (quantiseMatrix A p)).IsHermitian)
    (i j : Fin (Fintype.card I))
    (hgap : 2 * (Fintype.card I : ℝ) * ratUnitR p
      < orderedHermitianValues hA i - orderedHermitianValues hA j) :
    0 < orderedHermitianValues hÃ i - orderedHermitianValues hÃ j ∧
    (orderedHermitianValues hA i - orderedHermitianValues hA j)
      - (orderedHermitianValues hÃ i - orderedHermitianValues hÃ j)
        ≤ 2 * (Fintype.card I : ℝ) * ratUnitR p := by
  refine ⟨?_, tunableGoal_spectral_gap A p hA hÃ i j⟩
  have hgap' := tunableGoal_spectral_gap A p hA hÃ i j
  have h1 : orderedHermitianValues hÃ i - orderedHermitianValues hÃ j
      = (orderedHermitianValues hA i - orderedHermitianValues hA j)
        - ((orderedHermitianValues hA i - orderedHermitianValues hA j)
          - (orderedHermitianValues hÃ i - orderedHermitianValues hÃ j)) := by ring
  rw [h1]
  linarith

/-- The matrix read cost is `D * D * p` and is at most `D * D * (p + 1)`. -/
theorem tunableGoal_read_cost (D p : ℕ) :
    matrixReadBits D p = D * D * p ∧
    matrixReadBits D p ≤ D * D * (p + 1) := by
  refine ⟨?_, ?_⟩
  · simp [matrixReadBits]
  · simp only [matrixReadBits]
    nlinarith

/-- The complex matrix obtained by casting the rational Gram entries in `FrameData`. -/
def FrameData.gramMatrix
    {m : ℕ} (F : FrameData m) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (F.gram i j : ℚ)

/-- The prescribed polar correction time cost `F.entries * F.entries`. -/
def FrameData.polarCorrectionBitTime
    {m : ℕ} (F : FrameData m) : ℕ := F.entries * F.entries

/-- The sum of the frame read time and polar correction time costs. -/
def FrameData.totalBitTime
    {m : ℕ} (F : FrameData m) : ℕ :=
  F.readBitTime + (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.polarCorrectionBitTime F)

/-- The condition that the recorded defect and total time fit the specified error and time
budgets. -/
def FrameData.implementable
    {m : ℕ} (F : FrameData m) (errorBudget : ℝ)
    (bitTimeBudget : ℕ) : Prop :=
  (F.defect : ℝ) ≤ errorBudget ∧ (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.totalBitTime F) ≤ bitTimeBudget

/-- Every gate in the frame preparation word belongs to the fixed list `FrameGateSet.all`. -/
theorem optGoal_fixed_gate_table {m : ℕ} (F : FrameData m) :
    ∀ g ∈ F.prepareWord, g ∈ FrameGateSet.all := by
  intro g hg
  have hdisj : g = FrameGateKind.gramCorrection ∨ g = FrameGateKind.reflection ∨
      g = FrameGateKind.phaseRotation ∨ g = FrameGateKind.ancillaSwap ∨
      g = FrameGateKind.uncompute := by
    simp only [FrameData.prepareWord, List.mem_append, List.mem_replicate,
      List.mem_cons, List.not_mem_nil, or_false] at hg
    aesop
  simpa only [FrameGateSet.all, List.mem_cons, List.not_mem_nil, or_false] using hdisj

/-- The frame preparation word has length `F.entries + 5`. -/
theorem optGoal_gate_count {m : ℕ} (F : FrameData m) :
    F.prepareWord.length = F.entries + 5 := by
  simp only [FrameData.prepareWord, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The recorded frame ancilla count is `F.entries + 1`. -/
theorem optGoal_ancillas {m : ℕ} (F : FrameData m) : F.ancillas = F.entries + 1 := by
  rfl

/-- The total frame time cost equals `F.entries + F.entries * F.entries`. -/
theorem optGoal_read_bit_time {m : ℕ} (F : FrameData m) :
    (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.totalBitTime F) = F.entries + F.entries * F.entries := by
  rfl

/-- A supplied Gram defect certificate gives the same operator norm bound by the recorded
defect. -/
theorem optGoal_operator_error {m : ℕ} (F : FrameData m)
    (hcert : ‖(1 : Matrix (Fin m) (Fin m) ℂ) - (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.gramMatrix F)‖ ≤ (F.defect : ℝ)) :
    ‖(1 : Matrix (Fin m) (Fin m) ℂ) - (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.gramMatrix F)‖ ≤ (F.defect : ℝ) :=
  hcert

/-- The recorded frame defect is nonnegative both as a rational number and after casting to the
reals. -/
theorem optGoal_success_budget {m : ℕ} (F : FrameData m) :
    0 ≤ (F.defect : ℝ) ∧ 0 ≤ F.defect := by
  exact ⟨by exact_mod_cast F.defect_nonneg, F.defect_nonneg⟩

/-- Frame implementability is equivalent to the recorded defect and total time satisfying their
respective budgets. -/
theorem optGoal_implementability {m : ℕ} (F : FrameData m) (errorBudget : ℝ)
    (bitTimeBudget : ℕ) :
    (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.implementable F) errorBudget bitTimeBudget ↔
      ((F.defect : ℝ) ≤ errorBudget ∧ (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.totalBitTime F) ≤ bitTimeBudget) := by
  rfl

/-- Collect the quantization precision, entrywise, Frobenius, operator, symmetrization,
eigenvalue, gap, and read cost guarantees. -/
theorem tunableGoal_endpoint :
    (∀ (x : CauchyReal) (k : ℕ),
      (quantise x (digitsFor k)).error ≤ ratUnitR k ∧
      (quantise x (digitsFor k)).bits = digitsFor k ∧
      (quantise x (digitsFor k)).value = x.approx (digitsFor k)) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ) (i j : I),
      ‖quantiseMatrix A p i j - A.data i j‖ ≤ ratUnitR p) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ),
      spectralFrobenius (quantiseMatrix A p - A.data)
        ≤ (Fintype.card I : ℝ) * ratUnitR p) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ),
      ‖quantiseMatrix A p - A.data‖ ≤ (Fintype.card I : ℝ) * ratUnitR p) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ) (hA : A.data.IsHermitian),
      ‖sym (quantiseMatrix A p) - A.data‖ ≤ (Fintype.card I : ℝ) * ratUnitR p) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ) (hA : A.data.IsHermitian)
      (hÃ : (sym (quantiseMatrix A p)).IsHermitian),
      (∑ i : Fin (Fintype.card I), (orderedHermitianValues hA i
          - orderedHermitianValues hÃ i) ^ 2)
        ≤ ((Fintype.card I : ℝ) * ratUnitR p) ^ 2) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ) (hA : A.data.IsHermitian)
      (hÃ : (sym (quantiseMatrix A p)).IsHermitian) (i j : Fin (Fintype.card I)),
      (orderedHermitianValues hA i - orderedHermitianValues hA j)
        - (orderedHermitianValues hÃ i - orderedHermitianValues hÃ j)
          ≤ 2 * (Fintype.card I : ℝ) * ratUnitR p) ∧
    (∀ (A : CauchyComplexMatrix I) (p : ℕ) (hA : A.data.IsHermitian)
      (hÃ : (sym (quantiseMatrix A p)).IsHermitian) (i j : Fin (Fintype.card I)),
      2 * (Fintype.card I : ℝ) * ratUnitR p
        < orderedHermitianValues hA i - orderedHermitianValues hA j →
        0 < orderedHermitianValues hÃ i - orderedHermitianValues hÃ j ∧
        (orderedHermitianValues hA i - orderedHermitianValues hA j)
          - (orderedHermitianValues hÃ i - orderedHermitianValues hÃ j)
            ≤ 2 * (Fintype.card I : ℝ) * ratUnitR p) ∧
    (∀ (D p : ℕ),
      matrixReadBits D p = D * D * p ∧ matrixReadBits D p ≤ D * D * (p + 1)) := by
  refine ⟨tunableGoal_digits, tunableGoal_entry_error, tunableGoal_frobenius_error, tunableGoal_operator_error,
    fun A p hA => (tunableGoal_sym_error A p hA).1, tunableGoal_gram_error, tunableGoal_spectral_gap,
    tunableGoal_same_word_margin, tunableGoal_read_cost⟩

/-- Collect the fixed gate list, word length, ancilla count, time cost, defect certificate,
nonnegativity, and budget equivalence for frame data. -/
theorem optGoal_endpoint :
    (∀ {m : ℕ} (F : FrameData m), ∀ g ∈ F.prepareWord, g ∈ FrameGateSet.all) ∧
    (∀ {m : ℕ} (F : FrameData m), F.prepareWord.length = F.entries + 5) ∧
    (∀ {m : ℕ} (F : FrameData m), F.ancillas = F.entries + 1) ∧
    (∀ {m : ℕ} (F : FrameData m), (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.totalBitTime F) = F.entries + F.entries * F.entries) ∧
    (∀ {m : ℕ} (F : FrameData m)
      (hcert : ‖(1 : Matrix (Fin m) (Fin m) ℂ) - (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.gramMatrix F)‖ ≤ (F.defect : ℝ)),
      ‖(1 : Matrix (Fin m) (Fin m) ℂ) - (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.gramMatrix F)‖ ≤ (F.defect : ℝ)) ∧
    (∀ {m : ℕ} (F : FrameData m), 0 ≤ (F.defect : ℝ) ∧ 0 ≤ F.defect) ∧
    (∀ {m : ℕ} (F : FrameData m) (errorBudget : ℝ) (bitTimeBudget : ℕ),
      (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.implementable F) errorBudget bitTimeBudget ↔
        ((F.defect : ℝ) ≤ errorBudget ∧ (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.MatrixComputation.FrameData.totalBitTime F) ≤ bitTimeBudget)) := by
  refine ⟨optGoal_fixed_gate_table, optGoal_gate_count, optGoal_ancillas, optGoal_read_bit_time,
    optGoal_operator_error, optGoal_success_budget, optGoal_implementability⟩

end MatrixComputation
end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
