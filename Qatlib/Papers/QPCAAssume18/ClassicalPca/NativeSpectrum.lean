/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualGramLaw

/-!
# Spectral data for PCA sketches

Defines canonical small-sketch eigenvectors and squared singular values using the ordered
Hermitian spectrum. Energy identities, cutoff counts, and gap isolation bounds provide the
spectral estimates used in the PCA construction of [Tang2021].

## Main statements

* `pcaSmallVector_action`: The canonical small-sketch vector is an eigenvector of `W * Wᴴ` with
  eigenvalue `pcaSmallValue W i`.
* `pca_antitone_prefix_isolation`: For an antitone finite sequence, consecutive gaps at least
  `g` along the prescribed prefix separate each prefix value from every other value by at least
  `g`.

## References

* [Tang, 2021][Tang2021]
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SketchSpectral.SketchPerturb
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

/-- Transports an index in `Fin d` to the equal-sized index type `Fin (Fintype.card (Fin d))`. -/
def pcaNativeIndex {d : ℕ} (i : Fin d) : Fin (Fintype.card (Fin d)) :=
  ⟨i.val, by simpa only [Fintype.card_fin] using! i.isLt⟩

/-- The ordered unit eigenvector of `W * Wᴴ` corresponding to index `i`. -/
def pcaSmallVector {q : ℕ} (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    EuclideanSpace ℂ (Fin q) :=
  orderedHermitianBasis (Matrix.isHermitian_mul_conjTranspose_self W) (pcaNativeIndex i)

/-- The squared singular value of `W` at index `i`. -/
def pcaSmallValue {q : ℕ} (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) : ℝ :=
  matrixSingularValues W i ^ 2

/-- Each canonical small-sketch eigenvector has norm one. -/
theorem pcaSmallVector_norm {q : ℕ} (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    ‖pcaSmallVector W i‖ = 1 :=
  (orderedHermitianBasis (Matrix.isHermitian_mul_conjTranspose_self W)).norm_eq_one _

/-- The canonical small-sketch vector is an eigenvector of `W * Wᴴ` with eigenvalue
`pcaSmallValue W i`. -/
theorem pcaSmallVector_action {q : ℕ} (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    (W * Wᴴ).toEuclideanLin (pcaSmallVector W i) =
      (pcaSmallValue W i : ℂ) • pcaSmallVector W i := by
  have h :=
      orderedHermitianBasis_action (Matrix.isHermitian_mul_conjTranspose_self W) (pcaNativeIndex i)
  rw [sketchSingularValueStability_outer_gram] at h
  exact h

/-- The sum of squared singular values over the column dimension equals the squared Frobenius
energy. -/
theorem pca_native_squared_energy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i ∈ Finset.range d, matrixSingularValues A i ^ 2) = sketchSquared A := by
  have h := spectralFrobenius_sq_singular A
  rw [Fin.sum_univ_eq_sum_range (fun i => matrixSingularValues A i ^ 2)] at h
  simp only [Fintype.card_fin] at h
  rw [← h]
  unfold spectralFrobenius sketchSquared sketchRowSquared
  exact Real.sq_sqrt
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)

/-- The squared singular values in a prefix of length at most the column dimension sum to at
most the input energy. -/
theorem pca_prefix_squared_energy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (k : ℕ) (hkd : k ≤ d) :
    (∑ i ∈ Finset.range k, matrixSingularValues A i ^ 2) ≤ sketchSquared A := by
  rw [← pca_native_squared_energy A]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkd) fun i _ _ => sq_nonneg _

/-- Each squared singular value indexed by `Fin d` is at most the input energy. -/
theorem pca_squared_value_le_energy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) (i : Fin d) :
    matrixSingularValues A i ^ 2 ≤ sketchSquared A := by
  rw [← pca_native_squared_energy A]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (matrixSingularValues A j))
      (Finset.mem_range.mpr i.isLt)

/-- If the first `k` singular values are at least `sigma`, then `k * sigma^2` is at most the
input energy. -/
theorem pca_cutoff_count {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (k : ℕ) (hkd : k ≤ d) (sigma : ℝ) (hsigma : 0 < sigma)
    (hcut : ∀ i ∈ Finset.range k, sigma ≤ matrixSingularValues A i) :
    (k : ℝ) * sigma ^ 2 ≤ sketchSquared A := by
  calc
    _ = ∑ _ ∈ Finset.range k, sigma ^ 2 := by simp
    _ ≤ ∑ i ∈ Finset.range k, matrixSingularValues A i ^ 2 :=
      Finset.sum_le_sum fun i hi => pow_le_pow_left₀ hsigma.le (hcut i hi) 2
    _ ≤ _ := pca_prefix_squared_energy A k hkd

/-- A nonempty retained prefix above a positive cutoff implies that the effective rank parameter
is at least one. -/
theorem pca_effective_rank_one_le {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (sigma : ℝ) (hsigma : 0 < sigma)
    (hcut : ∀ i ∈ Finset.range k, sigma ≤ matrixSingularValues A i) :
    1 ≤ sketchSquared A / sigma ^ 2 := by
  have hcount := pca_cutoff_count A k hkd sigma hsigma hcut
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply (le_div_iff₀ (sq_pos_of_pos hsigma)).mpr
  nlinarith

/-- A relative squared-singular-value gap on a nonempty prefix is at most one for a matrix of
positive energy. -/
theorem pca_relative_gap_le_one {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (eta : ℝ)
    (hgap : ∀ i ∈ Finset.range k,
      eta * sketchSquared A ≤ matrixSingularValues A i ^ 2 - matrixSingularValues A (i + 1) ^ 2) :
    eta ≤ 1 := by
  have hd : 0 < d := by omega
  have h0 := hgap 0 (Finset.mem_range.mpr (by omega))
  have hval := pca_squared_value_le_energy A ⟨0, hd⟩
  have hbound : eta * sketchSquared A ≤ sketchSquared A := by
    nlinarith [sq_nonneg (matrixSingularValues A 1)]
  have h := (le_div_iff₀ hA).mpr hbound
  simpa only [div_self hA.ne'] using! h

/-- For an antitone finite sequence, consecutive gaps at least `g` along the prescribed prefix
separate each prefix value from every other value by at least `g`. -/
theorem pca_antitone_prefix_isolation {N : ℕ} (vals : Fin N → ℝ) (hanti : Antitone vals)
    (k : ℕ) (g : ℝ)
    (hgap : ∀ i : Fin N, i.val < k → ∀ hi : i.val + 1 < N,
      g ≤ vals i - vals ⟨i.val + 1, hi⟩)
    (i : Fin N) (hik : i.val < k) (j : Fin N) (hne : j ≠ i) :
    g ≤ |vals j - vals i| := by
  have hv : j.val ≠ i.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hji | hij
  · let p : Fin N := ⟨i.val - 1, by omega⟩
    have hpnext : p.val + 1 < N := by dsimp [p]; omega
    have hp : p.val < k := by dsimp [p]; omega
    have heq : (⟨p.val + 1, hpnext⟩ : Fin N) = i := by apply Fin.ext; dsimp [p]; omega
    have hg := hgap p hp hpnext
    rw [heq] at hg
    have hpj : vals p ≤ vals j := hanti (by change j.val ≤ p.val; dsimp [p]; omega)
    have hijv : vals i ≤ vals j := hanti (by change j.val ≤ i.val; omega)
    rw [abs_of_nonneg (sub_nonneg.mpr hijv)]
    linarith
  · have hnext : i.val + 1 < N := by omega
    have hg := hgap i hik hnext
    have hpj : vals j ≤ vals ⟨i.val + 1, hnext⟩ := hanti (by change i.val + 1 ≤ j.val; omega)
    have hijv : vals j ≤ vals i := hanti (by change i.val ≤ j.val; omega)
    rw [abs_of_nonpos (sub_nonpos.mpr hijv)]
    linarith

end Qatlib.Papers.QPCAAssume18.ClassicalPca
