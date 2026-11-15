/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.BosonFock.PermAnalysis.ScaledMatrixIsometryEmbeddingStat
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib

open scoped Matrix

/-- The complex embedding of a real number is fixed by conjugation. -/
private theorem star_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = (r : ℂ) :=
  Complex.conj_ofReal r

/-- The complex embedding of the squared norm of `z` equals its conjugate multiplied by `z`. -/
private theorem normSq_star (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = star z * z :=
  Complex.normSq_eq_conj_mul_self

/-- Scaling a matrix by a real scalar scales each squared output-coordinate norm by the square
of that scalar. -/
private theorem normSq_smul_vecMul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) (v : Fin n → ℂ)
    (i : Fin n) :
    Complex.normSq ((((ε : ℂ) • X) *ᵥ v) i) = ε * ε * Complex.normSq ((X *ᵥ v) i) := by
  have h1 : (((ε : ℂ) • X) *ᵥ v) i = ((ε : ℂ) * (X *ᵥ v) i) := by
    simp only [Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, dotProduct, mul_assoc]
    rw [← Finset.mul_sum]
  have h2 : Complex.normSq ((ε : ℂ)) = ε * ε := by
    simp [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
  rw [h1, Complex.normSq_mul, h2]

/-- The assumed norm contraction implies that the scaled matrix does not increase the sum of
squared coordinate norms. -/
private theorem contraction_sum_normSq {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hc : ∀ v : Fin n → ℂ,
      ε * Real.sqrt (∑ i, Complex.normSq ((X *ᵥ v) i))
        ≤ Real.sqrt (∑ i, Complex.normSq (v i))) (v : Fin n → ℂ) :
    ∑ i, Complex.normSq ((((ε : ℂ) • X) *ᵥ v) i) ≤ ∑ i, Complex.normSq (v i) := by
  have hS : 0 ≤ ∑ i, Complex.normSq ((X *ᵥ v) i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hT : 0 ≤ ∑ i, Complex.normSq (v i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hsq := mul_self_le_mul_self (mul_nonneg hε (Real.sqrt_nonneg _)) (hc v)
  rw [Real.mul_self_sqrt hT] at hsq
  have h4 : ε * Real.sqrt (∑ i, Complex.normSq ((X *ᵥ v) i))
        * (ε * Real.sqrt (∑ i, Complex.normSq ((X *ᵥ v) i)))
      = ε * ε * ∑ i, Complex.normSq ((X *ᵥ v) i) := by
    nlinarith [Real.mul_self_sqrt hS]
  rw [h4] at hsq
  calc ∑ i, Complex.normSq ((((ε : ℂ) • X) *ᵥ v) i)
      = ε * ε * ∑ i, Complex.normSq ((X *ᵥ v) i) := by
        rw [Finset.sum_congr rfl (fun i _ => normSq_smul_vecMul X ε v i), ← Finset.mul_sum]
    _ ≤ ∑ i, Complex.normSq (v i) := hsq

/-- Moves a conjugate-transposed matrix across the complex inner product. -/
private theorem dotProduct_conjTranspose_mulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ)
    (v w : Fin n → ℂ) :
    star v ⬝ᵥ (Yᴴ *ᵥ w) = star (Y *ᵥ v) ⬝ᵥ w := by
  simp only [Pi.star_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hre : ∀ i : Fin n, star (v i) * (star (Y k i) * w k)
      = star (Y k i * v i) * w k := by
    intro i; rw [star_mul']; ring
  rw [Finset.sum_congr rfl (fun i _ => hre i), ← Finset.sum_mul, star_sum]

/-- The quadratic form of the identity minus the Gram matrix of `Y` is the difference between
the squared norms of the input and its image under `Y`. -/
private theorem qf_one_sub {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    star v ⬝ᵥ ((1 - Yᴴ * Y) *ᵥ v)
      = ((∑ i, Complex.normSq (v i)) : ℝ) - ((∑ i, Complex.normSq ((Y *ᵥ v) i)) : ℝ) := by
  have hsplit : ((1 - Yᴴ * Y) *ᵥ v) = v - (Yᴴ * Y) *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hprod : (Yᴴ * Y) *ᵥ v = Yᴴ *ᵥ (Y *ᵥ v) := (Matrix.mulVec_mulVec v Yᴴ Y).symm
  have hA : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i)) : ℝ) := by
    simp only [Pi.star_apply, dotProduct, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (normSq_star (v i)).symm
  have hB : star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v)
      = ((∑ i, Complex.normSq ((Y *ᵥ v) i)) : ℝ) := by
    simp only [Pi.star_apply, dotProduct, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (normSq_star ((Y *ᵥ v) i)).symm
  rw [hsplit, hprod, dotProduct_sub, dotProduct_conjTranspose_mulVec Y v (Y *ᵥ v), hA, hB]

/-- Every nonnegatively scaled contraction admits an isometric embedding with twice as many rows
whose upper block is the scaled matrix. -/
theorem scaledMatrixIsometryEmbedding : ScaledMatrixIsometryEmbedding := by
  unfold ScaledMatrixIsometryEmbedding
  intro n X ε hε hc
  set Y : Matrix (Fin n) (Fin n) ℂ := (ε : ℂ) • X with hY
  set H : Matrix (Fin n) (Fin n) ℂ := 1 - Yᴴ * Y with hHdef
  have hH : H.IsHermitian := by
    show Hᴴ = H
    rw [hHdef]
    simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

  have hpos : ∀ i : Fin n, 0 ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i, qf_one_sub Y ((hH.eigenvectorBasis i).ofLp : Fin n → ℂ)]
    exact sub_nonneg_of_le (contraction_sum_normSq hε hc _)

  obtain ⟨U, hUspec, hUunit⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ,
      H = U * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Uᴴ ∧ Uᴴ * U = 1 := by
    refine ⟨(hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_⟩
    · simpa using! hH.spectral_theorem
    · have hmem := (hH.eigenvectorUnitary : Matrix.unitaryGroup (Fin n) ℂ).2
      rwa [Matrix.mem_unitaryGroup_iff'] at hmem
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)) with hD
  have hDherm : Dᴴ = D := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    by_cases hab : a = b
    · subst hab; simp [hD, star_ofReal]
    · have hba : b ≠ a := Ne.symm hab; simp [hD, hab, hba]
  have hdiag : D * D = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i)]
    rfl
  set Z : Matrix (Fin n) (Fin n) ℂ := U * D * Uᴴ with hZ
  have hZconj : Zᴴ = Z := by
    rw [hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDherm, Matrix.mul_assoc]
  have hZH : Zᴴ * Z = H := by
    rw [hZconj, hZ]
    have hm : Uᴴ * (U * (D * Uᴴ)) = D * Uᴴ := by
      rw [← Matrix.mul_assoc, hUunit, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hm, (Matrix.mul_assoc D D Uᴴ).symm, hdiag, ← Matrix.mul_assoc]
    exact hUspec.symm

  set W : Matrix (Fin (2 * n)) (Fin n) ℂ := Matrix.of fun i j =>
    if h : (i : ℕ) < n then Y (Fin.castLT i h) j
    else Z (⟨(i : ℕ) - n, by have := i.isLt; omega⟩ : Fin n) j with hW
  have htop : ∀ (i : Fin n) (j : Fin n), W (Fin.castLE (by omega) i) j = Y i j := by
    intro i j
    have hlt : ((Fin.castLE (by omega) i : Fin (2 * n)) : ℕ) < n := by
      simp only [Fin.val_castLE]; exact i.isLt
    have hidx : Fin.castLT (Fin.castLE (by omega) i) hlt = i := by
      ext; simp
    simp only [hW, Matrix.of_apply, dite_eq_left hlt, hidx]
  have hbot : ∀ (i : Fin n) (j : Fin n),
      W (Fin.cast (show n + n = 2 * n by omega) (Fin.natAdd n i)) j = Z i j := by
    intro i j
    set b : Fin (2 * n) := Fin.cast (show n + n = 2 * n by omega) (Fin.natAdd n i) with hb
    have hbval : (b : ℕ) = n + (i : ℕ) := by
      simp only [hb, Fin.val_cast, Fin.val_natAdd]
    have hlt : ¬(b : ℕ) < n := by omega
    have hidx : (⟨(b : ℕ) - n, by have := b.isLt; omega⟩ : Fin n) = i := by
      ext; simp only [hbval]; omega
    simp only [hW, Matrix.of_apply, dite_eq_right hlt, hidx]
  have hsplit : ∀ f : Fin (2 * n) → ℂ,
      ∑ i, f i = (∑ i : Fin n, f (Fin.castLE (by omega) i))
        + ∑ i : Fin n, f (Fin.cast (show n + n = 2 * n by omega) (Fin.natAdd n i)) := by
    intro f
    rw [Fintype.sum_equiv (finCongr (show 2 * n = n + n by omega)) f
      (fun i => f ((finCongr (show 2 * n = n + n by omega)).symm i)) (fun _ => by simp),
      Fin.sum_univ_add]
    have e1 : ∀ i : Fin n, (finCongr (show 2 * n = n + n by omega)).symm (Fin.castAdd n i)
        = Fin.castLE (by omega) i := by
      intro i; apply Fin.ext; simp
    have e2 : ∀ i : Fin n, (finCongr (show 2 * n = n + n by omega)).symm (Fin.natAdd n i)
        = Fin.cast (show n + n = 2 * n by omega) (Fin.natAdd n i) := by
      intro i; apply Fin.ext; simp
    rw [Finset.sum_congr rfl (fun i _ => congrArg f (e1 i)),
      Finset.sum_congr rfl (fun i _ => congrArg f (e2 i))]
  refine ⟨W, ?_, ?_⟩
  · ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have h1 : ∀ i : Fin n,
        star (W (Fin.castLE (by omega) i) j) * W (Fin.castLE (by omega) i) k
          = star (Y i j) * Y i k := by
      intro i; rw [htop i j, htop i k]
    have h2 : ∀ i : Fin n,
        star (W (Fin.cast (show n + n = 2 * n by omega) (Fin.natAdd n i)) j)
          * W (Fin.cast (show n + n = 2 * n by omega) (Fin.natAdd n i)) k
          = star (Z i j) * Z i k := by
      intro i; rw [hbot i j, hbot i k]
    rw [hsplit (fun i => star (W i j) * W i k),
      Finset.sum_congr rfl (fun i _ => h1 i),
      Finset.sum_congr rfl (fun i _ => h2 i)]
    have hsum : (Yᴴ * Y + Zᴴ * Z) j k = ((1 : Matrix (Fin n) (Fin n) ℂ)) j k := by
      rw [hZH, hHdef, add_sub_cancel]
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hsum
  · intro i j
    rw [htop i j, hY, Matrix.smul_apply, smul_eq_mul]

end Qatlib.Concepts.BosonFock.PermAnalysis
