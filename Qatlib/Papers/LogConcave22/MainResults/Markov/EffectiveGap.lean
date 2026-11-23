/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic

/-!
# Slow spectral mass of a reversible finite chain

Detailed balance produces a Hermitian discriminant with a concrete orthonormal
basis. A power of the original transition matrix evolves the centered square-root
density. The weighted norm of that evolution controls the sample's slow-band mass.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.LogConcave22.MainResults.Markov

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual weighted discriminant `diag(√π) P diag(1/√π)`. -/
def discriminant (P : Matrix I I ℝ) (π : I → ℝ) : Matrix I I ℝ :=
  fun i j => Real.sqrt (π i) * P i j / Real.sqrt (π j)

/-- The nonnegative square-root sample of an actual finite probability law. -/
def sample (μ : I → ℝ) : EuclideanSpace ℝ I := WithLp.toLp 2 fun i => Real.sqrt (μ i)

/-- The stationary-state component is removed with its actual inner-product coefficient. -/
def centered (π μ : I → ℝ) : EuclideanSpace ℝ I :=
  sample μ - (inner ℝ (sample π) (sample μ)) • sample π

omit [Fintype I] [DecidableEq I] in
/-- Positive detailed-balance weights make the constructed discriminant Hermitian. -/
theorem discriminant_hermitian (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ i, 0 < π i) (hrev : ∀ i j, π i * P i j = π j * P j i) :
    (discriminant P π).IsHermitian := by
  change (discriminant P π)ᴴ = discriminant P π
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, discriminant]
  apply (div_eq_div_iff (Real.sqrt_pos.mpr (hπ i)).ne'
    (Real.sqrt_pos.mpr (hπ j)).ne').2
  calc
    _ = π j * P j i := by rw [mul_right_comm, ← pow_two, Real.sq_sqrt (hπ j).le]
    _ = π i * P i j := (hrev i j).symm
    _ = _ := by rw [mul_right_comm, ← pow_two, Real.sq_sqrt (hπ i).le]

/-- Row stochasticity makes the actual square-root stationary law a fixed vector. -/
theorem discriminant_stationary (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ i, 0 < π i) (hrow : ∀ i, ∑ j, P i j = 1) :
    (discriminant P π).toEuclideanLin (sample π) = sample π := by
  apply PiLp.ext
  intro i
  change (∑ j, discriminant P π i j * Real.sqrt (π j)) = Real.sqrt (π i)
  have hterm (j : I) : discriminant P π i j * Real.sqrt (π j) =
      Real.sqrt (π i) * P i j := by
    unfold discriminant
    field_simp [(Real.sqrt_pos.mpr (hπ j)).ne']
  simp_rw [hterm]
  rw [← Finset.mul_sum, hrow, mul_one]

omit [DecidableEq I] in
/-- Nonnegative probabilities give a square-root state with the same total squared mass. -/
theorem sample_norm_sq (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ‖sample μ‖ ^ 2 = ∑ i, μ i := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Real.sq_sqrt (hμ i)

omit [DecidableEq I] in
/-- A genuine probability law has a normalized square-root quantum sample. -/
theorem sample_normalized (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hμsum : ∑ i, μ i = 1) : ‖sample μ‖ = 1 := by
  have hs := sample_norm_sq μ hμ
  rw [hμsum] at hs
  nlinarith [norm_nonneg (sample μ)]

/-- An actual matrix eigenvector remains an eigenvector under every matrix power. -/
theorem eigen_pow (A : Matrix I I ℝ) (v : I → ℝ) (ν : ℝ)
    (hv : A *ᵥ v = ν • v) (t : ℕ) : (A ^ t) *ᵥ v = ν ^ t • v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih,
      smul_smul, pow_succ, mul_comm ν]

/-- Coordinates in the actual Hermitian eigenbasis evolve by the corresponding
eigenvalue power. -/
theorem power_coordinate (A : Matrix I I ℝ) (hA : A.IsHermitian) (t : ℕ)
    (v : EuclideanSpace ℝ I) (j : I) :
    inner ℝ (hA.eigenvectorBasis j) ((A ^ t).toEuclideanLin v) =
      hA.eigenvalues j ^ t * inner ℝ (hA.eigenvectorBasis j) v := by
  have he : (A ^ t).toEuclideanLin (hA.eigenvectorBasis j) =
      hA.eigenvalues j ^ t • hA.eigenvectorBasis j := by
    apply PiLp.ext
    intro i
    exact congrFun (eigen_pow A _ _ (hA.mulVec_eigenvectorBasis j) t) i
  rw [← (Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.pow t))
    (hA.eigenvectorBasis j) v, he, real_inner_smul_left]

/-- Eigenvectors with eigenvalue different from one are orthogonal to an actual
stationary vector. -/
theorem stationary_coordinate (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (s : EuclideanSpace ℝ I) (hs : A.toEuclideanLin s = s) (j : I)
    (hj : hA.eigenvalues j ≠ 1) : inner ℝ (hA.eigenvectorBasis j) s = 0 := by
  have hh := power_coordinate A hA 1 s j
  simp only [pow_one, hs] at hh
  have hm : (hA.eigenvalues j - 1) * inner ℝ (hA.eigenvectorBasis j) s = 0 := by linarith
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hj)

/-- Removing a stationary component does not change any nonstationary coefficient. -/
theorem center_coordinate (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (s v : EuclideanSpace ℝ I) (hs : A.toEuclideanLin s = s) (j : I)
    (hj : hA.eigenvalues j < 1) :
    inner ℝ (hA.eigenvectorBasis j) (v - (inner ℝ s v) • s) =
      inner ℝ (hA.eigenvectorBasis j) v := by
  rw [inner_sub_right, inner_smul_right, stationary_coordinate A hA s hs j hj.ne, mul_zero,
    sub_zero]

/-- Total squared spectral mass in the actual slow nonstationary band. -/
def bandMass (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (v : EuclideanSpace ℝ I) (a : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j < 1),
    (inner ℝ (hA.eigenvectorBasis j) v) ^ 2

/-- The slow-band mass is nonnegative. -/
theorem bandMass_nonneg (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (v : EuclideanSpace ℝ I) (a : ℝ) : 0 ≤ bandMass A hA v a :=
  Finset.sum_nonneg fun _j _hj => sq_nonneg _

/-- Actual square-root-state mixing bounds the actual slow-band spectral mass;
the eigenbasis is derived from the given matrix by the Hermitian spectral theorem. -/
theorem effective_gap (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (s v : EuclideanSpace ℝ I) (hs : A.toEuclideanLin s = s)
    (t : ℕ) (a r : ℝ) (ha : 0 < a)
    (hmix : ‖(A ^ t).toEuclideanLin (v - (inner ℝ s v) • s)‖ ≤ r) :
    bandMass A hA v a ≤ r ^ 2 / a ^ (2 * t) := by
  let w := (A ^ t).toEuclideanLin (v - (inner ℝ s v) • s)
  let B := Finset.univ.filter (fun j => a ≤ hA.eigenvalues j ∧ hA.eigenvalues j < 1)
  have hpoint (j : I) (hj : j ∈ B) :
      a ^ (2 * t) * (inner ℝ (hA.eigenvectorBasis j) v) ^ 2 ≤
        (inner ℝ (hA.eigenvectorBasis j) w) ^ 2 := by
    have hb := (Finset.mem_filter.mp hj).2
    have hp := pow_le_pow_left₀ ha.le hb.1 (2 * t)
    dsimp [w]
    rw [power_coordinate, center_coordinate A hA s v hs j hb.2,
      mul_pow, ← pow_mul, Nat.mul_comm t 2]
    exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
  have hscaled : a ^ (2 * t) * bandMass A hA v a ≤ ‖w‖ ^ 2 := by
    calc
      _ = ∑ j ∈ B, a ^ (2 * t) * (inner ℝ (hA.eigenvectorBasis j) v) ^ 2 :=
        Finset.mul_sum ..
      _ ≤ ∑ j ∈ B, (inner ℝ (hA.eigenvectorBasis j) w) ^ 2 :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ j, (inner ℝ (hA.eigenvectorBasis j) w) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _j _hj _hnot => sq_nonneg _)
      _ = ‖w‖ ^ 2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using hA.eigenvectorBasis.sum_sq_norm_inner_right w
  have hw : ‖w‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg w]
  apply (le_div_iff₀ (pow_pos ha (2 * t))).2
  simpa only [mul_comm] using hscaled.trans hw

/-- The repaired spectral implication specialized to an actual finite reversible
transition and its actual stationary and initial square-root samples. -/
theorem reversible_effective_gap (P : Matrix I I ℝ) (π μ : I → ℝ)
    (hπ : ∀ i, 0 < π i) (hrow : ∀ i, ∑ j, P i j = 1)
    (hrev : ∀ i j, π i * P i j = π j * P j i)
    (t : ℕ) (a r : ℝ) (ha : 0 < a)
    (hmix : ‖((discriminant P π) ^ t).toEuclideanLin (centered π μ)‖ ≤ r) :
    bandMass (discriminant P π) (discriminant_hermitian P π hπ hrev) (sample μ) a ≤
      r ^ 2 / a ^ (2 * t) := by
  exact effective_gap (discriminant P π) (discriminant_hermitian P π hπ hrev)
    (sample π) (sample μ) (discriminant_stationary P π hπ hrow) t a r ha hmix

/-- Positive probability weights give the actual diagonal change of representation. -/
def weight (π : I → ℝ) : Matrix I I ℝ := Matrix.diagonal fun i => Real.sqrt (π i)

/-- The inverse diagonal change of representation. -/
def weightInv (π : I → ℝ) : Matrix I I ℝ := Matrix.diagonal fun i => (Real.sqrt (π i))⁻¹

/-- The entrywise discriminant is exactly the actual diagonal similarity transform. -/
theorem discriminant_similarity (P : Matrix I I ℝ) (π : I → ℝ) :
    discriminant P π = weight π * P * weightInv π := by
  ext i j
  simp [discriminant, weight, weightInv, Matrix.diagonal_mul, Matrix.mul_diagonal,
    div_eq_mul_inv]

/-- The diagonal inverse cancels the square-root probability weights. -/
theorem weight_inverse (π : I → ℝ) (hπ : ∀ i, 0 < π i) :
    weightInv π * weight π = 1 := by
  rw [weightInv, weight, Matrix.diagonal_mul_diagonal]
  simp only [inv_mul_cancel₀ (Real.sqrt_pos.mpr (hπ _)).ne']
  exact Matrix.diagonal_one

/-- The actual discriminant and transition matrix intertwine through the weight matrix. -/
theorem discriminant_intertwines (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ i, 0 < π i) : discriminant P π * weight π = weight π * P := by
  rw [discriminant_similarity, Matrix.mul_assoc, Matrix.mul_assoc,
    weight_inverse π hπ, Matrix.mul_one]

/-- The intertwining identity persists under every actual discrete-time evolution. -/
theorem power_intertwines (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ i, 0 < π i) (t : ℕ) :
    (discriminant P π) ^ t * weight π = weight π * P ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      discriminant_intertwines P π hπ, Matrix.mul_assoc, ← pow_succ']

/-- An ordinary function lifted to the Euclidean square-root-weight representation. -/
def weightedLift (π f : I → ℝ) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 fun i => Real.sqrt (π i) * f i

/-- Weighted Euclidean evolution is exactly the actual Markov transition evolution. -/
theorem power_lift (P : Matrix I I ℝ) (π : I → ℝ)
    (hπ : ∀ i, 0 < π i) (t : ℕ) (f : I → ℝ) :
    ((discriminant P π) ^ t).toEuclideanLin (weightedLift π f) =
      weightedLift π ((P ^ t) *ᵥ f) := by
  have hw : (fun i => Real.sqrt (π i) * f i) = weight π *ᵥ f := by
    funext i
    simp [weight, Matrix.mulVec_diagonal]
  apply PiLp.ext
  intro i
  change (((discriminant P π) ^ t) *ᵥ (fun i => Real.sqrt (π i) * f i)) i =
    Real.sqrt (π i) * ((P ^ t) *ᵥ f) i
  rw [hw, Matrix.mulVec_mulVec, power_intertwines P π hπ,
    ← Matrix.mulVec_mulVec]
  simp [weight, Matrix.mulVec_diagonal]

/-- The square-root density ratio relative to the actual positive stationary law. -/
def sqrtRatio (π μ : I → ℝ) (i : I) : ℝ := Real.sqrt (μ i) / Real.sqrt (π i)

omit [DecidableEq I] in
/-- Centering uses the preserved mean of the square-root density, not the constant one. -/
theorem centered_lift (π μ : I → ℝ) (hπ : ∀ i, 0 < π i) :
    centered π μ = weightedLift π
      (fun i => sqrtRatio π μ i - inner ℝ (sample π) (sample μ)) := by
  apply PiLp.ext
  intro i
  change Real.sqrt (μ i) - inner ℝ (sample π) (sample μ) * Real.sqrt (π i) =
    Real.sqrt (π i) * (Real.sqrt (μ i) / Real.sqrt (π i) - inner ℝ (sample π) (sample μ))
  field_simp [(Real.sqrt_pos.mpr (hπ i)).ne']

omit [DecidableEq I] in
/-- The lifted Euclidean norm is the actual probability-weighted `L2` norm. -/
theorem weighted_norm (π f : I → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    ‖weightedLift π f‖ ^ 2 = ∑ i, π i * f i ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _hi
  change (Real.sqrt (π i) * f i) ^ 2 = π i * f i ^ 2
  rw [mul_pow, Real.sq_sqrt (hπ i)]

/-- The stronger mixing hypothesis has an exact source-space interpretation:
it evolves the centered square-root density with the actual transition matrix. -/
theorem mixing_source_bridge (P : Matrix I I ℝ) (π μ : I → ℝ)
    (hπ : ∀ i, 0 < π i) (t : ℕ) :
    ‖((discriminant P π) ^ t).toEuclideanLin (centered π μ)‖ ^ 2 =
      ∑ i, π i * (((P ^ t) *ᵥ
        (fun j => sqrtRatio π μ j - inner ℝ (sample π) (sample μ))) i) ^ 2 := by
  rw [centered_lift π μ hπ, power_lift P π hπ, weighted_norm π _ (fun i => (hπ i).le)]

/-- A stochastic reversible transition and genuine normalized probability laws
instantiate the repaired estimate with normalized source and initial qsample states. -/
theorem normalized_effective_gap (P : Matrix I I ℝ) (π μ : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I)
    (hπ : ∀ i, 0 < π i) (hπsum : ∑ i, π i = 1)
    (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1)
    (hrev : ∀ i j, π i * P i j = π j * P j i)
    (t : ℕ) (a r : ℝ) (ha : 0 < a)
    (hmix : ‖((discriminant P π) ^ t).toEuclideanLin (centered π μ)‖ ≤ r) :
    ‖sample π‖ = 1 ∧ ‖sample μ‖ = 1 ∧
      bandMass (discriminant P π) (discriminant_hermitian P π hπ hrev) (sample μ) a ≤
        r ^ 2 / a ^ (2 * t) := by
  exact ⟨sample_normalized π (fun i => (hπ i).le) hπsum,
    sample_normalized μ hμ hμsum,
    reversible_effective_gap P π μ hπ (Matrix.sum_row_of_mem_rowStochastic hP) hrev t a r ha hmix⟩

omit [Fintype I] [DecidableEq I] in
/-- Detailed balance identifies the weighted discriminant with the actual
square-root transition compression used by the quantum-walk construction. -/
theorem discriminant_szegedy_entry (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hπ : ∀ i, 0 < π i)
    (hrev : ∀ i j, π i * P i j = π j * P j i) (i j : I) :
    discriminant P π i j = Real.sqrt (P i j * P j i) := by
  have hD : 0 ≤ discriminant P π i j :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hP i j)) (Real.sqrt_nonneg _)
  have hsq : (discriminant P π i j) ^ 2 = P i j * P j i := by
    unfold discriminant
    rw [div_pow, mul_pow, Real.sq_sqrt (hπ i).le, Real.sq_sqrt (hπ j).le]
    apply (div_eq_iff (hπ j).ne').2
    have hb := congrArg (fun x => x * P i j) (hrev i j)
    nlinarith only [hb]
  rw [← hsq, Real.sqrt_sq hD]

/-- The source-sized slow band has mass at most `4r²` under the repaired
square-root-density mixing hypothesis, with a fixed explicit constant. -/
theorem effective_gap_four (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (s v : EuclideanSpace ℝ I) (hs : A.toEuclideanLin s = s)
    (t : ℕ) (ht : 1 ≤ t) (r : ℝ)
    (hmix : ‖(A ^ t).toEuclideanLin (v - (inner ℝ s v) • s)‖ ≤ r) :
    bandMass A hA v (1 - 1 / (2 * (t : ℝ))) ≤ 4 * r ^ 2 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hsmall : 1 / (2 * (t : ℝ)) ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have ha : 0 < 1 - 1 / (2 * (t : ℝ)) := by linarith
  have hbern := one_add_mul_le_pow (a := -(1 / (2 * (t : ℝ)))) (by linarith) t
  have hleft : 1 + (t : ℝ) * (-(1 / (2 * (t : ℝ)))) = 1 / 2 := by
    field_simp
    ring
  rw [hleft] at hbern
  have hpower : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (t : ℝ))) ^ t := by
    simpa only [sub_eq_add_neg] using hbern
  have hquarter : (1 / 4 : ℝ) ≤ (1 - 1 / (2 * (t : ℝ))) ^ (2 * t) := by
    rw [show 2 * t = t * 2 by omega, pow_mul]
    nlinarith
  have hbound := effective_gap A hA s v hs t (1 - 1 / (2 * (t : ℝ))) r ha hmix
  have hprod := (le_div_iff₀ (pow_pos ha (2 * t))).mp hbound
  have hm := bandMass_nonneg A hA v (1 - 1 / (2 * (t : ℝ)))
  have hlow := mul_le_mul_of_nonneg_right hquarter hm
  nlinarith

/-- A reversible finite chain has slow-band mass at most `4r²` when its
centered square-root density mixes to weighted `L²` norm at most `r`.
See the finite spectral implication associated with [Lemma C.7][LogConcave22]. -/
theorem weighted_effective_gap_four (P : Matrix I I ℝ) (π μ : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ i, 0 < π i)
    (hrev : ∀ i j, π i * P i j = π j * P j i)
    (t : ℕ) (ht : 1 ≤ t) (r : ℝ) (hr : 0 ≤ r)
    (hmix : (∑ i, π i * (((P ^ t) *ᵥ
      (fun j => sqrtRatio π μ j - inner ℝ (sample π) (sample μ))) i) ^ 2) ≤ r ^ 2) :
    bandMass (discriminant P π) (discriminant_hermitian P π hπ hrev)
      (sample μ) (1 - 1 / (2 * (t : ℝ))) ≤ 4 * r ^ 2 := by
  have hsq := (mixing_source_bridge P π μ hπ t).trans_le hmix
  have hnorm : ‖((discriminant P π) ^ t).toEuclideanLin (centered π μ)‖ ≤ r :=
    (sq_le_sq₀ (norm_nonneg _) hr).mp hsq
  exact effective_gap_four (discriminant P π) (discriminant_hermitian P π hπ hrev)
    (sample π) (sample μ)
    (discriminant_stationary P π hπ (Matrix.sum_row_of_mem_rowStochastic hP)) t ht r hnorm

end Qatlib.Papers.LogConcave22.MainResults.Markov
