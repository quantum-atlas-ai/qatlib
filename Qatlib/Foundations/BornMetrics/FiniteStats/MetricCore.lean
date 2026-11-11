/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.Defs
import Mathlib.Tactic

/-!
# Bounds for finite measurement distances

This module proves that coarsening measurements decreases the full ℓ¹ distance and that
normalized vectors have measurement distance at most twice their Euclidean separation. It also
establishes selected-column norm estimates, prefix monotonicity, and normalization of unitary
columns, supplying estimates for approximation comparisons associated with [Knill1995].

## Main statements

* `measDist_refine_le`: Compare coarse and fine outcome maps.
* `measDist_le_two_l2`: Control measurement distance by vector distance.
* `column_norm_le_operator`: Bound selected-column norms by the matrix norm.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator NNReal

namespace Qatlib.Foundations.BornMetrics.FiniteStats

/-- The mass of a fiber under a composite outcome map is the sum of the finer fiber masses
mapped to that outcome. -/
theorem fiberProb_comp {N A B : ℕ} (q : Fin N → Fin B) (r : Fin B → Fin A)
    (u : Fin N → ℂ) (a : Fin A) :
    fiberProb (fun i => r (q i)) u a
      = ∑ b : Fin B, if r b = a then fiberProb q u b else 0 := by
  simp only [fiberProb]
  have step1 :
      (∑ b : Fin B, if r b = a then (∑ i : Fin N, if q i = b then ‖u i‖ ^ 2 else 0) else 0)
        = ∑ b : Fin B, ∑ i : Fin N,
            (if r b = a ∧ q i = b then ‖u i‖ ^ 2 else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : r b = a
    · simp [h]
    · simp [h]
  rw [step1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (q i)]
  · simp
  · intro b _ hb
    have hc : ¬ (r b = a ∧ q i = b) := by
      rintro ⟨-, h2⟩
      exact hb h2.symm
    rw [if_neg hc]
  · intro h; exact absurd (Finset.mem_univ (q i)) h

/-- Coarsening an outcome map cannot increase the sum of absolute differences of measurement
masses. -/
theorem measDist_refine_le {N A B : ℕ} (q : Fin N → Fin B) (r : Fin B → Fin A)
    (u v : Fin N → ℂ) :
    measDist (fun i => r (q i)) u v ≤ measDist q u v := by
  have habs (a : Fin A) :
      |fiberProb (fun i => r (q i)) u a - fiberProb (fun i => r (q i)) v a|
        ≤ ∑ b : Fin B, if r b = a then
            |fiberProb q u b - fiberProb q v b| else 0 := by
    rw [fiberProb_comp q r u a, fiberProb_comp q r v a, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : r b = a <;> simp [h]
  refine (Finset.sum_le_sum fun a _ => habs a).trans (le_of_eq ?_)
  unfold measDist
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single (r b)]
  · simp
  · intro a _ ha
    have hc : ¬ (r b = a) := fun h => ha h.symm
    rw [if_neg hc]
  · intro h; exact absurd (Finset.mem_univ (r b)) h

/-- Summing all fiber masses recovers the sum of squared coordinate norms. -/
theorem sum_fiberProb {N A : ℕ} (p : Fin N → Fin A) (u : Fin N → ℂ) :
    ∑ a, fiberProb p u a = ∑ i, ‖u i‖ ^ 2 := by
  unfold fiberProb
  rw [Finset.sum_comm]
  simp

/-- The probability-simplex point obtained by pushing the squared coordinate norms of a
normalized vector through an outcome map. -/
def probabilityVector {N A : ℕ} (p : Fin N → Fin A) (u : Fin N → ℂ)
    (hu : ∑ i, ‖u i‖ ^ 2 = 1) : simplex A := by
  refine ⟨(EuclideanSpace.equiv (Fin A) ℝ).symm (fiberProb p u), ?_, ?_⟩
  · intro a
    change 0 ≤ fiberProb p u a
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  · change ∑ a, fiberProb p u a = 1
    rw [sum_fiberProb, hu]

/-- The simplex distance between the induced probability vectors equals their measurement
distance. -/
theorem probabilityVector_distance {N A : ℕ} (p : Fin N → Fin A)
    (u v : Fin N → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    simplexDistance (probabilityVector p u hu) (probabilityVector p v hv) = measDist p u v := by
  rfl

/-- Measurement distance is at most the sum of absolute differences of the individual squared
coordinate norms. -/
theorem measDist_le_coordinate_mass {N A : ℕ} (p : Fin N → Fin A)
    (u v : Fin N → ℂ) : measDist p u v ≤ ∑ i, |‖u i‖ ^ 2 - ‖v i‖ ^ 2| := by
  simpa [measDist, fiberProb] using measDist_refine_le (fun i : Fin N => i) p u v

/-- For normalized vectors, measurement distance is at most twice the Euclidean norm of their
difference. -/
theorem measDist_le_two_l2 {N A : ℕ} (p : Fin N → Fin A)
    (u v : Fin N → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    measDist p u v ≤ 2 * l2norm (u - v) := by
  let a : Fin N → ℝ := fun i => |‖u i‖ - ‖v i‖|
  let b : Fin N → ℝ := fun i => ‖u i‖ + ‖v i‖
  let d : Fin N → ℝ := fun i => ‖u i - v i‖
  have hA : ∑ i, a i ^ 2 ≤ ∑ i, d i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (abs_norm_sub_norm_le _ _)
  have hB : ∑ i, b i ^ 2 ≤ 4 := by
    calc
      _ ≤ ∑ i, (2 * ‖u i‖ ^ 2 + 2 * ‖v i‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp only [b]
        nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]
      _ = 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu, hv]
        norm_num
  have hD : (∑ i, d i ^ 2) = l2norm (u - v) ^ 2 := by
    exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (d i))).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hsq : (∑ i, a i * b i) ^ 2 ≤ 4 * l2norm (u - v) ^ 2 := by
    calc
      _ ≤ (∑ i, a i ^ 2) * ∑ i, b i ^ 2 := hcs
      _ ≤ (∑ i, d i ^ 2) * 4 := mul_le_mul hA hB
        (Finset.sum_nonneg fun i _ => sq_nonneg (b i))
        (Finset.sum_nonneg fun i _ => sq_nonneg (d i))
      _ = _ := by rw [hD]; ring
  have hsum : ∑ i, a i * b i ≤ 2 * l2norm (u - v) := by
    nlinarith [l2norm_nonneg (u - v)]
  refine (measDist_le_coordinate_mass p u v).trans ?_
  calc
    _ = ∑ i, a i * b i := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [a, b]
      rw [show ‖u i‖ ^ 2 - ‖v i‖ ^ 2 = (‖u i‖ - ‖v i‖) * (‖u i‖ + ‖v i‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ _ := hsum

/-- The maximum norm of columns with indices below `k` is nonnegative. -/
theorem norm2k_nonneg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    0 ≤ norm2k A k := NNReal.coe_nonneg _

/-- For a nonnegative bound, bounding `norm2k A k` is equivalent to bounding every column with
index below `k`. -/
theorem norm2k_le_iff {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (r : ℝ) (hr : 0 ≤ r) :
    norm2k A k ≤ r ↔ ∀ b : Fin N, b.val < k → l2norm (A *ᵥ ket b) ≤ r := by
  unfold norm2k
  change ((Finset.univ.filter (fun b : Fin N => b.val < k)).sup
    (fun b => (⟨l2norm (A *ᵥ ket b), l2norm_nonneg _⟩ : ℝ≥0)) ≤ ⟨r, hr⟩) ↔ _
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- Each column with index below `k` has Euclidean norm at most `norm2k A k`. -/
theorem norm2k_column_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (b : Fin N) (hb : b.val < k) : l2norm (A *ᵥ ket b) ≤ norm2k A k :=
  (norm2k_le_iff A k _ (norm2k_nonneg A k)).mp le_rfl b hb

/-- The Euclidean norm of `A *ᵥ u` is at most the matrix norm of `A` times the Euclidean norm of
`u`. -/
theorem l2norm_mulVec_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (u : Fin N → ℂ) : l2norm (A *ᵥ u) ≤ ‖A‖ * l2norm u := by
  have h := Matrix.l2_opNorm_mulVec A (toEuc u)
  change ‖toEuc (A *ᵥ u)‖ ≤ ‖A‖ * ‖toEuc u‖ at h
  simpa only [norm_toEuc] using h

/-- The maximum norm of columns with indices below `k` is bounded by the matrix norm. -/
theorem column_norm_le_operator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    norm2k A k ≤ ‖A‖ := by
  apply (norm2k_le_iff A k _ (norm_nonneg A)).mpr
  intro b _
  simpa only [l2norm_ket, mul_one] using l2norm_mulVec_le A (ket b)

/-- The maximum column norm is monotone in the cutoff index. -/
theorem column_norm_mono {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) {k l : ℕ}
    (h : k ≤ l) : norm2k A k ≤ norm2k A l := by
  apply (norm2k_le_iff A k _ (norm2k_nonneg A l)).mpr
  intro b hb
  exact norm2k_column_le A l b (lt_of_lt_of_le hb h)

/-- The finite complex Euclidean norm satisfies the triangle inequality. -/
theorem l2norm_add_le {N : ℕ} (u v : Fin N → ℂ) :
    l2norm (u + v) ≤ l2norm u + l2norm v := by
  have h := norm_add_le (toEuc u) (toEuc v)
  change ‖toEuc (u + v)‖ ≤ ‖toEuc u‖ + ‖toEuc v‖ at h
  simpa only [norm_toEuc] using h

/-- The maximum column norm with a fixed cutoff is subadditive under matrix addition. -/
theorem norm2k_add_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    norm2k (A + B) k ≤ norm2k A k + norm2k B k := by
  apply (norm2k_le_iff _ k _ (add_nonneg (norm2k_nonneg A k) (norm2k_nonneg B k))).mpr
  intro b hb
  rw [Matrix.add_mulVec]
  exact (l2norm_add_le _ _).trans
    (add_le_add (norm2k_column_le A k b hb) (norm2k_column_le B k b hb))

/-- Left multiplication by `A` increases the maximum column norm by at most a factor of the
matrix norm of `A`. -/
theorem norm2k_mul_left_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    norm2k (A * B) k ≤ ‖A‖ * norm2k B k := by
  apply (norm2k_le_iff _ k _ (mul_nonneg (norm_nonneg A) (norm2k_nonneg B k))).mpr
  intro b hb
  rw [← Matrix.mulVec_mulVec]
  exact (l2norm_mulVec_le A _).trans
    (mul_le_mul_of_nonneg_left (norm2k_column_le B k b hb) (norm_nonneg A))

/-- Taking an `l`-bit prefix agrees with first taking an `L`-bit prefix and then an `l`-bit
prefix whenever `l ≤ L ≤ n`. -/
theorem prefixMap_comp (n l L : ℕ) (hl : l ≤ n) (hlL : l ≤ L) (hLn : L ≤ n)
    (i : Fin (2 ^ n)) :
    prefixMap n l hl i = prefixMap L l hlL (prefixMap n L hLn i) := by
  apply Fin.ext
  dsimp only [prefixMap]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  omega

/-- Measurement distance on a shorter prefix is at most measurement distance on a longer prefix;
see [Knill, Lemma 2.1][Knill1995]. -/
theorem vPrefix_mono {n l L : ℕ} (hl : l ≤ n) (hlL : l ≤ L) (hLn : L ≤ n)
    (u v : Fin (2 ^ n) → ℂ) : vPrefix n l hl u v ≤ vPrefix n L hLn u v := by
  have hp : prefixMap n l hl = fun i => prefixMap L l hlL (prefixMap n L hLn i) := by
    funext i
    exact prefixMap_comp n l L hl hlL hLn i
  unfold vPrefix
  rw [hp]
  exact measDist_refine_le (prefixMap n L hLn) (prefixMap L l hlL) u v

/-- For a nonnegative bound, bounding `maxPrefixTV` is equivalent to bounding the prefix
distance of every column with index below `k`. -/
theorem maxPrefixTV_le_iff {n l : ℕ} (hl : l ≤ n)
    (U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (k : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    maxPrefixTV n l hl U V k ≤ r ↔ ∀ b : Fin (2 ^ n), b.val < k →
      vPrefix n l hl (U *ᵥ ket b) (V *ᵥ ket b) ≤ r := by
  unfold maxPrefixTV
  change ((Finset.univ.filter (fun b : Fin (2 ^ n) => b.val < k)).sup
    (fun b => (⟨vPrefix n l hl (U *ᵥ ket b) (V *ᵥ ket b), measDist_nonneg _ _ _⟩ : ℝ≥0))
      ≤ ⟨r, hr⟩) ↔ _
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- The maximum prefix measurement distance is nonnegative. -/
theorem maxPrefixTV_nonneg {n l : ℕ} (hl : l ≤ n)
    (U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (k : ℕ) :
    0 ≤ maxPrefixTV n l hl U V k := NNReal.coe_nonneg _

/-- The prefix distance of each column with index below `k` is bounded by `maxPrefixTV`. -/
theorem maxPrefixTV_column_le {n l : ℕ} (hl : l ≤ n)
    (U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (k : ℕ)
    (b : Fin (2 ^ n)) (hb : b.val < k) :
    vPrefix n l hl (U *ᵥ ket b) (V *ᵥ ket b) ≤ maxPrefixTV n l hl U V k :=
  (maxPrefixTV_le_iff hl U V k _ (maxPrefixTV_nonneg hl U V k)).mp le_rfl b hb

/-- Every computational basis column of a unitary matrix has squared coordinate norms summing to
one. -/
theorem unitary_column_mass {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) (b : Fin N) :
    ∑ i, ‖(U *ᵥ ket b) i‖ ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M b b)
    (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hz (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq, hz] at h
  have hc : U *ᵥ ket b = fun i => U i b := by
    ext i
    simp [Matrix.mulVec, dotProduct, ket]
  rw [hc]
  exact_mod_cast h

end Qatlib.Foundations.BornMetrics.FiniteStats
