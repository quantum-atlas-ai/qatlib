/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.TransposeAccess.CompactSketchConsumers
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation

/-!
# Counted sketch Gram action and uniform error bounds

This module implements the action of a compact sketch Gram matrix by accumulating contributions
from cached, scaled rows. The construction `sketchGramCounted` computes `Sᴴ *ᵥ (S *ᵥ x)` for `S
= compactSketched d A`, with exact counts of `n * r` row entries and `2 * n * r` multiplications
for the dot products and conjugate scaling. It fits the sampling framework of [ChiaEtAl2022].

For independent samples whose probabilities dominate row energies,
`sketch_gram_actual_fresh_energy_second_moment` bounds the expected squared Frobenius error.
This yields a tail bound that holds simultaneously for the real Rayleigh forms of all normalized
vectors.

## Main statements

* `sketch_gram_actual_cached_rows_and_matrix_free_cost`: exact Gram action and operation counts.
* `sketch_gram_actual_fresh_energy_second_moment`: expected squared Frobenius error.
* `sketch_rayleigh_of_energy_le`: real quadratic form control from Frobenius energy.
* `sketch_gram_all_vectors_rayleigh_tail`: one sampling event controlling every normalized
  vector.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option autoImplicit false
set_option maxRecDepth 4096

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.SketchArith.GramAction
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The list of entries of the row of `A` selected by `d t`, scaled by its real sketch weight. -/
noncomputable def sketchCachedRow {K : Type} {n r : ℕ} (d : Fin r  → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (t : Fin r) : List ℂ := List.ofFn (fun j : Fin n => (d t).2*A (d t).1 j)

/-- The rank-one Gram contribution of a cached row acting on `x`, formed by its dot product with
`x` followed by conjugate scaling. Entries beyond the list length are interpreted as zero. -/
noncomputable def sketchGramRow {n : ℕ} (row : List ℂ) (x : QState (Fin n)) : QState (Fin n) :=
  let dot := ((List.finRange n).map (fun j => row.getD j.val 0*x j)).sum
  fun j => star (row.getD j.val 0)*dot

/-- Accumulates the Gram contributions of the `r` cached sketch rows and records their total
entry count and the dot-product and conjugate-scaling multiplication count. -/
noncomputable def sketchGramCounted {K : Type} {n r : ℕ} (d : Fin r  → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (x : QState (Fin n)) : QState (Fin n) × ℕ × ℕ :=
  (List.finRange r).foldl (fun z t =>
    let row := sketchCachedRow d A t
    (z.1+sketchGramRow row x,z.2.1+row.length,z.2.2+2*row.length)) (0,0,0)

/-- Each cached sketch row contains exactly `n` entries. -/
theorem sketchCachedRow_length {K : Type} {n r : ℕ} (d : Fin r → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (t : Fin r) : (sketchCachedRow d A t).length=n := by
  simp [sketchCachedRow]

/-- Reading coordinate `j` of a cached sketch row returns the selected entry of `A` multiplied
by its sketch weight. -/
theorem sketchCachedRow_get {K : Type} {n r : ℕ} (d : Fin r → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (t : Fin r) (j : Fin n) :
    (sketchCachedRow d A t).getD j.val 0=(d t).2*A (d t).1 j := by
  simp [sketchCachedRow, List.getD, j.isLt]

/-- Each coordinate of a cached row's Gram contribution is its conjugated sketch entry times the
corresponding coordinate of the sketched matrix-vector product. -/
theorem sketchGramRow_apply {K : Type} {n r : ℕ} (d : Fin r → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (x : QState (Fin n)) (t : Fin r) (j : Fin n) :
    sketchGramRow (sketchCachedRow d A t) x j =
      star (compactSketched d A t j) * ((compactSketched d A)*ᵥ x) t := by
  simp only [sketchGramRow, ← Fin.sum_univ_def, sketchCachedRow_get, compactSketched,
    Matrix.mulVec, dotProduct, compactSketchEntry]

/-- Folding over a list of row indices adds their Gram contributions to the initial vector and
increases the two counters by `n * ts.length` and `2 * n * ts.length`. -/
theorem sketchGram_fold {K : Type} {n r : ℕ} (d : Fin r → K × ℝ)
    (A : Matrix K (Fin n) ℂ) (x : QState (Fin n)) (ts : List (Fin r))
    (z : QState (Fin n) × ℕ × ℕ) :
    ts.foldl (fun z t => let row := sketchCachedRow d A t
      (z.1+sketchGramRow row x,z.2.1+row.length,z.2.2+2*row.length)) z =
      (z.1+(ts.map (fun t => sketchGramRow (sketchCachedRow d A t) x)).sum,
        z.2.1+n*ts.length,z.2.2+2*n*ts.length) := by
  induction ts generalizing z with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [sketchCachedRow_length, List.map_cons, List.sum_cons, List.length_cons]
    apply Prod.ext
    · abel
    · apply Prod.ext <;> ring

/-- The counted row algorithm computes `(compactSketched d A)ᴴ *ᵥ ((compactSketched d A) *ᵥ x)`
exactly, with entry count `n * r` and multiplication count `2 * n * r`. -/
theorem sketch_gram_actual_cached_rows_and_matrix_free_cost :
    ∀ (K : Type) (n r : ℕ) (d : Fin r → K × ℝ) (A : Matrix K (Fin n) ℂ) (x : QState (Fin n)),
      (sketchGramCounted d A x).1=(compactSketched d A)ᴴ*ᵥ ((compactSketched d A)*ᵥ x) ∧
      (sketchGramCounted d A x).2.1=n*r ∧ (sketchGramCounted d A x).2.2=2*n*r := by
  intro K n r d A x
  rw [sketchGramCounted, sketchGram_fold]
  simp only [zero_add, List.length_finRange]
  refine ⟨?_, trivial, trivial⟩
  rw [← Fin.sum_univ_def]
  funext j
  simp only [Fintype.sum_apply, sketchGramRow_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply]

/-- For positive sample count and nonzero matrix energy, sampling probabilities that dominate
the row-energy distribution up to `phi ≥ 1` give expected squared Frobenius Gram error at
most `phi * (sketchSquared A)^2 / r`. This is the Gram specialization of the sampling bound
associated with [Chia et al., Lemma 4.4][ChiaEtAl2022]. -/
theorem sketch_gram_actual_fresh_energy_second_moment :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (n r : ℕ) (p : FinDist K)
      (A : Matrix K (Fin n) ℂ) (phi : ℝ), 0 < r → 1 ≤ phi → 0 < sketchSquared A →
      (∀ i, sketchRowSquared A i/(phi*sketchSquared A) ≤ p.prob i) →
      (∑ omega : Fin r → K, p.probOf omega * sketchSquared (sketchProduct p r A A omega-Aᴴ*A)) ≤
        phi*(sketchSquared A)^2/r := by
  intro K _ _ n r p A phi hr hphi hA hdom
  have h := (compact_sketch_unbiased_product_and_variances K (Fin n) (Fin n) p r A A phi
    hr hphi (Or.inl ⟨hA,hdom⟩)).2.1
  simp_rw [sketch_frobenius_norm_sq] at h
  simpa only [pow_two, mul_assoc] using h

/-- The squared Euclidean norm of `E *ᵥ x` is at most the squared Frobenius norm of `E` times
the squared Euclidean norm of `x`. -/
theorem sketch_mulVec_energy_le {n : ℕ} (E : Operator n) (x : QState (Fin n)) :
    ‖toEuclidean_fromVec (E*ᵥ x)‖^2 ≤ sketchSquared E * ‖toEuclidean_fromVec x‖^2 := by
  have hrow (i : Fin n) : ‖(E*ᵥ x) i‖^2 ≤
      (∑ j : Fin n, ‖E i j‖^2)*‖toEuclidean_fromVec x‖^2 := by
    let v : QState (Fin n) := fun j => star (E i j)
    have hc := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec v) (toEuclidean_fromVec x)
    rw [inner_euclidean_fromVec] at hc
    have he : Inner v x=(E*ᵥ x) i := by simp [inner_apply, v, Matrix.mulVec, dotProduct]
    rw [he] at hc
    have hs := pow_le_pow_left₀ (norm_nonneg _) hc 2
    rw [mul_pow, norm_toEuclidean_fromVec_sq] at hs
    simpa only [v, norm_star] using hs
  rw [norm_toEuclidean_fromVec_sq]
  calc
    _ ≤ ∑ i : Fin n, (∑ j : Fin n, ‖E i j‖^2)*‖toEuclidean_fromVec x‖^2 :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [sketchSquared, sketchRowSquared, Complex.normSq_eq_norm_sq]

/-- If `sketchSquared E ≤ eps^2` with `eps > 0`, the absolute real part of the quadratic form of
`E` at `x` is at most `eps` times the squared Euclidean norm of `x`. -/
theorem sketch_rayleigh_of_energy_le {n : ℕ} (E : Operator n) (x : QState (Fin n))
    (eps : ℝ) (heps : 0 < eps) (hE : sketchSquared E ≤ eps^2) :
    |(Inner x (E*ᵥ x)).re| ≤ eps*‖toEuclidean_fromVec x‖^2 := by
  have hc := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec x) (toEuclidean_fromVec (E*ᵥ x))
  rw [inner_euclidean_fromVec] at hc
  have hr := Complex.abs_re_le_norm (Inner x (E*ᵥ x))
  have hs := pow_le_pow_left₀ (abs_nonneg _) (hr.trans hc) 2
  rw [mul_pow] at hs
  have hm := (sketch_mulVec_energy_le E x).trans
    (mul_le_mul_of_nonneg_right hE (sq_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖toEuclidean_fromVec x‖)
  have hnon : 0 ≤ eps*‖toEuclidean_fromVec x‖^2 := by positivity
  nlinarith [abs_nonneg ((Inner x (E*ᵥ x)).re)]

/-- Under the row-energy domination hypotheses, any event on which squared Frobenius Gram error
exceeds `eps^2` has probability at most `phi * (sketchSquared A)^2 / (r * eps^2)`. -/
theorem sketch_gram_energy_event_bound {K : Type} [Fintype K] [DecidableEq K]
    (n r : ℕ) (p : FinDist K) (A : Matrix K (Fin n) ℂ) (phi eps : ℝ)
    (hr : 0 < r) (hphi : 1 ≤ phi) (heps : 0 < eps) (hA : 0 < sketchSquared A)
    (hdom : ∀ i, sketchRowSquared A i/(phi*sketchSquared A) ≤ p.prob i)
    (event : (Fin r → K) → Prop)
    (hbad : ∀ omega, event omega → eps^2 < sketchSquared (sketchProduct p r A A omega-Aᴴ*A)) :
    (∑ omega ∈ Finset.univ.filter event, p.probOf omega) ≤ phi*(sketchSquared A)^2/(r*eps^2) := by
  have hmass (omega : Fin r → K) : 0 ≤ p.probOf omega := Finset.prod_nonneg fun i _ => p.nonneg _
  have hs : (∑ omega ∈ Finset.univ.filter event, p.probOf omega)*eps^2 ≤
      ∑ omega : Fin r → K, p.probOf omega * sketchSquared (sketchProduct p r A A omega-Aᴴ*A) := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ omega ∈ Finset.univ.filter event,
          p.probOf omega * sketchSquared (sketchProduct p r A A omega-Aᴴ*A) := by
        apply Finset.sum_le_sum
        intro omega ho
        exact mul_le_mul_of_nonneg_left (hbad omega (Finset.mem_filter.mp ho).2).le (hmass omega)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun omega _ _ =>
        mul_nonneg (hmass omega) (sketchSquared_nonneg _)
  have hm := sketch_gram_actual_fresh_energy_second_moment K n r p A phi hr hphi hA hdom
  have hd : 0 < eps^2 := sq_pos_of_pos heps
  have h := (le_div_iff₀ hd).mpr (hs.trans hm)
  convert! h using 1
  field_simp

/-- Under the row-energy domination hypotheses, the probability that some normalized vector has
absolute real Gram error above `eps` is at most `phi * (sketchSquared A)^2 / (r * eps^2)`. -/
theorem sketch_gram_all_vectors_rayleigh_tail :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (n r : ℕ) (p : FinDist K)
      (A : Matrix K (Fin n) ℂ) (phi eps : ℝ), 0 < r → 1 ≤ phi → 0 < eps → 0 < sketchSquared A →
      (∀ i, sketchRowSquared A i/(phi*sketchSquared A) ≤ p.prob i) →
      (∑ omega ∈ Finset.univ.filter (fun omega : Fin r → K =>
        ∃ x : QState (Fin n), Normalized x ∧ eps < |(Inner x ((sketchProduct p r A A omega-Aᴴ*A)*ᵥ x)).re|),
        p.probOf omega) ≤ phi*(sketchSquared A)^2/(r*eps^2) := by
  intro K _ _ n r p A phi eps hr hphi heps hA hdom
  apply sketch_gram_energy_event_bound n r p A phi eps hr hphi heps hA hdom
  intro omega ho
  obtain ⟨x,hx,hbad⟩ := ho
  by_contra h
  have hb :=
      sketch_rayleigh_of_energy_le (sketchProduct p r A A omega-Aᴴ*A) x eps heps (le_of_not_gt h)
  rw [(normalized_iff_norm_toEuclidean_fromVec x).mp hx] at hb
  norm_num at hb
  exact not_lt_of_ge hb hbad
end Qatlib.Concepts.SketchArith.GramAction
