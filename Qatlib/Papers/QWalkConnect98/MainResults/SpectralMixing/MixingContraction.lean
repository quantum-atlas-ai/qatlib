/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator.WalkOperatorAction
import Mathlib.Analysis.Complex.Exponential

/-!
# Mass preservation and spectral contraction

`RegularDegree` states the common vertex degree, and `SpectralGap` specifies a quantitative
Euclidean contraction on vectors supported in one component and summing to zero. The module
proves mass preservation, stationarity of `uniformOn`, and iteration of this contraction.

The initial difference `basisVec u - uniformOn G u` has squared norm `1 - 1 / compSize G u`,
giving a strict norm bound by one. These results support the connectivity analysis in
[Watrous1998].

## Main statements

* `walkM_mulVec_uniformOn`: the component-uniform vector is stationary.
* `l2norm_walkM_pow_le`: iterate the assumed component contraction.
* `l2norm_basisVec_sub_uniformOn_sq`: compute the squared initial error norm.

## References

* [Watrous, 1998][Watrous1998]
-/

namespace Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing

open Finset
open Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
open scoped BigOperators Matrix

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The predicate that every vertex has degree `d`, with the finite neighbor count viewed as a
real number. -/
def RegularDegree (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Prop :=
  ∀ v : V, ((G.neighborFinset v).card : ℝ) = d

/-- The walk coefficients satisfy `walkA d + walkB d * d = 1`. -/
theorem walkA_add_walkB_mul (d : ℝ) : walkA d + walkB d * d = 1 := by
  rw [walkA, walkB]
  by_cases h : d + 1 = 0
  · have hd : d = -1 := by linarith
    subst hd
    norm_num
  · field_simp
    ring

/-- The sum of a column of the adjacency matrix is the degree of its vertex. -/
theorem sum_adjMatrix_column (G : SimpleGraph V) [DecidableRel G.Adj] (j : V) :
    (∑ i, adjMatrix G i j) = ((G.neighborFinset j).card : ℝ) := by
  have h : (∑ i, adjMatrix G i j) =
      ∑ i ∈ Finset.univ.filter (fun i => G.Adj i j), (1 : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hadj : G.Adj i j <;> simp [adjMatrix, hadj]
  rw [h, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun i => G.Adj i j)) = G.neighborFinset j := by
    apply Finset.ext
    intro i
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hcard]

/-- For a regular graph, every column of `walkM G d` sums to one. -/
theorem walkM_column_sum (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (j : V) :
    (∑ i, walkM G d i j) = 1 := by
  calc (∑ i, walkM G d i j)
      = ∑ i, (walkA d * (if i = j then (1 : ℝ) else 0) +
          walkB d * adjMatrix G i j) := by
        apply Finset.sum_congr rfl
        intro i _
        simp [walkM, Pi.add_apply, Pi.smul_apply, Matrix.one_apply]
    _ = walkA d + walkB d * ((G.neighborFinset j).card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_adjMatrix_column G j,
          Finset.sum_ite_eq', if_pos (Finset.mem_univ j), mul_one]
    _ = 1 := by
        rw [hreg j]
        exact walkA_add_walkB_mul d

/-- On a regular graph, applying `walkM` preserves the sum of a real vector's coordinates. -/
theorem sum_walkM_mulVec_eq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (x : V → ℝ) :
    (∑ v, (walkM G d *ᵥ x) v) = ∑ v, x v := by
  calc (∑ v, (walkM G d *ᵥ x) v)
      = ∑ j, (∑ i, walkM G d i j) * x j := by
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        simp [Finset.sum_mul]
    _ = ∑ j, x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [walkM_column_sum G hreg j, one_mul]

/-- Every power of `walkM` on a regular graph preserves the sum of a real vector's coordinates. -/
theorem sum_walkM_pow_mulVec_eq (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (k : ℕ) :
    ∀ x : V → ℝ, (∑ v, ((walkM G d ^ k) *ᵥ x) v) = ∑ v, x v := by
  induction k with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [pow_succ', ← Matrix.mulVec_mulVec,
      sum_walkM_mulVec_eq G hreg ((walkM G d ^ n) *ᵥ x), ih x]

/-- The coordinates of the uniform vector on the component of `u` sum to one. -/
theorem sum_uniformOn (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (∑ v, uniformOn G u v) = 1 := by
  classical
  have h : (∑ v, uniformOn G u v) = ∑ v ∈ compSet G u, (1 / (compSize G u : ℝ)) := by
    rw [compSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hr : G.Reachable u v
    · simp [uniformOn, hr]
    · simp [uniformOn, hr]
  rw [h, Finset.sum_const, nsmul_eq_mul]
  rw [mul_one_div]
  exact div_self (ne_of_gt (compSize_pos G u))

/-- The uniform vector on the component of `u` is fixed by `walkM` on a regular graph. -/
theorem walkM_mulVec_uniformOn (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (u : V) :
    walkM G d *ᵥ uniformOn G u = uniformOn G u := by
  classical
  funext v
  rw [walkM_mulVec_apply]
  by_cases hv : G.Reachable u v
  · have hterm : ∀ w ∈ G.neighborFinset v, uniformOn G u w = 1 / (compSize G u : ℝ) := by
      intro w hw
      have hreach : G.Reachable u w := hv.trans (reachable_of_mem_neighborFinset hw).symm
      simp [uniformOn, hreach]
    have hsum : (∑ w ∈ G.neighborFinset v, uniformOn G u w) =
        d * (1 / (compSize G u : ℝ)) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hreg v]
    rw [hsum, uniformOn, if_pos hv]
    calc walkA d * (1 / (compSize G u : ℝ)) +
          walkB d * (d * (1 / (compSize G u : ℝ)))
        = (walkA d + walkB d * d) * (1 / (compSize G u : ℝ)) := by ring
      _ = 1 * (1 / (compSize G u : ℝ)) := by rw [walkA_add_walkB_mul]
      _ = 1 / (compSize G u : ℝ) := by ring
  · have hsum : (∑ w ∈ G.neighborFinset v, uniformOn G u w) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hreach : ¬ G.Reachable u w :=
        fun hr => hv (hr.trans (reachable_of_mem_neighborFinset hw))
      simp [uniformOn, hreach]
    rw [hsum, uniformOn, if_neg hv]
    ring

/-- Every power of `walkM` on a regular graph fixes the uniform vector on the component of `u`. -/
theorem walkM_pow_mulVec_uniformOn (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (k : ℕ) (u : V) :
    (walkM G d ^ k) *ᵥ uniformOn G u = uniformOn G u := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, walkM_mulVec_uniformOn G hreg]

/-- The predicate that `walkM` contracts every zero-sum vector supported in the component of `u`
by the factor `1 - 8 / (d * (d + 1) ^ 2 * compSize G u ^ 2)`. -/
def SpectralGap (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (u : V) : Prop :=
  ∀ x : V → ℝ, (∀ v, ¬ G.Reachable u v → x v = 0) → (∑ v, x v = 0) →
    l2norm (walkM G d *ᵥ x) ≤
      (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) * l2norm x

/-- The `SpectralGap` hypothesis gives its specified contraction bound for a zero-sum vector
supported in the component of `u`. -/
theorem component_spectral_contraction (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℝ} (u : V) (hgap : SpectralGap G d u) (x : V → ℝ)
    (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) :
    l2norm (walkM G d *ᵥ x) ≤
      (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) * l2norm x :=
  hgap x hsupp hsum

/-- A component with one vertex satisfies `SpectralGap` for every real degree parameter. -/
theorem spectralGap_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (u : V)
    (hcard : compSize G u = 1) : SpectralGap G d u := by
  intro x hsupp hsum
  have hcomp : compSet G u = {u} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hu : u ∈ compSet G u := self_mem_compSet G u
    have hau : a = u := by
      have hmem : u ∈ ({a} : Finset V) := ha ▸ hu
      rw [Finset.mem_singleton] at hmem
      exact hmem.symm
    rw [ha, hau]
  have hzero : x = 0 := by
    funext v
    by_cases hv : v = u
    · rw [hv]
      have hsum' : (∑ w, x w) = x u := by
        rw [Finset.sum_eq_single u]
        · intro w _ hw
          apply hsupp w
          intro hreach
          have hmem : w ∈ compSet G u := mem_compSet.mpr hreach
          rw [hcomp] at hmem
          exact hw (by simpa using hmem)
        · intro hnot
          exact absurd (Finset.mem_univ u) hnot
      rw [← hsum', hsum]
      simp
    · apply hsupp v
      intro hreach
      have hmem : v ∈ compSet G u := mem_compSet.mpr hreach
      rw [hcomp] at hmem
      exact hv (by simpa using hmem)
  rw [hzero]
  have hmul : walkM G d *ᵥ (0 : V → ℝ) = 0 := Matrix.mulVec_zero _
  rw [hmul]
  simp [l2norm]

/-- For `2 ≤ d`, the component contraction factor `1 - 8 / (d * (d + 1) ^ 2 * compSize G u ^ 2)`
is positive. -/
theorem spectral_coeff_pos (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hd : 2 ≤ d) (u : V) :
    (0 : ℝ) < 1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hn1 : (1 : ℝ) ≤ (compSize G u : ℝ) := by
    exact_mod_cast compSet_pos G u
  have h9 : (9 : ℝ) ≤ (d + 1) ^ 2 := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ d + 4) (by linarith : (0 : ℝ) ≤ d - 2)
    nlinarith [h]
  have hsq : (1 : ℝ) ≤ (compSize G u : ℝ) ^ 2 := by
    have h := mul_nonneg (by linarith : (0 : ℝ) ≤ (compSize G u : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (compSize G u : ℝ) + 1)
    nlinarith [h]
  have h18a : (18 : ℝ) ≤ d * (d + 1) ^ 2 := by
    have := mul_le_mul hd h9 (by norm_num) hd0.le
    nlinarith [this]
  have h18 : (18 : ℝ) ≤ d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2 := by
    have := mul_le_mul h18a hsq (by norm_num) (by linarith)
    nlinarith [this]
  have hden : (0 : ℝ) < d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) < (d + 1) ^ 2 := by positivity
    have h2 : (0 : ℝ) < (compSize G u : ℝ) ^ 2 := by positivity
    exact mul_pos (mul_pos hd0 h1) h2
  have hfrac : 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) ≤ 4 / 9 := by
    rw [div_le_iff₀ hden]
    nlinarith [h18]
  linarith

/-- For a regular graph of degree at least two satisfying `SpectralGap`, the norm after `k`
steps of a component-supported zero-sum vector is bounded by the `k`th power of the
contraction factor times its initial norm. -/
theorem l2norm_walkM_pow_le (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hreg : RegularDegree G d) (hd : 2 ≤ d) (u : V) (hgap : SpectralGap G d u)
    (x : V → ℝ)
    (hsupp : ∀ v, ¬ G.Reachable u v → x v = 0) (hsum : ∑ v, x v = 0) (k : ℕ) :
    l2norm ((walkM G d ^ k) *ᵥ x) ≤
      (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ k * l2norm x := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hsupp' : ∀ v, ¬ G.Reachable u v → ((walkM G d ^ n) *ᵥ x) v = 0 :=
      walkM_pow_apply_eq_zero G d u hsupp n
    have hsum' : ∑ v, ((walkM G d ^ n) *ᵥ x) v = ∑ v, x v :=
      sum_walkM_pow_mulVec_eq G hreg n x
    have hcontr := hgap ((walkM G d ^ n) *ᵥ x) hsupp' (by rw [hsum', hsum])
    have hρ : (0 : ℝ) ≤ 1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2) :=
      (spectral_coeff_pos G hd u).le
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    calc l2norm (walkM G d *ᵥ ((walkM G d ^ n) *ᵥ x))
        ≤ (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) *
            l2norm ((walkM G d ^ n) *ᵥ x) := hcontr
      _ ≤ (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) *
            ((1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ n * l2norm x) := by
        apply mul_le_mul_of_nonneg_left ih hρ
      _ = (1 - 8 / (d * (d + 1) ^ 2 * (compSize G u : ℝ) ^ 2)) ^ (n + 1) * l2norm x := by
        rw [pow_succ']
        ring

/-- The squared Euclidean norm of `basisVec u - uniformOn G u` is `1 - 1 / compSize G u`. -/
theorem l2norm_basisVec_sub_uniformOn_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) :
    l2norm (basisVec u - uniformOn G u) ^ 2 = 1 - 1 / (compSize G u : ℝ) := by
  classical
  have hpt : ∀ v : V, (basisVec u - uniformOn G u) v ^ 2 =
      (if v ∈ compSet G u then
        ((if v = u then (1 : ℝ) else 0) - 1 / (compSize G u : ℝ)) ^ 2 else 0) := by
    intro v
    by_cases hv : v ∈ compSet G u
    · have hreach : G.Reachable u v := mem_compSet.mp hv
      have hu : uniformOn G u v = 1 / (compSize G u : ℝ) := by simp [uniformOn, hreach]
      rw [Pi.sub_apply, hu, if_pos hv]
      simp [basisVec]
    · have hreach : ¬ G.Reachable u v := fun h => hv (mem_compSet.mpr h)
      have hne : v ≠ u := fun h => hreach (h ▸ SimpleGraph.Reachable.rfl)
      have hu : uniformOn G u v = 0 := by simp [uniformOn, hreach]
      rw [Pi.sub_apply, hu, if_neg hv, basisVec_apply_of_ne hne]
      ring
  rw [l2norm_sq_eq]
  simp only [hpt, Finset.sum_ite_mem, Finset.univ_inter]
  have hmem : u ∈ compSet G u := self_mem_compSet G u
  have hpos : 0 < compSize G u := compSet_pos G u
  have herase : (∑ v ∈ (compSet G u).erase u,
      ((if v = u then (1 : ℝ) else 0) - 1 / (compSize G u : ℝ)) ^ 2) =
      ((compSize G u : ℝ) - 1) * (1 / (compSize G u : ℝ)) ^ 2 := by
    have hconst : ∀ v ∈ (compSet G u).erase u,
        ((if v = u then (1 : ℝ) else 0) - 1 / (compSize G u : ℝ)) ^ 2 =
          (1 / (compSize G u : ℝ)) ^ 2 := by
      intro v hv
      have hne : v ≠ u := Finset.ne_of_mem_erase hv
      rw [if_neg hne]
      ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem hmem]
    have h1 : 1 ≤ (compSet G u).card := Nat.succ_le_of_lt (compSet_pos G u)
    have hcast : (((compSet G u).card - 1 : ℕ) : ℝ) = (compSize G u : ℝ) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      simp [compSize]
    rw [hcast]
  have hsplit : (∑ v ∈ compSet G u,
        ((if v = u then (1 : ℝ) else 0) - 1 / (compSize G u : ℝ)) ^ 2)
      = (1 - 1 / (compSize G u : ℝ)) ^ 2 +
        ((compSize G u : ℝ) - 1) * (1 / (compSize G u : ℝ)) ^ 2 := by
    rw [← Finset.add_sum_erase (compSet G u)
      (fun v => ((if v = u then (1 : ℝ) else 0) - 1 / (compSize G u : ℝ)) ^ 2) hmem]
    rw [herase]
    simp
  rw [hsplit]
  have hn : (compSize G u : ℝ) ≠ 0 := ne_of_gt (compSize_pos G u)
  field_simp
  ring

/-- The Euclidean norm of `basisVec u - uniformOn G u` is at most one. -/
theorem l2norm_basisVec_sub_uniformOn_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) :
    l2norm (basisVec u - uniformOn G u) ≤ 1 := by
  have hS : (∑ i, (basisVec u - uniformOn G u) i ^ 2) ≤ 1 := by
    have hsq := l2norm_basisVec_sub_uniformOn_sq G u
    rw [l2norm_sq_eq] at hsq
    have hfrac : (0 : ℝ) < 1 / (compSize G u : ℝ) := by
      have hp : (0 : ℝ) < (compSize G u : ℝ) := compSize_pos G u
      positivity
    linarith
  calc l2norm (basisVec u - uniformOn G u)
      = Real.sqrt (∑ i, (basisVec u - uniformOn G u) i ^ 2) := rfl
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hS
    _ = 1 := Real.sqrt_one

/-- The Euclidean norm of `basisVec u - uniformOn G u` is strictly less than one. -/
theorem l2norm_basisVec_sub_uniformOn_lt_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) :
    l2norm (basisVec u - uniformOn G u) < 1 := by
  have hS : (∑ i, (basisVec u - uniformOn G u) i ^ 2) < 1 := by
    have hsq := l2norm_basisVec_sub_uniformOn_sq G u
    rw [l2norm_sq_eq] at hsq
    have hfrac : (0 : ℝ) < 1 / (compSize G u : ℝ) := by
      have hp : (0 : ℝ) < (compSize G u : ℝ) := compSize_pos G u
      positivity
    linarith
  calc l2norm (basisVec u - uniformOn G u)
      = Real.sqrt (∑ i, (basisVec u - uniformOn G u) i ^ 2) := rfl
    _ < 1 := by
        rw [Real.sqrt_lt' one_pos]
        simpa using hS

end

end Qatlib.Papers.QWalkConnect98.MainResults.SpectralMixing
