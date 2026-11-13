/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarCompact
import Qatlib.Papers.Trainability23.HaarAverages.HaarIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Haar unitary moments and tensor averages

This module constructs normalized Haar measure `haarUnitaryGroup` on finite complex unitary
groups and computes its matrix-entry second moments. It defines the conjugation averages
`haarKroneckerAverage` and `haarTensorAverage`, proves their invariance, and evaluates
single-qubit pure-state moments through four tensor copies. See [RudolphEtAl2024].

## Main statements

* `haar_entryPair_eq`: orthogonality formula for a unitary entry and a conjugate entry.
* `haarKroneckerAverage_eq_one_plus_swap`: the two-copy average under the stated trace
  conditions.
* `haarTensorAverage_three_eq_permSum` and `haarTensorAverage_four_eq_permSum`: permutation-sum
  formulas for the third and fourth pure-state moments.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Papers.Trainability23.HaarAverages

open scoped BigOperators Matrix

noncomputable section MeasurableInstances

local instance instMeasurableSpaceMatrix (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelSpaceMatrix (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

/-- Normalized Haar measure on the unitary group of complex matrices indexed by `n`. -/
noncomputable def haarUnitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    MeasureTheory.Measure (Matrix.unitaryGroup n ℂ) :=
  MeasureTheory.Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup n ℂ))

/-- The measure `haarUnitaryGroup n` is a Haar measure. -/
theorem haarUnitaryGroup_isHaarMeasure (n : Type*) [Fintype n] [DecidableEq n] :
    (haarUnitaryGroup n).IsHaarMeasure := by
  rw [haarUnitaryGroup]
  infer_instance

/-- The normalized unitary Haar measure assigns mass one to the whole group. -/
theorem haarUnitaryGroup_univ (n : Type*) [Fintype n] [DecidableEq n] :
    haarUnitaryGroup n Set.univ = 1 := by
  have h : (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup n ℂ)).carrier = Set.univ := by
    simp
  rw [haarUnitaryGroup, ← h]
  exact MeasureTheory.Measure.haarMeasure_self

/-- The product of a unitary matrix entry and a conjugate entry is Haar integrable. -/
theorem haarIntegrable_entryPair (n : Type*) [Fintype n] [DecidableEq n] (a b k l : n) :
    MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) k a * star ((V : Matrix n n ℂ) l b))
      (haarUnitaryGroup n) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup n) :=
    ⟨by rw [haarUnitaryGroup_univ n]; exact ENNReal.one_lt_top⟩
  have h1 : Continuous fun V : Matrix.unitaryGroup n ℂ => (V : Matrix n n ℂ) k a := by
    change Continuous fun V : Matrix.unitaryGroup n ℂ => (V : n → n → ℂ) k a
    have hk : Continuous fun p : n → n → ℂ => p k := continuous_apply k
    have ha : Continuous fun q : n → ℂ => q a := continuous_apply a
    exact (ha.comp hk).comp continuous_subtype_val
  have h2 : Continuous fun V : Matrix.unitaryGroup n ℂ => (V : Matrix n n ℂ) l b := by
    change Continuous fun V : Matrix.unitaryGroup n ℂ => (V : n → n → ℂ) l b
    have hl : Continuous fun p : n → n → ℂ => p l := continuous_apply l
    have hb : Continuous fun q : n → ℂ => q b := continuous_apply b
    exact (hb.comp hl).comp continuous_subtype_val
  refine MeasureTheory.Integrable.of_bound
    (Continuous.aestronglyMeasurable (h1.mul (continuous_star.comp h2))) 1 ?_
  filter_upwards with V
  rw [norm_mul, norm_star]
  have hk := unitaryGroup_entry_norm_le_one V.2 k a
  have hl := unitaryGroup_entry_norm_le_one V.2 l b
  nlinarith [norm_nonneg ((V : Matrix n n ℂ) k a), norm_nonneg ((V : Matrix n n ℂ) l b)]

/-- Every entry of the unitary conjugate of a matrix unit is Haar integrable. -/
theorem haarIntegrable_conjSingle (n : Type*) [Fintype n] [DecidableEq n] (a b k l : n) :
    MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup n ℂ =>
        ((V : Matrix n n ℂ) * Matrix.single a b (1 : ℂ) * star (V : Matrix n n ℂ)) k l)
      (haarUnitaryGroup n) := by
  refine (haarIntegrable_entryPair n a b k l).congr ?_
  filter_upwards with V
  exact (conj_single_apply (V : Matrix n n ℂ) a b k l).symm

/-- Expands an entry of a unitary product times a conjugate entry as a double sum over the
entries of its factors. -/
theorem unitaryGroup_mul_entry_expand (n : Type*) [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n ℂ) (a b i j : n) :
    (((U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) i a *
        star (((U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) j b))
      = ∑ l, ∑ k, (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
          ((V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b)) := by
  have hcoe : ((U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)
      = (U : Matrix n n ℂ) * (V : Matrix n n ℂ) := rfl
  rw [hcoe, Matrix.mul_apply, Matrix.mul_apply, star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul]
  ring

/-- Expresses invariance of the Haar entry-pair integral under left multiplication by a fixed
unitary as a double-sum identity. -/
theorem haar_entryPair_invariant (n : Type*) [Fintype n] [DecidableEq n] (a b : n)
    (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b))
      = ∑ l, ∑ k, (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
          MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
            (V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b)) := by
  haveI : (haarUnitaryGroup n).IsMulLeftInvariant := by
    rw [haarUnitaryGroup]
    infer_instance
  have hint : ∀ l k : n, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup n ℂ =>
        (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
          ((V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b)))
      (haarUnitaryGroup n) :=
    fun l k => (haarIntegrable_entryPair n a b l k).const_mul _
  calc MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b))
      = MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          ((U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) i a *
            star (((U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) j b)) :=
        (MeasureTheory.integral_mul_left_eq_self _ U).symm
    _ = MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          ∑ l, ∑ k, (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
            ((V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b))) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
          fun V => unitaryGroup_mul_entry_expand n U V a b i j)
    _ = ∑ l, MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          ∑ k, (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
            ((V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b))) :=
        MeasureTheory.integral_finsetSum Finset.univ
          (fun l _ => MeasureTheory.integrable_finsetSum Finset.univ fun k _ => hint l k)
    _ = ∑ l, ∑ k, MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
            ((V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b))) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        exact MeasureTheory.integral_finsetSum Finset.univ fun k _ => hint l k
    _ = ∑ l, ∑ k, (U : Matrix n n ℂ) i l * star ((U : Matrix n n ℂ) j k) *
          MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
            (V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b)) := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
        exact MeasureTheory.integral_const_mul _ _

/-- Conjugation by a diagonal matrix multiplies the `(i, j)` entry by `d i * star (d j)`. -/
theorem diagonal_conj_apply (n : Type*) [Fintype n] [DecidableEq n] (d : n → ℂ)
    (M : Matrix n n ℂ) (i j : n) :
    (Matrix.diagonal d * M * star (Matrix.diagonal d)) i j = d i * M i j * star (d j) := by
  have hstar : star (Matrix.diagonal d) = Matrix.diagonal (star d) := by
    rw [show star (Matrix.diagonal d) = (Matrix.diagonal d)ᴴ from rfl]
    exact Matrix.diagonal_conjTranspose d
  rw [hstar, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- The diagonal matrix with a single negative sign and all other diagonal entries one is
unitary. -/
theorem signDiagonal_mem_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] (i : n) :
    Matrix.diagonal (fun x : n => if x = i then (-1 : ℂ) else 1) ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.sum_eq_single x]
    · simp only [Matrix.star_apply, Matrix.diagonal_apply, if_pos rfl]
      by_cases hx : x = i <;> simp [hx]
    · intro k _ hk
      simp [Matrix.star_apply, Matrix.diagonal_apply, Ne.symm hk]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkx : k = x
    · subst hkx
      simp [Matrix.star_apply, Matrix.diagonal_apply, hxy, Ne.symm hxy]
    · simp [Matrix.star_apply, Matrix.diagonal_apply, hkx, Ne.symm hkx]

/-- The Haar integral of an entry-pair product vanishes when its two row indices differ. -/
theorem haar_entryPair_offdiag (n : Type*) [Fintype n] [DecidableEq n] (a b : n) {i j : n}
    (hij : i ≠ j) :
    MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b)) = 0 := by
  set d : n → ℂ := fun x => if x = i then -1 else 1 with hd
  have hunit : Matrix.diagonal d ∈ Matrix.unitaryGroup n ℂ := by
    rw [show Matrix.diagonal d =
      Matrix.diagonal (fun x : n => if x = i then (-1 : ℂ) else 1) from rfl]
    exact signDiagonal_mem_unitaryGroup n i
  have hcollapse : ∑ l, ∑ k, Matrix.diagonal d i l * star (Matrix.diagonal d j k) *
        MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b))
      = d i * star (d j) * MeasureTheory.integral (haarUnitaryGroup n)
          (fun V : Matrix.unitaryGroup n ℂ =>
            (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b)) := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [Matrix.diagonal_apply, if_pos rfl, Matrix.diagonal_apply, if_pos rfl]
      · intro k _ hk
        simp [Matrix.diagonal_apply, Ne.symm hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    · intro l _ hl
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [Matrix.diagonal_apply, Ne.symm hl]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hval : d i * star (d j) = (-1 : ℂ) := by
    rw [hd]
    simp [Ne.symm hij]
  have hmain := (haar_entryPair_invariant n a b ⟨Matrix.diagonal d, hunit⟩ i j).trans hcollapse
  rw [hval, neg_one_mul] at hmain
  have h2 : (2 : ℂ) * MeasureTheory.integral (haarUnitaryGroup n)
      (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b)) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hmain]
    ring
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Unitary conjugation preserves the trace of a complex matrix. -/
theorem trace_conj_unitary (n : Type*) [Fintype n] [DecidableEq n]
    (V : Matrix.unitaryGroup n ℂ) (P : Matrix n n ℂ) :
    ((V : Matrix n n ℂ) * P * star (V : Matrix n n ℂ)).trace = P.trace := by
  rw [Matrix.trace_mul_cycle]
  have h : star (V : Matrix n n ℂ) * (V : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp V.2
  rw [h, one_mul]

/-- The permutation matrix whose `(a, b)` entry is one exactly when `b = σ a`. -/
def permMatrix (n : Type*) [DecidableEq n] (σ : Equiv.Perm n) : Matrix n n ℂ :=
  Matrix.of fun a b => if b = σ a then 1 else 0

/-- Every permutation matrix `permMatrix n σ` is unitary. -/
theorem permMatrix_mem_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    permMatrix n σ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single (σ a)]
    · simp [permMatrix, Matrix.of_apply, Matrix.star_apply]
    · intro k _ hk
      simp [permMatrix, Matrix.of_apply, Matrix.star_apply, hk]
    · intro h
      exact absurd (Finset.mem_univ (σ a)) h
  · rw [if_neg hab]
    have hne : σ a ≠ σ b := fun h => hab (σ.injective h)
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = σ a
    · subst hk
      simp [permMatrix, Matrix.of_apply, Matrix.star_apply, hne]
    · simp [permMatrix, Matrix.of_apply, Matrix.star_apply, hk, hne]

/-- Simultaneously permuting the row indices leaves the Haar entry-pair integral unchanged. -/
theorem haar_entryPair_perm (n : Type*) [Fintype n] [DecidableEq n] (a b : n) (σ : Equiv.Perm n)
    (i j : n) :
    MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b))
      = MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) (σ i) a * star ((V : Matrix n n ℂ) (σ j) b)) := by
  have hunit : permMatrix n σ ∈ Matrix.unitaryGroup n ℂ := permMatrix_mem_unitaryGroup n σ
  have hcollapse : ∑ l, ∑ k, permMatrix n σ i l * star (permMatrix n σ j k) *
        MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (V : Matrix n n ℂ) l a * star ((V : Matrix n n ℂ) k b))
      = MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (V : Matrix n n ℂ) (σ i) a * star ((V : Matrix n n ℂ) (σ j) b)) := by
    rw [Finset.sum_eq_single (σ i)]
    · rw [Finset.sum_eq_single (σ j)]
      · simp [permMatrix, Matrix.of_apply]
      · intro k _ hk
        simp [permMatrix, Matrix.of_apply, hk]
      · intro h
        exact absurd (Finset.mem_univ (σ j)) h
    · intro l _ hl
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [permMatrix, Matrix.of_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ (σ i)) h
  exact (haar_entryPair_invariant n a b ⟨permMatrix n σ, hunit⟩ i j).trans hcollapse

/-- Summing the diagonal row entry-pair integrals gives the trace of the corresponding matrix
unit. -/
theorem haar_entryPair_trace (n : Type*) [Fintype n] [DecidableEq n] (a b : n) :
    ∑ i, MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) i b))
      = (Matrix.single a b (1 : ℂ)).trace := by
  rw [← MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => haarIntegrable_entryPair n a b i i)]
  rw [show (fun V : Matrix.unitaryGroup n ℂ => ∑ i, (V : Matrix n n ℂ) i a *
        star ((V : Matrix n n ℂ) i b))
      = fun V : Matrix.unitaryGroup n ℂ =>
          ((V : Matrix n n ℂ) * Matrix.single a b (1 : ℂ) * star (V : Matrix n n ℂ)).trace from
    funext fun V => by
      simp only [Matrix.trace]
      exact Finset.sum_congr rfl fun i _ =>
        (conj_single_apply (V : Matrix n n ℂ) a b i i).symm]
  rw [show (fun V : Matrix.unitaryGroup n ℂ =>
        ((V : Matrix n n ℂ) * Matrix.single a b (1 : ℂ) * star (V : Matrix n n ℂ)).trace)
      = fun _ : Matrix.unitaryGroup n ℂ => (Matrix.single a b (1 : ℂ)).trace from
    funext fun V => trace_conj_unitary n V (Matrix.single a b (1 : ℂ))]
  rw [MeasureTheory.integral_const]
  change ((haarUnitaryGroup n) Set.univ).toReal • (Matrix.single a b (1 : ℂ)).trace
    = (Matrix.single a b (1 : ℂ)).trace
  rw [haarUnitaryGroup_univ n, ENNReal.toReal_one, one_smul]

/-- The Haar entry-pair integral is zero for distinct row indices and otherwise equals the trace
of the corresponding matrix unit divided by the dimension. See [RudolphEtAl2024]. -/
theorem haar_entryPair_eq (n : Type*) [Fintype n] [DecidableEq n] (a b : n) (i j : n) :
    MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) j b))
      = if i = j then (Matrix.single a b (1 : ℂ)).trace / (Fintype.card n : ℂ) else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hcard : (Fintype.card n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨i⟩).ne'
    have hconst : ∀ k : n,
        MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (V : Matrix n n ℂ) k a * star ((V : Matrix n n ℂ) k b))
        = MeasureTheory.integral (haarUnitaryGroup n) (fun V : Matrix.unitaryGroup n ℂ =>
          (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) i b)) := by
      intro k
      have h := haar_entryPair_perm n a b (Equiv.swap i k) i i
      rw [Equiv.swap_apply_left] at h
      exact h.symm
    have hsum : ∑ k, MeasureTheory.integral (haarUnitaryGroup n)
          (fun V : Matrix.unitaryGroup n ℂ =>
            (V : Matrix n n ℂ) k a * star ((V : Matrix n n ℂ) k b))
        = (Fintype.card n : ℂ) * MeasureTheory.integral (haarUnitaryGroup n)
          (fun V : Matrix.unitaryGroup n ℂ =>
            (V : Matrix n n ℂ) i a * star ((V : Matrix n n ℂ) i b)) := by
      rw [Finset.sum_congr rfl fun k _ => hconst k, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [haar_entryPair_trace n a b] at hsum
    rw [eq_div_iff hcard, mul_comm]
    exact hsum.symm
  · rw [if_neg hij]
    exact haar_entryPair_offdiag n a b hij

/-- The permutation matrix exchanging the two factors of `n × n`. -/
def swapOp (n : Type*) [Fintype n] [DecidableEq n] : Matrix (n × n) (n × n) ℂ :=
  permMatrix (n × n) (Equiv.prodComm n n)

/-- The tensor-factor swap matrix is unitary. -/
theorem swapOp_mem_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    swapOp n ∈ Matrix.unitaryGroup (n × n) ℂ :=
  permMatrix_mem_unitaryGroup (n × n) (Equiv.prodComm n n)

/-- Multiplication of Kronecker products agrees with the Kronecker product of the factorwise
products. -/
theorem kroneckerMap_mul (n : Type*) [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n ℂ) :
    Matrix.kroneckerMap (· * ·) A C * Matrix.kroneckerMap (· * ·) B D
      = Matrix.kroneckerMap (· * ·) (A * B) (C * D) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.mul_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The Kronecker square of a unitary matrix is unitary. -/
theorem kronecker_mem_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) :
    Matrix.kroneckerMap (· * ·) (U : Matrix n n ℂ) (U : Matrix n n ℂ)
      ∈ Matrix.unitaryGroup (n × n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (Matrix.kroneckerMap (· * ·) (U : Matrix n n ℂ) (U : Matrix n n ℂ))
      = (Matrix.kroneckerMap (· * ·) (U : Matrix n n ℂ) (U : Matrix n n ℂ))ᴴ := rfl
  rw [hstar, Matrix.conjTranspose_kronecker, kroneckerMap_mul n]
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  rw [hUU, Matrix.one_kronecker_one]

/-- A diagonal matrix is unitary when every diagonal entry has squared modulus one. -/
theorem diagonal_mem_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] (d : n → ℂ)
    (hd : ∀ i, star (d i) * d i = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.sum_eq_single x]
    · simpa [Matrix.star_apply, Matrix.diagonal_apply, mul_comm] using hd x
    · intro k _ hk
      simp [Matrix.star_apply, Matrix.diagonal_apply, Ne.symm hk]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkx : k = x
    · subst hkx
      simp [Matrix.star_apply, Matrix.diagonal_apply, hxy, Ne.symm hxy]
    · simp [Matrix.star_apply, Matrix.diagonal_apply, hkx, Ne.symm hkx]

/-- The Kronecker square of a two-dimensional diagonal matrix has diagonal entry `z p.1 * z p.2`
and zero off-diagonal entries. -/
theorem diagonal_kronecker_apply (z : Fin 2 → ℂ) (p q : Fin 2 × Fin 2) :
    Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z) p q
      = if p = q then z p.1 * z p.2 else 0 := by
  rw [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    simp
  · rw [if_neg h]
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    simp only [Prod.mk.injEq] at h
    by_cases h₁ : p₁ = q₁
    · rw [if_pos h₁]
      have h₂ : p₂ ≠ q₂ := fun h₂ => h ⟨h₁, h₂⟩
      rw [if_neg h₂, mul_zero]
    · rw [if_neg h₁, zero_mul]

/-- A matrix commuting with a diagonal Kronecker square has zero entries between indices with
distinct diagonal eigenvalues. -/
theorem torus_sparsity (z : Fin 2 → ℂ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z) * M
      = M * Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z))
    {p q : Fin 2 × Fin 2} (hne : z p.1 * z p.2 ≠ z q.1 * z q.2) : M p q = 0 := by
  have hleft : (Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z) * M) p q
      = z p.1 * z p.2 * M p q := by
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · rw [diagonal_kronecker_apply, if_pos rfl]
    · intro r _ hr
      rw [diagonal_kronecker_apply, if_neg (fun hh => hr hh.symm), zero_mul]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  have hright : (M * Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z)) p q
      = M p q * (z q.1 * z q.2) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · rw [diagonal_kronecker_apply, if_pos rfl]
    · intro r _ hr
      rw [diagonal_kronecker_apply, if_neg hr, mul_zero]
    · intro hq
      exact absurd (Finset.mem_univ q) hq
  have hpq : z p.1 * z p.2 * M p q = (z q.1 * z q.2) * M p q := by
    have h' : (Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z) * M) p q
        = (M * Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z)) p q := by
      rw [h]
    rw [hleft, hright, mul_comm (M p q) (z q.1 * z q.2)] at h'
    exact h'
  have hzero : (z p.1 * z p.2 - z q.1 * z q.2) * M p q = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hpq
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

/-- The permutation matrix exchanging the two computational basis states. -/
def bitFlip : Matrix (Fin 2) (Fin 2) ℂ := permMatrix (Fin 2) (Equiv.swap 0 1)

/-- The bit-flip matrix is unitary. -/
theorem bitFlip_mem_unitaryGroup : bitFlip ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  permMatrix_mem_unitaryGroup (Fin 2) (Equiv.swap 0 1)

/-- The `(i, j)` entry of `bitFlip` is one exactly when `j` is the bit flip of `i`. -/
theorem bitFlip_apply (i j : Fin 2) : bitFlip i j = if j = Equiv.swap 0 1 i then 1 else 0 := rfl

/-- The Kronecker square of `bitFlip` has entry one exactly when both bits are flipped. -/
theorem bitflip_kronecker_apply (p₁ p₂ q₁ q₂ : Fin 2) :
    Matrix.kroneckerMap (· * ·) bitFlip bitFlip (p₁, p₂) (q₁, q₂)
      = if (q₁, q₂) = (Equiv.swap 0 1 p₁, Equiv.swap 0 1 p₂) then 1 else 0 := by
  rw [Matrix.kroneckerMap_apply, bitFlip_apply, bitFlip_apply]
  by_cases h₁ : q₁ = Equiv.swap 0 1 p₁ <;> by_cases h₂ : q₂ = Equiv.swap 0 1 p₂ <;>
    simp [h₁, h₂, Prod.ext_iff]

/-- Commutation with the simultaneous bit flip makes matrix entries invariant under flipping
every row and column bit. -/
theorem bitflip_relation (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : Matrix.kroneckerMap (· * ·) bitFlip bitFlip * M
      = M * Matrix.kroneckerMap (· * ·) bitFlip bitFlip)
    (i j k l : Fin 2) :
    M (Equiv.swap 0 1 i, Equiv.swap 0 1 j) (Equiv.swap 0 1 k, Equiv.swap 0 1 l)
      = M (i, j) (k, l) := by
  have h' : (Matrix.kroneckerMap (· * ·) bitFlip bitFlip * M) (i, j)
        (Equiv.swap 0 1 k, Equiv.swap 0 1 l)
      = (M * Matrix.kroneckerMap (· * ·) bitFlip bitFlip) (i, j)
        (Equiv.swap 0 1 k, Equiv.swap 0 1 l) := by
    rw [h]
  have hleft : (Matrix.kroneckerMap (· * ·) bitFlip bitFlip * M) (i, j)
        (Equiv.swap 0 1 k, Equiv.swap 0 1 l)
      = M (Equiv.swap 0 1 i, Equiv.swap 0 1 j) (Equiv.swap 0 1 k, Equiv.swap 0 1 l) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap 0 1 i, Equiv.swap 0 1 j)]
    · rw [bitflip_kronecker_apply]
      simp
    · intro r _ hr
      rw [bitflip_kronecker_apply, if_neg (fun hh => hr (by cases r with | mk a b => exact hh)),
        zero_mul]
    · intro hp
      exact absurd (Finset.mem_univ _) hp
  have hright : (M * Matrix.kroneckerMap (· * ·) bitFlip bitFlip) (i, j)
        (Equiv.swap 0 1 k, Equiv.swap 0 1 l)
      = M (i, j) (k, l) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (k, l)]
    · rw [bitflip_kronecker_apply]
      simp
    · intro r _ hr
      rw [bitflip_kronecker_apply, if_neg ?_, mul_zero]
      intro hh
      have h1 : r.1 = k := (Equiv.swap 0 1).injective (Prod.ext_iff.mp hh).1.symm
      have h2 : r.2 = l := (Equiv.swap 0 1).injective (Prod.ext_iff.mp hh).2.symm
      exact hr (Prod.ext h1 h2)
    · intro hq
      exact absurd (Finset.mem_univ _) hq
  rw [hleft, hright] at h'
  exact h'

/-- The trace of a permutation matrix is the number of fixed points of the permutation. -/
theorem permMatrix_trace (n : Type*) [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    (permMatrix n σ).trace = ((Finset.univ.filter fun i => σ i = i).card : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, permMatrix, Matrix.of_apply]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : σ i = i
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh : i = σ i => h hh.symm), if_neg h]

/-- The identity matrix on two qubits has trace four. -/
theorem trace_one_fin2x2 : (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).trace = 4 := by
  rw [Matrix.trace_one]
  norm_num

/-- The swap matrix on two qubits has trace two. -/
theorem swapOp_trace : (swapOp (Fin 2)).trace = 2 := by
  rw [swapOp, permMatrix_trace]
  have h : (Finset.univ.filter fun i : Fin 2 × Fin 2 =>
      Equiv.prodComm (Fin 2) (Fin 2) i = i).card = 2 := by decide
  rw [h]
  norm_num

/-- The product of two permutation matrices represents their composition `σ.trans τ`. -/
theorem permMatrix_mul (n : Type*) [Fintype n] [DecidableEq n] (σ τ : Equiv.Perm n) :
    permMatrix n σ * permMatrix n τ = permMatrix n (σ.trans τ) := by
  ext a c
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
  · simp [permMatrix, Matrix.of_apply, Equiv.trans_apply]
  · intro b _ hb
    simp [permMatrix, Matrix.of_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ (σ a)) h

/-- The permutation matrix of the identity equivalence is the identity matrix. -/
theorem permMatrix_refl (n : Type*) [Fintype n] [DecidableEq n] :
    permMatrix n (Equiv.refl n) = 1 := by
  ext a c
  rw [permMatrix, Matrix.of_apply, Matrix.one_apply, Equiv.refl_apply]
  by_cases h : c = a
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-- The two-qubit swap matrix squares to the identity. -/
theorem swapOp_mul_self : swapOp (Fin 2) * swapOp (Fin 2) = 1 := by
  have h : (Equiv.prodComm (Fin 2) (Fin 2)).trans (Equiv.prodComm (Fin 2) (Fin 2))
      = Equiv.refl (Fin 2 × Fin 2) :=
    Equiv.ext fun x => by simp [Equiv.trans_apply, Equiv.prodComm]
  rw [swapOp, permMatrix_mul, h, permMatrix_refl]

/-- Right multiplication by the swap matrix exchanges the two components of the column index. -/
theorem mul_swapOp_apply (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p q : Fin 2 × Fin 2) :
    (N * swapOp (Fin 2)) p q = N p q.swap := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q.swap]
  · simp [swapOp, permMatrix, Matrix.of_apply]
  · intro r _ hr
    have hq : ¬ (q = r.swap) := fun h => hr (by rw [h]; simp)
    simp [swapOp, permMatrix, Matrix.of_apply, hq]
  · intro hq
    exact absurd (Finset.mem_univ _) hq

/-- Left multiplication by the swap matrix exchanges the two components of the row index. -/
theorem swapOp_mul_apply (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p q : Fin 2 × Fin 2) :
    (swapOp (Fin 2) * N) p q = N p.swap q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p.swap]
  · simp [swapOp, permMatrix, Matrix.of_apply]
  · intro r _ hr
    simp [swapOp, permMatrix, Matrix.of_apply, hr]
  · intro hp
    exact absurd (Finset.mem_univ _) hp

/-- Conjugation by the two-qubit swap exchanges the factors of a Kronecker product. -/
theorem swapOp_kronecker_conj (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    swapOp (Fin 2) * Matrix.kroneckerMap (· * ·) A B * swapOp (Fin 2)
      = Matrix.kroneckerMap (· * ·) B A := by
  ext p q
  rw [mul_swapOp_apply, swapOp_mul_apply, Matrix.kroneckerMap_apply, Matrix.kroneckerMap_apply]
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact mul_comm _ _

/-- The swap matrix commutes with the Kronecker square of any two-dimensional complex matrix. -/
theorem swapOp_mul_kronecker (U : Matrix (Fin 2) (Fin 2) ℂ) :
    swapOp (Fin 2) * Matrix.kroneckerMap (· * ·) U U
      = Matrix.kroneckerMap (· * ·) U U * swapOp (Fin 2) := by
  have h := swapOp_kronecker_conj U U
  calc swapOp (Fin 2) * Matrix.kroneckerMap (· * ·) U U
      = (swapOp (Fin 2) * Matrix.kroneckerMap (· * ·) U U * swapOp (Fin 2)) * swapOp (Fin 2) := by
        rw [mul_assoc, swapOp_mul_self, mul_one]
    _ = Matrix.kroneckerMap (· * ·) U U * swapOp (Fin 2) := by
        rw [h]

/-- The two-dimensional matrix with diagonal entries `(1 + Complex.I) / 2` and off-diagonal
entries `(1 - Complex.I) / 2`. -/
def mixUnitary : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i = j then (1 + Complex.I) / 2 else (1 - Complex.I) / 2

/-- The `(0, 0)` entry of `mixUnitary` is `(1 + Complex.I) / 2`. -/
theorem mixUnitary_zero_zero : mixUnitary 0 0 = (1 + Complex.I) / 2 := by
  simp [mixUnitary, Matrix.of_apply]

/-- The `(0, 1)` entry of `mixUnitary` is `(1 - Complex.I) / 2`. -/
theorem mixUnitary_zero_one : mixUnitary 0 1 = (1 - Complex.I) / 2 := by
  simp [mixUnitary, Matrix.of_apply]

/-- The `(0, 0)` entry of `mixUnitary` is nonzero. -/
theorem mixUnitary_zero_zero_ne_zero : mixUnitary 0 0 ≠ 0 := by
  rw [mixUnitary_zero_zero]
  intro h
  have h1 := congrArg Complex.re h
  norm_num at h1

/-- The `(0, 1)` entry of `mixUnitary` is nonzero. -/
theorem mixUnitary_zero_one_ne_zero : mixUnitary 0 1 ≠ 0 := by
  rw [mixUnitary_zero_one]
  intro h
  have h1 := congrArg Complex.im h
  norm_num at h1

/-- Evaluates each entry of `mixUnitary` according to whether its indices agree. -/
theorem mixUnitary_apply (i j : Fin 2) :
    mixUnitary i j = if i = j then (1 + Complex.I) / 2 else (1 - Complex.I) / 2 := rfl

/-- The matrix `mixUnitary` is unitary. -/
theorem mixUnitary_mem_unitaryGroup : mixUnitary ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [mixUnitary, Matrix.of_apply, Matrix.star_apply] <;>
    apply Complex.ext <;> simp <;> norm_num

/-- The `(1, 0)` entry of `mixUnitary` is `(1 - Complex.I) / 2`. -/
theorem mixUnitary_one_zero : mixUnitary 1 0 = (1 - Complex.I) / 2 := by
  simp [mixUnitary, Matrix.of_apply]

/-- The `(1, 1)` entry of `mixUnitary` is `(1 + Complex.I) / 2`. -/
theorem mixUnitary_one_one : mixUnitary 1 1 = (1 + Complex.I) / 2 := by
  simp [mixUnitary, Matrix.of_apply]

/-- Cancels the nonzero product of the two mixing coefficients to deduce `a = b + c`. -/
theorem mix_factor_cancel (a b c : ℂ)
    (h : ((1 + Complex.I) / 2) * ((1 - Complex.I) / 2) * (b + c)
      = a * (((1 + Complex.I) / 2) * ((1 - Complex.I) / 2))) :
    a = b + c := by
  have hne : ((1 + Complex.I) / 2) * ((1 - Complex.I) / 2) ≠ 0 :=
    mul_ne_zero (by rw [← mixUnitary_zero_zero]; exact mixUnitary_zero_zero_ne_zero)
      (by rw [← mixUnitary_zero_one]; exact mixUnitary_zero_one_ne_zero)
  have h2 : ((1 + Complex.I) / 2) * ((1 - Complex.I) / 2) * (b + c)
      = ((1 + Complex.I) / 2) * ((1 - Complex.I) / 2) * a := by
    rw [h]; ring
  exact (mul_left_cancel₀ hne h2).symm

/-- The product of the diagonal and off-diagonal mixing coefficients is one half. -/
theorem mix_coeff : ((1 + Complex.I) / 2) * ((1 - Complex.I) / 2) = 1 / 2 := by
  have h : ((1 + Complex.I) / 2) * ((1 - Complex.I) / 2)
      = ((1 + Complex.I) * (1 - Complex.I)) / 4 := by ring
  rw [h, show (1 + Complex.I) * (1 - Complex.I) = (2 : ℂ) by
    apply Complex.ext <;> simp <;> norm_num]
  norm_num

/-- The reversed product of the two mixing coefficients is one half. -/
theorem mix_coeff_symm : ((1 - Complex.I) / 2) * ((1 + Complex.I) / 2) = 1 / 2 := by
  rw [mul_comm ((1 - Complex.I) / 2) ((1 + Complex.I) / 2), mix_coeff]

/-- Commutation with the Kronecker square of `mixUnitary`, together with the four specified zero
entries, gives the stated relation among three entries of `M`. -/
theorem mixUnitary_relation {M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (h : Matrix.kroneckerMap (· * ·) mixUnitary mixUnitary * M
      = M * Matrix.kroneckerMap (· * ·) mixUnitary mixUnitary)
    (h1 : M (0, 0) (0, 1) = 0) (h2 : M (1, 1) (0, 1) = 0)
    (h3 : M (0, 0) (1, 1) = 0) (h4 : M (0, 0) (1, 0) = 0) :
    M (0, 0) (0, 0) = M (0, 1) (0, 1) + M (1, 0) (0, 1) := by
  have h' : (Matrix.kroneckerMap (· * ·) mixUnitary mixUnitary * M) (0, 0) (0, 1)
      = (M * Matrix.kroneckerMap (· * ·) mixUnitary mixUnitary) (0, 0) (0, 1) := by rw [h]
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type] at h'
  simp only [Matrix.kroneckerMap_apply, Fin.sum_univ_two, mixUnitary_apply] at h'

  have e1 : M (0, 0) (0, 1) = 0 := h1
  have e2 : M (1, 1) (0, 1) = 0 := h2
  have e3 : M (0, 0) (1, 1) = 0 := h3
  have e4 : M (0, 0) (1, 0) = 0 := h4
  simp only [e1, e2, e3, e4, zero_mul, mul_zero, Fin.isValue, if_true] at h'

  simp [mix_coeff, mix_coeff_symm] at h'

  rw [mul_comm (M (0, 0) (0, 0)) (2⁻¹ : ℂ)] at h'

  have h3 : (2⁻¹ : ℂ) * (M (0, 1) (0, 1) + M (1, 0) (0, 1))
      = (2⁻¹ : ℂ) * M (0, 0) (0, 0) := by
    rw [mul_add]; exact h'
  exact (mul_left_cancel₀ (by norm_num : ((2⁻¹ : ℂ)) ≠ 0) h3).symm

/-- The stated bit-flip symmetry, entry relation, and sparsity conditions express `M` as a
linear combination of the identity and swap matrices. -/
theorem span_one_swap (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hbit : Matrix.kroneckerMap (· * ·) bitFlip bitFlip * M
      = M * Matrix.kroneckerMap (· * ·) bitFlip bitFlip)
    (hsum : M (0, 0) (0, 0) = M (0, 1) (0, 1) + M (1, 0) (0, 1))
    (hzero : ∀ p q : Fin 2 × Fin 2, p ≠ q → ¬(p = (0, 1) ∧ q = (1, 0)) →
      ¬(p = (1, 0) ∧ q = (0, 1)) → M p q = 0) :
    M = M (0, 1) (0, 1) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      + M (1, 0) (0, 1) • swapOp (Fin 2) := by

  have h11 : M (1, 1) (1, 1) = M (0, 0) (0, 0) := by
    simpa using bitflip_relation M hbit 0 0 0 0
  have hmid : M (1, 0) (1, 0) = M (0, 1) (0, 1) := by
    simpa using bitflip_relation M hbit 0 1 0 1
  have hsw : M (0, 1) (1, 0) = M (1, 0) (0, 1) := by
    simpa using bitflip_relation M hbit 1 0 0 1
  ext p q
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
    simp [Matrix.add_apply, Matrix.smul_apply, swapOp, permMatrix,
      Matrix.of_apply, Equiv.prodComm_apply, hsum, h11, hmid, hsw, hzero, Ne.symm]

/-- The trace of `c` times the identity plus `b` times the two-qubit swap is `4 * c + 2 * b`. -/
theorem span_trace (c b : ℂ) :
    (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + b • swapOp (Fin 2)).trace
      = 4 * c + 2 * b := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_one_fin2x2, swapOp_trace,
    smul_eq_mul]
  ring

/-- The trace after multiplying this identity-swap combination by the swap is `2 * c + 4 * b`. -/
theorem span_trace_mul_swap (c b : ℂ) :
    ((c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) + b • swapOp (Fin 2))
        * swapOp (Fin 2)).trace = 2 * c + 4 * b := by
  rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Matrix.one_mul, swapOp_mul_self,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, swapOp_trace, trace_one_fin2x2,
    smul_eq_mul]
  ring

/-- An identity-swap combination with trace one and swap-weighted trace one has both
coefficients equal to one sixth. -/
theorem eq_one_plus_swap_of_traces (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hspan : M = M (0, 1) (0, 1) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      + M (1, 0) (0, 1) • swapOp (Fin 2))
    (htr : M.trace = 1) (htrS : (M * swapOp (Fin 2)).trace = 1) :
    M = (1 / 6 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      + (1 / 6 : ℂ) • swapOp (Fin 2) := by
  have h1 : 4 * M (0, 1) (0, 1) + 2 * M (1, 0) (0, 1) = 1 := by
    rw [hspan, span_trace] at htr
    exact htr
  have h2 : 2 * M (0, 1) (0, 1) + 4 * M (1, 0) (0, 1) = 1 := by
    rw [hspan, span_trace_mul_swap] at htrS
    exact htrS
  have hc : M (0, 1) (0, 1) = 1 / 6 := by
    linear_combination (1 / 3 : ℂ) * h1 - (1 / 6 : ℂ) * h2
  have hb : M (1, 0) (0, 1) = 1 / 6 := by
    linear_combination (1 / 3 : ℂ) * h2 - (1 / 6 : ℂ) * h1
  rw [hspan, hc, hb]

/-- Every entry of the Kronecker square of a unitary matrix has norm at most one. -/
theorem kronecker_entry_norm_le_one (n : Type*) [Fintype n] [DecidableEq n]
    (V : Matrix.unitaryGroup n ℂ) (p q : n × n) :
    ‖Matrix.kroneckerMap (· * ·) (V : Matrix n n ℂ) (V : Matrix n n ℂ) p q‖ ≤ 1 := by
  rw [Matrix.kroneckerMap_apply, norm_mul]
  have h1 := unitaryGroup_entry_norm_le_one V.2 p.1 q.1
  have h2 := unitaryGroup_entry_norm_le_one V.2 p.2 q.2
  nlinarith [norm_nonneg ((V : Matrix n n ℂ) p.1 q.1),
    norm_nonneg ((V : Matrix n n ℂ) p.2 q.2)]

/-- Each entry of the Kronecker square depends continuously on the unitary matrix. -/
theorem continuous_kronecker_entry (n : Type*) [Fintype n] [DecidableEq n] (p q : n × n) :
    Continuous fun V : Matrix.unitaryGroup n ℂ =>
      Matrix.kroneckerMap (· * ·) (V : Matrix n n ℂ) (V : Matrix n n ℂ) p q := by
  have h1 : Continuous fun V : Matrix.unitaryGroup n ℂ => (V : Matrix n n ℂ) p.1 q.1 := by
    change Continuous fun V : Matrix.unitaryGroup n ℂ => (V : n → n → ℂ) p.1 q.1
    have hk : Continuous fun r : n → n → ℂ => r p.1 := continuous_apply p.1
    have ha : Continuous fun s : n → ℂ => s q.1 := continuous_apply q.1
    exact (ha.comp hk).comp continuous_subtype_val
  have h2 : Continuous fun V : Matrix.unitaryGroup n ℂ => (V : Matrix n n ℂ) p.2 q.2 := by
    change Continuous fun V : Matrix.unitaryGroup n ℂ => (V : n → n → ℂ) p.2 q.2
    have hk : Continuous fun r : n → n → ℂ => r p.2 := continuous_apply p.2
    have ha : Continuous fun s : n → ℂ => s q.2 := continuous_apply q.2
    exact (ha.comp hk).comp continuous_subtype_val
  have hfun : (fun V : Matrix.unitaryGroup n ℂ =>
        Matrix.kroneckerMap (· * ·) (V : Matrix n n ℂ) (V : Matrix n n ℂ) p q)
      = fun V : Matrix.unitaryGroup n ℂ =>
        (V : Matrix n n ℂ) p.1 q.1 * (V : Matrix n n ℂ) p.2 q.2 := by
    funext V
    rw [Matrix.kroneckerMap_apply]
  rw [hfun]
  exact h1.mul h2

/-- The Kronecker square of a two-dimensional unitary matrix, viewed as a matrix on two qubits. -/
def unitaryKronecker (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (V : Matrix (Fin 2) (Fin 2) ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ)

/-- Expands an entry of `K * P * Kᴴ` as a double sum of matrix entries. -/
theorem kroneckerConj_apply (P K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (p q : Fin 2 × Fin 2) :
    (K * P * Kᴴ) p q = ∑ a, ∑ b, K p a * P a b * star (K q b) := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- Each entry of conjugation by the Kronecker square of a Haar unitary is integrable. -/
theorem haarIntegrable_kroneckerConj (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (p q : Fin 2 × Fin 2) :
    MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) p q) (haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hbase : ∀ a b : Fin 2 × Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        unitaryKronecker V p a * star (unitaryKronecker V q b)) (haarUnitaryGroup (Fin 2)) := by
    intro a b
    refine MeasureTheory.Integrable.of_bound
      (Continuous.aestronglyMeasurable
        ((continuous_kronecker_entry (Fin 2) p a).mul
          (continuous_star.comp (continuous_kronecker_entry (Fin 2) q b)))) 1 ?_
    filter_upwards with V
    simp only [unitaryKronecker]
    rw [norm_mul, norm_star]
    have h1 := kronecker_entry_norm_le_one (Fin 2) V p a
    have h2 := kronecker_entry_norm_le_one (Fin 2) V q b
    nlinarith [norm_nonneg (Matrix.kroneckerMap (· * ·) (V : Matrix (Fin 2) (Fin 2) ℂ)
        (V : Matrix (Fin 2) (Fin 2) ℂ) p a),
      norm_nonneg (Matrix.kroneckerMap (· * ·) (V : Matrix (Fin 2) (Fin 2) ℂ)
        (V : Matrix (Fin 2) (Fin 2) ℂ) q b)]
  have hsum : MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ∑ a, ∑ b, P a b * (unitaryKronecker V p a * star (unitaryKronecker V q b)))
      (haarUnitaryGroup (Fin 2)) :=
    MeasureTheory.integrable_finsetSum Finset.univ fun a _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun b _ => (hbase a b).const_mul (P a b)
  refine hsum.congr ?_
  filter_upwards with V
  rw [kroneckerConj_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The entrywise Haar average of conjugating `P` by the Kronecker square of a single-qubit
unitary. -/
def haarKroneckerAverage (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    MeasureTheory.integral (haarUnitaryGroup (Fin 2)) fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) p q

/-- Taking the Kronecker square preserves multiplication of unitary matrices. -/
theorem unitaryKronecker_mul (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryKronecker U * unitaryKronecker V = unitaryKronecker (U * V) := by
  simp only [unitaryKronecker]
  rw [kroneckerMap_mul (Fin 2), Submonoid.coe_mul]

/-- Each entry remains Haar integrable after conjugating the Kronecker-conjugation integrand by
a fixed matrix `K`. -/
theorem haarIntegrable_conjKroneckerConj (P K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (p q : Fin 2 × Fin 2) :
    MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (K * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * Kᴴ) p q)
      (haarUnitaryGroup (Fin 2)) := by
  have hsum : MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ∑ a, ∑ b, star (K q b) *
        (K p a * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) a b))
      (haarUnitaryGroup (Fin 2)) :=
    MeasureTheory.integrable_finsetSum Finset.univ fun a _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun b _ =>
        ((haarIntegrable_kroneckerConj P a b).const_mul (K p a)).const_mul (star (K q b))
  refine hsum.congr ?_
  filter_upwards with V
  rw [kroneckerConj_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Successive conjugations by Kronecker squares combine into conjugation by the Kronecker
square of the unitary product. -/
theorem unitaryKronecker_conj_mul (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    unitaryKronecker U * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * (unitaryKronecker U)ᴴ
      = unitaryKronecker (U * V) * P * (unitaryKronecker (U * V))ᴴ := by
  rw [← unitaryKronecker_mul, Matrix.conjTranspose_mul]
  simp only [mul_assoc]

/-- Conjugation by a fixed matrix can be moved inside the entrywise Haar Kronecker average. -/
theorem kroneckerAverage_conj_apply (P K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (p q : Fin 2 × Fin 2) :
    (K * haarKroneckerAverage P * Kᴴ) p q
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (K * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * Kᴴ) p q) := by
  have hterm : ∀ a b : Fin 2 × Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        K p a * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) a b * star (K q b))
      (haarUnitaryGroup (Fin 2)) := by
    intro a b
    refine (((haarIntegrable_kroneckerConj P a b).const_mul (K p a)).const_mul
      (star (K q b))).congr ?_
    filter_upwards with V
    ring
  rw [kroneckerConj_apply]
  simp only [haarKroneckerAverage, Matrix.of_apply]

  have hR : MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          (K * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * Kᴴ) p q)
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ∑ a, ∑ b, K p a * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) a b * star (K q b)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V =>
      kroneckerConj_apply (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) K p q)
  rw [hR]
  symm
  calc MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ∑ a, ∑ b, K p a * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) a b * star (K q b))
      = ∑ a, MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∑ b, K p a * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) a b * star (K q b)) := by
        rw [MeasureTheory.integral_finsetSum Finset.univ
          (fun a _ => MeasureTheory.integrable_finsetSum Finset.univ (fun b _ => hterm a b))]
    _ = ∑ a, ∑ b, K p a * (MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) a b)) * star (K q b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun b _ => hterm a b)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]

/-- The Haar Kronecker average is invariant under conjugation by the Kronecker square of any
single-qubit unitary. -/
theorem haarKroneckerAverage_invariant (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    unitaryKronecker U * haarKroneckerAverage P * (unitaryKronecker U)ᴴ = haarKroneckerAverage P := by
  haveI : (haarUnitaryGroup (Fin 2)).IsMulLeftInvariant := by
    rw [haarUnitaryGroup]
    infer_instance
  ext p q
  rw [kroneckerAverage_conj_apply, haarKroneckerAverage, Matrix.of_apply]
  have hX : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (unitaryKronecker U * (unitaryKronecker V * P * (unitaryKronecker V)ᴴ)
          * (unitaryKronecker U)ᴴ) p q)
      = fun V => (unitaryKronecker (U * V) * P * (unitaryKronecker (U * V))ᴴ) p q := by
    funext V
    rw [unitaryKronecker_conj_mul]
  rw [hX]
  exact MeasureTheory.integral_mul_left_eq_self (μ := haarUnitaryGroup (Fin 2))
    (fun W : Matrix.unitaryGroup (Fin 2) ℂ =>
      (unitaryKronecker W * P * (unitaryKronecker W)ᴴ) p q) U

/-- The Haar Kronecker average commutes with every Kronecker square of a single-qubit unitary. -/
theorem haarKroneckerAverage_commute (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    unitaryKronecker U * haarKroneckerAverage P = haarKroneckerAverage P * unitaryKronecker U := by
  have hU : (unitaryKronecker U)ᴴ * unitaryKronecker U = 1 := by
    have hstar : star (unitaryKronecker U) = (unitaryKronecker U)ᴴ := rfl
    rw [← hstar]
    exact Matrix.mem_unitaryGroup_iff'.mp (kronecker_mem_unitaryGroup (Fin 2) U)
  calc unitaryKronecker U * haarKroneckerAverage P
      = unitaryKronecker U * haarKroneckerAverage P
          * ((unitaryKronecker U)ᴴ * unitaryKronecker U) := by
        rw [hU, mul_one]
    _ = unitaryKronecker U * haarKroneckerAverage P * (unitaryKronecker U)ᴴ
          * unitaryKronecker U := by
        conv_rhs => rw [mul_assoc]
    _ = haarKroneckerAverage P * unitaryKronecker U := by
        rw [haarKroneckerAverage_invariant U P]

/-- The two diagonal phases one and `Complex.I`. -/
def torusPhase : Fin 2 → ℂ := fun i => if i = 0 then 1 else Complex.I

/-- Every entry of `torusPhase` has squared modulus one. -/
theorem torusPhase_star_mul (i : Fin 2) : star (torusPhase i) * torusPhase i = 1 := by
  fin_cases i <;> simp [torusPhase, Complex.I_mul_I]

/-- The Haar Kronecker average commutes with the Kronecker square of every diagonal unitary. -/
theorem torus_relation (z : Fin 2 → ℂ) (hd : ∀ i, star (z i) * z i = 1)
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z) * haarKroneckerAverage P
      = haarKroneckerAverage P
        * Matrix.kroneckerMap (· * ·) (Matrix.diagonal z) (Matrix.diagonal z) := by
  have hmem : Matrix.diagonal z ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    diagonal_mem_unitaryGroup (Fin 2) z hd
  simpa only [unitaryKronecker] using haarKroneckerAverage_commute ⟨Matrix.diagonal z, hmem⟩ P

/-- Products of the selected diagonal phases distinguish distinct two-bit indices except for the
pair `(0, 1)` and `(1, 0)`. -/
theorem torusPhase_mul_ne {p q : Fin 2 × Fin 2} (hpq : p ≠ q)
    (h1 : ¬(p = (0, 1) ∧ q = (1, 0))) (h2 : ¬(p = (1, 0) ∧ q = (0, 1))) :
    torusPhase p.1 * torusPhase p.2 ≠ torusPhase q.1 * torusPhase q.2 := by

  have hI1 : ¬(1 : ℂ) = Complex.I := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hI1' : ¬Complex.I = (1 : ℂ) := fun h => hI1 h.symm
  have hI2 : ¬Complex.I = (-1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hI2' : ¬(-1 : ℂ) = Complex.I := fun h => hI2 h.symm
  have h13 : ¬(1 : ℂ) = (-1 : ℂ) := by norm_num
  have h13' : ¬(-1 : ℂ) = (1 : ℂ) := fun h => h13 h.symm
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
    simp_all [torusPhase, Complex.I_mul_I]

/-- Off-diagonal entries of the Haar Kronecker average vanish except possibly between `(0, 1)`
and `(1, 0)`. -/
theorem haarKroneckerAverage_offDiagonal_zero
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ∀ p q : Fin 2 × Fin 2, p ≠ q → ¬(p = (0, 1) ∧ q = (1, 0)) →
      ¬(p = (1, 0) ∧ q = (0, 1)) → haarKroneckerAverage P p q = 0 := by
  intro p q hpq h1 h2
  exact torus_sparsity torusPhase (haarKroneckerAverage P)
    (torus_relation torusPhase torusPhase_star_mul P) (torusPhase_mul_ne hpq h1 h2)

/-- The Haar Kronecker average commutes with the simultaneous bit-flip matrix. -/
theorem haarKroneckerAverage_bitflip_commute
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.kroneckerMap (· * ·) bitFlip bitFlip * haarKroneckerAverage P
      = haarKroneckerAverage P * Matrix.kroneckerMap (· * ·) bitFlip bitFlip := by
  simpa only [unitaryKronecker] using
    haarKroneckerAverage_commute ⟨bitFlip, bitFlip_mem_unitaryGroup⟩ P

/-- The Haar Kronecker average commutes with the Kronecker square of `mixUnitary`. -/
theorem haarKroneckerAverage_mixUnitary_commute
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.kroneckerMap (· * ·) mixUnitary mixUnitary * haarKroneckerAverage P
      = haarKroneckerAverage P * Matrix.kroneckerMap (· * ·) mixUnitary mixUnitary := by
  simpa only [unitaryKronecker] using
    haarKroneckerAverage_commute ⟨mixUnitary, mixUnitary_mem_unitaryGroup⟩ P

/-- The trace of a matrix product is the double sum of paired entries `A p r * K r p`. -/
theorem trace_mul_apply_sum (A K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (A * K).trace = ∑ p, ∑ r, A p r * K r p := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- The trace of the Haar Kronecker average multiplied by a fixed matrix equals the integral of
the corresponding traces. -/
theorem haarKroneckerAverage_mul_trace (P K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (haarKroneckerAverage P * K).trace
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * K).trace) := by
  have hterm : ∀ p r : Fin 2 × Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) p r * K r p)
      (haarUnitaryGroup (Fin 2)) :=
    fun p r => (haarIntegrable_kroneckerConj P p r).mul_const (K r p)
  have hL : (haarKroneckerAverage P * K).trace
      = ∑ p, ∑ r, (MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) p r) * K r p := by
    rw [trace_mul_apply_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    simp only [haarKroneckerAverage, Matrix.of_apply]
  have hR : MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * K).trace)
      = ∑ p, ∑ r, (MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) p r) * K r p := by
    have hcongr : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * K).trace)
        = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ∑ p, ∑ r, (unitaryKronecker V * P * (unitaryKronecker V)ᴴ) p r * K r p := by
      funext V
      rw [trace_mul_apply_sum]
    rw [hcongr, MeasureTheory.integral_finsetSum Finset.univ
      (fun p _ => MeasureTheory.integrable_finsetSum Finset.univ (fun r _ => hterm p r))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun r _ => hterm p r)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MeasureTheory.integral_mul_const]
  exact hL.trans hR.symm

/-- The real-valued mass of the entire unitary group under normalized Haar measure is one. -/
theorem haarUnitaryGroup_real_univ (n : Type*) [Fintype n] [DecidableEq n] :
    (haarUnitaryGroup n).real Set.univ = 1 := by
  rw [MeasureTheory.measureReal_def, haarUnitaryGroup_univ n]
  simp

/-- The two-qubit swap matrix is self-adjoint. -/
theorem star_swapOp : star (swapOp (Fin 2)) = swapOp (Fin 2) := by
  ext p q
  rw [Matrix.star_apply]
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;>
    simp [swapOp, permMatrix, Matrix.of_apply, Equiv.prodComm_apply]

/-- Conjugating by a unitary Kronecker square preserves the swap-weighted trace. -/
theorem trace_kroneckerConj_mul_swap (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * swapOp (Fin 2)).trace
      = (P * swapOp (Fin 2)).trace := by
  have hAA : (unitaryKronecker V)ᴴ * unitaryKronecker V = 1 := by
    have hstar : star (unitaryKronecker V) = (unitaryKronecker V)ᴴ := rfl
    rw [← hstar]
    exact Matrix.mem_unitaryGroup_iff'.mp (kronecker_mem_unitaryGroup (Fin 2) V)
  have hSA : swapOp (Fin 2) * unitaryKronecker V = unitaryKronecker V * swapOp (Fin 2) := by
    simpa only [unitaryKronecker] using swapOp_mul_kronecker (V : Matrix (Fin 2) (Fin 2) ℂ)
  have hSA' : (unitaryKronecker V)ᴴ * swapOp (Fin 2)
      = swapOp (Fin 2) * (unitaryKronecker V)ᴴ := by
    have h := congrArg star hSA
    simp only [star_mul, star_swapOp] at h
    exact h
  calc ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * swapOp (Fin 2)).trace
      = (unitaryKronecker V * (P * ((unitaryKronecker V)ᴴ * swapOp (Fin 2)))).trace := by
        simp only [mul_assoc]
    _ = (unitaryKronecker V * (P * (swapOp (Fin 2) * (unitaryKronecker V)ᴴ))).trace := by
        rw [hSA']
    _ = ((P * (swapOp (Fin 2) * (unitaryKronecker V)ᴴ)) * unitaryKronecker V).trace :=
        Matrix.trace_mul_comm _ _
    _ = (P * (swapOp (Fin 2) * ((unitaryKronecker V)ᴴ * unitaryKronecker V))).trace := by
        simp only [mul_assoc]
    _ = (P * swapOp (Fin 2)).trace := by rw [hAA, mul_one]

/-- The Haar Kronecker average preserves the trace of its input. -/
theorem haarKroneckerAverage_trace (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (haarKroneckerAverage P).trace = P.trace := by
  have h1 := haarKroneckerAverage_mul_trace P 1
  rw [mul_one] at h1
  have hcongr : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * 1).trace) = fun _ => P.trace := by
    funext V
    rw [mul_one]
    exact trace_conj_unitary (Fin 2 × Fin 2)
      ⟨unitaryKronecker V, kronecker_mem_unitaryGroup (Fin 2) V⟩ P
  rw [h1, hcongr, MeasureTheory.integral_const, haarUnitaryGroup_real_univ, one_smul]

/-- If `P` has trace one and swap-weighted trace one, its Haar Kronecker average is one sixth of
the sum of the identity and swap matrices. See [RudolphEtAl2024]. -/
theorem haarKroneckerAverage_eq_one_plus_swap (P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (htr : P.trace = 1) (htrS : (P * swapOp (Fin 2)).trace = 1) :
    haarKroneckerAverage P
      = (1 / 6 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        + (1 / 6 : ℂ) • swapOp (Fin 2) := by
  have hzero := haarKroneckerAverage_offDiagonal_zero P
  have hsum : haarKroneckerAverage P (0, 0) (0, 0)
      = haarKroneckerAverage P (0, 1) (0, 1) + haarKroneckerAverage P (1, 0) (0, 1) :=
    mixUnitary_relation (haarKroneckerAverage_mixUnitary_commute P)
      (hzero (0, 0) (0, 1) (by decide) (by decide) (by decide))
      (hzero (1, 1) (0, 1) (by decide) (by decide) (by decide))
      (hzero (0, 0) (1, 1) (by decide) (by decide) (by decide))
      (hzero (0, 0) (1, 0) (by decide) (by decide) (by decide))
  refine eq_one_plus_swap_of_traces (haarKroneckerAverage P)
    (span_one_swap (haarKroneckerAverage P) (haarKroneckerAverage_bitflip_commute P) hsum
      hzero) ?_ ?_
  · rw [haarKroneckerAverage_trace, htr]
  · rw [haarKroneckerAverage_mul_trace P (swapOp (Fin 2))]
    have hcongr : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ((unitaryKronecker V * P * (unitaryKronecker V)ᴴ) * swapOp (Fin 2)).trace)
        = fun _ => (1 : ℂ) := by
      funext V
      rw [trace_kroneckerConj_mul_swap V P, htrS]
    rw [hcongr, MeasureTheory.integral_const, haarUnitaryGroup_real_univ, one_smul]

/-- The `t`-fold tensor power of a single-qubit matrix, indexed by bit strings of length `t`. -/
def tensorPow (t : ℕ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, V (x i) (y i)

/-- An entry of a tensor power is the product of the corresponding single-qubit entries. -/
theorem tensorPow_apply (t : ℕ) (V : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin t → Fin 2) :
    tensorPow t V x y = ∏ i, V (x i) (y i) := rfl

/-- The tensor power of the identity matrix is the identity matrix. -/
theorem tensorPow_one (t : ℕ) : tensorPow t (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext x y
  rw [tensorPow_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun i _ => by rw [Matrix.one_apply, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Matrix.one_apply, if_neg hi])

/-- Taking a tensor power preserves matrix multiplication. -/
theorem tensorPow_mul (t : ℕ) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorPow t (U * V) = tensorPow t U * tensorPow t V := by
  ext x y
  simp only [tensorPow_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib

/-- Taking a tensor power commutes with conjugate transpose. -/
theorem tensorPow_conjTranspose (t : ℕ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorPow t V)ᴴ = tensorPow t Vᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, tensorPow_apply]
  exact star_prod Finset.univ fun i => V (y i) (x i)

/-- Every tensor power of a single-qubit unitary is unitary. -/
theorem tensorPow_mem_unitaryGroup (t : ℕ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin t → Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ))
      = (tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := rfl
  have hV : (V : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.2
  rw [hstar, tensorPow_conjTranspose, ← tensorPow_mul, hV, tensorPow_one]

/-- The permutation matrix implementing a permutation of tensor positions in a bit string. -/
def tensorPerm (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ :=
  Matrix.of fun x y => if y = x ∘ σ.symm then 1 else 0

/-- An entry of `tensorPerm t σ` is one exactly when the column string is the row string
composed with `σ.symm`. -/
theorem tensorPerm_apply (t : ℕ) (σ : Equiv.Perm (Fin t)) (x y : Fin t → Fin 2) :
    tensorPerm t σ x y = if y = x ∘ σ.symm then 1 else 0 := rfl

/-- The identity permutation of tensor positions gives the identity matrix. -/
theorem tensorPerm_one (t : ℕ) : tensorPerm t (Equiv.refl (Fin t)) = 1 := by
  ext x y
  rw [tensorPerm_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h
    rw [if_pos rfl]
    simp
  · rw [if_neg h]
    refine if_neg fun hyx => h ?_
    funext i
    have hi := congrFun hyx i
    simpa [Function.comp] using hi.symm

/-- Composition `σ.trans τ` of tensor-position permutations corresponds to multiplication of
their matrices. -/
theorem tensorPerm_mul (t : ℕ) (σ τ : Equiv.Perm (Fin t)) :
    tensorPerm t (σ.trans τ) = tensorPerm t σ * tensorPerm t τ := by
  ext x y
  rw [tensorPerm_apply, Matrix.mul_apply, Finset.sum_eq_single (x ∘ σ.symm)]
  · simp only [tensorPerm_apply, if_true, one_mul]
    have hcomp : (x ∘ σ.symm) ∘ τ.symm = x ∘ (σ.trans τ).symm := by
      funext i
      simp only [Function.comp_apply, Equiv.symm_trans_apply]
    rw [hcomp]
  · intro z _ hz
    rw [tensorPerm_apply, if_neg hz, zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ (x ∘ σ.symm)) hx

/-- The conjugate transpose of a tensor permutation matrix is the matrix of the inverse
permutation. -/
theorem tensorPerm_conjTranspose (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    (tensorPerm t σ)ᴴ = tensorPerm t σ.symm := by
  ext x y
  rw [Matrix.conjTranspose_apply, tensorPerm_apply, tensorPerm_apply, Equiv.symm_symm]
  have hiff : (x = y ∘ σ.symm) ↔ (y = x ∘ σ) := by
    constructor
    · intro h
      funext i
      have hi := congrFun h (σ i)
      simpa [Function.comp, Equiv.symm_apply_apply] using hi.symm
    · intro h
      funext i
      have hi := congrFun h (σ.symm i)
      simpa [Function.comp, Equiv.apply_symm_apply] using hi.symm
  by_cases h : x = y ∘ σ.symm
  · rw [if_pos h, if_pos (hiff.mp h)]
    simp
  · rw [if_neg h, if_neg fun hc => h (hiff.mpr hc)]
    simp

/-- Every tensor permutation matrix is unitary. -/
theorem tensorPerm_mem_unitaryGroup (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    tensorPerm t σ ∈ Matrix.unitaryGroup (Fin t → Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (tensorPerm t σ) = (tensorPerm t σ)ᴴ := rfl
  rw [hstar, tensorPerm_conjTranspose, ← tensorPerm_mul, Equiv.self_trans_symm, tensorPerm_one]

/-- Expands an entry of matrix conjugation `K * P * Kᴴ` as a double sum. -/
theorem conjTranspose_mul_apply_sum {n : Type*} [Fintype n] (P K : Matrix n n ℂ) (p q : n) :
    (K * P * Kᴴ) p q = ∑ a, ∑ b, K p a * P a b * star (K q b) := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- Every entry of a tensor power of a single-qubit unitary has norm at most one. -/
theorem tensorPow_entry_norm_le_one (t : ℕ) (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (x y : Fin t → Fin 2) :
    ‖tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ) x y‖ ≤ 1 := by
  rw [tensorPow_apply]
  have h1 : ‖∏ i : Fin t, (V : Matrix (Fin 2) (Fin 2) ℂ) (x i) (y i)‖
      = ∏ i : Fin t, ‖(V : Matrix (Fin 2) (Fin 2) ℂ) (x i) (y i)‖ :=
    Complex.norm_prod Finset.univ fun i => (V : Matrix (Fin 2) (Fin 2) ℂ) (x i) (y i)
  rw [h1]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
    fun i _ => unitaryGroup_entry_norm_le_one V.2 (x i) (y i)

/-- Each tensor-power entry depends continuously on the single-qubit unitary. -/
theorem continuous_tensorPow_entry (t : ℕ) (x y : Fin t → Fin 2) :
    Continuous fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ) x y := by
  have hfun : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ) x y)
      = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ∏ i, (V : Matrix (Fin 2) (Fin 2) ℂ) (x i) (y i) := by
    funext V
    rw [tensorPow_apply]
  rw [hfun]
  refine continuous_finset_prod Finset.univ fun i _ => ?_
  change Continuous fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
    (V : Fin 2 → Fin 2 → ℂ) (x i) (y i)
  have hk : Continuous fun r : Fin 2 → Fin 2 → ℂ => r (x i) := continuous_apply (x i)
  have ha : Continuous fun s : Fin 2 → ℂ => s (y i) := continuous_apply (y i)
  exact (ha.comp hk).comp continuous_subtype_val

/-- The `t`-fold tensor power of a single-qubit unitary, viewed as a matrix on bit strings. -/
def unitaryTensorPow (t : ℕ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ :=
  tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ)

/-- The construction `unitaryTensorPow` preserves multiplication of unitary matrices. -/
theorem unitaryTensorPow_mul (t : ℕ) (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryTensorPow t U * unitaryTensorPow t V = unitaryTensorPow t (U * V) := by
  simp only [unitaryTensorPow]
  rw [← tensorPow_mul, Submonoid.coe_mul]

/-- Every entry of conjugation by a tensor power of a Haar single-qubit unitary is integrable. -/
theorem haarIntegrable_unitaryTensorPowConj (t : ℕ)
    (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) (p q : Fin t → Fin 2) :
    MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p q)
      (haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hbase : ∀ a b : Fin t → Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        unitaryTensorPow t V p a * star (unitaryTensorPow t V q b)) (haarUnitaryGroup (Fin 2)) := by
    intro a b
    refine MeasureTheory.Integrable.of_bound
      (Continuous.aestronglyMeasurable
        ((continuous_tensorPow_entry t p a).mul
          (continuous_star.comp (continuous_tensorPow_entry t q b)))) 1 ?_
    filter_upwards with V
    simp only [unitaryTensorPow]
    rw [norm_mul, norm_star]
    have h1 := tensorPow_entry_norm_le_one t V p a
    have h2 := tensorPow_entry_norm_le_one t V q b
    nlinarith [norm_nonneg (tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ) p a),
      norm_nonneg (tensorPow t (V : Matrix (Fin 2) (Fin 2) ℂ) q b)]
  have hsum : MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ∑ a, ∑ b, P a b * (unitaryTensorPow t V p a * star (unitaryTensorPow t V q b)))
      (haarUnitaryGroup (Fin 2)) :=
    MeasureTheory.integrable_finsetSum Finset.univ fun a _ =>
      MeasureTheory.integrable_finsetSum Finset.univ fun b _ => (hbase a b).const_mul (P a b)
  refine hsum.congr ?_
  filter_upwards with V
  rw [conjTranspose_mul_apply_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The entrywise Haar average of conjugation by the `t`-fold tensor power of a single-qubit
unitary. -/
def haarTensorAverage (t : ℕ) (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ :=
  Matrix.of fun p q =>
    MeasureTheory.integral (haarUnitaryGroup (Fin 2)) fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p q

/-- Conjugation by a fixed matrix can be moved inside each entry of the Haar tensor average. -/
theorem haarTensorAverage_conj_apply (t : ℕ)
    (P K : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) (p q : Fin t → Fin 2) :
    (K * haarTensorAverage t P * Kᴴ) p q
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (K * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * Kᴴ) p q) := by
  have hterm : ∀ a b : Fin t → Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        K p a * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) a b * star (K q b))
      (haarUnitaryGroup (Fin 2)) := by
    intro a b
    refine (((haarIntegrable_unitaryTensorPowConj t P a b).const_mul (K p a)).const_mul
      (star (K q b))).congr ?_
    filter_upwards with V
    ring
  rw [conjTranspose_mul_apply_sum]
  simp only [haarTensorAverage, Matrix.of_apply]
  have hR : MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          (K * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * Kᴴ) p q)
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ∑ a, ∑ b, K p a * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) a b
            * star (K q b)) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V =>
      conjTranspose_mul_apply_sum (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) K p q)
  rw [hR]
  symm
  calc MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ∑ a, ∑ b, K p a * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) a b
            * star (K q b))
      = ∑ a, MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∑ b, K p a * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) a b
              * star (K q b)) := by
        rw [MeasureTheory.integral_finsetSum Finset.univ
          (fun a _ => MeasureTheory.integrable_finsetSum Finset.univ (fun b _ => hterm a b))]
    _ = ∑ a, ∑ b, K p a * (MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) a b)) * star (K q b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun b _ => hterm a b)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]

/-- Successive conjugations by unitary tensor powers combine into conjugation by the tensor
power of the product. -/
theorem unitaryTensorPow_conj_mul (t : ℕ) (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    unitaryTensorPow t U * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)
        * (unitaryTensorPow t U)ᴴ
      = unitaryTensorPow t (U * V) * P * (unitaryTensorPow t (U * V))ᴴ := by
  rw [← unitaryTensorPow_mul, Matrix.conjTranspose_mul]
  simp only [mul_assoc]

/-- The Haar tensor average is invariant under conjugation by every `t`-fold tensor power of a
single-qubit unitary. -/
theorem haarTensorAverage_invariant (t : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    unitaryTensorPow t U * haarTensorAverage t P * (unitaryTensorPow t U)ᴴ
      = haarTensorAverage t P := by
  haveI : (haarUnitaryGroup (Fin 2)).IsMulLeftInvariant := by
    rw [haarUnitaryGroup]
    infer_instance
  ext p q
  rw [haarTensorAverage_conj_apply, haarTensorAverage, Matrix.of_apply]
  have hX : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (unitaryTensorPow t U * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)
          * (unitaryTensorPow t U)ᴴ) p q)
      = fun V => (unitaryTensorPow t (U * V) * P * (unitaryTensorPow t (U * V))ᴴ) p q := by
    funext V
    rw [unitaryTensorPow_conj_mul]
  rw [hX]
  exact MeasureTheory.integral_mul_left_eq_self (μ := haarUnitaryGroup (Fin 2))
    (fun W : Matrix.unitaryGroup (Fin 2) ℂ =>
      (unitaryTensorPow t W * P * (unitaryTensorPow t W)ᴴ) p q) U

/-- The Haar tensor average commutes with every `t`-fold tensor power of a single-qubit unitary. -/
theorem haarTensorAverage_commute (t : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    unitaryTensorPow t U * haarTensorAverage t P
      = haarTensorAverage t P * unitaryTensorPow t U := by
  have hU : (unitaryTensorPow t U)ᴴ * unitaryTensorPow t U = 1 := by
    have hstar : star (unitaryTensorPow t U) = (unitaryTensorPow t U)ᴴ := rfl
    rw [← hstar]
    exact Matrix.mem_unitaryGroup_iff'.mp (tensorPow_mem_unitaryGroup t U)
  calc unitaryTensorPow t U * haarTensorAverage t P
      = unitaryTensorPow t U * haarTensorAverage t P
          * ((unitaryTensorPow t U)ᴴ * unitaryTensorPow t U) := by
        rw [hU, mul_one]
    _ = unitaryTensorPow t U * haarTensorAverage t P * (unitaryTensorPow t U)ᴴ
          * unitaryTensorPow t U := by
        conv_rhs => rw [mul_assoc]
    _ = haarTensorAverage t P * unitaryTensorPow t U := by
        rw [haarTensorAverage_invariant t U P]

/-- Permutations of tensor positions commute with tensor powers of a single-qubit unitary. -/
theorem tensorPerm_mul_unitaryTensorPow (t : ℕ) (σ : Equiv.Perm (Fin t))
    (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorPerm t σ * unitaryTensorPow t V = unitaryTensorPow t V * tensorPerm t σ := by
  have hL : ∀ x y : Fin t → Fin 2,
      (tensorPerm t σ * unitaryTensorPow t V) x y
        = ∏ i, (V : Matrix (Fin 2) (Fin 2) ℂ) (x (σ.symm i)) (y i) := by
    intro x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (x ∘ σ.symm)]
    · rw [tensorPerm_apply, if_pos rfl, one_mul]
      simp only [unitaryTensorPow, tensorPow_apply, Function.comp_apply]
    · intro z _ hz
      rw [tensorPerm_apply, if_neg hz, zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ (x ∘ σ.symm)) hx
  have hR : ∀ x y : Fin t → Fin 2,
      (unitaryTensorPow t V * tensorPerm t σ) x y
        = ∏ i, (V : Matrix (Fin 2) (Fin 2) ℂ) (x i) (y (σ i)) := by
    intro x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (y ∘ σ)]
    · rw [tensorPerm_apply, if_pos ?_, mul_one]
      · simp only [unitaryTensorPow, tensorPow_apply, Function.comp_apply]
      · funext i
        simp [Function.comp, Equiv.symm_apply_apply]
    · intro z _ hz
      rw [tensorPerm_apply, if_neg ?_, mul_zero]
      intro hyz
      exact hz (by
        funext j
        have h := congrFun hyz (σ j)
        simpa [Function.comp, Equiv.symm_apply_apply] using h.symm)
    · intro hy
      exact absurd (Finset.mem_univ (y ∘ σ)) hy
  ext x y
  rw [hL x y, hR x y]
  refine Fintype.prod_equiv σ.symm _ _ fun i => ?_
  simp

/-- The trace of a product of finite complex matrices is the double sum of paired entries. -/
theorem trace_mul_apply_sum' {n : Type*} [Fintype n] (A K : Matrix n n ℂ) :
    (A * K).trace = ∑ p, ∑ r, A p r * K r p := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

/-- The trace of a Haar tensor average multiplied by a fixed matrix equals the integral of the
corresponding traces. -/
theorem haarTensorAverage_mul_trace (t : ℕ)
    (P K : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    (haarTensorAverage t P * K).trace
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ((unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * K).trace) := by
  have hterm : ∀ p r : Fin t → Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p r * K r p)
      (haarUnitaryGroup (Fin 2)) :=
    fun p r => (haarIntegrable_unitaryTensorPowConj t P p r).mul_const (K r p)
  have hL : (haarTensorAverage t P * K).trace
      = ∑ p, ∑ r, (MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p r) * K r p := by
    rw [trace_mul_apply_sum']
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    simp only [haarTensorAverage, Matrix.of_apply]
  have hR : MeasureTheory.integral (haarUnitaryGroup (Fin 2))
        (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ((unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * K).trace)
      = ∑ p, ∑ r, (MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p r) * K r p := by
    have hcongr : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ((unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * K).trace)
        = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ∑ p, ∑ r, (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p r * K r p := by
      funext V
      rw [trace_mul_apply_sum']
    rw [hcongr, MeasureTheory.integral_finsetSum Finset.univ
      (fun p _ => MeasureTheory.integrable_finsetSum Finset.univ (fun r _ => hterm p r))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun r _ => hterm p r)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MeasureTheory.integral_mul_const]
  exact hL.trans hR.symm

/-- Conjugation by a unitary tensor power preserves the trace weighted by a tensor permutation
matrix. -/
theorem trace_unitaryTensorPow_conj_mul_tensorPerm (t : ℕ) (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (σ : Equiv.Perm (Fin t)) (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    ((unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * tensorPerm t σ).trace
      = (P * tensorPerm t σ).trace := by
  have hAA : (unitaryTensorPow t V)ᴴ * unitaryTensorPow t V = 1 := by
    have hstar : star (unitaryTensorPow t V) = (unitaryTensorPow t V)ᴴ := rfl
    rw [← hstar]
    exact Matrix.mem_unitaryGroup_iff'.mp (tensorPow_mem_unitaryGroup t V)
  have hAA' : unitaryTensorPow t V * (unitaryTensorPow t V)ᴴ = 1 := by
    have hstar : star (unitaryTensorPow t V) = (unitaryTensorPow t V)ᴴ := rfl
    rw [← hstar]
    exact Matrix.mem_unitaryGroup_iff.mp (tensorPow_mem_unitaryGroup t V)
  have hkey : (unitaryTensorPow t V)ᴴ * tensorPerm t σ * unitaryTensorPow t V
      = tensorPerm t σ := by
    rw [Matrix.mul_assoc, tensorPerm_mul_unitaryTensorPow t σ V, ← Matrix.mul_assoc, hAA,
      Matrix.one_mul]
  have hkey' : (unitaryTensorPow t V)ᴴ * tensorPerm t σ
      = tensorPerm t σ * (unitaryTensorPow t V)ᴴ := by
    calc (unitaryTensorPow t V)ᴴ * tensorPerm t σ
        = (unitaryTensorPow t V)ᴴ * tensorPerm t σ
            * (unitaryTensorPow t V * (unitaryTensorPow t V)ᴴ) := by
          rw [hAA', Matrix.mul_one]
      _ = tensorPerm t σ * (unitaryTensorPow t V)ᴴ := by
          rw [← Matrix.mul_assoc, hkey]
  have hstep : (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * tensorPerm t σ
      = unitaryTensorPow t V * (P * (tensorPerm t σ * (unitaryTensorPow t V)ᴴ)) := by
    rw [Matrix.mul_assoc, hkey', Matrix.mul_assoc]
  have hmat : (P * (tensorPerm t σ * (unitaryTensorPow t V)ᴴ)) * unitaryTensorPow t V
      = P * tensorPerm t σ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hAA, Matrix.mul_one]
  rw [hstep, Matrix.trace_mul_comm (unitaryTensorPow t V)
    (P * (tensorPerm t σ * (unitaryTensorPow t V)ᴴ)), hmat]

/-- The Haar tensor average preserves each trace weighted by a tensor permutation matrix. -/
theorem haarTensorAverage_mul_tensorPerm_trace (t : ℕ) (σ : Equiv.Perm (Fin t))
    (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) :
    (haarTensorAverage t P * tensorPerm t σ).trace = (P * tensorPerm t σ).trace := by
  rw [haarTensorAverage_mul_trace]
  have hcongr : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ((unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) * tensorPerm t σ).trace)
      = fun _ => (P * tensorPerm t σ).trace := by
    funext V
    exact trace_unitaryTensorPow_conj_mul_tensorPerm t V σ P
  rw [hcongr, MeasureTheory.integral_const, haarUnitaryGroup_real_univ, one_smul]

/-- The matrix projecting onto the all-zero computational basis string of length `t`. -/
def zeroProj (t : ℕ) : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ :=
  Matrix.of fun x y => if x = 0 ∧ y = 0 then (1 : ℂ) else 0

/-- The only nonzero entry of `zeroProj t` is its all-zero row and all-zero column entry, which
is one. -/
theorem zeroProj_apply (t : ℕ) (x y : Fin t → Fin 2) :
    zeroProj t x y = if x = 0 ∧ y = 0 then (1 : ℂ) else 0 := rfl

/-- Permuting the positions of a bit string gives the zero string exactly when the original
string is zero. -/
theorem comp_symm_eq_zero_iff (t : ℕ) (x : Fin t → Fin 2) (σ : Equiv.Perm (Fin t)) :
    x ∘ σ.symm = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have h' := congrFun h (σ i)
    simpa [Function.comp, Equiv.symm_apply_apply] using h'
  · rintro rfl
    funext i
    rfl

/-- Left multiplication by a tensor permutation leaves the all-zero projector unchanged. -/
theorem tensorPerm_mul_zeroProj (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    tensorPerm t σ * zeroProj t = zeroProj t := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (x ∘ σ.symm)]
  · rw [tensorPerm_apply, if_pos rfl, one_mul]
    simp only [zeroProj_apply]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
      simp [hx, hy, comp_symm_eq_zero_iff t x σ]
  · intro z _ hz
    rw [tensorPerm_apply, if_neg hz, zero_mul]
  · intro hx
    exact absurd (Finset.mem_univ (x ∘ σ.symm)) hx

/-- The all-zero projector is idempotent. -/
theorem zeroProj_mul_zeroProj (t : ℕ) : zeroProj t * zeroProj t = zeroProj t := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single 0]
  · simp only [zeroProj_apply]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  · intro z _ hz
    simp [zeroProj_apply, hz]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-- The all-zero projector has trace one. -/
theorem trace_zeroProj (t : ℕ) : (zeroProj t).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_eq_single 0]
  · simp [zeroProj_apply]
  · intro z _ hz
    simp [zeroProj_apply, hz]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-- The equivalence on tensor-position permutations given by composition `τ ↦ σ.trans τ`. -/
def permTransEquiv (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    Equiv.Perm (Fin t) ≃ Equiv.Perm (Fin t) where
  toFun τ := σ.trans τ
  invFun ρ := σ.symm.trans ρ
  left_inv τ := by
    ext i
    simp [Equiv.trans_apply]
  right_inv ρ := by
    ext i
    simp [Equiv.trans_apply]

/-- Evaluates the permutation-composition equivalence as `σ.trans τ`. -/
@[simp]
theorem permTransEquiv_apply (t : ℕ) (σ τ : Equiv.Perm (Fin t)) :
    permTransEquiv t σ τ = σ.trans τ := rfl

/-- The average of all tensor permutation matrices, with normalization `1 / t!`. -/
def symProj (t : ℕ) : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ :=
  ((t.factorial : ℂ))⁻¹ • ∑ σ : Equiv.Perm (Fin t), tensorPerm t σ

/-- The complex cast of a natural-number factorial is nonzero. -/
theorem factorial_cast_ne_zero (t : ℕ) : ((t.factorial : ℂ)) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero t

/-- Left multiplication by any tensor permutation leaves `symProj t` unchanged. -/
theorem tensorPerm_mul_symProj (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    tensorPerm t σ * symProj t = symProj t := by
  rw [symProj, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  refine Fintype.sum_equiv (permTransEquiv t σ)
    (fun τ => tensorPerm t σ * tensorPerm t τ) (fun ρ => tensorPerm t ρ) fun τ => ?_
  exact (tensorPerm_mul t σ τ).symm

/-- The symmetrizing matrix `symProj t` is idempotent. -/
theorem symProj_mul_symProj (t : ℕ) : symProj t * symProj t = symProj t := by
  rw [symProj, Matrix.smul_mul, Matrix.mul_smul, Fintype.sum_mul_sum]
  have hinner : ∀ σ : Equiv.Perm (Fin t),
      (∑ τ : Equiv.Perm (Fin t), tensorPerm t σ * tensorPerm t τ)
        = ∑ ρ : Equiv.Perm (Fin t), tensorPerm t ρ := by
    intro σ
    refine Fintype.sum_equiv (permTransEquiv t σ)
      (fun τ => tensorPerm t σ * tensorPerm t τ) (fun ρ => tensorPerm t ρ) fun τ => ?_
    exact (tensorPerm_mul t σ τ).symm
  rw [Finset.sum_congr rfl fun σ _ => hinner σ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (factorial_cast_ne_zero t), mul_one]

/-- The symmetrizing matrix acts as the identity on the all-zero projector. -/
theorem symProj_mul_zeroProj (t : ℕ) : symProj t * zeroProj t = zeroProj t := by
  rw [symProj, Matrix.smul_mul, Finset.sum_mul]
  rw [show (∑ σ : Equiv.Perm (Fin t), tensorPerm t σ * zeroProj t)
      = ∑ _σ : Equiv.Perm (Fin t), zeroProj t from
        Finset.sum_congr rfl fun σ _ => tensorPerm_mul_zeroProj t σ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (factorial_cast_ne_zero t), one_smul]

/-- If left multiplication by a tensor permutation fixes `P`, it also fixes its conjugate by any
unitary tensor power. -/
theorem tensorPerm_mul_conjTensorPow (t : ℕ) (σ : Equiv.Perm (Fin t))
    (V : Matrix.unitaryGroup (Fin 2) ℂ) (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ)
    (hP : tensorPerm t σ * P = P) :
    tensorPerm t σ * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)
      = unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ := by
  calc tensorPerm t σ * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)
      = (tensorPerm t σ * unitaryTensorPow t V) * P * (unitaryTensorPow t V)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = (unitaryTensorPow t V * tensorPerm t σ) * P * (unitaryTensorPow t V)ᴴ := by
        rw [tensorPerm_mul_unitaryTensorPow t σ V]
    _ = unitaryTensorPow t V * (tensorPerm t σ * P) * (unitaryTensorPow t V)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ := by
        rw [hP]

/-- If left multiplication by a tensor permutation fixes `P`, it also fixes the Haar tensor
average of `P`. -/
theorem tensorPerm_mul_haarTensorAverage (t : ℕ) (σ : Equiv.Perm (Fin t))
    (P : Matrix (Fin t → Fin 2) (Fin t → Fin 2) ℂ) (hP : tensorPerm t σ * P = P) :
    tensorPerm t σ * haarTensorAverage t P = haarTensorAverage t P := by
  ext p q
  have hterm : ∀ r : Fin t → Fin 2, MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        tensorPerm t σ p r * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) r q)
      (haarUnitaryGroup (Fin 2)) :=
    fun r => (haarIntegrable_unitaryTensorPowConj t P r q).const_mul _
  have hL : (∑ r, tensorPerm t σ p r * haarTensorAverage t P r q)
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            (tensorPerm t σ * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)) p q) := by
    have h1 : ∀ r : Fin t → Fin 2, tensorPerm t σ p r * haarTensorAverage t P r q
        = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
            (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
              tensorPerm t σ p r * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) r q) := by
      intro r
      rw [haarTensorAverage, Matrix.of_apply, MeasureTheory.integral_const_mul]
    rw [Finset.sum_congr rfl fun r _ => h1 r]
    rw [← MeasureTheory.integral_finsetSum Finset.univ (fun r _ => hterm r)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
    show (∑ r, tensorPerm t σ p r
        * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) r q)
      = (tensorPerm t σ * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)) p q
    rw [Matrix.mul_apply]
  rw [Matrix.mul_apply, hL]
  rw [haarTensorAverage, Matrix.of_apply]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  show (tensorPerm t σ * (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ)) p q
    = (unitaryTensorPow t V * P * (unitaryTensorPow t V)ᴴ) p q
  rw [tensorPerm_mul_conjTensorPow t σ V P hP]

/-- The Haar tensor average of the all-zero projector is fixed by left multiplication by the
symmetrizing matrix. -/
theorem symProj_mul_haarTensorAverage_zeroProj (t : ℕ) :
    symProj t * haarTensorAverage t (zeroProj t) = haarTensorAverage t (zeroProj t) := by
  rw [symProj, Matrix.smul_mul, Finset.sum_mul]
  rw [show (∑ σ : Equiv.Perm (Fin t),
        tensorPerm t σ * haarTensorAverage t (zeroProj t))
      = ∑ _σ : Equiv.Perm (Fin t), haarTensorAverage t (zeroProj t) from
        Finset.sum_congr rfl fun σ _ =>
          tensorPerm_mul_haarTensorAverage t σ (zeroProj t) (tensorPerm_mul_zeroProj t σ)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ (factorial_cast_ne_zero t), one_smul]

/-- The trace of a tensor permutation matrix counts bit strings fixed by the corresponding
permutation of positions. -/
theorem trace_tensorPerm (t : ℕ) (σ : Equiv.Perm (Fin t)) :
    (tensorPerm t σ).trace
      = ((Finset.univ.filter fun x : Fin t → Fin 2 => x = x ∘ σ.symm).card : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, tensorPerm_apply]
  rw [Finset.sum_boole]

/-- The symmetrizing matrix on three qubits has trace four. -/
theorem trace_symProj_three : (symProj 3).trace = 4 := by
  rw [symProj, Matrix.trace_smul, Matrix.trace_sum]
  have h : (∑ σ : Equiv.Perm (Fin 3), (tensorPerm 3 σ).trace)
      = ((∑ σ : Equiv.Perm (Fin 3),
          (Finset.univ.filter fun x : Fin 3 → Fin 2 => x = x ∘ σ.symm).card : ℕ) : ℂ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun σ _ => trace_tensorPerm 3 σ
  rw [h]
  have h24 : (∑ σ : Equiv.Perm (Fin 3),
      (Finset.univ.filter fun x : Fin 3 → Fin 2 => x = x ∘ σ.symm).card) = 24 := by decide
  rw [h24]
  norm_num

/-- The symmetrizing matrix on four qubits has trace five. -/
theorem trace_symProj_four : (symProj 4).trace = 5 := by
  rw [symProj, Matrix.trace_smul, Matrix.trace_sum]
  have h : (∑ σ : Equiv.Perm (Fin 4), (tensorPerm 4 σ).trace)
      = ((∑ σ : Equiv.Perm (Fin 4),
          (Finset.univ.filter fun x : Fin 4 → Fin 2 => x = x ∘ σ.symm).card : ℕ) : ℂ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun σ _ => trace_tensorPerm 4 σ
  rw [h]
  have h120 : (∑ σ : Equiv.Perm (Fin 4),
      (Finset.univ.filter fun x : Fin 4 → Fin 2 => x = x ∘ σ.symm).card) = 120 := by decide
  rw [h120]
  norm_num

/-- The single-qubit permutation matrix exchanging zero and one. -/
def swapUnitary : Matrix (Fin 2) (Fin 2) ℂ := permMatrix (Fin 2) (Equiv.swap (0 : Fin 2) 1)

/-- The matrix `swapUnitary` is unitary. -/
theorem swapUnitary_mem : swapUnitary ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  permMatrix_mem_unitaryGroup (Fin 2) (Equiv.swap (0 : Fin 2) 1)

/-- Left multiplication by `swapUnitary` exchanges the two rows of a single-qubit matrix. -/
theorem swapUnitary_mul_entry (V : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (swapUnitary * V) i j = V (Equiv.swap (0 : Fin 2) 1 i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap (0 : Fin 2) 1 i)]
  · rw [show swapUnitary i (Equiv.swap (0 : Fin 2) 1 i) = 1 by
      simp [swapUnitary, permMatrix, Matrix.of_apply]]
    rw [one_mul]
  · intro k _ hk
    rw [show swapUnitary i k = 0 by simp [swapUnitary, permMatrix, Matrix.of_apply, hk]]
    rw [zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (Equiv.swap (0 : Fin 2) 1 i)) h

/-- Each entry is a continuous function on the single-qubit unitary group. -/
theorem continuous_unitaryEntry (i j : Fin 2) :
    Continuous fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (V : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  have hk : Continuous fun r : Fin 2 → Fin 2 → ℂ => r i := continuous_apply i
  have ha : Continuous fun s : Fin 2 → ℂ => s j := continuous_apply j
  exact (ha.comp hk).comp continuous_subtype_val

/-- The squared norms of the two entries in the first column of a single-qubit unitary sum to
one. -/
theorem unitary_col_norm_sq (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2 + ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = 1 := by
  have e : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    intro z
    have h1 := Complex.normSq_eq_conj_mul_self (z := z)
    have h2 := Complex.normSq_eq_norm_sq z
    calc ((‖z‖ ^ 2 : ℝ) : ℂ) = ((Complex.normSq z : ℝ) : ℂ) := by rw [h2]
      _ = star z * z := h1
  have e2 : ∀ z : ℂ, (((↑‖z‖ : ℂ)) ^ 2) = star z * z := by
    intro z
    rw [← e z]
    push_cast
    rfl
  have h := Matrix.mem_unitaryGroup_iff'.mp V.2
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h00
  have key : (((‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2
        + ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [e2 ((V : Matrix (Fin 2) (Fin 2) ℂ) 0 0), e2 ((V : Matrix (Fin 2) (Fin 2) ℂ) 1 0)]
    exact h00
  exact_mod_cast key

/-- Every natural power of a real number in the interval from zero to one is at most one. -/
theorem real_pow_le_one_of_le_one {x : ℝ} (h0 : 0 ≤ x) (h : x ≤ 1) (n : ℕ) : x ^ n ≤ 1 := by
  induction n with
  | zero => simpa using le_rfl
  | succ k ih =>
      rw [pow_succ]
      simpa using mul_le_mul ih h h0 (zero_le_one)

/-- The Haar average of `‖V 0 0‖^(2 * A) * ‖V 1 0‖^(2 * B)` for a single-qubit unitary `V`. -/
def symMoment (A B : ℕ) : ℝ :=
  MeasureTheory.integral (haarUnitaryGroup (Fin 2))
    fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * A)
        * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * B)

/-- The integrand defining each mixed squared-modulus moment `symMoment A B` is Haar integrable. -/
theorem integrable_symMoment (A B : ℕ) : MeasureTheory.Integrable
    (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * A)
        * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * B))
    (haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  refine MeasureTheory.Integrable.of_bound
    (Continuous.aestronglyMeasurable
      (((continuous_unitaryEntry 0 0).norm.pow (2 * A)).mul
        ((continuous_unitaryEntry 1 0).norm.pow (2 * B)))) 1 ?_
  filter_upwards with V
  have hX : ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ 1 := unitaryGroup_entry_norm_le_one V.2 0 0
  have hY : ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ 1 := unitaryGroup_entry_norm_le_one V.2 1 0
  have p1 : ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * A) ≤ 1 :=
    real_pow_le_one_of_le_one (norm_nonneg _) hX _
  have p2 : ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * B) ≤ 1 :=
    real_pow_le_one_of_le_one (norm_nonneg _) hY _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _), abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa using mul_le_mul p1 p2 (pow_nonneg (norm_nonneg _) _) (zero_le_one)

/-- The two moments obtained by increasing either exponent by one sum to `symMoment A B`. -/
theorem symMoment_succ (A B : ℕ) :
    symMoment (A + 1) B + symMoment A (B + 1) = symMoment A B := by
  rw [symMoment, symMoment, symMoment, ← MeasureTheory.integral_add
    (integrable_symMoment (A + 1) B) (integrable_symMoment A (B + 1))]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only []
  rw [show 2 * (A + 1) = 2 * A + 2 by omega, show 2 * (B + 1) = 2 * B + 2 by omega,
    pow_add, pow_add]
  have h1 := unitary_col_norm_sq V
  have hkey : (‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * A)
      * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * B))
      * (‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2
        + ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2)
      = ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * A)
        * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * B) := by
    rw [h1, mul_one]
  rw [← hkey]
  ring

/-- The mixed Haar moment is symmetric in its two exponents. -/
theorem symMoment_swap (A B : ℕ) : symMoment A B = symMoment B A := by
  haveI : (haarUnitaryGroup (Fin 2)).IsMulLeftInvariant := by
    rw [haarUnitaryGroup]
    infer_instance
  rw [symMoment, symMoment]
  have hL := (MeasureTheory.integral_mul_left_eq_self (μ := haarUnitaryGroup (Fin 2))
      (fun W : Matrix.unitaryGroup (Fin 2) ℂ =>
        ‖(W : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * A)
          * ‖(W : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * B))
      (⟨swapUnitary, swapUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ)).symm
  rw [hL]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  have s0 : Equiv.swap (0 : Fin 2) 1 0 = 1 := by decide
  have s1 : Equiv.swap (0 : Fin 2) 1 1 = 0 := by decide
  have e0 : (swapUnitary * (V : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
      = (V : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    rw [swapUnitary_mul_entry, s0]
  have e1 : (swapUnitary * (V : Matrix (Fin 2) (Fin 2) ℂ)) 1 0
      = (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [swapUnitary_mul_entry, s1]
  simp only [Submonoid.coe_mul]
  rw [e0, e1]
  ring

/-- The zeroth mixed Haar moment is one. -/
theorem symMoment_zero_zero : symMoment 0 0 = 1 := by
  rw [symMoment]
  have hcongr : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * 0)
          * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * 0))
      = fun _ => (1 : ℝ) := by
    funext V
    simp
  rw [hcongr, MeasureTheory.integral_const, haarUnitaryGroup_real_univ, one_smul]

/-- Each first squared-modulus Haar moment is one half. -/
theorem symMoment_one : symMoment 1 0 = 1 / 2 ∧ symMoment 0 1 = 1 / 2 := by
  have h1 : symMoment (0 + 1) 0 + symMoment 0 (0 + 1) = symMoment 0 0 := symMoment_succ 0 0
  simp only [zero_add] at h1
  rw [symMoment_zero_zero] at h1
  have hswap : symMoment 1 0 = symMoment 0 1 := symMoment_swap 1 0
  rw [← hswap] at h1
  constructor <;> linarith

/-- An entry of the averaged all-zero projector is the Haar integral of a product of
first-column entries and their conjugates. -/
theorem haarTensorAverage_zeroProj_apply (t : ℕ) (x y : Fin t → Fin 2) :
    haarTensorAverage t (zeroProj t) x y
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
              * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0))) := by
  simp only [haarTensorAverage, Matrix.of_apply]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only []
  rw [conjTranspose_mul_apply_sum]
  rw [Finset.sum_eq_single (0 : Fin t → Fin 2)]
  · rw [Finset.sum_eq_single (0 : Fin t → Fin 2)]
    · rw [zeroProj_apply, if_pos ⟨rfl, rfl⟩, mul_one]
      simp only [unitaryTensorPow, tensorPow_apply]
      rw [star_prod, Finset.prod_mul_distrib]
      rfl
    · intro b _ hb
      simp [zeroProj_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin t → Fin 2)) h
  · intro a _ ha
    simp [zeroProj_apply, ha]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin t → Fin 2)) h

/-- The Hamming weight of a bit string, defined as the sum of its bit values. -/
def hamWeight {t : ℕ} (x : Fin t → Fin 2) : ℕ := ∑ i, (x i).val

/-- The Hamming weight of a length-`t` bit string is at most `t`. -/
theorem hamWeight_le {t : ℕ} (x : Fin t → Fin 2) : hamWeight x ≤ t := by
  classical
  rw [hamWeight]
  calc ∑ i, (x i).val ≤ ∑ _i, 1 := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (Fin.isLt (x i))
    _ = t := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp

/-- The complex phase `(3 + 4 * Complex.I) / 5` used to separate small Hamming weights. -/
def torusRoot : ℂ := (3 + 4 * Complex.I) / 5

/-- Expands a product of two complex numbers written in terms of their real and imaginary parts. -/
theorem complex_mul_aux (a b c d : ℝ) : (a + b * Complex.I) * (c + d * Complex.I)
    = (a * c - b * d) + (a * d + b * c) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im] <;> ring

/-- The complex number `torusRoot` has squared modulus one. -/
theorem star_mul_self_torusRoot : star torusRoot * torusRoot = 1 := by
  have hre : torusRoot.re = 3 / 5 := by
    rw [torusRoot]
    norm_num [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have him : torusRoot.im = 4 / 5 := by
    rw [torusRoot]
    norm_num [Complex.div_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hns : Complex.normSq torusRoot = 1 := by
    rw [Complex.normSq_apply, hre, him]
    norm_num
  calc star torusRoot * torusRoot = (starRingEnd ℂ) torusRoot * torusRoot := rfl
    _ = ((Complex.normSq torusRoot : ℝ) : ℂ) := Complex.normSq_eq_conj_mul_self.symm
    _ = 1 := by rw [hns]; norm_num

/-- The square of `torusRoot` is `(-7 + 24 * Complex.I) / 25`. -/
theorem torusRoot_pow_two : torusRoot ^ 2 = (-7 + 24 * Complex.I) / 25 := by
  rw [torusRoot, div_pow, sq]
  apply Complex.ext <;>
    simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im] <;>
    norm_num

/-- The cube of `torusRoot` is `(-117 + 44 * Complex.I) / 125`. -/
theorem torusRoot_pow_three : torusRoot ^ 3 = (-117 + 44 * Complex.I) / 125 := by
  rw [pow_succ, torusRoot_pow_two, torusRoot]
  apply Complex.ext <;>
    simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im] <;>
    norm_num

/-- The fourth power of `torusRoot` is `(-527 - 336 * Complex.I) / 625`. -/
theorem torusRoot_pow_four : torusRoot ^ 4 = (-527 - 336 * Complex.I) / 625 := by
  rw [show torusRoot ^ 4 = torusRoot ^ 2 * torusRoot ^ 2 from by rw [← mul_pow, ← sq, ← pow_mul],
    torusRoot_pow_two]
  apply Complex.ext <;>
    simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im] <;>
    norm_num

/-- No positive power of `torusRoot` with exponent at most four equals one. -/
theorem torusRoot_pow_ne_one : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → torusRoot ^ k ≠ 1 := by
  intro k hk1 hk4
  interval_cases k
  · intro h
    rw [torusRoot] at h
    field_simp at h
    apply_fun Complex.im at h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im] at h
    norm_num at h
  · intro h
    rw [torusRoot_pow_two] at h
    field_simp at h
    apply_fun Complex.im at h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im] at h
    norm_num at h
  · intro h
    rw [torusRoot_pow_three] at h
    field_simp at h
    apply_fun Complex.im at h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im] at h
    norm_num at h
  · intro h
    rw [torusRoot_pow_four] at h
    field_simp at h
    apply_fun Complex.im at h
    simp only [Complex.sub_im, Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_im] at h
    norm_num at h

/-- No nonzero integer power of `torusRoot` with exponent between negative four and four equals
one. -/
theorem torusRoot_zpow_ne_one {d : ℤ} (hd : d ≠ 0) (hlo : -4 ≤ d) (hhi : d ≤ 4) :
    torusRoot ^ d ≠ 1 := by
  have hkey : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → torusRoot ^ ((k : ℕ) : ℤ) ≠ 1 := by
    intro k hk1 hk4
    rw [zpow_natCast]
    exact torusRoot_pow_ne_one k hk1 hk4
  rcases lt_or_gt_of_ne hd with h | h
  · intro hgoal
    have hpos : 1 ≤ -d := by omega
    have h4 : -d ≤ 4 := by omega
    have hn : (((-d).toNat : ℕ) : ℤ) = -d := Int.toNat_of_nonneg (by omega)
    have hz : torusRoot ^ (-d) = 1 := by
      rw [zpow_neg, hgoal]
      simp
    exact hkey ((-d).toNat) (by omega) (by omega) (by rw [hn]; exact hz)
  · have h0 : (0 : ℤ) ≤ d := by omega
    rw [← Int.toNat_of_nonneg h0]
    exact hkey _ (by omega) (by omega)

/-- The two phases used as diagonal entries of `phaseUnitary`. -/
def phaseVec : Fin 2 → ℂ := fun i => if i = 0 then torusRoot else 1

/-- Each entry of `phaseVec` has squared modulus one. -/
theorem phaseVec_star_mul (i : Fin 2) : star (phaseVec i) * phaseVec i = 1 := by
  fin_cases i
  · exact star_mul_self_torusRoot
  · simp [phaseVec]

/-- The diagonal single-qubit matrix with diagonal entries `phaseVec`. -/
def phaseUnitary : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal phaseVec

/-- The diagonal matrix `phaseUnitary` is unitary. -/
theorem phaseUnitary_mem : phaseUnitary ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  diagonal_mem_unitaryGroup (Fin 2) phaseVec phaseVec_star_mul

/-- Left multiplication by `phaseUnitary` scales row `i` by `phaseVec i`. -/
theorem phaseUnitary_mul_entry (V : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (phaseUnitary * V) i j = phaseVec i * V i j :=
  Matrix.diagonal_mul _ _ _ _

/-- A finite product of integer powers of a nonzero complex number is the power with exponent
equal to their sum. -/
theorem prod_zpow_sum {ι : Type*} {w : ℂ} (hw : w ≠ 0) (s : Finset ι) (c : ι → ℤ) :
    ∏ i ∈ s, w ^ (c i) = w ^ (s.sum c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, ih, zpow_add' (Or.inl hw)]

/-- The phase contributed by a pair of bits is `torusRoot` raised to the difference of their
values. -/
theorem phase_factor {t : ℕ} (x y : Fin t → Fin 2) (i : Fin t) :
    phaseVec (x i) * star (phaseVec (y i))
      = torusRoot ^ (((y i).val : ℤ) - ((x i).val : ℤ)) := by
  have key : ∀ a b : Fin 2, phaseVec a * star (phaseVec b)
      = torusRoot ^ (((b : Fin 2).val : ℤ) - ((a : Fin 2).val : ℤ)) := by
    intro a b
    have hw : torusRoot * star torusRoot = 1 := by rw [mul_comm, star_mul_self_torusRoot]
    have hst : star torusRoot = torusRoot ⁻¹ := eq_inv_of_mul_eq_one_left star_mul_self_torusRoot
    fin_cases a <;> fin_cases b <;>
      simp_all [phaseVec, hw, hst, zpow_zero, zpow_one, zpow_neg_one, Fin.val_zero, Fin.val_one]
  exact key (x i) (y i)

/-- The product of bitwise phase factors is `torusRoot` raised to the difference of the Hamming
weights. -/
theorem phaseProd_eq {t : ℕ} (x y : Fin t → Fin 2) :
    (∏ i, (phaseVec (x i) * star (phaseVec (y i))))
      = torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ)) := by
  have hw0 : torusRoot ≠ 0 := by
    intro h0
    have h1 := star_mul_self_torusRoot
    rw [h0] at h1
    simp at h1
  rw [Finset.prod_congr rfl fun i _ => phase_factor x y i, prod_zpow_sum hw0, hamWeight, hamWeight,
    Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum]

/-- Conjugation of the all-zero projector by a unitary tensor power has entries given by
products of first-column entries and their conjugates. -/
theorem zeroProjEntry_eq (t : ℕ) (V : Matrix.unitaryGroup (Fin 2) ℂ) (x y : Fin t → Fin 2) :
    (unitaryTensorPow t V * zeroProj t * (unitaryTensorPow t V)ᴴ) x y
      = ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
        * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)) := by
  rw [conjTranspose_mul_apply_sum]
  rw [Finset.sum_eq_single (0 : Fin t → Fin 2)]
  · rw [Finset.sum_eq_single (0 : Fin t → Fin 2)]
    · rw [zeroProj_apply, if_pos ⟨rfl, rfl⟩, mul_one]
      simp only [unitaryTensorPow, tensorPow_apply]
      rw [star_prod, Finset.prod_mul_distrib]
      rfl
    · intro b _ hb
      simp [zeroProj_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin t → Fin 2)) h
  · intro a _ ha
    simp [zeroProj_apply, ha]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin t → Fin 2)) h

/-- The product formula for an entry of the conjugated all-zero projector is Haar integrable. -/
theorem integrable_zeroProjEntry (t : ℕ) (x y : Fin t → Fin 2) : MeasureTheory.Integrable
    (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
        * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
    (haarUnitaryGroup (Fin 2)) :=
  (haarIntegrable_unitaryTensorPowConj t (zeroProj t) x y).congr
    (Filter.Eventually.of_forall fun V => zeroProjEntry_eq t V x y)

/-- Each entry of the averaged all-zero projector equals itself multiplied by the phase
determined by the Hamming-weight difference. -/
theorem haarTensorAverage_zeroProj_phase_mul (t : ℕ) (x y : Fin t → Fin 2) :
    haarTensorAverage t (zeroProj t) x y
      = torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ))
        * haarTensorAverage t (zeroProj t) x y := by
  have hinv : (haarUnitaryGroup (Fin 2)).IsMulLeftInvariant := by
    rw [haarUnitaryGroup]
    infer_instance
  have hL : MeasureTheory.integral (haarUnitaryGroup (Fin 2))
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ∏ i, (((⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) * V :
            Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
          * star (((⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) * V :
            Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
              * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0))) :=
    @MeasureTheory.integral_mul_left_eq_self _ ℂ _ _ _ (haarUnitaryGroup (Fin 2)) _ _ hinv
      (fun W : Matrix.unitaryGroup (Fin 2) ℂ =>
        ∏ i, ((W : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
          * star ((W : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
      (⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ)
  calc haarTensorAverage t (zeroProj t) x y
      = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
              * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0))) :=
        haarTensorAverage_zeroProj_apply t x y
    _ = MeasureTheory.integral (haarUnitaryGroup (Fin 2))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∏ i, (((⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) * V :
                Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
              * star (((⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) * V :
                Matrix (Fin 2) (Fin 2) ℂ) (y i) 0))) := hL.symm
    _ = torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ))
          * MeasureTheory.integral (haarUnitaryGroup (Fin 2))
              (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
                ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
                  * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0))) := by
        have hfun : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
              ∏ i, (((⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) * V :
                  Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
                * star (((⟨phaseUnitary, phaseUnitary_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) * V :
                  Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
            = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
                torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ))
                * ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
                  * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)) := by
          funext V
          simp only [Submonoid.coe_mul]
          calc ∏ i, ((phaseUnitary * (V : Matrix (Fin 2) (Fin 2) ℂ)) (x i) 0
                * star ((phaseUnitary * (V : Matrix (Fin 2) (Fin 2) ℂ)) (y i) 0))
              = (∏ i, (phaseVec (x i) * star (phaseVec (y i))))
                * ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
                  * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)) := by
                rw [← Finset.prod_mul_distrib]
                exact Finset.prod_congr rfl fun i _ => by
                  rw [phaseUnitary_mul_entry, phaseUnitary_mul_entry, star_mul]
                  ring
            _ = torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ))
                * ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
                  * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)) := by rw [phaseProd_eq]
        conv_lhs => rw [hfun]
        haveI hint : MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
              * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
            (haarUnitaryGroup (Fin 2)) := integrable_zeroProjEntry t x y
        exact MeasureTheory.integral_const_mul (r :=
          torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ)))
          (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
            ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
              * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
    _ = torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ))
          * haarTensorAverage t (zeroProj t) x y := by
        rw [haarTensorAverage_zeroProj_apply]

/-- For at most four tensor copies, entries of the averaged all-zero projector vanish between
strings of different Hamming weights. -/
theorem haarTensorAverage_zeroProj_of_hamWeight_ne {t : ℕ} (ht : t ≤ 4)
    (x y : Fin t → Fin 2) (hne : hamWeight x ≠ hamWeight y) :
    haarTensorAverage t (zeroProj t) x y = 0 := by
  have hd : ((hamWeight y : ℤ) - (hamWeight x : ℤ)) ≠ 0 := by
    intro h
    apply hne
    exact_mod_cast (sub_eq_zero.mp h).symm
  have h1 : ((hamWeight y : ℤ)) ≤ 4 := by exact_mod_cast le_trans (hamWeight_le y) ht
  have h2 : ((hamWeight x : ℤ)) ≤ 4 := by exact_mod_cast le_trans (hamWeight_le x) ht
  have h3 : (0 : ℤ) ≤ (hamWeight y : ℤ) := by exact_mod_cast Nat.zero_le _
  have h4 : (0 : ℤ) ≤ (hamWeight x : ℤ) := by exact_mod_cast Nat.zero_le _
  have hlo : (-4 : ℤ) ≤ ((hamWeight y : ℤ) - (hamWeight x : ℤ)) := by omega
  have hhi : ((hamWeight y : ℤ) - (hamWeight x : ℤ)) ≤ 4 := by omega
  have h := haarTensorAverage_zeroProj_phase_mul t x y
  have key : (1 - torusRoot ^ ((hamWeight y : ℤ) - (hamWeight x : ℤ)))
      * haarTensorAverage t (zeroProj t) x y = 0 := by
    rw [one_sub_mul, ← h, sub_self]
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 (sub_ne_zero_of_ne (fun hc => torusRoot_zpow_ne_one hd hlo hhi hc.symm))
  · exact h0

/-- The natural value of a bit is one when it equals one and zero otherwise. -/
theorem fin_two_val_eq (b : Fin 2) : (b.val : ℕ) = if b = 1 then 1 else 0 := by
  fin_cases b <;> simp

/-- A bit is nonzero exactly when it is one. -/
theorem fin_two_ne_zero_iff (b : Fin 2) : ¬b = 0 ↔ b = 1 := by
  fin_cases b <;> simp

/-- The complex cast of the squared norm of `z` equals `star z * z`. -/
theorem complex_cast_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  rw [← Complex.normSq_eq_norm_sq z]
  exact Complex.normSq_eq_conj_mul_self

/-- The Hamming weight equals the number of positions containing the bit one. -/
theorem hamWeight_eq_card {t : ℕ} (x : Fin t → Fin 2) :
    (Finset.univ.filter fun i => x i = 1).card = hamWeight x := by
  rw [Finset.card_filter, hamWeight]
  exact Finset.sum_congr rfl fun i _ => (fin_two_val_eq (x i)).symm

/-- Splits a product selected by bit values into powers indexed by the numbers of zero and one
bits. -/
theorem prod_if_split {t : ℕ} (x : Fin t → Fin 2) (a b : ℂ) :
    (∏ i, (if x i = 0 then a else b))
      = a ^ ((Finset.univ.filter fun i => x i = 0).card)
        * b ^ ((Finset.univ.filter fun i => x i = 1).card) := by
  have h1 : (Finset.univ.filter fun i => x i = 1) = Finset.univ.filter fun i => x i ≠ 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (fin_two_ne_zero_iff (x i)).symm
  rw [h1]
  conv_lhs => rw [← Finset.filter_union_filter_not_eq (fun i => x i = 0) Finset.univ]
  rw [Finset.prod_union (Finset.disjoint_filter_filter_not _ _ _)]
  rw [Finset.prod_congr rfl fun i hi => if_pos (Finset.mem_filter.mp hi).2,
    Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_filter.mp hi).2,
    Finset.prod_const, Finset.prod_const]

/-- The product of `u^A * v^B` with its conjugate factors into powers of `u * star u` and `v *
star v`. -/
theorem complex_pow_star_pow (u v : ℂ) (A B : ℕ) :
    (u ^ A * v ^ B) * star (u ^ A * v ^ B)
      = (u * star u) ^ A * (v * star v) ^ B := by
  rw [star_mul, star_pow, star_pow, mul_pow, mul_pow]
  ring

/-- The power `(z * star z)^n` is the complex cast of `‖z‖^(2 * n)`. -/
theorem cast_norm_pow (z : ℂ) (n : ℕ) :
    (z * star z) ^ n = (((‖z‖ ^ (2 * n) : ℝ) : ℂ)) := by
  rw [mul_comm z (star z), ← complex_cast_norm_sq, ← Complex.ofReal_pow, ← pow_mul]

/-- For strings of equal Hamming weight, the first-column entry product equals the corresponding
mixed squared-modulus moment integrand. -/
theorem zeroProjEntry_eq_symMoment_integrand {t : ℕ} (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (x y : Fin t → Fin 2) (hk : hamWeight x = hamWeight y) :
    (∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
        * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
      = ((‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * (t - hamWeight x))
          * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * hamWeight x) : ℝ) : ℂ) := by
  have hxy : ∀ (z : Fin t → Fin 2) (i : Fin t),
      (V : Matrix (Fin 2) (Fin 2) ℂ) (z i) 0
        = if z i = 0 then (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0
          else (V : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    intro z i
    by_cases h : z i = 0
    · simp [h]
    · rw [if_neg h, (fin_two_ne_zero_iff (z i)).mp h]
  rw [Finset.prod_mul_distrib, ← star_prod]
  have hpx : (∏ i, (V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0)
      = (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ ((Finset.univ.filter fun i => x i = 0).card)
        * (V : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ ((Finset.univ.filter fun i => x i = 1).card) := by
    rw [Finset.prod_congr rfl fun i _ => hxy x i]
    exact prod_if_split x _ _
  have hpy : (∏ i, (V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)
      = (V : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ ((Finset.univ.filter fun i => y i = 0).card)
        * (V : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ ((Finset.univ.filter fun i => y i = 1).card) := by
    rw [Finset.prod_congr rfl fun i _ => hxy y i]
    exact prod_if_split y _ _
  have hcardgen : ∀ z : Fin t → Fin 2,
      ((Finset.univ.filter fun i => z i = 0).card) = t - hamWeight z := by
    intro z
    have hsplit : (Finset.univ.filter fun i => z i = 0).card
        + (Finset.univ.filter fun i => z i = 1).card = t := by
      have h2 : (Finset.univ.filter fun i => z i = 1)
          = Finset.univ.filter fun i => z i ≠ 0 := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (fin_two_ne_zero_iff (z i)).symm
      rw [h2, ← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter_not Finset.univ Finset.univ (fun i => z i = 0)),
        Finset.filter_union_filter_not_eq, Finset.card_univ, Fintype.card_fin]
    rw [hamWeight_eq_card z] at hsplit
    omega
  rw [hpx, hpy, hamWeight_eq_card x, hamWeight_eq_card y, hcardgen x, hcardgen y, ← hk,
    complex_pow_star_pow, cast_norm_pow, cast_norm_pow, Complex.ofReal_mul]

/-- An entry between strings of equal Hamming weight is the complex cast of the corresponding
`symMoment`. -/
theorem haarTensorAverage_zeroProj_apply_eq_symMoment {t : ℕ} (x y : Fin t → Fin 2)
    (hk : hamWeight x = hamWeight y) :
    haarTensorAverage t (zeroProj t) x y
      = ((symMoment (t - hamWeight x) (hamWeight x) : ℝ) : ℂ) := by
  rw [haarTensorAverage_zeroProj_apply]
  haveI hint : MeasureTheory.Integrable
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * (t - hamWeight x))
          * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * hamWeight x))
      (haarUnitaryGroup (Fin 2)) := integrable_symMoment _ _
  have hfun : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ∏ i, ((V : Matrix (Fin 2) (Fin 2) ℂ) (x i) 0
          * star ((V : Matrix (Fin 2) (Fin 2) ℂ) (y i) 0)))
      = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
          ((‖(V : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (2 * (t - hamWeight x))
            * ‖(V : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ (2 * hamWeight x) : ℝ) : ℂ) := by
    funext V
    exact zeroProjEntry_eq_symMoment_integrand V x y hk
  rw [hfun, integral_complex_ofReal]
  rfl

/-- For at most four tensor copies, an entry of the averaged all-zero projector is the
corresponding mixed moment when the Hamming weights agree and zero otherwise. -/
theorem haarTensorAverage_zeroProj_apply_eq {t : ℕ} (ht : t ≤ 4) (a b : Fin t → Fin 2) :
    haarTensorAverage t (zeroProj t) a b
      = if hamWeight a = hamWeight b
        then ((symMoment (t - hamWeight a) (hamWeight a) : ℝ) : ℂ)
        else 0 := by
  by_cases hk : hamWeight a = hamWeight b
  · rw [if_pos hk]
    exact haarTensorAverage_zeroProj_apply_eq_symMoment a b hk
  · rw [if_neg hk]
    exact haarTensorAverage_zeroProj_of_hamWeight_ne ht a b hk

/-- The square of `Real.sqrt 2 / 2` is one half. -/
theorem half_sqrt_two_sq : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  rw [pow_two, h2]

/-- The normalized single-qubit Hadamard matrix with entries `Real.sqrt 2 / 2` and a negative
`(1, 1)` entry. -/
def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    Complex.ofReal (Real.sqrt 2 / 2) * (if i.val + j.val = 2 then -1 else 1)

/-- Complex conjugation fixes the complex cast of a real number. -/
theorem ofReal_star (x : ℝ) : star (Complex.ofReal x) = Complex.ofReal x := by
  simp

/-- The square of the complex cast of `Real.sqrt 2 / 2` is the complex cast of one half. -/
theorem half_sqrt_two_sq_complex :
    Complex.ofReal (Real.sqrt 2 / 2) * Complex.ofReal (Real.sqrt 2 / 2)
      = Complex.ofReal (1 / 2) := by
  rw [← Complex.ofReal_mul, half_sqrt_two_sq]

/-- The sum of two copies of one half times a complex number equals that number. -/
theorem two_half_mul (x : ℂ) :
    Complex.ofReal (1 / 2) * x + Complex.ofReal (1 / 2) * x = x := by
  have h : Complex.ofReal (1 / 2) + Complex.ofReal (1 / 2) = (1 : ℂ) := by
    rw [← Complex.ofReal_add]
    norm_num
  calc Complex.ofReal (1 / 2) * x + Complex.ofReal (1 / 2) * x
      = (Complex.ofReal (1 / 2) + Complex.ofReal (1 / 2)) * x := by ring
    _ = (1 : ℂ) * x := by rw [h]
    _ = x := one_mul x

/-- Every entry in the first row of `hadamard` is the complex cast of `Real.sqrt 2 / 2`. -/
theorem hadamard_row_zero (j : Fin 2) :
    hadamard 0 j = Complex.ofReal (Real.sqrt 2 / 2) := by
  fin_cases j <;> simp [hadamard, Matrix.of_apply]

/-- The Hadamard matrix is self-adjoint. -/
theorem hadamard_star : star hadamard = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.of_apply, ofReal_star, star_neg]

/-- The Hadamard matrix squares to the identity. -/
theorem hadamard_mul_self : hadamard * hadamard = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.of_apply, Fin.sum_univ_two,
      ← Complex.ofReal_mul, half_sqrt_two_sq, mul_neg, neg_mul, neg_neg,
      add_neg_cancel, - Complex.ofReal_div] <;>
    norm_num

/-- The Hadamard matrix is unitary. -/
theorem hadamard_mem : hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', hadamard_star]
  exact hadamard_mul_self

/-- The equivalence identifying a length-two bit string with its ordered pair of entries. -/
def vecFinTwoEquiv : (Fin 2 → Fin 2) ≃ (Fin 2 × Fin 2) where
  toFun a := (a 0, a 1)
  invFun p := ![p.1, p.2]
  left_inv a := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    cases p
    simp

/-- A sum over length-two bit strings expands into the four possible bit strings. -/
theorem sum_pi_fin_two (f : (Fin 2 → Fin 2) → ℂ) :
    ∑ a : Fin 2 → Fin 2, f a = f ![0,0] + f ![0,1] + f ![1,0] + f ![1,1] := by
  have key : ∀ a : Fin 2 → Fin 2, f a = f ![a 0, a 1] :=
    fun a => congrArg f (vecFinTwoEquiv.left_inv a).symm
  have h : ∑ a : Fin 2 → Fin 2, f a = ∑ p : Fin 2 × Fin 2, f ![p.1, p.2] :=
    Fintype.sum_equiv vecFinTwoEquiv f (fun p => f ![p.1, p.2]) key
  rw [h, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  ring

/-- For a matrix equipped with a proof of unitarity, `unitaryTensorPow` equals its matrix tensor
power. -/
theorem unitaryTensorPow_mk (t : ℕ) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    unitaryTensorPow t ⟨V, hV⟩ = tensorPow t V := rfl

/-- Every entry in the all-zero row of the second tensor power of `hadamard` is one half. -/
theorem hadamardPow2_row_zero (b : Fin 2 → Fin 2) :
    tensorPow 2 hadamard ![0,0] b = Complex.ofReal (1 / 2) := by
  simp only [tensorPow_apply, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    hadamard_row_zero, ← Complex.ofReal_mul, half_sqrt_two_sq]

/-- The bit string `![0,0]` has Hamming weight zero. -/
theorem hamWeight_vec00 : hamWeight ![0,0] = 0 := by simp [hamWeight]

/-- The bit string `![0,1]` has Hamming weight one. -/
theorem hamWeight_vec01 : hamWeight ![0,1] = 1 := by simp [hamWeight]

/-- The bit string `![1,0]` has Hamming weight one. -/
theorem hamWeight_vec10 : hamWeight ![1,0] = 1 := by simp [hamWeight]

/-- The bit string `![1,1]` has Hamming weight two. -/
theorem hamWeight_vec11 : hamWeight ![1,1] = 2 := by simp [hamWeight]

/-- The all-zero diagonal entry of the two-copy averaged all-zero projector is the complex cast
of `symMoment 2 0`. -/
theorem Mtwo_00 : haarTensorAverage 2 (zeroProj 2) ![0,0] ![0,0]
    = ((symMoment 2 0 : ℝ) : ℂ) := by
  simpa [hamWeight_vec00] using
    haarTensorAverage_zeroProj_apply_eq_symMoment ![0,0] ![0,0] rfl

/-- The `![0,1]` diagonal entry of the two-copy averaged all-zero projector is the complex cast
of `symMoment 1 1`. -/
theorem Mtwo_diag11 : haarTensorAverage 2 (zeroProj 2) ![0,1] ![0,1]
    = ((symMoment 1 1 : ℝ) : ℂ) := by
  simpa [hamWeight_vec01] using
    haarTensorAverage_zeroProj_apply_eq_symMoment ![0,1] ![0,1] rfl

/-- The entry with row `![1,0]` and column `![0,1]` of the two-copy averaged all-zero projector
is the complex cast of `symMoment 1 1`. -/
theorem Mtwo_cross : haarTensorAverage 2 (zeroProj 2) ![1,0] ![0,1]
    = ((symMoment 1 1 : ℝ) : ℂ) := by
  have hk : hamWeight ![1,0] = hamWeight ![0,1] := by
    simp [hamWeight_vec10, hamWeight_vec01]
  simpa [hamWeight_vec10] using
    haarTensorAverage_zeroProj_apply_eq_symMoment ![1,0] ![0,1] hk

/-- The entry with row `![0,0]` and column `![0,1]` of the two-copy averaged all-zero projector
is zero. -/
theorem Mtwo_01 : haarTensorAverage 2 (zeroProj 2) ![0,0] ![0,1] = 0 :=
  haarTensorAverage_zeroProj_of_hamWeight_ne (by norm_num) _ _
    (by simp [hamWeight_vec00, hamWeight_vec01])

/-- The entry with row `![0,0]` and column `![1,0]` of the two-copy averaged all-zero projector
is zero. -/
theorem Mtwo_10 : haarTensorAverage 2 (zeroProj 2) ![0,0] ![1,0] = 0 :=
  haarTensorAverage_zeroProj_of_hamWeight_ne (by norm_num) _ _
    (by simp [hamWeight_vec00, hamWeight_vec10])

/-- The entry with row `![0,0]` and column `![1,1]` of the two-copy averaged all-zero projector
is zero. -/
theorem Mtwo_11 : haarTensorAverage 2 (zeroProj 2) ![0,0] ![1,1] = 0 :=
  haarTensorAverage_zeroProj_of_hamWeight_ne (by norm_num) _ _
    (by simp [hamWeight_vec00, hamWeight_vec11])

/-- The entry with row `![1,1]` and column `![0,1]` of the two-copy averaged all-zero projector
is zero. -/
theorem Mtwo_11z : haarTensorAverage 2 (zeroProj 2) ![1,1] ![0,1] = 0 :=
  haarTensorAverage_zeroProj_of_hamWeight_ne (by norm_num) _ _
    (by simp [hamWeight_vec11, hamWeight_vec01])

/-- The mixed moment `symMoment 1 1` is one half of `symMoment 2 0`. -/
theorem symMoment_two_hadamard : 2 * symMoment 1 1 = symMoment 2 0 := by
  have hcom := haarTensorAverage_commute 2
    (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) (zeroProj 2)
  have hentry := Matrix.ext_iff.symm.mp hcom ![0,0] ![0,1]
  have hH2 : ∀ a : Fin 2 → Fin 2,
      (unitaryTensorPow 2 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ)) ![0,0] a
        = Complex.ofReal (1/2) := by
    intro a
    rw [unitaryTensorPow_mk]
    exact hadamardPow2_row_zero a
  have hL : (unitaryTensorPow 2 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ)
      * haarTensorAverage 2 (zeroProj 2)) ![0,0] ![0,1]
      = ((symMoment 1 1 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, sum_pi_fin_two]
    simp only [hH2, Mtwo_01, Mtwo_diag11, Mtwo_cross, Mtwo_11z,
      mul_zero, add_zero, zero_add, two_half_mul]
  have hR : (haarTensorAverage 2 (zeroProj 2)
      * unitaryTensorPow 2 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
      ![0,0] ![0,1]
      = ((symMoment 2 0 : ℝ) : ℂ) * Complex.ofReal (1/2) := by
    have hH201 : (unitaryTensorPow 2 (⟨hadamard, hadamard_mem⟩ :
        Matrix.unitaryGroup (Fin 2) ℂ)) ![0,0] ![0,1] = Complex.ofReal (1/2) := by
      rw [unitaryTensorPow_mk]
      exact hadamardPow2_row_zero ![0,1]
    rw [Matrix.mul_apply, sum_pi_fin_two]
    simp only [Mtwo_00, hH201, Mtwo_01, Mtwo_10, Mtwo_11,
      zero_mul, add_zero]
  have hkey : ((symMoment 1 1 : ℝ) : ℂ)
      = ((symMoment 2 0 : ℝ) : ℂ) * Complex.ofReal (1/2) := by
    rw [← hL, ← hR]
    exact hentry
  rw [← Complex.ofReal_mul] at hkey
  have hreal : symMoment 1 1 = symMoment 2 0 * (1/2 : ℝ) := by
    have hr := congrArg Complex.re hkey
    rwa [Complex.ofReal_re, Complex.ofReal_re] at hr
  linarith

/-- The degree-two mixed moments are `1 / 3`, `1 / 6`, and `1 / 3` for exponent pairs `(2, 0)`,
`(1, 1)`, and `(0, 2)`. -/
theorem symMoment_two :
    symMoment 2 0 = 1 / 3 ∧ symMoment 1 1 = 1 / 6 ∧ symMoment 0 2 = 1 / 3 := by
  have hrel : 2 * symMoment 1 1 = symMoment 2 0 := symMoment_two_hadamard
  have hp : symMoment 2 0 + symMoment 1 1 = 1 / 2 := by
    have h := symMoment_succ 1 0
    rw [symMoment_one.1] at h
    simpa using h
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [symMoment_swap]
    linarith

/-- The degree-three mixed moments are `1 / 4`, `1 / 12`, `1 / 12`, and `1 / 4` in increasing
order of the second exponent. -/
theorem symMoment_three :
    symMoment 3 0 = 1 / 4 ∧ symMoment 2 1 = 1 / 12
      ∧ symMoment 1 2 = 1 / 12 ∧ symMoment 0 3 = 1 / 4 := by
  obtain ⟨h20, h11, _⟩ := symMoment_two
  have hs1 : 2 * symMoment 2 1 = symMoment 1 1 := by
    have h := symMoment_succ 1 1
    norm_num at h
    rw [← symMoment_swap 2 1] at h
    linarith
  have hs2 : symMoment 3 0 + symMoment 2 1 = symMoment 2 0 := by
    have h := symMoment_succ 2 0
    norm_num at h
    exact h
  have hsw2 : symMoment 0 3 = symMoment 3 0 := (symMoment_swap 3 0).symm
  have hsw3 : symMoment 1 2 = symMoment 2 1 := (symMoment_swap 2 1).symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The only length-four bit string of Hamming weight zero is `![0,0,0,0]`. -/
theorem weight_zero_filter :
    (Finset.univ.filter fun a : Fin 4 → Fin 2 => hamWeight a = 0) = {![0,0,0,0]} := by
  decide

/-- The length-four bit strings of Hamming weight one form the displayed four-element set. -/
theorem weight_one_filter :
    (Finset.univ.filter fun a : Fin 4 → Fin 2 => hamWeight a = 1)
      = {![0,0,0,1], ![0,0,1,0], ![0,1,0,0], ![1,0,0,0]} := by
  decide

/-- The length-four bit strings of Hamming weight two form the displayed six-element set. -/
theorem weight_two_filter :
    (Finset.univ.filter fun a : Fin 4 → Fin 2 => hamWeight a = 2)
      = {![0,0,1,1], ![0,1,0,1], ![0,1,1,0], ![1,0,0,1], ![1,0,1,0], ![1,1,0,0]} := by
  decide

/-- One half times the square of `Real.sqrt 2 / 2` is one quarter. -/
theorem half_sqrt_mul_two :
    (1 / 2 : ℝ) * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 4 := by
  rw [mul_assoc, half_sqrt_two_sq]
  norm_num

/-- Every entry in the all-zero row of the fourth tensor power of `hadamard` is one quarter. -/
theorem hadamardPow4_row_zero (b : Fin 4 → Fin 2) :
    tensorPow 4 hadamard ![0,0,0,0] b = Complex.ofReal (1 / 4) := by
  have h0 : (![0,0,0,0] : Fin 4 → Fin 2) = fun _ => 0 := by decide
  simp only [tensorPow_apply, Fin.prod_univ_four, h0, hadamard_row_zero,
    ← Complex.ofReal_mul, half_sqrt_two_sq, half_sqrt_mul_two]

/-- The bit string `![0,0,0,0]` has Hamming weight zero. -/
theorem hamWeight_vec0000 : hamWeight (![0,0,0,0] : Fin 4 → Fin 2) = 0 := by decide

/-- The bit string `![0,0,0,1]` has Hamming weight one. -/
theorem hamWeight_vec0001 : hamWeight (![0,0,0,1] : Fin 4 → Fin 2) = 1 := by decide

/-- The bit string `![0,0,1,1]` has Hamming weight two. -/
theorem hamWeight_vec0011 : hamWeight (![0,0,1,1] : Fin 4 → Fin 2) = 2 := by decide

/-- The column `![0,0,0,1]` of the four-copy averaged all-zero projector equals `symMoment 3 1`
on weight-one rows and zero on all other rows. -/
theorem Mfour_entry_w1 (a : Fin 4 → Fin 2) :
    haarTensorAverage 4 (zeroProj 4) a ![0,0,0,1]
      = if hamWeight a = 1 then ((symMoment 3 1 : ℝ) : ℂ) else 0 := by
  rw [haarTensorAverage_zeroProj_apply_eq (by norm_num) a ![0,0,0,1], hamWeight_vec0001]
  by_cases h : hamWeight a = 1
  · rw [if_pos h, h, if_pos rfl]
  · rw [if_neg h, if_neg h]

/-- The column `![0,0,1,1]` of the four-copy averaged all-zero projector equals `symMoment 2 2`
on weight-two rows and zero on all other rows. -/
theorem Mfour_entry_w2 (a : Fin 4 → Fin 2) :
    haarTensorAverage 4 (zeroProj 4) a ![0,0,1,1]
      = if hamWeight a = 2 then ((symMoment 2 2 : ℝ) : ℂ) else 0 := by
  rw [haarTensorAverage_zeroProj_apply_eq (by norm_num) a ![0,0,1,1], hamWeight_vec0011]
  by_cases h : hamWeight a = 2
  · rw [if_pos h, h, if_pos rfl]
  · rw [if_neg h, if_neg h]

/-- The all-zero row of the four-copy averaged all-zero projector equals `symMoment 4 0` on
weight-zero columns and zero otherwise. -/
theorem Mfour_entry_w0 (a : Fin 4 → Fin 2) :
    haarTensorAverage 4 (zeroProj 4) ![0,0,0,0] a
      = if hamWeight a = 0 then ((symMoment 4 0 : ℝ) : ℂ) else 0 := by
  rw [haarTensorAverage_zeroProj_apply_eq (by norm_num) ![0,0,0,0] a]
  by_cases h : hamWeight a = 0
  · rw [if_pos (by rw [hamWeight_vec0000, h]), hamWeight_vec0000, if_pos h]
  · rw [if_neg (by rw [hamWeight_vec0000]; exact fun hh => h hh.symm), if_neg h]

/-- The sum of column `![0,0,0,1]` of the four-copy averaged all-zero projector is four times
the complex cast of `symMoment 3 1`. -/
theorem sum_Mfour_col_w1 :
    ∑ a : Fin 4 → Fin 2, haarTensorAverage 4 (zeroProj 4) a ![0,0,0,1]
      = 4 * ((symMoment 3 1 : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl (fun a _ => Mfour_entry_w1 a),
    ← Finset.sum_filter (fun a : Fin 4 → Fin 2 => hamWeight a = 1), weight_one_filter]
  simp

/-- The sum of column `![0,0,1,1]` of the four-copy averaged all-zero projector is six times the
complex cast of `symMoment 2 2`. -/
theorem sum_Mfour_col_w2 :
    ∑ a : Fin 4 → Fin 2, haarTensorAverage 4 (zeroProj 4) a ![0,0,1,1]
      = 6 * ((symMoment 2 2 : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl (fun a _ => Mfour_entry_w2 a),
    ← Finset.sum_filter (fun a : Fin 4 → Fin 2 => hamWeight a = 2), weight_two_filter]
  simp

/-- Multiplying the all-zero row of the four-copy averaged all-zero projector by the fourth
Hadamard tensor power gives `symMoment 4 0` times one quarter in every column. -/
theorem sum_Mfour_row_w0 (y : Fin 4 → Fin 2) :
    ∑ a : Fin 4 → Fin 2, haarTensorAverage 4 (zeroProj 4) ![0,0,0,0] a
        * tensorPow 4 hadamard a y
      = ((symMoment 4 0 : ℝ) : ℂ) * Complex.ofReal (1 / 4) := by
  have hite : ∀ a : Fin 4 → Fin 2,
      haarTensorAverage 4 (zeroProj 4) ![0,0,0,0] a * tensorPow 4 hadamard a y
      = if hamWeight a = 0
        then ((symMoment 4 0 : ℝ) : ℂ) * tensorPow 4 hadamard a y else 0 := by
    intro a
    rw [Mfour_entry_w0 a]
    by_cases h : hamWeight a = 0
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, zero_mul, if_neg h]
  rw [Finset.sum_congr rfl (fun a _ => hite a),
    ← Finset.sum_filter (fun a : Fin 4 → Fin 2 => hamWeight a = 0), weight_zero_filter,
    Finset.sum_singleton, hadamardPow4_row_zero y]

/-- One quarter times four times a complex number equals that number. -/
theorem quarter_mul_four (x : ℂ) : Complex.ofReal (1 / 4) * (4 * x) = x := by
  have h : Complex.ofReal (1 / 4) * (4 : ℂ) = 1 := by norm_num
  rw [← mul_assoc, h, one_mul]

/-- Four times `symMoment 3 1` equals `symMoment 4 0`. -/
theorem symMoment_four_hadamard1 : 4 * symMoment 3 1 = symMoment 4 0 := by
  have hcom := haarTensorAverage_commute 4
    (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) (zeroProj 4)
  have hentry := Matrix.ext_iff.symm.mp hcom ![0,0,0,0] ![0,0,0,1]
  have hH4 : ∀ a : Fin 4 → Fin 2,
      (unitaryTensorPow 4 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
        ![0,0,0,0] a = Complex.ofReal (1 / 4) := by
    intro a
    rw [unitaryTensorPow_mk]
    exact hadamardPow4_row_zero a
  have hL : (unitaryTensorPow 4 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ)
      * haarTensorAverage 4 (zeroProj 4)) ![0,0,0,0] ![0,0,0,1]
      = ((symMoment 3 1 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [hH4]
    rw [← Finset.mul_sum, sum_Mfour_col_w1, quarter_mul_four]
  have hR : (haarTensorAverage 4 (zeroProj 4)
      * unitaryTensorPow 4 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
      ![0,0,0,0] ![0,0,0,1]
      = ((symMoment 4 0 : ℝ) : ℂ) * Complex.ofReal (1 / 4) := by
    rw [Matrix.mul_apply, unitaryTensorPow_mk]
    exact sum_Mfour_row_w0 ![0,0,0,1]
  have hkey : ((symMoment 3 1 : ℝ) : ℂ)
      = ((symMoment 4 0 : ℝ) : ℂ) * Complex.ofReal (1 / 4) := by
    rw [← hL, ← hR]
    exact hentry
  rw [← Complex.ofReal_mul] at hkey
  have hreal : symMoment 3 1 = symMoment 4 0 * (1 / 4 : ℝ) := by
    have hr := congrArg Complex.re hkey
    rwa [Complex.ofReal_re, Complex.ofReal_re] at hr
  linarith

/-- Multiplication of six times the complex cast of `symMoment 2 2` by one quarter agrees with
casting the corresponding real expression. -/
theorem sum_quarter_w2 :
    Complex.ofReal (1 / 4) * (6 * ((symMoment 2 2 : ℝ) : ℂ))
      = (((1 / 4 : ℝ) * (6 * symMoment 2 2)) : ℝ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  norm_num

/-- Six times `symMoment 2 2` equals `symMoment 4 0`. -/
theorem symMoment_four_hadamard2 : 6 * symMoment 2 2 = symMoment 4 0 := by
  have hcom := haarTensorAverage_commute 4
    (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ) (zeroProj 4)
  have hentry := Matrix.ext_iff.symm.mp hcom ![0,0,0,0] ![0,0,1,1]
  have hH4 : ∀ a : Fin 4 → Fin 2,
      (unitaryTensorPow 4 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
        ![0,0,0,0] a = Complex.ofReal (1 / 4) := by
    intro a
    rw [unitaryTensorPow_mk]
    exact hadamardPow4_row_zero a
  have hL : (unitaryTensorPow 4 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ)
      * haarTensorAverage 4 (zeroProj 4)) ![0,0,0,0] ![0,0,1,1]
      = (((1 / 4 : ℝ) * (6 * symMoment 2 2)) : ℝ) := by
    rw [Matrix.mul_apply]
    simp only [hH4]
    rw [← Finset.mul_sum, sum_Mfour_col_w2]
    exact sum_quarter_w2
  have hR : (haarTensorAverage 4 (zeroProj 4)
      * unitaryTensorPow 4 (⟨hadamard, hadamard_mem⟩ : Matrix.unitaryGroup (Fin 2) ℂ))
      ![0,0,0,0] ![0,0,1,1]
      = ((symMoment 4 0 : ℝ) : ℂ) * Complex.ofReal (1 / 4) := by
    rw [Matrix.mul_apply, unitaryTensorPow_mk]
    exact sum_Mfour_row_w0 ![0,0,1,1]
  have hkey : (((1 / 4 : ℝ) * (6 * symMoment 2 2)) : ℝ)
      = ((symMoment 4 0 : ℝ) : ℂ) * Complex.ofReal (1 / 4) := by
    rw [← hL, ← hR]
    exact hentry
  rw [← Complex.ofReal_mul] at hkey
  have hreal : (1 / 4 : ℝ) * (6 * symMoment 2 2) = symMoment 4 0 * (1 / 4 : ℝ) := by
    have hr := congrArg Complex.re hkey
    rwa [Complex.ofReal_re, Complex.ofReal_re] at hr
  linarith

/-- The degree-four mixed moments are `1 / 5`, `1 / 20`, `1 / 30`, `1 / 20`, and `1 / 5` in
increasing order of the second exponent. -/
theorem symMoment_four :
    symMoment 4 0 = 1 / 5 ∧ symMoment 3 1 = 1 / 20 ∧ symMoment 2 2 = 1 / 30
      ∧ symMoment 1 3 = 1 / 20 ∧ symMoment 0 4 = 1 / 5 := by
  have h1 : 4 * symMoment 3 1 = symMoment 4 0 := symMoment_four_hadamard1
  have h2 : 6 * symMoment 2 2 = symMoment 4 0 := symMoment_four_hadamard2
  have hp1 : symMoment 4 0 + symMoment 3 1 = symMoment 3 0 := by
    have h := symMoment_succ 3 0
    norm_num at h
    exact h
  have hp2 : symMoment 3 1 + symMoment 2 2 = symMoment 2 1 := by
    have h := symMoment_succ 2 1
    norm_num at h
    exact h
  have hm30 : symMoment 3 0 = 1 / 4 := symMoment_three.1
  have hm21 : symMoment 2 1 = 1 / 12 := symMoment_three.2.1
  have hsw1 : symMoment 1 3 = symMoment 3 1 := (symMoment_swap 3 1).symm
  have hsw2 : symMoment 0 4 = symMoment 4 0 := (symMoment_swap 4 0).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The number of position permutations taking one length-three bit string to another is the
product of the two weight factorials when their weights agree, and zero otherwise. -/
theorem perm_count_three (a b : Fin 3 → Fin 2) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => b = a ∘ σ.symm).card
      = if hamWeight a = hamWeight b
        then (hamWeight a).factorial * (3 - hamWeight a).factorial else 0 := by
  fin_cases a <;> fin_cases b <;> decide

/-- Evaluates entries of the sum of all three-position tensor permutation matrices using the
common Hamming weight. -/
theorem permSum_three_apply (a b : Fin 3 → Fin 2) :
    (∑ σ : Equiv.Perm (Fin 3), tensorPerm 3 σ) a b
      = if hamWeight a = hamWeight b
        then (((hamWeight a).factorial * (3 - hamWeight a).factorial : ℕ) : ℂ) else 0 := by
  rw [Matrix.sum_apply,
    Finset.sum_congr rfl (fun σ _ => tensorPerm_apply 3 σ a b),
    ← Finset.sum_filter (fun σ : Equiv.Perm (Fin 3) => b = a ∘ σ.symm),
    Finset.sum_const, perm_count_three a b]
  by_cases hk : hamWeight a = hamWeight b
  · rw [if_pos hk, if_pos hk]
    exact Nat.smul_one_eq_cast _
  · rw [if_neg hk, if_neg hk, zero_smul]

/-- The third tensor moment of a Haar-random single-qubit pure state is the sum of the
three-position permutation matrices divided by `4!`. See [RudolphEtAl2024]. -/
theorem haarTensorAverage_three_eq_permSum :
    haarTensorAverage 3 (zeroProj 3)
      = (((4 : ℕ).factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin 3), tensorPerm 3 σ := by
  ext a b
  rw [Matrix.smul_apply, smul_eq_mul, permSum_three_apply,
    haarTensorAverage_zeroProj_apply_eq (by norm_num)]
  by_cases hk : hamWeight a = hamWeight b
  · rw [if_pos hk, if_pos hk]
    have hle : hamWeight a ≤ 3 := by
      have h := hamWeight_le a
      omega
    interval_cases hamWeight a
    · rw [show 3 - 0 = 3 from rfl, symMoment_three.1]; norm_num
    · rw [show 3 - 1 = 2 from rfl, symMoment_three.2.1]; norm_num
    · rw [show 3 - 2 = 1 from rfl, symMoment_swap, symMoment_three.2.1]; norm_num
    · rw [show 3 - 3 = 0 from rfl, symMoment_swap, symMoment_three.1]; norm_num
  · rw [if_neg hk, if_neg hk]
    ring

/-- The number of position permutations taking one length-four bit string to another is the
product of the two weight factorials when their weights agree, and zero otherwise. -/
theorem perm_count_four (a b : Fin 4 → Fin 2) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) => b = a ∘ σ.symm).card
      = if hamWeight a = hamWeight b
        then (hamWeight a).factorial * (4 - hamWeight a).factorial else 0 := by
  fin_cases a <;> fin_cases b <;> decide

/-- Evaluates entries of the sum of all four-position tensor permutation matrices using the
common Hamming weight. -/
theorem permSum_four_apply (a b : Fin 4 → Fin 2) :
    (∑ σ : Equiv.Perm (Fin 4), tensorPerm 4 σ) a b
      = if hamWeight a = hamWeight b
        then (((hamWeight a).factorial * (4 - hamWeight a).factorial : ℕ) : ℂ) else 0 := by
  rw [Matrix.sum_apply,
    Finset.sum_congr rfl (fun σ _ => tensorPerm_apply 4 σ a b),
    ← Finset.sum_filter (fun σ : Equiv.Perm (Fin 4) => b = a ∘ σ.symm),
    Finset.sum_const, perm_count_four a b]
  by_cases hk : hamWeight a = hamWeight b
  · rw [if_pos hk, if_pos hk]
    exact Nat.smul_one_eq_cast _
  · rw [if_neg hk, if_neg hk, zero_smul]

/-- The fourth tensor moment of a Haar-random single-qubit pure state is the sum of the
four-position permutation matrices divided by `5!`. See [RudolphEtAl2024]. -/
theorem haarTensorAverage_four_eq_permSum :
    haarTensorAverage 4 (zeroProj 4)
      = (((5 : ℕ).factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin 4), tensorPerm 4 σ := by
  ext a b
  rw [Matrix.smul_apply, smul_eq_mul, permSum_four_apply,
    haarTensorAverage_zeroProj_apply_eq (by norm_num)]
  by_cases hk : hamWeight a = hamWeight b
  · rw [if_pos hk, if_pos hk]
    have hle : hamWeight a ≤ 4 := by
      have h := hamWeight_le a
      omega
    interval_cases hamWeight a
    · rw [show 4 - 0 = 4 from rfl, symMoment_four.1]; norm_num
    · rw [show 4 - 1 = 3 from rfl, symMoment_four.2.1]; norm_num
    · rw [show 4 - 2 = 2 from rfl, symMoment_four.2.2.1]; norm_num
    · rw [show 4 - 3 = 1 from rfl, symMoment_swap, symMoment_four.2.1]; norm_num
    · rw [show 4 - 4 = 0 from rfl, symMoment_swap, symMoment_four.1]; norm_num
  · rw [if_neg hk, if_neg hk]
    ring

end MeasurableInstances

end Qatlib.Papers.Trainability23.HaarAverages
