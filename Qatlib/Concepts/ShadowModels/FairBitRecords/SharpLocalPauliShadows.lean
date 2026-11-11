/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.FairBitRecords.SparsePauliEnergyConsumers
import Qatlib.Concepts.ShadowModels.SampleBudget.RationalLinearSelection
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Support bounds and counted estimators for local Pauli shadows

Defines rational sparse-Pauli sample, mean, and median computations with explicit operation
counters. `local_pauli_native_means_median_and_work` identifies the computed median with the
real block-mean median and bounds the recorded work.

Pauli trace orthogonality and a support-restricted pair-weight kernel yield
`local_pauli_shadow_sharp_support_moments`: unbiasedness and second-moment bounds with factor `4
^ S.card` times the squared observable norm. For the local Pauli measurement framework, see
[HuangKuengPreskill2020].

## Main statements

* `local_pauli_native_means_median_and_work`: The counted median's real value is the sorted
  median of the `2 * r + 1` block means, its evaluation count is `(2 * r + 1) * m * q * (n +
  1)`, and its selection-work count is at most `10000 * (2 * r + 1)`.
* `localShadowPauli_trace_orthogonal`: The trace of the product of two `n`-qubit Pauli words is
  `2 ^ n` when the words agree and zero otherwise.
* `local_pauli_shadow_sharp_support_moments`: For a sparse Pauli observable supported in `S`,
  the local Pauli sample is unbiased for its expectation in the density operator, and both its
  second moment and centered second moment are at most `4 ^ S.card * ‖O‖ ^ 2`.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.SampleBudget
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.FairBitRecords
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The predicate that every Pauli word with nonzero coefficient is the identity at each
coordinate outside `S`. -/
def localShadowSupported {n q : ℕ} (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ) : Prop :=
  ∀ j, c j ≠ 0 → ∀ i, i ∉ S → w j i = none

/-- The rational local Pauli shadow value `sparseLocalRat a o` for a word factor `a` and
measurement record `o`. -/
def localPauliValueQ (a : Option (Fin 3)) (o : Fin 3 × Bool) : ℚ :=
  sparseLocalRat a o

/-- Evaluates a rational sparse-Pauli sample by multiplying local factors, weighting by
coefficients, and summing, while recording `q * (n + 1)` counted operations. -/
def localSparseSampleCounted {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (o : Fin n → Fin 3 × Bool) : ℚ × ℕ :=
  (List.ofFn (fun j : Fin q =>
    let p := (List.ofFn (fun i : Fin n => localPauliValueQ (w j i) (o i))).foldl
      (fun (z : ℚ × ℕ) x => (z.1*x,z.2+1)) (1,0)
    (c j*p.1,p.2+1))).foldl (fun z x => (z.1+x.1,z.2+x.2)) (0,0)

/-- The rational mean of the supplied counted sparse-Pauli samples, paired with the sum of their
operation counters. -/
def localSparseMeanCounted {n q m : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (ω : Fin m → Fin n → Fin 3 × Bool) : ℚ × ℕ :=
  let z := (List.ofFn ω).foldl (fun z o =>
    let v := localSparseSampleCounted w c o
    (z.1+v.1,z.2+v.2)) (0,0)
  (z.1/m,z.2)

/-- Computes the rational block means and selects their median with `qSelect`, returning the
median, total sample-evaluation count, and selection-work count. -/
def localSparseMedianCounted {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (m r : ℕ) (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) :
    ℚ × ℕ × ℕ :=
  let groups := (List.ofFn ω).map (localSparseMeanCounted w c)
  let z := qSelect (groups.map Prod.fst) r
  (z.1,(groups.map Prod.snd).sum,z.2)

/-- The counted product fold returns the initial scalar times the list product and increases the
counter by the list length. -/
private theorem local_counted_product (xs : List ℚ) (r : ℚ) (k : ℕ) :
    xs.foldl (fun (z : ℚ × ℕ) x => (z.1*x,z.2+1)) (r,k) =
      (r*xs.prod,k+xs.length) := by
  induction xs generalizing r k with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The counted sum fold adds the sum of first components to the initial scalar and the sum of
second components to the initial counter. -/
private theorem local_counted_sum (xs : List (ℚ × ℕ)) (r : ℚ) (k : ℕ) :
    xs.foldl (fun z x => (z.1+x.1,z.2+x.2)) (r,k) =
      (r+(xs.map Prod.fst).sum,k+(xs.map Prod.snd).sum) := by
  induction xs generalizing r k with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

/-- The counted sample equals the rational sum of coefficient-weighted local-factor products,
paired with the exact count `q * (n + 1)`. -/
theorem localSparseSampleCounted_spec {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ)
    (o : Fin n → Fin 3 × Bool) :
    localSparseSampleCounted w c o =
      (∑ j, c j * ∏ i, sparseLocalRat (w j i) (o i), q*(n+1)) := by
  unfold localSparseSampleCounted
  simp_rw [local_counted_product]
  rw [local_counted_sum]
  simp [localPauliValueQ, List.map_ofFn, Function.comp_def, Fin.sum_ofFn, Fin.prod_ofFn]

/-- Casting the rational local Pauli value to the reals gives `tensorPauliLocalValue`. -/
theorem localPauliValueQ_cast (a : Option (Fin 3)) (o : Fin 3 × Bool) :
    (localPauliValueQ a o : ℝ) = tensorPauliLocalValue a o := by
  cases a with
  | none => norm_num [localPauliValueQ, sparseLocalRat, tensorPauliLocalValue]
  | some a =>
    rcases o with ⟨b,s⟩
    by_cases h : b=a <;> cases s <;>
      norm_num [localPauliValueQ, sparseLocalRat, tensorPauliLocalValue,h]

/-- The real value of the counted mean is the average of `sparsePauliValue` over the records,
and its operation count is `m * q * (n + 1)`. -/
theorem localSparseMeanCounted_spec {n q m : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ)
    (ω : Fin m → Fin n → Fin 3 × Bool) :
    ((localSparseMeanCounted w c ω).1 : ℝ) =
      (m:ℝ)⁻¹ * ∑ i, sparsePauliValue w c (ω i) ∧
    (localSparseMeanCounted w c ω).2 = m*q*(n+1) := by
  have he : localSparseMeanCounted w c ω =
      ((∑ i, ∑ j, c j * ∏ l, sparseLocalRat (w j l) (ω i l)) / m,
        m*(q*(n+1))) := by
    unfold localSparseMeanCounted
    rw [show (List.ofFn ω).foldl (fun z o =>
        let v := localSparseSampleCounted w c o
        (z.1+v.1,z.2+v.2)) (0,0) =
        ((List.ofFn ω).map (localSparseSampleCounted w c)).foldl
          (fun z x => (z.1+x.1,z.2+x.2)) (0,0) by
      rw [List.foldl_map]]
    rw [local_counted_sum]
    simp [List.map_ofFn, Function.comp_def, localSparseSampleCounted_spec, Fin.sum_ofFn]
  rw [he]
  refine ⟨?_, by simp [mul_assoc]⟩
  simp only [Rat.cast_div, Rat.cast_sum, Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast,
    sparsePauliValue, tensorPauliValue]
  simp_rw [← localPauliValueQ_cast, localPauliValueQ]
  rw [div_eq_mul_inv, mul_comm]

/-- The counted median's real value is the sorted median of the `2 * r + 1` block means, its
evaluation count is `(2 * r + 1) * m * q * (n + 1)`, and its selection-work count is at most
`10000 * (2 * r + 1)`. See [HuangKuengPreskill2020]. -/
theorem local_pauli_native_means_median_and_work
    (n q m r : ℕ) (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ)
    (ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool) :
    ((localSparseMedianCounted w c m r ω).1 : ℝ) =
      sortedBlockMedian r (fun j => (m:ℝ)⁻¹ * ∑ i, sparsePauliValue w c (ω j i)) ∧
    (localSparseMedianCounted w c m r ω).2.1 = (2*r+1)*m*q*(n+1) ∧
    (localSparseMedianCounted w c m r ω).2.2 ≤ 10000*(2*r+1) := by
  have hs := rational_selection_median_exact_real_sorted_semantics r
    (fun j => (localSparseMeanCounted w c (ω j)).1)
  have hm : ∀ j, ((localSparseMeanCounted w c (ω j)).1 : ℝ) =
      (m:ℝ)⁻¹ * ∑ i, sparsePauliValue w c (ω j i) :=
    fun j => (localSparseMeanCounted_spec w c (ω j)).1
  have hc : ∀ j, (localSparseMeanCounted w c (ω j)).2 = m*q*(n+1) :=
    fun j => (localSparseMeanCounted_spec w c (ω j)).2
  simp only [localSparseMedianCounted, List.map_ofFn, Function.comp_def]
  refine ⟨?_, ?_, hs.2⟩
  · simpa only [hm] using hs.1
  · simp [hc, mul_assoc]
    ring

/-- The trace of the product of two single-qubit Pauli word factors is two when their optional
axis labels agree and zero otherwise. -/
private theorem local_word_trace (a b : Option (Fin 3)) :
    Matrix.trace (tensorPauliWordFactor a * tensorPauliWordFactor b) =
      if a=b then (2:ℂ) else 0 := by
  cases a with
  | none => cases b with
    | none => norm_num [tensorPauliWordFactor, Matrix.trace_one]
    | some b => fin_cases b <;>
        norm_num [tensorPauliWordFactor, Matrix.trace, Fin.sum_univ_two,
          pauliMatrix, pauliX, pauliY, pauliZ, Matrix.one_mul] <;> decide
  | some a => cases b with
    | none => fin_cases a <;>
        norm_num [tensorPauliWordFactor, Matrix.trace, Fin.sum_univ_two,
          pauliMatrix, pauliX, pauliY, pauliZ, Matrix.mul_one] <;> decide
    | some b => fin_cases a <;> fin_cases b <;>
        norm_num [tensorPauliWordFactor, Matrix.trace, Matrix.mul_apply,
          Fin.sum_univ_two, pauliMatrix, pauliX, pauliY, pauliZ]

/-- The trace of the product of two `n`-qubit Pauli words is `2 ^ n` when the words agree and
zero otherwise. -/
theorem localShadowPauli_trace_orthogonal {n : ℕ}
    (u v : Fin n → Option (Fin 3)) :
    Matrix.trace (tensorPauliWord n u * tensorPauliWord n v) =
      if u=v then (2:ℂ)^n else 0 := by
  rw [tensorPauliWord, tensorPauliWord, tensorPauliProduct_mul, tensorPauliProduct_trace]
  simp_rw [local_word_trace]
  by_cases h : u=v
  · subst v
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The real coefficient of the Pauli word `u` after summing all rational coefficients whose
indexed word equals `u`. -/
def localShadowCoefficient {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (u : Fin n → Option (Fin 3)) : ℝ :=
  ∑ j, if w j=u then (c j:ℝ) else 0

/-- A weighted sum over grouped Pauli-word coefficients equals the original indexed
coefficient-weighted sum. -/
private theorem localShadowCoefficient_sum {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ)
    (f : (Fin n → Option (Fin 3)) → ℝ) :
    ∑ u, localShadowCoefficient w c u * f u = ∑ j, (c j:ℝ)*f (w j) := by
  simp only [localShadowCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

/-- The real trace of the square of a sparse Pauli observable equals `2 ^ n` times the sum of
its squared grouped Pauli coefficients. -/
private theorem localShadow_parseval {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ) :
    (Matrix.trace (sparsePauliObservable w c * sparsePauliObservable w c)).re =
      (2:ℝ)^n * ∑ u, (localShadowCoefficient w c u)^2 := by
  have hs : ∑ u, localShadowCoefficient w c u ^ 2 =
      ∑ j, ∑ l, if w j=w l then (c j:ℝ)*(c l:ℝ) else 0 := by
    simp_rw [pow_two]
    rw [localShadowCoefficient_sum]
    simp only [localShadowCoefficient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : w j=w l
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hs]
  have hn : ((2:ℂ)^n).re = (2:ℝ)^n := by norm_cast
  simp only [sparsePauliObservable, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, localShadowPauli_trace_orthogonal, Complex.re_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : w j=w l
  · simp [h, Complex.mul_re, Complex.mul_im, hn]
    ring
  · simp [h, Ne.symm h]

/-- The norm of each matrix entry is at most the norm of the operator. -/
private theorem localShadow_entry_norm {N : ℕ} (A : Operator N) (i j : Fin N) :
    ‖A i j‖ ≤ ‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 := by
    have hs : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖^2 = 1 := by
      rw [norm_toEuclidean_sq_eq_re_inner,
        (normalized_iff_inner_self _).mp (normalized_ket j)]
      rfl
    nlinarith [norm_nonneg (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j))]
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk,mul_one] at hn
  have hi := PiLp.norm_apply_le (toEuclidean_fromVec (A*ᵥKet j)) i
  have he : (A*ᵥKet j) i = A i j := by
    simp [Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite]
  change ‖(A*ᵥKet j) i‖ ≤ ‖toEuclidean_fromVec (A*ᵥKet j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- The sum of squared grouped Pauli coefficients is at most `‖sparsePauliObservable w c‖ ^ 2`. -/
theorem localShadowCoefficient_sq_sum_le {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ) :
    ∑ u, (localShadowCoefficient w c u)^2 ≤ ‖sparsePauliObservable w c‖^2 := by
  have ht : (Matrix.trace (sparsePauliObservable w c * sparsePauliObservable w c)).re ≤
      (2:ℝ)^n * ‖sparsePauliObservable w c‖^2 := by
    calc
      _ = ∑ i, ((sparsePauliObservable w c * sparsePauliObservable w c) i i).re := by
        simp [Matrix.trace]
      _ ≤ ∑ _ : Fin (2^n), ‖sparsePauliObservable w c‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖(sparsePauliObservable w c * sparsePauliObservable w c) i i‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖sparsePauliObservable w c * sparsePauliObservable w c‖ :=
            localShadow_entry_norm _ i i
          _ ≤ ‖sparsePauliObservable w c‖^2 := by
            simpa [pow_two] using
                norm_mul_le (sparsePauliObservable w c) (sparsePauliObservable w c)
      _ = _ := by simp
  rw [localShadow_parseval] at ht
  have hp : (0:ℝ)<2^n := by positivity
  nlinarith [ht]

/-- The local pair weight, equal to one when either label is the identity, three for equal
nonidentity axes, and zero for distinct nonidentity axes. -/
def localShadowWeight : Option (Fin 3) → Option (Fin 3) → ℝ
  | none, _ => 1
  | some _, none => 1
  | some a, some b => if a=b then 3 else 0

/-- The local Pauli pair weight is symmetric in its two labels. -/
private theorem localShadowWeight_symm (a b : Option (Fin 3)) :
    localShadowWeight a b = localShadowWeight b a := by
  cases a <;> cases b <;> simp [localShadowWeight, eq_comm]

/-- Every local Pauli pair weight is nonnegative. -/
private theorem localShadowWeight_nonneg (a b : Option (Fin 3)) :
    0 ≤ localShadowWeight a b := by
  cases a <;> cases b <;> simp [localShadowWeight]
  positivity

/-- For any fixed optional axis label, the local pair weights summed over the second label equal
four. -/
private theorem localShadowWeight_sum (a : Option (Fin 3)) :
    ∑ b, localShadowWeight a b = 4 := by
  cases a <;> simp [Fintype.sum_option, localShadowWeight]
  norm_num

/-- The product of local pair weights equals `3 ^ pauliWordOverlap u v` for compatible words and
zero for incompatible words. -/
private theorem localShadowWeight_prod {n : ℕ} (u v : Fin n → Option (Fin 3)) :
    ∏ i, localShadowWeight (u i) (v i) =
      if pauliWordsCompatible u v then (3:ℝ)^pauliWordOverlap u v else 0 := by
  by_cases h : pauliWordsCompatible u v
  · rw [if_pos h, pauliWordOverlap, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i _
    cases hu : u i <;> cases hv : v i <;> simp [localShadowWeight]
    rename_i a b
    have hab := h i a b hu hv
    simp [hab]
  · rw [if_neg h]
    obtain ⟨i,a,b,hu,hv,hab⟩ := by
      simpa only [pauliWordsCompatible, not_forall, Classical.not_imp] using h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hu,hv,localShadowWeight,hab]

/-- For a density operator, the absolute sparse-Pauli pair moment is at most the product of the
local pair weights. -/
private theorem localShadowMoment_bound {n : ℕ} (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (u v : Fin n → Option (Fin 3)) :
    |sparsePauliMoment ρ u v| ≤ ∏ i, localShadowWeight (u i) (v i) := by
  rw [localShadowWeight_prod]
  by_cases h : pauliWordsCompatible u v
  · simp only [sparsePauliMoment, if_pos h, abs_mul,
      abs_of_nonneg (show 0 ≤ (3:ℝ)^pauliWordOverlap u v by positivity)]
    exact mul_le_of_le_one_right (by positivity)
      (sparsePauliWord_expectation_abs_le_one n ρ hρ _)
  · simp [sparsePauliMoment,h]

/-- If every nonzero indexed word is supported in `S`, the grouped coefficient of a word that is
nonidentity outside `S` is zero. -/
private theorem localShadowCoefficient_outside {n q : ℕ} (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ)
    (hs : localShadowSupported S w c) (u : Fin n → Option (Fin 3))
    (hu : ¬ ∀ i, i ∉ S → u i=none) : localShadowCoefficient w c u = 0 := by
  unfold localShadowCoefficient
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : w j=u
  · subst u
    have hz : c j=0 := by
      by_contra hc
      exact hu (hs j hc)
    simp [hz]
  · simp [hj]

/-- The product of the local pair weights when both words are identity outside `S`, and zero
otherwise. -/
noncomputable def localShadowSupportWeight {n : ℕ} (S : Finset (Fin n))
    (u v : Fin n → Option (Fin 3)) : ℝ :=
  if (∀ i, i ∉ S → u i=none) ∧ (∀ i, i ∉ S → v i=none) then
    ∏ i, localShadowWeight (u i) (v i) else 0

/-- The support-restricted Pauli pair weight is symmetric in its two words. -/
private theorem localShadowSupportWeight_symm {n : ℕ} (S : Finset (Fin n))
    (u v : Fin n → Option (Fin 3)) :
    localShadowSupportWeight S u v = localShadowSupportWeight S v u := by
  simp only [localShadowSupportWeight, and_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact localShadowWeight_symm _ _

/-- Every support-restricted Pauli pair weight is nonnegative. -/
private theorem localShadowSupportWeight_nonneg {n : ℕ} (S : Finset (Fin n))
    (u v : Fin n → Option (Fin 3)) : 0 ≤ localShadowSupportWeight S u v := by
  unfold localShadowSupportWeight
  split
  · exact Finset.prod_nonneg (fun _ _ => localShadowWeight_nonneg _ _)
  · exact le_rfl

/-- The sum of a row of the support-restricted pair-weight kernel is at most `4 ^ S.card`. -/
private theorem localShadowSupportWeight_row {n : ℕ} (S : Finset (Fin n))
    (u : Fin n → Option (Fin 3)) : ∑ v, localShadowSupportWeight S u v ≤ (4:ℝ)^S.card := by
  by_cases hu : ∀ i, i ∉ S → u i=none
  · have he : ∀ v, localShadowSupportWeight S u v =
        ∏ i, (if i ∈ S ∨ v i=none then localShadowWeight (u i) (v i) else 0) := by
      intro v
      by_cases hv : ∀ i, i ∉ S → v i=none
      · rw [localShadowSupportWeight, if_pos (And.intro hu hv)]
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · simp [hi]
        · simp [hv i hi]
      · rw [localShadowSupportWeight, if_neg (fun h => hv h.2)]
        obtain ⟨i,hi,hvi⟩ := by simpa only [not_forall,Classical.not_imp] using hv
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi,hvi]
    simp_rw [he]
    rw [← Fintype.prod_sum (fun (i : Fin n) (b : Option (Fin 3)) =>
      if i ∈ S ∨ b=none then localShadowWeight (u i) b else 0)]
    have hl : ∀ i : Fin n,
        (∑ b : Option (Fin 3), if i ∈ S ∨ b=none then localShadowWeight (u i) b else 0) =
        if i ∈ S then 4 else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [hi,true_or,if_true]
        exact localShadowWeight_sum (u i)
      · simp [hi,localShadowWeight,hu i hi]
    simp_rw [hl]
    simp
  · simp [localShadowSupportWeight,hu]

/-- The second moment of the sparse-Pauli sample equals the double sum of grouped coefficient
products weighted by the sparse-Pauli pair moments. -/
private theorem localShadow_grouped_second {n q : ℕ} (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ) :
    (tensorPauliLaw n ρ hρ).expect (fun o => sparsePauliValue w c o ^ 2) =
      ∑ u, ∑ v, localShadowCoefficient w c u * localShadowCoefficient w c v *
        sparsePauliMoment ρ u v := by
  have hv : ∀ o, sparsePauliValue w c o =
      ∑ u, localShadowCoefficient w c u * tensorPauliValue u o := by
    intro o
    exact (localShadowCoefficient_sum w c (fun u => tensorPauliValue u o)).symm
  simp only [FinDist.expect, hv, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← tensor_pauli_actual_cross_moment n ρ hρ u v]
  simp only [FinDist.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

/-- For a density operator and words supported in `S` whenever their coefficients are nonzero,
the sample's second moment is at most `4 ^ S.card` times the sum of squared grouped
coefficients. -/
theorem localShadow_second_le_coefficient {n q : ℕ} (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) (hs : localShadowSupported S w c) :
    (tensorPauliLaw n ρ hρ).expect (fun o => sparsePauliValue w c o ^ 2) ≤
      (4:ℝ)^S.card * ∑ u, localShadowCoefficient w c u ^ 2 := by
  let a := localShadowCoefficient w c
  let K := localShadowSupportWeight S
  have hterm : ∀ u v, a u*a v*sparsePauliMoment ρ u v ≤
      ((a u)^2+(a v)^2)/2 * K u v := by
    intro u v
    by_cases hu : ∀ i, i ∉ S → u i=none
    · by_cases hv : ∀ i, i ∉ S → v i=none
      · have ha : |a u*a v| ≤ ((a u)^2+(a v)^2)/2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|a u|-|a v|),sq_abs (a u),sq_abs (a v)]
        calc
          _ ≤ |a u*a v*sparsePauliMoment ρ u v| := le_abs_self _
          _ = |a u*a v| *|sparsePauliMoment ρ u v| := abs_mul _ _
          _ ≤ |a u*a v| *(∏ i, localShadowWeight (u i) (v i)) :=
            mul_le_mul_of_nonneg_left (localShadowMoment_bound ρ hρ u v) (abs_nonneg _)
          _ ≤ _ := by
            dsimp [K]
            rw [localShadowSupportWeight,if_pos (And.intro hu hv)]
            exact mul_le_mul_of_nonneg_right ha
              (Finset.prod_nonneg (fun _ _ => localShadowWeight_nonneg _ _))
      · have hz := localShadowCoefficient_outside S w c hs v hv
        simp [a,hz,K,localShadowSupportWeight,hv]
    · have hz := localShadowCoefficient_outside S w c hs u hu
      simp [a,hz,K,localShadowSupportWeight,hu]
  rw [localShadow_grouped_second ρ hρ w c]
  calc
    _ ≤ ∑ u, ∑ v, ((a u)^2+(a v)^2)/2*K u v :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hterm u v))
    _ = ∑ u, (a u)^2 * ∑ v, K u v := by
      have he : (∑ u, ∑ v, (a v)^2*K u v) = ∑ u, ∑ v, (a u)^2*K u v := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        rw [show K v u=K u v from localShadowSupportWeight_symm S v u]
      simp only [add_div,add_mul,div_mul_eq_mul_div,Finset.sum_add_distrib]
      simp_rw [← Finset.sum_div]
      rw [he]
      simp_rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ u, (a u)^2 * (4:ℝ)^S.card :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left
        (localShadowSupportWeight_row S u) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- For a sparse Pauli observable supported in `S`, the local Pauli sample is unbiased for its
expectation in the density operator, and both its second moment and centered second moment
are at most `4 ^ S.card * ‖O‖ ^ 2`. See [HuangKuengPreskill2020]. -/
theorem local_pauli_shadow_sharp_support_moments
    (n q : ℕ) (S : Finset (Fin n)) (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (hs : localShadowSupported S w c) :
    let O := sparsePauliObservable w c
    let mu := (Matrix.trace (O*ρ)).re
    (tensorPauliLaw n ρ hρ).expect (sparsePauliValue w c) = mu ∧
    (tensorPauliLaw n ρ hρ).expect (fun o => (sparsePauliValue w c o)^2) ≤
      (4:ℝ)^S.card * ‖O‖^2 ∧
    (tensorPauliLaw n ρ hρ).expect (fun o => (sparsePauliValue w c o-mu)^2) ≤
      (4:ℝ)^S.card * ‖O‖^2 := by
  (try dsimp only)
  have hm := (sparse_pauli_exact_energy_variance_and_bound n q ρ hρ w c).1
  have hs' := (localShadow_second_le_coefficient S w c ρ hρ hs).trans
    (mul_le_mul_of_nonneg_left (localShadowCoefficient_sq_sum_le w c) (by positivity))
  refine ⟨hm,hs',?_⟩
  rw [← hm]
  change (tensorPauliLaw n ρ hρ).variance (sparsePauliValue w c) ≤ _
  rw [FinDist.variance_eq_expect_sq_sub,hm]
  exact (sub_le_self _ (sq_nonneg _)).trans hs'

end Qatlib.Concepts.ShadowModels.FairBitRecords
