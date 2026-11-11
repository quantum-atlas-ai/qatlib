/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliPairRecords
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability

/-!
# Real Pauli estimator moments

This module extends sparse Pauli observables and their tensor measurement statistics to real
coefficients. Grouping repeated words by `realShadowCoefficient` gives a Parseval identity and a
coefficient square-sum bound in terms of the observable's operator norm.

Local compatibility weights control the grouped second moment on a specified support, yielding
`real_pauli_second_moment_bound` with factor `4^S.card`. The final lemmas relate pure-state and
density-state trace expectations to matrix norms and prove Hermiticity of the real Pauli
observable. See [HuangKuengPreskill2020] for background.

## Main statements

* `realShadowCoefficient_sq_sum_le`: grouped coefficient squares are bounded by the squared
  operator norm.
* `real_pauli_second_moment_bound`: the support-dependent real Pauli second-moment bound.
* `abs_trace_density_le_norm`: a density-state expectation norm bound.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.ShadowModels.FairBitRecords
open Qatlib.Concepts.ShadowModels.ShadowVariance
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Qatlib.Concepts.ShadowModels.ShadowChannel
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The condition that every Pauli word with a nonzero real coefficient is the identity outside
`S`. -/
def realShadowSupported {n q : ℕ} (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ) : Prop :=
  ∀ j, c j ≠ 0 → ∀ i, i ∉ S → w j i = none

/-- The real-weighted sum of tensor Pauli word operators. -/
noncomputable def realSparsePauliObservable {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ) : Operator (2^n) :=
  ∑ j, (c j : ℂ) • tensorPauliWord n (w j)

/-- The real-weighted sum of tensor Pauli estimator values for a measurement record. -/
def realSparsePauliValue {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℝ) (o : Fin n → Fin 3 × Bool) : ℝ :=
  ∑ j, c j * tensorPauliValue (w j) o

/-- The sum of coefficients of all terms whose Pauli word equals `u`. -/
def realShadowCoefficient {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℝ) (u : Fin n → Option (Fin 3)) : ℝ :=
  ∑ j, if w j=u then (c j:ℝ) else 0

/-- Summation against grouped Pauli coefficients equals summation over the original weighted
terms. -/
private theorem realShadowCoefficient_sum {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ)
    (f : (Fin n → Option (Fin 3)) → ℝ) :
    ∑ u, realShadowCoefficient w c u * f u = ∑ j, (c j:ℝ)*f (w j) := by
  simp only [realShadowCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

/-- The real trace of the real Pauli observable's square equals `2^n` times the sum of its
grouped coefficient squares. -/
private theorem realShadow_parseval {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ) :
    (Matrix.trace (realSparsePauliObservable w c * realSparsePauliObservable w c)).re =
      (2:ℝ)^n * ∑ u, (realShadowCoefficient w c u)^2 := by
  have hs : ∑ u, realShadowCoefficient w c u ^ 2 =
      ∑ j, ∑ l, if w j=w l then (c j:ℝ)*(c l:ℝ) else 0 := by
    simp_rw [pow_two]
    rw [realShadowCoefficient_sum]
    simp only [realShadowCoefficient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : w j=w l
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hs]
  have hn : ((2:ℂ)^n).re = (2:ℝ)^n := by norm_cast
  simp only [realSparsePauliObservable, Matrix.sum_mul, Matrix.mul_sum,
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

/-- The norm of a matrix entry is at most the matrix operator norm. -/
private theorem realShadow_entry_norm {N : ℕ} (A : Operator N) (i j : Fin N) :
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

/-- The sum of squared grouped real Pauli coefficients is at most the squared operator norm of
the corresponding observable. -/
theorem realShadowCoefficient_sq_sum_le {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ) :
    ∑ u, (realShadowCoefficient w c u)^2 ≤ ‖realSparsePauliObservable w c‖^2 := by
  have ht : (Matrix.trace (realSparsePauliObservable w c * realSparsePauliObservable w c)).re ≤
      (2:ℝ)^n * ‖realSparsePauliObservable w c‖^2 := by
    calc
      _ = ∑ i, ((realSparsePauliObservable w c * realSparsePauliObservable w c) i i).re := by
        simp [Matrix.trace]
      _ ≤ ∑ _ : Fin (2^n), ‖realSparsePauliObservable w c‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖(realSparsePauliObservable w c * realSparsePauliObservable w c) i i‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖realSparsePauliObservable w c * realSparsePauliObservable w c‖ :=
            realShadow_entry_norm _ i i
          _ ≤ ‖realSparsePauliObservable w c‖^2 := by
            simpa [pow_two] using!
                norm_mul_le (realSparsePauliObservable w c) (realSparsePauliObservable w c)
      _ = _ := by simp
  rw [realShadow_parseval] at ht
  have hp : (0:ℝ)<2^n := by positivity
  nlinarith [ht]

/-- The local shadow compatibility weight is symmetric in its two Pauli labels. -/
private theorem localShadowWeight_symm (a b : Option (Fin 3)) :
    localShadowWeight a b = localShadowWeight b a := by
  cases a <;> cases b <;> simp [localShadowWeight, eq_comm]

/-- Every local shadow compatibility weight is nonnegative. -/
private theorem localShadowWeight_nonneg (a b : Option (Fin 3)) :
    0 ≤ localShadowWeight a b := by
  cases a <;> cases b <;> simp [localShadowWeight]
  positivity

/-- Each row of the local shadow weight matrix sums to four. -/
private theorem localShadowWeight_sum (a : Option (Fin 3)) :
    ∑ b, localShadowWeight a b = 4 := by
  cases a <;> simp [Fintype.sum_option, localShadowWeight]
  norm_num

/-- The product of local shadow weights is `3` to the overlap count for compatible Pauli words
and zero otherwise. -/
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
      simpa only [pauliWordsCompatible, not_forall, Classical.not_imp] using! h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hu,hv,localShadowWeight,hab]

/-- The absolute sparse Pauli cross moment in a density state is bounded by the product of its
local shadow weights. -/
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

/-- Under `realShadowSupported S w c`, the grouped coefficient of any word nontrivial outside
`S` is zero. -/
private theorem realShadowCoefficient_outside {n q : ℕ} (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ)
    (hs : realShadowSupported S w c) (u : Fin n → Option (Fin 3))
    (hu : ¬ ∀ i, i ∉ S → u i=none) : realShadowCoefficient w c u = 0 := by
  unfold realShadowCoefficient
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : w j=u
  · subst u
    have hz : c j=0 := by
      by_contra hc
      exact hu (hs j hc)
    simp [hz]
  · simp [hj]

/-- The support-restricted shadow weight is symmetric in its two words. -/
private theorem localShadowSupportWeight_symm {n : ℕ} (S : Finset (Fin n))
    (u v : Fin n → Option (Fin 3)) :
    localShadowSupportWeight S u v = localShadowSupportWeight S v u := by
  simp only [localShadowSupportWeight, and_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact localShadowWeight_symm _ _

/-- Every support-restricted shadow weight is nonnegative. -/
private theorem localShadowSupportWeight_nonneg {n : ℕ} (S : Finset (Fin n))
    (u v : Fin n → Option (Fin 3)) : 0 ≤ localShadowSupportWeight S u v := by
  unfold localShadowSupportWeight
  split
  · exact Finset.prod_nonneg (fun _ _ => localShadowWeight_nonneg _ _)
  · exact le_rfl

/-- Each row sum of the support-restricted shadow weights is at most `4^S.card`. -/
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
        obtain ⟨i,hi,hvi⟩ := by simpa only [not_forall,Classical.not_imp] using! hv
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

/-- The second moment of the real sparse Pauli estimator equals the double sum of grouped
coefficient products times sparse Pauli cross moments. -/
private theorem realShadow_grouped_second {n q : ℕ} (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ) :
    (tensorPauliLaw n ρ hρ).expect (fun o => realSparsePauliValue w c o ^ 2) =
      ∑ u, ∑ v, realShadowCoefficient w c u * realShadowCoefficient w c v *
        sparsePauliMoment ρ u v := by
  have hv : ∀ o, realSparsePauliValue w c o =
      ∑ u, realShadowCoefficient w c u * tensorPauliValue u o := by
    intro o
    exact (realShadowCoefficient_sum w c (fun u => tensorPauliValue u o)).symm
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

/-- For an observable supported on `S`, the estimator second moment is at most `4^S.card` times
the sum of squared grouped coefficients. -/
theorem realShadow_second_le_coefficient {n q : ℕ} (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) (hs : realShadowSupported S w c) :
    (tensorPauliLaw n ρ hρ).expect (fun o => realSparsePauliValue w c o ^ 2) ≤
      (4:ℝ)^S.card * ∑ u, realShadowCoefficient w c u ^ 2 := by
  let a := realShadowCoefficient w c
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
      · have hz := realShadowCoefficient_outside S w c hs v hv
        simp [a,hz,K,localShadowSupportWeight,hv]
    · have hz := realShadowCoefficient_outside S w c hs u hu
      simp [a,hz,K,localShadowSupportWeight,hu]
  rw [realShadow_grouped_second ρ hρ w c]
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

/-- For a real Pauli observable supported on `S`, the estimator second moment under the tensor
Pauli law is at most `4^S.card` times the squared operator norm. -/
theorem real_pauli_second_moment_bound (n q : ℕ) (S : Finset (Fin n))
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ)
    (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) (hs : realShadowSupported S w c) :
    (tensorPauliLaw n ρ hρ).expect (fun o => realSparsePauliValue w c o ^ 2) ≤
      (4 : ℝ)^S.card * ‖realSparsePauliObservable w c‖^2 :=
  (realShadow_second_le_coefficient S w c ρ hρ hs).trans
    (mul_le_mul_of_nonneg_left (realShadowCoefficient_sq_sum_le w c) (by positivity))

/-- A nonnegative uniform bound on the absolute real expectation of a Hermitian matrix over
normalized pure states bounds its operator norm. -/
theorem hermitian_norm_le_of_pure_trace {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ v : QState I, Normalized v → |(Matrix.trace (A * outerProduct v)).re| ≤ M) :
    ‖A‖ ≤ M := by
  rw [orderedHermitian_diagonal hA]
  apply spectralDiagonal_norm_le _ _ hM
  intro i
  let v := (orderedHermitianBasis hA i).ofLp
  have hv : A *ᵥ v = (orderedHermitianValues hA i : ℂ) • v :=
    congrArg (fun x : EuclideanSpace ℂ I => x.ofLp) (orderedHermitianBasis_action hA i)
  have hn : Normalized v := by
    show ∑ j, ‖v j‖^2 = 1
    have he : ‖orderedHermitianBasis hA i‖^2 = ∑ j, ‖v j‖^2 := EuclideanSpace.norm_sq_eq _
    rw [← he, OrthonormalBasis.norm_eq_one, one_pow]
  have ht : Matrix.trace (A * outerProduct v) = (orderedHermitianValues hA i : ℂ) := by
    have he (j : I) : ∑ k, A j k * (v k * star (v j)) =
        (orderedHermitianValues hA i : ℂ) * (star (v j) * v j) := by
      calc
        _ = star (v j) * (A *ᵥ v) j := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [hv]; simp only [Pi.smul_apply, smul_eq_mul]; ring
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct_apply]
    change (∑ x, ∑ y, A x y * (v y * star (v x))) = _
    simp_rw [he]
    rw [← Finset.mul_sum]
    have hs : (∑ j, star (v j) * v j) = (1 : ℂ) := by
      simpa only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply] using!
          (normalized_iff_inner_self v).mp hn
    rw [hs, mul_one]
  simpa only [Complex.norm_real, Real.norm_eq_abs, ht, Complex.ofReal_re] using! h v hn

/-- The absolute real trace expectation of any matrix against a positive semidefinite trace-one
matrix is at most its operator norm. -/
theorem abs_trace_density_le_norm {I : Type} [Fintype I] [DecidableEq I]
    (A ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ = 1) :
    |(Matrix.trace (A * ρ)).re| ≤ ‖A‖ := by
  have htn : Matrix.traceNorm ρ = 1 := by
    simpa only [ht, Complex.one_re] using!
        congrArg Complex.re (Matrix.PosSemidef.traceNorm_eq_trace hρ)
  calc
    _ ≤ ‖Matrix.trace (A * ρ)‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (A * ρ) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖A‖ * Matrix.traceNorm ρ := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = _ := by rw [htn, mul_one]

/-- A real linear combination of tensor Pauli word operators is Hermitian. -/
theorem realSparsePauliObservable_hermitian {n q : ℕ}
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℝ) :
    (realSparsePauliObservable w c).IsHermitian := by
  change (realSparsePauliObservable w c)ᴴ = _
  simp only [realSparsePauliObservable, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    (pauli_pair_word_hermitian _ _).eq]
  simp

end Qatlib.Concepts.ShadowModels.ShadowChannel
