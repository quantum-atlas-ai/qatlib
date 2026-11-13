/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.QuadraticObservableShadows
import Qatlib.Concepts.ShadowModels.FairBitRecords.SharpLocalPauliShadows

/-!
# Pauli pair observables and record budgets

This module represents rational linear combinations of pairs of Pauli words by
`pauliPairObservable`. It derives their symmetrized shadow kernels, trace formulas, coefficient
bounds, and grouped-record budgets for quadratic classical-shadow estimation
[HuangKuengPreskill2020].

## Main statements

* `pauli_pair_kernel_and_estimand`: kernel, trace, Hermiticity, and symmetrization identities.
* `pauli_pair_coefficient_mass_le`: coefficient mass bounded by the squared observable norm.
* `quadratic_same_records_source_budget`: simultaneous concentration from shared records.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.FairBitRecords
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.ShadowVariance

open Matrix
open scoped Classical BigOperators

/-- A pair of tensor Pauli words on `n` qubits. -/
def pauliPairWord (n : ℕ) := (Fin n → Option (Fin 3)) × (Fin n → Option (Fin 3))

/-- Every term with nonzero coefficient has its first and second Pauli words supported in `S₁`
and `S₂`, respectively. -/
def pauliPairSupported {n q : ℕ} (S₁ S₂ : Finset (Fin n))
    (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ) : Prop :=
  ∀ j, c j ≠ 0 →
    (∀ i, i ∉ S₁ → (ww j).1 i = none) ∧ (∀ i, i ∉ S₂ → (ww j).2 i = none)

/-- The rationally weighted sum of tensor products of the two Pauli words in each term. -/
noncomputable def pauliPairObservable (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ :=
  ∑ j, (c j : ℂ) • TensorGate (tensorPauliWord n (ww j).1) (tensorPauliWord n (ww j).2)

open scoped Matrix.Norms.L2Operator Kronecker

/-- The conditional variance and kernel variance of a finite pair kernel are both nonnegative. -/
theorem pauli_pair_variances_nonneg {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) :
    0 ≤ pairConditionalVariance p h ∧ 0 ≤ pairKernelVariance p h := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => mul_nonneg (p.nonneg _) (sq_nonneg _)
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (mul_nonneg (p.nonneg _) (p.nonneg _)) (sq_nonneg _)

/-- The stated sample-size budget bounds `4 * C / m + 4 * K / m ^ 2` by `ε ^ 2 / 34` when `m ≥
2` and `0 < ε ≤ 1`. -/
private theorem pauli_pair_budget_arithmetic (m C K ε : ℝ)
    (hm : 2 ≤ m) (_hC : 0 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hb : 140 * max C (Real.sqrt K) / ε^2 ≤ m) :
    4 / m * C + 4 / m^2 * K ≤ ε^2 / 34 := by
  have hm0 : 0 < m := by linarith
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hv := (div_le_iff₀ he2).1 hb
  have hc : 140 * C ≤ m * ε^2 :=
    (mul_le_mul_of_nonneg_left (le_max_left C (Real.sqrt K)) (by norm_num)).trans hv
  have hs : 140 * Real.sqrt K ≤ m * ε^2 :=
    (mul_le_mul_of_nonneg_left (le_max_right C (Real.sqrt K)) (by norm_num)).trans hv
  have hc' : C / m ≤ ε^2 / 140 := by
    apply (div_le_iff₀ hm0).2
    linarith
  have hs' : Real.sqrt K / m ≤ ε^2 / 140 := by
    apply (div_le_iff₀ hm0).2
    linarith
  have hk' : K / m^2 ≤ (ε^2 / 140)^2 := by
    have hh := mul_self_le_mul_self (div_nonneg (Real.sqrt_nonneg K) (le_of_lt hm0)) hs'
    simpa only [← pow_two, div_pow, Real.sq_sqrt hK] using! hh
  have he1 : ε^2 ≤ 1 := by nlinarith
  have he4 : (ε^2)^2 ≤ ε^2 := by nlinarith [sq_nonneg ε]
  calc
    _ = 4 * (C / m) + 4 * (K / m^2) := by ring
    _ ≤ 4 * (ε^2 / 140) + 4 * (ε^2 / 140)^2 := by gcongr
    _ ≤ ε^2 / 34 := by nlinarith

/-- The stated variance-based sample budget bounds the mean squared error of the quadratic
shadow U-statistic by `ε ^ 2 / 34`. See [HuangKuengPreskill2020]. -/
theorem quadratic_group_variance_source_budget
    (n m : ℕ) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (O : Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (hO : O.IsHermitian) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 2 ≤ m)
    (hb : (m : ℝ) ≥ 140 * max
      (pairConditionalVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n O))
      (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n O))) /
        ε^2) :
    (∑ ω : Fin m → Fin n → Fin 3 × Bool,
      (tensorPauliLaw n ρ hρ).probOf ω *
        (quadraticShadowU n m O ω - (Matrix.trace (O * TensorGate ρ ρ)).re)^2) ≤ ε^2/34 := by
  let p := tensorPauliLaw n ρ hρ
  let h := quadraticShadowKernel n O
  obtain ⟨hC, hK⟩ := pauli_pair_variances_nonneg p h
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc1 : ((m-1 : ℕ) : ℝ) = (m : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  have hc2 : ((m-2 : ℕ) : ℝ) = (m : ℝ)-2 := by
    rw [Nat.cast_sub hm]; norm_num
  have hd : 0 < (m : ℝ)*(m-1 : ℕ) := by
    rw [hc1]
    exact mul_pos hm0 (by linarith)
  have ha : (4*(m-2 : ℕ) : ℝ)/((m : ℝ)*(m-1 : ℕ)) ≤ 4/(m : ℝ) := by
    apply (div_le_div_iff₀ hd hm0).2
    rw [hc1, hc2]
    nlinarith
  have hb' : (2 : ℝ)/((m : ℝ)*(m-1 : ℕ)) ≤ 4/(m : ℝ)^2 := by
    apply (div_le_div_iff₀ hd (sq_pos_of_pos hm0)).2
    rw [hc1]
    nlinarith
  rw [quadratic_shadow_exact_covariance_from_same_records n m ρ hρ O hm hO]
  exact (add_le_add (mul_le_mul_of_nonneg_right ha hC)
    (mul_le_mul_of_nonneg_right hb' hK)).trans
      (pauli_pair_budget_arithmetic m _ _ ε hm2 hC hK hε hε1 hb)

/-- For the specified group size and odd number of groups, fresh-record resources have the
displayed exact counts, each counted median uses the stated number of groups and comparison
bound, and pair evaluations total the number of groups times `m.choose 2`. See
[HuangKuengPreskill2020]. -/
theorem pauli_pair_endpoint_ledger
    (n D q : ℕ) (ww : Fin D → Fin q → pauliPairWord n) (c : Fin D → Fin q → ℚ)
    (S₁ S₂ : Fin D → Finset (Fin n)) (ε δ : ℝ)
    (_hO : ∀ z, 1 ≤ ‖pauliPairObservable n q (ww z) (c z)‖)
    (_hε : 0 < ε) (_hε1 : ε ≤ 1) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (_hD : 0 < D) :
    let B := (Finset.univ : Finset (Fin D)).fold max 0
      (fun z => (4 : ℝ)^(max (S₁ z).card (S₂ z).card) *
        ‖pauliPairObservable n q (ww z) (c z)‖^2)
    let m := Nat.ceil (140*B/ε^2)
    let r := Nat.log 4 (8*D*Nat.ceil (1/δ))+1
    ∀ ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool,
      tensorPauliFreshResourceCounts n m (2*r+1) ω =
        ((2*r+1)*m, 2*n*((2*r+1)*m), n*((2*r+1)*m), 0) ∧
      (∀ z, (quadraticShadowMedianCounted n m r (pauliPairObservable n q (ww z) (c z)) ω).2.1
          = 2*r+1 ∧
        (quadraticShadowMedianCounted n m r (pauliPairObservable n q (ww z) (c z)) ω).2.2
          ≤ (2*r+1)^2) ∧
      (∀ z, (∑ b, (pairUCounted
        (quadraticShadowKernel n (pauliPairObservable n q (ww z) (c z))) (ω b)).2)
        = (2*r+1)*m.choose 2) := by
  (try dsimp only)
  intro ω
  refine ⟨tensorPauliFreshResourceCounts_spec _ _ _ ω, ?_, ?_⟩
  · intro z
    exact (quadraticShadowMedianCounted_spec _ _ _ _ ω).2
  · intro z
    exact (quadratic_shadow_actual_quantum_and_pair_ledger _ _ _
      (pauliPairObservable n q (ww z) (c z)) ω).2

/-- Every tensor Pauli word is Hermitian. -/
theorem pauli_pair_word_hermitian (n : ℕ) (w : Fin n → Option (Fin 3)) :
    (tensorPauliWord n w).IsHermitian := by
  change (tensorPauliWord n w)ᴴ = tensorPauliWord n w
  rw [tensorPauliWord, tensorPauliProduct_conjTranspose]
  congr 1
  funext i
  cases w i with
  | none => simp [tensorPauliWordFactor]
  | some a => simp [tensorPauliWordFactor, pauliMatrix_conjTranspose]

/-- A rationally weighted Pauli pair observable is Hermitian. -/
theorem pauli_pair_observable_hermitian (n q : ℕ)
    (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ) :
    (pauliPairObservable n q ww c).IsHermitian := by
  change (pauliPairObservable n q ww c)ᴴ = pauliPairObservable n q ww c
  simp only [pauliPairObservable, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    TensorGate, Matrix.conjTranspose_kronecker,
    (pauli_pair_word_hermitian _ _).eq]
  simp

/-- The trace pairing of a Pauli pair observable with a tensor product factors into a
coefficient-weighted sum of products of single-register trace pairings. -/
theorem pauli_pair_complex_estimand (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (ρ ρ' : Operator (2^n)) :
    Matrix.trace (pauliPairObservable n q ww c * TensorGate ρ ρ') =
      ∑ j, (c j : ℂ) * Matrix.trace (tensorPauliWord n (ww j).1 * ρ) *
        Matrix.trace (tensorPauliWord n (ww j).2 * ρ') := by
  have ht (A B : Operator (2^n)) :
      Matrix.trace (TensorGate A B) = Matrix.trace A * Matrix.trace B :=
    Matrix.trace_kronecker A B
  simp only [pauliPairObservable, Matrix.sum_mul, Matrix.smul_mul,
    tensorGate_mul, Matrix.trace_sum, Matrix.trace_smul,
    ht, smul_eq_mul, mul_assoc]

/-- The quadratic shadow kernel of a Pauli pair observable is the average of the two orders of
the product estimators. -/
theorem pauli_pair_kernel_formula (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (a b : Fin n → Fin 3 × Bool) :
    quadraticShadowKernel n (pauliPairObservable n q ww c) a b =
      (1/2 : ℝ) * ∑ j, (c j : ℝ) *
        (tensorPauliValue (ww j).1 a * tensorPauliValue (ww j).2 b +
          tensorPauliValue (ww j).1 b * tensorPauliValue (ww j).2 a) := by
  rw [quadraticShadowKernel, quadratic_symmetric_trace,
    pauli_pair_complex_estimand, pauli_pair_complex_estimand]
  simp only [tensorPauliValue_trace, Complex.mul_re, Complex.add_re, Complex.re_sum,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  norm_num
  rw [← Finset.sum_add_distrib]
  congr 1
  funext j
  ring

/-- Symmetrizing a two-register observable does not increase its norm. -/
theorem pauli_pair_symmetrization_norm {D : ℕ}
    (O : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    ‖quadraticSymmetric O‖ ≤ ‖O‖ := by
  have hs : ‖swapRegisterMatrix D‖ ≤ 1 := l2_norm_unitary_le_one (by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      swapRegisterMatrix_conjTranspose, swapRegisterMatrix_mul_self])
  have hm : ‖swapRegisterMatrix D * O * swapRegisterMatrix D‖ ≤ ‖O‖ := by
    calc
      _ ≤ ‖swapRegisterMatrix D‖ * ‖O‖ * ‖swapRegisterMatrix D‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖O‖ * 1 := by gcongr
      _ = _ := by ring
  rw [quadraticSymmetric, norm_smul]
  have hc : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hc]
  have ha := norm_add_le O (swapRegisterMatrix D * O * swapRegisterMatrix D)
  linarith

/-- The formula replacing each complex trace factor by its real part is not valid for all
unrestricted input operators. -/
theorem pauli_pair_unrestricted_estimand_false :
    ¬ (∀ (n q : ℕ) (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ)
      (ρ ρ' : Operator (2^n)),
      (Matrix.trace (pauliPairObservable n q ww c * TensorGate ρ ρ')).re =
        ∑ j, (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ)).re *
          (Matrix.trace (tensorPauliWord n (ww j).2 * ρ')).re) := by
  intro hall
  let ww : Fin 1 → pauliPairWord 0 := fun _ => (fun _ => none, fun _ => none)
  have hw : tensorPauliWord 0 (fun _ => none) = 1 := by
    exact tensorPauliProduct_one 0
  have ht : Matrix.trace ((Complex.I : ℂ) • (1 : Operator (2^0))) = Complex.I := by
    norm_num [Matrix.trace_smul, Matrix.trace_one]
  have hh := hall 0 1 ww (fun _ => 1) (Complex.I • 1) (Complex.I • 1)
  rw [pauli_pair_complex_estimand] at hh
  simp only [ww, Fin.sum_univ_one, hw, Matrix.one_mul, ht] at hh
  norm_num [Complex.mul_re, Complex.mul_im] at hh

/-- The trace of the product of two Hermitian matrices has zero imaginary part. -/
theorem pauli_pair_hermitian_trace_real {D : ℕ} (A B : Operator D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (Matrix.trace (A * B)).im = 0 := by
  have hh : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hh
  change -(Matrix.trace (A * B)).im = (Matrix.trace (A * B)).im at hi
  linarith

/-- For Hermitian input operators, the real trace pairing of a Pauli pair observable is the
coefficient-weighted sum of products of real single-register trace pairings. -/
theorem pauli_pair_real_estimand (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (ρ ρ' : Operator (2^n))
    (hρ : ρ.IsHermitian) (hρ' : ρ'.IsHermitian) :
    (Matrix.trace (pauliPairObservable n q ww c * TensorGate ρ ρ')).re =
      ∑ j, (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ)).re *
        (Matrix.trace (tensorPauliWord n (ww j).2 * ρ')).re := by
  rw [pauli_pair_complex_estimand, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im,
    pauli_pair_hermitian_trace_real _ _ (pauli_pair_word_hermitian _ _) hρ,
    pauli_pair_hermitian_trace_real _ _ (pauli_pair_word_hermitian _ _) hρ',
    mul_zero, sub_zero]
  norm_num

/-- If every Hermitian observable satisfies the displayed group-size budget, the probability
that any median estimate exceeds error `ε` is bounded by the number of observables times the
stated geometric factor. -/
theorem quadratic_same_records_source_budget (n m r : ℕ)
    (Z : Type) [Fintype Z] (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (O : Z → Matrix (Fin (2^n) × Fin (2^n)) (Fin (2^n) × Fin (2^n)) ℂ)
    (ε : ℝ) (hm : 2 ≤ m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbudget : ∀ z, (O z).IsHermitian ∧
      140 * max
        (pairConditionalVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))
        (Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ) (quadraticShadowKernel n (O z)))) /
          ε^2 ≤ (m : ℝ)) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
      ∃ z, ε < |quadraticShadowMedian n m r (O z) ω - (Matrix.trace (O z * TensorGate ρ ρ)).re|),
      ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤
        (Fintype.card Z:ℝ)*(2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) := by
  classical
  let p := tensorPauliLaw n ρ hρ
  let Y := Fin m → Fin n → Fin 3 × Bool
  let q : FinDist Y :=
    { prob := p.probOf
      nonneg := fun ω => Finset.prod_nonneg fun _ _ => p.nonneg _
      sum_one := p.sum_probOf m }
  let θ := fun z => (Matrix.trace (O z * TensorGate ρ ρ)).re
  have hμ (z : Z) : q.expect (quadraticShadowU n m (O z)) = θ z :=
    quadratic_shadow_actual_u_unbiased n m ρ hρ (O z) hm (hbudget z).1
  have hv (z : Z) : q.expect (fun ω =>
      (quadraticShadowU n m (O z) ω - q.expect (quadraticShadowU n m (O z)))^2) ≤ ε^2/16 := by
    rw [hμ]
    exact (quadratic_group_variance_source_budget n m ρ hρ (O z) (hbudget z).1
      ε hε hε1 hm (hbudget z).2).trans (by nlinarith [sq_nonneg ε])
  have hc := heterogeneous_same_records_many_observables r 1 (fun _ _ => q)
    (fun _ _ _ => 1) (fun z _ _ => quadraticShadowU n m (O z)) θ ε hε
    (fun z _ => by simpa only [Fin.sum_univ_one, one_mul] using! hμ z)
    (fun z _ => by simpa only [Fin.sum_univ_one, one_pow, one_mul] using! hv z)
  let e : (Fin (2*r+1) → Y) ≃ (Fin (2*r+1) → Fin 1 → Y) :=
    { toFun := fun ω j _ => ω j
      invFun := fun ω j => ω j 0
      left_inv := fun _ => rfl
      right_inv := by
        intro ω
        funext j b
        have hb : b = 0 := Subsingleton.elim _ _
        subst b
        rfl }
  have hblock (z : Z) (ω : Fin (2*r+1) → Y) :
      weightedBlock r 1 (fun _ _ => 1) (fun _ _ => quadraticShadowU n m (O z)) (e ω) =
        fun j => quadraticShadowU n m (O z) (ω j) := by
    funext j
    change (∑ _b : Fin 1, (1:ℝ)*quadraticShadowU n m (O z) (ω j)) = _
    simp only [Fin.sum_univ_one, one_mul]
  have hprob (ω : Fin (2*r+1) → Y) :
      (blockRecordLaw r 1 (fun _ _ => q)).prob (e ω) = ∏ j, p.probOf (ω j) := by
    change (∏ j, ∏ _b : Fin 1, p.probOf (ω j)) = _
    simp only [Fin.prod_univ_one]
  rw [Finset.sum_filter] at hc ⊢
  rw [← e.sum_comp] at hc
  simp_rw [hblock, hprob] at hc
  simpa only [quadraticShadowMedian, θ, p, mul_assoc] using! hc

/-- The total real coefficient of a Pauli pair word, summing all occurrences in the indexed
presentation. -/
noncomputable def pauliPairCoefficient {n q : ℕ} (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ)
    (u : pauliPairWord n) : ℝ := ∑ j, if ww j = u then (c j : ℝ) else 0

noncomputable instance pauliPairWordFintype (n : ℕ) : Fintype (pauliPairWord n) := by
  unfold pauliPairWord
  infer_instance

/-- Summing a function against the aggregated Pauli pair coefficients equals the original
coefficient-weighted sum over terms. -/
private theorem pauli_pair_coefficient_sum {n q : ℕ}
    (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ) (f : pauliPairWord n → ℝ) :
    ∑ u, pauliPairCoefficient ww c u * f u = ∑ j, (c j : ℝ)*f (ww j) := by
  simp only [pauliPairCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

/-- The trace pairing of tensor Pauli pairs is zero for distinct pairs and `4 ^ n` for equal
pairs. -/
theorem pauli_pair_trace_orthogonal {n : ℕ} (u v : pauliPairWord n) :
    Matrix.trace (TensorGate (tensorPauliWord n u.1) (tensorPauliWord n u.2) *
      TensorGate (tensorPauliWord n v.1) (tensorPauliWord n v.2)) =
      if u = v then (4 : ℂ)^n else 0 := by
  rw [tensorGate_mul]
  change Matrix.trace ((tensorPauliWord n u.1 * tensorPauliWord n v.1) ⊗ₖ
    (tensorPauliWord n u.2 * tensorPauliWord n v.2)) = _
  rw [Matrix.trace_kronecker, localShadowPauli_trace_orthogonal,
    localShadowPauli_trace_orthogonal]
  have he : u = v ↔ u.1 = v.1 ∧ u.2 = v.2 := Prod.ext_iff
  by_cases h1 : u.1 = v.1 <;> by_cases h2 : u.2 = v.2 <;>
    simp [he, h1, h2, ← mul_pow]
  norm_num

/-- The real trace of the square of a Pauli pair observable is `4 ^ n` times the sum of squares
of its aggregated coefficients. -/
theorem pauli_pair_coefficient_parseval {n q : ℕ}
    (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ) :
    (Matrix.trace (pauliPairObservable n q ww c * pauliPairObservable n q ww c)).re =
      (4 : ℝ)^n * ∑ u, pauliPairCoefficient ww c u ^ 2 := by
  have hs : ∑ u, pauliPairCoefficient ww c u ^ 2 =
      ∑ j, ∑ l, if ww j = ww l then (c j : ℝ)*(c l : ℝ) else 0 := by
    simp_rw [pow_two]
    rw [pauli_pair_coefficient_sum]
    simp only [pauliPairCoefficient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : ww j = ww l <;> simp [h, Ne.symm]
  rw [hs]
  have hn : ((4 : ℂ)^n).re = (4 : ℝ)^n := by norm_cast
  simp only [pauliPairObservable, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul,
    pauli_pair_trace_orthogonal, Complex.re_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : ww j = ww l
  · simp [h, Complex.mul_re, Complex.mul_im, hn]
    ring
  · simp [h, Ne.symm h]

/-- The norm of any matrix entry is at most the norm of the matrix. -/
private theorem pauli_pair_entry_norm {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i j : I) : ‖A i j‖ ≤ ‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 := by
    have hs : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖^2 = 1 := by
      rw [norm_toEuclidean_sq_eq_re_inner,
        (normalized_iff_inner_self _).mp (normalized_ket j)]
      rfl
    nlinarith [norm_nonneg (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j))]
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk, mul_one] at hn
  have hi := PiLp.norm_apply_le (toEuclidean_fromVec (A*ᵥKet j)) i
  have he : (A*ᵥKet j) i = A i j := by
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]
  change ‖(A*ᵥKet j) i‖ ≤ ‖toEuclidean_fromVec (A*ᵥKet j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- The sum of squares of the aggregated Pauli pair coefficients is at most the squared
observable norm. -/
theorem pauli_pair_coefficient_mass_le {n q : ℕ}
    (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ) :
    ∑ u, pauliPairCoefficient ww c u ^ 2 ≤ ‖pauliPairObservable n q ww c‖^2 := by
  have ht : (Matrix.trace (pauliPairObservable n q ww c * pauliPairObservable n q ww c)).re ≤
      (4 : ℝ)^n * ‖pauliPairObservable n q ww c‖^2 := by
    calc
      _ = ∑ i, ((pauliPairObservable n q ww c * pauliPairObservable n q ww c) i i).re := by
        simp only [Matrix.trace, Complex.re_sum, Matrix.diag_apply]
      _ ≤ ∑ _ : Fin (2^n) × Fin (2^n), ‖pauliPairObservable n q ww c‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ‖(pauliPairObservable n q ww c * pauliPairObservable n q ww c) i i‖ :=
            (le_abs_self _).trans (Complex.abs_re_le_norm _)
          _ ≤ ‖pauliPairObservable n q ww c * pauliPairObservable n q ww c‖ :=
            pauli_pair_entry_norm _ i i
          _ ≤ ‖pauliPairObservable n q ww c‖^2 := by
            simpa [pow_two] using!
                norm_mul_le (pauliPairObservable n q ww c) (pauliPairObservable n q ww c)
      _ = (4 : ℝ)^n * ‖pauliPairObservable n q ww c‖^2 := by
        simp [← mul_pow]
  rw [pauli_pair_coefficient_parseval] at ht
  have hp : (0 : ℝ) < 4^n := by positivity
  nlinarith

/-- A Pauli pair observable is Hermitian, has the displayed symmetrized kernel and
complex-product trace formula, and its symmetrization has no larger norm. -/
theorem pauli_pair_kernel_and_estimand
    (n q : ℕ) (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ)
    (ρ ρ' : Operator (2^n)) (a b : Fin n → Fin 3 × Bool) :
    (pauliPairObservable n q ww c).IsHermitian ∧
    quadraticShadowKernel n (pauliPairObservable n q ww c) a b =
      (1 / 2 : ℝ) * ∑ j, (c j : ℝ) * (tensorPauliValue (ww j).1 a *
        tensorPauliValue (ww j).2 b + tensorPauliValue (ww j).1 b * tensorPauliValue (ww j).2 a) ∧
    (Matrix.trace (pauliPairObservable n q ww c * TensorGate ρ ρ')).re =
      ∑ j, (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ) *
        Matrix.trace (tensorPauliWord n (ww j).2 * ρ')).re ∧
    ‖quadraticSymmetric (pauliPairObservable n q ww c)‖ ≤ ‖pauliPairObservable n q ww c‖ := by
  refine ⟨pauli_pair_observable_hermitian n q ww c, pauli_pair_kernel_formula n q ww c a b,
    ?_, pauli_pair_symmetrization_norm _⟩
  rw [pauli_pair_complex_estimand, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_assoc, Complex.mul_re]

end Qatlib.Concepts.ShadowModels.ShadowVariance
