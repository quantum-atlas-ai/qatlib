/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder
import Mathlib.Algebra.Order.Floor.Ring

/-!
# qDRIFT with finite references

This module formalizes coefficient-weighted qDRIFT simulation with independently sampled
component evolutions. The estimates follow the random-compiler framework of [Campbell2019] and
apply to arbitrary complex matrix inputs with an arbitrary finite reference; the proved global
bound uses the constant `4`.

## Main statements

* `qdrift_signed_coefficient_bridge`: signed coefficients give a probability law and a matching
  mean Hamiltonian.
* `qdrift_fresh_reference_global_error`: the `4*lam^2*t^2/n` trace norm error estimate.
* `qdrift_derived_precision_budget`: an explicit positive step count achieving the requested
  precision.
* `qdrift_zero_coefficients_and_empty_index`: zero coefficients produce no component calls and
  preserve the input.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.RandCompile.ReferenceModel

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

/-- The Hamiltonian obtained by multiplying the distribution-weighted mean of `K` by the real
scale `lam`. -/
noncomputable def qdriftHamiltonian {L D : ℕ} (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam : ℝ) : Operator D :=
  (lam : ℂ) • ∑ j, (d.prob j : ℂ) • K j

/-- The step budget `max 1` of the natural ceiling of `4*lam^2*t^2/ε`. -/
noncomputable def qdriftSteps (lam t ε : ℝ) : ℕ := max 1 ⌈4 * lam ^ 2 * t ^ 2 / ε⌉₊

/-- The probability distribution with probabilities proportional to the absolute coefficients,
assuming their sum is positive. -/
noncomputable def qdriftCoefficientLaw {L : ℕ} (a : Fin L → ℝ)
    (hlam : 0 < ∑ j, |a j|) : FinDist (Fin L) where
  prob j := |a j| / ∑ i, |a i|
  nonneg j := div_nonneg (abs_nonneg _) hlam.le
  sum_one := by rw [← Finset.sum_div, div_self (ne_of_gt hlam)]

/-- The component operators with each negative coefficient sign absorbed into its operator. -/
noncomputable def qdriftSignedTerms {L D : ℕ} (a : Fin L → ℝ)
    (K : Fin L → Operator D) (j : Fin L) : Operator D :=
  (if a j < 0 then -1 else (1 : ℂ)) • K j

/-- The ordered component-time list for the sampled indices `ω`, using the same time `s` for
every component. -/
def qdriftComponentWord {L n : ℕ} (ω : Fin n → Fin L) (s : ℝ) : List (Fin L × ℝ) :=
  List.ofFn (fun i => (ω i, s))

/-- The list of `n` common qDRIFT times for positive coefficient mass, or the empty list when
the mass is zero. -/
noncomputable def zeroSafeQdriftTimes {L : ℕ} (a : Fin L → ℝ) (t : ℝ) (n : ℕ) : List ℝ :=
  if 0 < ∑ j, |a j| then List.replicate n (t * (∑ j, |a j|) / (n : ℝ)) else []

/-- The length of the zero-safe component-time list, independent of the requested evolution
time. -/
noncomputable def zeroSafeQdriftCalls {L : ℕ} (a : Fin L → ℝ) (n : ℕ) : ℕ :=
  (zeroSafeQdriftTimes a 0 n).length

/-- The zero-safe call count equals the component-time list length for any time `t`. -/
theorem zeroSafeQdriftCalls_eq_times_length {L : ℕ} (a : Fin L → ℝ) (t : ℝ) (n : ℕ) :
    zeroSafeQdriftCalls a n = (zeroSafeQdriftTimes a t n).length := by
  by_cases h : 0 < ∑ j, |a j|
  · simp [zeroSafeQdriftCalls, zeroSafeQdriftTimes, h]
  · simp [zeroSafeQdriftCalls, zeroSafeQdriftTimes, h]

/-- The iterated signed-component qDRIFT mixture for positive coefficient mass, returning the
input otherwise. -/
noncomputable def zeroSafeQdrift {L D : ℕ} (a : Fin L → ℝ) (K : Fin L → Operator D)
    (t : ℝ) (n : ℕ) (ρ : Operator D) : Operator D :=
  if hlam : 0 < ∑ j, |a j| then
    mixturePowerMap (qdriftCoefficientLaw a hlam)
      (fun j => HamiltonianEvolution (qdriftSignedTerms a K j)
        (t * (∑ j, |a j|) / (n : ℝ))) n ρ
  else ρ

/-- The uniform probability distribution on two component indices. -/
noncomputable def qdriftTwoLaw : FinDist (Fin 2) where
  prob _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fin.sum_univ_two]

/-- Absolute-coefficient sampling and sign absorption reconstruct the coefficient-weighted
Hamiltonian and preserve Hermitian contraction bounds on the terms. This is the
signed-coefficient setup for qDRIFT in [Campbell2019]. -/
theorem qdrift_signed_coefficient_bridge (L D : ℕ) (a : Fin L → ℝ)
    (K : Fin L → Operator D) (hlam : 0 < ∑ j, |a j|) :
    (∀ j, (qdriftCoefficientLaw a hlam).prob j = |a j| / (∑ i, |a i|)) ∧
    qdriftHamiltonian (qdriftCoefficientLaw a hlam) (qdriftSignedTerms a K) (∑ j, |a j|) =
      ∑ j, (a j : ℂ) • K j ∧
    ((∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
      ∀ j, (qdriftSignedTerms a K j).IsHermitian ∧ ‖qdriftSignedTerms a K j‖ ≤ 1) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · unfold qdriftHamiltonian
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [qdriftCoefficientLaw, qdriftSignedTerms, smul_smul]
    congr 1
    have hne : (∑ i, |a i| : ℝ) ≠ 0 := ne_of_gt hlam
    have hneC : (∑ i, ((|a i| : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hne
    by_cases h : a j < 0
    · simp [h, abs_of_neg h, Complex.ofReal_div, hne]
      field_simp [hneC]
    · simp [h, abs_of_nonneg (le_of_not_gt h), Complex.ofReal_div, hne]
      field_simp [hneC]
  · intro h j
    by_cases hj : a j < 0
    · constructor
      · simpa [qdriftSignedTerms, hj] using (h j).1.neg
      · simpa [qdriftSignedTerms, hj] using (h j).2
    · simpa [qdriftSignedTerms, hj] using h j

/-- A real multiple of a probability-weighted mean of Hermitian components is Hermitian. -/
theorem qdriftHamiltonian_isHermitian {L D : ℕ} (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam : ℝ) (hK : ∀ j, (K j).IsHermitian) :
    (qdriftHamiltonian d K lam).IsHermitian := by
  change (qdriftHamiltonian d K lam)ᴴ = qdriftHamiltonian d K lam
  simp [qdriftHamiltonian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    fun j => (hK j).eq]

/-- If `lam` is nonnegative and every component has operator norm at most one, the mean
Hamiltonian has norm at most `lam`. -/
theorem qdriftHamiltonian_norm_le {L D : ℕ} (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam : ℝ) (hlam : 0 ≤ lam) (hK : ∀ j, ‖K j‖ ≤ 1) :
    ‖qdriftHamiltonian d K lam‖ ≤ lam := by
  calc
    _ = lam * ‖∑ j, (d.prob j : ℂ) • K j‖ := by
      simp [qdriftHamiltonian, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
    _ ≤ lam * ∑ j, ‖(d.prob j : ℂ) • K j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hlam
    _ ≤ lam * ∑ j, d.prob j := by
      gcongr with j
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d.nonneg j)]
      exact (mul_le_mul_of_nonneg_left (hK j) (d.nonneg j)).trans_eq (mul_one _)
    _ = lam := by rw [d.sum_one, mul_one]

/-- The trace norm of a finite matrix sum is at most the sum of the trace norms. -/
private theorem qdrift_traceNorm_sum_le {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] (F : J → Matrix I I ℂ) :
    Matrix.traceNorm (∑ j, F j) ≤ ∑ j, Matrix.traceNorm (F j) := by
  have h : ∀ S : Finset J, Matrix.traceNorm (∑ j ∈ S, F j) ≤ ∑ j ∈ S, Matrix.traceNorm (F j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      simpa [Finset.sum_insert hj] using (Matrix.traceNorm_add_le (F j) (∑ k ∈ S, F k)).trans
        (add_le_add (le_refl _) ih)
  exact h Finset.univ

/-- The linear map sending a Hamiltonian to its commutator with `ρ` after tensoring with the
reference identity. -/
private noncomputable def qdriftReferenceGenerator {D : ℕ} (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Operator D →ₗ[ℂ] Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ where
  toFun H := TensorGate H (1 : Operator r) * ρ - ρ * TensorGate H (1 : Operator r)
  map_add' A B := by
    simp only [TensorGate, Matrix.add_kronecker, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' c A := by
    simp only [TensorGate, Matrix.smul_kronecker, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rfl

/-- The probability-weighted first-order component expansions coincide with the first-order
expansion for the mean Hamiltonian. -/
private theorem qdrift_first_order_cancellation {L D : ℕ} (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam τ : ℝ) (r : ℕ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    (∑ j, (d.prob j : ℂ) •
      (ρ - (Complex.I * ((τ * lam : ℝ) : ℂ)) • qdriftReferenceGenerator r ρ (K j))) =
      ρ - (Complex.I * (τ : ℂ)) • qdriftReferenceGenerator r ρ (qdriftHamiltonian d K lam) := by
  have hprob : (∑ j, (d.prob j : ℂ)) = 1 := by exact_mod_cast d.sum_one
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hprob, one_smul]
  congr 1
  simp only [qdriftHamiltonian, map_smul, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  push_cast
  ring

/-- Conjugation by Hamiltonian evolution on the system tensored with the identity on the finite
reference. -/
private noncomputable def qdriftReferenceConjugation {D : ℕ} (H : Operator D) (τ : ℝ)
    (r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
  TensorGate (HamiltonianEvolution H τ) (1 : Operator r) * ρ *
    (TensorGate (HamiltonianEvolution H τ) (1 : Operator r))ᴴ

/-- For Hermitian `H`, the first-order reference conjugation remainder has trace norm at most
`2*τ^2*‖H‖^2*Matrix.traceNorm ρ`. -/
private theorem qdrift_remainder_bound {D : ℕ} (H : Operator D) (τ : ℝ)
    (r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) (hH : H.IsHermitian) :
    Matrix.traceNorm (qdriftReferenceConjugation H τ r ρ -
      (ρ - (Complex.I * (τ : ℂ)) • qdriftReferenceGenerator r ρ H)) ≤
      2 * τ ^ 2 * ‖H‖ ^ 2 * Matrix.traceNorm ρ := by
  have he : qdriftReferenceConjugation H τ r ρ -
      (ρ - (Complex.I * (τ : ℂ)) • qdriftReferenceGenerator r ρ H) =
      qdriftReferenceConjugation H τ r ρ - ρ +
        (Complex.I * (τ : ℂ)) • qdriftReferenceGenerator r ρ H := by abel
  rw [he]
  exact hamiltonian_reference_first_order_remainder D r H τ ρ hH

/-- For Hermitian contraction components and nonnegative `lam`, the one-step mixture error
relative to mean-Hamiltonian evolution is at most `4*(τ*lam)^2*Matrix.traceNorm ρ`. -/
private theorem qdrift_one_step_bound (L D r : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam τ : ℝ) (hlam : 0 ≤ lam)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixture d (fun j => HamiltonianEvolution (K j) (τ * lam)) r ρ -
      qdriftReferenceConjugation (qdriftHamiltonian d K lam) τ r ρ) ≤
      4 * (τ * lam) ^ 2 * Matrix.traceNorm ρ := by
  let s := τ * lam
  let P : Operator D → ℝ → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ :=
    fun H u => ρ - (Complex.I * (u : ℂ)) • qdriftReferenceGenerator r ρ H
  let R := fun j => qdriftReferenceConjugation (K j) s r ρ - P (K j) s
  let RI := qdriftReferenceConjugation (qdriftHamiltonian d K lam) τ r ρ -
    P (qdriftHamiltonian d K lam) τ
  have hρ := Matrix.traceNorm_nonneg ρ
  have hr (j : Fin L) : Matrix.traceNorm (R j) ≤ 2 * s ^ 2 * Matrix.traceNorm ρ := by
    have h := qdrift_remainder_bound (K j) s r ρ (hK j).1
    refine h.trans ?_
    calc
      2 * s ^ 2 * ‖K j‖ ^ 2 * Matrix.traceNorm ρ ≤
          2 * s ^ 2 * 1 ^ 2 * Matrix.traceNorm ρ := by gcongr; exact (hK j).2
      _ = _ := by ring
  have hri : Matrix.traceNorm RI ≤ 2 * s ^ 2 * Matrix.traceNorm ρ := by
    have h := qdrift_remainder_bound (qdriftHamiltonian d K lam) τ r ρ
      (qdriftHamiltonian_isHermitian d K lam (fun j => (hK j).1))
    refine h.trans ?_
    calc
      2 * τ ^ 2 * ‖qdriftHamiltonian d K lam‖ ^ 2 * Matrix.traceNorm ρ ≤
          2 * τ ^ 2 * lam ^ 2 * Matrix.traceNorm ρ := by
        gcongr
        exact qdriftHamiltonian_norm_le d K lam hlam (fun j => (hK j).2)
      _ = _ := by dsimp [s]; ring
  have hrmean : Matrix.traceNorm (∑ j, (d.prob j : ℂ) • R j) ≤
      2 * s ^ 2 * Matrix.traceNorm ρ := by
    refine (qdrift_traceNorm_sum_le _).trans ?_
    calc
      (∑ j, Matrix.traceNorm ((d.prob j : ℂ) • R j)) =
          ∑ j, d.prob j * Matrix.traceNorm (R j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Matrix.traceNorm_smul]
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d.nonneg j)]
      _ ≤ ∑ j, d.prob j * (2 * s ^ 2 * Matrix.traceNorm ρ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hr j) (d.nonneg j))
      _ = _ := by rw [← Finset.sum_mul, d.sum_one, one_mul]
  have he : referenceMixture d (fun j => HamiltonianEvolution (K j) (τ * lam)) r ρ -
      qdriftReferenceConjugation (qdriftHamiltonian d K lam) τ r ρ =
      (∑ j, (d.prob j : ℂ) • R j) - RI := by
    have hc : (∑ j, (d.prob j : ℂ) • P (K j) s) = P (qdriftHamiltonian d K lam) τ :=
      qdrift_first_order_cancellation d K lam τ r ρ
    have hs : (∑ j, (d.prob j : ℂ) • R j) =
        referenceMixture d (fun j => HamiltonianEvolution (K j) (τ * lam)) r ρ -
          P (qdriftHamiltonian d K lam) τ := by
      calc
        _ = (∑ j, (d.prob j : ℂ) • qdriftReferenceConjugation (K j) s r ρ) -
            ∑ j, (d.prob j : ℂ) • P (K j) s := by
          simp only [R, smul_sub, Finset.sum_sub_distrib]
        _ = _ := by rw [hc]; rfl
    rw [hs]
    dsimp [RI]
    abel
  rw [he, sub_eq_add_neg]
  have hn : Matrix.traceNorm (-RI) = Matrix.traceNorm RI := by
    exact Matrix.traceNorm_neg RI
  refine (Matrix.traceNorm_add_le _ _).trans ?_
  rw [hn]
  exact (add_le_add hrmean hri).trans_eq (by dsimp [s]; ring)

/-- For a positive step count, nonnegative `lam`, and Hermitian contraction components, one
qDRIFT step differs from mean-Hamiltonian evolution for time `t/n` by at most
`4*(t*lam/n)^2*Matrix.traceNorm ρ`. This implements the first-order cancellation underlying
[Campbell2019]. -/
theorem qdrift_actual_one_step_first_order_cancels (L D r : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam t : ℝ) (n : ℕ) (hlam : 0 ≤ lam) (_hn : 0 < n)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixture d (fun j => HamiltonianEvolution (K j) (t * lam / (n : ℝ))) r ρ -
      TensorGate (HamiltonianEvolution (qdriftHamiltonian d K lam) (t / (n : ℝ))) (1 : Operator r) * ρ *
        (TensorGate (HamiltonianEvolution (qdriftHamiltonian d K lam) (t / (n : ℝ))) (1 : Operator r))ᴴ) ≤
      4 * (t * lam / (n : ℝ)) ^ 2 * Matrix.traceNorm ρ := by
  have he : t / (n : ℝ) * lam = t * lam / (n : ℝ) := by ring
  simpa only [he, qdriftReferenceConjugation] using
      qdrift_one_step_bound L D r d K lam (t / n) hlam hK ρ

/-- Successive reference conjugations by one Hamiltonian combine by adding the evolution times. -/
private theorem qdriftReferenceConjugation_add {D : ℕ} (H : Operator D) (s t : ℝ)
    (r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    qdriftReferenceConjugation H s r (qdriftReferenceConjugation H t r ρ) =
      qdriftReferenceConjugation H (s + t) r ρ := by
  have hm : TensorGate (HamiltonianEvolution H (s + t)) (1 : Operator r) =
      TensorGate (HamiltonianEvolution H s) (1 : Operator r) *
        TensorGate (HamiltonianEvolution H t) (1 : Operator r) := by
    rw [tensorGate_mul, Matrix.one_mul, ← hamiltonianEvolution_add]
  simp only [qdriftReferenceConjugation, hm, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- For positive `n`, nonnegative `lam`, and Hermitian contraction components, the fresh-sample
qDRIFT output has reference trace norm error at most `4*lam^2*t^2/n*Matrix.traceNorm ρ`.
This is the global simulation estimate corresponding to [Campbell2019]. -/
theorem qdrift_fresh_reference_global_error (L D r : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam t : ℝ) (n : ℕ) (hlam : 0 ≤ lam) (hn : 0 < n)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixturePower d
      (fun j => HamiltonianEvolution (K j) (t * lam / (n : ℝ))) r n ρ -
      TensorGate (HamiltonianEvolution (qdriftHamiltonian d K lam) t) (1 : Operator r) * ρ *
        (TensorGate (HamiltonianEvolution (qdriftHamiltonian d K lam) t) (1 : Operator r))ᴴ) ≤
      4 * lam ^ 2 * t ^ 2 / (n : ℝ) * Matrix.traceNorm ρ := by
  let δ := t / (n : ℝ)
  let U := fun j => HamiltonianEvolution (K j) (δ * lam)
  let H := qdriftHamiltonian d K lam
  have hH : H.IsHermitian := qdriftHamiltonian_isHermitian d K lam (fun j => (hK j).1)
  have hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    fun j => hamiltonianEvolution_unitary (hK j).1 _
  have hρ := Matrix.traceNorm_nonneg ρ
  have hi : ∀ m : ℕ,
      Matrix.traceNorm (referenceMixturePower d U r m ρ -
        qdriftReferenceConjugation H ((m : ℝ) * δ) r ρ) ≤
        (m : ℝ) * (4 * (δ * lam) ^ 2) * Matrix.traceNorm ρ := by
    intro m
    induction m with
    | zero => simp [referenceMixturePower, qdriftReferenceConjugation, tensorGate_one]
    | succ m ih =>
      let A := referenceMixturePower d U r m ρ
      let B := qdriftReferenceConjugation H ((m : ℝ) * δ) r ρ
      have hiter : referenceMixturePower d U r (m + 1) ρ = referenceMixture d U r A :=
        Function.iterate_succ_apply' (referenceMixture d U r) m ρ
      have htime : ((m + 1 : ℕ) : ℝ) * δ = δ + (m : ℝ) * δ := by push_cast; ring
      rw [hiter, htime, ← qdriftReferenceConjugation_add]
      have hs : referenceMixture d U r A - qdriftReferenceConjugation H δ r B =
          referenceMixture d U r (A - B) +
            (referenceMixture d U r B - qdriftReferenceConjugation H δ r B) := by
        rw [referenceMixture_sub]
        abel
      change Matrix.traceNorm (referenceMixture d U r A - qdriftReferenceConjugation H δ r B) ≤ _
      rw [hs]
      have h1 := (finite_reference_mixture_contraction d U r (A - B) hU).trans ih
      have h2 := qdrift_one_step_bound L D r d K lam δ hlam hK B
      have hB : Matrix.traceNorm B = Matrix.traceNorm ρ :=
        finite_reference_unitary_traceNorm _ r ρ (hamiltonianEvolution_unitary hH _)
      rw [hB] at h2
      exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by push_cast; ring)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have htime : (n : ℝ) * δ = t := by dsimp [δ]; field_simp
  have hstep : δ * lam = t * lam / (n : ℝ) := by dsimp [δ]; ring
  have h := hi n
  rw [htime] at h
  change Matrix.traceNorm (referenceMixturePower d U r n ρ - _) ≤ _ at h
  simpa only [U, hstep, H, qdriftReferenceConjugation] using h.trans_eq
    (by dsimp [δ]; field_simp)

/-- For positive `ε`, `qdriftSteps` is positive, is at most `4*lam^2*t^2/ε+1`, and achieves
reference error at most `ε*Matrix.traceNorm ρ` under the component assumptions. This gives
an explicit precision budget for [Campbell2019]. -/
theorem qdrift_derived_precision_budget (L D r : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (lam t ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    0 < qdriftSteps lam t ε ∧
    (qdriftSteps lam t ε : ℝ) ≤ 4 * lam ^ 2 * t ^ 2 / ε + 1 ∧
    ∀ ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      Matrix.traceNorm (referenceMixturePower d (fun j => HamiltonianEvolution (K j)
        (t * lam / (qdriftSteps lam t ε : ℝ))) r (qdriftSteps lam t ε) ρ -
        TensorGate (HamiltonianEvolution (qdriftHamiltonian d K lam) t) (1 : Operator r) * ρ *
          (TensorGate (HamiltonianEvolution (qdriftHamiltonian d K lam) t) (1 : Operator r))ᴴ) ≤
        ε * Matrix.traceNorm ρ := by
  let q := 4 * lam ^ 2 * t ^ 2 / ε
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn : 0 < qdriftSteps lam t ε := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hnR : 0 < (qdriftSteps lam t ε : ℝ) := by exact_mod_cast hn
  have hupper : (qdriftSteps lam t ε : ℝ) ≤ q + 1 := by
    simp only [qdriftSteps, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one hq).le
  have hlower : q ≤ (qdriftSteps lam t ε : ℝ) :=
    (Nat.le_ceil q).trans (by exact_mod_cast Nat.le_max_right 1 (Nat.ceil q))
  refine ⟨hn, hupper, fun ρ => ?_⟩
  have h := qdrift_fresh_reference_global_error L D r d K lam t
    (qdriftSteps lam t ε) hlam hn hK ρ
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg ρ))
  apply (div_le_iff₀ hnR).mpr
  have he := (div_le_iff₀ hε).mp hlower
  simpa only [mul_comm] using he

/-- Sequentially applying the component evolutions in a word agrees with running the
corresponding gate circuit. -/
private theorem run_component_word {L D : ℕ} (K : Fin L → Operator D)
    (word : List (Fin L × ℝ)) (ψ : QState (Fin D)) :
    word.foldl (fun v step => ApplyGate (HamiltonianEvolution (K step.1) step.2) v) ψ =
      Run 1 (word.map (fun step => Step.gate (HamiltonianEvolution (K step.1) step.2))) ψ := by
  induction word generalizing ψ with
  | nil => rfl
  | cons step word ih => simpa using ih (ApplyGate (HamiltonianEvolution (K step.1) step.2) ψ)

/-- A sampled component path has length and gate count `n`, total absolute time `n*|s|`, and
circuit semantics equal to the component fold. Hermitian components make this circuit
unitary, giving the component-cost interpretation of [Campbell2019]. -/
theorem qdrift_actual_fresh_path_and_component_cost (L D n : ℕ)
    (K : Fin L → Operator D) (ω : Fin n → Fin L) (s : ℝ) (ψ : QState (Fin D)) :
    (qdriftComponentWord ω s).length = n ∧
    ((qdriftComponentWord ω s).map (fun step => |step.2|)).sum = (n : ℝ) * |s| ∧
    (qdriftComponentWord ω s).foldl
      (fun v step => ApplyGate (HamiltonianEvolution (K step.1) step.2) v) ψ =
      Run 1 (mixturePathCircuit (fun j => HamiltonianEvolution (K j) s) ω) ψ ∧
    GateCount (mixturePathCircuit (fun j => HamiltonianEvolution (K j) s) ω) = n ∧
    ((∀ j, (K j).IsHermitian) →
      IsUnitaryCircuit (mixturePathCircuit (fun j => HamiltonianEvolution (K j) s) ω)) := by
  have hc := mixture_path_circuit_semantics_cost
    (fun j => HamiltonianEvolution (K j) s) n ω ψ
  refine ⟨by simp [qdriftComponentWord], ?_, ?_, hc.2.2.1, ?_⟩
  · simp only [qdriftComponentWord, List.map_ofFn, Function.comp_apply]
    change (List.ofFn (fun _ : Fin n => |s|)).sum = _
    simp [List.ofFn_const, List.sum_replicate]
  · simpa [qdriftComponentWord, mixturePathCircuit, ← List.ofFn_comp'] using!
      run_component_word K (qdriftComponentWord ω s) ψ
  · intro hK
    exact hc.2.2.2 (fun j => hamiltonianEvolution_unitary (hK j) s)

/-- For a single available component, the `n`-step reference mixture equals exact evolution for
total time `n*s`. -/
theorem qdrift_single_component_reference_exact (D r n : ℕ) (d : FinDist (Fin 1))
    (H : Operator D) (s : ℝ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixturePower d (fun _ => HamiltonianEvolution H s) r n ρ =
      TensorGate (HamiltonianEvolution H ((n : ℝ) * s)) (1 : Operator r) * ρ *
        (TensorGate (HamiltonianEvolution H ((n : ℝ) * s)) (1 : Operator r))ᴴ := by
  have hp : d.prob 0 = 1 := by simpa only [Fin.sum_univ_one] using d.sum_one
  change referenceMixturePower d (fun _ => HamiltonianEvolution H s) r n ρ =
    qdriftReferenceConjugation H ((n : ℝ) * s) r ρ
  induction n with
  | zero => simp [referenceMixturePower, qdriftReferenceConjugation, tensorGate_one]
  | succ n ih =>
    rw [show referenceMixturePower d (fun _ => HamiltonianEvolution H s) r (n + 1) ρ =
      referenceMixture d (fun _ => HamiltonianEvolution H s) r
        (referenceMixturePower d (fun _ => HamiltonianEvolution H s) r n ρ) from
          Function.iterate_succ_apply' _ n ρ, ih, referenceMixture_apply,
      Fin.sum_univ_one, hp, Complex.ofReal_one, one_smul]
    change qdriftReferenceConjugation H s r
      (qdriftReferenceConjugation H ((n : ℝ) * s) r ρ) = _
    rw [qdriftReferenceConjugation_add]
    congr 1
    push_cast
    ring

/-- The iterated reference mixture equals the average conjugation by sampled path operators
under the independent product law. -/
theorem qdrift_actual_fresh_reference_output (L D n r : ℕ) (d : FinDist (Fin L))
    (K : Fin L → Operator D) (s : ℝ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixturePower d (fun j => HamiltonianEvolution (K j) s) r n ρ =
      ∑ ω, ((independentSampleLaw (fun _ : Fin n => d)).prob ω : ℂ) •
        (TensorGate (mixturePathOperator (fun j => HamiltonianEvolution (K j) s) ω)
          (1 : Operator r) * ρ *
          (TensorGate (mixturePathOperator (fun j => HamiltonianEvolution (K j) s) ω)
            (1 : Operator r))ᴴ) :=
  mixture_fresh_paths_reference_output d (fun j => HamiltonianEvolution (K j) s) n r ρ

/-- For positive `n`, a qDRIFT path uses zero queries and its component times have total
absolute value `|t*lam|`. -/
theorem qdrift_actual_path_queries_and_total_time (L D n : ℕ)
    (K : Fin L → Operator D) (ω : Fin n → Fin L) (lam t : ℝ) (hn : 0 < n)
    (ψ : QState (Fin D)) :
    QueryCount (mixturePathCircuit (fun j => HamiltonianEvolution (K j) (t * lam / (n : ℝ))) ω) = 0 ∧
    ((qdriftComponentWord ω (t * lam / (n : ℝ))).map (fun step => |step.2|)).sum = |t * lam| := by
  refine ⟨(mixture_path_circuit_semantics_cost _ n ω ψ).2.1, ?_⟩
  rw [(qdrift_actual_fresh_path_and_component_cost L D n K ω _ ψ).2.1]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hnR]
  field_simp

/-- Zero coefficient mass gives a zero Hamiltonian, no component calls, and unchanged output.
Positive mass gives exactly `n` calls and the stated signed-component mixture. -/
theorem qdrift_zero_coefficients_and_empty_index (L D n : ℕ) (a : Fin L → ℝ)
    (K : Fin L → Operator D) (t : ℝ) :
    ((∑ j, |a j|) = 0 → (∑ j, (a j : ℂ) • K j) = 0 ∧ zeroSafeQdriftCalls a n = 0 ∧
      ∀ ρ : Operator D, zeroSafeQdrift a K t n ρ = ρ) ∧
    (∀ hlam : 0 < ∑ j, |a j|, zeroSafeQdriftCalls a n = n ∧
      ∀ ρ : Operator D, zeroSafeQdrift a K t n ρ =
        mixturePowerMap (qdriftCoefficientLaw a hlam)
          (fun j => HamiltonianEvolution (qdriftSignedTerms a K j)
            (t * (∑ j, |a j|) / (n : ℝ))) n ρ) := by
  constructor
  · intro hzero
    have ha : ∀ j, a j = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (a j))).mp hzero
      intro j
      exact abs_eq_zero.mp (h j (Finset.mem_univ j))
    simp [ha, zeroSafeQdriftCalls, zeroSafeQdriftTimes, zeroSafeQdrift]
  · intro hlam
    simp [zeroSafeQdriftCalls, zeroSafeQdriftTimes, zeroSafeQdrift, hlam]

end Qatlib.Concepts.RandCompile.ReferenceModel
