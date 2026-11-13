/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.MeasuredPauliShadows
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Moments and concentration of Pauli shadow estimates

For the single-qubit observable `pauliObservable c θ`, this module identifies
`pauliSnapshotValue c θ` with the trace against a Pauli shadow and computes its mean, second
moment, and variance under the physical distribution `pauliRecordDist`. These formulas give the
finite probability calculation underlying the classical-shadow estimator
[HuangKuengPreskill2020].

The result `pauli_shadow_many_observable_concentration` applies median-of-means concentration
and a union bound to a shared array of independent records for finitely many observables. Its
bound uses `K / 2` as natural-number division, exactly as in the finite-distribution
concentration statement.

## Main statements

* `trace_pauliMatrix_mul` gives the trace orthogonality of the three Pauli matrices.
* `trace_observable_shadow` identifies the matrix trace with the real snapshot formula.
* `pauli_shadow_mean_second_moment` proves unbiasedness, exact moments, and the variance bound
  `3 * ∑ a, (θ a)^2`.
* `pauli_shadow_many_observable_concentration` bounds simultaneous estimation failure by `M *
  3^(K/2) / 2^K` under the stated block-size budget.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.PauliClifford.ExactRank

open Matrix
open scoped ComplexOrder

set_option maxHeartbeats 4000000

/-- Each of the three Pauli matrices has trace zero. -/
theorem trace_pauliMatrix (a : Fin 3) : Matrix.trace (pauliMatrix a) = 0 := by
  fin_cases a <;>
    simp [pauliX, pauliY, pauliZ, Matrix.trace_fin_two]

/-- The trace of the product of two Pauli matrices is two when their axes agree and zero
otherwise. -/
theorem trace_pauliMatrix_mul (a b : Fin 3) :
    Matrix.trace (pauliMatrix a * pauliMatrix b) = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauliX, pauliY, pauliZ, Matrix.trace_fin_two] <;> norm_num

/-- The trace of the Pauli observable is twice its identity coefficient `c`. -/
theorem pauliObservable_trace (c : ℝ) (θ : Fin 3 → ℝ) :
    Matrix.trace (pauliObservable c θ) = 2 * (c : ℂ) := by
  rw [pauliObservable, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum]
  simp [Matrix.trace_smul, trace_pauliMatrix, Matrix.trace_one, Fintype.card_fin]
  ring

/-- The trace pairing of the Pauli observable with axis `a` is twice its coefficient `θ a`. -/
theorem pauliObservable_mul_pauliMatrix_trace (c : ℝ) (θ : Fin 3 → ℝ) (a : Fin 3) :
    Matrix.trace (pauliObservable c θ * pauliMatrix a) = 2 * (θ a : ℂ) := by
  have h1 : ∀ a' : Fin 3, Matrix.trace (((θ a' : ℂ) • pauliMatrix a') * pauliMatrix a)
      = (θ a' : ℂ) * (if a' = a then 2 else 0) := by
    intro a'
    rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauliMatrix_mul, smul_eq_mul]
  have h2 : ∀ a' : Fin 3, (θ a' : ℂ) * (if a' = a then (2 : ℂ) else 0)
      = if a' = a then (θ a' : ℂ) * 2 else 0 := by
    intro a'
    by_cases h : a' = a <;> simp [h]
  rw [pauliObservable, Matrix.add_mul, Finset.sum_mul, Matrix.trace_add, Matrix.trace_sum]
  rw [show Matrix.trace ((c : ℂ) • 1 * pauliMatrix a) = 0 from by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, trace_pauliMatrix, smul_zero]]
  rw [zero_add, Finset.sum_congr rfl fun a' _ => h1 a', Finset.sum_congr rfl fun a' _ => h2 a',
    Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ a)]
  ring

/-- The trace pairing with a Pauli outcome projector is `c + s * θ a`, where `s` is one for
`true` and minus one for `false`. -/
theorem trace_observable_projector (c : ℝ) (θ : Fin 3 → ℝ) (a : Fin 3) (b : Bool) :
    Matrix.trace (pauliObservable c θ * PauliProjector a b)
      = (c : ℂ) + (if b then (1 : ℂ) else -1) * (θ a : ℂ) := by
  rw [PauliProjector, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, pauliObservable_trace,
    pauliObservable_mul_pauliMatrix_trace]
  ring

/-- The complex trace of the observable against a Pauli shadow equals the corresponding real
snapshot value coerced to the complex numbers. -/
theorem trace_observable_shadow (c : ℝ) (θ : Fin 3 → ℝ) (a : Fin 3) (b : Bool) :
    Matrix.trace (pauliObservable c θ * PauliShadow b a)
      = ((pauliSnapshotValue c θ (a, b) : ℝ) : ℂ) := by
  rw [PauliShadow, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.mul_one, trace_observable_projector, pauliObservable_trace]
  cases b <;> simp [pauliSnapshotValue] <;> ring

/-- For a density operator, the real trace pairing of the Pauli observable is `c + ∑ a, θ a *
pauliExpectation a ρ`. -/
theorem pauliObservable_trace_re (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (c : ℝ) (θ : Fin 3 → ℝ) :
    (Matrix.trace (pauliObservable c θ * ρ)).re = c + ∑ a, θ a * pauliExpectation a ρ := by
  have h1 : Matrix.trace (pauliObservable c θ * ρ)
      = (c : ℂ) * Matrix.trace ρ
          + ∑ a : Fin 3, (θ a : ℂ) * Matrix.trace (pauliMatrix a * ρ) := by
    rw [pauliObservable, Matrix.add_mul, Finset.sum_mul, Matrix.trace_add, Matrix.trace_sum]
    rw [show Matrix.trace ((c : ℂ) • 1 * ρ) = (c : ℂ) * Matrix.trace ρ from by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [h1, hρ.2]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_sum, zero_mul, sub_zero, mul_one]
  rfl

/-- The snapshot equals the real shadow trace and is unbiased for the observable expectation;
writing `s = ∑ a, θ a * pauliExpectation a ρ`, its second moment is `c^2 + 2*c*s + 3*∑ a, (θ
a)^2`. Its variance is `3*∑ a, (θ a)^2 - s^2`, hence at most `3*∑ a, (θ a)^2`. -/
theorem pauli_shadow_mean_second_moment (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (c : ℝ) (θ : Fin 3 → ℝ) :
    (∀ o, pauliSnapshotValue c θ o = (Matrix.trace (pauliObservable c θ * PauliShadow o.2 o.1)).re) ∧
    (pauliRecordDist ρ hρ).expect (pauliSnapshotValue c θ) = (Matrix.trace (pauliObservable c θ * ρ)).re ∧
    (pauliRecordDist ρ hρ).expect (fun o => (pauliSnapshotValue c θ o)^2) = c^2 + 2*c*(∑ a, θ a*pauliExpectation a ρ) + 3*∑ a, (θ a)^2 ∧
    (pauliRecordDist ρ hρ).variance (pauliSnapshotValue c θ) = 3*(∑ a, (θ a)^2) - (∑ a, θ a*pauliExpectation a ρ)^2 ∧
    (pauliRecordDist ρ hρ).variance (pauliSnapshotValue c θ) ≤ 3*∑ a, (θ a)^2 := by
  set u : Fin 3 → Bool → ℝ :=
    fun a b => (Matrix.trace (PauliProjector a b * ρ)).re with hu
  have hub := pauliShadow_unbiased ρ hρ
  have hub' : (1/3 : ℂ) • ∑ a : Fin 3, ∑ b : Bool, (u a b : ℂ) • PauliShadow b a = ρ := hub

  have hbridge : ∀ o : Fin 3 × Bool,
      pauliSnapshotValue c θ o = (Matrix.trace (pauliObservable c θ * PauliShadow o.2 o.1)).re := by
    intro o
    obtain ⟨a, b⟩ := o
    rw [trace_observable_shadow]
    exact (Complex.ofReal_re _).symm

  have hlin : Matrix.trace (pauliObservable c θ *
        ((1/3 : ℂ) • ∑ a : Fin 3, ∑ b : Bool, (u a b : ℂ) • PauliShadow b a))
      = (1/3 : ℂ) * ∑ a : Fin 3, ∑ b : Bool, (u a b : ℂ) * (pauliSnapshotValue c θ (a, b) : ℂ) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_observable_shadow, smul_eq_mul]
  have hlin' : (1/3 : ℂ) * ∑ a : Fin 3, ∑ b : Bool, (u a b : ℂ) * (pauliSnapshotValue c θ (a, b) : ℂ)
      = (((1/3) * ∑ a : Fin 3, ∑ b : Bool, u a b * pauliSnapshotValue c θ (a, b) : ℝ) : ℂ) := by
    push_cast
    ring
  have hmean : (pauliRecordDist ρ hρ).expect (pauliSnapshotValue c θ)
      = (Matrix.trace (pauliObservable c θ * ρ)).re := by
    have hstep : (pauliRecordDist ρ hρ).expect (pauliSnapshotValue c θ)
        = (1/3) * ∑ a : Fin 3, ∑ b : Bool, u a b * pauliSnapshotValue c θ (a, b) := by
      show ∑ o : Fin 3 × Bool, (pauliRecordDist ρ hρ).prob o * pauliSnapshotValue c θ o = _
      rw [Fintype.sum_prod_type' (fun a b => (pauliRecordDist ρ hρ).prob (a, b) *
          pauliSnapshotValue c θ (a, b)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hu]
      rw [show (pauliRecordDist ρ hρ).prob (a, b)
          = instrumentProb pauliShadowRecordInstrument ρ (a, b) from rfl,
        (pauli_record_kraus_and_mass.2 ρ (a, b)).2, mul_assoc]
    calc (pauliRecordDist ρ hρ).expect (pauliSnapshotValue c θ)
        = (((1/3) * ∑ a : Fin 3, ∑ b : Bool, u a b * pauliSnapshotValue c θ (a, b) : ℝ) : ℂ).re := by
          rw [hstep]
          rfl
      _ = (Matrix.trace (pauliObservable c θ * ρ)).re := by
          rw [← hlin', ← hlin, hub']

  have hu_sum : ∀ a : Fin 3, u a true + u a false = 1 := by
    intro a
    have hsumP : PauliProjector a true + PauliProjector a false = 1 := by
      rw [← pauliProjector_sum a, sum_bool, add_comm]
    have h1 : Matrix.trace (PauliProjector a true * ρ) + Matrix.trace (PauliProjector a false * ρ)
        = 1 := by
      rw [← Matrix.trace_add, ← Matrix.add_mul, hsumP, Matrix.one_mul, hρ.2]
    simp only [hu]
    rw [← Complex.add_re, h1]
    rfl
  have hu_diff : ∀ a : Fin 3, u a true - u a false = pauliExpectation a ρ := by
    intro a
    have hsub : PauliProjector a true - PauliProjector a false = pauliMatrix a := by
      rw [PauliProjector, PauliProjector]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      module
    simp only [hu]
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul, hsub]
    rfl

  have haxis : ∀ a : Fin 3,
      ∑ b : Bool, (1/3) * u a b * (pauliSnapshotValue c θ (a, b))^2
        = (1/3) * (c^2 + 9*(θ a)^2 + 6*c*(θ a)*pauliExpectation a ρ) := by
    intro a
    have huT : u a true = (1 + pauliExpectation a ρ) / 2 := by
      have h1 := hu_sum a
      have h2 := hu_diff a
      linarith
    have huF : u a false = (1 - pauliExpectation a ρ) / 2 := by
      have h1 := hu_sum a
      have h2 := hu_diff a
      linarith
    rw [sum_bool]
    simp only [pauliSnapshotValue, ite_true, Bool.false_eq_true, ite_false]
    rw [huT, huF]
    ring
  have hmoment2 : (pauliRecordDist ρ hρ).expect (fun o => (pauliSnapshotValue c θ o)^2)
      = c^2 + 2*c*(∑ a, θ a*pauliExpectation a ρ) + 3*∑ a, (θ a)^2 := by
    calc (pauliRecordDist ρ hρ).expect (fun o => (pauliSnapshotValue c θ o)^2)
        = ∑ a : Fin 3, ∑ b : Bool, (1/3) * u a b * (pauliSnapshotValue c θ (a, b))^2 := by
          show ∑ o : Fin 3 × Bool, (pauliRecordDist ρ hρ).prob o * (pauliSnapshotValue c θ o)^2 = _
          rw [Fintype.sum_prod_type' (fun a b => (pauliRecordDist ρ hρ).prob (a, b) *
              (pauliSnapshotValue c θ (a, b))^2)]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          simp only [hu]
          rw [show (pauliRecordDist ρ hρ).prob (a, b)
              = instrumentProb pauliShadowRecordInstrument ρ (a, b) from rfl,
            (pauli_record_kraus_and_mass.2 ρ (a, b)).2, mul_assoc]
      _ = ∑ a : Fin 3, (1/3) * (c^2 + 9*(θ a)^2 + 6*c*(θ a)*pauliExpectation a ρ) :=
          Finset.sum_congr rfl fun a _ => haxis a
      _ = c^2 + 2*c*(∑ a, θ a*pauliExpectation a ρ) + 3*∑ a, (θ a)^2 := by
          have h2 : ∀ a : Fin 3, (1/3 : ℝ) * (c^2 + 9*(θ a)^2 + 6*c*(θ a)*pauliExpectation a ρ)
              = (1/3)*c^2 + (1/3)*9*(θ a)^2 + (1/3)*(6*c)*(θ a * pauliExpectation a ρ) :=
            fun a => by ring
          rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  have hmean_re : (pauliRecordDist ρ hρ).expect (pauliSnapshotValue c θ)
      = c + ∑ a, θ a * pauliExpectation a ρ := by
    rw [hmean]
    exact pauliObservable_trace_re ρ hρ c θ
  refine ⟨hbridge, hmean, hmoment2, ?_, ?_⟩
  · rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance_eq_expect_sq_sub, hmoment2, hmean_re]
    ring
  · rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance_eq_expect_sq_sub, hmoment2, hmean_re]
    have h3 : c^2 + 2*c*(∑ a, θ a*pauliExpectation a ρ) + 3*∑ a, (θ a)^2 - (c + ∑ a, θ a*pauliExpectation a ρ)^2
        = 3*(∑ a, (θ a)^2) - (∑ a, θ a*pauliExpectation a ρ)^2 := by ring
    rw [h3]
    exact sub_le_self _ (sq_nonneg _)

/-- For positive `L`, `K`, and `ε`, if every observable satisfies `12 * ∑ a, (θ j a)^2 ≤ L *
ε^2`, the probability that any median-of-means estimate has absolute error greater than `ε`
is at most `M * 3^(K/2) / 2^K`. The probability uses independent blocks of `L` physical
Pauli records, and `K / 2` is natural-number division. -/
theorem pauli_shadow_many_observable_concentration (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (L K M : ℕ) (c : Fin M → ℝ) (θ : Fin M → Fin 3 → ℝ) (ε : ℝ) (hL : 0<L) (hK : 0<K) (hε : 0<ε)
    (hbud : ∀ j, 12*(∑ a, (θ j a)^2) ≤ (L:ℝ)*ε^2) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool => ∃ j : Fin M, ε < |(pauliRecordDist ρ hρ).medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω - (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|),
        ∏ k, (pauliRecordDist ρ hρ).probOf (ω k)) ≤ (M:ℝ)*3^(K/2)/2^K := by
  set p := pauliRecordDist ρ hρ
  set q : FinDist (Fin L → Fin 3 × Bool) :=
    ⟨p.probOf, fun ω => Finset.prod_nonneg fun i _ => p.nonneg _, p.sum_probOf L⟩
  have hper : ∀ j : Fin M,
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool =>
          ε < |p.medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|), ∏ k, p.probOf (ω k))
        ≤ 3^(K/2)/2^K := by
    intro j
    have hvar : 4 * p.variance (pauliSnapshotValue (c j) (θ j)) ≤ (L:ℝ) * ε^2 := by
      have h1 := (pauli_shadow_mean_second_moment ρ hρ (c j) (θ j)).2.2.2.2
      calc 4 * p.variance (pauliSnapshotValue (c j) (θ j))
          ≤ 4 * (3 * ∑ a, (θ j a)^2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 12 * (∑ a, (θ j a)^2) := by ring
        _ ≤ (L:ℝ) * ε^2 := hbud j
    have hmean : p.expect (pauliSnapshotValue (c j) (θ j))
        = (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re :=
      (pauli_shadow_mean_second_moment ρ hρ (c j) (θ j)).2.1
    have hmc := p.median_of_means_concentration (pauliSnapshotValue (c j) (θ j)) hL hK ε hε hvar
    rw [hmean] at hmc
    exact hmc
  have hub := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.union_bound q (fun j (ω : Fin K → Fin L → Fin 3 × Bool) =>
    ε < |p.medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
      (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|)
  calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool => ∃ j : Fin M,
          ε < |p.medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|),
        ∏ k, p.probOf (ω k))
      = q.probEvent (fun ω : Fin K → Fin L → Fin 3 × Bool => ∃ j : Fin M,
          ε < |p.medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|) := rfl
    _ ≤ ∑ j : Fin M, q.probEvent (fun ω : Fin K → Fin L → Fin 3 × Bool =>
          ε < |p.medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|) := hub
    _ = ∑ j : Fin M, (∑ ω ∈ Finset.univ.filter (fun ω : Fin K → Fin L → Fin 3 × Bool =>
          ε < |p.medianOfMeans (pauliSnapshotValue (c j) (θ j)) ω -
            (Matrix.trace (pauliObservable (c j) (θ j) * ρ)).re|), ∏ k, p.probOf (ω k)) := rfl
    _ ≤ ∑ j : Fin M, 3^(K/2)/2^K := Finset.sum_le_sum fun j _ => hper j
    _ = (M:ℝ)*3^(K/2)/2^K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]

end Qatlib.Concepts.PauliClifford.ExactRank
