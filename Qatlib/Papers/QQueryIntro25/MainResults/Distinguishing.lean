/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QQueryIntro25.MainResults.SourceModel
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

set_option backward.isDefEq.respectTransparency false

/-!
# Pseudorandomness of `2k`-Wise Independent Distributions Against Quantum Queries

This module formalizes Section 3.3, Proposition 26 of Hamoudi on the polynomial
method for distinguishing problems over `{0, 1}^n`, proving that any `2k`-wise
independent distribution `μ` has zero distinguishing advantage against every
unitary workspace-oracle quantum algorithm making at most `k` queries.

## Main definitions

* `IsKWiseIndependent`: `k`-wise uniform marginal condition on `{0, 1}^n`.
* `uniformWeight`, `uniformAverage`, `distinguishingAdvantage`: Boolean-cube
  uniform expectation and predictor distinguishing advantage.
* `IsPseudorandomForKQueryAlgorithms`: zero distinguishing advantage for all
  `k`-query unitary quantum circuits.

## Main statements

* `proposition26_distinguishing`: Proposition 26, `2k`-wise independence implies
  pseudorandomness against `k`-query quantum algorithms.

## References

* [Hamoudi, 2025][Hamoudi2025QueryIntro], Section 3.3, Proposition 26, p. 13.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QQueryIntro25.MainResults

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A distribution `mu` on the Boolean cube `{0,1}^n` is `k`-wise independent:
every restriction to at most `k` coordinates is uniform.  This is the paper's
`k`-wise independence hypothesis (printed p. 13), written with an explicit
uniform marginal on each coordinate set `S` with `|S| ≤ k`. -/
def IsKWiseIndependent (n k : ℕ) (mu : (Fin n → Bool) → ℝ) : Prop :=
  (∀ x : Fin n → Bool, 0 ≤ mu x) ∧
    (∑ x : Fin n → Bool, mu x = 1) ∧
      (∀ S : Finset (Fin n), S.card ≤ k → ∀ b : Fin n → Bool,
        (∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => ∀ i ∈ S, x i = b i), mu x) =
          (1 / 2 : ℝ) ^ S.card)

/-- The weight of a single point under the uniform distribution on `{0,1}^n`. -/
def uniformWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- The uniform average of a real-valued function `D` on the Boolean cube. -/
def uniformAverage (n : ℕ) (D : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ x : Fin n → Bool, uniformWeight n * D x

/-- The distinguishing advantage of the predictor `D` between the distribution
`mu` and the uniform distribution on `{0,1}^n` (printed p. 13). -/
def distinguishingAdvantage (n : ℕ) (mu : (Fin n → Bool) → ℝ)
    (D : (Fin n → Bool) → ℝ) : ℝ :=
  |(∑ x : Fin n → Bool, mu x * D x) - uniformAverage n D|

/-- `mu` is pseudorandom for the class of quantum algorithms making at most `k`
queries: every bounded-error `k`-query circuit (with any accepting register) has
zero distinguishing advantage between `mu` and the uniform distribution. -/
def IsPseudorandomForKQueryAlgorithms (n k : ℕ) (mu : (Fin n → Bool) → ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (E : Finset ((Fin n × Bool) × W)),
    IsUnitaryCircuit C → Normalized ψ → QueryCount C ≤ k →
      distinguishingAdvantage n mu
        (fun x => MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E) = 0

private theorem boolean_cube_true_card (n : ℕ) (S : Finset (Fin n)) :
    (Finset.univ.filter (fun x : Fin n → Bool => ∀ i ∈ S, x i = true)).card =
      2 ^ (n - S.card) := by
  classical
  let e : {x : Fin n → Bool // ∀ i ∈ S, x i = true} ≃
      ((Finset.univ \ S : Finset (Fin n)) → Bool) :=
    { toFun := fun x i => x.1 i.1
      invFun := fun y => ⟨fun i => if hi : i ∈ S then true else y ⟨i, by simp [hi]⟩,
        fun i hi => by simp [hi]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi, x.2 i hi]
        · simp [hi]
      right_inv := by
        intro y
        funext i
        have hi : i.1 ∉ S := (Finset.mem_sdiff.mp i.2).2
        simp [hi] }
  calc
    _ = Fintype.card {x : Fin n → Bool // ∀ i ∈ S, x i = true} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card ((Finset.univ \ S : Finset (Fin n)) → Bool) :=
      Fintype.card_congr e
    _ = 2 ^ (n - S.card) := by simp

private theorem uniform_true_moment (n : ℕ) (S : Finset (Fin n)) :
    (∑ x : Fin n → Bool,
      uniformWeight n * (if ∀ i ∈ S, x i = true then (1 : ℝ) else 0)) =
      (1 / 2 : ℝ) ^ S.card := by
  classical
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => ∀ i ∈ S, x i = true),
        uniformWeight n := by
      simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
    _ = (2 : ℝ) ^ (n - S.card) * (1 / 2 : ℝ) ^ n := by
      rw [Finset.sum_const, nsmul_eq_mul, boolean_cube_true_card]
      simp [uniformWeight]
    _ = (1 / 2 : ℝ) ^ S.card := by
      have hcancel : (2 : ℝ) ^ (n - S.card) * (1 / 2 : ℝ) ^ (n - S.card) = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (2 : ℝ) ^ (n - S.card) *
            ((1 / 2 : ℝ) ^ (n - S.card) * (1 / 2 : ℝ) ^ S.card) := by
          rw [← pow_add, Nat.sub_add_cancel hS]
        _ = _ := by rw [← mul_assoc, hcancel, one_mul]

private theorem independent_polynomial_average (n t : ℕ) (mu : (Fin n → Bool) → ℝ)
    (hmu : IsKWiseIndependent n t mu) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ t)
    (hmulti : ∀ d ∈ p.support, ∀ i, d i ≤ 1) :
    (∑ x : Fin n → Bool, mu x * MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) =
      uniformAverage n (fun x => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) := by
  classical
  have heval (x : Fin n → Bool) :
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p =
        ∑ d ∈ p.support, p.coeff d *
          (if ∀ i ∈ d.support, x i = true then (1 : ℝ) else 0) := by
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun d hd => congrArg (p.coeff d * ·) ?_
    calc
      _ = ∏ i ∈ d.support, (if x i then (1 : ℝ) else 0) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hdi : d i = 1 := by
          have hne := Finsupp.mem_support_iff.mp hi
          have hle := hmulti d hd i
          omega
        simp [hdi]
      _ = _ := by
        rw [Finset.prod_boole]
        split_ifs <;> rfl
  unfold uniformAverage
  simp_rw [heval, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hcard : d.support.card ≤ t := by
    calc
      d.support.card = ∑ i ∈ d.support, 1 := by simp
      _ ≤ ∑ i ∈ d.support, d i := by
        exact Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr
          (Finsupp.mem_support_iff.mp hi)
      _ = d.sum (fun _ e => e) := rfl
      _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd
      _ ≤ t := hp
  have hmoment : (∑ x : Fin n → Bool,
      mu x * (if ∀ i ∈ d.support, x i = true then (1 : ℝ) else 0)) =
        (1 / 2 : ℝ) ^ d.support.card := by
    simpa [Finset.sum_filter] using hmu.2.2 d.support hcard (fun _ => true)
  calc
    _ = p.coeff d * (∑ x : Fin n → Bool,
        mu x * (if ∀ i ∈ d.support, x i = true then (1 : ℝ) else 0)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    _ = p.coeff d * (1 / 2 : ℝ) ^ d.support.card := by rw [hmoment]
    _ = p.coeff d * (∑ x : Fin n → Bool,
        uniformWeight n * (if ∀ i ∈ d.support, x i = true then (1 : ℝ) else 0)) := by
      rw [uniform_true_moment]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring

/-- **Proposition 26 (Polynomial method applied to the distinguishing problem)**
(arXiv:2508.08852v1, printed p. 13).  If `μ` is a `2k`-wise independent
distribution over `{0,1}^n`, then `μ` is pseudorandom for all quantum algorithms
making at most `k` queries. -/
theorem proposition26_distinguishing (n k : ℕ) (mu : (Fin n → Bool) → ℝ)
    (hmu : IsKWiseIndependent n (2 * k) mu) :
    IsPseudorandomForKQueryAlgorithms n k mu := by
  classical
  intro W instF instD C ψ E hU hN hQ
  obtain ⟨hdegree, hmulti, heval⟩ :=
    acceptance_boolean_multilinearization_preserves_run C ψ E
  have havg := independent_polynomial_average n (2 * k) mu hmu
    (booleanAcceptancePolynomial C ψ E) (hdegree.trans (Nat.mul_le_mul_left 2 hQ))
    (fun d hd => hmulti d (MvPolynomial.mem_support_iff.mp hd))
  have havg_run : (∑ x : Fin n → Bool,
      mu x * MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E) =
        uniformAverage n
          (fun x => MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E) := by
    simpa only [heval, workspaceBitOracle] using havg
  have hone := measureProb_univ
    (hU.normalized_run (workspaceBitOracle_unitary (W := W) (fun _ : Fin n => false)) hN)
  calc
    _ = distinguishingAdvantage n mu
        (fun x => MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E) *
          MeasureProb (Run (workspaceBitOracle (W := W) (fun _ : Fin n => false)) C ψ)
            Finset.univ := by rw [hone, mul_one]
    _ = 0 := by simp only [distinguishingAdvantage, havg_run, sub_self, abs_zero, zero_mul]

end Qatlib.Papers.QQueryIntro25.MainResults
