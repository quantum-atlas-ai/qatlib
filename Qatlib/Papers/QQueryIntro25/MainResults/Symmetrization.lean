/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QQueryIntro25.MainResults.SourceModel
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

set_option backward.isDefEq.respectTransparency false

/-!
# Minsky-Papert Symmetrization and Approximate-Degree Query Lower Bounds

This module formalizes Section 3.3, Propositions 27, 28, and 29 of Hamoudi on
Minsky-Papert univariate symmetrization of Boolean polynomials and the resulting
bounded-error approximate-degree and quantum query lower bounds for `Parity`
(`deg̃ = n`, `Q ≥ n / 2`) and `OR_n` (`deg̃ ≥ √(n / 6)`, `Q ≥ √(n / 24)`).

## Main statements

* `prop27_symmetrization`: Proposition 27, univariate layer-average polynomial of
  degree at most `totalDegree p`.
* `prop28_parity_approx_degree`, `prop28_parity_query_lower_bound`: Proposition 28,
  `approxDegree (Parity I) = |I|` and `Q(Parity) ≥ |I| / 2`.
* `prop29_or_approx_degree`, `prop29_or_query_lower_bound`: Proposition 29,
  `√(n / 6) ≤ approxDegree (ORn n)` and `√(n / 24) ≤ T` for `T`-query `OR_n`.

## References

* [Hamoudi, 2025][Hamoudi2025QueryIntro], Section 3.3, Propositions 27--29, pp. 13--15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QQueryIntro25.MainResults

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.QueryWordCore.Circuit

open Matrix
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Proposition 27 (Minsky–Papert symmetrization)** (arXiv:2508.08852v1, printed
p. 13).  Let `p` be a multilinear polynomial on `n` Boolean variables.  Then there
is a univariate polynomial `q` with `q(k) = E_{|x| = k}[p(x)]` for every integer
`k ∈ {0, …, n}` and `natDegree q ≤ totalDegree p`.

Bridge to the library theorem `symmetrizationAverageSubgoal` (FQN
`Qatlib.Concepts.QueryComplexity.DegreeMethod.symmetrizationAverageSubgoal`),
which proves exactly this statement with `layerAverage p k` in place of the
expectation over the weight-`k` layer. -/
theorem prop27_symmetrization {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) :
    ∃ q : Polynomial ℝ,
      (∀ k : ℕ, k ≤ Fintype.card I → layerAverage p k = q.eval (k : ℝ)) ∧
        q.natDegree ≤ p.totalDegree :=
  symmetrizationAverageSubgoal I p

/-- **Proposition 28, degree half (Symmetrization method applied to Parity)**
(arXiv:2508.08852v1, printed p. 14).  The approximate degree of Parity on `n`
bits equals `n`. -/
theorem prop28_parity_approx_degree {I : Type} [Fintype I] [DecidableEq I] :
    approxDegree (Parity I) = Fintype.card I := by
  let pParity : MvPolynomial I ℝ := MvPolynomial.C (1 / 2 : ℝ) *
    (1 - ∏ i : I, (1 - MvPolynomial.C (2 : ℝ) * MvPolynomial.X i))
  have heval (x : I → Bool) : boolEval pParity x = if Parity I x then 1 else 0 := by
    have hprod : (∏ i : I, (1 - 2 * (if x i then (1 : ℝ) else 0))) =
        (-1 : ℝ) ^ (Finset.univ.filter (fun i => x i = true)).card := by
      calc
        _ = ∏ i ∈ Finset.univ.filter (fun i => x i = true), (-1 : ℝ) := by
          rw [Finset.prod_filter]
          exact Finset.prod_congr rfl fun i _ => by cases x i <;> norm_num
        _ = _ := Finset.prod_const _
    simp only [boolEval, pParity, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_sub, map_one, MvPolynomial.eval_prod, MvPolynomial.eval_X, hprod]
    by_cases hx : (Finset.univ.filter (fun i => x i = true)).card % 2 = 1
    · rw [(Nat.odd_iff.mpr hx).neg_one_pow]
      norm_num [Parity, hx]
    · have heven : Even (Finset.univ.filter (fun i => x i = true)).card :=
        Nat.not_odd_iff_even.mp (fun hodd => hx (Nat.odd_iff.mp hodd))
      rw [heven.neg_one_pow]
      norm_num [Parity, hx]
  have happrox : ∀ x : I → Bool,
      |boolEval pParity x - (if Parity I x then (1 : ℝ) else 0)| ≤ 1 / 3 := by
    intro x
    rw [heval x, sub_self, abs_zero]
    norm_num
  have hfactor (i : I) :
      (1 - MvPolynomial.C (2 : ℝ) * MvPolynomial.X i : MvPolynomial I ℝ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
    simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C (2 : ℝ))
      (MvPolynomial.X i : MvPolynomial I ℝ)
  have hprodDegree :
      (∏ i : I, (1 - MvPolynomial.C (2 : ℝ) * MvPolynomial.X i) :
        MvPolynomial I ℝ).totalDegree ≤ Fintype.card I := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hfactor i)
  have hdegree : pParity.totalDegree ≤ Fintype.card I := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp only [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) hprodDegree)
  let S := (fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ x : I → Bool, |boolEval p x - (if Parity I x then (1 : ℝ) else 0)| ≤ 1 / 3}
  have hmem : pParity.totalDegree ∈ S := ⟨pParity, happrox, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hupper : approxDegree (Parity I) ≤ Fintype.card I :=
    (Nat.sInf_le hmem).trans hdegree
  obtain ⟨p, hp, hdeg⟩ := Nat.sInf_mem hne
  change p.totalDegree = approxDegree (Parity I) at hdeg
  apply le_antisymm hupper
  have hlower := parity_boolean_approximation_degree p (fun x => by
    simpa only [boolEval, Parity, decide_eq_true_eq] using hp x)
  rw [← hdeg]
  exact hlower

/-- **Proposition 28, query half (Symmetrization method applied to Parity)**
(arXiv:2508.08852v1, printed p. 14).  Any bounded-error quantum decision procedure
for Parity on the finite query alphabet `I` that makes at most `T` queries satisfies
`T ≥ |I|/2`.

Stated for one explicit `T`-query circuit (the paper's `Q(Parity) ≤ T` unpacked;
`SourceModel.QuantumQueryComplexityAtMost` is the packaged form of the same data).
The proof converts the `2/3`-correctness hypotheses into the `1/3`-approximation
hypothesis of the library theorem
`parity_actual_bounded_error_query_lower_bound` (FQN
`Qatlib.Concepts.QueryComplexity.DegreeMethod.parity_actual_bounded_error_query_lower_bound`)
and concludes `|I| ≤ 2 * QueryCount C ≤ 2 * T`. -/
theorem prop28_parity_query_lower_bound {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (E : Finset ((I × Bool) × W)) (T : ℕ)
    (hU : IsUnitaryCircuit C) (hN : Normalized ψ) (hQ : QueryCount C ≤ T)
    (hsucc : ∀ x : I → Bool, (2 / 3 : ℝ) ≤
      MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ)
        (if Parity I x then E else Eᶜ)) :
    (Fintype.card I : ℝ) / 2 ≤ (T : ℝ) := by
  -- Every run state is normalized, so its acceptance weight is at most `1` and
  -- complementary events split the weight.
  have hnorm : ∀ f : I → Bool, Normalized (Run (workspaceBitOracle (W := W) f) C ψ) :=
    fun f => hU.normalized_run (workspaceBitOracle_unitary f) hN
  have hcompl : ∀ f : I → Bool,
      MeasureProb (Run (workspaceBitOracle (W := W) f) C ψ) Eᶜ =
        1 - MeasureProb (Run (workspaceBitOracle (W := W) f) C ψ) E := by
    intro f
    have hunion := measureProb_union (Run (workspaceBitOracle (W := W) f) C ψ)
      (S := E) (T := Eᶜ) disjoint_compl_right
    rw [Finset.union_compl, measureProb_univ (hnorm f)] at hunion
    linarith
  have hbound : ∀ f : I → Bool,
      |MeasureProb (Run (workspaceBitOracle (W := W) f) C ψ) E -
        (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then
          (1 : ℝ) else 0)| ≤ 1 / 3 := by
    intro f
    have hs := hsucc f
    rw [show (if Parity I f then E else Eᶜ) =
        (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then E else Eᶜ) by
      simp [Parity]] at hs
    have hle1 := measureProb_le_one (hnorm f) E
    have hnn := measureProb_nonneg (Run (workspaceBitOracle (W := W) f) C ψ) E
    by_cases hf : (Finset.univ.filter (fun i => f i = true)).card % 2 = 1
    · simp only [hf, ↓reduceIte] at hs ⊢
      rw [abs_le]
      constructor <;> linarith
    · simp only [hf, ↓reduceIte] at hs ⊢
      rw [hcompl f] at hs
      rw [abs_le]
      constructor <;> linarith
  have hcard : Fintype.card I ≤ 2 * QueryCount C :=
    parity_actual_bounded_error_query_lower_bound (W := W) C ψ E hU hN hbound
  have hcast : (Fintype.card I : ℝ) ≤ 2 * (QueryCount C : ℝ) := by
    exact_mod_cast hcard
  have hle : (QueryCount C : ℝ) ≤ (T : ℝ) := by exact_mod_cast hQ
  linarith

/-- **Proposition 29, degree half (Symmetrization method applied to OR)**
(arXiv:2508.08852v1, printed p. 15).  The approximate degree of OR on `n` bits is
at least `√(n/6)`. -/
theorem prop29_or_approx_degree (n : ℕ) :
    Real.sqrt ((n : ℝ) / 6) ≤ (approxDegree (ORn n) : ℝ) := by
  let pOR : MvPolynomial (Fin n) ℝ := 1 - ∏ i : Fin n, (1 - MvPolynomial.X i)
  have heval (x : Fin n → Bool) : boolEval pOR x = if ORn n x then 1 else 0 := by
    simp only [boolEval, pOR, MvPolynomial.eval_sub, map_one, MvPolynomial.eval_prod,
      MvPolynomial.eval_X]
    by_cases hx : ∃ i : Fin n, x i = true
    · obtain ⟨i, hi⟩ := hx
      have hz : (∏ j : Fin n, (1 - (if x j then (1 : ℝ) else 0))) = 0 := by
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      simp [ORn, show ∃ j : Fin n, x j = true from ⟨i, hi⟩, hz]
    · have hall (i : Fin n) : x i = false := Bool.eq_false_iff.mpr (fun hi => hx ⟨i, hi⟩)
      simp [ORn, hall]
  let S := (fun p : MvPolynomial (Fin n) ℝ => p.totalDegree) ''
    {p | ∀ x : Fin n → Bool, |boolEval p x - (if ORn n x then (1 : ℝ) else 0)| ≤ 1 / 3}
  have hne : S.Nonempty := by
    refine ⟨pOR.totalDegree, pOR, ?_, rfl⟩
    intro x
    rw [heval x, sub_self, abs_zero]
    norm_num
  obtain ⟨p, hp, hdegree⟩ := Nat.sInf_mem hne
  change p.totalDegree = approxDegree (ORn n) at hdegree
  let q : MvPolynomial (Fin n) ℝ :=
    MvPolynomial.C (3 / 5 : ℝ) * p + MvPolynomial.C (1 / 5 : ℝ)
  have hqdegree : q.totalDegree ≤ p.totalDegree := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ (by simp))
    simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C (3 / 5 : ℝ)) p
  have hqeval (x : Fin n → Bool) : boolEval q x = (3 / 5 : ℝ) * boolEval p x + 1 / 5 := by
    simp [boolEval, q]
  have hq : ∀ x : Fin n → Bool,
      0 ≤ boolEval q x ∧ boolEval q x ≤ 1 ∧
        |boolEval q x - (if ORn n x then (1 : ℝ) else 0)| ≤ 2 / 5 := by
    intro x
    have hx := hp x
    rw [hqeval]
    cases hf : ORn n x <;> simp only [hf, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    all_goals
      obtain ⟨hlo, hhi⟩ := abs_le.mp hx
      refine ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hbs := approximatePolynomialBlockSensitivity n (ORn n) q (2 / 5)
    (by norm_num) (by norm_num) hq
  have hnbs : n ≤ blockSensitivity (ORn n) := by
    let B := Finset.univ.image (fun i : Fin n => ({i} : Finset (Fin n)))
    have hcard : B.card = n := by
      rw [Finset.card_image_of_injective _ Finset.singleton_injective]
      exact Fintype.card_fin n
    have hsensitive : ∀ b ∈ B, BlockSensitive (ORn n) (allZero n) b := by
      intro b hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      have hone : ORn n (flipBlock (allZero n) {i}) = true := by
        simp only [ORn, decide_eq_true_eq]
        exact ⟨i, by simp [flipBlock, allZero]⟩
      simp only [BlockSensitive, hone]
      simp [ORn, allZero]
    have hdisjoint : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → b₁ ∩ b₂ = ∅ := by
      intro b₁ hb₁ b₂ hb₂ hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb₁
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb₂
      have hij : i ≠ j := fun h => hne (congrArg (fun k : Fin n => ({k} : Finset (Fin n))) h)
      simp [hij]
    have hlocal : B.card ≤ blockSensitivityAt (ORn n) (allZero n) := by
      exact Finset.le_sup (f := Finset.card)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ B, hsensitive, hdisjoint⟩)
    have hglobal : blockSensitivityAt (ORn n) (allZero n) ≤ blockSensitivity (ORn n) := by
      exact Finset.le_sup (f := id) (Finset.mem_image.mpr
        ⟨allZero n, Finset.mem_univ _, rfl⟩)
    calc n = B.card := hcard.symm
      _ ≤ blockSensitivityAt (ORn n) (allZero n) := hlocal
      _ ≤ blockSensitivity (ORn n) := hglobal
  have hcast : (n : ℝ) ≤ (blockSensitivity (ORn n) : ℝ) := by exact_mod_cast hnbs
  have hsq : (q.totalDegree : ℝ) ^ 2 ≤ (p.totalDegree : ℝ) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast hqdegree)
  apply Real.sqrt_le_iff.mpr
  refine ⟨Nat.cast_nonneg _, ?_⟩
  rw [← hdegree]
  nlinarith

/-- **Proposition 29, query half (Symmetrization method applied to OR)**
(arXiv:2508.08852v1, printed p. 15).  Any bounded-error quantum decision procedure
for OR on `n` bits that makes at most `T` queries satisfies `T ≥ √(n/24)`. -/
theorem prop29_or_query_lower_bound (n : ℕ) (T : ℕ)
    (h : QuantumQueryComplexityAtMost (ORn n) T) :
    Real.sqrt ((n : ℝ) / 24) ≤ (T : ℝ) := by
  obtain ⟨W, instF, instD, instN, C, ψ, E, hU, hQ, hN, hsucc⟩ := h
  let _ := instF
  let _ := instD
  let _ := instN
  have hnorm (x : Fin n → Bool) : Normalized (Run (workspaceBitOracle (W := W) x) C ψ) :=
    hU.normalized_run (workspaceBitOracle_unitary x) hN
  have hcompl (x : Fin n → Bool) :
      MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) Eᶜ =
        1 - MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E := by
    have hunion := measureProb_union (Run (workspaceBitOracle (W := W) x) C ψ)
      (S := E) (T := Eᶜ) disjoint_compl_right
    rw [Finset.union_compl, measureProb_univ (hnorm x)] at hunion
    linarith
  have hbound (x : Fin n → Bool) :
      |MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ) E -
        (if ORn n x then (1 : ℝ) else 0)| ≤ 1 / 3 := by
    have hs := hsucc x
    have hle1 := measureProb_le_one (hnorm x) E
    have hnn := measureProb_nonneg (Run (workspaceBitOracle (W := W) x) C ψ) E
    cases hf : ORn n x <;> simp only [hf, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    · rw [hcompl x] at hs
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hdegree, _, heval⟩ :=
    Qatlib.Concepts.QueryWordCore.QueryMachinery.acceptance_boolean_multilinearization_preserves_run
      C ψ E
  have happrox : approxDegree (ORn n) ≤ 2 * T := by
    refine le_trans ?_ (hdegree.trans (Nat.mul_le_mul_left 2 hQ))
    apply Nat.sInf_le
    refine ⟨
      Qatlib.Concepts.QueryWordCore.QueryMachinery.booleanAcceptancePolynomial C ψ E,
      ?_, rfl⟩
    intro x
    simpa only [boolEval, heval x, workspaceBitOracle] using hbound x
  have hcast : (approxDegree (ORn n) : ℝ) ≤ 2 * (T : ℝ) := by exact_mod_cast happrox
  have hsqrt := prop29_or_approx_degree n
  have hnonneg : 0 ≤ (approxDegree (ORn n) : ℝ) := Nat.cast_nonneg _
  have hsquared := (Real.sqrt_le_iff.mp hsqrt).2
  apply Real.sqrt_le_iff.mpr
  refine ⟨Nat.cast_nonneg _, ?_⟩
  nlinarith

end Qatlib.Papers.QQueryIntro25.MainResults
