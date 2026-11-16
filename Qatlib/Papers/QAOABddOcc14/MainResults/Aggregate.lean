/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.ClauseModel
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

@[expose] public section


/-!
# Closed finite aggregation support for Max-E3LIN2

Legacy commit d8d59743ce7eb006f4a072c0a266ff7ca628f31d, SourceMainResults;
arXiv:1412.6062v2, algebraic aggregation surrounding (27)--(35).
These nine declarations concern present clauses and finite sums of a supplied
polynomial family. Per-clause bounds and coefficient representation are
explicit local hypotheses. No QAOA-to-clause formula, Taylor theorem,
normalization, Chebyshev extremal bound, or typical-case claim is imported.
In particular the archived trigonometric functional is not identified with
an actual quantum expectation. The headline claims remain open.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QAOABddOcc14.MainResults

open scoped BigOperators
open Qatlib.Papers.QAOABddOcc14.MainResults

/-- The present clauses of an instance: the triples with `d_abc ≠ 0`. -/
def presentTriples {n : ℕ} (I : E3Instance n) : Finset (Triple n) :=
  Finset.univ.filter (fun p => I.d p ≠ 0)

/-- The number of equations is the number of present triples. -/
theorem presentCount {n : ℕ} (I : E3Instance n) :
    I.numEquations = (presentTriples I).card := rfl

/-- The aggregate odd polynomial `P^k = Σ_p P^k_p` of (35), over present clauses. -/
def aggPoly {n : ℕ} (I : E3Instance n) (P : Triple n → ℝ → ℝ) (γ : ℝ) : ℝ :=
  ∑ p ∈ presentTriples I, P p γ

/-- The aggregate remainder `R^k = Σ_p R^k_p` of (35), over present clauses. -/
def aggRemainder {n : ℕ} (I : E3Instance n) (P : Triple n → ℝ → ℝ) (γ : ℝ) : ℝ :=
  ∑ p ∈ presentTriples I, (clauseExpr I γ p - γ / 2 - P p γ)

/-- The aggregate `j`-th Taylor coefficient `Σ_p c_{p,j}`, over present clauses. -/
def aggCoeff {n : ℕ} (I : E3Instance n) (c : Triple n → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ presentTriples I, c p j

/-- An absent clause (`d_abc = 0`) has zero archived clause expression: the prefactor
`(1/8) d_abc` in (25) vanishes. -/
theorem clauseZero {n : ℕ} (I : E3Instance n) (γ : ℝ) (p : Triple n)
    (hd : I.d p = 0) : clauseExpr I γ p = 0 := by
  unfold clauseExpr
  simp [hd]

/-- **Source (34)–(35): the aggregate remainder bound.**  The per-clause bound
`|R^k_p| ≤ (9√D|γ|)^{k+2}` (34), valid for present clauses, sums over the `m`
present clauses to `|R^k| ≤ m (9√D|γ|)^{k+2}`. -/
theorem remainderBound {n : ℕ} (I : E3Instance n) (D : ℕ)
    (P : Triple n → ℝ → ℝ) (k : ℕ) (γ : ℝ)
    (hR : ∀ p : Triple n, I.d p ≠ 0 →
      |clauseExpr I γ p - γ / 2 - P p γ| ≤ (9 * Real.sqrt (D : ℝ) * |γ|) ^ (k + 2)) :
    |aggRemainder I P γ| ≤
      (I.numEquations : ℝ) * (9 * Real.sqrt (D : ℝ) * |γ|) ^ (k + 2) := by
  unfold aggRemainder presentTriples
  calc
    |∑ p ∈ Finset.univ.filter (fun p => I.d p ≠ 0),
        (clauseExpr I γ p - γ / 2 - P p γ)|
        ≤ ∑ p ∈ Finset.univ.filter (fun p => I.d p ≠ 0),
            |clauseExpr I γ p - γ / 2 - P p γ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Finset.univ.filter (fun p => I.d p ≠ 0),
            (9 * Real.sqrt (D : ℝ) * |γ|) ^ (k + 2) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hR p (Finset.mem_filter.mp hp).2
    _ = (I.numEquations : ℝ) * (9 * Real.sqrt (D : ℝ) * |γ|) ^ (k + 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          unfold E3Instance.numEquations
          ring

/-- **Source (27)–(35): the aggregate polynomial is a polynomial.**  Summing the
per-clause polynomials `P_p(γ) = Σ_{j≤k} c_{p,j} γ^j` gives
`P^k(γ) = Σ_{j≤k} (Σ_p c_{p,j}) γ^j`. -/
theorem polySum {n : ℕ} (I : E3Instance n) (P : Triple n → ℝ → ℝ)
    (c : Triple n → ℕ → ℝ) (k : ℕ)
    (hP : ∀ p γ, P p γ = ∑ j ∈ Finset.range (k + 1), c p j * γ ^ j) (γ : ℝ) :
    aggPoly I P γ = ∑ j ∈ Finset.range (k + 1), aggCoeff I c j * γ ^ j := by
  unfold aggPoly aggCoeff presentTriples
  calc
    (∑ p ∈ Finset.univ.filter (fun p => I.d p ≠ 0), P p γ)
        = ∑ p ∈ Finset.univ.filter (fun p => I.d p ≠ 0),
            ∑ j ∈ Finset.range (k + 1), c p j * γ ^ j :=
          Finset.sum_congr rfl (fun p _ => hP p γ)
    _ = ∑ j ∈ Finset.range (k + 1),
          ∑ p ∈ Finset.univ.filter (fun p => I.d p ≠ 0), c p j * γ ^ j :=
          Finset.sum_comm
    _ = ∑ j ∈ Finset.range (k + 1),
          (∑ p ∈ Finset.univ.filter (fun p => I.d p ≠ 0), c p j) * γ ^ j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]

/-- The aggregate coefficient inherits the support of the per-clause
coefficients: it is nonzero only at odd degrees `3,5,…,k` (27). -/
theorem coeffSupport {n : ℕ} (I : E3Instance n) (c : Triple n → ℕ → ℝ) (k : ℕ)
    (hc : ∀ p j, c p j ≠ 0 → Odd j ∧ 3 ≤ j ∧ j ≤ k) (j : ℕ)
    (hj : aggCoeff I c j ≠ 0) : Odd j ∧ 3 ≤ j ∧ j ≤ k := by
  have hex : ∃ p ∈ presentTriples I, c p j ≠ 0 := by
    by_contra h
    push Not at h
    apply hj
    unfold aggCoeff
    exact Finset.sum_eq_zero (fun p hp => h p hp)
  obtain ⟨p, _, hp⟩ := hex
  exact hc p j hp

end Qatlib.Papers.QAOABddOcc14.MainResults
