/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Filtered Gram bounds for bit queries

Proves that a bit oracle call changes the Gram matrix of normalized states by a filtered
certificate of budget two. Summing these certificates along a unitary circuit gives a budget of
twice its query count [LeeEtAl2011].

The final theorem only requires the circuit output to have the target Gram matrix, so it also
covers conversion specified by equality of pairwise output inner products.

## Main statements

* `gram_one_query_filteredCert`: gives the budget-two certificate for a bit query.
* `gram_exact_state_conversion_filteredCert`: bounds target Gram change by twice the query
  count.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools

open Matrix

/-- Simultaneously XOR-flipping the Boolean coordinate of two state slices preserves their inner
product. -/
private theorem gram_query_slice_flip_inner {R : ℕ} (a b : QState (Bool × Fin R))
    (c : Bool) :
    (star (fun bw : Bool × Fin R => a (bw.1 ^^ c, bw.2)) ⬝ᵥ
      (fun bw : Bool × Fin R => b (bw.1 ^^ c, bw.2))) = star a ⬝ᵥ b := by
  cases c <;> simp [dotProduct, Fintype.sum_prod_type, add_comm]

/-- XOR-flipping a state slice's Boolean coordinate preserves its total squared amplitude. -/
private theorem gram_query_slice_flip_mass {R : ℕ} (a : QState (Bool × Fin R))
    (c : Bool) :
    (∑ bw : Bool × Fin R, Complex.normSq (a (bw.1 ^^ c, bw.2))) =
      ∑ bw, Complex.normSq (a bw) := by
  cases c <;> simp [Fintype.sum_prod_type, add_comm]

/-- One workspace bit oracle call on normalized states yields a filtered Gram difference
certificate with budget two, as in [Lee et al., Lemma 4.7][LeeEtAl2011]. -/
theorem gram_one_query_filteredCert {X : Type} [Fintype X] [DecidableEq X]
    {n R : ℕ} (input : X → Fin n → Bool)
    {ψ : X → QState ((Fin n × Bool) × Fin R)} (hψ : ∀ x, Normalized (ψ x)) :
    gramFilteredCert
      (gramStateMatrix ψ - gramStateMatrix
        (fun x => ApplyGate (workspaceBitOracle (W := Fin R) (input x)) (ψ x)))
      (gramFilterDelta input) 2 := by
  classical
  let a (j : Fin n) (x : X) (bw : Bool × Fin R) := ψ x ((j, bw.1), bw.2)
  let b (j : Fin n) (x : X) (bw : Bool × Fin R) :=
    a j x (bw.1 ^^ input x j, bw.2)
  have hmass (x : X) : (∑ j, ∑ bw, Complex.normSq (a j x bw)) = 1 := by
    simpa only [Normalized, Complex.normSq_eq_norm_sq, a, Fintype.sum_prod_type]
      using hψ x
  have hflip (j : Fin n) (x : X) :
      (∑ bw, Complex.normSq (b j x bw)) = ∑ bw, Complex.normSq (a j x bw) :=
    gram_query_slice_flip_mass (a j x) (input x j)
  refine ⟨(Bool × Fin R) ⊕ (Bool × Fin R), inferInstance,
    fun j x => Sum.elim (a j x) (b j x),
    fun j y => Sum.elim (a j y) (fun bw => -b j y bw), ?_, ?_, ?_⟩
  · intro x
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      hflip, Finset.sum_add_distrib, hmass]
    norm_num
  · intro y
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Complex.normSq_neg, hflip, Finset.sum_add_distrib, hmass]
    norm_num
  · intro x y
    have hslot (j : Fin n) :
        gramFilterDelta input j x y *
          (star (Sum.elim (a j x) (b j x)) ⬝ᵥ
            Sum.elim (a j y) (fun bw => -b j y bw)) =
          star (a j x) ⬝ᵥ a j y - star (b j x) ⬝ᵥ b j y := by
      simp only [dotProduct, Pi.star_apply, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, mul_neg, Finset.sum_neg_distrib]
      by_cases he : input x j = input y j
      · have hi : star (b j x) ⬝ᵥ b j y = star (a j x) ⬝ᵥ a j y := by
          dsimp only [b]
          rw [← he]
          exact gram_query_slice_flip_inner (a j x) (a j y) (input x j)
        simp only [dotProduct, Pi.star_apply, RCLike.star_def] at hi
        simp [gramFilterDelta, he, hi]
      · simp [gramFilterDelta, he, sub_eq_add_neg]
    simp_rw [hslot]
    simp only [Matrix.sub_apply, gramStateMatrix, Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply,
      Fintype.sum_prod_type, applyGate_workspaceBitOracle_mk, Finset.sum_sub_distrib,
      a, b]

/-- A unitary bit-query circuit acting on normalized states yields a filtered Gram difference
certificate with budget twice its query count. -/
private theorem gram_run_filteredCert {X : Type} [Fintype X] [DecidableEq X]
    {n R : ℕ} (input : X → Fin n → Bool)
    (C : Circuit ((Fin n × Bool) × Fin R)) (hC : IsUnitaryCircuit C)
    (ρ : X → QState ((Fin n × Bool) × Fin R)) (hρ : ∀ x, Normalized (ρ x)) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix
      (fun x => Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)))
      (gramFilterDelta input) (2 * QueryCount C) := by
  induction C generalizing ρ with
  | nil => simpa using gramFilteredCert_zero (gramFilterDelta input) (by norm_num : (0 : ℝ) ≤ 0)
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      have hg : gramStateMatrix (fun x => ApplyGate U (ρ x)) = gramStateMatrix ρ := by
        ext x y
        exact inner_applyGate hU (ρ x) (ρ y)
      simpa only [run_gate, queryCount_gate, hg] using
        ih hC' (fun x => ApplyGate U (ρ x)) (fun x => normalized_applyGate hU (hρ x))
    | query =>
      have hC' := (isUnitaryCircuit_query C).mp hC
      have hn (x : X) := normalized_applyGate (workspaceBitOracle_unitary (input x)) (hρ x)
      have h := gramFilteredCert_add (gram_one_query_filteredCert input hρ)
        (ih hC' (fun x => ApplyGate (workspaceBitOracle (W := Fin R) (input x)) (ρ x)) hn)
      have hm : ∀ (A B D : Matrix X X ℂ), (A - B) + (B - D) = A - D := by
        intros; abel
      have hw : (2 : ℝ) + 2 * QueryCount C = 2 * (QueryCount C + 1 : ℕ) := by
        push_cast
        ring
      rw [hw] at h
      simpa only [hm, run_query, queryCount_query] using h

/-- If a unitary circuit with `T` queries has the target family's pairwise output inner
products, then the initial-to-target Gram difference has a filtered certificate with budget
`2*T` [LeeEtAl2011]. -/
theorem gram_exact_state_conversion_filteredCert {X : Type} [Fintype X] [DecidableEq X]
    {n R T : ℕ} (input : X → Fin n → Bool)
    (ρ σ : X → QState ((Fin n × Bool) × Fin R))
    (C : Circuit ((Fin n × Bool) × Fin R))
    (hT : QueryCount C = T) (hC : IsUnitaryCircuit C) (hρ : ∀ x, Normalized (ρ x))
    (hexact : ∀ x y, Qatlib.Foundations.PureStateMath.Inner (Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x))
      (Run (workspaceBitOracle (W := Fin R) (input y)) C (ρ y)) = Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y)) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (gramFilterDelta input) (2 * T) := by
  have hg : gramStateMatrix
      (fun x => Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)) = gramStateMatrix σ := by
    ext x y
    exact hexact x y
  simpa only [hg, hT] using gram_run_filteredCert input C hC ρ hρ

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
