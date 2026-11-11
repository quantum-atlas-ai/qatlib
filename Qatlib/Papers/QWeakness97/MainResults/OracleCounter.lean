/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceMarkSetHybrid

/-!
# Oracle-port constant and query-clock counterexamples

This module records two explicit Boolean XOR-oracle computations that check the constants and
clock convention when comparing finite query circuits with Theorem 3.3 and Corollary 3.4 of
[BennettEtAl1997]. `OracleConstantCounter` uses a single basis-state query: its reference charge
is one, while changing the oracle answer gives squared final distance two.

`Cor34QueryClockCounter` uses a uniform four-address register and a minus-state answer bit.
Changing any one address gives squared final distance one, so the exceptional-set coefficient
two fails at tolerance `3/4` when time is counted as one oracle query. These are statements
about the actual XOR query primitive and its query clock.

## Main statements

* `OracleConstantCounter.printed_bound_fails` verifies the charge budget at tolerance one and
  the failure of the corresponding distance conclusion.
* `Cor34QueryClockCounter.actual_gap_squared` computes the squared gap for every address.
* `Cor34QueryClockCounter.no_bad_set` rules out the coefficient-two exceptional-set bound in the
  four-address example.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QWeakness97.MainResults
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
namespace OracleConstantCounter
/-- The one-address, one-answer-bit state space with a trivial workspace used for the
oracle-constant example. -/
abbrev R := ((Unit × Bool) × Unit)

/-- The circuit consisting of a single oracle query on the one-address state space. -/
def word : Circuit R := [.query]

/-- The basis state with the unique query address, a false answer bit, and the unique workspace
value. -/
def seed : QState R := Ket (((), false), ())

/-- Querying the constant Boolean oracle `b` from the basis seed produces the basis state whose
answer bit is `b`. -/
theorem run_one (b : Bool) :
    Run (workspaceBitOracle (W := Unit) (fun _ : Unit => b)) word seed =
      Ket (((), b), ()) := by
  funext p
  obtain ⟨⟨u,c⟩,w⟩ := p
  cases u; cases w; cases c <;> cases b <;>
    simp [word, seed, applyGate_workspaceBitOracle, Ket]

/-- The reference execution of the single-query example has total query charge exactly one at
its unique address. -/
theorem source_charge :
    ((oracleQueryInputs (fun _ : Unit => false) word seed).map
      (fun φ => MeasureProb φ (workspaceQueryFiber (W := Unit) ()))).sum = 1 := by
  simp [word, seed, oracleQueryInputs, workspaceQueryFiber, MeasureProb, BornProb, Ket,
    Fintype.sum_prod_type]

/-- The final states obtained from the constant true and constant false oracles in the
single-query example have squared Euclidean distance exactly two. -/
theorem actual_squared_gap :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun _ : Unit => true)) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Unit => false)) word seed)‖ ^ 2 = 2 := by
  rw [run_one, run_one, norm_toEuclidean_fromVec_sq]
  norm_num [Ket, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The normalized one-query XOR-oracle example satisfies the budget `ε^2 / T` at `ε = 1` but
has final distance greater than one. This verifies the oracle-port constant caveat when the
printed Theorem 3.3 budget of [BennettEtAl1997] is interpreted directly for this primitive. -/
theorem printed_bound_fails :
    QueryCount word = 1 ∧ IsUnitaryCircuit word ∧ Normalized seed ∧
    ((oracleQueryInputs (fun _ : Unit => false) word seed).map
      (fun φ => MeasureProb φ (workspaceQueryFiber (W := Unit) ()))).sum ≤
        (1 : ℝ)^2/(QueryCount word : ℝ) ∧
    ¬ ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun _ : Unit => true)) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Unit => false)) word seed)‖ ≤ 1 := by
  refine ⟨rfl, by simp [word], normalized_ket _, ?_, ?_⟩
  · rw [source_charge]; norm_num [word, QueryCount]
  · intro h
    have hn := norm_nonneg (toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun _ : Unit => true)) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Unit => false)) word seed))
    have hg := actual_squared_gap
    nlinarith
end OracleConstantCounter

open scoped BigOperators
namespace Cor34QueryClockCounter
/-- The four-address, one-answer-bit state space with trivial workspace used for the query-clock
exceptional-set example. -/
abbrev R := ((Fin 4 × Bool) × Unit)

/-- The tensor product of a uniform four-address state, a minus-state answer bit, and the unique
workspace basis state. -/
noncomputable def seed : QState R := TensorState (TensorState (Uniform (Fin 4)) Minus) (Ket ())

/-- The circuit consisting of a single oracle query on the four-address state space. -/
def word : Circuit R := [.query]

/-- The uniform-address, minus-answer seed has unit total Born probability. This verifies
normalization for the query-clock caveat accompanying Corollary 3.4 of [BennettEtAl1997]. -/
theorem seed_normalized : Normalized seed :=
  normalized_tensorState (normalized_tensorState (normalized_uniform (by decide)) normalized_minus)
    (normalized_ket ())

/-- Changing the false oracle to the oracle marked only at `y` changes the final amplitude by
`-2 * seed p` on configurations with address `y` and by zero at all other addresses. -/
theorem actual_difference (y : Fin 4) :
    Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
      Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed =
    fun p => if p.1.1 = y then (-2 : ℂ)*seed p else 0 := by
  funext p
  obtain ⟨⟨x,b⟩,u⟩ := p
  cases u; cases b <;> by_cases h : x=y <;>
    simp [word, applyGate_workspaceBitOracle, h, seed, TensorState, Minus, Hadamard] <;> ring

/-- For every one of the four addresses, changing only that address of the false oracle produces
final states with squared Euclidean distance exactly one. -/
theorem actual_gap_squared (y : Fin 4) :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed)‖^2 = 1 := by
  rw [actual_difference, norm_toEuclidean_fromVec_sq]
  have hc : ‖(Real.sqrt 2 : ℂ)⁻¹‖^2 = (1/2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hterm (p : R) :
      ‖(if p.1.1 = y then (-2 : ℂ)*seed p else 0)‖^2 =
        if p.1.1 = y then (1/2 : ℝ) else 0 := by
    obtain ⟨⟨x,b⟩,u⟩ := p
    cases u
    by_cases h : x=y
    · cases b <;> norm_num [h, seed, TensorState, Uniform, Minus, Hadamard, Ket,
        norm_mul, mul_pow, hc]
    · simp [h]
  simp_rw [hterm]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- At tolerance `3/4`, no exceptional set satisfies the bound `2 * T^2 / ε^2` for this
four-address, one-query example while controlling all remaining final-state distances. This
records the query-clock scope caveat for a direct XOR-oracle reading of Corollary 3.4 of
[BennettEtAl1997]. -/
theorem no_bad_set :
    ¬ ∃ S : Finset (Fin 4),
      (S.card : ℝ) ≤ 2*(QueryCount word : ℝ)^2/(3/4 : ℝ)^2 ∧
      ∀ y : Fin 4, y ∉ S →
        ‖toEuclidean_fromVec
          (Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
           Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed)‖ ≤ 3/4 := by
  rintro ⟨S,hcard,hgood⟩
  have hall : ∀ y : Fin 4, y ∈ S := by
    intro y
    by_contra h
    have hg := hgood y h
    have hsq := actual_gap_squared y
    have hnn := norm_nonneg (toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed))
    nlinarith
  have heq : S = Finset.univ := Finset.eq_univ_of_forall hall
  subst S
  norm_num [word, QueryCount] at hcard
end Cor34QueryClockCounter

end Qatlib.Papers.QWeakness97.MainResults
