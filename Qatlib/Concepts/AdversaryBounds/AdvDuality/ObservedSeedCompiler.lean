/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedHiddenMixture
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedPurification
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Compiling finite random seeds into observed circuits

The circuit `seedObservedProgram` measures a seed register and executes the corresponding
observed circuit on the data register. The input `seedObservedInput` encodes a finite
distribution using square-root amplitudes, as in the measurement formalism of
[NielsenChuang2010].

The event and expected-query identities recover the distribution-weighted behavior of the
original circuit family, while preserving well-formedness and the maximum query budget.

## Main statements

* `seedObservedProgram_event`: Event mass equals the weighted sum of branch event masses.
* `seedObservedProgram_expected`: Expected queries equal the weighted sum of branch
  expectations.
* `seedObservedProgram_budget`: The compiled query budget is the supremum of the seed budgets.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*} [Fintype I] [DecidableEq I] {s : ℕ}

/-- An observed circuit that measures the seed register and runs the selected circuit, lifted to
preserve that register. -/
noncomputable def seedObservedProgram (P : Fin s → ObservedCircuit I) :
    ObservedCircuit (I × Fin s) :=
  .measure s (fun x => x.2)
    (fun j => liftObservedEnvironment (E := Fin s) (P j))

/-- The tensor product of `psi` with a seed state whose amplitudes are the square roots of the
probabilities in `p`. -/
noncomputable def seedObservedInput (p : FinDist (Fin s)) (psi : QState I) :
    QState (I × Fin s) :=
  TensorState psi (fun j => (Real.sqrt (p.prob j) : ℂ))

/-- Interprets the first recorded outcome as a seed and applies its event predicate to the
remaining record; missing or out-of-range seeds give `false`. -/
def seedObservedEvent (E : Fin s → Bool → List (ℕ × ℕ) → Bool)
    (acc : Bool) (rec : List (ℕ × ℕ)) : Bool :=
  match rec with
  | [] => false
  | (_, j) :: rest => if h : j < s then E ⟨j, h⟩ acc rest else false

/-- The query budget of the seed-selected circuit is the supremum of the budgets of its
component circuits. -/
theorem seedObservedProgram_budget (P : Fin s → ObservedCircuit I) :
    observedQueryBudget (seedObservedProgram P) =
      Finset.univ.sup (fun j => observedQueryBudget (P j)) := by
  simp only [seedObservedProgram, observedQueryBudget, liftObservedEnvironment_budget]

/-- Selecting among well-formed observed circuits by a seed measurement produces a well-formed
observed circuit. -/
theorem seedObservedProgram_wellFormed (P : Fin s → ObservedCircuit I)
    (hP : ∀ j, observedWellFormed (P j)) :
    observedWellFormed (seedObservedProgram P) :=
  fun j => liftObservedEnvironment_wellFormed (P j) (hP j)

/-- The squared complex norm of the square-root amplitude for seed `j` is its probability under
`p`. -/
private theorem seed_sqrt_mass (p : FinDist (Fin s)) (j : Fin s) :
    Complex.normSq (Real.sqrt (p.prob j) : ℂ) = p.prob j := by
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (p.nonneg j)]

/-- Attaching the square-root seed state to a normalized data state preserves normalization. -/
theorem seedObservedInput_normalized (p : FinDist (Fin s)) (psi : QState I)
    (hpsi : Normalized psi) : Normalized (seedObservedInput p psi) := by
  apply normalized_tensorState hpsi
  change (∑ j, ‖(Real.sqrt (p.prob j) : ℂ)‖ ^ 2) = 1
  simpa only [← Complex.normSq_eq_norm_sq, seed_sqrt_mass] using p.sum_one

/-- A hidden-table oracle with the same matrix in every seed block equals that matrix tensored
with the identity on the seed register. -/
private theorem seed_hiddenOracle (O : Matrix I I ℂ) :
    hiddenTableOracle (fun _ : Fin s => O) = TensorGate O (1 : Operator s) := by
  funext x y
  rcases x with ⟨i, a⟩
  rcases y with ⟨k, b⟩
  by_cases h : a = b <;>
    simp [hiddenTableOracle, tensorGate_apply, Matrix.one_apply, h]

/-- Collapsing the input to seed `j` leaves `psi` tensored with the seed basis vector weighted
by the square root of `p.prob j`. -/
private theorem seed_input_collapse (p : FinDist (Fin s)) (psi : QState I)
    (j : Fin s) :
    Collapse (seedObservedInput p psi)
        (Finset.univ.filter (fun x : I × Fin s => x.2 = j)) =
      TensorState psi (fun a => if a = j then (Real.sqrt (p.prob j) : ℂ) else 0) := by
  funext x
  rcases x with ⟨i, a⟩
  by_cases h : a = j
  · subst a
    simp [collapse_apply, seedObservedInput, TensorState]
  · simp [collapse_apply, seedObservedInput, TensorState, h]

/-- The squared norm of a seed amplitude supported only at `j` is `p.prob j` at `j` and zero
elsewhere. -/
private theorem seed_selected_mass (p : FinDist (Fin s)) (j a : Fin s) :
    Complex.normSq (if a = j then (Real.sqrt (p.prob j) : ℂ) else 0) =
      if a = j then p.prob j else 0 := by
  by_cases h : a = j <;> simp only [h, reduceIte, seed_sqrt_mass, map_zero]

/-- A record beginning with the valid seed outcome `(s, j.val)` evaluates to the event for `j`
on the remaining record. -/
private theorem seed_event_cons (E : Fin s → Bool → List (ℕ × ℕ) → Bool)
    (j : Fin s) (acc : Bool) (rec : List (ℕ × ℕ)) :
    seedObservedEvent E acc ((s, j.val) :: rec) = E j acc rec := by
  simp [seedObservedEvent, j.isLt]

/-- The compiled event mass equals the sum of the component event masses weighted by `p`, with
the oracle acting trivially on the seed register. -/
theorem seedObservedProgram_event (p : FinDist (Fin s)) (O : Matrix I I ℂ)
    (P : Fin s → ObservedCircuit I) (psi : QState I)
    (E : Fin s → Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass (TensorGate O (1 : Operator s)) (seedObservedProgram P)
      (seedObservedInput p psi) (fun t => seedObservedEvent E t.accepted t.outcomes) =
      ∑ j, p.prob j * observedEventMass O (P j) psi
        (fun t => E j t.accepted t.outcomes) := by
  simp only [seedObservedProgram, observedEventMass, observedTraces,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  change observedEventMass (TensorGate O (1 : Operator s))
    (liftObservedEnvironment (E := Fin s) (P j))
    (Collapse (seedObservedInput p psi)
      (Finset.univ.filter (fun x : I × Fin s => x.2 = j)))
    (fun t => seedObservedEvent E t.accepted ((s, j.val) :: t.outcomes)) =
    p.prob j * observedEventMass O (P j) psi (fun t => E j t.accepted t.outcomes)
  simp only [seed_event_cons]
  rw [seed_input_collapse]
  have h := observed_hiddenTable_event_average (fun _ : Fin s => O) (P j) psi
    (fun a => if a = j then (Real.sqrt (p.prob j) : ℂ) else 0)
    (fun accepted outcomes => E j accepted outcomes)
  rw [seed_hiddenOracle] at h
  simpa [seed_selected_mass, ite_mul] using h

/-- The expected query count of the compiled circuit equals the `p`-weighted sum of the
component expected query counts. -/
theorem seedObservedProgram_expected (p : FinDist (Fin s)) (O : Matrix I I ℂ)
    (P : Fin s → ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries (TensorGate O (1 : Operator s)) (seedObservedProgram P)
      (seedObservedInput p psi) =
      ∑ j, p.prob j * expectedObservedQueries O (P j) psi := by
  simp only [seedObservedProgram, expectedObservedQueries_eq_sum, observedTraces,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  have h := observed_hiddenTable_expected_average (fun _ : Fin s => O) (P j) psi
    (fun a => if a = j then (Real.sqrt (p.prob j) : ℂ) else 0)
  rw [seed_hiddenOracle] at h
  have hbranch : expectedObservedQueries (TensorGate O (1 : Operator s))
      (liftObservedEnvironment (E := Fin s) (P j))
      (Collapse (seedObservedInput p psi)
        (Finset.univ.filter (fun x : I × Fin s => x.2 = j))) =
      p.prob j * expectedObservedQueries O (P j) psi := by
    rw [seed_input_collapse]
    simpa [seed_selected_mass, ite_mul] using h
  simpa only [expectedObservedQueries_eq_sum] using hbranch

end Qatlib.Concepts.AdversaryBounds.AdvDuality
