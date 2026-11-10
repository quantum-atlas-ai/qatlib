/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedSeedCompiler
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.ShadowModels.ShadowChannel


namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
variable {I : Type*} [Fintype I] [DecidableEq I] {s : ℕ}

noncomputable def seedDependentInput (p : FinDist (Fin s))
    (psi : Fin s → QState I) : QState (I × Fin s) :=
  fun x => psi x.2 x.1 * (Real.sqrt (p.prob x.2) : ℂ)

theorem seedDependentInput_const (p : FinDist (Fin s)) (psi : QState I) :
    seedDependentInput p (fun _ => psi) = seedObservedInput p psi := rfl

private theorem sqrt_mass (p : FinDist (Fin s)) (j : Fin s) :
    Complex.normSq (Real.sqrt (p.prob j) : ℂ) = p.prob j := by
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (p.nonneg j)]

theorem seedDependentInput_mass (p : FinDist (Fin s)) (psi : Fin s → QState I) :
    branchMass (seedDependentInput p psi) = ∑ j, p.prob j * branchMass (psi j) := by
  simp only [branchMass, MeasureProb, BornProb, seedDependentInput,
    Fintype.sum_prod_type, norm_mul, mul_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [show ‖(Real.sqrt (p.prob j) : ℂ)‖ ^ 2 = p.prob j from
    (Complex.normSq_eq_norm_sq _).symm.trans (sqrt_mass p j)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem seedDependentInput_normalized (p : FinDist (Fin s))
    (psi : Fin s → QState I) (hpsi : ∀ j, Normalized (psi j)) :
    Normalized (seedDependentInput p psi) := by
  change branchMass (seedDependentInput p psi) = 1
  rw [seedDependentInput_mass]
  simpa only [show ∀ j, branchMass (psi j) = 1 from hpsi, mul_one] using p.sum_one

private theorem input_collapse (p : FinDist (Fin s)) (psi : Fin s → QState I)
    (j : Fin s) :
    Collapse (seedDependentInput p psi)
      (Finset.univ.filter (fun x : I × Fin s => x.2 = j)) =
      TensorState (psi j) (fun a => if a = j then (Real.sqrt (p.prob j) : ℂ) else 0) := by
  funext x
  rcases x with ⟨i,a⟩
  by_cases h : a = j
  · subst a
    simp [collapse_apply, seedDependentInput, TensorState]
  · simp [collapse_apply, seedDependentInput, TensorState, h]

private theorem hiddenOracle (O : Matrix I I ℂ) :
    hiddenTableOracle (fun _ : Fin s => O) = TensorGate O (1 : Operator s) := by
  funext x y
  rcases x with ⟨i,a⟩
  rcases y with ⟨k,b⟩
  by_cases h : a = b <;>
    simp [hiddenTableOracle, tensorGate_apply, Matrix.one_apply, h]

private theorem selected_mass (p : FinDist (Fin s)) (j a : Fin s) :
    Complex.normSq (if a = j then (Real.sqrt (p.prob j) : ℂ) else 0) =
      if a = j then p.prob j else 0 := by
  by_cases h : a = j <;> simp only [h, reduceIte, sqrt_mass, map_zero]

private theorem event_cons (E : Fin s → Bool → List (ℕ × ℕ) → Bool)
    (j : Fin s) (acc : Bool) (rec : List (ℕ × ℕ)) :
    seedObservedEvent E acc ((s,j.val)::rec) = E j acc rec := by
  simp [seedObservedEvent,j.isLt]

theorem seedDependentInput_event (p : FinDist (Fin s)) (O : Matrix I I ℂ)
    (P : Fin s → ObservedCircuit I) (psi : Fin s → QState I)
    (E : Fin s → Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass (TensorGate O (1 : Operator s)) (seedObservedProgram P)
      (seedDependentInput p psi) (fun t => seedObservedEvent E t.accepted t.outcomes) =
      ∑ j, p.prob j * observedEventMass O (P j) (psi j)
        (fun t => E j t.accepted t.outcomes) := by
  simp only [seedObservedProgram, observedEventMass, observedTraces,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  change observedEventMass (TensorGate O (1 : Operator s))
    (liftObservedEnvironment (E := Fin s) (P j))
    (Collapse (seedDependentInput p psi)
      (Finset.univ.filter (fun x : I × Fin s => x.2 = j)))
    (fun t => seedObservedEvent E t.accepted ((s,j.val)::t.outcomes)) =
    p.prob j * observedEventMass O (P j) (psi j) (fun t => E j t.accepted t.outcomes)
  simp only [event_cons]
  rw [input_collapse]
  have h := observed_hiddenTable_event_average (fun _ : Fin s => O) (P j) (psi j)
    (fun a => if a = j then (Real.sqrt (p.prob j) : ℂ) else 0)
    (fun accepted outcomes => E j accepted outcomes)
  rw [hiddenOracle] at h
  simpa [selected_mass,ite_mul] using h

theorem seedDependentInput_expected (p : FinDist (Fin s)) (O : Matrix I I ℂ)
    (P : Fin s → ObservedCircuit I) (psi : Fin s → QState I) :
    expectedObservedQueries (TensorGate O (1 : Operator s)) (seedObservedProgram P)
      (seedDependentInput p psi) =
      ∑ j, p.prob j * expectedObservedQueries O (P j) (psi j) := by
  simp only [seedObservedProgram, expectedObservedQueries_eq_sum, observedTraces,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  have h := observed_hiddenTable_expected_average (fun _ : Fin s => O) (P j) (psi j)
    (fun a => if a = j then (Real.sqrt (p.prob j) : ℂ) else 0)
  rw [hiddenOracle] at h
  have hbranch : expectedObservedQueries (TensorGate O (1 : Operator s))
      (liftObservedEnvironment (E := Fin s) (P j))
      (Collapse (seedDependentInput p psi)
        (Finset.univ.filter (fun x : I × Fin s => x.2 = j))) =
      p.prob j * expectedObservedQueries O (P j) (psi j) := by
    rw [input_collapse]
    simpa [selected_mass,ite_mul] using h
  simpa only [expectedObservedQueries_eq_sum] using hbranch
end Qatlib.Concepts.AdversaryBounds.AdvDuality
