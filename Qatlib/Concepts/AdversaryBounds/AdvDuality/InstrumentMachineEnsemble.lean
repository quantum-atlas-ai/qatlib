/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachine
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.ENNReal.BigOperators

/-!
# Finite Ensembles of Instrument Machines

This module averages halting masses and expected query costs over a finite classical seed
distribution. Each seed may select its own instrument machine, initial control, initial density
operator, and event. The resulting mixture statistics fit the classical randomization of quantum
processes described in [NielsenChuang2010] and [Watrous2018].

The infinite ensemble statistics are finite weighted sums of the individual infinite statistics.
Monotonicity permits these sums to be expressed as suprema of common finite prefixes, yielding
uniform finite approximation and prefix characterizations of expected cost bounds.

## Main statements

* `instrumentMachineSeedInfiniteHaltMass_eq_iSup` identifies infinite ensemble halting mass with
  the supremum of finite ensemble masses.
* `instrumentMachineSeedHaltMass_finite_approx` gives a common prefix satisfying finitely many
  strict thresholds.
* `instrumentMachineSeedInfiniteExpectedQueries_eq_iSup` expresses infinite expected cost
  through common finite prefixes.
* `instrumentMachineSeedInfiniteExpectedQueries_le_iff` characterizes a bound by its
  finite-prefix counterparts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010], Quantum Computation and Quantum Information.
* [Watrous, 2018][Watrous2018], The Theory of Quantum Information.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Classical ComplexOrder ENNReal

/-- The finite-fuel halted-event mass averaged over a finite seed distribution, allowing the
machine, initial control, state, and event to depend on the seed. -/
noncomputable def instrumentMachineSeedHaltMass {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) : ℝ :=
  ∑ j, p.prob j * instrumentMachineHaltMass (M j) O T (c j) (rho j) (event j)

/-- The seed-weighted sum of infinite halted-event masses in extended nonnegative reals. -/
noncomputable def instrumentMachineSeedInfiniteHaltMass {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (p.prob j) *
    instrumentMachineInfiniteHaltMass (M j) O (c j) (rho j) (event j)

/-- The finite-fuel expected query cost averaged over the seed distribution. -/
noncomputable def instrumentMachineSeedExpectedQueries {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D) : ℝ :=
  ∑ j, p.prob j * instrumentMachineExpectedQueries (M j) O T (c j) (rho j)

/-- The seed-weighted sum of infinite expected query costs in extended nonnegative reals. -/
noncomputable def instrumentMachineSeedInfiniteExpectedQueries {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (p.prob j) *
    instrumentMachineInfiniteExpectedQueries (M j) O (c j) (rho j)

/-- A finite probability-weighted sum of suprema of nonnegative monotone real sequences equals
the supremum of their weighted sums at a common prefix. -/
private theorem seed_prefix_iSup {r : ℕ} (p : FinDist (Fin r))
    (f : Fin r → ℕ → ℝ) (hf : ∀ j T, 0 ≤ f j T) (hmono : ∀ j, Monotone (f j)) :
    (∑ j, ENNReal.ofReal (p.prob j) * ⨆ T, ENNReal.ofReal (f j T)) =
      ⨆ T, ENNReal.ofReal (∑ j, p.prob j * f j T) := by
  simp only [ENNReal.mul_iSup]
  have hm (j : Fin r) : Monotone (fun T : ℕ =>
      ENNReal.ofReal (p.prob j) * ENNReal.ofReal (f j T)) := by
    intro S T hST
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hmono j hST)) _
  rw [ENNReal.finsetSum_iSup_of_monotone (s := Finset.univ) hm]
  congr 1
  funext T
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.ofReal_mul (p.nonneg j)]
  · intro j _
    exact mul_nonneg (p.nonneg j) (hf j T)

/-- The seed-averaged finite halted-event mass is nonnegative when every initial state is
positive semidefinite. -/
theorem instrumentMachineSeedHaltMass_nonneg {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D)
    (hrho : ∀ j, (rho j).PosSemidef)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) :
    0 ≤ instrumentMachineSeedHaltMass p M O T c rho event :=
  Finset.sum_nonneg fun j _ => mul_nonneg (p.nonneg j)
    (instrumentMachineHaltMass_nonneg (M j) O T (c j) (rho j) (hrho j) (event j))

/-- For positive semidefinite initial states, seed-averaged halted-event mass is nondecreasing
in the common execution fuel. -/
theorem instrumentMachineSeedHaltMass_monotone {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) :
    Monotone (fun T => instrumentMachineSeedHaltMass p M O T c rho event) := by
  intro S T hST
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (instrumentMachineHaltMass_monotone (M j) O (c j) (rho j) (hrho j) (event j) hST)
    (p.nonneg j)

/-- The seed-averaged infinite halting mass equals the supremum of the seed-averaged finite
halting masses at common cutoffs, for positive semidefinite initial states. -/
theorem instrumentMachineSeedInfiniteHaltMass_eq_iSup {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) :
    instrumentMachineSeedInfiniteHaltMass p M O c rho event =
      ⨆ T : ℕ, ENNReal.ofReal (instrumentMachineSeedHaltMass p M O T c rho event) := by
  apply seed_prefix_iSup p
    (fun j T => instrumentMachineHaltMass (M j) O T (c j) (rho j) (event j))
    (fun j T => instrumentMachineHaltMass_nonneg (M j) O T (c j) (rho j) (hrho j) (event j))
    (fun j => instrumentMachineHaltMass_monotone (M j) O (c j) (rho j) (hrho j) (event j))

/-- Strict thresholds below the infinite seed-averaged halting masses for finitely many oracles
and events are all exceeded by one common finite execution prefix. -/
theorem instrumentMachineSeedHaltMass_finite_approx {D r : ℕ} {C J : Type*} [Fintype J]
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : J → Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef)
    (event : J → Fin r → C → Bool → List (ℕ×ℕ) → Bool)
    (threshold : J → ℝ≥0∞)
    (hthreshold : ∀ a, threshold a < instrumentMachineSeedInfiniteHaltMass
      p M (O a) c rho (event a)) :
    ∃ T : ℕ, ∀ a, threshold a < ENNReal.ofReal
      (instrumentMachineSeedHaltMass p M (O a) T c rho (event a)) := by
  have hchoose (a : J) : ∃ T : ℕ, threshold a < ENNReal.ofReal
      (instrumentMachineSeedHaltMass p M (O a) T c rho (event a)) := by
    apply lt_iSup_iff.mp
    rw [← instrumentMachineSeedInfiniteHaltMass_eq_iSup p M (O a) c rho hrho (event a)]
    exact hthreshold a
  choose cutoff hcutoff using hchoose
  refine ⟨Finset.univ.sup cutoff, fun a => (hcutoff a).trans_le ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact instrumentMachineSeedHaltMass_monotone p M (O a) c rho hrho (event a)
    (Finset.le_sup (f := cutoff) (Finset.mem_univ a))

/-- The seed-averaged finite expected query cost is nonnegative when every initial state is
positive semidefinite. -/
theorem instrumentMachineSeedExpectedQueries_nonneg {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef) :
    0 ≤ instrumentMachineSeedExpectedQueries p M O T c rho :=
  Finset.sum_nonneg fun j _ => mul_nonneg (p.nonneg j)
    (instrumentMachineExpectedQueries_nonneg (M j) O T (c j) (rho j) (hrho j))

/-- For positive semidefinite initial states, the seed-averaged finite expected query cost is
bounded by the seed-averaged infinite expected query cost. -/
theorem instrumentMachineSeedExpectedQueries_le_infinite {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef) :
    ENNReal.ofReal (instrumentMachineSeedExpectedQueries p M O T c rho) ≤
      instrumentMachineSeedInfiniteExpectedQueries p M O c rho := by
  unfold instrumentMachineSeedExpectedQueries instrumentMachineSeedInfiniteExpectedQueries
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_le_sum
    intro j _
    rw [ENNReal.ofReal_mul (p.nonneg j)]
    exact mul_le_mul_right (instrumentMachineExpectedQueries_le_infinite
      (M j) O T (c j) (rho j)) _
  · intro j _
    exact mul_nonneg (p.nonneg j)
      (instrumentMachineExpectedQueries_nonneg (M j) O T (c j) (rho j) (hrho j))

/-- For well-formed machines, a unitary oracle, and positive semidefinite initial states,
infinite seed-averaged expected query cost equals the supremum of its finite-prefix
averages. -/
theorem instrumentMachineSeedInfiniteExpectedQueries_eq_iSup {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C)
    (hM : ∀ j, instrumentMachineWellFormed (M j))
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef) :
    instrumentMachineSeedInfiniteExpectedQueries p M O c rho =
      ⨆ T : ℕ, ENNReal.ofReal (instrumentMachineSeedExpectedQueries p M O T c rho) := by
  apply seed_prefix_iSup p
    (fun j T => instrumentMachineExpectedQueries (M j) O T (c j) (rho j))
    (fun j T => instrumentMachineExpectedQueries_nonneg (M j) O T (c j) (rho j) (hrho j))
    (fun j => instrumentMachineExpectedQueries_monotone (M j) (hM j) O hO (c j) (rho j) (hrho j))

/-- Under well-formedness, unitarity, and positivity assumptions, a bound on infinite
seed-averaged expected cost is equivalent to the same bound on every finite-prefix average. -/
theorem instrumentMachineSeedInfiniteExpectedQueries_le_iff {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C)
    (hM : ∀ j, instrumentMachineWellFormed (M j))
    (O : Operator D) (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef) (Q : ℝ≥0∞) :
    instrumentMachineSeedInfiniteExpectedQueries p M O c rho ≤ Q ↔
      ∀ T : ℕ, ENNReal.ofReal (instrumentMachineSeedExpectedQueries p M O T c rho) ≤ Q := by
  rw [instrumentMachineSeedInfiniteExpectedQueries_eq_iSup p M hM O hO c rho hrho]
  exact iSup_le_iff

end Qatlib.Concepts.AdversaryBounds.AdvDuality
