/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachine
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.ENNReal.BigOperators
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped Classical ComplexOrder ENNReal

noncomputable def instrumentMachineSeedHaltMass {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) : ℝ :=
  ∑ j, p.prob j * instrumentMachineHaltMass (M j) O T (c j) (rho j) (event j)

noncomputable def instrumentMachineSeedInfiniteHaltMass {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (p.prob j) *
    instrumentMachineInfiniteHaltMass (M j) O (c j) (rho j) (event j)

noncomputable def instrumentMachineSeedExpectedQueries {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D) : ℝ :=
  ∑ j, p.prob j * instrumentMachineExpectedQueries (M j) O T (c j) (rho j)

noncomputable def instrumentMachineSeedInfiniteExpectedQueries {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D) : ℝ≥0∞ :=
  ∑ j, ENNReal.ofReal (p.prob j) *
    instrumentMachineInfiniteExpectedQueries (M j) O (c j) (rho j)

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

theorem instrumentMachineSeedHaltMass_nonneg {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D)
    (hrho : ∀ j, (rho j).PosSemidef)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) :
    0 ≤ instrumentMachineSeedHaltMass p M O T c rho event :=
  Finset.sum_nonneg fun j _ => mul_nonneg (p.nonneg j)
    (instrumentMachineHaltMass_nonneg (M j) O T (c j) (rho j) (hrho j) (event j))

theorem instrumentMachineSeedHaltMass_monotone {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef)
    (event : Fin r → C → Bool → List (ℕ×ℕ) → Bool) :
    Monotone (fun T => instrumentMachineSeedHaltMass p M O T c rho event) := by
  intro S T hST
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (instrumentMachineHaltMass_monotone (M j) O (c j) (rho j) (hrho j) (event j) hST)
    (p.nonneg j)

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

theorem instrumentMachineSeedExpectedQueries_nonneg {D r : ℕ} {C : Type*}
    (p : FinDist (Fin r)) (M : Fin r → InstrumentMachine D C) (O : Operator D)
    (T : ℕ) (c : Fin r → C) (rho : Fin r → Operator D) (hrho : ∀ j, (rho j).PosSemidef) :
    0 ≤ instrumentMachineSeedExpectedQueries p M O T c rho :=
  Finset.sum_nonneg fun j _ => mul_nonneg (p.nonneg j)
    (instrumentMachineExpectedQueries_nonneg (M j) O T (c j) (rho j) (hrho j))

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
