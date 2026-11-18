/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.SingleSpin.QuarticSpin
public import Qatlib.Papers.HydroSpinLatt21.WaveCoupling.SymmetricEnergy
public import Qatlib.Papers.HydroSpinLatt21.Order.IsingGroundStates
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Finite active-spin model consumers

Concrete four-site rings distinguish ferro- and antiferromagnetic energies.
Single-spin examples distinguish the central stationary point from the two
global minima; an odd-ring example verifies the frustration boundary. These
are exact ideal-model consequences associated with [Saenz2021HydroSpinLattices].
-/

set_option autoImplicit false

noncomputable section

namespace QatlibTests.HydroSpinLatticeRegression

open Qatlib.Papers.HydroSpinLatt21.SingleSpin
open Qatlib.Papers.HydroSpinLatt21.Order
open Qatlib.Papers.HydroSpinLatt21.WaveCoupling

/-- A four-site alternating orientation used as a concrete graph consumer. -/
def alternatingFour : Fin 4 → ℝ := ![1, -1, 1, -1]

/-- All four concrete orientations have unit magnitude. -/
theorem alternating_four_unit : UnitSpins alternatingFour := by
  intro i
  fin_cases i <;> norm_num [alternatingFour]

/-- An actual Rayleigh normalization has precisely its preferred clockwise and
anticlockwise fixed angular velocities, in addition to the zero state. -/
example (x : ℝ) : rayleighDrift 2 3 x = 0 ↔ x = 0 ∨ x = 3 ∨ x = -3 :=
  rayleigh_stationary_iff 2 3 x (by norm_num) (by norm_num)

/-- The two nonzero stationary branches at parameter four are exactly `2` and
`-2`, with zero as the remaining stationary point. -/
example (x : ℝ) : spinDrift 4 x = 0 ↔ x = 0 ∨ x = 2 ∨ x = -2 := by
  have hs : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  simpa [hs] using stationary_pos_iff (by norm_num : (0 : ℝ) < 4) x

/-- The central stationary point has higher energy than both broken-symmetry
minima at parameter four. -/
example : spinDrift 4 0 = 0 ∧ spinPotential 4 2 < spinPotential 4 0 ∧
    spinPotential 4 (-2) = spinPotential 4 2 := by
  norm_num [spinDrift, spinPotential]

/-- Below threshold the cubic drift has no nonzero stationary spin. -/
example (x : ℝ) : spinDrift (-1) x = 0 ↔ x = 0 :=
  stationary_nonpos_iff (by norm_num) x

/-- An aligned four-site ferromagnetic ring has the sharp energy `-4`. -/
example : ferroEnergy (fun e : Fin 4 => e) (fun e => e + 1)
    (fun _ => 1) (fun _ => 1) = -4 := by
  norm_num [ferroEnergy]

/-- The alternating four-site ring has antiferromagnetic energy `-4`. -/
example : antiferroEnergy (fun e : Fin 4 => e) (fun e => e + 1)
    (fun _ => 1) alternatingFour = -4 := by
  norm_num [antiferroEnergy, alternatingFour, Fin.sum_univ_succ]

/-- Reversing the coupling sign raises the alternating ring's energy to `4`. -/
example : ferroEnergy (fun e : Fin 4 => e) (fun e => e + 1)
    (fun _ => 1) alternatingFour = 4 := by
  norm_num [ferroEnergy, alternatingFour, Fin.sum_univ_succ]

/-- The explicit alternating ring is a global antiferromagnetic minimizer
among all real unit-spin configurations. -/
example (spin : Fin 4 → ℝ) (hspin : UnitSpins spin) :
    antiferroEnergy (fun e : Fin 4 => e) (fun e => e + 1) (fun _ => 1)
      alternatingFour ≤
    antiferroEnergy (fun e : Fin 4 => e) (fun e => e + 1) (fun _ => 1) spin := by
  apply bipartite_antiferro_global_min _ _ _ (by intro; norm_num)
    alternatingFour alternating_four_unit _ spin hspin
  intro e
  fin_cases e <;> norm_num [alternatingFour]

/-- An odd three-site ring cannot alternate perfectly with unit initial spin. -/
example (spin : ℕ → ℝ) (hzero : spin 0 ^ 2 = 1) (hclose : spin 3 = spin 0) :
    ¬(∀ i < 3, spin (i + 1) = -spin i) :=
  odd_ring_obstruction spin (by decide : Odd 3) hzero hclose

/-- An even four-site alternating chain closes and has opposite neighbours. -/
example : alternatingSpin 4 = alternatingSpin 0 ∧
    ∀ i : ℕ, alternatingSpin (i + 1) = -alternatingSpin i := by
  exact ⟨alternating_spin_even_closure (by decide : Even 4), alternating_spin_succ⟩

/-- Symmetric two-site coupling has the advertised bilinear interchange law. -/
example (x y : Fin 2 → ℝ) :
    pairForm (fun i j => if i = j then 0 else 1) x y =
      pairForm (fun i j => if i = j then 0 else 1) y x := by
  apply pair_form_symmetric
  intro i j
  simp [eq_comm]

/-- The full finite-network Lyapunov identity is externally consumable with
the explicit coordinate gradient, rather than an assumed energy derivative. -/
example {ι : Type*} [Fintype ι] (a : ℝ) (coupling : ι → ι → ℝ)
    (hsymm : ∀ i j, coupling i j = coupling j i) (x : ℝ → ι → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (-networkGradient a coupling (x t) i) t) :
    deriv (fun s => networkEnergy a coupling (x s)) t ≤ 0 :=
  network_energy_deriv_nonpos a coupling hsymm x t hx

end QatlibTests.HydroSpinLatticeRegression
