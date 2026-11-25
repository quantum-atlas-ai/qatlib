/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.OpenChainEnergy

@[expose] public section

/-!
# Consumers of the open-chain energy balance

Concrete checks for [Saenz2021HydroSpinLattices], Methods equations
(23)-(26), on the three-site open chain `Fin 3`, whose endpoints `0` and
`2` have the single neighbour `1` and whose interior site `1` has the two
neighbours `0` and `2`, with the nonzero coupling coefficients
`(a, b) = (1, 2)`, inertia `m r = 1`, relaxation `τ = 1` and natural
frequency `ω₀ = 2`: endpoint and interior neighbour counts, the endpoint
non-double counting receipt (total pair potential exactly one copy of `U`
per edge, value `3 = a + b` at the cross phases `(0, π/2, 0)`), the nonzero
endpoint coupling force `2 = b`, and the exact energy balance along a
concrete trajectory of the active open-chain equation with strictly
subnatural unit speeds and nonvanishing coupling forces, giving the
strictly increasing energy derivative `9/4`. The axiom closures of the main
theorems are printed at the end.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.HydroSpinLatt21.GKModel

namespace QatlibTests.HydroSpinOpenChainEnergyRegression

/-- The cross phase pattern on the three-site open chain: endpoints at
phase `0`, interior site at phase `π/2`. -/
private def threePhase : Fin 3 → ℝ := fun i => if i.val = 1 then Real.pi / 2 else 0

/-- The cross pattern evaluates to `(0, π/2, 0)`. -/
private theorem threePhase_zero : threePhase 0 = 0 := by
  simp [threePhase]

/-- The interior site of the cross pattern sits at phase `π/2`. -/
private theorem threePhase_one : threePhase 1 = Real.pi / 2 := by
  simp [threePhase]

/-- The right endpoint of the cross pattern sits at phase `0`. -/
private theorem threePhase_two : threePhase 2 = 0 := by
  simp [threePhase]

/-- Both endpoints of the nontrivial three-site open chain have exactly one
neighbour. -/
example : (openChainNeighbors 3 (0 : Fin 3)).card = 1 :=
  openChainNeighbors_left_endpoint_card 3 (by norm_num) 0 rfl

example : (openChainNeighbors 3 (2 : Fin 3)).card = 1 :=
  openChainNeighbors_right_endpoint_card 3 (by norm_num) 2 rfl

/-- The interior site of the three-site open chain has exactly two
neighbours. -/
example : (openChainNeighbors 3 (1 : Fin 3)).card = 2 :=
  openChainNeighbors_interior_card 3 1 (by norm_num) (by norm_num)

/-- The endpoint coupling force is nonzero: with the coefficients
`(1, 2)`, the left endpoint receives the force `b = 2` from its single
neighbour `1` at the cross pattern. -/
private theorem endpointForceSum_zero :
    openForceSum 1 2 (openChainNeighbors 3) threePhase 0 = 2 := by
  unfold openForceSum
  rw [openChainNeighbors_three_zero, Finset.sum_singleton, threePhase_zero,
    threePhase_one, gk_pair_force_zero_pi_half]

/-- The interior coupling force sum is nonzero and opposite: `-2`. -/
private theorem interiorForceSum_one :
    openForceSum 1 2 (openChainNeighbors 3) threePhase 1 = -2 := by
  unfold openForceSum
  rw [openChainNeighbors_three_one, Finset.sum_pair (by decide), threePhase_one,
    threePhase_zero, threePhase_two, gk_pair_force_pi_half_zero]
  norm_num

/-- The right endpoint receives the same nonzero force `2`. -/
private theorem endpointForceSum_two :
    openForceSum 1 2 (openChainNeighbors 3) threePhase 2 = 2 := by
  unfold openForceSum
  rw [openChainNeighbors_three_two, Finset.sum_singleton, threePhase_two,
    threePhase_one, gk_pair_force_zero_pi_half]

/-- Non-double counting receipt: the total half-weighted pair potential of
the three-site open chain at the cross pattern with coefficients `(1, 2)`
is `3`: exactly one copy of `U(0, π/2) = 3/2` on the left edge plus one
copy of `U(π/2, 0) = 3/2` on the right edge, each edge counted once. -/
example : openPairPotential 1 2 (openChainNeighbors 3) threePhase = 3 := by
  rw [openChainPairPotential_three 1 2 threePhase, threePhase_zero,
    threePhase_one, threePhase_two]
  unfold gkPairPotential
  rw [Real.cos_zero, Real.cos_pi_div_two, Real.sin_zero, Real.sin_pi_div_two]
  norm_num

/-- The open-chain adjacency of `Fin 3` has exactly four ordered adjacency
pairs, the two orientations of each of the two edges. -/
example : (∑ i, (openChainNeighbors 3 i).card) = 4 := by
  rw [Fin.sum_univ_three, openChainNeighbors_three_zero,
    openChainNeighbors_three_one, openChainNeighbors_three_two]
  norm_num [Finset.card_singleton, Finset.card_insert_of_notMem]

/-! ## A concrete trajectory of the active open-chain equation -/

/-- The acceleration of site `i` of the three-site open chain under the
active equation with the cross phases, unit inertia, relaxation `τ = 1`,
natural frequency `ω₀ = 2` and unit speeds: the Rayleigh drift `3/4` plus
the site's coupling force. -/
private def openChainAcc : Fin 3 → ℝ :=
  fun i => rayleighAngularAcceleration 1 2 1 + openForceSum 1 2
    (openChainNeighbors 3) threePhase i

/-- The phase curves advance at unit speed from the cross pattern. -/
private def openChainΦ : Fin 3 → ℝ → ℝ := fun i t => threePhase i + 1 * t

/-- The velocity curves start at unit speed with the open-chain
accelerations. -/
private def openChainW : Fin 3 → ℝ → ℝ := fun i t => 1 + openChainAcc i * t

/-- The phase curves of the test trajectory have unit derivatives. -/
private theorem openChainΦ_hasDerivAt (i : Fin 3) : HasDerivAt (openChainΦ i) 1 0 :=
  HasDerivAt.congr_deriv
    ((hasDerivAt_const 0 (threePhase i)).add ((hasDerivAt_id 0).const_mul 1))
    (by ring)

/-- The velocity curves of the test trajectory have the open-chain
accelerations as derivatives. -/
private theorem openChainW_hasDerivAt (i : Fin 3) :
    HasDerivAt (openChainW i) (openChainAcc i) 0 :=
  HasDerivAt.congr_deriv
    ((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).const_mul
      (openChainAcc i))) (by ring)

/-- The test trajectory solves the active open-chain equation at the cross
phases with unit inertia: each site's acceleration is the Rayleigh drift at
its unit speed plus its coupling force sum. -/
private theorem openChain_acc_eq (i : Fin 3) :
    1 * 1 * openChainAcc i = 1 * 1 * rayleighAngularAcceleration 1 2 (openChainW i 0)
      + openForceSum 1 2 (openChainNeighbors 3)
          (fun k => openChainΦ k 0) i := by
  rw [openChainAcc, show openChainW i 0 = 1 by simp only [openChainW]; ring]
  have hφ : (fun k => openChainΦ k 0) = threePhase := by
    funext k
    simp only [openChainΦ]
    rw [mul_zero, add_zero]
  rw [hφ]
  ring

/-- The open-chain energy balance along the concrete subnatural trajectory:
with all speeds at `1 < ω₀ = 2` and genuinely nonzero coupling forces at
every site, the energy derivative at `t = 0` is exactly the total Rayleigh
power of the unit speeds. -/
private theorem openChain_balance_receipt :
    HasDerivAt (fun t => openEnergy 1 2 1 1 (openChainNeighbors 3)
        (fun i => openChainΦ i t) (fun i => openChainW i t))
      (latticeRayleighPower 1 1 1 2 (fun i => openChainW i 0)) 0 :=
  openChain_energy_balance 1 2 1 1 1 2 3 openChainΦ openChainW
    (fun i _ => openChainAcc i) 0
    (fun i => by
      rw [show openChainW i 0 = 1 by simp only [openChainW]; ring]
      exact openChainΦ_hasDerivAt i)
    (fun i => openChainW_hasDerivAt i) openChain_acc_eq

/-- The velocities of the test trajectory start at unit speed. -/
private theorem openChainW_zero (i : Fin 3) : openChainW i 0 = 1 := by
  simp only [openChainW, mul_zero, add_zero]

/-- The total Rayleigh power of the three unit speeds at `ω₀ = 2` is the
strictly positive `9/4`: below the natural frequency the active friction
injects energy, independently of the nonzero coupling. -/
example : latticeRayleighPower 1 1 1 2 (fun i => openChainW i 0) = 9 / 4 := by
  simp only [openChainW_zero]
  unfold latticeRayleighPower
  rw [Fin.sum_univ_three]
  norm_num

/-- The energy derivative of the concrete trajectory is therefore the
strictly positive `9/4`. -/
example : HasDerivAt (fun t => openEnergy 1 2 1 1 (openChainNeighbors 3)
      (fun i => openChainΦ i t) (fun i => openChainW i t)) (9 / 4) 0 := by
  rw [show (9 / 4 : ℝ) =
      latticeRayleighPower 1 1 1 2 (fun i => openChainW i 0) by
      simp only [openChainW_zero]; unfold latticeRayleighPower
      rw [Fin.sum_univ_three]; norm_num]
  exact openChain_balance_receipt

/-- The Rayleigh drift of the unit speeds is `3/4`, the common part of the
three site accelerations `11/4`, `-5/4`, `11/4`. -/
example : rayleighAngularAcceleration 1 2 1 = 3 / 4 := by
  unfold rayleighAngularAcceleration
  norm_num

/-- The endpoint site acceleration `3/4 + 2 = 11/4` of the test trajectory
is driven by its single neighbour. -/
example : openChainAcc 0 = 11 / 4 := by
  rw [openChainAcc, endpointForceSum_zero]
  unfold rayleighAngularAcceleration
  norm_num

/-- The interior site acceleration `3/4 - 2 = -5/4` receives the nonzero
coupling of both its neighbours. -/
example : openChainAcc 1 = -5 / 4 := by
  rw [openChainAcc, interiorForceSum_one]
  unfold rayleighAngularAcceleration
  norm_num

/-! ## Axiom closures -/

#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.open_edge_sum_transpose
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.open_pair_potential_hasDerivAt
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.open_energy_balance
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChainNeighbors_symmetric
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChainNeighbors_left_endpoint_card
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChainNeighbors_right_endpoint_card
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChainNeighbors_interior_card
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChain_energy_balance
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChain_energy_balance_of_rhs
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChainPairPotential_eq_forward
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.openChainPairPotential_three

end QatlibTests.HydroSpinOpenChainEnergyRegression

end
