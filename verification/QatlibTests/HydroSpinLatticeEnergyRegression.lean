/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselEnergyBalance

@[expose] public section

/-!
# Consumers of the active-lattice energy balance

Concrete checks for [Saenz2021HydroSpinLattices], Methods equations
(23)-(26): on the two-site `Bool` lattice with neighbour maps `not`
(mutually inverse), with the nonzero coupling coefficients `(a, b) = (1, 2)`,
inertia `m r = 1`, relaxation `τ = 1` and natural frequency `ω₀ = 2`:
nonvanishing coupling force sums and coupling power, the exact energy
balance below and above the natural frequency (positive and negative
derivatives `3/4` and `-45/4`), energy conservation and value on the locked
natural-rotation branch, positivity of the escape rates, per-site threshold
signs, and the impossibility of a potential-flow description. The axiom
closures of the main theorems are printed at the end.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.HydroSpinLatt21.GKModel

namespace QatlibTests.HydroSpinLatticeEnergyRegression

/-- The two-site lattice: both neighbour maps are the logical negation,
which is its own inverse. -/
private theorem twoSite_mutuallyInverse :
    MutuallyInverse (fun x : Bool => !x) (fun x : Bool => !x) := by
  intro i
  exact ⟨Bool.not_not i, Bool.not_not i⟩

/-- The cross phase pattern: site `false` at phase `0` and site `true` at
phase `π/2`. -/
private def crossPhase : Bool → ℝ := fun i => if i then Real.pi / 2 else 0

/-- Sums over the two-site lattice split into the `false` and `true`
summands. -/
private theorem bool_sum_eq (f : Bool → ℝ) :
    ∑ i : Bool, f i = f false + f true := by
  rw [Fintype.univ_bool, Finset.sum_pair (by decide)]
  ring

/-- With the nonzero coefficients `(1, 2)`, the coupling force sum at the
`false` site of the cross pattern is `4`, not `0`: the cancellation in the
energy balance is a chain-rule cancellation, not a vanishing coupling. -/
private theorem crossForceSum_false : latticeForceSum 1 2
    (fun x : Bool => !x) (fun x : Bool => !x) crossPhase false = 4 := by
  show gkPairForce 1 2 (0 : ℝ) (Real.pi / 2)
      + gkPairForce 1 2 (0 : ℝ) (Real.pi / 2) = 4
  rw [gk_pair_force_zero_pi_half]
  norm_num

/-- At the `true` site of the cross pattern the coupling force sum is `-2`:
the lattice force field is nonvanishing at both sites. -/
private theorem crossForceSum_true : latticeForceSum 1 2
    (fun x : Bool => !x) (fun x : Bool => !x) crossPhase true = -2 := by
  show gkPairForce 1 2 (Real.pi / 2) (0 : ℝ)
      + gkPairForce 1 2 (Real.pi / 2) (0 : ℝ) = -2
  rw [gk_pair_force_pi_half_zero]
  norm_num

/-- With unit weights, the total coupling power `Σ ω_i F_i` at the cross
pattern is `2 ≠ 0`: the channel cancelled by the chain rule carries a
genuinely nonzero power before cancellation. -/
example : ∑ i : Bool, (1 : ℝ) * latticeForceSum 1 2
      (fun x : Bool => !x) (fun x : Bool => !x) crossPhase i = 2 := by
  rw [bool_sum_eq]
  norm_num [crossForceSum_false, crossForceSum_true]

/-- The subnatural test trajectory: rigid phase `t` at the `false` site and
`π/2` at the `true` site, with the velocities solving the active lattice
equation at the announced parameters. -/
private def belowPhase : Bool → ℝ → ℝ :=
  fun i t => if i then Real.pi / 2 else t

/-- The velocities of the subnatural test trajectory. -/
private def belowSpeed : Bool → ℝ → ℝ :=
  fun i t => if i then (-2 : ℝ) * t else 1 + 19 / 4 * t

/-- The accelerations of the subnatural test trajectory. -/
private def belowAcc : Bool → ℝ → ℝ :=
  fun i _ => if i then (-2 : ℝ) else 19 / 4

/-- The coupling force sum of the subnatural trajectory at its `false`
site: both neighbours sit at phase `π/2` while the site itself sits at
phase `0`. -/
private theorem belowForceSum_false : latticeForceSum 1 2 (fun x : Bool => !x)
    (fun x : Bool => !x) (fun i => belowPhase i 0) false = 4 := by
  show gkPairForce 1 2 (0 : ℝ) (Real.pi / 2)
      + gkPairForce 1 2 (0 : ℝ) (Real.pi / 2) = 4
  rw [gk_pair_force_zero_pi_half]
  norm_num

/-- The coupling force sum of the subnatural trajectory at its `true`
site: both neighbours sit at phase `0` while the site itself sits at
phase `π/2`. -/
private theorem belowForceSum_true : latticeForceSum 1 2 (fun x : Bool => !x)
    (fun x : Bool => !x) (fun i => belowPhase i 0) true = -2 := by
  show gkPairForce 1 2 (Real.pi / 2) (0 : ℝ)
      + gkPairForce 1 2 (Real.pi / 2) (0 : ℝ) = -2
  rw [gk_pair_force_pi_half_zero]
  norm_num

/-- Below the natural frequency: along the trajectory with phases
`(t, π/2)` and velocities `(1 + 19/4 t, -2t)`, which solves the active
lattice equation at the announced parameters, the energy grows at the
strictly positive rate `3/4`, the Rayleigh injection below `ω₀ = 2`. -/
example : HasDerivAt (fun t => latticeEnergy 1 2 1 1
      (fun x : Bool => !x) (fun x : Bool => !x)
      (fun i => belowPhase i t) (fun i => belowSpeed i t))
    (3 / 4 : ℝ) 0 := by
  have hkin : ∀ i : Bool, HasDerivAt (belowPhase i) (belowSpeed i 0) 0 := by
    intro i
    cases i
    · exact HasDerivAt.congr_deriv (hasDerivAt_id 0) (by norm_num [belowSpeed])
    · exact HasDerivAt.congr_deriv (hasDerivAt_const 0 (Real.pi / 2))
        (by norm_num [belowPhase, belowSpeed])
  have hvel : ∀ i : Bool, HasDerivAt (belowSpeed i) (belowAcc i 0) 0 := by
    intro i
    cases i
    · exact HasDerivAt.congr_deriv
        ((hasDerivAt_const 0 (1 : ℝ)).add
          ((hasDerivAt_id 0).const_mul (19 / 4 : ℝ))) (by norm_num [belowAcc])
    · exact HasDerivAt.congr_deriv ((hasDerivAt_id 0).const_mul (-2 : ℝ))
        (by norm_num [belowAcc])
  have hacc : ∀ i : Bool, (1 : ℝ) * 1 * belowAcc i 0
      = (1 : ℝ) * 1 * rayleighAngularAcceleration 1 2 (belowSpeed i 0)
        + latticeForceSum 1 2 (fun x : Bool => !x) (fun x : Bool => !x)
          (fun i => belowPhase i 0) i := by
    intro i
    cases i
    · rw [belowForceSum_false]
      norm_num [rayleighAngularAcceleration, belowSpeed, belowAcc]
    · rw [belowForceSum_true]
      norm_num [rayleighAngularAcceleration, belowSpeed, belowAcc]
  refine HasDerivAt.congr_deriv (lattice_energy_balance 1 2 1 1 1 2
    (fun x : Bool => !x) (fun x : Bool => !x) twoSite_mutuallyInverse
    belowPhase belowSpeed belowAcc 0 hkin hvel hacc) ?_
  simp only [latticeRayleighPower, bool_sum_eq]
  norm_num [belowSpeed]

/-- The supernatural test trajectory: rigid phase `3t` at the `false` site,
with the velocities solving the active lattice equation at the same
nonzero coupling. -/
private def abovePhase : Bool → ℝ → ℝ :=
  fun i t => if i then Real.pi / 2 else 3 * t

/-- The velocities of the supernatural test trajectory. -/
private def aboveSpeed : Bool → ℝ → ℝ :=
  fun i t => if i then (-2 : ℝ) * t else 3 + 1 / 4 * t

/-- The accelerations of the supernatural test trajectory. -/
private def aboveAcc : Bool → ℝ → ℝ :=
  fun i _ => if i then (-2 : ℝ) else 1 / 4

/-- The coupling force sum of the supernatural trajectory at its `false`
site: the site sits at phase `3·0` while both neighbours sit at `π/2`. -/
private theorem aboveForceSum_false : latticeForceSum 1 2 (fun x : Bool => !x)
    (fun x : Bool => !x) (fun i => abovePhase i 0) false = 4 := by
  show gkPairForce 1 2 (3 * (0 : ℝ)) (Real.pi / 2)
      + gkPairForce 1 2 (3 * (0 : ℝ)) (Real.pi / 2) = 4
  rw [show (3 : ℝ) * 0 = 0 from by norm_num, gk_pair_force_zero_pi_half]
  norm_num

/-- The coupling force sum of the supernatural trajectory at its `true`
site: the site sits at phase `π/2` while both neighbours sit at `3·0`. -/
private theorem aboveForceSum_true : latticeForceSum 1 2 (fun x : Bool => !x)
    (fun x : Bool => !x) (fun i => abovePhase i 0) true = -2 := by
  show gkPairForce 1 2 (Real.pi / 2) (3 * (0 : ℝ))
      + gkPairForce 1 2 (Real.pi / 2) (3 * (0 : ℝ)) = -2
  rw [show (3 : ℝ) * 0 = 0 from by norm_num, gk_pair_force_pi_half_zero]
  norm_num

/-- Above the natural frequency: the energy decreases at the strictly
negative rate `-45/4`, the Rayleigh dissipation above `ω₀ = 2`. The coupling
coefficients are the same as in the subnatural example; only the speed has
crossed the threshold. -/
example : HasDerivAt (fun t => latticeEnergy 1 2 1 1
      (fun x : Bool => !x) (fun x : Bool => !x)
      (fun i => abovePhase i t) (fun i => aboveSpeed i t))
    (-45 / 4 : ℝ) 0 := by
  have hkin : ∀ i : Bool, HasDerivAt (abovePhase i) (aboveSpeed i 0) 0 := by
    intro i
    cases i
    · exact HasDerivAt.congr_deriv ((hasDerivAt_id 0).const_mul (3 : ℝ))
        (by norm_num [abovePhase, aboveSpeed])
    · exact HasDerivAt.congr_deriv (hasDerivAt_const 0 (Real.pi / 2))
        (by norm_num [abovePhase, aboveSpeed])
  have hvel : ∀ i : Bool, HasDerivAt (aboveSpeed i) (aboveAcc i 0) 0 := by
    intro i
    cases i
    · exact HasDerivAt.congr_deriv
        ((hasDerivAt_const 0 (3 : ℝ)).add
          ((hasDerivAt_id 0).const_mul (1 / 4 : ℝ))) (by norm_num [aboveAcc])
    · exact HasDerivAt.congr_deriv ((hasDerivAt_id 0).const_mul (-2 : ℝ))
        (by norm_num [aboveAcc])
  have hacc : ∀ i : Bool, (1 : ℝ) * 1 * aboveAcc i 0
      = (1 : ℝ) * 1 * rayleighAngularAcceleration 1 2 (aboveSpeed i 0)
        + latticeForceSum 1 2 (fun x : Bool => !x) (fun x : Bool => !x)
          (fun i => abovePhase i 0) i := by
    intro i
    cases i
    · rw [aboveForceSum_false]
      norm_num [rayleighAngularAcceleration, aboveSpeed, aboveAcc]
    · rw [aboveForceSum_true]
      norm_num [rayleighAngularAcceleration, aboveSpeed, aboveAcc]
  refine HasDerivAt.congr_deriv (lattice_energy_balance 1 2 1 1 1 2
    (fun x : Bool => !x) (fun x : Bool => !x) twoSite_mutuallyInverse
    abovePhase aboveSpeed aboveAcc 0 hkin hvel hacc) ?_
  simp only [latticeRayleighPower, bool_sum_eq]
  norm_num [aboveSpeed]

/-- The locked natural-rotation branch at `Ω = 2 = ω₀` conserves the energy
exactly, for every phase offset and time. -/
example (φstar t₀ : ℝ) :
    HasDerivAt (fun t => latticeEnergy 1 2 1 1 (fun x : Bool => !x)
        (fun x : Bool => !x) (fun _ : Bool => φstar + 2 * t)
        (fun _ : Bool => 2))
      0 t₀ :=
  synchronized_natural_rotation_energy_constant 1 2 1 1 1 2 2 φstar
    (fun x : Bool => !x) (fun x : Bool => !x) twoSite_mutuallyInverse
    (by norm_num) t₀

/-- On that locked branch the energy is the kinetic value `4`: the two
in-phase pairs contribute no potential energy. -/
example (φstar t : ℝ) :
    latticeEnergy 1 2 1 1 (fun x : Bool => !x) (fun x : Bool => !x)
      (fun _ : Bool => φstar + 2 * t) (fun _ : Bool => 2) = 4 := by
  unfold latticeEnergy latticeKineticEnergy latticePairPotential
  simp only [bool_sum_eq, gk_pair_potential_in_phase]
  norm_num

/-- The supernatural escape rate of the two-site lattice at `ω₀ = 2`,
`δ = 1`, unit inertia and relaxation, is the strictly positive `45/2`. -/
example : (Fintype.card Bool : ℝ) * (1 * 1 / (1 * 2 ^ 2)) * (2 + 1) ^ 2
      * ((2 + 1) ^ 2 - 2 ^ 2) = 45 / 2 := by norm_num

/-- The subnatural injection rate of the same two-site lattice in the band
`[1/2, 1]` (with `ε = 1/2`, `δ = 1`) is the strictly positive `3/8`. -/
example : (Fintype.card Bool : ℝ) * (1 * 1 / (1 * 2 ^ 2))
      * ((1 / 2) ^ 2 * (2 ^ 2 - (2 - 1) ^ 2)) = 3 / 8 := by norm_num

/-- Per-site injection sign below the natural frequency, at unit
parameters: the speed `1 < 2` gives strictly positive Rayleigh power. -/
example : 0 < (1 : ℝ) * 1 / 1 * (1 - 1 ^ 2 / 2 ^ 2) * 1 ^ 2 := by norm_num

/-- Per-site dissipation sign above the natural frequency: the speed
`3 > 2` gives strictly negative Rayleigh power. -/
example : (1 : ℝ) * 1 / 1 * (1 - 3 ^ 2 / 2 ^ 2) * 3 ^ 2 < 0 := by norm_num

/-- On a nonempty symmetric lattice with all speeds in `(0, ω₀)`, the total
Rayleigh power is strictly positive even at the nonzero coupling
coefficients of the cross pattern. -/
example : 0 < latticeRayleighPower 1 1 1 2 (fun _ : Bool => 1) :=
  lattice_rayleigh_power_pos_of_lt 1 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun _ : Bool => 1)
    (fun _ => ⟨by norm_num, by norm_num⟩)

/-- On a nonempty symmetric lattice with all speeds above `ω₀`, the total
Rayleigh power is strictly negative. -/
example : latticeRayleighPower 1 1 1 2 (fun _ : Bool => 3) < 0 :=
  lattice_rayleigh_power_neg_of_gt 1 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun _ : Bool => 3) (fun _ => by norm_num)

/-- With nonzero angular inertia, the active lattice field at the cross
coefficients admits no potential-flow description on the two-site lattice. -/
example : ¬ ∃ G : (Bool → ℝ) → (Bool → ℝ) → ℝ,
      ∀ (ψ ν : Bool → ℝ) (j : Bool) (x y : ℝ),
        HasDerivAt (fun x' => G (Function.update ψ j x') ν) (-(ν j)) x ∧
        HasDerivAt (fun y' => G ψ (Function.update ν j y'))
          (-(rayleighAngularAcceleration 1 2 (ν j)
            + latticeForceSum 1 2 (fun x : Bool => !x) (fun x : Bool => !x) ψ j
              / (1 * 1))) y :=
  not_active_lattice_potential_flow 1 2 1 1 1 2 (fun x : Bool => !x)
    (fun x : Bool => !x)

/-! ## Axiom closures -/

#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.lattice_energy_balance
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.lattice_pair_potential_hasDerivAt
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.lattice_rayleigh_power_pos_of_lt
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.lattice_rayleigh_power_neg_of_gt
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.rayleigh_power_le_of_supernatural
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.rayleigh_power_ge_of_subnatural
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.lattice_energy_escape_bound_above
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.lattice_energy_escape_bound_below
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.latticeRayleighPower_const_eq_zero
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.synchronized_natural_rotation_rhs_eq_zero
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.synchronized_natural_rotation_energy_constant
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.not_active_lattice_potential_flow
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.bessel_gk_lattice_energy_balance

end QatlibTests.HydroSpinLatticeEnergyRegression

end
