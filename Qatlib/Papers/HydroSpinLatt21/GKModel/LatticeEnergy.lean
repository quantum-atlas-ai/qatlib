/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.SignedPairPotential

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact energy balance of the active generalized Kuramoto lattice

[Saenz2021HydroSpinLattices], Methods equations (23)-(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
This file proves the exact energy balance of the *actual* second-order active
generalized Kuramoto equation on a symmetric finite lattice, continuing
`Qatlib.Papers.HydroSpinLatt21.GKModel.SignedPairPotential` (the pair
potential and force of equations (24)-(26)); the Bessel-coefficient
instantiation for the lattice field of
`Qatlib.Papers.HydroSpinLatt21.BesselModel.GkTrajectory` is given in
`Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselEnergyBalance`.

## Main results

* `lattice_pair_potential_hasDerivAt` — the chain rule on the signed pair
  potential, combined with the exchange symmetry `U_ij = U_ji` and the
  mutual-inverse symmetry of the neighbour maps, cancels the coupling power
  channel exactly: the derivative of the total pair potential is the negative
  of the power delivered by the pair forces. The cancellation holds for each
  signed component separately and is *not* a Newton third-law cancellation,
  since the pair force is not antisymmetric under exchange
  (`gk_pair_force_not_exchange_antisymmetric` gives a witness).
* `lattice_energy_balance` — for any trajectory of the second-order active
  lattice equation
  `m r ω̇_i = m r (1/τ)(1 - ω_i²/ω₀²)ω_i + Σ_{j ∈ {L i, R i}} F_ij(φ_i, φ_j)`,
  the time derivative of the energy `E = Σ_i (m r/2) ω_i² + Σ_pairs U/2` is
  exactly the Rayleigh power `Σ_i (m r/τ)(1 - ω_i²/ω₀²)ω_i²`. The coupling
  channel contributes nothing: the error between the dynamics and an
  effective Hamiltonian flow of `E` is exactly the Rayleigh term, and
  nothing else.
* `rayleigh_power_pos_iff`, `rayleigh_power_neg_iff`,
  `rayleigh_power_eq_zero_iff` and their lattice versions
  `lattice_rayleigh_power_pos_of_lt`, `lattice_rayleigh_power_neg_of_gt` —
  the natural orbital frequency `ω₀ = v₀/r₀` of the paper is the exact
  injection threshold on any symmetric lattice: speeds strictly between `0`
  and `ω₀` in magnitude give strictly increasing energy, speeds strictly
  above `ω₀` give strictly decreasing energy, independently of the coupling.
* `lattice_energy_escape_bound_above` and `lattice_energy_escape_bound_below`
  — quantitative escape times from speed ranges bounded away from
  `{0, ±ω₀}`: strictly supernatural trajectories lose energy at an explicit
  uniform rate (so they can persist at most a bounded time), and strictly
  subnatural trajectories gain energy at an explicit uniform rate (so they
  cannot stay inside the injection band).
* `synchronized_natural_rotation_rhs_eq_zero` and
  `synchronized_natural_rotation_energy_constant` — the locked synchronized
  rotation branches at natural speeds solve the active lattice equation
  exactly and conserve the energy.
* `not_active_lattice_potential_flow` — the active second-order field is not
  the negative gradient of any scalar potential on the full phase-velocity
  state space whenever `m r ≠ 0`, delimiting the gradient-flow
  approximation.

## Scope and boundary conditions

The balance is exact at the level of the generalized Kuramoto lattice
equation with instantaneous signed pair forces; deriving that equation from
the Faraday-wave memory dynamics requires `r/L ≪ 1` and short memory, as
quantified in the `BesselModel` files (the exact azimuthal wave force is
*not* a gradient, see
`Qatlib.Papers.HydroSpinLatt21.GKModel.wave_force_not_symmetric_pair_gradient`).
The symmetry hypothesis `MutuallyInverse left right` covers periodic
one-dimensional lattices of any period, the two-site lattice with coinciding
neighbour maps, and the one-site lattice; the paper's hydrodynamic spin
lattices are open chains whose boundary sites have a single neighbour, so
the identity applies to their periodic idealization. Experimental facts (the
driving threshold `Γ_c ≈ 0.85 Γ_F` for the spin regime, the measured
response curves and the rotation threshold `ω₀ = v₀/r₀` as an observed
quantity) remain registered observations rather than theorems. Global
asymptotic stability of the rotating branches on the lattice is *not* proved
here; the escape bounds are the quantitative substitute.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.GKModel

open Real Set

/-! ## Lattice data and energies -/

/-- The mutual-inverse symmetry of the two neighbour maps of a finite
lattice: shifting by `left` and then `right` (in either order) returns to the
starting site. This covers periodic one-dimensional lattices of any period,
the two-site lattice with coinciding neighbour maps, and the one-site
lattice. -/
def MutuallyInverse {ι : Type*} (left right : ι → ι) : Prop :=
  ∀ i, right (left i) = i ∧ left (right i) = i

/-- The Rayleigh angular acceleration drift of equation (23), driving each
angular velocity towards the natural orbital frequency `ω₀ = v₀/r₀`. This is
definitionally the drift `rayleighDrift` used by the lattice field of the
Bessel model trajectory file. -/
def rayleighAngularAcceleration (τ ω₀ w : ℝ) : ℝ :=
  1 / τ * (1 - w ^ 2 / ω₀ ^ 2) * w

/-- The total signed pair force received by site `i` from its two
neighbours, each force taken in the receiving site's phase as in the
assembled equation (23). -/
def latticeForceSum (a b : ℝ) {ι : Type*} (left right : ι → ι) (φ : ι → ℝ)
    (i : ι) : ℝ :=
  gkPairForce a b (φ i) (φ (left i)) + gkPairForce a b (φ i) (φ (right i))

/-- The total pair potential of the lattice: the signed potential of
equation (24) summed over all ordered receiving-emitting pairs and halved,
so that each unordered pair of a symmetric lattice is counted once. -/
def latticePairPotential (a b : ℝ) {ι : Type*} [Fintype ι] (left right : ι → ι)
    (φ : ι → ℝ) : ℝ :=
  ∑ i, (1 / 2) * (gkPairPotential a b (φ i) (φ (left i))
    + gkPairPotential a b (φ i) (φ (right i)))

/-- The kinetic energy of the lattice in the angular velocities, with the
angular inertia `m r` of the tangential balance (11). -/
def latticeKineticEnergy (m r : ℝ) {ι : Type*} [Fintype ι] (ω : ι → ℝ) : ℝ :=
  ∑ i, m * r / 2 * ω i ^ 2

/-- The total Rayleigh power of the lattice: the injection rate of the
active friction at speeds below `ω₀` and the dissipation rate above it. -/
def latticeRayleighPower (m r τ ω₀ : ℝ) {ι : Type*} [Fintype ι] (ω : ι → ℝ) : ℝ :=
  ∑ i, m * r / τ * (1 - ω i ^ 2 / ω₀ ^ 2) * ω i ^ 2

/-- The energy of the active lattice: angular-velocity kinetic energy plus
signed pair potential. -/
def latticeEnergy (a b m r : ℝ) {ι : Type*} [Fintype ι] (left right : ι → ι)
    (φ ω : ι → ℝ) : ℝ :=
  latticeKineticEnergy m r ω + latticePairPotential a b left right φ

/-! ## Periodicity and exchange structure of the pair force -/

/-- The sine is unchanged by a full-period advance. -/
private theorem sin_add_two_pi (x : ℝ) :
    Real.sin (x + 2 * Real.pi) = Real.sin x := by
  have hcast : ((1 : ℤ) : ℝ) * (2 * Real.pi) = 2 * Real.pi := by norm_num
  rw [← hcast]
  exact Real.sin_add_int_mul_two_pi x 1

/-- The cosine is unchanged by a full-period advance. -/
private theorem cos_add_two_pi (x : ℝ) :
    Real.cos (x + 2 * Real.pi) = Real.cos x := by
  have hcast : ((1 : ℤ) : ℝ) * (2 * Real.pi) = 2 * Real.pi := by norm_num
  rw [← hcast]
  exact Real.cos_add_int_mul_two_pi x 1

/-- The pair force is unchanged when the receiving phase advances by a full
period. -/
theorem gkPairForce_add_two_pi_first (a b x y : ℝ) :
    gkPairForce a b (x + 2 * Real.pi) y = gkPairForce a b x y := by
  unfold gkPairForce
  rw [sin_add_two_pi, cos_add_two_pi]

/-- The pair force is unchanged when the emitting phase advances by a full
period. -/
theorem gkPairForce_add_two_pi_second (a b x y : ℝ) :
    gkPairForce a b x (y + 2 * Real.pi) = gkPairForce a b x y := by
  unfold gkPairForce
  rw [sin_add_two_pi, cos_add_two_pi]

/-- The pair force is unchanged when both phases advance by a full period. -/
theorem gkPairForce_add_two_pi_both (a b x y : ℝ) :
    gkPairForce a b (x + 2 * Real.pi) (y + 2 * Real.pi) = gkPairForce a b x y := by
  rw [gkPairForce_add_two_pi_first, gkPairForce_add_two_pi_second]

/-- Advancing only the receiving site's phase by a full period leaves the
force sum at that site unchanged, whatever the neighbour maps are. -/
theorem latticeForceSum_update_self_add_two_pi (a b : ℝ) {ι : Type*}
    [DecidableEq ι] (left right : ι → ι) (φ : ι → ℝ) (j : ι) :
    latticeForceSum a b left right
        (Function.update φ j (φ j + 2 * Real.pi)) j
      = latticeForceSum a b left right φ j := by
  unfold latticeForceSum
  by_cases hl : left j = j
  · by_cases hr : right j = j
    · rw [hl, hr, Function.update_self, gkPairForce_add_two_pi_both]
    · rw [hl, Function.update_self, Function.update_of_ne hr,
        gkPairForce_add_two_pi_both, gkPairForce_add_two_pi_first]
  · by_cases hr : right j = j
    · rw [hr, Function.update_self, Function.update_of_ne hl,
        gkPairForce_add_two_pi_both, gkPairForce_add_two_pi_first]
    · rw [Function.update_of_ne hl, Function.update_of_ne hr, Function.update_self,
        gkPairForce_add_two_pi_first, gkPairForce_add_two_pi_first]

/-- The pair force is not antisymmetric under exchange of the two phases:
with coefficients `(1, 2)` the two transverse forces at the phase pair
`(0, π/2)` sum to `1`, not `0`. The energy cancellation on the lattice is
therefore a chain-rule cancellation between the exchange-symmetric potential
and the kinetic coupling power, not a Newton third-law cancellation. -/
theorem gk_pair_force_not_exchange_antisymmetric :
    gkPairForce 1 2 0 (Real.pi / 2) + gkPairForce 1 2 (Real.pi / 2) 0 ≠ 0 := by
  rw [gk_pair_force_zero_pi_half, gk_pair_force_pi_half_zero]
  norm_num

/-! ## Reindexing along the symmetric lattice -/

/-- Under the mutual-inverse symmetry the `right` map is a bijection. -/
theorem bijective_right_of_mutuallyInverse {ι : Type*} {left right : ι → ι}
    (hinv : MutuallyInverse left right) : Function.Bijective right := by
  constructor
  · intro x y hxy
    have h := congrArg left hxy
    rw [(hinv x).2, (hinv y).2] at h
    exact h
  · intro i
    exact ⟨left i, (hinv i).1⟩

/-- Under the mutual-inverse symmetry the `left` map is a bijection. -/
theorem bijective_left_of_mutuallyInverse {ι : Type*} {left right : ι → ι}
    (hinv : MutuallyInverse left right) : Function.Bijective left := by
  constructor
  · intro x y hxy
    have h := congrArg right hxy
    rw [(hinv x).1, (hinv y).1] at h
    exact h
  · intro i
    exact ⟨right i, (hinv i).2⟩

/-- Reindexing along `left`: the emitting-side weighted forces of the left
neighbour pairs sum to the weighted forces received from the right
neighbours. -/
theorem sum_pair_force_weight_left {ι : Type*} [Fintype ι] (a b : ℝ)
    (left right : ι → ι) (hinv : MutuallyInverse left right) (φ w : ι → ℝ) :
    ∑ i, gkPairForce a b (φ (left i)) (φ i) * w (left i)
      = ∑ i, gkPairForce a b (φ i) (φ (right i)) * w i := by
  refine Fintype.sum_bijective left (bijective_left_of_mutuallyInverse hinv)
    (fun i => gkPairForce a b (φ (left i)) (φ i) * w (left i))
    (fun j => gkPairForce a b (φ j) (φ (right j)) * w j) ?_
  intro i
  rw [(hinv i).1]

/-- Reindexing along `right`: the emitting-side weighted forces of the right
neighbour pairs sum to the weighted forces received from the left
neighbours. -/
theorem sum_pair_force_weight_right {ι : Type*} [Fintype ι] (a b : ℝ)
    (left right : ι → ι) (hinv : MutuallyInverse left right) (φ w : ι → ℝ) :
    ∑ i, gkPairForce a b (φ (right i)) (φ i) * w (right i)
      = ∑ i, gkPairForce a b (φ i) (φ (left i)) * w i := by
  refine Fintype.sum_bijective right (bijective_right_of_mutuallyInverse hinv)
    (fun i => gkPairForce a b (φ (right i)) (φ i) * w (right i))
    (fun j => gkPairForce a b (φ j) (φ (left j)) * w j) ?_
  intro i
  rw [(hinv i).2]

/-! ## The chain-rule cancellation of the coupling channel -/

/-- The two-argument chain rule for the pair potential along two
differentiable phase curves: the derivative of `U_ij` along `(φ_i, φ_j)` is
minus the receiving force times the receiving speed, minus the transposed
emitting force times the emitting speed. This is the pair-level form of the
exchange-symmetric cancellation. -/
theorem gk_pair_potential_hasDerivAt_pair (a b : ℝ) (c d : ℝ → ℝ)
    (t₀ c' d' : ℝ) (hc : HasDerivAt c c' t₀) (hd : HasDerivAt d d' t₀) :
    HasDerivAt (fun t => gkPairPotential a b (c t) (d t))
      (-(gkPairForce a b (c t₀) (d t₀) * c'
          + gkPairForce a b (d t₀) (c t₀) * d')) t₀ := by
  have hu : HasDerivAt (fun t => Real.cos (c t) - Real.cos (d t))
      (-(Real.sin (c t₀)) * c' - (-(Real.sin (d t₀)) * d')) t₀ :=
    hc.cos.sub hd.cos
  have hv : HasDerivAt (fun t => Real.sin (c t) - Real.sin (d t))
      (Real.cos (c t₀) * c' - Real.cos (d t₀) * d') t₀ :=
    hc.sin.sub hd.sin
  have h1 : HasDerivAt
      (fun t => (a / 2) * ((Real.cos (c t) - Real.cos (d t))
        * (Real.cos (c t) - Real.cos (d t))))
      ((a / 2) * ((Real.cos (c t₀) - Real.cos (d t₀))
          * (-(Real.sin (c t₀)) * c' - (-(Real.sin (d t₀)) * d'))
        + (Real.cos (c t₀) - Real.cos (d t₀))
          * (-(Real.sin (c t₀)) * c' - (-(Real.sin (d t₀)) * d')))) t₀ := by
    refine ((hu.mul hu).const_mul (a / 2)).congr_deriv ?_
    ring
  have h2 : HasDerivAt
      (fun t => (b / 2) * ((Real.sin (c t) - Real.sin (d t))
        * (Real.sin (c t) - Real.sin (d t))))
      ((b / 2) * ((Real.sin (c t₀) - Real.sin (d t₀))
          * (Real.cos (c t₀) * c' - Real.cos (d t₀) * d')
        + (Real.sin (c t₀) - Real.sin (d t₀))
          * (Real.cos (c t₀) * c' - Real.cos (d t₀) * d'))) t₀ := by
    refine ((hv.mul hv).const_mul (b / 2)).congr_deriv ?_
    ring
  refine HasDerivAt.congr_deriv (h1.add h2) ?_
  unfold gkPairForce
  ring

/-- The sum-level cancellation identity: the halved sum over ordered pairs of
the two-argument chain-rule derivatives equals the negative coupling power,
using the two reindexing identities along the symmetric neighbour maps. -/
theorem lattice_potential_power_cancellation {ι : Type*} [Fintype ι]
    (a b : ℝ) (left right : ι → ι) (hinv : MutuallyInverse left right)
    (φ w : ι → ℝ) :
    (∑ i, (1 / 2) * ((-(gkPairForce a b (φ i) (φ (left i)) * w i
              + gkPairForce a b (φ (left i)) (φ i) * w (left i)))
        + (-(gkPairForce a b (φ i) (φ (right i)) * w i
              + gkPairForce a b (φ (right i)) (φ i) * w (right i)))))
      = -(∑ i, w i * latticeForceSum a b left right φ i) := by
  have hsumhalf : ∑ i, (1 / 2) * ((gkPairForce a b (φ i) (φ (left i)) * w i
          + gkPairForce a b (φ (left i)) (φ i) * w (left i))
        + (gkPairForce a b (φ i) (φ (right i)) * w i
          + gkPairForce a b (φ (right i)) (φ i) * w (right i)))
      = ∑ i, w i * latticeForceSum a b left right φ i := by
    have h1 := sum_pair_force_weight_left a b left right hinv φ w
    have h2 := sum_pair_force_weight_right a b left right hinv φ w
    have hcomb : (∑ i, gkPairForce a b (φ i) (φ (left i)) * w i)
        + (∑ i, gkPairForce a b (φ i) (φ (right i)) * w i)
        = ∑ i, w i * latticeForceSum a b left right φ i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by unfold latticeForceSum; ring
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, h1, h2]
    linarith [hcomb]
  have hEq : ∀ i : ι,
      (1 / 2) * ((-(gkPairForce a b (φ i) (φ (left i)) * w i
            + gkPairForce a b (φ (left i)) (φ i) * w (left i)))
          + (-(gkPairForce a b (φ i) (φ (right i)) * w i
            + gkPairForce a b (φ (right i)) (φ i) * w (right i))))
        = -((1 / 2) * ((gkPairForce a b (φ i) (φ (left i)) * w i
              + gkPairForce a b (φ (left i)) (φ i) * w (left i))
            + (gkPairForce a b (φ i) (φ (right i)) * w i
              + gkPairForce a b (φ (right i)) (φ i) * w (right i)))) := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ => hEq i), Finset.sum_neg_distrib, hsumhalf]

/-- The chain-rule cancellation theorem for the lattice: along any
differentiable family of phase curves, the derivative of the total pair
potential is exactly the negative of the coupling power, the sum of the
angular velocities weighted by the received pair forces. This holds for
arbitrary signed coefficients and requires only the mutual-inverse symmetry
of the neighbour maps. -/
theorem lattice_pair_potential_hasDerivAt {ι : Type*} [Fintype ι]
    (a b : ℝ) (left right : ι → ι) (hinv : MutuallyInverse left right)
    (Φ W : ι → ℝ → ℝ) (t₀ : ℝ) (hΦ : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀) :
    HasDerivAt (fun t => latticePairPotential a b left right (fun i => Φ i t))
      (-(∑ i, W i t₀ * latticeForceSum a b left right (fun i => Φ i t₀) i)) t₀ := by
  have hsum : HasDerivAt
      (fun t => ∑ i, (1 / 2) * (gkPairPotential a b (Φ i t) (Φ (left i) t)
        + gkPairPotential a b (Φ i t) (Φ (right i) t)))
      (∑ i, (1 / 2) * ((-(gkPairForce a b (Φ i t₀) (Φ (left i) t₀) * W i t₀
                + gkPairForce a b (Φ (left i) t₀) (Φ i t₀) * W (left i) t₀))
            + (-(gkPairForce a b (Φ i t₀) (Φ (right i) t₀) * W i t₀
                + gkPairForce a b (Φ (right i) t₀) (Φ i t₀)
                  * W (right i) t₀)))) t₀ := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    exact ((gk_pair_potential_hasDerivAt_pair a b (Φ i) (Φ (left i)) t₀ (W i t₀)
      (W (left i) t₀) (hΦ i) (hΦ (left i))).add
      (gk_pair_potential_hasDerivAt_pair a b (Φ i) (Φ (right i)) t₀ (W i t₀)
        (W (right i) t₀) (hΦ i) (hΦ (right i)))).const_mul (1 / 2)
  unfold latticePairPotential
  refine HasDerivAt.congr_deriv hsum ?_
  exact lattice_potential_power_cancellation a b left right hinv (fun i => Φ i t₀)
      (fun i => W i t₀)

/-! ## The exact energy balance -/

/-- The derivative of the angular-velocity kinetic energy along a
differentiable family of velocity curves. -/
theorem lattice_kinetic_energy_hasDerivAt {ι : Type*} [Fintype ι] (m r : ℝ)
    (W V : ι → ℝ → ℝ) (t₀ : ℝ) (hW : ∀ i, HasDerivAt (W i) (V i t₀) t₀) :
    HasDerivAt (fun t => latticeKineticEnergy m r (fun i => W i t))
      (∑ i, m * r * (W i t₀ * V i t₀)) t₀ := by
  unfold latticeKineticEnergy
  refine HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum fun i _ => (HasDerivAt.pow (hW i) 2).const_mul (m * r / 2)) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_num
  ring

/-- The exact energy balance of the second-order active generalized
Kuramoto equation on a symmetric finite lattice. Along any trajectory whose
phase velocities and accelerations satisfy the active lattice equation with
angular inertia `m r`, the energy (angular-velocity kinetic energy plus
signed pair potential) changes at exactly the Rayleigh power: the coupling
channel cancels identically by the chain rule of
`lattice_pair_potential_hasDerivAt`. No sign or positivity hypothesis is
imposed on any parameter; the identity is exact, so the residual of the
effective Hamiltonian description is precisely the Rayleigh term. -/
theorem lattice_energy_balance {ι : Type*} [Fintype ι] (a b m r τ ω₀ : ℝ)
    (left right : ι → ι) (hinv : MutuallyInverse left right)
    (Φ W Acc : ι → ℝ → ℝ) (t₀ : ℝ)
    (hkin : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀)
    (hvel : ∀ i, HasDerivAt (W i) (Acc i t₀) t₀)
    (hacc : ∀ i, m * r * Acc i t₀
      = m * r * rayleighAngularAcceleration τ ω₀ (W i t₀)
        + latticeForceSum a b left right (fun i => Φ i t₀) i) :
    HasDerivAt (fun t => latticeEnergy a b m r left right
        (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t₀)) t₀ := by
  have hpot := lattice_pair_potential_hasDerivAt a b left right hinv Φ W t₀ hkin
  have hkinE := lattice_kinetic_energy_hasDerivAt m r W Acc t₀ hvel
  have hsplit : ∀ i : ι,
      m * r * (W i t₀ * Acc i t₀)
        - W i t₀ * latticeForceSum a b left right (fun i => Φ i t₀) i
        = m * r / τ * (1 - W i t₀ ^ 2 / ω₀ ^ 2) * W i t₀ ^ 2 := by
    intro i
    have hkey : m * r * (W i t₀ * Acc i t₀)
        = W i t₀ * (m * r * Acc i t₀) := by ring
    rw [hkey, hacc i, mul_add, mul_sub]
    unfold rayleighAngularAcceleration
    field_simp
    ring
  have hsum : (∑ i, m * r * (W i t₀ * Acc i t₀))
      + -(∑ i, W i t₀ * latticeForceSum a b left right (fun i => Φ i t₀) i)
      = latticeRayleighPower m r τ ω₀ (fun i => W i t₀) := by
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun i _ => hsplit i)]
    simp only [latticeRayleighPower]
  exact HasDerivAt.congr_deriv (hkinE.add hpot) hsum

/-! ## Sign of the Rayleigh injection and dissipation -/

/-- Rewriting of the per-site Rayleigh power as a positive prefactor times
the quartic gap factor `(ω₀² - w²) w²`, for a nonzero natural frequency. -/
private theorem rayleigh_power_eq {ω₀ : ℝ} (hω₀ : ω₀ ≠ 0) (m r τ w : ℝ) :
    m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2
      = (m * r / (τ * ω₀ ^ 2)) * ((ω₀ ^ 2 - w ^ 2) * w ^ 2) := by
  field_simp [hω₀]

/-- With a positive natural frequency, the quartic gap factor is strictly
positive exactly off rest and strictly below the natural speed. -/
private theorem gap_factor_pos_iff {ω₀ w : ℝ} (hω₀ : 0 < ω₀) :
    0 < (ω₀ ^ 2 - w ^ 2) * w ^ 2 ↔ w ≠ 0 ∧ |w| < ω₀ := by
  constructor
  · intro h
    have hw2 : w ^ 2 ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at h
      exact lt_irrefl 0 h
    have hw : w ≠ 0 := fun h0 => hw2 (by rw [h0]; ring)
    have hsq : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (Ne.symm hw2)
    have hdiff : 0 < ω₀ ^ 2 - w ^ 2 := by
      by_contra hcon
      simp only [not_lt] at hcon
      have hnonpos : (ω₀ ^ 2 - w ^ 2) * w ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcon hsq.le
      linarith
    exact ⟨hw, abs_lt_of_sq_lt_sq (by linarith : w ^ 2 < ω₀ ^ 2) hω₀.le⟩
  · rintro ⟨h0, habs⟩
    have hsq : 0 < w ^ 2 := sq_pos_of_ne_zero h0
    have hlt : w ^ 2 < ω₀ ^ 2 := by
      refine sq_lt_sq.2 ?_
      rwa [abs_of_pos hω₀]
    exact mul_pos (by linarith) hsq

/-- With positive physical parameters, the per-site Rayleigh power is
strictly positive exactly strictly between rest and the natural speed. -/
theorem rayleigh_power_pos_iff {m r τ ω₀ w : ℝ}
    (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀) :
    0 < m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2 ↔
      w ≠ 0 ∧ |w| < ω₀ := by
  have hk : 0 < m * r / (τ * ω₀ ^ 2) := by positivity
  constructor
  · intro h
    have hgap : 0 < (ω₀ ^ 2 - w ^ 2) * w ^ 2 := by
      by_contra hcon
      simp only [not_lt] at hcon
      have hnonpos : m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2 ≤ 0 := by
        rw [rayleigh_power_eq hω₀.ne' m r τ w]
        exact mul_nonpos_of_nonneg_of_nonpos hk.le hcon
      linarith
    exact (gap_factor_pos_iff hω₀).1 hgap
  · intro h
    rw [rayleigh_power_eq hω₀.ne' m r τ w]
    exact mul_pos hk ((gap_factor_pos_iff hω₀).2 h)

/-- With positive physical parameters, the per-site Rayleigh power is
strictly negative exactly strictly above the natural speed. -/
theorem rayleigh_power_neg_iff {m r τ ω₀ w : ℝ}
    (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀) :
    m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2 < 0 ↔
      ω₀ < |w| := by
  have hk : 0 < m * r / (τ * ω₀ ^ 2) := by positivity
  have hω₀2 : 0 < ω₀ ^ 2 := by positivity
  constructor
  · intro h
    have hgap : (ω₀ ^ 2 - w ^ 2) * w ^ 2 < 0 := by
      by_contra hcon
      simp only [not_lt] at hcon
      have hnonneg : 0 ≤ m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2 := by
        rw [rayleigh_power_eq hω₀.ne' m r τ w]
        exact mul_nonneg hk.le hcon
      linarith
    have hw : w ≠ 0 := by
      intro h0
      rw [h0] at hgap
      norm_num at hgap
    have hsq : 0 < w ^ 2 := sq_pos_of_ne_zero hw
    have hlt : ω₀ ^ 2 < w ^ 2 := by
      by_contra hcon
      simp only [not_lt] at hcon
      have hnonneg : 0 ≤ (ω₀ ^ 2 - w ^ 2) * w ^ 2 :=
        mul_nonneg (sub_nonneg.2 hcon) hsq.le
      linarith
    have habs := sq_lt_sq.1 hlt
    rwa [abs_of_pos hω₀] at habs
  · intro h
    have hlt : ω₀ ^ 2 < w ^ 2 := by
      refine sq_lt_sq.2 ?_
      rwa [abs_of_pos hω₀]
    have hw : w ≠ 0 := by
      intro h0
      rw [h0] at hlt
      norm_num at hlt
      linarith
    have hsq : 0 < w ^ 2 := sq_pos_of_ne_zero hw
    rw [rayleigh_power_eq hω₀.ne' m r τ w]
    exact mul_neg_of_pos_of_neg hk
      (mul_neg_of_neg_of_pos (by linarith : ω₀ ^ 2 - w ^ 2 < 0) hsq)

/-- With positive physical parameters, the per-site Rayleigh power vanishes
exactly at the stationary speed and the two natural speeds. -/
theorem rayleigh_power_eq_zero_iff {m r τ ω₀ w : ℝ}
    (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀) :
    m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2 = 0 ↔
      w = 0 ∨ |w| = ω₀ := by
  have hc : m * r / (τ * ω₀ ^ 2) ≠ 0 := by positivity
  rw [rayleigh_power_eq hω₀.ne' m r τ w, mul_eq_zero, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h hc
    · right
      have habs := (sq_eq_sq_iff_abs_eq_abs ω₀ w).1 h
      rw [abs_of_pos hω₀] at habs
      exact habs.symm
    · left
      exact (sq_eq_zero_iff).1 h
  · rintro (h | h)
    · exact Or.inr (Or.inr (by rw [h]; ring))
    · exact Or.inr (Or.inl ((sq_eq_sq_iff_abs_eq_abs ω₀ w).2 (by
        rw [abs_of_pos hω₀]; exact h.symm)))

/-- On a nonempty symmetric lattice, speeds everywhere strictly between rest
and the natural frequency make the total energy strictly increase: the
natural frequency `ω₀ = v₀/r₀` is the exact injection threshold,
independently of the coupling. -/
theorem lattice_rayleigh_power_pos_of_lt {ι : Type*} [Fintype ι] [Nonempty ι]
    (m r τ ω₀ : ℝ) (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀)
    (w : ι → ℝ) (hw : ∀ i, w i ≠ 0 ∧ |w i| < ω₀) :
    0 < latticeRayleighPower m r τ ω₀ w := by
  unfold latticeRayleighPower
  refine Finset.sum_pos' (fun i _ => ?_)
    ⟨Classical.arbitrary ι, Finset.mem_univ _, ?_⟩
  · exact le_of_lt ((rayleigh_power_pos_iff (w := w i) hm hr hτ hω₀).2 (hw i))
  · exact (rayleigh_power_pos_iff (w := w (Classical.arbitrary ι)) hm hr hτ hω₀).2
      (hw (Classical.arbitrary ι))

/-- On a nonempty symmetric lattice, speeds everywhere strictly above the
natural frequency make the total energy strictly decrease. -/
theorem lattice_rayleigh_power_neg_of_gt {ι : Type*} [Fintype ι] [Nonempty ι]
    (m r τ ω₀ : ℝ) (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀)
    (w : ι → ℝ) (hw : ∀ i, ω₀ < |w i|) :
    latticeRayleighPower m r τ ω₀ w < 0 := by
  unfold latticeRayleighPower
  have hneg : ∑ i, m * r / τ * (1 - w i ^ 2 / ω₀ ^ 2) * w i ^ 2
      = -∑ i, -(m * r / τ * (1 - w i ^ 2 / ω₀ ^ 2) * w i ^ 2) := by
    rw [Finset.sum_neg_distrib]
    ring
  rw [hneg, neg_lt_zero]
  refine Finset.sum_pos' (fun i _ => ?_)
    ⟨Classical.arbitrary ι, Finset.mem_univ _, ?_⟩
  · refine le_of_lt ?_
    have hper := (rayleigh_power_neg_iff (w := w i) hm hr hτ hω₀).2 (hw i)
    linarith
  · have hper := (rayleigh_power_neg_iff
        (w := w (Classical.arbitrary ι)) hm hr hτ hω₀).2 (hw (Classical.arbitrary ι))
    linarith

/-! ## Uniform power bounds and energy bounds -/

/-- Per-site dissipation bound: at speeds at least `ω₀ + δ`, the per-site
Rayleigh power is bounded above by the explicit negative rate obtained at
the boundary speed, because the quartic factor is decreasing above the
natural frequency. -/
theorem rayleigh_power_le_of_supernatural (m r τ ω₀ δ w : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀) (hδ : 0 < δ)
    (hw : ω₀ + δ ≤ |w|) :
    m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2
      ≤ -((m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2 * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) := by
  rw [rayleigh_power_eq hω₀.ne' m r τ w]
  have hω₀2 : 0 < ω₀ ^ 2 := by positivity
  have hs0 : ω₀ ^ 2 ≤ (ω₀ + δ) ^ 2 := by
    have hexp : (ω₀ + δ) ^ 2 = ω₀ ^ 2 + 2 * ω₀ * δ + δ ^ 2 := by ring
    have hpos : 0 < 2 * ω₀ * δ := by positivity
    rw [hexp]
    linarith [sq_nonneg δ]
  have hw2 : (ω₀ + δ) ^ 2 ≤ w ^ 2 := by
    have habs : (ω₀ + δ) ^ 2 ≤ |w| ^ 2 :=
      sq_le_sq' (by linarith : -|w| ≤ ω₀ + δ) hw
    rwa [sq_abs] at habs
  have hsplit : (ω₀ ^ 2 - w ^ 2) * w ^ 2 - (ω₀ ^ 2 - (ω₀ + δ) ^ 2) * (ω₀ + δ) ^ 2
      = (w ^ 2 - (ω₀ + δ) ^ 2) * (ω₀ ^ 2 - w ^ 2 - (ω₀ + δ) ^ 2) := by
    ring
  have hprod : (w ^ 2 - (ω₀ + δ) ^ 2) * (ω₀ ^ 2 - w ^ 2 - (ω₀ + δ) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hbound : (ω₀ ^ 2 - w ^ 2) * w ^ 2
      ≤ (ω₀ ^ 2 - (ω₀ + δ) ^ 2) * (ω₀ + δ) ^ 2 := by
    linarith
  have hk : 0 ≤ m * r / (τ * ω₀ ^ 2) := by positivity
  calc (m * r / (τ * ω₀ ^ 2)) * ((ω₀ ^ 2 - w ^ 2) * w ^ 2)
      ≤ (m * r / (τ * ω₀ ^ 2)) * ((ω₀ ^ 2 - (ω₀ + δ) ^ 2) * (ω₀ + δ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbound hk
    _ = -((m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2 * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) := by
        ring

/-- Per-site injection bound: at speeds in `[ε, ω₀ - δ]`, the per-site
Rayleigh power is bounded below by the explicit positive rate obtained at
the strip corners. -/
theorem rayleigh_power_ge_of_subnatural (m r τ ω₀ ε δ w : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hτ : 0 < τ) (hω₀ : 0 < ω₀) (hε : 0 < ε)
    (hδ : 0 < δ) (hδε : δ ≤ ω₀) (h1 : ε ≤ |w|) (h2 : |w| ≤ ω₀ - δ) :
    (m * r / (τ * ω₀ ^ 2)) * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2))
      ≤ m * r / τ * (1 - w ^ 2 / ω₀ ^ 2) * w ^ 2 := by
  rw [rayleigh_power_eq hω₀.ne' m r τ w]
  have hε2 : ε ^ 2 ≤ w ^ 2 := by
    have habs : ε ^ 2 ≤ |w| ^ 2 := sq_le_sq' (by linarith : -|w| ≤ ε) h1
    rwa [sq_abs] at habs
  have hw2 : w ^ 2 ≤ (ω₀ - δ) ^ 2 := by
    obtain ⟨hleft, hright⟩ := abs_le.1 h2
    exact sq_le_sq' hleft hright
  have hstrip : 0 ≤ ω₀ ^ 2 - (ω₀ - δ) ^ 2 := by
    have hexp : (ω₀ - δ) ^ 2 = ω₀ ^ 2 - 2 * ω₀ * δ + δ ^ 2 := by ring
    have hkey : δ ^ 2 ≤ ω₀ * δ := by
      calc δ ^ 2 = δ * δ := by ring
        _ ≤ δ * ω₀ := mul_le_mul_of_nonneg_left hδε hδ.le
        _ = ω₀ * δ := by ring
    rw [hexp]
    linarith [hkey, sq_nonneg δ]
  have hstep : ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2) ≤ w ^ 2 * (ω₀ ^ 2 - w ^ 2) := by
    have h₁ : ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2)
        ≤ w ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2) :=
      mul_le_mul_of_nonneg_right hε2 hstrip
    have h₂ : w ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2) ≤ w ^ 2 * (ω₀ ^ 2 - w ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg w)
    linarith
  have hbound : ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2) ≤ (ω₀ ^ 2 - w ^ 2) * w ^ 2 := by
    rw [mul_comm (ω₀ ^ 2 - w ^ 2) (w ^ 2)]
    exact hstep
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The signed pair potential of equation (24) is uniformly bounded in both
phases by twice the sum of the absolute coefficient values. -/
theorem abs_gkPairPotential_le (a b x y : ℝ) :
    |gkPairPotential a b x y| ≤ 2 * (|a| + |b|) := by
  rw [gkPairPotential_eq]
  have h1 : |(a / 2) * cosGapSq x y| ≤ |a| / 2 * 4 := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (cosGapSq_nonneg x y)]
    exact mul_le_mul_of_nonneg_left (cosGapSq_le_four x y) (by positivity)
  have h2 : |(b / 2) * sinGapSq x y| ≤ |b| / 2 * 4 := by
    rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (sinGapSq_nonneg x y)]
    exact mul_le_mul_of_nonneg_left (sinGapSq_le_four x y) (by positivity)
  calc |(a / 2) * cosGapSq x y + (b / 2) * sinGapSq x y|
      ≤ |(a / 2) * cosGapSq x y| + |(b / 2) * sinGapSq x y| := abs_add_le _ _
    _ ≤ |a| / 2 * 4 + |b| / 2 * 4 := add_le_add h1 h2
    _ = 2 * (|a| + |b|) := by ring

/-- The total lattice pair potential is uniformly bounded by twice the site
count times the sum of the absolute coefficient values. -/
theorem abs_latticePairPotential_le {ι : Type*} [Fintype ι] (a b : ℝ)
    (left right : ι → ι) (φ : ι → ℝ) :
    |latticePairPotential a b left right φ|
      ≤ 2 * (Fintype.card ι : ℝ) * (|a| + |b|) := by
  have hterm : ∀ i : ι, |(1 / 2) * (gkPairPotential a b (φ i) (φ (left i))
      + gkPairPotential a b (φ i) (φ (right i)))| ≤ 2 * (|a| + |b|) := by
    intro i
    have h1 := abs_gkPairPotential_le a b (φ i) (φ (left i))
    have h2 := abs_gkPairPotential_le a b (φ i) (φ (right i))
    have hsum : |gkPairPotential a b (φ i) (φ (left i))|
        + |gkPairPotential a b (φ i) (φ (right i))| ≤ 4 * (|a| + |b|) := by
      linarith
    calc |1 / 2 * (gkPairPotential a b (φ i) (φ (left i))
          + gkPairPotential a b (φ i) (φ (right i)))|
        = 1 / 2 * |gkPairPotential a b (φ i) (φ (left i))
            + gkPairPotential a b (φ i) (φ (right i))| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      _ ≤ 1 / 2 * (|gkPairPotential a b (φ i) (φ (left i))|
            + |gkPairPotential a b (φ i) (φ (right i))|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num : (0:ℝ) ≤ 1 / 2)
      _ ≤ 1 / 2 * (4 * (|a| + |b|)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 1 / 2)
      _ = 2 * (|a| + |b|) := by ring
  unfold latticePairPotential
  calc |∑ i, (1 / 2) * (gkPairPotential a b (φ i) (φ (left i))
        + gkPairPotential a b (φ i) (φ (right i)))|
      ≤ ∑ i, |(1 / 2) * (gkPairPotential a b (φ i) (φ (left i))
          + gkPairPotential a b (φ i) (φ (right i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * (|a| + |b|) := Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * (Fintype.card ι : ℝ) * (|a| + |b|) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

/-- The angular-velocity kinetic energy is nonnegative for nonnegative
inertia parameters. -/
theorem lattice_kinetic_energy_nonneg {ι : Type*} [Fintype ι] {m r : ℝ}
    (hm : 0 ≤ m) (hr : 0 ≤ r) (ω : ι → ℝ) :
    0 ≤ latticeKineticEnergy m r ω := by
  unfold latticeKineticEnergy
  refine Finset.sum_nonneg fun i _ => ?_
  have hmr : 0 ≤ m * r / 2 := by positivity
  exact mul_nonneg hmr (sq_nonneg _)

/-- On a bounded velocity range the kinetic energy is capped by the square
of the velocity cap times the site count. -/
theorem lattice_kinetic_energy_le_of_abs_le {ι : Type*} [Fintype ι] {m r : ℝ}
    (hm : 0 ≤ m) (hr : 0 ≤ r) (ω : ι → ℝ) (W : ℝ) (hW : ∀ i, |ω i| ≤ W) :
    latticeKineticEnergy m r ω ≤ (Fintype.card ι : ℝ) * (m * r / 2) * W ^ 2 := by
  have hmr : 0 ≤ m * r / 2 := by positivity
  have hterm : ∀ i : ι, m * r / 2 * ω i ^ 2 ≤ m * r / 2 * W ^ 2 := by
    intro i
    obtain ⟨hleft, hright⟩ := abs_le.1 (hW i)
    have hsq : ω i ^ 2 ≤ W ^ 2 := sq_le_sq' hleft hright
    exact mul_le_mul_of_nonneg_left hsq hmr
  calc latticeKineticEnergy m r ω
      ≤ ∑ i, m * r / 2 * W ^ 2 := by
        unfold latticeKineticEnergy
        exact Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι : ℝ) * (m * r / 2) * W ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

/-- The total energy of the active lattice is uniformly bounded below by
the potential bound alone, the kinetic energy being nonnegative. -/
theorem lattice_energy_lower_bound {ι : Type*} [Fintype ι] {a b m r : ℝ}
    {left right : ι → ι} (hm : 0 ≤ m) (hr : 0 ≤ r) (φ ω : ι → ℝ) :
    -2 * (Fintype.card ι : ℝ) * (|a| + |b|)
      ≤ latticeEnergy a b m r left right φ ω := by
  have hpot := abs_latticePairPotential_le a b left right φ
  have hkin := lattice_kinetic_energy_nonneg hm hr ω
  have hpotge : -|latticePairPotential a b left right φ|
      ≤ latticePairPotential a b left right φ := by
    rw [← abs_neg (latticePairPotential a b left right φ), neg_le]
    exact le_abs_self _
  unfold latticeEnergy
  linarith

/-! ## Quantitative escape from the strictly supra- and subnatural ranges -/

/-- A real curve whose derivative is bounded above by `-c` on a compact
interval drops by at least `c` times the interval length. -/
private theorem hasDeriv_slope_le_drop (f p : ℝ → ℝ) (c t₀ t₁ : ℝ)
    (ht : t₀ < t₁)
    (h : ∀ t ∈ Icc t₀ t₁, HasDerivAt f (p t) t)
    (hle : ∀ t ∈ Icc t₀ t₁, p t ≤ -c) :
    f t₁ + c * (t₁ - t₀) ≤ f t₀ := by
  have hcont : ContinuousOn f (Icc t₀ t₁) := fun t ht' =>
    ((h t ht').continuousAt).continuousWithinAt
  obtain ⟨s, hsmem, hs⟩ := exists_hasDerivAt_eq_slope f p ht hcont
    (fun t ht' => h t (Ioo_subset_Icc_self ht'))
  rw [eq_div_iff (sub_ne_zero.2 ht.ne')] at hs
  have hps : p s ≤ -c := hle s (Ioo_subset_Icc_self hsmem)
  have hΔ : 0 < t₁ - t₀ := sub_pos.2 ht
  have hX : p s * (t₁ - t₀) ≤ -c * (t₁ - t₀) :=
    mul_le_mul_of_nonneg_right hps hΔ.le
  linarith

/-- A real curve whose derivative is bounded below by `c` on a compact
interval gains at least `c` times the interval length. -/
private theorem hasDeriv_slope_ge_gain (f p : ℝ → ℝ) (c t₀ t₁ : ℝ)
    (ht : t₀ < t₁)
    (h : ∀ t ∈ Icc t₀ t₁, HasDerivAt f (p t) t)
    (hge : ∀ t ∈ Icc t₀ t₁, c ≤ p t) :
    f t₀ + c * (t₁ - t₀) ≤ f t₁ := by
  have h' : ∀ t ∈ Icc t₀ t₁,
      HasDerivAt (fun t => -f t) (-(p t)) t := fun t ht' => (h t ht').neg
  have hle : ∀ t ∈ Icc t₀ t₁, -(p t) ≤ -c := fun t ht' => neg_le_neg (hge t ht')
  have hdrop := hasDeriv_slope_le_drop (fun t => -f t) (fun t => -p t) c t₀ t₁ ht h' hle
  linarith

/-- Quantitative escape from the strictly supernatural speed range: a
trajectory of the active lattice equation whose speeds all stay at least
`ω₀ + δ` loses energy at an explicit uniform rate, so it can persist for at
most the bounded time `(E(t₀) + 2 N (|a| + |b|)) / rate`. Only neighborhoods
of the stationary speed `0` and of the natural speeds `±ω₀` admit
arbitrarily long persistence. -/
theorem lattice_energy_escape_bound_above {ι : Type*} [Fintype ι]
    (a b m r τ ω₀ δ : ℝ) (left right : ι → ι)
    (hinv : MutuallyInverse left right) (hm : 0 < m) (hr : 0 < r)
    (hτ : 0 < τ) (hω₀ : 0 < ω₀) (hδ : 0 < δ)
    (Φ W : ι → ℝ → ℝ) (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hkin : ∀ t ∈ Icc t₀ t₁, ∀ i, HasDerivAt (Φ i) (W i t) t)
    (hvel : ∀ t ∈ Icc t₀ t₁, ∀ i, HasDerivAt (W i)
      (rayleighAngularAcceleration τ ω₀ (W i t)
        + latticeForceSum a b left right (fun i => Φ i t) i / (m * r)) t)
    (hspeed : ∀ t ∈ Icc t₀ t₁, ∀ i, ω₀ + δ ≤ |W i t|) :
    (Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
        * ((ω₀ + δ) ^ 2 - ω₀ ^ 2) * (t₁ - t₀)
      ≤ latticeEnergy a b m r left right (fun i => Φ i t₀) (fun i => W i t₀)
        + 2 * (Fintype.card ι : ℝ) * (|a| + |b|) := by
  have hmr : m * r ≠ 0 := mul_ne_zero hm.ne' hr.ne'
  have hbal : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun t => latticeEnergy a b m r left right (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t)) t := by
    intro t ht'
    refine lattice_energy_balance a b m r τ ω₀ left right hinv Φ W
      (fun i t' => rayleighAngularAcceleration τ ω₀ (W i t')
        + latticeForceSum a b left right (fun i => Φ i t') i / (m * r)) t
      (hkin t ht') (hvel t ht') fun i => ?_
    rw [mul_add, mul_div_cancel₀ _ hmr]
  have hpowle : ∀ t ∈ Icc t₀ t₁, latticeRayleighPower m r τ ω₀ (fun i => W i t)
      ≤ -((Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
          * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) := by
    intro t ht'
    unfold latticeRayleighPower
    have hper : ∀ i : ι, m * r / τ * (1 - W i t ^ 2 / ω₀ ^ 2) * W i t ^ 2
        ≤ -((m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2 * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) :=
      fun i => rayleigh_power_le_of_supernatural m r τ ω₀ δ (W i t)
        hm hr hτ hω₀ hδ (hspeed t ht' i)
    have hsum : ∑ i : ι, -((m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
          * ((ω₀ + δ) ^ 2 - ω₀ ^ 2))
        = -((Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
            * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) := by
      rw [Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring
    calc ∑ i, m * r / τ * (1 - W i t ^ 2 / ω₀ ^ 2) * W i t ^ 2
        ≤ ∑ i, -((m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
            * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = -((Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
            * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) := hsum
  have hdrop := hasDeriv_slope_le_drop
    (fun t => latticeEnergy a b m r left right (fun i => Φ i t) (fun i => W i t))
    (fun t => latticeRayleighPower m r τ ω₀ (fun i => W i t))
    ((Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2)) * (ω₀ + δ) ^ 2
      * ((ω₀ + δ) ^ 2 - ω₀ ^ 2)) t₀ t₁ ht hbal hpowle
  have hlow : -2 * (Fintype.card ι : ℝ) * (|a| + |b|)
      ≤ latticeEnergy a b m r left right (fun i => Φ i t₁) (fun i => W i t₁) :=
    lattice_energy_lower_bound hm.le hr.le _ _
  linarith

/-- Quantitative escape from the strictly subnatural speed band: a
trajectory of the active lattice equation whose speeds all stay inside
`[ε, ω₀ - δ]` gains energy at an explicit uniform positive rate, so its
energy cannot remain below the band's kinetic cap plus the potential bound;
equivalently, speeds cannot stay in the injection band forever. This is the
quantitative energy-injection half of the threshold mechanism. -/
theorem lattice_energy_escape_bound_below {ι : Type*} [Fintype ι]
    (a b m r τ ω₀ ε δ : ℝ) (left right : ι → ι)
    (hinv : MutuallyInverse left right) (hm : 0 < m) (hr : 0 < r)
    (hτ : 0 < τ) (hω₀ : 0 < ω₀) (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ω₀)
    (Φ W : ι → ℝ → ℝ) (t₀ t₁ : ℝ) (ht : t₀ < t₁)
    (hkin : ∀ t ∈ Icc t₀ t₁, ∀ i, HasDerivAt (Φ i) (W i t) t)
    (hvel : ∀ t ∈ Icc t₀ t₁, ∀ i, HasDerivAt (W i)
      (rayleighAngularAcceleration τ ω₀ (W i t)
        + latticeForceSum a b left right (fun i => Φ i t) i / (m * r)) t)
    (hspeed : ∀ t ∈ Icc t₀ t₁, ∀ i, ε ≤ |W i t| ∧ |W i t| ≤ ω₀ - δ) :
    latticeEnergy a b m r left right (fun i => Φ i t₀) (fun i => W i t₀)
      + (Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2))
        * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2)) * (t₁ - t₀)
      ≤ (Fintype.card ι : ℝ) * (m * r / 2) * (ω₀ - δ) ^ 2
        + 2 * (Fintype.card ι : ℝ) * (|a| + |b|) := by
  have hmr : m * r ≠ 0 := mul_ne_zero hm.ne' hr.ne'
  have hbal : ∀ t ∈ Icc t₀ t₁, HasDerivAt
      (fun t => latticeEnergy a b m r left right (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t)) t := by
    intro t ht'
    refine lattice_energy_balance a b m r τ ω₀ left right hinv Φ W
      (fun i t' => rayleighAngularAcceleration τ ω₀ (W i t')
        + latticeForceSum a b left right (fun i => Φ i t') i / (m * r)) t
      (hkin t ht') (hvel t ht') fun i => ?_
    rw [mul_add, mul_div_cancel₀ _ hmr]
  have hpowge : ∀ t ∈ Icc t₀ t₁, (Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2))
      * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2))
      ≤ latticeRayleighPower m r τ ω₀ (fun i => W i t) := by
    intro t ht'
    unfold latticeRayleighPower
    have hper : ∀ i : ι, (m * r / (τ * ω₀ ^ 2))
        * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2))
        ≤ m * r / τ * (1 - W i t ^ 2 / ω₀ ^ 2) * W i t ^ 2 :=
      fun i => rayleigh_power_ge_of_subnatural m r τ ω₀ ε δ (W i t)
        hm hr hτ hω₀ hε hδ hδε (hspeed t ht' i).1 (hspeed t ht' i).2
    have hsum : ∑ i : ι, (m * r / (τ * ω₀ ^ 2))
        * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2))
        = (Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2))
          * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring
    calc (Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2))
        * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2))
        = ∑ i, (m * r / (τ * ω₀ ^ 2))
            * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2)) := hsum.symm
      _ ≤ ∑ i, m * r / τ * (1 - W i t ^ 2 / ω₀ ^ 2) * W i t ^ 2 :=
          Finset.sum_le_sum fun i _ => hper i
  have hgain := hasDeriv_slope_ge_gain
    (fun t => latticeEnergy a b m r left right (fun i => Φ i t) (fun i => W i t))
    (fun t => latticeRayleighPower m r τ ω₀ (fun i => W i t))
    ((Fintype.card ι : ℝ) * (m * r / (τ * ω₀ ^ 2))
      * (ε ^ 2 * (ω₀ ^ 2 - (ω₀ - δ) ^ 2))) t₀ t₁ ht hbal hpowge
  have hcap := lattice_kinetic_energy_le_of_abs_le hm.le hr.le (fun i => W i t₁)
    (ω₀ - δ) (fun i => (hspeed t₁ (Set.mem_Icc.2 ⟨ht.le, le_rfl⟩) i).2)
  have hcappot := abs_latticePairPotential_le a b left right (fun i => Φ i t₁)
  have hpotle : latticePairPotential a b left right (fun i => Φ i t₁)
      ≤ 2 * (Fintype.card ι : ℝ) * (|a| + |b|) := (abs_le.1 hcappot).2
  have hEt1 : latticeEnergy a b m r left right (fun i => Φ i t₁) (fun i => W i t₁)
      = latticeKineticEnergy m r (fun i => W i t₁)
        + latticePairPotential a b left right (fun i => Φ i t₁) := rfl
  linarith

/-! ## Locked natural-rotation branches -/

/-- The Rayleigh drift vanishes at any natural speed, that is, at any angular
velocity whose square equals `ω₀ ^ 2`; the degenerate case `ω₀ = 0` is
included through the arithmetic of division by zero. -/
theorem rayleighAngularAcceleration_eq_zero_of_nat_square (τ ω₀ Ω : ℝ)
    (hΩ : Ω ^ 2 = ω₀ ^ 2) : rayleighAngularAcceleration τ ω₀ Ω = 0 := by
  unfold rayleighAngularAcceleration
  by_cases h0 : ω₀ = 0
  · have hΩ0 : Ω = 0 := by
      have hs : Ω ^ 2 = 0 := by rw [hΩ, h0]; ring
      exact (sq_eq_zero_iff).1 hs
    rw [hΩ0, mul_zero]
  · rw [hΩ, div_self (pow_ne_zero 2 h0), sub_self]
    ring

/-- At a phase-locked constant phase pattern the coupling force sum vanishes
identically, whatever the neighbour maps are: synchronized phases are a
critical point of the lattice pair potential. -/
theorem latticeForceSum_const_eq_zero {ι : Type*} (a b φstar : ℝ)
    (left right : ι → ι) (i : ι) :
    latticeForceSum a b left right (fun _ => φstar) i = 0 := by
  simp only [latticeForceSum, gk_pair_force_self_eq_zero, add_zero]

/-- The locked natural-rotation branches: a phase-locked lattice rotating
rigidly at a natural speed `Ω` with `Ω ^ 2 = ω₀ ^ 2` solves the active
lattice equation exactly, with vanishing acceleration at every site. -/
theorem synchronized_natural_rotation_rhs_eq_zero {ι : Type*}
    (a b m r τ ω₀ Ω φstar : ℝ) (left right : ι → ι) (hΩ : Ω ^ 2 = ω₀ ^ 2)
    (i : ι) :
    rayleighAngularAcceleration τ ω₀ Ω
      + latticeForceSum a b left right (fun _ : ι => φstar) i / (m * r) = 0 := by
  rw [rayleighAngularAcceleration_eq_zero_of_nat_square τ ω₀ Ω hΩ,
    latticeForceSum_const_eq_zero a b φstar left right i, zero_div, add_zero]

/-- The total Rayleigh power of a lattice rotating rigidly at a natural
speed vanishes: the Rayleigh term neither injects nor dissipates energy on
the locked natural-rotation branches. -/
theorem latticeRayleighPower_const_eq_zero {ι : Type*} [Fintype ι]
    (m r τ ω₀ Ω : ℝ) (hΩ : Ω ^ 2 = ω₀ ^ 2) :
    latticeRayleighPower m r τ ω₀ (fun _ : ι => Ω) = 0 := by
  by_cases h0 : ω₀ = 0
  · have hΩ0 : Ω = 0 := by
      have hs : Ω ^ 2 = 0 := by rw [hΩ, h0]; ring
      exact (sq_eq_zero_iff).1 hs
    unfold latticeRayleighPower
    rw [hΩ0]
    simp
  · unfold latticeRayleighPower
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [rayleigh_power_eq h0 m r τ Ω, hΩ, sub_self]
    ring

/-- Along a locked natural-rotation branch the lattice energy is exactly
constant in time: the Rayleigh power vanishes at the natural speeds and the
locked potential stays critical, so the energy balance gives a zero
derivative. -/
theorem synchronized_natural_rotation_energy_constant {ι : Type*} [Fintype ι]
    (a b m r τ ω₀ Ω φstar : ℝ) (left right : ι → ι)
    (hinv : MutuallyInverse left right) (hΩ : Ω ^ 2 = ω₀ ^ 2) (t₀ : ℝ) :
    HasDerivAt (fun t => latticeEnergy a b m r left right
        (fun _ : ι => φstar + Ω * t) (fun _ : ι => Ω))
      0 t₀ := by
  have hkin : ∀ i : ι, HasDerivAt (fun t => φstar + Ω * t) Ω t₀ := fun _ =>
    HasDerivAt.congr_deriv
      ((hasDerivAt_const t₀ φstar).add ((hasDerivAt_id t₀).const_mul Ω)) (by ring)
  have hvel : ∀ i : ι, HasDerivAt (fun _ : ℝ => Ω) 0 t₀ := fun _ =>
    hasDerivAt_const t₀ Ω
  have hacc : ∀ i : ι, m * r * 0
      = m * r * rayleighAngularAcceleration τ ω₀ Ω
        + latticeForceSum a b left right (fun _ : ι => φstar + Ω * t₀) i := by
    intro i
    rw [mul_zero, rayleighAngularAcceleration_eq_zero_of_nat_square τ ω₀ Ω hΩ,
      latticeForceSum_const_eq_zero a b (φstar + Ω * t₀) left right i, mul_zero,
      add_zero]
  refine HasDerivAt.congr_deriv
    (lattice_energy_balance a b m r τ ω₀ left right hinv
      (fun _ : ι => fun t : ℝ => φstar + Ω * t) (fun _ : ι => fun _ : ℝ => Ω)
      (fun _ : ι => fun _ : ℝ => 0) t₀ hkin hvel hacc) ?_
  exact latticeRayleighPower_const_eq_zero m r τ ω₀ Ω hΩ

/-! ## Boundary of the gradient-flow approximation -/

/-- A real function differentiable everywhere with a constant derivative is
affine: the difference between any two base points with the left one smaller
equals the constant derivative times the increment. -/
private theorem deriv_const_slope_eq {f : ℝ → ℝ} (c x₀ x₁ : ℝ) (hx : x₀ < x₁)
    (h : ∀ x, HasDerivAt f c x) : f x₁ - f x₀ = c * (x₁ - x₀) := by
  have hcont : ContinuousOn f (Icc x₀ x₁) := fun t ht' =>
    ((h t).continuousAt).continuousWithinAt
  obtain ⟨s, hsmem, hs⟩ := exists_hasDerivAt_eq_slope f (fun _ => c) hx hcont
    (fun t _ht' => h t)
  rw [eq_div_iff (sub_ne_zero.2 hx.ne')] at hs
  exact hs.symm

/-- The active second-order lattice field is not the negative gradient of
any scalar potential on the full phase-velocity state space. A potential
would make the slice along any single site's phase-velocity directions
simultaneously affine in that site's phase (with slope minus its velocity,
by the kinematic equation) and `2π`-periodic in the same phase (because the
phase re-entering is identified by `latticeForceSum_update_self_add_two_pi`);
comparing the two velocity curves then forces the coupling force sum to grow
by `2π m r` per period, contradicting periodicity whenever `m r ≠ 0`, and
for `m r = 0` the velocity slopes of the two frozen-phase curves coincide,
forcing the same contradiction through the kinematic slope alone. This
delimits the gradient-flow approximation of the paper's coarse-grained
description. -/
theorem not_active_lattice_potential_flow {ι : Type*} [Nonempty ι] [DecidableEq ι]
    (a b m r τ ω₀ : ℝ) (left right : ι → ι) :
    ¬ ∃ G : (ι → ℝ) → (ι → ℝ) → ℝ,
      ∀ (ψ ν : ι → ℝ) (j : ι) (x y : ℝ),
        HasDerivAt (fun x' => G (Function.update ψ j x') ν) (-(ν j)) x ∧
        HasDerivAt (fun y' => G ψ (Function.update ν j y'))
          (-(rayleighAngularAcceleration τ ω₀ (ν j)
            + latticeForceSum a b left right ψ j / (m * r))) y := by
  rintro ⟨G, hG⟩
  have j := Classical.arbitrary ι
  have hdx : ∀ x y : ℝ, HasDerivAt
      (fun x' => G (Function.update (fun _ : ι => 0) j x')
        (Function.update (fun _ : ι => 0) j y)) (-y) x := by
    intro x y
    have h := (hG (Function.update (fun _ : ι => 0) j x)
      (Function.update (fun _ : ι => 0) j y) j x y).1
    simp only [Function.update_idem, Function.update_self] at h
    exact h
  have hdy : ∀ x y : ℝ, HasDerivAt
      (fun y' => G (Function.update (fun _ : ι => 0) j x)
        (Function.update (fun _ : ι => 0) j y'))
      (-(rayleighAngularAcceleration τ ω₀ y
        + latticeForceSum a b left right
          (Function.update (fun _ : ι => 0) j x) j / (m * r))) y := by
    intro x y
    have h := (hG (Function.update (fun _ : ι => 0) j x)
      (Function.update (fun _ : ι => 0) j y) j x y).2
    simp only [Function.update_idem, Function.update_self] at h
    exact h
  have hint : ∀ y : ℝ,
      G (Function.update (fun _ : ι => 0) j (2 * Real.pi))
        (Function.update (fun _ : ι => 0) j y)
      - G (Function.update (fun _ : ι => 0) j 0)
        (Function.update (fun _ : ι => 0) j y)
      = -y * (2 * Real.pi) := by
    intro y
    have h := deriv_const_slope_eq (-y) 0 (2 * Real.pi) (by positivity) (hdx · y)
    rw [sub_zero] at h
    exact h
  have hdrop : ∀ y : ℝ, HasDerivAt
      (fun y' => G (Function.update (fun _ : ι => 0) j (2 * Real.pi))
          (Function.update (fun _ : ι => 0) j y')
        - G (Function.update (fun _ : ι => 0) j 0)
          (Function.update (fun _ : ι => 0) j y'))
      ((latticeForceSum a b left right (Function.update (fun _ : ι => 0) j 0) j
        - latticeForceSum a b left right
          (Function.update (fun _ : ι => 0) j (2 * Real.pi)) j) / (m * r)) y := by
    intro y
    refine HasDerivAt.congr_deriv
      (HasDerivAt.sub (hdy (2 * Real.pi) y) (hdy 0 y)) ?_
    rw [sub_div]
    ring
  have hper : latticeForceSum a b left right
      (Function.update (fun _ : ι => 0) j (2 * Real.pi)) j
    = latticeForceSum a b left right (Function.update (fun _ : ι => 0) j 0) j := by
    have hkey := latticeForceSum_update_self_add_two_pi a b left right
      (Function.update (fun _ : ι => 0) j 0) j
    simp only [Function.update_self, zero_add, Function.update_idem] at hkey
    exact hkey
  have hk := deriv_const_slope_eq
    ((latticeForceSum a b left right (Function.update (fun _ : ι => 0) j 0) j
      - latticeForceSum a b left right
        (Function.update (fun _ : ι => 0) j (2 * Real.pi)) j) / (m * r)) 0 1
    (by norm_num) hdrop
  rw [hint 1, hint 0, hper, sub_self, zero_div] at hk
  norm_num at hk

end Qatlib.Papers.HydroSpinLatt21.GKModel

end
