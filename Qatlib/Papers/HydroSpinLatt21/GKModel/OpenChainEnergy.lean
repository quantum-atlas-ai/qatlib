/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.LatticeEnergy

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact energy balance of the active GK lattice on open chains

[Saenz2021HydroSpinLattices], Methods equations (23)-(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
The experimental one-dimensional hydrodynamic spin lattices of the paper are
open chains with aperiodic boundaries (N = 20 and N = 28 sites): interior
sites have two neighbours while each endpoint has a single one. Such
adjacencies admit no pair of mutually inverse neighbour maps, so the energy
balance of `Qatlib.Papers.HydroSpinLatt21.GKModel.LatticeEnergy` — stated
for mutual-inverse (periodic-type) lattices — does not cover them. This file
proves the same exact energy identity for finite lattices whose adjacency is
given by symmetric neighbour finsets, and instantiates it explicitly for the
open chain on `Fin n`.

## Main results

* `open_edge_sum_transpose` — over a symmetric finset adjacency, summing
  `g i j` over all ordered adjacency pairs equals summing the transposed
  `g j i`. The proof converts both sums to indicator sums over the full
  index type, exchanges the two summations by `Finset.sum_comm`, and
  transports the membership condition by the symmetry hypothesis: the
  symmetrization is genuinely proved, not assumed.
* `open_pair_potential_hasDerivAt` — the chain rule on the half-weighted
  pair potential of equation (24): along any differentiable family of phase
  curves its derivative is exactly the negative coupling power, the half
  weights combining with the transpose identity so that each unordered pair
  contributes one full gradient pairing.
* `open_energy_balance` — for any trajectory of the second-order active
  equation (23) assembled over a symmetric finset adjacency, the derivative
  of the energy (angular-velocity kinetic energy plus half-weighted pair
  potential) is exactly the Rayleigh power
  `Σ_i (m r/τ)(1 - ω_i²/ω₀²)ω_i²`. No two-neighbour hypothesis is imposed:
  endpoints with a single neighbour are covered by the same identity.
* `openChainNeighbors`, `openChainNeighbors_symmetric`,
  `openChainNeighbors_left_endpoint_card`,
  `openChainNeighbors_right_endpoint_card`,
  `openChainNeighbors_interior_card`, `openChain_energy_balance` — the
  explicit open chain on `Fin n`: site `i` adjoins exactly the sites whose
  index differs from `i` by one, the adjacency is symmetric, both endpoints
  have exactly one neighbour, interior sites have exactly two, and the
  energy balance applies verbatim.
* `openChainPairPotential_eq_forward` — on the open chain the half-weighted
  ordered-pair potential equals the full-weight sum over strictly forward
  neighbours: each of the `n - 1` chain edges contributes exactly one copy
  of `U`, never two.
* `openChainPairPotential_three` — the three-site receipt: the total pair
  potential is exactly `U(φ₀, φ₁) + U(φ₁, φ₂)`.

## Scope and boundary conditions

The identity proved here lives at the level of the generalized Kuramoto
equation (23), whose pair force is the exact phase gradient of the signed
pair potential (24) — the near-synchronous, `r/L ≪ 1` leading-order force of
the paper's expansion — whatever real coefficients `(a, b)` instantiate it,
including the Bessel coefficients of equations (25) and (26). The full
Bessel azimuthal wave force of the pilot-wave model is *not* the gradient of
any exchange-symmetric pair potential
(`Qatlib.Papers.HydroSpinLatt21.GKModel.wave_force_not_symmetric_pair_gradient`),
so this exact cancellation is a GK-level statement and cannot be promoted to
the full wave force; for trajectories of the full memory dynamics the energy
discrepancy is controlled instead by the acceleration residual and Grönwall
bounds of `Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselGkError`. The
qualitative companions of the balance (threshold signs, escape bounds,
locked natural-rotation branches, non-existence of a potential flow) are
proved in `Qatlib.Papers.HydroSpinLatt21.GKModel.LatticeEnergy` for
mutual-inverse lattices and are not re-proved here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.GKModel

/-! ## Symmetric finset adjacency and the half-weight edge energy -/

/-- The symmetry of a finite adjacency given by neighbour finsets: one site
lists another exactly when the other lists the one. Open chains, periodic
chains and every nearest-neighbour geometry of the paper satisfy this. -/
def SymmetricNeighbors {ι : Type*} (nbrs : ι → Finset ι) : Prop :=
  ∀ i j, j ∈ nbrs i ↔ i ∈ nbrs j

/-- The total signed pair force received by site `i` from all of its
neighbours, each force taken in the receiving site's phase as in the
assembled equation (23). -/
def openForceSum (a b : ℝ) {ι : Type*} (nbrs : ι → Finset ι) (φ : ι → ℝ)
    (i : ι) : ℝ :=
  ∑ j ∈ nbrs i, gkPairForce a b (φ i) (φ j)

/-- The total pair potential with half weight on ordered adjacency pairs,
so that each unordered pair of a symmetric adjacency is counted once in
total. -/
def openPairPotential (a b : ℝ) {ι : Type*} [Fintype ι] (nbrs : ι → Finset ι)
    (φ : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ nbrs i, (1 / 2) * gkPairPotential a b (φ i) (φ j)

/-- The energy of the active lattice over a finite adjacency:
angular-velocity kinetic energy (reused from the mutual-inverse development)
plus the half-weighted pair potential. -/
def openEnergy (a b m r : ℝ) {ι : Type*} [Fintype ι] (nbrs : ι → Finset ι)
    (φ ω : ι → ℝ) : ℝ :=
  latticeKineticEnergy m r ω + openPairPotential a b nbrs φ

/-! ## The transpose identity over symmetric adjacencies -/

/-- A finset equals the filter of the universe by its own membership. -/
private theorem filter_univ_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) :
    Finset.univ.filter (fun j => j ∈ s) = s := by
  ext j
  simp

/-- Double sums over a symmetric adjacency are sums over the full index type
guarded by membership. -/
private theorem sum_guard_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nbrs : ι → Finset ι)
    (F : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ nbrs i, F i j)
      = ∑ i, ∑ j ∈ Finset.univ, if j ∈ nbrs i then F i j else 0 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter (fun j => j ∈ nbrs i) (fun j => F i j), filter_univ_eq]

/-- The transpose identity: over a symmetric finset adjacency, summing `g i j`
over all ordered adjacency pairs equals summing the transposed `g j i`. The
proof exchanges the two summations over the full index type and transports
the membership guard by the symmetry hypothesis; this is the genuinely
proved symmetrization step behind the half-weight edge energy. -/
theorem open_edge_sum_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nbrs : ι → Finset ι)
    (hsym : SymmetricNeighbors nbrs) (g : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ nbrs i, g i j) = (∑ i, ∑ j ∈ nbrs i, g j i) := by
  rw [sum_guard_eq nbrs (fun i j => g i j), sum_guard_eq nbrs (fun i j => g j i),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ∈ nbrs i
  · simp only [(hsym i j).mp h, h]
  · simp only [show ¬ i ∈ nbrs j from fun hc => h ((hsym i j).mpr hc), h]

/-! ## The chain-rule cancellation of the coupling channel -/

/-- The chain-rule cancellation over a symmetric finset adjacency: along any
differentiable family of phase curves, the derivative of the half-weighted
pair potential of equation (24) is exactly the negative of the coupling
power delivered by the pair forces of equation (23). Each ordered pair
contributes the two chain-rule terms of
`gk_pair_potential_hasDerivAt_pair` at half weight, and the transpose
identity identifies the emitting-side halves with the receiving-side halves,
so the potential gradient and the coupling power cancel on each unordered
pair. -/
theorem open_pair_potential_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ℝ)
    (nbrs : ι → Finset ι) (hsym : SymmetricNeighbors nbrs)
    (Φ W : ι → ℝ → ℝ) (t₀ : ℝ) (hΦ : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀) :
    HasDerivAt (fun t => openPairPotential a b nbrs (fun i => Φ i t))
      (-(∑ i, W i t₀ * openForceSum a b nbrs (fun i => Φ i t₀) i)) t₀ := by
  have hsum : HasDerivAt
    (fun t => ∑ i, ∑ j ∈ nbrs i, (1 / 2) * gkPairPotential a b (Φ i t) (Φ j t))
    (∑ i, ∑ j ∈ nbrs i, (1 / 2) * (-(gkPairForce a b (Φ i t₀) (Φ j t₀) * W i t₀
          + gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀))) t₀ :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      (gk_pair_potential_hasDerivAt_pair a b (Φ i) (Φ j) t₀ (W i t₀) (W j t₀)
        (hΦ i) (hΦ j)).const_mul (1 / 2)
  have hinner : ∀ i : ι,
      ∑ j ∈ nbrs i, (1 / 2) * (-(gkPairForce a b (Φ i t₀) (Φ j t₀) * W i t₀
            + gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀))
        = -((1 / 2) * ∑ j ∈ nbrs i, gkPairForce a b (Φ i t₀) (Φ j t₀) * W i t₀
          + (1 / 2) * ∑ j ∈ nbrs i,
              gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀) := by
    intro i
    rw [← Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    ring
  have hS₂ : (∑ i, ∑ j ∈ nbrs i, gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀)
      = (∑ i, ∑ j ∈ nbrs i, gkPairForce a b (Φ i t₀) (Φ j t₀) * W i t₀) :=
    open_edge_sum_transpose nbrs hsym
      (fun i j => gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀)
  have hforce : (∑ i, ∑ j ∈ nbrs i, gkPairForce a b (Φ i t₀) (Φ j t₀) * W i t₀)
      = (∑ i, W i t₀ * openForceSum a b nbrs (fun i => Φ i t₀) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold openForceSum
    rw [← Finset.sum_mul, mul_comm]
  have hsplit : (∑ i, ∑ j ∈ nbrs i, (1 / 2) * (-(gkPairForce a b (Φ i t₀)
            (Φ j t₀) * W i t₀ + gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀)))
      = -((1 / 2) * (∑ i, ∑ j ∈ nbrs i,
              gkPairForce a b (Φ i t₀) (Φ j t₀) * W i t₀)
        + (1 / 2) * (∑ i, ∑ j ∈ nbrs i,
              gkPairForce a b (Φ j t₀) (Φ i t₀) * W j t₀)) := by
    rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_neg_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold openPairPotential
  refine HasDerivAt.congr_deriv hsum ?_
  linarith [hsplit, hS₂, hforce]

/-- The exact energy balance of the second-order active generalized Kuramoto
equation on a finite lattice with a symmetric finset adjacency: along any
trajectory whose phase velocities and accelerations satisfy the active
equation with angular inertia `m r`, the energy (angular-velocity kinetic
energy plus half-weighted pair potential) changes at exactly the Rayleigh
power; the coupling channel cancels identically by
`open_pair_potential_hasDerivAt`. No two-neighbour hypothesis is imposed, so
open chains whose endpoints have a single neighbour are covered, and no sign
or positivity hypothesis is imposed on any parameter. -/
theorem open_energy_balance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b m r τ ω₀ : ℝ)
    (nbrs : ι → Finset ι) (hsym : SymmetricNeighbors nbrs)
    (Φ W Acc : ι → ℝ → ℝ) (t₀ : ℝ)
    (hkin : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀)
    (hvel : ∀ i, HasDerivAt (W i) (Acc i t₀) t₀)
    (hacc : ∀ i, m * r * Acc i t₀
        = m * r * rayleighAngularAcceleration τ ω₀ (W i t₀)
          + openForceSum a b nbrs (fun i => Φ i t₀) i) :
    HasDerivAt (fun t => openEnergy a b m r nbrs (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t₀)) t₀ := by
  have hpot := open_pair_potential_hasDerivAt a b nbrs hsym Φ W t₀ hkin
  have hkinE := lattice_kinetic_energy_hasDerivAt m r W Acc t₀ hvel
  have hsplit : ∀ i : ι,
      m * r * (W i t₀ * Acc i t₀)
        - W i t₀ * openForceSum a b nbrs (fun i => Φ i t₀) i
        = m * r / τ * (1 - W i t₀ ^ 2 / ω₀ ^ 2) * W i t₀ ^ 2 := by
    intro i
    have hkey : m * r * (W i t₀ * Acc i t₀)
        = W i t₀ * (m * r * Acc i t₀) := by ring
    rw [hkey, hacc i, mul_add, mul_sub]
    unfold rayleighAngularAcceleration
    field_simp
    ring
  have hsum : (∑ i, m * r * (W i t₀ * Acc i t₀))
      + -(∑ i, W i t₀ * openForceSum a b nbrs (fun i => Φ i t₀) i)
      = latticeRayleighPower m r τ ω₀ (fun i => W i t₀) := by
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun i _ => hsplit i)]
    simp only [latticeRayleighPower]
  unfold openEnergy
  exact HasDerivAt.congr_deriv (hkinE.add hpot) hsum

/-! ## The explicit open chain on `Fin n` -/

/-- The open-chain adjacency on `Fin n`: site `i` adjoins exactly the sites
whose index differs from `i` by one, so interior sites have two neighbours
and the two endpoints have one. -/
def openChainNeighbors (n : ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j.val + 1 = i.val ∨ j.val = i.val + 1)

/-- Membership in the open-chain adjacency: `j` is a neighbour of `i` exactly
when the two indices differ by one. -/
theorem mem_openChainNeighbors {n : ℕ} {i j : Fin n} :
    j ∈ openChainNeighbors n i ↔ j.val + 1 = i.val ∨ j.val = i.val + 1 := by
  simp [openChainNeighbors]

/-- The open-chain adjacency is symmetric. -/
theorem openChainNeighbors_symmetric (n : ℕ) :
    SymmetricNeighbors (openChainNeighbors n) := by
  intro i j
  rw [mem_openChainNeighbors, mem_openChainNeighbors]
  omega

/-- No site of the open chain is its own neighbour. -/
theorem notMem_openChainNeighbors_self (n : ℕ) (i : Fin n) :
    i ∉ openChainNeighbors n i := by
  intro hcon
  rcases mem_openChainNeighbors.mp hcon with h | h <;> omega

/-- The left endpoint of a nontrivial open chain adjoins exactly the site of
index one. -/
theorem openChainNeighbors_left_endpoint (n : ℕ) (i : Fin n)
    (hi : i.val = 0) (j : Fin n) :
    j ∈ openChainNeighbors n i ↔ j.val = 1 := by
  rw [mem_openChainNeighbors, hi]
  omega

/-- The left endpoint of a nontrivial open chain has exactly one neighbour. -/
theorem openChainNeighbors_left_endpoint_card (n : ℕ) (hn : 1 < n) (i : Fin n)
    (hi : i.val = 0) :
    (openChainNeighbors n i).card = 1 := by
  have hsingle : openChainNeighbors n i = ({⟨1, by omega⟩} : Finset (Fin n)) := by
    ext j
    rw [openChainNeighbors_left_endpoint n i hi j, Finset.mem_singleton]
    constructor
    · intro h
      exact Fin.eq_of_val_eq h
    · intro h
      rw [h]
  rw [hsingle, Finset.card_singleton]

/-- The right endpoint of a nontrivial open chain adjoins exactly the site of
index `n - 2`. -/
theorem openChainNeighbors_right_endpoint (n : ℕ) (hn : 1 < n) (i j : Fin n)
    (hi : i.val = n - 1) :
    j ∈ openChainNeighbors n i ↔ j.val + 1 = n - 1 := by
  have hj : j.val < n := j.isLt
  rw [mem_openChainNeighbors, hi]
  omega

/-- The right endpoint of a nontrivial open chain has exactly one
neighbour. -/
theorem openChainNeighbors_right_endpoint_card (n : ℕ) (hn : 1 < n)
    (i : Fin n) (hi : i.val = n - 1) :
    (openChainNeighbors n i).card = 1 := by
  have hsingle : openChainNeighbors n i = ({⟨n - 2, by omega⟩} : Finset (Fin n)) := by
    ext j
    rw [openChainNeighbors_right_endpoint n hn i j hi, Finset.mem_singleton]
    constructor
    · intro h
      exact Fin.eq_of_val_eq (show j.val = n - 2 by omega)
    · intro h
      rw [h]
      show n - 2 + 1 = n - 1
      omega
  rw [hsingle, Finset.card_singleton]

/-- An interior site of the open chain adjoins exactly the two sites of
adjacent index. -/
theorem openChainNeighbors_interior (n : ℕ) (i : Fin n) (h1 : 0 < i.val)
    (j : Fin n) :
    j ∈ openChainNeighbors n i ↔ j.val = i.val - 1 ∨ j.val = i.val + 1 := by
  rw [mem_openChainNeighbors]
  omega

/-- An interior site of the open chain has exactly two neighbours. -/
theorem openChainNeighbors_interior_card (n : ℕ) (i : Fin n) (h1 : 0 < i.val)
    (h2 : i.val + 1 < n) :
    (openChainNeighbors n i).card = 2 := by
  have hpair : openChainNeighbors n i
      = ({⟨i.val - 1, by omega⟩, ⟨i.val + 1, by omega⟩} : Finset (Fin n)) := by
    ext j
    rw [openChainNeighbors_interior n i h1 j, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.eq_of_val_eq h)
      · exact Or.inr (Fin.eq_of_val_eq h)
    · rintro (h | h)
      · subst h
        exact Or.inl rfl
      · subst h
        exact Or.inr rfl
  have hne : (⟨i.val - 1, by omega⟩ : Fin n)
      ∉ ({⟨i.val + 1, by omega⟩} : Finset (Fin n)) := by
    intro hmem
    have hv : i.val - 1 = i.val + 1 :=
      congrArg Fin.val (Finset.mem_singleton.mp hmem)
    omega
  rw [hpair, Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-- The energy balance specialized to the open chain on `Fin n`: along any
trajectory of the second-order active equation with the open-chain
adjacency, the derivative of the open-chain energy is exactly the Rayleigh
power. The endpoints with their single neighbour are covered by the same
identity as the interior sites. -/
theorem openChain_energy_balance (a b m r τ ω₀ : ℝ) (n : ℕ)
    (Φ W Acc : Fin n → ℝ → ℝ) (t₀ : ℝ)
    (hkin : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀)
    (hvel : ∀ i, HasDerivAt (W i) (Acc i t₀) t₀)
    (hacc : ∀ i, m * r * Acc i t₀
        = m * r * rayleighAngularAcceleration τ ω₀ (W i t₀)
          + openForceSum a b (openChainNeighbors n) (fun i => Φ i t₀) i) :
    HasDerivAt (fun t => openEnergy a b m r (openChainNeighbors n)
        (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t₀)) t₀ :=
  open_energy_balance a b m r τ ω₀ (openChainNeighbors n)
    (openChainNeighbors_symmetric n) Φ W Acc t₀ hkin hvel hacc

/-- The energy balance of the open chain in acceleration form: the
accelerations are given as the Rayleigh drift plus the neighbour force sum
divided by the angular inertia, as consumed from a first-order vector-field
description. -/
theorem openChain_energy_balance_of_rhs (a b m r τ ω₀ : ℝ) (n : ℕ)
    (hm : 0 < m) (hr : 0 < r)
    (Φ W Acc : Fin n → ℝ → ℝ) (t₀ : ℝ)
    (hkin : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀)
    (hvel : ∀ i, HasDerivAt (W i) (Acc i t₀) t₀)
    (hacc : ∀ i, Acc i t₀
        = rayleighAngularAcceleration τ ω₀ (W i t₀)
          + openForceSum a b (openChainNeighbors n) (fun i => Φ i t₀) i
            / (m * r)) :
    HasDerivAt (fun t => openEnergy a b m r (openChainNeighbors n)
        (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t₀)) t₀ := by
  refine openChain_energy_balance a b m r τ ω₀ n Φ W Acc t₀ hkin hvel
    fun i => ?_
  rw [hacc i, mul_add, mul_div_cancel₀ _ (mul_ne_zero hm.ne' hr.ne')]

/-! ## Non-double counting of the half-weight edge energy -/

/-- On the open chain, the half-weighted ordered-pair potential of equation
(24) equals the full-weight sum over strictly forward neighbours: each of
the `n - 1` chain edges contributes exactly one copy of `U`, never two. The
forward half and the backward half of the ordered-pair sum are identified by
the transpose identity `open_edge_sum_transpose` and the exchange symmetry
of the pair potential. -/
theorem openChainPairPotential_eq_forward (a b : ℝ) (n : ℕ) (φ : Fin n → ℝ) :
    openPairPotential a b (openChainNeighbors n) φ
      = ∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
          gkPairPotential a b (φ i) (φ j) := by
  have hfwdbwd : ∀ i : Fin n,
      (openChainNeighbors n i).filter (fun j => ¬ i.val < j.val)
        = (openChainNeighbors n i).filter (fun j => j.val < i.val) := by
    intro i
    ext j
    simp only [Finset.mem_filter, mem_openChainNeighbors]
    constructor
    · rintro ⟨hj, h⟩
      exact ⟨hj, by
        rcases hj with h1 | h1 <;> simp only [not_lt] at h <;> omega⟩
    · rintro ⟨hj, h⟩
      exact ⟨hj, by omega⟩
  have hsplit : ∀ i : Fin n,
      (∑ j ∈ openChainNeighbors n i, (1 / 2) * gkPairPotential a b (φ i) (φ j))
        = (∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
              (1 / 2) * gkPairPotential a b (φ i) (φ j))
          + (∑ j ∈ (openChainNeighbors n i).filter (fun j => j.val < i.val),
              (1 / 2) * gkPairPotential a b (φ i) (φ j)) := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not (openChainNeighbors n i)
      (fun j => i.val < j.val)
      (fun j => (1 / 2) * gkPairPotential a b (φ i) (φ j)), hfwdbwd i]
  have hTA : (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
        (1 / 2) * gkPairPotential a b (φ i) (φ j))
      = (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => j.val < i.val),
        (1 / 2) * gkPairPotential a b (φ i) (φ j)) := by
    have h1 := open_edge_sum_transpose (openChainNeighbors n)
      (openChainNeighbors_symmetric n)
      (fun i j => if i.val < j.val then
        (1 / 2) * gkPairPotential a b (φ i) (φ j) else 0)
    have e1 : ∀ i : Fin n,
        (∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
            (1 / 2) * gkPairPotential a b (φ i) (φ j))
          = ∑ j ∈ openChainNeighbors n i,
              if i.val < j.val then
                (1 / 2) * gkPairPotential a b (φ i) (φ j) else 0 :=
      fun i => Finset.sum_filter _ _
    have e2 : ∀ i : Fin n,
        (∑ j ∈ (openChainNeighbors n i).filter (fun j => j.val < i.val),
            (1 / 2) * gkPairPotential a b (φ i) (φ j))
          = ∑ j ∈ openChainNeighbors n i,
              if j.val < i.val then
                (1 / 2) * gkPairPotential a b (φ i) (φ j) else 0 :=
      fun i => Finset.sum_filter _ _
    have hR : (∑ i, ∑ j ∈ openChainNeighbors n i,
          if j.val < i.val then
            (1 / 2) * gkPairPotential a b (φ j) (φ i) else 0)
        = (∑ i, ∑ j ∈ openChainNeighbors n i,
          if j.val < i.val then
            (1 / 2) * gkPairPotential a b (φ i) (φ j) else 0) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        by_cases h : j.val < i.val
        · simp only [h]
          rw [gk_pair_potential_exchange]
        · simp [h]
    rw [Finset.sum_congr rfl (fun i _ => e1 i),
      Finset.sum_congr rfl (fun i _ => e2 i), ← hR]
    exact h1
  calc openPairPotential a b (openChainNeighbors n) φ
      = ∑ i, ((∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
              (1 / 2) * gkPairPotential a b (φ i) (φ j))
          + (∑ j ∈ (openChainNeighbors n i).filter (fun j => j.val < i.val),
              (1 / 2) * gkPairPotential a b (φ i) (φ j))) := by
        unfold openPairPotential
        exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
            (1 / 2) * gkPairPotential a b (φ i) (φ j))
        + (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => j.val < i.val),
            (1 / 2) * gkPairPotential a b (φ i) (φ j)) :=
        Finset.sum_add_distrib
    _ = (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
            (1 / 2) * gkPairPotential a b (φ i) (φ j))
        + (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
            (1 / 2) * gkPairPotential a b (φ i) (φ j)) := by rw [hTA]
    _ = ∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
          gkPairPotential a b (φ i) (φ j) := by
        have hX : (∑ i, ∑ j ∈ (openChainNeighbors n i).filter (fun j => i.val < j.val),
              (1 / 2) * gkPairPotential a b (φ i) (φ j))
            = (1 / 2) * (∑ i, ∑ j ∈ (openChainNeighbors n i).filter
                (fun j => i.val < j.val),
              gkPairPotential a b (φ i) (φ j)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        linarith

/-- The three-site open-chain adjacency at the left endpoint: exactly the
site `1`. -/
theorem openChainNeighbors_three_zero :
    openChainNeighbors 3 (0 : Fin 3) = {1} := by
  ext j
  have hj : j.val < 3 := j.isLt
  have hj1 : j = 1 ↔ j.val = 1 := Fin.val_inj.symm
  rw [mem_openChainNeighbors, Finset.mem_singleton, hj1]
  simp only [Fin.val_zero]
  omega

/-- The three-site open-chain adjacency at the interior site: exactly the
sites `0` and `2`. -/
theorem openChainNeighbors_three_one :
    openChainNeighbors 3 (1 : Fin 3) = {0, 2} := by
  ext j
  have hj : j.val < 3 := j.isLt
  have h0 : j = 0 ↔ j.val = 0 := Fin.val_inj.symm
  have h2 : j = 2 ↔ j.val = 2 := Fin.val_inj.symm
  rw [mem_openChainNeighbors, Finset.mem_insert, Finset.mem_singleton, h0,
    h2]
  simp only [Fin.val_one]
  omega

/-- The three-site open-chain adjacency at the right endpoint: exactly the
site `1`. -/
theorem openChainNeighbors_three_two :
    openChainNeighbors 3 (2 : Fin 3) = {1} := by
  ext j
  have hj : j.val < 3 := j.isLt
  have hj1 : j = 1 ↔ j.val = 1 := Fin.val_inj.symm
  rw [mem_openChainNeighbors, Finset.mem_singleton, hj1]
  simp only [Fin.val_two]
  omega

/-- The three-site non-double counting receipt: the total half-weighted pair
potential of the open chain on `Fin 3` is exactly one copy of `U` on each of
the two edges, the halves over the two orientations of each edge combining
through the exchange symmetry `U_ij = U_ji`. -/
theorem openChainPairPotential_three (a b : ℝ) (φ : Fin 3 → ℝ) :
    openPairPotential a b (openChainNeighbors 3) φ
      = gkPairPotential a b (φ 0) (φ 1) + gkPairPotential a b (φ 1) (φ 2) := by
  unfold openPairPotential
  rw [Fin.sum_univ_three, openChainNeighbors_three_zero,
    openChainNeighbors_three_one, openChainNeighbors_three_two]
  rw [Finset.sum_singleton, Finset.sum_pair (by decide), Finset.sum_singleton]
  rw [gk_pair_potential_exchange a b (φ 1) (φ 0),
    gk_pair_potential_exchange a b (φ 2) (φ 1)]
  ring

end Qatlib.Papers.HydroSpinLatt21.GKModel

end
