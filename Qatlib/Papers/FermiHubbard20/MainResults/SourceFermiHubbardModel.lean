/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionHubbard

set_option backward.isDefEq.respectTransparency false

/-!
# Source model definitions: the 1D spinful Fermi-Hubbard Hamiltonian

This file formalises the model used in *"Observing the charge-spin separation
and a linear damping law ..."* (arXiv:2010.07965, Phys. Rev. Lett. 2020).  The
active claims of paper `FermiHubbard20` all refer to the one-dimensional
spinful Fermi-Hubbard model of Eq. (1) and to the charge/spin densities of
Eq. (2) together with the density-spread observables of Eq. (3).

The single-particle modes are `2 * L` Majorana-Jordan-Wigner modes: site `j`,
spin `ν` (`ν = false` is spin-up, `ν = true` is spin-down) is placed at
`2 j + ν`.  All algebraic primitives (`creation`, `annihilation`, `numberOp`)
are reused verbatim from the frozen concept library
`QuantumAlgorithm.Concepts.FermionAlgebra.CarJordanWigner`, so no fermionic
algebra is re-axiomatised here.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.FermiHubbard20.MainResults

open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Foundations.PureStateMath

/-! ## Mode indexing -/

/-- The Jordan-Wigner mode index of site `j` with spin `ν` among the `2 * L`
modes.  `ν = false` (spin-up) uses the even index `2 j`, `ν = true`
(spin-down) the odd index `2 j + 1`. -/
def mode (L : ℕ) (j : Fin L) (ν : Bool) : Fin (2 * L) :=
  ⟨2 * (j : ℕ) + (if ν = true then 1 else 0), by
    have hj := j.isLt
    split_ifs <;> omega⟩

/-- Value of the mode index, by definition. -/
@[simp] lemma mode_val (L : ℕ) (j : Fin L) (ν : Bool) :
    (mode L j ν : ℕ) = 2 * (j : ℕ) + (if ν = true then 1 else 0) := rfl

/-- Spin-up mode is the even mode `2 j`. -/
lemma mode_false (L : ℕ) (j : Fin L) : (mode L j false : ℕ) = 2 * (j : ℕ) := by
  simp [mode]

/-- Spin-down mode is the odd mode `2 j + 1`. -/
lemma mode_true (L : ℕ) (j : Fin L) : (mode L j true : ℕ) = 2 * (j : ℕ) + 1 := by
  simp [mode]

/-- Distinct spins on the same site give distinct modes. -/
lemma mode_ne_spin (L : ℕ) (j : Fin L) : mode L j false ≠ mode L j true := by
  intro h
  have hv : (mode L j false : ℕ) = (mode L j true : ℕ) := by
    simpa using congrArg (fun x : Fin (2 * L) => (x : ℕ)) h
  rw [mode_false, mode_true] at hv
  omega

/-! ## Hamiltonian (source Eq. (1)) -/

/-- The one-dimensional spinful Fermi-Hubbard Hamiltonian of Eq. (1) on `L`
sites with open boundaries:

* nearest-neighbour hopping with amplitude `J`,
* on-site interaction `U`,
* a per-site, per-spin local potential `φ` (used for the Gaussian trapping
  potentials of §II).

All amplitudes are real (`J U : ℝ`, `φ : Fin L → Bool → ℝ`) so that the
resulting matrix is Hermitian (proved as `fermiHubbard1D_isHermitian` below
would require the frozen Hermiticity helpers, which are private; the
Hermiticity of the corresponding frozen Hamiltonian is the public theorem
`QuantumAlgorithm.Concepts.FermionAlgebra.CarJordanWigner.g2`). -/
noncomputable def fermiHubbard1D (L : ℕ) (J U : ℝ) (φ : Fin L → Bool → ℝ) :
    Matrix (Reg (2 * L)) (Reg (2 * L)) ℂ :=
  (∑ j : Fin L, ∑ ν : Bool,
      if h : (j : ℕ) + 1 < L then
        (-(J : ℂ)) •
          (creation (mode L j ν) * annihilation (mode L ⟨(j : ℕ) + 1, h⟩ ν)
            + creation (mode L ⟨(j : ℕ) + 1, h⟩ ν) * annihilation (mode L j ν))
      else 0)
    + (∑ j : Fin L, (U : ℂ) • (numberOp (mode L j false) * numberOp (mode L j true)))
    + (∑ j : Fin L, ∑ ν : Bool, (φ j ν : ℂ) • numberOp (mode L j ν))

/-! ## Observables (source Eq. (2), Eq. (3)) -/

/-- Expectation value `⟨ψ| M |ψ⟩` of a matrix in the (unnormalised) state
vector `ψ`. -/
noncomputable def expectation {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ)
    (ψ : Reg n → ℂ) : ℂ :=
  ∑ x : Reg n, star (ψ x) * (M *ᵥ ψ) x

/-- Occupation `⟨n_i⟩` of mode `i` in state `ψ`. -/
noncomputable def occExp {n : ℕ} (i : Fin n) (ψ : Reg n → ℂ) : ℂ :=
  expectation (numberOp i) ψ

/-- Charge density `ρ⁺_j = ⟨n_{j,↑}⟩ + ⟨n_{j,↓}⟩` of Eq. (2) (signed variant,
the component along the total-density direction). -/
noncomputable def chargeDensity (L : ℕ) (ψ : Reg (2 * L) → ℂ) (j : Fin L) : ℂ :=
  occExp (mode L j false) ψ + occExp (mode L j true) ψ

/-- Spin density `ρ⁻_j = ⟨n_{j,↑}⟩ - ⟨n_{j,↓}⟩` of Eq. (2) (signed variant,
the component along the spin-density direction). -/
noncomputable def spinDensity (L : ℕ) (ψ : Reg (2 * L) → ℂ) (j : Fin L) : ℂ :=
  occExp (mode L j false) ψ - occExp (mode L j true) ψ

/-- Normalisation of a state vector: `∑_x |ψ x|² = 1`. -/
noncomputable def normalized {n : ℕ} (ψ : Reg n → ℂ) : Prop :=
  ∑ x : Reg n, Complex.normSq (ψ x) = 1

/-- Total particle number in spin sector `ν` of a state `ψ`:
`N_ν = ∑_j ⟨n_{j,ν}⟩`.  This is the fixed particle number with which the
paper prepares the initial state (`N_↑ = N_↓ = 2` for `L = 8`). -/
noncomputable def particleNumber (L : ℕ) (ν : Bool) (ψ : Reg (2 * L) → ℂ) : ℝ :=
  ∑ j : Fin L, (occExp (mode L j ν) ψ).re

/-- Density spread of Eq. (3): `κ(ρ) = ∑_j |j - (L+1)/2| · ρ_j`.  The paper
labels sites `1 … L`; with `j : Fin L` the value `j.val` is `j - 1`, so the
distance to the centre `(L+1)/2` becomes `|j.val - (L-1)/2|`. -/
noncomputable def spread (L : ℕ) (ρ : Fin L → ℂ) : ℂ :=
  ∑ j : Fin L, ((((|(((j : ℕ) : ℝ) - ((L : ℝ) - 1) / 2)|)) : ℝ) : ℂ) * ρ j

/-- Charge spread `κ⁺` of Eq. (3). -/
noncomputable def chargeSpread (L : ℕ) (ψ : Reg (2 * L) → ℂ) : ℂ :=
  spread L (chargeDensity L ψ)

/-- Spin spread `κ⁻` of Eq. (3). -/
noncomputable def spinSpread (L : ℕ) (ψ : Reg (2 * L) → ℂ) : ℂ :=
  spread L (spinDensity L ψ)

/-! ## Ground states and the initial trap of §II -/

/-- Energy `⟨ψ| H |ψ⟩` of `H` in `ψ`. -/
noncomputable def energy {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ) (ψ : Reg n → ℂ) : ℂ :=
  expectation H ψ

/-- `ψ` is a (normalised) ground state of `H`: it minimises the real energy
among normalised vectors.  This is the precise sense in which the initial
state of §II is the ground state of the trapping Hamiltonian `H₀`. -/
noncomputable def IsGroundState {n : ℕ} (H : Matrix (Reg n) (Reg n) ℂ)
    (ψ : Reg n → ℂ) : Prop :=
  normalized ψ ∧ ∀ χ : Reg n → ℂ, normalized χ → (energy H ψ).re ≤ (energy H χ).re

/-- The Gaussian local potentials of §II (paper: `φ_{j,ν} = -λ_ν exp(-½ (j-m_ν)²/σ_ν²)`,
with site labels `j = 1,…,8`): a well of depth `4` on the spin-up component
centred at site `4.5` with width `σ = 1` (`λ↑ = 4`, `m↑ = 4.5`, `σ↑ = 1`),
and no potential on the spin-down component (`λ↓ = 0`).  Here `j : Fin 8`
has value `j.val = j - 1`, so the paper's label `j` is `j.val + 1`. -/
noncomputable def paperPhi (j : Fin 8) (ν : Bool) : ℝ :=
  if ν = true then 0
  else -(4 * Real.exp
    (-(((((j : ℕ) : ℝ) + 1) - 4.5) ^ 2) / (2 * (1 : ℝ) ^ 2)))

end Qatlib.Papers.FermiHubbard20.MainResults
