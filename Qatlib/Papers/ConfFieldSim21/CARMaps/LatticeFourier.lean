/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ConfFieldSim21 — Fourier diagonalisation of the lattice hopping operator

Osborne--Stottmeister, *Quantum Simulation of Conformal Field Theory*,
fixed arXiv:2109.14214v1, Eq. (12) and the surrounding discussion (pp. 12-13).

The paper diagonalises the free staggered fermion chain by a Fourier transform
`U_FT` followed by a Bogoliubov transformation `U_B`.  This file formalises the
Fourier half of that circuit on the momentum lattice `ZMod m`: the plane waves
`j ↦ stdAddChar (k * j)` are eigenvectors of the nearest-neighbour hopping
operator `f j ↦ f (j+1) + f (j-1)`, with eigenvalue
`stdAddChar k + stdAddChar (-k)`.

Boundary: the staggered two-component fermion model, the Bogoliubov matrix and
the Fock-space assembly `H_0^(N) = U_FT U_B D_0^(N) U_B† U_FT†` are not
formalised here; this file covers only the momentum-mode diagonalisation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConfFieldSim21.CARMaps

variable {m : ℕ} [NeZero m]

/-- The momentum plane wave `j ↦ e^{2π i k j / m}` on the lattice `ZMod m`. -/
def momentumMode (k : ZMod m) : ZMod m → ℂ :=
  fun j => ZMod.stdAddChar (k * j)

/-- Nearest-neighbour hopping `(hop f) j = f (j+1) + f (j-1)`. -/
def hop (f : ZMod m → ℂ) (j : ZMod m) : ℂ :=
  f (j + 1) + f (j - 1)

/-- **Fourier half of Eq. (12).**  Every momentum plane wave is an eigenvector of
the nearest-neighbour hopping operator, with eigenvalue
`stdAddChar k + stdAddChar (-k)`. -/
theorem momentumMode_hop (k j : ZMod m) :
    hop (momentumMode k) j =
      (ZMod.stdAddChar k + ZMod.stdAddChar (-k)) * momentumMode k j := by
  unfold hop momentumMode
  have h1 : (ZMod.stdAddChar (k * (j + 1)) : ℂ) =
      (ZMod.stdAddChar (k * j) : ℂ) * (ZMod.stdAddChar k : ℂ) := by
    rw [← AddChar.map_add_eq_mul (ZMod.stdAddChar : AddChar (ZMod m) ℂ) (k * j) k]
    congr 1
    ring
  have h2 : (ZMod.stdAddChar (k * (j - 1)) : ℂ) =
      (ZMod.stdAddChar (k * j) : ℂ) * (ZMod.stdAddChar (-k) : ℂ) := by
    rw [← AddChar.map_add_eq_mul (ZMod.stdAddChar : AddChar (ZMod m) ℂ) (k * j) (-k)]
    congr 1
    ring
  rw [h1, h2]
  ring

end Qatlib.Papers.ConfFieldSim21.CARMaps
