/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergySim23.MainResults.Framework.Core

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 — the symmetry group of the projected Hamiltonian

Fixed paper version: arXiv:2312.08867v3 (Quantum **8**, 1409 (2024)).
Original text: `prove/assets/2312.08867.pdf`,
Proposition 1 on p.24.

Proposition 1: if `S` is the symmetry group of `H`, then `S` is a subgroup of
the symmetry group of `H̄ = Π_{≤Δ'} H Π_{≤Δ'}`, i.e. every unitary `C`
commuting with `H` also commutes with `Π_{≤Δ'} H Π_{≤Δ'}`.

This is **fully proved** below from `Framework.Core`: diagonalize
`H = U diag(λ) Uᴴ`; a matrix commuting with `H` becomes block diagonal across
distinct eigenvalues in the eigenbasis, hence commutes with every spectral
indicator, in particular with `Π_{≤Δ'}`; since `C` commutes with both `H` and
`Π_{≤Δ'}`, it commutes with `Π_{≤Δ'} H Π_{≤Δ'}`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LowEnergySim23.MainResults.Propositions

/-- **Proposition 1 (p.24).**  `S` is a subgroup of the symmetry group of
`H̄ = Π_{≤Δ'} H Π_{≤Δ'}`: every unitary commuting with `H` commutes with the
projected Hamiltonian. -/
theorem proposition1_symmetry_group_subgroup {D : ℕ} (H : Framework.Op D)
    (hH : H.IsHermitian) (Δ' : ℝ) :
    Framework.symmetryGroup H ⊆
      Framework.symmetryGroup
        (Framework.lowEnergyProjector H hH Δ' * H * Framework.lowEnergyProjector H hH Δ') :=
  Framework.symmetry_group_le_projected_symmetry_group H hH Δ'

end Qatlib.Papers.LowEnergySim23.MainResults.Propositions
