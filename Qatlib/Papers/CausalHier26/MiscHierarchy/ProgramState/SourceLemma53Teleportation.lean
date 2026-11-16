/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra
public import Mathlib.Basic.Real.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma53Teleportation — Lemma 5.3 (teleportation simulation is DISC)

Zhu--Zhao--Zhao--Chen--Wang--Zheng, fixed arXiv:2609.08639v1, Lemma 5.3, p. 22
(txt lines 1115-1140), Eqs. (120)-(124).

**Statement.**  The teleportation simulator `T_tel` satisfies the DISC condition
on the full linear qubit Choi space, hence is also MISC.  Moreover every
mixed-Pauli channel is a fixed point, `T_tel(N_p) = N_p` (Eq. (120)).

**Paper proof.**  The simulator is built from the Bell-basis projections
`|Φ_ab⟩⟨Φ_ab|`, and the teleportation identity shows that composing with the
input/output complete dephasing gives back the same map — the DISC equation
`Δ_C ∘ T_tel = T_tel ∘ Δ_X` (Eq. (124)).  A mixed-Pauli channel is invariant
under both the input dephasing and the teleportation correction, giving
`T_tel(N_p) = N_p` (Eqs. (121)-(123)).

**Modelling boundary.** The Bell-projection/Choi computation is unproved.
`PauliSimulation` exposes its structural laws as hypotheses about caller-supplied
maps. The results below are conditional reductions, not a construction of the
physical simulator or of complete dephasing.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState

open Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra

/-- A qubit Pauli channel `N_p` by its probability vector `(p_0,p_1,p_2,p_3)`
(Eq. (119), p. 22). -/
structure PauliChannel where
  /-- Probability of `I`. -/
  p0 : ℝ
  /-- Probability of `X`. -/
  p1 : ℝ
  /-- Probability of `Y`. -/
  p2 : ℝ
  /-- Probability of `Z`. -/
  p3 : ℝ
  /-- Nonnegativity of the probabilities. -/
  nonneg : 0 ≤ p0 ∧ 0 ≤ p1 ∧ 0 ≤ p2 ∧ 0 ≤ p3
  /-- Normalization of the probabilities. -/
  sum_one : p0 + p1 + p2 + p3 = 1

/-- Structural bridge for an actual Pauli/Choi-space simulator. Its maps
are supplied by the caller; Bell-basis derivation of these laws remains open. -/
structure PauliSimulation where
  /-- Complete dephasing, restricted to this representation. -/
  dephase : PauliChannel → PauliChannel
  /-- Teleportation simulation, restricted to this representation. -/
  teleport : PauliChannel → PauliChannel
  /-- Dephasing is an idempotent projection. -/
  dephase_idempotent : ∀ N, dephase (dephase N) = dephase N
  /-- Mixed-Pauli channels are fixed by the actual teleportation simulator. -/
  teleport_fixed : ∀ N, teleport N = N
  /-- The actual simulator intertwines the dephasing maps. -/
  disc : ∀ N, dephase (teleport N) = teleport (dephase N)

/-- Conditional fixed-point consequence of the simulation bridge, Eq. (120). -/
theorem source_lemma_53_teleportation_fixes_pauli (B : PauliSimulation) (N : PauliChannel) :
    B.teleport N = N := B.teleport_fixed N

/-- Conditional DISC consequence of the simulation bridge, Eq. (124). -/
theorem source_lemma_53_teleportation_disc (B : PauliSimulation) (N : PauliChannel) :
    B.dephase (B.teleport N) = B.teleport (B.dephase N) := B.disc N

/-- Idempotent dephasing gives the reduced MISC identity for the simulator. -/
theorem source_lemma_53_teleportation_misc (B : PauliSimulation) (N : PauliChannel) :
    B.dephase (B.dephase (B.teleport N)) = B.dephase (B.teleport N) :=
  B.dephase_idempotent _

/-- Fixed arXiv:2609.08639v1, Lemma 5.3, p. 22: the DISC identity as an instance
of the abstract free-operation predicate on a single-input interface. -/
theorem source_lemma_53_teleportation_discGen
    (dC dX : PauliChannel → PauliChannel)
    (hdC : ∀ N, dC N = N) (hdX : ∀ N, dX N = N) (Ttel : PauliChannel → PauliChannel)
    (hT : ∀ N, Ttel N = N) :
    IsDISCGen (fun _ : Fin 1 => dX) dC (fun a => Ttel (a 0)) := by
  intro a
  simp only [hdC, hT, hdX]

end Qatlib.Papers.CausalHier26.MiscHierarchy.ProgramState
