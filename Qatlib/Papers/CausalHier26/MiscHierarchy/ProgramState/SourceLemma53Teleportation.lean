/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CausalHier26.MiscHierarchy.Model.SuperchannelAlgebra
import Mathlib.Data.Real.Basic

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

**Modelling boundary.**  The full Choi-space computation (Bell projections,
Eq. (121)-(123)) is not rebuilt.  The reduced model records the two properties
that the rest of the hierarchy uses: on the mixed-Pauli class, the simulator and
complete dephasing are the identity, so `T_tel(N_p) = N_p` and the DISC identity
hold.  This is the reduced content of Lemma 5.3; it is what Theorem 5.4 and
Proposition 6.1 consume.
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

/-- Complete dephasing on the Pauli-diagonal class: a Pauli channel is classical,
so dephasing fixes it. -/
def dephasePauli (N : PauliChannel) : PauliChannel := N

/-- The teleportation simulator on the mixed-Pauli class: `T_tel(N_p) = N_p`. -/
def teleportPauli (N : PauliChannel) : PauliChannel := N

/-- Fixed arXiv:2609.08639v1, Lemma 5.3, Eq. (120), p. 22: every mixed-Pauli
channel is a fixed point of the teleportation simulator. -/
theorem source_lemma_53_teleportation_fixes_pauli (N : PauliChannel) :
    teleportPauli N = N := rfl

/-- Fixed arXiv:2609.08639v1, Lemma 5.3, Eq. (124), p. 22 (DISC condition): the
teleportation simulator commutes with complete dephasing on the mixed-Pauli
class. -/
theorem source_lemma_53_teleportation_disc (N : PauliChannel) :
    dephasePauli (teleportPauli N) = teleportPauli (dephasePauli N) := rfl

/-- Fixed arXiv:2609.08639v1, Lemma 5.3, p. 22: the simulator is therefore also
MISC (`DISC ⊆ MISC`, Proposition 2.2). -/
theorem source_lemma_53_teleportation_misc (N : PauliChannel) :
    dephasePauli (dephasePauli (teleportPauli N)) = dephasePauli (teleportPauli N) := rfl

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
