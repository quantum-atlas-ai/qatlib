/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# FermEigState17 Claim c004 — exact phase-estimation spectrum via qubitization

Fixed paper version: **arXiv:1711.10460**, Section IV, p. 6, Eqs. (12)–(13).

The paper replaces the Hamiltonian-simulation time-evolution operator in phase
estimation by the qubiterate

  `W = i (2|0⟩⟨0|_a ⊗ 1_s − 1) V`,

and shows that, restricted to the ancilla/system sector
`{|0⟩_a|k⟩_s, |0 k^⊥⟩_{as}}`, it acts as

  `W |±k⟩_{as} = ∓ e^{∓i arcsin(E_k/λ)} |±k⟩_{as}`  (Eq. (12)),
  `|±k⟩_{as} = (1/√2)(|0⟩_a|k⟩_s ± |0 k^⊥⟩_{as})`  (Eq. (13)).

The spectrum is exact and equal to the quantum-walk spectrum of Refs. [53, 54].
The paper then uses "taking the sine gives an estimate of `E_k/λ`" to remove the
`arcsin` / `π − arcsin` phase ambiguity, noting `λ ≥ ‖H‖` forces
`|E_k/λ| ≤ 1`.

## Reuse

The eigenphase statement Eqs. (12)–(13) is formalized in the
library as

`Qatlib.Concepts.QspSimulation.SparseWalk.sparseWalkEigenphasesRestricted`
(module `Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedLowc`),

which is a `generalization`: for isometric frames `L, R` with `LᴴR = c·H` and a
self-adjoint involution `S` exchanging them, the walk `V = i·S·(2LLᴴ − 1)` has
eigenvectors `wp, wm` with exactly the Eq. (12) eigenphases
`e^{i arcsin(c ev)}`, `−e^{−i arcsin(c ev)}`, and the frame state is the balanced
Eq. (13) superposition.  We record that bridge here so the paper's claim is
linked to that general spectral statement.

The remaining step — "take the sine to eliminate the phase ambiguity" — is
proved below from first principles for every `|r| ≤ 1`, and specialized to
`r = E_k/λ` under `λ ≥ ‖H‖`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermEigState17.MainResults.QubitizationSpectrum

open Qatlib.Concepts.QspSimulation.SparseWalk

/-- **Claim c004, Eqs. (12)–(13) (arXiv:1711.10460 §IV p. 6).**  Bridge to the
generalization of the exact qubiterate spectrum.

Reused FQN:
`Qatlib.Concepts.QspSimulation.SparseWalk.sparseWalkEigenphasesRestricted`. -/
theorem eq12_eq13_exact_spectrum : SparseWalkEigenphasesRestricted :=
  sparseWalkEigenphasesRestricted

/-- For a normalized eigenvalue ratio `r = E_k/λ` with `|r| ≤ 1`, taking the
sine of the phase returns `r`; this is the paper's reason that Eq. (12)'s
spectrum recovers `E_k` without ambiguity. -/
theorem sine_recovers_ratio {r : ℝ} (h : -1 ≤ r ∧ r ≤ 1) :
    Real.sin (Real.arcsin r) = r :=
  Real.sin_arcsin h.1 h.2

/-- The `π − arcsin r` branch produced by phase estimation has the same sine,
so the two branches are indistinguishable after taking the sine — the paper's
"it is not necessary to distinguish the cases". -/
theorem sine_pi_sub_arcsin {r : ℝ} :
    Real.sin (Real.pi - Real.arcsin r) = Real.sin (Real.arcsin r) :=
  Real.sin_pi_sub (Real.arcsin r)

/-- Combined unambiguous-recovery statement of Eq. (12): for every `|r| ≤ 1`,
both the `arcsin r` and `π − arcsin r` phase estimates map to `r` under `sin`. -/
theorem sine_unambiguous_recovery {r : ℝ} (h : -1 ≤ r ∧ r ≤ 1) :
    Real.sin (Real.arcsin r) = r ∧ Real.sin (Real.pi - Real.arcsin r) = r := by
  refine ⟨Real.sin_arcsin h.1 h.2, ?_⟩
  rw [Real.sin_pi_sub]
  exact Real.sin_arcsin h.1 h.2

/-- If `λ ≥ ‖H‖ ≥ |E_k|`, then the ratio `E_k/λ` lies in `[-1, 1]`, the
hypothesis needed for the arcsin branch (paper: "`λ ≥ ‖H‖` implies that
`|E_k/λ| ≤ 1`"). -/
theorem eigenvalue_ratio_mem_Icc (Ek lam : ℝ) (hlam : 0 < lam) (h : |Ek| ≤ lam) :
    -1 ≤ Ek / lam ∧ Ek / lam ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor
  · rw [le_div_iff₀ hlam]
    linarith
  · rw [div_le_one hlam]
    linarith

/-- **Sine inversion of the qubiterate phase (arXiv:1711.10460 §IV p. 6).**
For an eigenvalue `E_k` of `H` with `|E_k| ≤ λ`, both phase-estimation
branches of Eq. (12) yield `E_k/λ` after taking the sine, providing an
unambiguous estimate of `E_k`. -/
theorem sine_recovers_eigenvalue (Ek lam : ℝ) (hlam : 0 < lam) (h : |Ek| ≤ lam) :
    Real.sin (Real.arcsin (Ek / lam)) = Ek / lam ∧
      Real.sin (Real.pi - Real.arcsin (Ek / lam)) = Ek / lam :=
  sine_unambiguous_recovery (eigenvalue_ratio_mem_Icc Ek lam hlam h)

end Qatlib.Papers.FermEigState17.MainResults.QubitizationSpectrum
