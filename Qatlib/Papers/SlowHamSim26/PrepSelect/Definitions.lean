/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowHamSim26.Amplification.Definitions
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / PrepSelect — ancilla registers and the `|0⟩_{5∼1}` frame

Fixed source: arXiv:2608.17653v1, §6.1.2 (Theorems 6.1 and 6.3, pp. 41–42 and 48–49).
The prepare/select constructions act on five ancillary-qubit systems whose
sizes are recorded in (6.88) (general case) and (6.158) (control-Hamiltonian
case).  This file provides the modelling layer:

* `Aux n = Fin (2^n)` — a register of `n` ancilla qubits;
* `FullSpace nanc lmax d = Aux nanc × (D^{4lmax} × ℂ^d)` — the five ancilla
  systems together with the truncated Floquet register `D^{4lmax}` and the
  system register;
* `zeroFrame` — the isometric frame `|0⟩_{5∼1} : D^{4lmax} ⊗ ℂ^d ↪ FullSpace`
  used in the paper's `⟨0|_{5∼1} (G_prep,L)† O_select G_prep,R |0⟩_{5∼1}`;
* `blockEncoding_of_prepareSelect` — turns the paper's error bound on that
  compression into the reusable Frozen `BlockEncoding` predicate with `α = 1`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.PrepSelect

open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding

/-- A register of `n` ancilla qubits, `Aux n = Fin (2^n)`. -/
abbrev Aux (n : ℕ) : Type := Fin (2 ^ n)

/-- The truncated Floquet register `D^{4lmax} = Fin (2·(4·lmax))` together with the
`d`-dimensional system register. -/
abbrev SystemSpace (lmax d : ℕ) : Type := Fin (2 * (4 * lmax)) × Fin d

/-- The full workspace of Theorem 6.1: the five ancillary systems (totalling `nanc`
qubits) together with the truncated Floquet register and the system register. -/
abbrev FullSpace (nanc lmax d : ℕ) : Type := Aux nanc × SystemSpace lmax d

/-- The all-zero ancilla state `|0⟩` of a register of `n` qubits. -/
def zeroAncilla (n : ℕ) : Aux n := ⟨0, Nat.pow_pos (by norm_num : (0 : ℕ) < 2)⟩

/-- The isometric frame `|0⟩_{5∼1}` embedding `D^{4lmax} ⊗ ℂ^d` into the full
workspace: the paper's `|0⟩_{5∼1} ⊗ |m, a⟩ ↦ |0…0⟩ ⊗ |m, a⟩`. -/
def zeroFrame (nanc lmax d : ℕ) :
    Matrix (FullSpace nanc lmax d) (SystemSpace lmax d) ℂ :=
  fun h s => if h = (zeroAncilla nanc, s) then 1 else 0

/-- `zeroFrame` is an isometry: `|0⟩_{5∼1}` has orthonormal columns. -/
theorem zeroFrame_isIsometry (nanc lmax d : ℕ) :
    IsIsometry (zeroFrame nanc lmax d) := by
  unfold IsIsometry
  ext s t
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, zeroFrame]
  rw [Finset.sum_eq_single (zeroAncilla nanc, s)]
  · by_cases hst : s = t
    · subst hst
      simp
    · simp [hst]
  · intro b _ hb
    simp [hb]
  · intro hmem
    simp at hmem

/-- Fixed arXiv:2608.17653v1, §6.1.2: the paper's error bound on
`⟨0|_{5∼1} (G_prep,L)† O_select G_prep,R |0⟩_{5∼1}` (Eqs. (6.89), (6.159)) yields a
Frozen `BlockEncoding` of the normalised target with `α = 1`.  The three oracles are
unitaries on the full workspace; compression between the `|0⟩_{5∼1}` frames is
Frozen's `compress`. -/
theorem blockEncoding_of_prepareSelect
    {nanc lmax d : ℕ} (A : Matrix (SystemSpace lmax d) (SystemSpace lmax d) ℂ)
    (GprepL GprepR Oselect : Matrix (FullSpace nanc lmax d) (FullSpace nanc lmax d) ℂ)
    (hL : GprepL ∈ Matrix.unitaryGroup (FullSpace nanc lmax d) ℂ)
    (hR : GprepR ∈ Matrix.unitaryGroup (FullSpace nanc lmax d) ℂ)
    (hS : Oselect ∈ Matrix.unitaryGroup (FullSpace nanc lmax d) ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ‖A - compress (zeroFrame nanc lmax d)
        (Matrix.conjTranspose GprepL * Oselect * GprepR) (zeroFrame nanc lmax d)‖ ≤ ε) :
    BlockEncoding A (Matrix.conjTranspose GprepL * Oselect * GprepR)
      (zeroFrame nanc lmax d) (zeroFrame nanc lmax d) 1 ε where
  unitary := (Matrix.unitaryGroup (FullSpace nanc lmax d) ℂ).mul_mem
    ((Matrix.unitaryGroup (FullSpace nanc lmax d) ℂ).mul_mem
      (adjoint_unitary hL) hS) hR
  left_isometry := zeroFrame_isIsometry nanc lmax d
  right_isometry := zeroFrame_isIsometry nanc lmax d
  normalization_pos := one_pos
  error_nonneg := hε
  error_le := by simpa using herror

end Qatlib.Papers.SlowHamSim26.PrepSelect
