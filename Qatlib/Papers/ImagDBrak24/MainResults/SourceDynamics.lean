/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ImagDBrak24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Dynamics of DB-QITE / DBI / ITE — shared definitions

Fixed paper version: arXiv:2412.04554v2 (2 Jul 2025).

* `unitaryEvolve A t` — the unitary `e^{itÂ}`;
* `realEvolve A s` — the (non-unitary) matrix exponential `e^{sÂ}`;
* `dbiStep lam s ψ` — the QITE-DBI step Eq. (59) p.17:
  `|σ_{k+1}⟩ = e^{s_k[σ_k,Ĥ]}|σ_k⟩` with `σ_k = |ψ⟩⟨ψ|`;
* `dbqiteNext lam s ψ` — the reduced DB-QITE state recursion Eq. (124) p.22
  (main text Eq. (12)):
  `e^{i√s Ĥ} e^{i√s ω_k} e^{-i√s Ĥ}|ω_k⟩`;
* `dbqiteStep lam s ψ U` — the operator-level DB-QITE recursion Eq. (13) p.3;
* `dbqiteUnitaryStep lam x0 s U` — the unitary recursion of Eq. (166) p.25,
  `U_{k+1} = e^{i√s Ĥ} U_k e^{i√s |0⟩⟨0|} U_k† e^{-i√s Ĥ} U_k`;
* `charFun lam ψ t` — the characteristic function Eq. (127) p.23,
  `φ(t) = ⟨ω_k| e^{itĤ} |ω_k⟩`;
* `fidelity ψ φ` — the ground-state fidelity `F = |⟨ψ|φ⟩|²` (Theorem 2, Eq. (16)).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.ImagDBrak24.MainResults

open Matrix
open scoped BigOperators ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unitary evolution `e^{itÂ}` (Hamiltonian simulation with real time `t`). -/
def unitaryEvolve (A : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • A)

/-- The real-time-parameter matrix exponential `e^{sÂ}`, used for the DBI flow
`e^{s_k[σ_k,Ĥ]}` of Eq. (59). -/
def realEvolve (A : Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((s : ℂ) • A)

/-- One QITE-DBI step Eq. (59) p.17: `|σ_{k+1}⟩ = e^{s_k[σ_k,Ĥ]}|σ_k⟩` with
`σ_k = |ψ⟩⟨ψ|`. -/
def dbiStep (lam : ι → ℝ) (s : ℝ) (ψ : ι → ℂ) : ι → ℂ :=
  realEvolve (commutator (pureState ψ) (diagHam lam)) s *ᵥ ψ

/-- One reduced DB-QITE step on states, Eq. (124) p.22 (main text Eq. (12)):
`|ω_{k+1}⟩ = e^{i√s Ĥ} e^{i√s ω_k} e^{-i√s Ĥ}|ω_k⟩`. -/
def dbqiteNext (lam : ι → ℝ) (s : ℝ) (ψ : ι → ℂ) : ι → ℂ :=
  unitaryEvolve (diagHam lam) (Real.sqrt s) *ᵥ
    (unitaryEvolve (pureState ψ) (Real.sqrt s) *ᵥ
      (unitaryEvolve (diagHam lam) (-(Real.sqrt s)) *ᵥ ψ))

/-- One operator-level DB-QITE step, Eq. (13) p.3:
`U_{k+1} = e^{i√s Ĥ} e^{i√s ω_k} e^{-i√s Ĥ} U_k` with `ω_k = |U_k 0⟩⟨U_k 0|`. -/
def dbqiteStep (lam : ι → ℝ) (s : ℝ) (ψ : ι → ℂ) (U : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  unitaryEvolve (diagHam lam) (Real.sqrt s) * unitaryEvolve (pureState ψ) (Real.sqrt s) *
    unitaryEvolve (diagHam lam) (-(Real.sqrt s)) * U

/-- The unitary recursion of Eq. (166) p.25:
`U_{k+1} = e^{i√s Ĥ} U_k e^{i√s |0⟩⟨0|} U_k† e^{-i√s Ĥ} U_k`,
with `|0⟩ = x0` the fixed reference state. -/
def dbqiteUnitaryStep (lam : ι → ℝ) (x0 : ι → ℂ) (s : ℝ) (U : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  unitaryEvolve (diagHam lam) (Real.sqrt s) * U * unitaryEvolve (pureState x0) (Real.sqrt s) *
    Uᴴ * unitaryEvolve (diagHam lam) (-(Real.sqrt s)) * U

/-- The characteristic function Eq. (127) p.23: `φ(t) = ⟨ω_k| e^{itĤ} |ω_k⟩`. -/
def charFun (lam : ι → ℝ) (ψ : ι → ℂ) (t : ℝ) : ℂ :=
  vdot ψ (unitaryEvolve (diagHam lam) t *ᵥ ψ)

/-- The fidelity `F(ψ, φ) = |⟨ψ|φ⟩|²` between two state vectors
(`F_k = |⟨λ_0|ω_k⟩|²` of Theorem 2). -/
def fidelity (ψ φ : ι → ℂ) : ℝ := Complex.normSq (vdot ψ φ)

end Qatlib.Papers.ImagDBrak24.MainResults
