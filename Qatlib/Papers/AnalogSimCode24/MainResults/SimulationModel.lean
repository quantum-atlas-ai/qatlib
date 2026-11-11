/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel

set_option backward.isDefEq.respectTransparency false

/-!
# Source model: robust analog quantum simulation (arXiv:2412.07764v1)

Fixed paper: Cao--Liu--Deng--Xia--Wu--Wang, *Robust analog quantum simulators by quantum
error-detecting codes*, arXiv:2412.07764v1 (10 Dec 2024).

This module fixes the operator-level objects used by the paper's error bounds (Appendix B)
and its main theorem (Theorem III.1, main text p. 5).  A Hamiltonian is a Hermitian matrix
`Matrix ι ι ℂ` on a finite-dimensional Hilbert space with orthonormal index type `ι`.

Time evolution `e^{-iHt}` is *not* re-defined: it is the matrix exponential
`exp (-t • (I • H))`, i.e. the foundation evolution
`QuantumAlgorithmDev.Foundations.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution`
applied to the generator `I • H`.  This keeps the actual Dyson propagator of the library as
the single source of truth for `e^{-iHt}`.

The paper writes `H_sim = λ H_pen + √λ H_enc^(2) + H_enc^(1)` (Eq. (13)), the error
suppression condition `P_0 V_i P_0 = c_i P_0` (Eq. (11), app. B assumption 1), and the
encoding conditions (Eq. (14a)--(14d), app. B assumptions 2--4).  These are recorded as
explicit predicates below so that Theorem III.1 and Appendix B share the same hypotheses.

The spectral-gap hypotheses are recorded exactly as the paper states them: `S_0` is the
zero-energy eigenspace with "all nonzero eigenvalues outside `(-Δ, Δ)`" (Theorem B.1) or
outside `(-1, 1)` (Theorem B.3).  The pseudoinverse `R_0` satisfies the paper's defining
relations `R_0 = Q_0 R_0 Q_0` and `R_0 H_0 = H_0 R_0 = Q_0`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AnalogSimCode24.MainResults.SimulationModel

open Qatlib.Foundations.PureStateMath

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Time evolution -/

/-- The time-evolution operator `e^{-iHt}` of a Hamiltonian `H`, realized through the library's
Dyson propagator `evolution (I • H) t = exp(-t • (I • H))`. -/
def propagator (H : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution
    (Complex.I • H) t

/-- The `propagator_zero` result for the AnalogSimCode24 paper model. -/
@[simp] theorem propagator_zero (H : Matrix ι ι ℂ) : propagator H 0 = 1 := by
  simp [propagator]

/-- `e^{iθ}` as a complex scalar (the global phase of Eq. (B14)). -/
def globalPhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- A global phase is a unit-modulus scalar `‖e^{iθ}‖ = 1`. -/
theorem norm_globalPhase (θ : ℝ) : ‖globalPhase θ‖ = 1 := by
  simp [globalPhase, Complex.norm_exp]

/-! ## Projectors, gaps and pseudoinverses -/

/-- `P` is an orthogonal (Hermitian, idempotent) projector. -/
structure OrthogonalProjector (P : Matrix ι ι ℂ) : Prop where
  idem : P * P = P
  herm : Pᴴ = P

/-- The zero-energy eigenspace of the Hermitian `H` has orthogonal projector `P0`, orthogonal
complement projector `Q0 = 1 - P0`, and spectral gap `Δ` in the paper's sense: every nonzero
eigenvalue `λ` of `H` satisfies `Δ ≤ ‖λ‖` (Theorem B.1 / Theorem B.3 with `Δ = 1`). -/
structure ZeroEigenspaceGap (H P0 Q0 : Matrix ι ι ℂ) (Δ : ℝ) : Prop where
  pos : 0 < Δ
  herm : H.IsHermitian
  proj : P0 * P0 = P0
  proj_herm : P0ᴴ = P0
  complement : Q0 = 1 - P0
  vanishes : H * P0 = 0
  gap : ∀ (mu : ℂ) (v : ι → ℂ), v ≠ 0 → H *ᵥ v = mu • v → mu ≠ 0 → Δ ≤ ‖mu‖

/-- `R0` is the pseudoinverse of `H0` on the orthogonal complement of the zero eigenspace, in
the paper's sense: `R0 = Q0 R0 Q0` and `R0 H0 = H0 R0 = Q0` (text after Eq. (B3)). -/
structure Pseudoinverse (H0 Q0 R0 : Matrix ι ι ℂ) : Prop where
  sandwich : R0 = Q0 * R0 * Q0
  left : R0 * H0 = Q0
  right : H0 * R0 = Q0

/-! ## Effective Hamiltonians (Eqs. (B1a), (B1b), (B2), (B15)) -/

/-- First-order effective Hamiltonian `H_eff^(1) = P0 W P0` (Eq. (B1a)). -/
def effectiveFirst (P0 W : Matrix ι ι ℂ) : Matrix ι ι ℂ := P0 * W * P0

/-- Second-order effective Hamiltonian `H_eff^(2) = -P0 W R0 W P0` (Eq. (B1b)). -/
def effectiveSecond (P0 W R0 : Matrix ι ι ℂ) : Matrix ι ι ℂ := -(P0 * W * R0 * W * P0)

/-- Up-to-second-order effective Hamiltonian (Eq. (B2)). -/
def effectiveLeqTwo (P0 W R0 : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  effectiveFirst P0 W + effectiveSecond P0 W R0

/-- The effective Hamiltonian of Eq. (B15), written with the penalty pseudoinverse `R0` of
`H0 = λ H_pen`. -/
def effectiveLeqTwoOfPen (P0 W R0 : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  P0 * W * P0 - P0 * W * R0 * W * P0

/-! ## Simulator Hamiltonian (Eq. (13)) and error family (Eq. (3), (11)) -/

/-- The simulator Hamiltonian of Eq. (13):
`H_sim = λ H_pen + √λ H_enc^(2) + H_enc^(1)`. -/
def simulatorHamiltonian (lam : ℝ) (Hpen Henc2 Henc1 : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (lam : ℂ) • Hpen + ((Real.sqrt lam : ℝ) : ℂ) • Henc2 + Henc1

variable {ν : Type} [Fintype ν]

/-- The coherent error `V = Σ_i ε_i V_i` of Eq. (3), as a weighted family of Hermitian error
operators. -/
def errorOperator (ε : ν → ℝ) (Vs : ν → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ i, (ε i : ℂ) • Vs i

/-- Error suppression condition Eq. (11) / Theorem B.3 assumption 1: every error component
acts as a scalar `c_i` on the zero-energy subspace. -/
def ErrorSuppressed (P0 : Matrix ι ι ℂ) (Vs : ν → Matrix ι ι ℂ) (c : ν → ℝ) : Prop :=
  ∀ i, P0 * Vs i * P0 = (c i : ℂ) • P0

/-! ## Encoding conditions (Eq. (14), Theorem B.3 assumptions 2--4) -/

/-- The three encoding conditions of Theorem B.3 (Eqs. (14b)--(14d)); assumption 1 is
`ErrorSuppressed` above.  `HpenInv` is the penalty pseudoinverse `H_pen^{-1}` of Appendix D
(it satisfies `Pseudoinverse Hpen Q0 HpenInv`). -/
structure EncodingConditions (P0 Q0 Penc Hpen HpenInv Henc1 Henc2 Htar : Matrix ι ι ℂ) :
    Prop where
  assume2 : (P0 - Penc) * Henc1 * Penc = 0
  assume3a : P0 * Henc2 * P0 = 0
  assume3b : (P0 - Penc) * Henc2 * Q0 * HpenInv * Q0 * Henc2 * Penc = 0
  assume4 : Penc * Henc1 * Penc - Penc * Henc2 * Q0 * HpenInv * Q0 * Henc2 * Penc = Htar

/-! ## States, infidelity and the phase-uncertain operator bound -/

/-- Target state `|ψ_tar(t)⟩ = e^{-iH_tar t}|ψ_0⟩` (Theorem III.1). -/
def targetState (Htar : Matrix ι ι ℂ) (t : ℝ) (ψ0 : QState ι) : QState ι :=
  propagator Htar t *ᵥ ψ0

/-- Noisy simulator state `|ψ(t)⟩ = e^{-i(H_sim + V)t}|ψ_0⟩` (Theorem III.1). -/
def noisyState (Hsim V : Matrix ι ι ℂ) (t : ℝ) (ψ0 : QState ι) : QState ι :=
  propagator (Hsim + V) t *ᵥ ψ0

/-- Infidelity `1 - |⟨ψ_tar(t)|ψ(t)⟩|²` (Theorem III.1, Eq. (16)). -/
def infidelity (ψtar ψ : QState ι) : ℝ := 1 - ‖Inner ψtar ψ‖ ^ 2

/-- `PhaseClose A B ε`: the two operators agree up to a global phase `θ` within `ε`:
`∃ θ, ‖A - e^{iθ} B‖ ≤ ε`.  This is the `min_θ` of Eq. (B14) with the minimum unfolded (the
paper's proof exhibits the phase `θ = α t` explicitly, and the minimum is attained). -/
def PhaseClose (A B : Matrix ι ι ℂ) (ε : ℝ) : Prop :=
  ∃ θ : ℝ, ‖A - globalPhase θ • B‖ ≤ ε

end Qatlib.Papers.AnalogSimCode24.MainResults.SimulationModel
