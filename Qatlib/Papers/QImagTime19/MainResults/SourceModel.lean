/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model: quantum imaginary-time evolution (QITE) and quantum Lanczos

Paper: M. Motta et al., "Determining eigenstates and thermal states on a
quantum computer using quantum imaginary time evolution", arXiv:1901.07653
(2019).  Fixed source: `assets/1901.07653.pdf`.

This module carries the paper-level vocabulary shared by the four active claims:

* `State ι` — a pure state of a register with orthonormal index type `ι`
  (`EuclideanSpace ℂ ι`);
* `act` — the action of a matrix (operator) on a state;
* `normalize`, `imaginaryStep` — the renormalised imaginary-time step of
  Eq. (28), `|Ψ_s⟩ = e^{-Δτ ĥ[i_s]} |Ψ_{s-1}⟩ / ‖e^{-Δτ ĥ[i_s]} |Ψ_{s-1}⟩‖`;
* `trotterSeq` — the exact Trotterised imaginary-time state `|Ψ_s⟩` of Eq. (23);
* `qiteSeq` — the state `|Φ_s⟩` produced by the local unitaries `Û_s`;
* `connectedCorrelation`, `CorrelationLengthBound` — the finite-correlation
  assumption of Eq. (24);
* `qiteDomainWidth`, `qiteQubitCount` — Eq. (25), the `N_q` qubit budget;
* `theorem2DomainWidth`, `theorem2QubitCount` — Eq. (37), the local-region
  qubit budget;
* `partialTraceRight`, `pureDensity`, `traceNorm`, `traceDist` — the reduced
  density matrices and trace distance of Eq. (38).

No statement in this model asserts a physical result; the model only fixes the
objects the claim files quantify over.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QImagTime19.MainResults

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- A pure state of a register whose orthonormal basis is indexed by `ι`. -/
abbrev State (ι : Type*) : Type _ := EuclideanSpace ℂ ι

/-- The action of an operator (matrix) on a state, `ψ ↦ U ψ`. -/
def act {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ : State ι) : State ι :=
  (EuclideanSpace.equiv ι ℂ).symm (U *ᵥ (EuclideanSpace.equiv ι ℂ) ψ)

/-- The amplitude of a state in the basis index `i`. -/
def amp {ι : Type*} [Fintype ι] (ψ : State ι) (i : ι) : ℂ :=
  (EuclideanSpace.equiv ι ℂ) ψ i

/-- The amplitude function is the Euclidean-space coordinate map. -/
@[simp] theorem amp_apply {ι : Type*} [Fintype ι] (ψ : State ι) :
    (fun i => amp ψ i) = (EuclideanSpace.equiv ι ℂ) ψ := rfl

/-- Renormalisation of a state (`ψ / ‖ψ‖`), Eq. (28). -/
def normalize {ι : Type*} [Fintype ι] (ψ : State ι) : State ι :=
  ((‖ψ‖ : ℝ) : ℂ)⁻¹ • ψ

/-- One renormalised imaginary-time step `e^{-Δτ Ĥ}` applied to `ψ`, Eq. (28). -/
def imaginaryStep {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (Δτ : ℝ)
    (ψ : State ι) : State ι :=
  normalize (act (NormedSpace.exp ((-Δτ) • H)) ψ)

/-- The `s`-th local factor of the Trotter decomposition, cycling through the
`m` Hamiltonian terms (Eq. (23) with `n·m` factors). -/
def trotterFactor {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
    (H : Fin m → Matrix ι ι ℂ) (s : ℕ) : Matrix ι ι ℂ :=
  H ⟨s % m, Nat.mod_lt _ (Nat.pos_of_neZero m)⟩

/-- The exact (renormalised) Trotterised imaginary-time sequence `|Ψ_s⟩` of
Eq. (23): `n` rounds of the `m` local factors `e^{-Δτ ĥ[l]}`, normalising after
every factor.  With `m·n` factors this is the `|Ψ_{mn}⟩` of Theorem 1. -/
def trotterSeq {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
    (H : Fin m → Matrix ι ι ℂ) (Δτ : ℝ) (ψ0 : State ι) : ℕ → State ι
  | 0 => ψ0
  | s + 1 => imaginaryStep (trotterFactor H s) Δτ (trotterSeq H Δτ ψ0 s)

/-- The state sequence `|Φ_s⟩` produced by the unitaries `Û_s` of the QITE
algorithm (`|Φ_s⟩ = Û_s |Φ_{s-1}⟩`). -/
def qiteSeq {ι : Type*} [Fintype ι] (U : ℕ → Matrix ι ι ℂ) (ψ0 : State ι) :
    ℕ → State ι
  | 0 => ψ0
  | s + 1 => act (U s) (qiteSeq U ψ0 s)

/-- The connected two-point function `⟨ψ|Â B̂|ψ⟩ − ⟨ψ|Â|ψ⟩⟨ψ|B̂|ψ⟩` of Eq. (24). -/
def connectedCorrelation {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : State ι)
    (A B : Matrix ι ι ℂ) : ℂ :=
  inner ℂ ψ (act (A * B) ψ) - inner ℂ ψ (act A ψ) * inner ℂ ψ (act B ψ)

/-- The finite-correlation-length assumption of Eq. (24): every connected
two-point function of operators whose supports are separated by `sep A B`
lattice sites decays as `‖A‖ ‖B‖ e^{-sep/C}`.  `sep` is the lattice distance
between the supports, supplied by the geometry of the concrete register. -/
def CorrelationLengthBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sep : Matrix ι ι ℂ → Matrix ι ι ℂ → ℝ) (C : ℝ) (ψ : State ι) : Prop :=
  ∀ A B : Matrix ι ι ℂ,
    ‖connectedCorrelation ψ A B‖ ≤ ‖A‖ * ‖B‖ * Real.exp (-(sep A B) / C)

/-- The domain width `ν = 2C ln(2√2 n m ε^{-1})` (Eq. (34)). -/
def qiteDomainWidth (C : ℝ) (n m : ℕ) (ε : ℝ) : ℝ :=
  2 * C * Real.log (2 * Real.sqrt 2 * (n : ℝ) * (m : ℝ) / ε)

/-- The qubit budget `N_q = k (2C)^d ln^d(2√2 n m ε^{-1}) = k ν^d` of Theorem 1,
Eq. (25), written in terms of the domain width `ν = 2C ln(2√2 n m ε^{-1})`.  The
ceiling turns the real-valued width into a qubit count. -/
def qiteQubitCount (k : ℕ) (C : ℝ) (_d n m : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil ((k : ℝ) * (qiteDomainWidth C n m ε) ^ _d)

/-- The local-region domain width of Theorem 2 (Eq. (37), inner logarithm). -/
def theorem2DomainWidth (C : ℝ) (d n S : ℕ) (ε : ℝ) : ℝ :=
  2 * C *
    Real.log (2 * Real.sqrt 2 * (n : ℝ) *
      ((S : ℝ) + C * (Real.log (8 * (n : ℝ) * C * (2 * C) ^ (d + 1) / ε)) ^ d))

/-- The qubit budget `N_q = k(2C)^d ln^d(2√2 n (|S| + C ln^d(8nC(2C)^{d+1}ε^{-1})))`
of Theorem 2, Eq. (37), written as `k ν^d` with `ν` the width of
`theorem2DomainWidth`. -/
def theorem2QubitCount (k : ℕ) (C : ℝ) (d n S : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil ((k : ℝ) * (theorem2DomainWidth C d n S ε) ^ d)

universe u

/-- `ActsOnAtMost q U` says that the operator `U` acts on at most `q` qubits:
there is a splitting of the register into a `q`-qubit factor `Fin (2^q')` with
`q' ≤ q` and a complement `β` such that `U` is block diagonal with respect to
this splitting (it never maps between different complement configurations).
This is the locality condition used in Theorems 1 and 2: the unitary `Û_s`
produced by QITE acts on `N_q` qubits only. -/
def ActsOnAtMost {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (U : Matrix ι ι ℂ) : Prop :=
  ∃ (q' : ℕ), q' ≤ q ∧ ∃ (β : Type u) (_ : Fintype β) (e : ι ≃ Fin (2 ^ q') × β),
    ∀ i j : ι, (e i).2 ≠ (e j).2 → U i j = 0

/-- The identity acts on no qubits at all, hence on at most `q` qubits. -/
theorem actsOnAtMost_one {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ℕ) :
    ActsOnAtMost q (1 : Matrix ι ι ℂ) := by
  refine ⟨0, Nat.zero_le _, ι, inferInstance, (Equiv.uniqueProd ι (Fin 1)).symm, ?_⟩
  intro i j hij
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h
    exact absurd rfl hij
  · simp [h]

/-- The pure-state density matrix `|ψ⟩⟨ψ|`. -/
def pureDensity {ι : Type*} [Fintype ι] (ψ : State ι) : Matrix ι ι ℂ :=
  fun i j => amp ψ i * star (amp ψ j)

/-- The partial trace over the second (complement) factor of a bipartite
register `α × β`.  This is the `tr_{∖S}` of Eq. (38) in the model where the
region `S` indexes the `α` factor. -/
def partialTraceRight {α β : Type*} [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- The Schatten 1-norm (trace norm) `‖A‖₁ = tr sqrt(Aᴴ A)`, used by the trace
distance of Eq. (38).  The square root is taken through the continuous
functional calculus of the Hermitian matrix `Aᴴ A`. -/
def traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, Real.sqrt
    (Matrix.IsHermitian.eigenvalues
      (Matrix.PosSemidef.isHermitian (Matrix.posSemidef_self_mul_conjTranspose Aᴴ)) i)

/-- The trace distance `‖ρ − σ‖₁`. -/
def traceDist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ σ : Matrix ι ι ℂ) : ℝ := traceNorm (ρ - σ)

end Qatlib.Papers.QImagTime19.MainResults
