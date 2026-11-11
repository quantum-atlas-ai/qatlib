/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Matrix.Rank

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-level model for *Quantum Algorithms for Variants of Average-Case Lattice Problems via Filtering*

Fixed source version: arXiv:2108.11015 (the `metadata/papers/LatticeFilter21.json`
claims are transcribed from that version).

This module fixes the vocabulary used by the paper layer of `LatticeFilter21`:

* `MachineKind`/`PolyAlgorithm`/`IsPolynomialTime`/`SolvableByFamily` are the
  paper-level computational interface.  The repository does not carry a
  circuit-level QPT model, so a "polynomial-time quantum algorithm" is rendered
  as an `n`-indexed family of algorithms with `kind = .quantum`, a polynomial
  cost bound and a `run` function; the correctness statement is the mathematical
  problem specification.  This is the same abstraction level at which the paper
  states its reductions (it never counts gates inside the reductions).
* `BigOmega`, `PolynomiallyBounded`, `Negligible`, `NonNegligible` render the
  asymptotic parameter conditions of the paper.
* `IsSISSolution`, `lweState`, `clweState`, `sisState`, `qftVec`, `fhat` render
  the lattice problems and state constructions of Section 1.1 and Section 3.
-/

namespace Qatlib.Papers.LatticeFilter21.MainResults

open scoped BigOperators
open Asymptotics Filter

set_option autoImplicit false

/-! ## Computational interface -/

/-- Whether the algorithm is classical or quantum. -/
inductive MachineKind : Type
  | classical
  | quantum
  deriving DecidableEq, Repr

/-- A paper-level algorithm: a machine kind, an input-size-indexed cost, a
success probability (used by the EDCP statements, whose solving probability is
only required to be inverse-polynomial), and the input-output function. -/
structure PolyAlgorithm (Input Output : Type) where
  kind : MachineKind
  cost : ℕ → ℕ
  successProb : ℕ → ℝ
  run : Input → Output

/-- The paper's "polynomial time": one polynomial bounds the cost at every
input size `n`. -/
def IsPolynomialTime {Input Output : Type} (A : PolyAlgorithm Input Output) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, A.cost n ≤ C * (n + 1) ^ d

/-- An `n`-indexed family of algorithms of the given kind, whose `n`-th member
has polynomial cost and satisfies `spec n` on every instance.  This is the
paper-level rendering of "there is a polynomial-time algorithm that solves the
problem". -/
def SolvableByFamily (kind : MachineKind)
    (I O : ℕ → Type) (spec : ∀ n, I n → O n → Prop) : Prop :=
  ∃ alg : ∀ n, PolyAlgorithm (I n) (O n),
    (∀ n, (alg n).kind = kind) ∧
    (∃ C d : ℕ, ∀ n, (alg n).cost n ≤ C * (n + 1) ^ d) ∧
    (∀ n (i : I n), spec n i ((alg n).run i))

/-- Same as `SolvableByFamily`, but the algorithm also has success probability
at least the prescribed inverse-polynomial schedule `p` (used for EDCP, whose
definition only asks for `poly(1/(n log q))` success probability). -/
def SolvableByFamilyWithProbability (kind : MachineKind) (p : ℕ → ℝ)
    (I O : ℕ → Type) (spec : ∀ n, I n → O n → Prop) : Prop :=
  ∃ alg : ∀ n, PolyAlgorithm (I n) (O n),
    (∀ n, (alg n).kind = kind) ∧
    (∃ C d : ℕ, ∀ n, (alg n).cost n ≤ C * (n + 1) ^ d) ∧
    (∀ n, p n ≤ (alg n).successProb n) ∧
    (∀ n (i : I n), spec n i ((alg n).run i))

/-- A quantum state over a finite index type, written as an amplitude function. -/
abbrev QState (ι : Type) : Type := ι → ℂ

/-- The `ℓ¹` distance of two amplitude functions on a finite index type.  The
paper only uses this to mean "negligibly close", so the exact metric is
immaterial; `ℓ¹` is chosen because it is a genuine metric on amplitudes. -/
noncomputable def stateDist {ι : Type} [Fintype ι] (φ ψ : QState ι) : ℝ :=
  ∑ i, ‖φ i - ψ i‖

/-- "There is an `n`-indexed family of quantum algorithms that, in polynomial
time, prepares a state negligibly close (in `n`) to the target family `target`."
This is the state-construction form of `C|LWE⟩`. -/
def ConstructibleInPolyTime (I : ℕ → Type) (O : ℕ → Type) [∀ n, Fintype (O n)]
    (target : ∀ n, I n → QState (O n)) : Prop :=
  ∃ alg : ∀ n, PolyAlgorithm (I n) (QState (O n)),
    (∀ n, (alg n).kind = MachineKind.quantum) ∧
    (∃ C d : ℕ, ∀ n, (alg n).cost n ≤ C * (n + 1) ^ d) ∧
    (∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ i : I n,
      stateDist ((alg n).run i) (target n i) ≤ (n : ℝ) ^ (-(k : ℤ)))

/-! ## Asymptotic vocabulary -/

/-- `f ∈ Ω(g)` in the paper's sense: a positive constant times `f` is
eventually below `g`. -/
def BigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, c * f n ≤ g n

/-- `q` is polynomially large. -/
def PolynomiallyBounded (q : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, q n ≤ C * (n + 1) ^ d

/-- A real sequence is negligible when it has super-polynomial decay. -/
def Negligible (g : ℕ → ℝ) : Prop :=
  SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) g

/-- A real sequence is non-negligible when it is eventually at least the
reciprocal of a polynomial. -/
def NonNegligible (η : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ((n : ℝ) + 1) ^ (-(k : ℤ)) ≤ η n

/-! ## The ring `Z_q` and norms -/

/-- The ring `Z_q`. -/
abbrev Zq (q : ℕ) : Type := ZMod q

/-- The `ℓ∞`-type shortness condition: the centred integer representative of
`x` has absolute value at most `β`.  For `SIS^∞` this is exactly the paper's
`‖x‖∞ ≤ β`. -/
def IsShort {q : ℕ} (β : ℤ) (x : Zq q) : Prop :=
  |ZMod.valMinAbs x| ≤ β

/-- A valid `SIS^∞_{n,m,q,β}` solution for the matrix `A`: nonzero, killed by
`A`, and `ℓ∞`-short. -/
def IsSISSolution {n m q : ℕ} (β : ℤ)
    (A : Matrix (Fin n) (Fin m) (Zq q)) (x : Fin m → Zq q) : Prop :=
  x ≠ 0 ∧ A.mulVec x = 0 ∧ ∀ i, IsShort β (x i)

/-! ## Fourier transforms, LWE states and the SIS state -/

/-- `1/√q` in `ℂ`, the normalisation of the paper's DFT
`f̂(y) = q^{-1/2} ∑_x ω_q^{xy} f(x)`. -/
noncomputable def invSqrt (q : ℕ) : ℂ := ((Real.sqrt (q : ℝ) : ℝ) : ℂ)⁻¹

/-- The paper's DFT of an amplitude function on `Z_q`. -/
noncomputable def fhat {q : ℕ} [NeZero q] (f : Zq q → ℂ) (y : Zq q) : ℂ :=
  invSqrt q * ∑ x : Zq q, ZMod.stdAddChar (x * y) * f x

/-- The product amplitude `f̂(e) = ∏_i f̂(e_i)` on `Z_q^m`. -/
noncomputable def fhatVec {q m : ℕ} [NeZero q] (f : Zq q → ℂ) (e : Fin m → Zq q) : ℂ :=
  ∏ i, fhat f (e i)

/-- The LWE state `|φ_u⟩ = ∑_e f̂(e) |uᵀA + e⟩` of Eq. (5). -/
noncomputable def lweState {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) (u : Fin n → Zq q) :
    QState (Fin m → Zq q) :=
  fun z => fhatVec f (fun i => z i - A.mulVec u i)

/-- The coherent-LWE state `∑_u |φ_u⟩ ⊗ |u⟩`, with the `u` register summed
out: its amplitude at `z` is `∑_u f̂(z - uᵀA)`. -/
noncomputable def clweState {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) : QState (Fin m → Zq q) :=
  fun z => ∑ u : Fin n → Zq q, lweState f A u z

/-- The SIS state `∑_{z : Az = 0} f(z) |z⟩`. -/
noncomputable def sisState {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin n) (Fin m) (Zq q)) : QState (Fin m → Zq q) :=
  fun z => if A.mulVec z = 0 then ∏ i, f (z i) else 0

/-- The `m`-fold QFT `QFT_q^⊗m` with the paper's normalisation. -/
noncomputable def qftVec {m q : ℕ} [NeZero q] (φ : QState (Fin m → Zq q)) :
    QState (Fin m → Zq q) :=
  fun y => (invSqrt q) ^ m * ∑ x, (∏ i, ZMod.stdAddChar (x i * y i)) * φ x

/-! ## The `S|LWE⟩` and `EDCP` problem instances -/

/-- An instance of `S|LWE⟩`: the public matrix and the secret that generates
the LWE samples.  The quantum samples themselves are determined by `A` and
`u` through `lweState`, so no separate oracle is carried. -/
structure SLWEInstance (n m q : ℕ) where
  A : Matrix (Fin m) (Fin n) (Zq q)
  u : Fin n → Zq q

/-- Solving `S|LWE⟩` means outputting the secret. -/
def SLWESpec {n m q : ℕ} (inst : SLWEInstance n m q) (out : Fin n → Zq q) : Prop :=
  out = inst.u

/-- The information carried by an `EDCP` instance: the common offset `x` and the
secret difference `s`; the sampled states are `∑_j D(j)|j⟩|x + j·s⟩`. -/
structure EDCPInstance (n m q : ℕ) where
  x : Fin n → Zq q
  s : Fin n → Zq q

/-- Solving `EDCP` means outputting `s`. -/
def EDCPSpec {n m q : ℕ} (inst : EDCPInstance n m q) (out : Fin n → Zq q) : Prop :=
  out = inst.s

end Qatlib.Papers.LatticeFilter21.MainResults
