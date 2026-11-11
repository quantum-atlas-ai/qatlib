/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeFilter21.MainResults.Model.Distributions

set_option backward.isDefEq.respectTransparency false

/-!
# Problem statements of `LatticeFilter21`

Fixed source version: arXiv:2108.11015.

This module renders the problem families of Section 1.1 at the paper's
abstraction level:

* `CLWEConstructible` — `C|LWE⟩_{n,m,q,f}` (Definition 6): construct the equal
  superposition of all LWE states for the given matrix `A` (no secret);
* `SLWESolvable` — `S|LWE⟩_{n,m,q,f}` (Definition 7): recover the secret `u`
  from the LWE-state samples;
* `edcpState`/`EDCPSolvable` — `EDCP_{n,m,q,D}` (Definition 11): recover `s`
  from `m` copies of `∑_j D(j)|j⟩|x + j·s⟩`;
* `SISSolvable` — `SIS^∞_{n,m,q,β}`.

The quantum state given to the algorithm is an *input* (as in the paper's
oracle formulations), so `SolvableFromState` is the search-problem analogue of
`SolvableByFamily`.
-/

namespace Qatlib.Papers.LatticeFilter21.MainResults

open scoped BigOperators
open Finset

set_option autoImplicit false

/-! ## Search problems whose input is a quantum state -/

/-- A family of algorithms that receive the quantum state of the `n`-th
instance and output a candidate solution (this is the paper's oracle model:
`S|LWE⟩` and `EDCP` only give access to states). -/
def SolvableFromState (kind : MachineKind) (q : ℕ → ℕ)
    (Inst St : ℕ → Type) (state : ∀ n, Inst n → QState (St n))
    (spec : ∀ n, Inst n → (Fin n → Zq (q n)) → Prop) : Prop :=
  ∃ alg : ∀ n, PolyAlgorithm (QState (St n)) (Fin n → Zq (q n)),
    (∀ n, (alg n).kind = kind) ∧
    (∃ C d : ℕ, ∀ n, (alg n).cost n ≤ C * (n + 1) ^ d) ∧
    (∀ n (i : Inst n), spec n i ((alg n).run (state n i)))

/-- `SolvableFromState` with the inverse-polynomial success probability that the
`EDCP` definition requires (Definition 11). -/
def SolvableFromStateWithProbability (kind : MachineKind) (p : ℕ → ℝ) (q : ℕ → ℕ)
    (Inst St : ℕ → Type) (state : ∀ n, Inst n → QState (St n))
    (spec : ∀ n, Inst n → (Fin n → Zq (q n)) → Prop) : Prop :=
  ∃ alg : ∀ n, PolyAlgorithm (QState (St n)) (Fin n → Zq (q n)),
    (∀ n, (alg n).kind = kind) ∧
    (∃ C d : ℕ, ∀ n, (alg n).cost n ≤ C * (n + 1) ^ d) ∧
    (∀ n, p n ≤ (alg n).successProb n) ∧
    (∀ n (i : Inst n), spec n i ((alg n).run (state n i)))

/-! ## `C|LWE⟩` (Definition 6) -/

/-- The LWE state with error amplitude `g` (not necessarily a Fourier
transform): `∑_e g(e)|uᵀA + e⟩` on the sample register. -/
noncomputable def rawLweState {n m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) (u : Fin n → Zq q) :
    QState (Fin m → Zq q) :=
  fun z => ∏ i, g (z i - A.mulVec u i)

/-- The coherent sum `∑_u ∑_e g(e)|uᵀA + e⟩` over all secrets (Definition 6). -/
noncomputable def rawClweState {n m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) : QState (Fin m → Zq q) :=
  fun z => ∑ u : Fin n → Zq q, rawLweState g A u z

/-- `lweState` is the raw state with amplitude `f̂` (this is the state of
Eq. (5)); the lemma records the definitional identification. -/
theorem lweState_eq_raw {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) (u : Fin n → Zq q) :
    lweState f A u = rawLweState (fhat f) A u := rfl

/-- `clweState` is the raw coherent state with amplitude `f̂`. -/
theorem clweState_eq_raw {n m q : ℕ} [NeZero q] (f : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) :
    clweState f A = rawClweState (fhat f) A := rfl

/-- `C|LWE⟩_{n,m,q,g}`: from `A`, construct the coherent superposition
`∑_u ∑_e g(e)|uᵀA + e⟩` of all LWE states.  There is no secret vector, so this
is a state-construction problem. -/
def CLWEConstructible (q m : ℕ → ℕ) [∀ n, NeZero (q n)]
    (g : ∀ n, Zq (q n) → ℂ) : Prop :=
  ConstructibleInPolyTime
    (fun n => Matrix (Fin (m n)) (Fin n) (Zq (q n)))
    (fun n => Fin (m n) → Zq (q n))
    (fun n A => rawClweState (g n) A)

/-! ## `S|LWE⟩` (Definition 7) -/

/-- `S|LWE⟩_{n,m,q,g}`: given one LWE state with error amplitude `g` generated
by `(A, u)`, output `u`. -/
def SLWESolvable (q m : ℕ → ℕ) [∀ n, NeZero (q n)]
    (g : ∀ n, Zq (q n) → ℂ) : Prop :=
  SolvableFromState MachineKind.quantum q
    (fun n => SLWEInstance n (m n) (q n)) (fun n => Fin (m n) → Zq (q n))
    (fun n inst => rawLweState (g n) inst.A inst.u)
    (fun n inst out => SLWESpec inst out)

/-! ## `EDCP` (Definition 11) -/

/-- The `m` input states `⊗_{i=1}^{m} ∑_{j} D(j)|j⟩|x + j·s⟩` of an EDCP
instance, in the joint register `∏_i (j_i, y_i)` where `j_i ∈ Z_q` is the error
value and `y_i ∈ Z_q^n` the sample vector `x + j_i·s`. -/
noncomputable def edcpState {n m q : ℕ} [NeZero q] (D : Zq q → ℂ)
    (inst : EDCPInstance n m q) : QState (Fin m → Zq q × (Fin n → Zq q)) :=
  fun p => ∏ i, if (p i).2 = inst.x + (p i).1 • inst.s then D (p i).1 else 0

/-- `EDCP_{n,m,q,D}` is solvable when some quantum algorithm, in time
`poly(n log q)` and with success probability `poly(1/(n log q))`, recovers `s`
from the `m` states.  The schedule `edcpSchedule` encodes the inverse-polynomial
success requirement (Definition 11). -/
def EDCPSolvable (q m : ℕ → ℕ) [∀ n, NeZero (q n)]
    (D : ∀ n, Zq (q n) → ℂ) : Prop :=
  SolvableFromStateWithProbability MachineKind.quantum (edcpSchedule q) q
    (fun n => EDCPInstance n (m n) (q n))
    (fun n => Fin (m n) → Zq (q n) × (Fin n → Zq (q n)))
    (fun n inst => edcpState (D n) inst)
    (fun n inst out => EDCPSpec inst out)

/-! ## `SIS^∞` -/

/-- `SIS^∞_{n,m,q,β}` is solvable by a family of algorithms of kind `k`. -/
def SISSolvable (k : MachineKind) (q m : ℕ → ℕ) (β : ℕ → ℤ) : Prop :=
  SolvableByFamily k
    (fun n => Matrix (Fin n) (Fin (m n)) (Zq (q n)))
    (fun n => Fin (m n) → Zq (q n))
    (fun n A x => IsSISSolution (β n) A x)

end Qatlib.Papers.LatticeFilter21.MainResults
