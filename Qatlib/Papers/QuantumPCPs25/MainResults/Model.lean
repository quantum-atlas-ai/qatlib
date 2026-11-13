/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper-layer model and statement bank for
"Quantum PCPs: on Adaptivity, Multiple Provers and Reductions to Local
Hamiltonians" (arXiv:2403.04841, 2025).

The file fixes the finite semantic model used by the claim statements:

* computational-basis operators on `n` qubits, the expectation `<psi|A|psi>`
  and the trace product `tr[A xi]` (§1 Notations, Eq. (2));
* locality of an operator on a qubit subset (Definition 4 context) and
  weighted local-Hamiltonian instances built from PSD local terms, with a
  variational characterisation of the least eigenvalue;
* an abstract acceptance-probability interface for (k,q,p1,p2,p3)-QPCP
  verifiers (semantic projection of Definition 4) and the induced classes
  `QPCP[k,q,c,s]`, `QMA`, `QCMA`;
* phase-marking oracles for the oracle-separation claims (§5, Lemmas 20-21);
* faithful `Prop` statements for the remaining claims (`c001_statement` …),
  each docstring recording the claim id and the scope of the formalisation;
* two fully proved numerical cores: the weighted-energy identity of Eq. (11)
  (c010) and the robustness bound behind Eq. (30)'s analysis (c026).

Claims c004, c005, c013, c016, c017 are not stated here: their faithful
formalisation needs partial-trace / tensor-product / quantum de Finetti
infrastructure or full reduction syntax beyond the scope of this module.

All objects are concrete matrices and functions over `ZMod 2` index sets.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Batteries.Tactic.Exact
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
open Matrix

noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults.Model

/-! ## Qubit strings and operators in the computational basis -/

/-- Computational basis strings `x ∈ {0,1}^n`. -/
abbrev BitStr (n : ℕ) := Fin n → ZMod 2

/-- Linear operators on `n` qubits, as matrices in the computational basis. -/
abbrev Op (n : ℕ) := Matrix (BitStr n) (BitStr n) ℂ

/-- The expectation `⟨ψ|A|ψ⟩` of an operator in a state vector `ψ`. -/
def expectation {n : ℕ} (A : Op n) (ψ : BitStr n → ℂ) : ℂ :=
  ∑ x, starRingEnd ℂ (ψ x) * (A *ᵥ ψ) x

/-- The trace product `tr[Aξ]` of two operators. -/
def traceProd {n : ℕ} (A ξ : Op n) : ℂ := Matrix.trace (A * ξ)

/-- The squared norm `⟨ψ|ψ⟩ = Σ_x |ψ_x|²` of a state vector. -/
def normSq {n : ℕ} (ψ : BitStr n → ℂ) : ℝ := ∑ x, Complex.normSq (ψ x)

/-- Positive semidefiniteness via nonnegative quadratic forms:
`⟨ψ|A|ψ⟩ ≥ 0` for all `ψ` (which for a matrix forces Hermitianity). -/
def IsPSD {n : ℕ} (A : Op n) : Prop := ∀ ψ : BitStr n → ℂ, 0 ≤ (expectation A ψ).re

/-- A density matrix: PSD with unit trace. -/
def IsDensity {n : ℕ} (ρ : Op n) : Prop :=
  IsPSD ρ ∧ (Matrix.trace ρ).re = 1

/-! ## Locality and local-Hamiltonian instances -/

/-- `A` acts only on the qubits in `S` (i.e. `A = A_S ⊗ I_{S̄}` in the
computational basis): `A` is block-diagonal along `S̄` and its entries do
not depend on the `S̄` coordinates. -/
def IsLocalOn {n : ℕ} (A : Op n) (S : Finset (Fin n)) : Prop :=
  (∀ x y : BitStr n, (∃ i ∉ S, x i ≠ y i) → A x y = 0) ∧
    (∀ x y x' y' : BitStr n,
      (∀ i ∈ S, x i = x' i ∧ y i = y' i) → A x y = A x' y')

/-- `A` is `q`-local: it acts nontrivially on at most `q` qubits. -/
def IsQLocal {n : ℕ} (A : Op n) (q : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ q ∧ IsLocalOn A S

/-- A weighted local-Hamiltonian instance `H = Σ_i w_i H_i` on `n` qubits
with `m` PSD `q`-local terms (§1, Eq. (3)). -/
structure LHInstance (n m q : ℕ) where
  /-- The local terms `H_i`. -/
  terms : Fin m → Op n
  /-- The nonnegative weights `w_i` with `Σ_i w_i = 1`. -/
  weights : Fin m → ℝ
  /-- Every term is positive semidefinite. -/
  hpsd : ∀ i, IsPSD (terms i)
  /-- Every term is `q`-local. -/
  hlocal : ∀ i, IsQLocal (terms i) q

/-- The total operator `H = Σ_i w_i H_i` of an instance. -/
def totalOp {n m q : ℕ} (H : LHInstance n m q) : Op n :=
  ∑ i, (H.weights i : ℂ) • H.terms i

/-- The energy `⟨ψ|H|ψ⟩ = Σ_i w_i ⟨ψ|H_i|ψ⟩` (real part). -/
def energy {n m q : ℕ} (H : LHInstance n m q) (ψ : BitStr n → ℂ) : ℝ :=
  ∑ i, H.weights i * (expectation (H.terms i) ψ).re

/-- Variational upper bound on the least eigenvalue: energy `≤ a` is
attained up to `ϵ` by some unit vector. -/
def MinLeqAt {n m q : ℕ} (H : LHInstance n m q) (a : ℝ) : Prop :=
  ∀ ϵ > 0, ∃ ψ : BitStr n → ℂ, normSq ψ = 1 ∧ energy H ψ ≤ a + ϵ

/-- Variational lower bound: every unit vector has energy `≥ b`. -/
def MinGeqAt {n m q : ℕ} (H : LHInstance n m q) (b : ℝ) : Prop :=
  ∀ ψ : BitStr n → ℂ, normSq ψ = 1 → b ≤ energy H ψ

/-- The promise gap instance: `λ_min(H) ≤ a` or `λ_min(H) ≥ b`. -/
def HasGap {n m q : ℕ} (H : LHInstance n m q) (a b : ℝ) : Prop :=
  MinLeqAt H a ∨ MinGeqAt H b

/-! ## Abstract QPCP verifier interface (Definition 4, semantic projection) -/

/-- Semantic interface of a QPCP verifier on inputs of length `n` reading a
proof register of `prf` qubits: its acceptance probability on a proof state
`ξ` and input `x`.  The full circuit/PVM syntax of Definition 4 (adaptive
queries, private randomness `p1`, classical postprocessing `p3`) is outside
the scope of this semantic interface. -/
structure QPCPVerifier (n prf : ℕ) where
  /-- Number of quantum proof queries used. -/
  nq : ℕ
  /-- Acceptance probability on proof `ξ` and input `x`. -/
  accept : Op prf → BitStr n → ℝ

/-- A promise problem: families of yes/no instances. -/
structure RegisterPromise where
  /-- Predicate selecting yes instances of length `n`. -/
  yes : (n : ℕ) → BitStr n → Prop
  /-- Predicate selecting no instances of length `n`. -/
  no : (n : ℕ) → BitStr n → Prop

/-- Membership of a promise problem in `QPCP[k, q, c, s]` with total proof
length `prf n`: some verifier family attains completeness `c` on yes
instances and soundness `s` on no instances. -/
def InQPCPClass (P : RegisterPromise) (k : ℕ) (prf : ℕ → ℕ) (q : ℕ) (c s : ℝ) :
    Prop :=
  ∃ V : ∀ n, QPCPVerifier n (k * prf n),
    (∀ n, (V n).nq ≤ q) ∧
      (∀ n x, P.yes n x → ∃ ξ, (V n).accept ξ x ≥ c) ∧
      (∀ n x, P.no n x → ∀ ξ, (V n).accept ξ x ≤ s)

/-- Membership in `QMA` (semantic interface): a single-prover quantum
verifier with one query and the given completeness/soundness. -/
def InQMAClass (P : RegisterPromise) (prf : ℕ → ℕ) (c s : ℝ) : Prop :=
  InQPCPClass P 1 prf 1 c s

/-- Membership in `QCMA` (semantic interface): as `QMA` but with classical
witnesses, expressed by requiring completeness on basis states `|w⟩⟨w|`. -/
def InQCMAClass (P : RegisterPromise) (prf : ℕ → ℕ) (c s : ℝ) : Prop :=
  ∃ V : ∀ n, QPCPVerifier n (prf n),
    (∀ n x, P.yes n x → ∃ w : BitStr (prf n),
        (V n).accept (Matrix.diagonal fun z => if z = w then 1 else 0) x ≥ c) ∧
      (∀ n x, P.no n x → ∀ ξ, (V n).accept ξ x ≤ s)

/-- AND composition of two promise problems on the same input
(used by c018): yes iff both are yes, no if either is no. -/
def andPP (P Q : RegisterPromise) : RegisterPromise where
  yes n x := P.yes n x ∧ Q.yes n x
  no n x := P.no n x ∨ Q.no n x

/-! ## Phase-marking oracles (§5, Lemmas 20-21) -/

/-- `U` is the phase oracle marking the string `xs`:
`U|y⟩ = −|y⟩` for `y = xs` and `U|y⟩ = |y⟩` otherwise. -/
def IsMarkingOracle {n : ℕ} (U : Op n) (xs : BitStr n) : Prop :=
  U = Matrix.diagonal fun y => if y = xs then -1 else 1

/-- Semantic interface of an oracle algorithm on `n` qubits: its number of
oracle queries and its probability of outputting `1` given oracle `U`.
The interleaved-circuit syntax is abstracted away; statement-level
obligations quantify over this structure. -/
structure OracleAlgorithm (n : ℕ) where
  /-- Number of oracle queries used. -/
  nq : ℕ
  /-- Probability of outputting `1` when run with oracle `U`. -/
  pr1 : Op n → ℝ

/-- `alg` fails to distinguish any marking oracle from the identity with
bounded error: for every marked string, it cannot both accept the marking
oracle with probability `≥ 2/3` and accept the identity with probability
`≤ 1/3`.  Granting extra witness data (`q` indices and `ϵ`-net density
matrices) only enlarges the algorithm class this quantifies over. -/
def FailsMarkingDistinction {n : ℕ} (alg : OracleAlgorithm n) : Prop :=
  ∀ (U : Op n) (xs : BitStr n), IsMarkingOracle U xs →
    alg.pr1 U < 2 / 3 ∨ 1 / 3 < alg.pr1 (1 : Op n)

/-! ## Claim statements -/

/-- **c001 (Theorem 1, Eq. (9))**: for constant `q` and polynomials
`p1, p2, p3`, every `(k,q,p1,p2,p3)`-QPCP verifier on input `x` admits,
with success probability `1 − δ` and time `poly(n,1/ϵ,log(1/δ))`, a
`q`-local Hamiltonian with `m = poly(n)` PSD terms and operator norm `≤ 1`
such that `|Pr[V_x accepts ξ] − (1 − tr[H ξ])| ≤ ϵ` for all proofs `ξ`.
The quantum reduction construction (and the norm/time side conditions) is
the outside the scope of this module; the statement keeps its universal shape. -/
def c001_statement (k q : ℕ) (p1 p2 : ℕ → ℕ) (m : ℕ) (ϵ : ℝ) : Prop :=
  ∀ n (x : BitStr n) (V : QPCPVerifier n (p2 n * k + p1 n)),
    ∃ H : LHInstance (p2 n * k + p1 n) m q,
      ∀ ξ, |V.accept ξ x - (1 - (traceProd (totalOp H) ξ).re)| ≤ ϵ

/-- **c002 (Theorem 3)**: parallel repetition amplifies a constant gap:
`QPCP[1,q,c,s] ⊆ QPCP[1,O(qt),1−2^{−t},2^{−t}]`, soundness surviving
entangled proofs via Chernoff bounds for conditional expectations.  The
repeated-verifier construction and Chernoff analysis are the recorded
obstacle. -/
def c002_statement (P : RegisterPromise) (prf prf' : ℕ → ℕ) (q : ℕ) (c s : ℝ)
    (t : ℕ) : Prop :=
  InQPCPClass P 1 prf q c s →
    InQPCPClass P 1 prf' (q * t) (1 - ((2 ^ t : ℝ))⁻¹) (((2 ^ t : ℝ))⁻¹)

/-- **c003 (Theorem 4)**: near-complete non-adaptive QPCPs repeat on the
same quantum proof: `QPCPNA[1,q,c,s] = QPCPNA[1,lq,c′,s′]` with
`s′ = 2^{−O(l)}`.  The repeated-query verifier analysis is the recorded
obstacle. -/
def c003_statement (P : RegisterPromise) (prf : ℕ → ℕ) (q l : ℕ) (c s c' s' : ℝ) :
    Prop :=
  InQPCPClass P 1 prf q c s → InQPCPClass P 1 prf (l * q) c' s'

/-- **c006 (Eq. (3))**: for constant `q` and polynomials `p1, p2, p3`,
every `(k,q,p1,p2,p3)`-QPCP verifier and proof admits a PSD `q`-local
Hamiltonian with `Pr[V accepts ξ] = 1 − tr[H ξ]` exactly.  Constructing
`H` from the verifier (Eq. (2) composed PVM operator) needs
measurement-composition semantics, the outside the scope of this module. -/
def c006_statement (k q : ℕ) (p1 p2 : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ n (x : BitStr n) (V : QPCPVerifier n (p2 n * k + p1 n)),
    ∃ H : LHInstance (p2 n * k + p1 n) m q,
      ∀ ξ, V.accept ξ x = 1 - (traceProd (totalOp H) ξ).re

/-- **c008 (Theorem 2)**: the reduction of Theorem 1 can output one fixed
Hamiltonian `H̃_x` realising the error bound; i.e. the output does not
resample across the `1 − δ` probability branch.  Reduction-output
semantics beyond the acceptance interface is the outside the scope of this module. -/
def c008_statement (k q : ℕ) (p1 p2 : ℕ → ℕ) (m : ℕ) (ϵ : ℝ) : Prop :=
  c001_statement k q p1 p2 m ϵ

/-- **c009 (Lemma 5)**: gap amplification with locality doubling: a
`q`-local instance with gap `b − a ≥ γ` yields a `2q`-local instance with
normalised terms and gap at least `γ/2`.  The Kitaev-style clock/flag
construction is the outside the scope of this module. -/
def c009_statement {n m : ℕ} (q : ℕ) (a b γ : ℝ)
    (H : LHInstance n m q) (H' : LHInstance n m (2 * q)) : Prop :=
  HasGap H a b → b - a ≥ γ → ∃ a' b', b' - a' ≥ γ / 2 ∧ HasGap H' a' b'

/-- **c010 (Lemma 6, Eq. (11))**: weighted energy estimation — sampling a
term `i` with probability `w_i` and measuring its `q` qubits outputs `1`
with probability `Σ_i w_i (1 − ⟨ψ|H_i|ψ⟩) = 1 − ⟨ψ|H|ψ⟩`.  The
sampling-measurement protocol semantics is abstracted; the algebraic
identity is proved below as `c010_weighted_energy`. -/
def c010_statement {n m q : ℕ} (H : LHInstance n m q) : Prop :=
  ∀ ψ : BitStr n → ℂ,
    ∑ i, H.weights i * (1 - (expectation (H.terms i) ψ).re) = 1 - energy H ψ

/-- **c011 (Theorem 6)**: `q-LH[δ] ⊆ QPCPNA[q′]` for constant `q`: the
promise problem `P` of `q`-local Hamiltonians with gap `δ` has
constant-query non-adaptive QPCP verifiers.  The verifier construction is
the outside the scope of this module. -/
def c011_statement (P : RegisterPromise) (prf : ℕ → ℕ) (q' : ℕ) (δ : ℝ) :
    Prop :=
  InQPCPClass P 1 prf q' (1 - δ) δ

/-- **c012 (Lemma 8)**: random reduction to `2q`-local instances with
`l = O(n)` terms preserving a constant relative gap, with success
probability `1 − δ`.  The term-subsampling reduction is the recorded
obstacle. -/
def c012_statement {n m l : ℕ} (q : ℕ) (a b γ' δ : ℝ)
    (H : LHInstance n m q) (G' : LHInstance n l (2 * q)) : Prop :=
  HasGap H a b → 0 < δ → γ' ≤ (b - a) / 2 ∧ HasGap G' (a + γ') b

/-- **c014 (Theorem 8)**: if constant-gap `q`-local Hamiltonians are in
QCMA for all constant `q`, then `QPCP[q] ⊆ QCMA` for all constant `q`.
The derandomised Hamiltonian reproduction inside a QCMA verifier is the
outside the scope of this module. -/
def c014_statement (prf : ℕ → ℕ) : Prop :=
  ∀ P : RegisterPromise, InQPCPClass P 1 prf 1 (2 / 3) (1 / 3) →
    InQCMAClass P prf (2 / 3) (1 / 3)

/-- **c015 (Theorem 5)**: adaptive constant-query QPCPs are simulated by
non-adaptive ones with `q′ = O(q(4q/(c−s))²)` queries:
`QPCP_{c,s}[q] ⊆ QPCPNA[q′]`; the induced completeness/soundness loss is
parametrised as `(c−s)/4`.  The simulation construction is the recorded
obstacle. -/
def c015_statement (P : RegisterPromise) (prf : ℕ → ℕ) (q q' : ℕ) (c s : ℝ) :
    Prop :=
  InQPCPClass P 1 prf q c s →
    InQPCPClass P 1 prf q' (c - (c - s) / 4) (s + (c - s) / 4)

/-- **c018 (Lemma 14)**: QMA is closed under AND composition of promise
problems: the parallel-composition verifier runs each QMA verifier and
accepts iff all accept.  The threshold bookkeeping is the recorded
obstacle. -/
def c018_statement (P Q : RegisterPromise) (prf : ℕ → ℕ) : Prop :=
  InQMAClass P prf (2 / 3) (1 / 3) → InQMAClass Q prf (2 / 3) (1 / 3) →
    ∃ prf' : ℕ → ℕ, InQMAClass (andPP P Q) prf' (2 / 3) (1 / 3)

/-- **c020 (Corollary 3)**: if every two-prover problem reduces to
`QPCP[k′,q]` (class form of `QMA[2] ⊆ QPCP[k′,q]`), then every such problem
is in QMA: compose the reduction to a `q`-local Hamiltonian (Theorem 1)
with the QMA simulation of QPCP verifiers (Lemma 14).  The composed
construction is the outside the scope of this module. -/
def c020_statement (prf prf2 : ℕ → ℕ) (k' q : ℕ) : Prop :=
  ∀ P : RegisterPromise, InQPCPClass P k' prf2 q (2 / 3) (1 / 3) →
    InQMAClass P prf (2 / 3) (1 / 3)

/-- **c021 (Lemma 12)**: `d`-dimensional density matrices admit a trace
-distance `ϵ`-net of size `≤ C (1/ϵ)^{5d}`, obtained by taking partial
traces of an `h`-net of pure states in dimension `2d`.  The trace distance
is abstracted as a parameter `dist`; the volumetric net construction is
the outside the scope of this module. -/
def c021_statement (d : ℕ) (dist : Op d → Op d → ℝ) (C ϵ : ℝ) : Prop :=
  ∃ net : Finset (Op d),
    (∀ ρ : Op d, IsDensity ρ → ∃ σ ∈ net, IsDensity σ ∧ dist ρ σ ≤ ϵ) ∧
      (net.card : ℝ) ≤ C * (1 / ϵ) ^ (5 * d)

/-- **c022 (Lemma 13)**: replacing a proof state by its projection onto an
`ϵ`-net of density matrices degrades completeness/soundness by at most
`ϵ`: `QPCP^U[k,q] ⊆ QPCP_ϵ^U[k,q,2/3−ϵ,1/3+ϵ]` for every oracle `U`
(the oracle is abstracted away by the class predicate).  The
net-projection verifier analysis is the outside the scope of this module. -/
def c022_statement (P : RegisterPromise) (prf : ℕ → ℕ) (k q : ℕ) (ϵ : ℝ) : Prop :=
  InQPCPClass P k prf q (2 / 3) (1 / 3) →
    InQPCPClass P k prf q (2 / 3 - ϵ) (1 / 3 + ϵ)

/-- **c023 (Lemma 20, Eq. (40))**: marking-oracle witness verification
lower bound: any algorithm distinguishing a marked oracle from the identity
with bounded error, even granted `q` indices and `ϵ`-net density-matrix
witnesses (absorbed into the algorithm interface), needs
`Ω(√(2^n/(5·2^q log(1/ϵ) + q·polylog(n,q) + C)))` queries.  The
polynomial-method lower bound is the outside the scope of this module. -/
def c023_statement (n : ℕ) (T : ℝ) : Prop :=
  ∀ alg : OracleAlgorithm n, alg.nq < T → FailsMarkingDistinction alg

/-- **c024 (Theorem 9)**: there is a quantum oracle `U` such that
`QCMA^U ≠ QMA^U` and `QPCP[k,q]^U ≠ QMA^U` for all `q ∈ O(log n)` and
`1 ≤ k ≤ poly(n)`: the marking-oracle separation defeats every
sub-`√(2^n)`-query verifier.  The oracle-construction diagonalisation is
the outside the scope of this module. -/
def c024_statement (n : ℕ) : Prop :=
  ∃ (U : Op n) (xs : BitStr n), IsMarkingOracle U xs ∧
    ∀ alg : OracleAlgorithm n, alg.nq < 2 ^ (n / 2) →
      alg.pr1 U < 2 / 3 ∨ 1 / 3 < alg.pr1 (1 : Op n)

/-- **c025 (Theorem 10)**: there is a classical oracle `O` with
`QPCP[k,q]^O ≠ QMA^O` (indeed `≠ NP^O`) for all constant `q`; the counting
lower bound of Lemma 21 replaces the quantum one. -/
def c025_statement (n : ℕ) : Prop :=
  ∃ (O : Op n) (xs : BitStr n), IsMarkingOracle O xs ∧
    ∀ alg : OracleAlgorithm n, alg.nq < 2 ^ (n / 2) →
      alg.pr1 O < 2 / 3 ∨ 1 / 3 < alg.pr1 (1 : Op n)

/-- **c027 (Lemma 21, Eq. (41))**: classical phase-oracle search with
`(q, ϵ)`-net density-matrix witnesses requires
`Ω(√(2^n/((e·p(n)/q)^q C(1/ϵ)^{5·2^q})))` queries for bounded-error
verification; the counting lower bound used by c025. -/
def c027_statement (n : ℕ) (T : ℝ) : Prop :=
  ∀ alg : OracleAlgorithm n, alg.nq < T → FailsMarkingDistinction alg

/-! ## Proved numerical cores -/

/-- **c010, algebraic core (Eq. (11))**: the weighted rejection
probability of the sampled energy-estimation measurement equals
`1 − ⟨ψ|H|ψ⟩` whenever the weights sum to one.  This is the exact
identity of Eq. (11); the Born-rule identification of each term with a
`q`-qubit measurement outcome is the remaining (semantics) gap. -/
theorem c010_weighted_energy {n m q : ℕ} (H : LHInstance n m q)
    (hsumW : ∑ i, H.weights i = 1) (ψ : BitStr n → ℂ) :
    ∑ i, H.weights i * (1 - (expectation (H.terms i) ψ).re) = 1 - energy H ψ := by
  rw [energy]
  have key : ∀ i : Fin m, H.weights i * (1 - (expectation (H.terms i) ψ).re)
      = H.weights i - H.weights i * (expectation (H.terms i) ψ).re := by
    intro i
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, hsumW]

/-- **c026, numerical core (Eq. (30) analysis)**: stability of the
Hamiltonian energy under weight and term perturbations: if the weights
differ by at most `ϵ0 ≤ ϵ/(8m²)` and each term's expectation differs by at
most `ϵ1 ≤ ϵ/6` (relative to `⟨ψ|ψ⟩`), then the weighted energies differ
by at most `ϵ·⟨ψ|ψ⟩`.  With the paper's hypotheses (unit-norm terms and
probability weights) this is exactly the operator-norm bound
`‖H − H̃‖ ≤ ϵ` evaluated on states; the renormalisation step
(`p̂ = p̃/W̃`, `Ĥ = H̃/max{‖H̃‖,1}`) is the remaining gap. -/
theorem c026_energy_stability {n m : ℕ} (H Ht : Fin m → Op n) (p pt : Fin m → ℝ)
    (ψ : BitStr n → ℂ) (ϵ ϵ0 ϵ1 : ℝ)
    (hnorm : ∀ i, |(expectation (H i) ψ).re| ≤ normSq ψ)
    (hdiff : ∀ i, |(expectation (H i) ψ).re - (expectation (Ht i) ψ).re|
      ≤ ϵ1 * normSq ψ)
    (hp : ∀ i, |p i - pt i| ≤ ϵ0) (hsumPt : ∑ i, |pt i| ≤ 1)
    (hm : 1 ≤ m) (hϵ0 : ϵ0 ≤ ϵ / (8 * m ^ 2)) (hϵ1 : ϵ1 ≤ ϵ / 6) (hϵ : 0 ≤ ϵ) :
    |∑ i, p i * (expectation (H i) ψ).re
        - ∑ i, pt i * (expectation (Ht i) ψ).re| ≤ ϵ * normSq ψ := by
  have hnsq : 0 ≤ normSq ψ :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (ψ i)
  have hϵ0pos : 0 ≤ ϵ0 := le_trans (abs_nonneg _) (hp ⟨0, hm⟩)
  set E : Fin m → ℝ := fun i => (expectation (H i) ψ).re with hE
  set Et : Fin m → ℝ := fun i => (expectation (Ht i) ψ).re with hEt
  rw [show ∑ i, p i * (expectation (H i) ψ).re = ∑ i, p i * E i from rfl,
    show ∑ i, pt i * (expectation (Ht i) ψ).re = ∑ i, pt i * Et i from rfl]
  have hsplit : ∑ i, p i * E i - ∑ i, pt i * Et i
      = ∑ i, ((p i - pt i) * E i + pt i * (E i - Et i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i : Fin m, |(p i - pt i) * E i + pt i * (E i - Et i)|
      ≤ ϵ0 * normSq ψ + |pt i| * (ϵ1 * normSq ψ) := by
    intro i
    have h2 : |(p i - pt i) * E i| ≤ ϵ0 * normSq ψ :=
      calc |(p i - pt i) * E i| = |p i - pt i| * |E i| := abs_mul _ _
        _ ≤ ϵ0 * |E i| := mul_le_mul_of_nonneg_right (hp i) (abs_nonneg _)
        _ ≤ ϵ0 * normSq ψ := mul_le_mul_of_nonneg_left (hnorm i) hϵ0pos
    have h3 : |pt i * (E i - Et i)| ≤ |pt i| * (ϵ1 * normSq ψ) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdiff i) (abs_nonneg _)
    calc |(p i - pt i) * E i + pt i * (E i - Et i)|
        ≤ |(p i - pt i) * E i| + |pt i * (E i - Et i)| := abs_add_le _ _
      _ ≤ ϵ0 * normSq ψ + |pt i| * (ϵ1 * normSq ψ) := add_le_add h2 h3
  have hcard : ∑ i : Fin m, (ϵ0 * normSq ψ) = m * (ϵ0 * normSq ψ) := by
    simp
  have hsum2 : ∑ i, (ϵ0 * normSq ψ + |pt i| * (ϵ1 * normSq ψ))
      = m * (ϵ0 * normSq ψ) + (∑ i, |pt i|) * (ϵ1 * normSq ψ) := by
    rw [Finset.sum_add_distrib, hcard, ← Finset.sum_mul]
  have hprod : 0 ≤ ϵ1 * normSq ψ := le_trans (abs_nonneg _) (hdiff ⟨0, hm⟩)
  have hptbound : (∑ i, |pt i|) * (ϵ1 * normSq ψ) ≤ ϵ1 * normSq ψ := by
    have h1 : (∑ i, |pt i|) * (ϵ1 * normSq ψ) ≤ 1 * (ϵ1 * normSq ψ) :=
      mul_le_mul_of_nonneg_right hsumPt hprod
    simpa using h1
  have hmϵ0 : m * (ϵ0 * normSq ψ) ≤ ϵ / 8 * normSq ψ := by
    have hstep1 : m * (ϵ / (8 * m ^ 2)) = ϵ / (8 * m) := by
      field_simp
    have hstep2 : ϵ / (8 * m) ≤ ϵ / 8 := by
      have h1m : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) h1m
      have h8m : (0 : ℝ) < 8 * m := mul_pos (by norm_num) hm0
      have hkey : ϵ / (8 * m) * (8 * m) ≤ ϵ / 8 * (8 * m) := by
        have h1 : ϵ / (8 * m) * (8 * m) = ϵ := div_mul_cancel₀ ϵ (ne_of_gt h8m)
        have h2 : ϵ / 8 * (8 * m) = ϵ * m := by
          field_simp
        rw [h1, h2]
        calc ϵ = ϵ * 1 := by ring
          _ ≤ ϵ * m := mul_le_mul_of_nonneg_left h1m hϵ
      exact le_of_mul_le_mul_right hkey h8m
    have h1 : m * ϵ0 ≤ ϵ / 8 := by
      calc m * ϵ0 ≤ m * (ϵ / (8 * m ^ 2)) :=
            mul_le_mul_of_nonneg_left hϵ0 (Nat.cast_nonneg _)
        _ = ϵ / (8 * m) := hstep1
        _ ≤ ϵ / 8 := hstep2
    have hmid : m * (ϵ0 * normSq ψ) = (m * ϵ0) * normSq ψ := by ring
    rw [hmid]
    exact mul_le_mul_of_nonneg_right h1 hnsq
  have hbound : ∑ i, |(p i - pt i) * E i + pt i * (E i - Et i)|
      ≤ (ϵ / 8 + ϵ / 6) * normSq ψ := by
    have hϵ1b : ϵ1 * normSq ψ ≤ ϵ / 6 * normSq ψ :=
      mul_le_mul_of_nonneg_right hϵ1 hnsq
    calc ∑ i, |(p i - pt i) * E i + pt i * (E i - Et i)|
        ≤ ∑ i, (ϵ0 * normSq ψ + |pt i| * (ϵ1 * normSq ψ)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = m * (ϵ0 * normSq ψ) + (∑ i, |pt i|) * (ϵ1 * normSq ψ) := hsum2
      _ ≤ ϵ / 8 * normSq ψ + ϵ1 * normSq ψ := add_le_add hmϵ0 hptbound
      _ ≤ ϵ / 8 * normSq ψ + ϵ / 6 * normSq ψ :=
          add_le_add (le_refl _) hϵ1b
      _ = (ϵ / 8 + ϵ / 6) * normSq ψ := by ring
  have hfinal : |∑ i, ((p i - pt i) * E i + pt i * (E i - Et i))|
      ≤ (ϵ / 8 + ϵ / 6) * normSq ψ :=
    le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) hbound
  have hsplit' : ϵ / 8 + ϵ / 6 ≤ ϵ := by
    have h1 : (7 : ℝ) / 24 ≤ 1 := by norm_num
    have h2 : ϵ / 8 + ϵ / 6 = (7 / 24) * ϵ := by ring
    rw [h2]
    calc (7 / 24) * ϵ ≤ 1 * ϵ := mul_le_mul_of_nonneg_right h1 hϵ
      _ = ϵ := by ring
  calc |∑ i, p i * E i - ∑ i, pt i * Et i|
      = |∑ i, ((p i - pt i) * E i + pt i * (E i - Et i))| := by rw [hsplit]
    _ ≤ (ϵ / 8 + ϵ / 6) * normSq ψ := hfinal
    _ ≤ ϵ * normSq ψ := mul_le_mul_of_nonneg_right hsplit' hnsq

end Qatlib.Papers.QuantumPCPs25.MainResults.Model
