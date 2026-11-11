/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-level model for QuantumPCPs25

Source: Buhrman--Helsen--Weggemans, *Quantum PCPs: on Adaptivity, Multiple
Provers and Reductions to Local Hamiltonians*, arXiv:2403.04841v3 (Quantum 9,
1791 (2025)).  Fixed version: arXiv:2403.04841v3 (2025-07-08).

This file fixes the semantic vocabulary used by the paper-layer statements:

* `PromiseProblem`               -- promise problem (Definition 2/3/5 setup);
* `QuantumVerifier`              -- semantic core of a QPCP/QMA verifier
                                    (Definition 4 with the acceptance
                                    distribution of Definition 5);
* `InQPCP`, `InQPCPNA`, `InQMA`,
  `InQCMA`, `InNP`                -- the complexity classes of Section 2.2 and
                                    Definitions 5/5a;
* `LocalHamiltonianInstance`,
  `QLHProblem`, `KLHProblem`      -- the (k-separable) q-local Hamiltonian
                                    problem (Definition 3);
* `CLDMInstance`, `CLDMProblem`   -- the local density matrix consistency
                                    problem of Section 5;
* relativised verifier vocabulary for the oracle separations of Section 6.

Modelling note.  The paper defines a verifier by an explicit P-uniform family of
polynomial-size quantum circuits with `q` adaptive proof queries (Definition 4).
Here a verifier is represented by its *semantics*: for every input `x` and every
joint quantum witness tuple it returns the acceptance probability
`acceptProb x ξ ∈ [0,1]`.  The fields `numProvers`, `numQueries`,
`nonAdaptive`, `efficient` and `DependsOnAtMostQueries` record the structural
data that the class definitions quantify over.  `efficient : Prop` is the
opaque P-uniform poly-time condition; it is a field so that every existential
class witness must carry it.  This keeps the statements faithful to the paper's
definitions without rebuilding the full circuit model, which lives in the
shared `Foundations`/`Concepts` layers.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults.Model

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath

/-- Bit strings of length `n`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- A promise problem: disjoint yes/no instance sets (paper: Definition 2). -/
structure PromiseProblem (α : Type*) where
  /-- Yes instances. -/
  yes : α → Prop
  /-- No instances. -/
  no : α → Prop
  /-- Promise hardness: the sets are disjoint. -/
  disjoint : ∀ x, ¬ (yes x ∧ no x)

/-- The computational-basis state `|i⟩` of a `d`-dimensional register. -/
def basisState (d : ℕ) (i : Fin d) : Fin d → ℂ := fun j => if j = i then 1 else 0

/-- Semantic core of a quantum PCP / QMA verifier (paper: Definition 4, with
the acceptance probabilities of Definition 5).  `acceptProb x ξ` is the
probability that the verifier accepts input `x` on the joint proof tuple `ξ`
(one state per prover). -/
structure QuantumVerifier (α : Type*) where
  /-- Number of (unentangled) provers. -/
  numProvers : ℕ
  /-- Number of proof qubits queried. -/
  numQueries : ℕ
  /-- Whether the verifier is non-adaptive (Definition 4a). -/
  nonAdaptive : Bool
  /-- The P-uniform polynomial-time condition (opaque here). -/
  efficient : Prop
  /-- Dimension of each prover's proof register as a function of the input. -/
  proofDim : α → ℕ
  /-- Acceptance probability on input `x` and joint proof tuple `ξ`. -/
  acceptProb : (x : α) → (Fin numProvers → Fin (proofDim x) → ℂ) → ℝ
  /-- Acceptance probabilities are nonnegative. -/
  acceptProb_nonneg : ∀ x ξ, 0 ≤ acceptProb x ξ
  /-- Acceptance probabilities are at most one. -/
  acceptProb_le_one : ∀ x ξ, acceptProb x ξ ≤ 1

/-- A verifier depends on at most `q` proof coordinates: there is a set of at
most `q` `(prover, qubit)` coordinates that determines its acceptance
probability.  This is the semantic content of the `q`-query restriction of
Definition 4. -/
def DependsOnAtMostQueries {α : Type*} (q : ℕ) (V : QuantumVerifier α) : Prop :=
  ∃ S : α → Finset (ℕ × ℕ),
    (∀ x, (S x).card ≤ q) ∧
    ∀ (x : α) (ξ η : Fin V.numProvers → Fin (V.proofDim x) → ℂ),
      (∀ (i : Fin V.numProvers) (j : Fin (V.proofDim x)),
        (i.val, j.val) ∈ S x → ξ i j = η i j) →
      V.acceptProb x ξ = V.acceptProb x η

/-- `A ∈ QPCP[k, q, c, s]` (paper: Definition 5).  The acceptance thresholds
`c` and `s` may depend on the instance (so that `1 - 2^{-Ω(n)}` type bounds are
representable), which is exactly the paper's convention since `n = |x|`. -/
def InQPCP {α : Type*} (k q : ℕ) (c s : α → ℝ) (A : PromiseProblem α) : Prop :=
  ∃ V : QuantumVerifier α,
    V.numProvers = k ∧ V.numQueries ≤ q ∧ V.efficient ∧
    DependsOnAtMostQueries q V ∧
    (∀ x, A.yes x → ∃ ξ, c x ≤ V.acceptProb x ξ) ∧
    (∀ x, A.no x → ∀ ξ, V.acceptProb x ξ ≤ s x)

/-- `A ∈ QPCPNA[k, q, c, s]` (paper: Definition 5a, non-adaptive verifiers). -/
def InQPCPNA {α : Type*} (k q : ℕ) (c s : α → ℝ) (A : PromiseProblem α) : Prop :=
  ∃ V : QuantumVerifier α,
    V.numProvers = k ∧ V.numQueries ≤ q ∧ V.nonAdaptive = true ∧ V.efficient ∧
    DependsOnAtMostQueries q V ∧
    (∀ x, A.yes x → ∃ ξ, c x ≤ V.acceptProb x ξ) ∧
    (∀ x, A.no x → ∀ ξ, V.acceptProb x ξ ≤ s x)

/-- `A ∈ QMA[k, c, s]` (paper: Definition 2). -/
def InQMA {α : Type*} (k : ℕ) (c s : α → ℝ) (A : PromiseProblem α) : Prop :=
  ∃ V : QuantumVerifier α,
    V.numProvers = k ∧ V.efficient ∧
    (∀ x, A.yes x → ∃ ξ, c x ≤ V.acceptProb x ξ) ∧
    (∀ x, A.no x → ∀ ξ, V.acceptProb x ξ ≤ s x)

/-- `A ∈ QCMA[k, c, s]` (paper: Definition 2a): the witness is a tuple of
computational-basis states. -/
def InQCMA {α : Type*} (k : ℕ) (c s : α → ℝ) (A : PromiseProblem α) : Prop :=
  ∃ V : QuantumVerifier α,
    V.numProvers = k ∧ V.efficient ∧
    (∀ x, A.yes x → ∃ w : Fin V.numProvers → Fin (V.proofDim x),
      c x ≤ V.acceptProb x (fun j => basisState (V.proofDim x) (w j))) ∧
    (∀ x, A.no x → ∀ w : Fin V.numProvers → Fin (V.proofDim x),
      V.acceptProb x (fun j => basisState (V.proofDim x) (w j)) ≤ s x)

/-- `A ∈ NP`: a classical witness predicate (paper: the classical class used
in Corollary 4). -/
def InNP {α : Type*} (A : PromiseProblem α) : Prop :=
  ∃ (W : α → Type) (_ : ∀ x, Nonempty (W x)) (decide : (x : α) → W x → Bool),
    (∀ x, A.yes x → ∃ w, decide x w = true) ∧
    (∀ x, A.no x → ∀ w, decide x w = false)

/-- `InNP` without the nonemptiness side condition (kept for statement reuse). -/
def InNP' {α : Type*} (A : PromiseProblem α) : Prop :=
  ∃ W : α → Type, ∃ decide : (x : α) → W x → Bool,
    (∀ x, A.yes x → ∃ w, decide x w = true) ∧
    (∀ x, A.no x → ∀ w, decide x w = false)

/-- The unqualified class `QPCP[k, q]` (paper: `c = 2/3`, `s = 1/3`). -/
def QPCP {α : Type*} (k q : ℕ) (A : PromiseProblem α) : Prop :=
  InQPCP k q (fun _ => 2 / 3) (fun _ => 1 / 3) A

/-- The unqualified class `QPCPNA[k, q]`. -/
def QPCPNA {α : Type*} (k q : ℕ) (A : PromiseProblem α) : Prop :=
  InQPCPNA k q (fun _ => 2 / 3) (fun _ => 1 / 3) A

/-- The unqualified class `QMA[k]` (paper: `c = 2/3`, `s = 1/3`). -/
def QMA {α : Type*} (k : ℕ) (A : PromiseProblem α) : Prop :=
  InQMA k (fun _ => 2 / 3) (fun _ => 1 / 3) A

/-- The unqualified class `QCMA` (paper: Definition 2a). -/
def QCMA {α : Type*} (A : PromiseProblem α) : Prop :=
  InQCMA 1 (fun _ => 2 / 3) (fun _ => 1 / 3) A

/-- `QMA[2]` as used in Theorem 5. -/
def QMA2 {α : Type*} (A : PromiseProblem α) : Prop := QMA 2 A

/-! ## The (k-separable) local Hamiltonian problem -/

/-- A q-local Hamiltonian instance (paper: Definition 3): a weighted sum of
`q`-local PSD terms with operator norm at most one, an energy functional on
`n`-qubit density matrices, and promise thresholds `a < b` with gap `δ`. -/
structure QLHInstance (q : ℕ) (δ : ℝ) where
  /-- Number of qubits. -/
  n : ℕ
  /-- Number of local terms. -/
  m : ℕ
  /-- Weights of the local terms. -/
  weight : Fin m → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : (∑ i, weight i) = 1
  /-- The local (q-qubit) PSD terms. -/
  term : Fin m → Operator (2 ^ q)
  term_psd : ∀ i, (term i).PosSemidef
  term_norm_le_one : ∀ i, OperatorSpectralNorm (term i) ≤ 1
  /-- Energy expectation functional of the assembled `n`-qubit Hamiltonian. -/
  energy : Operator (2 ^ n) → ℝ
  a : ℝ
  b : ℝ
  hδ : 0 < δ
  gap : b - a = δ

/-- The promise gap of a q-local Hamiltonian instance is constant in `n`. -/
def HasConstantGap {q : ℕ} {δ : ℝ} (_I : QLHInstance q δ) : Prop := ∃ c : ℝ, 0 < c ∧ c ≤ δ

/-- The `q`-local Hamiltonian problem `q-LH[δ]` (paper: Definition 3 with
`k = 1`).  Yes instances have energy at most `a`; no instances have energy at
least `b`. -/
def QLHProblem (q : ℕ) (δ : ℝ) : PromiseProblem (QLHInstance q δ) where
  yes I := ∃ ρ : Operator (2 ^ I.n), IsDensityOperator ρ ∧ I.energy ρ ≤ I.a
  no I := ∀ ρ : Operator (2 ^ I.n), IsDensityOperator ρ → I.b ≤ I.energy ρ
  disjoint := by
    rintro I ⟨⟨ρ, hρ, hle⟩, hall⟩
    have hge := hall ρ hρ
    have : I.b ≤ I.a := le_trans hge hle
    linarith [I.gap, I.hδ]

/-- A k-separable q-local Hamiltonian instance: product-state energies. -/
structure KLHInstance (k q : ℕ) (δ : ℝ) where
  n : ℕ
  m : ℕ
  weight : Fin m → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : (∑ i, weight i) = 1
  term : Fin m → Operator (2 ^ q)
  term_psd : ∀ i, (term i).PosSemidef
  term_norm_le_one : ∀ i, OperatorSpectralNorm (term i) ≤ 1
  /-- Energy on a `k`-fold tensor product of `n`-qubit states. -/
  energyProd : (Fin k → Operator (2 ^ n)) → ℝ
  a : ℝ
  b : ℝ
  hδ : 0 < δ
  gap : b - a = δ

/-- The k-separable q-local Hamiltonian problem `LH(k, q, δ)`. -/
def KLHProblem (k q : ℕ) (δ : ℝ) : PromiseProblem (KLHInstance k q δ) where
  yes I := ∃ ρ : Fin k → Operator (2 ^ I.n),
    (∀ j, IsDensityOperator (ρ j)) ∧ I.energyProd ρ ≤ I.a
  no I := ∀ ρ : Fin k → Operator (2 ^ I.n),
    (∀ j, IsDensityOperator (ρ j)) → I.b ≤ I.energyProd ρ
  disjoint := by
    rintro I ⟨⟨ρ, hprod, hle⟩, hall⟩
    have hge := hall ρ hprod
    have : I.b ≤ I.a := le_trans hge hle
    linarith [I.gap, I.hδ]

/-! ## The local density matrix consistency problem (Section 5) -/

/-- A CLDM instance (paper: Section 5): target `q`-qubit marginals, a map from
global `n`-qubit states to their induced marginals, and thresholds
`α < β` in trace distance. -/
structure CLDMInstance (q : ℕ) where
  n : ℕ
  m : ℕ
  marginal : Fin m → Operator (2 ^ q)
  reduced : Operator (2 ^ n) → Fin m → Operator (2 ^ q)
  alpha : ℝ
  beta : ℝ
  beta_pos : 0 < beta
  gap : alpha < beta

/-- The trace distance `‖A - B‖₁` (paper: `‖ρ̃ - ρ‖₁` in Lemma 11). -/
def traceDistance {D : ℕ} (A B : Operator D) : ℝ := SchattenOne (A - B)

/-- The local density matrix consistency problem `CLDM(q, α, β)`: yes if some
global state has exactly the prescribed marginals; no if every global state has
some marginal at trace distance at least `β`. -/
def CLDMProblem (q : ℕ) : PromiseProblem (CLDMInstance q) where
  yes I := ∃ ρ : Operator (2 ^ I.n), IsDensityOperator ρ ∧
    ∀ i, I.reduced ρ i = I.marginal i
  no I := ∀ ρ : Operator (2 ^ I.n), IsDensityOperator ρ →
    ∃ i, I.beta ≤ traceDistance (I.reduced ρ i) (I.marginal i)
  disjoint := by
    rintro I ⟨⟨ρ, hρ, hex⟩, hall⟩
    obtain ⟨i, hi⟩ := hall ρ hρ
    have hzero : I.reduced ρ i - I.marginal i = 0 := by rw [hex i, sub_self]
    have h0 : traceDistance (I.reduced ρ i) (I.marginal i) = 0 := by
      unfold traceDistance
      rw [hzero]
      simp [SchattenOne]
    linarith [I.beta_pos]

/-! ## Relativised vocabulary for the oracle separations (Section 6) -/

/-- A classical/quantum oracle is a Boolean function on addresses. -/
abbrev Oracle := ℕ → Bool

/-- A verifier with oracle access (paper: Section 6). -/
structure OracleVerifier (O : Oracle) (α : Type*) where
  numProvers : ℕ
  numQueries : ℕ
  oracleQueries : ℕ
  nonAdaptive : Bool
  efficient : Prop
  proofDim : α → ℕ
  acceptProb : (x : α) → (Fin numProvers → Fin (proofDim x) → ℂ) → ℝ
  acceptProb_nonneg : ∀ x ξ, 0 ≤ acceptProb x ξ
  acceptProb_le_one : ∀ x ξ, acceptProb x ξ ≤ 1

/-- Oracle-relative QPCP membership. -/
def InQPCPr (O : Oracle) (k q : ℕ) (c s : List Bool → ℝ) (A : PromiseProblem (List Bool)) : Prop :=
  ∃ V : OracleVerifier O (List Bool),
    V.numProvers = k ∧ V.numQueries ≤ q ∧ V.efficient ∧
    (∀ x, A.yes x → ∃ ξ, c x ≤ V.acceptProb x ξ) ∧
    (∀ x, A.no x → ∀ ξ, V.acceptProb x ξ ≤ s x)

/-- Oracle-relative QMA membership. -/
def InQMAr (O : Oracle) (k : ℕ) (c s : List Bool → ℝ) (A : PromiseProblem (List Bool)) : Prop :=
  ∃ V : OracleVerifier O (List Bool),
    V.numProvers = k ∧ V.efficient ∧
    (∀ x, A.yes x → ∃ ξ, c x ≤ V.acceptProb x ξ) ∧
    (∀ x, A.no x → ∀ ξ, V.acceptProb x ξ ≤ s x)

/-- Oracle-relative QCMA membership. -/
def InQCMAr (O : Oracle) (c s : List Bool → ℝ) (A : PromiseProblem (List Bool)) : Prop :=
  ∃ V : OracleVerifier O (List Bool),
    V.numProvers = 1 ∧ V.efficient ∧
    (∀ x, A.yes x → ∃ w : Fin (V.proofDim x),
      c x ≤ V.acceptProb x (fun _ => basisState (V.proofDim x) w)) ∧
    (∀ x, A.no x → ∀ w : Fin (V.proofDim x),
      V.acceptProb x (fun _ => basisState (V.proofDim x) w) ≤ s x)

/-- Unqualified oracle-relative classes (thresholds `2/3`, `1/3`). -/
def QMAr (O : Oracle) (A : PromiseProblem (List Bool)) : Prop :=
  InQMAr O 1 (fun _ => 2 / 3) (fun _ => 1 / 3) A
def QCMAr (O : Oracle) (A : PromiseProblem (List Bool)) : Prop :=
  InQCMAr O (fun _ => 2 / 3) (fun _ => 1 / 3) A
def QPCPr (O : Oracle) (k q : ℕ) (A : PromiseProblem (List Bool)) : Prop :=
  InQPCPr O k q (fun _ => 2 / 3) (fun _ => 1 / 3) A
def NPr (O : Oracle) (A : PromiseProblem (List Bool)) : Prop :=
  ∃ V : OracleVerifier O (List Bool), V.efficient ∧
    (∀ x, A.yes x → ∃ w : Fin (V.proofDim x),
      (2 / 3 : ℝ) ≤ V.acceptProb x (fun _ => basisState (V.proofDim x) w)) ∧
    (∀ x, A.no x → ∀ w : Fin (V.proofDim x),
      V.acceptProb x (fun _ => basisState (V.proofDim x) w) ≤ 1 / 3)

/-! ## Analytic vocabulary shared by the paper-layer statements -/

/-- Expectation value `⟨ψ| H |ψ⟩` of an operator in the pure state `ψ`
(paper: `⟨ψ| H |ψ⟩`, Lemma 9, p. 25). -/
noncomputable def pureExpect {D : ℕ} (H : Operator D) (ψ : Fin D → ℂ) : ℝ :=
  (∑ i, ∑ j, star (ψ i) * H i j * ψ j).re

/-- The ground-state energy `λ_min(H) = inf_ρ tr[Hρ]` over density operators
(paper: `λ_min`, Lemma 8, p. 23). -/
noncomputable def groundEnergy {D : ℕ} (H : Operator D) : ℝ :=
  ⨅ (ρ : {ρ : Operator D // IsDensityOperator ρ}), (Matrix.trace (H * ρ.1)).re

/-- `l`-fold tensor power of an operator, on `l` registers of dimension `d`
(paper: `ρ^{⊗l}`, Lemma 11, p. 33). -/
noncomputable def tensorPow {d : ℕ} (l : ℕ) (M : Operator d) :
    Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ :=
  fun a b => ∏ i, M (a i) (b i)

/-- Probability of a measurement outcome with POVM element `P` on state `ρ`,
namely `tr[Pρ]` (paper: `tr{M_k ρ}`, Section 5.4.3, p. 33). -/
noncomputable def outcomeProb {D : ℕ} (P ρ : Operator D) : ℝ :=
  (Matrix.trace (P * ρ)).re

/-- `H` is a sum of weighted local PSD terms, each with a support certificate of
at most `q` register indices and operator norm at most one (paper: "`H_x`
consisting of `q`-local PSD terms", Lemma 5, p. 17). -/
def IsQLocalPSDHamiltonian {D : ℕ} (q : ℕ) (H : Operator D) : Prop :=
  ∃ (m : ℕ) (weight : Fin m → ℝ) (term : Fin m → Operator D) (support : Fin m → Finset ℕ),
    (∀ i, 0 ≤ weight i) ∧
    (∀ i, (term i).PosSemidef) ∧
    (∀ i, OperatorSpectralNorm (term i) ≤ 1) ∧
    (∀ i, (support i).card ≤ q) ∧
    H = ∑ i, weight i • term i

/-- Probability `tr[Pρ]` for a POVM element `P` and state `ρ` on an arbitrary
finite index type (used for tensor-power registers in Lemma 11). -/
noncomputable def traceProb {m : Type*} [Fintype m] [DecidableEq m]
    (P ρ : Matrix m m ℂ) : ℝ :=
  (Matrix.trace (P * ρ)).re

/-- A polynomial-time (Karp) reduction between promise problems: a map sending
yes instances to yes instances and no instances to no instances (paper:
"quantum reductions", Corollary 3, p. 28). -/
def PolyReduction {α β : Type*} (A : PromiseProblem α) (B : PromiseProblem β) : Prop :=
  ∃ f : α → β, (∀ x, A.yes x → B.yes (f x)) ∧ (∀ x, A.no x → B.no (f x))

/-! ## Basic containment facts -/

/-- Every QPCP verifier is a QMA verifier with the same acceptance behaviour,
so `QPCP[k,q,c,s] ⊆ QMA[k,c,s]` (nothing about the witness changes). -/
theorem inQPCP_inQMA {α : Type*} (k q : ℕ) (c s : α → ℝ) (A : PromiseProblem α) :
    InQPCP k q c s A → InQMA k c s A := by
  rintro ⟨V, hk, -, heff, -, hyes, hno⟩
  exact ⟨V, hk, heff, hyes, hno⟩

/-- Every non-adaptive QPCP verifier is in particular a QPCP verifier. -/
theorem inQPCPNA_inQPCP {α : Type*} (k q : ℕ) (c s : α → ℝ) (A : PromiseProblem α) :
    InQPCPNA k q c s A → InQPCP k q c s A := by
  rintro ⟨V, hk, hq, -, heff, hdep, hyes, hno⟩
  exact ⟨V, hk, hq, heff, hdep, hyes, hno⟩

end Qatlib.Papers.QuantumPCPs25.MainResults.Model
