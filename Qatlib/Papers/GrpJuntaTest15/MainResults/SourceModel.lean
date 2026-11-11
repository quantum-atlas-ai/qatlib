/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared paper model for GrpJuntaTest15

Ambainis--Belovs--Regev--de Wolf, *Efficient Quantum Algorithms for (Gapped) Group
Testing and Junta Testing*, arXiv:1507.03126v1 (11 Jul 2015).  Fixed version: v1;
PDF `prove/assets/1507.03126.pdf`.

This module fixes the paper-level vocabulary used by every claim file:

* Boolean functions on a finite input set, Hamming distance `dist`, `k`-juntas,
  `ε`-farness, Walsh--Fourier coefficients and the influence `infSet` of Eq. (6);
* the family form of the (E)GGT problems of Definitions 3.1--3.2;
* deterministic decision trees, randomized distributions over them (the paper's
  randomized query model), and the "fresh variables" lists of Lemma 3.6;
* the concrete bounded-error quantum query model of the shared library
  (`Circuit`, `Run`, `IsPovm`, `povmProb` from
  `QuantumAlgorithm.Foundations.ReferenceError.MixturePaths` and
  `QuantumAlgorithm.Concepts.AdversaryBounds.AdvDuality`), specialized to a
  bit phase oracle and to the QGGT block oracle of Definition 5.1;
* the adversary-bound SDP feasibility/objective vocabulary of Eq. (3), and the
  irrelevant-variable composition of Definitions 2.8--2.10.

Definitions only: no claim is asserted here.  Algorithmic bounds are stated
over these concrete models in the claim files; where a proof is not completed,
the claim file records the exact source theorem, the paper's proof route, the
current Lean gap and candidate dependencies.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality

/-! ## Boolean functions, distance, junta-ness, influence -/

/-- Boolean functions on a finite input set `α`.  The paper's setting is
`α = Fin n`. -/
abbrev BoolFun (α : Type*) := (α → Bool) → Bool

/-- Hamming distance: the number of inputs on which `f` and `g` differ. -/
def hammingDist {α : Type*} [Fintype α] [DecidableEq α]
    (f g : BoolFun α) : ℕ :=
  Fintype.card {x : α → Bool // f x ≠ g x}

/-- Normalized Hamming distance `|f ⊕ g| / 2^{|α|}` (paper's relative distance). -/
def dist {α : Type*} [Fintype α] [DecidableEq α]
    (f g : BoolFun α) : ℝ :=
  (hammingDist f g : ℝ) / (Fintype.card (α → Bool) : ℝ)

/-- `f` is a `k`-junta: it depends only on a set `W` of at most `k` variables. -/
def IsKJunta {α : Type*} [Fintype α] [DecidableEq α]
    (k : ℕ) (f : BoolFun α) : Prop :=
  ∃ W : Finset α, W.card ≤ k ∧ ∀ x y, (∀ i ∈ W, x i = y i) → f x = f y

/-- `f` is `ε`-far from every `k`-junta (Definition in Section 4). -/
def epsFarFromKJunta {α : Type*} [Fintype α] [DecidableEq α]
    (ε : ℝ) (k : ℕ) (f : BoolFun α) : Prop :=
  ∀ g, IsKJunta k g → ε ≤ dist f g

/-- `±1` embedding of a Boolean function. -/
def pm {α : Type*} (f : BoolFun α) (x : α → Bool) : ℝ :=
  if f x then 1 else -1

/-- The character `χ_T(x) = (-1)^{Σ_{i∈T} x_i}` of Eq. (6). -/
def char {α : Type*} [DecidableEq α] (T : Finset α) (x : α → Bool) : ℝ :=
  (-1 : ℝ) ^ (T.filter (fun i => x i)).card

/-- Fourier coefficient `f̂(T) = 2^{-|α|} Σ_x f(x) χ_T(x)`. -/
def fourierCoeff {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFun α) (T : Finset α) : ℝ :=
  (1 / (Fintype.card (α → Bool) : ℝ)) *
    ∑ x : α → Bool, pm f x * char T x

/-- Influence of a variable set `S` on `f`, Eq. (6):
`Inf_S(f) = Σ_{T : T ∩ S ≠ ∅} f̂(T)^2`. -/
def infSet {α : Type*} [Fintype α] [DecidableEq α]
    (f : BoolFun α) (S : Finset α) : ℝ :=
  ∑ T : Finset α, if (T ∩ S).Nonempty then (fourierCoeff f T) ^ 2 else 0

/-- Flip exactly the coordinates in `S`. -/
def flipOn {α : Type*} [DecidableEq α] (S : Finset α) (x : α → Bool) : α → Bool :=
  fun i => if i ∈ S then !x i else x i

/-! ## Group-testing promise problems (Definitions 3.1--3.2) -/

/-- A family over `2^[n]`, i.e. a Boolean function on subsets of `[n]`. -/
abbrev Family (n : ℕ) := Finset (Fin n) → Bool

/-- `Intersects_A(S) = 1` iff `S ∩ A ≠ ∅` (Eq. (7)). -/
def Intersects {n : ℕ} (A : Finset (Fin n)) : Family n :=
  fun S => decide (S ∩ A).Nonempty

/-- The "small" family `X̃` of Definition 3.2 (false negatives allowed). -/
def GGTLeft (n k : ℕ) : Set (Family n) :=
  {f | ∃ A : Finset (Fin n), A.card = k ∧ ∀ S, S ∩ A = ∅ → f S = false}

/-- The "large" family `Ỹ` of Definition 3.2 (false positives allowed). -/
def GGTRight (n k d : ℕ) : Set (Family n) :=
  {f | ∃ B : Finset (Fin n), B.card = k + d ∧ ∀ S, (S ∩ B).Nonempty → f S = true}

/-- Exact gap group testing `X` of Definition 3.1. -/
def EGGTLeft (n k : ℕ) : Set (Family n) :=
  {f | ∃ A : Finset (Fin n), A.card = k ∧ f = Intersects A}

/-- Exact gap group testing `Y` of Definition 3.1. -/
def EGGTRight (n k d : ℕ) : Set (Family n) :=
  {f | ∃ B : Finset (Fin n), B.card = k + d ∧ f = Intersects B}

/-! ## Deterministic and randomized decision trees -/

/-- A deterministic decision tree of depth `q` over subset queries.  `query S next`
queries `S` and branches on the oracle answer. -/
inductive DetTree (n : ℕ) : ℕ → Type where
  | leaf (b : Bool) : DetTree n 0
  | query {q : ℕ} (S : Finset (Fin n)) (next : Bool → DetTree n q) : DetTree n (q + 1)

/-- Evaluation of a decision tree against a family. -/
def DetTree.eval {n : ℕ} : {q : ℕ} → DetTree n q → Family n → Bool
  | 0, .leaf b, _ => b
  | _ + 1, .query S next, f => DetTree.eval (next (f S)) f

/-- The list of fresh-variable sets of all vertices of a decision tree
(Lemma 3.6: `F_V = S_V \ ⋃_{ancestors} S_i`, with the root's ancestors empty). -/
def DetTree.freshAux {n q : ℕ} : DetTree n q → Finset (Fin n) → List (Finset (Fin n))
  | .leaf _, _ => []
  | .query S next, acc =>
      (S \ acc) ::
        (DetTree.freshAux (next true) (acc ∪ S) ++
         DetTree.freshAux (next false) (acc ∪ S))

/-- Fresh-variable sets of all vertices of the tree. -/
def DetTree.freshSets {n q : ℕ} (t : DetTree n q) : List (Finset (Fin n)) :=
  t.freshAux ∅

/-- A finitary randomized decision tree with `q` queries: a finite weighted list of
deterministic depth-`q` trees (the paper's randomized query model). -/
structure RandAlg (n q : ℕ) where
  size : ℕ
  tree : Fin size → DetTree n q
  weight : Fin size → ℚ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1

/-- Probability that a randomized tree outputs `b` on `f`. -/
def RandAlg.successProb {n q : ℕ} (alg : RandAlg n q) (f : Family n) (b : Bool) : ℚ :=
  ∑ i : Fin alg.size, if DetTree.eval (alg.tree i) f = b then alg.weight i else 0

/-- `RandSolves n k d q`: some `q`-query randomized decision tree decides the GGT
promise `X̃_k ∪ Ỹ_{k,d}` with error at most `1/3` (both sides). -/
def RandSolves (n k d q : ℕ) : Prop :=
  ∃ alg : RandAlg n q,
    (∀ f ∈ GGTLeft n k, (2 / 3 : ℚ) ≤ alg.successProb f false) ∧
    (∀ f ∈ GGTRight n k d, (2 / 3 : ℚ) ≤ alg.successProb f true)

/-- `RandSolvesEGGT n k d q`: the same promise for the exact variant `X ∪ Y`. -/
def RandSolvesEGGT (n k d q : ℕ) : Prop :=
  ∃ alg : RandAlg n q,
    (∀ f ∈ EGGTLeft n k, (2 / 3 : ℚ) ≤ alg.successProb f false) ∧
    (∀ f ∈ EGGTRight n k d, (2 / 3 : ℚ) ≤ alg.successProb f true)

/-- Average of a real functional over all `k`-subsets (0 when there are none). -/
def subsetAvg (n k : ℕ) (p : Finset (Fin n) → ℝ) : ℝ :=
  if (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k)).card = 0 then 0
  else
    (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k)).sum p /
      ((Finset.univ.filter (fun A : Finset (Fin n) => A.card = k)).card : ℝ)

/-- Disagreement probability of two decision trees on `A ~ D`, where `D` is the
uniform mixture of the uniform distributions on `k`- and `(k+d)`-subsets
(the distribution of the proof of Theorem 3.5).  The trees are evaluated on the
oracle family `Intersects_A`. -/
def disagreeProb (n k d : ℕ) {q q' : ℕ} (t : DetTree n q) (t' : DetTree n q') : ℝ :=
  (1 / 2) * subsetAvg n k
      (fun A => if DetTree.eval t (Intersects A) = DetTree.eval t' (Intersects A)
        then 0 else 1) +
    (1 / 2) * subsetAvg n (k + d)
      (fun A => if DetTree.eval t (Intersects A) = DetTree.eval t' (Intersects A)
        then 0 else 1)

/-! ## Concrete bounded-error quantum query model -/

/-- Bit phase oracle on a query register `ι` and workspace `W`: it multiplies the
amplitude of `(i, w)` by `(-1)^{bits i}` and is diagonal in the computational
basis.  This is the standard phase-query model used throughout the paper. -/
def bitOracle {ι W : Type} [Fintype ι] [DecidableEq ι] [DecidableEq W]
    (bits : ι → Bool) : Matrix (ι × W) (ι × W) ℂ :=
  diagonal (fun p => if bits p.1 then (-1 : ℂ) else 1)

/-- Block-diagonal oracle on the input register `ι` assembled from a family of
workspace unitaries `O S` (Definition 5.1: `O_f = ⊕_S O_{f,S}`). -/
def blockOracle {ι W : Type} [DecidableEq ι]
    (O : ι → Matrix W W ℂ) : Matrix (ι × W) (ι × W) ℂ :=
  of fun p q => if p.1 = q.1 then O p.1 p.2 q.2 else 0

/-- `QuantumDecides input P yes q s`: there is a bounded-error quantum query
algorithm (at most `q` queries, at most `s` circuit steps) that, on every input
of the promise set `P`, outputs `yes x` with probability at least `2/3`.
The algorithm is a concrete `Circuit` over the phase-oracle space `ι × W`. -/
def QuantumDecides {X ι : Type} [Fintype ι] [DecidableEq ι]
    (input : X → ι → Bool) (P : Set X) (yes : X → Bool) (q s : ℕ) : Prop :=
  ∃ (W : Type) (iW : Fintype W) (dW : DecidableEq W),
    letI := iW
    letI := dW
    ∃ (C : Circuit (ι × W)) (psi : QState (ι × W))
      (out : Bool → Matrix (ι × W) (ι × W) ℂ),
      IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧
        QueryCount C ≤ q ∧ Size C ≤ s ∧
        ∀ x ∈ P,
          (2 / 3 : ℝ) ≤ povmProb out (yes x) (Run (bitOracle (W := W) (input x)) C psi)

/-- Query-only version of `QuantumDecides` (no step bound), used for lower bounds. -/
def QuantumDecidesQ {X ι : Type} [Fintype ι] [DecidableEq ι]
    (input : X → ι → Bool) (P : Set X) (yes : X → Bool) (q : ℕ) : Prop :=
  ∃ (W : Type) (iW : Fintype W) (dW : DecidableEq W),
    letI := iW
    letI := dW
    ∃ (C : Circuit (ι × W)) (psi : QState (ι × W))
      (out : Bool → Matrix (ι × W) (ι × W) ℂ),
      IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧ QueryCount C ≤ q ∧
        ∀ x ∈ P,
          (2 / 3 : ℝ) ≤ povmProb out (yes x) (Run (bitOracle (W := W) (input x)) C psi)

/-- Two-sided tester: accepts every member of `accept` with probability at least
`pAccept`, rejects every member of `reject` with probability at least `pReject`.
`pReject = 1` means rejection with certainty (Lemma 4.2). -/
def QuantumTester {X ι : Type} [Fintype ι] [DecidableEq ι]
    (input : X → ι → Bool) (accept reject : Set X) (pAccept pReject : ℝ)
    (q s : ℕ) : Prop :=
  ∃ (W : Type) (iW : Fintype W) (dW : DecidableEq W),
    letI := iW
    letI := dW
    ∃ (C : Circuit (ι × W)) (psi : QState (ι × W))
      (out : Bool → Matrix (ι × W) (ι × W) ℂ),
      IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧
        QueryCount C ≤ q ∧ Size C ≤ s ∧
        (∀ x ∈ accept,
          pAccept ≤ povmProb out true (Run (bitOracle (W := W) (input x)) C psi)) ∧
        (∀ x ∈ reject,
          pReject ≤ povmProb out false (Run (bitOracle (W := W) (input x)) C psi))

/-- Query-only tester (used for quantum lower bounds). -/
def QuantumTesterQ {X ι : Type} [Fintype ι] [DecidableEq ι]
    (input : X → ι → Bool) (accept reject : Set X) (pAccept pReject : ℝ)
    (q : ℕ) : Prop :=
  ∃ (W : Type) (iW : Fintype W) (dW : DecidableEq W),
    letI := iW
    letI := dW
    ∃ (C : Circuit (ι × W)) (psi : QState (ι × W))
      (out : Bool → Matrix (ι × W) (ι × W) ℂ),
      IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧ QueryCount C ≤ q ∧
        (∀ x ∈ accept,
          pAccept ≤ povmProb out true (Run (bitOracle (W := W) (input x)) C psi)) ∧
        (∀ x ∈ reject,
          pReject ≤ povmProb out false (Run (bitOracle (W := W) (input x)) C psi))

/-- Tester with separate bounds on queries and on non-query elementary
operations (`GateCount`), matching Lemma 4.2's "queries" vs "other elementary
operations" split. -/
def QuantumTesterGate {X ι : Type} [Fintype ι] [DecidableEq ι]
    (input : X → ι → Bool) (accept reject : Set X) (pAccept pReject : ℝ)
    (q g : ℕ) : Prop :=
  ∃ (W : Type) (iW : Fintype W) (dW : DecidableEq W),
    letI := iW
    letI := dW
    ∃ (C : Circuit (ι × W)) (psi : QState (ι × W))
      (out : Bool → Matrix (ι × W) (ι × W) ℂ),
      IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧
        QueryCount C ≤ q ∧ GateCount C ≤ g ∧
        (∀ x ∈ accept,
          pAccept ≤ povmProb out true (Run (bitOracle (W := W) (input x)) C psi)) ∧
        (∀ x ∈ reject,
          pReject ≤ povmProb out false (Run (bitOracle (W := W) (input x)) C psi))

/-- The QGGT promise of Definition 5.1: the oracle family is in `X̃` (identity on
`S ∩ A = ∅`) or in `Ỹ` (`-1` on `S ∩ B ≠ ∅`). -/
def IsQGGTInstance {n : ℕ} {W : Type} [DecidableEq W]
    (k d : ℕ) (O : Finset (Fin n) → Matrix W W ℂ) : Prop :=
  (∃ A : Finset (Fin n), A.card = k ∧ ∀ S, S ∩ A = ∅ → O S = 1) ∨
    (∃ B : Finset (Fin n), B.card = k + d ∧ ∀ S, (S ∩ B).Nonempty → O S = -1)

/-- `QGGTSolver k d n q s`: one quantum algorithm (circuit + readout, independent of
the instance oracle) that solves every QGGT instance with `k, d` on `n` qubits in
at most `q` queries and `s` steps, accepting all `X̃` instances and rejecting all
`Ỹ` instances. -/
def QGGTSolver (k d n q s : ℕ) : Prop :=
  ∃ (W : Type) (iW : Fintype W) (dW : DecidableEq W),
    letI := iW
    letI := dW
    ∃ (C : Circuit (Finset (Fin n) × W)) (psi : QState (Finset (Fin n) × W))
      (out : Bool → Matrix (Finset (Fin n) × W) (Finset (Fin n) × W) ℂ),
      IsUnitaryCircuit C ∧ Normalized psi ∧ IsPovm out ∧
        QueryCount C ≤ q ∧ Size C ≤ s ∧
        ∀ (O : Finset (Fin n) → Matrix W W ℂ), IsQGGTInstance k d O →
          (∀ A : Finset (Fin n), A.card = k → (∀ S, S ∩ A = ∅ → O S = 1) →
            (2 / 3 : ℝ) ≤
              povmProb out true (Run (blockOracle O) C psi)) ∧
          (∀ B : Finset (Fin n), B.card = k + d → (∀ S, (S ∩ B).Nonempty → O S = -1) →
            (2 / 3 : ℝ) ≤
              povmProb out false (Run (blockOracle O) C psi))

/-! ## Adversary bound and irrelevant-variable composition (Section 2.3, Appendix A) -/

variable {X ι : Type} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]

/-- A partial Boolean function: domain predicate and Boolean value. -/
structure PartialBoolFun (X : Type*) where
  dom : X → Prop
  val : X → Bool

/-- Feasible solution of the dual adversary SDP (3) for the input family
`input : X → ι → Bool`: PSD matrices `M j` and the constraint (3b). -/
def AdvFeasible (input : X → ι → Bool) (F : PartialBoolFun X)
    (M : ι → Matrix X X ℂ) : Prop :=
  (∀ j, (M j).PosSemidef) ∧
    ∀ x y, F.dom x → F.dom y → F.val x ≠ F.val y →
      (Finset.univ.filter (fun j => input x j ≠ input y j)).sum (fun j => M j x y) = 1

/-- The paper's `ADV±(F)`, Eq. (3): infimum of the objective over feasible
solutions of the dual adversary SDP. -/
def AdvPlus (input : X → ι → Bool) (F : PartialBoolFun X) : ℝ :=
  sInf {T : ℝ | ∃ M : ι → Matrix X X ℂ,
    AdvFeasible input F M ∧ 0 ≤ T ∧ ∀ z, F.dom z →
      (∑ j, (M j z z).re) ≤ T}

/-- Consistency condition of Definition 2.8: every pair of inputs of `F` (a partial
Boolean function on `n` bits) with different values has a variable relevant to both
on which they differ. -/
def IrrelevantConsistent {n : ℕ} (F : PartialBoolFun (Fin n → Bool))
    (rel : (Fin n → Bool) → Fin n → Prop) : Prop :=
  ∀ x y, F.dom x → F.dom y → F.val x ≠ F.val y →
    ∃ j, rel x j ∧ rel y j ∧ x j ≠ y j

/-- Irrelevant variables of Proposition 2.11: `j` is irrelevant for `z` iff
`X_j[[z,z]] = 0`; hence relevant iff the diagonal entry is nonzero. -/
def diagonalRelevant (M : ι → Matrix X X ℂ) (z : X) (j : ι) : Prop :=
  M j z z ≠ 0

/-- The robust composition `F ∘ (G_1, …, G_n)` of Definition 2.10 (with irrelevant
variables).  Inputs are tuples `x j : (Fin (m j) → Bool)`.  It is defined iff there
is a witness `z ∈ dom F` matching every relevant `G_j(x_j)`; the value is `F(z)`
(independent of the witness, by Proposition 2.11). -/
def robustCompose {n : ℕ} (m : Fin n → ℕ)
    (F : PartialBoolFun (Fin n → Bool)) (rel : (Fin n → Bool) → Fin n → Prop)
    (G : ∀ j, PartialBoolFun (Fin (m j) → Bool)) :
    PartialBoolFun (∀ j, Fin (m j) → Bool) where
  dom x := ∃ z, F.dom z ∧
    ∀ j, rel z j → (G j).dom (x j) ∧ (G j).val (x j) = z j
  val x := if h : (∃ z, F.dom z ∧
      ∀ j, rel z j → (G j).dom (x j) ∧ (G j).val (x j) = z j)
    then F.val (Classical.choose h) else false

end Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel
