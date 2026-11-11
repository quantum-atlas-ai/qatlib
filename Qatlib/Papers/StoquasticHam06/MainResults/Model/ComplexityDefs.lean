/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Finset

/-!
# Verifier and complexity predicates for stoquastic problems

The model packages Boolean encodings, yes and no predicates, bounded programs, and acceptance
counts. `InMA`, `InMAq`, `InAM`, and the postselection and oracle predicates express the
conditions used by the result files; `PolyComputable`, `PolyReduces`, and `MAHard` specify their
reduction framework. See [BravyiEtAl2008Stoquastic].

## Main statements

* `InMA`: the classical witness acceptance conditions.
* `InMAq`: the corresponding normalized-vector acceptance conditions.
* `InPostBPP`: conditional acceptance with a nonzero postselection count.
* `PolyReduces`: a computable reduction preserving both promises.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Concepts.CountingClasses.ClassTransport

namespace Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

/-- Boolean strings of length `n`, represented as functions from `Fin n` to `Bool`. -/
abbrev Sigma (n : ℕ) := Fin n → Bool

/-- A choice of Boolean-list code for each input. -/
structure Encoding (α : Type*) where

  code : α → List Bool

namespace Encoding

/-- The Boolean encoding obtained from the bits of an `Encodable` natural-number code. -/
def ofEncodable (α : Type*) [Encodable α] : Encoding α :=
  ⟨fun a => Nat.bits (Encodable.encode a)⟩

/-- The identity encoding of Boolean lists. -/
def listEncoding : Encoding (List Bool) := ⟨id⟩

end Encoding

/-- A pair of predicates specifying yes instances and no instances. -/
structure PromiseProblem (α : Type*) where

  yes : α → Prop

  no : α → Prop

/-- A bounded verifier program with a polynomial-time certificate and a function specifying
witness lengths. -/
structure Verifier (α : Type*) where

  states : ℕ

  c : ℕ

  k : ℕ

  witnessPoly : ℕ → ℕ

  V : CcProgram states

  poly : CcPolyTime V c k

namespace Verifier

variable {α : Type*}

/-- The verifier's witness-length function evaluated at the encoded input length. -/
def witnessLen (W : Verifier α) (E : Encoding α) (x : α) : ℕ :=
  W.witnessPoly (E.code x).length

/-- The verifier's time and coin budget `c * length ^ k + c` for the concatenated encoded input
and witness. -/
def budget (W : Verifier α) (E : Encoding α) (x : α) (w : List Bool) : ℕ :=
  W.c * (E.code x ++ w).length ^ W.k + W.c

/-- The number of accepting coin strings for the verifier on the encoded input and witness
within its budget. -/
def acceptCount (W : Verifier α) (E : Encoding α) (x : α) (w : List Bool) : ℕ :=
  ccAcceptCount W.V ccZeroOracle (E.code x ++ w) (W.budget E x w)

/-- The verifier's accepting count divided by `2` to the power of its budget. -/
def accept (W : Verifier α) (E : Encoding α) (x : α) (w : List Bool) : ℝ :=
  (W.acceptCount E x w : ℝ) / (2 : ℝ) ^ W.budget E x w

end Verifier

/-- The existence of a verifier with a classical witness reaching acceptance at least `2 / 3` on
yes instances and every witness reaching at most `1 / 3` on no instances. -/
def InMA {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ W : Verifier α, ∀ x : α,
    (L.yes x → ∃ z : Fin (W.witnessLen E x) → Bool,
      (2 : ℝ) / 3 ≤ W.accept E x (List.ofFn z)) ∧
    (L.no x → ∀ z : Fin (W.witnessLen E x) → Bool,
      W.accept E x (List.ofFn z) ≤ (1 : ℝ) / 3)

/-- The condition that the sum of squared complex norms of all coordinates is one. -/
def Normalized {n : ℕ} (ξ : Sigma n → ℂ) : Prop :=
  (∑ z, Complex.normSq (ξ z)) = 1

/-- The diagonal acceptance average `∑ z, a z * normSq (ξ z)`. -/
def qAccept {n : ℕ} (a : Sigma n → ℝ) (ξ : Sigma n → ℂ) : ℝ :=
  ∑ z, a z * Complex.normSq (ξ z)

/-- The verifier predicate using normalized complex witnesses and `qAccept`, with completeness
`2 / 3` and soundness `1 / 3`. -/
def InMAq {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ W : Verifier α, ∀ x : α,
    (L.yes x → ∃ ξ : Sigma (W.witnessLen E x) → ℂ,
      Normalized ξ ∧ (2 : ℝ) / 3 ≤ qAccept (fun z => W.accept E x (List.ofFn z)) ξ) ∧
    (L.no x → ∀ ξ : Sigma (W.witnessLen E x) → ℂ,
      Normalized ξ → qAccept (fun z => W.accept E x (List.ofFn z)) ξ ≤ (1 : ℝ) / 3)

/-- A verifier extended with a function specifying the length of the public question. -/
structure AMVerifier (α : Type*) extends Verifier α where

  questionPoly : ℕ → ℕ

namespace AMVerifier

variable {α : Type*}

/-- The public-question length function evaluated at the encoded input length. -/
def questionLen (A : AMVerifier α) (E : Encoding α) (x : α) : ℕ :=
  A.questionPoly (E.code x).length

/-- The common coin budget determined by the encoded input, question length, and specified
witness length. -/
def coinBudget (A : AMVerifier α) (E : Encoding α) (x : α) : ℕ :=
  A.c * ((E.code x).length + A.questionLen E x + A.witnessPoly (E.code x).length) ^ A.k + A.c

/-- A response strategy assigning a Boolean-list answer to each public question. -/
def strategy (A : AMVerifier α) (E : Encoding α) (x : α) : Type :=
  (Fin (A.questionLen E x) → Bool) → List Bool

/-- The sum of accepting verifier counts over all public questions under the given response
strategy. -/
def amAcceptCount (A : AMVerifier α) (E : Encoding α) (x : α)
    (R : A.strategy E x) : ℕ :=
  ∑ q : Fin (A.questionLen E x) → Bool,
    ccAcceptCount A.V ccZeroOracle (E.code x ++ List.ofFn q ++ R q) (A.coinBudget E x)

/-- The summed accepting count divided by the product of the numbers of question strings and
coin strings. -/
def amProb (A : AMVerifier α) (E : Encoding α) (x : α) (R : A.strategy E x) : ℝ :=
  (A.amAcceptCount E x R : ℝ) /
    ((2 : ℝ) ^ A.questionLen E x * (2 : ℝ) ^ A.coinBudget E x)

end AMVerifier

/-- The existence of an AM verifier with a strategy reaching acceptance at least `2 / 3` on yes
instances and all strategies reaching at most `1 / 3` on no instances. -/
def InAM {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ A : AMVerifier α, ∀ x : α,
    (L.yes x → ∃ R : A.strategy E x, (2 : ℝ) / 3 ≤ A.amProb E x R) ∧
    (L.no x → ∀ R : A.strategy E x, A.amProb E x R ≤ (1 : ℝ) / 3)

/-- A pair of programs for acceptance and postselection, each with a polynomial-time
certificate. -/
structure PPTMachine (α : Type*) where

  statesA : ℕ

  cA : ℕ

  kA : ℕ

  A : CcProgram statesA

  polyA : CcPolyTime A cA kA

  statesB : ℕ

  cB : ℕ

  kB : ℕ

  B : CcProgram statesB

  polyB : CcPolyTime B cB kB

namespace PPTMachine

variable {α : Type*}

/-- The polynomial budget of the acceptance program on the encoded input. -/
def budgetA (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  M.cA * (E.code x).length ^ M.kA + M.cA

/-- The polynomial budget of the postselection program on the encoded input. -/
def budgetB (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  M.cB * (E.code x).length ^ M.kB + M.cB

/-- The common coin length, defined as the maximum of the acceptance and postselection budgets. -/
def coinLen (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  max (M.budgetA E x) (M.budgetB E x)

/-- The accepting count of the postselection program at the common coin length. -/
def bCount (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  ccAcceptCount M.B ccZeroOracle (E.code x) (M.coinLen E x)

/-- The accepting count of the acceptance program at the common coin length. -/
def aCount (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  ccAcceptCount M.A ccZeroOracle (E.code x) (M.coinLen E x)

/-- The number of common coin strings on which both the acceptance and postselection programs
return true. -/
def abCount (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  (Finset.univ.filter (fun ω : Fin (M.coinLen E x) → Bool =>
    ccResult M.B ccZeroOracle (ccCoinString ω) (E.code x) (M.coinLen E x) = some true ∧
    ccResult M.A ccZeroOracle (ccCoinString ω) (E.code x) (M.coinLen E x) = some true)).card

/-- The joint accepting count divided by the postselection accepting count. -/
def postFrac (M : PPTMachine α) (E : Encoding α) (x : α) : ℝ :=
  (M.abCount E x : ℝ) / (M.bCount E x : ℝ)

end PPTMachine

/-- The existence of paired programs with positive postselection count on promised inputs and
conditional acceptance at least `2 / 3` on yes instances and at most `1 / 3` on no
instances. -/
def InPostBPP {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ M : PPTMachine α, ∀ x : α,
    (L.yes x → 0 < M.bCount E x ∧ (2 : ℝ) / 3 ≤ M.postFrac E x) ∧
    (L.no x → 0 < M.bCount E x ∧ M.postFrac E x ≤ (1 : ℝ) / 3)

/-- A single bounded program with a polynomial-time certificate for the path acceptance
predicate. -/
structure PathMachine (α : Type*) where

  states : ℕ

  c : ℕ

  k : ℕ

  M : CcProgram states

  poly : CcPolyTime M c k

namespace PathMachine

variable {α : Type*}

/-- The path machine's polynomial coin and time budget on the encoded input. -/
def coinLen (P : PathMachine α) (E : Encoding α) (x : α) : ℕ :=
  P.c * (E.code x).length ^ P.k + P.c

/-- The number of accepting coin strings for the path machine within its budget. -/
def acceptCount (P : PathMachine α) (E : Encoding α) (x : α) : ℕ :=
  ccAcceptCount P.M ccZeroOracle (E.code x) (P.coinLen E x)

/-- The path machine's accepting count divided by the number of coin strings. -/
def frac (P : PathMachine α) (E : Encoding α) (x : α) : ℝ :=
  (P.acceptCount E x : ℝ) / (2 : ℝ) ^ P.coinLen E x

end PathMachine

/-- The existence of a path machine with positive accepting count on both promises and
acceptance fraction at least `2 / 3` on yes instances and at most `1 / 3` on no instances. -/
def InBPPpath {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ P : PathMachine α, ∀ x : α,
    (L.yes x → 0 < P.acceptCount E x ∧ (2 : ℝ) / 3 ≤ P.frac E x) ∧
    (L.no x → 0 < P.acceptCount E x ∧ P.frac E x ≤ (1 : ℝ) / 3)

/-- The existence of a BPP oracle and a polynomial-time oracle verifier whose bounded witnesses
characterize exactly the yes instances. -/
def InNPBPP {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ (B : List Bool → Prop), InBPP B ∧
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : α, (L.yes x ↔ ∃ w : Fin (p * (E.code x).length ^ p + p) → Bool,
      ccOracleVerifies V (ccOracleOf B) c k (E.code x) (List.ofFn w) = true)

/-- The existence of an NP oracle and a polynomial-time randomized oracle program satisfying the
stated `2 / 3` completeness and `1 / 3` soundness count bounds. -/
def InBPPNP {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ (B : List Bool → Prop), InNP B ∧
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : α,
      (L.yes x →
        3 * ccAcceptCount M (ccOracleOf B) (E.code x) (c * (E.code x).length ^ k + c)
          ≥ 2 * 2 ^ (c * (E.code x).length ^ k + c)) ∧
      (L.no x →
        3 * ccAcceptCount M (ccOracleOf B) (E.code x) (c * (E.code x).length ^ k + c)
          ≤ 2 ^ (c * (E.code x).length ^ k + c))

/-- Membership of the encoded yes-instance language in level three of the polynomial hierarchy. -/
def InSigma3p {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  InPHLevel 3 (fun z => ∃ x : α, E.code x = z ∧ L.yes x)

/-- The existence of a polynomial-time program that outputs the chosen code of `f x` from the
chosen code of `x` using the default coin string. -/
def PolyComputable {α β : Type*} (E : Encoding α) (F : Encoding β) (f : α → β) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : α, ccOutput M ccZeroOracle ccDefaultCoin (E.code x)
      (c * (E.code x).length ^ k + c) = F.code (f x)

/-- A polynomially computable map that sends yes instances to yes instances and no instances to
no instances. -/
def PolyReduces {α β : Type*} (E : Encoding α) (F : Encoding β) (f : α → β)
    (L : PromiseProblem α) (P : PromiseProblem β) : Prop :=
  PolyComputable E F f ∧ ∀ x : α, (L.yes x → P.yes (f x)) ∧ (L.no x → P.no (f x))

/-- The property that every encoded promise problem satisfying `InMA` has a `PolyReduces`
reduction to the given problem. -/
def MAHard {α : Type*} (E : Encoding α) (P : PromiseProblem α) : Prop :=
  ∀ (β : Type) (F : Encoding β) (L : PromiseProblem β), InMA F L →
    ∃ f : β → α, PolyReduces F E f L P

end Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
