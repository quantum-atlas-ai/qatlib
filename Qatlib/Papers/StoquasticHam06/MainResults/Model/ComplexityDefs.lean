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

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Concepts.CountingClasses.ClassTransport

namespace Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

abbrev Sigma (n : ℕ) := Fin n → Bool

structure Encoding (α : Type*) where

  code : α → List Bool

namespace Encoding

def ofEncodable (α : Type*) [Encodable α] : Encoding α :=
  ⟨fun a => Nat.bits (Encodable.encode a)⟩

def listEncoding : Encoding (List Bool) := ⟨id⟩

end Encoding

structure PromiseProblem (α : Type*) where

  yes : α → Prop

  no : α → Prop

structure Verifier (α : Type*) where

  states : ℕ

  c : ℕ

  k : ℕ

  witnessPoly : ℕ → ℕ

  V : CcProgram states

  poly : CcPolyTime V c k

namespace Verifier

variable {α : Type*}

def witnessLen (W : Verifier α) (E : Encoding α) (x : α) : ℕ :=
  W.witnessPoly (E.code x).length

def budget (W : Verifier α) (E : Encoding α) (x : α) (w : List Bool) : ℕ :=
  W.c * (E.code x ++ w).length ^ W.k + W.c

def acceptCount (W : Verifier α) (E : Encoding α) (x : α) (w : List Bool) : ℕ :=
  ccAcceptCount W.V ccZeroOracle (E.code x ++ w) (W.budget E x w)

def accept (W : Verifier α) (E : Encoding α) (x : α) (w : List Bool) : ℝ :=
  (W.acceptCount E x w : ℝ) / (2 : ℝ) ^ W.budget E x w

end Verifier

def InMA {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ W : Verifier α, ∀ x : α,
    (L.yes x → ∃ z : Fin (W.witnessLen E x) → Bool,
      (2 : ℝ) / 3 ≤ W.accept E x (List.ofFn z)) ∧
    (L.no x → ∀ z : Fin (W.witnessLen E x) → Bool,
      W.accept E x (List.ofFn z) ≤ (1 : ℝ) / 3)

def Normalized {n : ℕ} (ξ : Sigma n → ℂ) : Prop :=
  (∑ z, Complex.normSq (ξ z)) = 1

def qAccept {n : ℕ} (a : Sigma n → ℝ) (ξ : Sigma n → ℂ) : ℝ :=
  ∑ z, a z * Complex.normSq (ξ z)

def InMAq {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ W : Verifier α, ∀ x : α,
    (L.yes x → ∃ ξ : Sigma (W.witnessLen E x) → ℂ,
      Normalized ξ ∧ (2 : ℝ) / 3 ≤ qAccept (fun z => W.accept E x (List.ofFn z)) ξ) ∧
    (L.no x → ∀ ξ : Sigma (W.witnessLen E x) → ℂ,
      Normalized ξ → qAccept (fun z => W.accept E x (List.ofFn z)) ξ ≤ (1 : ℝ) / 3)

structure AMVerifier (α : Type*) extends Verifier α where

  questionPoly : ℕ → ℕ

namespace AMVerifier

variable {α : Type*}

def questionLen (A : AMVerifier α) (E : Encoding α) (x : α) : ℕ :=
  A.questionPoly (E.code x).length

def coinBudget (A : AMVerifier α) (E : Encoding α) (x : α) : ℕ :=
  A.c * ((E.code x).length + A.questionLen E x + A.witnessPoly (E.code x).length) ^ A.k + A.c

def strategy (A : AMVerifier α) (E : Encoding α) (x : α) : Type :=
  (Fin (A.questionLen E x) → Bool) → List Bool

def amAcceptCount (A : AMVerifier α) (E : Encoding α) (x : α)
    (R : A.strategy E x) : ℕ :=
  ∑ q : Fin (A.questionLen E x) → Bool,
    ccAcceptCount A.V ccZeroOracle (E.code x ++ List.ofFn q ++ R q) (A.coinBudget E x)

def amProb (A : AMVerifier α) (E : Encoding α) (x : α) (R : A.strategy E x) : ℝ :=
  (A.amAcceptCount E x R : ℝ) /
    ((2 : ℝ) ^ A.questionLen E x * (2 : ℝ) ^ A.coinBudget E x)

end AMVerifier

def InAM {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ A : AMVerifier α, ∀ x : α,
    (L.yes x → ∃ R : A.strategy E x, (2 : ℝ) / 3 ≤ A.amProb E x R) ∧
    (L.no x → ∀ R : A.strategy E x, A.amProb E x R ≤ (1 : ℝ) / 3)

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

def budgetA (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  M.cA * (E.code x).length ^ M.kA + M.cA

def budgetB (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  M.cB * (E.code x).length ^ M.kB + M.cB

def coinLen (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  max (M.budgetA E x) (M.budgetB E x)

def bCount (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  ccAcceptCount M.B ccZeroOracle (E.code x) (M.coinLen E x)

def aCount (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  ccAcceptCount M.A ccZeroOracle (E.code x) (M.coinLen E x)

def abCount (M : PPTMachine α) (E : Encoding α) (x : α) : ℕ :=
  (Finset.univ.filter (fun ω : Fin (M.coinLen E x) → Bool =>
    ccResult M.B ccZeroOracle (ccCoinString ω) (E.code x) (M.coinLen E x) = some true ∧
    ccResult M.A ccZeroOracle (ccCoinString ω) (E.code x) (M.coinLen E x) = some true)).card

def postFrac (M : PPTMachine α) (E : Encoding α) (x : α) : ℝ :=
  (M.abCount E x : ℝ) / (M.bCount E x : ℝ)

end PPTMachine

def InPostBPP {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ M : PPTMachine α, ∀ x : α,
    (L.yes x → 0 < M.bCount E x ∧ (2 : ℝ) / 3 ≤ M.postFrac E x) ∧
    (L.no x → 0 < M.bCount E x ∧ M.postFrac E x ≤ (1 : ℝ) / 3)

structure PathMachine (α : Type*) where

  states : ℕ

  c : ℕ

  k : ℕ

  M : CcProgram states

  poly : CcPolyTime M c k

namespace PathMachine

variable {α : Type*}

def coinLen (P : PathMachine α) (E : Encoding α) (x : α) : ℕ :=
  P.c * (E.code x).length ^ P.k + P.c

def acceptCount (P : PathMachine α) (E : Encoding α) (x : α) : ℕ :=
  ccAcceptCount P.M ccZeroOracle (E.code x) (P.coinLen E x)

def frac (P : PathMachine α) (E : Encoding α) (x : α) : ℝ :=
  (P.acceptCount E x : ℝ) / (2 : ℝ) ^ P.coinLen E x

end PathMachine

def InBPPpath {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ P : PathMachine α, ∀ x : α,
    (L.yes x → 0 < P.acceptCount E x ∧ (2 : ℝ) / 3 ≤ P.frac E x) ∧
    (L.no x → 0 < P.acceptCount E x ∧ P.frac E x ≤ (1 : ℝ) / 3)

def InNPBPP {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  ∃ (B : List Bool → Prop), InBPP B ∧
  ∃ (q c k p : ℕ) (V : CcProgram q), CcPolyTime V c k ∧
    ∀ x : α, (L.yes x ↔ ∃ w : Fin (p * (E.code x).length ^ p + p) → Bool,
      ccOracleVerifies V (ccOracleOf B) c k (E.code x) (List.ofFn w) = true)

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

def InSigma3p {α : Type*} (E : Encoding α) (L : PromiseProblem α) : Prop :=
  InPHLevel 3 (fun z => ∃ x : α, E.code x = z ∧ L.yes x)

def PolyComputable {α β : Type*} (E : Encoding α) (F : Encoding β) (f : α → β) : Prop :=
  ∃ (q c k : ℕ) (M : CcProgram q), CcPolyTime M c k ∧
    ∀ x : α, ccOutput M ccZeroOracle ccDefaultCoin (E.code x)
      (c * (E.code x).length ^ k + c) = F.code (f x)

def PolyReduces {α β : Type*} (E : Encoding α) (F : Encoding β) (f : α → β)
    (L : PromiseProblem α) (P : PromiseProblem β) : Prop :=
  PolyComputable E F f ∧ ∀ x : α, (L.yes x → P.yes (f x)) ∧ (L.no x → P.no (f x))

def MAHard {α : Type*} (E : Encoding α) (P : PromiseProblem α) : Prop :=
  ∀ (β : Type) (F : Encoding β) (L : PromiseProblem β), InMA F L →
    ∃ f : β → α, PolyReduces F E f L P

end Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
