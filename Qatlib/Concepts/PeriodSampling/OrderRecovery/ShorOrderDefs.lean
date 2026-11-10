/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder
import Qatlib.Concepts.PeriodSampling.OrderRecovery.ContinuedFractionOrderConsumers
import Qatlib.Concepts.WalshMoment.Forrelation.FiniteAbelian
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.PeriodSampling.OrderRecovery.ModularOrderPhaseReadout
import Qatlib.Concepts.PeriodSampling.OrderRecovery.OrderFactorConsumers
import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor
import Qatlib.Concepts.IntWordFraming.WordFraming.SmithFraming
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.WalshMoment.Forrelation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery

open Qatlib
open Matrix
open scoped Classical BigOperators ComplexConjugate
set_option warningAsError false

theorem pow_le_pow_of_le_base (a b n : ℕ) (h : a ≤ b) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact Nat.mul_le_mul ih h

theorem pow_ge_self (a n : ℕ) (ha : 1 ≤ a) (hn : 1 ≤ n) : a ≤ a ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · rw [h, pow_succ, pow_zero, one_mul]
    · rw [pow_succ]
      have h1 : a ≤ a ^ n := ih (by omega)
      exact h1.trans (by simpa using! Nat.mul_le_mul (le_refl _) (by omega : 1 ≤ a))

def orderBitLength (N : ℕ) : ℕ := Nat.log 2 N + 1

def polyLogBound (c d N : ℕ) : ℕ := c * (orderBitLength N + 1) ^ d

def PolyLogDominates (c d N : ℕ) : Prop :=
  0 < c ∧ 0 < d ∧ orderBitLength N ≤ polyLogBound c d N

def powExceedSet (e N : ℕ) : Finset ℕ :=
  (Finset.filter (fun r => r ^ e > N) (Finset.range (N + 2)))

def powExceedWitness (e N : ℕ) (he : 1 ≤ e) : ∃ r, r ^ e > N :=
  ⟨N + 1, by
    have hpow := pow_ge_self (N + 1) e (by omega) he
    omega⟩

def intRoot (e N : ℕ) : ℕ :=
  if h : e = 0 then 0 else Nat.find (powExceedWitness e N (by omega)) - 1

def perfectPowerCandidates (N : ℕ) : Finset ℕ :=
  (Finset.filter (fun e => 2 ≤ e ∧ 2 ≤ intRoot e N ∧ intRoot e N ^ e = N)
    (Finset.range (orderBitLength N + 1)))

def perfectPowerDivisors (N : ℕ) : Finset ℕ :=
  (perfectPowerCandidates N).image (fun e => intRoot e N)

def perfectPowerExponent (N : ℕ) : Option ℕ :=
  let s := perfectPowerCandidates N
  if h : s.card = 0 then none else some (s.min' (Finset.card_ne_zero.mp (by omega)))

def perfectPowerDivisor (N : ℕ) : Option ℕ :=
  (perfectPowerExponent N).map (fun e => intRoot e N)

def evenDivisor (N : ℕ) : Option ℕ :=
  if 4 ≤ N ∧ 2 ∣ N then some 2 else none

inductive PreprocessVerdict where

  | even (d : ℕ)

  | perfectPower (d : ℕ)

  | residue
  deriving DecidableEq, Repr

def preprocess (N : ℕ) : PreprocessVerdict :=
  match evenDivisor N with
  | some d => .even d
  | none =>
    match perfectPowerDivisor N with
    | some d => .perfectPower d
    | none => .residue

def preprocessBitCost (N : ℕ) : ℕ :=
  orderBitLength N * (orderBitLength N + 1) * (orderBitLength N + 1)

def CompositeCertificate (N d : ℕ) : Prop := 1 < d ∧ d < N ∧ d ∣ N

def PrimeDirectionWitness (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Prop :=
  a ^ (N - 1) = 1

def schoolbookMulModCost (b : ℕ) : ℕ := 2 * b * b + b

def localQftGateCount (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

def localQftSpaceCost (n : ℕ) : ℕ := n

def euclidStepBound (b : ℕ) : ℕ := 2 * b + 1

def euclidStepCost (b : ℕ) : ℕ := schoolbookMulModCost b

def euclidBitCost (b : ℕ) : ℕ := euclidStepBound b * euclidStepCost b

def euclidSpaceCost (b : ℕ) : ℕ := 2 * b

structure AttemptLedger where

  bits : ℕ

  queries : ℕ

  gates : ℕ

  space : ℕ
  deriving DecidableEq, Repr

def AttemptLedger.le (l₁ l₂ : AttemptLedger) : Prop :=
  l₁.bits ≤ l₂.bits ∧ l₁.queries ≤ l₂.queries ∧ l₁.gates ≤ l₂.gates ∧ l₁.space ≤ l₂.space

instance : LE AttemptLedger := ⟨fun l₁ l₂ => l₁.le l₂⟩

def attemptLedgerBound (N M k : ℕ) : AttemptLedger where
  bits := k + 2 * euclidBitCost (orderBitLength N)
  queries := 2 * (M * (M - 1) / 2)
  gates := 2 * (M * (M - 1) + 2)
  space := k + 2 * orderBitLength M + 2 * orderBitLength N

def rejectedLedger (k : ℕ) : AttemptLedger where
  bits := k
  queries := 0
  gates := 0
  space := k

inductive AttemptOutcome (N M : ℕ) [NeZero N] where

  | rejected

  | classicalGcd (y : ZMod N)

  | quantumOrder (a : (ZMod N)ˣ) (yz : Fin M × Fin M)
  deriving DecidableEq

noncomputable def attemptOutcomeFactor (N M : ℕ) [NeZero N] :
    AttemptOutcome N M → Option ℕ
  | .rejected => none
  | .classicalGcd y =>
    let d := Nat.gcd N y.val
    if 1 < d ∧ d < N then some d else none
  | .quantumOrder a yz =>
    (cfPairLCMOrderDecode N M a yz).1.bind (orderFactor N a)

def firstSuccessAt {N M R : ℕ} [NeZero N] (ω : Fin R → AttemptOutcome N M) (j : Fin R) : Prop :=
  (attemptOutcomeFactor N M (ω j)).isSome ∧
    ∀ (i : ℕ) (hi : i < j.val),
      (attemptOutcomeFactor N M (ω ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_of_lt j.isLt)⟩)).isSome = false

structure FirstSuccessReceipt (N M k R : ℕ) [NeZero N] where

  trajectory : Fin R → AttemptOutcome N M

  first : Fin R

  first_success : firstSuccessAt (N := N) (M := M) (R := R) trajectory first

structure ProperDivisor (n : ℕ) where

  d : ℕ

  proof : 1 < d ∧ d < n ∧ d ∣ n

inductive FactorTree where

  | leaf (p : ℕ) (cost : ℕ)

  | node (n d : ℕ) (cost : ℕ) (left right : FactorTree)
  deriving DecidableEq, Repr

def FactorTree.root : FactorTree → ℕ
  | .leaf p _ => p
  | .node n _ _ _ _ => n

def FactorTree.cost : FactorTree → ℕ
  | .leaf _ c => c
  | .node _ _ c l r => c + l.cost + r.cost

def FactorTree.leaves : FactorTree → List ℕ
  | .leaf p _ => [p]
  | .node _ _ _ l r => l.leaves ++ r.leaves

def FactorTree.leavesProduct : FactorTree → ℕ
  | .leaf p _ => p
  | .node _ _ _ l r => l.leavesProduct * r.leavesProduct

def factorTreeOfFuel (split : ∀ n, Option (ProperDivisor n)) : ℕ → ℕ → FactorTree
  | 0, _ => .leaf 0 0
  | _ + 1, 0 => .leaf 0 0
  | fuel + 1, n + 1 =>
    Option.rec (motive := fun _ => FactorTree) (FactorTree.leaf (n + 1) 0)
      (fun pd => FactorTree.node (n + 1) pd.d 0
        (factorTreeOfFuel split fuel pd.d)
        (factorTreeOfFuel split fuel ((n + 1) / pd.d)))
      (split (n + 1))

def factorTreeOf (split : ∀ n, Option (ProperDivisor n)) (n : ℕ) : FactorTree :=
  factorTreeOfFuel split n n

def FactorTree.complete (t : FactorTree) : Prop :=
  t.leavesProduct = t.root ∧ ∀ p ∈ t.leaves, p ≤ 1 ∨ Nat.Prime p

def FactorTree.splitSound (split : ∀ n, Option (ProperDivisor n)) :
    FactorTree → Prop
  | .leaf _ _ => True
  | .node n d _ l r =>
    ∃ pd : ProperDivisor n, split n = some pd ∧
      pd.d = d ∧ l.root = d ∧ r.root = n / d

variable {Ω H O : Type} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O]

def ComputationIsometry (V : Matrix H Ω ℂ) : Prop := Vᴴ * V = 1

def MeasurementOperatorFamily (T : O → Matrix Ω Ω ℂ) : Prop :=
  ∑ ω, (T ω)ᴴ * (T ω) = 1

noncomputable def workspaceMass (T : O → Matrix Ω Ω ℂ) (ψ : QState Ω) (ω : O) : ℝ :=
  ∑ i, ‖((T ω) *ᵥ ψ) i‖ ^ 2

noncomputable def compiledMass (V : Matrix H Ω ℂ) (T : O → Matrix Ω Ω ℂ)
    (φ : QState H) (ω : O) : ℝ :=
  ∑ i, ‖((V * (T ω) * Vᴴ) *ᵥ φ) i‖ ^ 2

def compactRecordWidth (m : ℕ) : ℕ := Nat.log 2 m + 1

def HasCompactEncoding (X : Type) [Fintype X] : Prop :=
  ∃ encode : X → Fin (2 ^ compactRecordWidth (Fintype.card X)), Function.Injective encode

noncomputable def orbitFourierMatrix (G : Type*) [AddCommGroup G] [Fintype G] :
    Matrix (AddChar G ℂ) G ℂ := Qatlib.Concepts.WalshMoment.Forrelation.fourierMatrix G

noncomputable def orbitFourier (G : Type*) [AddCommGroup G] [Fintype G]
    (ψ : G → ℂ) : AddChar G ℂ → ℂ := Qatlib.Concepts.WalshMoment.Forrelation.fourier ψ

def OriginalClockWindow (N q : ℕ) : Prop :=
  ∃ t : ℕ, q = 2 ^ t ∧ N ^ 2 ≤ q ∧ q < 2 * N ^ 2

def OrderGoodEvent (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y : Fin M) : Prop :=
  (verifiedOrderDecode N M a y).1 = some (orderOf a)

noncomputable def orderGoodMass (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) : ℝ :=
  Finset.sum (Finset.univ.filter (fun y : Fin M => OrderGoodEvent N M a y))
    (fun y => (modularOrderLaw N M a hM).prob y)

def smallPrimes : Finset ℕ := (Finset.range 19).filter Nat.Prime

def smallPrimePowers (m : ℕ) : Finset ℕ :=
  (Finset.filter (fun p : ℕ × ℕ =>
      1 ≤ p.2 ∧ p.1 ^ p.2 ∣ m ∧ ¬ (p.1 * p.1 ^ p.2 ∣ m))
    (Finset.product smallPrimes (Finset.range (orderBitLength m + 1)))).image
    (fun p => p.1 ^ p.2)

def smallPrimePart (m : ℕ) : ℕ := Finset.prod (smallPrimePowers m) (fun _ => 1)

noncomputable def effectiveCrtCandidates (p : ℕ) (t : ℕ) (c' d' : Fin t → ℤ) : List ℕ :=
  ((Finset.range (p - 1)).filter fun r' =>
    ∀ i : Fin t, (d' i + ((r' : ℕ) : ℤ) * c' i) % (((p - 1 : ℕ) : ℤ)) = 0).toList

def OrderRepetitionBudget (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (t : ℕ) : Prop :=
  t * (orderGoodMass N M a hM)⁻¹ ≤ 480 * t

end Qatlib.Concepts.PeriodSampling.OrderRecovery
