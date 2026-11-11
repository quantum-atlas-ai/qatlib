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

/-!
# Definitions for order-based factoring

This module collects data and predicates for preprocessing, order-finding attempts, factor
extraction, resource accounting, and recursive factor trees. These definitions organize the
classical and quantum components of the factoring framework in [Shor1997].

It also specifies finite-register encodings, measurement probabilities under computation
embeddings, orbit Fourier transforms, and clock and repetition conditions. Resource records and
correctness predicates are stated separately so that later results can attach guarantees to the
recorded data.

## Main statements

* `preprocess`: checks for an even divisor and a perfect-power divisor before returning a
  residual case.
* `AttemptLedger` and `AttemptOutcome`: resource records and possible outcomes of a factoring
  attempt.
* `FactorTree.complete`: the leaf-product and primality condition for a factor tree.
* `OrderGoodEvent` and `orderGoodMass`: exact-order decoding success and its probability mass.

## References

* [Shor, 1997][Shor1997]
-/

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

/-- Natural powers preserve an inequality between their bases. -/
theorem pow_le_pow_of_le_base (a b n : ℕ) (h : a ≤ b) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ]; exact Nat.mul_le_mul ih h

/-- A natural number at least one is at most any of its positive natural powers. -/
theorem pow_ge_self (a n : ℕ) (ha : 1 ≤ a) (hn : 1 ≤ n) : a ≤ a ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    · rw [h, pow_succ, pow_zero, one_mul]
    · rw [pow_succ]
      have h1 : a ≤ a ^ n := ih (by omega)
      exact h1.trans (by simpa using! Nat.mul_le_mul (le_refl _) (by omega : 1 ≤ a))

/-- The bit-length parameter `Nat.log 2 N + 1` used for order-finding resource bounds. -/
def orderBitLength (N : ℕ) : ℕ := Nat.log 2 N + 1

/-- The resource expression `c * (orderBitLength N + 1) ^ d`. -/
def polyLogBound (c d N : ℕ) : ℕ := c * (orderBitLength N + 1) ^ d

/-- The coefficients `c` and `d` are positive and the corresponding polynomial bit-length
expression bounds `orderBitLength N`. -/
def PolyLogDominates (c d N : ℕ) : Prop :=
  0 < c ∧ 0 < d ∧ orderBitLength N ≤ polyLogBound c d N

/-- The natural numbers below `N + 2` whose `e`th powers exceed `N`. -/
def powExceedSet (e N : ℕ) : Finset ℕ :=
  (Finset.filter (fun r => r ^ e > N) (Finset.range (N + 2)))

/-- For positive exponent `e`, provides a natural number whose `e`th power exceeds `N`. -/
def powExceedWitness (e N : ℕ) (he : 1 ≤ e) : ∃ r, r ^ e > N :=
  ⟨N + 1, by
    have hpow := pow_ge_self (N + 1) e (by omega) he
    omega⟩

/-- For nonzero `e`, one less than the least natural number whose `e`th power exceeds `N`; for
`e = 0`, returns zero. -/
def intRoot (e N : ℕ) : ℕ :=
  if h : e = 0 then 0 else Nat.find (powExceedWitness e N (by omega)) - 1

/-- The exponents from two through `orderBitLength N` for which `intRoot e N` is at least two
and its `e`th power equals `N`. -/
def perfectPowerCandidates (N : ℕ) : Finset ℕ :=
  (Finset.filter (fun e => 2 ≤ e ∧ 2 ≤ intRoot e N ∧ intRoot e N ^ e = N)
    (Finset.range (orderBitLength N + 1)))

/-- The integer roots associated with the candidate perfect-power exponents. -/
def perfectPowerDivisors (N : ℕ) : Finset ℕ :=
  (perfectPowerCandidates N).image (fun e => intRoot e N)

/-- The least candidate perfect-power exponent, or `none` if there are no candidates. -/
def perfectPowerExponent (N : ℕ) : Option ℕ :=
  let s := perfectPowerCandidates N
  if h : s.card = 0 then none else some (s.min' (Finset.card_ne_zero.mp (by omega)))

/-- The integer root corresponding to the selected perfect-power exponent, when one exists. -/
def perfectPowerDivisor (N : ℕ) : Option ℕ :=
  (perfectPowerExponent N).map (fun e => intRoot e N)

/-- Returns two when `N ≥ 4` and `N` is divisible by two, and returns `none` otherwise. -/
def evenDivisor (N : ℕ) : Option ℕ :=
  if 4 ≤ N ∧ 2 ∣ N then some 2 else none

/-- A preprocessing outcome recording an even divisor, a perfect-power divisor, or a residual
case. -/
inductive PreprocessVerdict where

  | even (d : ℕ)

  | perfectPower (d : ℕ)

  | residue
  deriving DecidableEq, Repr

/-- Checks for an even divisor first, then a perfect-power divisor, and otherwise returns the
residual verdict. -/
def preprocess (N : ℕ) : PreprocessVerdict :=
  match evenDivisor N with
  | some d => .even d
  | none =>
    match perfectPowerDivisor N with
    | some d => .perfectPower d
    | none => .residue

/-- The preprocessing cost expression `orderBitLength N * (orderBitLength N + 1)²`. -/
def preprocessBitCost (N : ℕ) : ℕ :=
  orderBitLength N * (orderBitLength N + 1) * (orderBitLength N + 1)

/-- The assertion that `d` is a nontrivial divisor of `N`. -/
def CompositeCertificate (N d : ℕ) : Prop := 1 < d ∧ d < N ∧ d ∣ N

/-- The Fermat-type condition `a ^ (N - 1) = 1` for a modular unit. -/
def PrimeDirectionWitness (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Prop :=
  a ^ (N - 1) = 1

/-- The modular multiplication cost expression `2 * b² + b`. -/
def schoolbookMulModCost (b : ℕ) : ℕ := 2 * b * b + b

/-- The local Fourier-transform gate-count expression `n + n * (n - 1) / 2 + n / 2`. -/
def localQftGateCount (n : ℕ) : ℕ := n + n * (n - 1) / 2 + n / 2

/-- The local Fourier-transform space parameter, equal to the register width `n`. -/
def localQftSpaceCost (n : ℕ) : ℕ := n

/-- The Euclidean-algorithm step-bound expression `2 * b + 1`. -/
def euclidStepBound (b : ℕ) : ℕ := 2 * b + 1

/-- The cost assigned to one Euclidean-algorithm step, equal to `schoolbookMulModCost b`. -/
def euclidStepCost (b : ℕ) : ℕ := schoolbookMulModCost b

/-- The product of the Euclidean step bound and the assigned step cost. -/
def euclidBitCost (b : ℕ) : ℕ := euclidStepBound b * euclidStepCost b

/-- The Euclidean-algorithm space expression `2 * b`. -/
def euclidSpaceCost (b : ℕ) : ℕ := 2 * b

/-- A record of bit work, oracle queries, gates, and space for a factoring attempt. -/
structure AttemptLedger where

  bits : ℕ

  queries : ℕ

  gates : ℕ

  space : ℕ
  deriving DecidableEq, Repr

/-- Componentwise comparison of the four resource counters in two attempt ledgers. -/
def AttemptLedger.le (l₁ l₂ : AttemptLedger) : Prop :=
  l₁.bits ≤ l₂.bits ∧ l₁.queries ≤ l₂.queries ∧ l₁.gates ≤ l₂.gates ∧ l₁.space ≤ l₂.space

instance : LE AttemptLedger := ⟨fun l₁ l₂ => l₁.le l₂⟩

/-- The prescribed attempt ledger combining two Euclidean costs, two modular-order circuit
costs, and the stated register-space expression. -/
def attemptLedgerBound (N M k : ℕ) : AttemptLedger where
  bits := k + 2 * euclidBitCost (orderBitLength N)
  queries := 2 * (M * (M - 1) / 2)
  gates := 2 * (M * (M - 1) + 2)
  space := k + 2 * orderBitLength M + 2 * orderBitLength N

/-- The ledger assigning `k` units of bit work and space to a rejected attempt, with zero
queries and gates. -/
def rejectedLedger (k : ℕ) : AttemptLedger where
  bits := k
  queries := 0
  gates := 0
  space := k

/-- An attempt outcome consisting of rejection, a classical gcd sample, or a modular unit with
two quantum clock samples. -/
inductive AttemptOutcome (N M : ℕ) [NeZero N] where

  | rejected

  | classicalGcd (y : ZMod N)

  | quantumOrder (a : (ZMod N)ˣ) (yz : Fin M × Fin M)
  deriving DecidableEq

/-- Extracts an optional divisor from an attempt outcome using a checked gcd or the
continued-fraction pair decoder followed by `orderFactor`. -/
noncomputable def attemptOutcomeFactor (N M : ℕ) [NeZero N] :
    AttemptOutcome N M → Option ℕ
  | .rejected => none
  | .classicalGcd y =>
    let d := Nat.gcd N y.val
    if 1 < d ∧ d < N then some d else none
  | .quantumOrder a yz =>
    (cfPairLCMOrderDecode N M a yz).1.bind (orderFactor N a)

/-- The attempt at index `j` returns a factor and every preceding attempt returns no factor. -/
def firstSuccessAt {N M R : ℕ} [NeZero N] (ω : Fin R → AttemptOutcome N M) (j : Fin R) : Prop :=
  (attemptOutcomeFactor N M (ω j)).isSome ∧
    ∀ (i : ℕ) (hi : i < j.val),
      (attemptOutcomeFactor N M (ω ⟨i, Nat.lt_of_lt_of_le hi (Nat.le_of_lt j.isLt)⟩)).isSome = false

/-- A finite trajectory together with an index and proof that the indexed attempt is its first
successful factor output. -/
structure FirstSuccessReceipt (N M k R : ℕ) [NeZero N] where

  trajectory : Fin R → AttemptOutcome N M

  first : Fin R

  first_success : firstSuccessAt (N := N) (M := M) (R := R) trajectory first

/-- A natural divisor of `n` certified to lie strictly between one and `n`. -/
structure ProperDivisor (n : ℕ) where

  d : ℕ

  proof : 1 < d ∧ d < n ∧ d ∣ n

/-- A binary tree storing leaf values and costs, with internal nodes recording a number, a
proposed splitting divisor, and two subtrees. -/
inductive FactorTree where

  | leaf (p : ℕ) (cost : ℕ)

  | node (n d : ℕ) (cost : ℕ) (left right : FactorTree)
  deriving DecidableEq, Repr

/-- The value stored at a factor tree's root. -/
def FactorTree.root : FactorTree → ℕ
  | .leaf p _ => p
  | .node n _ _ _ _ => n

/-- The sum of the costs stored at all nodes and leaves of a factor tree. -/
def FactorTree.cost : FactorTree → ℕ
  | .leaf _ c => c
  | .node _ _ c l r => c + l.cost + r.cost

/-- The list of leaf values of a factor tree, ordered from left to right. -/
def FactorTree.leaves : FactorTree → List ℕ
  | .leaf p _ => [p]
  | .node _ _ _ l r => l.leaves ++ r.leaves

/-- The product of the leaf values of a factor tree. -/
def FactorTree.leavesProduct : FactorTree → ℕ
  | .leaf p _ => p
  | .node _ _ _ l r => l.leavesProduct * r.leavesProduct

/-- Builds a factor tree using a proper-divisor splitter and bounded recursion, returning a zero
leaf when fuel is exhausted. -/
def factorTreeOfFuel (split : ∀ n, Option (ProperDivisor n)) : ℕ → ℕ → FactorTree
  | 0, _ => .leaf 0 0
  | _ + 1, 0 => .leaf 0 0
  | fuel + 1, n + 1 =>
    Option.rec (motive := fun _ => FactorTree) (FactorTree.leaf (n + 1) 0)
      (fun pd => FactorTree.node (n + 1) pd.d 0
        (factorTreeOfFuel split fuel pd.d)
        (factorTreeOfFuel split fuel ((n + 1) / pd.d)))
      (split (n + 1))

/-- Builds a factor tree for `n` with initial recursion fuel `n`. -/
def factorTreeOf (split : ∀ n, Option (ProperDivisor n)) (n : ℕ) : FactorTree :=
  factorTreeOfFuel split n n

/-- The leaf product equals the root value and every leaf value is at most one or prime. -/
def FactorTree.complete (t : FactorTree) : Prop :=
  t.leavesProduct = t.root ∧ ∀ p ∈ t.leaves, p ≤ 1 ∨ Nat.Prime p

/-- At an internal node, the recorded divisor is returned by the splitter and the two child
roots equal that divisor and its quotient; leaves satisfy the predicate automatically. -/
def FactorTree.splitSound (split : ∀ n, Option (ProperDivisor n)) :
    FactorTree → Prop
  | .leaf _ _ => True
  | .node n d _ l r =>
    ∃ pd : ProperDivisor n, split n = some pd ∧
      pd.d = d ∧ l.root = d ∧ r.root = n / d

variable {Ω H O : Type} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
  [Fintype O] [DecidableEq O]

/-- The matrix condition `Vᴴ * V = 1` for a computation embedding. -/
def ComputationIsometry (V : Matrix H Ω ℂ) : Prop := Vᴴ * V = 1

/-- The completeness condition that the sum of `T ω` adjoint times `T ω` is the identity. -/
def MeasurementOperatorFamily (T : O → Matrix Ω Ω ℂ) : Prop :=
  ∑ ω, (T ω)ᴴ * (T ω) = 1

/-- The sum of squared output amplitudes after applying measurement operator `T ω` to a
workspace state. -/
noncomputable def workspaceMass (T : O → Matrix Ω Ω ℂ) (ψ : QState Ω) (ω : O) : ℝ :=
  ∑ i, ‖((T ω) *ᵥ ψ) i‖ ^ 2

/-- The sum of squared amplitudes after applying the transported measurement operator `V * T ω *
Vᴴ` to a compiled state. -/
noncomputable def compiledMass (V : Matrix H Ω ℂ) (T : O → Matrix Ω Ω ℂ)
    (φ : QState H) (ω : O) : ℝ :=
  ∑ i, ‖((V * (T ω) * Vᴴ) *ᵥ φ) i‖ ^ 2

/-- The record-width parameter `Nat.log 2 m + 1`. -/
def compactRecordWidth (m : ℕ) : ℕ := Nat.log 2 m + 1

/-- A finite type has an injective encoding into bit strings represented by `Fin (2 ^
compactRecordWidth (Fintype.card X))`. -/
def HasCompactEncoding (X : Type) [Fintype X] : Prop :=
  ∃ encode : X → Fin (2 ^ compactRecordWidth (Fintype.card X)), Function.Injective encode

/-- The finite additive-group Fourier matrix with rows indexed by complex additive characters. -/
noncomputable def orbitFourierMatrix (G : Type*) [AddCommGroup G] [Fintype G] :
    Matrix (AddChar G ℂ) G ℂ := Qatlib.Concepts.WalshMoment.Forrelation.fourierMatrix G

/-- The finite additive-group Fourier transform of a complex-valued state. -/
noncomputable def orbitFourier (G : Type*) [AddCommGroup G] [Fintype G]
    (ψ : G → ℂ) : AddChar G ℂ → ℂ := Qatlib.Concepts.WalshMoment.Forrelation.fourier ψ

/-- The clock size is a power of two lying in the interval `[N², 2 * N²)`. -/
def OriginalClockWindow (N q : ℕ) : Prop :=
  ∃ t : ℕ, q = 2 ^ t ∧ N ^ 2 ≤ q ∧ q < 2 * N ^ 2

/-- The verified order decoder returns the exact multiplicative order for the given clock
sample. -/
def OrderGoodEvent (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y : Fin M) : Prop :=
  (verifiedOrderDecode N M a y).1 = some (orderOf a)

/-- The total `modularOrderLaw` probability of clock samples satisfying `OrderGoodEvent`. -/
noncomputable def orderGoodMass (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) : ℝ :=
  Finset.sum (Finset.univ.filter (fun y : Fin M => OrderGoodEvent N M a y))
    (fun y => (modularOrderLaw N M a hM).prob y)

/-- The finite set of prime natural numbers below nineteen. -/
def smallPrimes : Finset ℕ := (Finset.range 19).filter Nat.Prime

/-- The powers of primes below nineteen that divide `m` with exact positive exponent within the
specified bit-length range. -/
def smallPrimePowers (m : ℕ) : Finset ℕ :=
  (Finset.filter (fun p : ℕ × ℕ =>
      1 ≤ p.2 ∧ p.1 ^ p.2 ∣ m ∧ ¬ (p.1 * p.1 ^ p.2 ∣ m))
    (Finset.product smallPrimes (Finset.range (orderBitLength m + 1)))).image
    (fun p => p.1 ^ p.2)

/-- The product of the constant value one over `smallPrimePowers m`. -/
def smallPrimePart (m : ℕ) : ℕ := Finset.prod (smallPrimePowers m) (fun _ => 1)

/-- The residues below `p - 1` satisfying all the specified linear congruences modulo `p - 1`. -/
noncomputable def effectiveCrtCandidates (p : ℕ) (t : ℕ) (c' d' : Fin t → ℤ) : List ℕ :=
  ((Finset.range (p - 1)).filter fun r' =>
    ∀ i : Fin t, (d' i + ((r' : ℕ) : ℤ) * c' i) % (((p - 1 : ℕ) : ℤ)) = 0).toList

/-- The inverse-success-mass repetition expression `t * (orderGoodMass N M a hM)⁻¹` is at most
`480 * t`. -/
def OrderRepetitionBudget (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (t : ℕ) : Prop :=
  t * (orderGoodMass N M a hM)⁻¹ ≤ 480 * t

end Qatlib.Concepts.PeriodSampling.OrderRecovery
