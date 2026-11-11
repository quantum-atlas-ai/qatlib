/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Interfaces for noisy learning models

Defines Boolean registers, oracle-relative algorithm records, and the predicates `NBQP`, `BQP`,
and `NISQ`. It also provides finite learning trees, Pauli labels and noise scalars, and a
real-linear contractive `Channel` interface used by the later estimates. See
[CotlerGongKannan2025] for the surrounding analysis.

## Main statements

* `InRelClass`: The existence of an algorithm satisfying an admissibility predicate and
  `SolvesPromise`.
* `LayerTree`: A finite-depth tree of nonnegative, normalized transition kernels depending on
  the preceding outcomes.
* `Channel`: A real-linear map equipped with a proof that it contracts the norm.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults

open scoped BigOperators

/-- An `n`-bit register represented as a function from `Fin n` to `Bool`. -/
abbrev Reg (n : ℕ) : Type := Fin n → Bool

/-- Half the sum of absolute pointwise differences of two real-valued functions on a finite
type. -/
def tvDist {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- The predicate that `A` is contained in `B` and some element of `B` lies outside `A`. -/
def StrictSubset {α : Type*} (A B : Set α) : Prop :=
  A ⊆ B ∧ ∃ a, a ∈ B ∧ a ∉ A

/-- The predicate that `f n` is bounded by `c * (n + 1)^k` for fixed natural constants `c` and
`k`. -/
def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

/-- The predicate that `f n` is bounded by a fixed polynomial in `Nat.log 2 (n + 1) + 1`. -/
def IsPolylog (f : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, f n ≤ c * (Nat.log 2 (n + 1) + 1) ^ k

/-- The one-sided eventual bound `f n ≤ c * g n` for some positive real `c`. -/
def IsBigO (g f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → f n ≤ c * g n

/-- The one-sided eventual bound `c * g n ≤ f n` for some positive real `c`. -/
def IsBigOmega (g f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → c * g n ≤ f n

/-- The conjunction of `IsBigO g f` and `IsBigOmega g f`. -/
def IsTheta (g f : ℕ → ℝ) : Prop := IsBigO g f ∧ IsBigOmega g f

/-- A finite-width Boolean-register oracle with an evaluation function. -/
structure Oracle where

  width : ℕ

  eval : Reg width → Reg width

/-- The first `n` bits of a register of length `n + n`. -/
def firstHalf {n : ℕ} (x : Reg (n + n)) : Reg n :=
  fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n n)⟩

/-- The last `n` bits of a register of length `n + n`. -/
def secondHalf {n : ℕ} (x : Reg (n + n)) : Reg n :=
  fun i => x ⟨i.val + n, Nat.add_lt_add_right i.isLt n⟩

/-- The value of `f` on the first half when the second half is zero, and the zero register
otherwise. -/
def fLift {n : ℕ} (f : Reg n → Reg n) (x : Reg (n + n)) : Reg n :=
  fun i => if (∀ k, secondHalf x k = false) then f (firstHalf x) i else false

/-- A doubled-width oracle preserving the first half and XORing the second half with `fLift f
x`. -/
def liftedSimonOracle {n : ℕ} (f : Reg n → Reg n) : Oracle where
  width := n + n
  eval := fun x i =>
    if h : i.val < n then x i
    else Bool.xor (x i) (fLift f x ⟨i.val - n, by omega⟩)

/-- An oracle interface equipped with a shuffling proposition and a shadow oracle, indexed by
`n` and `d`. -/
structure EncodedShufflingOracle (n d : ℕ) extends Oracle where

  isShuffling : Prop

  shadow : Oracle

/-- An oracle-relative algorithm record containing qubit count, depth, noise, query count, and a
success-weight function. -/
structure RelAlgorithm (O : Oracle) where

  qubits : ℕ

  depth : ℕ → ℕ

  noise : ℝ

  queries : ℕ → ℕ

  successProb : List Bool → ℝ

/-- The predicate that the empty-transcript success weight is at least `2 / 3` when `yes` holds
and at most `1 / 3` when `no` holds. -/
def SolvesPromise {O : Oracle} (A : RelAlgorithm O) (yes no : Prop) : Prop :=
  (yes → (2 : ℝ) / 3 ≤ A.successProb []) ∧ (no → A.successProb [] ≤ (1 : ℝ) / 3)

/-- The existence of an algorithm satisfying an admissibility predicate and `SolvesPromise`. -/
def InRelClass {O : Oracle} (admissible : RelAlgorithm O → Prop)
    (yes no : Prop) : Prop :=
  ∃ A : RelAlgorithm O, admissible A ∧ SolvesPromise A yes no

/-- The existence of a promise-solving algorithm with noise strictly between zero and one and
polynomially bounded queries. -/
def NBQP (O : Oracle) (yes no : Prop) : Prop :=
  InRelClass (O := O)
    (fun A => 0 < A.noise ∧ A.noise < 1 ∧ IsPolynomial A.queries) yes no

/-- The existence of a promise-solving algorithm with polynomially bounded queries. -/
def BQP (O : Oracle) (yes no : Prop) : Prop :=
  InRelClass (O := O) (fun A => IsPolynomial A.queries) yes no

/-- The existence of a promise-solving algorithm with noise strictly between zero and one,
polynomially bounded queries, and polylogarithmically bounded depth. -/
def NISQ (O : Oracle) (yes no : Prop) : Prop :=
  InRelClass (O := O)
    (fun A => 0 < A.noise ∧ A.noise < 1 ∧ IsPolynomial A.queries ∧
      IsPolylog A.depth) yes no

/-- The predicate that every promise pair in `C` is in `D` and some promise pair is in `D` but
outside `C`. -/
def ClassStrict (C D : Prop → Prop → Prop) : Prop :=
  (∀ yes no, C yes no → D yes no) ∧ ∃ yes no, D yes no ∧ ¬ C yes no

/-- A finite-depth tree of nonnegative, normalized transition kernels depending on the preceding
outcomes. -/
structure LayerTree (A : Type*) [Fintype A] (N : ℕ) where

  kernel : (i : Fin N) → (Fin i.val → A) → A → ℝ

  kernel_nonneg : ∀ (i : Fin N) (u : Fin i.val → A) (a : A), 0 ≤ kernel i u a

  kernel_sum_one : ∀ (i : Fin N) (u : Fin i.val → A), ∑ a, kernel i u a = 1

/-- The restriction of a path to the indices preceding `i`. -/
def LayerTree.pathPrefix {A : Type*} [Fintype A] {N : ℕ} (x : Fin N → A) (i : Fin N) :
    Fin i.val → A :=
  fun j => x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt i.isLt)⟩

/-- The probability weight of a path, given by the product of its successive conditional kernel
weights. -/
def LayerTree.pathProb {A : Type*} [Fintype A] {N : ℕ} (T : LayerTree A N)
    (x : Fin N → A) : ℝ :=
  ∏ i : Fin N, T.kernel i (pathPrefix x i) (x i)

/-- Half the sum of absolute differences of the two trees' path probabilities. -/
def leafTV {A : Type*} [Fintype A] {N : ℕ} (T T' : LayerTree A N) : ℝ :=
  (∑ x : Fin N → A, |T.pathProb x - T'.pathProb x|) / 2

/-- The predicate that the register function `f` is injective. -/
def IsInjective {n : ℕ} (f : Reg n → Reg n) : Prop := Function.Injective f

/-- The existence of a nonzero XOR period preserving the values of `f`. -/
def HasPeriod {n : ℕ} (f : Reg n → Reg n) : Prop :=
  ∃ s : Reg n, s ≠ (fun _ => false) ∧ ∀ x, f (fun i => Bool.xor (x i) (s i)) = f x

/-- The four Pauli labels represented by `Fin 4`. -/
abbrev PauliChar : Type := Fin 4

/-- An `n`-fold Pauli label represented as a function from `Fin n` to `PauliChar`. -/
abbrev Pauli (n : ℕ) : Type := Fin n → PauliChar

/-- The number of nonzero entries in a Pauli label. -/
def pauliWeight {n : ℕ} (P : Pauli n) : ℕ :=
  (Finset.univ.filter (fun i => P i ≠ 0)).card

/-- The unchanged Pauli label; the noise parameter does not alter the label in this definition. -/
def depolarizePauli {n : ℕ} (_lam : ℝ) (P : Pauli n) : Pauli n := P

/-- The scalar noise factor `(1 - lam) ^ pauliWeight P`. -/
def depolScale {n : ℕ} (lam : ℝ) (P : Pauli n) : ℝ := (1 - lam) ^ pauliWeight P

/-- The noise polynomial `1 - lam + lam² / 2`. -/
def fLambda (lam : ℝ) : ℝ := 1 - lam + lam ^ 2 / 2

/-- The two-copy sample-cost expression `n * (1 - lam)^(-4n)`. -/
def twoCopySampleCost (n : ℕ) (lam : ℝ) : ℝ := (n : ℝ) * (1 - lam) ^ (-(4 * (n : ℝ)))

/-- The logarithmic ratio `n * log(2 / fLambda lam) / (log n - 4n * log(1 - lam))`. -/
def corollary27Exponent (n : ℕ) (lam : ℝ) : ℝ :=
  (n : ℝ) * Real.log (2 / fLambda lam) /
    (Real.log (n : ℝ) - 4 * (n : ℝ) * Real.log (1 - lam))

/-- A real-linear map equipped with a proof that it contracts the norm. -/
structure Channel (E : Type*) [NormedAddCommGroup E] [Module ℝ E] where

  toFun : E → E

  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y

  map_smul' : ∀ (c : ℝ) x, toFun (c • x) = c • toFun x

  contract : ∀ x, ‖toFun x‖ ≤ ‖x‖

/-- The natural-number iterate of a channel, with the zeroth iterate equal to the identity. -/
def Channel.iterate {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (Φ : Channel E) : ℕ → E → E
  | 0, x => x
  | (N + 1), x => Φ.toFun (iterate Φ N x)

/-- A channel preserves subtraction. -/
theorem Channel.map_sub {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (Φ : Channel E) (x y : E) : Φ.toFun (x - y) = Φ.toFun x - Φ.toFun y := by
  have hneg : Φ.toFun (-y) = -Φ.toFun y := by
    have := Φ.map_smul' (-1) y
    rwa [neg_one_smul, neg_one_smul] at this
  rw [sub_eq_add_neg, Φ.map_add', hneg, sub_eq_add_neg]

end Qatlib.Papers.NoisyLearn26.MainResults
