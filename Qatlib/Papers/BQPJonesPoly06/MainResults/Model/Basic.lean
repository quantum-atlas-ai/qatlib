/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Zify

/-!
# Promise models for Jones approximation reductions

This module defines braid words, Jones-value functions, scaling factors, and promise problems
used in the Jones approximation development. `PolyReduction` records a map with a polynomial
output-size bound and preservation of legal yes and no instances.

The predicates `BQPHard`, `InBQP`, and `SharpPHard` are defined by reductions between these
explicit model problems. The module also provides Boolean CNF evaluation and
satisfying-assignment counts for the counting-gap source problem. See [AharonovArad2011].

## Main statements

* `PolyReduction`: maps promise instances with a polynomial size bound.
* `jonesPromise`: the additive-scale Jones gap promise.
* `mulJonesPromise`: the multiplicative-scale Jones gap promise.
* `sharpGapProblem`: the satisfying-assignment gap source.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

open Complex

/-- A signed braid generator, represented by a natural generator index and a Boolean sign. -/
abbrev SignedGen := ℕ × Bool

/-- A braid word on `n` strands, stored as a list of signed generators without a bundled
legality condition. -/
structure BraidWord (n : ℕ) where

  crossings : List SignedGen

namespace BraidWord

/-- The number of crossings in a braid word, given by its list length. -/
def numCrossings {n : ℕ} (b : BraidWord n) : ℕ := b.crossings.length

/-- Every crossing generator index `g.1` satisfies `g.1 + 1 < n`. -/
def Legal {n : ℕ} (b : BraidWord n) : Prop := ∀ g ∈ b.crossings, g.1 + 1 < n

end BraidWord

/-- A plat-closure datum consisting of its underlying braid word. -/
structure PlatClosure (n : ℕ) where

  braid : BraidWord n

/-- A complex-valued function on braid words with `n` strands. -/
abbrev JonesValue (n : ℕ) := BraidWord n → ℂ

/-- The complex number `exp (2 * Real.pi * Complex.I / k)`. -/
noncomputable def rootOfUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / k)

/-- The real scale `(2 * cos (Real.pi / k)) ^ (n / 2 - 1)`, using natural-number division and
subtraction in the exponent. -/
noncomputable def deltaScale (k n : ℕ) : ℝ :=
  (2 * Real.cos (Real.pi / k)) ^ (n / 2 - 1)

/-- The Jones scale `deltaScale k n` is positive when `2 < k`. -/
theorem deltaScale_pos {k n : ℕ} (hk : 2 < k) : 0 < deltaScale k n := by
  unfold deltaScale
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.lt_trans (by norm_num) hk
  have harg : Real.pi / k < Real.pi / 2 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast hk
  have hargpos : (0 : ℝ) < Real.pi / k := div_pos Real.pi_pos hk0
  have hcos : 0 < Real.cos (Real.pi / k) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], harg⟩
  exact pow_pos (by linarith) _

/-- A promise problem with an input-size function, a legality predicate, and yes and no
predicates disjoint on legal inputs. -/
structure PromisedProblem (α : Type*) where

  size : α → ℕ

  legal : α → Prop

  yes : α → Prop

  no : α → Prop

  disjoint : ∀ a, legal a → ¬ (yes a ∧ no a)

/-- A map between promise problems with a polynomial output-size bound that preserves legal yes
and no instances. -/
structure PolyReduction {α β : Type*} (P : PromisedProblem α) (Q : PromisedProblem β) where

  map : α → β

  degree : ℕ

  constant : ℕ

  size_bound : ∀ a, Q.size (map a) ≤ constant * (P.size a + 1) ^ degree

  maps_yes : ∀ a, P.legal a → P.yes a → Q.legal (map a) ∧ Q.yes (map a)

  maps_no : ∀ a, P.legal a → P.no a → Q.legal (map a) ∧ Q.no (map a)

/-- A circuit-gap datum recording qubit count, gate count, and a real amplitude. -/
structure CircuitGap where

  qubits : ℕ

  gateCount : ℕ

  amplitude : ℝ

/-- The size of a circuit-gap datum is its qubit count plus its gate count. -/
def CircuitGap.size (C : CircuitGap) : ℕ := C.qubits + C.gateCount

/-- The circuit-gap promise with all inputs legal, yes amplitudes at most `lo`, and no
amplitudes at least `hi`, where `lo < hi`. -/
def circuitGapProblemWith (lo hi : ℝ) (h : lo < hi) : PromisedProblem CircuitGap where
  size := CircuitGap.size
  legal := fun _ => True
  yes := fun C => C.amplitude ≤ lo
  no := fun C => hi ≤ C.amplitude
  disjoint := by
    intro C _ hc
    linarith [hc.1, hc.2]

/-- The circuit-gap promise with yes threshold one third and no threshold two thirds. -/
noncomputable def circuitGapProblem : PromisedProblem CircuitGap :=
  circuitGapProblemWith (1 / 3) (2 / 3) (by norm_num)

/-- The circuit-gap promise with yes threshold one twentieth and no threshold nineteen
twentieths. -/
noncomputable def circuitGapAmplified : PromisedProblem CircuitGap :=
  circuitGapProblemWith (1 / 20) (19 / 20) (by norm_num)

/-- The amplified circuit-gap problem has a `PolyReduction` to `P`. -/
def BQPHard {α : Type*} (P : PromisedProblem α) : Prop :=
  Nonempty (PolyReduction circuitGapAmplified P)

/-- The promise problem `P` has a `PolyReduction` to the standard circuit-gap problem. -/
def InBQP {α : Type*} (P : PromisedProblem α) : Prop :=
  Nonempty (PolyReduction P circuitGapProblem)

/-- The conjunction of the model predicates `BQPHard P` and `InBQP P`. -/
def BQPComplete {α : Type*} (P : PromisedProblem α) : Prop :=
  BQPHard P ∧ InBQP P

/-- The function `f` is bounded by `C * (n + 1) ^ d` for some natural constants `C` and `d`. -/
def PolyBound (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, f n ≤ C * (n + 1) ^ d

/-- The Jones promise with positive scale `Δ`, crossing-count size, yes norms at most `Δ / 10`,
and no norms at least `9 * Δ / 10`. -/
noncomputable def jonesPromise (n : ℕ) (V : JonesValue n) (Δ : ℝ) :
    PromisedProblem (BraidWord n) where
  size := fun b => b.numCrossings
  legal := fun _ => 0 < Δ
  yes := fun b => ‖V b‖ ≤ Δ / 10
  no := fun b => 9 * Δ / 10 ≤ ‖V b‖
  disjoint := by
    intro b hΔ h
    have h1 := h.1
    have h2 := h.2
    nlinarith [norm_nonneg (V b), hΔ]

/-- A multiplicative Jones instance consisting of a braid word and a real scale. -/
structure MulInstance (n : ℕ) where

  braid : BraidWord n

  scale : ℝ

/-- The size of a multiplicative Jones instance is the crossing count of its braid. -/
def MulInstance.size {n : ℕ} (a : MulInstance n) : ℕ := a.braid.numCrossings

/-- The multiplicative Jones promise with legal conditions `1 < c` and positive instance scale,
separating norms at most the scale from norms at least `c` times the scale. -/
noncomputable def mulJonesPromise (n : ℕ) (V : JonesValue n) (c : ℝ) :
    PromisedProblem (MulInstance n) where
  size := MulInstance.size
  legal := fun a => 1 < c ∧ 0 < a.scale
  yes := fun a => ‖V a.braid‖ ≤ a.scale
  no := fun a => c * a.scale ≤ ‖V a.braid‖
  disjoint := by
    intro a hlegal h
    have hc : 1 < c := hlegal.1
    have hts : 0 < a.scale := hlegal.2
    have h1 := h.1
    have h2 := h.2
    nlinarith

/-- A Boolean CNF formula represented by a variable count and a list of clauses of indexed
signed literals. -/
structure CNF where

  vars : ℕ

  clauses : List (List (ℕ × Bool))

/-- Evaluate a signed literal, using the assignment directly for sign true and its negation for
sign false. -/
def evalLit (σ : ℕ → Bool) (l : ℕ × Bool) : Bool :=
  match l.2 with
  | true => σ l.1
  | false => !σ l.1

/-- Evaluate a clause as the disjunction of its literal values. -/
def clauseSat (σ : ℕ → Bool) (cl : List (ℕ × Bool)) : Bool :=
  cl.any (evalLit σ)

/-- Evaluate a CNF formula as the conjunction of its clause values. -/
def cnfSat (σ : ℕ → Bool) (φ : CNF) : Bool :=
  φ.clauses.all (clauseSat σ)

/-- Count satisfying assignments on the declared finite variable set, extending each assignment
by false outside that set. -/
noncomputable def satCount (φ : CNF) : ℕ :=
  (Finset.univ.filter (fun σ : Fin φ.vars → Bool =>
    cnfSat (fun i => if h : i < φ.vars then σ ⟨i, h⟩ else false) φ = true)).card

/-- The size of a CNF formula is its variable count plus its number of clauses. -/
def CNF.size (φ : CNF) : ℕ := φ.vars + φ.clauses.length

/-- The legal-variable CNF promise separating satisfying fractions at least two thirds from
fractions at most one third. -/
noncomputable def sharpGapProblem : PromisedProblem CNF where
  size := CNF.size
  legal := fun φ => ∀ l ∈ φ.clauses.flatten, l.1 < φ.vars
  yes := fun φ => 2 ^ φ.vars * 2 ≤ 3 * satCount φ
  no := fun φ => 3 * satCount φ ≤ 2 ^ φ.vars
  disjoint := by
    intro φ _ h
    have hpow : 0 < 2 ^ φ.vars := pow_pos (by norm_num) _
    linarith [h.1, h.2]

/-- The counting-gap source problem `sharpGapProblem` has a `PolyReduction` to `P`. -/
def SharpPHard {α : Type*} (P : PromisedProblem α) : Prop :=
  Nonempty (PolyReduction sharpGapProblem P)

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
