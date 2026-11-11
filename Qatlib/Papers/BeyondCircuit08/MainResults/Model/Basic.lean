/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Symbol-string model for Fibonacci braid generators

The types `QStr`, `StarStarBasis`, `StarPBasis`, `PStarBasis`, and `PPBasis` model symbol
strings with no adjacent stars and specified endpoint symbols. The coefficients `fiba` through
`fibe` and the entry rule `fibRepEntry` define the four blocks of the Fibonacci braid generators
used in [Jordan2008].

The module also defines signed braid words and their evaluation, the matrix expression
`normalizeGen`, and the predicates `IsSUOn` and `PhaseDenseOn` for special unitarity and
approximation up to a scalar phase.

## Main statements

* `fibRepEntry`: the local entry rule for a Fibonacci braid generator.
* `starStarGen`, `starPGen`, `pStarGen`, and `ppGen`: generator matrices for the four endpoint
  sectors.
* `PhaseDenseOn`: approximation of every special unitary to any positive tolerance after a
  scalar phase adjustment.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Model

/-- Boolean symbols, with `true` representing a star and `false` representing the other symbol. -/
abbrev Symbol := Bool

/-- The Boolean test for the existence of two consecutive star symbols in a finite string. -/
def hasAdjacentStar {L : ℕ} (s : Fin L → Symbol) : Bool :=
  (List.range L).any fun i =>
    if h : i + 1 < L then s ⟨i, Nat.lt_of_succ_lt h⟩ && s ⟨i + 1, h⟩ else false

/-- The type of symbol strings of length `L` with no adjacent stars. -/
def QStr (L : ℕ) : Type := {s : Fin L → Symbol // hasAdjacentStar s = false}

instance (L : ℕ) : Fintype (QStr L) := by
  unfold QStr; infer_instance

instance (L : ℕ) : DecidableEq (QStr L) := by
  unfold QStr; infer_instance

/-- The endpoint condition that both the first and last symbols are stars. -/
def IsStarStar {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = true

/-- The endpoint condition that the first symbol is a star and the last is the nonstar symbol. -/
def IsStarP {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = false

/-- The endpoint condition that the first symbol is the nonstar symbol and the last is a star. -/
def IsPStar {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = false ∧ s ⟨n, Nat.lt_succ_self n⟩ = true

/-- The endpoint condition that both the first and last symbols are nonstar symbols. -/
def IsPP {n : ℕ} (s : Fin (n + 1) → Symbol) : Prop :=
  s ⟨0, Nat.succ_pos n⟩ = false ∧ s ⟨n, Nat.lt_succ_self n⟩ = false

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsStarStar (n := n) s) :=
  fun s => by unfold IsStarStar; infer_instance

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsStarP (n := n) s) :=
  fun s => by unfold IsStarP; infer_instance

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsPStar (n := n) s) :=
  fun s => by unfold IsPStar; infer_instance

instance (n : ℕ) : DecidablePred (fun s : Fin (n + 1) → Symbol => IsPP (n := n) s) :=
  fun s => by unfold IsPP; infer_instance

/-- The type of admissible strings of length `n + 1` whose two endpoints are stars. -/
def StarStarBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsStarStar (n := n) s.1}

/-- The type of admissible strings of length `n + 1` with a star at the first endpoint and a
nonstar at the last. -/
def StarPBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsStarP (n := n) s.1}

/-- The type of admissible strings of length `n + 1` with a nonstar at the first endpoint and a
star at the last. -/
def PStarBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsPStar (n := n) s.1}

/-- The type of admissible strings of length `n + 1` whose two endpoints are nonstar symbols. -/
def PPBasis (n : ℕ) : Type :=
  {s : QStr (n + 1) // IsPP (n := n) s.1}

instance (n : ℕ) : Fintype (StarStarBasis n) := by unfold StarStarBasis; infer_instance
instance (n : ℕ) : DecidableEq (StarStarBasis n) := by unfold StarStarBasis; infer_instance
instance (n : ℕ) : Fintype (StarPBasis n) := by unfold StarPBasis; infer_instance
instance (n : ℕ) : DecidableEq (StarPBasis n) := by unfold StarPBasis; infer_instance
instance (n : ℕ) : Fintype (PStarBasis n) := by unfold PStarBasis; infer_instance
instance (n : ℕ) : DecidableEq (PStarBasis n) := by unfold PStarBasis; infer_instance
instance (n : ℕ) : Fintype (PPBasis n) := by unfold PPBasis; infer_instance
instance (n : ℕ) : DecidableEq (PPBasis n) := by unfold PPBasis; infer_instance

/-- The reciprocal golden ratio `2 / (1 + √5)`. -/
def goldenTau : ℝ := 2 / (1 + Real.sqrt 5)

/-- The complex phase `exp (-3 * π * i / 5)` used in the Fibonacci representation. -/
def fibA : ℂ := Complex.exp ((-(3 * Real.pi / 5) : ℝ) * Complex.I)

/-- The Fibonacci coefficient `-(fibA ^ 4)`. -/
def fiba : ℂ := -(fibA ^ 4)

/-- The Fibonacci coefficient `fibA ^ 8`. -/
def fibb : ℂ := fibA ^ 8

/-- The Fibonacci coefficient `fibA ^ 8 * goldenTau ^ 2 - fibA ^ 4 * goldenTau`, with real
quantities cast to complex numbers. -/
def fibc : ℂ := fibA ^ 8 * (goldenTau : ℂ) ^ 2 - fibA ^ 4 * (goldenTau : ℂ)

/-- The complex cast of `√goldenTau * goldenTau`, used for the three-halves power in the
Fibonacci coefficients. -/
def tauThreeHalves : ℂ := ((Real.sqrt goldenTau : ℝ) : ℂ) * (goldenTau : ℂ)

/-- The Fibonacci coefficient `(fibA ^ 8 + fibA ^ 4) * tauThreeHalves`. -/
def fibd : ℂ := fibA ^ 8 * tauThreeHalves + fibA ^ 4 * tauThreeHalves

/-- The Fibonacci coefficient `fibA ^ 8 * goldenTau - fibA ^ 4 * goldenTau ^ 2`, with real
quantities cast to complex numbers. -/
def fibe : ℂ := fibA ^ 8 * (goldenTau : ℂ) - fibA ^ 4 * (goldenTau : ℂ) ^ 2

/-- The entry rule for generator `c`, using the three local symbols of the input string; nonzero
off-diagonal entries can occur only when the middle symbol is flipped. -/
def fibRepEntry (n : ℕ) (c : Fin (n - 1)) (t s : Fin (n + 1) → Symbol) : ℂ :=
  let mid : Fin (n + 1) := ⟨c.1 + 1, by omega⟩
  let lv : Symbol := s ⟨c.1, by omega⟩
  let rv : Symbol := s ⟨c.1 + 2, by omega⟩
  let mv : Symbol := s mid
  if t = s then
    (if lv = false ∧ rv = false then (if mv = true then fibc else fibe)
     else if lv = true ∧ rv = true then fibb else fiba)
  else if t = Function.update s mid (!mv) then
    (if lv = false ∧ rv = false then fibd else 0)
  else 0

/-- The matrix obtained by evaluating `fibRepEntry` on the strings associated with the row and
column indices of `B`. -/
def blockGen {n : ℕ} (B : Type) [Fintype B] [DecidableEq B]
    (toFun : B → Fin (n + 1) → Symbol) (c : Fin (n - 1)) : Matrix B B ℂ :=
  fun t s => fibRepEntry n c (toFun t) (toFun s)

/-- The Fibonacci generator matrix indexed by admissible strings with two star endpoints. -/
def starStarGen (n : ℕ) (c : Fin (n - 1)) : Matrix (StarStarBasis n) (StarStarBasis n) ℂ :=
  blockGen (StarStarBasis n) (fun s => s.1.1) c

/-- The Fibonacci generator matrix indexed by admissible strings with a star first endpoint and
a nonstar last endpoint. -/
def starPGen (n : ℕ) (c : Fin (n - 1)) : Matrix (StarPBasis n) (StarPBasis n) ℂ :=
  blockGen (StarPBasis n) (fun s => s.1.1) c

/-- The Fibonacci generator matrix indexed by admissible strings with a nonstar first endpoint
and a star last endpoint. -/
def pStarGen (n : ℕ) (c : Fin (n - 1)) : Matrix (PStarBasis n) (PStarBasis n) ℂ :=
  blockGen (PStarBasis n) (fun s => s.1.1) c

/-- The Fibonacci generator matrix indexed by admissible strings with two nonstar endpoints. -/
def ppGen (n : ℕ) (c : Fin (n - 1)) : Matrix (PPBasis n) (PPBasis n) ℂ :=
  blockGen (PPBasis n) (fun s => s.1.1) c

/-- Words on `n - 1` generator indices paired with Boolean signs. -/
def BraidWord (n : ℕ) : Type := List (Fin (n - 1) × Bool)

/-- The number of crossings of a braid word, defined as its list length. -/
def crossingCount {n : ℕ} (w : BraidWord n) : ℕ := w.length

/-- The ordered product of the chosen generators, using a generator when its Boolean sign is
`true` and its inverse otherwise. -/
def evalWord {M : Type} [Monoid M] [Inv M] {n : ℕ}
    (gen : Fin (n - 1) → M) (w : BraidWord n) : M :=
  (w.map fun g => if g.2 then gen g.1 else (gen g.1)⁻¹).prod

/-- The matrix obtained by multiplying `M` by the reciprocal of the complex square root of its
determinant. -/
def normalizeGen {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Complex.sqrt M.det)⁻¹ • M

/-- The property that a complex matrix indexed by `ι` is unitary and has determinant one. -/
def IsSUOn (ι : Type) [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup ι ℂ ∧ U.det = 1

/-- The property that every special unitary matrix can be approximated to every positive
tolerance by a member of `G` after multiplication by some phase `exp (θ * i)`. -/
def PhaseDenseOn (ι : Type) [Fintype ι] [DecidableEq ι] (G : Set (Matrix ι ι ℂ)) : Prop :=
  ∀ U : Matrix ι ι ℂ, IsSUOn ι U → ∀ ε : ℝ, 0 < ε →
    ∃ M ∈ G, ∃ θ : ℝ, ‖(Complex.exp (θ * Complex.I)) • M - U‖ ≤ ε

end Qatlib.Papers.BeyondCircuit08.MainResults.Model
