/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Trace

/-!
# Characters and Fourier conventions for shifted problems

This module fixes the character functions, shift predicates, and Fourier conventions used for
the shifted quadratic-character problems of [VanDamHallgren2000]. `quadCharZMod`,
`jacobiCharZMod`, and `finiteFieldQuadChar` give integer-valued characters, while the four shift
predicates express the corresponding oracle promises, including the ambient-modulus promise for
unknown Jacobi modulus.

The normalized transforms `modularFourier` and `modularFourierInv` use the standard additive
character with opposite signs. The module also defines the Legendre setup state, modular and
finite-field Gauss sums, the trace-induced additive character, a polynomial cost predicate, and
the two-query count `algorithm1Queries`.

## Main statements

* `quadCharZMod_eq_legendreSym`: agreement with the integer Legendre symbol.
* `jacobiCharZMod_natCast`: agreement with the integer Jacobi symbol on natural representatives.
* `modularFourier` and `modularFourierInv`: the normalized transform conventions.
* `traceAddChar`: the additive character obtained from the finite-field trace.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators NumberTheorySymbols
open Finset

/-- The integer-valued quadratic character on the prime residue field `ZMod p`. -/
def quadCharZMod (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℤ :=
  quadraticChar (ZMod p) a

/-- Evaluating `quadCharZMod p` at an integer residue gives the Legendre symbol of that integer
modulo `p`. -/
theorem quadCharZMod_eq_legendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) :
    quadCharZMod p (a : ZMod p) = legendreSym p a := rfl

/-- The integer Jacobi symbol modulo `n`, evaluated at the canonical natural representative of a
residue in `ZMod n`. -/
def jacobiCharZMod (n : ℕ) (a : ZMod n) : ℤ :=
  jacobiSym (a.val : ℤ) n

/-- The Jacobi character of a natural-number residue equals the integer Jacobi symbol of that
natural number modulo `n`. -/
theorem jacobiCharZMod_natCast (n a : ℕ) :
    jacobiCharZMod n (a : ZMod n) = jacobiSym (a : ℤ) n := by
  unfold jacobiCharZMod
  rw [ZMod.val_natCast]
  apply jacobiSym.mod_left'
  simp

/-- The integer-valued quadratic character of a finite field. -/
def finiteFieldQuadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F] : F → ℤ :=
  quadraticChar F

/-- The promise that `f x` equals the quadratic character of `x + s` over the prime residue
field. -/
def IsShiftedLegendre (p : ℕ) [Fact p.Prime] (f : ZMod p → ℤ) (s : ZMod p) : Prop :=
  ∀ x, f x = quadCharZMod p (x + s)

/-- The promise that `f x` equals the Jacobi character of `x + s` modulo `n`. -/
def IsShiftedJacobi (n : ℕ) (f : ZMod n → ℤ) (s : ZMod n) : Prop :=
  ∀ x, f x = jacobiCharZMod n (x + s)

/-- The unknown-modulus Jacobi promise that `n ^ 2 < M` and `f` on `ZMod M` agrees with the
shifted Jacobi character after reducing each canonical representative modulo `n`. -/
def IsShiftedJacobiUnknown (M n : ℕ) (f : ZMod M → ℤ) (s : ZMod n) : Prop :=
  n ^ 2 < M ∧ ∀ x : ZMod M,
    f x = jacobiCharZMod n ((x.val : ZMod n) + s)

/-- The promise that `f` is the finite-field quadratic character translated by the shift `s`. -/
def IsShiftedQuadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : F → ℤ) (s : F) : Prop :=
  ∀ x, f x = finiteFieldQuadChar F (x + s)

/-- The standard complex additive character modulo `n` evaluated at one, giving the chosen `n`th
root of unity. -/
def omega (n : ℕ) [NeZero n] : ℂ := ZMod.stdAddChar (1 : ZMod n)

/-- The normalized Fourier transform on `ZMod n` with coefficient `1 / sqrt n` and kernel given
by the standard additive character of `x * y`. -/
def modularFourier (n : ℕ) [NeZero n] (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun y => (Real.sqrt n : ℂ)⁻¹ * ∑ x : ZMod n, v x * ZMod.stdAddChar (x * y)

/-- The normalized inverse Fourier transform on `ZMod n` with coefficient `1 / sqrt n` and
kernel given by the standard additive character of `-(x * y)`. -/
def modularFourierInv (n : ℕ) [NeZero n] (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun y => (Real.sqrt n : ℂ)⁻¹ * ∑ x : ZMod n, v x * ZMod.stdAddChar (-(x * y))

/-- The complex amplitude function given by the shifted Legendre character divided by `sqrt (p -
1)`. -/
def legendreSetupState (p : ℕ) [Fact p.Prime] (s : ZMod p) : ZMod p → ℂ :=
  fun x => ((quadCharZMod p (x + s) : ℤ) : ℂ) * ((Real.sqrt (p - 1) : ℂ)⁻¹)

/-- The Gauss sum of the quadratic character on `ZMod p` against its standard complex additive
character. -/
def legendreGaussSum (p : ℕ) [Fact p.Prime] : ℂ :=
  ∑ x : ZMod p, ((quadCharZMod p x : ℤ) : ℂ) * ZMod.stdAddChar x

/-- The Gauss sum of the Jacobi character modulo `n` against the standard complex additive
character. -/
def jacobiGaussSum (n : ℕ) [NeZero n] : ℂ :=
  ∑ x : ZMod n, ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar x

/-- The complex additive character on `F` obtained by composing the field trace to `ZMod p` with
the standard additive character of `ZMod p`. -/
def traceAddChar (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : AddChar F ℂ where
  toFun x := ZMod.stdAddChar (Algebra.trace (ZMod p) F x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    rw [map_add]
    exact AddChar.map_add_eq_mul ZMod.stdAddChar _ _

/-- The Gauss sum of the finite-field quadratic character against the additive character induced
by the trace to `ZMod p`. -/
def finiteFieldGaussSum (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] : ℂ :=
  ∑ x : F, ((finiteFieldQuadChar F x : ℤ) : ℂ) * traceAddChar p F x

/-- States that a natural-number cost function is bounded at every input `n` by `c * (n + 1) ^
k` for some natural constants `c` and `k`. -/
def PolynomiallyBounded (cost : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, cost n ≤ c * (n + 1) ^ k

/-- The query-count constant two assigned to Algorithm 1 of [VanDamHallgren2000]. -/
def algorithm1Queries : ℕ := 2

end Qatlib.Papers.QuadChar00.MainResults
