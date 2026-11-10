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

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators NumberTheorySymbols
open Finset

def quadCharZMod (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℤ :=
  quadraticChar (ZMod p) a

theorem quadCharZMod_eq_legendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) :
    quadCharZMod p (a : ZMod p) = legendreSym p a := rfl

def jacobiCharZMod (n : ℕ) (a : ZMod n) : ℤ :=
  jacobiSym (a.val : ℤ) n

theorem jacobiCharZMod_natCast (n a : ℕ) :
    jacobiCharZMod n (a : ZMod n) = jacobiSym (a : ℤ) n := by
  unfold jacobiCharZMod
  rw [ZMod.val_natCast]
  apply jacobiSym.mod_left'
  simp

def finiteFieldQuadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F] : F → ℤ :=
  quadraticChar F

def IsShiftedLegendre (p : ℕ) [Fact p.Prime] (f : ZMod p → ℤ) (s : ZMod p) : Prop :=
  ∀ x, f x = quadCharZMod p (x + s)

def IsShiftedJacobi (n : ℕ) (f : ZMod n → ℤ) (s : ZMod n) : Prop :=
  ∀ x, f x = jacobiCharZMod n (x + s)

def IsShiftedJacobiUnknown (M n : ℕ) (f : ZMod M → ℤ) (s : ZMod n) : Prop :=
  n ^ 2 < M ∧ ∀ x : ZMod M,
    f x = jacobiCharZMod n ((x.val : ZMod n) + s)

def IsShiftedQuadChar (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : F → ℤ) (s : F) : Prop :=
  ∀ x, f x = finiteFieldQuadChar F (x + s)

def omega (n : ℕ) [NeZero n] : ℂ := ZMod.stdAddChar (1 : ZMod n)

def modularFourier (n : ℕ) [NeZero n] (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun y => (Real.sqrt n : ℂ)⁻¹ * ∑ x : ZMod n, v x * ZMod.stdAddChar (x * y)

def modularFourierInv (n : ℕ) [NeZero n] (v : ZMod n → ℂ) : ZMod n → ℂ :=
  fun y => (Real.sqrt n : ℂ)⁻¹ * ∑ x : ZMod n, v x * ZMod.stdAddChar (-(x * y))

def legendreSetupState (p : ℕ) [Fact p.Prime] (s : ZMod p) : ZMod p → ℂ :=
  fun x => ((quadCharZMod p (x + s) : ℤ) : ℂ) * ((Real.sqrt (p - 1) : ℂ)⁻¹)

def legendreGaussSum (p : ℕ) [Fact p.Prime] : ℂ :=
  ∑ x : ZMod p, ((quadCharZMod p x : ℤ) : ℂ) * ZMod.stdAddChar x

def jacobiGaussSum (n : ℕ) [NeZero n] : ℂ :=
  ∑ x : ZMod n, ((jacobiCharZMod n x : ℤ) : ℂ) * ZMod.stdAddChar x

def traceAddChar (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [Algebra (ZMod p) F] : AddChar F ℂ where
  toFun x := ZMod.stdAddChar (Algebra.trace (ZMod p) F x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    rw [map_add]
    exact AddChar.map_add_eq_mul ZMod.stdAddChar _ _

def finiteFieldGaussSum (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] : ℂ :=
  ∑ x : F, ((finiteFieldQuadChar F x : ℤ) : ℂ) * traceAddChar p F x

def PolynomiallyBounded (cost : ℕ → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ n, cost n ≤ c * (n + 1) ^ k

def algorithm1Queries : ℕ := 2

end Qatlib.Papers.QuadChar00.MainResults
