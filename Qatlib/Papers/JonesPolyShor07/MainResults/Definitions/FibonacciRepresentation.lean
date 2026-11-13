/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic
import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.SpecialUnitary

/-!
# Fibonacci generator matrices on endpoint sectors

This module defines the complex coefficients and local update rule for Fibonacci generator
matrices. Boolean strings satisfying `NoAdj` are restricted to three endpoint sectors, giving
`rhoSS`, `rhoSP`, and `rhoPS`; signed words are evaluated by ordered multiplication of these
matrices and their inverses. See [ShorJordan2008].

## Main statements

* `rhoSS`: The Fibonacci generator matrix restricted to the SS endpoint sector.
* `evalSP`: The ordered evaluation of a signed word using `rhoSP` for true signs and its matrix
  inverse for false signs.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

open Matrix

/-- The complex phase exp(−3πi/5). -/
def AFib : ℂ := Complex.exp (Complex.I * (-(3 * Real.pi / 5)))

/-- The positive real constant 2/(1 + √5). -/
def tauFib : ℝ := 2 / (1 + Real.sqrt 5)

/-- The complex embedding of `tauFib`. -/
def tauC : ℂ := (tauFib : ℂ)

/-- The complex embedding of √`tauFib`, raised to the third power. -/
def tau32C : ℂ := ((Real.sqrt tauFib : ℝ) : ℂ) ^ 3

/-- The Fibonacci coefficient −`AFib`^4. -/
def aFib : ℂ := -(AFib ^ 4)

/-- The Fibonacci coefficient `AFib`^8. -/
def bFib : ℂ := AFib ^ 8

/-- The coefficient `AFib`^8 `tauC`² − `AFib`^4 `tauC`. -/
def cFib : ℂ := AFib ^ 8 * tauC ^ 2 - AFib ^ 4 * tauC

/-- The coefficient (`AFib`^8 + `AFib`^4)`tau32C`. -/
def dFib : ℂ := AFib ^ 8 * tau32C + AFib ^ 4 * tau32C

/-- The coefficient `AFib`^8 `tauC` − `AFib`^4 `tauC`². -/
def eFib : ℂ := AFib ^ 8 * tauC - AFib ^ 4 * tauC ^ 2

/-- The local Fibonacci coefficient selected by two neighboring bits, the current middle bit,
and its target value. -/
def fibRule (x m z t : Bool) : ℂ :=
  if m = true then
    if ((!x) && (!z)) = true then (if t = true then cFib else dFib) else 0
  else
    match x, z with
    | false, true => if t = true then 0 else aFib
    | true, false => if t = true then 0 else aFib
    | true, true => if t = true then 0 else bFib
    | false, false => if t = true then dFib else eFib

/-- The condition that no two consecutive positions of a finite Boolean string are both true. -/
def NoAdj {L : ℕ} (s : Fin L → Bool) : Prop :=
  ∀ (i j : Fin L), j.val = i.val + 1 → ¬ (s i = true ∧ s j = true)

/-- The generator matrix entry obtained by applying `fibRule` at the indexed middle position
when the target string is unchanged or differs only by flipping that bit, and zero
otherwise. -/
def rhoEntry (n : ℕ) (i : Fin (n - 1)) (s t : Fin (n + 1) → Bool) : ℂ :=
  let m := s ⟨i.val + 1, by omega⟩
  let x := s ⟨i.val, by omega⟩
  let z := s ⟨i.val + 2, by omega⟩
  if t = Function.update s ⟨i.val + 1, by omega⟩ (!m) then fibRule x m z (!m)
  else if t = s then fibRule x m z m
  else 0

/-- Boolean strings of length n + 1 with both endpoints true and no adjacent true entries. -/
abbrev SSBasis (n : ℕ) : Type :=
  {s : Fin (n + 1) → Bool //
    s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = true ∧ NoAdj s}

/-- Boolean strings of length n + 1 with first endpoint true, last endpoint false, and no
adjacent true entries. -/
abbrev SPBasis (n : ℕ) : Type :=
  {s : Fin (n + 1) → Bool //
    s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = false ∧ NoAdj s}

/-- Boolean strings of length n + 1 with first endpoint false, last endpoint true, and no
adjacent true entries. -/
abbrev PSBasis (n : ℕ) : Type :=
  {s : Fin (n + 1) → Bool //
    s ⟨0, Nat.succ_pos n⟩ = false ∧ s ⟨n, Nat.lt_succ_self n⟩ = true ∧ NoAdj s}

noncomputable instance ssBasisFintype (n : ℕ) : Fintype (SSBasis n) := by
  classical exact inferInstance

noncomputable instance spBasisFintype (n : ℕ) : Fintype (SPBasis n) := by
  classical exact inferInstance

noncomputable instance psBasisFintype (n : ℕ) : Fintype (PSBasis n) := by
  classical exact inferInstance

instance ssBasisDecEq (n : ℕ) : DecidableEq (SSBasis n) := by
  classical exact inferInstance

instance spBasisDecEq (n : ℕ) : DecidableEq (SPBasis n) := by
  classical exact inferInstance

instance psBasisDecEq (n : ℕ) : DecidableEq (PSBasis n) := by
  classical exact inferInstance

/-- The Fibonacci generator matrix restricted to the SS endpoint sector. -/
def rhoSS (n : ℕ) (i : Fin (n - 1)) : Matrix (SSBasis n) (SSBasis n) ℂ :=
  fun s t => rhoEntry n i s.1 t.1

/-- The Fibonacci generator matrix restricted to the SP endpoint sector. -/
def rhoSP (n : ℕ) (i : Fin (n - 1)) : Matrix (SPBasis n) (SPBasis n) ℂ :=
  fun s t => rhoEntry n i s.1 t.1

/-- The Fibonacci generator matrix restricted to the PS endpoint sector. -/
def rhoPS (n : ℕ) (i : Fin (n - 1)) : Matrix (PSBasis n) (PSBasis n) ℂ :=
  fun s t => rhoEntry n i s.1 t.1

/-- A list of generator indices paired with Boolean signs on n strands. -/
abbrev BraidWord (n : ℕ) : Type := List (Fin (n - 1) × Bool)

/-- The ordered evaluation of a signed word using `rhoSS` for true signs and its matrix inverse
for false signs. -/
def evalSS (n : ℕ) (w : BraidWord n) : Matrix (SSBasis n) (SSBasis n) ℂ :=
  w.foldl (fun M g => M * (if g.2 = true then rhoSS n g.1 else (rhoSS n g.1)⁻¹)) 1

/-- The ordered evaluation of a signed word using `rhoSP` for true signs and its matrix inverse
for false signs. -/
def evalSP (n : ℕ) (w : BraidWord n) : Matrix (SPBasis n) (SPBasis n) ℂ :=
  w.foldl (fun M g => M * (if g.2 = true then rhoSP n g.1 else (rhoSP n g.1)⁻¹)) 1

/-- The ordered evaluation of a signed word using `rhoPS` for true signs and its matrix inverse
for false signs. -/
def evalPS (n : ℕ) (w : BraidWord n) : Matrix (PSBasis n) (PSBasis n) ℂ :=
  w.foldl (fun M g => M * (if g.2 = true then rhoPS n g.1 else (rhoPS n g.1)⁻¹)) 1

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions
