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
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

open Matrix

def AFib : ℂ := Complex.exp (Complex.I * (-(3 * Real.pi / 5)))

def tauFib : ℝ := 2 / (1 + Real.sqrt 5)

def tauC : ℂ := (tauFib : ℂ)

def tau32C : ℂ := ((Real.sqrt tauFib : ℝ) : ℂ) ^ 3

def aFib : ℂ := -(AFib ^ 4)

def bFib : ℂ := AFib ^ 8

def cFib : ℂ := AFib ^ 8 * tauC ^ 2 - AFib ^ 4 * tauC

def dFib : ℂ := AFib ^ 8 * tau32C + AFib ^ 4 * tau32C

def eFib : ℂ := AFib ^ 8 * tauC - AFib ^ 4 * tauC ^ 2

def fibRule (x m z t : Bool) : ℂ :=
  if m = true then
    if ((!x) && (!z)) = true then (if t = true then cFib else dFib) else 0
  else
    match x, z with
    | false, true => if t = true then 0 else aFib
    | true, false => if t = true then 0 else aFib
    | true, true => if t = true then 0 else bFib
    | false, false => if t = true then dFib else eFib

def NoAdj {L : ℕ} (s : Fin L → Bool) : Prop :=
  ∀ (i j : Fin L), j.val = i.val + 1 → ¬ (s i = true ∧ s j = true)

def rhoEntry (n : ℕ) (i : Fin (n - 1)) (s t : Fin (n + 1) → Bool) : ℂ :=
  let m := s ⟨i.val + 1, by omega⟩
  let x := s ⟨i.val, by omega⟩
  let z := s ⟨i.val + 2, by omega⟩
  if t = Function.update s ⟨i.val + 1, by omega⟩ (!m) then fibRule x m z (!m)
  else if t = s then fibRule x m z m
  else 0

abbrev SSBasis (n : ℕ) : Type :=
  {s : Fin (n + 1) → Bool //
    s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = true ∧ NoAdj s}

abbrev SPBasis (n : ℕ) : Type :=
  {s : Fin (n + 1) → Bool //
    s ⟨0, Nat.succ_pos n⟩ = true ∧ s ⟨n, Nat.lt_succ_self n⟩ = false ∧ NoAdj s}

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

def rhoSS (n : ℕ) (i : Fin (n - 1)) : Matrix (SSBasis n) (SSBasis n) ℂ :=
  fun s t => rhoEntry n i s.1 t.1

def rhoSP (n : ℕ) (i : Fin (n - 1)) : Matrix (SPBasis n) (SPBasis n) ℂ :=
  fun s t => rhoEntry n i s.1 t.1

def rhoPS (n : ℕ) (i : Fin (n - 1)) : Matrix (PSBasis n) (PSBasis n) ℂ :=
  fun s t => rhoEntry n i s.1 t.1

abbrev BraidWord (n : ℕ) : Type := List (Fin (n - 1) × Bool)

def evalSS (n : ℕ) (w : BraidWord n) : Matrix (SSBasis n) (SSBasis n) ℂ :=
  w.foldl (fun M g => M * (if g.2 = true then rhoSS n g.1 else (rhoSS n g.1)⁻¹)) 1

def evalSP (n : ℕ) (w : BraidWord n) : Matrix (SPBasis n) (SPBasis n) ℂ :=
  w.foldl (fun M g => M * (if g.2 = true then rhoSP n g.1 else (rhoSP n g.1)⁻¹)) 1

def evalPS (n : ℕ) (w : BraidWord n) : Matrix (PSBasis n) (PSBasis n) ℂ :=
  w.foldl (fun M g => M * (if g.2 = true then rhoPS n g.1 else (rhoPS n g.1)⁻¹)) 1

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions
