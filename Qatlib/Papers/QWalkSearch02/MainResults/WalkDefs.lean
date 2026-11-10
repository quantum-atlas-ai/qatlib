/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace Qatlib.Papers.QWalkSearch02.MainResults

abbrev BitVec (n : ℕ) := Fin n → Bool

abbrev FullIdx (n : ℕ) := Fin n × BitVec n

def zeroVec (n : ℕ) : BitVec n := fun _ => false

def flipBit {n : ℕ} (d : Fin n) (x : BitVec n) : BitVec n :=
  fun k => if k = d then !(x k) else x k

def swapBits {n : ℕ} (i j : Fin n) (x : BitVec n) : BitVec n :=
  fun k => x (Equiv.swap i j k)

def swapDir {n : ℕ} (i j : Fin n) (d : Fin n) : Fin n :=
  Equiv.swap i j d

def swapOp {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) : FullIdx n → ℂ :=
  fun p => v (swapDir i j p.1, swapBits i j p.2)

def shiftOp (n : ℕ) (v : FullIdx n → ℂ) : FullIdx n → ℂ :=
  fun p => v (p.1, flipBit p.1 p.2)

def groverEntry (n : ℕ) (d d' : Fin n) : ℂ :=
  (if d = d' then -1 else 0) + (2 : ℂ) / (n : ℂ)

def coinOp (n : ℕ) (v : FullIdx n → ℂ) : FullIdx n → ℂ :=
  fun p =>
    if p.2 = zeroVec n then -v p
    else ∑ d' : Fin n, groverEntry n p.1 d' * v (d', p.2)

def perturbedWalkOp (n : ℕ) : (FullIdx n → ℂ) → (FullIdx n → ℂ) :=
  fun v => shiftOp n (coinOp n v)

lemma swapBits_zero {n : ℕ} (i j : Fin n) : swapBits i j (zeroVec n) = zeroVec n := by
  funext k
  simp [swapBits, zeroVec]

lemma swapBits_apply_apply {n : ℕ} (i j : Fin n) (x : BitVec n) :
    swapBits i j (swapBits i j x) = x := by
  funext k
  simp [swapBits]

lemma swapBits_eq_zero_iff {n : ℕ} (i j : Fin n) (x : BitVec n) :
    swapBits i j x = zeroVec n ↔ x = zeroVec n := by
  constructor
  · intro h
    have := congrArg (swapBits i j) h
    simpa [swapBits_apply_apply, swapBits_zero] using this
  · intro h
    subst h
    exact swapBits_zero i j

lemma groverEntry_swap {n : ℕ} (i j d d' : Fin n) :
    groverEntry n (Equiv.swap i j d) (Equiv.swap i j d') = groverEntry n d d' := by
  unfold groverEntry
  by_cases h : d = d'
  · subst h
    simp
  · have h' : Equiv.swap i j d ≠ Equiv.swap i j d' :=
      fun hh => h ((Equiv.swap i j).injective hh)
    simp [h, h']

abbrev LineIdx (n : ℕ) := Fin n ⊕ Fin n

def lineIdxNat {n : ℕ} : LineIdx n → ℕ
  | Sum.inl i => (i : ℕ)
  | Sum.inr i => (i : ℕ)

def cosOmega (n x : ℕ) : ℝ := 1 - 2 * (x : ℝ) / (n : ℝ)

def sinOmega (n x : ℕ) : ℝ := 2 / (n : ℝ) * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)))

def lineWalk (n : ℕ) : Matrix (LineIdx n) (LineIdx n) ℂ :=
  fun s t =>
    match s, t with
    | Sum.inl i, Sum.inl j =>
        if (j : ℕ) = (i : ℕ) + 1 then ((sinOmega n (j : ℕ) : ℝ) : ℂ) else 0
    | Sum.inl i, Sum.inr j =>
        if (j : ℕ) = (i : ℕ) then ((-(cosOmega n ((i : ℕ) + 1)) : ℝ) : ℂ) else 0
    | Sum.inr i, Sum.inl j =>
        if (j : ℕ) = (i : ℕ) then ((cosOmega n (i : ℕ) : ℝ) : ℂ) else 0
    | Sum.inr i, Sum.inr j =>
        if (i : ℕ) = (j : ℕ) + 1 then ((sinOmega n (i : ℕ) : ℝ) : ℂ) else 0

def perturbedLineWalk (n : ℕ) (o : Fin n) : Matrix (LineIdx n) (LineIdx n) ℂ :=
  fun s t => lineWalk n s t - if s = Sum.inr o ∧ t = Sum.inl o then 2 else 0

def linePsi0 (n : ℕ) : LineIdx n → ℂ :=
  fun s => (Real.sqrt ((Nat.choose (n - 1) (lineIdxNat s) : ℝ) / (2 : ℝ) ^ n) : ℂ)

def lineA (m i : ℕ) : ℝ := 1 / Real.sqrt (2 * (Nat.choose (2 * m - 1) i : ℝ))

def lineC (m : ℕ) : ℝ :=
  Real.sqrt (∑ x ∈ Finset.range m, 1 / (Nat.choose (2 * m - 1) x : ℝ))

def linePsi1 (m : ℕ) : LineIdx (2 * m) → ℂ :=
  fun s =>
    match s with
    | Sum.inl i => if (i : ℕ) < m then ((lineA m (i : ℕ) / lineC m : ℝ) : ℂ) else 0
    | Sum.inr i => if (i : ℕ) < m then ((-(lineA m (i : ℕ) / lineC m) : ℝ) : ℂ) else 0

def spectrumArc (n : ℕ) : Set ℂ :=
  {z | 1 - 2 / (3 * (n : ℝ)) < z.re ∧ ‖z‖ = 1}

def searchTime (n : ℕ) : ℕ :=
  Nat.floor (Real.pi / 2 * Real.sqrt ((2 : ℝ) ^ (n - 1)))

def innerC {ι : Type*} [Fintype ι] (u v : ι → ℂ) : ℂ := ∑ k, star (u k) * v k

def successAmplitude (n : ℕ) (o : Fin n) (t : ℕ) : ℂ :=
  ((perturbedLineWalk n o ^ t) *ᵥ linePsi0 n) (Sum.inl o)

end Qatlib.Papers.QWalkSearch02.MainResults
