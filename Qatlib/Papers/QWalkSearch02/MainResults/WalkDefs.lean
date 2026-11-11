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

/-!
# Hypercube search walk and radial definitions

This module defines the hypercube shift, the Grover coin with a marked zero vertex, and the
resulting perturbed walk. It also introduces coordinate-swap operators, a two-sector radial
matrix model, trial vectors, a spectral arc, and a success amplitude for the search analysis of
[ShenviKempeWhaley2003].

## Main statements

* `perturbedWalkOp`: composes the marked coin with the hypercube shift.
* `lineWalk`: defines the unperturbed radial matrix.
* `successAmplitude`: reads the marked left-sector amplitude after perturbed radial evolution.

## References

* [Shenvi et al., 2003][ShenviKempeWhaley2003]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace Qatlib.Papers.QWalkSearch02.MainResults

/-- The type of Boolean vectors with `n` coordinates. -/
abbrev BitVec (n : ℕ) := Fin n → Bool

/-- The full hypercube-walk index type, consisting of a direction and a Boolean vertex. -/
abbrev FullIdx (n : ℕ) := Fin n × BitVec n

/-- The Boolean vector whose coordinates are all false. -/
def zeroVec (n : ℕ) : BitVec n := fun _ => false

/-- The Boolean vector obtained by negating coordinate `d` and leaving all other coordinates
fixed. -/
def flipBit {n : ℕ} (d : Fin n) (x : BitVec n) : BitVec n :=
  fun k => if k = d then !(x k) else x k

/-- The Boolean vector obtained by exchanging coordinates `i` and `j`. -/
def swapBits {n : ℕ} (i j : Fin n) (x : BitVec n) : BitVec n :=
  fun k => x (Equiv.swap i j k)

/-- The direction obtained by exchanging direction labels `i` and `j`. -/
def swapDir {n : ℕ} (i j : Fin n) (d : Fin n) : Fin n :=
  Equiv.swap i j d

/-- The action on amplitudes induced by simultaneously swapping direction labels and vertex
coordinates. -/
def swapOp {n : ℕ} (i j : Fin n) (v : FullIdx n → ℂ) : FullIdx n → ℂ :=
  fun p => v (swapDir i j p.1, swapBits i j p.2)

/-- The hypercube shift, which flips the vertex bit selected by the direction register. -/
def shiftOp (n : ℕ) (v : FullIdx n → ℂ) : FullIdx n → ℂ :=
  fun p => v (p.1, flipBit p.1 p.2)

/-- The Grover coin entry `2 / n` minus the indicator of equal direction indices. -/
def groverEntry (n : ℕ) (d d' : Fin n) : ℂ :=
  (if d = d' then -1 else 0) + (2 : ℂ) / (n : ℂ)

/-- The coin action that negates amplitudes at the zero vertex and applies the Grover coin at
every other vertex. -/
def coinOp (n : ℕ) (v : FullIdx n → ℂ) : FullIdx n → ℂ :=
  fun p =>
    if p.2 = zeroVec n then -v p
    else ∑ d' : Fin n, groverEntry n p.1 d' * v (d', p.2)

/-- The marked hypercube-walk operator obtained by applying `coinOp` and then `shiftOp`. -/
def perturbedWalkOp (n : ℕ) : (FullIdx n → ℂ) → (FullIdx n → ℂ) :=
  fun v => shiftOp n (coinOp n v)

/-- A coordinate swap fixes the all-false Boolean vector. -/
lemma swapBits_zero {n : ℕ} (i j : Fin n) : swapBits i j (zeroVec n) = zeroVec n := by
  funext k
  simp [swapBits, zeroVec]

/-- Applying the same coordinate swap twice returns the original Boolean vector. -/
lemma swapBits_apply_apply {n : ℕ} (i j : Fin n) (x : BitVec n) :
    swapBits i j (swapBits i j x) = x := by
  funext k
  simp [swapBits]

/-- A swapped Boolean vector is zero exactly when the original vector is zero. -/
lemma swapBits_eq_zero_iff {n : ℕ} (i j : Fin n) (x : BitVec n) :
    swapBits i j x = zeroVec n ↔ x = zeroVec n := by
  constructor
  · intro h
    have := congrArg (swapBits i j) h
    simpa [swapBits_apply_apply, swapBits_zero] using this
  · intro h
    subst h
    exact swapBits_zero i j

/-- Grover coin entries are invariant under simultaneous swaps of their two direction indices. -/
lemma groverEntry_swap {n : ℕ} (i j d d' : Fin n) :
    groverEntry n (Equiv.swap i j d) (Equiv.swap i j d') = groverEntry n d d' := by
  unfold groverEntry
  by_cases h : d = d'
  · subst h
    simp
  · have h' : Equiv.swap i j d ≠ Equiv.swap i j d' :=
      fun hh => h ((Equiv.swap i j).injective hh)
    simp [h, h']

/-- The radial-walk index type with two copies of `Fin n`. -/
abbrev LineIdx (n : ℕ) := Fin n ⊕ Fin n

/-- The natural index of a radial state, discarding its left or right sector. -/
def lineIdxNat {n : ℕ} : LineIdx n → ℕ
  | Sum.inl i => (i : ℕ)
  | Sum.inr i => (i : ℕ)

/-- The radial cosine coefficient `1 - 2 * x / n`. -/
def cosOmega (n x : ℕ) : ℝ := 1 - 2 * (x : ℝ) / (n : ℝ)

/-- The radial sine coefficient `2 / n * √(x * (n - x))`. -/
def sinOmega (n x : ℕ) : ℝ := 2 / (n : ℝ) * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)))

/-- The two-sector radial walk matrix with nearest-neighbor sine entries and same-index cosine
entries. -/
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

/-- The radial walk matrix with two subtracted from the entry at row `Sum.inr o` and column
`Sum.inl o`. -/
def perturbedLineWalk (n : ℕ) (o : Fin n) : Matrix (LineIdx n) (LineIdx n) ℂ :=
  fun s t => lineWalk n s t - if s = Sum.inr o ∧ t = Sum.inl o then 2 else 0

/-- The radial vector with binomial amplitude `√(choose (n - 1) i / 2^n)` in both sectors. -/
def linePsi0 (n : ℕ) : LineIdx n → ℂ :=
  fun s => (Real.sqrt ((Nat.choose (n - 1) (lineIdxNat s) : ℝ) / (2 : ℝ) ^ n) : ℂ)

/-- The coefficient `1 / √(2 * choose (2 * m - 1) i)` used in the second trial vector. -/
def lineA (m i : ℕ) : ℝ := 1 / Real.sqrt (2 * (Nat.choose (2 * m - 1) i : ℝ))

/-- The square root of the sum of reciprocal binomial coefficients of order `2 * m - 1` over
indices less than `m`. -/
def lineC (m : ℕ) : ℝ :=
  Real.sqrt (∑ x ∈ Finset.range m, 1 / (Nat.choose (2 * m - 1) x : ℝ))

/-- The trial vector supported on indices below `m`, with coefficients `lineA / lineC` in the
left sector and their negatives in the right sector. -/
def linePsi1 (m : ℕ) : LineIdx (2 * m) → ℂ :=
  fun s =>
    match s with
    | Sum.inl i => if (i : ℕ) < m then ((lineA m (i : ℕ) / lineC m : ℝ) : ℂ) else 0
    | Sum.inr i => if (i : ℕ) < m then ((-(lineA m (i : ℕ) / lineC m) : ℝ) : ℂ) else 0

/-- The unit-circle arc consisting of complex numbers with real part greater than `1 - 2 / (3 *
n)`. -/
def spectrumArc (n : ℕ) : Set ℂ :=
  {z | 1 - 2 / (3 * (n : ℝ)) < z.re ∧ ‖z‖ = 1}

/-- The integer search time given by the floor of `(π / 2) * √(2^(n - 1))`. -/
def searchTime (n : ℕ) : ℕ :=
  Nat.floor (Real.pi / 2 * Real.sqrt ((2 : ℝ) ^ (n - 1)))

/-- The finite Hermitian inner product `∑ k, star (u k) * v k`. -/
def innerC {ι : Type*} [Fintype ι] (u v : ι → ℂ) : ℂ := ∑ k, star (u k) * v k

/-- The `Sum.inl o` coordinate after `t` iterations of the perturbed radial walk starting from
`linePsi0 n`. -/
def successAmplitude (n : ℕ) (o : Fin n) (t : ℕ) : ℂ :=
  ((perturbedLineWalk n o ^ t) *ᵥ linePsi0 n) (Sum.inl o)

end Qatlib.Papers.QWalkSearch02.MainResults
