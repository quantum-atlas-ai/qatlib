/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Shared Gaussian FFT definitions and integer audits

Gaussian scalars are pairs of integers with a shared scale supplied to multiplication. This
module defines the recursive even-odd butterfly transform, its conjugation-based positive
variant, operation counters, and predicates bounding component magnitudes and all intermediate
multiplication integers.

For background on finite Fourier transforms in quantum computation, see [NielsenChuang2010].

## Main statements

* `gaussianSharedFFT`: the shared butterfly recursion with operation counts.
* `gaussianSharedPositiveFFT`: conjugation-based positive variant.
* `GaussianFFTIntegerBounded`: recursive bounds on the computation integers.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput
open scoped BigOperators

/-- A Gaussian scalar represented by a pair of integer components. -/
abbrev GaussianDyadicScalar := ℤ × ℤ

/-- Adds the two integer components of Gaussian scalars separately. -/
def gaussianScalarAdd (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  (x.1 + y.1, x.2 + y.2)

/-- Subtracts the two integer components of Gaussian scalars separately. -/
def gaussianScalarSub (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  (x.1 - y.1, x.2 - y.2)

/-- Conjugates a Gaussian scalar by negating its second component. -/
def gaussianScalarConj (x : GaussianDyadicScalar) : GaussianDyadicScalar := (x.1, -x.2)

/-- A table assigning a Gaussian twiddle scalar to every index at each of the `k` butterfly
levels. -/
abbrev GaussianTwiddleTable (k : ℕ) :=
  (level : Fin k) → Fin (2 ^ level.val) → GaussianDyadicScalar

/-- A length-`2 ^ k` vector of Gaussian output scalars together with product and addition
counts. -/
structure GaussianDyadicFFTRun (k : ℕ) where
  values : Vector GaussianDyadicScalar (2 ^ k)
  products : ℕ
  additions : ℕ

/-- Forms the usual Gaussian product components and divides each integer component by the shared
scale `D`. -/
def gaussianScalarMulShared (D : ℤ) (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  let ac := x.1 * y.1
  let bd := x.2 * y.2
  let ad := x.1 * y.2
  let bc := x.2 * y.1
  ((ac - bd) / D, (ad + bc) / D)

/-- Computes the recursive even-odd Gaussian butterfly transform using the supplied twiddle
table and shared multiplication scale, recording products and additions. -/
def gaussianSharedFFT (D : ℤ) : (k : ℕ) → GaussianTwiddleTable k →
    (Fin (2 ^ k) → GaussianDyadicScalar) → GaussianDyadicFFTRun k
  | 0, _, f => ⟨Vector.ofFn f, 0, 0⟩
  | k + 1, t, f =>
    let lower : GaussianTwiddleTable k := fun l => t l.castSucc
    let e := gaussianSharedFFT D k lower
      (fun j => f ⟨2 * j.val, by rw [pow_succ]; have := j.isLt; omega⟩)
    let o := gaussianSharedFFT D k lower
      (fun j => f ⟨2 * j.val + 1, by rw [pow_succ]; have := j.isLt; omega⟩)
    let products := Vector.ofFn (fun j : Fin (2 ^ k) =>
      gaussianScalarMulShared D (t (Fin.last k) j) o.values[j.val])
    ⟨Vector.ofFn (fun j =>
      let j' : Fin (2 ^ k) := ⟨j.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
      if j.val < 2 ^ k then gaussianScalarAdd e.values[j'.val] products[j'.val]
        else gaussianScalarSub e.values[j'.val] products[j'.val]),
      e.products + o.products + 2 ^ k, e.additions + o.additions + 2 ^ (k + 1)⟩

/-- Conjugates the input, applies the shared FFT, and conjugates its output while retaining the
operation counts. -/
def gaussianSharedPositiveFFT (D : ℤ) (k : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) : GaussianDyadicFFTRun k :=
  let r := gaussianSharedFFT D k t (fun j => gaussianScalarConj (f j))
  ⟨r.values.map gaussianScalarConj, r.products, r.additions⟩

/-- Both integer components of a Gaussian scalar have natural absolute value at most `L`. -/
def GaussianScalarBound (x : GaussianDyadicScalar) (L : ℕ) : Prop :=
  x.1.natAbs ≤ L ∧ x.2.natAbs ≤ L

/-- Lists the scale, operand components, intermediate products and sums, and output components
of shared Gaussian multiplication. -/
def gaussianMulWork (D : ℤ) (x y : GaussianDyadicScalar) : List ℤ :=
  [D, x.1, x.2, y.1, y.2, x.1 * y.1, x.2 * y.2, x.1 * y.2, x.2 * y.1,
    x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1,
    (gaussianScalarMulShared D x y).1, (gaussianScalarMulShared D x y).2]

/-- Recursively bounds the leaf inputs and scale, all listed twiddle-multiplication integers,
and each level's output components by `L` in absolute value. -/
def GaussianFFTIntegerBounded (D : ℤ) : (k : ℕ) → GaussianTwiddleTable k →
    (Fin (2 ^ k) → GaussianDyadicScalar) → ℕ → Prop
  | 0, _, f, L => D.natAbs ≤ L ∧ ∀ j, GaussianScalarBound (f j) L
  | k + 1, t, f, L =>
    let lower : GaussianTwiddleTable k := fun l => t l.castSucc
    let ev : Fin (2 ^ k) → GaussianDyadicScalar :=
      fun j => f ⟨2 * j.val, by rw [pow_succ]; have := j.isLt; omega⟩
    let od : Fin (2 ^ k) → GaussianDyadicScalar :=
      fun j => f ⟨2 * j.val + 1, by rw [pow_succ]; have := j.isLt; omega⟩
    let o := gaussianSharedFFT D k lower od
    GaussianFFTIntegerBounded D k lower ev L ∧
    GaussianFFTIntegerBounded D k lower od L ∧
    (∀ j : Fin (2 ^ k), ∀ n ∈ gaussianMulWork D (t (Fin.last k) j) o.values[j.val], n.natAbs ≤ L) ∧
    (∀ j : Fin (2 ^ (k + 1)), GaussianScalarBound (gaussianSharedFFT D (k + 1) t f).values[j.val] L)

/-- Both integer components of a Gaussian scalar have absolute-value binary size at most `L`. -/
def GaussianScalarBits (x : GaussianDyadicScalar) (L : ℕ) : Prop :=
  x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L

end Qatlib.Concepts.FinitePrecision.ComputableInput
