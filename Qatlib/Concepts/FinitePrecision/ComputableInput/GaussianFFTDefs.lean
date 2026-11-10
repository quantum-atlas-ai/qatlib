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

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput
open scoped BigOperators

abbrev GaussianDyadicScalar := ℤ × ℤ

def gaussianScalarAdd (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  (x.1 + y.1, x.2 + y.2)

def gaussianScalarSub (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  (x.1 - y.1, x.2 - y.2)

def gaussianScalarConj (x : GaussianDyadicScalar) : GaussianDyadicScalar := (x.1, -x.2)

abbrev GaussianTwiddleTable (k : ℕ) :=
  (level : Fin k) → Fin (2 ^ level.val) → GaussianDyadicScalar

structure GaussianDyadicFFTRun (k : ℕ) where
  values : Vector GaussianDyadicScalar (2 ^ k)
  products : ℕ
  additions : ℕ

def gaussianScalarMulShared (D : ℤ) (x y : GaussianDyadicScalar) : GaussianDyadicScalar :=
  let ac := x.1 * y.1
  let bd := x.2 * y.2
  let ad := x.1 * y.2
  let bc := x.2 * y.1
  ((ac - bd) / D, (ad + bc) / D)

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

def gaussianSharedPositiveFFT (D : ℤ) (k : ℕ) (t : GaussianTwiddleTable k)
    (f : Fin (2 ^ k) → GaussianDyadicScalar) : GaussianDyadicFFTRun k :=
  let r := gaussianSharedFFT D k t (fun j => gaussianScalarConj (f j))
  ⟨r.values.map gaussianScalarConj, r.products, r.additions⟩

def GaussianScalarBound (x : GaussianDyadicScalar) (L : ℕ) : Prop :=
  x.1.natAbs ≤ L ∧ x.2.natAbs ≤ L

def gaussianMulWork (D : ℤ) (x y : GaussianDyadicScalar) : List ℤ :=
  [D, x.1, x.2, y.1, y.2, x.1 * y.1, x.2 * y.2, x.1 * y.2, x.2 * y.1,
    x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1,
    (gaussianScalarMulShared D x y).1, (gaussianScalarMulShared D x y).2]

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

def GaussianScalarBits (x : GaussianDyadicScalar) (L : ℕ) : Prop :=
  x.1.natAbs.size ≤ L ∧ x.2.natAbs.size ≤ L

end Qatlib.Concepts.FinitePrecision.ComputableInput
