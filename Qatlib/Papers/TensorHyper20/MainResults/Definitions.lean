/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults

def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

def nOf (M : ℕ) : ℕ := Nat.clog 2 (M + 1)

def mOf (M ℵ : ℕ) : ℕ := 2 * nOf M + 2 + ℵ

noncomputable def qpeIterations (lam eps : ℝ) : ℕ := ⌈Real.pi * lam / (2 * eps)⌉₊

def prepareCost (M br ℵ d ks1 ks2 : ℕ) : ℤ :=
  28 * (nOf M : ℤ) + 4 * (br : ℤ) - 18 + 2 * (nOf M : ℤ) ^ 2 + 2 * (ℵ : ℤ)
    + (ceilDiv d ks1 : ℤ) + (mOf M ℵ : ℤ) * ((ks1 : ℤ) - 1)
    + (ceilDiv d ks2 : ℤ) + (ks2 : ℤ)

def selectCost (M N i kr1 kr2 : ℕ) : ℤ :=
  2 * (M : ℤ) + 4 * (N : ℤ) * (i : ℤ) - ((11 * N / 2 : ℕ) : ℤ)
    + (ceilDiv M kr1 : ℤ) + (ceilDiv N (2 * kr1) : ℤ) + (kr1 : ℤ)
    + (ceilDiv M kr2 : ℤ) + (kr2 : ℤ) - 2

def reflectionCost (M ℵ : ℕ) : ℤ := 2 * (nOf M : ℤ) + (ℵ : ℤ) + 4

def stepCost (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) : ℤ :=
  30 * (nOf M : ℤ) + 4 * (br : ℤ) - 16 + 2 * (nOf M : ℤ) ^ 2 + 3 * (ℵ : ℤ)
    + (ceilDiv d ks1 : ℤ) + (mOf M ℵ : ℤ) * ((ks1 : ℤ) - 1)
    + (ceilDiv d ks2 : ℤ) + (ks2 : ℤ)
    + 2 * (M : ℤ) + 4 * (N : ℤ) * (i : ℤ) - ((11 * N / 2 : ℕ) : ℤ)
    + (ceilDiv M kr1 : ℤ) + (ceilDiv N (2 * kr1) : ℤ) + (kr1 : ℤ)
    + (ceilDiv M kr2 : ℤ) + (kr2 : ℤ)

noncomputable def totalToffoli (M N br ℵ i d ks1 ks2 kr1 kr2 : ℕ) (lam eps : ℝ) : ℤ :=
  (qpeIterations lam eps : ℤ) * stepCost M N br ℵ i d ks1 ks2 kr1 kr2

def logicalQubitsFormula (N M I i d ℵ m ks1 : ℕ) : ℕ :=
  2 * Nat.clog 2 (I + 1) + N + 2 * nOf M + i + Nat.clog 2 d + ℵ + 5
    + max (m * ks1 + Nat.clog 2 (ceilDiv d ks1))
        (m + i * N / 2 + i - 2)

def logicalQubitsParts (N M I i d ℵ m ks1 : ℕ) : ℕ :=
  (2 * Nat.clog 2 (I + 1) - 1) + N + 2 * nOf M + ℵ + 1 + 1 + 2 + 1 + 1
    + i + Nat.clog 2 d
    + max (m * ks1 + Nat.clog 2 (ceilDiv d ks1))
        (m + i * N / 2 + i - 2)

end Qatlib.Papers.TensorHyper20.MainResults
