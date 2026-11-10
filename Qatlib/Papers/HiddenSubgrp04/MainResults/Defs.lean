/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

open scoped BigOperators

noncomputable section

def nearInt (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

def alpha (M N : ℕ) : ℤ := ⌊(M : ℝ) / (2 * (N : ℝ)) + 1 / 2⌋

def beta (M N : ℕ) : ℤ := ⌊(M : ℝ) / (2 * (N : ℝ)) - 1 / 2⌋

def alphaNat (M N : ℕ) : ℕ := (alpha M N).toNat

def distMod (M : ℝ) (x : ℝ) : ℝ := |x - M * (nearInt (x / M) : ℝ)|

def delta (M N : ℕ) (s : ℤ) : ℝ :=
  (M : ℝ) / (N : ℝ) * (s : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (s : ℝ)) : ℝ)

def cell (M N : ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range M).filter (fun b =>
    distMod (M : ℝ) ((b : ℝ) - (nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ)) : ℝ)) <
      (M : ℝ) / (2 * (N : ℝ)) - 1 / 2)

def cellZ (M N : ℕ) (i : ℤ) : Finset ℕ := cell M N i.toNat

def deltaMap (M N : ℕ) (k : ℕ) : ℤ × ℤ :=
  let k' : ℤ := nearInt ((N : ℝ) / (M : ℝ) * (k : ℝ))
  (k' % (N : ℤ), (k : ℤ) - nearInt ((M : ℝ) / (N : ℝ) * (k' : ℝ)))

def Cs (M N : ℕ) (s : ℤ) : Set ℤ :=
  {t : ℤ | ∃ k : ℕ, k < M ∧ (deltaMap M N k).1 = s ∧ (deltaMap M N k).2 = t}

def lambdaSet (M N : ℕ) : Set ℤ :=
  {t : ℤ | -((M : ℝ) / (2 * (N : ℝ))) - 1 / 2 < (t : ℝ) ∧
    (t : ℝ) < (M : ℝ) / (2 * (N : ℝ)) - 1 / 2}

def lambdaFinset (M N : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(alpha M N)) (alpha M N)).filter (fun t => t ∈ lambdaSet M N)

def omega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))

def Acoef (L M N : ℕ) (i k : ℕ) : ℂ :=
  ((Real.sqrt ((L * M * N : ℕ) : ℝ) : ℂ))⁻¹ *
    ∑ a ∈ Finset.range (L * N), (omega N ^ (a * i))⁻¹ * (omega M ^ (a * k))

def Avec (L M N : ℕ) (i : ℕ) : Fin M → ℂ :=
  fun k => Acoef L M N i k.val

def Bvec (L M N : ℕ) (i : ℕ) : Fin M → ℂ :=
  fun k => if k.val ∈ cell M N i then Acoef L M N i k.val else 0

def Tvec (L M N : ℕ) (i : ℕ) : Fin M → ℂ :=
  fun k => if k.val ∈ cell M N i then 0 else Acoef L M N i k.val

def Svec (L M N : ℕ) (i : ℕ) : Fin M → ℂ :=
  fun k =>
    let b : ℕ := ((k.val : ℤ) - nearInt ((M : ℝ) / (N : ℝ) * (i : ℝ))) % (M : ℤ) |>.toNat
    if b ∈ cell M N 0 then Acoef L M N 0 b else 0

def l2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

def cyclicQFT {N : ℕ} (u : Fin N → ℂ) : Fin N → ℂ :=
  fun k => ((Real.sqrt (N : ℝ) : ℂ))⁻¹ * ∑ j : Fin N, omega N ^ (j.val * k.val) * u j

def uL (L M N : ℕ) (u : Fin N → ℂ) : Fin M → ℂ :=
  fun k => ∑ i : Fin N, cyclicQFT u i * Avec L M N i.val k

def DeltaVec (M N : ℕ) (v : Fin M → ℂ) : Fin N × Fin (2 * alphaNat M N + 1) → ℂ :=
  fun p =>
    ∑ k : Fin M,
      if (deltaMap M N k.val).1 = (p.1.val : ℤ) ∧
          (deltaMap M N k.val).2 + alpha M N = (p.2.val : ℤ) then v k else 0

def garbageVec (L M N : ℕ) : Fin (2 * alphaNat M N + 1) → ℂ := by
  classical
  exact fun u =>
    let t : ℤ := (u.val : ℤ) - alpha M N
    if t ∈ lambdaSet M N then Acoef L M N 0 ((t % (M : ℤ)).toNat) else 0

def algOutput (L M N : ℕ) (u : Fin N → ℂ) : Fin N × Fin (2 * alphaNat M N + 1) → ℂ :=
  DeltaVec M N (uL L M N u)

def tensorVec {n m : ℕ} (a : Fin n → ℂ) (b : Fin m → ℂ) : Fin n × Fin m → ℂ :=
  fun p => a p.1 * b p.2

def tvDist {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℝ :=
  ∑ i, |‖v i‖ ^ 2 - ‖w i‖ ^ 2|

theorem alpha_eq_beta_add_one (M N : ℕ) : alpha M N = beta M N + 1 := by
  unfold alpha beta
  have h : (M : ℝ) / (2 * (N : ℝ)) + 1 / 2 =
      ((M : ℝ) / (2 * (N : ℝ)) - 1 / 2) + (1 : ℤ) := by
    push_cast
    ring
  rw [h, Int.floor_add_intCast]

theorem beta_add_one_eq_alpha (M N : ℕ) : beta M N + 1 = alpha M N :=
  (alpha_eq_beta_add_one M N).symm

theorem mem_lambdaSet_iff (M N : ℕ) (t : ℤ) :
    t ∈ lambdaSet M N ↔
      -((M : ℝ) / (2 * (N : ℝ))) - 1 / 2 < (t : ℝ) ∧
        (t : ℝ) < (M : ℝ) / (2 * (N : ℝ)) - 1 / 2 :=
  Iff.rfl

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
