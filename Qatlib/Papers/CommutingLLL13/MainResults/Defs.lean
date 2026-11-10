/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumEntropy.EntropyCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped BigOperators Matrix ComplexOrder
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

noncomputable section

namespace Qatlib.Papers.CommutingLLL13.MainResults.Defs

variable {D : Type} [Fintype D] [DecidableEq D]

def IsProjector (P : Matrix D D ℂ) : Prop := P.PosSemidef ∧ P * P = P

def rankAtMost (P : Matrix D D ℂ) (r : ℕ) : Prop := Matrix.rank P ≤ r

structure QSatParams where

  n : ℕ

  m : ℕ

  k : ℕ

  r : ℕ

  g : ℕ

  hr : 0 < r

structure QSatFamily (D : Type) [Fintype D] [DecidableEq D] (m : ℕ) where

  P : Fin m → Matrix D D ℂ

  isProj : ∀ i, IsProjector (P i)

def CommutingFamily {m : ℕ} (F : QSatFamily D m) : Prop :=
  ∀ i j, F.P i * F.P j = F.P j * F.P i

def SatisfiesMat {m : ℕ} (M : Matrix D D ℂ) (F : QSatFamily D m) : Prop :=
  ∀ i, F.P i * M = 0

def Satisfies {m : ℕ} (ρ : Density D) (F : QSatFamily D m) : Prop :=
  SatisfiesMat ρ.val F

noncomputable def etaNatural (δ k r g : ℝ) : ℝ :=
  1 / (δ * (k - Real.log (g * r * Real.exp 1)))

noncomputable def thresholdNatural (m : ℕ) (η : ℝ) : ℕ :=
  Nat.ceil (4 * (m : ℝ) * η * Real.log (η + 2))

def zeroPostselect {m : ℕ} (F : QSatFamily D m) (i0 : Fin m) (M : Matrix D D ℂ) :
    Matrix D D ℂ :=
  (1 - F.P i0) * M * (1 - F.P i0)

theorem zeroPostselect_satisfies_own {m : ℕ} (F : QSatFamily D m) (i0 : Fin m)
    (M : Matrix D D ℂ) :
    F.P i0 * zeroPostselect F i0 M = 0 := by
  have hsq : F.P i0 * F.P i0 = F.P i0 := (F.isProj i0).2
  have h1 : F.P i0 * (1 - F.P i0) = 0 := by
    rw [Matrix.mul_sub, mul_one, hsq, sub_self]
  calc F.P i0 * zeroPostselect F i0 M
      = (F.P i0 * (1 - F.P i0)) * M * (1 - F.P i0) := by
        simp only [zeroPostselect]
        noncomm_ring
    _ = 0 := by rw [h1]; simp

theorem zeroPostselect_preserves {m : ℕ} (F : QSatFamily D m) (hcomm : CommutingFamily F)
    (i0 j : Fin m) (M : Matrix D D ℂ) (hM : F.P j * M = 0) :
    F.P j * zeroPostselect F i0 M = 0 := by
  have hc : F.P j * (1 - F.P i0) = (1 - F.P i0) * F.P j := by
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, one_mul, hcomm j i0]
  calc F.P j * zeroPostselect F i0 M
      = (F.P j * (1 - F.P i0)) * M * (1 - F.P i0) := by
        simp only [zeroPostselect]
        noncomm_ring
    _ = ((1 - F.P i0) * F.P j) * M * (1 - F.P i0) := by rw [hc]
    _ = (1 - F.P i0) * (F.P j * M) * (1 - F.P i0) := by noncomm_ring
    _ = 0 := by rw [hM]; simp

theorem zeroSweep_preserves {m : ℕ} (F : QSatFamily D m) (hcomm : CommutingFamily F)
    (l : List (Fin m)) (M : Matrix D D ℂ) (hM : SatisfiesMat M F) :
    SatisfiesMat (l.foldr (zeroPostselect F) M) F := by
  induction l with
  | nil => exact hM
  | cons i0 rest ih =>
    simp only [List.foldr_cons]
    intro j
    exact zeroPostselect_preserves F hcomm i0 j (rest.foldr (zeroPostselect F) M) (ih j)

end Qatlib.Papers.CommutingLLL13.MainResults.Defs
