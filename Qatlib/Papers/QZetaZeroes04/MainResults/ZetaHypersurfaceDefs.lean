/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs

open Matrix
open scoped BigOperators

def planeCount (q n s : ℕ) : ℝ := ((q : ℝ) ^ (s * n) - 1) / ((q : ℝ) ^ s - 1)

def rootRadius (q n : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ (n - 1))

theorem rootRadius_pos {q n : ℕ} (hq : 2 ≤ q) : 0 < rootRadius q n := by
  unfold rootRadius
  apply Real.sqrt_pos.mpr
  have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  exact pow_pos this _

structure ZetaHypersurface where

  q : ℕ

  q_ge_two : 2 ≤ q

  m : ℕ

  m_ge_two : 2 ≤ m

  n : ℕ

  n_ge_one : 1 ≤ n

  rootCount : ℕ

  rootCount_pos : 0 < rootCount

  rootCount_le : rootCount ≤ m ^ n

  alpha : Fin rootCount → ℂ

  alpha_ne_zero : ∀ j, alpha j ≠ 0

  alpha_norm : ∀ j, ‖alpha j‖ = rootRadius q n

  traceMean : ℝ

  traceMean_bound : |traceMean| ≤ 1

namespace ZetaHypersurface

variable (H : ZetaHypersurface)

def zetaRoot (j : Fin H.rootCount) : ℂ := 1 / H.alpha j

def eigenPhase (j : Fin H.rootCount) : ℂ :=
  H.zetaRoot j / ((‖H.zetaRoot j‖ : ℝ) : ℂ)

def zetaCircuit : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ :=
  Matrix.diagonal H.eigenPhase

def planeCountOf (s : ℕ) : ℝ := planeCount H.q H.n s

def firstPointCount : ℝ :=
  H.planeCountOf 1
    - (-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ) * H.traceMean

def pointCountEstimate (est : ℝ) : ℝ :=
  H.planeCountOf 1
    - (-1 : ℝ) ^ H.n * rootRadius H.q H.n * (H.rootCount : ℝ) * est

end ZetaHypersurface

structure ZetaUnitaryCostAnnotation (H : ZetaHypersurface) where

  size : ℕ

  unitary : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ

  isUnitary : unitary ∈ Matrix.unitaryGroup (Fin H.rootCount) ℂ

def HasPolynomialCostAnnotation (H : ZetaHypersurface)
    (U : Matrix (Fin H.rootCount) (Fin H.rootCount) ℂ) : Prop :=
  ∃ (C : ZetaUnitaryCostAnnotation H) (c k : ℕ), 0 < c ∧ 0 < k ∧ C.unitary = U ∧
    C.size ≤ c * ((Nat.log 2 H.q + 1) * (H.n * (Nat.log 2 H.m + 1))) ^ k

end Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
