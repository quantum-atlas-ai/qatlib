/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem1Afas
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit

theorem rotationMatrix_entries (n : ℕ) (i j : Reg n) :
    ZeroPhaseReflection n i j =
      if i = j then (if i = ZeroStr n then (1 : ℂ) else -1) else 0 := by
  rw [ZeroPhaseReflection, Matrix.diagonal_apply]

theorem walshHadamard_entries (n : ℕ) (i j : Reg n) :
    HadamardN n i j =
      ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ∏ k, (if i k && j k then (-1 : ℂ) else 1) :=
  hadamardN_apply i j

theorem diffusion_entries (n : ℕ) (i j : Reg n) :
    Diffusion (Reg n) i j =
      if i = j then (-1 + 2 / ((2 : ℂ) ^ n)) else (2 / ((2 : ℂ) ^ n)) := by
  have hN : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  unfold Diffusion AverageProjection
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.one_apply, card_reg, Nat.cast_pow, Nat.cast_ofNat]
  split_ifs <;> field_simp <;> ring

theorem theorem1_factorization (n : ℕ) :
    Diffusion (Reg n) = HadamardN n * ZeroPhaseReflection n * HadamardN n :=
  theorem1 n

theorem run_expandedDiffusion (n j : ℕ) (O : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    Run O (ExpandedCircuit n j) ψ = Run O (GroverCircuit (Reg n) j) ψ :=
  run_expandedCircuit n j O ψ

theorem queryCount_expandedCircuit (n j : ℕ) :
    QueryCount (ExpandedCircuit n j) = j :=
  (expandedCircuit_counts n j).1

theorem gateCount_expandedCircuit (n j : ℕ) :
    GateCount (ExpandedCircuit n j) = 3 * j :=
  (expandedCircuit_counts n j).2.1

end Qatlib.Papers.GroverSearch96.MainResults
