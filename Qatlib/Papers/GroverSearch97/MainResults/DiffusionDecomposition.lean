/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Concepts.SearchStopping.KnownCount.Theorem1Afas
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.GroverSearch97.MainResults.DiffusionDecomposition

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem diffusion_entry (i j : I) :
    Diffusion I i j =
      (if i = j then (-1 + 2 / (Fintype.card I : ℂ)) else 2 / (Fintype.card I : ℂ)) := by
  simp only [Diffusion, AverageProjection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · rw [div_eq_mul_inv]; ring
  · rw [div_eq_mul_inv]; ring

theorem source_zeroPhaseReflection_diagonal (n : ℕ) :
    ZeroPhaseReflection n =
      Matrix.diagonal (fun x : Reg n => if x = ZeroStr n then (1 : ℂ) else -1) := rfl

theorem source_zeroPhaseReflection_entry (n : ℕ) (i j : Reg n) :
    ZeroPhaseReflection n i j =
      (if i = j then (if i = ZeroStr n then (1 : ℂ) else -1) else 0) := by
  simp only [ZeroPhaseReflection, Matrix.diagonal_apply]

theorem source_hadamardN_entry (n : ℕ) (y z : Reg n) :
    HadamardN n y z =
      ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ∏ i, (if y i && z i then (-1 : ℂ) else 1) :=
  hadamardN_apply y z

theorem source_diffusion_eq_wrw (n : ℕ) :
    Diffusion (Reg n) = HadamardN n * ZeroPhaseReflection n * HadamardN n :=
  diffusion_eq_hadamardN_zeroPhaseReflection n

theorem source_wrw_macro_unitary (n : ℕ) :
    IsUnitaryCircuit (DiffusionCircuit n) ∧
      QueryCount (DiffusionCircuit n) = 0 ∧ GateCount (DiffusionCircuit n) = 3 :=
  ⟨diffusionCircuit_valid n, diffusionCircuit_counts n⟩

theorem source_run_diffusionCircuit (n : ℕ) (O : Matrix (Reg n) (Reg n) ℂ)
    (ψ : QState (Reg n)) :
    Run O (DiffusionCircuit n) ψ = ApplyGate (Diffusion (Reg n)) ψ :=
  run_diffusionCircuit n O ψ

end Qatlib.Papers.GroverSearch97.MainResults.DiffusionDecomposition
