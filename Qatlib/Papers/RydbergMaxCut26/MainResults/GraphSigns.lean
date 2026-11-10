/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalRatios
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib MeasureTheory
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MainResults.GraphSigns
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Ground
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped

theorem zero_weights {E : Type*} [Fintype E] (w : E → ℝ) (hw : ∀ e,0 ≤ w e)
    (hW : ∑ e,w e=0) (e : E) : w e=0 := by
  have h := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => hw i) (Finset.mem_univ e)
  rw [hW] at h
  exact le_antisymm h (hw e)

theorem zero_graph_energy {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (w : E → ℝ) (hw : ∀ e,0 ≤ w e) (hW : ∑ e,w e=0) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (qmcHamiltonian ends w) ρ=0 := by
  simp only [qmcHamiltonian,zero_weights w hw hW,zero_smul,Finset.sum_const_zero,smul_zero,
    energy,Matrix.zero_mul,Matrix.trace_zero,Complex.zero_re]

theorem ground_sign_split {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0 ≤ w e)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : GroundDensity (qmcHamiltonian ends w) ρQ) :
    (∑ e,w e=0 ∧ energy (qmcHamiltonian ends w) ρQ=0) ∨
      (0 < ∑ e,w e ∧ energy (qmcHamiltonian ends w) ρQ < 0) := by
  have hW : 0 ≤ ∑ e,w e := Finset.sum_nonneg (fun e _ => hw e)
  rcases eq_or_lt_of_le hW with hz|hp
  · exact Or.inl ⟨hz.symm,zero_graph_energy ends w hw hz.symm ρQ⟩
  · exact Or.inr ⟨hp,ground_energy_negative ends hends w hp ρQ hQ.2.2⟩

theorem physical_ratio {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n)
    (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hW : 0 < ∑ e,w e)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : GroundDensity (qmcHamiltonian ends w) ρQ)
    (Eout κ : ℝ) (hbound : Eout ≤ κ*energy (qmcHamiltonian ends w) ρQ) :
    κ ≤ Eout/energy (qmcHamiltonian ends w) ρQ :=
  ratio_of_energy _ _ _ (ground_energy_negative ends hends w hW ρQ hQ.2.2) hbound

theorem weaken_651_to_533 (Eout Eopt : ℝ) (hopt : Eopt ≤ 0)
    (h : Eout ≤ (651/1000:ℝ)*Eopt) : Eout ≤ (533/1000:ℝ)*Eopt :=
  weaken_energy Eout Eopt (651/1000) (533/1000) hopt h (by norm_num)
end Qatlib.Papers.RydbergMaxCut26.MainResults.GraphSigns
