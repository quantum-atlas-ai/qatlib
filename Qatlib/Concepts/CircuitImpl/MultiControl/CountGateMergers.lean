/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliGadget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Matrix
open scoped Classical BigOperators

private theorem matrix_eq_of_ket_action {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (h : ∀ x, ApplyGate A (Qatlib.Foundations.PureStateMath.Ket x) = ApplyGate B (Qatlib.Foundations.PureStateMath.Ket x)) : A=B := by
  ext y x
  have hh := congrFun (h x) y
  simpa [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using! hh

theorem source_wireGate_commute {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (U V : Matrix Bool Bool ℂ) :
    wireGate N a U * wireGate N b V = wireGate N b V * wireGate N a U := by
  apply matrix_eq_of_ket_action
  intro x
  simp only [applyGate_mul, applyGate_wireGate_ket, reflectionApplyGate_add,
    reflectionApplyGate_smul, Function.update_of_ne hab,
    Function.update_of_ne hab.symm, smul_add, smul_smul]
  rw [Function.update_comm hab, Function.update_comm hab,
    Function.update_comm hab, Function.update_comm hab]
  module

theorem source_cnot_wireGate_commute {N : ℕ} (a b w : Fin N)
    (hab : a ≠ b) (hwa : w ≠ a) (hwb : w ≠ b) (U : Matrix Bool Bool ℂ) :
    cnotGate N a b * wireGate N w U = wireGate N w U * cnotGate N a b := by
  apply matrix_eq_of_ket_action
  intro x
  simp only [applyGate_mul, applyGate_wireGate_ket, reflectionApplyGate_add,
    reflectionApplyGate_smul, applyGate_cnotGate_ket N a b hab,
    Function.update_of_ne hwa.symm, Function.update_of_ne hwb.symm,
    Function.update_of_ne hwb]
  rw [Function.update_comm hwb, Function.update_comm hwb]

theorem source_cnot_control_phase_commute {N : ℕ} (a b : Fin N)
    (hab : a ≠ b) (d : Bool → ℂ) :
    cnotGate N a b * wireGate N a (diagonal d) =
      wireGate N a (diagonal d) * cnotGate N a b := by
  apply matrix_eq_of_ket_action
  intro x
  have hd (y : Reg N) : ApplyGate (wireGate N a (diagonal d)) (Qatlib.Foundations.PureStateMath.Ket y) = d (y a) • Qatlib.Foundations.PureStateMath.Ket y := by
    rw [applyGate_wireGate_ket]
    have hup : Function.update y a (y a) = y := Function.update_eq_self a y
    cases hy : y a <;> simp only [Matrix.diagonal_apply, hy, if_true, if_false,
      Bool.false_eq_true, Bool.true_eq_false, zero_smul, add_zero, zero_add]
    all_goals rw [hy] at hup; rw [hup]
  simp only [applyGate_mul, hd, reflectionApplyGate_smul,
    applyGate_cnotGate_ket N a b hab, Function.update_of_ne hab]

theorem source_wireGate_commute_table {N : ℕ} (w : Fin N) (U : Matrix Bool Bool ℂ)
    (gs : List (ReflectionGate N)) (hgs : reflectionLegal gs)
    (havoid : ∀ g ∈ gs, w ∉ reflectionGateWires g) :
    wireGate N w U * reflectionProgramMatrix gs =
      reflectionProgramMatrix gs * wireGate N w U := by
  induction gs with
  | nil => simp [reflectionProgramMatrix]
  | cons g gs ih =>
    have htail : reflectionLegal gs := fun q hq => hgs q (List.mem_cons_of_mem _ hq)
    have hat : ∀ q ∈ gs, w ∉ reflectionGateWires q :=
      fun q hq => havoid q (List.mem_cons_of_mem _ hq)
    have hg := hgs g List.mem_cons_self
    have ha := havoid g List.mem_cons_self
    have hc : wireGate N w U * reflectionGateMatrix g =
        reflectionGateMatrix g * wireGate N w U := by
      rcases g with ⟨v,V⟩ | ⟨a,b⟩
      · exact source_wireGate_commute w v (by simpa [reflectionGateWires] using! ha) U V
      · have hav : w ≠ a ∧ w ≠ b := by simpa [reflectionGateWires] using! ha
        exact (source_cnot_wireGate_commute a b w hg hav.1 hav.2 U).symm
    simp only [reflectionProgramMatrix]
    rw [← Matrix.mul_assoc, ih htail hat, Matrix.mul_assoc, hc, ← Matrix.mul_assoc]

theorem source_controlPhase_commute_table {N : ℕ} (w : Fin N) (d : Bool → ℂ)
    (gs : List (ReflectionGate N)) (hgs : reflectionLegal gs)
    (havoid : ∀ g ∈ gs, match g with
      | .inl (v,_) => w ≠ v
      | .inr (_,t) => w ≠ t) :
    wireGate N w (diagonal d) * reflectionProgramMatrix gs =
      reflectionProgramMatrix gs * wireGate N w (diagonal d) := by
  induction gs with
  | nil => simp [reflectionProgramMatrix]
  | cons g gs ih =>
    have htail : reflectionLegal gs := fun q hq => hgs q (List.mem_cons_of_mem _ hq)
    have hat : ∀ q ∈ gs, match q with
      | .inl (v,_) => w ≠ v
      | .inr (_,t) => w ≠ t := fun q hq => havoid q (List.mem_cons_of_mem _ hq)
    have hg := hgs g List.mem_cons_self
    have ha := havoid g List.mem_cons_self
    have hc : wireGate N w (diagonal d) * reflectionGateMatrix g =
        reflectionGateMatrix g * wireGate N w (diagonal d) := by
      rcases g with ⟨v,V⟩ | ⟨a,b⟩
      · exact source_wireGate_commute w v ha _ V
      · by_cases hwa : w = a
        · subst w
          exact (source_cnot_control_phase_commute a b hg d).symm
        · exact (source_cnot_wireGate_commute a b w hg hwa ha _).symm
    simp only [reflectionProgramMatrix]
    rw [← Matrix.mul_assoc, ih htail hat, Matrix.mul_assoc, hc, ← Matrix.mul_assoc]

theorem source_slide_gate {N : ℕ} (g : ReflectionGate N)
    (xs ys : List (ReflectionGate N))
    (hcomm : reflectionGateMatrix g * reflectionProgramMatrix xs =
      reflectionProgramMatrix xs * reflectionGateMatrix g) :
    reflectionProgramMatrix (xs ++ [g] ++ ys) =
      reflectionProgramMatrix ([g] ++ xs ++ ys) := by
  simp only [reflectionProgramMatrix_append, reflectionProgramMatrix,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [hcomm]

theorem source_merge_singles {N : ℕ} (w : Fin N) (U V : Matrix Bool Bool ℂ)
    (xs ys : List (ReflectionGate N)) :
    reflectionProgramMatrix (xs ++ [.inl (w,U), .inl (w,V)] ++ ys) =
      reflectionProgramMatrix (xs ++ [.inl (w,V*U)] ++ ys) := by
  simp only [reflectionProgramMatrix_append, reflectionProgramMatrix,
    reflectionGateMatrix, Matrix.one_mul]
  rw [← Matrix.mul_assoc, wireGate_mul, Matrix.mul_assoc]

theorem source_run_smul {N : ℕ} (gs : List (ReflectionGate N))
    (z : ℂ) (ψ : QState (Reg N)) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (z • ψ) =
      z • Run 1 (reflectionCompile gs) ψ := by
  simp only [run_reflectionCompile, reflectionApplyGate_smul]

theorem source_adjoint_after {N : ℕ} (gs : List (ReflectionGate N))
    (hgs : reflectionLegal gs) (ψ : QState (Reg N)) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint gs))
      (Run 1 (reflectionCompile gs) ψ) = ψ := by
  rw [run_reflectionCompile, run_reflectionCompile, reflectionAdjoint_matrix gs hgs,
    ← applyGate_mul]
  have hu : (reflectionProgramMatrix gs)ᴴ * reflectionProgramMatrix gs = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using!
      Matrix.mem_unitaryGroup_iff'.mp (reflectionProgramMatrix_unitary gs hgs)
  rw [hu, applyGate_one]

theorem source_adjoint_avoids {N : ℕ} (gs : List (ReflectionGate N)) (z : Fin N)
    (havoid : ∀ g ∈ gs, z ∉ reflectionGateWires g) :
    ∀ g ∈ reflectionAdjoint gs, z ∉ reflectionGateWires g := by
  intro g hg
  change g ∈ List.map reflectionGateAdjoint gs.reverse at hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  have ha := havoid q (List.mem_reverse.mp hq)
  rcases q with ⟨w,U⟩ | ⟨a,b⟩ <;>
    simpa only [reflectionGateAdjoint, reflectionGateWires] using! ha

theorem source_adjoint_involutive_action {N : ℕ} (gs : List (ReflectionGate N))
    (hgs : reflectionLegal gs) (F : Reg N → Reg N) (hF : Function.Involutive F)
    (hrun : ∀ x, Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (F x))
    (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint gs)) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (F x) := by
  have h := source_adjoint_after gs hgs (Qatlib.Foundations.PureStateMath.Ket (F x))
  rw [hrun, hF x] at h
  exact h

private theorem wire_flip_ket {N : ℕ} (t : Fin N) (x : Reg N) :
    ApplyGate (wireGate N t PauliX) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (!x t)) := by
  rw [applyGate_wireGate_ket]
  cases hx : x t <;> simp [PauliX, permMatrix, hx]

theorem source_signed_spectator_forward {N : ℕ} (gs : List (ReflectionGate N))
    (hgs : reflectionLegal gs) (t : Fin N) (havoid : ∀ g ∈ gs, t ∉ reflectionGateWires g)
    (x y : Reg N) (z : ℂ) (hyt : y t = x t)
    (hrun : Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) = z • Qatlib.Foundations.PureStateMath.Ket y)
    (v : Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket (Function.update x t v)) =
      z • Qatlib.Foundations.PureStateMath.Ket (Function.update y t v) := by
  have hc := source_wireGate_commute_table t PauliX gs hgs havoid
  have hh : Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs)
      (ApplyGate (wireGate N t PauliX) (Qatlib.Foundations.PureStateMath.Ket x)) =
      ApplyGate (wireGate N t PauliX) (Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x)) := by
    simp only [run_reflectionCompile, ← applyGate_mul]
    rw [hc]
  rw [wire_flip_ket, hrun, reflectionApplyGate_smul, wire_flip_ket, hyt] at hh
  by_cases hv : v = x t
  · rw [hv, Function.update_eq_self, hrun, ← hyt, Function.update_eq_self]
  · have hvf : v = !x t := by cases v <;> cases hx : x t <;> simp_all
    rw [hvf]
    exact hh

theorem source_signed_spectator_inverse {N : ℕ} (gs : List (ReflectionGate N))
    (hgs : reflectionLegal gs) (t : Fin N) (havoid : ∀ g ∈ gs, t ∉ reflectionGateWires g)
    (x y : Reg N) (z : ℂ) (hz : z*z=1) (hyt : y t = x t)
    (hrun : Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) = z • Qatlib.Foundations.PureStateMath.Ket y)
    (v : Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (reflectionAdjoint gs))
      (Qatlib.Foundations.PureStateMath.Ket (Function.update y t v)) = z • Qatlib.Foundations.PureStateMath.Ket (Function.update x t v) := by
  have hh :=
      source_adjoint_after gs hgs
      (Qatlib.Foundations.PureStateMath.Ket (Function.update x t v))
  rw [source_signed_spectator_forward gs hgs t havoid x y z hyt hrun v, source_run_smul] at hh
  have hs := congrArg (fun ψ : QState (Reg N) => z • ψ) hh
  simpa only [smul_smul, hz, one_smul] using! hs

theorem source_quad_matrix_congr {N : ℕ} (as bs xs ys : List (ReflectionGate N))
    (has : reflectionLegal as) (hbs : reflectionLegal bs) (hxs : reflectionLegal xs) (hys : reflectionLegal ys)
    (hA : reflectionProgramMatrix as = reflectionProgramMatrix xs)
    (hB : reflectionProgramMatrix bs = reflectionProgramMatrix ys) :
    reflectionProgramMatrix (as ++ bs ++ reflectionAdjoint as ++ reflectionAdjoint bs) =
      reflectionProgramMatrix (xs ++ ys ++ reflectionAdjoint xs ++ reflectionAdjoint ys) := by
  have factor (a b : List (ReflectionGate N)) (ha : reflectionLegal a) (hb : reflectionLegal b) :
      reflectionProgramMatrix (a ++ b ++ reflectionAdjoint a ++ reflectionAdjoint b) =
        (reflectionProgramMatrix b)ᴴ*((reflectionProgramMatrix a)ᴴ*(reflectionProgramMatrix b*reflectionProgramMatrix a)) := by
    rw [reflectionProgramMatrix_append, reflectionProgramMatrix_append, reflectionProgramMatrix_append,
      reflectionAdjoint_matrix a ha, reflectionAdjoint_matrix b hb]
  exact (factor as bs has hbs).trans
    ((congrArg₂ (fun A B : Matrix (Reg N) (Reg N) ℂ => Bᴴ*(Aᴴ*(B*A))) hA hB).trans (factor xs ys hxs hys).symm)

end Qatlib.Concepts.CircuitImpl.MultiControl
