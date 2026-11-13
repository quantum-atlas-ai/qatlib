/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.WireContextData
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis

/-!
# Transporting circuits into a wire context

This module proves that `wireContextExtend` and `wireContextEmbed` preserve the selected
register while fixing the surrounding wires. Legal reflection-gate programs commute with this
embedding, including on finite sums of states with different surrounding registers. This
formalizes the register-extension reasoning used in [NielsenChuang2010].

## Main statements

* `wire_context_program`: execution commutes with embedding into selected wires.
* `wire_context_inner`: each fixed-context embedding preserves inner products.
* `wire_context_orthogonal`: contexts differing on an unselected wire give orthogonal states.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Extending a register along the wire injection recovers each original bit on its selected
wire. -/
private theorem wc_at {a L : ℕ} (e : Fin a ↪ Fin L) (s : Reg L) (x : Reg a) (i : Fin a) :
    wireContextExtend e s x (e i) = x i := e.injective.extend_apply _ _ _

/-- On a wire outside the injection's image, an extended register equals the fixed surrounding
register. -/
private theorem wc_out {a L : ℕ} (e : Fin a ↪ Fin L) (s : Reg L) (x : Reg a)
    (j : Fin L) (hj : ¬ ∃ i, e i=j) : wireContextExtend e s x j = s j :=
  Function.extend_apply' _ _ j hj

/-- Register extension agrees with the input on selected wires and with the fixed context
elsewhere, and is injective. -/
theorem wire_context_extend (a L : ℕ) (e : Fin a ↪ Fin L) (s : Reg L) :
    (∀ x i, wireContextExtend e s x (e i) = x i) ∧
      (∀ x j, (¬ ∃ i, e i=j) → wireContextExtend e s x j = s j) ∧
      Function.Injective (wireContextExtend e s) := by
  refine ⟨wc_at e s,wc_out e s,?_⟩
  intro x y h
  funext i
  simpa only [wc_at] using! congrFun h (e i)

/-- Updating a selected bit after register extension equals extending the correspondingly
updated smaller register. -/
theorem wire_context_update (a L : ℕ) (e : Fin a ↪ Fin L) (s : Reg L)
    (x : Reg a) (t : Fin a) (v : Bool) :
    Function.update (wireContextExtend e s x) (e t) v =
      wireContextExtend e s (Function.update x t v) := by
  funext j
  by_cases hj : ∃ i, e i=j
  · obtain ⟨i,rfl⟩ := hj
    by_cases hi : i=t
    · subst i
      simp only [wc_at,Function.update_self]
    · rw [Function.update_of_ne (fun h => hi (e.injective h)),wc_at,wc_at,Function.update_of_ne hi]
  · have hn : j ≠ e t := fun h => hj ⟨t,h.symm⟩
    rw [Function.update_of_ne hn,wc_out e s x j hj,wc_out e s (Function.update x t v) j hj]

/-- The wire-context embedding sends a computational basis ket to the ket of its extended
register. -/
theorem wire_context_ket {a L : ℕ} (e : Fin a ↪ Fin L) (s : Reg L) (x : Reg a) :
    wireContextEmbed e s (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s x) := by
  simp [wireContextEmbed,Qatlib.Foundations.PureStateMath.Ket]

/-- The wire-context embedding commutes with complex scalar multiplication. -/
private theorem wc_smul {a L : ℕ} (e : Fin a ↪ Fin L) (s : Reg L) (z : ℂ) (ψ : QState (Reg a)) :
    wireContextEmbed e s (z • ψ) = z • wireContextEmbed e s ψ := by
  simp [wireContextEmbed,Finset.smul_sum,smul_smul]

/-- The wire-context embedding commutes with finite sums of states. -/
private theorem wc_sum {a L : ℕ} {J : Type} [Fintype J] (e : Fin a ↪ Fin L) (s : Reg L)
    (ψ : J → QState (Reg a)) : wireContextEmbed e s (∑ j, ψ j) = ∑ j, wireContextEmbed e s (ψ j) := by
  simp only [wireContextEmbed,Finset.sum_apply,Finset.sum_smul]
  exact Finset.sum_comm

/-- Applying a legally mapped reflection gate to an extended basis ket equals embedding the
original gate's action on that ket. -/
private theorem wc_gate_ket {a L : ℕ} (e : Fin a ↪ Fin L) (s : Reg L)
    (g : ReflectionGate a) (hg : reflectionGateLegal g) (x : Reg a) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s x)) =
      wireContextEmbed e s (ApplyGate (reflectionGateMatrix g) (Qatlib.Foundations.PureStateMath.Ket x)) := by
  rcases g with ⟨t,U⟩ | ⟨c,t⟩
  · simp only [knownWireGateMap,reflectionGateMatrix,applyGate_wireGate_ket,wc_at,wire_context_update]
    rw [show wireContextEmbed e s
      (U false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false)+U true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true)) =
      wireContextEmbed e s (U false (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t false))+
        wireContextEmbed e s (U true (x t) • Qatlib.Foundations.PureStateMath.Ket (Function.update x t true)) by
          simp [wireContextEmbed,add_smul,Finset.sum_add_distrib]]
    simp only [wc_smul,wire_context_ket]
  · simp only [knownWireGateMap,reflectionGateMatrix]
    rw [applyGate_cnotGate_ket L (e c) (e t) (fun h => hg (e.injective h)),
      applyGate_cnotGate_ket a c t hg,wire_context_ket,wc_at,wire_context_update]
    simp only [wc_at]

/-- A legal reflection gate mapped along the wire injection commutes with the wire-context state
embedding. -/
private theorem wc_gate {a L : ℕ} (e : Fin a ↪ Fin L) (s : Reg L)
    (g : ReflectionGate a) (hg : reflectionGateLegal g) (ψ : QState (Reg a)) :
    ApplyGate (reflectionGateMatrix (knownWireGateMap e g)) (wireContextEmbed e s ψ) =
      wireContextEmbed e s (ApplyGate (reflectionGateMatrix g) ψ) := by
  conv_rhs => arg 3; arg 2; rw [state_ket_expansion ψ]
  simp only [ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul,wc_sum,wc_smul]
  change reflectionGateMatrix (knownWireGateMap e g) *ᵥ
    (∑ x, ψ x • Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s x)) = _
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  rw [show reflectionGateMatrix (knownWireGateMap e g) *ᵥ Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s x) =
    wireContextEmbed e s (reflectionGateMatrix g *ᵥ Qatlib.Foundations.PureStateMath.Ket x) from wc_gate_ket e s g hg x]

/-- Execution of a legal reflection-gate program commutes with embedding the state and mapping
the program along the wire injection. -/
theorem wire_context_program (a L : ℕ) (e : Fin a ↪ Fin L) (s : Reg L)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs) (ψ : QState (Reg a)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap e))) (wireContextEmbed e s ψ) =
      wireContextEmbed e s (Run 1 (reflectionCompile gs) ψ) := by
  induction gs generalizing ψ with
  | nil => simp [reflectionCompile]
  | cons g gs ih =>
    simp only [List.map_cons,reflectionCompile,List.map_cons,run_gate]
    rw [wc_gate e s g (hgs g List.mem_cons_self)]
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) _

/-- A mapped legal reflection program acts termwise on a finite sum of states embedded with
possibly different surrounding registers. -/
theorem wire_context_program_family (a L : ℕ) (e : Fin a ↪ Fin L)
    (gs : List (ReflectionGate a)) (hgs : reflectionLegal gs)
    (S : Type) [Fintype S] (s : S → Reg L) (ψ : S → QState (Reg a)) :
    Run 1 (reflectionCompile (gs.map (knownWireGateMap e))) (∑ t, wireContextEmbed e (s t) (ψ t)) =
      ∑ t, wireContextEmbed e (s t) (Run 1 (reflectionCompile gs) (ψ t)) := by
  rw [run_reflectionCompile_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact wire_context_program a L e (s t) gs hgs (ψ t)

/-- Expand the inner product of two wire-context embeddings as a double sum of basis-ket inner
products weighted by their state coefficients. -/
private theorem wc_inner_expansion {a L : ℕ} (e : Fin a ↪ Fin L) (s t : Reg L)
    (ψ φ : QState (Reg a)) :
    Qatlib.Foundations.PureStateMath.Inner (wireContextEmbed e s ψ) (wireContextEmbed e t φ) =
      ∑ v, ∑ u, φ v * (star (ψ u) *
        Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s u)) (Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e t v))) := by
  simp only [wireContextEmbed,Qatlib.Foundations.PureStateMath.Inner,star_sum,star_smul,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  simp_rw [Finset.mul_sum]

/-- Embedding two states into the same wire context preserves their inner product. -/
theorem wire_context_inner (a L : ℕ) (e : Fin a ↪ Fin L) (s : Reg L)
    (ψ φ : QState (Reg a)) :
    Qatlib.Foundations.PureStateMath.Inner (wireContextEmbed e s ψ) (wireContextEmbed e s φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  rw [wc_inner_expansion]
  simp_rw [inner_ket_ket,(wire_context_extend a L e s).2.2.eq_iff]
  simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct,mul_comm]

/-- States embedded in contexts that differ on a wire outside the selected image have zero inner
product. -/
theorem wire_context_orthogonal (a L : ℕ) (e : Fin a ↪ Fin L) (s t : Reg L)
    (j : Fin L) (hj : ¬ ∃ i, e i=j) (hst : s j ≠ t j) (ψ φ : QState (Reg a)) :
    Qatlib.Foundations.PureStateMath.Inner (wireContextEmbed e s ψ) (wireContextEmbed e t φ) = 0 := by
  have hn (u v : Reg a) : wireContextExtend e s u ≠ wireContextExtend e t v := by
    intro h
    apply hst
    simpa only [wc_out e s u j hj,wc_out e t v j hj] using! congrFun h j
  rw [wc_inner_expansion]
  simp only [inner_ket_ket,hn,ite_false,mul_zero,Finset.sum_const_zero]

end Qatlib.Concepts.MatrixAccess.RitzPipeline
