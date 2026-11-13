/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Mathlib.Logic.Equiv.Set

/-!
# Three-wire unitary gates

This module defines `Phi3Gate`, a unitary on three distinct selected wires, and its action on a
larger qubit register. The ambient matrix acts as the local unitary tensored with the identity
on the remaining wires, following the circuit framework of [BarencoEtAl1995].

Lists of these gates compile to unitary circuits with no oracle queries and exactly one circuit
gate per list entry.

## Main statements

* `phi3GateMatrix_tensor`: expresses the ambient matrix through a tensor product and relabeling.
* `phi3GateMatrix_unitary`: the ambient gate is unitary.
* `phi3Compile_count`: compilation preserves list length as gate count and uses no queries.
* `isUnitaryCircuit_phi3Compile`: every compiled gate list is unitary.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CircuitImpl.Phi3Universal

open Matrix

/-- A unitary matrix on three qubits together with three distinct selected wires in an ambient
register. -/
structure Phi3Gate (n : ℕ) where

  wires : Fin 3 → Fin n

  wires_inj : Function.Injective wires

  localMatrix : Matrix (Reg 3) (Reg 3) ℂ

  localMatrix_unitary : localMatrix ∈ Matrix.unitaryGroup (Reg 3) ℂ

/-- The ambient matrix applying the local three-qubit unitary and leaving every unselected wire
unchanged. -/
def phi3GateMatrix {n : ℕ} (g : Phi3Gate n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y =>
    if (∀ w : Fin n, (∀ q : Fin 3, g.wires q ≠ w) → x w = y w) then
      g.localMatrix (fun q => x (g.wires q)) (fun q => y (g.wires q))
    else 0

/-- Compiles a list of three-wire unitary gates into the corresponding circuit gate steps. -/
def phi3Compile {n : ℕ} (gs : List (Phi3Gate n)) : Circuit (Reg n) :=
  gs.map (fun g => Step.gate (phi3GateMatrix g))

/-- Splits an ambient register into the three selected bits and the bits on their complement. -/
private def phi3Split {n : ℕ} (w : Fin 3 → Fin n) (hw : Function.Injective w) :
    Reg n ≃ Reg 3 × ({k : Fin n // k ∉ Set.range w} → Bool) :=
  (Equiv.piEquivPiSubtypeProd (fun k => k ∈ Set.range w) (fun _ => Bool)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective w hw).symm (Equiv.refl Bool))
      (Equiv.refl _))

/-- Agreement outside the selected wires is equivalent to equality of the restrictions to their
complement. -/
private theorem phi3Off_iff {n : ℕ} (w : Fin 3 → Fin n) (x y : Reg n) :
    (∀ k : Fin n, (∀ q : Fin 3, w q ≠ k) → x k = y k) ↔
      (fun k : {k : Fin n // k ∉ Set.range w} => x k) = (fun k : {k : Fin n // k ∉ Set.range w} => y k) := by
  constructor
  · intro h
    funext k
    exact h k (fun q hq => k.property ⟨q, hq⟩)
  · intro h k hk
    have hkr : k ∉ Set.range w := by
      rintro ⟨q, hq⟩
      exact hk q hq
    exact congrFun h ⟨k, hkr⟩

/-- The ambient three-wire gate is the relabeled tensor product of its local matrix with the
identity on the complementary wires. -/
private theorem phi3GateMatrix_tensor {n : ℕ} (g : Phi3Gate n) :
    phi3GateMatrix g = relabelGate (phi3Split g.wires g.wires_inj).symm
      (TensorGate g.localMatrix (1 : Matrix ({k : Fin n // k ∉ Set.range g.wires} → Bool)
        ({k : Fin n // k ∉ Set.range g.wires} → Bool) ℂ)) := by
  classical
  ext x y
  simp only [phi3GateMatrix, Matrix.of_apply, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, TensorGate, Matrix.kroneckerMap_apply]
  change (if (∀ k, (∀ q, g.wires q ≠ k) → x k = y k) then
    g.localMatrix (fun q => x (g.wires q)) (fun q => y (g.wires q)) else 0) =
    g.localMatrix (fun q => x (g.wires q)) (fun q => y (g.wires q)) *
      (1 : Matrix ({k : Fin n // k ∉ Set.range g.wires} → Bool)
        ({k : Fin n // k ∉ Set.range g.wires} → Bool) ℂ) (fun k : {k : Fin n // k ∉ Set.range g.wires} => x k)
        (fun k : {k : Fin n // k ∉ Set.range g.wires} => y k)
  rw [Matrix.one_apply]
  by_cases h : ∀ k : Fin n, (∀ q : Fin 3, g.wires q ≠ k) → x k = y k
  · rw [if_pos h, if_pos ((phi3Off_iff g.wires x y).mp h), mul_one]
  · rw [if_neg h, if_neg (fun he => h ((phi3Off_iff g.wires x y).mpr he)), mul_zero]

/-- The ambient matrix of a three-wire gate is unitary. -/
theorem phi3GateMatrix_unitary {n : ℕ} (g : Phi3Gate n) :
    phi3GateMatrix g ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  classical
  rw [phi3GateMatrix_tensor]
  exact (relabelGate_mem_unitaryGroup _ _).mpr
    (tensorGate_unitary g.localMatrix_unitary (Submonoid.one_mem _))

/-- Compiling three-wire gates uses no oracle queries and has gate count equal to the list
length. -/
theorem phi3Compile_count {n : ℕ} (gs : List (Phi3Gate n)) :
    QueryCount (phi3Compile gs) = 0 ∧ GateCount (phi3Compile gs) = gs.length := by
  induction gs with
  | nil => simp [phi3Compile]
  | cons g gs ih => simp [phi3Compile] at ih ⊢; exact ih

/-- The circuit compiled from any list of three-wire unitary gates is unitary. -/
theorem isUnitaryCircuit_phi3Compile {n : ℕ} (gs : List (Phi3Gate n)) :
    IsUnitaryCircuit (phi3Compile gs) := by
  induction gs with
  | nil => simp [phi3Compile]
  | cons g gs ih =>
    simpa only [phi3Compile, List.map_cons, isUnitaryCircuit_gate] using
      And.intro (phi3GateMatrix_unitary g) ih

end Qatlib.Concepts.CircuitImpl.Phi3Universal
