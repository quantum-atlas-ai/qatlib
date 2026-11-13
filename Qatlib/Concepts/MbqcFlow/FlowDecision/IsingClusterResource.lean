/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetwork
import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport

/-!
# Ising pulses and cluster resource phases

This module defines an edge-based diagonal pulse Hamiltonian, its time-`π` evolution
`sourcePulse`, and the associated uniform-input resource states. It relates this pulse to the
controlled-Z preparation of cluster resources in [RaussendorfBriegel2001] through an explicit
local Z frame determined by incoming-edge parity.

The circuit words `czWord` and `frameWord` implement the corresponding diagonal matrices.
Boolean phase identities describe how bit flips change the CZ and frame phases and give the
coordinate action of `stabilizer`.

## Main statements

* `sourcePulse_eq_frame_cz`: factorization of the source pulse into the frame and CZ matrices.
* `czMatrix_unitary` and `frameMatrix_unitary`: unitarity of both factors.
* `run_czWord` and `run_frameWord`: circuit execution identities.
* `czPhase_flip`: the CZ phase change under a bit flip for increasingly ordered edges.
* `apply_stabilizer`: the neighbor-phase formula for the stabilizer action.

## References

* [Raussendorf and Briegel, 2001][RaussendorfBriegel2001]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
open scoped Classical BigOperators

/-- The parity flag for the number of directed edges ending at vertex `v`. -/
def incomingOdd {n : ℕ} (edges : Finset (Fin n × Fin n)) (v : Fin n) : Bool :=
  decide ((edges.filter fun e => e.2=v).card % 2 = 1)

/-- The set of vertices with odd incoming-edge count. -/
def frameVertices {n : ℕ} (edges : Finset (Fin n × Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => incomingOdd edges v = true

/-- The diagonal Hamiltonian counting edges whose source bit is false and target bit is true. -/
noncomputable def pulseHamiltonian {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => ∑ e ∈ edges, if (!x e.1) && x e.2 then (1 : ℂ) else 0

/-- Evolution under `pulseHamiltonian edges` for time `π`. -/
noncomputable def sourcePulse {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  hamiltonianEvolution (pulseHamiltonian edges) Real.pi

/-- The circuit containing one controlled-Z gate for each listed edge. -/
noncomputable def czWord {n : ℕ} (edges : Finset (Fin n × Fin n)) : Circuit (Reg n) :=
  edges.toList.map fun e => Step.gate (networkCzGateB e.1 e.2)

/-- The diagonal Pauli Z action on register coordinate `v`. -/
noncomputable def localZ {n : ℕ} (v : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if x v then (-1 : ℂ) else 1

/-- The circuit applying local Z gates at all vertices of odd incoming-edge count. -/
noncomputable def frameWord {n : ℕ} (edges : Finset (Fin n × Fin n)) : Circuit (Reg n) :=
  (frameVertices edges).toList.map fun v => Step.gate (localZ v)

/-- The circuit obtained by concatenating the edge CZ word with the local Z frame word. -/
noncomputable def compiledPulseWord {n : ℕ} (edges : Finset (Fin n × Fin n)) : Circuit (Reg n) :=
  czWord edges ++ frameWord edges

/-- The diagonal matrix of the product of controlled-Z phases over the edge set. -/
noncomputable def czMatrix {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => ∏ e ∈ edges, if x e.1 && x e.2 then (-1 : ℂ) else 1

/-- The diagonal local Z frame determined by incoming-edge parity. -/
noncomputable def frameMatrix {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => ∏ v : Fin n,
    if incomingOdd edges v && x v then (-1 : ℂ) else 1

/-- The state obtained by applying the source pulse to the uniform register state. -/
noncomputable def sourceResource {n : ℕ} (edges : Finset (Fin n × Fin n)) : QState (Reg n) :=
  ApplyGate (sourcePulse edges) (Uniform (Reg n))

/-- The state obtained by applying the edge CZ matrix to the uniform register state. -/
noncomputable def czResource {n : ℕ} (edges : Finset (Fin n × Fin n)) : QState (Reg n) :=
  ApplyGate (czMatrix edges) (Uniform (Reg n))

/-- The permutation matrix that flips register bit `v`. -/
noncomputable def localX {n : ℕ} (v : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  permMatrix fun x => Function.update x v (!(x v))

/-- The product of local X at `v` with the diagonal Z phase on all vertices adjacent to `v` in
either edge orientation. -/
noncomputable def stabilizer {n : ℕ} (edges : Finset (Fin n × Fin n)) (v : Fin n) :
    Matrix (Reg n) (Reg n) ℂ :=
  localX v * Matrix.diagonal (fun x => ∏ w : Fin n,
    if (((v,w)∈edges ∨ (w,v)∈edges) ∧ x w = true) then (-1 : ℂ) else 1)

/-- The complex sign `-1` for true and `1` for false. -/
def bitPhase (b : Bool) : ℂ := if b then -1 else 1

/-- Every Boolean phase has square one. -/
@[simp] theorem bitPhase_sq (b : Bool) : bitPhase b * bitPhase b = 1 := by
  cases b <;> norm_num [bitPhase]

/-- Every Boolean phase has complex norm one. -/
@[simp] theorem norm_bitPhase (b : Bool) : ‖bitPhase b‖ = 1 := by
  cases b <;> simp [bitPhase]

/-- A natural power of a Boolean phase is determined by the parity of the exponent. -/
theorem bitPhase_pow (b : Bool) (k : ℕ) :
    bitPhase b ^ k = bitPhase (decide (k % 2 = 1) && b) := by
  cases b
  · simp [bitPhase]
  · rw [show bitPhase true = (-1 : ℂ) by rfl, neg_one_pow_eq_pow_mod_two]
    have hm := Nat.mod_lt k (by decide : 0 < 2)
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h <;> simp [h, bitPhase]

/-- The product of local phases specified by incoming parity equals the product of target-bit
phases over all edges. -/
theorem framePhase_eq_edges {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) :
    (∏ v : Fin n, bitPhase (incomingOdd edges v && x v)) =
      ∏ e ∈ edges, bitPhase (x e.2) := by
  rw [← Finset.prod_fiberwise' edges Prod.snd (fun v => bitPhase (x v))]
  apply Finset.prod_congr rfl
  intro v _
  simp only [Finset.prod_const]
  exact (bitPhase_pow (x v) _).symm

/-- The single-edge source-pulse exponential factors into a target-bit phase and a controlled-Z
phase. -/
theorem exp_source_edge (a b : Bool) :
    Complex.exp ((-Complex.I * (Real.pi : ℂ)) * (if (!a) && b then 1 else 0)) =
      bitPhase b * bitPhase (a && b) := by
  have hp : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
    rw [show -(Complex.I * (Real.pi : ℂ)) = -((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  cases a <;> cases b <;> simp [bitPhase, hp]

/-- The source pulse factors as the incoming-parity frame matrix multiplied by the edge CZ
matrix. -/
theorem sourcePulse_eq_frame_cz {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    sourcePulse edges = frameMatrix edges * czMatrix edges := by
  classical
  unfold sourcePulse hamiltonianEvolution pulseHamiltonian frameMatrix czMatrix
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  change Complex.exp ((-Complex.I * (Real.pi : ℂ)) *
    ∑ e ∈ edges, (if (!x e.1) && x e.2 then 1 else 0)) = _
  rw [Finset.mul_sum, Complex.exp_sum]
  simp_rw [exp_source_edge]
  rw [Finset.prod_mul_distrib, ← framePhase_eq_edges]
  rfl

/-- The product-phase CZ matrix is unitary. -/
theorem czMatrix_unitary {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    czMatrix edges ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  change ‖∏ e ∈ edges, bitPhase (x e.1 && x e.2)‖ = 1
  simp [norm_prod]

/-- The incoming-parity frame matrix is unitary. -/
theorem frameMatrix_unitary {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    frameMatrix edges ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  change ‖∏ v : Fin n, bitPhase (incomingOdd edges v && x v)‖ = 1
  simp [norm_prod]

/-- The local Z matrix is unitary. -/
theorem localZ_unitary {n : ℕ} (v : Fin n) :
    localZ v ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  exact norm_bitPhase (x v)

/-- A list compiled entirely into gates has zero oracle query count. -/
theorem queryCount_gateList {A I : Type*} (l : List A) (g : A → Matrix I I ℂ) :
    QueryCount (l.map fun a => Step.gate (g a)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => exact ih

/-- A list compiled entirely into gates has gate count equal to its length. -/
theorem gateCount_gateList {A I : Type*} (l : List A) (g : A → Matrix I I ℂ) :
    GateCount (l.map fun a => Step.gate (g a)) = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa only [List.map_cons, gateCount_gate, List.length_cons] using congrArg (· + 1) ih

/-- A list of unitary gate matrices defines a unitary circuit. -/
theorem unitary_gateList {A I : Type*} [Fintype I] [DecidableEq I]
    (l : List A) (g : A → Matrix I I ℂ) (hg : ∀ a, g a ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (l.map fun a => Step.gate (g a)) := by
  induction l with
  | nil => exact isUnitaryCircuit_nil
  | cons a l ih => exact (isUnitaryCircuit_gate _ _).mpr ⟨hg a, ih⟩

/-- Running a list of diagonal gates multiplies each state amplitude by the product of the
corresponding diagonal entries. -/
theorem run_diagonalList {A I : Type*} [Fintype I] [DecidableEq I]
    (l : List A) (d : A → I → ℂ) (ψ : QState I) (x : I) :
    Run 1 (l.map fun a => Step.gate (Matrix.diagonal (d a))) ψ x =
      (l.map fun a => d a x).prod * ψ x := by
  induction l generalizing ψ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, run_gate, ih, List.prod_cons,
      ApplyGate, Matrix.mulVec_diagonal]
    ring

/-- Running the edge CZ circuit applies `czMatrix edges` to the input state. -/
theorem run_czWord {n : ℕ} (edges : Finset (Fin n × Fin n)) (ψ : QState (Reg n)) :
    Run 1 (czWord edges) ψ = ApplyGate (czMatrix edges) ψ := by
  classical
  funext x
  change Run 1 (edges.toList.map fun e => Step.gate
    (Matrix.diagonal fun x => if x e.1 && x e.2 then (-1 : ℂ) else 1)) ψ x = _
  rw [run_diagonalList]
  rw [← List.prod_toFinset _ (Finset.nodup_toList _)]
  simp [ApplyGate, czMatrix, Matrix.mulVec_diagonal]

/-- Running the local Z frame circuit applies `frameMatrix edges` to the input state. -/
theorem run_frameWord {n : ℕ} (edges : Finset (Fin n × Fin n)) (ψ : QState (Reg n)) :
    Run 1 (frameWord edges) ψ = ApplyGate (frameMatrix edges) ψ := by
  classical
  funext x
  change Run 1 ((frameVertices edges).toList.map fun v => Step.gate
    (Matrix.diagonal fun x => if x v then (-1 : ℂ) else 1)) ψ x = _
  rw [run_diagonalList]
  rw [← List.prod_toFinset _ (Finset.nodup_toList _)]
  simp only [Finset.toList_toFinset, frameVertices, Finset.prod_filter,
    ApplyGate, frameMatrix, Matrix.mulVec_diagonal]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  cases incomingOdd edges v <;> cases x v <;> simp

/-- The product of the Boolean controlled phases of all edges at a register value. -/
def czPhase {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) : ℂ :=
  ∏ e ∈ edges, bitPhase (x e.1 && x e.2)

/-- The product of local Boolean phases selected by incoming-edge parity. -/
def framePhase {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) : ℂ :=
  ∏ v : Fin n, bitPhase (incomingOdd edges v && x v)

/-- The product of Boolean phases on vertices adjacent to `v` in either edge orientation. -/
def neighborPhase {n : ℕ} (edges : Finset (Fin n × Fin n)) (v : Fin n) (x : Reg n) : ℂ :=
  ∏ w : Fin n, if (v,w) ∈ edges ∨ (w,v) ∈ edges then bitPhase (x w) else 1

/-- The phase of the opposite endpoint when `v` is incident to the edge, and one otherwise,
testing the source endpoint first. -/
def incidentPhase {n : ℕ} (e : Fin n × Fin n) (v : Fin n) (x : Reg n) : ℂ :=
  if e.1 = v then bitPhase (x e.2) else if e.2 = v then bitPhase (x e.1) else 1

/-- The register obtained by negating bit `v` and preserving every other bit. -/
def flipBit {n : ℕ} (v : Fin n) (x : Reg n) : Reg n := Function.update x v (!(x v))

/-- Flipping the same register bit twice returns the original register. -/
theorem flipBit_involutive {n : ℕ} (v : Fin n) : Function.Involutive (flipBit v) := by
  intro x
  funext w
  by_cases h : w = v
  · subst w; simp [flipBit]
  · simp [flipBit, h]

/-- The total CZ phase has square one. -/
@[simp] theorem czPhase_sq {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) :
    czPhase edges x * czPhase edges x = 1 := by
  unfold czPhase
  rw [← Finset.prod_mul_distrib]
  simp

/-- The total incoming-parity frame phase has square one. -/
@[simp] theorem framePhase_sq {n : ℕ} (edges : Finset (Fin n × Fin n)) (x : Reg n) :
    framePhase edges x * framePhase edges x = 1 := by
  unfold framePhase
  rw [← Finset.prod_mul_distrib]
  simp

/-- The product of neighbor phases has square one. -/
@[simp] theorem neighborPhase_sq {n : ℕ} (edges : Finset (Fin n × Fin n))
    (v : Fin n) (x : Reg n) : neighborPhase edges v x * neighborPhase edges v x = 1 := by
  unfold neighborPhase
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro w _
  split_ifs <;> simp

/-- For an edge with distinct endpoints, its incident phase equals the product over vertices
adjacent to `v` along that edge. -/
theorem incidentPhase_eq_vertexProduct {n : ℕ} (e : Fin n × Fin n)
    (he : e.1 ≠ e.2) (v : Fin n) (x : Reg n) :
    (∏ w : Fin n, if (v,w) = e ∨ (w,v) = e then bitPhase (x w) else 1) =
      incidentPhase e v x := by
  rcases e with ⟨a,b⟩
  by_cases ha : a = v
  · subst v
    simp [incidentPhase, Prod.mk.injEq, he]
  · by_cases hb : b = v
    · subst v
      simp [incidentPhase, Prod.mk.injEq, ha, Ne.symm ha]
    · simp [incidentPhase, Prod.mk.injEq, ha, hb, Ne.symm ha, Ne.symm hb]

/-- When every edge is ordered increasingly, the neighbor phase equals the product of incident
phases over the edge set. -/
theorem neighborPhase_eq_edges {n : ℕ} (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) (v : Fin n) (x : Reg n) :
    neighborPhase edges v x = ∏ e ∈ edges, incidentPhase e v x := by
  classical
  induction edges using Finset.induction_on with
  | empty => simp [neighborPhase]
  | @insert e edges he ih =>
    have heord := horder e (Finset.mem_insert_self _ _)
    have hold : ∀ a ∈ edges, a.1 < a.2 := fun a ha => horder a (Finset.mem_insert_of_mem ha)
    have hreverse : (e.2,e.1) ∉ edges := by
      intro h
      have := hold _ h
      exact (lt_asymm heord this)
    have hdisjoint (w : Fin n) :
        ¬ (((v,w) = e ∨ (w,v) = e) ∧ ((v,w) ∈ edges ∨ (w,v) ∈ edges)) := by
      rintro ⟨hnew,hprev⟩
      rcases hnew with hnew | hnew
      · have ha : e.1 = v := (congrArg Prod.fst hnew).symm
        have hb : e.2 = w := (congrArg Prod.snd hnew).symm
        rcases hprev with hprev | hprev
        · exact he (hnew ▸ hprev)
        · exact hreverse (by simpa [ha, hb] using hprev)
      · have ha : e.1 = w := (congrArg Prod.fst hnew).symm
        have hb : e.2 = v := (congrArg Prod.snd hnew).symm
        rcases hprev with hprev | hprev
        · exact hreverse (by simpa [ha, hb] using hprev)
        · exact he (hnew ▸ hprev)
    have hfactor (w : Fin n) :
        (if (v,w) ∈ insert e edges ∨ (w,v) ∈ insert e edges then bitPhase (x w) else 1) =
        (if (v,w) = e ∨ (w,v) = e then bitPhase (x w) else 1) *
        (if (v,w) ∈ edges ∨ (w,v) ∈ edges then bitPhase (x w) else 1) := by
      have := hdisjoint w
      simp only [Finset.mem_insert]
      by_cases hn : (v,w) = e ∨ (w,v) = e <;>
        by_cases hp : (v,w) ∈ edges ∨ (w,v) ∈ edges <;> simp_all
    unfold neighborPhase
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib, incidentPhase_eq_vertexProduct e (ne_of_lt heord)]
    rw [show (∏ w : Fin n, if (v,w) ∈ edges ∨ (w,v) ∈ edges then bitPhase (x w) else 1) =
      ∏ a ∈ edges, incidentPhase a v x from ih hold]
    exact (Finset.prod_insert (f := fun a => incidentPhase a v x) he).symm

/-- For an edge with distinct endpoints, flipping bit `v` changes its controlled phase by the
edge's incident phase at `v`. -/
theorem cz_edge_flip {n : ℕ} (e : Fin n × Fin n) (he : e.1 ≠ e.2)
    (v : Fin n) (x : Reg n) :
    bitPhase (flipBit v x e.1 && flipBit v x e.2) =
      incidentPhase e v x * bitPhase (x e.1 && x e.2) := by
  rcases e with ⟨a,b⟩
  by_cases ha : a = v
  · subst v
    cases hxa : x a <;> cases hxb : x b <;>
      simp [flipBit, incidentPhase, Ne.symm he, hxa, hxb, bitPhase]
  · by_cases hb : b = v
    · subst v
      cases hxa : x a <;> cases hxb : x b <;>
        simp [flipBit, incidentPhase, ha, hxa, hxb, bitPhase]
    · simp [flipBit, incidentPhase, ha, hb]

/-- For increasingly ordered edges, flipping bit `v` changes the total CZ phase by
`neighborPhase edges v x`. -/
theorem czPhase_flip {n : ℕ} (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) (v : Fin n) (x : Reg n) :
    czPhase edges (flipBit v x) = neighborPhase edges v x * czPhase edges x := by
  unfold czPhase
  rw [neighborPhase_eq_edges edges horder]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun e he => cz_edge_flip e (ne_of_lt (horder e he)) v x)

/-- For increasingly ordered edges, the neighbor phase at `v` is unchanged by flipping bit `v`. -/
theorem neighborPhase_flip {n : ℕ} (edges : Finset (Fin n × Fin n))
    (horder : ∀ e ∈ edges, e.1 < e.2) (v : Fin n) (x : Reg n) :
    neighborPhase edges v (flipBit v x) = neighborPhase edges v x := by
  have hloop : (v,v) ∉ edges := by
    intro h
    exact (lt_irrefl v) (horder _ h)
  apply Finset.prod_congr rfl
  intro w _
  by_cases h : w = v
  · subst w; simp [hloop]
  · simp [flipBit, h]

/-- Flipping bit `v` changes the frame phase by the sign determined by its incoming-edge parity. -/
theorem framePhase_flip {n : ℕ} (edges : Finset (Fin n × Fin n))
    (v : Fin n) (x : Reg n) :
    framePhase edges (flipBit v x) = bitPhase (incomingOdd edges v) * framePhase edges x := by
  have hf (w : Fin n) :
      bitPhase (incomingOdd edges w && flipBit v x w) =
        (if w = v then bitPhase (incomingOdd edges v) else 1) *
          bitPhase (incomingOdd edges w && x w) := by
    by_cases h : w = v
    · subst w
      cases incomingOdd edges v <;> cases hx : x v <;> simp [flipBit, hx, bitPhase]
    · simp [flipBit, h]
  unfold framePhase
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

/-- Applying the stabilizer at `v` evaluates the state at the flipped register and multiplies by
the neighbor phase there. -/
theorem apply_stabilizer {n : ℕ} (edges : Finset (Fin n × Fin n))
    (v : Fin n) (ψ : QState (Reg n)) (x : Reg n) :
    ApplyGate (stabilizer edges v) ψ x =
      neighborPhase edges v (flipBit v x) * ψ (flipBit v x) := by
  rw [stabilizer, applyGate_mul]
  change ApplyGate (permMatrix (flipBit v)) _ x = _
  rw [applyGate_permMatrix (flipBit_involutive v), ApplyGate, Matrix.mulVec_diagonal]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  by_cases h : (v,w) ∈ edges ∨ (w,v) ∈ edges
  · simp [h, bitPhase]
  · simp [h]

end Qatlib.Concepts.MbqcFlow.FlowDecision
