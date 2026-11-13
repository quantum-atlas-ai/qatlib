/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InstrumentCore.PatternCompile.UniversalGraphDefs

/-!
# Local cluster compilation identities and counts

This module proves structural facts used to compile single-qubit and CNOT gates into
cluster-network words. It establishes phase normalization, legality, word lengths, and separate
wire and controlled-Z counts, together with the target-Hadamard conjugation identity for CNOT.
This supplies finite circuit identities for the one-way universality construction of
[RaussendorfBriegel2000].

## Main statements

* `mbqcCompiledWord_length`: The compiled length is four times the single-qubit count plus three
  times the CNOT count.
* `mbqcCompiledWord_legal`: Legal local gate lists compile to legal cluster networks.
* `mbqcCompiledWord_counts`: Computes the wire-gate and controlled-Z counts separately.
* `mbqcCnot_matrix`: Hadamard conjugation on a distinct target converts controlled-Z to CNOT.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- The compiled single-qubit phase word has length four. -/
theorem mbqcQubitWord_length (U : Matrix Bool Bool ℂ) : (mbqcQubitWord U).length=4 := rfl

/-- Every phase in the compiled single-qubit word has norm one. -/
theorem mbqcQubitWord_norm (U : Matrix Bool Bool ℂ) : ∀ z ∈ mbqcQubitWord U, ‖z‖=1 := by
  exact (cluster_euler_four_measurement_actual_consumer _ _ _).2.1

/-- The accumulated scalar phase of a local compilation has norm one. -/
theorem mbqcLocalScalar_norm {n : ℕ} (gs : List (ReflectionGate n)) : ‖mbqcLocalScalar gs‖=1 := by
  induction gs with
  | nil => simp [mbqcLocalScalar]
  | cons g gs ih =>
    cases g with
    | inl p =>
      obtain ⟨i,U⟩ := p
      change ‖mbqcLocalScalar gs * mbqcQubitScalar U‖=1
      rw [norm_mul,ih]
      exact one_mul _ |>.trans (Complex.norm_exp_ofReal_mul_I _)
    | inr p => simpa [mbqcLocalScalar] using! ih

/-- The compiled word has four steps per single-qubit gate and three per CNOT gate. -/
theorem mbqcCompiledWord_length {n : ℕ} (gs : List (ReflectionGate n)) :
    (mbqcCompiledWord gs).length=4*(mbqcLocalCounts gs).1+3*(mbqcLocalCounts gs).2 := by
  induction gs with
  | nil => simp [mbqcCompiledWord,mbqcLocalCounts]
  | cons g gs ih =>
    cases g with
    | inl p =>
      obtain ⟨i,U⟩ := p
      simp only [mbqcCompiledWord, List.flatMap_cons, List.length_append,
        mbqcLocalExpansion, List.length_map, mbqcQubitWord_length, mbqcLocalCounts] at ⊢
      change 4+(mbqcCompiledWord gs).length = _
      rw [ih]
      omega
    | inr p =>
      obtain ⟨i,j⟩ := p
      simp only [mbqcCompiledWord,List.flatMap_cons,List.length_append,
        mbqcLocalExpansion,List.length_cons,List.length_nil,mbqcLocalCounts]
      change 3+(mbqcCompiledWord gs).length = _
      rw [ih]
      omega

/-- Enumerating the finite graph word recovers the compiled gate list. -/
theorem mbqcGraphWord_ofFn {n : ℕ} (gs : List (ReflectionGate n)) :
    List.ofFn (mbqcGraphWord gs)=mbqcCompiledWord gs := by
  exact List.ofFn_getElem

/-- The local expansion of a legal reflection gate is a legal cluster network. -/
theorem mbqcLocalExpansion_legal {n : ℕ} (g : ReflectionGate n) (hg : reflectionGateLegal g) :
    networkLegal (mbqcLocalExpansion g) := by
  cases g with
  | inl p =>
    obtain ⟨i,U⟩ := p
    intro g hg'
    simp only [mbqcLocalExpansion,List.mem_map] at hg'
    obtain ⟨z,hz,rfl⟩ := hg'
    exact mbqcQubitWord_norm U z hz
  | inr p =>
    obtain ⟨c,t⟩ := p
    intro g hg'
    simp only [mbqcLocalExpansion,List.mem_cons,List.not_mem_nil,or_false] at hg'
    rcases hg' with rfl | rfl | rfl
    · norm_num
    · exact hg
    · norm_num

/-- Compiling a legal list of reflection gates gives a legal cluster network. -/
theorem mbqcCompiledWord_legal {n : ℕ} (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) : networkLegal (mbqcCompiledWord gs) := by
  intro g hg
  obtain ⟨a,ha,hga⟩ := List.mem_flatMap.mp hg
  exact mbqcLocalExpansion_legal a (hgs a ha) g hga

/-- Wire-gate and controlled-Z counts add componentwise under concatenation. -/
private theorem networkCounts_append {n : ℕ} (as bs : List (ClusterNetworkGate n)) :
    networkCounts (as++bs)=((networkCounts as).1+(networkCounts bs).1,
      (networkCounts as).2+(networkCounts bs).2) := by
  induction as with
  | nil => simp [networkCounts]
  | cons g as ih =>
    cases g <;> simp only
        [List.cons_append,networkCounts,ih,Prod.mk.injEq] <;> constructor <;> first | trivial | omega

/-- A phase word on one wire has one wire-gate step per phase and no controlled-Z steps. -/
private theorem networkCounts_wire {n : ℕ} (i : Fin n) (zs : List ℂ) :
    networkCounts (zs.map (fun z => Sum.inl (i,z)))=(zs.length,0) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [networkCounts,ih]

/-- The compiled network has four wire steps per single-qubit gate, two wire steps per CNOT, and
one controlled-Z step per CNOT. -/
theorem mbqcCompiledWord_counts {n : ℕ} (gs : List (ReflectionGate n)) :
    networkCounts (mbqcCompiledWord gs)=
      (4*(mbqcLocalCounts gs).1+2*(mbqcLocalCounts gs).2,(mbqcLocalCounts gs).2) := by
  induction gs with
  | nil => simp [mbqcCompiledWord,mbqcLocalCounts,networkCounts]
  | cons g gs ih =>
    cases g with
    | inl p =>
      obtain ⟨i,U⟩ := p
      rw [mbqcCompiledWord,List.flatMap_cons,networkCounts_append]
      change ((networkCounts ((mbqcQubitWord U).map (fun z => Sum.inl (i,z)))).1+
        (networkCounts (mbqcCompiledWord gs)).1,
        (networkCounts ((mbqcQubitWord U).map (fun z => Sum.inl (i,z)))).2+
        (networkCounts (mbqcCompiledWord gs)).2)=_
      rw [networkCounts_wire,mbqcQubitWord_length,ih]
      simp only [mbqcLocalCounts, Prod.mk.injEq]
      omega
    | inr p =>
      obtain ⟨i,j⟩ := p
      rw [mbqcCompiledWord,List.flatMap_cons,networkCounts_append]
      change ((networkCounts [Sum.inl (j,1),Sum.inr (i,j),Sum.inl (j,1)]).1+
        (networkCounts (mbqcCompiledWord gs)).1,
        (networkCounts [Sum.inl (j,1),Sum.inr (i,j),Sum.inl (j,1)]).2+
        (networkCounts (mbqcCompiledWord gs)).2)=_
      rw [ih]
      simp only [networkCounts,mbqcLocalCounts,Prod.mk.injEq]
      omega

/-- The single-qubit and CNOT counts sum to the length of the original local gate list. -/
theorem mbqcLocalCounts_length {n : ℕ} (gs : List (ReflectionGate n)) :
    (mbqcLocalCounts gs).1+(mbqcLocalCounts gs).2=gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g <;> simp only [mbqcLocalCounts,List.length_cons] <;> omega

/-- A controlled-Z gate acts on a basis ket by the sign determined by its control and target
bits. -/
private theorem cz_ket {n : ℕ} (c t : Fin n) (x : Reg n) :
    ApplyGate (networkCzGateB c t) (Qatlib.Foundations.PureStateMath.Ket x)=
      (if x c && x t then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  funext y
  simp only [ApplyGate,networkCzGateB,Matrix.mulVec_diagonal,Qatlib.Foundations.PureStateMath.Ket,
    Pi.smul_apply,smul_eq_mul]
  by_cases hy : y=x <;> simp [hy]

/-- Conjugating controlled-Z by Hadamard on its target gives CNOT when the control and target
wires are distinct. -/
theorem mbqcCnot_matrix {n : ℕ} (c t : Fin n) (hct : c≠t) :
    wireGate n t Hadamard*networkCzGateB c t*wireGate n t Hadamard=cnotGate n c t := by
  have hc (x : Reg n) : ApplyGate
      (wireGate n t Hadamard*networkCzGateB c t*wireGate n t Hadamard) (Qatlib.Foundations.PureStateMath.Ket x)=
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ x c)) := by
    simp only [applyGate_mul,applyGate_wireGate_ket,reflectionApplyGate_add,
      reflectionApplyGate_smul,cz_ket]
    simp only [Function.update_of_ne hct,Function.update_self,Function.update_idem]
    cases hxc : x c <;> cases hxt : x t <;>
      simp [Hadamard] <;>
      funext y <;> simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul] <;>
      ring_nf <;> norm_num [show ((Real.sqrt 2 : ℂ)⁻¹)^2=(1/2 : ℂ) from by
        simpa [pow_two] using! Qatlib.Concepts.QuditTeleport.TeleportCore.sqrt2_inv_sq] <;> ring
  ext y x
  have he := congrFun ((hc x).trans (applyGate_cnotGate_ket n c t hct x).symm) y
  simpa [ApplyGate,Matrix.mulVec,dotProduct,Qatlib.Foundations.PureStateMath.Ket,mul_ite] using! he

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
