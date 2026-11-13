/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodySim96.MainResults.LocalAssembly
import Qatlib.Papers.ManyBodySim96.MainResults.MeasurementSampling
import Qatlib.Papers.ManyBodySim96.MainResults.KineticLedger
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Gate-cost assembly for many-body simulation

This module combines explicit first-order segment bounds with reflection-gate compilation and
sampling costs. It also counts Fourier-transform and supplied potential costs in a particle
segment. The polynomial estimates retain their hypotheses on term counts, operator norms, and
the costs of the supplied local implementations.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `local_hamiltonian_no_work_matrix`: Every Hermitian operator on `b ≥ 1` qubits has an exact
  evolution implemented on those qubits by a legal, query-free reflection program of length at
  most `768 * (b + 1) ^ 3 * 4 ^ b`.
* `first_order_compiled_gate_polynomial`: Given exact legal local implementations of length at
  most `C`, polynomial term and norm bounds yield a query-free compiled first-order word with
  the displayed polynomial gate bound and exact product-formula matrix.
* `particle_total_gates_polynomial'`: Substituting the polynomial term-count bound into the
  particle cost gives the displayed bound with potential contribution `(N + 1) ^ 2 * cV`.

## References

* [Wiesner, 1996][Wiesner1996]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ManyBodySim96.MainResults

/-- The one- and two-body term count is at most `(N + 1) ^ 2`. -/
theorem oneTwoBodyTermCount_le (N : ℕ) : oneTwoBodyTermCount N ≤ (N + 1) ^ 2 := by
  unfold oneTwoBodyTermCount
  apply Nat.div_le_of_le_mul
  nlinarith [Nat.zero_le N]

/-- A nonnegative norm bound at most `(N + 1) ^ d` and at most `(N + 1) ^ 2` terms give the
displayed polynomial upper bound on the selected first-order segment count. -/
theorem sourceSegments_le_uniform {M N d : ℕ} {bnorm T ε : ℝ}
    (hb : 0 ≤ bnorm) (hB : bnorm ≤ ((N + 1 : ℕ) : ℝ) ^ d) (hε : 0 < ε)
    (hM : M ≤ (N + 1) ^ 2) :
    sourceFirstSegments M bnorm T ε ≤
      1 + Nat.ceil (T ^ 2 / ε) * ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2 := by
  have h := sourceFirstSegments_le M ((N + 1) ^ d) bnorm T ε hb (by simpa using! hB) hε
  have hstep : M * (N + 1) ^ d ≤ (N + 1) ^ 2 * (N + 1) ^ d :=
    Nat.mul_le_mul_right _ hM
  have hp : (M * (N + 1) ^ d) ^ 2 ≤ ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2 :=
    Nat.pow_le_pow_left hstep 2
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hp) 1)

/-- Every Hermitian operator on `b ≥ 1` qubits has an exact evolution implemented on those
qubits by a legal, query-free reflection program of length at most `768 * (b + 1) ^ 3 * 4 ^
b`. [Wiesner1996] -/
theorem local_hamiltonian_no_work_matrix {b : ℕ} (hb : 1 ≤ b)
    (H : Operator (2 ^ b)) (hH : H.IsHermitian) (s : ℝ) :
    ∃ gs : List (ReflectionGate b), reflectionLegal gs ∧
      gs.length ≤ 768 * (b + 1) ^ 3 * 4 ^ b ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      relabelGate (bitVecEquiv b) (reflectionProgramMatrix gs) =
        HamiltonianEvolution H s := by
  let U : Matrix (Reg b) (Reg b) ℂ :=
    relabelGate (bitVecEquiv b).symm (HamiltonianEvolution H s)
  have hU : U ∈ Matrix.unitaryGroup (Reg b) ℂ :=
    (Qatlib.Concepts.GateVocabulary.GateVocab.relabelGate_mem_unitaryGroup
      (bitVecEquiv b).symm (HamiltonianEvolution H s)).mpr
        (Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hH s)
  obtain ⟨gs, hlegal, hlen, hquery, hcount, hrun⟩ :=
    Qatlib.Concepts.CircuitImpl.MultiControl.known_unitary_no_work_actual_local_synthesis
      b hb U hU
  refine ⟨gs, hlegal, hlen, hquery, hcount, ?_⟩
  have hmatrix : reflectionProgramMatrix gs = U := by
    ext i j
    have he := congrFun (hrun (Qatlib.Foundations.PureStateMath.Ket j)) i
    rw [run_reflectionCompile] at he
    simpa [ApplyGate, Matrix.mulVec, dotProduct,
      Qatlib.Foundations.PureStateMath.Ket, mul_ite] using! he
  rw [hmatrix]
  simpa [U] using!
    (Qatlib.Concepts.GateVocabulary.GateVocab.relabelGate_symm
      (bitVecEquiv b).symm (HamiltonianEvolution H s))

/-- Given exact legal local implementations of length at most `C`, polynomial term and norm
bounds yield a query-free compiled first-order word with the displayed polynomial gate bound
and exact product-formula matrix. [Wiesner1996] -/
theorem first_order_compiled_gate_polynomial {b N M d : ℕ} {bnorm T ε : ℝ}
    (H : Fin M → Operator (2 ^ b)) (C : ℕ) (ws : Fin M → List (ReflectionGate b))
    (hreal : ∀ j, relabelGate (bitVecEquiv b) (reflectionProgramMatrix (ws j)) =
      HamiltonianEvolution (H j) ((-T) / (sourceFirstSegments M bnorm T ε : ℝ)))
    (hlegal : ∀ j, reflectionLegal (ws j)) (hlen : ∀ j, (ws j).length ≤ C)
    (hb : 0 ≤ bnorm) (hB : bnorm ≤ ((N + 1 : ℕ) : ℝ) ^ d) (hε : 0 < ε)
    (hM : M ≤ (N + 1) ^ 2) :
    ∃ gs : List (ReflectionGate b),
      reflectionLegal gs ∧
      GateCount (reflectionCompile gs) ≤
        ((N + 1) ^ 2 * (1 + Nat.ceil (T ^ 2 / ε) *
          ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2)) * C ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      relabelGate (bitVecEquiv b) (reflectionProgramMatrix gs) =
        pfFamily H (-T) (sourceFirstSegments M bnorm T ε) := by
  obtain ⟨gs, hleg, hlen_gs, hgc, hqc, hmat⟩ :=
    compiled_first_order_word H (-T) ws C hreal hlegal hlen
  refine ⟨gs, hleg, ?_, hqc, hmat⟩
  rw [hgc]
  have hpoly := source_first_order_polynomial_macro_count N M d bnorm T ε hb hB hε hM
  exact hlen_gs.trans (Nat.mul_le_mul_right C hpoly)

/-- Under the supplied local implementation, term-count, and norm bounds, a legal query-free
program has sample-count-weighted gate cost bounded by the displayed product of the sampling
and compilation bounds. [Wiesner1996] -/
theorem first_order_total_work_polynomial {b N M d : ℕ} {bnorm T ε : ℝ}
    (H : Fin M → Operator (2 ^ b)) (C : ℕ) (ws : Fin M → List (ReflectionGate b))
    (hreal : ∀ j, relabelGate (bitVecEquiv b) (reflectionProgramMatrix (ws j)) =
      HamiltonianEvolution (H j) ((-T) / (sourceFirstSegments M bnorm T ε : ℝ)))
    (hlegal : ∀ j, reflectionLegal (ws j)) (hlen : ∀ j, (ws j).length ≤ C)
    (hb : 0 ≤ bnorm) (hB : bnorm ≤ ((N + 1 : ℕ) : ℝ) ^ d) (hε : 0 < ε)
    (hM : M ≤ (N + 1) ^ 2) (δ η : ℝ) :
    ∃ gs : List (ReflectionGate b),
      reflectionLegal gs ∧
      sampleCount δ η * GateCount (reflectionCompile gs) ≤
        sampleCount δ η *
          (((N + 1) ^ 2 * (1 + Nat.ceil (T ^ 2 / ε) *
            ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2)) * C) ∧
      QueryCount (reflectionCompile gs) = 0 := by
  obtain ⟨gs, hleg, hgc, hqc, -⟩ :=
    first_order_compiled_gate_polynomial H C ws hreal hlegal hlen hb hB hε hM
  exact ⟨gs, hleg, Nat.mul_le_mul_left _ hgc, hqc⟩

/-- The segment cost of `N` kinetic Fourier-transform pairs and `M` potential operations of
supplied cost `cV`. -/
def particleSegmentGates (N M k : ℕ) (cV : ℕ) : ℕ :=
  N * kineticQFTGates k + M * cV

/-- For `k ≥ 1`, the particle segment cost is at most `4 * N * k ^ 2 + M * cV`. -/
theorem particleSegmentGates_le (N M k cV : ℕ) (hk : 1 ≤ k) :
    particleSegmentGates N M k cV ≤ 4 * N * k ^ 2 + M * cV := by
  have hq : kineticQFTGates k ≤ 4 * k ^ 2 := kineticQFTGates_le k hk
  have hN : N * kineticQFTGates k ≤ N * (4 * k ^ 2) := Nat.mul_le_mul_left _ hq
  calc particleSegmentGates N M k cV
      = N * kineticQFTGates k + M * cV := rfl
    _ ≤ N * (4 * k ^ 2) + M * cV := Nat.add_le_add_right hN _
    _ = 4 * N * k ^ 2 + M * cV := by ring

/-- Under polynomial term and norm bounds and `k ≥ 1`, the segment count times the particle
segment cost is bounded by the displayed segment bound times `4 * N * k ^ 2 + M * cV`. -/
theorem particle_total_gates_polynomial {M N d : ℕ} {bnorm T ε : ℝ} (k cV : ℕ)
    (hk : 1 ≤ k) (hb : 0 ≤ bnorm) (hB : bnorm ≤ ((N + 1 : ℕ) : ℝ) ^ d)
    (hε : 0 < ε) (hM : M ≤ (N + 1) ^ 2) :
    sourceFirstSegments M bnorm T ε * particleSegmentGates N M k cV ≤
      (1 + Nat.ceil (T ^ 2 / ε) * ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2) *
        (4 * N * k ^ 2 + M * cV) := by
  have hr := sourceSegments_le_uniform (M := M) (N := N) (d := d)
    (bnorm := bnorm) (T := T) (ε := ε) hb hB hε hM
  have hseg := particleSegmentGates_le N M k cV hk
  exact Nat.mul_le_mul hr hseg

/-- Substituting the polynomial term-count bound into the particle cost gives the displayed
bound with potential contribution `(N + 1) ^ 2 * cV`. [Wiesner1996] -/
theorem particle_total_gates_polynomial' {M N d : ℕ} {bnorm T ε : ℝ} (k cV : ℕ)
    (hk : 1 ≤ k) (hb : 0 ≤ bnorm) (hB : bnorm ≤ ((N + 1 : ℕ) : ℝ) ^ d)
    (hε : 0 < ε) (hM : M ≤ (N + 1) ^ 2) :
    sourceFirstSegments M bnorm T ε * particleSegmentGates N M k cV ≤
      (1 + Nat.ceil (T ^ 2 / ε) * ((N + 1) ^ 2 * (N + 1) ^ d) ^ 2) *
        (4 * N * k ^ 2 + (N + 1) ^ 2 * cV) := by
  refine (particle_total_gates_polynomial (M := M) (N := N) (d := d)
    k cV hk hb hB hε hM).trans ?_
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_left (Nat.mul_le_mul_right cV hM) _

end Qatlib.Papers.ManyBodySim96.MainResults
