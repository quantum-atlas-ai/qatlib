/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Defs
import Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

/-!
# Measurement-pattern clauses and a combined counterexample

This module collects resource, loading, flow, and complexity statements for finite measurement
patterns. It proves lattice-entangler factorization, the three-CNOT swap identity, a
vertex-projection formula, and bounds involving peak space, communication, and bit time.

It also defines the combined proposition `Clause18Frozen` and refutes it using the
corrected-loading clause under the present definitions. Measurement-pattern semantics are placed
in the broader setting of [DanosKashefiPanangaden2007].

## Main statements

* `clause7_clause4b`: Three alternating CNOT gates implement the wire swap.
* `clause7_clause6a`: Euler-pattern dependencies satisfy the flow condition.
* `clause7_counter_clause5b`: The proposed universal corrected-loading identity fails.
* `clause7_counter`: The combined proposition `Clause18Frozen` is false.

## References

* [Danos et al., 2007][DanosKashefiPanangaden2007]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open scoped BigOperators Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns

/-- The peak-space quantity of a pattern with `w` measured wires and `m` outputs equals `w + m`. -/
theorem clause7_clause6b : ∀ (n w m : ℕ) (P : MpPattern n w m), mpPeakSpace P = w + m := by
  intro n w m P
  rfl

/-- For a deterministic pattern, the total number of measured and output wires is at most its
bit-time quantity. -/
theorem clause7_clause6d : ∀ (n w m : ℕ) (P : MpPattern n w m) (resource : QState (Reg (w + m - n))),
    MpDeterministic P resource → w + m ≤ mpBitTime P := by
  intro n w m P resource _hdet
  have h : mpBitTime P = 2 * w + m + (MpDependency P).card := rfl
  omega

/-- The lattice entangler factors into its frame matrix followed by its controlled-Z matrix. -/
theorem clause7_clause4a : ∀ a b : ℕ,
    mpLatticeEntangler a b
      = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix (mpLatticeEdges a b)
        * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix (mpLatticeEdges a b) := by
  intro a b
  exact Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz (mpLatticeEdges a b)

/-- Every loading Pauli matrix multiplied by its conjugate transpose equals the identity. -/
theorem clause7_clause5a : ∀ (f1 f2 : Bool),
    mpLoadPauli f1 f2 * (mpLoadPauli f1 f2).conjTranspose = 1 := by
  intro f1 f2
  cases f1 <;> cases f2 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [mpLoadPauli, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fin.sum_univ_two, star_mul]
  all_goals norm_num

/-- The proposed uniform quarter-weight identity for all corrected loading branches is false for
the present loading matrices. -/
theorem clause7_counter_clause5b :
    ¬ (∀ (f1 f2 : Bool) (ρ : Operator 2),
        mpLoadPauli f1 f2
          * (mpLoadKraus f1 f2 * ρ * (mpLoadKraus f1 f2).conjTranspose)
          * (mpLoadPauli f1 f2).conjTranspose
        = (1 / 4 : ℂ) • ρ) := by
  intro h
  have hk : mpLoadKraus false false = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp only [mpLoadKraus]
    rw [show ((1 : ℕ) / 2 : ℕ) = 0 from rfl]
    exact zero_nsmul _
  have h5 := h false false (1 : Operator 2)
  rw [hk] at h5
  simp only [Matrix.zero_mul, Matrix.mul_zero] at h5
  have hentry := congrArg (fun M : Operator 2 => M 0 0) h5
  simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hentry
  norm_num at hentry

/-- The frame matrix of the single edge from zero to one has diagonal sign determined by wire
one. -/
private theorem frame_entry_edge01 (x : Reg 2) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix mpEdge01 x x = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 1) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x),
    Fin.prod_univ_two]
  have h0 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd mpEdge01 0 = false := by decide
  have h1 : Qatlib.Concepts.MbqcFlow.FlowDecision.incomingOdd mpEdge01 1 = true := by decide
  rw [h0, h1]
  simp [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]

/-- The controlled-Z matrix of the single edge from zero to one has diagonal sign determined by
the product of its two bits. -/
private theorem cz_entry_edge01 (x : Reg 2) :
    Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix mpEdge01 x x = Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (x 0 && x 1) := by
  rw [Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix, Matrix.diagonal_apply, if_pos (rfl : x = x)]
  simp only [mpEdge01, Finset.prod_singleton]
  rfl

/-- The uniform state on a two-bit register has amplitude one half at every register. -/
private theorem uniform_reg2 (x : Reg 2) : Uniform (Reg 2) x = (1 / 2 : ℂ) := by
  show ((Real.sqrt (Fintype.card (Reg 2)) : ℝ) : ℂ)⁻¹ = 1 / 2
  have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [card_reg]
  norm_num [h4]

/-- Projecting vertex zero of the two-vertex source resource onto outcome `b` produces
`mpDeletionState b`. -/
theorem clause7_clause4c : ∀ b : Bool,
    Matrix.mulVec (mpVertexProjector 2 ⟨0, by omega⟩ b)
        (Qatlib.Concepts.MbqcFlow.FlowDecision.sourceResource mpEdge01) = mpDeletionState b := by
  intro b
  have hsrc : ∀ x : Reg 2, Qatlib.Concepts.MbqcFlow.FlowDecision.sourceResource mpEdge01 x
      = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix mpEdge01 x x
        * (Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix mpEdge01 x x * (1 / 2 : ℂ)) := by
    intro x
    rw [Qatlib.Concepts.MbqcFlow.FlowDecision.sourceResource, ApplyGate,
      Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse_eq_frame_cz, ← Matrix.mulVec_mulVec,
      Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix, Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix,
      Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
    simp only [Matrix.diagonal_apply, uniform_reg2]
    simp
  funext x
  rw [mpVertexProjector, Matrix.mulVec_diagonal, hsrc, frame_entry_edge01, cz_entry_edge01,
    mpDeletionState]
  by_cases hx : x ⟨0, by omega⟩ = b
  · have hxB : x 0 = b := hx
    rw [if_pos hx, if_pos hxB, one_mul, hxB]
    cases hb : b <;> cases hy : x 1 <;> norm_num [Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase]
  · have hxB : ¬ x 0 = b := hx
    rw [if_neg hx, if_neg hxB, zero_mul]

/-- Simultaneous row and column reindexing by an equivalence preserves matrix multiplication. -/
private theorem reindex_square_mul {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A B : Matrix m m ℂ) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.mul_apply]
  exact Fintype.sum_equiv e.symm (fun k => A (e.symm i) (e.symm k) * B (e.symm k) (e.symm j))
    (fun k => A (e.symm i) k * B k (e.symm j)) (fun _ => rfl)

/-- The product of two function matrices is the matrix of their composition in the same order. -/
private theorem permMatrix_mul' {I : Type*} [Fintype I] [DecidableEq I] (σ τ : I → I) :
    Qatlib.Foundations.PureStateMath.permMatrix σ * Qatlib.Foundations.PureStateMath.permMatrix τ
      = Qatlib.Foundations.PureStateMath.permMatrix (σ ∘ τ) := by
  ext i j
  simp only [Qatlib.Foundations.PureStateMath.permMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · simp

/-- The integer-indexed CNOT matrix is the register CNOT matrix reindexed by `bitVecEquiv` when
its wire indices are distinct. -/
private theorem mpFinCnot_eq_reindex (c t : Fin 2) (hct : (c : ℕ) ≠ (t : ℕ)) :
    mpFinCnot c t = Matrix.reindex (bitVecEquiv 2) (bitVecEquiv 2)
      (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.cnotGate 2 c t) := by
  simp only [mpFinCnot, mpFinGate, finiteCodeMatrix]
  have h : (c : ℕ) < 2 ∧ (t : ℕ) < 2 ∧ (c : ℕ) ≠ (t : ℕ) := ⟨c.isLt, t.isLt, hct⟩
  rw [dif_pos h]

/-- Three CNOT gates with alternating control and target implement the wire-swap matrix. -/
theorem clause7_clause4b : mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩
      * (mpFinCnot ⟨1, by omega⟩ ⟨0, by omega⟩
        * mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩)
    = mpWireSwapMatrix := by
  have h01 : ((⟨0, by omega⟩ : Fin 2) : ℕ) ≠ ((⟨1, by omega⟩ : Fin 2) : ℕ) := by norm_num
  have h10 : ((⟨1, by omega⟩ : Fin 2) : ℕ) ≠ ((⟨0, by omega⟩ : Fin 2) : ℕ) := by norm_num
  rw [mpFinCnot_eq_reindex ⟨0, by omega⟩ ⟨1, by omega⟩ h01,
    mpFinCnot_eq_reindex ⟨1, by omega⟩ ⟨0, by omega⟩ h10]
  rw [reindex_square_mul, reindex_square_mul]
  simp only [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.cnotGate]
  rw [permMatrix_mul', permMatrix_mul']
  simp only [mpWireSwapMatrix]
  congr 1
  apply congrArg Qatlib.Foundations.PureStateMath.permMatrix
  funext i k
  fin_cases k <;> simp [Function.comp_apply, Function.update, Bool.xor_comm,
    Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

/-- A deterministic pattern has at most twice as many measured wires as communication bits. -/
theorem clause7_clause6c : ∀ (n w m : ℕ) (P : MpPattern n w m) (resource : QState (Reg (w + m - n))),
    MpDeterministic P resource → w ≤ 2 * mpCommBits P := by
  intro n w m P resource hdet
  classical
  have hle : w ≤ w + m := by omega
  have hcover : (Finset.univ : Finset (Fin w)).image (Fin.castLE hle)
      ⊆ (MpDependency P).biUnion (fun p => ({p.1, p.2} : Finset (Fin (w + m)))) := by
    intro y hy
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    subst y
    obtain ⟨p, hp, hpc⟩ := hdet.2 j
    refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
    rcases hpc with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  have hcard : ((Finset.univ : Finset (Fin w)).image (Fin.castLE hle)).card = w := by
    rw [Finset.card_image_of_injective _ (Fin.castLE_injective hle)]
    simp
  have hle' : w ≤ (MpDependency P).card * 2 := by
    calc w = ((Finset.univ : Finset (Fin w)).image (Fin.castLE hle)).card := hcard.symm
      _ ≤ ((MpDependency P).biUnion (fun p => ({p.1, p.2} : Finset (Fin (w + m))))).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ p ∈ MpDependency P, ({p.1, p.2} : Finset (Fin (w + m))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ MpDependency P, 2 := by
          refine Finset.sum_le_sum fun p _ => ?_
          have h2 := Finset.card_insert_le p.1 ({p.2} : Finset (Fin (w + m)))
          simp at h2
          omega
      _ = (MpDependency P).card * 2 := by
          rw [Finset.sum_const, smul_eq_mul]
  have hcomm : mpCommBits P = (MpDependency P).card := rfl
  rw [hcomm]
  omega

/-- Every Euler pattern satisfies `MpFlowCondition`. -/
theorem clause7_clause6a : ∀ θ : Fin 5 → ℝ, MpFlowCondition (mpEulerPattern θ) := by
  intro θ
  have hsub : MpDependency (mpEulerPattern θ)
      ⊆ Finset.univ.filter (fun q : Fin (5 + 1) × Fin (5 + 1) => (q.1 : ℕ) < (q.2 : ℕ)) := by
    rw [MpDependency]
    apply Finset.biUnion_subset.mpr
    intro j _
    apply Finset.union_subset
    · apply Finset.image_subset_iff.mpr
      intro i hi
      have hsmall : (mpEulerPattern θ).angleSign j ∪ (mpEulerPattern θ).angleShift j
          ⊆ mpEulerSignSet j := by
        apply Finset.union_subset
        · exact subset_rfl
        · exact Finset.empty_subset _
      have hmem : i ∈ mpEulerSignSet j := Finset.mem_of_subset hsmall hi
      simp only [mpEulerSignSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ((Fin.castLE (by omega : (5 : ℕ) ≤ 5 + 1) i : Fin (5 + 1)) : ℕ)
        < ((Fin.castLE (by omega : (5 : ℕ) ≤ 5 + 1) j : Fin (5 + 1)) : ℕ)
      rw [Fin.val_castLE, Fin.val_castLE]
      exact hmem.1
    · apply Finset.biUnion_subset.mpr
      intro k _
      apply Finset.image_subset_iff.mpr
      intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show ((Fin.castLE (by omega : (5 : ℕ) ≤ 5 + 1) i : Fin (5 + 1)) : ℕ)
        < ((Fin.natAdd 5 k : Fin (5 + 1)) : ℕ)
      rw [Fin.val_castLE, Fin.val_natAdd]
      have : (i : ℕ) < 5 := Fin.isLt i
      omega
  intro p hp
  have hmem := Finset.mem_of_subset hsub hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns Qatlib.Concepts.ClusterPatterns.CnotPatterns.Basic
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Infra
open Qatlib.Concepts.ClusterPatterns.CnotPatterns.Clause18Wire

/-- The conjunction of the specified wire, CNOT, Euler, loading, resource, flow, complexity,
gate-realization, and angle-rounding claims. -/
def Clause18Frozen : Prop :=

  (∀ (s : Fin 2 → Bool) (ρ : Operator 2),
      ∑ z : Fin 2 → Bool,
          (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z) * ρ
            * (mpPatternKraus mpWirePattern (Uniform (Reg 2)) s z).conjTranspose
        = (1 / 4 : ℂ) • ρ)

  ∧ (∀ (s : Fin 4 → Bool) (ρ : Operator 4),
      ∑ z : Fin 4 → Bool,
          (mpPatternKraus mpCnotPattern (Uniform (Reg 4)) s z) * ρ
            * (mpPatternKraus mpCnotPattern (Uniform (Reg 4)) s z).conjTranspose
        = (1 / 16 : ℂ) •
            (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩ * ρ
              * (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩).conjTranspose))

  ∧ (∀ A : Operator 2,
      Matrix.trace (∑ s : Fin 2 → Bool,
        mpPatternBranch mpWirePattern (Uniform (Reg 2)) s A) = Matrix.trace A
    ∧ ∀ B : Operator 4,
      Matrix.trace (∑ s : Fin 4 → Bool,
        mpPatternBranch mpCnotPattern (Uniform (Reg 4)) s B) = Matrix.trace B)

  ∧ (∀ θ : Fin 5 → ℝ,
      ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
        V * V.conjTranspose = 1 ∧ V.conjTranspose * V = 1 ∧
        ∀ (s : Fin 5 → Bool) (ρ : Operator 2),
          ∑ z : Fin 5 → Bool,
              (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z) * ρ
                * (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z).conjTranspose
            = (1 / 32 : ℂ) • (V * ρ * V.conjTranspose))

  ∧ (∃ W : Matrix (Fin 4) (Fin 2) ℂ,
      W.conjTranspose * W = 1 ∧
      ∀ (s : Fin 2 → Bool) (ρ : Operator 2),
        ∑ z : Fin 2 → Bool,
            (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z) * ρ
              * (mpPatternKraus mpTwoOutputPattern (Uniform (Reg 3)) s z).conjTranspose
          = (1 / 4 : ℂ) • (W * ρ * W.conjTranspose))

  ∧ (∀ a b : ℕ,
      mpLatticeEntangler a b
        = Qatlib.Concepts.MbqcFlow.FlowDecision.frameMatrix (mpLatticeEdges a b)
            * Qatlib.Concepts.MbqcFlow.FlowDecision.czMatrix (mpLatticeEdges a b))

  ∧ (mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩
        * (mpFinCnot ⟨1, by omega⟩ ⟨0, by omega⟩
            * mpFinCnot ⟨0, by omega⟩ ⟨1, by omega⟩)
      = mpWireSwapMatrix)

  ∧ (∀ b : Bool,
      Matrix.mulVec (mpVertexProjector 2 ⟨0, by omega⟩ b)
        (Qatlib.Concepts.MbqcFlow.FlowDecision.sourceResource mpEdge01) = mpDeletionState b)

  ∧ (∀ f1 f2 : Bool,
      mpLoadPauli f1 f2 * (mpLoadPauli f1 f2).conjTranspose = 1)

  ∧ (∀ (f1 f2 : Bool) (ρ : Operator 2),
      mpLoadPauli f1 f2
        * (mpLoadKraus f1 f2 * ρ * (mpLoadKraus f1 f2).conjTranspose)
        * (mpLoadPauli f1 f2).conjTranspose
        = (1 / 4 : ℂ) • ρ)

  ∧ (∀ θ : Fin 5 → ℝ, MpFlowCondition (mpEulerPattern θ))

  ∧ (∀ (n w m : ℕ) (P : MpPattern n w m), mpPeakSpace P = w + m)

  ∧ (∀ (n w m : ℕ) (P : MpPattern n w m) (resource : QState (Reg (w + m - n))),
      MpDeterministic P resource → w ≤ 2 * mpCommBits P)

  ∧ (∀ (n w m : ℕ) (P : MpPattern n w m) (resource : QState (Reg (w + m - n))),
      MpDeterministic P resource → w + m ≤ mpBitTime P)

  ∧ (∀ g : FiniteGateCode,
      (g = FiniteGateCode.h 0 ∨ g = FiniteGateCode.x 0
        ∨ g = FiniteGateCode.t 0 ∨ g = FiniteGateCode.tdg 0) →
      ∃ θ : Fin 5 → ℝ,
        ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
          V * V.conjTranspose = 1 ∧ V.conjTranspose * V = 1 ∧
          ∃ φ : ℝ, V = Complex.exp (Complex.ofReal φ * Complex.I) • mpFin1Gate g ∧
          ∀ (s : Fin 5 → Bool) (ρ : Operator 2),
            ∑ z : Fin 5 → Bool,
                (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z) * ρ
                  * (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z).conjTranspose
              = (1 / 32 : ℂ) • (V * ρ * V.conjTranspose))

  ∧ (∀ (θ : Fin 5 → ℝ) (b : ℕ), 1 ≤ b →
      ∃ V : Matrix (Fin 2) (Fin 2) ℂ,
        V * V.conjTranspose = 1 ∧ V.conjTranspose * V = 1 ∧
        (∀ (s : Fin 5 → Bool) (ρ : Operator 2),
          ∑ z : Fin 5 → Bool,
              (mpPatternKraus (mpEulerPattern fun j => mpRoundedAngle b (θ j))
                  (Uniform (Reg 5)) s z) * ρ
              * (mpPatternKraus (mpEulerPattern fun j => mpRoundedAngle b (θ j))
                  (Uniform (Reg 5)) s z).conjTranspose
            = (1 / 32 : ℂ) • (V * ρ * V.conjTranspose))
        ∧ ∀ (s z : Fin 5 → Bool) (i j : Fin 2),
            ‖(mpPatternKraus (mpEulerPattern fun j => mpRoundedAngle b (θ j))
                (Uniform (Reg 5)) s z) i j
              - (mpPatternKraus (mpEulerPattern θ) (Uniform (Reg 5)) s z) i j‖
              ≤ 2 ^ 11 * (2 : ℝ) ^ (-(b : ℤ)))

/-- The combined specification `Clause18Frozen` is false under the present definitions. -/
theorem clause7_counter : ¬ Clause18Frozen := by
  intro h
  exact clause7_counter_clause5b h.2.2.2.2.2.2.2.2.2.1
end Qatlib.Concepts.ClusterPatterns.CnotPatterns
