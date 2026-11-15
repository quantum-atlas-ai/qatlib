/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBoundsDefs

@[expose] public section
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Papers.QMAvsQCMA25.Forrelation
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds

open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds Matrix
open scoped BigOperators ComplexOrder

open scoped Classical in

private noncomputable instance instFockBasisFintype (N t : ℕ) :
    Fintype (FockBasis N t) :=
  inferInstanceAs (Fintype {v : Fin N → Fin (t + 1) // ∑ i, (v i : ℕ) = t})

private instance instFockBasisDecidableEq (N t : ℕ) : DecidableEq (FockBasis N t) :=
  inferInstanceAs (DecidableEq {v : Fin N → Fin (t + 1) // ∑ i, (v i : ℕ) = t})

private def bosonicBitFlip (N t : ℕ) (x : Fin N) (p : FockBasis N t × Bool) :
    FockBasis N t × Bool :=
  (p.1, Bool.xor p.2 (decide (((p.1.1 x : ℕ) % 2) = 1)))

private noncomputable def bosonicBitOracleBlock (N t : ℕ) (x : Fin N) :
    Matrix (FockBasis N t × Bool) (FockBasis N t × Bool) ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 ∧ p.2 = Bool.xor q.2 (decide (((q.1.1 x : ℕ) % 2) = 1)) then 1 else 0

private noncomputable def fockHadamardTensor (N t : ℕ) :
    Matrix (FockBasis N t × Bool) (FockBasis N t × Bool) ℂ :=
  Matrix.of fun p q => if p.1.1 = q.1.1 then Hadamard p.2 q.2 else 0

private noncomputable def bosonicPhaseEmbed (N t : ℕ) (x : Fin N) :
    Matrix (FockBasis N t × Bool) (FockBasis N t × Bool) ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 ∧ p.2 = q.2 then bosonicPhaseOracleBlock N t Real.pi x p.1 q.1 else 0

/-- The decompression entry is symmetric in its two Boolean indices. -/
private theorem decompressEntry_symmetric' (p : ℝ) (a b : Bool) :
    decompressEntry p a b = decompressEntry p b a := by
  cases a <;> cases b <;> rfl

/-- Every decompression entry is fixed by complex conjugation. -/
private theorem decompressEntry_star' (p : ℝ) (a b : Bool) :
    star (decompressEntry p a b) = decompressEntry p a b := by
  cases a <;> cases b <;> simp [decompressEntry]

/-- The decompression gate is self-adjoint. -/
private theorem decompressGate_selfadjoint' {I : Type} [Fintype I] [DecidableEq I]
    (p : ℝ) : (decompressGate (I := I) p)ᴴ = decompressGate p := by
  ext x y
  simp only [Matrix.conjTranspose_apply, decompressGate, Matrix.of_apply, star_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [decompressEntry_star', decompressEntry_symmetric']

/-- The decompression gate is unitary for `p` between zero and one. -/
private theorem decompressGate_mem_unitary' {I : Type} [Fintype I] [DecidableEq I]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact decompressGate_unitary p hp0 hp1

/-- The joint phase oracle is unitary. -/
private theorem jointPhaseOracle_unitary' {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] :
    jointPhaseOracle (I := I) (W := W) ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ :=
  phaseOracle_unitary (fun q : (((I × Bool) × W) × (I → Bool)) =>
    q.1.1.2 && q.2 q.1.1.1)

/-- The compressed oracle is unitary for `p` between zero and one. -/
private theorem compressedOracle_unitary' {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    compressedOracle (I := I) (W := W) p ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  have hF := decompressGate_mem_unitary' (I := I) p hp0 hp1
  have hF' : (decompressGate (I := I) p)ᴴ ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [decompressGate_selfadjoint']
    exact hF
  exact Submonoid.mul_mem _
    (Submonoid.mul_mem _ (tensorGate_unitary (Submonoid.one_mem _) hF')
      jointPhaseOracle_unitary')
    (tensorGate_unitary (Submonoid.one_mem _) hF)

/-- Tensor lifting a unitary circuit preserves circuit unitarity. -/
private theorem tensorLiftCircuit_unitary' {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (C : Circuit ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) : IsUnitaryCircuit (tensorLiftCircuit C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
      cases s with
      | gate U =>
          obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
          exact (isUnitaryCircuit_gate (TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ))
            (tensorLiftCircuit C)).mpr
            ⟨tensorGate_unitary hU (Submonoid.one_mem _), ih hC'⟩
      | query =>
          exact (isUnitaryCircuit_query (tensorLiftCircuit C)).mpr
            (ih ((isUnitaryCircuit_query C).mp hC))

/-- A compressed oracle run of a unitary circuit on a normalized state remains normalized for
`p` between zero and one. -/
private theorem compressedRunState_normalized' {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : Circuit ((I × Bool) × W)) (hC : IsUnitaryCircuit C)
    (ψ : QState ((I × Bool) × W)) (hψ : Normalized ψ) :
    Normalized (compressedRunState p C ψ) :=
  normalized_run _ (compressedOracle_unitary' p hp0 hp1) _ (tensorLiftCircuit_unitary' C hC)
    (normalized_tensorState hψ (normalized_ket _))

/-- A Boolean database records a new element at an index exactly when that index belongs to its
support. -/
private theorem databaseNewElement_iff {I : Type} [Fintype I] (d : I → Bool) (x : I) :
    DatabaseNewElement d x ↔ x ∈ databaseSupport d := by
  simp [DatabaseNewElement, databaseSupport]

/-- A Boolean database records a collision exactly when its support has cardinality at least
two. -/
private theorem databaseRecordsCollision_iff {I : Type} [Fintype I] [DecidableEq I]
    (d : I → Bool) :
    DatabaseRecordsCollision d ↔ 2 ≤ databaseCard d := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    have hxm : x ∈ databaseSupport d := by simp [databaseSupport, hx]
    have hym : y ∈ databaseSupport d := by simp [databaseSupport, hy]
    have h1 : 1 < (databaseSupport d).card :=
      Finset.one_lt_card.mpr ⟨x, hxm, y, hym, hxy⟩
    show 2 ≤ (databaseSupport d).card
    omega
  · intro h
    simp only [databaseCard] at h
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      Finset.one_lt_card.mp (show 1 < (databaseSupport d).card by omega)
    exact ⟨x, y, hxy, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩

/-- A natural number at least two has at least one unordered pair of distinct elements. -/
private theorem one_le_choose_two {c : ℕ} (h : 2 ≤ c) : (1 : ℝ) ≤ Nat.choose c 2 := by
  have h0 : 1 ≤ Nat.choose c 2 := by
    have := Nat.choose_pos h
    omega
  exact_mod_cast h0

/-- A nonnegative weight gated by a cardinality-at-least-two indicator is bounded by that weight
times the number of unordered pairs. -/
private theorem collisionIndicator_le {c : ℕ} {w : ℝ} (hw : 0 ≤ w) :
    (if 2 ≤ c then w else 0) ≤ (Nat.choose c 2 : ℝ) * w := by
  by_cases h : 2 ≤ c
  · rw [ite_eq_left h]
    calc w = 1 * w := (one_mul w).symm
      _ ≤ (Nat.choose c 2 : ℝ) * w := mul_le_mul_of_nonneg_right (one_le_choose_two h) hw
  · rw [ite_eq_right h]
    exact mul_nonneg (Nat.cast_nonneg _) hw

/-- Establishes compressed XOR equivalence, query-preserving bit-to-phase transport, the Boolean
database support characterizations, and the displayed expected-cardinality and collision
bounds for unitary compressed runs. -/
theorem g1 :
  CompressedXOREquivalence ∧
  (∀ (I W : Type) [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W] (x : I → Bool)
      (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)),
    QueryCount (bitToPhaseCircuit C) = QueryCount C ∧
      Run (workspacePhaseOracle (I := I) (W := W) x) (bitToPhaseCircuit C)
          (ApplyGate controlHadamard ψ)
        = Run (workspaceBitOracle (I := I) (W := W) x) C ψ) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (d : I → Bool),
    (DatabaseRecordsCollision d ↔ 2 ≤ databaseCard d) ∧
      ∀ x : I, DatabaseNewElement d x ↔ x ∈ databaseSupport d) ∧
  (∀ (I W : Type) [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W] (p : ℝ),
    0 ≤ p → p ≤ 1 →
    ∀ (t : ℕ) (C : Circuit ((I × Bool) × W)), QueryCount C ≤ t → IsUnitaryCircuit C →
      ∀ ψ : QState ((I × Bool) × W), Normalized ψ →
      (∑ q : (I × Bool) × W, ∑ d : I → Bool,
          (databaseCard d : ℝ) * ‖compressedRunState p C ψ (q, d)‖ ^ 2)
        ≤ t * (2 * Real.sqrt (p * (1 - p))) ∧
      (∑ q : (I × Bool) × W, ∑ d : I → Bool,
          if 2 ≤ databaseCard d then ‖compressedRunState p C ψ (q, d)‖ ^ 2 else 0)
        ≤ (Nat.choose t 2 : ℝ) * (2 * Real.sqrt (p * (1 - p))) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I W _ _ _ _ p hp0 hp1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro C ψ hC hψ
      exact compressedRunState_normalized' p hp0 hp1 C hC ψ hψ
    · intro C ψ t ht q d hd
      exact database_support_bound p hp0 hp1 C ψ t ht q d hd
    · intro C hC ψ hψ i t ht
      exact database_moment_bound p hp0 hp1 C hC ψ hψ i t ht
    · intro C ψ q q'
      exact compressed_marginal p hp0 hp1 C ψ q q'
  · intro I W _ _ _ _ x C ψ
    exact ⟨bitToPhaseCircuit_queryCount C, run_bitToPhaseCircuit x C ψ⟩
  · intro I _ _ d
    exact ⟨databaseRecordsCollision_iff d, fun x => databaseNewElement_iff d x⟩
  · intro I W _ _ _ _ p hp0 hp1 t C ht hC ψ hψ
    refine ⟨?_, ?_⟩
    · have hm := database_moment_bound (I := I) (W := W) p hp0 hp1 C hC ψ hψ 1 t ht
      simpa only [Nat.choose_one_right, pow_one] using hm
    · have hstep : ∀ (q : (I × Bool) × W) (d : I → Bool),
          (if 2 ≤ databaseCard d then ‖compressedRunState p C ψ (q, d)‖ ^ 2 else 0)
            ≤ (Nat.choose (databaseCard d) 2 : ℝ)
                * ‖compressedRunState p C ψ (q, d)‖ ^ 2 :=
        fun q d => collisionIndicator_le (sq_nonneg _)
      exact (Finset.sum_le_sum fun q _ =>
        Finset.sum_le_sum fun d _ => hstep q d).trans
        (database_moment_bound (I := I) (W := W) p hp0 hp1 C hC ψ hψ 2 t ht)

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
