/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.CompressedOracleBounds
public import Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Papers.QMAvsQCMA25.Forrelation Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.XorCompressedDatabaseIntertwining

open Matrix
open scoped BigOperators
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def xorDecode (p : ℝ) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)

def xorEncode (p : ℝ) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  TensorGate (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (decompressGate p)ᴴ

/-- The conjugate transpose of the identity matrix is the identity. -/
theorem matrix_one_conjTranspose {X : Type} [Fintype X] [DecidableEq X] :
    (1 : Matrix X X ℂ)ᴴ = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply, h, Ne.symm h]

/-- The conjugate transpose of `xorDecode` is `xorEncode`. -/
theorem xorEncode_eq_conjTranspose (p : ℝ) :
    (xorDecode (I := I) (W := W) p)ᴴ = xorEncode (I := I) (W := W) p := by
  rw [xorDecode, tensorGate_conjTranspose, matrix_one_conjTranspose, xorEncode]

def xorWriteAt (j : I) (b : Bool) (d : I → Bool) : I → Bool :=
  fun k => if k = j then b else d k

omit [Fintype I] in

/-- Writing the existing Boolean value at an address leaves the database unchanged. -/
theorem xorWriteAt_self (j : I) (d : I → Bool) : xorWriteAt j (d j) d = d := by
  funext k
  by_cases hk : k = j
  · simp [xorWriteAt, hk]
  · simp [xorWriteAt, hk]

omit [Fintype I] in

/-- If a Boolean value differs from the stored value, writing it is the same as writing the
negation of the stored value. -/
theorem xorWriteAt_ne {j : I} {b : Bool} {d : I → Bool} (h : d j ≠ b) :
    xorWriteAt j (!d j) d = xorWriteAt j b d := by
  funext k
  by_cases hk : k = j
  · subst k
    simp only [xorWriteAt]
    cases hdj : d j <;> cases b <;> simp_all
  · simp [xorWriteAt, hk]

/-- For a parameter in the closed unit interval, `decompressGate` multiplied by its conjugate
transpose is the identity. -/
theorem decompressGate_counit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    decompressGate (I := I) p * (decompressGate p)ᴴ = 1 := by
  have hU : decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact decompressGate_unitary p hp0 hp1
  simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff.mp hU

/-- For a parameter in the closed unit interval, `xorDecode` times `xorEncode` is the identity. -/
theorem xorDecode_mul_xorEncode (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    xorDecode (I := I) (W := W) p * xorEncode p = 1 := by
  simp only [xorDecode, xorEncode, tensorGate_mul, Matrix.one_mul,
    decompressGate_counit (I := I) p hp0 hp1, tensorGate_one]

/-- For a parameter in the closed unit interval, `xorEncode` times `xorDecode` is the identity. -/
theorem xorEncode_mul_xorDecode (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    xorEncode (I := I) (W := W) p * xorDecode p = 1 := by
  simp only [xorDecode, xorEncode, tensorGate_mul, Matrix.one_mul,
    decompressGate_unitary (I := I) p hp0 hp1, tensorGate_one]

/-- Applying `xorDecode` acts by `decompressGate` on each fixed algorithm-register slice. -/
theorem xorDecode_apply (p : ℝ) (v : QState (((I × Bool) × W) × (I → Bool)))
    (q : (I × Bool) × W) (x : I → Bool) :
    ApplyGate (xorDecode p) v (q, x) =
      ApplyGate (decompressGate p) (fun d => v (q, d)) x := by
  simp [xorDecode, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply]

/-- Decoding an empty database prepares the Bernoulli database state while preserving the
algorithm state. -/
theorem xorDecode_prep (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ψ : QState ((I × Bool) × W)) :
    ApplyGate (xorDecode p) (TensorState ψ (Ket (fun _ => false))) =
      TensorState ψ (bernoulliState p) := by
  rw [xorDecode, applyGate_tensorGate, applyGate_one,
    decompressGate_empty_database p hp0 hp1]

def xorPurifiedQuery :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  Matrix.of fun p q =>
    if p.2 = q.2 then workspaceBitOracle p.2 p.1 q.1 else 0

omit [Fintype I] in

/-- A finite sum restricted by equality to a fixed index evaluates the summand at that index. -/
theorem sum_ite_univ {X : Type} [Fintype X] [DecidableEq X] (x : X) (F : X → ℂ) :
    ∑ y : X, (if x = y then F y else 0) = F x := by
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left rfl]
  · intro b _ hb
    exact ite_eq_right (fun h => hb h.symm)
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- The purified XOR query acts on each fixed database slice by the corresponding workspace bit
oracle. -/
theorem xorPurifiedQuery_apply (v : QState (((I × Bool) × W) × (I → Bool)))
    (q : (I × Bool) × W) (x : I → Bool) :
    ApplyGate xorPurifiedQuery v (q, x) =
      ApplyGate (workspaceBitOracle x) (fun r => v (r, x)) q := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, xorPurifiedQuery,
    Matrix.of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  simp_rw [sum_ite_univ]

/-- A gate tensored with the identity acts on each fixed second-register slice by the original
gate. -/
theorem tensor_one_left_slice' {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (M : Matrix A A ℂ) (v : QState (A × B)) (a : A) (b : B) :
    ApplyGate (TensorGate M (1 : Matrix B B ℂ)) v (a, b) =
      ApplyGate M (fun x => v (x, b)) a := by
  simp [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

/-- Two matrices are equal if their actions agree on every computational basis ket. -/
theorem matrix_eq_of_applyGate_ket {X : Type} [Fintype X] [DecidableEq X]
    (A B : Matrix X X ℂ) (h : ∀ z : X, ApplyGate A (Ket z) = ApplyGate B (Ket z)) :
    A = B := by
  ext i j
  have hA : A i j = ApplyGate A (Ket j) i := by
    simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite]
  have hB : B i j = ApplyGate B (Ket j) i := by
    simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, mul_ite]
  rw [hA, hB, h j]

/-- The joint phase oracle applies the workspace phase oracle determined by a basis database and
preserves that database. -/
theorem jointPhaseOracle_tensor (ψ : QState ((I × Bool) × W)) (x : I → Bool) :
    ApplyGate jointPhaseOracle (TensorState ψ (Ket x)) =
      TensorState (ApplyGate (workspacePhaseOracle x) ψ) (Ket x) := by
  funext q
  obtain ⟨⟨r1, r2⟩, y⟩ := q
  have hL : ApplyGate jointPhaseOracle (TensorState ψ (Ket x)) ((r1, r2), y)
      = (if r1.2 && y r1.1 then (-1 : ℂ) else 1) * (ψ (r1, r2) * Ket x y) := by
    simp only [ApplyGate, jointPhaseOracle, Matrix.mulVec_diagonal, tensorState_apply]
  rw [hL, tensorState_apply]
  simp only [workspacePhaseOracle]
  rw [tensor_one_left_slice', ApplyGate, PhaseOracle, Matrix.mulVec_diagonal]
  by_cases hxy : x = y
  · subst y
    simp only [Ket]
    ring
  · rw [Ket, ite_eq_right (Ne.symm hxy)]
    ring

/-- The purified XOR query applies the workspace bit oracle determined by a basis database and
preserves that database. -/
theorem xorPurifiedQuery_tensor (ψ : QState ((I × Bool) × W)) (x : I → Bool) :
    ApplyGate xorPurifiedQuery (TensorState ψ (Ket x)) =
      TensorState (ApplyGate (workspaceBitOracle x) ψ) (Ket x) := by
  funext q
  obtain ⟨r, y⟩ := q
  rw [xorPurifiedQuery_apply]
  by_cases hxy : x = y
  · subst y
    simp only [TensorState, ket_self, mul_one]
  · have hslice : (fun v : (I × Bool) × W => TensorState ψ (Ket x) (v, y)) =
        fun _ => (0 : ℂ) := by
      funext v
      simp [TensorState, Ket, Ne.symm hxy]
    rw [hslice]
    have hzero : ApplyGate (workspaceBitOracle (I := I) (W := W) y)
        (fun _ => (0 : ℂ)) r = 0 := by
      simp [ApplyGate, Matrix.mulVec, dotProduct]
    rw [hzero, tensorState_apply, Ket, ite_eq_right (Ne.symm hxy), mul_zero]

/-- The database target Hadamard acts on a tensor state by applying `controlHadamard` to its
algorithm factor. -/
theorem databaseTargetHadamard_tensor (ψ : QState ((I × Bool) × W))
    (χ : QState (I → Bool)) :
    ApplyGate databaseTargetHadamard (TensorState ψ χ) =
      TensorState (ApplyGate controlHadamard ψ) χ := by
  rw [databaseTargetHadamard, applyGate_tensorGate, applyGate_one]

/-- Conjugating the joint phase oracle by the database target Hadamard gives the purified XOR
query. -/
theorem xorJointPhase_conj :
    databaseTargetHadamard (I := I) (W := W) * jointPhaseOracle * databaseTargetHadamard
      = xorPurifiedQuery := by
  refine matrix_eq_of_applyGate_ket
    (databaseTargetHadamard * jointPhaseOracle * databaseTargetHadamard)
    xorPurifiedQuery fun z => ?_
  obtain ⟨q, x⟩ := z
  rw [show Ket (q, x) = TensorState (Ket q) (Ket x) from (tensorState_ket_ket q x).symm,
    applyGate_mul, applyGate_mul, databaseTargetHadamard_tensor,
    jointPhaseOracle_tensor, databaseTargetHadamard_tensor, ← applyGate_mul,
    ← applyGate_mul,
    controlHadamard_mul_phase_mul_controlHadamard (I := I) (W := W) x,
    xorPurifiedQuery_tensor]

/-- On a basis ket, the purified XOR query XORs the addressed database bit into the target bit. -/
theorem xorPurifiedQuery_ket (j : I) (b : Bool) (w : W) (x : I → Bool) :
    ApplyGate xorPurifiedQuery (Ket (((j, b), w), x)) =
      Ket (((j, b ^^ x j), w), x) := by
  rw [show Ket (((j, b), w), x) = TensorState (Ket ((j, b), w)) (Ket x) from
      (tensorState_ket_ket ((j, b), w) x).symm,
    xorPurifiedQuery_tensor,
    show Ket ((j, b), w) = TensorState (Ket (j, b)) (Ket w) from
      (tensorState_ket_ket (j, b) w).symm,
    workspaceBitOracle, applyGate_tensorGate, applyGate_one,
    applyGate_bitOracleOn_ket, tensorState_ket_ket, tensorState_ket_ket]

/-- The database target Hadamard commutes with `xorDecode`. -/
theorem databaseTargetHadamard_comm_xorDecode (p : ℝ) :
    databaseTargetHadamard (I := I) (W := W) * xorDecode p
      = xorDecode p * databaseTargetHadamard := by
  simp only [databaseTargetHadamard, xorDecode, tensorGate_mul, Matrix.one_mul, mul_one]

/-- The database target Hadamard commutes with `xorEncode`. -/
theorem databaseTargetHadamard_comm_xorEncode (p : ℝ) :
    databaseTargetHadamard (I := I) (W := W) * xorEncode p
      = xorEncode p * databaseTargetHadamard := by
  simp only [databaseTargetHadamard, xorEncode, tensorGate_mul, Matrix.one_mul, mul_one]

/-- The compressed oracle is the joint phase oracle conjugated by encoding and decoding. -/
theorem compressedOracle_eq (p : ℝ) :
    compressedOracle (I := I) (W := W) p
      = xorEncode p * jointPhaseOracle * xorDecode p := rfl

/-- For a parameter in the closed unit interval, decoding intertwines the database XOR oracle
with the purified XOR query. -/
theorem xorDecode_mul_databaseXorOracle (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    xorDecode (I := I) (W := W) p * databaseXorOracle p = xorPurifiedQuery * xorDecode p := by
  have h5r : ∀ Z : Matrix (((I × Bool) × W) × (I → Bool))
      (((I × Bool) × W) × (I → Bool)) ℂ,
      xorDecode p * (xorEncode p * Z) = Z := by
    intro Z
    rw [← mul_assoc, xorDecode_mul_xorEncode p hp0 hp1, Matrix.one_mul]
  have h6r : ∀ Z : Matrix (((I × Bool) × W) × (I → Bool))
      (((I × Bool) × W) × (I → Bool)) ℂ,
      xorDecode p * (databaseTargetHadamard * Z)
        = databaseTargetHadamard * (xorDecode p * Z) := by
    intro Z
    rw [← mul_assoc, ← databaseTargetHadamard_comm_xorDecode p, mul_assoc]
  simp only [databaseXorOracle, compressedOracle_eq, mul_assoc, h6r, h5r]
  rw [← databaseTargetHadamard_comm_xorDecode p, ← mul_assoc, ← mul_assoc,
    xorJointPhase_conj]

/-- For a parameter in the closed unit interval, the database XOR oracle is the purified XOR
query conjugated by encoding and decoding. -/
theorem databaseXorOracle_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    databaseXorOracle (I := I) (W := W) p
      = xorEncode p * xorPurifiedQuery * xorDecode p := by
  have hE : xorEncode (I := I) (W := W) p * (xorDecode p * databaseXorOracle p)
      = databaseXorOracle p := by
    rw [← mul_assoc, xorEncode_mul_xorDecode p hp0 hp1, Matrix.one_mul]
  rw [← hE, xorDecode_mul_databaseXorOracle p hp0 hp1, mul_assoc]

/-- For a parameter in the closed unit interval, encoding intertwines the purified XOR query
with the database XOR oracle. -/
theorem databaseXorOracle_mul_xorEncode (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    databaseXorOracle (I := I) (W := W) p * xorEncode p
      = xorEncode p * xorPurifiedQuery := by
  rw [databaseXorOracle_eq p hp0 hp1, mul_assoc, xorDecode_mul_xorEncode p hp0 hp1,
    Matrix.mul_one]

/-- Decoding after a database XOR query equals applying the purified XOR query after decoding. -/
theorem xorDecode_databaseXorOracle_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (ApplyGate (databaseXorOracle p) v) =
      ApplyGate xorPurifiedQuery (ApplyGate (xorDecode p) v) := by
  rw [← applyGate_mul, ← applyGate_mul, xorDecode_mul_databaseXorOracle p hp0 hp1]

/-- Decoding commutes with every algorithm-register gate tensored with the database identity. -/
theorem xorDecode_comm_tensorGateL (p : ℝ)
    (U : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) :
    xorDecode (I := I) (W := W) p * TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ)
      = TensorGate U (1 : Matrix (I → Bool) (I → Bool) ℂ) * xorDecode p := by
  simp only [xorDecode, tensorGate_mul, Matrix.one_mul, mul_one]

/-- Decoding transports a single database XOR query to a purified XOR query. -/
theorem xorDecode_run_query (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (Run (databaseXorOracle p) [Step.query] v) =
      Run xorPurifiedQuery [Step.query] (ApplyGate (xorDecode p) v) := by
  simp only [run_query, run_nil]
  exact xorDecode_databaseXorOracle_apply p hp0 hp1 v

def xorPhysicalStep (p : ℝ) (s : Step (((I × Bool) × W) × (I → Bool))) :
    Step (((I × Bool) × W) × (I → Bool)) :=
  match s with
  | Step.gate U => Step.gate (xorDecode p * U * xorEncode p)
  | Step.query => Step.query

def xorPhysicalCircuit (p : ℝ) (D : Circuit (((I × Bool) × W) × (I → Bool))) :
    Circuit (((I × Bool) × W) × (I → Bool)) :=
  D.map (xorPhysicalStep p)

/-- The physical-circuit transformation sends the empty circuit to the empty circuit. -/
theorem xorPhysicalCircuit_nil (p : ℝ) :
    xorPhysicalCircuit p ([] : Circuit (((I × Bool) × W) × (I → Bool))) = [] := rfl

/-- The physical-circuit transformation acts on a nonempty circuit by transforming its head step
and tail. -/
theorem xorPhysicalCircuit_cons (p : ℝ)
    (s : Step (((I × Bool) × W) × (I → Bool)))
    (D : Circuit (((I × Bool) × W) × (I → Bool))) :
    xorPhysicalCircuit p (s :: D) = xorPhysicalStep p s :: xorPhysicalCircuit p D := rfl

/-- Decoding transports gate application to application of the gate conjugated by decoding and
encoding. -/
theorem xorDecode_applyGate (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (ApplyGate U v)
      = ApplyGate (xorDecode p * U * xorEncode p) (ApplyGate (xorDecode p) v) := by
  rw [← applyGate_mul, ← applyGate_mul, mul_assoc,
    xorEncode_mul_xorDecode p hp0 hp1, Matrix.mul_one]

/-- Decoding transports an arbitrary database XOR circuit to its physical circuit with purified
XOR queries. -/
theorem xorDecode_run_transport (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Circuit (((I × Bool) × W) × (I → Bool)))
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (Run (databaseXorOracle p) D v)
      = Run xorPurifiedQuery (xorPhysicalCircuit p D) (ApplyGate (xorDecode p) v) := by
  induction D generalizing v with
  | nil => rfl
  | cons s D ih =>
    cases s with
    | gate U =>
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, run_gate]
      rw [ih, xorDecode_applyGate p hp0 hp1 U]
    | query =>
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, run_query]
      rw [ih, xorDecode_databaseXorOracle_apply p hp0 hp1]

/-- The physical-circuit transformation preserves query count. -/
theorem xorPhysicalCircuit_queryCount (p : ℝ)
    (D : Circuit (((I × Bool) × W) × (I → Bool))) :
    QueryCount (xorPhysicalCircuit p D) = QueryCount D := by
  induction D with
  | nil => rfl
  | cons s D ih =>
    cases s <;>
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, queryCount_gate,
        queryCount_query, ih]

def IsAlgorithmCircuit (D : Circuit (((I × Bool) × W) × (I → Bool))) : Prop :=
  ∀ U : Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ,
    Step.gate U ∈ D →
      ∃ V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ,
        U = TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ)

/-- Conjugating an algorithm-register gate by decoding and encoding leaves it unchanged. -/
theorem xorDecode_mul_tensorGateL_xorEncode (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (V : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) :
    xorDecode (I := I) (W := W) p
        * TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ) * xorEncode p
      = TensorGate V (1 : Matrix (I → Bool) (I → Bool) ℂ) := by
  rw [xorDecode_comm_tensorGateL p, mul_assoc, xorDecode_mul_xorEncode p hp0 hp1,
    Matrix.mul_one]

/-- For a parameter in the closed unit interval, the physical-circuit transformation fixes
algorithm circuits. -/
theorem xorPhysicalCircuit_eq_of_isAlgorithmCircuit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Circuit (((I × Bool) × W) × (I → Bool))) :
    IsAlgorithmCircuit D → xorPhysicalCircuit p D = D := by
  induction D with
  | nil => intro _; rfl
  | cons s D ih =>
    intro hD
    cases s with
    | gate U =>
      obtain ⟨V, hV⟩ := hD U List.mem_cons_self
      have hrest := ih (fun U' hU' => hD U' (List.mem_cons_of_mem _ hU'))
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, hV,
        xorDecode_mul_tensorGateL_xorEncode p hp0 hp1, hrest]
    | query =>
      have hrest := ih (fun U' hU' => hD U' (List.mem_cons_of_mem _ hU'))
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, hrest]

omit [DecidableEq I] [Fintype W] [DecidableEq W] in

/-- Tensor lifting any algorithm circuit produces an `IsAlgorithmCircuit` circuit. -/
theorem isAlgorithmCircuit_tensorLiftCircuit (C : Circuit ((I × Bool) × W)) :
    IsAlgorithmCircuit (tensorLiftCircuit (I := I) (W := W) C) := by
  intro U hU
  simp only [tensorLiftCircuit, List.mem_map] at hU
  obtain ⟨s, _, hs⟩ := hU
  cases s with
  | gate V =>
    injection hs with hs'
    exact ⟨V, hs'.symm⟩
  | query => exact absurd hs (by simp [tensorLiftStep])

omit [DecidableEq I] [Fintype W] [DecidableEq W] in

/-- The empty circuit satisfies `IsAlgorithmCircuit`. -/
theorem isAlgorithmCircuit_nil :
    IsAlgorithmCircuit ([] : Circuit (((I × Bool) × W) × (I → Bool))) := by
  intro U hU
  simp at hU

omit [DecidableEq I] [Fintype W] [DecidableEq W] in

/-- Prepending a query preserves `IsAlgorithmCircuit`. -/
theorem isAlgorithmCircuit_cons_query {D : Circuit (((I × Bool) × W) × (I → Bool))}
    (hD : IsAlgorithmCircuit D) : IsAlgorithmCircuit (Step.query :: D) := by
  intro U hU
  rcases List.mem_cons.mp hU with hU | hU
  · exact absurd hU (by simp)
  · exact hD U hU

omit [DecidableEq I] [Fintype W] [DecidableEq W] in

/-- Prepending a query and an algorithm-register gate tensored with the database identity
preserves `IsAlgorithmCircuit`. -/
theorem isAlgorithmCircuit_cons_query_gate (U : Matrix ((I × Bool) × W)
    ((I × Bool) × W) ℂ) {D : Circuit (((I × Bool) × W) × (I → Bool))}
    (hD : IsAlgorithmCircuit D) :
    IsAlgorithmCircuit (Step.query :: Step.gate (TensorGate U
      (1 : Matrix (I → Bool) (I → Bool) ℂ)) :: D) := by
  intro V hV
  rcases List.mem_cons.mp hV with hV | hV
  · exact absurd hV (by simp)
  · rcases List.mem_cons.mp hV with hV | hV
    · injection hV with hV'
      exact ⟨U, hV'⟩
    · exact hD V hV

/-- For algorithm circuits, decoding transports the database XOR run to the same circuit with
purified XOR queries. -/
theorem xorDecode_run_transport_algorithm (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Circuit (((I × Bool) × W) × (I → Bool))) (hD : IsAlgorithmCircuit D)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (Run (databaseXorOracle p) D v)
      = Run xorPurifiedQuery D (ApplyGate (xorDecode p) v) := by
  rw [xorDecode_run_transport p hp0 hp1 D v,
    xorPhysicalCircuit_eq_of_isAlgorithmCircuit p hp0 hp1 D hD]

/-- Decoding an algorithm-circuit run from an empty database equals its purified XOR run from a
Bernoulli database state. -/
theorem xorDecode_run_from_empty (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Circuit (((I × Bool) × W) × (I → Bool))) (hD : IsAlgorithmCircuit D)
    (ψ : QState ((I × Bool) × W)) :
    ApplyGate (xorDecode p)
        (Run (databaseXorOracle p) D (TensorState ψ (Ket (fun _ => false))))
      = Run xorPurifiedQuery D (TensorState ψ (bernoulliState p)) := by
  rw [xorDecode_run_transport_algorithm p hp0 hp1 D hD, xorDecode_prep p hp0 hp1 ψ]

/-- The purified XOR query squared is the identity. -/
theorem xorPurifiedQuery_mul_self :
    xorPurifiedQuery (I := I) (W := W) * xorPurifiedQuery = 1 := by
  refine matrix_eq_of_applyGate_ket (xorPurifiedQuery * xorPurifiedQuery) 1 fun z => ?_
  obtain ⟨⟨⟨j, b⟩, w⟩, x⟩ := z
  rw [applyGate_mul, xorPurifiedQuery_ket, xorPurifiedQuery_ket, applyGate_one]
  cases hb : b <;> cases hx : x j <;> rfl

/-- For a parameter in the closed unit interval, the database XOR oracle squared is the
identity. -/
theorem databaseXorOracle_mul_self (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    databaseXorOracle (I := I) (W := W) p * databaseXorOracle p = 1 := by
  rw [databaseXorOracle_eq p hp0 hp1,
    Matrix.mul_assoc (xorEncode p * xorPurifiedQuery) (xorDecode p)
      (xorEncode p * xorPurifiedQuery * xorDecode p),
    ← Matrix.mul_assoc (xorDecode p) (xorEncode p * xorPurifiedQuery) (xorDecode p),
    ← Matrix.mul_assoc (xorDecode p) (xorEncode p) xorPurifiedQuery,
    xorDecode_mul_xorEncode p hp0 hp1, Matrix.one_mul,
    Matrix.mul_assoc (xorEncode p) xorPurifiedQuery (xorPurifiedQuery * xorDecode p),
    ← Matrix.mul_assoc xorPurifiedQuery xorPurifiedQuery (xorDecode p),
    xorPurifiedQuery_mul_self, Matrix.one_mul,
    xorEncode_mul_xorDecode p hp0 hp1]

/-- The conjugate transpose of `xorEncode` is `xorDecode`. -/
theorem xorEncode_conjTranspose (p : ℝ) :
    (xorEncode (I := I) (W := W) p)ᴴ = xorDecode p := by
  rw [xorEncode, tensorGate_conjTranspose, matrix_one_conjTranspose,
    Matrix.conjTranspose_conjTranspose, xorDecode]

/-- The joint phase oracle squared is the identity. -/
theorem jointPhaseOracle_mul_self :
    jointPhaseOracle (I := I) (W := W) * jointPhaseOracle = 1 := by
  ext q q'
  simp only [Matrix.mul_diagonal, jointPhaseOracle, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hqq : q = q'
  · subst q'
    by_cases hc : q.1.1.2 && q.2 q.1.1.1 <;> simp [hc]
  · rw [ite_eq_right hqq, ite_eq_right hqq, zero_mul]

omit [Fintype W] in

/-- The joint phase oracle is self-adjoint. -/
theorem jointPhaseOracle_conjTranspose :
    (jointPhaseOracle (I := I) (W := W))ᴴ = jointPhaseOracle := by
  ext q q'
  have hL : ((jointPhaseOracle (I := I) (W := W))ᴴ) q q'
      = star (if q' = q then (if q'.1.1.2 && q'.2 q'.1.1.1 then (-1 : ℂ) else 1) else 0) := by
    rfl
  have hR : (jointPhaseOracle (I := I) (W := W)) q q'
      = if q = q' then (if q.1.1.2 && q.2 q.1.1.1 then (-1 : ℂ) else 1) else 0 := by
    simp only [jointPhaseOracle, Matrix.diagonal_apply]
  rw [hL, hR]
  by_cases hqq : q = q'
  · subst q'
    rw [ite_eq_left rfl]
    by_cases hc : q.1.1.2 && q.2 q.1.1.1 <;> simp [hc]
  · rw [ite_eq_right (Ne.symm hqq), ite_eq_right hqq]
    simp

/-- The joint phase oracle is unitary. -/
theorem jointPhaseOracle_unitary' :
    jointPhaseOracle (I := I) (W := W) ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    jointPhaseOracle_conjTranspose, jointPhaseOracle_mul_self]

/-- The controlled Hadamard is unitary. -/
theorem controlHadamard_unitary' :
    controlHadamard (I := I) (W := W) ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
  tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

/-- The database target Hadamard is unitary. -/
theorem databaseTargetHadamard_unitary :
    databaseTargetHadamard (I := I) (W := W) ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  rw [databaseTargetHadamard]
  exact tensorGate_unitary controlHadamard_unitary' (Submonoid.one_mem _)

/-- The database target Hadamard is self-adjoint. -/
theorem databaseTargetHadamard_conjTranspose :
    (databaseTargetHadamard (I := I) (W := W))ᴴ = databaseTargetHadamard := by
  rw [databaseTargetHadamard, tensorGate_conjTranspose, matrix_one_conjTranspose,
    controlHadamard, tensorGate_conjTranspose, tensorGate_conjTranspose,
    matrix_one_conjTranspose, matrix_one_conjTranspose, hadamard_conjTranspose]

/-- The database target Hadamard squared is the identity. -/
theorem databaseTargetHadamard_mul_self :
    databaseTargetHadamard (I := I) (W := W) * databaseTargetHadamard = 1 := by
  simp only [databaseTargetHadamard, controlHadamard, tensorGate_mul, mul_one,
    hadamard_mul_self, tensorGate_one]

/-- The compressed oracle is self-adjoint. -/
theorem compressedOracle_conjTranspose (p : ℝ) :
    (compressedOracle (I := I) (W := W) p)ᴴ = compressedOracle p := by
  rw [compressedOracle_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    xorEncode_eq_conjTranspose, jointPhaseOracle_conjTranspose, xorEncode_conjTranspose,
    ← mul_assoc, ← compressedOracle_eq]

/-- The purified XOR query is self-adjoint. -/
theorem xorPurifiedQuery_conjTranspose :
    (xorPurifiedQuery (I := I) (W := W))ᴴ = xorPurifiedQuery := by
  have h : (xorPurifiedQuery (I := I) (W := W))ᴴ
      = (databaseTargetHadamard * jointPhaseOracle * databaseTargetHadamard)ᴴ := by
    rw [xorJointPhase_conj]
  rw [h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    databaseTargetHadamard_conjTranspose, jointPhaseOracle_conjTranspose,
    ← mul_assoc, xorJointPhase_conj]

/-- The database XOR oracle is self-adjoint. -/
theorem databaseXorOracle_conjTranspose (p : ℝ) :
    (databaseXorOracle (I := I) (W := W) p)ᴴ = databaseXorOracle p := by
  rw [databaseXorOracle, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    databaseTargetHadamard_conjTranspose, compressedOracle_conjTranspose,
    ← mul_assoc]

/-- The purified XOR query is unitary. -/
theorem xorPurifiedQuery_unitary :
    xorPurifiedQuery (I := I) (W := W) ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    xorPurifiedQuery_conjTranspose, xorPurifiedQuery_mul_self]

/-- For a parameter in the closed unit interval, `xorDecode` is unitary. -/
theorem xorDecode_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    xorDecode (I := I) (W := W) p ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  have hV : decompressGate (I := I) p ∈ Matrix.unitaryGroup (I → Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact decompressGate_unitary p hp0 hp1
  rw [xorDecode]
  exact tensorGate_unitary (Submonoid.one_mem _) hV

/-- The conjugate transpose of a unitary matrix is unitary. -/
theorem conjTranspose_mem_unitaryGroup' {X : Type} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} (hA : A ∈ Matrix.unitaryGroup X ℂ) :
    Aᴴ ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hA

/-- For a parameter in the closed unit interval, `xorEncode` is unitary. -/
theorem xorEncode_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    xorEncode (I := I) (W := W) p ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  rw [← xorEncode_eq_conjTranspose]
  exact conjTranspose_mem_unitaryGroup' (xorDecode_unitary p hp0 hp1)

/-- For a parameter in the closed unit interval, physical-circuit transformation preserves
unitarity of circuits. -/
theorem xorPhysicalCircuit_isUnitaryCircuit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (D : Circuit (((I × Bool) × W) × (I → Bool))) :
    IsUnitaryCircuit D → IsUnitaryCircuit (xorPhysicalCircuit p D) := by
  induction D with
  | nil => intro _; exact isUnitaryCircuit_nil
  | cons s D ih =>
    intro hD
    cases s with
    | gate U =>
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, isUnitaryCircuit_gate]
      refine ⟨?_, ih ((isUnitaryCircuit_gate U D).mp hD).2⟩
      exact Submonoid.mul_mem _
        (Submonoid.mul_mem _ (xorDecode_unitary p hp0 hp1) (hD U List.mem_cons_self))
        (xorEncode_unitary p hp0 hp1)
    | query =>
      simp only [xorPhysicalCircuit_cons, xorPhysicalStep, isUnitaryCircuit_query]
      exact ih ((isUnitaryCircuit_query D).mp hD)

/-- For a parameter in the closed unit interval, the database XOR oracle is unitary. -/
theorem databaseXorOracle_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    databaseXorOracle (I := I) (W := W) p ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    databaseXorOracle_conjTranspose, databaseXorOracle_mul_self p hp0 hp1]

/-- Applying a unitary gate preserves total Born mass. -/
theorem applyGate_bornMass {X : Type} [Fintype X] [DecidableEq X]
    {U : Matrix X X ℂ} (hU : U ∈ Matrix.unitaryGroup X ℂ) (v : QState X) :
    ∑ z, BornProb (ApplyGate U v) z = ∑ z, BornProb v z := by
  have h := inner_applyGate hU v v
  rw [inner_self, inner_self] at h
  have h' : Complex.ofReal (∑ z : X, BornProb (ApplyGate U v) z)
      = Complex.ofReal (∑ z : X, BornProb v z) := by
    rw [Complex.ofReal_sum, Complex.ofReal_sum]
    exact h
  exact Complex.ofReal_inj.mp h'

/-- For a parameter in the closed unit interval, the database XOR oracle preserves total Born
mass. -/
theorem databaseXorOracle_bornMass (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) :
    ∑ z, BornProb (ApplyGate (databaseXorOracle p) v) z = ∑ z, BornProb v z :=
  applyGate_bornMass (databaseXorOracle_unitary p hp0 hp1) v

/-- For a parameter in the closed unit interval, the database XOR oracle preserves state
normalization. -/
theorem databaseXorOracle_normalized (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : QState (((I × Bool) × W) × (I → Bool))) (hv : Normalized v) :
    Normalized (ApplyGate (databaseXorOracle p) v) :=
  normalized_applyGate (databaseXorOracle_unitary p hp0 hp1) hv

/-- Running a unitary circuit with a unitary oracle preserves total Born mass. -/
theorem run_bornMass {X : Type} [Fintype X] [DecidableEq X]
    {O : Matrix X X ℂ} (hO : O ∈ Matrix.unitaryGroup X ℂ) :
    ∀ (D : Circuit X), IsUnitaryCircuit D → ∀ (v : QState X),
      ∑ z, BornProb (Run O D v) z = ∑ z, BornProb v z := by
  intro D
  induction D with
  | nil => intro _ _; rfl
  | cons s D ih =>
    rintro hD v
    cases s with
    | gate U =>
      rw [run_gate, ih ((isUnitaryCircuit_gate U D).mp hD).2,
        applyGate_bornMass (hD U List.mem_cons_self)]
    | query =>
      rw [run_query, ih ((isUnitaryCircuit_query D).mp hD), applyGate_bornMass hO]

/-- Running a unitary circuit with a unitary oracle preserves normalization. -/
theorem run_preserves_normalized {X : Type} [Fintype X] [DecidableEq X]
    {O : Matrix X X ℂ} (hO : O ∈ Matrix.unitaryGroup X ℂ)
    (D : Circuit X) : IsUnitaryCircuit D → ∀ (v : QState X), Normalized v →
      Normalized (Run O D v) := by
  induction D with
  | nil => intro _ _ hv; exact hv
  | cons s D ih =>
    intro hD v hv
    cases s with
    | gate U =>
      rw [run_gate]
      exact ih ((isUnitaryCircuit_gate U D).mp hD).2 (ApplyGate U v)
        (normalized_applyGate (hD U List.mem_cons_self) hv)
    | query =>
      rw [run_query]
      exact ih ((isUnitaryCircuit_query D).mp hD) (ApplyGate O v)
        (normalized_applyGate hO hv)

/-- Repeated database XOR queries act as the identity for an even number of repetitions and as
one query for an odd number. -/
theorem databaseXorOracle_run_repeat (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (v : QState (((I × Bool) × W) × (I → Bool))) :
    Run (databaseXorOracle p) (RepeatCircuit [Step.query] k) v
      = if k % 2 = 0 then v else ApplyGate (databaseXorOracle p) v := by
  induction k generalizing v with
  | zero => simp [RepeatCircuit]
  | succ k ih =>
    rw [RepeatCircuit, run_append, run_query, run_nil, ih]
    by_cases hk : k % 2 = 0
    · rw [ite_eq_left hk]
      have h1 : (k + 1) % 2 = 1 := by omega
      rw [h1, ite_eq_right one_ne_zero]
    · rw [ite_eq_right hk]
      have h0 : (k + 1) % 2 = 0 := by omega
      rw [h0, ite_eq_left rfl, ← applyGate_mul, databaseXorOracle_mul_self p hp0 hp1,
        applyGate_one]

omit [Fintype I] in

/-- A database differing from another only at one address is obtained by writing its value at
that address. -/
theorem xorWriteAt_eq_of_locality (j : I) (d e : I → Bool)
    (hloc : ∀ k, k ≠ j → d k = e k) : e = xorWriteAt j (e j) d := by
  funext k
  by_cases hk : k = j
  · subst k; simp [xorWriteAt]
  · rw [xorWriteAt, ite_eq_right hk, hloc k hk]

/-- A nonzero database XOR oracle entry relates databases by writing either false or true at the
queried address. -/
theorem databaseXorOracle_output_eq_xorWriteAt (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : databaseXorOracle p (((j, b), w), d) (((j, a), w), e) ≠ 0) :
    e = xorWriteAt j false d ∨ e = xorWriteAt j true d := by
  have hloc := databaseXorOracle_locality p hp0 hp1 j b a w d e h
  rw [xorWriteAt_eq_of_locality j d e hloc]
  cases hej : e j <;> simp

/-- At a fresh address, a nonzero database XOR oracle entry either preserves the database or
writes true there. -/
theorem databaseXorOracle_output_of_fresh (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d e : I → Bool) (hdj : d j = false)
    (h : databaseXorOracle p (((j, b), w), d) (((j, a), w), e) ≠ 0) :
    e = d ∨ e = xorWriteAt j true d := by
  rcases databaseXorOracle_output_eq_xorWriteAt p hp0 hp1 j b a w d e h with h' | h'
  · exact Or.inl (h'.trans (by rw [← hdj]; exact xorWriteAt_self j d))
  · exact Or.inr h'

/-- Computes the database XOR oracle entry associated with writing true at a fresh address in
terms of Hadamard entries and the Bernoulli parameter. -/
theorem databaseXorOracle_write_entry (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d : I → Bool) (hdj : d j = false) :
    databaseXorOracle p (((j, b), w), d) (((j, a), w), xorWriteAt j true d)
      = Hadamard b true * Complex.ofReal (2 * Real.sqrt (p * (1 - p))) * Hadamard true a := by
  have hloc : ∀ k, k ≠ j → d k = xorWriteAt j true d k := by
    intro k hk; rw [xorWriteAt, ite_eq_right hk]
  have hself : xorWriteAt j true d j = true := by rw [xorWriteAt, ite_eq_left rfl]
  have hne : d ≠ xorWriteAt j true d := by
    intro he
    rw [he, hself] at hdj
    exact Bool.noConfusion hdj
  rw [databaseXorOracle_entry p hp0 hp1, Finset.sum_eq_single true]
  · rw [ite_eq_left hloc, hself, hdj]
    simp [compressedQueryEntry]
  · intro c _ hc
    cases c
    · rw [ite_eq_right hc, ite_eq_right hne]
      ring
    · exact absurd rfl hc
  · intro hmem
    exact absurd (Finset.mem_univ true) hmem

/-- Writing true at an address inserts that address into the database support. -/
theorem databaseSupport_xorWriteAt_true (j : I) (d : I → Bool) :
    databaseSupport (xorWriteAt j true d) = insert j (databaseSupport d) := by
  ext k
  simp only [databaseSupport, Finset.mem_filter, Finset.mem_univ, true_and, xorWriteAt]
  by_cases hk : k = j
  · simp [hk]
  · simp [hk]

/-- Writing true at a previously false address increases database cardinality by one. -/
theorem databaseCard_xorWriteAt_true (j : I) (d : I → Bool) (hdj : d j = false) :
    databaseCard (xorWriteAt j true d) = databaseCard d + 1 := by
  simp only [databaseCard, databaseSupport_xorWriteAt_true]
  have hj : j ∉ databaseSupport d := by
    intro hmem
    rw [databaseSupport, Finset.mem_filter, hdj] at hmem
    exact Bool.noConfusion hmem.2
  rw [Finset.card_insert_of_notMem hj]

/-- Writing any Boolean value at an already true address cannot increase database cardinality. -/
theorem databaseCard_xorWriteAt_le (j : I) (b : Bool) (d : I → Bool) (hdj : d j = true) :
    databaseCard (xorWriteAt j b d) ≤ databaseCard d := by
  cases b
  · have hsub : databaseSupport (xorWriteAt j false d) ⊆ databaseSupport d := by
      intro k hk
      rw [databaseSupport, Finset.mem_filter] at hk ⊢
      refine ⟨hk.1, ?_⟩
      by_cases hkj : k = j
      · subst k
        rw [xorWriteAt, ite_eq_left rfl] at hk
        exact Bool.noConfusion hk.2
      · rw [xorWriteAt, ite_eq_right hkj] at hk
        exact hk.2
    exact Finset.card_le_card hsub
  · exact le_of_eq (congrArg databaseCard (by rw [← hdj]; exact xorWriteAt_self j d))

/-- A nonzero database XOR oracle entry at an already true address cannot increase database
cardinality. -/
theorem databaseXorOracle_collision_card (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (b a : Bool) (w : W) (d e : I → Bool) (hdj : d j = true)
    (h : databaseXorOracle p (((j, b), w), d) (((j, a), w), e) ≠ 0) :
    databaseCard e ≤ databaseCard d := by
  rcases databaseXorOracle_output_eq_xorWriteAt p hp0 hp1 j b a w d e h with rfl | rfl
  · exact databaseCard_xorWriteAt_le j false d hdj
  · exact le_of_eq (congrArg databaseCard (by rw [← hdj]; exact xorWriteAt_self j d))

omit [Fintype I] [DecidableEq I] in

/-- The Boolean-valued database stores `some true` exactly at addresses whose Boolean value is
true. -/
theorem booleanValuedDatabase_eq_some_true_iff {d : I → Bool} {k : I} :
    booleanValuedDatabase d k = some true ↔ d k = true := by
  simp [booleanValuedDatabase]

omit [Fintype I] in

/-- Writing true in the Boolean database corresponds to `valuedUpdate` in its valued
representation. -/
theorem booleanValuedDatabase_xorWriteAt_true (j : I) (d : I → Bool) :
    booleanValuedDatabase (xorWriteAt j true d)
      = valuedUpdate (booleanValuedDatabase d) j true := by
  funext k
  by_cases hk : k = j
  · subst k; simp [booleanValuedDatabase, valuedUpdate, xorWriteAt]
  · simp [booleanValuedDatabase, valuedUpdate, xorWriteAt, hk]

/-- Updating an address to true gives a new element there exactly when every other Boolean
database entry is false. -/
theorem valuedUpdate_newElement_iff (j : I) (d : I → Bool) :
    newElement (valuedUpdate (booleanValuedDatabase d) j true) j true ↔
      ∀ k, k ≠ j → d k = false := by
  constructor
  · intro h k hk
    have h2 := h.2 k hk
    rw [valuedUpdate_ne _ _ _ hk] at h2
    exact Bool.eq_false_iff.mpr (booleanValuedDatabase_eq_some_true_iff.not.mp h2)
  · intro h
    refine ⟨valuedUpdate_at _ _ _, fun k hk => ?_⟩
    rw [valuedUpdate_ne _ _ _ hk]
    intro hdk
    have hcontr : d k = true := booleanValuedDatabase_eq_some_true_iff.mp hdk
    rw [h k hk] at hcontr
    exact Bool.noConfusion hcontr

/-- Two distinct true database entries make a true-valued query at one of them a duplicate-value
query. -/
theorem booleanValuedDatabase_duplicateValueQuery (j k : I) (d : I → Bool)
    (hkj : k ≠ j) (hdj : d j = true) (hdk : d k = true) :
    duplicateValueQuery (booleanValuedDatabase d) j true :=
  ⟨booleanValuedDatabase_eq_some_true_iff.mpr hdj, k, hkj,
    booleanValuedDatabase_eq_some_true_iff.mpr hdk⟩

/-- Updating one of two distinct true entries yields a value collision in the valued database. -/
theorem booleanValuedDatabase_shadow_valueCollision (j k : I) (d : I → Bool)
    (hkj : k ≠ j) (hdj : d j = true) (hdk : d k = true) :
    valueCollision (valuedUpdate (booleanValuedDatabase d) j true) :=
  valuedUpdate_valueCollision _ _ _ (booleanValuedDatabase_duplicateValueQuery j k d hkj hdj hdk)

omit [Fintype I] in

/-- Updating an already true entry in the valued representation leaves it unchanged. -/
theorem valuedUpdate_shadow_idem (j : I) (d : I → Bool) (hdj : d j = true) :
    valuedUpdate (booleanValuedDatabase d) j true = booleanValuedDatabase d := by
  rw [← booleanValuedDatabase_xorWriteAt_true, ← hdj, xorWriteAt_self j d]

/-- Reading a true database entry is either a duplicate-value query or a new element. -/
theorem booleanValuedDatabase_read_dichotomy (j : I) (d : I → Bool) (hdj : d j = true) :
    duplicateValueQuery (booleanValuedDatabase d) j true ∨
      newElement (booleanValuedDatabase d) j true :=
  duplicateValueQuery_or_newElement _ _ _ (booleanValuedDatabase_eq_some_true_iff.mpr hdj)

/-- Expands a gate application coordinate as a finite matrix-vector sum. -/
theorem applyGate_eq_sum {X : Type} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℂ) (v : QState X) (y : X) :
    ApplyGate A v y = ∑ x : X, A y x * v x := by
  simp [ApplyGate, Matrix.mulVec, dotProduct]

/-- A nonzero finite sum of complex numbers has a nonzero summand. -/
theorem exists_ne_zero_of_sum_ne_zero {X : Type} [Fintype X] [DecidableEq X]
    {F : X → ℂ} (h : ∑ x, F x ≠ 0) : ∃ x : X, F x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (Finset.sum_eq_zero fun x _ => hcon x)

/-- Writing one Boolean database entry increases cardinality by at most one. -/
theorem databaseCard_xorWriteAt_le_one (j : I) (b : Bool) (d : I → Bool) :
    databaseCard (xorWriteAt j b d) ≤ databaseCard d + 1 := by
  have hsub : databaseSupport (xorWriteAt j b d) ⊆ insert j (databaseSupport d) := by
    intro k hk
    simp only [databaseSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    by_cases hkj : k = j
    · exact Finset.mem_insert.mpr (Or.inl hkj)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [xorWriteAt, ite_eq_right hkj] at hk
      simp only [databaseSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

inductive XorReachable : List I → (I → Bool) → (I → Bool) → Prop
  | nil (d : I → Bool) : XorReachable [] d d
  | cons (j : I) (l : List I) (d d' e : I → Bool) (b : Bool)
      (hw : d' = xorWriteAt j b d) (h : XorReachable l d' e) :
      XorReachable (j :: l) d e

omit [Fintype I] in

/-- Appending an address to a reachability list permits a further write at that address. -/
theorem xorReachable_snoc {l : List I} {d : I → Bool} (j : I) :
    ∀ {d' : I → Bool}, XorReachable l d d' → ∀ (b : Bool) {e : I → Bool},
      e = xorWriteAt j b d' → XorReachable (l ++ [j]) d e := by
  intro d' h
  induction h with
  | nil d₀ =>
      intro b e hw
      exact XorReachable.cons j [] d₀ e e b hw (XorReachable.nil e)
  | cons j₀ l₀ d₀ d₁ e₀ b₀ hw₀ hrest ih =>
      intro b e hw
      rw [List.cons_append]
      exact XorReachable.cons j₀ (l₀ ++ [j]) d₀ d₁ e b₀ hw₀ (ih b hw)

/-- A reachable database has cardinality at most the initial cardinality plus the length of its
address list. -/
theorem xorReachable_card {l : List I} {d e : I → Bool} (h : XorReachable l d e) :
    databaseCard e ≤ databaseCard d + l.length := by
  induction h with
  | nil d => simp
  | cons j l d d' e b hw hrest ih =>
      have h1 : databaseCard d' ≤ databaseCard d + 1 := by
        rw [hw]; exact databaseCard_xorWriteAt_le_one j b d
      have h2 : (j :: l).length = l.length + 1 := rfl
      rw [h2]
      omega

omit [Fintype I] in

/-- Every true entry of a reachable database was initially true or appears in the address list. -/
theorem xorReachable_label {l : List I} {d e : I → Bool} (h : XorReachable l d e) :
    ∀ k : I, e k = true → d k = true ∨ k ∈ l := by
  induction h with
  | nil d => intro k hk; exact Or.inl hk
  | cons j l d d' e b hw hrest ih =>
      intro k hk
      rcases ih k hk with h' | h'
      · rw [hw] at h'
        by_cases hkj : k = j
        · exact Or.inr (List.mem_cons.mpr (Or.inl hkj))
        · rw [xorWriteAt, ite_eq_right hkj] at h'
          exact Or.inl h'
      · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- A database reachable from the empty database has cardinality at most the address-list
length. -/
theorem xorReachable_from_empty_card {l : List I} {e : I → Bool}
    (h : XorReachable l (fun _ => false) e) : databaseCard e ≤ l.length := by
  have hc := xorReachable_card h
  rw [show databaseCard (fun _ : I => false) = 0 by simp [databaseCard, databaseSupport]] at hc
  simpa using! hc

omit [Fintype I] in

/-- Every true entry of a database reachable from the empty database appears in its address
list. -/
theorem xorReachable_from_empty_label {l : List I} {e : I → Bool}
    (h : XorReachable l (fun _ => false) e) {k : I} (hk : e k = true) : k ∈ l :=
  ((xorReachable_label h k hk).resolve_left fun hc => absurd hc (by simp))

omit [Fintype I] in

/-- Every stored true value in a database reachable from empty appears in its address list. -/
theorem xorReachable_from_empty_shadow {l : List I} {e : I → Bool}
    (h : XorReachable l (fun _ => false) e) {k : I}
    (hk : booleanValuedDatabase e k = some true) : k ∈ l :=
  xorReachable_from_empty_label h (booleanValuedDatabase_eq_some_true_iff.mp hk)

/-- Every stored true value in a database reachable from empty is recorded by `queryRecord`. -/
theorem xorReachable_shadow_queryRecord {N : ℕ} {l : List (Fin N)} {e : Fin N → Bool}
    (h : XorReachable l (fun _ => false) e) {k : Fin N}
    (hk : booleanValuedDatabase e k = some true) : queryRecord l k = some true :=
  (queryRecord_eq_some_true_iff l k).mpr (xorReachable_from_empty_shadow h hk)

def XorSupportedOn (j : I) (w : W) (l : List I) (d : I → Bool)
    (u : QState (((I × Bool) × W) × (I → Bool))) : Prop :=
  ∀ q : (I × Bool) × W, ∀ e : I → Bool, u (q, e) ≠ 0 →
    q.1.1 = j ∧ q.2 = w ∧ XorReachable l d e

omit [Fintype W] in

/-- A basis ket satisfies `XorSupportedOn` for its own address, workspace, and database with an
empty query list. -/
theorem xorSupportedOn_ket (j : I) (b : Bool) (w : W) (d : I → Bool) :
    XorSupportedOn j w [] d (Ket (((j, b), w), d)) := by
  rintro ⟨⟨j₁, b₁⟩, w₁⟩ e hne
  by_cases hq : (((j₁, b₁), w₁), e) = (((j, b), w), d)
  · simp only [Prod.mk.injEq] at hq
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hq
    exact ⟨rfl, rfl, XorReachable.nil _⟩
  · exact absurd (by simp [Ket, hq]) hne

/-- Applying the database XOR oracle extends `XorSupportedOn` by appending the queried address. -/
theorem xorSupportedOn_apply_databaseXorOracle (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (j : I) (w : W) (l : List I) (d : I → Bool)
    (u : QState (((I × Bool) × W) × (I → Bool))) (h : XorSupportedOn j w l d u) :
    XorSupportedOn j w (l ++ [j]) d (ApplyGate (databaseXorOracle p) u) := by
  rintro ⟨⟨j', a⟩, w'⟩ e hne
  rw [applyGate_eq_sum] at hne
  obtain ⟨z, hz⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨⟨⟨j₀, b₀⟩, w₀⟩, d₀⟩ := z
  have hentry : databaseXorOracle p (((j', a), w'), e) (((j₀, b₀), w₀), d₀) ≠ 0 :=
    fun h0 => hz (by rw [h0, zero_mul])
  have hu : u (((j₀, b₀), w₀), d₀) ≠ 0 :=
    fun h0 => hz (by rw [h0, mul_zero])
  obtain ⟨hj₀, hw₀, hreach⟩ := h ((j₀, b₀), w₀) d₀ hu
  have hj₀' : j₀ = j := by simpa using! hj₀
  have hw₀' : w₀ = w := by simpa using! hw₀
  have hjw : j₀ = j' ∧ w₀ = w' := by
    by_contra hcon
    push Not at hcon
    have hoff : j' ≠ j₀ ∨ w' ≠ w₀ := by
      by_cases hjj : j' = j₀
      · exact Or.inr (fun heq => hcon hjj.symm heq.symm)
      · exact Or.inl hjj
    exact hentry (databaseXorOracle_offblock p j' j₀ a b₀ w' w₀ e d₀ hoff)
  have hj' : j' = j := (hjw.1).symm.trans hj₀'
  have hw' : w' = w := (hjw.2).symm.trans hw₀'
  refine ⟨hj', hw', ?_⟩
  have hentry' : databaseXorOracle p (((j₀, a), w₀), e) (((j₀, b₀), w₀), d₀) ≠ 0 := by
    rw [show j' = j₀ from (hjw.1).symm, show w' = w₀ from (hjw.2).symm] at hentry
    exact hentry
  have hloc := databaseXorOracle_locality p hp0 hp1 j₀ a b₀ w₀ e d₀ hentry'
  have hwr : e = xorWriteAt j₀ (e j₀) d₀ :=
    xorWriteAt_eq_of_locality j₀ d₀ e (fun k hk => (hloc k hk).symm)
  rw [hj₀'] at hwr
  exact xorReachable_snoc j hreach (e j) hwr

/-- Repeated database XOR queries extend the support history by the corresponding repeated
address list. -/
theorem xorSupportedOn_run_repeat (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (j : I) (w : W) (l : List I) (d : I → Bool)
    (u : QState (((I × Bool) × W) × (I → Bool))) :
    XorSupportedOn j w l d u →
    XorSupportedOn j w (l ++ List.replicate k j) d
      (Run (databaseXorOracle p) (RepeatCircuit [Step.query] k) u) := by
  induction k generalizing u l with
  | zero =>
      intro h
      rw [show l ++ List.replicate 0 j = l by simp]
      exact h
  | succ k ih =>
      intro h
      rw [RepeatCircuit, run_append, run_query, run_nil]
      have hrest := ih (l ++ [j]) (ApplyGate (databaseXorOracle p) u)
        (xorSupportedOn_apply_databaseXorOracle p hp0 hp1 j w l d u h)
      have hlist : (l ++ [j]) ++ List.replicate k j = l ++ List.replicate (k + 1) j := by
        rw [List.append_assoc l [j] (List.replicate k j), List.singleton_append,
          List.replicate_succ]
      rw [hlist] at hrest
      exact hrest

/-- Repeated queries from a basis ket satisfy `XorSupportedOn` with the repeated address list. -/
theorem xorSupportedOn_run_repeat_ket (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (j : I) (b : Bool) (w : W) (d : I → Bool) :
    XorSupportedOn j w (List.replicate k j) d
      (Run (databaseXorOracle p) (RepeatCircuit [Step.query] k)
        (Ket (((j, b), w), d))) := by
  have h := xorSupportedOn_run_repeat p hp0 hp1 k j w [] d (Ket (((j, b), w), d))
    (xorSupportedOn_ket j b w d)
  rwa [List.nil_append] at h

/-- Any database with nonzero amplitude after repeated queries from a basis ket is reachable
along the repeated address list. -/
theorem databaseXorOracle_run_query_reachable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : Run (databaseXorOracle p) (RepeatCircuit [Step.query] k)
        (Ket (((j, b), w), d)) (((j, a), w), e) ≠ 0) :
    XorReachable (List.replicate k j) d e :=
  (xorSupportedOn_run_repeat_ket p hp0 hp1 k j b w d ((j, a), w) e h).2.2

/-- Repeated database XOR queries preserve the address and workspace on every basis state with
nonzero amplitude. -/
theorem databaseXorOracle_run_query_offword (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (j j' : I) (b a : Bool) (w w' : W) (d e : I → Bool)
    (h : Run (databaseXorOracle p) (RepeatCircuit [Step.query] k)
        (Ket (((j, b), w), d)) (((j', a), w'), e) ≠ 0) :
    j' = j ∧ w' = w :=
  ⟨(xorSupportedOn_run_repeat_ket p hp0 hp1 k j b w d ((j', a), w') e h).1,
    (xorSupportedOn_run_repeat_ket p hp0 hp1 k j b w d ((j', a), w') e h).2.1⟩

/-- After repeated queries from a basis ket, every database with nonzero amplitude has
cardinality at most its initial cardinality plus the query count. -/
theorem databaseXorOracle_run_query_card (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : Run (databaseXorOracle p) (RepeatCircuit [Step.query] k)
        (Ket (((j, b), w), d)) (((j, a), w), e) ≠ 0) :
    databaseCard e ≤ databaseCard d + k := by
  have hc := xorReachable_card (databaseXorOracle_run_query_reachable p hp0 hp1 k j b a w d e h)
  rwa [List.length_replicate] at hc

/-- From an empty basis database, repeated queries produce only databases of bounded cardinality
whose stored entries occur in the repeated address list. -/
theorem databaseXorOracle_run_query_from_empty (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (k : ℕ) (j : I) (b a : Bool) (w : W) (e : I → Bool)
    (h : Run (databaseXorOracle p) (RepeatCircuit [Step.query] k)
        (Ket (((j, b), w), fun _ => false)) (((j, a), w), e) ≠ 0) :
    databaseCard e ≤ k ∧ ∀ k' : I, booleanValuedDatabase e k' = some true →
      k' ∈ List.replicate k j :=
  ⟨(databaseXorOracle_run_query_card p hp0 hp1 k j b a w (fun _ => false) e h).trans_eq
      (by simp [databaseCard, databaseSupport]),
    fun k' hk => xorReachable_from_empty_shadow
      (databaseXorOracle_run_query_reachable p hp0 hp1 k j b a w (fun _ => false) e h) hk⟩

/-- Every stored true value after repeated queries from an empty basis database is present in
the corresponding query record. -/
theorem databaseXorOracle_run_query_from_empty_queryRecord {N : ℕ} (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (k : ℕ) (j : Fin N) (b a : Bool) (w : W) (e : Fin N → Bool)
    (h : Run (databaseXorOracle p) (RepeatCircuit [Step.query] k)
        (Ket (((j, b), w), fun _ => false)) (((j, a), w), e) ≠ 0)
    (x : Fin N) (hx : booleanValuedDatabase e x = some true) :
    queryRecord (List.replicate k j) x = some true :=
  xorReachable_shadow_queryRecord
    (databaseXorOracle_run_query_reachable p hp0 hp1 k j b a w (fun _ => false) e h) hx

def permGate (f : I ≃ I) : Matrix I I ℂ :=
  Matrix.of fun x y => if x = f y then 1 else 0

def xorAddressGate (f : I ≃ I) :
    Matrix (((I × Bool) × W) × (I → Bool)) (((I × Bool) × W) × (I → Bool)) ℂ :=
  TensorGate (TensorGate (TensorGate (permGate f) (1 : Matrix Bool Bool ℂ))
    (1 : Matrix W W ℂ)) (1 : Matrix (I → Bool) (I → Bool) ℂ)

omit [Fintype W] in

/-- The address gate has entry one exactly when it applies the address permutation and preserves
the target, workspace, and database, and zero otherwise. -/
theorem xorAddressGate_apply (f : I ≃ I) (j j' : I) (b b' : Bool) (w w' : W)
    (e e' : I → Bool) :
    xorAddressGate (I := I) (W := W) f (((j, b), w), e) (((j', b'), w'), e')
      = if j = f j' ∧ b = b' ∧ w = w' ∧ e = e' then 1 else 0 := by
  simp only [xorAddressGate, tensorGate_apply, permGate, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h1 : j = f j' <;> by_cases h2 : b = b' <;> by_cases h3 : w = w' <;>
    by_cases h4 : e = e' <;> simp [h1, h2, h3, h4]

/-- The matrix of an address permutation is unitary. -/
theorem permGate_unitary (f : I ≃ I) :
    permGate (I := I) f ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext x y
  have hsum : (permGate (I := I) f * (permGate f)ᴴ) x y
      = ∑ k : I, (if x = f k then (1:ℂ) else 0) * (if y = f k then (1:ℂ) else 0) := by
    simp [permGate, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsum, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    rw [Finset.sum_eq_single (f.symm x)]
    · simp [Equiv.apply_symm_apply]
    · intro k _ hk
      have hfk : ¬ x = f k := fun h => hk ((Equiv.eq_symm_apply (e := f)).mpr h.symm)
      simp [hfk]
    · simp
  · rw [ite_eq_right hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases eq_or_ne x (f k) with hx | hx
    · have hne : ¬ y = f k := fun hc => hxy (hx.trans hc.symm)
      rw [ite_eq_left hx, ite_eq_right hne, mul_zero]
    · rw [ite_eq_right hx, zero_mul]

/-- The XOR address gate induced by an address permutation is unitary. -/
theorem xorAddressGate_unitary (f : I ≃ I) :
    xorAddressGate (I := I) (W := W) f ∈
      Matrix.unitaryGroup (((I × Bool) × W) × (I → Bool)) ℂ := by
  rw [xorAddressGate]
  exact tensorGate_unitary (tensorGate_unitary (tensorGate_unitary
    (permGate_unitary (I := I) f) (Submonoid.one_mem _)) (Submonoid.one_mem _))
    (Submonoid.one_mem _)

/-- Applying an address gate transports `XorSupportedOn` to the permuted address while
preserving its history and initial database. -/
theorem xorSupportedOn_apply_addressGate (f : I ≃ I) (j : I) (w : W) (l : List I)
    (d : I → Bool) (u : QState (((I × Bool) × W) × (I → Bool)))
    (h : XorSupportedOn j w l d u) :
    XorSupportedOn (f j) w l d (ApplyGate (xorAddressGate f) u) := by
  rintro ⟨⟨j', a⟩, w'⟩ e hne
  rw [applyGate_eq_sum] at hne
  obtain ⟨z, hz⟩ := exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨⟨⟨j₀, b₀⟩, w₀⟩, d₀⟩ := z
  have hentry : xorAddressGate f (((j', a), w'), e) (((j₀, b₀), w₀), d₀) ≠ 0 :=
    fun h0 => hz (by rw [h0, zero_mul])
  have hu : u (((j₀, b₀), w₀), d₀) ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
  obtain ⟨hj₀, hw₀, hreach⟩ := h ((j₀, b₀), w₀) d₀ hu
  rw [xorAddressGate_apply f j' j₀ a b₀ w' w₀ e d₀] at hentry
  have hc : j' = f j₀ ∧ a = b₀ ∧ w' = w₀ ∧ e = d₀ := by
    by_cases hc' : j' = f j₀ ∧ a = b₀ ∧ w' = w₀ ∧ e = d₀
    · exact hc'
    · rw [ite_eq_right hc'] at hentry
      exact absurd hentry (by simp)
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  refine ⟨hc1.trans (congrArg f (by simpa using! hj₀)), hc3.trans (by simpa using! hw₀), ?_⟩
  rw [hc4]
  exact hreach

def xorScheduleWord : List (I ≃ I) → Circuit (((I × Bool) × W) × (I → Bool))
  | [] => []
  | f :: fs => Step.gate (xorAddressGate f) :: Step.query :: xorScheduleWord fs

def xorScheduleAddresses (j : I) : List (I ≃ I) → List I
  | [] => []
  | f :: fs => f j :: xorScheduleAddresses (f j) fs

def xorScheduleFinal (j : I) (fs : List (I ≃ I)) : I := fs.foldl (fun j' f => f j') j

omit [Fintype W] in

/-- The query count of an XOR schedule word equals the number of address permutations in the
schedule. -/
theorem xorScheduleWord_queryCount (fs : List (I ≃ I)) :
    QueryCount (xorScheduleWord (I := I) (W := W) fs) = fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [xorScheduleWord, ih]

/-- Every XOR schedule word is a unitary circuit. -/
theorem xorScheduleWord_isUnitaryCircuit (fs : List (I ≃ I)) :
    IsUnitaryCircuit (xorScheduleWord (I := I) (W := W) fs) := by
  induction fs with
  | nil => exact isUnitaryCircuit_nil
  | cons f fs ih =>
      simp only [xorScheduleWord, isUnitaryCircuit_gate]
      refine ⟨xorAddressGate_unitary f, ?_⟩
      simp only [isUnitaryCircuit_query]
      exact ih

omit [Fintype W] in

/-- Every XOR schedule word satisfies `IsAlgorithmCircuit`. -/
theorem isAlgorithmCircuit_xorScheduleWord (fs : List (I ≃ I)) :
    IsAlgorithmCircuit (xorScheduleWord (I := I) (W := W) fs) := by
  induction fs with
  | nil => intro U hU; simp [xorScheduleWord] at hU
  | cons f fs ih =>
      intro U hU
      simp only [xorScheduleWord, List.mem_cons] at hU
      rcases hU with hU | hU
      · injection hU with hU
        refine ⟨TensorGate (TensorGate (permGate f) (1 : Matrix Bool Bool ℂ))
          (1 : Matrix W W ℂ), ?_⟩
        rw [hU]
        rfl
      · rcases hU with hU' | hU'
        · injection hU'
        · exact ih U hU'

/-- Decoding transports a scheduled database XOR run to the same schedule with purified XOR
queries. -/
theorem xorDecode_run_transport_schedule (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (v : QState (((I × Bool) × W) × (I → Bool))) :
    ApplyGate (xorDecode p) (Run (databaseXorOracle p) (xorScheduleWord fs) v)
      = Run xorPurifiedQuery (xorScheduleWord fs) (ApplyGate (xorDecode p) v) := by
  rw [xorDecode_run_transport p hp0 hp1 (xorScheduleWord fs) v,
    xorPhysicalCircuit_eq_of_isAlgorithmCircuit p hp0 hp1 (xorScheduleWord fs)
      (isAlgorithmCircuit_xorScheduleWord fs)]

/-- Running an XOR schedule updates the supported address to its final address and appends its
queried addresses to the support history. -/
theorem xorSupportedOn_run_schedule (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) :
    ∀ (j : I) (w : W) (l : List I) (d : I → Bool)
      (u : QState (((I × Bool) × W) × (I → Bool))),
      XorSupportedOn j w l d u →
      XorSupportedOn (xorScheduleFinal j fs) w (l ++ xorScheduleAddresses j fs) d
        (Run (databaseXorOracle p) (xorScheduleWord fs) u) := by
  induction fs with
  | nil =>
      intro j w l d u h
      simp only [xorScheduleWord, xorScheduleFinal, xorScheduleAddresses,
        List.foldl_nil, List.append_nil, run_nil]
      exact h
  | cons f fs ih =>
      intro j w l d u h
      simp only [xorScheduleWord, run_gate, run_query]
      have hmove : XorSupportedOn (f j) w l d (ApplyGate (xorAddressGate f) u) :=
        xorSupportedOn_apply_addressGate f j w l d u h
      have hquery : XorSupportedOn (f j) w (l ++ [f j]) d
          (ApplyGate (databaseXorOracle p) (ApplyGate (xorAddressGate f) u)) :=
        xorSupportedOn_apply_databaseXorOracle p hp0 hp1 (f j) w l d _ hmove
      have hrest := ih (f j) w (l ++ [f j]) d _ hquery
      rw [xorScheduleFinal] at hrest
      rw [List.append_assoc l [f j]] at hrest
      rw [List.singleton_append] at hrest
      rw [xorScheduleFinal, xorScheduleAddresses, List.foldl_cons]
      exact hrest

/-- An XOR schedule run from a basis ket satisfies `XorSupportedOn` with its final address and
scheduled query history. -/
theorem xorSupportedOn_run_schedule_ket (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (j : I) (b : Bool) (w : W) (d : I → Bool) :
    XorSupportedOn (xorScheduleFinal j fs) w (xorScheduleAddresses j fs) d
      (Run (databaseXorOracle p) (xorScheduleWord fs)
        (Ket (((j, b), w), d))) := by
  have h := xorSupportedOn_run_schedule p hp0 hp1 fs j w [] d (Ket (((j, b), w), d))
    (xorSupportedOn_ket j b w d)
  rwa [List.nil_append] at h

/-- Any database with nonzero amplitude after a scheduled run from a basis ket is reachable
along the scheduled addresses. -/
theorem databaseXorOracle_run_schedule_reachable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : Run (databaseXorOracle p) (xorScheduleWord fs)
        (Ket (((j, b), w), d)) (((xorScheduleFinal j fs, a), w), e) ≠ 0) :
    XorReachable (xorScheduleAddresses j fs) d e :=
  (xorSupportedOn_run_schedule_ket p hp0 hp1 fs j b w d
    ((xorScheduleFinal j fs, a), w) e h).2.2

/-- A scheduled run preserves the workspace and gives the prescribed final address on every
basis state with nonzero amplitude. -/
theorem databaseXorOracle_run_schedule_offword (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (j j' : I) (b a : Bool) (w w' : W) (d e : I → Bool)
    (h : Run (databaseXorOracle p) (xorScheduleWord fs)
        (Ket (((j, b), w), d)) (((j', a), w'), e) ≠ 0) :
    j' = xorScheduleFinal j fs ∧ w' = w :=
  ⟨(xorSupportedOn_run_schedule_ket p hp0 hp1 fs j b w d ((j', a), w') e h).1,
    (xorSupportedOn_run_schedule_ket p hp0 hp1 fs j b w d ((j', a), w') e h).2.1⟩

/-- After a scheduled run, every database with nonzero amplitude has cardinality at most its
initial cardinality plus the schedule's address-list length. -/
theorem databaseXorOracle_run_schedule_card (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (j : I) (b a : Bool) (w : W) (d e : I → Bool)
    (h : Run (databaseXorOracle p) (xorScheduleWord fs)
        (Ket (((j, b), w), d)) (((xorScheduleFinal j fs, a), w), e) ≠ 0) :
    databaseCard e ≤ databaseCard d + (xorScheduleAddresses j fs).length :=
  xorReachable_card (databaseXorOracle_run_schedule_reachable p hp0 hp1 fs j b a w d e h)

/-- From an empty basis database, a scheduled run produces only databases of bounded cardinality
whose stored entries occur in the schedule's address list. -/
theorem databaseXorOracle_run_schedule_from_empty (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fs : List (I ≃ I)) (j : I) (b a : Bool) (w : W) (e : I → Bool)
    (h : Run (databaseXorOracle p) (xorScheduleWord fs)
        (Ket (((j, b), w), fun _ => false))
        (((xorScheduleFinal j fs, a), w), e) ≠ 0) :
    databaseCard e ≤ (xorScheduleAddresses j fs).length ∧
      ∀ k : I, booleanValuedDatabase e k = some true →
        k ∈ xorScheduleAddresses j fs :=
  ⟨(databaseXorOracle_run_schedule_card p hp0 hp1 fs j b a w (fun _ => false) e h).trans_eq
      (by simp [databaseCard, databaseSupport]),
    fun k hk => xorReachable_from_empty_shadow
      (databaseXorOracle_run_schedule_reachable p hp0 hp1 fs j b a w (fun _ => false) e h) hk⟩

/-- Every stored true value after a scheduled run from an empty basis database appears in the
schedule's query record. -/
theorem databaseXorOracle_run_schedule_from_empty_queryRecord {N : ℕ} (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (fs : List (Fin N ≃ Fin N)) (j : Fin N) (b a : Bool) (w : W)
    (e : Fin N → Bool)
    (h : Run (databaseXorOracle p) (xorScheduleWord fs)
        (Ket (((j, b), w), fun _ => false))
        (((xorScheduleFinal j fs, a), w), e) ≠ 0) (x : Fin N)
    (hx : booleanValuedDatabase e x = some true) :
    queryRecord (xorScheduleAddresses j fs) x = some true :=
  xorReachable_shadow_queryRecord
    (databaseXorOracle_run_schedule_reachable p hp0 hp1 fs j b a w (fun _ => false) e h) hx

/-- Collects the decoding intertwining identity, mutual encoding-decoding inverse identities,
and involutivity of the database and purified XOR oracles. -/
theorem frontier1 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    xorDecode (I := I) (W := W) p * databaseXorOracle p
      = xorPurifiedQuery * xorDecode p ∧
    xorDecode (I := I) (W := W) p * xorEncode p = 1 ∧
    xorEncode (I := I) (W := W) p * xorDecode p = 1 ∧
    databaseXorOracle (I := I) (W := W) p * databaseXorOracle p = 1 ∧
    xorPurifiedQuery (I := I) (W := W) * xorPurifiedQuery = 1 :=
  ⟨xorDecode_mul_databaseXorOracle p hp0 hp1, xorDecode_mul_xorEncode p hp0 hp1,
    xorEncode_mul_xorDecode p hp0 hp1, databaseXorOracle_mul_self p hp0 hp1,
    xorPurifiedQuery_mul_self⟩

end Qatlib.Papers.QMAvsQCMA25.Forrelation.XorCompressedDatabaseIntertwining
