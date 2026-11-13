/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionConstructionRefl
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.QueryComplexity.Amplification.ParallelCopies
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
import Qatlib.Concepts.QueryComplexity.Reflections.ReflectionsPhaseBridge

/-!
# Counted bit-query programs for reflection algorithms

`reflectionsFrame` embeds logical states into an explicit query register, and
compute-phase-uncompute implements controlled source reflections. The module constructs clocked
reflection trials and routes independent copies through a shared bit oracle, with exact query
and gate counts.

`reflections_amplified_actual` combines 100 trials with a threshold event to obtain success
probability at least 2/3 from the stated probability gap, in the reflection framework of
[Reichardt2011].

## Main statements

* `reflections_two_query_source_program`: implements a controlled two-reflection unitary using
  two queries and two gates.
* `standardCopiesCircuit_spec`: runs a circuit on each tensor factor with explicit routing
  overhead.
* `reflections_amplified_actual`: constructs the counted amplified decision circuit.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.Reflections
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped BigOperators

variable {A H : Type} [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H]
  {n : ℕ}

/-- Embeds a logical state with query address `addr` and a false query bit, assigning zero
amplitude off this frame. -/
def reflectionsFrame (addr : H → Fin n) (ψ : QState (A × H)) :
    QState ((Fin n × Bool) × (A × H)) :=
  fun p => if p.1 = (addr p.2.2, false) then ψ p.2 else 0

/-- The matrix embedding each logical basis vector into its addressed query frame with a false
query bit. -/
def reflectionsFrameMatrix (addr : H → Fin n) :
    Matrix ((Fin n × Bool) × (A × H)) (A × H) ℂ :=
  fun p q => if p = ((addr q.2, false), q) then 1 else 0

/-- Matrix multiplication by `reflectionsFrameMatrix` agrees with `reflectionsFrame`. -/
theorem reflectionsFrameMatrix_apply (addr : H → Fin n) (ψ : QState (A × H)) :
    reflectionsFrameMatrix (A := A) addr *ᵥ ψ = reflectionsFrame addr ψ := by
  funext p
  simp only [Matrix.mulVec, dotProduct, reflectionsFrameMatrix, reflectionsFrame]
  rw [Finset.sum_eq_single p.2]
  · by_cases hp : p.1 = (addr p.2.2, false)
    · have he : p = ((addr p.2.2, false), p.2) := Prod.ext hp rfl
      rw [ite_eq_left he, ite_eq_left hp, one_mul]
    · have he : p ≠ ((addr p.2.2, false), p.2) := fun he => hp (congrArg Prod.fst he)
      simp only [he, hp, ite_false, zero_mul]
  · intro q _ hq
    have he : p ≠ ((addr q.2, false), q) := fun he => hq (congrArg Prod.snd he).symm
    simp only [he, ite_false, zero_mul]
  · simp

/-- The query-frame embedding matrix is an isometry. -/
theorem reflectionsFrameMatrix_isometry (addr : H → Fin n) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (reflectionsFrameMatrix (A := A) addr) := by
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, reflectionsFrameMatrix]
  rw [Finset.sum_eq_single ((addr p.2, false), p)]
  · simp only [ite_true, star_one, one_mul]
    by_cases hpq : p = q
    · subst q
      simp
    · have he : ((addr p.2, false), p) ≠ ((addr q.2, false), q) :=
        fun he => hpq (congrArg Prod.snd he)
      simp only [he, ite_false, Matrix.one_apply_ne hpq]
  · intro r _ hr
    simp only [hr, ite_false, star_zero, zero_mul]
  · simp

/-- Every unitary logical gate extends to a unitary on the query-frame space that intertwines
the frame embedding. -/
theorem reflectionsFrame_transport (addr : H → Fin n) (L : Matrix (A × H) (A × H) ℂ)
    (hL : L ∈ Matrix.unitaryGroup (A × H) ℂ) :
    ∃ K : Matrix ((Fin n × Bool) × (A × H)) ((Fin n × Bool) × (A × H)) ℂ,
      K ∈ Matrix.unitaryGroup _ ℂ ∧
      ∀ ψ, ApplyGate K (reflectionsFrame addr ψ) = reflectionsFrame addr (ApplyGate L ψ) := by
  let F := reflectionsFrameMatrix (A := A) addr
  have hF : Fᴴ * F = 1 := reflectionsFrameMatrix_isometry addr
  have hLL : Lᴴ * L = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hL.1
  have hG : Fᴴ * F = (F * L)ᴴ * (F * L) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F L,
      hF, Matrix.one_mul, hLL]
  obtain ⟨K, hK, hKF⟩ := gram_equal_actual_unitary_transport _ _ F (F * L) hG
  refine ⟨K, hK, ?_⟩
  intro ψ
  change K *ᵥ reflectionsFrame addr ψ = reflectionsFrame addr (L *ᵥ ψ)
  calc
    _ = K *ᵥ (F *ᵥ ψ) := congrArg (fun φ => K *ᵥ φ) (reflectionsFrameMatrix_apply addr ψ).symm
    _ = (K * F) *ᵥ ψ := Matrix.mulVec_mulVec _ _ _
    _ = (F * L) *ᵥ ψ := congrArg (fun M => M *ᵥ ψ) hKF
    _ = F *ᵥ (L *ᵥ ψ) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = _ := reflectionsFrameMatrix_apply addr (L *ᵥ ψ)

/-- Applies `U` on the `H` register for active control values and the identity for inactive
values. -/
def reflectionsControlled (active : A → Bool) (U : Matrix H H ℂ) :
    Matrix (A × H) (A × H) ℂ := Select (fun a => if active a then U else 1)

/-- A controlled selection of a unitary and the identity is unitary. -/
theorem reflectionsControlled_unitary (active : A → Bool) (U : Matrix H H ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    reflectionsControlled active U ∈ Matrix.unitaryGroup (A × H) ℂ := by
  apply Qatlib.Concepts.BlockEncoding.LinearCombination.select_unitary
  intro a
  cases active a <;> simp [hU]

/-- Evaluates the controlled gate on each control fibre, applying `U` precisely on active
fibres. -/
theorem reflectionsControlled_apply (active : A → Bool) (U : Matrix H H ℂ)
    (ψ : QState (A × H)) (a : A) (h : H) :
    ApplyGate (reflectionsControlled active U) ψ (a, h) =
      if active a then ApplyGate U (fun z => ψ (a, z)) h else ψ (a, h) := by
  simp only [ApplyGate, reflectionsControlled, Select, Matrix.of_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · by_cases ha : active a = true
    · simp only [ha, ite_true]
    · simp only [ite_eq_right ha]
      exact congrFun (Matrix.one_mulVec (fun z => ψ (a, z))) h
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The diagonal sign gate controlled by activity and the exclusive-or of the query bit with the
optional column bit. -/
def reflectionsColumnPhase (bit : H → Option Bool) (active : A → Bool) :
    Matrix ((Fin n × Bool) × (A × H)) ((Fin n × Bool) × (A × H)) ℂ :=
  Matrix.diagonal fun p => match bit p.2.2 with
    | none => 1
    | some b => if active p.2.1 && (p.1.2 ^^ b) then -1 else 1

/-- The column-phase sign gate is unitary. -/
theorem reflectionsColumnPhase_unitary (bit : H → Option Bool) (active : A → Bool) :
    reflectionsColumnPhase (n := n) bit active ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    reflectionsColumnPhase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext p
  simp only [Pi.star_apply]
  cases hb : bit p.2.2 with
  | none => simp
  | some b => simp only []; split_ifs <;> norm_num

/-- The logical diagonal sign gate obtained from the oracle value at `addr`, the optional column
bit, and the activity control. -/
def reflectionsLogicalPhase (addr : H → Fin n) (bit : H → Option Bool)
    (active : A → Bool) (o : Fin n → Bool) : Matrix (A × H) (A × H) ℂ :=
  Matrix.diagonal fun p => match bit p.2 with
    | none => 1
    | some b => if active p.1 && (o (addr p.2) ^^ b) then -1 else 1

/-- Two bit-oracle calls surrounding the column-phase gate implement the logical phase gate on
framed states. -/
theorem reflections_compute_phase_uncompute (addr : H → Fin n) (bit : H → Option Bool)
    (active : A → Bool) (o : Fin n → Bool) (ψ : QState (A × H)) :
    Run (workspaceBitOracle (W := A × H) o)
      [Step.query, Step.gate (reflectionsColumnPhase bit active), Step.query]
      (reflectionsFrame addr ψ) =
      reflectionsFrame addr (ApplyGate (reflectionsLogicalPhase addr bit active o) ψ) := by
  funext p
  rcases p with ⟨⟨i, t⟩, a, z⟩
  simp only [Run]
  rw [applyGate_workspaceBitOracle]
  change (reflectionsColumnPhase bit active *ᵥ
    (ApplyGate (workspaceBitOracle o) (reflectionsFrame addr ψ)))
      ((i, t ^^ o i), (a, z)) = _
  rw [reflectionsColumnPhase, Matrix.mulVec_diagonal, applyGate_workspaceBitOracle]
  simp only [reflectionsLogicalPhase, ApplyGate, Matrix.mulVec_diagonal, reflectionsFrame]
  by_cases hi : i = addr z
  · subst i
    cases t <;> cases bit z <;> simp
  · have hpair : (i, t) ≠ (addr z, false) := fun h => hi (congrArg Prod.fst h)
    have hpair2 : (i, t ^^ o i ^^ o i) ≠ (addr z, false) :=
      fun h => hi (congrArg Prod.fst h)
    have hpair : (i, t) ≠ (addr z, false) := fun h => hi (congrArg Prod.fst h)
    simp only [hpair, hpair2, ite_false, mul_zero]

variable {X : Type} [Fintype X] [DecidableEq X] {m : ℕ}

/-- Extracts a query vertex address, using address zero on the other vertex summands. -/
def reflectionsVertexAddress (f : X → Bool) (hn : 0 < n) : Vertex X f n m → Fin n
  | .inr (.inr (j, _, _)) => j
  | _ => ⟨0, hn⟩

/-- Extracts the Boolean label of a query vertex and returns `none` on the other vertex
summands. -/
def reflectionsVertexBit (f : X → Bool) : Vertex X f n m → Option Bool
  | .inr (.inr (_, b, _)) => some b
  | _ => none

omit [Fintype A] [Fintype X] in

/-- The logical vertex phase equals the controlled reflection `2 • pixProj - 1`. -/
theorem reflections_source_phase (f : X → Bool) (hn : 0 < n)
    (input : X → Fin n → Bool) (active : A → Bool) (x : X) :
    reflectionsLogicalPhase (reflectionsVertexAddress f hn) (reflectionsVertexBit f)
      active (input x) =
      reflectionsControlled active ((2 : ℂ) • pixProj (m := m) input f x - 1) := by
  ext ⟨a, z⟩ ⟨b, w⟩
  by_cases hab : a = b
  · subst b
    by_cases hzw : z = w
    · subst w
      rcases z with r | z
      · cases ha : active a <;>
          norm_num [reflectionsLogicalPhase, reflectionsVertexAddress, reflectionsVertexBit,
            reflectionsControlled, Select, pixProj, ha]
      · rcases z with u | ⟨j, b, k⟩
        · cases ha : active a <;>
            norm_num [reflectionsLogicalPhase, reflectionsVertexAddress, reflectionsVertexBit,
              reflectionsControlled, Select, pixProj, complementMark, ha]
        · cases ha : active a <;> cases hx : input x j <;> cases b <;>
            norm_num [reflectionsLogicalPhase, reflectionsVertexAddress, reflectionsVertexBit,
              reflectionsControlled, Select, pixProj, complementMark, ha, hx]
    · cases ha : active a <;>
        simp [reflectionsLogicalPhase, reflectionsControlled, Select, pixProj, hzw, ha]
  · simp [reflectionsLogicalPhase, reflectionsControlled, Select, hab]

/-- Successive controlled applications of `V` and `U` equal a controlled application of `U * V`
with the same activity predicate. -/
theorem reflectionsControlled_product_apply (active : A → Bool) (U V : Matrix H H ℂ)
    (ψ : QState (A × H)) :
    ApplyGate (reflectionsControlled active U) (ApplyGate (reflectionsControlled active V) ψ) =
      ApplyGate (reflectionsControlled active (U * V)) ψ := by
  funext ⟨a, z⟩
  simp only [reflectionsControlled_apply]
  by_cases ha : active a = true
  · simp only [ha, ite_true]
    exact congrFun (Matrix.mulVec_mulVec (fun w => ψ (a, w)) U V) z
  · simp only [ite_eq_right ha]

/-- A singleton circuit containing a unitary gate is a unitary circuit. -/
theorem reflections_single_gate_wellFormed (U : Matrix H H ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) : IsUnitaryCircuit [Step.gate U] := by
  intro V hV
  simp only [List.mem_singleton, Step.gate.injEq] at hV
  subst V
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  have he := congrFun (congrFun hU.1 i) j
  by_cases hij : i = j
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, ite_eq_left hij] using he
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply, ite_eq_right hij] using he

/-- Constructs a circuit implementing the controlled source two-reflection unitary on framed
states using exactly two queries and two gates. -/
theorem reflections_two_query_source_program (A X : Type)
    [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]
    (n m : ℕ) (f : X → Bool) (hn : 0 < n)
    (input : X → Fin n → Bool)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) (hΔ : IsOrthogonalProjector Δ)
    (active : A → Bool) :
    ∃ C : Circuit ((Fin n × Bool) × (A × Vertex X f n m)),
      IsUnitaryCircuit C ∧ QueryCount C = 2 ∧ GateCount C = 2 ∧
      ∀ (x : X) (ψ : QState (A × Vertex X f n m)),
        Run (workspaceBitOracle (W := A × Vertex X f n m) (input x)) C
          (reflectionsFrame (reflectionsVertexAddress f hn) ψ) =
          reflectionsFrame (reflectionsVertexAddress f hn)
            (ApplyGate (reflectionsControlled active (twoReflectionUnitary input f x Δ)) ψ) := by
  obtain ⟨K, hK, hrun⟩ := reflectionsFrame_transport (reflectionsVertexAddress f hn)
    (reflectionsControlled active (ReflectionAbout Δ))
    (reflectionsControlled_unitary active _ (reflectionAbout_unitary hΔ))
  let C := [Step.gate K, Step.query,
    Step.gate (reflectionsColumnPhase (reflectionsVertexBit f) active), Step.query]
  refine ⟨C, ?_, by simp [C], by simp [C], ?_⟩
  · have hKC := reflections_single_gate_wellFormed K hK
    have hDC := reflections_single_gate_wellFormed
      (reflectionsColumnPhase (n := n) (reflectionsVertexBit (n := n) (m := m) f) active)
      (reflectionsColumnPhase_unitary (n := n) (reflectionsVertexBit (n := n) (m := m) f) active)
    simpa only [C, isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil,
      and_true] using (show _ ∧ _ from ⟨(isUnitaryCircuit_gate _ []).mp hKC |>.1,
        (isUnitaryCircuit_gate _ []).mp hDC |>.1⟩)
  · intro x ψ
    change Run (workspaceBitOracle (input x))
      [Step.query, Step.gate (reflectionsColumnPhase (reflectionsVertexBit f) active), Step.query]
      (ApplyGate K (reflectionsFrame (reflectionsVertexAddress f hn) ψ)) = _
    rw [hrun]
    rw [reflections_compute_phase_uncompute (reflectionsVertexAddress f hn)
      (reflectionsVertexBit f) active (input x)
      (ApplyGate (reflectionsControlled active (ReflectionAbout Δ)) ψ)]
    rw [reflections_source_phase, reflectionsControlled_product_apply]
    rfl

/-- The ordered product of controlled copies of `U` with the successive activity predicates,
starting from the identity. -/
def reflectionsLoop (active : ℕ → A → Bool) (U : Matrix H H ℂ) :
    ℕ → Matrix (A × H) (A × H) ℂ
  | 0 => 1
  | k + 1 => reflectionsControlled (active k) U * reflectionsLoop active U k

/-- Implements `T` controlled source-walk steps on framed states using exactly `2 * T` queries
and `2 * T` gates. -/
theorem reflections_counted_source_loop (A X : Type)
    [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]
    (n m : ℕ) (f : X → Bool) (hn : 0 < n) (input : X → Fin n → Bool)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) (hΔ : IsOrthogonalProjector Δ)
    (active : ℕ → A → Bool) (T : ℕ) :
    ∃ C : Circuit ((Fin n × Bool) × (A × Vertex X f n m)),
      IsUnitaryCircuit C ∧ QueryCount C = 2 * T ∧ GateCount C = 2 * T ∧
      ∀ (x : X) (ψ : QState (A × Vertex X f n m)),
        Run (workspaceBitOracle (W := A × Vertex X f n m) (input x)) C
          (reflectionsFrame (reflectionsVertexAddress f hn) ψ) =
          reflectionsFrame (reflectionsVertexAddress f hn)
            (reflectionsLoop active (twoReflectionUnitary input f x Δ) T *ᵥ ψ) := by
  induction T with
  | zero => refine ⟨[], by simp, by simp, by simp, ?_⟩; intro x ψ; simp [reflectionsLoop, Run]
  | succ T ih =>
    obtain ⟨C, hC, hCQ, hCG, hCr⟩ := ih
    obtain ⟨D, hD, hDQ, hDG, hDr⟩ :=
      reflections_two_query_source_program A X n m f hn input Δ hΔ (active T)
    refine ⟨C ++ D, (isUnitaryCircuit_append _ _).mpr ⟨hC, hD⟩, ?_, ?_, ?_⟩
    · rw [queryCount_append, hCQ, hDQ]; omega
    · rw [gateCount_append, hCG, hDG]; omega
    · intro x ψ
      rw [run_append, hCr, hDr]
      change reflectionsFrame (reflectionsVertexAddress f hn)
        (reflectionsControlled (active T) (twoReflectionUnitary input f x Δ) *ᵥ
          (reflectionsLoop active (twoReflectionUnitary input f x Δ) T *ᵥ ψ)) = _
      rw [Matrix.mulVec_mulVec]
      rfl

/-- Activates a clock-control pair when its Boolean flag is true and the step index does not
exceed the clock value. -/
def reflectionsClockActive (τ : ℕ) (k : ℕ) (a : Fin τ × Bool) : Bool :=
  a.2 && decide (k ≤ a.1.val)

/-- After `k` clocked steps, a true control fibre receives `U` to the power `min k (t.val + 1)`,
while a false fibre is unchanged. -/
theorem reflections_clock_loop_fibre (τ k : ℕ) (U : Matrix H H ℂ)
    (ψ : QState ((Fin τ × Bool) × H)) (t : Fin τ) (b : Bool) (z : H) :
    (reflectionsLoop (reflectionsClockActive τ) U k *ᵥ ψ) ((t, b), z) =
      if b then (U ^ min k (t.val + 1) *ᵥ (fun w => ψ ((t, b), w))) z
      else ψ ((t, b), z) := by
  induction k generalizing ψ t b z with
  | zero => cases b <;> simp [reflectionsLoop]
  | succ k ih =>
    rw [reflectionsLoop, ← Matrix.mulVec_mulVec]
    change ApplyGate (reflectionsControlled (reflectionsClockActive τ k) U)
      (reflectionsLoop (reflectionsClockActive τ) U k *ᵥ ψ) ((t, b), z) = _
    rw [reflectionsControlled_apply]
    cases b with
    | false => simpa only [reflectionsClockActive, Bool.false_and, Bool.false_eq_true,
        ite_false] using ih ψ t false z
    | true =>
      have hf : (fun w => (reflectionsLoop (reflectionsClockActive τ) U k *ᵥ ψ)
          ((t, true), w)) = U ^ min k (t.val + 1) *ᵥ (fun w => ψ ((t, true), w)) := by
        funext w
        exact ih ψ t true w
      by_cases hk : k ≤ t.val
      · simp only [reflectionsClockActive, Bool.true_and, decide_eq_true_eq, hk,
          ite_true, hf]
        rw [min_eq_left (by omega : k ≤ t.val + 1),
          min_eq_left (by omega : k + 1 ≤ t.val + 1), pow_succ', ← Matrix.mulVec_mulVec]
        rfl
      · simp only [reflectionsClockActive, Bool.true_and, decide_eq_true_eq, hk,
          ite_false, ite_true]
        rw [ih ψ t true z, min_eq_right (by omega : t.val + 1 ≤ k),
          min_eq_right (by omega : t.val + 1 ≤ k + 1)]
        simp only [ite_true]

/-- A complete clocked loop applies `U ^ (t.val + 1)` on each true clock fibre and leaves false
fibres unchanged. -/
theorem reflections_clock_loop_complete (τ : ℕ) (U : Matrix H H ℂ)
    (ψ : QState ((Fin τ × Bool) × H)) :
    reflectionsLoop (reflectionsClockActive τ) U τ *ᵥ ψ =
      fun p => if p.1.2 then
        (U ^ (p.1.1.val + 1) *ᵥ (fun w => ψ (p.1, w))) p.2 else ψ p := by
  funext ⟨⟨t, b⟩, z⟩
  rw [reflections_clock_loop_fibre, min_eq_right (by omega : t.val + 1 ≤ τ)]

/-- Framing a normalized state preserves normalization. -/
theorem reflectionsFrame_normalized (addr : H → Fin n) (ψ : QState (A × H))
    (hψ : Normalized ψ) : Normalized (reflectionsFrame addr ψ) := by
  have he :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.measureProb_mulVec
      (reflectionsFrameMatrix_isometry (A := A) addr) ψ
  rw [reflectionsFrameMatrix_apply] at he
  exact he.trans hψ

/-- The tensor product of a uniform clock state, a plus control state, and the input state `r`. -/
def reflectionsTrialStart (τ : ℕ) (r : QState H) : QState ((Fin τ × Bool) × H) :=
  TensorState (TensorState (Uniform (Fin τ)) Plus) r

/-- The trial start state is normalized when the clock is nonempty and `r` is normalized. -/
theorem reflectionsTrialStart_normalized (τ : ℕ) (hτ : 0 < τ)
    (r : QState H) (hr : Normalized r) : Normalized (reflectionsTrialStart τ r) :=
  normalized_tensorState
    (normalized_tensorState (normalized_uniform (by simpa using hτ)) normalized_plus) hr

/-- A unitary prepares any normalized framed state from the specified framed basis state. -/
theorem reflections_frame_prepare (addr : H → Fin n) (j : A × H)
    (ψ : QState (A × H)) (hψ : Normalized ψ) :
    ∃ K : Matrix ((Fin n × Bool) × (A × H)) ((Fin n × Bool) × (A × H)) ℂ,
      K ∈ Matrix.unitaryGroup _ ℂ ∧
      ApplyGate K (Qatlib.Foundations.PureStateMath.Ket ((addr j.2, false), j)) = reflectionsFrame addr ψ := by
  let S : Matrix ((Fin n × Bool) × (A × H)) Unit ℂ :=
      fun p _ => Qatlib.Foundations.PureStateMath.Ket ((addr j.2, false), j) p
  let T : Matrix ((Fin n × Bool) × (A × H)) Unit ℂ := fun p _ => reflectionsFrame addr ψ p
  have hs : Sᴴ * S = Tᴴ * T := by
    ext i k
    change Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket ((addr j.2, false), j)) (Qatlib.Foundations.PureStateMath.Ket ((addr j.2, false), j)) =
      Qatlib.Foundations.PureStateMath.Inner (reflectionsFrame addr ψ) (reflectionsFrame addr ψ)
    rw [(normalized_iff_inner_self _).mp (normalized_ket _),
      (normalized_iff_inner_self _).mp (reflectionsFrame_normalized addr ψ hψ)]
  obtain ⟨K, hK, hKT⟩ := gram_equal_actual_unitary_transport _ Unit S T hs
  refine ⟨K, hK, ?_⟩
  funext p
  exact congrArg (fun M : Matrix _ Unit ℂ => M p ()) hKT

/-- The Hadamard gate on the trial control bit, tensored with identities on the clock and state
registers. -/
def reflectionsTrialHadamard (τ : ℕ) : Matrix ((Fin τ × Bool) × H) ((Fin τ × Bool) × H) ℂ :=
  TensorGate (TensorGate (1 : Matrix (Fin τ) (Fin τ) ℂ) Hadamard) 1

/-- The trial-control Hadamard gate is unitary. -/
theorem reflectionsTrialHadamard_unitary (τ : ℕ) :
    reflectionsTrialHadamard (H := H) τ ∈ Matrix.unitaryGroup _ ℂ :=
  tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

/-- Gives the sum-and-difference amplitude formula for the trial-control Hadamard gate. -/
theorem reflectionsTrialHadamard_apply (τ : ℕ) (ψ : QState ((Fin τ × Bool) × H))
    (t : Fin τ) (b : Bool) (z : H) :
    ApplyGate (reflectionsTrialHadamard τ) ψ ((t, b), z) =
      (Real.sqrt 2 : ℂ)⁻¹ *
        (ψ ((t, false), z) + (if b then -1 else 1) * ψ ((t, true), z)) := by
  simp only [ApplyGate, reflectionsTrialHadamard, TensorGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply, Hadamard,
    Matrix.of_apply, Fintype.sum_bool]
  cases b <;> simp [ite_mul, mul_ite, Finset.sum_add_distrib] <;> ring

set_option autoImplicit false

/-- The clock-indexed sum and difference of `r` and its image under the corresponding positive
power of `U`. -/
def reflectionsTrialOutput (τ : ℕ) (U : Matrix H H ℂ) (r : QState H) :
    QState ((Fin τ × Bool) × H) := fun p =>
  Uniform (Fin τ) p.1.1 / 2 *
    (r p.2 + (if p.1.2 then -1 else 1) * (U ^ (p.1.1.val + 1) *ᵥ r) p.2)

/-- A clocked loop followed by the trial Hadamard produces `reflectionsTrialOutput` from the
trial start state. -/
theorem reflections_trial_output (τ : ℕ) (U : Matrix H H ℂ) (r : QState H) :
    ApplyGate (reflectionsTrialHadamard τ)
      (reflectionsLoop (reflectionsClockActive τ) U τ *ᵥ reflectionsTrialStart τ r) =
      reflectionsTrialOutput τ U r := by
  funext ⟨⟨t, b⟩, z⟩
  rw [reflectionsTrialHadamard_apply, reflections_clock_loop_complete]
  have hf (c : Bool) : (fun w => reflectionsTrialStart τ r ((t, c), w)) =
      (Uniform (Fin τ) t * (Real.sqrt 2 : ℂ)⁻¹) • r := by
    funext w
    simp [reflectionsTrialStart, TensorState, Plus, Hadamard, mul_assoc]
  simp only [hf, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ite_true]
  simp only [reflectionsTrialStart, TensorState, Plus, Hadamard, Matrix.of_apply,
    Bool.and_false, Bool.false_eq_true, ite_false, reflectionsTrialOutput]
  have hs := inv_sqrt2_mul_self
  linear_combination (Uniform (Fin τ) t *
    (r z + (if b then -1 else 1) * (U ^ (t.val + 1) *ᵥ r) z)) * hs

/-- Measuring a logical event after framing has the same probability as measuring that event in
the original state. -/
theorem reflections_frame_readout (addr : H → Fin n) (ψ : QState (A × H))
    (E : Finset (A × H)) :
    MeasureProb (reflectionsFrame addr ψ)
      (Finset.univ.filter (fun p : (Fin n × Bool) × (A × H) => p.2 ∈ E)) =
      MeasureProb ψ E := by
  let F := Finset.univ.filter (fun p : (Fin n × Bool) × (A × H) => p.2 ∈ E)
  have he : Collapse (reflectionsFrame addr ψ) F = reflectionsFrame addr (Collapse ψ E) := by
    funext p
    simp only [collapse_apply, reflectionsFrame, F, Finset.mem_filter,
      Finset.mem_univ, true_and]
    split_ifs <;> rfl
  have hm :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.measureProb_mulVec
      (reflectionsFrameMatrix_isometry (A := A) addr) (Collapse ψ E)
  rw [reflectionsFrameMatrix_apply, ← he, measureProb_collapse,
    measureProb_collapse, Finset.inter_univ, Finset.inter_univ] at hm
  exact hm

/-- Constructs the framed source-walk trial from a fixed basis state with exactly `2 * τ`
queries and `2 * τ + 2` gates. -/
theorem reflections_actual_trial (X : Type) [Fintype X] [DecidableEq X]
    (n m τ : ℕ) (f : X → Bool) (hn : 0 < n) (hτ : 0 < τ)
    (input : X → Fin n → Bool)
    (Δ : Matrix (Vertex X f n m) (Vertex X f n m) ℂ) (hΔ : IsOrthogonalProjector Δ) :
    ∃ C : Circuit ((Fin n × Bool) × ((Fin τ × Bool) × Vertex X f n m)),
      IsUnitaryCircuit C ∧ QueryCount C = 2 * τ ∧ GateCount C = 2 * τ + 2 ∧
      ∀ x : X, Run (workspaceBitOracle (input x)) C
        (Qatlib.Foundations.PureStateMath.Ket ((⟨0, hn⟩, false), ((⟨0, hτ⟩, false), Sum.inr (Sum.inl ())))) =
        reflectionsFrame (reflectionsVertexAddress f hn)
          (reflectionsTrialOutput τ (twoReflectionUnitary input f x Δ)
            (Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ())))) := by
  let r : QState (Vertex X f n m) :=
      Qatlib.Foundations.PureStateMath.Ket (Sum.inr (Sum.inl ()))
  let addr := reflectionsVertexAddress (m := m) f hn
  let j : (Fin τ × Bool) × Vertex X f n m := ((⟨0, hτ⟩, false), Sum.inr (Sum.inl ()))
  obtain ⟨P, hP, hPr⟩ := reflections_frame_prepare addr j (reflectionsTrialStart τ r)
    (reflectionsTrialStart_normalized τ hτ r (normalized_ket _))
  obtain ⟨H, hH, hHr⟩ := reflectionsFrame_transport addr
    (reflectionsTrialHadamard (H := Vertex X f n m) τ) (reflectionsTrialHadamard_unitary τ)
  obtain ⟨D, hD, hDQ, hDG, hDr⟩ := reflections_counted_source_loop (Fin τ × Bool) X n m f
    hn input Δ hΔ (reflectionsClockActive τ) τ
  let C := [Step.gate P] ++ D ++ [Step.gate H]
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · apply (isUnitaryCircuit_append _ _).mpr
    exact ⟨(isUnitaryCircuit_append _ _).mpr
      ⟨reflections_single_gate_wellFormed P hP, hD⟩,
      reflections_single_gate_wellFormed H hH⟩
  · simp [C, queryCount_append, hDQ]
  · simp [C, gateCount_append, hDG]
  · intro x
    change Run (workspaceBitOracle (input x)) C
        (Qatlib.Foundations.PureStateMath.Ket ((addr j.2, false), j)) = _
    rw [show C = ([Step.gate P] ++ D) ++ [Step.gate H] from rfl,
      run_append, run_append]
    simp only [Run]
    rw [hPr, hDr, hHr, reflections_trial_output]

namespace ReflectionsFresh
open Matrix
open scoped Classical BigOperators

variable {n k : ℕ} {W : Type} [Fintype W] [DecidableEq W]

/-- Swaps the shared query register with the query register of copy `j`, leaving that copy's
workspace unchanged. -/
private def copySwap (j : Fin k)
    (z : (Fin n × Bool) × (Fin k → (Fin n × Bool) × W)) :=
  ((z.2 j).1, Function.update z.2 j (z.1, (z.2 j).2))

omit [Fintype W] [DecidableEq W] in

/-- Swapping the shared query register with a fixed copy twice is the identity. -/
private theorem copySwap_involutive (j : Fin k) : Function.Involutive (copySwap (n := n) (W := W) j) := by
  intro z
  apply Prod.ext
  · simp [copySwap]
  · funext l
    by_cases hl : l = j
    · subst l; simp [copySwap]
    · simp [copySwap]

/-- The permutation gate routing the shared query register to copy `j`. -/
private noncomputable def copySwapGate (j : Fin k) := permMatrix (copySwap (n := n) (W := W) j)

/-- The query-routing swap gate is unitary. -/
private theorem copySwapGate_unitary (j : Fin k) :
    copySwapGate (n := n) (W := W) j ∈ Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary (copySwap_involutive j)

/-- Swapping into copy `j`, querying, and swapping back applies the oracle to that copy alone on
tensor-product inputs. -/
private theorem routed_query (j : Fin k) (x : Fin n → Bool)
    (χ : QState (Fin n × Bool)) (ψ : Fin k → QState ((Fin n × Bool) × W)) :
    ApplyGate (copySwapGate j) (ApplyGate (workspaceBitOracle x)
      (ApplyGate (copySwapGate j) (TensorState χ (PiTensorState ψ)))) =
    TensorState χ (PiTensorState (Function.update ψ j
      (ApplyGate (workspaceBitOracle x) (ψ j)))) := by
  funext z
  simp only [copySwapGate, applyGate_permMatrix (copySwap_involutive j),
    applyGate_workspaceBitOracle, copySwap, Function.update_self, tensorState_apply,
    piTensorState_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  by_cases hl : l = j
  · subst l
    simp [applyGate_workspaceBitOracle]
  · simp [hl]

/-- Routes a circuit to copy `j`, replacing each query by a swap-query-swap sequence through the
shared query register. -/
noncomputable def StandardCopyCircuit (j : Fin k) :
    Circuit ((Fin n × Bool) × W) →
      Circuit ((Fin n × Bool) × (Fin k → (Fin n × Bool) × W))
  | [] => []
  | Step.gate U :: C => Step.gate (TensorGate 1 (FactorGate j U)) :: StandardCopyCircuit j C
  | Step.query :: C => Step.gate (copySwapGate j) :: Step.query ::
      Step.gate (copySwapGate j) :: StandardCopyCircuit j C

/-- Routing a unitary circuit to one copy preserves circuit unitarity. -/
theorem standardCopyCircuit_unitary (j : Fin k)
    {C : Circuit ((Fin n × Bool) × W)} (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (StandardCopyCircuit j C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    have htail : IsUnitaryCircuit C := fun U hU => hC U (List.mem_cons_of_mem _ hU)
    cases s with
    | gate U =>
      exact (isUnitaryCircuit_gate _ _).mpr
        ⟨tensorGate_unitary (Submonoid.one_mem _) (factorGate_unitary j (hC U List.mem_cons_self)),
          ih htail⟩
    | query =>
      exact (isUnitaryCircuit_gate _ _).mpr ⟨copySwapGate_unitary j,
        (isUnitaryCircuit_query _).mpr ((isUnitaryCircuit_gate _ _).mpr
          ⟨copySwapGate_unitary j, ih htail⟩)⟩

omit [Fintype W] in

/-- Routing a circuit to one copy preserves its query count. -/
theorem standardCopyCircuit_queries (j : Fin k) (C : Circuit ((Fin n × Bool) × W)) :
    QueryCount (StandardCopyCircuit j C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [StandardCopyCircuit, QueryCount, ih]

omit [Fintype W] in

/-- Routing a circuit to one copy adds two gates for each original query. -/
theorem standardCopyCircuit_gates (j : Fin k) (C : Circuit ((Fin n × Bool) × W)) :
    GateCount (StandardCopyCircuit j C) = GateCount C + 2 * QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [StandardCopyCircuit, GateCount, QueryCount, ih] <;> omega

/-- The routed circuit runs the original circuit on copy `j` of a tensor-product input and
preserves the other factors. -/
theorem standardCopyCircuit_run (j : Fin k) (C : Circuit ((Fin n × Bool) × W))
    (x : Fin n → Bool) (χ : QState (Fin n × Bool))
    (ψ : Fin k → QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle x) (StandardCopyCircuit j C) (TensorState χ (PiTensorState ψ)) =
      TensorState χ (PiTensorState (Function.update ψ j (Run (workspaceBitOracle x) C (ψ j)))) := by
  induction C generalizing ψ with
  | nil => simp [StandardCopyCircuit, Run, Function.update_eq_self]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [StandardCopyCircuit, run_gate, applyGate_tensorGate, applyGate_one,
        applyGate_factorGate_piTensorState, ih, run_gate]
      simp
    | query =>
      rw [StandardCopyCircuit, run_gate, run_query, run_gate, routed_query, ih, run_query]
      simp

/-- Concatenates the routed circuit for every copy in `Fin k`. -/
noncomputable def StandardCopiesCircuit (k : ℕ) (C : Circuit ((Fin n × Bool) × W)) :
    Circuit ((Fin n × Bool) × (Fin k → (Fin n × Bool) × W)) :=
  (List.finRange k).flatMap fun j => StandardCopyCircuit j C

/-- Concatenating routed versions of a unitary circuit over a list of copy indices yields a
unitary circuit. -/
private theorem copies_list_unitary {C : Circuit ((Fin n × Bool) × W)}
    (hC : IsUnitaryCircuit C) (L : List (Fin k)) :
    IsUnitaryCircuit (L.flatMap fun j => StandardCopyCircuit j C) := by
  induction L with
  | nil => exact isUnitaryCircuit_nil
  | cons j L ih =>
    simp only [List.flatMap_cons, isUnitaryCircuit_append]
    exact ⟨standardCopyCircuit_unitary j hC, ih⟩

/-- The query count of a list of routed copies is the list length times the original query
count. -/
private theorem copies_list_queries (C : Circuit ((Fin n × Bool) × W)) (L : List (Fin k)) :
    QueryCount (L.flatMap fun j => StandardCopyCircuit j C) = L.length * QueryCount C := by
  induction L with
  | nil => simp
  | cons j L ih => simp [queryCount_append, standardCopyCircuit_queries, ih, Nat.succ_mul, Nat.add_comm]

/-- A list of routed copies uses its length times the original gate count plus twice the
original query count per copy. -/
private theorem copies_list_gates (C : Circuit ((Fin n × Bool) × W)) (L : List (Fin k)) :
    GateCount (L.flatMap fun j => StandardCopyCircuit j C) =
      L.length * (GateCount C + 2 * QueryCount C) := by
  induction L with
  | nil => simp
  | cons j L ih => simp [gateCount_append, standardCopyCircuit_gates, ih, Nat.succ_mul, Nat.add_comm]

/-- For a list without repeated indices, the routed circuits update exactly the listed tensor
factors by the original circuit. -/
private theorem copies_list_run (C : Circuit ((Fin n × Bool) × W)) (x : Fin n → Bool)
    (χ : QState (Fin n × Bool)) (L : List (Fin k)) (hL : L.Nodup)
    (ψ : Fin k → QState ((Fin n × Bool) × W)) :
    Run (workspaceBitOracle x) (L.flatMap fun j => StandardCopyCircuit j C)
      (TensorState χ (PiTensorState ψ)) =
    TensorState χ (PiTensorState fun j => if j ∈ L then Run (workspaceBitOracle x) C (ψ j)
      else ψ j) := by
  induction L generalizing ψ with
  | nil => simp
  | cons j L ih =>
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hL
    simp only [List.flatMap_cons]
    rw [run_append, standardCopyCircuit_run, ih hnd]
    congr 2
    funext l
    by_cases hl : l = j
    · subst l; simp [hj]
    · simp [hl]

/-- Constructs independent runs on all `k` tensor factors with `k` times the original queries
and two routing gates per copied query. -/
theorem standardCopiesCircuit_spec (k : ℕ) (C : Circuit ((Fin n × Bool) × W))
    (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (StandardCopiesCircuit k C) ∧
    QueryCount (StandardCopiesCircuit k C) = k * QueryCount C ∧
    GateCount (StandardCopiesCircuit k C) = k * GateCount C + 2 * k * QueryCount C ∧
    ∀ (x : Fin n → Bool) (χ : QState (Fin n × Bool))
      (ψ : Fin k → QState ((Fin n × Bool) × W)),
      Run (workspaceBitOracle x) (StandardCopiesCircuit k C) (TensorState χ (PiTensorState ψ)) =
      TensorState χ (PiTensorState fun j => Run (workspaceBitOracle x) C (ψ j)) := by
  refine ⟨copies_list_unitary hC _, ?_, ?_, ?_⟩
  · simpa [StandardCopiesCircuit] using copies_list_queries C (List.finRange k)
  · simpa [StandardCopiesCircuit, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using copies_list_gates C (List.finRange k)
  · intro x χ ψ
    simpa [StandardCopiesCircuit] using copies_list_run C x χ
      (List.finRange k) (List.nodup_finRange k) ψ

end ReflectionsFresh

/-- The probability of a false trial-control outcome equals `reflectionsPowerMean`. -/
theorem reflections_trial_born (τ : ℕ) (U : Matrix H H ℂ) (r : QState H) :
    MeasureProb (reflectionsTrialOutput τ U r)
      (Finset.univ.filter (fun p : (Fin τ × Bool) × H => p.1.2 = false)) =
      reflectionsPowerMean τ U r := by
  simp only [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, reflectionsTrialOutput,
    BornProb, one_mul, norm_mul, norm_div, mul_pow, div_pow]
  have hc (t : Fin τ) : ‖Uniform (Fin τ) t‖ ^ 2 / ‖(2 : ℂ)‖ ^ 2 =
      (4 * (τ : ℝ))⁻¹ := by
    have h := bornProb_uniform t
    change ‖Uniform (Fin τ) t‖ ^ 2 = _ at h
    rw [h, Fintype.card_fin]
    norm_num
    ring
  simp only [hc]
  norm_num
  simp only [reflectionsPowerMean, norm_toEuclidean_fromVec_sq, Pi.add_apply, _root_.mul_inv_rev]
  simp_rw [← Finset.mul_sum]
  ring

/-- The event that at least 75 of 100 coordinates belong to `S`. -/
def reflectionsAccept100 (S : Finset H) : Finset (Fin 100 → H) :=
  Finset.univ.filter (fun ω => 75 ≤ (Finset.univ.filter (fun j => ω j ∈ S)).card)

/-- The finite probability distribution given by the Born probabilities of a normalized state. -/
def reflectionsBornLaw (φ : QState H) (hφ : Normalized φ) : FinDist H where
  prob := BornProb φ
  nonneg := bornProb_nonneg φ
  sum_one := hφ

/-- For 100 tensor copies, the threshold event or its complement has probability at least 2/3
under the respective 9/10 or 3/5 probability bound. -/
theorem reflections_fresh100_born (φ : QState H) (hφ : Normalized φ) (S : Finset H)
    (b : Bool) (hgap : if b then (9 / 10 : ℝ) ≤ MeasureProb φ S
      else MeasureProb φ S ≤ (3 / 5 : ℝ)) :
    (2 / 3 : ℝ) ≤ MeasureProb (PiTensorState (fun _ : Fin 100 => φ))
      (if b then reflectionsAccept100 S else (reflectionsAccept100 S)ᶜ) := by
  classical
  let p := reflectionsBornLaw φ hφ
  let g : H → ℝ := fun z => if z ∈ S then 1 else 0
  have hg (z : H) : 0 ≤ g z ∧ g z ≤ 1 := by dsimp [g]; split_ifs <;> norm_num
  have hmean : p.expect g = MeasureProb φ S := by
    simp [p, reflectionsBornLaw, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, g,
        MeasureProb]
  have hd : ∀ i (ω η : Fin 100 → H), (∀ j, j ≠ i → ω j = η j) →
      |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g ω - Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g η| ≤ (1 / 100 : ℝ) := by
    intro i ω η h
    rw [finite_avg_coordinate_difference 100 g ω η i h, abs_div]
    norm_num
    apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr
    have ha := abs_le.mpr (show -(1 : ℝ) ≤ g (ω i) - g (η i) ∧
        g (ω i) - g (η i) ≤ 1 by constructor <;> linarith [(hg (ω i)).1,
          (hg (ω i)).2, (hg (η i)).1, (hg (η i)).2])
    nlinarith
  have hs : (∑ i : Fin 100, ((1 / 100 : ℝ)) ^ 2) = 1 / 100 := by norm_num
  have ht := (finite_product_bounded_differences_tail H 100 (fun _ => p)
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g) (fun _ => 1 / 100) (3 / 20)
    (fun _ => by norm_num) (by rw [hs]; norm_num) (by norm_num) hd).2
  have hm : (independentSampleLaw (fun _ : Fin 100 => p)).expect (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g) =
      MeasureProb φ S := (p.expect_avg g (by norm_num)).trans hmean
  rw [hm, hs] at ht
  norm_num at ht
  have hexp : 2 * Real.exp (-(9 / 2 : ℝ)) ≤ 1 / 3 := by
    have he2 : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have he4 : 9 ≤ Real.exp 4 := by
      have he := Real.exp_add (2 : ℝ) 2
      norm_num at he
      nlinarith [Real.exp_pos (2 : ℝ)]
    have hneg : Real.exp (-(9 / 2 : ℝ)) ≤ (Real.exp 4)⁻¹ := by
      rw [← Real.exp_neg]
      exact (Real.exp_le_exp).mpr (by norm_num)
    have hinv : (Real.exp 4)⁻¹ ≤ (9 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos 4) (by norm_num)).mpr he4
    linarith
  let bad : Finset (Fin 100 → H) :=
    if b then (reflectionsAccept100 S)ᶜ else reflectionsAccept100 S
  have havg (ω : Fin 100 → H) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g ω =
      ((Finset.univ.filter (fun j => ω j ∈ S)).card : ℝ) / 100 := by
    simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg, g]
  have hb : bad ⊆ Finset.univ.filter
      (fun ω => (3 / 20 : ℝ) ≤ |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g ω - MeasureProb φ S|) := by
    intro ω hω
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [havg]
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hgap
      have hc : 75 ≤ (Finset.univ.filter (fun j => ω j ∈ S)).card := by
        simpa [bad, reflectionsAccept100] using hω
      have hc' : (75 : ℝ) ≤ (Finset.univ.filter (fun j => ω j ∈ S)).card :=
        by exact_mod_cast hc
      apply le_trans _ (le_abs_self _)
      linarith
    · simp only [ite_true] at hgap
      have hc : (Finset.univ.filter (fun j => ω j ∈ S)).card < 75 := by
        simpa [bad, reflectionsAccept100, not_le] using hω
      have hc' : ((Finset.univ.filter (fun j => ω j ∈ S)).card : ℝ) < 75 :=
        by exact_mod_cast hc
      apply le_trans _ (neg_le_abs _)
      linarith
  have hbad : MeasureProb (PiTensorState (fun _ : Fin 100 => φ)) bad ≤ 1 / 3 := by
    calc
      _ = ∑ ω ∈ bad, (independentSampleLaw (fun _ : Fin 100 => p)).prob ω := by
        apply Finset.sum_congr rfl
        intro ω _
        exact bornProb_piTensorState (fun _ : Fin 100 => φ) ω
      _ ≤ ∑ ω ∈ Finset.univ.filter
          (fun ω => (3 / 20 : ℝ) ≤ |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg g ω - MeasureProb φ S|),
          (independentSampleLaw (fun _ : Fin 100 => p)).prob ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hb (fun ω _ _ =>
          (independentSampleLaw (fun _ : Fin 100 => p)).nonneg ω)
      _ ≤ 1 / 3 := ht.trans hexp
  have hu := measureProb_univ
    (normalized_piTensorState (fun _ : Fin 100 => hφ))
  have hc := measureProb_union (PiTensorState (fun _ : Fin 100 => φ))
    (S := reflectionsAccept100 S) (T := (reflectionsAccept100 S)ᶜ)
    (Finset.disjoint_left.mpr (by
      intro z hz hzc
      exact (Finset.mem_compl.mp hzc) hz))
  rw [Finset.union_compl] at hc
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hbad ⊢ <;>
    dsimp [bad] at hbad <;> linarith

/-- Amplifies the stated decision gap to success probability at least 2/3 using 100 copies and
exact routing resource counts. -/
theorem reflections_amplified_actual (X : Type) [Fintype X] [DecidableEq X]
    (n : ℕ) (hn : 0 < n) (input : X → Fin n → Bool) (f : X → Bool)
    {W : Type} [Fintype W] [DecidableEq W] (j : W)
    (C : Circuit ((Fin n × Bool) × W)) (hC : IsUnitaryCircuit C)
    (S : Finset ((Fin n × Bool) × W))
    (hgap : ∀ x, if f x then (9 / 10 : ℝ) ≤ MeasureProb
        (Run (workspaceBitOracle (input x)) C (Qatlib.Foundations.PureStateMath.Ket ((⟨0, hn⟩, false), j))) S
      else MeasureProb (Run (workspaceBitOracle (input x)) C
        (Qatlib.Foundations.PureStateMath.Ket ((⟨0, hn⟩, false), j))) S ≤ (3 / 5 : ℝ)) :
    ∃ (r : ℕ) (hr : 0 < r) (D : Circuit ((Fin n × Bool) × Fin r))
      (E : Finset ((Fin n × Bool) × Fin r)), IsUnitaryCircuit D ∧
      QueryCount D = 100 * QueryCount C ∧
      GateCount D = 100 * GateCount C + 200 * QueryCount C ∧
      ∀ x, (2 / 3 : ℝ) ≤ MeasureProb (Run (workspaceBitOracle (input x)) D
        (Qatlib.Foundations.PureStateMath.Ket ((⟨0, hn⟩, false), ⟨0, hr⟩))) (if f x then E else Eᶜ) := by
  classical
  let bus : Fin n × Bool := (⟨0, hn⟩, false)
  let z : (Fin n × Bool) × W := (bus, j)
  let B := ReflectionsFresh.StandardCopiesCircuit 100 C
  obtain ⟨hB, hBQ, hBG, hBr⟩ := ReflectionsFresh.standardCopiesCircuit_spec 100 C hC
  let V := Fin 100 → (Fin n × Bool) × W
  let j0 : V := fun _ => z
  let : Nonempty V := ⟨j0⟩
  let r := Fintype.card V
  have hr : 0 < r := Fintype.card_pos
  let e0 : V ≃ Fin r := Fintype.equivFin V
  let e : V ≃ Fin r := e0.trans (Equiv.swap (e0 j0) ⟨0, hr⟩)
  have he0 : e j0 = ⟨0, hr⟩ := by simp [e]
  let q : ((Fin n × Bool) × V) ≃ ((Fin n × Bool) × Fin r) :=
    Equiv.prodCongr (Equiv.refl _) e
  let E0 : Finset ((Fin n × Bool) × V) := Finset.univ ×ˢ reflectionsAccept100 S
  let E := E0.map q.toEmbedding
  have hleg := relabelCircuit_legality_resources q B
  refine ⟨r, hr, relabelCircuit q B, E, hleg.1.mpr hB,
    hleg.2.1.trans hBQ, ?_, ?_⟩
  · rw [hleg.2.2.1, hBG]
  · intro x
    let φ := Run (workspaceBitOracle (input x)) C (Qatlib.Foundations.PureStateMath.Ket z)
    have hφ : Normalized φ := hC.normalized_run (workspaceBitOracle_unitary _) (normalized_ket _)
    have hprob := reflections_fresh100_born φ hφ S (f x) (hgap x)
    have hstart : TensorState (Qatlib.Foundations.PureStateMath.Ket bus) (PiTensorState (fun _ : Fin 100 => Qatlib.Foundations.PureStateMath.Ket z)) =
        Qatlib.Foundations.PureStateMath.Ket (bus, j0) := by rw [piTensorState_const_ket, tensorState_ket_ket]
    have hRun : Run (workspaceBitOracle (input x)) B (Qatlib.Foundations.PureStateMath.Ket (bus, j0)) =
        TensorState (Qatlib.Foundations.PureStateMath.Ket bus) (PiTensorState (fun _ : Fin 100 => φ)) := by
      rw [← hstart]
      exact hBr (input x) (Qatlib.Foundations.PureStateMath.Ket bus)
          (fun _ => Qatlib.Foundations.PureStateMath.Ket z)
    have hO : relabelGate q (workspaceBitOracle (W := V) (input x)) =
        workspaceBitOracle (W := Fin r) (input x) := by
      ext a b
      simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
        workspaceBitOracle, TensorGate]
      change BitOracleOn (input x) a.1 b.1 * (if e.symm a.2 = e.symm b.2 then 1 else 0) =
        BitOracleOn (input x) a.1 b.1 * (if a.2 = b.2 then 1 else 0)
      simp only [e.symm.injective.eq_iff]
    have hket : relabelState q (Qatlib.Foundations.PureStateMath.Ket (bus, j0)) = Qatlib.Foundations.PureStateMath.Ket (bus, ⟨0, hr⟩) := by
      have hk : relabelState q (Qatlib.Foundations.PureStateMath.Ket (bus, j0)) = Qatlib.Foundations.PureStateMath.Ket (q (bus, j0)) := by
        funext a
        simp [relabelState, Qatlib.Foundations.PureStateMath.Ket, Equiv.symm_apply_eq]
      simpa [q, he0] using hk
    let F : Finset V := if f x then reflectionsAccept100 S else (reflectionsAccept100 S)ᶜ
    have hF : (Finset.univ ×ˢ F).map q.toEmbedding = if f x then E else Eᶜ := by
      have hc : (Finset.univ ×ˢ (reflectionsAccept100 S)ᶜ).map q.toEmbedding = Eᶜ := by
        ext a
        simp only [E, E0, Finset.mem_compl, Finset.mem_map, Finset.mem_product,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨w, hw, rfl⟩ ⟨v, hv, he⟩
          have hvw := q.injective he
          subst v
          exact hw hv
        · intro ha
          refine ⟨q.symm a, ?_, q.apply_symm_apply a⟩
          intro hs
          exact ha ⟨q.symm a, hs, q.apply_symm_apply a⟩
      cases hx : f x <;> simp [F, hx, hc, E0, E]
    have he := (run_relabelCircuit_readout q (workspaceBitOracle (input x)) B
      (Qatlib.Foundations.PureStateMath.Ket (bus, j0)) (Finset.univ ×ˢ F)).2
    rw [hO, hket, hF, hRun,
      measureProb_tensorState_right (normalized_ket _)] at he
    rw [he]
    exact hprob

end Qatlib.Concepts.ConversionCore.WitnessCompile
