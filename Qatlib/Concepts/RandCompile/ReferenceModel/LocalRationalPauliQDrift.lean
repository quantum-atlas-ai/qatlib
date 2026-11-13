/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ReferenceModel.LocalPauliEvolution
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# Rational local Pauli qDRIFT

This module compiles dyadically quantized Pauli qDRIFT samples into local gate programs with
rational phase approximations. It relates their averaged output to fresh reference mixtures and
combines the qDRIFT simulation error of [Campbell2019] with finite sampling, phase, and
coefficient errors.

## Main statements

* `local_pauli_qdrift_actual_paths_arithmetic_and_zero`: path legality, exact resource counts,
  and the zero-weight case.
* `local_quantized_pauli_qdrift_actual_total_error`: the combined finite-reference error
  estimate.
* `local_pauli_qdrift_computed_finite_precision_budget`: explicit step and precision choices for
  a dyadic error target.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.RandCompile.EffectiveInput
open Qatlib.Concepts.RandCompile.FairBitSampling

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.RandCompile.ReferenceModel
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option maxHeartbeats 2000000

/-- The rational qDRIFT time for a selected term, using its dyadic coefficient sign and the
total dyadic weight. -/
def localPauliQdriftAngle {L : ℕ} (b N : ℕ) (a : Fin L → ℚ) (t : ℚ) (j : Fin L) : ℚ :=
  (if dyadicCoefficient b (a j) < 0 then (-1 : ℚ) else 1) * t *
    (weightTotal (dyadicWeights b a) : ℚ) / ((2 : ℚ)^b * N)

/-- The flattened sequence of rational Pauli circuits selected by the bounded fair-bit sampler,
or the empty sequence when the total weight is zero. -/
noncomputable def localPauliQdriftSteps {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (labels : Fin L → Fin q → Fin 4) (t : ℚ)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))) :
    List (ReflectionGate q) :=
  if weightTotal (dyadicWeights b a) = 0 then [] else
    (List.ofFn (fun i : Fin N =>
      let j := (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1
      localPauliRationalSteps q (labels j) (localPauliQdriftAngle b N a t j) k)).flatten

/-- The average reference-extended conjugation by the sampled local Pauli circuits, returning
the input when the total weight is zero. -/
noncomputable def localPauliQdriftOutput {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (labels : Fin L → Fin q → Fin 4) (t : ℚ) (r : ℕ)
    (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ) :
    Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ :=
  if weightTotal (dyadicWeights b a) = 0 then X else
    ∑ ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))),
      ((independentSampleLaw (fun _ : Fin N =>
        fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))))).prob ω : ℂ) •
      (let U := relabelGate (bitVecEquiv q)
        (reflectionProgramMatrix (localPauliQdriftSteps q b N R k a j0 labels t ω))
       TensorGate U (1 : Operator r) * X * (TensorGate U (1 : Operator r))ᴴ)

/-- The phase arithmetic counts for one selected Pauli term, with zero counts when its support
is empty. -/
def localPauliSelectedArithmetic {L : ℕ} (q b N k : ℕ) (a : Fin L → ℚ)
    (labels : Fin L → Fin q → Fin 4) (t : ℚ) (j : Fin L) : ℕ × ℕ × ℕ × ℕ :=
  match pauliStringTarget q (labels j) with
  | none => (0,0,0,0)
  | some _ => (localPauliPhaseData (localPauliQdriftAngle b N a t j) k).2

/-- The sum of selected phase arithmetic counts along a sampled path, with zero counts for zero
total weight. -/
def localPauliPhaseArithmetic {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (labels : Fin L → Fin q → Fin 4) (t : ℚ)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))) :
    ℕ × ℕ × ℕ × ℕ :=
  if weightTotal (dyadicWeights b a) = 0 then (0,0,0,0) else
    ∑ i : Fin N,
      localPauliSelectedArithmetic q b N k a labels t
        (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1

/-- Flattening a list of legal reflection programs produces a legal reflection program. -/
private theorem reflection_flatten_legal {q : ℕ} (words : List (List (ReflectionGate q)))
    (h : ∀ word ∈ words, reflectionLegal word) : reflectionLegal words.flatten := by
  intro g hg
  obtain ⟨word,hw,hg⟩ := List.mem_flatten.mp hg
  exact h word hw g hg

/-- The gate count of a flattened reflection program equals the sum of the gate counts of its
component programs. -/
private theorem reflection_flatten_length {q : ℕ} (words : List (List (ReflectionGate q))) :
    GateCount (reflectionCompile words.flatten) =
      (words.map (fun word => GateCount (reflectionCompile word))).sum := by
  simp only [gateCount_reflectionCompile,List.length_flatten]

/-- Every sampled local Pauli path is legal, uses zero queries, and has gate count equal to the
sum of its selected term costs when the weight is positive. Its gate count is at most
`N*(6*q+1)`. -/
theorem localPauliQdrift_path_gates {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (v : Fin L → Fin q → Fin 4) (t : ℚ)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))) :
    reflectionLegal (localPauliQdriftSteps q b N R k a j0 v t ω) ∧
    QueryCount (reflectionCompile (localPauliQdriftSteps q b N R k a j0 v t ω)) = 0 ∧
    GateCount (reflectionCompile (localPauliQdriftSteps q b N R k a j0 v t ω)) =
      (if weightTotal (dyadicWeights b a) = 0 then 0 else
        ∑ i : Fin N, localPauliGateCost q (v (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1)) ∧
    GateCount (reflectionCompile (localPauliQdriftSteps q b N R k a j0 v t ω)) ≤ N*(6*q+1) := by
  by_cases hW : weightTotal (dyadicWeights b a) = 0
  · simp [localPauliQdriftSteps,hW,reflectionLegal,reflectionCompile]
  · have hlegal : reflectionLegal (localPauliQdriftSteps q b N R k a j0 v t ω) := by
      rw [localPauliQdriftSteps,if_neg hW]
      apply reflection_flatten_legal
      intro word hw
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
      subst word
      exact (localPauliSteps_legal _ _ _ _).2
    have hcount : GateCount (reflectionCompile (localPauliQdriftSteps q b N R k a j0 v t ω)) =
        ∑ i : Fin N, localPauliGateCost q (v (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1) := by
      rw [localPauliQdriftSteps,if_neg hW,reflection_flatten_length,List.map_ofFn,List.sum_ofFn]
      exact Finset.sum_congr rfl fun i _ => localPauliSteps_gateCount _ _ _ _
    refine ⟨hlegal,queryCount_reflectionCompile _,by rw [if_neg hW]; exact hcount,?_⟩
    rw [hcount]
    calc
      _ ≤ ∑ _ : Fin N, (6*q+1) := Finset.sum_le_sum fun i _ =>
        (local_pauli_exact_and_finite_phase_gate_tables q
          (v (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1) 0 k).2.2.2.2.1
      _ = N*(6*q+1) := by simp

/-- For positive total weight, the total sampler bit cost is at most `N*Nat.clog 2 W*R` and the
total comparison cost is at most `N*L*R`, where `W` is the total weight. -/
theorem localPauliQdrift_sampler_cost {L : ℕ} (b N R : ℕ) (a : Fin L → ℚ) (j0 : Fin L)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))))
    (hW : 0 < weightTotal (dyadicWeights b a)) :
    (∑ i : Fin N, (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).2.1) ≤
      N * Nat.clog 2 (weightTotal (dyadicWeights b a)) * R ∧
    (∑ i : Fin N, (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).2.2) ≤ N*L*R := by
  constructor
  · calc _ ≤ ∑ _ : Fin N, Nat.clog 2 (weightTotal (dyadicWeights b a))*R :=
          Finset.sum_le_sum fun i _ =>
            (fair_bit_qdrift_actual_coin_path_cost L R (dyadicWeights b a) j0 hW).1 (ω i) |>.1
        _ = _ := by simp [Nat.mul_assoc]
  · calc _ ≤ ∑ _ : Fin N, L*R := Finset.sum_le_sum fun i _ =>
          (fair_bit_qdrift_actual_coin_path_cost L R (dyadicWeights b a) j0 hW).1 (ω i) |>.2
        _ = _ := by simp [Nat.mul_assoc]

/-- A Pauli string has no selected target exactly when its support is not nonempty. -/
private theorem pauliTarget_none_iff (q : ℕ) (v : Fin q → Fin 4) :
    pauliStringTarget q v = none ↔ ¬(pauliStringSupport q v).Nonempty := by
  constructor
  · intro ht
    rw [← Finset.card_pos] at *
    rw [(pauliStringTarget_none q v ht).2]
    simp
  · intro hs
    cases ht : pauliStringTarget q v with
    | none => rfl
    | some w => exact False.elim (hs ⟨w,pauliStringTarget_mem q v w ht⟩)

/-- A selected nonempty Pauli support has phase counts `(k, 4*k+3, 2*k+2, 3)`, while an empty
support has zero counts. -/
private theorem selectedArithmetic_actual {L : ℕ} (q b N k : ℕ) (a : Fin L → ℚ)
    (v : Fin L → Fin q → Fin 4) (t : ℚ) (j : Fin L) :
    localPauliSelectedArithmetic q b N k a v t j =
      if (pauliStringSupport q (v j)).Nonempty then (k,4*k+3,2*k+2,3) else (0,0,0,0) := by
  cases ht : pauliStringTarget q (v j) with
  | none => simp [localPauliSelectedArithmetic,ht,(pauliTarget_none_iff q (v j)).mp ht]
  | some w =>
    have hs : (pauliStringSupport q (v j)).Nonempty := ⟨w,pauliStringTarget_mem q (v j) w ht⟩
    simp only [localPauliSelectedArithmetic,ht,if_pos hs]
    exact (localPauliPhaseData_value_counts _ k).2

/-- For positive total weight, the path phase counts are `(m*k, m*(4*k+3), m*(2*k+2), 3*m)`,
where `m` counts selections with nonempty support. All counts vanish when the total weight
is zero. -/
theorem localPauliPhaseArithmetic_actual {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (v : Fin L → Fin q → Fin 4) (t : ℚ)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))) :
    let m := (Finset.univ.filter (fun i : Fin N =>
      (pauliStringSupport q (v (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1)).Nonempty)).card
    localPauliPhaseArithmetic q b N R k a j0 v t ω =
      if weightTotal (dyadicWeights b a) = 0 then (0,0,0,0) else
        (m*k,m*(4*k+3),m*(2*k+2),3*m) := by
  classical
  (try dsimp only)
  unfold localPauliPhaseArithmetic
  split_ifs with hW
  · rfl
  · simp only [selectedArithmetic_actual]
    rw [Finset.sum_ite]
    simp [Finset.sum_const,Nat.mul_comm]

/-- Sampled local Pauli paths satisfy legality, zero-query, gate-count, and phase-arithmetic
formulas. Zero total weight gives an empty program and leaves every reference input
unchanged. -/
theorem local_pauli_qdrift_actual_paths_arithmetic_and_zero :
    ∀ (L q b N R k : ℕ) (a : Fin L → ℚ) (j0 : Fin L)
      (v : Fin L → Fin q → Fin 4) (t : ℚ)
      (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))),
      let gs := localPauliQdriftSteps q b N R k a j0 v t ω
      let W := weightTotal (dyadicWeights b a)
      let j := fun i : Fin N => (fairQdriftPick (dyadicWeights b a) j0 R (ω i)).1
      let m :=
          (Finset.univ.filter (fun i : Fin N => (pauliStringSupport q (v (j i))).Nonempty)).card
      reflectionLegal gs ∧ QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = (if W = 0 then 0 else ∑ i : Fin N, localPauliGateCost q (v (j i))) ∧
      GateCount (reflectionCompile gs) ≤ N*(6*q+1) ∧
      localPauliPhaseArithmetic q b N R k a j0 v t ω =
        (if W = 0 then (0,0,0,0) else (m*k,m*(4*k+3),m*(2*k+2),3*m)) ∧
      (W = 0 → gs = [] ∧ ∀ (r : ℕ)
        (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ),
        localPauliQdriftOutput q b N R k a j0 v t r X = X) := by
  intro L q b N R k a j0 v t ω
  (try dsimp only)
  have hp := localPauliQdrift_path_gates q b N R k a j0 v t ω
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,localPauliPhaseArithmetic_actual q b N R k a j0 v t ω,?_⟩
  intro hW
  simp [localPauliQdriftSteps,localPauliQdriftOutput,hW]

/-- Relabeling finite matrices by an equivalence preserves multiplication. -/
private theorem local_relabel_mul {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A*B) = relabelGate e A * relabelGate e B := by
  simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_mul_equiv]

/-- A left fold that multiplies successive matrices on the left equals the fold starting at
identity followed by the initial matrix. -/
private theorem local_fold_init {D : ℕ} (ms : List (Operator D)) (X : Operator D) :
    ms.foldl (fun A B => B*A) X = ms.foldl (fun A B => B*A) 1 * X := by
  have h : ∀ (A B : Operator D), ms.foldl (fun X Y => Y*X) (A*B) =
      ms.foldl (fun X Y => Y*X) A * B := by
    induction ms with
    | nil => intro A B; rfl
    | cons M ms ih =>
      intro A B
      rw [List.foldl_cons,List.foldl_cons,← mul_assoc,ih]
  simpa using h 1 X

/-- The relabeled matrix of a flattened reflection program equals the ordered product of the
relabeled matrices of its component words. -/
private theorem reflection_flatten_matrix (q : ℕ) (words : List (List (ReflectionGate q))) :
    relabelGate (bitVecEquiv q) (reflectionProgramMatrix words.flatten) =
      (words.map (fun word => relabelGate (bitVecEquiv q) (reflectionProgramMatrix word))).foldl
        (fun A B => B*A) 1 := by
  induction words with
  | nil =>
    ext x y
    simp [reflectionProgramMatrix,relabelGate,Matrix.one_apply]
  | cons word words ih =>
    rw [List.flatten_cons,reflectionProgramMatrix_append,local_relabel_mul,ih,
      List.map_cons,List.foldl_cons]
    simp only [mul_one]
    exact (local_fold_init _ _).symm

/-- For positive total weight, the compiled path matrix equals the mixture path operator of the
individually sampled rational Pauli circuits. -/
theorem localPauliQdrift_path_matrix {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (v : Fin L → Fin q → Fin 4) (t : ℚ)
    (ω : Fin N → Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))))
    (hW : 0 < weightTotal (dyadicWeights b a)) :
    relabelGate (bitVecEquiv q)
      (reflectionProgramMatrix (localPauliQdriftSteps q b N R k a j0 v t ω)) =
      mixturePathOperator (fun bits =>
        let j := (fairQdriftPick (dyadicWeights b a) j0 R bits).1
        relabelGate (bitVecEquiv q)
          (reflectionProgramMatrix (localPauliRationalSteps q (v j) (localPauliQdriftAngle b N a t j) k))) ω := by
  rw [localPauliQdriftSteps,if_neg (ne_of_gt hW),reflection_flatten_matrix,List.map_ofFn]
  rfl

/-- For positive total weight, averaging local Pauli circuit paths equals iterating the one-step
reference mixture `N` times. -/
theorem localPauliQdrift_fresh_bridge {L : ℕ} (q b N R k : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (v : Fin L → Fin q → Fin 4) (t : ℚ) (r : ℕ)
    (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ)
    (hW : 0 < weightTotal (dyadicWeights b a)) :
    localPauliQdriftOutput q b N R k a j0 v t r X =
      referenceMixturePower (fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))))
        (fun bits =>
          let j := (fairQdriftPick (dyadicWeights b a) j0 R bits).1
          relabelGate (bitVecEquiv q) (reflectionProgramMatrix
            (localPauliRationalSteps q (v j) (localPauliQdriftAngle b N a t j) k))) r N X := by
  rw [mixture_fresh_paths_reference_output,localPauliQdriftOutput,if_neg (ne_of_gt hW)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [localPauliQdrift_path_matrix q b N R k a j0 v t ω hW]

/-- The trace norm of a finite sum of matrices is at most the sum of their trace norms. -/
private theorem local_traceNorm_sum {J I : Type} [Fintype I] [DecidableEq I]
    (s : Finset J) (F : J → Matrix I I ℂ) :
    Matrix.traceNorm (∑ j ∈ s,F j) ≤ ∑ j ∈ s,Matrix.traceNorm (F j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    exact (Matrix.traceNorm_add_le _ _).trans (add_le_add (le_refl _) ih)

/-- A uniform reference trace norm error bound for all branches also bounds their mixture with
the same factor. -/
private theorem local_reference_mixture_error {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (d : FinDist J) (U V : J → Operator D) (r : ℕ) (ε : ℝ)
    (hbranch : ∀ j (Y : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (TensorGate (U j) (1 : Operator r)*Y*(TensorGate (U j) (1 : Operator r))ᴴ -
        TensorGate (V j) (1 : Operator r)*Y*(TensorGate (V j) (1 : Operator r))ᴴ) ≤
          ε*Matrix.traceNorm Y)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixture d U r X - referenceMixture d V r X) ≤ ε*Matrix.traceNorm X := by
  rw [referenceMixture_apply,referenceMixture_apply,← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  refine (local_traceNorm_sum _ _).trans ?_
  calc
    _ ≤ ∑ j, d.prob j*(ε*Matrix.traceNorm X) := by
      apply Finset.sum_le_sum
      intro j _
      rw [Matrix.traceNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (d.nonneg j)]
      exact mul_le_mul_of_nonneg_left (hbranch j X) (d.nonneg j)
    _ = _ := by rw [← Finset.sum_mul,d.sum_one,one_mul]

/-- For unitary branches and nonnegative `ε`, a uniform one-step branch error of `ε` yields an
`n`-step mixture error of at most `n*ε*Matrix.traceNorm X`. -/
private theorem local_reference_iterated_error {J : Type} [Fintype J] [DecidableEq J]
    {D : ℕ} (d : FinDist J) (U V : J → Operator D) (r n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hU : ∀ j,U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hV : ∀ j,V j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hbranch : ∀ j (Y : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (TensorGate (U j) (1 : Operator r)*Y*(TensorGate (U j) (1 : Operator r))ᴴ -
        TensorGate (V j) (1 : Operator r)*Y*(TensorGate (V j) (1 : Operator r))ᴴ) ≤
          ε*Matrix.traceNorm Y)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixturePower d U r n X-referenceMixturePower d V r n X) ≤
      n*ε*Matrix.traceNorm X := by
  induction n with
  | zero => simp [referenceMixturePower]
  | succ n ih =>
    let A := referenceMixturePower d U r n X
    let B := referenceMixturePower d V r n X
    have hs : referenceMixture d U r A - referenceMixture d V r B =
        referenceMixture d U r (A-B) + (referenceMixture d U r B-referenceMixture d V r B) := by
      rw [referenceMixture_sub]
      abel
    rw [show referenceMixturePower d U r (n+1) X = referenceMixture d U r A from
      Function.iterate_succ_apply' _ n X,
      show referenceMixturePower d V r (n+1) X = referenceMixture d V r B from
      Function.iterate_succ_apply' _ n X,hs]
    have h1 := (finite_reference_mixture_contraction d U r (A-B) hU).trans ih
    have h2 := local_reference_mixture_error d U V r ε hbranch B
    have h2' :=
        h2.trans (mul_le_mul_of_nonneg_left (referenceMixturePower_contraction d V r n X hV) hε)
    exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2')).trans_eq (by push_cast; ring)

/-- Evolution under a signed dyadic Pauli term at the common qDRIFT time equals evolution under
the unsigned Pauli string at `localPauliQdriftAngle`. -/
private theorem pauli_signed_angle {L : ℕ} (q b N : ℕ) (a : Fin L → ℚ)
    (v : Fin L → Fin q → Fin 4) (t : ℚ) (j : Fin L) :
    HamiltonianEvolution (dyadicSignedTerms b a (fun j => pauliStringMatrix q (v j)) j)
      ((t:ℝ)/(2:ℝ)^b*(weightTotal (dyadicWeights b a):ℝ)/(N:ℝ)) =
      HamiltonianEvolution (pauliStringMatrix q (v j)) (localPauliQdriftAngle b N a t j : ℝ) := by
  unfold dyadicSignedTerms localPauliQdriftAngle
  split_ifs with hsign
  · have hs := quantized_evolution_scale (pauliStringMatrix q (v j))
      ((t:ℝ)/(2:ℝ)^b*(weightTotal (dyadicWeights b a):ℝ)/(N:ℝ)) (-1)
    simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul] at hs
    rw [hs]
    congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- The common qDRIFT angle bound implies `|2*localPauliQdriftAngle b N a t j| ≤ 1` for every
component. -/
private theorem pauli_angle_bound {L : ℕ} (b N : ℕ) (a : Fin L → ℚ) (t : ℚ)
    (j : Fin L) (h : |2*t*(weightTotal (dyadicWeights b a):ℚ)/((2:ℚ)^b*N)| ≤ 1) :
    |(2*localPauliQdriftAngle b N a t j : ℚ)| ≤ 1 := by
  unfold localPauliQdriftAngle
  split_ifs <;> convert h using 1 <;> ring_nf
  rw [abs_neg]

/-- For positive total weight, the ideal quantized Pauli qDRIFT output equals the iterated
fair-bit mixture of exact Pauli evolutions at the selected signed angles. -/
private theorem pauli_raw_ideal_bridge {L : ℕ} (q b N R : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (v : Fin L → Fin q → Fin 4) (t : ℚ) (r : ℕ)
    (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ)
    (hW : 0 < weightTotal (dyadicWeights b a)) :
    quantizedQdriftOutput b a j0 N R (fun j => pauliStringMatrix q (v j)) (t:ℝ) r X =
      referenceMixturePower (fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a)))))
        (fun bits =>
          let j := (fairQdriftPick (dyadicWeights b a) j0 R bits).1
          HamiltonianEvolution (pauliStringMatrix q (v j)) (localPauliQdriftAngle b N a t j : ℝ)) r N X := by
  rw [quantizedQdriftOutput,fairQdriftReferenceOutput,if_neg (ne_of_gt hW),mixture_fresh_paths_reference_output]
  simp only [pauli_signed_angle]

/-- Under positive total weight and the angle bound, replacing exact phases by rational phases
causes trace norm error at most `2*N*(1/2)^k*Matrix.traceNorm X`. -/
theorem localPauliQdrift_phase_error {L : ℕ} (q b N R k r : ℕ) (a : Fin L → ℚ)
    (j0 : Fin L) (v : Fin L → Fin q → Fin 4) (t : ℚ)
    (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ)
    (hW : 0 < weightTotal (dyadicWeights b a))
    (hangle : |2*t*(weightTotal (dyadicWeights b a):ℚ)/((2:ℚ)^b*N)| ≤ 1) :
    Matrix.traceNorm (localPauliQdriftOutput q b N R k a j0 v t r X -
      quantizedQdriftOutput b a j0 N R (fun j => pauliStringMatrix q (v j)) (t:ℝ) r X) ≤
      2*N*(1/2 : ℝ)^k*Matrix.traceNorm X := by
  rw [localPauliQdrift_fresh_bridge _ _ _ _ _ _ _ _ _ _ _ hW,
    pauli_raw_ideal_bridge q b N R a j0 v t r X hW]
  have hU : ∀ bits : Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))),
      relabelGate (bitVecEquiv q) (reflectionProgramMatrix
        (localPauliRationalSteps q (v (fairQdriftPick (dyadicWeights b a) j0 R bits).1)
          (localPauliQdriftAngle b N a t (fairQdriftPick (dyadicWeights b a) j0 R bits).1) k)) ∈
        Matrix.unitaryGroup (Fin (2^q)) ℂ := by
    intro bits
    rw [relabelGate_mem_unitaryGroup]
    exact reflectionProgramMatrix_unitary _ (localPauliSteps_legal _ _ _ _).2
  have hV : ∀ bits : Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))),
      HamiltonianEvolution (pauliStringMatrix q (v (fairQdriftPick (dyadicWeights b a) j0 R bits).1))
        (localPauliQdriftAngle b N a t (fairQdriftPick (dyadicWeights b a) j0 R bits).1 : ℝ) ∈
        Matrix.unitaryGroup (Fin (2^q)) ℂ := by
    intro bits
    exact hamiltonianEvolution_unitary (local_pauli_string_contract_and_support q _).1 _
  have he := local_reference_iterated_error
    (fairQdriftUniform (Fin R → Reg (Nat.clog 2 (weightTotal (dyadicWeights b a))))) _ _ r N (2*(1/2 : ℝ)^k) (by positivity) hU hV
    (fun bits Y => local_pauli_rational_actual_reference_error q _ _ k r Y
      (pauli_angle_bound b N a t _ hangle)) X
  exact he.trans_eq (by ring)

/-- Under the stated positive-weight, step, coefficient, and angle assumptions, the implemented
reference output has error at most the sum of the qDRIFT, sampling, phase, and coefficient
error terms, multiplied by `Matrix.traceNorm X`. -/
theorem local_quantized_pauli_qdrift_actual_total_error :
    ∀ (L q b N R k r : ℕ) (a : Fin L → ℚ) (h : Fin L → ℝ) (j0 : Fin L)
      (v : Fin L → Fin q → Fin 4) (t : ℚ) (δ : ℝ)
      (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ),
      0 < N → 0 < weightTotal (dyadicWeights b a) →
      (∑ j, |h j-(a j:ℝ)|) ≤ δ →
      |2*t*(weightTotal (dyadicWeights b a):ℚ)/((2:ℚ)^b*N)| ≤ 1 →
      let W := (weightTotal (dyadicWeights b a):ℝ)/(2:ℝ)^b
      let V := TensorGate (HamiltonianEvolution (∑ j,(h j:ℂ) • pauliStringMatrix q (v j)) (t:ℝ))
        (1 : Operator r)
      Matrix.traceNorm (localPauliQdriftOutput q b N R k a j0 v t r X - V*X*Vᴴ) ≤
        (4*W^2*(t:ℝ)^2/(N:ℝ)+2*N*(1/2:ℝ)^R+2*N*(1/2:ℝ)^k+
          2*|(t:ℝ)| *(δ+(L:ℝ)/(2:ℝ)^(b+1)))*Matrix.traceNorm X := by
  intro L q b N R k r a h j0 v t δ X hN hW ha hangle
  (try dsimp only)
  have hK : ∀ j, (pauliStringMatrix q (v j)).IsHermitian ∧ ‖pauliStringMatrix q (v j)‖ ≤ 1 := by
    intro j
    have hc := local_pauli_string_contract_and_support q (v j)
    exact ⟨hc.1,hc.2.2.1.le⟩
  have hp := localPauliQdrift_phase_error q b N R k r a j0 v t X hW hangle
  have hq := quantized_qdrift_actual_reference_error L (2^q) b N R r a h j0
    (fun j => pauliStringMatrix q (v j)) (t:ℝ) δ X hN hW hK ha
  have ht := Matrix.traceNorm_add_le
    (localPauliQdriftOutput q b N R k a j0 v t r X -
      quantizedQdriftOutput b a j0 N R (fun j => pauliStringMatrix q (v j)) (t:ℝ) r X)
    (quantizedQdriftOutput b a j0 N R (fun j => pauliStringMatrix q (v j)) (t:ℝ) r X -
      TensorGate (HamiltonianEvolution (∑ j,(h j:ℂ) • pauliStringMatrix q (v j)) (t:ℝ))
        (1 : Operator r)*X*
      (TensorGate (HamiltonianEvolution (∑ j,(h j:ℂ) • pauliStringMatrix q (v j)) (t:ℝ))
        (1 : Operator r))ᴴ)
  rw [sub_add_sub_cancel] at ht
  exact (ht.trans (add_le_add hp hq)).trans_eq (by ring)

/-- The explicit choices `N = max 1 (16*W^2*T^2*2^s)` and `K = s+Nat.clog 2 (max 1 N)+3` give a
positive step count, the angle bound, and the two stated quarter-budget estimates when `W >
0` and `|t| ≤ T`. -/
private theorem local_pauli_scalar_budget (W b T s : ℕ) (t : ℝ)
    (hW : 0 < W) (ht : |t| ≤ T) :
    let N := max 1 (16*W^2*T^2*2^s)
    let K := s+Nat.clog 2 (max 1 N)+3
    0 < N ∧ |2*t*(W:ℝ)/((2:ℝ)^b*N)| ≤ 1 ∧
    4*((W:ℝ)/(2:ℝ)^b)^2*t^2/(N:ℝ) ≤ (1/2:ℝ)^s/4 ∧
    2*N*(1/2:ℝ)^K ≤ (1/2:ℝ)^s/4 := by
  let N := max 1 (16*W^2*T^2*2^s)
  let c := Nat.clog 2 (max 1 N)
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hWr : 0 < (W:ℝ) := by exact_mod_cast hW
  have hp : (1:ℝ) ≤ 2^b := one_le_pow₀ (by norm_num)
  have hpn : 0 < (2:ℝ)^b*(N:ℝ) := by positivity
  have hl : 16*(W:ℝ)^2*(T:ℝ)^2*(2:ℝ)^s ≤ (N:ℝ) := by
    exact_mod_cast Nat.le_max_right 1 (16*W^2*T^2*2^s)
  have hc : (N:ℝ) ≤ (2:ℝ)^c := by
    exact_mod_cast (Nat.le_max_right 1 N).trans (Nat.le_pow_clog (by decide) (max 1 N))
  have htt : t^2 ≤ (T:ℝ)^2 := by
    simpa only [← sq,sq_abs] using mul_self_le_mul_self (abs_nonneg t) ht
  have hscale : (W:ℝ)/(2:ℝ)^b ≤ W := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa using mul_le_mul_of_nonneg_left hp (le_of_lt hWr)
  refine ⟨hN,?_,?_,?_⟩
  · have hbase : 2*(W:ℝ)*(T:ℝ) ≤ (N:ℝ) := by
      by_cases hT : T = 0
      · simp [hT,hNr.le]
      · have hTr : 1 ≤ (T:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
        have hWr1 : 1 ≤ (W:ℝ) := by exact_mod_cast hW
        have hwt : 1 ≤ (W:ℝ)*(T:ℝ) := by nlinarith
        have hs : (1:ℝ) ≤ 2^s := one_le_pow₀ (by norm_num)
        calc
          2*(W:ℝ)*(T:ℝ) ≤ 16*(W:ℝ)^2*(T:ℝ)^2 := by nlinarith
          _ ≤ 16*(W:ℝ)^2*(T:ℝ)^2*(2:ℝ)^s := by
            simpa using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16*(W:ℝ)^2*(T:ℝ)^2)
          _ ≤ _ := hl
    rw [abs_div,abs_of_pos hpn,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_pos hWr]
    apply (div_le_iff₀ hpn).mpr
    simp only [one_mul]
    calc
      2*|t| *(W:ℝ) ≤ 2*(T:ℝ)*(W:ℝ) := by gcongr
      _ ≤ (N:ℝ) := by simpa [mul_comm,mul_left_comm] using hbase
      _ ≤ (2:ℝ)^b*(N:ℝ) := by simpa using mul_le_mul_of_nonneg_right hp hNr.le
  · apply (div_le_iff₀ hNr).mpr
    calc
      4*((W:ℝ)/(2:ℝ)^b)^2*t^2 ≤ 4*(W:ℝ)^2*(T:ℝ)^2 := by gcongr
      _ = ((1/2:ℝ)^s/4)*(16*(W:ℝ)^2*(T:ℝ)^2*2^s) := by
        simp only [one_div,inv_pow]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  · change 2*(N:ℝ)*(1/2:ℝ)^(s+c+3) ≤ _
    rw [pow_add,pow_add]
    calc
      _ ≤ 2*(2:ℝ)^c*((1/2:ℝ)^s*(1/2:ℝ)^c*(1/2:ℝ)^3) := by gcongr
      _ = _ := by
        simp only [one_div,inv_pow]
        field_simp
        norm_num

/-- Under the coefficient quarter-budget and time bound, the computed step count and common
sampling and phase precision give reference trace norm error at most
`(1/2)^s*Matrix.traceNorm X`. -/
theorem local_pauli_qdrift_computed_finite_precision_budget :
    ∀ (L q b T s r : ℕ) (a : Fin L → ℚ) (h : Fin L → ℝ) (j0 : Fin L)
      (v : Fin L → Fin q → Fin 4) (t : ℚ) (δ : ℝ)
      (X : Matrix (Fin (2^q) × Fin r) (Fin (2^q) × Fin r) ℂ),
      0 < weightTotal (dyadicWeights b a) → |(t:ℝ)| ≤ T →
      (∑ j,|h j-(a j:ℝ)|) ≤ δ →
      2*(T:ℝ)*(δ+(L:ℝ)/(2:ℝ)^(b+1)) ≤ (1/2:ℝ)^s/4 →
      let W := weightTotal (dyadicWeights b a)
      let N := max 1 (16*W^2*T^2*2^s)
      let K := s+Nat.clog 2 (max 1 N)+3
      let V := TensorGate (HamiltonianEvolution (∑ j,(h j:ℂ) • pauliStringMatrix q (v j)) (t:ℝ))
        (1 : Operator r)
      Matrix.traceNorm (localPauliQdriftOutput q b N K K a j0 v t r X-V*X*Vᴴ) ≤
        (1/2:ℝ)^s*Matrix.traceNorm X := by
  intro L q b T s r a h j0 v t δ X hW ht ha hprecision
  (try dsimp only)
  let W := weightTotal (dyadicWeights b a)
  let N := max 1 (16*W^2*T^2*2^s)
  let K := s+Nat.clog 2 (max 1 N)+3
  have hb := local_pauli_scalar_budget W b T s (t:ℝ) hW ht
  have hangle : |2*t*(W:ℚ)/((2:ℚ)^b*N)| ≤ 1 := by
    exact_mod_cast hb.2.1
  have herr := local_quantized_pauli_qdrift_actual_total_error L q b N K K r a h j0 v t δ X
    hb.1 hW ha hangle
  have hδ : 0 ≤ δ := (Finset.sum_nonneg (fun j _ => abs_nonneg (h j-(a j:ℝ)))).trans ha
  have hcoeff : 2*|(t:ℝ)| *(δ+(L:ℝ)/(2:ℝ)^(b+1)) ≤ (1/2:ℝ)^s/4 := by
    calc
      _ ≤ 2*(T:ℝ)*(δ+(L:ℝ)/(2:ℝ)^(b+1)) := by gcongr
      _ ≤ _ := hprecision
  refine herr.trans (mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg X))
  linarith [hb.2.2.1,hb.2.2.2]

end Qatlib.Concepts.RandCompile.ReferenceModel
