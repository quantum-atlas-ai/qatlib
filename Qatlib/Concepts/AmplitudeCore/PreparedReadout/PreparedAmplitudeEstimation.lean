/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.LchsSimulation.StaticLchs.ReadoutError

/-!
# Prepared amplitude estimation

`AEAccessStep` and `countedAECircuit` expand amplitude estimation into explicit preparation,
inverse preparation, source-reflection, marking, and fixed-gate operations. `aeLaw` is the
actual counter-label Born distribution, and `aeEstimate` decodes a label as a squared sine.

The module proves the two-eigenphase distribution, the BHMT error guarantee and endpoint
behavior, exact access ledgers, and a noisy controlled-access success bound. The
amplitude-estimation construction follows [BrassardEtAl2002].

## Main statements

* `prepared_ae_access_ledger`: gives the expanded query, gate, and preparation counts.
* `prepared_ae_two_phase_distribution`: expresses the interior counter law as an equal two-phase
  mixture.
* `prepared_ae_bhmt_error_and_endpoints`: proves the error guarantee and exact endpoint cases.

## References

* [Brassard et al., 2002, Theorem 12][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator
set_option autoImplicit false
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The access vocabulary for expanded amplitude estimation, distinguishing initialization,
preparation directions, source reflection, marking, and fixed gates. -/
inductive AEAccessStep (R : Type) where
  | initialize
  | prepareForward
  | prepareBackward
  | sourceReflection
  | mark
  | fixed (U : Matrix R R ℂ)

/-- Expand an iterate query into marking, inverse preparation, source reflection, and forward
preparation; retain a fixed gate as one access step. -/
def expandAEAccess {R : Type} : Step R → List (AEAccessStep R)
  | .query => [.mark, .prepareBackward, .sourceReflection, .prepareForward]
  | .gate U => [.fixed U]

/-- The controlled system gate with an identity spectator on the phase counter. -/
noncomputable def aeControlledGate (M : ℕ) (U : Matrix I I ℂ) :
    Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ :=
  TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle U)

/-- Interpret an amplitude-estimation access step as a gate or marking query on the counter,
flag, and system registers. -/
noncomputable def aeAccessInstruction (M : ℕ) (A : Matrix I I ℂ) (j : I) :
    AEAccessStep (Fin M × (Bool × I)) → Step (Fin M × (Bool × I))
  | .initialize => .gate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))
  | .prepareForward => .gate (aeControlledGate M A)
  | .prepareBackward => .gate (aeControlledGate M Aᴴ)
  | .sourceReflection => .gate (aeControlledGate M (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j))))
  | .mark => .query
  | .fixed U => .gate U

/-- The phase-estimation access word expanded into preparation and reflection operations, with
an initial preparation step. -/
noncomputable def aeAccessWord (M : ℕ) : List (AEAccessStep (Fin M × (Bool × I))) :=
  .initialize :: (countedPhaseCircuit (I := I) M).flatMap expandAEAccess

/-- The circuit obtained by interpreting `aeAccessWord` using preparation matrix `A` and seed
`j`. -/
noncomputable def countedAECircuit (M : ℕ) (A : Matrix I I ℂ) (j : I) :
    Circuit (Fin M × (Bool × I)) :=
  (aeAccessWord (I := I) M).map (aeAccessInstruction M A j)

/-- Count initialization and forward or backward preparation accesses in an amplitude-estimation
word. -/
def aeInputAccesses {R : Type} (w : List (AEAccessStep R)) : ℕ :=
  (w.map (fun s => match s with
    | .initialize | .prepareForward | .prepareBackward => 1
    | _ => 0)).sum

/-- Count source-reflection steps in an amplitude-estimation word. -/
def aeSourceReflections {R : Type} (w : List (AEAccessStep R)) : ℕ :=
  (w.map (fun s => match s with | .sourceReflection => 1 | _ => 0)).sum

/-- The amplitude estimate `sin²(π z / M)` decoded from a phase-counter label. -/
noncomputable def aeEstimate (M : ℕ) (z : Fin M) : ℝ :=
  (Real.sin (Real.pi*(z.val : ℝ)/(M : ℝ)))^2

/-- The controlled counter lift preserves matrix multiplication. -/
private theorem aeControlledGate_mul (M : ℕ) (U V : Matrix I I ℂ) :
    aeControlledGate M U * aeControlledGate M V = aeControlledGate M (U*V) := by
  rw [aeControlledGate, aeControlledGate, tensorGate_mul, Matrix.one_mul, controlOracle_mul]
  rfl

/-- Running the expanded accesses with the marking oracle equals running the original circuit
with the prepared amplification iterate. -/
private theorem run_expandedAE (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (C : Circuit (Fin M × (Bool × I))) (ψ : QState (Fin M × (Bool × I))) :
    Run (aeControlledGate M (preparedMark S))
        ((C.flatMap expandAEAccess).map (aeAccessInstruction M A j)) ψ =
      Run (aeControlledGate M (preparedAAIterate A j S)) C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simpa [expandAEAccess, aeAccessInstruction, Run] using ih (ApplyGate U ψ)
    | query =>
      simp only [List.flatMap_cons, expandAEAccess, List.map_cons,
        List.cons_append, List.nil_append, aeAccessInstruction, Run]
      rw [ih]
      congr 1
      rw [← applyGate_mul, ← applyGate_mul, ← applyGate_mul,
        aeControlledGate_mul, aeControlledGate_mul, aeControlledGate_mul]
      rfl

omit [Fintype I] in

/-- Expansion preserves the query count, adds three gates per query, and uses two preparation
accesses and one source reflection per query. -/
private theorem expandedAE_counts (M : ℕ) (A : Matrix I I ℂ) (j : I)
    (C : Circuit (Fin M × (Bool × I))) :
    QueryCount ((C.flatMap expandAEAccess).map (aeAccessInstruction M A j)) = QueryCount C ∧
    GateCount ((C.flatMap expandAEAccess).map (aeAccessInstruction M A j)) =
      GateCount C+3*QueryCount C ∧
    aeInputAccesses (C.flatMap expandAEAccess) = 2*QueryCount C ∧
    aeSourceReflections (C.flatMap expandAEAccess) = QueryCount C := by
  induction C with
  | nil => simp [aeInputAccesses, aeSourceReflections]
  | cons s C ih =>
    cases s <;>
      simp [expandAEAccess, aeAccessInstruction, aeInputAccesses, aeSourceReflections,
        ih.1, ih.2.1] at * <;> omega

/-- The controlled counter lift of a unitary matrix is unitary. -/
private theorem aeControlledGate_unitary (M : ℕ) {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    aeControlledGate M U ∈ Matrix.unitaryGroup (Fin M × (Bool × I)) ℂ :=
  tensorGate_unitary (by simp) (controlOracle_unitary hU)

/-- Expanding a unitary circuit through a unitary preparation matrix produces a unitary circuit. -/
private theorem expandedAE_unitary (M : ℕ) (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (C : Circuit (Fin M × (Bool × I)))
    (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit ((C.flatMap expandAEAccess).map (aeAccessInstruction M A j)) := by
  induction C with
  | nil => simp
  | cons s C ih =>
    cases s with
    | gate U =>
      simp only [isUnitaryCircuit_gate] at hC
      simpa [expandAEAccess, aeAccessInstruction] using
        (isUnitaryCircuit_gate U _).mpr ⟨hC.1, ih hC.2⟩
    | query =>
      simp only [isUnitaryCircuit_query] at hC
      simp [expandAEAccess, aeAccessInstruction, ih hC,
        aeControlledGate_unitary M hA,
        aeControlledGate_unitary M (conjTranspose_mem_unitaryGroup hA),
        aeControlledGate_unitary M (outerProduct_reflection_unitary (normalized_ket j))]

/-- The prepared circuit uses `M - 1` marking queries, `5 * (M - 1) + 3` gates, `2 * (M - 1) +
1` preparation accesses, and `M - 1` source reflections. -/
theorem prepared_ae_access_ledger (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (countedAECircuit M A j) = M-1 ∧
    GateCount (countedAECircuit M A j) = 5*(M-1)+3 ∧
    aeInputAccesses (aeAccessWord (I := I) M) = 2*(M-1)+1 ∧
    aeSourceReflections (aeAccessWord (I := I) M) = M-1 := by
  have hC := (counted_offgrid_qpe_clean_flag M hM A (Qatlib.Foundations.PureStateMath.Ket j)).2
  have he := expandedAE_counts M A j (countedPhaseCircuit M)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [countedAECircuit, aeAccessWord, List.map_cons, aeAccessInstruction,
      queryCount_gate, he.1, hC.1]
  · simp only [countedAECircuit, aeAccessWord, List.map_cons, aeAccessInstruction,
      gateCount_gate, he.2.1, hC.1, hC.2.1]
    omega
  · have hi : aeInputAccesses (aeAccessWord (I := I) M) =
        1 + aeInputAccesses ((countedPhaseCircuit (I := I) M).flatMap expandAEAccess) := by
      simp [aeAccessWord, aeInputAccesses]
    rw [hi, he.2.2.1, hC.1]
    omega
  · have hr : aeSourceReflections (aeAccessWord (I := I) M) =
        aeSourceReflections ((countedPhaseCircuit (I := I) M).flatMap expandAEAccess) := by
      simp [aeAccessWord, aeSourceReflections]
    rw [hr, he.2.2.2, hC.1]

/-- For a positive counter size and unitary preparation, the counted amplitude-estimation
circuit is unitary. -/
private theorem countedAECircuit_unitary (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ)
    (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) : IsUnitaryCircuit (countedAECircuit M A j) := by
  apply (isUnitaryCircuit_gate _ _).mpr
  exact ⟨tensorGate_unitary (by simp) (tensorGate_unitary (by simp) hA),
    expandedAE_unitary M A j hA _ (counted_offgrid_qpe_clean_flag M hM A (Qatlib.Foundations.PureStateMath.Ket j)).2.2.2⟩

/-- The counted amplitude-estimation output equals the flag embedding of phase estimation on the
prepared amplification iterate. -/
theorem countedAE_output (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) (S : Finset I) :
    Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))) =
        phaseFlagEmbed M (qpeOutput M (preparedAAIterate A j S) (preparedAAState A j)) := by
  simp only [countedAECircuit, aeAccessWord, List.map_cons, aeAccessInstruction, Run]
  rw [applyGate_tensorGate, applyGate_one, applyGate_tensorGate, applyGate_one]
  rw [run_expandedAE]
  exact (counted_offgrid_qpe_clean_flag M hM (preparedAAIterate A j S)
    (preparedAAState A j)).1

/-- The counted amplitude-estimation output is normalized for a unitary preparation and positive
counter size. -/
private theorem normalized_countedAE_output (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Normalized (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j)))) :=
  (countedAECircuit_unitary M hM A j hA).normalized_run
    (aeControlledGate_unitary M (prepared_aa_reflection_and_access A j S hA).1)
    (normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) (normalized_ket _)))

/-- The finite Born distribution of the counter label in the counted prepared
amplitude-estimation circuit. -/
noncomputable def aeLaw (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) : FinDist (Fin M) where
  prob z := MeasureProb
    (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
    (Finset.univ.filter (fun p => p.1=z))
  nonneg z := measureProb_nonneg _ _
  sum_one := by
    have hn := normalized_countedAE_output M (by omega) A j S hA
    unfold Normalized at hn
    simp only [MeasureProb, Finset.sum_filter, BornProb]
    rw [Finset.sum_comm]
    simpa using hn

/-- The expanded circuit has the stated query and gate counts, is unitary, and produces a
normalized state with counter law `aeLaw` and zero amplitude on flag `true`
[BrassardEtAl2002]. -/
theorem prepared_ae_expanded_access_and_output (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let input :=
        TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M))
        (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))
    let O := TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (preparedMark S))
    let out := Run O (countedAECircuit M A j) input
    QueryCount (countedAECircuit M A j) = M-1 ∧
    GateCount (countedAECircuit M A j) = 5*(M-1)+3 ∧
    IsUnitaryCircuit (countedAECircuit M A j) ∧ Normalized out ∧
    (∀ z : Fin M, (aeLaw M A j S hA hM).prob z =
      MeasureProb out (Finset.univ.filter (fun p => p.1=z))) ∧
    (∀ z i, out (z,(true,i))=0) := by
  have hl := prepared_ae_access_ledger M (by omega) A j
  refine ⟨hl.1, hl.2.1, countedAECircuit_unitary M (by omega) A j hA,
    normalized_countedAE_output M (by omega) A j S hA, fun _ => rfl, ?_⟩
  intro z i
  change Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j) _ (z,true,i) = 0
  rw [countedAE_output]
  rfl

omit [DecidableEq I] in

/-- The inner product of two linear combinations expands into the four pairwise inner products
with conjugated coefficients in the first argument. -/
private theorem aeInner_combination (b g : QState I) (a c d e : ℂ) :
    Qatlib.Foundations.PureStateMath.Inner (a • b+c • g) (d • b+e • g) =
      star a*d*Qatlib.Foundations.PureStateMath.Inner b b+star a*e*Qatlib.Foundations.PureStateMath.Inner b g+star c*d*Qatlib.Foundations.PureStateMath.Inner g b+star c*e*Qatlib.Foundations.PureStateMath.Inner g g := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Swapping the arguments of the complex inner product conjugates its value. -/
private theorem aeInner_swap (b g : QState I) : Qatlib.Foundations.PureStateMath.Inner b g = star (Qatlib.Foundations.PureStateMath.Inner g b) := by
  rw [inner_apply, inner_apply, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, map_mul, starRingEnd_self_apply, mul_comm]

/-- The two candidate amplification eigenvectors formed from the good and bad components of the
prepared state. -/
private noncomputable def aeEigenVector (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (θ : ℝ) (b : Bool) : QState I :=
  ((Real.sqrt 2 : ℂ)*(Real.cos θ : ℂ))⁻¹ •
      (preparedAAState A j-Collapse (preparedAAState A j) S) +
    ((if b then -Complex.I else Complex.I)/((Real.sqrt 2 : ℂ)*(Real.sin θ : ℂ))) •
      Collapse (preparedAAState A j) S

/-- The complex coefficients used to express the prepared state in its two amplification
eigenvectors. -/
private noncomputable def aeEigenCoefficient (θ : ℝ) (b : Bool) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (((if b then θ else -θ : ℝ) : ℂ)*Complex.I)

/-- For nonzero sine and cosine and the stated success probability, the two amplification
eigenvectors are orthonormal. -/
private theorem aeEigenVector_orthonormal (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hs : Real.sin θ ≠ 0)
    (hc : Real.cos θ ≠ 0) (ha : MeasureProb (preparedAAState A j) S=(Real.sin θ)^2) :
    ∀ b c, Qatlib.Foundations.PureStateMath.Inner (aeEigenVector A j S θ b) (aeEigenVector A j S θ c) =
      if b=c then 1 else 0 := by
  let g := Collapse (preparedAAState A j) S
  let b := preparedAAState A j-g
  have hgeo := prepared_aa_good_bad_geometry A j S hA
  have hgg : Qatlib.Foundations.PureStateMath.Inner g g = ((Real.sin θ)^2 : ℝ) := by
    rw [inner_self, ← Complex.ofReal_sum, ← norm_toEuclidean_fromVec_sq]
    rw [hgeo.2.2.1, ha]
  have hbb : Qatlib.Foundations.PureStateMath.Inner b b = ((Real.cos θ)^2 : ℝ) := by
    rw [inner_self, ← Complex.ofReal_sum, ← norm_toEuclidean_fromVec_sq]
    rw [hgeo.2.2.2.1, ha]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hgb : Qatlib.Foundations.PureStateMath.Inner g b = 0 := hgeo.2.1
  have hbg : Qatlib.Foundations.PureStateMath.Inner b g = 0 := by
    rw [aeInner_swap, hgb, star_zero]
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcC : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc
  have hrC : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hr2 : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ)≤2))
  intro v w
  unfold aeEigenVector
  rw [aeInner_combination]
  change _ + _ * Qatlib.Foundations.PureStateMath.Inner b g + _ * Qatlib.Foundations.PureStateMath.Inner g b + _ * Qatlib.Foundations.PureStateMath.Inner g g = _
  rw [hbb,hgg,hbg,hgb]
  cases v <;> cases w <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false,
      Complex.star_def, map_mul, map_inv₀, map_div₀, map_neg, Complex.conj_ofReal,
      Complex.conj_I, mul_zero, add_zero, Complex.ofReal_pow] <;>
    field_simp [hsC,hcC,hrC, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    simp only [Complex.I_sq,hr2] <;> ring

/-- The amplification eigenvectors have eigenphases `θ / π` and `-θ / π` under the stated
preparation and probability hypotheses. -/
private theorem aeEigenVector_eigen (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) (hs : Real.sin θ ≠ 0)
    (hc : Real.cos θ ≠ 0) (ha : MeasureProb (preparedAAState A j) S=(Real.sin θ)^2) :
    ∀ b, ApplyGate (preparedAAIterate A j S) (aeEigenVector A j S θ b) =
      Complex.exp (2*Real.pi*Complex.I*(if b then θ/Real.pi else -θ/Real.pi)) •
        aeEigenVector A j S θ b := by
  have hstep := prepared_aa_two_component_step A j S hA
  dsimp only at hstep
  rw [ha] at hstep
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcC : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc
  have hrC : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have htrig : (Real.sin θ : ℂ)^2+(Real.cos θ : ℂ)^2=1 := by
    exact_mod_cast (Real.sin_sq_add_cos_sq θ)
  have hexp (b : Bool) :
      Complex.exp (2*Real.pi*Complex.I*(if b then θ/Real.pi else -θ/Real.pi)) =
        (Real.cos (2*θ) : ℂ)+(if b then Complex.I else -Complex.I)*(Real.sin (2*θ) : ℂ) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    cases b
    · simp only [Bool.false_eq_true, if_false]
      push_cast
      have he : (2*Real.pi*Complex.I*(-θ/Real.pi) : ℂ) = ((-2*θ : ℝ) : ℂ)*Complex.I := by
        push_cast
        field_simp
      rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        show -2*θ = -(2*θ) by ring, Real.cos_neg, Real.sin_neg]
      simp only [Complex.ofReal_neg]
      push_cast
      ring
    · simp only [if_true]
      push_cast
      have he : (2*Real.pi*Complex.I*(θ/Real.pi) : ℂ) = ((2*θ : ℝ) : ℂ)*Complex.I := by
        push_cast
        field_simp
      rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
  intro b
  rw [hexp]
  unfold aeEigenVector
  have hlin (a c : ℂ) (x y : QState I) :
      ApplyGate (preparedAAIterate A j S) (a • x+c • y) =
        a • ApplyGate (preparedAAIterate A j S) x+c • ApplyGate (preparedAAIterate A j S) y := by
    simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hlin, hstep.1,hstep.2]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.cos_two_mul, Real.sin_two_mul]
  push_cast
  simp only [Complex.ofReal_cos, Complex.ofReal_sin] at hsC hcC htrig ⊢
  cases b <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
    field_simp [hsC,hcC,hrC, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    ring_nf <;> simp only [Complex.I_sq] <;>
    first
    | linear_combination htrig.symm *
        (2*Complex.sin (θ : ℂ)*(preparedAAState A j-Collapse (preparedAAState A j) S) i +
          2*(Complex.sin (θ : ℂ)+Complex.I*Complex.cos (θ : ℂ))*Collapse (preparedAAState A j) S i)
    | linear_combination htrig.symm *
        (2*Complex.sin (θ : ℂ)*(preparedAAState A j-Collapse (preparedAAState A j) S) i +
          2*(Complex.sin (θ : ℂ)-Complex.I*Complex.cos (θ : ℂ))*Collapse (preparedAAState A j) S i)

/-- Each amplification eigenvector coefficient has squared norm `1 / 2`. -/
private theorem aeEigenCoefficient_norm (θ : ℝ) (b : Bool) :
    ‖aeEigenCoefficient θ b‖^2 = 1/2 := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hn (t : ℝ) : ‖Complex.exp ((t : ℂ)*Complex.I)‖=1 := by
    rw [Complex.norm_exp]
    simp
  simp only [aeEigenCoefficient, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr, hn, mul_one, inv_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  norm_num

/-- The weighted sum of the two amplification eigenvectors equals the prepared state when sine
and cosine are nonzero. -/
private theorem aeEigen_decomposition (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (θ : ℝ) (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    (∑ b : Bool, aeEigenCoefficient θ b • aeEigenVector A j S θ b) = preparedAAState A j := by
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcC : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc
  have hrC : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hr2 : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ)≤2))
  rw [Fintype.sum_bool]
  unfold aeEigenCoefficient aeEigenVector
  simp only [if_true, Bool.false_eq_true, if_false, Complex.ofReal_neg,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  simp only [Complex.ofReal_cos,Complex.ofReal_sin] at hsC hcC ⊢
  field_simp [hsC,hcC,hrC]
  ring_nf
  simp only [Complex.I_sq,hr2]
  ring

/-- The counter probability in `aeLaw` equals the corresponding phase-estimation marginal. -/
theorem aeLaw_prob_eq_qpe_marginal (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (z : Fin M) :
    (aeLaw M A j S hA hM).prob z =
      MarginalProbLeft (qpeOutput M (preparedAAIterate A j S) (preparedAAState A j)) {z} := by
  change MeasureProb (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
    (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j)))) _ = _
  rw [countedAE_output]
  simp [MeasureProb, MarginalProbLeft, Finset.sum_filter,
    Fintype.sum_prod_type, phaseFlagEmbed, BornProb]

/-- For an interior amplification angle, the counter law is the equal mixture of the squared
phase-estimation kernels at `θ / π` and `-θ / π` [BrassardEtAl2002]. -/
theorem prepared_ae_two_phase_distribution (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (ha : MeasureProb (preparedAAState A j) S=(Real.sin θ)^2) (z : Fin M) :
    (aeLaw M A j S hA hM).prob z =
      (‖qpeKernel M (θ/Real.pi) z‖^2+‖qpeKernel M (-θ/Real.pi) z‖^2)/2 := by
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ1⟩).ne'
  have h := (offgrid_qpe_eigen_and_spectral_law M (preparedAAIterate A j S)
    (preparedAAState A j) (θ/Real.pi) (by omega)).2 Bool
    (aeEigenVector A j S θ) (aeEigenCoefficient θ)
    (fun b => if b then θ/Real.pi else -θ/Real.pi)
    (by
      intro b c
      have h := aeEigenVector_orthonormal A j S hA θ hs hc ha b c
      by_cases he : b=c <;> simpa only [he, if_true, if_false] using h)
    (aeEigenVector_eigen A j S hA θ hs hc ha) z
  rw [aeEigen_decomposition A j S θ hs hc] at h
  rw [aeLaw_prob_eq_qpe_marginal, h]
  simp_rw [aeEigenCoefficient_norm]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_true, if_false]
  ring

/-- The change in squared sine is bounded by the linear variance term and the squared
displacement. -/
private theorem sin_sq_displacement (θ t : ℝ) :
    |(Real.sin (θ+t))^2-(Real.sin θ)^2| ≤
      2*Real.sqrt ((Real.sin θ)^2*(1-(Real.sin θ)^2))*|t|+t^2 := by
  have hi := Real.sin_sq_add_cos_sq θ
  have ht := Real.abs_sin_le_abs (x := t)
  have hc := Real.abs_cos_le_one t
  have hdiff : |(Real.cos θ)^2-(Real.sin θ)^2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (Real.sin θ),sq_nonneg (Real.cos θ)]
  have he : (Real.sin (θ+t))^2-(Real.sin θ)^2 =
      2*Real.sin θ*Real.cos θ*Real.sin t*Real.cos t+
        ((Real.cos θ)^2-(Real.sin θ)^2)*(Real.sin t)^2 := by
    rw [Real.sin_add]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hsqrt : Real.sqrt ((Real.sin θ)^2*(1-(Real.sin θ)^2)) = |Real.sin θ*Real.cos θ| := by
    rw [show (Real.sin θ)^2*(1-(Real.sin θ)^2) = (Real.sin θ*Real.cos θ)^2 by
      nlinarith only [hi]]
    exact Real.sqrt_sq_eq_abs _
  rw [hsqrt,he]
  calc
    _ ≤ |2*Real.sin θ*Real.cos θ*Real.sin t*Real.cos t|+
        |((Real.cos θ)^2-(Real.sin θ)^2)*(Real.sin t)^2| := abs_add_le _ _
    _ ≤ 2*|Real.sin θ*Real.cos θ| *|t|+t^2 := by
      simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h1 : 2*|Real.sin θ*Real.cos θ| *|Real.sin t| *|Real.cos t| ≤
          2*|Real.sin θ*Real.cos θ| *|t| := by
        calc
          _ ≤ 2*|Real.sin θ*Real.cos θ| *|t| *1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left ht (by positivity)) hc
              (abs_nonneg _) (by positivity)
          _ = _ := by ring
      have h2 : |(Real.cos θ)^2-(Real.sin θ)^2| *|Real.sin t|^2 ≤ t^2 := by
        calc
          _ ≤ 1*|t|^2 := mul_le_mul hdiff (pow_le_pow_left₀ (abs_nonneg _) ht 2)
            (by positivity) (by norm_num)
          _ = _ := by rw [sq_abs,one_mul]
      simpa only [abs_mul,mul_assoc] using add_le_add h1 h2

/-- Adding an integer multiple of π leaves squared sine unchanged. -/
private theorem sin_sq_integer_shift (t : ℝ) (n : ℤ) :
    (Real.sin (t+(n : ℝ)*Real.pi))^2=(Real.sin t)^2 := by
  rw [Real.sin_add_int_mul_pi,mul_pow]
  have hs : ((-1 : ℝ)^n)^2=1 := by
    rw [← sq_abs,abs_zpow]
    norm_num
  rw [hs,one_mul]

/-- A phase label within circular distance `1 / M` yields amplitude error at most `2π
sqrt(a(1-a)) / M + π² / M²`. -/
theorem aeEstimate_error_of_phaseDistance (M : ℕ) (hM : 0 < M) (φ : ℝ) (z : Fin M)
    (hd : phaseDistance φ ((z.val : ℝ)/(M : ℝ)) ≤ 1/(M : ℝ)) :
    let a := (Real.sin (Real.pi*φ))^2
    |aeEstimate M z-a| ≤ 2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+
      Real.pi^2/(M : ℝ)^2 := by
  let c : ℤ := ⌊φ-(z.val : ℝ)/(M : ℝ)+1/2⌋
  let t : ℝ := Real.pi*((z.val : ℝ)/(M : ℝ)-φ+(c : ℝ))
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have he : (Real.sin (Real.pi*φ+t))^2=aeEstimate M z := by
    rw [show Real.pi*φ+t = Real.pi*(z.val : ℝ)/(M : ℝ)+(c : ℝ)*Real.pi by dsimp [t]; ring,
      sin_sq_integer_shift]
    rfl
  have ht : |t|=Real.pi*phaseDistance φ ((z.val : ℝ)/(M : ℝ)) := by
    change |Real.pi*((z.val : ℝ)/(M : ℝ)-φ+(c : ℝ))| =
      Real.pi*|φ-(z.val : ℝ)/(M : ℝ)-(c : ℝ)|
    rw [show Real.pi*((z.val : ℝ)/(M : ℝ)-φ+(c : ℝ)) =
      -Real.pi*(φ-(z.val : ℝ)/(M : ℝ)-(c : ℝ)) by ring,
      abs_mul,abs_neg,abs_of_pos Real.pi_pos]
  have ht' : |t| ≤ Real.pi/(M : ℝ) := by
    rw [ht]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hd Real.pi_pos.le
  have h := sin_sq_displacement (Real.pi*φ) t
  rw [he] at h
  (try dsimp only)
  calc
    _ ≤ 2*Real.sqrt ((Real.sin (Real.pi*φ))^2*(1-(Real.sin (Real.pi*φ))^2))*|t|+t^2 := h
    _ ≤ 2*Real.sqrt ((Real.sin (Real.pi*φ))^2*(1-(Real.sin (Real.pi*φ))^2))*
        (Real.pi/(M : ℝ))+(Real.pi/(M : ℝ))^2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left ht' (by positivity)
      · have hh := pow_le_pow_left₀ (abs_nonneg t) ht' 2
        simpa only [sq_abs] using hh
    _ = _ := by ring

/-- At success probabilities zero and one, the prepared state is an eigenvector of the
amplification iterate with eigenvalues one and minus one, respectively. -/
private theorem preparedAAIterate_endpoint_eigen (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (MeasureProb (preparedAAState A j) S=0 →
      ApplyGate (preparedAAIterate A j S) (preparedAAState A j)=preparedAAState A j) ∧
    (MeasureProb (preparedAAState A j) S=1 →
      ApplyGate (preparedAAIterate A j S) (preparedAAState A j)=-(preparedAAState A j)) := by
  have hr := (prepared_aa_actual_circuit A j S 1 hA).2.2.2
  rw [pow_one] at hr
  have he := prepared_aa_endpoint_states A j S 1 hA
  constructor
  · intro ha
    exact hr.symm.trans (he.1 ha)
  · intro ha
    simpa only [pow_one,neg_one_smul] using hr.symm.trans (he.2 ha)

/-- When the prepared state has a specified eigenphase, its counter law is the squared
phase-estimation kernel at that phase. -/
private theorem aeLaw_eigen_mass (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (φ : ℝ)
    (he : ApplyGate (preparedAAIterate A j S) (preparedAAState A j) =
      Complex.exp (2*Real.pi*Complex.I*φ) • preparedAAState A j) (z : Fin M) :
    (aeLaw M A j S hA hM).prob z=‖qpeKernel M φ z‖^2 := by
  rw [aeLaw_prob_eq_qpe_marginal, qpeOutput_eigen M _ _ φ he,
    marginalProbLeft_tensorState _ (prepared_aa_reflection_and_access A j S hA).2.1]
  simp [MeasureProb,BornProb]

/-- At zero success probability, the counter law is the squared phase-estimation kernel at phase
zero. -/
theorem aeLaw_zero_mass (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S=0) (z : Fin M) :
    (aeLaw M A j S hA hM).prob z=‖qpeKernel M 0 z‖^2 := by
  apply aeLaw_eigen_mass M hM A j S hA 0
  simpa using (preparedAAIterate_endpoint_eigen A j S hA).1 ha

/-- At unit success probability, the counter law is the squared phase-estimation kernel at phase
`1 / 2`. -/
theorem aeLaw_one_mass (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : MeasureProb (preparedAAState A j) S=1) (z : Fin M) :
    (aeLaw M A j S hA hM).prob z=‖qpeKernel M (1/2) z‖^2 := by
  apply aeLaw_eigen_mass M hM A j S hA (1/2)
  have he : (2*Real.pi*Complex.I*(1/2 : ℝ) : ℂ) = (Real.pi : ℂ)*Complex.I := by norm_num; ring
  rw [he,Complex.exp_pi_mul_I,neg_one_smul]
  exact (preparedAAIterate_endpoint_eigen A j S hA).2 ha

/-- The phase-estimation kernel assigns probability at least `8 / π²` to the BHMT
amplitude-error event [BrassardEtAl2002]. -/
private theorem qpeKernel_bhmt_success (M : ℕ) (hM : 2 ≤ M) (φ : ℝ) :
    let a := (Real.sin (Real.pi*φ))^2
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a| ≤
        2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2),
      ‖qpeKernel M φ z‖^2 ≥ 8/Real.pi^2 := by
  apply (offgrid_phase_window_probability M φ hM).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hz ⊢
    exact aeEstimate_error_of_phaseDistance M (by omega) φ z hz
  · intro z _ _
    exact sq_nonneg _

/-- The prepared counter law assigns probability at least `8 / π²` to the BHMT amplitude-error
event [BrassardEtAl2002]. -/
private theorem aeLaw_bhmt_success (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let a := MeasureProb (preparedAAState A j) S
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a| ≤
        2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2),
      (aeLaw M A j S hA hM).prob z ≥ 8/Real.pi^2 := by
  let a := MeasureProb (preparedAAState A j) S
  have hgeo := prepared_aa_good_bad_geometry A j S hA
  have ha0 : 0 ≤ a := hgeo.2.2.2.2.1
  have ha1 : a ≤ 1 := hgeo.2.2.2.2.2
  by_cases hzero : a=0
  · have hzero' : MeasureProb (preparedAAState A j) S=0 := hzero
    simp_rw [aeLaw_zero_mass M hM A j S hA hzero]
    have h := qpeKernel_bhmt_success M hM 0
    simpa [hzero'] using h
  by_cases hone : a=1
  · have hone' : MeasureProb (preparedAAState A j) S=1 := hone
    simp_rw [aeLaw_one_mass M hM A j S hA hone]
    have h := qpeKernel_bhmt_success M hM (1/2)
    have hsin : (Real.sin (Real.pi*(1/2)))^2=(1 : ℝ) := by
      rw [mul_one_div,Real.sin_pi_div_two]
      norm_num
    simpa only [hone',hsin] using h
  have ha0' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
  have ha1' : a < 1 := lt_of_le_of_ne ha1 hone
  let θ := Real.arcsin (Real.sqrt a)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0')
  have hroot1 : Real.sqrt a < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt ha0 ha1'
  have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hroot1
  have hθa : a=(Real.sin θ)^2 := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le]
    exact (Real.sq_sqrt ha0).symm
  have hp : (Real.sin (Real.pi*(θ/Real.pi)))^2=a := by
    rw [show Real.pi*(θ/Real.pi)=θ by field_simp]
    exact hθa.symm
  have hn : (Real.sin (Real.pi*(-θ/Real.pi)))^2=a := by
    rw [show Real.pi*(-θ/Real.pi)=-θ by field_simp,Real.sin_neg,neg_sq]
    exact hθa.symm
  have hlo := qpeKernel_bhmt_success M hM (θ/Real.pi)
  have hhi := qpeKernel_bhmt_success M hM (-θ/Real.pi)
  dsimp only at hlo hhi
  rw [hp] at hlo
  rw [hn] at hhi
  simp_rw [prepared_ae_two_phase_distribution M hM A j S hA θ hθ0 hθ1 hθa]
  rw [← Finset.sum_div,Finset.sum_add_distrib]
  linarith

/-- The BHMT amplitude-error bound holds with probability at least `8 / π²`; zero amplitude is
decoded exactly, as is unit amplitude when `M` is even [BrassardEtAl2002]. -/
theorem prepared_ae_bhmt_error_and_endpoints (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let a := MeasureProb (preparedAAState A j) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a| ≤
        2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2),
      (aeLaw M A j S hA hM).prob z) ≥ 8/Real.pi^2 ∧
    (a=0 → (aeLaw M A j S hA hM).prob ⟨0,by omega⟩=1) ∧
    (a=1 → 2 ∣ M → ∑ z ∈ Finset.univ.filter (fun z => aeEstimate M z=1),
      (aeLaw M A j S hA hM).prob z=1) := by
  refine ⟨aeLaw_bhmt_success M hM A j S hA, ?_, ?_⟩
  · intro ha
    rw [aeLaw_zero_mass M hM A j S hA ha]
    have hk := (offgrid_phase_geometric_and_periodic M 0 (⟨0,by omega⟩ : Fin M)
      (by omega)).2.2 (⟨0,by omega⟩ : Fin M)
    have hk' : qpeKernel M 0 (⟨0,by omega⟩ : Fin M)=1 := by
      simpa [Qatlib.Foundations.PureStateMath.Ket] using hk
    rw [hk']
    norm_num
  · intro ha hdiv
    let z : Fin M := ⟨M/2,by omega⟩
    have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hcast : ((M/2 : ℕ) : ℝ)*2=(M : ℝ) := by exact_mod_cast (Nat.div_mul_cancel hdiv)
    have hz : (z.val : ℝ)/(M : ℝ)=1/2 := by
      apply (div_eq_iff hm).mpr
      change ((M/2 : ℕ) : ℝ)=1/2*(M : ℝ)
      linarith
    have he : aeEstimate M z=1 := by
      rw [aeEstimate,mul_div_assoc,hz,mul_one_div,Real.sin_pi_div_two]
      norm_num
    have hk (y : Fin M) : qpeKernel M (1/2) y=Qatlib.Foundations.PureStateMath.Ket z y := by
      rw [← hz]
      exact (offgrid_phase_geometric_and_periodic M 0 y (by omega)).2.2 z
    simp_rw [aeLaw_one_mass M hM A j S hA ha,hk]
    rw [Finset.sum_eq_single z]
    · simp [Qatlib.Foundations.PureStateMath.Ket]
    · intro y _ hy
      simp [Qatlib.Foundations.PureStateMath.Ket,hy]
    · simp [Finset.mem_filter,he]

/-- Summing `aeLaw` over a counter-label predicate equals the Born probability of that predicate
on the actual circuit output. -/
theorem aeLaw_event (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (P : Fin M → Prop) :
    (∑ z ∈ Finset.univ.filter P, (aeLaw M A j S hA hM).prob z) =
      MeasureProb (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
      (Finset.univ.filter (fun p => P p.1)) := by
  simp only [aeLaw,MeasureProb,BornProb]
  conv_lhs =>
    arg 2
    ext z
    rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [Finset.sum_filter]

/-- A unitary marking oracle within operator distance `δ` gives BHMT success probability at
least `8 / π² - 2 * (M - 1) * δ`. -/
theorem prepared_ae_noisy_controlled_access (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (V : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) (δ : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin M × (Bool × I)) ℂ)
    (hδ : ‖V-TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (preparedMark S))‖ ≤ δ) :
    let a := MeasureProb (preparedAAState A j) S
    MeasureProb (Run V (countedAECircuit M A j)
      (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))))
      (Finset.univ.filter (fun p => |aeEstimate M p.1-a| ≤
        2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2)) ≥
          8/Real.pi^2-2*((M-1 : ℕ) : ℝ)*δ := by
  let a := MeasureProb (preparedAAState A j) S
  let E := Finset.univ.filter (fun p : Fin M × (Bool × I) => |aeEstimate M p.1-a| ≤
    2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2)
  let input :=
      TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))
  have hgood := (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).1
  rw [aeLaw_event] at hgood
  have hC := prepared_ae_expanded_access_and_output M hM A j S hA
  have hb := measureProb_run_sub_le_queryCount V (aeControlledGate M (preparedMark S))
    (countedAECircuit M A j) input E hV
    (tensorGate_unitary (by simp) (controlOracle_unitary (prepared_aa_reflection_and_access A j S hA).1)) hC.2.2.1
    (normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) (normalized_ket _)))
  rw [hC.1] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hδ
    (by positivity : 0 ≤ 2*((M-1 : ℕ) : ℝ)))
  have hl := (abs_le.mp hb').1
  change 8/Real.pi^2 ≤ MeasureProb (Run (aeControlledGate M (preparedMark S))
    (countedAECircuit M A j) input) E at hgood
  (try dsimp only)
  change 8/Real.pi^2-2*((M-1 : ℕ) : ℝ)*δ ≤
    MeasureProb (Run V (countedAECircuit M A j) input) E
  linarith only [hgood,hl]

/-- Count initialization and forward preparation steps. -/
def aeForwardAccesses {R : Type} (w : List (AEAccessStep R)) : ℕ :=
  (w.map (fun s => match s with | .initialize | .prepareForward => 1 | _ => 0)).sum

/-- Count backward preparation steps. -/
def aeBackwardAccesses {R : Type} (w : List (AEAccessStep R)) : ℕ :=
  (w.map (fun s => match s with | .prepareBackward => 1 | _ => 0)).sum

/-- Count fixed-gate macro steps. -/
def aeFixedMacros {R : Type} (w : List (AEAccessStep R)) : ℕ :=
  (w.map (fun s => match s with | .fixed _ => 1 | _ => 0)).sum

/-- The expanded threshold-loop portion of amplitude estimation. -/
noncomputable def aeFlagAccessWord (M : ℕ) : List (AEAccessStep (Fin M × (Bool × I))) :=
  (phaseThresholdLoop (I := I) M (M-1)).flatMap expandAEAccess

/-- The two fixed Fourier macros surrounding the threshold loop. -/
noncomputable def aeFourierAccessWord (M : ℕ) : List (AEAccessStep (Fin M × (Bool × I))) :=
  [.fixed (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ)),
    .fixed (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]

omit [Fintype I] [DecidableEq I] in

/-- Each expanded query contributes one forward and one backward preparation access, while fixed
macros correspond exactly to the original gates. -/
private theorem expandedAE_separate_counts {M : ℕ} (C : Circuit (Fin M × (Bool × I))) :
    aeForwardAccesses (C.flatMap expandAEAccess)=QueryCount C ∧
    aeBackwardAccesses (C.flatMap expandAEAccess)=QueryCount C ∧
    aeFixedMacros (C.flatMap expandAEAccess)=GateCount C := by
  induction C with
  | nil => simp [aeForwardAccesses,aeBackwardAccesses,aeFixedMacros]
  | cons c C ih =>
    cases c <;>
      simp [expandAEAccess,aeForwardAccesses,aeBackwardAccesses,aeFixedMacros] at * <;> omega

omit [Fintype I] in

/-- The amplitude-estimation access word splits into initialization, a Fourier gate, the
expanded flag loop, and an inverse Fourier gate. -/
theorem aeAccessWord_split (M : ℕ) :
    aeAccessWord (I := I) M = .initialize ::
      ([.fixed (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
        aeFlagAccessWord M ++
        [.fixed (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]) := by
  simp [aeAccessWord,countedPhaseCircuit,List.flatMap_append,expandAEAccess,aeFlagAccessWord]

/-- The full word has `M` forward and `M - 1` backward accesses; its flag loop has `2 * (M - 1)`
fixed macros and its Fourier portion has two. -/
theorem prepared_ae_separate_access_counts (M : ℕ) (hM : 0 < M) :
    aeForwardAccesses (aeAccessWord (I := I) M)=M ∧
    aeBackwardAccesses (aeAccessWord (I := I) M)=M-1 ∧
    aeFixedMacros (aeFlagAccessWord (I := I) M)=2*(M-1) ∧
    aeFixedMacros (aeFourierAccessWord (I := I) M)=2 := by
  have hc := (counted_offgrid_qpe_clean_flag M hM (1 : Matrix I I ℂ) (0 : QState I)).2
  have hs := expandedAE_separate_counts (countedPhaseCircuit (I := I) M)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hi : aeForwardAccesses (aeAccessWord (I := I) M) =
        1+aeForwardAccesses ((countedPhaseCircuit (I := I) M).flatMap expandAEAccess) := by
      simp [aeAccessWord,aeForwardAccesses]
    rw [hi,hs.1,hc.1]
    omega
  · have hi : aeBackwardAccesses (aeAccessWord (I := I) M) =
        aeBackwardAccesses ((countedPhaseCircuit (I := I) M).flatMap expandAEAccess) := by
      simp [aeAccessWord,aeBackwardAccesses]
    rw [hi,hs.2.1,hc.1]
  · rw [aeFlagAccessWord,(expandedAE_separate_counts _).2.2,
      (phaseThresholdLoop_resources (I := I) M (M-1)).2.1]
  · rfl

/-- The chord length from one to a complex phase is twice the absolute sine of half its angle. -/
private theorem aeZero_chord (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * t) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have he : (2 * Real.pi * Complex.I * t : ℂ) =
      Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * t) / 2 = Real.pi * t by ring, Real.norm_eq_abs, abs_mul]
  norm_num

/-- For positive squared sine, the phase-estimation kernel at label zero is bounded by `1 / (M²
* sin²(πφ))`. -/
private theorem aeZero_kernel_bound (M : ℕ) (hM : 0 < M) (φ : ℝ)
    (ha : 0 < Real.sin (Real.pi * φ) ^ 2) :
    ‖qpeKernel M φ ⟨0, hM⟩‖ ^ 2 ≤ 1 / ((M : ℝ) ^ 2 * Real.sin (Real.pi * φ) ^ 2) := by
  have hg := congrArg norm (qpeKernel_geometric_identity M φ ⟨0, hM⟩ hM)
  push_cast at hg
  simp only [zero_div, sub_zero, norm_mul, Complex.norm_natCast] at hg
  have hc := aeZero_chord ((M : ℝ) * φ)
  push_cast at hc
  rw [aeZero_chord, hc] at hg
  have hsq := congrArg (fun x : ℝ => x ^ 2) hg
  simp only [mul_pow, sq_abs] at hsq
  have hs := Real.sin_sq_le_one (Real.pi * ((M : ℝ) * φ))
  apply (le_div_iff₀ (mul_pos (by positivity : 0 < (M : ℝ) ^ 2) ha)).mpr
  nlinarith only [hsq, hs]

/-- For positive prepared success probability `a`, the counter probability at zero is at most `1
/ (M² * a)`. -/
theorem aeLaw_zero_label_mass_bound (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha : 0 < MeasureProb (preparedAAState A j) S) :
    (aeLaw M A j S hA hM).prob ⟨0, by omega⟩ ≤
      1 / ((M : ℝ) ^ 2 * MeasureProb (preparedAAState A j) S) := by
  let a := MeasureProb (preparedAAState A j) S
  have ha1 : a ≤ 1 := (prepared_aa_good_bad_geometry A j S hA).2.2.2.2.2
  by_cases hone : a = 1
  · have hone' : MeasureProb (preparedAAState A j) S = 1 := hone
    rw [aeLaw_one_mass M hM A j S hA hone', hone']
    have h := aeZero_kernel_bound M (by omega) (1 / 2)
      (by rw [mul_one_div, Real.sin_pi_div_two]; norm_num)
    simpa only [mul_one_div, Real.sin_pi_div_two, one_pow, mul_one] using h
  have ha1' : a < 1 := lt_of_le_of_ne ha1 hone
  let θ := Real.arcsin (Real.sqrt a)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha)
  have hroot1 : Real.sqrt a < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt ha.le ha1'
  have hθ1 : θ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hroot1
  have hθa : a = Real.sin θ ^ 2 := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le]
    exact (Real.sq_sqrt ha.le).symm
  have hp : Real.sin (Real.pi * (θ / Real.pi)) ^ 2 = a := by
    rw [show Real.pi * (θ / Real.pi) = θ by field_simp]
    exact hθa.symm
  have hn : Real.sin (Real.pi * (-θ / Real.pi)) ^ 2 = a := by
    rw [show Real.pi * (-θ / Real.pi) = -θ by field_simp, Real.sin_neg, neg_sq]
    exact hθa.symm
  have hlo := aeZero_kernel_bound M (by omega) (θ / Real.pi) (by rwa [hp])
  have hhi := aeZero_kernel_bound M (by omega) (-θ / Real.pi) (by rwa [hn])
  rw [hp] at hlo
  rw [hn] at hhi
  rw [prepared_ae_two_phase_distribution M hM A j S hA θ hθ0 hθ1 hθa]
  linarith

end Qatlib.Concepts.AmplitudeCore.PreparedReadout
