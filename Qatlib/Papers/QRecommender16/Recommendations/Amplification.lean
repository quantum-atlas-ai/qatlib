/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.ConditionalReadout
public import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseConsumers
public import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

@[expose] public section

/-!
# Amplification of QRAM recommendations

[KerenidisPrakash2017], Algorithm 5.2, supplies the successful branch
of the singular-value test for recommendation. The preparation here executes the QRAM
loaders and the reversible phase threshold flag. A mixed integer window
uses a certified lower bound on the success amplitude and preserves the
conditional product law of the unamplified sampler. Costs count calls to
the preparation and its adjoint and the two reflections. The spectral
error estimate includes the user's transition mass, and the model uses exact gates.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_smul)
open Qatlib.Foundations.QueryWordCore.Circuit (Run)
open Qatlib.Concepts.LchsSimulation.StaticLchs
  (preparedAACircuit preparedAAState preparedAAWord preparedDataQueries preparedFixedGates preparedInputQueries
    preparedMark prepared_aa_separate_access_word)
open Qatlib.Concepts.HhlAlgorithms.Postselection (depth)
open Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe (amplified_collapse_smul mixed_window_avg)
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
open Qatlib.Papers.QRecommender16.QramMatrix
open Qatlib.Foundations.QramData.SquaredNormTree (Address Valid mass)
open scoped BigOperators Classical Matrix.Norms.Frobenius

variable {rows columns : ℕ}

/-- The flags, counting labels, and QRAM input workspace of the recommendation circuit. -/
abbrev RecommendationBasis (rows columns bits : ℕ) := Bool × (Reg bits × (Fin (2 ^ rows) × Fin (2 ^ columns)))

/-- The clean flag, counting register and row-column seed for the QRAM sampler. -/
def storedRecommendationSeed (rows columns bits : ℕ) : RecommendationBasis rows columns bits :=
  (false, ZeroStr bits, storedWalkUserSeed rows columns)

/-- The reversible QRAM loaders followed by the coherent phase threshold flag and its
counting-register uncomputation. -/
def storedRecommendationPreparation (storage : MatrixStorage rows columns) (user : Address rows)
    (bits : ℕ) (accepted : Finset (Reg bits)) :
    Matrix (RecommendationBasis rows columns bits) (RecommendationBasis rows columns bits) ℂ :=
  thresholdFlagGate bits ((bireflectionWalk (storedMatrix storage)).map Complex.ofReal) accepted *
    TensorGate 1 (TensorGate 1 (storedWalkUserLoader storage user))

/-- The actual preparation, including the QRAM loaders, is a unitary whenever the
stored matrix and its rows have the positive masses required by the walk. -/
theorem stored_recommendation_preparation_unitary (storage : MatrixStorage rows columns) (hValid : Valid storage)
    (hPos : 0 < mass storage) (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row))
    (user : Address rows) (bits : ℕ) (accepted : Finset (Reg bits)) :
    storedRecommendationPreparation storage user bits accepted ∈ Matrix.unitaryGroup _ ℂ := by
  have hRows' (i : Fin (2 ^ rows)) : 0 < rowNormSq (storedMatrix storage) i := by
    rw [stored_matrix_row_norm_sq storage hValid]
    exact hRows _
  have hNorm : 0 < ‖storedMatrix storage‖ := by
    rw [stored_matrix_frobenius_norm storage hValid]
    exact Real.sqrt_pos.mpr hPos
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    (threshold_flag_gate_unitary bits _ (complex_bireflection_walk_unitary _ hRows' hNorm) accepted)
    (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem
      (tensorGate_unitary (Matrix.unitaryGroup (Reg bits) ℂ).one_mem
        (stored_walk_user_loader_unitary storage hValid user)))

/-- With a clean seed the combined unitary agrees with the actual unamplified QRAM sampler. -/
theorem stored_recommendation_preparation_apply (storage : MatrixStorage rows columns) (user : Address rows)
    (bits : ℕ) (accepted : Finset (Reg bits)) :
    preparedAAState (storedRecommendationPreparation storage user bits accepted)
      (storedRecommendationSeed rows columns bits) =
      executeThresholdFlag bits ((bireflectionWalk (storedMatrix storage)).map Complex.ofReal) accepted
        (storedWalkUserInput storage user) := by
  unfold preparedAAState storedRecommendationPreparation storedRecommendationSeed
  rw [applyGate_mul, ← tensorState_ket_ket false, ← tensorState_ket_ket (ZeroStr bits)]
  simp only [applyGate_tensorGate, applyGate_one, stored_walk_user_loader_apply, threshold_flag_gate_apply]

/-- Every state with the threshold flag set to true counts as a successful recommendation. -/
def recommendationSuccess (rows columns bits : ℕ) : Finset (RecommendationBasis rows columns bits) :=
  {true} ×ˢ Finset.univ

/-- Execute the amplified recommendation sampler with the actual threshold-flag reflection. -/
def storedRecommendationAmplifiedOutput (storage : MatrixStorage rows columns) (user : Address rows)
    (bits : ℕ) (accepted : Finset (Reg bits)) (k : ℕ) : QState (RecommendationBasis rows columns bits) :=
  let seed := storedRecommendationSeed rows columns bits
  Run (preparedMark (recommendationSuccess rows columns bits))
    (preparedAACircuit (storedRecommendationPreparation storage user bits accepted) seed k) (Ket seed)

/-- The executed amplification word uses one success reflection and one seed reflection per
round, with one initial preparation and a forward and inverse preparation per round. -/
theorem stored_recommendation_amplification_access (storage : MatrixStorage rows columns) (hValid : Valid storage)
    (hPos : 0 < mass storage) (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row))
    (user : Address rows) (bits : ℕ) (accepted : Finset (Reg bits)) (k : ℕ) :
    let word := preparedAAWord (storedRecommendationSeed rows columns bits) k
    preparedDataQueries word = k ∧ preparedInputQueries word = 2 * k + 1 ∧ preparedFixedGates word = k := by
  obtain ⟨_, hData, hPrep, hFixed, _, _⟩ := prepared_aa_separate_access_word
    (storedRecommendationPreparation storage user bits accepted) (storedRecommendationSeed rows columns bits)
    (recommendationSuccess rows columns bits) k
    (stored_recommendation_preparation_unitary storage hValid hPos hRows user bits accepted)
  exact ⟨hData, hPrep, hFixed⟩

set_option maxHeartbeats 1500000 in
/-- A uniform mixture over the window succeeds with probability at least `1/8` and preserves
the conditional law even when some individual depths have zero success mass. The integer
window can be supplied from any positive certified lower bound on the original amplitude. -/
theorem stored_recommendation_mixed_window (storage : MatrixStorage rows columns) (hValid : Valid storage)
    (hPos : 0 < mass storage) (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row))
    (user : Address rows) (bits : ℕ) (accepted : Finset (Reg bits)) (m : ℕ) (hm : 0 < m)
    (lower : ℝ) (hLower : 0 < lower) (hWindow : 1 ≤ (m : ℝ) * lower)
    (event : Finset (RecommendationBasis rows columns bits)) :
    let base := executeThresholdFlag bits ((bireflectionWalk (storedMatrix storage)).map Complex.ofReal)
      accepted (storedWalkUserInput storage user)
    let good := recommendationSuccess rows columns bits
    let out := fun s : Fin (2 * m) => storedRecommendationAmplifiedOutput storage user bits accepted (depth m s)
    lower ^ 2 ≤ MeasureProb base good →
      (1 / 8 : ℝ) ≤ (∑ s, MeasureProb (out s) good) / (2 * m : ℝ) ∧
      (∀ s : Fin (2 * m), depth m s < m) ∧
      (∑ s, MeasureProb (out s) (good ∩ event)) / (∑ s, MeasureProb (out s) good) =
        MeasureProb (PostMeasure base good) event := by
  intro base good out hBound
  let A := storedRecommendationPreparation storage user bits accepted
  let seed := storedRecommendationSeed rows columns bits
  have hA : A ∈ Matrix.unitaryGroup _ ℂ :=
    stored_recommendation_preparation_unitary storage hValid hPos hRows user bits accepted
  have hPrep : preparedAAState A seed = base := stored_recommendation_preparation_apply storage user bits accepted
  have hRaw : 0 < MeasureProb base good := (pow_pos hLower _).trans_le hBound
  have hSuccess : (1 / 8 : ℝ) ≤ (∑ s, MeasureProb (out s) good) / (2 * m : ℝ) :=
    mixed_window_avg A seed good m lower hA hm hLower (by rwa [hPrep]) hWindow
  have hm' : (0 : ℝ) < 2 * m := by positivity
  have hTotal : 0 < ∑ s, MeasureProb (out s) good :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 8) hm').trans_le ((le_div_iff₀ hm').mp hSuccess)
  refine ⟨hSuccess, ?_, ?_⟩
  · intro s
    unfold depth
    split_ifs <;> omega
  · have hFactor (s : Fin (2 * m)) : MeasureProb (out s) (good ∩ event) =
        MeasureProb (PostMeasure base good) event * MeasureProb (out s) good := by
      obtain ⟨z, hz⟩ := amplified_collapse_smul A seed good (depth m s) hA
      change Collapse (out s) good = z • Collapse (preparedAAState A seed) good at hz
      rw [hPrep] at hz
      have hs (E : Finset (RecommendationBasis rows columns bits)) :
          MeasureProb (out s) (good ∩ E) = ‖z‖ ^ 2 * MeasureProb base (good ∩ E) := by
        rw [← measureProb_collapse, hz, measureProb_smul, measureProb_collapse]
      have hGood := hs Finset.univ
      rw [Finset.inter_univ] at hGood
      rw [hs event, hGood, ← postMeasure_chain_rule hRaw event]
      ring
    simp_rw [hFactor]
    rw [← Finset.mul_sum, mul_div_cancel_right₀ _ hTotal.ne']

set_option maxHeartbeats 1700000 in
/-- The mixed amplified QRAM sampler has constant success probability and the same
conditional product-event error bound as the unamplified singular-value filter. Any positive
lower bound below the retained norm minus the classification error certifies a window of size
the ceiling of its reciprocal. -/
theorem stored_recommendation_amplified_event_error
    (storage : MatrixStorage rows columns) (hValid : Valid storage) (hPos : 0 < mass storage)
    (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row)) (user : Address rows)
    (bits : ℕ) (window cutoff halfWidth : ℝ) (hWindow : 1 < window)
    (hResolution : ‖storedMatrix storage‖ * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (keep : Fin (2 ^ columns) → Prop)
    (hSelection : IsThresholdSelection (rightSingularValue (storedMatrix storage)) cutoff halfWidth keep)
    (lower : ℝ) (hLower : 0 < lower)
    (products : Finset (Fin (2 ^ columns))) :
    let A := storedMatrix storage
    let x := rightSingularPart A (storedUserAmplitudes storage user) keep
    let error := Real.sqrt (1 / (2 * (window - 1)) +
      rightSingularTransitionMass A (storedUserAmplitudes storage user) cutoff halfWidth)
    let m := ⌈1 / lower⌉₊
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue ‖A‖ label
    let good := recommendationSuccess rows columns bits
    let out := fun s : Fin (2 * m) => storedRecommendationAmplifiedOutput storage user bits accepted (depth m s)
    let event : Finset (RecommendationBasis rows columns bits) :=
      Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ products))
    lower ≤ Real.sqrt (∑ j, x j ^ 2) - error →
      (1 / 8 : ℝ) ≤ (∑ s, MeasureProb (out s) good) / (2 * m : ℝ) ∧
      (∀ s : Fin (2 * m), depth m s < m) ∧ (m : ℝ) < 1 / lower + 1 ∧
      |(∑ s, MeasureProb (out s) (good ∩ event)) / (∑ s, MeasureProb (out s) good) -
        (∑ j ∈ products, x j ^ 2) / ∑ j, x j ^ 2| ≤ 2 * error / Real.sqrt (∑ j, x j ^ 2) := by
  intro A x error m accepted good out event hBound
  have hGap : error < Real.sqrt (∑ j, x j ^ 2) := by linarith only [hLower, hBound]
  obtain ⟨_, hProb, hEvent⟩ := stored_recommendation_event_error storage hValid hPos hRows user bits
    window cutoff halfWidth hWindow hResolution keep hSelection products hGap
  have hSquared := (sq_le_sq₀ hLower.le (sub_nonneg.mpr hGap.le)).mpr hBound
  have hInverse : 0 < 1 / lower := div_pos one_pos hLower
  have hm : 0 < m := Nat.ceil_pos.mpr hInverse
  have hAmplifier : 1 ≤ (m : ℝ) * lower := (div_le_iff₀ hLower).mp (Nat.le_ceil (1 / lower))
  obtain ⟨hSuccess, hDepth, hLaw⟩ := stored_recommendation_mixed_window storage hValid hPos hRows user bits
    accepted m hm lower hLower hAmplifier event (hSquared.trans hProb)
  refine ⟨hSuccess, hDepth, Nat.ceil_lt_add_one hInverse.le, ?_⟩
  rw [hLaw]
  exact hEvent

end Qatlib.Papers.QRecommender16.Recommendations
