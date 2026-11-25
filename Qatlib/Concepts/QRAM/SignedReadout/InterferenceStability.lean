/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.Calibration
public import Qatlib.Concepts.QRAM.SignedReadout.BornReadoutStability

@[expose] public section

/-!
# Stability of calibrated signed interference

In the signed readout of [KerenidisLandmanPrakash2020], Appendix G, both
sign branches use the common success flag. The conditional state's error
includes the decoded target error and the change in the two weights when
the reference is loaded using an approximate success probability.
The finite Born-law bound also applies after deterministic relabeling.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds (tvDist)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt (observe_mass)
open Qatlib.Foundations.InstrumentCore.Measurement
  (PostMeasure normalized_postMeasure postMeasure_apply_of_not_mem)
open Qatlib.Foundations.PureStateMath
  (ApplyGate BornProb Ket MeasureProb Normalized QState normalized_applyGate normalized_ket)
open Qatlib.Foundations.PureStateMath.BornBridge
  (normalized_iff_norm_toEuclidean_fromVec norm_toEuclidean_fromVec_sq toEuclidean_fromVec)
open Qatlib.Concepts.QRAM.AmplitudeAccess (pathAmplitude)
open Qatlib.Foundations.QramData.SquaredNormTree (Address mass)
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Place the two signed combinations in the two sign outputs on the common
success slice. The failure slice has zero amplitude. -/
def interferenceSuccessState (target reference : QState I) : QState (Bool × (Bool × I)) :=
  fun (sign, success, i) =>
    if success then
      (if sign then target i - reference i else target i + reference i) / (2 : ℂ)
    else 0

omit [Fintype I] [DecidableEq I] in
/-- Subtracting two interference states subtracts both input branches. -/
private theorem interference_success_state_sub (u v x y : QState I) :
    interferenceSuccessState u v - interferenceSuccessState x y =
      interferenceSuccessState (u - x) (v - y) := by
  funext z
  rcases z with ⟨b, f, i⟩
  cases f <;> cases b <;> simp [interferenceSuccessState] <;> ring

omit [DecidableEq I] in
/-- Half the sum of the squared input norms is the squared norm of the
interference state on the common success slice. -/
theorem interference_success_state_norm_sq (u v : QState I) :
    ‖toEuclidean_fromVec (interferenceSuccessState u v)‖ ^ 2 =
      (‖toEuclidean_fromVec u‖ ^ 2 + ‖toEuclidean_fromVec v‖ ^ 2) / 2 := by
  have hFlag (b : Bool) :
      (∑ z : Bool × I, ‖interferenceSuccessState u v (b, z)‖ ^ 2) =
        ∑ i, ‖(if b then u i - v i else u i + v i) / (2 : ℂ)‖ ^ 2 := by
    simp [Fintype.sum_prod_type, interferenceSuccessState]
  calc
    _ = ∑ b : Bool, ∑ i, ‖(if b then u i - v i else u i + v i) / (2 : ℂ)‖ ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
      simp only [hFlag]
    _ = (‖toEuclidean_fromVec (u + v)‖ ^ 2 + ‖toEuclidean_fromVec (u - v)‖ ^ 2) / 4 := by
      rw [Fintype.sum_bool, norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
      simp [div_pow, ← Finset.sum_div]
      ring
    _ = _ := by
      change (‖toEuclidean_fromVec u + toEuclidean_fromVec v‖ ^ 2 +
        ‖toEuclidean_fromVec u - toEuclidean_fromVec v‖ ^ 2) / 4 = _
      rw [parallelogram_law_with_norm ℂ]
      ring

omit [DecidableEq I] in
/-- An interference state's norm is bounded by the sum of the two input norms. -/
private theorem interference_success_state_norm_le (u v : QState I) :
    ‖toEuclidean_fromVec (interferenceSuccessState u v)‖ ≤
      ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [interference_success_state_norm_sq]
  nlinarith [sq_nonneg ‖toEuclidean_fromVec u‖, sq_nonneg ‖toEuclidean_fromVec v‖,
    mul_nonneg (norm_nonneg (toEuclidean_fromVec u)) (norm_nonneg (toEuclidean_fromVec v))]

/-- The conditioned circuit state is the interference of the decoded inputs,
weighted by their respective square-root success masses. -/
theorem heralded_interference_readout_eq_weighted_state
    (target decoder reference : Matrix I I ℂ) (S : Finset I) (q : ℝ) (seed : I)
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ)
    (hReference : reference ∈ Matrix.unitaryGroup I ℂ) (hq : 0 ≤ q)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed)) S) :
    let p := MeasureProb (ApplyGate target (Ket seed)) S
    let m := (p + q) / 2
    let ψ := ApplyGate decoder (PostMeasure (ApplyGate target (Ket seed)) S)
    let φ := ApplyGate reference (Ket seed)
    heraldedInterferenceReadout target decoder reference S q seed =
      interferenceSuccessState
        ((Real.sqrt p / Real.sqrt m : ℝ) • ψ) ((Real.sqrt q / Real.sqrt m : ℝ) • φ) := by
  intro p m ψ φ
  funext z
  rcases z with ⟨b, f, i⟩
  cases f with
  | false =>
    change PostMeasure _ (Finset.univ ×ˢ ({true} ×ˢ (Finset.univ : Finset I))) (b, false, i) = 0
    exact postMeasure_apply_of_not_mem _ _ (by simp)
  | true =>
    have hEntry := heralded_interference_calibrated_entry target decoder reference S q seed
      hDecoder hReference hq hp b i
    change heraldedInterferenceReadout target decoder reference S q seed (b, true, i) =
      (if b then (Real.sqrt p : ℂ) * ψ i - (Real.sqrt q : ℂ) * φ i
        else (Real.sqrt p : ℂ) * ψ i + (Real.sqrt q : ℂ) * φ i) / (2 * (Real.sqrt m : ℂ)) at hEntry
    rw [hEntry]
    cases b <;> simp [interferenceSuccessState, Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_eq_mul, div_eq_mul_inv, _root_.mul_inv_rev] <;> ring

/-- The total variation of a calibrated shot is bounded by the decoded target
error plus twice the relative mass imbalance, with the same loaded reference
in the ideal experiment. The estimate holds for every deterministic reading
of the sign, success flag, and workspace label. -/
theorem heralded_interference_shot_tv_le {O : Type} [Fintype O] [DecidableEq O]
    (target decoder reference : Matrix I I ℂ) (S : Finset I) (q : ℝ) (seed : I)
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ)
    (hReference : reference ∈ Matrix.unitaryGroup I ℂ) (hq : 0 ≤ q)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed)) S)
    (ideal : QState I) (hIdeal : Normalized ideal) (label : Bool × (Bool × I) → O) :
    let p := MeasureProb (ApplyGate target (Ket seed)) S
    let ψ := ApplyGate decoder (PostMeasure (ApplyGate target (Ket seed)) S)
    let φ := ApplyGate reference (Ket seed)
    let state := heraldedInterferenceReadout target decoder reference S q seed
    let clean := interferenceSuccessState ideal φ
    ∃ hState hClean, tvDist (bornReadoutLaw state hState label) (bornReadoutLaw clean hClean label) ≤
      ‖toEuclidean_fromVec (ψ - ideal)‖ + 2 * (|p - q| / (p + q)) := by
  intro p ψ φ state clean
  let m := (p + q) / 2
  let w := Real.sqrt p / Real.sqrt m
  let v := Real.sqrt q / Real.sqrt m
  let δ := |p - q| / (p + q)
  have hw : |w - 1| ≤ δ := (le_max_left _ _).trans (interference_calibration_weights p q hp hq)
  have hv : |v - 1| ≤ δ := (le_max_right _ _).trans (interference_calibration_weights p q hp hq)
  have hState : Normalized state := by
    dsimp only [state, heraldedInterferenceReadout]
    apply normalized_postMeasure
    rw [heralded_interference_success target decoder reference S q seed hDecoder hReference hq]
    exact half_pos (add_pos_of_pos_of_nonneg hp hq)
  have hψ : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).1 (normalized_applyGate hDecoder (normalized_postMeasure hp))
  have hφ : ‖toEuclidean_fromVec φ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec φ).1 (normalized_applyGate hReference (normalized_ket seed))
  have hClean : Normalized clean := by
    apply (normalized_iff_norm_toEuclidean_fromVec clean).2
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    change ‖toEuclidean_fromVec (interferenceSuccessState ideal φ)‖ ^ 2 = (1 : ℝ) ^ 2
    rw [interference_success_state_norm_sq, (normalized_iff_norm_toEuclidean_fromVec ideal).1 hIdeal, hφ]
    norm_num
  have hLeft : ‖toEuclidean_fromVec (w • ψ - ideal)‖ ≤ ‖toEuclidean_fromVec (ψ - ideal)‖ + δ := by
    have hEq : w • ψ - ideal = (ψ - ideal) + (w - 1) • ψ := by
      rw [sub_smul, one_smul]
      abel
    rw [hEq]
    change ‖toEuclidean_fromVec (ψ - ideal) + (w - 1) • toEuclidean_fromVec ψ‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hψ, mul_one]
    exact add_le_add le_rfl hw
  have hRight : ‖toEuclidean_fromVec (v • φ - φ)‖ ≤ δ := by
    have hEq : v • φ - φ = (v - 1) • φ := by rw [sub_smul, one_smul]
    rw [hEq]
    change ‖(v - 1) • toEuclidean_fromVec φ‖ ≤ δ
    rw [norm_smul, Real.norm_eq_abs, hφ, mul_one]
    exact hv
  have hRead : state = interferenceSuccessState (w • ψ) (v • φ) :=
    heralded_interference_readout_eq_weighted_state target decoder reference S q seed hDecoder hReference hq hp
  refine ⟨hState, hClean, (born_readout_tv_le state clean hState hClean label).trans ?_⟩
  calc
    ‖toEuclidean_fromVec (state - clean)‖ ≤
        ‖toEuclidean_fromVec (w • ψ - ideal)‖ + ‖toEuclidean_fromVec (v • φ - φ)‖ := by
      rw [hRead, show clean = interferenceSuccessState ideal φ from rfl, interference_success_state_sub]
      exact interference_success_state_norm_le _ _
    _ ≤ _ := by linarith

variable {depth : ℕ}

/-- Read the sign and physical address from a flagged interference outcome. -/
def placedInterferenceLabel (place : Address depth ↪ I) (fallback : Address depth)
    (z : Bool × (Bool × I)) : Bool × Address depth :=
  (z.1, readPlacedAddress place fallback z.2.2)

/-- Balanced interference on the embedded real direction and the embedded
empirical reference gives the exact conditional law of the signed readout. -/
theorem embedded_interference_readout_law (place : Address depth ↪ I) (fallback : Address depth)
    (direction : Address depth → ℝ) (hDirection : ∑ i, direction i ^ 2 = 1)
    (samples : List (Address depth)) (hSamples : samples ≠ [])
    (ref : QState I)
    (hRef : ref = embeddedDirection place (fun i => pathAmplitude (empiricalTree samples) i))
    (hState : Normalized (interferenceSuccessState (embeddedDirection place direction) ref)) :
    bornReadoutLaw (interferenceSuccessState (embeddedDirection place direction) ref) hState
      (placedInterferenceLabel place fallback) =
      interferenceSampleLaw direction hDirection samples hSamples := by
  subst ref
  let r (i : Address depth) := pathAmplitude (empiricalTree samples) i
  let ψ := interferenceSuccessState (embeddedDirection place direction) (embeddedDirection place r)
  let e := referenceWorkspaceEquiv place
  have hPad (d : Address depth → ℝ) (j : Address depth ⊕ {i // i ∉ Set.range place}) :
      embeddedDirection place d (e j) = (Sum.elim (fun a => (d a : ℂ)) 0) j := by
    change (Sum.elim (fun a => (d a : ℂ)) 0) (e.symm (e j)) = _
    rw [Equiv.symm_apply_apply]
  have hIn (b : Bool) (i : Address depth) :
      ψ (b, true, e (Sum.inl i)) = (interferenceAmplitude direction samples (b, i) : ℂ) := by
    cases b <;> simp [ψ, r, interferenceSuccessState, hPad, interferenceAmplitude, positiveAmplitude,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div]
  have hOut (b : Bool) (k : {i // i ∉ Set.range place}) :
      ψ (b, true, e (Sum.inr k)) = 0 := by
    cases b <;> simp [ψ, interferenceSuccessState, hPad]
  have hRead (i : Address depth) :
      readPlacedAddress place fallback (e (Sum.inl i)) = i := read_placed_address place fallback i
  apply Qatlib.Concepts.ProbabilityCore.Concentration.FinDist.ext
  rintro ⟨b, a⟩
  rw [bornReadoutLaw, observe_mass, interference_sample_born]
  change (∑ z, if placedInterferenceLabel place fallback z = (b, a) then BornProb ψ z else 0) =
    BornProb (fun z => (interferenceAmplitude direction samples z : ℂ)) (b, a)
  let weight := BornProb (fun z => (interferenceAmplitude direction samples z : ℂ)) (b, a)
  have hFiber (s f : Bool) :
      (∑ i : I, if (s, readPlacedAddress place fallback i) = (b, a) then BornProb ψ (s, f, i) else 0) =
        if f then (if s = b then weight else 0) else 0 := by
    cases f with
    | false => simp [ψ, interferenceSuccessState, BornProb]
    | true =>
      rw [← e.sum_comp (fun i =>
        if (s, readPlacedAddress place fallback i) = (b, a) then BornProb ψ (s, true, i) else 0),
        Fintype.sum_sum_type]
      cases s <;> cases b <;> simp [hIn, hOut, hRead, BornProb, weight]
  simp only [Fintype.sum_prod_type]
  change (∑ s : Bool, ∑ f : Bool, ∑ i : I,
    if (s, readPlacedAddress place fallback i) = (b, a) then BornProb ψ (s, f, i) else 0) = weight
  simp_rw [hFiber]
  cases b <;> simp

/-- A calibrated conditional shot with the QRAM-loaded empirical reference
approximates the ideal signed law on addresses. The bound separates the
decoder's target-state error and the relative calibration imbalance. -/
theorem embedded_heralded_interference_shot_tv_le (place : Address depth ↪ I) (fallback : Address depth)
    (target decoder : Matrix I I ℂ) (S : Finset I) (q : ℝ) (seed : I)
    (hDecoder : decoder ∈ Matrix.unitaryGroup I ℂ) (hq : 0 ≤ q)
    (hp : 0 < MeasureProb (ApplyGate target (Ket seed)) S)
    (direction : Address depth → ℝ) (hDirection : ∑ i, direction i ^ 2 = 1)
    (samples : List (Address depth)) (hSamples : samples ≠ []) :
    let ref := embeddedReferencePreparation place seed samples
    let p := MeasureProb (ApplyGate target (Ket seed)) S
    let ψ := ApplyGate decoder (PostMeasure (ApplyGate target (Ket seed)) S)
    let state := heraldedInterferenceReadout target decoder ref S q seed
    ∃ hState, tvDist (bornReadoutLaw state hState (placedInterferenceLabel place fallback))
        (interferenceSampleLaw direction hDirection samples hSamples) ≤
      ‖toEuclidean_fromVec (ψ - embeddedDirection place direction)‖ + 2 * (|p - q| / (p + q)) := by
  intro ref p ψ state
  have hRef : ApplyGate ref (Ket seed) =
      embeddedDirection place (fun i => pathAmplitude (empiricalTree samples) i) := by
    have hMass : 0 < mass (empiricalTree samples) := by rw [empirical_tree_mass samples hSamples]; exact zero_lt_one
    exact embedded_tree_preparation_apply place seed (empiricalTree samples) (valid_empirical_tree samples) hMass
  obtain ⟨hState, hClean, hBound⟩ := heralded_interference_shot_tv_le target decoder ref S q seed hDecoder
    (embedded_reference_preparation_unitary place seed samples) hq hp (embeddedDirection place direction)
    (embedded_direction_normalized place direction hDirection) (placedInterferenceLabel place fallback)
  change tvDist (bornReadoutLaw state hState (placedInterferenceLabel place fallback))
    (bornReadoutLaw (interferenceSuccessState (embeddedDirection place direction) (ApplyGate ref (Ket seed)))
      hClean (placedInterferenceLabel place fallback)) ≤ _ at hBound
  rw [embedded_interference_readout_law place fallback direction hDirection samples hSamples
    (ApplyGate ref (Ket seed)) hRef hClean] at hBound
  exact ⟨hState, hBound⟩

end Qatlib.Concepts.QRAM.SignedReadout
