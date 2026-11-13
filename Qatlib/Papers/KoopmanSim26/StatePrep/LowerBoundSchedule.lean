/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.StatePrep.ObservablePreparation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Mathlib.Tactic

/-!
# Randomized preparation from a probability lower bound

This module constructs a finite randomized amplitude amplification schedule for a unitary
preparation matrix with marked probability at least a known positive lower bound. The schedule
samples a Boolean branch and a uniform round index: `chosenRound` uses zero rounds on one branch
and the sampled index on the other. `jointLaw` combines this choice with the actual Born
measurement, and `lower_bound_schedule` proves success at least 1/8 with expected preparation
access count at most 5 divided by the square root of the lower bound. This supplies a concrete
preparation schedule for the observable input construction of [ZhangEtAl2026].

For observable states, `balanced_source_schedule` specializes the cost to a balanced collection
of amplitudes. The span results and `actual_successful_density` show that every successful
amplified branch retains the same complex target direction, so averaging the branches gives the
target pure density multiplied by its success probability.

## Main statements

* `window_bounds` controls the integer amplification window by the inverse square root of the
  supplied probability bound.
* `lower_bound_schedule` proves the actual success and expected access bounds for the finite
  joint law.
* `balanced_source_schedule` gives the expected access bound 5/(c sqrt(eta)) under balanced
  observable amplitudes.
* `actual_successful_density` identifies the successful density exactly, and
  `mature_window_success` gives constant success for any sufficiently large window.

## References

* [Zhang et al., 2026][ZhangEtAl2026], Quantum simulation of real-world nonlinear dynamics via
  Koopman method.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Papers.KoopmanSim26.StatePrep.Observables
open scoped Classical
namespace Qatlib.Papers.KoopmanSim26.StatePrep.LowerSchedule

/-- The amplification window is the larger of one and the natural ceiling of the inverse square
root of the supplied real lower bound. -/
noncomputable def window (ℓ : ℝ) : ℕ := max 1 (Nat.ceil (1/Real.sqrt ℓ))

/-- The chosen amplification window is positive for every real input. -/
theorem window_pos (ℓ : ℝ) : 0 < window ℓ := by unfold window; omega

/-- For a lower bound strictly between zero and one inclusive, the window times its square root
is at least one, while the window itself is at most twice its inverse square root. -/
theorem window_bounds (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    1 ≤ (window ℓ : ℝ) * Real.sqrt ℓ ∧ (window ℓ : ℝ) ≤ 2 / Real.sqrt ℓ := by
  have hr : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hr1 : Real.sqrt ℓ ≤ 1 := Real.sqrt_le_one.mpr hℓ1
  have hceil : 1/Real.sqrt ℓ ≤ (window ℓ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 1 (Nat.ceil (1/Real.sqrt ℓ)))
  have hupper : (window ℓ : ℝ) ≤ 1/Real.sqrt ℓ + 1 := by
    simp only [window, Nat.cast_max, Nat.cast_one]
    apply max_le
    · have : 0 < 1/Real.sqrt ℓ := one_div_pos.mpr hr
      linarith
    · exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1/Real.sqrt ℓ)).le
  constructor
  · exact (div_le_iff₀ hr).mp hceil
  · have h1 : 1 ≤ 1/Real.sqrt ℓ := (le_div_iff₀ hr).mpr (by simpa using! hr1)
    linarith [show 2 / Real.sqrt ℓ = 2 * (1/Real.sqrt ℓ) by ring]

/-- Selects zero amplification rounds when the Boolean branch is true and the supplied finite
index otherwise. -/
def chosenRound {M : ℕ} (z : Bool × Fin M) : ℕ := if z.1 then 0 else z.2.val

/-- The state obtained by running prepared amplitude amplification from the basis seed with the
round count selected by `chosenRound` and marked set `S`. -/
noncomputable def runState {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) {M : ℕ} (z : Bool × Fin M) : QState I :=
  Run (preparedMark S) (preparedAACircuit A j (chosenRound z)) (Ket j)

/-- A unitary preparation matrix makes every state selected by the randomized schedule
normalized. -/
theorem runState_normalized {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    {M : ℕ} (z : Bool × Fin M) : Normalized (runState A j S z) :=
  (prepared_aa_actual_circuit A j S (chosenRound z) hA).1.normalized_run
    (prepared_aa_reflection_and_access A j S hA).1 (normalized_ket j)

/-- The finite joint distribution of a uniform Boolean branch, a uniform index in the positive
window, and the Born measurement outcome of the corresponding amplified state. -/
noncomputable def jointLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) : FinDist ((Bool × Fin M) × I) where
  prob x := 1/(2*(M:ℝ)) * BornProb (runState A j S x.1) x.2
  nonneg x := mul_nonneg (by positivity) (bornProb_nonneg _ _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, bornProb_sum_eq_one (runState_normalized A hA j S _)]
    simp
    field_simp

/-- The probability mass function obtained from the finite joint law of the randomized schedule
and its measurement outcome. -/
noncomputable def jointPMF {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) : PMF ((Bool × Fin M) × I) := toPMF (jointLaw A hA j S M hM)

/-- The sum of marked measurement masses over all Boolean and round choices, each weighted by
the reciprocal of twice the window size. -/
noncomputable def success {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (M : ℕ) : ℝ :=
  ∑ z : Bool × Fin M, 1/(2*(M:ℝ)) * MeasureProb (runState A j S z) S

/-- For a unitary preparation and positive window, `success` equals the expectation of the
marked outcome indicator under the actual joint law. -/
theorem success_is_actual {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    (jointLaw A hA j S M hM).expect (fun x => if x.2 ∈ S then 1 else 0) = success A j S M := by
  simp only [FinDist.expect, jointLaw, success, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  simp [MeasureProb, Finset.mul_sum]

/-- For a positive window, the schedule's success is half the unamplified marked probability
plus half the average marked probability over round counts from zero to one less than the
window size. -/
theorem success_formula {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (M : ℕ) (hM : 0 < M) :
    success A j S M = (1/2)*MeasureProb (preparedAAState A j) S +
      (1/2)*((∑ i : Fin M, MeasureProb
        (Run (preparedMark S) (preparedAACircuit A j i.val) (Ket j)) S)/(M:ℝ)) := by
  simp only [success, Fintype.sum_prod_type, Fintype.sum_bool, runState, chosenRound,
    Bool.false_eq_true, if_false, if_true]
  have hzero : Run (preparedMark S) (preparedAACircuit A j 0) (Ket j) = preparedAAState A j := by
    simp [preparedAACircuit, preparedAAState, RepeatCircuit]
  simp_rw [hzero]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hMr : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- For a unitary preparation, if a positive lower bound does not exceed the initial marked
probability and that probability is at most one, the randomized schedule using `window` has
success at least 1/8. -/
theorem lower_bound_success {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hlower : ℓ ≤ MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    1/8 ≤ success A j S (window ℓ) := by
  let p := MeasureProb (preparedAAState A j) S
  have hp0 : 0 < p := hℓ.trans_le hlower
  have hr0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hℓ1 : ℓ ≤ 1 := hlower.trans hp1
  have hwindow := window_bounds ℓ hℓ hℓ1
  rw [success_formula A j S _ (window_pos ℓ)]
  have hnonneg : 0 ≤ (∑ i : Fin (window ℓ), MeasureProb
      (Run (preparedMark S) (preparedAACircuit A j i.val) (Ket j)) S)/(window ℓ:ℝ) := by
    apply div_nonneg (Finset.sum_nonneg (fun _ _ => measureProb_nonneg _ _))
    positivity
  by_cases hp : p < 1/2
  · let θ := Real.arcsin (Real.sqrt p)
    have hsquare : (Real.sqrt p)^2 = p := Real.sq_sqrt hp0.le
    have hrs : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
    have hsin : Real.sin θ = Real.sqrt p := Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) hrs
    have hθ0 : 0 < θ := Real.arcsin_pos.mpr hr0
    have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr (by nlinarith)
    have hmass : p = (Real.sin θ)^2 := by rw [hsin, hsquare]
    have hcos : Real.cos θ = Real.sqrt (1-p) := by
      dsimp only [θ]
      rw [Real.cos_arcsin, hsquare]
    have hc0 : 0 ≤ Real.sqrt (1-p) := Real.sqrt_nonneg _
    have hc2 : (Real.sqrt (1-p))^2 = 1-p := Real.sq_sqrt (by linarith)
    have hc : 1/2 ≤ Real.cos θ := by rw [hcos]; nlinarith
    have hs2 : Real.sqrt ℓ ≤ Real.sin (2*θ) := by
      rw [Real.sin_two_mul, hsin]
      have hroot := Real.sqrt_le_sqrt hlower
      have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2*Real.sqrt p)
      nlinarith
    have hwin : 1 ≤ (window ℓ:ℝ)*Real.sin (2*θ) :=
      hwindow.1.trans (mul_le_mul_of_nonneg_left hs2 (Nat.cast_nonneg _))
    have hl := prepared_aa_uniform_success_lower A j S θ (window ℓ) hA (window_pos ℓ)
      hθ0 hθ1 hmass hwin
    linarith [measureProb_nonneg (preparedAAState A j) S]
  · have hp' : 1/2 ≤ MeasureProb (preparedAAState A j) S := le_of_not_gt hp
    linarith

/-- Every selected amplification word uses at most twice the window size plus one preparation
accesses when the preparation matrix is unitary. -/
theorem selected_count_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    {M : ℕ} (z : Bool × Fin M) :
    preparedInputQueries (preparedAAWord j (chosenRound z)) ≤ 2*M+1 := by
  rw [(prepared_aa_separate_access_word A j S (chosenRound z) hA).2.2.1]
  unfold chosenRound
  split_ifs <;> omega

/-- For a unitary preparation and positive window size M, the expected preparation access count
under the joint law is at most 2M + 1. -/
theorem expected_count_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) :
    (jointLaw A hA j S M hM).expect
      (fun x => (preparedInputQueries (preparedAAWord j (chosenRound x.1)) : ℝ)) ≤ 2*(M:ℝ)+1 := by
  let law := jointLaw A hA j S M hM
  calc
    _ ≤ ∑ x, law.prob x * (2*(M:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (law.nonneg x)
      (try dsimp only)
      exact_mod_cast selected_count_le A hA j S x.1
    _ = 2*(M:ℝ)+1 := by rw [← Finset.sum_mul, law.sum_one, one_mul]

/-- For a unitary preparation, a positive lower bound on an initial marked probability at most
one yields actual success at least 1/8 and expected preparation access count at most five
divided by the square root of that lower bound. -/
theorem lower_bound_schedule {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hlower : ℓ ≤ MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) :
    1/8 ≤ (jointLaw A hA j S (window ℓ) (window_pos ℓ)).expect
      (fun x => if x.2 ∈ S then 1 else 0) ∧
    (jointLaw A hA j S (window ℓ) (window_pos ℓ)).expect
      (fun x => (preparedInputQueries (preparedAAWord j (chosenRound x.1)) : ℝ)) ≤
      5 / Real.sqrt ℓ := by
  constructor
  · rw [success_is_actual]
    exact lower_bound_success A hA j S ℓ hℓ hlower hp1
  · have hw := (window_bounds ℓ hℓ (hlower.trans hp1)).2
    have hr0 : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
    have hr1 : Real.sqrt ℓ ≤ 1 := Real.sqrt_le_one.mpr (hlower.trans hp1)
    have h1 : 1 ≤ 1/Real.sqrt ℓ := (le_div_iff₀ hr0).mpr (by simpa using! hr1)
    have hc := expected_count_le A hA j S (window ℓ) (window_pos ℓ)
    linarith [show 2 / Real.sqrt ℓ = 2 * (1/Real.sqrt ℓ) by ring,
      show 5 / Real.sqrt ℓ = 5 * (1/Real.sqrt ℓ) by ring]

/-- For positive G, c, and eta, if at least an eta fraction of the observable indices have
amplitude norm at least cG and all encoded values are bounded by G, the schedule based on
eta c^2 succeeds with probability at least 1/8. Its expected preparation access count is at
most 5/(c sqrt(eta)). -/
theorem balanced_source_schedule {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G c η : ℝ) (hG : 0 < G) (hc : 0 < c) (hη : 0 < η)
    (hvalue : ∀ v, ‖value v‖ ≤ G) (S : Finset (Reg n))
    (hcard : η * (2:ℝ)^n ≤ S.card)
    (hbig : ∀ j ∈ S, c * G ≤ ‖target b value j‖) :
    let A := preparation b value G
    let law := jointLaw A (preparation_unitary b value G hG hvalue) (seed n m)
      (goodSet n m) (window (η*c^2)) (window_pos (η*c^2))
    law.expect (fun x => if x.2 ∈ goodSet n m then 1 else 0) ≥ 1/8 ∧
    law.expect (fun x => (preparedInputQueries
      (preparedAAWord (seed n m) (chosenRound x.1)) : ℝ)) ≤ 5/(c*Real.sqrt η) := by
  have hs := lower_bound_schedule (preparation b value G) (preparation_unitary b value G hG hvalue)
    (seed n m) (goodSet n m) (η*c^2) (by positivity)
    (balanced_actual_probability b value G c η hG hc hη S hcard hbig)
    (actual_probability_le_one b value G hG hvalue)
  refine ⟨hs.1, ?_⟩
  have hroot : Real.sqrt (η*c^2) = c*Real.sqrt η := by
    rw [Real.sqrt_mul hη.le, Real.sqrt_sq hc.le]
    ring
  simpa only [hroot] using! hs.2

/-- For a unitary preparation with positive marked probability at most one, the marked component
after any number of amplification rounds is a complex scalar multiple of its original marked
component. -/
theorem aa_good_span {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1) (k : ℕ) :
    ∃ z : ℂ, Collapse (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) S =
      z • Collapse (preparedAAState A j) S := by
  let p := MeasureProb (preparedAAState A j) S
  by_cases hp : p < 1
  · let θ := Real.arcsin (Real.sqrt p)
    have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp0)
    have hslt : Real.sqrt p < 1 := by nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg p]
    have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hslt
    have hsin : Real.sin θ = Real.sqrt p := Real.sin_arcsin
      (by linarith [Real.sqrt_nonneg p]) (Real.sqrt_le_one.mpr hp1)
    have hmass : p = (Real.sin θ)^2 := by rw [hsin, Real.sq_sqrt hp0.le]
    refine ⟨((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ), ?_⟩
    ext i
    by_cases hi : i ∈ S
    · simpa only [collapse_apply, hi, if_true, Pi.smul_apply, smul_eq_mul] using!
        actual_marked_amplitude A j S θ k hA hθ0 hθ1 hmass i hi
    · simp [collapse_apply, hi]
  · have hpEq : MeasureProb (preparedAAState A j) S = 1 := le_antisymm hp1 (le_of_not_gt hp)
    refine ⟨(-1:ℂ)^k, ?_⟩
    rw [(prepared_aa_endpoint_states A j S k hA).2 hpEq]
    ext i
    by_cases hi : i ∈ S <;> simp [collapse_apply, hi]

/-- For a bounded observable preparation with nonzero target, the successful index amplitudes
after any amplification round count lie in the complex span of `postselected`. -/
theorem amplified_index_span {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) (k : ℕ) :
    ∃ z : ℂ, (fun j => Run (preparedMark (goodSet n m))
      (preparedAACircuit (preparation b value G) (seed n m) k) (Ket (seed n m))
        (j,(ZeroStr m,false))) = z • postselected b value G := by
  let A := preparation b value G
  let p := MeasureProb (preparedAAState A (seed n m)) (goodSet n m)
  have hp0 : 0 < p := by
    change 0 < MeasureProb (preparation b value G *ᵥ Ket (seed n m)) (goodSet n m)
    rw [actual_success_probability b value G hG]
    exact div_pos (targetNormSq_pos b value hu) (by positivity)
  have hpr : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hp0).ne'
  obtain ⟨z,hz⟩ := aa_good_span A (preparation_unitary b value G hG hvalue)
    (seed n m) (goodSet n m) hp0 (actual_probability_le_one b value G hG hvalue) k
  refine ⟨z*(Real.sqrt p : ℂ), ?_⟩
  ext j
  have hi : (j,(ZeroStr m,false)) ∈ goodSet n m := by simp [goodSet]
  have hcoord := congrFun hz (j,(ZeroStr m,false))
  simp only [collapse_apply, hi, if_true, Pi.smul_apply, smul_eq_mul] at hcoord
  rw [hcoord]
  change z * (preparation b value G *ᵥ Ket (seed n m)) (j,(ZeroStr m,false)) =
    (z*(Real.sqrt p : ℂ)) * ((preparation b value G *ᵥ Ket (seed n m))
      (j,(ZeroStr m,false)) / (Real.sqrt p : ℂ))
  field_simp

/-- Multiplying a state by a complex scalar multiplies its outer product by the squared norm of
that scalar. -/
theorem outerProduct_scale {I : Type} [Fintype I] [DecidableEq I] (v : QState I) (z : ℂ) :
    outerProduct (z • v) = ((‖z‖^2 : ℝ) : ℂ) • outerProduct v := by
  have hz : ((‖z‖^2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring
  ext i j
  simp only [outerProduct_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hz]
  ring

/-- If a state lies in the complex span of a normalized state, its outer product is the
normalized state's outer product multiplied by the sum of its own squared amplitude norms. -/
theorem outerProduct_of_span {I : Type} [Fintype I] [DecidableEq I]
    (u v : QState I) (hu : Normalized u) (hspan : ∃ z : ℂ, v=z • u) :
    outerProduct v = (((∑ i, ‖v i‖^2 : ℝ)) : ℂ) • outerProduct u := by
  obtain ⟨z,rfl⟩ := hspan
  have hmass : (∑ i, ‖(z • u) i‖^2) = ‖z‖^2 := by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [hu, mul_one]
  rw [outerProduct_scale, hmass]

/-- The unnormalized successful index density formed by averaging the outer products of the
successful amplitude vectors over the Boolean and round choices of the schedule. -/
noncomputable def successfulDensity {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (M : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ z : Bool × Fin M, ((1/(2*(M:ℝ)) : ℝ) : ℂ) • outerProduct
    (fun j => runState (preparation b value G) (seed n m) (goodSet n m) z (j,(ZeroStr m,false)))

/-- For bounded observable values and a nonzero target, the successful density equals the
schedule's success mass times the outer product of the normalized postselected state. -/
theorem actual_successful_density {n m : ℕ} (b : Reg n → Reg m) (value : Reg m → ℂ)
    (G : ℝ) (hG : 0 < G) (hvalue : ∀ v, ‖value v‖ ≤ G) (hu : target b value ≠ 0) (M : ℕ) :
    successfulDensity b value G M =
      ((success (preparation b value G) (seed n m) (goodSet n m) M : ℝ) : ℂ) •
        outerProduct (postselected b value G) := by
  have heach (z : Bool × Fin M) :
      outerProduct (fun j => runState (preparation b value G) (seed n m) (goodSet n m) z (j,(ZeroStr m,false))) =
      ((MeasureProb (runState (preparation b value G) (seed n m) (goodSet n m) z) (goodSet n m) : ℝ) : ℂ) •
        outerProduct (postselected b value G) := by
    rw [measure_good]
    exact outerProduct_of_span _ _ (actual_postselection b value G hG hu).2
      (amplified_index_span b value G hG hvalue hu (chosenRound z))
  simp only [successfulDensity, heach, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [success, Complex.ofReal_sum, Complex.ofReal_mul]

/-- For a unitary preparation with marked probability p in (0, 1], every positive window M
satisfying M sqrt(p) at least one gives randomized schedule success at least 1/8. -/
theorem mature_window_success {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) (hp0 : 0 < MeasureProb (preparedAAState A j) S)
    (hp1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hmature : 1 ≤ (M:ℝ)*Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    1/8 ≤ success A j S M := by
  let p := MeasureProb (preparedAAState A j) S
  rw [success_formula A j S M hM]
  have hnonneg : 0 ≤ (∑ i : Fin M, MeasureProb
      (Run (preparedMark S) (preparedAACircuit A j i.val) (Ket j)) S)/(M:ℝ) := by
    apply div_nonneg (Finset.sum_nonneg (fun _ _ => measureProb_nonneg _ _))
    positivity
  by_cases hp : p < 1/2
  · let θ := Real.arcsin (Real.sqrt p)
    have hsquare : (Real.sqrt p)^2 = p := Real.sq_sqrt hp0.le
    have hsin : Real.sin θ = Real.sqrt p := Real.sin_arcsin
      (by linarith [Real.sqrt_nonneg p]) (Real.sqrt_le_one.mpr hp1)
    have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp0)
    have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr (by nlinarith [Real.sqrt_nonneg p])
    have hmass : p = (Real.sin θ)^2 := by rw [hsin, hsquare]
    have hcos : Real.cos θ = Real.sqrt (1-p) := by
      dsimp only [θ]
      rw [Real.cos_arcsin, hsquare]
    have hc : 1/2 ≤ Real.cos θ := by
      rw [hcos]
      nlinarith [Real.sqrt_nonneg (1-p), Real.sq_sqrt (show 0 ≤ 1-p by linarith)]
    have hs2 : Real.sqrt p ≤ Real.sin (2*θ) := by
      rw [Real.sin_two_mul, hsin]
      have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2*Real.sqrt p)
      nlinarith
    have hwin : 1 ≤ (M:ℝ)*Real.sin (2*θ) :=
      hmature.trans (mul_le_mul_of_nonneg_left hs2 (Nat.cast_nonneg _))
    have hl := prepared_aa_uniform_success_lower A j S θ M hA hM hθ0 hθ1 hmass hwin
    linarith [measureProb_nonneg (preparedAAState A j) S]
  · have hp' : 1/2 ≤ MeasureProb (preparedAAState A j) S := le_of_not_gt hp
    linarith

end Qatlib.Papers.KoopmanSim26.StatePrep.LowerSchedule
