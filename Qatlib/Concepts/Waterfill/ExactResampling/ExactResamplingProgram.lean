/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityLevelSubgoalQuan

/-!
# Exact water-level resampling circuits

`resamplingExactSchedule` tunes an amplitude-amplification angle and scale to reach the selected
branch exactly. `resamplingPaidWord_actual` verifies the expanded circuit and its source-query,
data-query, and fixed-gate counts; `resamplingExactOutput_actual` identifies the normalized
clipped-fill output, its target overlap, and its query bound.

This construction formalizes ingredients of quantum rejection sampling
[OzolsRoettelerRoland2013] in the setting of [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.Waterfill.ExactResampling
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- The natural ceiling of `π / (4 * arcsin β) - 1 / 2`, used as the number of exact
amplitude-amplification rounds. -/
def resamplingExactRounds (β : ℝ) : ℕ :=
  Nat.ceil (Real.pi / (4 * Real.arcsin β) - 1 / 2)

/-- The angle `π / (2 * (2 * resamplingExactRounds β + 1))` that makes the total amplification
angle equal to `π / 2`. -/
def resamplingExactAngle (β : ℝ) : ℝ :=
  Real.pi / (2 * (2 * (resamplingExactRounds β : ℝ) + 1))

/-- The scale `sin (resamplingExactAngle β) / β` applied to the initial selected amplitude. -/
def resamplingExactScale (β : ℝ) : ℝ := Real.sin (resamplingExactAngle β) / β

/-- The clipped-fill amplitude divided by the source amplitude, with value zero at a zero source
coordinate. -/
def resamplingLevelRatio {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ) (i : Fin m) : ℝ :=
  if π i = 0 then 0 else levelFill π σ γ i / (π i : ℝ)

/-- The coin payoff rotation with probability parameter equal to the square of the scaled
fill-to-source ratio at each source coordinate. -/
def resamplingLevelFilter {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ) :
    Matrix ((Fin m × Fin D) × Bool) ((Fin m × Fin D) × Bool) ℂ :=
  payoffRotation (fun p => (a * resamplingLevelRatio π σ γ p.1) ^ 2)

/-- Extends the source-preparation matrix by the identity on the Boolean coin register. -/
def resamplingEmbeddedOracle {m D : ℕ}
    (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) :=
  TensorGate U (1 : Matrix Bool Bool ℂ)

/-- The source preparation followed by the scaled water-level coin filter, expressed as a matrix
product. -/
def resamplingLevelPrepare {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) :=
  resamplingLevelFilter π σ γ a * resamplingEmbeddedOracle U

/-- The permutation matrix that flips the Boolean coin and leaves the source and ancillary
registers unchanged. -/
def resamplingCoinSwap (m D : ℕ) :
    Matrix ((Fin m × Fin D) × Bool) ((Fin m × Fin D) × Bool) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2 = !y.2 then 1 else 0

/-- Expands a prepared instruction into source-oracle calls and known filter or marking gates,
using adjoints for backward instructions. Ordinary fixed gates are retained unchanged. -/
def resamplingExpandStep {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ) :
    PreparedStep ((Fin m × Fin D) × Bool) → List (PreparedStep ((Fin m × Fin D) × Bool))
  | .prepareForward => [.gate (resamplingLevelFilter π σ γ a), .prepareForward]
  | .prepareBackward => [.prepareBackward, .gate (resamplingLevelFilter π σ γ a)ᴴ]
  | .dataForward => [.gate (preparedMark (waterEvent m D))]
  | .dataBackward => [.gate (preparedMark (waterEvent m D))ᴴ]
  | .gate V => [.gate V]

/-- Expands the prepared amplitude-amplification word for `t` rounds and adds a coin swap so
that the selected output lies in the false-coin branch. -/
def resamplingPaidWord {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (j₀ : Fin m × Fin D) (t : ℕ) : List (PreparedStep ((Fin m × Fin D) × Bool)) :=
  .gate (resamplingCoinSwap m D) ::
    ((preparedAAWord (j₀, false) t).map (resamplingExpandStep π σ γ a)).flatten

/-- The paid resampling word with scale and round count chosen from the square root of the
clipped-fill mass. -/
def resamplingExactWord {m D : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (j₀ : Fin m × Fin D) : List (PreparedStep ((Fin m × Fin D) × Bool)) :=
  let β := Real.sqrt (levelMass π σ γ)
  resamplingPaidWord π σ γ (resamplingExactScale β) j₀ (resamplingExactRounds β)

/-- The state obtained by evaluating the exact resampling word with the embedded source oracle
and applying it to the starting basis state with false coin. -/
def resamplingExactOutput {m D : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D) :=
  ApplyGate (evaluatePrepared 1 (resamplingEmbeddedOracle U)
    (resamplingExactWord π σ γ j₀)) (Ket (j₀, false))

/-- Combines real weights with an ancillary state family in the false-coin branch, assigning
zero amplitude to the true-coin branch. -/
def resamplingFamily {m D : ℕ} (v : Fin m → ℝ) (ξ : Fin m → QState (Fin D)) :
    QState ((Fin m × Fin D) × Bool) :=
  fun p => if p.2 then 0 else (v p.1.1 : ℂ) * ξ p.1.1 p.1.2

/-- For `0 < β ≤ 1`, proves a scale in `[1/2, 1]`, a positive angle at most `π/2`, the exact
total-angle identity, and the query estimate `2 * rounds + 1 ≤ π / (2 * β) + 2`; see
[OzolsRoettelerRoland2013] for the quantum rejection-sampling context. At `β = 1`, the
schedule uses zero rounds and scale one. -/
theorem resamplingExactSchedule :
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    1 / 2 ≤ resamplingExactScale β ∧ resamplingExactScale β ≤ 1 ∧
    0 < resamplingExactAngle β ∧ resamplingExactAngle β ≤ Real.pi / 2 ∧
    Real.sin (resamplingExactAngle β) = resamplingExactScale β * β ∧
    (2 * (resamplingExactRounds β : ℝ) + 1) * resamplingExactAngle β = Real.pi / 2 ∧
    ((2 * resamplingExactRounds β + 1 : ℕ) : ℝ) ≤ Real.pi / (2 * β) + 2 ∧
    (β = 1 → resamplingExactRounds β = 0 ∧ resamplingExactScale β = 1) := by
  intro β hβ hβ1
  let θ := Real.arcsin β
  let q := Real.pi/(4*θ)-1/2
  let t := resamplingExactRounds β
  let α := resamplingExactAngle β
  have hθ : 0 < θ := Real.arcsin_pos.mpr hβ
  have hθ1 : θ ≤ Real.pi/2 := Real.arcsin_le_pi_div_two β
  have hsin : Real.sin θ = β := Real.sin_arcsin (by linarith) hβ1
  have hq : 0 ≤ q := by
    dsimp [q]
    rw [sub_nonneg, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hlo : q ≤ (t : ℝ) := Nat.le_ceil q
  have hhi : (t : ℝ) < q+1 := Nat.ceil_lt_add_one hq
  have hqθ : q*θ = Real.pi/4-θ/2 := by
    dsimp [q]
    field_simp [ne_of_gt hθ]

  have hloθ := mul_le_mul_of_nonneg_right hlo hθ.le
  have hhiθ := mul_lt_mul_of_pos_right hhi hθ
  have hleft : Real.pi/2 ≤ (2*(t : ℝ)+1)*θ := by nlinarith
  have hright : (2*(t : ℝ)+1)*θ < Real.pi/2+2*θ := by nlinarith
  have hden : 0 < 2*(2*(t : ℝ)+1) := by positivity
  have hα : 0 < α := div_pos Real.pi_pos hden
  have hα1 : α ≤ Real.pi/2 := by
    change Real.pi/(2*(2*(t : ℝ)+1)) ≤ Real.pi/2
    apply (div_le_iff₀ hden).mpr
    have ht0 := Nat.cast_nonneg (α := ℝ) t
    nlinarith [Real.pi_pos]
  have hαθ : α ≤ θ := by
    change Real.pi/(2*(2*(t : ℝ)+1)) ≤ θ
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hαeq : (2*(t : ℝ)+1)*α = Real.pi/2 := by
    dsimp [α,resamplingExactAngle]
    change (2*(t : ℝ)+1)*(Real.pi/(2*(2*(t : ℝ)+1))) = _
    field_simp
  have hsin_le : Real.sin α ≤ β := by
    rw [← hsin]
    exact Real.monotoneOn_sin
      ⟨by linarith [Real.pi_pos], hα1⟩
      ⟨by linarith [Real.pi_pos], hθ1⟩ hαθ
  have hsin_half : β/2 ≤ Real.sin α := by
    by_cases ht0 : t = 0
    · have htR : (t : ℝ) = 0 := by rw [ht0]; norm_num
      have hθeq : θ = Real.pi/2 := by rw [htR] at hleft; linarith
      have hβeq : β = 1 := by rw [hθeq, Real.sin_pi_div_two] at hsin; exact hsin.symm
      have hαeq' : α = Real.pi/2 := by rw [htR] at hαeq; simpa using! hαeq
      rw [hβeq,hαeq',Real.sin_pi_div_two]
      norm_num
    · by_cases ht1 : t = 1
      · have hαeq' : α = Real.pi/6 := by
          change Real.pi/(2*(2*(t : ℝ)+1)) = _
          rw [ht1]; norm_num
        rw [hαeq',Real.sin_pi_div_six]
        linarith
      · have hθquarter : θ ≤ Real.pi/4 := by
          by_contra hn
          have hq1 : q ≤ 1 := by
            dsimp [q]
            apply (sub_le_iff_le_add).mpr
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith [Real.pi_pos]
          have ht_le : t ≤ 1 := Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using! hq1)
          omega
        have hhalfα : θ/2 ≤ α := by
          change θ/2 ≤ Real.pi/(2*(2*(t : ℝ)+1))
          apply (le_div_iff₀ hden).mpr
          nlinarith
        have hs0 : 0 ≤ Real.sin (θ/2) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
        have hdouble : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
          have he := Real.sin_two_mul (θ/2)
          rw [show 2*(θ/2) = θ by ring] at he
          exact he
        have hmono : Real.sin (θ/2) ≤ Real.sin α :=
          Real.monotoneOn_sin ⟨by linarith [Real.pi_pos],by linarith⟩
            ⟨by linarith [Real.pi_pos],hα1⟩ hhalfα
        nlinarith [Real.cos_le_one (θ/2)]
  have hqueries : ((2*t+1 : ℕ) : ℝ) ≤ Real.pi/(2*β)+2 := by
    have hβθ : β ≤ θ := by rw [← hsin]; exact Real.sin_le hθ.le
    have hdiv : Real.pi/(2*θ) ≤ Real.pi/(2*β) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
    have he : 2*(Real.pi/(4*θ)) = Real.pi/(2*θ) := by field_simp; ring
    dsimp [q] at hhi
    push_cast
    linarith
  have hend : β = 1 → t = 0 ∧ resamplingExactScale β = 1 := by
    intro hb
    have hθeq : θ = Real.pi/2 := by simp [θ,hb,Real.arcsin_one]
    have hqzero : q = 0 := by
      dsimp [q]
      rw [hθeq]
      field_simp [Real.pi_ne_zero]
      ring
    have htzero : t = 0 := by change Nat.ceil q = 0; rw [hqzero]; exact Nat.ceil_zero
    refine ⟨htzero,?_⟩
    unfold resamplingExactScale
    change Real.sin α/β = 1
    have hαeq' : α = Real.pi/2 := by
      rw [htzero, Nat.cast_zero] at hαeq
      simpa using! hαeq
    rw [hαeq',Real.sin_pi_div_two,hb,div_one]
  refine ⟨?_,?_,hα,hα1,?_,hαeq,hqueries,hend⟩
  · unfold resamplingExactScale
    exact (le_div_iff₀ hβ).mpr (by linarith)
  · unfold resamplingExactScale
    exact (div_le_iff₀ hβ).mpr (by simpa using! hsin_le)
  · unfold resamplingExactScale
    exact (div_mul_cancel₀ _ hβ.ne').symm

/-- For nonnegative tables and level, proves that each fill-to-source ratio lies in `[0, 1]` and
recovers the clipped fill when multiplied by the source amplitude. -/
theorem resamplingLevelRatio_bounds {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (h : ∀ i, 0 ≤ π i ∧ 0 ≤ σ i) (hγ : 0 ≤ γ) (i : Fin m) :
    0 ≤ resamplingLevelRatio π σ γ i ∧ resamplingLevelRatio π σ γ i ≤ 1 ∧
    (π i : ℝ)*resamplingLevelRatio π σ γ i = levelFill π σ γ i := by
  have hp : (0 : ℝ) ≤ π i := by exact_mod_cast (h i).1
  have hs : (0 : ℝ) ≤ σ i := by exact_mod_cast (h i).2
  have hfill : 0 ≤ levelFill π σ γ i := le_min hp (mul_nonneg hγ hs)
  have hle : levelFill π σ γ i ≤ (π i : ℝ) := min_le_left _ _
  by_cases hi : π i = 0
  · have hz : levelFill π σ γ i = 0 := by
      unfold levelFill
      rw [hi,Rat.cast_zero,min_eq_left (mul_nonneg hγ hs)]
    simp [resamplingLevelRatio,hi,hz]
  · have hpi : (π i : ℝ) ≠ 0 := by exact_mod_cast hi
    have hpos : (0 : ℝ) < π i := lt_of_le_of_ne hp hpi.symm
    simp only [resamplingLevelRatio,if_neg hi]
    refine ⟨div_nonneg hfill hp, (div_le_one hpos).mpr hle, ?_⟩
    field_simp

/-- The scaled water-level filter is unitary when the tables and level are nonnegative and the
scale lies in `[0, 1]`. -/
theorem resamplingLevelFilter_unitary {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (h : ∀ i, 0 ≤ π i ∧ 0 ≤ σ i) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    resamplingLevelFilter (D := D) π σ γ a ∈ Matrix.unitaryGroup _ ℂ := by
  apply payoffRotation_mem_unitaryGroup
  intro p
  have hr := resamplingLevelRatio_bounds π σ γ h hγ p.1
  have hx : 0 ≤ a*resamplingLevelRatio π σ γ p.1 := mul_nonneg ha hr.1
  have hx1 : a*resamplingLevelRatio π σ γ p.1 ≤ 1 := by
    calc
      _ ≤ a*1 := mul_le_mul_of_nonneg_left hr.2.1 ha
      _ ≤ 1 := by simpa using! ha1
  exact ⟨sq_nonneg _,by nlinarith⟩

/-- For normalized ancillary states, the squared norm of the weighted true-coin family is the
sum of the squared real weights. -/
theorem resamplingSelected_normSq (m D : ℕ) (w : Fin m → ℝ)
    (ξ : Fin m → QState (Fin D)) (hξ : ∀ i, Normalized (ξ i)) :
    (∑ p : ((Fin m × Fin D) × Bool), Complex.normSq
      (if p.2 then (w p.1.1 : ℂ)*ξ p.1.1 p.1.2 else 0)) = ∑ i, (w i)^2 := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,if_false,if_true,
    Complex.normSq_zero,add_zero,Complex.normSq_mul,Complex.normSq_ofReal]
  have hnorm (i : Fin m) : (∑ d, Complex.normSq (ξ i d)) = 1 := by
    simpa only [← Complex.sq_norm] using! hξ i
  simp_rw [← Finset.mul_sum,hnorm,mul_one]
  simp only [pow_two]

/-- Proves unitarity of the filter and the filtered source preparation under nonnegative input
and scale bounds; see [OzolsRoettelerRoland2013] for the quantum rejection-sampling context.
The marked collapse has amplitudes `a * levelFill` times the ancillary states, and its
probability is `a^2 * levelMass`. -/
theorem resamplingLevelPrepare_actual :
  ∀ (m D : ℕ) (π σ : Fin m → ℚ) (γ a : ℝ),
    (∀ i, 0 ≤ π i ∧ 0 ≤ σ i) → 0 ≤ γ → 0 ≤ a → a ≤ 1 →
    (resamplingLevelFilter (D := D) π σ γ a ∈ Matrix.unitaryGroup _ ℂ) ∧
    ∀ (ξ : Fin m → QState (Fin D))
      (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D),
      (∀ i, Normalized (ξ i)) → U ∈ Matrix.unitaryGroup _ ℂ →
      U *ᵥ Ket j₀ = waterSource π ξ →
      resamplingLevelPrepare π σ γ a U ∈ Matrix.unitaryGroup _ ℂ ∧
      Collapse (ApplyGate (resamplingLevelPrepare π σ γ a U) (Ket (j₀, false)))
        (waterEvent m D) =
          (fun p => if p.2 then ((a * levelFill π σ γ p.1.1 : ℝ) : ℂ) *
            ξ p.1.1 p.1.2 else 0) ∧
      MeasureProb (ApplyGate (resamplingLevelPrepare π σ γ a U) (Ket (j₀, false)))
        (waterEvent m D) = a ^ 2 * levelMass π σ γ := by
  intro m D π σ γ a h hγ ha ha1
  have hf := resamplingLevelFilter_unitary (D := D) π σ γ a h hγ ha ha1
  refine ⟨hf,?_⟩
  intro ξ U j₀ hξ hU hsource
  have hprepare : resamplingLevelPrepare π σ γ a U ∈ Matrix.unitaryGroup _ ℂ :=
    mul_mem hf (tensorGate_unitary hU (Submonoid.one_mem _))
  have hcol (p : Fin m × Fin D) : U p j₀ = (π p.1 : ℂ)*ξ p.1 p.2 := by
    have he := congrFun hsource p
    have hk : (U *ᵥ Ket j₀) p = U p j₀ := applyGate_eq_mulVec_ket U j₀ p
    simpa only [waterSource,hk] using! he
  have hcollapse : Collapse (ApplyGate (resamplingLevelPrepare π σ γ a U) (Ket (j₀,false)))
      (waterEvent m D) =
      (fun p => if p.2 then ((a*levelFill π σ γ p.1.1 : ℝ) : ℂ)*ξ p.1.1 p.1.2 else 0) := by
    change Collapse (payoffPreparation U (fun p => (a*resamplingLevelRatio π σ γ p.1)^2) *ᵥ
      Ket (j₀,false)) _ = _
    rw [payoffPreparation_mulVec_ket]
    funext p
    obtain ⟨⟨i,d⟩,b⟩ := p
    cases b
    · simp [collapse_apply,waterEvent]
    · have hr := resamplingLevelRatio_bounds π σ γ h hγ i
      have hsqrt : Real.sqrt ((a*resamplingLevelRatio π σ γ i)^2) =
          a*resamplingLevelRatio π σ γ i := Real.sqrt_sq (mul_nonneg ha hr.1)
      simp only [collapse_apply,waterEvent,Finset.mem_filter,Finset.mem_univ,and_true,
        if_true,if_false,Bool.false_eq_true,payoffRotation_apply,hsqrt,hcol]
      have he : (π i : ℂ)*(a*resamplingLevelRatio π σ γ i : ℝ) =
          ((a*levelFill π σ γ i : ℝ) : ℂ) := by
        rw [← Complex.ofReal_ratCast,← Complex.ofReal_mul]
        congr 1
        nlinarith [hr.2.2]
      calc
        _ = ((π i : ℂ)*(a*resamplingLevelRatio π σ γ i : ℝ))*ξ i d := by ring
        _ = _ := by rw [he]
  refine ⟨hprepare,hcollapse,?_⟩
  rw [← sum_normSq_collapse,hcollapse]
  calc
    _ = ∑ i : Fin m, (a*levelFill π σ γ i)^2 := by
      simpa only [← Complex.sq_norm] using!
        resamplingSelected_normSq m D (fun i => a*levelFill π σ γ i) ξ hξ
    _ = _ := by simp only [mul_pow,levelMass,Finset.mul_sum]

/-- The Boolean coin-swap matrix is unitary for every source and ancillary dimension. -/
theorem resamplingCoinSwap_unitary (m D : ℕ) :
    resamplingCoinSwap m D ∈ Matrix.unitaryGroup _ ℂ := by
  have he : resamplingCoinSwap m D = permMatrix
      (fun p : (Fin m × Fin D) × Bool => (p.1,!p.2)) := by
    ext ⟨x,b⟩ ⟨y,c⟩
    simp only [resamplingCoinSwap,permMatrix,Matrix.of_apply,Prod.mk.injEq]
  rw [he]
  exact permMatrix_unitary (by intro p; simp)

/-- Expanding a prepared word preserves its input-query count and removes all data queries. Its
fixed-gate count becomes the original fixed-gate count plus the original input- and
data-query counts. -/
theorem resamplingExpanded_counts {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (cs : List (PreparedStep ((Fin m × Fin D) × Bool))) :
    preparedInputQueries ((cs.map (resamplingExpandStep π σ γ a)).flatten) = preparedInputQueries cs ∧
    preparedDataQueries ((cs.map (resamplingExpandStep π σ γ a)).flatten) = 0 ∧
    preparedFixedGates ((cs.map (resamplingExpandStep π σ γ a)).flatten) =
      preparedFixedGates cs+preparedInputQueries cs+preparedDataQueries cs := by
  induction cs with
  | nil => simp [preparedInputQueries,preparedDataQueries,preparedFixedGates]
  | cons c cs ih =>
    simp only [List.map_cons,List.flatten_cons]
    have he := preparedCounts_append (resamplingExpandStep π σ γ a c)
      ((cs.map (resamplingExpandStep π σ γ a)).flatten)
    rw [he.1,he.2.1,he.2.2,ih.1,ih.2.1,ih.2.2]
    cases c <;> simp [resamplingExpandStep,preparedInputQueries,preparedDataQueries,
      preparedFixedGates,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Evaluating the expanded word with the embedded source oracle equals evaluating the original
word with the water-event marking matrix and filtered source preparation. -/
theorem resamplingExpanded_evaluate {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ)
    (cs : List (PreparedStep ((Fin m × Fin D) × Bool))) :
    evaluatePrepared 1 (resamplingEmbeddedOracle U)
      ((cs.map (resamplingExpandStep π σ γ a)).flatten) =
    evaluatePrepared (preparedMark (waterEvent m D)) (resamplingLevelPrepare π σ γ a U) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons,List.flatten_cons,evaluatePrepared_append,ih,evaluatePrepared]
    cases c <;> simp [resamplingExpandStep,evaluatePrepared,preparedInstruction,
      resamplingLevelPrepare,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- Expansion preserves prepared-circuit validity when the inserted filter and water-event
marking matrices are unitary. -/
theorem resamplingExpanded_valid {m D : ℕ} (π σ : Fin m → ℚ) (γ a : ℝ)
    (hf : resamplingLevelFilter (D := D) π σ γ a ∈ Matrix.unitaryGroup _ ℂ)
    (hm : preparedMark (waterEvent m D) ∈ Matrix.unitaryGroup _ ℂ)
    (cs : List (PreparedStep ((Fin m × Fin D) × Bool))) (hcs : PreparedCircuitValid cs) :
    PreparedCircuitValid ((cs.map (resamplingExpandStep π σ γ a)).flatten) := by
  intro c hc
  obtain ⟨block,hblock,hc⟩ := List.mem_flatten.mp hc
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hblock
  have hstep := hcs s hs
  cases s with
  | gate V =>
    simp only [resamplingExpandStep,List.mem_singleton] at hc
    subst c
    exact hstep
  | dataForward =>
    simp only [resamplingExpandStep,List.mem_singleton] at hc
    subst c
    exact hm
  | dataBackward =>
    simp only [resamplingExpandStep,List.mem_singleton] at hc
    subst c
    exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hm
  | prepareForward =>
    simp [resamplingExpandStep] at hc
    rcases hc with rfl | rfl
    · exact hf
    · trivial
  | prepareBackward =>
    simp [resamplingExpandStep] at hc
    rcases hc with rfl | rfl
    · trivial
    · exact Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hf

/-- Verifies the paid word and gives exactly `2 * t + 1` source queries, zero data queries, and
`4 * t + 2` fixed gates; see [OzolsRoettelerRoland2013] for the quantum rejection-sampling
context. Its evaluated matrix is the prepared amplitude-amplification matrix followed by the
coin swap. -/
theorem resamplingPaidWord_actual :
  ∀ (m D : ℕ) (π σ : Fin m → ℚ) (γ a : ℝ) (j₀ : Fin m × Fin D) (t : ℕ),
    (∀ i, 0 ≤ π i ∧ 0 ≤ σ i) → 0 ≤ γ → 0 ≤ a → a ≤ 1 →
    PreparedCircuitValid (resamplingPaidWord π σ γ a j₀ t) ∧
    preparedInputQueries (resamplingPaidWord π σ γ a j₀ t) = 2 * t + 1 ∧
    preparedDataQueries (resamplingPaidWord π σ γ a j₀ t) = 0 ∧
    preparedFixedGates (resamplingPaidWord π σ γ a j₀ t) = 4 * t + 2 ∧
    ∀ (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ),
      U ∈ Matrix.unitaryGroup _ ℂ →
      evaluatePrepared 1 (resamplingEmbeddedOracle U) (resamplingPaidWord π σ γ a j₀ t) =
        resamplingCoinSwap m D * evaluatePrepared (preparedMark (waterEvent m D))
          (resamplingLevelPrepare π σ γ a U) (preparedAAWord (j₀, false) t) := by
  intro m D π σ γ a j₀ t h hγ ha ha1
  have hf := resamplingLevelFilter_unitary (D := D) π σ γ a h hγ ha ha1
  have hm := (prepared_aa_reflection_and_access (1 : Matrix ((Fin m × Fin D) × Bool) _ ℂ)
    (j₀,false) (waterEvent m D) (Submonoid.one_mem _)).1
  have hw := prepared_aa_separate_access_word (1 : Matrix ((Fin m × Fin D) × Bool) _ ℂ)
    (j₀,false) (waterEvent m D) t (Submonoid.one_mem _)
  have hcounts := resamplingExpanded_counts (D := D) π σ γ a (preparedAAWord (j₀,false) t)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact resamplingCoinSwap_unitary m D
    · exact resamplingExpanded_valid π σ γ a hf hm _ hw.1 c hc
  · change preparedInputQueries _ = _
    simpa only [resamplingPaidWord,preparedInputQueries] using! hcounts.1.trans hw.2.2.1
  · simpa only [resamplingPaidWord,preparedDataQueries] using! hcounts.2.1
  · simp only [resamplingPaidWord,preparedFixedGates,hcounts.2.2,hw.2.1,hw.2.2.1,hw.2.2.2.1]
    omega
  · intro U _hU
    simpa only [resamplingPaidWord,evaluatePrepared,preparedInstruction] using!
      congrArg (resamplingCoinSwap m D * ·) (resamplingExpanded_evaluate π σ γ a U
        (preparedAAWord (j₀,false) t))

/-- Collapsing a normalized state onto an event of probability one leaves the state unchanged. -/
private theorem resamplingFullCollapse {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) (hψ : Normalized ψ) (hS : MeasureProb ψ S = 1) :
    Collapse ψ S = ψ := by
  have hadd : MeasureProb ψ S + MeasureProb ψ Sᶜ = 1 := by
    rw [← measureProb_union ψ disjoint_compl_right,Finset.union_compl,measureProb_univ hψ]
  have hc : MeasureProb ψ Sᶜ = 0 := by linarith
  funext i
  by_cases hi : i ∈ S
  · simp [collapse_apply,hi]
  · have hle : BornProb ψ i ≤ MeasureProb ψ Sᶜ :=
      Finset.single_le_sum (fun k _ => bornProb_nonneg ψ k) (Finset.mem_compl.mpr hi)
    have hz : ψ i = 0 := by
      have hn : ‖ψ i‖^2 = 0 := le_antisymm (by simpa only [hc,BornProb] using! hle) (sq_nonneg _)
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ψ i)])
    simp [collapse_apply,hi,hz]

/-- Applying the coin swap evaluates the original state at the same source and ancillary indices
with the Boolean coin negated. -/
theorem resamplingCoinSwap_apply (m D : ℕ) (ψ : QState ((Fin m × Fin D) × Bool))
    (p : (Fin m × Fin D) × Bool) :
    ApplyGate (resamplingCoinSwap m D) ψ p = ψ (p.1,!p.2) := by
  have he : resamplingCoinSwap m D = permMatrix
      (fun p : (Fin m × Fin D) × Bool => (p.1,!p.2)) := by
    ext ⟨x,b⟩ ⟨y,c⟩
    simp only [resamplingCoinSwap,permMatrix,Matrix.of_apply,Prod.mk.injEq]
  rw [he]
  exact applyGate_permMatrix (by intro p; simp) ψ p

/-- For normalized ancillary states, the inner product of two weighted resampling families is
the real dot product of their weights, cast to the complex numbers. -/
theorem resamplingFamily_inner (m D : ℕ) (v w : Fin m → ℝ)
    (ξ : Fin m → QState (Fin D)) (hξ : ∀ i, Normalized (ξ i)) :
    Inner (resamplingFamily v ξ) (resamplingFamily w ξ) =
      ((∑ i, v i*w i : ℝ) : ℂ) := by
  simp only [inner_apply,resamplingFamily,Fintype.sum_prod_type,Fintype.sum_bool,
    if_true,if_false,Bool.false_eq_true,map_zero,zero_mul,zero_add,map_mul,
    Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (v i : ℂ)*(w i : ℂ)*(∑ d, (starRingEnd ℂ) (ξ i d)*ξ i d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = (v i : ℂ)*(w i : ℂ) := by
      rw [← inner_apply,inner_self_eq_one (hξ i),mul_one]

/-- The clipped-fill mass is at most one when the source table has squared norm one and the
tables and level are nonnegative. -/
theorem resamplingLevelMass_le_one {m : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (h : ∀ i, 0 ≤ π i ∧ 0 ≤ σ i) (hγ : 0 ≤ γ)
    (hπ : (∑ i, (π i : ℝ)^2) = 1) : levelMass π σ γ ≤ 1 := by
  calc
    _ ≤ ∑ i, (π i : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hp : (0 : ℝ) ≤ π i := by exact_mod_cast (h i).1
      have hs : (0 : ℝ) ≤ σ i := by exact_mod_cast (h i).2
      have hf : 0 ≤ levelFill π σ γ i := le_min hp (mul_nonneg hγ hs)
      have hle : levelFill π σ γ i ≤ (π i : ℝ) := min_le_left _ _
      nlinarith
    _ = 1 := hπ

/-- The state inner product is linear in scalar multiplication of its second argument. -/
private theorem resamplingInner_smul_right {I : Type*} [Fintype I] [DecidableEq I] (c : ℂ) (ψ φ : QState I) :
    Inner ψ (c • φ) = c * Inner ψ φ := by
  rw [inner_apply,inner_apply]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- When the initial selected probability is `sin(α)^2` and `(2 * t + 1) * α = π/2`, the
amplified state equals the selected collapse scaled by `1 / sin α`. The statement includes
the endpoint angle `α = π/2`. -/
private theorem resamplingExactAAState {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (α : ℝ) (t : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hα : 0 < α) (hα1 : α ≤ Real.pi/2)
    (htotal : (2*(t:ℝ)+1)*α = Real.pi/2)
    (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin α)^2) :
    ApplyGate (evaluatePrepared (preparedMark S) A (preparedAAWord j₀ t)) (Ket j₀) =
      ((1/Real.sin α : ℝ) : ℂ) • Collapse (preparedAAState A j₀) S := by
  rw [(prepared_aa_separate_access_word A j₀ S t hA).2.2.2.2.2]
  by_cases hlt : α < Real.pi/2
  · rw [prepared_aa_actual_rotation A j₀ S α t hA hα hlt hmass,htotal]
    simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,zero_div,Complex.ofReal_zero,
      zero_smul,zero_add]
  · have heq : α = Real.pi/2 := le_antisymm hα1 (le_of_not_gt hlt)
    have ht : t = 0 := by
      have ht0 : (t : ℝ) = 0 := by rw [heq] at htotal; nlinarith [Real.pi_pos]
      exact_mod_cast ht0
    have hm : MeasureProb (preparedAAState A j₀) S = 1 := by
      simpa only [heq,Real.sin_pi_div_two,one_pow] using! hmass
    rw [(prepared_aa_endpoint_states A j₀ S t hA).2 hm,ht,heq]
    simp only [pow_zero,one_smul,Real.sin_pi_div_two,div_one,Complex.ofReal_one]
    exact (resamplingFullCollapse _ S (normalized_applyGate hA (normalized_ket j₀)) hm).symm

/-- Identifies the exact output as the clipped-fill family normalized by the square root of its
positive mass, and proves normalization, zero true-coin probability, and squared target
overlap `levelDot^2 / levelMass`; see [OzolsRoettelerRoland2013] for the quantum
rejection-sampling context. It also gives the exact source and fixed-gate counts, zero data
queries, and the source-query upper bound `π / (2 * sqrt(levelMass)) + 2`. -/
theorem resamplingExactOutput_actual :
∀ (m D : ℕ) (π σ : Fin m → ℚ) (γ : ℝ),
    (∀ i, 0 ≤ π i ∧ 0 ≤ σ i) → 0 ≤ γ →
    (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
    0 < levelMass π σ γ →
    ∀ (ξ : Fin m → QState (Fin D))
      (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D),
      (∀ i, Normalized (ξ i)) → U ∈ Matrix.unitaryGroup _ ℂ →
      U *ᵥ Ket j₀ = waterSource π ξ →
      resamplingExactOutput π σ γ U j₀ =
        ((1 / Real.sqrt (levelMass π σ γ) : ℝ) : ℂ) •
          resamplingFamily (levelFill π σ γ) ξ ∧
      Normalized (resamplingExactOutput π σ γ U j₀) ∧
      MeasureProb (resamplingExactOutput π σ γ U j₀) (waterEvent m D) = 0 ∧
      Complex.normSq (Inner (resamplingFamily (fun i => (σ i : ℝ)) ξ)
        (resamplingExactOutput π σ γ U j₀)) = levelDot π σ γ ^ 2 / levelMass π σ γ ∧
      preparedInputQueries (resamplingExactWord π σ γ j₀) =
        2 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 1 ∧
      (preparedInputQueries (resamplingExactWord π σ γ j₀) : ℝ) ≤
        Real.pi / (2 * Real.sqrt (levelMass π σ γ)) + 2 ∧
      preparedDataQueries (resamplingExactWord π σ γ j₀) = 0 ∧
      preparedFixedGates (resamplingExactWord π σ γ j₀) =
        4 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 2 := by
  intro m D π σ γ h hγ hπ _hσ hmass ξ U j₀ hξ hU hsource
  let β := Real.sqrt (levelMass π σ γ)
  let a := resamplingExactScale β
  let α := resamplingExactAngle β
  let t := resamplingExactRounds β
  let A := resamplingLevelPrepare π σ γ a U
  let S := waterEvent m D
  have hβ : 0 < β := Real.sqrt_pos_of_pos hmass
  have hβ1 : β ≤ 1 := Real.sqrt_le_one.mpr (resamplingLevelMass_le_one π σ γ h hγ hπ)
  have hβsq : β^2 = levelMass π σ γ := Real.sq_sqrt hmass.le
  obtain ⟨haLow,ha1,hα,hα1,hsin,htotal,hquery,_hend⟩ := resamplingExactSchedule β hβ hβ1
  have ha : 0 < a := by dsimp [a]; linarith
  have hprepare := (resamplingLevelPrepare_actual m D π σ γ a h hγ ha.le ha1).2
    ξ U j₀ hξ hU hsource
  have hA : A ∈ Matrix.unitaryGroup _ ℂ := hprepare.1
  have hm : MeasureProb (preparedAAState A (j₀,false)) S = (Real.sin α)^2 := by
    change MeasureProb (ApplyGate A (Ket (j₀,false))) S = _
    rw [hprepare.2.2,hsin,← hβsq,mul_pow]
  have haa := resamplingExactAAState A (j₀,false) S α t hA hα hα1 htotal hm
  have hword := resamplingPaidWord_actual m D π σ γ a j₀ t h hγ ha.le ha1
  have heval := hword.2.2.2.2 U hU
  have hcoeff : 1/Real.sin α*a = 1/β := by
    rw [show Real.sin α = a*β from hsin]
    field_simp [ne_of_gt ha,ne_of_gt hβ]
  have hout : resamplingExactOutput π σ γ U j₀ =
      ((1/β : ℝ) : ℂ) • resamplingFamily (levelFill π σ γ) ξ := by
    change ApplyGate (evaluatePrepared 1 (resamplingEmbeddedOracle U)
      (resamplingPaidWord π σ γ a j₀ t)) (Ket (j₀,false)) = _
    rw [heval,applyGate_mul,haa]
    funext p
    rw [resamplingCoinSwap_apply]
    simp only [Pi.smul_apply,smul_eq_mul,preparedAAState]
    rw [hprepare.2.1]
    obtain ⟨⟨i,d⟩,b⟩ := p
    have hc : ((1/Real.sin α : ℝ) : ℂ)*((a*levelFill π σ γ i : ℝ) : ℂ) =
        ((1/β : ℝ) : ℂ)*(levelFill π σ γ i : ℂ) := by
      rw [← Complex.ofReal_mul,← Complex.ofReal_mul]
      congr 1
      calc
        _ = (1/Real.sin α*a)*levelFill π σ γ i := by ring
        _ = _ := by rw [hcoeff]
    cases b
    · simpa only [Bool.not_false,resamplingFamily,Bool.false_eq_true,if_true,if_false,← mul_assoc] using!
        congrArg (· * ξ i d) hc
    · simp [resamplingFamily]
  refine ⟨hout,?_,?_,?_,hword.2.1,?_,hword.2.2.1,hword.2.2.2.1⟩
  · apply normalized_applyGate _ (normalized_ket (j₀,false))
    exact hword.1.evaluate_unitary (Submonoid.one_mem _)
      (tensorGate_unitary hU (Submonoid.one_mem _))
  · rw [hout]
    apply Finset.sum_eq_zero
    intro p hp
    have hb : p.2 = true := (Finset.mem_filter.mp hp).2
    simp [BornProb,resamplingFamily,hb]
  · rw [hout,resamplingInner_smul_right,resamplingFamily_inner m D _ _ ξ hξ]
    simp only [Complex.normSq_mul,Complex.normSq_ofReal]
    change (1/β*(1/β))*(levelDot π σ γ*levelDot π σ γ) = _
    rw [← pow_two,← pow_two,div_pow,one_pow,hβsq]
    ring
  · change (preparedInputQueries (resamplingPaidWord π σ γ a j₀ t) : ℝ) ≤ _
    rw [hword.2.1]
    exact hquery

end Qatlib.Concepts.Waterfill.ExactResampling
