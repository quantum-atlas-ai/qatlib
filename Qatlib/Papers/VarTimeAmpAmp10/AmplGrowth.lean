/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.AmplCascade
public import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.TightAASuccessBound
public import Qatlib.Papers.VarTimeAmpAmp10.StopModel.SourceLemma2
public import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.SourceLemma3
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenFinalRoundCalibration
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Odd-angle growth and exact VTAA stage bounds (third executable slice)

The one-round theorem `window_step_recurrence` is the stopped-mass projection of a rotation in
an invariant plane.  Iterating the scalar expression `p * (3 - 4 * p)^2` would be incorrect:
after the first round the reference state of the diffusion is still the original state.  This
module therefore iterates the actual fixed-reference operator.  For an initial split with real
amplitudes `sin θ` and `cos θ`, its `k`-th power has amplitudes
`sin ((2 * k + 1) * θ)` and `cos ((2 * k + 1) * θ)`, and hence stopped mass
`sin ((2 * k + 1) * θ)^2`.  This is the exact `(2k+1)`-fold growth chain behind the fixed-reference
first-round recurrence.

The tight cubic sine bound gives the finite amplification estimate used by Lemma 2.  A derived
first-quarter crossing supplies a final window with stopped mass at least `1/2`; its marking
count is the crossing index computed from `θ`, not a prescribed global count.  Finally, the
source's Lemma 2 stage recurrence, equation (6), and Lemma 3 gain-product bounds are exposed for
chains whose stages carry the repetition counts of this development's `Window` records.

All results are finite and exact.  No `O`/`Ω`/`Θ` statement, asymptotic `T_av`/`T_max` formula,
or measurement of intermediate stop registers is claimed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Papers.VarTimeAmpAmp10.CoherentStop
open Qatlib.Papers.VarTimeAmpAmp10.AmplCascade
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.MainTheorem
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Matrix ComplexConjugate

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.AmplGrowth

variable {a w : ℕ}

/-- The squared complex norm of a real cast is the square of that real number. -/
theorem norm_real_cast_sq (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The fixed-reference plane rotation -/

/-- The pairing of a reference split state with the marked image of an arbitrary vector in the
same stopped/running plane.  Orthogonality and normalization leave only the two diagonal terms. -/
theorem plane_overlap_general (f : Addr a → Bool) (α β x y : ℂ)
    (g b : QState (OReg a w)) (hg : g ∈ stopSub f) (hb : b ∈ contSub f)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    ∑ k, (starRingEnd ℂ) ((α • g + β • b) k) * ((-x) • g + y • b) k =
      (starRingEnd ℂ) β * y - (starRingEnd ℂ) α * x := by
  have hzero : ∀ k : OReg a w,
      (starRingEnd ℂ) (g k) * b k = 0 ∧ (starRingEnd ℂ) (b k) * g k = 0 := by
    intro k
    by_cases hflag : k.2.1 = true
    · by_cases hf : f k.1 = true
      · have hbk : b k = 0 := contCoord f hb k (by simp [hflag, hf])
        simp [hbk]
      · have hgk : g k = 0 := stopCoord f hg k (by simp [hflag, hf])
        simp [hgk]
    · have hgk : g k = 0 := stopCoord f hg k (by simp [hflag])
      simp [hgk]
  have key : ∀ k : OReg a w,
      (starRingEnd ℂ) (α * g k + β * b k) * (-x * g k + y * b k) =
        -((starRingEnd ℂ) α * x) * ((starRingEnd ℂ) (g k) * g k) +
          ((starRingEnd ℂ) β * y) * ((starRingEnd ℂ) (b k) * b k) := by
    intro k
    rw [map_add, map_mul, map_mul]
    linear_combination ((starRingEnd ℂ) α * y) * (hzero k).1 -
      ((starRingEnd ℂ) β * x) * (hzero k).2
  have hgsum : ∑ k, (starRingEnd ℂ) (g k) * g k = 1 := by
    simp only [star_mul_self]
    rw [← Complex.ofReal_sum, hgN]
    push_cast
    rfl
  have hbsum : ∑ k, (starRingEnd ℂ) (b k) * b k = 1 := by
    simp only [star_mul_self]
    rw [← Complex.ofReal_sum, hbN]
    push_cast
    rfl
  have hconv : ∀ k : OReg a w,
      (starRingEnd ℂ) ((α • g + β • b) k) * ((-x) • g + y • b) k =
        (starRingEnd ℂ) (α * g k + β * b k) * (-x * g k + y * b k) := fun k => rfl
  rw [Finset.sum_congr rfl fun k _ => hconv k, Finset.sum_congr rfl fun k _ => key k,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hgsum, hbsum,
    mul_one, mul_one]
  ring

/-- One fixed-reference amplification step on an arbitrary vector in the invariant plane.  The
pairing coefficient is supplied explicitly so that the theorem can be iterated without changing
the reference state. -/
theorem plane_step_general (f : Addr a → Bool) (ψ : QState (OReg a w)) (α β x y S : ℂ)
    (g b : QState (OReg a w)) (hsplit : ψ = α • g + β • b)
    (hg : g ∈ stopSub f) (hb : b ∈ contSub f)
    (hS : ∑ k, (starRingEnd ℂ) ((α • g + β • b) k) * ((-x) • g + y • b) k = S) :
    (reflAbout ψ * stopMark f) *ᵥ (x • g + y • b) =
      (x + 2 * α * S) • g + (-y + 2 * β * S) • b := by
  have hS' : ∑ k, (starRingEnd ℂ) (ψ k) * ((-x) • g + y • b) k = S := by
    rwa [hsplit]
  rw [← Matrix.mulVec_mulVec, mark_split f x y g b hg hb,
    reflAbout_mulVec_eq ψ ((-x) • g + y • b) S hS', hsplit]
  funext r
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- The real sine/cosine form of one fixed-reference step: it advances the plane angle by `2θ`. -/
theorem plane_step_sin_cos (f : Addr a → Bool) (ψ : QState (OReg a w)) (θ φ : ℝ)
    (g b : QState (OReg a w))
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub f) (hb : b ∈ contSub f)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    (reflAbout ψ * stopMark f) *ᵥ ((Real.sin φ : ℂ) • g + (Real.cos φ : ℂ) • b) =
      (Real.sin (φ + 2 * θ) : ℂ) • g + (Real.cos (φ + 2 * θ) : ℂ) • b := by
  have hS0 := plane_overlap_general f (Real.sin θ : ℂ) (Real.cos θ : ℂ)
    (Real.sin φ : ℂ) (Real.cos φ : ℂ) g b hg hb hgN hbN
  have hS : ∑ k, (starRingEnd ℂ)
        (((Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b) k) *
        ((-(Real.sin φ : ℂ)) • g + (Real.cos φ : ℂ) • b) k =
      (Real.cos (θ + φ) : ℂ) := by
    rw [hS0, Real.cos_add]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  rw [plane_step_general f ψ (Real.sin θ : ℂ) (Real.cos θ : ℂ)
    (Real.sin φ : ℂ) (Real.cos φ : ℂ) (Real.cos (θ + φ) : ℂ) g b hsplit hg hb hS]
  have hsin : Real.sin φ + 2 * Real.sin θ * Real.cos (θ + φ) =
      Real.sin (φ + 2 * θ) := by
    rw [Real.cos_add, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
    linear_combination (-2 * Real.sin φ) * (Real.sin_sq_add_cos_sq θ)
  have hcos : -Real.cos φ + 2 * Real.cos θ * Real.cos (θ + φ) =
      Real.cos (φ + 2 * θ) := by
    rw [Real.cos_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul]
    ring
  rw [← hsin, ← hcos]
  push_cast
  rfl

/-- **Exact odd-angle operator iteration.** The `k`-th power of the fixed-reference round
maps the initial `sin θ`/`cos θ` split to the split at angle `(2k+1)θ`. -/
theorem window_power_sin_cos (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ)
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    ∀ k : ℕ, (stepOf ω) ^ k *ᵥ ψ =
      (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ) • g +
        (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ) • b := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec, hsplit]
      norm_num
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, stepOf, hω]
      have hstep := plane_step_sin_cos ω.pred ψ θ ((2 * (k : ℝ) + 1) * θ)
        g b hsplit hg hb hgN hbN
      rw [hstep]
      have hang : (2 * (k : ℝ) + 1) * θ + 2 * θ = (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ := by
        push_cast
        ring
      rw [hang]

/-- The exact odd-angle formula for the repetition word stored in a window. -/
theorem window_round_sin_cos (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ)
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    roundOf ω *ᵥ ψ =
      (Real.sin ((2 * (ω.reps : ℝ) + 1) * θ) : ℂ) • g +
        (Real.cos ((2 * (ω.reps : ℝ) + 1) * θ) : ℂ) • b := by
  exact window_power_sin_cos ω θ hω hsplit hg hb hgN hbN ω.reps

/-- The initial stopped mass of a real sine/cosine split is `sin θ ^ 2`. -/
theorem window_initial_mass_sin_cos (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) :
    MeasureProb ψ (stopFinset ω.pred) = Real.sin θ ^ 2 := by
  have hbS : ∀ r ∈ stopFinset ω.pred, b r = 0 := by
    intro r hr
    rw [stopFinset, Finset.mem_filter] at hr
    obtain ⟨_, h1, h2⟩ := hr
    exact contCoord ω.pred hb r (by simp [h1, h2])
  have hgS : ∀ r ∉ stopFinset ω.pred, g r = 0 := by
    intro r hr
    exact stopCoord ω.pred hg r (fun h => hr (by
      rw [stopFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ r, h⟩))
  rw [hsplit, measureProb_sector (stopFinset ω.pred) _ _ g b hbS hgS hgN]
  exact norm_real_cast_sq _

/-- **Exact `(2k+1)`-fold stopped mass.** After `k` rounds the stopped Born mass is precisely
`sin ((2k+1)θ)^2`, not an iteration of the one-round scalar cubic map. -/
theorem window_power_mass_sin_cos (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ)
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) (k : ℕ) :
    MeasureProb ((stepOf ω) ^ k *ᵥ ψ) (stopFinset ω.pred) =
      Real.sin ((2 * (k : ℝ) + 1) * θ) ^ 2 := by
  have hbS : ∀ r ∈ stopFinset ω.pred, b r = 0 := by
    intro r hr
    rw [stopFinset, Finset.mem_filter] at hr
    obtain ⟨_, h1, h2⟩ := hr
    exact contCoord ω.pred hb r (by simp [h1, h2])
  have hgS : ∀ r ∉ stopFinset ω.pred, g r = 0 := by
    intro r hr
    exact stopCoord ω.pred hg r (fun h => hr (by
      rw [stopFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ r, h⟩))
  rw [window_power_sin_cos ω θ hω hsplit hg hb hgN hbN k,
    measureProb_sector (stopFinset ω.pred) _ _ g b hbS hgS hgN]
  exact norm_real_cast_sq _

/-- The stopped mass after the window's stored number of rounds is the exact odd-angle square. -/
theorem window_round_mass_sin_cos (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ)
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) :
    MeasureProb (roundOf ω *ᵥ ψ) (stopFinset ω.pred) =
      Real.sin ((2 * (ω.reps : ℝ) + 1) * θ) ^ 2 := by
  exact window_power_mass_sin_cos ω θ hω hsplit hg hb hgN hbN ω.reps

/-- **Tight finite growth.** In the safe odd-angle window, the exact stopped mass obeys the
source's cubic lower bound `(1 - (2k+1)^2 sin²θ / 3) * (2k+1)^2 sin²θ`. -/
theorem window_power_tight_growth (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ)
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1) (k : ℕ)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi / 2)
    (hwin : ((2 * k + 1 : ℕ) : ℝ) * θ ≤ Real.pi / 2) :
    (1 - ((2 * (k : ℝ) + 1) ^ 2) * Real.sin θ ^ 2 / 3) *
        ((2 * (k : ℝ) + 1) ^ 2 * Real.sin θ ^ 2) ≤
      MeasureProb ((stepOf ω) ^ k *ᵥ ψ) (stopFinset ω.pred) := by
  rw [window_power_mass_sin_cos ω θ hω hsplit hg hb hgN hbN k]
  have h := clause88_tight_sin_sq (2 * k + 1) θ hθ0 hθpi hwin
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by norm_cast
  rw [hcast] at h
  exact h

/-! ### Derived final amplification to at least one half -/

/-- The first odd multiple of `θ` reaching `π/4`, chosen from the proved finite crossing. -/
def finalReps (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : ℕ :=
  Classical.choose (rdvt_first_quarter θ hθ0 hθ1)

/-- The derived final repetition count reaches the first-quarter angle window and is minimal
among all odd multiples reaching `π/4`. -/
theorem finalReps_spec (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Real.pi / 4 ≤ (2 * (finalReps θ hθ0 hθ1 : ℝ) + 1) * θ ∧
      (2 * (finalReps θ hθ0 hθ1 : ℝ) + 1) * θ ≤ 3 * Real.pi / 4 ∧
      ∀ j : ℕ, j < finalReps θ hθ0 hθ1 →
        (2 * (j : ℝ) + 1) * θ < Real.pi / 4 := by
  exact Classical.choose_spec (rdvt_first_quarter θ hθ0 hθ1)

/-- Install the repetition count derived from the first-quarter crossing of `θ`, leaving the
window's predicate, continuation, and reflection unchanged. -/
def Window.ofFinal (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (ω : Window a w) :
    Window a w where
  pred := ω.pred
  cont := ω.cont
  cont_uni := ω.cont_uni
  cont_fix := ω.cont_fix
  refl := ω.refl
  refl_uni := ω.refl_uni
  reps := finalReps θ hθ0 hθ1

/-- The final window uses the odd-angle repetition count selected from its angle. -/
@[simp]
theorem ofFinal_reps (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (ω : Window a w) :
    (Window.ofFinal θ hθ0 hθ1 ω).reps = finalReps θ hθ0 hθ1 := rfl

/-- The final window's actual cascade marking count is exactly its derived crossing index. -/
theorem ofFinal_markCalls (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (ω : Window a w) :
    markCalls [Window.ofFinal θ hθ0 hθ1 ω] = finalReps θ hθ0 hθ1 := by
  simp [markCalls]

/-- **Final amplification at least one half.** The explicitly constructed final window has
stopped Born mass at least `1/2`; the same theorem returns the exact marking count of its word. -/
theorem ofFinal_half_and_count (ω : Window a w) {ψ : QState (OReg a w)} (θ : ℝ)
    {g b : QState (OReg a w)}
    (hω : ω.refl = reflAbout ψ)
    (hsplit : ψ = (Real.sin θ : ℂ) • g + (Real.cos θ : ℂ) • b)
    (hg : g ∈ stopSub ω.pred) (hb : b ∈ contSub ω.pred)
    (hgN : ∑ k, ‖g k‖ ^ 2 = 1) (hbN : ∑ k, ‖b k‖ ^ 2 = 1)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    1 / 2 ≤ MeasureProb (roundOf (Window.ofFinal θ hθ0 hθ1 ω) *ᵥ ψ)
        (stopFinset (Window.ofFinal θ hθ0 hθ1 ω).pred) ∧
      markCalls [Window.ofFinal θ hθ0 hθ1 ω] = finalReps θ hθ0 hθ1 := by
  refine ⟨?_, ofFinal_markCalls θ hθ0 hθ1 ω⟩
  change 1 / 2 ≤ MeasureProb ((stepOf ω) ^ (finalReps θ hθ0 hθ1) *ᵥ ψ) (stopFinset ω.pred)
  rw [window_power_mass_sin_cos ω θ hω hsplit hg hb hgN hbN (finalReps θ hθ0 hθ1)]
  exact rdvt_sin_sq_ge_of_window (finalReps_spec θ hθ0 hθ1).1 (finalReps_spec θ hθ0 hθ1).2.1

/-! ### Lemma 2/3 stage costs and gain products -/

/-- Convert a window and its measured weights/angle into the public source-stage record.  The
odd multiplier is the window's actual repetition count. -/
def stageOfWindow (ω : Window a w) (baseWeight ampWeight angle : ℝ) : VtStage where
  kind := if ω.reps = 0 then VtStageKind.base else VtStageKind.amplified
  baseWeight := baseWeight
  ampWeight := ampWeight
  oddMultiplier := ω.reps
  angle := angle

/-- The real odd-call multiplier of a converted stage is `2 * ω.reps + 1`. -/
theorem stageOfWindow_oddCalls (ω : Window a w) (baseWeight ampWeight angle : ℝ) :
    (stageOfWindow ω baseWeight ampWeight angle).oddCalls =
      ((2 * ω.reps + 1 : ℕ) : ℝ) := rfl

/-- **Window stage time recurrence.** A source stage chain built from windows charges its actual
odd multiplier to the previous-stage time plus the dyadic continuation time. -/
theorem window_stage_time_recurrence {m : ℕ} (chain : VtStageChain m)
    (windows : ℕ → Window a w) (base amp angle : ℕ → ℝ)
    (hstage : ∀ j, chain.stage j = stageOfWindow (windows j) (base j) (amp j) (angle j))
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    chain.time i = ((2 * (windows i).reps + 1 : ℕ) : ℝ) *
      (chain.time (i - 1) + (2 : ℝ) ^ (i - 1)) := by
  have h := chain.timeRec i h1 h2
  rw [hstage i] at h
  exact h

/-- **Lemma 2 for window stages.** The exact stage-time recurrence obeys the source's
`(1 + 1/(3m-1)) * √(r/r') * (Tprev + 2^(i-1))` bound. -/
theorem window_stage_lemma2 {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m)
    (windows : ℕ → Window a w) (base amp angle : ℕ → ℝ)
    (hstage : ∀ j, chain.stage j = stageOfWindow (windows j) (base j) (amp j) (angle j))
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    chain.time i ≤ (1 + 1 / (3 * (m : ℝ) - 1)) *
      (Real.sqrt (amp i) / Real.sqrt (base i)) *
      (chain.time (i - 1) + (2 : ℝ) ^ (i - 1)) := by
  have h := Qatlib.Papers.VarTimeAmpAmp10.StopModel.source_lemma2 chain hm h1 h2
  simpa only [hstage i, stageOfWindow] using h

/-- **Equation (6) for window stages.** Unrolling the actual odd-multiplier time recurrence gives
the source's overhead factor times the initial gain product plus the dyadic product sum. -/
theorem window_stage_eq6 {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m)
    (windows : ℕ → Window a w) (base amp angle : ℕ → ℝ)
    (hstage : ∀ j, chain.stage j = stageOfWindow (windows j) (base j) (amp j) (angle j)) :
    chain.time m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
      (gainRatioProduct amp base 1 (m + 1) * chain.time 0 + eq6ProductSum amp base m) := by
  have h := (clause89_endpoint chain hm).2
  simpa only [hstage, stageOfWindow] using h

/-- **Lemma 3, proof-controlled core, for window stages.** The gain product strictly after stage
`i` is bounded by the exact stopping-mass expression `3 * (1 + √(pstop/psucc))`. -/
theorem window_stage_lemma3_core {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m)
    (windows : ℕ → Window a w) (base amp angle : ℕ → ℝ)
    (hstage : ∀ j, oc.chain.stage j = stageOfWindow (windows j) (base j) (amp j) (angle j))
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct amp base (i + 1) (m + 1) ≤
      lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc := by
  have h := source_lemma3_core oc hm h1 h2
  simpa only [hstage, stageOfWindow] using h

/-- **Lemma 3 with the printed initial factor exposed.** The product from `i` through `m` is
bounded by the stage-`i` gain times the proof-controlled stopping-mass bound. -/
theorem window_stage_lemma3_printed_bound {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m)
    (windows : ℕ → Window a w) (base amp angle : ℕ → ℝ)
    (hstage : ∀ j, oc.chain.stage j = stageOfWindow (windows j) (base j) (amp j) (angle j))
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct amp base i (m + 1) ≤ gainRatio (amp i) (base i) *
      lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc := by
  have h := source_lemma3_printed_bound oc hm h1 h2
  simpa only [hstage, stageOfWindow] using h

/-- **Exact final stage-cost accounting.** Combining the equation-(6) unrolling with Lemma 3
bounds every dyadic term by the remaining stopping mass while exposing each stage-`i` gain. -/
theorem window_stage_final_cost {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m)
    (windows : ℕ → Window a w) (base amp angle : ℕ → ℝ)
    (hstage : ∀ j, oc.chain.stage j = stageOfWindow (windows j) (base j) (amp j) (angle j)) :
    oc.chain.time m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
      (gainRatioProduct amp base 1 (m + 1) * oc.chain.time 0 +
        ∑ i ∈ Finset.Ico 1 (m + 1),
          (3 : ℝ) * (gainRatio (amp i) (base i) *
            (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)) *
            (2 : ℝ) ^ (i - 1))) := by
  have h := clause64_endpoint oc hm
  simpa only [hstage, stageOfWindow] using h

end Qatlib.Papers.VarTimeAmpAmp10.AmplGrowth
