/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.AmplEstimate
public import Qatlib.Papers.VarTimeAmpAmp10.AmplGrowth
public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
public import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-!
# Arbitrary-relative-error estimation and the estimate-driven cascade (fourth slice)

Theorem 4 of arXiv:1010.4458v2 (Ambainis 2010) states a procedure `Estimate(A, c, p, k)` which,
for every relative-error parameter `c > 0`, estimates the output probability `ε` of `A` promised
to be `0` or at least `p`, with success probability `1 - 1/2^k`, satisfying
`(i) |ε - ε̃| ≤ c ε̃` when `ε ≥ p` and `(ii) ε̃ = 0` when `ε = 0`.

This slice constructs such an estimator from the counted median estimator and proves both
guarantees as explicit theorems.  The single-sample error radius is taken to be the exact
Brassard–Høyer–Mosca–Tapp bound `bhmtRadius` (purely additive in the mass, unlike the prescribed-error
prescribed radius whose `a/4` term caps the attainable relative error).  Re-running the median
amplification argument at this radius gives failure at most `(8/9)^r` for any `r`, and the
resolution `M = relSampleCount c p` and repetition count `r = confidenceReps k` are derived
constants: at that resolution the absolute radius is at most `c/(1+c) · ε`, which decodes to the
relative-error bound `|ε - ε̃| ≤ c ε̃`; at that repetition count the failure probability is at
most `1/2^k`.  The executed-operation counts of the actual estimation circuit are exact, and an
explicit real-valued budget bound in terms of `(c, p, k)` is derived from it.

The second half is the bridge from estimation outcomes to the cascade: `estimatedCascade`
installs, for every window, the repetition count computed by `bandReps` from its own estimation
record.  The composed schedule is unitary, preserves the `H_1 ⊆ … ⊆ H_m` nesting of the base
windows, lands every window in the Algorithm 2 band, and its derived call count ν is exactly the
sum of the per-record `bandReps` values; the total accounting theorem equates the per-window
estimation circuit costs plus the flat reflection word length with that ν plus one continuation
per window.  All costs are exact finite counts of the constructions actually executed.

Boundary (kept out of this slice): the doubling schedule and the expected (rather than
worst-case) cost of the adaptive procedure, the `Θ`-form of the cost, the full `T_av`/`T_max`
assembly, and any measurement claims about intermediate stop registers.  No asymptotic
statement is made.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Papers.VarTimeAmpAmp10.CoherentStop
open Qatlib.Papers.VarTimeAmpAmp10.AmplCascade
open Qatlib.Papers.VarTimeAmpAmp10.AmplGrowth
open Qatlib.Papers.VarTimeAmpAmp10.AmplEstimate
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Matrix

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.AmplEstimateC

variable {a w : ℕ}

/-! ### The absolute estimation radius and the derived `(c, p, k)` parameters -/

/-- The exact Brassard–Høyer–Mosca–Tapp error radius of one `M`-point amplitude estimate of the
mass `a`: purely additive in `a`, so choosing `M` relative to a mass floor `p` makes it an
arbitrarily small fraction of any mass `a ≥ p`. -/
def bhmtRadius (a : ℝ) (M : ℕ) : ℝ :=
  2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2

/-- The estimation resolution derived from the relative-error parameter `c` and the mass floor
`p`: enough phase-counter levels to push both terms of `bhmtRadius` below `c/(2(1+c)) · a` for
every mass `a ≥ p`, plus the constant `2` needed for the sampling law. -/
def relSampleCount (c p : ℝ) : ℕ :=
  Nat.ceil (8 * Real.pi * (1 + c) / (c * Real.sqrt p))
    + Nat.ceil (4 * Real.pi ^ 2 * (1 + c) / (c * p)) + 2

/-- The derived resolution supports the estimation law (it is at least `2`). -/
theorem relSampleCount_two (c p : ℝ) : 2 ≤ relSampleCount c p := by
  unfold relSampleCount
  omega

/-- The derived resolution exceeds the first scale term `8π(1+c)/(c√p)`. -/
theorem relSampleCount_le_pi_over_sqrt (c p : ℝ) :
    8 * Real.pi * (1 + c) / (c * Real.sqrt p) ≤ relSampleCount c p := by
  have h1 := Nat.le_ceil (8 * Real.pi * (1 + c) / (c * Real.sqrt p))
  unfold relSampleCount
  push_cast
  linarith

/-- The derived resolution exceeds the second scale term `4π²(1+c)/(cp)`. -/
theorem relSampleCount_le_pi_sq (c p : ℝ) :
    4 * Real.pi ^ 2 * (1 + c) / (c * p) ≤ relSampleCount c p := by
  have h1 := Nat.le_ceil (4 * Real.pi ^ 2 * (1 + c) / (c * p))
  unfold relSampleCount
  push_cast
  linarith

/-- **Explicit real budget of the derived resolution.** The resolution is strictly below the sum
of its two scale terms plus four, an explicit expression in `(c, p)`. -/
theorem relSampleCount_lt (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ((relSampleCount c p : ℕ) : ℝ) <
      8 * Real.pi * (1 + c) / (c * Real.sqrt p) +
        4 * Real.pi ^ 2 * (1 + c) / (c * p) + 4 := by
  have hx1 : 0 ≤ 8 * Real.pi * (1 + c) / (c * Real.sqrt p) := by
    refine div_nonneg ?_ (mul_nonneg hc.le (Real.sqrt_nonneg p))
    nlinarith [Real.pi_pos, hc]
  have hx2 : 0 ≤ 4 * Real.pi ^ 2 * (1 + c) / (c * p) := by
    refine div_nonneg ?_ (mul_nonneg hc.le hp.le)
    nlinarith [Real.pi_pos, hc]
  have h1 := Nat.ceil_lt_add_one hx1
  have h2 := Nat.ceil_lt_add_one hx2
  unfold relSampleCount
  push_cast
  linarith

/-- The median repetition count derived from the confidence parameter `k`: the least number of
fresh samples whose median amplification pushes the failure probability below `1/2^k`. -/
def confidenceReps (k : ℕ) : ℕ := sInf {r : ℕ | (2 : ℝ) ^ k ≤ (9 / 8 : ℝ) ^ r}

/-- Six ninth-eighth factors more than double: `(9/8)^6 ≥ 2`. -/
theorem two_le_nine_eighths_six : (2 : ℝ) ≤ (9 / 8 : ℝ) ^ 6 := by
  norm_num

/-- The count `6 * k` is a valid witness for the confidence policy: `(9/8)^(6k) ≥ 2^k`. -/
theorem confidenceReps_witness (k : ℕ) : (2 : ℝ) ^ k ≤ (9 / 8 : ℝ) ^ (6 * k) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) two_le_nine_eighths_six k

/-- **Confidence policy spec.** The derived repetition count reaches the geometric confidence
threshold `(9/8)^r ≥ 2^k`. -/
theorem confidenceReps_spec (k : ℕ) : (2 : ℝ) ^ k ≤ (9 / 8 : ℝ) ^ confidenceReps k := by
  have hne : {r : ℕ | (2 : ℝ) ^ k ≤ (9 / 8 : ℝ) ^ r}.Nonempty :=
    ⟨6 * k, confidenceReps_witness k⟩
  exact Nat.sInf_mem hne

/-- The derived confidence count is at most `6 * k`. -/
theorem confidenceReps_le (k : ℕ) : confidenceReps k ≤ 6 * k :=
  Nat.sInf_le (confidenceReps_witness k)

/-- **Confidence failure bound.** At the derived repetition count the median estimator's failure
probability is at most `1/2^k`. -/
theorem confidenceReps_failure (k : ℕ) :
    (8 / 9 : ℝ) ^ confidenceReps k ≤ (1 / 2 : ℝ) ^ k := by
  have h1 : (8 / 9 : ℝ) ^ confidenceReps k = ((9 / 8 : ℝ) ^ confidenceReps k)⁻¹ := by
    rw [← inv_pow, inv_div]
  have h2 : ((9 / 8 : ℝ) ^ confidenceReps k)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 (confidenceReps_spec k)
  have h3 : (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ := by rw [one_div, inv_pow]
  rw [h1]
  linarith [h2, h3]

/-! ### Decoding an absolute-error bound as a relative error -/

/-- **Relative decoding.** An estimate `m` of a positive mass `a` with absolute error at most
`c/(1+c) · a` has relative error at most `c` measured against the estimate:
`|a - m| ≤ c * m`. -/
theorem relative_error_of_le {c a m : ℝ} (hc : 0 < c) (ha : 0 < a)
    (h : |m - a| ≤ c / (1 + c) * a) : |a - m| ≤ c * m := by
  have h1cne : (1 + c : ℝ) ≠ 0 := by linarith
  have hsplit : a - c / (1 + c) * a = a / (1 + c) := by
    field_simp
    ring
  obtain ⟨hlo, _⟩ := abs_le.mp h
  have hm : a / (1 + c) ≤ m := by linarith
  have hkey : c / (1 + c) * a ≤ c * m := by
    have hcast : c / (1 + c) * a = c * (a / (1 + c)) := by
      field_simp
    rw [hcast]
    exact mul_le_mul_of_nonneg_left hm hc.le
  rw [abs_sub_comm]
  linarith [h, hkey]

/-- **Radius to relative error.** For every positive relative-error parameter `c` and mass floor
`p`, the absolute radius at the derived resolution is at most a `c/(1+c)` fraction of any mass
`a ≥ p`. -/
theorem bhmtRadius_le_relSample {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    {a : ℝ} (ha0 : 0 ≤ a) (hpa : p ≤ a) :
    bhmtRadius a (relSampleCount c p) ≤ c / (1 + c) * a := by
  have hap : 0 < a := lt_of_lt_of_le hp hpa
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos_of_pos hap
  have hM2 : 2 ≤ relSampleCount c p := relSampleCount_two c p
  have hMpos : (0 : ℝ) < (relSampleCount c p : ℕ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hM2)
  have h1cne : (1 + c : ℝ) ≠ 0 := by linarith
  have b1 : 8 * Real.pi * (1 + c) / (c * Real.sqrt a) ≤ (relSampleCount c p : ℕ) := by
    have hceil := relSampleCount_le_pi_over_sqrt c p
    have hdiv : 8 * Real.pi * (1 + c) / (c * Real.sqrt a)
        ≤ 8 * Real.pi * (1 + c) / (c * Real.sqrt p) :=
      (div_le_div_iff₀ (by nlinarith [Real.pi_pos, hc])
          (mul_pos hc (Real.sqrt_pos_of_pos hp))).2
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpa) hc.le)
          (by nlinarith [Real.pi_pos, hc] : (0 : ℝ) ≤ 8 * Real.pi * (1 + c)))
    exact hdiv.trans hceil
  have b2 : 4 * Real.pi ^ 2 * (1 + c) / (c * a) ≤ (relSampleCount c p : ℕ) := by
    have hceil := relSampleCount_le_pi_sq c p
    have hdiv : 4 * Real.pi ^ 2 * (1 + c) / (c * a)
        ≤ 4 * Real.pi ^ 2 * (1 + c) / (c * p) :=
      (div_le_div_iff₀ (by nlinarith [Real.pi_pos, hc]) (mul_pos hc hp)).2
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpa hc.le)
          (by nlinarith [Real.pi_pos, hc] : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * (1 + c)))
    exact hdiv.trans hceil
  have hterm1 : 2 * Real.pi * Real.sqrt (a * (1 - a)) / (relSampleCount c p : ℕ) ≤
      c * a / (2 * (1 + c)) := by
    rw [div_le_iff₀ hMpos]
    have hs1 : Real.sqrt (a * (1 - a)) ≤ Real.sqrt a :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])
    have hnn : (0 : ℝ) ≤ c * a / (2 * (1 + c)) := by
      refine div_nonneg (mul_nonneg hc.le hap.le) ?_
      linarith
    have hkey : 2 * Real.pi * Real.sqrt a ≤
        c * a / (2 * (1 + c)) * (relSampleCount c p : ℕ) := by
      have hstep : c * a / (2 * (1 + c)) *
          (8 * Real.pi * (1 + c) / (c * Real.sqrt a)) = 4 * Real.pi * Real.sqrt a := by
        have hcsne : c * Real.sqrt a ≠ 0 := mul_ne_zero (ne_of_gt hc) (ne_of_gt hsqrta)
        have h2cne : (2 * (1 + c) : ℝ) ≠ 0 := by linarith
        have hsa : Real.sqrt a * Real.sqrt a = a := by
          rw [← pow_two (Real.sqrt a)]
          exact Real.sq_sqrt ha0
        field_simp [hcsne, h2cne]
        nlinarith [hsa]
      calc 2 * Real.pi * Real.sqrt a
          ≤ c * a / (2 * (1 + c)) *
              (8 * Real.pi * (1 + c) / (c * Real.sqrt a)) := by
            rw [hstep]
            nlinarith [Real.pi_pos, Real.sqrt_nonneg a]
        _ ≤ c * a / (2 * (1 + c)) * (relSampleCount c p : ℕ) :=
            mul_le_mul_of_nonneg_left b1 hnn
    calc 2 * Real.pi * Real.sqrt (a * (1 - a))
        ≤ 2 * Real.pi * Real.sqrt a :=
          mul_le_mul_of_nonneg_left hs1 (by nlinarith [Real.pi_pos])
      _ ≤ c * a / (2 * (1 + c)) * (relSampleCount c p : ℕ) := hkey
  have hterm2 : Real.pi ^ 2 / (relSampleCount c p : ℕ) ^ 2 ≤ c * a / (2 * (1 + c)) := by
    rw [div_le_iff₀ (pow_pos hMpos 2)]
    have hstep2 : c * a / (2 * (1 + c)) * ((relSampleCount c p : ℕ) *
        (4 * Real.pi ^ 2 * (1 + c) / (c * a))) =
        2 * Real.pi ^ 2 * (relSampleCount c p : ℕ) := by
      have hcane : c * a ≠ 0 := mul_ne_zero (ne_of_gt hc) (ne_of_gt hap)
      have h2cne : (2 * (1 + c) : ℝ) ≠ 0 := by linarith
      field_simp [hcane, h2cne]
      ring
    have hMcast : (2 : ℝ) ≤ (relSampleCount c p : ℕ) := by exact_mod_cast hM2
    have hnn : (0 : ℝ) ≤ c * a / (2 * (1 + c)) := by
      refine div_nonneg (mul_nonneg hc.le hap.le) ?_
      linarith
    have hlast : (relSampleCount c p : ℕ) * (4 * Real.pi ^ 2 * (1 + c) / (c * a))
        ≤ (relSampleCount c p : ℕ) * (relSampleCount c p : ℕ) :=
      mul_le_mul_of_nonneg_left b2 hMpos.le
    calc Real.pi ^ 2 ≤ 2 * Real.pi ^ 2 * (relSampleCount c p : ℕ) := by
          nlinarith [Real.pi_pos, hMcast]
      _ = c * a / (2 * (1 + c)) * ((relSampleCount c p : ℕ) *
              (4 * Real.pi ^ 2 * (1 + c) / (c * a))) := hstep2.symm
      _ = c * a / (2 * (1 + c)) *
              ((relSampleCount c p : ℕ) * (4 * Real.pi ^ 2 * (1 + c) / (c * a))) := by ring
      _ ≤ c * a / (2 * (1 + c)) *
              ((relSampleCount c p : ℕ) * (relSampleCount c p : ℕ)) :=
            mul_le_mul_of_nonneg_left hlast hnn
      _ = c * a / (2 * (1 + c)) * (relSampleCount c p : ℕ) ^ 2 := by
            rw [pow_two]
  have hfinal : c * a / (2 * (1 + c)) + c * a / (2 * (1 + c)) = c / (1 + c) * a := by
    field_simp
    ring
  unfold bhmtRadius
  exact (add_le_add hterm1 hterm2).trans (le_of_eq hfinal)

/-! ### Median failure at the absolute radius -/

/-- **Median failure at the absolute radius.** The executed product law of the median
estimator assigns mass at most `(8/9)^r` to records whose median differs from the true stopped
mass by more than the exact Brassard–Høyer–Mosca–Tapp radius.  Unlike the prescribed
radius, this radius has no fixed relative part, so it can be made an arbitrarily small fraction
of any positive mass. -/
theorem median_abs_failure (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    (aeLaw M A j (stopFinset f) hA hM).probEvent
      (fun record : Fin (2 * r + 1) → Fin M =>
        bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M <
          |estimatedWeight M r record -
            MeasureProb (preparedAAState A j) (stopFinset f)|) ≤ (8 / 9 : ℝ) ^ r := by
  have ha := prepared_aa_good_bad_geometry A j (stopFinset f) hA
  have ha0 : 0 ≤ MeasureProb (preparedAAState A j) (stopFinset f) := ha.2.2.2.2.1
  have hrad : 0 ≤ bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M := by
    unfold bhmtRadius
    apply add_nonneg <;> apply div_nonneg <;> positivity
  have hgood := (prepared_ae_bhmt_error_and_endpoints M hM A j (stopFinset f) hA).1
  have hpi : 2 / 3 ≤ 8 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (pow_pos Real.pi_pos 2)).mpr
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hc := Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement
      (aeLaw M A j (stopFinset f) hA hM)
      (fun z => |aeEstimate M z - MeasureProb (preparedAAState A j) (stopFinset f)| ≤
        bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M)
  simp only [not_le] at hc
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass
      (aeLaw M A j (stopFinset f) hA hM)
      (fun z => bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M <
        |aeEstimate M z - MeasureProb (preparedAAState A j) (stopFinset f)|) ≤ 1 / 3 := by
    change 8 / Real.pi ^ 2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass
        (aeLaw M A j (stopFinset f) hA hM)
        (fun z => |aeEstimate M z - MeasureProb (preparedAAState A j) (stopFinset f)| ≤
          bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M) at hgood
    linarith
  exact Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure
      (aeLaw M A j (stopFinset f) hA hM) (aeEstimate M)
      r (MeasureProb (preparedAAState A j) (stopFinset f))
      (bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M) hrad hb

/-! ### Theorem 4: arbitrary-`c` relative-error estimation -/

/-- The decoded median weight of the estimator at the derived `(c, p, k)` parameters. -/
def estimatedWeightC (c p : ℝ) (k : ℕ)
    (record : Fin (2 * confidenceReps k + 1) → Fin (relSampleCount c p)) : ℝ :=
  estimatedWeight (relSampleCount c p) (confidenceReps k) record

/-- The executed arbitrary-`c` estimator circuit: the counted fresh-register median estimator of
the counted estimator, at the resolution and repetition count derived from `(c, p, k)`. -/
def estimateCircuitC (c p : ℝ) (k : ℕ) (A : Matrix (OReg a w) (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    Circuit (FreshRegister (Fin (relSampleCount c p) × (Bool × OReg a w))
      (2 * confidenceReps k + 1)) :=
  estimateCircuit (relSampleCount c p) (confidenceReps k) A j f

/-- **Theorem 4, generic form.** For any resolution `M` whose absolute radius is a `c/(1+c)`
fraction of every mass above the floor `p`, and any repetition count `r` whose failure is below
`1/2^k`, the executed estimator satisfies the two Theorem-4 guarantees with probability at least
`1 - 1/2^k` under the promise that the true mass is `0` or at least `p`: a relative error
`|ε - ε̃| ≤ c ε̃` in the positive case, and the exact value `ε̃ = 0` in the zero case. -/
theorem estimate_rel_event_success (M r k : ℕ) (hM : 2 ≤ M)
    (hr : (8 / 9 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ k)
    (c p : ℝ) (hc : 0 < c) (hp : 0 < p)
    (hradius : ∀ x : ℝ, 0 ≤ x → p ≤ x → bhmtRadius x M ≤ c / (1 + c) * x)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool)
    (hpromise : MeasureProb (preparedAAState A j) (stopFinset f) = 0 ∨
      p ≤ MeasureProb (preparedAAState A j) (stopFinset f)) :
    1 - (1 / 2 : ℝ) ^ k ≤
      (aeLaw M A j (stopFinset f) hA hM).probEvent
        (fun record : Fin (2 * r + 1) → Fin M =>
          (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
            |MeasureProb (preparedAAState A j) (stopFinset f) -
              estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
          (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
            estimatedWeight M r record = 0)) := by
  have hpnn : ∀ x : Fin (2 * r + 1) → Fin M,
      (0 : ℝ) ≤ (aeLaw M A j (stopFinset f) hA hM).probOf x :=
    fun x => Finset.prod_nonneg fun _ _ => (aeLaw M A j (stopFinset f) hA hM).nonneg _
  rcases hpromise with h0 | hpa
  · -- Zero case: every positive-probability record decodes to exactly zero.
    have hE : ∀ record : Fin (2 * r + 1) → Fin M,
        0 < (aeLaw M A j (stopFinset f) hA hM).probOf record →
        (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
          |MeasureProb (preparedAAState A j) (stopFinset f) -
            estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
        (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
          estimatedWeight M r record = 0) := by
      intro record hpos
      have hm := estimatedWeight_zero_support M hM r A hA j f h0 record hpos
      exact ⟨fun _ => by rw [h0, hm]; simp, fun _ => hm⟩
    have h1 : (aeLaw M A j (stopFinset f) hA hM).probEvent
        (fun record : Fin (2 * r + 1) → Fin M =>
          (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
            |MeasureProb (preparedAAState A j) (stopFinset f) -
              estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
          (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
            estimatedWeight M r record = 0)) = 1 := by
      show (Finset.univ.filter
          (fun record : Fin (2 * r + 1) → Fin M =>
            (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
              |MeasureProb (preparedAAState A j) (stopFinset f) -
                estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
            (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
              estimatedWeight M r record = 0))).sum
          (aeLaw M A j (stopFinset f) hA hM).probOf = 1
      rw [Finset.sum_subset (Finset.filter_subset _ _) ?_]
      · exact (aeLaw M A j (stopFinset f) hA hM).sum_probOf (2 * r + 1)
      · intro record _ hne
        by_cases hpos : 0 < (aeLaw M A j (stopFinset f) hA hM).probOf record
        · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ record, hE record hpos⟩) hne
        · exact le_antisymm (not_lt.mp hpos) (hpnn record)
    rw [h1]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  · -- Positive case: the good radius event implies the Theorem-4 event.
    have ha0 : 0 ≤ MeasureProb (preparedAAState A j) (stopFinset f) :=
      (prepared_aa_good_bad_geometry A j (stopFinset f) hA).2.2.2.2.1
    have hap : 0 < MeasureProb (preparedAAState A j) (stopFinset f) := lt_of_lt_of_le hp hpa
    have hsub : ∀ record : Fin (2 * r + 1) → Fin M,
        |estimatedWeight M r record - MeasureProb (preparedAAState A j) (stopFinset f)| ≤
          bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M →
        (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
          |MeasureProb (preparedAAState A j) (stopFinset f) -
            estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
        (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
          estimatedWeight M r record = 0) := by
      intro record hle
      refine ⟨fun _ => ?_, fun hne => absurd hne (by linarith)⟩
      exact relative_error_of_le hc hap (hle.trans (hradius _ ha0 hpa))
    have hfail := median_abs_failure M hM r A hA j f
    have hBadeq : (aeLaw M A j (stopFinset f) hA hM).probEvent
        (fun record : Fin (2 * r + 1) → Fin M =>
          bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M <
            |estimatedWeight M r record -
              MeasureProb (preparedAAState A j) (stopFinset f)|) =
        (Finset.univ.filter
          (fun record : Fin (2 * r + 1) → Fin M =>
            bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M <
              |estimatedWeight M r record -
                MeasureProb (preparedAAState A j) (stopFinset f)|)).sum
          (aeLaw M A j (stopFinset f) hA hM).probOf := rfl
    rw [hBadeq] at hfail
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin (2 * r + 1) → Fin M))
      (fun record : Fin (2 * r + 1) → Fin M =>
        bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M <
          |estimatedWeight M r record - MeasureProb (preparedAAState A j) (stopFinset f)|)
      ((aeLaw M A j (stopFinset f) hA hM).probOf)
    simp only [not_lt] at hsplit
    have htot : ∑ record : Fin (2 * r + 1) → Fin M,
        (aeLaw M A j (stopFinset f) hA hM).probOf record = 1 :=
      (aeLaw M A j (stopFinset f) hA hM).sum_probOf (2 * r + 1)
    have hEeq : (aeLaw M A j (stopFinset f) hA hM).probEvent
        (fun record : Fin (2 * r + 1) → Fin M =>
          (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
            |MeasureProb (preparedAAState A j) (stopFinset f) -
              estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
          (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
            estimatedWeight M r record = 0)) =
        (Finset.univ.filter
          (fun record : Fin (2 * r + 1) → Fin M =>
            (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
              |MeasureProb (preparedAAState A j) (stopFinset f) -
                estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
            (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
              estimatedWeight M r record = 0))).sum
          (aeLaw M A j (stopFinset f) hA hM).probOf := rfl
    rw [hEeq]
    have hmono : (Finset.univ.filter
          (fun record : Fin (2 * r + 1) → Fin M =>
            |estimatedWeight M r record -
              MeasureProb (preparedAAState A j) (stopFinset f)| ≤
              bhmtRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M)).sum
          (aeLaw M A j (stopFinset f) hA hM).probOf ≤
        (Finset.univ.filter
          (fun record : Fin (2 * r + 1) → Fin M =>
            (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
              |MeasureProb (preparedAAState A j) (stopFinset f) -
                estimatedWeight M r record| ≤ c * estimatedWeight M r record) ∧
            (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
              estimatedWeight M r record = 0))).sum
          (aeLaw M A j (stopFinset f) hA hM).probOf :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, hsub x (Finset.mem_filter.mp hx).2⟩)
        (fun x _ _ => hpnn x)
    linarith [hfail, hsplit, htot, hmono, hr]

/-- **Theorem 4, instantiated.** With the resolution `relSampleCount c p` and repetition count
`confidenceReps k` derived from the parameters, the executed estimator satisfies both guarantees
of Theorem 4 with probability at least `1 - 1/2^k`, for every relative-error parameter `c > 0`
and mass floor `p > 0`, under the promise that the stopped mass of the preparation is `0` or at
least `p`. -/
theorem estimateC_theorem4 {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (k : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool)
    (hpromise : MeasureProb (preparedAAState A j) (stopFinset f) = 0 ∨
      p ≤ MeasureProb (preparedAAState A j) (stopFinset f)) :
    1 - (1 / 2 : ℝ) ^ k ≤
      (aeLaw (relSampleCount c p) A j (stopFinset f) hA (relSampleCount_two c p)).probEvent
        (fun record : Fin (2 * confidenceReps k + 1) → Fin (relSampleCount c p) =>
          (p ≤ MeasureProb (preparedAAState A j) (stopFinset f) →
            |MeasureProb (preparedAAState A j) (stopFinset f) -
              estimatedWeightC c p k record| ≤ c * estimatedWeightC c p k record) ∧
          (MeasureProb (preparedAAState A j) (stopFinset f) = 0 →
            estimatedWeightC c p k record = 0)) :=
  estimate_rel_event_success (relSampleCount c p) (confidenceReps k) k
    (relSampleCount_two c p) (confidenceReps_failure k) c p hc hp
    (fun _x ha0 hpa => bhmtRadius_le_relSample hc hp ha0 hpa) A hA j f hpromise

/-- **Exact executed-operation count.** The arbitrary-`c` estimator circuit uses exactly
`(2r+1)(6M-3)` query/gate operations at the derived resolution `M` and repetition count `r`. -/
theorem estimateCircuitC_count (c p : ℝ) (k : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    QueryCount (estimateCircuitC c p k A j f) +
      GateCount (estimateCircuitC c p k A j f) =
      (2 * confidenceReps k + 1) * (6 * relSampleCount c p - 3) :=
  estimateCircuit_count (relSampleCount c p) (relSampleCount_two c p) (confidenceReps k)
    A hA j f

/-- **Count bound in `k`.** The executed-operation count of the estimator is at most
`(12k+1)(6M-3)` at the derived resolution `M`, since the confidence count is at most `6k`. -/
theorem estimateCircuitC_count_le (c p : ℝ) (k : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    QueryCount (estimateCircuitC c p k A j f) +
      GateCount (estimateCircuitC c p k A j f) ≤
      (12 * k + 1) * (6 * relSampleCount c p - 3) := by
  have h1 : 2 * confidenceReps k + 1 ≤ 12 * k + 1 := by
    have := confidenceReps_le k
    omega
  have hcount := estimateCircuitC_count c p k A hA j f
  rw [hcount]
  exact Nat.mul_le_mul h1 (Nat.le_refl _)

/-- **Explicit real budget.** The executed-operation count of the arbitrary-`c` estimator is
strictly below `(12k+1)` times an explicit expression in `(c, p)`: six times the two scale terms
plus four, minus three. -/
theorem estimateCircuitC_budget (c p : ℝ) (hc : 0 < c) (hp : 0 < p) (k : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    ((QueryCount (estimateCircuitC c p k A j f) +
        GateCount (estimateCircuitC c p k A j f) : ℕ) : ℝ) <
      (12 * (k : ℝ) + 1) *
        (6 * (8 * Real.pi * (1 + c) / (c * Real.sqrt p) +
          4 * Real.pi ^ 2 * (1 + c) / (c * p) + 4) - 3) := by
  have hMlt := relSampleCount_lt c p hc hp
  have hrle : 2 * confidenceReps k + 1 ≤ 12 * k + 1 := by
    have := confidenceReps_le k
    omega
  have hnum : ((QueryCount (estimateCircuitC c p k A j f) +
      GateCount (estimateCircuitC c p k A j f) : ℕ) : ℝ) =
      ((2 * confidenceReps k + 1 : ℕ) : ℝ) * ((6 * relSampleCount c p - 3 : ℕ) : ℝ) := by
    exact_mod_cast estimateCircuitC_count c p k A hA j f
  have hsub : ((6 * relSampleCount c p - 3 : ℕ) : ℝ) <
      6 * (8 * Real.pi * (1 + c) / (c * Real.sqrt p) +
        4 * Real.pi ^ 2 * (1 + c) / (c * p) + 4) - 3 := by
    have hcast : ((6 * relSampleCount c p - 3 : ℕ) : ℝ) =
        6 * ((relSampleCount c p : ℕ) : ℝ) - 3 := by
      rw [Nat.cast_sub (by have := relSampleCount_two c p; omega), Nat.cast_mul]
      push_cast
      ring
    rw [hcast]
    linarith
  have hpos : (0 : ℝ) < 12 * (k : ℝ) + 1 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hnn : (0 : ℝ) ≤ ((6 * relSampleCount c p - 3 : ℕ) : ℝ) := by
    have := relSampleCount_two c p
    exact_mod_cast (by omega : (0 : ℕ) ≤ 6 * relSampleCount c p - 3)
  rw [hnum]
  calc ((2 * confidenceReps k + 1 : ℕ) : ℝ) * ((6 * relSampleCount c p - 3 : ℕ) : ℝ)
      ≤ (12 * (k : ℝ) + 1) * ((6 * relSampleCount c p - 3 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrle) hnn
    _ < (12 * (k : ℝ) + 1) *
          (6 * (8 * Real.pi * (1 + c) / (c * Real.sqrt p) +
            4 * Real.pi ^ 2 * (1 + c) / (c * p) + 4) - 3) :=
        mul_lt_mul_of_pos_left hsub hpos

/-! ### The estimate-driven cascade: schedule, nesting, band, and accounting -/

/-- Installing an estimation-derived repetition count leaves the window's stop predicate
unchanged. -/
theorem ofEstimate_pred (M r m : ℕ) (record : Fin (2 * r + 1) → Fin M) (ω : Window a w) :
    (Window.ofEstimate M r m record ω).pred = ω.pred := rfl

/-- The schedule built from estimation records: each window's repetition count is computed by
`bandReps` from its own executed estimation record; nothing is prescribed independently. -/
def estimatedCascade (M r m : ℕ)
    (pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))) : List (Window a w) :=
  pairs.map fun pr => Window.ofEstimate M r m pr.2 pr.1

/-- **Derived call count ν of the estimate-driven schedule.** The total marking count of the
composed schedule is exactly the sum over windows of the rounds computed from their estimation
records: estimate, then rounds, then the total ν — an identity, not a budget. -/
theorem estimatedCascade_markCalls (M r m : ℕ)
    (pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))) :
    markCalls (estimatedCascade M r m pairs) =
      (pairs.map fun pr => bandReps (estimatedWeight M r pr.2) m).sum := by
  induction pairs with
  | nil => rfl
  | cons pr pairs ih =>
    have hd : estimatedCascade M r m (pr :: pairs)
        = Window.ofEstimate M r m pr.2 pr.1 :: estimatedCascade M r m pairs := rfl
    rw [hd, markCalls_cons, List.map_cons, List.sum_cons, ofEstimate_reps, ih]

/-- **Word length of the estimate-driven schedule.** The flat reflection word of the composed
schedule has length ν + one continuation per window, with ν the derived call count above. -/
theorem estimatedCascade_wordLength (M r m : ℕ)
    (pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))) :
    (wordFactors (estimatedCascade M r m pairs)).length =
      (pairs.map fun pr => bandReps (estimatedWeight M r pr.2) m).sum + pairs.length := by
  rw [wordFactors_length, estimatedCascade_markCalls]
  have hlen : (estimatedCascade M r m pairs).length = pairs.length := by
    unfold estimatedCascade
    rw [List.length_map]
  rw [hlen]

/-- **Unitarity of the estimate-driven schedule.** The cascade word composed from the
estimation-derived windows is unitary end-to-end. -/
theorem estimatedCascade_uni (M r m : ℕ)
    (pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))) :
    cascadeWord (estimatedCascade M r m pairs) ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  cascadeWord_uni _

/-- **Nesting preservation.** If the base windows form a nested `H_1 ⊆ … ⊆ H_m` schedule, the
estimate-driven schedule built on them is nested as well, because installing a derived
repetition count never changes a window's stop predicate. -/
theorem estimatedCascade_nested {M r m : ℕ}
    {pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))} :
    WindowsNested (pairs.map Prod.fst) →
    WindowsNested (estimatedCascade M r m pairs) := by
  induction pairs with
  | nil => intro _; exact True.intro
  | cons pq pairs ih =>
    intro h
    have hd : ∀ ω' ∈ pairs.map Prod.fst, ∀ x, pq.1.pred x = true → ω'.pred x = true := h.1
    refine ⟨fun ω' hmem x hx => ?_, ih h.2⟩
    rw [ofEstimate_pred] at hx
    obtain ⟨pq', hpq', rfl⟩ := List.mem_map.mp hmem
    rw [ofEstimate_pred]
    exact hd pq'.1 (List.mem_map.mpr ⟨pq', hpq', rfl⟩) x hx

/-- **Algorithm 2 band, schedule-wide.** If every estimation record decodes to a positive weight
below the threshold, every window of the estimate-driven schedule has its amplified weight in
the exact band `[1/(9m), 1/m]`. -/
theorem estimatedCascade_band {M r m : ℕ} {pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))}
    (hm : 0 < m)
    (hpos : ∀ pr ∈ pairs, 0 < estimatedWeight M r pr.2)
    (hth : ∀ pr ∈ pairs, estimatedWeight M r pr.2 ≤ 1 / (9 * (m : ℝ))) :
    ∀ pr ∈ pairs,
      1 / (9 * (m : ℝ)) ≤
        ampFactor (Window.ofEstimate M r m pr.2 pr.1).reps * estimatedWeight M r pr.2 ∧
      ampFactor (Window.ofEstimate M r m pr.2 pr.1).reps * estimatedWeight M r pr.2 ≤
        1 / (m : ℝ) :=
  fun pr hpr => ofEstimate_band hm (hpos pr hpr) (hth pr hpr) pr.1

/-- The source-stage odd multiplier of an estimate-driven window is the round count computed
from its estimation record, linking the estimation bridge to the Lemma 2/3 stage interface. -/
theorem ofEstimate_stage_multiplier (M r m : ℕ) (record : Fin (2 * r + 1) → Fin M)
    (ω : Window a w) (base amp angle : ℝ) :
    (stageOfWindow (Window.ofEstimate M r m record ω) base amp angle).oddMultiplier =
      bandReps (estimatedWeight M r record) m := rfl

/-- **End-to-end accounting.** For the estimate-driven schedule, the per-window estimation
circuit costs plus the flat reflection word length equal the constant estimation cost per window
times the number of windows, plus the derived call count ν (the sum of the per-record round
counts), plus one continuation per window: estimate → rounds → total marking count, as an
identity of the constructions actually executed. -/
theorem estimatedCascade_total_ops (M r m : ℕ) (hM : 2 ≤ M)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w)
    (pairs : List (Window a w × (Fin (2 * r + 1) → Fin M))) :
        ((pairs.map fun pr =>
        QueryCount (estimateCircuit M r A j pr.1.pred) +
        GateCount (estimateCircuit M r A j pr.1.pred)).sum : ℕ) +
      (wordFactors (estimatedCascade M r m pairs)).length =
      pairs.length * ((2 * r + 1) * (6 * M - 3)) +
        ((pairs.map fun pr => bandReps (estimatedWeight M r pr.2) m).sum + pairs.length) := by
  have hsum : ((pairs.map fun pr =>
      QueryCount (estimateCircuit M r A j pr.1.pred) +
      GateCount (estimateCircuit M r A j pr.1.pred)).sum : ℕ) =
      pairs.length * ((2 * r + 1) * (6 * M - 3)) := by
    induction pairs with
    | nil => simp
    | cons pr pairs ihpx =>
      rw [List.map_cons, List.sum_cons, List.length_cons,
        estimateCircuit_count M hM r A hA j pr.1.pred, ihpx]
      ring
  rw [hsum, estimatedCascade_wordLength]

end Qatlib.Papers.VarTimeAmpAmp10.AmplEstimateC
