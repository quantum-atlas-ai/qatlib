/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.AmplCascade
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.MedianEstimate

@[expose] public section

/-!
# Counted amplitude estimation for the VTAA cascade (third executable slice)

This module connects the coherent stop sector of `AmplCascade` to the public, counted
amplitude-estimation circuit.  A fresh-register circuit produces `2 * r + 1` independent
phase-estimation labels, and `vtMedianEstimate` decodes their median into a real number.
The Born law of that number is therefore the law of an executed circuit, not an externally
supplied success probability.  The exact circuit and access ledgers are retained.

The decoded median is also wired directly into Algorithm 2: `Qatlib.Papers.VarTimeAmpAmp10.AmplEstimate.Window.ofEstimate` computes its
repetition count by applying `bandReps` to the median outcome record.  No round count or
success weight is prescribed independently of the estimation circuit and its record.

The error radius here is the explicit finite precision radius of the public estimator.  The
failure bound `(8 / 9) ^ r` and the zero-support statement are exact; no asymptotic estimate,
expected-time claim, or stepwise stop measurement is asserted.
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
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Matrix

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.AmplEstimate

variable {a w : ℕ}

/-- The executed fresh-register estimator for the stopped mass of preparation `A` on seed `j`:
`2 * r + 1` independent counted phase-estimation samples on the stop sector of `f`. -/
def estimateCircuit (M r : ℕ) (A : Matrix (OReg a w) (OReg a w) ℂ) (j : OReg a w)
    (f : Addr a → Bool) : Circuit (FreshRegister (Fin M × (Bool × OReg a w)) (2 * r + 1)) :=
  vtFreshAECircuit M A j (stopFinset f) (2 * r + 1)

/-- The all-zero phase-label, unflagged, seeded input to the fresh-register estimator. -/
def estimateInput (M : ℕ) (hM : 2 ≤ M) (r : ℕ) (j : OReg a w) :
    QState (FreshRegister (Fin M × (Bool × OReg a w)) (2 * r + 1)) :=
  vtFreshAEInput M hM j (2 * r + 1)

/-- The identity oracle on the fresh estimation register, with the concrete computational
 equality instance used by the executed circuit semantics. -/
def estimateOracleIdentity (M r : ℕ) :
    Matrix (FreshRegister (Fin M × (Bool × OReg a w)) (2 * r + 1))
      (FreshRegister (Fin M × (Bool × OReg a w)) (2 * r + 1)) ℂ :=
  @One.one _ (@Matrix.one _ ℂ (fun x y => instDecidableEqFreshRegister (2 * r + 1) x y)
    Complex.instZero Complex.instOne)

/-- The success weight decoded from an actual odd-size estimation record by its sorted median. -/
def estimatedWeight (M r : ℕ) (record : Fin (2 * r + 1) → Fin M) : ℝ :=
  vtMedianEstimate M r record

/-- The good records: their decoded median is within the explicit finite estimation radius of
the actual stopped Born mass of the prepared state. -/
def estimateGood (M r : ℕ) (A : Matrix (OReg a w) (OReg a w) ℂ) (j : OReg a w)
    (f : Addr a → Bool) : Finset (Fin (2 * r + 1) → Fin M) :=
  vtMedianGood M r (MeasureProb (preparedAAState A j) (stopFinset (w := w) f))

/-- **Estimator Born law.** Every odd-size record's product-law probability is exactly the Born
mass of that record after running the explicit fresh-register estimation circuit. -/
theorem estimateCircuit_born_law (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) (record : Fin (2 * r + 1) → Fin M) :
    (aeLaw M A j (stopFinset f) hA hM).probOf record =
      MeasureProb (Run (estimateOracleIdentity M r) (estimateCircuit M r A j f)
        (estimateInput M hM r j))
        (Finset.univ.filter fun p => vtFreshLabel (2 * r + 1) p = record) :=
  vt_fresh_ae_born_law M hM A hA j (stopFinset f) (2 * r + 1) record

/-- **Exact executed-operation count.** The odd fresh-sample estimator uses exactly
`(2 * r + 1) * (6 * M - 3)` query/gate operations after its oracle calls are instantiated. -/
theorem estimateCircuit_count (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    QueryCount (estimateCircuit M r A j f) + GateCount (estimateCircuit M r A j f) =
      (2 * r + 1) * (6 * M - 3) :=
  vt_fresh_ae_count M hM A hA j (stopFinset f) (2 * r + 1)

/-- **Single-sample access ledger.** Before fresh-register replication, one estimation sample
uses `M - 1` marking queries, `5 * (M - 1) + 3` gates, `2 * (M - 1) + 1` preparation accesses,
and `M - 1` source reflections. -/
theorem estimate_single_access_ledger (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (j : OReg a w) :
    QueryCount (countedAECircuit M A j) = M - 1 ∧
      GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
      aeInputAccesses (aeAccessWord (I := OReg a w) M) = 2 * (M - 1) + 1 ∧
      aeSourceReflections (aeAccessWord (I := OReg a w) M) = M - 1 :=
  prepared_ae_access_ledger M (by omega) A j

/-- **Median failure bound.** The executed product law assigns mass at most `(8 / 9) ^ r` to
records whose decoded median lies outside the explicit radius around the true stopped mass. -/
theorem estimate_failure (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) :
    (aeLaw M A j (stopFinset f) hA hM).probEvent (fun record : Fin (2 * r + 1) → Fin M =>
      vtEstimateRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M <
        |estimatedWeight M r record - MeasureProb (preparedAAState A j) (stopFinset f)|) ≤
      (8 / 9 : ℝ) ^ r :=
  vt_median_estimate_failure M hM r A hA j (stopFinset f)

/-- A member of `estimateGood` satisfies its defining finite accuracy bound. -/
theorem estimateGood_spec (M r : ℕ) (A : Matrix (OReg a w) (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool) {record : Fin (2 * r + 1) → Fin M}
    (hrecord : record ∈ estimateGood M r A j f) :
    |estimatedWeight M r record - MeasureProb (preparedAAState A j) (stopFinset f)| ≤
      vtEstimateRadius (MeasureProb (preparedAAState A j) (stopFinset f)) M :=
  (Finset.mem_filter.mp hrecord).2

/-- **Zero-support exactness.** If the prepared state has zero stopped mass, every record of
positive product-law probability decodes to estimated weight zero. -/
theorem estimatedWeight_zero_support (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix (OReg a w) (OReg a w) ℂ) (hA : A ∈ Matrix.unitaryGroup (OReg a w) ℂ)
    (j : OReg a w) (f : Addr a → Bool)
    (hzero : MeasureProb (preparedAAState A j) (stopFinset f) = 0)
    (record : Fin (2 * r + 1) → Fin M)
    (hrecord : 0 < (aeLaw M A j (stopFinset f) hA hM).probOf record) :
    estimatedWeight M r record = 0 :=
  vt_median_estimate_zero_support M hM r A hA j (stopFinset f) hzero record hrecord

/-- The Algorithm 2 window computed from an estimation record: all unitary data are unchanged,
while the repetition count is the least count selected by `bandReps` for the decoded median. -/
def Window.ofEstimate (M r m : ℕ) (record : Fin (2 * r + 1) → Fin M) (ω : Window a w) :
    Window a w :=
  Window.ofBand m (estimatedWeight M r record) ω

/-- The estimated window uses the repetition count obtained from its median record. -/
@[simp]
theorem ofEstimate_reps (M r m : ℕ) (record : Fin (2 * r + 1) → Fin M) (ω : Window a w) :
    (Window.ofEstimate M r m record ω).reps =
      bandReps (estimatedWeight M r record) m := rfl

/-- The one-window cascade's marking count is computed from the estimation record, not supplied
as an independent schedule parameter. -/
theorem ofEstimate_markCalls (M r m : ℕ) (record : Fin (2 * r + 1) → Fin M) (ω : Window a w) :
    markCalls [Window.ofEstimate M r m record ω] =
      bandReps (estimatedWeight M r record) m := by
  simp [markCalls]

/-- **Estimated Algorithm 2 band.** Whenever the decoded median is positive and below the
threshold, the repetition count computed from the estimation record puts its ideal odd-factor
weight in the exact source band `[1 / (9m), 1 / m]`. -/
theorem ofEstimate_band {M r m : ℕ} {record : Fin (2 * r + 1) → Fin M} (hm : 0 < m)
    (hp : 0 < estimatedWeight M r record)
    (hpm : estimatedWeight M r record ≤ 1 / (9 * (m : ℝ))) (ω : Window a w) :
    1 / (9 * (m : ℝ)) ≤
        ampFactor (Window.ofEstimate M r m record ω).reps * estimatedWeight M r record ∧
      ampFactor (Window.ofEstimate M r m record ω).reps * estimatedWeight M r record ≤
        1 / (m : ℝ) := by
  exact bandReps_band hm hp hpm

end Qatlib.Papers.VarTimeAmpAmp10.AmplEstimate
