/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.DysonError.HistorySolver
import Qatlib.Papers.DysonSeries22.TimeSteps
import Qatlib.Papers.DysonSeries22.HistoryReadout

/-!
# Padded Dyson history systems

This module packages a finite Dyson time march as a padded history system. After step `r`,
`paddedStep` is the identity and `paddedDriving` vanishes, so the trajectory repeats its
endpoint. It constructs the history vector, proves the history equation and forward substitution
formula, and evaluates the native endpoint readout of the normalized history.

The mathematical setting follows [BerryCosta2024].

## Main statements

* `source_forward_substitution`: solving the history system recovers the padded trajectory.
* `normalizedHistory_padding`: endpoint clock slices repeat the normalized endpoint.
* `actual_history_endpoint_Born`: the endpoint readout probability for the constructed history.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Papers.DysonSeries22.HistorySystem
open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.TimeEvolution.DysonError
open Qatlib.Papers.DysonSeries22.Truncation
open Qatlib.Papers.DysonSeries22.HistoryReadout
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The truncated evolution map before step `r`, and the identity map from step `r` onward. -/
def paddedStep (A : ℝ → Matrix I I ℂ) (t : ℕ → ℝ) (K r n : ℕ) :
    EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  if n<r then (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (truncatedEvolution A (t n) (t (n+1)) K) else 1

/-- The truncated source vector before step `r`, and zero from step `r` onward. -/
def paddedDriving (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K r n : ℕ) : EuclideanSpace ℂ I :=
  if n<r then truncatedSource A b (t n) (t (n+1)) K else 0

/-- The affine trajectory formed from the padded evolution maps and driving vectors, starting at
`x₀`. -/
def paddedTrajectory (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K r : ℕ) (x₀ : EuclideanSpace ℂ I) : ℕ → EuclideanSpace ℂ I :=
  affineTrajectory (fun n => paddedStep A t K r n) (paddedDriving A b t K r) x₀

/-- The padded trajectory is constant after step `r`. See [Berry and Costa, 2024, Section 2.1.1;
Eqs. (19)–(26)][BerryCosta2024]. -/
theorem paddedTrajectory_constant (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r k : ℕ) (x₀ : EuclideanSpace ℂ I) :
    paddedTrajectory A b t K r x₀ (r+k)=paddedTrajectory A b t K r x₀ r := by
  induction k with
  | zero => simp
  | succ k ih =>
    change paddedStep A t K r (r+k) (paddedTrajectory A b t K r x₀ (r+k)) +
      paddedDriving A b t K r (r+k) = _
    simp [paddedStep,paddedDriving,show ¬r+k<r by omega,ih]

/-- Up to and including step `r`, the padded trajectory agrees with the finite Dyson time march. -/
theorem paddedTrajectory_before (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r n : ℕ) (x₀ : EuclideanSpace ℂ I) (hn : n≤r) :
    paddedTrajectory A b t K r x₀ n = TimeSteps.finiteMarch A b t K x₀ n := by
  have h : ∀ m, m≤r → paddedTrajectory A b t K r x₀ m = TimeSteps.finiteMarch A b t K x₀ m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hmr : m<r := by omega
      change paddedStep A t K r m (paddedTrajectory A b t K r x₀ m) +
        paddedDriving A b t K r m =
        (Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) (truncatedEvolution A (t m) (t (m+1)) K)
          (TimeSteps.finiteMarch A b t K x₀ m) + truncatedSource A b (t m) (t (m+1)) K
      rw [paddedStep,paddedDriving,if_pos hmr,if_pos hmr,ih (by omega)]
  exact h n hn

/-- The history system right hand side consisting of the initial vector followed by the padded
driving vectors. -/
def sourceRhs (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) : Fin (N+1) → EuclideanSpace ℂ I :=
  Fin.cases x₀ (fun i => paddedDriving A b t K r i.val)

/-- Applying the history operator to the padded trajectory gives `sourceRhs`. -/
theorem source_history_equation (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) :
    historyOperator (fun i : Fin N => paddedStep A t K r i.val)
      (fun i : Fin (N+1) => paddedTrajectory A b t K r x₀ i.val) = sourceRhs A b t K r N x₀ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [historyOperator,sourceRhs,Fin.cases_succ,Fin.val_succ,Fin.val_castSucc]
    change (paddedStep A t K r j.val (paddedTrajectory A b t K r x₀ j.val) +
      paddedDriving A b t K r j.val) - _ = _
    abel

/-- Forward substitution for the padded history system recovers the padded trajectory at every
represented clock time. See [Berry and Costa, 2024, Eqs. (30)–(38)][BerryCosta2024]. -/
theorem source_forward_substitution (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) :
    solveHistory (fun i : Fin N => paddedStep A t K r i.val) (sourceRhs A b t K r N x₀) =
      fun i : Fin (N+1) => paddedTrajectory A b t K r x₀ i.val :=
  (history_unique _ _ _ (source_history_equation A b t K r N x₀)).symm

/-- The Euclidean vector whose clock slices are the padded trajectory values from zero through
`N`. -/
def historyVector (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) : EuclideanSpace ℂ (Fin (N+1)×I) :=
  WithLp.toLp 2 (fun ci => paddedTrajectory A b t K r x₀ ci.1.val ci.2)

/-- A nonzero initial vector gives a nonzero history vector. -/
theorem historyVector_ne_zero (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) (hx₀ : x₀≠0) :
    historyVector A b t K r N x₀≠0 := by
  intro hz
  apply hx₀
  ext i
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin (N+1)×I) => z (0,i)) hz
  exact h

/-- The clock labels in `Fin (N + 1)` whose values are at least `r`. -/
def endpointClocks (r N : ℕ) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun c => r ≤ c.val)

/-- The history vector scaled by the reciprocal of its norm. -/
def normalizedHistory (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (t : ℕ → ℝ)
    (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) : EuclideanSpace ℂ (Fin (N+1)×I) :=
  (‖historyVector A b t K r N x₀‖⁻¹ : ℝ) • historyVector A b t K r N x₀

/-- The normalized history has norm one when the history vector has nonzero norm. -/
theorem normalizedHistory_norm (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I)
    (hn : ‖historyVector A b t K r N x₀‖≠0) :
    ‖normalizedHistory A b t K r N x₀‖=1 := by
  rw [normalizedHistory,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hn]

/-- Every endpoint clock slice of the normalized history equals the endpoint trajectory vector
scaled by the reciprocal history norm. -/
theorem normalizedHistory_padding (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I)
    (c : Fin (N+1)) (hc : c ∈ endpointClocks r N) (i : I) :
    normalizedHistory A b t K r N x₀ (c,i)=
      ((‖historyVector A b t K r N x₀‖⁻¹ : ℝ) • paddedTrajectory A b t K r x₀ r) i := by
  have hr : r≤c.val := (Finset.mem_filter.1 hc).2
  have h := paddedTrajectory_constant A b t K r (c.val-r) x₀
  rw [Nat.add_sub_of_le hr] at h
  change (‖historyVector A b t K r N x₀‖⁻¹ : ℝ) • paddedTrajectory A b t K r x₀ c.val i = _
  rw [h]
  rfl

/-- For a history vector of nonzero norm, the native endpoint readout probability equals the
number of endpoint clocks times the squared norm of the scaled endpoint vector. See [Berry
and Costa, 2024, Eqs. (96)–(101)][BerryCosta2024]. -/
theorem actual_history_endpoint_Born (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I)
    (hn : ‖historyVector A b t K r N x₀‖≠0) :
    (((Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument.readout
      (clockProjector (I:=I) (endpointClocks r N)) (clockProjector_norm _)).measure
      (MState.pure (Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn.ketOfUnit
        (normalizedHistory A b t K r N x₀) (normalizedHistory_norm A b t K r N x₀ hn)))) true : ℝ) =
      ((endpointClocks r N).card:ℝ) *
        ‖(‖historyVector A b t K r N x₀‖⁻¹ : ℝ) • paddedTrajectory A b t K r x₀ r‖^2 :=
  padded_native_Born _ _ (normalizedHistory_norm A b t K r N x₀ hn) _
    (normalizedHistory_padding A b t K r N x₀)
end Qatlib.Papers.DysonSeries22.HistorySystem
