module

public import Qatlib.Papers.DysonSeries22.HistorySystem.EndpointRatio

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace QatlibTests.DysonSeries22EndpointRatioRegression

open Matrix
open Qatlib.Foundations.PureStateMath

private def oneState : EuclideanSpace ℂ (Fin 1) :=
  WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ))

private def zeroMatrix : ℝ → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ => 0

private def zeroSource : ℝ → QState (Fin 1) :=
  fun _ => 0

private def timeGrid : ℕ → ℝ :=
  fun n => n

/-- The concrete one-dimensional consumer state is nonzero. -/
private theorem oneState_ne_zero : oneState ≠ 0 := by
  intro h
  have hi := congrArg (fun z : EuclideanSpace ℂ (Fin 1) => z 0) h
  simp [oneState] at hi

/-- An ordinary consumer can instantiate the ratio theorem on a nonzero one-dimensional state,
with a nontrivial final clock and zero forcing. -/
example :=
  Qatlib.Papers.DysonSeries22.HistorySystem.actual_history_endpoint_Born_ratio
    zeroMatrix zeroSource timeGrid 1 1 1 oneState oneState_ne_zero

example (N : ℕ) :
    (Qatlib.Papers.DysonSeries22.HistorySystem.endpointClocks N N).card = 1 := by
  exact Qatlib.Papers.DysonSeries22.HistorySystem.endpointClocks_last_card N

end QatlibTests.DysonSeries22EndpointRatioRegression
