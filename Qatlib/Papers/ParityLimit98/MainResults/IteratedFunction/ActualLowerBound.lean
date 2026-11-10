/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction.HardIteration
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.ParityLimit98.MainResults.LowerBound

def iterateEvent {N : ℕ} [NeZero N] (W : Type) [Fintype W]
    (g : Equiv.Perm (Fin N × Bool)) : Finset (PolynomialWorkspace (Fin N) W) :=
  {g^[N] (0,false)} ×ˢ Finset.univ

def evenReadout (N : ℕ) (W : Type) [Fintype W] : Finset (PolynomialWorkspace (Fin N) W) :=
  Finset.univ.filter (fun q => q.1.2 = false)

theorem iterateEvent_subset_parity {N : ℕ} [NeZero N] {W : Type} [Fintype W] [DecidableEq W]
    (f : Fin N → Bool) :
    iterateEvent W (hardPermutation f) ⊆
      if parityOddB f then Finset.univ \ evenReadout N W else evenReadout N W := by
  intro q hq
  have he : q.1 = (0,parityOddB f) := by
    have he := Finset.mem_singleton.mp (Finset.mem_product.mp hq).1
    simpa only [hardPermutation_iterate_card] using he
  have hb := congrArg Prod.snd he
  cases hp : parityOddB f <;> simp [hp, evenReadout, show q.1.2 = _ from hb]

theorem iterate_event_probability_mono {H : Type} [Fintype H] [DecidableEq H]
    (ψ : QState H) {E F : Finset H} (h : E ⊆ F) : MeasureProb ψ E ≤ MeasureProb ψ F := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => sq_nonneg ‖ψ i‖)

theorem hard_iteration_positive_bias_lower {N : ℕ} [NeZero N]
    {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin N) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin N) W)) (hn : Normalized ψ)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ f : Fin N → Bool,
      1 / 2 + ε ≤ MeasureProb (Run (hardOracle f) C ψ) (iterateEvent W (hardPermutation f))) :
    N ≤ 2 * QueryCount C := by
  have hb := physical_positive_bias_query_bound
    (substituteForward (knownShift N W) C)
    (substituteForward_unitary _ (knownShift_unitary N W) C hC)
    ψ hn (Projector (evenReadout N W)) (projector_isOrthogonalProjector _) ε hε (by
      intro f
      rw [projectorCorrectness_event, hardOracle_substitution]
      exact (hs f).trans (iterate_event_probability_mono _ (iterateEvent_subset_parity f)))
  simpa only [(substituteForward_cost (knownShift N W) C).1] using hb

theorem iterate_computation_requires_half_queries {N : ℕ} [NeZero N]
    {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin N) W)) (hC : IsUnitaryCircuit C)
    (ψ : QState (PolynomialWorkspace (Fin N) W)) (hn : Normalized ψ)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ g : Equiv.Perm (Fin N × Bool),
      1 / 2 + ε ≤ MeasureProb (Run (TensorGate (permMatrix g) 1) C ψ) (iterateEvent W g)) :
    N ≤ 2 * QueryCount C :=
  hard_iteration_positive_bias_lower C hC ψ hn ε hε (fun f => hs (hardPermutation f))

end Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
