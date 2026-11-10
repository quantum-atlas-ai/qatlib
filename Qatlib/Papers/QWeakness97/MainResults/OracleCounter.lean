/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceMarkSetHybrid
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QWeakness97.MainResults
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
namespace OracleConstantCounter
abbrev R := ((Unit × Bool) × Unit)

def word : Circuit R := [.query]

def seed : QState R := Ket (((), false), ())

theorem run_one (b : Bool) :
    Run (workspaceBitOracle (W := Unit) (fun _ : Unit => b)) word seed =
      Ket (((), b), ()) := by
  funext p
  obtain ⟨⟨u,c⟩,w⟩ := p
  cases u; cases w; cases c <;> cases b <;>
    simp [word, seed, applyGate_workspaceBitOracle, Ket]

theorem source_charge :
    ((oracleQueryInputs (fun _ : Unit => false) word seed).map
      (fun φ => MeasureProb φ (workspaceQueryFiber (W := Unit) ()))).sum = 1 := by
  simp [word, seed, oracleQueryInputs, workspaceQueryFiber, MeasureProb, BornProb, Ket,
    Fintype.sum_prod_type]

theorem actual_squared_gap :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun _ : Unit => true)) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Unit => false)) word seed)‖ ^ 2 = 2 := by
  rw [run_one, run_one, norm_toEuclidean_fromVec_sq]
  norm_num [Ket, Fintype.sum_prod_type, Fintype.sum_bool]

theorem printed_bound_fails :
    QueryCount word = 1 ∧ IsUnitaryCircuit word ∧ Normalized seed ∧
    ((oracleQueryInputs (fun _ : Unit => false) word seed).map
      (fun φ => MeasureProb φ (workspaceQueryFiber (W := Unit) ()))).sum ≤
        (1 : ℝ)^2/(QueryCount word : ℝ) ∧
    ¬ ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun _ : Unit => true)) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Unit => false)) word seed)‖ ≤ 1 := by
  refine ⟨rfl, by simp [word], normalized_ket _, ?_, ?_⟩
  · rw [source_charge]; norm_num [word, QueryCount]
  · intro h
    have hn := norm_nonneg (toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun _ : Unit => true)) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Unit => false)) word seed))
    have hg := actual_squared_gap
    nlinarith
end OracleConstantCounter

open scoped BigOperators
namespace Cor34QueryClockCounter
abbrev R := ((Fin 4 × Bool) × Unit)

noncomputable def seed : QState R := TensorState (TensorState (Uniform (Fin 4)) Minus) (Ket ())

def word : Circuit R := [.query]

theorem seed_normalized : Normalized seed :=
  normalized_tensorState (normalized_tensorState (normalized_uniform (by decide)) normalized_minus)
    (normalized_ket ())

theorem actual_difference (y : Fin 4) :
    Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
      Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed =
    fun p => if p.1.1 = y then (-2 : ℂ)*seed p else 0 := by
  funext p
  obtain ⟨⟨x,b⟩,u⟩ := p
  cases u; cases b <;> by_cases h : x=y <;>
    simp [word, applyGate_workspaceBitOracle, h, seed, TensorState, Minus, Hadamard] <;> ring

theorem actual_gap_squared (y : Fin 4) :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed)‖^2 = 1 := by
  rw [actual_difference, norm_toEuclidean_fromVec_sq]
  have hc : ‖(Real.sqrt 2 : ℂ)⁻¹‖^2 = (1/2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hterm (p : R) :
      ‖(if p.1.1 = y then (-2 : ℂ)*seed p else 0)‖^2 =
        if p.1.1 = y then (1/2 : ℝ) else 0 := by
    obtain ⟨⟨x,b⟩,u⟩ := p
    cases u
    by_cases h : x=y
    · cases b <;> norm_num [h, seed, TensorState, Uniform, Minus, Hadamard, Ket,
        norm_mul, mul_pow, hc]
    · simp [h]
  simp_rw [hterm]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

theorem no_bad_set :
    ¬ ∃ S : Finset (Fin 4),
      (S.card : ℝ) ≤ 2*(QueryCount word : ℝ)^2/(3/4 : ℝ)^2 ∧
      ∀ y : Fin 4, y ∉ S →
        ‖toEuclidean_fromVec
          (Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
           Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed)‖ ≤ 3/4 := by
  rintro ⟨S,hcard,hgood⟩
  have hall : ∀ y : Fin 4, y ∈ S := by
    intro y
    by_contra h
    have hg := hgood y h
    have hsq := actual_gap_squared y
    have hnn := norm_nonneg (toEuclidean_fromVec
      (Run (workspaceBitOracle (W := Unit) (fun x => decide (x=y))) word seed -
       Run (workspaceBitOracle (W := Unit) (fun _ : Fin 4 => false)) word seed))
    nlinarith
  have heq : S = Finset.univ := Finset.eq_univ_of_forall hall
  subst S
  norm_num [word, QueryCount] at hcard
end Cor34QueryClockCounter

end Qatlib.Papers.QWeakness97.MainResults
