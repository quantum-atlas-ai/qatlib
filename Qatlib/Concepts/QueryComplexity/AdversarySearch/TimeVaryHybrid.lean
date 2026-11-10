/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceMarkSetHybrid
import Qatlib.Foundations.BornMetrics.EventProbability
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Classical BigOperators

structure OracleEdit (I W : Type) where
  reference : I → Bool
  replacement : I → Bool
  scope : Finset I
  agrees : ∀ x, x ∉ scope → replacement x = reference x
  mixing : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def editAdvance (e : OracleEdit I W) (modified : Bool)
    (ψ : QState ((I × Bool) × W)) : QState ((I × Bool) × W) :=
  ApplyGate e.mixing (ApplyGate (workspaceBitOracle
    (if modified then e.replacement else e.reference)) ψ)

def runOracleEdits (modified : Bool) : List (OracleEdit I W) →
    QState ((I × Bool) × W) → QState ((I × Bool) × W)
  | [], ψ => ψ
  | e :: tail, ψ => runOracleEdits modified tail (editAdvance e modified ψ)

def editCharges : List (OracleEdit I W) → QState ((I × Bool) × W) → List ℝ
  | [], _ => []
  | e :: tail, ψ => MeasureProb ψ (workspaceMarkFiber (W := W) e.scope) ::
      editCharges tail (editAdvance e false ψ)

theorem editCharges_length (L : List (OracleEdit I W))
    (ψ : QState ((I × Bool) × W)) : (editCharges L ψ).length = L.length := by
  induction L generalizing ψ with
  | nil => rfl
  | cons e tail ih => simp [editCharges, ih]

theorem editCharges_nonneg (L : List (OracleEdit I W))
    (ψ : QState ((I × Bool) × W)) : ∀ q ∈ editCharges L ψ, 0 ≤ q := by
  induction L generalizing ψ with
  | nil => simp [editCharges]
  | cons e tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with h | h
    · subst q; exact measureProb_nonneg _ _
    · exact ih _ q h

theorem editAdvance_sub (e : OracleEdit I W) (b : Bool)
    (ψ χ : QState ((I × Bool) × W)) :
    editAdvance e b (ψ - χ) = editAdvance e b ψ - editAdvance e b χ := by
  simp only [editAdvance, ApplyGate, Matrix.mulVec_sub]

theorem runOracleEdits_sub (b : Bool) (L : List (OracleEdit I W))
    (ψ χ : QState ((I × Bool) × W)) :
    runOracleEdits b L (ψ - χ) = runOracleEdits b L ψ - runOracleEdits b L χ := by
  induction L generalizing ψ χ with
  | nil => rfl
  | cons e tail ih => simp only [runOracleEdits, editAdvance_sub, ih]

theorem norm_runOracleEdits (b : Bool) (L : List (OracleEdit I W))
    (hL : ∀ e ∈ L, e.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (ψ : QState ((I × Bool) × W)) :
    ‖toEuclidean_fromVec (runOracleEdits b L ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
  induction L generalizing ψ with
  | nil => rfl
  | cons e tail ih =>
    change ‖toEuclidean_fromVec (runOracleEdits b tail (editAdvance e b ψ))‖ = _
    rw [ih (fun a ha => hL a (List.mem_cons_of_mem _ ha))]
    unfold editAdvance
    rw [norm_applyGate_of_mem_unitaryGroup (hL e List.mem_cons_self),
      norm_applyGate_of_mem_unitaryGroup (workspaceBitOracle_unitary _)]

theorem edit_query_deviation (e : OracleEdit I W)
    (ψ : QState ((I × Bool) × W)) :
    ‖toEuclidean_fromVec
      (ApplyGate (workspaceBitOracle e.replacement) ψ -
       ApplyGate (workspaceBitOracle e.reference) ψ)‖ ≤
        2 * Real.sqrt (MeasureProb ψ (workspaceMarkFiber (W := W) e.scope)) := by
  have hsub : workspaceMarkFiber (W := W)
      (Finset.univ.filter (fun x => e.reference x ≠ e.replacement x)) ⊆
      workspaceMarkFiber (W := W) e.scope := by
    intro p hp
    have hd : e.reference p.1.1 ≠ e.replacement p.1.1 := by
      simpa [workspaceMarkFiber] using hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    exact hd (e.agrees _ hnot).symm
  exact (workspace_mark_set_query_l2 e.reference e.replacement ψ).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (Qatlib.Foundations.BornMetrics.EventProbability.measureProb_mono ψ hsub))
        (by norm_num))

theorem time_varying_hybrid (L : List (OracleEdit I W))
    (hL : ∀ e ∈ L, e.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (ψ : QState ((I × Bool) × W)) :
    ‖toEuclidean_fromVec (runOracleEdits true L ψ - runOracleEdits false L ψ)‖ ≤
      2 * ((editCharges L ψ).map Real.sqrt).sum := by
  induction L generalizing ψ with
  | nil => simp [runOracleEdits, editCharges, toEuclidean_fromVec]
  | cons e tail ih =>
    have ht : ∀ a ∈ tail, a.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
      fun a ha => hL a (List.mem_cons_of_mem _ ha)
    have he : runOracleEdits true (e :: tail) ψ - runOracleEdits false (e :: tail) ψ =
        runOracleEdits true tail (editAdvance e true ψ - editAdvance e false ψ) +
        (runOracleEdits true tail (editAdvance e false ψ) -
          runOracleEdits false tail (editAdvance e false ψ)) := by
      simp only [runOracleEdits, runOracleEdits_sub]
      module
    have hstep : ‖toEuclidean_fromVec (editAdvance e true ψ - editAdvance e false ψ)‖ ≤
        2 * Real.sqrt (MeasureProb ψ (workspaceMarkFiber (W := W) e.scope)) := by
      change ‖toEuclidean_fromVec
        (ApplyGate e.mixing (ApplyGate (workspaceBitOracle e.replacement) ψ) -
          ApplyGate e.mixing (ApplyGate (workspaceBitOracle e.reference) ψ))‖ ≤ _
      rw [show ApplyGate e.mixing (ApplyGate (workspaceBitOracle e.replacement) ψ) -
            ApplyGate e.mixing (ApplyGate (workspaceBitOracle e.reference) ψ) =
          ApplyGate e.mixing (ApplyGate (workspaceBitOracle e.replacement) ψ -
            ApplyGate (workspaceBitOracle e.reference) ψ) by
              simp only [ApplyGate, Matrix.mulVec_sub]]
      rw [norm_applyGate_of_mem_unitaryGroup (hL e List.mem_cons_self)]
      exact edit_query_deviation e ψ
    have hh := (norm_runOracleEdits true tail ht
      (editAdvance e true ψ - editAdvance e false ψ)).le.trans hstep
    have htail := ih ht (editAdvance e false ψ)
    rw [he]
    simp only [toEuclidean_fromVec, WithLp.toLp_add]
    exact (norm_add_le _ _).trans ((add_le_add hh htail).trans_eq (by
      simp only [editCharges, List.map_cons, List.sum_cons]
      ring))

theorem time_varying_hybrid_energy (L : List (OracleEdit I W))
    (hL : ∀ e ∈ L, e.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (ψ : QState ((I × Bool) × W)) :
    ‖toEuclidean_fromVec (runOracleEdits true L ψ - runOracleEdits false L ψ)‖ ^ 2 ≤
      4 * (L.length : ℝ) * (editCharges L ψ).sum := by
  let Q := editCharges L ψ
  have hr : (Q.map Real.sqrt).sum = ∑ i : Fin Q.length, Real.sqrt (Q.get i) := by
    conv_lhs => rw [← List.ofFn_get Q, List.map_ofFn, List.sum_ofFn]
    rfl
  have hq : Q.sum = ∑ i : Fin Q.length, Q.get i := by
    conv_lhs => rw [← List.ofFn_get Q, List.sum_ofFn]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin Q.length))
    (fun i => Real.sqrt (Q.get i)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hc
  rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt
    (editCharges_nonneg L ψ _ (List.get_mem Q i)))] at hc
  have hh := pow_le_pow_left₀ (norm_nonneg _) (time_varying_hybrid L hL ψ) 2
  rw [hr] at hh
  have hlen : (Q.length : ℝ) = L.length := by exact_mod_cast editCharges_length L ψ
  rw [hlen] at hc
  rw [hq]
  nlinarith only [hc, hh]

theorem time_varying_hybrid_budget (L : List (OracleEdit I W))
    (hL : ∀ e ∈ L, e.mixing ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ)
    (ψ : QState ((I × Bool) × W)) (hT : 0 < L.length) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : (editCharges L ψ).sum ≤ ε ^ 2 / (4 * (L.length : ℝ))) :
    ‖toEuclidean_fromVec (runOracleEdits true L ψ - runOracleEdits false L ψ)‖ ≤ ε := by
  have he := time_varying_hybrid_energy L hL ψ
  have hp : (0 : ℝ) < 4 * (L.length : ℝ) := by positivity
  have hb := (le_div_iff₀ hp).mp hbudget
  have hn := norm_nonneg (toEuclidean_fromVec
    (runOracleEdits true L ψ - runOracleEdits false L ψ))
  nlinarith

end Qatlib.Concepts.QueryComplexity.AdversarySearch
