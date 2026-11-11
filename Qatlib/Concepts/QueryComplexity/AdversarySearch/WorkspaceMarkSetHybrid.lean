/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Workspace hybrid bounds for marked sets

This module records the states immediately before oracle queries and bounds the effect of
changing a Boolean oracle on a set of indices. The query masses on that disagreement set control
both the final Euclidean deviation and its square, following the hybrid method of
[BennettEtAl1997].

## Main statements

* `oracle_query_inputs_accounting`: query input states have the expected count and
  normalization.
* `workspace_mark_set_hybrid`: the final deviation is controlled by reference disagreement
  masses.
* `measureProb_sqrt_lipschitz`: event mass square roots are Lipschitz in the state norm.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SketchArith.GramAction

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The states immediately preceding oracle queries during execution of a circuit with the
workspace bit oracle for `f`. -/
noncomputable def oracleQueryInputs (f : I → Bool) :
    Circuit ((I × Bool) × W) → QState ((I × Bool) × W) → List (QState ((I × Bool) × W))
  | [], _ => []
  | Step.gate U :: C, ψ => oracleQueryInputs f C (ApplyGate U ψ)
  | Step.query :: C, ψ => ψ :: oracleQueryInputs f C (ApplyGate (workspaceBitOracle f) ψ)

/-- The workspace basis states whose query index belongs to `S`. -/
def workspaceMarkFiber (S : Finset I) : Finset ((I × Bool) × W) :=
  Finset.univ.filter (fun p => p.1.1 ∈ S)

/-- For a unitary circuit and normalized initial state, the recorded query inputs number exactly
`QueryCount C`, remain normalized, and have total query fiber mass one. -/
theorem oracle_query_inputs_accounting (f : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    (oracleQueryInputs f C ψ).length = QueryCount C ∧
      (∀ φ ∈ oracleQueryInputs f C ψ, Normalized φ ∧
        ∑ x : I, MeasureProb φ (workspaceQueryFiber (W := W) x) = 1) := by
  induction C generalizing ψ with
  | nil => exact ⟨rfl, fun φ hφ => False.elim ((List.mem_nil_iff φ).mp hφ)⟩
  | cons s C ih =>
    have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
    cases s with
    | gate U =>
      exact ih (ApplyGate U ψ) hC' (normalized_applyGate (hC U List.mem_cons_self) hψ)
    | query =>
      obtain ⟨hlen, hmem⟩ := ih (ApplyGate (workspaceBitOracle f) ψ) hC'
        (normalized_applyGate (workspaceBitOracle_unitary f) hψ)
      refine ⟨?_, ?_⟩
      · change (ψ :: oracleQueryInputs f C (ApplyGate (workspaceBitOracle f) ψ)).length = _
        rw [List.length_cons, hlen]; rfl
      · intro φ hφ
        rcases List.mem_cons.mp hφ with h | h
        · subst φ; exact ⟨hψ, measureProb_sum_workspaceQueryFiber hψ⟩
        · exact hmem φ h

/-- Replacing a workspace bit oracle changes a state by Euclidean norm at most twice the square
root of its mass on the oracle disagreement set. See [Bennett et al., Theorem
3.3][BennettEtAl1997]. -/
theorem workspace_mark_set_query_l2 (f g : I → Bool) (ψ : QState ((I × Bool) × W)) :
    ‖toEuclidean_fromVec (ApplyGate (workspaceBitOracle g) ψ-ApplyGate (workspaceBitOracle f) ψ)‖ ≤
      2*Real.sqrt (MeasureProb ψ (workspaceMarkFiber (W := W)
        (Finset.univ.filter (fun x : I => f x ≠ g x)))) := by
  let S := workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => f x ≠ g x))
  have he : ApplyGate (workspaceBitOracle g) ψ-ApplyGate (workspaceBitOracle f) ψ =
      ApplyGate (workspaceBitOracle g) (Collapse ψ S)-ApplyGate (workspaceBitOracle f) (Collapse ψ S) := by
    funext p
    obtain ⟨⟨i,b⟩,w⟩ := p
    change ApplyGate _ ψ ((i,b),w)-ApplyGate _ ψ ((i,b),w) =
      ApplyGate _ (Collapse ψ S) ((i,b),w)-ApplyGate _ (Collapse ψ S) ((i,b),w)
    rw [applyGate_workspaceBitOracle_mk, applyGate_workspaceBitOracle_mk,
      applyGate_workspaceBitOracle_mk, applyGate_workspaceBitOracle_mk]
    by_cases hi : f i ≠ g i
    · have hm (c : Bool) : (((i,c),w) : (I × Bool) × W) ∈ S := by simp [S, workspaceMarkFiber, hi]
      rw [collapse_apply, collapse_apply, if_pos (hm _), if_pos (hm _)]
    · have heq : f i = g i := not_ne_iff.mp hi
      rw [heq]; simp
  rw [he]
  simp only [toEuclidean_fromVec, WithLp.toLp_sub]
  calc
    _ ≤ ‖toEuclidean_fromVec (ApplyGate (workspaceBitOracle g) (Collapse ψ S))‖+
        ‖toEuclidean_fromVec (ApplyGate (workspaceBitOracle f) (Collapse ψ S))‖ := norm_sub_le _ _
    _ = 2*‖toEuclidean_fromVec (Collapse ψ S)‖ := by
      rw [norm_applyGate_of_mem_unitaryGroup (workspaceBitOracle_unitary g),
        norm_applyGate_of_mem_unitaryGroup (workspaceBitOracle_unitary f)]
      ring
    _ = _ := by rw [norm_toEuclidean_collapse_eq_sqrt_measureProb]

/-- For a unitary circuit, the final state deviation between two oracles is at most twice the
sum of the square roots of their disagreement masses along the reference execution. See
[Bennett et al., Theorem 3.3][BennettEtAl1997]. -/
theorem workspace_mark_set_hybrid (f g : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (hC : IsUnitaryCircuit C) :
    ‖toEuclidean_fromVec (Run (workspaceBitOracle g) C ψ-Run (workspaceBitOracle f) C ψ)‖ ≤
      2*((oracleQueryInputs f C ψ).map (fun φ => Real.sqrt (MeasureProb φ
        (workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => f x ≠ g x)))))).sum := by
  induction C generalizing ψ with
  | nil => simp [toEuclidean_fromVec, oracleQueryInputs]
  | cons s C ih =>
    have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
    cases s with
    | gate U => exact ih (ApplyGate U ψ) hC'
    | query =>
      let Og := workspaceBitOracle (W := W) g
      let Of := workspaceBitOracle (W := W) f
      have he : Run Og (Step.query :: C) ψ-Run Of (Step.query :: C) ψ =
          Run Og C (ApplyGate Og ψ-ApplyGate Of ψ)+
            (Run Og C (ApplyGate Of ψ)-Run Of C (ApplyGate Of ψ)) := by
        change Run Og C (ApplyGate Og ψ)-Run Of C (ApplyGate Of ψ) = _
        rw [run_sub]; module
      rw [he]
      simp only [toEuclidean_fromVec, WithLp.toLp_add]
      have hh := (norm_run_le Og (workspaceBitOracle_unitary g) hC' _).trans
        (workspace_mark_set_query_l2 f g ψ)
      have ht := ih (ApplyGate Of ψ) hC'
      refine (norm_add_le _ _).trans ((add_le_add hh ht).trans_eq ?_)
      change 2*Real.sqrt
          (MeasureProb ψ _)+2*((oracleQueryInputs f C (ApplyGate Of ψ)).map _).sum = _
      simp only [oracleQueryInputs, List.map_cons, List.sum_cons]
      ring

/-- For a unitary circuit and normalized initial state, the squared final oracle deviation is
bounded by four times the query count times the total disagreement mass along the reference
execution. See [Bennett et al., Theorem 3.3][BennettEtAl1997]. -/
theorem workspace_mark_set_hybrid_energy (f g : I → Bool) (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec (Run (workspaceBitOracle g) C ψ-Run (workspaceBitOracle f) C ψ)‖^2 ≤
      4*(QueryCount C : ℝ)*((oracleQueryInputs f C ψ).map (fun φ => MeasureProb φ
        (workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => f x ≠ g x))))).sum := by
  let L := oracleQueryInputs f C ψ
  let S := workspaceMarkFiber (W := W) (Finset.univ.filter (fun x : I => f x ≠ g x))
  have hlen := (oracle_query_inputs_accounting f C ψ hC hψ).1
  have hm : (L.map (fun φ => Real.sqrt (MeasureProb φ S))).sum =
      ∑ i : Fin L.length, Real.sqrt (MeasureProb (L.get i) S) := by
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    rfl
  have hms : (L.map (fun φ => MeasureProb φ S)).sum =
      ∑ i : Fin L.length, MeasureProb (L.get i) S := by
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    rfl
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin L.length))
    (fun i => Real.sqrt (MeasureProb (L.get i) S)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hc
  rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (measureProb_nonneg _ _))] at hc
  have hh := pow_le_pow_left₀ (norm_nonneg _) (workspace_mark_set_hybrid f g C ψ hC) 2
  rw [hm] at hh
  change L.length = QueryCount C at hlen
  have hlenR : (L.length : ℝ) = QueryCount C := by exact_mod_cast hlen
  rw [hlenR] at hc
  rw [hms]
  nlinarith only [hc, hh]

/-- The workspace query fiber consisting of indices whose first component is `y`. -/
def workspaceQuerySliceFiber {V K W : Type} [Fintype V] [DecidableEq V] [Fintype K] [Fintype W]
    (y : V) : Finset (((V × K) × Bool) × W) :=
  Finset.univ.filter (fun p => p.1.1.1 = y)

/-- For a normalized state, the masses of the query slices indexed by `V` sum to one. -/
theorem workspace_query_slice_mass_partition {V K W : Type} [Fintype V] [DecidableEq V]
    [Fintype K] [Fintype W] (φ : QState (((V × K) × Bool) × W)) (hφ : Normalized φ) :
    (∑ y : V, MeasureProb φ (workspaceQuerySliceFiber (V := V) y)) = 1 := by
  have he := Finset.sum_fiberwise Finset.univ (fun p : ((V × K) × Bool) × W => p.1.1.1)
    (fun p => BornProb φ p)
  exact he.trans hφ

/-- The square root of the mass of any event changes by at most the Euclidean distance between
two states. -/
theorem measureProb_sqrt_lipschitz {R : Type} [Fintype R] [DecidableEq R]
    (χ χ' : QState R) (E : Finset R) :
    |Real.sqrt (MeasureProb χ' E)-Real.sqrt (MeasureProb χ E)| ≤
      ‖toEuclidean_fromVec (χ'-χ)‖ := by
  rw [← norm_toEuclidean_collapse_eq_sqrt_measureProb χ' E,
    ← norm_toEuclidean_collapse_eq_sqrt_measureProb χ E]
  have hh :=
      abs_norm_sub_norm_le (toEuclidean_fromVec (Collapse χ' E))
      (toEuclidean_fromVec (Collapse χ E))
  exact hh.trans
      (by simpa only [toEuclidean_fromVec, WithLp.toLp_sub] using norm_toEuclidean_collapse_sub_le χ χ' E)

end Qatlib.Concepts.QueryComplexity.AdversarySearch
