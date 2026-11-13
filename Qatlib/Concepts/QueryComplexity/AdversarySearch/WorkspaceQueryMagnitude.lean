/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation

/-!
# Workspace query magnitude estimates

This module extends Boolean bit oracles by an auxiliary workspace and records query input states
for execution with the identity oracle. Their query fiber masses yield singleton hybrid bounds
and an aggregate squared deviation estimate, implementing the query magnitude method of
[BennettEtAl1997].

## Main statements

* `workspace_query_inputs_accounting`: identity oracle query states are normalized and have
  total query fiber mass one.
* `workspace_query_magnitude_hybrid`: marked query masses control a singleton oracle's final
  deviation.
* `workspace_query_hybrid_energy`: the summed squared singleton deviations are at most 4Q².

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.SketchArith.GramAction

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

open Matrix
open scoped Matrix.Norms.L2Operator

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The Boolean bit oracle tensored with the identity on an auxiliary workspace. -/
noncomputable def workspaceBitOracle (f : I → Bool) :
    Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  TensorGate (BitOracleOn f) 1

/-- The workspace basis states with query index `x`, allowing arbitrary target and workspace
values. -/
def workspaceQueryFiber (x : I) : Finset ((I × Bool) × W) :=
  Finset.univ.filter fun p : (I × Bool) × W => p.1.1 = x

/-- The states immediately before query steps when a circuit is executed with the identity
oracle. -/
noncomputable def nullQueryInputs {H : Type} [Fintype H] [DecidableEq H] :
    Circuit H → QState H → List (QState H)
  | [], _ => []
  | Step.gate U :: C, ψ => nullQueryInputs C (ApplyGate U ψ)
  | Step.query :: C, ψ => ψ :: nullQueryInputs C ψ

/-- An empty circuit has no recorded query inputs. -/
@[simp] theorem nullQueryInputs_nil {H : Type} [Fintype H] [DecidableEq H] (ψ : QState H) :
    nullQueryInputs [] ψ = [] := rfl

/-- A leading gate updates the state before recording the remaining query inputs. -/
@[simp] theorem nullQueryInputs_gate {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (C : Circuit H) (ψ : QState H) :
    nullQueryInputs (Step.gate U :: C) ψ = nullQueryInputs C (ApplyGate U ψ) := rfl

/-- A leading identity query records the current state before continuing. -/
@[simp] theorem nullQueryInputs_query {H : Type} [Fintype H] [DecidableEq H]
    (C : Circuit H) (ψ : QState H) :
    nullQueryInputs (Step.query :: C) ψ = ψ :: nullQueryInputs C ψ := rfl

omit [DecidableEq I] in

/-- A gate tensored with the workspace identity acts separately on each fixed workspace slice of
a state. -/
theorem applyGate_tensorGate_one (U : Matrix (I × Bool) (I × Bool) ℂ)
    (ψ : QState ((I × Bool) × W)) (p : (I × Bool) × W) :
    ApplyGate (TensorGate U (1 : Matrix W W ℂ)) ψ p
      = ApplyGate U (fun j => ψ (j, p.2)) p.1 := by
  simp only [ApplyGate, TensorGate, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single p.2 (fun w _ hw => ?_) (fun h => absurd (Finset.mem_univ p.2) h)]
  · rw [Matrix.one_apply_eq]
    ring
  · rw [Matrix.one_apply_ne (fun h => hw h.symm), mul_zero, zero_mul]

/-- The workspace bit oracle acts by XORing `f` at the query index into the target coordinate. -/
theorem applyGate_workspaceBitOracle (f : I → Bool) (ψ : QState ((I × Bool) × W))
    (p : (I × Bool) × W) :
    ApplyGate (workspaceBitOracle (W := W) f) ψ p
      = ψ ((p.1.1, p.1.2 ^^ f p.1.1), p.2) := by
  rw [workspaceBitOracle, applyGate_tensorGate_one]
  exact applyGate_bitOracleOn f (fun j => ψ (j, p.2)) p.1

/-- At the basis coordinate `((i, b), w)`, the workspace bit oracle reads the input amplitude at
`((i, b ^^ f i), w)`. -/
theorem applyGate_workspaceBitOracle_mk (f : I → Bool) (ψ : QState ((I × Bool) × W))
    (i : I) (b : Bool) (w : W) :
    ApplyGate (workspaceBitOracle (W := W) f) ψ ((i, b), w) = ψ ((i, b ^^ f i), w) :=
  applyGate_workspaceBitOracle f ψ ((i, b), w)

omit [DecidableEq W] in

/-- For a normalized state, the masses of all workspace query fibers sum to one. -/
theorem measureProb_sum_workspaceQueryFiber {ψ : QState ((I × Bool) × W)}
    (hψ : Normalized ψ) :
    ∑ x : I, MeasureProb ψ (workspaceQueryFiber (W := W) x) = 1 := by
  have h : ∑ x : I, ∑ p ∈ (Finset.univ : Finset ((I × Bool) × W)).filter
        (fun p => p.1.1 = x), BornProb ψ p
      = ∑ p : (I × Bool) × W, BornProb ψ p :=
    Finset.sum_fiberwise Finset.univ (fun p : (I × Bool) × W => p.1.1)
      (fun p => BornProb ψ p)
  calc ∑ x : I, MeasureProb ψ (workspaceQueryFiber (W := W) x)
      = ∑ x : I, ∑ p ∈ (Finset.univ : Finset ((I × Bool) × W)).filter
          (fun p => p.1.1 = x), BornProb ψ p := rfl
    _ = ∑ p : (I × Bool) × W, BornProb ψ p := h
    _ = 1 := hψ

/-- For a unitary circuit and normalized input, identity oracle query states number exactly
`QueryCount C`, are normalized, and have total query fiber mass one. This supplies the query
accounting used in [BennettEtAl1997]. -/
theorem workspace_query_inputs_accounting (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    (nullQueryInputs C ψ).length = QueryCount C ∧
    (∀ φ ∈ nullQueryInputs C ψ, Normalized φ ∧
      ∑ x : I, MeasureProb φ (workspaceQueryFiber (W := W) x) = 1) := by
  induction C generalizing ψ with
  | nil => exact ⟨rfl, fun φ hφ => False.elim ((List.mem_nil_iff φ).mp hφ)⟩
  | cons s C ih =>
    cases s with
    | gate U =>
      have hU : U ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := hC U List.mem_cons_self
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      exact ih (ApplyGate U ψ) hC' (normalized_applyGate hU hψ)
    | query =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      obtain ⟨hlen, hmem⟩ := ih ψ hC' hψ
      refine ⟨?_, ?_⟩
      · show (ψ :: nullQueryInputs C ψ).length = QueryCount (Step.query :: C)
        rw [List.length_cons, hlen]
        rfl
      · intro φ hφ
        rcases List.mem_cons.mp hφ with hφψ | hφC
        · subst hφψ
          exact ⟨hψ, measureProb_sum_workspaceQueryFiber hψ⟩
        · exact hmem φ hφC

/-- The workspace bit oracle for the constantly false function is the identity matrix. -/
theorem workspaceBitOracle_null : workspaceBitOracle (I := I) (W := W) (fun _ => false) = 1 := by
  have hbit : BitOracleOn (fun _ : I => false) = 1 := by
    ext ⟨i, b⟩ ⟨j, c⟩
    simp [BitOracleOn, permMatrix, BitFlip, Matrix.one_apply]
  rw [workspaceBitOracle, hbit, tensorGate_one]

/-- Every workspace bit oracle is unitary. -/
theorem workspaceBitOracle_unitary (f : I → Bool) :
    workspaceBitOracle (W := W) f ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
  tensorGate_unitary (bitOracleOn_unitary f) (Submonoid.one_mem _)

/-- The null workspace oracle is the identity, all workspace bit oracles are unitary, and a
singleton oracle changes a state by norm at most twice the square root of its query fiber
mass. See [Bennett et al., Theorem 3.3][BennettEtAl1997]. -/
theorem workspace_single_mark_query_l2 :
    (workspaceBitOracle (I := I) (W := W) (fun _ => false) = 1) ∧
    (∀ f : I → Bool,
      workspaceBitOracle (W := W) f ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ) ∧
    (∀ (x : I) (ψ : QState ((I × Bool) × W)),
      ‖toEuclidean_fromVec
        (ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x))) ψ - ψ)‖ ≤
        2 * Real.sqrt (MeasureProb ψ (workspaceQueryFiber (W := W) x))) := by
  refine ⟨workspaceBitOracle_null, workspaceBitOracle_unitary, ?_⟩
  intro x ψ
  have hdiff :
      ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x))) ψ - ψ
        = ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x)))
            (Collapse ψ (workspaceQueryFiber (W := W) x)) -
          Collapse ψ (workspaceQueryFiber (W := W) x) := by
    funext p
    obtain ⟨⟨i, b⟩, w⟩ := p
    show ApplyGate _ ψ ((i, b), w) - ψ ((i, b), w)
      = ApplyGate _ (Collapse ψ (workspaceQueryFiber (W := W) x)) ((i, b), w)
        - Collapse ψ (workspaceQueryFiber (W := W) x) ((i, b), w)
    rw [applyGate_workspaceBitOracle_mk, applyGate_workspaceBitOracle_mk]
    by_cases hi : i = x
    · have hdec : decide (i = x) = true := by simp [hi]
      rw [hdec]
      have hm : ∀ b' : Bool,
          (((i, b'), w) : (I × Bool) × W) ∈ workspaceQueryFiber (W := W) x :=
        fun b' => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [collapse_apply, collapse_apply, ite_eq_left (hm _), ite_eq_left (hm _)]
    · have hdec : decide (i = x) = false := decide_eq_false hi
      rw [hdec, Bool.xor_false]
      have hoff : ∀ b' : Bool,
          (((i, b'), w) : (I × Bool) × W) ∉ workspaceQueryFiber (W := W) x :=
        fun b' hmem => hi (Finset.mem_filter.mp hmem).2
      rw [collapse_apply, ite_eq_right (hoff _), sub_self, sub_self]
  rw [hdiff]
  have hsub :
      toEuclidean_fromVec
          (ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x)))
              (Collapse ψ (workspaceQueryFiber (W := W) x)) -
            Collapse ψ (workspaceQueryFiber (W := W) x))
        = toEuclidean_fromVec
            (ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x)))
              (Collapse ψ (workspaceQueryFiber (W := W) x)))
          - toEuclidean_fromVec (Collapse ψ (workspaceQueryFiber (W := W) x)) := by
    simp only [toEuclidean_fromVec, WithLp.toLp_sub]
  rw [hsub]
  calc ‖toEuclidean_fromVec (ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x)))
            (Collapse ψ (workspaceQueryFiber (W := W) x)))
          - toEuclidean_fromVec (Collapse ψ (workspaceQueryFiber (W := W) x))‖
      ≤ ‖toEuclidean_fromVec (ApplyGate (workspaceBitOracle (W := W) (fun y => decide (y = x)))
            (Collapse ψ (workspaceQueryFiber (W := W) x)))‖
          + ‖toEuclidean_fromVec (Collapse ψ (workspaceQueryFiber (W := W) x))‖ :=
        norm_sub_le _ _
    _ = 2 * ‖toEuclidean_fromVec (Collapse ψ (workspaceQueryFiber (W := W) x))‖ := by
        rw [norm_applyGate_of_mem_unitaryGroup
          (workspaceBitOracle_unitary (fun y => decide (y = x))) _]
        ring
    _ = 2 * Real.sqrt (MeasureProb ψ (workspaceQueryFiber (W := W) x)) := by
        rw [norm_toEuclidean_collapse_eq_sqrt_measureProb]

/-- For a unitary circuit, the final deviation between a singleton oracle and the identity
oracle is at most twice the sum of the square roots of the marked query masses along the
identity execution. See [Bennett et al., Theorem 3.3][BennettEtAl1997]. -/
theorem workspace_query_magnitude_hybrid (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (x : I) (hC : IsUnitaryCircuit C) :
    ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
        Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ≤
      2 * ((nullQueryInputs C ψ).map
        (fun φ => Real.sqrt (MeasureProb φ (workspaceQueryFiber (W := W) x)))).sum := by
  induction C generalizing ψ with
  | nil => simp [toEuclidean_fromVec]
  | cons s C ih =>
    cases s with
    | gate U =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      exact ih (ApplyGate U ψ) hC'
    | query =>
      have hC' : IsUnitaryCircuit C := fun V hV => hC V (List.mem_cons_of_mem _ hV)
      set O := workspaceBitOracle (W := W) (fun y => decide (y = x)) with hOdef
      have hsplit : Run O (Step.query :: C) ψ
            - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) (Step.query :: C) ψ
          = Run O C (ApplyGate O ψ - ψ)
            + (Run O C ψ - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) := by
        show Run O C (ApplyGate O ψ)
              - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C (ApplyGate 1 ψ)
            = Run O C (ApplyGate O ψ - ψ)
              + (Run O C ψ - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)
        rw [run_sub, applyGate_one]
        module
      rw [hsplit]
      have hadd :
          toEuclidean_fromVec (Run O C (ApplyGate O ψ - ψ)
              + (Run O C ψ - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ))
            = toEuclidean_fromVec (Run O C (ApplyGate O ψ - ψ))
              + toEuclidean_fromVec
                  (Run O C ψ - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ) := by
        simp only [toEuclidean_fromVec, WithLp.toLp_add]
      rw [hadd]
      have hhead : ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ψ))‖
          ≤ 2 * Real.sqrt (MeasureProb ψ (workspaceQueryFiber (W := W) x)) :=
        (norm_run_le O (workspaceBitOracle_unitary _) hC' _).trans
          ((workspace_single_mark_query_l2).2.2 x ψ)
      have htail := ih ψ hC'
      calc ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ψ))
              + toEuclidean_fromVec
                  (Run O C ψ - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖
          ≤ ‖toEuclidean_fromVec (Run O C (ApplyGate O ψ - ψ))‖
            + ‖toEuclidean_fromVec
                (Run O C ψ - Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ :=
            norm_add_le _ _
        _ ≤ 2 * Real.sqrt (MeasureProb ψ (workspaceQueryFiber (W := W) x))
            + 2 * ((nullQueryInputs C ψ).map
              (fun φ => Real.sqrt (MeasureProb φ (workspaceQueryFiber (W := W) x)))).sum :=
            add_le_add hhead htail
        _ = 2 * ((nullQueryInputs (Step.query :: C) ψ).map
              (fun φ => Real.sqrt (MeasureProb φ (workspaceQueryFiber (W := W) x)))).sum := by
            rw [nullQueryInputs_query, List.map_cons, List.sum_cons]
            ring

/-- For a unitary circuit and normalized initial state, the sum over all singleton marks of
squared final deviations from the identity execution is at most four times the squared query
count. See [Bennett et al., Theorem 3.3][BennettEtAl1997]. -/
theorem workspace_query_hybrid_energy (C : Circuit ((I × Bool) × W))
    (ψ : QState ((I × Bool) × W)) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) :
    (∑ x : I, ‖toEuclidean_fromVec
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
        Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2) ≤
      4 * (QueryCount C : ℝ) ^ 2 := by
  obtain ⟨hlen, hmem⟩ := workspace_query_inputs_accounting C ψ hC hψ
  set L := nullQueryInputs C ψ with hLdef
  have hG3 : ∀ x : I, ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
          Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖
      ≤ 2 * (L.map (fun φ => Real.sqrt (MeasureProb φ
          (workspaceQueryFiber (W := W) x)))).sum :=
    fun x => workspace_query_magnitude_hybrid C ψ x hC
  have hmap : ∀ x : I, (L.map (fun φ => Real.sqrt (MeasureProb φ
        (workspaceQueryFiber (W := W) x)))).sum
      = ∑ t : Fin L.length, Real.sqrt (MeasureProb (L.get t)
          (workspaceQueryFiber (W := W) x)) := by
    intro x
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    rfl
  have hcs : ∀ x : I, ((L.map (fun φ => Real.sqrt (MeasureProb φ
        (workspaceQueryFiber (W := W) x)))).sum) ^ 2
      ≤ (L.length : ℝ) * ∑ t : Fin L.length, MeasureProb (L.get t)
          (workspaceQueryFiber (W := W) x) := by
    intro x
    rw [hmap x]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin L.length))
      (fun t => Real.sqrt (MeasureProb (L.get t) (workspaceQueryFiber (W := W) x)))
      (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    rw [Finset.sum_congr rfl
      (fun t _ => Real.sq_sqrt (measureProb_nonneg _ _))] at h
    rwa [mul_comm] at h
  have hdx : ∀ x : I, ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
          Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2
      ≤ 4 * ((L.length : ℝ) * ∑ t : Fin L.length, MeasureProb (L.get t)
          (workspaceQueryFiber (W := W) x)) := by
    intro x
    have hsum_nonneg : 0 ≤ (L.map (fun φ => Real.sqrt (MeasureProb φ
        (workspaceQueryFiber (W := W) x)))).sum :=
      List.sum_nonneg fun a ha => by
        obtain ⟨φ, _, rfl⟩ := List.mem_map.mp ha
        exact Real.sqrt_nonneg _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hG3 x) 2
    have h3 := hcs x
    nlinarith [h2, h3, hsum_nonneg]
  calc ∑ x : I, ‖toEuclidean_fromVec
        (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C ψ -
          Run (1 : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ) C ψ)‖ ^ 2
      ≤ ∑ x : I, 4 * ((L.length : ℝ) * ∑ t : Fin L.length, MeasureProb (L.get t)
          (workspaceQueryFiber (W := W) x)) :=
        Finset.sum_le_sum fun x _ => hdx x
    _ = (4 * (L.length : ℝ)) * ∑ x : I, ∑ t : Fin L.length, MeasureProb (L.get t)
          (workspaceQueryFiber (W := W) x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = (4 * (L.length : ℝ)) * ∑ t : Fin L.length, ∑ x : I, MeasureProb (L.get t)
          (workspaceQueryFiber (W := W) x) := by rw [Finset.sum_comm]
    _ = (4 * (L.length : ℝ)) * (L.length : ℝ) := by
        rw [Finset.sum_congr rfl
          (fun t _ => (hmem (L.get t) (List.get_mem L t)).2)]
        simp
    _ = 4 * (QueryCount C : ℝ) ^ 2 := by
        have hcast : ((L.length : ℕ) : ℝ) = (QueryCount C : ℝ) :=
          congrArg Nat.cast hlen
        rw [hcast]
        ring

end Qatlib.Concepts.QueryComplexity.AdversarySearch
