/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
import Qatlib.Concepts.QueryComplexity.AdversarySearch.OrZeroErrorQueryLowerBoundBeal
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Papers.ElemDistinct00.MainResults.Defs
open Matrix

namespace Qatlib.Papers.ElemDistinct00.MainResults.Claw

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def stepMap (e : A ≃ B) : Step A → Step B
  | Step.gate U => Step.gate (relabelGate e U)
  | Step.query => Step.query

theorem run_map (e : A ≃ B) (O : Matrix A A ℂ) (C : Circuit A) (ψ : QState A) :
    Run (relabelGate e O) (C.map (stepMap e)) (relabelState e ψ)
      = relabelState e (Run O C ψ) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
        show Run (relabelGate e O) (C.map (stepMap e))
            (ApplyGate (relabelGate e U) (relabelState e ψ))
          = relabelState e (Run O C (ApplyGate U ψ))
        rw [applyGate_relabelGate]
        exact ih _
    | query =>
        show Run (relabelGate e O) (C.map (stepMap e))
            (ApplyGate (relabelGate e O) (relabelState e ψ))
          = relabelState e (Run O C (ApplyGate O ψ))
        rw [applyGate_relabelGate]
        exact ih _

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in

theorem queryCount_map (e : A ≃ B) (C : Circuit A) :
    QueryCount (C.map (stepMap e)) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simp only [List.map_cons, stepMap, QueryCount, ih]
    | query => simp only [List.map_cons, stepMap, QueryCount, ih]

theorem isUnitary_map (e : A ≃ B) (C : Circuit A) (h : IsUnitaryCircuit C) :
    IsUnitaryCircuit (C.map (stepMap e)) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    have hC : IsUnitaryCircuit C := by
      intro U hU
      exact h U (List.mem_cons_of_mem _ hU)
    cases s with
    | query =>
        simp only [List.map_cons, stepMap]
        exact (isUnitaryCircuit_query _).mpr (ih hC)
    | gate U =>
        have hU : U ∈ Matrix.unitaryGroup A ℂ := h U List.mem_cons_self
        simp only [List.map_cons, stepMap]
        exact (isUnitaryCircuit_gate _ _).mpr
          ⟨Qatlib.Concepts.BlockEncoding.StateBlockEncoding.unitaryGroup_reindex e hU, ih hC⟩

def e1 (M : ℕ) : Fin 1 × Fin M ≃ Fin M where
  toFun p := p.2
  invFun y := (0, y)
  left_inv p := by
    refine Prod.ext ?_ rfl
    exact Subsingleton.elim _ _
  right_inv _ := rfl

def we (M : ℕ) (W : Type) :
    ((Fin 1 × Fin M) × Bool) × W ≃ (Fin M × Bool) × W :=
  Equiv.prodCongr (Equiv.prodCongr (e1 M) (Equiv.refl Bool)) (Equiv.refl W)

theorem relabel_bitOracle {ι κ W : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype W] [DecidableEq W]
    (e : ι ≃ κ) (f : κ → Bool) :
    relabelGate (Equiv.prodCongr (Equiv.prodCongr e (Equiv.refl Bool))
        (Equiv.refl W)) (workspaceBitOracle (W := W) (fun i => f (e i)))
      = workspaceBitOracle (W := W) f := by
  unfold workspaceBitOracle
  rw [relabelGate_prodCongr]
  have hone : relabelGate (Equiv.refl W) (1 : Matrix W W ℂ) = 1 := by
    ext i j
    simp [relabelGate, Matrix.reindex_apply, Matrix.one_apply]
  rw [hone]
  congr 1
  unfold BitOracleOn permMatrix BitFlip
  ext p q
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm,
    Equiv.coe_refl, id_eq, Equiv.apply_symm_apply]
  have hiff : ((e.symm p.1, p.2) = (e.symm q.1, q.2 ^^ f q.1))
      ↔ (p = (q.1, q.2 ^^ f q.1)) := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      have h1' : p.1 = q.1 := by
        have := congrArg e h1
        simpa using this
      exact Prod.ext_iff.mpr ⟨h1', h2⟩
    · intro h
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
      exact Prod.ext_iff.mpr ⟨by rw [h1], h2⟩
  exact if_congr hiff rfl rfl

theorem measureProb_eq_zero_of_disjoint {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {ψ : QState Ω} {S N : Finset Ω} (hN : Normalized ψ) (hdisj : Disjoint S N)
    (hS : MeasureProb ψ S = 1) : MeasureProb ψ N = 0 := by
  have hunion : MeasureProb ψ (S ∪ N) = MeasureProb ψ S + MeasureProb ψ N := by
    unfold MeasureProb
    exact Finset.sum_union hdisj
  have hsub : S ∪ N ⊆ Finset.univ := Finset.subset_univ _
  have hle : MeasureProb ψ (S ∪ N) ≤ MeasureProb ψ Finset.univ := by
    unfold MeasureProb
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => bornProb_nonneg ψ i)
  rw [measureProb_univ hN] at hle
  have hnonneg := measureProb_nonneg ψ N
  linarith

theorem comparisonBit_const_one {M : ℕ} (g : Fin M → Bool) (p : Fin 1 × Fin M) :
    comparisonBit (fun _ : Fin 1 => (1 : ℤ)) (fun y => if g y then (1 : ℤ) else 0) p
      = g p.2 := by
  unfold comparisonBit
  by_cases h : g p.2 <;> simp [h]

theorem hasClaw_const_one {M : ℕ} (g : Fin M → Bool) :
    HasClaw (fun _ : Fin 1 => (1 : ℤ)) (fun y => if g y then (1 : ℤ) else 0)
      ↔ ∃ y, g y = true := by
  constructor
  · rintro ⟨x, y, hxy⟩
    by_cases h : g y
    · exact ⟨y, h⟩
    · simp [h] at hxy
  · rintro ⟨y, hy⟩
    exact ⟨0, y, by simp [hy]⟩

theorem exact_claw_lower {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hM : 0 < M)
    (hExact : ∀ (f : Fin 1 → ℤ) (g : Fin M → ℤ), HasClaw f g →
      MeasureProb (clawRun A f g) (clawSuccessSet A f g) = 1)
    (hNone : ∀ (f : Fin 1 → ℤ) (g : Fin M → ℤ), ¬ HasClaw f g →
      MeasureProb (clawRun A f g) (clawNoneSet A) = 1) :
    M ≤ QueryCount A.circuit := by
  let e := we M W
  let C' : Circuit ((Fin M × Bool) × W) := A.circuit.map (stepMap e)
  let ψ' : QState ((Fin M × Bool) × W) := relabelState e A.init
  let E0 : Finset ((Fin M × Bool) × W) := (clawNoneSet A).map e
  have hC' : IsUnitaryCircuit C' := isUnitary_map e A.circuit A.unitary

  have hno : ∀ g : Fin M → Bool, (∃ i : Fin M, g i = true) →
      MeasureProb (Run (workspaceBitOracle (W := W) g) C' ψ') E0 = 0 := by
    intro g hg
    have hbit : (fun p : Fin 1 × Fin M => g p.2)
        = comparisonBit (fun _ : Fin 1 => (1 : ℤ))
            (fun y => if g y then (1 : ℤ) else 0) := by
      funext p
      exact (comparisonBit_const_one g p).symm
    have horacle : workspaceBitOracle (W := W) g
        = relabelGate e (workspaceBitOracle (W := W) (fun p : Fin 1 × Fin M => g p.2)) := by
      rw [show e = Equiv.prodCongr (Equiv.prodCongr (e1 M) (Equiv.refl Bool))
          (Equiv.refl W) from rfl]
      exact (relabel_bitOracle (e1 M) g).symm
    have hrun : Run (workspaceBitOracle (W := W) g) C' ψ'
        = relabelState e (clawRun A (fun _ : Fin 1 => (1 : ℤ))
            (fun y => if g y then (1 : ℤ) else 0)) := by
      rw [horacle, hbit]
      show Run (relabelGate e (workspaceBitOracle
          (W := W) (comparisonBit (fun _ : Fin 1 => (1 : ℤ))
            (fun y => if g y then (1 : ℤ) else 0)))) C' ψ' = _
      rw [show C' = A.circuit.map (stepMap e) from rfl,
        show ψ' = relabelState e A.init from rfl, run_map]
      rfl
    rw [hrun, measureProb_relabelState]
    have hclaw : HasClaw (fun _ : Fin 1 => (1 : ℤ))
        (fun y => if g y then (1 : ℤ) else 0) := (hasClaw_const_one g).mpr hg
    have hnorm : Normalized (clawRun A (fun _ : Fin 1 => (1 : ℤ))
        (fun y => if g y then (1 : ℤ) else 0)) :=
      A.unitary.normalized_run (workspaceBitOracle_unitary _) A.norm
    have hdisj : Disjoint (clawSuccessSet A (fun _ : Fin 1 => (1 : ℤ))
        (fun y => if g y then (1 : ℤ) else 0)) (clawNoneSet A) := by
      rw [Finset.disjoint_left]
      intro p hpS hpN
      simp only [clawSuccessSet, clawNoneSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hpS hpN
      obtain ⟨a, b, hdec, _⟩ := hpS
      rw [hdec] at hpN
      exact absurd hpN (by simp)
    exact measureProb_eq_zero_of_disjoint hnorm hdisj (hExact _ _ hclaw)

  have hpos : 0 < MeasureProb
      (Run (workspaceBitOracle (W := W) (fun _ => false)) C' ψ') E0 := by
    have horacle : workspaceBitOracle (W := W) (fun _ : Fin M => false)
        = relabelGate e (workspaceBitOracle (W := W)
            (fun p : Fin 1 × Fin M => (fun _ : Fin M => false) p.2)) := by
      rw [show e = Equiv.prodCongr (Equiv.prodCongr (e1 M) (Equiv.refl Bool))
          (Equiv.refl W) from rfl]
      exact (relabel_bitOracle (e1 M) (fun _ => false)).symm
    have hbit : (fun p : Fin 1 × Fin M => (fun _ : Fin M => false) p.2)
        = comparisonBit (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin M => (0 : ℤ)) := by
      funext p
      simp [comparisonBit]
    have hrun : Run (workspaceBitOracle (W := W) (fun _ => false)) C' ψ'
        = relabelState e (clawRun A (fun _ : Fin 1 => (1 : ℤ)) (fun _ => (0 : ℤ))) := by
      rw [horacle, hbit]
      show Run (relabelGate e (workspaceBitOracle
          (W := W) (comparisonBit (fun _ : Fin 1 => (1 : ℤ)) (fun _ => (0 : ℤ)))))
        C' ψ' = _
      rw [show C' = A.circuit.map (stepMap e) from rfl,
        show ψ' = relabelState e A.init from rfl, run_map]
      rfl
    rw [hrun, measureProb_relabelState]
    have hnocl : ¬ HasClaw (fun _ : Fin 1 => (1 : ℤ)) (fun _ : Fin M => (0 : ℤ)) := by
      rintro ⟨x, y, hxy⟩
      simp at hxy
    have h := hNone _ _ hnocl
    rw [h]
    norm_num
  have hcard := orZeroErrorQueryLowerBound (I := Fin M) (W := W) C' ψ' E0
    (by simpa using hM) hno hpos
  simpa [C', queryCount_map] using hcard

theorem q2_claw_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hM6 : 6 ≤ M)
    (hB : ∀ (f : Fin 1 → ℤ) (g : Fin M → ℤ), HasClaw f g →
      (2 / 3 : ℝ) ≤ MeasureProb (clawRun A f g) (clawSuccessSet A f g)) :
    (M : ℝ) ≤ 64 * (QueryCount A.circuit : ℝ) ^ 2 := by
  let e := we M W
  let C' : Circuit ((Fin M × Bool) × W) := A.circuit.map (stepMap e)
  let ψ' : QState ((Fin M × Bool) × W) := relabelState e A.init
  let decode : ((Fin M × Bool) × W) → Option (Fin M) :=
    fun p => (A.decoder p.2).map (fun ab => ab.2)
  have hC' : IsUnitaryCircuit C' := isUnitary_map e A.circuit A.unitary
  have hψ' : Normalized ψ' := normalized_relabelState e A.norm
  have hmark : ∀ x : Fin M, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y => decide (y = x))) C' ψ')
      (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3 := by
    intro x
    let g : Fin M → Bool := fun y => decide (y = x)
    let gg : Fin M → ℤ := fun y => if g y then 1 else 0
    have hgg : ∀ b : Fin M, gg b = 1 ↔ b = x := by
      intro b
      unfold gg g
      by_cases h : b = x <;> simp [h]
    have hbit : (fun p : Fin 1 × Fin M => g p.2)
        = comparisonBit (fun _ : Fin 1 => (1 : ℤ)) gg := by
      funext p
      exact (comparisonBit_const_one g p).symm
    have horacle : workspaceBitOracle (W := W) g
        = relabelGate e (workspaceBitOracle (W := W) (fun p : Fin 1 × Fin M => g p.2)) := by
      rw [show e = Equiv.prodCongr (Equiv.prodCongr (e1 M) (Equiv.refl Bool))
          (Equiv.refl W) from rfl]
      exact (relabel_bitOracle (e1 M) g).symm
    have hrun : Run (workspaceBitOracle (W := W) g) C' ψ'
        = relabelState e (clawRun A (fun _ : Fin 1 => (1 : ℤ)) gg) := by
      rw [horacle, hbit]
      show Run (relabelGate e (workspaceBitOracle (W := W)
          (comparisonBit (fun _ : Fin 1 => (1 : ℤ)) gg))) C' ψ' = _
      rw [show C' = A.circuit.map (stepMap e) from rfl,
        show ψ' = relabelState e A.init from rfl, run_map]
      rfl
    have hset : (clawSuccessSet A (fun _ : Fin 1 => (1 : ℤ)) gg).map e
        = Finset.univ.filter (fun p : (Fin M × Bool) × W => decode p = some x) := by
      ext p
      constructor
      · intro hp
        rw [Finset.mem_map] at hp
        obtain ⟨q, hq, hpq⟩ := hp
        subst hpq
        simp only [clawSuccessSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        obtain ⟨a, b, hdec, hval⟩ := hq
        have hb : b = x := (hgg b).mp hval.symm
        subst hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decode]
        change Option.map (fun ab : Fin 1 × Fin M => ab.2) (A.decoder q.2) = some b
        rw [hdec]
        rfl
      · intro hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [Finset.mem_map]
        refine ⟨e.symm p, ?_, by simp⟩
        simp only [clawSuccessSet, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [decode] at hp
        rw [Option.map_eq_some_iff] at hp
        obtain ⟨ab, hdec, hb⟩ := hp
        refine ⟨ab.1, ab.2, hdec, ?_⟩
        rw [(hgg ab.2).mpr hb]
    have hclaw : HasClaw (fun _ : Fin 1 => (1 : ℤ)) gg := by
      refine (hasClaw_const_one g).mpr ⟨x, ?_⟩
      unfold g; simp
    rw [hrun, ← hset, measureProb_relabelState]
    exact hB _ _ hclaw
  have hcard : 6 ≤ Fintype.card (Fin M) := by simpa using hM6
  have h := workspace_search_query_lower_bound C' ψ' decode hC' hψ' hcard hmark
  simpa [C', QueryCount, queryCount_map] using h

theorem sqrt_div_eight_le_of_sq (M : ℕ) {Q : ℝ} (hQ : 0 ≤ Q)
    (h : (M : ℝ) ≤ 64 * Q ^ 2) : Real.sqrt (M : ℝ) / 8 ≤ Q := by
  have hsq : Real.sqrt (M : ℝ) ≤ Real.sqrt (64 * Q ^ 2) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)] at hsq
  have h8 : Real.sqrt (64 : ℝ) = 8 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h8, Real.sqrt_sq hQ] at hsq
  linarith

theorem claw_qe_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hE : ClawExact A) (hM : 0 < M) :
    (M : ℝ) ≤ (QueryCount A.circuit : ℝ) := by
  have h := exact_claw_lower A hM hE.1 hE.2
  exact_mod_cast h

theorem claw_q2_lower_at_one {M : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : ClawAlgorithm (Fin 1) (Fin M) ℤ W) (hB : ClawBoundedError A) (hM6 : 6 ≤ M) :
    Real.sqrt (M : ℝ) / 8 ≤ (QueryCount A.circuit : ℝ) :=
  sqrt_div_eight_le_of_sq M (by positivity) (q2_claw_lower_at_one A hM6 hB)

end Qatlib.Papers.ElemDistinct00.MainResults.Claw
