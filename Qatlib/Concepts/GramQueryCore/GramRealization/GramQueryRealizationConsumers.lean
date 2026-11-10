/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.GramQueryCore.GramRealization

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem gram_isometry_gate_transport {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L)
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    ∃ V : Matrix K K ℂ, V ∈ Matrix.unitaryGroup K ℂ ∧ V * L = L * U := by
  apply gram_equal_actual_unitary_transport K H L (L * U)
  have hu : Uᴴ * U = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hU
  change Lᴴ * L = (L * U)ᴴ * (L * U)
  rw [Matrix.conjTranspose_mul]
  calc
    _ = 1 := hL
    _ = Uᴴ * U := hu.symm
    _ = Uᴴ * (Lᴴ * L) * U := by rw [hL, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

noncomputable def gramLiftGate {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L)
    (U : Matrix H H ℂ) : Matrix K K ℂ :=
  if hU : U ∈ Matrix.unitaryGroup H ℂ then
    Classical.choose (gram_isometry_gate_transport L hL U hU) else 1

theorem gramLiftGate_unitary {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L)
    (U : Matrix H H ℂ) : gramLiftGate L hL U ∈ Matrix.unitaryGroup K ℂ := by
  unfold gramLiftGate
  split_ifs with hU
  · exact (Classical.choose_spec (gram_isometry_gate_transport L hL U hU)).1
  · exact (Matrix.unitaryGroup K ℂ).one_mem

theorem gramLiftGate_intertwining {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L)
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    gramLiftGate L hL U * L = L * U := by
  rw [gramLiftGate, dif_pos hU]
  exact (Classical.choose_spec (gram_isometry_gate_transport L hL U hU)).2

noncomputable def gramLiftCircuit {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L) : Circuit H → Circuit K
  | [] => []
  | Step.gate U :: C => Step.gate (gramLiftGate L hL U) :: gramLiftCircuit L hL C
  | Step.query :: C => Step.query :: gramLiftCircuit L hL C

theorem gramLiftCircuit_queryCount {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L) (C : Circuit H) :
    QueryCount (gramLiftCircuit L hL C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [gramLiftCircuit, ih]

theorem gramLiftCircuit_unitary {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L) (C : Circuit H) :
    IsUnitaryCircuit (gramLiftCircuit L hL C) := by
  induction C with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U => simpa only [gramLiftCircuit, isUnitaryCircuit_gate] using ⟨gramLiftGate_unitary L hL U, ih⟩
    | query => simpa only [gramLiftCircuit, isUnitaryCircuit_query] using ih

theorem gramLiftCircuit_run {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L)
    (O : Matrix H H ℂ) (P : Matrix K K ℂ) (hO : P * L = L * O)
    (C : Circuit H) (hC : IsUnitaryCircuit C) (ψ : QState H) :
    Run P (gramLiftCircuit L hL C) (L *ᵥ ψ) = L *ᵥ Run O C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      simp only [gramLiftCircuit, Run, ApplyGate]
      rw [Matrix.mulVec_mulVec, gramLiftGate_intertwining L hL U hU, ← Matrix.mulVec_mulVec]
      exact ih hC' _
    | query =>
      have hC' := (isUnitaryCircuit_query C).mp hC
      simp only [gramLiftCircuit, Run, ApplyGate]
      rw [Matrix.mulVec_mulVec, hO, ← Matrix.mulVec_mulVec]
      exact ih hC' _

theorem gram_isometry_inner {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (L : Matrix K H ℂ) (hL : IsIsometry L)
    (ψ φ : QState H) : Qatlib.Foundations.PureStateMath.Inner (L *ᵥ ψ) (L *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hL, Matrix.vecMul_one]

noncomputable def gramBasisFrame {H K : Type} [DecidableEq K] (e : H ↪ K) : Matrix K H ℂ :=
  fun k h => if k = e h then 1 else 0

theorem gramBasisFrame_isIsometry {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (e : H ↪ K) : IsIsometry (gramBasisFrame e) := by
  unfold IsIsometry
  ext h j
  simp [gramBasisFrame, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, eq_comm, e.injective.eq_iff]

theorem gramBasisFrame_apply_image {H K : Type} [Fintype H] [DecidableEq H] [DecidableEq K]
    (e : H ↪ K) (ψ : QState H) (h : H) : (gramBasisFrame e *ᵥ ψ) (e h) = ψ h := by
  simp [gramBasisFrame, Matrix.mulVec, dotProduct, e.injective.eq_iff]

theorem gramBasisFrame_apply_outside {H K : Type} [Fintype H] [DecidableEq K]
    (e : H ↪ K) (ψ : QState H) (k : K) (hk : ¬∃ h, e h = k) :
    (gramBasisFrame e *ᵥ ψ) k = 0 := by
  have hn (h : H) : k ≠ e h := fun he => hk ⟨h, he.symm⟩
  simp [gramBasisFrame, Matrix.mulVec, dotProduct, hn]

noncomputable def gramBasisReadout {H K Z : Type} (e : H ↪ K) (r : H → Z) (fallback : Z) : K → Z :=
  fun k => if hk : ∃ h, e h = k then r (Classical.choose hk) else fallback

theorem gramBasisReadout_image {H K Z : Type} (e : H ↪ K) (r : H → Z) (fallback : Z) (h : H) :
    gramBasisReadout e r fallback (e h) = r h := by
  rw [gramBasisReadout, dif_pos (show ∃ a, e a = e h from ⟨h, rfl⟩)]
  congr 1
  apply e.injective
  exact Classical.choose_spec (show ∃ a, e a = e h from ⟨h, rfl⟩)

theorem gramBasisFrame_measureProb {H K Z : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] [DecidableEq Z] (e : H ↪ K) (ψ : QState H)
    (r : H → Z) (fallback z : Z) :
    MeasureProb (gramBasisFrame e *ᵥ ψ)
      (Finset.univ.filter (fun k => gramBasisReadout e r fallback k = z)) =
        MeasureProb ψ (Finset.univ.filter (fun h => r h = z)) := by
  let S := Finset.univ.filter (fun h => r h = z)
  let T := Finset.univ.filter (fun k => gramBasisReadout e r fallback k = z)
  have hsub : S.map e ⊆ T := by
    intro k hk
    obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hk
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
        (gramBasisReadout_image e r fallback h).trans (Finset.mem_filter.mp hh).2⟩
  have hz (k : K) (hk : k ∈ T) (hn : k ∉ S.map e) : BornProb (gramBasisFrame e *ᵥ ψ) k = 0 := by
    have hout : ¬∃ h, e h = k := by
      rintro ⟨h, rfl⟩
      apply hn
      apply Finset.mem_map.mpr
      refine ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      rw [← gramBasisReadout_image e r fallback h]
      exact (Finset.mem_filter.mp hk).2
    simp [BornProb, gramBasisFrame_apply_outside e ψ k hout]
  change (∑ k ∈ T, BornProb (gramBasisFrame e *ᵥ ψ) k) = ∑ h ∈ S, BornProb ψ h
  rw [← Finset.sum_subset hsub hz, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro h _
  simp only [BornProb, gramBasisFrame_apply_image]

theorem gram_witness_same_count_exact_bit_query_consumer :
    ∀ (X Z : Type) [Fintype X] [DecidableEq X] [Nonempty X]
      [Fintype Z] [DecidableEq Z] (n T : ℕ) [NeZero n] (input : X → Fin n → Bool)
      (label : X → Z) (G : Fin (T + 1) → Matrix X X ℂ)
      (M : Fin T → Fin (n + 1) → Matrix X X ℂ), gramQueryWitness n T input G M →
      (∀ x y, label x ≠ label y → G ⟨T, by omega⟩ x y = 0) →
      ∃ (R : ℕ) (C : Circuit ((Fin n × Bool) × Fin R)) (j : (Fin n × Bool) × Fin R)
        (readout : (Fin n × Bool) × Fin R → Z), 0 < R ∧ QueryCount C = T ∧
        (∀ U, Step.gate U ∈ C → U ∈ Matrix.unitaryGroup _ ℂ) ∧
        ∀ x : X, MeasureProb (Run (workspaceBitOracle (W := Fin R) (input x)) C (Qatlib.Foundations.PureStateMath.Ket j))
          (Finset.univ.filter (fun z => readout z = label x)) = 1 := by
  intro X Z _ _ _ _ _ n T _ input label G M hw hlabel
  obtain ⟨R, C, j, r, hR, hCq, hCu, hcorrect⟩ :=
    gram_witness_actual_exact_phase_query_algorithm X Z n T input label G M hw hlabel
  let H := Fin (n + 1) × Fin R
  let K := (Fin n × Bool) × Fin R
  let L : Matrix K H ℂ := gramBitLift n R
  let x0 : X := Classical.choice inferInstance
  have hL : IsIsometry L :=
    (gram_idle_phase_actual_single_bit_query_bridge n R (input x0)).1
  have hdim : Fintype.card H ≤ Fintype.card K := by
    simp only [H, K, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    have hn := NeZero.pos n
    nlinarith
  let e : H ↪ K := Classical.choice (Function.Embedding.nonempty_of_card_le hdim)
  let J := gramBasisFrame e
  have hJ : IsIsometry J := gramBasisFrame_isIsometry e
  have hGram : Lᴴ * L = Jᴴ * J := by rw [hL, hJ]
  obtain ⟨B1, hB1, hB1L⟩ := gram_equal_actual_unitary_transport K H L J hGram
  let S : Matrix K (Fin 1) ℂ := fun k _ => Qatlib.Foundations.PureStateMath.Ket (e j) k
  let A : Matrix K (Fin 1) ℂ := fun k _ => (L *ᵥ Qatlib.Foundations.PureStateMath.Ket j) k
  have hseed : Sᴴ * S = Aᴴ * A := by
    ext u v
    change Qatlib.Foundations.PureStateMath.Inner
        (Qatlib.Foundations.PureStateMath.Ket (e j))
        (Qatlib.Foundations.PureStateMath.Ket (e j)) = Qatlib.Foundations.PureStateMath.Inner (L *ᵥ Qatlib.Foundations.PureStateMath.Ket j) (L *ᵥ Qatlib.Foundations.PureStateMath.Ket j)
    rw [gram_isometry_inner L hL]
    rw [(normalized_iff_inner_self _).mp (normalized_ket (e j)),
      (normalized_iff_inner_self _).mp (normalized_ket j)]
  obtain ⟨B0, hB0, hB0S⟩ := gram_equal_actual_unitary_transport K (Fin 1) S A hseed
  have hprep : B0 *ᵥ Qatlib.Foundations.PureStateMath.Ket (e j) = L *ᵥ Qatlib.Foundations.PureStateMath.Ket j := by
    funext k
    exact congrArg (fun V : Matrix K (Fin 1) ℂ => V k 0) hB0S
  let C' := [Step.gate B0] ++ gramLiftCircuit L hL C ++ [Step.gate B1]
  let r' := gramBasisReadout e r (label x0)
  have hC'q : QueryCount C' = T := by
    simp only [C', queryCount_append, queryCount_gate, queryCount_nil,
      gramLiftCircuit_queryCount, zero_add, add_zero, hCq]
  have hC'u : IsUnitaryCircuit C' := by
    simp only [C', isUnitaryCircuit_append, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
    exact ⟨⟨hB0, gramLiftCircuit_unitary L hL C⟩, hB1⟩
  refine ⟨R, C', e j, r', hR, hC'q, hC'u, ?_⟩
  intro x
  have hO : workspaceBitOracle (W := Fin R) (input x) * L = L * gramPhaseQuery n R (input x) :=
    (gram_idle_phase_actual_single_bit_query_bridge n R (input x)).2
  have hrun : Run (workspaceBitOracle (W := Fin R) (input x)) C' (Qatlib.Foundations.PureStateMath.Ket (e j)) =
      J *ᵥ Run (gramPhaseQuery n R (input x)) C (Qatlib.Foundations.PureStateMath.Ket j) := by
    dsimp [C']
    rw [run_append]
    simp only [Run, ApplyGate]
    rw [hprep, gramLiftCircuit_run L hL _ _ hO C hCu, Matrix.mulVec_mulVec, hB1L]
  rw [hrun]
  exact (gramBasisFrame_measureProb e (Run (gramPhaseQuery n R (input x)) C (Qatlib.Foundations.PureStateMath.Ket j))
    r (label x0) (label x)).trans (hcorrect x)

end Qatlib.Concepts.GramQueryCore.GramRealization
