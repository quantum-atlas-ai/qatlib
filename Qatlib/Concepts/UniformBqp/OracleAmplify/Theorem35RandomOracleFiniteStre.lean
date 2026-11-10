/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.Theorem35RandomOracleFiniteStat
import Qatlib.Concepts.UniformBqp.OracleAmplify.Theorem35RandomOracleAux
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceMarkSetHybrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {K W : Type} [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W]

private def oracleCharge (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (A : (K → Bool) → (K → Bool)) (y : K → Bool) : ℝ :=
  ((oracleQueryInputs (bitQueryOf A) C ψ).map (fun φ =>
    MeasureProb φ (workspaceQuerySliceFiber (V := K → Bool) y))).sum

private theorem oracleCharge_nonneg (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (A : (K → Bool) → (K → Bool)) (y : K → Bool) : 0 ≤ oracleCharge C ψ A y :=
  List.sum_nonneg (fun z hz => by
    obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hz
    exact measureProb_nonneg _ _)

private theorem oracleCharge_sum (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (A : (K → Bool) → (K → Bool)) :
    (∑ y : K → Bool, oracleCharge C ψ A y) = (QueryCount C : ℝ) := by
  let L := oracleQueryInputs (bitQueryOf A) C ψ
  obtain ⟨hlen, hmem⟩ := oracle_query_inputs_accounting (bitQueryOf A) C ψ hC hψ
  have hm (y : K → Bool) : oracleCharge C ψ A y =
      ∑ i : Fin L.length, MeasureProb (L.get i) (workspaceQuerySliceFiber (V := K → Bool) y) := by
    unfold oracleCharge
    change (L.map (fun φ => MeasureProb φ (workspaceQuerySliceFiber (V := K → Bool) y))).sum = _
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    rfl
  calc
    _ = ∑ y : K → Bool, ∑ i : Fin L.length,
        MeasureProb (L.get i) (workspaceQuerySliceFiber (V := K → Bool) y) := Finset.sum_congr rfl (fun y _ => hm y)
    _ = ∑ i : Fin L.length, ∑ y : K → Bool,
        MeasureProb (L.get i) (workspaceQuerySliceFiber (V := K → Bool) y) := by rw [Finset.sum_comm]
    _ = ∑ _i : Fin L.length, (1 : ℝ) := Finset.sum_congr rfl (fun i _ =>
      workspace_query_slice_mass_partition (L.get i) (hmem _ (List.get_mem L i)).1)
    _ = (L.length : ℝ) := by simp
    _ = _ := by exact_mod_cast hlen

private theorem measureProb_subset {R : Type} [Fintype R] (φ : QState R)
    (S T : Finset R) (hST : S ⊆ T) : MeasureProb φ S ≤ MeasureProb φ T := by
  unfold MeasureProb
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by unfold BornProb; positivity)

private theorem oracle_update_hybrid_energy (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (hC : IsUnitaryCircuit C) (hψ : Normalized ψ) (A : (K → Bool) → (K → Bool)) (y : K → Bool) :
    ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (bitQueryOf (Function.update A y allOnes))) C ψ-
      Run (workspaceBitOracle (W := W) (bitQueryOf A)) C ψ)‖^2 ≤
      4*(QueryCount C : ℝ)*oracleCharge C ψ A y := by
  let B := Function.update A y allOnes
  let S := workspaceMarkFiber (W := W) (Finset.univ.filter
    (fun x : (K → Bool) × K => bitQueryOf A x ≠ bitQueryOf B x))
  have hsub : S ⊆ workspaceQuerySliceFiber (V := K → Bool) y := by
    intro p hp
    have hne := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2).2
    have heq : p.1.1.1 = y := by
      by_contra hn
      apply hne
      have hh : B p.1.1.1 = A p.1.1.1 := Function.update_of_ne hn allOnes A
      exact (congrFun hh p.1.1.2).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
  let L := oracleQueryInputs (bitQueryOf A) C ψ
  have hmass : (L.map (fun φ => MeasureProb φ S)).sum ≤ oracleCharge C ψ A y := by
    unfold oracleCharge
    change (L.map (fun φ => MeasureProb φ S)).sum ≤
      (L.map (fun φ => MeasureProb φ (workspaceQuerySliceFiber (V := K → Bool) y))).sum
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    conv_rhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_le_sum (fun i _ => measureProb_subset (L.get i) S _ hsub)
  exact (workspace_mark_set_hybrid_energy (bitQueryOf A) (bitQueryOf B) C ψ hC hψ).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity))

private theorem sqrt_gap_numeric : (Real.sqrt (1/3)+Real.sqrt (1/20))^2 < (2/3 : ℝ) := by
  have hx : Real.sqrt (1/3) ≤ (7/12 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/3)
    nlinarith only [hs, Real.sqrt_nonneg (1/3)]
  have hy : Real.sqrt (1/20) ≤ (9/40 : ℝ) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/20)
    nlinarith only [hs, Real.sqrt_nonneg (1/20)]
  have h :=
      pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt (1/3)+Real.sqrt (1/20)) (add_le_add hx hy) 2
  exact h.trans_lt (by norm_num : (7/12+9/40 : ℝ)^2 < 2/3)

theorem theorem3_5RandomOracleFinite : Theorem3_5RandomOracleFinite := by
  intro K W _ _ _ _ C ψ E hC hψ hT hTN
  classical
  let V := K → Bool
  let N := Fintype.card V
  let T := QueryCount C
  let fails := fun A : V → V => ¬decidesAtAllOnes (acceptProb C ψ E A) A
  let δ : ℝ := 1/(80*(T : ℝ))
  let S := fun A : V → V => Finset.univ.filter (fun y => δ ≤ oracleCharge C ψ A y)
  have hTR : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hsmall (A : V → V) : 2*(S A).card ≤ N := by
    have hcard : ((S A).card : ℝ)*δ ≤ (T : ℝ) := by
      calc
        _ = ∑ _y ∈ S A, δ := by simp
        _ ≤ ∑ y ∈ S A, oracleCharge C ψ A y :=
          Finset.sum_le_sum (fun y hy => (Finset.mem_filter.mp hy).2)
        _ ≤ ∑ y : V, oracleCharge C ψ A y :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun y _ _ => oracleCharge_nonneg C ψ A y)
        _ = _ := oracleCharge_sum C ψ hC hψ A
    have hδden : 0 < 80*(T : ℝ) := by positivity
    change ((S A).card : ℝ)*(1/(80*(T : ℝ))) ≤ (T : ℝ) at hcard
    rw [mul_one_div] at hcard
    have hc := (div_le_iff₀ hδden).mp hcard
    have hb : 2*((S A).card : ℝ) ≤ (N : ℝ) := by
      change 160*(T : ℝ)^2 ≤ (N : ℝ) at hTN
      nlinarith only [hc, hTN]
    exact_mod_cast hb
  have hupdate (A : V → V) (havoid : ∀ x, A x ≠ allOnes) (hgood : ¬fails A)
      (y : V) (hy : y ∉ S A) : fails (Function.update A y allOnes) := by
    let B := Function.update A y allOnes
    have hnotimage : allOnes ∉ Finset.univ.image A := by
      intro h
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
      exact havoid x hx
    have hdec : decidesAtAllOnes (acceptProb C ψ E A) A := not_not.mp hgood
    have hp : acceptProb C ψ E A ≤ 1/3 := hdec.2 hnotimage
    have hg : oracleCharge C ψ A y < δ := lt_of_not_ge (by
      intro h; exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have he := oracle_update_hybrid_energy C ψ hC hψ A y
    have hstrict := mul_lt_mul_of_pos_left hg (by positivity : 0 < 4*(T : ℝ))
    have hδeq : 4*(T : ℝ)*δ = 1/20 := by dsimp [δ]; field_simp; norm_num
    rw [hδeq] at hstrict
    have he' : ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (bitQueryOf B)) C ψ-
        Run (workspaceBitOracle (W := W) (bitQueryOf A)) C ψ)‖^2 ≤ (1/20 : ℝ) := he.trans hstrict.le
    have hnorm : ‖toEuclidean_fromVec (Run (workspaceBitOracle (W := W) (bitQueryOf B)) C ψ-
        Run (workspaceBitOracle (W := W) (bitQueryOf A)) C ψ)‖ ≤ Real.sqrt (1/20) := by
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/20)]
      exact he'
    have hl := measureProb_sqrt_lipschitz
      (Run (workspaceBitOracle (W := W) (bitQueryOf A)) C ψ)
      (Run (workspaceBitOracle (W := W) (bitQueryOf B)) C ψ) E
    have hgap :=
        (le_abs_self (Real.sqrt (acceptProb C ψ E B)-Real.sqrt (acceptProb C ψ E A))).trans hl
    have hsqrt : Real.sqrt (acceptProb C ψ E B) ≤ Real.sqrt (1/3)+Real.sqrt (1/20) := by
      have hpRoot := Real.sqrt_le_sqrt hp
      linarith only [hgap, hnorm, hpRoot]
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    have hpB : 0 ≤ acceptProb C ψ E B := measureProb_nonneg _ _
    rw [Real.sq_sqrt hpB] at hs
    have hplt : acceptProb C ψ E B < 2/3 := hs.trans_lt sqrt_gap_numeric
    have hhit : allOnes ∈ Finset.univ.image B :=
      Finset.mem_image.mpr ⟨y, Finset.mem_univ _, Function.update_self ..⟩
    intro h
    exact (not_le_of_gt hplt) (h.1 hhit)
  have hcount := random_oracle_failure_count (allOnes (K := K)) fails S
    (fun A _ _ => hsmall A) hupdate
  have hNpow : N = 2^(Fintype.card K) := by simp [N, V]
  have hk : 0 < Fintype.card K := by
    by_contra hn
    have hk0 : Fintype.card K = 0 := by omega
    have hN1 : N = 1 := by rw [hNpow, hk0]; rfl
    have hTR1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    change 160*(T : ℝ)^2 ≤ (N : ℝ) at hTN
    rw [hN1] at hTN
    norm_num at hTN
    nlinarith only [hTR1, hTN]
  have hNtwice : N = 2*(2^(Fintype.card K-1)) := by
    rw [hNpow]
    have he : Fintype.card K = Fintype.card K-1+1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  have havoid : N^N ≤ 4*(N-1)^N := by
    rw [hNtwice]
    exact even_oracle_avoid_count _ (by positivity)
  have hAvoidCard : Fintype.card {A : V → V // ∀ x, A x ≠ allOnes} = (N-1)^N :=
      random_oracle_avoid_card _
  have hTotal : Fintype.card (V → V) = N^N := Fintype.card_fun
  have hFailCard : Fintype.card {A : V → V // fails A} =
      (Finset.univ.filter (fun A : V → V => fails A)).card := Fintype.card_subtype fails
  rw [hAvoidCard] at hcount
  have hcount' : (N-1)^N ≤ 2*Fintype.card {A : V → V // fails A} := by
    simpa only [Fintype.card_eq_nat_card] using hcount
  have hfinal : Fintype.card (V → V) ≤ 8*(Finset.univ.filter (fun A : V → V => fails A)).card := by
    rw [hTotal]
    calc
      _ ≤ 4*(N-1)^N := havoid
      _ ≤ 4*(2*Fintype.card {A : V → V // fails A}) := Nat.mul_le_mul_left 4 hcount'
      _ = _ := by rw [hFailCard]; ring
  exact_mod_cast hfinal

end Qatlib.Concepts.UniformBqp.OracleAmplify
