/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphEnergy.ZeroEnergy.GraphEnergyKernelProofs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GraphEnergy.ZeroEnergy

open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem energy_zero_of_edge_constant [Nonempty V] (f : V → ℝ)
    (h : ∀ x y : V, G.Adj x y → f x = f y) : energy G f = 0 := by
  by_cases hv : volume G = 0
  · exact energy_eq_zero_of_volume_eq_zero G f hv
  · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    rw [energy_eq_lapQuadratic_div G hvpos f,
      (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj ℝ G f).2 h,
      zero_div]

theorem edge_constant_iff_reachable_constant (f : V → ℝ) :
    (∀ x y : V, G.Adj x y → f x = f y) ↔ ∀ x y : V, G.Reachable x y → f x = f y := by
  rw [← SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj ℝ G f,
    ← SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable ℝ G f]

theorem twoDisjointEdges_energy_eq_zero :
    energy twoDisjointEdges (fun x : Fin 4 => if x.val ≤ 1 then (0 : ℝ) else 1) = 0 := by
  refine energy_zero_of_edge_constant twoDisjointEdges _ ?_
  intro x y h
  have hx : x.val < 4 := x.isLt
  have hy : y.val < 4 := y.isLt
  unfold twoDisjointEdges at h
  rcases h with h | h
  · simp [show x.val ≤ 1 by omega, show y.val ≤ 1 by omega]
  · simp [show ¬ (x.val ≤ 1) by omega, show ¬ (y.val ≤ 1) by omega]

theorem twoDisjointEdges_not_constant :
    ¬ ∃ c : ℝ, ∀ x : Fin 4, (if x.val ≤ 1 then (0 : ℝ) else 1) = c := by
  rintro ⟨c, hc⟩
  have h0 : (if (0 : Fin 4).val ≤ 1 then (0 : ℝ) else 1) = c := hc 0
  have h2 : (if (2 : Fin 4).val ≤ 1 then (0 : ℝ) else 1) = c := hc 2
  norm_num at h0 h2
  linarith

theorem edgeWithIsolate_energy_eq_zero :
    energy edgeWithIsolate (fun x : Fin 3 => if x.val = 2 then (100 : ℝ) else 0) = 0 := by
  refine energy_zero_of_edge_constant edgeWithIsolate _ ?_
  intro x y h
  have hx : x.val < 3 := x.isLt
  have hy : y.val < 3 := y.isLt
  unfold edgeWithIsolate at h
  simp [show x.val ≠ 2 by omega, show y.val ≠ 2 by omega]

theorem edgeWithIsolate_degree_zero : degree edgeWithIsolate 0 = 1 := by
  unfold degree
  simp only [edgeWithIsolate, Fin.sum_univ_three]
  norm_num

theorem edgeWithIsolate_degree_two : degree edgeWithIsolate 2 = 0 := by
  unfold degree
  simp only [edgeWithIsolate, Fin.sum_univ_three]
  norm_num

theorem edgeWithIsolate_stationary_two : stationary edgeWithIsolate 2 = 0 := by
  have h1 : (1 : ℝ) ≤ volume edgeWithIsolate := by
    have hle : degree edgeWithIsolate 0 ≤ volume edgeWithIsolate := by
      unfold volume
      exact Finset.single_le_sum (fun z _ => degree_nonneg _ z) (Finset.mem_univ 0)
    rw [edgeWithIsolate_degree_zero] at hle
    exact hle
  have hv : volume edgeWithIsolate ≠ 0 := by linarith
  rw [stationary, if_neg hv, edgeWithIsolate_degree_two, zero_div]

theorem botFin3_kernel :
    ∀ x y : Fin 3, kernel (⊥ : SimpleGraph (Fin 3)) x y = if x = y then (1 : ℝ) else 0 := by
  intro x y
  have hd : degree (⊥ : SimpleGraph (Fin 3)) x = 0 := by
    unfold degree
    simp [SimpleGraph.bot_adj]
  exact kernel_eq_of_degree_eq_zero _ hd (y := y)

theorem botFin3_energy :
    energy (⊥ : SimpleGraph (Fin 3)) (fun x : Fin 3 => (x.val : ℝ)) = 0 := by
  refine energy_zero_of_edge_constant _ _ ?_
  intro x y h
  exact absurd h (by simp [SimpleGraph.bot_adj])

theorem botFin3_reachable :
    ∀ x y : Fin 3, (⊥ : SimpleGraph (Fin 3)).Reachable x y → x = y := fun _ _ h =>
  SimpleGraph.reachable_bot.1 h

theorem botFin1_energy : ∀ f : Fin 1 → ℝ, energy (⊥ : SimpleGraph (Fin 1)) f = 0 := by
  intro f
  refine energy_zero_of_edge_constant _ f ?_
  intro x y h
  exact absurd h (by simp [SimpleGraph.bot_adj])

theorem energy_zero_fin0 : ∀ f : Fin 0 → ℝ, energy (⊥ : SimpleGraph (Fin 0)) f = 0 := by
  intro f
  unfold energy
  simp

theorem singleEdgeFin2_degree (i : Fin 2) : degree singleEdgeFin2 i = 1 := by
  fin_cases i <;> unfold degree <;> simp only [singleEdgeFin2, Fin.sum_univ_two] <;> norm_num

theorem singleEdgeFin2_volume : volume singleEdgeFin2 = 2 := by
  rw [volume, Fin.sum_univ_two]
  simp only [singleEdgeFin2_degree]
  norm_num

theorem singleEdgeFin2_stationary (i : Fin 2) : stationary singleEdgeFin2 i = 1 / 2 := by
  rw [stationary, if_neg (by rw [singleEdgeFin2_volume]; norm_num), singleEdgeFin2_degree,
    singleEdgeFin2_volume]

theorem singleEdgeFin2_energy :
    energy singleEdgeFin2 (fun x : Fin 2 => (x.val : ℝ)) = 1 / 4 := by
  have hstat := singleEdgeFin2_stationary
  have k00 : kernel singleEdgeFin2 0 0 = 1 / 2 := by
    rw [kernel, singleEdgeFin2_degree 0]; simp [singleEdgeFin2]
  have k01 : kernel singleEdgeFin2 0 1 = 1 / 2 := by
    rw [kernel, singleEdgeFin2_degree 0]; simp [singleEdgeFin2]
  have k10 : kernel singleEdgeFin2 1 0 = 1 / 2 := by
    rw [kernel, singleEdgeFin2_degree 1]; simp [singleEdgeFin2]
  have k11 : kernel singleEdgeFin2 1 1 = 1 / 2 := by
    rw [kernel, singleEdgeFin2_degree 1]; simp [singleEdgeFin2]
  rw [energy, Fin.sum_univ_two]
  simp [hstat, k00, k01, k10, k11, Fin.sum_univ_two]
  norm_num

theorem singleEdgeFin2_variance :
    variance singleEdgeFin2 (fun x : Fin 2 => (x.val : ℝ)) = 1 / 4 := by
  have hstat := singleEdgeFin2_stationary
  have hmean : mean singleEdgeFin2 (fun x : Fin 2 => (x.val : ℝ)) = 1 / 2 := by
    rw [mean, Fin.sum_univ_two]
    simp [hstat]
  rw [variance, Fin.sum_univ_two, hmean]
  simp [hstat]
  norm_num

theorem reachable_kernel_and_consumers :
    (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ),
        (energy G f = 0 ↔ ∀ x y : V, G.Reachable x y → f x = f y)
        ∧ (G.Connected → (energy G f = 0 ↔ ∃ c : ℝ, ∀ x : V, f x = c)))
    ∧ (energy twoDisjointEdges (fun x : Fin 4 => if x.val ≤ 1 then (0 : ℝ) else 1) = 0
        ∧ ¬ ∃ c : ℝ, ∀ x : Fin 4, (if x.val ≤ 1 then (0 : ℝ) else 1) = c)
    ∧ (energy edgeWithIsolate (fun x : Fin 3 => if x.val = 2 then (100 : ℝ) else 0) = 0
        ∧ stationary edgeWithIsolate 2 = 0)
    ∧ (∀ x y : Fin 3, kernel (⊥ : SimpleGraph (Fin 3)) x y = if x = y then (1 : ℝ) else 0)
      ∧ energy (⊥ : SimpleGraph (Fin 3)) (fun x : Fin 3 => (x.val : ℝ)) = 0
      ∧ ∀ x y : Fin 3, (⊥ : SimpleGraph (Fin 3)).Reachable x y → x = y
    ∧ (∀ f : Fin 1 → ℝ, energy (⊥ : SimpleGraph (Fin 1)) f = 0)
    ∧ (∀ f : Fin 0 → ℝ, energy (⊥ : SimpleGraph (Fin 0)) f = 0)
    ∧ (energy singleEdgeFin2 (fun x : Fin 2 => (x.val : ℝ)) = 1 / 4
        ∧ variance singleEdgeFin2 (fun x : Fin 2 => (x.val : ℝ)) = 1 / 4) := by
  refine ⟨fun V _ _ _ G _ f => ⟨?_, ?_⟩,
    ⟨twoDisjointEdges_energy_eq_zero, twoDisjointEdges_not_constant⟩,
    ⟨edgeWithIsolate_energy_eq_zero, edgeWithIsolate_stationary_two⟩,
    ⟨botFin3_kernel, botFin3_energy, ?_⟩⟩
  · rw [(energy_zero_iff_edge_constant V G f).2.1]
    exact edge_constant_iff_reachable_constant G f
  · intro hconn
    haveI hne : Nonempty V := inferInstance
    obtain ⟨x₀⟩ := hne
    constructor
    · intro h0
      have hreach : ∀ x y : V, G.Reachable x y → f x = f y :=
        ((energy_zero_iff_edge_constant V G f).2.1.trans
          (edge_constant_iff_reachable_constant G f)).1 h0
      exact ⟨f x₀, fun x => (hreach x₀ x (hconn x₀ x)).symm⟩
    · rintro ⟨c, hc⟩
      refine ((energy_zero_iff_edge_constant V G f).2.1).2 ?_
      intro x y h
      rw [hc x, hc y]
  · intro x y h
    exact ⟨botFin3_reachable x y h, botFin1_energy, energy_zero_fin0,
      singleEdgeFin2_energy, singleEdgeFin2_variance⟩

end Qatlib.Concepts.GraphEnergy.ZeroEnergy
