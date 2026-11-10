/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.TensorSupport
variable {N R M k d : ℕ} {J : ℝ}
namespace Hamiltonian

def nested (h : Hamiltonian N R M k d J) (seed : Fin R) : List (Fin R)→Matrix (Register N) (Register N) ℂ
  | []=>h.term seed
  | a::w=>h.term a*h.nested seed w-h.nested seed w*h.term a

def region (h : Hamiltonian N R M k d J) (seed : Fin R) : List (Fin R)→Finset (Fin N)
  | []=>h.support seed
  | a::w=>h.support a∪h.region seed w

theorem nested_supported (h : Hamiltonian N R M k d J) (seed : Fin R) (w : List (Fin R)) :
    h.nested seed w∈onSupport (h.region seed w) := by
  induction w with
  | nil=>exact h.supported seed
  | cons a w ih=>exact commutator_mem_union _ _ (h.supported a) ih

theorem region_card (h : Hamiltonian N R M k d J) (seed : Fin R) (w : List (Fin R)) :
    (h.region seed w).card ≤ (w.length+1)*k := by
  induction w with
  | nil=>simpa only [region,List.length_nil,zero_add,one_mul] using h.locality seed
  | cons a w ih=>
    simp only [region,List.length_cons]
    calc
      _ ≤ (h.support a).card+(h.region seed w).card := Finset.card_union_le _ _
      _ ≤ k+(w.length+1)*k := Nat.add_le_add (h.locality a) ih
      _=(w.length+1+1)*k := by ring

theorem nested_norm (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (seed : Fin R) (w : List (Fin R)) :
    ‖h.nested seed w‖ ≤ J^(w.length+1) := by
  induction w with
  | nil=>simpa only [nested,List.length_nil,zero_add,pow_one] using (h.strength seed).trans (by linarith)
  | cons a w ih=>
    simp only [nested,List.length_cons]
    calc
      _ ≤ ‖h.term a*h.nested seed w‖+‖h.nested seed w*h.term a‖ := norm_sub_le _ _
      _ ≤ ‖h.term a‖*‖h.nested seed w‖+‖h.nested seed w‖*‖h.term a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (J/2)*J^(w.length+1)+J^(w.length+1)*(J/2) := by gcongr <;> exact h.strength a
      _=J^(w.length+1+1) := by rw [pow_succ]; ring

def active (h : Hamiltonian N R M k d J) (m : Fin M) (s : Finset (Fin N)) : Finset (Fin R) :=
  (h.labels m).filter (fun i=>i∈h.neighbors s)

theorem active_card (h : Hamiltonian N R M k d J) (m : Fin M) (s : Finset (Fin N)) :
    (h.active m s).card ≤ s.card*d := by
  exact (Finset.card_le_card (by intro i hi; exact (Finset.mem_filter.mp hi).2)).trans
      (h.neighbors_card s)

theorem grouped_commutator (h : Hamiltonian N R M k d J) (m : Fin M) (s : Finset (Fin N))
    (B : Matrix (Register N) (Register N) ℂ) (hB : B∈onSupport s) :
    h.grouped m*B-B*h.grouped m=∑i∈h.active m s,(h.term i*B-B*h.term i) := by
  unfold grouped active
  rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hn:i∈h.neighbors s
  · simp [hn]
  · have hc:=h.nonneighbor_commute s B hB i hn
    simp only [hn,if_false,hc.eq,sub_self]

theorem grouped_commutator_norm (h : Hamiltonian N R M k d J) (hJ : 0 ≤ J) (m : Fin M)
    (s : Finset (Fin N)) (B : Matrix (Register N) (Register N) ℂ) (hB : B∈onSupport s) :
    ‖h.grouped m*B-B*h.grouped m‖ ≤ (s.card*d:ℕ)*J*‖B‖ := by
  rw [h.grouped_commutator m s B hB]
  calc
    _ ≤ ∑i∈h.active m s,‖h.term i*B-B*h.term i‖ := norm_sum_le _ _
    _ ≤ ∑_i∈h.active m s,J*‖B‖ := Finset.sum_le_sum (fun i _=>by
      calc
        _ ≤ ‖h.term i*B‖+‖B*h.term i‖ := norm_sub_le _ _
        _ ≤ ‖h.term i‖*‖B‖+‖B‖*‖h.term i‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ (J/2)*‖B‖+‖B‖*(J/2) := by gcongr <;> exact h.strength i
        _=J*‖B‖ := by ring)
    _=(h.active m s).card*(J*‖B‖) := by simp
    _ ≤ (s.card*d:ℕ)*(J*‖B‖) := by gcongr; exact h.active_card m s
    _=_ := by ring

end Hamiltonian
end Qatlib.Papers.LowEnergyProd24.LocalModel
