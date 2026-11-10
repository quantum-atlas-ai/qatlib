/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientAux
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoefficientDiagnostics
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped BigOperators

theorem multiproduct_node_pos (k : ℕ) (N : ℝ) (hN : 0 < N) (q : Fin (k+1)) :
    0 < mNode k N q := by
  unfold mNode
  split_ifs
  · positivity
  · exact hN

theorem multiproduct_squared_nodes_injective (k : ℕ) (N : ℝ) (hN : 0 < N)
    (hd : NodesDistinct k N) : Function.Injective (fun q => mNode k N q^2) := by
  intro i j h
  have he : mNode k N i = mNode k N j :=
    (sq_eq_sq₀ (le_of_lt (multiproduct_node_pos k N hN i))
      (le_of_lt (multiproduct_node_pos k N hN j))).mp h
  by_cases hi : i.val < k <;> by_cases hj : j.val < k
  · simp only [mNode, if_pos hi, if_pos hj] at he
    apply Fin.ext
    have hn : i.val + 1 = j.val + 1 := by exact_mod_cast he
    omega
  · simp only [mNode, if_pos hi, if_neg hj] at he
    exact (hd i hi he.symm).elim
  · simp only [mNode, if_neg hi, if_pos hj] at he
    exact (hd j hj he).elim
  · apply Fin.ext
    omega

theorem multiproductMoment : MultiproductMoment := by
  intro k N hN hd
  exact multiproduct_moments_of_squared_distinct k N
    (fun q => ne_of_gt (multiproduct_node_pos k N hN q))
    (multiproduct_squared_nodes_injective k N hN hd)

end Qatlib.Papers.HamLCUSim12.Multiproduct
