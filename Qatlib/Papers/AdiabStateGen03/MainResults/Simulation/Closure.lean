/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Simulation.CommutingAssembly
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Simulation

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

theorem fin_sum_castSucc_mul {M : ℕ} (Hs : Fin (M + 1) → Ham n) :
    (∑ i : Fin M, Hs (Fin.castSucc i)) * Hs (Fin.last M)
      = ∑ i : Fin M, Hs (Fin.castSucc i) * Hs (Fin.last M) :=
  Finset.sum_mul _ _ _

theorem fin_sum_mul_castSucc {M : ℕ} (Hs : Fin (M + 1) → Ham n) :
    Hs (Fin.last M) * (∑ i : Fin M, Hs (Fin.castSucc i))
      = ∑ i : Fin M, Hs (Fin.last M) * Hs (Fin.castSucc i) :=
  Finset.mul_sum _ _ _

theorem simulatable_sum_of_pairwise_commute (M : ℕ) (Hs : Fin M → Ham n)
    (hcomm : ∀ i j : Fin M, Hs i * Hs j = Hs j * Hs i)
    (hsim : ∀ i, Simulatable (Hs i)) :
    Simulatable (∑ i, Hs i) := by
  induction M with
  | zero => simpa using simulatable_zero
  | succ M ih =>
      have hsplit : (∑ i : Fin (M + 1), Hs i)
          = (∑ i : Fin M, Hs (Fin.castSucc i)) + Hs (Fin.last M) :=
        Fin.sum_univ_castSucc Hs
      rw [hsplit]
      have ihsum : Simulatable (∑ i : Fin M, Hs (Fin.castSucc i)) :=
        ih _ (fun i j => hcomm _ _) (fun i => hsim _)
      have hlastcomm : (∑ i : Fin M, Hs (Fin.castSucc i)) * Hs (Fin.last M)
          = Hs (Fin.last M) * (∑ i : Fin M, Hs (Fin.castSucc i)) := by
        rw [fin_sum_castSucc_mul, fin_sum_mul_castSucc]
        exact Finset.sum_congr rfl (fun i _ => hcomm _ _)
      exact simulatable_add_of_commute hlastcomm ihsum (hsim (Fin.last M))

theorem real_smul_matrix (r : ℝ) (H : Ham n) : r • H = ((r : ℂ)) • H := by
  ext i j
  simp

theorem toOp_smul_ham (H : Ham n) (r : ℝ) : toOp (r • H) = r • toOp H := by
  rw [real_smul_matrix, real_smul_op]
  unfold toOp
  exact map_smul _ _ _

theorem timeEvolution_smul_ham (H : Ham n) (r t : ℝ) :
    timeEvolution (r • H) t = timeEvolution H (t * r) := by
  unfold timeEvolution
  rw [toOp_smul_ham]
  have h1 : (-t : ℝ) • (Complex.I • (r • toOp H))
      = (-(t * r) : ℝ) • (Complex.I • toOp H) := by
    simp only [real_smul_op, smul_smul]
    congr 1
    push_cast
    ring
  rw [h1]

theorem PolySize3.mono_time {C : Circuit n} {t t' α : ℝ} (ht' : 0 < t') (hα : 0 < α)
    (htt : t' ≤ t) (h : PolySize3 n t' α C) : PolySize3 n t α C := by
  obtain ⟨c, k, hc⟩ := h
  refine ⟨c, k, ?_⟩
  have hbase : (n : ℝ) + t' + 1 / α + 1 ≤ (n : ℝ) + t + 1 / α + 1 := by linarith
  have hpow : ((n : ℝ) + t' + 1 / α + 1) ^ k ≤ ((n : ℝ) + t + 1 / α + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) hbase k
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  calc (C.size : ℝ) ≤ (c : ℝ) * ((n : ℝ) + t' + 1 / α + 1) ^ k + (c : ℝ) := hc
    _ ≤ (c : ℝ) * ((n : ℝ) + t + 1 / α + 1) ^ k + (c : ℝ) := by
        have := mul_le_mul_of_nonneg_left hpow hc0
        linarith

theorem simulatable_smul_of_pos_le_one {H : Ham n} (hH : Simulatable H)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : Simulatable (r • H) := by
  intro t ht α hα hα1
  have htr : 0 < t * r := mul_pos ht hr0
  obtain ⟨C, hp, hd⟩ := hH (t * r) htr α hα hα1
  refine ⟨C, PolySize3.mono_time htr hα ?_ hp, ?_⟩
  · nlinarith
  · rwa [timeEvolution_smul_ham]

end Qatlib.Papers.AdiabStateGen03.MainResults.Simulation
