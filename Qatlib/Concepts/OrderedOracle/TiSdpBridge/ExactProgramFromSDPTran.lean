/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ExactProgramFromSDPStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.OrderedOracle.TiSdpBridge
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

theorem ti_final_psd_matrix {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (htr : A.trace = 1) (hfin : 1 ≤ (A 0 0).re) :
    ∀ i j, A i j = if i = 0 ∧ j = 0 then 1 else 0 := by
  classical
  have hdiag (i : Fin n) : 0 ≤ (A i i).re := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1
  have him (i : Fin n) : (A i i).im = 0 := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).2.symm
  have hsum : ∑ i : Fin n, (A i i).re = 1 := by
    simpa [Matrix.trace, Matrix.diag_apply] using congrArg Complex.re htr
  have hb : (A 0 0).re ≤ ∑ i : Fin n, (A i i).re :=
    Finset.single_le_sum (fun i _ => hdiag i) (Finset.mem_univ 0)
  rw [hsum] at hb
  have h0 : (A 0 0).re = 1 := le_antisymm hb hfin
  have he : ∑ i ∈ (Finset.univ : Finset (Fin n)).erase 0, (A i i).re = 0 := by
    have hh := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (A i i).re) (Finset.mem_univ 0)
    rw [hsum] at hh
    try dsimp at hh
    linarith
  have hd (j : Fin n) (hj : j ≠ 0) : A j j = 0 := by
    have hr := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hdiag i)).mp he
      j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    apply Complex.ext <;> simp [hr, him j]
  have haa : A 0 0 = 1 := by apply Complex.ext <;> simp [h0, him 0]
  intro i j
  by_cases hj : j = 0
  · subst j
    by_cases hi : i = 0
    · subst i
      simpa using haa
    · have hc := posSemidef_column_zero_of_diag_zero A hA i (hd i hi) 0
      have hh := hA.isHermitian.apply i 0
      simpa [hi, hc] using hh.symm
  · have hc := posSemidef_column_zero_of_diag_zero A hA j (hd j hj) i
    simpa [hj] using hc

theorem genTrace_first_projector {n : ℕ} [NeZero n] (j : ℤ) :
    genTrace (Matrix.of (fun i i' : Fin n => if i = 0 ∧ i' = 0 then (1 : ℂ) else 0)) j =
      if j = 0 then 1 else 0 := by
  classical
  unfold genTrace
  rw [Finset.sum_eq_single (0 : Fin n)]
  · rw [Finset.sum_eq_single (0 : Fin n)]
    · simp [Matrix.of_apply, eq_comm]
    · intro b _ hb
      simp [Matrix.of_apply, hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    simp [Matrix.of_apply, hb]
  · simp

theorem exactProgramFromSDP : ExactProgramFromSDP := by
  intro n k _ h
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨Q, hps, hQ, htr, hfin, hroot⟩ := (lemma11_tiSDPFeasible_iff_rootForm n k 0).mp h
  let q : ℕ → Fin n → ℝ := fun t i => (genTrace (Q t) ((i : ℕ) : ℤ)).re
  have hQt (t : ℕ) (ht : t ∈ Finset.Icc 0 k) : (Q t).trace = 1 := by
    by_cases h0 : t = 0
    · subst t
      exact ti_initial_trace n Q hQ
    · apply htr
      simp only [Finset.mem_Icc] at ht ⊢
      omega
  have hQ0 : Q 0 = (n : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin n => (1 : ℂ)) := by
    ext i j
    simpa using hQ i j
  have hQk : Q k = Matrix.of (fun i j : Fin n => if i = 0 ∧ j = 0 then (1 : ℂ) else 0) := by
    ext i j
    apply ti_final_psd_matrix (Q k) (hps k)
    · exact hQt k (by simp)
    · simpa using hfin
  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    change (genTrace (Q 0) ((i : ℕ) : ℤ)).re = fejerCoeffs n i
    rw [hQ0, genTrace_onesDiv]
    simp [fejerCoeffs, abs_of_nonneg (Int.natCast_nonneg (i : ℕ))]
  · constructor
    · change (genTrace (Q k) (0 : ℤ)).re = 1
      rw [hQk, genTrace_first_projector]
      simp
    · intro j hj
      have hj0 : j ≠ 0 := ne_of_gt hj
      change (genTrace (Q k) ((j : ℕ) : ℤ)).re = 0
      rw [hQk, genTrace_first_projector]
      simp [hj0]
  · intro t ht
    change (genTrace (Q t) (0 : ℤ)).re = 1
    rw [genTrace_zero, hQt t ht]
    simp
  · intro t ht z hz
    have hcircle := norm_eq_one_of_twisted_root hn t hz
    have hsz : (star z) ^ n = (-1 : ℂ) ^ t := by rw [← star_pow, hz]; simp
    change laurentEval (fun i : Fin n => (genTrace (Q t) ((i : ℕ) : ℤ)).re) z =
      laurentEval (fun i : Fin n => (genTrace (Q (t - 1)) ((i : ℕ) : ℤ)).re) z
    rw [laurentEval_real_genTrace _ (hps t).isHermitian hcircle,
      laurentEval_real_genTrace _ (hps (t - 1)).isHermitian hcircle,
      hroot t ht z hz, hroot t ht (star z) hsz]
  · intro t _ z hz
    exact laurentEval_real_genTrace_nonneg (Q t) (hps t) hz

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
