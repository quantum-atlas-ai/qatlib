/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetInterrogation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def alphabetCoordinateShift {n a : ℕ} (i : Fin n) (c : ZMod a) :
    Equiv.Perm (Fin n → ZMod a) where
  toFun x := Function.update x i (x i + c)
  invFun x := Function.update x i (x i - c)
  left_inv x := by ext j; by_cases h : j = i <;> simp [h]
  right_inv x := by ext j; by_cases h : j = i <;> simp [h]

private theorem alphabet_single_diff {n a : ℕ} (x y : Fin n → ZMod a) (i : Fin n)
    (hc : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1) (hi : x i ≠ y i) :
    x = alphabetCoordinateShift i (x i - y i) y := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hij : i = j := by
    have hm : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hi]
    rw [hj] at hm
    exact Finset.mem_singleton.mp hm
  subst j
  ext k
  by_cases hk : k = i
  · subst k; simp [alphabetCoordinateShift]
  · have he : x k = y k := by
      by_contra h
      have hm : k ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [h]
      rw [hj] at hm
      exact hk (Finset.mem_singleton.mp hm)
    simp [alphabetCoordinateShift, hk, he]

private theorem alphabet_shift_diff {n a : ℕ} (i : Fin n) (c : ZMod a) (hc : c ≠ 0)
    (y : Fin n → ZMod a) :
    Finset.univ.filter (fun j => alphabetCoordinateShift i c y j ≠ y j) = {i} := by
  ext j
  by_cases h : j = i <;> simp [alphabetCoordinateShift, h, hc]

private theorem alphabetFilter_sum_perm {n a : ℕ} [NeZero a] (i : Fin n) :
    alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i =
      ∑ c ∈ Finset.univ.erase (0 : ZMod a), permMatrix (alphabetCoordinateShift i c) := by
  ext x y
  simp only [Matrix.sum_apply]
  by_cases hc : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1 ∧ x i ≠ y i
  · have hd : x i - y i ≠ 0 := sub_ne_zero.mpr hc.2
    rw [Finset.sum_eq_single (x i - y i)]
    · simp only [alphabetFilter, if_pos hc.2, alphabetCubeGamma, if_pos hc.1,
        permMatrix, Matrix.of_apply, if_pos (alphabet_single_diff x y i hc.1 hc.2)]
    · intro c _ hcd
      have hne : x ≠ alphabetCoordinateShift i c y := by
        intro h
        have hi := congrFun h i
        simp [alphabetCoordinateShift] at hi
        exact hcd (by rw [hi]; abel)
      simp [permMatrix, hne]
    · simp [hd]
  · have hzero : alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i x y = 0 := by
      simp only [alphabetFilter, alphabetCubeGamma]
      by_cases h : x i = y i <;> simp_all
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro c hcm
    have hd : c ≠ 0 := (Finset.mem_erase.mp hcm).1
    have hne : x ≠ alphabetCoordinateShift i c y := by
      intro h
      subst x
      exact hc ⟨by rw [alphabet_shift_diff i c hd y]; simp,
        by simp [alphabetCoordinateShift, hd]⟩
    simp [permMatrix, hne]

private theorem alphabetCubeGamma_sum (n a : ℕ) [NeZero a] :
    alphabetCubeGamma n a = ∑ i, alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i := by
  ext x y
  simp only [Matrix.sum_apply, alphabetFilter, alphabetCubeGamma]
  by_cases hc : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1
  · simp only [if_pos hc]
    rw [← Finset.sum_filter]
    simp [hc]
  · simp [hc]

private theorem alphabet_perm_ones {I : Type} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) :
    permMatrix e *ᵥ (fun _ => (1 : ℂ)) = (fun _ => (1 : ℂ)) := by
  ext x
  simp only [Matrix.mulVec, dotProduct, permMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro y _ hy
    have hxy : x ≠ e y := by
      intro h
      exact hy (by simpa using congrArg e.symm h.symm)
    simp [hxy]
  · simp

private theorem alphabet_nonzero_card (a : ℕ) [NeZero a] :
    ((Finset.univ.erase (0 : ZMod a)).card : ℝ) = (a : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  exact_mod_cast Nat.cast_sub (R:=ℝ) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne a))

private theorem alphabet_eigenvalue_le_norm {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (v : QState I) (lam : ℝ)
    (hv : 0 < ‖toEuclidean_fromVec v‖) (he : A *ᵥ v = (lam : ℂ) • v) : |lam| ≤ ‖A‖ := by
  have h := l2_norm_mulVec_fromVec_le A v
  rw [he, show toEuclidean_fromVec ((lam : ℂ) • v) = (lam : ℂ) • toEuclidean_fromVec v from rfl,
    norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  exact (mul_le_mul_iff_left₀ hv).mp h

private theorem alphabet_ones_norm_pos (n a : ℕ) [NeZero a] :
    0 < ‖toEuclidean_fromVec (fun _ : Fin n → ZMod a => (1 : ℂ))‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin n → ZMod a) => z (fun _ => 0)) hz
  simp at h

private theorem alphabetFilter_ones {n a : ℕ} [NeZero a] (i : Fin n) :
    alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i *ᵥ (fun _ => (1 : ℂ)) =
      (((a : ℝ) - 1 : ℝ) : ℂ) • (fun _ => (1 : ℂ)) := by
  rw [alphabetFilter_sum_perm, Matrix.sum_mulVec]
  simp_rw [alphabet_perm_ones]
  ext x
  simp only [Finset.sum_apply, Finset.sum_const, nsmul_eq_mul, mul_one, Pi.smul_apply, smul_eq_mul]
  exact_mod_cast alphabet_nonzero_card a

private theorem alphabetFilter_norm {n a : ℕ} [NeZero a] (ha : 2 ≤ a) (i : Fin n) :
    ‖alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i‖ = (a : ℝ) - 1 := by
  apply le_antisymm
  · rw [alphabetFilter_sum_perm]
    calc _ ≤ ∑ c ∈ Finset.univ.erase (0 : ZMod a), ‖permMatrix (alphabetCoordinateShift i c)‖ := norm_sum_le _ _
      _ = _ := by
        simp_rw [l2_norm_unitary_eq_one (permMatrix_unitary_of_injective (alphabetCoordinateShift i _).injective)]
        simpa using alphabet_nonzero_card a
  · have h := alphabet_eigenvalue_le_norm _ _ ((a : ℝ) - 1)
      (alphabet_ones_norm_pos n a) (alphabetFilter_ones i)
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
    rw [abs_of_nonneg (by linarith : 0 ≤ (a : ℝ) - 1)] at h
    exact h

theorem alphabet_hamming_actual_witness_norms (n a : ℕ) [NeZero a] (ha : 2 ≤ a) :
    (alphabetCubeGamma n a).IsHermitian ∧
    ‖alphabetCubeGamma n a‖ = (n : ℝ) * ((a : ℝ) - 1) ∧
    (∀ i : Fin n, ‖alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i‖ = (a : ℝ) - 1) := by
  have hG : (alphabetCubeGamma n a).IsHermitian := by
    ext x y
    have he : Finset.univ.filter (fun i => y i ≠ x i) = Finset.univ.filter (fun i => x i ≠ y i) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
    simp [Matrix.conjTranspose_apply, alphabetCubeGamma, he]
  refine ⟨hG, ?_, alphabetFilter_norm ha⟩
  apply le_antisymm
  · rw [alphabetCubeGamma_sum]
    calc _ ≤ ∑ i : Fin n, ‖alphabetFilter (fun x : Fin n → ZMod a => x) (alphabetCubeGamma n a) i‖ := norm_sum_le _ _
      _ = _ := by simp only [alphabetFilter_norm ha, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have he : alphabetCubeGamma n a *ᵥ (fun _ => (1 : ℂ)) =
        (((n : ℝ) * ((a : ℝ) - 1) : ℝ) : ℂ) • (fun _ => (1 : ℂ)) := by
      rw [alphabetCubeGamma_sum, Matrix.sum_mulVec]
      simp_rw [alphabetFilter_ones]
      ext x
      simp only [Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Pi.smul_apply, smul_eq_mul, mul_one, Complex.ofReal_mul, Complex.ofReal_natCast]
    have h := alphabet_eigenvalue_le_norm _ _ ((n : ℝ) * ((a : ℝ) - 1))
      (alphabet_ones_norm_pos n a) he
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (show 0 ≤ (a : ℤ) - 1 by omega)))] at h
    exact h

theorem alphabet_interrogation_matching_lower_bound
    (W : Type) [Fintype W] [DecidableEq W] (n a : ℕ) [NeZero a]
    (C : Circuit ((Fin n × ZMod a) × W)) (ψ : QState ((Fin n × ZMod a) × W))
    (label : ((Fin n × ZMod a) × W) → (Fin n → ZMod a)) (eps : ℝ)
    (ha : 2 ≤ a) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1 / 2)
    (hs : ∀ x : Fin n → ZMod a, 1 - eps ≤ MeasureProb (Run (alphabetOracle x) C ψ)
      (Finset.univ.filter (fun p => label p = x))) :
    (1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * (n : ℝ) ≤ 2 * (QueryCount C) := by
  obtain ⟨hG, hnorm, hfilter⟩ := alphabet_hamming_actual_witness_norms n a ha
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : 0 < (a : ℝ) - 1 := by linarith
  have hz : ∀ x y : Fin n → ZMod a, x = y → alphabetCubeGamma n a x y = 0 := by
    intro x y h; subst y; simp [alphabetCubeGamma]
  have h := multioutput_adversary_actual_circuit_lower_bound (Fin n → ZMod a) W (Fin n → ZMod a)
    n a (fun x => x) (alphabetCubeGamma n a) (fun x => x) label C ψ eps ((a : ℝ) - 1)
    hG hz hC hψ he0 he1 (le_of_lt hap) (fun i => le_of_eq (hfilter i)) hs
  rw [hnorm] at h
  have h' : ((1 - 2 * Real.sqrt (eps * (1 - eps)) - 2 * eps) * (n : ℝ)) * ((a : ℝ) - 1) ≤
      (2 * (QueryCount C)) * ((a : ℝ) - 1) := by nlinarith [h]
  exact (mul_le_mul_iff_left₀ hap).mp h'

theorem alphabet_interrogation_upper_and_lower (n a : ℕ) [NeZero a] (hn : 0 < n) (ha : 2 ≤ a) :
    ∃ (C : Circuit ((Fin n × ZMod a) × (Fin n → ZMod a)))
      (j : (Fin n × ZMod a) × (Fin n → ZMod a)),
      IsUnitaryCircuit C ∧ QueryCount C = n ∧ GateCount C ≤ 3 * n + 1 ∧
      (∀ x : Fin n → ZMod a, MeasureProb (Run (alphabetOracle x) C (Ket j))
        (Finset.univ.filter (fun p => p.2 = x)) = 1) ∧
      (n : ℝ) ≤ 2 * QueryCount C := by
  obtain ⟨C, j, hC, hq, hg, hs⟩ := alphabet_interrogation_actual_output_and_counts n a hn
  refine ⟨C, j, hC, hq, hg, hs, ?_⟩
  simpa using alphabet_interrogation_matching_lower_bound (Fin n → ZMod a) n a C (Ket j)
    Prod.snd 0 ha hC (normalized_ket j) (by norm_num) (by norm_num) (by intro x; rw [hs x]; norm_num)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
