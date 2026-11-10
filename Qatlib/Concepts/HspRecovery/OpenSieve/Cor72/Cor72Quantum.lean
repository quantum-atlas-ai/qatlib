/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Cor72Quantum

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection

theorem traceNorm_finset_sum_le {D : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Operator D) :
    (∑ i ∈ s, f i).traceNorm ≤ ∑ i ∈ s, (f i).traceNorm := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Matrix.traceNorm_add_le (f a) (∑ i ∈ s, f i)).trans
        (by linarith [ih])

theorem traceDistance_uniformMixture_le {D m : ℕ} (hm : 0 < m)
    (P Q : Fin m → Operator D) :
    traceDistance (((m : ℝ)⁻¹ : ℂ) • ∑ i, P i) (((m : ℝ)⁻¹ : ℂ) • ∑ i, Q i)
      ≤ (m : ℝ)⁻¹ * ∑ i, traceDistance (P i) (Q i) := by
  have hc : ‖(((m : ℝ)⁻¹ : ℂ))‖ = (m : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsub : (((m : ℝ)⁻¹ : ℂ) • ∑ i, P i) - (((m : ℝ)⁻¹ : ℂ) • ∑ i, Q i)
      = (((m : ℝ)⁻¹ : ℂ)) • (∑ i, P i - ∑ i, Q i) := by rw [smul_sub]
  have hsplit : (∑ i : Fin m, P i) - (∑ i : Fin m, Q i)
      = ∑ i : Fin m, (P i - Q i) := by rw [Finset.sum_sub_distrib]
  have hsum : (∑ i : Fin m, (P i - Q i)).traceNorm
      ≤ ∑ i : Fin m, (P i - Q i).traceNorm := traceNorm_finset_sum_le _ _
  have hgoal : (∑ i : Fin m, traceDistance (P i) (Q i))
      = ((∑ i : Fin m, (P i - Q i).traceNorm) / 2) := by
    have h1 : (∑ i : Fin m, traceDistance (P i) (Q i))
        = ∑ i : Fin m, ((P i - Q i).traceNorm / 2) :=
      Finset.sum_congr rfl fun i _ => rfl
    rw [h1, Finset.sum_div]
  have hL : traceDistance (((m : ℝ)⁻¹ : ℂ) • ∑ i, P i) (((m : ℝ)⁻¹ : ℂ) • ∑ i, Q i)
      = Matrix.traceNorm ((((m : ℝ)⁻¹ : ℂ) • ∑ i, P i)
          - (((m : ℝ)⁻¹ : ℂ) • ∑ i, Q i)) / 2 := rfl
  rw [hL, hsub, hsplit, Matrix.traceNorm_smul, hc, hgoal]
  have h1 : (m : ℝ)⁻¹ * (∑ i : Fin m, (P i - Q i)).traceNorm
      ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, (P i - Q i).traceNorm :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  nlinarith [h1]

@[simp] theorem traceDistance_self {D : ℕ} (ρ : Operator D) : traceDistance ρ ρ = 0 := by
  unfold traceDistance
  rw [sub_self, Matrix.traceNorm_zero, zero_div]

theorem traceDistance_outerProduct_le_one {D : ℕ} (u v : QState (Fin D))
    (hu : Normalized u) (hv : Normalized v) :
    traceDistance (outerProduct u) (outerProduct v) ≤ 1 := by
  have h := pure_trace_distance_le_re_inner u v hu hv
  have htrace : traceDistance (outerProduct u) (outerProduct v)
      = (outerProduct u - outerProduct v).traceNorm / 2 := rfl
  rw [htrace]
  refine h.trans ?_
  have hle : 1 - (Inner u v).re ^ 2 ≤ 1 := by
    have := sq_nonneg (Inner u v).re
    linarith
  calc Real.sqrt (1 - (Inner u v).re ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
    _ = 1 := Real.sqrt_one

theorem traceDistance_pureMixture_le_of_agrees {D m : ℕ} (hm : 0 < m)
    (u v : Fin m → QState (Fin D)) (hu : ∀ i, Normalized (u i))
    (hv : ∀ i, Normalized (v i)) (S : Finset (Fin m))
    (hagree : ∀ i, i ∉ S → u i = v i) :
    traceDistance (((m : ℝ)⁻¹ : ℂ) • ∑ i, outerProduct (u i))
        (((m : ℝ)⁻¹ : ℂ) • ∑ i, outerProduct (v i)) ≤ S.card / m := by
  have hmain := traceDistance_uniformMixture_le (D := D) (m := m) hm
    (fun i => outerProduct (u i)) (fun i => outerProduct (v i))
  refine hmain.trans ?_
  have hterm : ∀ i, traceDistance (outerProduct (u i)) (outerProduct (v i)) ≤ 1 :=
    fun i => traceDistance_outerProduct_le_one (u i) (v i) (hu i) (hv i)
  have hzero : ∀ i ∈ Finset.univ, i ∉ S →
      traceDistance (outerProduct (u i)) (outerProduct (v i)) = 0 := by
    intro i _ hi
    rw [hagree i hi, traceDistance_self]
  have hsum_eq : ∑ i : Fin m, traceDistance (outerProduct (u i)) (outerProduct (v i))
      = ∑ i ∈ S, traceDistance (outerProduct (u i)) (outerProduct (v i)) := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    exact hzero i (Finset.mem_univ i) hi
  rw [hsum_eq]
  have hbound : ∑ i ∈ S, traceDistance (outerProduct (u i)) (outerProduct (v i))
      ≤ ∑ _i ∈ S, (1 : ℝ) := Finset.sum_le_sum fun i _ => hterm i
  have hcard : ∑ _i ∈ S, (1 : ℝ) = (S.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc (m : ℝ)⁻¹ * ∑ i ∈ S, traceDistance (outerProduct (u i)) (outerProduct (v i))
      ≤ (m : ℝ)⁻¹ * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left (hbound.trans_eq hcard) (by positivity)
    _ = (S.card : ℝ) / m := by rw [div_eq_inv_mul]

theorem traceDistance_pureMixture_le_of_card_le {D m : ℕ} (hm : 0 < m)
    (u v : Fin m → QState (Fin D)) (hu : ∀ i, Normalized (u i))
    (hv : ∀ i, Normalized (v i)) (S : Finset (Fin m))
    (hagree : ∀ i, i ∉ S → u i = v i) (k : ℕ) (hk : S.card ≤ k) :
    traceDistance (((m : ℝ)⁻¹ : ℂ) • ∑ i, outerProduct (u i))
        (((m : ℝ)⁻¹ : ℂ) • ∑ i, outerProduct (v i)) ≤ (k : ℝ) / m := by
  refine (traceDistance_pureMixture_le_of_agrees hm u v hu hv S hagree).trans ?_
  have hk' : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  exact div_le_div_of_nonneg_right hk' (by positivity)

theorem gridCandidateCount (m : ℕ) : (Finset.range (2 ^ m)).card = 2 ^ m := by
  simp

theorem candidateCount_le (n : ℕ) :
    (2 : ℝ) ^ ((Nat.ceil (Real.sqrt (n : ℝ)) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ (Real.sqrt (n : ℝ) + 1) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h := Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))
  exact le_of_lt h

theorem cor72_enumeration_cost (C : ℝ) (_hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ ((Nat.ceil (Real.sqrt (n : ℝ)) : ℕ) : ℝ)
        * (2 : ℝ) ^ (C * Real.sqrt (n : ℝ))
      ≤ (2 : ℝ) ^ ((C + 2) * Real.sqrt (n : ℝ)) := by
  have hcount := candidateCount_le n
  have hprod : (2 : ℝ) ^ ((Nat.ceil (Real.sqrt (n : ℝ)) : ℕ) : ℝ)
        * (2 : ℝ) ^ (C * Real.sqrt (n : ℝ))
      ≤ (2 : ℝ) ^ (Real.sqrt (n : ℝ) + 1) * (2 : ℝ) ^ (C * Real.sqrt (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hcount (by positivity)
  refine hprod.trans ?_
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  nlinarith

end Qatlib.Concepts.HspRecovery.OpenSieve.Cor72Quantum
