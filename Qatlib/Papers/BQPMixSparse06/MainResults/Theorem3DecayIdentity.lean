/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem2PathsReduction
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset Matrix

def cqrDoubled {N : ℕ} (W : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) (j : Fin N) : ℝ :=
  W (0, j) (0, j) - W (0, j) (1, j)

def graphLaplacian {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℝ) (d : ℝ) :
    Matrix ι ι ℝ :=
  d • (1 : Matrix ι ι ℝ) - W

theorem graphLaplacian_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (d : ℝ) (v : ι → ℝ) :
    graphLaplacian W d *ᵥ v = d • v - W *ᵥ v := by
  funext i
  rw [Pi.sub_apply, Pi.smul_apply]
  simp only [graphLaplacian, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.mulVec, dotProduct, smul_eq_mul]
  have hcongr : ∀ x : ι, (d * (if i = x then (1 : ℝ) else 0) - W i x) * v x =
      d * (if i = x then (1 : ℝ) else 0) * v x - W i x * v x := fun x => by ring
  have hone : (∑ x, d * (if i = x then (1 : ℝ) else 0) * v x) = d * v i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx
      rw [if_neg (Ne.symm hx)]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [hcongr, Finset.sum_sub_distrib, hone]

theorem dot_graphLaplacian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix ι ι ℝ) (d : ℝ) (ψ : ι → ℝ) (hnorm : dot ψ ψ = 1) :
    dot ψ (graphLaplacian W d *ᵥ ψ) = d - dot ψ (W *ᵥ ψ) := by
  rw [graphLaplacian_mulVec]
  have hsplit : dot ψ (d • ψ - W *ᵥ ψ) = dot ψ (d • ψ) - dot ψ (W *ᵥ ψ) := by
    unfold dot
    simp only [Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  have hd : dot ψ (d • ψ) = d * dot ψ ψ := by
    unfold dot
    simp only [Pi.smul_apply, smul_eq_mul]
    have hpt : ∀ i, ψ i * (d * ψ i) = d * (ψ i * ψ i) := fun i => by ring
    simp only [hpt]
    rw [← Finset.mul_sum]
  rw [hd, hnorm, mul_one]

theorem theorem3_cqr_state_identity {N : ℕ}
    (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) (j : Fin N)
    (hsym : M (0, j) (1, j) = M (1, j) (0, j))
    (hdiag : M (0, j) (0, j) = M (1, j) (1, j)) :
    dot (psiMinus j) (M *ᵥ psiMinus j) = cqrDoubled M j :=
  phiMinus_bilinear_eq M j hsym hdiag

lemma gammaBlock_diag_eq (a : ℤ) :
    gammaBlock a (0 : Fin 2) 0 = gammaBlock a (1 : Fin 2) 1 := by
  by_cases h0 : a = 0
  · simp [gammaBlock, h0]
  · by_cases h1 : a = 1
    · simp [gammaBlock, h1]
    · simp [gammaBlock, h0, h1]

lemma dot_psiMinus_self {N : ℕ} (j : Fin N) : dot (psiMinus j) (psiMinus j) = 1 := by
  have h := dot_psiMinus_lift (N := N) (w := (Pi.single j (1 : ℝ) : Fin N → ℝ)) j
  simpa [psiMinus, Pi.single_eq_same] using h

theorem blockConvert_cqr_state_identity {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hAsym : ∀ i j, A i j = A j i) (j : Fin N) :
    dot (psiMinus j) (blockConvert A *ᵥ psiMinus j) = cqrDoubled (blockConvert A) j := by
  refine theorem3_cqr_state_identity (blockConvert A) j
    (blockConvert_symm A hAsym (0, j) (1, j)) ?_
  show gammaBlock (A j j) (0 : Fin 2) 0 = gammaBlock (A j j) (1 : Fin 2) 1
  exact gammaBlock_diag_eq (A j j)

theorem theorem3_energy_identity {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hAsym : ∀ i j, A i j = A j i) (j : Fin N) :
    dot (psiMinus j) (graphLaplacian (blockConvert A) 4 *ᵥ psiMinus j) =
      4 - cqrDoubled (blockConvert A) j := by
  rw [dot_graphLaplacian (blockConvert A) 4 (psiMinus j) (dot_psiMinus_self j)]
  rw [blockConvert_cqr_state_identity A hAsym j]

theorem decay_fast_time {mu nu T M : ℝ} (hM : 0 < M)
    (hT : (nu - mu) * T = Real.log (6 * M)) :
    Real.exp (-(nu * T)) = (1 / (6 * M)) * Real.exp (-(mu * T)) := by
  have h6M : 0 < 6 * M := by positivity
  have h1 : Real.exp (-(nu * T)) =
      Real.exp (-(mu * T)) * Real.exp (-((nu - mu) * T)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-((nu - mu) * T)) = (6 * M)⁻¹ := by
    calc Real.exp (-((nu - mu) * T)) = Real.exp (-(Real.log (6 * M))) := by rw [hT]
      _ = (Real.exp (Real.log (6 * M)))⁻¹ := Real.exp_neg _
      _ = (6 * M)⁻¹ := by rw [Real.exp_log h6M]
  rw [h1, h2, one_div]
  ring

theorem decay_upper_bound {alpha_sq mu nu T M c : ℝ} (hM : 0 < M)
    (hslow : c ≤ alpha_sq / M * Real.exp (-(mu * T)) + Real.exp (-(nu * T)))
    (hfast : Real.exp (-(nu * T)) = (1 / (6 * M)) * Real.exp (-(mu * T))) :
    c ≤ (alpha_sq + 1 / 6) / M * Real.exp (-(mu * T)) := by
  have he : 0 < Real.exp (-(mu * T)) := Real.exp_pos _
  have h1 : c ≤ alpha_sq / M * Real.exp (-(mu * T)) +
      (1 / (6 * M)) * Real.exp (-(mu * T)) := by
    have := hslow
    rw [hfast] at this
    exact this
  have hid : alpha_sq / M * Real.exp (-(mu * T)) +
      (1 / (6 * M)) * Real.exp (-(mu * T)) =
        (alpha_sq + 1 / 6) / M * Real.exp (-(mu * T)) := by
    field_simp
  rwa [hid] at h1

theorem decay_bound_in_L {alpha_sq mu nu T M c : ℝ} (hM : 0 < M)
    (halpha : alpha_sq ≤ 1 / 3)
    (hslow : c ≤ alpha_sq / M * Real.exp (-(mu * T)) + Real.exp (-(nu * T)))
    (hfast : Real.exp (-(nu * T)) = (1 / (6 * M)) * Real.exp (-(mu * T))) :
    c ≤ 1 / (2 * M) * Real.exp (-(mu * T)) := by
  have hup := decay_upper_bound hM hslow hfast
  have he : 0 < Real.exp (-(mu * T)) := Real.exp_pos _
  have hmul : alpha_sq * M ≤ (1 / 3) * M :=
    mul_le_mul_of_nonneg_right halpha (le_of_lt hM)
  have hcoef : (alpha_sq + 1 / 6) / M ≤ 1 / (2 * M) := by
    rw [div_le_div_iff₀ hM (by positivity : (0 : ℝ) < 2 * M)]
    nlinarith [hmul]
  exact le_trans hup (mul_le_mul_of_nonneg_right hcoef (le_of_lt he))

theorem decay_bound_not_in_L {alpha_sq mu T M c : ℝ} (hM : 0 < M)
    (halpha : 2 / 3 ≤ alpha_sq)
    (hlow : alpha_sq / M * Real.exp (-(mu * T)) ≤ c) :
    2 / (3 * M) * Real.exp (-(mu * T)) ≤ c := by
  have he : 0 < Real.exp (-(mu * T)) := Real.exp_pos _
  have hmul : (2 / 3) * (3 * M) ≤ alpha_sq * (3 * M) :=
    mul_le_mul_of_nonneg_right halpha (by positivity)
  have hcoef : 2 / (3 * M) ≤ alpha_sq / M := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * M) hM]
    nlinarith [hmul]
  exact le_trans (mul_le_mul_of_nonneg_right hcoef (le_of_lt he)) hlow

theorem decay_thresholds_ordered {M : ℝ} (hM : 0 < M) :
    1 / (2 * M) < 2 / (3 * M) := by
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * M) (by positivity : (0 : ℝ) < 3 * M)]
  nlinarith

theorem decay_cases_disjoint {M e c : ℝ} (hM : 0 < M) (he : 0 < e) :
    ¬ (c ≤ 1 / (2 * M) * e ∧ 2 / (3 * M) * e ≤ c) := by
  intro h
  have hlt : 1 / (2 * M) * e < 2 / (3 * M) * e :=
    mul_lt_mul_of_pos_right (decay_thresholds_ordered hM) he
  linarith [h.1, h.2]

end Qatlib.Papers.BQPMixSparse06.MainResults
