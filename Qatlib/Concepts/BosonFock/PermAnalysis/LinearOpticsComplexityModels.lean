/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
public import Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStabilityThec
public import Qatlib.Foundations.ProbabilityCore.Concentration.GaussianShiftTVDBoundThec
public import Qatlib.Concepts.BosonFock.PermAnalysis.BosonDistributionNormalizationThec
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Algebra.Order.Chebyshev
public import Qatlib.Concepts.BosonFock.PermAnalysis.LinearOpticsComplexityModelsSampling
public import Qatlib.Concepts.BosonFock.PermAnalysis.LinearOpticsComplexityModelsPermanent
public import Qatlib.Concepts.BosonFock.PermAnalysis.LinearOpticsComplexityModelsGaussian

@[expose] public section
open Qatlib.Concepts.BosonFock.PermAnalysis
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.CountingClasses.ClassTransport

set_option autoImplicit false

namespace Qatlib.Concepts.BosonFock.PermAnalysis

open Qatlib.Foundations.ComplexGeometry.PhaseRecovery Qatlib.Foundations.ProbabilityCore.Concentration

open Qatlib

open scoped BigOperators Nat ComplexConjugate Matrix

open Module MeasureTheory

/-- Every complex matrix with orthonormal columns and at least as many rows as columns admits a
unitary completion. -/
private theorem clause17_unitaryCompletion (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ)
    (hA : Aᴴ * A = 1) (hnm : n ≤ m) :
    Nonempty (LoCompletedUnitary m n hnm A) := by
  classical
  let v : Fin n → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
  have hvapply : ∀ (j : Fin n) (i : Fin m), v j i = A i j := fun _ _ => rfl
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    have h1 : v i = WithLp.toLp 2 (Aᵀ i) := rfl
    have h2 : v j = WithLp.toLp 2 (Aᵀ j) := rfl
    rw [h1, h2, inner_matrix_col_col A A i j, hA, Matrix.one_apply]
  have hli : LinearIndependent ℂ v := hv.linearIndependent
  set S : Submodule ℂ (EuclideanSpace ℂ (Fin m)) := Submodule.span ℂ (Set.range v) with hSdef
  have hdimS : finrank ℂ S = n := by
    rw [hSdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hdimV : finrank ℂ (EuclideanSpace ℂ (Fin m)) = m :=
    finrank_euclideanSpace_fin
  have hdimperp : finrank ℂ Sᗮ = m - n := by
    have hadd := S.finrank_add_finrank_orthogonal
    rw [hdimS, hdimV] at hadd
    omega
  have hvmem : ∀ j, v j ∈ S := fun j => Submodule.subset_span (Set.mem_range_self j)
  let b : OrthonormalBasis (Fin (m - n)) ℂ Sᗮ :=
    (stdOrthonormalBasis ℂ Sᗮ).reindex (finCongr hdimperp)
  have hbite : ∀ k k' : Fin (m - n),
      inner ℂ (b k : Sᗮ) (b k' : Sᗮ) = if k = k' then (1 : ℂ) else 0 :=
    fun k k' => orthonormal_iff_ite.mp b.orthonormal k k'
  have hbmem : ∀ k : Fin (m - n), ((b k : Sᗮ) : EuclideanSpace ℂ (Fin m)) ∈ Sᗮ :=
    fun k => (b k).2
  let c : Fin m → EuclideanSpace ℂ (Fin m) := fun j =>
    if h : (j : ℕ) < n then v ⟨j, h⟩
    else (b ⟨(j : ℕ) - n, by omega⟩ : Sᗮ)
  have hc_cols : ∀ j : Fin n, c (Fin.castLE hnm j) = v j := by
    intro j
    show (if h : (Fin.castLE hnm j : ℕ) < n then v ⟨Fin.castLE hnm j, h⟩
      else (b ⟨(Fin.castLE hnm j : ℕ) - n, by omega⟩ : Sᗮ)) = v j
    rw [dite_eq_left (show (Fin.castLE hnm j : ℕ) < n by simp)]
    have hfin : (⟨(Fin.castLE hnm j : ℕ), by simp⟩ : Fin n) = j := by
      rw [Fin.ext_iff]
      simp
    rw [hfin]
  have hc_memperp : ∀ j : Fin m, n ≤ (j : ℕ) → c j ∈ Sᗮ := by
    intro j hj
    simp only [c]
    rw [dite_eq_right (by omega : ¬(j : ℕ) < n)]
    exact hbmem _
  have hc_orth : ∀ i j : Fin m, inner ℂ (c i) (c j) = if i = j then (1 : ℂ) else 0 := by
    intro i j
    by_cases hi : (i : ℕ) < n
    · by_cases hj : (j : ℕ) < n
      · have e1 : c i = v ⟨i, hi⟩ := by
          simp only [c]; rw [dite_eq_left hi]
        have e2 : c j = v ⟨j, hj⟩ := by
          simp only [c]; rw [dite_eq_left hj]
        rw [e1, e2, orthonormal_iff_ite.mp hv]
        by_cases heq : i = j
        · subst heq
          simp
        · have hne2 : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := by
            intro hh
            apply heq
            ext
            simp only [Fin.ext_iff] at hh
            exact hh
          rw [ite_eq_right hne2, ite_eq_right heq]
      · have hj' : n ≤ (j : ℕ) := by omega
        have e1 : c i = v ⟨i, hi⟩ := by
          simp only [c]; rw [dite_eq_left hi]
        have h0 : inner ℂ (c i) (c j) = 0 := by
          rw [e1]
          exact Submodule.inner_right_of_mem_orthogonal (hvmem _) (hc_memperp j hj')
        rw [h0]
        have hne2 : i ≠ j := by
          intro hh
          simp [hh] at hi hj
          omega
        rw [ite_eq_right hne2]
    · have hi' : n ≤ (i : ℕ) := by omega
      by_cases hj : (j : ℕ) < n
      · have e2 : c j = v ⟨j, hj⟩ := by
          simp only [c]; rw [dite_eq_left hj]
        have h0 : inner ℂ (c j) (c i) = 0 := by
          rw [e2]
          exact Submodule.inner_right_of_mem_orthogonal (hvmem _) (hc_memperp i hi')
        have h0' : inner ℂ (c i) (c j) = 0 := by
          rw [← inner_conj_symm, h0, map_zero]
        rw [h0']
        have hne2 : i ≠ j := by
          intro hh
          simp [hh] at hi hj
          omega
        rw [ite_eq_right hne2]
      · have hj' : n ≤ (j : ℕ) := by omega
        have hi2 : c i = (b ⟨(i : ℕ) - n, by omega⟩ : Sᗮ) := by
          simp only [c]; rw [dite_eq_right (by omega : ¬(i : ℕ) < n)]
        have hj2 : c j = (b ⟨(j : ℕ) - n, by omega⟩ : Sᗮ) := by
          simp only [c]; rw [dite_eq_right (by omega : ¬(j : ℕ) < n)]
        rw [hi2, hj2, ← Submodule.coe_inner, hbite]
        by_cases heq : i = j
        · subst heq
          simp
        · have hnn : (⟨(i : ℕ) - n, by omega⟩ : Fin (m - n))
              ≠ ⟨(j : ℕ) - n, by omega⟩ := by
            intro hh
            apply heq
            ext
            have hh' : ((i : ℕ) - n) = ((j : ℕ) - n) := by
              simpa using congrArg Fin.val hh
            omega
          rw [ite_eq_right hnn, ite_eq_right heq]
  refine ⟨⟨Matrix.of fun i j => c j i, ?_, ?_⟩⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    have hcol : ∀ k : Fin m, WithLp.toLp 2 ((Matrix.of fun i j => c j i)ᵀ k) = c k := by
      intro k
      have h1 : (Matrix.of fun i j => c j i)ᵀ k = WithLp.ofLp (c k) := rfl
      rw [h1, WithLp.toLp_ofLp]
    rw [← inner_matrix_col_col (Matrix.of fun i j => c j i) (Matrix.of fun i j => c j i) i j,
      hcol i, hcol j, hc_orth, Matrix.one_apply]
  · intro i j
    rw [Matrix.of_apply, hc_cols, hvapply]

/-- An isometry with at least twice as many rows as columns admits a unitary completion whose
Fock and physical output distributions agree with its isometry distribution. -/
theorem clause17_clause1 : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∀ (_hmn : 2 * n ≤ m),
    Nonempty (LoCompletedUnitary m n (by omega : n ≤ m) A)
    ∧ (∀ W : LoCompletedUnitary m n (by omega : n ≤ m) A, ∀ S : FockOccupation m n,
        loFockDist m n (by omega : n ≤ m) W.U S = loIsometryDist m n A S)
    ∧ (∀ (W : LoCompletedUnitary m n (by omega : n ≤ m) A) (G : loInterferometer m),
        loInterferometerMatrix m G = W.U → ∀ S : FockOccupation m n,
          loPhysicalDist m n (by omega : n ≤ m) G S = loIsometryDist m n A S) := by
  intro m n A hA _hmn
  have hnm : n ≤ m := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact clause17_unitaryCompletion m n A hA hnm
  · intro W S
    exact loFockDist_eq_of_extendCols W S
  · intro W G hG S
    rw [loPhysicalDist_eq_loFockDist m n (by omega : n ≤ m) G S, hG]
    exact loFockDist_eq_of_extendCols W S

/-- Under the stated hypotheses, establishes pointwise and triangle bounds for sampler error and
the existence of a bounded estimator with the specified relative-error guarantee. -/
theorem clause17_clause6 :
    Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStability →
    Qatlib.Foundations.ProbabilityCore.Concentration.GaussianShiftTVDBound →
    LoPaccHypothesis →
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∀ (ε_s δ η : ℝ), 0 < ε_s → 0 < δ → δ < 1 → 0 < η → η < 1 →
    ∀ Sam : LoSampler m n,
      loTvDist (loSamplerDist Sam) (loIsometryDist m n A) ≤ ε_s →

      (∀ S : FockOccupation m n,
          |loSamplerDist Sam S - loIsometryDist m n A S|
            ≤ 2 * loTvDist (loSamplerDist Sam) (loIsometryDist m n A))

      ∧ (∀ B : Matrix (Fin m) (Fin n) ℚ,
          loTvDist (loSamplerDist Sam) (loIsometryDist m n (loOfRat m n B))
            ≤ loTvDist (loSamplerDist Sam) (loIsometryDist m n A)
              + loTvDist (loIsometryDist m n A) (loIsometryDist m n (loOfRat m n B)))

      ∧ (∀ S₀ : FockOccupation m n,
          ε_s ≤ δ / 2 * loIsometryDist m n A S₀ →
          ∃ est : LoFbppEstimator m n,
            est.q ≤ 64 * (m + n + 1) ^ 4 + 64 * Nat.ceil (Real.logb 2 (1 / η))
            ∧ est.qlen ≤ 64 * (m + n + 1) ^ 4
            ∧ ∀ np : List Bool → Bool,
                (∑ coins : Fin est.q → Bool,
                    if |(est.out np coins : ℝ) - loIsometryDist m n A S₀|
                        ≤ δ * loIsometryDist m n A S₀ then (1 : ℝ) else 0)
                  / ((2 : ℕ) ^ est.q : ℝ) ≥ 1 - η) := by
  intro _hTri _hGau _hPacc m n A _hA ε_s δ η hεs hδ hδ1 hη hη1 Sam _hSam
  refine ⟨fun S => loTvDist_apply_le (loSamplerDist Sam) (loIsometryDist m n A) S,
    fun B => loTvDist_triangle (loSamplerDist Sam) (loIsometryDist m n A)
      (loIsometryDist m n (loOfRat m n B)), ?_⟩
  intro S₀ hS₀

  have hmul : 0 < δ / 2 * loIsometryDist m n A S₀ := lt_of_lt_of_le hεs hS₀
  have hp0 : 0 < loIsometryDist m n A S₀ := by
    by_cases hp : 0 < loIsometryDist m n A S₀
    · exact hp
    · exfalso
      have hnp : loIsometryDist m n A S₀ ≤ 0 := le_of_not_gt hp
      have hle : δ / 2 * loIsometryDist m n A S₀ ≤ 0 := by nlinarith [hnp, hδ]
      linarith
  have hδp : 0 < δ * loIsometryDist m n A S₀ := by positivity
  obtain ⟨q, hq⟩ := exists_rat_near (loIsometryDist m n A S₀) hδp
  rw [abs_sub_comm] at hq
  refine ⟨⟨0, 0, fun _ _ => q⟩, Nat.zero_le _, Nat.zero_le _, ?_⟩
  intro _np
  have hfun : ∀ g : Fin 0 → Bool, g = fun _ => false := fun g =>
    funext fun j => absurd j.isLt (Nat.not_lt_zero _)
  have hsum : (∑ coins : Fin 0 → Bool,
      if |((q : ℚ) : ℝ) - loIsometryDist m n A S₀|
          ≤ δ * loIsometryDist m n A S₀ then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_subset
        (s₁ := (Finset.univ : Finset (Fin 0 → Bool)))
        (s₂ := ({(fun _ => false)} : Finset (Fin 0 → Bool)))
        (fun g _ => Finset.mem_singleton.mpr (hfun g))
        (fun g _ hne => absurd (Finset.mem_univ g) hne),
      Finset.sum_singleton]
    exact ite_eq_left hq.le
  have hone : (1 : ℝ) / ((2 : ℕ) ^ 0 : ℝ) = 1 := by norm_num
  rw [hsum, hone]
  linarith

section GaussianL2

open MeasureTheory
open scoped Classical

set_option maxHeartbeats 2000000

/-- The integral of the second moment of the unnormalized real Gaussian equals one half of the
square root of pi. -/
private theorem clause17_1d_sq : (∫ x : ℝ, x ^ 2 * Real.exp (-(x ^ 2 : ℝ)))
    = Real.sqrt Real.pi / 2 := by
  have hIoi : (∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-(x ^ 2 : ℝ)))
      = Real.sqrt Real.pi / 4 := by
    have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2) (by norm_num) (by norm_num)
    have hgr : ∀ x ∈ (Set.Ioi (0 : ℝ)), x ^ 2 * Real.exp (-(x ^ 2 : ℝ))
        = (x : ℝ) ^ (2 : ℝ) * Real.exp (-((x : ℝ) ^ (2 : ℝ))) := by
      intro x _hx
      rw [Real.rpow_two]
    rw [setIntegral_congr_fun measurableSet_Ioi hgr]
    have hG : ((1 : ℝ) / 2) * Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 4 := by
      have h1 : ((2 + 1 : ℝ) / 2) = 1 / 2 + 1 := by ring
      rw [h1, Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0)]
      have h2 : Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
      rw [h2]
      ring
    exact h.trans hG
  have hIic : (∫ x in Set.Iic (0 : ℝ), x ^ 2 * Real.exp (-(x ^ 2 : ℝ)))
      = Real.sqrt Real.pi / 4 := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun x => x ^ 2 * Real.exp (-(x ^ 2 : ℝ)))
    have hL : (fun x : ℝ => (fun x => x ^ 2 * Real.exp (-(x ^ 2 : ℝ))) (-x))
        = fun x => x ^ 2 * Real.exp (-(x ^ 2 : ℝ)) := by
      funext x
      simp only [neg_sq]
    rw [hL] at h
    simp only [neg_zero] at h
    rw [hIoi] at h
    exact h
  have hfi : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2 : ℝ))) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num)
      (s := 2) (by norm_num)
    simpa [Real.rpow_two, neg_one_mul] using this
  have hcomp := integral_add_compl (s := Set.Iic (0:ℝ)) (hs := measurableSet_Iic)
    (f := fun x : ℝ => x ^ 2 * Real.exp (-(x ^ 2 : ℝ))) hfi
  rw [Set.compl_Iic, hIic, hIoi] at hcomp
  linarith

end GaussianL2

/-- Combines the unitary completion, normalization, rounding, Gaussian perturbation, sampling,
estimation, and permanent encoding statements of clause 17. -/
theorem clause17 :
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 → ∀ (_hmn : 2 * n ≤ m),
      Nonempty (LoCompletedUnitary m n (by omega : n ≤ m) A)
      ∧ (∀ W : LoCompletedUnitary m n (by omega : n ≤ m) A, ∀ S : FockOccupation m n,
          loFockDist m n (by omega : n ≤ m) W.U S = loIsometryDist m n A S)
      ∧ (∀ (W : LoCompletedUnitary m n (by omega : n ≤ m) A) (G : loInterferometer m),
          loInterferometerMatrix m G = W.U → ∀ S : FockOccupation m n,
            loPhysicalDist m n (by omega : n ≤ m) G S = loIsometryDist m n A S))
    ∧ (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
        ∑ S : FockOccupation m n, loIsometryDist m n A S = 1)
    ∧ (∀ (m n : ℕ) (ε : ℝ), 0 < ε →
        ∀ (A : Matrix (Fin m) (Fin n) ℝ),
          (∀ i j, |A i j| ≤ 1) → (A.map (algebraMap ℝ ℂ))ᴴ * A.map (algebraMap ℝ ℂ) = 1 →
          loTvDist
              (loIsometryDist m n
                (loOfRat m n (loRoundToDyadic m n
                  (m * (n + 1) + 2 * n * n + 3 * n + Nat.ceil (Real.logb 2 (1 / ε)) + 3) A)))
              (loIsometryDist m n (A.map (algebraMap ℝ ℂ)))
            ≤ ε)
    ∧ (∀ (N : ℕ) (v : Fin N → ℂ),
        (1 / 2) * ∫ x : Fin N → ℂ,
            |∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i - v i))))
              - ∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i))))|
          ∂MeasureTheory.volume
          ≤ Real.sqrt (∑ i, Complex.normSq (v i)))
    ∧ (∀ (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) (R : ℝ), 0 ≤ R →
        (∀ i j, Complex.normSq (V i j) ≤ R ^ 2) →
        (∫ G : Fin n → Fin n → ℂ,
            Complex.normSq (Matrix.permanent (V + Matrix.of G) - Matrix.permanent V)
              * loGaussianMatDensity n G
          ∂MeasureTheory.volume)
          ≤ 4 * (n ! : ℝ) ^ 2 * (1 + R ^ 2) ^ n)
    ∧ (∀ (m n b : ℕ) (Enc : LoDyadicEncoding m n b) (ε : ℝ), 0 < ε →
        (loOfRat m n Enc.mat)ᴴ * loOfRat m n Enc.mat = 1 →
        ∃ Sam : LoSampler m n,
          Sam.L ≤ m + Nat.ceil (Real.logb 2 (Fintype.card (FockOccupation m n) : ℝ))
              + Nat.ceil (Real.logb 2 (1 / ε)) + 2
          ∧ loTvDist (loSamplerDist Sam) (loIsometryDist m n (loOfRat m n Enc.mat)) ≤ ε)
    ∧ (Qatlib.Foundations.ComplexGeometry.PhaseRecovery.TriangulationStability →
      Qatlib.Foundations.ProbabilityCore.Concentration.GaussianShiftTVDBound →
      LoPaccHypothesis →
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
      ∀ (ε_s δ η : ℝ), 0 < ε_s → 0 < δ → δ < 1 → 0 < η → η < 1 →
      ∀ Sam : LoSampler m n,
        loTvDist (loSamplerDist Sam) (loIsometryDist m n A) ≤ ε_s →
        (∀ S : FockOccupation m n,
            |loSamplerDist Sam S - loIsometryDist m n A S|
              ≤ 2 * loTvDist (loSamplerDist Sam) (loIsometryDist m n A))
        ∧ (∀ B : Matrix (Fin m) (Fin n) ℚ,
            loTvDist (loSamplerDist Sam) (loIsometryDist m n (loOfRat m n B))
              ≤ loTvDist (loSamplerDist Sam) (loIsometryDist m n A)
                + loTvDist (loIsometryDist m n A) (loIsometryDist m n (loOfRat m n B)))
        ∧ (∀ S₀ : FockOccupation m n,
            ε_s ≤ δ / 2 * loIsometryDist m n A S₀ →
            ∃ est : LoFbppEstimator m n,
              est.q ≤ 64 * (m + n + 1) ^ 4 + 64 * Nat.ceil (Real.logb 2 (1 / η))
              ∧ est.qlen ≤ 64 * (m + n + 1) ^ 4
              ∧ ∀ np : List Bool → Bool,
                  (∑ coins : Fin est.q → Bool,
                      if |(est.out np coins : ℝ) - loIsometryDist m n A S₀|
                          ≤ δ * loIsometryDist m n A S₀ then (1 : ℝ) else 0)
                    / ((2 : ℕ) ^ est.q : ℝ) ≥ 1 - η))
    ∧ (∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℚ), (∀ i j, 0 ≤ X i j) →
        ∃ (D : ℕ) (Y : Matrix (Fin n) (Fin n) ℕ) (B : ℕ), 0 < D
          ∧ (∀ i j, (Y i j : ℚ) = D * X i j)
          ∧ (∀ i j, Y i j ≤ B)
          ∧ ((Finset.univ.filter
                (fun p : Equiv.Perm (Fin n) × (Fin n → Fin (B + 1)) =>
                  ∀ i, ((p.2 i : Fin (B + 1)) : ℕ) < Y i (p.1 i))).card : ℚ)
              = (D : ℚ) ^ n * Matrix.permanent X)
    ∧ (∀ (n : ℕ) (Xr Xi : Matrix (Fin n) (Fin n) ℚ),
        ∃ (D : ℕ) (Yr Yi : Matrix (Fin n) (Fin n) ℤ), 0 < D
          ∧ (∀ i j, (Yr i j : ℚ) = D * Xr i j ∧ (Yi i j : ℚ) = D * Xi i j)
          ∧ (∑ p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n),
                ∏ i, (((Yr i (p.1 i) : ℂ) + Complex.I * (Yi i (p.1 i) : ℂ))
                  * conj ((Yr i (p.2 i) : ℂ) + Complex.I * (Yi i (p.2 i) : ℂ))))
              = ((D : ℂ) ^ 2) ^ n
                * Complex.normSq (Matrix.permanent
                    (Matrix.of fun i j => (Xr i j : ℂ) + Complex.I * (Xi i j : ℂ)))) :=
  ⟨clause17_clause1, clause17_clause2, clause17_clause3, clause17_clause4a, clause17_clause4b, clause17_clause5,
    clause17_clause6, clause17_clause7a, clause17_clause7b⟩

end Qatlib.Concepts.BosonFock.PermAnalysis
