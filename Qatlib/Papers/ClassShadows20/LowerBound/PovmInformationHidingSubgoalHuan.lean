/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClassShadows20.LowerBound.PovmInformationHidingSubgoalStat
import Qatlib.Papers.ClassShadows20.LowerBound.FiniteMutualInformation
import QuantumInfo.ForMathlib.HermitianMat.Inner
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Papers.ClassShadows20.LowerBound
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ClassShadows20.LowerBound.PovmInformationHidingSubgoalHuan

open Matrix
open scoped ComplexOrder
open scoped Classical BigOperators

private theorem trace_mul_re_nonneg {D : ℕ} (A B : Operator D)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  have hA' : (0 : HermitianMat (Fin D) ℂ) ≤ ⟨A, hA.1⟩ := HermitianMat.zero_le_iff.mpr hA
  have hB' : (0 : HermitianMat (Fin D) ℂ) ≤ ⟨B, hB.1⟩ := HermitianMat.zero_le_iff.mpr hB
  have h := HermitianMat.inner_ge_zero hA' hB'
  rw [HermitianMat.inner_eq_re_trace] at h
  exact h

private theorem trace_sq_le_trace_sq {D : ℕ} (A : Operator D) (hA : A.PosSemidef) :
    (Matrix.trace (A * A)).re ≤ (Matrix.trace A).re ^ 2 := by
  have hA' : (0 : HermitianMat (Fin D) ℂ) ≤ ⟨A, hA.1⟩ := HermitianMat.zero_le_iff.mpr hA
  have h := HermitianMat.inner_le_mul_trace hA' hA'
  rw [HermitianMat.inner_eq_re_trace] at h
  exact h.trans_eq (pow_two _).symm

private noncomputable def gatedConjugate {d : ℕ} {I : Type} [Fintype I]
    (μ : FinDist I) (Uf : I → Operator d)
    (ρ : Operator d) (i : I) : Operator d :=
  if 0 < μ.prob i then Uf i * ρ * (Uf i)ᴴ else ρ

theorem povmInformationHidingSubgoal : PovmInformationHidingSubgoal := by
  intro d r M O _ _ I _ _ F hFpsd hFsum P hP hd hr hrd hM α hα0 hα1 μ Uf hμU s hs h1 h2
  classical

  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : (0:ℕ) < d)
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hdrd : ((r : ℝ) ≤ (d : ℝ)) := by exact_mod_cast hrd
  have h2d : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd1pos : (0 : ℝ) < (d : ℝ) ^ 2 - 1 := by nlinarith
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'

  have hPpsd : ∀ x, (P x).PosSemidef := by
    intro x
    have hH := (hP x).1
    have hPP := (hP x).2.1
    have hEq : P x = (P x).conjTranspose * P x := by rw [hH, hPP]
    rw [hEq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hρpsd : ∀ x, (lemma8CodeState d r α (P x)).PosSemidef := by
    intro x
    rw [lemma8CodeState]
    exact Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul Matrix.PosSemidef.one
        (div_nonneg (by linarith) (by positivity)))
      (Matrix.PosSemidef.smul (hPpsd x) (by positivity))
  have htraceρ : ∀ x, Matrix.trace (lemma8CodeState d r α (P x)) = 1 := by
    intro x
    have hc : ∀ (c : ℝ) (n : ℕ), 0 < n → (c / (n : ℝ)) • ((n : ℂ)) = ((c : ℝ) : ℂ) := by
      intro c n hn
      have hn' : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn.ne'
      have hkey : Complex.ofReal (c / (n : ℝ)) * Complex.ofReal ((n : ℝ)) = Complex.ofReal c := by
        rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hn']
      rw [Algebra.smul_def]
      exact hkey
    rw [lemma8CodeState, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      (hP x).2.2, Matrix.trace_one, Fintype.card_fin, hc (1 - α) d (by omega), hc α r hr]
    push_cast
    ring

  have hu_mem : ∀ i, 0 < μ.prob i → (Uf i * (Uf i)ᴴ = 1 ∧ (Uf i)ᴴ * Uf i = 1) := by
    intro i hi
    have hu := hμU i hi
    have ha := Matrix.mem_unitaryGroup_iff.mp hu
    rw [Matrix.star_eq_conjTranspose] at ha
    have hb := Matrix.mem_unitaryGroup_iff'.mp hu
    rw [Matrix.star_eq_conjTranspose] at hb
    exact ⟨ha, hb⟩
  have hunit : ∀ i, 0 < μ.prob i → IsUnit (Uf i) := by
    intro i hi
    obtain ⟨ha, _hb⟩ := hu_mem i hi
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ((isUnit_iff_ne_zero).mpr ?_)
    intro hzero
    have hdet : Matrix.det (Uf i) * Matrix.det ((Uf i)ᴴ) = 1 := by
      rw [← Matrix.det_mul, ha, Matrix.det_one]
    rw [hzero, zero_mul] at hdet
    exact zero_ne_one hdet
  have hconjpsd : ∀ x i, 0 < μ.prob i →
      (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ).PosSemidef := by
    intro x i hi
    have hu := ((hunit i hi).posSemidef_star_right_conjugate_iff).mpr (hρpsd x)
    rwa [Matrix.star_eq_conjTranspose] at hu
  have hconjtr : ∀ x i, 0 < μ.prob i →
      Matrix.trace (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ) = 1 := by
    intro x i hi
    obtain ⟨_, hb⟩ := hu_mem i hi
    rw [Matrix.trace_mul_cycle, hb, Matrix.one_mul]
    exact htraceρ x

  set qstate : Fin M → I → Operator d :=
    fun x i => gatedConjugate μ Uf (lemma8CodeState d r α (P x)) i with hqstate
  have hqpos : ∀ x i, 0 < μ.prob i →
      qstate x i = Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ := by
    intro x i h
    rw [hqstate]
    exact dif_pos h
  have hqneg : ∀ x i, ¬ 0 < μ.prob i →
      qstate x i = lemma8CodeState d r α (P x) := by
    intro x i h
    rw [hqstate]
    exact dif_neg h
  have hqpsd : ∀ x i, (qstate x i).PosSemidef := by
    intro x i
    by_cases hi : 0 < μ.prob i
    · rw [hqpos x i hi]; exact hconjpsd x i hi
    · rw [hqneg x i hi]; exact hρpsd x
  have hqtr : ∀ x i, Matrix.trace (qstate x i) = 1 := by
    intro x i
    by_cases hi : 0 < μ.prob i
    · rw [hqpos x i hi]; exact hconjtr x i hi
    · rw [hqneg x i hi]; exact htraceρ x

  have hsumborn : ∀ x i, (∑ o, (Matrix.trace (F o * qstate x i)).re) = 1 := by
    intro x i
    calc (∑ o, (Matrix.trace (F o * qstate x i)).re)
        = (∑ o, Matrix.trace (F o * qstate x i)).re := (Complex.re_sum ..).symm
      _ = (Matrix.trace (∑ o, F o * qstate x i)).re := by rw [Matrix.trace_sum]
      _ = (Matrix.trace ((∑ o, F o) * qstate x i)).re := by rw [Finset.sum_mul]
      _ = (Matrix.trace (1 * qstate x i)).re := by rw [hFsum]
      _ = (Matrix.trace (qstate x i)).re := by rw [Matrix.one_mul]
      _ = 1 := by rw [hqtr x i]; simp

  set ν : FinDist (Fin M × I) := {
    prob := fun c => (1 / (M : ℝ)) * μ.prob c.2
    nonneg := fun c => mul_nonneg (div_nonneg (by norm_num) (by exact_mod_cast hM.le))
      (μ.nonneg c.2)
    sum_one := by
      rw [Fintype.sum_prod_type]
      have hmul : ∀ x : Fin M,
          (∑ i, (1 / (M : ℝ)) * μ.prob i) = (1 / (M : ℝ)) * ∑ i, μ.prob i := by
        intro x
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun x _ => hmul x), μ.sum_one, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
  } with hν
  set q : (Fin M × I) → FinDist O :=
    fun c =>
      { prob := fun o => (Matrix.trace (F o * qstate c.1 c.2)).re
        nonneg := fun o =>
          trace_mul_re_nonneg (F o) (qstate c.1 c.2) (hFpsd o) (hqpsd c.1 c.2)
        sum_one := hsumborn c.1 c.2 } with hq
  have hνprob : ∀ c : Fin M × I, ν.prob c = (1 / (M : ℝ)) * μ.prob c.2 := by
    intro c
    rw [hν]
  have hqprob : ∀ (c : Fin M × I) (o : O), (q c).prob o
      = (Matrix.trace (F o * qstate c.1 c.2)).re := by
    intro c o
    rw [hq]

  have hbrid : ∀ (g : Operator d → ℝ) (x : Fin M),
      (∑ i, μ.prob i * g (qstate x i))
        = ∑ i, μ.prob i * g (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ) := by
    intro g x
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 0 < μ.prob i
    · rw [hqpos x i hi]
    · have hi0 : μ.prob i = 0 := le_antisymm (not_lt.mp hi) (μ.nonneg i)
      rw [hi0, zero_mul, zero_mul]
  have hpull : ∀ (f : Fin M × I → ℝ),
      (∑ c, ν.prob c * f c)
        = (1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i * f (x, i) := by
    intro f
    have h0 : ∀ c : Fin M × I, ν.prob c * f c = (1 / (M : ℝ)) * (μ.prob c.2 * f c) := by
      intro c
      rw [hνprob]
      ring
    rw [Finset.sum_congr rfl (fun c _ => h0 c), ← Finset.mul_sum, Fintype.sum_prod_type]
  have hfact : ∀ (g : Operator d → ℝ),
      ((1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i * g (qstate x i))
        = (1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i *
            g (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ) := by
    intro g
    exact congrArg (fun S => (1 / (M : ℝ)) * S)
      (Finset.sum_congr rfl (fun x _ => hbrid g x))

  have hlin : ∀ (o : O) (x : Fin M),
      (∑ i, μ.prob i *
          (Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re)
        = (Matrix.trace (F o)).re / (d : ℝ) := by
    intro o x
    have hid : Matrix.trace (F o * ((1 / (d : ℝ)) • 1 : Operator d))
        = ∑ i, ((μ.prob i : ℝ) : ℂ) *
          Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ)) := by
      conv_lhs => rw [← h1 x]
      rw [Finset.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.trace_smul, Algebra.smul_def,
        RCLike.algebraMap_eq_ofReal]
      rfl
    have hre := congrArg Complex.re hid
    rw [Complex.re_sum] at hre
    have hterm : ∀ i, (((μ.prob i : ℝ) : ℂ) *
          Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re
        = μ.prob i *
          (Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re := by
      intro i
      simp [Complex.mul_re]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)] at hre
    have hL : (Matrix.trace (F o * ((1 / (d : ℝ)) • 1 : Operator d))).re
        = (Matrix.trace (F o)).re / (d : ℝ) := by
      have hM : F o * ((1 / (d : ℝ)) • 1 : Operator d) = (1 / (d : ℝ)) • F o := by
        rw [Matrix.mul_smul, Matrix.mul_one]
      have hkey : (Complex.ofReal (1 / (d : ℝ)) * Matrix.trace (F o)).re
          = (Matrix.trace (F o)).re / (d : ℝ) := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        field_simp
      rw [hM, Matrix.trace_smul, Algebra.smul_def]
      exact hkey
    rw [hL] at hre
    exact hre.symm
  have hm : ∀ o, (finDistMixture ν q).prob o = (Matrix.trace (F o)).re / (d : ℝ) := by
    intro o
    have hf : ∀ c : Fin M × I, ν.prob c * (q c).prob o
        = ν.prob c * (Matrix.trace (F o * qstate c.1 c.2)).re := by
      intro c
      rw [hqprob]
    rw [Qatlib.Papers.ClassShadows20.LowerBound.finDistMixture_prob, Finset.sum_congr rfl (fun c _ => hf c),
      hpull (fun c => (Matrix.trace (F o * qstate c.1 c.2)).re),
      hfact (fun σ => (Matrix.trace (F o * σ)).re),
      Finset.sum_congr rfl (fun x _ => hlin o x), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp

  have hE2 : ∀ o, (∑ c, ν.prob c * (q c).prob o ^ 2)
      = ((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) * ((Matrix.trace (F o)).re) ^ 2
        + ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
          (Matrix.trace (F o * F o)).re := by
    intro o
    have hf : ∀ c : Fin M × I, ν.prob c * (q c).prob o ^ 2
        = ν.prob c * ((Matrix.trace (F o * qstate c.1 c.2)).re ^ 2) := by
      intro c
      rw [hqprob]
    have hsam : ∀ x : Fin M,
        (∑ i, μ.prob i *
            ((Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re ^ 2))
        = ((d : ℝ) - s) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o)).re * (Matrix.trace (F o)).re
          + ((d : ℝ) * s - 1) / ((d : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            (Matrix.trace (F o * F o)).re :=
      fun x => (Finset.sum_congr rfl
        (fun i _ => by rw [pow_two]; ring)).trans (h2 x (F o) (F o) (hFpsd o).1 (hFpsd o).1)
    rw [Finset.sum_congr rfl (fun c _ => hf c),
      hpull (fun c => (Matrix.trace (F o * qstate c.1 c.2)).re ^ 2),
      hfact (fun σ => (Matrix.trace (F o * σ)).re ^ 2),
      Finset.sum_congr rfl (fun x _ => hsam x), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp

  have hκ : ∀ o,
      ((∑ c, ν.prob c * (q c).prob o ^ 2) - (finDistMixture ν q).prob o ^ 2)
        = (α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1)) / (d : ℝ))
          * ((Matrix.trace (F o * F o)).re
              - (Matrix.trace (F o)).re * (Matrix.trace (F o)).re / (d : ℝ)) := by
    intro o
    rw [hE2 o, hm o, hs]
    field_simp
    ring

  have hule : ∀ o, (Matrix.trace (F o * F o)).re
      ≤ (Matrix.trace (F o)).re * (Matrix.trace (F o)).re := by
    intro o
    have h := trace_sq_le_trace_sq (F o) (hFpsd o)
    rwa [sq] at h
  have htnn : ∀ o, 0 ≤ (Matrix.trace (F o)).re := fun o =>
    (RCLike.nonneg_iff.mp (hFpsd o).trace_nonneg).1
  have hterm : ∀ o, 0 < (Matrix.trace (F o)).re →
      ((∑ c, ν.prob c * (q c).prob o ^ 2) - (finDistMixture ν q).prob o ^ 2) /
        (finDistMixture ν q).prob o
      ≤ α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1))
        * ((Matrix.trace (F o)).re - (Matrix.trace (F o)).re / (d : ℝ)) := by
    intro o ht
    rw [hκ o, hm o, div_le_iff₀ (div_pos ht hdpos)]
    have hRWeq : α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1))
        * ((Matrix.trace (F o)).re - (Matrix.trace (F o)).re / (d : ℝ))
        * ((Matrix.trace (F o)).re / (d : ℝ))
      = (α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1)) / (d : ℝ))
        * ((Matrix.trace (F o)).re * (Matrix.trace (F o)).re
            - (Matrix.trace (F o)).re * (Matrix.trace (F o)).re / (d : ℝ)) := by
      field_simp
    rw [hRWeq]
    have hnn : 0 ≤ α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1)) :=
      div_nonneg (mul_nonneg (sq_nonneg α) (by linarith))
        (mul_pos hrpos hd1pos).le
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hnn hdpos.le)
    linarith [hule o]

  have hfilteq : (Finset.univ.filter fun o => 0 < (finDistMixture ν q).prob o)
      = Finset.univ.filter (fun o => 0 < (Matrix.trace (F o)).re) := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hm o]
    exact ⟨fun h => (div_pos_iff_of_pos_right hdpos).mp h, fun h => div_pos h hdpos⟩
  have htsum : (∑ o, (Matrix.trace (F o)).re) = (d : ℝ) := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, hFsum, Matrix.trace_one]
    simp
  have hsumfilter : (∑ o ∈ Finset.univ.filter (fun o => 0 < (Matrix.trace (F o)).re),
        (Matrix.trace (F o)).re) = (d : ℝ) := by
    rw [Finset.sum_filter]
    have hterm' : ∀ o ∈ (Finset.univ : Finset O),
        (if 0 < (Matrix.trace (F o)).re then (Matrix.trace (F o)).re else 0)
          = (Matrix.trace (F o)).re := by
      intro o _
      by_cases h : 0 < (Matrix.trace (F o)).re
      · rw [if_pos h]
      · rw [if_neg h]
        exact le_antisymm (htnn o) (not_lt.mp h)
    rw [Finset.sum_congr rfl (fun o ho => hterm' o ho), htsum]
  have hfinal : (∑ o ∈ Finset.univ.filter (fun o => 0 < (finDistMixture ν q).prob o),
        ((∑ c, ν.prob c * (q c).prob o ^ 2) - (finDistMixture ν q).prob o ^ 2) /
          (finDistMixture ν q).prob o)
      ≤ α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1)) := by
    rw [hfilteq]
    calc (∑ o ∈ Finset.univ.filter (fun o => 0 < (Matrix.trace (F o)).re),
            ((∑ c, ν.prob c * (q c).prob o ^ 2) - (finDistMixture ν q).prob o ^ 2) /
              (finDistMixture ν q).prob o)
        ≤ ∑ o ∈ Finset.univ.filter (fun o => 0 < (Matrix.trace (F o)).re),
              α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1))
                * ((Matrix.trace (F o)).re - (Matrix.trace (F o)).re / (d : ℝ)) :=
          Finset.sum_le_sum fun o ho => hterm o ((Finset.mem_filter.mp ho).2)
      _ = α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            ((∑ o ∈ Finset.univ.filter (fun o => 0 < (Matrix.trace (F o)).re),
                (Matrix.trace (F o)).re)
              - (∑ o ∈ Finset.univ.filter (fun o => 0 < (Matrix.trace (F o)).re),
                  (Matrix.trace (F o)).re) / (d : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_div]
      _ = α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) ^ 2 - 1)) *
            ((d : ℝ) - (d : ℝ) / (d : ℝ)) := by rw [hsumfilter]
      _ = α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1)) := by
          have hdne1 : ((d : ℝ) - 1) ≠ 0 := by linarith
          have hdp1 : ((d : ℝ) + 1) ≠ 0 := by linarith
          have hdmd : ((d : ℝ) - (d : ℝ) / (d : ℝ)) = ((d : ℝ) - 1) := by field_simp
          have hfac : ((d : ℝ) ^ 2 - 1) = ((d : ℝ) - 1) * ((d : ℝ) + 1) := by ring
          rw [hdmd, hfac]
          field_simp

  have hmixeq : ∀ o, (1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i *
      (Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re
      = (finDistMixture ν q).prob o := by
    intro o
    rw [hm o, Finset.sum_congr rfl (fun x _ => hlin o x), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hent1 : (∑ o, Real.negMulLog ((1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i *
        (Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re))
      = finDistEntropy (finDistMixture ν q) := by
    simp only [Qatlib.Papers.ClassShadows20.LowerBound.finDistEntropy]
    exact Finset.sum_congr rfl fun o _ => by rw [hmixeq o]
  have hent2 : (1 / (M : ℝ)) * ∑ x, ∑ i, μ.prob i * ∑ o, Real.negMulLog
      ((Matrix.trace (F o * (Uf i * lemma8CodeState d r α (P x) * (Uf i)ᴴ))).re)
      = ∑ c, ν.prob c * finDistEntropy (q c) := by
    have hR : ∑ c, ν.prob c * finDistEntropy (q c)
        = ∑ c, ν.prob c * ∑ o, Real.negMulLog
            ((Matrix.trace (F o * qstate c.1 c.2)).re) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Qatlib.Papers.ClassShadows20.LowerBound.finDistEntropy, hqprob]
    rw [hR, hpull (fun c => ∑ o, Real.negMulLog
      ((Matrix.trace (F o * qstate c.1 c.2)).re))]
    refine congrArg (fun S => (1 / (M : ℝ)) * S) ?_
    exact Finset.sum_congr rfl fun x _ =>
      (hbrid (fun σ => ∑ o, Real.negMulLog ((Matrix.trace (F o * σ)).re)) x).symm
  rw [hent1, hent2]
  exact (Qatlib.Papers.ClassShadows20.LowerBound.finDistCondMutualInfo_le_variance_ratio ν q).trans hfinal

end Qatlib.Papers.ClassShadows20.LowerBound.PovmInformationHidingSubgoalHuan
