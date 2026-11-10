/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSvtCore.EvenSVTFrobeniusCoreSamp
import Qatlib.Concepts.SketchArith.TransposeAccess.CompactSketchConsumers
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchArith.TransposeAccess

open Qatlib.Concepts.SketchSpectral.EvenSvtCore
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem eigenvalue_in_ordered_spectrum {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (lam : ℝ) (v : I → ℂ)
    (hv : A *ᵥ v = (lam : ℂ) • v) (hne : v ≠ 0) :
    ∃ j, orderedHermitianValues hA j = lam := by
  let b := orderedHermitianBasis hA
  let V : Matrix I (Fin (Fintype.card I)) ℂ := basisColumns b
  let u := Vᴴ *ᵥ v
  have hu0 : u ≠ 0 := by
    intro hu
    have h := congrArg (fun w => V *ᵥ w) hu
    apply hne
    simpa only [u, Matrix.mulVec_mulVec, V, basisColumns_mul_adjoint, Matrix.one_mulVec,
      Matrix.mulVec_zero] using! h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu0
  have hVA : Vᴴ * A = Matrix.diagonal (fun j => (orderedHermitianValues hA j : ℂ)) * Vᴴ := by
    calc
      _ = Vᴴ * spectralDiagonal b (fun j => (orderedHermitianValues hA j : ℂ)) :=
        congrArg (fun M => Vᴴ * M) (orderedHermitian_diagonal hA)
      _ = _ := basis_adjoint_mul_spectralDiagonal b _
  have h := congrArg (fun w => Vᴴ *ᵥ w) hv
  (try dsimp only at h)
  rw [Matrix.mulVec_mulVec, hVA, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h
  have hc : (orderedHermitianValues hA j : ℂ) * u j = (lam : ℂ) * u j := by
    simpa only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] using! congrFun h j
  refine ⟨j, ?_⟩
  exact Complex.ofReal_injective (mul_right_cancel₀ hj hc)

theorem outer_gram_value {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (R : Matrix K C ℂ) (i : Fin (Fintype.card K)) :
    orderedHermitianValues (Matrix.isHermitian_mul_conjTranspose_self R) i = 0 ∨
    ∃ j, orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self R) j =
      orderedHermitianValues (Matrix.isHermitian_mul_conjTranspose_self R) i := by
  let hB := Matrix.isHermitian_mul_conjTranspose_self R
  let lam := orderedHermitianValues hB i
  let v := (orderedHermitianBasis hB i).ofLp
  have hv : (R * Rᴴ) *ᵥ v = (lam : ℂ) • v :=
    congrArg (fun x : EuclideanSpace ℂ K => x.ofLp) (orderedHermitianBasis_action hB i)
  by_cases hl : lam = 0
  · exact Or.inl hl
  · apply Or.inr
    have hv0 : v ≠ 0 := by
      intro h
      have he : orderedHermitianBasis hB i = 0 := by
        exact (WithLp.ofLp_eq_zero 2).mp h
      have hn := (orderedHermitianBasis hB).norm_eq_one i
      rw [he, norm_zero] at hn
      norm_num at hn
    have hRv : Rᴴ *ᵥ v ≠ 0 := by
      intro h
      have hh := hv
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero] at hh
      have : (lam : ℂ) • v ≠ 0 := smul_ne_zero (by exact_mod_cast hl) hv0
      exact this hh.symm
    apply eigenvalue_in_ordered_spectrum (Rᴴ * R) (Matrix.isHermitian_conjTranspose_mul_self R)
      lam (Rᴴ *ᵥ v) _ hRv
    calc
      _ = Rᴴ *ᵥ ((R * Rᴴ) *ᵥ v) := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by rw [hv, Matrix.mulVec_smul]

theorem sketchSquared_adjoint {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) :
    sketchSquared Aᴴ = sketchSquared A := by
  simp only [sketchSquared, sketchRowSquared, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

open scoped Matrix.Norms.Frobenius in

theorem spectralFrobenius_eq_sampling_norm {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) :
    spectralFrobenius A = ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  simp only [spectralFrobenius, ← Real.sqrt_eq_rpow, Complex.normSq_eq_norm_sq]
  simp only [Real.rpow_two]

theorem exact_sketch_energy_bound {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (q : FinDist K) (r : ℕ) (A : Matrix K C ℂ)
    (hr : 0 < r) (hA : 0 < sketchSquared A)
    (hq : ∀ i, q.prob i = sketchRowSquared A i / sketchSquared A) (v : Fin r → K) :
    sketchSquared (compactSketched (compactSketchData q r v) A) ≤ sketchSquared A := by
  have h := compact_sketch_frobenius_norm_bounds_and_tail K C q r A 1 hr
    (by norm_num) hA (by intro k; simp only [one_mul, hq]; exact le_rfl)
  simpa only [one_mul] using! h.2.1 v

theorem outer_gram_zero_right_mul {K C D : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (R : Matrix K C ℂ) (T : Matrix C D ℂ) (i : Fin (Fintype.card K))
    (hz : orderedHermitianValues (Matrix.isHermitian_mul_conjTranspose_self R) i = 0) :
    orderedHermitianValues (Matrix.isHermitian_mul_conjTranspose_self (R * T)) i = 0 := by
  have hR := (singular_gram_ordered Rᴴ).2 i
  simp only [Matrix.conjTranspose_conjTranspose] at hR
  have hs : matrixSingularValues Rᴴ i = 0 := by
    rw [hz] at hR; nlinarith [sq_nonneg (matrixSingularValues Rᴴ i)]
  have hi : Module.finrank ℂ Rᴴ.toEuclideanLin.range ≤ (i : ℕ) :=
    Rᴴ.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mp hs
  have hcomp : (R * T)ᴴ.toEuclideanLin = Tᴴ.toEuclideanLin ∘ₗ Rᴴ.toEuclideanLin := by
    rw [Matrix.conjTranspose_mul, Matrix.toLpLin_mul_same]
  have hle : Module.finrank ℂ (R * T)ᴴ.toEuclideanLin.range ≤
      Module.finrank ℂ Rᴴ.toEuclideanLin.range := by
    rw [hcomp]
    exact Module.finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right Rᴴ.toEuclideanLin Tᴴ.toEuclideanLin)
      (Module.rank_lt_aleph0 _ _)
  have hs' : matrixSingularValues (R * T)ᴴ i = 0 :=
    (R * T)ᴴ.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr (hle.trans hi)
  have hh := (singular_gram_ordered (R * T)ᴴ).2 i
  simpa only [Matrix.conjTranspose_conjTranspose, hs', zero_pow (by decide : 2 ≠ 0)] using! hh

theorem exact_gram_tail {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (q : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (δ : ℝ)
    (hr : 0 < r) (hA : 0 < sketchSquared A) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hq : ∀ i, q.prob i = sketchRowSquared A i / sketchSquared A) :
    q.probEvent (fun v : Fin r → K =>
      Real.sqrt (8 * Real.log (2 / δ) / (r : ℝ)) * sketchSquared A ≤
        spectralFrobenius ((compactSketched (compactSketchData q r v) A)ᴴ *
          compactSketched (compactSketchData q r v) A - Aᴴ * A)) ≤ δ := by
  obtain ⟨p, hp, _, _, ht, _, _⟩ := compact_sketch_actual_mixture_product_consumer
    K C C q q r A A δ hr hA hA hδ hδ1 hq hq
  have hpq : p = q := by
    have hh : p.prob = q.prob := by
      funext i
      rw [hp]
      unfold sketchMixtureProbability
      ring
    cases p
    cases q
    cases hh
    rfl
  subst p
  have hs : Real.sqrt (sketchSquared A) * Real.sqrt (sketchSquared A) = sketchSquared A :=
    Real.mul_self_sqrt hA.le
  simp only [mul_assoc, hs] at ht
  simp_rw [(compact_sketch_actual_pairs_entries_and_queries K C C q r A A _).2.2.2.2.2,
    ← spectralFrobenius_eq_sampling_norm] at ht
  exact ht

theorem hermitianFunction_shift {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) :
    hermitianFunction A hA (fun x => f x - f 0) =
      hermitianFunction A hA f - (f 0) • 1 := by
  unfold hermitianFunction
  rw [← spectralDiagonal_const (orderedHermitianBasis hA) (f 0), spectralDiagonal_sub]

theorem evenSVT_band_core {K C RS CT : Type}
    [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (T : Matrix C CT ℂ)
    (f fbar : ℝ → ℂ) (L Lbar d η₁ η₂ : ℝ)
    (hL : 0 ≤ L) (hLb : 0 ≤ Lbar) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hd : η₁ + η₂ ≤ d)
    (hLip : ∀ x y : ℝ,
      ((∃ i, |x - orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) ∨ x = 0) →
      ((∃ i, |y - orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) ∨ y = 0) →
      ‖f x - f y‖ ≤ L * |x - y|)
    (hLipb : ∀ x y : ℝ,
      ((∃ i, |x - orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) ∨ x = 0) →
      ((∃ i, |y - orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) ∨ y = 0) →
      ‖fbar x - fbar y‖ ≤ Lbar * |x - y|)
    (hcons : ∀ x : ℝ, 0 < x →
      (∃ i, |x - orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) →
      fbar x * (x : ℂ) = f x - f 0)
    (hE₁ : spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ η₁)
    (hE₂ : spectralFrobenius ((R * T) * (R * T)ᴴ - R * Rᴴ) ≤ η₂) :
    spectralFrobenius (Rᴴ * hermitianFunction ((R * T) * (R * T)ᴴ)
      (Matrix.isHermitian_mul_conjTranspose_self _) fbar * R + (f 0) • 1 -
      hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self _) f) ≤
      L * η₁ + (‖Aᴴ * A‖ + η₁) * (Lbar * η₂) := by
  let hA := Matrix.isHermitian_conjTranspose_mul_self A
  let hR := Matrix.isHermitian_conjTranspose_mul_self R
  let hRR := Matrix.isHermitian_mul_conjTranspose_self R
  let hCC := Matrix.isHermitian_mul_conjTranspose_self (R * T)
  have hinner (i : Fin (Fintype.card C)) :
      |orderedHermitianValues hR i - orderedHermitianValues hA i| ≤ η₁ :=
    ((ordered_hermitian_weyl_and_hoffman_wielandt C _ _ hR hA).1 i).trans
      ((spectral_operator_norm_le_frobenius _).trans hE₁)
  have houter (i : Fin (Fintype.card RS)) :
      |orderedHermitianValues hCC i - orderedHermitianValues hRR i| ≤ η₂ :=
    ((ordered_hermitian_weyl_and_hoffman_wielandt RS _ _ hCC hRR).1 i).trans
      ((spectral_operator_norm_le_frobenius _).trans hE₂)
  have hbR (i : Fin (Fintype.card C)) :
      ∃ j, |orderedHermitianValues hR i - orderedHermitianValues hA j| ≤ d :=
    ⟨i, (hinner i).trans (by linarith)⟩
  have hbRR (i : Fin (Fintype.card RS)) :
      (∃ j, |orderedHermitianValues hRR i - orderedHermitianValues hA j| ≤ d) ∨
        orderedHermitianValues hRR i = 0 := by
    rcases outer_gram_value R i with hz | ⟨j, hj⟩
    · exact Or.inr hz
    · exact Or.inl (by rw [← hj]; exact hbR j)
  have hbCC (i : Fin (Fintype.card RS)) :
      (∃ j, |orderedHermitianValues hCC i - orderedHermitianValues hA j| ≤ d) ∨
        orderedHermitianValues hCC i = 0 := by
    rcases outer_gram_value R i with hz | ⟨j, hj⟩
    · exact Or.inr (outer_gram_zero_right_mul R T i hz)
    · apply Or.inl
      refine ⟨j, ?_⟩
      calc
        _ ≤ |orderedHermitianValues hCC i - orderedHermitianValues hRR i| +
          |orderedHermitianValues hRR i - orderedHermitianValues hA j| := abs_sub_le _ _ _
        _ ≤ η₂ + η₁ := add_le_add (houter i) (by rw [← hj]; exact hinner j)
        _ ≤ d := by linarith
  have hW : ‖Rᴴ * R‖ ≤ ‖Aᴴ * A‖ + η₁ := by
    calc
      _ = ‖(Rᴴ * R - Aᴴ * A) + Aᴴ * A‖ := by rw [sub_add_cancel]
      _ ≤ ‖Rᴴ * R - Aᴴ * A‖ + ‖Aᴴ * A‖ := norm_add_le _ _
      _ ≤ _ := by linarith [(spectral_operator_norm_le_frobenius _).trans hE₁]
  have hc (i : Fin (Fintype.card C)) :
      fbar (orderedHermitianValues hR i) * (orderedHermitianValues hR i : ℂ) =
        f (orderedHermitianValues hR i) - f 0 := by
    have hn : 0 ≤ orderedHermitianValues hR i := by
      rw [(singular_gram_ordered R).2 i]
      exact sq_nonneg _
    by_cases hz : orderedHermitianValues hR i = 0
    · simp only [hz, Complex.ofReal_zero, mul_zero, sub_self]
    · exact hcons _ (lt_of_le_of_ne hn (Ne.symm hz)) (hbR i)
  have h := evenSVTFrobeniusCore_proof K C RS CT A R (R * T) f fbar L Lbar η₁ η₂
    (‖Aᴴ * A‖ + η₁) hL hLb hη₁ hη₂ hc
    (fun i j => hLip _ _ (Or.inl (hbR i)) (Or.inl ⟨j, by simp; linarith⟩))
    (fun i j => hLipb _ _ (hbCC i) (hbRR j)) hE₁ hE₂ hW
  rw [hermitianFunction_shift] at h
  convert! h using 1; abel

theorem probEvent_single {X : Type} [Fintype X] [DecidableEq X] (q : FinDist X) (P : X → Prop) :
    q.probEvent (fun ω : Fin 1 → X => P (ω 0)) = ∑ x, if P x then q.prob x else 0 := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  simp only [Finset.sum_filter, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf,
      Fin.prod_univ_one]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) X)
  intro ω
  rfl

noncomputable def twoSketchRecordLaw {K C : Type} [Fintype K] [Fintype C]
    (q : FinDist K) (r c : ℕ) (condQ : (Fin r → K) → FinDist C) :
    FinDist ((Fin r → K) × (Fin c → C)) where
  prob z := q.probOf z.1 * (condQ z.1).probOf z.2
  nonneg z := mul_nonneg (Finset.prod_nonneg fun _ _ => q.nonneg _)
    (Finset.prod_nonneg fun _ _ => (condQ z.1).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf, mul_one]

theorem twoSketch_union_bound {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (q : FinDist K) (r c : ℕ)
    (condQ : (Fin r → K) → FinDist C)
    (E₁ : (Fin r → K) → Prop) (E₂ : (Fin r → K) → (Fin c → C) → Prop)
    (Bad : ((Fin r → K) × (Fin c → C)) → Prop) (δ₁ δ₂ : ℝ)
    (hsub : ∀ v w, Bad (v, w) → E₁ v ∨ E₂ v w)
    (h₁ : q.probEvent E₁ ≤ δ₁) (h₂ : ∀ v, (condQ v).probEvent (E₂ v) ≤ δ₂) :
    (twoSketchRecordLaw q r c condQ).probEvent
      (fun ω : Fin 1 → ((Fin r → K) × (Fin c → C)) => Bad (ω 0)) ≤ δ₁ + δ₂ := by
  rw [probEvent_single, Fintype.sum_prod_type]
  have hn (v : Fin r → K) : 0 ≤ q.probOf v := Finset.prod_nonneg fun _ _ => q.nonneg _
  have hpoint (v : Fin r → K) (w : Fin c → C) :
      (if Bad (v, w) then q.probOf v * (condQ v).probOf w else 0) ≤
        (if E₁ v then q.probOf v * (condQ v).probOf w else 0) +
        q.probOf v * (if E₂ v w then (condQ v).probOf w else 0) := by
    have hw : 0 ≤ (condQ v).probOf w := Finset.prod_nonneg fun _ _ => (condQ v).nonneg _
    by_cases hb : Bad (v, w)
    · rcases hsub v w hb with hrow | hcol
      · simp only [hb, hrow, if_true]
        exact le_add_of_nonneg_right (mul_nonneg (hn v) (by split_ifs <;> positivity))
      · simp only [hb, hcol, if_true]
        exact le_add_of_nonneg_left (by split_ifs; exact mul_nonneg (hn v) hw; exact le_rfl)
    · simp only [hb, if_false]
      apply add_nonneg
      · split_ifs; exact mul_nonneg (hn v) hw; exact le_rfl
      · apply mul_nonneg (hn v)
        split_ifs; exact hw; exact le_rfl
  calc
    _ ≤ ∑ v, ∑ w, ((if E₁ v then q.probOf v * (condQ v).probOf w else 0) +
        q.probOf v * (if E₂ v w then (condQ v).probOf w else 0)) :=
      Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hpoint v w
    _ = q.probEvent E₁ + ∑ v, q.probOf v * (condQ v).probEvent (E₂ v) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      · unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp only [← Finset.mul_sum, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sum_probOf, mul_one, Finset.sum_const_zero]
      · unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
        simp only [Finset.sum_filter]
    _ ≤ δ₁ + ∑ v, q.probOf v * δ₂ := add_le_add h₁
      (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h₂ v) (hn v))
    _ = δ₁ + δ₂ := by rw [← Finset.sum_mul, q.sum_probOf r, one_mul]

theorem sketchSquared_zero_matrix {K C : Type} [Fintype K] [Fintype C] [DecidableEq C]
    (A : Matrix K C ℂ) (hA : sketchSquared A = 0) : A = 0 := by
  have hrow (k : K) : sketchRowSquared A k = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sketchRowSquared_nonneg A k)).mp hA k (Finset.mem_univ k)
  ext k j
  exact sketchRowSquared_eq_zero_entry A k (hrow k) j

end Qatlib.Concepts.SketchSpectral.EvenSvtLaw
