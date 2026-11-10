/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeLayeredMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.NativeNumerics.LayeredMean
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem native_record_event_lower {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (δ : ℝ) (hd : (∑ x,|p.prob x-q.prob x|)≤δ) (E : Finset X) :
    (∑ x∈E,p.prob x)≥(∑ x∈E,q.prob x)-δ := by
  have hh : |(∑ x∈E,p.prob x)-(∑ x∈E,q.prob x)|≤δ := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun x _ _ => abs_nonneg _)).trans hd)
  have hl := (abs_le.mp hh).1
  linarith

theorem native_layered_actual_mean_guarantee
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (k : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hf : ∀ i,0≤f i)
    (hP : ∀ l : Fin (k+2),nativeLayerPrepare A f k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (law : FinDist (LayerRecord k))
    (hlaw : ∀ ω,law.prob ω=∏ l : Fin (k+2),
      (aeLaw (layerGrid k) (nativeLayerPrepare A f k l) (j,false) (nativeLayerEvent I)
        (hP l) (layerGrid_ge_two k)).probOf (ω l))
    (hE : (∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)^2)≤1) :
    (∑ ω∈Finset.univ.filter (fun ω : LayerRecord k =>
      |layerEstimate k ω-∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)|≤(1/2:ℝ)^k),law.prob ω)≥1-2*(1/2:ℝ)^k := by
  cases k with
  | zero =>
    have hp : 0≤∑ ω∈Finset.univ.filter (fun ω : LayerRecord 0 =>
        |layerEstimate 0 ω-∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)|≤(1/2:ℝ)^0),law.prob ω :=
      Finset.sum_nonneg (fun ω _ => law.nonneg ω)
    norm_num at hp ⊢
    linarith
  | succ k =>
    let hfR := fun i => (show (0:ℝ)≤(f i:ℝ) by exact_mod_cast hf i)
    have hg :=
        layered_quantum_mean_actual_guarantee (k+1) (by omega) A j (fun i => (f i:ℝ)) hA hfR hE
    rw [neg_pow_half_eq] at hg
    (try dsimp only at hg)
    simp only [ApplyGate] at hg
    have ht := native_record_event_lower law (layerLaw (k+1) A j (fun i => (f i:ℝ)) hA hfR)
      ((1/2:ℝ)^(k+1)) (native_layered_same_record_variation_budget I A j f (k+1) hA hf hP law hlaw)
      (Finset.univ.filter (fun ω : LayerRecord (k+1) =>
        |layerEstimate (k+1) ω-∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)|≤(1/2:ℝ)^(k+1)))
    linarith

noncomputable def nativeSignedLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (σ : ℚ) (k : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ)
    (hP : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
      (fun i => max 0 ((f i-f x)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (hN : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
      (fun i => max 0 ((f x-f i)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ) :
    FinDist (I×(LayerRecord k×LayerRecord k)) where
  prob ω := BornProb (A*ᵥKet j) ω.1*
    (nativeLayerLaw A j (fun i => max 0 ((f i-f ω.1)/(4*σ))) k (hP ω.1)).prob ω.2.1*
    (nativeLayerLaw A j (fun i => max 0 ((f ω.1-f i)/(4*σ))) k (hN ω.1)).prob ω.2.2
  nonneg ω := mul_nonneg (mul_nonneg (bornProb_nonneg _ _)
    ((nativeLayerLaw A j _ k (hP ω.1)).nonneg _)) ((nativeLayerLaw A j _ k (hN ω.1)).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    calc
      _ = ∑ x,BornProb (A*ᵥKet j) x := by
        apply Finset.sum_congr rfl
        intro x _
        let P := nativeLayerLaw A j (fun i => max 0 ((f i-f x)/(4*σ))) k (hP x)
        let N := nativeLayerLaw A j (fun i => max 0 ((f x-f i)/(4*σ))) k (hN x)
        change (∑ u,∑ v,BornProb (A*ᵥKet j) x*P.prob u*N.prob v)=_
        simp only [← Finset.mul_sum, N.sum_one, mul_one, P.sum_one]
      _ = 1 := normalized_applyGate hA (normalized_ket j)

theorem native_pair_record_l1 {X : Type} [Fintype X] [DecidableEq X]
    (p q r s : FinDist X) :
    (∑ u,∑ v,|p.prob u*r.prob v-q.prob u*s.prob v|)≤
      (∑ u,|p.prob u-q.prob u|)+(∑ v,|r.prob v-s.prob v|) := by
  calc
    _ ≤ ∑ u,∑ v,(|p.prob u-q.prob u| * r.prob v+q.prob u*|r.prob v-s.prob v|) := by
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro v _
      have hh := abs_sub_le (p.prob u*r.prob v) (q.prob u*r.prob v) (q.prob u*s.prob v)
      simpa only [← sub_mul, ← mul_sub, abs_mul, abs_of_nonneg (q.nonneg u),
          abs_of_nonneg (r.nonneg v)] using! hh
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, r.sum_one, mul_one, ← Finset.sum_mul,
          q.sum_one, one_mul]

theorem native_center_positive_cast {I : Type} (f : I→ℚ) (σ : ℚ) (x : I) :
    (fun i => ((max 0 ((f i-f x)/(4*σ)):ℚ):ℝ))=centerPositive (fun i => (f i:ℝ)) (σ:ℝ) x := by
  funext i
  simp [centerPositive, max_comm]

theorem native_center_negative_cast {I : Type} (f : I→ℚ) (σ : ℚ) (x : I) :
    (fun i => ((max 0 ((f x-f i)/(4*σ)):ℚ):ℝ))=centerNegative (fun i => (f i:ℝ)) (σ:ℝ) x := by
  funext i
  simp [centerNegative, max_comm]

theorem native_signed_record_l1
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (σ : ℚ) (k : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ)
    (hP : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
      (fun i => max 0 ((f i-f x)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (hN : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
      (fun i => max 0 ((f x-f i)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ) :
    (∑ ω : I×(LayerRecord k×LayerRecord k),
      |(nativeSignedLaw A j f σ k hA hP hN).prob ω-
        (signedMeanLaw k A j (fun i => (f i:ℝ)) (σ:ℝ) hA).prob ω|)≤2*(1/2:ℝ)^k := by
  have hplus (x : I) := native_layered_same_record_variation_budget I A j
    (fun i => max 0 ((f i-f x)/(4*σ))) k hA (fun _ => le_max_left _ _) (hP x)
    (nativeLayerLaw A j _ k (hP x)) (fun _ => rfl)
  have hminus (x : I) := native_layered_same_record_variation_budget I A j
    (fun i => max 0 ((f x-f i)/(4*σ))) k hA (fun _ => le_max_left _ _) (hN x)
    (nativeLayerLaw A j _ k (hN x)) (fun _ => rfl)
  simp_rw [native_center_positive_cast] at hplus
  simp_rw [native_center_negative_cast] at hminus
  simp only [Fintype.sum_prod_type, nativeSignedLaw, signedMeanLaw, signedMeanSource]
  have hnorm : ∑ x,BornProb (A*ᵥKet j) x=1 := normalized_applyGate hA (normalized_ket j)
  calc
    _ = ∑ x,BornProb (A*ᵥKet j) x*
        (∑ u,∑ v,|(nativeLayerLaw A j (fun i => max 0 ((f i-f x)/(4*σ))) k (hP x)).prob u*
          (nativeLayerLaw A j (fun i => max 0 ((f x-f i)/(4*σ))) k (hN x)).prob v-
          (layerLaw k A j (centerPositive (fun i => (f i:ℝ)) (σ:ℝ) x) hA (fun _ => le_max_right _ _)).prob u*
          (layerLaw k A j (centerNegative (fun i => (f i:ℝ)) (σ:ℝ) x) hA (fun _ => le_max_right _ _)).prob v|) := by
      simp only [mul_assoc, ← mul_sub, abs_mul, abs_of_nonneg (bornProb_nonneg _ _),
          ← Finset.mul_sum, ApplyGate]
    _ ≤ ∑ x,BornProb (A*ᵥKet j) x*(2*(1/2:ℝ)^k) := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (bornProb_nonneg _ _)
      exact (native_pair_record_l1 _ _ _ _).trans (by linarith [hplus x,hminus x])
    _ = _ := by rw [← Finset.sum_mul,hnorm,one_mul]

theorem native_signed_centered_same_program_consumer
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (j : I) (f : I→ℚ) (σ : ℚ) (k : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ)
    (hk : 4≤k) (hσ : 0<σ) :
    let μ := ∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)
    (∑ i,BornProb (A*ᵥKet j) i*((f i:ℝ)-μ)^2)≤(σ:ℝ)^2 →
    ∃ (hP : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
        (fun i => max 0 ((f i-f x)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ)
      (hN : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
        (fun i => max 0 ((f x-f i)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ)
      (law : FinDist (I×(LayerRecord k×LayerRecord k))),
      (∀ ω,law.prob ω=BornProb (A*ᵥKet j) ω.1*
        (∏ l : Fin (k+2),(aeLaw (layerGrid k) (nativeLayerPrepare A
          (fun i => max 0 ((f i-f ω.1)/(4*σ))) k l) (j,false) (nativeLayerEvent I)
          (hP ω.1 l) (layerGrid_ge_two k)).probOf (ω.2.1 l))*
        (∏ l : Fin (k+2),(aeLaw (layerGrid k) (nativeLayerPrepare A
          (fun i => max 0 ((f ω.1-f i)/(4*σ))) k l) (j,false) (nativeLayerEvent I)
          (hN ω.1 l) (layerGrid_ge_two k)).probOf (ω.2.2 l))) ∧
      (∑ ω∈Finset.univ.filter (fun ω : I×(LayerRecord k×LayerRecord k) =>
        |(f ω.1:ℝ)+4*(σ:ℝ)*(layerEstimate k ω.2.1-layerEstimate k ω.2.2)-μ|≤8*(σ:ℝ)*(1/2:ℝ)^k),
        law.prob ω)≥13/24 := by
  intro μ hvar
  let hP := fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
    (fun i => max 0 ((f i-f x)/(4*σ))) k l hA (fun _ => le_max_left _ _)
  let hN := fun (x : I) (l : Fin (k+2)) => nativeLayerPrepare_unitary A
    (fun i => max 0 ((f x-f i)/(4*σ))) k l hA (fun _ => le_max_left _ _)
  let law := nativeSignedLaw A j f σ k hA hP hN
  refine ⟨hP,hN,law,fun _ => rfl,?_⟩
  have hgood := signed_centered_same_program_mean_guarantee I k A j (fun i => (f i:ℝ)) (σ:ℝ)
    hA hk (by exact_mod_cast hσ) hvar
  have hd := native_signed_record_l1 I A j f σ k hA hP hN
  have ht := native_record_event_lower law (signedMeanLaw k A j (fun i => (f i:ℝ)) (σ:ℝ) hA)
    (2*(1/2:ℝ)^k) hd (Finset.univ.filter (fun ω : I×(LayerRecord k×LayerRecord k) =>
      |(f ω.1:ℝ)+4*(σ:ℝ)*(layerEstimate k ω.2.1-layerEstimate k ω.2.2)-μ|≤8*(σ:ℝ)*(1/2:ℝ)^k))
  have hb : (1/2:ℝ)^k≤(1/2:ℝ)^4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  change 2/3≤∑ ω∈Finset.univ.filter (fun ω : I×(LayerRecord k×LayerRecord k) =>
      |(f ω.1:ℝ)+4*(σ:ℝ)*(layerEstimate k ω.2.1-layerEstimate k ω.2.2)-μ|≤8*(σ:ℝ)*(1/2:ℝ)^k),
        (signedMeanLaw k A j (fun i => (f i:ℝ)) (σ:ℝ) hA).prob ω at hgood
  norm_num at hb
  linarith

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
set_option warningAsError false

theorem native_sorted_median_failure {I : Type} [Fintype I] [DecidableEq I] (p : FinDist I) (v : I → ℝ) (r : ℕ) (μ ε : ℝ)
    (hε : 0 ≤ ε) (hb : mass p (fun x => ε < |v x-μ|) ≤ 11/24) :
    p.probEvent (fun ω : Fin (2*r+1) → I =>
      ε < |sortedBlockMedian r (fun k => v (ω k))-μ|) ≤ (143/144 : ℝ)^r := by
  let B := fun x => ε < |v x-μ|
  let w := fun x => if B x then (13/11 : ℝ) else 1
  have hw : (∑ x, p.prob x*w x)=1+(2/11)*mass p B := by
    have he (x : I) : p.prob x*w x=p.prob x+(2/11)*(if B x then p.prob x else 0) := by
      dsimp [w]
      by_cases hx : B x <;> simp [hx]; ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, p.sum_one, ← Finset.mul_sum, ← Finset.sum_filter]
    rfl
  have hmoment : (∑ ω : Fin (2*r+1) → I, p.probOf ω*∏ k, w (ω k)) ≤ (13/12 : ℝ)^(2*r+1) := by
    rw [p.expect_prod (fun _ x => w x)]
    simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    apply pow_le_pow_left₀
    · exact add_nonneg (by norm_num) (mul_nonneg (by norm_num) (mass_nonneg p B))
    · linarith
  have hbound : (13/11 : ℝ)^(r+1)*p.probEvent (fun ω : Fin (2*r+1) → I =>
      ε < |sortedBlockMedian r (fun k => v (ω k))-μ|) ≤
      ∑ ω : Fin (2*r+1) → I, p.probOf ω*∏ k, w (ω k) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ ω with ε < |sortedBlockMedian r (fun k => v (ω k))-μ|,
          p.probOf ω*∏ k, w (ω k) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hh := heterogeneous_sorted_median_majority_witness r (fun k => v (ω k)) μ ε hε
          (Finset.mem_filter.mp hω).2
        have he : (∏ k, w (ω k)) = (13/11 : ℝ)^(Finset.univ.filter (fun k => B (ω k))).card := by
          simp only [w, Finset.prod_ite, Finset.prod_const, one_pow, mul_one, div_pow]
        have hp : 0 ≤ p.probOf ω := Finset.prod_nonneg (fun _ _ => p.nonneg _)
        rw [he, mul_comm ((13/11 : ℝ)^(r+1))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh) hp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => mul_nonneg (Finset.prod_nonneg (fun _ _ => p.nonneg _))
          (Finset.prod_nonneg (fun _ _ => by dsimp [w]; split_ifs <;> norm_num)))
  have he : (13/12 : ℝ)^(2*r+1)/(13/11 : ℝ)^(r+1)=(11/12 : ℝ)*(143/144 : ℝ)^r := by
    rw [pow_succ, pow_succ, pow_mul]
    rw [show (13/12 : ℝ)^2=(143/144 : ℝ)*(13/11) from by norm_num, mul_pow]
    field_simp
  calc
    _ ≤ (13/12 : ℝ)^(2*r+1)/(13/11 : ℝ)^(r+1) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using! hbound.trans hmoment)
    _ = _ := he
    _ ≤ (143/144 : ℝ)^r := by
      have hp : 0 ≤ (143/144 : ℝ)^r := by positivity
      nlinarith

def nativeLayerTableComparisons {I : Type} [Fintype I] (f : I→ℚ) (k l : ℕ) : ℕ :=
  ∑ i, ((rationalSqrtBracket (nativeLayerPayoff f l i) (nativeLayerBits k)).2.2+
    (rationalSqrtBracket (1-nativeLayerPayoff f l i) (nativeLayerBits k)).2.2)

theorem native_layered_paid_ledger
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (k : ℕ)
    (_hA : A∈Matrix.unitaryGroup I ℂ) (hf : ∀ i,0≤f i) :
    (∀ l : Fin (k+2),nativeLayerTableComparisons f k l=2*Fintype.card I*nativeLayerBits k) ∧
    (∀ l : Fin (k+2),aeForwardAccesses (aeAccessWord (I:=I×Bool) (layerGrid k))=layerGrid k ∧
      aeBackwardAccesses (aeAccessWord (I:=I×Bool) (layerGrid k))=layerGrid k-1 ∧
      QueryCount (countedAECircuit (layerGrid k) (nativeLayerPrepare A f k l) (j,false))=layerGrid k-1) ∧
    2*(k+2)*(2*layerRepetitions k+1)=(k+2)*(2*layerRepetitions k+1)+(k+2)*(2*layerRepetitions k+1) := by
  refine ⟨?_,?_,by ring⟩
  · intro l
    have hc (q : ℚ) (hq : 0≤q) (hq1 : q≤1) :=
      (rational_sqrt_bracket_actual_interval_and_comparisons q (nativeLayerBits k) hq hq1).2.2.2.2.2.2.1
    unfold nativeLayerTableComparisons
    have hp (i : I) := native_layered_payoff_exact_partition I f hf l i
    have hfirst (i : I) : (rationalSqrtBracket (nativeLayerPayoff f l i) (nativeLayerBits k)).2.2=nativeLayerBits k :=
      hc _ (hp i).1 (hp i).2.1
    have hsecond (i : I) : (rationalSqrtBracket (1-nativeLayerPayoff f l i) (nativeLayerBits k)).2.2=nativeLayerBits k :=
      hc _ (by linarith [(hp i).2.1]) (by linarith [(hp i).1])
    simp_rw [hfirst,hsecond]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    ring

  · intro l
    have hsep := prepared_ae_separate_access_counts (I:=I×Bool) (layerGrid k) (layerGrid_pos k)
    have hquery :=
        (prepared_ae_access_ledger (layerGrid k) (layerGrid_pos k) (nativeLayerPrepare A f k l) (j,false)).1
    exact ⟨hsep.1,hsep.2.1,hquery⟩

theorem native_signed_pilot_scale_consumer
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ)
    (N h : ℕ) (nu eps : ℚ) (pilot : Fin N→I)
    (hA : A∈Matrix.unitaryGroup I ℂ) (hN : 0<N) (hf : ∀ i,|f i|≤1)
    (hnu : 0<nu) (hnu1 : nu≤1/4) (heps : 0<eps)
    (hvar : (∑ i,BornProb (A*ᵥKet j) i*((f i:ℝ)-∑ z,BornProb (A*ᵥKet j) z*(f z:ℝ))^2)≤
      (pilotScale N h f nu pilot:ℝ)^2) :
    ∃ (hP : ∀ (x : I) (l : Fin (pilotPrecision N h f nu eps pilot+2)),nativeLayerPrepare A
        (fun i => max 0 ((f i-f x)/(4*pilotScale N h f nu pilot))) (pilotPrecision N h f nu eps pilot) l∈
          Matrix.unitaryGroup (I×Bool) ℂ)
      (hN : ∀ (x : I) (l : Fin (pilotPrecision N h f nu eps pilot+2)),nativeLayerPrepare A
        (fun i => max 0 ((f x-f i)/(4*pilotScale N h f nu pilot))) (pilotPrecision N h f nu eps pilot) l∈
          Matrix.unitaryGroup (I×Bool) ℂ)
      (law : FinDist (I×(LayerRecord (pilotPrecision N h f nu eps pilot)×LayerRecord (pilotPrecision N h f nu eps pilot)))),
      (∑ ω∈Finset.univ.filter (fun ω =>
        |signedMeanEstimate (pilotPrecision N h f nu eps pilot) (fun i => (f i:ℝ))
          (pilotScale N h f nu pilot:ℝ) ω-∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)|≤(eps:ℝ)),law.prob ω)≥13/24 ∧
      law=nativeSignedLaw A j f (pilotScale N h f nu pilot) (pilotPrecision N h f nu eps pilot) hA hP hN := by
  have hs :=
      (unknown_variance_pilot_native_moments_and_scale I N h f nu pilot hN hf hnu hnu1).2.2.2.2.1
  have hp :=
      unknown_variance_pilot_computed_precision_and_worst_path I N h f nu eps pilot hN hf hnu hnu1 heps
  let k := pilotPrecision N h f nu eps pilot
  let σ := pilotScale N h f nu pilot
  obtain ⟨hP,hN,law,hexact,hgood⟩ :=
      native_signed_centered_same_program_consumer I A j f σ k hA hp.1 hs hvar
  have he : law=nativeSignedLaw A j f σ k hA hP hN := by
    cases law
    congr
    funext ω
    exact hexact ω
  refine ⟨hP,hN,law,hgood.trans ?_,he⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hω).2.trans hp.2.1⟩
  · intro ω _ _; exact law.nonneg ω

theorem native_signed_fresh_median : ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
  (j : I) (f : I→ℚ) (σ : ℚ) (k r : ℕ), A∈Matrix.unitaryGroup I ℂ → 4≤k → 0 < σ →
  let μ := ∑ i,BornProb (A*ᵥKet j) i*(f i:ℝ)
  (∑ i,BornProb (A*ᵥKet j) i*((f i:ℝ)-μ)^2)≤(σ:ℝ)^2 →
  ∃ (hP : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
      (fun i => max 0 ((f i-f x)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (hN : ∀ (x : I) (l : Fin (k+2)),nativeLayerPrepare A
      (fun i => max 0 ((f x-f i)/(4*σ))) k l∈Matrix.unitaryGroup (I×Bool) ℂ)
    (law : FinDist (I×(LayerRecord k×LayerRecord k))),
  (∀ ω,law.prob ω=BornProb (A*ᵥKet j) ω.1*
    (∏ l : Fin (k+2),(aeLaw (layerGrid k) (nativeLayerPrepare A
      (fun i => max 0 ((f i-f ω.1)/(4*σ))) k l) (j,false) (nativeLayerEvent I)
      (hP ω.1 l) (layerGrid_ge_two k)).probOf (ω.2.1 l))*
    (∏ l : Fin (k+2),(aeLaw (layerGrid k) (nativeLayerPrepare A
      (fun i => max 0 ((f ω.1-f i)/(4*σ))) k l) (j,false) (nativeLayerEvent I)
      (hN ω.1 l) (layerGrid_ge_two k)).probOf (ω.2.2 l))) ∧
  law.probEvent (fun ω : Fin (2*r+1)→I×(LayerRecord k×LayerRecord k) =>
    8*(σ:ℝ)*(1/2:ℝ)^k < |signedMeanMedian k r (fun i => (f i:ℝ)) (σ:ℝ) ω-μ|)≤(143/144:ℝ)^r
 := by
  intro I _ _ A j f σ k r hA hk hσ μ hvar
  obtain ⟨hP,hN,law,hexact,hgood⟩ :=
      native_signed_centered_same_program_consumer I A j f σ k hA hk hσ hvar
  refine ⟨hP,hN,law,hexact,?_⟩
  let v := signedMeanEstimate k (fun i => (f i:ℝ)) (σ:ℝ)
  let ε := 8*(σ:ℝ)*(1/2:ℝ)^k
  have hmass : mass law (fun ω => |v ω-μ|≤ε)+mass law (fun ω => ε< |v ω-μ|)=1 := by
    have hh := mass_complement law (fun ω => |v ω-μ|≤ε)
    simpa only [not_le] using! hh
  have hbad : mass law (fun ω => ε< |v ω-μ|)≤11/24 := by
    change 13/24≤ mass law (fun ω => |v ω-μ|≤ε) at hgood
    linarith
  exact native_sorted_median_failure law v r μ ε (by dsimp [ε]; positivity) hbad

noncomputable def nativeLayerAEPrograms {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℚ) :
    List (Circuit (Fin (layerGrid k) × (Bool × (I × Bool)))) :=
  (List.ofFn (fun l : Fin (k+2) => List.replicate (2*layerRepetitions k+1)
    (countedAECircuit (layerGrid k) (nativeLayerPrepare A f k l.val) (j,false)))).flatten

theorem nativeLayerAEPrograms_counts {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℚ) :
    let q := (k+2)*(2*layerRepetitions k+1)
    (nativeLayerAEPrograms k A j f).length=q ∧
      ((nativeLayerAEPrograms k A j f).map QueryCount).sum=q*(layerGrid k-1) ∧
      ((nativeLayerAEPrograms k A j f).map GateCount).sum=q*(5*(layerGrid k-1)+3) := by
  have hquery (l : Fin (k+2)) := (prepared_ae_access_ledger (layerGrid k) (layerGrid_pos k)
    (nativeLayerPrepare A f k l.val) (j,false)).1
  have hgate (l : Fin (k+2)) := (prepared_ae_access_ledger (layerGrid k) (layerGrid_pos k)
    (nativeLayerPrepare A f k l.val) (j,false)).2.1
  constructor
  · simp [nativeLayerAEPrograms, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    ring
  · constructor <;>
      simp only [nativeLayerAEPrograms, List.map_flatten, List.sum_flatten,
        Function.comp_def, List.map_ofFn, List.sum_ofFn, List.map_replicate, List.sum_replicate,
        hquery, hgate, nsmul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    all_goals push_cast; ring

def nativeSignedTableComparisons {I : Type} [Fintype I] (f : I→ℚ) (σ : ℚ) (k : ℕ) (x : I) : ℕ :=
  ∑ l : Fin (k+2), (nativeLayerTableComparisons (fun i => max 0 ((f i-f x)/(4*σ))) k l+
    nativeLayerTableComparisons (fun i => max 0 ((f x-f i)/(4*σ))) k l)

noncomputable def nativeSignedAEPrograms {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (σ : ℚ) (k : ℕ) (x : I) :=
  nativeLayerAEPrograms k A j (fun i => max 0 ((f i-f x)/(4*σ))) ++
    nativeLayerAEPrograms k A j (fun i => max 0 ((f x-f i)/(4*σ)))

theorem native_signed_actual_program_ledger
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I→ℚ) (σ : ℚ) (k : ℕ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (x : I) :
    let q := 2*(k+2)*(2*layerRepetitions k+1)
    nativeSignedTableComparisons f σ k x=4*(k+2)*Fintype.card I*nativeLayerBits k ∧
    (nativeSignedAEPrograms A j f σ k x).length=q ∧
    ((nativeSignedAEPrograms A j f σ k x).map QueryCount).sum=q*(layerGrid k-1) ∧
    ((nativeSignedAEPrograms A j f σ k x).map GateCount).sum=q*(5*(layerGrid k-1)+3) ∧
    (q*aeForwardAccesses (aeAccessWord (I:=I×Bool) (layerGrid k))=q*layerGrid k ∧
      q*aeBackwardAccesses (aeAccessWord (I:=I×Bool) (layerGrid k))=q*(layerGrid k-1)) := by
  (try dsimp only)
  have hpos :=
      (native_layered_paid_ledger I A j (fun i => max 0 ((f i-f x)/(4*σ))) k hA (fun _ => le_max_left _ _)).1
  have hneg :=
      (native_layered_paid_ledger I A j (fun i => max 0 ((f x-f i)/(4*σ))) k hA (fun _ => le_max_left _ _)).1
  have hp := nativeLayerAEPrograms_counts k A j (fun i => max 0 ((f i-f x)/(4*σ)))
  have hn := nativeLayerAEPrograms_counts k A j (fun i => max 0 ((f x-f i)/(4*σ)))
  have hc := prepared_ae_separate_access_counts (I:=I×Bool) (layerGrid k) (layerGrid_pos k)
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold nativeSignedTableComparisons
    simp_rw [hpos,hneg]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    ring
  · simp [nativeSignedAEPrograms, hp.1, hn.1]; ring
  · simp [nativeSignedAEPrograms, List.map_append, List.sum_append, hp.2.1, hn.2.1]; ring
  · simp [nativeSignedAEPrograms, List.map_append, List.sum_append, hp.2.2, hn.2.2]; ring
  · rw [hc.1,hc.2.1]; exact ⟨rfl,rfl⟩

end Qatlib.Concepts.NativeNumerics.LayeredMean
