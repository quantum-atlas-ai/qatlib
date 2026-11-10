/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorRefined
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false
variable {I : Type} [Fintype I] [DecidableEq I]

def prefixAdBudget (xs : List (Matrix I I ℂ)) (p : ℕ) : ℝ :=
  ∑ j : Fin xs.length,pfOrderedAdBudget (xs.take j.val) (xs.getD j.val 0) p LinearMap.id

def prefixMultinomial (xs : List (Matrix I I ℂ)) (p : ℕ) : ℝ :=
  ∑ j : Fin xs.length,pfCommAlphaOrderedV2 (xs.take j.val) (xs.getD j.val 0) p

theorem prefixAdBudget_nonneg (xs : List (Matrix I I ℂ)) (p : ℕ) :
    0 ≤ prefixAdBudget xs p :=
  Finset.sum_nonneg (fun _ _ => pfOrderedAdBudget_nonneg _ _ _ _)

theorem prefixMultinomial_eq (xs : List (Matrix I I ℂ)) (p : ℕ) :
    prefixMultinomial xs p=(p.factorial:ℝ)*prefixAdBudget xs p := by
  simp only [prefixMultinomial,pfCommAlphaOrderedV2_eq_budget,prefixAdBudget,Finset.mul_sum]

theorem prefixMultinomial_nonneg (xs : List (Matrix I I ℂ)) (p : ℕ) :
    0 ≤ prefixMultinomial xs p := by
  rw [prefixMultinomial_eq]
  exact mul_nonneg (Nat.cast_nonneg _) (prefixAdBudget_nonneg xs p)

theorem matched_defect_ordered (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p : ℕ) (t : ℝ) (hp : 1 ≤ p)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) :
    ‖pfLeftGenerator xs t-H‖ ≤ prefixAdBudget xs p*|t|^p := by
  have hz := sub_eq_zero.mp (pf_defect_prefix_polynomial_zero xs H p hp hc t)
  have he : pfLeftGenerator xs t-H =
      ∑ j : Fin xs.length,(pfConjWord (xs.take j.val) (xs.getD j.val 0) t -
        pfConjTrunc (xs.take j.val) (xs.getD j.val 0) p t) := by
    rw [Finset.sum_sub_distrib,hz,pfLeftGenerator_prefix_sum]
  rw [he]
  calc
    _ ≤ ∑ j : Fin xs.length,‖pfConjWord (xs.take j.val) (xs.getD j.val 0) t -
        pfConjTrunc (xs.take j.val) (xs.getD j.val 0) p t‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin xs.length,pfOrderedAdBudget (xs.take j.val) (xs.getD j.val 0) p LinearMap.id*|t|^p := by
      apply Finset.sum_le_sum
      intro j _
      have hh := pfConjWord_ordered_remainder_norm_mode true (xs.take j.val)
        (xs.getD j.val 0) p t (fun _ Y hY => hxs Y (List.mem_of_mem_take hY))
      simpa only [pfWordInflation_true,mul_one] using! hh
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem matched_local_ordered (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p : ℕ) (t : ℝ) (hp : 1 ≤ p)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) (hH : H.conjTranspose = -H) :
    ‖suzukiExponentialWord xs t-NormedSpace.exp (t • H)‖ ≤
      prefixAdBudget xs p*|t|^(p+1)/(p+1:ℕ) := by
  rw [pf_word_duhamel]
  apply pf_norm_integral_power_bound _ t _ p (prefixAdBudget_nonneg xs p)
  intro u _
  have hA := l2_norm_unitary_le_one (general_trotter_exp_unitary H (t-u) hH)
  have hS := l2_norm_unitary_le_one (pf_word_unitary xs u hxs)
  calc
    _ ≤ ‖NormedSpace.exp ((t-u) • H)‖*
        (‖pfLeftGenerator xs u-H‖*‖suzukiExponentialWord xs u‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖pfLeftGenerator xs u-H‖*1) := by gcongr
    _ = ‖pfLeftGenerator xs u-H‖ := by ring
    _ ≤ _ := matched_defect_ordered xs H p u hp hc hxs

theorem matched_segmented_ordered (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p r : ℕ) (t : ℝ) (hp : 1 ≤ p) (hr : 0<r)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) (hH : H.conjTranspose = -H) :
    ‖suzukiExponentialWord xs (t/r)^r-NormedSpace.exp (t • H)‖ ≤
      prefixMultinomial xs p*|t|^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p) := by
  rw [← pf_segment_ideal_pow H t r hr]
  have hh := pf_unitary_power_error _ _ (pf_word_unitary xs (t/r) hxs)
    (general_trotter_exp_unitary H (t/r) hH) r
  apply (hh.trans (mul_le_mul_of_nonneg_left
    (matched_local_ordered xs H p (t/r) hp hc hxs hH) (Nat.cast_nonneg r))).trans_eq
  rw [pf_segment_commutator_budget _ _ _ _ hr,prefixMultinomial_eq]

noncomputable def segments (C ε : ℝ) (p : ℕ) : ℕ :=
  max 1 (Nat.ceil ((C/ε)^((p:ℝ)⁻¹)))

theorem selected_error (C ε : ℝ) (p : ℕ) (hC : 0 ≤ C) (hε : 0 < ε) (hp : 0 < p) :
    0 < segments C ε p ∧ C / (segments C ε p : ℝ)^p ≤ ε := by
  have hr1 : 1 ≤ segments C ε p := le_max_left _ _
  have hr : 0 < segments C ε p := by omega
  refine ⟨hr, ?_⟩
  have hA : 0 ≤ C/ε := div_nonneg hC hε.le
  have hpow : C/ε ≤ (segments C ε p : ℝ)^p := by
    rw [← Real.rpow_inv_natCast_pow hA hp.ne']
    apply pow_le_pow_left₀ (Real.rpow_nonneg hA _)
    apply (Nat.le_ceil _).trans
    exact_mod_cast le_max_right 1 (Nat.ceil ((C/ε)^((p:ℝ)⁻¹)))
  have hrpow : 0 < (segments C ε p : ℝ)^p := by positivity
  rw [div_le_iff₀ hrpow]
  have := (div_le_iff₀ hε).mp hpow
  nlinarith

def orderedErrorCoefficient (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) : ℝ :=
  prefixMultinomial xs p*|t|^(p+1)/((p+1).factorial:ℝ)

def orderedSegments (xs : List (Matrix I I ℂ)) (p : ℕ) (t ε : ℝ) : ℕ :=
  segments (orderedErrorCoefficient xs p t) ε p

theorem orderedErrorCoefficient_nonneg (xs : List (Matrix I I ℂ)) (p : ℕ) (t : ℝ) :
    0 ≤ orderedErrorCoefficient xs p t := by
  unfold orderedErrorCoefficient
  exact div_nonneg (mul_nonneg (prefixMultinomial_nonneg xs p) (by positivity)) (Nat.cast_nonneg _)

theorem selected_segment_error (xs : List (Matrix I I ℂ)) (H : Matrix I I ℂ)
    (p : ℕ) (t ε : ℝ) (hp : 1 ≤ p) (hε : 0<ε)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) (hH : H.conjTranspose = -H) :
    0<orderedSegments xs p t ε ∧
      ‖(segmentWord xs t (orderedSegments xs p t ε)).prod-NormedSpace.exp (t • H)‖ ≤ ε := by
  cases Subsingleton.elim ‹DecidableEq I› (Classical.decEq I)
  obtain ⟨hr,hbound⟩ := selected_error (orderedErrorCoefficient xs p t) ε p
    (orderedErrorCoefficient_nonneg xs p t) hε (by omega)
  refine ⟨hr,?_⟩
  rw [segmentWord,pf_segment_word_prod]
  apply (matched_segmented_ordered xs H p _ t hp hr hc hxs hH).trans
  convert! hbound using 1
  simp only [orderedErrorCoefficient]
  ring

def taggedSegmentWord {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (t : ℝ) (r : ℕ) : List (Fin m × Matrix I I ℂ) :=
  (List.replicate r ((List.finRange xs.length).map
    (fun i => (lab i,NormedSpace.exp ((t/r) • xs.get i))))).flatten

theorem taggedSegmentWord_erase {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (t : ℝ) (r : ℕ) :
    (taggedSegmentWord xs lab t r).map Prod.snd = segmentWord xs t r := by
  cases Subsingleton.elim ‹DecidableEq I› (Classical.decEq I)
  unfold taggedSegmentWord segmentWord
  rw [List.map_flatten,List.map_replicate,List.map_map]
  congr 2
  rw [← List.ofFn_eq_map]
  exact List.ofFn_getElem_eq_map xs (fun X => NormedSpace.exp ((t/r) • X))

theorem taggedSegmentWord_visits {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (t : ℝ) (r : ℕ) (j : Fin m) :
    (taggedSegmentWord xs lab t r).countP (fun z => z.1=j) =
      r*((List.finRange xs.length).filter (fun i => lab i=j)).length := by
  unfold taggedSegmentWord
  rw [List.countP_flatten,List.map_replicate,List.sum_replicate,List.countP_map,
    List.countP_eq_length_filter]
  simp only [Function.comp_def,smul_eq_mul]

theorem selected_tagged_error {m : ℕ} (xs : List (Matrix I I ℂ))
    (lab : Fin xs.length → Fin m) (H : Matrix I I ℂ) (p : ℕ) (t ε : ℝ)
    (hp : 1 ≤ p) (hε : 0<ε)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • H^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) (hH : H.conjTranspose = -H) :
    0<orderedSegments xs p t ε ∧
      ‖((taggedSegmentWord xs lab t (orderedSegments xs p t ε)).map Prod.snd).prod-
        NormedSpace.exp (t • H)‖ ≤ ε ∧
      ∀ j,(taggedSegmentWord xs lab t (orderedSegments xs p t ε)).countP (fun z => z.1=j) =
        orderedSegments xs p t ε*((List.finRange xs.length).filter (fun i => lab i=j)).length := by
  rw [taggedSegmentWord_erase]
  exact ⟨(selected_segment_error xs H p t ε hp hε hc hxs hH).1,
    (selected_segment_error xs H p t ε hp hε hc hxs hH).2,
    fun j => taggedSegmentWord_visits xs lab t _ j⟩

def prefixIndex {α : Type*} (xs : List α) (j : ℕ) (i : Fin (xs.take j).length) : Fin xs.length :=
  ⟨i.val,lt_of_lt_of_le i.isLt (List.length_take_le' j xs)⟩

def familyPrefixMultinomial {D m : ℕ} (H : Fin m → Operator D)
    (xs : List (Operator D)) (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ)
    (p : ℕ) : ℝ :=
  ∑ j : Fin xs.length,∑ q∈pfCompositions (xs.take j.val).length p,
    (p.factorial:ℝ)*(∏ i,((q i).factorial:ℝ))⁻¹ *
      |scaleProduct (fun i => c (prefixIndex xs j.val i)) q*c j| *
      ‖pfNestedCommList (H (lab j)::
        (familyCompositionWord (fun i => lab (prefixIndex xs j.val i)) q).map H)‖

omit [DecidableEq I] in

theorem nested_seed_smul (a : ℝ) (B : Matrix I I ℂ) (l : List (Matrix I I ℂ)) :
    pfNestedCommList ((a • B)::l)=a • pfNestedCommList (B::l) := by
  rw [clause50_nested_comm_eq_fold,clause50_nested_comm_eq_fold]
  exact clause50_fold_seed_scale l a B

theorem prefixMultinomial_family {D m : ℕ} (H : Fin m → Operator D)
    (xs : List (Operator D)) (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ)
    (hfam : IsFamilyWord H xs lab c) (p : ℕ) :
    prefixMultinomial xs p=familyPrefixMultinomial H xs lab c p := by
  unfold prefixMultinomial familyPrefixMultinomial
  apply Finset.sum_congr rfl
  intro j _
  have hprefix : IsFamilyWord H (xs.take j.val)
      (fun i => lab (prefixIndex xs j.val i)) (fun i => c (prefixIndex xs j.val i)) := by
    intro i
    simpa only [List.get_eq_getElem,List.getElem_take,prefixIndex] using!
        hfam (prefixIndex xs j.val i)
  rw [pfCommAlphaOrderedV2_eq_budget,
    clause50_family_ordered_budget_eq H (xs.getD j.val 0) LinearMap.id (xs.take j.val) _ _ hprefix p]
  apply Finset.sum_congr rfl
  intro q _
  have hseed : xs.getD j.val 0=c j • H (lab j) := by
    simpa only [List.get_eq_getElem,List.getD_eq_getElem _ _ j.isLt] using! hfam j
  simp only [LinearMap.id_apply]
  rw [hseed,nested_seed_smul,norm_smul,Real.norm_eq_abs,abs_mul]
  ring

theorem matched_segmented_family {D m : ℕ} (H : Fin m → Operator D)
    (xs : List (Operator D)) (lab : Fin xs.length → Fin m) (c : Fin xs.length → ℝ)
    (hfam : IsFamilyWord H xs lab c) (K : Operator D) (p r : ℕ) (t : ℝ)
    (hp : 1 ≤ p) (hr : 0<r)
    (hc : ∀ n≤p,suzukiSeries xs n=((n.factorial:ℝ)⁻¹) • K^n)
    (hxs : ∀ X∈xs,X.conjTranspose = -X) (hK : K.conjTranspose = -K) :
    ‖suzukiExponentialWord xs (t/r)^r-NormedSpace.exp (t • K)‖ ≤
      familyPrefixMultinomial H xs lab c p*|t|^(p+1)/(((p+1).factorial:ℝ)*(r:ℝ)^p) := by
  rw [← prefixMultinomial_family H xs lab c hfam p]
  exact matched_segmented_ordered xs K p r t hp hr hc hxs hK

theorem recursive_segmented_ordered (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ)
    (hr : 0<r) (hhs : ∀ X∈hs,X.conjTranspose = -X) :
    ‖suzukiExponentialWord (recursiveSuzukiGenerators hs k) (t/r)^r-
        NormedSpace.exp (t • hs.sum)‖ ≤
      prefixMultinomial (recursiveSuzukiGenerators hs k) (2*(k+1))*|t|^(2*(k+1)+1)/
        (((2*(k+1)+1).factorial:ℝ)*(r:ℝ)^(2*(k+1))) := by
  have hsum : hs.sum.conjTranspose = -hs.sum := by
    induction hs with
    | nil => simp
    | cons X xs ih =>
      simp only [List.sum_cons,Matrix.conjTranspose_add,hhs X (by simp),
        ih (fun Y hY => hhs Y (List.mem_cons_of_mem X hY)),neg_add]
  exact matched_segmented_ordered (recursiveSuzukiGenerators hs k) hs.sum (2*(k+1)) r t
    (by omega) hr (recursive_suzuki_all_even_order_coefficients I hs k)
    (recursiveSuzukiGenerators_antiHermitian hs k hhs) hsum

end Qatlib.Concepts.TrotterFormula.GeneralOrder
