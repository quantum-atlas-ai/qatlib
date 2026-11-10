/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21StrictSeparationStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessNega
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
private noncomputable def rowCertificate (x : Fin 20) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => kushilevitzInputW x i = kushilevitzFunW x)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem row_certificate_valid : ∀ x : Fin 20, (rowCertificate x).card = 3 ∧
    ∀ v : Fin 6 → Bool, (∀ i ∈ rowCertificate x, v i = kushilevitzInputW x i) →
      kushilevitzMonotone v = kushilevitzFunW x := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem row_certificate_cover : ∀ w : Fin 6 → Bool, ∃ x : Fin 20,
    kushilevitzFunW x = kushilevitzMonotone w ∧
      ∀ i ∈ rowCertificate x, w i = kushilevitzInputW x i := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem input_embedding_facts : Function.Injective kushilevitzInputW ∧
    ∀ x : Fin 20, kushilevitzMonotone (kushilevitzInputW x) = kushilevitzFunW x := by
  decide +kernel
private def separatedRow : Fin 6 → Fin 20 := ![18,19,17,17,18,13]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in

private theorem filter_nonzero_entries : ∀ i : Fin 6,
    kushilevitzFunW 0 ≠ kushilevitzFunW (separatedRow i) ∧
    kushilevitzInputW 0 i ≠ kushilevitzInputW (separatedRow i) i ∧
    kushilevitzDist 0 (separatedRow i) = 2 := by
  decide +kernel

private theorem initial_le_fold_max (l : List ℝ) (z : ℝ) : z ≤ l.foldl max z := by
  induction l generalizing z with
  | nil => exact le_rfl
  | cons b l ih => exact (le_max_left z b).trans (ih (max z b))

private theorem mem_le_fold_max (l : List ℝ) (z a : ℝ) (ha : a ∈ l) : a ≤ l.foldl max z := by
  induction l generalizing z with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with hab | ha
    · simpa only [hab] using! (le_max_right z b).trans (initial_le_fold_max l (max z b))
    · exact ih (max z b) ha

private theorem witness_filter_positive (i : Fin 6) :
    0 < ‖weightedAdvFilter kushilevitzInputW kushilevitzGammaW i‖ := by
  obtain ⟨hfun,hbit,hdist⟩ := filter_nonzero_entries i
  have he : weightedAdvFilter kushilevitzInputW kushilevitzGammaW i 0 (separatedRow i) =
      (kushilevitzWeightA : ℂ) := by
    simp [weightedAdvFilter,kushilevitzGammaW,hfun,hbit,kushilevitzWeight,hdist]
  apply norm_pos_iff.mpr
  intro hz
  have hh := congrFun (congrFun hz 0) (separatedRow i)
  rw [he] at hh
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt (by unfold kushilevitzWeightA; positivity))) hh

private theorem witness_filter_le_one (i : Fin 6) :
    ‖weightedAdvFilter kushilevitzInputW kushilevitzGammaW i‖ ≤ 1 := by
  have hm : ‖advFilter kushilevitzInputW kushilevitzGammaW i‖ ∈
      List.ofFn (fun j : Fin 6 => ‖advFilter kushilevitzInputW kushilevitzGammaW j‖) :=
    List.mem_ofFn.mpr ⟨i,rfl⟩
  exact (mem_le_fold_max _ 0 _ hm).trans theorem21RealizedWitness.2.2.1

theorem theorem21StrictSeparation : Theorem21StrictSeparation := by
  classical
  constructor
  · let r (w : Fin 6 → Bool) := Classical.choose (row_certificate_cover w)
    have hr (w : Fin 6 → Bool) : kushilevitzFunW (r w) = kushilevitzMonotone w ∧
        ∀ i ∈ rowCertificate (r w), w i = kushilevitzInputW (r w) i :=
      Classical.choose_spec (row_certificate_cover w)
    let c (w : Fin 6 → Bool) := rowCertificate (r w)
    have hcard (w : Fin 6 → Bool) : ((c w).card : ℝ) ≤ 3 := by
      have hh := (row_certificate_valid (r w)).1
      dsimp [c]
      rw [hh]
      norm_num
    have hcvalid (w v : Fin 6 → Bool) (he : ∀ i ∈ c w, v i = w i) :
        kushilevitzMonotone v = kushilevitzMonotone w := by
      apply ((row_certificate_valid (r w)).2 v (fun i hi => (he i hi).trans ((hr w).2 i hi))).trans
      exact (hr w).1
    have hc (w v : Fin 6 → Bool) (hdiff : kushilevitzMonotone w ≠ kushilevitzMonotone v) :
        ∃ j ∈ c w ∩ c v, w j ≠ v j := by
      by_contra hh
      have he (j : Fin 6) (hj : j ∈ c w ∩ c v) : w j = v j := by
        by_contra hn
        exact hh ⟨j,hj,hn⟩
      let z : Fin 6 → Bool := fun j => if j ∈ c w then w j else v j
      have hw := hcvalid w z (by intro j hj; simp [z,hj])
      have hv := hcvalid v z (by
        intro j hj
        by_cases hjw : j ∈ c w
        · simp [z,hjw,he j (Finset.mem_inter.mpr ⟨hjw,hj⟩)]
        · simp [z,hjw])
      exact hdiff (hw.symm.trans hv)
    exact advNonneg_le_of_certificates (fun w => w) kushilevitzMonotone c 3 (by norm_num) hcard hc
  · let A : {A : Matrix (Fin 20) (Fin 20) ℂ // A.IsHermitian ∧
        ∀ x y, kushilevitzFunW x = kushilevitzFunW y → A x y = 0} :=
      ⟨kushilevitzGammaW,theorem21RealizedWitness.1,theorem21RealizedWitness.2.1⟩
    have hv : 2+3*Real.sqrt 5/5 ≤ advWitnessValue kushilevitzInputW (fun _ => 1) kushilevitzGammaW := by
      apply le_ciInf
      intro i
      simp only [one_mul]
      calc
        _ ≤ ‖kushilevitzGammaW‖ := theorem21RealizedWitness.2.2.2
        _ ≤ ‖kushilevitzGammaW‖/‖weightedAdvFilter kushilevitzInputW kushilevitzGammaW i‖ :=
          (le_div_iff₀ (witness_filter_positive i)).mpr
            (mul_le_of_le_one_right (norm_nonneg _) (witness_filter_le_one i))
    have hs : ENNReal.ofReal (2+3*Real.sqrt 5/5) ≤ advPlus kushilevitzInputW kushilevitzFunW (fun _ => 1) := by
      apply (ENNReal.ofReal_le_ofReal hv).trans
      apply le_iSup_of_le A
      exact le_rfl
    exact hs.trans (advPlus_mono_of_injective (fun _ => 1) kushilevitzInputW input_embedding_facts.1
      kushilevitzInputW kushilevitzFunW (fun w => w) kushilevitzMonotone (fun _ => rfl) input_embedding_facts.2)

theorem three_lt_kushilevitz_threshold : (3 : ℝ) < 2+3*Real.sqrt 5/5 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg 5
  nlinarith

end Qatlib.Concepts.AdversaryBounds.AdvDuality
