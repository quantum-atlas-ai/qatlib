/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.KnownCountPermutation
import Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Count Cohorts

The actual slots occupied by one known address, with their literal multiplicity.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

/-- The actual slots occupied by one known address, with their literal multiplicity. -/
def slots {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) (a : A) :
    {j : Fin Q // y j=a} ≃ Fin (multiplicity y a) := Fintype.equivFin _

/-- A known basis equivalence groups every unknown spin into its original address cohort. -/
def group {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) :
    (Fin Q → Bool) ≃ ((a : A) → Fin (multiplicity y a) → Bool) :=
  Equiv.piCongrFiberwise (fun a => Equiv.piCongrLeft' (fun _ : {j : Fin Q // y j=a} => Bool) (slots y a))

/-- Grouping only reindexes the original unknown spin basis. -/
theorem group_apply {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (y : Fin Q → A) (s : Fin Q → Bool) (a : A) (i : Fin (multiplicity y a)) :
    group y s a i=s ((slots y a).symm i).val := rfl

/-- Original tensor amplitudes factor over actual address cohorts, including all empty cohorts. -/
theorem amplitude_group {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (y : Fin Q → A) (u : A → Bool → ℂ) (s : Fin Q → Bool) :
    copyAmplitude u Q (fun j => (y j,s j))=
      ∏ a : A,∏ i : Fin (multiplicity y a),u a (group y s a i) := by
  have h := Equiv.prod_comp (Equiv.sigmaFiberEquiv y)
    (fun j : Fin Q => u (y j) (s j))
  change (∏ j : Fin Q,u (y j) (s j))=_
  rw [←h,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro a _
  have ht := Equiv.prod_comp (slots y a).symm
    (fun j : {j : Fin Q // y j=a} => u a (s j.val))
  simp only [Equiv.sigmaFiberEquiv_apply]
  calc
    _ = ∏ j : {j : Fin Q // y j=a},u a (s j.val) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [j.property]
    _ = _ := by simpa only [group_apply] using ht.symm

/-- The full edge-cohort basis retains both original spin cohorts for every matched pair. -/
abbrev EdgeBasis {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ} (y : Fin Q → E × Bool) :=
  (e : E) → PairBasis (multiplicity y (e,false)) (multiplicity y (e,true))

/-- Regrouping matched labels is an equivalence of complete physical spin bases. -/
def siteToEdge {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ} (y : Fin Q → E × Bool) :
    ((a : E × Bool) → Fin (multiplicity y a) → Bool) ≃ EdgeBasis y where
  toFun s e := (s (e,false),s (e,true))
  invFun t a := match a with
    | (e,false) => (t e).1
    | (e,true) => (t e).2
  left_inv s := by
    funext a
    rcases a with ⟨e,b⟩
    cases b <;> rfl
  right_inv t := by
    funext e
    rfl

/-- The known pair grouping is a basis equivalence for every copy count. -/
def groupPairs {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ} (y : Fin Q → E × Bool) :
    (Fin Q → Bool) ≃ EdgeBasis y := (group y).trans (siteToEdge y)

/-- The literal full spin tensor factors into the actual two cohorts at every matched edge. -/
theorem amplitude_groupPairs {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (y : Fin Q → E × Bool) (u : E × Bool → Bool → ℂ) (s : Fin Q → Bool) :
    copyAmplitude u Q (fun j => (y j,s j))=
      ∏ e : E,(∏ i : Fin (multiplicity y (e,false)),u (e,false) ((groupPairs y s e).1 i))*
        (∏ i : Fin (multiplicity y (e,true)),u (e,true) ((groupPairs y s e).2 i)) := by
  rw [amplitude_group,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro e _
  rw [Fintype.prod_bool]
  exact mul_comm _ _

end Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

namespace Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation

/-- The original four-pair ordering fixes the first sign once for its complete cohort. -/
def firstSign (i : Fin 4) : ℝ := ![-1,1,-1,1] i

/-- The original four-pair ordering fixes the second sign once for its complete cohort. -/
def secondSign (i : Fin 4) : ℝ := ![-1,-1,1,1] i

/-- The full unknown field retains each sampled sign on every copy of its site. -/
def pairedWeakSpin {E : Type*} (b : ℝ) (κ : E → Fin 4) (a : E × Bool) : Bool → ℂ :=
  weakSpin b (if a.2 then secondSign (κ a.1) else firstSign (κ a.1))

/-- The literal four physical vectors use exactly these two original signs. -/
theorem physicalPairStates_signs (b : ℝ) (r s : ℕ) (i : Fin 4) :
    physicalPairStates b r s i=physicalPair b r s (firstSign i) (secondSign i) := by
  fin_cases i <;> rfl

/-- The complete same-sign tensor factors into the actual physical pair vectors under a known basis equivalence. -/
theorem paired_amplitude {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (b : ℝ) (y : Fin Q → E × Bool) (κ : E → Fin 4) (s : Fin Q → Bool) :
    copyAmplitude (pairedWeakSpin b κ) Q (fun j => (y j,s j))=
      ∏ e : E,physicalPairStates b (multiplicity y (e,false)) (multiplicity y (e,true))
        (κ e) (pairBasisEquiv _ _ (groupPairs y s e)) := by
  rw [amplitude_groupPairs]
  apply Finset.prod_congr rfl
  intro e _
  rw [physicalPairStates_signs]
  simp only [physicalPair,tensorVector,Equiv.symm_apply_apply,weakCopies,pairedWeakSpin,
    Bool.false_eq_true,ite_false,ite_true]

/-- Independent original edge-sign pairs, without independent resampling between copies. -/
def pairedSignLaw {E : Type*} [Fintype E] (ρ : ℝ) (κ : E → Fin 4) : ℝ :=
  ∏ e : E,signPairLaw ρ (κ e)

/-- The actual independent pair law is normalized, including the empty edge product. -/
theorem pairedSignLaw_prob {E : Type*} [Fintype E] [DecidableEq E] (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    (∀ κ : E → Fin 4,0≤pairedSignLaw ρ κ) ∧ (∑ κ : E → Fin 4,pairedSignLaw ρ κ)=1 := by
  have hp := signPairLaw_prob ρ hlo hhi
  constructor
  · intro κ
    exact Finset.prod_nonneg (fun e _ => hp.1 (κ e))
  · change (∑ κ : E → Fin 4,∏ e : E,signPairLaw ρ (κ e))=1
    rw [←Fintype.prod_sum (fun (_e : E) (i : Fin 4) => signPairLaw ρ i)]
    simp only [hp.2,Finset.prod_const_one]

/-- The literal original conditional spin density is averaged over the same fixed sign field. -/
def conditionalDensity {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (b : ℝ) (y : Fin Q → E × Bool) (ρ : ℝ) : Matrix (Fin Q → Bool) (Fin Q → Bool) ℂ :=
  ∑ κ : E → Fin 4,(pairedSignLaw ρ κ : ℂ) •
    outerProduct (fun s : Fin Q → Bool => copyAmplitude (pairedWeakSpin b κ) Q (fun j => (y j,s j)))

/-- Full conditional density entries are the product of the actual count-indexed quantum pair densities. -/
theorem conditionalDensity_entry {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (b : ℝ) (y : Fin Q → E × Bool) (ρ : ℝ) (s t : Fin Q → Bool) :
    conditionalDensity b y ρ s t=
      ∏ e : E,physicalPairMixture b (multiplicity y (e,false)) (multiplicity y (e,true)) ρ
        (pairBasisEquiv _ _ (groupPairs y s e)) (pairBasisEquiv _ _ (groupPairs y t e)) := by
  simp only [conditionalDensity,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    outerProduct,Matrix.of_apply,paired_amplitude,pairedSignLaw,Complex.ofReal_prod,map_prod]
  simp only [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (e : E) (i : Fin 4) => (signPairLaw ρ i : ℂ)*(
    physicalPairStates b (multiplicity y (e,false)) (multiplicity y (e,true)) i
      (pairBasisEquiv _ _ (groupPairs y s e))*
    (starRingEnd ℂ) (physicalPairStates b (multiplicity y (e,false)) (multiplicity y (e,true)) i
      (pairBasisEquiv _ _ (groupPairs y t e)))))]
  rfl

end Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

open scoped Classical BigOperators
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

/-- A known complete basis equivalence expresses every original spin coordinate on the actual pair matrix bases. -/
def pairCoordinates {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (y : Fin Q → E × Bool) : (Fin Q → Bool) ≃
      ((e : E) → Fin (Fintype.card (PairBasis (multiplicity y (e,false)) (multiplicity y (e,true))))) :=
  (groupPairs y).trans (Equiv.piCongrRight (fun e => pairBasisEquiv (multiplicity y (e,false)) (multiplicity y (e,true))))

/-- A complete physical spin register is large enough to purify each actual conditional pair, including empty cohorts. -/
theorem pair_dimension_le_whole {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (y : Fin Q → E × Bool) (e : E) :
    Fintype.card (PairBasis (multiplicity y (e,false)) (multiplicity y (e,true)))≤
      Fintype.card (Fin Q → Bool) := by
  let : ∀ e : E,Nonempty (Fin (Fintype.card (PairBasis (multiplicity y (e,false)) (multiplicity y (e,true))))) :=
    fun e => ⟨pairBasisEquiv _ _ ((fun _ => false),(fun _ => false))⟩
  have h : Function.Surjective (fun s : Fin Q → Bool => pairCoordinates y s e) :=
    (Function.surjective_eval e).comp (pairCoordinates y).surjective
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective _ h

/-- An environment with one actual full-spin-sized factor per edge is large enough for a full-spin purification. -/
theorem product_environment_card {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E] (Q : ℕ) :
    Fintype.card (Fin Q → Bool)≤Fintype.card (E → Fin (Fintype.card (Fin Q → Bool))) := by
  let : Nonempty (Fin (Fintype.card (Fin Q → Bool))) :=
    ⟨Fintype.equivFin (Fin Q → Bool) (fun _ => false)⟩
  obtain ⟨e⟩ := ‹Nonempty E›
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective _ (Function.surjective_eval (β := fun _ : E => Fin (Fintype.card (Fin Q → Bool))) e)

end Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts

open scoped ComplexOrder
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin

/-- The four actual pair labels give unit signs at both sites. -/
theorem pairedWeakSpin_normalized {E : Type*} (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (κ : E → Fin 4) (a : E × Bool) : Normalized (pairedWeakSpin b κ a) := by
  have hs (i : Fin 4) : (firstSign i)^2=1 ∧ (secondSign i)^2=1 := by
    fin_cases i <;> norm_num [firstSign,secondSign]
  apply weakSpin_normalized b _ hb0 hb1
  split_ifs
  · exact (hs (κ a.1)).2
  · exact (hs (κ a.1)).1

/-- Each literal conditional source tensor retains all Q unknown spins and has norm one. -/
theorem pairedConditionalVector_normalized {E : Type*} [Fintype E] {Q : ℕ}
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (κ : E → Fin 4) (y : Fin Q → E × Bool) :
    Normalized (fun s : Fin Q → Bool => copyAmplitude (pairedWeakSpin b κ) Q (fun j => (y j,s j))) := by
  change (∑ s : Fin Q → Bool,‖∏ j : Fin Q,pairedWeakSpin b κ (y j) (s j)‖^2)=1
  simp only [norm_prod,←Finset.prod_pow]
  rw [←Fintype.prod_sum (fun (j : Fin Q) (t : Bool) => ‖pairedWeakSpin b κ (y j) t‖^2)]
  have hn (j : Fin Q) : (∑ t : Bool,‖pairedWeakSpin b κ (y j) t‖^2)=1 :=
    pairedWeakSpin_normalized b hb0 hb1 κ (y j)
  simp only [hn,Finset.prod_const_one]

/-- The original independent sign prior gives a normalized positive conditional density internally. -/
theorem conditionalDensity_legal {E : Type*} [Fintype E] [DecidableEq E] {Q : ℕ}
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (y : Fin Q → E × Bool) (ρ : ℝ)
    (hlo : -1≤ρ) (hhi : ρ≤1) :
    (conditionalDensity b y ρ).PosSemidef ∧ (conditionalDensity b y ρ).trace=1 := by
  have hp := pairedSignLaw_prob (E := E) ρ hlo hhi
  constructor
  · apply Matrix.posSemidef_sum
    intro κ _
    exact (outerProduct_posSemidef _).smul (by exact_mod_cast hp.1 κ)
  · simp only [conditionalDensity,Matrix.trace_sum,Matrix.trace_smul,
      (outerProduct_density (pairedConditionalVector_normalized b hb0 hb1 _ y)).2,
      smul_eq_mul,mul_one]
    exact_mod_cast hp.2

end Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
