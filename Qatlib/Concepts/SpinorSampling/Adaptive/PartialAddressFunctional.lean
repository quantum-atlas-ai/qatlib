/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressUnrotated
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressTwoColor
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressAdaptive

set_option backward.isDefEq.respectTransparency false

/-!
Full clipped F output under real, history-dependent matching measurements.
The order matches the reference direction/color loop. Every stage uses the
original supplied spinors, fresh native pilot and selected-word main law;
records are written into a finite history and the same sparse count-map is
postprocessed with the production nested clipping. Public trained/unrotated
tails derive all component probabilities internally and use the exact budgets.
Literal producer hN/hbudget/hcount and runtime word checks remain explicit.
This does not certify native address gates, complete costs or final L_h.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.FunctionalProgram
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open RetainedSpin FiniteAxisWord UniformMatching

/-- Abbreviation for Index in the partial address functional model. -/
abbrev Index (d : ℕ) := Fin d × Fin 2
/-- Abbreviation for Pilot in the partial address functional model. -/
abbrev Pilot (d r p : ℕ) := Fin 3 → Fin p → (Fin d → Fin (2^r)) × Bool
/-- Abbreviation for Data in the partial address functional model. -/
abbrev Data (C m d r p n : ℕ) (i : Index d) := Pilot d r p × (Fin n → GlobalRecord (TrainedGrid.Edge C m d i.1))
/-- Abbreviation for History in the partial address functional model. -/
abbrev History (C m d r p n : ℕ) := (i : Index d) → Option (Data C m d r p n i)
/-- Typeclass instance for history Fintype in the partial address functional model. -/
instance historyFintype (C m d r p n : ℕ) : Fintype (History C m d r p n) := by
  letI : (i : Index d) → Fintype (Option (Data C m d r p n i)) := fun i => inferInstance
  exact Pi.instFintype

/-- Typeclass instance for history Nonempty in the partial address functional model. -/
instance historyNonempty (C m d r p n : ℕ) : Nonempty (History C m d r p n) :=
  ⟨fun _ => none⟩

/-- Typeclass instance for history Decidable Eq in the partial address functional model. -/
noncomputable instance historyDecidableEq (C m d r p n : ℕ) : DecidableEq (History C m d r p n) :=
  Classical.decEq _

/-- Abbreviation for Words in the partial address functional model. -/
abbrev Words (C m d r p n : ℕ) := (i : Index d) → History C m d r p n → Pilot d r p → TrainedGrid.Box C d → List Gate

/-- Construction for raw At in the partial address functional model. -/
def rawAt {C m d r p n : ℕ} (h : History C m d r p n) (i : Index d) : ℚ :=
  match h i with
  | none => 0
  | some z => CountMap.sparseCountValueQ z.2

/-- Construction for center in the partial address functional model. -/
def center (C m d r : ℕ) [NeZero (C*(2*m))] (hN : 2^r=C*(2*m)*2)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (i : Index d) : ℝ :=
  TrainedOriginal.target C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k

/-- Construction for bad At in the partial address functional model. -/
def badAt {C m d r p n : ℕ} [NeZero (C*(2*m))] (hN : 2^r=C*(2*m)*2)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (ε : ℝ) (i : Index d) (h : History C m d r p n) : ℝ :=
  if ε/(d : ℝ)< |(rawAt h i : ℝ)-center C m d r hN a b c k i| then 1 else 0

/-- Construction for stage in the partial address functional model. -/
def stage (C m d r p n : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (words : Words C m d r p n) (i : Index d) (past : FinDist (History C m d r p n)) :
    FinDist (History C m d r p n) :=
  Schedule.step past (NativePilot.originalTraining d r a b c k hz p)
    (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k false)
    (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k true)
    (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz false)
    (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz true)
    (fun h Ω e => words i h Ω e.1) n (fun h Ω ω => Function.update h i (some (Ω,ω)))

/-- Construction for initial in the partial address functional model. -/
def initial (C m d r p n : ℕ) : FinDist (History C m d r p n) where
  prob h := if h=(fun _ => none) then 1 else 0
  nonneg h := by split_ifs <;> norm_num
  sum_one := by
    classical
    simp

/-- Construction for order in the partial address functional model. -/
def order (d : ℕ) : List (Index d) :=
  List.ofFn (fun j : Fin (d*2) => (finProdFinEquiv (m:=d) (n:=2)).symm j)

/-- Complete original `mem_order` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem mem_order (d : ℕ) (i : Index d) : i∈order d := by
  simp only [order,List.mem_ofFn]
  exact ⟨finProdFinEquiv i,Equiv.symm_apply_apply _ i⟩

/-- Construction for law in the partial address functional model. -/
def law (C m d r p n : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (words : Words C m d r p n) :
    FinDist (History C m d r p n) :=
  Schedule.run (stage C m d r p n hN a b c k hz words) (order d) (initial C m d r p n)

/-- Construction for value Q in the partial address functional model. -/
def valueQ {C m d r p n : ℕ} (p0 : ℚ) (h : History C m d r p n) : ℚ :=
  TwoColor.clippedValueQ p0 (fun j color => rawAt h (j,color))

/-- Complete original `stage_keeps` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem stage_keeps (C m d r p n : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (words : Words C m d r p n)
    (ε : ℝ) (i j : Index d) (hne : i≠j) (past : FinDist (History C m d r p n)) :
    (stage C m d r p n hN a b c k hz words j past).expect (badAt hN a b c k ε i)=
      past.expect (badAt hN a b c k ε i) := by
  unfold stage
  apply Schedule.step_keep
  intro h Ω ω
  simp only [badAt,rawAt,Function.update_of_ne hne]

/-- Complete original `stage_bound` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
private theorem stage_bound (C m d r p n : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (words : Words C m d r p n)
    (ε bnd : ℝ) (i : Index d) (past : FinDist (History C m d r p n))
    (hcomponent : ∀ h,(TrainedMain.trainedLaw (NativePilot.originalTraining d r a b c k hz p)
      (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k false)
      (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k true)
      (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz false)
      (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz true)
      (fun Ω e => words i h Ω e.1) n).expect
        (fun z => if ε/(d : ℝ)< |(CountMap.sparseCountValueQ z.2 : ℝ)-center C m d r hN a b c k i|
          then (1 : ℝ) else 0)≤bnd) :
    (stage C m d r p n hN a b c k hz words i past).expect (badAt hN a b c k ε i)≤bnd := by
  unfold stage
  refine Schedule.step_bound _ _ _ _ _ _ _ _ _ _
    (fun z => if ε/(d : ℝ)< |(CountMap.sparseCountValueQ z.2 : ℝ)-center C m d r hN a b c k i|
      then (1 : ℝ) else 0) bnd ?_ hcomponent
  intro h Ω ω
  simp only [badAt,rawAt,Function.update_self]

/-- Complete original `full_tail` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
private theorem full_tail (C m d r p n : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (hd : 0<d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (words : Words C m d r p n) (ε bnd : ℝ)
    (hcomponent : ∀ i h,(TrainedMain.trainedLaw (NativePilot.originalTraining d r a b c k hz p)
      (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k false)
      (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k true)
      (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz false)
      (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz true)
      (fun Ω e => words i h Ω e.1) n).expect
        (fun z => if ε/(d : ℝ)< |(CountMap.sparseCountValueQ z.2 : ℝ)-center C m d r hN a b c k i|
          then (1 : ℝ) else 0)≤bnd) :
    (law C m d r p n hN a b c k hz words).expect
      (fun h => if ε< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k| then (1 : ℝ) else 0)≤
      (2*(d : ℝ))*bnd := by
  classical
  let out := law C m d r p n hN a b c k hz words
  have hpart (i : Index d) : out.expect (badAt hN a b c k ε i)≤bnd := by
    apply Schedule.run_bound _ (badAt hN a b c k ε) (fun _ => bnd)
      (stage_keeps C m d r p n hN a b c k hz words ε)
      (fun j past => stage_bound C m d r p n hN a b c k hz words ε bnd j past (hcomponent j))
      (order d) i (mem_order d i)
  have hnonneg (h : History C m d r p n) (i : Index d) : 0≤badAt hN a b c k ε i h := by
    unfold badAt
    split_ifs <;> norm_num
  have hdom (h : History C m d r p n) :
      (if ε< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k| then (1 : ℝ) else 0)≤
        ∑ i : Index d,badAt hN a b c k ε i h := by
    by_cases hb : ε< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k|
    · have hex : ∃ i : Index d,ε/(d : ℝ)< |(rawAt h i : ℝ)-center C m d r hN a b c k i| := by
        by_contra! hno
        have hgood := TwoColor.clipped_value_error C m d r hN hd a b c k hz p0 hp
          (fun j color => rawAt h (j,color)) ε (fun j color => hno (j,color))
        exact (not_le_of_gt hb) hgood
      obtain ⟨i,hi⟩ := hex
      rw [ite_eq_left hb]
      calc
        (1 : ℝ) = badAt hN a b c k ε i h := by simp only [badAt,ite_eq_left hi]
        _ ≤ ∑ j : Index d,badAt hN a b c k ε j h :=
          Finset.single_le_sum (fun j _ => hnonneg h j) (Finset.mem_univ i)
    · rw [ite_eq_right hb]
      exact Finset.sum_nonneg (fun j _ => hnonneg h j)
  calc
    _ ≤ out.expect (fun h => ∑ i : Index d,badAt hN a b c k ε i h) := finite_expect_mono _ _ _ hdom
    _ = ∑ i : Index d,out.expect (badAt hN a b c k ε i) := finite_expect_sum _ _
    _ ≤ ∑ _i : Index d,bnd := Finset.sum_le_sum (fun i _ => hpart i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
      ring

/-- Complete original `trained_tail` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem trained_tail (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (hd : 0<d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (α β τ ε : ℚ) (hα : 0<α) (hβ : 0<β) (hτ : 0<τ) (hτ1 : τ≤1/2)
    (hbudget : (d : ℝ)*((2*m : ℕ) : ℝ)^2*(p0 : ℝ)≤(τ : ℝ)/32)
    (n : ℕ) (hcount : checkedXYZCountQ ((2^r)^d) τ (ε/(d : ℚ)) β=some n)
    (words : Words C m d r (PilotVector.pilotCountQ ((2*C)^d) α τ) n)
    (hcheck : ∀ i h Ω box,AxisCertificate.check (fun axis => PilotProjection.counterMeanQ box
      (fun t => NativePilot.recordEquiv (GridPatch.nativeGridEquiv C (2*m) d r hN
        (TwoColor.offset C m d i.1 i.2)) (Ω axis t))) τ (words i h Ω box)=true) :
    (law C m d r (PilotVector.pilotCountQ ((2*C)^d) α τ) n hN a b c k hz words).expect
      (fun h => if (ε : ℝ)< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k| then (1 : ℝ) else 0)≤
      (2*(d : ℝ))*((α : ℝ)+(β : ℝ)) := by
  apply full_tail C m d r _ n hN hd a b c k hz p0 hp words (ε : ℝ) ((α : ℝ)+(β : ℝ))
  intro i h
  have hc : checkedXYZCountQ (2*Fintype.card (TrainedGrid.Edge C m d i.1)) τ (ε/(d : ℚ)) β=some n := by
    rw [TrainedGrid.matching_card C m d r hN (TwoColor.offset C m d i.1 i.2) i.1]
    exact hcount
  have ht := TrainedOriginal.original_matching_tail C m d r hN (TwoColor.offset C m d i.1 i.2)
    i.1 a b c k hz (p0 : ℝ) hp α β τ (ε/(d : ℚ)) hα hβ hτ hτ1 hbudget
    (words i h) (hcheck i h) n hc
  simpa only [TrainedOriginal.originalLaw,Rat.cast_div,Rat.cast_natCast,center] using ht

/-- Complete original `unrotated_tail` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem unrotated_tail (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (hd : 0<d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (β ε : ℚ) (n : ℕ) (hcount : checkedXYZCountQ ((2^r)^d) (1/2) (ε/(d : ℚ)) β=some n) :
    (law C m d r 0 n hN a b c k hz (fun _ _ _ _ => [])).expect
      (fun h => if (ε : ℝ)< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k| then (1 : ℝ) else 0)≤
      (2*(d : ℝ))*(β : ℝ) := by
  apply full_tail C m d r 0 n hN hd a b c k hz p0 hp (fun _ _ _ _ => []) (ε : ℝ) (β : ℝ)
  intro i h
  rw [Schedule.empty_words_expect (f:=fun ω : Fin n → GlobalRecord (TrainedGrid.Edge C m d i.1) =>
    if (ε : ℝ)/(d : ℝ)< |(CountMap.sparseCountValueQ ω : ℝ)-center C m d r hN a b c k i|
      then (1 : ℝ) else 0),← TrainedMain.event_weighted]
  have hc : checkedXYZCountQ (2*Fintype.card (TrainedGrid.Edge C m d i.1)) (1/2) (ε/(d : ℚ)) β=some n := by
    rw [TrainedGrid.matching_card C m d r hN (TwoColor.offset C m d i.1 i.2) i.1]
    exact hcount
  have ht := Functional.checked_unrotated_confidence
    (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k false)
    (TrainedOriginal.endpointSpin C m d r hN (TwoColor.offset C m d i.1 i.2) i.1 a b c k true)
    (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz false)
    (TrainedOriginal.endpoint_mass C m d r hN _ i.1 a b c k hz true)
    (ε/(d : ℚ)) β n hc
  simpa only [Rat.cast_div,Rat.cast_natCast,center,TrainedOriginal.target] using ht

/-- Construction for failure Share in the partial address functional model. -/
def failureShare (d : ℕ) (δ : ℚ) : ℚ := δ/(4*(d : ℚ))

/-- Complete original `failure_share_pos` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem failure_share_pos (d : ℕ) (hd : 0<d) (δ : ℚ) (hδ : 0<δ) : 0<failureShare d δ := by
  unfold failureShare
  apply div_pos hδ
  have hdQ : (0 : ℚ)<d := by exact_mod_cast hd
  positivity

/-- Complete original `trained_confidence` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem trained_confidence (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (hd : 0<d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (δ τ ε : ℚ) (hδ : 0<δ) (hτ : 0<τ) (hτ1 : τ≤1/2)
    (hbudget : (d : ℝ)*((2*m : ℕ) : ℝ)^2*(p0 : ℝ)≤(τ : ℝ)/32)
    (n : ℕ) (hcount : checkedXYZCountQ ((2^r)^d) τ (ε/(d : ℚ)) (failureShare d δ)=some n)
    (words : Words C m d r (PilotVector.pilotCountQ ((2*C)^d) (failureShare d δ) τ) n)
    (hcheck : ∀ i h Ω box,AxisCertificate.check (fun axis => PilotProjection.counterMeanQ box
      (fun t => NativePilot.recordEquiv (GridPatch.nativeGridEquiv C (2*m) d r hN
        (TwoColor.offset C m d i.1 i.2)) (Ω axis t))) τ (words i h Ω box)=true) :
    (law C m d r (PilotVector.pilotCountQ ((2*C)^d) (failureShare d δ) τ) n hN a b c k hz words).expect
      (fun h => if (ε : ℝ)< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k| then (1 : ℝ) else 0)≤(δ : ℝ) := by
  have hs := failure_share_pos d hd δ hδ
  have ht := trained_tail C m d r hN hd a b c k hz p0 hp (failureShare d δ) (failureShare d δ)
    τ ε hs hs hτ hτ1 hbudget n hcount words hcheck
  have hd0 : (d : ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
  calc
    _ ≤ (2*(d : ℝ))*((failureShare d δ : ℝ)+(failureShare d δ : ℝ)) := ht
    _ = (δ : ℝ) := by
      simp only [failureShare,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
      field_simp
      ring

/-- Complete original `unrotated_confidence` guarantee for `PartialAddressFunctional`; all source hypotheses and output obligations are retained. -/
theorem unrotated_confidence (C m d r : ℕ) [NeZero C] [NeZero m] [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (hd : 0<d) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (p0 : ℚ)
    (hp : ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p0 : ℝ))
    (δ ε : ℚ) (hδ : 0<δ) (n : ℕ)
    (hcount : checkedXYZCountQ ((2^r)^d) (1/2) (ε/(d : ℚ)) (failureShare d δ)=some n) :
    (law C m d r 0 n hN a b c k hz (fun _ _ _ _ => [])).expect
      (fun h => if (ε : ℝ)< |(valueQ p0 h : ℝ)-TwoColor.fullTarget d r a b c k| then (1 : ℝ) else 0)≤(δ : ℝ) := by
  have ht := unrotated_tail C m d r hN hd a b c k hz p0 hp (failureShare d δ) ε n hcount
  have hd0 : (d : ℝ)≠0 := by exact_mod_cast (by omega : d≠0)
  calc
    _ ≤ (2*(d : ℝ))*(failureShare d δ : ℝ) := ht
    _ = (δ : ℝ)/2 := by
      simp only [failureShare,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
      field_simp
      norm_num
    _ ≤ (δ : ℝ) := by have hδR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ; linarith

#print axioms initial
#print axioms order
#print axioms mem_order
#print axioms stage
#print axioms law
#print axioms stage_keeps
#print axioms trained_tail
#print axioms unrotated_tail
#print axioms failure_share_pos
#print axioms trained_confidence
#print axioms unrotated_confidence
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.FunctionalProgram
