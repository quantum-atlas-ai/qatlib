/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver
import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweightingBoundary
import Qatlib.Concepts.Waterfill.LevelFidelity.WaterfillZeroLimits
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel

set_option autoImplicit false
set_option maxHeartbeats 1500000
open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.Waterfill.LevelFidelity
open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

def rationalCheckedFill {m : ℕ} (π σ : Fin m → ℚ) (p γ : ℚ) : Option (Fin m → ℚ) :=
  if 0<computedMass π σ γ then
    if p*computedMass π σ γ≤computedDot π σ γ^2 then some (waterFill π σ γ) else none
  else none
end Qatlib.Concepts.Waterfill.LevelFidelity

noncomputable section
namespace Qatlib.Concepts.Waterfill.LevelFidelity.WaterfillZeroBoundary
open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open Qatlib
open Filter Set
open scoped Classical BigOperators Topology
variable {m : ℕ}

def projectedSource (π σ : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if 0<σ i then π i else 0

def projectedMass (π σ : Fin m → ℝ) : ℝ := ∑ i,(projectedSource π σ i)^2

def overlap (π σ : Fin m → ℝ) : ℝ := ∑ i,σ i*π i

def high (π σ : Fin m → ℝ) : ℝ :=
  1+∑ i,if 0<σ i then π i/σ i else 0

def lowDen (π σ : Fin m → ℝ) : ℝ :=
  1+∑ i,if 0<π i then σ i/π i else 0

def low (π σ : Fin m → ℝ) : ℝ := (lowDen π σ)⁻¹

theorem high_ge_one (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) : 1≤high π σ := by
  have hs : 0≤∑ i,if 0<σ i then π i/σ i else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs with hi
    · exact div_nonneg (hπ i) hi.le
    · exact le_rfl
  dsimp [high]
  linarith

theorem lowDen_ge_one (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) : 1≤lowDen π σ := by
  have hs : 0≤∑ i,if 0<π i then σ i/π i else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs with hi
    · exact div_nonneg (hσ i) hi.le
    · exact le_rfl
  dsimp [lowDen]
  linarith

theorem low_pos (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) : 0<low π σ :=
  inv_pos.mpr (lt_of_lt_of_le zero_lt_one (lowDen_ge_one π σ hσ))

theorem low_le_one (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) : low π σ≤1 := by
  exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (lowDen_ge_one π σ hσ))).mpr
    (lowDen_ge_one π σ hσ)

theorem high_bracket (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) :
    BracketHigh π σ (high π σ) := by
  intro i hi
  have hterm : π i/σ i ≤ ∑ j,if 0<σ j then π j/σ j else 0 := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if 0<σ j then π j/σ j else 0)
      (fun j _ => by (try dsimp only); split_ifs with hj; exact div_nonneg (hπ j) hj.le; exact le_rfl)
      (Finset.mem_univ i)
    simpa only [if_pos hi] using! hh
  apply (div_le_iff₀ hi).mp
  dsimp [high]
  linarith

theorem low_bracket (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) :
    BracketLow π σ (low π σ) := by
  intro i hi
  have hterm : σ i/π i ≤ ∑ j,if 0<π j then σ j/π j else 0 := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if 0<π j then σ j/π j else 0)
      (fun j _ => by (try dsimp only); split_ifs with hj; exact div_nonneg (hσ j) hj.le; exact le_rfl)
      (Finset.mem_univ i)
    simpa only [if_pos hi] using! hh
  have hden : 0<lowDen π σ := lt_of_lt_of_le zero_lt_one (lowDen_ge_one π σ hσ)
  have hh : σ i≤lowDen π σ*π i := by
    apply (div_le_iff₀ hi).mp
    dsimp [lowDen]
    linarith
  dsimp [low]
  apply (inv_mul_le_iff₀ hden).mpr
  exact hh

theorem fill_high (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (i : Fin m) : realFill π σ (high π σ) i=projectedSource π σ i := by
  unfold projectedSource
  split_ifs with hi
  · exact realFill_bracketHigh hπ (high_bracket π σ hπ) i hi
  · exact realFill_zeroSigma hπ i (le_antisymm (not_lt.mp hi) (hσ i))

theorem mass_high (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i) :
    realMass π σ (high π σ)=projectedMass π σ := by
  simp only [realMass,projectedMass,fill_high π σ hπ hσ]

theorem dot_high (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i) :
    realDot π σ (high π σ)=overlap π σ := by
  unfold realDot overlap
  apply Finset.sum_congr rfl
  intro i _
  rw [fill_high π σ hπ hσ]
  unfold projectedSource
  split_ifs with hi
  · rfl
  · have hz : σ i=0 := le_antisymm (not_lt.mp hi) (hσ i)
    simp only [hz,zero_mul]

theorem mass_low (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i) :
    realMass π σ (low π σ)=(low π σ)^2*realPmax π σ :=
  realMass_bracketLow hπ hσ (low_pos π σ hσ).le (low_bracket π σ hσ)

theorem dot_low (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i) :
    realDot π σ (low π σ)=low π σ*realPmax π σ :=
  realDot_bracketLow hπ hσ (low_pos π σ hσ).le (low_bracket π σ hσ)

def HasOverlap (π σ : Fin m → ℝ) : Prop := ∃ i,0<π i ∧ 0<σ i

theorem pmax_pos_iff (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) :
    0<realPmax π σ ↔ HasOverlap π σ := by
  constructor
  · intro hp
    by_contra hn
    have hz : ∀ i, (if 0<π i then σ i^2 else 0)=0 := by
      intro i
      split_ifs with hi
      · have hs : ¬0<σ i := fun hh => hn ⟨i,hi,hh⟩
        have he : σ i=0 := le_antisymm (not_lt.mp hs) (hσ i)
        simp only [he,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      · rfl
    simp only [realPmax,hz,Finset.sum_const_zero] at hp
    exact (lt_irrefl 0) hp
  · rintro ⟨i,hi,hs⟩
    have hterm : (if 0<π i then σ i^2 else 0) ≤ realPmax π σ :=
      Finset.single_le_sum (f := fun j => if 0<π j then σ j^2 else 0)
        (fun j _ => by (try dsimp only); split_ifs; exact sq_nonneg _; exact le_rfl)
        (Finset.mem_univ i)
    rw [if_pos hi] at hterm
    exact lt_of_lt_of_le (sq_pos_of_pos hs) hterm

theorem mass_pos (π σ : Fin m → ℝ) (ho : HasOverlap π σ) (γ : ℝ) (hγ : 0<γ) :
    0<realMass π σ γ := by
  obtain ⟨i,hpi,hsi⟩ := ho
  have hf : 0<realFill π σ γ i := lt_min hpi (mul_pos hγ hsi)
  have hb : (realFill π σ γ i)^2≤realMass π σ γ :=
    Finset.single_le_sum (fun j _ => sq_nonneg (realFill π σ γ j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le (sq_pos_of_pos hf) hb

theorem fill_no_overlap (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (hn : ¬HasOverlap π σ) (γ : ℝ) (hγ : 0≤γ) (i : Fin m) : realFill π σ γ i=0 := by
  by_cases hi : 0<π i
  · have hs : σ i=0 := le_antisymm (not_lt.mp (fun hh => hn ⟨i,hi,hh⟩)) (hσ i)
    exact realFill_zeroSigma hπ i hs
  · exact realFill_sourceZero hσ hγ i (le_antisymm (not_lt.mp hi) (hπ i))

theorem mass_no_overlap (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (hn : ¬HasOverlap π σ) (γ : ℝ) (hγ : 0≤γ) : realMass π σ γ=0 := by
  simp only [realMass,fill_no_overlap π σ hπ hσ hn γ hγ,ne_eq,OfNat.ofNat_ne_zero,
    not_false_eq_true,zero_pow,Finset.sum_const_zero]

theorem fidelity_low (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) : realFidelity π σ (low π σ)=realPmax π σ := by
  have hm := mass_pos π σ ho (low π σ) (low_pos π σ hσ)
  rw [realFidelity,if_neg hm.ne',mass_low π σ hπ hσ,dot_low π σ hπ hσ]
  have hl := low_pos π σ hσ
  have hp := (pmax_pos_iff π σ hσ).mpr ho
  field_simp

theorem fidelity_high (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) :
    realFidelity π σ (high π σ)=(overlap π σ)^2/projectedMass π σ := by
  have hm := mass_pos π σ ho (high π σ) (lt_of_lt_of_le zero_lt_one (high_ge_one π σ hπ))
  rw [realFidelity,if_neg hm.ne',mass_high π σ hπ hσ,dot_high π σ hπ hσ]

def checkedFill (π σ : Fin m → ℝ) (p γ : ℝ) : Option (Fin m → ℝ) :=
  if 0<realMass π σ γ then
    if p*realMass π σ γ ≤ realDot π σ γ^2 then some (realFill π σ γ) else none
  else none

theorem checkedFill_spec (π σ : Fin m → ℝ) (p γ : ℝ) (x : Fin m → ℝ) :
    checkedFill π σ p γ=some x ↔
      0<realMass π σ γ ∧ p≤realFidelity π σ γ ∧ x=realFill π σ γ := by
  unfold checkedFill
  split_ifs with hm hp
  · simp only [Option.some.injEq]
    rw [realFidelity,if_neg hm.ne',le_div_iff₀ hm]
    constructor
    · intro he; exact ⟨hm,hp,he.symm⟩
    · rintro ⟨_,_,he⟩;exact he.symm
  · simp only [false_iff]
    rintro ⟨_,hf,_⟩
    rw [realFidelity,if_neg hm.ne',le_div_iff₀ hm] at hf
    exact hp hf
  · simp only [false_iff]
    rintro ⟨hh,_,_⟩
    exact hm hh

theorem checkedFill_no_overlap (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (hn : ¬HasOverlap π σ) (p γ : ℝ) (hγ : 0≤γ) : checkedFill π σ p γ=none := by
  simp only [checkedFill,mass_no_overlap π σ hπ hσ hn γ hγ,lt_self_iff_false,if_false]

theorem exists_finite_level (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) (p : ℝ)
    (hp : (overlap π σ)^2/projectedMass π σ≤p ∧ p≤realPmax π σ) :
    ∃ γ∈Set.Icc (low π σ) (high π σ),RealizesFidelity π σ p γ := by
  have hb : low π σ≤high π σ := (low_le_one π σ hσ).trans (high_ge_one π σ hπ)
  have hm : ∀ γ∈Set.Icc (low π σ) (high π σ),realMass π σ γ≠0 := by
    intro γ hγ
    exact (mass_pos π σ ho γ ((low_pos π σ hσ).trans_le hγ.1)).ne'
  have hc := ((continuous_realDot (π := π) (σ := σ)).continuousOn.pow 2).div
    (continuous_realMass (π := π) (σ := σ)).continuousOn hm
  have hend : realDot π σ (high π σ)^2/realMass π σ (high π σ)≤p ∧
      p≤realDot π σ (low π σ)^2/realMass π σ (low π σ) := by
    simpa only [← fidelity_eq_div,fidelity_high π σ hπ hσ ho,fidelity_low π σ hπ hσ ho] using! hp
  obtain ⟨γ,hγ,hval⟩ := intermediate_value_Icc' hb hc hend
  refine ⟨γ,hγ,mass_pos π σ ho γ ((low_pos π σ hσ).trans_le hγ.1),?_⟩
  exact (div_eq_iff (hm γ hγ)).mp hval

def vectorMass (x : Fin m → ℝ) : ℝ := ∑ i,x i^2

def vectorDot (σ x : Fin m → ℝ) : ℝ := ∑ i,σ i*x i

theorem sourceBox_overlap_bound (π σ x : Fin m → ℝ) (hx : SourceBox π x) :
    (vectorDot σ x)^2≤realPmax π σ*vectorMass x := by
  let s : Fin m → ℝ := fun i => if 0<π i then σ i else 0
  have hdot : vectorDot σ x=∑ i,s i*x i := by
    unfold vectorDot
    apply Finset.sum_congr rfl
    intro i _
    dsimp [s]
    split_ifs with hi
    · rfl
    · have hz : x i=0 := le_antisymm ((hx i).2.trans (not_lt.mp hi)) (hx i).1
      simp only [hz,mul_zero]
  have hs : (∑ i,s i^2)=realPmax π σ := by
    unfold realPmax
    apply Finset.sum_congr rfl
    intro i _
    dsimp [s]
    split_ifs <;> simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
  rw [hdot]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s x).trans_eq (by rw [hs]; rfl)

theorem checkedFill_unreachable (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (p γ : ℝ) (hγ : 0≤γ) (hp : realPmax π σ<p) : checkedFill π σ p γ=none := by
  have hbox : SourceBox π (realFill π σ γ) := by
    intro i
    exact ⟨le_min (hπ i) (mul_nonneg hγ (hσ i)),min_le_left _ _⟩
  have hc := sourceBox_overlap_bound π σ (realFill π σ γ) hbox
  change realDot π σ γ^2≤realPmax π σ*realMass π σ γ at hc
  unfold checkedFill
  split_ifs with hm hh
  · have hlt := mul_lt_mul_of_pos_right hp hm
    exact False.elim (not_lt_of_ge (hh.trans hc) hlt)
  · rfl
  · rfl

def boundaryFill (π σ : Fin m → ℝ) (lam : ℝ) : Fin m → ℝ :=
  fun i => if 0<σ i then π i else min (π i) lam

def boundaryResidualMass (π σ : Fin m → ℝ) (lam : ℝ) : ℝ :=
  ∑ i,if σ i=0 then (min (π i) lam)^2 else 0

theorem boundaryMass (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) (lam : ℝ) :
    vectorMass (boundaryFill π σ lam)=projectedMass π σ+boundaryResidualMass π σ lam := by
  unfold vectorMass projectedMass boundaryResidualMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0<σ i
  · have hn : σ i≠0 := hi.ne'
    simp only [boundaryFill,projectedSource,if_pos hi,if_neg hn,add_zero]
  · have hz : σ i=0 := le_antisymm (not_lt.mp hi) (hσ i)
    simp only [boundaryFill,projectedSource,if_neg hi,if_pos hz,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_add]

theorem boundaryDot (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) (lam : ℝ) :
    vectorDot σ (boundaryFill π σ lam)=overlap π σ := by
  unfold vectorDot overlap
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0<σ i
  · simp only [boundaryFill,if_pos hi]
  · have hz : σ i=0 := le_antisymm (not_lt.mp hi) (hσ i)
    simp only [hz,zero_mul]

theorem boundary_zero (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) :
    boundaryFill π σ 0=projectedSource π σ := by
  funext i
  unfold boundaryFill projectedSource
  split_ifs with hi
  · rfl
  · exact min_eq_right (hπ i)

theorem boundary_eventually (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i)
    (lam : ℝ) (hlam : 0<lam) :
    ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      realFill π (fun i => σ i+δ) (lam/δ)=boundaryFill π σ lam := by
  have hh : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ i, realFill π (fun j => σ j+δ) (lam/δ) i=boundaryFill π σ lam i :=
    Filter.eventually_all.mpr (fun i => boundary_fill π σ hσ lam hlam i)
  exact hh.mono (fun _ h => funext h)

def sourceCap (π : Fin m → ℝ) : ℝ := 1+∑ i,π i

theorem source_le_cap (π : Fin m → ℝ) (hπ : ∀ i,0≤π i) (i : Fin m) : π i≤sourceCap π := by
  have hh := Finset.single_le_sum (f := π) (fun j _ => hπ j) (Finset.mem_univ i)
  dsimp [sourceCap]
  linarith

theorem boundary_cap (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) :
    boundaryFill π σ (sourceCap π)=π := by
  funext i
  unfold boundaryFill
  split_ifs with hi
  · rfl
  · exact min_eq_left (source_le_cap π hπ i)

theorem boundary_mass_tendsto (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i)
    (lam : ℝ) (hlam : 0<lam) :
    Tendsto (fun δ : ℝ => realMass π (fun i => σ i+δ) (lam/δ)) (𝓝[>]0)
      (𝓝 (vectorMass (boundaryFill π σ lam))) := by
  have he : (fun δ : ℝ => realMass π (fun i => σ i+δ) (lam/δ)) =ᶠ[𝓝[>]0]
      (fun _ => vectorMass (boundaryFill π σ lam)) := by
    filter_upwards [boundary_eventually π σ hσ lam hlam] with δ hδ
    change vectorMass (realFill π (fun i => σ i+δ) (lam/δ))=_
    rw [hδ]
  exact tendsto_const_nhds.congr' he.symm

theorem boundary_dot_tendsto (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i)
    (lam : ℝ) (hlam : 0<lam) :
    Tendsto (fun δ : ℝ => realDot π (fun i => σ i+δ) (lam/δ)) (𝓝[>]0) (𝓝 (overlap π σ)) := by
  have hc : Continuous (fun δ : ℝ => vectorDot (fun i => σ i+δ) (boundaryFill π σ lam)) := by
    unfold vectorDot
    fun_prop
  have hh : Tendsto (fun δ : ℝ => vectorDot (fun i => σ i+δ) (boundaryFill π σ lam))
      (𝓝[>]0) (𝓝 (overlap π σ)) := by
    have hat : ContinuousAt (fun δ : ℝ => vectorDot (fun i => σ i+δ) (boundaryFill π σ lam)) 0 :=
      hc.continuousAt
    simpa only [add_zero,boundaryDot π σ hσ lam] using!
      hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  apply hh.congr'
  filter_upwards [boundary_eventually π σ hσ lam hlam] with δ hδ
  change vectorDot (fun i => σ i+δ) (boundaryFill π σ lam)=
    vectorDot (fun i => σ i+δ) (realFill π (fun i => σ i+δ) (lam/δ))
  rw [hδ]

theorem boundary_fidelity_tendsto (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i)
    (lam : ℝ) (hlam : 0<lam) (hm : 0<vectorMass (boundaryFill π σ lam)) :
    Tendsto (fun δ : ℝ => realFidelity π (fun i => σ i+δ) (lam/δ)) (𝓝[>]0)
      (𝓝 ((overlap π σ)^2/(projectedMass π σ+boundaryResidualMass π σ lam))) := by
  rw [← boundaryMass π σ hσ lam]
  simp_rw [fidelity_eq_div]
  exact ((boundary_dot_tendsto π σ hσ lam hlam).pow 2).div
    (boundary_mass_tendsto π σ hσ lam hlam) hm.ne'

theorem regularized_positive (σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) (δ : ℝ) (hδ : 0<δ) :
    ∀ i,0<σ i+δ := fun i => add_pos_of_nonneg_of_pos (hσ i) hδ

theorem positive_chain_compatible (π σ : Fin m → ℝ) (hσ : ∀ i,0≤σ i) (γ : ℝ)
    (hm : 0<realMass π σ γ) :
    (∀ δ>0,∀ i,0<σ i+δ) ∧
    (∀ i,Tendsto (fun δ : ℝ => realFill π (fun j => σ j+δ) γ i) (𝓝[>]0)
      (𝓝 (realFill π σ γ i))) ∧
    Tendsto (fun δ : ℝ => realMass π (fun j => σ j+δ) γ) (𝓝[>]0) (𝓝 (realMass π σ γ)) ∧
    Tendsto (fun δ : ℝ => realDot π (fun j => σ j+δ) γ) (𝓝[>]0) (𝓝 (realDot π σ γ)) ∧
    Tendsto (fun δ : ℝ => realFidelity π (fun j => σ j+δ) γ) (𝓝[>]0) (𝓝 (realFidelity π σ γ)) := by
  have hs : ∀ i,Tendsto (fun δ : ℝ => σ i+δ) (𝓝[>]0) (𝓝 (σ i)) := by
    intro i
    simpa only [add_zero] using! tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun δ : ℝ => δ) (𝓝[>]0) (𝓝 0))
  exact ⟨fun δ hδ => regularized_positive σ hσ δ hδ,
    fun i => fill_parameter_tendsto π σ _ hs γ i,mass_parameter_tendsto π σ _ hs γ,
    dot_parameter_tendsto π σ _ hs γ,fidelity_parameter_tendsto π σ _ hs γ hm.ne'⟩

theorem rational_fill_cast (π σ : Fin m → ℚ) (γ : ℚ) (i : Fin m) :
    realFill (fun j => (π j:ℝ)) (fun j => (σ j:ℝ)) (γ:ℝ) i=(waterFill π σ γ i:ℝ) := by
  simp only [realFill,waterFill,Rat.cast_min,Rat.cast_mul]

theorem rational_mass_cast (π σ : Fin m → ℚ) (γ : ℚ) :
    realMass (fun j => (π j:ℝ)) (fun j => (σ j:ℝ)) (γ:ℝ)=(computedMass π σ γ:ℝ) := by
  simp only [realMass,rational_fill_cast,computedMass,computedWaterEnergy,Rat.cast_sum,Rat.cast_pow]

theorem rational_dot_cast (π σ : Fin m → ℚ) (γ : ℚ) :
    realDot (fun j => (π j:ℝ)) (fun j => (σ j:ℝ)) (γ:ℝ)=(computedDot π σ γ:ℝ) := by
  simp only [realDot,rational_fill_cast,computedDot,Rat.cast_sum,Rat.cast_mul]

theorem rational_checked_cast (π σ : Fin m → ℚ) (p γ : ℚ) :
    (rationalCheckedFill π σ p γ).map (fun x i => (x i:ℝ)) =
      checkedFill (fun i => (π i:ℝ)) (fun i => (σ i:ℝ)) (p:ℝ) (γ:ℝ) := by
  unfold rationalCheckedFill checkedFill
  rw [rational_mass_cast,rational_dot_cast]
  have hm : (0<(computedMass π σ γ:ℝ)) ↔ (0:ℚ)<computedMass π σ γ := by exact_mod_cast Iff.rfl
  have hh : (p:ℝ)*(computedMass π σ γ:ℝ)≤(computedDot π σ γ:ℝ)^2 ↔
      p*computedMass π σ γ≤computedDot π σ γ^2 := by exact_mod_cast Iff.rfl
  simp only [hm,hh]
  split_ifs
  · simp only [Option.map_some,Option.some.injEq]
    funext i
    exact (rational_fill_cast π σ γ i).symm
  · rfl
  · rfl

theorem fidelity_anti_positive (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    realFidelity π σ b≤realFidelity π σ a := by
  rw [fidelity_eq_div,fidelity_eq_div]
  exact (div_le_div_iff₀ (mass_pos π σ ho b (ha.trans_le hab)) (mass_pos π σ ho a ha)).mpr
    (realFidelity_anti π σ hπ hσ ha.le hab)

theorem degenerate_interval (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) (he : (overlap π σ)^2/projectedMass π σ=realPmax π σ)
    (γ : ℝ) (hγ : γ∈Set.Icc (low π σ) (high π σ)) :
    realFidelity π σ γ=realPmax π σ := by
  have hu := fidelity_anti_positive π σ hπ hσ ho (low_pos π σ hσ) hγ.1
  have hl := fidelity_anti_positive π σ hπ hσ ho ((low_pos π σ hσ).trans_le hγ.1) hγ.2
  rw [fidelity_low π σ hπ hσ ho] at hu
  rw [fidelity_high π σ hπ hσ ho,he] at hl
  exact le_antisymm hu hl

theorem boundary_mass_pos (π σ : Fin m → ℝ) (ho : HasOverlap π σ) (lam : ℝ) :
    0<vectorMass (boundaryFill π σ lam) := by
  obtain ⟨i,hpi,hsi⟩ := ho
  have hh : (boundaryFill π σ lam i)^2≤vectorMass (boundaryFill π σ lam) :=
    Finset.single_le_sum (fun j _ => sq_nonneg (boundaryFill π σ lam j)) (Finset.mem_univ i)
  simp only [boundaryFill,if_pos hsi] at hh
  exact lt_of_lt_of_le (sq_pos_of_pos hpi) hh

theorem continuous_boundaryMass (π σ : Fin m → ℝ) :
    Continuous (fun lam => vectorMass (boundaryFill π σ lam)) := by
  unfold vectorMass
  apply continuous_finsetSum
  intro i _
  by_cases hi : 0<σ i
  · simp only [boundaryFill,if_pos hi]
    exact continuous_const
  · simp only [boundaryFill,if_neg hi]
    fun_prop

theorem exists_boundary_level (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) (p : ℝ)
    (hp : (overlap π σ)^2/vectorMass π≤p ∧ p≤(overlap π σ)^2/projectedMass π σ) :
    ∃ lam∈Set.Icc 0 (sourceCap π),
      SourceBox π (boundaryFill π σ lam) ∧ 0<vectorMass (boundaryFill π σ lam) ∧
      (vectorDot σ (boundaryFill π σ lam))^2=p*vectorMass (boundaryFill π σ lam) := by
  have hcap : 0≤sourceCap π := by
    have hs : 0≤∑ i,π i := Finset.sum_nonneg (fun i _ => hπ i)
    dsimp [sourceCap]
    linarith
  have hm : ∀ lam∈Set.Icc 0 (sourceCap π),vectorMass (boundaryFill π σ lam)≠0 :=
    fun lam _ => (boundary_mass_pos π σ ho lam).ne'
  have hc : ContinuousOn (fun lam => (overlap π σ)^2/vectorMass (boundaryFill π σ lam))
      (Set.Icc 0 (sourceCap π)) :=
    continuous_const.continuousOn.div (continuous_boundaryMass π σ).continuousOn hm
  have hend : (overlap π σ)^2/vectorMass (boundaryFill π σ (sourceCap π))≤p ∧
      p≤(overlap π σ)^2/vectorMass (boundaryFill π σ 0) := by
    simpa only [boundary_cap π σ hπ,boundary_zero π σ hπ,vectorMass,projectedMass] using! hp
  obtain ⟨lam,hlam,hval⟩ := intermediate_value_Icc' hcap hc hend
  refine ⟨lam,hlam,?_,boundary_mass_pos π σ ho lam,?_⟩
  · intro i
    unfold boundaryFill
    split_ifs
    · exact ⟨hπ i,le_rfl⟩
    · exact ⟨le_min (hπ i) hlam.1,min_le_left _ _⟩
  · rw [boundaryDot π σ hσ lam]
    exact (div_eq_iff (hm lam hlam)).mp hval

theorem frontier1 (π σ : Fin m → ℝ) (hπ : ∀ i,0≤π i) (hσ : ∀ i,0≤σ i)
    (ho : HasOverlap π σ) (p : ℝ)
    (hp : (overlap π σ)^2/projectedMass π σ≤p ∧ p≤realPmax π σ) :
    ∃ γ∈Set.Icc (low π σ) (high π σ),
      RealizesFidelity π σ p γ ∧
      checkedFill π σ p γ=some (realFill π σ γ) ∧
      Tendsto (fun δ : ℝ => realMass π (fun i => σ i+δ) γ) (𝓝[>]0) (𝓝 (realMass π σ γ)) ∧
      Tendsto (fun δ : ℝ => realFidelity π (fun i => σ i+δ) γ) (𝓝[>]0) (𝓝 p) := by
  obtain ⟨γ,hγ,hreal⟩ := exists_finite_level π σ hπ hσ ho p hp
  have hf : realFidelity π σ γ=p := by
    rw [fidelity_eq_div,hreal.2,mul_div_cancel_right₀ _ hreal.1.ne']
  have hs := positive_chain_compatible π σ hσ γ hreal.1
  refine ⟨γ,hγ,hreal,(checkedFill_spec π σ p γ _).mpr ⟨hreal.1,hf.ge,rfl⟩,hs.2.2.1,?_⟩
  simpa only [hf] using! hs.2.2.2.2

end Qatlib.Concepts.Waterfill.LevelFidelity.WaterfillZeroBoundary
