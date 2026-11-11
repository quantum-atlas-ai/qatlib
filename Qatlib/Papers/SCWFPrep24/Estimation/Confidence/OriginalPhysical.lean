/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridLossBridge
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhysicalScales
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhaseLaw

set_option backward.isDefEq.respectTransparency false

/-!
# Original Physical

The literal pair labels of the complete original periodic grid.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridLossBridge
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The literal pair labels of the complete original periodic grid. -/
abbrev PairLabels (d N : ℕ) := (Fin (N/4) × Bool) × (Fin d → Fin ((N/4)*4))

/-- The exact original double shift expressed in its one known full pair-coordinate basis. -/
def originalGraph (d N : ℕ) [NeZero N] (h4 : 4∣N) (j : Fin (d+1)) : Equiv.Perm (PairLabels d N × Bool) :=
  (((originalGrid d N h4).symm.trans (periodicDoubleShift (d+1) N j)).trans (originalGrid d N h4))

/-- The actual original unit shifts, rather than an assumed graph certificate, have the pair-coordinate double-shift action. -/
theorem originalGraph_unit_square (d N : ℕ) [NeZero N] (h4 : 4∣N) (j : Fin (d+1))
    (a : Fin (d+1) → Fin N) :
    originalGrid d N h4 (periodicUnitShift (d+1) N j (periodicUnitShift (d+1) N j a))=
      originalGraph d N h4 j (originalGrid d N h4 a) := by
  have hs := congrArg (fun p : Equiv.Perm (Fin (d+1) → Fin N) => p a)
    (periodic_unit_shift_square (d+1) N j)
  change periodicUnitShift (d+1) N j (periodicUnitShift (d+1) N j a)=periodicDoubleShift (d+1) N j a at hs
  rw [hs]
  simp only [originalGraph,Equiv.trans_apply,Equiv.symm_apply_apply]

/-- The concrete matched-block graph is the same complete original graph at every original side length divisible by four. -/
theorem originalGraph_eq (d N : ℕ) [NeZero N] [NeZero ((N/4)*4)] (h4 : 4∣N) :
    originalGraph d N h4=doubleGraph d (N/4) := by
  funext j
  apply Equiv.ext
  intro a
  apply (grid d (N/4)).symm.injective
  simp only [originalGraph,Equiv.trans_apply,originalGrid,Equiv.symm_apply_apply,doubleGraph_inverse]
  exact periodic_size_transport (d+1) N ((N/4)*4) (Nat.div_mul_cancel h4).symm j _

/-- The actual original sign-and-phase field on the entire original periodic grid. -/
abbrev originalField (d N : ℕ) (h4 : 4∣N) (b : ℝ) (κ : PairLabels d N → Fin 4)
    (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) :=
  physicalField (originalGrid d N h4) b κ Q ω

/-- The exact original full loss of one actual prior member, including its phase-sensitive velocity term. -/
abbrev originalFieldLoss (d N : ℕ) [NeZero N] (h4 : 4∣N) (b : ℝ)
    (κ : PairLabels d N → Fin 4) (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) (h lam : ℝ) :=
  spinorDiscreteLoss (real0 (originalField d N h4 b κ Q ω)) (imag0 (originalField d N h4 b κ Q ω))
    (real1 (originalField d N h4 b κ Q ω)) (imag1 (originalField d N h4 b κ Q ω))
    (fun _ _ => 0) (periodicUnitShift (d+1) N) h 1 lam

/-- The true original periodic-grid prior mean is computed from its actual four-sign law at the original side length. -/
theorem original_graph_mean (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (b G ρ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1) :
    (finitePairLaw (PairLabels d N) ρ hlo hhi).expect (spinEnergy b G (originalGraph d N h4))=
      G*b*(1-b)*((d+1 : ℕ)-ρ/2) := by
  have hK := original_block_range N hN h4
  let : NeZero ((N/4)*4) := ⟨by omega⟩
  change (∑ κ : PairLabels d N → Fin 4,pairedSignLaw ρ κ*spinEnergy b G (originalGraph d N h4) κ)=_
  rw [originalGraph_eq]
  exact original_spin_prior_mean d (N/4) (by omega) b G ρ hb0 hb1 hlo hhi

/-- Every original phase realization pays its same actual graph spin energy and its full velocity nuisance, with no supplied graph or gap certificate. -/
theorem original_field_full_loss (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (κ : PairLabels d N → Fin 4)
    (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) (h lam : ℝ) (hh : h≠0) :
    0≤originalFieldLoss d N h4 b κ Q ω h lam-spinEnergy b (2*lam^2/h^2) (originalGraph d N h4) κ ∧
    originalFieldLoss d N h4 b κ Q ω h lam-spinEnergy b (2*lam^2/h^2) (originalGraph d N h4) κ≤(d+1 : ℕ)/h^2 := by
  have hK := original_block_range N hN h4
  let : NeZero (N/4) := ⟨by omega⟩
  exact physicalField_full_loss (originalGrid d N h4) (periodicUnitShift (d+1) N)
    (originalGraph d N h4) (originalGraph_unit_square d N h4) b hb0 hb1 κ Q ω h lam hh

/-- Every actual original prior member meets each direction of the original public Bell promise. -/
theorem original_field_bell_promise (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (κ : PairLabels d N → Fin 4) (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) (j : Fin (d+1)) :
    bellMean (real0 (originalField d N h4 (128/((N : ℝ)^2)) κ Q ω))
      (imag0 (originalField d N h4 (128/((N : ℝ)^2)) κ Q ω))
      (real1 (originalField d N h4 (128/((N : ℝ)^2)) κ Q ω))
      (imag1 (originalField d N h4 (128/((N : ℝ)^2)) κ Q ω)) (periodicDoubleShift (d+1) N j)≤256/((N : ℝ)^2) :=
  original_weak_phase_bell_bound N Q hN (fun a => siteSign κ (originalGrid d N h4 a))
    (fun a => siteSign_unit κ (originalGrid d N h4 a)) ω (periodicDoubleShift (d+1) N j)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical


namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The actual complete physical loss lies outside its two deterministic spin-mean envelopes. -/
def badFieldLoss (d N : ℕ) [NeZero N] (h4 : 4∣N) (b η ρ h lam : ℝ)
    (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) (κ : PairLabels d N → Fin 4) : Prop :=
  originalFieldLoss d N h4 b κ Q ω h lam<(2*lam^2/h^2)*b*(1-b)*((d+1 : ℕ)-ρ/2)-η/2 ∨
    (2*lam^2/h^2)*b*(1-b)*((d+1 : ℕ)-ρ/2)+η/2+(d+1 : ℕ)/h^2<
      originalFieldLoss d N h4 b κ Q ω h lam

/-- The actual complete original loss, for every fixed shared phase realization, has the real bad-prior bound under its unique original sign law. -/
theorem original_actual_loss_tail (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (b η ρ h lam : ℝ) (hb : 0<b) (hb1 : b≤1) (hη : 0<η)
    (hlo : -1≤ρ) (hhi : ρ≤1) (hh : h≠0) (hlam : 0<lam)
    (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) :
    (∑ κ ∈ Finset.univ.filter (badFieldLoss d N h4 b η ρ h lam Q ω),
      (finitePairLaw (PairLabels d N) ρ hlo hhi).prob κ)≤
      2*Real.exp (-(N^(d+1) : ℕ)*η^2/(64*((d+1 : ℕ) : ℝ)^2*(2*lam^2/h^2)^2*b^2)) := by
  have hK := original_block_range N hN h4
  let : NeZero (N/4) := ⟨by omega⟩
  let G : ℝ := 2*lam^2/h^2
  have hG : 0<G := by dsimp [G]; positivity
  let μ : ℝ := G*b*(1-b)*((d+1 : ℕ)-ρ/2)
  have ht := finite_pair_spin_tail (E := PairLabels d N) (d+1) (by omega) b G η ρ
    hb hb1 hG hη hlo hhi (originalGraph d N h4)
  rw [original_graph_mean d N hN h4 b G ρ hb.le hb1 hlo hhi] at ht
  have hinc (κ : PairLabels d N → Fin 4) (hbad : badFieldLoss d N h4 b η ρ h lam Q ω κ) :
      η/2≤|spinEnergy b G (originalGraph d N h4) κ-μ| := by
    have hn := original_field_full_loss d N hN h4 b hb.le hb1 κ Q ω h lam hh
    change 0≤originalFieldLoss d N h4 b κ Q ω h lam-spinEnergy b G (originalGraph d N h4) κ ∧
      originalFieldLoss d N h4 b κ Q ω h lam-spinEnergy b G (originalGraph d N h4) κ≤(d+1 : ℕ)/h^2 at hn
    change originalFieldLoss d N h4 b κ Q ω h lam<μ-η/2 ∨
      μ+η/2+(d+1 : ℕ)/h^2<originalFieldLoss d N h4 b κ Q ω h lam at hbad
    rcases hbad with hlow | hhigh
    · exact (show η/2≤-(spinEnergy b G (originalGraph d N h4) κ-μ) by linarith [hn.1]).trans (neg_le_abs _)
    · exact (show η/2≤ spinEnergy b G (originalGraph d N h4) κ-μ by linarith [hn.2]).trans (le_abs_self _)
  have hmass : (∑ κ ∈ Finset.univ.filter (badFieldLoss d N h4 b η ρ h lam Q ω),
      (finitePairLaw (PairLabels d N) ρ hlo hhi).prob κ)≤
      ∑ κ ∈ Finset.univ.filter (fun κ : PairLabels d N → Fin 4 =>
        η/2≤|spinEnergy b G (originalGraph d N h4) κ-μ|),
        (finitePairLaw (PairLabels d N) ρ hlo hhi).prob κ := by
    simp only [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro κ _
    by_cases hbad : badFieldLoss d N h4 b η ρ h lam Q ω κ
    · simp only [ite_eq_left hbad,ite_eq_left (hinc κ hbad)]
      exact le_rfl
    · simp only [ite_eq_right hbad]
      split_ifs
      · exact (finitePairLaw (PairLabels d N) ρ hlo hhi).nonneg κ
      · exact le_rfl
  have hcard : (Fintype.card (PairLabels d N × Bool) : ℝ)=(N^(d+1) : ℕ) := by
    exact_mod_cast original_grid_cardinality d N h4
  exact hmass.trans (by simpa only [μ,G,hcard] using ht)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical


namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy

/-- The actual full-loss bad prior of the original physical input has mass at most delta throughout the original collision-confidence regime. -/
theorem original_actual_bad_prior_paid (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (hd : d+1=2 ∨ d+1=3) (ρ δ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1)
    (hδ : 0<δ) (hmax : δ≤1/10) (hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2)
    (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) :
    (∑ κ ∈ Finset.univ.filter (badFieldLoss d N h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) ρ (2*Real.pi/N) N Q ω),
      (finitePairLaw (PairLabels d N) ρ hlo hhi).prob κ)≤δ := by
  have hn : 0<(N : ℝ) := by
    have h : (256 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hb := original_weak_excitation N hN
  have ht := original_actual_loss_tail d N hN h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) ρ (2*Real.pi/N) N
    (by positivity) (by linarith [hb.2]) (by positivity) hlo hhi (by positivity) hn Q ω
  have hs := original_spin_exponent_lower N (d+1) (N^(d+1) : ℕ) hN hd (by positivity)
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hs)) (by norm_num : (0 : ℝ)≤2)
  have he' :
      2*Real.exp (-(N^(d+1) : ℕ)*((N : ℝ)^2)^2/
        (64*((d+1 : ℕ) : ℝ)^2*(2*(N : ℝ)^2/(2*Real.pi/N)^2)^2*(128/((N : ℝ)^2))^2))≤
      2*Real.exp (-(81/(262144*((d+1 : ℕ) : ℝ)^2))*(N^(d+1) : ℕ)) := by
    simpa only [neg_div,neg_mul] using he
  exact (ht.trans he').trans (original_bad_prior_paid N (d+1) (N^(d+1) : ℕ) δ hN hd (by positivity) hδ hmax hL)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhaseLaw
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The actual original prior samples one pair-sign field and one site-phase field, each retained across all supplied copies. -/
def originalPriorLaw (d N : ℕ) (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) (Q : ℕ) :
    FinDist ((PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1))) where
  prob z := (finitePairLaw (PairLabels d N) ρ hlo hhi).prob z.1*
    (uniformPhaseLaw (Fin (d+1) → Fin N) Q).prob z.2
  nonneg z := mul_nonneg ((finitePairLaw (PairLabels d N) ρ hlo hhi).nonneg z.1)
    ((uniformPhaseLaw (Fin (d+1) → Fin N) Q).nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,(uniformPhaseLaw (Fin (d+1) → Fin N) Q).sum_one,mul_one,
      (finitePairLaw (PairLabels d N) ρ hlo hhi).sum_one]

/-- The true source prior's bad physical-loss mass is exactly the normalized average of its fixed-phase bad masses. -/
theorem original_bad_mass_disintegrate (d N : ℕ) [NeZero N] (h4 : 4∣N) (b η ρ h lam : ℝ)
    (hlo : -1≤ρ) (hhi : ρ≤1) (Q : ℕ) :
    (∑ z ∈ Finset.univ.filter (fun z : (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1)) =>
      badFieldLoss d N h4 b η ρ h lam Q z.2 z.1),(originalPriorLaw d N ρ hlo hhi Q).prob z)=
    ∑ ω,(uniformPhaseLaw (Fin (d+1) → Fin N) Q).prob ω*
      (∑ κ ∈ Finset.univ.filter (badFieldLoss d N h4 b η ρ h lam Q ω),
        (finitePairLaw (PairLabels d N) ρ hlo hhi).prob κ) := by
  simp only [Finset.sum_filter,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ _
  by_cases hb : badFieldLoss d N h4 b η ρ h lam Q ω κ
  · simp only [ite_eq_left hb,originalPriorLaw]
    ring
  · simp only [ite_eq_right hb,mul_zero]

/-- The true original full sign/shared-phase physical prior, rather than a conditional or externally certified law, pays at most delta bad-input mass for all original collision confidence values. -/
theorem original_joint_bad_prior_paid (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N)
    (hd : d+1=2 ∨ d+1=3) (ρ δ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1)
    (hδ : 0<δ) (hmax : δ≤1/10) (hL : Real.log (1/δ)≤(N^(d+1) : ℕ)/(N : ℝ)^2) (Q : ℕ) :
    (∑ z ∈ Finset.univ.filter (fun z : (PairLabels d N → Fin 4) × ((Fin (d+1) → Fin N) → Fin (Q+1)) =>
      badFieldLoss d N h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) ρ (2*Real.pi/N) N Q z.2 z.1),
      (originalPriorLaw d N ρ hlo hhi Q).prob z)≤δ := by
  rw [original_bad_mass_disintegrate]
  exact phase_average_le Q _ δ (fun ω => original_actual_bad_prior_paid d N hN h4 hd ρ δ hlo hhi hδ hmax hL Q ω)

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical


namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence

/-- The fixed physical threshold between the original two actual full-loss prior envelopes. -/
def physicalThreshold (D N : ℕ) : ℝ :=
  (2*(N : ℝ)^2/(2*Real.pi/N)^2)*(128/((N : ℝ)^2))*(1-128/((N : ℝ)^2))*(D : ℝ)+
    ((D : ℝ)/(2*Real.pi/N)^2)/2

/-- Accurate estimation on every good actual low-loss input forces the original real output below the one common threshold. -/
theorem original_low_threshold (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (hd : d+1≤3)
    (κ : PairLabels d N → Fin 4) (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) (z : ℝ)
    (hgood : ¬badFieldLoss d N h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) (3/4) (2*Real.pi/N) N Q ω κ)
    (herr : |z-originalFieldLoss d N h4 (128/((N : ℝ)^2)) κ Q ω (2*Real.pi/N) N|≤(N : ℝ)^2) :
    z<physicalThreshold (d+1) N := by
  let C : ℝ := (2*(N : ℝ)^2/(2*Real.pi/N)^2)*(128/((N : ℝ)^2))*(1-128/((N : ℝ)^2))
  let η : ℝ := (N : ℝ)^2
  let v : ℝ := ((d+1 : ℕ) : ℝ)/(2*Real.pi/N)^2
  have hg := original_physical_threshold_gap N (d+1) hN hd
  change 3*η+v<C*(3/4) at hg
  change ¬(originalFieldLoss d N h4 (128/((N : ℝ)^2)) κ Q ω (2*Real.pi/N) N<C*((d+1 : ℕ)-(3/4 : ℝ)/2)-η/2 ∨
    C*((d+1 : ℕ)-(3/4 : ℝ)/2)+η/2+v<originalFieldLoss d N h4 (128/((N : ℝ)^2)) κ Q ω (2*Real.pi/N) N) at hgood
  have hL := not_lt.mp (not_or.mp hgood).2
  have hz := (abs_le.mp herr).2
  change z<C*((d+1 : ℕ) : ℝ)+v/2
  nlinarith

/-- Accurate estimation on every good actual high-loss input forces the original real output above the same threshold. -/
theorem original_high_threshold (d N : ℕ) [NeZero N] (hN : 256≤N) (h4 : 4∣N) (hd : d+1≤3)
    (κ : PairLabels d N → Fin 4) (Q : ℕ) (ω : (Fin (d+1) → Fin N) → Fin (Q+1)) (z : ℝ)
    (hgood : ¬badFieldLoss d N h4 (128/((N : ℝ)^2)) ((N : ℝ)^2) (-3/4) (2*Real.pi/N) N Q ω κ)
    (herr : |z-originalFieldLoss d N h4 (128/((N : ℝ)^2)) κ Q ω (2*Real.pi/N) N|≤(N : ℝ)^2) :
    physicalThreshold (d+1) N<z := by
  let C : ℝ := (2*(N : ℝ)^2/(2*Real.pi/N)^2)*(128/((N : ℝ)^2))*(1-128/((N : ℝ)^2))
  let η : ℝ := (N : ℝ)^2
  let v : ℝ := ((d+1 : ℕ) : ℝ)/(2*Real.pi/N)^2
  have hg := original_physical_threshold_gap N (d+1) hN hd
  change 3*η+v<C*(3/4) at hg
  change ¬(originalFieldLoss d N h4 (128/((N : ℝ)^2)) κ Q ω (2*Real.pi/N) N<C*((d+1 : ℕ)-(-3/4 : ℝ)/2)-η/2 ∨
    C*((d+1 : ℕ)-(-3/4 : ℝ)/2)+η/2+v<originalFieldLoss d N h4 (128/((N : ℝ)^2)) κ Q ω (2*Real.pi/N) N) at hgood
  have hL := not_lt.mp (not_or.mp hgood).1
  have hz := (abs_le.mp herr).1
  change C*((d+1 : ℕ) : ℝ)+v/2<z
  nlinarith

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.OriginalPhysical
